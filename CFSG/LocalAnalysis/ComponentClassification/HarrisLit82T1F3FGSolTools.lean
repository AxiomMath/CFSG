module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem exists_two_mul_odd [Finite G] (g : G) :
    ∃ a ∈ zpowers g, ∃ b ∈ zpowers g, g = a * b ∧ (∃ k : ℕ, a ^ 2 ^ k = 1) ∧
      Odd (orderOf b) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hg : g ^ ((2 ^ k * m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hn, pow_orderOf_eq_one]
  refine ⟨g ^ (v * m), zpow_mem (mem_zpowers g) _, g ^ (u * 2 ^ k),
    zpow_mem (mem_zpowers g) _, ?_, ⟨k, ?_⟩, ?_⟩
  · rw [← zpow_add, show v * (m : ℤ) + u * 2 ^ k = 1 by push_cast at huv; linear_combination huv,
      zpow_one]
  · rw [← zpow_natCast, ← zpow_mul, show v * (m : ℤ) * ((2 ^ k : ℕ) : ℤ) =
      ((2 ^ k * m : ℕ) : ℤ) * v by push_cast; ring, zpow_mul, hg, one_zpow]
  · apply Odd.of_dvd_nat hm
    apply orderOf_dvd_of_pow_eq_one
    rw [← zpow_natCast, ← zpow_mul, show u * (2 : ℤ) ^ k * (m : ℤ) =
      ((2 ^ k * m : ℕ) : ℤ) * u by push_cast; ring, zpow_mul, hg, one_zpow]

@[expose] def iterComm (N A : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | k + 1 => ⁅iterComm N A k, A⁆

theorem iterComm_mono_right {N A B : Subgroup G} (h : A ≤ B) :
    ∀ k, iterComm N A k ≤ iterComm N B k
  | 0 => le_rfl
  | k + 1 => Subgroup.commutator_mono (iterComm_mono_right h k) h

theorem exists_iterComm_le_inf {A N : Subgroup G} (hA : A.IsSubnormal) (hN : N.Normal) :
    ∃ n, iterComm N A n ≤ A ⊓ N := by
  induction hA with
  | top => exact ⟨0, le_inf le_top le_rfl⟩
  | step H K hHK hK hHn ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    show ⁅iterComm N H n, H⁆ ≤ H ⊓ N
    rw [Subgroup.commutator_le]
    intro x hx h hh
    have hxK : x ∈ K ⊓ N := hn (iterComm_mono_right hHK n hx)
    have h1 : x * h * x⁻¹ ∈ H := (normal_subgroupOf_iff hHK).mp hHn h x hh hxK.1
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact H.mul_mem h1 (H.inv_mem hh)
    · rw [commutatorElement_def, show x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) by group]
      exact N.mul_mem hxK.2 (hN.conj_mem _ (N.inv_mem hxK.2) h)

theorem iterComm_le_self {N R : Subgroup G} (hN : N.Normal) : ∀ k, iterComm N R k ≤ N
  | 0 => le_rfl
  | k + 1 => Subgroup.commutator_le.mpr fun x hx r _ => by
      have hxN := iterComm_le_self hN k hx
      rw [commutatorElement_def, show x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹) by group]
      exact N.mul_mem hxN (hN.conj_mem _ (N.inv_mem hxN) r)

theorem le_normalizer_iterComm {N R : Subgroup G} (hN : N.Normal) :
    ∀ k, R ≤ normalizer (iterComm N R k : Set G)
  | 0 => by
    show R ≤ normalizer (N : Set G)
    rw [normalizer_eq_top_iff.mpr hN]
    exact le_top
  | _ + 1 => normalizer_commutator_ge_right _ _

theorem commutator_eq_bot_of_iterComm [Finite G] {N R : Subgroup G} (hN : N.Normal)
    (hN2 : IsPGroup 2 N) (hRo : Odd (Nat.card R)) {n : ℕ} (hn : iterComm N R n = ⊥) :
    ⁅N, R⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ j, iterComm N R (j + 2) = ⊥ → iterComm N R (j + 1) = ⊥ := by
    intro j h
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hN2.to_le (iterComm_le_self hN j))
    exact GorensteinWalter.commutator_eq_bot_of_coprime_double_commutator_eq_bot _ R
      (le_normalizer_iterComm hN j)
      (by rw [ha]; exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hRo)) h
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · change N = ⊥ at hn
    rw [hn, Subgroup.commutator_bot_left]
  have hdown : ∀ j, j + 1 ≤ n → iterComm N R (n - j) = ⊥ := by
    intro j
    induction j with
    | zero => intro _; simpa using hn
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      rw [show n - j = (n - (j + 1) - 1) + 2 by omega] at h
      rw [show n - (j + 1) = (n - (j + 1) - 1) + 1 by omega]
      exact key _ h
  have h1 := hdown (n - 1) (by omega)
  rwa [show n - (n - 1) = 0 + 1 by omega] at h1

theorem commute_of_subnormal [Finite G] {A N : Subgroup G} (hA : A.IsSubnormal) (hN : N.Normal)
    (hN2 : IsPGroup 2 N) (hAN : A ⊓ N = ⊥) {y : G} (hy : y ∈ A) (hyo : Odd (orderOf y)) :
    ∀ x ∈ N, x * y = y * x := by
  obtain ⟨n, hn⟩ := exists_iterComm_le_inf hA hN
  have hR : iterComm N (zpowers y) n = ⊥ :=
    le_bot_iff.mp ((iterComm_mono_right (zpowers_le.mpr hy) n).trans (hn.trans hAN.le))
  have hc := commutator_eq_bot_of_iterComm hN hN2 (by rwa [Nat.card_zpowers]) hR
  intro x hx
  have h1 : ⁅x, y⁆ ∈ ⁅N, zpowers y⁆ := Subgroup.commutator_mem_commutator hx (mem_zpowers y)
  rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem isSubnormal_map_center {X : Type*} [Group X] {t : X} {J : Subgroup X}
    (hJt : J ≤ centralizer {t}) (hJs : (J.subgroupOf (centralizer {t})).IsSubnormal) :
    J.map (QuotientGroup.mk' (center X)) ≤ centralizer {QuotientGroup.mk' (center X) t} ∧
      ((J.map (QuotientGroup.mk' (center X))).subgroupOf
        (centralizer {QuotientGroup.mk' (center X) t})).IsSubnormal := by
  set σ := QuotientGroup.mk' (center X) with hσ
  let C := centralizer ({t} : Set X)
  let Ct := centralizer ({σ t} : Set (X ⧸ center X))
  have hC0 : C.map σ ≤ Ct := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    change σ c ∈ centralizer ({σ t} : Set _)
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hc']
  have hC0n : ((C.map σ).subgroupOf Ct).Normal := by
    rw [normal_subgroupOf_iff hC0]
    rintro _ b ⟨c, hc, rfl⟩ hb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center X) b
    have hb' : σ y * σ t = σ t * σ y := mem_centralizer_singleton_iff.mp hb
    have hn : (y * t)⁻¹ * (t * y) ∈ center X := by
      have h1 : σ (y * t) = σ (t * y) := by rw [map_mul, map_mul, hb']
      exact QuotientGroup.eq.mp h1
    set n := (y * t)⁻¹ * (t * y) with hndef
    have hnc : ∀ g, g * n = n * g := fun g => mem_center_iff.mp hn g
    have hc' : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    have hty : t * y = y * t * n := by rw [hndef]; group
    have hyt : y⁻¹ * t = t * n * y⁻¹ := by
      calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
        _ = y⁻¹ * (y * t * n) * y⁻¹ := by rw [hty]
        _ = t * n * y⁻¹ := by group
    have hd : y * c * y⁻¹ ∈ C := by
      rw [mem_centralizer_singleton_iff]
      calc y * c * y⁻¹ * t = y * c * (y⁻¹ * t) := by group
        _ = y * c * (t * n * y⁻¹) := by rw [hyt]
        _ = y * (c * t) * n * y⁻¹ := by group
        _ = y * (t * c) * n * y⁻¹ := by rw [hc']
        _ = y * t * (c * n) * y⁻¹ := by group
        _ = y * t * n * c * y⁻¹ := by rw [hnc c]; group
        _ = t * y * c * y⁻¹ := by rw [← hty]
        _ = t * (y * c * y⁻¹) := by group
    exact ⟨y * c * y⁻¹, hd, by simp [hσ]⟩
  let γ : ↥C →* ↥Ct := (σ.comp C.subtype).codRestrict Ct (fun c => hC0 (mem_map_of_mem σ c.2))
  have hγr : γ.range = (C.map σ).subgroupOf Ct := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, hcy⟩
      exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hγn : γ.range.Normal := by rw [hγr]; exact hC0n
  have hJle : J.map σ ≤ Ct := (map_mono hJt).trans hC0
  refine ⟨hJle, ?_⟩
  have h1 := isSubnormal_map_of_range_normal γ hγn hJs
  convert h1 using 1
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hJt hx⟩, hx, rfl⟩
  · rintro ⟨c, hc, hcy⟩
    exact ⟨c, hc, congrArg Subtype.val hcy⟩

theorem eq_of_inv_mul_mem_center {Y H : Type*} [Group Y] [Group H] [Group.IsPerfect Y]
    (a b : Y →* H) (hab : ∀ y, (a y)⁻¹ * b y ∈ center H) : a = b := by
  let χ : Y →* center H :=
    { toFun := fun y => ⟨(a y)⁻¹ * b y, hab y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => by
        apply Subtype.ext
        have hc : (a y')⁻¹ * ((a y)⁻¹ * b y) = ((a y)⁻¹ * b y) * (a y')⁻¹ :=
          Subgroup.mem_center_iff.1 (hab y) ((a y')⁻¹)
        change (a (y * y'))⁻¹ * b (y * y') = (a y)⁻¹ * b y * ((a y')⁻¹ * b y')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a y')⁻¹ * (a y)⁻¹ * (b y * b y') = ((a y')⁻¹ * ((a y)⁻¹ * b y)) * b y' := by
              simp only [mul_assoc]
          _ = ((a y)⁻¹ * b y) * (a y')⁻¹ * b y' := by rw [hc]
          _ = (a y)⁻¹ * b y * ((a y')⁻¹ * b y') := by simp only [mul_assoc] }
  have hker : _root_.commutator Y ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun y => ?_
  have hy : y ∈ χ.ker := hker (htop ▸ Subgroup.mem_top y)
  exact inv_mul_eq_one.1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hy))

theorem commute_of_inv_mul_mem_center {E : Subgroup G} [Group.IsPerfect ↥E] {x : G}
    (hxE : ∀ e ∈ E, x * e * x⁻¹ ∈ E)
    (hZ : ∀ e : ↥E, e⁻¹ * ⟨x * e * x⁻¹, hxE e e.2⟩ ∈ center ↥E) :
    ∀ e ∈ E, x * e = e * x := by
  let b : ↥E →* ↥E :=
    { toFun := fun e => ⟨x * e * x⁻¹, hxE e e.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun e f => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have h := eq_of_inv_mul_mem_center (MonoidHom.id ↥E) b hZ
  intro e he
  have h1 := congrArg (fun φ : ↥E →* ↥E => ((φ ⟨e, he⟩ : ↥E) : G)) h
  simp only [MonoidHom.id_apply, b, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [← h1]

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
