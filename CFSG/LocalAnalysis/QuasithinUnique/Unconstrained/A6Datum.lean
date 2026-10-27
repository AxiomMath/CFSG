module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Datum

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

@[expose] noncomputable def Notation25.actHom (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) :
    ↥N.H →* ↥(autOn N.H N.K) :=
  MonoidHom.codRestrict ((conjAct N.K).comp (Subgroup.inclusion hKH)) (autOn N.H N.K)
    fun h => Subgroup.mem_map.mpr
      ⟨Subgroup.inclusion hKH h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩

theorem Notation25.actHom_apply (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h : ↥N.H)
    (k : ↥N.K) :
    ((((N.actHom hKH h : ↥(autOn N.H N.K)) : MulAut ↥N.K) k : ↥N.K) : G) =
      (h : G) * k * (h : G)⁻¹ := rfl

theorem Notation25.actHom_surjective (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) :
    Function.Surjective (N.actHom hKH) := by
  rintro ⟨f, hf⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hf
  refine ⟨⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
  apply Subtype.ext
  rfl

theorem Notation25.actHom_eq_one_iff (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h : ↥N.H) :
    N.actHom hKH h = 1 ↔ ∀ k ∈ N.K, (h : G) * k = k * (h : G) := by
  constructor
  · intro h1 k hk
    have := congrArg (fun f : ↥(autOn N.H N.K) => (((f : MulAut ↥N.K) ⟨k, hk⟩ : ↥N.K) : G)) h1
    simp only [N.actHom_apply hKH h] at this
    have h2 : (h : G) * k * (h : G)⁻¹ = k := this
    calc (h : G) * k = (h : G) * k * (h : G)⁻¹ * (h : G) := by group
      _ = k * (h : G) := by rw [h2]
  · intro hc
    apply Subtype.ext
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    show (h : G) * k * (h : G)⁻¹ = k
    rw [hc k k.2]
    group

structure A6Datum (N : Notation25 hs) where
  Φ : G → P10
  mem : ∀ h ∈ N.H, Φ h ∈ A6Models.autA6
  mul : ∀ a ∈ N.H, ∀ b ∈ N.H, Φ (a * b) = Φ a * Φ b
  surj : ∀ y ∈ A6Models.autA6, ∃ h ∈ N.H, Φ h = y
  ker : ∀ h ∈ N.H, Φ h = 1 ↔ ∀ k ∈ N.K, h * k = k * h
  S_mem : ∀ s ∈ N.S, Φ s ∈ P0
  S_surj : ∀ p ∈ P0, ∃ s ∈ N.S, Φ s = p
  K_mem : ∀ k ∈ N.K, Φ k ∈ A6Models.psl29
  K_surj : ∀ y ∈ A6Models.psl29, ∃ k ∈ N.K, Φ k = y

theorem exists_hom_S_eq_P0 (hS : IsSylowTwoOf N.S N.H) (Φ₀ : ↥N.H →* ↥A6Models.autA6)
    (hsurj : Function.Surjective Φ₀) :
    ∃ Φ₁ : ↥N.H →* ↥A6Models.autA6, Function.Surjective Φ₁ ∧
      (∀ h : ↥N.H, Φ₁ h = 1 ↔ Φ₀ h = 1) ∧
      (∀ s : ↥N.H, (s : G) ∈ N.S → ((Φ₁ s : ↥A6Models.autA6) : P10) ∈ P0) ∧
      (∀ p : P10, ∀ hp : p ∈ P0, ∃ s : ↥N.H, (s : G) ∈ N.S ∧ (Φ₁ s : ↥A6Models.autA6) =
        ⟨p, P0_le_autA6 hp⟩) := by
  have hS2 : IsPGroup 2 ↥(N.S.subgroupOf N.H) :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hS.le).symm
  set S₀ : Subgroup ↥A6Models.autA6 := (N.S.subgroupOf N.H).map Φ₀ with hS₀def
  have hS₀p : IsPGroup 2 ↥S₀ := hS2.map Φ₀
  have hS₀idx : ¬ 2 ∣ S₀.index := fun hd =>
    hS.2.2 (hd.trans (Subgroup.index_map_dvd (N.S.subgroupOf N.H) hsurj))
  have hS₀ : IsSylowTwoOf S₀ ⊤ :=
    ⟨le_top, hS₀p, by rw [index_subgroupOf_top]; exact hS₀idx⟩
  set P0A : Subgroup ↥A6Models.autA6 := P0.subgroupOf A6Models.autA6 with hP0A
  have hP0Acard : Nat.card P0A = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P0_le_autA6).toEquiv, card_P0]
  have hP0p : IsPGroup 2 ↥P0A := IsPGroup.of_card (n := 5) (by rw [hP0Acard]; norm_num)
  have hP0idx : ¬ 2 ∣ P0A.index := by
    have h1 := Subgroup.card_mul_index P0A
    rw [hP0Acard, card_autA6] at h1
    omega
  have hP0 : IsSylowTwoOf P0A ⊤ :=
    ⟨le_top, hP0p, by rw [index_subgroupOf_top]; exact hP0idx⟩
  obtain ⟨g, -, hg⟩ := hS₀.exists_conj hP0
  refine ⟨(MulAut.conj g).toMonoidHom.comp Φ₀, ?_, ?_, ?_, ?_⟩
  · exact (MulAut.conj g).surjective.comp hsurj
  · intro h
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe]
    exact (map_eq_one_iff _ (MulEquiv.injective _))
  · intro s hs
    have h1 : Φ₀ s ∈ S₀ := Subgroup.mem_map.mpr ⟨s, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    have h2 : (MulAut.conj g).toMonoidHom (Φ₀ s) ∈ P0A := by
      rw [hg]; exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
    exact Subgroup.mem_subgroupOf.mp h2
  · intro p hp
    have h1 : (⟨p, P0_le_autA6 hp⟩ : ↥A6Models.autA6) ∈ P0A := Subgroup.mem_subgroupOf.mpr hp
    rw [hg] at h1
    obtain ⟨x, hx, hxp⟩ := Subgroup.mem_map.mp h1
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨s, Subgroup.mem_subgroupOf.mp hs, hxp⟩

theorem K_part (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (hsimple : IsSimpleGroup ↥N.K)
    (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1) (hcard : Nat.card N.K = 360)
    (Φ : ↥N.H →* ↥A6Models.autA6)
    (hsurj : Function.Surjective Φ)
    (hker : ∀ h : ↥N.H, Φ h = 1 ↔ ∀ k ∈ N.K, (h : G) * k = k * (h : G)) :
    (∀ k : ↥N.H, (k : G) ∈ N.K → ((Φ k : ↥A6Models.autA6) : P10) ∈ A6Models.psl29) ∧
      ∀ y ∈ A6Models.psl29, ∃ k : ↥N.H, (k : G) ∈ N.K ∧
        ((Φ k : ↥A6Models.autA6) : P10) = y := by
  set ψ : ↥N.K →* ↥A6Models.autA6 := Φ.comp (Subgroup.inclusion N.K_le_H) with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : Φ (Subgroup.inclusion N.K_le_H k) = 1 := hk
    rw [hker] at h1
    apply Subtype.ext
    exact hZ _ k.2 fun y hy => h1 y hy
  set psl' : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6 with hpsl'
  have hpslcard : Nat.card psl' = 360 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
  have hnorm' : ∀ a ∈ psl', ∀ g : ↥A6Models.autA6, g * a * g⁻¹ ∈ psl' := by
    intro a ha g
    exact psl29_normal g.1 g.2 a ha
  set Q : Subgroup ↥N.K := psl'.comap ψ with hQ
  have : Q.Normal := ⟨fun n hn g => by
    show ψ (g * n * g⁻¹) ∈ psl'
    rw [map_mul, map_mul, map_inv]
    exact hnorm' _ hn _⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hQ0 | hQ1
  ·
    exfalso
    obtain ⟨k, hk1⟩ : ∃ k : ↥N.K, k ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card ↥N.K = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
      omega
    have hcent : ∀ y ∈ A6Models.psl29, ((ψ k : ↥A6Models.autA6) : P10) * y =
        y * ((ψ k : ↥A6Models.autA6) : P10) := by
      intro y hy
      have hy' : y ∈ A6Models.autA6 := psl29_le_autA6 hy
      obtain ⟨h, hh⟩ := hsurj ⟨y, hy'⟩
      have hy'psl : (⟨y, hy'⟩ : ↥A6Models.autA6) ∈ psl' := Subgroup.mem_subgroupOf.mpr hy
      set kk : ↥N.H := Subgroup.inclusion N.K_le_H k with hkk
      have hmem : ((h * kk⁻¹ * h⁻¹ : ↥N.H) : G) ∈ N.K := by
        show (h : G) * (k : G)⁻¹ * (h : G)⁻¹ ∈ N.K
        exact (Subgroup.mem_normalizer_iff.mp (hKH h.2) _).mp (N.K.inv_mem k.2)
      set k₂ : ↥N.K := ⟨((h * kk⁻¹ * h⁻¹ : ↥N.H) : G), hmem⟩ with hk₂
      have hik₂ : Subgroup.inclusion N.K_le_H k₂ = h * kk⁻¹ * h⁻¹ := Subtype.ext rfl
      have hψk₂ : ψ k₂ = ⟨y, hy'⟩ * (ψ k)⁻¹ * ⟨y, hy'⟩⁻¹ := by
        show Φ (Subgroup.inclusion N.K_le_H k₂) = _
        rw [hik₂, map_mul, map_mul, map_inv, map_inv, hh]
        rfl
      have hw : ψ (k * k₂) ∈ psl' := by
        rw [map_mul, hψk₂]
        have e : ψ k * (⟨y, hy'⟩ * (ψ k)⁻¹ * ⟨y, hy'⟩⁻¹) =
            (ψ k * ⟨y, hy'⟩ * (ψ k)⁻¹) * ⟨y, hy'⟩⁻¹ := by group
        rw [e]
        exact psl'.mul_mem (hnorm' _ hy'psl _) (psl'.inv_mem hy'psl)
      have hkk2 : k * k₂ ∈ Q := hw
      rw [hQ0, Subgroup.mem_bot] at hkk2
      have h1 : ψ (k * k₂) = 1 := by rw [hkk2, map_one]
      rw [map_mul, hψk₂] at h1
      have : ψ k * ⟨y, hy'⟩ = ⟨y, hy'⟩ * ψ k := by
        calc ψ k * ⟨y, hy'⟩
            = (ψ k * (⟨y, hy'⟩ * (ψ k)⁻¹ * ⟨y, hy'⟩⁻¹)) * (⟨y, hy'⟩ * ψ k) := by group
          _ = ⟨y, hy'⟩ * ψ k := by rw [h1, one_mul]
      exact congrArg Subtype.val this
    have hψk : ((ψ k : ↥A6Models.autA6) : P10) = 1 := centralizer_psl29 (ψ k).2 hcent
    apply hk1
    apply hψinj
    apply Subtype.ext
    rw [hψk, map_one]
    rfl
  · have hall : ∀ k : ↥N.K, ψ k ∈ psl' := fun k => by
      have : k ∈ Q := by rw [hQ1]; exact Subgroup.mem_top k
      exact this
    refine ⟨fun k hk => ?_, fun y hy => ?_⟩
    · have := hall ⟨(k : G), hk⟩
      exact Subgroup.mem_subgroupOf.mp this
    · have hy' : y ∈ A6Models.autA6 := psl29_le_autA6 hy
      have hrange : ψ.range ≤ psl' := by
        rintro a ⟨k, rfl⟩
        exact hall k
      have hcr : Nat.card ψ.range = Nat.card N.K := Nat.card_range_of_injective hψinj
      have hrange' : ψ.range = psl' :=
        Subgroup.eq_of_le_of_card_ge hrange (by rw [hpslcard, hcr, hcard])
      have hmem : (⟨y, hy'⟩ : ↥A6Models.autA6) ∈ ψ.range := by
        rw [hrange']; exact Subgroup.mem_subgroupOf.mpr hy
      obtain ⟨k, hk⟩ := hmem
      refine ⟨Subgroup.inclusion N.K_le_H k, k.2, ?_⟩
      have : ψ k = ⟨y, hy'⟩ := hk
      exact congrArg Subtype.val this

theorem exists_a6Datum (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h258 : Facts258 N) (h2521 : Concl2521 N) : Nonempty (A6Datum N) := by
  obtain ⟨e⟩ := h2521.nonempty_autOn
  obtain ⟨eK⟩ := h2521.nonempty_K
  set Φ₀ : ↥N.H →* ↥A6Models.autA6 := e.toMonoidHom.comp (N.actHom hKH) with hΦ₀
  have hΦ₀surj : Function.Surjective Φ₀ := e.surjective.comp (N.actHom_surjective hKH)
  have hker₀ : ∀ h : ↥N.H, Φ₀ h = 1 ↔ ∀ k ∈ N.K, (h : G) * k = k * (h : G) := by
    intro h
    rw [← N.actHom_eq_one_iff hKH h, hΦ₀]
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe]
    exact map_eq_one_iff _ e.injective
  obtain ⟨Φ₁, hΦ₁surj, hΦ₁ker, hΦ₁S, hΦ₁Ssurj⟩ :=
    exists_hom_S_eq_P0 N N.tuple.sylow Φ₀ hΦ₀surj
  have hker₁ : ∀ h : ↥N.H, Φ₁ h = 1 ↔ ∀ k ∈ N.K, (h : G) * k = k * (h : G) :=
    fun h => (hΦ₁ker h).trans (hker₀ h)
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial h258.simple hx hc
  have hcard : Nat.card N.K = 360 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨hKmem, hKsurj⟩ := K_part N hKH h258.simple hZ hcard Φ₁ hΦ₁surj hker₁
  classical
  refine ⟨{ Φ := fun x => if hx : x ∈ N.H then ((Φ₁ ⟨x, hx⟩ : ↥A6Models.autA6) : P10) else 1
            mem := ?_, mul := ?_, surj := ?_, ker := ?_, S_mem := ?_, S_surj := ?_,
            K_mem := ?_, K_surj := ?_ }⟩
  · intro h hh
    simp only [hh, dite_true]
    exact (Φ₁ _).2
  · intro a ha b hb
    simp only [ha, hb, N.H.mul_mem ha hb, dite_true]
    have : (⟨a * b, N.H.mul_mem ha hb⟩ : ↥N.H) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    rfl
  · intro y hy
    obtain ⟨h, hh⟩ := hΦ₁surj ⟨y, hy⟩
    refine ⟨(h : G), h.2, ?_⟩
    simp only [h.2, dite_true]
    have : (⟨(h : G), h.2⟩ : ↥N.H) = h := rfl
    rw [this, hh]
  · intro h hh
    simp only [hh, dite_true]
    rw [← hker₁ ⟨h, hh⟩]
    constructor
    · intro h1
      exact Subtype.ext h1
    · intro h1
      exact congrArg Subtype.val h1
  · intro s hs
    have hsH := N.S_le_H hs
    simp only [hsH, dite_true]
    exact hΦ₁S ⟨s, hsH⟩ hs
  · intro p hp
    obtain ⟨s, hs, hsp⟩ := hΦ₁Ssurj p hp
    refine ⟨(s : G), hs, ?_⟩
    simp only [s.2, dite_true]
    have : (⟨(s : G), s.2⟩ : ↥N.H) = s := rfl
    rw [this, hsp]
  · intro k hk
    have hkH := N.K_le_H hk
    simp only [hkH, dite_true]
    exact hKmem ⟨k, hkH⟩ hk
  · intro y hy
    obtain ⟨k, hk, hky⟩ := hKsurj y hy
    refine ⟨(k : G), hk, ?_⟩
    simp only [k.2, dite_true]
    have : (⟨(k : G), k.2⟩ : ↥N.H) = k := rfl
    rw [this, hky]

namespace A6Datum

variable {N} (D : A6Datum N)

theorem Φ_one : D.Φ 1 = 1 := by
  have h := D.mul 1 N.H.one_mem 1 N.H.one_mem
  rw [one_mul] at h
  exact (mul_left_cancel (a := D.Φ 1) (by rw [mul_one]; exact h)).symm

theorem Φ_inv {a : G} (ha : a ∈ N.H) : D.Φ a⁻¹ = (D.Φ a)⁻¹ := by
  have h := D.mul a ha a⁻¹ (N.H.inv_mem ha)
  rw [mul_inv_cancel, D.Φ_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem Φ_pow {a : G} (ha : a ∈ N.H) (n : ℕ) : D.Φ (a ^ n) = D.Φ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, D.Φ_one]
  | succ n ih => rw [pow_succ, D.mul _ (N.H.pow_mem ha n) a ha, ih, pow_succ]

theorem Φ_conj {a b : G} (ha : a ∈ N.H) (hb : b ∈ N.H) :
    D.Φ (a * b * a⁻¹) = D.Φ a * D.Φ b * (D.Φ a)⁻¹ := by
  rw [D.mul _ (N.H.mul_mem ha hb) _ (N.H.inv_mem ha), D.mul a ha b hb, D.Φ_inv ha]

theorem inv_mul_mem_SC (hK0 : N.K0 = N.K) {a b : G} (ha : a ∈ N.S) (hb : b ∈ N.S)
    (h : D.Φ a = D.Φ b) : a⁻¹ * b ∈ N.SC := by
  have haH := N.S_le_H ha
  have hbH := N.S_le_H hb
  have h1 : D.Φ (a⁻¹ * b) = 1 := by
    rw [D.mul _ (N.H.inv_mem haH) _ hbH, D.Φ_inv haH, h, inv_mul_cancel]
  have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem haH) hbH)).mp h1
  refine ⟨N.S.mul_mem (N.S.inv_mem ha) hb, ?_⟩
  rw [hK0]
  exact Subgroup.mem_centralizer_iff.mpr fun k hk => (h2 k hk).symm

theorem Φ_eq_one_of_mem_SC (hK0 : N.K0 = N.K) {a : G} (ha : a ∈ N.SC) : D.Φ a = 1 := by
  have haH : a ∈ N.H := N.S_le_H (N.SC_le_S ha)
  rw [D.ker a haH]
  intro k hk
  have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer ha) k (hK0 ▸ hk)
  exact this.symm

theorem mem_SC_of_Φ_eq_one (hK0 : N.K0 = N.K) {a : G} (ha : a ∈ N.S) (h1 : D.Φ a = 1) :
    a ∈ N.SC := by
  refine ⟨ha, ?_⟩
  rw [hK0]
  have h2 := (D.ker a (N.S_le_H ha)).mp h1
  exact Subgroup.mem_centralizer_iff.mpr fun k hk => (h2 k hk).symm

theorem exists_mem_SK (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) {d : P10} (hdP : d ∈ P0) (hdpsl : d ∈ A6Models.psl29) :
    ∃ a ∈ N.SK, D.Φ a = d := by
  obtain ⟨s, hs, hsd⟩ := D.S_surj d hdP
  obtain ⟨k, hk, hkd⟩ := D.K_surj d hdpsl
  have hkH := N.K_le_H hk
  have hsH := N.S_le_H hs
  have h1 : D.Φ (k⁻¹ * s) = 1 := by
    rw [D.mul _ (N.H.inv_mem hkH) _ hsH, D.Φ_inv hkH, hkd, hsd, inv_mul_cancel]
  have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem hkH) hsH)).mp h1
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have h3 : k⁻¹ * s ∈ N.S :=
    N.mem_S_of_centralizes hKH h254 hZ (N.H.mul_mem (N.H.inv_mem hkH) hsH) h2
  have hkS : k ∈ N.S := by
    have := N.S.mul_mem hs (N.S.inv_mem h3)
    simpa using this
  exact ⟨k, ⟨hkS, hk⟩, hkd⟩

theorem inj_K (hsimple : IsSimpleGroup ↥N.K) {a b : G} (ha : a ∈ N.K) (hb : b ∈ N.K)
    (h : D.Φ a = D.Φ b) : a = b := by
  have haH := N.K_le_H ha
  have hbH := N.K_le_H hb
  have h1 : D.Φ (a⁻¹ * b) = 1 := by
    rw [D.mul _ (N.H.inv_mem haH) _ hbH, D.Φ_inv haH, h, inv_mul_cancel]
  have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem haH) hbH)).mp h1
  have h3 : a⁻¹ * b = 1 :=
    N.center_K_trivial hsimple (N.K.mul_mem (N.K.inv_mem ha) hb) (fun y hy => h2 y hy)
  exact inv_mul_eq_one.mp h3

theorem card_K_centralizer (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (hsimple : IsSimpleGroup ↥N.K) {u : G} (huH : u ∈ N.H) :
    Nat.card ↥(N.K ⊓ Subgroup.centralizer ({u} : Set G)) =
      Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({D.Φ u} : Set P10)) := by
  have hmemf : ∀ k : ↥(N.K ⊓ Subgroup.centralizer ({u} : Set G)),
      D.Φ (k : G) ∈ A6Models.psl29 ⊓ Subgroup.centralizer ({D.Φ u} : Set P10) := by
    intro k
    refine ⟨D.K_mem _ k.2.1, ?_⟩
    show D.Φ (k : G) ∈ Subgroup.centralizer ({D.Φ u} : Set P10)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hku : (k : G) * u = u * (k : G) := Subgroup.mem_centralizer_singleton_iff.mp k.2.2
    have hkH := N.K_le_H k.2.1
    rw [← D.mul _ hkH _ huH, ← D.mul _ huH _ hkH, hku]
  let f : ↥(N.K ⊓ Subgroup.centralizer ({u} : Set G)) →
      ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({D.Φ u} : Set P10)) :=
    fun k => ⟨D.Φ (k : G), hmemf k⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro k₁ k₂ h
    apply Subtype.ext
    exact D.inj_K hsimple k₁.2.1 k₂.2.1 (congrArg Subtype.val h)
  · rintro ⟨y, hy1, hy2⟩
    obtain ⟨k, hk, hky⟩ := D.K_surj y hy1
    have hkH := N.K_le_H hk
    have hcomm : y * D.Φ u = D.Φ u * y := Subgroup.mem_centralizer_singleton_iff.mp hy2
    have hc : k * u * k⁻¹ * u⁻¹ ∈ N.K := by
      have hu' : u ∈ Subgroup.normalizer (N.K : Set G) := hKH huH
      have : u * k⁻¹ * u⁻¹ ∈ N.K :=
        (Subgroup.mem_normalizer_iff.mp hu' k⁻¹).mp (N.K.inv_mem hk)
      have := N.K.mul_mem hk this
      simpa [mul_assoc] using this
    have hΦc : D.Φ (k * u * k⁻¹ * u⁻¹) = 1 := by
      rw [D.mul _ (N.H.mul_mem (N.H.mul_mem hkH huH) (N.H.inv_mem hkH)) _ (N.H.inv_mem huH),
        D.mul _ (N.H.mul_mem hkH huH) _ (N.H.inv_mem hkH), D.mul _ hkH _ huH, D.Φ_inv hkH,
        D.Φ_inv huH, hky, hcomm]
      group
    have h1 : k * u * k⁻¹ * u⁻¹ = 1 :=
      D.inj_K hsimple hc N.K.one_mem (by rw [hΦc, D.Φ_one])
    have hku : k * u = u * k := by
      calc k * u = (k * u * k⁻¹ * u⁻¹) * (u * k) := by group
        _ = u * k := by rw [h1, one_mul]
    refine ⟨⟨k, hk, Subgroup.mem_centralizer_singleton_iff.mpr hku⟩, ?_⟩
    exact Subtype.ext hky

end A6Datum

end Datum

end CFSG.QuasithinUnique
