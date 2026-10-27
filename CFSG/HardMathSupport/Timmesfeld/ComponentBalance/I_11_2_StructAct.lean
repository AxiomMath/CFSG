module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Struct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Generic

variable {G : Type*} [Group G]

theorem card_sup_of_commute_of_disjoint {F K : Subgroup G}
    (hc : ∀ f ∈ F, ∀ k ∈ K, f * k = k * f) (hd : Disjoint F K) :
    Nat.card ↥(F ⊔ K) = Nat.card F * Nat.card K := by
  have hcomm : ∀ (m : ↥F) (n : ↥K), Commute (F.subtype m) (K.subtype n) :=
    fun m n => hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod F.subtype K.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨F.subtype_injective, K.subtype_injective, by simpa using hd⟩
  have hrange := MonoidHom.noncommCoprod_range F.subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod]

end Generic


section Act

variable {X : Type} [Group X] {p : ℕ} {B L : Subgroup X}

@[expose] def i112A (B L : Subgroup X) : Subgroup X := Subgroup.normalizer (L : Set X) ⊓ B

@[expose] def i112Bc (B L : Subgroup X) : Subgroup X :=
  B ⊓ Subgroup.centralizer (i112J B L : Set X)

theorem i112A_le_normalizer : i112A B L ≤ Subgroup.normalizer (L : Set X) := inf_le_left

theorem i112A_le_B : i112A B L ≤ B := inf_le_right

theorem mem_i112A {a : X} : a ∈ i112A B L ↔ a ∈ Subgroup.normalizer (L : Set X) ∧ a ∈ B :=
  Subgroup.mem_inf

theorem i112Bc_le_B : i112Bc B L ≤ B := inf_le_left

@[expose] def i112Act (B L : Subgroup X) : ↥(i112A B L) →* MulAut ↥L :=
  L.normalizerMonoidHom.comp (Subgroup.inclusion i112A_le_normalizer)

theorem i112Act_apply (a : ↥(i112A B L)) (l : ↥L) :
    ((i112Act B L a l : ↥L) : X) = a * l * a⁻¹ := rfl

theorem i112Act_eq_one_iff (a : ↥(i112A B L)) :
    i112Act B L a = 1 ↔ (a : X) ∈ Subgroup.centralizer (L : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h l hl
    have := congrArg (fun φ : MulAut ↥L => ((φ ⟨l, hl⟩ : ↥L) : X)) h
    simp only [i112Act_apply, MulAut.one_apply] at this
    rw [InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    refine MulEquiv.ext fun l => Subtype.ext ?_
    rw [i112Act_apply, MulAut.one_apply, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
    exact (h l l.2).symm

theorem i112_Bc_eq (hB : IsElemAbelian p B) :
    i112Bc B L = i112A B L ⊓ Subgroup.centralizer (L : Set X) := by
  ext b
  simp only [i112Bc, i112A, Subgroup.mem_inf]
  constructor
  · rintro ⟨hbB, hbC⟩
    have hcL : b ∈ Subgroup.centralizer (L : Set X) :=
      Subgroup.centralizer_le (fun x hx => i112_orbit_le_J (M := L) i112_self_mem_orbit hx) hbC
    exact ⟨⟨Subgroup.centralizer_le_normalizer (L : Set X) hcL, hbB⟩, hcL⟩
  · rintro ⟨⟨_, hbB⟩, hbC⟩
    refine ⟨hbB, ?_⟩
    have hJ : i112J B L ≤ Subgroup.centralizer ({b} : Set X) := by
      refine i112_J_le fun M hM y hy => ?_
      obtain ⟨g, hg, rfl⟩ := mem_i112Orbit.1 hM
      rw [mem_gLBConj] at hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hbl : Commute b (g * y * g⁻¹) :=
        (Subgroup.mem_centralizer_iff.1 hbC _ hy : (g * y * g⁻¹) * b = b * (g * y * g⁻¹)).symm
      have hbg : Commute b g := i116pI_comm hB hbB hg
      have := (hbg.inv_right.mul_right hbl).mul_right hbg
      rw [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
      exact this.eq.symm
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJ hj)

theorem i112Bc_le_A (hB : IsElemAbelian p B) : i112Bc B L ≤ i112A B L := by
  rw [i112_Bc_eq hB]; exact inf_le_left

theorem i112_center_inf_B_le_Bc :
    (i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓ B ≤ i112Bc B L :=
  fun _ hx => ⟨hx.2, hx.1.2⟩

theorem isElemAbelian_top_of {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (⊤ : Subgroup ↥E) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => Subtype.ext (hE.2 x x.2)⟩
  exact Subtype.ext (mul_comm' (a : ↥E) b)

@[expose] def i112H (B L : Subgroup X) : Subgroup (MulAut ↥L) := (i112Act B L).range

theorem i112_isElemAbelian_H (hB : IsElemAbelian p B) : IsElemAbelian p (i112H B L) := by
  have h := CFSG.SectionRank.isElemAbelian_map
    (isElemAbelian_top_of (isElemAbelian_of_le hB (i112A_le_B (L := L)))) (i112Act B L)
  rwa [← MonoidHom.range_eq_map] at h

theorem i112_card_A (hB : IsElemAbelian p B) [Finite X] :
    Nat.card (i112A B L) = Nat.card (i112H B L) * Nat.card (i112Bc B L) := by
  have h := Subgroup.card_ker_mul_card_range (i112Act B L)
  have hk : (i112Act B L).ker = (i112Bc B L).subgroupOf (i112A B L) := by
    ext a
    rw [MonoidHom.mem_ker, i112Act_eq_one_iff, Subgroup.mem_subgroupOf, i112_Bc_eq hB,
      Subgroup.mem_inf]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hker : Nat.card (i112Act B L).ker = Nat.card (i112Bc B L) := by
    rw [hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (i112Bc_le_A hB)).toEquiv
  rw [← h, hker, mul_comm]
  rfl

theorem i112_card_B [Finite X] :
    Nat.card B = (Subgroup.normalizer (L : Set X)).relIndex B * Nat.card (i112A B L) := by
  have h := Subgroup.card_mul_index ((Subgroup.normalizer (L : Set X)).subgroupOf B)
  have hA : Nat.card ((Subgroup.normalizer (L : Set X)).subgroupOf B) = Nat.card (i112A B L) := by
    rw [← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (L : Set X)) B]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h, hA, mul_comm]
  rfl

theorem i112_pRank_formula [Finite X] (hp : p.Prime) (hB : IsElemAbelian p B)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X)) :
    ∃ r a : ℕ, 1 ≤ r ∧ (Subgroup.normalizer (L : Set X)).relIndex B = p ^ r ∧
      Nat.card (i112H B L) = p ^ a ∧ CFSG.Open.pRank p (i112H B L) = a ∧
      CFSG.Open.pRank p B = r + a + CFSG.Open.pRank p (i112Bc B L) := by
  obtain ⟨r, hr1, hr⟩ := i112_relIndex_eq_pow hp hB hnL
  have hH := i112_isElemAbelian_H (L := L) hB
  have hBc : IsElemAbelian p (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨a, ha⟩ := exists_card_eq_of_isElemAbelian hp hH
  obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian hp hB
  obtain ⟨c, hc⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hcard : p ^ k = p ^ (r + a + c) := by
    rw [← hk, i112_card_B (L := L), hr, i112_card_A hB, ha, hc, pow_add, pow_add, mul_assoc]
  have hkrac : k = r + a + c := Nat.pow_right_injective hp.two_le hcard
  refine ⟨r, a, hr1, hr, ha, pRank_eq_of_card hp.one_lt hH ha, ?_⟩
  rw [pRank_eq_of_card hp.one_lt hB hk, pRank_eq_of_card hp.one_lt hBc hc, hkrac]

theorem i112_pRank_H_le [Finite X] (hp : 1 < p) :
    CFSG.Open.pRank p (i112H B L) ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥L)) :=
  CFSG.SectionRank.pRank_mono hp le_top

theorem i112_exists_inner_of_mem_J [Finite X] (hL : IsComponentOf L ⊤) {j : X}
    (hj : j ∈ i112J B L) : ∃ l ∈ L, ∀ t ∈ L, j * t * j⁻¹ = l * t * l⁻¹ := by
  rw [i112_J_eq_iSup] at hj
  refine Subgroup.iSup_induction (fun M : ↥(i112Orbit B L) => (M : Subgroup X)) hj
    (C := fun j => ∃ l ∈ L, ∀ t ∈ L, j * t * j⁻¹ = l * t * l⁻¹) ?_ ⟨1, L.one_mem, by simp⟩ ?_
  · intro M x hx
    rcases i112_conj_eq_or_commute hL (i112_self_mem_orbit (B := B) (L := L)) M.2 with h | h
    · exact ⟨x, h ▸ hx, fun t _ => rfl⟩
    · refine ⟨1, L.one_mem, fun t ht => ?_⟩
      rw [← h t ht x hx]
      simp
  · rintro x y ⟨lx, hlx, hx⟩ ⟨ly, hly, hy⟩
    refine ⟨lx * ly, L.mul_mem hlx hly, fun t ht => ?_⟩
    have h1 : x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    have h2 : y * t * y⁻¹ = ly * t * ly⁻¹ := hy t ht
    rw [h1, h2, hx _ (L.mul_mem (L.mul_mem hly ht) (L.inv_mem hly))]
    group

theorem i112_not_mem_J_of_not_inner [Finite X] (hL : IsComponentOf L ⊤) {y : ↥(i112A B L)}
    (hy : ¬ IsInnerAut (i112Act B L y)) : (y : X) ∉ i112J B L := by
  intro hyJ
  obtain ⟨l, hl, h⟩ := i112_exists_inner_of_mem_J hL hyJ
  exact hy ⟨⟨l, hl⟩, fun t => Subtype.ext (by
    rw [i112Act_apply]
    exact h t t.2)⟩

theorem i112_orderOf_eq_of_not_inner (hp : p.Prime) (hB : IsElemAbelian p B)
    {y : ↥(i112A B L)} (hy : ¬ IsInnerAut (i112Act B L y)) : orderOf (y : X) = p := by
  have h1 : orderOf (y : X) ∣ p :=
    orderOf_dvd_of_pow_eq_one (hB.2 y (i112A_le_B y.2))
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · exfalso
    have hy1 : (y : X) = 1 := orderOf_eq_one_iff.1 h
    have : y = 1 := Subtype.ext hy1
    exact hy ⟨1, fun t => by simp [this]⟩
  · exact h

theorem i112_card_sup_zpowers [Finite X] (hp : p.Prime) (hB : IsElemAbelian p B)
    (hL : IsComponentOf L ⊤) {y : ↥(i112A B L)} (hy : ¬ IsInnerAut (i112Act B L y))
    {F₀ : Subgroup X} (hF₀ : F₀ ≤ i112J B L) (hc : ∀ f ∈ F₀, f * (y : X) = (y : X) * f) :
    Nat.card ↥(F₀ ⊔ Subgroup.zpowers (y : X)) = p * Nat.card F₀ := by
  have hyJ := i112_not_mem_J_of_not_inner hL hy
  have hyo := i112_orderOf_eq_of_not_inner hp hB hy
  have hzp : Nat.card (Subgroup.zpowers (y : X)) = p := by rw [Nat.card_zpowers, hyo]
  have hdisj : Disjoint F₀ (Subgroup.zpowers (y : X)) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(F₀ ⊓ Subgroup.zpowers (y : X)) ∣ p := by
      rw [← hzp]; exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right : F₀ ⊓ Subgroup.zpowers (y : X) ≤ _)
        (by rw [h, hzp])
      exact hyJ (hF₀ ((heq ▸ Subgroup.mem_zpowers (y : X) : (y : X) ∈ F₀ ⊓ _).1))
  rw [card_sup_of_commute_of_disjoint (fun f hf k hk => ?_) hdisj, hzp, mul_comm]
  obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  exact ((Commute.zpow_right (hc f hf : Commute f (y : X)) z)).eq

theorem i112_zpow_mem_normalizer_iff (hp : p.Prime) (hB : IsElemAbelian p B) {b : X} (hb : b ∈ B)
    (hbn : b ∉ Subgroup.normalizer (L : Set X)) (z : ℤ) :
    b ^ z ∈ Subgroup.normalizer (L : Set X) ↔ (p : ℤ) ∣ z := by
  constructor
  · intro hz
    by_contra hdvd
    have hcop : IsCoprime (p : ℤ) z :=
      (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hdvd
    obtain ⟨u, v, huv⟩ := hcop
    apply hbn
    have hbp : b ^ p = 1 := hB.2 b hb
    have : b = (b ^ z) ^ v := by
      calc b = b ^ ((p : ℤ) * u + z * v) := by
            rw [show (p : ℤ) * u + z * v = 1 by linarith [huv], zpow_one]
        _ = (b ^ p) ^ u * (b ^ z) ^ v := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast]
        _ = (b ^ z) ^ v := by rw [hbp, one_zpow, one_mul]
    rw [this]
    exact (Subgroup.normalizer (L : Set X)).zpow_mem hz v
  · rintro ⟨k, rfl⟩
    have hbp : b ^ p = 1 := hB.2 b hb
    rw [zpow_mul, zpow_natCast, hbp, one_zpow]
    exact Subgroup.one_mem _

theorem i112_conj_pow_injOn [Finite X] (hp : p.Prime) (hB : IsElemAbelian p B) {b : X} (hb : b ∈ B)
    (hbn : b ∉ Subgroup.normalizer (L : Set X)) {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : GLBConj (b ^ i) L = GLBConj (b ^ j) L) : i = j := by
  have h1 : GLBConj (b ^ i * (b ^ j)⁻¹) L = L := by
    rw [← gLBConj_gLBConj, h, gLBConj_inv_gLBConj]
  have h2 : b ^ ((i : ℤ) - j) ∈ Subgroup.normalizer (L : Set X) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
    exact h1
  have h3 := (i112_zpow_mem_normalizer_iff hp hB hb hbn _).1 h2
  have h4 := Int.eq_zero_of_abs_lt_dvd h3 (by rw [abs_lt]; constructor <;> omega)
  omega

theorem i112_orbit_eq_pow [Finite X] (hp : p.Prime) (hB : IsElemAbelian p B)
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = p) {b : X} (hb : b ∈ B)
    (hbn : b ∉ Subgroup.normalizer (L : Set X)) :
    i112Orbit B L = (fun i : ℕ => GLBConj (b ^ i) L) '' (Finset.range p : Set ℕ) := by
  have hinj : Set.InjOn (fun i : ℕ => GLBConj (b ^ i) L) (Finset.range p : Set ℕ) :=
    fun i hi j hj h => i112_conj_pow_injOn hp hB hb hbn (by simpa using hi) (by simpa using hj) h
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ i112_finite_orbit
  · rintro _ ⟨i, -, rfl⟩
    exact i112_gLBConj_mem_orbit (B.pow_mem hb i)
  · rw [i112_ncard_orbit, hidx, hinj.ncard_image, Set.ncard_coe_finset,
      Finset.card_range]

end Act

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
