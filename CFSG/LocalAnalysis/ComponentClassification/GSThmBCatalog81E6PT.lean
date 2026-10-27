module

public import CFSG.GH74.Orders.LieType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8Sp4

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X]

theorem card_sec8J {Y : Type} [Group Y] {p f : ℕ} (h : IsSec8JType Y p f) :
    Nat.card Y = Open.ordA 1 (p ^ (2 * f)) := by
  rcases h with hL | ⟨rfl, rfl, ⟨eA⟩⟩
  · exact GH74.card_of_lieModel_PSL (by norm_num) hL
  · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem ordA_dvd_card_fstar [Finite X] {J : Subgroup X} {p f : ℕ}
    (hJt : IsSec8JType (J ⧸ pPrimeCore 2 J) p f) (hJF : J ≤ generalizedFitting X) :
    Open.ordA 1 (p ^ (2 * f)) ∣ Nat.card (generalizedFitting X) := by
  rw [← card_sec8J hJt]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hJF)

theorem ordBC_two_mul {q : ℕ} (hq : Odd q) :
    Open.ordBC 2 q * 2 = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨k, rfl⟩ := hq
  have hg : Nat.gcd 2 (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    exact Nat.gcd_mul_right_right k 2
  have hdvd : 2 ∣ (2 * k + 1) ^ (2 * 2) * ∏ i ∈ Finset.Icc 1 2, ((2 * k + 1) ^ (2 * i) - 1) := by
    refine Dvd.dvd.mul_left ?_ _
    rw [show Finset.Icc 1 2 = {1, 2} by rfl, Finset.prod_pair (by norm_num)]
    refine Dvd.dvd.mul_right ?_ _
    exact ⟨2 * k * k + 2 * k, by ring_nf; omega⟩
  rw [Open.ordBC, hg, Nat.div_mul_cancel hdvd, show Finset.Icc 1 2 = {1, 2} by rfl,
    Finset.prod_pair (by norm_num)]

theorem card_socle_cases {Y : Type} [Group Y] {p f : ℕ} (hp2 : p ≠ 2)
    (h : IsSec8Socle Y p f) : Nat.card Y = Open.ordBC 2 (p ^ f) ∨ Nat.card Y = 20160 := by
  rcases h with hL | ⟨-, -, ⟨eA⟩⟩
  · exact Or.inl (GH74.card_of_lieModel_PSp (by norm_num) hp2 hL)
  · right
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem le_card_socle {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h : IsSec8Socle Y p f) : 20160 ≤ Nat.card Y := by
  rcases h with hL | ⟨-, -, ⟨eA⟩⟩
  · rw [GH74.card_of_lieModel_PSp (by norm_num) hp2 hL]
    have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have hq3 : 3 ≤ p ^ f := le_trans (by have := hp.two_le; omega)
      (Nat.le_self_pow (by omega) p)
    have h2 := ordBC_two_mul hq
    have h4 : 81 ≤ (p ^ f) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
    have hsq : 9 ≤ (p ^ f) ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
    have h8 : 8 ≤ (p ^ f) ^ 2 - 1 := by omega
    have h80 : 80 ≤ (p ^ f) ^ 4 - 1 := by omega
    have : 81 * (8 * 80) ≤ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
      Nat.mul_le_mul h4 (Nat.mul_le_mul h8 h80)
    omega
  · rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem commutator_eq_of_isPComp {C M : Subgroup X} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) : ⁅M, M⁆ = M := by
  have h := Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hM)
  have h2 := congrArg (Subgroup.map C.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hMC] at h2

theorem le_card_of_socle [Finite X] {K : Subgroup X} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hKt : IsSec8Socle (K ⧸ pPrimeCore 2 K) p f) : 20160 ≤ Nat.card K :=
  (le_card_socle hp hp2 hf hKt).trans
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _))

theorem le_derivedSeries_of_perfect' (K : Subgroup X) (hK : ⁅K, K⁆ = K) (n : ℕ) :
    K ≤ derivedSeries X n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← hK]
    exact Subgroup.commutator_mono ih ih

theorem conjNormal_injective' (N : Subgroup X) [N.Normal] (hC : centralizer (N : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro t ht
  rw [← hC, mem_centralizer_iff]
  intro g hg
  have h1 := congrArg (fun φ : MulAut N => ((φ ⟨g, hg⟩ : N) : X)) (MonoidHom.mem_ker.mp ht)
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc g * t = t * g * t⁻¹ * t := by rw [h1]
    _ = t * g := by group

theorem le_fstar_of_perfect {G : Type*} [Group G]
    (hC : centralizer (generalizedFitting X : Set X) = ⊥) (e : ↥(generalizedFitting X) ≃* G)
    {n : ℕ} (hG : derivedSeries (MulAut G) n ≤ (MulAut.conj : G →* MulAut G).range)
    {K : Subgroup X} (hK : ⁅K, K⁆ = K) : K ≤ generalizedFitting X := by
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  set φ : X →* MulAut G := (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal with hφdef
  have hφ : Function.Injective φ :=
    (MulAut.congr e).injective.comp (conjNormal_injective' _ hC)
  intro k hk
  have h1 : φ k ∈ derivedSeries (MulAut G) n :=
    map_derivedSeries_le_derivedSeries φ n ⟨k, le_derivedSeries_of_perfect' K hK n hk, rfl⟩
  obtain ⟨g, hg⟩ := hG h1
  have h2 : φ ((e.symm g : ↥(generalizedFitting X)) : X) = MulAut.conj g := by
    ext x
    have h3 : (MulAut.conjNormal ((e.symm g : ↥(generalizedFitting X)) : X)) (e.symm x) =
        e.symm g * e.symm x * (e.symm g)⁻¹ := Subtype.ext (by simp [MulAut.conjNormal_apply])
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulAut.conj_apply, h3, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rw [← hφ (h2.trans hg)]
  exact (e.symm g).2

theorem eq_one_of_card_le [Finite X] {K : Subgroup X} {b : X}
    (hC : centralizer (generalizedFitting X : Set X) = ⊥) (hKF : K ≤ generalizedFitting X)
    (hKb : K ≤ centralizer ({b} : Set X))
    (hcard : Nat.card (generalizedFitting X) ≤ Nat.card K) : b = 1 := by
  have hK : K = generalizedFitting X := eq_of_le_of_card_ge hKF hcard
  have hb : b ∈ centralizer (generalizedFitting X : Set X) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, ← hK] at hy
    exact (mem_centralizer_iff.mp (hKb hy) b rfl).symm
  rw [hC, mem_bot] at hb
  exact hb

theorem sq_dvd_ordA' {q : ℕ} (hq : Odd q) : q ^ 2 ∣ Open.ordA 1 (q ^ 2) := by
  obtain ⟨k, rfl⟩ := hq
  have hg : Nat.gcd 2 ((2 * k + 1) ^ 2 - 1) = 2 := by
    rw [show (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * k + 2 * k) by ring_nf; omega]
    exact Nat.gcd_mul_right_right _ 2
  have h2 : 2 ∣ ((2 * k + 1) ^ 2) ^ 2 - 1 :=
    ⟨2 * ((2 * k + 1) ^ 2 * (k * k + k)) + 2 * k * k + 2 * k, by ring_nf; omega⟩
  rw [Open.ordA, hg, show Finset.Icc 2 (1 + 1) = {2} by rfl, Finset.prod_singleton,
    show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, Nat.mul_div_assoc _ h2]
  exact Dvd.intro _ rfl

theorem sq_dvd_of_sq_dvd_two_pow_mul {q a M : ℕ} (hq : Odd q) (h : q ^ 2 ∣ 2 ^ a * M) :
    q ^ 2 ∣ M :=
  (Nat.Coprime.pow 2 a (Nat.coprime_two_right.mpr hq)).dvd_of_dvd_mul_left h

end CFSG.ComponentClassification.GSThmB.P211
