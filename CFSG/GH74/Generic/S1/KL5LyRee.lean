module

public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExOrd
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly

public section

namespace CFSG.GH74.Generic.S1

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ClassicalInvolution CFSG.Sporadic.Ly
  CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Proofs2.Ivk94

theorem kl5_pow_three_mul_not_dvd_fact_eleven {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    ¬ p ^ (3 * f) ∣ 39916800 := by
  intro h
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h1
    · simp at h5
    · exact h1
  have hpd : p ∣ Nat.factorial 11 :=
    (dvd_pow_self p (by omega : 3 * f ≠ 0)).trans (by simpa [Nat.factorial] using h)
  have hp11 : p ≤ 11 := (hp.dvd_factorial).1 hpd
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpow : ∀ m : ℕ, m ≤ 3 * f → p ^ m ∣ 39916800 := fun m hm =>
    (pow_dvd_pow p hm).trans h
  have hcases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    interval_cases p <;> first | omega | exact absurd hp (by norm_num)
  rcases hcases with rfl | rfl | rfl | rfl
  · have h2 : 2 ≤ f := by
      by_contra hlt
      have : f = 1 := by omega
      subst this
      omega
    have := hpow 6 (by omega)
    omega
  all_goals
    have := hpow 3 (by omega)
    omega

theorem kl5_card_centralizer_ly {S : Type} [Group S] (hS : NativeSporadic.IsSporadic S .Ly) {y : S}
    (hy : orderOf y = 2) : Nat.card ↥(centralizer ({y} : Set S)) = 39916800 := by
  obtain ⟨hkey, -, -, hK⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  obtain ⟨e⟩ := hS
  let e' : S ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
    (Subgroup.mem_top _) hord
  have eqv := (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
    (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
    (by rw [hc]; simp)).trans
    ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey))
  rw [Nat.card_congr eqv.toEquiv]
  exact hK

theorem kl5_false_ly {S : Type} [Group S] (hS : NativeSporadic.IsSporadic S .Ly) {A : Subgroup S}
    {b : S} (hb2 : orderOf b = 2) (hAb : ∀ a ∈ A, a * b = b * a) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hcube : p ^ (3 * f) ∣ Nat.card ↥A) : False := by
  have hle : A ≤ centralizer ({b} : Set S) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.2 (hAb a ha)
  have h1 : Nat.card ↥A ∣ Nat.card ↥(centralizer ({b} : Set S)) := Subgroup.card_dvd_of_le hle
  rw [kl5_card_centralizer_ly hS hb2] at h1
  exact kl5_pow_three_mul_not_dvd_fact_eleven hp hp2 h5 (hcube.trans h1)

theorem kl5_false_ree
    {S : Type} [Group S] {f' : ℕ}
    (hS : LieModel S .twistedG2 0 3 f') (h16 : 16 ∣ Nat.card S) : False := by
  obtain ⟨k, -, hcard⟩ := CFSG.GH74.card_of_lieModel_twistedG2 hS
  rw [hcard] at h16
  have := ordRee_pow_three_mod k
  omega

end CFSG.GH74.Generic.S1
