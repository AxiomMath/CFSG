module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJMain

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
  CFSG.EvenSporadicStandard.Wong77.Module CFSG.RankThree.PartTwo.Sec4.Census

theorem golay_three_points_independent {X : Type*} [Group X] (φ : Multiplicative Word →* X)
    (hker : ∀ w : Word, φ (Multiplicative.ofAdd w) = 1 ↔ w ∈ golayCode) (a b d : ZMod 2)
    (h : φ (eVec 1) ^ a.val * φ (eVec 2) ^ b.val * φ (eVec 3) ^ d.val = 1) :
    a = 0 ∧ b = 0 ∧ d = 0 := by
  rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul] at h
  have hw : Multiplicative.toAdd (eVec 1 ^ a.val * eVec 2 ^ b.val * eVec 3 ^ d.val) ∈
      golayCode := (hker _).mp h
  have key : ∀ a b d : ZMod 2, (a = 0 ∧ b = 0 ∧ d = 0) ∨
      (Multiplicative.toAdd (eVec 1 ^ a.val * eVec 2 ^ b.val * eVec 3 ^ d.val) ≠ 0 ∧
        hammingNorm (Multiplicative.toAdd (eVec 1 ^ a.val * eVec 2 ^ b.val * eVec 3 ^ d.val)) <
          7) := by decide
  rcases key a b d with h0 | ⟨hne, hlt⟩
  · exact h0
  · exact absurd (le_hammingNorm_of_mem_golayCode _ hw hne) (by omega)

theorem sporadicCoverRankInput_Fi22 :
    SporadicCoverRankInput .Fi22 := by
  intro Q _ _ hQ hZ2 hS
  obtain ⟨t, htZ, ht2, -⟩ := exists_center_eq_zpowers hZ2
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at ht2; omega
  have hQo := ((Foundations.SteinbergCA.quasisimple_iff Q).2.2.1).mp hQ
  obtain ⟨ψ, -⟩ := exists_iso_Cd hQo hZ2 hS htZ ht1
  obtain ⟨φ, T, hker, -, hD23, hTc, -, hT⟩ := fi23_frame
  have hφT : ∀ i, φ (eVec i) ∈ Cd := fun i => hTc ((hT _ (hD23 i)).2 ⟨i, rfl⟩)
  have hsqJ : ∀ i, φ (eVec i) * φ (eVec i) = 1 := fun i => by
    rw [← map_mul, ← map_one φ]
    congr 1
    apply Multiplicative.toAdd.injective
    funext j
    simp only [eVec, toAdd_mul, toAdd_ofAdd, toAdd_one, Pi.add_apply, Pi.zero_apply]
    exact ZModModule.add_self _
  have hcommJ : ∀ i j, φ (eVec i) * φ (eVec j) = φ (eVec j) * φ (eVec i) := fun i j => by
    rw [← map_mul, ← map_mul, mul_comm]
  set u : Fin 23 → Q := fun i => ψ.symm ⟨φ (eVec i), hφT i⟩ with hu
  have hψu : ∀ i, ((ψ (u i) : Cd) : J) = φ (eVec i) := fun i => by
    simp only [hu, MulEquiv.apply_symm_apply]
  have hinj : Function.Injective (fun q : Q => ((ψ q : Cd) : J)) :=
    Subtype.val_injective.comp ψ.injective
  have hval : ∀ q q' : Q, ((ψ (q * q') : Cd) : J) = ((ψ q : Cd) : J) * ((ψ q' : Cd) : J) :=
    fun q q' => by rw [map_mul, Subgroup.coe_mul]
  have hsq : ∀ i, u i * u i = 1 := fun i => hinj (by
    simp only [hval, hψu, hsqJ, map_one, Subgroup.coe_one])
  have hcomm : ∀ i j, u i * u j = u j * u i := fun i j => hinj (by
    simp only [hval, hψu, hcommJ])
  refine three_le_pRank_of_involutions (hsq 1) (hsq 2) (hsq 3) (hcomm 1 2) (hcomm 1 3)
    (hcomm 2 3) fun a b d h => golay_three_points_independent φ hker a b d ?_
  have h' := congrArg (fun q : Q => ((ψ q : Cd) : J)) h
  simpa only [hval, map_pow, Subgroup.coe_pow, hψu, map_one, Subgroup.coe_one] using h'

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
