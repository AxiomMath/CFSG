module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversFacts
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CoversUnitaryField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelUnitaryRoot

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped commutatorElement

namespace CoverUnitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] (J : HermitianForm 3 K) {f : ℕ}

@[expose] noncomputable def centerCoord (c : K) : hermitianUnipotentCoord J := by
  classical
  exact if h : J.conj c = c then
    ⟨(0, c), by
      change c + J.conj c + 0 * J.conj 0 = 0
      rw [h, CharTwo.add_self_eq_zero, zero_mul, add_zero]⟩
  else 1

omit [Finite K] in
theorem centerCoord_fst (c : K) : (centerCoord J c).1.1 = 0 := by
  unfold centerCoord
  split_ifs
  · rfl
  · rfl

omit [Finite K] in
theorem centerCoord_snd {c : K} (hc : J.conj c = c) : (centerCoord J c).1.2 = c := by
  unfold centerCoord
  split_ifs
  rfl

omit [Finite K] in
theorem eq_centerCoord {w : hermitianUnipotentCoord J} (hw : w.1.1 = 0) :
    w = centerCoord J w.1.2 :=
  coord_ext (by rw [hw, centerCoord_fst])
    (by rw [centerCoord_snd J (conj_snd_of_fst_eq_zero J hw)])

theorem unitaryCoverRoot_center_commutator (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (w : ProjectiveSpecialUnitaryMatrixGroup J)
    (hw : InCenterOf (unitaryCoverRoot J hJ) w) :
    ∃ a ∈ unitaryCoverRoot J hJ, ∃ b ∈ unitaryCoverRoot J hJ, w = a * b * a⁻¹ * b⁻¹ := by
  obtain ⟨z, hz, rfl⟩ := (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).1 hw
  obtain ⟨β, hβ⟩ := exists_trace_eq J (2 ^ f) hcard hfixed (conj_snd_of_fst_eq_zero J hz)
  obtain ⟨z₁, hz₁⟩ := exists_fst_eq J (2 ^ f) hcard hfixed 1
  obtain ⟨z₂, hz₂⟩ := exists_fst_eq J (2 ^ f) hcard hfixed β
  refine ⟨_, ⟨z₁, rfl⟩, _, ⟨z₂, rfl⟩, ?_⟩
  have hc : ⁅z₁, z₂⁆ = z := coord_ext (by rw [fst_commutator, hz])
    (by rw [snd_commutator, hz₁, hz₂, map_one, mul_one, one_mul, hβ])
  rw [← hc, map_commutatorElement, commutatorElement_def]

theorem coverPairingVanishes_unitaryCoverRoot (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    CoverPairingVanishes (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryCoverRoot J hJ) := by
  intro P h₁ h₂ h₃ h₄ a ha b hb
  set ψ := hermitianUnipotentPSU J hJ
  have hQ : ∀ z, ψ z ∈ unitaryCoverRoot J hJ := fun z => ⟨z, rfl⟩
  have hZ : ∀ w : hermitianUnipotentCoord J, w.1.1 = 0 →
      InCenterOf (unitaryCoverRoot J hJ) (ψ w) :=
    fun w hw => (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).2 ⟨w, hw, rfl⟩
  choose s hs using exists_fst_eq J (2 ^ f) hcard hfixed
  have hR : ∀ z w : hermitianUnipotentCoord J, w.1.1 = 0 →
      P (ψ z) (ψ w) = P (ψ (s z.1.1)) (ψ w) := by
    intro z w hw
    have hc : ((s z.1.1)⁻¹ * z).1.1 = 0 := by rw [fst_mul, fst_inv, hs, neg_add_cancel]
    have hz : z = s z.1.1 * ((s z.1.1)⁻¹ * z) := (mul_inv_cancel_left _ _).symm
    conv_lhs => rw [hz]
    rw [map_mul, h₁ _ (hQ _) _ (hQ _) _ (hZ w hw), h₃ _ _ (hZ _ hc) (hZ w hw), add_zero]
  let F : K → K → ZMod 2 := fun x c => P (ψ (s x)) (ψ (centerCoord J c))
  have hF : ∀ z w : hermitianUnipotentCoord J, w.1.1 = 0 → P (ψ z) (ψ w) = F z.1.1 w.1.2 := by
    intro z w hw
    rw [hR z w hw]
    conv_lhs => rw [eq_centerCoord J hw]
  have hzero := unitary_pairing_eq_zero J hf hcard hfixed F
    (fun x x' c hc => by
      have h := hF (s x * s x') (centerCoord J c) (centerCoord_fst J c)
      rw [fst_mul, hs, hs, centerCoord_snd J hc] at h
      rw [← h, map_mul, h₁ _ (hQ _) _ (hQ _) _ (hZ _ (centerCoord_fst J c))])
    (fun x c c' hc hc' => by
      have h := hF (s x) (centerCoord J c * centerCoord J c')
        (by rw [fst_mul, centerCoord_fst, centerCoord_fst, add_zero])
      rw [hs, snd_mul, centerCoord_snd J hc, centerCoord_snd J hc', centerCoord_fst, zero_mul,
        sub_zero] at h
      rw [← h, map_mul, h₂ _ (hQ _) _ _ (hZ _ (centerCoord_fst J c))
        (hZ _ (centerCoord_fst J c'))])
    (fun k x c hc => by
      have hfst : (hermitianTorusAction J k (centerCoord J c)).1.1 = 0 := by
        rw [hermitianTorusAction_fst, centerCoord_fst, zero_mul, zero_mul]
      have hk := h₄ (hermitianTorusPSU J hJ k) (unitaryCoverTorus_le_normalizer J hJ ⟨k, rfl⟩) _
        (hQ (s x)) _ (hZ _ (centerCoord_fst J c))
      rw [unitaryCoverTorus_conj_root, unitaryCoverTorus_conj_root,
        hF (hermitianTorusAction J k (s x)) (hermitianTorusAction J k (centerCoord J c)) hfst,
        hermitianTorusAction_fst, hermitianTorusAction_snd, hs, centerCoord_snd J hc] at hk
      exact hk)
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨w, hw, rfl⟩ := (inCenterOf_unitaryCoverRoot_iff J hcard hfixed hJ).1 hb
  rw [hF z w hw]
  exact hzero _ _ (conj_snd_of_fst_eq_zero J hw)

theorem benderCoverFacts_unitaryCoverRoot (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    BenderCoverFacts (ProjectiveSpecialUnitaryMatrixGroup J) (unitaryCoverRoot J hJ) :=
  ⟨Or.inr (unitaryCoverRoot_center_commutator J hcard hfixed hJ),
    coverPairingVanishes_unitaryCoverRoot J hf hcard hfixed hJ⟩

end CoverUnitary

theorem unitaryCoverFacts {n : ℕ} (hn : 2 ≤ n) :
    ∃ Q : Sylow 2 ↥(PSU3Model n), BenderCoverFacts ↥(PSU3Model n) (Q : Subgroup _) := by
  let k := GaloisField 2 n
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian n (by omega)
  have : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ n :=
    quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hcard hfixed
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  let P : Sylow 2 (PSU3Model n) := (unitaryCoverSylow J n hn hcard hfixed hJ).mapSurjective
    (f := e.toMonoidHom) fun y => ⟨e.symm y, e.apply_symm_apply y⟩
  have hP : (P : Subgroup (PSU3Model n)) = (unitaryCoverRoot J hJ).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  exact ⟨P, hP ▸ benderCoverFacts_map_mulEquiv e
    (CoverUnitary.benderCoverFacts_unitaryCoverRoot J hn hcard hfixed hJ)⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
