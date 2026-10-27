module

public import Certificates.Certificate9670
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Finish
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38ShapeTop
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38WeakChecks

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open scoped Matrix

variable {X : Type} [Group X] (K : Subgroup X) [K.Normal]

noncomputable def model9 (e : K ≃* SU) (z : X) (hzc : ∀ k ∈ K, z * k = k * z) (hz9 : z ^ 9 = 1)
    (hz3 : z ^ 3 = ((e.symm omegaSU : K) : X)) (hzmem : ∀ k : ℕ, z ^ k ∈ K → 3 ∣ k) :
    Model9 X where
  ι := K.subtype.comp e.symm.toMonoidHom
  z := z
  ι_inj := Subtype.val_injective.comp e.symm.injective
  z_comm g := hzc _ (e.symm g).2
  z_nine := hz9
  z_cube := hz3
  z_mem k hk := by
    obtain ⟨g, hg⟩ := hk
    exact hzmem k (by rw [← hg]; exact (e.symm g).2)

omit [K.Normal] in
theorem range_model9 (e : K ≃* SU) (z : X) (hzc : ∀ k ∈ K, z * k = k * z) (hz9 : z ^ 9 = 1)
    (hz3 : z ^ 3 = ((e.symm omegaSU : K) : X)) (hzmem : ∀ k : ℕ, z ^ k ∈ K → 3 ∣ k) :
    (model9 K e z hzc hz9 hz3 hzmem).ι.range = K := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    exact (e.symm g).2
  · intro k hk
    exact ⟨e ⟨k, hk⟩, by simp [model9]⟩

theorem le_weakCore_of_order_nine [Finite X] (e : K ≃* SU)
    (z : X) (hzc : ∀ k ∈ K, z * k = k * z) (hz9 : z ^ 9 = 1)
    (hz3 : z ^ 3 = ((e.symm omegaSU : K) : X)) (hzmem : ∀ k : ℕ, z ^ k ∈ K → 3 ∣ k)
    (R : Sylow 3 X) : K ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) := by
  set M := model9 K e z hzc hz9 hz3 hzmem with hM
  have hG : ∀ k < 2, checkG M.repSys.sc M.repSys.valid y9Data k = true := by
    intro k hk
    interval_cases k
    exacts [checkG_y9_zero, checkG_y9_one]
  obtain ⟨E, hEab, -, hrange⟩ := range_le_weakCore_of_repSys_top M.repSys M.ι y9Data y9Gen
    checkE_y9 hG Certificates.certificate9670 rfl
    (by intro k hk; interval_cases k <;> rfl) (by
      intro k hk g hgk
      have hsz9 : (y9Gen.gens.getD k #[]).size = 9 := by interval_cases k <;> rfl
      refine ⟨hsz9, rfl, g, 0, ?_, ?_⟩
      · rw [hgk.symm, pow_zero, one_smul]
      · simp)
  rw [hM, range_model9] at hrange
  exact normal_le_weakCore_sylow K E hEab hrange R

end CFSG.AGLEmbedding.ChevOuter.U38
