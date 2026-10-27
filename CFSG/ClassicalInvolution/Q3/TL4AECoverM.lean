module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverI
public import CFSG.ClassicalInvolution.Q3.TL4AECoverK
public import CFSG.ClassicalInvolution.Q3.TL4AECoverL
public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverG

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement

namespace AECov

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}

theorem eq_one_of_mem_ker_of_mem_commutator (I : AEIdent P k) (hk : 5 ≤ k) (hodd : Odd k)
    (hker : IsPGroup 2 ↥I.φ.ker)
    (hU : ∀ a ∈ (permHom I).ker, ∀ b ∈ (permHom I).ker, a * b = b * a ∧ a * a = 1)
    {z : ↥(pSpan P)} (hz : z ∈ I.φ.ker)
    (hzc : z ∈ ⁅(permHom I).ker, (⊤ : Subgroup ↥(pSpan P))⁆) : z = 1 := by
  set U := (permHom I).ker with hUdef
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => (hU a ha b hb).1
  have hk3 : 3 ≤ k := by omega
  set p₀ : Fin k := ⟨0, by omega⟩ with hp₀
  obtain ⟨u₀, hu₀⟩ := exists_lift_ePt I hodd p₀
  let _ : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with mul_comm := fun a b => Subtype.ext (hUab a a.2 b b.2) }
  set u : Fin k → ↥U := fun p => ⟨pointLift I hk3 p₀ u₀ p, pointLift_mem_ker I hk3 hu₀ p⟩
    with hudef
  set f : ↥U →* AEQ k := I.φ.comp U.subtype with hfdef
  have hf : ∀ p, f (u p) = ePt k p := fun p => map_pointLift I hk3 hu₀ p
  have hu2 : ∀ p, u p * u p = 1 := fun p =>
    Subtype.ext (hU _ (pointLift_mem_ker I hk3 hu₀ p) _ (pointLift_mem_ker I hk3 hu₀ p)).2
  set T : Subgroup ↥(pSpan P) :=
    Subgroup.closure {x | ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ x = ((sv u v : ↥U) : ↥(pSpan P))}
    with hTdef
  have hT : ∀ x ∈ T, ∃ v : Fin k → ZMod 2, ∑ i, v i = 0 ∧ x = ((sv u v : ↥U) : ↥(pSpan P)) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨0, by simp, by rw [sv_zero]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨v, hv, rfl⟩ := ihx
      obtain ⟨w, hw, rfl⟩ := ihy
      refine ⟨v + w, by simp only [Pi.add_apply]; rw [Finset.sum_add_distrib, hv, hw, add_zero],
        ?_⟩
      rw [sv_add u hu2]
      rfl
    | inv x _ ih =>
      obtain ⟨v, hv, rfl⟩ := ih
      refine ⟨v, hv, ?_⟩
      have h2 := (hU _ (sv u v).2 _ (sv u v).2).2
      exact inv_eq_of_mul_eq_one_right h2
  have hcomm : ⁅U, (⊤ : Subgroup ↥(pSpan P))⁆ ≤ T := by
    rw [Subgroup.commutator_le]
    intro a ha x _
    obtain ⟨v, hv, hav⟩ := exists_vec_of_mem_ker_permHom I ha
    set s : ↥U := sv u v with hs
    have hζ : (s : ↥(pSpan P))⁻¹ * a ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hav]
      have hfs : f s = mkQ k (Wr.ofVec v) := f_sv u f hf v
      rw [show I.φ (s : ↥(pSpan P)) = f s from rfl, hfs, inv_mul_cancel]
    have hζc : ∀ g : ↥(pSpan P), g * ((s : ↥(pSpan P))⁻¹ * a) = ((s : ↥(pSpan P))⁻¹ * a) * g :=
      fun g => Subgroup.mem_center_iff.mp (I.ker_le hζ) g
    set σ := (permHom I x : Equiv.Perm (Fin k)) with hσ
    set c : ↥U →* ↥U := (MulAut.conjNormal x).toMonoidHom with hc
    have hcu : ∀ p, c (u p) = u (σ p) := fun p => by
      apply Subtype.ext
      show x * pointLift I hk3 p₀ u₀ p * x⁻¹ = pointLift I hk3 p₀ u₀ (σ p)
      exact conj_pointLift I hk3 hker hUab hu₀ x p
    have hcs : x * (s : ↥(pSpan P)) * x⁻¹ = ((sv u fun q => v (σ.symm q) : ↥U) : ↥(pSpan P)) := by
      have h := map_sv u c σ hcu v
      exact congrArg Subtype.val h
    have hv' : ∑ i, (v + fun q => v (σ.symm q)) i = 0 := by
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, hv, Equiv.sum_comp σ.symm v, hv, add_zero]
    refine Subgroup.subset_closure ⟨v + fun q => v (σ.symm q), hv', ?_⟩
    rw [sv_add u hu2]
    have hs2 : ((sv u fun q => v (σ.symm q) : ↥U) : ↥(pSpan P)) =
        (((sv u fun q => v (σ.symm q) : ↥U) : ↥(pSpan P)))⁻¹ := by
      have h2 := (hU _ (sv u fun q => v (σ.symm q)).2 _ (sv u fun q => v (σ.symm q)).2).2
      exact (mul_eq_one_iff_inv_eq.mp h2).symm
    show ⁅a, x⁆ = (s : ↥(pSpan P)) * ((sv u fun q => v (σ.symm q) : ↥U) : ↥(pSpan P))
    rw [hs2, ← hcs, commutatorElement_def]
    have ha' : a = (s : ↥(pSpan P)) * ((s : ↥(pSpan P))⁻¹ * a) := by group
    calc a * x * a⁻¹ * x⁻¹
        = (s : ↥(pSpan P)) * ((s : ↥(pSpan P))⁻¹ * a) * x * a⁻¹ * x⁻¹ := by rw [← ha']
      _ = (s : ↥(pSpan P)) * (x * ((s : ↥(pSpan P))⁻¹ * a)) * a⁻¹ * x⁻¹ := by
          rw [mul_assoc (s : ↥(pSpan P)), hζc x]
      _ = (s : ↥(pSpan P)) * (x * (s : ↥(pSpan P)) * x⁻¹)⁻¹ := by group
  obtain ⟨v, hv, rfl⟩ := hT z (hcomm hzc)
  have h1 : f (sv u v) = 1 := hz
  rw [eq_one_of_sv u hodd f hf hv h1]
  rfl

end AECov

theorem aeCoverOddKer_proved : AECoverOddKer := by
  intro G _ _ P k I hk hodd hH
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    AECov.comm_of_isUniqueInvolution I hk hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL' hu
      hu'
  have hW := AECov.zSpan_elem hcomm
  have hWn := AECov.zSpan_normal hH.conj_mem
  have hUW := AECov.ker_permHom_le_zSpan I (by omega) hH.card hH.conj_mem hH.label_inj
    hH.ker_two hWn hW
  have hU : ∀ a ∈ (AECov.permHom I).ker, ∀ b ∈ (AECov.permHom I).ker, a * b = b * a ∧ a * a = 1 :=
    fun a ha b hb => hW a (hUW ha) b (hUW hb)
  have h7 := AECov.zSpan_le_commutator I hk hH.card hH.twin_comm
  rw [eq_bot_iff]
  intro z hz
  have hzU : z ∈ (AECov.permHom I).ker := by
    rw [AECov.mem_ker_permHom, MonoidHom.mem_ker.mp hz]
    rfl
  rw [Subgroup.mem_bot]
  exact AECov.eq_one_of_mem_ker_of_mem_commutator I hk hodd hH.ker_two hU hz (h7 (hUW hzU))

end CFSG.ClassicalInvolution.Q3.TL4
