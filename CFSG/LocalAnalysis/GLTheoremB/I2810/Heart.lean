module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.LocalAnalysis.GLTheoremB.I2810.HeartQuot
import CFSG.LocalAnalysis.GLTheoremB.I2810.Step0Basic
import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section CaseOneTwo
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem S_cases (h : Setup28 W K S) {a : X} (haS : a ∈ S) (hna : a ∉ kerAct W K S)
    (hc : Nat.card ↥(indAut W K S) = 2) : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S := by
  have hidx : ((kerAct W K S).subgroupOf S).index = 2 := by
    have h1 := InducedAux.card_indAut h (le_refl S)
    rw [hc] at h1
    exact h1.symm
  intro s hs
  by_contra hcon
  push Not at hcon
  have hmul := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨a⁻¹, S.inv_mem haS⟩ : ↥S))
    (b := (⟨s, hs⟩ : ↥S))
  have hiff : (⟨a⁻¹, S.inv_mem haS⟩ : ↥S) ∈ (kerAct W K S).subgroupOf S ↔
      (⟨s, hs⟩ : ↥S) ∈ (kerAct W K S).subgroupOf S := by
    simp only [Subgroup.mem_subgroupOf]
    exact iff_of_false (fun h' => hna (by simpa using (kerAct W K S).inv_mem h')) hcon.1
  exact hcon.2 (Subgroup.mem_subgroupOf.mp (hmul.mpr hiff))

theorem ccent_normalizes (h : Setup28 W K S) {k : X} (hkS : ∀ s ∈ S, ⁅k, s⁆ ∈ kerAct W K S) :
    k ∈ Subgroup.normalizer (S : Set X) := by
  refine Subgroup.mem_normalizer_fintype (S := (S : Set X)) fun n hn => ?_
  have h1 : k * n * k⁻¹ = ⁅k, n⁆ * n := by simp only [commutatorElement_def]; group
  rw [SetLike.mem_coe, h1]
  exact S.mul_mem (hkS n hn).1 hn

theorem heart_s3_quot (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    {p : X} (hp : p ∈ K) (hp3 : p ^ 3 = 1) (hpn : p ∉ kerAct W K S)
    (hpa : a * p * a⁻¹ * p ∈ kerAct W K S) :
    CFSG.QuasithinUnique.IsSylowTwoOf S (S ⊔ Subgroup.zpowers p) ∧
      CFSG.QuasithinUnique.CharTwo (S ⊔ Subgroup.zpowers p) ∧
      pCoreOf 2 (S ⊔ Subgroup.zpowers p) = kerAct W K S ∧
      Nonempty (↥(S ⊔ Subgroup.zpowers p) ⧸ CFSG.pCore 2 ↥(S ⊔ Subgroup.zpowers p) ≃*
        Equiv.Perm (Fin 3)) :=
  HeartQuot.quot_aux h hR haS hna hS2 hp hp3 hpn hpa

theorem heart_s3 (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (hna : a ∉ kerAct W K S) (hS2 : ∀ s ∈ S, s ∈ kerAct W K S ∨ a⁻¹ * s ∈ kerAct W K S)
    {p : X} (hp : p ∈ K) (hp3 : p ^ 3 = 1) (hpn : p ∉ kerAct W K S)
    (hpa : a * p * a⁻¹ * p ∈ kerAct W K S) :
    (∃ C : Subgroup X, C ≠ ⊥ ∧ IsCharIn C S ∧ p ∈ Subgroup.normalizer (C : Set X)) ∨
      ∀ w ∈ kerAct W K S, ⁅p, w⁆ ∈ vOf W K S := by
  obtain ⟨hT, hF, hcore, ⟨e⟩⟩ := heart_s3_quot h hR haS hna hS2 hp hp3 hpn hpa
  have hpX : p ∈ S ⊔ Subgroup.zpowers p := Subgroup.mem_sup_right (Subgroup.mem_zpowers p)
  rcases GL83.I_28_3_S3_proved X (S ⊔ Subgroup.zpowers p) S hT hF ⟨e⟩ with
    ⟨C, hCS, hC0, hCchar, hXC⟩ | hX3
  · left
    refine ⟨C, hC0, ⟨hCS, fun ψ x hx => ?_⟩, hXC hpX⟩
    have hmem : ψ.symm (ψ x) ∈ C.subgroupOf S := by
      rw [MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]; exact hx
    have h1 : ψ x ∈ (C.subgroupOf S).comap ψ.symm.toMonoidHom := hmem
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.characteristic_iff_comap_le.mp hCchar) ψ.symm h1)
  · right
    intro w hw
    have hp1 : p ≠ 1 := fun h1 => hpn (h1 ▸ (kerAct W K S).one_mem)
    obtain ⟨-, hle, -⟩ := hX3 p hpX hp3 hp1
    rw [hcore] at hle
    have hV : CFSG.Quasithin.omegaOneCenterOf (kerAct W K S) = vOf W K S :=
      (CFSG.Quasithin.omegaOneCenterOf_eq _).trans (s0_omegaZ_eq_quasithin _).symm
    rw [hV] at hle
    have hw' : ⁅w, p⁆ ∈ ⁅kerAct W K S, Subgroup.zpowers p⁆ :=
      Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers p)
    have h2 : ⁅p, w⁆ = ⁅w, p⁆⁻¹ := (commutatorElement_inv w p).symm
    rw [h2]
    exact (vOf W K S).inv_mem (hle hw')

end CaseOneTwo

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
