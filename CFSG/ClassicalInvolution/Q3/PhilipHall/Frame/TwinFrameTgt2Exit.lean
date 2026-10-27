module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open scoped commutatorElement

section Shape

@[expose] def ExitE4At (H : Type) [Group H] : Prop :=
  TwinE4 H ∨ TightE4 H ∨
    ∃ f : H →* CFSG.Blueprint.NativeSporadic.Carrier .M12,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker

variable {H : Type} [Group H] [Finite H]

theorem ExitE4At.exists_simple (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM : ModelFactM12)
    (h : ExitE4At H) :
    ∃ (Q : Type) (_ : Group Q) (_ : IsSimpleGroup Q) (f : H →* Q), Function.Surjective f ∧
      IsPGroup 2 ↥f.ker ∧ ((∃ a b : Q, a * b ≠ b * a) → Q3NM.AutOddFree Q) := by
  rcases h with h | h | ⟨f, hfs, hf2⟩
  · obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
    have : Finite Q := Finite.of_surjective f hfs
    rcases hQ with hQ | hQ
    · have := isSimple_of_psp hQ
      exact ⟨Q, inferInstance, inferInstance, f, hfs, hf2,
        fun hnab => autOddFree_of_sp62 hSp hQ hnab⟩
    · have := isSimple_of_pomegaPlus hQ
      exact ⟨Q, inferInstance, inferInstance, f, hfs, hf2, fun _ => hD4 Q hQ⟩
  · obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := TightE4.twinE4 h
    have : Finite Q := Finite.of_surjective f hfs
    rcases hQ with hQ | hQ
    · have := isSimple_of_psp hQ
      exact ⟨Q, inferInstance, inferInstance, f, hfs, hf2,
        fun hnab => autOddFree_of_sp62 hSp hQ hnab⟩
    · have := isSimple_of_pomegaPlus hQ
      exact ⟨Q, inferInstance, inferInstance, f, hfs, hf2, fun _ => hD4 Q hQ⟩
  · have := hM.1
    exact ⟨_, inferInstance, inferInstance, f, hfs, hf2, fun _ => hM.2⟩

end Shape

section Moved

variable {G : Type} [Group G] [Finite G]

theorem autOddFree_of_exit_moved {H : Subgroup G} (hH : IsSubnormal H ⊤) {Q : Type} [Group Q]
    [IsSimpleGroup Q] (f : (↥H ⧸ classicalInvolutionOddCore ↥H) →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 ↥f.ker)
    (hQ : (∃ a b : Q, a * b ≠ b * a) → Q3NM.AutOddFree Q) {τ : G} (hτ : τ ∈ H)
    {L : Subgroup (G ⧸ componentClassificationOddCore G)} (hL : CFSG.IsComponent L)
    (hmv : ∃ y ∈ L, QuotientGroup.mk' (componentClassificationOddCore G) τ * y ≠
      y * QuotientGroup.mk' (componentClassificationOddCore G) τ) :
    Q3NM.AutOddFree ↥L := by
  set N := componentClassificationOddCore G with hN
  set M := classicalInvolutionOddCore ↥H with hM
  obtain ⟨χ, hχ, hχmk, hχR⟩ := TL4.exists_oddQuot_embedding hH
  set x : ↥H ⧸ M := QuotientGroup.mk' M ⟨τ, hτ⟩ with hx
  have hχx : χ x = QuotientGroup.mk' N τ := hχmk ⟨τ, hτ⟩
  have hHm : H.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hH
      Subgroup.IsSubnormal.top
  have hRm : χ.range.IsSubnormal := by
    rw [hχR]
    exact hHm.map (QuotientGroup.mk'_surjective N)
  have hτR : QuotientGroup.mk' N τ ∈ χ.range := ⟨x, hχx⟩
  have hle : L ≤ χ.range := by
    rcases CFSG.LocalCores.component_subnormal_subgroup hL hRm with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hne⟩ := hmv
      apply hne
      have hc := Subgroup.commutator_mem_commutator hy hτR
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
  set χ' : (↥H ⧸ M) ≃* ↥χ.range := MonoidHom.ofInjective hχ with hχ'
  have hL₂ : CFSG.IsComponent (L.comap χ) := by
    have h1 := CFSG.LocalCores.isComponent_map_mulEquiv χ'.symm
      (CFSG.LocalCores.component_overgroup hL hle)
    have h2 : (L.subgroupOf χ.range).map χ'.symm.toMonoidHom = L.comap χ := by
      ext z
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_subgroupOf,
        Subgroup.mem_comap]
      rfl
    rwa [h2] at h1
  have hAO : Q3NM.AutOddFree ↥(L.comap χ) := autOddFree_component_of_surj f hf hk hL₂ hQ
  have e : ↥(L.comap χ) ≃* ↥L := by
    refine MulEquiv.ofBijective
      (((χ.comp (L.comap χ).subtype).codRestrict L fun y => Subgroup.mem_comap.mp y.2) :
        ↥(L.comap χ) →* ↥L) ⟨?_, ?_⟩
    · intro a b hab
      apply Subtype.ext
      apply hχ
      exact congrArg Subtype.val hab
    · intro y
      have := hle y.2
      obtain ⟨w, hw⟩ := this
      exact ⟨⟨w, by rw [Subgroup.mem_comap, hw]; exact y.2⟩, Subtype.ext hw⟩
  exact Q3NM.AutOddFree.of_mulEquiv e hAO

end Moved

section Hyp

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_autOddFree {B : Subgroup G} (hB : IsElemAbelian 2 B) {a c : G} (haB : a ∈ B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G))
    (hU : ∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) →
      (∃ y ∈ L₂, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) → L₁ = L₂)
    (hAO : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      Q3NM.AutOddFree ↥L) : Hyp51At B c :=
  TL4.hyp51At_of_moved (fun b hb => (sq b).symm.trans (hB.2 b hb))
    (fun b hb b' hb' => congrArg Subtype.val (hB.1.is_comm.comm (⟨b, hb⟩ : B) ⟨b', hb'⟩))
    ⟨oddQuotMk c ⟨a, haC⟩, oddQuotMk_mem_modOdd haB haC,
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC, hU⟩
    (fun L hL hm _ _ _ _ => (hAO L hL hm).on _)

end Hyp

section ExitAt

variable {G : Type} [Group G] [Finite G]

@[expose] def ExitAt (M : Subgroup G) (c z : G) (hzc : z ∈ Subgroup.centralizer ({c} : Set G)) :
    Prop :=
  ∃ _ : (⟨z, hzc⟩ : Subgroup.centralizer ({c} : Set G)) ∈ secH M c, ExitE4At (SecQ M c)

theorem ExitAt.autOddFree (hSp : ModelFactSp62) (hD4 : ModelFactD42) (hM : ModelFactM12)
    {M : Subgroup G} {c z : G} {hzc : z ∈ Subgroup.centralizer ({c} : Set G)}
    (h : ExitAt M c z hzc) {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L)
    (hmv : ∃ y ∈ L, oddQuotMk c ⟨z, hzc⟩ * y ≠ y * oddQuotMk c ⟨z, hzc⟩) :
    Q3NM.AutOddFree ↥L := by
  obtain ⟨ht, hex⟩ := h
  obtain ⟨Q, _, _, f, hf, hk, hQ⟩ := hex.exists_simple hSp hD4 hM
  exact autOddFree_of_exit_moved (isSubnormal_subnormalClosure _) f hf hk hQ ht hL hmv

end ExitAt

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
