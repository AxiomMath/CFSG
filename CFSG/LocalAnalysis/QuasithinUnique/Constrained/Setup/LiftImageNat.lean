module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBaumannNat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyDeleted

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement
open Projectivization

universe v

section Image

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem hglob_of_natural (hnat : NaturalFamily H F r Lc) :
    ∀ i A, IsMinOffender H A → ⁅Lc i, A⁆ ≠ ⊥ → A ≤ Lc i := by
  intro i A hA hmove
  have h := le_blockB_gen hA hmove
  rwa [hnat.B_eq i] at h

theorem natural_thompson_image (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)) (𝓔 : Set (Subgroup (V ≃ₗ[ZMod 2] V)))
    (hE : ∀ E ∈ 𝓔, E ≤ T ∧ (E = ⊥ ∨ IsOffender H E))
    (hDn : ((⨆ E ∈ 𝓔, E).subgroupOf T).Normal) (hne : (⨆ E ∈ 𝓔, E) ≠ ⊥) :
    (⨆ E ∈ 𝓔, E) = ⨆ i, T ⊓ Lc i := by
  classical
  have hglob := hglob_of_natural hnat
  apply le_antisymm
  · refine iSup₂_le fun E hE' => ?_
    obtain ⟨hET, hE0⟩ := hE E hE'
    rcases hE0 with rfl | hoff
    · exact bot_le
    obtain ⟨I, U, hI, hUS, rfl⟩ := (natural_offender_iff ctx hglob E).1 hoff
    refine iSup₂_le fun i hi => ?_
    exact le_iSup_of_le i (le_inf ((le_iSup₂_of_le i hi le_rfl).trans hET) (hUS i hi).1)
  · obtain ⟨E, hE', hE0⟩ : ∃ E ∈ 𝓔, E ≠ ⊥ := by
      by_contra hno
      push Not at hno
      apply hne
      refine le_bot_iff.1 (iSup₂_le fun E hE' => ?_)
      rw [hno E hE']
    have hoff : IsOffender H E := ((hE E hE').2).resolve_left hE0
    obtain ⟨I, U, hI, hUS, rfl⟩ := (natural_offender_iff ctx hglob E).1 hoff
    obtain ⟨i0, hi0⟩ := hI
    have hED : (⨆ i ∈ I, U i) ≤ ⨆ E ∈ 𝓔, E := le_iSup₂_of_le _ hE' le_rfl
    have hUle : U i0 ≤ T ⊓ Lc i0 :=
      le_inf ((le_iSup₂_of_le i0 hi0 le_rfl).trans (hE _ hE').1) (hUS i0 hi0).1
    have hTU : T ⊓ Lc i0 = U i0 :=
      (isSylowOf_two_of (hUS i0 hi0)).eq_of_le hUle inf_le_right (hU i0).2.1
    have hi0D : T ⊓ Lc i0 ≤ ⨆ E ∈ 𝓔, E :=
      hTU.le.trans ((le_iSup₂_of_le i0 hi0 le_rfl).trans hED)
    refine iSup_le fun j => ?_
    intro x hx
    obtain ⟨t, ht, hconj⟩ := ctx.layer.transitive i0 j
    have hxj : x ∈ (Lc i0).map (MulAut.conj t).toMonoidHom := by rw [hconj]; exact hx.2
    obtain ⟨z, hz, hzx⟩ := hxj
    have hzT : z ∈ T := by
      have h1 : z = t⁻¹ * x * t := by
        rw [← hzx]
        simp [MulAut.conj_apply, mul_assoc]
      rw [h1]
      exact T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht
    have hzD : (⟨z, hzT⟩ : ↥T) ∈ (⨆ E ∈ 𝓔, E).subgroupOf T := hi0D ⟨hzT, hz⟩
    have h2 := hDn.conj_mem ⟨z, hzT⟩ hzD ⟨t, ht⟩
    have h3 : t * z * t⁻¹ ∈ ⨆ E ∈ 𝓔, E := h2
    have h4 : t * z * t⁻¹ = x := by
      rw [← hzx]
      simp [MulAut.conj_apply]
    rwa [h4] at h3

omit [Finite V] in
theorem mem_fixGL_prod (ctx : FamilyCtx H T n F r Lc) {i : Fin r} {v : V}
    (hv : v ∈ commGL (Lc i) ⊤) (hvU : v ∈ fixGL (T ⊓ Lc i)) : v ∈ fixGL (⨆ j, T ⊓ Lc j) := by
  have hle : (⨆ j, T ⊓ Lc j) ≤ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v := by
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · rw [hji]
      exact fun z hz => hvU z hz
    · intro z hz
      exact ctx.layer.others_fix i j hji z hz.2 v hv
  intro g hg
  exact hle hg

theorem natural_fixGL (ctx : FamilyCtx H T n F r Lc) :
    fixGL (⨆ i, T ⊓ Lc i) =
      (⨆ i, commGL (Lc i) ⊤ ⊓ fixGL (T ⊓ Lc i)) ⊔ fixGL (oddGen H) := by
  classical
  apply le_antisymm
  · intro v hv
    have hv' : v ∈ (⨆ i, commGL (Lc i) ⊤) ⊔ fixGL (oddGen H) := by
      rw [V_sum ctx]
      trivial
    obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 hv'
    obtain ⟨x, hx, rfl⟩ := mem_iSup_exists_sum _ hy
    refine Submodule.add_mem_sup ?_ hc
    refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨hx j, ?_⟩
    intro u hu
    have hvfix := hv u (le_iSup (fun i => T ⊓ Lc i) j hu)
    have huK : u ∈ oddGen H := by
      rw [ctx.layer.K_eq]
      exact Subgroup.mem_iSup_of_mem j hu.2
    have hcfix : u c = c := hc u huK
    have h1 : u (∑ i, x i + c) = ∑ i, x i + c := hvfix
    rw [map_add, hcfix, map_sum] at h1
    have h1' : ∑ i, u (x i) = ∑ i, x i := add_right_cancel h1
    rw [Fintype.sum_eq_add_sum_compl j (fun i => u (x i)), Fintype.sum_eq_add_sum_compl j x] at h1'
    have h2 : ∑ i ∈ ({j} : Finset (Fin r))ᶜ, u (x i) = ∑ i ∈ ({j} : Finset (Fin r))ᶜ, x i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hij : j ≠ i := fun h => by simp [h] at hi
      exact ctx.layer.others_fix i j hij u hu.2 (x i) (hx i)
    rw [h2] at h1'
    exact add_right_cancel h1'
  · refine sup_le (iSup_le fun i v hv => mem_fixGL_prod ctx hv.1 hv.2) (fixSub_anti _ ?_)
    refine iSup_le fun j => inf_le_right.trans ?_
    rw [ctx.layer.K_eq]
    exact le_iSup Lc j

theorem natCard_iSup_of_le {G : Type*} [Group G] (Bk U : Fin r → Subgroup G)
    (hUL : ∀ i, U i ≤ Bk i) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Bk i, ∀ y ∈ Bk j, x * y = y * x)
    (hdirect : ∀ i, Bk i ⊓ (⨆ j, ⨆ (_ : j ≠ i), Bk j) = ⊥) {m : ℕ}
    (hm : ∀ i, Nat.card ↥(U i) = m) (s : Finset (Fin r)) :
    Nat.card ↥(⨆ i ∈ s, U i) = m ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset (Fin r)), U i) = ⊥ := by simp
    rw [hbot, Subgroup.card_bot]
    simp
  | insert j s hj ih =>
    rw [Finset.iSup_insert, Finset.card_insert_of_notMem hj, pow_succ]
    have hDL : (⨆ i ∈ s, U i) ≤ ⨆ i, ⨆ (_ : i ≠ j), Bk i :=
      iSup₂_le fun i hi => (hUL i).trans (le_iSup₂_of_le i (fun h => hj (h ▸ hi)) le_rfl)
    have hc : ∀ a ∈ U j, ∀ d ∈ (⨆ i ∈ s, U i), a * d = d * a := by
      intro a ha d hd
      have : (⨆ i ∈ s, U i) ≤ Subgroup.centralizer (Bk j : Set G) := by
        refine hDL.trans (iSup₂_le fun i hij z hz => ?_)
        exact Subgroup.mem_centralizer_iff.2 fun l hl => hcomm j i (Ne.symm hij) l hl z hz
      exact Subgroup.mem_centralizer_iff.1 (this hd) a (hUL j ha)
    have hdisj : Disjoint (U j) (⨆ i ∈ s, U i) := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      have h1 : x ∈ Bk j ⊓ ⨆ i, ⨆ (_ : i ≠ j), Bk i := ⟨hUL j hx.1, hDL hx.2⟩
      rw [hdirect j] at h1
      exact h1
    rw [natCard_sup_of_commute_of_disjoint hc hdisj, ih, hm j, mul_comm]

theorem natCard_natural_D (ctx : FamilyCtx H T n F r Lc) (hnat : NaturalFamily H F r Lc)
    (hU : ∀ i, IsSylowTwoOf (T ⊓ Lc i) (Lc i)) :
    Nat.card ↥(⨆ i, T ⊓ Lc i) = Fintype.card F ^ r := by
  have hcard : ∀ i, Nat.card ↥(T ⊓ Lc i) = Fintype.card F := fun i => by
    obtain ⟨θ, β, x, -, hline⟩ := natural_coords hnat (hU i)
    exact natCard_of_natural_coords inf_le_right θ x hline
  have h := natCard_iSup_of_le Lc (fun i => T ⊓ Lc i) (fun i => inf_le_right)
    (fun i j hij => ctx.hLc.elem_commute hij) ctx.layer.direct hcard Finset.univ
  simpa using h

end Image

end CFSG.QuasithinUnique.Setup.Lift
