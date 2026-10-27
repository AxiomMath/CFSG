module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayBlock
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapGraphBlock

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear pairEmbed)
open CFSG.LieType.Ree (ReeTag)

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem blockSpecialLinear_pair_le_closure {a b : Fin n} (hab : a ≠ b) :
    blockSpecialLinear (K := K) ({a, b} : Finset (Fin n)) ≤
      closure (Set.range (fun c : K => SpecialLinearGroup.transvection hab c) ∪
        Set.range (fun c : K => SpecialLinearGroup.transvection hab.symm c)) := by
  rw [← LinearPilot.range_pairEmbed hab, MonoidHom.range_eq_map, ← sl2_closure_upper_lower,
    MonoidHom.map_closure, closure_le]
  rintro _ ⟨x, hx | hx, rfl⟩
  · obtain ⟨c, rfl⟩ := hx
    exact subset_closure (Or.inl ⟨c, (SymplecticPilot.pairEmbed_sl2Upper hab c).symm⟩)
  · obtain ⟨c, rfl⟩ := hx
    exact subset_closure (Or.inr ⟨c, (SymplecticPilot.pairEmbed_sl2Lower hab c).symm⟩)

variable (K) in
@[expose] noncomputable def blockSL4Equiv {I : Finset (Fin n)} (σ : Fin 4 ≃ I) :
    blockSpecialLinear (K := K) I ≃* SpecialLinearGroup (Fin 4) K :=
  (blockSpecialLinearMulEquivSL K I).trans (LinearPilot.reindexSpecialLinear σ.symm)

theorem blockSL4Equiv_apply {I : Finset (Fin n)} (σ : Fin 4 ≃ I)
    (x : blockSpecialLinear (K := K) I) (p q : Fin 4) :
    ((blockSL4Equiv K σ x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) p q =
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) (σ p) (σ q) := by
  change (reindex σ.symm σ.symm ((blockSpecialLinearMulEquivSL K I x :
    SpecialLinearGroup I K) : Matrix I I K)) p q = _
  rw [reindex_apply, submatrix_apply, Equiv.symm_symm, blockSpecialLinearMulEquivSL_apply]

theorem blockSL4Equiv_transvection {I : Finset (Fin n)} (σ : Fin 4 ≃ I) {p q : Fin 4}
    (hpq : p ≠ q) (c : K)
    (hmem : SpecialLinearGroup.transvection (show ((σ p : I) : Fin n) ≠ σ q from fun h =>
      hpq (σ.injective (Subtype.ext h))) c ∈ blockSpecialLinear I) :
    blockSL4Equiv K σ ⟨_, hmem⟩ = SpecialLinearGroup.transvection hpq c := by
  apply Subtype.ext
  ext k l
  rw [blockSL4Equiv_apply]
  simp only [SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, Subtype.ext_iff.symm, σ.injective.eq_iff]

theorem blockSL4Equiv_transvection' {I : Finset (Fin n)} (σ : Fin 4 ≃ I) {i j : Fin n}
    (hij : i ≠ j) (c : K) (hmem : SpecialLinearGroup.transvection hij c ∈ blockSpecialLinear I)
    {p q : Fin 4} (hpq : p ≠ q) (hp : ((σ p : I) : Fin n) = i) (hq : ((σ q : I) : Fin n) = j) :
    blockSL4Equiv K σ ⟨_, hmem⟩ = SpecialLinearGroup.transvection hpq c := by
  subst hp hq
  exact blockSL4Equiv_transvection σ hpq c hmem

end Blocks

section Rigid


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem edge_eq_or_eq_conj (hK : Nat.card K = 2) {e : L ≃* adjointGroup .F4 K}
    {t : G} (ht : t ∈ centralizer (L : Set G)) {ΦA : e6ScLevi K e6A5Nodes →* G}
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hr : ΦA.range = centralizerPerfectCore (subgroupToG e X₀))
    (hinj : Function.Injective (chainSL6 ΦA)) {a b : Fin 6} (hab : a ≠ b)
    {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hx : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab c) =
      ((e.symm (Adjoint.f4Par K β c) : L) : G))
    (hx' : ∀ c : K, chainSL6 ΦA (SpecialLinearGroup.transvection hab.symm c) =
      ((e.symm (Adjoint.f4Par K (-β) c) : L) : G))
    {i i' j j' : Fin 6} (hii : i ≠ i') (hjj : j ≠ j')
    (hcov : ∀ y ∈ ({a, b} : Finset (Fin 6))ᶜ, y = i ∨ y = i' ∨ y = j ∨ y = j')
    (hmi : i ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmi' : i' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hmj : j ∈ ({a, b} : Finset (Fin 6))ᶜ) (hmj' : j' ∈ ({a, b} : Finset (Fin 6))ᶜ)
    (hL1 : chainSL6 ΦA (SpecialLinearGroup.transvection hii 1) ∈ L)
    (hL2 : chainSL6 ΦA (SpecialLinearGroup.transvection hii.symm 1) ∈ L)
    (hL3 : chainSL6 ΦA (SpecialLinearGroup.transvection hjj 1) ∈ L)
    (hL4 : chainSL6 ΦA (SpecialLinearGroup.transvection hjj.symm 1) ∈ L)
    (htm : ∃ x ∈ blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ,
      t * chainSL6 ΦA x * t⁻¹ ≠ chainSL6 ΦA x)
    {α' : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ →* G}
    (hα' : Function.Injective α')
    (hα'r : α'.range ≤
      centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β))))
    (h1 : α' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii hmi hmi' 1⟩ =
      chainSL6 ΦA (SpecialLinearGroup.transvection hii 1))
    (h2 : α' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii.symm hmi' hmi 1⟩ =
      chainSL6 ΦA (SpecialLinearGroup.transvection hii.symm 1))
    (h3 : α' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj hmj hmj' 1⟩ =
      chainSL6 ΦA (SpecialLinearGroup.transvection hjj 1))
    (h4 : α' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj.symm hmj' hmj 1⟩ =
      chainSL6 ΦA (SpecialLinearGroup.transvection hjj.symm 1)) :
    (∀ x, α' x = chainSL6 ΦA x) ∨ ∀ x, α' x = t * chainSL6 ΦA x * t⁻¹ := by
  set E := centralizerPerfectCore (subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)))
    with hE
  set α : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ →* G :=
    (chainSL6 ΦA).comp (blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ).subtype with hαdef
  have hαinj : Function.Injective α := hinj.comp Subtype.val_injective
  have hαr : α.range = E := by
    rw [hαdef, MonoidHom.range_comp, Subgroup.range_subtype]
    exact le_antisymm
      (le_centralizerPerfectCore_chain hr hab (subgroupToG_zpowers_chainZ_le hab hβ hx hx'))
      (centralizerPerfectCore_chain_le hK hr hinj hab (chainSL6_pairEmbed_mem hab hx hx'))
  have hcard : 3 ≤ (({a, b} : Finset (Fin 6))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    norm_num
  have χ : E ≃* LinearFlag.projectiveSL (({a, b} : Finset (Fin 6))ᶜ).card K := by
    have e0 : blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ ≃* E :=
      (MonoidHom.ofInjective hαinj).trans (MulEquiv.subgroupCongr hαr)
    have e1 : SpecialLinearGroup (({a, b} : Finset (Fin 6))ᶜ : Finset (Fin 6)) K ≃*
        blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ :=
      (MonoidHom.ofInjective (LinearPilot.blockEmbed_injective _)).trans
        (MulEquiv.subgroupCongr (LinearPilot.range_blockEmbed _))
    have e2 : SpecialLinearGroup (({a, b} : Finset (Fin 6))ᶜ : Finset (Fin 6)) K ≃*
        SpecialLinearGroup (Fin (({a, b} : Finset (Fin 6))ᶜ).card) K :=
      LinearPilot.reindexSpecialLinear (({a, b} : Finset (Fin 6))ᶜ).equivFin
    have e3 : SpecialLinearGroup (Fin (({a, b} : Finset (Fin 6))ᶜ).card) K ≃*
        LinearFlag.projectiveSL (({a, b} : Finset (Fin 6))ᶜ).card K :=
      MulEquiv.ofBijective (LinearFlag.proj _ K)
        ⟨LinearPilot.proj_injective_of_card_two hK, LinearFlag.proj_surjective _ K⟩
    exact e0.symm.trans ((e1.symm.trans e2).trans e3)
  set T : Set (blockSpecialLinear (K := K) ({a, b} : Finset (Fin 6))ᶜ) :=
    {⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii hmi hmi' 1⟩,
      ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii.symm hmi' hmi 1⟩,
      ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj hmj hmj' 1⟩,
      ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj.symm hmj' hmj 1⟩} with hT
  set S : Subgroup G := (closure T).map α with hS
  have hSE : S ≤ E := by
    rw [← hαr, MonoidHom.range_eq_map]
    exact Subgroup.map_mono le_top
  have hTS : ∀ g ∈ T, α g ∈ S := fun g hg => ⟨g, subset_closure hg, rfl⟩
  have hC : ∀ x ∈ E, (∀ s ∈ S, x * s = s * x) → x = 1 := by
    intro x hx hcomm
    rw [← hαr] at hx
    obtain ⟨y, rfl⟩ := hx
    have hcomm' : ∀ g ∈ T, (y : SpecialLinearGroup (Fin 6) K) *
        (g : SpecialLinearGroup (Fin 6) K) =
        (g : SpecialLinearGroup (Fin 6) K) * (y : SpecialLinearGroup (Fin 6) K) := by
      intro g hg
      have h := hcomm _ (hTS g hg)
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hαinj h)
    have hy1 : (y : SpecialLinearGroup (Fin 6) K) = 1 :=
      relay_eq_one_of_commute hK y.2 hii hjj hcov
        (hcomm' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii hmi hmi' 1⟩
          (Set.mem_insert _ _))
        (hcomm' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hii.symm hmi' hmi 1⟩
          (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
        (hcomm' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj hmj hmj' 1⟩
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
        (hcomm' ⟨_, LinearPilot.transvection_mem_blockSpecialLinear hjj.symm hmj' hmj 1⟩
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
    have hy : y = 1 := Subtype.ext hy1
    rw [hy, map_one]
  have hSL : S ≤ L := by
    rw [hS, MonoidHom.map_closure, closure_le]
    rintro _ ⟨g, hg, rfl⟩
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hL1
    · exact hL2
    · exact hL3
    · exact hL4
  have hJL : subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)) ≤ L :=
    sup_le (relay_subgroupToG_le e _) (relay_subgroupToG_le e _)
  have hJ : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)), t * y = y * t :=
    fun y hy => (mem_centralizer_iff.1 ht y (hJL hy)).symm
  have hJ' : ∀ y ∈ subgroupToG e X₀ ⊔ subgroupToG e (zpowers (chainZ K β)),
      t⁻¹ * y = y * t⁻¹ :=
    fun y hy => (mem_centralizer_iff.1 (inv_mem ht) y (hJL hy)).symm
  have htE : ∀ x ∈ E, t * x * t⁻¹ ∈ E := fun x hx => relay_conj_mem_centralizerPerfectCore hJ hx
  have htE' : ∀ x ∈ E, t⁻¹ * x * t ∈ E := fun x hx => by
    have h := relay_conj_mem_centralizerPerfectCore hJ' hx
    rwa [inv_inv] at h
  have htS : ∀ s ∈ S, t * s * t⁻¹ = s := fun s hs => by
    rw [← mem_centralizer_iff.1 ht s (hSL hs), mul_inv_cancel_right]
  have htm' : ∃ x ∈ E, t * x * t⁻¹ ≠ x := by
    obtain ⟨x, hxB, hx⟩ := htm
    exact ⟨chainSL6 ΦA x, hαr ▸ ⟨⟨x, hxB⟩, rfl⟩, hx⟩
  have hagree : closure T ≤ MonoidHom.eqLocus α' α := by
    rw [closure_le]
    intro g hg
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hSα : ∀ x, α x ∈ S → α' x = α x := fun x hx =>
    hagree ((Subgroup.mem_map_iff_mem hαinj).1 hx)
  exact eq_or_eq_conj_of_agree_projectiveSL hK hcard χ hSE hC htE htE' htS htm' hαinj hα' hαr
    hα'r hSα

end Rigid

end CFSG.SeitzReduction.F4Pilot
