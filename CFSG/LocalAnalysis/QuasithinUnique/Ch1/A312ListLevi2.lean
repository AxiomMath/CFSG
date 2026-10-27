module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

section Levi2

variable {G : Type*} [Group G]

theorem isSolvable_of_levi {P Q M : Subgroup G} (hQP : Q ≤ P)
    (hN : P ≤ Subgroup.normalizer (Q : Set G)) (hP : Q ⊔ M = P) (hQs : Group.IsSolvable ↥Q)
    (hMs : Group.IsSolvable ↥M) : Group.IsSolvable ↥P := by
  have hMP : M ≤ P := hP ▸ le_sup_right
  have hnorm : (Q.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mpr hN
  let ψ : ↥M →* ↥P ⧸ Q.subgroupOf P :=
    (QuotientGroup.mk' (Q.subgroupOf P)).comp (Subgroup.inclusion hMP)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective y
    have hp : (p : G) ∈ ((M ⊔ Q : Subgroup G) : Set G) := by
      rw [sup_comm, hP]
      exact p.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right M Q (hMP.trans hN)] at hp
    obtain ⟨m, hm, q, hq, hpmq⟩ := hp
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (((Subgroup.inclusion hMP ⟨m, hm⟩)⁻¹ * p : ↥P) : G) = q := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hpmq]
      simp
    rw [this]
    exact hq
  have hQs' : Group.IsSolvable ↥(Q.subgroupOf P) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQP).toMonoidHom) (MulEquiv.injective _)
  have hMs' : Group.IsSolvable (↥P ⧸ Q.subgroupOf P) := Group.isSolvable_of_surjective hψsurj
  exact Group.isSolvable_of_subgroup_quotient (Q.subgroupOf P)

theorem inf_eq_bot_of_simple {p : ℕ} [Fact p.Prime] [Finite G] {V M : Subgroup G} [IsSimpleGroup ↥M]
    (hnorm : M ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup p ↥V) (hMperf : ⁅M, M⁆ = M) :
    V ⊓ M = ⊥ := by
  have hnormal : ((V ⊓ M).subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnV, hnM⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hnorm g.2) (n : G)).1 hnV,
      mul_mem (mul_mem g.2 hnM) (inv_mem g.2)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V ⊓ M).subgroupOf M) with h | h
  · have := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right, Subgroup.map_bot] at this
  · exfalso
    have hle : M ≤ V ⊓ M := Subgroup.subgroupOf_eq_top.mp h
    have hM2 : IsPGroup p ↥M :=
      IsPGroup.of_injective hV (Subgroup.inclusion (hle.trans inf_le_left))
        (Subgroup.inclusion_injective _)
    have hnil := hM2.isNilpotent
    have : Group.IsPerfect ↥M := Subgroup.isPerfect_iff.mpr hMperf
    exact Group.IsPerfect.not_isSolvable ↥M inferInstance

theorem exists_levi_hom_final {p : ℕ} [Fact p.Prime] [Finite G] {C P N V M : Subgroup G}
    [IsSimpleGroup ↥M] (hNP : N ≤ P) (hPC : P ≤ C) (hpc : perfectCore P = perfectCore N)
    (hVN : V ≤ N) (hNV : N ≤ Subgroup.normalizer (V : Set G)) (hsup : V ⊔ M = N)
    (hMnorm : M ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup p ↥V) (hMperf : ⁅M, M⁆ = M) :
    ∃ g : ↥(perfectCore (P.subgroupOf C)) →* ↥M, Function.Surjective g ∧ IsPGroup p g.ker := by
  have hVM : V ⊓ M = ⊥ := inf_eq_bot_of_simple hMnorm hV hMperf
  obtain ⟨g, hg, hk⟩ := exists_levi_hom_subgroupOf (C := C) (hNP.trans hPC) hVN hNV hVM hsup
    le_rfl hMperf (perfectCore_le _)
  have hpcC : perfectCore (P.subgroupOf C) = perfectCore (N.subgroupOf C) := by
    apply Subgroup.map_injective C.subtype_injective
    rw [perfectCore_map_subgroupOf hPC, perfectCore_map_subgroupOf (hNP.trans hPC), hpc]
  let g' : ↥(perfectCore (P.subgroupOf C)) →* ↥M := g.comp (MulEquiv.subgroupCongr hpcC).toMonoidHom
  refine ⟨g', hg.comp (MulEquiv.subgroupCongr hpcC).surjective, ?_⟩
  exact isPGroup_ker_of_levi hV g' fun x hx => hk _ hx

theorem perfect_of_isSimpleGroup_nonabelian {H : Subgroup G} [IsSimpleGroup ↥H]
    (hnab : ∃ x y : ↥H, x * y ≠ y * x) : ⁅H, H⁆ = H := by
  have hcomm : commutator ↥H = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥H) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      apply hxy
      have hmem : ⁅x, y⁆ ∈ commutator ↥H :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hcomm)

theorem perfectCore_eq_of_commutator_le [Finite G] {P N : Subgroup G} (hNP : N ≤ P)
    (hc : ⁅P, P⁆ ≤ N) : perfectCore P = perfectCore N :=
  le_antisymm
    (le_perfectCore_of_perfect
      ((calc perfectCore P = ⁅perfectCore P, perfectCore P⁆ := (perfectCore_perfect P).symm
        _ ≤ ⁅P, P⁆ := Subgroup.commutator_mono (perfectCore_le P) (perfectCore_le P)).trans hc)
      (perfectCore_perfect P))
    (perfectCore_mono hNP)

end Levi2

end CFSG.QuasithinUnique.Vol2Native.A312L
