module

public import CFSG.LieType.Chevalley.GraphFixedIntrinsicPairs
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement MatrixGroups

theorem derivedSeries_perm_three_eq_bot {α : Type*} [Fintype α] [DecidableEq α]
    (h : Nat.card α = 4) : derivedSeries (Equiv.Perm α) 3 = ⊥ := by
  have h1 : derivedSeries (Equiv.Perm α) 1 ≤ alternatingGroup α :=
    Abelianization.commutator_subset_ker (Equiv.Perm.sign : Equiv.Perm α →* ℤˣ)
  have hA : ⁅alternatingGroup α, alternatingGroup α⁆ =
      (alternatingGroup.kleinFour α).map (alternatingGroup α).subtype := by
    rw [alternatingGroup.kleinFour_eq_commutator h, _root_.commutator_def,
      Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h2 : derivedSeries (Equiv.Perm α) 2 ≤
      (alternatingGroup.kleinFour α).map (alternatingGroup α).subtype := by
    rw [derivedSeries_succ, ← hA]
    exact Subgroup.commutator_mono h1 h1
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono h2 h2).trans (Subgroup.commutator_le.2 ?_)
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul]
  exact congrArg _ (congrArg Subtype.val (mul_comm_of_exponent_two
    (alternatingGroup.exponent_kleinFour_of_card_eq_four h) ⟨v, hv⟩ ⟨w, hw⟩))

theorem derivedSeries_perm_one_eq_bot {α : Type*} [Finite α] (h : Nat.card α ≤ 2) :
    derivedSeries (Equiv.Perm α) 1 = ⊥ := by
  have hc := Equiv.Perm.isMulCommutative_iff_card_le_two.2 h
  rw [derivedSeries_one, _root_.commutator_def, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x _ y _ => ?_
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hc.is_comm.comm x y

theorem derivedSeries_add_le_map {G : Type*} [Group G] {N : Subgroup G} {d : ℕ}
    (h : derivedSeries G d ≤ N) (n : ℕ) :
    derivedSeries G (d + n) ≤ (derivedSeries N n).map N.subtype := by
  induction n with
  | zero => rwa [add_zero, derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih =>
    rw [← add_assoc, derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator]
    exact Subgroup.commutator_mono ih ih

section Restrict

variable {G : Type*} [Group G]

theorem apply_mem_of_map_eq {H : Subgroup G} {e : MulAut G} (he : H.map e.toMonoidHom = H)
    {g : G} (hg : g ∈ H) : e g ∈ H := by
  rw [← he]
  exact Subgroup.mem_map_of_mem _ hg

theorem symm_apply_mem_of_map_eq {H : Subgroup G} {e : MulAut G} (he : H.map e.toMonoidHom = H)
    {g : G} (hg : g ∈ H) : e.symm g ∈ H :=
  Subgroup.mem_map_equiv.1 (by rw [he]; exact hg)

@[expose] def restrictMulAut {A : Type*} [Group A] (ι : A →* MulAut G) (H : Subgroup G)
    (hH : ∀ α, H.map (ι α).toMonoidHom = H) : A →* MulAut H where
  toFun α :=
    { toFun := fun h => ⟨ι α (h : G), apply_mem_of_map_eq (hH α) h.2⟩
      invFun := fun h => ⟨(ι α).symm (h : G), symm_apply_mem_of_map_eq (hH α) h.2⟩
      left_inv := fun h => Subtype.ext ((ι α).symm_apply_apply (h : G))
      right_inv := fun h => Subtype.ext ((ι α).apply_symm_apply (h : G))
      map_mul' := fun h h' => Subtype.ext (map_mul (ι α) (h : G) (h' : G)) }
  map_one' := MulEquiv.ext fun h => Subtype.ext (by
    change ι 1 (h : G) = h
    rw [map_one]
    rfl)
  map_mul' α β := MulEquiv.ext fun h => Subtype.ext (by
    change ι (α * β) (h : G) = ι α (ι β (h : G))
    rw [map_mul]
    rfl)

theorem coe_restrictMulAut_apply {A : Type*} [Group A] (ι : A →* MulAut G) (H : Subgroup G)
    (hH : ∀ α, H.map (ι α).toMonoidHom = H) (α : A) (h : H) :
    ((restrictMulAut ι H hH α h : H) : G) = ι α (h : G) :=
  rfl

variable {F : Type*} [Field F] (ρ : SL(2, F) →* G)

theorem range_eq_sl2RootX_sup_sl2RootY : ρ.range = sl2RootX ρ ⊔ sl2RootY ρ := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨g, rfl⟩
    have hg : g ∈ Subgroup.closure (Set.range (sl2Upper F) ∪ Set.range (sl2Lower F)) := by
      rw [sl2_closure_upper_lower]
      trivial
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · exact Subgroup.mem_sup_left ⟨c, rfl⟩
      · exact Subgroup.mem_sup_right ⟨c, rfl⟩
    | one => rw [map_one]; exact one_mem _
    | mul g h _ _ hg hh => rw [map_mul]; exact mul_mem hg hh
    | inv g _ hg => rw [map_inv]; exact inv_mem hg
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl⟩

theorem map_subtype_sl2RootX_rangeRestrict :
    (sl2RootX ρ.rangeRestrict).map ρ.range.subtype = sl2RootX ρ := by
  ext y
  rw [Subgroup.mem_map, mem_sl2RootX]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

theorem map_subtype_sl2RootY_rangeRestrict :
    (sl2RootY ρ.rangeRestrict).map ρ.range.subtype = sl2RootY ρ := by
  ext y
  rw [Subgroup.mem_map, mem_sl2RootY]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

theorem map_restrictMulAut_eq {A : Type*} [Group A] (ι : A →* MulAut G) {H : Subgroup G}
    (hH : ∀ α, H.map (ι α).toMonoidHom = H) {S : Subgroup G} {S' : Subgroup H}
    (hS' : S'.map H.subtype = S) (hS : ∀ α, S.map (ι α).toMonoidHom = S) (α : A) :
    S'.map (restrictMulAut ι H hH α).toMonoidHom = S' := by
  refine Subgroup.map_injective H.subtype_injective ?_
  have e : H.subtype.comp (restrictMulAut ι H hH α).toMonoidHom =
      (ι α).toMonoidHom.comp H.subtype := MonoidHom.ext fun _ => rfl
  rw [Subgroup.map_map, e, ← Subgroup.map_map, hS', hS]

variable {ρ}

theorem apply_eq_self_of_mem_derivedSeries_two [Finite F]
    (hker : ∀ g : SL(2, F), ρ g = 1 → ∃ l : Fˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F))
    {A : Type*} [Group A] (ι : A →* MulAut G)
    (hX : ∀ α, (sl2RootX ρ).map (ι α).toMonoidHom = sl2RootX ρ)
    (hY : ∀ α, (sl2RootY ρ).map (ι α).toMonoidHom = sl2RootY ρ)
    {x : A} (hx : x ∈ derivedSeries A 2) {g : G} (hg : g ∈ ρ.range) : ι x g = g := by
  have hH : ∀ α, ρ.range.map (ι α).toMonoidHom = ρ.range := fun α => by
    rw [range_eq_sl2RootX_sup_sl2RootY, Subgroup.map_sup, hX, hY]
  have hker' : ∀ g : SL(2, F), ρ.rangeRestrict g = 1 → ∃ l : Fˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) F) = (l : F) • (1 : Matrix (Fin 2) (Fin 2) F) :=
    fun g h => hker g (congrArg Subtype.val h)
  have hr : ∀ α, restrictMulAut ι ρ.range hH α ∈
      pairAutSubgroup (sl2RootX ρ.rangeRestrict) (sl2RootY ρ.rangeRestrict) := fun α =>
    ⟨map_restrictMulAut_eq ι hH (map_subtype_sl2RootX_rangeRestrict ρ) hX α,
      map_restrictMulAut_eq ι hH (map_subtype_sl2RootY_rangeRestrict ρ) hY α⟩
  have hmap := map_derivedSeries_le_derivedSeries ((restrictMulAut ι ρ.range hH).codRestrict _ hr) 2
  rw [exceptional_central_SL2_pair_stabilizer ρ.rangeRestrict ρ.rangeRestrict_surjective hker',
    le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
  have hx1 : restrictMulAut ι ρ.range hH x = 1 := congrArg Subtype.val (hmap hx)
  exact congrArg (fun e : MulAut ρ.range => ((e ⟨g, hg⟩ : ρ.range) : G)) hx1

theorem eq_one_of_forall_apply_eq {ι' : Type*} {e : MulAut G} {H : ι' → Subgroup G}
    (hH : ⨆ i, H i = ⊤) (he : ∀ i, ∀ g ∈ H i, e g = g) : e = 1 := by
  have hle : ⨆ i, H i ≤ e.toMonoidHom.eqLocus (MonoidHom.id G) := iSup_le fun i g hg => he i g hg
  exact MulEquiv.ext fun g => hle (hH ▸ Subgroup.mem_top g)

end Restrict

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem range_orbitRankOneHom_le
    (a : Fin t.foldedTag.rank) :
    (orbitRankOneHom t K σ a).range ≤ graphFixedRootGroup t K σ := by
  rw [orbitRankOneHom_range, Subgroup.closure_le]
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a c)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
      (orbitY_mem_graphFixedNegUnipotent t σ a c)

variable (t K σ) in
@[expose] def orbitRankOneHomFixed
    (a : Fin t.foldedTag.rank) :
    SL(2, orbitField t K σ a) →* graphFixedRootGroup t K σ :=
  (orbitRankOneHom t K σ a).codRestrict _ fun g => range_orbitRankOneHom_le a ⟨g, rfl⟩

theorem orbitRankOneHomFixed_ker
    {a : Fin t.foldedTag.rank} (g : SL(2, orbitField t K σ a))
    (hg : orbitRankOneHomFixed t K σ a g = 1) :
    ∃ l : (orbitField t K σ a)ˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) =
        (l : orbitField t K σ a) • (1 : Matrix (Fin 2) (Fin 2) (orbitField t K σ a)) := by
  obtain ⟨l, hl, hg'⟩ := eq_smul_one_of_mem_ker_orbitRankOneHom (g := g)
    ((MonoidHom.mem_ker).2 (congrArg Subtype.val hg))
  exact ⟨l, Units.ext (by rw [Units.val_pow_eq_pow_val, hl, Units.val_one]), hg'⟩

theorem sl2RootX_orbitRankOneHomFixed
    (a : Fin t.foldedTag.rank) :
    sl2RootX (orbitRankOneHomFixed t K σ a) =
      (orbitXSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ) := by
  ext g
  rw [mem_sl2RootX, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, coe_orbitXSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (orbitRankOneHom_uSL a c).symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext ((orbitRankOneHom_uSL a c).trans hc)⟩

theorem sl2RootY_orbitRankOneHomFixed
    (a : Fin t.foldedTag.rank) :
    sl2RootY (orbitRankOneHomFixed t K σ a) =
      (orbitYSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ) := by
  ext g
  rw [mem_sl2RootY, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, coe_orbitYSubgroup]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (orbitRankOneHom_vSL a c).symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, Subtype.ext ((orbitRankOneHom_vSL a c).trans hc)⟩

theorem iSup_range_orbitRankOneHomFixed
    (hσ : Function.Surjective σ) :
    ⨆ a, (orbitRankOneHomFixed t K σ a).range = ⊤ := by
  have hmap : (⨆ a, (orbitRankOneHomFixed t K σ a).range).map
      (graphFixedRootGroup t K σ).subtype = graphFixedRootGroup t K σ := by
    refine (Subgroup.map_iSup _ _).trans ((iSup_congr fun a => ?_).trans
      (graphFixedRootGroup_eq_iSup_orbitRankOneGroup hσ).symm)
    rw [MonoidHom.map_range, orbitRankOneGroup, ← orbitRankOneHom_range]
    rfl
  rw [eq_top_iff]
  rintro g -
  obtain ⟨g', hg', e⟩ := (Subgroup.mem_map).1 (hmap.symm ▸ g.2 :
    (g : ModGL t.tag K) ∈ (⨆ a, (orbitRankOneHomFixed t K σ a).range).map
      (graphFixedRootGroup t K σ).subtype)
  rwa [Subtype.ext e] at hg'

theorem derivedSeries_two_ker_eq_bot
    [Finite K] (σ : K ≃+* K)
    (φ : graphFixedUnipotentStabilizer t K σ.toRingHom →* Equiv.Perm (Fin t.foldedTag.rank))
    (hφ : ∀ β : graphFixedUnipotentStabilizer t K σ.toRingHom,
      PermutesSimpleOrbitGroups t K σ.toRingHom β (φ β)) :
    derivedSeries φ.ker 2 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  let ι := (graphFixedUnipotentStabilizer t K σ.toRingHom).subtype.comp φ.ker.subtype
  have hperm : ∀ α : φ.ker, PermutesSimpleOrbitGroups t K σ.toRingHom (ι α) 1 := by
    intro α
    have h := hφ α.1
    rwa [show φ α.1 = 1 from α.2] at h
  have hX : ∀ a (α : φ.ker), (sl2RootX (orbitRankOneHomFixed t K σ.toRingHom a)).map
      (ι α).toMonoidHom = sl2RootX (orbitRankOneHomFixed t K σ.toRingHom a) := fun a α => by
    rw [sl2RootX_orbitRankOneHomFixed]
    exact (hperm α a).1
  have hY : ∀ a (α : φ.ker), (sl2RootY (orbitRankOneHomFixed t K σ.toRingHom a)).map
      (ι α).toMonoidHom = sl2RootY (orbitRankOneHomFixed t K σ.toRingHom a) := fun a α => by
    rw [sl2RootY_orbitRankOneHomFixed]
    exact (hperm α a).2
  have h1 : ι x = 1 := eq_one_of_forall_apply_eq (iSup_range_orbitRankOneHomFixed σ.surjective)
    fun a g hg => apply_eq_self_of_mem_derivedSeries_two orbitRankOneHomFixed_ker ι (hX a)
      (hY a) hx hg
  exact (Subgroup.mem_bot).2 (Subtype.ext (Subtype.ext h1))

theorem exceptional_fixed_root_group_Schreier
    (t : TwistTag) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) :
    (t = .E6 → derivedSeries (Outer (graphFixedRootGroup t K σ.toRingHom)) 5 = ⊥) ∧
    (t = .D4 → derivedSeries (Outer (graphFixedRootGroup t K σ.toRingHom)) 3 = ⊥) := by
  obtain ⟨-, ⟨φ, hφ⟩, -, -⟩ := diagram_fixed_intrinsic_simple_pairs t K σ
  have hker := derivedSeries_two_ker_eq_bot σ φ hφ
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hopp := (exceptional_fixed_Sylow_opposition t K (ringChar K) σ w₀ hw₀).2.2.2.2.2
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup t K σ.toRingHom))).comp
        (graphFixedUnipotentStabilizer t K σ.toRingHom).subtype) := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨c, β, hU, hV, rfl⟩ := hopp α
    refine ⟨⟨β, (show β ∈ graphFixedUnipotentStabilizer t K σ.toRingHom from ⟨hU, hV⟩)⟩, ?_⟩
    have hc : MulAut.conj c ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
        (graphFixedRootGroup t K σ.toRingHom) := ⟨c, rfl⟩
    change QuotientGroup.mk' _ β = QuotientGroup.mk' _ (MulAut.conj c * β)
    rw [map_mul, QuotientGroup.mk'_apply _ (MulAut.conj c), (QuotientGroup.eq_one_iff _).2 hc,
      one_mul]
  have key : ∀ d, derivedSeries (Equiv.Perm (Fin t.foldedTag.rank)) d = ⊥ →
      derivedSeries (Outer (graphFixedRootGroup t K σ.toRingHom)) (d + 2) = ⊥ := by
    intro d hd
    have h1 := map_derivedSeries_le_derivedSeries φ d
    rw [hd, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    have h2 := derivedSeries_add_le_map h1 2
    rw [hker, Subgroup.map_bot, le_bot_iff] at h2
    rw [← map_derivedSeries_eq hsurj, h2, Subgroup.map_bot]
  refine ⟨?_, ?_⟩
  · rintro rfl
    have h4 : Nat.card (Fin TwistTag.E6.foldedTag.rank) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    exact key 3 (derivedSeries_perm_three_eq_bot h4)
  · rintro rfl
    have h2 : Nat.card (Fin TwistTag.D4.foldedTag.rank) ≤ 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    exact key 1 (derivedSeries_perm_one_eq_bot h2)

end CFSG.LieType.Chevalley
