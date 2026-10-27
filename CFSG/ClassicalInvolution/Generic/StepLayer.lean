module

public import CFSG.ClassicalInvolution.Generic.StepSplit
public import CFSG.ClassicalInvolution.Balance.Layer
public import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.ClassicalInvolution CFSG.ComponentClassification
open scoped MatrixGroups

section Algebra

variable {G : Type*} [Group G]

theorem le_of_perfect_of_le_sup_odd [Finite G] {A S L : Subgroup G} [A.Normal]
    (hS : Odd (Nat.card S)) (hL : Group.IsPerfect L) (h : L ≤ A ⊔ S) : L ≤ A := by
  have hsolv : Group.IsSolvable S := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hS
  set π := QuotientGroup.mk' A with hπ
  have hA : A.map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by rw [hπ, QuotientGroup.ker_mk'])
  have h1 : L.map π ≤ S.map π := by
    calc L.map π ≤ (A ⊔ S).map π := Subgroup.map_mono h
      _ = A.map π ⊔ S.map π := Subgroup.map_sup _ _ _
      _ = S.map π := by rw [hA, bot_sup_eq]
  have hsolvS : Group.IsSolvable (S.map π) :=
    Group.isSolvable_of_surjective (f := π.subgroupMap S) (MonoidHom.subgroupMap_surjective π S)
  have hsolvL : Group.IsSolvable (L.map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h1)
  have hperfL : Group.IsPerfect (L.map π) := Group.IsPerfect.map π
  by_contra hne
  have hbot : L.map π ≠ ⊥ := fun hb => hne (by
    intro x hx
    have := Subgroup.mem_map_of_mem π hx
    rw [hb, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this)
  have hnt : Nontrivial (L.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
  exact Group.IsPerfect.not_isSolvable (L.map π) hsolvL

theorem map_conj_eq_of_normal (N : Subgroup G) [N.Normal] (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance y hy g
  · intro hx
    exact ⟨g⁻¹ * x * g, by simpa using Subgroup.Normal.conj_mem inferInstance x hx g⁻¹,
      by simp [mul_assoc]⟩

theorem fixedSubgroup_conj_eq_centralizer (z : G) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set G) := by
  ext member
  change z * member * z⁻¹ = member ↔ member ∈ Subgroup.centralizer ({z} : Set G)
  constructor
  · intro heq
    apply Subgroup.mem_centralizer_iff.mpr
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    calc z * member = (z * member * z⁻¹) * z := by group
      _ = member * z := by rw [heq]
  · intro hmem
    have hc := Subgroup.mem_centralizer_iff.mp hmem z (Set.mem_singleton z)
    rw [hc]
    group

theorem le_of_map_eq_of_le [Finite G] {Lc L₀ N : Subgroup G} [N.Normal]
    (hperf : Group.IsPerfect Lc)
    (hmap : L₀.map (QuotientGroup.mk' (componentClassificationOddCore G)) =
      Lc.map (QuotientGroup.mk' (componentClassificationOddCore G))) (hN : L₀ ≤ N) : Lc ≤ N := by
  have h1 : Lc.map (QuotientGroup.mk' (componentClassificationOddCore G)) ≤
      N.map (QuotientGroup.mk' (componentClassificationOddCore G)) := hmap ▸ Subgroup.map_mono hN
  have h2 := Subgroup.map_le_iff_le_comap.mp h1
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  exact le_of_perfect_of_le_sup_odd (CFSG.ComponentClassification.OddCore.odd_card G) hperf h2

end Algebra

section Layer

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem IsClassicalMember.le_twoLayer (hLB : L2PrimeBalance) (hq : 4 ≤ p ^ f) {L : Subgroup Y}
    {z : Y} (h : IsClassicalMember p f L z) : L ≤ TwoLayer.subgroup Y := by
  have hA : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_eq_two]; simp)
  have hXz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup Y) : Set Y) =
      Subgroup.centralizer ({z} : Set Y) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf]; exact hq
  obtain ⟨e⟩ := h.nonempty_equiv
  have hLC : L ≤ Subgroup.centralizer ({z} : Set Y) := isSubnormal_le h.subnormal
  refine Balance.le_twoLayer_of_l2PrimeBalance hLB hA (by rw [hXz]; exact hLC)
    (by rw [hXz]; exact h.subnormal) h.perfect.commutator_eq_top ?_
  exact Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4)

theorem twoLayer_le_layer_of_corefree (hO : classicalInvolutionOddCore Y = ⊥) :
    TwoLayer.subgroup Y ≤ Layer.subgroup Y :=
  sSup_le fun _ hC => Layer.component_le (TwoComponents.ordinary_of_corefree hO hC)

theorem layer_eq_top (hLB : L2PrimeBalance) (hq : 4 ≤ p ^ f)
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ) :
    Layer.subgroup Y = ⊤ := by
  rw [eq_top_iff, ← hΛ.generated]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨z, hz⟩ := hΛ.classical L hL
  exact (hz.le_twoLayer hLB hq).trans (twoLayer_le_layer_of_corefree hO)

theorem IsClassicalMember.le_or_le_centralizer_of_component (hq : 4 ≤ p ^ f)
    (hlayer : Layer.subgroup Y = ⊤) {T : Subgroup Y} (hT : IsComponentOf T ⊤) {L : Subgroup Y}
    {z : Y} (hL : IsClassicalMember p f L z) :
    L ≤ T ∨ L ≤ Subgroup.centralizer (T : Set Y) := by
  have hTn : T.Normal := by
    have h := Layer.normal_component hT
    rw [hlayer] at h
    exact ⟨fun n hn g => (Subgroup.normal_subgroupOf_iff le_top).mp h n g hn (Subgroup.mem_top g)⟩
  set D : Subgroup Y := Subgroup.centralizer (T : Set Y) with hD
  have hDn : D.Normal := ⟨fun x hx g => by
    rw [hD, Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 := Subgroup.mem_centralizer_iff.mp hx (g⁻¹ * t * g)
      (by simpa using hTn.conj_mem t ht g⁻¹)
    calc t * (g * x * g⁻¹) = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * t := by group⟩
  have hcover : T ⊔ D = ⊤ := by
    rw [eq_top_iff, ← hlayer]
    refine sSup_le fun C hC => ?_
    by_cases hCT : C = T
    · rw [hCT]; exact le_sup_left
    · exact le_sup_of_le_right (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (LocalComponents.commute_of_ne C T hC hT hCT))
  have hcomm : ⁅T, D⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy x hx).symm
  set C : Subgroup Y := Subgroup.centralizer ({z} : Set Y) with hC
  have hder := FixedCommutingProduct.derived_fixed_of_cover T D hcomm hcover (MulAut.conj z)
    (map_conj_eq_of_normal T z) (map_conj_eq_of_normal D z)
  rw [fixedSubgroup_conj_eq_centralizer] at hder
  have hLC : L ≤ C := isSubnormal_le hL.subnormal
  have hLperf : ⁅L, L⁆ = L := by
    have := hL.perfect
    exact Subgroup.commutator_eq_self
  have hLle : L ≤ T ⊓ C ⊔ D ⊓ C :=
    hLperf ▸ ((Subgroup.commutator_mono hLC hLC).trans hder)
  have hLc := hL.subgroupOf p f hLC
  have hLcsub : IsSubnormal (L.subgroupOf C) ⊤ := by
    have := isSubnormal_subgroupOf hL.subnormal C
    rwa [Subgroup.subgroupOf_self] at this
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf]; exact hq
  obtain ⟨e⟩ := hLc.nonempty_equiv
  have hLcq : CFSG.Open.IsQuasisimple
      (↥(L.subgroupOf C) ⧸ componentClassificationOddCore (L.subgroupOf C)) :=
    Components.quasisimple_of_equiv e (isQuasisimple_specialLinearGroup_two h4)
  obtain ⟨L₀, hL₀le, hL₀, hmap⟩ := exists_isTwoComponent_le (L.subgroupOf C) hLcsub hLcq
  have hsubnormalOf : ∀ N : Subgroup C, N.Normal → IsSubnormal N ⊤ := fun N hN =>
    IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤)
  have hLcle : L.subgroupOf C ≤ T.subgroupOf C ⊔ D.subgroupOf C := by
    rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_sup,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLC]
    exact hLle
  obtain ⟨S, hS, hL₀S⟩ := TwoComponentJoins.exists_le_of_le_sSup L₀ hL₀
    {T.subgroupOf C, D.subgroupOf C}
    (by
      intro S hS
      rcases Set.mem_insert_iff.mp hS with rfl | hS
      · exact hsubnormalOf _ inferInstance
      · rw [Set.mem_singleton_iff.mp hS]
        exact hsubnormalOf _ inferInstance)
    (by rw [sSup_pair]; exact hL₀le.trans hLcle)
  rcases Set.mem_insert_iff.mp hS with rfl | hS
  · left
    have h := le_of_map_eq_of_le hLc.perfect hmap hL₀S
    intro x hx
    exact h (show (⟨x, hLC hx⟩ : C) ∈ L.subgroupOf C from hx)
  · right
    rw [Set.mem_singleton_iff.mp hS] at hL₀S
    have h := le_of_map_eq_of_le hLc.perfect hmap hL₀S
    intro x hx
    exact h (show (⟨x, hLC hx⟩ : C) ∈ L.subgroupOf C from hx)

end Layer

section Connected

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]

theorem isQuasisimple_of_nonCommConnected (hLB : L2PrimeBalance) (hq : 4 ≤ p ^ f)
    (hO : classicalInvolutionOddCore Y = ⊥) {Λ : Set (Subgroup Y)} (hΛ : InClass p f Λ)
    (hconn : NonCommConnected Λ) : CFSG.Open.IsQuasisimple Y := by
  have hlayer := layer_eq_top hLB hq hO hΛ
  obtain ⟨L₀, hL₀⟩ := hΛ.nonempty
  obtain ⟨z₀, hz₀⟩ := hΛ.classical L₀ hL₀
  have hex : ∃ T : Subgroup Y, IsComponentOf T ⊤ ∧ L₀ ≤ T := by
    by_contra hno
    push Not at hno
    have hcent : ∀ T : Subgroup Y, IsComponentOf T ⊤ → L₀ ≤ Subgroup.centralizer (T : Set Y) :=
      fun T hT => (hz₀.le_or_le_centralizer_of_component hq hlayer hT).resolve_left (hno T hT)
    refine hz₀.not_le_center ?_
    have h1 : Layer.subgroup Y ≤ Subgroup.centralizer (L₀ : Set Y) :=
      sSup_le fun T hT => commutes_iff_le_centralizer.mp
        (commutes_iff_le_centralizer.mpr (hcent T hT)).symm
    rw [hlayer, top_le_iff, Subgroup.centralizer_eq_top_iff_subset] at h1
    exact h1
  obtain ⟨T₀, hT₀, hL₀T⟩ := hex
  have hall : ∀ v : ↥Λ, (nonCommGraph Λ).Reachable ⟨L₀, hL₀⟩ v → (v : Subgroup Y) ≤ T₀ := by
    intro v hv
    rw [SimpleGraph.reachable_iff_reflTransGen] at hv
    induction hv with
    | refl => exact hL₀T
    | @tail b c _ hadj ih =>
      obtain ⟨z, hz⟩ := hΛ.classical (c : Subgroup Y) c.2
      rcases hz.le_or_le_centralizer_of_component hq hlayer hT₀ with h | h
      · exact h
      · exfalso
        obtain ⟨-, hnc⟩ := nonCommGraph_adj.mp hadj
        exact hnc (fun x hx y hy => (commutes_iff_le_centralizer.mpr h y hy x (ih hx)).symm)
  have htop : T₀ = ⊤ := by
    rw [eq_top_iff, ← hΛ.generated]
    exact iSup₂_le fun M hM => hall ⟨M, hM⟩ (hconn.preconnected _ _)
  have hqs : CFSG.Open.IsQuasisimple T₀ := hT₀.2.2
  subst htop
  exact Components.quasisimple_of_equiv Subgroup.topEquiv.symm hqs

end Connected

end CFSG.ClassicalInvolution.Generic
