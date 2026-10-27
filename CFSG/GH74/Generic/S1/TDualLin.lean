module

public import CFSG.GH74.Generic.S1.TDualCore
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.GH74.Generic.S1.RQ3Lin

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

theorem choose_coords (i j : Fin 5) :
    ∃ c d : Fin 4, c ≠ d ∧ Fin.castSucc c ≠ i ∧ Fin.castSucc c ≠ j ∧ Fin.castSucc d ≠ i ∧
      Fin.castSucc d ≠ j := by
  revert i j
  decide

section Layer

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

@[expose] def layerDataOf (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (e : ↥K ≃* ↥S) : LayerData x S :=
  ⟨K, Subgroup.isPerfect_iff.mp hset.comp.1.1, normal_of_layer_eq hfront.layer_eq,
    fun P hP => hfront.good_le P (Or.inl hP), hExact G x K hset hfront, e⟩

theorem ι_comm_symX {x : G} (D : LayerData x S) {u : Fin 4 → G}
    (hu : ∀ k, u k ∈ centralizer ({x} : Set G))
    (hact : ∀ k, ActsAsReflOn D.iso (barOf (hu k)) (reflDiag F k)) (blk : Subgroup ↥S) {c d : Fin 4}
    (hcomm : ∀ s ∈ blk, ∀ k, k ≠ c → k ≠ d →
      (s : GL (Fin 4) F) * reflDiag F k = reflDiag F k * (s : GL (Fin 4) F))
    {m : Fin 5} (hmc : Fin.castSucc c ≠ m) (hmd : Fin.castSucc d ≠ m) {s : ↥S} (hs : s ∈ blk) :
    D.ι s * symX x u m = symX x u m * D.ι s := by
  revert hmc hmd
  refine Fin.lastCases ?_ (fun k => ?_) m
  · intro _ _
    rw [symX_last]
    exact D.ι_comm_self s
  · intro hkc hkd
    rw [symX_castSucc]
    have hkc' : k ≠ c := fun h => hkc (by rw [h])
    have hkd' : k ≠ d := fun h => hkd (by rw [h])
    exact D.ι_comm_of (hu k) (hact k) (hcomm s hs k hkc' hkd')

end Layer

section Pair

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]

theorem exists_q8_blkLin [Finite F] (hF : Nat.card F % 4 = 3) {c d : Fin 4} (hcd : c ≠ d) :
    ∃ q8 : QuaternionGroup 2 →* ↥(StatedSL 4 F), Function.Injective q8 ∧
      ∀ g, q8 g ∈ blkLin (F := F) c d := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  obtain ⟨a, b, hab⟩ := (odd_field_two_dimensional_quaternion_matrices hF2).1
  obtain ⟨eb⟩ := blkLin_equiv (F := F) c d hcd
  let qh : QuaternionGroup 2 →* SL(2, F) := quatHom hab
  have hqh : Function.Injective qh := quatHom_injective hF2 hab
  refine ⟨(blkLin (F := F) c d).subtype.comp (eb.toMonoidHom.comp qh), ?_, fun g => (eb (qh g)).2⟩
  exact (blkLin (F := F) c d).subtype_injective.comp (eb.injective.comp hqh)

theorem not_exotic_lin_of_frame (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) {u : Fin 4 → G}
    {hu : ∀ k, u k ∈ centralizer ({x} : Set G)} [Finite F] (hF : Nat.card F % 4 = 3)
    (e : ↥K ≃* ↥(StatedSL 4 F)) (hact : ∀ k, ActsAsReflOn e (barOf (hu k)) (reflDiag F k))
    (i j : Fin 5) {K' : Subgroup (CentralizerBar (symX x u i))} [K'.Normal]
    (hfront' : S1Front G (symX x u i) K')
    (hv : symX x u j ∈ centralizer ({symX x u i} : Set G)) (e' : ↥K' ≃* ↥(StatedSL 4 F)) :
    ¬ IsExoticLin (StatedSL 4 F) (MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K')) := by
  classical
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨c, d, hcd, hci, hcj, hdi, hdj⟩ := choose_coords i j
  set D := layerDataOf hExact hset hfront e with hD
  have hactD : ∀ k, ActsAsReflOn D.iso (barOf (hu k)) (reflDiag F k) := hact
  obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_blkLin hF hcd
  have hgood : ⁅blkLin (F := F) c d, blkLin (F := F) c d⁆ = blkLin (F := F) c d ∨
      (OddGenerated (blkLin (F := F) c d) ∧ ThreeModel ↥K') := by
    by_cases h3 : Nat.card F = 3
    · right
      exact ⟨blkLin_oddGenerated hodd c d hcd, F, inferInstance, inferInstance, h3, Or.inl ⟨e'⟩⟩
    · left
      have hpos : 0 < Nat.card F := Nat.card_pos
      exact blkLin_perfect (by omega) c d hcd
  have hcomm : ∀ s ∈ blkLin (F := F) c d, ∀ k, k ≠ c → k ≠ d →
      (s : GL (Fin 4) F) * reflDiag F k = reflDiag F k * (s : GL (Fin 4) F) :=
    fun s hs k hkc hkd => blkLin_comm_refl c d k hkc hkd s hs
  have hy : ∀ s ∈ blkLin (F := F) c d, D.ι s * symX x u i = symX x u i * D.ι s :=
    fun s hs => ι_comm_symX D hu hactD (blkLin (F := F) c d) hcomm hci hdi hs
  have hvc : ∀ s ∈ blkLin (F := F) c d, D.ι s * symX x u j = symX x u j * D.ι s :=
    fun s hs => ι_comm_symX D hu hactD (blkLin (F := F) c d) hcomm hcj hdj hs
  obtain ⟨Φ, hΦ, hfix⟩ := exists_fixed_q8 D (blkLin (F := F) c d) hfront' hgood q8 hq8 hq8blk hy hv hvc e'
  exact no_exotic_of_fixed_q8_lin h2 _ Φ hΦ hfix

end Pair

section Sym

variable {G : Type} [Group G] [Finite G]

theorem outer_reflection_lin_of_noExotic {y : G} {K : Subgroup (CentralizerBar y)} [K.Normal]
    (hset : S1Setup G y K) (hfront : S1Front G y K) {v : G} (hv : v ∈ centralizer ({y} : Set G))
    (hconj : IsConj y v) (hvy : v ≠ y) (hv2 : v * v = 1) (hvK : barOf hv ∉ K) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F % 4 = 3) (e : ↥K ≃* ↥(StatedSL 4 F))
    (hNoExo : ¬ IsExoticLin (StatedSL 4 F) (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))) :
    IsReflection (StatedSL 4 F) (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K)) := by
  have hxK : xbar y ∈ K := hset.shape.2
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar y)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  obtain ⟨hα2, hout⟩ := conjNormal_involutory hcentle hv hv2 hvK
  have hnotA := not_goodFixed_conjNormal hset.inv hxK hfront hv hconj hvy hv2
  have hback : ∀ (hA : GoodFixedCentral (Nat.card F = 3)
      (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))), False := fun hA => by
    apply hnotA
    have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => ⟨F, inferInstance,
      inferInstance, h, Or.inl ⟨e⟩⟩)
    rwa [congr_symm_congr] at h1
  rcases linClassify F hF (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
    (congr_mul_self_eq_one e hα2) (congr_not_inner e hout) with hA | hR | hG
  · exact (hback hA).elim
  · exact hR
  · rcases graphLinRefine F hF (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
      (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exact (hback hA).elim
    · exact (hNoExo hE).elim

theorem sym_at_dual {x : G} {K : Subgroup (CentralizerBar x)} [K.Normal] (hset : S1Setup G x K)
    (hfront : S1Front G x K) {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}
    (ops : ModelOps F S) (e : ↥K ≃* ↥S) (Good : G → G → Prop)
    (reflOf : ∀ (y : G) (K' : Subgroup (CentralizerBar y)) [K'.Normal], S1Setup G y K' →
      S1Front G y K' → ∀ (e' : ↥K' ≃* ↥S) {v : G} (hv : v ∈ centralizer ({y} : Set G)),
        Good y v → IsConj y v → v ≠ y → v * v = 1 → barOf hv ∉ K' →
          IsReflection S (MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K')))
    {y : G} (hy : IsConj x y) (w : Fin 4 → G) (hw : ∀ j, w j ∈ centralizer ({y} : Set G))
    (hgood : ∀ j, Good y (w j))
    (hw2 : ∀ j, w j * w j = 1) (hwc : ∀ j k, w j * w k = w k * w j)
    (hwconj : ∀ j, IsConj y (w j)) (hwne : ∀ j, w j ≠ y)
    (hind2 : ∀ j k, j ≠ k → w j * w k ≠ 1) (hind3 : ∀ j k, j ≠ k → w j * w k * y ≠ 1)
    (hprod : w 0 * w 1 * w 2 * w 3 = y) :
    ∃ K' : Subgroup (CentralizerBar y), S1Setup G y K' ∧ S1Front G y K' ∧
      (∀ j, IsConj y (w j) ∧ w j * w j = 1 ∧ barOf (hw j) ∉ K') ∧
        (∀ j k, w j * w k = w k * w j) ∧ w 0 * w 1 * w 2 * w 3 = y ∧
          (∀ j k, j ≠ k → w j ≠ w k) ∧
            ∃ e'' : ↥K' ≃* ↥S, ∀ j, ActsAsReflOn e'' (barOf (hw j)) (reflDiag F j) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hy
  have hset' := hset.conj g
  have hfront' := hfront.conj g
  have hKn : (K.map (barConj x g).toMonoidHom).Normal := normal_of_layer_eq hfront'.layer_eq
  let e' : ↥(K.map (barConj x g).toMonoidHom) ≃* ↥S :=
    (K.equivMapOfInjective (barConj x g).toMonoidHom (barConj x g).injective).symm.trans e
  have hnotK : ∀ j, barOf (hw j) ∉ K.map (barConj x g).toMonoidHom := fun j =>
    barOf_notMem hset' hfront' (hw j) (hw2 j) (hwconj j) (hwne j)
  have hR : ∀ j, IsReflection S (MulAut.congr e'
      (MulAut.conjNormal (barOf (hw j)) : MulAut ↥(K.map (barConj x g).toMonoidHom))) := fun j =>
    reflOf _ _ hset' hfront' e' (hw j) (hgood j) (hwconj j) (hwne j) (hw2 j) (hnotK j)
  obtain ⟨h1, h2, h3, h4, e'', h5⟩ :=
    sym_local hset' hfront' ops e' w hw hw2 hwc hwconj hwne hind2 hind3 hprod hR
  exact ⟨_, hset', hfront', h1, h2, h3, h4, e'', h5⟩

theorem s1_symFrame_lin_dual (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    [K.Normal] (hset : S1Setup G x K) (hfront : S1Front G x K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) (e : ↥K ≃* ↥(StatedSL 4 F))
    (hact : ∀ k, ActsAsReflOn e (barOf (hu k)) (reflDiag F k)) : S1SymFrameLin x u F := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  intro i
  obtain ⟨hy, hw, hw2, hwc, hwconj, hwne, hind2, hind3, hprod⟩ :=
    sym_hyps hset.shape.2 hset.inv hf i
  obtain ⟨K', hset', hfront', h1, h2', h3, h4, e'', he''⟩ :=
    sym_at_dual hset hfront (linOps h2) e (fun y v => ∃ m n : Fin 5, m ≠ n ∧ y = symX x u m ∧ v = symX x u n)
      (fun y K' _ hs hfr e' v hv hgd hc hvy hv2 hvK => by
        obtain ⟨m, n, hmn, rfl, rfl⟩ := hgd
        exact outer_reflection_lin_of_noExotic hs hfr hv hc hvy hv2 hvK hF e'
          (not_exotic_lin_of_frame hExact hset hfront hF e hact m n hfr hv e'))
      hy (fun j => symX x u (i.succAbove j)) hw
      (fun j => ⟨i, i.succAbove j, (Fin.succAbove_ne i j).symm, rfl, rfl⟩) hw2 hwc hwconj hwne hind2
      hind3 hprod
  exact ⟨K', hw, hset', hfront', ⟨h1, h2', h3, h4, Or.inl ⟨F, inferInstance, inferInstance, e'', hF,
    he''⟩⟩, e'', he''⟩

end Sym

end CFSG.GH74.Generic.S1
