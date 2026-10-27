module

public import CFSG.CGT.Foote82.T66.BranchAOdd
import CFSG.CGT.Foote82.T66.Overgroup
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.CGT.Foote82.BranchAAux

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

section Components

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem isComponent_subgroupOf {Q H : Subgroup Γ} (hQ : IsComponentOf Q H) :
    CFSG.IsComponent (Q.subgroupOf H) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hQ.1).1
    (CFSG.Assembly.isComponentOf_iff_open.2 hQ)

theorem eq_or_commute_of_isComponentOf {Q₁ Q₂ H : Subgroup Γ} (h₁ : IsComponentOf Q₁ H)
    (h₂ : IsComponentOf Q₂ H) : Q₁ = Q₂ ∨ ⁅Q₁, Q₂⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf h₁)
    (isComponent_subgroupOf h₂) with he | hc
  · left
    rw [Subgroup.subgroupOf_inj, inf_eq_left.2 h₁.1, inf_eq_left.2 h₂.1] at he
    exact he
  · right
    have := congrArg (Subgroup.map H.subtype) hc
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁.1,
      Subgroup.map_subgroupOf_eq_of_le h₂.1, Subgroup.map_bot] at this

theorem le_or_commute_of_normal {Q U H : Subgroup Γ} (hQ : IsComponentOf Q H) (hUH : U ≤ H)
    (hU : (U.subgroupOf H).Normal) : Q ≤ U ∨ ⁅Q, U⁆ = ⊥ := by
  rcases CFSG.LocalCores.component_normal_subgroup (isComponent_subgroupOf hQ) hU with hle | hc
  · exact Or.inl (CFSG.LocalCores.le_of_subgroupOf_le hQ.1 hle)
  · right
    have := congrArg (Subgroup.map H.subtype) hc
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQ.1,
      Subgroup.map_subgroupOf_eq_of_le hUH, Subgroup.map_bot] at this

theorem map_conj_self {H : Subgroup Γ} {g : Γ} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_map_conj_iff]
  constructor
  · intro hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [this]
    exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
  · intro hx
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg

theorem isComponentOf_conj {Q H : Subgroup Γ} (hQ : IsComponentOf Q H) {g : Γ} (hg : g ∈ H) :
    IsComponentOf (Q.map (MulAut.conj g).toMonoidHom) H := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_conj_self hg]
    exact Subgroup.map_mono hQ.1
  · have := hQ.2.1.map (MulAut.conj g).toMonoidHom
    rwa [map_conj_self hg] at this
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Q.equivMapOfInjective _ (MulAut.conj g).injective).symm hQ.2.2

theorem sSup_le_normalizer {Q H : Subgroup Γ} (hQ : IsComponentOf Q H) :
    sSup {P : Subgroup Γ | IsComponentOf P H} ≤ Subgroup.normalizer (Q : Set Γ) := by
  refine sSup_le fun P hP => ?_
  rcases eq_or_commute_of_isComponentOf hP hQ with rfl | hc
  · exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc).trans
      (Subgroup.centralizer_le_normalizer _)

theorem not_isSolvable_of_isQuasisimple {Q : Subgroup Γ} (hQ : CFSG.Open.IsQuasisimple ↥Q) :
    ¬ Group.IsSolvable ↥Q := by
  have hQ' : CFSG.IsQuasisimple ↥Q :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Q).1 hQ
  have : Nontrivial ↥Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ'
  have : Group.IsPerfect ↥Q := hQ'.1
  exact Group.IsPerfect.not_isSolvable ↥Q

end Components

section Gen

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

abbrev classClosure (G : Subgroup (GLV V)) (z : GLV V) : Subgroup (GLV V) :=
  Subgroup.closure {x | ∃ g ∈ G, x = g * z * g⁻¹}

theorem classClosure_le (hz : z ∈ G) : classClosure G z ≤ G := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact G.mul_mem (G.mul_mem hg hz) (G.inv_mem hg)

theorem mem_classClosure (hz : z ∈ G) : z ∈ classClosure G z :=
  Subgroup.subset_closure ⟨1, G.one_mem, by group⟩

theorem conj_mem_classClosure {g x : GLV V} (hg : g ∈ G) (hx : x ∈ classClosure G z) :
    g * x * g⁻¹ ∈ classClosure G z := by
  have hle : classClosure G z ≤ (classClosure G z).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    show g * (k * z * k⁻¹) * g⁻¹ ∈ classClosure G z
    exact Subgroup.subset_closure ⟨g * k, G.mul_mem hg hk, by group⟩
  exact hle hx

theorem commutator_mem_classClosure (hz : z ∈ G) {g : GLV V} (hg : g ∈ G) :
    g * z * g⁻¹ * z⁻¹ ∈ classClosure G z :=
  Subgroup.mul_mem _ (Subgroup.subset_closure ⟨g, hg, rfl⟩)
    (Subgroup.inv_mem _ (mem_classClosure hz))

theorem layerIn_le_normalizer {J : Subgroup (GLV V)} (hJ : IsComponentOf J G) :
    layerIn G ≤ Subgroup.normalizer (J : Set (GLV V)) := by
  rw [layerIn_eq_sSup]
  exact sSup_le_normalizer hJ

theorem false_of_centralizes (h : StdForm G L z) {J : Subgroup (GLV V)} (hJ : IsComponentOf J G)
    (hzJ : z ∈ Subgroup.centralizer (J : Set (GLV V))) : False := by
  have hJG : J ≤ G := hJ.1
  have hGN : G ≤ Subgroup.normalizer (J : Set (GLV V)) := by
    rw [h.eq_layerIn_sup]
    exact sup_le (layerIn_le_normalizer hJ)
      ((Subgroup.zpowers_le).2 (Subgroup.centralizer_le_normalizer _ hzJ))
  set C := G ⊓ Subgroup.centralizer ({z} : Set (GLV V)) with hC
  have hLC : IsComponentOf L C :=
    h.component_of_inv z (z_mem_G h) h.orderOf_s (z_mem_cent h)
  have hJC : J ≤ C := by
    intro j hj
    refine Subgroup.mem_inf.2 ⟨hJG hj, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 hzJ) j hj
  have hJn : (J.subgroupOf C).Normal := by
    constructor
    intro x hx c
    exact (Subgroup.mem_normalizer_iff.1 (hGN (Subgroup.mem_inf.1 c.2).1) x).1 hx
  rcases le_or_commute_of_normal hLC hJC hJn with hLJ | hLJ
  ·
    have hJGn : IsSubnormal J G := by
      refine .step hJG ?_ (.refl G)
      constructor
      intro x hx c
      exact (Subgroup.mem_normalizer_iff.1 (hGN c.2) x).1 hx
    have hLJs : IsSubnormal L J := by
      have := hLC.2.1.inf_of_le hJC
      rwa [inf_eq_left.2 hLJ] at this
    have hLG : IsComponentOf L G := ⟨L_le_G h, hLJs.trans hJGn, hLC.2.2⟩
    apply not_le_normalizer h
    intro g hg
    rcases eq_or_commute_of_isComponentOf hLG (isComponentOf_conj hLG hg) with heq | hc
    · rw [Subgroup.mem_normalizer_iff]
      intro l
      constructor
      · intro hl
        rw [heq]
        exact ⟨l, hl, rfl⟩
      · intro hl
        have : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := by rw [← heq]; exact hl
        rw [mem_map_conj_iff] at this
        simpa [mul_assoc] using this
    · exact absurd hc (h.commutator_ne_bot g hg)
  ·
    obtain ⟨g, hg, hgN⟩ := exists_not_mem_normalizer h
    have hJK : J ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
      intro j hj
      refine Subgroup.mem_inf.2 ⟨hJG hj, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLJ hl
      exact (Subgroup.mem_centralizer_iff.1 this j hj).symm
    have hJKg : J ≤ (G ⊓ Subgroup.centralizer (L : Set (GLV V))) ⊓
        (G ⊓ Subgroup.centralizer (L : Set (GLV V))).map (MulAut.conj g).toMonoidHom := by
      intro j hj
      refine Subgroup.mem_inf.2 ⟨hJK hj, ?_⟩
      rw [mem_map_conj_iff]
      have hginv : g⁻¹ ∈ Subgroup.normalizer (J : Set (GLV V)) := hGN (G.inv_mem hg)
      have := (Subgroup.mem_normalizer_iff.1 hginv j).1 hj
      rw [inv_inv] at this
      exact hJK this
    have hodd : Odd (Nat.card J) :=
      Odd.of_dvd_nat (h.tight g hg hgN) (Subgroup.card_dvd_of_le hJKg)
    exact not_isSolvable_of_isQuasisimple hJ.2.2 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd)

theorem isComponentOf_le_classClosure (h : StdForm G L z) {J : Subgroup (GLV V)}
    (hJ : IsComponentOf J G) : J ≤ classClosure G z := by
  have hzG := z_mem_G h
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1 hJ.2.2
  have hJperf : Group.IsPerfect ↥J := hJq.1
  have hJp : ⁅J, J⁆ = J := commutator_eq_self_of_isQuasisimple hJ.2.2
  by_cases hzN : z ∈ Subgroup.normalizer (J : Set (GLV V))
  ·
    have hN : ((J ⊓ classClosure G z).subgroupOf J).Normal := by
      constructor
      intro x hx j
      exact ⟨J.mul_mem (J.mul_mem j.2 hx.1) (J.inv_mem j.2),
        conj_mem_classClosure (hJ.1 j.2) hx.2⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hJq hN with htop | hcen
    · intro j hj
      have : (⟨j, hj⟩ : ↥J) ∈ (J ⊓ classClosure G z).subgroupOf J := by rw [htop]; trivial
      exact this.2
    · exfalso
      have hcomm : ∀ c ∈ J ⊓ classClosure G z, ∀ j ∈ J, c * j = j * c := by
        intro c hc j hj
        have := Subgroup.mem_center_iff.1 (hcen (show (⟨c, hc.1⟩ : ↥J) ∈ _ from hc)) ⟨j, hj⟩
        exact (congrArg Subtype.val this).symm
      have hcle : ⁅J, Subgroup.zpowers z⁆ ≤ J ⊓ classClosure G z := by
        rw [Subgroup.commutator_le]
        intro j' hj' w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
        have hzn : z ^ n ∈ Subgroup.normalizer (J : Set (GLV V)) := Subgroup.zpow_mem _ hzN n
        have hzn' : z ^ n ∈ classClosure G z := Subgroup.zpow_mem _ (mem_classClosure hzG) n
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · have h1 : z ^ n * j'⁻¹ * (z ^ n)⁻¹ ∈ J :=
            (Subgroup.mem_normalizer_iff.1 hzn _).1 (J.inv_mem hj')
          have e : j' * z ^ n * j'⁻¹ * (z ^ n)⁻¹ = j' * (z ^ n * j'⁻¹ * (z ^ n)⁻¹) := by group
          rw [commutatorElement_def, e]
          exact J.mul_mem hj' h1
        · rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (conj_mem_classClosure (hJ.1 hj') hzn')
            (Subgroup.inv_mem _ hzn')
      have hc : ⁅J, Subgroup.zpowers z⁆ = ⊥ := by
        refine CFSG.LocalCores.perfect_double_commutator hJperf ?_
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro c hc j hj
        rw [Subgroup.mem_bot, commutatorElement_def, hcomm c (hcle hc) j hj]
        group
      apply false_of_centralizes h hJ
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have := Subgroup.commutator_mem_commutator hj (Subgroup.mem_zpowers z)
      rw [hc, Subgroup.mem_bot, commutatorElement_def] at this
      calc j * z = (j * z * j⁻¹ * z⁻¹) * z * j := by group
        _ = z * j := by rw [this, one_mul]
  ·
    have hJz : IsComponentOf (J.map (MulAut.conj z).toMonoidHom) G := isComponentOf_conj hJ hzG
    rcases eq_or_commute_of_isComponentOf hJ hJz with heq | hc
    · exfalso
      apply hzN
      rw [Subgroup.mem_normalizer_iff]
      intro j
      constructor
      · intro hj
        rw [heq]
        exact ⟨j, hj, rfl⟩
      · intro hj
        rw [heq, mem_map_conj_iff] at hj
        simpa [mul_assoc] using hj
    · rw [← hJp, Subgroup.commutator_le]
      intro j₁ hj₁ j₂ hj₂
      have hc₁ : z * j₁⁻¹ * z⁻¹ ∈ J.map (MulAut.conj z).toMonoidHom := by
        rw [mem_map_conj_iff]
        simpa [mul_assoc] using J.inv_mem hj₁
      have hcomm : z * j₁⁻¹ * z⁻¹ * j₂ = j₂ * (z * j₁⁻¹ * z⁻¹) :=
        Subgroup.mem_centralizer_iff.1
          (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc hj₂) _ hc₁
      have hx : j₁ * (z * j₁⁻¹ * z⁻¹) ∈ classClosure G z := by
        have := commutator_mem_classClosure hzG (hJ.1 hj₁)
        simpa [mul_assoc] using this
      have e : ⁅j₁, j₂⁆ = (j₁ * (z * j₁⁻¹ * z⁻¹)) *
          (j₂ * (j₁ * (z * j₁⁻¹ * z⁻¹))⁻¹ * j₂⁻¹) := by
        rw [commutatorElement_def]
        calc j₁ * j₂ * j₁⁻¹ * j₂⁻¹ =
            j₁ * (j₂ * (z * j₁⁻¹ * z⁻¹)) * (z * j₁⁻¹ * z⁻¹)⁻¹ * j₁⁻¹ * j₂⁻¹ := by group
          _ = j₁ * (z * j₁⁻¹ * z⁻¹ * j₂) * (z * j₁⁻¹ * z⁻¹)⁻¹ * j₁⁻¹ * j₂⁻¹ := by rw [hcomm]
          _ = _ := by group
      rw [e]
      exact Subgroup.mul_mem _ hx (conj_mem_classClosure (hJ.1 hj₂) (Subgroup.inv_mem _ hx))

theorem eq_classClosure (h : StdForm G L z) : G = classClosure G z := by
  refine le_antisymm ?_ (classClosure_le (z_mem_G h))
  conv_lhs => rw [h.eq_layerIn_sup]
  refine sup_le ?_ ((Subgroup.zpowers_le).2 (mem_classClosure (z_mem_G h)))
  rw [layerIn_eq_sSup]
  exact sSup_le fun J hJ => isComponentOf_le_classClosure h hJ

theorem commutator_eq_layerIn (h : StdForm G L z) : ⁅G, G⁆ = layerIn G := by
  apply le_antisymm
  ·
    have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
    have htop : CFSG.layer ↥G ⊔ Subgroup.zpowers (⟨z, z_mem_G h⟩ : ↥G) = ⊤ := by
      apply Subgroup.map_injective G.subtype_injective
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype]
      exact h.eq_layerIn_sup.symm
    have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop
      (Subgroup.zpowers_isMulCommutative _)
    have := Subgroup.map_mono (f := G.subtype) hle
    rwa [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      Subgroup.range_subtype] at this
  · calc layerIn G = ⁅layerIn G, layerIn G⁆ := by
          rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]
      _ ≤ ⁅G, G⁆ := Subgroup.commutator_mono (layerIn_le G) (layerIn_le G)

end Gen

end CFSG.CGT.Foote82.BranchAAux
