module

public import CFSG.GH74.E2.ComponentsBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Stage12.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

variable {G : Type} [Group G]

theorem map_centralizer_conj (x g : G) :
    (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * x * g⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w ∈ centralizer ({x} : Set G) := hw
    rw [mem_centralizer_singleton_iff] at hw'
    rw [mem_centralizer_singleton_iff]
    change g * w * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * w * g⁻¹)
    calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hw']
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  · intro hz
    rw [mem_centralizer_singleton_iff] at hz
    refine ⟨g⁻¹ * z * g, ?_, by change g * (g⁻¹ * z * g) * g⁻¹ = z; group⟩
    show g⁻¹ * z * g ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h1 : z * (g * x * g⁻¹) = g * x * g⁻¹ * z := hz
    calc g⁻¹ * z * g * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [h1]
      _ = x * (g⁻¹ * z * g) := by group

@[expose] noncomputable def cenConj (x g : G) :
    ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({g * x * g⁻¹} : Set G)) :=
  (MulEquiv.subgroupMap (MulAut.conj g) (centralizer ({x} : Set G))).trans
    (MulEquiv.subgroupCongr (map_centralizer_conj x g))

@[expose] noncomputable def barConj (x g : G) : CentralizerBar x ≃* CentralizerBar (g * x * g⁻¹) :=
  QuotientGroup.congr (pPrimeCore 2 ↥(centralizer ({x} : Set G)))
    (pPrimeCore 2 ↥(centralizer ({g * x * g⁻¹} : Set G))) (cenConj x g)
    (pPrimeCore_map_iso 2 (cenConj x g))

@[expose] def Good (K : Type) [Group K] : Prop := InC2 K ∨ InT2 K

theorem Good.of_mulEquiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : Good K) : Good K' :=
  h.imp (E2.inC2_of_mulEquiv e) (TwoThin.inT2_of_mulEquiv e)

theorem Good.not_inG2 {K : Type} [Group K] (h : Good K) : ¬ InG2 K := fun hg => by
  rcases h with h | h
  · exact hg.2.1 h
  · exact hg.2.2 h

@[expose] def CompsGood (z : G) : Prop :=
  ∀ K : Subgroup (CentralizerBar z), IsComponent K → Good ↥K

theorem compsGood_conj {z : G} (g : G) (h : CompsGood z) : CompsGood (g * z * g⁻¹) := by
  intro K' hK'
  have hK : IsComponent (K'.map (barConj z g).symm.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (barConj z g).symm hK'
  exact (h _ hK).of_mulEquiv
    (K'.equivMapOfInjective (barConj z g).symm.toMonoidHom (barConj z g).symm.injective).symm

theorem compsGood_of_isConj {z x : G} (hzx : IsConj z x) (h : CompsGood z) : CompsGood x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hzx
  subst hc
  exact compsGood_conj c h

theorem not_l2Meets_inG2_of_reps {z x : G} (hz : CompsGood z) (hx : CompsGood x)
    (hcl : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u) : ¬ L2Meets G InG2 := by
  rintro ⟨u, hu, K, hK, hG2⟩
  rcases hcl u hu with h | h
  · exact (compsGood_of_isConj h hz K hK).not_inG2 hG2
  · exact (compsGood_of_isConj h hx K hK).not_inG2 hG2

theorem not_l2Meets_inG2_of_oneClass {z : G} (hz : CompsGood z)
    (hcl : ∀ u : G, orderOf u = 2 → IsConj z u) : ¬ L2Meets G InG2 :=
  not_l2Meets_inG2_of_reps hz hz fun u hu => Or.inl (hcl u hu)

theorem false_of_component_isSolvable {X : Type} [Group X] {K : Subgroup X} (hK : IsComponent K)
    (hs : Group.IsSolvable ↥K) : False := by
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect ↥K := hK.1.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance

theorem isComponent_eq_top_of_isQuasisimple {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    {K : Subgroup X} (hK : IsComponent K) : K = ⊤ := by
  have hXc : IsComponent (⊤ : Subgroup X) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hX, Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hK hXc with h | h
  · exact h
  · exfalso
    have hle : K ≤ center X := Subgroup.commutator_top_right_eq_bot_iff_le_center.mp h
    exact false_of_component_isSolvable hK
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))

theorem comp_eq_of_le {X : Type} [Group X] [Finite X] {K L : Subgroup X} (hK : IsComponent K)
    (hKL : K ≤ L) (hL : IsQuasisimple ↥L) : K = L := by
  have h2 := isComponent_eq_top_of_isQuasisimple hL (CFSG.LocalCores.component_overgroup hK hKL)
  refine le_antisymm hKL fun x hx => ?_
  have : (⟨x, hx⟩ : L) ∈ K.subgroupOf L := by rw [h2]; trivial
  exact this

end CFSG.GH74.GLS.Stage2.Local.Prop28
