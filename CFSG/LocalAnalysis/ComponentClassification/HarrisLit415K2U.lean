module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

namespace L415

theorem pComponent_eq_of_normal_quasisimple {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hNq : CFSG.IsQuasisimple N) {L : Subgroup G} (hL : CFSG.IsPComponent p L) : L = N := by
  obtain ⟨hLN, hLN'⟩ := (CatalogueBFixedCentralQuotient.p_components_solvable_quotient_invariance
    p Fact.out N L).1 hL
  have hLsub : (L.subgroupOf N).IsSubnormal := hLN'.choose_spec.2.1
  have := CatalogueBAlternating.pComponent_nontrivial hLN'
  have := CatalogueBAlternating.pComponent_perfect hLN'
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hNq hLsub with h | h
  · refine le_antisymm hLN fun g hg => ?_
    have hmem : (⟨g, hg⟩ : N) ∈ L.subgroupOf N := by
      rw [h]
      trivial
    exact hmem
  · exfalso
    refine Group.IsPerfect.not_isMulCommutative (L.subgroupOf N) ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.1 (h x.2) y).symm

theorem layerIn_eq_of_unique {G : Type*} [Group G] [Finite G] {A J : Subgroup G}
    (hJ : IsTwoComponentIn J A) (huniq : ∀ J' : Subgroup G, IsTwoComponentIn J' A → J' = J) :
    GSThmB.layerIn A = J := by
  have hJA : J ≤ A := hJ.1
  have hset : {L : Subgroup ↥A | IsPComponent 2 L} = {J.subgroupOf A} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      have hLA : L.map A.subtype ≤ A := map_subtype_le L
      have h1 : IsTwoComponentIn (L.map A.subtype) A := by
        rw [isTwoComponentIn_iff hLA, subgroupOf_map_subtype_eq L]
        exact hL
      rw [← huniq _ h1, subgroupOf_map_subtype_eq L]
    · rintro rfl
      exact (isTwoComponentIn_iff hJA).mp hJ
  unfold GSThmB.layerIn pLayer
  rw [hset, sSup_singleton, subgroupOf_map_subtype, inf_eq_left.mpr hJA]

theorem eq_of_isTwoComponentIn_of_unique {X : Type} [Group X] [Finite X] {β z : X}
    (hzβ : z ∈ centralizer ({β} : Set X)) (hz : orderOf z = 2) {Y : Subgroup (MBar β)}
    (hY : ∀ J : Subgroup ↥(centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)}),
      IsPComponent 2 J → J = Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)}))
    {J₁ J₂ : Subgroup X} (h₁ : IsTwoComponentIn J₁ (centralizer {β} ⊓ centralizer {z}))
    (h₂ : IsTwoComponentIn J₂ (centralizer {β} ⊓ centralizer {z})) : J₁ = J₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let z' : ↥M := ⟨z, hzβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({z'} : Set ↥M)
  have hz'2 : z' * z' = 1 := Subtype.ext (by
    change z * z = 1
    rw [← sq, ← hz, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} :=
    map_centralizer_eq hodd hz'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨z, hzβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {z} := by
    rw [map_subtype_centralizer hzβ, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {z}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  have htr : ∀ J : Subgroup X, IsTwoComponentIn J (centralizer {β} ⊓ centralizer {z}) →
      IsPComponent 2 ((J.subgroupOf (centralizer {β} ⊓ centralizer {z})).map
        eC.symm.toMonoidHom) := by
    intro J hJ
    exact isPComponent_map_mulEquiv eC.symm ((isTwoComponentIn_iff hJ.1).mp hJ)
  have hJ₁ := htr J₁ h₁
  have hJ₂ := htr J₂ h₂
  have he : ((J₁.subgroupOf (centralizer {β} ⊓ centralizer {z})).map eC.symm.toMonoidHom).map
      φ = ((J₂.subgroupOf (centralizer {β} ⊓ centralizer {z})).map eC.symm.toMonoidHom).map φ := by
    rw [hY _ (hbij.mapsTo hJ₁), hY _ (hbij.mapsTo hJ₂)]
  have h3 := hbij.injOn hJ₁ hJ₂ he
  have h4 : J₁.subgroupOf (centralizer {β} ⊓ centralizer {z}) =
      J₂.subgroupOf (centralizer {β} ⊓ centralizer {z}) := by
    have h5 := congrArg (fun H => H.map eC.toMonoidHom) h3
    simp only [Subgroup.map_map] at h5
    rwa [show eC.toMonoidHom.comp eC.symm.toMonoidHom = MonoidHom.id _ by ext; simp,
      Subgroup.map_id, Subgroup.map_id] at h5
  have h6 := congrArg (fun H => H.map (centralizer ({β} : Set X) ⊓ centralizer {z}).subtype) h4
  simp only [subgroupOf_map_subtype, inf_eq_left.mpr h₁.1, inf_eq_left.mpr h₂.1] at h6
  exact h6

end L415

end CFSG.ComponentClassification.HarrisLit
