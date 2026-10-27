module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalStar
import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.UnbalancedLayer

theorem isHeldKType_gsFixedLayer (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L)
    {u : X} (hu : HeldTwoA L u) : IsHeldKType ↥(gsFixedLayer L u) := by
  obtain ⟨-, -, -, ⟨eL⟩, -⟩ := id hset
  have hKL : gsFixedLayer L u ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  obtain ⟨hKp, hKt⟩ := hLay X L ⟨eL⟩ u hu
  obtain ⟨hKcen, -, hKC⟩ := hAK X L ⟨eL⟩ u hu
  have hKel : ∀ z ∈ center ↥(gsFixedLayer L u), z * z = 1 := by
    intro z hz
    have hzc : ∀ k ∈ gsFixedLayer L u, (z : X) * k = k * z := fun k hk =>
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)).symm
    rcases hKC (z : X) (hKL z.2) hzc with h | ⟨hzA, -⟩
    · exact Subtype.ext (by simp [h])
    · have hsq : (z : X) * z = 1 := by rw [← sq, ← hzA.2.1, pow_orderOf_eq_one]
      exact Subtype.ext (by simpa using hsq)
  exact ⟨isPerfect_iff.mpr hKp, hKcen, hKel, hKt⟩

theorem heldKOrbitData (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L)
    {u : X} (hu : HeldTwoA L u) :
    ∃ (a : X) (ha : a ∈ centralizer ({u} : Set X)), orderOf a = 2 ∧
      a ∈ centralizer (L : Set X) ∧
      (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) ≤
          centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))) ∧
      IsPComponent 2 (((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).subgroupOf
          (centralizer ({⟨a, ha⟩} : Set ↥(centralizer ({u} : Set X))))) ∧
      (gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X)) ≤
        pLayer ↥(centralizer ({u} : Set X)) 2 := by
  obtain ⟨⟨-, -, -, -, -, ⟨a, ha2, hLa, hLc⟩, -⟩, -, hstd, -, -⟩ := id hset
  obtain ⟨-, -, hsub, -⟩ := hLc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haC : a ∈ centralizer (L : Set X) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hLa hh)
  have haD : a ∈ centralizer ({u} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haC u hu.1).symm
  have hCa : centralizer ({a} : Set X) ≤ normalizer (L : Set X) :=
    HeKN.centralizer_le_normalizer hstd haC ha2
  have hKLD : gsFixedLayer L u ≤ L ⊓ centralizer ({u} : Set X) := gsFixedLayer_le_inf L u
  have hKD : gsFixedLayer L u ≤ centralizer ({u} : Set X) := hKLD.trans inf_le_right
  have hKL : gsFixedLayer L u ≤ L := hKLD.trans inf_le_left
  have hKq : IsQuasisimple ↥(gsFixedLayer L u) :=
    (isHeldKType_gsFixedLayer hLay hAK hset hu).isQuasisimple
  set D : Subgroup X := centralizer ({u} : Set X)
  set t : ↥D := ⟨a, haD⟩ with htdef
  have hTC : (gsFixedLayer L u).subgroupOf D ≤ centralizer ({t} : Set ↥D) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_iff.mp haC (x : X) (hKL (mem_subgroupOf.mp hx)))
  have hconj : ∀ c ∈ centralizer ({t} : Set ↥D), ∀ y ∈ gsFixedLayer L u,
      (c : X) * y * (c : X)⁻¹ ∈ gsFixedLayer L u := by
    intro c hc y hy
    have hca : (c : X) ∈ centralizer ({a} : Set X) := by
      have := mem_centralizer_singleton_iff.mp hc
      exact mem_centralizer_singleton_iff.mpr (by
        have h := congrArg Subtype.val this
        simpa [htdef] using h)
    have hcL : (c : X) ∈ normalizer (L : Set X) := hCa hca
    have hcu : (c : X) * u * (c : X)⁻¹ = u := by
      have h := mem_centralizer_singleton_iff.mp (c : ↥D).2
      calc (c : X) * u * (c : X)⁻¹ = u * c * (c : X)⁻¹ := by rw [← h]
        _ = u := by group
    have h1 := GSLit.map_gsFixedLayer (MulAut.conj (c : X)) L u
    have h2 : L.map (MulAut.conj (c : X)).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp hcL
    rw [h2, MulAut.conj_apply, hcu] at h1
    have : (c : X) * y * (c : X)⁻¹ ∈ (gsFixedLayer L u).map (MulAut.conj (c : X)).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [h1] at this
  have hTn : (((gsFixedLayer L u).subgroupOf D).subgroupOf (centralizer ({t} : Set ↥D))).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
      simpa using hconj (g : ↥D) g.2 (n : ↥D) hn⟩
  have hTq : IsQuasisimple
      ↥(((gsFixedLayer L u).subgroupOf D).subgroupOf (centralizer ({t} : Set ↥D))) :=
    LocalCores.isQuasisimple_of_mulEquiv
      ((subgroupOfEquivOfLe hTC).trans (subgroupOfEquivOfLe hKD)).symm hKq
  have hT : IsPComponent 2 (((gsFixedLayer L u).subgroupOf D).subgroupOf
      (centralizer ({t} : Set ↥D))) :=
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent ⟨hTq, hTn.isSubnormal⟩
  have hTE : (gsFixedLayer L u).subgroupOf D ≤ pLayer ↥D 2 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := gsFixedLayer_le_pLayer_centralizer ha2 hLa hsub hu.1
      (mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    rwa [← this]
  exact ⟨a, haD, ha2, haC, hTC, hT, hTE⟩

theorem fixedComponent_orbit_trichotomy {H : Type*} [Group H] [Finite H] {t : H}
    (ht : orderOf t = 2) (hH : pPrimeCore 2 H = ⊥) {T : Subgroup H}
    (hTC : T ≤ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer ({t} : Set H)))) (hTE : T ≤ pLayer H 2) :
    T.IsSubnormal ∨
    ∃ M : Subgroup H, IsPComponent 2 M ∧ T ≤ M ⊔ conjugate M t ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))) ∧
      ((conjugate M t = M ∧ T ≤ M ∧
          (pPrimeCore 2 T).index < (pPrimeCore 2 M).index) ∨ conjugate M t ≠ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hM, hTM, hTp⟩ := two_layer_fixed_component_orbit_location ht hTC hT hTE
  by_cases hMt : conjugate M t = M
  · have hTM' : T ≤ M := by
      rw [hMt, sup_idem] at hTM
      exact hTM
    have hTCC : T ≤ (M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H) := le_inf hTM hTC
    obtain ⟨hle, -, heq⟩ := involution_orbit_fixed_component_quotient_comparison ht M hM _ rfl _
      rfl T hTCC hTp
    by_cases hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 M).index
    · exact Or.inr ⟨M, hM, hTM, hTp, Or.inl ⟨hMt, hTM', hlt⟩⟩
    · left
      have hindex := le_antisymm hle (not_lt.mp hlt)
      have hsup := (heq hindex).2 hMt.symm
      have hMsub : M.IsSubnormal :=
        ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM).1
      have hMcore : pPrimeCore 2 M = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hH hMsub
      rw [hMcore, Subgroup.map_bot, sup_bot_eq] at hsup
      rw [hsup]
      exact hMsub
  · exact Or.inr ⟨M, hM, hTM, hTp, Or.inr hMt⟩

end CFSG.ComponentClassification.GrSLit
