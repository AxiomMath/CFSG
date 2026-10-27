module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePConfig
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYSummary

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki.PFAppendixIII

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

structure StarLift (B : Subgroup J) (z u : J) : Prop extends EscapingLift B z u where
  rank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)
  star : ∃ L : Subgroup (QuasiQuotient u),
    OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
    Nat.card (Subgroup.center L) = 2 ∧ quasiBar u ∉ L ∧
    Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) ∧
    ∀ x : QuasiQuotient u, orderOf x = 2 →
      x ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u))

theorem BadLift.starLift
    (hu : BadLift B z u) (h : Setting J Q B) (hz : FourGen Q z)
    (IH : CanonicalBelow (Nat.card J)) (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    StarLift B z u :=
  ⟨hu.toEscapingLift, hrank, hu.exists_alternating_component h hz IH hrank⟩

theorem EscapingLift.false_of_pair (hu : EscapingLift B z u) (h : Setting J Q B) {q₁ q₂ : J}
    (hq₁ : q₁ * u = u * q₁) (hq₂ : q₂ * u = u * q₂) (hq₁q₁ : q₁ * q₁ = centralElt J)
    (hq₂q₂ : q₂ * q₂ = centralElt J) (hq₁u : q₁ * u ≠ 1) (hq₂u : q₂ * u ≠ 1)
    (hq₁₂ : q₁ * q₂ * (q₁ * q₂) = centralElt J) {H : Subgroup (QuasiQuotient u)}
    (hinv : ∀ t : quasiNormalizer u, orderOf t = 2 → quasiMk u t ∈ H)
    (hsq : ∀ x ∈ H, x * x ≠ quasiCentral u) : False := by
  have he := h.centralElt_mul_self
  have hmem : ∀ {q : J}, q * u = u * q → q * u ∈ quasiNormalizer u := fun {q} hq => by
    refine (quasiNormalizer u).mul_mem ((h.mem_normalizer_zpowers_iff hu.sq).mpr ?_)
      (Subgroup.le_normalizer (Subgroup.mem_zpowers u))
    rw [hq, mul_inv_cancel_right, mul_inv_cancel]
    exact (Subgroup.center J).one_mem
  have hord : ∀ {q : J}, q * u = u * q → q * q = centralElt J → q * u ≠ 1 →
      orderOf (q * u) = 2 := fun {q} hq hqq hqu => by
    refine orderOf_eq_prime ?_ hqu
    rw [pow_two, show q * u * (q * u) = q * q * (u * u) by
      rw [show q * u * (q * u) = q * (u * q) * u by group, ← hq]; group, hqq, hu.sq, he]
  set t₁ : quasiNormalizer u := ⟨q₁ * u, hmem hq₁⟩
  set t₂ : quasiNormalizer u := ⟨q₂ * u, hmem hq₂⟩
  have h₁ : quasiMk u t₁ ∈ H := hinv t₁ (by rw [Subgroup.orderOf_mk]; exact hord hq₁ hq₁q₁ hq₁u)
  have h₂ : quasiMk u t₂ ∈ H := hinv t₂ (by rw [Subgroup.orderOf_mk]; exact hord hq₂ hq₂q₂ hq₂u)
  apply hsq _ (H.mul_mem h₁ h₂)
  rw [← map_mul, ← map_mul, ← hu.quasiMk_centralElt h]
  congr 1
  apply Subtype.ext
  change q₁ * u * (q₂ * u) * (q₁ * u * (q₂ * u)) = centralElt J
  have hprod : q₁ * u * (q₂ * u) = q₁ * q₂ * centralElt J := by
    rw [← hu.sq, show q₁ * u * (q₂ * u) = q₁ * (u * q₂) * u by group, ← hq₂]
    group
  rw [hprod, show q₁ * q₂ * centralElt J * (q₁ * q₂ * centralElt J) =
      q₁ * q₂ * (q₁ * q₂) * (centralElt J * centralElt J) by
    rw [show q₁ * q₂ * centralElt J * (q₁ * q₂ * centralElt J) =
        q₁ * q₂ * (centralElt J * (q₁ * q₂)) * centralElt J by group,
      ← (h.commute_centralElt (q₁ * q₂)).eq]
    group, he, hq₁₂, mul_one]

theorem EscapingLift.starLift_of_pair
    (hu : EscapingLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J))
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) {q₁ q₂ : J}
    (hq₁ : q₁ * u = u * q₁) (hq₂ : q₂ * u = u * q₂) (hq₁q₁ : q₁ * q₁ = centralElt J)
    (hq₂q₂ : q₂ * q₂ = centralElt J) (hq₁u : q₁ * u ≠ 1) (hq₂u : q₂ * u ≠ 1)
    (hq₁₂ : q₁ * q₂ * (q₁ * q₂) = centralElt J) : StarLift B z u := by
  have hc := hu.baseConfig h hz hrank
  have hno := fun {H : Subgroup (QuasiQuotient u)} =>
    hu.false_of_pair h hq₁ hq₂ hq₁q₁ hq₂q₂ hq₁u hq₂u hq₁₂ (H := H)
  have hall : ∀ L : Subgroup (QuasiQuotient u), CFSG.IsComponent L → quasiCentral u ∈ L := by
    intro L hL
    by_contra heL
    exact hno (fun t ht => hc.involution_mem_component_sup hL heL (quasi_orderOf_mk u ht))
      (fun x hx => hc.mul_self_ne_of_mem_component_sup hL heL hx)
  obtain ⟨L, hL⟩ := hc.exists_oneComponent (three_le_twoRank_quasiQuotient hrank)
    (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hall
  obtain ⟨hZ, hvL, hcov⟩ := hL.center_card_and_cover hc (quasiBar_mul_self u)
    (zpowers_quasiBar_normal u) (canonicalBelow_quasiQuotient IH u)
  rcases hcov with hL2 | hS
  · obtain ⟨e₅⟩ :=
      CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
    let eA := hL2.some.trans e₅
    exact ⟨hu, hrank, L, hL, hZ, hvL, ⟨eA⟩, fun x hx => hL.mem_sup_centralizer_of_alternating hc
      (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hZ eA hx⟩
  · exact (hno (fun t ht => hL.mem_of_szModel hZ hS.some (quasi_orderOf_mk u ht))
      (fun x hx => hL.mul_self_ne_of_szModel hc hZ hS.some hx)).elim

theorem StarLift.exists_partC (hu : StarLift B z u) (h : Setting J Q B) (hz : FourGen Q z) :
    ∃ T : Sylow 2 (quasiNormalizer u),
      (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u) ∧
      quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) ∧ z ∈ partCSylow T ∧
      ∃ L : Subgroup (QuasiQuotient u),
        OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
        PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u ∧
        3 ≤ CFSG.Open.pRank 2 (partCSylow T) := by
  obtain ⟨T, hTB, huT, hzT⟩ := hu.exists_sylow h hz
  obtain ⟨L, hL, hZ, -, ⟨eA⟩, hα⟩ := hu.star
  have hc := hu.baseConfig h hz hu.rank
  set T' := T.mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 (quasiNormalizer u)))
  have hT' : (T' : Subgroup (QuasiQuotient u)) =
      (T : Subgroup (quasiNormalizer u)).map (quasiMk u) := Sylow.coe_mapSurjective _ _
  have hP := hL.partC hc (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hZ eA hα T'
  rw [hT'] at hP
  have heT : (⟨centralElt J, h.centralElt_mem_quasiNormalizer u⟩ : quasiNormalizer u) ∈
      (T : Subgroup (quasiNormalizer u)) := by
    rw [hu.centralElt_mk_eq h]
    exact (T : Subgroup (quasiNormalizer u)).mul_mem huT huT
  rw [← hu.quasiMk_centralElt h] at hP
  have hP' := PartC.transport (quasiMk u) (quasiNormalizer u).subtype
    (fun a ha b hb hab => quasiMk_injOn_twoGroup u T.isPGroup' ha hb hab)
    (quasiNormalizer u).subtype_injective heT huT hP h.centralElt_mem_center
  have hinf : ∀ M : Subgroup (QuasiQuotient u),
      (T : Subgroup (quasiNormalizer u)) ⊓
          (((T : Subgroup (quasiNormalizer u)).map (quasiMk u)) ⊓ M).comap (quasiMk u) =
        (T : Subgroup (quasiNormalizer u)) ⊓ M.comap (quasiMk u) := fun M => by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, Subgroup.mem_map_of_mem _ hx.1, hx.2⟩⟩
  rw [hinf, hinf] at hP'
  refine ⟨T, hTB, huT, ⟨_, hzT, rfl⟩, L, hL, hP', ?_⟩
  rw [sylow_image_two_rank_eq]
  exact hu.rank

structure MaximalStarLift (B : Subgroup J) (z u : J) : Prop extends StarLift B z u where
  maximal : ∀ v : J, StarLift B z v →
    (Nat.card (quasiNormalizer v)).factorization 2 ≤
      (Nat.card (quasiNormalizer u)).factorization 2

theorem exists_maximalStarLift (hex : ∃ u : J, StarLift B z u) :
    ∃ u : J, MaximalStarLift B z u := by
  obtain ⟨u, hu, hmax⟩ := Set.exists_max_image {v : J | StarLift B z v}
    (fun v => (Nat.card (quasiNormalizer v)).factorization 2) (Set.toFinite _) hex
  exact ⟨u, hu, fun v hv => hmax v hv⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
