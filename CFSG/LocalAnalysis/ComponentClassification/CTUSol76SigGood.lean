module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigMain
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigL38g

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N K K' : Subgroup G}

theorem inf_centralizer_le_oddCoreIn_of_mem_V (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) (hK : K ∈ kStarComponents N) (hK' : K' ∈ kStarComponents N)
    (hne : K ≠ K') {V B E : Subgroup G} (hV : IsKleinFour V) (hVK' : V ≤ K')
    (hBQ : B ≤ coreActionKernel K') (hBV : B ≤ centralizer (V : Set G))
    (hB : CFSG.Open.IsElemAbelian 2 B) (hB8 : Nat.card B = 8) (hE : IsKleinFour E)
    (hEB : E ≤ B) (hEK : E ≤ K) (hKW : K ≤ normalizer (wGroup B V : Set G)) {v : G}
    (hvV : v ∈ V) (hv1 : v ≠ 1) :
    oddCoreIn (normalizer (wGroup B V : Set G)) ⊓ centralizer ({v} : Set G) ≤
      oddCoreIn (centralizer ({v} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (wGroup B V : Set G)
  set Cv := centralizer ({v} : Set G)
  set X := oddCoreIn H ⊓ Cv with hX
  have hBv : B ≤ Cv := fun b hb =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hBV hb)) v hvV).symm
  have hBH : B ≤ H := fun x hx =>
    le_normalizer_wGroup (le_normalizer hx) (Subgroup.centralizer_le_normalizer _ (hBV hx))
  have hXcop : Nat.Coprime 2 (Nat.card X) :=
    Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn H)
  have hXodd : Odd (Nat.card X) := Nat.coprime_two_left.mp hXcop
  have hBX : B ≤ normalizer (X : Set G) := fun x hx =>
    mem_normalizer_inf (le_normalizer_oddCoreIn H (hBH hx)) (le_normalizer (hBv hx))
  have hLv := twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hK hK' hne hV hVK' hBQ hBV hB hB8
    hE hEB hEK hKW hvV hv1
  refine le_oddCoreIn_of_commutator_le inf_le_right hXodd ?_ fun M hM =>
    commutator_le_oddCoreIn_of_twoLayerIn_le hLv hM inf_le_left inf_le_right
  obtain ⟨Kc, hKc⟩ := exists_subgroup_commutator_mem (A := oddTwoCoreIn Cv)
    (le_normalizer_oddCoreIn Cv)
  suffices hXK : X ≤ Kc by
    rw [commutator_le]
    intro a ha x hx
    exact ((hKc x).mp (hXK hx)).2 a ha
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two B X hB (by rw [hB8]; norm_num) hBX hXcop]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨hSB, hScard⟩ := hS
  have hSK : IsKleinFour S :=
    isKleinFour_of_card_eq_four (by rw [hScard]; norm_num) fun x hx => hB.2 x (hSB hx)
  set Z := X ⊓ centralizer (S : Set G) with hZ
  have hZodd : Odd (Nat.card Z) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hXcop)
  have hNZ : Cv ⊓ centralizer (S : Set G) ≤ normalizer (Z : Set G) := by
    intro g hg
    obtain ⟨hgv, hgS⟩ := mem_inf.mp hg
    have hgH : g ∈ H := le_normalizer_wGroup_of_mem_of_mem hq hR1 hG hN hK hK' hne hV hVK' hBQ
      hBV hB hE hEB hEK hSK hSB hvV hv1 (Subgroup.centralizer_le_normalizer _ hgS) hgv
    exact mem_normalizer_inf (mem_normalizer_inf (le_normalizer_oddCoreIn H hgH)
      (le_normalizer hgv)) (le_normalizer hgS)
  have hPQ := commutator_oddTwoCoreIn_le_of_normalizes (hSB.trans hBv)
    (isPGroup_of_isKleinFour hSK) (inf_le_left.trans inf_le_right) hZodd (fun z hz => hz.2) hNZ
  intro z hz
  exact (hKc z).mpr ⟨hz.1.2, fun a ha => hPQ (commutator_mem_commutator ha hz)⟩

@[expose] def IsGoodFor (N W : Subgroup G) (x : G) : Prop :=
  x ≠ 1 ∧ ∃ K K' U A : Subgroup G, SigPair N K K' U A ∧ wGroup A U = W ∧ (x ∈ A ∨ x ∈ U)

theorem good_facts (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {W : Subgroup G}
    (hKW : ∀ K ∈ kStarComponents N, K ≤ normalizer (W : Set G)) {x : G} (hx : IsGoodFor N W x) :
    twoLayerIn (centralizer ({x} : Set G)) ≤ normalizer (W : Set G) ∧
      oddCoreIn (centralizer ({x} : Set G)) ≤ normalizer (W : Set G) ∧
      oddCoreIn (normalizer (W : Set G)) ⊓ centralizer ({x} : Set G) ≤
        oddCoreIn (centralizer ({x} : Set G)) := by
  obtain ⟨hx1, Ka, Kb, U, A, hP, hW, hxAU⟩ := hx
  obtain ⟨hKa, hKb, hne, hU, hUK, hAQ, hAU, hA, hA8, -, F, hF, hFA, hFK⟩ := hP
  subst hW
  have hAc : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm (⟨y, hy⟩ : A) ⟨z, hz⟩)
  have hKaW := hKW Ka hKa
  have hKbW := hKW Kb hKb
  rcases hxAU with hxA | hxU
  · have hAx : A ≤ centralizer ({x} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.mpr (hAc y hy x hxA)
    have hUx : U ≤ centralizer ({x} : Set G) := le_centralizer_singleton_of_mem hAU hxA
    exact ⟨twoLayerIn_centralizer_le_of_mem_B hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8 hF
        hFA hFK hKaW hKbW hxA hx1,
      oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8
        hF hFA hFK hAx hUx,
      inf_centralizer_le_oddCoreIn_of_mem_B hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8 hF hFA
        hFK hKaW hKbW hxA hx1⟩
  · have hUc := comm_of_isKleinFour hU
    have hAx : A ≤ centralizer ({x} : Set G) := fun y hy =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hAU hy)) x hxU).symm
    have hUx : U ≤ centralizer ({x} : Set G) := fun w hw =>
      mem_centralizer_singleton_iff.mpr (hUc w hw x hxU)
    exact ⟨twoLayerIn_centralizer_le_of_mem_V hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8 hF
        hFA hFK hKaW hxU hx1,
      oddCoreIn_centralizer_le_normalizer_wGroup hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8
        hF hFA hFK hAx hUx,
      inf_centralizer_le_oddCoreIn_of_mem_V hq hR1 hG hN hKa hKb hne hU hUK hAQ hAU hA hA8 hF hFA
        hFK hKaW hxU hx1⟩

theorem good_facts_of_conj {H : Subgroup G} {g x : G} (hg : g ∈ H)
    (h : twoLayerIn (centralizer ({g⁻¹ * x * g} : Set G)) ≤ H ∧
      oddCoreIn (centralizer ({g⁻¹ * x * g} : Set G)) ≤ H ∧
      oddCoreIn H ⊓ centralizer ({g⁻¹ * x * g} : Set G) ≤
        oddCoreIn (centralizer ({g⁻¹ * x * g} : Set G))) :
    twoLayerIn (centralizer ({x} : Set G)) ≤ H ∧ oddCoreIn (centralizer ({x} : Set G)) ≤ H ∧
      oddCoreIn H ⊓ centralizer ({x} : Set G) ≤ oddCoreIn (centralizer ({x} : Set G)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨twoLayerIn_centralizer_le_of_conj hg h1, oddCoreIn_centralizer_le_of_conj hg h2, ?_⟩
  set φ := MulAut.conj g
  have hc := map_centralizer_singleton φ (g⁻¹ * x * g)
  have hx : φ (g⁻¹ * x * g) = x := by rw [MulAut.conj_apply]; group
  rw [hx] at hc
  have hO := map_oddCoreIn φ (centralizer ({g⁻¹ * x * g} : Set G))
  rw [hc] at hO
  have hH : (oddCoreIn H).map φ.toMonoidHom = oddCoreIn H := by
    have h4 : H.map φ.toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp (le_normalizer hg)
    rw [map_oddCoreIn φ H, h4]
  calc oddCoreIn H ⊓ centralizer ({x} : Set G)
      = (oddCoreIn H ⊓ centralizer ({g⁻¹ * x * g} : Set G)).map φ.toMonoidHom := by
        rw [map_inf _ _ _ φ.injective, hH, hc]
    _ ≤ (oddCoreIn (centralizer ({g⁻¹ * x * g} : Set G))).map φ.toMonoidHom := map_mono h3
    _ = oddCoreIn (centralizer ({x} : Set G)) := hO

end CFSG.ComponentClassification.Sol76.Sig
