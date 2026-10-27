module

public import CFSG.ClassicalInvolution.Q3.Q3T8L274B

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Layer

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T7
  CFSG.ClassicalInvolution.Q3.Disc3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T8
open scoped commutatorElement

section Good

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


theorem exactLayer3_conjSub_eq (hΩ : ConjInvariant Ω) {n : G} (hn : n ∈ cenZ x) :
    conjSub n (exactLayer3 Ω x) = exactLayer3 Ω x := by
  have hn' : n ∈ Subgroup.centralizer ({x} : Set G) := (cenZ_eq_centralizer x) ▸ hn
  have key : ∀ d ∈ Subgroup.centralizer ({x} : Set G),
      conjSub d (exactLayer3 Ω x) ≤ exactLayer3 Ω x := by
    intro d hd
    rw [exactLayer3_eq_iSup, conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (conjSub d L) (conjSub_mem_exactFamily3 hΩ hd hL) le_rfl
  refine le_antisymm (key n hn') ?_
  have h := conjSub_mono (n := n)
    (key n⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hn'))
  rwa [conjSub_conjSub_inv] at h

theorem mem_normalizer_oddCoreOf_exactLayer3 (hΩ : ConjInvariant Ω) {n : G} (hn : n ∈ cenZ x) :
    n ∈ Subgroup.normalizer (oddCoreOf (exactLayer3 Ω x) : Set G) :=
  mem_normalizer_oddCore_of_mem_normalizer
    (mem_normalizer_iff_conjSub_eq.mpr (exactLayer3_conjSub_eq hΩ hn))

theorem oddCoreOf_exactLayer3_le_of_good (hΩ : ConjInvariant Ω) {E J : Subgroup G}
    (hEcomm : IsMulCommutative E) (hEexp : ∀ w ∈ E, w ^ 2 = 1) (hE4 : 4 ≤ Nat.card E)
    (hEx : E ≤ cenZ x)
    (hgood : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ J) :
    oddCoreOf (exactLayer3 Ω x) ≤ J :=
  CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le hEcomm hEexp hE4
    (fun _ hw => mem_normalizer_oddCoreOf_exactLayer3 hΩ (hEx hw)) (odd_natCard_oddCoreOf _)
    (fun e he he1 => inf_le_right.trans (hgood e he he1))

theorem oddCoreOf_exactLayer3_le_of_good_pair (hΩ : ConjInvariant Ω) {u v : G} {J : Subgroup G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hne : u ≠ v) (hux : u ∈ cenZ x) (hvx : v ∈ cenZ x)
    (hgu : Subgroup.centralizer ({u} : Set G) ≤ J) (hgv : Subgroup.centralizer ({v} : Set G) ≤ J)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ J) :
    oddCoreOf (exactLayer3 Ω x) ≤ J := by
  refine oddCoreOf_exactLayer3_le_of_good hΩ (E := Subgroup.closure ({u, v} : Set G))
    ⟨⟨fun a b => Subtype.ext (closure_pair_mul_comm huv a.2 b.2)⟩⟩
    (fun w hw => closure_pair_sq hu hv huv hw)
    (four_le_natCard_closure_pair hu hu1 hv1 hne) ?_ ?_
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hux
    · exact hvx
  · intro e he he1
    rcases mem_closure_pair_involutions hu hv huv he with h | h | h | h
    · exact absurd h he1
    · rw [h]
      exact hgu
    · rw [h]
      exact hgv
    · rw [h]
      exact hguv

end Good

section Star

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


theorem layer_omegaStarNbr3 (L : LayerHyp Ω x) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω x)
    (hJ : J ∈ tqMembers3 Ω x) (m : ↥(exactLayer3 Ω x))
    (h : (exactCore3 x J).subgroupOf (exactLayer3 Ω x) ∈
      omegaStarNbr (exactPair3 Ω x) (conjSub m ((exactCore3 x K).subgroupOf (exactLayer3 Ω x)))) :
    J ∈ omegaStarNbr Ω (conjSub (m : G) K) := by
  obtain ⟨-, hne, U', hU'S, hU'J, hU'N⟩ := h
  obtain ⟨R', hR'S, -, -, -, hU'R', hcyc, hcard, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet L.pair hU'S
  have hmc : (m : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x m.2
  have hmc' : (m : G) ∈ Subgroup.centralizer ({x} : Set G) := (cenZ_eq_centralizer x) ▸ hmc
  have hKm : conjSub (m : G) K ∈ tqMembers3 Ω x :=
    conjSub_mem_tqMembers3 L.gen.conjInvariant hmc' hK
  have hLm : exactCore3 x (conjSub (m : G) K) = conjSub (m : G) (exactCore3 x K) :=
    (exactCore3_conj_cen hmc K).symm
  have hYJ : exactCore3 x J ≤ exactLayer3 Ω x := exactCore3_le_exactLayer3 hJ
  have hYKm : exactCore3 x (conjSub (m : G) K) ≤ exactLayer3 Ω x := exactCore3_le_exactLayer3 hKm
  have hUJ : U'.map (exactLayer3 Ω x).subtype ≤ exactCore3 x J := by
    have := Subgroup.map_mono (f := (exactLayer3 Ω x).subtype) hU'J
    rwa [Subgroup.map_subgroupOf_eq_of_le hYJ] at this
  obtain ⟨J₀, ⟨⟨J₀', hJ₀', rfl⟩, -⟩, hJ₀Y, hRJ₀⟩ := exists_isSylow2In_of_mem_RSet_restrict hR'S
  have hRK₀ : IsSylow2In (R'.map (exactLayer3 Ω x).subtype) J₀' :=
    ((isSylow2In_exactCore3_iff L.hc2 hJ₀'.2).mp hRJ₀).1
  have hUR : U'.map (exactLayer3 Ω x).subtype ≤ R'.map (exactLayer3 Ω x).subtype :=
    Subgroup.map_mono hU'R'
  have hUcyc : IsCyclic ↥(U'.map (exactLayer3 Ω x).subtype) :=
    isCyclic_of_surjective
      (U'.equivMapOfInjective (exactLayer3 Ω x).subtype
        (exactLayer3 Ω x).subtype_injective).toMonoidHom
      (U'.equivMapOfInjective (exactLayer3 Ω x).subtype
        (exactLayer3 Ω x).subtype_injective).surjective
  have hUcard : Nat.card (R'.map (exactLayer3 Ω x).subtype) =
      2 * Nat.card (U'.map (exactLayer3 Ω x).subtype) := by
    rw [Subgroup.card_map_of_injective (exactLayer3 Ω x).subtype_injective,
      Subgroup.card_map_of_injective (exactLayer3 Ω x).subtype_injective]
    exact hcard
  have hU4 : 4 ≤ Nat.card (U'.map (exactLayer3 Ω x).subtype) := by
    rw [Subgroup.card_map_of_injective (exactLayer3 Ω x).subtype_injective]
    exact h4
  have hUS : U'.map (exactLayer3 Ω x).subtype ∈ USet Ω :=
    mem_USet_of_natCard hJ₀'.1 hRK₀ hUR hUcyc hUcard
  have hU2 : IsPGroup 2 (U'.map (exactLayer3 Ω x).subtype) := hRK₀.2.1.to_le hUR
  have hJJ : J₀' = J := Sec6Gen.eq_of_le_of_le L.gen hJ₀'.1 hJ.1 hU2 hU4
    (hUR.trans hRK₀.1) (hUJ.trans (exactCore3_le_left x J))
  subst hJJ
  have hKJ : conjSub (m : G) K ≠ J₀' := by
    intro hKJ
    apply hne
    rw [← hKJ, hLm, conjSub_subgroupOf]
  obtain ⟨z', hz'⟩ := Sec6Gen.exists_uniqueInvolution L.gen hKm.1
  have hz'L : IsUniqueInvolution (exactCore3 x (conjSub (m : G) K)) z' :=
    isUniqueInvolution_exactCore3 hKm.2.1 hz'
  have hYm : conjSub (m : G) (exactCore3 x K) ≤ exactLayer3 Ω x := by
    rw [← hLm]
    exact hYKm
  have hUN : U'.map (exactLayer3 Ω x).subtype ≤
      Subgroup.normalizer ((exactCore3 x (conjSub (m : G) K) : Subgroup G) : Set G) := by
    rintro _ ⟨u', hu', rfl⟩
    have h1 := hU'N hu'
    rw [conjSub_subgroupOf] at h1
    show (u' : G) ∈ _
    rw [hLm]
    exact (mem_normalizer_subgroupOf_iff hYm).mpr h1
  have hAc : U'.map (exactLayer3 Ω x).subtype ≤ Subgroup.centralizer ({z'} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_conjSub_eq hz' (exactCore3_le_left x (conjSub (m : G) K)) hz'L.mem
      (mem_normalizer_iff_conjSub_eq.mp (hUN hu))
    calc u * z' = (u * z' * u⁻¹) * u := by group
      _ = z' * u := by rw [this]
  have hUNK : U'.map (exactLayer3 Ω x).subtype ≤
      Subgroup.normalizer (conjSub (m : G) K : Set G) :=
    Sec6Gen.le_normalizer_of_le_centralizer L.gen hKm.1 hJ₀'.1 hKJ hz' (hUR.trans hRK₀.1) hU2
      (by omega) hAc
  exact ⟨hJ₀'.1, fun h => hKJ h.symm, _, hUS, hUR.trans hRK₀.1, hUNK⟩

theorem exists_oddCore_conj_omegaStarNbr3 (L : LayerHyp Ω x) {K J : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hJ : J ∈ tqMembers3 Ω x)
    (h : layerImg3 Ω x J ∈ omegaStarNbr (layerFam3 Ω x) (layerImg3 Ω x K)) :
    ∃ n ∈ oddCoreOf (exactLayer3 Ω x), J ∈ omegaStarNbr Ω (conjSub n K) := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  obtain ⟨m, hmN, hm⟩ := exists_conj_omegaStarNbr3 L.pair L.quot hodd
    (subgroupOf_mem_exactPair3 hK) (subgroupOf_mem_exactPair3 hJ) h
  exact ⟨(m : G), ⟨m, hmN, rfl⟩, layer_omegaStarNbr3 L hK hJ m hm⟩

theorem exists_oddCore_conj_mem_dstarComp3 (L : LayerHyp Ω x) {K : Subgroup G}
    (hK : K ∈ tqMembers3 Ω x) (hconn : T3.DStarConnected (layerFam3 Ω x)) {M : Subgroup G}
    (hM : M ∈ tqMembers3 Ω x) :
    ∃ ν ∈ oddCoreOf (exactLayer3 Ω x), conjSub ν M ∈ dstarComp Ω K := by
  have key : ∀ U : Subgroup (layerQuot3 Ω x),
      Relation.ReflTransGen (dstarAdj (layerFam3 Ω x)) (layerImg3 Ω x K) U →
      U ∈ layerFam3 Ω x ∧ ∀ M' : Subgroup G, M' ∈ tqMembers3 Ω x → layerImg3 Ω x M' = U →
        ∃ ν ∈ oddCoreOf (exactLayer3 Ω x), conjSub ν M' ∈ dstarComp Ω K := by
    intro U hU
    induction hU with
    | refl =>
      refine ⟨layerImg3_mem hK, fun M' hM' h => ?_⟩
      obtain ⟨n, hn, hnM⟩ := exists_oddCore_conj_of_layerImg3_eq L hK hM' h.symm
      refine ⟨n⁻¹, (oddCoreOf _).inv_mem hn, ?_⟩
      rw [← hnM, conjSub_inv_conjSub]
      exact Relation.ReflTransGen.refl
    | @tail b c hab hbc ih =>
      obtain ⟨hbΦ, hPb⟩ := ih
      obtain ⟨hcΦ, hadj⟩ := hbc
      refine ⟨hcΦ, fun M' hM' hMc => ?_⟩
      obtain ⟨_, ⟨L₀, ⟨⟨M₁, hM₁, rfl⟩, -⟩, hLY, rfl⟩, hb⟩ := hbΦ
      have hb' : layerImg3 Ω x M₁ = b := hb
      obtain ⟨ν₁, hν₁, hM₂⟩ := hPb M₁ hM₁ hb'
      have hν₁c : ν₁ ∈ cenZ x := exactLayer3_le_cenZ Ω x (oddCoreOf_le_self _ hν₁)
      have hν₁c' : ν₁ ∈ Subgroup.centralizer ({x} : Set G) := (cenZ_eq_centralizer x) ▸ hν₁c
      have hM₂X : conjSub ν₁ M₁ ∈ tqMembers3 Ω x :=
        conjSub_mem_tqMembers3 L.gen.conjInvariant hν₁c' hM₁
      have hM₂b : layerImg3 Ω x (conjSub ν₁ M₁) = b :=
        (layerImg3_conj_of_mem_oddCore hν₁).trans hb'
      have hdc : dstarComp Ω (conjSub ν₁ M₁) = dstarComp Ω K :=
        T7A.dstarComp_eq_of_mem hK.1 hM₂
      rcases hadj with hc1 | hc2
      · rw [← hM₂b, ← hMc] at hc1
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaStarNbr3 L hM₂X hM' hc1
        refine ⟨m⁻¹, (oddCoreOf _).inv_mem hm, ?_⟩
        have h1 := omegaStarNbr_conj L.gen.conjInvariant hmn m⁻¹
        rw [conjSub_inv_conjSub] at h1
        have h2 : conjSub m⁻¹ M' ∈ dstarComp Ω (conjSub ν₁ M₁) :=
          Relation.ReflTransGen.single ⟨L.gen.conjInvariant m⁻¹ M' hM'.1, Or.inl h1⟩
        rwa [hdc] at h2
      · rw [← hM₂b, ← hMc] at hc2
        obtain ⟨m, hm, hmn⟩ := exists_oddCore_conj_omegaStarNbr3 L hM' hM₂X hc2
        refine ⟨m, hm, ?_⟩
        exact Relation.ReflTransGen.tail hM₂
          ⟨L.gen.conjInvariant m M' hM'.1, Or.inr hmn⟩
  exact (key _ (hconn _ (layerImg3_mem hK) _ (layerImg3_mem hM))).2 M hM rfl

theorem exactLayer3_le_sigmaNorm_of_lift (L : LayerHyp Ω x) {K₀ : Subgroup G}
    (hK : K₀ ∈ tqMembers3 Ω x) (hcomp : dComp Ω K₀ = dstarComp Ω K₀)
    (hO : oddCoreOf (exactLayer3 Ω x) ≤ sigmaNorm Ω K₀)
    (hconn : T3.DStarConnected (layerFam3 Ω x)) : exactLayer3 Ω x ≤ sigmaNorm Ω K₀ := by
  rw [exactLayer3_eq_iSup]
  refine iSup₂_le fun L₁ hL₁ => ?_
  obtain ⟨K', hK', rfl⟩ := hL₁
  obtain ⟨ν, hν, hνK⟩ := exists_oddCore_conj_mem_dstarComp3 L hK hconn hK'
  rw [← hcomp] at hνK
  have hle : conjSub ν K' ≤ sigmaNorm Ω K₀ :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem L.gen.conjInvariant hK.1 hνK)
  have hνN : ν ∈ sigmaNorm Ω K₀ := hO hν
  intro y hy
  have hyK : y ∈ K' := exactCore3_le_left x K' hy
  have h1 : ν * y * ν⁻¹ ∈ sigmaNorm Ω K₀ :=
    hle (mem_conjSub_iff.mpr (by simpa [mul_assoc] using hyK))
  have h2 := (sigmaNorm Ω K₀).mul_mem ((sigmaNorm Ω K₀).mul_mem
    ((sigmaNorm Ω K₀).inv_mem hνN) h1) hνN
  simpa [mul_assoc] using h2

end Star

section Dichotomy

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}


theorem layer_dichotomy3 {K₀ : Subgroup G} (hs : AscStand3 Ω K₀) (L : LayerHyp Ω x)
    (hnc : ¬ ({x} : Set G) ⊆ Subgroup.center G) {K J : Subgroup G} (hK : K ∈ tqMembers3 Ω x)
    (hJ : J ∈ tqMembers3 Ω x) :
    (∃ y ∈ exactLayer3 Ω x, J = conjSub y K) ∨
      (∃ m ∈ exactLayer3 Ω x, J ∈ omegaNbr Ω (conjSub m K)) := by
  have hodd := odd_natCard_oddCore_exactLayer3 (Ω := Ω) (x := x)
  have hK'Λ := subgroupOf_mem_exactPair3 hK
  have hJ'Λ := subgroupOf_mem_exactPair3 hJ
  have hne0 : (tqMembers3 Ω x).Nonempty := ⟨K, hK⟩
  by_cases hconj : ∃ g : layerQuot3 Ω x, conjSub g (layerImg3 Ω x K) = layerImg3 Ω x J
  · obtain ⟨g, hg⟩ := hconj
    obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective g
    left
    have h1 : (conjSub y₀ ((exactCore3 x K).subgroupOf (exactLayer3 Ω x))).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x))) =
        ((exactCore3 x J).subgroupOf (exactLayer3 Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer3 Ω x))) := by
      rw [AscQuot.map_conjSub]
      exact hg
    obtain ⟨m, hm, hJ'⟩ := T3CII.exists_conj_of_map_eq_gen L.pair hodd
      (L.pair.conjInvariant y₀ _ hK'Λ) hJ'Λ h1
    have hy : ((m * y₀ : ↥(exactLayer3 Ω x)) : G) ∈ exactLayer3 Ω x := (m * y₀).2
    have hyc : ((m * y₀ : ↥(exactLayer3 Ω x)) : G) ∈ cenZ x := exactLayer3_le_cenZ Ω x hy
    have hyc' : ((m * y₀ : ↥(exactLayer3 Ω x)) : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (cenZ_eq_centralizer x) ▸ hyc
    refine ⟨((m * y₀ : ↥(exactLayer3 Ω x)) : G), hy, ?_⟩
    rw [← conjSub_mul, conjSub_subgroupOf] at hJ'
    have h2 := Subgroup.subgroupOf_inj.mp hJ'
    rw [inf_eq_left.mpr (exactCore3_le_exactLayer3 hJ)] at h2
    have hKy : conjSub ((m * y₀ : ↥(exactLayer3 Ω x)) : G) K ∈ tqMembers3 Ω x :=
      conjSub_mem_tqMembers3 L.gen.conjInvariant hyc' hK
    have h3 : conjSub ((m * y₀ : ↥(exactLayer3 Ω x)) : G) (exactCore3 x K) ≤
        exactLayer3 Ω x := by
      rw [exactCore3_conj_cen hyc K]
      exact exactCore3_le_exactLayer3 hKy
    rw [inf_eq_left.mpr h3] at h2
    exact (eq_of_exactCore3_eq L hKy hJ ((exactCore3_conj_cen hyc K).symm.trans h2.symm)).symm
  · right
    have hA := Q3T7.aEmpty_layerFam3 hs L.hc2 hne0
    have hcomm := Q3T7.layer_commutes_of_not_conj hs L.hc2 hnc hne0 hA (layerImg3_mem hK)
      (layerImg3_mem hJ) hconj
    have hne : layerImg3 Ω x K ≠ layerImg3 Ω x J := by
      intro h
      exact hconj ⟨1, by rw [conjSub_one]; exact h⟩
    have hadj := omegaNbr_of_commutes (Φ := layerFam3 Ω x) (layerImg3_mem hJ) hne hcomm
    obtain ⟨m, -, hm⟩ := C25J.exists_conj_omegaNbr_gen L.pair L.quot hodd hK'Λ hJ'Λ hadj
    exact ⟨(m : G), m.2, layer_omegaNbr3 L hK hJ m hm⟩

end Dichotomy

section Zt

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem xMem_zt3 (hs : Std8 Ω K J S R T W z t) : XMem Ω (z * t) K := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  refine ⟨hK, ?_, R, Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hs.hR.1 hs.hR.2.1, fun r hr => ?_⟩
  · have hc := CFSG.ClassicalInvolution.Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
    have haz : z * t ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc z * t * z = z * (t * z) := by group
        _ = z * (z * t) := by rw [← hc]
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK hs.noTwins hs.hz haz
  · exact Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_mul hs hr)

theorem zt_not_central3 [IsSimpleGroup G] (hs : Std8 Ω K J S R T W z t) :
    ¬ ({z * t} : Set G) ⊆ Subgroup.center G :=
  not_central_of_ne_one3 hs.stand.modU hs.stand.mem
    (mul_ne_one_of_ne hs.hz.sq (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht))

theorem centralizer_le_sigmaNorm_of_exactLayer3_le [IsSimpleGroup G]
    (hs : Std8 Ω K J S R T W z t) (hY : exactLayer3 Ω (z * t) ≤ sigmaNorm Ω K) :
    Subgroup.centralizer ({z * t} : Set G) ≤ sigmaNorm Ω K := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hs3 : AscStand3 Ω K := hs.stand.toStand3
  have ha2 : z * t * (z * t) = 1 :=
    CFSG.ClassicalInvolution.Q3.Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKx : XMem Ω (z * t) K := xMem_zt3 hs
  have hKt : K ∈ tqMembers3 Ω (z * t) := hKx.mem_tqMembers3 hΩ ha2
  have hL : LayerHyp Ω (z * t) := LayerHyp.of_stand3 hs3 ha2 ⟨K, hKt⟩
  have hnc := zt_not_central3 hs
  intro c hc
  have hKc : conjSub c K ∈ tqMembers3 Ω (z * t) :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hc hKt
  rw [mem_sigmaNorm_iff hΩ.conjInvariant hK]
  rcases layer_dichotomy3 hs3 hL hnc hKt hKc with ⟨y, hy, hyc⟩ | ⟨m, hm, hmc⟩
  · rw [hyc]
    exact (mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hy)
  · have hmK := (mem_sigmaNorm_iff hΩ.conjInvariant hK).1 (hY hm)
    exact hmK.trans (Relation.ReflTransGen.single ⟨hKc.1, Or.inl hmc⟩)

end Zt

end CFSG.ClassicalInvolution.Q3.Q3T8.Layer
