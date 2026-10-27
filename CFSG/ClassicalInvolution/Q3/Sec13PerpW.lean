module

public import CFSG.ClassicalInvolution.Q3.Sec13PerpPair
import CFSG.ClassicalInvolution.Q3.TL3T38

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem perpW_mem_RSet (h : EndHyp Ω) {J : Subgroup G} (hJ : J ∈ Ω) : J ∈ RSet Ω :=
  TC.mem_RSet_of_isPGroup hJ (h.thmD.two J hJ)

theorem perpW_isSylow2In_self (h : EndHyp Ω) {K : Subgroup G} (hK : K ∈ Ω) :
    IsSylow2In K K :=
  ⟨le_rfl, h.thmD.two K hK, fun _ hVK _ hKV => le_antisymm hVK hKV⟩

theorem perpW_card_of_mem_RSet (h : EndHyp Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) :
    Nat.card R = 8 := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hJR : J = R := hRJ.2.2 J le_rfl (h.thmD.two J hJ) hRJ.1
  rw [← hJR]
  exact h.card_eq_eight hJ

theorem perpW_usetOf {η : Set (Subgroup G)} {U : Subgroup G} (hη : η ∈ etaG Ω) (hU : U ∈ η) :
    U ∈ USet Ω := by
  obtain ⟨S', hS', -⟩ := hη
  exact (hS'.1 hU).1

theorem perpW_frontier {K J : Subgroup G} (hJ : J ∈ dstarComp Ω K) (hJD : J ∉ dComp Ω K) :
    ∃ A B : Subgroup G, A ∈ dComp Ω K ∧ dstarAdj Ω A B ∧ B ∉ dComp Ω K := by
  have key : ∀ Y, Relation.ReflTransGen (dstarAdj Ω) K Y →
      Y ∈ dComp Ω K ∨ ∃ A B : Subgroup G, A ∈ dComp Ω K ∧ dstarAdj Ω A B ∧ B ∉ dComp Ω K := by
    intro Y hY
    induction hY with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rcases ih with hb | ⟨A, B, hA, hAB, hB⟩
      · by_cases hc : c ∈ dComp Ω K
        · exact Or.inl hc
        · exact Or.inr ⟨b, c, hb, hbc, hc⟩
      · exact Or.inr ⟨A, B, hA, hAB, hB⟩
  rcases key J hJ with h1 | h1
  · exact absurd h1 hJD
  · exact h1

theorem perpW_mem_of_mem_dComp {K A : Subgroup G} (hK : K ∈ Ω) (hA : A ∈ dComp Ω K) :
    A ∈ Ω := by
  have h : Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K A :=
    hA
  induction h with
  | refl => exact hK
  | tail _ hbc _ => exact hbc.1

theorem perpW_dComp_step {K A B : Subgroup G} (hA : A ∈ dComp Ω K) (hB : B ∈ Ω)
    (hAB : Disconnected.dAdj Ω A B) : B ∈ dComp Ω K :=
  Relation.ReflTransGen.tail hA ⟨hB, hAB⟩

theorem perpW_exists_nc_edge (h : EndHyp Ω) :
    ∃ K ∈ Ω, ∃ J ∈ Ω, J ∈ omegaStarNbr Ω K ∧ J ∉ omegaNbr Ω K := by
  obtain ⟨K, hK, J, hJ, hJD⟩ : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dComp Ω K := by
    by_contra hcon
    push Not at hcon
    exact h.disc fun K hK J hJ => hcon K hK J hJ
  obtain ⟨A, B, hA, ⟨hBΩ, hBA⟩, hB⟩ := perpW_frontier (h.star K hK J hJ) hJD
  have hAΩ := perpW_mem_of_mem_dComp hK hA
  rcases hBA with hBA | hAB
  · refine ⟨A, hAΩ, B, hBΩ, hBA, fun hBn => hB ?_⟩
    exact perpW_dComp_step hA hBΩ (Or.inl hBn)
  · refine ⟨B, hBΩ, A, hAΩ, hAB, fun hAn => hB ?_⟩
    exact perpW_dComp_step hA hBΩ (Or.inr hAn)

theorem perpW_exists_sylow_edge (h : EndHyp Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) :
    ∃ S₀ : Sylow 2 G, 2 < Nat.card ↥(J ⊓ (S₀ : Subgroup G)) ∧ J ⊓ (S₀ : Subgroup G) ∉ RSet Ω := by
  have hJΩ : J ∈ Ω := hJ.1
  have h4 := (pair_structure h hK hJ hJn).2.2.2.1
  have hV2 : IsPGroup 2 ↥(J ⊓ Subgroup.normalizer (K : Set G)) :=
    (h.thmD.two J hJΩ).to_le inf_le_left
  have hsup : IsPGroup 2 ↥((J ⊓ Subgroup.normalizer (K : Set G)) ⊔ K) :=
    hV2.to_sup_of_normal_right' (h.thmD.two K hK) inf_le_right
  obtain ⟨S₀, hS₀⟩ := hsup.exists_le_sylow
  have hKS : K ≤ (S₀ : Subgroup G) := le_sup_right.trans hS₀
  have hVS : J ⊓ Subgroup.normalizer (K : Set G) ≤ (S₀ : Subgroup G) := le_sup_left.trans hS₀
  have hJS : ¬ J ≤ (S₀ : Subgroup G) := by
    intro hJS
    have hne : K ≠ J := fun e => hJ.2.1 e.symm
    have hc := Q3CP.l67Gen G Ω h.thmD.hyp S₀ K (perpW_mem_RSet h hK) J
      (perpW_mem_RSet h hJΩ) hKS hJS hne
    have hJN : J ≤ Subgroup.normalizer (K : Set G) :=
      Asc77.AscL62.le_normalizer_of_commutes hc.symm
    exact hJn ((TC.mem_omegaNbr_iff h.thmD.hyp h.thmD.two).mpr ⟨hJΩ, hJ.2.1, hJN⟩)
  refine ⟨S₀, ?_, fun hmem => ?_⟩
  · have hle : J ⊓ Subgroup.normalizer (K : Set G) ≤ J ⊓ (S₀ : Subgroup G) :=
      le_inf inf_le_left hVS
    have := Subgroup.card_le_of_le hle
    omega
  · have h8 := perpW_card_of_mem_RSet h hmem
    have hJ8 : Nat.card J = 8 := h.card_eq_eight hJΩ
    have heq : J ⊓ (S₀ : Subgroup G) = J :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hJS ((le_of_eq heq.symm).trans inf_le_right)

theorem perpW_not_halt (h : EndHyp Ω) (S : Sylow 2 G) :
    ¬ (∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) → K ⊓ (S : Subgroup G) ∈ RSet Ω) := by
  intro hall
  obtain ⟨K, hK, J, hJΩ, hJ, hJn⟩ := perpW_exists_nc_edge h
  obtain ⟨S₀, hcard, hnot⟩ := perpW_exists_sylow_edge h hK hJ hJn
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S
  have hJg : conjSub g J ∈ Ω := h.thmD.hyp.conjInvariant g J hJΩ
  have hinf : conjSub g J ⊓ (S : Subgroup G) = conjSub g (J ⊓ (S₀ : Subgroup G)) := by
    rw [← hg]
    ext x
    simp only [Subgroup.mem_inf, mem_conjSub_iff]
  have hcardg : 2 < Nat.card ↥(conjSub g J ⊓ (S : Subgroup G)) := by
    rw [hinf, natCard_conjSub]
    exact hcard
  have hmem := hall (conjSub g J) hJg hcardg
  rw [hinf] at hmem
  apply hnot
  have := Q3CL.Thompson.conjSub_mem_RSet h.thmD.hyp hmem g⁻¹
  rwa [conjSub_inv_conjSub] at this

theorem perpW_inv_of_sylow (h : EndHyp Ω) {S : Sylow 2 G} {η : Set (Subgroup G)}
    (hη : η ∈ etaG Ω) (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) :
    ∀ m ∈ ⨆ U ∈ {U : Subgroup G | (∃ η' ∈ etaG Ω, U ∈ η') ∧ U ≤ (S : Subgroup G)}, U,
      ∀ V ∈ η, conjSub m V ∈ η := by
  have h10 := Sec6Gen.l6_10Gen G Ω h.thmD.hyp S η hη hηS
  set T : Set (Subgroup G) := {U : Subgroup G | (∃ η' ∈ etaG Ω, U ∈ η') ∧
    U ≤ (S : Subgroup G)} with hT
  have hgen : ∀ U : Subgroup G, U ∈ T → ∀ u ∈ U, ∀ V ∈ η, conjSub u V ∈ η := by
    rintro U ⟨⟨η', hη', hUη'⟩, hUS⟩ u hu V hV
    exact (h10).2 U (perpW_usetOf hη' hUη') hUS u hu V hV
  intro m hm
  have key : (⨆ U : T, (U : Subgroup G)) = ⨆ U ∈ T, U := iSup_subtype'' T (fun U => U)
  have hm' : m ∈ ⨆ U : T, (U : Subgroup G) := by
    rw [key]
    exact hm
  exact Subgroup.iSup_induction (fun U : T => (U : Subgroup G))
    (C := fun x => ∀ V ∈ η, conjSub x V ∈ η) hm'
    (fun U x hx V hV => hgen U.1 U.2 x hx V hV)
    (fun V hV => by rw [conjSub_one]; exact hV)
    (fun x y hx hy V hV => by rw [conjSub_mul]; exact hx _ (hy V hV))

theorem perpW_sylow_spec (h : EndHyp Ω) (S : Sylow 2 G) :
    ∃ η₀ ∈ etaG Ω, (∀ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) → η = η₀) ∧
      ∀ g : G, (∀ U ∈ η₀, conjSub g U ≤ (S : Subgroup G)) → ∀ U ∈ η₀, conjSub g U ∈ η₀ := by
  have h612 := Q3.Q3T8.Disconnected.AschTight.Sec7.l6_12_mod G Ω h.partIHyp h.thmD.trans S
  dsimp only at h612
  rcases h612 with ⟨η₀, hη₀, -, huniq, hwc⟩ | halt
  · exact ⟨η₀, hη₀, fun η hη hηS => huniq η hη (perpW_inv_of_sylow h hη hηS), hwc⟩
  · exact absurd halt (perpW_not_halt h S)

theorem perpW_eq_of_sylow (h : EndHyp Ω) (S : Sylow 2 G) {η₁ η₂ : Set (Subgroup G)}
    (h₁ : η₁ ∈ etaG Ω) (h₂ : η₂ ∈ etaG Ω) (hs₁ : ∀ V ∈ η₁, V ≤ (S : Subgroup G))
    (hs₂ : ∀ V ∈ η₂, V ≤ (S : Subgroup G)) : η₁ = η₂ := by
  obtain ⟨η₀, -, huniq, -⟩ := perpW_sylow_spec h S
  rw [huniq η₁ h₁ hs₁, huniq η₂ h₂ hs₂]

theorem perpW_conjSub_iSup (g : G) (η : Set (Subgroup G)) :
    conjSub g (⨆ U ∈ η, U) = ⨆ U ∈ η, conjSub g U := by
  simp only [conjSub, Subgroup.map_iSup]

theorem wSet_conj (h : EndHyp Ω) {W W' : Subgroup G} (hW : W ∈ WSet Ω) (hW' : W' ∈ WSet Ω) :
    ∃ g : G, conjSub g W = W' := by
  obtain ⟨η, hη, rfl⟩ := hW
  obtain ⟨η', hη', rfl⟩ := hW'
  have hη₁ := hη
  have hη₂ := hη'
  obtain ⟨S₁, hS₁, -⟩ := hη₁
  obtain ⟨S₂, hS₂, -⟩ := hη₂
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S₂
  have hsub : ∀ V ∈ conjSub g '' η, V ≤ (S₂ : Subgroup G) := by
    rintro V ⟨U, hU, rfl⟩
    rw [← hg]
    exact conjSub_mono ((hS₁.1 hU).2)
  have hsub' : ∀ V ∈ η', V ≤ (S₂ : Subgroup G) := fun V hV => (hS₂.1 hV).2
  have hEq : conjSub g '' η = η' :=
    perpW_eq_of_sylow h S₂ (Sec7.etaG_conj h.thmD.hyp.conjInvariant hη g) hη' hsub hsub'
  refine ⟨g, ?_⟩
  rw [← hEq, iSup_image, perpW_conjSub_iSup]

theorem wSet_weaklyClosed (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω) (S : Sylow 2 G)
    (hWS : W ≤ (S : Subgroup G)) (g : G) (hg : conjSub g W ≤ (S : Subgroup G)) :
    conjSub g W = W := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans hWS
  obtain ⟨η₀, -, huniq, hwc⟩ := perpW_sylow_spec h S
  have hη0 : η = η₀ := huniq η hη hηS
  subst hη0
  have hall : ∀ U ∈ η, conjSub g U ∈ η := hwc g fun U hU =>
    (conjSub_mono (le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU)).trans hg
  exact Sec7.conjSub_iSup_eq_of_forall_mem hall

theorem perpW_comm_of_index_two {R C : Subgroup G} {r : G}
    (hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (hr : ∀ c ∈ C, r * c = c * r)
    (hdec : ∀ x ∈ R, x ∈ C ∨ ∃ c ∈ C, x = r * c) : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
  intro x hx y hy
  rcases hdec x hx with hxC | ⟨c, hc, rfl⟩ <;> rcases hdec y hy with hyC | ⟨c', hc', rfl⟩
  · exact hC x hxC y hyC
  · exact Commute.mul_right (hr x hxC).symm (hC x hxC c' hc')
  · exact Commute.mul_left (hr y hyC) (hC c hc y hyC)
  · exact Commute.mul_right (Commute.mul_left (Commute.refl r) (hr c hc).symm)
      (Commute.mul_left (hr c' hc') (hC c hc c' hc'))

theorem dSet_bar_injective (h : EndHyp Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {R R' : Subgroup G} (hR : R ∈ DSet Ω W) (hR' : R' ∈ DSet Ω W)
    (heq : R ⊔ W ⊔ OCW W = R' ⊔ W ⊔ OCW W) : R = R' := by
  by_contra hne
  have hΩ : HypOmegaGen Ω := h.thmD.hyp
  have hRΩ : R ∈ Ω := (h.mem_dSet_iff.mp hR).1
  have hR'Ω : R' ∈ Ω := (h.mem_dSet_iff.mp hR').1
  have hCW : W ⊔ OCW W ≤ Subgroup.centralizer (W : Set G) :=
    sup_le (fun w hw => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Q3CL.Thompson.commutes_of_mem_WSet hΩ hW x hx w hw)
      (Asc77.Thompson.OCW_le_centralizer W)
  have hcent : ∀ y ∈ W ⊔ OCW W, ∀ w ∈ W, w * y = y * w := fun y hy w hw =>
    Subgroup.mem_centralizer_iff.mp (hCW hy) w hw
  obtain ⟨r, hr, hrW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR
  obtain ⟨t, ht, htW⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΩ hW hR'
  have hR'le : R' ≤ R ⊔ W ⊔ OCW W := by
    rw [heq]
    exact le_sup_left.trans le_sup_left
  have hpi : Asc77.Thompson.piG W t = Asc77.Thompson.piG W r :=
    Q3CL.Thompson.piG_eq_of_le_sup hΩ hW hR hR' hR'le hr ht hrW htW
  have hy0 : r⁻¹ * t ∈ W ⊔ OCW W :=
    (CFSG.ClassicalInvolution.Asc77.Thompson.piG_eq_iff (hR.2 hr) (hR'.2 ht)).mp hpi.symm
  obtain ⟨y, rfl⟩ : ∃ y : G, t = r * y := ⟨r⁻¹ * t, by group⟩
  have hy : y ∈ W ⊔ OCW W := by simpa using hy0
  have hrN : ∀ w ∈ W, r⁻¹ * w * r ∈ W := by
    intro w hw
    have hconj : r * (r⁻¹ * w * r) * r⁻¹ = w := by group
    have := (Subgroup.mem_normalizer_iff.mp (hR.2 hr) (r⁻¹ * w * r)).mpr (by rw [hconj]; exact hw)
    simpa using this
  have K1 : ∀ w ∈ W, (r * y)⁻¹ * w * (r * y) = r⁻¹ * w * r := by
    intro w hw
    have hc := hcent y hy _ (hrN w hw)
    calc (r * y)⁻¹ * w * (r * y) = y⁻¹ * ((r⁻¹ * w * r) * y) := by group
      _ = y⁻¹ * (y * (r⁻¹ * w * r)) := by rw [hc]
      _ = r⁻¹ * w * r := by group
  have K2 : ∀ z ∈ W, (r * y) * z * (r * y)⁻¹ = r * z * r⁻¹ := by
    intro z hz
    have hyz : y * z * y⁻¹ = z := by
      rw [← hcent y hy z hz]
      group
    calc (r * y) * z * (r * y)⁻¹ = r * (y * z * y⁻¹) * r⁻¹ := by group
      _ = r * z * r⁻¹ := by rw [hyz]
  by_cases hA : R' ∈ omegaNbr Ω R
  ·
    exfalso
    have hcm : ∀ x ∈ R, ∀ w ∈ R', x * w = w * x :=
      comm_of_mem_omegaNbr hΩ h.thmD.two hRΩ hA
    have hrc : ∀ c ∈ R ⊓ W, r * c = c * r := by
      intro c hc
      have h1 : (r * y)⁻¹ * c * (r * y) = c := by
        calc (r * y)⁻¹ * c * (r * y) = (r * y)⁻¹ * (c * (r * y)) := by group
          _ = (r * y)⁻¹ * ((r * y) * c) := by rw [hcm c hc.1 (r * y) ht]
          _ = c := by group
      rw [K1 c hc.2] at h1
      have h2 : c * r = r * c := by
        calc c * r = r * (r⁻¹ * c * r) := by group
          _ = r * c := by rw [h1]
      exact h2.symm
    have hdec : ∀ x ∈ R, x ∈ R ⊓ W ∨ ∃ c ∈ R ⊓ W, x = r * c := by
      intro x hx
      by_cases hxW : x ∈ W
      · exact Or.inl ⟨hx, hxW⟩
      · refine Or.inr ⟨r⁻¹ * x, ⟨R.mul_mem (R.inv_mem hr) hx, ?_⟩, by group⟩
        exact Q3CL.Thompson.D_inv_mul_mem hΩ hW hR hr hx hrW hxW
    have hcomm := perpW_comm_of_index_two (R := R) (C := R ⊓ W) (r := r)
      (fun x hx y hy => Q3CL.Thompson.commutes_of_mem_WSet hΩ hW x hx.2 y hy.2) hrc hdec
    obtain ⟨x, hx, w, hw, hxw⟩ :=
      IsQuatSub.exists_not_commute (Sec6Gen.isQuatSub_of_mem_RSet hΩ (perpW_mem_RSet h hRΩ))
    exact hxw (hcomm x hx w hw)
  ·
    have hsyl := perpW_isSylow2In_self h hRΩ
    have hsyl' := perpW_isSylow2In_self h hR'Ω
    have hBsd : R' ∈ omegaStarNbr Ω R :=
      (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W hΩ hW hRΩ hR'Ω hne hR hR' hsyl hsyl').1
    have h4 := (pair_structure h hRΩ hBsd hA).2.2.2.1
    have hR'8 := perpW_card_of_mem_RSet h (perpW_mem_RSet h hR'Ω)
    have hdR' := Q3CL.Thompson.D_card hΩ hW hR'
    have hcardW' : Nat.card ↥(R' ⊓ W) = 4 := by omega
    have hle : R' ⊓ W ≤ R' ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf inf_le_left
        (Q3CL.Thompson.inf_W_le_normalizer_of_ne hΩ hW hRΩ hR'Ω hne hR hR' hsyl hsyl').2
    have heq' : R' ⊓ W = R' ⊓ Subgroup.normalizer (R : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by omega)
    have htN : r * y ∉ Subgroup.normalizer (R : Set G) := by
      intro htR
      have hmem : r * y ∈ R' ⊓ Subgroup.normalizer (R : Set G) := ⟨ht, htR⟩
      rw [← heq'] at hmem
      exact htW hmem.2
    obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hRΩ
    obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hR'Ω
    have hzW : z ∈ W := by
      have hcyc := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hR hRΩ hsyl
      have hcardR : Nat.card ↥(R ⊓ W) = 4 := by
        have := Q3CL.Thompson.D_card hΩ hW hR
        have h8 := perpW_card_of_mem_RSet h (perpW_mem_RSet h hRΩ)
        omega
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R ⊓ W)) 2 (by
        rw [hcardR]; norm_num)
      have hg2 : (g : G) * g = 1 := by
        have h1 : g ^ 2 = 1 := by
          rw [← hg]
          exact pow_orderOf_eq_one g
        have h2 := congrArg Subtype.val h1
        simpa [pow_two] using h2
      have hg1 : (g : G) ≠ 1 := by
        intro e
        have hg' : g = 1 := Subtype.ext e
        rw [hg', orderOf_one] at hg
        norm_num at hg
      have hgz : (g : G) = z := (hz.unique (g : G) g.2.1 hg2).resolve_left hg1
      rw [← hgz]
      exact g.2.2
    have hrzr : r * z * r⁻¹ = z := by
      have hmem : r * z * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hz.mem) (R.inv_mem hr)
      have hsq : r * z * r⁻¹ * (r * z * r⁻¹) = 1 := by
        calc r * z * r⁻¹ * (r * z * r⁻¹) = r * (z * z) * r⁻¹ := by group
          _ = 1 := by rw [hz.sq]; group
      have hne1 : r * z * r⁻¹ ≠ 1 := by
        intro e
        apply hz.ne_one
        calc z = r⁻¹ * (r * z * r⁻¹) * r := by group
          _ = 1 := by rw [e]; group
      exact (hz.unique _ hmem hsq).resolve_left hne1
    have hzt : (r * y) * z * (r * y)⁻¹ = z := by
      rw [K2 z hzW, hrzr]
    have hcj := conj_involution_eq_mul h hRΩ hBsd hA hz hj ht htN
    have hzj : z * j = z * 1 := by
      rw [mul_one]
      exact (hzt.symm.trans hcj).symm
    exact hj.ne_one (mul_left_cancel hzj)

theorem exists_wSet_of_clique (h : EndHyp Ω) {C : Set (Subgroup G)} (hC : C ⊆ Ω)
    (hcomm : ∀ R ∈ C, ∀ T ∈ C, R ≠ T → ∀ x ∈ R, ∀ y ∈ T, x * y = y * x) :
    ∃ W ∈ WSet Ω, C ⊆ DSet Ω W := by
  have h2 : ∀ L ∈ C, IsPGroup 2 L := fun L hL => h.thmD.two L (hC hL)
  obtain ⟨S, hS⟩ := (isPGroup_pSpan_of_comm h2 hcomm).exists_le_sylow
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.thmD.hyp S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  refine ⟨⨆ U ∈ η, U, ⟨η, hη, rfl⟩, fun R hR => ⟨perpW_mem_RSet h (hC hR), ?_⟩⟩
  have hRS : R ≤ (S : Subgroup G) := (le_pSpan hR).trans hS
  intro x hx
  exact mem_normalizer_iff_conjSub_eq.mpr
    (Sec7.conjSub_iSup_eq_of_forall_mem (hinv x (hRS hx)))

end CFSG.ClassicalInvolution.Q3.Sec13
