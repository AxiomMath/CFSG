module

public import CFSG.ClassicalInvolution.Asc77.AscE186QuotOdd
public import CFSG.ClassicalInvolution.Asc77.AscMuTabAbel
import CFSG.ClassicalInvolution.Asc77.AscT8S2SecEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8S2

section Lift

variable {H : Type} [Group H] [Finite H]

theorem exists_conj_le_of_le_sup_odd {N P V : Subgroup H} [N.Normal] (hN : Odd (Nat.card N))
    (hP : IsPGroup 2 P) (hV : IsPGroup 2 V) (hVle : V ≤ P ⊔ N) :
    ∃ n ∈ N, V ≤ conjSub n P := by
  have hS : IsSylow2In P (P ⊔ N) := isSylow2In_sup_of_odd hN hP
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV hVle
  obtain ⟨x, hx, hxV⟩ := Thompson.exists_conj_of_isSylow2In hS hV'
  rw [sup_comm] at hx
  obtain ⟨n, hn, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  refine ⟨n, hn, hVV'.trans ?_⟩
  rw [← hxV, conjSub_mul, conjSub_eq_self_of_mem hw]

omit [Finite H] in
theorem natCard_conjSub_eq (g : H) (K : Subgroup H) : Nat.card (conjSub g K) = Nat.card K :=
  (Nat.card_congr (Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

end Lift

section Member

variable {H : Type} [Group H] [Finite H] {p f : ℕ} [Fact p.Prime]

theorem eq_image_of_mem_USet_le_sylow (hp : p ≠ 2) {Λ : Set (Subgroup H)}
    (hΛ : HypOmegaMod p f Λ) (hΦ : HypOmegaMod p f (oddQuotientFamily Λ)) (S : Sylow 2 H)
    (J₀ : Subgroup H)
    (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀)
    {M : Subgroup (H ⧸ classicalInvolutionOddCore H)} (hM : M ∈ oddQuotientFamily Λ)
    {Ub : Subgroup (H ⧸ classicalInvolutionOddCore H)}
    (hUb : Ub ∈ USet (oddQuotientFamily Λ)) (hUbM : Ub ≤ M)
    (hUbS : Ub ≤ (S : Subgroup H).map (QuotientGroup.mk' (classicalInvolutionOddCore H))) :
    M = J₀.map (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
  set N := classicalInvolutionOddCore H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card H
  obtain ⟨J, hJ, rfl⟩ := hM
  obtain ⟨U, hU, hUJ, hUmap⟩ := exists_lift_USet hp hΦ hN hJ hUb hUbM
  have hUSN : U ≤ (S : Subgroup H) ⊔ N := by
    intro u hu
    have h1 : QuotientGroup.mk' N u ∈ (S : Subgroup H).map (QuotientGroup.mk' N) :=
      hUbS (hUmap ▸ Subgroup.mem_map_of_mem _ hu)
    have h2 : u ∈ Subgroup.comap (QuotientGroup.mk' N) ((S : Subgroup H).map
        (QuotientGroup.mk' N)) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hU2 : IsPGroup 2 U := hΛ.isPGroup_of_mem_USet hp hU
  obtain ⟨n, hn, hUn⟩ := exists_conj_le_of_le_sup_odd hN S.isPGroup' hU2 hUSN
  have hJ' : conjSub n⁻¹ J ∈ Λ := hΛ.conjInvariant _ J hJ
  have hU4 : 4 ≤ Nat.card U := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΛ.exists_data_of_mem_USet hp hU
    exact h4
  have hle : conjSub n⁻¹ U ≤ conjSub n⁻¹ J ⊓ (S : Subgroup H) := by
    refine le_inf (conjSub_mono (n := n⁻¹) hUJ) ?_
    have := conjSub_mono (n := n⁻¹) hUn
    rwa [conjSub_inv_conjSub] at this
  have hcard : 2 < Nat.card ↥(conjSub n⁻¹ J ⊓ (S : Subgroup H)) := by
    have h1 := Subgroup.card_le_of_le hle
    rw [natCard_conjSub_eq] at h1
    omega
  have hJeq : conjSub n⁻¹ J = J₀ := hK1 _ hJ' hcard
  have hJn : J = conjSub n J₀ := by
    rw [← hJeq, conjSub_conjSub_inv]
  have hnN : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  rw [hJn, AscQuot.map_conjSub, hnN, conjSub_one]

end Member

section Z2

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem muIsoZ2_of_unique_member (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {J₀ : Subgroup G}
    (hJ₀ : J₀ ∈ Ω) (h : ∀ ρ : Rep Ω W, ρ.K = J₀) : MuIsoZ2 Ω W := by
  exact muIsoZ2_of_unique_memberE (MuTab.muTabElt_eq_iff hP hW)
    (fun ρ => muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hW (MuTab.muTabElt_mem ρ)) hW
    (by
      obtain ⟨g₀, ρ₀, hρ₀⟩ := MuTab.exists_rep hP hW hJ₀
      exact ⟨ρ₀⟩) h

end Z2

section Main

variable {H : Type} [Group H] [Finite H] {p f : ℕ} [Fact p.Prime]

theorem exists_muIsoZ2_of_sylow (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {Λ : Set (Subgroup H)}
    (hΛ : HypOmegaMod p f Λ) (hΦ : HypOmegaMod p f (oddQuotientFamily Λ))
    (hA : ∀ M ∈ oddQuotientFamily Λ, AEmpty (oddQuotientFamily Λ) M) (S : Sylow 2 H)
    {J₀ : Subgroup H} (hJ₀ : J₀ ∈ Λ)
    (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀) :
    ∃ W' ∈ WSet (oddQuotientFamily Λ), MuIsoZ2 (oddQuotientFamily Λ) W' := by
  set N := classicalInvolutionOddCore H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set S' : Sylow 2 (H ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S with hS'def
  have hS' : (S' : Subgroup (H ⧸ N)) = (S : Subgroup H).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨η, hη, hinv⟩ := exists_invariant_mem_etaSet hp hq hΦ S'
  have hηG : η ∈ etaG (oddQuotientFamily Λ) := ⟨S', hη, hinv⟩
  set W' : Subgroup (H ⧸ N) := ⨆ U ∈ η, U with hW'def
  have hW' : W' ∈ WSet (oddQuotientFamily Λ) := ⟨η, hηG, rfl⟩
  refine ⟨W', hW', ?_⟩
  have hP : PartIHyp p f (oddQuotientFamily Λ) := ⟨hp, hq, hΦ, hA⟩
  refine muIsoZ2_of_unique_member hP hW' (J₀ := J₀.map π) ⟨J₀, hJ₀, rfl⟩ fun ρ => ?_
  have hW2 : IsPGroup 2 W' := isPGroup_of_mem_WSet hW'
  have hR2 : IsPGroup 2 ρ.R := ρ.hRK.2.1
  have hRN : ρ.R ≤ Subgroup.normalizer (W' : Set (H ⧸ N)) := ρ.hR.2
  have hRW : IsPGroup 2 ↥(ρ.R ⊔ W') := hR2.to_sup_of_normal_right' hW2 hRN
  obtain ⟨S'', hS''⟩ := hRW.exists_le_sylow
  have hηS'' : ∀ V ∈ η, V ≤ (S'' : Subgroup (H ⧸ N)) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans (le_sup_right.trans hS'')
  have hcard : 2 < Nat.card ↥(ρ.K ⊓ (S'' : Subgroup (H ⧸ N))) := by
    have h8 := hΦ.eight_le_of_mem_RSet hp ρ.hR.1
    have h1 := Subgroup.card_le_of_le (le_inf ρ.hRK.1 (le_sup_left.trans hS''))
    omega
  have h611 := l6_11_proved p f hp hq (H ⧸ N) (oddQuotientFamily Λ) hΦ S'' η hηG hηS'' ρ.K ρ.hK
    hcard
  have hV := hη.1 h611
  exact eq_image_of_mem_USet_le_sylow hp hΛ hΦ S J₀ hK1 ρ.hK hV.1 inf_le_left
    (hS' ▸ hV.2)

end Main

end T8S2

end CFSG.ClassicalInvolution.Asc77
