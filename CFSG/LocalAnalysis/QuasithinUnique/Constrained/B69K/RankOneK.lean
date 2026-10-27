module

public import CFSG.Quasithin.Background.FFC12B
public import CFSG.Quasithin.Background.FFC12E
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace B69K

open CFSG.Quasithin.B69

theorem asB69RankOneSylowK : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), B69.CompHypK X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) →
          CFSG.QuasithinUnique.IsSylowTwoOf A L := by
  intro V _ _ hV X T M A L hH W hW hex
  obtain ⟨e, he, hnat⟩ := hex
  obtain ⟨-, -, hO2, -, -, hA, hL, hLA⟩ := hH
  have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
  have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
    B19Aux.conj_mem_of_le_normalizer hAnL ha hl
  have hAW := a_stab_irr hV hA hL.2.2 hLA hW
  have hAst : A ≤ stabSub W := B1.le_stabSub_of_invariant hAW
  have hAU : A ≤ stabSub (W ⊓ fixV L) :=
    B1.le_stabSub_of_invariant (isInv_inf hAW (B1Red.fixV_inv_of_normalizes hAn))
  have hact := exists_act_natural hL.2.2 hW he hnat hA.1 hAn hAW
  obtain ⟨hS, hge⟩ := natural_counts hV hA hL.2.2 hLA hW he hnat hact
  have hsup := (eq_sup_fixV_of_sec hV hA hL.2.2 hLA hW hS).1
  have hAL : A ≤ L := le_of_act hV hO2 hA hL hLA hW hsup hact
  have hcard : Nat.card (autSec A W (W ⊓ fixV L)) ≤ Nat.card A := by
    have := card_autSec_mul hAst hAU
    exact Nat.le_of_dvd Nat.card_pos ⟨_, this.symm⟩
  obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
  let π : ↥(StatedSL 2 K) →* ↥L := π₀
  have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
  exact isSylowTwoOf_of_natural hAL hA.1.2.2.1.2 he hK π hπ.1 (hge.trans hcard)

theorem asB69RankOneBorelK : ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M A L : Subgroup (MulAut V)), B69.CompHypK X T M A L →
      ∀ W : Subgroup V, W ∈ IrrPlus L (⊤ : Subgroup V) →
        (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL L W (W ⊓ fixV L) 2 e) →
          M ⊓ L = L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
  intro V _ _ hV X T M A L hH W hW hex
  obtain ⟨e, he, hnat⟩ := hex
  obtain ⟨-, hmp, hO2, -, -, hA, hL, hLA⟩ := hH
  have hTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    A312.isSylowTwoOf_inf_of_subnormal hL.2.1 hmp.isSylow
  apply le_antisymm
  · obtain ⟨K, hKf, hKfin, hK, π₀, hπ₀⟩ := hnat
    let π : ↥(StatedSL 2 K) →* ↥L := π₀
    have hπ : (FFModel.nat (StatedSL 2 K)).RealizesVia L W (W ⊓ fixV L) π := hπ₀
    let π' : Matrix.SpecialLinearGroup (Fin 2) K →* ↥L :=
      π.comp (specialLinearGroupEquivStatedSL 2 K).toMonoidHom
    have hπ's : Function.Surjective π' :=
      hπ.1.comp (specialLinearGroupEquivStatedSL 2 K).surjective
    set U : Subgroup ↥L := (T ⊓ L).subgroupOf L with hUdef
    set R : Subgroup ↥L := (M ⊓ L).subgroupOf L with hRdef
    have hUR : U ≤ R := fun x hx => ⟨hmp.le hx.1, hx.2⟩
    have hUp : IsPGroup 2 ↥U :=
      hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).symm
    have hUi : ¬ 2 ∣ U.index := hTL.2.2
    rcases overgroup_sylow_of_quotient_sl2 he hK π' hπ's hUp hUi hUR with h | h
    · exfalso
      apply not_component_le_M hmp hO2 hL
      intro x hx
      have : (⟨x, hx⟩ : ↥L) ∈ R := by rw [h]; trivial
      exact this.1
    · intro x hx
      have hxR : (⟨x, hx.2⟩ : ↥L) ∈ R := hx
      have hn := h hxR
      rw [Subgroup.mem_normalizer_iff] at hn
      have hxn : x ∈ Subgroup.normalizer ((T ⊓ L : Subgroup (MulAut V)) : Set (MulAut V)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          exact (hn ⟨w, hw.2⟩).1 hw
        · intro hw
          have hwL : w ∈ L := by
            have h1 : x⁻¹ * (x * w * x⁻¹) * x ∈ L :=
              L.mul_mem (L.mul_mem (L.inv_mem hx.2) hw.2) hx.2
            have h2 : x⁻¹ * (x * w * x⁻¹) * x = w := by group
            rwa [h2] at h1
          exact (hn ⟨w, hwL⟩).2 hw
      exact ⟨hx.2, hxn⟩
  · intro x hx
    exact ⟨normalizer_le_M_of_component hmp hO2 hL hTL hx, hx.1⟩

end B69K

end CFSG.Quasithin
