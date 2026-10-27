module

public import CFSG.GH74.Uniqueness.SU.KI1r4EFix
public import CFSG.GH74.Uniqueness.SU.KI1r4TG2a
public import CFSG.GH74.Uniqueness.SU.KI1r4EMov
public import CFSG.GH74.Uniqueness.SU.KI1r4ESimple

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4

open Subgroup CFSG CFSG.LocalCores CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.K.R3
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem lemma85_main
    {T : Sylow 2 H} {x : H} (h : Cfg H T x) (h4 : 4 ≤ Open.twoRank H)
    (hF : fittingSubgroup H ≠ ⊥) : generalizedFitting H = fittingSubgroup H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hEn : (layer H).Normal := layer_normal H
  have hlayer : layer H ≠ ⊥ := by
    intro hl
    apply hne
    rw [generalizedFitting, hl, sup_bot_eq]
  have hcomp : ∃ K : Subgroup H, IsComponent K := by
    by_contra hno
    push Not at hno
    apply hlayer
    have : {K : Subgroup H | IsComponent K} = ∅ := by
      ext K
      simp [hno K]
    rw [layer, this, sSup_empty]
  have hxx := h.mul_self_x
  have hFQ : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  have hQ2 : IsPGroup 2 (pCore 2 H) := pCore_isPGroup
  have hQn : (pCore 2 H).Normal := pCore_normal
  have hQne : pCore 2 H ≠ ⊥ := by rw [← hFQ]; exact hF
  obtain ⟨u, huQ, hu1, hu2, hxu⟩ :=
    exists_fixed_involution hQ2 hQne hxx (fun q hq => hQn.conj_mem q hq x)
  have huF : u ∈ fittingSubgroup H := hFQ ▸ huQ
  have huE : ∀ g ∈ layer H, u * g = g * u := by
    have hle : fittingSubgroup H ≤ centralizer (layer H : Set H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp fitting_layer_commute
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hle huF) g hg).symm
  have hK1 : ∀ K : Subgroup H, IsComponent K →
      ∃ z ∈ K, (∀ k ∈ K, z * k = k * z) ∧ z ≠ 1 :=
    fun K hK => h.component_center_nontrivial hu1 hu2 hxu huE hK
  have hEz : ∀ z ∈ layer H, (∀ g ∈ layer H, z * g = g * z) → z ∈ (T : Subgroup H) := by
    intro z hz hzc
    have hzF : z ∈ fittingSubgroup H := by
      apply CFSG.ComponentClassification.UnbalancedLayer.center_layer_le_fittingSubgroup
      exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2).symm, rfl⟩
    have hzQ : z ∈ pCore 2 H := hFQ ▸ hzF
    exact (hQ2.le_sylow_of_normal T) hzQ
  let A : Subgroup H :=
    { carrier := {a | a ∈ layer H ∧ (∀ g ∈ layer H, a * g = g * a) ∧ a * a = 1}
      one_mem' := ⟨Subgroup.one_mem _, fun g _ => by simp, by simp⟩
      mul_mem' := by
        rintro a b ⟨haE, hac, ha2⟩ ⟨hbE, hbc, hb2⟩
        refine ⟨(layer H).mul_mem haE hbE, fun g hg => ?_, ?_⟩
        · rw [mul_assoc, hbc g hg, ← mul_assoc, hac g hg, mul_assoc]
        · calc a * b * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [hbc a haE]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha2, hb2]; group
      inv_mem' := by
        rintro a ⟨haE, hac, ha2⟩
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hinv]
        exact ⟨haE, hac, ha2⟩ }
  have hAmem : ∀ a, a ∈ A ↔ a ∈ layer H ∧ (∀ g ∈ layer H, a * g = g * a) ∧ a * a = 1 :=
    fun a => Iff.rfl
  have hAn : A.Normal := by
    refine ⟨fun a ha g => ?_⟩
    obtain ⟨haE, hac, ha2⟩ := (hAmem a).mp ha
    rw [hAmem]
    refine ⟨hEn.conj_mem a haE g, fun e he => ?_, ?_⟩
    · have he' : g⁻¹ * e * g ∈ layer H := by simpa using hEn.conj_mem e he g⁻¹
      have := hac _ he'
      calc g * a * g⁻¹ * e = g * (a * (g⁻¹ * e * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * e * g) * a) * g⁻¹ := by rw [this]
        _ = e * (g * a * g⁻¹) := by group
    · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
        _ = 1 := by rw [ha2]; group
  have hAel : Open.IsElemAbelian 2 A := by
    rw [CFSG.GH74.Uniqueness.SU.SU5.isElemAbelian_iff]
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · exact ((hAmem a).mp ha).2.1 b ((hAmem b).mp hb).1
    · rw [pow_two]; exact ((hAmem a).mp ha).2.2
  have hAne : A ≠ ⊥ := by
    obtain ⟨K₀, hK₀⟩ := hcomp
    obtain ⟨z, hzK, hzc, hz1⟩ := hK1 K₀ hK₀
    have hzE : ∀ g ∈ layer H, z * g = g * z := center_of_component_central hK₀ hzK hzc
    have hzL : z ∈ layer H := component_le_layer hK₀ hzK
    have hzT : z ∈ (T : Subgroup H) := hEz z hzL hzE
    obtain ⟨n, hn⟩ := T.isPGroup' ⟨z, hzT⟩
    obtain ⟨j, hj⟩ := exists_pow_orderOf_eq_two hz1 ⟨n, congrArg Subtype.val hn⟩
    have hj1 : z ^ j ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hj; omega
    intro hbot
    apply hj1
    have : z ^ j ∈ A := by
      rw [hAmem]
      refine ⟨Subgroup.pow_mem _ hzL j, fun g hg => ?_, ?_⟩
      · exact ((Commute.pow_left (show Commute z g from hzE g hg) j)).eq
      · have : (z ^ j) ^ 2 = 1 := hj ▸ pow_orderOf_eq_one (z ^ j)
        rwa [pow_two] at this
    rw [hbot] at this
    exact Subgroup.mem_bot.mp this
  obtain ⟨y, hR⟩ := Cfg.rdata h hAn hAel hAne
  have hR82 := hR.lemma82 le_rfl hR.x_norm hR.y_norm
  unfold Lemma82Concl at hR82
  have hTrank : 4 ≤ Open.pRank 2 (T : Subgroup H) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T]
    exact h4
  set R : Subgroup H := (T : Subgroup H) ⊓ centralizer (A : Set H) with hRdef
  obtain ⟨h64, hZ4, hfr, -, hcom, -, -⟩ : (Nat.card R = 64 ∧ Nat.card (center ↥R) = 4 ∧
      frattini ↥R = center ↥R ∧ (∀ u : ↥R, u * u ∈ center ↥R) ∧
      (∀ u v : ↥R, ⁅u, v⁆ ∈ center ↥R) ∧ (∀ a ∈ center ↥R, a * a = 1) ∧
      Nonempty (↥(centralizer ({x} : Set H) ⊓ R) ≃* QuaternionGroup 2)) := by
    rcases hR82 with ⟨hab, c, hcR, -, hgen, -⟩ | hb
    · exfalso
      have := hR.pRank_T_le_three hab ⟨c, hcR, hgen⟩
      omega
    · exact hb
  have hAE : ∀ a ∈ A, a ∈ layer H ∧ ∀ g ∈ layer H, a * g = g * a :=
    fun a ha => ⟨((hAmem a).mp ha).1, ((hAmem a).mp ha).2.1⟩
  have d := L85Data.of_basic hR h64 hZ4 hfr hcom hAE hEz hK1 hcomp
  by_cases hfix : ∃ K : Subgroup H, IsComponent K ∧ ∀ k ∈ K, y * k * y⁻¹ ∈ K
  · obtain ⟨K, hK, hKy⟩ := hfix
    exact d.false_of_fixed hK hKy
  · exact d.false_of_moved hR.y_three (fun K hK hKy => hfix ⟨K, hK, hKy⟩) hcomp

end CFSG.GH74.Uniqueness.SU.K.R4
