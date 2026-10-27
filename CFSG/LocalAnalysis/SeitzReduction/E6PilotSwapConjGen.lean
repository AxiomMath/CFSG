module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenFactor
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwapUnique
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverDiag
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (swapDiagHom swapDiagHom_apply F4Work QuadraticFrobenius)

local instance e6PilotSwapConjGenNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_mul_dvd_card_sup {P₁ P₂ Z₁ Z₂ : Subgroup G} (h₁₂ : P₂ ≤ centralizer (P₁ : Set G))
    (hinf : P₁ ⊓ P₂ ≤ Z₁) {D₁ D₂ : ℕ} (h₁ : D₁ * Nat.card Z₁ ∣ Nat.card P₁)
    (h₂ : D₂ * Nat.card Z₂ ∣ Nat.card P₂) : D₁ * D₂ ∣ Nat.card (P₁ ⊔ P₂ : Subgroup G) := by
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (h₁₂.trans (centralizer_le_normalizer _))
  obtain ⟨m, hm⟩ := card_dvd_of_le hinf
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hpos : 0 < Nat.card (P₁ ⊓ P₂ : Subgroup G) := Nat.card_pos
  refine ⟨m * a * Nat.card Z₂ * b, Nat.eq_of_mul_eq_mul_right hpos ?_⟩
  rw [hprod, ha, hb, hm]
  ring

theorem two_pow_add_dvd_card_sup {X₁ X₂ : Subgroup G} (h₁₂ : X₂ ≤ centralizer (X₁ : Set G))
    (hodd : Odd (Nat.card (X₁ ⊓ X₂ : Subgroup G))) {a b : ℕ} (ha : 2 ^ a ∣ Nat.card X₁)
    (hb : 2 ^ b ∣ Nat.card X₂) : 2 ^ (a + b) ∣ Nat.card (X₁ ⊔ X₂ : Subgroup G) := by
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (h₁₂.trans (centralizer_le_normalizer _))
  have h1 : 2 ^ (a + b) ∣ Nat.card (X₁ ⊔ X₂ : Subgroup G) * Nat.card (X₁ ⊓ X₂ : Subgroup G) := by
    rw [hprod, pow_add]
    exact mul_dvd_mul ha hb
  exact (Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)).dvd_of_dvd_mul_right h1

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_two {t w : G} (ht : orderOf t = 2)
    (hw : w ∈ zpowers t) : w = 1 ∨ w = t := by
  rw [← mem_powers_iff_mem_zpowers] at hw
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hw
  rw [← pow_mod_orderOf, ht]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · left
    rw [h, pow_zero]
  · right
    rw [h, pow_one]

theorem odd_card_center_of_swap {G₁ L : Subgroup G} {t : G} (hqs : CFSG.Open.IsQuasisimple G₁)
    (ht : orderOf t = 2) (h₁₂ : G₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hL : L ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    Odd (Nat.card (center G₁)) := by
  obtain ⟨hperf, hbot, -⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqs
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  set G₂ := G₁.map (MulAut.conj t).toMonoidHom with hG₂
  have hnot : ¬ t ∈ centralizer (G₁ : Set G) := by
    intro htc
    have hG : G₂ = G₁ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← mem_centralizer_iff.1 htc y hy, mul_inv_cancel_right]
        exact hy
      · intro hx
        refine ⟨x, hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [← mem_centralizer_iff.1 htc x hx, mul_inv_cancel_right]
    rw [hG] at h₁₂
    exact hbot (by rw [← hperf, commutator_eq_bot_iff_le_centralizer.2 h₁₂])
  have hcen : ∀ x : G, x ∈ centralizer (G₁ : Set G) → x ∈ centralizer (G₂ : Set G) →
      x ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) := fun x h1 h2 =>
    F4Pilot.centralizer_inf_centralizer_le_centralizer_sup ⟨h1, h2⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G₁) 2 h2
  set z' : G := ((z : G₁) : G) with hz'
  have hz1 : z' ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzz : z' * z' = 1 := by
    have h1 : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
    have h2 := congrArg (fun y : center G₁ => ((y : G₁) : G)) h1
    simpa [sq] using h2
  have hzG₁ : z' ∈ G₁ := (z : G₁).2
  have hzc1 : z' ∈ centralizer (G₁ : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (mem_center_iff.1 z.2 ⟨g, hg⟩)
  have hzc2 : z' ∈ centralizer (G₂ : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact (mem_centralizer_iff.1 (h₁₂ hg) z' hzG₁).symm
  have hconj : ∀ x : G, x ∈ centralizer (G₁ : Set G) → x ∈ centralizer (G₂ : Set G) →
      t * x * t⁻¹ ∈ centralizer (G₁ : Set G) ∧ t * x * t⁻¹ ∈ centralizer (G₂ : Set G) := by
    intro x h1 h2
    constructor
    · rw [mem_centralizer_iff]
      intro g hg
      have hg' : t * g * t⁻¹ ∈ G₂ := ⟨g, hg, rfl⟩
      have h3 := mem_centralizer_iff.1 h2 _ hg'
      have h4 : t * (t * g * t⁻¹) * t⁻¹ = g := by
        rw [show t * (t * g * t⁻¹) * t⁻¹ = (t * t) * g * (t * t)⁻¹ by group, htt]
        group
      calc g * (t * x * t⁻¹) = t * ((t⁻¹ * g * t) * x) * t⁻¹ := by group
        _ = t * ((t * g * t⁻¹) * x) * t⁻¹ := by rw [htinv]
        _ = t * (x * (t * g * t⁻¹)) * t⁻¹ := by rw [h3]
        _ = t * x * t⁻¹ * (t * (t * g * t⁻¹) * t⁻¹) := by group
        _ = t * x * t⁻¹ * g := by rw [h4]
    · rw [mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h3 := mem_centralizer_iff.1 h1 g hg
      calc t * g * t⁻¹ * (t * x * t⁻¹) = t * (g * x) * t⁻¹ := by group
        _ = t * (x * g) * t⁻¹ := by rw [h3]
        _ = t * x * t⁻¹ * (t * g * t⁻¹) := by group
  obtain ⟨hc1, hc2⟩ := hconj z' hzc1 hzc2
  set w := z' * (t * z' * t⁻¹) with hw
  have hwc : w ∈ centralizer ((G₁ ⊔ G₂ : Subgroup G) : Set G) :=
    hcen w (mul_mem hzc1 hc1) (mul_mem hzc2 hc2)
  have hwL : w ∈ centralizer (L : Set G) := centralizer_le (SetLike.coe_subset_coe.2 hL) hwc
  have hzt : z' * (t * z' * t⁻¹) = t * z' * t⁻¹ * z' :=
    mem_centralizer_iff.1 hc1 z' hzG₁
  have hwt : w ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff, hw]
    calc z' * (t * z' * t⁻¹) * t = t * z' * t⁻¹ * z' * t := by rw [hzt]
      _ = t * (z' * (t * z' * t⁻¹)) := by rw [htinv]; group
  have hwz : w ∈ zpowers t := hKt ▸ ⟨hwL, hwt⟩
  have hwt' : w = 1 ∨ w = t := eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht hwz
  rcases hwt' with h1 | h1
  ·
    have hz2 : t * z' * t⁻¹ = z' := by
      have : t * z' * t⁻¹ = z'⁻¹ := eq_inv_of_mul_eq_one_right (hw ▸ h1)
      rw [this, inv_eq_of_mul_eq_one_right hzz]
    have hzt' : z' ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc z' * t = t * z' * t⁻¹ * t := by rw [hz2]
        _ = t * z' := by group
    have hzL : z' ∈ centralizer (L : Set G) :=
      centralizer_le (SetLike.coe_subset_coe.2 hL) (hcen z' hzc1 hzc2)
    have hzz' : z' ∈ zpowers t := hKt ▸ ⟨hzL, hzt'⟩
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two ht hzz' with h | h
    · exact hz1 h
    · exact hnot (h ▸ hzc1)
  ·
    have htc : t ∈ centralizer (G₁ : Set G) := by
      rw [← h1]
      exact centralizer_le (SetLike.coe_subset_coe.2 le_sup_left) hwc
    exact hnot htc

end Generic

section Steps


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_normalizes_both_E6 (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    {k : Type} [Field k] (hk : Nat.card k = 2 ^ f) (e : L ≃* adjointGroup .E6 k) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {M₁ M₂ : Subgroup G} (h₁₂ : M₂ ≤ centralizer (M₁ : Set G)) (hM₁ : ⁅M₁, M₁⁆ = M₁)
    (hM₂ : ⁅M₂, M₂⁆ = M₂) (hZ₁ : Odd (Nat.card (center M₁))) (hZ₂ : Odd (Nat.card (center M₂)))
    (e₁ : M₁ ⧸ center M₁ ≃* adjointGroup .E6 k) (e₂ : M₂ ⧸ center M₂ ≃* adjointGroup .E6 k)
    (hinf : M₁ ⊓ M₂ ≤ (center M₁).map M₁.subtype) (ht₁ : t ∈ normalizer (M₁ : Set G))
    (ht₂ : t ∈ normalizer (M₂ : Set G)) : False := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hk
  obtain ⟨X₁, hX₁, hX₁'⟩ := exists_le_inf_centralizer_E6_factor hM₁ hZ₁ hf hk e₁ ht ht₁
  obtain ⟨X₂, hX₂, hX₂'⟩ := exists_le_inf_centralizer_E6_factor hM₂ hZ₂ hf hk e₂ ht ht₂
  have hX₁M : X₁ ≤ M₁ := hX₁.trans inf_le_left
  have hX₂M : X₂ ≤ M₂ := hX₂.trans inf_le_left
  have h12 : X₂ ≤ centralizer (X₁ : Set G) := fun y hy =>
    centralizer_le (SetLike.coe_subset_coe.2 hX₁M) (h₁₂ (hX₂M hy))
  have hinfX : X₁ ⊓ X₂ ≤ (center M₁).map M₁.subtype := (inf_le_inf hX₁M hX₂M).trans hinf
  have hodd : Odd (Nat.card (X₁ ⊓ X₂ : Subgroup G)) := by
    refine hZ₁.of_dvd_nat ?_
    rw [← card_map_of_injective M₁.subtype_injective]
    exact card_dvd_of_le hinfX
  have hXt : X₁ ⊔ X₂ ≤ centralizer ({t} : Set G) :=
    sup_le (hX₁.trans inf_le_right) (hX₂.trans inf_le_right)
  have hb := factorization_card_le_of_le_centralizer_E6 hset.standard hk e ht hKt hXt
  have hlt : f.factorization 2 < f := Nat.factorization_lt 2 (by omega)
  have hpos : Nat.card (X₁ ⊔ X₂ : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  have hbig : ∀ a b : ℕ, 2 ^ a ∣ Nat.card X₁ → 2 ^ b ∣ Nat.card X₂ →
      a + b ≤ 36 * f + 2 + f.factorization 2 := by
    intro a b ha hb'
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1
      (two_pow_add_dvd_card_sup h12 hodd ha hb')
    omega
  have hfield2 : ∀ (X M : Subgroup G) (e' D : ℕ), f = 2 * e' → 1 ≤ e' →
      (D = ordE6 (2 ^ e') ∨ D = ordTwistedE6 (2 ^ e')) →
      D * Nat.card (X ⊓ (center M).map M.subtype : Subgroup G) ∣ Nat.card X →
      2 ^ (18 * f) ∣ Nat.card X := by
    intro X M e' D hfe he' hD hdvd
    have h2D : 2 ^ (18 * f) ∣ D := by
      rcases hD with rfl | rfl
      · obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordE6 he').two
        rw [hr, hfe, show 18 * (2 * e') = e' * 36 by ring]
        exact Dvd.intro _ rfl
      · obtain ⟨r, -, hr⟩ := (CFSG.Timmesfeld.Orders.profile_ordTwistedE6 he').two
        rw [hr, hfe, show 18 * (2 * e') = e' * 36 by ring]
        exact Dvd.intro _ rfl
    exact h2D.trans ((Dvd.intro _ rfl).trans hdvd)
  rcases hX₁' with h1 | ⟨e₁', he₁, hfe₁, hp₁, D₁, hD₁, hd₁⟩ <;>
    rcases hX₂' with h2 | ⟨e₂', he₂, hfe₂, hp₂, D₂, hD₂, hd₂⟩
  · have := hbig _ _ h1 h2
    omega
  · have := hbig _ _ h1 (hfield2 _ _ _ _ hfe₂ he₂ hD₂ hd₂)
    omega
  · have := hbig _ _ (hfield2 _ _ _ _ hfe₁ he₁ hD₁ hd₁) h2
    omega
  ·
    have hee : e₂' = e₁' := by omega
    subst hee
    have hOut : Group.IsSolvable (Outer L) :=
      ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier k).1⟩⟩
    have hPL : X₁ ⊔ X₂ ≤ L := std_perfect_le hset hOut htC ht
      (F4Pilot.commutator_sup_eq_sup_of_perfect hp₁ hp₂) hXt
    have hdvd := (card_mul_dvd_card_sup h12 (le_inf inf_le_left hinfX) hd₁ hd₂).trans
      (card_dvd_of_le hPL)
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6, hk,
      hfe₁, show (2 : ℕ) ^ (2 * e₂') = (2 ^ e₂') ^ 2 by rw [← pow_mul, mul_comm]] at hdvd
    exact not_mul_dvd_ordE6_sq he₂ hD₁ hD₂ hdvd

theorem range_swapDiagHom_eq_of_swap_E6 (hset : StandardSetting G L) {k : Type} [Field k]
    [Finite k] (e : L ≃* adjointGroup .E6 k) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M₁ : Subgroup G}
    (hcomm : M₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (M₁ : Set G))
    (hM₁ : ⁅M₁, M₁⁆ = M₁) (e₁ : M₁ ⧸ center M₁ ≃* adjointGroup .E6 k) :
    (swapDiagHom hcomm).range = L := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨3, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier k).1⟩⟩
  set δ := swapDiagHom hcomm with hδ
  have htop : ⁅(⊤ : Subgroup M₁), (⊤ : Subgroup M₁)⁆ = (⊤ : Subgroup M₁) := by
    have h1 := commutator_subgroupOf_eq_self (le_refl M₁) hM₁
    rwa [subgroupOf_self] at h1
  have hrp : ⁅δ.range, δ.range⁆ = δ.range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, htop]
  have hrt : δ.range ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨x, rfl⟩
    exact swapDiagHom_mem_centralizer hcomm htt x
  have hle : δ.range ≤ L := std_perfect_le hset hOut htC ht hrp hrt
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hker : δ.ker ≤ center M₁ := by
    intro x hx
    rw [MonoidHom.mem_ker, swapDiagHom_apply] at hx
    have hxt : (x : G) ∈ M₁.map (MulAut.conj t).toMonoidHom := by
      refine ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc t * (x : G)⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
        _ = x := (eq_inv_of_mul_eq_one_left hx).symm
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 (hcomm hxt) g g.2)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center M₁)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker
  have h3 : Nat.card δ.ker ≤ Nat.card (center M₁) := Subgroup.card_le_of_le hker
  have h4 : Nat.card (M₁ ⧸ δ.ker) = Nat.card δ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv
  have h5 : Nat.card (M₁ ⧸ center M₁) = Nat.card L := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e.toEquiv]
  have hZpos : 0 < Nat.card (center M₁) := Nat.card_pos
  rw [← h4]
  refine Nat.le_of_mul_le_mul_right ?_ hZpos
  calc Nat.card L * Nat.card (center M₁) = Nat.card M₁ := by rw [← h5, ← h1]
    _ = Nat.card (M₁ ⧸ δ.ker) * Nat.card δ.ker := h2
    _ ≤ Nat.card (M₁ ⧸ δ.ker) * Nat.card (center M₁) := Nat.mul_le_mul_left _ h3

theorem le_iSup_map_levi_singleton {k : Type} [Field k] (e : L ≃* adjointGroup .E6 k) :
    L ≤ ⨆ i, (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i}).map
      (L.subtype.comp e.symm.toMonoidHom) := by
  intro l hl
  have htop : ⊤ ≤ (⨆ i, (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i}).map
      (L.subtype.comp e.symm.toMonoidHom)).comap (L.subtype.comp e.symm.toMonoidHom) :=
    top_le_of_forall_levi_singleton_le_E6 fun i y hy =>
      le_iSup (fun i => (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i}).map
        (L.subtype.comp e.symm.toMonoidHom)) i ⟨y, hy, rfl⟩
  have h1 := htop (mem_top (e ⟨l, hl⟩))
  rw [mem_comap] at h1
  have h2 : (L.subtype.comp e.symm.toMonoidHom) (e ⟨l, hl⟩) = l := by simp
  rwa [h2] at h1

theorem map_levi_eq_modelToG {k : Type} [Field k] (e : L ≃* adjointGroup .E6 k)
    (J : Finset (Fin (Tag.rank .E6))) :
    (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup J).map
        (L.subtype.comp e.symm.toMonoidHom) =
      modelToG e (rootSpan .E6 k (amalgamRoots J)) := by
  rw [modelToG, Subgroup.map_map, levi_adjDatumE6_eq]

theorem le_iSup_pieceCore_E6 {k : Type} [Field k] [Finite k] (hq : 4 ≤ Nat.card k)
    (e : L ≃* adjointGroup .E6 k) :
    L ≤ ⨆ J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}, pieceCore e J.1 := by
  refine (le_iSup_map_levi_singleton e).trans (iSup_le fun i => ?_)
  rw [map_levi_eq_modelToG]
  refine (modelToG_rootSpan_le_pieceCore_of_perfect e {i}
    (commutator_rootSpan_amalgamRoots_eq_E6 (F4Pilot.three_le_natCard_top_units hq) _)).trans ?_
  exact le_iSup (fun J : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2} => pieceCore e J.1)
    ⟨{i}, by simp⟩

theorem ker_swapDiagHom_le_center {M₁ : Subgroup G} {t : G}
    (hcomm : M₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (M₁ : Set G)) :
    (swapDiagHom hcomm).ker ≤ center M₁ := by
  intro x hx
  rw [MonoidHom.mem_ker, swapDiagHom_apply] at hx
  have hxt : (x : G) ∈ M₁.map (MulAut.conj t).toMonoidHom := by
    refine ⟨(x : G)⁻¹, inv_mem x.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc t * (x : G)⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      _ = x := (eq_inv_of_mul_eq_one_left hx).symm
  rw [mem_center_iff]
  intro g
  exact Subtype.ext (mem_centralizer_iff.1 (hcomm hxt) g g.2)

theorem le_iSup_perfectCore_of_swap_E6 {k : Type} [Field k] [Finite k] (hq : 4 ≤ Nat.card k)
    (e : L ≃* adjointGroup .E6 k) {t : G} (htC : t ∈ centralizer (L : Set G)) {M₁ : Subgroup G}
    (hcomm : M₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (M₁ : Set G))
    (hM₁ : ⁅M₁, M₁⁆ = M₁) (hrange : (swapDiagHom hcomm).range = L)
    (htN : t ∈ normalizer ((M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) :
    M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom ≤ ⨆ i : Fin (Tag.rank .E6),
      perfectCore ((M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer (modelToG e (leviTorus k {i}) : Set G)) := by
  have : Finite (adjointGroup .E6 k) := by
    have : Finite (ModGL Tag.E6 k) := finite_modGL
    infer_instance
  set M : Subgroup G := M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom with hM
  set δ := swapDiagHom hcomm with hδ
  set ψ : adjointGroup .E6 k →* G := L.subtype.comp e.symm.toMonoidHom with hψ
  have hker := ker_swapDiagHom_le_center hcomm
  set P : Subgroup G := ⨆ i : Fin (Tag.rank .E6),
    perfectCore (M ⊓ centralizer (modelToG e (leviTorus k {i}) : Set G)) with hP
  have htop : ⁅(⊤ : Subgroup M₁), (⊤ : Subgroup M₁)⁆ = (⊤ : Subgroup M₁) := by
    have h1 := commutator_subgroupOf_eq_self (le_refl M₁) hM₁
    rwa [subgroupOf_self] at h1
  have hQ : ∀ i : Fin (Tag.rank .E6), ∃ Q : Subgroup M₁, Q.map M₁.subtype ≤ P ∧
      (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i}).map ψ ≤ Q.map δ := by
    intro i
    set R := (CFSG.LieType.CurtisTits.levi (adjDatumE6 k).rootGroup {i}).map ψ with hR
    have hRL : R ≤ δ.range := by
      rw [hrange]
      rintro _ ⟨y, -, rfl⟩
      exact (e.symm y).2
    have hRp : ⁅R, R⁆ = R := by rw [hR, ← map_commutator, commutator_levi_eq_E6 hq]
    refine ⟨perfectCore (R.comap δ), ?_, ?_⟩
    · have hQp : ⁅(perfectCore (R.comap δ)).map M₁.subtype,
          (perfectCore (R.comap δ)).map M₁.subtype⁆ = (perfectCore (R.comap δ)).map M₁.subtype := by
        rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
      refine le_trans ?_ (le_iSup (fun i : Fin (Tag.rank .E6) =>
        perfectCore (M ⊓ centralizer (modelToG e (leviTorus k {i}) : Set G))) i)
      refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf ((map_subtype_le _).trans
        le_sup_left) ?_) hQp
      rw [← le_centralizer_iff]
      intro τ hτ
      have hτL : τ ∈ δ.range := hrange ▸ modelToG_le e _ hτ
      obtain ⟨y, rfl⟩ := hτL
      refine mul_mem ?_ ?_
      · refine swapMem_centralizer_of_perfect hQp (Z := δ.ker.map M₁.subtype) ?_ ?_ fun x hx => ?_
        · rintro _ ⟨z, hz, rfl⟩
          rw [mem_centralizer_iff]
          rintro _ ⟨w, -, rfl⟩
          exact (congrArg Subtype.val (mem_center_iff.1 (hker hz) w))
        · rintro _ ⟨z, hz, rfl⟩
          rw [mem_centralizer_iff]
          rintro _ ⟨w, -, rfl⟩
          exact (congrArg Subtype.val (mem_center_iff.1 (hker hz) w))
        · obtain ⟨x, hx, rfl⟩ := hx
          have hxR : δ x ∈ R := (CFSG.Quasithin.perfectCore_le (R.comap δ) hx : x ∈ R.comap δ)
          obtain ⟨c, hc, hcx⟩ := hxR
          obtain ⟨d, hdT, hdy⟩ := (mem_modelToG e).1 hτ
          have hcd : c * d = d * c := (mem_centralizer_iff.1
            (levi_le_centralizer_leviTorus_E6 {i} hc) d (mem_subgroupOf.2 hdT)).symm
          have hcomm' : δ x * δ y = δ y * δ x := by
            rw [← hcx, ← hdy]
            change ψ c * ψ d = ψ d * ψ c
            rw [← map_mul, ← map_mul, hcd]
          refine ⟨x⁻¹ * (y * x * y⁻¹), ?_, by simp⟩
          show x⁻¹ * (y * x * y⁻¹) ∈ δ.ker
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, ← hcomm']
          group
      · exact centralizer_le (SetLike.coe_subset_coe.2 (map_subtype_le _)) (hcomm ⟨y, y.2, rfl⟩)
    · rw [CFSG.Quasithin.map_perfectCore, map_comap_eq_self hRL,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect hRp]
  choose Q hQP hQR using hQ
  set S : Subgroup M₁ := ⨆ i, Q i with hS
  have hSL : L ≤ S.map δ := by
    refine (le_iSup_map_levi_singleton e).trans (iSup_le fun i => (hQR i).trans ?_)
    exact map_mono (le_iSup Q i)
  have hM₁S : (⊤ : Subgroup M₁) ≤ S := by
    refine F4Pilot.perfect_le_of_forall_exists_commute htop le_top fun a _ => ?_
    have haL : δ a ∈ S.map δ := hSL (hrange ▸ ⟨a, rfl⟩)
    obtain ⟨s, hs, hsa⟩ := haL
    refine ⟨s, hs, s⁻¹ * a, by group, fun b _ => ?_⟩
    have hk : s⁻¹ * a ∈ δ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hsa, inv_mul_cancel]
    exact (mem_center_iff.1 (hker hk) b).symm
  have hM₁P : M₁ ≤ P := by
    intro x hx
    have h1 : (⟨x, hx⟩ : M₁) ∈ S := hM₁S (mem_top _)
    have h2 : S.map M₁.subtype ≤ P := by
      rw [hS, Subgroup.map_iSup]
      exact iSup_le hQP
    exact h2 ⟨_, h1, rfl⟩
  have htP : ∀ i : Fin (Tag.rank .E6),
      (perfectCore (M ⊓ centralizer (modelToG e (leviTorus k {i}) : Set G))).map
        (MulAut.conj t).toMonoidHom =
      perfectCore (M ⊓ centralizer (modelToG e (leviTorus k {i}) : Set G)) := by
    intro i
    refine F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.1
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore _
        (inf_normalizer_le_normalizer_inf ⟨htN, le_normalizer ?_⟩))
    exact centralizer_le (SetLike.coe_subset_coe.2 (modelToG_le e _)) htC
  refine sup_le hM₁P ?_
  calc M₁.map (MulAut.conj t).toMonoidHom ≤ P.map (MulAut.conj t).toMonoidHom := map_mono hM₁P
    _ = P := by rw [hP, Subgroup.map_iSup]; exact iSup_congr htP

end Steps

section Input


theorem e6SwapConjGenInput_holds : E6SwapConjGenInput := by
  intro G _ _ L K₂ _ _ _ σ f _ hf e t hw _ G₁ hqs ⟨eG⟩ h₁₂ hsup h htM
  have hk : Nat.card (fixSubfield σ) = 2 ^ f := hw.card_eq
  have hq4 : 4 ≤ Nat.card (fixSubfield σ) := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have ht := hw.orderOf_eq
  have hKt := hw.inf_eq
  have hset := hw.standard
  have hLG₀ : L ≤ G₁ ⊔ G₁.map (MulAut.conj t).toMonoidHom := by
    rw [hsup]
    exact le_iSup_pieceCore_E6 hq4 e
  have hZ := odd_card_center_of_swap hqs ht h₁₂ hLG₀ hKt
  obtain ⟨hperf, hbot, hn₁⟩ := F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqs
  have hG₂ : G₁.map (MulAut.conj t).toMonoidHom = CFSG.conjugate G₁ t⁻¹ := by
    rw [CFSG.conjugate, inv_inv]
  rw [hG₂] at h₁₂ hsup
  set G₂ := CFSG.conjugate G₁ t⁻¹ with hG₂def
  set M₁ := CFSG.conjugate G₁ h with hM₁def
  set M₂ := CFSG.conjugate G₂ h with hM₂def
  have hMsup : CFSG.conjugate (pieceSup e) h = M₁ ⊔ M₂ := by
    rw [← hsup]
    exact F4Pilot.conjugate_sup_eq_sup_conjugate _ _ _
  rw [hMsup] at htM ⊢
  have h₁₂' : M₂ ≤ centralizer (M₁ : Set G) :=
    F4Pilot.conjugate_le_centralizer_conjugate_of_le h₁₂ h
  have hG₂p : ⁅G₂, G₂⁆ = G₂ := commutator_conjugate_eq hperf t⁻¹
  have hM₁p : ⁅M₁, M₁⁆ = M₁ := commutator_conjugate_eq hperf h
  have hM₂p : ⁅M₂, M₂⁆ = M₂ := commutator_conjugate_eq hG₂p h
  have hZ₁ : Odd (Nat.card (center M₁)) := by rw [hM₁def, card_center_conjugate]; exact hZ
  have hZ₂ : Odd (Nat.card (center M₂)) := by
    rw [hM₂def, card_center_conjugate, hG₂def, card_center_conjugate]
    exact hZ
  have e₁ : M₁ ⧸ center M₁ ≃* adjointGroup .E6 (fixSubfield σ) :=
    (coverConjugateQuotientCenterEquiv G₁ h).symm.trans eG
  have e₂ : M₂ ⧸ center M₂ ≃* adjointGroup .E6 (fixSubfield σ) :=
    (coverConjugateQuotientCenterEquiv G₂ h).symm.trans
      ((coverConjugateQuotientCenterEquiv G₁ t⁻¹).symm.trans eG)
  have hn₁' : ∀ N : Subgroup G, N ≤ M₁ → M₁ ≤ normalizer (N : Set G) →
      N ≤ centralizer (M₁ : Set G) ∨ N = M₁ :=
    F4Pilot.dichotomy_map_mulAut (MulAut.conj h⁻¹) hn₁
  have hn₂' : ∀ N : Subgroup G, N ≤ M₂ → M₂ ≤ normalizer (N : Set G) →
      N ≤ centralizer (M₂ : Set G) ∨ N = M₂ :=
    F4Pilot.dichotomy_map_mulAut (MulAut.conj h⁻¹)
      (F4Pilot.dichotomy_map_mulAut (MulAut.conj t⁻¹⁻¹) hn₁)
  have hM₁bot : M₁ ≠ ⊥ := fun h0 =>
    hbot ((map_eq_bot_iff_of_injective G₁ (MulAut.conj h⁻¹).injective).1 h0)
  have hM₂bot : M₂ ≠ ⊥ := fun h0 => hbot ((map_eq_bot_iff_of_injective G₁
    (MulAut.conj t⁻¹⁻¹).injective).1 ((map_eq_bot_iff_of_injective G₂
      (MulAut.conj h⁻¹).injective).1 h0))
  rcases F4Pilot.map_conj_eq_or_eq_of_perfect h₁₂' hM₁p hM₁bot hn₁' hn₂' htM with hc | hc
  ·
    exfalso
    have ht₁ : t ∈ normalizer (M₁ : Set G) := F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 hc
    have htM' : t ∈ normalizer ((M₂ ⊔ M₁ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact htM
    have h₂₁ : M₁ ≤ centralizer (M₂ : Set G) := le_centralizer_iff.1 h₁₂'
    have ht₂ : t ∈ normalizer (M₂ : Set G) := by
      rcases F4Pilot.map_conj_eq_or_eq_of_perfect h₂₁ hM₂p hM₂bot hn₂' hn₁' htM' with h' | h'
      · exact F4Pilot.mem_normalizer_iff_map_conj_toMonoidHom.2 h'
      · exfalso
        have h12 : M₂ = M₁ := F4Pilot.map_conj_toMonoidHom_inj.1 (h'.trans hc.symm)
        rw [h12] at h₁₂'
        exact hM₁bot (by rw [← hM₁p, commutator_eq_bot_iff_le_centralizer.2 h₁₂'])
    have hinf : M₁ ⊓ M₂ ≤ (center M₁).map M₁.subtype := by
      intro x hx
      refine ⟨⟨x, hx.1⟩, mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.1 (h₁₂' hx.2) g g.2
    exact false_of_normalizes_both_E6 hset hf hk e htC ht hKt h₁₂' hM₁p hM₂p hZ₁ hZ₂ e₁ e₂ hinf
      ht₁ ht₂
  ·
    have hcomm : M₁.map (MulAut.conj t).toMonoidHom ≤ centralizer (M₁ : Set G) := hc ▸ h₁₂'
    have hrange := range_swapDiagHom_eq_of_swap_E6 hset e htC ht hcomm hM₁p e₁
    have htN : t ∈ normalizer ((M₁ ⊔ M₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
      rw [hc]
      exact htM
    have hgen := le_iSup_perfectCore_of_swap_E6 hq4 e htC hcomm hM₁p hrange htN
    rw [hc] at hgen
    refine hgen.trans (iSup_le fun i => ?_)
    exact le_iSup_of_le (⟨{i}, by simp⟩ : {J : Finset (Fin (Tag.rank .E6)) // J.card ≤ 2}) le_rfl

theorem e6SwapRowUniqueInput_holds : E6SwapRowUniqueInput :=
  e6SwapRowUniqueInput_of_conjGen e6SwapConjGenInput_holds

end Input

end CFSG.SeitzReduction.E6Pilot
