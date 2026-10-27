module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigNorm
public import CFSG.GH74.GLS.TwoThin.Orbit
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ComponentClassification.GSThmB.HConfig

open CFSG Subgroup LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G]

theorem fixed_coord_mem {X Y : Subgroup G} (hXY : ⁅X, Y⁆ = ⊥) {b : G}
    (hX : b ∈ normalizer (X : Set G)) (hY : b ∈ normalizer (Y : Set G)) {x y : G} (hx : x ∈ X)
    (hy : y ∈ Y) (hfix : b * (x * y) * b⁻¹ = x * y) : x⁻¹ * (b * x * b⁻¹) ∈ X ⊓ Y := by
  have hxb : b * x * b⁻¹ ∈ X := (mem_normalizer_iff.mp hX x).mp hx
  have hyb : b * y * b⁻¹ ∈ Y := (mem_normalizer_iff.mp hY y).mp hy
  have h1 : (b * x * b⁻¹) * (b * y * b⁻¹) = x * y := by rw [← hfix]; group
  have h2 : x⁻¹ * (b * x * b⁻¹) = y * (b * y * b⁻¹)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, h1, inv_mul_cancel_left]
  refine mem_inf.mpr ⟨mul_mem (inv_mem hx) hxb, ?_⟩
  rw [h2]
  exact mul_mem hy (inv_mem hyb)

theorem conj_commutator_eq_of_fixed {X Y : Subgroup G} (hXY : ⁅X, Y⁆ = ⊥) {b : G}
    (hX : b ∈ normalizer (X : Set G)) (hY : b ∈ normalizer (Y : Set G)) {x y x' y' : G}
    (hx : x ∈ X) (hy : y ∈ Y) (hx' : x' ∈ X) (hy' : y' ∈ Y)
    (hfix : b * (x * y) * b⁻¹ = x * y) (hfix' : b * (x' * y') * b⁻¹ = x' * y') :
    b * ⁅x, x'⁆ * b⁻¹ = ⁅x, x'⁆ := by
  have hc := fixed_coord_mem hXY hX hY hx hy hfix
  have hc' := fixed_coord_mem hXY hX hY hx' hy' hfix'
  set c := x⁻¹ * (b * x * b⁻¹)
  set c' := x'⁻¹ * (b * x' * b⁻¹)
  have hcomm : ∀ {u v : G}, u ∈ X → v ∈ Y → Commute u v := fun hu hv =>
    commute_of_commutator_eq_bot hXY hu hv
  have e1 : b * x * b⁻¹ = x * c := by rw [mul_inv_cancel_left]
  have e2 : b * x' * b⁻¹ = x' * c' := by rw [mul_inv_cancel_left]
  have e3 : b * ⁅x, x'⁆ * b⁻¹ = ⁅b * x * b⁻¹, b * x' * b⁻¹⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e3, e1, e2, commutatorElement_mul_mul_eq_mul (hcomm hx (mem_inf.mp hc).2)
    (hcomm hx (mem_inf.mp hc').2) (hcomm hx' (mem_inf.mp hc).2) (hcomm hx' (mem_inf.mp hc').2),
    commutatorElement_eq_one_iff_mul_comm.mpr (hcomm (mem_inf.mp hc).1 (mem_inf.mp hc').2).eq,
    mul_one]

theorem commutator_fixed_sup_le {X Y B : Subgroup G} (hXY : ⁅X, Y⁆ = ⊥)
    (hX : B ≤ normalizer (X : Set G)) (hY : B ≤ normalizer (Y : Set G)) :
    ⁅(X ⊔ Y) ⊓ centralizer (B : Set G), (X ⊔ Y) ⊓ centralizer (B : Set G)⁆ ≤
      (X ⊓ centralizer (B : Set G)) ⊔ (Y ⊓ centralizer (B : Set G)) := by
  have hcomm : ∀ {u v : G}, u ∈ X → v ∈ Y → Commute u v := fun hu hv =>
    commute_of_commutator_eq_bot hXY hu hv
  have hYX : ⁅Y, X⁆ = ⊥ := by rw [commutator_comm]; exact hXY
  rw [commutator_le]
  intro u hu v hv
  obtain ⟨hu1, hu2⟩ := mem_inf.mp hu
  obtain ⟨hv1, hv2⟩ := mem_inf.mp hv
  rw [← SetLike.mem_coe, coe_sup_of_commutator_eq_bot hXY] at hu1 hv1
  obtain ⟨x, hx, y, hy, rfl⟩ := hu1
  obtain ⟨x', hx', y', hy', rfl⟩ := hv1
  have hfix : ∀ {w : G}, w ∈ centralizer (B : Set G) → ∀ b ∈ B, b * w * b⁻¹ = w := by
    intro w hw b hb
    rw [mem_centralizer_iff.mp hw b hb, mul_inv_cancel_right]
  rw [commutatorElement_mul_mul_eq_mul (hcomm hx hy) (hcomm hx hy') (hcomm hx' hy)
    (hcomm hx' hy')]
  have hcm : ∀ {w : G}, (∀ b ∈ B, b * w * b⁻¹ = w) → w ∈ centralizer (B : Set G) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro b hb
    exact (mul_inv_eq_iff_eq_mul.mp (hw b hb))
  have hyx : ∀ {x₀ y₀ : G}, x₀ ∈ X → y₀ ∈ Y → y₀ * x₀ = x₀ * y₀ := fun h1 h2 =>
    (hcomm h1 h2).eq.symm
  refine mul_mem (mem_sup_left (mem_inf.mpr ⟨?_, hcm fun b hb => ?_⟩))
    (mem_sup_right (mem_inf.mpr ⟨?_, hcm fun b hb => ?_⟩))
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hx') (inv_mem hx)) (inv_mem hx')
  · exact conj_commutator_eq_of_fixed hXY (hX hb) (hY hb) hx hy hx' hy' (hfix hu2 b hb)
      (hfix hv2 b hb)
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  · refine conj_commutator_eq_of_fixed hYX (hY hb) (hX hb) hy hx hy' hx' ?_ ?_
    · rw [hyx hx hy]
      exact hfix hu2 b hb
    · rw [hyx hx' hy']
      exact hfix hv2 b hb

theorem le_or_le_of_isPComponent_centralizer [Finite G] {X Y E P : Subgroup G}
    (hXY : ⁅X, Y⁆ = ⊥) (hX : E ≤ normalizer (X : Set G)) (hY : E ≤ normalizer (Y : Set G))
    (hPC : P ≤ centralizer (E : Set G))
    (hP' : IsPComponent 2 (P.subgroupOf (centralizer (E : Set G)))) (hPXY : P ≤ X ⊔ Y) :
    P ≤ X ∨ P ≤ Y := by
  have hP := (CatalogueBAlternating.pComponent_two_iff _).mp hP'
  classical
  set C := centralizer (E : Set G) with hCdef
  set A := X ⊓ C with hAdef
  set B := Y ⊓ C with hBdef
  set D := A ⊔ B with hDdef
  have hperf : ⁅P, P⁆ = P := GH74.GLS.TwoThin.commutator_self_of_isTwoComponent hPC hP
  have hPD : P ≤ D := by
    rw [← hperf]
    exact (commutator_mono (le_inf hPXY hPC) (le_inf hPXY hPC)).trans
      (commutator_fixed_sup_le hXY hX hY)
  have hDC : D ≤ C := sup_le inf_le_right inf_le_right
  have hABC : ⁅A, B⁆ = ⊥ := eq_bot_iff.2 (hXY ▸ commutator_mono inf_le_left inf_le_left)
  have hnormA : D ≤ normalizer (A : Set G) :=
    sup_le le_normalizer ((commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact hABC)).trans (centralizer_le_normalizer _))
  have hnormB : D ≤ normalizer (B : Set G) :=
    sup_le ((commutator_eq_bot_iff_le_centralizer.1 hABC).trans (centralizer_le_normalizer _))
      le_normalizer
  have hPD' : TwoComponents.IsTwoComponent (P.subgroupOf D) :=
    TwoComponentTransport.restrict_nested P D C hPD hDC hP
  have hAn : (A.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hnormA
  have hBn : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hnormB
  have hsubn : ∀ N : Subgroup ↥D, N.Normal → CFSG.Open.IsSubnormal N ⊤ := fun N hN =>
    Components.chain_of_mathlib_subnormal
      (Subgroup.IsSubnormal.step N ⊤ le_top Subgroup.IsSubnormal.top inferInstance)
  have hle : ∀ N : Subgroup G, P.subgroupOf D ≤ N.subgroupOf D → P ≤ N := fun N h j hj =>
    Subgroup.mem_subgroupOf.1
      (h (Subgroup.mem_subgroupOf.2 hj : (⟨j, hPD hj⟩ : D) ∈ P.subgroupOf D))
  rcases TwoComponentSubnormal.contains_or_normalizes_core (P.subgroupOf D) (A.subgroupOf D) hPD'
      (hsubn _ hAn) with h1 | ⟨h1n, h1c⟩
  · exact Or.inl ((hle A h1).trans inf_le_left)
  rcases TwoComponentSubnormal.contains_or_normalizes_core (P.subgroupOf D) (B.subgroupOf D) hPD'
      (hsubn _ hBn) with h2 | ⟨h2n, h2c⟩
  · exact Or.inr ((hle B h2).trans inf_le_left)
  exfalso
  set P' : Subgroup ↥D := P.subgroupOf D with hP'def
  set R : Subgroup ↥D := (CFSG.Open.componentClassificationOddCore ↥P').map P'.subtype with hRdef
  have hdecomp : ∀ q : ↥D, ∃ a ∈ A, ∃ b ∈ B, a * b = (q : G) := by
    intro q
    have hq : (q : G) ∈ ((A ⊔ B : Subgroup G) : Set G) := q.2
    rw [coe_sup_of_commutator_eq_bot hABC] at hq
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hq
    exact ⟨a, ha, b, hb, hab⟩
  have hAD : A ≤ D := le_sup_left
  have hBD : B ≤ D := le_sup_right
  have hPnorm : P'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine top_unique fun q _ => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp q
    have hq : q = (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩ := Subtype.ext hab.symm
    rw [hq]
    exact Subgroup.mul_mem _ (h1n (Subgroup.mem_subgroupOf.2 ha))
      (h2n (Subgroup.mem_subgroupOf.2 hb))
  have hRn : R.Normal := by
    have : (pPrimeCore 2 ↥P').Characteristic := inferInstance
    have h := (CatalogueBAlternating.primeCore_two_eq_oddCore ↥P')
    rw [hRdef, ← h]
    exact ConjAct.normal_of_characteristic_of_normal
  have hPR : P' ≤ R := by
    have hperf' : ⁅P', P'⁆ = P' := GH74.GLS.TwoThin.commutator_self_of_isTwoComponent' hPD'
    rw [← hperf', Subgroup.commutator_le]
    intro p hp q hq
    obtain ⟨a, ha, b, hb, hab⟩ := hdecomp q
    have hq' : q = (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩ := Subtype.ext hab.symm
    have hpa : ⁅p, (⟨a, hAD ha⟩ : ↥D)⁆ ∈ R :=
      h1c (Subgroup.commutator_mem_commutator hp (Subgroup.mem_subgroupOf.2 ha))
    have hpb : ⁅p, (⟨b, hBD hb⟩ : ↥D)⁆ ∈ R :=
      h2c (Subgroup.commutator_mem_commutator hp (Subgroup.mem_subgroupOf.2 hb))
    have hid : ⁅p, (⟨a, hAD ha⟩ : ↥D) * ⟨b, hBD hb⟩⁆ =
        ⁅p, (⟨a, hAD ha⟩ : ↥D)⁆ * ((⟨a, hAD ha⟩ : ↥D) * ⁅p, (⟨b, hBD hb⟩ : ↥D)⁆ *
          (⟨a, hAD ha⟩ : ↥D)⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hq', hid]
    exact R.mul_mem hpa (hRn.conj_mem _ hpb _)
  have hRodd : Odd (Nat.card R) := by
    rw [hRdef, Subgroup.card_map_of_injective P'.subtype_injective]
    exact OddCore.odd_card ↥P'
  have hP'odd : Odd (Nat.card P') := Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le hPR)
  have hsolv : Group.IsSolvable ↥P' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hP'odd
  have hnt := TwoComponents.nontrivial hPD'
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥P'
  rw [TwoComponents.perfect hPD'] at h1
  exact lt_irrefl _ h1

theorem mem_normalizer_of_cj_le {g : G} {H : Subgroup G} (h1 : cj g H ≤ H)
    (h2 : cj g⁻¹ H ≤ H) : g ∈ normalizer (H : Set G) := by
  rw [← cj_eq_self_iff]
  refine le_antisymm h1 ?_
  rw [← cj_le_cj_iff (g := g⁻¹), ← cj_mul, inv_mul_cancel, cj_one]
  exact h2

theorem le_normalizer_orbJoin (B K : Subgroup G) : B ≤ normalizer (orbJoin B K : Set G) := by
  have key : ∀ c ∈ B, cj c (orbJoin B K) ≤ orbJoin B K := by
    intro c hc
    rw [Subgroup.map_le_iff_le_comap]
    unfold orbJoin
    refine iSup₂_le fun b hb => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    change cj c (cj b K) ≤ _
    rw [← cj_mul]
    exact cj_le_orbJoin (mul_mem hc hb)
  exact fun c hc => mem_normalizer_of_cj_le (key c hc) (key c⁻¹ (inv_mem hc))

theorem exists_component_orbit [Finite G] {B N : Subgroup G}
    (hNC : N ≤ centralizer (B : Set G))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer (B : Set G)))) (hNE : N ≤ layer G) :
    ∃ K : Subgroup G, IsComponent K ∧ ⁅K, N⁆ ≠ ⊥ ∧ N ≤ orbJoin B K := by
  have hN2 := (CatalogueBAlternating.pComponent_two_iff _).mp hN
  have hperf : ⁅N, N⁆ = N := GH74.GLS.TwoThin.commutator_self_of_isTwoComponent hNC hN2
  have hne : N ≠ ⊥ := GH74.GLS.TwoThin.ne_bot_of_isTwoComponent hN2
  obtain ⟨K, hK, hKN⟩ : ∃ K : Subgroup G, IsComponent K ∧ ⁅K, N⁆ ≠ ⊥ := by
    by_contra h
    push Not at h
    have hlay : layer G ≤ centralizer (N : Set G) := by
      rw [layer.eq_sSup]
      exact sSup_le fun L hL => commutator_eq_bot_iff_le_centralizer.mp (h L hL)
    have h1 : ⁅N, N⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (hNE.trans hlay)
    exact hne (hperf ▸ h1)
  refine ⟨K, hK, hKN, ?_⟩
  set Y : Subgroup G := sSup {L : Subgroup G | IsComponent L ∧ ∀ b ∈ B, L ≠ cj b K} with hYdef
  have hXY : ⁅orbJoin B K, Y⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    unfold orbJoin
    refine iSup₂_le fun b _ => ?_
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm,
      commutator_eq_bot_iff_le_centralizer]
    refine sSup_le fun L hL => ?_
    rw [← commutator_eq_bot_iff_le_centralizer]
    exact (LocalCores.distinct_components_commute hL.1 (isComponent_cj hK b)).resolve_left
      (hL.2 b ‹_›)
  have hlay : layer G ≤ orbJoin B K ⊔ Y := by
    rw [layer.eq_sSup]
    refine sSup_le fun L hL => ?_
    by_cases h : ∃ b ∈ B, L = cj b K
    · obtain ⟨b, hb, rfl⟩ := h
      exact (cj_le_orbJoin hb).trans le_sup_left
    · push Not at h
      have hmem : L ∈ {L : Subgroup G | IsComponent L ∧ ∀ b ∈ B, L ≠ cj b K} := ⟨hL, h⟩
      exact (le_sSup hmem).trans le_sup_right
  have hBY : B ≤ normalizer (Y : Set G) := by
    have key : ∀ c ∈ B, cj c Y ≤ Y := by
      intro c hc
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun L hL => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      refine le_sSup ⟨isComponent_cj hL.1 c, fun b hb h => hL.2 (c⁻¹ * b) (mul_mem (inv_mem hc) hb)
        ?_⟩
      change cj c L = cj b K at h
      calc L = cj c⁻¹ (cj c L) := by rw [← cj_mul, inv_mul_cancel, cj_one]
        _ = cj (c⁻¹ * b) K := by rw [h, cj_mul]
    exact fun c hc => mem_normalizer_of_cj_le (key c hc) (key c⁻¹ (inv_mem hc))
  rcases le_or_le_of_isPComponent_centralizer hXY (le_normalizer_orbJoin B K) hBY hNC hN
      (hNE.trans hlay) with h | h
  · exact h
  · exact absurd (eq_bot_iff.mpr ((commutator_mono (le_orbJoin B K) h).trans hXY.le)) hKN

end CFSG.ComponentClassification.GSThmB.HConfig
