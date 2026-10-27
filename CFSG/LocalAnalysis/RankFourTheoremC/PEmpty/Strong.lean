module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fusion

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (SmallRankSylowTwo)

@[expose] def Prop614At {G : Type} [Group G] (M : Subgroup G) (x z : G) : Prop :=
  ∀ H : Subgroup G, IsTwoLocal H → zpowers x ⊔ zpowers z ≤ H →
    (∃ S : Subgroup G, S ≤ H ⊓ M ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧
      zpowers x ⊔ zpowers z ≤ normalizer (S : Set G)) → H ≤ M

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem le_of_inf_ne_bot (h614 : Prop614At M x z) (hBM : zpowers x ⊔ zpowers z ≤ M)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hBS : zpowers x ⊔ zpowers z ≤ normalizer (S : Set G))
    (hSM : S ⊓ M ≠ ⊥) : S ≤ M := by
  have hS1 : S ≠ ⊥ := fun h => hSM (by rw [h]; exact bot_inf_eq _)
  have hH : IsTwoLocal (normalizer (S : Set G)) := ⟨S, hS1, hS2, rfl⟩
  refine le_normalizer.trans (h614 _ hH hBS ⟨S ⊓ M, ?_, hSM, hS2.to_le inf_le_left, ?_⟩)
  · exact inf_le_inf le_normalizer le_rfl
  · exact (le_inf hBS (hBM.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf

theorem exists_sylowTwo (hS : Situation G p P M) : ∃ T : Subgroup G, SmallRankSylowTwo P M T := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hMO, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  obtain ⟨S, hSn⟩ := CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow p 2
    hprime Nat.prime_two (P : Subgroup G) (rankThreePrimeCore p M)
    P.isPGroup' (hS.sylow_le.trans hMO) hcop
  refine ⟨(S : Subgroup (rankThreePrimeCore p M)).map
    (rankThreePrimeCore p M).subtype,
    map_subtype_le _, S.isPGroup'.map _, ?_, hSn⟩
  rw [Subgroup.subgroupOf,
    comap_map_eq_self_of_injective (rankThreePrimeCore p M).subtype_injective]
  exact S.not_dvd_index

omit [Finite G] in
private theorem orderOf_conj_eq (a y : G) : orderOf (a * y * a⁻¹) = orderOf y := by
  simpa [MulAut.conj_apply] using
    orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective y

theorem exists_point (hS : Situation G p P M) (hns : ¬ GLBStronglyEmbedded p M) :
    ∃ x : G, Point P M x := by
  classical
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI := hS.simple
  have hPM := hS.sylow_le
  have hMtop : M ≠ ⊤ :=
    CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top hS.nonab hS.loc.maxLocal.1
  have hpM : p ∣ Nat.card M :=
    (dvd_card_of_one_le_pRank hprime (by have := hS.four_le_pRank; omega)).trans
      (Subgroup.card_dvd_of_le hPM)
  obtain ⟨g, hgM, hdvd⟩ : ∃ g : G, g ∉ M ∧ p ∣ Nat.card (M ⊓ GLBConj g M : Subgroup G) := by
    by_contra h
    push Not at h
    exact hns ⟨hMtop, hpM, fun g hg => h g hg⟩
  obtain ⟨y₀', hy₀'⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set y₀ : G := (y₀' : G) with hy₀def
  have hy₀ord : orderOf y₀ = p := by rw [hy₀def, Subgroup.orderOf_coe]; exact hy₀'
  have hy₀M : y₀ ∈ M := (Subgroup.mem_inf.mp y₀'.2).1
  have hgy₀ : g * y₀ * g⁻¹ ∈ M := by
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp y₀'.2).2
    have : g * y₀ * g⁻¹ = m := by
      rw [← hy₀def] at hmy
      rw [← hmy]
      simp [MulAut.conj_apply, mul_assoc]
    rwa [this]
  have hy₀p : IsPGroup p (zpowers y₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy₀ord, pow_one])
  obtain ⟨m, hm⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM (zpowers y₀)
    hy₀p (zpowers_le.mpr hy₀M)
  set y : G := (m : G) * y₀ * (m : G)⁻¹ with hydef
  have hyP : y ∈ (P : Subgroup G) := hm ⟨y₀, mem_zpowers y₀, rfl⟩
  have hyord : orderOf y = p := by rw [hydef, orderOf_conj_eq, hy₀ord]
  set g' : G := g * (m : G)⁻¹ with hg'def
  have hg'M : g' ∉ M := fun h => hgM (by
    have := M.mul_mem h m.2
    simpa [hg'def] using this)
  have hg'y : g' * y * g'⁻¹ ∈ M := by
    have : g' * y * g'⁻¹ = g * y₀ * g⁻¹ := by simp only [hg'def, hydef]; group
    rw [this]
    exact hgy₀
  have hCy : ¬ centralizer ({y} : Set G) ≤ M := by
    intro hC
    have hzp : IsPGroup p (zpowers (g' * y * g'⁻¹)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_conj_eq, hyord, pow_one])
    obtain ⟨m₂, hm₂⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P M hPM _ hzp
      (zpowers_le.mpr hg'y)
    set h : G := (m₂ : G) * g' with hhdef
    have hhM : h ∉ M := fun hh => hg'M (by
      have := M.mul_mem (M.inv_mem m₂.2) hh
      simpa [hhdef] using this)
    have hz'P : h * y * h⁻¹ ∈ (P : Subgroup G) := by
      have := hm₂ ⟨g' * y * g'⁻¹, mem_zpowers _, rfl⟩
      have e : (m₂ : G) * (g' * y * g'⁻¹) * (m₂ : G)⁻¹ = h * y * h⁻¹ := by
        simp only [hhdef]; group
      simpa [MulAut.conj_apply, e] using this
    have hmap : (zpowers y).map (MulAut.conj (h⁻¹)⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [← conj_zpow]
      exact zpow_mem hz'P k
    obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS (zpowers_le.mpr hyP) hmap
    have hc1 : c⁻¹ * y * c = h * y * h⁻¹ := by
      simpa using hc y (mem_zpowers y)
    have hd : c * h ∈ centralizer ({y} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c * h * y = c * (h * y * h⁻¹) * h := by group
        _ = c * (c⁻¹ * y * c) * h := by rw [hc1]
        _ = y * (c * h) := by group
    exact hhM (by
      have := M.mul_mem (M.inv_mem hcM) (hC hd)
      simpa using this)
  set C : Subgroup G := centralizer ({y} : Set G) with hCdef
  have hyC : y ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hyp' : IsPGroup p ↥((zpowers y).subgroupOf C) :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyord, pow_one]) :
      IsPGroup p (zpowers y)).of_equiv (subgroupOfEquivOfLe (zpowers_le.mpr hyC)).symm
  obtain ⟨R₀, hR₀⟩ := hyp'.exists_le_sylow
  set R : Subgroup G := (R₀ : Subgroup C).map C.subtype with hRdef
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf p R C := ⟨R₀, rfl⟩
  have hyR : y ∈ R :=
    ⟨⟨y, hyC⟩, hR₀ (show (⟨y, hyC⟩ : C) ∈ (zpowers y).subgroupOf C from mem_zpowers y), rfl⟩
  obtain ⟨k, hk⟩ := pGroup_conjugate_into_sylow_within_overgroup p hprime P ⊤ le_top R
    hRsyl.isPGroup le_top
  set k₀ : G := (k : G) with hk₀def
  set x : G := k₀ * y * k₀⁻¹ with hxdef
  have hxP : x ∈ (P : Subgroup G) := hk ⟨y, hyR, rfl⟩
  have hxord : orderOf x = p := by rw [hxdef, orderOf_conj_eq, hyord]
  have hR'syl : CFSG.ABGLocalTools.IsSylowOf p (R.map (MulAut.conj k₀).toMonoidHom)
      (centralizer ({x} : Set G)) := by
    rw [hxdef, centralizer_conj_eq k₀ y]
    exact isSylowOf_map_conj hRsyl k₀
  have hPCx : (P : Subgroup G) ⊓ centralizer ({x} : Set G) =
      R.map (MulAut.conj k₀).toMonoidHom :=
    hR'syl.eq_of_le (le_inf hk hR'syl.le) inf_le_right (P.isPGroup'.to_inf_left)
  refine ⟨x, hxP, hxord, ?_, by rw [hPCx]; exact hR'syl⟩
  intro hCx
  have hmap : (zpowers y).map (MulAut.conj (k₀⁻¹)⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← conj_zpow]
    exact zpow_mem hxP j
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS (zpowers_le.mpr hyP) hmap
  have hc1 : c⁻¹ * y * c = x := by simpa using hc y (mem_zpowers y)
  refine hCy fun w hw => ?_
  have hw' : c⁻¹ * w * c ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hwy : w * y = y * w := mem_centralizer_singleton_iff.mp hw
    calc c⁻¹ * w * c * x = c⁻¹ * (w * y) * c := by rw [← hc1]; group
      _ = c⁻¹ * (y * w) * c := by rw [hwy]
      _ = x * (c⁻¹ * w * c) := by rw [← hc1]; group
  have := M.mul_mem (M.mul_mem hcM (hCx hw')) (M.inv_mem hcM)
  simpa [mul_assoc] using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
