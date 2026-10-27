module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem mul_comm_of_isMulCommutative {G : Type} [Group G] {H : Subgroup G} (h : IsMulCommutative ↥H)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y = y * x :=
  congrArg Subtype.val (isMulCommutative_iff.1 h ⟨x, hx⟩ ⟨y, hy⟩)

theorem exists_card_eq_pow_of_isElemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} (hE : IsElemAbelian p E) : ∃ k : ℕ, Nat.card E = p ^ k :=
  (IsPGroup.iff_card).1 (isPGroup_of_isElemAbelian hE)

theorem le_pRank_of_isElemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.Open.pRank p H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    intro m hm
    obtain ⟨E', -, -, hm'⟩ := hm
    have h1 : p ^ m ≤ Nat.card G := by
      rw [← hm']
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)) h1
  · exact ⟨E, hEH, hE, hk⟩

theorem pRank_le_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    CFSG.Open.pRank p H ≤ Nat.card G := by
  unfold CFSG.Open.pRank
  apply csSup_le
  · refine ⟨0, ⊥, bot_le, ?_, ?_⟩
    · refine ⟨isMulCommutative_iff.2 (fun a b => Subtype.ext ?_), fun x hx => ?_⟩
      · show (a : G) * b = b * a
        rw [Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2]
      · rw [Subgroup.mem_bot.1 hx, one_pow]
    · simp
  · rintro m ⟨E', -, -, hm⟩
    have h1 : p ^ m ≤ Nat.card G := by
      rw [← hm]
      exact Subgroup.card_le_card_group E'
    exact le_trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt)) h1

theorem pRank_normalizer_le_glaTwoLocalRank {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P) :
    CFSG.Open.pRank p (Subgroup.normalizer (P : Set G)) ≤ GLATwoLocalRank p G := by
  show _ ≤ CFSG.Open.twoLocalPrimeRank p G
  unfold CFSG.Open.twoLocalPrimeRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro k ⟨H, -, rfl⟩
    exact pRank_le_card hp H
  · exact ⟨Subgroup.normalizer (P : Set G), ⟨P, hP, hP2, rfl⟩, rfl⟩

theorem isElemAbelian_sup_of_commute {G : Type} [Group G] {p : ℕ} {W D : Subgroup G}
    (hW : IsElemAbelian p W) (hD : IsElemAbelian p D) (hWD : ∀ w ∈ W, ∀ d ∈ D, w * d = d * w) :
    IsElemAbelian p (W ⊔ D) := by
  have hcomm : ((W : Set G) ∪ (D : Set G)).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact mul_comm_of_isMulCommutative hW.1 hx hy
    · exact hWD x hx y hy
    · exact (hWD y hy x hx).symm
    · exact mul_comm_of_isMulCommutative hD.1 hx hy
  rw [Subgroup.sup_eq_closure]
  have hcl := Subgroup.isMulCommutative_closure hcomm
  refine ⟨hcl, ?_⟩
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hW.2 x hx
    · exact hD.2 x hx
  | one => rw [one_pow]
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := mul_comm_of_isMulCommutative hcl hx hy
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ih =>
    rw [inv_pow, ih, inv_one]

theorem card_map_of_injOn {K G' : Type} [Group K] [Group G'] (f : K →* G') {S : Subgroup K}
    (hf : Set.InjOn f S) : Nat.card (S.map f) = Nat.card S := by
  have hinj : Function.Injective (f.comp S.subtype) := by
    intro a b hab
    apply Subtype.ext
    exact hf a.2 b.2 hab
  have hrange : (⊤ : Subgroup S).map (f.comp S.subtype) = S.map f := by
    ext x
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, trivial, rfl⟩
  rw [← hrange, Subgroup.card_map_of_injective hinj, Subgroup.card_top]

theorem mem_normalizer_of_commute {G : Type} [Group G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x = x * g) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hy := h x hx
    have hxx : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [← hy]
        _ = x := by group
    rw [hxx]
    exact hx
  · intro hx
    have hy := h _ hx
    have e : g * x * g⁻¹ = g⁻¹ * (g * x * g⁻¹) * g := by
      calc g * x * g⁻¹ = g⁻¹ * (g * (g * x * g⁻¹)) := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [hy]
        _ = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hx' : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g * x * g⁻¹ := e.symm
    rw [hx']
    exact hx

theorem two_local_lift {G : Type} [Group G] [Finite G] {J D : Subgroup G} (hD : IsElemAbelian 3 D)
    (hD9 : Nat.card D = 9) (hDJ : ∀ d ∈ D, ∀ j ∈ J, d * j = j * d) {r : ℕ}
    (hw : I1430TwoLocal (PQuot 3 J) r) :
    r + 2 ≤ GLATwoLocalRank 3 G + CFSG.Open.pRank 3 (Subgroup.center (PQuot 3 J)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨U, E₀, hU, hU2, hEU, hE₀, hE₀card⟩ := hw
  set π : ↥J →* PQuot 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hπ
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    have := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥J)
    exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 this h
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.2 hπs
  obtain ⟨W, P, hW3, hWmap, hWinj, hP2, hPmap, hWP⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lift_normalizing π hk3
      (isPGroup_of_isElemAbelian hE₀) hU2 (by rw [hrange]; exact le_top)
      (by rw [hrange]; exact le_top) hEU
  have hWinj' : ∀ a ∈ W, ∀ b ∈ W, π a = π b → a = b := by
    intro a ha b hb hab
    exact congrArg Subtype.val (hWinj (show (π.comp W.subtype) ⟨a, ha⟩ = (π.comp W.subtype) ⟨b, hb⟩
      from hab))
  have hWimg : ∀ a ∈ W, π a ∈ E₀ := by
    intro a ha
    rw [← hWmap]
    exact Subgroup.mem_map_of_mem π ha
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
    intro a ha b hb
    apply hWinj' _ (W.mul_mem ha hb) _ (W.mul_mem hb ha)
    rw [map_mul, map_mul]
    exact mul_comm_of_isMulCommutative hE₀.1 (hWimg a ha) (hWimg b hb)
  have hWexp : ∀ a ∈ W, a ^ 3 = 1 := by
    intro a ha
    apply hWinj' _ (W.pow_mem ha 3) 1 W.one_mem
    rw [map_pow, map_one]
    exact hE₀.2 _ (hWimg a ha)
  have hWea : IsElemAbelian 3 W :=
    ⟨isMulCommutative_iff.2 (fun x y => Subtype.ext (hWcomm x x.2 y y.2)), fun x hx => hWexp x hx⟩
  set W' : Subgroup G := W.map J.subtype with hW'
  have hW'J : W' ≤ J := Subgroup.map_subtype_le W
  have hW'ea : IsElemAbelian 3 W' := by
    refine ⟨isMulCommutative_iff.2 (fun x y => ?_), fun x hx => ?_⟩
    · refine Subtype.ext ?_
      obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
      obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
      have hab := congrArg (fun z : ↥J => (z : G)) (hWcomm a ha b hb)
      simp only [Subgroup.coe_mul] at hab
      show (x : G) * (y : G) = (y : G) * (x : G)
      rw [← hax, ← hby]
      exact hab
    · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
      rw [← hax]
      have h3 := congrArg (fun z : ↥J => (z : G)) (hWexp a ha)
      simpa using h3
  have hW'card : Nat.card W' = 3 ^ r := by
    have h1 : Nat.card W' = Nat.card W := Subgroup.card_map_of_injective J.subtype_injective
    have h2 : Nat.card (W.map π) = Nat.card W :=
      card_map_of_injOn π (fun a ha b hb hab => hWinj' a ha b hb hab)
    rw [h1, ← h2, hWmap, hE₀card]
  set P' : Subgroup G := P.map J.subtype with hP'
  have hP'2 : IsPGroup 2 P' := hP2.map J.subtype
  have hPne : P ≠ ⊥ := by
    intro h
    apply hU
    rw [← hPmap, h, Subgroup.map_bot]
  have hP'ne : P' ≠ ⊥ := by
    intro h
    apply hPne
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp'
    have hmem : (p : G) ∈ P' := Subgroup.mem_map_of_mem J.subtype hp'
    rw [h, Subgroup.mem_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  have hWnorm : ∀ a ∈ W, ∀ p ∈ P, a * p * a⁻¹ ∈ P := by
    intro a ha p hp
    exact (Subgroup.mem_normalizer_iff.1 (hWP ha) p).1 hp
  have hW'norm : W' ≤ Subgroup.normalizer (P' : Set G) := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hx
    apply Subgroup.mem_normalizer_iff.2
    intro h
    constructor
    · intro hh
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hh
      refine Subgroup.mem_map.2 ⟨a * p * a⁻¹, hWnorm a ha p hp, ?_⟩
      rw [← hax, ← hpx]
      simp
    · intro hh
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.1 hh
      refine Subgroup.mem_map.2 ⟨a⁻¹ * p * a⁻¹⁻¹, hWnorm a⁻¹ (W.inv_mem ha) p hp, ?_⟩
      have hconj : J.subtype (a⁻¹ * p * a⁻¹⁻¹) = (J.subtype a)⁻¹ * J.subtype p * J.subtype a := by
        simp
      rw [hconj, hax, hpx]
      group
  have hDnormP : D ≤ Subgroup.normalizer (P' : Set G) := by
    intro d hd
    apply mem_normalizer_of_commute
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hx
    exact hDJ _ hd _ p.2
  have hDnormW' : D ≤ Subgroup.normalizer (W' : Set G) := by
    intro d hd
    apply mem_normalizer_of_commute
    intro x hx
    exact hDJ d hd x (hW'J hx)
  have hWD : ∀ w ∈ W', ∀ d ∈ D, w * d = d * w := fun w hw d hd => (hDJ d hd w (hW'J hw)).symm
  have hA : IsElemAbelian 3 (W' ⊔ D) := isElemAbelian_sup_of_commute hW'ea hD hWD
  have hAnorm : W' ⊔ D ≤ Subgroup.normalizer (P' : Set G) := sup_le hW'norm hDnormP
  have hcardA := card_sup_mul_card_inf_of_le_normalizer (A := W') (B := D) hDnormW'
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hA
  have hmle : m ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (P' : Set G)) :=
    le_pRank_of_isElemAbelian hp hAnorm hA hm
  have hT : IsElemAbelian 3 (W' ⊓ D) := isElemAbelian_mono hD inf_le_right
  obtain ⟨t, ht⟩ := exists_card_eq_pow_of_isElemAbelian hT
  set S : Subgroup ↥J := (W' ⊓ D).subgroupOf J with hS
  have hSmap : S.map J.subtype = W' ⊓ D := by
    rw [hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (le_trans inf_le_left hW'J)]
  have hSW : S ≤ W := by
    intro s hs
    have hs' : (s : G) ∈ W' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 hs'
    have hEq : a = s := Subtype.ext hax
    rw [← hEq]
    exact ha
  have hSc : ∀ s ∈ S, ∀ j : ↥J, s * j = j * s := by
    intro s hs j
    have hsD : (s : G) ∈ D := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hDJ _ hsD _ j.2
  have hSinj : Set.InjOn π (S : Set ↥J) := fun a ha b hb hab =>
    hWinj' a (hSW ha) b (hSW hb) hab
  have hcS : Nat.card S = 3 ^ t := by
    have hc : Nat.card (S.map J.subtype) = Nat.card S := Subgroup.card_map_of_injective J.subtype_injective
    rw [← hc, hSmap, ht]
  have hSea : IsElemAbelian 3 (S.map π) :=
    CFSG.LocalAnalysis.GLTheoremA.I106TGroup.isElemAbelian_map_of_hom (f := π)
      (isElemAbelian_mono hWea hSW)
  have hSmapc : S.map π ≤ Subgroup.center (PQuot 3 J) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨j, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, hSc s hs j]
  have hcSπ : Nat.card (S.map π) = 3 ^ t := by
    rw [card_map_of_injOn π hSinj, hcS]
  have htle : t ≤ CFSG.Open.pRank 3 (Subgroup.center (PQuot 3 J)) :=
    le_pRank_of_isElemAbelian hp hSmapc hSea hcSπ
  have h1 : 3 ^ m * 3 ^ t = 3 ^ r * 9 := by
    rw [← hm, ← ht, ← hW'card, ← hD9]
    exact hcardA
  have h2 : 3 ^ (m + t) = 3 ^ (r + 2) := by
    calc 3 ^ (m + t) = 3 ^ m * 3 ^ t := pow_add _ _ _
      _ = 3 ^ r * 9 := h1
      _ = 3 ^ (r + 2) := by rw [pow_add]; norm_num
  have hmt : m + t = r + 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
  have hfin := pRank_normalizer_le_glaTwoLocalRank hp hP'ne hP'2
  omega

end CFSG.LocalAnalysis.GLTheoremA.S8.L84
