module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import CFSG.RankThree.PartTwo.Census.LinearRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartTwo.Census

universe u v

variable {K : Type u} [Field K]

structure HermForm (σ : K →+* K) (X : Type v) [AddCommGroup X] [Module K X] where
  B : X → X → K
  add_left : ∀ u u' w, B (u + u') w = B u w + B u' w
  add_right : ∀ u w w', B u (w + w') = B u w + B u w'
  smul_left : ∀ (c : K) u w, B (c • u) w = σ c * B u w
  smul_right : ∀ (c : K) u w, B u (c • w) = c * B u w
  herm : ∀ u w, B w u = σ (B u w)

namespace HermForm

variable {σ : K →+* K} {X : Type v} [AddCommGroup X] [Module K X]

theorem zero_right (h : HermForm σ X) (u : X) : h.B u 0 = 0 := by
  have := h.smul_right (0 : K) u 0
  simpa using this

theorem zero_left (h : HermForm σ X) (w : X) : h.B 0 w = 0 := by
  have := h.smul_left (0 : K) 0 w
  simpa using this

theorem neg_right (h : HermForm σ X) (u w : X) : h.B u (-w) = -h.B u w := by
  have := h.smul_right (-1 : K) u w
  simpa using this

theorem sub_right (h : HermForm σ X) (u w w' : X) : h.B u (w - w') = h.B u w - h.B u w' := by
  rw [sub_eq_add_neg, h.add_right, h.neg_right, ← sub_eq_add_neg]

def restrict (h : HermForm σ X) (S : Submodule K X) : HermForm σ S where
  B u w := h.B (u : X) (w : X)
  add_left u u' w := h.add_left u u' w
  add_right u w w' := h.add_right u w w'
  smul_left c u w := h.smul_left c u w
  smul_right c u w := h.smul_right c u w
  herm u w := h.herm u w

end HermForm

private theorem card_le_pow_of_finrank_lt_two {r : ℕ} (σ : K →+* K)
    (hσ : ∀ c : K, c ^ r = 1 → c * σ c = 1 → c = 1)
    {X : Type v} [AddCommGroup X] [Module K X] [FiniteDimensional K X] {n : ℕ}
    (hn : finrank K X = n) (hn2 : n < 2) {h : HermForm σ X}
    (hnd : ∀ v, (∀ w, h.B v w = 0) → v = 0) (E : Subgroup (X ≃ₗ[K] X)) [Finite E]
    (hexp : ∀ g ∈ E, g ^ r = 1)
    (hpres : ∀ g ∈ E, ∀ u w, h.B (g u) (g w) = h.B u w) : Nat.card E ≤ r ^ (n / 2) := by
  interval_cases n
  · have : Subsingleton X := finrank_zero_iff.mp hn
    have hsub : Subsingleton E :=
      ⟨fun a b => Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)⟩
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [h1]; simp
  ·
    have hpos : 0 < finrank K X := by omega
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hall := (finrank_eq_one_iff_of_nonzero' v hv).mp hn
    have hBvv : h.B v v ≠ 0 := by
      intro h0
      apply hv
      apply hnd
      intro w
      obtain ⟨c, rfl⟩ := hall w
      rw [h.smul_right, h0, mul_zero]
    have htriv : ∀ g : E, g = 1 := by
      intro g
      obtain ⟨c, hc⟩ := hall ((g : X ≃ₗ[K] X) v)
      have hgv : (g : X ≃ₗ[K] X) v = c • v := hc.symm
      have h1 := hpres g g.2 v v
      rw [hgv, h.smul_left, h.smul_right] at h1
      have h2 : σ c * c = 1 := by
        have : (σ c * c) * h.B v v = 1 * h.B v v := by rw [one_mul]; linear_combination h1
        exact mul_right_cancel₀ hBvv this
      have hpow : ∀ i : ℕ, ((g : X ≃ₗ[K] X) ^ i) v = (c ^ i) • v := by
        intro i
        induction i with
        | zero => simp
        | succ i ih =>
          rw [pow_succ, LinearEquiv.mul_apply, hgv, map_smul, ih, smul_smul, pow_succ']
      have h3 : c ^ r = 1 := by
        have hgr : ((g : X ≃ₗ[K] X) ^ r) v = v := by
          rw [hexp g g.2]; rfl
        have h4 := hpow r
        rw [hgr] at h4
        have h5 : (c ^ r) • v = (1 : K) • v := by rw [one_smul]; exact h4.symm
        exact smul_left_injective K hv h5
      have hc1 : c = 1 := hσ c h3 (by rw [mul_comm]; exact h2)
      apply Subtype.ext
      apply LinearEquiv.ext
      intro y
      obtain ⟨a, rfl⟩ := hall y
      change (g : X ≃ₗ[K] X) (a • v) = a • v
      rw [map_smul, hgv, hc1, one_smul]
    have hsub : Subsingleton E := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    have h1 : Nat.card E = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [h1]; simp

private theorem fixedSpace_orthogonal_commSpace {σ : K →+* K} {X : Type v} [AddCommGroup X]
    [Module K X] {h : HermForm σ X} {x : X ≃ₗ[K] X} (hpres : ∀ u w, h.B (x u) (x w) = h.B u w) :
    (∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, h.B u w = 0) ∧
      (∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, h.B w u = 0) := by
  have hUW : ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, h.B u w = 0 := by
    intro u hu w hw
    obtain ⟨y, rfl⟩ := mem_commSpace.mp hw
    have h1 := hpres u y
    rw [mem_fixedSpace.mp hu] at h1
    rw [h.sub_right, h1, sub_self]
  refine ⟨hUW, fun w hw u hu => ?_⟩
  rw [h.herm u w, hUW u hu w hw, map_zero]

private theorem restrict_fixedSpace_nondegenerate {σ : K →+* K} {X : Type v}
    [AddCommGroup X] [Module K X] {h : HermForm σ X} {x : X ≃ₗ[K] X}
    (hnd : ∀ v, (∀ w, h.B v w = 0) → v = 0)
    (hc : IsCompl (fixedSpace x) (commSpace x))
    (hUW : ∀ u ∈ fixedSpace x, ∀ w ∈ commSpace x, h.B u w = 0) :
    ∀ u : fixedSpace x, (∀ u' : fixedSpace x, h.B (u : X) (u' : X) = 0) → u = 0 := by
  intro u hu
  apply Subtype.ext
  apply hnd
  intro y
  have hy : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hy
  rw [h.add_right, hUW u u.2 w₁ hw₁, add_zero]
  exact hu ⟨u₁, hu₁⟩

private theorem restrict_commSpace_nondegenerate {σ : K →+* K} {X : Type v}
    [AddCommGroup X] [Module K X] {h : HermForm σ X} {x : X ≃ₗ[K] X}
    (hnd : ∀ v, (∀ w, h.B v w = 0) → v = 0)
    (hc : IsCompl (fixedSpace x) (commSpace x))
    (hWU : ∀ w ∈ commSpace x, ∀ u ∈ fixedSpace x, h.B w u = 0) :
    ∀ w : commSpace x, (∀ w' : commSpace x, h.B (w : X) (w' : X) = 0) → w = 0 := by
  intro w hw
  apply Subtype.ext
  apply hnd
  intro y
  have hy : y ∈ fixedSpace x ⊔ commSpace x := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hy
  rw [h.add_right, hWU w w.2 u₁ hu₁, zero_add]
  exact hw ⟨w₁, hw₁⟩

private theorem card_le_mul_card_restrictRange {X : Type v} [AddCommGroup X] [Module K X]
    {x : X ≃ₗ[K] X} (hc : IsCompl (fixedSpace x) (commSpace x))
    (E : Subgroup (X ≃ₗ[K] X)) [Finite E]
    (hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x)
    (hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x) :
    Nat.card E ≤
      Nat.card (restrictAction E.subtype (fixedSpace x) hUinv).range *
        Nat.card (restrictAction E.subtype (commSpace x) hWinv).range := by
  let ρ : E →* (X ≃ₗ[K] X) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
  let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
  have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
  have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
  have hinj : Function.Injective
      (fun g : E => ((⟨ρU g, g, rfl⟩ : EU), (⟨ρW g, g, rfl⟩ : EW))) := by
    intro g k hgk
    simp only [Prod.mk.injEq] at hgk
    obtain ⟨h1, h2⟩ := hgk
    have h1' : ρU g = ρU k := congrArg Subtype.val h1
    have h2' : ρW g = ρW k := congrArg Subtype.val h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : X ≃ₗ[K] X).toLinearMap = (k : X ≃ₗ[K] X).toLinearMap := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          ((congrArg Subtype.val (LinearEquiv.congr_fun h1' ⟨u, hu⟩)).trans
            (restrictAction_apply ρ (fixedSpace x) hUinv k ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          ((congrArg Subtype.val (LinearEquiv.congr_fun h2' ⟨w, hw⟩)).trans
            (restrictAction_apply ρ (commSpace x) hWinv k ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  calc Nat.card E ≤ Nat.card EU * Nat.card EW := by
        rw [← Nat.card_prod]
        exact Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (restrictAction E.subtype (fixedSpace x) hUinv).range *
        Nat.card (restrictAction E.subtype (commSpace x) hWinv).range := rfl

private theorem commSpace_ne_bot_of_ne_one {X : Type v} [AddCommGroup X] [Module K X]
    {x : X ≃ₗ[K] X} (hx1 : x ≠ 1) : commSpace x ≠ ⊥ := by
  intro hbot
  apply hx1
  apply LinearEquiv.ext
  intro y
  have hy : x y - y ∈ commSpace x := mem_commSpace.mpr ⟨y, rfl⟩
  have h2 : x y - y = 0 := (Submodule.eq_bot_iff _).1 hbot (x y - y) hy
  simpa [sub_eq_zero] using h2

theorem card_le_pow_half_of_herm {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0) (σ : K →+* K)
    (hσ : ∀ c : K, c ^ r = 1 → c * σ c = 1 → c = 1) :
    ∀ (n : ℕ) (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X],
      finrank K X = n → ∀ (h : HermForm σ X), (∀ v, (∀ w, h.B v w = 0) → v = 0) →
      ∀ (E : Subgroup (X ≃ₗ[K] X)) [Finite E],
      (∀ g ∈ E, ∀ k ∈ E, g * k = k * g) → (∀ g ∈ E, g ^ r = 1) →
      (∀ g ∈ E, ∀ u w, h.B (g u) (g w) = h.B u w) → Nat.card E ≤ r ^ (n / 2) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ _ hn h hnd E _ hcomm hexp hpres
  have hexpE : ∀ a : E, a ^ r = 1 := fun a => Subtype.ext (hexp a a.2)
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_exponent hr hexpE
  have hr2 : 2 ≤ r := hr.two_le
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · exact card_le_pow_of_finrank_lt_two σ hσ hn hn2 hnd E hexp hpres
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hle : Nat.card E ≤ r := by
      rw [hk]
      calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos (by omega)
        _ = r := pow_one r
    calc Nat.card E ≤ r := hle
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)
  ·
    have hbig : r ^ 2 ≤ Nat.card E := by
      rw [hk]; exact Nat.pow_le_pow_right hr.pos hk2
    obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hbig
    have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
    have hsum := Submodule.finrank_add_eq_of_isCompl hc
    have hUpos : 0 < finrank K (fixedSpace x) := by
      apply Module.finrank_pos_iff_exists_ne_zero.mpr
      exact ⟨⟨v, mem_fixedSpace.mpr hxv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
    have hWpos : 0 < finrank K (commSpace x) := by
      by_contra h
      have h0 : commSpace x = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro w hw
        by_contra hw0
        exact h (Module.finrank_pos_iff_exists_ne_zero.mpr
          ⟨⟨w, hw⟩, fun h0 => hw0 (congrArg Subtype.val h0)⟩)
      exact commSpace_ne_bot_of_ne_one hx1 h0
    have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
    have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
      fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
    have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
      fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
    obtain ⟨hUW, hWU⟩ := fixedSpace_orthogonal_commSpace (hpres := fun u w => hpres x hxE u w)
    have hBU := restrict_fixedSpace_nondegenerate hnd hc hUW
    have hBW := restrict_commSpace_nondegenerate hnd hc hWU
    let ρ : E →* (X ≃ₗ[K] X) := E.subtype
    let ρU := restrictAction ρ (fixedSpace x) hUinv
    let ρW := restrictAction ρ (commSpace x) hWinv
    let BU : HermForm σ (fixedSpace x) := h.restrict (fixedSpace x)
    let BW : HermForm σ (commSpace x) := h.restrict (commSpace x)
    let EU : Subgroup (fixedSpace x ≃ₗ[K] fixedSpace x) := ρU.range
    let EW : Subgroup (commSpace x ≃ₗ[K] commSpace x) := ρW.range
    have : Finite EU := Finite.of_surjective ρU.rangeRestrict ρU.rangeRestrict_surjective
    have : Finite EW := Finite.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective
    have hcommU : ∀ g ∈ EU, ∀ k ∈ EU, g * k = k * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρU (Subtype.ext (hcomm a a.2 b b.2))
    have hcommW : ∀ g ∈ EW, ∀ k ∈ EW, g * k = k * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ρW (Subtype.ext (hcomm a a.2 b b.2))
    have hexpU : ∀ g ∈ EU, g ^ r = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hexpW : ∀ g ∈ EW, g ^ r = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_pow, hexpE a, map_one]
    have hpresU : ∀ g ∈ EU, ∀ u w, BU.B (g u) (g w) = BU.B u w := by
      rintro _ ⟨a, rfl⟩ u w
      exact hpres a a.2 u w
    have hpresW : ∀ g ∈ EW, ∀ u w, BW.B (g u) (g w) = BW.B u w := by
      rintro _ ⟨a, rfl⟩ u w
      exact hpres a a.2 u w
    have hIU := ih (finrank K (fixedSpace x)) (by omega) (fixedSpace x) rfl BU hBU EU
      hcommU hexpU hpresU
    have hIW := ih (finrank K (commSpace x)) (by omega) (commSpace x) rfl BW hBW EW
      hcommW hexpW hpresW
    have hle := card_le_mul_card_restrictRange hc E hUinv hWinv
    calc Nat.card E ≤ Nat.card EU * Nat.card EW := hle
      _ ≤ r ^ (finrank K (fixedSpace x) / 2) * r ^ (finrank K (commSpace x) / 2) :=
        Nat.mul_le_mul hIU hIW
      _ = r ^ (finrank K (fixedSpace x) / 2 + finrank K (commSpace x) / 2) :=
        (pow_add _ _ _).symm
      _ ≤ r ^ (n / 2) := Nat.pow_le_pow_right hr.pos (by omega)

end CFSG.LocalAnalysis.GLTheoremA
