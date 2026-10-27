module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Pent

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open CFSG CFSG.RankThree.GroupTheory
open scoped commutatorElement

universe u v

section Fixed

variable {G : Type*} [Group G]

theorem exists_central_mod {N W Z : Subgroup G} [Finite N] (hN : IsPGroup 2 N)
    (hWN : W ≤ N) (hZc : ∀ z ∈ Z, ∀ n ∈ N, z * n = n * z)
    (hWn : ∀ n ∈ N, ∀ w ∈ W, n * w * n⁻¹ ∈ W) (hne : ∃ w ∈ W, w ∉ Z) :
    ∃ w ∈ W, w ∉ Z ∧ ∀ n ∈ N, n * w * n⁻¹ * w⁻¹ ∈ Z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Zn : Subgroup N := Z.subgroupOf N
  haveI hZnn : Zn.Normal := by
    constructor
    intro z hz g
    have hz' : (z : G) ∈ Z := hz
    have hc := hZc _ hz' g g.2
    have : (g * z * g⁻¹ : N) = z := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : G) * z * (g : G)⁻¹ = (g * z) * (g : G)⁻¹ := rfl
        _ = (z * g) * (g : G)⁻¹ := by rw [← hc]
        _ = z := by group
    rw [this]; exact hz
  let Wn : Subgroup N := W.subgroupOf N
  haveI hWnn : Wn.Normal := by
    constructor
    intro w hw g
    have hw' : (w : G) ∈ W := hw
    show ((g * w * g⁻¹ : N) : G) ∈ W
    simpa using hWn g g.2 w hw'
  have hQ : IsPGroup 2 (N ⧸ Zn) := hN.to_quotient Zn
  haveI : Group.IsNilpotent (N ⧸ Zn) := hQ.isNilpotent
  let π := QuotientGroup.mk' Zn
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Zn
  have hWq : (Wn.map π).Normal := hWnn.map π hπ
  obtain ⟨w₀, hw₀, hw₀Z⟩ := hne
  have hne' : Wn.map π ≠ ⊥ := by
    intro hbot
    have : π ⟨w₀, hWN hw₀⟩ ∈ Wn.map π := ⟨⟨w₀, hWN hw₀⟩, hw₀, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact hw₀Z this
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨q, hqW, hqc⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hcen
  obtain ⟨w', hw', rfl⟩ := hqW
  refine ⟨(w' : G), hw', ?_, ?_⟩
  · intro hwZ
    apply hq1
    apply Subtype.ext
    change π w' = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hwZ
  · intro n hn
    have h1 : ⁅π ⟨n, hn⟩, π w'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.mp hqc (π ⟨n, hn⟩)
    rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : ((⁅(⟨n, hn⟩ : N), w'⁆ : N) : G) ∈ Z := h1
    simpa [commutatorElement_def] using h2

end Fixed

section Central

variable {G : Type*} [Group G]

@[expose] def prodCentral (R Z : Subgroup G) (hZ : ∀ z ∈ Z, ∀ g : G, z * g = g * z) :
    Subgroup G where
  carrier := {w | ∃ r ∈ R, ∃ z ∈ Z, w = r * z}
  one_mem' := ⟨1, R.one_mem, 1, Z.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨r, hr, z, hz, rfl⟩ ⟨r', hr', z', hz', rfl⟩
    refine ⟨r * r', R.mul_mem hr hr', z * z', Z.mul_mem hz hz', ?_⟩
    calc r * z * (r' * z') = r * (z * r') * z' := by group
      _ = r * (r' * z) * z' := by rw [hZ z hz r']
      _ = r * r' * (z * z') := by group
  inv_mem' := by
    rintro _ ⟨r, hr, z, hz, rfl⟩
    refine ⟨r⁻¹, R.inv_mem hr, z⁻¹, Z.inv_mem hz, ?_⟩
    calc (r * z)⁻¹ = z⁻¹ * r⁻¹ := by group
      _ = r⁻¹ * z⁻¹ := by rw [hZ z⁻¹ (Z.inv_mem hz) r⁻¹]

theorem eq_of_self_normalizing {Q W : Subgroup G} [Finite Q] (hQ : IsPGroup 2 Q) (hWQ : W ≤ Q)
    (h : ∀ y ∈ Q, y ∈ Subgroup.normalizer (W : Set G) → y ∈ W) : W = Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent Q := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := Q)
  by_contra hne
  have hlt : W.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    apply le_antisymm hWQ
    intro q hq
    have : (⟨q, hq⟩ : Q) ∈ W.subgroupOf Q := by rw [htop]; exact Subgroup.mem_top _
    exact this
  obtain ⟨hle, hnle⟩ := lt_iff_le_not_ge.mp (hnc _ hlt)
  apply hnle
  intro x hx
  have hxQ : (x : G) ∈ Q := x.2
  have hxn : (x : G) ∈ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have hgQ : g ∈ Q := hWQ hg
      have := (Subgroup.mem_normalizer_iff.mp hx) ⟨g, hgQ⟩
      have h1 : (⟨g, hgQ⟩ : Q) ∈ W.subgroupOf Q := hg
      exact (this.mp h1 : _)
    · intro hg
      by_cases hgQ : g ∈ Q
      · have := (Subgroup.mem_normalizer_iff.mp hx) ⟨g, hgQ⟩
        have h1 : (⟨g, hgQ⟩ : Q) ∈ W.subgroupOf Q := this.mpr hg
        exact h1
      · exfalso
        apply hgQ
        have hxg : (x : G) * g * (x : G)⁻¹ ∈ Q := hWQ hg
        have : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
        rw [this]
        exact Q.mul_mem (Q.mul_mem (Q.inv_mem hxQ) hxg) hxQ
  exact h _ hxQ hxn

end Central

section Pattern

variable {G : Type*} [Group G] [HasDistribNeg G]

theorem comm_of_same_pattern (g g' x : G)
    (h : (g * x = x * g ∧ g' * x = x * g') ∨ (g * x = -(x * g) ∧ g' * x = -(x * g'))) :
    (g * g'⁻¹) * x = x * (g * g'⁻¹) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hk : g'⁻¹ * x = x * g'⁻¹ := by
      calc g'⁻¹ * x = g'⁻¹ * (x * g') * g'⁻¹ := by group
        _ = g'⁻¹ * (g' * x) * g'⁻¹ := by rw [h2]
        _ = x * g'⁻¹ := by group
    calc g * g'⁻¹ * x = g * (g'⁻¹ * x) := by group
      _ = g * (x * g'⁻¹) := by rw [hk]
      _ = (g * x) * g'⁻¹ := by group
      _ = (x * g) * g'⁻¹ := by rw [h1]
      _ = x * (g * g'⁻¹) := by group
  · have hk : g'⁻¹ * x = -(x * g'⁻¹) := by
      have : x * g'⁻¹ = -(g'⁻¹ * x) := by
        calc x * g'⁻¹ = g'⁻¹ * (g' * x) * g'⁻¹ := by group
          _ = g'⁻¹ * (-(x * g')) * g'⁻¹ := by rw [h2]
          _ = -(g'⁻¹ * x) := by rw [mul_neg, neg_mul]; group
      exact eq_neg_symm this
    calc g * g'⁻¹ * x = g * (g'⁻¹ * x) := by group
      _ = g * (-(x * g'⁻¹)) := by rw [hk]
      _ = -((g * x) * g'⁻¹) := by rw [mul_neg]; group
      _ = -(-(x * g) * g'⁻¹) := by rw [h1]
      _ = x * (g * g'⁻¹) := by rw [neg_mul, neg_neg]; group

end Pattern

theorem bool_pattern (S : Fin 5 → Bool) (h : Even ([0, 1, 2, 3, 4].countP S)) :
    (∀ k, S k = false) ∨ (∃ i j : Fin 5, i ≠ j ∧ ∀ k, S k = true ↔ (k = i ∨ k = j)) ∨
      (∃ j : Fin 5, ∀ k, S k = true ↔ k ≠ j) := by
  revert h
  revert S
  decide

section Realize

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {R : Subgroup (Module.End k V)ˣ} {u : (Module.End k V)ˣ}
  {t : Fin 5 → (Module.End k V)ˣ}

theorem pair_pattern (ht : Pent R u t) {i j : Fin 5} (hij : i ≠ j) (k : Fin 5) :
    (k ≠ i → k ≠ j → (t i * t j) * t k = t k * (t i * t j)) ∧
      ((k = i ∨ k = j) → (t i * t j) * t k = -(t k * (t i * t j))) := by
  constructor
  · intro hki hkj
    have hji : j ≠ k := fun h' => hkj h'.symm
    have hik : i ≠ k := fun h' => hki h'.symm
    calc (t i * t j) * t k = t i * (t j * t k) := by group
      _ = t i * (-(t k * t j)) := by rw [ht.anti j k hji]
      _ = -((t i * t k) * t j) := by rw [mul_neg]; group
      _ = -(-(t k * t i) * t j) := by rw [ht.anti i k hik]
      _ = t k * (t i * t j) := by rw [neg_mul, neg_neg]; group
  · rintro (rfl | rfl)
    · calc (t k * t j) * t k = t k * (t j * t k) := by group
        _ = t k * (-(t k * t j)) := by rw [ht.anti j k (Ne.symm hij)]
        _ = -(t k * (t k * t j)) := by rw [mul_neg]
    · calc (t i * t k) * t k = -(-((t i * t k) * t k)) := (neg_neg _).symm
        _ = -((-(t i * t k)) * t k) := by rw [neg_mul]
        _ = -((t k * t i) * t k) := by rw [← ht.anti k i (Ne.symm hij)]
        _ = -(t k * (t i * t k)) := by rw [mul_assoc]

open Classical in
theorem exists_same_pattern (ht : Pent R u t) (y : (Module.End k V)ˣ)
    (hy : ∀ k, y * t k = t k * y ∨ y * t k = -(t k * y))
    (hpar : Even ([0, 1, 2, 3, 4].countP (fun k : Fin 5 => decide (y * t k ≠ t k * y)))) :
    ∃ a ∈ R, ∀ k, (y * t k = t k * y ∧ a * t k = t k * a) ∨
      (y * t k = -(t k * y) ∧ a * t k = -(t k * a)) := by
  have hS : ∀ k, decide (y * t k ≠ t k * y) = true ↔ y * t k ≠ t k * y := fun k => by simp
  rcases bool_pattern (fun k : Fin 5 => decide (y * t k ≠ t k * y)) hpar with
    h0 | ⟨i, j, hij, hp⟩ | ⟨j, hp⟩
  · refine ⟨1, R.one_mem, fun k => Or.inl ⟨?_, by simp⟩⟩
    by_contra hne
    have := h0 k
    simp only [decide_eq_false_iff_not, ne_eq, not_not] at this
    exact hne this
  · refine ⟨t i * t j, R.mul_mem (ht.mem i) (ht.mem j), fun k => ?_⟩
    by_cases hk : k = i ∨ k = j
    · refine Or.inr ⟨?_, (pair_pattern ht hij k).2 hk⟩
      have : decide (y * t k ≠ t k * y) = true := (hp k).mpr hk
      exact (hy k).resolve_left ((hS k).mp this)
    · push Not at hk
      refine Or.inl ⟨?_, (pair_pattern ht hij k).1 hk.1 hk.2⟩
      by_contra hne
      have := (hp k).mp ((hS k).mpr hne)
      tauto
  · refine ⟨t j, ht.mem j, fun k => ?_⟩
    by_cases hk : k = j
    · subst hk
      refine Or.inl ⟨?_, rfl⟩
      by_contra hne
      have := (hp k).mp ((hS k).mpr hne)
      exact this rfl
    · have hne : y * t k ≠ t k * y := (hS k).mp ((hp k).mpr hk)
      exact Or.inr ⟨(hy k).resolve_left hne, ht.anti j k (Ne.symm hk)⟩

open Classical in
theorem parity_pattern (h : Min32 R u) (ht : Pent R u t) (y : (Module.End k V)ˣ)
    (hy : ∀ k, y * t k = t k * y ∨ y * t k = -(t k * y)) :
    Even ([0, 1, 2, 3, 4].countP (fun k : Fin 5 => decide (y * t k ≠ t k * y))) := by
  have hl : ∀ a ∈ [t 0, t 1, t 2, t 3, t 4], a * y = y * a ∨ a * y = -(y * a) := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hy _ with h1 | h1 <;> [exact Or.inl h1.symm; exact Or.inr (eq_neg_symm h1);
        exact Or.inl h1.symm; exact Or.inr (eq_neg_symm h1); exact Or.inl h1.symm;
        exact Or.inr (eq_neg_symm h1); exact Or.inl h1.symm; exact Or.inr (eq_neg_symm h1);
        exact Or.inl h1.symm; exact Or.inr (eq_neg_symm h1)]
  have h2 := list_prod_mul_eq y (fun a => decide (y * a ≠ a * y))
    (fun a => by simp only [decide_eq_true_eq]; exact ne_comm) [t 0, t 1, t 2, t 3, t 4] hl
  simp only [List.prod_cons, List.prod_nil, mul_one] at h2
  have hmap : [t 0, t 1, t 2, t 3, t 4] = ([0, 1, 2, 3, 4] : List (Fin 5)).map t := rfl
  rw [hmap, List.countP_map] at h2
  have hc : (-1 : (Module.End k V)ˣ) ^ ([0, 1, 2, 3, 4].countP
      (fun k : Fin 5 => decide (y * t k ≠ t k * y))) = 1 := by
    rcases ht.prod with he | he
    · rw [he, one_mul, mul_one] at h2
      exact mul_right_cancel (b := y) (by rw [one_mul]; exact h2.symm)
    · rw [he, neg_mul, one_mul, mul_neg, mul_one] at h2
      exact mul_right_cancel (b := -y) (by rw [one_mul]; exact h2.symm)
  exact (neg_one_pow_eq_one_iff_even h.neg_one_ne_one).mp hc

theorem exists_inner (h : Min32 R u) (ht : Pent R u t) (y : (Module.End k V)ˣ)
    (hy : ∀ k, y * t k = t k * y ∨ y * t k = -(t k * y)) :
    ∃ a ∈ R, ∀ r ∈ R, (y * a⁻¹) * r = r * (y * a⁻¹) := by
  obtain ⟨a, haR, hpat⟩ := exists_same_pattern ht y hy (parity_pattern h ht y hy)
  refine ⟨a, haR, ?_⟩
  have hk : ∀ k, (y * a⁻¹) * t k = t k * (y * a⁻¹) := fun k =>
    comm_of_same_pattern y a (t k) (hpat k)
  set z := y * a⁻¹ with hz
  have hall : ∀ x ∈ Subgroup.closure (insert (-1 : (Module.End k V)ˣ) (Set.range t)),
      z * x = x * z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨i, rfl⟩
      · rw [mul_neg_one, neg_one_mul]
      · exact hk i
    | one => simp
    | mul x y' _ _ hx hy' =>
      calc z * (x * y') = (z * x) * y' := by group
        _ = (x * z) * y' := by rw [hx]
        _ = x * (z * y') := by group
        _ = x * (y' * z) := by rw [hy']
        _ = x * y' * z := by group
    | inv x _ hx =>
      calc z * x⁻¹ = x⁻¹ * (x * z) * x⁻¹ := by group
        _ = x⁻¹ * (z * x) * x⁻¹ := by rw [hx]
        _ = x⁻¹ * z := by group
  intro r hr
  exact hall r (ht.gen r hr)

theorem Min32.scalar_of_centralizes [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hdim : Module.finrank k V = 4) (h : Min32 R u) {y : (Module.End k V)ˣ}
    (hy : ∀ r ∈ R, y * r = r * y) :
    ∃ a : k, (y : Module.End k V) = algebraMap k (Module.End k V) a := by
  haveI : Finite R := Nat.finite_of_card_ne_zero (by rw [h.card_eq]; norm_num)
  obtain ⟨z, hz, hzV⟩ := h.center
  let ρ : Representation k R V := (Units.coeHom (Module.End k V)).comp R.subtype
  have hρ : Function.Injective ρ := fun a b hab => Subtype.ext (Units.ext hab)
  have hK : ringChar k ≠ 2 := by
    intro hc
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [hc] at this
    exact_mod_cast this
  have hcard : Nat.card R = 2 ^ (1 + 2 * 2) := by rw [h.card_eq]; norm_num
  have hcent := (SteinbergBM.minimal_extraspecial_module_scalar_centralizer.{_, _, _, 0}
    h.isExtra hcard hz hK (by rw [hdim]; norm_num) ρ hρ).2.2.1
  have hmem : y ∈ Subgroup.centralizer (Set.range ρ.asGroupHom) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, rfl⟩
    have : ρ.asGroupHom r = (r : (Module.End k V)ˣ) :=
      Units.ext (by rw [Representation.asGroupHom_apply]; rfl)
    rw [this]
    exact (hy r r.2).symm
  rw [hcent] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc]; rfl⟩

theorem Min32.irred_prod (h : Min32 R u) {Z M : Subgroup (Module.End k V)ˣ}
    (hZ1 : (-1 : (Module.End k V)ˣ) ∈ Z) (hZM : Z ≤ M)
    (huM : u ∈ Subgroup.normalizer (M : Set (Module.End k V)ˣ))
    (hMW : ∀ m ∈ M, ∃ r ∈ R, ∃ z ∈ Z, m = r * z) (hne : ∃ m ∈ M, m ∉ Z) :
    ∀ r ∈ R, ∀ z ∈ Z, r * z ∈ M := by
  intro r hr z hz
  by_cases hRM : R ≤ M
  · exact M.mul_mem (hRM hr) (hZM hz)
  · exfalso
    have hMR : M ⊓ R ≠ R := fun heq => hRM (by rw [← heq]; exact inf_le_left)
    have hnorm : u ∈ Subgroup.normalizer ((M ⊓ R : Subgroup (Module.End k V)ˣ) :
        Set (Module.End k V)ˣ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        exact ⟨(Subgroup.mem_normalizer_iff.mp huM g).mp hg.1,
          (Subgroup.mem_normalizer_iff.mp h.norm g).mp hg.2⟩
      · intro hg
        exact ⟨(Subgroup.mem_normalizer_iff.mp huM g).mpr hg.1,
          (Subgroup.mem_normalizer_iff.mp h.norm g).mpr hg.2⟩
    have hcomm := h.minimal (M ⊓ R) inf_le_right hMR hnorm
    have hsmall : ∀ s ∈ M ⊓ R, s = 1 ∨ s = -1 := fun s hs =>
      h.fpf_elem hs.2 (Or.inl (hcomm s hs))
    obtain ⟨m, hmM, hmZ⟩ := hne
    obtain ⟨r', hr', z', hz', rfl⟩ := hMW m hmM
    have hr'M : r' ∈ M := by
      have := M.mul_mem hmM (M.inv_mem (hZM hz'))
      rwa [mul_inv_cancel_right] at this
    apply hmZ
    rcases hsmall r' ⟨hr'M, hr'⟩ with h1 | h1
    · rw [h1, one_mul]; exact hz'
    · rw [h1]; exact Z.mul_mem hZ1 hz'

theorem scalar_unit_sq {A : Type*} [Ring A] [Algebra k A] [Nontrivial A] {c : Aˣ} {a : k}
    (ha : (c : A) = algebraMap k A a) (hc : c * c = 1) : c = 1 ∨ c = -1 := by
  have h1 : algebraMap k A (a * a) = algebraMap k A 1 := by
    rw [map_mul, ← ha, map_one, ← Units.val_mul, hc, Units.val_one]
  have h2 : a * a = 1 := (algebraMap k A).injective h1
  rcases mul_self_eq_one_iff.mp h2 with rfl | rfl
  · left; apply Units.ext; rw [ha, map_one, Units.val_one]
  · right; apply Units.ext; rw [ha, map_neg, map_one, Units.val_neg, Units.val_one]

theorem Min32.eq_of_commutator_eq [FiniteDimensional k V] (h2 : (2 : k) ≠ 0)
    (hdim : Module.finrank k V = 4) (h : Min32 R u) (hu5 : u ^ 5 = 1)
    {Q : Subgroup (Module.End k V)ˣ} [Finite Q] (hQ2 : IsPGroup 2 Q) (hRQ : R ≤ Q)
    (huQ : u ∈ Subgroup.normalizer (Q : Set (Module.End k V)ˣ))
    (hcQ : ∀ q ∈ Q, q ∈ ⁅Q, Subgroup.zpowers u⁆) : Q = R := by
  classical
  obtain ⟨t, ht⟩ := h.exists_pent hu5
  obtain ⟨hm1, -, -, -⟩ := h.facts
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  let Z : Subgroup (Module.End k V)ˣ := Q ⊓ Subgroup.centralizer (R : Set (Module.End k V)ˣ)
  have hZsc : ∀ z ∈ Z, ∃ a : k, (z : Module.End k V) = algebraMap k (Module.End k V) a :=
    fun z hz => h.scalar_of_centralizes h2 hdim (y := z)
      (fun r hr => (Subgroup.mem_centralizer_iff.mp hz.2 r hr).symm)
  have hZcen : ∀ z ∈ Z, ∀ g : (Module.End k V)ˣ, z * g = g * z := by
    intro z hz g
    obtain ⟨a, ha⟩ := hZsc z hz
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ha]
    exact Algebra.commutes a (g : Module.End k V)
  have hZ1 : (-1 : (Module.End k V)ˣ) ∈ Z :=
    ⟨hRQ hm1, Subgroup.mem_centralizer_iff.mpr fun r _ => by rw [mul_neg_one, neg_one_mul]⟩
  have hZu : ∀ z ∈ Z, u * z * u⁻¹ = z := fun z hz => by
    rw [← hZcen z hz u]; group
  have ht0Z : t 0 ∉ Z := by
    intro hz
    have hc := Subgroup.mem_centralizer_iff.mp hz.2 (t 1) (ht.mem 1)
    have ha := ht.anti 0 1 (by decide)
    rw [hc] at ha
    exact h.eq_neg_self_false ha
  let W : Subgroup (Module.End k V)ˣ := prodCentral R Z hZcen
  have hWQ : W ≤ Q := by
    rintro _ ⟨r, hr, z, hz, rfl⟩
    exact Q.mul_mem (hRQ hr) hz.1
  have hRW : ∀ r ∈ R, r ∈ W := fun r hr => ⟨r, hr, 1, Z.one_mem, (mul_one r).symm⟩
  have hZW : ∀ z ∈ Z, z ∈ W := fun z hz => ⟨1, R.one_mem, z, hz, (one_mul z).symm⟩
  have huW : ∀ w ∈ W, u * w * u⁻¹ ∈ W := by
    rintro _ ⟨r, hr, z, hz, rfl⟩
    refine ⟨u * r * u⁻¹, (Subgroup.mem_normalizer_iff.mp h.norm r).mp hr, z, hz, ?_⟩
    rw [conj_mul, hZu z hz]
  have hnormW : u ∈ Subgroup.normalizer (W : Set (Module.End k V)ˣ) :=
    mem_normalizer_of_five hu5 huW
  have hWinv : ∀ w ∈ W, u⁻¹ * w * u ∈ W := by
    intro w hw
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnormW) w).mp hw
    simpa using this
  let N : Subgroup (Module.End k V)ˣ := Q ⊓ Subgroup.normalizer (W : Set (Module.End k V)ˣ)
  haveI : Finite N := Finite.of_injective (Subgroup.inclusion (inf_le_left : N ≤ Q))
    (Subgroup.inclusion_injective _)
  have hN2 : IsPGroup 2 N := hQ2.to_le inf_le_left
  have hWN : W ≤ N := fun w hw => ⟨hWQ hw, Subgroup.le_normalizer hw⟩
  have hNW : ∀ n ∈ N, ∀ w ∈ W, n * w * n⁻¹ ∈ W := fun n hn w hw =>
    (Subgroup.mem_normalizer_iff.mp hn.2 w).mp hw
  have hunN : ∀ n ∈ N, u⁻¹ * n * u ∈ N := by
    intro n hn
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem huQ) n).mp hn.1
      simpa using this
    · refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
      have hconj : (u⁻¹ * n * u) * g * (u⁻¹ * n * u)⁻¹ =
          u⁻¹ * (n * (u * g * u⁻¹) * n⁻¹) * u := by group
      rw [hconj]
      constructor
      · intro hg
        exact hWinv _ (hNW n hn _ (huW g hg))
      · intro hg
        have h1 : n * (u * g * u⁻¹) * n⁻¹ ∈ W := by
          have := huW _ hg
          have e : u * (u⁻¹ * (n * (u * g * u⁻¹) * n⁻¹) * u) * u⁻¹ =
              n * (u * g * u⁻¹) * n⁻¹ := by group
          rwa [e] at this
        have h2 : u * g * u⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hn.2 _).mpr h1
        exact (Subgroup.mem_normalizer_iff.mp hnormW g).mpr h2
  let M : Subgroup (Module.End k V)ˣ :=
    { carrier := {w | w ∈ W ∧ ∀ n ∈ N, n * w * n⁻¹ * w⁻¹ ∈ Z}
      one_mem' := ⟨W.one_mem, fun n _ => by simpa using Z.one_mem⟩
      mul_mem' := by
        rintro w w' ⟨hw, hcw⟩ ⟨hw', hcw'⟩
        refine ⟨W.mul_mem hw hw', fun n hn => ?_⟩
        have hc := hcw n hn
        have hc' := hcw' n hn
        have hcent : w * (n * w' * n⁻¹ * w'⁻¹) * w⁻¹ = n * w' * n⁻¹ * w'⁻¹ := by
          rw [← hZcen _ hc' w]; group
        have e : n * (w * w') * n⁻¹ * (w * w')⁻¹ =
            (n * w * n⁻¹ * w⁻¹) * (n * w' * n⁻¹ * w'⁻¹) := by
          calc n * (w * w') * n⁻¹ * (w * w')⁻¹
              = (n * w * n⁻¹ * w⁻¹) * (w * (n * w' * n⁻¹ * w'⁻¹) * w⁻¹) := by group
            _ = (n * w * n⁻¹ * w⁻¹) * (n * w' * n⁻¹ * w'⁻¹) := by rw [hcent]
        rw [e]
        exact Z.mul_mem hc hc'
      inv_mem' := by
        rintro w ⟨hw, hcw⟩
        refine ⟨W.inv_mem hw, fun n hn => ?_⟩
        have hc := hcw n hn
        have e1 : n * w * n⁻¹ = (n * w * n⁻¹ * w⁻¹) * w := by group
        have e2 : n * w⁻¹ * n⁻¹ * (w⁻¹)⁻¹ = (n * w * n⁻¹ * w⁻¹)⁻¹ := by
          calc n * w⁻¹ * n⁻¹ * (w⁻¹)⁻¹ = (n * w * n⁻¹)⁻¹ * w := by group
            _ = ((n * w * n⁻¹ * w⁻¹) * w)⁻¹ * w := by rw [← e1]
            _ = w⁻¹ * (n * w * n⁻¹ * w⁻¹)⁻¹ * w := by group
            _ = (n * w * n⁻¹ * w⁻¹)⁻¹ := by
              calc w⁻¹ * (n * w * n⁻¹ * w⁻¹)⁻¹ * w
                  = w⁻¹ * ((n * w * n⁻¹ * w⁻¹)⁻¹ * w) := by group
                _ = w⁻¹ * (w * (n * w * n⁻¹ * w⁻¹)⁻¹) := by
                  rw [hZcen _ (Z.inv_mem hc) w]
                _ = (n * w * n⁻¹ * w⁻¹)⁻¹ := by group
        rw [e2]
        exact Z.inv_mem hc }
  have hZM : Z ≤ M := fun z hz =>
    ⟨hZW z hz, fun n _ => by rw [← hZcen z hz n]; simpa using Z.one_mem⟩
  have huM : u ∈ Subgroup.normalizer (M : Set (Module.End k V)ˣ) := by
    refine mem_normalizer_of_five hu5 ?_
    rintro w ⟨hw, hcw⟩
    refine ⟨huW w hw, fun n hn => ?_⟩
    have hc := hcw (u⁻¹ * n * u) (hunN n hn)
    have e : n * (u * w * u⁻¹) * n⁻¹ * (u * w * u⁻¹)⁻¹ =
        u * ((u⁻¹ * n * u) * w * (u⁻¹ * n * u)⁻¹ * w⁻¹) * u⁻¹ := by group
    rw [e, hZu _ hc]
    exact hc
  have hMW : ∀ m ∈ M, ∃ r ∈ R, ∃ z ∈ Z, m = r * z := fun m hm => hm.1
  have hne : ∃ m ∈ M, m ∉ Z := by
    obtain ⟨w, hwW, hwZ, hwc⟩ := exists_central_mod hN2 hWN (fun z hz n _ => hZcen z hz n) hNW
      ⟨t 0, hRW _ (ht.mem 0), ht0Z⟩
    exact ⟨w, ⟨hwW, hwc⟩, hwZ⟩
  have hstep1 : ∀ n ∈ N, ∀ w ∈ W, n * w * n⁻¹ * w⁻¹ ∈ Z := by
    rintro n hn _ ⟨r, hr, z, hz, rfl⟩
    exact (h.irred_prod hZ1 hZM huM hMW hne r hr z hz).2 n hn
  have hclaim : ∀ y ∈ N, y ∈ W := by
    intro y hy
    have hyk : ∀ k, y * t k = t k * y ∨ y * t k = -(t k * y) := by
      intro k
      have hc : y * t k * y⁻¹ * (t k)⁻¹ ∈ Z := hstep1 y hy (t k) (hRW _ (ht.mem k))
      obtain ⟨a, ha⟩ := hZsc _ hc
      set c := y * t k * y⁻¹ * (t k)⁻¹ with hcdef
      have e1 : y * t k * y⁻¹ = c * t k := by rw [hcdef]; group
      have hcc : c * c = 1 := by
        have e2 : (y * t k * y⁻¹) * (y * t k * y⁻¹) = 1 := by
          calc (y * t k * y⁻¹) * (y * t k * y⁻¹) = y * (t k * t k) * y⁻¹ := by group
            _ = 1 := by rw [ht.sq k]; group
        rw [e1] at e2
        calc c * c = c * c * (t k * t k) := by rw [ht.sq k, mul_one]
          _ = c * (c * t k) * t k := by group
          _ = c * (t k * c) * t k := by rw [hZcen c hc (t k)]
          _ = (c * t k) * (c * t k) := by group
          _ = 1 := e2
      rcases scalar_unit_sq ha hcc with h1 | h1
      · left
        calc y * t k = (y * t k * y⁻¹) * y := by group
          _ = t k * y := by rw [e1, h1, one_mul]
      · right
        calc y * t k = (y * t k * y⁻¹) * y := by group
          _ = -(t k * y) := by rw [e1, h1, neg_one_mul, neg_mul]
    obtain ⟨a, haR, hcomm⟩ := exists_inner h ht y hyk
    have hz : y * a⁻¹ ∈ Z := ⟨Q.mul_mem hy.1 (Q.inv_mem (hRQ haR)),
      Subgroup.mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm⟩
    refine ⟨a, haR, y * a⁻¹, hz, ?_⟩
    calc y = (y * a⁻¹) * a := by group
      _ = a * (y * a⁻¹) := hZcen _ hz a
  have hWQeq : W = Q :=
    eq_of_self_normalizing hQ2 hWQ (fun y hyQ hyn => hclaim y ⟨hyQ, hyn⟩)
  apply le_antisymm _ hRQ
  intro q hq
  have hle : ⁅Q, Subgroup.zpowers u⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [← hWQeq] at hg₁
    obtain ⟨r, hr, z, hz, rfl⟩ := hg₁
    have hg2 : g₂ ∈ Subgroup.normalizer (R : Set (Module.End k V)ˣ) :=
      Subgroup.zpowers_le.mpr h.norm hg₂
    have e : ⁅r * z, g₂⁆ = r * (g₂ * r⁻¹ * g₂⁻¹) := by
      simp only [commutatorElement_def]
      have hzg : z * g₂ = g₂ * z := hZcen z hz g₂
      calc r * z * g₂ * (r * z)⁻¹ * g₂⁻¹ = r * (z * g₂) * z⁻¹ * r⁻¹ * g₂⁻¹ := by group
        _ = r * (g₂ * z) * z⁻¹ * r⁻¹ * g₂⁻¹ := by rw [hzg]
        _ = r * (g₂ * r⁻¹ * g₂⁻¹) := by group
    rw [e]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.mp hg2 r⁻¹).mp (R.inv_mem hr))
  exact hle (hcQ q hq)

end Realize

section Core

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem core_lemma [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) (hV : Module.finrank k V ≤ 4)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Q : Subgroup (Module.End k V)ˣ} [Finite Q]
    (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥) {u : (Module.End k V)ˣ}
    (hu : u ∈ Subgroup.normalizer (Q : Set (Module.End k V)ˣ)) (hup : u ^ p = 1)
    (hcQ : ⁅Q, Subgroup.zpowers u⁆ = Q) :
    p = 5 ∧ Module.finrank k V = 4 ∧ Min32 Q u := by
  have hum : u ^ p ^ 1 = 1 := by simpa using hup
  rcases exists_min32_of_finrank_le_four h2 hp hp5 hV Q hQ2 u hu hum with hcomm |
    ⟨R, hRQ, hR, hp5', hdim⟩
  · exfalso
    apply hQ1
    rw [eq_bot_iff]
    intro q hq
    have hq' : q ∈ ⁅Q, Subgroup.zpowers u⁆ := by rw [hcQ]; exact hq
    have hle : ⁅Q, Subgroup.zpowers u⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg₂
      have hc : Commute u g₁ := (hcomm g₁ hg₁)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact ((hc.zpow_left n).eq).symm ▸ rfl
    exact hle hq'
  · subst hp5'
    refine ⟨rfl, hdim, ?_⟩
    have hcQ' : ∀ q ∈ Q, q ∈ ⁅Q, Subgroup.zpowers u⁆ := fun q hq => by rw [hcQ]; exact hq
    have hQR := Min32.eq_of_commutator_eq h2 hdim hR hup hQ2 hRQ hu hcQ'
    rw [hQR]
    exact hR

end Core

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
