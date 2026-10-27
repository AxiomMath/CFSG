module

public import CFSG.CGT.T75F.E710Num4
public import CFSG.CGT.T75F.E710Bender

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

variable {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}
  {q' : ℕ} {δ : X ⧸ Subgroup.center X}

theorem exists_minimal_normalizing (L : Subgroup X) (a : X) :
    ∃ μ : ℕ, 0 < μ ∧ (∀ l ∈ L, a ^ μ * l * (a ^ μ)⁻¹ ∈ L) ∧
      ∀ k : ℕ, 0 < k → (∀ l ∈ L, a ^ k * l * (a ^ k)⁻¹ ∈ L) → μ ≤ k := by
  classical
  have hex : ∃ k : ℕ, 0 < k ∧ ∀ l ∈ L, a ^ k * l * (a ^ k)⁻¹ ∈ L :=
    ⟨orderOf a, orderOf_pos a, fun l hl => by rw [pow_orderOf_eq_one]; simpa using hl⟩
  exact ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
    fun k hk hN => Nat.find_min' hex ⟨hk, hN⟩⟩

namespace Endgame710

variable (h : Endgame710 D M L q)

include h in
theorem L_complement (hT : Torus710 M q' δ) (hq' : q' = q ^ 2) :
    ∀ x ∈ M, ∃ y ∈ L, y⁻¹ * x ∈ Subgroup.center X := by
  let f : L → Mhat M := fun l => ⟨(QuotientGroup.mk (l : X) : X ⧸ Subgroup.center X),
    psi_mem_Mhat (h.L_le l.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact h.psi_inj_L a.2 b.2 (congrArg Subtype.val hab)
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hT.card, h.L_card, hq'])
  intro x hx
  obtain ⟨⟨y, hy⟩, hyx⟩ := hbij.2 ⟨(QuotientGroup.mk x : X ⧸ Subgroup.center X), psi_mem_Mhat hx⟩
  refine ⟨y, hy, ?_⟩
  have : (QuotientGroup.mk y : X ⧸ Subgroup.center X) = QuotientGroup.mk x :=
    congrArg Subtype.val hyx
  exact QuotientGroup.eq.1 this

omit [Finite X] in
theorem fpf_fixed {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ) {k : ℕ}
    (hfpf : ∀ ω ∈ Mhat M, ω ≠ 1 → δ ^ k * ω * (δ ^ k)⁻¹ ≠ ω) :
    ∀ m ∈ M, a ^ k * m * (a ^ k)⁻¹ = m → m ∈ Subgroup.center X := by
  intro m hm hfix
  have : (QuotientGroup.mk m : X ⧸ Subgroup.center X) = 1 := by
    by_contra hne
    apply hfpf (QuotientGroup.mk m) (psi_mem_Mhat hm) hne
    have := congrArg (fun x => (QuotientGroup.mk x : X ⧸ Subgroup.center X)) hfix
    simpa [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, ha] using this
  exact (QuotientGroup.eq_one_iff m).1 this

variable (hT : Torus710 M q' δ)

include h hT in
theorem conj_mem_M {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ) (i : ℕ) :
    ∀ m ∈ M, a ^ i * m * (a ^ i)⁻¹ ∈ M := by
  have hle : M ≤ M.comap (MulAut.conj (a ^ i)).toMonoidHom := by
    calc M = Subgroup.closure (D ∩ (M : Set X)) := h.M_gen.symm
      _ ≤ M.comap (MulAut.conj (a ^ i)).toMonoidHom := by
        rw [Subgroup.closure_le]
        intro β hβ
        exact (h.conj_mem_delta hT ha i hβ.1 hβ.2).2
  intro m hm
  exact hle hm

include h hT in
theorem mu_le {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ) {μ : ℕ}
    (hμmin : ∀ k : ℕ, 0 < k → (∀ l ∈ L, a ^ k * l * (a ^ k)⁻¹ ∈ L) → μ ≤ k) : μ ≤ q + 1 := by
  have hq4 := h.q_ge
  have key : ∀ i j : ℕ, i < j → j < μ → ∀ l ∈ L, l ≠ 1 → ∀ l' ∈ L, l' ≠ 1 →
      a ^ i * l * (a ^ i)⁻¹ = a ^ j * l' * (a ^ j)⁻¹ → False := by
    intro i j hij hjμ l hl hl1 l' hl' hl'1 heq
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : 0 < d := by omega
    have h1 : l = a ^ d * l' * (a ^ d)⁻¹ := by
      calc l = (a ^ i)⁻¹ * (a ^ i * l * (a ^ i)⁻¹) * a ^ i := by group
        _ = (a ^ i)⁻¹ * (a ^ (i + d) * l' * (a ^ (i + d))⁻¹) * a ^ i := by rw [heq]
        _ = a ^ d * l' * (a ^ d)⁻¹ := by rw [pow_add]; group
    have hN := h.L_TI (a ^ d) l' hl' hl'1 (by rw [← h1]; exact hl)
    have := hμmin d hd hN
    omega
  have hsd : (Set.Iio μ ×ˢ ((L : Set X) \ ({1} : Set X))).ncard ≤ (D ∩ (M : Set X)).ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun p : ℕ × X => a ^ p.1 * p.2 * (a ^ p.1)⁻¹) ?_ ?_
      (Set.toFinite _)
    · rintro ⟨i, l⟩ hp
      simp only [Set.mem_prod, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hp
      exact h.conj_mem_delta hT ha i (h.L_D l hp.2.1 hp.2.2) (h.L_le hp.2.1)
    · rintro ⟨i, l⟩ hp ⟨j, l'⟩ hp' heq
      simp only [Set.mem_prod, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
        Set.mem_Iio] at hp hp'
      have heq' : a ^ i * l * (a ^ i)⁻¹ = a ^ j * l' * (a ^ j)⁻¹ := heq
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact (key i j hij hp'.1 l hp.2.1 hp.2.2 l' hp'.2.1 hp'.2.2 heq').elim
      · have : l = l' := by simpa using heq'
        rw [this]
      · exact (key j i hji hp.1 l' hp'.2.1 hp'.2.2 l hp.2.1 hp.2.2 heq'.symm).elim
  rw [Set.ncard_prod] at hsd
  have h3 : (Set.Iio μ).ncard = μ := by
    rw [← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  have h4 : ((L : Set X) \ ({1} : Set X)).ncard = q ^ 2 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem L.one_mem, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) h.L_card
  have h5 : (D ∩ (M : Set X)).ncard = (q + 1) * (q ^ 2 - 1) := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_Delta
  rw [h3, h4, h5] at hsd
  have hpos : 0 < q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  exact Nat.le_of_mul_le_mul_right hsd hpos

include h hT in
theorem normalizes_L {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ)
    (hq' : q' = q ^ 2) : ∀ l ∈ L, a * l * a⁻¹ ∈ L := by
  have hq4 := h.q_ge
  obtain ⟨μ, hμ, hμN, hμmin⟩ := exists_minimal_normalizing L a
  have hμq := h.mu_le hT ha hμmin
  have hnt : 1 < Nat.card L := by rw [h.L_card]; nlinarith
  have : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 hnt
  obtain ⟨⟨u₀, hu₀⟩, hne⟩ := exists_ne (1 : L)
  have hu₀1 : u₀ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hω₀M : (QuotientGroup.mk u₀ : X ⧸ Subgroup.center X) ∈ Mhat M :=
    psi_mem_Mhat (h.L_le hu₀)
  have hω₀1 : (QuotientGroup.mk u₀ : X ⧸ Subgroup.center X) ≠ 1 := h.mk_ne_one (h.L_D u₀ hu₀ hu₀1)
  by_cases hfixed : ∃ ω ∈ Mhat M, ω ≠ 1 ∧ δ ^ μ * ω * (δ ^ μ)⁻¹ = ω
  · exfalso
    obtain ⟨ω₁, hω₁, hω₁1, hω₁fix⟩ := hfixed
    have hcen := hT.fix_all μ hω₁ hω₁1 hω₁fix
    have h1 := hT.card_le_of_central hμ hω₀M hω₀1 hcen
    rw [hq'] at h1
    have h4q : 4 * q ≤ q ^ 2 := by nlinarith
    generalize q ^ 2 = P at h1 h4q
    omega
  · push Not at hfixed
    have hfix := fpf_fixed ha (k := μ) (fun ω hω hω1 => hfixed ω hω hω1)
    have hM1 := h.conj_mem_M hT ha 1
    simp only [pow_one] at hM1
    have hle := le_of_invariant_complement (M := M) (L₁ := L.map (MulAut.conj a).toMonoidHom)
      (L₂ := L) h.M_comm h.M_sq (s := a ^ μ) (h.conj_mem_M hT ha μ) hfix ?_ h.L_le ?_ hμN ?_ ?_
    · intro l hl
      exact hle ⟨l, hl, rfl⟩
    · rintro _ ⟨l, hl, rfl⟩
      exact hM1 l (h.L_le hl)
    · rintro _ ⟨l, hl, rfl⟩
      refine ⟨a ^ μ * l * (a ^ μ)⁻¹, hμN l hl, ?_⟩
      show a * (a ^ μ * l * (a ^ μ)⁻¹) * a⁻¹ = a ^ μ * (a * l * a⁻¹) * (a ^ μ)⁻¹
      group
    · rintro _ ⟨l, hl, rfl⟩ hz
      have hz' : a * l * a⁻¹ ∈ Subgroup.center X := hz
      have hcz := Subgroup.mem_center_iff.1 hz'
      have hleq : l = a * l * a⁻¹ := by
        calc l = a⁻¹ * (a * l * a⁻¹) * a := by group
          _ = (a * l * a⁻¹) * a⁻¹ * a := by rw [hcz a⁻¹]
          _ = a * l * a⁻¹ := by group
      have hlz : l ∈ Subgroup.center X := by rw [hleq]; exact hz'
      have hl1 : l = 1 := h.L_inf_center hl hlz
      subst hl1
      simp
    · exact h.L_complement hT hq'

include h hT in
theorem caseA_false {a : X} (ha : (QuotientGroup.mk a : X ⧸ Subgroup.center X) = δ)
    (hfib : ∀ ω ∈ Mhat M, ω ≠ 1 → (fib D M ω).ncard = q + 1)
    (hN : ∀ l ∈ L, a * l * a⁻¹ ∈ L) : False := by
  have hq4 := h.q_ge
  have hNi : ∀ i : ℕ, ∀ l ∈ L, a ^ i * l * (a ^ i)⁻¹ ∈ L := by
    intro i
    induction i with
    | zero => intro l hl; simpa using hl
    | succ i ih =>
      intro l hl
      have h1 := hN _ (ih l hl)
      have h2 : a ^ (i + 1) * l * (a ^ (i + 1))⁻¹ = a * (a ^ i * l * (a ^ i)⁻¹) * a⁻¹ := by
        rw [pow_succ']; group
      rw [h2]
      exact h1
  have hA1 : ∀ c ∈ Subgroup.center X, ∀ u ∈ L, u ≠ 1 → ∀ u' ∈ L, u' ≠ 1 → c * u ∈ D →
      c * u' ∈ D := by
    intro c hc u hu hu1 u' hu' hu'1 hcu
    obtain ⟨i, hi⟩ := hT.trans (QuotientGroup.mk u) (psi_mem_Mhat (h.L_le hu))
      (h.mk_ne_one (h.L_D u hu hu1)) (QuotientGroup.mk u') (psi_mem_Mhat (h.L_le hu'))
      (h.mk_ne_one (h.L_D u' hu' hu'1))
    have h1 : a ^ i * u * (a ^ i)⁻¹ = u' := by
      refine h.psi_inj_L (hNi i u hu) hu' ?_
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow,
        ha]
      exact hi
    have hcc := Subgroup.mem_center_iff.1 hc
    have h2 : c * u' = a ^ i * (c * u) * (a ^ i)⁻¹ := by
      rw [← h1]
      calc c * (a ^ i * u * (a ^ i)⁻¹) = (c * a ^ i) * u * (a ^ i)⁻¹ := by group
        _ = (a ^ i * c) * u * (a ^ i)⁻¹ := by rw [← hcc (a ^ i)]
        _ = a ^ i * (c * u) * (a ^ i)⁻¹ := by group
    rw [h2]
    exact h.conj_mem _ hcu _
  have hnt : 1 < Nat.card L := by rw [h.L_card]; nlinarith
  have : Nontrivial L := Finite.one_lt_card_iff_nontrivial.1 hnt
  obtain ⟨⟨u₀, hu₀⟩, hne⟩ := exists_ne (1 : L)
  have hu₀1 : u₀ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hu₀D : u₀ ∈ D := h.L_D u₀ hu₀ hu₀1
  have hu₀M : u₀ ∈ M := h.L_le hu₀
  have hu₀2 : u₀ * u₀ = 1 := h.sq_eq_one u₀ hu₀D
  have hω₀M : (QuotientGroup.mk u₀ : X ⧸ Subgroup.center X) ∈ Mhat M := psi_mem_Mhat hu₀M
  have hω₀1 : (QuotientGroup.mk u₀ : X ⧸ Subgroup.center X) ≠ 1 := h.mk_ne_one hu₀D
  have hfibcard := hfib _ hω₀M hω₀1
  have hu₀fib : u₀ ∈ fib D M (QuotientGroup.mk u₀) := ⟨hu₀D, hu₀M, rfl⟩
  have hpos : 0 < (fib D M (QuotientGroup.mk u₀) \ {u₀}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hu₀fib, hfibcard]
    omega
  obtain ⟨β, hβ⟩ := (Set.ncard_pos (Set.toFinite _)).1 hpos
  obtain ⟨⟨hβD, hβM, hβω⟩, hβne⟩ := hβ
  have hβne' : β ≠ u₀ := hβne
  have hc₀z : β * u₀ ∈ Subgroup.center X := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, hβω]
    have := h.Mhat_sq hω₀M
    exact this
  have hc₀1 : β * u₀ ≠ 1 := by
    intro h1
    apply hβne'
    have := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact inv_eq_of_mul_eq_one_right hu₀2
  have hc₀M : β * u₀ ∈ M := M.mul_mem hβM hu₀M
  have hβeq : (β * u₀) * u₀ = β := by
    calc (β * u₀) * u₀ = β * (u₀ * u₀) := by group
      _ = β := by rw [hu₀2, mul_one]
  have hβL : β ∉ L := by
    intro hβL
    have : β * u₀ ∈ L := L.mul_mem hβL hu₀
    exact hc₀1 (h.L_inf_center this hc₀z)
  have hcount := h.count65 β hβD hβM hβL
  have hsub : (L : Set X) \ {u₀} ⊆ {l : X | l ∈ L ∧ β * l ∈ D} := by
    intro l hl
    obtain ⟨hlL, hlne⟩ := hl
    have hlne' : l ≠ u₀ := hlne
    refine ⟨hlL, ?_⟩
    have hu₀l : u₀ * l ∈ L := L.mul_mem hu₀ hlL
    have hu₀l1 : u₀ * l ≠ 1 := by
      intro h1
      apply hlne'
      have := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right hu₀2
    have hD := hA1 (β * u₀) hc₀z u₀ hu₀ hu₀1 (u₀ * l) hu₀l hu₀l1 (by rw [hβeq]; exact hβD)
    have : β * l = (β * u₀) * (u₀ * l) := by
      calc β * l = β * (u₀ * u₀) * l := by rw [hu₀2, mul_one]
        _ = (β * u₀) * (u₀ * l) := by group
    rw [this]
    exact hD
  have h1 : ((L : Set X) \ {u₀}).ncard ≤ Nat.card {l : X | l ∈ L ∧ β * l ∈ D} := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ((L : Set X) \ {u₀}).ncard = q ^ 2 - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem hu₀, ← Nat.card_coe_set_eq]
    exact congrArg (· - 1) h.L_card
  rw [h2] at h1
  have hq2 : q ^ 2 - 1 ≤ q := le_trans h1 hcount
  have h4q : 4 * q ≤ q ^ 2 := by nlinarith
  generalize q ^ 2 = P at hq2 h4q
  omega

end Endgame710

theorem endgame710_false
    (hG : CFSG.CGT.Timmesfeld75.Goldschmidt1974) (hA : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne)
    {X : Type} [Group X] [Finite X] {D : Set X} {M L : Subgroup X} {q : ℕ}
    (h : Endgame710 D M L q) : False := by
  have hB := h.quot_isBender hG hA
  obtain ⟨q', δ, hT⟩ := h.exists_torus hB
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective δ
  obtain ⟨hq', hfib, -⟩ := h.main_count hT ha
  exact h.caseA_false hT ha hfib (h.normalizes_L hT ha hq')

end CFSG.CGT.T75F
