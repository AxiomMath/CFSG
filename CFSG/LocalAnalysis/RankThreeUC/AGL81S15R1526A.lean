module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526Defs
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open scoped commutatorElement

section NatModAux

variable {N : Type} [Group N] [Finite N]

theorem IsNatSum.fixed_eq_one_aux_fix (hN : Nat.card N = 8) {σ : MulAut N}
    (hσ : orderOf σ = 7) {n : N} (hn : σ n = n) : n = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hG : IsPGroup 7 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hσ]; norm_num)
  have hmod := hG.card_modEq_card_fixedPoints N
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) N = {x | σ x = x} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_setOf_eq]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro h m
      have hm : m.1 ∈ MulAction.stabilizer (MulAut N) x := by
        have : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut N) x :=
          (Subgroup.zpowers_le).2 (by rw [MulAction.mem_stabilizer_iff]; exact h)
        exact this m.2
      exact MulAction.mem_stabilizer_iff.1 hm
  rw [hfix, hN] at hmod
  by_contra hne
  have h2 : 2 ≤ ({x | σ x = x} : Set N).ncard := by
    have hsub : ({1, n} : Set N) ⊆ {x | σ x = x} := by
      intro y hy
      rcases hy with rfl | rfl
      · exact map_one σ
      · exact hn
    calc 2 = ({1, n} : Set N).ncard := (Set.ncard_pair (Ne.symm hne)).symm
      _ ≤ _ := Set.ncard_le_ncard hsub
  have h8 : ({x | σ x = x} : Set N).ncard ≤ 8 := by
    rw [← hN, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  rw [Nat.card_coe_set_eq] at hmod
  have hc : ({x | σ x = x} : Set N).ncard = 8 := by
    unfold Nat.ModEq at hmod
    omega
  have hall : ({x | σ x = x} : Set N) = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, hN, hc]
  have hone : σ = 1 := by
    ext x
    have : x ∈ ({x | σ x = x} : Set N) := by rw [hall]; trivial
    exact this
  rw [hone, orderOf_one] at hσ
  omega

theorem IsNatSum.fixed_eq_one_aux_pow_ne (hN : Nat.card N = 8) {σ : MulAut N}
    (hσ : orderOf σ = 7) {n₀ : N} (h₀ : n₀ ≠ 1) {a b : ℕ} (hab : a < b) (hb : b < 7) :
    (σ ^ a) n₀ ≠ (σ ^ b) n₀ := by
  intro h
  have h1 : (σ ^ (b - a)) n₀ = n₀ := by
    have : (σ ^ a) ((σ ^ (b - a)) n₀) = (σ ^ a) n₀ := by
      rw [← MulAut.mul_apply, ← pow_add, Nat.add_sub_cancel' hab.le]
      exact h.symm
    exact (σ ^ a).injective this
  have hcop : (orderOf σ).Coprime (b - a) := by
    rw [hσ]
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (by omega)
  have hord : orderOf (σ ^ (b - a)) = 7 := by rw [hcop.orderOf_pow, hσ]
  exact h₀ (IsNatSum.fixed_eq_one_aux_fix hN hord h1)

theorem IsNatSum.fixed_eq_one_aux_orbit (hN : Nat.card N = 8) {σ : MulAut N}
    (hσ : orderOf σ = 7) {n₀ n : N} (h₀ : n₀ ≠ 1) (hn : n ≠ 1) :
    ∃ k : ℕ, (σ ^ k) n₀ = n := by
  classical
  let F : Fin 7 → {m : N // m ≠ 1} := fun i =>
    ⟨(σ ^ (i : ℕ)) n₀, fun h => h₀ ((σ ^ (i : ℕ)).map_eq_one_iff.1 h)⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have h : (σ ^ (i : ℕ)) n₀ = (σ ^ (j : ℕ)) n₀ := congrArg Subtype.val hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h' => hne (Fin.ext h')) with h' | h'
    · exact IsNatSum.fixed_eq_one_aux_pow_ne hN hσ h₀ h' j.2 h
    · exact IsNatSum.fixed_eq_one_aux_pow_ne hN hσ h₀ h' i.2 h.symm
  have hcard : Nat.card {m : N // m ≠ 1} = 7 := by
    haveI := Fintype.ofFinite N
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun m : N => m = 1),
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hN]
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [hcard]; simp)
  obtain ⟨i, hi⟩ := hbij.2 ⟨n, hn⟩
  exact ⟨i, congrArg Subtype.val hi⟩

theorem IsNatSum.fixed_eq_one_aux_commute (hN : Nat.card N = 8) {σ : MulAut N}
    (hσ : orderOf σ = 7) {τ : MulAut N} (hτ : τ * σ = σ * τ) : ∃ k : ℕ, τ = σ ^ k := by
  have hnt : Nontrivial N := Finite.one_lt_card_iff_nontrivial.1 (by rw [hN]; norm_num)
  obtain ⟨n₀, h₀⟩ := exists_ne (1 : N)
  have hτ₀ : τ n₀ ≠ 1 := fun h => h₀ (τ.map_eq_one_iff.1 h)
  obtain ⟨k, hk⟩ := IsNatSum.fixed_eq_one_aux_orbit hN hσ h₀ hτ₀
  refine ⟨k, ?_⟩
  ext n
  by_cases hn : n = 1
  · subst hn; simp
  · obtain ⟨j, rfl⟩ := IsNatSum.fixed_eq_one_aux_orbit hN hσ h₀ hn
    have hj : τ * σ ^ j = σ ^ j * τ := (Commute.pow_right (show Commute τ σ from hτ) j).eq
    calc τ ((σ ^ j) n₀) = (τ * σ ^ j) n₀ := rfl
      _ = (σ ^ j * τ) n₀ := by rw [hj]
      _ = (σ ^ j) (τ n₀) := rfl
      _ = (σ ^ j) ((σ ^ k) n₀) := by rw [← hk]
      _ = (σ ^ (j + k)) n₀ := by rw [pow_add]; rfl
      _ = (σ ^ (k + j)) n₀ := by rw [add_comm]
      _ = (σ ^ k) ((σ ^ j) n₀) := by rw [pow_add]; rfl

theorem IsNatSum.fixed_eq_one_aux_card_le (hN : Nat.card N = 8) {σ : MulAut N}
    (hσ : orderOf σ = 7) {A : Subgroup (MulAut N)} (hcomm : ∀ a ∈ A, a * σ = σ * a) :
    Nat.card A ≤ 7 := by
  have hle : A ≤ Subgroup.zpowers σ := by
    intro a ha
    obtain ⟨k, rfl⟩ := IsNatSum.fixed_eq_one_aux_commute hN hσ (hcomm a ha)
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) k
  calc Nat.card A ≤ Nat.card (Subgroup.zpowers σ) := Subgroup.card_le_of_le hle
    _ = 7 := by rw [Nat.card_zpowers, hσ]

theorem IsNatSum.fixed_eq_one_aux_endo (hN : Nat.card N = 8) {A : Subgroup (MulAut N)}
    {σ : MulAut N} (hσ : orderOf σ = 7) (hσA : σ ∈ A) (hA : 7 < Nat.card A) {φ : N →* N}
    (hφ : ∀ a ∈ A, ∀ n, φ (a n) = a (φ n)) : φ = 1 ∨ φ = MonoidHom.id N := by
  have hnt : Nontrivial N := Finite.one_lt_card_iff_nontrivial.1 (by rw [hN]; norm_num)
  have hφσ : ∀ (k : ℕ) (n : N), φ ((σ ^ k) n) = (σ ^ k) (φ n) := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, hφ σ hσA]
  obtain ⟨n₀, h₀⟩ := exists_ne (1 : N)
  by_cases hker : φ n₀ = 1
  · left
    ext n
    by_cases hn : n = 1
    · subst hn; simp
    · obtain ⟨k, rfl⟩ := IsNatSum.fixed_eq_one_aux_orbit hN hσ h₀ hn
      rw [hφσ, hker]; simp
  · right
    obtain ⟨k, hk⟩ := IsNatSum.fixed_eq_one_aux_orbit hN hσ h₀ hker
    have hφk : ∀ n, φ n = (σ ^ k) n := by
      intro n
      by_cases hn : n = 1
      · subst hn; simp
      · obtain ⟨j, rfl⟩ := IsNatSum.fixed_eq_one_aux_orbit hN hσ h₀ hn
        rw [hφσ, ← hk, ← MulAut.mul_apply, ← MulAut.mul_apply, ← pow_add, ← pow_add, add_comm]
    by_cases h7 : 7 ∣ k
    · have h1 : σ ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (hσ ▸ h7)
      ext n
      rw [hφk, h1]; rfl
    · exfalso
      have hc : ∀ a ∈ A, Commute a (σ ^ k) := by
        intro a ha
        ext n
        show a ((σ ^ k) n) = (σ ^ k) (a n)
        rw [← hφk, ← hφk, hφ a ha]
      have hcop : Nat.Coprime k 7 :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 7)).2 h7 |>.symm
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := σ) (n := k) (by rw [hσ]; exact hcop)
      have hσm : σ = (σ ^ k) ^ m := hm.symm
      have hle := IsNatSum.fixed_eq_one_aux_card_le hN hσ (A := A) (fun a ha => by
        have := ((hc a ha).pow_right m).eq
        rw [← hσm] at this
        exact this)
      omega

end NatModAux

section Abstract

variable {Lg G N₁ N₂ : Type} [Group Lg] [Group G] [Group N₁] [Group N₂]

theorem IsNatSum.fixed_eq_one_aux_proj (hG : ∀ a b : G, a * b = b * a)
    (j₁ : N₁ →* G) (j₂ : N₂ →* G) (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hrange : ∀ g : G, ∃ a b, g = j₁ a * j₂ b) (hinf : ∀ a b, j₁ a = j₂ b → j₁ a = 1) :
    ∃ (π₁ : G →* N₁) (π₂ : G →* N₂), ∀ a b, π₁ (j₁ a * j₂ b) = a ∧ π₂ (j₁ a * j₂ b) = b := by
  let e : N₁ × N₂ →* G := j₁.noncommCoprod j₂ (fun a b => hG _ _)
  have he : ∀ p : N₁ × N₂, e p = j₁ p.1 * j₂ p.2 := fun p =>
    MonoidHom.noncommCoprod_apply j₁ j₂ _ p
  have hbij : Function.Bijective e := by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ h
      rw [he] at h
      simp only at h
      have h1 : j₁ a = j₂ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
      have h2 : j₁ a = 1 := hinf a b⁻¹ h1
      have ha : a = 1 := hj₁ (by rw [h2, map_one])
      have hb : b = 1 := by
        apply hj₂
        rw [map_one]
        rw [h2, one_mul] at h
        exact h
      simp [ha, hb]
    · intro g
      obtain ⟨a, b, rfl⟩ := hrange g
      exact ⟨(a, b), he (a, b)⟩
  let E := MulEquiv.ofBijective e hbij
  refine ⟨(MonoidHom.fst N₁ N₂).comp E.symm.toMonoidHom,
    (MonoidHom.snd N₁ N₂).comp E.symm.toMonoidHom, fun a b => ?_⟩
  have : E.symm (j₁ a * j₂ b) = (a, b) := by
    rw [MulEquiv.symm_apply_eq]
    exact (he (a, b)).symm
  simp [this]

theorem IsNatSum.fixed_eq_one_aux_exists {N : Type} [Group N] {A : Subgroup (MulAut N)}
    (hA : Nat.card A = 168) : ∃ σ ∈ A, orderOf σ = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 7 (by rw [hA]; norm_num)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem IsNatSum.fixed_eq_one_aux_fixed_rho [Finite N₁] (ρ : Lg →* MulAut N₁)
    (hN : Nat.card N₁ = 8) (hρ : Nat.card ρ.range = 168) {n : N₁} (hn : ∀ l, ρ l n = n) :
    n = 1 := by
  obtain ⟨σ, hσA, hσ⟩ := IsNatSum.fixed_eq_one_aux_exists hρ
  obtain ⟨l, rfl⟩ := hσA
  exact IsNatSum.fixed_eq_one_aux_fix hN hσ (hn l)

theorem IsNatSum.fixed_eq_one_aux_endo_rho [Finite N₁] (ρ : Lg →* MulAut N₁)
    (hN : Nat.card N₁ = 8) (hρ : Nat.card ρ.range = 168) {φ : N₁ →* N₁}
    (hφ : ∀ l n, φ (ρ l n) = ρ l (φ n)) : φ = 1 ∨ φ = MonoidHom.id N₁ := by
  obtain ⟨σ, hσA, hσ⟩ := IsNatSum.fixed_eq_one_aux_exists hρ
  refine IsNatSum.fixed_eq_one_aux_endo hN hσ hσA (by rw [hρ]; norm_num) ?_
  rintro a ⟨l, rfl⟩ n
  exact hφ l n

theorem IsNatSum.fixed_eq_one_aux_two (hG : ∀ a b : G, a * b = b * a)
    (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N₁) (ρ₂ : Lg →* MulAut N₂)
    (j₁ : N₁ →* G) (j₂ : N₂ →* G) (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hrange : ∀ g : G, ∃ a b, g = j₁ a * j₂ b) (hinf : ∀ a b, j₁ a = j₂ b → j₁ a = 1)
    (hρ₁ : ∀ l a, j₁ (ρ₁ l a) = ρ l (j₁ a)) (hρ₂ : ∀ l b, j₂ (ρ₂ l b) = ρ l (j₂ b))
    (hf₁ : ∀ n : N₁, (∀ l, ρ₁ l n = n) → n = 1) (hf₂ : ∀ n : N₂, (∀ l, ρ₂ l n = n) → n = 1)
    {g : G} (hg : ∀ l, ρ l g = g) : g = 1 := by
  obtain ⟨π₁, π₂, hπ⟩ := IsNatSum.fixed_eq_one_aux_proj hG j₁ j₂ hj₁ hj₂ hrange hinf
  obtain ⟨a, b, rfl⟩ := hrange g
  have ha : a = 1 := by
    apply hf₁
    intro l
    have h1 : ρ l (j₁ a * j₂ b) = j₁ (ρ₁ l a) * j₂ (ρ₂ l b) := by rw [map_mul, hρ₁, hρ₂]
    have h2 := congrArg π₁ (hg l)
    rw [h1, (hπ _ _).1, (hπ a b).1] at h2
    exact h2
  have hb : b = 1 := by
    apply hf₂
    intro l
    have h1 : ρ l (j₁ a * j₂ b) = j₁ (ρ₁ l a) * j₂ (ρ₂ l b) := by rw [map_mul, hρ₁, hρ₂]
    have h2 := congrArg π₂ (hg l)
    rw [h1, (hπ _ _).2, (hπ a b).2] at h2
    exact h2
  subst ha hb
  simp

end Abstract

section Abstract3

variable {Lg G N₁ N₂ : Type} [Group Lg] [Group G] [Group N₁] [Group N₂]

theorem IsNatSum.card_centralizer_dvd_six_aux_comm (ρ : Lg →* MulAut G) {α : MulAut G}
    (hα : α ∈ Subgroup.centralizer (ρ.range : Set (MulAut G))) (l : Lg) (g : G) :
    α (ρ l g) = ρ l (α g) := by
  have h := (Subgroup.mem_centralizer_iff.1 hα) (ρ l) ⟨l, rfl⟩
  have h2 := congrArg (fun f : MulAut G => f g) h
  exact h2.symm

namespace IsNatSum.card_centralizer_dvd_six_aux

abbrev EqvHom (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N₁) : Type :=
  {h : N₁ →* G // (∀ l a, h (ρ₁ l a) = ρ l (h a)) ∧ h ≠ 1}

def EqvHom.act (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N₁)
    (α : Subgroup.centralizer (ρ.range : Set (MulAut G))) (h : EqvHom ρ ρ₁) : EqvHom ρ ρ₁ :=
  ⟨α.1.toMonoidHom.comp h.1, fun l a => by
    show α.1 (h.1 (ρ₁ l a)) = ρ l (α.1 (h.1 a))
    rw [h.2.1 l a, IsNatSum.card_centralizer_dvd_six_aux_comm ρ α.2], fun h0 => h.2.2 (by
    ext a
    have := congrArg (fun φ : N₁ →* G => φ a) h0
    simpa using this)⟩

instance EqvHom.action (ρ : Lg →* MulAut G)
    (ρ₁ : Lg →* MulAut N₁) :
    MulAction (Subgroup.centralizer (ρ.range : Set (MulAut G))) (EqvHom ρ ρ₁) where
  smul α h := EqvHom.act ρ ρ₁ α h
  one_smul h := by
    apply Subtype.ext
    ext a
    rfl
  mul_smul α β h := by
    apply Subtype.ext
    ext a
    rfl

end IsNatSum.card_centralizer_dvd_six_aux

open IsNatSum.card_centralizer_dvd_six_aux

theorem IsNatSum.card_centralizer_dvd_six_aux_eq [Nontrivial N₁] {φ ψ : N₁ →* N₁}
    (hφ : φ = 1 ∨ φ = MonoidHom.id N₁) (hψ : ψ = 1 ∨ ψ = MonoidHom.id N₁)
    (h : φ = 1 ↔ ψ = 1) : φ = ψ := by
  have hne : (1 : N₁ →* N₁) ≠ MonoidHom.id N₁ := by
    intro h'
    obtain ⟨a, ha⟩ := exists_ne (1 : N₁)
    exact ha (by simpa using (congrArg (fun φ : N₁ →* N₁ => φ a) h').symm)
  rcases hφ with h1 | h1 <;> rcases hψ with h2 | h2
  · rw [h1, h2]
  · exact absurd ((h.1 h1).symm.trans h2) hne
  · exact absurd ((h.2 h2).symm.trans h1) hne
  · rw [h1, h2]

theorem IsNatSum.card_centralizer_dvd_six_aux_two [Finite G] (hG : ∀ a b : G, a * b = b * a)
    (ρ : Lg →* MulAut G) (ρ₁ : Lg →* MulAut N₁) (ρ₂ : Lg →* MulAut N₂)
    (j₁ : N₁ →* G) (j₂ : N₂ →* G) (hj₁ : Function.Injective j₁) (hj₂ : Function.Injective j₂)
    (hrange : ∀ g : G, ∃ a b, g = j₁ a * j₂ b) (hinf : ∀ a b, j₁ a = j₂ b → j₁ a = 1)
    (hρ₁ : ∀ l a, j₁ (ρ₁ l a) = ρ l (j₁ a)) (hρ₂ : ∀ l b, j₂ (ρ₂ l b) = ρ l (j₂ b))
    (c₁ : Nat.card N₁ = 8) (r₁ : Nat.card ρ₁.range = 168)
    (f : N₁ ≃* N₂) (hf : ∀ l a, f (ρ₁ l a) = ρ₂ l (f a)) :
    Nat.card (Subgroup.centralizer (ρ.range : Set (MulAut G))) ∣ 6 := by
  classical
  haveI : Finite N₁ := Finite.of_injective j₁ hj₁
  haveI : Nontrivial N₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [c₁]; norm_num)
  obtain ⟨π₁, π₂, hπ⟩ := IsNatSum.fixed_eq_one_aux_proj hG j₁ j₂ hj₁ hj₂ hrange hinf
  have hdec : ∀ g, g = j₁ (π₁ g) * j₂ (π₂ g) := by
    intro g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [(hπ a b).1, (hπ a b).2]
  have hπ₁ : ∀ l g, π₁ (ρ l g) = ρ₁ l (π₁ g) := by
    intro l g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [map_mul, ← hρ₁, ← hρ₂, (hπ _ _).1, (hπ _ _).1]
  have hπ₂ : ∀ l g, π₂ (ρ l g) = ρ₂ l (π₂ g) := by
    intro l g
    obtain ⟨a, b, rfl⟩ := hrange g
    rw [map_mul, ← hρ₁, ← hρ₂, (hπ _ _).2, (hπ _ _).2]
  have hfs : ∀ l b, f.symm (ρ₂ l b) = ρ₁ l (f.symm b) := by
    intro l b
    apply f.injective
    rw [hf, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  let c₁' : EqvHom ρ ρ₁ → (N₁ →* N₁) := fun h => π₁.comp h.1
  let c₂' : EqvHom ρ ρ₁ → (N₁ →* N₁) := fun h => f.symm.toMonoidHom.comp (π₂.comp h.1)
  have hc₁ : ∀ h : EqvHom ρ ρ₁, c₁' h = 1 ∨ c₁' h = MonoidHom.id N₁ := by
    intro h
    apply IsNatSum.fixed_eq_one_aux_endo_rho ρ₁ c₁ r₁
    intro l n
    show π₁ (h.1 (ρ₁ l n)) = ρ₁ l (π₁ (h.1 n))
    rw [h.2.1, hπ₁]
  have hc₂ : ∀ h : EqvHom ρ ρ₁, c₂' h = 1 ∨ c₂' h = MonoidHom.id N₁ := by
    intro h
    apply IsNatSum.fixed_eq_one_aux_endo_rho ρ₁ c₁ r₁
    intro l n
    show f.symm (π₂ (h.1 (ρ₁ l n))) = ρ₁ l (f.symm (π₂ (h.1 n)))
    rw [h.2.1, hπ₂, hfs]
  have hrec : ∀ (h : EqvHom ρ ρ₁) (a : N₁), h.1 a = j₁ (c₁' h a) * j₂ (f (c₂' h a)) := by
    intro h a
    conv_lhs => rw [hdec (h.1 a)]
    simp [c₁', c₂']
  let Θ : EqvHom ρ ρ₁ → {p : Bool × Bool // p ≠ (true, true)} := fun h =>
    ⟨(decide (c₁' h = 1), decide (c₂' h = 1)), by
      intro hp
      simp only [Prod.mk.injEq, decide_eq_true_eq] at hp
      apply h.2.2
      ext a
      rw [hrec h a, hp.1, hp.2]
      simp⟩
  have hΘ : Function.Injective Θ := by
    intro h h' hh
    have hh' : (decide (c₁' h = 1), decide (c₂' h = 1)) =
        (decide (c₁' h' = 1), decide (c₂' h' = 1)) := congrArg Subtype.val hh
    simp only [Prod.mk.injEq, decide_eq_decide] at hh'
    have e₁ : c₁' h = c₁' h' := IsNatSum.card_centralizer_dvd_six_aux_eq (hc₁ h) (hc₁ h') hh'.1
    have e₂ : c₂' h = c₂' h' := IsNatSum.card_centralizer_dvd_six_aux_eq (hc₂ h) (hc₂ h') hh'.2
    apply Subtype.ext
    ext a
    rw [hrec h a, hrec h' a, e₁, e₂]
  have hcard : Nat.card (EqvHom ρ ρ₁) ≤ 3 := by
    calc Nat.card (EqvHom ρ ρ₁) ≤ Nat.card {p : Bool × Bool // p ≠ (true, true)} :=
          Nat.card_le_card_of_injective Θ hΘ
      _ = 3 := by
        rw [Nat.card_eq_fintype_card]
        decide
  haveI : Finite (EqvHom ρ ρ₁) := by
    refine Finite.of_injective (fun h : EqvHom ρ ρ₁ => (h.1 : N₁ → G)) ?_
    intro h h' hh
    exact Subtype.ext (DFunLike.coe_injective hh)
  have hinj : Function.Injective (MulAction.toPermHom
      (Subgroup.centralizer (ρ.range : Set (MulAut G))) (EqvHom ρ ρ₁)) := by
    rw [injective_iff_map_eq_one]
    intro α hα
    obtain ⟨a₀, ha₀⟩ := exists_ne (1 : N₁)
    let ι₁ : EqvHom ρ ρ₁ := ⟨j₁, hρ₁, fun h => ha₀ (hj₁ (by
      have := congrArg (fun φ : N₁ →* G => φ a₀) h
      simpa using this))⟩
    let ι₂ : EqvHom ρ ρ₁ := ⟨j₂.comp f.toMonoidHom, fun l a => by
      show j₂ (f (ρ₁ l a)) = ρ l (j₂ (f a))
      rw [hf, hρ₂], fun h => ha₀ (f.injective (hj₂ (by
      have := congrArg (fun φ : N₁ →* G => φ a₀) h
      simpa using this)))⟩
    have e₁ : α • ι₁ = ι₁ := congrArg (fun p : Equiv.Perm (EqvHom ρ ρ₁) => p ι₁) hα
    have e₂ : α • ι₂ = ι₂ := congrArg (fun p : Equiv.Perm (EqvHom ρ ρ₁) => p ι₂) hα
    have h₁ : ∀ a, α.1 (j₁ a) = j₁ a := fun a => congrArg (fun h : EqvHom ρ ρ₁ => h.1 a) e₁
    have h₂ : ∀ b, α.1 (j₂ b) = j₂ b := fun b => by
      have h3 : α.1 (j₂ (f (f.symm b))) = j₂ (f (f.symm b)) :=
        congrArg (fun h : EqvHom ρ ρ₁ => h.1 (f.symm b)) e₂
      simpa using h3
    apply Subtype.ext
    ext g
    rw [hdec g, map_mul, h₁, h₂]
    rfl
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_perm] at hdvd
  refine hdvd.trans ?_
  interval_cases h : Nat.card (EqvHom ρ ρ₁) <;> decide

theorem IsNatSum.card_centralizer_dvd_six_aux_one [Finite G] (ρ : Lg →* MulAut G)
    (ρ₁ : Lg →* MulAut N₁) (j₁ : N₁ →* G) (hj₁ : Function.Injective j₁)
    (hsurj : Function.Surjective j₁) (hρ₁ : ∀ l a, j₁ (ρ₁ l a) = ρ l (j₁ a))
    (c₁ : Nat.card N₁ = 8) (r₁ : Nat.card ρ₁.range = 168) :
    Nat.card (Subgroup.centralizer (ρ.range : Set (MulAut G))) ∣ 6 := by
  haveI : Finite N₁ := Finite.of_injective j₁ hj₁
  haveI : Nontrivial N₁ := Finite.one_lt_card_iff_nontrivial.1 (by rw [c₁]; norm_num)
  let e : N₁ ≃* G := MulEquiv.ofBijective j₁ ⟨hj₁, hsurj⟩
  have he : ∀ a, e a = j₁ a := fun a => rfl
  have htriv : ∀ α : MulAut G, α ∈ Subgroup.centralizer (ρ.range : Set (MulAut G)) → α = 1 := by
    intro α hα
    let φ : N₁ →* N₁ := e.symm.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom)
    have hφ : ∀ l n, φ (ρ₁ l n) = ρ₁ l (φ n) := by
      intro l n
      have hs : ∀ g, e.symm (ρ l g) = ρ₁ l (e.symm g) := by
        intro g
        apply e.injective
        rw [MulEquiv.apply_symm_apply, he, hρ₁, ← he, MulEquiv.apply_symm_apply]
      show e.symm (α (e (ρ₁ l n))) = ρ₁ l (e.symm (α (e n)))
      rw [he, hρ₁, IsNatSum.card_centralizer_dvd_six_aux_comm ρ hα, ← he, hs]
    rcases IsNatSum.fixed_eq_one_aux_endo_rho ρ₁ c₁ r₁ hφ with h1 | h1
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : N₁)
      have h2 : e.symm (α (e a)) = 1 := by
        have := congrArg (fun ψ : N₁ →* N₁ => ψ a) h1
        simpa [φ] using this
      have h3 : α (e a) = 1 := by simpa using h2
      exact ha (e.injective (by simpa using α.injective (h3.trans (map_one α).symm)))
    · ext g
      obtain ⟨a, rfl⟩ := e.surjective g
      have := congrArg (fun ψ : N₁ →* N₁ => ψ a) h1
      have h4 : e.symm (α (e a)) = a := by simpa [φ] using this
      have h5 : α (e a) = e a := by simpa using congrArg e h4
      simpa using h5
  haveI : Subsingleton (Subgroup.centralizer (ρ.range : Set (MulAut G))) :=
    ⟨fun α β => Subtype.ext ((htriv _ α.2).trans (htriv _ β.2).symm)⟩
  rw [Nat.card_of_subsingleton 1]
  exact one_dvd 6

end Abstract3

section XLevel

variable {X : Type} [Group X] [Finite X]

theorem IsNatSum.card_centralizer_dvd_six_aux_range {L N : Subgroup X}
    (hN : IsNaturalLThreeTwo L N) : Nat.card (actOn L N hN.2.2.1).range = 168 := by
  have h := hN.2.2.1
  rw [← Subgroup.index_ker]
  have hker : (actOn L N h).ker = (Subgroup.centralizer (N : Set X)).subgroupOf L := by
    unfold actOn
    rw [← MonoidHom.comap_ker, Subgroup.normalizerMonoidHom_ker]
    ext l
    simp [Subgroup.mem_subgroupOf]
  rw [hker]
  exact hN.2.2.2

theorem IsNatSum.card_centralizer_dvd_six_aux_card {L N : Subgroup X}
    (hN : IsNaturalLThreeTwo L N) : Nat.card N = 8 := by
  rw [hN.2.1]; norm_num

theorem IsNatSum.card_centralizer_dvd_six_aux_mem_sup {s t : Subgroup X}
    (hc : ∀ a ∈ s, ∀ b ∈ t, a * b = b * a) {x : X} (hx : x ∈ s ⊔ t) :
    ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro y (h | h)
    · exact ⟨y, h, 1, t.one_mem, by simp⟩
    · exact ⟨1, s.one_mem, y, h, by simp⟩
  · exact ⟨1, s.one_mem, 1, t.one_mem, by simp⟩
  · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
    refine ⟨y₁ * y₂, s.mul_mem hy₁ hy₂, z₁ * z₂, t.mul_mem hz₁ hz₂, ?_⟩
    calc y₁ * y₂ * (z₁ * z₂) = y₁ * (y₂ * z₁) * z₂ := by group
      _ = y₁ * (z₁ * y₂) * z₂ := by rw [hc y₂ hy₂ z₁ hz₁]
      _ = y₁ * z₁ * (y₂ * z₂) := by group
  · rintro _ _ ⟨y, hy, z, hz, rfl⟩
    refine ⟨y⁻¹, s.inv_mem hy, z⁻¹, t.inv_mem hz, ?_⟩
    calc y⁻¹ * z⁻¹ = (z * y)⁻¹ := by group
      _ = (y * z)⁻¹ := by rw [hc y hy z hz]

theorem IsNatSum.fixed_eq_one_aux_le_normalizer {L U : Subgroup X} (h : IsNatSum L U) :
    L ≤ Subgroup.normalizer (U : Set X) := by
  obtain ⟨N₁, N₂, hN₁, hsup, h2⟩ := h
  subst hsup
  have h1 : L ≤ Subgroup.normalizer (N₁ : Set X) := hN₁.2.2.1
  have h2' : L ≤ Subgroup.normalizer (N₂ : Set X) := by
    rcases h2 with rfl | ⟨hN₂, _⟩
    · rw [Subgroup.normalizer_eq_top]; exact le_top
    · exact hN₂.2.2.1
  exact le_trans (le_inf h1 h2') (Subgroup.inf_normalizer_le_normalizer_sup N₁ N₂)

theorem IsNatSum.card_centralizer_dvd_six_of_comm {L U : Subgroup X} (h : IsNatSum L U)
    (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hn : L ≤ Subgroup.normalizer (U : Set X)) :
    Nat.card (Subgroup.centralizer
      (((actOn L U hn).range : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))) ∣ 6 := by
  obtain ⟨N₁, N₂, hN₁, hsup, h2⟩ := h
  have hN₁U : N₁ ≤ U := hsup ▸ le_sup_left
  have hn₁ : L ≤ Subgroup.normalizer (N₁ : Set X) := hN₁.2.2.1
  have hρ₁ : ∀ (l : L) (a : N₁), Subgroup.inclusion hN₁U (actOn L N₁ hn₁ l a) =
      actOn L U hn l (Subgroup.inclusion hN₁U a) := fun l a => Subtype.ext rfl
  rcases h2 with rfl | ⟨hN₂, hinf, f, hf⟩
  · have hUeq : N₁ = U := by rw [← hsup, sup_bot_eq]
    subst hUeq
    refine IsNatSum.card_centralizer_dvd_six_aux_one (actOn L N₁ hn) (actOn L N₁ hn₁)
      (Subgroup.inclusion hN₁U) (Subgroup.inclusion_injective hN₁U) ?_ hρ₁
      (IsNatSum.card_centralizer_dvd_six_aux_card hN₁)
      (IsNatSum.card_centralizer_dvd_six_aux_range hN₁)
    intro g
    exact ⟨g, Subtype.ext rfl⟩
  · have hN₂U : N₂ ≤ U := hsup ▸ le_sup_right
    have hn₂ : L ≤ Subgroup.normalizer (N₂ : Set X) := hN₂.2.2.1
    have hρ₂ : ∀ (l : L) (b : N₂), Subgroup.inclusion hN₂U (actOn L N₂ hn₂ l b) =
        actOn L U hn l (Subgroup.inclusion hN₂U b) := fun l b => Subtype.ext rfl
    refine IsNatSum.card_centralizer_dvd_six_aux_two (G := ↥U)
      (fun a b => Subtype.ext (hab a a.2 b b.2)) (actOn L U hn) (actOn L N₁ hn₁) (actOn L N₂ hn₂)
      (Subgroup.inclusion hN₁U) (Subgroup.inclusion hN₂U) (Subgroup.inclusion_injective hN₁U)
      (Subgroup.inclusion_injective hN₂U) ?_ ?_ hρ₁ hρ₂
      (IsNatSum.card_centralizer_dvd_six_aux_card hN₁)
      (IsNatSum.card_centralizer_dvd_six_aux_range hN₁) f ?_
    · intro g
      have hg : (g : X) ∈ N₁ ⊔ N₂ := hsup ▸ g.2
      obtain ⟨y, hy, z, hz, hyz⟩ := IsNatSum.card_centralizer_dvd_six_aux_mem_sup
        (fun a ha b hb => hab a (hN₁U ha) b (hN₂U hb)) hg
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext hyz.symm⟩
    · intro a b hab'
      have h1 : (Subgroup.inclusion hN₁U a : X) ∈ N₁ ⊓ N₂ :=
        ⟨a.2, hab' ▸ b.2⟩
      rw [hinf] at h1
      exact Subtype.ext (Subgroup.mem_bot.1 h1)
    · intro l a
      exact Subtype.ext (hf l l.2 a (actOn L N₁ hn₁ l a) rfl)

theorem IsNatSum.fixed_eq_one_of_comm {L U : Subgroup X} (h : IsNatSum L U)
    (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {u : X} (hu : u ∈ U)
    (hfix : ∀ l ∈ L, l * u * l⁻¹ = u) : u = 1 := by
  have hn : L ≤ Subgroup.normalizer (U : Set X) := IsNatSum.fixed_eq_one_aux_le_normalizer h
  obtain ⟨N₁, N₂, hN₁, hsup, h2⟩ := h
  have hN₁U : N₁ ≤ U := hsup ▸ le_sup_left
  have hn₁ : L ≤ Subgroup.normalizer (N₁ : Set X) := hN₁.2.2.1
  have hρ₁ : ∀ (l : L) (a : N₁), Subgroup.inclusion hN₁U (actOn L N₁ hn₁ l a) =
      actOn L U hn l (Subgroup.inclusion hN₁U a) := fun l a => Subtype.ext rfl
  have hf₁ : ∀ n : N₁, (∀ l : L, actOn L N₁ hn₁ l n = n) → n = 1 := fun n hn' =>
    IsNatSum.fixed_eq_one_aux_fixed_rho (actOn L N₁ hn₁)
      (IsNatSum.card_centralizer_dvd_six_aux_card hN₁)
      (IsNatSum.card_centralizer_dvd_six_aux_range hN₁) hn'
  rcases h2 with rfl | ⟨hN₂, hinf, f, hf⟩
  · have hUeq : N₁ = U := by rw [← hsup, sup_bot_eq]
    subst hUeq
    have := hf₁ ⟨u, hu⟩ (fun l => Subtype.ext (hfix l l.2))
    exact congrArg Subtype.val this
  · have hN₂U : N₂ ≤ U := hsup ▸ le_sup_right
    have hn₂ : L ≤ Subgroup.normalizer (N₂ : Set X) := hN₂.2.2.1
    have hρ₂ : ∀ (l : L) (b : N₂), Subgroup.inclusion hN₂U (actOn L N₂ hn₂ l b) =
        actOn L U hn l (Subgroup.inclusion hN₂U b) := fun l b => Subtype.ext rfl
    have hf₂ : ∀ n : N₂, (∀ l : L, actOn L N₂ hn₂ l n = n) → n = 1 := fun n hn' =>
      IsNatSum.fixed_eq_one_aux_fixed_rho (actOn L N₂ hn₂)
        (IsNatSum.card_centralizer_dvd_six_aux_card hN₂)
        (IsNatSum.card_centralizer_dvd_six_aux_range hN₂) hn'
    have key := IsNatSum.fixed_eq_one_aux_two (G := ↥U)
      (fun a b => Subtype.ext (hab a a.2 b b.2)) (actOn L U hn) (actOn L N₁ hn₁) (actOn L N₂ hn₂)
      (Subgroup.inclusion hN₁U) (Subgroup.inclusion hN₂U) (Subgroup.inclusion_injective hN₁U)
      (Subgroup.inclusion_injective hN₂U) ?_ ?_ hρ₁ hρ₂ hf₁ hf₂
      (g := ⟨u, hu⟩) (fun l => Subtype.ext (hfix l l.2))
    · exact congrArg Subtype.val key
    · intro g
      have hg : (g : X) ∈ N₁ ⊔ N₂ := hsup ▸ g.2
      obtain ⟨y, hy, z, hz, hyz⟩ := IsNatSum.card_centralizer_dvd_six_aux_mem_sup
        (fun a ha b hb => hab a (hN₁U ha) b (hN₂U hb)) hg
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext hyz.symm⟩
    · intro a b hab'
      have h1 : (Subgroup.inclusion hN₁U a : X) ∈ N₁ ⊓ N₂ :=
        ⟨a.2, hab' ▸ b.2⟩
      rw [hinf] at h1
      exact Subtype.ext (Subgroup.mem_bot.1 h1)

theorem sevenElement_centralizes_of_isNatSum_of_comm {L U : Subgroup X}
    (hLU : L ≤ Subgroup.normalizer (U : Set X)) (h : IsNatSum L U)
    (hab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) {x : X}
    (hx : x ∈ Subgroup.normalizer (U : Set X))
    (hcomm : ∀ l ∈ L, ∀ u ∈ U, x * (l * u * l⁻¹) * x⁻¹ = l * (x * u * x⁻¹) * l⁻¹)
    (h7 : ∃ k : ℕ, orderOf x = 7 ^ k) : ∀ u ∈ U, x * u * x⁻¹ = u := by
  obtain ⟨k, hk⟩ := h7
  set α : MulAut ↥U := Subgroup.normalizerMonoidHom U ⟨x, hx⟩ with hα
  have hαC : α ∈ Subgroup.centralizer
      (((actOn L U hLU).range : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, rfl⟩
    ext u
    show l * (x * u * x⁻¹) * (l : X)⁻¹ = x * (l * u * (l : X)⁻¹) * x⁻¹
    exact (hcomm l l.2 u u.2).symm
  have hdvd6 := IsNatSum.card_centralizer_dvd_six_of_comm h hab hLU
  have h1 : orderOf α ∣ 6 := by
    have : orderOf (⟨α, hαC⟩ : Subgroup.centralizer
        (((actOn L U hLU).range : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))) ∣ Nat.card _ :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at this
    exact this.trans hdvd6
  have h2 : orderOf α ∣ 7 ^ k := by
    rw [← hk]
    have := orderOf_map_dvd (Subgroup.normalizerMonoidHom U)
      (⟨x, hx⟩ : Subgroup.normalizer (U : Set X))
    rw [Subgroup.orderOf_mk] at this
    exact this
  have hcop : Nat.Coprime (7 ^ k) 6 := Nat.Coprime.pow_left _ (by norm_num)
  have h3 : orderOf α = 1 := Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
  have hα1 : α = 1 := orderOf_eq_one_iff.1 h3
  intro u hu
  have := congrArg (fun β : MulAut ↥U => ((β ⟨u, hu⟩ : U) : X)) hα1
  exact this

theorem IsNatSum.conj_aux_centralizer (m : X) (N : Subgroup X) :
    Subgroup.centralizer ((conjSub m N : Subgroup X) : Set X) =
      conjSub m (Subgroup.centralizer (N : Set X)) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx
    refine ⟨m⁻¹ * x * m, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro n hn
      have := hx (m * n * m⁻¹) ⟨n, hn, rfl⟩
      calc n * (m⁻¹ * x * m) = m⁻¹ * (m * n * m⁻¹ * x) * m := by group
        _ = m⁻¹ * (x * (m * n * m⁻¹)) * m := by rw [this]
        _ = m⁻¹ * x * m * n := by group
    · show m * (m⁻¹ * x * m) * m⁻¹ = x
      group
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 hc) n hn
    show m * n * m⁻¹ * (m * c * m⁻¹) = m * c * m⁻¹ * (m * n * m⁻¹)
    calc m * n * m⁻¹ * (m * c * m⁻¹) = m * (n * c) * m⁻¹ := by group
      _ = m * (c * n) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * (m * n * m⁻¹) := by group

theorem IsNatSum.conj_aux_natural {L N : Subgroup X} (m : X) (hN : IsNaturalLThreeTwo L N) :
    IsNaturalLThreeTwo (conjSub m L) (conjSub m N) := by
  obtain ⟨⟨hcomm, hexp⟩, hcard, hnorm, hrel⟩ := hN
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨a', ha'⟩ : N) ⟨b', hb'⟩))
  · rintro _ ⟨x, hx, rfl⟩
    show ((MulAut.conj m) x) ^ 2 = 1
    rw [← map_pow, hexp x hx, map_one]
  · rw [conjSub, Subgroup.card_map_of_injective hinj]; exact hcard
  · exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)
  · rw [IsNatSum.conj_aux_centralizer, conjSub, conjSub,
      Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact hrel

theorem IsNatSum.conj {L U : Subgroup X} (h : IsNatSum L U) (m : X) :
    IsNatSum (conjSub m L) (conjSub m U) := by
  obtain ⟨N₁, N₂, hN₁, hsup, h2⟩ := h
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  refine ⟨conjSub m N₁, conjSub m N₂, IsNatSum.conj_aux_natural m hN₁, ?_, ?_⟩
  · rw [← hsup]; exact (Subgroup.map_sup _ _ _).symm
  · rcases h2 with rfl | ⟨hN₂, hinf, f, hf⟩
    · exact Or.inl (Subgroup.map_bot _)
    · refine Or.inr ⟨IsNatSum.conj_aux_natural m hN₂, ?_, ?_⟩
      · rw [conjSub, conjSub, ← Subgroup.map_inf _ _ _ hinj, hinf, Subgroup.map_bot]
      · let e₁ : ↥N₁ ≃* ↥(conjSub m N₁) :=
          Subgroup.equivMapOfInjective N₁ (MulAut.conj m).toMonoidHom hinj
        let e₂ : ↥N₂ ≃* ↥(conjSub m N₂) :=
          Subgroup.equivMapOfInjective N₂ (MulAut.conj m).toMonoidHom hinj
        refine ⟨e₁.symm.trans (f.trans e₂), ?_⟩
        rintro _ ⟨l, hl, rfl⟩ a b hab
        obtain ⟨a₀, rfl⟩ := e₁.surjective a
        obtain ⟨b₀, rfl⟩ := e₁.surjective b
        have ha : ((e₁ a₀ : conjSub m N₁) : X) = m * a₀ * m⁻¹ := rfl
        have hb : ((e₁ b₀ : conjSub m N₁) : X) = m * b₀ * m⁻¹ := rfl
        have h1 : (b₀ : X) = l * a₀ * l⁻¹ := by
          have := hab
          rw [ha, hb] at this
          show (b₀ : X) = l * a₀ * l⁻¹
          have h' : m * (b₀ : X) * m⁻¹ = (m * l * m⁻¹) * (m * a₀ * m⁻¹) * (m * l * m⁻¹)⁻¹ := this
          have h'' : (b₀ : X) = m⁻¹ * ((m * l * m⁻¹) * (m * a₀ * m⁻¹) * (m * l * m⁻¹)⁻¹) * m := by
            rw [← h']; group
          rw [h'']; group
        have h2 := hf l hl a₀ b₀ h1
        have key : ∀ a₀ : N₁, (e₁.symm.trans (f.trans e₂)) (e₁ a₀) = e₂ (f a₀) := by
          intro a₀
          simp
        rw [key, key]
        change ((e₂ (f b₀) : conjSub m N₂) : X) =
          (m * l * m⁻¹) * ((e₂ (f a₀) : conjSub m N₂) : X) * (m * l * m⁻¹)⁻¹
        have e2a : ((e₂ (f a₀) : conjSub m N₂) : X) = m * (f a₀ : X) * m⁻¹ := rfl
        have e2b : ((e₂ (f b₀) : conjSub m N₂) : X) = m * (f b₀ : X) * m⁻¹ := rfl
        rw [e2a, e2b, h2]; group

end XLevel

section C2

variable {X : Type} [Group X] [Finite X]

theorem IsC2.hom_eq_one_of_card_dvd_six_aux_comm {K : Type} [Group K] [Finite K]
    (h : Nat.card K ∣ 3) (a b : K) : a * b = b * a := by
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 h with h1 | h3
  · haveI : Subsingleton K := (Nat.card_eq_one_iff_unique.1 h1).1
    exact Subsingleton.elim _ _
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : IsCyclic K := isCyclic_of_prime_card h3
    exact mul_comm' a b

theorem IsC2.hom_eq_one_of_card_dvd_six_aux_gen {K : Type} [Group K] [Finite K]
    (hK : Nat.card K ∣ 6) (S : Set K) (hS : ∀ s ∈ S, Odd (orderOf s))
    (hgen : Subgroup.closure S = ⊤) : Nat.card K ∣ 3 := by
  by_contra h3
  have key : ∀ P : Subgroup K, P.index = 2 → False := by
    intro P hP
    have hSP : S ⊆ P := by
      intro s hs
      obtain ⟨k, hk⟩ := hS s hs
      have h1 : s * s ^ (2 * k) = 1 := by
        rw [← pow_succ', ← hk]
        exact pow_orderOf_eq_one s
      have h2 : s ^ (2 * k) = s⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h3 : s = (s⁻¹ * s⁻¹) ^ k := by
        rw [← sq, ← pow_mul, inv_pow, h2, inv_inv]
      rw [h3]
      exact P.pow_mem (Subgroup.mul_self_mem_of_index_two hP s⁻¹) k
    have : (⊤ : Subgroup K) ≤ P := hgen ▸ (Subgroup.closure_le P).2 hSP
    have hPtop : P = ⊤ := top_le_iff.1 this
    rw [hPtop, Subgroup.index_top] at hP
    omega
  have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) hK
  have hpos : 0 < Nat.card K := Nat.card_pos
  interval_cases hc : Nat.card K
  · exact h3 (by norm_num)
  · exact key ⊥ (by rw [Subgroup.index_bot, hc])
  · exact h3 (by norm_num)
  · omega
  · omega
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 (by rw [hc]; norm_num)
    refine key (Subgroup.zpowers y) ?_
    have h1 := Subgroup.index_mul_card (Subgroup.zpowers y)
    rw [Nat.card_zpowers, hy, hc] at h1
    omega

theorem IsC2.hom_eq_one_of_card_dvd_six {L : Subgroup X} (hL : IsC2 L) {H : Type} [Group H]
    (ψ : ↥L →* H) (hH : Nat.card H ∣ 6) : ψ = 1 := by
  obtain ⟨-, hodd, hcomp⟩ := hL
  let ψ' : ↥L →* ↥ψ.range := ψ.rangeRestrict
  have hsurj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  haveI : Finite ψ.range := Finite.of_surjective ψ' hsurj
  have hK : Nat.card ψ.range ∣ 6 := (Subgroup.card_subgroup_dvd_card ψ.range).trans hH
  have hTgen : Subgroup.closure {y : ↥L | Odd (orderOf y)} = ⊤ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective L)
    have himg : L.subtype '' {y : ↥L | Odd (orderOf y)} = {x : X | x ∈ L ∧ Odd (orderOf x)} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, by simpa [Subgroup.orderOf_coe] using hy⟩
      · rintro ⟨hx, hx'⟩
        exact ⟨⟨x, hx⟩, by simpa [Subgroup.orderOf_coe] using hx', rfl⟩
    rw [MonoidHom.map_closure, himg, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hodd
  have hKgen : Subgroup.closure (ψ' '' {y : ↥L | Odd (orderOf y)}) = ⊤ := by
    rw [← MonoidHom.map_closure, hTgen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 hsurj
  have hKodd : ∀ s ∈ ψ' '' {y : ↥L | Odd (orderOf y)}, Odd (orderOf s) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Odd.of_dvd_nat hy (orderOf_map_dvd ψ' y)
  have hK3 : Nat.card ψ.range ∣ 3 :=
    IsC2.hom_eq_one_of_card_dvd_six_aux_gen hK _ hKodd hKgen
  have hcomm := IsC2.hom_eq_one_of_card_dvd_six_aux_comm hK3
  let Kψ : Subgroup X := ψ'.ker.map L.subtype
  have hmem : ∀ x (hx : x ∈ L), x ∈ Kψ ↔ ψ' ⟨x, hx⟩ = 1 := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hcL : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ L := fun a ha b hb => by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
  have hLL : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.2 hcL
  have hcommutator : ⁅L, L⁆ ≤ Kψ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [hmem _ (hcL a ha b hb)]
    have : (⟨⁅a, b⁆, hcL a ha b hb⟩ : ↥L) = ⁅(⟨a, ha⟩ : ↥L), ⟨b, hb⟩⁆ := Subtype.ext rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
  have hpcore : ∀ y (hy : y ∈ L), y ∈ CFSG.pCore 2 X → y ∈ Kψ := by
    intro y hy hyp
    rw [hmem y hy]
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨y, hyp⟩
    have hy2 : (⟨y, hy⟩ : ↥L) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hord : orderOf (ψ' ⟨y, hy⟩) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hy2, map_one]
    have hord3 : orderOf (ψ' ⟨y, hy⟩) ∣ 3 := (_root_.orderOf_dvd_natCard _).trans hK3
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
    have h1 := Nat.dvd_gcd hord hord3
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h1
    exact orderOf_eq_one_iff.1 h1
  have hperf : _root_.commutator ↥(L.map (QuotientGroup.mk' (CFSG.pCore 2 X))) = ⊤ := hcomp.2.2.1
  have hLπ : (⁅L, L⁆).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      L.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    rw [Subgroup.map_commutator]
    have h1 := congrArg (Subgroup.map (L.map (QuotientGroup.mk' (CFSG.pCore 2 X))).subtype) hperf
    rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    rw [h1]
  have hall : ∀ x ∈ L, x ∈ Kψ := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 X) x ∈
        (⁅L, L⁆).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
      rw [hLπ]; exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨c, hc, hcx⟩ := h1
    have hcL' : c ∈ L := hLL hc
    have hy : x * c⁻¹ ∈ CFSG.pCore 2 X := by
      rw [← (QuotientGroup.ker_mk' (CFSG.pCore 2 X)), MonoidHom.mem_ker, map_mul, map_inv, ← hcx]
      group
    have : x = (x * c⁻¹) * c := by group
    rw [this]
    exact Kψ.mul_mem (hpcore _ (L.mul_mem hx (L.inv_mem hcL')) hy) (hcommutator hc)
  ext z
  have hz := (hmem z.1 z.2).1 (hall z.1 z.2)
  have : ψ z = ((ψ' z : ψ.range) : H) := rfl
  rw [this, show ψ' z = 1 from hz]
  rfl

end C2

section GnV

variable {X : Type} [Group X] [Finite X]

theorem comm_of_le_gnV {T : Subgroup X} (hX : GNSetting X T) {U : Subgroup X} (hU : U ≤ gnV T) :
    ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
  have hVea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  haveI := hVea.1
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm' (⟨x, hU hx⟩ : ↥(gnV T)) ⟨y, hU hy⟩)

end GnV

end CFSG.LocalAnalysis.RankThreeUC.S15
