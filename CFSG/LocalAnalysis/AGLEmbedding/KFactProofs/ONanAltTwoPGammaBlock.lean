module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Equiv Equiv.Perm

variable {Ω : Type} [DecidableEq Ω] {p : ℕ}

@[expose] def blockLabel (O : Finset Ω) (x : Ω) : ZMod 2 := if x ∈ O then 0 else 1

theorem zmod_two_aux : ∀ a b c : ZMod 2, a = b + c → b = a + c := by decide

omit [DecidableEq Ω] in
theorem perm_inv_apply_self' (σ : Perm Ω) (x : Ω) : σ⁻¹ (σ x) = x := Equiv.symm_apply_apply σ x

omit [DecidableEq Ω] in
theorem perm_apply_inv_self' (σ : Perm Ω) (x : Ω) : σ (σ⁻¹ x) = x := Equiv.apply_symm_apply σ x

theorem zmod_two_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem blockLabel_eq_iff {O : Finset Ω} {a b : Ω} :
    blockLabel O a = blockLabel O b ↔ (a ∈ O ↔ b ∈ O) := by
  unfold blockLabel
  by_cases ha : a ∈ O <;> by_cases hb : b ∈ O <;> simp only [ha, hb, ↓reduceIte] <;> decide

@[expose] def blockStab (O : Finset Ω) : Subgroup (Perm Ω) where
  carrier := {σ | ∃ c : ZMod 2, ∀ x, blockLabel O (σ x) = blockLabel O x + c}
  one_mem' := ⟨0, fun x => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d + c, fun x => by rw [Perm.mul_apply, hc, hd, add_assoc]⟩
  inv_mem' := by
    rintro σ ⟨c, hc⟩
    refine ⟨c, fun x => ?_⟩
    have h := hc (σ⁻¹ x)
    rw [perm_apply_inv_self'] at h
    exact zmod_two_aux _ _ _ h

theorem zmod_two_ne : ∀ a : ZMod 2, a + 1 ≠ a := by decide

theorem mem_blockStab_iff {O : Finset Ω} {σ : Perm Ω} :
    σ ∈ blockStab O ↔ (∀ x, x ∈ O ↔ σ x ∈ O) ∨ (∀ x, x ∈ O ↔ σ x ∉ O) := by
  constructor
  · rintro ⟨c, hc⟩
    rcases zmod_two_cases c with rfl | rfl
    · left
      intro x
      rw [← blockLabel_eq_iff, hc x, add_zero]
    · right
      intro x
      have hne : blockLabel O (σ x) ≠ blockLabel O x := by
        rw [hc x]
        exact zmod_two_ne _
      have hiff : ¬ (σ x ∈ O ↔ x ∈ O) := fun hh => hne (blockLabel_eq_iff.2 hh)
      tauto
  · rintro (h | h)
    · refine ⟨0, fun x => ?_⟩
      rw [add_zero, blockLabel_eq_iff]
      exact (h x).symm
    · refine ⟨1, fun x => ?_⟩
      unfold blockLabel
      by_cases hx : x ∈ O
      · have hy : σ x ∉ O := (h x).1 hx
        simp only [hx, hy, ↓reduceIte]
        decide
      · have hy : σ x ∈ O := by
          by_contra hy
          exact hx ((h x).2 hy)
        simp only [hx, hy, ↓reduceIte]
        decide

@[expose] def swapChar (O : Finset Ω) (x₀ : Ω) : blockStab O →* Multiplicative (ZMod 2) where
  toFun σ := Multiplicative.ofAdd (blockLabel O ((σ : Perm Ω) x₀) - blockLabel O x₀)
  map_one' := by
    show Multiplicative.ofAdd (blockLabel O ((1 : Perm Ω) x₀) - blockLabel O x₀) = 1
    simp
  map_mul' := by
    rintro ⟨σ, c, hc⟩ ⟨τ, d, hd⟩
    show Multiplicative.ofAdd (blockLabel O ((σ * τ) x₀) - blockLabel O x₀) =
      Multiplicative.ofAdd (blockLabel O (σ x₀) - blockLabel O x₀) *
        Multiplicative.ofAdd (blockLabel O (τ x₀) - blockLabel O x₀)
    rw [← ofAdd_add, Perm.mul_apply, hc (τ x₀), hc x₀]
    congr 1
    ring

theorem swapChar_eq_one_iff (O : Finset Ω) (x₀ : Ω) (σ : blockStab O) :
    swapChar O x₀ σ = 1 ↔ ∀ x, x ∈ O ↔ (σ : Perm Ω) x ∈ O := by
  obtain ⟨σ, c, hc⟩ := σ
  have h0 : blockLabel O (σ x₀) - blockLabel O x₀ = c := by
    rw [hc x₀]; ring
  show Multiplicative.ofAdd (blockLabel O (σ x₀) - blockLabel O x₀) = 1 ↔ _
  rw [h0]
  constructor
  · intro h x
    have hc0 : c = 0 := ofAdd_eq_one.1 h
    rw [← blockLabel_eq_iff, hc x, hc0, add_zero]
  · intro h
    have h1 : blockLabel O (σ x₀) = blockLabel O x₀ := blockLabel_eq_iff.2 (h x₀).symm
    rw [hc x₀] at h1
    have : c = 0 := by linear_combination h1
    exact ofAdd_eq_one.2 this

open scoped commutatorElement in
theorem eq_one_of_perfect {G : Type*} [Group G] {V : Subgroup G} (hV : ⁅V, V⁆ = V)
    {A : Type*} [CommGroup A] (f : ↥V →* A) (v : ↥V) : f v = 1 := by
  have hle : ⁅V, V⁆ ≤ f.ker.map V.subtype := by
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    refine ⟨⁅(⟨g₁, h₁⟩ : V), (⟨g₂, h₂⟩ : V)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  obtain ⟨w, hw, hwv⟩ := (le_of_eq hV.symm).trans hle v.2
  have : w = v := Subtype.ext hwv
  rw [← this]
  exact hw

structure TwoCycles (p : ℕ) (a₁ a₂ : Perm Ω) (O₁ O₂ : Finset Ω) : Prop where
  prime : p.Prime
  pow₁ : a₁ ^ p = 1
  pow₂ : a₂ ^ p = 1
  card₁ : O₁.card = p
  card₂ : O₂.card = p
  disj : Disjoint O₁ O₂
  cover : ∀ x, x ∈ O₁ ∨ x ∈ O₂
  moves₁ : ∀ x, a₁ x ≠ x ↔ x ∈ O₁
  moves₂ : ∀ x, a₂ x ≠ x ↔ x ∈ O₂

namespace TwoCycles

variable {a₁ a₂ : Perm Ω} {O₁ O₂ : Finset Ω}

omit [DecidableEq Ω] in
theorem symm (h : TwoCycles p a₁ a₂ O₁ O₂) : TwoCycles p a₂ a₁ O₂ O₁ :=
  ⟨h.prime, h.pow₂, h.pow₁, h.card₂, h.card₁, h.disj.symm, fun x => (h.cover x).symm,
    h.moves₂, h.moves₁⟩

omit [DecidableEq Ω] in
theorem mem_snd_iff (h : TwoCycles p a₁ a₂ O₁ O₂) (y : Ω) : y ∈ O₂ ↔ y ∉ O₁ :=
  ⟨fun h' h'' => Finset.disjoint_left.1 h.disj h'' h', fun h' => (h.cover y).resolve_left h'⟩

theorem snd_apply_of_mem_fst (h : TwoCycles p a₁ a₂ O₁ O₂) {x : Ω} (hx : x ∈ O₁) : a₂ x = x := by
  by_contra hne
  exact Finset.disjoint_left.1 h.disj hx ((h.moves₂ x).1 hne)

theorem exists_zpow_mul_zpow (h : TwoCycles p a₁ a₂ O₁ O₂) {g : Perm Ω} (hg₁ : g * a₁ = a₁ * g)
    (hg₂ : g * a₂ = a₂ * g) : ∃ i j : ℤ, g = a₁ ^ i * a₂ ^ j :=
  CFSG.AGLEmbeddingD2.AltSurvivor.exists_zpow_mul_zpow_eq
    (isCycle_of_moves h.prime h.pow₁ h.card₁ h.moves₁)
    (isCycle_of_moves h.prime h.pow₂ h.card₂ h.moves₂) h.moves₁ h.moves₂ h.disj h.cover hg₁ hg₂

end TwoCycles

theorem exists_mem_apply_eq_of_moves (hp : p.Prime) {a : Perm Ω} {O : Finset Ω}
    (ha : a ^ p = 1) (hO : O.card = p) (hma : ∀ x, a x ≠ x ↔ x ∈ O)
    {Q : Subgroup (Perm Ω)} {q : Perm Ω} (hq : q ∈ Q) {i : ℤ} (hqz : ∀ z ∈ O, q z = (a ^ i) z)
    {x' : Ω} (hx' : x' ∈ O) (hqx' : q x' ≠ x') {x y : Ω} (hx : x ∈ O) (hy : y ∈ O) :
    ∃ u ∈ Q, u x = y := by
  have hcp : (a ^ i) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
  have hcomm : ∀ k : ℕ, (a ^ i) * a ^ k = a ^ k * (a ^ i) := fun k =>
    (((Commute.refl a).zpow_left i).pow_right k).eq
  have hmc : ∀ z, (a ^ i) z ≠ z ↔ z ∈ O := by
    intro z
    constructor
    · intro hz
      by_contra hzO
      apply hz
      have : a z = z := by
        by_contra h
        exact hzO ((hma z).1 h)
      exact Perm.zpow_apply_eq_self_of_apply_eq_self this i
    · intro hz hcz
      obtain ⟨k, hk⟩ := exists_pow_apply_eq_of_moves hp ha hO hma hx' hz
      apply hqx'
      rw [hqz x' hx']
      have h1 : (a ^ i) ((a ^ k) x') = (a ^ k) ((a ^ i) x') := by
        have := congrArg (fun f : Perm Ω => f x') (hcomm k)
        simpa [Perm.mul_apply] using this
      rw [hk, hcz] at h1
      apply (a ^ k).injective
      rw [← h1, hk]
  obtain ⟨k, hk⟩ := exists_pow_apply_eq_of_moves hp hcp hO hmc hx hy
  have hpow : ∀ n : ℕ, ∀ z ∈ O, (q ^ n) z = ((a ^ i) ^ n) z := by
    intro n
    induction n with
    | zero => intro z hz; simp
    | succ n ih =>
      intro z hz
      rw [pow_succ', pow_succ', Perm.mul_apply, Perm.mul_apply, ih z hz]
      exact hqz _ (pow_apply_mem_of_moves hmc hz n)
  exact ⟨q ^ k, Subgroup.pow_mem Q hq k, by rw [hpow k x hx]; exact hk⟩

section Normalizer

variable {a₁ a₂ : Perm Ω} {O₁ O₂ : Finset Ω} {Q : Subgroup (Perm Ω)}

theorem exists_restrict (h : TwoCycles p a₁ a₂ O₁ O₂) (hQ₁ : ∀ q ∈ Q, q * a₁ = a₁ * q)
    (hQ₂ : ∀ q ∈ Q, q * a₂ = a₂ * q) {q : Perm Ω} (hq : q ∈ Q) :
    (∃ i : ℤ, ∀ z ∈ O₁, q z = (a₁ ^ i) z) ∧ (∃ j : ℤ, ∀ z ∈ O₂, q z = (a₂ ^ j) z) := by
  obtain ⟨i, j, hij⟩ := h.exists_zpow_mul_zpow (hQ₁ q hq) (hQ₂ q hq)
  have hcomm : Commute a₁ a₂ := by
    refine Perm.Disjoint.commute fun x => ?_
    by_cases hx : x ∈ O₁
    · right; exact h.snd_apply_of_mem_fst hx
    · left
      by_contra hne
      exact hx ((h.moves₁ x).1 hne)
  refine ⟨⟨i, fun z hz => ?_⟩, ⟨j, fun z hz => ?_⟩⟩
  · rw [hij, Perm.mul_apply, Perm.zpow_apply_eq_self_of_apply_eq_self (h.snd_apply_of_mem_fst hz)]
  · have hz1 : a₁ z = z := by
      by_contra hne
      exact Finset.disjoint_left.1 h.disj ((h.moves₁ z).1 hne) hz
    rw [hij, (hcomm.zpow_zpow i j).eq, Perm.mul_apply,
      Perm.zpow_apply_eq_self_of_apply_eq_self hz1]

omit [DecidableEq Ω] in
theorem exists_mem_apply_eq_map {τ : Perm Ω} (hτ : τ ∈ Subgroup.normalizer (Q : Set (Perm Ω)))
    {x y : Ω} (hxy : ∃ u ∈ Q, u x = y) : ∃ u ∈ Q, u (τ x) = τ y := by
  obtain ⟨u, hu, rfl⟩ := hxy
  exact ⟨τ * u * τ⁻¹, (Subgroup.mem_normalizer_iff.1 hτ u).1 hu, by
    rw [Perm.mul_apply, Perm.mul_apply, perm_inv_apply_self']⟩

theorem preserves_of_fixes_other (h : TwoCycles p a₁ a₂ O₁ O₂)
    (hQ₁ : ∀ q ∈ Q, q * a₁ = a₁ * q) (hQ₂ : ∀ q ∈ Q, q * a₂ = a₂ * q)
    (hfix : ∀ q ∈ Q, ∀ x ∈ O₂, q x = x) (hmv : ∃ q ∈ Q, ∃ x ∈ O₁, q x ≠ x) {σ : Perm Ω}
    (hσ : σ ∈ Subgroup.normalizer (Q : Set (Perm Ω))) : ∀ x, x ∈ O₁ ↔ σ x ∈ O₁ := by
  classical
  obtain ⟨q₀, hq₀, x', hx', hq₀x'⟩ := hmv
  obtain ⟨⟨i, hi⟩, -⟩ := exists_restrict h hQ₁ hQ₂ hq₀
  have htrans : ∀ x ∈ O₁, ∀ y ∈ O₁, ∃ u ∈ Q, u x = y := fun x hx y hy =>
    exists_mem_apply_eq_of_moves h.prime h.pow₁ h.card₁ h.moves₁ hq₀ hi hx' hq₀x' hx hy
  have hD : ∀ x, (∃ y, y ≠ x ∧ ∃ u ∈ Q, u x = y) ↔ x ∈ O₁ := by
    intro x
    constructor
    · rintro ⟨y, hyx, u, hu, rfl⟩
      by_contra hx
      exact hyx (hfix u hu x ((h.cover x).resolve_left hx))
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.exists_mem_ne (by rw [h.card₁]; exact h.prime.one_lt) x
      exact ⟨y, hyx, htrans x hx y hy⟩
  have hDmap : ∀ τ ∈ Subgroup.normalizer (Q : Set (Perm Ω)), ∀ x,
      (∃ y, y ≠ x ∧ ∃ u ∈ Q, u x = y) → ∃ y, y ≠ τ x ∧ ∃ u ∈ Q, u (τ x) = y := by
    rintro τ hτ x ⟨y, hyx, hu⟩
    exact ⟨τ y, fun hτy => hyx (τ.injective hτy), exists_mem_apply_eq_map hτ hu⟩
  intro x
  rw [← hD x, ← hD (σ x)]
  refine ⟨hDmap σ hσ x, fun hx => ?_⟩
  have := hDmap σ⁻¹ (Subgroup.inv_mem _ hσ) (σ x) hx
  rw [perm_inv_apply_self'] at this
  exact this

theorem preserves_of_moves_both (h : TwoCycles p a₁ a₂ O₁ O₂)
    (hQ₁ : ∀ q ∈ Q, q * a₁ = a₁ * q) (hQ₂ : ∀ q ∈ Q, q * a₂ = a₂ * q)
    (hmv₁ : ∃ q ∈ Q, ∃ x ∈ O₁, q x ≠ x) (hmv₂ : ∃ q ∈ Q, ∃ x ∈ O₂, q x ≠ x) {σ : Perm Ω}
    (hσ : σ ∈ Subgroup.normalizer (Q : Set (Perm Ω))) :
    (∀ x, x ∈ O₁ ↔ σ x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ σ x ∉ O₁) := by
  classical
  have htrans₁ : ∀ x ∈ O₁, ∀ y ∈ O₁, ∃ u ∈ Q, u x = y := by
    obtain ⟨q₀, hq₀, x', hx', hq₀x'⟩ := hmv₁
    obtain ⟨⟨i, hi⟩, -⟩ := exists_restrict h hQ₁ hQ₂ hq₀
    exact fun x hx y hy =>
      exists_mem_apply_eq_of_moves h.prime h.pow₁ h.card₁ h.moves₁ hq₀ hi hx' hq₀x' hx hy
  have htrans₂ : ∀ x ∈ O₂, ∀ y ∈ O₂, ∃ u ∈ Q, u x = y := by
    obtain ⟨q₀, hq₀, x', hx', hq₀x'⟩ := hmv₂
    obtain ⟨-, ⟨j, hj⟩⟩ := exists_restrict h hQ₁ hQ₂ hq₀
    exact fun x hx y hy =>
      exists_mem_apply_eq_of_moves h.prime h.pow₂ h.card₂ h.moves₂ hq₀ hj hx' hq₀x' hx hy
  have hpres₁ : ∀ q ∈ Q, ∀ x, x ∈ O₁ ↔ q x ∈ O₁ := fun q hq x =>
    (CFSG.AGLEmbeddingD2.AltSurvivor.apply_mem_iff_of_commute h.moves₁ (hQ₁ q hq) x).symm
  have hpres₂ : ∀ q ∈ Q, ∀ x, x ∈ O₂ ↔ q x ∈ O₂ := fun q hq x =>
    (CFSG.AGLEmbeddingD2.AltSurvivor.apply_mem_iff_of_commute h.moves₂ (hQ₂ q hq) x).symm
  have hσ' : σ⁻¹ ∈ Subgroup.normalizer (Q : Set (Perm Ω)) := Subgroup.inv_mem _ hσ
  obtain ⟨x₀, hx₀⟩ : O₁.Nonempty := Finset.card_pos.1 (by rw [h.card₁]; exact h.prime.pos)
  rcases h.cover (σ x₀) with h1 | h2
  · left
    intro x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := htrans₁ x₀ hx₀ x hx
      obtain ⟨u', hu', hu'x⟩ := exists_mem_apply_eq_map hσ ⟨u, hu, rfl⟩
      rw [← hu'x]
      exact (hpres₁ u' hu' _).1 h1
    · intro hx
      obtain ⟨u, hu, hux⟩ := htrans₁ (σ x₀) h1 (σ x) hx
      obtain ⟨u', hu', hu'x⟩ := exists_mem_apply_eq_map hσ' ⟨u, hu, hux⟩
      rw [perm_inv_apply_self', perm_inv_apply_self'] at hu'x
      rw [← hu'x]
      exact (hpres₁ u' hu' _).1 hx₀
  · right
    intro x
    constructor
    · intro hx
      obtain ⟨u, hu, rfl⟩ := htrans₁ x₀ hx₀ x hx
      obtain ⟨u', hu', hu'x⟩ := exists_mem_apply_eq_map hσ ⟨u, hu, rfl⟩
      rw [← hu'x]
      exact (h.mem_snd_iff _).1 ((hpres₂ u' hu' _).1 h2)
    · intro hx
      have hx2 : σ x ∈ O₂ := (h.mem_snd_iff _).2 hx
      obtain ⟨u, hu, hux⟩ := htrans₂ (σ x₀) h2 (σ x) hx2
      obtain ⟨u', hu', hu'x⟩ := exists_mem_apply_eq_map hσ' ⟨u, hu, hux⟩
      rw [perm_inv_apply_self', perm_inv_apply_self'] at hu'x
      rw [← hu'x]
      exact (hpres₁ u' hu' _).1 hx₀

theorem mem_blockStab_of_mem_normalizer (h : TwoCycles p a₁ a₂ O₁ O₂)
    (hQ₁ : ∀ q ∈ Q, q * a₁ = a₁ * q) (hQ₂ : ∀ q ∈ Q, q * a₂ = a₂ * q) (hQne : Q ≠ ⊥)
    {σ : Perm Ω} (hσ : σ ∈ Subgroup.normalizer (Q : Set (Perm Ω))) : σ ∈ blockStab O₁ := by
  classical
  rw [mem_blockStab_iff]
  by_cases hmv₁ : ∃ q ∈ Q, ∃ x ∈ O₁, q x ≠ x
  · by_cases hmv₂ : ∃ q ∈ Q, ∃ x ∈ O₂, q x ≠ x
    · exact preserves_of_moves_both h hQ₁ hQ₂ hmv₁ hmv₂ hσ
    · left
      push Not at hmv₂
      exact preserves_of_fixes_other h hQ₁ hQ₂ hmv₂ hmv₁ hσ
  · by_cases hmv₂ : ∃ q ∈ Q, ∃ x ∈ O₂, q x ≠ x
    · left
      push Not at hmv₁
      have := preserves_of_fixes_other h.symm hQ₂ hQ₁ hmv₁ hmv₂ hσ
      intro x
      rw [← not_iff_not, ← h.mem_snd_iff, ← h.mem_snd_iff]
      exact this x
    · exfalso
      apply hQne
      rw [Subgroup.eq_bot_iff_forall]
      intro q hq
      push Not at hmv₁ hmv₂
      ext x
      show q x = x
      rcases h.cover x with hx | hx
      · exact hmv₁ q hq x hx
      · exact hmv₂ q hq x hx

end Normalizer

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
