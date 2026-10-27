module

public import CFSG.GH74.Generic.S1.LayerPair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open Subgroup CFSG.GH74.Filter.ClassicalOdd CFSG.GH74 CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG CFSG.LocalCores
open scoped commutatorElement

namespace CFSG.GH74.Generic.S1

theorem q3_false_of_two_factor {H : Type} [Group H] [Finite H] (hH : Gen4 H) {σ : H} (hσ : σ * σ = 1)
    {L : Subgroup H} (hAB : ⁅L, conjSub σ⁻¹ L⁆ = ⊥) {A' : Subgroup H}
    (hAD : (swapDiag hAB).range = A')
    (hAcen : ∀ z ∈ A', (∀ w ∈ A', z * w = w * z) → z = 1)
    (φ : Q8 →* H) (hφ : Function.Injective φ)
    (hφL : ∀ g, ∀ m ∈ L, φ g * m = m * φ g)
    (hφL' : ∀ g, ∀ m ∈ conjSub σ⁻¹ L, φ g * m = m * φ g)
    (ψ : Q8 →* H) (hψ : Function.Injective ψ) (hψA : ∀ g, ψ g ∈ A') : False := by
  classical
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  set L' := conjSub σ⁻¹ L with hL'
  set δ := swapDiag hAB with hδ
  have hδapply : ∀ l : ↥L, δ l = (l : H) * (σ⁻¹ * (l : H) * σ) := fun l => rfl
  have hmem' : ∀ x, x ∈ L' ↔ σ * x * σ⁻¹ ∈ L := fun x => by
    rw [hL', CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', inv_inv]
  have hσL : ∀ l ∈ L, σ⁻¹ * l * σ ∈ L' := fun l hl => conj_mem_conjSub hl
  have hLL' : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    commute_of_commutator_conj_eq_bot hAB ha hb
  set Et : Subgroup ↥L := ψ.range.comap δ with hEt
  have hψR : ∀ g, ψ g ∈ δ.range := fun g => hAD ▸ hψA g
  let eψ : Q8 ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  let g₁ : ↥Et →* ↥ψ.range := (δ.comp Et.subtype).codRestrict ψ.range (fun l => l.2)
  let β₁ : ↥Et →* V4 := q8Frattini.comp (eψ.symm.toMonoidHom.comp g₁)
  have hβ₁surj : Function.Surjective β₁ := by
    intro v
    obtain ⟨q, hq⟩ := q8Frattini_surjective v
    obtain ⟨l, hl⟩ := hψR q
    have hlE : l ∈ Et := by
      show δ l ∈ ψ.range
      rw [hl]
      exact ⟨q, rfl⟩
    refine ⟨⟨l, hlE⟩, ?_⟩
    have : g₁ ⟨l, hlE⟩ = eψ q := Subtype.ext (by
      show δ l = ψ q
      exact hl)
    show q8Frattini (eψ.symm (g₁ ⟨l, hlE⟩)) = v
    rw [this, MulEquiv.symm_apply_apply]
    exact hq
  have hβ₁cen : ∀ l : ↥Et, (∀ m ∈ L, m * ((l : ↥L) : H) = ((l : ↥L) : H) * m) → β₁ l = 1 := by
    intro l hl
    have hδmem : δ (l : ↥L) ∈ A' := hAD ▸ ⟨_, rfl⟩
    have hδl : δ (l : ↥L) = 1 := by
      apply hAcen _ hδmem
      intro w hw
      rw [← hAD] at hw
      obtain ⟨m, rfl⟩ := hw
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hl m m.2).symm
    have hg : g₁ l = 1 := Subtype.ext hδl
    show q8Frattini (eψ.symm (g₁ l)) = 1
    rw [hg, map_one, map_one]
  let f₁ : ↥Et →* H := L.subtype.comp Et.subtype
  let f₂ : ↥Et →* H := (MulAut.conj σ).toMonoidHom.comp f₁
  have hf₂ : ∀ b : ↥Et, f₂ b = σ * ((b : ↥L) : H) * σ⁻¹ := fun b => by
    simp [f₂, f₁, MulAut.conj_apply]
  have hσσ : ∀ z : H, σ * (σ * z * σ⁻¹) * σ⁻¹ = z := fun z => by
    calc σ * (σ * z * σ⁻¹) * σ⁻¹ = (σ * σ) * z * (σ⁻¹ * σ⁻¹) := by group
      _ = z := by rw [hσ, ← mul_inv_rev, hσ]; simp
  have hf₂mem : ∀ b : ↥Et, f₂ b ∈ L' := fun b => by
    rw [hmem', hf₂, hσσ]
    exact (b : ↥L).2
  have hc12 : ∀ (a b : ↥Et), Commute (f₁ a) (f₂ b) := fun a b =>
    hLL' _ (a : ↥L).2 _ (hf₂mem b)
  let α₁₂ : ↥Et × ↥Et →* H := f₁.noncommCoprod f₂ hc12
  have hc3 : ∀ (x : ↥Et × ↥Et) (q : Q8), Commute (α₁₂ x) (φ q) := by
    intro x q
    have h1 : Commute (f₁ x.1) (φ q) := (hφL q _ (x.1 : ↥L).2).symm
    have h2 : Commute (f₂ x.2) (φ q) := (hφL' q _ (hf₂mem x.2)).symm
    show Commute (f₁ x.1 * f₂ x.2) (φ q)
    exact h1.mul_left h2
  let α : (↥Et × ↥Et) × Q8 →* H := α₁₂.noncommCoprod φ hc3
  let β : (↥Et × ↥Et) × Q8 →* (V4 × V4) × V4 := (β₁.prodMap β₁).prodMap q8Frattini
  have hβsurj : Function.Surjective β := by
    rintro ⟨⟨v₁, v₂⟩, v₃⟩
    obtain ⟨a, ha⟩ := hβ₁surj v₁
    obtain ⟨b, hb⟩ := hβ₁surj v₂
    obtain ⟨c, hc⟩ := q8Frattini_surjective v₃
    exact ⟨((a, b), c), Prod.ext (Prod.ext ha hb) hc⟩
  have hAcomm : ∀ x y : (V4 × V4) × V4, x * y = y * x := fun x y =>
    Prod.ext (Prod.ext (mul_comm _ _) (mul_comm _ _)) (mul_comm _ _)
  have hAsq : ∀ x : (V4 × V4) × V4, x ^ 2 = 1 := by
    intro x
    have : ∀ v : V4, v ^ 2 = 1 := by decide
    exact Prod.ext (Prod.ext (this _) (this _)) (this _)
  have hcard : 2 ^ 4 < Nat.card ((V4 × V4) × V4) := by
    rw [Nat.card_prod, Nat.card_prod, card_V4]
    norm_num
  refine not_sectionalTwoRankLE_of_surjection 4 α β hβsurj hAcomm hAsq hcard ?_ hH
  intro k hk
  obtain ⟨⟨a, b⟩, c⟩ := k
  rw [MonoidHom.mem_ker] at hk ⊢
  have hk' : f₁ a * f₂ b * φ c = 1 := hk
  have hx1L : f₁ a ∈ L := (a : ↥L).2
  have hx2L' : f₂ b ∈ L' := hf₂mem b
  have hx12 : f₁ a * f₂ b = f₂ b * f₁ a := hLL' _ hx1L _ hx2L'
  have hx1cen : ∀ m ∈ L, m * f₁ a = f₁ a * m := by
    intro m hm
    have hx1 : f₁ a = (f₂ b * φ c)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hk')
    have hcm : Commute m (f₂ b * φ c) :=
      Commute.mul_right (hLL' m hm _ hx2L') (hφL c m hm).symm
    rw [hx1]
    exact hcm.inv_right.eq
  have hx2cen : ∀ z ∈ L', z * f₂ b = f₂ b * z := by
    intro z hz
    have hx2 : f₂ b = (f₁ a * φ c)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc f₂ b * (f₁ a * φ c) = (f₂ b * f₁ a) * φ c := by rw [mul_assoc]
        _ = (f₁ a * f₂ b) * φ c := by rw [hx12]
        _ = 1 := hk'
    have hcm : Commute z (f₁ a * φ c) :=
      Commute.mul_right (hLL' _ hx1L z hz).symm (hφL' c z hz).symm
    rw [hx2]
    exact hcm.inv_right.eq
  have hbcen : ∀ m ∈ L, m * ((b : ↥L) : H) = ((b : ↥L) : H) * m := by
    intro m hm
    have hz : σ * m * σ⁻¹ ∈ L' := by
      rw [hmem']
      rw [show σ * (σ * m * σ⁻¹) * σ⁻¹ = m from hσσ m]
      exact hm
    have h1 := hx2cen _ hz
    rw [hf₂] at h1
    have h2 : m * ((b : ↥L) : H) = ((b : ↥L) : H) * m := by
      calc m * ((b : ↥L) : H) = σ⁻¹ * (σ * m * σ⁻¹ * (σ * ((b : ↥L) : H) * σ⁻¹)) * σ := by group
        _ = σ⁻¹ * (σ * ((b : ↥L) : H) * σ⁻¹ * (σ * m * σ⁻¹)) * σ := by rw [h1]
        _ = ((b : ↥L) : H) * m := by group
    exact h2
  have hq : ∀ q' : Q8, c * q' = q' * c := by
    intro q'
    have hc : φ c = (f₁ a * f₂ b)⁻¹ := eq_inv_of_mul_eq_one_right hk'
    have hcm : Commute (φ q') (f₁ a * f₂ b) :=
      Commute.mul_right (hφL q' _ hx1L) (hφL' q' _ hx2L')
    have h1 : φ q' * φ c = φ c * φ q' := by
      rw [hc]
      exact hcm.inv_right.eq
    apply hφ
    rw [map_mul, map_mul]
    exact h1.symm
  have hfr : q8Frattini c = 1 := by
    rcases CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center c
      (fun x => hq x) with rfl | rfl
    · exact map_one _
    · decide
  exact Prod.ext (Prod.ext (hβ₁cen a hx1cen) (hβ₁cen b hbcen)) hfr


theorem q3_centralizes_of_perfect {H : Type} [Group H] {L : Subgroup H} (hL : ⁅L, L⁆ = L) (g : H)
    (hg : ∀ l ∈ L, ∃ z ∈ L, (∀ m ∈ L, m * z = z * m) ∧ g * l * g⁻¹ = l * z) :
    ∀ l ∈ L, g * l = l * g := by
  have hle : L ≤ centralizer ({g} : Set H) := by
    calc L = ⁅L, L⁆ := hL.symm
      _ ≤ centralizer ({g} : Set H) := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        obtain ⟨za, hza, hzac, hza'⟩ := hg a ha
        obtain ⟨zb, hzb, hzbc, hzb'⟩ := hg b hb
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hconj : g * ⁅a, b⁆ * g⁻¹ = ⁅a, b⁆ := by
          have h1 : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [h1, hza', hzb']
          exact commutatorElement_mul_mul_of_commute
            (hzac b hb).symm (hzac zb hzb).symm (hzbc a ha).symm
        calc ⁅a, b⁆ * g = g * ⁅a, b⁆ * g⁻¹ * g := by rw [hconj]
          _ = g * ⁅a, b⁆ := by group
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hl)).symm


theorem q3_conjSub_eq_self_iff {H : Type} [Group H] (g : H) (K : Subgroup H) :
    conjSub g K = K ↔ g ∈ normalizer (K : Set H) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hz : ∀ z, z ∈ K ↔ g⁻¹ * z * g ∈ K := fun z => by
      rw [← CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', h]
    have := hz (g * x * g⁻¹)
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    exact this.symm
  · intro h
    ext z
    rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff']
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (K : Set H)).inv_mem h)) z
    rw [inv_inv] at this
    exact this.symm

theorem q3_conjSub_conjSub {H : Type} [Group H] (g : H) (K : Subgroup H) :
    conjSub g (conjSub g K) = conjSub (g * g) K := by
  ext z
  rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', CFSG.GH74.GLS.TwoThin.mem_conjSub_iff',
    CFSG.GH74.GLS.TwoThin.mem_conjSub_iff']
  rw [show (g * g)⁻¹ * z * (g * g) = g⁻¹ * (g⁻¹ * z * g) * g by group]

theorem q3_conjSub_injective {H : Type} [Group H] (g : H) {K₁ K₂ : Subgroup H}
    (h : conjSub g K₁ = conjSub g K₂) : K₁ = K₂ := by
  ext z
  have h1 : z ∈ K₁ ↔ g * z * g⁻¹ ∈ conjSub g K₁ := by
    rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  have h2 : z ∈ K₂ ↔ g * z * g⁻¹ ∈ conjSub g K₂ := by
    rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', show g⁻¹ * (g * z * g⁻¹) * g = z by group]
  rw [h1, h2, h]

theorem q3_eq_pow_sq_of_odd {H : Type} [Group H] {g : H} (hg : Odd (orderOf g)) :
    ∃ k : ℕ, g = (g * g) ^ k := by
  obtain ⟨n, hn⟩ := hg
  refine ⟨n + 1, ?_⟩
  have h1 : g ^ (orderOf g) = 1 := pow_orderOf_eq_one g
  calc g = g ^ (orderOf g + 1) := by rw [pow_succ, h1, one_mul]
    _ = (g * g) ^ (n + 1) := by
      rw [← sq, ← pow_mul, hn]
      congr 1


theorem q3_false_of_diag {H : Type} [Group H] [Finite H] (hH : Gen4 H) {σ : H} (hσ : σ * σ = 1)
    {L : Subgroup H} (hL : IsComponent L) (hne : conjSub σ⁻¹ L ≠ L)
    (hAB : ⁅L, conjSub σ⁻¹ L⁆ = ⊥) {A' J' : Subgroup H}
    (hAd : A' ≤ (swapDiag hAB).range)
    (hperf : ∀ P : Subgroup H, P ≤ centralizer ({σ} : Set H) → ⁅P, P⁆ = P → P ≤ A')
    (hAcen : ∀ z ∈ A', (∀ w ∈ A', z * w = w * z) → z = 1)
    (hJodd : OddGenerated J') (hJA : ∀ a ∈ A', ∀ j ∈ J', a * j = j * a)
    (φ : Q8 →* H) (hφ : Function.Injective φ) (hφJ : ∀ g, φ g ∈ J')
    (ψ : Q8 →* H) (hψ : Function.Injective ψ) (hψA : ∀ g, ψ g ∈ A') : False := by
  classical
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ
  set L' := conjSub σ⁻¹ L with hL'
  set δ := swapDiag hAB with hδ
  have hmem' : ∀ x, x ∈ L' ↔ σ * x * σ⁻¹ ∈ L := fun x => by
    rw [hL', CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', inv_inv]
  have hσL : ∀ l ∈ L, σ⁻¹ * l * σ ∈ L' := fun l hl => conj_mem_conjSub hl
  have hLL' : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    commute_of_commutator_conj_eq_bot hAB ha hb
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hL'comp : IsComponent L' := isComponent_conjSub hL σ⁻¹
  have hδσ : ∀ l : ↥L, δ l * σ = σ * δ l := by
    intro l
    have hl' : σ⁻¹ * (l : H) * σ ∈ L' := hσL l l.2
    have hc : (l : H) * (σ⁻¹ * (l : H) * σ) = (σ⁻¹ * (l : H) * σ) * l := hLL' _ l.2 _ hl'
    rw [hσinv] at hc
    show (l : H) * (σ⁻¹ * l * σ) * σ = σ * ((l : H) * (σ⁻¹ * l * σ))
    rw [hσinv]
    calc (l : H) * (σ * l * σ) * σ = l * σ * l * (σ * σ) := by group
      _ = l * σ * l := by rw [hσ, mul_one]
      _ = (σ * σ) * l * σ * l := by rw [hσ, one_mul]
      _ = σ * ((σ * l * σ) * l) := by group
      _ = σ * (l * (σ * l * σ)) := by rw [hc]
  have hDle : δ.range ≤ centralizer ({σ} : Set H) := by
    rintro _ ⟨l, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hδσ l)
  have hDperf : ⁅δ.range, δ.range⁆ = δ.range := by
    have := hL.1.1
    exact Subgroup.isPerfect_iff.1 (Group.IsPerfect.range δ)
  have hAD : δ.range = A' := le_antisymm (hperf _ hDle hDperf) hAd
  have hδmem : ∀ l : ↥L, δ l ∈ A' := fun l => hAD ▸ ⟨l, rfl⟩
  have hC : ∃ a ∈ A', ∃ m ∈ L, a * m ≠ m * a := by
    by_contra hnot
    push Not at hnot
    refine quasisimple_not_commutative hL.1 (fun l m => ?_)
    have hl' : σ⁻¹ * (l : H) * σ ∈ L' := hσL l l.2
    have h1 := hnot (δ l) (hδmem l) m m.2
    have h2 : (m : H) * (σ⁻¹ * (l : H) * σ) = (σ⁻¹ * (l : H) * σ) * m := hLL' _ m.2 _ hl'
    apply Subtype.ext
    apply mul_right_cancel (b := σ⁻¹ * (l : H) * σ)
    calc (l : H) * m * (σ⁻¹ * (l : H) * σ) = l * (m * (σ⁻¹ * l * σ)) := by group
      _ = l * ((σ⁻¹ * l * σ) * m) := by rw [h2]
      _ = (l * (σ⁻¹ * l * σ)) * m := by group
      _ = m * (l * (σ⁻¹ * l * σ)) := h1
      _ = m * l * (σ⁻¹ * l * σ) := by group
  have hC' : ∃ a ∈ A', ∃ m ∈ L', a * m ≠ m * a := by
    by_contra hnot
    push Not at hnot
    refine quasisimple_not_commutative hL'comp.1 (fun x y => ?_)
    have hxL : σ * (x : H) * σ⁻¹ ∈ L := (hmem' x).1 x.2
    have hδx : δ ⟨σ * (x : H) * σ⁻¹, hxL⟩ = σ * (x : H) * σ⁻¹ * x := by
      show σ * (x : H) * σ⁻¹ * (σ⁻¹ * (σ * (x : H) * σ⁻¹) * σ) = _
      group
    have h1 := hnot (δ ⟨σ * (x : H) * σ⁻¹, hxL⟩) (hδmem _) y y.2
    rw [hδx] at h1
    have h2 : σ * (x : H) * σ⁻¹ * (y : H) = (y : H) * (σ * (x : H) * σ⁻¹) := hLL' _ hxL _ y.2
    apply Subtype.ext
    apply mul_left_cancel (a := σ * (x : H) * σ⁻¹)
    calc σ * (x : H) * σ⁻¹ * ((x : H) * y) = (σ * x * σ⁻¹ * x) * y := by group
      _ = y * (σ * x * σ⁻¹ * x) := h1
      _ = (y * (σ * x * σ⁻¹)) * x := by group
      _ = (σ * x * σ⁻¹ * y) * x := by rw [h2]
      _ = σ * (x : H) * σ⁻¹ * (y * x) := by group
  have hperm : ∀ K : Subgroup H, IsComponent K → (∃ a ∈ A', ∃ m ∈ K, a * m ≠ m * a) →
      ∀ g : H, (∀ a ∈ A', a * g = g * a) → conjSub g K = L ∨ conjSub g K = L' := by
    intro K hK hNC g hg
    by_contra hnot
    push Not at hnot
    obtain ⟨hn1, hn2⟩ := hnot
    have hK₁ : IsComponent (conjSub g K) := isComponent_conjSub hK g
    have hc1 : ⁅conjSub g K, L⁆ = ⊥ := by
      rcases distinct_components_commute hK₁ hL with h | h
      · exact absurd h hn1
      · exact h
    have hc2 : ⁅conjSub g K, L'⁆ = ⊥ := by
      rcases distinct_components_commute hK₁ hL'comp with h | h
      · exact absurd h hn2
      · exact h
    obtain ⟨a, ha, m, hm, hne'⟩ := hNC
    rw [← hAD] at ha
    obtain ⟨l, rfl⟩ := ha
    have hgm : g * m * g⁻¹ ∈ conjSub g K := by
      rw [CFSG.GH74.GLS.TwoThin.mem_conjSub_iff', show g⁻¹ * (g * m * g⁻¹) * g = m by group]
      exact hm
    have hcl : (g * m * g⁻¹) * (l : H) = (l : H) * (g * m * g⁻¹) := by
      have := Subgroup.commutator_mem_commutator hgm l.2
      rw [hc1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcl' : (g * m * g⁻¹) * (σ⁻¹ * (l : H) * σ) = (σ⁻¹ * (l : H) * σ) * (g * m * g⁻¹) := by
      have := Subgroup.commutator_mem_commutator hgm (hσL l l.2)
      rw [hc2, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
    have hcδ : (g * m * g⁻¹) * δ l = δ l * (g * m * g⁻¹) := by
      show (g * m * g⁻¹) * ((l : H) * (σ⁻¹ * (l : H) * σ)) =
        ((l : H) * (σ⁻¹ * (l : H) * σ)) * (g * m * g⁻¹)
      calc (g * m * g⁻¹) * ((l : H) * (σ⁻¹ * (l : H) * σ))
          = ((g * m * g⁻¹) * l) * (σ⁻¹ * l * σ) := by group
        _ = (l * (g * m * g⁻¹)) * (σ⁻¹ * l * σ) := by rw [hcl]
        _ = l * ((g * m * g⁻¹) * (σ⁻¹ * l * σ)) := by group
        _ = l * ((σ⁻¹ * l * σ) * (g * m * g⁻¹)) := by rw [hcl']
        _ = ((l : H) * (σ⁻¹ * (l : H) * σ)) * (g * m * g⁻¹) := by group
    have hga : δ l * g = g * δ l := hg _ (hδmem l)
    have hconj : g⁻¹ * δ l * g = δ l := by
      calc g⁻¹ * δ l * g = g⁻¹ * (g * δ l) := by rw [← hga]; group
        _ = δ l := by group
    apply hne'
    have key : m * δ l = δ l * m := by
      calc m * δ l = g⁻¹ * ((g * m * g⁻¹) * δ l) * g := by
            calc m * δ l = m * (g⁻¹ * δ l * g) := by rw [hconj]
              _ = g⁻¹ * ((g * m * g⁻¹) * δ l) * g := by group
        _ = g⁻¹ * (δ l * (g * m * g⁻¹)) * g := by rw [hcδ]
        _ = (g⁻¹ * δ l * g) * m := by group
        _ = δ l * m := by rw [hconj]
    exact key.symm
  have hnorm : ∀ g ∈ J', Odd (orderOf g) → conjSub g L = L ∧ conjSub g L' = L' := by
    intro g hg hgo
    have hgA : ∀ a ∈ A', a * g = g * a := fun a ha => hJA a ha g hg
    have h1 := hperm L hL hC g hgA
    have h2 := hperm L' hL'comp hC' g hgA
    have hgL1 : conjSub g L = L := by
      by_contra hne1
      have hgL : conjSub g L = L' := h1.resolve_left hne1
      have hgL' : conjSub g L' = L := by
        rcases h2 with h | h
        · exact h
        · exfalso
          exact hne (q3_conjSub_injective g (by rw [hgL, h])).symm
      have hgg : conjSub (g * g) L = L := by
        rw [← q3_conjSub_conjSub, hgL, hgL']
      have hggN : g * g ∈ normalizer (L : Set H) := (q3_conjSub_eq_self_iff _ _).1 hgg
      obtain ⟨k, hk⟩ := q3_eq_pow_sq_of_odd hgo
      have hgN : g ∈ normalizer (L : Set H) := by
        rw [hk]
        exact (normalizer (L : Set H)).pow_mem hggN k
      exact hne1 ((q3_conjSub_eq_self_iff _ _).2 hgN)
    refine ⟨hgL1, ?_⟩
    rcases h2 with h | h
    · exfalso
      exact hne (q3_conjSub_injective g (by rw [h, hgL1])).symm
    · exact h
  have hcentL : ∀ g ∈ J', Odd (orderOf g) → ∀ l ∈ L, g * l = l * g := by
    intro g hg hgo
    obtain ⟨hgL, hgL'⟩ := hnorm g hg hgo
    have hgNL : g ∈ normalizer (L : Set H) := (q3_conjSub_eq_self_iff _ _).1 hgL
    have hgNL' : g ∈ normalizer (L' : Set H) := (q3_conjSub_eq_self_iff _ _).1 hgL'
    have hgA : ∀ a ∈ A', a * g = g * a := fun a ha => hJA a ha g hg
    apply q3_centralizes_of_perfect hLperf g
    intro l hl
    have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgNL l).1 hl
    have hl' : σ⁻¹ * l * σ ∈ L' := hσL l hl
    have hgl' : g * (σ⁻¹ * l * σ) * g⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.1 hgNL' _).1 hl'
    have hga := hgA (δ ⟨l, hl⟩) (hδmem ⟨l, hl⟩)
    have hconj : g * ((l : H) * (σ⁻¹ * l * σ)) * g⁻¹ = (l : H) * (σ⁻¹ * l * σ) := by
      have : δ ⟨l, hl⟩ = (l : H) * (σ⁻¹ * l * σ) := rfl
      rw [← this]
      calc g * δ ⟨l, hl⟩ * g⁻¹ = (δ ⟨l, hl⟩ * g) * g⁻¹ := by rw [hga]
        _ = δ ⟨l, hl⟩ := by group
    refine ⟨l⁻¹ * (g * l * g⁻¹), ?_, ?_, ?_⟩
    · exact L.mul_mem (L.inv_mem hl) hgl
    · intro m hm
      have hz : l⁻¹ * (g * l * g⁻¹) = (σ⁻¹ * l * σ) * (g * (σ⁻¹ * l * σ) * g⁻¹)⁻¹ := by
        have h3 : g * l * g⁻¹ * (g * (σ⁻¹ * l * σ) * g⁻¹) = l * (σ⁻¹ * l * σ) := by
          rw [← hconj]
          group
        calc l⁻¹ * (g * l * g⁻¹)
            = l⁻¹ * (g * l * g⁻¹ * (g * (σ⁻¹ * l * σ) * g⁻¹)) * (g * (σ⁻¹ * l * σ) * g⁻¹)⁻¹ := by
              group
          _ = l⁻¹ * (l * (σ⁻¹ * l * σ)) * (g * (σ⁻¹ * l * σ) * g⁻¹)⁻¹ := by rw [h3]
          _ = (σ⁻¹ * l * σ) * (g * (σ⁻¹ * l * σ) * g⁻¹)⁻¹ := by group
      have hzL' : l⁻¹ * (g * l * g⁻¹) ∈ L' := by
        rw [hz]
        exact L'.mul_mem hl' (L'.inv_mem hgl')
      exact hLL' m hm _ hzL'
    · group
  have hcentL' : ∀ g ∈ J', Odd (orderOf g) → ∀ l' ∈ L', g * l' = l' * g := by
    intro g hg hgo l' hl'
    have hgA : ∀ a ∈ A', a * g = g * a := fun a ha => hJA a ha g hg
    have hxL : σ * l' * σ⁻¹ ∈ L := (hmem' l').1 hl'
    have hL1 := hcentL g hg hgo _ hxL
    have hδl : δ ⟨σ * l' * σ⁻¹, hxL⟩ = σ * l' * σ⁻¹ * l' := by
      show σ * l' * σ⁻¹ * (σ⁻¹ * (σ * l' * σ⁻¹) * σ) = _
      group
    have hga := hgA _ (hδmem ⟨σ * l' * σ⁻¹, hxL⟩)
    rw [hδl] at hga
    have : (σ * l' * σ⁻¹) * (l' * g) = (σ * l' * σ⁻¹) * (g * l') := by
      calc (σ * l' * σ⁻¹) * (l' * g) = (σ * l' * σ⁻¹ * l') * g := by group
        _ = g * (σ * l' * σ⁻¹ * l') := hga
        _ = (g * (σ * l' * σ⁻¹)) * l' := by group
        _ = ((σ * l' * σ⁻¹) * g) * l' := by rw [hL1]
        _ = (σ * l' * σ⁻¹) * (g * l') := by group
    exact (mul_left_cancel this).symm
  have hJL : J' ≤ centralizer (L : Set H) := by
    rw [← hJodd]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    exact (hcentL g hg.1 hg.2 m hm).symm
  have hJL' : J' ≤ centralizer (L' : Set H) := by
    rw [← hJodd]
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    exact (hcentL' g hg.1 hg.2 m hm).symm
  exact q3_false_of_two_factor hH hσ hAB hAD hAcen φ hφ
    (fun g m hm => (Subgroup.mem_centralizer_iff.1 (hJL (hφJ g)) m hm).symm)
    (fun g m hm => (Subgroup.mem_centralizer_iff.1 (hJL' (hφJ g)) m hm).symm) ψ hψ hψA

end CFSG.GH74.Generic.S1