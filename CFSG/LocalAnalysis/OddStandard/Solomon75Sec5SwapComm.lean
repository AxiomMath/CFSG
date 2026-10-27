module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentA

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Quasisimple

variable {Q : Type*} [Group Q] [Finite Q]

theorem normal_pgroup_le_center_of_quasisimple (hq : IsQuasisimple Q) {R : Subgroup Q}
    [R.Normal] (hR : IsPGroup 2 ↥R) : R ≤ center Q := by
  classical
  have hs : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  set φ : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hRn : (R.map φ).Normal := Subgroup.Normal.map ‹R.Normal› φ hφs
  rcases hs.eq_bot_or_eq_top_of_normal (R.map φ) with h | h
  · intro x hx
    have : φ x ∈ R.map φ := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · exfalso
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    have h1 : Nat.card ↥(R.map φ) ∣ Nat.card R := Subgroup.card_map_dvd R φ
    rw [h, Subgroup.card_top, hk] at h1
    have hpt : IsPGroup 2 (Q ⧸ center Q) := IsPGroup.of_card_dvd_pow h1
    have hnil : Group.IsNilpotent (Q ⧸ center Q) := hpt.isNilpotent
    have hsolv : Group.IsSolvable (Q ⧸ center Q) := by
      have := hnil
      infer_instance
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv a b)

theorem normal_odd_eq_bot_of_quasisimple (hq : IsQuasisimple Q) (hZ : IsPGroup 2 ↥(center Q))
    {M : Subgroup Q} [M.Normal] (hM : Odd (Nat.card M)) : M = ⊥ := by
  classical
  have hs : IsSimpleGroup (Q ⧸ center Q) := hq.2.1
  set φ : Q →* Q ⧸ center Q := QuotientGroup.mk' (center Q) with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective _
  have hMn : (M.map φ).Normal := Subgroup.Normal.map ‹M.Normal› φ hφs
  rcases hs.eq_bot_or_eq_top_of_normal (M.map φ) with h | h
  · have hle : M ≤ center Q := by
      intro x hx
      have : φ x ∈ M.map φ := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff x).1 this
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    have h1 : Nat.card M ∣ Nat.card (center Q) := Subgroup.card_dvd_of_le hle
    rw [hk] at h1
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · exact h0
      · exfalso
        rw [hi] at hM
        exact (Nat.not_even_iff_odd.2 hM) (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)
    rw [this, pow_zero] at hi
    exact Subgroup.eq_bot_of_card_eq M hi
  · exfalso
    have hodd : Odd (Nat.card (Q ⧸ center Q)) := by
      have h1 : Nat.card ↥(M.map φ) ∣ Nat.card M := Subgroup.card_map_dvd M φ
      rw [h, Subgroup.card_top] at h1
      exact Odd.of_dvd_nat hM h1
    have hsolv : Group.IsSolvable (Q ⧸ center Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hq.2.2
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv a b)

end Quasisimple

section CIC

variable {X : Type} {Q : Type*} [Group X] [Group Q]

theorem commutator_image_normal_two {Λ OO W₂ : Subgroup X} {w : X} (ψ : ↥Λ →* Q)
    (hψ : Function.Surjective ψ) (hwΛ : ∀ x ∈ Λ, w * x * w⁻¹ ∈ Λ)
    (hOO : Odd (Nat.card OO)) (hΛOO : Λ ≤ normalizer (OO : Set X)) (hW₂ : IsPGroup 2 ↥W₂)
    (hW₂OO : W₂ ≤ normalizer (OO : Set X))
    (hQ : ∀ M : Subgroup Q, M.Normal → Odd (Nat.card M) → M = ⊥)
    (hV : ∀ x ∈ Λ, ⁅x, w⁆ ∈ OO ⊔ W₂) :
    ∃ R : Subgroup Q, R.Normal ∧ IsPGroup 2 ↥R ∧
      ∀ (x : ↥Λ) (hx : ⁅(x : X), w⁆ ∈ Λ), ψ ⟨⁅(x : X), w⁆, hx⟩ ∈ R := by
  classical
  have hmem : ∀ x : ↥Λ, ⁅(x : X), w⁆ ∈ Λ := by
    intro x
    have e : ⁅(x : X), w⁆ = x * (w * (x : X)⁻¹ * w⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Λ.mul_mem x.2 (hwΛ _ (Λ.inv_mem x.2))
  let f : ↥Λ → ↥Λ := fun x => ⟨⁅(x : X), w⁆, hmem x⟩
  let T : Subgroup ↥Λ := Subgroup.closure (Set.range f)
  have hfmul : ∀ e x : ↥Λ, e * f x * e⁻¹ = f (e * x) * (f e)⁻¹ := by
    intro e x
    apply Subtype.ext
    simp only [f, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hTn : T.Normal := by
    refine ⟨fun t ht e => ?_⟩
    induction ht using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨x, rfl⟩ := hg
      rw [hfmul]
      exact T.mul_mem (Subgroup.subset_closure ⟨_, rfl⟩)
        (T.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩))
    | one => simp
    | mul a b _ _ ha hb =>
      have : e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) := by group
      rw [this]; exact T.mul_mem ha hb
    | inv a _ ha =>
      have : e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ := by group
      rw [this]; exact T.inv_mem ha
  have hTbar : (T.map ψ).Normal := Subgroup.Normal.map hTn ψ hψ
  let V : Subgroup X := OO ⊔ W₂
  have hTV : ∀ t ∈ T, ((t : ↥Λ) : X) ∈ V := by
    intro t ht
    have : T ≤ V.comap Λ.subtype := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, rfl⟩
      exact hV x x.2
    exact this ht
  let O' : Subgroup ↥Λ := OO.comap Λ.subtype
  have hO'n : O'.Normal := ⟨fun o ho e => by
    show ((e * o * e⁻¹ : ↥Λ) : X) ∈ OO
    have := (Subgroup.mem_normalizer_iff.1 (hΛOO e.2) (o : X)).1 ho
    simpa using this⟩
  let R0 : Subgroup ↥Λ := T ⊓ O'
  have hRn : R0.Normal := inferInstance
  have hRbar : (R0.map ψ).Normal := Subgroup.Normal.map hRn ψ hψ
  have hRodd : Odd (Nat.card (R0.map ψ)) := by
    refine Odd.of_dvd_nat hOO ((Subgroup.card_map_dvd R0 ψ).trans ?_)
    let g : R0 →* ↥OO := ⟨⟨fun r => ⟨((r : ↥Λ) : X), r.2.2⟩, rfl⟩, fun a b => rfl⟩
    have hg : Function.Injective g := fun a b h => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : ↥OO => (w : X)) h
    exact Subgroup.card_dvd_of_injective g hg
  have hRbot : R0.map ψ = ⊥ := hQ _ hRbar hRodd
  have hTp : IsPGroup 2 ↥(T.map ψ) := by
    intro g
    obtain ⟨_, ⟨t, ht, rfl⟩⟩ := g
    obtain ⟨k, hk⟩ := exists_pow_two_mem_of_mem_sup hW₂OO hW₂ (hTV t ht)
    refine ⟨k, ?_⟩
    have htk : t ^ (2 ^ k) ∈ R0 := ⟨T.pow_mem ht _, hk⟩
    have : ψ (t ^ (2 ^ k)) ∈ R0.map ψ := ⟨_, htk, rfl⟩
    rw [hRbot, Subgroup.mem_bot] at this
    apply Subtype.ext
    simpa [map_pow] using this
  exact ⟨T.map ψ, hTbar, hTp, fun x hx => ⟨f x, Subgroup.subset_closure ⟨x, rfl⟩, rfl⟩⟩

end CIC

end CFSG.OddStandard.Solomon75
