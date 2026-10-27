module

public import CFSG.HardMathSupport.Curtis.Proving.ToralExponentP
public import CFSG.HardMathSupport.Curtis.Proving.ToralQuotient

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open Function

variable {Y : Type*} [Group Y]

theorem bijective_of_iterate_eq_id {α : Type*} (f : α → α) {N : ℕ} (hN : 0 < N)
    (h : f^[N] = id) : Function.Bijective f := by
  refine Function.bijective_iff_has_inverse.mpr ⟨f^[N - 1], fun x => ?_, fun x => ?_⟩
  · have h2 : f^[N - 1 + 1] x = x := by
      rw [Nat.sub_add_cancel hN]
      exact congrFun h x
    rwa [Function.iterate_succ_apply] at h2
  · have h1 : f^[N - 1 + 1] x = x := by
      rw [Nat.sub_add_cancel hN]
      exact congrFun h x
    rwa [Function.iterate_succ_apply'] at h1

def conjSub (T : Subgroup Y) {c : Y} (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T) : T →* T where
  toFun t := ⟨c * t * c⁻¹, hcT t t.2⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    simp [mul_assoc]

theorem conjSub_comap_le {T X : Subgroup Y} {c : Y} (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) :
    X.subgroupOf T ≤ (X.subgroupOf T).comap (conjSub T hcT) := by
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact hcX (x : Y) (Subgroup.mem_subgroupOf.mp hx)

noncomputable def conjQuot (T X : Subgroup Y) [(X.subgroupOf T).Normal] {c : Y}
    (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T) (hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X) :
    (T ⧸ X.subgroupOf T) →* (T ⧸ X.subgroupOf T) :=
  QuotientGroup.map (X.subgroupOf T) (X.subgroupOf T) (conjSub T hcT)
    (conjSub_comap_le hcT hcX)

theorem conjQuot_iterate (T X : Subgroup Y) [(X.subgroupOf T).Normal] {c : Y}
    (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T) (hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (n : ℕ) (t : Y) (ht : t ∈ T) :
    ∃ s : T, (s : Y) = c ^ n * t * (c ^ n)⁻¹ ∧
      (⇑(conjQuot T X hcT hcX))^[n] (QuotientGroup.mk ⟨t, ht⟩) = QuotientGroup.mk s := by
  induction n with
  | zero =>
    refine ⟨⟨t, ht⟩, ?_, ?_⟩
    · simp
    · simp
  | succ n ih =>
    obtain ⟨s, hs, hmk⟩ := ih
    refine ⟨⟨c * s * c⁻¹, hcT s s.2⟩, ?_, ?_⟩
    · show c * (s : Y) * c⁻¹ = c ^ (n + 1) * t * (c ^ (n + 1))⁻¹
      rw [hs, pow_succ']
      group
    · rw [Function.iterate_succ_apply', hmk, conjQuot, QuotientGroup.map_mk]
      rfl

abbrev addCommGroupOfComm {Q : Type*} [Group Q] (hc : ∀ x y : Q, x * y = y * x) :
    AddCommGroup (Additive Q) :=
  { (inferInstance : AddGroup (Additive Q)) with
    add_comm := fun a b => congrArg Additive.ofMul (hc (Additive.toMul a) (Additive.toMul b)) }

theorem premise_of_nontrivial_action {p r : ℕ} [hp : Fact p.Prime] [hr : Fact r.Prime]
    (hdvd : r ∣ p ^ 2 + 1) (hndvd : ¬ r ∣ p ^ 2 - 1)
    {T X : Subgroup Y} {c : Y} (hXT : X ≤ T)
    (hcomm : ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ X) (hpow : ∀ a ∈ T, a ^ p ∈ X)
    (hidx : X.relIndex T = p ^ 4)
    (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T) (hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X)
    (hcr : ∃ k : ℕ, c ^ (r ^ k) = 1)
    (hnt : ∃ t ∈ T, c * t * c⁻¹ * t⁻¹ ∉ X) :
    ∀ V : Subgroup Y, X ≤ V → V ≤ T → (∀ s ∈ T, ∀ v ∈ V, s * v * s⁻¹ ∈ V) →
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T := by
  intro V hXV hVT _ hVc
  have hnorm : (X.subgroupOf T).Normal := subgroupOf_normal_of_comm hcomm
  obtain ⟨k, hck⟩ := hcr
  let φ0 : (T ⧸ X.subgroupOf T) →* (T ⧸ X.subgroupOf T) := conjQuot T X hcT hcX
  let φA : Additive (T ⧸ X.subgroupOf T) →+ Additive (T ⧸ X.subgroupOf T) :=
    MonoidHom.toAdditive φ0
  have hiter : ∀ (n : ℕ) (a : Additive (T ⧸ X.subgroupOf T)),
      (⇑φA)^[n] a = Additive.ofMul ((⇑φ0)^[n] (Additive.toMul a)) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have hQid : ∀ q : T ⧸ X.subgroupOf T, (⇑φ0)^[r ^ k] q = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨s, hs, hmk⟩ := conjQuot_iterate T X hcT hcX (r ^ k) (a : Y) a.2
      have hsa : s = a := by
        apply Subtype.ext
        rw [hs, hck]
        simp
      rw [hsa] at hmk
      exact hmk
  have hk : (⇑φA)^[r ^ k] = id := by
    funext a
    rw [hiter, hQid]
    rfl
  have hbij : Function.Bijective (⇑φA) :=
    bijective_of_iterate_eq_id _ (pow_pos hr.out.pos k) hk
  let φ : Additive (T ⧸ X.subgroupOf T) ≃+ Additive (T ⧸ X.subgroupOf T) :=
    AddEquiv.ofBijective φA hbij
  have hφ : ∀ a, φ a = φA a := fun a => rfl
  have hne : ∃ a : Additive (T ⧸ X.subgroupOf T), φ a ≠ a := by
    obtain ⟨t, ht, hnot⟩ := hnt
    refine ⟨Additive.ofMul (QuotientGroup.mk (⟨t, ht⟩ : T)), ?_⟩
    intro heq
    have h2 : φ0 (QuotientGroup.mk (⟨t, ht⟩ : T)) = QuotientGroup.mk (⟨t, ht⟩ : T) :=
      Additive.ofMul.injective heq
    have hmk : φ0 (QuotientGroup.mk (⟨t, ht⟩ : T)) =
        (QuotientGroup.mk ⟨c * t * c⁻¹, hcT t ht⟩ : T ⧸ X.subgroupOf T) := rfl
    rw [hmk] at h2
    have hy := QuotientGroup.eq.mp h2
    rw [Subgroup.mem_subgroupOf] at hy
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hy
    have hy' : t⁻¹ * (c * t * c⁻¹) ∈ X := by
      have h := X.inv_mem hy
      rwa [show ((c * t * c⁻¹)⁻¹ * t)⁻¹ = t⁻¹ * (c * t * c⁻¹) by group] at h
    have hc := hcomm t ht (t⁻¹ * (c * t * c⁻¹)) (hXT hy')
    apply hnot
    have e : c * t * c⁻¹ * t⁻¹ = (t * (t⁻¹ * (c * t * c⁻¹)) * t⁻¹ * (t⁻¹ * (c * t * c⁻¹))⁻¹) *
        (t⁻¹ * (c * t * c⁻¹)) := by group
    rw [e]
    exact X.mul_mem hc hy'
  have hexp : ∀ a : Additive (T ⧸ X.subgroupOf T), p • a = 0 := by
    intro a
    exact congrArg Additive.ofMul (quotient_pow_eq_one hpow (Additive.toMul a))
  have hcard : Nat.card (Additive (T ⧸ X.subgroupOf T)) = p ^ 4 :=
    (Nat.card_congr (Additive.ofMul.symm : Additive (T ⧸ X.subgroupOf T) ≃ (T ⧸ X.subgroupOf T))).trans
      ((card_quotient_eq_relIndex T X).trans hidx)
  let W : Subgroup (T ⧸ X.subgroupOf T) := (V.subgroupOf T).map (QuotientGroup.mk' (X.subgroupOf T))
  let B : AddSubgroup (Additive (T ⧸ X.subgroupOf T)) := W.toAddSubgroup
  have hBmem : ∀ g : Additive (T ⧸ X.subgroupOf T), g ∈ B ↔ Additive.toMul g ∈ W := fun g =>
    Additive.mem_toAddSubgroup W g
  have hB : ∀ b ∈ B, φ b ∈ B := by
    intro b hb
    rw [hBmem] at hb ⊢
    obtain ⟨v, hv, hvb⟩ := Subgroup.mem_map.mp hb
    have hvV : (v : Y) ∈ V := Subgroup.mem_subgroupOf.mp hv
    refine Subgroup.mem_map.mpr ⟨⟨c * (v : Y) * c⁻¹, hcT v v.2⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hVc v hvV)
    · show QuotientGroup.mk' (X.subgroupOf T) ⟨c * (v : Y) * c⁻¹, hcT v v.2⟩ = φ0 (Additive.toMul b)
      rw [← hvb]
      rfl
  have hBcases := @addSubgroup_invariant_bot_or_top p r hp hr hdvd hndvd
    (Additive (T ⧸ X.subgroupOf T))
    (addCommGroupOfComm (fun x y => quotient_mul_comm hcomm x y))
    hexp hcard φ k hk hne B hB
  rcases hBcases with hBbot | hBtop
  · left
    apply le_antisymm _ hXV
    intro v hv
    have hvT : v ∈ T := hVT hv
    have hmem : Additive.ofMul (QuotientGroup.mk (⟨v, hvT⟩ : T) : T ⧸ X.subgroupOf T) ∈ B := by
      rw [hBmem]
      exact Subgroup.mem_map.mpr ⟨⟨v, hvT⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    rw [hBbot, AddSubgroup.mem_bot] at hmem
    have h1 : (QuotientGroup.mk (⟨v, hvT⟩ : T) : T ⧸ X.subgroupOf T) = 1 :=
      Additive.ofMul.injective hmem
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · right
    apply le_antisymm hVT
    intro t ht
    have hmem : Additive.ofMul (QuotientGroup.mk (⟨t, ht⟩ : T) : T ⧸ X.subgroupOf T) ∈ B := by
      rw [hBtop]
      exact AddSubgroup.mem_top _
    rw [hBmem] at hmem
    obtain ⟨v, hv, hvt⟩ := Subgroup.mem_map.mp hmem
    have h1 : (QuotientGroup.mk v : T ⧸ X.subgroupOf T) = QuotientGroup.mk (⟨t, ht⟩ : T) := hvt
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have e : t = (v : Y) * ((v : Y)⁻¹ * t) := by group
    rw [e]
    exact V.mul_mem (Subgroup.mem_subgroupOf.mp hv) (hXV h2)

end CFSG.HardMathSupport.Curtis.Proving

end
