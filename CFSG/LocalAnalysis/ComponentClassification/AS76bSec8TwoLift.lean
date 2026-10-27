module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExceptionalLift

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ComponentClassification.RankTwoSporadic

section TwoLift

variable {G : Type*} [Group G] {M : Type*} [Group M] {C : Subgroup M} {A : Subgroup G}

@[expose] def twoLift (ψ : normalizer (A : Set G) →* MulAut ↥C) (U : Subgroup M) :
    Subgroup G :=
  closure {a | ∃ ha : a ∈ A, a ^ 2 = 1 ∧
    ∃ y : ↥C, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y ∧ (y : M) ∈ U}

variable {ψ : normalizer (A : Set G) →* MulAut ↥C} {U : Subgroup M}

theorem twoLift_le : twoLift ψ U ≤ A :=
  (closure_le A).2 fun _ ⟨ha, _⟩ => ha

theorem mem_twoLift_of {a : G} (ha : a ∈ A) (h2 : a ^ 2 = 1) {y : ↥C}
    (hy : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y) (hyU : (y : M) ∈ U) : a ∈ twoLift ψ U :=
  subset_closure ⟨ha, h2, y, hy, hyU⟩

theorem twoLift_mono {U U' : Subgroup M} (h : U ≤ U') : twoLift ψ U ≤ twoLift ψ U' :=
  closure_mono fun _ ⟨ha, h2, y, hy, hyU⟩ => ⟨ha, h2, y, hy, h hyU⟩

omit [Group M] in
theorem commute_of_sq_eq_one (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (hc : a * b * a⁻¹ * b⁻¹ ∈ centralizer (A : Set G)) : a * b = b * a := by
  have hcA : a * b * a⁻¹ * b⁻¹ ∈ A := mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb2])
  have hac : a * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * a := mem_centralizer_iff.1 hc a ha
  have hinv : (a * b * a⁻¹ * b⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    have h1 : a * (a * b * a⁻¹ * b⁻¹) * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by
      rw [hai, hbi]
      calc a * (a * b * a * b) * a = (a * a) * (b * a * b * a) := by group
        _ = b * a * b * a := by rw [← sq, ha2, one_mul]
        _ = (a * b * a * b)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hai, hbi]
          simp only [mul_assoc]
    rw [← h1, hac, mul_inv_cancel_right]
  have hsq : (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [← hinv]
    exact mul_inv_cancel _
  have h1 := RankTwoL3Even.eq_one_of_odd_of_pow_two
    (RankTwoL3Even.odd_orderOf_of_mem hZ (mem_inf.2 ⟨hcA, hc⟩)) (k := 1)
    (by rw [pow_one]; exact hsq)
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem psi_conj_eq_conj' {n b : G}
    (hn : n ∈ normalizer (A : Set G)) (hb : b ∈ A) {x : ↥C}
    (hbx : ψ ⟨b, le_normalizer hb⟩ = MulAut.conj x) (hnb : n * b * n⁻¹ ∈ A) :
    ψ ⟨n * b * n⁻¹, le_normalizer hnb⟩ = MulAut.conj (ψ ⟨n, hn⟩ x) := by
  have e : (⟨n * b * n⁻¹, le_normalizer hnb⟩ : normalizer (A : Set G)) =
      ⟨n, hn⟩ * ⟨b, le_normalizer hb⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hbx, RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv]

variable (hψ : IsActionHom A (MulAut.conj : ↥C →* MulAut ↥C).range ψ)
  (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
  (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hU2 : ∀ u ∈ U, u ^ 2 = 1)
include hψ hZ hUc

theorem mem_twoLift {a : G} :
    a ∈ twoLift ψ U ↔ ∃ ha : a ∈ A, a ^ 2 = 1 ∧
      ∃ y : ↥C, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y ∧ (y : M) ∈ U := by
  refine ⟨fun h => ?_, fun ⟨ha, h2, y, hy, hyU⟩ => mem_twoLift_of ha h2 hy hyU⟩
  induction h using closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨one_mem A, one_pow 2, 1, by rw [map_one]; exact map_one _, one_mem U⟩
  | mul x y _ _ hx hy =>
    obtain ⟨hxA, hx2, u, hu, huU⟩ := hx
    obtain ⟨hyA, hy2, v, hv, hvU⟩ := hy
    have huv : u * v = v * u := Subtype.ext (hUc _ huU _ hvU)
    have hxyN : x * y * x⁻¹ * y⁻¹ ∈ normalizer (A : Set G) :=
      le_normalizer (mul_mem (mul_mem (mul_mem hxA hyA) (inv_mem hxA)) (inv_mem hyA))
    have hcomm : x * y = y * x := by
      refine commute_of_sq_eq_one hZ hxA hyA hx2 hy2 ((hψ.eq_one_iff ⟨_, hxyN⟩).1 ?_)
      have e : (⟨x * y * x⁻¹ * y⁻¹, hxyN⟩ : normalizer (A : Set G)) =
          ⟨x, le_normalizer hxA⟩ * ⟨y, le_normalizer hyA⟩ * ⟨x, le_normalizer hxA⟩⁻¹ *
            ⟨y, le_normalizer hyA⟩⁻¹ := rfl
      have h1 : (MulAut.conj : ↥C →* MulAut ↥C) (u * v * u⁻¹ * v⁻¹) = 1 := by
        rw [show u * v * u⁻¹ * v⁻¹ = (1 : ↥C) by rw [huv]; group, map_one]
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv, ← h1]
      simp only [map_mul, map_inv]
    refine ⟨mul_mem hxA hyA, ?_, u * v, ?_, mul_mem huU hvU⟩
    · rw [(Commute.mul_pow hcomm 2 : (x * y) ^ 2 = x ^ 2 * y ^ 2), hx2, hy2, one_mul]
    · have e : (⟨x * y, le_normalizer (mul_mem hxA hyA)⟩ : normalizer (A : Set G)) =
          ⟨x, le_normalizer hxA⟩ * ⟨y, le_normalizer hyA⟩ := rfl
      rw [e, map_mul, hu, hv, map_mul]
  | inv x _ hx =>
    obtain ⟨hxA, hx2, u, hu, huU⟩ := hx
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq, hx2])
    rw [hxi]
    exact ⟨hxA, hx2, u, hu, huU⟩

theorem commute_of_mem_twoLift {a b : G} (ha : a ∈ twoLift ψ U) (hb : b ∈ twoLift ψ U) :
    a * b = b * a := by
  obtain ⟨haA, ha2, u, hu, huU⟩ := (mem_twoLift hψ hZ hUc).1 ha
  obtain ⟨hbA, hb2, v, hv, hvU⟩ := (mem_twoLift hψ hZ hUc).1 hb
  have hab : a * b ∈ twoLift ψ U := mul_mem ha hb
  have hba : b * a ∈ twoLift ψ U := mul_mem hb ha
  obtain ⟨-, hab2, -⟩ := (mem_twoLift hψ hZ hUc).1 hab
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← sq, ha2])
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq, hb2])
  have h1 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rw [← sq, hab2])
  rw [mul_inv_rev, hai, hbi] at h1
  exact h1.symm

theorem sq_eq_one_of_mem_twoLift {a : G} (ha : a ∈ twoLift ψ U) : a ^ 2 = 1 :=
  ((mem_twoLift hψ hZ hUc).1 ha).2.1

theorem isElemAbelian_twoLift : CFSG.Open.IsElemAbelian 2 (twoLift ψ U) :=
  ⟨⟨⟨fun a b => Subtype.ext (commute_of_mem_twoLift hψ hZ hUc a.2 b.2)⟩⟩,
    fun _ ha => sq_eq_one_of_mem_twoLift hψ hZ hUc ha⟩

omit hUc in
theorem eq_of_sq_eq_one {a b : G} (ha : a ∈ A) (hb : b ∈ A) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (h : ψ ⟨a, le_normalizer ha⟩ = ψ ⟨b, le_normalizer hb⟩) : a = b :=
  eq_of_psi_eq hψ hZ ha hb (k := 1) (by rw [pow_one]; exact ha2) (by rw [pow_one]; exact hb2) h

omit hUc in
theorem exists_sq_eq_one_of_sq (y : ↥C) (hy2 : y ^ 2 = 1) :
    ∃ a : G, ∃ ha : a ∈ A, a ^ 2 = 1 ∧ ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y := by
  obtain ⟨a₀, ha₀, h₀⟩ := hψ.exists_eq (MulAut.conj y) ⟨y, rfl⟩
  set m := Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G) with hm
  obtain ⟨k, hk⟩ := hZ
  have ha₀N := le_normalizer ha₀
  have hsqN : a₀ ^ 2 ∈ normalizer (A : Set G) := pow_mem ha₀N 2
  have hsqZ : a₀ ^ 2 ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨pow_mem ha₀ 2, (hψ.eq_one_iff ⟨_, hsqN⟩).1 ?_⟩
    have e : (⟨a₀ ^ 2, hsqN⟩ : normalizer (A : Set G)) = ⟨a₀, ha₀N⟩ ^ 2 := rfl
    rw [e, map_pow, h₀, ← map_pow, hy2, map_one]
  have hpow : (a₀ ^ 2) ^ m = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hsqZ)
  refine ⟨a₀ ^ m, pow_mem ha₀ m, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hpow]
  · have e : (⟨a₀ ^ m, le_normalizer (pow_mem ha₀ m)⟩ : normalizer (A : Set G)) =
        ⟨a₀, ha₀N⟩ ^ m := rfl
    rw [e, map_pow, h₀, ← map_pow, hk, pow_succ, pow_mul, hy2, one_pow, one_mul]

omit hUc in
include hU2 in
theorem exists_mem_twoLift (y : ↥C) (hyU : (y : M) ∈ U) :
    ∃ a ∈ twoLift ψ U, ∃ ha : a ∈ A, ψ ⟨a, le_normalizer ha⟩ = MulAut.conj y := by
  have hy2 : y ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hU2 _ hyU)
  obtain ⟨a, ha, ha2, hay⟩ := exists_sq_eq_one_of_sq hψ hZ y hy2
  exact ⟨a, mem_twoLift_of ha ha2 hay hyU, ha, hay⟩

theorem eq_of_mem_twoLift {a b : G} (ha : a ∈ twoLift ψ U) (hb : b ∈ twoLift ψ U)
    (h : ψ ⟨a, le_normalizer (twoLift_le ha)⟩ = ψ ⟨b, le_normalizer (twoLift_le hb)⟩) : a = b :=
  eq_of_sq_eq_one hψ hZ (twoLift_le ha) (twoLift_le hb) (sq_eq_one_of_mem_twoLift hψ hZ hUc ha)
    (sq_eq_one_of_mem_twoLift hψ hZ hUc hb) h

include hU2 in
theorem card_twoLift (hZC : center ↥C = ⊥) :
    Nat.card (twoLift ψ U) = Nat.card (U.subgroupOf C) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have key : ∀ a : twoLift ψ U, ∃ y : U.subgroupOf C,
      ψ ⟨a, le_normalizer (twoLift_le a.2)⟩ = MulAut.conj (y : ↥C) := by
    intro a
    obtain ⟨_, -, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc).1 a.2
    exact ⟨⟨y, mem_subgroupOf.2 hyU⟩, hy⟩
  choose f hf using key
  refine Nat.card_eq_of_bijective f ⟨fun a b hab => ?_, fun y => ?_⟩
  · refine Subtype.ext (eq_of_mem_twoLift hψ hZ hUc a.2 b.2 ?_)
    rw [hf a, hf b, hab]
  · obtain ⟨a, ha, haA, hay⟩ := exists_mem_twoLift hψ hZ hU2 (y : ↥C) (mem_subgroupOf.1 y.2)
    refine ⟨⟨a, ha⟩, Subtype.ext (hinj ?_)⟩
    rw [← hf ⟨a, ha⟩]
    exact hay

theorem mem_normalizer_twoLift {n : G} (hn : n ∈ normalizer (A : Set G))
    (h : ∀ y : ↥C, (y : M) ∈ U ↔ ((ψ ⟨n, hn⟩ y : ↥C) : M) ∈ U) :
    n ∈ normalizer (twoLift ψ U : Set G) := by
  have key : ∀ (m : G) (hm : m ∈ normalizer (A : Set G)),
      (∀ y : ↥C, (y : M) ∈ U → ((ψ ⟨m, hm⟩ y : ↥C) : M) ∈ U) →
        ∀ a ∈ twoLift ψ U, m * a * m⁻¹ ∈ twoLift ψ U := by
    intro m hm hmU a ha
    obtain ⟨haA, ha2, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc).1 ha
    have hmaA : m * a * m⁻¹ ∈ A := (mem_normalizer_iff.1 hm a).1 haA
    refine mem_twoLift_of hmaA ?_ (y := ψ ⟨m, hm⟩ y) ?_ (hmU y hyU)
    · rw [conj_pow, ha2, mul_one, mul_inv_cancel]
    · have e : (⟨m * a * m⁻¹, le_normalizer hmaA⟩ : normalizer (A : Set G)) =
          ⟨m, hm⟩ * ⟨a, le_normalizer haA⟩ * ⟨m, hm⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hy, RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv]
  refine mem_normalizer_iff.2 fun a => ⟨key n hn (fun y hy => (h y).1 hy) a, fun ha => ?_⟩
  have hn' : n⁻¹ ∈ normalizer (A : Set G) := inv_mem hn
  have hU' : ∀ y : ↥C, (y : M) ∈ U → ((ψ ⟨n⁻¹, hn'⟩ y : ↥C) : M) ∈ U := by
    intro y hy
    have e : (⟨n⁻¹, hn'⟩ : normalizer (A : Set G)) = (⟨n, hn⟩ : normalizer (A : Set G))⁻¹ := rfl
    rw [e, map_inv]
    refine (h _).2 ?_
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    exact hy
  have := key n⁻¹ hn' hU' _ ha
  rwa [inv_inv, show n⁻¹ * (n * a * n⁻¹) * n = a by group] at this

omit hUc in
include hU2 in
theorem twoLift_eq_sup (hUc' : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {U₁ U₂ : Subgroup M}
    (hU₁ : U₁ ≤ U) (hU₂ : U₂ ≤ U)
    (hdec : ∀ y : ↥C, (y : M) ∈ U → ∃ y₁ y₂ : ↥C, (y₁ : M) ∈ U₁ ∧ (y₂ : M) ∈ U₂ ∧ y = y₁ * y₂) :
    twoLift ψ U = twoLift ψ U₁ ⊔ twoLift ψ U₂ := by
  refine le_antisymm (fun b hb => ?_) (sup_le (twoLift_mono hU₁) (twoLift_mono hU₂))
  obtain ⟨hbA, -, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc').1 hb
  obtain ⟨y₁, y₂, hy₁, hy₂, rfl⟩ := hdec y hyU
  obtain ⟨b₁, hb₁, hb₁A, hb₁ψ⟩ := exists_mem_twoLift hψ hZ (fun u hu => hU2 u (hU₁ hu)) y₁ hy₁
  obtain ⟨b₂, hb₂, hb₂A, hb₂ψ⟩ := exists_mem_twoLift hψ hZ (fun u hu => hU2 u (hU₂ hu)) y₂ hy₂
  have hb₁₂ : b₁ * b₂ ∈ twoLift ψ U := mul_mem (twoLift_mono hU₁ hb₁) (twoLift_mono hU₂ hb₂)
  have e : b = b₁ * b₂ := by
    refine eq_of_mem_twoLift hψ hZ hUc' hb hb₁₂ ?_
    have e2 : (⟨b₁ * b₂, le_normalizer (twoLift_le hb₁₂)⟩ : normalizer (A : Set G)) =
        ⟨b₁, le_normalizer hb₁A⟩ * ⟨b₂, le_normalizer hb₂A⟩ := rfl
    rw [e2, map_mul, hb₁ψ, hb₂ψ, ← map_mul]
    exact hy
  rw [e]
  exact mul_mem (mem_sup_left hb₁) (mem_sup_right hb₂)

omit hUc in
theorem map_conj_twoLift (hUc' : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {U' : Subgroup M}
    (hUc'' : ∀ u ∈ U', ∀ v ∈ U', u * v = v * u) {a : G} (ha : a ∈ A) {c : ↥C}
    (hc : ψ ⟨a, le_normalizer ha⟩ = MulAut.conj c)
    (hUU : ∀ y : ↥C, (y : M) ∈ U ↔ ((c * y * c⁻¹ : ↥C) : M) ∈ U') :
    (twoLift ψ U).map (MulAut.conj a).toMonoidHom = twoLift ψ U' := by
  ext x
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  have haN := le_normalizer ha
  constructor
  · intro hx
    obtain ⟨hxA, hx2, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc').1 hx
    have e : x = a * (a⁻¹ * x * a) * a⁻¹ := by group
    have hxA' : x ∈ A := by rw [e]; exact mul_mem (mul_mem ha hxA) (inv_mem ha)
    have hxA'' : a * (a⁻¹ * x * a) * a⁻¹ ∈ A := by rw [← e]; exact hxA'
    refine mem_twoLift_of hxA' ?_ (y := c * y * c⁻¹) ?_ ((hUU y).1 hyU)
    · rw [e, conj_pow, hx2, mul_one, mul_inv_cancel]
    · have h1 := psi_conj_eq_conj' (ψ := ψ) haN hxA hy hxA''
      have h2 : (⟨x, le_normalizer hxA'⟩ : normalizer (A : Set G)) =
          ⟨a * (a⁻¹ * x * a) * a⁻¹, le_normalizer hxA''⟩ := Subtype.ext e
      rw [h2, h1, hc, MulAut.conj_apply]
  · intro hx
    obtain ⟨hxA, hx2, y, hy, hyU⟩ := (mem_twoLift hψ hZ hUc'').1 hx
    have hxA' : a⁻¹ * x * a ∈ A := mul_mem (mul_mem (inv_mem ha) hxA) ha
    have hxA'' : a⁻¹ * x * a⁻¹⁻¹ ∈ A := by rw [inv_inv]; exact hxA'
    refine mem_twoLift_of hxA' ?_ (y := c⁻¹ * y * c) ?_ ((hUU _).2 ?_)
    · rw [show a⁻¹ * x * a = a⁻¹ * x * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hx2, mul_one,
        mul_inv_cancel]
    · have h1 := psi_conj_eq_conj' (ψ := ψ) (inv_mem haN) hxA hy hxA''
      have h2 : (⟨a⁻¹ * x * a, le_normalizer hxA'⟩ : normalizer (A : Set G)) =
          ⟨a⁻¹ * x * a⁻¹⁻¹, le_normalizer hxA''⟩ := Subtype.ext (by simp only [inv_inv])
      have h3 : ψ ⟨a⁻¹, inv_mem haN⟩ = MulAut.conj c⁻¹ := by
        have e : (⟨a⁻¹, inv_mem haN⟩ : normalizer (A : Set G)) = ⟨a, haN⟩⁻¹ := rfl
        rw [e, map_inv, hc, map_inv]
      rw [h2, h1, h3, MulAut.conj_apply, inv_inv]
    · rw [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
      exact hyU

end TwoLift

end CFSG.ComponentClassification.RankTwoExceptional
