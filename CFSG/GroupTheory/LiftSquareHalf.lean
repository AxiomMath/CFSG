module

public import CFSG.GroupTheory.FixedPointQuotientCard

public section

namespace CFSG.GroupTheory

open CFSG
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_inv_eq_of_card_fix_sq {V : Type*} [Group V] [Finite V]
    (hc : ∀ a b : V, a * b = b * a) (hsq : ∀ v : V, v * v = 1) {σ : MulAut V}
    (hσσ : ∀ v, σ (σ v) = v) (hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card V) :
    ∀ v : V, σ v = v → ∃ u : V, σ u * u⁻¹ = v := by
  intro v hv
  let φ : V →* V :=
    MonoidHom.mk' (fun v => σ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * ((σ b * b⁻¹) * a⁻¹) := by group
        _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hc (σ b * b⁻¹) a⁻¹]
        _ = σ a * a⁻¹ * (σ b * b⁻¹) := by group)
  have hker : ∀ v, v ∈ φ.ker ↔ σ v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    exact mul_inv_eq_one
  have hkerEq : φ.ker = autFixedSubgroup σ := Subgroup.ext fun v => by
    rw [hker, mem_autFixedSubgroup]
  have hrle : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker]
    show σ (σ v * v⁻¹) = σ v * v⁻¹
    rw [map_mul, map_inv, hσσ]
    have h1 : v = v⁻¹ := (inv_eq_of_mul_eq_one_left (hsq v)).symm
    have h2 : σ v = (σ v)⁻¹ := (inv_eq_of_mul_eq_one_left (hsq (σ v))).symm
    rw [← h1, ← h2]
    exact hc _ _
  have hcard2 : Nat.card φ.ker * Nat.card φ.range = Nat.card V :=
    Subgroup.card_ker_mul_card_range φ
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hrcard : Nat.card φ.ker ≤ Nat.card φ.range := by
    have h1 : Nat.card φ.ker * Nat.card φ.ker = Nat.card φ.ker * Nat.card φ.range := by
      rw [hcard2, ← hcard, hkerEq, sq]
    exact (Nat.eq_of_mul_eq_mul_left hkpos h1).le
  have hreq : φ.range = φ.ker := Subgroup.eq_of_le_of_card_ge hrle hrcard
  have hvker : v ∈ φ.ker := (hker v).mpr hv
  rw [← hreq] at hvker
  exact hvker

section JLevel

variable {J Z : Subgroup G} [(Z.subgroupOf J).Normal]

omit [Finite G] [(Z.subgroupOf J).Normal] in
private theorem mk_eq_iff {a b : G} (ha : a ∈ J) (hb : b ∈ J) :
    (QuotientGroup.mk ⟨a, ha⟩ : ↥J ⧸ Z.subgroupOf J) = QuotientGroup.mk ⟨b, hb⟩ ↔
      a⁻¹ * b ∈ Z := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

omit [Finite G] in
private theorem mk_eq_one_iff {a : G} (ha : a ∈ J) :
    (QuotientGroup.mk ⟨a, ha⟩ : ↥J ⧸ Z.subgroupOf J) = 1 ↔ a ∈ Z := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

omit [Finite G] in
private theorem quot_comm (hJ' : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ Z) (u v : ↥J ⧸ Z.subgroupOf J) :
    u * v = v * u := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  refine (mk_eq_iff (Z := Z) (J.mul_mem ha hb) (J.mul_mem hb ha)).mpr ?_
  have h1 := hJ' b⁻¹ (J.inv_mem hb) a⁻¹ (J.inv_mem ha)
  have h2 : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact h1

omit [Finite G] in
private theorem quot_sq (hJ2 : ∀ j ∈ J, j * j ∈ Z) (v : ↥J ⧸ Z.subgroupOf J) : v * v = 1 := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective v
  rw [← QuotientGroup.mk_mul]
  exact (mk_eq_one_iff (Z := Z) (J.mul_mem ha ha)).mpr (hJ2 a ha)

theorem exists_conj_mul_mem_of_card_fix_sq
    (hJ' : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ Z) (hJ2 : ∀ j ∈ J, j * j ∈ Z)
    {x : G} (hx : x ∈ Subgroup.normalizer (J : Set G)) (hxx : x * x ∈ J)
    {σ : MulAut (↥J ⧸ Z.subgroupOf J)}
    (hσ : ∀ (j : G) (hj : j ∈ J), σ (QuotientGroup.mk ⟨j, hj⟩) =
      QuotientGroup.mk ⟨x * j * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx j).mp hj⟩)
    (hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card (↥J ⧸ Z.subgroupOf J))
    {y₁ y₂ : G} (h₁ : x⁻¹ * y₁ ∈ J) (h₂ : x⁻¹ * y₂ ∈ J) (hy₁ : y₁ * y₁ ∈ Z)
    (hy₂ : y₂ * y₂ ∈ Z) : ∃ k ∈ J, ∃ e ∈ Z, k * y₂ * k⁻¹ = y₁ * e := by
  have hc := quot_comm (Z := Z) hJ'
  have hsq := quot_sq (Z := Z) hJ2
  have hinvV : ∀ v : ↥J ⧸ Z.subgroupOf J, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have hxJ' : ∀ a ∈ J, x⁻¹ * a * x ∈ J := fun a ha => by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hx) a).mp ha
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk_surjective v
    rw [hσ j hj, hσ _ ((Subgroup.mem_normalizer_iff.mp hx j).mp hj)]
    refine (mk_eq_iff (Z := Z) _ hj).mpr ?_
    have h1 := hJ' (x * x) hxx j⁻¹ (J.inv_mem hj)
    have h2 : (x * (x * j * x⁻¹) * x⁻¹)⁻¹ * j = ⁅x * x, j⁻¹⁆ := by
      have e : x * (x * j * x⁻¹) * x⁻¹ = (x * x) * j * (x * x)⁻¹ := by group
      rw [e]
      generalize x * x = w
      rw [commutatorElement_def]
      group
    rw [h2]
    exact h1
  have hσ' : ∀ (a : G) (ha : a ∈ J),
      (QuotientGroup.mk ⟨x⁻¹ * a * x, hxJ' a ha⟩ : ↥J ⧸ Z.subgroupOf J) =
        σ (QuotientGroup.mk ⟨a, ha⟩) := by
    intro a ha
    have h1 : σ (QuotientGroup.mk ⟨x⁻¹ * a * x, hxJ' a ha⟩) = QuotientGroup.mk ⟨a, ha⟩ := by
      rw [hσ _ (hxJ' a ha)]
      congr 1
      apply Subtype.ext
      show x * (x⁻¹ * a * x) * x⁻¹ = a
      group
    calc (QuotientGroup.mk ⟨x⁻¹ * a * x, hxJ' a ha⟩ : ↥J ⧸ Z.subgroupOf J)
        = σ (σ (QuotientGroup.mk ⟨x⁻¹ * a * x, hxJ' a ha⟩)) := (hσσ _).symm
      _ = σ (QuotientGroup.mk ⟨a, ha⟩) := by rw [h1]
  have hE : ∀ (y : G) (hy : x⁻¹ * y ∈ J), y * y ∈ Z →
      σ (QuotientGroup.mk ⟨x⁻¹ * y, hy⟩) * QuotientGroup.mk ⟨x⁻¹ * y, hy⟩ =
        (QuotientGroup.mk ⟨x * x, hxx⟩ : ↥J ⧸ Z.subgroupOf J)⁻¹ := by
    intro y hy hyy
    rw [← hσ' _ hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    refine (mk_eq_iff (Z := Z) (J.mul_mem (hxJ' _ hy) hy) (J.inv_mem hxx)).mpr ?_
    have h1 : (x⁻¹ * (x⁻¹ * y) * x * (x⁻¹ * y))⁻¹ * (x * x)⁻¹ = (y * y)⁻¹ := by group
    show (x⁻¹ * (x⁻¹ * y) * x * (x⁻¹ * y))⁻¹ * (x * x)⁻¹ ∈ Z
    rw [h1]
    exact Z.inv_mem hyy
  set ā₁ : ↥J ⧸ Z.subgroupOf J := QuotientGroup.mk ⟨x⁻¹ * y₁, h₁⟩ with hā₁
  set ā₂ : ↥J ⧸ Z.subgroupOf J := QuotientGroup.mk ⟨x⁻¹ * y₂, h₂⟩ with hā₂
  have hE₁ := hE y₁ h₁ hy₁
  have hE₂ := hE y₂ h₂ hy₂
  have hd : σ (ā₁ * ā₂⁻¹) = ā₁ * ā₂⁻¹ := by
    rw [map_mul, map_inv, hinvV ā₂, hinvV (σ ā₂)]
    have h12 : σ ā₁ * ā₁ = σ ā₂ * ā₂ := by rw [hE₁, hE₂]
    have h0 : (σ ā₁ * σ ā₂) * (ā₁ * ā₂) = 1 := by
      calc (σ ā₁ * σ ā₂) * (ā₁ * ā₂) = σ ā₁ * (σ ā₂ * ā₁) * ā₂ := by simp only [mul_assoc]
        _ = σ ā₁ * (ā₁ * σ ā₂) * ā₂ := by rw [hc (σ ā₂) ā₁]
        _ = (σ ā₁ * ā₁) * (σ ā₂ * ā₂) := by simp only [mul_assoc]
        _ = (σ ā₂ * ā₂) * (σ ā₂ * ā₂) := by rw [h12]
        _ = 1 := hsq _
    calc σ ā₁ * σ ā₂ = (ā₁ * ā₂)⁻¹ := eq_inv_of_mul_eq_one_left h0
      _ = ā₁ * ā₂ := hinvV _
  obtain ⟨u₀, hu₀⟩ := exists_mul_inv_eq_of_card_fix_sq hc hsq hσσ hcard _ hd
  obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective u₀
  have heJ : (x⁻¹ * y₁)⁻¹ * (x⁻¹ * u * x) * (x⁻¹ * y₂) * u⁻¹ ∈ J :=
    J.mul_mem (J.mul_mem (J.mul_mem (J.inv_mem h₁) (hxJ' u hu)) h₂) (J.inv_mem hu)
  refine ⟨u, hu, (x⁻¹ * y₁)⁻¹ * (x⁻¹ * u * x) * (x⁻¹ * y₂) * u⁻¹, ?_, ?_⟩
  · refine (mk_eq_one_iff (Z := Z) heJ).mp ?_
    have h1 : (QuotientGroup.mk ⟨(x⁻¹ * y₁)⁻¹ * (x⁻¹ * u * x) * (x⁻¹ * y₂) * u⁻¹, heJ⟩ :
        ↥J ⧸ Z.subgroupOf J) =
        ā₁⁻¹ * σ (QuotientGroup.mk ⟨u, hu⟩) * ā₂ * (QuotientGroup.mk ⟨u, hu⟩)⁻¹ := by
      rw [← hσ' u hu]
      rfl
    rw [h1]
    set ū : ↥J ⧸ Z.subgroupOf J := QuotientGroup.mk ⟨u, hu⟩ with hū
    have h2 : ū * ā₂ * ū⁻¹ = ā₂ := by
      rw [hc ū ā₂, mul_inv_cancel_right]
    calc ā₁⁻¹ * σ ū * ā₂ * ū⁻¹ = ā₁⁻¹ * (σ ū * ū⁻¹) * (ū * ā₂ * ū⁻¹) := by group
      _ = ā₁⁻¹ * (ā₁ * ā₂⁻¹) * ā₂ := by rw [hu₀, h2]
      _ = 1 := by group
  · group

theorem mul_self_eq_of_card_fix_sq
    (hZc : ∀ c ∈ Z, ∀ j ∈ J, j * c = c * j) (hZ2 : ∀ c ∈ Z, c * c = 1)
    (hJ' : ∀ a ∈ J, ∀ b ∈ J, ⁅a, b⁆ ∈ Z) (hJ2 : ∀ j ∈ J, j * j ∈ Z)
    {x : G} (hx : x ∈ Subgroup.normalizer (J : Set G)) (hxZ : ∀ c ∈ Z, x * c = c * x)
    (hxx : x * x ∈ J)
    {σ : MulAut (↥J ⧸ Z.subgroupOf J)}
    (hσ : ∀ (j : G) (hj : j ∈ J), σ (QuotientGroup.mk ⟨j, hj⟩) =
      QuotientGroup.mk ⟨x * j * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx j).mp hj⟩)
    (hcard : Nat.card (autFixedSubgroup σ) ^ 2 = Nat.card (↥J ⧸ Z.subgroupOf J))
    {y₁ y₂ : G} (h₁ : x⁻¹ * y₁ ∈ J) (h₂ : x⁻¹ * y₂ ∈ J) (hy₁ : y₁ * y₁ ∈ Z)
    (hy₂ : y₂ * y₂ ∈ Z) : y₁ * y₁ = y₂ * y₂ := by
  obtain ⟨k, hk, e, he, hke⟩ :=
    exists_conj_mul_mem_of_card_fix_sq hJ' hJ2 hx hxx hσ hcard h₁ h₂ hy₁ hy₂
  have hkc : k * (y₂ * y₂) = (y₂ * y₂) * k := hZc _ hy₂ k hk
  have hy₂k : (k * y₂ * k⁻¹) * (k * y₂ * k⁻¹) = y₂ * y₂ := by
    calc (k * y₂ * k⁻¹) * (k * y₂ * k⁻¹) = k * (y₂ * y₂) * k⁻¹ := by group
      _ = y₂ * y₂ := by rw [hkc]; group
  have he2 : e * e = 1 := hZ2 e he
  have hy₁e : y₁ * e = e * y₁ := by
    have h1 : y₁ = x * (x⁻¹ * y₁) := by group
    have h2 : x * e = e * x := hxZ e he
    have h3 : (x⁻¹ * y₁) * e = e * (x⁻¹ * y₁) := (hZc e he _ h₁)
    calc y₁ * e = x * ((x⁻¹ * y₁) * e) := by rw [h1]; group
      _ = x * (e * (x⁻¹ * y₁)) := by rw [h3]
      _ = (x * e) * (x⁻¹ * y₁) := by group
      _ = e * (x * (x⁻¹ * y₁)) := by rw [h2]; group
      _ = e * y₁ := by group
  calc y₁ * y₁ = (y₁ * y₁) * (e * e) := by rw [he2, mul_one]
    _ = (y₁ * e) * (y₁ * e) := by
        calc (y₁ * y₁) * (e * e) = y₁ * (y₁ * e) * e := by group
          _ = y₁ * (e * y₁) * e := by rw [hy₁e]
          _ = (y₁ * e) * (y₁ * e) := by group
    _ = (k * y₂ * k⁻¹) * (k * y₂ * k⁻¹) := by rw [hke]
    _ = y₂ * y₂ := hy₂k

end JLevel

end CFSG.GroupTheory
