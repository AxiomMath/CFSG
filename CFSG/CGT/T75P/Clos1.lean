module

public import CFSG.CGT.T75P.DecD
public import CFSG.CGT.T75P.ClosGen

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G] {T T₁ : Subgroup G}

structure Std81 (T T₁ : Subgroup G) : Prop where
  h1 : Sec4NoA
  h62 : Sec62
  h63 : Sec63
  h66 : Sec66
  hc : Sec6Ctx T T₁ 3 1
  hnat : NaturalSL T (hSub T (normIn T₁ T)) 3 1

@[expose] def Uc (T T₁ : Subgroup G) : Subgroup G := hSub T (normIn T₁ T) ⊔ T₁

theorem hSub_le_Uc : hSub T (normIn T₁ T) ≤ Uc T T₁ := le_sup_left

theorem T₁_le_Uc : T₁ ≤ Uc T T₁ := le_sup_right

theorem T_le_Uc : T ≤ Uc T T₁ := (hSub_data T T₁).1.trans hSub_le_Uc

theorem sup_le_Uc : T ⊔ T₁ ≤ Uc T T₁ := sup_le T_le_Uc T₁_le_Uc

theorem Std81.finite (s : Std81 T T₁) : Finite G := s.hc.finite

theorem Std81.hA8 : ¬ (3 = 4 ∧ 1 = 1) := by omega

theorem Std81.exists_ne_one (s : Std81 T T₁) : ∃ t ∈ T, t ≠ 1 := by
  have h4 := s.hc.hy.card
  by_contra hcon
  push Not at hcon
  have : T = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    exact hcon t ht
  rw [this, Subgroup.card_bot] at h4
  omega

theorem Std81.card_T (s : Std81 T T₁) : Nat.card T = 8 := by
  have := s.hc.hT
  norm_num at this
  exact this

theorem mem_deltaOf_Uc_of_mem_normD (s : Std81 T T₁) {x : G} (hx : x ∈ normD T) :
    x ∈ DeltaOf T (Uc T T₁) := by
  classical
  have hfin : Finite G := s.finite
  obtain ⟨x₀, hx₀X, hx₀⟩ := s.hc.sec3.conj
  have hx₀U : x₀ ∈ Uc T T₁ := sup_le_Uc hx₀X
  by_cases hxT : x ∈ T
  · exact mem_deltaOf_of_mem hxT (ne_one_of_mem_classD hx.1)
  · obtain ⟨ℓ₀, hℓ₀, hℓ₀1⟩ := exists_ne_one_mem_normIn s.hc
    obtain ⟨hℓD, hℓN, hℓT⟩ := mem_normD_of_mem_normIn s.hc hℓ₀ hℓ₀1
    obtain ⟨g, hg, hxg⟩ :=
      s.hc.sec67_conj s.h1 s.h62 s.h63 Std81.hA8 s.hnat ℓ₀ ⟨hℓD, hℓN⟩ hℓT x hx hxT
    obtain ⟨h, hh, c, hcC, hgh⟩ := normalizer_eq_mul s.h62 s.h63 s.hc s.hnat chain3 hg
    have hℓH : ℓ₀ ∈ hSub T (normIn T₁ T) := le_hSub hℓ₀
    have hcomm : ℓ₀ * c = c * ℓ₀ := Subgroup.mem_centralizer_iff.1 hcC ℓ₀ hℓH
    have hxh : x = h * ℓ₀ * h⁻¹ := by
      rw [hxg, hgh]
      calc h * c * ℓ₀ * (h * c)⁻¹ = h * (c * ℓ₀) * c⁻¹ * h⁻¹ := by group
        _ = h * (ℓ₀ * c) * c⁻¹ * h⁻¹ := by rw [hcomm]
        _ = h * ℓ₀ * h⁻¹ := by group
    have hℓT₁ : ℓ₀ ∈ T₁ := (mem_normIn.1 hℓ₀).1
    have hℓmem : x₀⁻¹ * ℓ₀ * x₀ ∈ T := by
      have : ℓ₀ ∈ conjSubgroup x₀ T := hx₀ ▸ hℓT₁
      exact mem_conjSubgroup.1 this
    refine ⟨h * x₀, (Uc T T₁).mul_mem (hSub_le_Uc hh) hx₀U, x₀⁻¹ * ℓ₀ * x₀, hℓmem, ?_, ?_⟩
    · intro h1
      apply hℓ₀1
      calc ℓ₀ = x₀ * (x₀⁻¹ * ℓ₀ * x₀) * x₀⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · rw [hxh]
      group

theorem Std81.h66' (s : Std81 T T₁) :
    ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T :=
  fun x hx y hy h4 => s.h66 G T T₁ 3 1 s.hc x hx y hy h4

theorem Std81.closure_normD (s : Std81 T T₁) :
    Subgroup.closure (normD T) = hSub T (normIn T₁ T) :=
  s.hc.closure_normD_of_not_a8 s.h1 s.h63 Std81.hA8

theorem Std81.normD_le (s : Std81 T T₁) {x : G} (hx : x ∈ normD T) :
    x ∈ hSub T (normIn T₁ T) :=
  s.hc.normD_le_hSub_of_not_a8 s.h1 s.h63 Std81.hA8 hx

theorem Std81.exists_comm (s : Std81 T T₁) {x : G} (hx : x ∈ normD T) (hxT : x ∉ T) :
    ∃ d ∈ T, d ≠ 1 ∧ x * d = d * x := by
  have hfin : Finite G := s.finite
  have hcard := s.hc.card_centralizer_eq s.h63 Std81.hA8 hx hxT
  have hL : Nat.card (normIn T T₁) = 4 := by
    rw [s.hc.card_normIn]
    norm_num
  rw [hL] at hcard
  have hne : T ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  obtain ⟨⟨d, hd⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  refine ⟨d, hd.1, fun h => hd1 (Subtype.ext h), ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.1 hd.2).symm

theorem Std81.uc_le_closure (s : Std81 T T₁) {c : G} (hcU : ∀ u ∈ Uc T T₁, c * u = u * c) :
    Uc T T₁ ≤ Subgroup.closure {d | d ∈ classD T ∧ c * d = d * c} := by
  refine sup_le ?_ ?_
  · rw [← s.closure_normD]
    refine Subgroup.closure_mono ?_
    intro x hx
    exact ⟨hx.1, hcU x (hSub_le_Uc (s.normD_le hx))⟩
  · intro t₁ ht₁
    by_cases ht1 : t₁ = 1
    · rw [ht1]
      exact Subgroup.one_mem _
    · obtain ⟨x₀, -, hx₀⟩ := s.hc.sec3.conj
      have hmem : t₁ ∈ conjSubgroup x₀ T := hx₀ ▸ ht₁
      exact Subgroup.subset_closure
        ⟨mem_classD_of_mem_conjSubgroup hmem ht1, hcU t₁ (T₁_le_Uc ht₁)⟩

theorem closed_CD81 (s : Std81 T T₁) {c : G} (hcU : ∀ u ∈ Uc T T₁, c * u = u * c) {d : G}
    (hd : d ∈ classD T) (hcd : c * d = d * c) {x : G} (hx : x ∈ classD T) (hxd : x * d = d * x) :
    c * x = x * c := by
  have hfin : Finite G := s.finite
  exact closed_CD s.hc.hy.pair.wc (fun x hx => mem_deltaOf_Uc_of_mem_normD s hx) s.h66'
    T_le_Uc s.exists_ne_one (fun t ht => hcU t (T_le_Uc ht)) (s.uc_le_closure hcU) hd hcd hx hxd

theorem closed_CD81_conj (s : Std81 T T₁) {c : G} (hcU : ∀ u ∈ Uc T T₁, c * u = u * c) {g m : G}
    (hm : m = g * c * g⁻¹) {d : G} (hd : d ∈ classD T) (hmd : m * d = d * m) {x : G}
    (hx : x ∈ classD T) (hxd : x * d = d * x) : m * x = x * m := by
  have hd' : g⁻¹ * d * g ∈ classD T := classD_conj hd g
  have hx' : g⁻¹ * x * g ∈ classD T := classD_conj hx g
  have hcd : c * (g⁻¹ * d * g) = (g⁻¹ * d * g) * c := by
    have h1 : g * c * g⁻¹ * d = d * (g * c * g⁻¹) := by rw [← hm]; exact hmd
    calc c * (g⁻¹ * d * g) = g⁻¹ * (g * c * g⁻¹ * d) * g := by group
      _ = g⁻¹ * (d * (g * c * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * d * g) * c := by group
  have hxd' : (g⁻¹ * x * g) * (g⁻¹ * d * g) = (g⁻¹ * d * g) * (g⁻¹ * x * g) := by
    calc (g⁻¹ * x * g) * (g⁻¹ * d * g) = g⁻¹ * (x * d) * g := by group
      _ = g⁻¹ * (d * x) * g := by rw [hxd]
      _ = (g⁻¹ * d * g) * (g⁻¹ * x * g) := by group
  have h2 := closed_CD81 s hcU hd' hcd hx' hxd'
  calc m * x = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [hm]; group
    _ = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by rw [h2]
    _ = x * m := by rw [hm]; group

theorem fus81 (s : Std81 T T₁) {c : G} (hcU : ∀ u ∈ Uc T T₁, c * u = u * c) {g m : G}
    (hm : m = g * c * g⁻¹) (hmN : m ∈ Subgroup.normalizer (T : Set G)) {n : ℕ}
    (hm2 : m ^ 2 ^ n = 1) : ∀ u ∈ Uc T T₁, m * u = u * m := by
  classical
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  obtain ⟨d₁, hd₁T, hd₁1, hd₁m⟩ :=
    exists_fixed_ne_one (T := T) (by rw [s.card_T]; norm_num) hmN hm2
  have hcl : ∀ d ∈ {d | d ∈ classD T ∧ m * d = d * m}, ∀ x ∈ classD T, x * d = d * x →
      x ∈ {d | d ∈ classD T ∧ m * d = d * m} := fun d hd x hx hxd =>
    ⟨hx, closed_CD81_conj s hcU hm hd.1 hd.2 hx hxd⟩
  have hN : normD T ⊆ {d | d ∈ classD T ∧ m * d = d * m} :=
    normD_le_of_closed hWC hcl ⟨d₁, hd₁T, hd₁1, mem_classD_of_mem hd₁T hd₁1, hd₁m⟩
      (fun x hx hxT => s.exists_comm hx hxT)
  have hCm : Subgroup.centralizer ({m} : Set G) ≥ Uc T T₁ := by
    refine sup_le ?_ ?_
    · rw [← s.closure_normD, Subgroup.closure_le]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.2 (hN hx).2.symm
    · obtain ⟨ℓ₀, hℓ₀, hℓ₀1⟩ := exists_ne_one_mem_normIn s.hc
      obtain ⟨hℓD, hℓN, -⟩ := mem_normD_of_mem_normIn s.hc hℓ₀ hℓ₀1
      have hℓm : m * ℓ₀ = ℓ₀ * m := (hN ⟨hℓD, hℓN⟩).2
      obtain ⟨x₀, -, hx₀⟩ := s.hc.sec3.conj
      have hT₁ab : IsElemAbelian 2 T₁ := hx₀ ▸ isElemAbelian_conjSubgroup hWC.1 x₀
      have hℓT₁ : ℓ₀ ∈ T₁ := (mem_normIn.1 hℓ₀).1
      intro t₁ ht₁
      by_cases ht1 : t₁ = 1
      · rw [ht1]
        exact Subgroup.one_mem _
      · have hmem : t₁ ∈ conjSubgroup x₀ T := hx₀ ▸ ht₁
        have htD : t₁ ∈ classD T := mem_classD_of_mem_conjSubgroup hmem ht1
        have hcomm : t₁ * ℓ₀ = ℓ₀ * t₁ := elemAbelian_mul_comm hT₁ab ht₁ hℓT₁
        exact Subgroup.mem_centralizer_singleton_iff.2
          (closed_CD81_conj s hcU hm hℓD hℓm htD hcomm).symm
  intro u hu
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hCm hu)).symm

end CFSG.CGT.T75P
