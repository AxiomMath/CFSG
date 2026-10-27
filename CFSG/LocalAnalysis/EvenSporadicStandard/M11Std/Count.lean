module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Sign
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M11Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem orderOf_t : orderOf H.t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact H.t_sq) H.t_ne

theorem zpowers_t_le : zpowers H.t ≤ centralizer (H.L : Set G) :=
  zpowers_le.2 (mem_centralizer_iff.2 fun ℓ hℓ => (H.comm ℓ hℓ).symm)

theorem disjoint_L_zpowers : Disjoint H.L (zpowers H.t) := by
  rw [Subgroup.disjoint_def]
  intro x hxL hxt
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hxt
  rcases J1Std.zpow_eq_one_or_self H.t_sq n with h | h
  · exact h
  · exfalso
    rw [h] at hxL
    exact H.t_not_mem hxL

theorem card_centralizer : Nat.card (centralizer ({H.t} : Set G)) = 15840 := by
  rw [H.centralizer_eq]
  have e := mulEquivProdSup H.zpowers_t_le H.disjoint_L_zpowers
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, H.card_L, Nat.card_zpowers, H.orderOf_t]

@[expose] def I : Set G := {u | u ∈ H.L ∧ u * u = 1 ∧ u ≠ 1}

theorem orderOf_I {u : G} (hu : u ∈ H.I) : orderOf (⟨u, hu.1⟩ : H.L) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by rw [pow_two]; exact hu.2.1) hu.2.2

theorem ncard_I : H.I.ncard = 165 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Nat.card_coe_set_eq, ← H.card_inv]
  refine Nat.card_congr (Equiv.symm
    { toFun := fun u => ⟨(u.1 : G), u.1.2, ?_, ?_⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, H.orderOf_I x.2⟩
      left_inv := fun u => rfl
      right_inv := fun x => rfl })
  · have h := u.2
    rw [← Subgroup.orderOf_coe] at h
    exact (by rw [← pow_two]; exact (orderOf_eq_prime_iff.1 h).1 : (u.1 : G) * u.1 = 1)
  · have h := u.2
    rw [← Subgroup.orderOf_coe] at h
    exact (orderOf_eq_prime_iff.1 h).2

theorem z_mem_I : H.a ^ 4 ∈ H.I := by
  refine ⟨H.L.pow_mem H.a_mem 4, ?_, H.a4⟩
  rw [← pow_add]; exact H.a8

theorem I_conj {u v : G} (hu : u ∈ H.I) (hv : v ∈ H.I) : ∃ c ∈ H.L, c * u * c⁻¹ = v := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (H.conj_inv ⟨u, hu.1⟩ ⟨v, hv.1⟩ (H.orderOf_I hu) (H.orderOf_I hv))
  exact ⟨c, c.2, by simpa using congrArg Subtype.val hc⟩

theorem isConj_of_I {u v : G} (hu : u ∈ H.I) (hv : v ∈ H.I) (h : IsConj H.t u) :
    IsConj H.t v := by
  obtain ⟨c, -, rfl⟩ := H.I_conj hu hv
  exact h.trans (isConj_iff.2 ⟨c, rfl⟩)

theorem isConj_mul_of_I {u v : G} (hu : u ∈ H.I) (hv : v ∈ H.I) (h : IsConj H.t (H.t * u)) :
    IsConj H.t (H.t * v) := by
  obtain ⟨c, hc, rfl⟩ := H.I_conj hu hv
  refine h.trans (isConj_iff.2 ⟨c, ?_⟩)
  have hcomm : c * H.t = H.t * c := (H.comm c hc).symm
  calc c * (H.t * u) * c⁻¹ = (c * H.t) * u * c⁻¹ := by group
    _ = (H.t * c) * u * c⁻¹ := by rw [hcomm]
    _ = H.t * (c * u * c⁻¹) := by group

theorem invol_centralizer {x : G} (hx : x ∈ centralizer ({H.t} : Set G)) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : x = H.t ∨ x ∈ H.I ∨ ∃ u ∈ H.I, x = H.t * u := by
  rw [H.centralizer_eq] at hx
  obtain ⟨ℓ, hℓ, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer H.zpowers_t_le hx
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs
  rcases J1Std.zpow_eq_one_or_self H.t_sq n with h | h
  · rw [h, mul_one] at hx2 hx1 ⊢
    exact Or.inr (Or.inl ⟨hℓ, hx2, hx1⟩)
  · rw [h] at hx2 hx1 ⊢
    have hc : ℓ * H.t = H.t * ℓ := (H.comm ℓ hℓ).symm
    have hl2 : ℓ * ℓ = 1 := by
      calc ℓ * ℓ = ℓ * ℓ * (H.t * H.t) := by rw [H.t_sq, mul_one]
        _ = ℓ * (ℓ * H.t) * H.t := by simp only [mul_assoc]
        _ = ℓ * (H.t * ℓ) * H.t := by rw [hc]
        _ = (ℓ * H.t) * (ℓ * H.t) := by simp only [mul_assoc]
        _ = 1 := hx2
    by_cases hl1 : ℓ = 1
    · subst hl1; exact Or.inl (by simp)
    · exact Or.inr (Or.inr ⟨ℓ, ⟨hℓ, hl2, hl1⟩, by rw [hc]⟩)

@[expose] def F : Set G := {x | IsConj H.t x ∧ H.t * x = x * H.t}

theorem sq_of_isConj {x : G} (h : IsConj H.t x) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  calc c * H.t * c⁻¹ * (c * H.t * c⁻¹) = c * (H.t * H.t) * c⁻¹ := by group
    _ = 1 := by rw [H.t_sq]; group

theorem ne_one_of_isConj {x : G} (h : IsConj H.t x) : x ≠ 1 := by
  rintro rfl
  exact H.t_ne (isConj_one_left.1 h)

theorem F_eq (P₁ P₂ : Prop) (h₁ : ∀ u ∈ H.I, IsConj H.t u ↔ P₁)
    (h₂ : ∀ u ∈ H.I, IsConj H.t (H.t * u) ↔ P₂) :
    H.F = {H.t} ∪ {x | x ∈ H.I ∧ P₁} ∪ {x | (∃ u ∈ H.I, x = H.t * u) ∧ P₂} := by
  ext x
  simp only [F, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hc, hx⟩
    have hxC : x ∈ centralizer ({H.t} : Set G) := mem_centralizer_singleton_iff.2 hx.symm
    rcases H.invol_centralizer hxC (H.sq_of_isConj hc) (H.ne_one_of_isConj hc) with
        h | h | ⟨u, hu, rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨h, (h₁ x h).1 hc⟩)
    · exact Or.inr ⟨⟨u, hu, rfl⟩, (h₂ u hu).1 hc⟩
  · rintro ((rfl | ⟨hxI, hP⟩) | ⟨⟨u, hu, rfl⟩, hP⟩)
    · exact ⟨IsConj.refl _, rfl⟩
    · exact ⟨(h₁ x hxI).2 hP, (H.comm x hxI.1)⟩
    · refine ⟨(h₂ u hu).2 hP, ?_⟩
      calc H.t * (H.t * u) = H.t * (u * H.t) := by rw [H.comm u hu.1]
        _ = H.t * u * H.t := by rw [mul_assoc]

theorem t_not_mem_I : H.t ∉ H.I := fun h => H.t_not_mem h.1

theorem disjoint_I_tI : Disjoint H.I ((fun u => H.t * u) '' H.I) := by
  rw [Set.disjoint_left]
  rintro x hx ⟨u, hu, rfl⟩
  apply H.t_not_mem
  have : H.t = (H.t * u) * u⁻¹ := by group
  rw [this]
  exact H.L.mul_mem hx.1 (H.L.inv_mem hu.1)

theorem disjoint_t_tI : Disjoint ({H.t} : Set G) ((fun u => H.t * u) '' H.I) := by
  rw [Set.disjoint_left]
  rintro x rfl ⟨u, hu, h⟩
  apply hu.2.2
  have : u = 1 := mul_eq_left.1 h
  exact this

theorem ncard_F (P₁ P₂ : Prop) [Decidable P₁] [Decidable P₂]
    (h₁ : ∀ u ∈ H.I, IsConj H.t u ↔ P₁) (h₂ : ∀ u ∈ H.I, IsConj H.t (H.t * u) ↔ P₂) :
    H.F.ncard = 1 + (if P₁ then 165 else 0) + (if P₂ then 165 else 0) := by
  rw [H.F_eq P₁ P₂ h₁ h₂]
  have htI : ((fun u => H.t * u) '' H.I).ncard = 165 := by
    rw [Set.ncard_image_of_injective _ (mul_right_injective H.t), H.ncard_I]
  have e1 : {x | x ∈ H.I ∧ P₁} = if P₁ then H.I else ∅ := by
    split_ifs with h
    · ext x; simp [h]
    · ext x; simp [h]
  have e2 : {x | (∃ u ∈ H.I, x = H.t * u) ∧ P₂} =
      if P₂ then ((fun u => H.t * u) '' H.I) else ∅ := by
    split_ifs with h
    · ext x
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, -⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hu, rfl⟩, h⟩
    · ext x; simp [h]
  rw [e1, e2]
  have hd : Disjoint ({H.t} ∪ (if P₁ then H.I else ∅))
      (if P₂ then ((fun u => H.t * u) '' H.I) else ∅) := by
    split_ifs
    · exact Set.disjoint_union_left.2 ⟨H.disjoint_t_tI, H.disjoint_I_tI⟩
    · exact Set.disjoint_empty _
    · exact Set.disjoint_union_left.2 ⟨H.disjoint_t_tI, Set.empty_disjoint _⟩
    · exact Set.disjoint_empty _
  have hd' : Disjoint ({H.t} : Set G) (if P₁ then H.I else ∅) := by
    split_ifs
    · exact Set.disjoint_singleton_left.2 H.t_not_mem_I
    · exact Set.disjoint_empty _
  rw [Set.ncard_union_eq hd, Set.ncard_union_eq hd', Set.ncard_singleton]
  have hI := H.ncard_I
  split_ifs <;> (try simp only [Set.ncard_empty]) <;> omega

theorem card_A_mul : Nat.card {x : G // IsConj H.t x} * 15840 = Nat.card G := by
  have h := J1Std.card_eq_card_conjClass_mul (⊤ : Subgroup G) H.t
  rw [Subgroup.card_top, inf_top_eq, H.card_centralizer] at h
  rw [h]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  constructor
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    exact ⟨c, Subgroup.mem_top _, rfl⟩
  · rintro ⟨m, -, rfl⟩
    exact isConj_iff.2 ⟨m, rfl⟩

theorem F_subset_A : H.F ⊆ {x | IsConj H.t x} := fun _ hx => hx.1

theorem card_A_eq : Nat.card {x : G // IsConj H.t x} = ({x | IsConj H.t x} : Set G).ncard :=
  Nat.card_coe_set_eq _

theorem four_dvd_A_sub_F : 4 ∣ ({x | IsConj H.t x} : Set G).ncard - H.F.ncard := by
  have := H.simple
  have h := four_dvd_card_sub_card_inf_centralizer H.nonabelian H.t_sq
  have h1 : Nat.card {x : G // IsConj H.t x ∧ H.t * x = x * H.t} = H.F.ncard :=
    Nat.card_coe_set_eq H.F
  rw [h1, card_A_eq] at h
  exact h

theorem cases :
    (IsConj H.t (H.a ^ 4) ∧ IsConj H.t (H.t * H.a ^ 4) ∧
      Nat.card {x : G // IsConj H.t x} % 4 = 3) ∨
    (IsConj H.t (H.a ^ 4) ∧ ¬ IsConj H.t (H.t * H.a ^ 4) ∧
      Nat.card {x : G // IsConj H.t x} % 4 = 2) ∨
    (¬ IsConj H.t (H.a ^ 4) ∧ IsConj H.t (H.t * H.a ^ 4) ∧
      Nat.card {x : G // IsConj H.t x} % 4 = 2) := by
  classical
  have := H.simple
  have hz := H.z_mem_I
  have hs := H.four_dvd_A_sub_F
  have hle : H.F.ncard ≤ ({x | IsConj H.t x} : Set G).ncard := Set.ncard_le_ncard H.F_subset_A
  rw [← card_A_eq] at hs hle
  have h1 : ∀ u ∈ H.I, IsConj H.t u ↔ IsConj H.t (H.a ^ 4) := fun u hu =>
    ⟨fun h => H.isConj_of_I hu hz h, fun h => H.isConj_of_I hz hu h⟩
  have h2 : ∀ u ∈ H.I, IsConj H.t (H.t * u) ↔ IsConj H.t (H.t * H.a ^ 4) := fun u hu =>
    ⟨fun h => H.isConj_mul_of_I hu hz h, fun h => H.isConj_mul_of_I hz hu h⟩
  have hF := H.ncard_F _ _ h1 h2
  by_cases p1 : IsConj H.t (H.a ^ 4) <;> by_cases p2 : IsConj H.t (H.t * H.a ^ 4)
  · left
    refine ⟨p1, p2, ?_⟩
    simp only [p1, p2, ↓reduceIte] at hF
    omega
  · right; left
    refine ⟨p1, p2, ?_⟩
    simp only [p1, p2, ↓reduceIte] at hF
    omega
  · right; right
    refine ⟨p1, p2, ?_⟩
    simp only [p1, p2, ↓reduceIte] at hF
    omega
  · exfalso
    obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution (G := G) H.nonabelian
      (t := H.t) H.orderOf_t
    have hmem : g * H.t * g⁻¹ ∈ H.F :=
      ⟨isConj_iff.2 ⟨g, rfl⟩, hcomm.symm⟩
    rw [H.F_eq _ _ h1 h2] at hmem
    simp only [p1, p2, and_false, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      or_false] at hmem
    exact hne hmem

end Setting

end CFSG.EvenSporadicStandard.M11Std
