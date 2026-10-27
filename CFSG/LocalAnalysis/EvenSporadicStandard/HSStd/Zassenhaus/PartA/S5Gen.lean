module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

namespace S5

section Odd

variable {X : Type*} [Group X]

theorem odd_fusionOddCore [Finite X] : Odd (Nat.card (Open.fusionOddCore X)) := by
  have h : Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem exists_conj_cent_of_odd [Finite X] (O : Subgroup X) [O.Normal] (hO : Odd (Nat.card O))
    {c a b : X} (ha : a * a = 1) (hb : b * b = 1) (hac : a * c = c * a) (hbc : b * c = c * b)
    (h : a⁻¹ * b ∈ O) : ∃ o ∈ O, o * c = c * o ∧ o * a * o⁻¹ = b := by
  set K : Subgroup X := centralizer ({c} : Set X) with hK
  have haK : a ∈ K := mem_centralizer_singleton_iff.2 hac
  have hbK : b ∈ K := mem_centralizer_singleton_iff.2 hbc
  have hdvd : Nat.card (O.subgroupOf K) ∣ Nat.card O := by
    have h1 : Nat.card ((O.subgroupOf K).map K.subtype) = Nat.card (O.subgroupOf K) :=
      Subgroup.card_map_of_injective K.subtype_injective
    rw [← h1]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.1 hx
  have hO' : Odd (Nat.card (O.subgroupOf K)) := Odd.of_dvd_nat hO hdvd
  obtain ⟨o, ho, hoc⟩ := exists_conj_of_mul_mem_odd (O.subgroupOf K) hO'
    (a := (⟨a, haK⟩ : K)) (b := (⟨b, hbK⟩ : K)) (Subtype.ext ha) (Subtype.ext hb)
    (by rw [mem_subgroupOf]; simpa using h)
  refine ⟨(o : X), mem_subgroupOf.1 ho, ?_, ?_⟩
  · have := mem_centralizer_singleton_iff.1 o.2
    exact this
  · simpa using congrArg Subtype.val hoc

end Odd

section Four

variable {G : Type*} [Group G]

theorem mem_V_iff {t u : G} (ht : t * t = 1) (hu : u * u = 1) (htu : t * u = u * t) {y : G} :
    y ∈ zpowers t ⊔ zpowers u ↔ y = 1 ∨ y = t ∨ y = u ∨ y = t * u := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hut : u * t = t * u := htu.symm
  have e1 : t * (t * u) = u := by rw [← mul_assoc, ht, one_mul]
  have e2 : u * (t * u) = t := by rw [← mul_assoc, hut, mul_assoc, hu, mul_one]
  have e3 : t * u * t = u := by rw [mul_assoc, hut, ← mul_assoc, ht, one_mul]
  have e4 : t * u * u = t := by rw [mul_assoc, hu, mul_one]
  have e5 : t * u * (t * u) = 1 := by rw [← mul_assoc, e3, hu]
  constructor
  · intro hy
    let M : Subgroup G :=
      { carrier := {y | y = 1 ∨ y = t ∨ y = u ∨ y = t * u}
        one_mem' := Or.inl rfl
        mul_mem' := by
          rintro x y (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;>
            simp [ht, hu, hut, e1, e2, e3, e4, e5]
        inv_mem' := by
          rintro x (rfl | rfl | rfl | rfl)
          · simp
          · simp [hti]
          · simp [hui]
          · simp [mul_inv_rev, hti, hui, hut] }
    have hle : zpowers t ⊔ zpowers u ≤ M :=
      sup_le ((zpowers_le).2 (Or.inr (Or.inl rfl))) ((zpowers_le).2 (Or.inr (Or.inr (Or.inl rfl))))
    exact hle hy
  · rintro (h | h | h | h) <;> subst h
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))

theorem card_V {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hne : a ≠ b) : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) = 4 := by
  have hset : ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) = {1, a, b, a * b} := by
    ext y
    rw [SetLike.mem_coe, mem_V_iff ha hb hab]
    simp
  have hne1 : (1 : G) ≠ a * b := by
    intro h
    apply hne
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this, inv_eq_of_mul_eq_one_right ha]
  have hne2 : a ≠ a * b := by
    intro h
    apply hb1
    exact (mul_eq_left.1 h.symm)
  have hne3 : b ≠ a * b := by
    intro h
    apply ha1
    exact (mul_eq_right.1 h.symm)
  have hcard : Nat.card (zpowers a ⊔ zpowers b : Subgroup G) =
      Set.ncard ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) := Nat.card_coe_set_eq _
  rw [hcard, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simpa using hne3
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hne2⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha1.symm, hb1.symm, hne1⟩

end Four

section Algebra

variable {G : Type*} [Group G]

theorem sq_cases {t b h : G} (hbb : b * b = 1) (hb1 : b ≠ 1)
    (hhb : h * b = b * h) (hht : h * t * h⁻¹ = t * b)
    (hmem : h * h = 1 ∨ h * h = t ∨ h * h = b ∨ h * h = t * b) : h * h = 1 ∨ h * h = b := by
  have h1 : h * t = t * b * h := by
    rw [mul_inv_eq_iff_eq_mul] at hht
    exact hht
  have hc : h * (h * h) = (h * h) * h := by rw [mul_assoc]
  rcases hmem with h0 | h0 | h0 | h0
  · exact Or.inl h0
  · exfalso
    rw [h0] at hc
    have h2 : t * h = t * (b * h) := by
      calc t * h = h * t := hc.symm
        _ = t * b * h := h1
        _ = t * (b * h) := mul_assoc _ _ _
    exact hb1 (mul_eq_right.1 (mul_left_cancel h2).symm)
  · exact Or.inr h0
  · exfalso
    rw [h0] at hc
    have h2 : t * h = t * b * h := by
      calc t * h = t * (b * b) * h := by rw [hbb, mul_one]
        _ = (t * b) * (b * h) := by simp only [mul_assoc]
        _ = (t * b) * (h * b) := by rw [hhb]
        _ = (t * b * h) * b := by simp only [mul_assoc]
        _ = (h * t) * b := by rw [← h1]
        _ = h * (t * b) := mul_assoc _ _ _
        _ = t * b * h := hc
    have h3 : h = b * h := by
      have : t * h = t * (b * h) := by rw [h2, mul_assoc]
      exact mul_left_cancel this
    exact hb1 (mul_eq_right.1 h3.symm)

theorem u₁_algebra {t b h : G} (htt : t * t = 1) (hbb : b * b = 1)
    (hbt : b * t = t * b) (hhb : h * b = b * h) (hht : h * t * h⁻¹ = t * b)
    (hsq : h * h = 1 ∨ h * h = b) :
    ∃ u₁ : G, (u₁ = h ∨ u₁ = h * t) ∧ u₁ * u₁ = 1 ∧ u₁ * b = b * u₁ ∧
      t * u₁ * t⁻¹ = b * u₁ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : h * t = t * b * h := by
    rw [mul_inv_eq_iff_eq_mul] at hht
    exact hht
  have ID : t * h = b * h * t := by
    symm
    calc b * h * t = h * b * t := by rw [hhb]
      _ = h * (b * t) := mul_assoc _ _ _
      _ = h * (t * b) := by rw [hbt]
      _ = (h * t) * b := (mul_assoc _ _ _).symm
      _ = (t * b * h) * b := by rw [h1]
      _ = t * b * (h * b) := mul_assoc _ _ _
      _ = t * b * (b * h) := by rw [hhb]
      _ = t * (b * b) * h := by simp only [mul_assoc]
      _ = t * h := by rw [hbb, mul_one]
  rcases hsq with h0 | h0
  · refine ⟨h, Or.inl rfl, h0, hhb, ?_⟩
    rw [hti]
    calc t * h * t = b * h * t * t := by rw [ID]
      _ = b * h := by rw [mul_assoc, htt, mul_one]
  · refine ⟨h * t, Or.inr rfl, ?_, ?_, ?_⟩
    · calc h * t * (h * t) = (t * b * h) * (h * t) := by rw [h1]
        _ = t * b * (h * h) * t := by simp only [mul_assoc]
        _ = t * b * b * t := by rw [h0]
        _ = t * (b * b) * t := by simp only [mul_assoc]
        _ = 1 := by rw [hbb, mul_one, htt]
    · calc h * t * b = h * (t * b) := mul_assoc _ _ _
        _ = h * (b * t) := by rw [hbt]
        _ = (h * b) * t := (mul_assoc _ _ _).symm
        _ = b * h * t := by rw [hhb]
        _ = b * (h * t) := mul_assoc _ _ _
    · rw [hti]
      calc t * (h * t) * t = t * h * (t * t) := by simp only [mul_assoc]
        _ = t * h := by rw [htt, mul_one]
        _ = b * h * t := ID
        _ = b * (h * t) := mul_assoc _ _ _

end Algebra

section Sup

variable {X : Type*} [Group X]

theorem exists_zpow_mul_of_mem_sup' {A : Subgroup X} {t : X} (h : ∀ a ∈ A, a * t = t * a) {g : X}
    (hg : g ∈ zpowers t ⊔ A) : ∃ n : ℤ, ∃ a ∈ A, g = t ^ n * a := by
  have hc : ∀ (n : ℤ) (a : X), a ∈ A → a * t ^ n = t ^ n * a := fun n a ha =>
    ((show Commute a t from h a ha).zpow_right n)
  let S : Subgroup X :=
    { carrier := {g | ∃ n : ℤ, ∃ a ∈ A, g = t ^ n * a}
      mul_mem' := by
        rintro _ _ ⟨n, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
        refine ⟨n + m, a * b, A.mul_mem ha hb, ?_⟩
        calc t ^ n * a * (t ^ m * b) = t ^ n * (a * t ^ m) * b := by simp only [mul_assoc]
          _ = t ^ n * (t ^ m * a) * b := by rw [hc m a ha]
          _ = t ^ (n + m) * (a * b) := by rw [zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 1, A.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, a, ha, rfl⟩
        refine ⟨-n, a⁻¹, A.inv_mem ha, ?_⟩
        have := hc (-n) a ha
        calc (t ^ n * a)⁻¹ = a⁻¹ * (t ^ n)⁻¹ := mul_inv_rev _ _
          _ = a⁻¹ * t ^ (-n) := by rw [zpow_neg]
          _ = t ^ (-n) * a⁻¹ := by
            exact (show Commute a (t ^ (-n)) from this).inv_left }
  have hle : zpowers t ⊔ A ≤ S := by
    refine sup_le ?_ (fun a ha => ⟨0, a, ha, by simp⟩)
    rintro _ ⟨n, rfl⟩
    exact ⟨n, 1, A.one_mem, by simp⟩
  exact hle hg

end Sup

end S5

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
