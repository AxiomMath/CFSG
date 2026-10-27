module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace BenderExt

open CFSG.Open Bender
open scoped commutatorElement

variable {Y : Type*} [Group Y]

namespace ExtCore

variable {K P T : Subgroup Y}

theorem exists_two_ne_one [Finite Y] {Z : Subgroup Y} (h : 3 ≤ Nat.card Z) :
    ∃ z₁ ∈ Z, ∃ z₂ ∈ Z, z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ≠ z₂ := by
  classical
  have hs : 1 < ((Z : Set Y) \ {1}).ncard := by
    rw [Set.ncard_sdiff (by simp [Z.one_mem]), Set.ncard_singleton, ← Nat.card_coe_set_eq]
    change 1 < Nat.card Z - 1
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hs
  exact ⟨a, ha.1, b, hb.1, ha.2, hb.2, hab⟩

theorem exists_three_ne_one [Finite Y] {Z : Subgroup Y} (h : 4 ≤ Nat.card Z) :
    ∃ z₁ ∈ Z, ∃ z₂ ∈ Z, ∃ z₃ ∈ Z, z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₃ ≠ 1 ∧ z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃ := by
  classical
  have hs : 2 < ((Z : Set Y) \ {1}).ncard := by
    rw [Set.ncard_sdiff (by simp [Z.one_mem]), Set.ncard_singleton, ← Nat.card_coe_set_eq]
    change 2 < Nat.card Z - 1
    omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).mp hs
  exact ⟨a, ha.1, b, hb.1, c, hc.1, ha.2, hb.2, hc.2, hab, hac, hbc⟩

theorem exists_orderOf_eq_two [Finite Y] {A P : Subgroup Y} (hP : IsPGroup 2 P) (hA : A ≤ P)
    (hA1 : A ≠ ⊥) : ∃ x ∈ A, orderOf x = 2 := by
  have hAp : IsPGroup 2 A := hP.to_le hA
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact hA1 (Subgroup.card_eq_one.mp hn)
  have hdvd : 2 ∣ Nat.card A := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨x, x.2, by rwa [Subgroup.orderOf_coe]⟩

theorem le_of_inf_le [Finite Y] [K.Normal] (hd : ExtData K P T) {A B : Subgroup Y}
    (hB : B ≤ P) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hcl : ∀ a ∈ (A : Set Y) ∪ B, ∀ y : Y, y⁻¹ * a * y ∈ P → y⁻¹ * a * y ∈ (A : Set Y) ∪ B)
    (hC : ∀ x ∈ (A : Set Y) ∪ B, x ∈ Subgroup.centralizer (K : Set Y) → x = 1)
    (hle : B ⊓ T ≤ A ⊓ T) (hZA : sylowCenter T ≤ A) : B ≤ A := by
  classical
  set C := Subgroup.centralizer (K : Set Y) with hCdef
  have hCcomm : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k := fun c hc k hk =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have hTK := hd.le_K
  have hTP := hd.le_P
  have hZT : sylowCenter T ≤ T := sylowCenter_le T
  have hZcomm : ∀ z ∈ sylowCenter T, ∀ t ∈ T, t * z = z * t := fun z hz =>
    (mem_sylowCenter.mp hz).2
  have hconjT : ∀ n ∈ Subgroup.normalizer (T : Set Y), ∀ t ∈ T, n⁻¹ * t * n ∈ T := by
    intro n hn t ht
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t).mp ht
    simpa using this
  have hconjtc : ∀ n ∈ K, ∀ t : Y, ∀ c ∈ C, n⁻¹ * (t * c) * n = (n⁻¹ * t * n) * c := by
    intro n hn t c hc
    have := hCcomm c hc n hn
    calc n⁻¹ * (t * c) * n = n⁻¹ * t * (c * n) := by group
      _ = n⁻¹ * t * (n * c) := by rw [this]
      _ = n⁻¹ * t * n * c := by group
  obtain ⟨z₁, hz₁, z₂, hz₂, hz₁1, hz₂1, hz₁₂⟩ :=
    exists_two_ne_one (Z := sylowCenter T) (by have := hd.card_center; omega)
  have h4a : ∀ y ∈ B, y ∈ T ⊔ C → y ∈ sylowCenter T := by
    intro y hy hyTC
    obtain ⟨t, ht, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hyTC
    have hcP : c ∈ P := hd.centralizer_le hc
    by_cases htZ : t ∈ sylowCenter T
    · by_cases hc1 : c = 1
      · rw [hc1, mul_one]
        exact htZ
      exfalso
      have ht1 : t ≠ 1 := by
        rintro rfl
        apply hc1
        have := hC _ (Or.inr hy) (by rw [one_mul]; exact hc)
        rwa [one_mul] at this
      have hzc : ∀ z ∈ sylowCenter T, z ≠ 1 → z * c ∈ B := by
        intro z hz hz1
        obtain ⟨n, hnK, hnN, hnz⟩ := hd.trans t htZ z hz ht1 hz1
        have hconj : n⁻¹ * (t * c) * n = z * c := by rw [hconjtc n hnK t c hc, hnz]
        have hmemP : n⁻¹ * (t * c) * n ∈ P := by
          rw [hconj]
          exact P.mul_mem (hTP (hZT hz)) hcP
        have h := hcl _ (Or.inr hy) n hmemP
        rw [hconj] at h
        rcases h with hA' | hB'
        · exfalso
          apply hc1
          apply hC c (Or.inl _) hc
          have := A.mul_mem (A.inv_mem (hZA hz)) hA'
          rwa [inv_mul_cancel_left] at this
        · exact hB'
      have e1 := hzc z₁ hz₁ hz₁1
      have e2 := hzc z₂ hz₂ hz₂1
      have hz3 : z₁ * z₂⁻¹ ∈ sylowCenter T :=
        (sylowCenter T).mul_mem hz₁ ((sylowCenter T).inv_mem hz₂)
      have hz31 : z₁ * z₂⁻¹ ≠ 1 := fun h => hz₁₂ (mul_inv_eq_one.mp h)
      have e3 := hzc _ hz3 hz31
      have hB3 : z₁ * z₂⁻¹ ∈ B := by
        have := B.mul_mem e1 (B.inv_mem e2)
        rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left] at this
      apply hc1
      apply hC c (Or.inr _) hc
      have := B.mul_mem (B.inv_mem hB3) e3
      rwa [inv_mul_cancel_left] at this
    · exfalso
      have htC : ∀ b ∈ A ⊓ T, b * t = t * b := by
        intro b hb
        have h := hAB b hb.1 (t * c) hy
        have hbc := hCcomm c hc b (hTK hb.2)
        have h2 : b * t * c = t * b * c := by
          calc b * t * c = b * (t * c) := by group
            _ = t * c * b := h
            _ = t * (b * c) := by rw [mul_assoc, hbc]
            _ = t * b * c := by group
        exact mul_right_cancel h2
      have hAT : ∀ s ∈ A ⊓ T, s ∈ sylowCenter T := by
        intro s hs
        by_contra hsZ
        obtain ⟨n, hnK, hnN, hpair⟩ := hd.cent s hs.2 hsZ
        have hsn : n⁻¹ * s * n ∈ A ⊓ T := by
          have hT' := hconjT n hnN s hs.2
          rcases hcl s (Or.inl hs.1) n (hTP hT') with h | h
          · exact ⟨h, hT'⟩
          · exact hle ⟨h, hT'⟩
        exact htZ (hpair t ht (htC s hs).symm (htC _ hsn).symm)
      have hBT : ∀ s ∈ B ⊓ T, s ∈ sylowCenter T := fun s hs => hAT s (hle hs)
      obtain ⟨n, hnK, hnN, hpair⟩ := hd.cent t ht htZ
      have htn : n⁻¹ * t * n ∈ T := hconjT n hnN t ht
      have hcomm : t * (n⁻¹ * t * n) = n⁻¹ * t * n * t := by
        have hmemP : n⁻¹ * (t * c) * n ∈ P := by
          rw [hconjtc n hnK t c hc]
          exact P.mul_mem (hTP htn) hcP
        rcases hcl _ (Or.inr hy) n hmemP with h | h
        · rw [hconjtc n hnK t c hc] at h
          have h1 := hAB _ h (t * c) hy
          have hc1 := hCcomm c hc t (hTK ht)
          have hc2 := hCcomm c hc _ (hTK htn)
          have h2 : n⁻¹ * t * n * t * (c * c) = t * (n⁻¹ * t * n) * (c * c) := by
            calc n⁻¹ * t * n * t * (c * c) = n⁻¹ * t * n * (t * c) * c := by group
              _ = n⁻¹ * t * n * (c * t) * c := by rw [hc1]
              _ = n⁻¹ * t * n * c * (t * c) := by group
              _ = t * c * (n⁻¹ * t * n * c) := h1
              _ = t * (c * (n⁻¹ * t * n)) * c := by group
              _ = t * (n⁻¹ * t * n * c) * c := by rw [hc2]
              _ = t * (n⁻¹ * t * n) * (c * c) := by group
          exact (mul_right_cancel h2).symm
        · rw [hconjtc n hnK t c hc] at h
          have h1 : n⁻¹ * t * n * t⁻¹ ∈ B := by
            have := B.mul_mem h (B.inv_mem hy)
            rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left] at this
          have hz : n⁻¹ * t * n * t⁻¹ ∈ sylowCenter T :=
            hBT _ ⟨h1, T.mul_mem htn (T.inv_mem ht)⟩
          have h2 := hZcomm _ hz t ht
          calc t * (n⁻¹ * t * n) = t * (n⁻¹ * t * n * t⁻¹) * t := by group
            _ = n⁻¹ * t * n * t⁻¹ * t * t := by rw [h2]
            _ = n⁻¹ * t * n * t := by group
      exact htZ (hpair t ht rfl hcomm)
  have h4b : ∀ y ∈ B, y ∈ T ⊔ C := by
    intro y hy
    by_contra hyTC
    have hyP : y ∈ P := hB hy
    have hyZ : ∀ z ∈ sylowCenter T, y * z = z * y := fun z hz => (hAB z (hZA hz) y hy).symm
    obtain ⟨hy2, hfix, ⟨t, ht, htZ⟩⟩ := hd.aut y hyP hyZ hyTC
    have hy2Z : y ^ 2 ∈ sylowCenter T := h4a _ (B.pow_mem hy 2) hy2
    apply htZ
    set s := y * t * y⁻¹ with hs
    have hsT : s ∈ T := hd.mem_T _ (P.mul_mem (P.mul_mem hyP (hTP ht)) (P.inv_mem hyP))
      ((inferInstance : K.Normal).conj_mem _ (hTK ht) y)
    have hw : s⁻¹ * y * s ∈ P := P.mul_mem (P.mul_mem (P.inv_mem (hTP hsT)) hyP) (hTP hsT)
    have hv : y⁻¹ * (s⁻¹ * y * s) = t⁻¹ * (y * t * y⁻¹) := by rw [hs]; group
    have hvT : t⁻¹ * (y * t * y⁻¹) ∈ T := T.mul_mem (T.inv_mem ht) hsT
    rcases hcl y (Or.inr hy) s hw with h | h
    ·
      have h1 := hAB _ h y hy
      apply hfix hy2Z _ hvT
      rw [← hv]
      calc y * (y⁻¹ * (s⁻¹ * y * s)) * y⁻¹ = y⁻¹ * (y * (s⁻¹ * y * s)) * y⁻¹ := by group
        _ = y⁻¹ * (s⁻¹ * y * s * y) * y⁻¹ := by rw [← h1]
        _ = y⁻¹ * (s⁻¹ * y * s) := by group
    ·
      rw [← hv]
      exact h4a _ (B.mul_mem (B.inv_mem hy) h) (Subgroup.mem_sup_left (hv ▸ hvT))
  intro y hy
  exact hZA (h4a y hy (h4b y hy))

end ExtCore

open ExtCore in
theorem nested_of_extData [Finite Y] {K P T : Subgroup Y} [K.Normal] (hd : ExtData K P T)
    (hP : IsPGroup 2 P) (A₁ A₂ : Subgroup Y) (h₁ : A₁ ≤ P) (h₂ : A₂ ≤ P) (hc : ⁅A₁, A₂⁆ = ⊥)
    (hcl : ∀ a ∈ (A₁ : Set Y) ∪ A₂, ∀ y : Y, y⁻¹ * a * y ∈ P →
      y⁻¹ * a * y ∈ (A₁ : Set Y) ∪ A₂)
    (hC : ∀ x ∈ (A₁ : Set Y) ∪ A₂, x ∈ Subgroup.centralizer (K : Set Y) → x = 1)
    (hinv : ∀ x ∈ (A₁ : Set Y) ∪ A₂, orderOf x = 2 →
      x ∈ K ⊔ Subgroup.centralizer (K : Set Y)) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  classical
  set C := Subgroup.centralizer (K : Set Y) with hCdef
  have hCcomm : ∀ c ∈ C, ∀ k ∈ K, k * c = c * k := fun c hc k hk =>
    Subgroup.mem_centralizer_iff.mp hc k hk
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hc, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  by_cases hA₁ : A₁ = ⊥
  · left
    rw [hA₁]
    exact bot_le
  by_cases hA₂ : A₂ = ⊥
  · right
    rw [hA₂]
    exact bot_le
  have hP' : ∀ x ∈ (A₁ : Set Y) ∪ A₂, x ∈ P := fun x hx => by
    rcases hx with hx | hx
    · exact h₁ hx
    · exact h₂ hx
  have hstep1 : ∀ x ∈ (A₁ : Set Y) ∪ A₂, orderOf x = 2 → x ∈ sylowCenter T := by
    intro x hx hx2
    obtain ⟨k, hk, c, hc', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hinv x hx hx2)
    have hkc : k * c = c * k := hCcomm c hc' k hk
    have hx1 : (k * c) ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one _
    have hk2c2 : k ^ 2 = (c ^ 2)⁻¹ := by
      have h : k ^ 2 * c ^ 2 = 1 := by
        rw [← hx1, sq, sq, sq]
        calc k * k * (c * c) = k * (k * c) * c := by group
          _ = k * (c * k) * c := by rw [hkc]
          _ = k * c * (k * c) := by group
      exact eq_inv_of_mul_eq_one_left h
    have hk2 : k ^ 2 = 1 := by
      have h : k ^ 2 ∈ K ⊓ C := ⟨K.pow_mem hk 2, by rw [hk2c2]; exact C.inv_mem (C.pow_mem hc' 2)⟩
      rw [hd.inf_centralizer, Subgroup.mem_bot] at h
      exact h
    have hc2 : c ^ 2 = 1 := by
      rw [hk2] at hk2c2
      exact inv_eq_one.mp hk2c2.symm
    have hcP : c ∈ P := hd.centralizer_le hc'
    have hkT : k ∈ T := by
      apply hd.mem_T _ _ hk
      have := P.mul_mem (hP' _ hx) (P.inv_mem hcP)
      rwa [mul_inv_cancel_right] at this
    have hkZ : k ∈ sylowCenter T := hd.omega_one k hkT hk2
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [one_mul] at hx hx2
      have := hC c hx hc'
      rw [this, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    by_contra hxZ
    have hc1 : c ≠ 1 := by
      rintro rfl
      rw [mul_one] at hxZ
      exact hxZ hkZ
    have hzc : ∀ z ∈ sylowCenter T, z ≠ 1 → z * c ∈ (A₁ : Set Y) ∪ A₂ := by
      intro z hz hz1
      obtain ⟨n, hnK, hnN, hnz⟩ := hd.trans k hkZ z hz hk1 hz1
      have hconj : n⁻¹ * (k * c) * n = z * c := by
        have := hCcomm c hc' n hnK
        rw [← hnz]
        calc n⁻¹ * (k * c) * n = n⁻¹ * k * (c * n) := by group
          _ = n⁻¹ * k * (n * c) := by rw [this]
          _ = n⁻¹ * k * n * c := by group
      have hmemP : n⁻¹ * (k * c) * n ∈ P := by
        rw [hconj]
        exact P.mul_mem (hd.le_P (sylowCenter_le T hz)) hcP
      have h := hcl _ hx n hmemP
      rwa [hconj] at h
    obtain ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, h1, h2, h3, h12, h13, h23⟩ :=
      exists_three_ne_one (Z := sylowCenter T) hd.card_center
    have hpair : ∀ (A : Subgroup Y), ∀ z ∈ sylowCenter T, ∀ z' ∈ sylowCenter T, z ≠ z' →
        z * c ∈ A → z' * c ∈ A → z * z'⁻¹ ∈ A ∧ z * z'⁻¹ ∈ sylowCenter T ∧ z * z'⁻¹ ≠ 1 := by
      intro A z hz z' hz' hne h h'
      refine ⟨?_, (sylowCenter T).mul_mem hz ((sylowCenter T).inv_mem hz'),
        fun h1 => hne (mul_inv_eq_one.mp h1)⟩
      have := A.mul_mem h (A.inv_mem h')
      rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left] at this
    have hforce : ∀ (A : Subgroup Y), (A = A₁ ∨ A = A₂) →
        (∀ w ∈ sylowCenter T, w ≠ 1 → w * c ∈ A) → False := by
      intro A hA hall
      obtain ⟨hm, hmZ, hm1⟩ := hpair A y₁ hy₁ y₂ hy₂ h12 (hall y₁ hy₁ h1) (hall y₂ hy₂ h2)
      apply hc1
      refine hC c ?_ hc'
      have := A.mul_mem (A.inv_mem hm) (hall _ hmZ hm1)
      rw [inv_mul_cancel_left] at this
      rcases hA with rfl | rfl
      · exact Or.inl this
      · exact Or.inr this
    have hcontra : ∀ m ∈ sylowCenter T, m ≠ 1 → m ∈ (A₁ : Set Y) ∪ A₂ → False := by
      intro m hm hm1 hmU
      have hZU : ((sylowCenter T : Subgroup Y) : Set Y) ⊆ (A₁ : Set Y) ∪ A₂ := by
        intro w hw
        by_cases hw1 : w = 1
        · rw [hw1]
          exact Or.inl A₁.one_mem
        obtain ⟨n, hnK, hnN, hnw⟩ := hd.trans m hm w hw hm1 hw1
        have := hcl m hmU n (by rw [hnw]; exact hd.le_P (sylowCenter_le T hw))
        rwa [hnw] at this
      rcases SubgroupClass.subset_union.mp hZU with hZ1 | hZ2
      · apply hforce A₂ (Or.inr rfl)
        intro w hw hw1
        rcases hzc w hw hw1 with h | h
        · exfalso
          apply hc1
          refine hC c (Or.inl ?_) hc'
          have := A₁.mul_mem (A₁.inv_mem (hZ1 hw)) h
          rwa [inv_mul_cancel_left] at this
        · exact h
      · apply hforce A₁ (Or.inl rfl)
        intro w hw hw1
        rcases hzc w hw hw1 with h | h
        · exact h
        · exfalso
          apply hc1
          refine hC c (Or.inr ?_) hc'
          have := A₂.mul_mem (A₂.inv_mem (hZ2 hw)) h
          rwa [inv_mul_cancel_left] at this
    have hside : ∀ (A : Subgroup Y), (A = A₁ ∨ A = A₂) → ∀ z ∈ sylowCenter T,
        ∀ z' ∈ sylowCenter T, z ≠ z' → z * c ∈ A → z' * c ∈ A → False := by
      intro A hA z hz z' hz' hne h h'
      obtain ⟨hm, hmZ, hm1⟩ := hpair A z hz z' hz' hne h h'
      apply hcontra _ hmZ hm1
      rcases hA with rfl | rfl
      · exact Or.inl hm
      · exact Or.inr hm
    rcases hzc y₁ hy₁ h1 with e1 | e1 <;> rcases hzc y₂ hy₂ h2 with e2 | e2 <;>
      rcases hzc y₃ hy₃ h3 with e3 | e3
    · exact hside A₁ (Or.inl rfl) _ hy₁ _ hy₂ h12 e1 e2
    · exact hside A₁ (Or.inl rfl) _ hy₁ _ hy₂ h12 e1 e2
    · exact hside A₁ (Or.inl rfl) _ hy₁ _ hy₃ h13 e1 e3
    · exact hside A₂ (Or.inr rfl) _ hy₂ _ hy₃ h23 e2 e3
    · exact hside A₁ (Or.inl rfl) _ hy₂ _ hy₃ h23 e2 e3
    · exact hside A₂ (Or.inr rfl) _ hy₁ _ hy₃ h13 e1 e3
    · exact hside A₂ (Or.inr rfl) _ hy₁ _ hy₂ h12 e1 e2
    · exact hside A₂ (Or.inr rfl) _ hy₁ _ hy₂ h12 e1 e2
  obtain ⟨x, hxA, hx2⟩ := exists_orderOf_eq_two hP h₁ hA₁
  have hxZ := hstep1 x (Or.inl hxA) hx2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hZU : ∀ z ∈ sylowCenter T, z ∈ (A₁ : Set Y) ∪ A₂ := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Or.inl A₁.one_mem
    obtain ⟨n, hnK, hnN, hnz⟩ := hd.trans x hxZ z hz hx1 hz1
    have h := hcl x (Or.inl hxA) n (by rw [hnz]; exact hd.le_P (sylowCenter_le T hz))
    rwa [hnz] at h
  have hnestB := hd.nest (A₁ ⊓ T) (A₂ ⊓ T) inf_le_right inf_le_right
    (by
      rw [eq_bot_iff, ← hc]
      exact Subgroup.commutator_mono inf_le_left inf_le_left)
    (by
      intro b hb k hk hbk
      have hbU : b ∈ (A₁ : Set Y) ∪ A₂ := by
        rcases hb with hb | hb
        · exact Or.inl hb.1
        · exact Or.inr hb.1
      rcases hcl b hbU k (hd.le_P hbk) with h | h
      · exact Or.inl ⟨h, hbk⟩
      · exact Or.inr ⟨h, hbk⟩)
  have hcl' : ∀ a ∈ (A₂ : Set Y) ∪ A₁, ∀ y : Y, y⁻¹ * a * y ∈ P →
      y⁻¹ * a * y ∈ (A₂ : Set Y) ∪ A₁ := by
    intro a ha y hy
    rw [Set.union_comm] at ha ⊢
    exact hcl a ha y hy
  have hC' : ∀ x ∈ (A₂ : Set Y) ∪ A₁, x ∈ C → x = 1 := by
    intro x hx
    rw [Set.union_comm] at hx
    exact hC x hx
  rcases hnestB with h | h
  ·
    left
    have hZA₂ : sylowCenter T ≤ A₂ := fun z hz => by
      rcases hZU z hz with h1 | h2
      · exact (h ⟨h1, sylowCenter_le T hz⟩).1
      · exact h2
    exact le_of_inf_le hd h₁ (fun a ha b hb => (hcomm b hb a ha).symm) hcl' hC' h hZA₂
  ·
    right
    have hZA₁ : sylowCenter T ≤ A₁ := fun z hz => by
      rcases hZU z hz with h1 | h2
      · exact h1
      · exact (h ⟨h2, sylowCenter_le T hz⟩).1
    exact le_of_inf_le hd h₂ hcomm hcl hC h hZA₁

end BenderExt

theorem bender_extension_strongly_closed_union_nested {Y : Type} [Group Y] [Finite Y]
    (K : Subgroup Y) [K.Normal] (hK : CFSG.Open.fusionIsBenderGroup K)
    (P : Sylow 2 Y) (hKP : K ⊔ (P : Subgroup Y) = ⊤)
    (A₁ A₂ : Subgroup Y) (h₁ : A₁ ≤ (P : Subgroup Y)) (h₂ : A₂ ≤ (P : Subgroup Y))
    (hc : ⁅A₁, A₂⁆ = ⊥)
    (hcl : ∀ a ∈ (A₁ : Set Y) ∪ A₂, ∀ y : Y, y⁻¹ * a * y ∈ (P : Subgroup Y) →
      y⁻¹ * a * y ∈ (A₁ : Set Y) ∪ A₂)
    (hC : ∀ x ∈ (A₁ : Set Y) ∪ A₂, x ∈ Subgroup.centralizer (K : Set Y) → x = 1)
    (hinv : ∀ x ∈ (A₁ : Set Y) ∪ A₂, orderOf x = 2 →
      x ∈ K ⊔ Subgroup.centralizer (K : Set Y)) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ :=
  BenderExt.nested_of_extData
    (BenderExt.extData_of_benderData K (BenderExt.benderData_of_isBenderGroup hK) P hKP)
    P.isPGroup' A₁ A₂ h₁ h₂ hc hcl hC hinv

end CFSG.ComponentClassification.AschbacherToolkit
