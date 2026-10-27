module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1PtsA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Prod
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t d : G}

private lemma y7a_z_comm_A (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    ∀ a ∈ A, a * z = z * a := by
  intro a ha
  exact y6q8_z_central h.cfg.rel a (by rwa [h.cfg.hA] at ha)

private lemma y7a_z_inv (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (y7a_z_sq h)

private lemma y7a_t_mem_normalizer_V (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    t ∈ normalizer (V : Set G) :=
  y7a_C1_le_N_V h (Subgroup.mem_sup_right (y7a_t_mem_C0 h))

private lemma y7a_sq_mul_z (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha2 : a ^ 2 = z) (hb2 : b ^ 2 = z) (hab : ⁅a, b⁆ = z) :
    (a * b) ^ 2 = z := by
  have ha' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at ha
  have hb' : b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.cfg.hA] at hb
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 * ⁅b, a⁆ := y6q8_sq_mul h.cfg.rel a ha' b hb'
    _ = ⁅b, a⁆ := by rw [ha2, hb2, ← pow_two, h.cfg.rel.z_sq, one_mul]
    _ = z := by rw [← commutatorElement_inv, hab, y7a_z_inv h]

private lemma y7a_card_coset [Finite G] (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) {c : G} {n : ℕ}
    (hcount : Nat.card ↥{a : G | a ∈ A ∧ a ^ 2 = c} = n) :
    Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = c ∧ ∃ v ∈ V, x = a * t * v} * 2 =
      n * Nat.card ↥V := by
  classical
  let S : Set G := {a : G | a ∈ A ∧ a ^ 2 = c}
  let SV : Set G := {x : G | ∃ s ∈ S, ∃ v ∈ V, x = s * v}
  have hSA : S ⊆ A := fun s hs => hs.1
  have hSZ : ∀ s ∈ S, ∀ w ∈ A ⊓ V, s * w ∈ S := by
    intro s hs w hw
    obtain ⟨hsA, hs2⟩ := hs
    have hw2 : w = 1 ∨ w = z := by
      have hwz : w ∈ zpowers z := by
        rw [← y7a_A_inf_V h]
        exact hw
      classical
      rw [mem_zpowers_iff_mem_range_orderOf] at hwz
      simp only [Finset.mem_image, Finset.mem_range] at hwz
      obtain ⟨i, hi, hiv⟩ := hwz
      have hz2 : orderOf z = 2 :=
        orderOf_eq_prime (by rw [pow_two]; exact y7a_z_sq h) h.cfg.z_ne
      have hi2 : i < 2 := by rwa [hz2] at hi
      interval_cases i
      · left; simpa using hiv.symm
      · right; simpa using hiv.symm
    rcases hw2 with hw1 | hwz
    · rw [hw1, mul_one]
      exact ⟨hsA, hs2⟩
    · rw [hwz]
      refine ⟨mul_mem hsA (y7a_z_mem_A h), ?_⟩
      have hcomm : Commute s z := y7a_z_comm_A h s hsA
      calc (s * z) ^ 2 = s ^ 2 * z ^ 2 := hcomm.mul_pow 2
        _ = c := by rw [hs2, pow_two, y7a_z_sq h, mul_one]
  have hprod := y6_card_prodSet (A := A) (V := V) (S := S) hSA hSZ
  have hcardinf : Nat.card ↥(A ⊓ V) = 2 := by
    rw [y7a_A_inf_V h, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact y7a_z_sq h) h.cfg.z_ne
  have hcard : Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = c ∧ ∃ v ∈ V, x = a * t * v} =
      Nat.card ↥SV := by
    have hset : {x : G | ∃ a ∈ A, a ^ 2 = c ∧ ∃ v ∈ V, x = a * t * v} =
        (fun y => y * t) '' SV := by
      ext x
      constructor
      · rintro ⟨a, haA, ha2, v, hvV, rfl⟩
        refine ⟨a * (t * v * t⁻¹), ⟨a, ⟨haA, ha2⟩, t * v * t⁻¹, ?_, rfl⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (y7a_t_mem_normalizer_V h) v).mp hvV
        · group
      · rintro ⟨y, ⟨s, ⟨hsA, hs2⟩, v, hvV, rfl⟩, rfl⟩
        refine ⟨s, hsA, hs2, t⁻¹ * v * t, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff''.mp (y7a_t_mem_normalizer_V h) v).mp hvV
        · group
    rw [hset, Nat.card_image_of_injective (mul_left_injective t) SV]
  have hS : Nat.card ↥S = n := hcount
  rw [hcardinf, hS] at hprod
  rw [hcard]
  exact hprod.symm

theorem y7a_card_Up [Finite G] (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    Nat.card ↥(y6Up A V t) = 10 * Nat.card ↥V := by
  classical
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.cfg.hA]; exact h.cfg.card_A
  have hcount : Nat.card ↥{a : G | a ∈ A ∧ a ^ 2 = 1} = 20 := by
    simpa [h.cfg.hA] using (y6q8_card h.cfg.rel h.cfg.z_ne hA32).2
  have key := y7a_card_coset (c := 1) h hcount
  change Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = 1 ∧ ∃ v ∈ V, x = a * t * v} =
    10 * Nat.card ↥V
  omega

theorem y7a_card_Um [Finite G] (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    Nat.card ↥(y6Um A V z t) = 6 * Nat.card ↥V := by
  classical
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.cfg.hA]; exact h.cfg.card_A
  have hcount : Nat.card ↥{a : G | a ∈ A ∧ a ^ 2 = z} = 12 := by
    simpa [h.cfg.hA] using (y6q8_card h.cfg.rel h.cfg.z_ne hA32).1
  have key := y7a_card_coset h hcount
  change Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = z ∧ ∃ v ∈ V, x = a * t * v} =
    6 * Nat.card ↥V
  omega

theorem y7a_gen_Um (h : Y7ACfg A C0 V a₁ b₁ a₂ b₂ z t d) :
    closure ((y6Um A V z t : Set G) ∪ (V : Set G)) = A ⊔ C0 := by
  classical
  let K : Subgroup G := closure ((y6Um A V z t : Set G) ∪ (V : Set G))
  have hle : K ≤ A ⊔ C0 := by
    apply (Subgroup.closure_le (A ⊔ C0)).mpr
    intro x hx
    rcases hx with hx | hx
    · exact (y7a_Um_sub h x hx).1
    · exact (le_sup_right : C0 ≤ A ⊔ C0) (y7a_V_le_C0 h hx)
  have ha1 : a₁ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb1 : b₁ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have ha2 : a₂ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb2 : b₂ ∈ A := by rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hmemUm : ∀ a ∈ A, a ^ 2 = z → a * t ∈ K := by
    intro a ha ha2
    exact Subgroup.subset_closure (Or.inl ⟨a, ha, ha2, 1, one_mem V, by rw [mul_one]⟩)
  have ha1t : a₁ * t ∈ K := hmemUm a₁ ha1 h.cfg.rel.a1_sq
  have hb1t : b₁ * t ∈ K := hmemUm b₁ hb1 h.cfg.rel.b1_sq
  have ha2t : a₂ * t ∈ K := hmemUm a₂ ha2 h.cfg.rel.a2_sq
  have hb2t : b₂ * t ∈ K := hmemUm b₂ hb2 h.cfg.rel.b2_sq
  have ha1b1t : (a₁ * b₁) * t ∈ K :=
    hmemUm (a₁ * b₁) (mul_mem ha1 hb1)
      (y7a_sq_mul_z h ha1 hb1 h.cfg.rel.a1_sq h.cfg.rel.b1_sq h.cfg.rel.comm1)
  have ha2b2t : (a₂ * b₂) * t ∈ K :=
    hmemUm (a₂ * b₂) (mul_mem ha2 hb2)
      (y7a_sq_mul_z h ha2 hb2 h.cfg.rel.a2_sq h.cfg.rel.b2_sq h.cfg.rel.comm2)
  have ha1K : a₁ ∈ K := by
    have hmem : (b₁ * t) * ((a₁ * b₁) * t)⁻¹ ∈ K := mul_mem hb1t (inv_mem ha1b1t)
    have heq : (b₁ * t) * ((a₁ * b₁) * t)⁻¹ = a₁⁻¹ := by group
    rw [heq] at hmem
    simpa using inv_mem hmem
  have hb1K : b₁ ∈ K := by
    have hmem : (a₁ * t) * (b₁ * t)⁻¹ ∈ K := mul_mem ha1t (inv_mem hb1t)
    have heq : (a₁ * t) * (b₁ * t)⁻¹ = a₁ * b₁⁻¹ := by group
    rw [heq] at hmem
    have hmem2 : a₁⁻¹ * (a₁ * b₁⁻¹) ∈ K := mul_mem (inv_mem ha1K) hmem
    have heq2 : a₁⁻¹ * (a₁ * b₁⁻¹) = b₁⁻¹ := by group
    rw [heq2] at hmem2
    simpa using inv_mem hmem2
  have ha2K : a₂ ∈ K := by
    have hmem : (b₂ * t) * ((a₂ * b₂) * t)⁻¹ ∈ K := mul_mem hb2t (inv_mem ha2b2t)
    have heq : (b₂ * t) * ((a₂ * b₂) * t)⁻¹ = a₂⁻¹ := by group
    rw [heq] at hmem
    simpa using inv_mem hmem
  have hb2K : b₂ ∈ K := by
    have hmem : (a₂ * t) * (b₂ * t)⁻¹ ∈ K := mul_mem ha2t (inv_mem hb2t)
    have heq : (a₂ * t) * (b₂ * t)⁻¹ = a₂ * b₂⁻¹ := by group
    rw [heq] at hmem
    have hmem2 : a₂⁻¹ * (a₂ * b₂⁻¹) ∈ K := mul_mem (inv_mem ha2K) hmem
    have heq2 : a₂⁻¹ * (a₂ * b₂⁻¹) = b₂⁻¹ := by group
    rw [heq2] at hmem2
    simpa using inv_mem hmem2
  have hAK : A ≤ K := by
    rw [h.cfg.hA]
    apply (Subgroup.closure_le K).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [ha1K, hb1K, ha2K, hb2K]
  have htK : t ∈ K := by
    have hmem : a₁⁻¹ * (a₁ * t) ∈ K := mul_mem (inv_mem ha1K) ha1t
    have heq : a₁⁻¹ * (a₁ * t) = t := by group
    rwa [heq] at hmem
  have hC0K : C0 ≤ K := by
    rw [h.cfg.hC0]
    apply (Subgroup.closure_le K).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mul_mem (Subgroup.subset_closure (Or.inr (y7a_d_mem_V h))) htK
    · exact htK
  exact le_antisymm hle (sup_le hAK hC0K)

end CFSG.OddStandard.HigherRank.YamadaG23
