module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6PtsA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Prod
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8c

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma y6_t_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : t * t = 1 := by
  rw [← pow_two, ← h.t_ord]
  exact pow_orderOf_eq_one t

private lemma y6_t_conj_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ v ∈ V, t * v * t⁻¹ = v⁻¹ := by
  intro v hv
  rw [h.hV] at hv
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← hk, ← conj_zpow, h.t_inv, inv_zpow]

private lemma y6_t_mul_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ v ∈ V, t * v = v⁻¹ * t := by
  intro v hv
  calc t * v = (t * v * t⁻¹) * t := by group
    _ = v⁻¹ * t := by rw [y6_t_conj_V h v hv]

private lemma y6_mul_t_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ v ∈ V, v * t = t * v⁻¹ := by
  intro v hv
  simpa using (y6_t_mul_V h v⁻¹ (inv_mem hv)).symm

private lemma y6_A_comm_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ a ∈ A, ∀ v ∈ V, a * v = v * a := by
  intro a ha v hv
  exact y6_C0_comm h a ha v (y6_V_le_C0 h hv)

private lemma y6_z_comm_A (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ a ∈ A, a * z = z * a := by
  intro a ha
  exact y6q8_z_central h.rel a (by rwa [h.hA] at ha)

private lemma y6_z_inv (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : z⁻¹ = z :=
  inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h.rel.z_sq)

private lemma y6_V_elems (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    ∀ v ∈ V, v = 1 ∨ v = u ∨ v = z ∨ v = u ^ 3 := by
  classical
  intro v hv
  rw [h.hV, mem_zpowers_iff_mem_range_orderOf] at hv
  simp only [Finset.mem_image, Finset.mem_range] at hv
  obtain ⟨i, hi, hiv⟩ := hv
  have hi4 : i < 4 := by rwa [h.u_ord] at hi
  rw [← hiv]
  interval_cases i
  · left; simp
  · right; left; simp
  · right; right; left; simpa using h.u_sq
  · right; right; right; rfl

private lemma y6_u3 (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : u ^ 3 = z * u := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h.u_sq, pow_one]

private lemma y6_u3_sq (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) : (u ^ 3) ^ 2 = z := by
  have hu4 : u ^ 4 = 1 := by rw [← h.u_ord]; exact pow_orderOf_eq_one u
  rw [← pow_mul, show 3 * 2 = 4 + 2 by norm_num, pow_add, hu4, one_mul, h.u_sq]

private lemma y6_card_A_inf_V (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    Nat.card ↥(A ⊓ V) = 2 := by
  rw [y6_A_inf_V h, Nat.card_zpowers, orderOf_eq_prime h.rel.z_sq h.z_ne]

private lemma y6_sq_mul_z (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha2 : a ^ 2 = z) (hb2 : b ^ 2 = z) (hab : ⁅a, b⁆ = z) :
    (a * b) ^ 2 = z := by
  have ha' : a ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.hA] at ha
  have hb' : b ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := by rwa [h.hA] at hb
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 * ⁅b, a⁆ := y6q8_sq_mul h.rel a ha' b hb'
    _ = ⁅b, a⁆ := by rw [ha2, hb2, ← pow_two, h.rel.z_sq, one_mul]
    _ = z := by rw [← commutatorElement_inv, hab, y6_z_inv h]

private lemma y6_sq_eq_z_of_mul (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {a v : G}
    (ha : a ∈ A) (hv : v ∈ V) (hv2 : v ^ 2 = z) (h1 : (a * v) ^ 2 = 1) : a ^ 2 = z := by
  have hcomm : Commute a v := y6_A_comm_V h a ha v hv
  have hsq : (a * v) ^ 2 = a ^ 2 * v ^ 2 := hcomm.mul_pow 2
  have hprod : a ^ 2 * z = 1 := by rw [← hv2]; exact hsq.symm.trans h1
  have h1' : a ^ 2 = z⁻¹ := mul_eq_one_iff_eq_inv.mp hprod
  rwa [y6_z_inv h] at h1'

private lemma y6_card_coset (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) {c : G} {n : ℕ}
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
    have hwA : w ∈ A := hw.1
    have hw2 : w = 1 ∨ w = z := by
      have hwz : w ∈ zpowers z := by
        rw [← y6_A_inf_V h]
        exact hw
      classical
      rw [mem_zpowers_iff_mem_range_orderOf] at hwz
      simp only [Finset.mem_image, Finset.mem_range] at hwz
      obtain ⟨i, hi, hiv⟩ := hwz
      have hz2 : orderOf z = 2 := orderOf_eq_prime h.rel.z_sq h.z_ne
      have hi2 : i < 2 := by rwa [hz2] at hi
      interval_cases i
      · left; simpa using hiv.symm
      · right; simpa using hiv.symm
    rcases hw2 with hw1 | hwz
    · rw [hw1, mul_one]
      exact ⟨hsA, hs2⟩
    · rw [hwz]
      refine ⟨mul_mem hsA (y6_z_mem_A h), ?_⟩
      have hcomm : Commute s z := y6_z_comm_A h s hsA
      calc (s * z) ^ 2 = s ^ 2 * z ^ 2 := hcomm.mul_pow 2
        _ = c := by rw [hs2, h.rel.z_sq, mul_one]
  have hprod := y6_card_prodSet (A := A) (V := V) (S := S) hSA hSZ
  have hcardinf : Nat.card ↥(A ⊓ V) = 2 := y6_card_A_inf_V h
  have hcard : Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = c ∧ ∃ v ∈ V, x = a * t * v} =
      Nat.card ↥SV := by
    have hset : {x : G | ∃ a ∈ A, a ^ 2 = c ∧ ∃ v ∈ V, x = a * t * v} =
        (fun y => y * t) '' SV := by
      ext x
      constructor
      · rintro ⟨a, haA, ha2, v, hvV, rfl⟩
        exact ⟨a * v⁻¹, ⟨a, ⟨haA, ha2⟩, v⁻¹, inv_mem hvV, rfl⟩,
          (calc a * t * v = a * (t * v) := mul_assoc a t v
            _ = a * (v⁻¹ * t) := by rw [y6_t_mul_V h v hvV]
            _ = (a * v⁻¹) * t := (mul_assoc a v⁻¹ t).symm).symm⟩
      · rintro ⟨y, ⟨s, ⟨hsA, hs2⟩, v, hvV, rfl⟩, rfl⟩
        exact ⟨s, hsA, hs2, v⁻¹, inv_mem hvV,
          (calc (s * v) * t = s * (v * t) := mul_assoc s v t
            _ = s * (t * v⁻¹) := by rw [y6_mul_t_V h v hvV]
            _ = s * t * v⁻¹ := (mul_assoc s t v⁻¹).symm)⟩
    rw [hset, Nat.card_image_of_injective (mul_left_injective t) SV]
  have hS : Nat.card ↥S = n := hcount
  have hprod' : Nat.card ↥SV * 2 = n * Nat.card ↥V := by
    rw [hcardinf, hS] at hprod
    exact hprod.symm
  rw [hcard]
  exact hprod'

theorem y6_card_Um (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    Nat.card ↥(y6Um A V z t) = 6 * Nat.card ↥V := by
  classical
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.hA]; exact h.card_A
  have hcount : Nat.card ↥{a : G | a ∈ A ∧ a ^ 2 = z} = 12 := by
    simpa [h.hA] using (y6q8_card h.rel h.z_ne hA32).1
  have key := y6_card_coset h hcount
  change Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = z ∧ ∃ v ∈ V, x = a * t * v} =
    6 * Nat.card ↥V
  omega

theorem y6_card_Up (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    Nat.card ↥(y6Up A V t) = 10 * Nat.card ↥V := by
  classical
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.hA]; exact h.card_A
  have hcount : Nat.card ↥{a : G | a ∈ A ∧ a ^ 2 = 1} = 20 := by
    simpa [h.hA] using (y6q8_card h.rel h.z_ne hA32).2
  have key := y6_card_coset (c := 1) h hcount
  change Nat.card ↥{x : G | ∃ a ∈ A, a ^ 2 = 1 ∧ ∃ v ∈ V, x = a * t * v} =
    10 * Nat.card ↥V
  omega

theorem y6_gen_Um (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    closure ((y6Um A V z t : Set G) ∪ (V : Set G)) = A ⊔ C0 := by
  classical
  let K : Subgroup G := closure ((y6Um A V z t : Set G) ∪ (V : Set G))
  have hle : K ≤ A ⊔ C0 := by
    apply (Subgroup.closure_le (A ⊔ C0)).mpr
    intro x hx
    rcases hx with hx | hx
    · exact (y6_Um_sub h x hx).1
    · exact (le_sup_right : C0 ≤ A ⊔ C0) (y6_V_le_C0 h hx)
  have ha1 : a₁ ∈ A := by rw [h.hA]; exact Subgroup.subset_closure (by simp)
  have hb1 : b₁ ∈ A := by rw [h.hA]; exact Subgroup.subset_closure (by simp)
  have ha2 : a₂ ∈ A := by rw [h.hA]; exact Subgroup.subset_closure (by simp)
  have hb2 : b₂ ∈ A := by rw [h.hA]; exact Subgroup.subset_closure (by simp)
  have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
  have huK : u ∈ K := Subgroup.subset_closure (Or.inr huV)
  have hmemUm : ∀ a ∈ A, a ^ 2 = z → a * t ∈ K := by
    intro a ha ha2
    exact Subgroup.subset_closure (Or.inl ⟨a, ha, ha2, 1, one_mem V, by rw [mul_one]⟩)
  have ha1t : a₁ * t ∈ K := hmemUm a₁ ha1 h.rel.a1_sq
  have hb1t : b₁ * t ∈ K := hmemUm b₁ hb1 h.rel.b1_sq
  have ha2t : a₂ * t ∈ K := hmemUm a₂ ha2 h.rel.a2_sq
  have hb2t : b₂ * t ∈ K := hmemUm b₂ hb2 h.rel.b2_sq
  have ha1b1t : (a₁ * b₁) * t ∈ K :=
    hmemUm (a₁ * b₁) (mul_mem ha1 hb1)
      (y6_sq_mul_z h ha1 hb1 h.rel.a1_sq h.rel.b1_sq h.rel.comm1)
  have ha2b2t : (a₂ * b₂) * t ∈ K :=
    hmemUm (a₂ * b₂) (mul_mem ha2 hb2)
      (y6_sq_mul_z h ha2 hb2 h.rel.a2_sq h.rel.b2_sq h.rel.comm2)
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
    rw [h.hA]
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
    rw [h.hC0]
    apply (Subgroup.closure_le K).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [huK, htK]
  exact le_antisymm hle (sup_le hAK hC0K)

theorem y6_card_invol (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    Nat.card ↥{w : G | w ∈ A ⊔ C0 ∧ w ∉ A ∧ w ^ 2 = 1} ≤ 52 := by
  classical
  let W : Set G := {w : G | w ∈ A ⊔ C0 ∧ w ∉ A ∧ w ^ 2 = 1}
  let Up : Set G := y6Up A V t
  let S : Set G := {a : G | a ∈ A ∧ a ^ 2 = z}
  let Su : Set G := (fun a => a * u) '' S
  have hA32 : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← h.hA]; exact h.card_A
  have hS12 : Nat.card ↥S = 12 := by
    simpa [S, h.hA] using (y6q8_card h.rel h.z_ne hA32).1
  have huV : u ∈ V := by rw [h.hV]; exact Subgroup.mem_zpowers u
  have hu3V : u ^ 3 ∈ V := by
    rw [h.hV]
    exact pow_mem (Subgroup.mem_zpowers u) 3
  have hWsub : W ⊆ Up ∪ Su := by
    intro w hw
    obtain ⟨hwC1, hwA, hwsq⟩ := hw
    rcases y6_C1_split h w hwC1 with hwAV | hwUm | hwUp
    · obtain ⟨a, haA, v, hvV, rfl⟩ := y6_AV_elems h w hwAV
      have hva : v ∉ A := fun hvA => hwA (mul_mem haA hvA)
      rcases y6_V_elems h v hvV with rfl | rfl | rfl | rfl
      · exact absurd (one_mem A) hva
      · have ha2 : a ^ 2 = z := y6_sq_eq_z_of_mul h haA huV h.u_sq hwsq
        exact Or.inr ⟨a, ⟨haA, ha2⟩, rfl⟩
      · exact absurd (y6_z_mem_A h) hva
      · have ha2 : a ^ 2 = z := y6_sq_eq_z_of_mul h haA hu3V (y6_u3_sq h) hwsq
        have hsq_az : (a * z) ^ 2 = z := by
          have hcomm : Commute a z := y6_z_comm_A h a haA
          calc (a * z) ^ 2 = a ^ 2 * z ^ 2 := hcomm.mul_pow 2
            _ = z := by rw [ha2, h.rel.z_sq, mul_one]
        refine Or.inr ⟨a * z, ⟨mul_mem haA (y6_z_mem_A h), hsq_az⟩, ?_⟩
        show (a * z) * u = a * u ^ 3
        rw [y6_u3 h, mul_assoc]
    · exfalso
      exact h.z_ne (by rw [← y6_sq_Um h w hwUm, hwsq])
    · exact Or.inl hwUp
  have hUpcard : Up.ncard = 40 := by
    rw [← Nat.card_coe_set_eq, y6_card_Up h, y6_card_V h]
  have hS12n : S.ncard = 12 := by
    rw [← Nat.card_coe_set_eq]
    exact hS12
  have hSucard : Su.ncard ≤ 12 := by
    have hle : Su.ncard ≤ S.ncard := Set.ncard_image_le (s := S) (f := fun a => a * u)
    rwa [hS12n] at hle
  calc Nat.card ↥W = W.ncard := Nat.card_coe_set_eq W
    _ ≤ (Up ∪ Su).ncard := Set.ncard_le_ncard hWsub
    _ ≤ Up.ncard + Su.ncard := Set.ncard_union_le Up Su
    _ ≤ 40 + 12 := Nat.add_le_add (le_of_eq hUpcard) hSucard
    _ = 52 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
