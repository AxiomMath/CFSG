module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5FrameB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Cover

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private lemma y4_zmod4_pow_four (x : Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  apply Multiplicative.ext
  rw [toAdd_pow, toAdd_one]
  simp [show (4 : ZMod 4) = 0 from by decide]

private lemma y4_zmod4_prod_pow_four
    (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) : x ^ 4 = 1 := by
  apply Prod.ext
  · have h := map_pow (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x 4
    rw [show (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) (x ^ 4)
        = (x ^ 4).1 from rfl,
      show (MonoidHom.fst (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x = x.1
        from rfl] at h
    rw [h]
    exact y4_zmod4_pow_four x.1
  · have h := map_pow (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x 4
    rw [show (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) (x ^ 4)
        = (x ^ 4).2 from rfl,
      show (MonoidHom.snd (Multiplicative (ZMod 4)) (Multiplicative (ZMod 4))) x = x.2
        from rfl] at h
    rw [h]
    exact y4_zmod4_pow_four x.2

private theorem y4_J_comm_exp {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    (∀ a ∈ thompsonSubgroup s.fr.B, ∀ b ∈ thompsonSubgroup s.fr.B, a * b = b * a) ∧
      (∀ j ∈ thompsonSubgroup s.fr.B, j ^ 4 = 1) := by
  obtain ⟨-, -, -, -, -, -, hJ, hJiso, -, -⟩ := hH.hLF.fact14.2.2.1
  have hJ' : thompsonSubgroup s.fr.B =
      closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ
  obtain ⟨e₀⟩ := hJiso
  let e : ↥(thompsonSubgroup s.fr.B) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    (MulEquiv.subgroupCongr hJ').trans e₀
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    have h : (⟨a, ha⟩ : ↥(thompsonSubgroup s.fr.B)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
      e.injective (by rw [map_mul, map_mul, mul_comm])
    simpa using congrArg (fun z : ↥(thompsonSubgroup s.fr.B) => (z : G)) h
  · intro j hj
    have h4 : e ⟨j, hj⟩ ^ 4 = 1 := y4_zmod4_prod_pow_four _
    have h : (⟨j, hj⟩ : ↥(thompsonSubgroup s.fr.B)) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h4, map_one]
    simpa using congrArg Subtype.val h

private theorem y4_a12_order {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    orderOf (s.fr.a₁ * s.fr.a₂) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (y5_a12_sq hH)
    (fun h1 => y5_a12_not_mem_J hH (h1 ▸ Subgroup.one_mem (thompsonSubgroup s.fr.B)))

theorem y4_card_V (hH : F33Hyp s e) : Nat.card ↥(cen s.fr.B) = 4 := by
  have h := (f3_V_isE2 hH).2
  norm_num at h
  exact h

theorem y4_card_J (hH : F33Hyp s e) : Nat.card ↥(thompsonSubgroup s.fr.B) = 16 := by
  obtain ⟨-, -, -, -, -, -, hJ, hJiso, -, -⟩ := hH.hLF.fact14.2.2.1
  have hJ' : thompsonSubgroup s.fr.B =
      closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ
  obtain ⟨e₀⟩ := hJiso
  let e : ↥(thompsonSubgroup s.fr.B) ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
    (MulEquiv.subgroupCongr hJ').trans e₀
  calc Nat.card ↥(thompsonSubgroup s.fr.B)
      = Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :=
        Nat.card_congr e.toEquiv
    _ = 16 := by
        simp [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem y4_J_comm (hH : F33Hyp s e) :
    ∀ a ∈ thompsonSubgroup s.fr.B, ∀ b ∈ thompsonSubgroup s.fr.B, a * b = b * a :=
  (y4_J_comm_exp hH).1

theorem y4_V_mul_self (hH : F33Hyp s e) : ∀ v ∈ cen s.fr.B, v * v = 1 := by
  intro v hv
  have h := (f3_V_isE2 hH).1.2 (⟨v, hv⟩ : ↥(cen s.fr.B)) (Subgroup.mem_top _)
  simpa [pow_two] using congrArg Subtype.val h

theorem y4_J_sq_mem_V (hH : F33Hyp s e) :
    ∀ j ∈ thompsonSubgroup s.fr.B, j * j ∈ cen s.fr.B := by
  obtain ⟨-, -, -, -, -, -, -, -, homega, -⟩ := hH.hLF.fact14.2.2.1
  have homega' : cen s.fr.B = omega1 (thompsonSubgroup s.fr.B) := homega
  intro j hj
  have h4 : j ^ 4 = 1 := (y4_J_comm_exp hH).2 j hj
  rw [homega']
  refine Subgroup.subset_closure ⟨Subgroup.mul_mem _ hj hj, ?_⟩
  show (j * j) ^ 2 = 1
  have hsq : (j * j) ^ 2 = j ^ 4 := by
    simp only [pow_succ, pow_zero, pow_one]
    group
  rw [hsq, h4]

theorem y4_J_sq_one_mem_V (hH : F33Hyp s e) :
    ∀ j ∈ thompsonSubgroup s.fr.B, j * j = 1 → j ∈ cen s.fr.B := by
  obtain ⟨-, -, -, -, -, -, -, -, homega, -⟩ := hH.hLF.fact14.2.2.1
  have homega' : cen s.fr.B = omega1 (thompsonSubgroup s.fr.B) := homega
  intro j hj hjj
  rw [homega']
  exact Subgroup.subset_closure ⟨hj, by simpa [pow_two] using hjj⟩

theorem y4_alpha_sq (hH : F33Hyp s e) : (s.fr.a₁ * s.fr.a₂) * (s.fr.a₁ * s.fr.a₂) = 1 := by
  simpa [pow_two] using y5_a12_sq hH

theorem y4_alpha_inv_J (hH : F33Hyp s e) :
    ∀ y ∈ thompsonSubgroup s.fr.B,
      (s.fr.a₁ * s.fr.a₂) * y * (s.fr.a₁ * s.fr.a₂)⁻¹ = y⁻¹ := by
  obtain ⟨-, -, -, -, -, -, hJ, -, -, hh₀⟩ := hH.hLF.fact14.2.2.1
  have hJ' : thompsonSubgroup s.fr.B =
      closure {s.fr.b₁, s.fr.a₁ * s.fr.a₂ * s.fr.h₀} := hJ
  have hh₀' : ∀ y ∈ thompsonSubgroup s.fr.B, s.fr.h₀ * y * s.fr.h₀⁻¹ = y⁻¹ := hh₀
  have hsrel : SRel s.fr := s3_srel hH.hS hH.hZ s
  have hcomm := (y4_J_comm_exp hH).1
  have hu : s.fr.a₁ * s.fr.a₂ * s.fr.h₀ ∈ thompsonSubgroup s.fr.B := by
    rw [hJ']; exact Subgroup.subset_closure (by simp)
  intro y hy
  have hα : s.fr.a₁ * s.fr.a₂ = (s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * s.fr.h₀ := by
    rw [mul_assoc, ← pow_two, hsrel.h0_sq, mul_one]
  rw [hα]
  have h1 : ((s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * s.fr.h₀) * y *
      ((s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * s.fr.h₀)⁻¹ =
      (s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * (s.fr.h₀ * y * s.fr.h₀⁻¹) *
        (s.fr.a₁ * s.fr.a₂ * s.fr.h₀)⁻¹ := by group
  rw [h1, hh₀' y hy]
  have h2 : (s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * y⁻¹ *
      (s.fr.a₁ * s.fr.a₂ * s.fr.h₀)⁻¹ = y⁻¹ := by
    have hc := hcomm _ hu _ (Subgroup.inv_mem _ hy)
    calc (s.fr.a₁ * s.fr.a₂ * s.fr.h₀) * y⁻¹ * (s.fr.a₁ * s.fr.a₂ * s.fr.h₀)⁻¹
        = (y⁻¹ * (s.fr.a₁ * s.fr.a₂ * s.fr.h₀)) *
            (s.fr.a₁ * s.fr.a₂ * s.fr.h₀)⁻¹ := by rw [hc]
      _ = y⁻¹ := by group
  rw [h2]

theorem y4_conj_V {x : G} (hx : x ∈ normalizer (s.fr.B : Set G)) :
    ∀ v ∈ cen s.fr.B, x * v * x⁻¹ ∈ cen s.fr.B := by
  have hmap : s.fr.B.map (MulAut.conj x) = s.fr.B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  intro v hv
  obtain ⟨hvB, hvc⟩ := Subgroup.mem_inf.mp hv
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have hmem : x * v * x⁻¹ ∈ s.fr.B.map (MulAut.conj x : G →* G) :=
      Subgroup.mem_map.mpr ⟨v, hvB, by
        show (MulAut.conj x) v = x * v * x⁻¹
        rw [MulAut.conj_apply]⟩
    rwa [hmap] at hmem
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : x⁻¹ * b * x ∈ s.fr.B := (Subgroup.mem_normalizer_iff''.mp hx b).mp hb
    have hcomm : (x⁻¹ * b * x) * v = v * (x⁻¹ * b * x) :=
      Subgroup.mem_centralizer_iff.mp hvc _ hb'
    have h1 : (x * v * x⁻¹) * b = x * (v * (x⁻¹ * b * x)) * x⁻¹ := by group
    have h2 : x * (v * (x⁻¹ * b * x)) * x⁻¹ = x * ((x⁻¹ * b * x) * v) * x⁻¹ := by
      rw [hcomm.symm]
    have h3 : x * ((x⁻¹ * b * x) * v) * x⁻¹ = b * (x * v * x⁻¹) := by group
    rw [h1, h2, h3]

theorem y4_B_cases (hH : F33Hyp s e) :
    ∀ b ∈ s.fr.B, b ∈ thompsonSubgroup s.fr.B ∨
      ∃ j ∈ thompsonSubgroup s.fr.B, b = j * (s.fr.a₁ * s.fr.a₂) := by
  intro x hx
  have hJnormB : s.fr.B ≤ Subgroup.normalizer (thompsonSubgroup s.fr.B : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      exact y5_J_conj s y (Subgroup.le_normalizer hy) j hj
    · intro hj
      have hyinv : y⁻¹ ∈ normalizer (s.fr.B : Set G) :=
        Subgroup.inv_mem _ (Subgroup.le_normalizer hy)
      have h := y5_J_conj s y⁻¹ hyinv (y * j * y⁻¹) hj
      have heq : y⁻¹ * (y * j * y⁻¹) * (y⁻¹)⁻¹ = j := by group
      rwa [heq] at h
  haveI : ((thompsonSubgroup s.fr.B).subgroupOf s.fr.B).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := s.fr.B)
      (N := thompsonSubgroup s.fr.B) hJnormB
  have hJleB : thompsonSubgroup s.fr.B ≤ s.fr.B := y5_J_le_B s
  have hKleB : Subgroup.zpowers (s.fr.a₁ * s.fr.a₂) ≤ s.fr.B :=
    Subgroup.zpowers_le.mpr (y5_a12_mem_B hH)
  have htop : (⊤ : Subgroup ↥s.fr.B) =
      (thompsonSubgroup s.fr.B).subgroupOf s.fr.B ⊔
        (Subgroup.zpowers (s.fr.a₁ * s.fr.a₂)).subgroupOf s.fr.B := by
    rw [← Subgroup.subgroupOf_sup hJleB hKleB, ← y5_B_eq_J_sup hH, Subgroup.subgroupOf_self]
  have hxtop : (⟨x, hx⟩ : ↥s.fr.B) ∈ (⊤ : Subgroup ↥s.fr.B) := trivial
  rw [htop] at hxtop
  obtain ⟨j, hj, k, hk, hjk⟩ :=
    (Subgroup.mem_sup_of_normal_left
      (s := (thompsonSubgroup s.fr.B).subgroupOf s.fr.B)
      (t := (Subgroup.zpowers (s.fr.a₁ * s.fr.a₂)).subgroupOf s.fr.B)
      (x := (⟨x, hx⟩ : ↥s.fr.B))).mp hxtop
  have hjJ : (j : G) ∈ thompsonSubgroup s.fr.B := hj
  have hkK : (k : G) ∈ Subgroup.zpowers (s.fr.a₁ * s.fr.a₂) := hk
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hkK
  have hval : (j : G) * (k : G) = x := congrArg Subtype.val hjk
  rw [← hn] at hval
  have hord : orderOf (s.fr.a₁ * s.fr.a₂) = 2 := y4_a12_order hH
  rcases Int.emod_two_eq_zero_or_one n with h2 | h2
  · left
    have h1 : (s.fr.a₁ * s.fr.a₂) ^ n = 1 := by
      have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
      rw [← zpow_mod_orderOf (s.fr.a₁ * s.fr.a₂) n, hord, h2']; simp
    rw [h1, mul_one] at hval
    rw [← hval]; exact hjJ
  · right
    refine ⟨(j : G), hjJ, ?_⟩
    have h1 : (s.fr.a₁ * s.fr.a₂) ^ n = s.fr.a₁ * s.fr.a₂ := by
      have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
      rw [← zpow_mod_orderOf (s.fr.a₁ * s.fr.a₂) n, hord, h2']; simp
    rw [h1] at hval
    exact hval.symm

theorem y4_fixJ (hH : F33Hyp s e) {k : G} (hk : Y52K s k) :
    ∀ j ∈ thompsonSubgroup s.fr.B, k * j * k⁻¹ * j⁻¹ ∈ cen s.fr.B → j ∈ cen s.fr.B := by
  intro j hjJ hkj
  by_contra hjV
  have hJab : ∀ a ∈ thompsonSubgroup s.fr.B, ∀ b ∈ thompsonSubgroup s.fr.B,
      a * b = b * a := (y4_J_comm_exp hH).1
  have hVJ : cen s.fr.B ≤ thompsonSubgroup s.fr.B := y5_V_le_J hH
  have hkN : k ∈ normalizer (s.fr.B : Set G) := hk.mem.2
  have hkV : ∀ v ∈ cen s.fr.B, k * v * k⁻¹ ∈ cen s.fr.B := y4_conj_V hkN
  have hk1 : k ≠ 1 := by
    intro h1
    obtain ⟨w, hwV, hzV, -, hz1, -⟩ := f3_V_elems hH
    exact hz1 (hk.fix s.fr.z hzV (by rw [h1]; group))
  have hkord : orderOf k = 3 := by
    have hdvd : orderOf k ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hk.cube
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hk1
    · exact h3
  have hkp : IsPGroup 3 (zpowers k) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hkord]; norm_num)
  have hkzL : k ∉ zL L := by
    rw [f3_zL_eq_bot hH]; simpa using hk1
  have htrans : ActsTransitively (zpowers k) (thompsonSubgroup s.fr.B) (cen s.fr.B) :=
    (hH.hLF.fact18.2.1.2.2.2.2.1 k hk.mem hkp hkzL).2.2
  have hJcard : (thompsonSubgroup s.fr.B : Set G).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact y4_card_J hH
  have hVcard : (cen s.fr.B : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact y4_card_V hH
  have hVuni : ((cen s.fr.B : Set G) ∪ (fun y => j * y) '' (cen s.fr.B : Set G)).ncard ≤ 8 := by
    calc ((cen s.fr.B : Set G) ∪ (fun y => j * y) '' (cen s.fr.B : Set G)).ncard
        ≤ (cen s.fr.B : Set G).ncard +
            ((fun y => j * y) '' (cen s.fr.B : Set G)).ncard := Set.ncard_union_le _ _
      _ ≤ 4 + 4 := by
          refine add_le_add (le_of_eq hVcard) ?_
          exact (Set.ncard_image_le (f := fun y => j * y)
            (s := (cen s.fr.B : Set G))).trans (le_of_eq hVcard)
      _ = 8 := by norm_num
  have hnotsub : ¬ (thompsonSubgroup s.fr.B : Set G) ⊆
      (cen s.fr.B : Set G) ∪ (fun y => j * y) '' (cen s.fr.B : Set G) := by
    intro hsub
    have hle := Set.ncard_mono hsub
    omega
  obtain ⟨v, hvJ, hvnot⟩ := Set.not_subset.mp hnotsub
  rw [Set.mem_union, not_or] at hvnot
  obtain ⟨hvV, hvjV⟩ := hvnot
  obtain ⟨k', hk'z, hk'v⟩ := htrans.2.2 j hjJ hjV v hvJ hvV
  have hmem : k' * j * k'⁻¹ * j⁻¹ ∈ cen s.fr.B := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk'z
    rw [← hn]
    have hn3 : ((n % (3 : ℤ)).toNat : ℤ) = n % (3 : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))
    have h1 : k ^ (n % (3 : ℤ)) = k ^ n := by simpa [hkord] using zpow_mod_orderOf k n
    have hzpow : k ^ n = k ^ (n % 3).toNat := by rw [← h1, ← zpow_natCast, hn3]
    rw [hzpow]
    have hmle : (n % 3).toNat ≤ 2 := by
      have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
      have h2 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
      omega
    have hkey : ∀ m ≤ 2, k ^ m * j * (k ^ m)⁻¹ * j⁻¹ ∈ cen s.fr.B := by
      intro m hm
      interval_cases m
      · simp
      · simpa using hkj
      · have hconj : k ^ 2 * j * (k ^ 2)⁻¹ * j⁻¹ =
            (k * (k * j * k⁻¹ * j⁻¹) * k⁻¹) * (k * j * k⁻¹ * j⁻¹) := by
          simp only [pow_two]
          group
        rw [hconj]
        exact Subgroup.mul_mem _ (hkV _ hkj) hkj
    exact hkey _ hmle
  have hmemjV : k' * j * k'⁻¹ ∈ (fun y => j * y) '' (cen s.fr.B : Set G) := by
    rw [Set.mem_image]
    exact ⟨k' * j * k'⁻¹ * j⁻¹, hmem, by rw [hJab j hjJ _ (hVJ hmem)]; group⟩
  obtain ⟨w', hw'V, hw'eq⟩ := hmemjV
  have hw'eq' : j * w' = k' * j * k'⁻¹ := hw'eq
  refine hvjV ?_
  rw [Set.mem_image]
  exact ⟨w' * (v⁻¹ * (k' * j * k'⁻¹))⁻¹,
    Subgroup.mul_mem _ hw'V (Subgroup.inv_mem _ hk'v), by
      rw [← mul_assoc, hw'eq']; group⟩

end CFSG.OddStandard.HigherRank.YamadaG23
