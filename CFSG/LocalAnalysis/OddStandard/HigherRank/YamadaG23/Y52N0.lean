module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B4
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5FrameB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

abbrev y52N0 (s : Setting3 G L) : Subgroup G := thompsonSubgroup s.fr.B ⊔ zpowers s.t

abbrev y52b (s : Setting3 G L) : G := s.fr.a₁ * s.fr.a₂ * s.fr.z

private theorem y52_z_mem_cenB {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.z ∈ cen s.fr.B := by
  have hcen : cen s.fr.B = closure {s.fr.b₁ * s.fr.b₂, s.fr.z} := hH.hLF.fact14.2.2.1.1
  rw [hcen]
  exact Subgroup.subset_closure (by simp)

private theorem y52_z_mem_J {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.z ∈ thompsonSubgroup s.fr.B :=
  y5_V_le_J hH (y52_z_mem_cenB hH)

private theorem y52_z_comm {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {x : G}
    (hx : x ∈ s.fr.B) : s.fr.z * x = x * s.fr.z :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (y52_z_mem_cenB hH)).2 x hx).symm

private theorem y52_a12_order {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    orderOf (s.fr.a₁ * s.fr.a₂) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (y5_a12_sq hH)
    (fun h1 => y5_a12_not_mem_J hH (h1 ▸ Subgroup.one_mem (thompsonSubgroup s.fr.B)))

private theorem y52_a12_norm_J {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {j : G}
    (hj : j ∈ thompsonSubgroup s.fr.B) :
    s.fr.a₁ * s.fr.a₂ * j * (s.fr.a₁ * s.fr.a₂) ∈ thompsonSubgroup s.fr.B := by
  have h := y5_J_conj s (s.fr.a₁ * s.fr.a₂)
    (Subgroup.le_normalizer (y5_a12_mem_B hH)) j hj
  have hinv : (s.fr.a₁ * s.fr.a₂)⁻¹ = s.fr.a₁ * s.fr.a₂ :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact y5_a12_sq hH)
  simpa [hinv] using h

private theorem y52_b_mul_mem_J {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    {j : G} (hj : j ∈ thompsonSubgroup s.fr.B) :
    y52b s * (j * (s.fr.a₁ * s.fr.a₂)) ∈ thompsonSubgroup s.fr.B := by
  have hjB : j ∈ s.fr.B := y5_J_le_B s hj
  have ha12B : s.fr.a₁ * s.fr.a₂ ∈ s.fr.B := y5_a12_mem_B hH
  have hconj := y52_a12_norm_J hH hj
  have hzj : s.fr.z * j = j * s.fr.z := y52_z_comm hH hjB
  have hza : s.fr.z * (s.fr.a₁ * s.fr.a₂) = (s.fr.a₁ * s.fr.a₂) * s.fr.z :=
    y52_z_comm hH ha12B
  have heq : y52b s * (j * (s.fr.a₁ * s.fr.a₂)) =
      (s.fr.a₁ * s.fr.a₂ * j * (s.fr.a₁ * s.fr.a₂)) * s.fr.z := by
    change (s.fr.a₁ * s.fr.a₂ * s.fr.z) * (j * (s.fr.a₁ * s.fr.a₂)) =
      (s.fr.a₁ * s.fr.a₂ * j * (s.fr.a₁ * s.fr.a₂)) * s.fr.z
    calc (s.fr.a₁ * s.fr.a₂ * s.fr.z) * (j * (s.fr.a₁ * s.fr.a₂))
        = s.fr.a₁ * s.fr.a₂ * (s.fr.z * (j * (s.fr.a₁ * s.fr.a₂))) := by group
      _ = s.fr.a₁ * s.fr.a₂ * ((s.fr.z * j) * (s.fr.a₁ * s.fr.a₂)) := by group
      _ = s.fr.a₁ * s.fr.a₂ * ((j * s.fr.z) * (s.fr.a₁ * s.fr.a₂)) := by rw [hzj]
      _ = s.fr.a₁ * s.fr.a₂ * (j * (s.fr.z * (s.fr.a₁ * s.fr.a₂))) := by group
      _ = s.fr.a₁ * s.fr.a₂ * (j * ((s.fr.a₁ * s.fr.a₂) * s.fr.z)) := by rw [hza]
      _ = (s.fr.a₁ * s.fr.a₂ * j * (s.fr.a₁ * s.fr.a₂)) * s.fr.z := by group
  rw [heq]
  exact Subgroup.mul_mem _ hconj (y52_z_mem_J hH)

private theorem mem_sup_zpowers_of_centralizer {G : Type*} [Group G] {c : G} {J : Subgroup G}
    (hJ : J ≤ Subgroup.centralizer ({c} : Set G)) {x : G}
    (hx : x ∈ J ⊔ Subgroup.zpowers c) :
    ∃ j ∈ J, ∃ n : ℤ, j * c ^ n = x := by
  set N : Subgroup G := J ⊔ Subgroup.zpowers c with hN
  have hJN : J ≤ N := le_sup_left
  have hKN : Subgroup.zpowers c ≤ N := le_sup_right
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      have hcomm : c * j = j * c := Subgroup.mem_centralizer_iff.mp (hJ hj) c rfl
      have heq : c * j * c⁻¹ = j := by rw [hcomm]; group
      rw [heq]; exact hj
    · intro hj
      have hx : c * j * c⁻¹ ∈ centralizer ({c} : Set G) := hJ hj
      have hcx : c * (c * j * c⁻¹) = (c * j * c⁻¹) * c :=
        Subgroup.mem_centralizer_iff.mp hx c rfl
      have heq : c * j * c⁻¹ = j := by
        have h1 := congrArg (fun y => c⁻¹ * y) hcx
        rw [show c⁻¹ * (c * (c * j * c⁻¹)) = c * j * c⁻¹ by group,
          show c⁻¹ * ((c * j * c⁻¹) * c) = j by group] at h1
        exact h1
      exact heq ▸ hj
  have hNnorm : N ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hcN
  haveI : (J.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := N) (N := J) hNnorm
  have htop : (⊤ : Subgroup ↥N) = J.subgroupOf N ⊔ (Subgroup.zpowers c).subgroupOf N := by
    rw [← Subgroup.subgroupOf_sup hJN hKN, ← hN, Subgroup.subgroupOf_self]
  have hxtop : (⟨x, hx⟩ : ↥N) ∈ (⊤ : Subgroup ↥N) := trivial
  rw [htop] at hxtop
  obtain ⟨j, hj, k, hk, hjk⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := J.subgroupOf N)
      (t := (Subgroup.zpowers c).subgroupOf N) (x := (⟨x, hx⟩ : ↥N))).mp hxtop
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (show (k : G) ∈ Subgroup.zpowers c from hk)
  refine ⟨(j : G), hj, n, ?_⟩
  have hval : (j : G) * (k : G) = x := congrArg Subtype.val hjk
  rw [← hn] at hval
  exact hval

private theorem y52_inf_L {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y52N0 s ⊓ L = thompsonSubgroup s.fr.B := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxN0, hxL⟩ := Subgroup.mem_inf.mp hx
    change x ∈ thompsonSubgroup s.fr.B ⊔ Subgroup.zpowers s.t at hxN0
    have hJcent : thompsonSubgroup s.fr.B ≤ Subgroup.centralizer ({s.t} : Set G) := by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact s3_comm_t_of_mem_L s (f3_B_le_L s (y5_J_le_B s hj))
    obtain ⟨j, hj, n, hn⟩ := mem_sup_zpowers_of_centralizer hJcent hxN0
    have hjL : j ∈ L := (y5_J_le_B s).trans (f3_B_le_L s) hj
    have htnL : s.t ^ n ∈ L := by
      have h1 : j⁻¹ * (j * s.t ^ n) ∈ L := L.mul_mem (L.inv_mem hjL) (hn ▸ hxL)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
    rcases Int.emod_two_eq_zero_or_one n with h2 | h2
    · have h1 : s.t ^ n = 1 := by
        have h2' : n % ((2 : ℕ) : ℤ) = 0 := h2
        rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp
      rw [h1, mul_one] at hn
      rw [← hn]; exact hj
    · exfalso
      have h1 : s.t ^ n = s.t := by
        have h2' : n % ((2 : ℕ) : ℤ) = 1 := h2
        rw [← zpow_mod_orderOf s.t n, s.t_order, h2']; simp
      exact s3_t_not_mem_L s hH.h31 (h1 ▸ htnL)
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_sup_left hx, (y5_J_le_B s).trans (f3_B_le_L s) hx⟩

private theorem y52_mem_B {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {x : G}
    (hx : x ∈ s.fr.B) :
    x ∈ thompsonSubgroup s.fr.B ∨
      ∃ j ∈ thompsonSubgroup s.fr.B, x = j * (s.fr.a₁ * s.fr.a₂) := by
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
  have hord : orderOf (s.fr.a₁ * s.fr.a₂) = 2 := y52_a12_order hH
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

theorem y52_N0_le_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y52N0 s ≤ f3P s := by
  apply sup_le
  · exact (y5_J_le_B s).trans le_sup_left
  · exact le_sup_right

theorem y52_N0_normal {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ n ∈ y52N0 s, x * n * x⁻¹ ∈ y52N0 s := by
  intro x hx n hn
  have hxB : x ∈ normalizer (s.fr.B : Set G) := f3_X_le_normB hH hx
  have hmap : (y52N0 s).map (MulAut.conj x : G →* G) ≤ y52N0 s := by
    rw [y52N0, Subgroup.map_sup, MonoidHom.map_zpowers]
    apply sup_le
    · rintro _ ⟨j, hj, rfl⟩
      exact Subgroup.mem_sup_left (S := thompsonSubgroup s.fr.B)
        (T := Subgroup.zpowers s.t) (y5_J_conj s x hxB j hj)
    · rw [Subgroup.zpowers_le]
      obtain ⟨v, hv, hvt⟩ := f3_tX_sub hH x hx
      have hvJ : v ∈ thompsonSubgroup s.fr.B := y5_V_le_J hH hv
      have hst : (MulAut.conj x : G →* G) s.t = v * s.t := by
        change x * s.t * x⁻¹ = v * s.t
        exact hvt
      rw [hst]
      exact Subgroup.mul_mem_sup (S := thompsonSubgroup s.fr.B)
        (T := Subgroup.zpowers s.t) hvJ (Subgroup.mem_zpowers s.t)
  exact hmap (Subgroup.mem_map_of_mem (MulAut.conj x : G →* G) hn)

theorem y52_b_mem_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y52b s ∈ f3P s := by
  have hbB : y52b s ∈ s.fr.B := by
    show s.fr.a₁ * s.fr.a₂ * s.fr.z ∈ s.fr.B
    exact Subgroup.mul_mem _ (y5_a12_mem_B hH) (s3_cenB_le_B s (y52_z_mem_cenB hH))
  exact Subgroup.mem_sup_left hbB

theorem y52_b_sq {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y52b s * y52b s = 1 := by
  have hsrel := s3_srel hH.hS hH.hZ s
  have hcomm : Commute (s.fr.a₁ * s.fr.a₂) s.fr.z := by
    have h1 : Commute s.fr.z s.fr.a₁ := by
      rw [← hsrel.a1_sq]
      exact (Commute.refl s.fr.a₁).pow_left 2
    have h2 : Commute s.fr.z s.fr.a₂ := by
      rw [← hsrel.a2_sq]
      exact (Commute.refl s.fr.a₂).pow_left 2
    exact (h1.mul_right h2).symm
  change ((s.fr.a₁ * s.fr.a₂) * s.fr.z) * ((s.fr.a₁ * s.fr.a₂) * s.fr.z) = 1
  rw [← pow_two, hcomm.mul_pow 2, y5_a12_sq hH, hsrel.z_sq, mul_one]

theorem y52_b_not_mem_N0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y52b s ∉ y52N0 s := by
  intro hb
  have hbB : y52b s ∈ s.fr.B := by
    show s.fr.a₁ * s.fr.a₂ * s.fr.z ∈ s.fr.B
    exact Subgroup.mul_mem _ (y5_a12_mem_B hH) (s3_cenB_le_B s (y52_z_mem_cenB hH))
  have hbJ : y52b s ∈ thompsonSubgroup s.fr.B := by
    have hx : y52b s ∈ y52N0 s ⊓ L := Subgroup.mem_inf.mpr ⟨hb, f3_B_le_L s hbB⟩
    rwa [y52_inf_L hH] at hx
  have h1 : s.fr.a₁ * s.fr.a₂ ∈ thompsonSubgroup s.fr.B := by
    have h2 : y52b s * s.fr.z⁻¹ ∈ thompsonSubgroup s.fr.B :=
      Subgroup.mul_mem _ hbJ (Subgroup.inv_mem _ (y52_z_mem_J hH))
    have heq : y52b s * s.fr.z⁻¹ = s.fr.a₁ * s.fr.a₂ := by
      change (s.fr.a₁ * s.fr.a₂ * s.fr.z) * s.fr.z⁻¹ = s.fr.a₁ * s.fr.a₂
      group
    rw [heq] at h2; exact h2
  exact y5_a12_not_mem_J hH h1

theorem y52_P_two_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ p ∈ f3P s, p ∈ y52N0 s ∨ y52b s * p ∈ y52N0 s := by
  intro p hp
  rcases f3_mem_P p hp with hpB | ⟨β, hβB, rfl⟩
  · rcases y52_mem_B hH hpB with hpJ | ⟨j, hjJ, rfl⟩
    · exact Or.inl (Subgroup.mem_sup_left hpJ)
    · exact Or.inr (Subgroup.mem_sup_left (y52_b_mul_mem_J hH hjJ))
  · rcases y52_mem_B hH hβB with hβJ | ⟨j, hjJ, rfl⟩
    · exact Or.inl (Subgroup.mul_mem_sup (S := thompsonSubgroup s.fr.B)
        (T := Subgroup.zpowers s.t) hβJ (Subgroup.mem_zpowers s.t))
    · refine Or.inr ?_
      have hbj := y52_b_mul_mem_J hH hjJ
      have heq : y52b s * ((j * (s.fr.a₁ * s.fr.a₂)) * s.t) =
          (y52b s * (j * (s.fr.a₁ * s.fr.a₂))) * s.t := by group
      rw [heq]
      exact Subgroup.mul_mem_sup (S := thompsonSubgroup s.fr.B)
        (T := Subgroup.zpowers s.t) hbj (Subgroup.mem_zpowers s.t)

theorem y52_C₂_cent_b {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.C₂, x * y52b s * x⁻¹ * (y52b s)⁻¹ ∈ y52N0 s := by
  intro x hx
  have hxX : x ∈ s.X := f3_C₂_le_X hH hx
  have hbP : y52b s ∈ f3P s := y52_b_mem_P hH
  have hxP : x * y52b s * x⁻¹ ∈ f3P s :=
    (Subgroup.mem_normalizer_iff.mp hxX (y52b s)).mp hbP
  rcases y52_P_two_cosets hH (x * y52b s * x⁻¹) hxP with h1 | h2
  · have hbN0 : y52b s ∈ y52N0 s := by
      have hxinv : x⁻¹ ∈ s.X := s.X.inv_mem hxX
      have hconj := y52_N0_normal hH x⁻¹ hxinv (x * y52b s * x⁻¹) h1
      have heq : x⁻¹ * (x * y52b s * x⁻¹) * (x⁻¹)⁻¹ = y52b s := by group
      rwa [heq] at hconj
    exact absurd hbN0 (y52_b_not_mem_N0 hH)
  · have hbX : y52b s ∈ s.X := Subgroup.le_normalizer hbP
    have hmem := y52_N0_normal hH (y52b s) hbX (y52b s * (x * y52b s * x⁻¹)) h2
    have heq : y52b s * (y52b s * (x * y52b s * x⁻¹)) * (y52b s)⁻¹ =
        x * y52b s * x⁻¹ * (y52b s)⁻¹ := by
      rw [← mul_assoc (y52b s) (y52b s) (x * y52b s * x⁻¹), y52_b_sq hH, one_mul]
    rw [heq] at hmem
    exact hmem

theorem y52_a_b {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    y5a s * y52b s * (y5a s)⁻¹ * (y52b s)⁻¹ ∈ y52N0 s := by
  have hA := lfactsA_of_setting hH.hS hH.hZ s
  have haA : y5a s ∈ s.fr.A := y5a_mem_A s
  have hbA : y52b s ∈ s.fr.A := by
    change s.fr.a₁ * s.fr.a₂ * s.fr.z ∈ s.fr.A
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (s3_a₁_mem_A s) (s3_a₂_mem_A s))
      (s3_z_mem_A s)
  have hcomm : ⁅y5a s, y52b s⁆ ∈ s.fr.Z := hA.comm_A _ haA _ hbA
  have hZJ : s.fr.Z ≤ thompsonSubgroup s.fr.B := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (y52_z_mem_J hH)
  have hmem : ⁅y5a s, y52b s⁆ ∈ y52N0 s := Subgroup.mem_sup_left (hZJ hcomm)
  rwa [commutatorElement_def] at hmem

end CFSG.OddStandard.HigherRank.YamadaG23
