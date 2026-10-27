module

public import CFSG.ClassicalInvolution.Q3.Sec13End15H
public import CFSG.ClassicalInvolution.Q3.Sec13End15R
public import CFSG.ClassicalInvolution.Q3.Sec13EndSp4Fin
import CFSG.ClassicalInvolution.Q3.Sec13EndS3E8
import CFSG.ClassicalInvolution.Q3.Sec13RecogQ8
import CFSG.ClassicalInvolution.Q3.Sec13PerpPair

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

private theorem e15i_card_closure_le {τ τ' : G} (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1)
    (hρ : (τ * τ') ^ 4 = 1) : Nat.card (Subgroup.closure ({τ, τ'} : Set G)) ≤ 8 := by
  set ρ : G := τ * τ' with hρdef
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hτ'i : τ'⁻¹ = τ' := inv_eq_of_mul_eq_one_right hτ'
  have hconj : τ * ρ * τ⁻¹ = ρ⁻¹ := by
    rw [hτi, hρdef, mul_inv_rev, hτ'i, hτi]
    calc τ * (τ * τ') * τ = (τ * τ) * (τ' * τ) := by group
      _ = τ' * τ := by rw [hτ, one_mul]
  have hcomm : ∀ m : ℤ, τ * ρ ^ m = ρ ^ (-m) * τ := by
    intro m
    have h1 : τ * ρ ^ m * τ⁻¹ = ρ ^ (-m) := by
      rw [← conj_zpow, hconj, inv_zpow, zpow_neg]
    calc τ * ρ ^ m = (τ * ρ ^ m * τ⁻¹) * τ := by group
      _ = ρ ^ (-m) * τ := by rw [h1]
  let P : Subgroup G :=
    { carrier := {g | ∃ n : ℤ, g = ρ ^ n ∨ g = ρ ^ n * τ}
      mul_mem' := by
        rintro _ _ ⟨n, rfl | rfl⟩ ⟨m, rfl | rfl⟩
        · exact ⟨n + m, Or.inl (zpow_add ρ n m).symm⟩
        · refine ⟨n + m, Or.inr ?_⟩
          rw [← mul_assoc, ← zpow_add]
        · refine ⟨n + -m, Or.inr ?_⟩
          rw [mul_assoc, hcomm m, ← mul_assoc, ← zpow_add]
        · refine ⟨n + -m, Or.inl ?_⟩
          calc ρ ^ n * τ * (ρ ^ m * τ) = ρ ^ n * (τ * ρ ^ m) * τ := by group
            _ = ρ ^ n * (ρ ^ (-m) * τ) * τ := by rw [hcomm m]
            _ = ρ ^ (n + -m) * (τ * τ) := by rw [zpow_add]; simp only [mul_assoc]
            _ = ρ ^ (n + -m) := by rw [hτ, mul_one]
      one_mem' := ⟨0, Or.inl (by simp)⟩
      inv_mem' := by
        rintro _ ⟨n, rfl | rfl⟩
        · exact ⟨-n, Or.inl (zpow_neg ρ n).symm⟩
        · refine ⟨n, Or.inr ?_⟩
          calc (ρ ^ n * τ)⁻¹ = τ⁻¹ * (ρ ^ n)⁻¹ := mul_inv_rev _ _
            _ = τ * ρ ^ (-n) := by rw [hτi, zpow_neg]
            _ = ρ ^ (-(-n)) * τ := hcomm (-n)
            _ = ρ ^ n * τ := by rw [neg_neg] }
  have hτP : τ ∈ P := ⟨0, Or.inr (by simp)⟩
  have hτ'P : τ' ∈ P := by
    refine ⟨-1, Or.inr ?_⟩
    have e : τ' = ρ ^ (-1 : ℤ) * τ := by
      rw [← hcomm 1, zpow_one, hρdef, ← mul_assoc, hτ, one_mul]
    rw [← e]
  have hTP : Subgroup.closure ({τ, τ'} : Set G) ≤ P := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hτP
    · exact hτ'P
  have hred : ∀ n : ℤ, ∃ k : ℕ, k < 4 ∧ ρ ^ n = ρ ^ k := by
    intro n
    have h4 : ρ ^ (4 : ℤ) = 1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact hρ
    have hn : ρ ^ n = ρ ^ (n % 4) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv n 4]
      rw [zpow_add, zpow_mul, h4, one_zpow, mul_one]
    refine ⟨(n % 4).toNat, by omega, ?_⟩
    have hc : n % 4 = (((n % 4).toNat : ℕ) : ℤ) := by omega
    rw [hn]
    conv_lhs => rw [hc]
    rw [zpow_natCast]
  let f : Fin 8 → G := ![1, ρ, ρ ^ 2, ρ ^ 3, τ, ρ * τ, ρ ^ 2 * τ, ρ ^ 3 * τ]
  have hsub : (Subgroup.closure ({τ, τ'} : Set G) : Set G) ⊆ Set.range f := by
    intro g hg
    obtain ⟨n, hn⟩ := hTP hg
    obtain ⟨k, hk, hkn⟩ := hred n
    rcases hn with rfl | rfl <;> rw [hkn] <;>
      interval_cases k <;> simp [f]
  have hcard : (Set.range f).ncard ≤ 8 := by
    rw [← Set.image_univ]
    calc (f '' Set.univ).ncard ≤ (Set.univ : Set (Fin 8)).ncard :=
          Set.ncard_image_le Set.finite_univ
      _ = 8 := by simp
  calc Nat.card (Subgroup.closure ({τ, τ'} : Set G))
      = (Subgroup.closure ({τ, τ'} : Set G) : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub (Set.finite_range f)
    _ ≤ 8 := hcard

private theorem e15i_isComplement' {N K : Subgroup G} [N.Normal] (h1 : N ⊓ K = ⊥)
    (h2 : N ⊔ K = ⊤) : N.IsComplement' K := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr h1) ?_
  rw [← Subgroup.normal_mul, h2]
  exact Subgroup.coe_top

theorem exists_complement_of_dihedral {D : Subgroup G} [D.Normal] (hDp : IsPGroup 2 D)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {τ τ' : G} (hτ : τ * τ = 1) (hτ' : τ' * τ' = 1)
    (hρ : (τ * τ') ^ 4 = 1)
    (hindex : D.relIndex (D ⊔ Subgroup.closure {τ, τ'}) = 8)
    (hodd : ¬ 2 ∣ (D ⊔ Subgroup.closure {τ, τ'}).index) :
    ∃ H : Subgroup G, D.IsComplement' H := by
  set T : Subgroup G := Subgroup.closure ({τ, τ'} : Set G) with hT
  have hrel : D.relIndex T = 8 := by
    rw [← hindex, Subgroup.relIndex_sup_left]
  have hTle : Nat.card T ≤ 8 := e15i_card_closure_le hτ hτ' hρ
  have hTmul : Nat.card T = 8 * Nat.card ↥(D ⊓ T) := by
    rw [← hrel]
    exact (Subgroup.relIndex_mul_card (H := D) (K := T)).symm
  have hcard1 : Nat.card ↥(D ⊓ T) = 1 := by
    have hpos : 0 < Nat.card ↥(D ⊓ T) := Nat.card_pos
    omega
  have hbot : D ⊓ T = ⊥ := Subgroup.card_eq_one.mp hcard1
  have hDT2 : IsPGroup 2 ↥(D ⊔ T) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hDp
    rw [IsPGroup.iff_card]
    refine ⟨a + 3, ?_⟩
    have hm := (Subgroup.relIndex_mul_card (H := D) (K := D ⊔ T))
    rw [inf_eq_left.mpr le_sup_left, hindex] at hm
    rw [← hm, ha, pow_add]
    norm_num
    ring
  obtain ⟨P, hDTP⟩ := IsPGroup.exists_le_sylow hDT2
  have hPeq : D ⊔ T = (P : Subgroup G) := by
    have h1 : (D ⊔ T).relIndex (P : Subgroup G) * (P : Subgroup G).index = (D ⊔ T).index :=
      Subgroup.relIndex_mul_index hDTP
    have hdvd : (D ⊔ T).relIndex (P : Subgroup G) ∣ (D ⊔ T).index :=
      h1 ▸ dvd_mul_right _ _
    have hodd' : ¬ 2 ∣ (D ⊔ T).relIndex (P : Subgroup G) := fun h2 => hodd (h2.trans hdvd)
    have h2 : (D ⊔ T).relIndex (P : Subgroup G) * Nat.card ↥((D ⊔ T) ⊓ (P : Subgroup G)) =
        Nat.card (P : Subgroup G) := Subgroup.relIndex_mul_card (D ⊔ T) (P : Subgroup G)
    rw [inf_eq_left.mpr hDTP] at h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp P.isPGroup'
    have hdvd2 : (D ⊔ T).relIndex (P : Subgroup G) ∣ 2 ^ k := by
      rw [← hk, ← h2]
      exact dvd_mul_right _ _
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd2
    have hi0 : i = 0 := by
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · exact h0
      · exact absurd (hi ▸ dvd_pow_self 2 hpos.ne') hodd'
    have hR1 : (D ⊔ T).relIndex (P : Subgroup G) = 1 := by
      rw [hi, hi0, pow_zero]
    exact le_antisymm hDTP (Subgroup.relIndex_eq_one.mp hR1)
  haveI : IsMulCommutative D := ⟨⟨fun a b => Subtype.ext (hDab a.1 a.2 b.1 b.2)⟩⟩
  have hTP : T ≤ (P : Subgroup G) := hPeq ▸ le_sup_right
  obtain ⟨K', hK1, hK2⟩ :=
    (CFSG.Quasithin.gaschutz hDp P).mpr ⟨T, hTP, hbot, hPeq⟩
  exact ⟨K', e15i_isComplement' hK1 hK2⟩

theorem dihedral_relations_of_relations {G : Type*} [Group G] {u r v d z : G}
    (hz2 : z * z = 1) (hu2 : u * u = z) (hr2 : r * r = z) (hru : r * u * r⁻¹ = u⁻¹)
    (hd2 : d * d = 1) (hdz : d * z * d⁻¹ = z)
    (hKK : ∀ x ∈ ({u, r} : Set G), ∀ y ∈ ({d * u * d⁻¹, d * r * d⁻¹} : Set G), x * y = y * x)
    (hvu : v * u * v⁻¹ = u) (hvr : v * r * v⁻¹ = r * u ∨ v * r * v⁻¹ = r * u⁻¹)
    (hv4 : v * v * v * v = 1) (hdv : d * v * d⁻¹ = v * v * v) :
    (v * d) * (v * d) = 1 ∧ (u * (d * r * d⁻¹)) * (u * (d * r * d⁻¹)) = 1 ∧
      ((v * d) * (u * (d * r * d⁻¹))) ^ 4 = 1 := by
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  set u' := d * u * d⁻¹ with hu'
  set r' := d * r * d⁻¹ with hr'
  have huu : u * u' = u' * u := hKK u (by simp) u' (by simp [hu'])
  have hur : u * r' = r' * u := hKK u (by simp) r' (by simp [hr'])
  have hru' : r * u' = u' * r := hKK r (by simp) u' (by simp [hu'])
  have hrr : r * r' = r' * r := hKK r (by simp) r' (by simp [hr'])
  have hu'2 : u' * u' = z := by
    calc u' * u' = d * (u * u) * d⁻¹ := by simp only [hu']; group
      _ = z := by rw [hu2]; exact hdz
  have hr'2 : r' * r' = z := by
    calc r' * r' = d * (r * r) * d⁻¹ := by simp only [hr']; group
      _ = z := by rw [hr2]; exact hdz
  have hr'u' : r' * u' * r'⁻¹ = u'⁻¹ := by
    calc r' * u' * r'⁻¹ = d * (r * u * r⁻¹) * d⁻¹ := by simp only [hu', hr']; group
      _ = u'⁻¹ := by rw [hru]; simp only [hu']; group
  have hzr : z * r = r * z := by rw [← hr2]; exact mul_assoc _ _ _
  have hzu' : z * u' = u' * z := by rw [← hu'2]; exact mul_assoc _ _ _
  have hzr' : z * r' = r' * z := by rw [← hr'2]; exact mul_assoc _ _ _
  have h1 : (v * d) * (v * d) = 1 := by
    calc (v * d) * (v * d) = v * (d * v * d⁻¹) * (d * d) := by group
      _ = v * (v * v * v) * 1 := by rw [hdv, hd2]
      _ = v * v * v * v := by group
      _ = 1 := hv4
  have h2 : (u * r') * (u * r') = 1 := by
    calc (u * r') * (u * r') = u * (r' * u) * r' := by group
      _ = u * (u * r') * r' := by rw [← hur]
      _ = (u * u) * (r' * r') := by group
      _ = 1 := by rw [hu2, hr'2, hz2]
  have hdv' : d⁻¹ * v * d = v * v * v := by
    rw [hdi]; rw [hdi] at hdv; exact hdv
  have hvd : v * d = d * (v * v * v) := by
    calc v * d = d * (d⁻¹ * v * d) := by group
      _ = d * (v * v * v) := by rw [hdv']
  have hvc : v * u = u * v := by
    have := hvu
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hvu3 : (v * v * v) * u = u * (v * v * v) := by
    calc (v * v * v) * u = v * v * (v * u) := by group
      _ = v * v * (u * v) := by rw [hvc]
      _ = v * (v * u) * v := by group
      _ = v * (u * v) * v := by rw [hvc]
      _ = (v * u) * v * v := by group
      _ = (u * v) * v * v := by rw [hvc]
      _ = u * (v * v * v) := by group
  have hvu' : v * u' * v⁻¹ = u' := by
    calc v * u' * v⁻¹ = (v * d) * u * (v * d)⁻¹ := by simp only [hu']; group
      _ = (d * (v * v * v)) * u * (d * (v * v * v))⁻¹ := by rw [hvd]
      _ = d * ((v * v * v) * u * (v * v * v)⁻¹) * d⁻¹ := by group
      _ = d * u * d⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hvu3]
  have hr'' : d * r' * d⁻¹ = r := by
    calc d * r' * d⁻¹ = (d * d) * r * (d * d)⁻¹ := by simp only [hr']; group
      _ = r := by rw [hd2]; group
  have hτε : (v * d) * (u * r') * (v * d)⁻¹ = u' * (v * r * v⁻¹) := by
    calc (v * d) * (u * r') * (v * d)⁻¹ = v * (d * u * d⁻¹) * (d * r' * d⁻¹) * v⁻¹ := by group
      _ = v * u' * r * v⁻¹ := by rw [hr'']
      _ = (v * u' * v⁻¹) * (v * r * v⁻¹) := by group
      _ = u' * (v * r * v⁻¹) := by rw [hvu']
  have hW2 : ((v * d) * (u * r')) * ((v * d) * (u * r')) = u' * (v * r * v⁻¹) * (u * r') := by
    calc ((v * d) * (u * r')) * ((v * d) * (u * r'))
        = ((v * d) * (u * r') * (v * d)⁻¹) * ((v * d) * (v * d)) * (u * r') := by group
      _ = u' * (v * r * v⁻¹) * (u * r') := by rw [hτε, h1, mul_one]
  have hcr : Commute r (u' * r') := Commute.mul_right hru' hrr
  have hu'r'2 : (u' * r') * (u' * r') = z := by
    calc (u' * r') * (u' * r') = u' * (r' * u' * r'⁻¹) * (r' * r') := by group
      _ = z := by rw [hr'u', hr'2]; group
  have hY : (u' * r * r') * (u' * r * r') = 1 := by
    have e1 : u' * r * r' = (u' * r') * r := by
      calc u' * r * r' = u' * (r * r') := by group
        _ = u' * (r' * r) := by rw [hrr]
        _ = (u' * r') * r := by group
    rw [e1]
    have := hcr.symm.mul_pow 2
    rw [pow_two, pow_two, pow_two] at this
    rw [this, hu'r'2, hr2, hz2]
  refine ⟨h1, h2, ?_⟩
  have hW4 : ((v * d) * (u * r')) ^ 4 = (((v * d) * (u * r')) * ((v * d) * (u * r'))) *
      (((v * d) * (u * r')) * ((v * d) * (u * r'))) := by
    calc ((v * d) * (u * r')) ^ 4 = ((v * d) * (u * r')) ^ 2 * ((v * d) * (u * r')) ^ 2 := by
          rw [← pow_add]
      _ = _ := by rw [pow_two]
  rw [hW4, hW2]
  have hzY : Commute z (u' * r * r') := Commute.mul_right (Commute.mul_right hzu' hzr) hzr'
  rcases hvr with hA | hB
  ·
    have e : u' * (v * r * v⁻¹) * (u * r') = z * (u' * r * r') := by
      calc u' * (v * r * v⁻¹) * (u * r') = u' * (r * u) * (u * r') := by rw [hA]
        _ = u' * r * (u * u) * r' := by group
        _ = u' * r * z * r' := by rw [hu2]
        _ = (u' * r) * (z * r') := by group
        _ = (u' * r) * (r' * z) := by rw [hzr']
        _ = (u' * r * r') * z := by group
        _ = z * (u' * r * r') := hzY.eq.symm
    rw [e]
    have := hzY.mul_pow 2
    rw [pow_two, pow_two, pow_two] at this
    rw [this, hz2, hY, mul_one]
  ·
    have e : u' * (v * r * v⁻¹) * (u * r') = u' * r * r' := by
      calc u' * (v * r * v⁻¹) * (u * r') = u' * (r * u⁻¹) * (u * r') := by rw [hB]
        _ = u' * r * r' := by group
    rw [e]
    exact hY


private theorem e15i_central {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z)
    (hx : x ∈ K) : x * z = z * x := by
  have hc := hz.conj x
  rw [mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hx)] at hc
  have h1 : x * z * x⁻¹ = z := hc.eq hz
  calc x * z = (x * z * x⁻¹) * x := by group
    _ = z * x := by rw [h1]

private theorem e15i_sq4 (x : G) : x * x * (x * x) = x ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

private theorem e15i_q8_ne {K : Subgroup G} {z i j : G} (hQ : Q8Data K z i j) :
    i * j ≠ j * i := by
  intro h
  have h1 : (1 : G) * (i * j) = z * (i * j) := by
    rw [one_mul]
    exact h.trans hQ.comm
  exact hQ.inv.ne_one (mul_right_cancel h1).symm

private theorem e15i_comm_or {K : Subgroup G} {z x y : G} (hz : IsUniqueInvolution K z)
    (h8 : Nat.card K = 8) (hnab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) (hx : x ∈ K) (hy : y ∈ K) :
    y * x = x * y ∨ y * x = z * (x * y) := by
  have hsx := mul_self_eq_one_or_eq_of_q8 hz h8 hnab hx
  have hsy := mul_self_eq_one_or_eq_of_q8 hz h8 hnab hy
  have hw := mul_self_eq_one_or_eq_of_q8 hz h8 hnab (K.mul_mem hx hy)
  have hs4 : ∀ a : G, (a * a = 1 ∨ a * a = z) → a * a * (a * a) = 1 := by
    intro a ha
    rcases ha with h | h <;> simp [h, hz.sq]
  have hxi : x⁻¹ = x * x * x := inv_eq_of_mul_eq_one_right (by
    calc x * (x * x * x) = x * x * (x * x) := by group
      _ = 1 := hs4 x hsx)
  have hyi : y⁻¹ = y * y * y := inv_eq_of_mul_eq_one_right (by
    calc y * (y * y * y) = y * y * (y * y) := by group
      _ = 1 := hs4 y hsy)
  have hzx : x * z = z * x := e15i_central hz hx
  have hzy : y * z = z * y := e15i_central hz hy
  have h1 : y * x = x⁻¹ * ((x * y) * (x * y)) * y⁻¹ := by group
  rw [hxi, hyi] at h1
  have hxz' : ∀ a : G, x * (z * a) = z * (x * a) := fun a => by
    rw [← mul_assoc, hzx, mul_assoc]
  have hyz' : ∀ a : G, y * (z * a) = z * (y * a) := fun a => by
    rw [← mul_assoc, hzy, mul_assoc]
  have hzz' : ∀ a : G, z * (z * a) = a := fun a => by
    rw [← mul_assoc, hz.sq, one_mul]
  rcases hsx with hs | hs <;> rcases hsy with ht | ht <;> rcases hw with hk | hk <;>
    rw [hs, ht, hk] at h1 <;> simp only [one_mul, mul_one, mul_assoc] at h1 <;>
    try simp only [hxz', hyz', hzz', mul_assoc] at h1
  all_goals first
    | exact Or.inl h1
    | exact Or.inr h1

private theorem e15i_not_central {K : Subgroup G} {z i j u : G} (hQ : Q8Data K z i j)
    (hu : u ∈ K) (huu : u * u = z) : ∃ x ∈ K, u * x ≠ x * u := by
  have hz := hQ.inv
  have hzi : z * i = i * z := by rw [← hQ.sq_i]; group
  have hzj : z * j = j * z := by rw [← hQ.sq_j]; group
  have hne := e15i_q8_ne hQ
  have hz1 : ∀ a : G, z * a = a → False := fun a ha => by
    have h1 : (1 : G) * a = z * a := by rw [one_mul]; exact ha.symm
    exact hz.ne_one (mul_right_cancel h1).symm
  have e4 : i * (z * j) = z * (i * j) := by
    calc i * (z * j) = (i * z) * j := (mul_assoc _ _ _).symm
      _ = (z * i) * j := by rw [← hzi]
      _ = z * (i * j) := mul_assoc _ _ _
  have e5 : i * (z * (i * j)) = z * (i * (i * j)) := by
    calc i * (z * (i * j)) = (i * z) * (i * j) := (mul_assoc _ _ _).symm
      _ = (z * i) * (i * j) := by rw [← hzi]
      _ = z * (i * (i * j)) := mul_assoc _ _ _
  have e6 : i * j * i = j := by
    calc i * j * i = i * (j * i) := mul_assoc _ _ _
      _ = i * (z * (i * j)) := by rw [hQ.comm]
      _ = z * (i * (i * j)) := e5
      _ = z * (z * j) := by rw [← mul_assoc i i j, hQ.sq_i]
      _ = j := by rw [← mul_assoc, hz.sq, one_mul]
  have e7 : i * (i * j) = z * j := by rw [← mul_assoc, hQ.sq_i]
  rcases hQ.nf u hu with h | h | h | h | h | h | h | h
  · rw [h, mul_one] at huu
    exact absurd huu.symm hz.ne_one
  · rw [h, hz.sq] at huu
    exact absurd huu.symm hz.ne_one
  · refine ⟨j, hQ.mem_j, ?_⟩
    rw [h]
    exact hne
  · refine ⟨j, hQ.mem_j, ?_⟩
    rw [h]
    intro heq
    have e2 : j * (z * i) = z * (j * i) := by
      calc j * (z * i) = (j * z) * i := (mul_assoc _ _ _).symm
        _ = (z * j) * i := by rw [← hzj]
        _ = z * (j * i) := mul_assoc _ _ _
    have e3 : z * (i * j) = i * j := by
      calc z * (i * j) = z * i * j := (mul_assoc _ _ _).symm
        _ = j * (z * i) := heq
        _ = z * (j * i) := e2
        _ = z * (z * (i * j)) := by rw [hQ.comm]
        _ = i * j := by rw [← mul_assoc, hz.sq, one_mul]
    exact hz1 (i * j) e3
  · refine ⟨i, hQ.mem_i, ?_⟩
    rw [h]
    exact fun e => hne e.symm
  · refine ⟨i, hQ.mem_i, ?_⟩
    rw [h]
    intro heq
    have e3 : z * (i * j) = i * j := by
      calc z * (i * j) = i * (z * j) := e4.symm
        _ = z * j * i := heq.symm
        _ = z * (j * i) := mul_assoc _ _ _
        _ = z * (z * (i * j)) := by rw [hQ.comm]
        _ = i * j := by rw [← mul_assoc, hz.sq, one_mul]
    exact hz1 (i * j) e3
  · refine ⟨i, hQ.mem_i, ?_⟩
    rw [h]
    intro heq
    rw [e6, e7] at heq
    exact hz1 j heq.symm
  · refine ⟨i, hQ.mem_i, ?_⟩
    rw [h]
    intro heq
    have e8 : z * (i * j) * i = z * j := by rw [mul_assoc, e6]
    rw [e8, e5, e7, show z * (z * j) = j by rw [← mul_assoc, hz.sq, one_mul]] at heq
    exact hz1 j heq

private theorem e15i_closure_eq {K : Subgroup G} (h8 : Nat.card K = 8) {u r : G}
    (hu : u ∈ K) (hu4 : orderOf u = 4) (hr : r ∈ K) (hnotz : r ∉ Subgroup.zpowers u) :
    Subgroup.closure ({u, r} : Set G) = K := by
  have hsub : Subgroup.closure ({u, r} : Set G) ≤ K := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hr
  have hzp : Subgroup.zpowers u ≤ Subgroup.closure ({u, r} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hrc : r ∈ Subgroup.closure ({u, r} : Set G) := Subgroup.subset_closure (by simp)
  have hc4 : Nat.card (Subgroup.zpowers u) = 4 := by rw [Nat.card_zpowers, hu4]
  have hdvd : Nat.card (Subgroup.closure ({u, r} : Set G)) ∣ 8 :=
    h8 ▸ Subgroup.card_dvd_of_le hsub
  have hgt : 4 < Nat.card (Subgroup.closure ({u, r} : Set G)) := by
    rcases Nat.lt_or_ge 4 (Nat.card (Subgroup.closure ({u, r} : Set G))) with hlt | hle
    · exact hlt
    · exfalso
      have heq : Subgroup.zpowers u = Subgroup.closure ({u, r} : Set G) :=
        Subgroup.eq_of_le_of_card_ge hzp (by rw [hc4]; omega)
      exact hnotz (heq ▸ hrc)
  have hle8 : Nat.card (Subgroup.closure ({u, r} : Set G)) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have h8' : Nat.card (Subgroup.closure ({u, r} : Set G)) = 8 := by
    rcases (by omega : Nat.card (Subgroup.closure ({u, r} : Set G)) = 5 ∨
        Nat.card (Subgroup.closure ({u, r} : Set G)) = 6 ∨
        Nat.card (Subgroup.closure ({u, r} : Set G)) = 7 ∨
        Nat.card (Subgroup.closure ({u, r} : Set G)) = 8) with h5 | h5 | h5 | h5
    · rw [h5] at hdvd; norm_num at hdvd
    · rw [h5] at hdvd; norm_num at hdvd
    · rw [h5] at hdvd; norm_num at hdvd
    · exact h5
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [h8, h8'])

namespace EndHyp

variable {Ω : Set (Subgroup G)} {K K' : Subgroup G} {z : G}

private theorem e15i_pair_rel (h : EndHyp Ω) (s : TwinSit Ω K K' z) {J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) {u v r : G}
    (hu : u ∈ K ⊓ Subgroup.normalizer (J : Set G)) (hu4 : orderOf u = 4)
    (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) (hv4 : orderOf v = 4)
    (hr : r ∈ K) (hrU : r ∉ Subgroup.normalizer (J : Set G)) :
    v * u * v⁻¹ = u ∧ (v * r * v⁻¹ = r * u ∨ v * r * v⁻¹ = r * u⁻¹) := by
  refine ⟨?_, ?_⟩
  · have hc := (pair_structure h s.mem hJ hJn).2.2.2.2.1 u hu v hv
    rw [← hc, mul_inv_cancel_right]
  · obtain ⟨a, ha, he⟩ := pair_action h s.mem hJ hJn hu hu4 hv hv4 hr hrU
    have h4u : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
    have hmod : u ^ (a % 4) = u ^ a := by
      have := zpow_mod_orderOf u a
      rw [hu4] at this
      exact_mod_cast this
    have hcases : a % 4 = 1 ∨ a % 4 = 3 := by
      obtain ⟨k, hk⟩ := ha
      omega
    rcases hcases with h1 | h1
    · left
      rw [he, ← hmod, h1, zpow_one]
    · right
      have h3 : u ^ (3 : ℤ) = u⁻¹ := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h4u)
      rw [he, ← hmod, h1, h3]

private theorem e15i_c_mul {D : Subgroup G} (hD : D.Normal)
    (hcomm : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) (v : G) {d d' : G} (hd : d ∈ D)
    (hd' : d' ∈ D) :
    d * d' * v * (d * d')⁻¹ * v⁻¹ = (d' * v * d'⁻¹ * v⁻¹) * (d * v * d⁻¹ * v⁻¹) := by
  have hA : v * d'⁻¹ * v⁻¹ ∈ D := hD.conj_mem d'⁻¹ (D.inv_mem hd') v
  have hc : d * (d' * (v * d'⁻¹ * v⁻¹)) = d' * (v * d'⁻¹ * v⁻¹) * d :=
    hcomm d hd _ (D.mul_mem hd' hA)
  calc d * d' * v * (d * d')⁻¹ * v⁻¹
      = d * (d' * (v * d'⁻¹ * v⁻¹)) * (v * d⁻¹ * v⁻¹) := by group
    _ = d' * (v * d'⁻¹ * v⁻¹) * d * (v * d⁻¹ * v⁻¹) := by rw [hc]
    _ = (d' * v * d'⁻¹ * v⁻¹) * (d * v * d⁻¹ * v⁻¹) := by group

private theorem e15i_exists_not_comm {R : Subgroup G} (hq : IsQuatSub R) {v : G} (hv : v ∈ R)
    (hvv : v * v ≠ 1) : ∃ y ∈ R, y * v ≠ v * y := by
  by_contra hcon
  push_neg at hcon
  exact hvv (hq.sq_eq_one_of_central hv (fun y hy => (hcon y hy).symm))

theorem exists_swap_vector (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') {J : Subgroup G}
    (hJ : J ∈ omegaStarNbr Ω K) (hJn : J ∉ omegaNbr Ω K) {v : G}
    (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) (hv4 : orderOf v = 4) :
    ∃ d ∈ zGroup Ω, d * v * d⁻¹ * v⁻¹ = v * v ∧ d ∉ Subgroup.normalizer (K : Set G) := by
  have hJΩ : J ∈ Ω := hJ.1
  have hJK : J ≠ K := hJ.2.1
  have hvJ : v ∈ J := (Subgroup.mem_inf.mp hv).1
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hcomm : ∀ a ∈ zGroup Ω, ∀ b ∈ zGroup Ω, a * b = b * a := h.zGroup_comm h9
  have hJt : J ∉ twinSet Ω K := by
    rintro ⟨-, z', hzK, hzJ⟩
    exact hJn (Q3CL.T3.twin_mem_omegaNbr h.thmD.hyp s.mem hJΩ hJK hzK hzJ)
  have hv4' : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
  have hvv_sq : v * v * (v * v) = 1 := by
    have h4 : v * v * (v * v) = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4]
    exact hv4'
  have hvv_ne : v * v ≠ 1 := by
    intro h1
    have hd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hv4] at hd
    norm_num at hd
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution h.thmD.hyp hJΩ
  have hvv : IsUniqueInvolution J (v * v) := by
    have hJeq : v * v = zJ :=
      (hzJ.unique (v * v) (J.mul_mem hvJ hvJ) hvv_sq).resolve_left hvv_ne
    rw [hJeq]
    exact hzJ
  obtain ⟨J', hJ'ne, hJtw⟩ := h.twinSet_pair s hJΩ
  have sJ : TwinSit Ω J J' (v * v) := ⟨hJΩ, hvv, hJtw, fun e => hJ'ne e.symm⟩
  obtain ⟨hD16, -, hDK⟩ := h.natCard_zGroup_eq_sixteen_local h9 s h13 hE
  have hcardDK : Nat.card ↥(zGroup Ω ⊓ Subgroup.normalizer (K : Set G)) = 8 := by
    have h2 := h.natCard_zGroup_eq_two_mul h9 s h13
    omega
  have hcardEK : Nat.card (eGroup Ω K) = 8 := by rw [← hDK]; exact hcardDK
  have hEJ : zGroup Ω ⊓ Subgroup.normalizer (J : Set G) = eGroup Ω J :=
    h.inf_normalizer_eq_eGroup_local h9 s h13 hE hJΩ
  have hcardEJ : Nat.card ↥(zGroup Ω ⊓ Subgroup.normalizer (J : Set G)) = 8 := by
    rw [hEJ, h.card_eGroup_eq hJΩ s.mem, hcardEK]
  have hcardEJ' : Nat.card (eGroup Ω J) = 8 := by rw [← hEJ]; exact hcardEJ
  have h13J : zGroup Ω ≠ eGroup Ω J := by
    intro hJeq
    have h1 : Nat.card (zGroup Ω) = Nat.card (eGroup Ω J) := by rw [hJeq]
    omega
  obtain ⟨d₀, hd₀, hsw⟩ := h.exists_mem_zGroup_swap h9 sJ h13J
  have hq : IsQuatSub J :=
    Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp (TC.mem_RSet_of_isPGroup hJΩ (h.thmD.two J hJΩ))
  obtain ⟨y, hyJ, hyv⟩ := e15i_exists_not_comm hq hvJ hvv_ne
  obtain ⟨hbE, hcomm_y⟩ := h.swap_commutator h9 sJ hd₀ hsw hyJ
  have hcv := hcomm_y v hvJ
  generalize d₀ * y * d₀⁻¹ * y⁻¹ = b at hbE hcv
  have hbD : b ∈ zGroup Ω := (Subgroup.mem_inf.mp hbE).1
  have hbN : b ∈ Subgroup.normalizer (J : Set G) := (Subgroup.mem_inf.mp hbE).2
  have hcJ : ∀ e ∈ Subgroup.normalizer (J : Set G), e * v * e⁻¹ * v⁻¹ ∈ J := by
    intro e he
    exact J.mul_mem ((Subgroup.mem_normalizer_iff.mp he v).mp hvJ) (J.inv_mem hvJ)
  have hcD : ∀ e ∈ zGroup Ω, e * v * e⁻¹ * v⁻¹ ∈ zGroup Ω := by
    intro e he
    have h1 : v * e⁻¹ * v⁻¹ ∈ zGroup Ω := hD.conj_mem e⁻¹ ((zGroup Ω).inv_mem he) v
    simpa only [mul_assoc] using (zGroup Ω).mul_mem he h1
  have hcb1 : b * v * b⁻¹ * v⁻¹ ≠ 1 := by
    rw [hcv]
    intro h1
    apply hyv
    have h2 : y⁻¹ * v * y = v := mul_inv_eq_one.mp h1
    calc y * v = y * (y⁻¹ * v * y) := by rw [h2]
      _ = v * y := by group
  have hbv : b * v * b⁻¹ * v⁻¹ = v * v :=
    (hvv.unique (b * v * b⁻¹ * v⁻¹) (hcJ b hbN)
      (h.zGroup_mul_self h9 _ (hcD b hbD))).resolve_left hcb1
  by_contra hcon
  push_neg at hcon
  have hsub : zGroup Ω ⊓ Subgroup.normalizer (J : Set G) ≤
      zGroup Ω ⊓ Subgroup.normalizer (K : Set G) := by
    intro e he
    obtain ⟨heD, heN⟩ := Subgroup.mem_inf.mp he
    by_cases hce1 : e * v * e⁻¹ * v⁻¹ = 1
    · have hcomb : e * b * v * (e * b)⁻¹ * v⁻¹ = v * v := by
        rw [e15i_c_mul hD hcomm v heD hbD, hbv, hce1, mul_one]
      have h1 : e * b ∈ Subgroup.normalizer (K : Set G) :=
        hcon (e * b) ((zGroup Ω).mul_mem heD hbD) hcomb
      have h2 : b ∈ Subgroup.normalizer (K : Set G) := hcon b hbD hbv
      have h3 : e * b * b⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).mul_mem h1
          ((Subgroup.normalizer (K : Set G)).inv_mem h2)
      rw [mul_inv_cancel_right] at h3
      exact Subgroup.mem_inf.mpr ⟨heD, h3⟩
    · have hce : e * v * e⁻¹ * v⁻¹ = v * v :=
        (hvv.unique (e * v * e⁻¹ * v⁻¹) (hcJ e heN)
          (h.zGroup_mul_self h9 _ (hcD e heD))).resolve_left hce1
      exact Subgroup.mem_inf.mpr ⟨heD, hcon e heD hce⟩
  have hEq : zGroup Ω ⊓ Subgroup.normalizer (J : Set G) =
      zGroup Ω ⊓ Subgroup.normalizer (K : Set G) :=
    Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (hcardDK.trans hcardEJ.symm))
  exact h.eGroup_ne_of_local h9 s h13 hE hJ hJt (by rw [← hEJ, ← hDK]; exact hEq)

theorem dihedral_relations_six (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) {u v r d : G} (hu : u ∈ K ⊓ Subgroup.normalizer (J : Set G))
    (hu4 : orderOf u = 4) (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) (hv4 : orderOf v = 4)
    (hr : r ∈ K) (hrU : r ∉ Subgroup.normalizer (J : Set G)) (hd : d ∈ zGroup Ω)
    (hdv : d * v * d⁻¹ * v⁻¹ = v * v) (hdK : d ∉ Subgroup.normalizer (K : Set G)) :
    (v * d) * (v * d) = 1 ∧ (u * (d * r * d⁻¹)) * (u * (d * r * d⁻¹)) = 1 ∧
      ((v * d) * (u * (d * r * d⁻¹))) ^ 4 = 1 := by
  obtain ⟨z', i, j, hQ⟩ := h.exists_q8Data s.mem
  rw [hQ.inv.eq s.isInv] at hQ
  have hK8 : Nat.card K = 8 := h.card_eq_eight s.mem
  have hnab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a :=
    ⟨i, hQ.mem_i, j, hQ.mem_j, e15i_q8_ne hQ⟩
  have hz2 : z * z = 1 := hQ.inv.sq
  have hu2 : u * u = z := by
    have h4 : (u * u) * (u * u) = 1 := by
      calc (u * u) * (u * u) = u ^ 4 := e15i_sq4 u
        _ = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
    rcases hQ.inv.unique _ (K.mul_mem hu.1 hu.1) h4 with h1 | h1
    · exfalso
      have h2 : u ^ 2 = 1 := by
        rw [pow_two]
        exact h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hu4] at h3
      norm_num at h3
    · exact h1
  have hz_mem : z ∈ Subgroup.normalizer (J : Set G) := by
    rw [← hu2]
    exact (Subgroup.normalizer (J : Set G)).mul_mem hu.2 hu.2
  have hr2 : r * r = z := by
    rcases mul_self_eq_one_or_eq_of_q8 hQ.inv hK8 hnab hr with h1 | h1
    · exfalso
      rcases hQ.inv.unique r hr h1 with h2 | h2
      · exact hrU (by rw [h2]; exact Subgroup.one_mem _)
      · exact hrU (by rw [h2]; exact hz_mem)
    · exact h1
  have hru : r * u * r⁻¹ = u⁻¹ := by
    have hnotz : r ∉ Subgroup.zpowers u := fun hm => hrU (Subgroup.zpowers_le.mpr hu.2 hm)
    rcases e15i_comm_or hQ.inv hK8 hnab hu.1 hr with hc | hc
    · exfalso
      have hcl := e15i_closure_eq hK8 hu.1 hu4 hr hnotz
      have hcen : K ≤ Subgroup.centralizer ({u} : Set G) := by
        rw [← hcl]
        refine (Subgroup.closure_le _).mpr ?_
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
            rw [Set.mem_singleton_iff] at hg
            rw [hg]
        · exact Subgroup.mem_centralizer_iff.mpr fun g hg => by
            rw [Set.mem_singleton_iff] at hg
            rw [hg]
            exact hc.symm
      obtain ⟨x, hx, hne⟩ := e15i_not_central hQ hu.1 hu2
      exact hne (Subgroup.mem_centralizer_iff.mp (hcen hx) u (Set.mem_singleton u))
    · have e1 : r * u * r⁻¹ = z * u := by
        calc r * u * r⁻¹ = (r * u) * r⁻¹ := rfl
          _ = z * (u * r) * r⁻¹ := by rw [hc]
          _ = z * u := by group
      have e2 : z * u = u⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hu2, hz2])
      rw [e1, e2]
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, hQ.inv⟩
  have hdz : d * z * d⁻¹ = z := by
    rw [h.zGroup_comm h9 d hd z hzD, mul_inv_cancel_right]
  have hd2 : d * d = 1 := h.zGroup_mul_self h9 d hd
  have hdv' : d * v * d⁻¹ = v * v * v := by
    calc d * v * d⁻¹ = (d * v * d⁻¹ * v⁻¹) * v := by group
      _ = v * v * v := by rw [hdv]
  have hv4' : v * v * v * v = 1 := by
    calc v * v * v * v = v ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
  have hvu : v * u * v⁻¹ = u := by
    have hc := (pair_structure h s.mem hJ hJn).2.2.2.2.1 u hu v hv
    rw [← hc, mul_inv_cancel_right]
  have hvr : v * r * v⁻¹ = r * u ∨ v * r * v⁻¹ = r * u⁻¹ := by
    obtain ⟨a, ha, he⟩ := pair_action h s.mem hJ hJn hu hu4 hv hv4 hr hrU
    have h4u : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
    have hmod : u ^ (a % 4) = u ^ a := by
      have := zpow_mod_orderOf u a
      rw [hu4] at this
      exact_mod_cast this
    have hcases : a % 4 = 1 ∨ a % 4 = 3 := by
      obtain ⟨k, hk⟩ := ha
      omega
    rcases hcases with h1 | h1
    · left
      rw [he, ← hmod, h1, zpow_one]
    · right
      have h3 : u ^ (3 : ℤ) = u⁻¹ := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h4u)
      rw [he, ← hmod, h1, h3]
  have hK' : conjSub d K = K' := by
    have hmem := conjSub_mem_twinSet_of_mem_zGroup h h9 s hd
    rw [s.twin] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h1 | h1
    · exact absurd (mem_normalizer_iff_conjSub_eq.mpr h1) hdK
    · exact h1
  have hKK : ∀ x ∈ ({u, r} : Set G), ∀ y ∈ ({d * u * d⁻¹, d * r * d⁻¹} : Set G),
      x * y = y * x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    have hxK : x ∈ K := by
      rcases hx with rfl | rfl
      · exact hu.1
      · exact hr
    have hyK' : y ∈ K' := by
      rw [← hK']
      rcases hy with rfl | rfl
      · exact conj_mem_conjSub hu.1
      · exact conj_mem_conjSub hr
    exact s.commutes h x hxK y hyK'
  exact dihedral_relations_of_relations hz2 hu2 hr2 hru hd2 hdz hKK hvu hvr hv4' hdv'

theorem sup_dihedral_eq_sup_pair (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) {J : Subgroup G} (hJ : J ∈ omegaStarNbr Ω K)
    (hJn : J ∉ omegaNbr Ω K) {u v r d : G} (hu : u ∈ K ⊓ Subgroup.normalizer (J : Set G))
    (hu4 : orderOf u = 4) (hv : v ∈ J ⊓ Subgroup.normalizer (K : Set G)) (hv4 : orderOf v = 4)
    (hr : r ∈ K) (hrU : r ∉ Subgroup.normalizer (J : Set G)) (hd : d ∈ zGroup Ω) :
    zGroup Ω ⊔ Subgroup.closure {v * d, u * (d * r * d⁻¹)} =
      zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) := by
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hK8 : Nat.card K = 8 := h.card_eq_eight s.mem
  have hps := pair_structure h s.mem hJ hJn
  obtain ⟨hvu, hvr⟩ := e15i_pair_rel h s hJ hJn hu hu4 hv hv4 hr hrU
  have hnotz : r ∉ Subgroup.zpowers u := fun hm => hrU (Subgroup.zpowers_le.mpr hu.2 hm)
  have hc : d * (r * d⁻¹ * r⁻¹) ∈ zGroup Ω :=
    (zGroup Ω).mul_mem hd (hDN.conj_mem d⁻¹ ((zGroup Ω).inv_mem hd) r)
  have hvV : v ∈ K ⊔ J ⊓ Subgroup.normalizer (K : Set G) := Subgroup.mem_sup_right hv
  apply le_antisymm
  ·
    have hKV : K ⊔ J ⊓ Subgroup.normalizer (K : Set G) ≤
        zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) := le_sup_right
    have hdr : d * r * d⁻¹ ∈ zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) := by
      have e : d * r * d⁻¹ = (d * (r * d⁻¹ * r⁻¹)) * r := by group
      rw [e]
      exact (zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G))).mul_mem
        (Subgroup.mem_sup_left hc)
        (hKV (Subgroup.mem_sup_left hr))
    refine sup_le le_sup_left ((Subgroup.closure_le _).mpr ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact (zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G))).mul_mem
        (hKV hvV) (Subgroup.mem_sup_left hd)
    · exact (zGroup Ω ⊔ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G))).mul_mem
        (hKV (Subgroup.mem_sup_left hu.1)) hdr
  ·
    set T := Subgroup.closure ({v * d, u * (d * r * d⁻¹)} : Set G) with hT
    have hτW : v * d ∈ zGroup Ω ⊔ T := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hεW : u * (d * r * d⁻¹) ∈ zGroup Ω ⊔ T :=
      Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hvW : v ∈ zGroup Ω ⊔ T := by
      have e := (zGroup Ω ⊔ T).mul_mem hτW ((zGroup Ω ⊔ T).inv_mem (Subgroup.mem_sup_left hd))
      rwa [mul_inv_cancel_right] at e
    have hur : u * r ∈ zGroup Ω ⊔ T := by
      have e : u * r = (u * (d * (r * d⁻¹ * r⁻¹)) * u⁻¹)⁻¹ * (u * (d * r * d⁻¹)) := by group
      rw [e]
      exact (zGroup Ω ⊔ T).mul_mem
        ((zGroup Ω ⊔ T).inv_mem (Subgroup.mem_sup_left (hDN.conj_mem _ hc u))) hεW
    have huW : u ∈ zGroup Ω ⊔ T := by
      have hk : (u * r)⁻¹ * (v * (u * r) * v⁻¹) ∈ zGroup Ω ⊔ T :=
        (zGroup Ω ⊔ T).mul_mem ((zGroup Ω ⊔ T).inv_mem hur)
          ((zGroup Ω ⊔ T).mul_mem ((zGroup Ω ⊔ T).mul_mem hvW hur)
            ((zGroup Ω ⊔ T).inv_mem hvW))
      have key : v * (u * r) * v⁻¹ = u * (v * r * v⁻¹) := by
        calc v * (u * r) * v⁻¹ = (v * u * v⁻¹) * (v * r * v⁻¹) := by group
          _ = u * (v * r * v⁻¹) := by rw [hvu]
      rw [key] at hk
      rcases hvr with hA | hB
      · rw [hA] at hk
        have e : (u * r)⁻¹ * (u * (r * u)) = u := by group
        rwa [e] at hk
      · rw [hB] at hk
        have e : (u * r)⁻¹ * (u * (r * u⁻¹)) = u⁻¹ := by group
        rw [e] at hk
        simpa using (zGroup Ω ⊔ T).inv_mem hk
    have hrW : r ∈ zGroup Ω ⊔ T := by
      have e := (zGroup Ω ⊔ T).mul_mem ((zGroup Ω ⊔ T).inv_mem huW) hur
      rwa [inv_mul_cancel_left] at e
    have hKT : K ≤ zGroup Ω ⊔ T := by
      rw [← e15i_closure_eq hK8 hu.1 hu4 hr hnotz]
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact huW
      · exact hrW
    have hzv : Subgroup.zpowers v = J ⊓ Subgroup.normalizer (K : Set G) :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv)
        (by rw [hps.2.2.2.1, Nat.card_zpowers, hv4])
    have hVT : J ⊓ Subgroup.normalizer (K : Set G) ≤ zGroup Ω ⊔ T := by
      rw [← hzv]
      exact Subgroup.zpowers_le.mpr hvW
    exact sup_le le_sup_left (sup_le hKT hVT)

private theorem e15i_card_closure_pair {z j : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hj2 : j * j = 1) (hj1 : j ≠ 1) (hzj : z * j = j * z) (hne : z ≠ j) :
    Nat.card (Subgroup.closure ({z, j} : Set G)) = 4 := by
  have hzz : ∀ a : G, z * (z * a) = a := fun a => by rw [← mul_assoc, hz2, one_mul]
  have hjj : ∀ a : G, j * (j * a) = a := fun a => by rw [← mul_assoc, hj2, one_mul]
  have hjz : ∀ a : G, j * (z * a) = z * (j * a) := fun a => by
    rw [← mul_assoc, ← hzj, mul_assoc]
  have hzj' : j * z = z * j := hzj.symm
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hj_inv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hj2
  have hS : (Subgroup.closure ({z, j} : Set G) : Set G) ⊆ ({1, z, j, z * j} : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with hx | hx <;> simp [hx]
    | one => simp
    | mul x y _ _ hx hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
        simp [mul_assoc, hz2, hj2, hzz, hjj, hjz, hzj']
    | inv x _ hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp [mul_inv_rev, hz_inv, hj_inv, hzj']
  have hS' : ({1, z, j, z * j} : Set G) ⊆ (Subgroup.closure ({z, j} : Set G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have heq : (Subgroup.closure ({z, j} : Set G) : Set G) = ({1, z, j, z * j} : Set G) :=
    Set.Subset.antisymm hS hS'
  have h1z : (1 : G) ∉ ({z, j, z * j} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun e => hz1 e.symm, fun e => hj1 e.symm, fun e => hne ?_⟩
    calc z = z * 1 := (mul_one z).symm
      _ = z * (z * j) := by rw [← e]
      _ = j := hzz j
  have hzzj : z ∉ ({j, z * j} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hne, fun e => hj1 ?_⟩
    have : z * 1 = z * j := by rw [mul_one]; exact e
    exact (mul_left_cancel this).symm
  have hjne : j ≠ z * j := by
    intro e
    have h1 : (1 : G) * j = z * j := by rw [one_mul]; exact e
    exact hz1 (mul_right_cancel h1).symm
  calc Nat.card (Subgroup.closure ({z, j} : Set G))
      = (Subgroup.closure ({z, j} : Set G) : Set G).ncard := Nat.card_coe_set_eq _
    _ = ({1, z, j, z * j} : Set G).ncard := by rw [heq]
    _ = 4 := by
      rw [Set.ncard_insert_of_notMem h1z, Set.ncard_insert_of_notMem hzzj,
        Set.ncard_pair hjne]

theorem exists_complement_zGroup (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    (hD16 : Nat.card (zGroup Ω) = 16) (hQ : pCore 2 G = zGroup Ω) :
    ∃ H : Subgroup G, (zGroup Ω).IsComplement' H := by
  have hDN : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant h.thmD.hyp.conjInvariant
  have hK8 : Nat.card K = 8 := h.card_eq_eight s.mem
  obtain ⟨-, -, -, -, J, -, -, hJom, hJtw, -⟩ := exists_choice h h9 s
  have hJn : J ∉ omegaNbr Ω K := notMem_omegaNbr_of_notMem_twinSet h h9 s.mem hJtw
  have hps := pair_structure h s.mem hJom hJn
  obtain ⟨v, hv, hv4, -⟩ := perpP_gen hps.2.2.1 hps.2.2.2.1
  obtain ⟨u, hu, hu4, -⟩ := perpP_gen hps.1 hps.2.1
  obtain ⟨r, hr, hrU⟩ : ∃ r ∈ K, r ∉ Subgroup.normalizer (J : Set G) := by
    by_contra hcon
    push_neg at hcon
    have hKle : K ≤ Subgroup.normalizer (J : Set G) := fun x hx => hcon x hx
    have h4 := hps.2.1
    rw [inf_eq_left.mpr hKle, hK8] at h4
    norm_num at h4
  obtain ⟨d, hd, hdv, hdK⟩ := exists_swap_vector h h9 s h13 hE hJom hJn hv hv4
  have hB := dihedral_relations_six h h9 s h13 hJom hJn hu hu4 hv hv4 hr hrU hd hdv hdK
  have hsup := sup_dihedral_eq_sup_pair h h9 s h13 hJom hJn hu hu4 hv hv4 hr hrU hd
  obtain ⟨j, hj⟩ := h.exists_isUniqueInvolution hJom.1
  have hKV_inf : zGroup Ω ⊓ (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) =
      Subgroup.closure ({z, j} : Set G) := by
    rw [inf_comm (zGroup Ω), ← hQ]
    exact inf_pCore_pair h h9 s h13 hJom hJn hj
  have hzK : z ∈ K := s.isInv.mem
  have hz2 : z * z = 1 := s.isInv.sq
  have hz1 : z ≠ 1 := s.isInv.ne_one
  have hj2 : j * j = 1 := hj.sq
  have hj1 : j ≠ 1 := hj.ne_one
  have hzj : z * j = j * z := h.zGroup_comm h9 z (Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩) j
    (Subgroup.subset_closure ⟨J, hJom.1, hj⟩)
  have hne : z ≠ j := by
    intro e
    have hzJ : z ∈ K ⊓ J := ⟨hzK, by rw [e]; exact hj.mem⟩
    rw [perpP_inf_bot h s.mem hJom.1 (hJom.2.1.symm) hJn] at hzJ
    exact hz1 (Subgroup.mem_bot.mp hzJ)
  have hzj4 := e15i_card_closure_pair hz2 hz1 hj2 hj1 hzj hne
  have hKVcard : Nat.card ↥(K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) = 32 :=
    natCard_sup_pair h s.mem hJom hJn
  have hrel : (zGroup Ω).relIndex (K ⊔ J ⊓ Subgroup.normalizer (K : Set G)) = 8 := by
    have hm := Subgroup.relIndex_mul_card (H := zGroup Ω)
      (K := K ⊔ J ⊓ Subgroup.normalizer (K : Set G))
    rw [hKV_inf, hzj4, hKVcard] at hm
    omega
  have hindex : (zGroup Ω).relIndex
      (zGroup Ω ⊔ Subgroup.closure {v * d, u * (d * r * d⁻¹)}) = 8 := by
    rw [hsup, Subgroup.relIndex_sup_left, hrel]
  have h360 : (zGroup Ω).index = 360 := by
    obtain ⟨φ, hφs, hφk⟩ := exists_hom_alternating_six h h9 s h13 hE
    have hker : φ.ker = zGroup Ω := by
      rw [hφk, centralizer_zGroup_eq_pCore h h9 s h13, hQ]
    have e1 : G ⧸ zGroup Ω ≃* G ⧸ φ.ker := QuotientGroup.quotientMulEquivOfEq hker.symm
    have e2 : G ⧸ φ.ker ≃* alternatingGroup (Fin 6) :=
      QuotientGroup.quotientKerEquivOfSurjective φ hφs
    show Nat.card (G ⧸ zGroup Ω) = 360
    rw [Nat.card_congr (e1.toEquiv.trans e2.toEquiv), nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hodd : ¬ 2 ∣ (zGroup Ω ⊔ Subgroup.closure {v * d, u * (d * r * d⁻¹)}).index := by
    have hm := Subgroup.relIndex_mul_index (H := zGroup Ω)
      (K := zGroup Ω ⊔ Subgroup.closure {v * d, u * (d * r * d⁻¹)}) le_sup_left
    rw [hindex, h360] at hm
    omega
  haveI := hDN
  exact exists_complement_of_dihedral h.zGroup_isPGroup (h.zGroup_comm h9) hB.1 hB.2.1 hB.2.2
    hindex hodd


private theorem e15i_zmod2 : ∀ p q r : ZMod 2, p + (q + r) = 0 → q + r = p := by decide

private theorem e15i_zmod2' : ∀ p q r : ZMod 2, p + (q + r) = 1 → q + r = p + 1 := by decide

private theorem e15i_zmod_two_add_self : ∀ t : ZMod 2, t + t = 0 := by decide

private theorem e15i_zmod_cases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide

private theorem e15i_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private theorem e15i_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

section E15I

private theorem e15i_exists_embed {n : ℕ} {ι : Fin 4 ↪ Fin n} {w : AE.Wr n}
    (hw : AE.SupportedOn w (Set.range ι)) : ∃ w0 : AE.Wr 4, AE.embed ι w0 = w := by
  classical
  have hmap : ∀ i : Fin 4, ∃ j : Fin 4, w.perm (ι i) = ι j := by
    intro i
    by_cases hi : w.perm (ι i) ∈ Set.range ι
    · obtain ⟨j, hj⟩ := hi
      exact ⟨j, hj.symm⟩
    · exfalso
      have h1 : w.perm (w.perm (ι i)) = w.perm (ι i) := (hw _ hi).2
      exact hi ⟨i, (w.perm.injective h1).symm⟩
  choose p0 hp0 using hmap
  have hinj : Function.Injective p0 := by
    intro i i' hii
    apply ι.injective
    apply w.perm.injective
    rw [hp0, hp0, hii]
  let e0 : Equiv.Perm (Fin 4) := Equiv.ofBijective p0 (Function.Injective.bijective_of_finite hinj)
  refine ⟨⟨fun k => w.vec (ι k), e0⟩, ?_⟩
  refine AE.Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
  · by_cases hx : x ∈ Set.range ι
    · obtain ⟨k, rfl⟩ := hx
      rw [AE.embed_vec, AE.embedVec_apply]
    · rw [AE.embed_vec, AE.embedVec_of_not_mem ι _ hx]
      exact ((hw x hx).1).symm
  · by_cases hx : x ∈ Set.range ι
    · obtain ⟨k, rfl⟩ := hx
      rw [AE.embed_perm, AE.embedPerm_apply]
      exact (hp0 k).symm
    · rw [AE.embed_perm, AE.embedPerm_of_not_mem ι _ hx]
      exact ((hw x hx).2).symm

private theorem e15i_cand_mem : ∀ w0 : AE.Wr 4, w0.perm * w0.perm = 1 →
    (∀ k, w0.vec k + w0.vec (w0.perm.symm k) = 1) → w0 ∈ AE.kList ∨ w0 ∈ AE.kStarList := by
  decide +kernel

private theorem e15i_sim_of_beta_eq {G' : Type*} [Group G'] (β : Multiplicative (Fin 6 → ZMod 2) →* G')
    (hker : ∀ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 →
      (β f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1))
    {x y : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0)
    (h : β (Multiplicative.ofAdd x) = β (Multiplicative.ofAdd y)) : Sp4.Sim x y := by
  have hev : ∑ i, (Multiplicative.ofAdd x * (Multiplicative.ofAdd y)⁻¹).toAdd i = 0 := by
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, hx, hy, neg_zero, add_zero]
  have h1 : β (Multiplicative.ofAdd x * (Multiplicative.ofAdd y)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  unfold Sp4.Sim
  rcases (hker _ hev).mp h1 with h2 | h2
  · left
    funext k
    have hk := congrFun h2 k
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply,
      Pi.zero_apply] at hk
    linear_combination hk
  · right
    funext k
    have hk := congrFun h2 k
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply] at hk
    simp only [Pi.add_apply, Sp4.ones]
    linear_combination hk

private theorem e15i_zpowers_of_sq {G' : Type*} [Group G'] {z x : G'} (hz : z * z = 1)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, hz2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hz2, one_zpow, one_mul]

end E15I

theorem map_eq_memBar_six (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    {σ : G →* Equiv.Perm (Fin 6)} {β : Multiplicative (Fin 6 → ZMod 2) →* G}
    (hsp : SixPointData (zGroup Ω) σ β) {H : Subgroup G}
    (R : AESplitHyp (zGroup Ω) H (σ.comp H.subtype) β) (φ : G →* AE.AEQ 6)
    (hφβ : ∀ f : Multiplicative (Fin 6 → ZMod 2), ∑ i, f.toAdd i = 0 →
      φ (β f) = AE.mkQ 6 (AE.Wr.ofVec f.toAdd))
    (hφH : ∀ x : H, φ x = AE.mkQ 6 (AE.Wr.ofPerm (σ x))) :
    ∃ (α : Finset (Fin 6)) (hα : α.card = 4) (b : Bool), K.map φ = AE.memBar α hα b := by
  classical
  obtain ⟨z', i, j, hQ⟩ := h.exists_q8Data s.mem
  have hQ8 : Q8Data K z i j := by
    rw [s.isInv.eq hQ.inv]
    exact hQ
  have hK : IsUniqueInvolution K z := hQ8.inv
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, s.mem, s.isInv⟩
  obtain ⟨a, b, hab, hzβ⟩ := hsp.exists_duad hzD hK.ne_one
  have hdEv : ∑ k, Sp4.duadVec a b k = 0 := by
    simp [Sp4.duadVec, Finset.sum_add_distrib, Pi.single_apply, hab] <;> decide
  have hdEv' : ∑ k, (Multiplicative.ofAdd (Sp4.duadVec a b)).toAdd k = 0 := hdEv
  have hdA : Sp4.duadVec a b a = 1 := by simp [Sp4.duadVec, Pi.single_apply, hab]
  have hdB : Sp4.duadVec a b b = 1 := by simp [Sp4.duadVec, Pi.single_apply, hab.symm]
  have hdK : ∀ k, k ≠ a → k ≠ b → Sp4.duadVec a b k = 0 := by
    intro k h1 h2
    simp [Sp4.duadVec, Pi.single_apply, h1, h2]
  have hβcomm : ∀ f g : Multiplicative (Fin 6 → ZMod 2), β f * β g = β g * β f := by
    intro f g
    rw [← map_mul, ← map_mul, mul_comm]
  have hσD : ∀ f : Multiplicative (Fin 6 → ZMod 2), ∑ k, f.toAdd k = 0 → σ (β f) = 1 := by
    intro f _
    refine (hsp.ker (β f)).mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨g, _, rfl⟩ := (hsp.mem_iff y).mp hy
    exact hβcomm g f
  have hσz : σ z = 1 := by
    rw [hzβ]
    exact hσD _ hdEv'
  have hσ_sq : ∀ g : G, g * g = z → σ g * σ g = 1 := fun g hg => by
    rw [← map_mul, hg, hσz]
  have hzi : i * z = z * i := by rw [← hQ8.sq_i, mul_assoc]
  have hzj : j * z = z * j := by rw [← hQ8.sq_j, mul_assoc]
  have hijz : i * j * z = z * (i * j) := by
    rw [mul_assoc, hzj, ← mul_assoc, hzi, mul_assoc]
  have hzK : ∀ x ∈ K, x * z = z * x := by
    intro x hx
    rcases hQ8.nf x hx with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · rw [h1, one_mul, mul_one]
    · rw [h1]
    · rw [h1]; exact hzi
    · rw [h1, mul_assoc, hzi]
    · rw [h1]; exact hzj
    · rw [h1, mul_assoc, hzj]
    · rw [h1]; exact hijz
    · rw [h1, mul_assoc, hijz]
  have hDK_card : Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (K : Set G)) = 2 := by
    have h16 := (h.natCard_zGroup_eq_sixteen_local h9 s h13 hE).1
    have h8 := h.natCard_zGroup_eq_eight_mul h9 s h13
    rw [h16] at h8
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDK : zGroup Ω ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z := by
    have hle : Subgroup.zpowers z ≤ zGroup Ω ⊓ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.zpowers_le]
      exact ⟨hzD, Subgroup.mem_centralizer_iff.mpr fun k hk => hzK k hk⟩
    have hord : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact hK.sq) hK.ne_one
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hord, hDK_card]))).symm
  have hcentr : ∀ g ∈ K, σ g = 1 → g = 1 ∨ g = z := by
    intro g hg h1
    have hmem : g ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) :=
      ⟨hg, (hsp.ker g).mp h1⟩
    rw [inf_centralizer_zGroup_eq_zpowers h h9 s h13] at hmem
    exact e15i_zpowers_of_sq hK.sq hmem
  have hsi2 : σ i * σ i = 1 := hσ_sq i hQ8.sq_i
  have hsj2 : σ j * σ j = 1 := hσ_sq j hQ8.sq_j
  have hsi1 : σ i ≠ 1 := by
    intro h1
    rcases hcentr i hQ8.mem_i h1 with h2 | h2
    · apply hK.ne_one
      calc z = i * i := hQ8.sq_i.symm
        _ = 1 * 1 := by rw [h2]
        _ = 1 := mul_one 1
    · apply hK.ne_one
      calc z = i * i := hQ8.sq_i.symm
        _ = z * z := by rw [h2]
        _ = 1 := hK.sq
  have hsj1 : σ j ≠ 1 := by
    intro h1
    rcases hcentr j hQ8.mem_j h1 with h2 | h2
    · apply hK.ne_one
      calc z = j * j := hQ8.sq_j.symm
        _ = 1 * 1 := by rw [h2]
        _ = 1 := mul_one 1
    · apply hK.ne_one
      calc z = j * j := hQ8.sq_j.symm
        _ = z * z := by rw [h2]
        _ = 1 := hK.sq
  have hst_ne : σ j ≠ σ i := by
    intro hij
    have hk : i⁻¹ * j ∈ K := K.mul_mem (K.inv_mem hQ8.mem_i) hQ8.mem_j
    have hσk : σ (i⁻¹ * j) = 1 := by
      rw [map_mul, map_inv, hij, inv_mul_cancel]
    rcases hcentr (i⁻¹ * j) hk hσk with h2 | h2
    · have hji : j = i := (inv_mul_eq_one.mp h2).symm
      have hc := hQ8.comm
      rw [hji, hQ8.sq_i] at hc
      exact hK.ne_one (hc.trans hK.sq)
    · have hj : j = i * z := by
        rw [← h2, mul_inv_cancel_left]
      have hc := hQ8.comm
      rw [hj] at hc
      have e1 : i * z * i = 1 := by
        rw [mul_assoc, ← hzi, ← mul_assoc, hQ8.sq_i, hK.sq]
      have e2 : z * (i * (i * z)) = z := by
        rw [← mul_assoc i i z, hQ8.sq_i, hK.sq, mul_one]
      exact hK.ne_one (e1.symm.trans (hc.trans e2)).symm
  have hcomm_st : σ i * σ j = σ j * σ i := by
    rw [← map_mul, ← map_mul, hQ8.comm, map_mul σ z (i * j), hσz, one_mul]
  have hsign : ∀ g : G, Equiv.Perm.sign (σ g) = 1 := fun g => by
    have hmem : σ g ∈ σ.range := MonoidHom.mem_range.mpr ⟨g, rfl⟩
    rw [hsp.range] at hmem
    exact Equiv.Perm.mem_alternatingGroup.mp hmem
  have hconj_d : ∀ g : G, g * z = z * g →
      Sp4.Sim (Sp4.permVec (σ g) (Sp4.duadVec a b)) (Sp4.duadVec a b) := by
    intro g hg
    have e := hsp.conj g (Multiplicative.ofAdd (Sp4.duadVec a b)) hdEv'
    simp only [toAdd_ofAdd] at e
    rw [← hzβ] at e
    have e' : g * z * g⁻¹ = z := by
      rw [hg, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : β (Multiplicative.ofAdd (Sp4.permVec (σ g) (Sp4.duadVec a b))) =
        β (Multiplicative.ofAdd (Sp4.duadVec a b)) := e.symm.trans (e'.trans hzβ)
    exact e15i_sim_of_beta_eq β hsp.eq_one_iff
      ((Equiv.sum_comp (σ g).symm _).trans hdEv) hdEv h2
  have hones : β (Multiplicative.ofAdd Sp4.ones) = 1 :=
    (hsp.eq_one_iff _ (by decide)).mpr (Or.inr rfl)
  have hX : ∀ x : Fin 6 → ZMod 2, Sp4.Even6 x → Sp4.Sim (Sp4.permVec (σ i) x) x →
      Sp4.Sim (Sp4.permVec (σ j) x) x → Sp4.Sim x 0 ∨ Sp4.Sim x (Sp4.duadVec a b) := by
    intro x hx hsx htx
    have hxev : ∑ k, (Multiplicative.ofAdd x).toAdd k = 0 := hx
    have hcommu : ∀ g : G, Sp4.Sim (Sp4.permVec (σ g) x) x →
        g * β (Multiplicative.ofAdd x) = β (Multiplicative.ofAdd x) * g := by
      intro g hsg
      have e := hsp.conj g (Multiplicative.ofAdd x) hxev
      simp only [toAdd_ofAdd] at e
      have e2 : β (Multiplicative.ofAdd (fun k => x ((σ g).symm k))) =
          β (Multiplicative.ofAdd x) := by
        unfold Sp4.Sim at hsg
        rcases hsg with h1 | h1
        · rw [show (fun k => x ((σ g).symm k)) = x from h1]
        · rw [show (fun k => x ((σ g).symm k)) = x + Sp4.ones from h1, ofAdd_add, map_mul,
            hones, mul_one]
      rw [e2] at e
      exact mul_inv_eq_iff_eq_mul.mp e
    have hu_i := hcommu i hsx
    have hu_j := hcommu j htx
    have hcomm_mul : ∀ p q u : G, p * u = u * p → q * u = u * q → p * q * u = u * (p * q) := by
      intro p q u hp hq
      rw [mul_assoc, hq, ← mul_assoc p u q, hp, mul_assoc]
    have hu_z : z * β (Multiplicative.ofAdd x) = β (Multiplicative.ofAdd x) * z := by
      rw [← hQ8.sq_i]
      exact hcomm_mul i i _ hu_i hu_i
    have hu_C : β (Multiplicative.ofAdd x) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      rcases hQ8.nf k hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
      · rw [one_mul, mul_one]
      · exact hu_z
      · exact hu_i
      · exact hcomm_mul z i _ hu_z hu_i
      · exact hu_j
      · exact hcomm_mul z j _ hu_z hu_j
      · exact hcomm_mul i j _ hu_i hu_j
      · exact hcomm_mul z (i * j) _ hu_z (hcomm_mul i j _ hu_i hu_j)
    have hu_D : β (Multiplicative.ofAdd x) ∈ zGroup Ω := (hsp.mem_iff _).mpr ⟨_, hxev, rfl⟩
    have hu1 : β (Multiplicative.ofAdd x) ∈ zGroup Ω ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨hu_D, hu_C⟩
    rw [hDK] at hu1
    unfold Sp4.Sim
    rcases e15i_zpowers_of_sq hK.sq hu1 with h1 | h1
    · left
      rcases (hsp.eq_one_iff _ hxev).mp h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by rw [zero_add]; exact h2)
    · right
      exact e15i_sim_of_beta_eq β hsp.eq_one_iff hx hdEv (h1.trans hzβ)
  obtain ⟨hsa, hsb, hta, htb⟩ := Sp4.klein_fixes_duad a b hab (σ i) hsi2 hsi1 (hsign i)
    (hconj_d i hzi) (σ j) hsj2 hsj1 (hsign j) hst_ne hcomm_st (hconj_d j hzj) hX
  obtain ⟨α, hαdef⟩ : ∃ α : Finset (Fin 6), α = ({a, b} : Finset (Fin 6))ᶜ := ⟨_, rfl⟩
  have hαcard : α.card = 4 := by
    rw [hαdef, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
  have hαmem : ∀ x, x ∈ α ↔ x ≠ a ∧ x ≠ b := by
    intro x
    rw [hαdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  have hrange : Set.range (AE.emb α hαcard) = (α : Set (Fin 6)) := AE.range_emb α hαcard
  have hι_mem : ∀ k, AE.emb α hαcard k ∈ α := fun k => by
    have hk : AE.emb α hαcard k ∈ Set.range (AE.emb α hαcard) := Set.mem_range_self k
    rw [hrange] at hk
    exact hk
  have hφinj : Function.Injective φ := R.injective_of hφβ hφH
  have hφz : φ z = AE.mkQ 6 (AE.Wr.ofVec (Sp4.duadVec a b)) := by
    rw [hzβ]
    exact hφβ _ hdEv'
  have hmkQ_one : ∀ v : AE.Wr 6, v ∈ AE.piSub 6 → AE.mkQ 6 v = 1 :=
    fun v hv => (QuotientGroup.eq_one_iff v).mpr hv
  have hzOf : AE.zOf (AE.emb α hαcard) = AE.Wr.ofVec (Sp4.duadVec a b) * AE.Wr.allOnes 6 := by
    refine AE.Wr.ext (funext fun x => ?_) (Equiv.ext fun x => ?_)
    · rw [AE.zOf_vec_apply]
      show (if x ∈ Set.range (AE.emb α hαcard) then (1 : ZMod 2) else 0) =
        Sp4.duadVec a b x + 1
      by_cases hx : x ∈ Set.range (AE.emb α hαcard)
      · have hxα : x ∈ α := by
          rw [hrange] at hx
          exact hx
        obtain ⟨h1, h2⟩ := (hαmem x).mp hxα
        rw [if_pos hx, hdK x h1 h2, zero_add]
      · have hxab : x = a ∨ x = b := by
          by_contra hc'
          push_neg at hc'
          exact hx (by rw [hrange]; exact (hαmem x).mpr hc')
        rw [if_neg hx]
        rcases hxab with h | h
        · rw [h, hdA, e15i_one_add_one]
        · rw [h, hdB, e15i_one_add_one]
    · simp [AE.zOf_perm, AE.Wr.mul_perm, AE.Wr.ofVec, AE.Wr.allOnes]
  have hφz' : φ z = AE.zBar α hαcard := by
    rw [hφz, AE.zBar, hzOf, map_mul, hmkQ_one _ (AE.mem_piSub.mpr (Or.inr rfl)), mul_one]
  have key : ∀ g : G, g * g = z → σ g ≠ 1 → σ g a = a → σ g b = b →
      φ g ∈ AE.memBar α hαcard true ⊔ AE.memBar α hαcard false := by
    intro g hgg hp1 hpa hpb
    have hp2 : σ g * σ g = 1 := hσ_sq g hgg
    obtain ⟨f, hf, x, hx⟩ := R.exists_eq_mul g
    have hpx : σ g = σ (x : G) := by
      rw [← hx, map_mul, hσD f hf, one_mul]
    obtain ⟨w, hw⟩ : ∃ w : AE.Wr 6, w = ⟨f.toAdd, σ g⟩ := ⟨_, rfl⟩
    have hφg : φ g = AE.mkQ 6 w := by
      rw [hw, hpx, ← hx, map_mul, hφβ f hf, hφH x, ← map_mul]
      congr 1
      refine AE.Wr.ext (funext fun k => ?_) ?_
      · simp [AE.Wr.mul_vec, AE.Wr.ofVec, AE.Wr.ofPerm]
      · simp [AE.Wr.mul_perm, AE.Wr.ofVec, AE.Wr.ofPerm]
    have hsq : AE.mkQ 6 (w * w) = AE.mkQ 6 (AE.Wr.ofVec (Sp4.duadVec a b)) := by
      have h1 : φ g * φ g = φ z := by rw [← map_mul, hgg]
      rw [hφg, hφz, ← map_mul] at h1
      exact h1
    have hcase := AE.mkQ_eq_iff.mp hsq.symm
    have hvecf : ∀ k, ((AE.Wr.ofVec (Sp4.duadVec a b))⁻¹ * (w * w)).vec k =
        Sp4.duadVec a b k + (f.toAdd k + f.toAdd ((σ g).symm k)) := by
      intro k
      simp [AE.Wr.mul_vec, AE.Wr.inv_vec, AE.Wr.inv_perm, AE.Wr.ofVec, hw, Equiv.Perm.one_def,
        Equiv.Perm.inv_def, Equiv.refl_symm, Equiv.refl_apply]
    have hsim : Sp4.Sim (f.toAdd + Sp4.permVec (σ g) f.toAdd) (Sp4.duadVec a b) := by
      unfold Sp4.Sim
      rcases hcase with h1 | h1
      · left
        funext k
        have hk := congrArg (fun v : AE.Wr 6 => v.vec k) h1
        simp only [AE.Wr.one_vec, Pi.zero_apply] at hk
        rw [hvecf k] at hk
        simp only [Pi.add_apply, Sp4.permVec]
        exact e15i_zmod2 _ _ _ hk
      · right
        funext k
        have hk := congrArg (fun v : AE.Wr 6 => v.vec k) h1
        simp only [AE.Wr.allOnes] at hk
        rw [hvecf k] at hk
        simp only [Pi.add_apply, Sp4.permVec, Sp4.ones]
        exact e15i_zmod2' _ _ _ hk
    have hfa : f.toAdd a = f.toAdd b :=
      Sp4.vec_supported_model a b hab (σ g) hp2 hp1 hpa hpb f.toAdd hf hsim
    obtain ⟨c, hc⟩ : ∃ c : ZMod 2, c = f.toAdd a := ⟨_, rfl⟩
    obtain ⟨w', hw'⟩ : ∃ w' : AE.Wr 6, w' = ⟨f.toAdd + fun _ : Fin 6 => c, σ g⟩ := ⟨_, rfl⟩
    have hF' : ∀ k, k ≠ a → k ≠ b →
        (f.toAdd + fun _ : Fin 6 => c) k + (f.toAdd + fun _ : Fin 6 => c) ((σ g).symm k) = 1 := by
      intro k hka hkb
      have hpsa : (σ g).symm a = a := (Equiv.symm_apply_eq _).mpr hpa.symm
      unfold Sp4.Sim at hsim
      rcases hsim with h1 | h1
      · exfalso
        have h2 := congrFun h1 a
        have e1 : (f.toAdd + Sp4.permVec (σ g) f.toAdd) a = 0 := by
          simp only [Pi.add_apply, Sp4.permVec, hpsa]
          exact e15i_zmod_two_add_self _
        rw [e1, hdA] at h2
        exact absurd h2 e15i_zero_ne_one
      · have h2 := congrFun h1 k
        simp only [Pi.add_apply, Sp4.permVec, Sp4.ones, hdK k hka hkb, zero_add] at h2
        simp only [Pi.add_apply]
        linear_combination h2 + e15i_zmod_two_add_self c
    have hF'a : (f.toAdd + fun _ : Fin 6 => c) a = 0 := by
      simp only [Pi.add_apply]
      rw [← hc]
      exact e15i_zmod_two_add_self c
    have hF'b : (f.toAdd + fun _ : Fin 6 => c) b = 0 := by
      simp only [Pi.add_apply]
      rw [← hfa, ← hc]
      exact e15i_zmod_two_add_self c
    have hcpi : ∀ t : ZMod 2, (⟨fun _ => t, 1⟩ : AE.Wr 6) ∈ AE.piSub 6 := by
      intro t
      rcases e15i_zmod_cases t with h0 | h0
      · rw [h0]
        exact AE.mem_piSub.mpr (Or.inl rfl)
      · rw [h0]
        exact AE.mem_piSub.mpr (Or.inr rfl)
    have hwv : w' = w * ⟨fun _ : Fin 6 => c, 1⟩ := by
      rw [hw, hw']
      refine AE.Wr.ext (funext fun k => ?_) ?_
      · simp [AE.Wr.mul_vec]
      · simp [AE.Wr.mul_perm]
    have hφw : φ g = AE.mkQ 6 w' := by
      rw [hφg, hwv, map_mul, hmkQ_one _ (hcpi c), mul_one]
    have hsupp : AE.SupportedOn w' (Set.range (AE.emb α hαcard)) := by
      intro x hx
      have hxab : x = a ∨ x = b := by
        by_contra hc'
        push_neg at hc'
        exact hx (by rw [hrange]; exact (hαmem x).mpr hc')
      rcases hxab with h | h
      · rw [h, hw']
        exact ⟨hF'a, hpa⟩
      · rw [h, hw']
        exact ⟨hF'b, hpb⟩
    obtain ⟨w0, hw0⟩ := e15i_exists_embed hsupp
    have hEp : AE.embedPerm (AE.emb α hαcard) w0.perm = σ g := by
      have h1 := congrArg AE.Wr.perm hw0
      rw [AE.embed_perm, hw'] at h1
      exact h1
    have hτ : w0.perm * w0.perm = 1 := by
      have h1 : AE.embedPerm (AE.emb α hαcard) (w0.perm * w0.perm) = 1 := by
        rw [AE.embedPerm_mul, hEp, hp2]
      refine Equiv.ext fun k => ?_
      have h2 := congrArg (fun π : Equiv.Perm (Fin 6) => π (AE.emb α hαcard k)) h1
      simp only [AE.embedPerm_apply, Equiv.Perm.one_apply] at h2
      exact (AE.emb α hαcard).injective h2
    have hcond : ∀ k, w0.vec k + w0.vec (w0.perm.symm k) = 1 := by
      intro k
      have h1 := congrArg (fun v : AE.Wr 6 => v.vec (AE.emb α hαcard k)) hw0
      have h2 := congrArg (fun v : AE.Wr 6 => v.vec (AE.emb α hαcard (w0.perm.symm k))) hw0
      simp only [AE.embed_vec, AE.embedVec_apply] at h1 h2
      have h3 : AE.emb α hαcard (w0.perm.symm k) = (σ g).symm (AE.emb α hαcard k) := by
        rw [← hEp, AE.embedPerm_symm_apply]
      rw [h3] at h2
      rw [h1, h2, hw']
      obtain ⟨hk1, hk2⟩ := (hαmem _).mp (hι_mem k)
      exact hF' _ hk1 hk2
    rcases e15i_cand_mem w0 hτ hcond with hk | hk
    · refine Subgroup.mem_sup_left ?_
      have hmemK : AE.embed (AE.emb α hαcard) w0 ∈ AE.memAt α hαcard true :=
        Subgroup.mem_map.mpr ⟨w0, AE.mem_kQ.mpr hk, rfl⟩
      rw [hφw, ← hw0]
      exact Subgroup.mem_map.mpr ⟨_, hmemK, rfl⟩
    · refine Subgroup.mem_sup_right ?_
      have hmemK : AE.embed (AE.emb α hαcard) w0 ∈ AE.memAt α hαcard false :=
        Subgroup.mem_map.mpr ⟨w0, AE.mem_kQStar.mpr hk, rfl⟩
      rw [hφw, ← hw0]
      exact Subgroup.mem_map.mpr ⟨_, hmemK, rfl⟩
  have hi_mem := key i hQ8.sq_i hsi1 hsa hsb
  have hj_mem := key j hQ8.sq_j hsj1 hta htb
  have hzT : AE.zBar α hαcard ∈ AE.memBar α hαcard true ⊔ AE.memBar α hαcard false :=
    Subgroup.mem_sup_left (AE.zBar_mem_memBar α hαcard true)
  have hXle : K.map φ ≤ AE.memBar α hαcard true ⊔ AE.memBar α hαcard false := by
    rintro _ ⟨k, hk, rfl⟩
    rcases hQ8.nf k hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [map_one]
      exact one_mem _
    · rw [hφz']
      exact hzT
    · exact hi_mem
    · rw [map_mul, hφz']
      exact mul_mem hzT hi_mem
    · exact hj_mem
    · rw [map_mul, hφz']
      exact mul_mem hzT hj_mem
    · rw [map_mul]
      exact mul_mem hi_mem hj_mem
    · rw [map_mul, map_mul, hφz']
      exact mul_mem hzT (mul_mem hi_mem hj_mem)
  have hXcard : Nat.card (K.map φ) = 8 := by
    rw [Subgroup.card_map_of_injective hφinj]
    exact h.card_eq_eight s.mem
  have hXw : IsUniqueInvolution (K.map φ) (AE.zBar α hαcard) := by
    refine ⟨Subgroup.mem_map.mpr ⟨z, hK.mem, hφz'⟩, AE.zBar_ne_one (by norm_num) α hαcard,
      AE.zBar_mul_self α hαcard, ?_⟩
    rintro y hy hyy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hkk : k * k = 1 := by
      apply hφinj
      rw [map_mul, hyy, map_one]
    rcases hK.unique k hk hkk with h1 | h1
    · left
      rw [h1, map_one]
    · right
      rw [h1, hφz']
  rcases eq_memBar_of_le_sup_memBar (by norm_num) hXle hXcard hXw with h1 | h1
  · exact ⟨α, hαcard, true, h1⟩
  · exact ⟨α, hαcard, false, h1⟩


theorem nonempty_aeRecog_six_of_complement (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K') (hQ : pCore 2 G = zGroup Ω)
    (hcompl : ∃ H : Subgroup G, (zGroup Ω).IsComplement' H) : Nonempty (AERecog Ω 6) := by
  obtain ⟨H, hH⟩ := hcompl
  obtain ⟨σ, β, -, -, hsp, -⟩ := h.exists_sixPoint h9 s h13 hE
  have hcen : Subgroup.centralizer (zGroup Ω : Set G) = zGroup Ω := by
    rw [centralizer_zGroup_eq_pCore h h9 s h13, hQ]
  have hD_ker : ∀ g : G, σ g = 1 → g ∈ zGroup Ω := fun g hg => by
    have hg' := (hsp.ker g).mp hg
    rwa [hcen] at hg'
  have hσD : ∀ d ∈ zGroup Ω, σ d = 1 := fun d hd =>
    (hsp.ker d).mpr (Subgroup.mem_centralizer_iff.mpr fun a ha => h.zGroup_comm h9 a ha d hd)
  have hinj : Function.Injective (σ.comp H.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxD : (x : G) ∈ zGroup Ω := hD_ker x hx
    have hbot : zGroup Ω ⊓ H = ⊥ := disjoint_iff.mp hH.disjoint
    have hmem : (x : G) ∈ zGroup Ω ⊓ H := ⟨hxD, x.2⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  set σH : H →* Equiv.Perm (Fin 6) := σ.comp H.subtype with hσH
  have halt : σH.range = alternatingGroup (Fin 6) := by
    rw [← hsp.range]
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      exact ⟨(x : G), rfl⟩
    · rintro y ⟨g, rfl⟩
      obtain ⟨⟨⟨d, hd⟩, ⟨x, hx⟩⟩, hdx, -⟩ := hH.existsUnique g
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only at hdx
      rw [← hdx, map_mul, hσD d hd, one_mul]
      rfl
  have hsplit : AESplitHyp (zGroup Ω) H σH β :=
    { compl := hH
      inj := hinj
      mem_iff := hsp.mem_iff
      eq_one_iff := hsp.eq_one_iff
      conj := fun x f hf => hsp.conj (x : G) f hf }
  obtain ⟨φ, hφβ, hφH⟩ := hsplit.exists_hom_apply
  obtain ⟨α, hα, b, hK⟩ := map_eq_memBar_six h h9 s h13 hE hsp hsplit φ hφβ hφH
  exact ⟨⟨zGroup Ω, H, σH, β, hsplit, halt, K, s.mem, α, hα, b, φ, hφβ, hφH, hK⟩⟩

theorem exists_aeRecog_six_of_local (h : EndHyp Ω) (h9 : Perp9 Ω) (s : TwinSit Ω K K' z)
    (h13 : zGroup Ω ≠ eGroup Ω K) (hE : eGroup Ω K ≤ K ⊔ K')
    (hD16 : Nat.card (zGroup Ω) = 16) (hQ : pCore 2 G = zGroup Ω) :
    Nonempty (AERecog Ω 6) :=
  h.nonempty_aeRecog_six_of_complement h9 s h13 hE hQ
    (h.exists_complement_zGroup h9 s h13 hE hD16 hQ)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
