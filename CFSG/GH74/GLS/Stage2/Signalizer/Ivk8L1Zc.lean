module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8L1Syl
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem exists_four_of_involutions {X : Type} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    ∃ V : Subgroup X, IVK.IsFourSubgroup V ∧ ∀ v ∈ V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have hba : b * a = a * b := hab.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have haba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have hab2 : a * b * (a * b) = 1 := by rw [← mul_assoc, haba, hb]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, hbi])
  have habA : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habB : a * b ≠ b := fun h => ha1 (by simpa using h)
  let V : Subgroup X :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
          simp [ha, hb, hba, haab, hbab, habb, haba, hab2]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rcases hx with hx | hx | hx | hx <;> rw [hx]
        · simp
        · simp [hai]
        · simp [hbi]
        · simp [mul_inv_rev, hai, hbi, hba] }
  have hV : (V : Set X) = {1, a, b, a * b} := by
    ext x
    simp [V]
  have hcard : Nat.card V = 4 := by
    have h1 : Nat.card V = (V : Set X).ncard := Nat.card_coe_set_eq (V : Set X)
    rw [h1, hV, Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
      Set.ncard_insert_of_notMem (by simp [hne, habA.symm]), Set.ncard_pair habB.symm]
  have hsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases hv with hv | hv | hv | hv <;> rw [hv]
    · simp
    · exact ha
    · exact hb
    · exact hab2
  exact ⟨V, Odd87.hat_isFourSubgroup_of_card_sq V hcard hsq, fun v hv => hv⟩

section ZC

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem zc (hfr : AFrame A zb Sb Vb) {J : Subgroup A} (hJ : IsComponent J)
    (hsw : Sb ≤ normalizer (J : Set A))
    (h4 : 4 ≤ Nat.card ↥(Sb ⊓ centralizer (J : Set A))) : False := by
  set N : Subgroup A := Sb ⊓ centralizer (J : Set A) with hN
  have hNS : N ≤ Sb := inf_le_left
  have hNn : ∀ s ∈ Sb, ∀ x ∈ N, s * x * s⁻¹ ∈ N := by
    intro s hs x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨Sb.mul_mem (Sb.mul_mem hs hxS) (Sb.inv_mem hs), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hsn : ∀ g ∈ Sb, ∀ h ∈ J, g * h * g⁻¹ ∈ J := fun g hg h hh =>
      (Subgroup.mem_normalizer_iff.mp (hsw hg) h).mp hh
    have hj' : s⁻¹ * j * s ∈ J := by
      have := hsn s⁻¹ (Sb.inv_mem hs) j hj
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hxC _ hj'
    calc j * (s * x * s⁻¹) = s * ((s⁻¹ * j * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * j * s)) * s⁻¹ := by rw [hc]
      _ = s * x * s⁻¹ * j := by group
  have hNz : ¬ N ≤ Subgroup.zpowers zb := by
    intro hle
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hfr.zb_ord] at this
    omega
  obtain ⟨w, hwN, hw2, hwz⟩ := normal_contains_involution hfr hNS hNn hNz
  have hP : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  have hw1 : w ≠ 1 := fun h => by
    rw [h, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)
  have hzbN : zb ∈ N := by
    have hnorm : (N.subgroupOf Sb).Normal := ⟨fun x hx t => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      simpa using hNn t.1 t.2 x.1 hx⟩
    have hne : N.subgroupOf Sb ≠ ⊥ := by
      intro h
      have : (⟨w, hNS hwN⟩ : ↥Sb) ∈ N.subgroupOf Sb := Subgroup.mem_subgroupOf.mpr hwN
      rw [h, Subgroup.mem_bot] at this
      exact hw1 (congrArg Subtype.val this)
    obtain ⟨u, hu, huc, hu2⟩ := Gen.exists_involution_center_of_normal hP hne
    have huz : ((u : ↥Sb) : A) = zb :=
      hfr.zcen _ u.2 (fun s hs => congrArg Subtype.val (Subgroup.mem_center_iff.mp huc ⟨s, hs⟩))
        (by rw [Subgroup.orderOf_coe]; exact hu2)
    rw [← huz]
    exact Subgroup.mem_subgroupOf.mp hu
  have hzb2 : zb * zb = 1 := by
    have := pow_orderOf_eq_one zb
    rwa [hfr.zb_ord, pow_two] at this
  have hw2' : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw2, pow_two] at this
  have hzb1 : zb ≠ 1 := fun h => by
    have h0 := hfr.zb_ord
    rw [h, orderOf_one] at h0
    exact absurd h0 (by norm_num)
  obtain ⟨V, hV, hVmem⟩ := exists_four_of_involutions hzb2 hw2'
    (zb_comm hfr w (hNS hwN)).symm hzb1 hw1 (Ne.symm hwz)
  have hNJ : ∀ x ∈ N, ∀ j ∈ J, j * x = x * j := fun x hx j hj =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 j hj
  have hJV : J ≤ centralizer (V : Set A) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases hVmem v hv with h | h | h | h <;> rw [h]
    · simp
    · exact (hNJ zb hzbN j hj).symm
    · exact (hNJ w hwN j hj).symm
    · calc zb * w * j = zb * (w * j) := by rw [mul_assoc]
        _ = zb * (j * w) := by rw [hNJ w hwN j hj]
        _ = zb * j * w := by rw [← mul_assoc]
        _ = j * zb * w := by rw [hNJ zb hzbN j hj]
        _ = j * (zb * w) := by rw [mul_assoc]
  exact hfr.false_of_comp_cent_four hV hJ hJV

theorem card_centralizer_le_two (hfr : AFrame A zb Sb Vb) {J : Subgroup A} (hJ : IsComponent J)
    (hsw : Sb ≤ normalizer (J : Set A)) : Nat.card ↥(Sb ⊓ centralizer (J : Set A)) ≤ 2 := by
  by_contra h
  have hdvd : Nat.card ↥(Sb ⊓ centralizer (J : Set A)) ∣ 2 ^ 8 := by
    rw [← hfr.card]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4 : 4 ≤ Nat.card ↥(Sb ⊓ centralizer (J : Set A)) := by
    by_cases hi2 : 2 ≤ i
    · rw [hc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi2
    · exfalso
      apply h
      rw [hc]
      interval_cases i <;> norm_num
  exact zc hfr hJ hsw h4

theorem map_conj_eq_of_mem_normalizer {X : Type} [Group X] {H : Subgroup X} {g : X}
    (hg : g ∈ normalizer (H : Set X)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) x).mp hx
    simpa using this

theorem mem_normalizer_of_map_conj_eq {X : Type} [Group X] {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := by simpa [MulAut.conj_apply] using hyx
      simpa using h1
    rw [← this]
    exact hy

end ZC

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
