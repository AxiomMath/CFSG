module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_15Abs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L20

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section J

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z y : G}

theorem Abs15.four_lt (a : Abs15 H z y) {V : Subgroup G} (hV : IsSylowOf 2 V H) (hzV : z ∈ V) (hyV : y ∈ V)
    (hC : ∀ x ∈ V, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) : 4 < Nat.card V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h4
  push Not at h4
  have hVp : IsPGroup 2 V := hV.isPGroup
  have hu1 : y * z ≠ 1 := by
    intro h1
    apply a.hne
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right a.hz2).symm ▸ rfl
  have hJp := Em_perfect H
  have hOpN : ∀ h ∈ H, ∀ n ∈ Op 2 H, h * n * h⁻¹ ∈ Op 2 H := fun h hh n hn =>
    Op_conj_mem 2 (fun c hc b hb => H.mul_mem (H.mul_mem hc hb) (H.inv_mem hc)) hh hn
  have hOpH : Op 2 H ≤ H := Subgroup.map_subtype_le _
  have hQV : Q4 z y a.hz2 a.hy2 a.hzy ≤ V := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact V.one_mem
    · exact hzV
    · exact hyV
    · exact V.mul_mem hyV hzV
  have hcardQ := card_Q4 a.hz2 a.hy2 a.hzy a.hz1 a.hy1 a.hne
  have hVeq : Q4 z y a.hz2 a.hy2 a.hzy = V := Subgroup.eq_of_le_of_card_ge hQV (by omega)
  have hVmem : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = y ∨ x = y * z := fun x hx => by
    rw [← hVeq] at hx; exact hx
  have hucomm : ∀ x ∈ V, x * (y * z) = (y * z) * x := by
    intro x hx
    rcases hVmem x hx with rfl | rfl | rfl | rfl
    · simp
    · rw [zyz_eq a.hz2 a.hzy, yzz_eq a.hz2]
    · rw [yyz_eq a.hy2, yzy_eq a.hy2 a.hzy]
    · rfl
  have hN2 : ∀ w ∈ Op 2 H, (y * z) * w = w * (y * z) := fun w hw =>
    (hucomm w (normal_le_sylow hV hOpH hOpN (isPGroup_Op 2 H) hw)).symm
  have hJ1 : Em H ≠ ⊥ := a.em_ne_bot hN2
  have hPJ := sylow_inf_Em hV
  have heven := even_card_of_perfect hJp hJ1
  have hP1 : V ⊓ Em H ≠ ⊥ := ne_bot_of_isSylowOf_even hPJ heven
  by_cases hVJ : V ≤ Em H
  · have hzJ : z ∈ Em H := hVJ hzV
    have huJ : y * z ∈ Em H := hVJ (V.mul_mem hyV hzV)
    exact a.not_mem_of_sc hV hzV hC huJ hzJ
  ·
    set P := V ⊓ Em H with hP
    have hPV : P < V := lt_of_le_of_ne inf_le_left (fun h => hVJ (h ▸ inf_le_right))
    have hcardP : Nat.card P = 2 := by
      have h1 : Nat.card P ∣ Nat.card V := Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card P < Nat.card V := Subgroup.card_lt_of_lt hPV
      have h3 : Nat.card P ≠ 1 := fun h => hP1 (Subgroup.card_eq_one.mp h)
      have h4' : Nat.card V = 4 := by
        have : Nat.card (Q4 z y a.hz2 a.hy2 a.hzy) = Nat.card V := by rw [hVeq]
        omega
      rw [h4'] at h1 h2
      have hpos : 0 < Nat.card P := Nat.card_pos
      interval_cases hc : Nat.card P
      · exact absurd rfl h3
      · rfl
      · exact absurd h1 (by norm_num)
    have hPcyc : IsCyclic ↥P := isCyclic_of_prime_card (p := 2) hcardP
    obtain ⟨w, hwP, hw2, hw1⟩ := exists_involution_of_ne_bot (hVp.to_le (inf_le_left : P ≤ V)) hP1
    have hwJ : w ∈ Em H := hwP.2
    have hperf : commutator ↥(Em H) = ⊤ := by
      have : Group.IsPerfect ↥(Em H) := Subgroup.isPerfect_iff.mpr hJp
      exact this.commutator_eq_top
    obtain ⟨Q, hQ⟩ := hPJ.exists_sylow_eq_subgroupOf
    have hPJle : P ≤ Em H := inf_le_right
    have hQcyc : IsCyclic ↥(Q : Subgroup ↥(Em H)) := by
      have h1 : IsCyclic ↥(P.subgroupOf (Em H)) :=
        isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPJle).symm
          (Subgroup.subgroupOfEquivOfLe hPJle).symm.surjective
      exact isCyclic_of_surjective (MulEquiv.subgroupCongr hQ.symm)
        (MulEquiv.subgroupCongr hQ.symm).surjective
    refine not_cyclic_sylow_of_perfect hperf Q hQcyc (t := ⟨w, hwJ⟩) (fun h => hw1 (congrArg Subtype.val h))
      ?_ (Subtype.ext hw2)
    rw [hQ]
    exact hwP

theorem Abs15.single_class (a : Abs15 H z y) {V : Subgroup G} (hV : IsSylowOf 2 V H) (hzV : z ∈ V)
    (hC : ∀ x ∈ V, z * x = x * z → x = 1 ∨ x = z ∨ x = y ∨ x = y * z) :
    ∀ a' ∈ Em H, ∀ b' ∈ Em H, a' * a' = 1 → b' * b' = 1 → a' ≠ 1 → b' ≠ 1 →
      ∃ c ∈ Em H, c * a' * c⁻¹ = b' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro a' ha' b' hb' ha2 hb2 ha1 hb1
  have hVp : IsPGroup 2 V := hV.isPGroup
  have hPJ := sylow_inf_Em hV
  obtain ⟨MV, hMVc, hMVrel⟩ : ∃ M : Subgroup G, IsCyclic M ∧ M.relIndex V ≤ 2 := by
    obtain ⟨M, -, h1, h2⟩ := exists_cyclic_relIndex_le_two hVp hzV a.hz2 a.hz1 hC
    exact ⟨M, h1, h2⟩
  set P := V ⊓ Em H with hP
  set M := MV ⊓ P with hM
  have hMc : IsCyclic ↥M := isCyclic_inf_left hMVc
  have hMP : M ≤ P := inf_le_right
  have hPV : P ≤ V := inf_le_left
  have hPJ' : P ≤ Em H := inf_le_right
  have hMrel : M.relIndex P ≤ 2 := by
    have h1 : M.relIndex P = MV.relIndex P := Subgroup.inf_relIndex_right MV P
    have h2 : MV.relIndex P ≤ MV.relIndex V := by
      have : MV.IsFiniteRelIndex V := Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
      exact Subgroup.relIndex_le_of_le_right hPV Subgroup.relIndex_ne_zero
    omega
  have hperf : commutator ↥(Em H) = ⊤ := by
    have : Group.IsPerfect ↥(Em H) := Subgroup.isPerfect_iff.mpr (Em_perfect H)
    exact this.commutator_eq_top
  have hMJ : M ≤ Em H := hMP.trans hPJ'
  have hSc := single_class_of_perfect (X := ↥(Em H)) hperf (P := P.subgroupOf (Em H)) (M := M.subgroupOf (Em H))
    (((isSylowOf_iff.mp hPJ).2.1).comap_subtype) (isSylowOf_iff.mp hPJ).2.2
    (Subgroup.subgroupOf_mono (Em H) hMP) (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hMJ).symm
      (Subgroup.subgroupOfEquivOfLe hMJ).symm.surjective)
    (by rw [Subgroup.relIndex_subgroupOf hPJ']; exact hMrel)
    (a := ⟨a', ha'⟩) (b := ⟨b', hb'⟩) (Subtype.ext ha2) (Subtype.ext hb2)
    (fun h => ha1 (congrArg Subtype.val h)) (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨c, hc⟩ := isConj_iff.mp hSc
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

theorem Abs15.jside (a : Abs15 H z y) (huJ : y * z ∈ Em H) :
    (∀ a' ∈ Em H, ∀ b' ∈ Em H, a' * a' = 1 → b' * b' = 1 → a' ≠ 1 → b' ≠ 1 →
      ∃ c ∈ Em H, c * a' * c⁻¹ = b') ∧
    ∃ v ∈ Em H, v * v = 1 ∧ v ≠ 1 ∧ v ≠ y * z ∧ (y * z) * v = v * (y * z) := by
  obtain ⟨V, hV, hzV, hyV, hC⟩ := a.exists_sylow
  have h4 := a.four_lt hV hzV hyV hC
  refine ⟨a.single_class hV hzV hC, ?_⟩
  obtain ⟨huniq, -⟩ := a.big_case hV hzV hyV hC h4
  have hVp : IsPGroup 2 V := hV.isPGroup
  obtain ⟨w, hwV, hwc, hw2, hw1⟩ := exists_central_involution hVp (by omega : 1 < Nat.card V)
  have hwu := huniq w hwV hwc hw2 hw1
  have hucen : ∀ v ∈ V, v * (y * z) = (y * z) * v := hwu ▸ hwc
  have hu1 : y * z ≠ 1 := by
    intro h1
    apply a.hne
    have : y = z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact (inv_eq_of_mul_eq_one_right a.hz2).symm ▸ rfl
  have hu2 : (y * z) * (y * z) = 1 := yzyz_eq a.hz2 a.hy2 a.hzy
  by_contra hno'
  push Not at hno'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact no_unique_involution (H := H) (J := Em H) (Em_le H) (fun h hh j hj => Em_conj_mem hh hj) (Em_perfect H)
    (Em_comm_pPrimeCore H) huJ hu2 hu1 a.hO (P := V ⊓ Em H) inf_le_right ⟨V.mul_mem hyV hzV, huJ⟩
    hVp.to_inf_left (isSylowOf_iff.mp (sylow_inf_Em hV)).2.2
    (fun s hs hs1 hs2 => by
      by_contra hsu
      exact hno' s hs.2 hs2 hs1 hsu (hucen s hs.1).symm)

end J

end CFSG.GH74.GLS.Stage2.Final.Thm6.L20
