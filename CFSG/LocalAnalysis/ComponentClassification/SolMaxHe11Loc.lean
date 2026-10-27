module

public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.SolMax.He11

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem eq_top_of_factorial_index_lt {D : Type*} [Group D] [Finite D] (hD : IsQuasisimple D)
    (H : Subgroup D) (h : H.index.factorial * Nat.card (center D) < Nat.card D) : H = ⊤ := by
  rcases LocalCores.quasisimple_normal_subgroups hD H.normalCore_normal with h1 | h1
  · exact top_le_iff.mp (h1 ▸ H.normalCore_le)
  · exfalso
    have h3 : Nat.card H.normalCore ≤ Nat.card (center D) := Subgroup.card_le_of_le h1
    have h4 : H.normalCore.index ≤ H.index.factorial :=
      Nat.le_of_dvd (Nat.factorial_pos _) H.index_normalCore_dvd_factorial_index
    have h5 : Nat.card D < Nat.card D :=
      calc Nat.card D = Nat.card H.normalCore * H.normalCore.index :=
            H.normalCore.card_mul_index.symm
        _ ≤ Nat.card (center D) * H.index.factorial := Nat.mul_le_mul h3 h4
        _ = H.index.factorial * Nat.card (center D) := mul_comm _ _
        _ < Nat.card D := h
    exact lt_irrefl _ h5

theorem eq_heOuterD_of_perfect
    {L : Subgroup (Equiv.Perm (Fin 8330))} (hLC : L ≤ heOuterC) (hLp : ⁅L, L⁆ = L)
    (h2520 : 2520 ∣ Nat.card L) : L = heOuterD := by
  obtain ⟨hDC, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hLD : L ≤ heOuterD := by
    rw [hDC, ← hLp]
    exact commutator_mono hLC hLC
  have hcard : Nat.card (L.subgroupOf heOuterD) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hLD).toEquiv
  have hidx : Nat.card L * (L.subgroupOf heOuterD).index = 7560 := by
    rw [← hcard, card_mul_index, card_heOuterD]
  obtain ⟨k, hk⟩ := h2520
  have hik : (L.subgroupOf heOuterD).index * k = 3 := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2520)
    calc 2520 * ((L.subgroupOf heOuterD).index * k) =
        Nat.card L * (L.subgroupOf heOuterD).index := by rw [hk]; ring
      _ = 2520 * 3 := by rw [hidx]
  have hi3 : (L.subgroupOf heOuterD).index ≤ 3 := Nat.le_of_dvd (by norm_num) ⟨k, hik.symm⟩
  have hf : (L.subgroupOf heOuterD).index.factorial ≤ 6 := Nat.factorial_le hi3
  have htop := eq_top_of_factorial_index_lt hq (L.subgroupOf heOuterD) (by
    rw [card_center_heOuterD, card_heOuterD]
    omega)
  exact le_antisymm hLD (subgroupOf_eq_top.mp htop)

theorem mem_heOuterD_of_commute
    {z : Equiv.Perm (Fin 8330)} (hz : z ∈ heOuterC)
    (hzD : ∀ d ∈ heOuterD, z * d = d * z) : z ∈ heOuterD ∧ z ^ 3 = 1 := by
  have hcube : ∀ w ∈ heOuterD, (∀ d ∈ heOuterD, w * d = d * w) → w ^ 3 = 1 := by
    intro w hw hwD
    have hwZ : (⟨w, hw⟩ : heOuterD) ∈ center heOuterD :=
      mem_center_iff.mpr fun g => Subtype.ext (hwD g g.2).symm
    have h1 := orderOf_dvd_natCard (⟨⟨w, hw⟩, hwZ⟩ : center heOuterD)
    rw [card_center_heOuterD, Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  by_cases hzD' : z ∈ heOuterD
  · exact ⟨hzD', hcube z hzD' hzD⟩
  exfalso
  have hz2 : z * z ∈ heOuterD :=
    Subgroup.mul_self_mem_of_index_two (H := heOuterD.subgroupOf heOuterC) heOuterD_relIndex
      (⟨z, hz⟩ : heOuterC)
  have hz6 : (z * z) ^ 3 = 1 := hcube _ hz2 fun d hd => by
    calc z * z * d = z * (z * d) := mul_assoc _ _ _
      _ = z * (d * z) := by rw [hzD d hd]
      _ = z * d * z := (mul_assoc _ _ _).symm
      _ = d * z * z := by rw [hzD d hd]
      _ = d * (z * z) := mul_assoc _ _ _
  obtain ⟨y, hy⟩ : ∃ y, y = z ^ 3 := ⟨_, rfl⟩
  have hyD : y ∉ heOuterD := by
    intro hyD
    apply hzD'
    have h1 : z = y * (z * z)⁻¹ := by rw [hy]; group
    rw [h1]
    exact mul_mem hyD (inv_mem hz2)
  have hy2 : y ^ 2 = 1 := by
    rw [hy, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, sq]
    exact hz6
  have hy1 : y ≠ 1 := fun h => hyD (h ▸ one_mem _)
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hCP : heOuterC ≤ heP := heOuterC_le_centralizer.trans inf_le_left
  have hyP : y ∈ heP := by
    rw [hy]
    exact hCP (pow_mem hz 3)
  have hDy : heOuterD ≤ heP ⊓ centralizer {y} := fun d hd =>
    mem_inf.mpr ⟨hCP (heOuterD_le_C hd), mem_centralizer_singleton_iff.mpr (by
      rw [hy]
      exact ((Commute.pow_left (show Commute z d from hzD d hd) 3).eq).symm)⟩
  have hdvd : 7560 ∣ Nat.card (heP ⊓ centralizer {y} : Subgroup (Equiv.Perm (Fin 8330))) := by
    rw [← card_heOuterD]
    exact card_dvd_of_le hDy
  rcases involution_conj_cases hyP hyo with ⟨c, hc, hyc⟩ | ⟨c, hc, hyc⟩
  · rw [hyc, Nat.card_congr (infCentralizerConjEquiv hc (heGenPerm 0)).toEquiv] at hdvd
    have h0 : Nat.card (heP ⊓ centralizer {heGenPerm 0} : Subgroup (Equiv.Perm (Fin 8330))) =
        161280 := card_heP_cent0
    rw [h0] at hdvd
    norm_num at hdvd
  · rw [hyc, Nat.card_congr (infCentralizerConjEquiv hc heT1P).toEquiv] at hdvd
    have h1 : Nat.card (heP ⊓ centralizer {heT1P} : Subgroup (Equiv.Perm (Fin 8330))) = 21504 :=
      card_heP_cent1
    rw [h1] at hdvd
    norm_num at hdvd

theorem commute_of_odd_normal
    {N : Subgroup (Equiv.Perm (Fin 8330))} (hND : N ≤ heOuterD)
    (hNn : ∀ d ∈ heOuterD, ∀ n ∈ N, d * n * d⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    ∀ n ∈ N, ∀ d ∈ heOuterD, n * d = d * n := by
  obtain ⟨-, hq, -⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hn : (N.subgroupOf heOuterD).Normal := ⟨fun n hn g => hNn g g.2 n hn⟩
  rcases LocalCores.quasisimple_normal_subgroups hq hn with h | h
  · exfalso
    have h1 : Nat.card heOuterD ∣ Nat.card N := card_dvd_of_le (subgroupOf_eq_top.mp h)
    rw [card_heOuterD] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 7560).trans h1))
  · intro n hn d hd
    have h1 := mem_center_iff.mp
      (h (show (⟨n, hND hn⟩ : heOuterD) ∈ N.subgroupOf heOuterD from hn)) ⟨d, hd⟩
    exact (congrArg Subtype.val h1).symm

theorem commute_of_perfect {G : Type*} [Group G] {D : Subgroup G} (hD : ⁅D, D⁆ = D) {z : G}
    (hz : ∀ d ∈ D, d⁻¹ * (z * d * z⁻¹) ∈ D ∧
      ∀ e ∈ D, d⁻¹ * (z * d * z⁻¹) * e = e * (d⁻¹ * (z * d * z⁻¹))) :
    ∀ d ∈ D, z * d = d * z := by
  have hle : ⁅D, D⁆ ≤ centralizer {z} := by
    rw [commutator_le]
    intro a ha b hb
    rw [mem_centralizer_singleton_iff]
    obtain ⟨hna, hca⟩ := hz a ha
    obtain ⟨-, hcb⟩ := hz b hb
    obtain ⟨na, hnadef⟩ : ∃ na, na = a⁻¹ * (z * a * z⁻¹) := ⟨_, rfl⟩
    obtain ⟨nb, hnbdef⟩ : ∃ nb, nb = b⁻¹ * (z * b * z⁻¹) := ⟨_, rfl⟩
    rw [← hnadef] at hna hca
    rw [← hnbdef] at hcb
    have hza : z * a * z⁻¹ = a * na := by rw [hnadef]; group
    have hzb : z * b * z⁻¹ = b * nb := by rw [hnbdef]; group
    have c1 : na * b = b * na := hca b hb
    have c2 : nb * na⁻¹ = na⁻¹ * nb :=
      ((show Commute nb na from hcb na hna).inv_right).eq
    have c3 : nb * a⁻¹ = a⁻¹ * nb := ((show Commute nb a from hcb a ha).inv_right).eq
    have key : z * ⁅a, b⁆ * z⁻¹ = ⁅a, b⁆ := by
      calc z * ⁅a, b⁆ * z⁻¹ =
          z * a * z⁻¹ * (z * b * z⁻¹) * (z * a * z⁻¹)⁻¹ * (z * b * z⁻¹)⁻¹ := by
            rw [commutatorElement_def]; group
        _ = a * na * (b * nb) * (a * na)⁻¹ * (b * nb)⁻¹ := by rw [hza, hzb]
        _ = a * (na * b) * (nb * na⁻¹) * a⁻¹ * nb⁻¹ * b⁻¹ := by group
        _ = a * (b * na) * (na⁻¹ * nb) * a⁻¹ * nb⁻¹ * b⁻¹ := by rw [c1, c2]
        _ = a * b * (nb * a⁻¹) * nb⁻¹ * b⁻¹ := by group
        _ = a * b * (a⁻¹ * nb) * nb⁻¹ * b⁻¹ := by rw [c3]
        _ = ⁅a, b⁆ := by rw [commutatorElement_def]; group
    calc ⁅a, b⁆ * z = z * ⁅a, b⁆ * z⁻¹ * z := by rw [key]
      _ = z * ⁅a, b⁆ := by group
  intro d hd
  rw [← hD] at hd
  exact (mem_centralizer_singleton_iff.mp (hle hd)).symm

theorem cube_of_commute
    {z : Equiv.Perm (Fin 8330)} (hzR : z ∈ heAutGroup)
    (hzu : z * heAutU = heAutU * z) (hzD : ∀ d ∈ heOuterD, z * d = d * z) :
    (z ∈ heP → z ∈ heOuterD ∧ z ^ 3 = 1) ∧
      (z ∉ heP → z * heAutU ∈ heOuterD ∧ (z * heAutU) ^ 3 = 1) := by
  have hC : ∀ w ∈ heP, w * heAutU = heAutU * w → w ∈ heOuterC := fun w hw hwu => by
    rw [heOuterC_eq]
    exact mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr hwu⟩
  refine ⟨fun hzP => mem_heOuterD_of_commute (hC z hzP hzu) hzD, fun hzP => ?_⟩
  have h1 : heAutU * z ∈ heP := heAutU_mul_mem_of_outer hzR hzP
  rw [← hzu] at h1
  have huD : ∀ d ∈ heOuterD, heAutU * d = d * heAutU := fun d hd =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (heOuterC_le_centralizer
      (heOuterD_le_C hd))).2).symm
  refine mem_heOuterD_of_commute (hC _ h1 ?_) fun d hd => ?_
  · calc z * heAutU * heAutU = heAutU * z * heAutU := by rw [hzu]
      _ = heAutU * (z * heAutU) := mul_assoc _ _ _
  · calc z * heAutU * d = z * (heAutU * d) := mul_assoc _ _ _
      _ = z * (d * heAutU) := by rw [huD d hd]
      _ = z * d * heAutU := (mul_assoc _ _ _).symm
      _ = d * z * heAutU := by rw [hzD d hd]
      _ = d * (z * heAutU) := mul_assoc _ _ _

end CFSG.ComponentClassification.SolMax.He11
