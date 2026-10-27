module

public import Certificates.Certificate55110
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.Sporadic.Schreier

namespace MF163

theorem m12_quat_check : m12QuatCheck = true :=
  Certificates.certificate55110.1

theorem m12_noRoot2_check : m12NoRoot2Check = true :=
  Certificates.certificate55110.2

theorem mem_enum1
    {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hc : g * m12Rep1 = m12Rep1 * g) : g ∈ enumerationTab m12CentQ1 := by
  have h : centralizerIn m12Certificate.originalSubgroup m12Rep1 = m12CentQ1.originalSubgroup :=
    m12_cover_and_centralizers.2 (m12Rep1, m12CentQ1.originalSubgroup) (by simp)
  rw [mem_enumerationTab_iff m12CentQ1 m12_oddcore_cent1.1, ← h, mem_centralizerIn,
    m12Certificate_originalSubgroup]
  exact ⟨hg, hc⟩

theorem mem_enum2
    {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hc : g * m12Rep2 = m12Rep2 * g) : g ∈ enumerationTab m12CentQ2 := by
  have h : centralizerIn m12Certificate.originalSubgroup m12Rep2 = m12CentQ2.originalSubgroup :=
    m12_cover_and_centralizers.2 (m12Rep2, m12CentQ2.originalSubgroup) (by simp)
  rw [mem_enumerationTab_iff m12CentQ2 m12_oddcore_cent2.1, ← h, mem_centralizerIn,
    m12Certificate_originalSubgroup]
  exact ⟨hg, hc⟩

theorem mul_self_ne_rep2
    {x : Equiv.Perm (Fin 12)}
    (hx : x ∈ NativeSporadic.M12) : x * x ≠ m12Rep2 := by
  intro h
  have hc : x * m12Rep2 = m12Rep2 * x := by rw [← h, mul_assoc]
  have h1 := List.all_eq_true.1 m12_noRoot2_check x (mem_enum2 hx hc)
  simp [h] at h1

theorem exists_conj_rep1
    {u x : Equiv.Perm (Fin 12)}
    (hu : u ∈ NativeSporadic.M12) (ho : orderOf u = 2) (hx : x ∈ NativeSporadic.M12)
    (hxu : x * x = u) : ∃ c ∈ NativeSporadic.M12, u = c * m12Rep1 * c⁻¹ := by
  have hu' : (1 : Equiv.Perm (Fin 12))⁻¹ * u ∈ m12Certificate.originalSubgroup := by
    rwa [inv_one, one_mul, m12Certificate_originalSubgroup]
  obtain ⟨d, hd, c, hc, hud⟩ := m12_cover_and_centralizers.1 u hu' ho
  rw [m12Certificate_originalSubgroup] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨c, hc, hud⟩
  · refine absurd ?_ (mul_self_ne_rep2 (x := c⁻¹ * x * c) (mul_mem (mul_mem (inv_mem hc) hx) hc))
    dsimp only at hud
    calc c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c := by group
      _ = m12Rep2 := by rw [hxu, hud]; group

theorem eq_of_comm_roots1
    {g x y : Equiv.Perm (Fin 12)}
    (hg : g ∈ NativeSporadic.M12) (hx : x ∈ NativeSporadic.M12) (hy : y ∈ NativeSporadic.M12)
    (hx2 : x * x = m12Rep1) (hy2 : y * y = m12Rep1) (hxy : x * y ≠ y * x)
    (hgx : g * x = x * g) (hgy : g * y = y * g) (h23 : g * g = 1 ∨ g * g * g = 1) :
    g = 1 ∨ g = m12Rep1 := by
  have hxR : x ∈ m12SqRoots1 :=
    List.mem_filter.2 ⟨mem_enum1 hx (by rw [← hx2, mul_assoc]), by simpa using hx2⟩
  have hyR : y ∈ m12SqRoots1 :=
    List.mem_filter.2 ⟨mem_enum1 hy (by rw [← hy2, mul_assoc]), by simpa using hy2⟩
  have hgc : g * m12Rep1 = m12Rep1 * g := by
    rw [← hx2]
    calc g * (x * x) = g * x * x := (mul_assoc _ _ _).symm
      _ = x * g * x := by rw [hgx]
      _ = x * (g * x) := mul_assoc _ _ _
      _ = x * (x * g) := by rw [hgx]
      _ = x * x * g := (mul_assoc _ _ _).symm
  have h := List.all_eq_true.1 m12_quat_check g (mem_enum1 hg hgc)
  simp only [Bool.or_eq_true] at h
  rcases h with ((hA | hC) | hD) | hE
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hA
    rcases h23 with h | h
    · exact absurd h hA.1
    · exact absurd h hA.2
  · exact Or.inl (of_decide_eq_true hC)
  · exact Or.inr (of_decide_eq_true hD)
  · have h1 := List.all_eq_true.1 (List.all_eq_true.1 hE x hxR) y hyR
    simp [hgx, hgy, hxy] at h1

theorem exists_conj_rep1_quat
    (ι : QuaternionGroup 2 →* NativeSporadic.M12) (hι : Function.Injective ι) :
    ∃ c ∈ NativeSporadic.M12,
      (ι (QuaternionGroup.a 2) : Equiv.Perm (Fin 12)) = c * m12Rep1 * c⁻¹ := by
  have hu2 : orderOf (ι (QuaternionGroup.a 2) : Equiv.Perm (Fin 12)) = 2 := by
    rw [Subgroup.orderOf_coe, orderOf_injective ι hι]
    exact orderOf_eq_prime (by decide) (by decide)
  refine exists_conj_rep1 (ι _).2 hu2 (ι (QuaternionGroup.a 1)).2 ?_
  rw [← Subgroup.coe_mul, ← map_mul,
    show QuaternionGroup.a 1 * QuaternionGroup.a 1 = (QuaternionGroup.a 2 : QuaternionGroup 2) by
      decide]

theorem eq_of_comm_quat
    (ι : QuaternionGroup 2 →* NativeSporadic.M12) (hι : Function.Injective ι)
    {m : NativeSporadic.M12} (hm : ∀ q, m * ι q = ι q * m) (h23 : m * m = 1 ∨ m * m * m = 1) :
    m = 1 ∨ m = ι (QuaternionGroup.a 2) := by
  have hsq : ∀ q : QuaternionGroup 2, q * q = QuaternionGroup.a 2 →
      (ι q : Equiv.Perm (Fin 12)) * ι q = ι (QuaternionGroup.a 2) := fun q hq => by
    rw [← Subgroup.coe_mul, ← map_mul, hq]
  obtain ⟨c, hc, huc⟩ := exists_conj_rep1_quat ι hι
  let κ : Equiv.Perm (Fin 12) → Equiv.Perm (Fin 12) := fun g => c⁻¹ * g * c
  have hκmul : ∀ g h, κ (g * h) = κ g * κ h := fun g h => by simp only [κ]; group
  have hκmem : ∀ g ∈ NativeSporadic.M12, κ g ∈ NativeSporadic.M12 := fun g hg =>
    mul_mem (mul_mem (inv_mem hc) hg) hc
  have hκinj : Function.Injective κ := fun g h hgh => by simpa [κ] using hgh
  have hκu : κ (ι (QuaternionGroup.a 2)) = m12Rep1 := by simp only [κ]; rw [huc]; group
  have hx2 : κ (ι (QuaternionGroup.a 1)) * κ (ι (QuaternionGroup.a 1)) = m12Rep1 := by
    rw [← hκmul, hsq _ (by decide), hκu]
  have hy2 : κ (ι (QuaternionGroup.xa 0)) * κ (ι (QuaternionGroup.xa 0)) = m12Rep1 := by
    rw [← hκmul, hsq _ (by decide), hκu]
  have hxy : κ (ι (QuaternionGroup.a 1)) * κ (ι (QuaternionGroup.xa 0)) ≠
      κ (ι (QuaternionGroup.xa 0)) * κ (ι (QuaternionGroup.a 1)) := by
    rw [← hκmul, ← hκmul]
    intro h
    have h1 := hκinj h
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul] at h1
    exact absurd (hι (Subtype.ext h1)) (by decide)
  have hcomm : ∀ q, κ m * κ (ι q) = κ (ι q) * κ m := fun q => by
    rw [← hκmul, ← hκmul, ← Subgroup.coe_mul, hm q, Subgroup.coe_mul]
  have h23' : κ m * κ m = 1 ∨ κ m * κ m * κ m = 1 := by
    rcases h23 with h | h
    · left
      rw [← hκmul, ← Subgroup.coe_mul, h]
      simp [κ]
    · right
      rw [← hκmul, ← hκmul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, h]
      simp [κ]
  rcases eq_of_comm_roots1 (hκmem _ m.2) (hκmem _ (ι _).2) (hκmem _ (ι _).2) hx2 hy2 hxy
    (hcomm _) (hcomm _) h23' with h | h
  · left
    apply Subtype.ext
    apply hκinj
    rw [h]
    simp [κ]
  · right
    apply Subtype.ext
    apply hκinj
    rw [h, hκu]

theorem exists_three_not_comm
    (ι : QuaternionGroup 2 →* NativeSporadic.M12) (hι : Function.Injective ι) :
    ∃ m : NativeSporadic.M12, m * ι (QuaternionGroup.a 2) = ι (QuaternionGroup.a 2) * m ∧
      orderOf m = 3 ∧ ∃ q, m * ι q ≠ ι q * m := by
  obtain ⟨c, hc, huc⟩ := exists_conj_rep1_quat ι hι
  have hcard : Nat.card (centralizerIn m12Certificate.originalSubgroup m12Rep1) = 192 := by
    rw [m12_cover_and_centralizers.2 (m12Rep1, m12CentQ1.originalSubgroup) (by simp)]
    exact m12_rep_data1.2.2.2.1
  obtain ⟨g, hg3⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizerIn m12Certificate.originalSubgroup m12Rep1) 3 (by rw [hcard]; norm_num)
  obtain ⟨hgM, hgr⟩ := mem_centralizerIn.1 g.2
  let m : NativeSporadic.M12 :=
    ⟨c * g * c⁻¹, mul_mem (mul_mem hc (m12Certificate_originalSubgroup.le hgM)) (inv_mem hc)⟩
  have hm3 : orderOf m = 3 := by
    rw [← Subgroup.orderOf_coe, ← hg3, ← Subgroup.orderOf_coe g]
    show orderOf (c * (g : Equiv.Perm (Fin 12)) * c⁻¹) = _
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  refine ⟨m, Subtype.ext ?_, hm3, ?_⟩
  · show c * g * c⁻¹ * (ι (QuaternionGroup.a 2) : Equiv.Perm (Fin 12)) =
      ι (QuaternionGroup.a 2) * (c * g * c⁻¹)
    rw [huc]
    calc c * g * c⁻¹ * (c * m12Rep1 * c⁻¹) = c * (g * m12Rep1) * c⁻¹ := by group
      _ = c * (m12Rep1 * g) * c⁻¹ := by rw [hgr]
      _ = c * m12Rep1 * c⁻¹ * (c * g * c⁻¹) := by group
  · by_contra hne
    have hall : ∀ q, m * ι q = ι q * m := fun q => by_contra fun h => hne ⟨q, h⟩
    have h3 : m * m * m = 1 := by rw [← pow_three', ← hm3, pow_orderOf_eq_one]
    have h2 : orderOf (QuaternionGroup.a 2 : QuaternionGroup 2) = 2 :=
      orderOf_eq_prime (by decide) (by decide)
    rcases eq_of_comm_quat ι hι hall (Or.inr h3) with h | h
    · rw [h, orderOf_one] at hm3
      exact absurd hm3 (by norm_num)
    · rw [h, orderOf_injective ι hι, h2] at hm3
      exact absurd hm3 (by norm_num)

end MF163

end CFSG.ClassicalInvolution.Q3.TL4
