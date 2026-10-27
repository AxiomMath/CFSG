module

public import CFSG.Quasithin.SteinbergBKCharTwoFrattiniAction

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG CFSG.SectionRank.Ccomm

theorem index_two_core_centralizers_no_new_involutions {H : Type*} [Group H] [Finite H]
    (hH : IsCharacteristicP 2 H)
    (hZ : ∀ z ∈ center (pCore 2 H), orderOf z = 2 → z ∈ frattini (pCore 2 H))
    {P : Subgroup H} (hPQ : P ≤ pCore 2 H) (hP2 : P.relIndex (pCore 2 H) = 2)
    {x : H} (hxP : x ∈ centralizer (P : Set H)) (hx : orderOf x = 2) : x ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCore 2 H with hQdef
  have hker : ((autQuotient (frattini Q)).comp (MulAut.conjNormal (H := Q))).ker = Q :=
    (Quasithin.SteinbergBK.characteristic_two_core_frattini_action_and_small_ranks hH).1
  set PQ := P.subgroupOf Q with hPQdef
  have hidx : PQ.index = 2 := hP2
  have hmemPQ : ∀ q : Q, q ∈ PQ ↔ (q : H) ∈ P := fun _ => mem_subgroupOf
  have hPn : PQ.Normal := normal_of_index_eq_two hidx
  have hxp : ∀ p ∈ P, x * p * x⁻¹ = p := fun p hp => by
    rw [← mem_centralizer_iff.mp hxP p hp, mul_inv_cancel_right]
  have hxp' : ∀ p ∈ P, x⁻¹ * p * x = p := fun p hp => by
    rw [mul_assoc, mem_centralizer_iff.mp hxP p hp, inv_mul_cancel_left]
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  set c := MulAut.conjNormal (H := Q) x with hc
  have hcv : ∀ q : Q, ((c q : Q) : H) = x * q * x⁻¹ := fun q => MulAut.conjNormal_apply x q
  obtain ⟨y, hyP⟩ : ∃ y : Q, y ∉ PQ := by
    by_contra h
    push Not at h
    have htop : PQ = ⊤ := eq_top_iff.mpr fun q _ => h q
    rw [htop, index_top] at hidx
    omega
  have hy' : y⁻¹ ∉ PQ := fun h => hyP (by simpa using inv_mem h)
  have hcy : c y ∉ PQ := by
    intro h
    apply hyP
    rw [hmemPQ] at h ⊢
    rw [hcv] at h
    have hy : (y : H) = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [hy, hxp' _ h]
    exact h
  set d : Q := y⁻¹ * c y with hd
  have hdP : d ∈ PQ := by
    rw [hd, mul_mem_iff_of_index_two hidx]
    exact ⟨fun h => absurd h hy', fun h => absurd h hcy⟩
  have hdP' : (d : H) ∈ P := (hmemPQ d).mp hdP
  have hcyd : c y = y * d := by rw [hd, mul_inv_cancel_left]
  have e2 : x * y * x⁻¹ = (y : H) * d := by rw [← hcv, hcyd, Subgroup.coe_mul]
  have e1 : x * (x * y * x⁻¹) * x⁻¹ = y := by
    calc x * (x * y * x⁻¹) * x⁻¹ = (x * x) * y * (x * x)⁻¹ := by group
      _ = y := by rw [hx2, one_mul, inv_one, mul_one]
  have e3 : x * ((y : H) * d) * x⁻¹ = (y * d) * d := by
    calc x * ((y : H) * d) * x⁻¹ = (x * y * x⁻¹) * (x * d * x⁻¹) := by group
      _ = (y * d) * d := by rw [e2, hxp _ hdP']
  have e4 : (y : H) * d * d = y := by rw [← e3, ← e2, e1]
  have hd2 : (d : H) * d = 1 := mul_left_cancel (a := (y : H)) (by rw [← mul_assoc, e4, mul_one])
  have hdinv : (d : H)⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hdc : ∀ p ∈ P, (d : H) * p = p * d := by
    intro p hp
    have hyp : (y : H) * p * (y : H)⁻¹ ∈ P :=
      (hmemPQ _).mp (hPn.conj_mem ⟨p, hPQ hp⟩ ((hmemPQ _).mpr hp) y)
    have h1 : (x * y * x⁻¹) * p * (x * y * x⁻¹)⁻¹ = (y : H) * p * (y : H)⁻¹ := by
      calc (x * y * x⁻¹) * p * (x * y * x⁻¹)⁻¹ =
            x * ((y : H) * (x⁻¹ * p * x) * (y : H)⁻¹) * x⁻¹ := by group
        _ = x * ((y : H) * p * (y : H)⁻¹) * x⁻¹ := by rw [hxp' p hp]
        _ = (y : H) * p * (y : H)⁻¹ := hxp _ hyp
    rw [e2] at h1
    have h2 : (d : H) * p * (d : H)⁻¹ = p := by
      calc (d : H) * p * (d : H)⁻¹ =
            (y : H)⁻¹ * (((y : H) * d) * p * ((y : H) * d)⁻¹) * y := by group
        _ = (y : H)⁻¹ * ((y : H) * p * (y : H)⁻¹) * y := by rw [h1]
        _ = p := by group
    calc (d : H) * p = d * p * (d : H)⁻¹ * d := by group
      _ = p * d := by rw [h2]
  have hdy : (d : H) * y = y * d := by
    have hy2 : (y : H) ^ 2 ∈ P := (hmemPQ _).mp (sq_mem_of_index_two hidx y)
    have h1 : x * (y : H) ^ 2 * x⁻¹ = (y : H) ^ 2 := hxp _ hy2
    rw [← conj_pow, e2, pow_two, pow_two] at h1
    have h2 : (d : H) * (y * d) = y :=
      mul_left_cancel (a := (y : H)) (by rw [← mul_assoc]; exact h1)
    calc (d : H) * y = ((d : H) * (y * d)) * (d : H)⁻¹ := by group
      _ = y * (d : H)⁻¹ := by rw [h2]
      _ = y * d := by rw [hdinv]
  have hdZ : d ∈ center Q := by
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    change (q : H) * d = d * q
    by_cases hq : q ∈ PQ
    · exact (hdc q ((hmemPQ q).mp hq)).symm
    · have hyq : y⁻¹ * q ∈ PQ :=
        (mul_mem_iff_of_index_two hidx).mpr ⟨fun h => absurd h hy', fun h => absurd h hq⟩
      have hp := hdc _ ((hmemPQ _).mp hyq)
      have hq' : (q : H) = y * ((y⁻¹ * q : Q) : H) := by simp
      rw [hq']
      calc (y : H) * ((y⁻¹ * q : Q) : H) * d = y * (d * ((y⁻¹ * q : Q) : H)) := by
            rw [mul_assoc, ← hp]
        _ = (d : H) * (y * ((y⁻¹ * q : Q) : H)) := by rw [← mul_assoc, ← hdy, mul_assoc]
  have hdΦ : d ∈ frattini Q := by
    by_cases hd1 : d = 1
    · rw [hd1]
      exact one_mem _
    · exact hZ d hdZ (orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hd2)) hd1)
  have htriv : ∀ q : Q, q⁻¹ * c q ∈ frattini Q := by
    intro q
    by_cases hq : q ∈ PQ
    · have hcq : c q = q := Subtype.ext (by rw [hcv]; exact hxp _ ((hmemPQ q).mp hq))
      rw [hcq, inv_mul_cancel]
      exact one_mem _
    · have hyq : y⁻¹ * q ∈ PQ :=
        (mul_mem_iff_of_index_two hidx).mpr ⟨fun h => absurd h hy', fun h => absurd h hq⟩
      have hcp : c (y⁻¹ * q) = y⁻¹ * q :=
        Subtype.ext (by rw [hcv]; exact hxp _ ((hmemPQ _).mp hyq))
      have hdp : d * (y⁻¹ * q) = (y⁻¹ * q) * d := (mem_center_iff.mp hdZ (y⁻¹ * q)).symm
      have hqyp : q = y * (y⁻¹ * q) := by rw [mul_inv_cancel_left]
      rw [hqyp, map_mul, hcp, hcyd, mul_assoc y d, hdp, ← mul_assoc y (y⁻¹ * q) d,
        inv_mul_cancel_left]
      exact hdΦ
  have hxQ : x ∈ Q := by
    rw [← hker, MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      mem_ker_autQuotient]
    exact htriv
  by_contra hxP'
  set xQ : Q := ⟨x, hxQ⟩ with hxQdef
  have hxQP : xQ ∉ PQ := fun h => hxP' ((hmemPQ xQ).mp h)
  have hxZ : xQ ∈ center Q := by
    rw [mem_center_iff]
    intro q
    apply Subtype.ext
    change (q : H) * x = x * q
    by_cases hq : q ∈ PQ
    · exact mem_centralizer_iff.mp hxP q ((hmemPQ q).mp hq)
    · have hxq : xQ⁻¹ * q ∈ PQ := (mul_mem_iff_of_index_two hidx).mpr
        ⟨fun h => absurd (by simpa using inv_mem h) hxQP, fun h => absurd h hq⟩
      have hp := mem_centralizer_iff.mp hxP _ ((hmemPQ _).mp hxq)
      have hq' : (q : H) = x * ((xQ⁻¹ * q : Q) : H) := by simp [hxQdef]
      rw [hq', mul_assoc, hp]
  have hxQ2 : orderOf xQ = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  exact hxQP (frattini_le_coatom (isCoatom_of_index_prime (hidx ▸ Nat.prime_two))
    (hZ xQ hxZ hxQ2))

end CFSG.LocalAnalysis.GorensteinLyons
