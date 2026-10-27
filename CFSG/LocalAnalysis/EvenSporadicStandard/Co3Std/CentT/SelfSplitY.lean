module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.L2Grp

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup

theorem exists_sylow_cyclic_index_two {Y : Type} [Group Y] [Finite Y] {a b : Y}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbc : ∀ y : Y, y * b = b * y)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hab : a ≠ b)
    (hcent : ∀ y : Y, y * a = a * y → y = 1 ∨ y = a ∨ y = b ∨ y = a * b)
    (h8 : 2 ^ 3 ∣ Nat.card Y) :
    ∃ (Q : Sylow 2 Y) (A : Subgroup Y), a ∈ (Q : Subgroup Y) ∧ b ∈ (Q : Subgroup Y) ∧
      A ≤ (Q : Subgroup Y) ∧ IsCyclic ↥A ∧ A.relIndex (Q : Subgroup Y) = 2 ∧ a ∉ A ∧ b ∈ A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbZ : b ∈ center Y := mem_center_iff.mpr hbc
  have hpa : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact ha2))
  have hpb : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hb2))
  have hsup : IsPGroup 2 ↥(zpowers a ⊔ zpowers b) := by
    haveI : (zpowers b).Normal := Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hbZ)
    exact hpa.to_sup_of_normal_right hpb
  obtain ⟨Q, hWQ⟩ := hsup.exists_le_sylow
  have haQ : a ∈ (Q : Subgroup Y) := hWQ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hbQ : b ∈ (Q : Subgroup Y) := hWQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  let R := ↥(Q : Subgroup Y)
  have hR : IsPGroup 2 R := Q.isPGroup'
  let z : R := ⟨a, haQ⟩
  have hzY : (z : Y) = a := rfl
  have hzz : z * z = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, hzY]
    exact ha2
  have hz1 : z ≠ 1 := fun h => ha1 (by simpa [z] using congrArg (fun w : R => (w : Y)) h)
  have hcard : Nat.card ↥(centralizer ({z} : Set R)) ≤ 4 := by
    have hle : Nat.card ↥(centralizer ({z} : Set R)) ≤
        Nat.card ↥({1, a, b, a * b} : Set Y) := by
      refine Nat.card_le_card_of_injective
        (fun c : ↥(centralizer ({z} : Set R)) =>
          (⟨((c : R) : Y), ?_⟩ : ↥({1, a, b, a * b} : Set Y))) ?_
      · have hcy := Subgroup.mem_centralizer_singleton_iff.mp c.2
        have hcyY : ((c : R) : Y) * a = a * ((c : R) : Y) := by
          have h := congrArg (fun w : R => (w : Y)) hcy
          rw [Subgroup.coe_mul, Subgroup.coe_mul, hzY] at h
          exact h
        rcases hcent ((c : R) : Y) hcyY with h | h | h | h <;> simp [h]
      · intro c d h
        exact Subtype.ext (Subtype.ext
          (congrArg (fun w : ↥({1, a, b, a * b} : Set Y) => (w : Y)) h))
    refine hle.trans ?_
    rw [Nat.card_coe_set_eq]
    have h1 := Set.ncard_insert_le (1 : Y) ({a, b, a * b} : Set Y)
    have h2 := Set.ncard_insert_le (a : Y) ({b, a * b} : Set Y)
    have h3 := Set.ncard_insert_le (b : Y) ({a * b} : Set Y)
    have h4 : ({a * b} : Set Y).ncard = 1 := Set.ncard_singleton _
    omega
  have hYpos : 0 < Nat.card Y := Finite.card_pos
  have hfac : 3 ≤ (Nat.card Y).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hYpos.ne').mp h8
  have hQcard : Nat.card R = 2 ^ (Nat.card Y).factorization 2 := Sylow.card_eq_multiplicity Q
  have hn8 : 8 ≤ Nat.card R := by
    have hdvd : 2 ^ 3 ∣ Nat.card R := by
      rw [hQcard]
      exact pow_dvd_pow 2 hfac
    have := Nat.le_of_dvd (Finite.card_pos (α := R)) hdvd
    norm_num at this
    exact this
  obtain ⟨a', ha'ord, hza'⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.Sec13.exists_cyclic_index_two (Nat.card R) R rfl hR z hzz hz1
      hcard hn8
  let A : Subgroup Y := zpowers (a' : Y)
  haveI : IsCyclic ↥A := inferInstance
  have hAQ : A ≤ (Q : Subgroup Y) := Subgroup.zpowers_le.mpr a'.2
  have hcardA : Nat.card A = orderOf a' := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe]
  have hrel : A.relIndex (Q : Subgroup Y) = 2 := by
    have hmain := Subgroup.relIndex_mul_card (H := A) (K := (Q : Subgroup Y))
    rw [inf_eq_left.mpr hAQ, hcardA] at hmain
    have hQR : Nat.card (Q : Subgroup Y) = Nat.card R := rfl
    rw [hQR, ← ha'ord] at hmain
    have hpos : 0 < orderOf a' := orderOf_pos_iff.mpr (isOfFinOrder_of_finite a')
    refine Nat.mul_right_cancel hpos ?_
    rw [hmain, mul_comm 2 (orderOf a')]
  have haA : a ∉ A := by
    intro ha
    apply hza'
    rw [Subgroup.mem_zpowers_iff] at ha ⊢
    obtain ⟨k, hk⟩ := ha
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hzY]
    exact hk
  have hbA : b ∈ A := by
    by_contra hbA
    have hbK : b ∈ A ⊔ zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    have hKne : A ⊔ zpowers b ≠ A := fun h => hbA (h ▸ hbK)
    haveI : (zpowers b).Normal := Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hbZ)
    have hKle : A ⊔ zpowers b ≤ (Q : Subgroup Y) :=
      sup_le hAQ ((Subgroup.zpowers_le).mpr hbQ)
    have hKQ : A ⊔ zpowers b = (Q : Subgroup Y) := by
      have hmul := Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ zpowers b)
        (L := (Q : Subgroup Y)) le_sup_left hKle
      rw [hrel] at hmul
      have hdvd : (A ⊔ zpowers b).relIndex (Q : Subgroup Y) ∣ 2 :=
        ⟨A.relIndex (A ⊔ zpowers b), by rw [mul_comm]; exact hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact le_antisymm hKle (Subgroup.relIndex_eq_one.mp h1)
      · exfalso
        have hA1 : A.relIndex (A ⊔ zpowers b) = 1 := by
          rw [h2] at hmul
          refine Nat.mul_right_cancel (by norm_num : 0 < 2) ?_
          rw [one_mul, hmul]
        exact hKne (le_antisymm (Subgroup.relIndex_eq_one.mp hA1) le_sup_left)
    have haK : a ∈ A ⊔ zpowers b := hKQ.symm ▸ haQ
    obtain ⟨α, hα, β, hβ, hαβ⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := A) (t := zpowers b)).mp haK
    have hcentA : A ≤ centralizer ({a} : Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hβle : zpowers b ≤ center Y := (Subgroup.zpowers_le).mpr hbZ
      have hβc : β ∈ center Y := hβle hβ
      calc x * a = x * (α * β) := by rw [hαβ]
        _ = (x * α) * β := by rw [mul_assoc]
        _ = (α * x) * β := by rw [setLike_mul_comm hx hα]
        _ = α * (x * β) := by rw [mul_assoc]
        _ = α * (β * x) := by rw [mem_center_iff.mp hβc x]
        _ = (α * β) * x := by rw [mul_assoc]
        _ = a * x := by rw [hαβ]
    have hbcent : b ∈ centralizer ({a} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hbc a).symm
    have hQle : (Q : Subgroup Y) ≤ centralizer ({a} : Set Y) := by
      rw [← hKQ]
      exact sup_le hcentA ((Subgroup.zpowers_le).mpr hbcent)
    have hzcenter : z ∈ center R := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply Subtype.ext
      have hv := Subgroup.mem_centralizer_singleton_iff.mp (hQle v.2)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hzY]
      exact hv
    have htop : centralizer ({z} : Set R) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hzcenter)
    have hEq : Nat.card ↥(centralizer ({z} : Set R)) = Nat.card R := by
      rw [htop, Subgroup.card_top]
    omega
  exact ⟨Q, A, haQ, hbQ, hAQ, inferInstance, hrel, haA, hbA⟩

theorem exists_cyclic_relIndex_le_two {Y : Type} [Group Y] [Finite Y] {a b : Y}
    (hb2 : b * b = 1) (hb1 : b ≠ 1) (hbc : ∀ y : Y, y * b = b * y)
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (hab : a ≠ b)
    (hcent : ∀ y : Y, y * a = a * y → y = 1 ∨ y = a ∨ y = b ∨ y = a * b)
    (h8 : 2 ^ 3 ∣ Nat.card Y) (P : Subgroup Y) (hP : IsPGroup 2 P) :
    ∃ M : Subgroup Y, M ≤ P ∧ IsCyclic ↥M ∧ M.relIndex P ≤ 2 := by
  classical
  obtain ⟨Q, A, haQ, hbQ, hAQ, hAcyc, hrel, haA, hbA⟩ :=
    exists_sylow_cyclic_index_two hb2 hb1 hbc ha2 ha1 hab hcent h8
  obtain ⟨Q', hPQ'⟩ := hP.exists_le_sylow
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 2 Y) := Sylow.finite_of_finiteIndex Q
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q Q'
  let f : Y →* Y := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  let A' : Subgroup Y := A.map f
  have hQmap : (Q : Subgroup Y).map f = (Q' : Subgroup Y) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hA'Q' : A' ≤ (Q' : Subgroup Y) := by
    rw [← hQmap]
    exact Subgroup.map_mono hAQ
  haveI hAcyc' : IsCyclic ↥A' := by
    haveI : IsCyclic ↥A := hAcyc
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective A f hf)
      (Subgroup.equivMapOfInjective A f hf).surjective
  have hrel' : A'.relIndex (Q' : Subgroup Y) = 2 := by
    have hmap := Subgroup.relIndex_map_map_of_injective (f := f) A (Q : Subgroup Y) hf
    rw [hrel, hQmap] at hmap
    exact hmap
  refine ⟨P ⊓ A', inf_le_left, ?_, ?_⟩
  · exact Subgroup.isCyclic_of_le inf_le_right
  · rw [Subgroup.inf_relIndex_left]
    calc A'.relIndex P ≤ A'.relIndex (Q' : Subgroup Y) :=
          Subgroup.relIndex_le_of_le_right hPQ' (by rw [hrel']; norm_num)
      _ = 2 := hrel'

end CFSG.EvenSporadicStandard.Co3Std.CentT
