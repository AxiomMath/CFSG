module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem exists_involution_lift_of_odd {A : Type*} [Group A] {N : Subgroup A} [N.Normal]
    (hN : Odd (Nat.card N)) {g : A} (hg : orderOf (QuotientGroup.mk g : A ⧸ N) = 2) :
    ∃ a : A, orderOf a = 2 ∧ (QuotientGroup.mk a : A ⧸ N) = QuotientGroup.mk g := by
  have hq2 : (QuotientGroup.mk g : A ⧸ N) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk g : A ⧸ N)
    rwa [hg] at this
  have hg2 : g ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hq2
  have hm : Odd (orderOf (g ^ 2)) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hg2)
  have hmk : (QuotientGroup.mk (g ^ orderOf (g ^ 2)) : A ⧸ N) = QuotientGroup.mk g := by
    obtain ⟨k, hk⟩ := hm
    rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, hq2, one_pow, one_mul]
  have hsq : (g ^ orderOf (g ^ 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_orderOf_eq_one (g ^ 2)
  have hne : g ^ orderOf (g ^ 2) ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk g : A ⧸ N) = 1 := by rw [← hmk, h]; exact QuotientGroup.mk_one N
    rw [h1, orderOf_one] at hg
    omega
  exact ⟨g ^ orderOf (g ^ 2), orderOf_eq_prime hsq hne, hmk⟩

theorem exists_involution_lift_oddCore {A : Type*} [Group A] [Finite A] {ā : A ⧸ oddCore A}
    (hā : orderOf ā = 2) : ∃ a : A, orderOf a = 2 ∧ (QuotientGroup.mk a : A ⧸ oddCore A) = ā := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (CFSG.oddCore A)) := by
    rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := A)]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := A))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ā
  exact exists_involution_lift_of_odd (N := oddCore A) hodd hā

theorem isSubnormal_subgroupOf_of_normal {K A B : Subgroup G} (hKA : K ≤ A) (hAB : A ≤ B)
    (hK : (K.subgroupOf A).IsSubnormal) (hA : (A.subgroupOf B).Normal) :
    (K.subgroupOf B).IsSubnormal := by
  have hKleB : K.subgroupOf B ≤ A.subgroupOf B := fun x hx => hKA hx
  have hHsn : ((K.subgroupOf B).subgroupOf (A.subgroupOf B)).IsSubnormal := by
    have h := hK.comap (A.subgroupOfEquivOfLe hAB).toMonoidHom
    convert h using 1
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rfl
  exact Subgroup.IsSubnormal.trans hKleB hHsn hA.isSubnormal

theorem Sl23PocketIn.of_normal_centralizer {L N : Subgroup G} {y : G} {K : Subgroup G}
    (h : Sl23PocketIn L y K) (hLN : L ≤ N)
    (hnorm : ∀ c ∈ N ⊓ centralizer ({y} : Set G), CFSG.conjugate L c = L) :
    Sl23PocketIn N y K := by
  have hAB : L ⊓ centralizer ({y} : Set G) ≤ N ⊓ centralizer ({y} : Set G) :=
    inf_le_inf hLN le_rfl
  refine ⟨h.1, h.2.1.trans hAB, ?_, h.2.2.2⟩
  have hAnorm : ((L ⊓ centralizer ({y} : Set G)).subgroupOf
      (N ⊓ centralizer ({y} : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAB, Subgroup.le_normalizer_iff]
    intro b hb a ha
    have hbinv := hnorm b⁻¹ ((N ⊓ centralizer ({y} : Set G)).inv_mem hb)
    rw [Subgroup.mem_inf] at hb ha ⊢
    obtain ⟨hbN, hbC⟩ := hb
    obtain ⟨haL, haC⟩ := ha
    refine ⟨?_, ?_⟩
    · rw [conjugate_inv_eq_map_conj] at hbinv
      rw [← hbinv]
      exact Subgroup.mem_map.mpr ⟨a, haL, by simp [MulAut.conj_apply]⟩
    · exact (centralizer ({y} : Set G)).mul_mem
        ((centralizer ({y} : Set G)).mul_mem hbC haC)
        ((centralizer ({y} : Set G)).inv_mem hbC)
  exact isSubnormal_subgroupOf_of_normal h.2.1 hAB h.2.2.1 hAnorm

private theorem sl2f3_comm_pow_four :
    ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), (a * b * a⁻¹ * b⁻¹) ^ 4 = 1 := by
  decide +kernel

private theorem sl2f3_mul_pow_four :
    ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 →
      (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem sl2f3_exists_pow_four_ne : ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
    g ^ 4 ≠ 1 := by
  decide +kernel

private theorem sl2f3_exists_noncomm : ∃ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
    a * b ≠ b * a := by
  decide +kernel

private def q3 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) where
  carrier := {g | g ^ 4 = 1}
  one_mem' := one_pow 4
  mul_mem' := fun {a b} ha hb => sl2f3_mul_pow_four a b ha hb
  inv_mem' := fun {a} ha => by
    have h : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, h, inv_one]

theorem not_isPerfect_sl2f3 :
    ¬ Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  intro hP
  have h1 : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) = ⊤ := hP.commutator_eq_top
  have h2 : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ≤ q3 := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [commutatorElement_def]
    exact sl2f3_comm_pow_four a b
  rw [h1, top_le_iff] at h2
  obtain ⟨g, hg⟩ := sl2f3_exists_pow_four_ne
  exact hg (h2 ▸ Subgroup.mem_top g : g ∈ q3)

theorem IsSL23Mod.not_isPerfect {Q : Type} [Group Q] (h : IsSL23Mod Q) :
    ¬ Group.IsPerfect Q := by
  intro hP
  obtain ⟨e⟩ := h
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom.comp (QuotientGroup.mk' (oddCore Q)))
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
  exact not_isPerfect_sl2f3 this

theorem IsSL23Mod.exists_noncomm {Q : Type} [Group Q] (h : IsSL23Mod Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨e⟩ := h
  obtain ⟨x, y, hxy⟩ := sl2f3_exists_noncomm
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm x)
  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (e.symm y)
  apply hxy
  have h1 : e (QuotientGroup.mk (a * b)) = e (QuotientGroup.mk (b * a)) := by rw [hcon a b]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, ha, hb] at h1
  simpa using h1

theorem subnormal_le_center_or_eq_top_of_isQuasisimple' {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) {N : Subgroup Q} (hN : N.IsSubnormal) :
    N ≤ center Q ∨ N = ⊤ := by
  rcases hN.lt_normal with htop | ⟨K, hKn, hNK, hKlt⟩
  · exact Or.inr htop
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hKn with hKtop | hKc
    · exact absurd hKtop hKlt.ne
    · exact Or.inl (hNK.trans hKc)

theorem exists_noncomm_of_sl23PocketIn {X K : Subgroup G} {y : G} (hX : CFSG.IsQuasisimple ↥X)
    (hK : Sl23PocketIn X y K) : ∃ a ∈ X, a * y ≠ y * a := by
  by_contra hcon
  push Not at hcon
  have hXC : X ≤ centralizer ({y} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcon a ha)
  have hKX : K ≤ X := hK.2.1.trans inf_le_left
  have hsub : (K.subgroupOf X).IsSubnormal := by
    have h := hK.2.2.1
    rwa [inf_eq_left.mpr hXC] at h
  rcases subnormal_le_center_or_eq_top_of_isQuasisimple' hX hsub with hc | htop
  · obtain ⟨a, b, hab⟩ := hK.2.2.2.exists_noncomm
    apply hab
    have ha : (⟨(a : G), hKX a.2⟩ : ↥X) ∈ center ↥X := hc a.2
    have := Subgroup.mem_center_iff.mp ha ⟨(b : G), hKX b.2⟩
    exact Subtype.ext (congrArg (fun z : ↥X => (z : G)) this).symm
  · have hXK : X ≤ K := fun a ha => by
      have : (⟨a, ha⟩ : ↥X) ∈ K.subgroupOf X := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have hKeq : K = X := le_antisymm hKX hXK
    subst hKeq
    exact hK.2.2.2.not_isPerfect hX.1

theorem conjugate_eq_of_noncomm [Finite G] {C X : Subgroup G} {y : G} (hX : IsComponentIn X C)
    (hy : y ∈ X) (hnc : ∃ a ∈ X, a * y ≠ y * a) :
    ∀ c ∈ C ⊓ centralizer ({y} : Set G), CFSG.conjugate X c = X := by
  intro c hc
  by_contra hne
  have hXc : IsComponentIn (CFSG.conjugate X c) C := hX.conjugate hc.1
  obtain ⟨a, ha, hay⟩ := hnc
  have hyc : y ∈ CFSG.conjugate X c := by
    have hcy : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    unfold CFSG.conjugate
    refine Subgroup.mem_map.mpr ⟨y, hy, ?_⟩
    change c⁻¹ * y * c⁻¹⁻¹ = y
    rw [inv_inv, mul_assoc, ← hcy, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hay (hX.commute_of_ne hXc (Ne.symm hne) a ha y hyc)

end CFSG.OddStandard.SmallF3.Omega
