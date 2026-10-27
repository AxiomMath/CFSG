module

public import CFSG.ClassicalInvolution.Uniform.UFacts
public import CFSG.ClassicalInvolution.Q3.Basic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Generic

variable {p f : ℕ} [Fact p.Prime] {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMemberU.ofGeneric (hp2 : p ≠ 2) (hf : 0 < f)
    (h : IsClassicalMember p f L z) : IsClassicalMemberU (.sl2 p f) L z where
  admissible := ⟨Fact.out, hp2, hf⟩
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := h.subnormal
  witness := ⟨inferInstance, h.nonempty_equiv⟩
  perfect _ := h.perfect

theorem IsClassicalMemberU.toGeneric (hq : 5 ≤ p ^ f) (h : IsClassicalMemberU (.sl2 p f) L z) :
    IsClassicalMember p f L z where
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  perfect := h.perfect (by
    intro h3
    have : (MemberType.sl2 p f).IsSolvableType := h3
    change p ^ f = 3 at this
    omega)
  subnormal := h.subnormal
  nonempty_equiv := h.nonempty_equiv_sl2

theorem isClassicalMember_iff_U (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    IsClassicalMember p f L z ↔ IsClassicalMemberU (.sl2 p f) L z := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  exact ⟨fun h => IsClassicalMemberU.ofGeneric hp2 hf h, fun h => h.toGeneric hq⟩

end Generic

section Three

variable {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMemberU.ofQ3 (h : Q3.IsClassicalMember3 L z) :
    IsClassicalMemberU (.sl2 3 1) L z where
  admissible := ⟨Nat.prime_three, by norm_num, by norm_num⟩
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := h.subnormal
  witness := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨e⟩ := h.nonempty_equiv
    obtain ⟨e'⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three
      (F := GaloisField 3 1) (by rw [natCard_galoisField_eq (by norm_num)]; norm_num)
    exact ⟨this, ⟨e.trans e'.symm⟩⟩
  perfect hns := absurd (show (3 : ℕ) ^ 1 = 3 by norm_num) hns

theorem IsClassicalMemberU.toQ3 {p f : ℕ} (h : IsClassicalMemberU (.sl2 p f) L z)
    (h3 : p ^ f = 3) : Q3.IsClassicalMember3 L z where
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := h.subnormal
  nonempty_equiv := h.nonempty_equiv_sl2Three h3

theorem isClassicalMember3_iff_U :
    Q3.IsClassicalMember3 L z ↔ IsClassicalMemberU (.sl2 3 1) L z :=
  ⟨fun h => IsClassicalMemberU.ofQ3 h, fun h => h.toQ3 (by norm_num)⟩

end Three

section A7

variable {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMemberU.of2A7 (h : Hat2A7.IsClassical2A7 ⊤ L z) :
    IsClassicalMemberU .twoA7 L z where
  admissible := trivial
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  subnormal := by
    have h1 := h.subnormal
    rwa [top_inf_eq] at h1
  witness := h.witness
  perfect _ := h.perfect

theorem IsClassicalMemberU.to2A7 (h : IsClassicalMemberU .twoA7 L z) :
    Hat2A7.IsClassical2A7 ⊤ L z where
  orderOf_eq_two := h.orderOf_eq_two
  mem := h.mem
  perfect := h.perfect MemberType.not_isSolvableType_twoA7
  subnormal := by rw [top_inf_eq]; exact h.subnormal
  witness := h.witness

theorem isClassical2A7_iff_U : Hat2A7.IsClassical2A7 ⊤ L z ↔ IsClassicalMemberU .twoA7 L z :=
  ⟨fun h => IsClassicalMemberU.of2A7 h, fun h => h.to2A7⟩

end A7

section Witness

variable {t : MemberType} {Y : Type} [Group Y] {L : Subgroup Y} {z : Y}

theorem IsClassicalMemberU.classicalInvolutionWitness (h : IsClassicalMemberU t L z) :
    classicalInvolutionWitness L := by
  cases t with
  | sl2 p f =>
    obtain ⟨hp, ⟨e⟩⟩ := h.witness
    exact Or.inl ⟨p, f, hp, h.admissible.2.1, h.admissible.2.2, ⟨e⟩⟩
  | twoA7 => exact Or.inr h.witness

theorem exists_memberU_of_witness {J : Subgroup Y} (hz : orderOf z = 2) (hzJ : z ∈ J)
    (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set Y)))
    (hw : classicalInvolutionWitness J) (hperf : ¬ Group.IsSolvable J → Group.IsPerfect J) :
    ∃ t : MemberType, IsClassicalMemberU t J z := by
  rcases hw with ⟨p, n, hp, hp2, hn, ⟨e⟩⟩ | ⟨hqs, hcard, ⟨ψ⟩⟩
  · refine ⟨.sl2 p n, ⟨⟨hp.out, hp2, hn⟩, hz, hzJ, hJ, ⟨hp, ⟨e⟩⟩, fun hns => hperf ?_⟩⟩
    intro hsolv
    have hodd : Odd (Nat.card (GaloisField p n)) := by
      have := hp
      exact odd_natCard_galoisField_of_pos hp2 hn
    have hs : Group.IsSolvable SL(2, GaloisField p n) := by
      have := hsolv
      have h1 : Group.IsSolvable (J ⧸ classicalInvolutionOddCore J) :=
        Group.isSolvable_of_surjective (f := QuotientGroup.mk' (classicalInvolutionOddCore J))
          (QuotientGroup.mk'_surjective _)
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have h3 := natCard_eq_three_of_isSolvable_sl2 hodd hs
    rw [natCard_galoisField_eq hn] at h3
    exact hns h3
  · refine ⟨.twoA7, ⟨trivial, hz, hzJ, hJ, ⟨hqs, hcard, ⟨ψ⟩⟩, fun _ => hperf ?_⟩⟩
    intro hsolv
    have hs : Group.IsSolvable (J ⧸ classicalInvolutionOddCore J) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' (classicalInvolutionOddCore J))
        (QuotientGroup.mk'_surjective _)
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hqs hs

end Witness

end CFSG.ClassicalInvolution.Uniform
