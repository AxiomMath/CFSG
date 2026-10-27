module

public import CFSG.GH74.Generic.BProg.B1.Stage3aRankCore
import CFSG.GH74.Generic.BProg.B1.Sp4Rank
import CFSG.GH74.Generic.S3.Front
public import CFSG.GH74.Generic.ClassicalCerts

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

theorem rankCertified_isSL4Model_three {K : Type} [Group K] (h : IsSL4Model K) :
    RankCertified K 3 := by
  rcases h with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
    exact (RankCertified.of_quotient ((StatedScalars (Fin 4) F).subgroupOf (StatedSL 4 F))
      (rankCertified_PSL4 (ringChar_ne_two_of_odd_natCard hodd))).of_mulEquiv e.symm
  · exact (RankCertified.of_quotient ((StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 q F))
      (rankCertified_PSU4 hF (by omega))).of_mulEquiv e.symm

theorem noJPrimeFor_shape1 : NoJPrimeFor QShape1 := by
  refine noJPrimeFor_of_bar (fun e h => IsSL4Model.of_mulEquiv h e) ?_
  intro G _ _ hgen x K hx hKpc _ hr hS1
  have hS1' : IsSL4Model ↥(imgBar x K) := hS1
  have hmem : xbar x ∈ imgBar x K := xbar_mem_of_isSL4Model hgen hx hS1'
  obtain ⟨z, φ, hz2, hcenter, -, -⟩ := hS1'.exists_center_q8q8
  have hxz : (⟨xbar x, hmem⟩ : ↥(imgBar x K)) = z := by
    have hc : (⟨xbar x, hmem⟩ : ↥(imgBar x K)) ∈ Subgroup.center ↥(imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (xbar_comm x g)
    rcases (hcenter _).1 hc with h | h
    · exact absurd (congrArg Subtype.val h) (xbar_ne_one hx)
    · exact h
  refine false_of_J2_pair_rank hgen hx hKpc hr (rankCertified_isSL4Model_three hS1') ?_
    (by norm_num) (fun _ => le_rfl)
  intro w hw
  rcases (hcenter w).1 hw with h | h
  · exact Or.inl (by rw [h]; rfl)
  · exact Or.inr (by rw [h, ← hxz])

@[expose] def QShape3W (Kt : Type) [Group Kt] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧
    ((LieModel Kt .PSL 3 p f ∧ p ^ f % 4 = 1) ∨ (LieModel Kt .PSU 3 p f ∧ p ^ f % 4 = 3))

@[expose] def QShape3SD (Kt : Type) [Group Kt] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 < p ^ f ∧
    ((LieModel Kt .PSL 3 p f ∧ p ^ f % 4 = 3) ∨ (LieModel Kt .PSU 3 p f ∧ p ^ f % 4 = 1))

theorem QShape3W.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3W A) :
    QShape3W B := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := h
  · exact ⟨p, f, hp, hp2, hq, Or.inl ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h.1, h.2⟩⟩
  · exact ⟨p, f, hp, hp2, hq, Or.inr ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h.1, h.2⟩⟩

theorem QShape3SD.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (h : QShape3SD A) :
    QShape3SD B := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := h
  · exact ⟨p, f, hp, hp2, hq, Or.inl ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h.1, h.2⟩⟩
  · exact ⟨p, f, hp, hp2, hq, Or.inr ⟨CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h.1, h.2⟩⟩

theorem QShape3SD.qShape3 {Kt : Type} [Group Kt] (h : QShape3SD Kt) : QShape3 Kt := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := h
  · exact ⟨p, f, hp, hp2, hq, Or.inl h.1⟩
  · exact ⟨p, f, hp, hp2, hq, Or.inr h.1⟩

theorem qShape3_split {Kt : Type} [Group Kt] (h : QShape3 Kt) : QShape3W Kt ∨ QShape3SD Kt := by
  obtain ⟨p, f, hp, hp2, hq, hL⟩ := h
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2).pow
  have h4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases hL with hL | hL <;> rcases h4 with h4 | h4
  · exact Or.inl ⟨p, f, hp, hp2, hq, Or.inl ⟨hL, h4⟩⟩
  · exact Or.inr ⟨p, f, hp, hp2, hq, Or.inl ⟨hL, h4⟩⟩
  · exact Or.inr ⟨p, f, hp, hp2, hq, Or.inr ⟨hL, h4⟩⟩
  · exact Or.inl ⟨p, f, hp, hp2, hq, Or.inr ⟨hL, h4⟩⟩

theorem center_eq_bot_of_simple_of_quasisimple {K : Type} [Group K] (hs : IsSimpleGroup K)
    (hq : IsQuasisimple K) : center K = ⊥ := by
  obtain ⟨-, -, a', b', hab'⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  have hnab : a * b ≠ b * a := fun h' => hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h'])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with hb | ht
  · exact hb
  · exfalso
    apply hnab
    have : a ∈ center K := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

theorem noJPrimeFor_shape3W : NoJPrimeFor QShape3W := by
  refine noJPrimeFor_of_bar (fun e h => QShape3W.of_mulEquiv e h) ?_
  intro G _ _ hgen x K hx hKpc hG2 hr h3
  obtain ⟨p, f, -, -, -, hmodel⟩ := h3
  have hsimple : IsSimpleGroup ↥(imgBar x K) :=
    isSimpleGroup_of_lieModel_L3 (hmodel.imp (fun h => h.1) (fun h => h.1))
  have hbot : center ↥(imgBar x K) = ⊥ := center_eq_bot_of_simple_of_quasisimple hsimple hG2.1.1
  exact false_of_J2_pair_rank_of_center_bot hgen hx hKpc hr hbot
    (rankCertified_two_of_eps ⟨p, f, hmodel⟩)

@[expose] def NoJPrimeShape3SD : Prop := NoJPrimeFor QShape3SD

theorem noJPrimeFor_shape3_of_SD (hSD : NoJPrimeShape3SD) : NoJPrimeFor QShape3 := by
  intro G _ _ hyp noAlt x K hJ hr hP
  rcases qShape3_split hP with h | h
  · exact noJPrimeFor_shape3W G hyp noAlt x K hJ hr h
  · exact hSD G hyp noAlt x K hJ hr h

end CFSG.GH74.Generic.BProg.B1
