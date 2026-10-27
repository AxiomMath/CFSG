module

public import CFSG.ClassicalInvolution.AschTight.S1916Local

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

omit [Finite G] in
theorem normalizer_le_centralizer_of_isUniqueInvolution {M : Subgroup G}
    (hz : IsUniqueInvolution M z) :
    Subgroup.normalizer (M : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  have h1 : n * z * n⁻¹ = z := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]

theorem inf_sup_eq_and_isSylow2In (S : Sylow 2 G) {C A H T : Subgroup G}
    (hSC : (S : Subgroup G) ≤ C) (hAC : A ≤ C) (hHC : H ≤ C)
    (hnA : C ≤ Subgroup.normalizer (A : Set G)) (hT : IsSylow2In T H)
    (hTS : T ≤ (S : Subgroup G)) :
    (S : Subgroup G) ⊓ (A ⊔ H) = ((S : Subgroup G) ⊓ A) ⊔ T ∧
      IsSylow2In ((S : Subgroup G) ⊓ (A ⊔ H)) (A ⊔ H) := by
  have hPA := isSylow2In_inf S hSC hAC hnA
  set PA := (S : Subgroup G) ⊓ A with hPAdef
  have hAH : IsSylow2In (T ⊓ (A ⊓ H)) (A ⊓ H) :=
    isSylow2In_inf_of_le_normalizer hT inf_le_right
      (fun x hx => mem_normalizer_inf (hnA (hHC hx)) (Subgroup.le_normalizer hx))
  have hTN : T ≤ Subgroup.normalizer (PA : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer (hTS hx)) (hnA (hHC (hT.1 hx)))
  have hinf : PA ⊓ T = T ⊓ (A ⊓ H) := by
    apply le_antisymm
    · exact le_inf inf_le_right (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hT.1))
    · exact le_inf (le_inf (inf_le_left.trans hTS) (inf_le_right.trans inf_le_left)) inf_le_left
  have hP := card_sup_mul_card_inf hTN
  rw [hinf, natCard_eq_of_isSylow2In hPA, natCard_eq_of_isSylow2In hT,
    natCard_eq_of_isSylow2In hAH] at hP
  have hH := card_sup_mul_card_inf (A := A) (C := H) (hHC.trans hnA)
  have hfac := congrArg (fun n => n.factorization 2) hH
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
  simp only [Finsupp.add_apply] at hfac
  have hcard : Nat.card ↥(PA ⊔ T) = 2 ^ (Nat.card ↥(A ⊔ H)).factorization 2 := by
    have h1 : Nat.card ↥(PA ⊔ T) * 2 ^ (Nat.card ↥(A ⊓ H)).factorization 2 =
        2 ^ (Nat.card ↥(A ⊔ H)).factorization 2 * 2 ^ (Nat.card ↥(A ⊓ H)).factorization 2 := by
      rw [hP, ← pow_add, ← pow_add, hfac]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hle : PA ⊔ T ≤ (S : Subgroup G) ⊓ (A ⊔ H) :=
    sup_le (inf_le_inf_left _ le_sup_left) (le_inf hTS (hT.1.trans le_sup_right))
  have h2 : IsPGroup 2 ↥((S : Subgroup G) ⊓ (A ⊔ H)) := S.isPGroup'.to_le inf_le_left
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (P := A ⊔ H) (T := ⊥) IsPGroup.of_bot bot_le
  have hSyl : IsSylow2In ((S : Subgroup G) ⊓ (A ⊔ H)) (A ⊔ H) := by
    refine hV.of_natCard_le h2 inf_le_right ?_
    rw [natCard_eq_of_isSylow2In hV, ← hcard]
    exact Subgroup.card_le_of_le hle
  refine ⟨(Subgroup.eq_of_le_of_card_ge hle ?_).symm, hSyl⟩
  rw [natCard_eq_of_isSylow2In hSyl, ← hcard]

theorem commutator_mem_oddCoreOf_of_sup {X A B : Subgroup G} {a : G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hA : ∀ x ∈ A, ⁅a, x⁆ ∈ oddCoreOf X) (hB : ∀ x ∈ B, ⁅a, x⁆ ∈ oddCoreOf X) :
    ∀ m ∈ A ⊔ B, ⁅a, m⁆ ∈ oddCoreOf X := by
  let H : Subgroup G :=
    { carrier := {m | m ∈ X ∧ ⁅a, m⁆ ∈ oddCoreOf X}
      one_mem' := ⟨X.one_mem, by simp [(oddCoreOf X).one_mem]⟩
      mul_mem' := by
        rintro m₁ m₂ ⟨h1X, h1⟩ ⟨h2X, h2⟩
        refine ⟨X.mul_mem h1X h2X, ?_⟩
        have e : ⁅a, m₁ * m₂⁆ = ⁅a, m₁⁆ * (m₁ * ⁅a, m₂⁆ * m₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        refine (oddCoreOf X).mul_mem h1 ?_
        exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCoreOf_of_mem_normalizer
          (Subgroup.le_normalizer h1X)) _).mp h2
      inv_mem' := by
        rintro m ⟨hX, h⟩
        refine ⟨X.inv_mem hX, ?_⟩
        have e : ⁅a, m⁻¹⁆ = m⁻¹ * ⁅a, m⁆⁻¹ * m := by
          simp only [commutatorElement_def]; group
        rw [e]
        have h1 := (oddCoreOf X).inv_mem h
        have h2 := (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCoreOf_of_mem_normalizer
          (Subgroup.le_normalizer (X.inv_mem hX))) _).mp h1
        rwa [inv_inv] at h2 }
  have hle : A ⊔ B ≤ H := sup_le (fun x hx => ⟨hAX hx, hA x hx⟩) (fun x hx => ⟨hBX hx, hB x hx⟩)
  exact fun m hm => (hle hm).2

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
