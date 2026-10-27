module

public import CFSG.CharacterTheory.BrauerLinearThree.QOneDefect
public import CFSG.CharacterTheory.BrauerLinearThree.LocalRecognition

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes CFSG.TwoRankLowerBound.Helpers CFSG.BrauerLinearThree.QOne

theorem brauer_linear_three_involution_centralizer_of_principal_block
    (h5 : BrauerWreathedTypeOnePrincipalBlockStatement)
    (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : p ^ f % 4 = 1)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = p ^ f)
    (Z : Subgroup (GL (Fin 2) F)) [Z.Normal]
    (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
    (x : G) (hx : orderOf x = 2) (e : Subgroup.centralizer ({x} : Set G) ≃* GL (Fin 2) F ⧸ Z) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  have hq' : Nat.card F % 4 = 1 := by rw [hF]; exact hq
  have h2 : (2 : F) ≠ 0 := by
    intro h
    let : Fintype F := Fintype.ofFinite F
    have hc : ((Nat.card F : ℕ) : F) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero F
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rw [hF, hk] at hc
    push_cast at hc
    rw [h] at hc
    simp at hc
  have hcard := card_mul_card_Z_eq e hZ hZodd h2 hx h5 hnonab hq'
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨n, S, S₁, S₂, T, hn, hgen, hcardS, hS₁, hS₂, hT, hcomm, hconj, -, hJpow, hJ₂pow⟩ :=
    exists_wreath_sylow_of_G e hZ hZodd h2 hx hq'
  obtain ⟨h6, hA⟩ := caseOneA_of_simple e hnonab n hn S S₁ S₂ T hgen hcardS hS₁ hS₂ hT hcomm
    hconj hJpow hJ₂pow
  obtain ⟨χ, hχ₁, hχ₄, hχ₅, hrel⟩ := typeOne_characters h5 hZ hZodd hq' n hn S S₁ S₂ T hgen
    hcardS hS₁ hS₂ hT hcomm hconj hJpow hJ₂pow hA e h6 basis
  have hL1 : ∀ p' : ℕ, p'.Prime → p' ≠ 2 → p' ∣ Nat.card F + 1 →
      ∀ g : G, orderOf g ≠ p' * ringChar F := fun p' hp' hp'2 hp'q g =>
    orderOf_ne_mul_ringChar hZ hcard basis hχ₁ hχ₅ (fun g hg => (hrel g hg).1)
      (fun g hg => (hrel g hg).2.2) h2 hp' hp'2 hp'q g
  have hinv := isConj_of_involutions e hZ hZodd h2 hx hnonab
  have h4G : ∀ z ∈ centerSub e, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({x} : Set G) :=
    fun z hz hz1 => centralizer_eq_of_mem_centerSub e hZ hZodd h2 hx h5 hnonab hq' hz hz1
  have hcent := card_centralizer_conditions e hZ hZodd h2 hcard basis hχ₁ hχ₄
    (fun g hg => (hrel g hg).1.trans (hrel g hg).2.1) hq' hx hinv hL1 h4G
  exact statedClassicalModel_of_local e hZ hZodd h2 hx hcard hcent hnonab p f hp hf hF

end CFSG.BrauerLinearThree
