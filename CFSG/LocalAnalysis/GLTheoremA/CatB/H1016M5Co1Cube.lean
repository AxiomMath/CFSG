module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Defs
public import Certificates.Certificate3024
public import Certificates.Certificate10145
public import Certificates.Certificate13670
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporCo15
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMFiveFixData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5

open CFSG.Open CFSG.Sporadic.Co1Schreier CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F

open scoped Matrix

private theorem fixFree_conj {x : GL24}
    (hx : ∀ v : Fin 24 → ZMod 2, (x : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0)
    (c : GL24) (v : Fin 24 → ZMod 2)
    (hv : ((c⁻¹ * x * c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) : v = 0 := by
  have h1 : (x : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
      ((c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) =
        (c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v :=
    calc _ = (c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
          (((c⁻¹ * x * c : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) := by
          simp only [Matrix.mulVec_mulVec, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
      _ = _ := by rw [hv]
  calc v = ((c⁻¹ : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ
        ((c : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    _ = 0 := by rw [hx _ h1, Matrix.mulVec_zero]

private theorem cube_facts_of {G : Type} [Group G] [Finite G] {Q A0 : Subgroup G}
    (hQ : Nat.card Q = 5 ^ (Nat.card G).factorization 5) (hA0c : Nat.card A0 = 125)
    (hle : ∀ A : Subgroup G, A ≤ Q → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → 125 ≤ Nat.card A →
      A ≤ A0)
    (P : G → Prop) (hP : ∀ x g : G, P x → P (g⁻¹ * x * g)) {x0 : G} (hx0 : x0 ∈ A0)
    (hPx0 : P x0) :
    (∀ E : Subgroup G, IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 3) ∧
      ∀ E : Subgroup G, IsElemAbelian 5 E → Nat.card E = 5 ^ 3 → ∃ j ∈ E, P j := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have key : ∀ E : Subgroup G, IsElemAbelian 5 E → 125 ≤ Nat.card E →
      ∃ g : G, E.map (MulAut.conj g).toMonoidHom = A0 := by
    intro E hE h125
    obtain ⟨g, hg⟩ := KD264Gen.Co15.exists_conj_le_of_full hQ hE.isPGroup
    have hel : IsElemAbelian 5 (E.map (MulAut.conj g).toMonoidHom) := hE.map _
    have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have hA := hle _ hg (fun x hx y hy => congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (by rw [hcard]; exact h125)
    exact ⟨g, Subgroup.eq_of_le_of_card_ge hA (by rw [hA0c, hcard]; exact h125)⟩
  refine ⟨fun E hE => ?_, fun E hE hE3 => ?_⟩
  · rw [show (5 : ℕ) ^ 3 = 125 by norm_num]
    by_contra hlt
    push Not at hlt
    obtain ⟨g, hg⟩ := key E hE hlt.le
    have hcard : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    have h2 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card A0 := by rw [hg]
    rw [hcard, hA0c] at h2
    omega
  · obtain ⟨g, hg⟩ := key E hE (by rw [hE3]; norm_num)
    have hx : x0 ∈ E.map (MulAut.conj g).toMonoidHom := by
      rw [hg]
      exact hx0
    obtain ⟨e, he, hge⟩ := hx
    refine ⟨e, he, ?_⟩
    have he' : e = g⁻¹ * x0 * g := by
      rw [← hge]
      show e = g⁻¹ * (g * e * g⁻¹) * g
      group
    rw [he']
    exact hP x0 g hPx0


private theorem g1_fixFree (hG : GOK) (v : Fin 24 → ZMod 2)
    (hv : (((g1 hG 1 : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) : v = 0 := by
  obtain ⟨-, hd0, -, -, -⟩ := KD264Gen.Co15.comp_parts Certificates.certificate10145
  have hpl := (planeOK_parts (globalOK_parts hG).2.2.2.2).2.2 1 (by norm_num)
  have hx : MRep CFSG.HardMathSupport.Dickson.I271.TabCo1.repD0 ((g1 hG 1 : ↥GA) : GL24) :=
    hd0 ▸ rep_a0Row hG hpl.1
  have hfix := CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount_fiveA_le hx
  unfold CFSG.HardMathSupport.Dickson.I271.TabMFive.fixCount at hfix
  have hsub : Subsingleton {w : Fin 24 → ZMod 2 //
      (((g1 hG 1 : ↥GA) : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ w = w} :=
    Finite.card_le_one_iff_subsingleton.1 hfix
  exact congrArg Subtype.val (@Subsingleton.elim _ hsub ⟨v, hv⟩ ⟨0, Matrix.mulVec_zero _⟩)

theorem co1FiveCubeFacts_holds : Co1FiveCubeFacts := by
  have hG : GOK := Certificates.certificate13670
  haveI : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  exact cube_facts_of (Q := Qsub) (A0 := A0 hG)
    (by rw [card_Qsub hG, factorization_card_GA_five]; norm_num) (card_A0 hG)
    (fun A hAQ hA h125 => KD264Gen.Co15.le_A0 hG Certificates.certificate10145 hAQ hA h125)
    (fun j => ∀ v : Fin 24 → ZMod 2,
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v → v = 0)
    (fun x g hx v hv => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hv
      exact fixFree_conj hx (g : GL24) v hv)
    (⟨_, rfl⟩ : g1 hG 1 ∈ A0 hG) (g1_fixFree hG)

end CFSG.LocalAnalysis.GLTheoremA.H1017.H1016M5
