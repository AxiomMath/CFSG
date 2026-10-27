module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.A5Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Emb
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.LemmaC
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.ModelCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Perfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Step1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Step23
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Step4
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Step5
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.ZStar

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M12Std.PropA

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Certified


theorem not_isComp_jOf_of_outer (h : StdHyp G L) (hL : IsSporadic L .M12) {t x : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hout : ¬ centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G))
    (hxL : x ∈ L) (hx2 : orderOf x = 2) (hx : Nat.card ↥(L ⊓ centralizer ({x} : Set G)) = 240) :
    ¬ Solomon78.IsCompIn (jOf L x) (centralizer ({x} : Set G)) := by
  intro ha
  obtain ⟨b, ι, hE⟩ := exists_isEmb h hL ht ht2 hout hxL hx2 hx
    (fun b => (model_of_certificate b).2.1) (model_of_certificate false).2.2
  have hF : Facts L t x := hE.facts (model_of_certificate b).1
  have hx2' : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have ht2' : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by rintro rfl; simp at hx2
  have hxt : x * t = t * x := mem_centralizer_iff.1 ht x hxL
  have hJA : Nonempty (jOf L x ≃* alternatingGroup (Fin 5)) :=
    nonempty_alt5_of_quasisimple ha.isQuasisimple
      (fun j hj => Subtype.ext (hF.J_center j j.2 fun j' hj' =>
        congrArg Subtype.val (hj ⟨j', hj'⟩)))
      hF.card_J
  have hJt : ∀ j ∈ jOf L x, t * j = j * t := fun j hj =>
    (mem_centralizer_singleton_iff.1 (hF.J_le hj).2).symm
  have hG0 : ∀ R : Subgroup G, R ≤ centralizer ({x} : Set G) ⊓ centralizer ({t} : Set G) →
      ⁅R, R⁆ = R → R ≤ jOf L x := fun R hR hRp =>
    le_of_perfect_of_card_two_pow hF.J_le hF.J_normal 4
      (by rw [hF.card_Cx, hF.card_J]; norm_num) hR hRp
  have hn : ∀ c ∈ centralizer ({x} : Set G), (jOf L x).map (MulAut.conj c).toMonoidHom = jOf L x :=
    fun c hc => map_conj_eq_of_isCompIn_alt5 hx2' hx1 ht2' hxt ha hJA hJt hG0 hF.card_Y hF.G3 hc
  have hz : ∃ z ∈ jOf L x, z ≠ 1 ∧ z * z = 1 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2
      (show 2 ∣ Nat.card ↥(jOf L x) by rw [hF.card_J]; norm_num)
    have hz' : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
    refine ⟨z, z.2, ?_, ?_⟩
    · intro h1
      rw [h1, orderOf_one] at hz'
      exact absurd hz' (by norm_num)
    · rw [← pow_two, ← hz', pow_orderOf_eq_one]
  have hN := centralizer_le_normalizer_of_normal hn hz hF.G5
  have hC := centralizer_le_of_le_normalizer h hL ht ht2 hxL hx2 hN
  obtain ⟨g, hgC, hne⟩ := exists_conj_mem_centralizer_ne h ht2
  have hw2 : orderOf (g * t * g⁻¹) = 2 := by
    rw [← SemiconjBy.orderOf_eq g
      (show SemiconjBy g t (g * t * g⁻¹) by simp [SemiconjBy, mul_assoc]), ht2]
  obtain ⟨c, -, hcx, hcJ⟩ := hF.G1 _ hgC hw2 hne
  refine hcJ ?_
  have := mem_centralizer_jOf_of_conj hF.card_J hF.card_Cx hG0 hF.G2 hx2 hC (c * g)
    (by simpa [mul_assoc] using hcx)
  simpa [mul_assoc] using this

end Certified

end CFSG.EvenSporadicStandard.M12Std
