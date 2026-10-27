module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PlaneCardAuxDescent
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG.RankThree.Classical2 CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TwCardAux
open Matrix
open scoped MatrixGroups

section


theorem exists_mem_unitarySet_orderOf {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hpq : p ∣ (ℓ ^ f) ^ 2 + 1) :
    ∃ Y ∈ unitarySet (Ω := Ω) (ℓ ^ f) 4, orderOf Y = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKcard, hKmem⟩ := mnSyl_exists_subfield (Ω := Ω) (ℓ := ℓ) hf
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have hrange : ∀ c : Ω, c ∈ Set.range K.subtype ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [← hKmem]
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨c, h⟩, rfl⟩⟩
  have hinj : Function.Injective
      (GeneralLinearGroup.map K.subtype : GL (Fin 4) K →* GL (Fin 4) Ω) :=
    fun A B h => Units.ext (Matrix.map_injective K.subtype_injective (congrArg Units.val h))
  haveI : CharP K ℓ := (RingHom.charP_iff K.subtype K.subtype_injective ℓ).mpr inferInstance
  have himg := mnSyl_image_SUid K.subtype hrange 4 (ℓ := ℓ) (f := f)
  have hcardeq : Nat.card (unitarySet (Ω := Ω) (ℓ ^ f) 4 : Set (GL (Fin 4) Ω)) =
      Nat.card (SUid (unitaryInvolution K ℓ f) 4) := by
    rw [← himg, Nat.card_image_of_injective hinj, SetLike.coe_sort_coe]
  have hint := card_unitarySet_int (Ω := Ω) (ℓ := ℓ) hf (n := 4) (by norm_num)
  have hdvdZ : (p : ℤ) ∣ (Nat.card (unitarySet (Ω := Ω) (ℓ ^ f) 4 : Set (GL (Fin 4) Ω)) : ℤ) := by
    rw [hint]
    refine Dvd.dvd.mul_left ?_ _
    rw [show Finset.Icc 2 4 = {2, 3, 4} by decide, Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    refine Dvd.dvd.mul_left ?_ _
    have hp' : (p : ℤ) ∣ (((ℓ ^ f : ℕ) : ℤ)) ^ 2 + 1 := by
      have := Int.natCast_dvd_natCast.2 hpq
      push_cast at this
      exact this
    have h4 : (((ℓ ^ f : ℕ) : ℤ)) ^ 4 - (-1) ^ 4 =
        (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1) := by ring
    rw [h4]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hp' _) _
  have hdvd : p ∣ Nat.card (SUid (unitaryInvolution K ℓ f) 4) := by
    rw [← hcardeq]
    exact Int.natCast_dvd_natCast.1 hdvdZ
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := SUid (unitaryInvolution K ℓ f) 4) p hdvd
  refine ⟨GeneralLinearGroup.map K.subtype (y : GL (Fin 4) K), ?_, ?_⟩
  · rw [← himg]
    exact ⟨y, y.2, rfl⟩
  · rw [orderOf_injective _ hinj, Subgroup.orderOf_coe, hy]

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
