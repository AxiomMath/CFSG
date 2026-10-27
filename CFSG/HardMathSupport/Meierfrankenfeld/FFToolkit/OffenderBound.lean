module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {L E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(L ⊔ E : Subgroup G) * Nat.card ↥(L ⊓ E : Subgroup G) =
      Nat.card L * Nat.card E := by
  rw [sup_comm, inf_comm, mul_comm (Nat.card L)]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hEN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hEN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient E L hEN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf E)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (L.subgroupOf (E ⊔ L))
  have h3 : Nat.card (L.subgroupOf E) = Nat.card (E ⊓ L : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (L.subgroupOf (E ⊔ L)) = Nat.card L :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem inf_centralizer_eq_bot_of_isIrrOn {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hirr : IsIrrOn L) (hEel : CFSG.Quasithin.IsElemAbelian2 E) :
    E ⊓ Subgroup.centralizer (L : Set (MulAut W)) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxE, hxC⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_commutes_of_sq_eq_one hW hirr ?_ ?_
  · intro l hl
    exact Subgroup.mem_centralizer_iff.1 hxC l hl
  · have := hEel.2 x hxE
    rwa [sq] at this

theorem odd_card_center_of_isIrrOn {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hirr : IsIrrOn L) :
    Odd (Nat.card (Subgroup.center ↥L)) := by
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W ≃ W))
      (fun f g h => MulEquiv.ext fun w => congrArg (fun e : W ≃ W => e w) h)
  rcases Nat.even_or_odd (Nat.card (Subgroup.center ↥L)) with he | ho
  · exfalso
    have : Fintype ↥(Subgroup.center ↥L) := Fintype.ofFinite _
    have h2 : 2 ∣ Fintype.card ↥(Subgroup.center ↥L) := by
      rw [← Nat.card_eq_fintype_card]
      exact even_iff_two_dvd.mp he
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card (G := ↥(Subgroup.center ↥L)) 2 h2
    have hcomm : ∀ l ∈ L, l * ((z : ↥L) : MulAut W) = ((z : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 z.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hsq : (z : ↥(Subgroup.center ↥L)) ^ 2 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    have hc2 : ((z : ↥L) : MulAut W) * ((z : ↥L) : MulAut W) = 1 := by
      have := congrArg (fun x : ↥(Subgroup.center ↥L) => ((x : ↥L) : MulAut W)) hsq
      simpa [sq] using this
    have hc1 := eq_one_of_commutes_of_sq_eq_one hW hirr hcomm hc2
    have hz1 : z = 1 := Subtype.ext (Subtype.ext (by simpa using hc1))
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  · exact ho

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
