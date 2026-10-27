module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA4Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Pieces
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264LieA4

theorem exists_isPrimitiveRoot_three_of_dvd (K : Type) [Field K] [Finite K]
    (h : 3 ∣ Nat.card K - 1) : ∃ ζ : K, IsPrimitiveRoot ζ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype Kˣ := Fintype.ofFinite _
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 (by rwa [Nat.card_eq_fintype_card] at hdvd)
  exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hx)⟩

theorem isElemAbelian_map {G G' : Type} [Group G] [Group G'] (φ : G ≃* G')
    {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 E) :
    CFSG.Open.IsElemAbelian 3 (E.map φ.toMonoidHom) := by
  have hcomm : IsMulCommutative ↥(E.map φ.toMonoidHom) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    have hab := congrArg Subtype.val (hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
    simp only [Subgroup.coe_mul] at hab
    show (a : G') * b = (b : G') * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, hab]
  refine ⟨hcomm, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow, hE.2 y hy, map_one]

theorem KD264Y1KerA4_holds : KD264Y1KerA4 := by
  unfold KD264Y1KerA4 KD264Y1Kernel
  intro d _hfin _hns _hk2 _hk3 hP E hE hc
  obtain ⟨d1, hd1⟩ := d
  obtain ⟨q, rfl, h3⟩ := hP
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [CFSG.Models.card_galoisField q, TauCeti.PrimePower.card_def q]
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three_of_dvd (GaloisField q.p q.exponent)
    (by rw [hcard]; exact h3)
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hd1
  apply kerConcl_of_equiv e E
  apply kerConcl_PSL4 hζ
  · exact isElemAbelian_map e hE
  · rw [Subgroup.card_map_of_injective e.injective, hc]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
