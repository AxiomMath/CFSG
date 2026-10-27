module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.AtlasOrders2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.L5Three.Dim5

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem nonempty_equiv_G52_of_isL5Two {X : Type} [Group X] (h : IsL5Two X) :
    Nonempty (X ≃* GL (Fin 5) (ZMod 2)) := by
  obtain ⟨⟨i, hv⟩, ⟨q, hq2, hd⟩, ⟨e⟩⟩ := h
  have hd' : i = .A 4 q := hd
  subst hd'
  have hp : q.p = 2 ∧ q.exponent = 1 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hq2, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.ne_of_gt q.exponent_pos)
    have h2 : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp hdvd
    have hpow : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def]; exact hq2
    rw [h2] at hpow
    exact ⟨h2, (Nat.prime_two.pow_eq_iff.mp hpow).2⟩
  have hmod := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA 4 q hv e
  rw [hp.1, hp.2] at hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.PSLN.psl_equiv_of_stated (F := ZMod 2) 5 2 1
    (by norm_num) (by rw [Nat.card_zmod, pow_one]) hmod
  exact ⟨e1.trans CFSG.GroupTheory.GL52.G52EquivPSL.symm⟩

theorem embG52_bijective {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Module.finrank (ZMod 2) V = 5) :
    Function.Bijective (CFSG.AGLEmbeddingD2.McLaughlin.L5Three.embG52 hV.le) := by
  have hinj := CFSG.AGLEmbeddingD2.McLaughlin.L5Three.embG52_injective hV.le
  refine ⟨hinj, ?_⟩
  have := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card (V ≃ₗ[ZMod 2] V) = Nat.card (GL (Fin 5) (ZMod 2)) := by
    rw [CFSG.AGLEmbeddingD2.McLaughlin.L5Three.card_linEquiv_five hV,
      CFSG.GroupTheory.GL52.card_G52]
    norm_num
  exact (Function.Injective.bijective_of_nat_card_le hinj (by omega)).2

theorem card_le_of_threePrime_isL5Two {X : Type} [Group X] (h : IsL5Two X) (H : Subgroup X)
    (hH : ¬ 3 ∣ Nat.card H) : Nat.card H ≤ 1024 := by
  obtain ⟨e⟩ := nonempty_equiv_G52_of_isL5Two h
  have hV : Module.finrank (ZMod 2) (GaloisField 2 5) = 5 := GaloisField.finrank 2 (by norm_num)
  have : Fintype (GaloisField 2 5) := Fintype.ofFinite _
  let φ : X ≃* (GaloisField 2 5 ≃ₗ[ZMod 2] GaloisField 2 5) :=
    e.trans (MulEquiv.ofBijective _ (embG52_bijective hV)).symm
  have hcard : Nat.card (H.map φ.toMonoidHom) = Nat.card H :=
    Subgroup.card_map_of_injective φ.injective
  have := CFSG.AGLEmbeddingD2.McLaughlin.L5Three.threeBound_five (GaloisField 2 5) hV
    (H.map φ.toMonoidHom) (by rw [hcard]; exact hH)
  rwa [hcard] at this

theorem l5Atlas_proved : L5Atlas := fun X _ hX =>
  ⟨card_of_isL5Two hX, card_le_of_threePrime_isL5Two hX⟩

end CFSG.AGLEmbeddingD2.McLaughlin
