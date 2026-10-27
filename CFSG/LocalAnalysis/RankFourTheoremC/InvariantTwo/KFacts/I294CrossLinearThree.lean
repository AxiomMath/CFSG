module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.Adapters.LinearCatalogStated
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryO.GL3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup

theorem isMulCommutative_sylow_statedProj_gl3 {K : Type} [Field K] [Finite K] {r : ℕ}
    (hr : r.Prime) (h5 : 5 ≤ r) (hrK : ¬ r ∣ Nat.card K) (H : Subgroup (GL (Fin 3) K))
    (R : Sylow r (StatedProj H)) : IsMulCommutative (R : Subgroup (StatedProj H)) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective
    (f := QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf H))
    (QuotientGroup.mk'_surjective _) r R
  rw [Sylow.coe_mapSurjective]
  have h1 : IsMulCommutative ((S : Subgroup H).map H.subtype) :=
    CFSG.SignalizerFunctorTheorem.McBride.UnitaryO.isMulCommutative_of_isPGroup_gl3 hr h5 hrK
      (S.isPGroup'.map _)
  have h2 : IsMulCommutative (S : Subgroup H) :=
    .of_setLike_mul_comm fun a ha b hb => Subtype.ext
      (setLike_mul_comm (s := (S : Subgroup H).map H.subtype) ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  infer_instance

theorem crossSylowAbelianAt_linearTwo {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) : CrossSylowAbelianAt ⟨.A 2 q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => isMulCommutative_sylow_statedProj_gl3 hp hp5 hpK (StatedSL 3 K) R) P

theorem crossSylowAbelianAt_unitaryTwo {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) :
    CrossSylowAbelianAt ⟨.twistedA 2 q, hv⟩ := by
  intro p hp hp5 hdp L _ _ hs ⟨e⟩ P
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hdp' : q.p ≠ p := by simpa using hdp
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1
      (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))).symm
  exact isMulCommutative_sylow_of_mulEquiv e'
    (fun R => isMulCommutative_sylow_statedProj_gl3 hp hp5 hpK (StatedSU 3 (q.p ^ q.exponent) K)
      R) P

theorem crossAt_linearTwo {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) :
    CrossAt ⟨.A 2 q, hv⟩ :=
  crossAt_of_sylowAbelian (crossSylowAbelianAt_linearTwo hv)

theorem crossAt_unitaryTwo {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) : CrossAt ⟨.twistedA 2 q, hv⟩ :=
  crossAt_of_sylowAbelian (crossSylowAbelianAt_unitaryTwo hv)

end CFSG.LocalAnalysis.RankFourTheoremC
