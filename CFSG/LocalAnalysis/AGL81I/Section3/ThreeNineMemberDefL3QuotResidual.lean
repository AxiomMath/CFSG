module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.PrimeComplementQuotient
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.Quasithin.Vol2.Ch11SecE42S2d
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.GroupTheory

open CFSG.RankThreeEvenClassification.Helpers

theorem oPPrimeHull_top_eq_primeResidual {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull p (⊤ : Subgroup X) =
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual p X := by
  rw [CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_eq_closure p,
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.oPPrimeHull]
  congr 1
  ext x
  simp

theorem comap_primeComplementCore_eq_of_surjective {A B : Type} [Group A] [Finite A] [Group B]
    [Finite B] {d : ℕ} (hd : d.Prime) (f : A →* B) (hf : Function.Surjective f)
    (hker : ¬ d ∣ Nat.card f.ker) :
    (primeComplementCore (G := B) d).comap f = primeComplementCore (G := A) d := by
  refine le_antisymm ?_ ?_
  · refine le_primeComplementCore d _ ((primeComplementCore_properties B d hd).1.comap f) ?_
    exact preimage_prime_complement d hd f hf hker _ (primeComplementCore_properties B d hd).2
  · rw [← Subgroup.map_le_iff_le_comap]
    refine le_primeComplementCore d _ ((primeComplementCore_properties A d hd).1.map f hf) ?_
    exact fun hdvd => (primeComplementCore_properties A d hd).2
      (hdvd.trans (Subgroup.card_map_dvd _ f))

theorem nonempty_quot_primeComplementCore_mulEquiv {A B : Type} [Group A] [Finite A] [Group B]
    [Finite B] {d : ℕ} (hd : d.Prime) (f : A →* B) (hf : Function.Surjective f)
    (hker : ¬ d ∣ Nat.card f.ker) :
    Nonempty ((A ⧸ primeComplementCore (G := A) d) ≃*
      (B ⧸ primeComplementCore (G := B) d)) := by
  classical
  let g : A →* (B ⧸ primeComplementCore (G := B) d) :=
    (QuotientGroup.mk' (primeComplementCore (G := B) d)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hgk : g.ker = primeComplementCore (G := A) d := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact comap_primeComplementCore_eq_of_surjective hd f hf hker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

theorem nonempty_primeResidual_quot_primeComplementCore_mulEquiv {A B : Type} [Group A]
    [Finite A] [Group B] [Finite B] {d : ℕ} (hd : d.Prime) (f : A →* B)
    (hf : Function.Surjective f) (hker : ¬ d ∣ Nat.card f.ker) :
    Nonempty (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (A ⧸ primeComplementCore (G := A) d) ≃*
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (B ⧸ primeComplementCore (G := B) d)) := by
  obtain ⟨e⟩ := nonempty_quot_primeComplementCore_mulEquiv hd f hf hker
  refine ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr ?_)⟩
  exact CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_equiv d e

open scoped MatrixGroups

theorem card_PSL_two_zmod {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    Nat.card (PSL(2, ZMod p)) = p * (p ^ 2 - 1) / 2 := by
  have hp : p.Prime := Fact.out
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [Nat.card_zmod, pow_one]⟩
  rw [CFSG.GorensteinWalter.psl2_card_formula (ZMod p) hodd, Nat.card_zmod]

theorem dvd_card_PSL_two_zmod {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) : d ∣ Nat.card (PSL(2, ZMod p)) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  have h2dvd : 2 ∣ p + 1 := ⟨k + 1, by omega⟩
  have hdvd2 : d ∣ (p + 1) / 2 := by
    refine (Nat.Coprime.dvd_of_dvd_mul_left (m := 2) ?_ ?_)
    · rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h =>
        hd2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hd).mp h).symm
    · rw [Nat.mul_div_cancel' h2dvd]
      exact hdp
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using Nat.sq_sub_sq p 1
  rw [card_PSL_two_zmod hp5, hsq, show p * ((p + 1) * (p - 1)) = p * (p - 1) * (p + 1) by ring]
  rw [Nat.mul_div_assoc _ h2dvd]
  exact dvd_mul_of_dvd_right hdvd2 _

theorem primeResidual_pgl2_zmod {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hd : d.Prime)
    (hd2 : d ≠ 2) (hdp : d ∣ p + 1) :
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d (PGL(2, ZMod p)) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : IsSimpleGroup (PSL(2, ZMod p)) := CFSG.Quasithin.Vol2.Ch11.SecE.isSimpleGroup_psl hp5
  have hdvd : d ∣ Nat.card (PSL(2, ZMod p)) := dvd_card_PSL_two_zmod hp5 hd hd2 hdp
  refine le_antisymm ?_ ?_
  · refine sSup_le fun P hP x hx => ?_
    obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨x, hx⟩ : P)
    refine CFSG.GorensteinWalter.pgl2_mem_psl2Range_of_odd_orderOf (g := x) ?_
    rw [← (Subgroup.orderOf_coe (⟨x, hx⟩ : P)).symm, hk]
    exact (hd.odd_of_ne_two hd2).pow
  ·
    have htop : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (PSL(2, ZMod p)) = ⊤ := by
      haveI : (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
          (PSL(2, ZMod p))).Characteristic :=
        CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_characteristic d _
      have hne : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
          (PSL(2, ZMod p)) ≠ ⊥ := by
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdvd
        intro hbot
        have hmem : x ∈ CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
            (PSL(2, ZMod p)) := by
          have hP : IsPGroup d (Subgroup.zpowers x) :=
            IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hx, pow_one]⟩
          exact CFSG.ComponentClassification.CatalogueBPrimeJoin.pSubgroup_le_residual d _
            hP (Subgroup.mem_zpowers x)
        rw [hbot] at hmem
        rw [Subgroup.mem_bot] at hmem
        rw [hmem, orderOf_one] at hx
        exact hd.ne_one hx.symm
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
          (PSL(2, ZMod p))) with h | h
      · exact absurd h hne
      · exact h
    have hiso : Nonempty (PSL(2, ZMod p) ≃*
        ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range) :=
      ⟨(Subgroup.topEquiv (G := PSL(2, ZMod p))).symm |>.trans
        ((Subgroup.equivMapOfInjective (⊤ : Subgroup (PSL(2, ZMod p))) _
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
          (MulEquiv.subgroupCongr (MonoidHom.range_eq_map _).symm))⟩
    have htopRange : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range = ⊤ := by
      obtain ⟨e⟩ := hiso
      rw [← CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_equiv d e, htop,
        Subgroup.map_top_of_surjective _ e.surjective]
    have hmap := CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_le d
      (Subgroup.subtype (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod p)).range)
    rw [htopRange] at hmap
    intro x hx
    exact hmap (Subgroup.mem_map_of_mem
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p)).range.subtype
      (Subgroup.mem_top (⟨x, hx⟩ : ↥(Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := ZMod p)).range)))

open CFSG.RankThreeEvenClassification.Helpers in
theorem nonempty_primeResidual_pgl2_quot_mulEquiv_PSL {p d : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hd : d.Prime) (hd2 : d ≠ 2) (hdp : d ∣ p + 1) :
    Nonempty (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (PGL(2, ZMod p) ⧸ primeComplementCore (G := PGL(2, ZMod p)) d) ≃*
      PSL(2, ZMod p)) := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : IsSimpleGroup (PSL(2, ZMod p)) := CFSG.Quasithin.Vol2.Ch11.SecE.isSimpleGroup_psl hp5
  have hdvd : d ∣ Nat.card (PSL(2, ZMod p)) := dvd_card_PSL_two_zmod hp5 hd hd2 hdp
  classical
  set toPGL := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := ZMod p) with htoPGL
  set O := primeComplementCore (G := PGL(2, ZMod p)) d with hO
  haveI hOnormal : O.Normal :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section12.primeComplementCore_normal d _
  have hOcard : ¬ d ∣ Nat.card ↥O := (primeComplementCore_properties _ d hd).2
  have hcomapbot : O.comap toPGL = ⊥ := by
    haveI : (O.comap toPGL).Normal := Subgroup.Normal.comap hOnormal toPGL
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.comap toPGL) with h | h
    · refine (Subgroup.map_eq_bot_iff_of_injective _ (f := toPGL)
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).mp ?_
      rw [h, Subgroup.map_bot]
    · exfalso
      have hcard : d ∣ Nat.card ↥(O.comap toPGL) := by
        rw [h, Subgroup.card_top]
        exact hdvd
      refine hOcard (hcard.trans ?_)
      calc Nat.card ↥(O.comap toPGL)
          = Nat.card ↥((O.comap toPGL).map toPGL) :=
            (Subgroup.card_map_of_injective
              Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm
        _ = Nat.card ↥(toPGL.range ⊓ O) := by rw [Subgroup.map_comap_eq]
        _ ∣ Nat.card ↥O := Subgroup.card_dvd_of_le inf_le_right
  have hprime : CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
      (PGL(2, ZMod p)) = toPGL.range := by
    rw [htoPGL]
    exact primeResidual_pgl2_zmod hp5 hd hd2 hdp
  have hsurj : Subgroup.map (QuotientGroup.mk' O)
      (CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d (PGL(2, ZMod p))) =
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (PGL(2, ZMod p) ⧸ O) :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual_map_surjective d
      (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  have hkerbot : ((QuotientGroup.mk' O).comp toPGL).ker = ⊥ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hcomapbot
  have hrange : ((QuotientGroup.mk' O).comp toPGL).range =
      CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
        (PGL(2, ZMod p) ⧸ O) := by
    rw [MonoidHom.range_comp]
    rw [show toPGL.range = CFSG.ComponentClassification.CatalogueBPrimeJoin.primeResidual d
      (PGL(2, ZMod p)) from hprime.symm]
    exact hsurj
  refine ⟨(MulEquiv.subgroupCongr hrange).symm |>.trans ?_⟩
  exact (QuotientGroup.quotientKerEquivRange ((QuotientGroup.mk' O).comp toPGL)).symm |>.trans
    ((QuotientGroup.quotientMulEquivOfEq hkerbot).trans QuotientGroup.quotientBot)

end CFSG.GroupTheory
