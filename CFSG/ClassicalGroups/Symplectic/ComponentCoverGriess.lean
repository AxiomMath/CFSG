module

public import CFSG.RankThree.GF2n.Tim78a.GriessSpMultiplier
public import CFSG.ClassicalGroups.Symplectic.BorelSolvable
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bSpHall
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bGenericHall

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem exists_mulEquiv_statedSp_of_component_B
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m f : ℕ} (hm : 3 <= m) (hf : 1 <= f) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.B m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : (m, f) ≠ (3, 1)) :
    Nonempty (L ≃* StatedSp m (GaloisField 2 f)) := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := inferInstance
  have hcardF : Nat.card F = Q.card := by
    rw [show Nat.card F = 2 ^ f from GaloisField.card 2 f (by omega),
      TauCeti.PrimePower.card_def, hQ, hQexp]
  obtain ⟨eB⟩ :=
    CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
      (r := m) (q := Q) hv hQ hm hcardF
  have hcenter : (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf (StatedSp m F) = ⊥ := by
    have h := center_statedSp_eq_bot_of_charP_two (m := m) (F := F) (by omega)
    rwa [show Subgroup.center (StatedSp m F) =
        (StatedScalars (Fin m ⊕ Fin m) F).subgroupOf (StatedSp m F) from by
      rw [show StatedSp m F = TauCeti.GLSymplectic (Fin m) F from
        statedSp_eq_GLSymplectic (n := m) (K := F)]
      exact center_GLSymplectic_eq (n := m) (K := F)] at h
  let eProj : StatedProj (StatedSp m F) ≃* StatedSp m F :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientBot (G := StatedSp m F))
  let ρL : L →* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  let φ : L →* StatedSp m F := eProj.toMonoidHom.comp (eB.symm.toMonoidHom.comp ρL)
  have hφsurj : Function.Surjective φ :=
    eProj.surjective.comp
      (eB.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)))
  have hkerφ : φ.ker = Subgroup.center L := by
    have h1 : φ.ker = (eB.symm.toMonoidHom.comp ρL).ker :=
      MonoidHom.ker_comp_of_injective _ _ eProj.injective
    rw [h1, MonoidHom.ker_comp_of_injective _ _ eB.symm.injective]
    show (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcen : φ.ker ≤ Subgroup.center L := le_of_eq hkerφ
  have hcom : φ.ker ≤ commutator L := by
    rw [hL.1]
    exact le_top
  have h11 : (m, f) ≠ (1, 1) := by
    rintro ⟨rfl, rfl⟩
    omega
  have h12 : (m, f) ≠ (1, 2) := by
    rintro ⟨rfl, rfl⟩
    omega
  have h21 : (m, f) ≠ (2, 1) := by
    rintro ⟨rfl, rfl⟩
    omega
  have hkerbot : φ.ker = ⊥ :=
    CFSG.RankThree.GF2n.Tim79a.griessSpMultiplierStatement_holds
      m f (by omega) hf h11 h12 h21 hne L φ hφsurj hcen hcom
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact hkerbot
  exact ⟨MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩⟩

theorem isSolvable_normalizer_sylow_of_component_B
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m f : ℕ} (hm : 3 <= m) (hf : 1 <= f) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.B m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : (m, f) ≠ (3, 1))
    {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := inferInstance
  obtain ⟨eL⟩ := exists_mulEquiv_statedSp_of_component_B hL hm hf hQ hQexp (hv := hv) e hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := F) 2 m
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent m F) ⊤ :=
    hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  have hUsylE : CFSG.QuasithinUnique.IsSylowTwoOf (U.map eL.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eL hUmax
    rwa [Subgroup.map_top_of_surjective _ eL.surjective] at h
  obtain ⟨g, -, hg⟩ := hUsyl.exists_conj hUsylE
  have hN : Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup (StatedSp m F)) :
        Set (StatedSp m F)) =
      (Subgroup.normalizer (unipotent m F : Set (StatedSp m F))).map
        (MulAut.conj g).toMonoidHom := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (unipotent m F) (MulAut.conj g)]
  haveI hNUstd : Group.IsSolvable
      ↥(Subgroup.normalizer (unipotent m F : Set (StatedSp m F))) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent
      (r := m) (K := F)]
    exact isSolvable_borel_sp hm
  haveI hNE : Group.IsSolvable ↥(Subgroup.normalizer
      ((U.map eL.toMonoidHom : Subgroup (StatedSp m F)) : Set (StatedSp m F))) := by
    rw [hN]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective
        (Subgroup.normalizer (unipotent m F : Set (StatedSp m F)))
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eL
  haveI : Group.IsSolvable ↥((Subgroup.normalizer (U : Set L)).map eL.toMonoidHom) :=
    hmap.symm ▸ hNE
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L))
      eL.toMonoidHom eL.injective).toMonoidHom)
    (MulEquiv.injective _)

theorem isMulCommutative_normalizer_quotient_pCore_of_component_B
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m f : ℕ} (hm : 3 <= m) (hf : 1 <= f) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.B m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : (m, f) ≠ (3, 1))
    {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := inferInstance
  obtain ⟨eL⟩ := exists_mulEquiv_statedSp_of_component_B hL hm hf hQ hQexp (hv := hv) e hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := F) 2 m
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent m F) ⊤ :=
    hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  have hUsylE : CFSG.QuasithinUnique.IsSylowTwoOf (U.map eL.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eL hUmax
    rwa [Subgroup.map_top_of_surjective _ eL.surjective] at h
  obtain ⟨g, -, hg⟩ := hUsyl.exists_conj hUsylE
  let B : Subgroup (StatedSp m F) :=
    Subgroup.normalizer (unipotent m F : Set (StatedSp m F))
  have hN : Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup (StatedSp m F)) :
        Set (StatedSp m F)) = B.map (MulAut.conj g).toMonoidHom := by
    dsimp only [B]
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (unipotent m F) (MulAut.conj g)]
  have hcommB : IsMulCommutative (↥B ⧸ CFSG.pCore 2 ↥B) :=
    isMulCommutative_borel_quotient_sp (m := m) (F := F) hm B rfl
  have hcommConj : IsMulCommutative
      (↥(B.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(B.map (MulAut.conj g).toMonoidHom)) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      (Subgroup.equivMapOfInjective B (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom
      (MulEquiv.surjective _) hcommB
  have hcommNE : IsMulCommutative
      (↥(Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup (StatedSp m F)) :
          Set (StatedSp m F))) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer ((U.map eL.toMonoidHom :
          Subgroup (StatedSp m F)) : Set (StatedSp m F)))) := by
    rw [hN]
    exact hcommConj
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eL
  let eN : ↥(Subgroup.normalizer ((U.map eL.toMonoidHom : Subgroup (StatedSp m F)) :
      Set (StatedSp m F))) ≃* ↥(Subgroup.normalizer (U : Set L)) :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L)) eL.toMonoidHom
        eL.injective).symm
  exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
    eN.toMonoidHom eN.surjective hcommNE

theorem exists_hc_component_B
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m f : ℕ} (hm : 3 <= m) (hf : 1 <= f) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hQexp : Q.exponent = f)
    {hv : (TauCeti.LieTypeIndex.B m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hne : (m, f) ≠ (3, 1))
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Nat.card (GaloisField 2 f) - 1) (hQcard : 2 <= f)
    {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ Hc : Subgroup L, Hc ≤ Subgroup.normalizer (U : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 <= CFSG.Open.pRank q Hc := by
  classical
  let F := GaloisField 2 f
  haveI : CharP F 2 := inferInstance
  obtain ⟨eL⟩ := exists_mulEquiv_statedSp_of_component_B hL hm hf hQ hQexp (hv := hv) e hne
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hTrank : 3 ≤ CFSG.Open.pRank q (TauCeti.GLSymplecticFin.diagonalTorus F m) :=
    three_le_pRank_diagonalTorus_sp (m := m) hm hq hdvd
  obtain ⟨E, hET, hEea, hEcard⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
      (p := q) (H := TauCeti.GLSymplecticFin.diagonalTorus F m) (k := 3) hTrank
  let Esub : Subgroup (TauCeti.GLSymplecticFin.diagonalTorus F m) :=
    E.subgroupOf (TauCeti.GLSymplecticFin.diagonalTorus F m)
  have hEsub_ea : CFSG.Open.IsElemAbelian q Esub :=
    hEea.subgroupOf (TauCeti.GLSymplecticFin.diagonalTorus F m)
  have hEsub_card : Nat.card Esub = q ^ 3 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv
  let P : Subgroup (Fin m → Fˣ) :=
    Esub.map (TauCeti.GLSymplecticFin.diagonalTorusEquiv F m).symm.toMonoidHom
  have hPea : CFSG.Open.IsElemAbelian q P :=
    hEsub_ea.map (TauCeti.GLSymplecticFin.diagonalTorusEquiv F m).symm.toMonoidHom
  have hPcard : Nat.card P = q ^ 3 := by
    rw [Subgroup.card_map_of_injective
      (TauCeti.GLSymplecticFin.diagonalTorusEquiv F m).symm.injective, hEsub_card]
  let E' : Subgroup (StatedSp m F) :=
    P.map (SymplecticTorusWeyl.torusHom (r := m) (k := F))
  have hE'ea : CFSG.Open.IsElemAbelian q E' :=
    hPea.map (SymplecticTorusWeyl.torusHom (r := m) (k := F))
  have hE'card : Nat.card E' = q ^ 3 := by
    rw [Subgroup.card_map_of_injective
      (SymplecticTorusWeyl.torusHom_injective (r := m) (k := F)), hPcard]
  have hE'le_torus : E' ≤ SymplecticTorusWeyl.torus m F := by
    rintro x hx
    obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact SymplecticTorusWeyl.torusHom_mem_torus p
  have hE'norm : E' ≤ Subgroup.normalizer (unipotent m F : Set (StatedSp m F)) := by
    have h3 : SymplecticTorusWeyl.torus m F ≤
        Subgroup.normalizer (unipotent m F : Set (StatedSp m F)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
      exact torus_le_borelSubgroup
    exact hE'le_torus.trans h3
  obtain ⟨P₀, hP₀⟩ := exists_sylow_unipotent (K := F) 2 m
  have hUsyl : CFSG.QuasithinUnique.IsSylowTwoOf (unipotent m F) ⊤ :=
    hP₀ ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P₀
  let π : StatedSp m F →* L := eL.symm.toMonoidHom
  let U₀ : Subgroup L := (unipotent m F).map π
  have hU₀syl : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eL.symm hUsyl
    rwa [Subgroup.map_top_of_surjective _ eL.symm.surjective] at h
  obtain ⟨g, -, hg⟩ := hU₀syl.exists_conj hUmax
  let ψ : StatedSp m F →* L := (MulAut.conj g).toMonoidHom.comp π
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g).injective.comp eL.symm.injective
  have hmapψ : (unipotent m F).map ψ = U := by
    rw [← Subgroup.map_map]
    exact hg.symm
  have hmapea : CFSG.Open.IsElemAbelian q (E'.map ψ) := hE'ea.map ψ
  have hmapcard : Nat.card (E'.map ψ) = q ^ 3 := by
    rw [Subgroup.card_map_of_injective hψinj, hE'card]
  refine ⟨E'.map ψ, ?_, ?_, ?_⟩
  ·
    have h1 : E'.map ψ ≤
        (Subgroup.normalizer (unipotent m F : Set (StatedSp m F))).map ψ :=
      Subgroup.map_mono hE'norm
    have h2 : (Subgroup.normalizer (unipotent m F : Set (StatedSp m F))).map ψ ≤
        Subgroup.normalizer ((unipotent m F).map ψ : Set L) :=
      Subgroup.le_normalizer_map ψ
    rw [hmapψ] at h2
    exact h1.trans h2
  ·
    intro p hp hp2
    have hHodd : Odd (Nat.card (E'.map ψ)) := by
      rw [hmapcard]
      exact hqodd.pow
    have h2 : ¬ 2 ∣ Nat.card (E'.map ψ) := fun hd =>
      (Nat.not_even_iff_odd.mpr hHodd) (even_iff_two_dvd.mpr hd)
    rw [hp2] at hp
    exact h2 hp
  ·
    exact CFSG.SectionRank.le_pRank hq.one_lt le_rfl hmapea hmapcard

end CFSG.ClassicalGroups.Symplectic

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem k517_4b_sp_of_top_of_hall_uncond
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : Nat} (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2) {m : Nat} (hm : 3 <= m) {Q : TauCeti.PrimePower}
    (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.B m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.B m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1) (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hf : 2 ≤ Q.exponent := by
    rcases Nat.lt_or_ge Q.exponent 2 with hlt | hge
    · have hpos : 0 < Q.exponent := Q.exponent_pos
      have he : Q.exponent = 1 := by omega
      have hcard2 : Q.card = 2 := by rw [hQcardpow, he]; norm_num
      have hdvd1 : q ∣ 1 := by
        rw [hcard2] at hqQ
        simpa using hqQ
      exact absurd hdvd1 hq.not_dvd_one
    · exact hge
  have hne : (m, Q.exponent) ≠ (3, 1) := by
    intro h
    have h1 : Q.exponent = 1 := congrArg Prod.snd h
    omega
  have hdvdF : q ∣ Nat.card (GaloisField 2 Q.exponent) - 1 := by
    rw [GaloisField.card 2 Q.exponent Q.exponent_pos.ne', ← hQcardpow]
    exact hqQ
  have hHc := CFSG.ClassicalGroups.Symplectic.exists_hc_component_B
    (L := ↥Ls) (m := m) (f := Q.exponent) (Q := Q) (hv := hv) (e := e) (q := q)
    (U := U) hLs.1.2.2 hm (by omega) hQ rfl hne hq hq2 hdvdF hf hUmax
  have hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False :=
    noXBlock_borelPre_subtype_sp hX hLs.1 hTinv m hm Q hQ hv e (by
      rcases Nat.lt_or_ge 2 Q.exponent with h2 | h2
      · left
        rw [hQcardpow]
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) (by omega)
      · right
        have he : Q.exponent = 2 := by omega
        rw [hQcardpow, he]
        norm_num)
  have hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
    isSolvable_gnImg_borelPre_of_borel hX hTinv hU
      (CFSG.ClassicalGroups.Symplectic.isSolvable_normalizer_sylow_of_component_B
        (L := ↥Ls) (m := m) (f := Q.exponent) (Q := Q) (hv := hv) (e := e)
        hLs.1.2.2 hm (by omega) hQ rfl hne hUmax)
  have hcomm : IsMulCommutative
      (↥(Subgroup.normalizer (U : Set ↥Ls)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set ↥Ls))) :=
    CFSG.ClassicalGroups.Symplectic.isMulCommutative_normalizer_quotient_pCore_of_component_B
      (L := ↥Ls) (m := m) (f := Q.exponent) (Q := Q) (hv := hv) (e := e)
      hLs.1.2.2 hm (by omega) hQ rfl hne hUmax
  let Y : Subgroup (X ⧸ gnC T) := gnImg T (borelPre T Ls)
  let Bstar : Subgroup (X ⧸ gnC T) :=
    Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) ⊓ Ls
  let BY : Subgroup ↥Y := Bstar.subgroupOf Y
  obtain ⟨hB, hHallB, hcommBY⟩ :=
    k517_4b_normalizer_data_of_mulCommutative hX hGood hLs hTinv hU hcomm
  have hBLs : BY ≤ Ls.subgroupOf Y := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
  exact k517_4b_of_setting_of_hall hX hGood hLs hq hq2 hHc hU hNB hsolvY
    (B := BY) hB hHallB hcommBY hBLs

end CFSG.LocalAnalysis.RankThreeUC.S15

end
