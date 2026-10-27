module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bGenericHall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15CartanBorelOrth
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorelAll
public import CFSG.ClassicalGroups.Orthogonal.ComponentBorelSolvable
public import CFSG.ClassicalGroups.Orthogonal.ComponentBorelQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem noXBlock_borelPre_subtype_D
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.D m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4) :
    ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hsub hblock
  let H : Subgroup X := borelPre T Ls
  let Y' : Subgroup X := Y.map H.subtype
  have hY' : Y' ≤ H := Subgroup.map_subtype_le (H := H) Y
  have hsub' : IsSubnormal Y' H := by
    have h := CFSG.Open.IsSubnormal.map (f := H.subtype) hsub
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hblock' : InClassXBlock Y' := by
    have hx : CFSG.RankThree.PartOne.InClassX ↥Y :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hblock
    let eY : ↥Y ≃* ↥Y' :=
      Subgroup.equivMapOfInjective Y H.subtype H.subtype_injective
    have hx' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv eY hx
    exact CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hx'
  exact noXBlock_borelPre_done_D hX hLs hinv m hm Q hQ hv e hcard Y' hY' hsub' hblock'

theorem k517_4b_orth_of_setting_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.D m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1) (hQcard : 4 ≤ Q.card)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls)
    (hsolvB : Group.IsSolvable ↥(Subgroup.normalizer (U : Set ↥Ls)))
    (hcommN : IsMulCommutative
      (↥(Subgroup.normalizer (U : Set ↥Ls)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set ↥Ls)))) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  have hq2' : (q != 2) = true := bne_iff_ne.mpr hq2
  obtain ⟨Hc, hHcN, hHcpi, hHc3⟩ :=
    exists_piSubgroup_three_le_pRank_in_borel_orth (L := ↥Ls) (m := m) (Q := Q)
      hLs.1.2.2 hm hQ hv e hq hq2' hqQ hQcard hU2 hUmax
  have hset : {p : Nat.Primes | (p : Nat) != 2} = {p : Nat.Primes | (p : Nat) ≠ 2} := by
    ext p; simp
  rw [hset] at hHcpi
  have hHc : ∃ Hc : Subgroup ↥Ls, Hc ≤ Subgroup.normalizer (U : Set ↥Ls) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧ 3 ≤ CFSG.Open.pRank q Hc :=
    ⟨Hc, hHcN, hHcpi, hHc3⟩
  have hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False :=
    noXBlock_borelPre_subtype_D hX hLs.1 hTinv m hm Q hQ hv e (by
      rcases Nat.lt_or_ge Q.card 5 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl h)
  have hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
    isSolvable_gnImg_borelPre_of_borel hX hTinv hU hsolvB
  obtain ⟨hB, hHallB, hcommBY⟩ :=
    k517_4b_normalizer_data_of_mulCommutative hX hGood hLs hTinv hU hcommN
  have hBLs : (Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls).subgroupOf (gnImg T (borelPre T Ls)) ≤
      Ls.subgroupOf (gnImg T (borelPre T Ls)) := by
    intro y hy
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
  exact k517_4b_of_setting_of_hall hX hGood hLs hq hq2 hHc hU hNB hsolvY hB hHallB hcommBY hBLs

theorem k517_4b_orth_of_top_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.D m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.D m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  have hQcard : 4 ≤ Q.card := by
    have hpow : Q.card = 2 ^ Q.exponent := by
      rw [TauCeti.PrimePower.card_def, hQ]
    have h2le : 2 ≤ Q.card := by
      rw [hpow]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) Q.exponent_pos
    have hdiv : 2 ∣ Q.card := by
      rw [hpow]
      exact dvd_pow_self 2 Q.exponent_pos.ne'
    have hne2 : Q.card ≠ 2 := by
      intro h2
      have h2' : Q.card - 1 = 1 := by omega
      exact hq.not_dvd_one (h2' ▸ hqQ)
    rcases Nat.lt_or_ge Q.card 4 with hlt | hge
    · rcases Nat.lt_or_ge Q.card 2 with h1 | h1
      · omega
      · interval_cases Q.card
        · exact absurd rfl hne2
        · exact absurd hdiv (by norm_num)
    · exact hge
  exact k517_4b_orth_of_setting_of_hall hX hGood hLs hq hq2 hm hQ e hTinv hU2 hUmax hqQ hQcard hU
    (CFSG.ClassicalGroups.Orthogonal.isSolvable_normalizer_sylow_of_component_orth
      hLs.1.2.2 m hm Q hQ hv e hQcard hUmax)
    (CFSG.ClassicalGroups.Orthogonal.isMulCommutative_normalizer_quotient_pCore_of_component_orth
      hLs.1.2.2 m hm Q hQ hv e hQcard hUmax)

end CFSG.LocalAnalysis.RankThreeUC.S15

end
