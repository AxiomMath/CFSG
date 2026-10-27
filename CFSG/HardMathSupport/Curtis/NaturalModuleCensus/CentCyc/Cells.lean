module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Glue
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Out
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Main
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.NodeWitnesses.Escapes
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeG2
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbBlockDefs

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.OutStructure
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus

@[expose] def CentCycCell (𝔉 : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParabE L J →
    𝔉 (↥L ⧸ Subgroup.center ↥L) →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ J ⊔ Subgroup.centralizer (L : Set Y) →
    (∀ A : Subgroup Y, A ≤ D → IsPGroup p A → IsCyclic A) →
    (∀ V : Subgroup Y, V ≤ J → ⁅V, V⁆ = V → ∀ k : ℕ, p ^ k ∣ Nat.card V →
      p ^ k ∣ Nat.card D) →
    ∀ x ∈ D, x ^ p = 1 → x ∉ Subgroup.centralizer (L : Set Y) →
    (∀ W : Subgroup Y, W ≤ L → ⁅W, W⁆ = W → W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥) →
    ∀ E : Subgroup Y, E ≤ Subgroup.normalizer (L : Set Y) → IsPGroup p E →
      (∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ L ⊔ Subgroup.centralizer (L : Set Y)) ∧
      (E ≤ J ⊔ Subgroup.centralizer (L : Set Y) → E ≤ Subgroup.centralizer (D : Set Y) →
        ∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ Subgroup.centralizer (L : Set Y))

section Generic

theorem exists_cover_mod_centralizer {Y : Type*} [Group Y] [Finite Y] {M C : Subgroup Y}
    {X : Type*} [Group X] (ρ : ↥M →* X) (hρker : ∀ g : ↥M, ρ g = 1 ↔ (g : Y) ∈ C)
    {E : Subgroup Y} (hEM : E ≤ M) (hcyc : IsCyclic ↥((E.subgroupOf M).map ρ)) :
    ∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ C := by
  obtain ⟨u, hu, hcov⟩ := exists_cover_of_cyclic_image ρ hcyc
  refine ⟨(u : Y), Subgroup.mem_subgroupOf.1 hu, fun e he => ?_⟩
  obtain ⟨k, hk⟩ := hcov ⟨e, hEM he⟩ (Subgroup.mem_subgroupOf.2 he)
  exact ⟨k, (hρker _).1 hk⟩

theorem isCyclic_of_pGroup_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ^ 2 ∣ Nat.card G) {A : Subgroup G} (hA : IsPGroup p A) : IsCyclic A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra hlt
    apply h
    have h1 : p ^ 2 ∣ p ^ n := pow_dvd_pow p (by omega)
    exact h1.trans (hn ▸ A.card_subgroup_dvd_card)
  interval_cases n
  · have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 (by simpa using hn)).1
    infer_instance
  · exact isCyclic_of_prime_card (by simpa using hn)

theorem center_bar_eq_bot {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} (h : CompParabE L J) :
    Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr h.comp.2.2.1
  exact Group.IsPerfect.center_quotient_center_eq_bot _

theorem isCyclic_of_centCycBar_hub {X : Type} [Group X] [Finite X] {J : Subgroup X} {p : ℕ}
    {v : X} (h : CentCycBar J p v) (hH : PerfectJoinHub p X) {A : Subgroup X} (hAJ : A ≤ J)
    (hA : IsPGroup p A) : IsCyclic A := by
  obtain ⟨S₀, hS₀, -⟩ := h.parab
  exact h.cyc (perfectJoin J) (perfectJoin_le J) (perfectJoin_perfect J) A
    (hH S₀ J hS₀ A hAJ hA) hA

theorem false_of_centCycBar_escapes {X : Type} [Group X] [Finite X] {J : Subgroup X} {p : ℕ}
    {v : X} (h : CentCycBar J p v) (hZ : Subgroup.center X = ⊥)
    (hE : CentralizerEscapes p X) : False := by
  obtain ⟨S₀, hS₀, hne⟩ := h.parab
  have hv : v ∉ Subgroup.center X := by
    rw [hZ, Subgroup.mem_bot]
    exact h.ne_one
  obtain ⟨g, -, P, hP, hPc, hPJ⟩ := hE S₀ J hS₀ hne h.ne_top h.cyc v h.join h.pow hv
  apply hPJ
  have hPbot : P = ⊥ := h.triv_conj g P (fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    rw [hk]
    exact (hPc x hx).symm) hP
  rw [hPbot]
  exact bot_le

theorem false_of_centCycBar_torus_b {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : IsLieOfTorus IdxB p X) {J : Subgroup X} {v : X}
    (h : CentCycBar J p v) : False := by
  obtain ⟨⟨d, hv⟩, hPd, hnt, ⟨e⟩⟩ := hX
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd
    have hnt' : q.card ≠ 2 ∧ p ∣ q.card - 1 := by
      simpa [IndexTorusFree] using hnt
    have hr : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
    have hq4 : 4 ≤ q.card := by
      rcases ToralCensus.card_eq_two_or_four_le_of_p_eq_two hq2 with h2 | h4
      · exact absurd h2 hnt'.1
      · exact h4
    have hmodel : StatedClassicalModel X .PSp r 2 q.exponent := by
      by_cases h2 : r = 2
      · subst h2
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
        rwa [hq2] at hm
      · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
          (by omega) e
        rwa [hq2] at hm
    obtain ⟨-, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hmodel
    have hcardK : Nat.card K = q.card := by
      rw [hcard, TauCeti.PrimePower.card_def, hq2]
    have hf1 : 1 ≤ q.exponent := q.exponent_pos
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf1
        hcard
    have : NeZero r := ⟨by omega⟩
    have hbij := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.even_symplectic_semilinear_normal_form
      (r := r) (K := K) hf1 hcard).1
    let π : StatedSp r K ≃* StatedProj (StatedSp r K) := MulEquiv.ofBijective _ hbij
    have hfin : Finite (StatedSp r K) := by
      have : Finite (StatedProj (StatedSp r K)) := Finite.of_equiv _ e'.toEquiv
      exact Finite.of_equiv _ π.toEquiv.symm
    let ee : X ≃* StatedSp r K := e'.trans π.symm
    exact false_of_fixBarData_symplectic (by omega) (by omega) hp hp5
      (by rw [hcardK]; exact hnt'.2) (h.toFixBarData.map_mulEquiv ee)
  | _ => exact hPd.elim

theorem perfectJoinHub_of_torusFree_classical {P : TauCeti.LieTypeIndex → Prop}
    (hP : P = IdxA ∨ P = IdxTwistedA ∨ P = IdxB ∨ P = IdxD ∨ P = IdxTwistedD) {X : Type}
    [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hX : IsLieOfTorusFree P p X) :
    PerfectJoinHub p X := by
  obtain ⟨d, hPd, ht, ⟨e⟩⟩ := hX
  obtain ⟨hd, hG2⟩ := ToralCensus.classical_index hP hPd
  exact perfectJoinHub_of_classicalIndex d hd hG2 e hp hp5 ht

theorem centCycCell_of_core {𝔉 : (X : Type) → [Group X] → Prop}
    (hOut : ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParabE L J →
      𝔉 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
        OutPChain p (↥L ⧸ Subgroup.center ↥L))
    (hcyc : ∀ (Y : Type) [Group Y] [Finite Y] (L J : Subgroup Y), CompParabE L J →
      𝔉 (↥L ⧸ Subgroup.center ↥L) → ∀ p : ℕ, p.Prime → 5 ≤ p →
        ∀ v : ↥L ⧸ Subgroup.center ↥L, CentCycBar (jBar L J) p v →
          ∀ A : Subgroup (↥L ⧸ Subgroup.center ↥L), A ≤ jBar L J → IsPGroup p A → IsCyclic A) :
    CentCycCell 𝔉 := by
  intro Y _ _ L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hCP.comp.2.2.1
  refine ⟨exists_cyclic_mod_of_outPChain (hOut Y L J hCP hX p hp hp5) hEp hEN, fun hEJ _ => ?_⟩
  obtain ⟨ρ, hρker, hρJ, v, hv⟩ := exists_centCycBar hCP hp hDp hDJ hDcyc hDpart hxD hxp hxC hxW
  refine exists_cover_mod_centralizer ρ hρker hEJ ?_
  refine hcyc Y L J hCP hX p hp hp5 v hv _ ?_ ?_
  · rintro _ ⟨g, -, rfl⟩
    exact hρJ g
  · exact (hEp.comap_subtype (K := J ⊔ Subgroup.centralizer (L : Set Y))).map ρ

end Generic

theorem centCycCell_b : CentCycCell (IsLieOf IdxB) := by
  refine centCycCell_of_core (fun Y _ _ L J h hX p hp hp5 => outPChain_b hp hp5 hX)
    (fun Y _ _ L J h hX p hp hp5 v hv A hA hAp => ?_)
  rcases isLieOf_split (p := p) hX with hTF | hT
  · exact isCyclic_of_centCycBar_hub hv
      (perfectJoinHub_of_torusFree_classical (Or.inr (Or.inr (Or.inl rfl))) hp hp5 hTF) hA hAp
  · exact (false_of_centCycBar_torus_b hp hp5 hT hv).elim

theorem centCycCell_d : CentCycCell (IsLieOf IdxD) := by
  refine centCycCell_of_core (fun Y _ _ L J h hX p hp hp5 => outPChain_d hp hp5 hX)
    (fun Y _ _ L J h hX p hp hp5 v hv A hA hAp => ?_)
  rcases isLieOf_split (p := p) hX with hTF | hT
  · exact isCyclic_of_centCycBar_hub hv
      (perfectJoinHub_of_torusFree_classical (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp hp5 hTF)
      hA hAp
  · exact (false_of_centCycBar_escapes hv (center_bar_eq_bot h)
      (NodeWitnesses.centralizerEscapes_of_isLieOfTorus_d hT hp hp5)).elim

theorem centCycCell_twistedD : CentCycCell (IsLieOf IdxTwistedD) := by
  refine centCycCell_of_core (fun Y _ _ L J h hX p hp hp5 => outPChain_twistedD hp hp5 hX)
    (fun Y _ _ L J h hX p hp hp5 v hv A hA hAp => ?_)
  rcases isLieOf_split (p := p) hX with hTF | hT
  · exact isCyclic_of_centCycBar_hub hv
      (perfectJoinHub_of_torusFree_classical (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp hp5 hTF)
      hA hAp
  · exact (false_of_centCycBar_escapes hv (center_bar_eq_bot h)
      (NodeWitnesses.centralizerEscapes_of_isLieOfTorus_twistedD hT hp hp5)).elim

theorem centCycCell_small : CentCycCell IsSmallTwoOrG2 := by
  refine centCycCell_of_core (fun Y _ _ L J h hX p hp hp5 => outPChain_small hp hp5 hX)
    (fun Y _ _ L J h hX p hp hp5 v hv A hA hAp => ?_)
  refine isCyclic_of_pGroup_of_not_sq_dvd hp (fun hd => ?_) hAp
  exact ToralCensus.not_sq_dvd_smallBound hp hp5
    (hd.trans ((ToralCensus.card_dvd_of_small hX).trans (by norm_num)))

section G2


theorem centCycCell_g2 : CentCycCell (IsLieOf IdxG2) := by
  intro Y _ _ L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  obtain ⟨ρ, -, -, v, hv⟩ := exists_centCycBar hCP hp hDp hDJ hDcyc hDpart hxD hxp hxC hxW
  exact (false_of_centCycBar_escapes hv (center_bar_eq_bot hCP)
    (centralizerEscapes_of_isLieOf_g2 hX hp (by omega))).elim

theorem kFactBlockCentCycIb_of_cells (hA : CentCycCell (IsLieOf IdxA))
    (hTA : CentCycCell (IsLieOf IdxTwistedA)) : KFactBlockCentCycIb := by
  intro Y _ _ L J hL hcl hpar hJL hnB p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  have hCP : CompParabE L J := ⟨hL, hcl, hpar, hJL, hnB⟩
  rcases isClassicalTwoOrG2_family_cases hcl with hX | hX | hX | hX | hX | hX | hX
  · exact hA Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  · exact hTA Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  · exact centCycCell_b Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  · exact centCycCell_d Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  · exact centCycCell_twistedD Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN
      hEp
  · exact centCycCell_g2 Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN hEp
  · exact centCycCell_small Y L J hCP hX p hp hp5 D hDp hDJ hDcyc hDpart x hxD hxp hxC hxW E hEN
      hEp

end G2

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
