module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.RankThree.PartOne.StrongP
  renaming conjSub → conjSubP, mem_conjSub_iff → mem_conjSubP_iff, card_conjSub → card_conjSubP

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_caseA_aux1 (M : Subgroup G) (D : Subgroup ↥M) :
    (Subgroup.centralizer (D : Set ↥M)).map M.subtype =
      M ⊓ Subgroup.centralizer ((D.map M.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hy d hd)
  · intro hx
    obtain ⟨hxM, hx⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show (⟨x, hxM⟩ : ↥M) ∈ Subgroup.centralizer (D : Set ↥M)
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx _ ⟨d, hd, rfl⟩)

theorem normalizer_le_of_caseA_aux2 (V : Type) [Group V] [Finite V] (h : Nat.card V ≤ 4) :
    Group.IsSolvable (MulAut V) := by
  have := Equiv.Perm.isSolvable h
  exact Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm V) (fun a b hab =>
    MulEquiv.ext fun x => congrArg (fun σ : Equiv.Perm V => σ x) hab)

theorem normalizer_le_of_caseA_gen {M : Subgroup G} (hO : O812sixAt G M) {p : ℕ}
    (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p) {D : Subgroup ↥M} (hD : CaseA1517 p D) :
    Subgroup.normalizer ((D.map M.subtype : Subgroup G) : Set G) ≤ M := by
  obtain ⟨hcard, hrank, hnsolv⟩ := hD
  haveI : Fact p.Prime := ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1⟩
  have hcardF : Nat.card (D.map M.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hcard]
  have hF3 : IsPGroup 3 (D.map M.subtype) :=
    (IsPGroup.of_card (n := 1) (by simpa using hcard) : IsPGroup 3 D).map M.subtype
  have hFne : D.map M.subtype ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardF
    omega
  have hAut : Group.IsSolvable (MulAut ↥(D.map M.subtype)) :=
    normalizer_le_of_caseA_aux2 _ (by rw [hcardF]; norm_num)
  have hC := normalizer_le_of_caseA_aux1 M D
  have hrk : 2 ≤ CFSG.Open.pRank p
      (M ⊓ Subgroup.centralizer ((D.map M.subtype : Subgroup G) : Set G)) := by
    rw [← hC]
    exact hrank.trans (CFSG.SectionRank.pRank_le_map (by omega) M.subtype M.subtype_injective _)
  have hns : ¬ CFSG.HallHigman.IsPSolvable p
      ↥(M ⊓ Subgroup.centralizer ((D.map M.subtype : Subgroup G) : Set G)) := by
    intro hB
    apply hnsolv
    let e : ↥(Subgroup.centralizer (D : Set ↥M)) ≃*
        ↥(M ⊓ Subgroup.centralizer ((D.map M.subtype : Subgroup G) : Set G)) :=
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr hC)
    exact isPSolvable_of_mulEquiv e.symm hB
  exact hO p hp hp5 _ (Subgroup.map_subtype_le D) hF3 hFne hAut hrk hns

theorem gamma_two_le_of_out_aux1 {Q : Subgroup G} (hQ : 2 ≤ CFSG.Open.pRank 3 Q) :
    ∃ E ≤ Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Q
  have hdvd : 3 ^ 2 ∣ Nat.card E := hcard ▸ pow_dvd_pow 3 hQ
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 hdvd
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  refine ⟨K.map E.subtype, hle.trans hEQ, CFSG.Open.IsElemAbelian.mono hE hle, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

theorem gamma_two_le_of_out_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) {p : ℕ} (hp : p ∈ sigmaM G M) (hout : Out1517 ↥M p)
    (hA : ∀ D : Subgroup ↥M, CaseA1517 p D →
      Subgroup.normalizer ((D.map M.subtype : Subgroup G) : Set G) ≤ M)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) :
    CFSG.Open.rankThreeGamma 2 3 R ≤ M := by
  haveI : Fact p.Prime := ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1⟩
  unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQR, hQ2, rfl⟩
  intro g hg
  by_contra hgM
  obtain ⟨E, hEQ, hE, hE9⟩ := gamma_two_le_of_out_aux1 hQ2
  have hEM : E ≤ M := hEQ.trans (hQR.trans hR.le)
  have hE'9 : Nat.card (E.subgroupOf M) = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  obtain ⟨D, hDE, hDcase⟩ :=
    hout.caseA (E.subgroupOf M) (CFSG.Open.IsElemAbelian.subgroupOf hE M) hE'9
  have hD'E : D.map M.subtype ≤ E := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDE hd
  have hDN := hA D hDcase
  set D' : Subgroup G := D.map M.subtype with hD'
  have hD'card : Nat.card D' = 3 := by
    rw [hD', Subgroup.card_map_of_injective M.subtype_injective, hDcase.1]
  have hcard' : Nat.card (conjSubP g D') = 3 := by
    rw [card_conjSubP, hD'card]
  have hgQ : ∀ y, y ∈ Q ↔ g * y * g⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hg
  have hconjQ : conjSubP g D' ≤ Q := by
    intro y hy
    rw [mem_conjSubP_iff] at hy
    have hyQ : g⁻¹ * y * g ∈ Q := hEQ (hD'E hy)
    have := (hgQ _).mp hyQ
    simpa [mul_assoc] using this
  have hconjM : conjSubP g D' ≤ M := hconjQ.trans (hQR.trans hR.le)
  set D'' : Subgroup ↥M := (conjSubP g D').subgroupOf M with hD''
  have hD''card : Nat.card D'' = 3 := by
    rw [hD'', ← hcard']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconjM).toEquiv
  obtain ⟨xc, hxc⟩ := exists_prime_orderOf_dvd_card' p (hout.dvd D'' hD''card)
  set x : ↥M := (xc : ↥M) with hx
  have hxcen : x ∈ Subgroup.centralizer (D'' : Set ↥M) := xc.2
  have hxord : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hxc]
  have hy : g⁻¹ * (x : G) * g ∈ Subgroup.centralizer (D' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdc : g * d * g⁻¹ ∈ conjSubP g D' := by
      rw [mem_conjSubP_iff]
      simpa [mul_assoc] using hd
    have hdc' : (⟨g * d * g⁻¹, hconjM hdc⟩ : ↥M) ∈ D'' := hdc
    have h2 : (g * d * g⁻¹) * (x : G) = (x : G) * (g * d * g⁻¹) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxcen _ hdc')
    calc d * (g⁻¹ * x * g) = g⁻¹ * ((g * d * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * d * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * x * g * d := by group
  have hyM : g⁻¹ * (x : G) * g ∈ M := hDN (Subgroup.centralizer_le_normalizer _ hy)
  have hxMg : (x : G) ∈ conjSubP g M := by
    rw [mem_conjSubP_iff]
    exact hyM
  have hle : Subgroup.zpowers (x : G) ≤ M ⊓ M.map (MulAut.conj g).toMonoidHom :=
    Subgroup.zpowers_le.mpr ⟨x.2, hxMg⟩
  have hdvd : p ∣ Nat.card ↥(M ⊓ M.map (MulAut.conj g).toMonoidHom) := by
    refine (?_ : p ∣ Nat.card (Subgroup.zpowers (x : G))).trans (Subgroup.card_dvd_of_le hle)
    rw [Nat.card_zpowers, hxord]
  exact (ctx.strong p hp).2.2 g hgM hdvd

theorem isStronglyPEmbedded_three_of_normalizers_aux0 {p : ℕ} [Fact p.Prime] {U K : Subgroup G}
    (hUK : U ≤ K) (hU : IsPGroup p U) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ U ≤ P := by
  obtain ⟨Q, hUQ⟩ := (hU.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun x hx => ⟨⟨x, hUK hx⟩, hUQ hx, rfl⟩⟩

theorem isStronglyPEmbedded_three_of_normalizers_aux1 {p : ℕ} [Fact p.Prime] {U Q : Subgroup G}
    (hQ : IsPGroup p Q) (hUQ : U < Q) : U < Q ⊓ Subgroup.normalizer (U : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hproper : U.subgroupOf Q < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro heq
    exact (not_le_of_gt hUQ) (Subgroup.subgroupOf_eq_top.mp heq)
  have hgrowth := Group.normalizerCondition_of_isNilpotent (G := Q) (U.subgroupOf Q) hproper
  have hmapgrowth := Subgroup.map_subtype_lt_map_subtype.mpr hgrowth
  rw [Subgroup.map_subgroupOf_eq_of_le hUQ.le] at hmapgrowth
  have hnormalizer : (Subgroup.normalizer (U.subgroupOf Q : Set Q)).map Q.subtype =
      Q ⊓ Subgroup.normalizer (U : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hUQ.le, Subgroup.subgroupOf_map_subtype, inf_comm]
  rwa [hnormalizer] at hmapgrowth

theorem isStronglyPEmbedded_three_of_normalizers_aux2 {p : ℕ} [Fact p.Prime] {P K A : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P K) (hN : Subgroup.normalizer (P : Set G) ≤ K)
    (hKA : K ≤ A) : CFSG.ABGLocalTools.IsSylowOf p P A := by
  obtain ⟨P₁, hP₁, hle⟩ :=
    isStronglyPEmbedded_three_of_normalizers_aux0 (hP.le.trans hKA) hP.isPGroup
  by_cases heq : P = P₁
  · rw [heq]
    exact hP₁
  · exfalso
    have hlt := isStronglyPEmbedded_three_of_normalizers_aux1 hP₁.isPGroup (lt_of_le_of_ne hle heq)
    have hQK : P₁ ⊓ Subgroup.normalizer (P : Set G) ≤ K := inf_le_right.trans hN
    exact hlt.ne' (hP.eq_of_le hlt.le hQK hP₁.isPGroup.to_inf_left)

theorem isStronglyPEmbedded_three_of_normalizers_aux3 {P : Subgroup G} {g x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.normalizer ((conjSubP g⁻¹ P : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  have e1 : y ∈ conjSubP g⁻¹ P ↔ g * y * g⁻¹ ∈ P := by
    rw [mem_conjSubP_iff]
    simp
  have e2 : g⁻¹ * x * g * y * (g⁻¹ * x * g)⁻¹ ∈ conjSubP g⁻¹ P ↔ x * (g * y * g⁻¹) * x⁻¹ ∈ P := by
    rw [mem_conjSubP_iff]
    simp only [inv_inv, mul_inv_rev, mul_assoc]
    constructor <;> intro h <;> convert h using 1 <;> group
  rw [e1, e2]
  exact hx _

theorem isStronglyPEmbedded_three_of_normalizers {M : Subgroup G} (hM : M ≠ ⊤)
    (h3 : 3 ∣ Nat.card M)
    (hN : ∀ U : Subgroup G, U ≤ M → U ≠ ⊥ → IsPGroup 3 U →
      Subgroup.normalizer (U : Set G) ≤ M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M := by
  refine ⟨hM, h3, ?_⟩
  intro g hg hdvd
  set K := M ⊓ M.map (MulAut.conj g).toMonoidHom with hK
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 K
  have hPK : P ≤ K := hP.le
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPne : P ≠ ⊥ := by
    intro hbot
    have := ((CFSG.ABGLocalTools.isSylowOf_iff).mp hP).2.2
    rw [hbot, Subgroup.relIndex_bot_left] at this
    exact this hdvd
  have hPM : P ≤ M := hPK.trans inf_le_left
  have hPMg : P ≤ conjSubP g M := hPK.trans inf_le_right
  have hNPM : Subgroup.normalizer (P : Set G) ≤ M := hN P hPM hPne hP3
  set Q := conjSubP g⁻¹ P with hQdef
  have hQmem : ∀ y : G, y ∈ Q ↔ g * y * g⁻¹ ∈ P := fun y => by
    rw [hQdef, mem_conjSubP_iff]
    simp
  have hQM : Q ≤ M := by
    intro y hy
    have h1 := hPMg ((hQmem y).mp hy)
    rw [mem_conjSubP_iff] at h1
    simpa [mul_assoc] using h1
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hPne
    refine Subgroup.card_eq_one.mp ?_
    rw [← card_conjSubP (g := g⁻¹) (Y := P)]
    change Nat.card Q = 1
    rw [h]
    exact Subgroup.card_bot
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ M := hN Q hQM hQne (hP3.map _)
  have hNPMg : Subgroup.normalizer (P : Set G) ≤ conjSubP g M := by
    intro x hx
    rw [mem_conjSubP_iff]
    exact hNQ (isStronglyPEmbedded_three_of_normalizers_aux3 hx)
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P M :=
    isStronglyPEmbedded_three_of_normalizers_aux2 hP (le_inf hNPM hNPMg) inf_le_left
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q M := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hQM ?_
    rw [card_conjSubP]
    exact hPsyl.card_eq
  obtain ⟨m, hmM, hQm⟩ := normalizer_inf_le_of_sylow_aux2 hPsyl hQsyl
  have hgm : g * m ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 : y ∈ P ↔ m * y * m⁻¹ ∈ Q := by
      rw [hQm]
      change y ∈ P ↔ m * y * m⁻¹ ∈ conjSubP m P
      rw [mem_conjSubP_iff]
      have e : m⁻¹ * (m * y * m⁻¹) * m = y := by group
      rw [e]
    rw [h1, hQmem]
    have e : g * (m * y * m⁻¹) * g⁻¹ = g * m * y * (g * m)⁻¹ := by group
    rw [e]
  have hgM : g * m ∈ M := hNPM hgm
  exact hg (by simpa using M.mul_mem hgM (M.inv_mem hmM))

theorem normalizer_le_of_card_three_aux1 (M : Subgroup G) (D : Subgroup ↥M) :
    (Subgroup.normalizer (D : Set ↥M)).map M.subtype =
      M ⊓ Subgroup.normalizer ((D.map M.subtype : Subgroup G) : Set G) := by
  have hsub : (D.map M.subtype).subgroupOf M = D :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective D
  have h := Subgroup.subgroupOf_normalizer_eq (H := D.map M.subtype) (N := M)
    (Subgroup.map_subtype_le D)
  rw [hsub] at h
  rw [← h, Subgroup.subgroupOf_map_subtype, inf_comm]

theorem normalizer_le_of_card_three_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO812 : O812sixAt G M) (hO1517 : O1517bAt G M)
    (ctx : S15CtxGen G M T T₁ T₂) {p : ℕ}
    (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p)
    (hout : Out1517 ↥M p) {D : Subgroup ↥M} (hD : Nat.card D = 3) :
    Subgroup.normalizer ((D.map M.subtype : Subgroup G) : Set G) ≤ M := by
  by_cases hcase : CaseA1517 p D
  · exact normalizer_le_of_caseA_gen hO812 hp hp5 hcase
  · have hshape := hout.shape D hD hcase
    obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 M
    have hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M :=
      gamma_two_le_of_out_gen ctx hp hout
        (fun D' hD' => normalizer_le_of_caseA_gen hO812 hp hp5 hD') hR
    have hcardA : Nat.card (D.map M.subtype) = 3 := by
      rw [Subgroup.card_map_of_injective M.subtype_injective, hD]
    have hdvd : p ∣ Nat.card
        ↥(M ⊓ Subgroup.centralizer ((D.map M.subtype : Subgroup G) : Set G)) := by
      rw [← normalizer_le_of_caseA_aux1, Subgroup.card_map_of_injective M.subtype_injective]
      exact hout.dvd D hD
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3
      (M ⊓ Subgroup.normalizer ((D.map M.subtype : Subgroup G) : Set G))
    have hPshape : ((IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P)) ∧
        3 ≤ CFSG.Open.pRank 3 P := by
      obtain ⟨P', rfl⟩ : ∃ P' : Subgroup ↥M, P'.map M.subtype = P :=
        ⟨P.subgroupOf M, by
          rw [Subgroup.subgroupOf_map_subtype]
          exact inf_eq_left.mpr (hP.le.trans inf_le_left)⟩
      rw [← normalizer_le_of_card_three_aux1] at hP
      have hP' := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff M).mp hP
      obtain ⟨hsh, hrk⟩ := hshape P' hP'
      refine ⟨?_, hrk.trans
        (CFSG.SectionRank.pRank_le_map (by norm_num) M.subtype M.subtype_injective P')⟩
      rcases hsh with ⟨hE, hc⟩ | hcyc
      · refine Or.inl ⟨CFSG.Open.IsElemAbelian.map hE _, ?_⟩
        rw [Subgroup.card_map_of_injective M.subtype_injective]
        exact hc
      · exact Or.inr
          ((Subgroup.centerCongr (P'.equivMapOfInjective M.subtype M.subtype_injective)).isCyclic.mp
            hcyc)
    exact hO1517 p hp R hR hΓ _ (Subgroup.map_subtype_le D) hcardA hdvd P hP hPshape

theorem strong_three_of_out1517_aux1 {U : Subgroup G} (hU3 : IsPGroup 3 U) (hUne : U ≠ ⊥)
    (h1 : CFSG.Open.pRank 3 U ≤ 1) :
    ∃ C : Subgroup G, C ≤ U ∧ (C.subgroupOf U).Characteristic ∧ Nat.card C = 3 := by
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, ∀ z, z ∈ C ↔
      z ∈ U ∧ z ∈ Subgroup.centralizer (U : Set G) ∧ z ^ 3 = 1 :=
    ⟨{ carrier := {z | z ∈ U ∧ z ∈ Subgroup.centralizer (U : Set G) ∧ z ^ 3 = 1}
       mul_mem' := by
         rintro a b ⟨haU, haC, ha3⟩ ⟨hbU, hbC, hb3⟩
         refine ⟨U.mul_mem haU hbU, Subgroup.mul_mem _ haC hbC, ?_⟩
         have hcomm : Commute a b := (Subgroup.mem_centralizer_iff.mp hbC) a haU
         rw [hcomm.mul_pow, ha3, hb3, one_mul]
       one_mem' := ⟨U.one_mem, Subgroup.one_mem _, one_pow 3⟩
       inv_mem' := by
         rintro a ⟨haU, haC, ha3⟩
         exact ⟨U.inv_mem haU, Subgroup.inv_mem _ haC, by rw [inv_pow, ha3, inv_one]⟩ },
     fun z => Iff.rfl⟩
  have hCU : C ≤ U := fun z hz => ((hC z).mp hz).1
  refine ⟨C, hCU, ?_, ?_⟩
  · rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hy' := (hC (y : G)).mp hy
    have hcomm : ∀ h' : ↥U, h' * y = y * h' := fun h' =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hy'.2.1) h' h'.2)
    have key : ∀ h' : ↥U, h' * φ y = φ y * h' := by
      intro h'
      have := congrArg φ (hcomm (φ.symm h'))
      simpa using this
    have hpow : (φ y) ^ 3 = 1 := by
      rw [← map_pow, show y ^ 3 = 1 from Subtype.ext hy'.2.2, map_one]
    refine (hC _).mpr ⟨(φ y).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (key ⟨h, hh⟩)
    · have := congrArg Subtype.val hpow
      simpa using this
  · have hC3 : IsPGroup 3 C := hU3.to_le hCU
    obtain ⟨k, hk⟩ := hC3.exists_card_eq
    have hCel : IsElemAbelian 3 C :=
      ⟨⟨⟨fun a b => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp ((hC (b : G)).mp b.2).2.1 (a : G) (hCU a.2))⟩⟩,
        fun x hx => ((hC x).mp hx).2.2⟩
    have hkle : k ≤ CFSG.Open.pRank 3 U :=
      CFSG.SectionRank.le_pRank (by norm_num) hCU hCel hk
    have hCne : C ≠ ⊥ := by
      have : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hUne
      have hZ : Nontrivial (Subgroup.center U) := hU3.center_nontrivial
      have hdvd : 3 ∣ Nat.card (Subgroup.center U) := by
        obtain ⟨k, hk⟩ := (hU3.to_subgroup (Subgroup.center U)).exists_card_eq
        have h1 : 1 < Nat.card (Subgroup.center U) := Finite.one_lt_card_iff_nontrivial.mpr hZ
        rw [hk] at h1 ⊢
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at h1
          exact lt_irrefl 1 h1
        exact dvd_pow_self 3 hk0
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center U) 3 hdvd
      intro h
      have hmem : (((z : Subgroup.center U) : U) : G) ∈ C := by
        rw [hC]
        refine ⟨(z : U).2, ?_, ?_⟩
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
        · have h1 := pow_orderOf_eq_one z
          rw [hz] at h1
          have h2 := congrArg (fun w : Subgroup.center U => ((w : U) : G)) h1
          simpa using h2
      rw [h, Subgroup.mem_bot] at hmem
      have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
      rw [hz1, orderOf_one] at hz
      exact Nat.prime_three.one_lt.ne hz
    have hk0 : k ≠ 0 := by
      intro h0
      apply hCne
      rw [h0, pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    have hk1 : k = 1 := by omega
    rw [hk, hk1, pow_one]

theorem strong_three_of_out1517_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO812 : O812sixAt G M) (hO1517 : O1517bAt G M)
    (ctx : S15CtxGen G M T T₁ T₂) {p : ℕ}
    (hp : p ∈ sigmaM G M) (hp5 : 5 ≤ p)
    (hout : Out1517 ↥M p) (h3 : 3 ∣ Nat.card M) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M := by
  refine isStronglyPEmbedded_three_of_normalizers (ctx.strong p hp).1 h3 ?_
  intro U hUM hUne hU3
  by_cases h2 : 2 ≤ CFSG.Open.pRank 3 U
  · obtain ⟨R, hR, hUR⟩ := isStronglyPEmbedded_three_of_normalizers_aux0 hUM hU3
    have hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M :=
      gamma_two_le_of_out_gen ctx hp hout
        (fun D hD => normalizer_le_of_caseA_gen hO812 hp hp5 hD) hR
    refine le_trans ?_ hΓ
    unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
    exact le_sSup ⟨U, hUR, h2, rfl⟩
  · obtain ⟨C, hCU, hCchar, hC3⟩ := strong_three_of_out1517_aux1 hU3 hUne (by omega)
    have hCM : C ≤ M := hCU.trans hUM
    have hD3 : Nat.card (C.subgroupOf M) = 3 := by
      rw [← hC3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv
    have hmap : (C.subgroupOf M).map M.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hCM
    have hN := normalizer_le_of_card_three_gen hO812 hO1517 ctx hp hp5 hout hD3
    rw [hmap] at hN
    exact (normalizer_le_normalizer_of_characteristic hCU hCchar).trans hN

end GLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
