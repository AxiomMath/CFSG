module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7Struct
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246A7NoBlock
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.L246A7

open Equiv CFSG.Open CFSG.Quasithin

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section General

theorem le_pCore_of_normal {H : Type*} [Group H] {N : Subgroup H} [N.Normal] (hN : IsPGroup 2 N) :
    N ≤ CFSG.pCore 2 H :=
  le_sSup ⟨inferInstance, hN⟩

theorem isSubnormal_subgroupOf_of_le {G : Type*} [Group G] {H K X : Subgroup G}
    (hKX : K ≤ X) (h : (H.subgroupOf X).IsSubnormal) : (H.subgroupOf K).IsSubnormal := by
  have h1 := h.subgroupOf (K := K.subgroupOf X)
  let e : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have h2 := Subgroup.IsSubnormal.map (f := e.toMonoidHom) e.surjective h1
  have heq : H.subgroupOf K =
      Subgroup.map e.toMonoidHom ((H.subgroupOf X).subgroupOf (K.subgroupOf X)) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [heq]
  exact h2

theorem order_mem_of_block_quotient {G : Type*} [Group G] {K : Subgroup G} {T : Type*} [Group T]
    (q : ↥K →* T) (hq : Function.Surjective q) (hT : IsSimpleGroup T) (hker : IsPGroup 2 q.ker)
    {B : Subgroup G} (hB : IsBlock2 K B) (P : ℕ → Prop)
    (hdata : ∃ (A : Type) (_ : Group A) (α : ↥B →* A), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥B ∧ Nontrivial A ∧ P (Nat.card A)) : P (Nat.card T) := by
  obtain ⟨hshort, hBK, hsub⟩ := hB
  obtain ⟨A, _, α, hαs, hαk, hAnt, hAord⟩ := hdata
  have hsub' : ((B.subgroupOf K).map q).IsSubnormal :=
    Subgroup.IsSubnormal.map hq hsub
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hT hsub' with hbot | htop
  ·
    exfalso
    have hB2 : IsPGroup 2 ↥B := by
      intro b
      have hb : q (Subgroup.inclusion hBK b) = 1 := by
        have : q (Subgroup.inclusion hBK b) ∈ (B.subgroupOf K).map q :=
          ⟨Subgroup.inclusion hBK b, b.2, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      obtain ⟨k, hk⟩ := hker ⟨Subgroup.inclusion hBK b, hb⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun x : ↥q.ker => ((x : ↥K) : G)) hk
      simpa using this
    have hcore : CFSG.pCore 2 ↥B = ⊤ := by
      rw [eq_top_iff]
      refine le_pCore_of_normal (N := (⊤ : Subgroup ↥B)) fun x => ?_
      obtain ⟨k, hk⟩ := hB2 (x : ↥B)
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    rw [hcore] at hαk
    have : ∀ y : A, y = 1 := by
      intro y
      obtain ⟨b, rfl⟩ := hαs y
      exact MonoidHom.mem_ker.1 (hαk ▸ Subgroup.mem_top b)
    obtain ⟨y, hy⟩ := exists_ne (1 : A)
    exact hy (this y)
  ·
    set β : ↥B →* T := q.comp (Subgroup.inclusion hBK) with hβ
    have hβs : Function.Surjective β := by
      intro t
      obtain ⟨k, hk, rfl⟩ : t ∈ (B.subgroupOf K).map q := htop ▸ Subgroup.mem_top t
      exact ⟨⟨k, hk⟩, rfl⟩
    have hβ2 : IsPGroup 2 β.ker := by
      intro b
      obtain ⟨k, hk⟩ := hker ⟨Subgroup.inclusion hBK b, b.2⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun x : ↥q.ker => ((x : ↥K) : G)) hk
      simpa using this
    have hle : β.ker ≤ α.ker := by
      rw [hαk]
      exact le_pCore_of_normal hβ2
    set α' : T →* A := β.liftOfSurjective hβs ⟨α, hle⟩ with hα'
    have hα'β : ∀ b : ↥B, α' (β b) = α b := fun b =>
      MonoidHom.liftOfRightInverse_comp_apply β _ _ ⟨α, hle⟩ b
    have hα's : Function.Surjective α' := by
      intro y
      obtain ⟨b, rfl⟩ := hαs y
      exact ⟨β b, hα'β b⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal α'.ker with h | h
    · have hinj : Function.Injective α' := (MonoidHom.ker_eq_bot_iff α').1 h
      have : Nat.card T = Nat.card A := Nat.card_congr (Equiv.ofBijective α' ⟨hinj, hα's⟩)
      rw [this]
      exact hAord
    · exfalso
      have : ∀ y : A, y = 1 := by
        intro y
        obtain ⟨t, rfl⟩ := hα's y
        exact MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top t)
      obtain ⟨y, hy⟩ := exists_ne (1 : A)
      exact hy (this y)

theorem chiBlock_type_data {G : Type*} [Group G] {B : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type B n) ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltType B m) :
    ∃ (A : Type) (_ : Group A) (α : ↥B →* A), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥B ∧ Nontrivial A ∧ ChiOrder (Nat.card A) := by
  rcases h with ⟨n, hn, F, hF, hFin, hcard, α, hαs, hαk, -⟩ | ⟨m, hm, hm3, α, hαs, hαk, -⟩
  · have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have h42 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ n * (4 ^ n - 1) := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hq, h42]
    refine ⟨Matrix.SpecialLinearGroup (Fin 2) F, inferInstance, α, hαs, hαk, ?_,
      Or.inl ⟨n, by omega, hcardSL⟩⟩
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 1 < Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [hcardSL]
      have h16 : 16 ≤ 4 ^ n := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h15 : 15 ≤ 4 ^ n - 1 := by omega
      calc 1 < 2 ^ n * 15 := by omega
        _ ≤ 2 ^ n * (4 ^ n - 1) := Nat.mul_le_mul_left _ h15
    exact Finite.one_lt_card_iff_nontrivial.1 h1
  · have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
    have hc : Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
    refine ⟨alternatingGroup (Fin m), inferInstance, α, hαs, hαk, ?_, Or.inr ⟨m, hm, hm3, hc⟩⟩
    have h6 : Nat.factorial 3 ≤ Nat.factorial m := Nat.factorial_le hm3
    have h6' : (6 : ℕ) ≤ Nat.factorial m := by simpa [Nat.factorial] using h6
    exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; omega)

end General

section G7

variable {G : Type} [Group G] [Finite G] {L T : Subgroup G} (D : Alt7Data L)

@[expose] def G7 (D : Alt7Data L) (T : Subgroup G) : Subgroup G := rhoPre D (L ⊔ T) S6

theorem G7_le (D : Alt7Data L) : G7 D T ≤ L ⊔ T := rhoPre_le D _ _

theorem card_range_jA : Nat.card ↥jA.range = 360 := by
  have : Nontrivial ↥pts6 := Fintype.one_lt_card_iff_nontrivial.1 (by rw [card_pts6]; norm_num)
  rw [← Nat.card_congr (MonoidHom.ofInjective jA_injective).toEquiv, nat_card_alternatingGroup,
    Nat.card_eq_fintype_card, card_pts6]
  decide

theorem no_chiBlock_G7 (hTN : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (B : Subgroup G) : ¬ IsChiBlock (G7 D T) B := by
  rintro ⟨⟨hshort, hBG7, hsub⟩, htype⟩
  have hHN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le_normalizer hTN
  set K : Subgroup G := rhoPre D (L ⊔ T) (S6 ⊓ alternatingGroup (Fin 7)) with hK
  have hKG7 : K ≤ G7 D T := fun g hg => ⟨hg.1, hg.2.1, (hg.2.2).1⟩
  have hKN : K ≤ Subgroup.normalizer (L : Set G) := fun g hg => hg.2.1
  have hBH : B ≤ L ⊔ T := hBG7.trans (G7_le D)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBH.trans hHN
  have hBK : B ≤ K := by
    let signB : ↥B →* ℤˣ := (Perm.sign).comp ((rhoN D).comp (Subgroup.inclusion hBN))
    have hker : signB.ker = ⊤ := by
      apply hshort.1
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      refine ⟨1, ?_⟩
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
      exact Int.units_sq _
    intro b hb
    have h1 : signB ⟨b, hb⟩ = 1 := by
      have : (⟨b, hb⟩ : ↥B) ∈ signB.ker := by rw [hker]; exact Subgroup.mem_top _
      exact this
    have h2 : rho D b ∈ alternatingGroup (Fin 7) := by
      rw [rho_eq D (hBN hb)]
      exact Perm.mem_alternatingGroup.2 h1
    have h3 : rho D b ∈ S6 := by
      have := hBG7 hb
      exact this.2.2
    exact ⟨hBH hb, hBN hb, h3, h2⟩
  have hsubK : (B.subgroupOf K).IsSubnormal := isSubnormal_subgroupOf_of_le hKG7 hsub
  let ρK : ↥K →* S₇ := (rhoN D).comp (Subgroup.inclusion hKN)
  have hρK : ∀ k : ↥K, ρK k = rho D k := fun k => (rho_eq D (hKN k.2)).symm
  have hA : ∀ k : ↥K, ρK k ∈ alternatingGroup (Fin 7) := fun k => by
    rw [hρK]; exact k.2.2.2.2
  have h6 : ∀ k : ↥K, (⟨ρK k, hA k⟩ : A₇) ∈ jA.range := fun k => by
    rw [mem_range_jA]
    show ρK k 6 = 6
    rw [hρK]
    exact k.2.2.2.1
  let q : ↥K →* ↥jA.range := (ρK.codRestrict (alternatingGroup (Fin 7)) hA).codRestrict jA.range h6
  have hq : Function.Surjective q := by
    rintro ⟨b, hb⟩
    have hb6 : (b : S₇) 6 = 6 := mem_range_jA.1 hb
    obtain ⟨ℓ, hℓ⟩ := D.hα b
    have hρℓ : rho D ℓ = (b : S₇) := by rw [rho_of_mem D ℓ.2, hℓ]
    have hℓK : (ℓ : G) ∈ K := by
      refine ⟨(le_sup_left : L ≤ L ⊔ T) ℓ.2, Subgroup.le_normalizer ℓ.2, ?_, ?_⟩
      · rw [hρℓ]; exact hb6
      · rw [hρℓ]; exact b.2
    refine ⟨⟨ℓ, hℓK⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ρK ⟨ℓ, hℓK⟩ = b
    rw [hρK]
    exact hρℓ
  have hqker : IsPGroup 2 q.ker := by
    intro k
    have hk1 : ρK k.1 = 1 := by
      have := k.2
      rw [MonoidHom.mem_ker] at this
      exact congrArg (fun x : ↥jA.range => ((x : A₇) : S₇)) this
    have hmem : (k.1 : G) ∈ rhoPre D (L ⊔ T) ⊥ :=
      ⟨k.1.2.1, k.1.2.2.1, by rw [← hρK]; simpa using hk1⟩
    obtain ⟨s, hs⟩ := isPGroup_kerRho D hTN hT2 ⟨k.1, hmem⟩
    refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
    have h' := congrArg Subtype.val hs
    simpa using h'
  have hord := order_mem_of_block_quotient q hq isSimpleGroup_range_jA hqker
    ⟨hshort, hBK, hsubK⟩ ChiOrder (chiBlock_type_data htype)
  rw [card_range_jA] at hord
  exact not_chiOrder_360 hord

end G7

end CFSG.QuasithinUnique.L246A7
