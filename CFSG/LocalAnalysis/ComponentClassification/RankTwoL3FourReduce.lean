module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCore
public import CFSG.LocalAnalysis.SectionRank.SporadicCatalog
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Open.StatedAPI
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs
public import Certificates.Certificate8026Base

public section

namespace CFSG.ComponentClassification.RankTwoL3Four

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.RankTwoStandard

section NormalClosure

variable {G H : Type} [Group G] [Group H]

theorem map_rankTwoX (f : G →* H) (hf : Function.Surjective f) (A : Subgroup G) :
    (rankTwoX A).map f = rankTwoX (A.map f) := by
  simp only [rankTwoX, Subgroup.map_normalClosure _ f hf, Subgroup.coe_map]

theorem le_centralizer_rankTwoX {A N : Subgroup G} [N.Normal]
    (h : N ≤ centralizer (A : Set G)) : N ≤ centralizer (rankTwoX A : Set G) := by
  rw [le_centralizer_iff] at h ⊢
  exact normalClosure_le_normal h

theorem commutator_rankTwoX_eq_top {A : Subgroup G} (hA : commutator A = ⊤) :
    commutator (rankTwoX A) = ⊤ := by
  have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hA
  have hle : A ≤ rankTwoX A := le_normalClosure
  have hN : (rankTwoX A).Normal := normalClosure_normal
  have hder : A ≤ ⁅rankTwoX A, rankTwoX A⁆ := by
    calc A = ⁅A, A⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅rankTwoX A, rankTwoX A⁆ := Subgroup.commutator_mono hle hle
  have heq : ⁅rankTwoX A, rankTwoX A⁆ = rankTwoX A :=
    le_antisymm (Subgroup.commutator_le_self _) (normalClosure_le_normal hder)
  exact (Group.isPerfect_def).1 (Subgroup.isPerfect_iff.mpr heq)

end NormalClosure

theorem center_eq_bot_of_not_prime {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hb | ht
  · exact hb
  · exfalso
    have : IsMulCommutative S := ⟨⟨fun a b => by
      have hb : b ∈ center S := ht ▸ mem_top b
      exact (mem_center_iff.mp hb a)⟩⟩
    exact h ((Group.is_simple_iff_prime_card).mp inferInstance)

theorem exists_ne_of_not_prime {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra hc
  have : IsMulCommutative S := ⟨⟨fun a b => by
    by_contra hab
    exact hc ⟨a, b, hab⟩⟩⟩
  exact h ((Group.is_simple_iff_prime_card).mp inferInstance)

theorem center_Suz_eq_bot : center NativeSporadic.Suz = ⊥ := by
  have := CFSG.Sporadic.Suz.isSimpleGroup_Suz
  exact center_eq_bot_of_not_prime (by rw [CFSG.Sporadic.Suz.card_Suz]; norm_num)

section Central

variable {Q S : Type} [Group Q] [Group S]

theorem ker_eq_center {f : Q →* S} (hf : Function.Surjective f) (hker : f.ker ≤ center Q)
    (hS : center S = ⊥) : f.ker = center Q := by
  refine le_antisymm hker fun z hz => ?_
  rw [MonoidHom.mem_ker, ← mem_bot, ← hS, mem_center_iff]
  intro s
  obtain ⟨q, rfl⟩ := hf s
  rw [← map_mul, ← map_mul, (mem_center_iff.mp hz q)]

end Central

section Quotient

variable {G : Type} [Group G] [Finite G]

theorem statedClassicalModel_of_mulEquiv {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    {n p f : ℕ} (h : Assembly.LowTwoRank.StatedClassicalModel Q' .PSL n p f) :
    Assembly.LowTwoRank.StatedClassicalModel Q .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem rankTwoHyp_map {A : Subgroup G} (hH : RankTwoHypNF G A) :
    RankTwoHypNF (G ⧸ standardComponentOddCore G)
        (A.map (QuotientGroup.mk' (standardComponentOddCore G))) ∧
      Nonempty (rankTwoQuot A ≃*
        rankTwoQuot (A.map (QuotientGroup.mk' (standardComponentOddCore G)))) := by
  have hodd := RankTwoSporadic.odd_card_standardComponentOddCore (G := G)
  have hNA := RankTwoSporadic.standardComponentOddCore_le_centralizer hH.standard hH.rank
  refine ⟨⟨?_, ?_, ?_⟩, ⟨RankTwoSporadic.quotCenterEquivMap hNA hH.standard.1.1⟩⟩
  · exact RankTwoSporadic.standard_map hH.standard hodd hNA
  · intro hn
    apply hH.not_normal
    have h1 : (A ⊔ standardComponentOddCore G).Normal := by
      have := hn.comap (QuotientGroup.mk' (standardComponentOddCore G))
      rwa [comap_map_eq, QuotientGroup.ker_mk'] at this
    rw [← normalizer_eq_top_iff, ← RankTwoSporadic.normalizer_sup_eq hodd hNA hH.standard.1.1]
    exact normalizer_eq_top_iff.mpr h1
  · exact RankTwoSporadic.two_le_pRank_map hodd hNA hH.standard.1.1 hH.rank

theorem l34Conclusion_of_map
    (hSuz : SuzMultiplierSix) {N A : Subgroup G} [N.Normal]
    (hodd : Odd (Nat.card N)) (hNA : N ≤ centralizer (A : Set G)) (hAp : commutator A = ⊤)
    (h : OddCoreFreeConclusion (A.map (QuotientGroup.mk' N))) : L34Conclusion A := by
  set π := QuotientGroup.mk' N
  set X := rankTwoX A
  have hXN : N ≤ centralizer (X : Set G) := le_centralizer_rankTwoX hNA
  have hXp : Group.IsPerfect ↥X := (Group.isPerfect_def).2 (commutator_rankTwoX_eq_top hAp)
  let ρ : ↥X →* ↥(X.map π) := π.subgroupMap X
  have hρ : Function.Surjective ρ := π.subgroupMap_surjective X
  have hmemker : ∀ x : ↥X, x ∈ ρ.ker ↔ (x : G) ∈ N := fun x => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π (x : G) = 1 := congrArg Subtype.val hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    · intro hx
      apply Subtype.ext
      change π (x : G) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
  have hker : ρ.ker ≤ center ↥X := fun x hx => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hXN ((hmemker x).mp hx)) y y.2)
  have hkerodd : Odd (Nat.card ρ.ker) := by
    refine hodd.of_dvd_nat ?_
    let φ : ↥ρ.ker →* ↥N :=
      { toFun := fun x => ⟨(x : ↥X), (hmemker _).mp x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective φ := fun a b hab => by
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact Subgroup.card_dvd_of_injective φ hinj
  have hXbar : X.map π = rankTwoX (A.map π) := map_rankTwoX π (QuotientGroup.mk'_surjective N) A
  unfold OddCoreFreeConclusion IsSporadic at h
  rcases h with hS | ⟨hZA, hHe⟩
  ·
    obtain ⟨e⟩ := hS
    let f : ↥X →* NativeSporadic.Suz :=
      (((MulEquiv.subgroupCongr hXbar).trans e : ↥(X.map π) ≃* NativeSporadic.Suz) :
        ↥(X.map π) →* NativeSporadic.Suz).comp ρ
    have hf : Function.Surjective f :=
      ((MulEquiv.subgroupCongr hXbar).trans e).surjective.comp hρ
    have hfker : f.ker = ρ.ker := by
      ext x
      simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        MonoidHom.coe_ofClass, map_eq_one_iff _ (MulEquiv.injective _)]
    have hZ : f.ker = center ↥X := ker_eq_center hf (hfker ▸ hker) center_Suz_eq_bot
    have eq : ↥X ⧸ center ↥X ≃* NativeSporadic.Suz :=
      (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    refine Or.inl ⟨⟨eq⟩, ?_⟩
    have h6 : Nat.card (center ↥X) ∣ 6 := hZ ▸ hSuz ↥X hXp f hf (hfker ▸ hker)
    have hodd' : Odd (Nat.card (center ↥X)) := by
      rw [← hZ, hfker]
      exact hkerodd
    have h3 : Nat.Coprime (Nat.card (center ↥X)) 2 :=
      hodd'.coprime_two_right
    exact h3.dvd_of_dvd_mul_left (by simpa [show (6 : ℕ) = 3 * 2 by norm_num] using h6)
  ·
    obtain ⟨eZ⟩ := hZA
    obtain ⟨e⟩ := hHe
    let f : ↥X →* NativeSporadic.He :=
      (((MulEquiv.subgroupCongr hXbar).trans e : ↥(X.map π) ≃* NativeSporadic.He) :
        ↥(X.map π) →* NativeSporadic.He).comp ρ
    have hf : Function.Surjective f :=
      ((MulEquiv.subgroupCongr hXbar).trans e).surjective.comp hρ
    have hfker : f.ker = ρ.ker := by
      ext x
      simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
        MonoidHom.coe_ofClass, map_eq_one_iff _ (MulEquiv.injective _)]
    have hf1 : f.ker = ⊥ :=
      CFSG.SectionRank.He_perfect_odd_cover_trivial f hf (hfker ▸ hker) (hfker ▸ hkerodd)
    have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hf1
    have eX : ↥X ≃* NativeSporadic.He := MulEquiv.ofBijective f ⟨hfinj, hf⟩
    refine Or.inr ⟨?_, ⟨eX⟩⟩
    have hAN : ∀ a ∈ A, a ∈ N → a = 1 := fun a ha haN => by
      have hax : a ∈ X := le_normalClosure ha
      have : (⟨a, hax⟩ : ↥X) ∈ f.ker := hfker ▸ (hmemker ⟨a, hax⟩).mpr haN
      rw [hf1, mem_bot] at this
      exact congrArg Subtype.val this
    let σ : ↥A →* ↥(A.map π) := π.subgroupMap A
    have hσinj : Function.Injective σ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker] at ha
      have hπ : π a = 1 := congrArg Subtype.val ha
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπ
      rw [mem_bot]
      exact Subtype.ext (hAN a a.2 hπ)
    let eA : ↥A ≃* ↥(A.map π) := MulEquiv.ofBijective σ ⟨hσinj, π.subgroupMap_surjective A⟩
    exact ⟨(Subgroup.centerCongr eA).trans eZ⟩

end Quotient

theorem l34General_of_oddCoreFree
    (h : L34OddCoreFree) (hSuz : SuzMultiplierSix) :
    L34General := by
  intro G _ _ A hH hL
  obtain ⟨hH', ⟨e⟩⟩ := rankTwoHyp_map hH
  exact l34Conclusion_of_map hSuz RankTwoSporadic.odd_card_standardComponentOddCore
    (RankTwoSporadic.standardComponentOddCore_le_centralizer hH.standard hH.rank)
    hH.standard.1.1 (h _ _ hH' (statedClassicalModel_of_mulEquiv e.symm hL)
      RankTwoSporadic.standardComponentOddCore_quotient_eq_bot)

theorem oddCoreFreeConclusion_of_l34Conclusion {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hO : standardComponentOddCore G = ⊥) (h : L34Conclusion A) : OddCoreFreeConclusion A := by
  unfold L34Conclusion IsSporadic at h
  rcases h with ⟨⟨e⟩, h3⟩ | hHe
  · refine Or.inl ⟨?_⟩
    have hZodd : Odd (Nat.card (center ↥(rankTwoX A))) :=
      Odd.of_dvd_nat (by norm_num) h3
    haveI : (rankTwoX A).Normal := normalClosure_normal
    let Z : Subgroup G := (center ↥(rankTwoX A)).map (rankTwoX A).subtype
    have hZn : Z.Normal := inferInstance
    have hZc : Nat.card Z = Nat.card (center ↥(rankTwoX A)) :=
      card_map_of_injective (rankTwoX A).subtype_injective
    have hZbot : Z = ⊥ := by
      have := RankTwoSporadic.le_standardComponentOddCore hZn (hZc ▸ hZodd)
      rwa [hO, le_bot_iff] at this
    have hc : center ↥(rankTwoX A) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (rankTwoX A).subtype_injective).mp hZbot
    exact (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans e
  · exact Or.inr hHe

theorem l34OddCoreFree_of_general (h : L34General) : L34OddCoreFree :=
  fun G _ _ A hH hL hO => oddCoreFreeConclusion_of_l34Conclusion hO (h G A hH hL)

theorem l34Step_of_oddCoreFree
    (hSuz : SuzMultiplierSix)
    (hstep : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
      L34GeneralBelow (Nat.card G) → RankTwoHypNF G A →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 →
      standardComponentOddCore G = ⊥ → OddCoreFreeConclusion A)
    (G : Type) [Group G] [Finite G] (A : Subgroup G) (hbelow : L34GeneralBelow (Nat.card G))
    (hH : RankTwoHypNF G A) (hL : Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2) :
    L34Conclusion A := by
  obtain ⟨hH', ⟨e⟩⟩ := rankTwoHyp_map hH
  have hle : Nat.card (G ⧸ standardComponentOddCore G) ≤ Nat.card G :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
  have hbelow' : L34GeneralBelow (Nat.card (G ⧸ standardComponentOddCore G)) :=
    fun G' _ _ A' hG' => hbelow G' A' (by omega)
  exact l34Conclusion_of_map hSuz RankTwoSporadic.odd_card_standardComponentOddCore
    (RankTwoSporadic.standardComponentOddCore_le_centralizer hH.standard hH.rank)
    hH.standard.1.1 (hstep _ _ hbelow' hH' (statedClassicalModel_of_mulEquiv e.symm hL)
      RankTwoSporadic.standardComponentOddCore_quotient_eq_bot)

theorem l34General_of_step
    (hstep : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
      L34GeneralBelow (Nat.card G) → RankTwoHypNF G A →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 → L34Conclusion A) :
    L34General := by
  suffices hn : ∀ n : ℕ, L34GeneralBelow n by
    intro G _ _ A hH hL
    exact hn (Nat.card G + 1) G A (Nat.lt_succ_self _) hH hL
  intro n
  induction n with
  | zero => intro G _ _ A hG; omega
  | succ n ih =>
    intro G _ _ A hG hH hL
    exact hstep G A (fun G' _ _ A' hG' => ih G' A' (by omega)) hH hL

theorem l34General_of_below
    (hSuz : SuzMultiplierSix)
    (hstep : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
      L34GeneralBelow (Nat.card G) → RankTwoHypNF G A →
      Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 →
      standardComponentOddCore G = ⊥ → OddCoreFreeConclusion A) :
    L34General :=
  l34General_of_step (l34Step_of_oddCoreFree hSuz hstep)

end CFSG.ComponentClassification.RankTwoL3Four
