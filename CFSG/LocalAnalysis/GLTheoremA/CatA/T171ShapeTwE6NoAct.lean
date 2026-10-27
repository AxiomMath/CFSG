module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6MarkNoAct
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6R4RankSix
import CFSG.LocalAnalysis.StandardType.GGTwE6TInHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
import CFSG.LieType.SeitzGeneration.HyperIrrGroup
import CFSG.GroupTheory.ConjKerCenter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section M4


theorem twE6_commutator_range_le_inner {Ω : Type} [Group Ω] {L : Subgroup Ω} [L.Normal]
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n) (hL : commutator ↥L = ⊤)
    {B A T : Subgroup Ω} (hA : IsElemAbelian 3 A) (hT2 : IsPGroup 2 T)
    (hBN : B ≤ Subgroup.normalizer (L : Set Ω)) (hAB : A ≤ B)
    (hAI : ∀ a ha, ggLAut L θ ⟨a, hBN (hAB ha)⟩ ∈ TwE6Delta.RecipeI K n)
    (hTN : T ≤ Subgroup.normalizer (L : Set Ω)) (hBT : B ≤ Subgroup.normalizer (T : Set Ω)) :
    ⁅((ggLAut L θ).comp (Subgroup.inclusion hTN)).range,
      ((ggLAut L θ).comp (Subgroup.inclusion (fun a ha => hBN (hAB ha)))).range⁆ ≤
      (MulAut.conj : TwE6Delta.RecipeR K n →* MulAut (TwE6Delta.RecipeR K n)).range :=
  let ⟨_, hDn, hID, hodd⟩ := TwE6Delta.ggOutdiagOdd_twE6 hn hK 3
  commutator_range_le_inner θ hL hDn hID hodd hA hT2 hBN hAB hAI hTN hBT

end M4

section Rank


theorem three_pow_four_le_card_of_twE6 {Ω : Type} [Group Ω] [Finite Ω]
    {B A L : Subgroup Ω} {x : Ω}
    (hcfg : S171.Cfg Ω 3 B x L) (hmax : S171.MaxG 3 B)
    (hcardB : Nat.card B = 3 * Nat.card A)
    {n : ℕ} (hn : 1 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n) : 3 ^ 4 ≤ Nat.card A := by
  obtain ⟨U, hU1, hU2, E, hEU, hE, hcases⟩ :=
    ggTwE6LocalRankInput_holds n hn h3 K hK hs ↥L hcfg.qs.1 θ
  let E' : Subgroup Ω := E.map L.subtype
  let U' : Subgroup Ω := U.map L.subtype
  have hEL : E' ≤ L := Subgroup.map_subtype_le E
  have hUL : U' ≤ L := Subgroup.map_subtype_le U
  have hE' : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE L.subtype
  have hU'2 : IsPGroup 2 U' := IsPGroup.map hU2 L.subtype
  have hU'1 : U' ≠ ⊥ := by
    intro hbot
    exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U L.subtype_injective).mp hbot)
  have hEU' : E' ≤ Subgroup.normalizer (U' : Set Ω) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map (H := U) L.subtype)
  have hbound := card_le_of_twoLocal hcfg hmax hEL hUL hE' hU'2 hU'1 hEU'
  have hcyc : IsCyclic ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) :=
    hcfg.cyc _ inf_le_right (hE'.isPGroup.to_le inf_le_left)
  have hE'C : IsElemAbelian 3 (E' ⊓ Subgroup.centralizer (L : Set Ω)) :=
    hE'.mono inf_le_left
  have hc3 : Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) ≤ 3 :=
    CFSG.StandardType.TableB.card_le_of_isCyclic (p := 3) (by norm_num) hcyc hE'C.2
  have hE'card : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective
  rcases hcases with hE5 | ⟨hE4, hZbot⟩
  · have hle : 3 * 3 ^ 5 ≤ 3 * Nat.card A * 3 := by
      calc 3 * 3 ^ 5 = 3 * Nat.card E' := by rw [hE'card, hE5]
        _ ≤ Nat.card B * Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) := hbound
        _ = 3 * Nat.card A * Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) := by
            rw [hcardB]
        _ ≤ 3 * Nat.card A * 3 := by gcongr
    omega
  · have hinf : E' ⊓ Subgroup.centralizer (L : Set Ω) = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyE', hyC⟩
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hyE'
      have hcen : e ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hyC (l : Ω) l.2
      have hmem : e ∈ E ⊓ Subgroup.center ↥L := ⟨he, hcen⟩
      rw [hZbot, Subgroup.mem_bot] at hmem
      simpa [hmem]
    have hc1 : Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) = 1 := by
      rw [hinf, Subgroup.card_bot]
    have hle : 3 * 3 ^ 4 ≤ 3 * Nat.card A * 1 := by
      calc 3 * 3 ^ 4 = 3 * Nat.card E' := by rw [hE'card, hE4]
        _ ≤ Nat.card B * Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) := hbound
        _ = 3 * Nat.card A * Nat.card ↥(E' ⊓ Subgroup.centralizer (L : Set Ω)) := by
            rw [hcardB]
        _ = 3 * Nat.card A * 1 := by rw [hc1]
    omega

end Rank

section NoAct


theorem twE6NoAct_of (hM : TwE6Marking) (hX : TwE6BigToralExit) : TwE6NoAct := by
  intro p Ω _ _ B x L D K β n _ hcfg hmax hLN hpre hKcomp hch hβB hβD hni hext hcat hnodd
    T hTN hTx hT2 hBT
  obtain ⟨rfl, -, -, -⟩ := hext
  obtain ⟨A, d, hAB, -, hSetup, hcardB⟩ :=
    setup_of_cfg hcfg hpre hKcomp hch hβB hβD hni
  have hE6cat : catalogIs (PSimple 3 L) (onLie fun i =>
      ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q) := by
    refine catalogIs_imp (fun i hi => ?_) hcat
    cases i with
    | cyclic p hp => simp [S10.isTE6n, onLie] at hi
    | alternating k hk => simp [S10.isTE6n, onLie] at hi
    | sporadic s => simp [S10.isTE6n, onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedE6 q =>
        simp only [S10.isTE6n, onLie] at hi
        obtain ⟨hp, hnq⟩ := hi
        refine ⟨q, ⟨rfl, hp, ?_⟩, rfl⟩
        rw [TauCeti.PrimePower.card_def, hp, hnq]
        simpa using Odd.nat_add_dvd_pow_add_pow (x := 2) (y := 1) (n := n) hnodd
      | _ => simp [S10.isTE6n, onLie] at hi
  obtain ⟨n', K', hKfield, hKfinite, hn1, h3dvd, hKcard, hsimple, θ, hmark⟩ :=
    hM Ω L K A d β hSetup hE6cat
  letI := hKfield
  letI := hKfinite
  haveI : Finite (TwE6Delta.RecipeR K' n') := TwE6Delta.finite_recipeR hKcard
  haveI : Finite (MulAut (TwE6Delta.RecipeR K' n')) := TwE6Delta.finite_mulAut_recipeR hKcard
  haveI : L.Normal := hLN
  have hL : commutator ↥L = ⊤ := hcfg.qs.1
  let N := Subgroup.normalizer (L : Set Ω)
  have hBN : B ≤ N := hcfg.norm
  have hAN : A ≤ N := fun a ha => hBN (hAB ha)
  let R := TwE6Delta.RecipeR K' n'
  let lam : N →* MulAut R := ggLAut L θ
  let lamA : A →* MulAut R := lam.comp (Subgroup.inclusion hAN)
  let lamB : B →* MulAut R := lam.comp (Subgroup.inclusion hBN)
  let Ab : Subgroup (MulAut R) := lamA.range
  let lamT : Subgroup (MulAut R) := (lam.comp (Subgroup.inclusion hTN)).range
  let T1 : Subgroup (MulAut R) := ⁅lamT, Ab⁆
  have hAI : ∀ a ha, ggLAut L θ ⟨a, hAN ha⟩ ∈ TwE6Delta.RecipeI K' n' :=
    fun a ha => ggLAut_mem_of_induces L θ hAN hmark ha
  have hmapAb : Subgroup.map lam (A.subgroupOf N) = Ab := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a.1, ha⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨⟨a.1, hAN a.2⟩, a.2, rfl⟩
  have hAb : IsElemAbelian 3 Ab := by
    have h := (hSetup.elem.subgroupOf N).map lam
    rwa [hmapAb] at h
  have hkerA : lamA.ker = ⊥ := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      have hc : (a : Ω) ∈ Subgroup.centralizer (L : Set Ω) :=
        mem_centralizer_of_ggLAut_eq_one L θ hL h
      have hmem : (a : Ω) ∈ A ⊓ Subgroup.centralizer (L : Set Ω) := ⟨a.2, hc⟩
      rw [hSetup.faithful] at hmem
      exact Subtype.ext (by simpa using hmem)
    · intro ha
      rw [ha, map_one]
  have hcardA' : Nat.card Ab = Nat.card A := by
    have h := Subgroup.card_ker_mul_card_range lamA
    rw [hkerA, Subgroup.card_bot, one_mul] at h
    change Nat.card lamA.range = Nat.card A
    exact h
  have hkerB : lamB.ker = (Subgroup.zpowers x).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact (hcfg.cent b b.2).1 (mem_centralizer_of_ggLAut_eq_one L θ hL h)
    · intro hx
      exact ggLAut_eq_one_of_mem_centralizer L θ ((hcfg.cent b b.2).2 hx)
  have hcardB' : Nat.card lamB.range = Nat.card A := by
    have h := Subgroup.card_ker_mul_card_range lamB
    have hker : Nat.card ((Subgroup.zpowers x).subgroupOf B) = 3 := by
      rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hcfg.mem)).toEquiv,
        Nat.card_zpowers, orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one]
    rw [hkerB, hker, hcardB] at h
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hAb_le_Bt : Ab ≤ lamB.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hAB a.2⟩, rfl⟩
  have hAb_eq_Bt : Ab = lamB.range := by
    refine Subgroup.eq_of_le_of_card_ge hAb_le_Bt ?_
    rw [hcardB']
    exact Nat.le_of_eq hcardA'.symm
  have hAbNT : Ab ≤ Subgroup.normalizer (lamT : Set (MulAut R)) := by
    rw [hAb_eq_Bt, Subgroup.le_normalizer_iff]
    rintro _ ⟨⟨b, hb⟩, rfl⟩ y hy
    obtain ⟨⟨t, ht⟩, rfl⟩ := hy
    refine ⟨⟨b * t * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht⟩, ?_⟩
    change lam ⟨b * t * b⁻¹, _⟩ =
      lam ⟨b, hBN hb⟩ * lam ⟨t, hTN ht⟩ * (lam ⟨b, hBN hb⟩)⁻¹
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hT1_le_lamT : T1 ≤ lamT := by
    have h := (Subgroup.le_normalizer_iff_commutator_le_right (H := Ab) (K := lamT)).mp hAbNT
    rwa [Subgroup.commutator_comm] at h
  have hlamT2 : IsPGroup 2 lamT :=
    hT2.of_surjective ((lam.comp (Subgroup.inclusion hTN)).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hT1_2 : IsPGroup 2 T1 := hlamT2.to_le hT1_le_lamT
  have hT1_le_inn : T1 ≤ (MulAut.conj : R →* MulAut R).range := by
    have h := twE6_commutator_range_le_inner (L := L) (K := K') (n := n') hn1 hKcard θ hL
      hSetup.elem hT2 hBN hAB hAI hTN hBT
    simpa [T1, lamT, Ab, lam, lamA, lamB, R] using h
  have hRcenter : Subgroup.center R = ⊥ := TwE6Delta.center_recipeR_eq_bot hn1 hKcard
  have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [← MonoidHom.ker_eq_bot_iff, CFSG.GroupTheory.ker_conj_eq_center, hRcenter]
  let V : Subgroup R := T1.comap (MulAut.conj : R →* MulAut R)
  by_contra hne
  have hT1ne : T1 ≠ ⊥ := by
    intro hbot
    apply hne
    rw [Subgroup.commutator_le]
    intro t ht b hb
    have hbz : lamB ⟨b, hb⟩ ∈ Ab := by
      rw [hAb_eq_Bt]
      exact ⟨⟨b, hb⟩, rfl⟩
    have hmem : ⁅(lam.comp (Subgroup.inclusion hTN)) ⟨t, ht⟩, lamB ⟨b, hb⟩⁆ ∈ T1 :=
      Subgroup.commutator_mem_commutator (MonoidHom.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩) hbz
    rw [hbot] at hmem
    have hcomm : ⁅(lam.comp (Subgroup.inclusion hTN)) ⟨t, ht⟩, lamB ⟨b, hb⟩⁆ = 1 := by
      simpa using hmem
    have hzN : ⁅t, b⁆ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem (hTN ht) (hBN hb)) (N.inv_mem (hTN ht)))
        (N.inv_mem (hBN hb))
    have hlz : lam ⟨⁅t, b⁆, hzN⟩ = 1 := by
      have h1 : lam ⟨⁅t, b⁆, hzN⟩ = ⁅lam ⟨t, hTN ht⟩, lam ⟨b, hBN hb⟩⁆ := by
        have h := map_commutatorElement lam
          (⟨t, hTN ht⟩ : Subgroup.normalizer (L : Set Ω))
          (⟨b, hBN hb⟩ : Subgroup.normalizer (L : Set Ω))
        convert h using 3 <;> rfl
      rw [h1]
      exact hcomm
    exact mem_centralizer_of_ggLAut_eq_one L θ hL hlz
  have hV2 : IsPGroup 2 V :=
    hT1_2.comap_of_injective (MulAut.conj : R →* MulAut R) hconjinj
  have hVne : V ≠ ⊥ := by
    intro hVbot
    apply hT1ne
    have hmap := Subgroup.map_comap_eq_self (f := (MulAut.conj : R →* MulAut R)) hT1_le_inn
    change Subgroup.map (MulAut.conj : R →* MulAut R) V = T1 at hmap
    rw [hVbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  have hAbV : ∀ φ ∈ Ab, ∀ v ∈ V, φ v ∈ V := by
    intro φ hφ v hv
    change MulAut.conj (φ v) ∈ T1
    have h1 : (MulAut.conj (φ v) : MulAut R) = φ * MulAut.conj v * φ⁻¹ := by
      ext w
      simp [MulAut.conj_apply, MulAut.mul_apply]
    rw [h1]
    have hNT1 : Ab ≤ Subgroup.normalizer (T1 : Set (MulAut R)) :=
      Subgroup.normalizer_commutator_ge_right lamT Ab
    exact (Subgroup.mem_normalizer_iff.mp (hNT1 hφ) (MulAut.conj v)).mp hv
  have hcardAb4 : 3 ^ 4 ≤ Nat.card Ab := by
    rw [hcardA']
    exact three_pow_four_le_card_of_twE6 hcfg hmax hcardB hn1 h3dvd hKcard hsimple θ
  have hAbI : Ab ≤ TwE6Delta.RecipeI K' n' := by
    rintro _ ⟨a, rfl⟩
    exact hAI a a.2
  have hdinvA : d⁻¹ ∈ A := A.inv_mem hSetup.d_mem
  have hdN : d⁻¹ ∈ N := hAN hdinvA
  obtain ⟨φd, -, hφdind⟩ := hmark d hSetup.d_mem
  have hφdeq : φd = ggLAut L θ ⟨d⁻¹, hdN⟩ :=
    eq_ggLAut_of_induces L θ (hAN hSetup.d_mem) hφdind
  have hφdAb : φd ∈ Ab := by
    rw [hφdeq]
    exact ⟨⟨d⁻¹, hdinvA⟩, rfl⟩
  have hβinvA : β⁻¹ ∈ A := A.inv_mem hSetup.b_mem
  have hβinvN : β⁻¹ ∈ N := hAN hβinvA
  obtain ⟨φβ, -, hφβind⟩ := hmark β hSetup.b_mem
  have hφβeq : φβ = ggLAut L θ ⟨β⁻¹, hβinvN⟩ :=
    eq_ggLAut_of_induces L θ (hAN hSetup.b_mem) hφβind
  have hφβAb : φβ ∈ Ab := by
    rw [hφβeq]
    exact ⟨⟨β⁻¹, hβinvA⟩, rfl⟩
  let xa : ↥Ab := ⟨φd, hφdAb⟩
  let ya : ↥Ab := ⟨φβ, hφβAb⟩
  let W : Subgroup ↥Ab := Subgroup.closure ({xa, ya} : Set ↥Ab)
  have hxa3 : xa ^ 3 = 1 := by
    apply Subtype.ext
    change φd ^ 3 = 1
    exact hAb.2 φd hφdAb
  have hya3 : ya ^ 3 = 1 := by
    apply Subtype.ext
    change φβ ^ 3 = 1
    exact hAb.2 φβ hφβAb
  have hxaya : Commute xa ya := hAb.1.is_comm.comm xa ya
  have hW9 : Nat.card W ≤ 9 := by
    have h := CFSG.LieType.SeitzGeneration.card_closure_pair_le (p := 3)
      (by norm_num) hxaya hxa3 hya3
    simpa [W] using h
  have hW3 : IsPGroup 3 W := hAb.isPGroup.to_subgroup W
  obtain ⟨k, hk⟩ := hW3.exists_card_eq
  have hk2 : k ≤ 2 := by
    have h : 3 ^ k ≤ 3 ^ 2 := by
      rw [← hk]
      norm_num
      exact hW9
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hWdvd : Nat.card W ∣ 3 ^ 4 := by
    rw [hk]
    exact pow_dvd_pow 3 (by omega : k ≤ 4)
  obtain ⟨r, hr⟩ := hAb.isPGroup.exists_card_eq
  have hr4 : 4 ≤ r := by
    have h : 3 ^ 4 ≤ 3 ^ r := by rw [← hr]; exact hcardAb4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
  have hAbdvd : 3 ^ 4 ∣ Nat.card (⊤ : Subgroup ↥Ab) := by
    rw [Subgroup.card_top, hr]
    exact pow_dvd_pow 3 hr4
  obtain ⟨S₀, hS₀card, hWS₀, -⟩ := Sylow.exists_subgroup_card_pow_prime_le_le
    (p := 3) (n := 4) Nat.prime_three hWdvd hAbdvd le_top
  let S : Subgroup (MulAut R) := S₀.map Ab.subtype
  have hScard : Nat.card S = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective Ab.subtype_injective, hS₀card]
  have hSleAb : S ≤ Ab := Subgroup.map_subtype_le S₀
  have hS : IsElemAbelian 3 S := hAb.mono hSleAb
  have hSI : ∀ φ ∈ S, φ ∈ TwE6Delta.RecipeI K' n' := fun φ hφ => hAbI (hSleAb hφ)
  have hxaW : xa ∈ W := Subgroup.subset_closure (by simp)
  have hxaS₀ : xa ∈ S₀ := hWS₀ hxaW
  have hφdS : φd ∈ S := ⟨xa, hxaS₀, rfl⟩
  have hyaW : ya ∈ W := Subgroup.subset_closure (by simp)
  have hyaS₀ : ya ∈ S₀ := hWS₀ hyaW
  have hφβS : φβ ∈ S := ⟨ya, hyaS₀, rfl⟩
  have hSV : ∀ φ ∈ S, ∀ v ∈ V, φ v ∈ V := fun φ hφ => hAbV φ (hSleAb hφ)
  obtain ⟨Y, hSY, hYI, hYel, hYcard⟩ :=
    CFSG.StandardType.TwE6R4.exists_rankSix_recipe
      CFSG.StandardType.NoOffTwE6Three.ggTwE6ThreeTwoLocalInnToralInput_holds
      CFSG.StandardType.TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput
      hn1 hKcard h3dvd hS hSI hScard hVne hV2 hSV
  have hY5 : 3 ^ 5 ≤ Nat.card Y := by
    rw [hYcard]
    norm_num
  exact hSetup.nonID (hX Ω L K A d β n' K' hn1 hKcard h3dvd hSetup θ Y
    hYel hY5 hYI ⟨φd, hSY hφdS, hφdind⟩ ⟨φβ, hSY hφβS, hφβind⟩)

end NoAct

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
