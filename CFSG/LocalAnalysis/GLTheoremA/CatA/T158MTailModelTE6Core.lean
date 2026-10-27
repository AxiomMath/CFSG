module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailModelU6Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6NoAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Mark
import CFSG.LocalAnalysis.StandardType.GGTwE6LocalRankHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6R4RankSix
import CFSG.LocalAnalysis.StandardType.GGTwE6TInHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
import CFSG.LieType.SeitzGeneration.HyperIrrGroup
import CFSG.GroupTheory.ConjKerCenter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.T171Sh
open scoped commutatorElement

theorem te6_noAct_core
    {Ω : Type} [Group Ω] [Finite Ω] {L K A B T : Subgroup Ω} {d β : Ω} {n : ℕ}
    (hSetup : Setup 3 L K A d β) (hTE6 : catalogIs (PSimple 3 L) (S10.isTE6n n)) (hnodd : Odd n)
    (hAB : A ≤ B) (hBN0 : B ≤ Subgroup.normalizer (L : Set Ω)) (hA81 : 3 ^ 4 ≤ Nat.card A)
    (hBA : ∀ b ∈ B, ∃ a ∈ A, b * a⁻¹ ∈ Subgroup.centralizer (L : Set Ω))
    (hT2 : IsPGroup 2 T) (hTN : T ≤ Subgroup.normalizer (L : Set Ω))
    (hBT : B ≤ Subgroup.normalizer (T : Set Ω)) (hX : TwE6BigToralExit) :
    (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (L : Set Ω) := by
  have hE6cat : catalogIs (PSimple 3 L) (onLie fun i =>
      ∃ q, I171.I171LieShape 3 i ∧ i = .twistedE6 q) := by
    refine catalogIs_imp (fun i hi => ?_) hTE6
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
    twE6Marking_holds Ω L K A d β hSetup hE6cat
  letI := hKfield
  letI := hKfinite
  haveI : Finite (TwE6Delta.RecipeR K' n') := TwE6Delta.finite_recipeR hKcard
  haveI : Finite (MulAut (TwE6Delta.RecipeR K' n')) := TwE6Delta.finite_mulAut_recipeR hKcard
  have hL : commutator ↥L = ⊤ := hSetup.qs.1
  let N := Subgroup.normalizer (L : Set Ω)
  have hBN : B ≤ N := hBN0
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
  have hAb_le_Bt : Ab ≤ lamB.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨a, hAB a.2⟩, rfl⟩
  have hAb_eq_Bt : Ab = lamB.range := by
    refine le_antisymm hAb_le_Bt ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨a, ha, hba⟩ := hBA b hb
    refine ⟨⟨a, ha⟩, ?_⟩
    have hbaN : b * a⁻¹ ∈ N := N.mul_mem (hBN hb) (N.inv_mem (hAN ha))
    have h1 : lam ⟨b * a⁻¹, hbaN⟩ = 1 := ggLAut_eq_one_of_mem_centralizer L θ hba
    have h2 : lam ⟨b * a⁻¹, hbaN⟩ = lam ⟨b, hBN hb⟩ * (lam ⟨a, hAN ha⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    change lam ⟨a, hAN ha⟩ = lam ⟨b, hBN hb⟩
    rw [h2] at h1
    exact (mul_inv_eq_one.mp h1).symm
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
    obtain ⟨D, hDn, hID, hodd⟩ := TwE6Delta.ggOutdiagOdd_twE6 hn1 hKcard 3
    have h := commutator_range_le_inner' (L := L) θ hL (p := 3) hDn hID hodd
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
    exact hA81
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

end CFSG.LocalAnalysis.GLTheoremA.T158

end
