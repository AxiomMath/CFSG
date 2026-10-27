module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveOneSylow

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace One

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6 Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist

set_option linter.unusedSectionVars false

section Col

variable {K : Type} [Field K] [Finite K]

@[expose] def rhoE {E : Subgroup (adjointGroup Tag.E8 K)} (hEN : E ≤ monomialN K) :
    E →* WeylGroup Tag.E8 :=
  (rhoN K).comp (Subgroup.inclusion hEN)

theorem exists_col_of_comm {ζ : K} (hζ : IsPrimitiveRoot ζ 5) {y : ModGL Tag.E8 K}
    (hy : y ∈ monomialSubgroup Tag.E8 K) {w : WeylGroup Tag.E8}
    (hyw : weylQuotientHom Tag.E8 K ⟨y, hy⟩ = w) {t : ModGL Tag.E8 K}
    (htT : t ∈ torusGroup Tag.E8 K) (ht5 : t ^ 5 = 1) (hcomm : y * t = t * y) :
    ∃ z : Fin Tag.E8.rank → ZMod 5, z ∈ fixSet w ∧
      t = rootDiagUnit Tag.E8 (fun i => griessU hζ ^ (z i).val) := by
  obtain ⟨b, rfl⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup htT
  have hb5 : ∀ i, b i ^ 5 = 1 := by
    have h1 : rootDiagUnit Tag.E8 (b ^ 5) = 1 := by
      have hpow : rootDiagUnit Tag.E8 b ^ 5 = rootDiagUnit Tag.E8 (b ^ 5) :=
        ((rootDiagUnitHom Tag.E8 K).map_pow b 5).symm
      rw [← hpow]
      exact ht5
    have h2 : b ^ 5 = 1 := rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    exact fun i => congrFun h2 i
  have hprim : IsPrimitiveRoot (griessU hζ) 5 := griessU_prim hζ
  have hord : orderOf (griessU hζ) = 5 := hprim.eq_orderOf.symm
  have hexp : ∀ i, ∃ n : ℕ, b i = griessU hζ ^ n := fun i => by
    have hi : ((b i : Kˣ) : K) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hb5 i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hζ.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  have hz : ∀ i, (fun i => (e i : ZMod 5)) i = (e i : ZMod 5) := fun i => rfl
  refine ⟨fun i => (e i : ZMod 5), ?_, ?_⟩
  · have hconj : y * rootDiagUnit Tag.E8 b * y⁻¹ = rootDiagUnit Tag.E8 b := by
      rw [hcomm]
      group
    have hact := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
      (⟨y, hy⟩ : monomialSubgroup Tag.E8 K) b
    rw [hyw] at hact
    have heq : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w b = b :=
      rootDiagUnit_injective (hact.symm.trans hconj)
    have hchar : ∀ u, rootChar b (w⁻¹ • u) = rootChar b u := fun u => by
      have := congrArg (fun b' => rootChar b' u) heq
      simpa [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct] using this
    have hstab : w⁻¹ ∈ dualWeylStabilizer (fun i => (e i : ZMod 5)) := fun u =>
      (rootChar_eq_rootChar_iff hord e b he (w⁻¹ • u) u).1 (hchar u)
    have : w ∈ dualWeylStabilizer (fun i => (e i : ZMod 5)) := by simpa using inv_mem hstab
    exact this
  · congr 1
    funext i
    rw [he i]
    show griessU hζ ^ e i = griessU hζ ^ ((e i : ZMod 5)).val
    rw [ZMod.val_natCast, ← hord, pow_mod_orderOf]

end Col

section Core

variable {K : Type} [Field K] [Finite K] {ζ : K}

theorem czVec_val_lt : ∀ i : Fin Tag.E8.rank, ((czVec i : ℕ) : ZMod 5).val = czVec i := by
  decide

theorem cxVec_val_lt : ∀ i : Fin Tag.E8.rank, ((cxVec i : ℕ) : ZMod 5).val = cxVec i := by
  decide

theorem cyclic_core (hζ : IsPrimitiveRoot ζ 5) {E : Subgroup (adjointGroup Tag.E8 K)}
    (hE : CFSG.Open.IsElemAbelian 5 E) (hcard : Nat.card E = 5 ^ 3) (hEN : E ≤ monomialN K)
    (hR : (rhoE hEN).range = Subgroup.zpowers griessW) :
    ∃ a : Fin Tag.E8.rank → Kˣ, E = griessCubeT hζ a := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨y0, hy0⟩ : ∃ y : E, rhoE hEN y = griessW := by
    have : griessW ∈ (rhoE hEN).range := hR ▸ Subgroup.mem_zpowers _
    exact this
  have hy0M : ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K :=
    hEN y0.2
  have hy0w : weylQuotientHom Tag.E8 K ⟨_, hy0M⟩ = griessW := hy0
  obtain ⟨a, ha⟩ : ∃ a, rootDiagUnit Tag.E8 a =
      (griessY K)⁻¹ * ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := by
    have hm : (griessY K)⁻¹ * ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈
        monomialSubgroup Tag.E8 K := mul_mem (inv_mem griessY_mono) hy0M
    have h1 : weylQuotientHom Tag.E8 K ⟨_, hm⟩ = 1 := by
      have e : (⟨(griessY K)⁻¹ * ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K), hm⟩ :
          monomialSubgroup Tag.E8 K) = ⟨griessY K, griessY_mono⟩⁻¹ * ⟨_, hy0M⟩ := rfl
      rw [e, map_mul, map_inv, weylQuotient_griessY, hy0w, inv_mul_cancel]
    exact CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup
      ((Four.weylQuotientHom_eq_one_iff hm).1 h1)
  have hy0eq : ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) = griessYT K a := by
    rw [griessYT, ha]
    group
  have hK0card : Nat.card (rhoE hEN).ker = 25 := by
    have h1 := Subgroup.card_mul_index (rhoE hEN).ker
    have h2 : Nat.card (rhoE hEN).range = 5 := by
      rw [hR, Nat.card_zpowers, orderOf_griessW]
    rw [Subgroup.index_ker, h2, hcard] at h1
    omega
  set u : Kˣ := griessU hζ with hu
  have hKsub : ∀ k ∈ (rhoE hEN).ker, ∃ z ∈ fixSet griessW,
      ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        rootDiagUnit Tag.E8 (fun i => u ^ (z i).val) := by
    intro k hk
    have hkM : ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ∈ monomialSubgroup Tag.E8 K :=
      hEN k.2
    have hk1 : weylQuotientHom Tag.E8 K ⟨_, hkM⟩ = 1 := hk
    have hkT := (Four.weylQuotientHom_eq_one_iff hkM).1 hk1
    have hk5 : ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) ^ 5 = 1 := by
      have := hE.2 k k.2
      have h' := congrArg (fun g : adjointGroup Tag.E8 K => (g : ModGL Tag.E8 K)) this
      simpa using h'
    have hcomm : ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
        ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
          ((y0 : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := by
      have := hE.1.is_comm.comm y0 k
      have h' := congrArg (fun g : E => ((g : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) this
      simpa using h'
    exact exists_col_of_comm hζ hy0M hy0w hkT hk5 hcomm
  let colSet : Set (ModGL Tag.E8 K) :=
    (fun z : Fin Tag.E8.rank → ZMod 5 => rootDiagUnit Tag.E8 (fun i => u ^ (z i).val)) ''
      fixSet griessW
  let Sset : Set (ModGL Tag.E8 K) :=
    (fun k : E => ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) '' ((rhoE hEN).ker : Set E)
  have hinj : Function.Injective (fun k : E => ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)) :=
    fun k l h => Subtype.ext (Subtype.ext h)
  have hSnc : Sset.ncard = 25 := by
    rw [Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
    exact hK0card
  have hsub : Sset ⊆ colSet := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨z, hz, hkz⟩ := hKsub k hk
    exact ⟨z, hz, hkz.symm⟩
  have hcolnc : colSet.ncard ≤ 25 :=
    (Set.ncard_image_le (Set.toFinite _)).trans ncard_fixSet_griessW_le
  have hSeq : Sset = colSet :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hSnc]; exact hcolnc) (Set.toFinite _)
  have hmemE : ∀ (c : Fin Tag.E8.rank → ZMod 5), c ∈ fixSet griessW →
      ∃ k ∈ (rhoE hEN).ker, ((k : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) =
        rootDiagUnit Tag.E8 (fun i => u ^ (c i).val) := by
    intro c hc
    have : rootDiagUnit Tag.E8 (fun i => u ^ (c i).val) ∈ Sset := by
      rw [hSeq]
      exact ⟨c, hc, rfl⟩
    obtain ⟨k, hk, hkc⟩ := this
    exact ⟨k, hk, hkc⟩
  have hZE : griessZA hζ ∈ E := by
    obtain ⟨k, -, hk⟩ := hmemE czCol czCol_mem_fixSet
    have : griessZA hζ = (k : adjointGroup Tag.E8 K) := by
      apply Subtype.ext
      rw [hk]
      show rootDiagUnit Tag.E8 (fun k => griessU hζ ^ czVec k) = _
      congr 1
      funext i
      show u ^ czVec i = u ^ (czCol i).val
      rw [czCol, czVec_val_lt]
    rw [this]
    exact k.2
  have hXE : griessXA hζ ∈ E := by
    obtain ⟨k, -, hk⟩ := hmemE cxCol cxCol_mem_fixSet
    have : griessXA hζ = (k : adjointGroup Tag.E8 K) := by
      apply Subtype.ext
      rw [hk]
      show rootDiagUnit Tag.E8 (fun k => griessU hζ ^ cxVec k) = _
      congr 1
      funext i
      show u ^ cxVec i = u ^ (cxCol i).val
      rw [cxCol, cxVec_val_lt]
    rw [this]
    exact k.2
  have hYE : griessYTA K a ∈ E := by
    have : griessYTA K a = (y0 : adjointGroup Tag.E8 K) := Subtype.ext hy0eq.symm
    rw [this]
    exact y0.2
  have hle : griessCubeT hζ a ≤ E := by
    rw [griessCubeT_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact hZE
    · exact hXE
    · exact hYE
  exact ⟨a, (Subgroup.eq_of_le_of_card_ge hle (by rw [griessCubeT_card hζ a, hcard])).symm⟩

end Core

end One

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
