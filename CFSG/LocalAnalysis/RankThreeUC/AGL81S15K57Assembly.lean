module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K57Chain
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K57StepA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541EvenAssembly
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderSplit

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement

section Center

theorem exists_center_ne_one {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) :
    ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F), z ≠ 1 := by
  classical
  obtain ⟨k, hk⟩ := hn
  haveI : Fintype F := Fintype.ofFinite F
  have h3 : 3 ∣ Nat.card Fˣ := by
    have hc : Nat.card Fˣ = 2 ^ n - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
    rw [hc, hk, ← two_mul, pow_mul]
    have := Nat.sub_one_dvd_pow_sub_one (2 ^ 2) k
    norm_num at this ⊢
    exact this
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hω3 : ((ω : F)) ^ Fintype.card (Fin 3) = 1 := by
    rw [Fintype.card_fin, ← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one]
    rfl
  let ζ := rootsOfUnity.mkOfPowEq (ω : F) hω3
  have hζ : ζ ≠ 1 := by
    intro h
    have h1 : (ω : F) = 1 := by
      have := congrArg (fun x : rootsOfUnity (Fintype.card (Fin 3)) F => ((x : Fˣ) : F)) h
      simpa [ζ, rootsOfUnity.coe_mkOfPowEq] using this
    have h2 : ω = 1 := Units.ext h1
    rw [h2, orderOf_one] at hω
    omega
  let e0 := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  refine ⟨(e0.symm ζ).1, (e0.symm ζ).2, fun h => hζ ?_⟩
  have h1 : e0.symm ζ = 1 := Subtype.ext h
  simpa using congrArg e0 h1

end Center

section Action

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def invAct (ρ : G →* Module.End (ZMod 2) W) (M : Subgroup G) (U : Submodule (ZMod 2) W)
    (hU : K57StepB.IsInv ρ M U) : ↥M →* Module.End (ZMod 2) ↥U where
  toFun m := (ρ m).restrict fun u hu => hU m m.2 u hu
  map_one' := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp
  map_mul' a b := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    simp

theorem mem_ker_invAct {ρ : G →* Module.End (ZMod 2) W} {M : Subgroup G}
    {U : Submodule (ZMod 2) W} (hU : K57StepB.IsInv ρ M U) {m : ↥M} :
    m ∈ (invAct ρ M U hU).ker ↔ ∀ u ∈ U, ρ m u = u := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h u hu
    exact congrArg Subtype.val (LinearMap.congr_fun h ⟨u, hu⟩)
  · intro h
    exact LinearMap.ext fun u => Subtype.ext (h u u.2)

end Action

section Main

theorem K57_of_count (hcount : K541CountEven) : K57 := by
  intro X _ _ T hGN Ls hL hJ n hn hEven hLiso x hx hZ
  obtain ⟨e⟩ := hLiso
  have hcnt := hcount X T hGN Ls hL hJ n hn hEven ⟨e⟩
  set g : X ⧸ gnC T := toStar T x with hg
  have hmem : ∀ y, g * y * g⁻¹ ∈ KFactsPair.conjSub g Ls ↔ y ∈ Ls := fun y => by
    constructor
    · rintro ⟨y', hy', hyy⟩
      have h1 : g * y' * g⁻¹ = g * y * g⁻¹ := hyy
      have h2 : y' = y := mul_left_cancel (mul_right_cancel h1)
      rwa [← h2]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hLne : Ls ≠ ⊥ := ne_bot_of_isComponentOf hL
  have hM : CFSG.Open.IsComponentOf (KFactsPair.conjSub g Ls) ⊤ := by
    refine CFSG.ComponentClassification.LocalComponents.image hL (MulAut.conj g).toMonoidHom
      (MulAut.conj g).surjective fun hle => hLne ?_
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g).injective] at hle
    exact le_bot_iff.mp hle
  let eM : ↥(KFactsPair.conjSub g Ls) ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n) :=
    (Subgroup.equivMapOfInjective Ls (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e
  set M : Subgroup (X ⧸ gnC T) := KFactsPair.conjSub g Ls with hMdef
  have hne : Ls ≠ M := by
    intro h
    apply hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hy := hmem y
    rw [← h] at hy
    exact hy.symm
  have hcomm : ⁅Ls, M⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne Ls M hL hM hne
  have hLM : ∀ l ∈ Ls, ∀ m ∈ M, l * m = m * l := fun l hl m hm => by
    have h1 : ⁅l, m⁆ ∈ ⁅Ls, M⁆ := Subgroup.commutator_mem_commutator hl hm
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨z₀, hz₀c, hz₀ne⟩ := exists_center_ne_one hF hEven
  let zL : ↥Ls := e.symm z₀
  have hez : e zL = z₀ := e.apply_symm_apply z₀
  have hzLc : zL ∈ Subgroup.center ↥Ls := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul, hez]
    exact Subgroup.mem_center_iff.mp hz₀c (e a)
  have hzL3 : zL ^ 3 = 1 := center_pow_three e zL hzLc
  have hzL1 : zL ≠ 1 := fun h => hz₀ne (by rw [← hez, h, map_one])
  have hz3 : (zL : X ⧸ gnC T) ^ 3 = 1 := by
    have := congrArg Subtype.val hzL3
    simpa using this
  have hz1 : (zL : X ⧸ gnC T) ≠ 1 := fun h => hzL1 (Subtype.ext h)
  have hzcL : ∀ l ∈ Ls, l * (zL : X ⧸ gnC T) = (zL : X ⧸ gnC T) * l := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzLc ⟨l, hl⟩)
  have hzZ : (zL : X ⧸ gnC T) ∈ CFSG.centerIn Ls := by
    rw [CFSG.centerIn_eq_map_center]
    exact Subgroup.mem_map.mpr ⟨zL, hzLc, rfl⟩
  rw [hZ, CFSG.centerIn_eq_map_center] at hzZ
  obtain ⟨y, hyc, hyz⟩ := Subgroup.mem_map.mp hzZ
  have hyz' : (y : X ⧸ gnC T) = (zL : X ⧸ gnC T) := hyz
  have hzcM : ∀ m ∈ M, m * (zL : X ⧸ gnC T) = (zL : X ⧸ gnC T) * m := fun m hm => by
    have h1 : m * (y : X ⧸ gnC T) = (y : X ⧸ gnC T) * m :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨m, hm⟩)
    rwa [hyz'] at h1
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hGN
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hUL := isInv_range_of_commute (gnRep hV) Ls hzcL
  have hUM := isInv_range_of_commute (gnRep hV) M hzcM
  have hlen := noChainThree_range hV zL.2 hz3 hcnt
  obtain ⟨c, hcn, hcU⟩ := K57StepB.exists_noncentral_acting_trivially (gnRep hV) Ls M hLM eM _
    hlen hUL hUM
  have hker : c ∈ (invAct (gnRep hV) M _ hUM).ker := (mem_ker_invAct hUM).mpr hcU
  have hKtop : (invAct (gnRep hV) M _ hUM).ker = ⊤ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hM.2.2
        (invAct (gnRep hV) M _ hUM).ker with h | h
    · exact (hcn (h hker)).elim
    · exact h
  have hyK : y ∈ (invAct (gnRep hV) M _ hUM).ker := by
    rw [hKtop]
    trivial
  have hyU := (mem_ker_invAct hUM).mp hyK
  have hU0 : LinearMap.range (gnRep hV (zL : X ⧸ gnC T) - 1) ≤ ⊥ :=
    le_of_sub_mem (ρ := gnRep hV) hz3 le_rfl
      (fun w hw => by
        rw [Submodule.mem_bot] at hw ⊢
        rw [hw, map_zero])
      (fun w hw => by
        rw [Submodule.mem_bot]
        have h1 := hyU w hw
        rw [hyz'] at h1
        rw [h1, sub_self])
  have hρz : gnRep hV (zL : X ⧸ gnC T) = 1 := LinearMap.ext fun v => by
    have hv : gnRep hV (zL : X ⧸ gnC T) v - v ∈
        LinearMap.range (gnRep hV (zL : X ⧸ gnC T) - 1) := ⟨v, by simp⟩
    have h1 := hU0 hv
    rw [Submodule.mem_bot, sub_eq_zero] at h1
    simpa using h1
  exact hz1 (gnRep_injective hV (hρz.trans (map_one _).symm))

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15
