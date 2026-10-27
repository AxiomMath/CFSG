module

public import CFSG.CGT.PushingUpLit.BHS6.NestedSym
public import CFSG.CGT.PushingUpLit.BHS6.NestedSix
public import CFSG.CGT.PushingUpLit.BHS6.NestedTransvection

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

omit [Group Γ] in
theorem exists_psi_conj [Group Γ] {E B W : Subgroup Γ} {S : Type*} [Group S]
    (ψ : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) →* S)
    (hBW : B ≤ Subgroup.normalizer (W : Set Γ)) (hBE : B ≤ Subgroup.normalizer (E : Set Γ))
    {g b : Γ} (hgE : g ∈ E) (hb : b ∈ B) (hgW : g ∈ Subgroup.normalizer (W : Set Γ))
    (hgN : conjAct W ⟨g, hgW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W))) :
    ∃ (hbW : b ∈ Subgroup.normalizer (W : Set Γ))
      (hbN : conjAct W ⟨b, hbW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))
      (_hyE : g * b * g⁻¹ ∈ Subgroup.normalizer (E : Set Γ))
      (hyW : g * b * g⁻¹ ∈ Subgroup.normalizer (W : Set Γ))
      (hzN : conjAct W ⟨g * b * g⁻¹, hyW⟩ ∈
        Subgroup.normalizer (autOn E W : Set (MulAut ↥W))),
      ψ ⟨conjAct W ⟨g * b * g⁻¹, hyW⟩, hzN⟩ =
        ψ ⟨conjAct W ⟨g, hgW⟩, hgN⟩ * ψ ⟨conjAct W ⟨b, hbW⟩, hbN⟩ *
          (ψ ⟨conjAct W ⟨g, hgW⟩, hgN⟩)⁻¹ := by
  have hbW : b ∈ Subgroup.normalizer (W : Set Γ) := hBW hb
  have hcb : conjAct W ⟨b, hbW⟩ ∈ autOn B W := mem_autOn_iff.mpr ⟨⟨b, hbW⟩, hb, rfl⟩
  have hbN : conjAct W ⟨b, hbW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hBW hBE hcb
  have hgNE : g ∈ Subgroup.normalizer (E : Set Γ) := Subgroup.le_normalizer hgE
  have hyE : g * b * g⁻¹ ∈ Subgroup.normalizer (E : Set Γ) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgNE (hBE hb))
      ((Subgroup.normalizer _).inv_mem hgNE)
  have hyW : g * b * g⁻¹ ∈ Subgroup.normalizer (W : Set Γ) :=
    (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgW hbW)
      ((Subgroup.normalizer _).inv_mem hgW)
  have hconj : conjAct W ⟨g * b * g⁻¹, hyW⟩ =
      conjAct W ⟨g, hgW⟩ * conjAct W ⟨b, hbW⟩ * (conjAct W ⟨g, hgW⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hzN : conjAct W ⟨g * b * g⁻¹, hyW⟩ ∈
      Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) := by
    rw [hconj]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgN hbN)
      ((Subgroup.normalizer _).inv_mem hgN)
  refine ⟨hbW, hbN, hyE, hyW, hzN, ?_⟩
  have e : (⟨conjAct W ⟨g * b * g⁻¹, hyW⟩, hzN⟩ :
      ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) =
      ⟨conjAct W ⟨g, hgW⟩, hgN⟩ * ⟨conjAct W ⟨b, hbW⟩, hbN⟩ * ⟨conjAct W ⟨g, hgW⟩, hgN⟩⁻¹ :=
    Subtype.ext hconj
  rw [e, map_mul, map_mul, map_inv]

section Finite

variable [Finite Γ] {G T E F : Subgroup Γ}

theorem false_of_linear_le_symm (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m) (hF : F ∈ btBlocksG G T) (hFE : F ≤ E)
    {k : ℕ} (hk2 : 2 ≤ k) (hFk : IsNaturalSLTwoModule ↥F k) : False := by
  classical
  have hF' := hF
  obtain ⟨s, hs, hFs⟩ := hF'
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS' : IsSylowTwoOf (A1b.conjSub s T) G := isSylowTwoOf_conjSub_of_mem hT' hs
  have hS : IsSylowOf 2 (A1b.conjSub s T) G := isSylowOf_of_isSylowTwoOf hS'
  have hcharF : CharTwo F := charTwo_of_isBTBlock hG hS hFs
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hFW : F ≤ Subgroup.normalizer (W : Set Γ) := hFE.trans hEW
  obtain ⟨D, ψ, hψβ, hβbij, hψbij, -, -, k₀, hk₀1, -, hswap, -, -⟩ :=
    block_structure_symm hG hT hE hm hn hWdef hWe
  have hn3 : 3 ≤ 2 * m + 1 := by omega
  have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
  let βe : ↥W ≃* ↥(coreMod (2 * m + 1)) := MulEquiv.ofBijective D.β hβbij
  have hψ' : ∀ (a : ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) (w : ↥W),
      βe ((a : MulAut ↥W) w) = coreAct (2 * m + 1) (ψ a) (βe w) := fun a w => hψβ a w
  have hψinj : Function.Injective ψ := hψbij.1
  set Ft : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := (modelHom hFE hEW ψ).range with hFt
  have hFres : opResidual 2 F = F := opResidual_eq_of_isBTBlock hFs
  have hFtres : opResidual 2 Ft = Ft := opResidual_range_of_eq hFres _
  have hirr : IsIrrSection (Ft.map (coreAct (2 * m + 1)))
      (commV (Ft.map (coreAct (2 * m + 1))) ⊔ fixV (Ft.map (coreAct (2 * m + 1))))
      (fixV (Ft.map (coreAct (2 * m + 1)))) :=
    isIrrSection_eq_map_congr βe (map_range_modelHom hFE hEW βe ψ hψ')
      (isIrrSection_autOn_nested hG hT hE hF hFE hWe)
  have hW'W : pCoreOf 2 F ≤ W := pCoreOf_le_of_le_block hG hT hE hF hFE
  have hFcomm : ⁅F, W⁆ = pCoreOf 2 F := commutator_eq_pCoreOf_nested hG hT hE hF hFE
  have hne : ⁅F, W⁆ ≠ ⊥ := by
    rw [hFcomm]
    exact pCoreOf_ne_bot hFs hcharF
  have hSLamb : @IsSLNatSection ↥W (commGroupOfElemAbelian hWe) (autOn F W) (commOn hWe F)
      (commOn hWe F ⊓ fixOn hWe F) k :=
    isSLNatSection_autOn_of_isBTBlock hG hS hFs hFk hWe (pCoreOf_le_pCoreOf_G hG hT hE) hFW hne
  have hSL : IsSLNatSection (Ft.map (coreAct (2 * m + 1)))
      (commV (Ft.map (coreAct (2 * m + 1))))
      (fixV (Ft.map (coreAct (2 * m + 1))) ⊓ commV (Ft.map (coreAct (2 * m + 1)))) k :=
    isSLNatSection_eq_map_congr βe (map_range_modelHom hFE hEW βe ψ hψ') hSLamb
  obtain ⟨-, hΩ6⟩ := card_movFin_eq_six_of_irr hodd hFtres hirr k hSL
  obtain ⟨T', hs', hc', hcard', hB⟩ := hswap
  obtain ⟨t₀, ht₀⟩ : T'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨π, hπ, hπT, a, ha, b, hb, hab, hπt₀⟩ := exists_even_conj_inside hodd ht₀ hs' hc' hΩ6
  obtain ⟨g, hgW, hgE, hgN, hgπ⟩ := exists_lift_of_mem_alt hWe hn3 D ψ hψβ hπ
  have hgG : g ∈ G := hE.le hgE
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have ht₀B : t₀ ∈ ((autOn (baum T) W).subgroupOf
      (Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))).map ψ := by
    rw [hB]
    exact Subgroup.subset_closure ht₀
  obtain ⟨a', ha', hψa'⟩ := Subgroup.mem_map.mp ht₀B
  obtain ⟨x, hxB, hxa⟩ := mem_autOn_iff.mp (Subgroup.mem_subgroupOf.mp ha')
  obtain ⟨hbW, hbN, -, hyW, hzN, hψy⟩ := exists_psi_conj ψ hBW hBN hgE hxB hgW hgN
  have hψy₀ : ψ ⟨conjAct W ⟨g * (x : Γ) * g⁻¹, hyW⟩, hzN⟩ = Equiv.swap a b := by
    rw [hψy, hgπ]
    have h1 : ψ ⟨conjAct W ⟨(x : Γ), hbW⟩, hbN⟩ = t₀ := by
      rw [← hψa']
      congr 1
      exact Subtype.ext hxa
    rw [h1]
    exact hπt₀
  obtain ⟨x₀, hx₀⟩ := exists_moved_of_irr hirr
  have hsame : ∀ c, (∃ f ∈ Ft, f c ≠ c) → ∃ f ∈ Ft, f x₀ = c := fun c hc =>
    same_orbit_of_moved hodd hFtres hirr hc hx₀
  have hcommA : commV (autOn F W) = (pCoreOf 2 F).subgroupOf W := by
    have := commOn_eq hWe hFW
    rw [hFcomm] at this
    exact this
  have memP : ∀ v : ↥W, βe v ∈ commV (Ft.map (coreAct (2 * m + 1))) ↔
      (v : Γ) ∈ pCoreOf 2 F := fun v => by
    refine (mem_commV_eq_map_congr βe (map_range_modelHom hFE hEW βe ψ hψ') v).trans ?_
    rw [hcommA, Subgroup.mem_subgroupOf]
  have hstabΩ : ∀ z ∈ baum (A1b.conjSub g T), ∃ (hzW : z ∈ Subgroup.normalizer (W : Set Γ))
      (hzN : conjAct W ⟨z, hzW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W))),
      ψ ⟨conjAct W ⟨z, hzW⟩, hzN⟩ ∈ setStab (movFin Ft) := by
    intro z hz
    rw [baum_conjSub] at hz
    have hzb : g⁻¹ * z * g ∈ baum T := A1b.mem_conjSub_iff.mp hz
    obtain ⟨c, hcb, rfl⟩ : ∃ c ∈ baum T, z = g * c * g⁻¹ := ⟨g⁻¹ * z * g, hzb, by group⟩
    obtain ⟨hcW, hcN, -, hzW, hzN', hψz⟩ := exists_psi_conj ψ hBW hBN hgE hcb hgW hgN
    refine ⟨hzW, hzN', ?_⟩
    rw [hψz, hgπ]
    apply hπT
    rw [← hB]
    exact ⟨⟨conjAct W ⟨c, hcW⟩, hcN⟩,
      Subgroup.mem_subgroupOf.mpr (mem_autOn_iff.mpr ⟨⟨c, hcW⟩, hcb, rfl⟩), rfl⟩
  have hnormW' : ∀ z ∈ baum (A1b.conjSub g T), ∀ w ∈ pCoreOf 2 F,
      z * w * z⁻¹ ∈ pCoreOf 2 F := by
    intro z hz w hw
    obtain ⟨hzW, hzN, hstz⟩ := hstabΩ z hz
    have hwW : w ∈ W := hW'W hw
    have h1 : βe ⟨w, hwW⟩ ∈ commV (Ft.map (coreAct (2 * m + 1))) := (memP ⟨w, hwW⟩).2 hw
    have h2 : coreAct (2 * m + 1) (ψ ⟨conjAct W ⟨z, hzW⟩, hzN⟩) (βe ⟨w, hwW⟩) ∈
        commV (Ft.map (coreAct (2 * m + 1))) :=
      coreAct_mem_commV_of_mem_setStab hodd hsame hstz h1
    rw [← hψ' ⟨conjAct W ⟨z, hzW⟩, hzN⟩ ⟨w, hwW⟩] at h2
    have h3 := (memP _).1 h2
    have e : (((conjAct W ⟨z, hzW⟩ : MulAut ↥W) ⟨w, hwW⟩ : ↥W) : Γ) = z * w * z⁻¹ :=
      conjAct_apply' W ⟨z, hzW⟩ ⟨w, hwW⟩
    rwa [e] at h3
  have hnormW'' : baum (A1b.conjSub g T) ≤ Subgroup.normalizer (pCoreOf 2 F : Set Γ) :=
    fun z hz => by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      refine ⟨hnormW' z hz w, fun h => ?_⟩
      have h1 := hnormW' z⁻¹ ((baum _).inv_mem hz) _ h
      have e : z⁻¹ * (z * w * z⁻¹) * z⁻¹⁻¹ = w := by group
      rwa [e] at h1
  have hS₂ : IsSylowTwoOf (A1b.conjSub g T) G := isSylowTwoOf_conjSub_of_mem hT' hgG
  set M : Subgroup Γ := G ⊓ Subgroup.normalizer (pCoreOf 2 F : Set Γ) with hM
  have hBS : baum (A1b.conjSub s T) ≤ M := by
    refine le_inf ((inf_le_left : baum (A1b.conjSub s T) ≤ A1b.conjSub s T).trans hS'.1) ?_
    exact (baum_le_normalizer_of_isBTBlock hFs).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 F)
  have hBg : baum (A1b.conjSub g T) ≤ M :=
    le_inf ((inf_le_left : baum (A1b.conjSub g T) ≤ A1b.conjSub g T).trans hS₂.1) hnormW''
  obtain ⟨n, hnM, hbn⟩ := exists_conj_baum_of_le_of_le hS' hS₂ inf_le_left hBS hBg
  have hnN : n ∈ Subgroup.normalizer (pCoreOf 2 F : Set Γ) := (Subgroup.mem_inf.mp hnM).2
  have hy₀ : g * (x : Γ) * g⁻¹ ∈ baum (A1b.conjSub g T) := by
    rw [baum_conjSub]
    exact A1b.mem_conjSub_of_mem hxB
  rw [hbn] at hy₀
  have hbS : n⁻¹ * (g * (x : Γ) * g⁻¹) * n ∈ baum (A1b.conjSub s T) :=
    A1b.mem_conjSub_iff.mp hy₀
  set y₀ : Γ := g * (x : Γ) * g⁻¹ with hy₀def
  set bS : Γ := n⁻¹ * y₀ * n with hbSdef
  have hbSN : bS ∈ Subgroup.normalizer (pCoreOf 2 F : Set Γ) :=
    (baum_le_normalizer_of_isBTBlock hFs).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 F) hbS
  have hsl := (block_structure_sl hG hS hFs hk2 hFk).1
  rw [blockW_eq_pCoreOf hFs] at hsl
  have hmemA : conjAct (pCoreOf 2 F) ⟨bS, hbSN⟩ ∈
      autOn (baum (A1b.conjSub s T)) (pCoreOf 2 F) :=
    mem_autOn_iff.mpr ⟨⟨bS, hbSN⟩, hbS, rfl⟩
  obtain ⟨f', hf'F, hf'⟩ := mem_autOn_iff.mp (hsl hmemA)
  have hbf : ∀ w ∈ pCoreOf 2 F, bS * w * bS⁻¹ = (f' : Γ) * w * (f' : Γ)⁻¹ := by
    intro w hw
    have h1 := congrArg (fun φ : MulAut ↥(pCoreOf 2 F) => ((φ ⟨w, hw⟩ : ↥(pCoreOf 2 F)) : Γ)) hf'
    simp only [conjAct_apply'] at h1
    exact h1.symm
  have hβz : ∀ v : ↥W, βe ((conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v) =
      coreAct (2 * m + 1) (Equiv.swap a b) (βe v) := fun v => by
    have := hψ' ⟨conjAct W ⟨y₀, hyW⟩, hzN⟩ v
    rw [hψy₀] at this
    exact this
  have hδβ : ∀ v : ↥W, βe ((conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v * v⁻¹) =
      if vcoord (βe v) a = vcoord (βe v) b then 1 else pairVec a b := fun v => by
    rw [map_mul, map_inv, hβz]
    exact coreAct_swap_mul_inv hab (βe v)
  obtain ⟨c, hcΩ, hcab⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b}) (t := movFin Ft)
    (Finset.card_le_two.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcab
  have hpvc : pairVec a c ∈ commV (Ft.map (coreAct (2 * m + 1))) :=
    pairVec_mem_commV_of_mem hodd hsame ha hcΩ
  have hpvb : pairVec a b ∈ commV (Ft.map (coreAct (2 * m + 1))) :=
    pairVec_mem_commV_of_mem hodd hsame ha hb
  set w₀ : ↥W := βe.symm (pairVec a c) with hw₀def
  have hβw₀ : βe w₀ = pairVec a c := βe.apply_symm_apply _
  have hw₀W' : (w₀ : Γ) ∈ pCoreOf 2 F := (memP w₀).1 (by rw [hβw₀]; exact hpvc)
  set κ₀ : ↥W := (conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) w₀ * w₀⁻¹ with hκ₀def
  have hac : a ≠ c := fun h => hcab.1 h.symm
  have hba : b ≠ a := fun h => hab h.symm
  have hbc : b ≠ c := fun h => hcab.2 h.symm
  have hva : vcoord (pairVec a c) a ≠ vcoord (pairVec a c) b := by
    rw [vcoord_pairVec, vcoord_pairVec]
    simp [hac, hba, hbc]
  have hκβ : βe κ₀ = pairVec a b := by
    rw [hκ₀def, hδβ, hβw₀]
    simp [hva]
  have hκ₁ : κ₀ ≠ 1 := by
    intro h
    have h1 : βe κ₀ = 1 := by rw [h]; exact map_one _
    rw [hκβ] at h1
    have h2 := congrArg (fun v => vcoord v a) h1
    simp [vcoord_pairVec, vcoord_one, hab] at h2
  have hκW' : (κ₀ : Γ) ∈ pCoreOf 2 F := (memP κ₀).1 (by rw [hκβ]; exact hpvb)
  have hκall : ∀ v : ↥W, (conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v * v⁻¹ = 1 ∨
      (conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v * v⁻¹ = κ₀ := by
    intro v
    by_cases h : vcoord (βe v) a = vcoord (βe v) b
    · left
      apply βe.injective
      rw [hδβ]
      simp [h]
    · right
      apply βe.injective
      rw [hδβ, hκβ]
      simp [h]
  have hcoe : ∀ v : ↥W, (((conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v * v⁻¹ : ↥W) : Γ) =
      ⁅y₀, (v : Γ)⁆ := fun v => by
    show (((conjAct W ⟨y₀, hyW⟩ : MulAut ↥W) v : ↥W) : Γ) * (v : Γ)⁻¹ = _
    rw [conjAct_apply', commutatorElement_def]
  have hy₀comm : ∀ w ∈ W, ⁅y₀, w⁆ = 1 ∨ ⁅y₀, w⁆ = (κ₀ : Γ) := by
    intro w hw
    rcases hκall ⟨w, hw⟩ with h | h
    · left
      rw [← hcoe ⟨w, hw⟩, h]
      rfl
    · right
      rw [← hcoe ⟨w, hw⟩, h]
  have hnatF : IsNatSL F (pCoreOf 2 F) k := by
    have := isNatSL_of_isBTBlock hG hS hFs hFk
    rwa [blockW_eq_pCoreOf hFs] at this
  have hnc : ∀ w : Γ, ⁅bS, w⁆ = n⁻¹ * ⁅y₀, n * w * n⁻¹⁆ * n := fun w => by
    simp only [commutatorElement_def, hbSdef]
    group
  have hfb : ∀ w ∈ pCoreOf 2 F, ⁅(f' : Γ), w⁆ = ⁅bS, w⁆ := fun w hw => by
    simp only [commutatorElement_def]
    rw [hbf w hw]
  have hninv : n⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 F : Set Γ) :=
    (Subgroup.normalizer _).inv_mem hnN
  have hw₁ : n⁻¹ * (w₀ : Γ) * n ∈ pCoreOf 2 F := by
    have := (Subgroup.mem_normalizer_iff.mp hninv (w₀ : Γ)).mp hw₀W'
    simpa using this
  refine false_of_transvection hk2 hnatF (le_normalizer_pCoreOf_self F) hf'F
    (c := n⁻¹ * (κ₀ : Γ) * n) ?_ ?_ ?_ ?_
  · have := (Subgroup.mem_normalizer_iff.mp hninv (κ₀ : Γ)).mp hκW'
    simpa using this
  · intro h
    apply hκ₁
    apply Subtype.ext
    have e : (κ₀ : Γ) = n * (n⁻¹ * (κ₀ : Γ) * n) * n⁻¹ := by group
    rw [e, h]
    simp
  · intro w hw
    have hnw : n * w * n⁻¹ ∈ pCoreOf 2 F := (Subgroup.mem_normalizer_iff.mp hnN w).mp hw
    rw [hfb w hw, hnc]
    rcases hy₀comm _ (hW'W hnw) with h | h
    · left
      rw [h]
      group
    · right
      rw [h]
  · refine ⟨n⁻¹ * (w₀ : Γ) * n, hw₁, ?_⟩
    rw [hfb _ hw₁, hnc]
    have e : n * (n⁻¹ * (w₀ : Γ) * n) * n⁻¹ = (w₀ : Γ) := by group
    rw [e, ← hcoe w₀]

end Finite

end CFSG.CGT.PushingUpLit.BHS6
