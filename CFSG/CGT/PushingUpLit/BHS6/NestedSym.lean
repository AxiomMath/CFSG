module

public import CFSG.CGT.PushingUpLit.BHS6.NestedFamily
public import CFSG.CGT.PushingUpLit.BHS6.NestedLinear
public import CFSG.CGT.PushingUpLit.BHS6.NestedPerm

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem exists_lift_of_mem_alt {V E : Subgroup Γ} (hV : IsElemAbelian 2 V) {n : ℕ} (h3 : 3 ≤ n) :
    letI : CommGroup ↥V := commGroupOfElemAbelian hV
    ∀ (D : AltNatData (autOn E V) n)
      (ψ : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V))) →* Equiv.Perm (Fin n)),
      (∀ (a : ↥(Subgroup.normalizer (autOn E V : Set (MulAut ↥V)))) (w : ↥V),
        D.β ((a : MulAut ↥V) w) = coreAct n (ψ a) (D.β w)) →
      ∀ {π : Equiv.Perm (Fin n)}, π ∈ alternatingGroup (Fin n) →
        ∃ (g : Γ) (hg : g ∈ Subgroup.normalizer (V : Set Γ)), g ∈ E ∧
          ∃ h : conjAct V ⟨g, hg⟩ ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)),
            ψ ⟨conjAct V ⟨g, hg⟩, h⟩ = π := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  intro D ψ hψ π hπ
  set a : ↥(autOn E V) := D.θ.symm ⟨π, hπ⟩ with ha
  obtain ⟨x, hxE, hxa⟩ := mem_autOn_iff.mp a.2
  have hxN : conjAct V x ∈ Subgroup.normalizer (autOn E V : Set (MulAut ↥V)) :=
    Subgroup.le_normalizer (hxa ▸ a.2)
  refine ⟨(x : Γ), x.2, hxE, hxN, ?_⟩
  have hθ : D.θ a = ⟨π, hπ⟩ := by rw [ha, MulEquiv.apply_symm_apply]
  refine (D.perm_unique h3 fun w => ?_).symm
  have h1 := hψ ⟨conjAct V x, hxN⟩ w
  have h2 := D.equivar a w
  rw [hθ] at h2
  have e : (conjAct V x : MulAut ↥V) w = (a : MulAut ↥V) w := by rw [hxa]
  show coreAct n π (D.β w) = coreAct n (ψ ⟨conjAct V x, hxN⟩) (D.β w)
  rw [← h1]
  show _ = D.β ((conjAct V x : MulAut ↥V) w)
  rw [e]
  exact h2.symm

section Finite

variable [Finite Γ] {G T E F : Subgroup Γ}

theorem exists_conj_baum_le_normalizer_of_symm (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hE : IsBTBlock G T E) {m : ℕ} (hm : 1 ≤ m) (hn : IsNaturalAltModule ↥E m)
    (hF : F ∈ btBlocksG G T) (hFE : F ≤ E) {r : ℕ} (hr : 1 ≤ r) (hFr : IsNaturalAltModule ↥F r) :
    ∃ g ∈ E, baum (A1b.conjSub g T) ≤ Subgroup.normalizer (F : Set Γ) := by
  classical
  have hF' := hF
  obtain ⟨s, hs, hFs⟩ := hF'
  have hT' : IsSylowTwoOf T G := isSylowTwoOf_of_isSylowOf hT
  have hS : IsSylowOf 2 (A1b.conjSub s T) G :=
    isSylowOf_of_isSylowTwoOf (isSylowTwoOf_conjSub_of_mem hT' hs)
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
  have hW'card : Nat.card ↥(pCoreOf 2 F) = Nat.card ↥(coreMod (2 * r + 1)) := by
    have hWe' : IsElemAbelian 2 (pCoreOf 2 F) :=
      isElemAbelian_of_forall' hFs.elemAbelian.1 hFs.elemAbelian.2
    let _ : CommGroup ↥(pCoreOf 2 F) := commGroupOfElemAbelian hWe'
    obtain ⟨D', -, -, hβ'bij, -⟩ := block_structure_symm hG hS hFs hr hFr rfl hWe'
    exact Nat.card_congr (Equiv.ofBijective D'.β hβ'bij)
  have hcV : Nat.card ↥(commV (Ft.map (coreAct (2 * m + 1)))) =
      Nat.card ↥(coreMod (2 * r + 1)) := by
    refine (card_commV_eq_map_congr βe (map_range_modelHom hFE hEW βe ψ hψ')).trans ?_
    have h1 : commV (autOn F W) = (pCoreOf 2 F).subgroupOf W := by
      have := commOn_eq hWe hFW
      rw [commutator_eq_pCoreOf_nested hG hT hE hF hFE] at this
      exact this
    rw [h1, ← hW'card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'W).toEquiv
  have hnatF : IsNatAlt F (pCoreOf 2 F) (2 * r + 1) := by
    have := isNatAlt_of_isBTBlock hG hS hFs hFr
    rwa [blockW_eq_pCoreOf hFs] at this
  have hW'ab : ∀ x ∈ pCoreOf 2 F, ∀ y ∈ pCoreOf 2 F, x * y = y * x := hFs.elemAbelian.1
  have hcapF : F ⊓ Subgroup.centralizer (pCoreOf 2 F : Set Γ) = pCoreOf 2 F :=
    le_antisymm hcharF fun w hw =>
      Subgroup.mem_inf.mpr ⟨CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 F hw,
        Subgroup.mem_centralizer_iff.mpr fun y hy => hW'ab y hy w hw⟩
  have hautF : Nat.card ↥(autOn F W) = Nat.card ↥(alternatingGroup (Fin (2 * r + 1))) := by
    rw [card_autOn_eq_relIndex hFW, inf_centralizer_pCoreOf_nested hG hT hE hF hFE]
    obtain ⟨hF1, -⟩ := relIndex_of_isNatBy hnatF
    rw [hcapF] at hF1
    exact hF1
  have hcF : Nat.card ↥Ft = (2 * r + 1).factorial / 2 := by
    rw [hFt, card_range_modelHom hFE hEW ψ hψinj, hautF]
    have : Nontrivial (Fin (2 * r + 1)) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨hFtAlt, -⟩ := eq_altOn_movFin_of_card hodd hFtres hirr ⟨r, rfl⟩ hcV hcF
  obtain ⟨T', hs', hc', hcard', hB⟩ := hswap
  have hne : T'.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨π, hπ, hπT⟩ := exists_even_conj_le_setStab hodd hne hs' hc' (movFin Ft)
  obtain ⟨g, hgW, hgE, hgN, hgπ⟩ := exists_lift_of_mem_alt hWe hn3 D ψ hψβ hπ
  refine ⟨g, hgE, fun y hy => ?_⟩
  rw [baum_conjSub] at hy
  have hb : g⁻¹ * y * g ∈ baum T := A1b.mem_conjSub_iff.mp hy
  set b := g⁻¹ * y * g with hbdef
  have hyb : y = g * b * g⁻¹ := by rw [hbdef]; group
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) :=
    hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  have hgNE : g ∈ Subgroup.normalizer (E : Set Γ) := Subgroup.le_normalizer hgE
  have hyE : y ∈ Subgroup.normalizer (E : Set Γ) := by
    rw [hyb]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgNE (hBN hb))
      ((Subgroup.normalizer _).inv_mem hgNE)
  have hyW : y ∈ Subgroup.normalizer (W : Set Γ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E hyE
  have hbW : b ∈ Subgroup.normalizer (W : Set Γ) := hBW hb
  have hcb : conjAct W ⟨b, hbW⟩ ∈ autOn (baum T) W := mem_autOn_iff.mpr ⟨⟨b, hbW⟩, hb, rfl⟩
  have hbN : conjAct W ⟨b, hbW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hBW hBN hcb
  have hconj : conjAct W ⟨y, hyW⟩ =
      conjAct W ⟨g, hgW⟩ * conjAct W ⟨b, hbW⟩ * (conjAct W ⟨g, hgW⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hyb
  have hzN : conjAct W ⟨y, hyW⟩ ∈ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) := by
    rw [hconj]
    exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem hgN hbN)
      ((Subgroup.normalizer _).inv_mem hgN)
  have hψz : ψ ⟨conjAct W ⟨y, hyW⟩, hzN⟩ = π * ψ ⟨conjAct W ⟨b, hbW⟩, hbN⟩ * π⁻¹ := by
    have e : (⟨conjAct W ⟨y, hyW⟩, hzN⟩ :
        ↥(Subgroup.normalizer (autOn E W : Set (MulAut ↥W)))) =
        ⟨conjAct W ⟨g, hgW⟩, hgN⟩ * ⟨conjAct W ⟨b, hbW⟩, hbN⟩ * ⟨conjAct W ⟨g, hgW⟩, hgN⟩⁻¹ :=
      Subtype.ext hconj
    rw [e, map_mul, map_mul, map_inv, hgπ]
  have hψb : ψ ⟨conjAct W ⟨b, hbW⟩, hbN⟩ ∈ Subgroup.closure T' := by
    rw [← hB]
    exact ⟨⟨conjAct W ⟨b, hbW⟩, hbN⟩, Subgroup.mem_subgroupOf.mpr hcb, rfl⟩
  have hstab : ψ ⟨conjAct W ⟨y, hyW⟩, hzN⟩ ∈ setStab (movFin Ft) := by
    rw [hψz]
    exact hπT _ hψb
  have hnormFt : ψ ⟨conjAct W ⟨y, hyW⟩, hzN⟩ ∈ Subgroup.normalizer (Ft : Set _) := by
    have h1 := mem_normalizer_altOn_of_mem_setStab hstab
    rwa [← hFtAlt] at h1
  have hnormF : conjAct W ⟨y, hyW⟩ ∈ Subgroup.normalizer (autOn F W : Set (MulAut ↥W)) :=
    mem_normalizer_autOn_of_map hFE hEW ψ hψinj hzN hnormFt
  exact mem_normalizer_of_conjAct hG hT hE hF hFE hyE hyW hnormF

end Finite

end CFSG.CGT.PushingUpLit.BHS6
