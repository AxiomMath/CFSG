module

public import CFSG.CGT.PushingUpLit.BHS7.Pending
public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteenTransport
public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteenAut
public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteenFixed
public import CFSG.CGT.PushingUpLit.BHS7.SevenFourteenComm
public import CFSG.CGT.PushingUpLit.BHS7.VFacts

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

@[expose] def SixEight (G T : Subgroup Γ) : Prop :=
  ∀ E : Subgroup Γ, E ∈ btBlocks G T → (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m) →
    ¬ E ≤ cStarIn G T →
      ∃ F : Subgroup Γ, F ∈ btBlocks G T ∧ F ≤ E ∧ ¬ F ≤ cStarIn G T ∧ IsNaturalAltModule ↥F 1

omit [Finite Γ] in
theorem omegaOneCenterOf_thompsonJ_le_zSub (T : Subgroup Γ) :
    omegaOneCenterOf (thompsonJ T) ≤ zSub T := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxZ, hx2⟩
  refine ⟨?_, hx2⟩
  have hxJ : x ∈ thompsonJ T := hxZ.1
  have hxB : x ∈ baum T := (B6.thompsonJ_le_baum T) hxJ
  refine ⟨hxB, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hxY : x ∈ omegaOneCenterOf (thompsonJ T) := Subgroup.subset_closure ⟨hxZ, hx2⟩
  exact (Subgroup.mem_centralizer_iff.mp hb.2 x hxY).symm

omit [Finite Γ] in
theorem vSub_le_baum (hG : CharTwo G) (hT : IsSylowOf 2 T G) (h : ⁅vSub G T, zSub T⁆ = ⊥) :
    vSub G T ≤ baum T := by
  have hT' : IsSylowTwoOf T G := hT
  have hVT : vSub G T ≤ T := (vSub_le_pCoreOf hG hT').trans hT'.pCoreOf_le
  intro v hv
  refine ⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have hyZ : y ∈ zSub T := omegaOneCenterOf_thompsonJ_le_zSub T hy
  have h1 : ⁅v, y⁆ ∈ (⁅vSub G T, zSub T⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hv hyZ
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

omit [Finite Γ] in
theorem autImage_mono (B : Subgroup Γ) {W V : Subgroup Γ} (hWV : W ≤ V) (α : ↥B ≃* ↥B) :
    autImage B W α ≤ autImage B V α :=
  Subgroup.map_mono (Subgroup.map_mono fun _ hx => hWV hx)

omit [Finite Γ] in
theorem le_normalizer_autImage (B V : Subgroup Γ) (hVB : V ≤ B)
    (hBV : B ≤ Subgroup.normalizer (V : Set Γ)) (α : ↥B ≃* ↥B) :
    B ≤ Subgroup.normalizer ((autImage B V α : Subgroup Γ) : Set Γ) := by
  have hn : (V.subgroupOf B).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVB).2 hBV
  have hn' : ((V.subgroupOf B).map α.toMonoidHom).Normal := hn.map _ α.surjective
  rw [← subgroupOf_autImage] at hn'
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (autImage_le B V α)).1 hn'

omit [Finite Γ] in
theorem autImage_comm (B V : Subgroup Γ) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (α : ↥B ≃* ↥B) : ∀ x ∈ autImage B V α, ∀ y ∈ autImage B V α, x * y = y * x := by
  rintro _ ⟨xB, hxB, rfl⟩ _ ⟨yB, hyB, rfl⟩
  obtain ⟨xv, hxv, rfl⟩ := hxB
  obtain ⟨yv, hyv, rfl⟩ := hyB
  have hc : xv * yv = yv * xv :=
    Subtype.ext (hVab _ (Subgroup.mem_subgroupOf.mp hxv) _ (Subgroup.mem_subgroupOf.mp hyv))
  have := congrArg (fun z : ↥B => ((α z : ↥B) : Γ)) hc
  simpa [map_mul] using this

omit [Finite Γ] in
theorem quadratic_of_autImage (B V W : Subgroup Γ) (hVB : V ≤ B) (hWV : W ≤ V)
    (hBV : B ≤ Subgroup.normalizer (V : Set Γ)) (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (α : ↥B ≃* ↥B) : ⁅⁅V, autImage B W α⁆, autImage B W α⁆ = ⊥ := by
  set A : Subgroup Γ := autImage B W α with hA
  set Vp : Subgroup Γ := autImage B V α with hVp
  have hAVp : A ≤ Vp := autImage_mono B hWV α
  have hVpB : Vp ≤ B := autImage_le B V α
  have hnorm : B ≤ Subgroup.normalizer (Vp : Set Γ) := le_normalizer_autImage B V hVB hBV α
  have hab : ∀ x ∈ Vp, ∀ y ∈ Vp, x * y = y * x := autImage_comm B V hVab α
  have h1 : ⁅V, A⁆ ≤ Vp := by
    rw [Subgroup.commutator_le]
    intro v hv a ha
    have hvB : v ∈ B := hVB hv
    have h2 : v * a * v⁻¹ ∈ Vp := (Subgroup.mem_normalizer_iff.mp (hnorm hvB) a).mp (hAVp ha)
    have h3 : a⁻¹ ∈ Vp := Vp.inv_mem (hAVp ha)
    have : ⁅v, a⁆ = (v * a * v⁻¹) * a⁻¹ := rfl
    rw [this]
    exact Vp.mul_mem h2 h3
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx a ha
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hab x (h1 hx) a (hAVp ha)

omit [Finite Γ] in
theorem not_le_centralizer_autImage (B W : Subgroup Γ) (hWB : W ≤ B) (α : ↥B ≃* ↥B)
    (h : ¬ ((W.subgroupOf B).map α.toMonoidHom ≤
      Subgroup.centralizer ((W.subgroupOf B : Subgroup ↥B) : Set ↥B))) :
    ¬ autImage B W α ≤ Subgroup.centralizer (W : Set Γ) := by
  intro hle
  apply h
  rw [← subgroupOf_centralizer B W hWB, ← subgroupOf_autImage]
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))

theorem block_fixed_data (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hlin : (∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∨ IsNaturalAltModule ↥E 1) :
    ∃ q : ℕ, (baum T ⊓ Subgroup.centralizer (blockW E : Set Γ)).relIndex (baum T) = q ∧
      (blockW E ⊓ Subgroup.centralizer (baum T : Set Γ)).relIndex (blockW E) = q ∧
      ∀ b ∈ baum T, b ∉ Subgroup.centralizer (blockW E : Set Γ) →
        blockW E ⊓ Subgroup.centralizer ({b} : Set Γ) =
          blockW E ⊓ Subgroup.centralizer (baum T : Set Γ) := by
  have hWE : blockW E = pCoreOf 2 E := blockW_eq_pCoreOf hE
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBW : baum T ≤ Subgroup.normalizer (blockW E : Set Γ) := by
    rw [hWE]
    exact hBN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)
  rcases hlin with ⟨n, hn2, hn⟩ | hn
  · obtain ⟨-, hcard, -⟩ := block_structure_sl hG hT hE hn2 hn
    obtain ⟨h1, h2⟩ := block_structure_sl_fixed hG hT hE hn2 hn
    refine ⟨2 ^ n, ?_, h1, h2⟩
    rw [← hcard, card_autOn_eq_relIndex hBW]
  · have hWe : IsElemAbelian 2 (pCoreOf 2 E) :=
      isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
    obtain ⟨D, ψ, -, -, -, -, -, hcard, -⟩ := block_structure_three hG hT hE hn rfl hWe
    obtain ⟨h1, h2⟩ := block_structure_three_fixed hG hT hE hn
    refine ⟨2, ?_, h1, h2⟩
    rw [← card_autOn_eq_relIndex hBW]
    rw [hWE]
    exact hcard

theorem seven14_of_linear (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hVB : vSub G T ≤ baum T)
    (hF : IsBTBlock G T F) (hFC : ¬ F ≤ cStarIn G T)
    (hlin : (∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥F n) ∨ IsNaturalAltModule ↥F 1) :
    ∃ A : Subgroup Γ, A ≤ baum T ∧ ⁅F, A⁆ = F ∧ ⁅⁅vSub G T, A⁆, A⁆ = ⊥ ∧
      (vSub G T ⊓ Subgroup.centralizer (A : Set Γ)).relIndex (vSub G T) =
        (A ⊓ Subgroup.centralizer (vSub G T : Set Γ)).relIndex A ∧
      ∀ a ∈ A, a ∉ Subgroup.centralizer (vSub G T : Set Γ) →
        vSub G T ⊓ Subgroup.centralizer (A : Set Γ) =
          vSub G T ⊓ Subgroup.centralizer ({a} : Set Γ) := by
  classical
  have hT' : IsSylowTwoOf T G := hT
  have hVG : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := le_normalizer_vSub G T
  have hVQ : vSub G T ≤ pCoreOf 2 G := vSub_le_pCoreOf hG hT'
  have hFV : F ≤ Subgroup.normalizer (vSub G T : Set Γ) := hF.le.trans hVG
  have hne : ⁅F, vSub G T⁆ ≠ ⊥ := by
    intro h0
    apply hFC
    have hFc : F ≤ G ⊓ Subgroup.centralizer (vSub G T : Set Γ) := by
      refine le_inf hF.le fun f hf => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ⁅f, v⁆ ∈ (⁅F, vSub G T⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hf hv
      rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    exact hFc.trans (centralizer_vSub_le_cStarIn G T)
  have hW : ⁅F, vSub G T⁆ = blockW F := commutator_eq_blockW hG hT hF hVQ hFV hne
  have hWV : blockW F ≤ vSub G T := hW ▸ commutator_le_of_le_normalizer hFV
  have hWB : blockW F ≤ baum T := hWV.trans hVB
  have hBV : baum T ≤ Subgroup.normalizer (vSub G T : Set Γ) :=
    (inf_le_left : baum T ≤ T).trans (hT.1.trans hVG)
  have hVab : ∀ x ∈ vSub G T, ∀ y ∈ vSub G T, x * y = y * x := fun x hx y hy =>
    isElemAbelian_comm' (isElemAbelian_vSub hG hT') hx hy
  obtain ⟨q, hq1, hq2, hfix⟩ := block_fixed_data hG hT hF hlin
  obtain ⟨α, hα⟩ := exists_aut_not_le_centralizer hG hT hF hFC hWB
  have hα' := not_le_centralizer_autImage (baum T) (blockW F) hWB α hα
  obtain ⟨hc1, hc2, hc3⟩ := transport_ambient (baum T) (blockW F) (vSub G T)
    (blockW F ⊓ Subgroup.centralizer (baum T : Set Γ)) hVB hWV inf_le_left q hq1.le hq2 hfix α hα'
  refine ⟨autImage (baum T) (blockW F) α, autImage_le _ _ _, ?_,
    quadratic_of_autImage (baum T) (vSub G T) (blockW F) hVB hWV hBV hVab α, hc1.trans hc2.symm,
    hc3⟩
  refine commutator_eq_of_not_centralizes hG hT hF (autImage_le _ _ _) ?_
  intro h0
  apply hα'
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 : ⁅w, a⁆ ∈ (⁅blockW F, autImage (baum T) (blockW F) α⁆ : Subgroup Γ) :=
    Subgroup.commutator_mem_commutator hw ha
  rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem seven_fourteen_of_six_eight (h : MinCex G T) (h13 : Seven13 G T) (h68 : SixEight G T) :
    Seven14 G T := by
  intro E hE hEC
  have hVB : vSub G T ≤ baum T := vSub_le_baum h.charTwo h.sylow h13.1
  rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm1, hm⟩
  · exact seven14_of_linear h.charTwo h.sylow hVB hE hEC (Or.inl ⟨n, hn2, hn⟩)
  · by_cases hm : m = 1
    · subst hm
      exact seven14_of_linear h.charTwo h.sylow hVB hE hEC (Or.inr ‹_›)
    · obtain ⟨F, hFb, hFE, hFC, hF3⟩ := h68 E hE ⟨m, hm1, ‹_›⟩ hEC
      obtain ⟨A, hAB, hFA, hq⟩ := seven14_of_linear h.charTwo h.sylow hVB hFb hFC (Or.inr hF3)
      exact ⟨A, hAB, commutator_eq_of_le h.charTwo h.sylow hE hFb hFE hAB hFA, hq⟩

end CFSG.CGT.PushingUpLit.BHS7
