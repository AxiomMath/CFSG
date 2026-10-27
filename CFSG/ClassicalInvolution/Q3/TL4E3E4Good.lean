module

public import CFSG.ClassicalInvolution.Q3.TL4E3SecEq
public import CFSG.ClassicalInvolution.Q3.TL4E3E4GoodM
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4GoodAll

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

section Cit3


variable {n : ℕ}

theorem tightE3E4Good_of (hNG : TightE4NoGood) : TightE3E4Good n := by
  intro hP Y _ _ R S t hL hO hcn hsp J hJ u hu htu ht hE4 hE2 htX
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set π := orbOf (TC.nbrAdj Ω) J (tightCore R) with hπdef
  set C := Subgroup.centralizer ({u} : Set Y) with hCdef
  have hd := hL.datum
  have hΩ := hd.hypOmegaGen
  have h2 : ∀ J' ∈ Ω, IsPGroup 2 J' := hd.isPGroup_member hO
  have htr : ∀ J' ∈ Ω, ∃ g : Y, conjSub g (tightCore R) = J' := fun J' hJ' => hJ'
  have hgen : (⨆ J' ∈ Ω, J') = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  have hF := TC.graphFam hΩ h2 hsp htr hgen hcn
  have hstd : OrbitStd Ω := ⟨hΩ, h2, hF⟩
  have hJΩ : J ∈ Ω := hJ.1.2.1
  have hmax : π ∈ maxOrbs (TC.nbrAdj Ω) J := orbOf_mem_maxOrbs hF hJ.1 hJ.2
  have hK₀π : tightCore R ∈ π := ⟨1, Subgroup.one_mem _, by ext x; simp [conjSub]⟩
  have hR2 : IsPGroup 2 R := hd.isPGroup_of_oddCent hO
  have hK₀R : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have hRX : R ≤ piGen π := hK₀R ▸ le_piGen hK₀π
  have hXC : piGen π ≤ C := hstd.piGen_le_centralizer hmax hu
  have hJN : C ≤ Subgroup.normalizer ((J : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hL).tight J hJΩ u hu
  have hXn : ∀ c ∈ C, conjSub c (piGen π) = piGen π := by
    intro c hc
    have hcJ : conjSub c J = J := conjSub_eq_of_mem_normalizer (hJN hc)
    have h1 := isMaxOrb_conj hF hmax c
    rw [hcJ] at h1
    have h2' := maxOrb_unique hF hJΩ h1 hmax
    rw [← piGen_conj, h2']
  have hX'n : ((piGen π).subgroupOf C).Normal := by
    refine ⟨fun x hx c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hm : (c : Y) * x * (c : Y)⁻¹ ∈ conjSub (c : Y) (piGen π) := by
      rw [mem_conjSub_iff]
      have he : (c : Y)⁻¹ * ((c : Y) * x * (c : Y)⁻¹) * (c : Y) = x := by group
      rw [he]
      exact hx
    rw [hXn c c.2] at hm
    simpa using hm
  obtain ⟨g₀, hg₀'⟩ := hJΩ
  have hg₀ : conjSub g₀ (tightCore R) = J := hg₀'
  have hu₀ : g₀ * t * g₀⁻¹ = u := by
    have h1 := hd.isUniqueInvolution_core.conj g₀
    rw [hg₀] at h1
    exact h1.eq hu
  have hOu : classicalInvolutionOddCore ↥C = ⊥ := by
    have h1 := card_oddCent_conj (t := t) g₀
    have h3 : Nat.card (oddCoreImg (Subgroup.centralizer ({t} : Set Y))) = 1 := by
      unfold TightOddCent at hO
      rw [hO, Subgroup.card_bot]
    rw [h3, hu₀] at h1
    have h4 : oddCoreImg C = ⊥ := Subgroup.card_eq_one.mp h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h4
  have hOX : classicalInvolutionOddCore ↥(piGen π) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hX'n hXC hOu
  have hOH : classicalInvolutionOddCore ↥(secH R u) = ⊥ := by
    have h1 := Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_subnormalClosure
      (tightCore (R.subgroupOf C)))
    have h2' : Balance.oddCoreIn (⊤ : Subgroup ↥C) = ⊥ := by
      have h3 := E3.map_oddCore_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup ↥C) ≃* ↥C)
      rw [hOu] at h3
      have h4 : classicalInvolutionOddCore ↥(⊤ : Subgroup ↥C) = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ Subgroup.topEquiv.injective).mp h3
      show (classicalInvolutionOddCore ↥(⊤ : Subgroup ↥C)).map _ = ⊥
      rw [h4, Subgroup.map_bot]
    rw [h2', le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have hsec : secH R u = (piGen π).subgroupOf C :=
    E3.secH_eq_orbGen_of_oddCent hL hO hcn hsp hJ hu
  let e : ↥(piGen π) ≃* SecQ R u :=
    (((Subgroup.subgroupOfEquivOfLe hXC).symm.trans (MulEquiv.subgroupCongr hsec.symm)).trans
      QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hOH.symm)
  have hE4X : TightE4 ↥(piGen π) :=
    TightE4.of_surjective e.toMonoidHom e.surjective
      (by
        rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
        exact IsPGroup.of_bot) hE4
  have hSX : (S : Subgroup R).map R.subtype ≤ piGen π := (Subgroup.map_subtype_le _).trans hRX
  obtain ⟨SX, hdX, ⟨eX⟩⟩ := hd.restrict hSX
  have hRX2 : IsPGroup 2 ↥(R.subgroupOf (piGen π)) :=
    hR2.comap_of_injective (piGen π).subtype (piGen π).subtype_injective
  have hself : TightSelfGen (R.subgroupOf (piGen π)) := by
    unfold TightSelfGen
    rw [tightCore_eq_self_of_isPGroup hRX2]
    apply Subgroup.map_injective (piGen π).subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    apply le_antisymm
    · exact iSup_le fun g => Subgroup.map_subtype_le _
    · refine piGen_le fun M hM => ?_
      obtain ⟨a, ha, hMa⟩ := transitive_of_maxOrb hF hmax (tightCore R) hK₀π M hM
      refine le_iSup_of_le ⟨a, ha⟩ ?_
      rw [E3.map_conjSub, Subgroup.map_subgroupOf_eq_of_le hRX, ← hMa, hK₀R]
      rfl
  have hcX : TightCls ↥(piGen π) (R.subgroupOf (piGen π)) SX (⟨t, hSX hd.mem⟩ : ↥(piGen π)) :=
    ⟨⟨eX.trans hL.cls.1.some⟩, hself, hOX⟩
  have hK' : tightCore (R.subgroupOf C) ≤ (piGen π).subgroupOf C := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, -⟩
    exact hRX hxR
  have hHX : secH R u ≤ (piGen π).subgroupOf C :=
    subnormalClosure_le hK' (IsSubnormal.step le_top Subgroup.normal_subgroupOf
      (IsSubnormal.refl ⊤))
  have hE2X : ¬ TightInO2 (⟨t, hSX hd.mem⟩ : ↥(piGen π)) := fun h =>
    hE2 (E3.tightInO2_secT_of_le htu ht hXC hHX _ h)
  exact hNG _ _ _ _ hdX hcX hE2X hE4X

end Cit3


theorem tightE3E4Good_proved {n : ℕ} : TightE3E4Good n :=
  tightE3E4Good_of (tightE4NoGood_of fun _ _ _ hM => e4QuatNoGood_of_exLie hM)

end CFSG.ClassicalInvolution.Q3.TL4
