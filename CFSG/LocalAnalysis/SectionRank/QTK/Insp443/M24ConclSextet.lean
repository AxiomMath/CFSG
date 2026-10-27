module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.KConf
public import CFSG.Quasithin.Vol2.KGFactC31M24Sx
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213FFt
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatM
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213HatH
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E17Trans
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E14Iso

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24
open scoped IsMulCommutative

private theorem card_quot_sextet
    [((eSub basis_s).subgroupOf Ls).Normal] :
    Nat.card (↥Ls ⧸ (eSub basis_s).subgroupOf Ls) = 1080 := by
  have hRs : Nat.card ↥((eSub basis_s).subgroupOf Ls) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe s_le_Ls).toEquiv, card_eSub]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((eSub basis_s).subgroupOf Ls)
  rw [card_Ls, hRs] at h1
  omega

theorem M24.isHat_Ls
    [((eSub basis_s).subgroupOf Ls).Normal] (hperf : ⁅Ls, Ls⁆ = Ls) :
    CFSG.Quasithin.IsHat (↥Ls ⧸ (eSub basis_s).subgroupOf Ls)
      ↥(alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, hψs, hψk, hRle⟩ := ls_alt_data hperf
  let φ : ↥Ls ⧸ (eSub basis_s).subgroupOf Ls →* ↥(alternatingGroup (Fin 6)) :=
    QuotientGroup.lift _ ψ hRle
  have hφs : Function.Surjective φ := by
    intro σ
    obtain ⟨x, hx⟩ := hψs σ
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  have hφk : Nat.card φ.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      card_alt6, card_quot_sextet] at h1
    omega
  have hcommL : commutator ↥Ls = ⊤ := by
    apply Subgroup.map_injective Ls.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hperf]
  have hperfQ : commutator (↥Ls ⧸ (eSub basis_s).subgroupOf Ls) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective ((eSub basis_s).subgroupOf Ls)), ← Subgroup.map_commutator,
      ← commutator_def, hcommL]
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact isHat_of_surj (H13.alternatingGroup_nonabelian (by norm_num)) hperfQ φ hφs hφk

theorem M24.normal_s_Ls : ((eSub basis_s).subgroupOf Ls).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer s_le_Ls).mpr Ls_le

theorem M24.pCoreOf_Ls (hperf : ⁅Ls, Ls⁆ = Ls) :
    pCoreOf 2 Ls = eSub basis_s := by
  haveI := M24.normal_s_Ls
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  refine pCoreOf_eq_of_surj s_le_Ls (IsPGroup.of_card (n := 6) (card_eSub basis_s))
    (QuotientGroup.mk' ((eSub basis_s).subgroupOf Ls)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) ?_
  exact noNormalTwo_of_isHat (M24.isHat_Ls hperf) (noNormalTwo_of_simple not_isPGroup_alt6)

theorem M24.irr_Ls
    (hperf : ⁅Ls, Ls⁆ = Ls)
    {W : Subgroup G₀} (hWR : W ≤ eSub basis_s)
    (hLW : Ls ≤ Subgroup.normalizer (W : Set G₀)) : W = ⊥ ∨ W = eSub basis_s := by
  haveI := M24.normal_s_Ls
  exact irr_of_hat (isElemAbelian_eSub basis_s) Ls_le (by rw [card_eSub]; norm_num)
    (by rw [cent_s]; exact inf_le_right) (M24.isHat_Ls hperf) hWR hLW

private theorem blockU_sextet
    (hO : pCoreOf 2 Ls = eSub basis_s) (hblock : CFSG.Quasithin.IsHatA6Block Ls) :
    blockU Ls = eSub basis_s := by
  obtain ⟨hshort, -, hcardU, -⟩ := hblock
  have hle : blockU Ls ≤ eSub basis_s := by
    have h := hshort.2.2.1.1
    unfold blockQ at h
    rw [hO] at h
    exact h.trans inf_le_left
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcardU, card_eSub]

private theorem isFFModule_sextet
    [IsMulCommutative ↥(eSub basis_s)]
    (hO : pCoreOf 2 Ls = eSub basis_s) (hblock : CFSG.Quasithin.IsHatA6Block Ls) :
    IsFFModule (autOn Ls (eSub basis_s)) := by
  set V := eSub basis_s with hV
  have hVU : V = blockU Ls := (blockU_sextet hO hblock).symm
  have hblock' := hblock
  obtain ⟨-, hhat, hcard, hcent⟩ := hblock'
  have hLHV : Ls ≤ Subgroup.normalizer (V : Set G₀) := Ls_le
  set ρ := Setup.rho V Ls hLHV with hρ
  have hmemQ : ∀ x : ↥Ls, (x : G₀) ∈ pCoreOf 2 Ls ↔
      (QuotientGroup.mk x : ModO2 Ls) = 1 := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem Ls.subtype_injective
  have hρ1 : ∀ ℓ : ↥Ls, ρ ℓ = 1 ↔ (ℓ : G₀) ∈ pCoreOf 2 Ls := by
    intro ℓ
    rw [Setup.rho_eq_one_iff, ← hcent, ← hVU]
    exact ⟨fun h => ⟨ℓ.2, h⟩, fun h => h.2⟩
  have hle : CFSG.pCore 2 ↥Ls ≤ ρ.ker := by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker, hρ1, hmemQ, QuotientGroup.eq_one_iff]
    exact hℓ
  set π : ModO2 Ls →* MulAut ↥V := QuotientGroup.lift (CFSG.pCore 2 ↥Ls) ρ hle with hπ
  have hπmk : ∀ ℓ : ↥Ls, π (QuotientGroup.mk ℓ) = ρ ℓ := fun ℓ => QuotientGroup.lift_mk _ _ _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hπmk, hρ1, hmemQ] at hq
    exact hq
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(Subgroup.center (ModO2 Ls)), c₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card (Subgroup.center (ModO2 Ls)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card (Subgroup.center (ModO2 Ls)) = 3 := hhat.2.1
    omega
  have hc3 : (c₀ : ModO2 Ls) ^ 3 = 1 := by
    have h1 : c₀ ^ Nat.card (Subgroup.center (ModO2 Ls)) = 1 := pow_card_eq_one'
    rw [hhat.2.1] at h1
    simpa using congrArg Subtype.val h1
  have hσ3 : π c₀ ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hσ1 : π c₀ ≠ 1 := fun h => hc₀ (Subtype.ext (hπinj (h.trans (map_one π).symm)))
  have hσc : ∀ q : ModO2 Ls, π q * π c₀ = π c₀ * π q := fun q => by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp c₀.2 q]
  have hU2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => by
    rw [pow_two]
    exact Subtype.ext (eSub_sq basis_s (v : G₀) v.2)
  have hU64 : Nat.card ↥V = 64 := by
    rw [hVU, hcard]
    norm_num
  have hfree : ∀ u : ↥V, π c₀ u = u → u = 1 := by
    set W : Subgroup G₀ := (FFt.fixU (π c₀)).map V.subtype with hW
    have hWU : W ≤ blockU Ls := hVU ▸ Subgroup.map_subtype_le _
    have hLHW : Ls ≤ Subgroup.normalizer (W : Set G₀) := by
      intro ℓ hℓ
      refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨ρ ⟨ℓ, hℓ⟩ u, ?_, Setup.rho_apply_coe hLHV _ _⟩
      rw [SetLike.mem_coe, FFt.mem_fixU] at hu ⊢
      have h1 := congrArg (fun g : MulAut ↥V => g u) (hσc (QuotientGroup.mk ⟨ℓ, hℓ⟩))
      simp only [MulAut.mul_apply, hπmk] at h1
      rw [← h1, hu]
    rcases T4213N.eq_bot_or_eq_blockU_of_isHatA6Block hblock hWU hLHW with hbot | htop
    · intro u hu
      have hmem : (u : G₀) ∈ W := ⟨u, FFt.mem_fixU.mpr hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · exfalso
      apply hσ1
      ext u
      have hmem : (u : G₀) ∈ W := by rw [htop, ← hVU]; exact u.2
      obtain ⟨u', hu', hu'u⟩ := hmem
      have : u' = u := Subtype.ext hu'u
      rw [← this, MulAut.one_apply, FFt.mem_fixU.mp hu']
  obtain ⟨e⟩ := hhat.2.2
  obtain ⟨r, s, hr4, hr2, hs2, hsr⟩ :=
    FFt.exists_dihedral_lift hhat.2.1 e FFt.r6_pow_four FFt.r6_sq_ne_one FFt.s6_sq FFt.s6_r6
  have hmemA : ∀ q : ModO2 Ls, π q ∈ autOn Ls V := by
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← Setup.range_rho hLHV, hπmk]
    exact ⟨ℓ, rfl⟩
  exact FFt.isFFModule_of_dihedral hU2 hU64 hσ3 hfree (hσc r) (hσc s)
    (by rw [← map_pow, hr4, map_one])
    (fun h => hr2 (hπinj (by rw [map_pow, h, map_one])))
    (by rw [← map_pow, hs2, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hsr, map_inv]) (hmemA r) (hmemA s)

theorem conclK_m24_sextet
    (hperf : ⁅Ls, Ls⁆ = Ls) (MK : Subgroup G₀) :
    ConclK G₀ Ls (eSub basis_s) MK := by
  unfold ConclK
  haveI hRn : ((eSub basis_s).subgroupOf Ls).Normal := M24.normal_s_Ls
  have hhatSR := M24.isHat_Ls hperf
  have hO := M24.pCoreOf_Ls hperf
  have hpk : CFSG.pCore 2 ↥Ls = (eSub basis_s).subgroupOf Ls := by
    rw [← Hex.pCoreOf_subgroupOf' Ls, hO]
  have hhat : CFSG.Quasithin.IsHat (↥Ls ⧸ CFSG.pCore 2 ↥Ls)
      ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpk).symm hhatSR
  have hq : CFSG.IsQuasisimple (↥Ls ⧸ CFSG.pCore 2 ↥Ls) := hhat.1
  have hshape : Shape443 (↥Ls ⧸ CFSG.pCore 2 ↥Ls) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hhat.1.1, hhat.2.1, hhat.2.2⟩)))))
  have hblock : CFSG.Quasithin.IsHatA6Block Ls :=
    isHatA6Block_of (isElemAbelian_eSub basis_s) s_le_Ls Ls_le hO
      (by rw [card_eSub]; norm_num) (by rw [cent_s]; exact inf_le_right) hperf hhatSR
  have hBU : blockU Ls = eSub basis_s := blockU_sextet hO hblock
  have hcardX : Nat.card (↥Ls ⧸ CFSG.pCore 2 ↥Ls) = 1080 :=
    (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hpk).toEquiv).trans card_quot_sextet
  have hcommV : IsMulCommutative ↥(eSub basis_s) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_s x y hx hy
  letI : IsMulCommutative ↥(eSub basis_s) := hcommV
  have hFF : IsFFModule (autOn Ls (eSub basis_s)) := isFFModule_sextet hO hblock
  have hFFN : IsFFModule (V := ↥(eSub basis_s))
      (autOn (Subgroup.normalizer (eSub basis_s : Set G₀)) (eSub basis_s)) :=
    isFFModule_of_le (autOn_mono' Ls_le) hFF
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFFN⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro h3
    have h1 := LieModel.card_psl_three_two h3
    rw [hcardX] at h1
    norm_num at h1
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, -, -⟩ S hS z hz hz2
    have hz' : z ∈ blockU Ls ⊓ Subgroup.centralizer (S : Set G₀) := by
      rw [hBU]
      exact hz
    have hkg := kgHatA6M24He_of (MulEquiv.refl _) CFSG.Sporadic.HeldB.heEquivP HatM.hatCoreAmb_m24
        HatH.hatCoreAmb_he (G := G₀) (K := ⊤) (B := Ls) (S := S)
      (Or.inl ⟨Subgroup.topEquiv⟩) le_top hblock hS z hz' hz2
    intro hle
    apply hkg
    rwa [hBU, top_inf_eq]
  ·
    rintro h3 -
    have h1 := LieModel.card_psu_three_three h3
    rw [hcardX] at h1
    norm_num at h1

end CFSG.SectionRank.QTK.Insp443

end
