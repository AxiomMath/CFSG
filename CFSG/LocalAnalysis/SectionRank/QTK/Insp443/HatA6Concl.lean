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
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443 CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.M24
open scoped IsMulCommutative

private theorem blockU_of_isHatA6 {K : Type} [Group K] [Finite K] {L V : Subgroup K}
    (hVc : Nat.card V = 64) (hO : pCoreOf 2 L = V)
    (hblock : CFSG.Quasithin.IsHatA6Block L) : blockU L = V := by
  obtain ⟨hshort, -, hcardU, -⟩ := hblock
  have hle : blockU L ≤ V := by
    have h := hshort.2.2.1.1
    unfold blockQ at h
    rw [hO] at h
    exact h.trans inf_le_left
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcardU, hVc]
  norm_num

private theorem isFFModule_of_isHatA6 {K : Type} [Group K] [Finite K] {L V : Subgroup K}
    [IsMulCommutative ↥V] (hEA : IsElemAbelian 2 V)
    (hLV : L ≤ Subgroup.normalizer (V : Set K)) (hVc : Nat.card V = 64)
    (hO : pCoreOf 2 L = V) (hblock : CFSG.Quasithin.IsHatA6Block L) :
    IsFFModule (autOn L V) := by
  have hVU : V = blockU L := (blockU_of_isHatA6 hVc hO hblock).symm
  have hblock' := hblock
  obtain ⟨-, hhat, hcard, hcent⟩ := hblock'
  set ρ := Setup.rho V L hLV with hρ
  have hmemQ : ∀ x : ↥L, (x : K) ∈ pCoreOf 2 L ↔
      (QuotientGroup.mk x : ModO2 L) = 1 := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem L.subtype_injective
  have hρ1 : ∀ ℓ : ↥L, ρ ℓ = 1 ↔ (ℓ : K) ∈ pCoreOf 2 L := by
    intro ℓ
    rw [Setup.rho_eq_one_iff, ← hcent, ← hVU]
    exact ⟨fun h => ⟨ℓ.2, h⟩, fun h => h.2⟩
  have hle : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro ℓ hℓ
    rw [MonoidHom.mem_ker, hρ1, hmemQ, QuotientGroup.eq_one_iff]
    exact hℓ
  set π : ModO2 L →* MulAut ↥V := QuotientGroup.lift (CFSG.pCore 2 ↥L) ρ hle with hπ
  have hπmk : ∀ ℓ : ↥L, π (QuotientGroup.mk ℓ) = ρ ℓ := fun ℓ => QuotientGroup.lift_mk _ _ _
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hπmk, hρ1, hmemQ] at hq
    exact hq
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥(Subgroup.center (ModO2 L)), c₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card (Subgroup.center (ModO2 L)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card (Subgroup.center (ModO2 L)) = 3 := hhat.2.1
    omega
  have hc3 : (c₀ : ModO2 L) ^ 3 = 1 := by
    have h1 : c₀ ^ Nat.card (Subgroup.center (ModO2 L)) = 1 := pow_card_eq_one'
    rw [hhat.2.1] at h1
    simpa using congrArg Subtype.val h1
  have hσ3 : π c₀ ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hσ1 : π c₀ ≠ 1 := fun h => hc₀ (Subtype.ext (hπinj (h.trans (map_one π).symm)))
  have hσc : ∀ q : ModO2 L, π q * π c₀ = π c₀ * π q := fun q => by
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp c₀.2 q]
  have hU2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hEA.2 v v.2)
  have hU64 : Nat.card ↥V = 64 := hVc
  have hfree : ∀ u : ↥V, π c₀ u = u → u = 1 := by
    set W : Subgroup K := (FFt.fixU (π c₀)).map V.subtype with hW
    have hWU : W ≤ blockU L := hVU ▸ Subgroup.map_subtype_le _
    have hLHW : L ≤ Subgroup.normalizer (W : Set K) := by
      intro ℓ hℓ
      refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
      obtain ⟨u, hu, rfl⟩ := hw
      refine ⟨ρ ⟨ℓ, hℓ⟩ u, ?_, Setup.rho_apply_coe hLV _ _⟩
      rw [SetLike.mem_coe, FFt.mem_fixU] at hu ⊢
      have h1 := congrArg (fun g : MulAut ↥V => g u) (hσc (QuotientGroup.mk ⟨ℓ, hℓ⟩))
      simp only [MulAut.mul_apply, hπmk] at h1
      rw [← h1, hu]
    rcases T4213N.eq_bot_or_eq_blockU_of_isHatA6Block hblock hWU hLHW with hbot | htop
    · intro u hu
      have hmem : (u : K) ∈ W := ⟨u, FFt.mem_fixU.mpr hu, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · exfalso
      apply hσ1
      ext u
      have hmem : (u : K) ∈ W := by rw [htop, ← hVU]; exact u.2
      obtain ⟨u', hu', hu'u⟩ := hmem
      have : u' = u := Subtype.ext hu'u
      rw [← this, MulAut.one_apply, FFt.mem_fixU.mp hu']
  obtain ⟨e⟩ := hhat.2.2
  obtain ⟨r, s, hr4, hr2, hs2, hsr⟩ :=
    FFt.exists_dihedral_lift hhat.2.1 e FFt.r6_pow_four FFt.r6_sq_ne_one FFt.s6_sq FFt.s6_r6
  have hmemA : ∀ q : ModO2 L, π q ∈ autOn L V := by
    intro q
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← Setup.range_rho hLV, hπmk]
    exact ⟨ℓ, rfl⟩
  exact FFt.isFFModule_of_dihedral hU2 hU64 hσ3 hfree (hσc r) (hσc s)
    (by rw [← map_pow, hr4, map_one])
    (fun h => hr2 (hπinj (by rw [map_pow, h, map_one])))
    (by rw [← map_pow, hs2, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hsr, map_inv]) (hmemA r) (hmemA s)

theorem conclK_of_isHatA6
    {K : Type} [Group K] [Finite K]
    (hK : IsSporadic .M24 K ∨ IsSporadic .He K) {L V : Subgroup K}
    (hEA : IsElemAbelian 2 V) (hVL : V ≤ L) (hLV : L ≤ Subgroup.normalizer (V : Set K))
    (hVc : Nat.card V = 64) (hC : L ⊓ Subgroup.centralizer (V : Set K) ≤ V)
    (hperf : ⁅L, L⁆ = L) [(V.subgroupOf L).Normal]
    (hhat : CFSG.Quasithin.IsHat (↥L ⧸ V.subgroupOf L) ↥(alternatingGroup (Fin 6)))
    (MK : Subgroup K) : ConclK K L V MK := by
  unfold ConclK
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hO : pCoreOf 2 L = V :=
    pCoreOf_eq_of_surj hVL (IsPGroup.of_card (n := 6) (by rw [hVc]; norm_num))
      (QuotientGroup.mk' (V.subgroupOf L)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)
      (noNormalTwo_of_isHat hhat (noNormalTwo_of_simple M24.not_isPGroup_alt6))
  have hpk : CFSG.pCore 2 ↥L = V.subgroupOf L := by
    rw [← Hex.pCoreOf_subgroupOf' L, hO]
  have hhat' : CFSG.Quasithin.IsHat (↥L ⧸ CFSG.pCore 2 ↥L)
      ↥(alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hpk).symm hhat
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hhat'.1
  have hshape : Shape443 (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hhat'.1.1, hhat'.2.1, hhat'.2.2⟩)))))
  have hblock : CFSG.Quasithin.IsHatA6Block L :=
    isHatA6Block_of hEA hVL hLV hO hVc hC hperf hhat
  have hBU : blockU L = V := blockU_of_isHatA6 hVc hO hblock
  have hcardX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [hhat'.2.1, Nat.card_congr hhat'.2.2.some.toEquiv, M24.card_alt6] at h1
    omega
  letI : IsMulCommutative ↥V := hEA.1
  have hFF : IsFFModule (autOn L V) := isFFModule_of_isHatA6 hEA hLV hVc hO hblock
  have hFFN : IsFFModule (V := ↥V)
      (autOn (Subgroup.normalizer (V : Set K)) V) :=
    isFFModule_of_le (autOn_mono' hLV) hFF
  have hKtop : IsSporadic .M24 ↥(⊤ : Subgroup K) ∨ IsSporadic .He ↥(⊤ : Subgroup K) := by
    rcases hK with h | h
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨Subgroup.topEquiv.trans e⟩
    · obtain ⟨e⟩ := h
      exact Or.inr ⟨Subgroup.topEquiv.trans e⟩
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hEA.1, hFFN⟩, ?_, ?_, ?_, ?_⟩⟩
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
    have hz' : z ∈ blockU L ⊓ Subgroup.centralizer (S : Set K) := by
      rw [hBU]
      exact hz
    have hkg := kgHatA6M24He_of (MulEquiv.refl _) CFSG.Sporadic.HeldB.heEquivP HatM.hatCoreAmb_m24
        HatH.hatCoreAmb_he (G := K) (K := ⊤) (B := L) (S := S)
      hKtop le_top hblock hS z hz' hz2
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
