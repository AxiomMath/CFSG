module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24ConclU5
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Facts
public import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.H13.Ch4.E443
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24 CFSG.SectionRank.QTK.Insp443.M24
open scoped IsMulCommutative Matrix

namespace M24

theorem conj_nE_comm
    {l u : G₀} (hl : l ∈ Lq) (hu : u ∈ eSub basis_u5) :
    l * (nE * u * nE⁻¹) * l⁻¹ = nE * (l * u * l⁻¹) * nE⁻¹ := by
  obtain ⟨-, heps⟩ := Lq_le_sectionCent hl
  have hmem : l * u * l⁻¹ ∈ eSub basis_u5 :=
    (Subgroup.mem_normalizer_iff.mp (Lq_le hl) u).mp hu
  have hX : nE * (l * u * l⁻¹) * nE⁻¹ ∈ eSub basis_et :=
    (Subgroup.mem_normalizer_iff.mp nE_mem (l * u * l⁻¹)).mp (u5_le_et hmem)
  have hcomm : (l * nE * l⁻¹ * nE⁻¹) * (nE * (l * u * l⁻¹) * nE⁻¹) * (l * nE * l⁻¹ * nE⁻¹)⁻¹ =
      nE * (l * u * l⁻¹) * nE⁻¹ := by
    rw [eSub_comm basis_et _ _ heps hX]
    group
  calc l * (nE * u * nE⁻¹) * l⁻¹
      = (l * nE * l⁻¹ * nE⁻¹) * (nE * (l * u * l⁻¹) * nE⁻¹) * (l * nE * l⁻¹ * nE⁻¹)⁻¹ := by
        group
    _ = nE * (l * u * l⁻¹) * nE⁻¹ := hcomm

end M24

private def W : Fin 2 → Subgroup G₀ :=
  ![eSub basis_u5, (eSub basis_u5).map (MulAut.conj nE).toMonoidHom]

private theorem W_one :
    W 1 = (eSub basis_u5).map (MulAut.conj nE).toMonoidHom := by simp [W]

private theorem W_one_le_et :
    W 1 ≤ eSub basis_et := by
  rw [W_one, ← u5_sup_conj_nE]
  exact le_sup_right

private theorem conj_mem_W1
    {l x : G₀} (hl : l ∈ Lq) (hx : x ∈ W 1) : l * x * l⁻¹ ∈ W 1 := by
  rw [W_one] at hx ⊢
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨l * u * l⁻¹, (Subgroup.mem_normalizer_iff.mp (Lq_le hl) u).mp hu,
    by simpa [MulAut.conj_apply] using (M24.conj_nE_comm hl hu).symm⟩

private theorem Lq_le_normalizer_W1 :
    Lq ≤ Subgroup.normalizer (W 1 : Set G₀) :=
  fun l hl => A4.mem_normalizer_of_conj_mem fun x hx => conj_mem_W1 hl hx

private theorem iSupIndep_W :
    iSupIndep W := by
  refine (iSupIndep_pair (i := (0 : Fin 2)) (j := 1) (by decide)
    (fun k => by fin_cases k <;> simp)).mpr ?_
  exact disjoint_iff.mpr u5_inf_conj_nE

private noncomputable def conjNHom :
    ↥(eSub basis_u5) →* ↥(W 1) where
  toFun u := ⟨nE * u * nE⁻¹, by
    rw [W_one]
    exact Subgroup.mem_map.mpr ⟨u, u.2, by simp [MulAut.conj_apply]⟩⟩
  map_one' := Subtype.ext (by show nE * (1 : G₀) * nE⁻¹ = 1; group)
  map_mul' u v := Subtype.ext (by
    show nE * (↑u * ↑v) * nE⁻¹ = nE * ↑u * nE⁻¹ * (nE * ↑v * nE⁻¹)
    group)

private theorem coe_conjNHom (u : ↥(eSub basis_u5)) :
    ((conjNHom u : ↥(W 1)) : G₀) = nE * u * nE⁻¹ := rfl

private theorem conjNHom_injective :
    Function.Injective conjNHom := by
  intro u v huv
  have h : ((conjNHom u : ↥(W 1)) : G₀) = ((conjNHom v : ↥(W 1)) : G₀) :=
    congrArg Subtype.val huv
  rw [coe_conjNHom, coe_conjNHom] at h
  exact Subtype.ext (mul_left_cancel (mul_right_cancel h))

private theorem conjNHom_surjective :
    Function.Surjective conjNHom := by
  intro x
  have hx : (x : G₀) ∈ (eSub basis_u5).map (MulAut.conj nE).toMonoidHom := W_one ▸ x.2
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
  exact ⟨⟨u, hu⟩, Subtype.ext (by rw [coe_conjNHom]; simpa [MulAut.conj_apply] using hux)⟩

private noncomputable def conjN :
    ↥(eSub basis_u5) ≃* ↥(W 1) :=
  MulEquiv.ofBijective conjNHom ⟨conjNHom_injective, conjNHom_surjective⟩

private theorem coe_conjN (u : ↥(eSub basis_u5)) :
    ((conjN u : ↥(W 1)) : G₀) = nE * u * nE⁻¹ := coe_conjNHom u

private theorem isLEquiv_conjN :
    IsLEquiv Lq conjN := by
  intro l hl a a' ha'
  rw [coe_conjN, coe_conjN, ha']
  exact (M24.conj_nE_comm hl a.2).symm

private theorem binaryNaturalSL_W1
    [IsMulCommutative ↥(W 1)] :
    BinaryNaturalSL (V := ↥(W 1)) (autOn Lq (W 1)) ⊤ ⊥ 3 1 := by
  haveI : IsMulCommutative ↥(eSub basis_u5) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_u5 x y hx hy
  exact binaryNaturalSL_of_isLEquiv Lq_le Lq_le_normalizer_W1 isLEquiv_conjN binaryNaturalSL_u5

private noncomputable def coordEquiv :
    ↥(eSub basis_et) ≃* Multiplicative (Fin 6 → ZMod 2) :=
  (MulEquiv.subgroupCongr eSub_u5n_basis.symm).trans (ecoords u5n_basis)

private noncomputable def coords
    (x : ↥(eSub basis_et)) : Fin 6 → ZMod 2 :=
  Multiplicative.toAdd (coordEquiv x)

private theorem eElt_coords
    (x : ↥(eSub basis_et)) : eElt u5nV (coords x) = (x : G₀) := by
  rw [coords, coordEquiv, MulEquiv.trans_apply, eElt_ecoords, MulEquiv.subgroupCongr_apply]

private def flatFun (d : Fin 2 → Fin 3 → ZMod 2) : Fin 6 → ZMod 2 :=
  Fin.append (m := 3) (n := 3) (d 0) (d 1)

private def unflatFun (c : Fin 6 → ZMod 2) : Fin 2 → Fin 3 → ZMod 2 :=
  ![fun j => c (Fin.castAdd 3 j), fun j => c (Fin.natAdd 3 j)]

private theorem unflatFun_zero (c : Fin 6 → ZMod 2) :
    unflatFun c 0 = fun j => c (Fin.castAdd 3 j) := rfl

private theorem unflatFun_one (c : Fin 6 → ZMod 2) :
    unflatFun c 1 = fun j => c (Fin.natAdd 3 j) := rfl

private theorem flat_unflat (c : Fin 6 → ZMod 2) : flatFun (unflatFun c) = c := by
  funext i
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
  · show Fin.append (unflatFun c 0) (unflatFun c 1) (Fin.castAdd 3 j) = c (Fin.castAdd 3 j)
    rw [Fin.append_left, unflatFun_zero]
  · show Fin.append (unflatFun c 0) (unflatFun c 1) (Fin.natAdd 3 j) = c (Fin.natAdd 3 j)
    rw [Fin.append_right, unflatFun_one]

private theorem unflat_flat (d : Fin 2 → Fin 3 → ZMod 2) : unflatFun (flatFun d) = d := by
  funext i
  fin_cases i
  · funext j
    show Fin.append (d 0) (d 1) (Fin.castAdd 3 j) = d 0 j
    rw [Fin.append_left]
  · funext j
    show Fin.append (d 0) (d 1) (Fin.natAdd 3 j) = d 1 j
    rw [Fin.append_right]

private theorem coords_append (c : Fin 6 → ZMod 2) :
    Fin.append (m := 3) (n := 3) (fun j : Fin 3 => c (Fin.castAdd 3 j))
      (fun j : Fin 3 => c (Fin.natAdd 3 j)) = c :=
  flat_unflat c

private def flatEquiv : (Fin 2 → Fin 3 → ZMod 2) ≃+ (Fin 6 → ZMod 2) where
  toFun := flatFun
  invFun := unflatFun
  left_inv := unflat_flat
  right_inv := flat_unflat
  map_add' d d' := by
    funext i
    refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) i
    · show Fin.append ((d + d') 0) ((d + d') 1) (Fin.castAdd 3 j) =
        Fin.append (d 0) (d 1) (Fin.castAdd 3 j) + Fin.append (d' 0) (d' 1) (Fin.castAdd 3 j)
      rw [Fin.append_left, Fin.append_left, Fin.append_left]
      rfl
    · show Fin.append ((d + d') 0) ((d + d') 1) (Fin.natAdd 3 j) =
        Fin.append (d 0) (d 1) (Fin.natAdd 3 j) + Fin.append (d' 0) (d' 1) (Fin.natAdd 3 j)
      rw [Fin.append_right, Fin.append_right, Fin.append_right]
      rfl

private noncomputable def reshapeMul :
    Multiplicative (Fin 2 → Fin 3 → ZMod 2) ≃* Multiplicative (Fin 6 → ZMod 2) :=
  AddEquiv.toMultiplicative flatEquiv

private noncomputable def betaEquiv :
    ↥(eSub basis_et) ≃* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  coordEquiv.trans reshapeMul.symm

private noncomputable def beta :
    ↥(eSub basis_et) →* Multiplicative (Fin 2 → Fin 3 → ZMod 2) :=
  betaEquiv.toMonoidHom

private theorem beta_apply
    (x : ↥(eSub basis_et)) :
    Multiplicative.toAdd (beta x) = unflatFun (coords x) := rfl

private theorem conj_eElt_conj
    (a : ↥Lq) (c : Fin 3 → ZMod 2) :
    (a : G₀) * eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) c * (a : G₀)⁻¹ =
      eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) (eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ c) := by
  rw [← conj_eElt nE c]
  rw [M24.conj_nE_comm a.2 (eElt_mem basis_u5 c)]
  rw [conj_eq_eElt_mulVec basis_u5 ⟨a, Lq_le a.2⟩ c, conj_eElt]

private theorem conj_coords
    (a : ↥Lq) (x : ↥(eSub basis_et)) :
    (a : G₀) * eElt u5nV (coords x) * (a : G₀)⁻¹ =
      eElt u5nV (Fin.append (eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ fun j => coords x (Fin.castAdd 3 j))
        (eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ fun j => coords x (Fin.natAdd 3 j))) := by
  set c₀ : Fin 3 → ZMod 2 := fun j => coords x (Fin.castAdd 3 j) with hc₀
  set c₁ : Fin 3 → ZMod 2 := fun j => coords x (Fin.natAdd 3 j) with hc₁
  have hc : coords x = Fin.append c₀ c₁ := (coords_append (coords x)).symm
  rw [hc, eElt_u5nV]
  rw [show (a : G₀) * (eElt vU5 c₀ * eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) c₁) * (a : G₀)⁻¹ =
      ((a : G₀) * eElt vU5 c₀ * (a : G₀)⁻¹) *
        ((a : G₀) * eElt (fun i : Fin 3 => nE * vU5 i * nE⁻¹) c₁ * (a : G₀)⁻¹) from by group]
  rw [conj_eq_eElt_mulVec basis_u5 ⟨a, Lq_le a.2⟩ c₀, conj_eElt_conj a c₁, ← eElt_u5nV]

private theorem isSumOfNaturalModules_et :
    IsSumOfNaturalModules Lq (eSub basis_et) ⊥ ((eSub basis_et).subgroupOf Lq)
      (StatedSL 3 (ZMod 2)) false 2 := by
  refine ⟨E8.e3Hom basis_u5 Lq_le, surjective_e3Hom_u5, ker_e3Hom_u5, Lq_le_eNorm_et, bot_le,
    beta, betaEquiv.surjective, ?_, ?_⟩
  · rw [Subgroup.bot_subgroupOf, MonoidHom.ker_eq_bot_iff]
    exact betaEquiv.injective
  · intro a u v huv i
    show Multiplicative.toAdd (beta v) i =
      (((E8.e3Hom basis_u5 Lq_le a : ↥(StatedSL 3 (ZMod 2))) :
        Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (beta u) i
    rw [E8.e3Hom_coe basis_u5 Lq_le a, beta_apply, beta_apply]
    have hcv : coords v = Fin.append (m := 3) (n := 3)
        (eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ fun j => coords u (Fin.castAdd 3 j))
        (eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ fun j => coords u (Fin.natAdd 3 j)) := by
      apply eElt_injective u5n_basis
      rw [eElt_coords v, huv, ← eElt_coords u]
      exact conj_coords a u
    fin_cases i
    · show (fun j => coords v (Fin.castAdd 3 j)) =
        eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ (fun j => coords u (Fin.castAdd 3 j))
      rw [hcv]
      funext j
      rw [Fin.append_left]
    · show (fun j => coords v (Fin.natAdd 3 j)) =
        eMat basis_u5 ⟨a, Lq_le a.2⟩ *ᵥ (fun j => coords u (Fin.natAdd 3 j))
      rw [hcv]
      funext j
      rw [Fin.append_right]

private theorem isNaturalSumUnder_et :
    IsNaturalSumUnder 3 Lq (eSub basis_et) := by
  haveI hcomm0 : IsMulCommutative ↥(eSub basis_u5) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_u5 x y hx hy
  haveI hcomm1 : IsMulCommutative ↥(W 1) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => by
      rw [W_one] at hx hy
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      have hcomm : nE * u * nE⁻¹ * (nE * v * nE⁻¹) = nE * v * nE⁻¹ * (nE * u * nE⁻¹) := by
        have h1 : nE * u * nE⁻¹ * (nE * v * nE⁻¹) = nE * (u * v) * nE⁻¹ := by group
        have h2 : nE * v * nE⁻¹ * (nE * u * nE⁻¹) = nE * (v * u) * nE⁻¹ := by group
        rw [h1, h2, eSub_comm basis_u5 u v hu hv]
      simpa [MulAut.conj_apply] using hcomm
  refine ⟨2, W, by norm_num, ?_, ?_, iSupIndep_W, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨u5_le_et, Lq_le, ⟨hcomm0, binaryNaturalSL_u5⟩⟩
    · exact ⟨W_one_le_et, Lq_le_normalizer_W1, ⟨hcomm1, binaryNaturalSL_W1⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
    · exact isXSectionIso₂_of_isLEquiv isLEquiv_conjN
    · exact isXSectionIso₂_of_isLEquiv (isLEquiv_conjN.symm Lq_le)
    · exact isXSectionIso₂_of_isLEquiv (φ := MulEquiv.refl _) (fun l hl a a' ha' => ha')
  · refine le_antisymm (iSup_le fun i => ?_) ?_
    · fin_cases i
      · exact u5_le_et
      · exact W_one_le_et
    · rw [← u5_sup_conj_nE]
      exact sup_le (le_iSup W 0) (le_iSup W 1)

open M24 in
theorem conclK_m24_trio
    (MK : Subgroup G₀) : ConclK G₀ Lq (eSub basis_et) MK := by
  unfold ConclK
  have hpsl : IsPSL 3 2 1 (↥Lq ⧸ CFSG.pCore 2 ↥Lq) := isPSL_Lq
  have hcardX : Nat.card (↥Lq ⧸ CFSG.pCore 2 ↥Lq) = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hpsl
  have hq : CFSG.IsQuasisimple (↥Lq ⧸ CFSG.pCore 2 ↥Lq) :=
    CFSG.Quasithin.H13.isQuasisimple_of_isPSL hpsl
      (by rw [hcardX]; norm_num) (by rw [hcardX]; norm_num)
  have hLM : LieModel (↥Lq ⧸ CFSG.pCore 2 ↥Lq) .PSL 3 2 1 := Or.inl ⟨by decide, hpsl⟩
  have hshape : Shape443 (↥Lq ⧸ CFSG.pCore 2 ↥Lq) := Or.inr (Or.inl hLM)
  have hcommV : IsMulCommutative ↥(eSub basis_et) :=
    IsMulCommutative.of_setLike_mul_comm fun x hx y hy => eSub_comm basis_et x y hx hy
  letI : IsMulCommutative ↥(eSub basis_et) := hcommV
  have hFFL : IsFFModule (autOn Lq (eSub basis_et)) :=
    FFn.isFFModule_autOn_of_sum (n := 2) (k := 2) (by decide) (by norm_num) le_rfl
      isSumOfNaturalModules_et
  have hFF : IsFFModule (autOn (Subgroup.normalizer (eSub basis_et : Set G₀))
      (eSub basis_et)) :=
    isFFModule_of_le (autOn_mono' Lq_le_eNorm_et) hFFL
  have hnat : IsNaturalSumUnder 3 Lq (eSub basis_et) := isNaturalSumUnder_et
  refine Or.inl ⟨hq, hshape, Or.inl ⟨⟨hcommV, hFF⟩, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro _
    exact hnat
  ·
    intro h4
    have h1 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two
      (h4.statedClassicalModel (by decide))
    rw [hcardX] at h1
    norm_num at h1
  ·
    rintro ⟨-, hc, -⟩
    rw [F420.center_eq_bot_of_statedPSL hpsl] at hc
    rw [Subgroup.card_bot] at hc
    norm_num at hc
  ·
    intro h3 _
    have h1 := LieModel.card_psu_three_three h3
    rw [hcardX] at h1
    norm_num at h1

end CFSG.SectionRank.QTK.Insp443

end
