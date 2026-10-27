module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321FF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321QA
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321StepsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321QD

public section
namespace CFSG.Quasithin.H13.L3321

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G} {α : ↥L →* SL4}

theorem le_centralizer_of_ut_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (hD : FData G T M L D α) (hQe : IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)))
    (hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T))
    (Φ : IntMod (pCoreOf 2 (L ⊔ T)) hQe ≃* B3.Mod.V 8 B3.Mod.ut)
    (hΦ : B3.IsModIso (rhoQ hQe hD.surj hD.ker hPQ) (B3.actL 8 B3.Mod.ut) Φ)
    {A : Subgroup G} (hA : IsMaxElemAbelian T A) :
    A ≤ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := by
  by_contra hAC
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_LT_le hD.hyp
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hB := offenderImages_isFFStarOffender hQe hQT hTN ⟨A, ⟨hA, hAC⟩, rfl⟩
  have hB' := isFFStarOffender_map_congr Φ hB
  have hrange : ∀ φ ∈ autI hQe T, H.congrHom Φ φ ∈
      (alternatingGroup (Fin 8)).map (B3.Mod.act 8 B3.Mod.ut) := by
    intro φ hφ
    obtain ⟨⟨x, hxN⟩, hxT, rfl⟩ := (mem_autI hQe).1 hφ
    obtain ⟨s, hs, hsc⟩ := exists_decomp_F4 h7 h14 hD hxT
    set σ : B3.LG 8 := gA8.symm (α ⟨s, hs.2⟩) with hσ
    have hρ : rhoQ hQe hD.surj hD.ker hPQ σ = rhoL hQe ⟨s, hs.2⟩ :=
      rhoQ_eq hQe hD.surj hD.ker hPQ (by rw [hσ, MulEquiv.apply_symm_apply])
    have hconv : convI hQe ⟨x, hxN⟩ = rhoQ hQe hD.surj hD.ker hPQ σ := by
      rw [hρ]
      refine MulEquiv.ext fun v => IntMod.val_injective ?_
      rw [rhoL_apply_val, convI_apply_val]
      show x * v.val * x⁻¹ = s * v.val * s⁻¹
      have hc : s⁻¹ * x ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun w hw =>
          congrArg Subtype.val (hQe.1.is_comm.comm ⟨w, hw⟩ ⟨_, hsc⟩)
      have h1 := Subgroup.mem_centralizer_iff.1 hc v.val v.val_mem
      calc x * v.val * x⁻¹ = s * ((s⁻¹ * x) * v.val) * (s⁻¹ * x)⁻¹ * s⁻¹ := by group
        _ = s * (v.val * (s⁻¹ * x)) * (s⁻¹ * x)⁻¹ * s⁻¹ := by rw [← h1]
        _ = s * v.val * s⁻¹ := by group
    refine ⟨σ.1, σ.2, ?_⟩
    rw [hconv]
    refine MulEquiv.ext fun w => ?_
    rw [H.congrHom_apply, hΦ, MulEquiv.apply_symm_apply]
    rfl
  set B : Subgroup (MulAut (B3.Mod.V 8 B3.Mod.ut)) := (autI hQe A).map (H.congrHom Φ) with hBdef
  have hBle : B ≤ (alternatingGroup (Fin 8)).map (B3.Mod.act 8 B3.Mod.ut) := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact hrange φ (autI_mono hQe hA.1 hφ)
  set Bbar := B.comap (B3.Mod.act 8 B3.Mod.ut) with hBbar
  have hmap : Bbar.map (B3.Mod.act 8 B3.Mod.ut) = B :=
    Subgroup.map_comap_eq_self (hBle.trans (Subgroup.map_le_range _ _))
  have halt : Bbar ≤ alternatingGroup (Fin 8) := by
    intro τ hτ
    obtain ⟨τ', hτ', hττ'⟩ := hBle hτ
    rw [← B3.act_injective (n := 8) (by norm_num) B3.Mod.ut hττ']
    exact hτ'
  have hoff : B3.IsOffG 8 B3.Mod.ut Bbar := by
    refine ⟨Subgroup.map_mono le_top, ?_⟩
    rw [hmap]
    exact hB'.2
  obtain ⟨a, b, hab, hswap⟩ := swap_mem_of_isOffG hoff
  have h1 := halt hswap
  rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hab] at h1
  exact absurd h1 (by decide)

theorem step3_3_21fQ_of_F4 (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (he : Step3_3_21e_F4) : Step3_3_21fQ_F4 := by
  intro G _ _ T M L D h ⟨e⟩ hcV hmod hin hcommL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, ρ, Z₀, hD, hαv, hZ₀, -, ⟨D₀⟩⟩ := exists_fdata_ext_F4 h14 hGA h e hmod hin
  have hmod' : Mod3321 T L := ⟨hcV, Or.inl hmod⟩
  have hVL0 := vPlus_inf_centralizer_eq_bot_F4 he h ⟨e⟩ hmod' hD.TL
  have hZ₀b : Z₀ = ⊥ := eq_bot_of_le_fixV h hVL0 (hZ₀.trans inf_le_left)
  subst hZ₀b
  have hcomm := commV_eq_top_F4 h7 h14 he h ⟨e⟩ hmod'
  have hCL := inf_centralizer_L_eq_bot_F4 he h ⟨e⟩ hmod' hD.TL
  have hPQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := hD.pCoreOf_L_le le_rfl
  have hVQ : vPlus L T ≤ pCoreOf 2 (L ⊔ T) :=
    (Hyp331.vPlus_reduced h.toSetup331).1.trans inf_le_left
  have hperf : ⁅L, L⁆ = L := h.Lmax.1.2.1.2.1
  have hQV := fun q (hq : q ∈ pCoreOf 2 (L ⊔ T)) =>
    comm_mem_vPlus h hD.TL hperf hcommL hq
  have hQe := isElemAbelian_pCoreOf_F4 h7 h14 h hCL hQV
  rcases classify hQe h hD.surj hD.ker hPQ hαv hVQ hcomm D₀ hCL hQV with hQ | ⟨Φ, hΦ⟩
  · exact hQ
  · exfalso
    apply (h7 G T M L D h).2.1.1
    refine iSup₂_le fun A hA => ?_
    have h1 := le_centralizer_of_ut_F4 h7 h14 hD hQe hPQ Φ hΦ hA
    intro a ha
    exact Subgroup.centralizer_le hVQ (h1 ha)

end CFSG.Quasithin.H13.L3321
