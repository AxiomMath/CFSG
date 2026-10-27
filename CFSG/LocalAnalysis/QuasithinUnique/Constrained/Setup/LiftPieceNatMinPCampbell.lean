module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceDict
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCampbell

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization commutatorElement

theorem natMinPCampbellProp
    : NatMinPCampbellProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hbase hY hmin hbasic himage hK
  classical
  have hS := ctx.setting
  have hn2 := hS.two_le
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  have hX := ctx.hX
  have hP : P ≤ Subgroup.normalizer (V : Set G) := le_top.trans hX
  have hSP : baum R ≤ P := hbasic.lt.le
  have hSM : baum R ≤ M := (inf_le_left : baum R ≤ R).trans hS.max.1
  have hMP : ¬ P ≤ M := hmin.not_le
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS ctx.comps
  have hbridge := even_SL2_original_bridge hS ctx.comps
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have hnat : NaturalFamily ((autOn (⊤ : Subgroup G) V).map ψ) F r (fun j => (Lc j).map ψ) := by
    have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
      rw [hbridge.K_eq]
      exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdel, -⟩
    · exact hnat
    · exfalso
      apply (himg.deleted hdel).1
      rw [← hKL]
      exact Subgroup.map_mono ctx.natural
  have hDeq := (himg.natural hnat).1
  have hSeq : (autOn (baum R) V).map ψ = ⨆ j, ((autOn R V).map ψ) ⊓ ((Lc j).map ψ) := by
    rw [← himg.baumann_eq]
    exact hDeq
  have layer := hmax.offenders.family.layer
  obtain ⟨ϱm, β, hequiv, hsurj, hker⟩ := natural_rho_model layer hnat hSeq i
  have hmemX : ∀ p : ↥P, ψ (rho V P hP p) ∈ (Lc i).map ψ ⊔ (autOn (baum R) V).map ψ := by
    intro p
    have h1 : rho V P hP p ∈ autOn P V := (mem_autOn_self_iff hP).2 ⟨p, rfl⟩
    rw [himage.image] at h1
    rw [← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem ψ h1
  let ρX : ↥P →* ↥((Lc i).map ψ ⊔ (autOn (baum R) V).map ψ) :=
    (ψ.comp (rho V P hP)).codRestrict _ hmemX
  let ϱ0 : ↥P →* Matrix.SpecialLinearGroup (Fin 2) F := ϱm.comp ρX
  have hϱ0 : Function.Surjective ϱ0 := by
    intro g
    obtain ⟨x, hx⟩ := hsurj g
    have hxm : (x : W ≃ₗ[ZMod 2] W) ∈ (autOn P V).map ψ := by
      rw [himage.image, Subgroup.map_sup]
      exact x.2
    obtain ⟨y, hy, hyx⟩ := hxm
    obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hP).1 hy
    refine ⟨p, ?_⟩
    have : ρX p = x := Subtype.ext hyx
    show ϱm (ρX p) = g
    rw [this]
    exact hx
  let ι := modCommEquiv' θ (Lc i)
  let ψI : ↥(modComm V (Lc i)) →* Multiplicative (Fin 2 → F) :=
    (AddMonoidHom.toMultiplicative
      (β.toAddMonoidHom.comp (Submodule.mkQ (fixIn ((Lc i).map ψ)
        (commGL ((Lc i).map ψ) ⊤))).toAddMonoidHom)).comp ι.toMonoidHom
  have hψIapply : ∀ v : ↥(modComm V (Lc i)), Multiplicative.toAdd (ψI v) =
      β (Submodule.Quotient.mk ⟨vecOf θ ⟨v.1, modComm_le' V (Lc i) v.2⟩,
        (mem_modComm_iff' θ (Lc i) _).1 v.2⟩) := fun v => rfl
  have hψI : Function.Surjective ψI := by
    intro w
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (β.symm (Multiplicative.toAdd w))
    refine ⟨ι.symm (Multiplicative.ofAdd u), ?_⟩
    apply Multiplicative.toAdd.injective
    show β (Submodule.Quotient.mk (Multiplicative.toAdd (ι (ι.symm (Multiplicative.ofAdd u))))) = _
    rw [ι.apply_symm_apply, toAdd_ofAdd, hu, AddEquiv.apply_symm_apply]
  have hequiv' : ∀ (p : ↥P) (v v' : ↥(modComm V (Lc i))),
      (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψI v') =
        (ϱ0 p : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (ψI v)) := by
    intro p v v' hv'
    have hvV : (v : G) ∈ V := modComm_le' V (Lc i) v.2
    have hv'V : (v' : G) ∈ V := modComm_le' V (Lc i) v'.2
    have h1 : rho V P hP p ⟨v, hvV⟩ = ⟨v', hv'V⟩ :=
      Subtype.ext (by rw [rho_apply_coe]; exact hv'.symm)
    have h2 : vecOf θ ⟨v', hv'V⟩ = ψ (rho V P hP p) (vecOf θ ⟨v, hvV⟩) := by
      rw [← h1]
      exact (binPsi_vecOf' θ _ _).symm
    rw [hψIapply, hψIapply]
    exact hequiv (ρX p) ⟨vecOf θ ⟨v, hvV⟩, (mem_modComm_iff' θ (Lc i) _).1 v.2⟩
      ⟨vecOf θ ⟨v', hv'V⟩, (mem_modComm_iff' θ (Lc i) _).1 v'.2⟩ h2
  have hLiA : Lc i ≤ autOn (⊤ : Subgroup G) V := (ctx.comps.isComp i).1
  have hcentr : ∀ v : ↥V, ((v : G) ∈ Subgroup.centralizer
      (rhoPreimage V ⊤ hX (Lc i) : Set G)) ↔ ∀ a ∈ Lc i, a v = v := by
    intro v
    constructor
    · intro hc a ha
      obtain ⟨p, rfl⟩ := (mem_autOn_self_iff hX).1 (hLiA ha)
      have hpm : (p : G) ∈ rhoPreimage V ⊤ hX (Lc i) := mem_rhoPreimage.2 ha
      have hcomm := Subgroup.mem_centralizer_iff.1 hc (p : G) hpm
      apply Subtype.ext
      rw [rho_apply_coe, hcomm, mul_inv_cancel_right]
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨hgT, hgρ⟩ := hg
      have h2 := congrArg (fun x : ↥V => (x : G)) (h _ hgρ)
      simp only [rho_apply_coe] at h2
      calc g * v = (g * v * g⁻¹) * g := by group
        _ = v * g := by rw [h2]
  have hker' : ψI.ker =
      (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf (modComm V (Lc i)) := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hvV : (v : G) ∈ V := modComm_le' V (Lc i) v.2
    have e1 : ψI v = 1 ↔ ∀ a ∈ Lc i, a ⟨v, hvV⟩ = ⟨v, hvV⟩ := by
      have h0 : ψI v = 1 ↔ Multiplicative.toAdd (ψI v) = 0 := Iff.rfl
      rw [h0, hψIapply, hker ⟨vecOf θ ⟨v.1, hvV⟩, (mem_modComm_iff' θ (Lc i) _).1 v.2⟩]
      constructor
      · intro h a ha
        have h1 := h (ψ a) (Subgroup.mem_map_of_mem ψ ha)
        apply vecOf_injective' θ
        rw [← binPsi_vecOf' θ a ⟨v, hvV⟩]
        exact h1
      · intro h l hl
        obtain ⟨a, ha, rfl⟩ := hl
        have h1 := h a ha
        show binPsi θ a (vecOf θ ⟨v.1, hvV⟩) = vecOf θ ⟨v.1, hvV⟩
        rw [binPsi_vecOf', h1]
    have e3 : (v : G) ∈ Subgroup.centralizer (oddOrderSubgroup P : Set G) ↔
        (v : G) ∈ Subgroup.centralizer (rhoPreimage V ⊤ hX (Lc i) : Set G) := by
      have h : (v : G) ∈ modComm V (Lc i) ⊓ Subgroup.centralizer (oddOrderSubgroup P : Set G) ↔
          (v : G) ∈ modComm V (Lc i) ⊓
            Subgroup.centralizer (rhoPreimage V ⊤ hX (Lc i) : Set G) := by
        rw [hK.fixed]
      simp only [Subgroup.mem_inf, v.2, true_and] at h
      exact h
    rw [e1, ← hcentr ⟨v, hvV⟩, e3]
  refine ⟨natQuotSetting_of_module hbasic.sylow hbasic.not_normal hSM hMP hbasic.max
    himage.I_reduced ϱ0 hϱ0 ψI hψI hequiv' hker', ?_⟩
  rw [hbase.J_S]
  have hF : Fintype.card F = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hS.card_eq
  have hU := hmax.U_sylow i
  obtain ⟨θi, βi, x, hc, hline⟩ := natural_coords hnat hU
  have hcardU := natCard_of_natural_coords (Lc := fun j => (Lc j).map ψ) (i := i) hU.1 θi x hline
  have hnt : ∃ l ∈ (autOn R V).map ψ ⊓ (Lc i).map ψ, l ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : (autOn R V).map ψ ⊓ (Lc i).map ψ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot, hF] at hcardU
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨l, hl, hl1⟩ := hnt
  have hlD : l ∈ (autOn (thompsonJ R) V).map ψ := by
    rw [hDeq]
    exact (le_iSup (fun j => (autOn R V).map ψ ⊓ (Lc j).map ψ) i) hl
  obtain ⟨y, hy, hyl⟩ := hlD
  obtain ⟨g', hg'J, rfl⟩ := mem_autOn_iff.1 hy
  have hmove : ∃ v ∈ commGL ((Lc i).map ψ) ⊤, l v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hl1 (layer.faithful_W i l hl.2 (fun v hv => by
      rw [hcon v hv, sub_self]
      exact Submodule.zero_mem _))
  obtain ⟨v, hv, hlv⟩ := hmove
  have hu : ((elOf θ v : ↥V) : G) ∈ modComm V (Lc i) := elOf_mem_modComm' θ (Lc i) hv
  have hne : ⁅(g' : G), ((elOf θ v : ↥V) : G)⁆ ≠ 1 := by
    intro h1
    apply hlv
    have h2 : conjAct V g' (elOf θ v) = elOf θ v := by
      apply Subtype.ext
      rw [coe_conjAct_apply]
      have : (g' : G) * ((elOf θ v : ↥V) : G) = ((elOf θ v : ↥V) : G) * g' :=
        commutatorElement_eq_one_iff_mul_comm.1 h1
      rw [this, mul_inv_cancel_right]
    have h3 := binPsi_vecOf' θ (conjAct V g') (elOf θ v)
    rw [h2, vecOf_elOf] at h3
    rw [← hyl]
    exact h3
  intro hbot
  apply hne
  have := Subgroup.commutator_mem_commutator hg'J hu
  rw [hbot] at this
  exact Subgroup.mem_bot.1 this

end CFSG.QuasithinUnique.Setup.Lift
