module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNaturalC
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify

public section

namespace CFSG.GH74.QTGen4.DSGen4.Lin2D

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.DSGen4.Lin2A CFSG.GH74.QTGen4.DSGen4.Lin2B
open CFSG.GH74.QTGen4.DSGen4.Lin2C
open CFSG.QuasithinUnique.A5.Delta5 (Alt5)
open Certificates.A5GL42 (HN Facts)
open scoped commutatorElement Matrix

theorem isLin2Type_of_natural {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hq : IsL2Quot 2 (oTwoQuot ↥L)) (hc : CharTwo L)
    (he : IsElemAbelian 2 (pCoreOf 2 L)) (hn : Nat.card (pCoreOf 2 L) = 16)
    (hnat : NatSec L ⊥ (pCoreOf 2 L)) : IsLin2Type L 2 := by
  classical
  have hF : Facts := a5Facts
  have hA5 : A5Pre L L (pCoreOf 2 L) ⊥ := a5Pre_self hq hc he hn
  obtain ⟨Mdl⟩ : Nonempty (A5Model L L (pCoreOf 2 L) ⊥ HN) := by
    rcases hA5.exists_model' with ⟨-, hm⟩ | ⟨hno, -⟩
    · exact hm
    · exact absurd hnat hno
  have hker : ∀ y : ↥L, y ∈ CFSG.pCore 2 ↥L → Mdl.F.M (Subgroup.inclusion hA5.le y) = 1 := by
    intro y hy
    exact Mdl.core (Subgroup.inclusion hA5.le y) ((mem_pCore_iff_pCoreOf y).mp hy)
  obtain ⟨e⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two hq
  have hιinj : Function.Injective (iotaOf Mdl.F hA5 hker e) := iotaOf_injective Mdl.F hA5 hker e
  set ι : Alt5 →* GL (Fin 4) (ZMod 2) := iotaOf Mdl.F hA5 hker e with hιdef
  have hιM : ∀ ℓ : ↥L,
      ((ι (e (QuotientGroup.mk ℓ)) : GL (Fin 4) (ZMod 2)) : Mat4) = (Mdl.F.M ℓ : Mat4) := by
    intro ℓ
    rw [hιdef, iotaOf_mk Mdl.F hA5 hker e ℓ]
    rfl
  have hlift : ∀ σ : Alt5, ∃ ℓ : ↥L, e (QuotientGroup.mk ℓ) = σ := by
    intro σ
    obtain ⟨q, hq'⟩ := e.surjective σ
    obtain ⟨ℓ, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨ℓ, hq'⟩
  obtain ⟨ℓ₀, hℓ₀⟩ := hlift y0
  have hy0 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) = (Mdl.F.M ℓ₀ : Mat4) := by
    rw [← hℓ₀]
    exact hιM ℓ₀
  have hy0HN : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ∈ HN := by
    rw [hy0]
    exact Mdl.imgL ℓ₀ ℓ₀.2
  have hy0ne : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ≠ 1 := by
    intro h
    apply y0_ne_one
    apply hιinj
    rw [map_one]
    exact Units.ext h
  have hy0cube : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) * ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *
      ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) = 1 := by
    have h3 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, y0_cube, map_one, Units.val_one]
    rw [pow_three] at h3
    rw [mul_assoc]
    exact h3
  have hVff : ∀ v : Fin 4 → ZMod 2, ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0 :=
    fun v hv => hF.fixN _ hy0HN hy0ne hy0cube v hv
  have hVx : ι x0 ≠ 1 := by
    intro h
    apply x0_ne_one
    apply hιinj
    rw [map_one]
    exact h
  have hFdim : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 := GaloisField.finrank 2 (by norm_num)
  set κ := kappa (GaloisField 2 2) hFdim with hκdef
  obtain ⟨eqPSL⟩ := hq
  set χ : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    eqPSL.trans (pslEquivSL _) with hχdef
  set ψ : Alt5 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) := e.symm.trans χ with hψdef
  have hψe : ∀ ℓ : ↥L, ψ (e (QuotientGroup.mk ℓ)) = χ (QuotientGroup.mk ℓ) := by
    intro ℓ
    rw [hψdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  set WmA : Alt5 →* Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    (natMat (GaloisField 2 2) κ).comp ψ.toMonoidHom with hWmA
  set Wu : Alt5 →* GL (Fin 4) (ZMod 2) := toUnitsHom WmA with hWu
  have hWuc : ∀ σ : Alt5,
      ((Wu σ : GL (Fin 4) (ZMod 2)) : Mat4) = natMat (GaloisField 2 2) κ (ψ σ) := fun σ => rfl
  have hWx : Wu x0 ≠ 1 := by
    intro h
    have h1 : natMat (GaloisField 2 2) κ (ψ x0) = 1 := by
      rw [← hWuc, h, Units.val_one]
    have h2 : ψ x0 = 1 := eq_one_of_natMat_eq_one κ h1
    apply x0_ne_one
    apply ψ.injective
    rw [h2, map_one]
  have hWff : ∀ v : Fin 4 → ZMod 2, ((Wu y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v = v → v = 0 := by
    intro v hv
    rw [hWuc] at hv
    have hg3 : (ψ y0) ^ 3 = 1 := by rw [← map_pow, y0_cube, map_one]
    have hg1 : ψ y0 ≠ 1 := by
      intro h
      apply y0_ne_one
      apply ψ.injective
      rw [h, map_one]
    exact natMat_fixFree κ (ψ y0) hg3 hg1 v hv
  obtain ⟨TU, hTU⟩ := exists_intertwiner hF ι Wu hVx hVff hWx hWff
  have hTUM : ∀ ℓ : ↥L,
      (TU : Mat4) * (Mdl.F.M ℓ : Mat4) =
        natMat (GaloisField 2 2) κ (χ (QuotientGroup.mk ℓ)) * (TU : Mat4) := by
    intro ℓ
    have h1 := congrArg Units.val (hTU (e (QuotientGroup.mk ℓ)))
    rw [Units.val_mul, Units.val_mul, hιM ℓ, hWuc, hψe] at h1
    exact h1
  have hBQ : CFSG.QuasithinUnique.blockU L ≤ pCoreOf 2 L := blockU_le_pCoreOf
  let β : ↥(CFSG.QuasithinUnique.blockU L) →* Multiplicative (Fin 2 → GaloisField 2 2) :=
    (linMul κ (TU : Mat4)).comp (Mdl.F.φ.comp (Subgroup.inclusion hBQ))
  let α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    χ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  haveI : Finite (GaloisField 2 2) := inferInstance
  refine ⟨GaloisField 2 2, inferInstance, @Fintype.ofFinite (GaloisField 2 2) inferInstance, ?_, α,
    ?_, ?_, β, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 2 (by norm_num)
  ·
    intro s
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (χ.symm s)
    refine ⟨x, ?_⟩
    show χ (QuotientGroup.mk x) = s
    rw [hx, MulEquiv.apply_symm_apply]
  ·
    ext ℓ
    rw [MonoidHom.mem_ker]
    show χ (QuotientGroup.mk ℓ) = 1 ↔ ℓ ∈ CFSG.pCore 2 ↥L
    rw [map_eq_one_iff χ χ.injective, QuotientGroup.eq_one_iff]
  ·
    intro w
    set x : Fin 4 → ZMod 2 := κ.symm (Multiplicative.toAdd w) with hx
    set z : Fin 4 → ZMod 2 := ((TU⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ x with hz
    have hinj : Function.Injective
        (fun v : Fin 4 → ZMod 2 => ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v - v) := by
      intro v v' hvv
      simp only at hvv
      have h1 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ (v - v') - (v - v') = 0 := by
        rw [Matrix.mulVec_sub]
        calc ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v - ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v' -
              (v - v') = (((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v - v) -
                (((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ v' - v') := by abel
          _ = 0 := by rw [hvv, sub_self]
      have h2 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ (v - v') = v - v' := sub_eq_zero.mp h1
      exact sub_eq_zero.mp (hVff (v - v') h2)
    obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj z
    dsimp only at hv
    obtain ⟨qe, hqe⟩ := Mdl.F.surj (Multiplicative.ofAdd v)
    have hqev : Multiplicative.toAdd (Mdl.F.φ qe) = v := by
      rw [hqe]
      rfl
    have hqc : (ℓ₀ : G) * (qe : G) * (ℓ₀ : G)⁻¹ ∈ pCoreOf 2 L :=
      ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCore ℓ₀.2)) (qe : G)).mp qe.2
    set qc : ↥(pCoreOf 2 L) := ⟨(ℓ₀ : G) * (qe : G) * (ℓ₀ : G)⁻¹, hqc⟩ with hqcdef
    have hact : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ Multiplicative.toAdd (Mdl.F.φ qe) =
        Multiplicative.toAdd (Mdl.F.φ qc) := by
      rw [hy0]
      exact Mdl.F.act ℓ₀ qe qc rfl
    let u : ↥(CFSG.QuasithinUnique.blockU L) :=
      ⟨(ℓ₀ : G) * (qe : G) * (ℓ₀ : G)⁻¹ * (qe : G)⁻¹, comm_mem_blockU ℓ₀ qe.2⟩
    have hincl : Subgroup.inclusion hBQ u = qc * qe⁻¹ := by
      apply Subtype.ext
      simp [u, qc, mul_assoc]
    have hφu : Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ u)) = z := by
      rw [hincl, map_mul, map_inv, toAdd_mul, toAdd_inv, ← hact, hqev, ← hv, sub_eq_add_neg]
      rfl
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ (Subgroup.inclusion hBQ u))) =
      Multiplicative.toAdd w
    rw [toAdd_linMul, hφu, hz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, hx, LinearEquiv.apply_symm_apply]
  ·
    have hTUinj : ∀ y : Fin 4 → ZMod 2, (TU : Mat4) *ᵥ y = 0 → y = 0 := by
      intro y hy
      have h := congrArg (fun z => ((TU⁻¹ : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ z) hy
      simpa [Matrix.mulVec_mulVec] using h
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have key1 : β u = 1 ↔ (u : G) = 1 := by
      constructor
      · intro h
        have h' : linMul κ (TU : Mat4) (Mdl.F.φ (Subgroup.inclusion hBQ u)) = 1 := h
        have h1 := congrArg Multiplicative.toAdd h'
        rw [toAdd_linMul, toAdd_one] at h1
        have h2 : (TU : Mat4) *ᵥ Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ u)) = 0 :=
          κ.map_eq_zero_iff.mp h1
        have h4 : Mdl.F.φ (Subgroup.inclusion hBQ u) = 1 := toAdd_eq_zero.mp (hTUinj _ h2)
        exact Subgroup.mem_bot.mp ((Mdl.F.ker _).mp h4)
      · intro h
        have hu1 : u = 1 := Subtype.ext h
        rw [hu1, map_one]
    have key2 : (u : G) ∈ blockZ L ↔ (u : G) = 1 := by
      unfold blockZ
      rw [Subgroup.mem_inf]
      constructor
      · rintro ⟨-, hcent⟩
        rw [Subgroup.mem_centralizer_iff] at hcent
        have hcomm : (ℓ₀ : G) * (u : G) = (u : G) * (ℓ₀ : G) := hcent (ℓ₀ : G) ℓ₀.2
        have hconj : (u : G) = (ℓ₀ : G) * (u : G) * (ℓ₀ : G)⁻¹ := by
          rw [hcomm, mul_inv_cancel_right]
        have hact2 : ((ι y0 : GL (Fin 4) (ZMod 2)) : Mat4) *ᵥ
            Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ u)) =
              Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ u)) := by
          rw [hy0]
          exact Mdl.F.act ℓ₀ (Subgroup.inclusion hBQ u) (Subgroup.inclusion hBQ u) hconj
        have hφ1 : Mdl.F.φ (Subgroup.inclusion hBQ u) = 1 := toAdd_eq_zero.mp (hVff _ hact2)
        exact Subgroup.mem_bot.mp ((Mdl.F.ker _).mp hφ1)
      · intro h
        rw [h]
        exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    exact key1.trans key2.symm
  ·
    intro ℓ u v huv
    have hact := Mdl.F.act ℓ (Subgroup.inclusion hBQ u) (Subgroup.inclusion hBQ v) huv
    have hact' : (Mdl.F.M ℓ : Mat4) *ᵥ Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ u)) =
        Multiplicative.toAdd (Mdl.F.φ (Subgroup.inclusion hBQ v)) := hact
    show Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ (Subgroup.inclusion hBQ v))) =
      natLin (GaloisField 2 2) (α ℓ) (Multiplicative.toAdd (linMul κ (TU : Mat4) (Mdl.F.φ (Subgroup.inclusion hBQ u))))
    rw [toAdd_linMul, toAdd_linMul, ← hact', Matrix.mulVec_mulVec, hTUM ℓ, ← Matrix.mulVec_mulVec,
      natMat_mulVec, LinearEquiv.apply_symm_apply]
    rfl

end CFSG.GH74.QTGen4.DSGen4.Lin2D
