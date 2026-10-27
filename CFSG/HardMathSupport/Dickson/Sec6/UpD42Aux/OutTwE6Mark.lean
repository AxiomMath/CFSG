module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6Tw
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public section

namespace CFSG.StandardType.UpD42Out

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rawMarking_of_mem_twistedE6Inndiag {S : Type} [Group S]
    (hZS : Subgroup.center S = ⊥) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (θ : S ≃* ↥(twistedE6RootGroup K σ)) {α : MulAut S}
    (hα : MulAut.congr θ α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    LargeEvenRawDatum ⟨.twE6, 0, f⟩ fun R _ I _ =>
      ∃ θ' : S ⧸ Subgroup.center S ≃* R, ∃ β ∈ I,
        LargeEvenInduces θ' (fun a b => b = α a) β := by
  classical
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ f := fun c => by simpa using hσ c
  let H := LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 f
  obtain ⟨e, T, hT, he⟩ := InnerDiagTwE6.exists_twistedTransport (K := K) f σ.toRingHom hσ'
  have hder : ⁅twistedFixedGroup TwistTag.E6 K σ.toRingHom,
      twistedFixedGroup TwistTag.E6 K σ.toRingHom⁆ =
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hf K hK σ.toRingHom hσ').2.2.1
  let T' : ↥(twistedE6RootGroup K σ) ≃* ↥H :=
    (MulEquiv.subgroupCongr hder.symm).trans (T.trans (MulEquiv.subgroupCongr
      (show LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm f = H from rfl)))
  have hT' : ∀ g : ↥(twistedE6RootGroup K σ),
      (((T' g : LargeEvenChevGL (LargeEvenCartanE 6) K) :
        Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
      e (((g : ModGL TwistTag.E6.tag K)) : Module.End K (RootModule TwistTag.E6.tag K))) :=
    fun g => hT _
  have hZ : Subgroup.center ↥H = ⊥ :=
    InnerDiagE6.center_eq_bot_of_mulEquiv (θ.trans T') hZS
  let q := centerQuotEquivOfBot hZ
  let ε : ↥(twistedE6RootGroup K σ) ≃* LargeEvenCenterQuot H := T'.trans q.symm
  let θ' : S ⧸ Subgroup.center S ≃* LargeEvenCenterQuot H :=
    (QuotientGroup.quotientMulEquivOfEq hZS).trans
      (QuotientGroup.quotientBot.trans (θ.trans ε))
  let β : MulAut (LargeEvenCenterQuot H) := MulAut.congr ε (MulAut.congr θ α)
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  have hmem : β ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K H := by
    have hle : twistedE6Inn K σ ⊔ twistedE6Diag K σ ≤
        (Subgroup.closure (LargeEvenInnSet (LargeEvenCenterQuot H) ∪
          LargeEvenChevDiagImage (LargeEvenCartanE 6) K H)).comap
          (MulAut.congr ε).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
          CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
        exact Subgroup.subset_closure (Or.inl ⟨ε g, rfl⟩)
      · rintro _ ⟨u, rfl⟩
        let b : Fin 6 → Kˣ := compatDiag TwistTag.E6 σ.toRingHom u
        have hb : ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (b i) :=
          compatDiag_perm u
        obtain ⟨φ, hφmem, hφ⟩ := InnerDiagE6.exists_diagAut hZ b
          (fun _ hh => InnerDiagTwE6.diagHom_conj_mem_twistedH f σ.toRingHom hσ' hb hh)
          (fun _ hh => InnerDiagTwE6.diagHom_inv_conj_mem_twistedH f σ.toRingHom hσ' hb hh)
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
        have hcongr : MulAut.congr ε (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) = φ := by
          refine MulEquiv.ext fun x => ?_
          obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥H) x
          rw [hφ h]
          have hεsymm : ε.symm (LargeEvenCenterMk H h) = T'.symm h := by
            change q.trans T'.symm (LargeEvenCenterMk H h) = T'.symm h
            rw [MulEquiv.trans_apply, centerQuotEquivOfBot_mk]
          have hεy : ε (compatDiagAutHom TwistTag.E6 K σ.toRingHom u (T'.symm h)) =
              LargeEvenCenterMk H (T' (compatDiagAutHom TwistTag.E6 K σ.toRingHom u (T'.symm h))) := by
            change q.symm (T' (compatDiagAutHom TwistTag.E6 K σ.toRingHom u (T'.symm h))) = _
            rw [centerQuotEquivOfBot_symm]
          rw [show (MulAut.congr ε (compatDiagAutHom TwistTag.E6 K σ.toRingHom u))
              (LargeEvenCenterMk H h) =
              ε (compatDiagAutHom TwistTag.E6 K σ.toRingHom u (ε.symm (LargeEvenCenterMk H h)))
              from rfl]
          rw [hεsymm, hεy]
          congr 1
          apply Subtype.ext
          apply Units.ext
          have hDcoe : (((compatDiagAutHom TwistTag.E6 K σ.toRingHom u (T'.symm h) :
              ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)) =
              rootDiagUnit TwistTag.E6.tag b * ((T'.symm h : ↥(twistedE6RootGroup K σ)) :
                ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag b)⁻¹ :=
            coe_compatDiagAutHom u _
          have hroot : e (((rootDiagUnit TwistTag.E6.tag b : ModGL TwistTag.E6.tag K)) :
              Module.End K (RootModule TwistTag.E6.tag K)) =
              LargeEvenDiagMap (LargeEvenCartanE 6) K b := he b
          rw [hT' (compatDiagAutHom TwistTag.E6 K σ.toRingHom u (T'.symm h)), hDcoe]
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv]
          have hroot_inv : e ((((rootDiagUnit TwistTag.E6.tag b)⁻¹ : ModGL TwistTag.E6.tag K)) :
              Module.End K (RootModule TwistTag.E6.tag K)) =
              LargeEvenDiagMap (LargeEvenCartanE 6) K b⁻¹ := he b⁻¹
          have hcoedinv : ((((TableB.diagHom (LargeEvenCartanE 6) K) b)⁻¹ :
              LargeEvenChevGL (LargeEvenCartanE 6) K) :
              Module.End K (LargeEvenChevModule (LargeEvenCartanE 6) K)) =
              LargeEvenDiagMap (LargeEvenCartanE 6) K b⁻¹ :=
            InnerDiagE6.coe_diagHom_inv Tag.E6 b
          rw [hroot, hroot_inv, ← hT' (T'.symm h), MulEquiv.apply_symm_apply,
            TableB.coe_diagHom, hcoedinv]
          rfl
        rw [hcongr]
        exact Subgroup.subset_closure (Or.inr hφmem)
    exact hle hα
  refine ⟨θ', β, hmem, ?_⟩
  have hq : ∀ a : S, θ' (QuotientGroup.mk a) = ε (θ a) := by
    intro a
    change (θ.trans ε) (QuotientGroup.quotientBot ((QuotientGroup.quotientMulEquivOfEq hZS)
      (QuotientGroup.mk a))) = ε (θ a)
    simp only [QuotientGroup.quotientBot, QuotientGroup.quotientKerEquivOfRightInverse,
      QuotientGroup.quotientMulEquivOfEq_mk]
    change (θ.trans ε) ((QuotientGroup.kerLift (MonoidHom.id S)) (QuotientGroup.mk a)) = ε (θ a)
    rw [QuotientGroup.kerLift_mk]
    rfl
  intro a b hb
  subst hb
  rw [hq a, hq (α a)]
  show (MulAut.congr ε (MulAut.congr θ α)) (ε (θ a)) = ε (θ (α a))
  simp [MulAut.congr_apply]

end CFSG.StandardType.UpD42Out
