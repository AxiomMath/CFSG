module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LWeyl
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6LFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveSylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.HardMathSupport.Lang.E6Descent CFSG.LieType.Steinberg.Adjoint
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.NoOffTwE6Three
open CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Model

variable {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)

@[expose] noncomputable def sylP : Subgroup (ModGL Tag.E6 Ω) :=
  xHat Tag.E6 Ω modelHomE6.range ⊓ TwistedDiag.thetaFixed Fr

theorem sylP_le_monoHat : sylP Fr ≤ monoHat Tag.E6 Ω := fun _ hx => (mem_xHat.1 hx.1).1

theorem sylP_le_thetaFixed : sylP Fr ≤ TwistedDiag.thetaFixed Fr := inf_le_right

variable {ζ : Ωˣ}

theorem theta_pow_succ (hζ : ζ ^ 3 = 1) (a : ZMod 3) : (DiagTorus.theta ζ a) ^ (2 + 1) = 1 := by
  unfold DiagTorus.theta
  rw [← pow_mul, mul_comm, pow_mul]
  norm_num [hζ]

theorem exists_theta_eq (hζ' : orderOf ζ = 3) {b : Ωˣ} (hb : b ^ 3 = 1) :
    ∃ a : ZMod 3, b = DiagTorus.theta ζ a := by
  have hprim : IsPrimitiveRoot ζ 3 := hζ' ▸ IsPrimitiveRoot.orderOf ζ
  have hprim' : IsPrimitiveRoot (ζ : Ω) 3 := IsPrimitiveRoot.coe_units_iff.2 hprim
  have hb' : ((b : Ωˣ) : Ω) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb]; rfl
  obtain ⟨i, hi, hib⟩ := hprim'.eq_pow_of_pow_eq_one hb'
  refine ⟨(i : ZMod 3), Units.ext ?_⟩
  unfold DiagTorus.theta
  rw [ZMod.val_natCast_of_lt hi, Units.val_pow_eq_pow_val]
  exact hib.symm

theorem Psi_mem_sylP [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1)
    (u : Multiplicative (Fin 6 → ZMod 3)) : Psi6 hζ u ∈ sylP Fr := by
  refine ⟨?_, ?_⟩
  · show Psi6 hζ u ∈ xHat Tag.E6 Ω modelHomE6.range
    rw [Psi6_apply]
    exact rootDiagUnit_mem_xHat _ _
  · show Psi6 hζ u ∈ TwistedDiag.thetaFixed Fr
    rw [TwistedDiag.mem_thetaFixed, Psi6_apply]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr _).2 fun i => theta_pow_succ hζ _⟩

theorem exists_Psi_of_psiHat_eq_one [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1)
    (hζ' : orderOf ζ = 3) {x : monoHat Tag.E6 Ω} (hx : (x : ModGL Tag.E6 Ω) ∈ sylP Fr)
    (h1 : psiHat Tag.E6 Ω x = 1) :
    ∃ u : Multiplicative (Fin 6 → ZMod 3), (x : ModGL Tag.E6 Ω) = Psi6 hζ u := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one h1
  have hθ : TwistedDiag.theta Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b := by
    have h2 : (x : ModGL Tag.E6 Ω) ∈ TwistedDiag.thetaFixed Fr := hx.2
    rw [TwistedDiag.mem_thetaFixed] at h2
    rw [hb] at h2
    exact h2.2
  have hcube := (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).1 hθ
  choose a ha using fun i => exists_theta_eq hζ' (hcube i)
  refine ⟨Multiplicative.ofAdd a, ?_⟩
  rw [hb, Psi6_apply]
  congr 1
  funext i
  exact ha i

theorem isPGroup_sylP [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1)
    (hζ' : orderOf ζ = 3) : IsPGroup 3 (sylP Fr) := by
  intro x
  refine ⟨5, ?_⟩
  have hxm : (x : ModGL Tag.E6 Ω) ∈ monoHat Tag.E6 Ω := sylP_le_monoHat Fr x.2
  obtain ⟨hxm', hS⟩ := mem_xHat.1
    (show (x : ModGL Tag.E6 Ω) ∈ xHat Tag.E6 Ω modelHomE6.range from x.2.1)
  set xm : monoHat Tag.E6 Ω := ⟨x, hxm⟩ with hxm_def
  have hS81 : psiHat Tag.E6 Ω xm ^ 81 = 1 := by
    have h := pow_card_eq_one' (G := modelHomE6.range) (x := ⟨psiHat Tag.E6 Ω xm, hS⟩)
    rw [card_range_modelHomE6] at h
    exact congrArg Subtype.val h
  have hz : ((x : ModGL Tag.E6 Ω) ^ 81) ∈ sylP Fr := Subgroup.pow_mem _ x.2 81
  have hzm : (xm ^ 81 : monoHat Tag.E6 Ω) =
      ⟨(x : ModGL Tag.E6 Ω) ^ 81, sylP_le_monoHat Fr hz⟩ :=
    Subtype.ext (Subgroup.coe_pow _ _ 81)
  obtain ⟨u, hu⟩ := exists_Psi_of_psiHat_eq_one Fr hFr hζ hζ' (x := xm ^ 81)
    (by rw [hzm]; exact hz) (by rw [map_pow, hS81])
  have hu' : ((x : ModGL Tag.E6 Ω) ^ 81) = Psi6 hζ u := by
    rw [hzm] at hu
    exact hu
  apply Subtype.ext
  show (x : ModGL Tag.E6 Ω) ^ (3 ^ 5) = 1
  rw [show 3 ^ 5 = 81 * 3 by norm_num, pow_mul, hu']
  exact Psi6_pow_three hζ u

@[expose] noncomputable def psiP : sylP Fr →* WeylGroup Tag.E6 :=
  (psiHat Tag.E6 Ω).comp (Subgroup.inclusion (sylP_le_monoHat Fr))

@[expose] noncomputable def rhoP : sylP Fr →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) :=
  weylActGL.comp (psiP Fr)

@[expose] noncomputable def PsiP [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1) :
    Multiplicative (Fin 6 → ZMod 3) →* sylP Fr :=
  (Psi6 hζ).codRestrict (sylP Fr) (Psi_mem_sylP Fr hFr hζ)

theorem PsiP_injective [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1)
    (hζ' : orderOf ζ = 3) : Function.Injective (PsiP Fr hFr hζ) := fun a b h =>
  Psi6_injective hζ hζ' (congrArg Subtype.val h)

theorem psiP_apply (x : sylP Fr) :
    psiP Fr x = psiHat Tag.E6 Ω ⟨(x : ModGL Tag.E6 Ω), sylP_le_monoHat Fr x.2⟩ := rfl

theorem conj_PsiP [IsAlgClosed Ω] (hFr : ∀ c, Fr c = c ^ 2) (hζ : ζ ^ 3 = 1) (x : sylP Fr)
    (u : Multiplicative (Fin 6 → ZMod 3)) :
    x * PsiP Fr hFr hζ u * x⁻¹ =
      PsiP Fr hFr hζ (Multiplicative.ofAdd ((rhoP Fr x : Matrix (Fin 6) (Fin 6) (ZMod 3)).mulVec
        (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  have h := conj_Psi6_of_mem_monoHat hζ ⟨(x : ModGL Tag.E6 Ω), sylP_le_monoHat Fr x.2⟩
    (Multiplicative.toAdd u)
  rw [ofAdd_toAdd] at h
  exact h

theorem frameSubP_sylP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop) [IsAlgClosed Ω]
    {S : Type} [Group S] [Finite S] (hFr : ∀ c, Fr c = c ^ 2)
    (hζ : ζ ^ 3 = 1) (hζ' : orderOf ζ = 3) (ι : sylP Fr →* MulAut S)
    (hι : Function.Injective ι)
    (hgood : ∀ G : Subgroup (Multiplicative (Fin 6 → ZMod 3)), Sel G →
      RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
        (G : Set _)) → IsGood 3 (G.map (ι.comp (PsiP Fr hFr hζ)))) :
    FrameSubP Sel S ι.range := by
  have hinj := PsiP_injective Fr hFr hζ hζ'
  let U : Subgroup (sylP Fr) := (PsiP Fr hFr hζ).range
  let c : U ≃* Multiplicative (Fin 6 → ZMod 3) := (MonoidHom.ofInjective hinj).symm
  have hc1 : ∀ a : Multiplicative (Fin 6 → ZMod 3),
      c ⟨PsiP Fr hFr hζ a, a, rfl⟩ = a := by
    intro a
    show (MonoidHom.ofInjective hinj).symm ⟨PsiP Fr hFr hζ a, a, rfl⟩ = a
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  refine frameSubP_of_embedding Sel ι hι U c (rhoP Fr) ?_ ?_ ?_ ?_ ?_
  · rintro x ⟨_, a, rfl⟩
    exact ⟨_, (conj_PsiP Fr hFr hζ x a).symm⟩
  · rintro x ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
    rw [hc1 a, hc1 b]
    have h1 := conj_PsiP Fr hFr hζ x a
    have h2 : PsiP Fr hFr hζ (Multiplicative.ofAdd
        ((rhoP Fr x : Matrix (Fin 6) (Fin 6) (ZMod 3)).mulVec (Multiplicative.toAdd a))) =
        PsiP Fr hFr hζ b := by
      rw [← h1]
      exact h
    have h3 := hinj h2
    rw [← h3]
    simp
  · intro x
    constructor
    · intro hx
      have h1 : weylAct (psiP Fr x) = 1 := by
        have := congrArg (fun m : Matrix.GeneralLinearGroup (Fin 6) (ZMod 3) =>
          (m : Matrix (Fin 6) (Fin 6) (ZMod 3))) hx
        simpa [rhoP, coe_weylActGL] using this
      have h2 : psiP Fr x = 1 := weylAct_eq_one h1
      obtain ⟨u, hu⟩ := exists_Psi_of_psiHat_eq_one Fr hFr hζ hζ'
        (x := ⟨(x : ModGL Tag.E6 Ω), sylP_le_monoHat Fr x.2⟩) x.2 h2
      exact ⟨u, Subtype.ext hu.symm⟩
    · rintro ⟨u, rfl⟩
      have h1 : psiHat Tag.E6 Ω ⟨(PsiP Fr hFr hζ u : sylP Fr),
          sylP_le_monoHat Fr (PsiP Fr hFr hζ u).2⟩ = 1 := by
        refine psiHat_eq ?_
        show MapsRootLines (Psi6 hζ u) 1
        rw [Psi6_apply]
        exact mapsRootLines_rootDiagUnit _
      show weylActGL (psiP Fr (PsiP Fr hFr hζ u)) = 1
      rw [psiP_apply, h1, map_one]
  · intro x
    exact weylActGL_mem_W3 _
  · intro G hS hG
    have := hgood G hS hG
    convert this using 2
    rw [Subgroup.map_map]
    congr 1

end Model

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
