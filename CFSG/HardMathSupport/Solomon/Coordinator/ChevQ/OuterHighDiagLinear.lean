module

public import CFSG.LieType.SeitzGeneration.OutdiagParabolic
public import CFSG.LieType.SeitzGeneration.HyperIrrBridge
public import CFSG.LieType.Seitz.Defs
public import CFSG.LieType.SeitzGeneration.HyperAveraging

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2

open Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Lifts

variable {n : ℕ} {F : Type} [Field F]

theorem scalarGL_injective (hn : 0 < n) :
    Function.Injective (GeneralLinearGroup.scalar (Fin n) : Fˣ →* GL (Fin n) F) := by
  intro a b h
  have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) ⟨0, hn⟩ ⟨0, hn⟩) h
  simp only [scalarGL_coe_eq_smul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one] at h1
  exact Units.ext h1

theorem coe_eq_smul_of_eq_scalar_mul {A B : GL (Fin n) F} {u : Fˣ}
    (h : B * A = GeneralLinearGroup.scalar (Fin n) u * (A * B)) :
    (B : Matrix (Fin n) (Fin n) F) * A = (u : F) • ((A : Matrix (Fin n) (Fin n) F) * B) := by
  have h1 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) h
  simp only [Units.val_mul] at h1
  rw [h1, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul]

theorem coe_pow_eq_smul {A : GL (Fin n) F} {p : ℕ} {c : Fˣ}
    (h : A ^ p = GeneralLinearGroup.scalar (Fin n) c) :
    (A : Matrix (Fin n) (Fin n) F) ^ p = (c : F) • 1 := by
  rw [← Units.val_pow_eq_pow_val, h, scalarGL_coe_eq_smul]

def commGL (M : Matrix (Fin n) (Fin n) F) : Subgroup (GL (Fin n) F) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) F) * M = M * A}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq, Units.val_mul] at hA hB ⊢
    rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at hA ⊢
    have h1 : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
        1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M
        = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M *
          ((A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [h2, Matrix.mul_one]
      _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((M * A) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          simp only [Matrix.mul_assoc]
      _ = ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          ((A * M) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by rw [hA]
      _ = (((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A) * M *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
      _ = M * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h1, Matrix.one_mul]

theorem mem_commGL {M : Matrix (Fin n) (Fin n) F} {A : GL (Fin n) F} :
    A ∈ commGL M ↔ (A : Matrix (Fin n) (Fin n) F) * M = M * A := Iff.rfl

theorem scalar_mem_commGL (M : Matrix (Fin n) (Fin n) F) (c : Fˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ commGL M := by
  rw [mem_commGL, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one]

def stabGL (W : Submodule F (Fin n → F)) : Subgroup (GL (Fin n) F) where
  carrier := {A | (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) ∧
    ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W}
  one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
  mul_mem' := by
    rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hA1 _ (hB1 w hw)
    · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
      exact hB2 _ (hA2 w hw)
  inv_mem' := by
    rintro A ⟨hA1, hA2⟩
    exact ⟨hA2, by simpa using hA1⟩

theorem scalar_mem_stabGL (W : Submodule F (Fin n → F)) (c : Fˣ) :
    GeneralLinearGroup.scalar (Fin n) c ∈ stabGL W := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · rw [scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem _ hw
  · rw [← map_inv, scalarGL_coe_eq_smul, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem _ hw

theorem mem_stabGL_of_pow {W : Submodule F (Fin n → F)} {A : GL (Fin n) F} {p : ℕ} (hp : 0 < p)
    {c : Fˣ} (hAp : A ^ p = GeneralLinearGroup.scalar (Fin n) c)
    (hW : ∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) : A ∈ stabGL W :=
  ⟨hW, inv_mulVec_mem_of_pow_scalar hp hAp hW⟩

variable [Finite F]

theorem mem_of_conjAut_mem_closure (hn : 3 ≤ n) {K : Subgroup (GL (Fin n) F)}
    (hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ K) {T : Set (GL (Fin n) F)}
    (hT : T ⊆ K) {A : GL (Fin n) F}
    (hA : conjAut n F A ∈ Subgroup.closure (conjAut n F '' T)) : A ∈ K := by
  rw [← MonoidHom.map_closure] at hA
  obtain ⟨g, hg, hgA⟩ := Subgroup.mem_map.1 hA
  have hgK : g ∈ K := (Subgroup.closure_le K).2 hT hg
  obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn (g⁻¹ * A)).mp
    (by rw [map_mul, map_inv, hgA, inv_mul_cancel])
  have hAeq : A = g * GeneralLinearGroup.scalar (Fin n) c := by
    rw [hc]
    group
  rw [hAeq]
  exact K.mul_mem hgK (hK c)

theorem mem_of_conjAut_mem_pair (hn : 3 ≤ n) {K : Subgroup (GL (Fin n) F)}
    (hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ K) {a₁ a₂ : GL (Fin n) F}
    (h₁ : a₁ ∈ K) (h₂ : a₂ ∈ K) {A : GL (Fin n) F}
    (hA : conjAut n F A ∈ Subgroup.closure ({conjAut n F a₁, conjAut n F a₂} :
      Set (MulAut (projectiveSL n F)))) : A ∈ K := by
  refine mem_of_conjAut_mem_closure hn hK (T := {a₁, a₂}) ?_ ?_
  · rintro x (rfl | rfl) <;> assumption
  · rw [Set.image_pair]
    exact hA

theorem mem_of_conjAut_mem_triple (hn : 3 ≤ n) {E : Subgroup (MulAut (projectiveSL n F))}
    {K : Subgroup (GL (Fin n) F)} (hK : ∀ c : Fˣ, GeneralLinearGroup.scalar (Fin n) c ∈ K)
    {a₁ a₂ a₃ : GL (Fin n) F} (h₁ : a₁ ∈ K) (h₂ : a₂ ∈ K) (h₃ : a₃ ∈ K)
    (hgen : E ≤ Subgroup.closure ({conjAut n F a₁, conjAut n F a₂, conjAut n F a₃} :
      Set (MulAut (projectiveSL n F))))
    {A : GL (Fin n) F} (hA : conjAut n F A ∈ E) : A ∈ K := by
  refine mem_of_conjAut_mem_closure hn hK (T := {a₁, a₂, a₃}) ?_ ?_
  · rintro x (rfl | rfl | rfl) <;> assumption
  · rw [Set.image_insert_eq, Set.image_pair]
    exact hgen hA

end Lifts

section Bridge

variable {n : ℕ} {F : Type} [Field F]

@[expose] def hyperLiftFix (p : ℕ) (E : Subgroup (MulAut (projectiveSL n F))) :
    Set (SpecialLinearGroup (Fin n) F) :=
  {k | ∃ F' : Subgroup (MulAut (projectiveSL n F)), F' ≤ E ∧ F'.relIndex E = p ∧
    ∀ A : GL (Fin n) F, conjAut n F A ∈ F' → k ∈ FixSL (A : Matrix (Fin n) (Fin n) F)}

theorem seitzHyperGamma_eq_top_of_closure_hyperLiftFix (hn : 0 < n) {p : ℕ}
    {E : Subgroup (MulAut (projectiveSL n F))} (hlin : E ≤ linearAutGroup n F)
    (h : Subgroup.closure (hyperLiftFix p E) = ⊤) : seitzHyperGamma p E = ⊤ := by
  have hle : Subgroup.closure (hyperLiftFix p E) ≤ (seitzHyperGamma p E).comap (proj n F) := by
    rw [Subgroup.closure_le]
    rintro k ⟨F', hF'E, hF'p, hk⟩
    have hfix : proj n F k ∈ fixedPoints F' := by
      rw [mem_fixedPoints]
      intro φ hφ
      obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 (hlin (hF'E hφ))
      exact conjAut_proj_eq_of_mem_fixSL hn (hk A hφ)
    exact (le_iSup₂_of_le F' ⟨hF'E, hF'p⟩ le_rfl : fixedPoints F' ≤ seitzHyperGamma p E) hfix
  rw [h, top_le_iff] at hle
  rw [eq_top_iff]
  intro g _
  obtain ⟨k, rfl⟩ := proj_surjective (n := n) (K := F) g
  have hk : k ∈ (seitzHyperGamma p E).comap (proj n F) := hle ▸ Subgroup.mem_top k
  exact hk

variable [Finite F]

theorem conjUnit_mem_hyperLiftFix (hn : 3 ≤ n) {p : ℕ} {E : Subgroup (MulAut (projectiveSL n F))}
    {a b : GL (Fin n) F} {Na Nb : Matrix (Fin n) (Fin n) F} (P : GL (Fin n) F)
    (haE : conjAut n F a ∈ E) (hbE : conjAut n F b ∈ E)
    (hrel : (Subgroup.closure ({conjAut n F a, conjAut n F b} :
      Set (MulAut (projectiveSL n F)))).relIndex E = p)
    (hMa : (a : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      (P : Matrix (Fin n) (Fin n) F) * Na)
    (hMb : (b : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) =
      (P : Matrix (Fin n) (Fin n) F) * Nb)
    {g₀ : SpecialLinearGroup (Fin n) F}
    (hga : Na * (g₀ : Matrix (Fin n) (Fin n) F) = (g₀ : Matrix (Fin n) (Fin n) F) * Na)
    (hgb : Nb * (g₀ : Matrix (Fin n) (Fin n) F) = (g₀ : Matrix (Fin n) (Fin n) F) * Nb) :
    conjUnit P g₀ ∈ hyperLiftFix p E := by
  refine ⟨Subgroup.closure {conjAut n F a, conjAut n F b}, closure_pair_le haE hbE, hrel,
    fun A hA => mem_FixSL_of_mul_comm ?_⟩
  exact mem_of_conjAut_mem_pair hn (K := commGL ((conjUnit P g₀ : SpecialLinearGroup (Fin n) F) :
    Matrix (Fin n) (Fin n) F)) (scalar_mem_commGL _) (commute_conjUnit P hMa hga)
    (commute_conjUnit P hMb hgb) hA

end Bridge

section Reducible

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_conjActionGL_hom (hn : 3 ≤ n) (E : Subgroup (MulAut (projectiveSL n F)))
    (hlin : E ≤ linearAutGroup n F) :
    ∃ ρ : E →* Module.End F (Matrix (Fin n) (Fin n) F),
      ∀ (A : GL (Fin n) F) (hA : conjAut n F A ∈ E), ρ ⟨conjAut n F A, hA⟩ = conjActionGL A := by
  classical
  let H : Subgroup (GL (Fin n) F) := E.comap (conjAut n F)
  let πH : H →* E := ((conjAut n F).comp H.subtype).codRestrict E (fun h => h.2)
  have hπH : Function.Surjective πH := by
    rintro ⟨e, he⟩
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 (hlin he)
    refine ⟨⟨A, show conjAut n F A ∈ E from hA ▸ he⟩, Subtype.ext ?_⟩
    exact hA
  let cH : H →* (Module.End F (Matrix (Fin n) (Fin n) F))ˣ :=
    (conjActionGL.comp H.subtype).toHomUnits
  have hker : πH.ker ≤ cH.ker := by
    intro A hA
    rw [MonoidHom.mem_ker] at hA ⊢
    have h1 : conjAut n F (A : GL (Fin n) F) = 1 := congrArg Subtype.val hA
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn _).mp h1
    apply Units.ext
    show conjActionGL (A : GL (Fin n) F) = 1
    rw [← hc, conjActionGL_scalar]
  let ρ' : E →* (Module.End F (Matrix (Fin n) (Fin n) F))ˣ :=
    (πH.liftOfRightInverse (Function.surjInv hπH) (Function.rightInverse_surjInv hπH)) ⟨cH, hker⟩
  have hρ : ∀ A : H, (ρ' (πH A) : Module.End F (Matrix (Fin n) (Fin n) F)) =
      conjActionGL (A : GL (Fin n) F) := fun A => by
    have := MonoidHom.liftOfRightInverse_comp_apply πH (Function.surjInv hπH)
      (Function.rightInverse_surjInv hπH) ⟨cH, hker⟩ A
    rw [this]
    rfl
  refine ⟨(Units.coeHom _).comp ρ', fun A hA => ?_⟩
  exact hρ ⟨A, hA⟩

theorem unip_mem_closure_hyperLiftFix (hn : 3 ≤ n) {p : ℕ} [Fact p.Prime] (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)}
    (hW : LiftStable E W) {g : SpecialLinearGroup (Fin n) F}
    (hg : (g : Matrix (Fin n) (Fin n) F) - 1 ∈ thetaSpace W) :
    g ∈ Subgroup.closure (hyperLiftFix p E) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_conjActionGL_hom hn E hlin
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  have hEc : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have hEp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hE.2 a a.2)
  have hS : ∀ (e : E), ∀ x ∈ thetaSpace W, ρ e x ∈ thetaSpace W := by
    rintro ⟨e, he⟩ x hx
    obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he)
    rw [hρ A he]
    exact conjActionGL_mem_thetaSpace (hW A he) (hW A⁻¹ (by rw [map_inv]; exact E.inv_mem he)) hx
  have hmem := mem_iSup_hyperFixed_top hpF hEc hEp ρ (thetaSpace W) hS (k := 3) (by norm_num)
    hcard hg
  let motive : Matrix (Fin n) (Fin n) F → Prop := fun ψ =>
    ∃ h : ψ ∈ thetaSpace W, unipSL h ∈ Subgroup.closure (hyperLiftFix p E)
  have h0 : motive 0 := by
    refine ⟨(thetaSpace W).zero_mem, ?_⟩
    have : unipSL (thetaSpace W).zero_mem = 1 := Subtype.ext (by simp [coe_unipSL])
    rw [this]
    exact Subgroup.one_mem _
  have hadd : ∀ x y, motive x → motive y → motive (x + y) := by
    rintro ψ ψ' ⟨h, hK⟩ ⟨h', hK'⟩
    refine ⟨(thetaSpace W).add_mem h h', ?_⟩
    have : unipSL ((thetaSpace W).add_mem h h') = unipSL h * unipSL h' := Subtype.ext (by
      show 1 + (ψ + ψ') = (1 + ψ) * (1 + ψ')
      simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, thetaSpace_mul h h', add_zero]
      abel)
    rw [this]
    exact Subgroup.mul_mem _ hK hK'
  have hgen : ∀ (F' : Subgroup E), F'.index = p → ∀ ψ ∈ hyperFixed ρ F' ⊓ thetaSpace W,
      motive ψ := by
    intro F' hF' ψ hψ
    have hψ1 := (Submodule.mem_inf.1 hψ).1
    have hψ2 := (Submodule.mem_inf.1 hψ).2
    refine ⟨hψ2, Subgroup.subset_closure ⟨F'.map E.subtype, Subgroup.map_subtype_le F', ?_, ?_⟩⟩
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      exact hF'
    · intro A hA
      obtain ⟨e, he, hee⟩ := Subgroup.mem_map.1 hA
      have hAE : conjAut n F A ∈ E := by
        rw [← hee]
        exact e.2
      have he' : e = ⟨conjAut n F A, hAE⟩ := Subtype.ext hee
      have hfix : ρ e ψ = ψ := (mem_hyperFixed.1 hψ1) e he
      rw [he', hρ A hAE] at hfix
      exact unipSL_mem_FixSL hψ2 (commute_of_conjActionGL_eq hfix)
  have hmotive : motive ((g : Matrix (Fin n) (Fin n) F) - 1) := by
    refine Submodule.iSup_induction (motive := motive) (fun F' : Subgroup E =>
      ⨆ (_ : F'.index = p), hyperFixed ρ F' ⊓ thetaSpace W) hmem ?_ h0 hadd
    intro F' ψ hψ
    exact Submodule.iSup_induction (motive := motive)
      (fun _ : F'.index = p => hyperFixed ρ F' ⊓ thetaSpace W) hψ
      (fun hF'' ψ' hψ' => hgen F' hF'' ψ' hψ') h0 hadd
  obtain ⟨h, hK⟩ := hmotive
  have hg' : unipSL h = g := Subtype.ext (by
    show 1 + ((g : Matrix (Fin n) (Fin n) F) - 1) = (g : Matrix (Fin n) (Fin n) F)
    abel)
  rwa [hg'] at hK

theorem closure_hyperLiftFix_of_reducible (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpF : (p : F) ≠ 0) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) {W : Submodule F (Fin n → F)}
    (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) (hWE : LiftStable E W) :
    Subgroup.closure (hyperLiftFix p E) = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨W', hcompl, hW'H⟩ := exists_invariant_compl_gl (H := E.comap (conjAut n F))
    (card_comap_conjAut_ne_zero hn hp hpF hE) (W := W)
    (fun x hx w hw => hWE x (Subgroup.mem_comap.1 hx) w hw)
  have hW'E : LiftStable E W' := fun A hA w hw => hW'H A (Subgroup.mem_comap.2 hA) w hw
  have hW'0 : W' ≠ ⊥ := by
    intro h
    apply hWt
    have := codisjoint_iff.1 hcompl.2
    rwa [h, sup_bot_eq] at this
  exact eq_top_of_unip_isCompl hcompl hW0 hW'0
    (fun g hg => unip_mem_closure_hyperLiftFix hn hpF hE hcard hlin hWE hg)
    (fun g hg => unip_mem_closure_hyperLiftFix hn hpF hE hcard hlin hW'E hg)

end Reducible

section Irreducible

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_indep_of_card_cube {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 3) :
    ∃ x ∈ E, ∃ y ∈ E, y ≠ 1 ∧ x ∉ Subgroup.zpowers y := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨y, hyE, hy1⟩ : ∃ y ∈ E, y ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
    rw [this, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  have hord : orderOf y = p := orderOf_eq_prime (hexp y hyE) hy1
  obtain ⟨x, hxE, hx⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers y := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers y := fun x hx => hcon x hx
    have hfin' : Finite (Subgroup.zpowers y) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; exact hp.ne_zero)
    have h1 := Subgroup.card_le_of_le hle
    rw [hcard, Nat.card_zpowers, hord] at h1
    have h2 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h2
    omega
  exact ⟨x, hxE, y, hyE, hy1, hx⟩

theorem eq_smul_one_of_commute_lifts {p : ℕ} (hζ : ∃ ζ : F, IsPrimitiveRoot ζ p) (hp : 0 < p)
    (hn : 0 < n) {E : Subgroup (MulAut (projectiveSL n F))}
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤)
    {M : Matrix (Fin n) (Fin n) F} (hM : M ^ p = 1)
    (hcomm : ∀ A : GL (Fin n) F, conjAut n F A ∈ E →
      (A : Matrix (Fin n) (Fin n) F) * M = M * A) :
    ∃ ξ : F, M = ξ • 1 := by
  classical
  obtain ⟨ξ, v, -, hv0, hMv⟩ := exists_eigenvector_of_pow_eq_one hp hζ hn hM
  let W : Submodule F (Fin n → F) :=
    LinearMap.ker (Matrix.toLin' (M - ξ • (1 : Matrix (Fin n) (Fin n) F)))
  have hW : ∀ w, w ∈ W ↔ M *ᵥ w = ξ • w := fun w => by
    simp [W, LinearMap.mem_ker, Matrix.toLin'_apply, sub_eq_zero]
  have hWs : LiftStable E W := by
    intro A hA w hw
    rw [hW] at hw ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm A hA, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  rcases hirr W hWs with h | h
  · have hv : v ∈ (⊥ : Submodule F (Fin n → F)) := h ▸ (hW v).2 hMv
    exact absurd (by simpa using hv) hv0
  · refine ⟨ξ, ?_⟩
    rw [Matrix.ext_iff_mulVec]
    intro w
    rw [(hW w).1 (h ▸ Submodule.mem_top), Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_noncomm_lifts (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hlin : E ≤ linearAutGroup n F) {e₁ e₂ : MulAut (projectiveSL n F)} (he₁ : e₁ ∈ E)
    (he₂ : e₂ ∈ E) (he₂1 : e₂ ≠ 1) (he₁₂ : e₁ ∉ Subgroup.zpowers e₂)
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) :
    ∃ x y : GL (Fin n) F, conjAut n F x ∈ E ∧ conjAut n F y ∈ E ∧
      (x : Matrix (Fin n) (Fin n) F) * y ≠ y * x := by
  by_contra hab
  push Not at hab
  obtain ⟨X, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₁)
  obtain ⟨Y, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₂)
  obtain ⟨i, j, z₀, hij, hz₀c, hz₀p⟩ := exists_pth_root_element hn hp hp2 hE he₁ he₂
  have hz₀E : conjAut n F z₀ ∈ E := by
    rw [hz₀c]
    exact E.mul_mem (E.pow_mem he₁ i) (E.pow_mem he₂ j)
  have hē₀ : conjAut n F z₀ ≠ 1 := by
    rw [hz₀c]
    exact pow_mul_pow_ne_one_of_indep hp (hE.2 _ he₁) (hE.2 _ he₂) he₂1 he₁₂ hij
  have hz₀pM : (z₀ : Matrix (Fin n) (Fin n) F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hz₀p, Units.val_one]
  obtain ⟨ξ, hξ⟩ := eq_smul_one_of_commute_lifts (exists_primitiveRoot_of_dvd_card_sub_one hp hpq)
    hp.pos (by omega) hirr hz₀pM (fun A hA => hab A z₀ hA hz₀E)
  obtain ⟨u, hu⟩ := exists_scalarGL_of_gl_coe_eq_smul (by omega) hξ
  exact hē₀ (by rw [← hu, conjAut_scalar])

theorem exists_radical_triple_gl (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) {x y : GL (Fin n) F}
    (hx : conjAut n F x ∈ E) (hy : conjAut n F y ∈ E)
    (hxy : (x : Matrix (Fin n) (Fin n) F) * y ≠ y * x) :
    ∃ (ζ : F) (r : GL (Fin n) F), IsPrimitiveRoot ζ p ∧
      (x : Matrix (Fin n) (Fin n) F) * y = ζ • ((y : Matrix (Fin n) (Fin n) F) * x) ∧
      conjAut n F r ∈ E ∧ conjAut n F r ≠ 1 ∧
      E ≤ Subgroup.closure ({conjAut n F x, conjAut n F y, conjAut n F r} :
        Set (MulAut (projectiveSL n F))) ∧
      (x : Matrix (Fin n) (Fin n) F) * r = r * x ∧
      (y : Matrix (Fin n) (Fin n) F) * r = r * y := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  have hn0 : 0 < n := by omega
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinj := scalarGL_injective (F := F) hn0
  obtain ⟨u, hu⟩ := exists_scalarGL_comm hn hE hx hy
  obtain ⟨cx, hcx⟩ := exists_scalarGL_pow hn hE hx
  obtain ⟨cy, hcy⟩ := exists_scalarGL_pow hn hE hy
  have hup : u ^ p = 1 := by
    have h1 := qcomm_pow_eq_one (A := x) (B := y) (mul_scalarGL_comm u) (mul_scalarGL_comm cx)
      hu hcx
    rw [← map_pow] at h1
    exact hinj (by rw [h1, map_one])
  have huM := coe_eq_smul_of_eq_scalar_mul hu
  set ζ : F := ((u : F))⁻¹ with hζdef
  have hζ : (x : Matrix (Fin n) (Fin n) F) * y = ζ • ((y : Matrix (Fin n) (Fin n) F) * x) := by
    rw [huM, smul_smul, hζdef, inv_mul_cancel₀ u.ne_zero, one_smul]
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hxy
    rw [hζ, h, one_smul]
  have hζp : ζ ^ p = 1 := by
    rw [hζdef, inv_pow, ← Units.val_pow_eq_pow_val, hup, Units.val_one, inv_one]
  have hprim : IsPrimitiveRoot ζ p := isPrimitiveRoot_of_pow_eq_one_ne_one hp hζp hζ1
  have hx1 : conjAut n F x ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn x).mp h
    apply hxy
    rw [← hc, scalarGL_coe_eq_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hy1 : conjAut n F y ∉ Subgroup.zpowers (conjAut n F x) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    obtain ⟨c, hc⟩ := (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn ((x ^ k)⁻¹ * y)).mp
      (by rw [map_mul, map_inv, map_zpow, hk, inv_mul_cancel])
    have hyeq : y = x ^ k * GeneralLinearGroup.scalar (Fin n) c := by
      rw [hc]
      group
    apply hxy
    have hxy' : x * y = y * x := by
      rw [hyeq]
      calc x * (x ^ k * GeneralLinearGroup.scalar (Fin n) c)
          = (x * x ^ k) * GeneralLinearGroup.scalar (Fin n) c := (mul_assoc _ _ _).symm
        _ = (x ^ k * x) * GeneralLinearGroup.scalar (Fin n) c := by
          rw [(Commute.self_zpow x k).eq]
        _ = x ^ k * (x * GeneralLinearGroup.scalar (Fin n) c) := mul_assoc _ _ _
        _ = x ^ k * (GeneralLinearGroup.scalar (Fin n) c * x) := by rw [mul_scalarGL_comm c x]
        _ = (x ^ k * GeneralLinearGroup.scalar (Fin n) c) * x := (mul_assoc _ _ _).symm
    have h2 := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hxy'
    simpa only [Units.val_mul] using h2
  obtain ⟨e₀, he₀E, he₀⟩ : ∃ e₀ ∈ E, e₀ ∉ Subgroup.closure
      ({conjAut n F x, conjAut n F y} : Set (MulAut (projectiveSL n F))) := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.closure
        ({conjAut n F x, conjAut n F y} : Set (MulAut (projectiveSL n F))) := fun e he => hcon e he
    have h1 := Subgroup.card_le_of_le hle
    have h2 := card_closure_pair_le hp.pos (hcomm _ hx _ hy) (hE.2 _ hx) (hE.2 _ hy)
    rw [hcard] at h1
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨r₀, rfl⟩ := mem_linearAutGroup_iff.1 (hlin he₀E)
  obtain ⟨α, hα⟩ := exists_scalarGL_comm hn hE hx he₀E
  obtain ⟨β, hβ⟩ := exists_scalarGL_comm hn hE hy he₀E
  have hαp : (α : F) ^ p = 1 := by
    have h1 := qcomm_pow_eq_one (A := x) (B := r₀) (mul_scalarGL_comm α) (mul_scalarGL_comm cx)
      hα hcx
    rw [← map_pow] at h1
    have h2 : α ^ p = 1 := hinj (by rw [h1, map_one])
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have hβp : (β : F) ^ p = 1 := by
    have h1 := qcomm_pow_eq_one (A := y) (B := r₀) (mul_scalarGL_comm β) (mul_scalarGL_comm cy)
      hβ hcy
    rw [← map_pow] at h1
    have h2 : β ^ p = 1 := hinj (by rw [h1, map_one])
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, j, h1, h2⟩ := exists_adjust hprim hζ (coe_eq_smul_of_eq_scalar_mul hα)
    (coe_eq_smul_of_eq_scalar_mul hβ) hαp hβp α.ne_zero β.ne_zero
  have hrmat : ((r₀ * x ^ i * y ^ j : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (r₀ : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) ^ i *
        (y : Matrix (Fin n) (Fin n) F) ^ j := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  have hrE : conjAut n F (r₀ * x ^ i * y ^ j) ∈ E := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact E.mul_mem (E.mul_mem he₀E (E.pow_mem hx i)) (E.pow_mem hy j)
  have hrcl : conjAut n F (r₀ * x ^ i * y ^ j) ∉ Subgroup.closure
      ({conjAut n F x, conjAut n F y} : Set (MulAut (projectiveSL n F))) := by
    intro h
    apply he₀
    have e2 : conjAut n F r₀ = conjAut n F (r₀ * x ^ i * y ^ j) * ((conjAut n F y) ^ j)⁻¹ *
        ((conjAut n F x) ^ i)⁻¹ := by
      rw [map_mul, map_mul, map_pow, map_pow]
      group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_closure_pair_right _ _) _)))
      (Subgroup.inv_mem _ (Subgroup.pow_mem _ (mem_closure_pair_left _ _) _))
  refine ⟨ζ, r₀ * x ^ i * y ^ j, hprim, hζ, hrE, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hrcl (h ▸ Subgroup.one_mem _)
  · exact le_closure_triple_of_independent hp hcard hx hy hrE (hE.2 _ hx) hx1 hy1 hrcl
  · rw [hrmat]
    exact h1.symm
  · rw [hrmat]
    exact h2.symm

theorem exists_mul_pow_eq_pow {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F - 1) {c t : F}
    (ht : t ≠ 0) (hc0 : c ≠ 0) (hnc : ∀ b : F, b ^ p ≠ c) :
    ∃ (j : ℕ) (s : F), s ≠ 0 ∧ t * c ^ j = s ^ p := by
  have := Fintype.ofFinite F
  set d := (Nat.card F - 1) / p with hd
  have hdp : d * p = Nat.card F - 1 := Nat.div_mul_cancel hpq
  have hpow : ∀ z : F, z ≠ 0 → (z ^ d) ^ p = 1 := fun z hz => by
    rw [← pow_mul, hdp, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one z hz
  have hω1 : c ^ d ≠ 1 := by
    intro h
    obtain ⟨s, -, hs⟩ := exists_pow_eq_of_pow_div_eq_one hpq hc0 h
    exact hnc s hs
  have hprim : IsPrimitiveRoot (c ^ d) p :=
    isPrimitiveRoot_of_pow_eq_one_ne_one hp (hpow c hc0) hω1
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, hti⟩ := hprim.eq_pow_of_pow_eq_one (hpow t ht)
  have e : d * i + (p - i) * d = d * p := by
    rw [mul_comm (p - i) d, ← Nat.mul_add, Nat.add_sub_cancel' hi.le]
  have htc : (t * c ^ (p - i)) ^ ((Nat.card F - 1) / p) = 1 := by
    rw [← hd, mul_pow, ← hti, ← pow_mul, ← pow_mul, ← pow_add, e, pow_mul, hpow c hc0]
  obtain ⟨s, hs0, hs⟩ := exists_pow_eq_of_pow_div_eq_one hpq
    (mul_ne_zero ht (pow_ne_zero _ hc0)) htc
  exact ⟨p - i, s, hs0, hs.symm⟩

theorem exists_normalized_gl {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F - 1)
    {a r : Matrix (Fin n) (Fin n) F} (har : a * r = r * a) {ca c : F} (hca0 : ca ≠ 0)
    (ha : a ^ p = ca • 1) (hc : r ^ p = c • 1) (hc0 : c ≠ 0) (hnc : ∀ b : F, b ^ p ≠ c) :
    ∃ (j : ℕ) (s : F), s ≠ 0 ∧ (a * r ^ j) ^ p = s ^ p • (1 : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨j, s, hs0, hs⟩ := exists_mul_pow_eq_pow hp hpq hca0 hc0 hnc
  refine ⟨j, s, hs0, ?_⟩
  have hcomm : Commute a (r ^ j) := Commute.pow_right har j
  rw [hcomm.mul_pow, ha, ← pow_mul, mul_comm j p, pow_mul, hc, smul_pow, one_pow,
    Matrix.smul_mul, Matrix.one_mul, smul_smul, hs]

theorem exists_kron_data_gl (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) {x y : GL (Fin n) F}
    (hx : conjAut n F x ∈ E) (hy : conjAut n F y ∈ E)
    (hxy : (x : Matrix (Fin n) (Fin n) F) * y ≠ y * x)
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) :
    ∃ (x' y' r : GL (Fin n) F) (sx sy ζ c : F) (A B C : Matrix (Fin n) (Fin n) F)
      (u₀ : Fin n → F),
      conjAut n F x' ∈ E ∧ conjAut n F y' ∈ E ∧ conjAut n F r ∈ E ∧
      E ≤ Subgroup.closure ({conjAut n F x', conjAut n F y', conjAut n F r} :
        Set (MulAut (projectiveSL n F))) ∧
      (x' : Matrix (Fin n) (Fin n) F) = sx • A ∧ (y' : Matrix (Fin n) (Fin n) F) = sy • B ∧
      (r : Matrix (Fin n) (Fin n) F) = C ∧ KronData p ζ c A B C u₀ := by
  classical
  have hn0 : 0 < n := by omega
  obtain ⟨ζ, r, hprim, hζ, hrE, hr1, hgen, hxr, hyr⟩ :=
    exists_radical_triple_gl hn hp hE hcard hlin hx hy hxy
  have hpq : p ∣ Nat.card F - 1 := dvd_card_sub_one_of_isPrimitiveRoot hprim hp.ne_zero
  have hrK : ∀ A : GL (Fin n) F, conjAut n F A ∈ E →
      (A : Matrix (Fin n) (Fin n) F) * r = r * A := fun A hA =>
    mem_of_conjAut_mem_triple hn (K := commGL (r : Matrix (Fin n) (Fin n) F))
      (scalar_mem_commGL _) hxr hyr (mem_commGL.2 rfl) hgen hA
  obtain ⟨cr, hcr⟩ := exists_scalarGL_pow hn hE hrE
  obtain ⟨cx, hcx⟩ := exists_scalarGL_pow hn hE hx
  obtain ⟨cy, hcy⟩ := exists_scalarGL_pow hn hE hy
  have hc := coe_pow_eq_smul hcr
  have hnc : ∀ b : F, b ^ p ≠ (cr : F) := by
    intro b hb
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact cr.ne_zero hb.symm
    obtain ⟨ξ, hξ⟩ := eq_smul_one_of_commute_lifts ⟨ζ, hprim⟩ hp.pos hn0 hirr
      (M := b⁻¹ • (r : Matrix (Fin n) (Fin n) F))
      (by rw [smul_pow, hc, smul_smul, inv_pow, hb, inv_mul_cancel₀ cr.ne_zero, one_smul])
      (fun A hA => by rw [Matrix.mul_smul, Matrix.smul_mul, hrK A hA])
    apply hr1
    have hr : (r : Matrix (Fin n) (Fin n) F) = (b * ξ) • 1 := by
      rw [mul_smul, ← hξ, smul_smul, mul_inv_cancel₀ hb0, one_smul]
    obtain ⟨w, hw⟩ := exists_scalarGL_of_gl_coe_eq_smul hn0 hr
    rw [← hw, conjAut_scalar]
  obtain ⟨jx, sx, hsx0, hsx⟩ := exists_normalized_gl hp hpq hxr cx.ne_zero (coe_pow_eq_smul hcx)
    hc cr.ne_zero hnc
  obtain ⟨jy, sy, hsy0, hsy⟩ := exists_normalized_gl hp hpq hyr cy.ne_zero (coe_pow_eq_smul hcy)
    hc cr.ne_zero hnc
  set x₁ : GL (Fin n) F := x * r ^ jx with hx₁
  set y₁ : GL (Fin n) F := y * r ^ jy with hy₁
  have hx₁mat : (x₁ : Matrix (Fin n) (Fin n) F) =
      (x : Matrix (Fin n) (Fin n) F) * (r : Matrix (Fin n) (Fin n) F) ^ jx := by
    rw [hx₁, Units.val_mul, Units.val_pow_eq_pow_val]
  have hy₁mat : (y₁ : Matrix (Fin n) (Fin n) F) =
      (y : Matrix (Fin n) (Fin n) F) * (r : Matrix (Fin n) (Fin n) F) ^ jy := by
    rw [hy₁, Units.val_mul, Units.val_pow_eq_pow_val]
  have hx₁E : conjAut n F x₁ ∈ E := by
    rw [hx₁, map_mul, map_pow]
    exact E.mul_mem hx (E.pow_mem hrE jx)
  have hy₁E : conjAut n F y₁ ∈ E := by
    rw [hy₁, map_mul, map_pow]
    exact E.mul_mem hy (E.pow_mem hrE jy)
  have hgen₁ : E ≤ Subgroup.closure ({conjAut n F x₁, conjAut n F y₁, conjAut n F r} :
      Set (MulAut (projectiveSL n F))) := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro z (rfl | rfl | rfl)
    · have e : conjAut n F x = conjAut n F x₁ * (conjAut n F r ^ jx)⁻¹ := by
        rw [hx₁, map_mul, map_pow]
        group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    · have e : conjAut n F y = conjAut n F y₁ * (conjAut n F r ^ jy)⁻¹ := by
        rw [hy₁, map_mul, map_pow]
        group
      rw [SetLike.mem_coe, e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _))
    · exact Subgroup.subset_closure (by simp)
  have hcX : Commute (x : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := hxr
  have hcY : Commute (y : Matrix (Fin n) (Fin n) F) (r : Matrix (Fin n) (Fin n) F) := hyr
  have hxy₁ : (x₁ : Matrix (Fin n) (Fin n) F) * y₁ =
      ζ • ((y₁ : Matrix (Fin n) (Fin n) F) * x₁) := by
    rw [hx₁mat, hy₁mat]
    exact quasi_mul_pow hζ hcX hcY jx jy
  have hX₁p : (x₁ : Matrix (Fin n) (Fin n) F) ^ p =
      sx ^ p • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [hx₁mat]
    exact hsx
  have hY₁p : (y₁ : Matrix (Fin n) (Fin n) F) ^ p =
      sy ^ p • (1 : Matrix (Fin n) (Fin n) F) := by
    rw [hy₁mat]
    exact hsy
  have hB₀ : (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F)) ^ p = 1 := by
    rw [smul_pow, hY₁p, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hsy0), one_smul]
  obtain ⟨ξ, v, hξ, hv0, hB₀v⟩ := exists_eigenvector_of_pow_eq_one hp.pos ⟨ζ, hprim⟩ hn0 hB₀
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hξ
    exact zero_ne_one hξ
  have hxA : (x₁ : Matrix (Fin n) (Fin n) F) =
      sx • (sx⁻¹ • (x₁ : Matrix (Fin n) (Fin n) F)) := by
    rw [smul_smul, mul_inv_cancel₀ hsx0, one_smul]
  have hyB : (y₁ : Matrix (Fin n) (Fin n) F) =
      (sy * ξ) • (ξ⁻¹ • (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F))) := by
    rw [smul_smul, smul_smul, show sy * ξ * ξ⁻¹ * sy⁻¹ = 1 by field_simp, one_smul]
  refine ⟨x₁, y₁, r, sx, sy * ξ, ζ, cr, sx⁻¹ • (x₁ : Matrix (Fin n) (Fin n) F),
    ξ⁻¹ • (sy⁻¹ • (y₁ : Matrix (Fin n) (Fin n) F)), (r : Matrix (Fin n) (Fin n) F), v,
    hx₁E, hy₁E, hrE, hgen₁, hxA, hyB, rfl, ?_⟩
  refine ⟨hp, hp2, hpF, hprim, hnc, ?_, ?_, hc, ?_, ?_, ?_, hv0, ?_, ?_⟩
  · rw [smul_pow, hX₁p, smul_smul, inv_pow, inv_mul_cancel₀ (pow_ne_zero p hsx0), one_smul]
  · rw [smul_pow, hB₀, inv_pow, hξ, inv_one, one_smul]
  · rw [smul_smul]
    exact smul_quasi hxy₁ _ _
  · have hc₁X : (x₁ : Matrix (Fin n) (Fin n) F) * r = r * x₁ := by
      rw [hx₁mat]
      exact (Commute.mul_left hcX (Commute.self_pow _ _).symm).eq
    rw [Matrix.smul_mul, Matrix.mul_smul, hc₁X]
  · have hc₁Y : (y₁ : Matrix (Fin n) (Fin n) F) * r = r * y₁ := by
      rw [hy₁mat]
      exact (Commute.mul_left hcY (Commute.self_pow _ _).symm).eq
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hc₁Y]
  · rw [Matrix.smul_mulVec, hB₀v, smul_smul, inv_mul_cancel₀ hξ0, one_smul]
  · intro W hAW hBW hCW
    apply hirr W
    have hx₁W : ∀ w ∈ W, (x₁ : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := fun w hw => by
      have h1 := W.smul_mem sx (hAW w hw)
      rw [hxA, Matrix.smul_mulVec]
      exact h1
    have hy₁W : ∀ w ∈ W, (y₁ : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := fun w hw => by
      have h1 := W.smul_mem (sy * ξ) (hBW w hw)
      rw [hyB, Matrix.smul_mulVec]
      exact h1
    obtain ⟨c₁, hc₁⟩ := exists_scalarGL_pow hn hE hx₁E
    obtain ⟨c₂, hc₂⟩ := exists_scalarGL_pow hn hE hy₁E
    intro A hA
    exact (mem_of_conjAut_mem_triple hn (scalar_mem_stabGL W) (mem_stabGL_of_pow hp.pos hc₁ hx₁W)
      (mem_stabGL_of_pow hp.pos hc₂ hy₁W) (mem_stabGL_of_pow hp.pos hcr hCW) hgen₁ hA).1

theorem closure_hyperLiftFix_of_irreducible (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) {x y : GL (Fin n) F}
    (hx : conjAut n F x ∈ E) (hy : conjAut n F y ∈ E)
    (hxy : (x : Matrix (Fin n) (Fin n) F) * y ≠ y * x)
    (hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤) :
    Subgroup.closure (hyperLiftFix p E) = ⊤ := by
  classical
  have : Finite (MulAut (projectiveSL n F)) := MulEquiv.finite_left
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨x', y', r, sx, sy, ζ, c, A, B, C, u₀, hx'E, hy'E, hrE, hgen, hxA, hyB, hrC, hk⟩ :=
    exists_kron_data_gl hn hp hp2 hpF hE hcard hlin hx hy hxy hirr
  obtain rfl : n = p * p := hk.card_eq_sq
  obtain ⟨P, hAP, hBP, hCP⟩ := exists_kron_model hk
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hKp := compMat_pow_eq hp.pos hk.hC P hCP
  have hc1 : 1 + c ≠ 0 := by
    intro h0
    apply hk.notPow (-1)
    rw [hodd.neg_one_pow]
    linear_combination (-1 : F) * h0
  obtain ⟨a, D, D', U, N, haC, haK, hDD, hUN, haeq⟩ :=
    exists_noncentral_block hp3 hodd hk.prim hc1 hKp
  have hxP : (x' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sx • kr (shiftMat p F) 1) := by
    rw [hxA, Matrix.smul_mul, hAP, Matrix.mul_smul]
  have hyP : (y' : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * (sy • kr (charMat p ζ⁻¹) 1) := by
    rw [hyB, Matrix.smul_mul, hBP, Matrix.mul_smul]
  have hrP : (r : Matrix (Fin (p * p)) (Fin (p * p)) F) *
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) =
      (P : Matrix (Fin (p * p)) (Fin (p * p)) F) * kr 1 (compMat p c) := by
    rw [hrC]
    exact hCP
  have hrel := relIndex_three_pairs hp.pos hx'E hy'E hrE (hcomm _ hx'E _ hy'E)
    (hcomm _ hx'E _ hrE) (hcomm _ hy'E _ hrE) (hE.2 _ hx'E) (hE.2 _ hy'E) (hE.2 _ hrE) hgen hcard
  let K'' : Subgroup (SpecialLinearGroup (Fin (p * p)) F) :=
    (Subgroup.closure (hyperLiftFix p E)).comap (conjUnit P)
  have hd : ∀ u : SpecialLinearGroup (Fin p) F, dHom u ∈ K'' := by
    intro u
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure
      (conjUnit_mem_hyperLiftFix hn P hx'E hy'E hrel.1 hxP hyP ?_ ?_))
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_dHom, kr_mul, Matrix.mul_one,
        Matrix.one_mul]
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_dHom, kr_mul, Matrix.mul_one,
        Matrix.one_mul]
  have ht : ∀ (m : Fin p) (z : F) (hz : z ^ p = 1), tEl m z hz ∈ K'' := by
    intro m z hz
    have hdc : charMat p ζ⁻¹ * diagUpd m z = diagUpd m z * charMat p ζ⁻¹ := by
      simp only [charMat, diagUpd, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure
      (conjUnit_mem_hyperLiftFix hn P hy'E hrE hrel.2.2 hyP hrP ?_ ?_))
    · simp only [Matrix.smul_mul, Matrix.mul_smul, coe_tEl, kr_mul, Matrix.mul_one, hdc]
    · simp only [coe_tEl, kr_mul, Matrix.mul_one, Matrix.one_mul]
  have hdetMf : (Mf (a : Matrix (Fin p) (Fin p) F)).det = 1 := by
    rw [haeq]
    exact det_Mf_conj hpF hDD hUN
  have hKa : compMat p c * ((a : Matrix (Fin p) (Fin p) F) - 1) =
      ((a : Matrix (Fin p) (Fin p) F) - 1) * compMat p c := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, haK]
  set aB : SpecialLinearGroup (Fin (p * p)) F := ⟨Mf (a : Matrix (Fin p) (Fin p) F), hdetMf⟩
    with haBdef
  have haB : aB ∈ K'' := by
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure
      (conjUnit_mem_hyperLiftFix hn P hx'E hrE hrel.2.1 hxP hrP ?_ ?_))
    · show sx • kr (shiftMat p F) 1 * Mf (a : Matrix (Fin p) (Fin p) F) =
        Mf (a : Matrix (Fin p) (Fin p) F) * (sx • kr (shiftMat p F) 1)
      simp only [Matrix.smul_mul, Matrix.mul_smul, Mf, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Matrix.one_mul, kr_mul, shiftMat_mul_projF hp.pos,
        projF_mul_shiftMat hp.pos, smul_add]
    · show kr 1 (compMat p c) * Mf (a : Matrix (Fin p) (Fin p) F) =
        Mf (a : Matrix (Fin p) (Fin p) F) * kr 1 (compMat p c)
      simp only [Mf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, kr_mul, hKa]
  have hblock : a ∈ blockSub hpF K'' := ⟨aB, haB, rfl⟩
  have htop : K'' = ⊤ := eq_top_of_three_families hk.prim hp3 hpF hd ht haC hblock
  rw [eq_top_iff]
  intro g _
  have h1 : conjUnit P⁻¹ g ∈ K'' := htop ▸ Subgroup.mem_top _
  have h2 : conjUnit P (conjUnit P⁻¹ g) ∈ Subgroup.closure (hyperLiftFix p E) := h1
  rwa [conjUnit_conjUnit_inv_self] at h2

end Irreducible

section Main

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem seitzHyperGamma_eq_top_of_le_linearAut (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) (hpq : p ∣ Nat.card F - 1) {E : Subgroup (MulAut (projectiveSL n F))}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) (hlin : E ≤ linearAutGroup n F) :
    seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_closure_hyperLiftFix (by omega) hlin ?_
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W
  · obtain ⟨W, hW0, hWt, hWE⟩ := hred
    exact closure_hyperLiftFix_of_reducible hn hp hpF hE hcard hlin hW0 hWt hWE
  · have hirr : ∀ W : Submodule F (Fin n → F), LiftStable E W → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra hcon
      push Not at hcon
      exact hred ⟨W, hcon.1, hcon.2, hW⟩
    obtain ⟨e₁, he₁, e₂, he₂, he₂1, he₁₂⟩ := exists_indep_of_card_cube hp hE.2 hcard
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_noncomm_lifts hn hp hp2 hpq hE hlin he₁ he₂ he₂1 he₁₂ hirr
    exact closure_hyperLiftFix_of_irreducible hn hp hp2 hpF hE hcard hlin hx hy hxy hirr

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2
