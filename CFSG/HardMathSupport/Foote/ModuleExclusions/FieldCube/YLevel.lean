module

public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.NormalCore
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Lift
public import CFSG.HardMathSupport.Foote.ModuleExclusions.FieldCube.Generation
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Cases
public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.WeakCoreKill
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffChar
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner

variable {Y : Type} [Group Y]

theorem modelAct_of_mem {K : Subgroup Y} [K.Normal] {M : Type*} [Group M]
    (e : K ⧸ Subgroup.center K ≃* M) (k : K) :
    modelAct K e (k : Y) = MulAut.conj (e (QuotientGroup.mk k)) := by
  ext m
  obtain ⟨q, rfl⟩ := e.surjective m
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  simp only [modelAct, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulAut.conj_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have h1 : (MulAut.conjNormal (k : Y) : MulAut K) n = k * n * k⁻¹ :=
    Subtype.ext (by simp [MulAut.conjNormal_apply])
  rw [centerQuotientHom_mk, h1]
  simp [QuotientGroup.mk_mul]

theorem mem_sup_centralizer_of_modelAct_mem_inn {K : Subgroup Y} [K.Normal]
    (hperf : Group.IsPerfect K) {M : Type*} [Group M] (e : K ⧸ Subgroup.center K ≃* M) {w : Y}
    (hw : modelAct K e w ∈ (MulAut.conj : M →* MulAut M).range) :
    w ∈ K ⊔ Subgroup.centralizer (K : Set Y) := by
  obtain ⟨p, hp⟩ := hw
  obtain ⟨q, rfl⟩ := e.surjective p
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : modelAct K e ((k : Y)⁻¹ * w) = 1 := by
    rw [map_mul, map_inv, modelAct_of_mem, ← hp]; simp
  have h2 : centerQuotientHom K (MulAut.conjNormal ((k : Y)⁻¹ * w)) = 1 := by
    have h1' : (MulAut.congr e) (centerQuotientHom K (MulAut.conjNormal ((k : Y)⁻¹ * w))) = 1 :=
      h1
    exact (MulAut.congr e).injective (h1'.trans (map_one _).symm)
  have h3 : (MulAut.conjNormal ((k : Y)⁻¹ * w) : MulAut K) = 1 :=
    centerQuotientHom_injective K (by rw [h2, map_one])
  have h4 : (k : Y)⁻¹ * w ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun φ : MulAut K => ((φ ⟨h, hh⟩ : K) : Y)) h3
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have : w = (k : Y) * ((k : Y)⁻¹ * w) := by group
  rw [this]
  exact Subgroup.mul_mem_sup k.2 h4

theorem le_normalCore_of_linear [Finite Y] (Rb : Sylow 3 Y) {K : Subgroup Y} [K.Normal]
    (hperf : Group.IsPerfect K) {F : Type} [Field F] [Finite F]
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F)
    (hC : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y)) {E : Subgroup Y}
    (hE : ∀ x ∈ E, x ^ 3 = 1) :
    E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
  intro x hx b
  set z : Y := b * x * b⁻¹ with hz
  have hz3 : z ^ 3 = 1 := by rw [hz, conj_pow, hE x hx]; simp
  have hz' : ∃ a : ℕ, (modelAct K e z) ^ 3 ^ a ∈ innAut F := ⟨1, by
    rw [show (3 : ℕ) ^ 1 = 3 from rfl, ← map_pow (modelAct K e) z 3, hz3, map_one]
    exact one_mem _⟩
  obtain ⟨r, hr, hrz⟩ := exists_sylow_mul_inn (F := F) Rb (modelAct K e) hz'
  have hw := mem_sup_centralizer_of_modelAct_mem_inn hperf e hrz
  have hw' : r⁻¹ * z ∈ K ⊔ (Rb : Subgroup Y) :=
    sup_le_sup_left hC K |> fun h => h hw
  have : z = r * (r⁻¹ * z) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hr) hw'

@[expose] def hyperFixed {G X : Type} [Group G] [Group X] [MulAction G X] (B : Subgroup G) :
    Set X :=
  {x | (orderOf x).Coprime 3 ∧
    ∃ H : Subgroup G, H ≤ B ∧ H.relIndex B = 3 ∧ ∀ b ∈ H, b • x = x}

theorem closure_hyperFixed_of_conj {X : Type} [Group X] (α : MulAut X)
    (B : Subgroup (MulAut X))
    (h : Subgroup.closure (hyperFixed (X := X) (B.map (MulAut.conj α).toMonoidHom)) = ⊤) :
    Subgroup.closure (hyperFixed (X := X) B) = ⊤ := by
  classical
  have hBα : (B.map (MulAut.conj α).toMonoidHom).map (MulAut.conj α⁻¹).toMonoidHom = B := by
    rw [Subgroup.map_map]
    have : (MulAut.conj α⁻¹).toMonoidHom.comp (MulAut.conj α).toMonoidHom = MonoidHom.id _ := by
      ext b
      simp [MulAut.conj_apply]
    rw [this, Subgroup.map_id]
  have hsub : (fun x => α⁻¹ x) '' hyperFixed (X := X) (B.map (MulAut.conj α).toMonoidHom) ⊆
      hyperFixed (X := X) B := by
    rintro _ ⟨x, ⟨hx3, H, hHB, hHi, hHx⟩, rfl⟩
    refine ⟨?_, H.map (MulAut.conj α⁻¹).toMonoidHom, ?_, ?_, ?_⟩
    · rw [show orderOf (α⁻¹ x) = orderOf x from
        orderOf_injective (α⁻¹ : MulAut X).toMonoidHom (α⁻¹).injective x]
      exact hx3
    · rw [← hBα]
      exact Subgroup.map_mono hHB
    · have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj α⁻¹).toMonoidHom)
        H (B.map (MulAut.conj α).toMonoidHom) (MulAut.conj α⁻¹).injective
      rw [hBα] at this
      rw [this, hHi]
    · rintro _ ⟨h', hh', rfl⟩
      have := hHx h' hh'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.smul_def] at this ⊢
      rw [MulAut.mul_apply, MulAut.mul_apply, inv_inv, MulAut.apply_inv_self, this]
  rw [eq_top_iff]
  have hmap : Subgroup.closure ((fun x => α⁻¹ x) '' hyperFixed (X := X)
        (B.map (MulAut.conj α).toMonoidHom)) = ⊤ := by
    have hm := MonoidHom.map_closure (α⁻¹ : MulAut X).toMonoidHom
      (hyperFixed (X := X) (B.map (MulAut.conj α).toMonoidHom))
    rw [h, Subgroup.map_top_of_surjective _ (α⁻¹).surjective] at hm
    exact hm.symm
  calc (⊤ : Subgroup X) = _ := hmap.symm
    _ ≤ _ := Subgroup.closure_mono hsub

theorem closure_hyperplane_quot_of_model {K E : Subgroup Y} [K.Normal] {M : Type} [Group M]
    (e : K ⧸ Subgroup.center K ≃* M)
    (hB : Subgroup.closure (hyperFixed (X := M) (E.map (modelAct K e))) = ⊤) :
    Subgroup.closure {x : K ⧸ Subgroup.center K | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup Y, H ≤ E ∧ H.relIndex E = 3 ∧
        ∀ y ∈ H, centerQuotientHom K (MulAut.conjNormal y) x = x} = ⊤ := by
  classical
  set SK : Set (K ⧸ Subgroup.center K) := {x | (orderOf x).Coprime 3 ∧
      ∃ H : Subgroup Y, H ≤ E ∧ H.relIndex E = 3 ∧
        ∀ y ∈ H, centerQuotientHom K (MulAut.conjNormal y) x = x} with hSK
  have hsub : hyperFixed (X := M) (E.map (modelAct K e)) ⊆ (fun q => e q) '' SK := by
    rintro x ⟨hx3, HB, hHB, hHi, hHx⟩
    refine ⟨e.symm x, ⟨?_, ?_⟩, by simp⟩
    · rw [show orderOf (e.symm x) = orderOf x from orderOf_injective e.symm.toMonoidHom
        e.symm.injective x]
      exact hx3
    · set ρE : E →* MulAut M := (modelAct K e).comp E.subtype with hρE
      set H₀ : Subgroup E := HB.comap ρE with hH₀
      refine ⟨H₀.map E.subtype, Subgroup.map_subtype_le H₀, ?_, ?_⟩
      · have h1 : (H₀.map E.subtype).relIndex E = H₀.index := by
          rw [Subgroup.relIndex]
          congr 1
          ext b
          simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        rw [h1, hH₀, Subgroup.index_comap]
        have : ρE.range = E.map (modelAct K e) := by
          rw [hρE, MonoidHom.range_comp, Subgroup.range_subtype]
        rw [this]
        exact hHi
      · rintro _ ⟨y', hy', rfl⟩
        have hyB : (modelAct K e) (y' : Y) ∈ HB := hy'
        have := hHx _ hyB
        have h2 : e (centerQuotientHom K (MulAut.conjNormal (y' : Y)) (e.symm x)) = x := this
        exact e.injective (h2.trans (e.apply_symm_apply x).symm)
  have hmap := MonoidHom.map_closure e.toMonoidHom SK
  have htop : Subgroup.map e.toMonoidHom (Subgroup.closure SK) = ⊤ := by
    rw [hmap, eq_top_iff, ← hB]
    exact Subgroup.closure_mono hsub
  rw [eq_top_iff]
  intro q _
  have hq : e q ∈ Subgroup.map e.toMonoidHom (Subgroup.closure SK) := by rw [htop]; trivial
  obtain ⟨q', hq', hqq⟩ := hq
  have : q' = q := e.injective hqq
  rw [← this]
  exact hq'

theorem le_centralizer_of_modelAct_trivial {K E : Subgroup Y} [K.Normal]
    (hperf : Group.IsPerfect K) {M : Type*} [Group M] (e : K ⧸ Subgroup.center K ≃* M)
    (hE : E.map (modelAct K e) = ⊥) : E ≤ Subgroup.centralizer (K : Set Y) := by
  intro y hy
  have h1 : modelAct K e y = 1 := by
    have : modelAct K e y ∈ E.map (modelAct K e) := ⟨y, hy, rfl⟩
    rw [hE] at this
    exact this
  have h2 : centerQuotientHom K (MulAut.conjNormal y) = 1 := by
    have h1' : (MulAut.congr e) (centerQuotientHom K (MulAut.conjNormal y)) = 1 := h1
    exact (MulAut.congr e).injective (h1'.trans (map_one _).symm)
  have h3 : (MulAut.conjNormal y : MulAut K) = 1 :=
    centerQuotientHom_injective K (by rw [h2, map_one])
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have := congrArg (fun φ : MulAut K => ((φ ⟨h, hh⟩ : K) : Y)) h3
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

open CFSG.AGLEmbedding in
theorem false_of_split_field_cube {Rb : Sylow 3 Y} {Y₀ : Subgroup Y} [Finite Y]
    (h : ReducedNongeneration 3 Y Rb Y₀) {K E : Subgroup Y} [K.Normal] (hK : Open.IsQuasisimple K)
    (hC : Subgroup.centralizer (K : Set Y) ≤ (Rb : Subgroup Y)) (hER : E ≤ (Rb : Subgroup Y))
    (hEa : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (hEKC : ¬ E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    {F : Type} [Field F] [Finite F] (h3 : 3 ∣ Nat.card F - 1)
    (e : K ⧸ Subgroup.center K ≃* projectiveSL 3 F)
    (hsplit : ∃ (α : MulAut (projectiveSL 3 F)) (σ : F ≃+* F)
      (A : Subgroup (MulAut (projectiveSL 3 F))), orderOf σ = 3 ∧
        SplitData σ A ((E.map (modelAct K e)).map (MulAut.conj α).toMonoidHom)) : False := by
  classical
  obtain ⟨α, σ, A, hσ, hd⟩ := hsplit
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  have hEp : IsPGroup 3 E := isPGroup_three_of_le hEa.2 le_rfl
  set B : Subgroup (MulAut (projectiveSL 3 F)) := E.map (modelAct K e) with hB
  have hBp : IsPGroup 3 (B.map (MulAut.conj α).toMonoidHom) := by
    rw [hB, Subgroup.map_map]
    exact hEp.map _
  have : Finite (B.map (MulAut.conj α).toMonoidHom) := by
    rw [hB, Subgroup.map_map]
    infer_instance
  obtain ⟨s, hs⟩ := (IsPGroup.iff_card).1 hBp
  have hbot : B ≠ ⊥ := by
    intro hb
    exact hEKC ((le_centralizer_of_modelAct_trivial hperf e hb).trans le_sup_right)
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have : s = 0 := by omega
    rw [this, pow_zero] at hs
    apply hbot
    have h1 : Nat.card (B.map (MulAut.conj α).toMonoidHom) = 1 := hs
    have : B.map (MulAut.conj α).toMonoidHom = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    rw [← Subgroup.map_bot (MulAut.conj α).toMonoidHom] at this
    exact Subgroup.map_injective (MulAut.conj α).injective this
  have hgenα := closure_hyperplane_fixed_eq_top hσ h3 hd hs1 hs
  have hgenB := closure_hyperFixed_of_conj α B hgenα
  have hgenK := closure_hyperplane_quot_of_model (K := K) (E := E) e hgenB
  have hgen := hyperGen_of_generation K E hK hEa hgenK
  exact h.false_of_hyperGen hEa hEc hER (le_normalCore_of_linear Rb hperf e hC hEa.2) hgen

end CFSG.HardMathSupport.Foote.ModuleExclusions
