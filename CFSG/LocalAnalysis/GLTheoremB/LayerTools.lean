module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.GLTheoremB.GammaBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Subnormal

variable {G : Type*} [Group G]

theorem isSubnormal_trans' {A B C : Subgroup G} (h1 : IsSubnormal A B) (h2 : IsSubnormal B C) :
    IsSubnormal A C :=
  h1.trans h2

theorem isSubnormal_inf {A B : Subgroup G} (h : IsSubnormal A B) (L : Subgroup G) :
    IsSubnormal (A ⊓ L) (B ⊓ L) :=
  h.inf L

theorem isSubnormal_of_le_of_le {A B L : Subgroup G} (h : IsSubnormal A B) (hAL : A ≤ L)
    (hLB : L ≤ B) : IsSubnormal A L := by
  have := isSubnormal_inf h L
  rwa [inf_eq_left.2 hAL, inf_eq_right.2 hLB] at this

end Subnormal

section Conj

variable {Q : Type*} [Group Q]

theorem gLBConj_centralizer (g : Q) (K : Subgroup Q) :
    GLBConj g (Subgroup.centralizer (K : Set Q)) = Subgroup.centralizer (GLBConj g K : Set Q) := by
  ext x
  rw [mem_gLBConj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have hz' := h _ (mem_gLBConj.1 hz)
    have : g * (z * x) * g⁻¹ = g * (x * z) * g⁻¹ := by
      calc g * (z * x) * g⁻¹ = (g * z * g⁻¹) * (g * x * g⁻¹) := by group
        _ = (g * x * g⁻¹) * (g * z * g⁻¹) := hz'
        _ = g * (x * z) * g⁻¹ := by group
    simpa using this
  · intro h k hk
    have hz : g⁻¹ * k * g ∈ GLBConj g K := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hk
    have h1 := h _ hz
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * k := by group

theorem le_of_le_iSup_conj {F : Subgroup Q → Subgroup Q}
    (hF : ∀ g K, GLBConj g (F K) = F (GLBConj g K)) {Y S K : Subgroup Q}
    (hY : Y ≤ ⨆ y ∈ Y, GLBConj y S) (h : ∀ y ∈ Y, S ≤ F (GLBConj y⁻¹ K)) : Y ≤ F K := by
  refine hY.trans (iSup₂_le fun y hy => ?_)
  calc GLBConj y S ≤ GLBConj y (F (GLBConj y⁻¹ K)) := gLBConj_mono y (h y hy)
    _ = F (GLBConj y (GLBConj y⁻¹ K)) := hF _ _
    _ = F K := by rw [gLBConj_gLBConj_inv]

theorem gLBConj_normalizer (g : Q) (K : Subgroup Q) :
    GLBConj g (Subgroup.normalizer (K : Set Q)) = Subgroup.normalizer (GLBConj g K : Set Q) :=
  (normalizer_gLBConj g K).symm

theorem isComponentOf_gLBConj {K : Subgroup Q} (h : IsComponentOf K ⊤) (g : Q) :
    IsComponentOf (GLBConj g K) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) K).2 h

end Conj

section Layer

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem isSubnormal_of_normal {F : Subgroup Q} (hF : F.Normal) : IsSubnormal F ⊤ :=
  IsSubnormal.step le_top (hF.subgroupOf ⊤) (IsSubnormal.refl ⊤)

theorem mem_pCore_of_centralizes {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p Q = ⊥) {x : Q}
    (hF : x ∈ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q))
    (hK : ∀ K : Subgroup Q, IsComponentOf K ⊤ → x ∈ Subgroup.centralizer (K : Set Q)) :
    x ∈ CFSG.Open.pCore p Q := by
  have : Fact p.Prime := ⟨hp⟩
  set S := Subgroup.zpowers x with hS
  have h1 : S ≤ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q) := Subgroup.zpowers_le.2 hF
  have h2 : ∀ K : Subgroup Q, IsComponentOf K ⊤ → S ≤ Subgroup.centralizer (K : Set Q) :=
    fun K hKc => Subgroup.zpowers_le.2 (hK K hKc)
  have hF' : CFSG.fittingSubgroup Q = CFSG.pCore p Q := CFSG.Fitting_eq_pcore Q p hcore
  have hFle : CFSG.fittingSubgroup Q ≤ Subgroup.centralizer (S : Set Q) := by
    rw [hF']
    exact Subgroup.le_centralizer_iff.1 h1
  have hLle : CFSG.layer Q ≤ Subgroup.centralizer (S : Set Q) :=
    sSup_le fun K hK => Subgroup.le_centralizer_iff.1
      (h2 K ((CFSG.isComponent_iff_open K).1 hK))
  have hstar : CFSG.generalizedFitting Q ≤ Subgroup.centralizer (S : Set Q) := sup_le hFle hLle
  have hcent : Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q) ≤
      CFSG.fittingSubgroup Q := by
    have := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting Q
    rw [← CFSG.generalizedFitting_eq_componentClassification] at this
    exact this
  have hSF : S ≤ CFSG.pCore p Q := hF' ▸ le_trans (Subgroup.le_centralizer_iff.2 hstar) hcent
  have := hSF (Subgroup.mem_zpowers x)
  assumption

theorem isSubnormal_iSup_components (𝒜 : Set (Subgroup Q))
    (h𝒜 : ∀ K ∈ 𝒜, IsComponentOf K ⊤) : IsSubnormal (⨆ K ∈ 𝒜, K) ⊤ := by
  set A : Subgroup Q := ⨆ K ∈ 𝒜, K with hA
  set E := CFSG.ComponentClassification.Layer.subgroup Q with hE
  have hAE : A ≤ E :=
    iSup₂_le fun K hK => CFSG.ComponentClassification.Layer.component_le (h𝒜 K hK)
  have hEN : E ≤ Subgroup.normalizer (A : Set Q) := by
    refine sSup_le fun K hK => ?_
    by_cases hK𝒜 : K ∈ 𝒜
    · exact (le_iSup₂_of_le K hK𝒜 le_rfl : K ≤ A).trans Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (A : Set Q))
      refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun K' hK' => ?_)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K (h𝒜 K' hK') hK
          (fun h => hK𝒜 (h ▸ hK')))
  have hEA : IsSubnormal A E :=
    IsSubnormal.step hAE ((Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEN)
      (IsSubnormal.refl E)
  exact isSubnormal_trans' hEA (isSubnormal_of_normal (CFSG.ComponentClassification.Layer.normal Q))

omit [Finite Q] in
theorem le_of_perfect_le_sup_centralizer {A B' Y : Subgroup Q}
    (hAB : A ≤ Subgroup.centralizer (B' : Set Q)) (hYB : Y ≤ Subgroup.centralizer (B' : Set Q))
    (hY : ⁅Y, Y⁆ = Y) (h : Y ≤ A ⊔ B') : Y ≤ A := by
  calc Y = ⁅Y, Y⁆ := hY.symm
    _ ≤ A := by
      refine Subgroup.commutator_le.2 fun y₁ hy₁ y₂ hy₂ => ?_
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup hAB (h hy₁)
      obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup hAB (h hy₂)
      have hc1 : b₁ * a₂ = a₂ * b₁ := (Subgroup.mem_centralizer_iff.1 (hAB ha₂)) b₁ hb₁
      have hc2 : b₂ * a₁ = a₁ * b₂ := (Subgroup.mem_centralizer_iff.1 (hAB ha₁)) b₂ hb₂
      have hc3 : b₁ * b₂ = b₂ * b₁ := by
        have h3 := (Subgroup.mem_centralizer_iff.1 (hYB hy₁)) b₂ hb₂
        have h4 : a₁ * (b₂ * b₁) = a₁ * (b₁ * b₂) := by
          calc a₁ * (b₂ * b₁) = (a₁ * b₂) * b₁ := by group
            _ = (b₂ * a₁) * b₁ := by rw [hc2]
            _ = b₂ * (a₁ * b₁) := by group
            _ = (a₁ * b₁) * b₂ := h3
            _ = a₁ * (b₁ * b₂) := by group
        exact (mul_left_cancel h4).symm
      have e2 : b₂ * a₁⁻¹ = a₁⁻¹ * b₂ := by
        calc b₂ * a₁⁻¹ = a₁⁻¹ * (a₁ * b₂) * a₁⁻¹ := by group
          _ = a₁⁻¹ * (b₂ * a₁) * a₁⁻¹ := by rw [hc2]
          _ = a₁⁻¹ * b₂ := by group
      have e3 : b₁ * b₂ * b₁⁻¹ = b₂ := by rw [hc3]; group
      have key : a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
        calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
            = a₁ * (b₁ * a₂) * (b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
          _ = a₁ * (a₂ * b₁) * (b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [hc1]
          _ = a₁ * a₂ * (b₁ * b₂ * b₁⁻¹) * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
          _ = a₁ * a₂ * b₂ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [e3]
          _ = a₁ * a₂ * (b₂ * a₁⁻¹) * b₂⁻¹ * a₂⁻¹ := by group
          _ = a₁ * a₂ * (a₁⁻¹ * b₂) * b₂⁻¹ * a₂⁻¹ := by rw [e2]
          _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group
      rw [commutatorElement_def, key]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha₁ ha₂) (A.inv_mem ha₁)) (A.inv_mem ha₂)

theorem le_layer_of_perfect {p : ℕ} (hp : p.Prime) (hcore : GLAPPrimeCore p Q = ⊥)
    (hOut : ∀ K : Subgroup Q, IsComponentOf K ⊤ → Group.IsSolvable (Outer ↥K))
    {Y : Subgroup Q} (hY : ⁅Y, Y⁆ = Y)
    (hF : Y ≤ Subgroup.centralizer (CFSG.Open.pCore p Q : Set Q))
    (hN : ∀ K : Subgroup Q, IsComponentOf K ⊤ → Y ≤ Subgroup.normalizer (K : Set Q)) :
    Y ≤ CFSG.ComponentClassification.Layer.subgroup Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hYp : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.2 hY
  set E := CFSG.ComponentClassification.Layer.subgroup Q with hE
  set F := CFSG.Open.pCore p Q with hFdef
  have hFn : F.Normal := CFSG.LieType.BorelTits.pCore_normal p
  have hFp : IsPGroup p F := CFSG.LieType.BorelTits.pCore_isPGroup p
  have hFnil : Group.IsNilpotent ↥F := hFp.isNilpotent
  have key : ∀ T : Finset (Subgroup Q), (∀ K ∈ T, IsComponentOf K ⊤) →
      ∀ y ∈ Y, ∃ e ∈ ⨆ K ∈ T, K, ∀ K ∈ T, y * e⁻¹ ∈ Subgroup.centralizer (K : Set Q) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _ y _
      exact ⟨1, one_mem _, by simp⟩
    | insert K₀ T hK₀T ih =>
      intro hcomp y hy
      have hK₀ : IsComponentOf K₀ ⊤ := hcomp K₀ (Finset.mem_insert_self _ _)
      have hT : ∀ K ∈ T, IsComponentOf K ⊤ := fun K hK => hcomp K (Finset.mem_insert_of_mem hK)
      obtain ⟨e, he, hecent⟩ := ih hT y hy
      have hcomm : ∀ K ∈ T, K₀ ≤ Subgroup.centralizer (K : Set Q) := fun K hK =>
        Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne K₀ K hK₀ (hT K hK)
            (fun h => hK₀T (h ▸ hK)))
      have hET : (⨆ K ∈ T, K) ≤ Subgroup.centralizer (K₀ : Set Q) :=
        iSup₂_le fun K hK => Subgroup.le_centralizer_iff.1 (hcomm K hK)
      have hSolv : Group.IsSolvable (Outer ↥K₀) := hOut K₀ hK₀
      let act : ↥Y →* MulAut ↥K₀ :=
        (Subgroup.normalizerMonoidHom K₀).comp (Subgroup.inclusion (hN K₀ hK₀))
      obtain ⟨κ, hκ⟩ :=
        CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner act ⟨y, hy⟩
      have hκ' : ∀ z ∈ K₀, y * z * y⁻¹ = (κ : Q) * z * (κ : Q)⁻¹ := by
        intro z hz
        have h1 := congrArg (fun φ : MulAut ↥K₀ => ((φ ⟨z, hz⟩ : ↥K₀) : Q)) hκ
        exact h1
      have hez : ∀ w ∈ K₀, w * e = e * w := fun w hw =>
        (Subgroup.mem_centralizer_iff.1 (hET he)) w hw
      have hκe : (κ : Q) * e = e * (κ : Q) := hez κ κ.2
      refine ⟨e * κ, ?_, ?_⟩
      · rw [Finset.iSup_insert]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right he) (Subgroup.mem_sup_left κ.2)
      · intro K hK
        rcases Finset.mem_insert.1 hK with rfl | hKT
        · rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hw' : (κ : Q)⁻¹ * z * (κ : Q) ∈ K := by
            exact K.mul_mem (K.mul_mem (K.inv_mem κ.2) hz) κ.2
          have h3 : y * ((κ : Q)⁻¹ * z * (κ : Q)) * y⁻¹ = z := by
            rw [hκ' _ hw']
            group
          have hez' : e⁻¹ * z = z * e⁻¹ := by
            have := hez z hz
            calc e⁻¹ * z = e⁻¹ * (z * e) * e⁻¹ := by group
              _ = e⁻¹ * (e * z) * e⁻¹ := by rw [this]
              _ = z * e⁻¹ := by group
          calc z * (y * (e * κ)⁻¹)
              = (y * ((κ : Q)⁻¹ * z * (κ : Q)) * y⁻¹) * (y * (κ : Q)⁻¹ * e⁻¹) := by
                rw [h3]; group
            _ = y * (κ : Q)⁻¹ * (z * e⁻¹) := by group
            _ = y * (κ : Q)⁻¹ * (e⁻¹ * z) := by rw [hez']
            _ = (y * (e * κ)⁻¹) * z := by group
        · have hκC : (κ : Q) ∈ Subgroup.centralizer (K : Set Q) := hcomm K hKT κ.2
          have : y * (e * (κ : Q))⁻¹ = (y * e⁻¹) * (κ : Q)⁻¹ := by
            rw [show e * (κ : Q) = (κ : Q) * e from hκe.symm, mul_inv_rev, mul_assoc]
          rw [this]
          exact Subgroup.mul_mem _ (hecent K hKT) (Subgroup.inv_mem _ hκC)
  have hcompsFin : {K : Subgroup Q | IsComponentOf K ⊤}.Finite := Set.toFinite _
  set T := hcompsFin.toFinset with hT
  have hTmem : ∀ K, K ∈ T ↔ IsComponentOf K ⊤ := fun K => hcompsFin.mem_toFinset
  have hEF : ⁅E, F⁆ = ⊥ := CFSG.ComponentClassification.Layer.commutes_with_solvable_subnormal
    F (isSubnormal_of_normal hFn)
  have hEcF : E ≤ Subgroup.centralizer (F : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hEF
  have hsup : Y ≤ F ⊔ E := by
    intro y hy
    obtain ⟨e, he, hecent⟩ := key T (fun K hK => (hTmem K).1 hK) y hy
    have heE : e ∈ E := (iSup₂_le fun K hK =>
      CFSG.ComponentClassification.Layer.component_le ((hTmem K).1 hK)) he
    have hyF : y * e⁻¹ ∈ Subgroup.centralizer (F : Set Q) :=
      Subgroup.mul_mem _ (hF hy) (Subgroup.inv_mem _ (hEcF heE))
    have hmem : y * e⁻¹ ∈ F :=
      mem_pCore_of_centralizes hp hcore hyF fun K hK => hecent K ((hTmem K).2 hK)
    have : y = (y * e⁻¹) * e := by simp
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right heE)
  have : Group.IsSolvable (QuotientGroup.mk' F).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  have : E.Normal := CFSG.ComponentClassification.Layer.normal Q
  refine CFSG.ComponentClassification.SolvableKernelContainment.perfect_containment
    (QuotientGroup.mk' F) Y E ?_
  have h1 := Subgroup.map_mono (f := QuotientGroup.mk' F) hsup
  rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff F).mpr (by rw [QuotientGroup.ker_mk']),
    bot_sup_eq] at h1

theorem le_layer_diff_of_perfect (𝒦 : Set (Subgroup Q)) (h𝒦 : ∀ K ∈ 𝒦, IsComponentOf K ⊤)
    {Y : Subgroup Q} (hY : ⁅Y, Y⁆ = Y) (hYE : Y ≤ CFSG.ComponentClassification.Layer.subgroup Q)
    (hYK : ∀ K ∈ 𝒦, Y ≤ Subgroup.centralizer (K : Set Q)) :
    Y ≤ ⨆ K ∈ {K : Subgroup Q | IsComponentOf K ⊤ ∧ K ∉ 𝒦}, K := by
  set A : Subgroup Q := ⨆ K ∈ {K : Subgroup Q | IsComponentOf K ⊤ ∧ K ∉ 𝒦}, K with hA
  set B' : Subgroup Q := ⨆ K ∈ 𝒦, K with hB'
  have hAB : A ≤ Subgroup.centralizer (B' : Set Q) := by
    refine iSup₂_le fun K hK => Subgroup.le_centralizer_iff.2 (iSup₂_le fun K' hK' => ?_)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K' K (h𝒦 K' hK') hK.1
        (fun h => hK.2 (h ▸ hK')))
  have hYB : Y ≤ Subgroup.centralizer (B' : Set Q) :=
    Subgroup.le_centralizer_iff.2 (iSup₂_le fun K hK => Subgroup.le_centralizer_iff.1 (hYK K hK))
  have hE : CFSG.ComponentClassification.Layer.subgroup Q ≤ A ⊔ B' := by
    refine sSup_le fun K hK => ?_
    by_cases hK𝒦 : K ∈ 𝒦
    · exact le_trans (le_iSup₂_of_le K hK𝒦 (le_refl K) : K ≤ B') le_sup_right
    · exact le_trans (le_iSup₂_of_le K ⟨hK, hK𝒦⟩ (le_refl K) : K ≤ A) le_sup_left
  exact le_of_perfect_le_sup_centralizer hAB hYB hY (hYE.trans hE)

end Layer

end CFSG.LocalAnalysis.GLTheoremB
