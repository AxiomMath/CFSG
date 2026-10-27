module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QXInv
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcSRE7Levi
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.Foote5.OddLieCore.Exc
  CFSG.ComponentClassification.CatLeafProof CFSG.ComponentClassification.Burgoyne.E2
  CFSG.LieType.Chevalley.ToralSign
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def CentModel (H : Type*) [Group H] : Prop :=
  ∃ (ι : Type) (S : ι → Subgroup H), (∀ i, IsComponent (S i)) ∧ (∀ i, Even (Nat.card (S i))) ∧
    (∀ g h : H, (∀ i, ∀ s ∈ S i, s * g = g * s) → (∀ i, ∀ s ∈ S i, s * h = h * s) →
      g * h = h * g) ∧
    (∀ g h : H, (∀ i, ∀ s ∈ S i, s * g = g * s) → (∀ i, ∀ s ∈ S i, s * h = h * s) →
      g * g = 1 → h * h = 1 → g ≠ 1 → h ≠ 1 → g = h)

theorem CentModel.of_mulEquiv {H H' : Type*} [Group H] [Group H'] (e : H ≃* H')
    (h : CentModel H') : CentModel H := by
  obtain ⟨ι, S, hS, hSe, hc, hi⟩ := h
  have hlift : ∀ g : H, (∀ i, ∀ s ∈ (S i).map e.symm.toMonoidHom, s * g = g * s) →
      ∀ i, ∀ s ∈ S i, s * e g = e g * s := by
    intro g hg i s hs
    have h1 := congrArg e (hg i (e.symm s) ⟨s, hs, rfl⟩)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
  refine ⟨ι, fun i => (S i).map e.symm.toMonoidHom,
    fun i => LocalCores.isComponent_map_mulEquiv e.symm (hS i), fun i => ?_,
    fun g h hg hh => e.injective ?_, fun g h hg hh hg2 hh2 hg1 hh1 => e.injective ?_⟩
  · rw [← Nat.card_congr ((S i).equivMapOfInjective _ e.symm.injective).toEquiv]
    exact hSe i
  · rw [map_mul, map_mul]
    exact hc _ _ (hlift g hg) (hlift h hh)
  · refine hi _ _ (hlift g hg) (hlift h hh) ?_ ?_ ?_ ?_
    · rw [← map_mul, hg2, map_one]
    · rw [← map_mul, hh2, map_one]
    · exact fun h1 => hg1 (e.injective (h1.trans (map_one e).symm))
    · exact fun h1 => hh1 (e.injective (h1.trans (map_one e).symm))

theorem evenCent_of_centModel {X : Type} [Group X] {z : X} (hz : orderOf z = 2) {H : Type*}
    [Group H] (Θ : centralizer ({z} : Set X) ≃* H) (h : CentModel H) :
    EvenCentComm X z ∧ EvenCentInv X z := by
  obtain ⟨ι, S, hS, hSe, hc, hi⟩ := h
  exact evenCent_of_mulEquiv hz Θ S hS hSe hc hi

theorem fixedSubgroup_mulConj_eq_map {G : Type*} [Group G] (ψ β : MulAut G) :
    fixedSubgroup (ψ * β * ψ⁻¹) = (fixedSubgroup β).map ψ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    have hy' : ψ (β (ψ⁻¹ y)) = y := hy
    refine ⟨ψ⁻¹ y, ?_, ?_⟩
    · change β (ψ⁻¹ y) = ψ⁻¹ y
      apply ψ.injective
      rw [hy', MulAut.apply_inv_self]
    · change ψ (ψ⁻¹ y) = y
      exact MulAut.apply_inv_self G ψ y
  · rintro ⟨x, hx, rfl⟩
    have hx' : β x = x := hx
    change ψ (β (ψ⁻¹ (ψ x))) = ψ x
    rw [MulAut.inv_apply_self, hx']

@[expose] def fixedSubgroupMulConjEquiv {G : Type*} [Group G] (ψ β : MulAut G) :
    fixedSubgroup β ≃* fixedSubgroup (ψ * β * ψ⁻¹) :=
  ((fixedSubgroup β).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (fixedSubgroup_mulConj_eq_map ψ β).symm)

variable {τ : Tag} {K : Type} [Field K]

theorem centModel_toral_single
    [Finite K] (hK2 : ringChar K ≠ 2) (hK5 : 5 ≤ Nat.card K)
    {c : Fin τ.rank → Kˣ} (hc : ∀ i, c i = 1 ∨ c i = -1) {i : Fin τ.rank}
    (hci : ∀ j, j ≠ i → c j = 1)
    (hW : ∀ w ∈ rootCharStabilizer c, (∀ β ∈ posRoots (rootCharKernel c), w • β = β) → w = 1) :
    CentModel (toralCentralizer τ K c) := by
  have : Finite (ModGL τ K) := finite_modGL
  exact ⟨KernelComponent (maskChar (signTupleBits c)),
    fun ψ => (componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
      (toralCentralizer τ K c),
    fun ψ => isComponent_componentRootSpan_toral hK2 hK5 hc ψ,
    fun ψ => Burgoyne.even_card_of_isQuasisimple
      (isComponent_componentRootSpan_toral hK2 hK5 hc ψ).1,
    toral_rootFactors_centComm hK2 hK5 hc hW, toral_rootFactors_centInv hK2 hK5 hc hW hci⟩

theorem centModel_fixedSubgroup_rootDiagAut
    {a : Fin τ.rank → Kˣ} (h : CentModel (toralCentralizer τ K a)) :
    CentModel (fixedSubgroup (rootDiagAut τ K a)) := by
  have hmap : (fixedSubgroup (rootDiagAut τ K a)).map (adjointGroup τ K).subtype =
      toralCentralizer τ K a := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_fixedSubgroup_rootDiagAut.1 hx
    · intro hy
      exact ⟨⟨y, (Subgroup.mem_inf.1 hy).1⟩, mem_fixedSubgroup_rootDiagAut.2 hy, rfl⟩
  exact h.of_mulEquiv (((fixedSubgroup (rootDiagAut τ K a)).equivMapOfInjective _
    Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap))

theorem rootChar_bitsTuple_eq_one {b : Fin τ.rank → Bool} {v : Fin τ.rank → ℤ}
    (h : ∀ j, b j = true → Even (v j)) : rootChar (bitsTuple (K := K) b) v = 1 := by
  show ∏ j, bitsTuple (K := K) b j ^ v j = 1
  refine Finset.prod_eq_one fun j _ => ?_
  cases hb : b j
  · simp [bitsTuple, hb]
  · rw [show bitsTuple (K := K) b j = -1 by simp [bitsTuple, hb]]
    exact (h j hb).neg_one_zpow

theorem isComponent_componentRootSpan_toral_of_ncard
    (hK2 : ringChar K ≠ 2) {c : Fin τ.rank → Kˣ}
    (hc : ∀ i, c i = 1 ∨ c i = -1) (ψ : KernelComponent (maskChar (signTupleBits c)))
    (hψ : 2 < (componentRoots (maskChar (signTupleBits c)) ψ).ncard) :
    IsComponent ((componentRootSpan K (maskChar (signTupleBits c)) ψ).subgroupOf
      (toralCentralizer τ K c)) := by
  have hkerχ : rootCharKernel c = kernelRoots (maskChar (signTupleBits c)) :=
    rootCharKernel_eq_kernelRoots hK2 hc
  obtain ⟨-, -, -, hnorm, -, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K (maskChar (signTupleBits c))
  have hΨS : componentRootSpan K (maskChar (signTupleBits c)) ψ ≤
      rootSpan τ K (rootCharKernel c) := by
    rw [hkerχ]
    exact (hnorm ψ).1
  have hEC := componentRootSpan_le_toralCentralizer hK2 hc ψ
  refine ⟨(isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hEC)).2
    ((odd_sign_root_component_quasisimple τ K _ ψ).2.2 hK2 hψ), ?_⟩
  refine isSubnormal_subgroupOf_of_conj (A := rootSpan τ K (rootCharKernel c)) hΨS
    (fun t ht a ha => (Subgroup.mem_normalizer_iff.1
      (toralCentralizer_le_normalizer_rootSpan c ht) a).1 ha) fun a ha _ e he => ?_
  have ha' : a ∈ rootSpan τ K (kernelRoots (maskChar (signTupleBits c))) := hkerχ ▸ ha
  exact (Subgroup.normal_subgroupOf_iff (hnorm ψ).1).1 (hnorm ψ).2 e a he ha'

theorem e7_rootDiagUnit_of_commute_rootSL2
    (p : ℕ) [Fact p.Prime] [Finite K] (hK3 : 3 ≤ Nat.card K)
    {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharP L p]
    {g : ModGL .E7 K} (hgG : g ∈ adjointGroup .E7 K) (Γ : List ((Fin (Tag.rank .E7) → ℤ) × ℤ))
    (hΓ : ∀ y ∈ Γ, IsRoot .E7 y.1) (B : ℕ)
    (hreg : ∀ α : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < B)
    (hcomm : ∀ y ∈ Γ, ∀ A : SL2 K, g * rootSL2 .E7 K y.1 A = rootSL2 .E7 K y.1 A * g) :
    ∃ b : Fin (Tag.rank .E7) → Lˣ, baseChangeGL (algebraMap K L) g = rootDiagUnit .E7 b ∧
      ∀ y ∈ Γ, rootChar b y.1 = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hK3' : 3 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hzG : baseChangeGL (algebraMap K L) g ∈ adjointGroup .E7 L :=
    LieType.Chevalley.baseChangeGL_mem_adjointGroup (algebraMap K L) hgG
  have hL : ∀ y ∈ Γ, ∀ A : SL2 L, baseChangeGL (algebraMap K L) g * rootSL2 .E7 L y.1 A =
      rootSL2 .E7 L y.1 A * baseChangeGL (algebraMap K L) g := by
    intro y hy
    refine SRE7.commute_rootSL2_of_field (algebraMap K L) hK3' _ fun B => ?_
    have h := congrArg (baseChangeGL (algebraMap K L)) (hcomm y hy B)
    rwa [map_mul, map_mul, RankThree.Chevalley.baseChangeGL_rootSL2_of_field] at h
  have hT := TwE7.mem_torusGroup_of_commute_rootTorus p (Or.inr (Or.inl rfl)) hzG Γ hΓ
    (fun y hy s => hL y hy (HSL s)) B hreg
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  refine ⟨b, hb, fun y hy => TwE7.rootChar_eq_one_of_commute (hΓ y hy) ?_⟩
  rw [← hb]
  exact hL y hy (uSL 1)

@[expose] def p51qE7Gamma1 : List ((Fin (Tag.rank .E7) → ℤ) × ℤ) :=
  [(![2, 2, 3, 4, 3, 2, 1], 17), (![0, 1, 0, 0, 0, 0, 0], 15), (![0, 0, 1, 0, 0, 0, 0], 15),
    (![0, 0, 0, 1, 0, 0, 0], 28), (![0, 0, 0, 0, 1, 0, 0], 24), (![0, 0, 0, 0, 0, 1, 0], 18),
    (![0, 0, 0, 0, 0, 0, 1], 10)]

theorem p51qE7Gamma1_reg : ∀ α ∈ rootFinset .E7,
    (∑ j, regCoweight p51qE7Gamma1 j * α j) ≠ 0 ∧
      (∑ j, regCoweight p51qE7Gamma1 j * α j).natAbs < 35 := by
  decide +kernel

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
