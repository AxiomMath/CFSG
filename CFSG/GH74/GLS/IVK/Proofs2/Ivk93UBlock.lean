module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorULinear
import CFSG.LocalAnalysis.ComponentClassification.Sp4RecSympLift
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecPGL

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.Sp4Rec
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
  CFSG.ComponentClassification.OddClassSelector
open scoped MatrixGroups

section Lifts

theorem ivk93_pComponent_lifts_map {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hcentral : f.ker ≤ center X) [f.range.Normal]
    [Group.IsSolvable (Y ⧸ f.range)] {L₁ L₂ : Subgroup Y} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) :
    ∃ M₁ M₂ : Subgroup X, IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ ∧
      M₁.map f = L₁ ∧ M₂.map f = L₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : f.rangeRestrict.ker ≤ center X := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hcentral
  obtain ⟨hle₁, hr₁⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₁ h₁
  obtain ⟨hle₂, hr₂⟩ :=
    CatalogueBFixedCentralQuotient.pComponent_in_normal_of_solvable_quotient 2 f.range L₂ h₂
  obtain ⟨M₁, hM₁, hm₁, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₁
  obtain ⟨M₂, hM₂, hm₂, -⟩ := CatalogueBCentralQuotient.pComponent_exists_lift 2
    f.rangeRestrict f.rangeRestrict_surjective hc _ hr₂
  have hmap : ∀ (L : Subgroup Y) (N : Subgroup X), L ≤ f.range →
      N.map f.rangeRestrict = L.subgroupOf f.range → N.map f = L := by
    intro L N hL hN
    have h1 : (N.map f.rangeRestrict).map f.range.subtype = N.map f := by
      rw [map_map]
      rfl
    rw [← h1, hN, map_subgroupOf_eq_of_le hL]
  refine ⟨M₁, M₂, hM₁, hM₂, fun h => hne ?_, hmap L₁ M₁ hle₁ hm₁, hmap L₂ M₂ hle₂ hm₂⟩
  rw [h, hm₂] at hm₁
  have h12 := subgroupOf_inj.mp hm₁
  rw [inf_of_le_left hle₂, inf_of_le_left hle₁] at h12
  exact h12.symm

theorem ivk93_linGL_pComponent_eq {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (hW : 1 ≤ finrank K W)
    {J₁ J₂ : Subgroup (LinearMap.GeneralLinearGroup K W)} (h₁ : IsPComponent 2 J₁)
    (h₂ : IsPComponent 2 J₂) : J₁ = J₂ :=
  CFSG.ComponentClassification.Sp4Rec.linGL_pComponent_eq hW h₁ h₂

theorem ivk93_isComponent_of_pComponent {X : Type*} [Group X] {L : Subgroup X}
    (hL : IsPComponent 2 L) (hq : CFSG.IsQuasisimple ↥L) : CFSG.IsComponent L := by
  obtain ⟨K, -, hsub, -⟩ := hL
  exact ⟨hq, hsub⟩

end Lifts

section Quaternion

variable {E : Type} [Field E] [Finite E] {W : Type} [AddCommGroup W] [Module E W]
  [FiniteDimensional E W] {sigma : E ≃+* E}

theorem ivk93_unitary_component_quaternion {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 3 ≤ finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    (hab : ∃ a b : E, sigma a = -a ∧ sigma b = -b ∧ a ^ 2 + b ^ 2 = -1)
    {Y : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hY : CFSG.IsComponent Y)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) :
    ∃ φ : QuaternionGroup 2 →* ↥X ⧸ center ↥X, Function.Injective φ := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP E ℓ := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hE
  have hE2 : (2 : E) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq E ℓ]; exact hℓ2)
  obtain ⟨eX⟩ := nonempty_quotient_psu hℓ hℓ2 he hE hW h hsym hnd hsigma hne hsig hY σ hσs hσk
  obtain ⟨a, b, ha, hb, hab'⟩ := hab
  have hsigU : sigma = CFSG.LieType.BorelTits.unitaryInvolution E ℓ e :=
    RingEquiv.ext fun z => by rw [hsig, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hSU : CFSG.LieType.Universal.Unitary.SUid sigma (finrank E W) =
      StatedSU (finrank E W) (ℓ ^ e) E := by
    rw [hsigU]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
  obtain ⟨φ, hφ⟩ := exists_quaternion_statedProj hE2 sigma hW hSU ha hb hab'
  exact ⟨eX.symm.toMonoidHom.comp φ, eX.symm.injective.comp hφ⟩

end Quaternion

section Block

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

@[expose] def Ivk93UnitaryBlock (p f : ℕ) {G : Type} [Group G] (M : Subgroup G) (d : ℕ) : Prop :=
  CFSG.IsQuasisimple ↥M ∧
    (d = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = p ^ f ∧
      Nonempty (SL(2, k) ≃* ↥M)) ∧
    (3 ≤ d → ∃ φ : QuaternionGroup 2 →* ↥M ⧸ center ↥M, Function.Injective φ)

theorem ivk93_su_half_block (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {W F : Submodule E V}
    (hWs : (B.domRestrict₁₂ W W).IsSymm) (hWl : (B.domRestrict₁₂ W W).SeparatingLeft)
    (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    {Y : Type} [Group Y] (ι : Y →* sesqUnitaryGroup B) (hιi : Function.Injective ι)
    (hYF : ∀ y : Y, ∀ w ∈ F, unitaryOp (ι y) w = w)
    (ρ : Y →* sesqUnitaryGroup (B.domRestrict₁₂ W W)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range)
    {X' : Type} [Group X'] {X : Subgroup X'} (σ : Y →* X) (hσs : Function.Surjective σ)
    (hσk : σ.ker ≤ center Y) (hker : ∀ y : Y, σ y = 1 → ι y ∈ sesqNormOneScalars h B) :
    2 ≤ finrank E W ∧
      (finrank E W = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = p ^ f ∧ Nonempty (SL(2, k) ≃* ↥X)) ∧
      (3 ≤ finrank E W → ∃ φ : QuaternionGroup 2 →* ↥X ⧸ center ↥X, Function.Injective φ) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  obtain ⟨hsigma, hne, hk0⟩ := CatalogueBUnitaryTwo.unitaryFieldConjugation_data p f h.card_eq_sq
  have hsig := CatalogueBUnitaryTwo.unitaryFieldConjugation_apply p f h.card_eq_sq
  have hnd := CatalogueBUnitaryB.nondegenerate_of_isSymm hWs hWl
  obtain ⟨hdim2, h23, hρeq⟩ := eq_unitarySpecial_of_isComponent h hp hW1 hWs hWl hρc
  let eρ := MonoidHom.ofInjective hρi
  refine ⟨hdim2, fun hd2 => ?_, fun h3 => ?_⟩
  · have hq3 : p ^ f ≠ 3 := fun h3' => h23 (by rw [hd2, h3'])
    have hσi : Function.Injective σ := by
      rw [injective_iff_map_eq_one]
      intro y hy
      exact hιi (by rw [map_one]; exact eq_one_of_mem_sesqNormOneScalars (hker y hy) hF0 (hYF y))
    obtain ⟨eU⟩ := nonempty_unitarySpecial_equiv h (B.domRestrict₁₂ W W)
    obtain ⟨hkp, -, -, eSL, -⟩ := CatalogueBUnitaryTwo.unitary_field_two_special_linear_isomorphism
      p f h.card_eq_sq (B.domRestrict₁₂ W W) hWs hnd hd2
    exact ⟨hq3, _, inferInstance, inferInstance, hkp,
      ⟨((MulEquiv.ofBijective σ ⟨hσi, hσs⟩).symm.trans
        (eρ.trans ((MulEquiv.subgroupCongr hρeq).trans (eU.trans eSL)))).symm⟩⟩
  · obtain ⟨F⟩ : Nonempty (↥(sesqUnitaryGroup (B.domRestrict₁₂ W W)) ≃*
        ↥(CatalogueBUnitaryIsometry.isometryGroup
          (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq)
          (B.domRestrict₁₂ W W))) :=
      ⟨CatalogueBUnitaryB.sesqUnitaryIsometryEquiv h (B.domRestrict₁₂ W W)⟩
    obtain ⟨e2⟩ : Nonempty (↥ρ.range ≃* ↥(ρ.range.map F.toMonoidHom)) :=
      ⟨ρ.range.equivMapOfInjective F.toMonoidHom F.injective⟩
    have hφi : Function.Injective (eρ.symm.toMonoidHom.comp e2.symm.toMonoidHom) :=
      eρ.symm.injective.comp e2.symm.injective
    exact ivk93_unitary_component_quaternion
      (sigma := CatalogueBUnitaryTwo.unitaryFieldConjugation p f h.card_eq_sq) h.prime hp h.one_le
      h.card_eq_sq h3 (B.domRestrict₁₂ W W) hWs hnd hsigma hne hsig
      (exists_antifixed_sq_add_sq h hp) (isComponent_map_of_isComponent F hρc)
      (σ.comp (eρ.symm.toMonoidHom.comp e2.symm.toMonoidHom))
      (hσs.comp (eρ.symm.surjective.comp e2.symm.surjective))
      (CFSG.ComponentClassification.OddClassSelector.ker_comp_le_center _ hφi σ hσk)

theorem ivk93_block_of_half (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    {B : V →ₛₗ[h.bar] V →ₗ[E] E} {A : sesqUnitaryGroup B} {W F : Submodule E V}
    (hWs : (B.domRestrict₁₂ W W).IsSymm) (hWl : (B.domRestrict₁₂ W W).SeparatingLeft)
    (hW1 : 1 ≤ finrank E W) (hF0 : F ≠ ⊥)
    (e : centralizer ({A} : Set (sesqUnitaryGroup B)) ≃*
      sesqUnitaryGroup (B.domRestrict₁₂ W W) × sesqUnitaryGroup (B.domRestrict₁₂ F F))
    (hFe : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
      F.subtype ∘ₗ (((e g).2 : LinearMap.GeneralLinearGroup E F) : Module.End E F) =
        unitaryOp (g : sesqUnitaryGroup B) ∘ₗ F.subtype)
    {N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B)))} (hNc : CFSG.IsComponent N)
    (hleft : ∀ n ∈ N, (e n).2 = 1)
    {M : Subgroup (centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
      Set (sesqProjUnitary h B)))} (hM : N.map (centralizerImageHom A) = M) :
    2 ≤ finrank E W ∧
      (finrank E W = 2 → p ^ f ≠ 3 ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
        Nat.card k = p ^ f ∧ Nonempty (SL(2, k) ≃* ↥M)) ∧
      (3 ≤ finrank E W → ∃ φ : QuaternionGroup 2 →* ↥M ⧸ center ↥M, Function.Injective φ) := by
  classical
  obtain ⟨ρ, hρi, hρc, -⟩ := restrict_component e hNc hleft
  let ι : N →* sesqUnitaryGroup B :=
    (centralizer ({A} : Set (sesqUnitaryGroup B))).subtype.comp N.subtype
  have hιi : Function.Injective ι := Subtype.val_injective.comp Subtype.val_injective
  have hYF : ∀ n : N, ∀ w ∈ F, unitaryOp (ι n) w = w := by
    intro n w hw
    have h4 := LinearMap.congr_fun (hFe (n : centralizer ({A} : Set (sesqUnitaryGroup B)))) ⟨w, hw⟩
    rw [hleft n n.2] at h4
    exact h4.symm
  let σ : N →* M := ((centralizerImageHom A).comp N.subtype).codRestrict M
    (fun n => hM ▸ Subgroup.mem_map_of_mem _ n.2)
  have hσs : Function.Surjective σ := by
    intro m
    have hm : (m : centralizer ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} :
        Set (sesqProjUnitary h B))) ∈ N.map (centralizerImageHom A) := hM ▸ m.2
    obtain ⟨n, hn, hnm⟩ := hm
    exact ⟨⟨n, hn⟩, Subtype.ext hnm⟩
  have hker0 : ∀ n : N, σ n = 1 → centralizerImageHom A (n : centralizer ({A} :
      Set (sesqUnitaryGroup B))) = 1 := fun n hn => congrArg Subtype.val hn
  have hσk : σ.ker ≤ center N := by
    intro n hn
    have h1 := ker_centralizerImageHom_le_center (h := h) A (hker0 n hn)
    rw [mem_center_iff] at h1 ⊢
    intro y
    exact Subtype.ext (h1 (y : centralizer ({A} : Set (sesqUnitaryGroup B))))
  have hker : ∀ n : N, σ n = 1 → ι n ∈ sesqNormOneScalars h B := by
    intro n hn
    have h1 := congrArg Subtype.val (hker0 n hn)
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ivk93_su_half_block h hp hWs hWl hW1 hF0 ι hιi hYF ρ hρi hρc σ hσs hσk hker

theorem ivk93_eq_of_both_left {G G₁ G₂ : Type*} [Group G] [Group G₁] [Group G₂] (e : G ≃* G₁ × G₂)
    {N₁ N₂ : Subgroup G} (hc₁ : CFSG.IsComponent N₁) (hc₂ : CFSG.IsComponent N₂)
    (l₁ : ∀ x ∈ N₁, (e x).2 = 1) (l₂ : ∀ x ∈ N₂, (e x).2 = 1)
    (hU : ∀ L₁ L₂ : Subgroup G₁, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ = L₂) :
    N₁ = N₂ := by
  obtain ⟨ρ₁, hρ₁i, hρ₁c, hρ₁e⟩ := restrict_component e hc₁ l₁
  obtain ⟨ρ₂, hρ₂i, hρ₂c, hρ₂e⟩ := restrict_component e hc₂ l₂
  have hr : ρ₁.range = ρ₂.range := hU _ _ hρ₁c hρ₂c
  have hle : ∀ {M₁ M₂ : Subgroup G} (ρ₁ : M₁ →* G₁) (ρ₂ : M₂ →* G₁),
      (∀ x : M₁, ρ₁ x = (e x).1) → (∀ x : M₂, ρ₂ x = (e x).1) → (∀ x ∈ M₁, (e x).2 = 1) →
      (∀ x ∈ M₂, (e x).2 = 1) → ρ₁.range ≤ ρ₂.range → M₁ ≤ M₂ := by
    intro M₁ M₂ ρ₁ ρ₂ h₁ h₂ k₁ k₂ hrange n hn
    obtain ⟨m, hm⟩ := hrange (⟨⟨n, hn⟩, rfl⟩ : ρ₁ ⟨n, hn⟩ ∈ ρ₁.range)
    have hem : e m = e n :=
      Prod.ext (by rw [← h₂ m, hm, h₁ ⟨n, hn⟩]) (by rw [k₂ m m.2, k₁ n hn])
    have hmn : (m : G) = n := e.injective hem
    rw [← hmn]
    exact m.2
  exact le_antisymm (hle ρ₁ ρ₂ hρ₁e hρ₂e l₁ l₂ hr.le) (hle ρ₂ ρ₁ hρ₂e hρ₁e l₂ l₁ hr.ge)

theorem ivk93_unitary_two_pComponents_blocks (h : UnitaryFieldData p f E) (hp : p ≠ 2)
    [FiniteDimensional E V] (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) {A : sesqUnitaryGroup B}
    (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    {M₁ M₂ : Subgroup (centralizer
      ({(QuotientGroup.mk' (sesqNormOneScalars h B)) A} : Set (sesqProjUnitary h B)))}
    (h₁ : IsPComponent 2 M₁) (h₂ : IsPComponent 2 M₂) (hne : M₁ ≠ M₂) :
    ∃ d₁ d₂ : ℕ, d₁ + d₂ = finrank E V ∧ 2 ≤ d₁ ∧ 2 ≤ d₂ ∧ Ivk93UnitaryBlock p f M₁ d₁ ∧
      Ivk93UnitaryBlock p f M₂ d₂ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite E := h.finite
  obtain ⟨l, -, -, hN, hP, hM, hcompl, hsplit, hpaired, -, hnormal, hindex, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  rw [← range_centralizerImageHom] at hnormal hindex
  have := hnormal
  have := CatalogueRelativeB.quotient_solvable_of_index_le_two _ hindex
  obtain ⟨N₁, N₂, hN₁, hN₂, hNne, hm₁, hm₂⟩ := ivk93_pComponent_lifts_map (centralizerImageHom A)
    (ker_centralizerImageHom_le_center A) h₁ h₂ hne
  have hq₁ := projective_unitary_involution_centralizer_p_components h hp hn hB hBl _ hA 2
    Nat.prime_two M₁ h₁
  have hq₂ := projective_unitary_involution_centralizer_p_components h hp hn hB hBl _ hA 2
    Nat.prime_two M₂ h₂
  have hc₁ : CFSG.IsComponent N₁ := ivk93_isComponent_of_pComponent hN₁
    (centralizer_lift_pComponent_quasisimple h hp hn hB hBl hA 2 Nat.prime_two N₁ hN₁)
  have hc₂ : CFSG.IsComponent N₂ := ivk93_isComponent_of_pComponent hN₂
    (centralizer_lift_pComponent_quasisimple h hp hn hB hBl hA 2 Nat.prime_two N₂ hN₂)
  rcases hN with hN | hN
  ·
    obtain ⟨-, hsepP, hsepM, e, he⟩ := hsplit hN
    have hsymm : ∀ P : Submodule E V, (B.domRestrict₁₂ P P).IsSymm := fun P =>
      ⟨fun x y => hB.eq (x : V) (y : V)⟩
    have hP1 : 1 ≤ finrank E (eigenPlus l (unitaryOp A)) := Submodule.one_le_finrank_iff.mpr hP
    have hM1 : 1 ≤ finrank E (eigenMinus l (unitaryOp A)) := Submodule.one_le_finrank_iff.mpr hM
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    have hUP : ∀ L₁ L₂ : Subgroup (sesqUnitaryGroup
        (B.domRestrict₁₂ (eigenPlus l (unitaryOp A)) (eigenPlus l (unitaryOp A)))),
        CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ = L₂ := fun L₁ L₂ k₁ k₂ =>
      (eq_unitarySpecial_of_isComponent h hp hP1 (hsymm _) hsepP k₁).2.2.trans
        (eq_unitarySpecial_of_isComponent h hp hP1 (hsymm _) hsepP k₂).2.2.symm
    have hUM : ∀ L₁ L₂ : Subgroup (sesqUnitaryGroup
        (B.domRestrict₁₂ (eigenMinus l (unitaryOp A)) (eigenMinus l (unitaryOp A)))),
        CFSG.IsComponent L₁ → CFSG.IsComponent L₂ → L₁ = L₂ := fun L₁ L₂ k₁ k₂ =>
      (eq_unitarySpecial_of_isComponent h hp hM1 (hsymm _) hsepM k₁).2.2.trans
        (eq_unitarySpecial_of_isComponent h hp hM1 (hsymm _) hsepM k₂).2.2.symm
    let e' := e.trans MulEquiv.prodComm
    have sides : ∀ N : Subgroup (centralizer ({A} : Set (sesqUnitaryGroup B))),
        CFSG.IsComponent N → (∀ n ∈ N, (e n).2 = 1) ∨ (∀ n ∈ N, (e' n).2 = 1) := by
      intro N hN'
      rcases CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
          (isComponent_map_of_isComponent e hN') with k | k
      · exact Or.inl fun n hn => k _ (mem_map_of_mem _ hn)
      · exact Or.inr fun n hn => k _ (mem_map_of_mem _ hn)
    have hhe : ∀ g : centralizer ({A} : Set (sesqUnitaryGroup B)),
        (eigenPlus l (unitaryOp A)).subtype ∘ₗ
            (((e' g).2 : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp A))) :
              Module.End E (eigenPlus l (unitaryOp A))) =
          unitaryOp (g : sesqUnitaryGroup B) ∘ₗ (eigenPlus l (unitaryOp A)).subtype :=
      fun g => (he g).1
    rcases sides N₁ hc₁ with l₁ | r₁ <;> rcases sides N₂ hc₂ with l₂ | r₂
    · exact (hNne (ivk93_eq_of_both_left e hc₁ hc₂ l₁ l₂ hUP)).elim
    ·
      obtain ⟨hd₁, b₁, b₁'⟩ := ivk93_block_of_half h hp (hsymm _) hsepP hP1 hM e
        (fun g => (he g).2) hc₁ l₁ hm₁
      obtain ⟨hd₂, b₂, b₂'⟩ := ivk93_block_of_half h hp (hsymm _) hsepM hM1 hP e' hhe hc₂ r₂ hm₂
      exact ⟨_, _, hsum, hd₁, hd₂, ⟨hq₁, b₁, b₁'⟩, ⟨hq₂, b₂, b₂'⟩⟩
    ·
      obtain ⟨hd₁, b₁, b₁'⟩ := ivk93_block_of_half h hp (hsymm _) hsepM hM1 hP e' hhe hc₁ r₁ hm₁
      obtain ⟨hd₂, b₂, b₂'⟩ := ivk93_block_of_half h hp (hsymm _) hsepP hP1 hM e
        (fun g => (he g).2) hc₂ l₂ hm₂
      exact ⟨_, _, by omega, hd₁, hd₂, ⟨hq₁, b₁, b₁'⟩, ⟨hq₂, b₂, b₂'⟩⟩
    · exact (hNne (ivk93_eq_of_both_left e' hc₁ hc₂ r₁ r₂ hUM)).elim
  ·
    exfalso
    obtain ⟨-, -, -, -, -, -, e, -⟩ := hpaired hN
    have hP1 : 1 ≤ finrank E (eigenPlus l (unitaryOp A)) := Submodule.one_le_finrank_iff.mpr hP
    exact hNne (map_injective e.injective (ivk93_linGL_pComponent_eq hP1
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₁)
      (CatalogueBAlternating.pComponent_map_equiv 2 e _ hN₂)))

end Block

section JLevel

theorem Ivk93Cfg.exists_unitary' {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1)
    {x : StatedProj (StatedSU (2 * r + ε) (p ^ f) K)} {q : ℕ}
    {L L' : Subgroup (StatedProj (StatedSU (2 * r + ε) (p ^ f) K))}
    (h : Ivk93Cfg x q L L') :
    ∃ hud : UnitaryFieldData p f K, ∃ A : sesqUnitaryGroup (hypForm hud r ε),
      orderOf (QuotientGroup.mk A : sesqProjUnitary hud (hypForm hud r ε)) = 2 ∧
      ∃ M₁ M₂ : Subgroup (centralizer
          ({QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε)) A} :
            Set (sesqProjUnitary hud (hypForm hud r ε)))),
        IsPComponent 2 M₁ ∧ IsPComponent 2 M₂ ∧ M₁ ≠ M₂ ∧ Nonempty (↥L ≃* ↥M₁) ∧
          Nonempty (↥L' ≃* ↥M₂) := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  have hrange : φ.range = projSpecial hud (hypForm hud r ε) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact (hypModelEquiv hud (θ y)).2
    · intro hz
      obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
      refine ⟨θ.symm w, ?_⟩
      rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
      rfl
  have : φ.range.Normal := by
    rw [hrange]
    infer_instance
  have hK₁ := isPComponent_map_of_normal φ hφ h.le₁ h.comp₁.2
  have hK₂ := isPComponent_map_of_normal φ hφ h.le₂ h.comp₂.2
  have e₁ : Nonempty (↥L ≃* ↥((L.map φ).subgroupOf (centralizer ({φ x} : Set _)))) :=
    ⟨(L.equivMapOfInjective φ hφ).trans (Subgroup.subgroupOfEquivOfLe hK₁.1).symm⟩
  have e₂ : Nonempty (↥L' ≃* ↥((L'.map φ).subgroupOf (centralizer ({φ x} : Set _)))) :=
    ⟨(L'.equivMapOfInjective φ hφ).trans (Subgroup.subgroupOfEquivOfLe hK₂.1).symm⟩
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (sesqNormOneScalars hud (hypForm hud r ε)) (φ x)
  rw [← hA] at hK₁ hK₂ e₁ e₂
  refine ⟨hud, A, ?_, _, _, hK₁.2, hK₂.2, fun k => h.ne ?_, e₁, e₂⟩
  · change orderOf ((QuotientGroup.mk' (sesqNormOneScalars hud (hypForm hud r ε))) A) = 2
    rw [hA, orderOf_injective φ hφ x, h.ord]
  · have h1 := subgroupOf_inj.mp k
    rw [inf_of_le_left hK₁.1, inf_of_le_left hK₂.1] at h1
    exact map_injective hφ h1

namespace Ivk93Cfg

variable {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {L₁ L₂ : Subgroup J}

theorem false_of_quaternion (h : Ivk93Cfg x q L₁ L₂) {M : Type} [Group M] (e : ↥L₁ ≃* M)
    (hM : CFSG.IsQuasisimple M) (φ : QuaternionGroup 2 →* M ⧸ center M)
    (hφ : Function.Injective φ) : False := by
  classical
  have : Finite M := Finite.of_equiv _ e.toEquiv
  obtain ⟨F, _, _, hFq, ⟨eF⟩⟩ := exists_sl2_equiv_of_hasSL2Model h.sl₁
  have eS : SL(2, F) ≃* (M ⧸ pPrimeCore 2 M) :=
    eF.trans (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)
  have hcard : Nat.card (M ⧸ pPrimeCore 2 M) = q * (q ^ 2 - 1) := by
    rw [← Nat.card_congr eS.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, hFq]
  have hker : pPrimeCore 2 M ≤ center M := by
    rcases LocalCores.quasisimple_normal_subgroups hM (inferInstance : (pPrimeCore 2 M).Normal) with
      htop | hle
    · exfalso
      have h1 : Nat.card (M ⧸ pPrimeCore 2 M) = 1 := by
        rw [htop]
        exact Subgroup.index_top
      have := h.sl2_card_ge
      omega
    · exact hle
  have hker' : (QuotientGroup.mk' (pPrimeCore 2 M)).ker ≤ center M := by
    rw [QuotientGroup.ker_mk']
    exact hker
  obtain ⟨eC⟩ := center_quotient_equiv_of_surjective hM (QuotientGroup.mk' (pPrimeCore 2 M))
    (QuotientGroup.mk'_surjective _) hker'
  let eQ : M ⧸ center M ≃* StatedProj (StatedSL 2 F) :=
    eC.trans ((QuotientGroup.congr (center (M ⧸ pPrimeCore 2 M)) (center SL(2, F)) eS.symm
      (Subgroup.map_center_eq eS.symm)).trans (projectiveSpecialLinearGroupEquivStatedProj 2 F))
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  have hk : Nat.card F = ringChar F ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have hq5 := h.five
  have hodd := h.odd
  have hℓ2 : ringChar F ≠ 2 := by
    intro h2
    rw [h2] at hk
    have : 2 ∣ q := by
      rw [← hFq, hk]
      exact dvd_pow_self 2 (PNat.ne_zero n)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have hX : StatedClassicalModel (M ⧸ center M) .PSL 2 (ringChar F) n :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv eQ
      (OddSelector.statedClassicalModel_psl_two hℓ n.pos hk (by omega) (by omega))
  exact OddSelector.not_psl_two_odd_of_quaternion φ hφ hℓ2 hX

end Ivk93Cfg

end JLevel

end CFSG.GH74.GLS.IVK.Proofs2
