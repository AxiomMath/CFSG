module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCompInner
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDec
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnCard
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwTorusGen


public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KFU
open scoped Fin.NatCast

set_option linter.unusedSectionVars false

section Group

variable {G : Type*} [Group G]

theorem twMap_inv_eq {S S' : Subgroup G} {a : MulAut G} (h : S.map a.toMonoidHom = S') :
    S'.map a⁻¹.toMonoidHom = S := by
  have e : a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [← h, Subgroup.map_map, e, Subgroup.map_id]

theorem twMap_conj_pow {L : Fin 3 → Subgroup G} {n : G}
    (hn : ∀ i, (L i).map (MulAut.conj n).toMonoidHom = L (i + 1)) (j : ℕ) (i : Fin 3) :
    (L i).map (MulAut.conj (n ^ j)).toMonoidHom = L (i + (j : Fin 3)) := by
  induction j generalizing i with
  | zero =>
    have e : (MulAut.conj (n ^ 0)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [e, Subgroup.map_id]
    simp
  | succ j ih =>
    have e : (MulAut.conj (n ^ (j + 1))).toMonoidHom =
        (MulAut.conj (n ^ j)).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
      ext x
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply, pow_succ]
      group
    rw [e, ← Subgroup.map_map, hn, ih, Nat.cast_succ]
    congr 1
    abel

end Group

section Frames

variable
  {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}

theorem twComp_pow_three_mem (hL : TwE6ThreeA2Line K σ h₀ L T n) : n ^ 3 ∈ T ⊔ ⨆ i, L i := by
  have hn : n ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    rw [hL.centralizer_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  refine hL.shift_zero (n ^ 3) (pow_mem hn 3) fun i => ?_
  rw [twMap_conj_pow hL.n_conj 3 i]
  have h30 : ((3 : ℕ) : Fin 3) = 0 := by decide
  rw [h30, add_zero]

theorem twComp_comm_h₀ (hL : TwE6ThreeA2Line K σ h₀ L T n) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ (T ⊔ ⨆ i, L i) ⊔ Subgroup.zpowers n) : h₀ * g = g * h₀ := by
  have hg' : g ∈ twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    rw [hL.centralizer_eq]
    exact hg
  exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg').2 h₀ (Set.mem_singleton h₀)

theorem twComp_frame_mem (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    (i : Fin 3) (w : unitarySU ℓ f K 3) :
    ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈ L i := by
  rw [← hρ i]
  exact ⟨ρ i w, ⟨w, rfl⟩, rfl⟩

theorem twComp_range_eq (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    (i : Fin 3) : (ρ i).range = (L i).subgroupOf (twistedE6RootGroup K σ) := by
  rw [← hρ i]
  ext x
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

theorem twFrames_commute (hL : TwE6ThreeA2Line K σ h₀ L T n)
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i) :
    ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s := fun i j hij s t =>
  Subtype.ext (hL.L_commute i j hij _ (twComp_frame_mem hρ i s) _ (twComp_frame_mem hρ j t))

theorem twLayerProd_mem (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    (y : Fin 3 → unitarySU ℓ f K 3) : twLayerProd ρ y ∈ ⨆ i, L i :=
  mul_mem (mul_mem (Subgroup.mem_iSup_of_mem 0 (twComp_frame_mem hρ 0 _))
    (Subgroup.mem_iSup_of_mem 1 (twComp_frame_mem hρ 1 _)))
    (Subgroup.mem_iSup_of_mem 2 (twComp_frame_mem hρ 2 _))

theorem twLayer_exists_layerProd (hL : TwE6ThreeA2Line K σ h₀ L T n)
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ ⨆ i, L i) :
    ∃ x : Fin 3 → unitarySU ℓ f K 3, g = twLayerProd ρ x := by
  have hcomm := twFrames_commute hL hρ
  have hle : (⨆ i, L i : Subgroup (ModGL TwistTag.E6.tag K)) ≤
      (commProd3 ρ hcomm).range.map (twistedE6RootGroup K σ).subtype := by
    refine iSup_le fun i => ?_
    rw [← hρ i]
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨ρ i s, ⟨Pi.mulSingle i s, commProd3_mulSingle ρ hcomm i s⟩, rfl⟩
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hle hg
  exact ⟨x, hx.symm⟩

theorem twM_exists_mul_layerProd (hL : TwE6ThreeA2Line K σ h₀ L T n)
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    {g : ModGL TwistTag.E6.tag K} (hg : g ∈ T ⊔ ⨆ i, L i) :
    ∃ τ ∈ T, ∃ x : Fin 3 → unitarySU ℓ f K 3, g = τ * twLayerProd ρ x := by
  have hTN : T ≤ Subgroup.normalizer
      ((⨆ i, L i : Subgroup (ModGL TwistTag.E6.tag K)) : Set (ModGL TwistTag.E6.tag K)) := by
    intro t ht
    apply hL.le_normalizer
    rw [hL.centralizer_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left ht)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hg
  obtain ⟨t, ht, l, hl, rfl⟩ := Set.mem_mul.1 hg
  obtain ⟨x, rfl⟩ := twLayer_exists_layerProd hL hρ hl
  exact ⟨t, ht, x, rfl⟩

theorem twLayerProd_act {h : UnitaryFieldData ℓ f K}
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s)
    {τ : ModGL TwistTag.E6.tag K} {A : Fin 3 → primeFormUnitary h (idGram K 3)}
    (hτ : ∀ i w, τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
      ((ρ i (conjSU h (A i) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))
    (x : Fin 3 → unitarySU ℓ f K 3) (i : Fin 3) (w : unitarySU ℓ f K 3) :
    (τ * twLayerProd ρ x) * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (τ * twLayerProd ρ x)⁻¹ =
      ((ρ i (conjSU h (A i * ⟨(x i : GL (Fin 3) K), unitarySU_le_primeFormUnitary h (x i).2⟩) w) :
        twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) := by
  have h1 : twLayerProd ρ x * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
      (twLayerProd ρ x)⁻¹ =
      ((ρ i (x i * w * (x i)⁻¹) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) :=
    congrArg Subtype.val (commProd3_conj_apply ρ hcomm x i w)
  have h2 := hτ i (x i * w * (x i)⁻¹)
  have h3 : conjSU h ⟨(x i : GL (Fin 3) K), unitarySU_le_primeFormUnitary h (x i).2⟩ w =
      x i * w * (x i)⁻¹ := Subtype.ext rfl
  rw [conjSU_mul_apply, h3]
  calc τ * twLayerProd ρ x * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (τ * twLayerProd ρ x)⁻¹
      = τ * (twLayerProd ρ x * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        (twLayerProd ρ x)⁻¹) * τ⁻¹ := by group
    _ = _ := by rw [h1]; exact h2

theorem twLayerProd_pow_three {h : UnitaryFieldData ℓ f K}
    (hinj : ∀ i, Function.Injective (ρ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s)
    {τ : ModGL TwistTag.E6.tag K} {A : Fin 3 → primeFormUnitary h (idGram K 3)}
    (hτ : ∀ i w, τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
      ((ρ i (conjSU h (A i) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))
    (x : Fin 3 → unitarySU ℓ f K 3) (h3 : (τ * twLayerProd ρ x) ^ 3 = 1) (i : Fin 3) :
    ∃ α : K, (((A i : GL (Fin 3) K) * (x i : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
  have hρ' : Function.Injective ((twistedE6RootGroup K σ).subtype.comp (ρ i)) :=
    (twistedE6RootGroup K σ).subtype_injective.comp (hinj i)
  have hε3 : (MulAut.conj (τ * twLayerProd ρ x)) ^ 3 = 1 := by
    rw [← map_pow, h3, map_one]
  have hact : ∀ w, (MulAut.conj (τ * twLayerProd ρ x))
      (((twistedE6RootGroup K σ).subtype.comp (ρ i)) w) =
      ((twistedE6RootGroup K σ).subtype.comp (ρ i))
        (conjSU h (A i * ⟨(x i : GL (Fin 3) K), unitarySU_le_primeFormUnitary h (x i).2⟩) w) := by
    intro w
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply]
    exact twLayerProd_act hcomm hτ x i w
  obtain ⟨α, hα⟩ := exists_pow_three_smul_one_su h hρ' hε3 hact
  exact ⟨α, hα⟩

end Frames

section Cubes


theorem twExists_inner_notMem_zpowers {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ q)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hEi : ¬ E ≤ twistedE6Inn K σ) {ε : MulAut (twistedE6RootGroup K σ)} (hε : ε ∈ E) :
    ∃ v : twistedE6RootGroup K σ, MulAut.conj v ∈ E ∧ MulAut.conj v ∉ Subgroup.zpowers ε := by
  by_contra hno
  push Not at hno
  have h9 : Nat.card ↥(E ⊓ twistedE6Inn K σ) = 3 ^ 2 :=
    card_inf_twistedE6Inn hK σ hσ hcard hED hEi
  have hle : E ⊓ twistedE6Inn K σ ≤ Subgroup.zpowers ε := by
    intro ε' hε'
    obtain ⟨hεE, hεI⟩ := Subgroup.mem_inf.1 hε'
    obtain ⟨v, rfl⟩ := MonoidHom.mem_range.1 hεI
    exact hno v hεE
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h9, Nat.card_zpowers] at hdvd
  have h33 := Nat.dvd_trans hdvd (orderOf_dvd_of_pow_eq_one (hE.2 ε hε))
  norm_num at h33

section Line

variable {K : Type} [Field K] {σ : K ≃+* K} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K} {ℓ f : ℕ}
  {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}

theorem twConj_ne_one (hL : TwE6ThreeA2Line K σ h₀ L T n) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) : MulAut.conj s ≠ 1 := by
  intro h1
  have hc : s ∈ Subgroup.center (twistedE6RootGroup K σ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [exceptional_fixed_center_trivial TwistTag.E6 K σ] at hc
  exact hL.h₀_ne (by rw [← hs, Subgroup.mem_bot.1 hc]; rfl)

theorem twComm_of_conj_commute {s v : twistedE6RootGroup K σ}
    (h : MulAut.conj v * MulAut.conj s = MulAut.conj s * MulAut.conj v) : v * s = s * v := by
  rw [← map_mul, ← map_mul] at h
  exact CFSG.Fischer.mulAutConj_injective (exceptional_fixed_center_trivial TwistTag.E6 K σ) h

theorem twComp_mem_of_notMem (hL : TwE6ThreeA2Line K σ h₀ L T n)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) {s : twistedE6RootGroup K σ}
    (hs : (s : ModGL TwistTag.E6.tag K) = h₀) (hsE : MulAut.conj s ∈ E)
    {v : twistedE6RootGroup K σ} (hvE : MulAut.conj v ∈ E)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s))
    (hvM : (v : ModGL TwistTag.E6.tag K) ∉ T ⊔ ⨆ i, L i) :
    n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  have hcomm : MulAut.conj v * MulAut.conj s = MulAut.conj s * MulAut.conj v :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨_, hvE⟩ : E) ⟨_, hsE⟩)
  have hvs' : v * s = s * v := twComm_of_conj_commute hcomm
  have hvC : (v : ModGL TwistTag.E6.tag K) ∈
      twistedE6RootGroup K σ ⊓ Subgroup.centralizer {h₀} := by
    refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hs]
    exact congrArg Subtype.val hvs'
  obtain ⟨t, ht, l₀, hl₀, l₁, hl₁, l₂, hl₂, j, hj, he⟩ := hL.centralizer_mul _ hvC
  have hm : t * l₀ * l₁ * l₂ ∈ T ⊔ ⨆ i, L i :=
    mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left ht)
      (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 0 hl₀)))
      (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 1 hl₁)))
      (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem 2 hl₂))
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at he
    exact hvM (by rw [he]; exact hm)
  have hσv : MulAut.conj s v = v := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (s : ModGL TwistTag.E6.tag K) * (v : ModGL TwistTag.E6.tag K) *
      (s : ModGL TwistTag.E6.tag K)⁻¹ = (v : ModGL TwistTag.E6.tag K)
    exact mul_inv_eq_iff_eq_mul.2 (congrArg Subtype.val hvs').symm
  have hvv : MulAut.conj v v = v := by
    rw [MulAut.conj_apply, mul_inv_cancel_right]
  have hvΓ := mem_seitzHyperGamma_of_fixed hE hcard27 hsE hvE (twConj_ne_one hL hs) hvs hσv hvv
  have hnj : n ^ j ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔
      (T ⊔ ⨆ i, L i) := by
    have e : n ^ j = (t * l₀ * l₁ * l₂)⁻¹ * (v : ModGL TwistTag.E6.tag K) := by
      rw [he, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_right (inv_mem hm)) (Subgroup.mem_sup_left ⟨v, hvΓ, rfl⟩)
  exact mem_of_pow_mem_of_cube_mem hj hj0 hnj (Subgroup.mem_sup_right (twComp_pow_three_mem hL))

theorem twLayerProd_commute {h : UnitaryFieldData ℓ f K} (h3 : 3 ∣ ℓ ^ f + 1)
    {Th : Subgroup (ModGL TwistTag.E6.tag K)} (hThc : ∀ x ∈ Th, ∀ y ∈ Th, x * y = y * x)
    {A : Fin 3 → ModGL TwistTag.E6.tag K → primeFormUnitary h (idGram K 3)}
    (hAc : ∀ i, ∀ τ ∈ Th, ∀ τ' ∈ Th, A i τ * A i τ' = A i τ' * A i τ)
    (hAact : ∀ i, ∀ τ ∈ Th, ∀ w : unitarySU ℓ f K 3,
      τ * ((ρ i w : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * τ⁻¹ =
        ((ρ i (conjSU h (A i τ) w) : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s)
    {τ t : ModGL TwistTag.E6.tag K} (hτ : τ ∈ Th) (ht : t ∈ Th) (x : Fin 3 → unitarySU ℓ f K 3)
    (hα : ∀ i, ∃ α : K, (((A i τ : GL (Fin 3) K) * (x i : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1) :
    ∃ y : Fin 3 → unitarySU ℓ f K 3,
      τ * twLayerProd ρ x * (t * twLayerProd ρ y) =
        t * twLayerProd ρ y * (τ * twLayerProd ρ x) := by
  choose α hα using hα
  have hAB : ∀ i, A i t * A i τ = A i τ * A i t := fun i => hAc i t ht τ hτ
  choose y hy using fun i => exists_conjSU_mul_eq h h3 (hAB i) (x i) (hα i)
  refine ⟨y, ?_⟩
  have hxy : twLayerProd ρ (fun i => conjSU h (A i t)⁻¹ (x i)) * twLayerProd ρ y =
      twLayerProd ρ (fun i => conjSU h (A i τ)⁻¹ (y i)) * twLayerProd ρ x := by
    have h1 : commProd3 ρ hcomm (fun i => conjSU h (A i t)⁻¹ (x i)) * commProd3 ρ hcomm y =
        commProd3 ρ hcomm (fun i => conjSU h (A i τ)⁻¹ (y i)) * commProd3 ρ hcomm x := by
      rw [← map_mul, ← map_mul]
      exact congrArg (commProd3 ρ hcomm) (funext hy)
    exact congrArg Subtype.val h1
  have hPt : t⁻¹ * twLayerProd ρ x * t = twLayerProd ρ (fun i => conjSU h (A i t)⁻¹ (x i)) :=
    twLayerProd_conj (fun i w => inv_conj_frame (B := fun i => A i t)
      (fun i w => hAact i t ht w) i w) x
  have hQτ : τ⁻¹ * twLayerProd ρ y * τ = twLayerProd ρ (fun i => conjSU h (A i τ)⁻¹ (y i)) :=
    twLayerProd_conj (fun i w => inv_conj_frame (B := fun i => A i τ)
      (fun i w => hAact i τ hτ w) i w) y
  calc τ * twLayerProd ρ x * (t * twLayerProd ρ y)
      = τ * t * (t⁻¹ * twLayerProd ρ x * t) * twLayerProd ρ y := by group
    _ = τ * t * (twLayerProd ρ (fun i => conjSU h (A i t)⁻¹ (x i)) * twLayerProd ρ y) := by
        rw [hPt]; group
    _ = τ * t * (twLayerProd ρ (fun i => conjSU h (A i τ)⁻¹ (y i)) * twLayerProd ρ x) := by
        rw [hxy]
    _ = τ * t * (τ⁻¹ * twLayerProd ρ y * τ) * twLayerProd ρ x := by rw [hQτ]; group
    _ = t * τ * (τ⁻¹ * twLayerProd ρ y * τ) * twLayerProd ρ x := by rw [hThc τ hτ t ht]
    _ = t * twLayerProd ρ y * (τ * twLayerProd ρ x) := by group

theorem twComp_mem_of_shift {h : UnitaryFieldData ℓ f K} (h3 : 3 ∣ ℓ ^ f + 1)
    (hL : TwE6ThreeA2Line K σ h₀ L T n) (hinj : ∀ i, Function.Injective (ρ i))
    (hrange : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    (htor : TwTorusAct K σ h₀ T h ρ)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    {s : twistedE6RootGroup K σ} (hs : (s : ModGL TwistTag.E6.tag K) = h₀)
    (hsE : MulAut.conj s ∈ E) {v : twistedE6RootGroup K σ} (hvE : MulAut.conj v ∈ E)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s))
    (hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i)
    {φ : MulAut (twistedE6RootGroup K σ)} (hφ : φ ∈ E) {k : Fin 3} (hk0 : k ≠ 0)
    (hfk : ∀ i, (ρ i).range.map φ.toMonoidHom = (ρ (i + k)).range) :
    n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  have hcard27 : Nat.card E = 27 := by rw [hcard]; norm_num
  obtain ⟨Th, A, hTTh, hThc, hAc, hAact, hDec⟩ := htor
  have hcomm := twFrames_commute hL hrange
  have hσ1 := twConj_ne_one hL hs
  have hZ : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  obtain ⟨j, hj3, hjk⟩ : ∃ j : ℕ, j < 3 ∧ ((j : ℕ) : Fin 3) = k :=
    ⟨k.val, k.2, Fin.cast_val_eq_self k⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hk0 (hjk.symm.trans Nat.cast_zero)
  obtain ⟨nj, hnjM⟩ : ∃ nj : twistedE6RootGroup K σ, (nj : ModGL TwistTag.E6.tag K) = n ^ j :=
    ⟨⟨n, hL.n_mem⟩ ^ j, rfl⟩
  have hnjs : nj * s = s * nj := by
    apply Subtype.ext
    show (nj : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) =
      (s : ModGL TwistTag.E6.tag K) * (nj : ModGL TwistTag.E6.tag K)
    rw [hnjM, hs]
    exact (twComp_comm_h₀ hL
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers n) j))).symm
  have hconjnjs : MulAut.conj nj * MulAut.conj s = MulAut.conj s * MulAut.conj nj := by
    rw [← map_mul, ← map_mul, hnjs]
  have hconjR : ∀ i, (ρ i).range.map (MulAut.conj nj).toMonoidHom = (ρ (i + k)).range := by
    intro i
    rw [twComp_range_eq hrange, twComp_range_eq hrange]
    refine map_conj_subgroupOf (twistedE6RootGroup K σ) (hL.L_le i) ?_
    rw [hnjM, ← hjk]
    exact twMap_conj_pow hL.n_conj j i
  obtain ⟨ε', hε'⟩ : ∃ ε' : MulAut (twistedE6RootGroup K σ), ε' = (MulAut.conj nj)⁻¹ * φ :=
    ⟨_, rfl⟩
  have hφε : φ = MulAut.conj nj * ε' := by rw [hε', mul_inv_cancel_left]
  have hinn : MulAut.conj nj ∈ twistedE6Inn K σ := MonoidHom.mem_range.2 ⟨nj, rfl⟩
  have hε'D : ε' ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rw [hε']
    exact mul_mem (inv_mem (Subgroup.mem_sup_left hinn)) (hED hφ)
  have hEcomm : ∀ ε ∈ E, ε * MulAut.conj s = MulAut.conj s * ε := fun ε hε =>
    congrArg Subtype.val (hE.1.is_comm.comm (⟨ε, hε⟩ : E) ⟨_, hsE⟩)
  have hε'comm : ε' * MulAut.conj s = MulAut.conj s * ε' := by
    rw [hε']
    have c1 : Commute (MulAut.conj nj) (MulAut.conj s) := hconjnjs
    have c2 : Commute φ (MulAut.conj s) := hEcomm φ hφ
    exact (c1.inv_left.mul_left c2).eq
  have hε'R : ∀ i, (ρ i).range.map ε'.toMonoidHom = (ρ i).range := by
    intro i
    have e : ε'.toMonoidHom = (MulAut.conj nj)⁻¹.toMonoidHom.comp φ.toMonoidHom := by
      rw [hε']; rfl
    rw [e, ← Subgroup.map_map, hfk i]
    exact twMap_inv_eq (hconjR i)
  obtain ⟨τ, hτTh, x, hx⟩ := hDec s hs ε' hε'D hε'comm hε'R
  have hφc : ∀ c : twistedE6RootGroup K σ,
      ((φ c : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        (n ^ j * (τ * twLayerProd ρ x)) * (c : ModGL TwistTag.E6.tag K) *
          (n ^ j * (τ * twLayerProd ρ x))⁻¹ := by
    intro c
    have h1 : φ c = nj * ε' c * nj⁻¹ := by
      rw [hφε, MulAut.mul_apply, MulAut.conj_apply]
    rw [h1]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnjM, hx c]
    group
  have hφv : φ v = v := by
    have hc : φ * MulAut.conj v = MulAut.conj v * φ :=
      congrArg Subtype.val (hE.1.is_comm.comm (⟨φ, hφ⟩ : E) ⟨_, hvE⟩)
    apply CFSG.Fischer.mulAutConj_injective hZ
    refine MulEquiv.ext fun y => ?_
    have h := congrArg (fun ψ : MulAut (twistedE6RootGroup K σ) => ψ (φ.symm y)) hc
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h
    simp only [MulAut.conj_apply]
    exact h
  have hĝv : (n ^ j * (τ * twLayerProd ρ x)) * (v : ModGL TwistTag.E6.tag K) *
      (n ^ j * (τ * twLayerProd ρ x))⁻¹ = v := by
    rw [← hφc v, hφv]
  obtain ⟨t', ht'T, w, hvw⟩ := twM_exists_mul_layerProd hL hrange hvM
  have ht'Th : t' ∈ Th := hTTh ht'T
  have hv3 : v ^ 3 = 1 := by
    apply CFSG.Fischer.mulAutConj_injective hZ
    rw [map_pow, map_one]
    exact hE.2 _ hvE
  have hv3M : (t' * twLayerProd ρ w) ^ 3 = 1 := by
    rw [← hvw]
    exact congrArg Subtype.val hv3
  have hα : ∀ i, ∃ α : K, (((A i t' : GL (Fin 3) K) * (w i : GL (Fin 3) K) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := fun i =>
    twLayerProd_pow_three (A := fun i => A i t') hinj hcomm
      (fun i w' => hAact i t' ht'Th w') w hv3M i
  obtain ⟨y, hy⟩ := twLayerProd_commute h3 hThc hAc hAact hcomm ht'Th (inv_mem hτTh) w hα
  rw [← hvw] at hy
  have hxτ : τ * twLayerProd ρ x * τ⁻¹ =
      twLayerProd ρ (fun i => conjSU h (A i τ) (x i)) := by
    have := twLayerProd_conj (ρ := ρ) (g := τ⁻¹) (φ := fun i => conjSU h (A i τ))
      (fun i w' => by rw [inv_inv]; exact hAact i τ hτTh w') x
    rwa [inv_inv] at this
  obtain ⟨gC, hgC⟩ : ∃ g : twistedE6RootGroup K σ, (g : ModGL TwistTag.E6.tag K) =
      n ^ j * (twLayerProd ρ (fun i => conjSU h (A i τ) (x i)) * twLayerProd ρ y) :=
    ⟨nj * (commProd3 ρ hcomm (fun i => conjSU h (A i τ) (x i)) * commProd3 ρ hcomm y), by
      rw [Subgroup.coe_mul, hnjM]; rfl⟩
  have hgcs : h₀ * (gC : ModGL TwistTag.E6.tag K) = (gC : ModGL TwistTag.E6.tag K) * h₀ := by
    rw [hgC]
    exact twComp_comm_h₀ hL (mul_mem (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers n) j))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (mul_mem (twLayerProd_mem hrange _) (twLayerProd_mem hrange _)))))
  have hσg : MulAut.conj s gC = gC := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (s : ModGL TwistTag.E6.tag K) * (gC : ModGL TwistTag.E6.tag K) *
      (s : ModGL TwistTag.E6.tag K)⁻¹ = (gC : ModGL TwistTag.E6.tag K)
    rw [hs]
    exact mul_inv_eq_iff_eq_mul.2 hgcs
  have hgv : (v : ModGL TwistTag.E6.tag K) * (gC : ModGL TwistTag.E6.tag K) =
      (gC : ModGL TwistTag.E6.tag K) * (v : ModGL TwistTag.E6.tag K) := by
    have hĝc : (n ^ j * (τ * twLayerProd ρ x)) * (v : ModGL TwistTag.E6.tag K) =
        (v : ModGL TwistTag.E6.tag K) * (n ^ j * (τ * twLayerProd ρ x)) :=
      mul_inv_eq_iff_eq_mul.1 hĝv
    have hPc : (τ⁻¹ * twLayerProd ρ y) * (v : ModGL TwistTag.E6.tag K) =
        (v : ModGL TwistTag.E6.tag K) * (τ⁻¹ * twLayerProd ρ y) := hy.symm
    have hgC' : (gC : ModGL TwistTag.E6.tag K) =
        (n ^ j * (τ * twLayerProd ρ x)) * (τ⁻¹ * twLayerProd ρ y) := by
      rw [hgC, ← hxτ]
      group
    rw [hgC']
    calc (v : ModGL TwistTag.E6.tag K) *
          ((n ^ j * (τ * twLayerProd ρ x)) * (τ⁻¹ * twLayerProd ρ y))
        = ((v : ModGL TwistTag.E6.tag K) * (n ^ j * (τ * twLayerProd ρ x))) *
          (τ⁻¹ * twLayerProd ρ y) := by group
      _ = ((n ^ j * (τ * twLayerProd ρ x)) * (v : ModGL TwistTag.E6.tag K)) *
          (τ⁻¹ * twLayerProd ρ y) := by rw [hĝc]
      _ = (n ^ j * (τ * twLayerProd ρ x)) *
          ((v : ModGL TwistTag.E6.tag K) * (τ⁻¹ * twLayerProd ρ y)) := by group
      _ = (n ^ j * (τ * twLayerProd ρ x)) *
          ((τ⁻¹ * twLayerProd ρ y) * (v : ModGL TwistTag.E6.tag K)) := by rw [hPc]
      _ = ((n ^ j * (τ * twLayerProd ρ x)) * (τ⁻¹ * twLayerProd ρ y)) *
          (v : ModGL TwistTag.E6.tag K) := by group
  have hvg : MulAut.conj v gC = gC := by
    apply Subtype.ext
    rw [MulAut.conj_apply]
    show (v : ModGL TwistTag.E6.tag K) * (gC : ModGL TwistTag.E6.tag K) *
      (v : ModGL TwistTag.E6.tag K)⁻¹ = (gC : ModGL TwistTag.E6.tag K)
    rw [hgv, mul_inv_cancel_right]
  have hgΓ : gC ∈ seitzHyperGamma 3 E :=
    mem_seitzHyperGamma_of_fixed hE hcard27 hsE hvE hσ1 hvs hσg hvg
  have hnj : n ^ j ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔
      (T ⊔ ⨆ i, L i) := by
    have e : n ^ j = (gC : ModGL TwistTag.E6.tag K) *
        (twLayerProd ρ (fun i => conjSU h (A i τ) (x i)) * twLayerProd ρ y)⁻¹ := by
      rw [hgC, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left ⟨gC, hgΓ, rfl⟩) (Subgroup.mem_sup_right
      (inv_mem (Subgroup.mem_sup_right (mul_mem (twLayerProd_mem hrange _)
        (twLayerProd_mem hrange _)))))
  exact mem_of_pow_mem_of_cube_mem hj3 hj0 hnj (Subgroup.mem_sup_right (twComp_pow_three_mem hL))

end Line

end Cubes

section Final


theorem twComp_mem_of_moves {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hch : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) (hq : q ≠ 2)
    {h₀ : ModGL TwistTag.E6.tag K} {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)}
    {T : Subgroup (ModGL TwistTag.E6.tag K)} {n : ModGL TwistTag.E6.tag K}
    (hL : TwE6ThreeA2Line K σ h₀ L T n)
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hED : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    {s : twistedE6RootGroup K σ} (hs : (s : ModGL TwistTag.E6.tag K) = h₀)
    (hsE : MulAut.conj s ∈ E) {v : twistedE6RootGroup K σ} (hvE : MulAut.conj v ∈ E)
    (hvs : MulAut.conj v ∉ Subgroup.zpowers (MulAut.conj s))
    (hvM : (v : ModGL TwistTag.E6.tag K) ∈ T ⊔ ⨆ i, L i)
    (hmove : ¬ ∀ f ∈ E, ∀ i, ((L i).subgroupOf (twistedE6RootGroup K σ)).map f.toMonoidHom =
      (L i).subgroupOf (twistedE6RootGroup K σ)) :
    n ∈ (seitzHyperGamma 3 E).map (twistedE6RootGroup K σ).subtype ⊔ (T ⊔ ⨆ i, L i) := by
  push Not at hmove
  obtain ⟨φ, hφ, i₀, hi₀⟩ := hmove
  obtain ⟨ℓ, f, h, ρ, hqℓ, ⟨hinj, hrange, -⟩, htor⟩ :=
    twTorusModel_holds K σ q hch hσ hK h3 hq h₀ L T n hL
  have h3' : 3 ∣ ℓ ^ f + 1 := by rw [hqℓ]; exact h3
  have hcomm : φ * MulAut.conj s = MulAut.conj s * φ :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨φ, hφ⟩ : E) ⟨_, hsE⟩)
  obtain ⟨k, hk⟩ := twLayer_exists_shift hL hs (hE.2 φ hφ) hcomm
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hi₀
    rw [hk i₀, add_zero]
  have hfk : ∀ i, (ρ i).range.map φ.toMonoidHom = (ρ (i + k)).range := fun i => by
    rw [twComp_range_eq hrange, twComp_range_eq hrange, hk i]
  exact twComp_mem_of_shift h3' hL hinj hrange htor hE hcard hED hs hsE hvE hvs hvM hφ hk0 hfk

end Final

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
