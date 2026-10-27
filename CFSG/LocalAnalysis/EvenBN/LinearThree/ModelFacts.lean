module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.FusionFacts
public import CFSG.LocalAnalysis.EvenBN.LinearThree.Setup
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelAut
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionPerfect
import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.LocalAnalysis.OddStandard.Seitz77Setup
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Matrix Subgroup CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover
open CFSG.ABGLocalTools (IsSylowOf)

section Act

variable {G : Type*} [Group G] {A : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def act (e : A ≃* projectiveSL 3 K) :
    normalizer (A : Set G) →* MulAut (projectiveSL 3 K) :=
  (MulAut.congr e).toMonoidHom.comp A.normalizerMonoidHom

theorem coe_symm_act_apply (e : A ≃* projectiveSL 3 K) (n : normalizer (A : Set G))
    (p : projectiveSL 3 K) : ((e.symm (act e n p) : A) : G) = n * (e.symm p : G) * (n : G)⁻¹ := by
  simp [act, MulAut.congr_apply]

theorem act_eq_one_iff (e : A ≃* projectiveSL 3 K) (n : normalizer (A : Set G)) :
    act e n = 1 ↔ (n : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := coe_symm_act_apply e n (e ⟨x, hx⟩)
    rw [h, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    change x = n * x * (n : G)⁻¹ at h1
    calc x * n = n * x * (n : G)⁻¹ * n := by rw [← h1]
      _ = n * x := by group
  · intro h
    refine MulEquiv.ext fun p => e.symm.injective (Subtype.ext ?_)
    rw [coe_symm_act_apply, MulAut.one_apply, ← mem_centralizer_iff.1 h _ (e.symm p).2]
    group

theorem act_of_mem (e : A ≃* projectiveSL 3 K) {a : G} (ha : a ∈ A) :
    act e ⟨a, le_normalizer ha⟩ = MulAut.conj (e ⟨a, ha⟩) := by
  refine MulEquiv.ext fun p => e.symm.injective (Subtype.ext ?_)
  rw [coe_symm_act_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  simp

theorem act_mem_range_iff (e : A ≃* projectiveSL 3 K) {x : G} (hx : x ∈ normalizer (A : Set G)) :
    act e ⟨x, hx⟩ ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range ↔
      x ∈ A ⊔ centralizer (A : Set G) := by
  constructor
  · rintro ⟨y, hy⟩
    set a : G := (e.symm y : G) with ha
    have haA : a ∈ A := (e.symm y).2
    have h1 : act e (⟨a, le_normalizer haA⟩⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, act_of_mem e haA, ← hy]
      have : (⟨a, haA⟩ : A) = e.symm y := rfl
      rw [this, MulEquiv.apply_symm_apply, inv_mul_cancel]
    have h2 := (act_eq_one_iff e _).1 h1
    have h3 : a⁻¹ * x ∈ centralizer (A : Set G) := h2
    rw [show x = a * (a⁻¹ * x) by group]
    exact mul_mem_sup haA h3
  · intro hmem
    let L : Subgroup G := ((MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range.comap
      (act e)).map (normalizer (A : Set G)).subtype
    have hAL : A ≤ L := fun a ha => ⟨⟨a, le_normalizer ha⟩,
      mem_comap.2 (by rw [act_of_mem e ha]; exact ⟨_, rfl⟩), rfl⟩
    have hCL : centralizer (A : Set G) ≤ L := fun c hc => ⟨⟨c, centralizer_le_normalizer _ hc⟩,
      mem_comap.2 (by rw [(act_eq_one_iff e _).2 hc]; exact one_mem _), rfl⟩
    obtain ⟨n, hn, hnx⟩ := sup_le hAL hCL hmem
    have : n = ⟨x, hx⟩ := Subtype.ext hnx
    rw [← this]
    exact hn

theorem act_apply_eq_iff (e : A ≃* projectiveSL 3 K) (n : normalizer (A : Set G)) (a : A) :
    act e n (e a) = e a ↔ (n : G) * a = a * n := by
  constructor
  · intro h
    have h1 := coe_symm_act_apply e n (e a)
    rw [h, MulEquiv.symm_apply_apply] at h1
    calc (n : G) * a = n * a * (n : G)⁻¹ * n := by group
      _ = a * n := by rw [← h1]
  · intro h
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_act_apply, MulEquiv.symm_apply_apply, h]
    group

end Act

structure Facts {G : Type*} [Group G] [Finite G] (A : Subgroup G) (q : ℕ) : Prop where
  center_eq_bot : A ⊓ centralizer (A : Set G) = ⊥
  invol_conj : ∀ x ∈ A, ∀ y ∈ A, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a * x * a⁻¹ = y
  elem_inner : ∀ E : Subgroup G, E ≤ normalizer (A : Set G) → IsElemAbelian 2 E →
    4 * q * Nat.card ↥(E ⊓ centralizer (A : Set G)) < Nat.card E →
      E ≤ A ⊔ centralizer (A : Set G)
  cent_sylow : ∀ V : Subgroup G, IsSylowOf 2 V A →
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G)
  cent_radical : ∀ V V₁ V₂ : Subgroup G, IsSylowOf 2 V A → Radicals V V₁ V₂ q →
    ∀ W : Subgroup G, (W = V₁ ∨ W = V₂) →
      normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ W ⊔ centralizer (A : Set G)
  radicals : ∀ V : Subgroup G, IsSylowOf 2 V A → ∃ V₁ V₂ : Subgroup G, Radicals V V₁ V₂ q
  levi : ∀ V V₁ V₂ : Subgroup G, IsSylowOf 2 V A → Radicals V V₁ V₂ q →
    ∀ W : Subgroup G, (W = V₁ ∨ W = V₂) →
      ∃ (K : Type) (_ : Field K), Nat.card K = q ∧ Nonempty (LeviData A W K)
  outer_fuse : ∀ y ∈ normalizer (A : Set G), y * y = 1 → y ∉ A ⊔ centralizer (A : Set G) →
    ∀ c ∈ A, y * c * (y * c) = 1 → ∃ b ∈ A, b * y * b⁻¹ = y * c
  outer_perfect : ∀ y ∈ normalizer (A : Set G), y * y = 1 → y ∉ A ⊔ centralizer (A : Set G) →
    ∃ D : Subgroup G, D ≤ A ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, orderOf c = 2
  perfect_inv : ∀ D : Subgroup G, D ≤ normalizer (A : Set G) → ⁅D, D⁆ = D →
    ∀ c ∈ D, c * c = 1 → c ∈ A

theorem Facts.outer_fuse_of_mem_centralizer {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {q : ℕ} (F : Facts A q) {y : G} (hyN : y ∈ normalizer (A : Set G)) (hy2 : y * y = 1)
    (hout : y ∉ A ⊔ centralizer (A : Set G)) {c : G} (hc : c ∈ A ⊓ centralizer ({y} : Set G))
    (hc2 : c * c = 1) : ∃ b ∈ A, b * y * b⁻¹ = y * c := by
  refine F.outer_fuse y hyN hy2 hout c hc.1 ?_
  have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hc.2
  calc y * c * (y * c) = y * (c * y) * c := by group
    _ = y * (y * c) * c := by rw [hcy]
    _ = (y * y) * (c * c) := by group
    _ = 1 := by rw [hy2, hc2, one_mul]

theorem Facts.toFusionFacts {G : Type*} [Group G] [Finite G]
    {A : Subgroup G} {q : ℕ} (F : Facts A q) : FusionFacts A q where
  odd_inf := by
    rw [F.center_eq_bot, Subgroup.card_bot]
    norm_num
  invol_conj := F.invol_conj
  elem_inner := F.elem_inner
  cent_sylow := F.cent_sylow
  outer_fuse := by
    intro y hyN hy2 hout c hc hc2
    exact F.outer_fuse_of_mem_centralizer hyN hy2 hout hc hc2
  outer_perfect := F.outer_perfect
  perfect_inv := F.perfect_inv

section Transport

variable {G : Type*} [Group G] {A : Subgroup G} {K : Type} [Field K]

theorem elem_inner_of_mulEquiv [Finite G] [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : A ≃* projectiveSL 3 K) {E : Subgroup G} (hEN : E ≤ normalizer (A : Set G))
    (hE : IsElemAbelian 2 E)
    (hcard : 4 * Nat.card K * Nat.card ↥(E ⊓ centralizer (A : Set G)) < Nat.card E) :
    E ≤ A ⊔ centralizer (A : Set G) := by
  let ψ : E →* MulAut (projectiveSL 3 K) := (act e).comp (Subgroup.inclusion hEN)
  have hrange : IsElemAbelian 2 ψ.range := by
    refine isElemAbelian_of_forall ?_ ?_
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (comm_of_isElemAbelian hE x.2 y.2))
    · rintro _ ⟨x, rfl⟩
      have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
      rw [← map_pow, hx2, map_one]
  have hker : Nat.card ψ.ker ≤ Nat.card ↥(E ⊓ centralizer (A : Set G)) := by
    rw [← Subgroup.card_map_of_injective E.subtype_injective]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z.2, (act_eq_one_iff e _).1 (MonoidHom.mem_ker.1 hz)⟩
  have h1 := Subgroup.card_ker_mul_card_range ψ
  have hle : ψ.range ≤ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range := by
    by_contra hnot
    have h2 := card_le_of_not_le_range hf hK hrange hnot
    have h3 : Nat.card ψ.ker * Nat.card ψ.range ≤
        Nat.card ↥(E ⊓ centralizer (A : Set G)) * (4 * Nat.card K) :=
      Nat.mul_le_mul hker h2
    rw [h1] at h3
    nlinarith
  intro x hx
  exact (act_mem_range_iff e (hEN hx)).1 (hle ⟨⟨x, hx⟩, rfl⟩)

theorem act_inv_mul (e : A ≃* projectiveSL 3 K) {a x : G} (ha : a ∈ A)
    (hx : x ∈ normalizer (A : Set G)) :
    act e ⟨a⁻¹ * x, mul_mem (inv_mem (le_normalizer ha)) hx⟩ =
      (MulAut.conj (e ⟨a, ha⟩))⁻¹ * act e ⟨x, hx⟩ := by
  have h : (⟨a⁻¹ * x, mul_mem (inv_mem (le_normalizer ha)) hx⟩ : normalizer (A : Set G)) =
      (⟨a, le_normalizer ha⟩ : normalizer (A : Set G))⁻¹ * ⟨x, hx⟩ := rfl
  rw [h, map_mul, map_inv, act_of_mem e ha]

theorem inv_mul_mem_centralizer (e : A ≃* projectiveSL 3 K) {a x : G} (ha : a ∈ A)
    (hx : x ∈ normalizer (A : Set G)) (h : act e ⟨x, hx⟩ = MulAut.conj (e ⟨a, ha⟩)) :
    a⁻¹ * x ∈ centralizer (A : Set G) := by
  have h1 := act_inv_mul e ha hx
  rw [h, inv_mul_cancel] at h1
  exact (act_eq_one_iff e _).1 h1

theorem cent_sylow_of_mulEquiv [Finite G] [Finite K] [CharP K 2] (e : A ≃* projectiveSL 3 K)
    {V : Subgroup G}
    (hV : IsSylowOf 2 V A) :
    normalizer (A : Set G) ⊓ centralizer (V : Set G) ≤
      (V ⊓ centralizer (V : Set G)) ⊔ centralizer (A : Set G) := by
  obtain ⟨F⟩ := exists_frame e hV
  rintro x ⟨hxN, hxV⟩
  set e' : A ≃* projectiveSL 3 K := F.equiv.symm with he'
  have hfix : ∀ u ∈ projUnitriangular 3 K, act e' ⟨x, hxN⟩ u = u := by
    intro u hu
    rw [← projUnip_eq_projUnitriangular] at hu
    have h := (act_apply_eq_iff e' ⟨x, hxN⟩ (F.equiv u)).2
      (mem_centralizer_iff.1 hxV _ (F.mem_V hu)).symm
    rwa [he', MulEquiv.symm_apply_apply] at h
  obtain ⟨y, hy⟩ := SeitzReduction.LinearPilot.mem_range_conj_of_fix_projUnitriangular le_rfl _ hfix
  have hyc : ∀ u ∈ projUnitriangular 3 K, u * y = y * u := by
    intro u hu
    have h := hfix u hu
    rw [← hy, MulAut.conj_apply] at h
    calc u * y = y * u * y⁻¹ * y := by rw [h]
      _ = y * u := by group
  obtain ⟨b, hb⟩ := SeitzReduction.LinearPilot.exists_eq_proj_transvection_of_commute
    (by norm_num : 2 ≤ 3) hyc
  have hyU : y ∈ projUnip K := by
    rw [projUnip_eq_projUnitriangular, hb]
    exact SeitzReduction.LinearPilot.proj_transvection_mem_projUnitriangular
      (SeitzReduction.LinearPilot.firstIdx_lt_lastIdx _) b
  have haA : F.φ y ∈ A := F.mem_A y
  have haV : F.φ y ∈ V ⊓ centralizer (V : Set G) := by
    refine ⟨F.mem_V hyU, mem_centralizer_iff.2 fun v hv => ?_⟩
    obtain ⟨u, hu, rfl⟩ := F.exists_eq_of_mem_V hv
    rw [← map_mul, ← map_mul,
      hyc u (by rw [← projUnip_eq_projUnitriangular]; exact hu)]
  have hcent : (F.φ y)⁻¹ * x ∈ centralizer (A : Set G) := by
    refine inv_mul_mem_centralizer e' haA hxN ?_
    rw [← hy]
    congr 1
    exact (MulEquiv.eq_symm_apply _).2 rfl
  rw [show x = F.φ y * ((F.φ y)⁻¹ * x) by group]
  exact mul_mem_sup haV hcent

theorem cent_radical_of_mulEquiv [Finite G] [Finite K] [CharP K 2] (e : A ≃* projectiveSL 3 K)
    {V V₁ V₂ W : Subgroup G} (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂ (Nat.card K))
    (hW : W = V₁ ∨ W = V₂) :
    normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ W ⊔ centralizer (A : Set G) := by
  obtain ⟨F⟩ := exists_frame e hV
  obtain ⟨i, rfl⟩ := F.exists_eq_radical hR hW
  rintro x ⟨hxN, hxW⟩
  set e' : A ≃* projectiveSL 3 K := F.equiv.symm with he'
  have hfix : ∀ u ∈ projRad K i, act e' ⟨x, hxN⟩ u = u := by
    intro u hu
    have h := (act_apply_eq_iff e' ⟨x, hxN⟩ (F.equiv u)).2
      (mem_centralizer_iff.1 hxW _ ⟨u, hu, rfl⟩).symm
    rwa [he', MulEquiv.symm_apply_apply] at h
  obtain ⟨r, hr, hβ⟩ := exists_conj_eq_of_fix_projRad i _ hfix
  have haA : F.φ r ∈ A := F.mem_A r
  have hcent : (F.φ r)⁻¹ * x ∈ centralizer (A : Set G) := by
    refine inv_mul_mem_centralizer e' haA hxN ?_
    rw [hβ]
    congr 1
    exact (MulEquiv.eq_symm_apply _).2 rfl
  rw [show x = F.φ r * ((F.φ r)⁻¹ * x) by group]
  exact mul_mem_sup ⟨r, hr, rfl⟩ hcent

theorem act_sq_eq_one (e : A ≃* projectiveSL 3 K) {y : G} (hyN : y ∈ normalizer (A : Set G))
    (hy2 : y * y = 1) : act e ⟨y, hyN⟩ ^ 2 = 1 := by
  rw [sq, ← map_mul]
  have : (⟨y, hyN⟩ : normalizer (A : Set G)) * ⟨y, hyN⟩ = 1 := Subtype.ext hy2
  rw [this, map_one]

theorem outer_fuse_of_mulEquiv [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : A ≃* projectiveSL 3 K) {y : G} (hyN : y ∈ normalizer (A : Set G)) (hy2 : y * y = 1)
    (hout : y ∉ A ⊔ centralizer (A : Set G)) {c : G} (hc : c ∈ A) (hyc : y * c * (y * c) = 1) :
    ∃ b ∈ A, b * y * b⁻¹ = y * c := by
  have hαout : act e ⟨y, hyN⟩ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
    fun h => hout ((act_mem_range_iff e hyN).1 h)
  have hL := isLangSurjective_of_not_mem_range hf hK (act_sq_eq_one e hyN hy2) hαout
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hz : act e ⟨y, hyN⟩ (e ⟨c, hc⟩) = (e ⟨c, hc⟩)⁻¹ := by
    apply e.symm.injective
    apply Subtype.ext
    rw [coe_symm_act_apply, MulEquiv.symm_apply_apply, ← map_inv, MulEquiv.symm_apply_apply]
    change y * c * y⁻¹ = c⁻¹
    rw [hyinv, eq_inv_iff_mul_eq_one, ← hyc]
    group
  obtain ⟨p, hp⟩ := hL _ hz
  have hp' : ((e.symm ((act e ⟨y, hyN⟩ p)⁻¹ * p) : A) : G) = c := by
    rw [hp, MulEquiv.symm_apply_apply]
  rw [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, coe_symm_act_apply] at hp'
  set a : G := (e.symm p : G) with ha
  have hc' : c = y * a⁻¹ * y⁻¹ * a := by
    rw [← hp']
    change (y * a * y⁻¹)⁻¹ * a = _
    group
  refine ⟨a⁻¹, A.inv_mem (e.symm p).2, ?_⟩
  rw [hc', hyinv]
  calc a⁻¹ * y * a⁻¹⁻¹ = (y * y) * (a⁻¹ * y * a) := by rw [hy2, one_mul, inv_inv]
    _ = y * (y * a⁻¹ * y * a) := by group

theorem outer_perfect_of_mulEquiv [Finite K] {f : ℕ} (hf : 3 ≤ f) (hK : Nat.card K = 2 ^ f)
    (e : A ≃* projectiveSL 3 K) {y : G} (hyN : y ∈ normalizer (A : Set G)) (hy2 : y * y = 1)
    (hout : y ∉ A ⊔ centralizer (A : Set G)) :
    ∃ D : Subgroup G, D ≤ A ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, orderOf c = 2 := by
  have hαout : act e ⟨y, hyN⟩ ∉
      (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
    fun h => hout ((act_mem_range_iff e hyN).1 h)
  obtain ⟨D₀, hfix, hperf, c₀, hc₀, hord⟩ :=
    exists_perfect_of_not_mem_range hf hK (act_sq_eq_one e hyN hy2) hαout
  let ι : projectiveSL 3 K →* G := A.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := A.subtype_injective.comp e.symm.injective
  refine ⟨D₀.map ι, ?_, by rw [← map_commutator, hperf], ι c₀, ⟨c₀, hc₀, rfl⟩, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨(e.symm p).2, mem_centralizer_singleton_iff.2 ?_⟩
    have h := hfix p hp
    rw [← MulEquiv.apply_symm_apply e p, act_apply_eq_iff] at h
    exact h.symm
  · rw [orderOf_injective ι hι, hord]

end Transport

section Perfect

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {K : Type} [Field K] [Finite K]

theorem perfect_inv_of_mulEquiv (e : A ≃* projectiveSL 3 K)
    (hcyc : ∀ S : Sylow 2 (centralizer (A : Set G)), IsCyclic ↥S)
    {D : Subgroup G} (hDN : D ≤ normalizer (A : Set G)) (hD : ⁅D, D⁆ = D) {c : G} (hc : c ∈ D)
    (hc2 : c * c = 1) : c ∈ A := by
  have hDperf : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hD
  let f : ↥D →* MulAut (projectiveSL 3 K) := (act e).comp (Subgroup.inclusion hDN)
  have hfperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hfle := le_range_conj_of_commutator_eq (Subgroup.isPerfect_iff.mp hfperf)
  have hDAK : ∀ d ∈ D, d ∈ A ⊔ centralizer (A : Set G) := fun d hd =>
    (act_mem_range_iff e (hDN hd)).1 (hfle ⟨⟨d, hd⟩, rfl⟩)
  let N₀ : Subgroup G := normalizer (A : Set G)
  let A' : Subgroup ↥N₀ := A.subgroupOf N₀
  have hA'n : A'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl
  let q : ↥N₀ →* ↥N₀ ⧸ A' := QuotientGroup.mk' A'
  have hKN : centralizer (A : Set G) ≤ N₀ := Subgroup.centralizer_le_normalizer _
  let φ : ↥(centralizer (A : Set G)) →* ↥N₀ ⧸ A' := q.comp (Subgroup.inclusion hKN)
  have hQcyc : ∀ T : Sylow 2 ↥φ.range, IsCyclic ↥T :=
    OddStandard.Seitz77.cyclic_sylow_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
      hcyc
  let f₂ : ↥D →* ↥N₀ ⧸ A' := q.comp (Subgroup.inclusion hDN)
  have hf₂ : ∀ x : ↥D, f₂ x ∈ φ.range := by
    rintro ⟨d, hd⟩
    obtain ⟨a, ha, k, hk, hdak⟩ := OddStandard.Seitz77.mem_sup_of_commute
      (fun a ha k hk => mem_centralizer_iff.mp hk a ha) (hDAK d hd)
    refine ⟨⟨k, hk⟩, ?_⟩
    have h1 : (⟨d, hDN hd⟩ : ↥N₀) = ⟨a, le_normalizer ha⟩ * ⟨k, hKN hk⟩ := Subtype.ext hdak
    have h2 : q ⟨a, le_normalizer ha⟩ = 1 := (QuotientGroup.eq_one_iff _).2 ha
    change q ⟨k, hKN hk⟩ = q ⟨d, hDN hd⟩
    rw [h1, map_mul, h2, one_mul]
  let g : ↥D →* ↥φ.range := f₂.codRestrict φ.range hf₂
  have hgperf : Group.IsPerfect ↥g.range := Group.IsPerfect.range g
  have hodd : Odd (Nat.card ↥g.range) :=
    OddStandard.Seitz77.odd_card_of_isPerfect_of_cyclic_sylow hgperf
      (OddStandard.Seitz77.cyclic_sylow_of_le hQcyc g.range)
  let y : ↥g.range := ⟨g ⟨c, hc⟩, ⟨_, rfl⟩⟩
  have hy2 : y * y = 1 := by
    apply Subtype.ext
    change g ⟨c, hc⟩ * g ⟨c, hc⟩ = 1
    rw [← map_mul]
    have : (⟨c, hc⟩ : ↥D) * ⟨c, hc⟩ = 1 := Subtype.ext hc2
    rw [this, map_one]
  have hy1 : y = 1 := by
    have h1 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy2)
    have h2 : orderOf y ∣ Nat.card ↥g.range := orderOf_dvd_natCard y
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      exact absurd hodd (Nat.not_odd_iff_even.2 (even_iff_two_dvd.2 h2))
  have hg1 : g ⟨c, hc⟩ = 1 := congrArg Subtype.val hy1
  have hq1 : q ⟨c, hDN hc⟩ = 1 := congrArg Subtype.val hg1
  exact (QuotientGroup.eq_one_iff (N := A') _).1 hq1

end Perfect

section Elem

variable {G : Type*} [Group G]

structure SylowSetting (A S : Subgroup G) (t : G) : Prop where
  le_normalizer : S ≤ normalizer (A : Set G)
  le_centralizer : S ≤ centralizer ({t} : Set G)
  t_mem : t ∈ S
  t_mem_centralizer : t ∈ centralizer (A : Set G)
  t_mul_self : t * t = 1
  t_ne_one : t ≠ 1
  eq_of_mem : ∀ r ∈ S ⊓ centralizer (A : Set G), r * r = 1 → r = 1 ∨ r = t
  sylow : IsSylowOf 2 (S ⊓ A) A

namespace SylowSetting

variable {A S E : Subgroup G} {t : G} {q : ℕ}

theorem of_datum [Finite G] (d : OddStandard.Seitz77.Datum A) : SylowSetting A d.P d.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : d.t * d.t = 1 := by
    rw [← sq, ← d.sector.t_order, pow_orderOf_eq_one]
  refine ⟨d.P_le_normalizer, d.P_le_centralizer, d.t_mem_P,
    OddStandard.t_mem_centralizer d.sector, ht2, fun h => ?_, fun r hr hr2 => ?_,
    d.hP.inf_of_le_normalizer Subgroup.le_normalizer le_rfl⟩
  · have := d.sector.t_order
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  · by_cases hr1 : r = 1
    · exact Or.inl hr1
    · refine Or.inr (OddStandard.eq_t_of_orderOf_eq_two d.sector ?_ ?_)
      · rw [← d.P_inf_centralizer_eq]
        exact hr
      · exact orderOf_eq_prime (by rw [sq]; exact hr2) hr1

theorem t_not_mem [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) : t ∉ A := by
  intro hA
  have hmem : t ∈ A ⊓ centralizer (A : Set G) := ⟨hA, hd.t_mem_centralizer⟩
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hd.t_mul_self) hd.t_ne_one
  have hdvd : 2 ∣ Nat.card ↥(A ⊓ centralizer (A : Set G)) := by
    have h := orderOf_dvd_natCard (⟨t, hmem⟩ : ↥(A ⊓ centralizer (A : Set G)))
    simpa [Subgroup.orderOf_coe, ht2] using h
  exact (Nat.not_even_iff_odd.mpr F.odd_inf) (even_iff_two_dvd.mpr hdvd)

theorem comm_t (hd : SylowSetting A S t) {x : G} (hx : x ∈ S) : x * t = t * x :=
  mem_centralizer_singleton_iff.1 (hd.le_centralizer hx)

theorem mem_V_or [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) {x : G}
    (hxS : x ∈ S) (hxA : x ∈ A ⊔ centralizer (A : Set G)) (hx2 : x * x = 1) :
    x ∈ S ⊓ A ∨ x * t ∈ S ⊓ A := by
  let fact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, k, hk, rfl⟩ := OddStandard.Seitz77.mem_sup_of_commute
    (fun a ha k hk => mem_centralizer_iff.mp hk a ha) hxA
  have hak : a * k = k * a := mem_centralizer_iff.1 hk a ha
  let a₂ : G := Group.pSingular 2 a
  let k₂ : G := Group.pSingular 2 k
  have ha₂A : a₂ ∈ A := by
    dsimp [a₂, Group.pSingular]
    exact A.zpow_mem ha _
  have hk₂ : k₂ ∈ centralizer (A : Set G) := by
    dsimp [k₂, Group.pSingular]
    exact (centralizer (A : Set G)).zpow_mem hk _
  have hcomm₂ : Commute a₂ k₂ := by
    dsimp [a₂, k₂, Group.pSingular]
    exact Commute.zpow_zpow hak _ _
  have hsing : IsPSingular 2 (a * k) := by
    have hdvd : orderOf (a * k) ∣ 2 := by
      exact orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx2)
    have hdvd' : orderOf (a * k) ∣ 2 ^ 1 := by simpa using hdvd
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow (p := 2) (m := 1) Nat.prime_two).mp hdvd'
    exact ⟨n, hn⟩
  have hdecomp : Group.pSingular 2 (a * k) =
      Group.pSingular 2 a * Group.pSingular 2 k :=
    Group.pSingular.mul_of_commute (p := 2) (isOfFinOrder_of_finite a)
      (isOfFinOrder_of_finite k) hak
  have hself : Group.pSingular 2 (a * k) = a * k :=
    Group.pSingular_eq_self_of_isPSingular (p := 2) (isOfFinOrder_of_finite (a * k)) hsing
  have hdecomp' : a * k = a₂ * k₂ := by
    calc a * k = Group.pSingular 2 (a * k) := hself.symm
      _ = Group.pSingular 2 a * Group.pSingular 2 k := hdecomp
      _ = a₂ * k₂ := rfl
  have hx2' : (a₂ * k₂) * (a₂ * k₂) = 1 := by
    rw [← hdecomp']
    exact hx2
  have haa : a₂ * a₂ = (k₂ * k₂)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← hx2']
    calc a₂ * a₂ * (k₂ * k₂) = a₂ * (a₂ * k₂) * k₂ := by group
      _ = a₂ * (k₂ * a₂) * k₂ := by rw [hcomm₂.eq]
      _ = (a₂ * k₂) * (a₂ * k₂) := by group
  have h2sing_sq : IsPSingular 2 (a₂ * a₂) := by
    rcases (Group.isPSingular_pSingular (p := 2) a) with ⟨n, hn⟩
    have hdvd : orderOf (a₂ * a₂) ∣ 2 ^ n := by
      rw [← hn]
      simpa [sq] using orderOf_pow_dvd (x := a₂) 2
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨m, hm⟩
  have hmem₂ : a₂ * a₂ ∈ A ⊓ centralizer (A : Set G) := by
    refine ⟨mul_mem ha₂A ha₂A, ?_⟩
    rw [haa]
    exact (centralizer (A : Set G)).inv_mem (mul_mem hk₂ hk₂)
  have hdvdCard : orderOf (a₂ * a₂) ∣
      Nat.card ↥(A ⊓ centralizer (A : Set G)) := by
    have h := orderOf_dvd_natCard (⟨a₂ * a₂, hmem₂⟩ :
      ↥(A ⊓ centralizer (A : Set G)))
    simpa [Subgroup.orderOf_coe] using h
  have hoddElem : Odd (orderOf (a₂ * a₂)) := F.odd_inf.of_dvd_nat hdvdCard
  have ha22 : a₂ * a₂ = 1 := by
    rcases h2sing_sq with ⟨n, hn⟩
    have hcop : Nat.Coprime (orderOf (a₂ * a₂)) (2 ^ n) := by
      simpa [hn] using hoddElem.coprime_two_right.pow_right n
    have hdvd : orderOf (a₂ * a₂) ∣ 2 ^ n := by rw [hn]
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)
  have hk22 : k₂ * k₂ = 1 := by
    rw [ha22, eq_comm, inv_eq_one] at haa
    exact haa
  have hn : ∀ v ∈ S ⊓ A, a₂ * v * a₂⁻¹ ∈ S ⊓ A := by
    intro v hv
    have hkv : k₂ * v * k₂⁻¹ = v := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_iff.1 hk₂ v hv.2).symm
    have h1 : a₂ * v * a₂⁻¹ = (a₂ * k₂) * v * (a₂ * k₂)⁻¹ := by
      calc a₂ * v * a₂⁻¹ = a₂ * (k₂ * v * k₂⁻¹) * a₂⁻¹ := by rw [hkv]
        _ = (a₂ * k₂) * v * (a₂ * k₂)⁻¹ := by group
    rw [h1, ← hdecomp']
    exact ⟨S.mul_mem (S.mul_mem hxS hv.1) (S.inv_mem hxS),
      (mem_normalizer_iff.1 (hd.le_normalizer hxS) v).1 hv.2⟩
  have haV : a₂ ∈ S ⊓ A :=
    OddStandard.Seitz77.mem_of_mul_self_of_normalizes hd.sylow ha₂A ha22 hn
  have hkS : k₂ ∈ S ⊓ centralizer (A : Set G) := by
    refine ⟨?_, hk₂⟩
    have := S.mul_mem (S.inv_mem (mem_inf.1 haV).1) hxS
    rw [hdecomp'] at this
    rwa [inv_mul_cancel_left] at this
  rcases hd.eq_of_mem k₂ hkS hk22 with hk1 | hkt
  · refine Or.inl ?_
    rw [hdecomp', hk1, mul_one]
    exact haV
  · refine Or.inr ?_
    rw [hdecomp', hkt, mul_assoc, hd.t_mul_self, mul_one]
    exact haV

theorem card_adj [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) {W : Subgroup G}
    (hW : W ≤ S ⊓ A) :
    Nat.card ↥(W ⊔ zpowers t) = 2 * Nat.card W := by
  have hc : ∀ v ∈ W, v * t = t * v := fun v hv => hd.comm_t (hW hv).1
  have h := OddStandard.Seitz77.card_eq_two_mul_card_inf (F := W ⊔ zpowers t) (V := W) (t := t)
    (mem_sup_right (mem_zpowers _)) (fun h => hd.t_not_mem F (hW h).2)
    fun x hx => (OddStandard.Seitz77.mem_sup_zpowers_iff hc hd.t_mul_self).mp hx
  rwa [inf_eq_right.mpr le_sup_left] at h

theorem elem_eq_adj [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) (hq : 4 < q)
    {V₁ V₂ : Subgroup G}
    (hR : Radicals (S ⊓ A) V₁ V₂ q) (hES : E ≤ S) (hE : IsElemAbelian 2 E)
    (hcard : 2 * q ^ 2 ≤ Nat.card E) : E = V₁ ⊔ zpowers t ∨ E = V₂ ⊔ zpowers t := by
  have hcomm : ∀ e ∈ E, e * t = t * e := fun e he => hd.comm_t (hES he)
  have hF : IsElemAbelian 2 (E ⊔ zpowers t) :=
    OddStandard.Seitz77.isElemAbelian_sup_zpowers hE hcomm hd.t_mul_self
  have hFS : E ⊔ zpowers t ≤ S := sup_le hES ((zpowers_le).mpr hd.t_mem)
  have hFcard : 2 * q ^ 2 ≤ Nat.card ↥(E ⊔ zpowers t) :=
    hcard.trans (Subgroup.card_le_of_le le_sup_left)
  have hFK : Nat.card ↥((E ⊔ zpowers t) ⊓ centralizer (A : Set G)) ≤ 2 := by
    have hle : (E ⊔ zpowers t) ⊓ centralizer (A : Set G) ≤ zpowers t := by
      intro y hy
      have hy2 : y * y = 1 := by rw [← sq]; exact hF.2 y hy.1
      rcases hd.eq_of_mem y ⟨hFS hy.1, hy.2⟩ hy2 with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    have h := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hd.t_mul_self) hd.t_ne_one] at h
    exact h
  have hFA : E ⊔ zpowers t ≤ A ⊔ centralizer (A : Set G) := by
    refine F.elem_inner _ (hFS.trans hd.le_normalizer) hF ?_
    have h1 : 4 * q * Nat.card ↥((E ⊔ zpowers t) ⊓ centralizer (A : Set G)) ≤ 4 * q * 2 :=
      Nat.mul_le_mul_left _ hFK
    nlinarith
  have hFV : ∀ y ∈ E ⊔ zpowers t, y ∈ S ⊓ A ∨ y * t ∈ S ⊓ A := fun y hy =>
    hd.mem_V_or F (hFS hy) (hFA hy) (by rw [← sq]; exact hF.2 y hy)
  have h2 := OddStandard.Seitz77.card_eq_two_mul_card_inf (F := E ⊔ zpowers t) (V := S ⊓ A)
    (t := t) (mem_sup_right (mem_zpowers _)) (fun h => hd.t_not_mem F h.2) hFV
  have hel : IsElemAbelian 2 ((E ⊔ zpowers t) ⊓ (S ⊓ A)) := IsElemAbelian.mono hF inf_le_left
  have key : ∀ W : Subgroup G, W ≤ S ⊓ A → Nat.card W = q ^ 2 →
      (E ⊔ zpowers t) ⊓ (S ⊓ A) ≤ W → E = W ⊔ zpowers t := by
    intro W hWV hWc hle
    have hEq : (E ⊔ zpowers t) ⊓ (S ⊓ A) = W :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hWc]; omega)
    have hFW : E ⊔ zpowers t ≤ W ⊔ zpowers t := by
      intro y hy
      have hc : ∀ v ∈ W, v * t = t * v := fun v hv => hd.comm_t (hWV hv).1
      rw [OddStandard.Seitz77.mem_sup_zpowers_iff hc hd.t_mul_self]
      rcases hFV y hy with h | h
      · exact Or.inl (by rw [← hEq]; exact ⟨hy, h⟩)
      · exact Or.inr (by rw [← hEq]; exact ⟨mul_mem hy (mem_sup_right (mem_zpowers _)), h⟩)
    have hWc2 : Nat.card ↥(W ⊔ zpowers t) = 2 * q ^ 2 := by rw [hd.card_adj F hWV, hWc]
    exact Subgroup.eq_of_le_of_card_ge (le_sup_left.trans hFW) (by rw [hWc2]; exact hcard)
  rcases hR.le_of_elem _ inf_le_right hel with h | h
  · exact Or.inl (key V₁ hR.le₁ hR.card₁ h)
  · exact Or.inr (key V₂ hR.le₂ hR.card₂ h)

theorem adj_properties [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) {V₁ V₂ W : Subgroup G}
    (hR : Radicals (S ⊓ A) V₁ V₂ q) (hW : W = V₁ ∨ W = V₂) :
    W ⊔ zpowers t ≤ S ∧ IsElemAbelian 2 (W ⊔ zpowers t) ∧
      Nat.card ↥(W ⊔ zpowers t) = 2 * q ^ 2 := by
  obtain ⟨hWV, hWe, hWc⟩ := hR.property hW
  refine ⟨sup_le (hWV.trans inf_le_left) ((zpowers_le).mpr hd.t_mem),
    OddStandard.Seitz77.isElemAbelian_sup_zpowers hWe (fun e he => hd.comm_t (hWV he).1)
      hd.t_mul_self, by rw [hd.card_adj F hWV, hWc]⟩

theorem card_elem_le [Finite G] (F : FusionFacts A q) (hd : SylowSetting A S t) (hq : 4 < q)
    {V₁ V₂ : Subgroup G}
    (hR : Radicals (S ⊓ A) V₁ V₂ q) (hES : E ≤ S) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 * q ^ 2 := by
  by_contra hlt
  push Not at hlt
  rcases hd.elem_eq_adj F hq hR hES hE hlt.le with h | h
  · have := (hd.adj_properties F hR (Or.inl rfl)).2.2
    rw [← h] at this
    omega
  · have := (hd.adj_properties F hR (Or.inr rfl)).2.2
    rw [← h] at this
    omega

end SylowSetting

end Elem

namespace Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {f : ℕ}

theorem exists_mulEquiv (h : Hyp G A f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (A ≃* projectiveSL 3 K) :=
  LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h.model

theorem exists_model (h : Hyp G A f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ f ∧
      Nonempty (A ≃* projectiveSL 3 K) := by
  obtain ⟨K, _, _, hK, he⟩ := h.exists_mulEquiv
  have hf1 : 1 ≤ f := by have := h.three_le; omega
  exact ⟨K, inferInstance, inferInstance,
    finite_field_prime_power_characteristic Nat.prime_two hf1 hK, hK, he⟩

theorem exists_datum (h : Hyp G A f) : Nonempty (OddStandard.Seitz77.Datum A) := by
  classical
  have hCeven : 2 ∣ Nat.card (centralizer (A : Set G)) :=
    even_iff_two_dvd.mp h.even_card_centralizer
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set G)) 2 hCeven
  have hcp : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc, pow_one])
  obtain ⟨R, hcR⟩ := hcp.exists_le_sylow
  have hcR' : c ∈ (R : Subgroup (centralizer (A : Set G))) := hcR (mem_zpowers c)
  have hsec : OddStandard.Sector A R (c : G) :=
    ⟨h.standard, h.cyc R, ⟨c, hcR', rfl⟩, by rw [Subgroup.orderOf_coe, hc]⟩
  have hRN : IsPGroup 2 ((OddStandard.sg A R).subgroupOf (normalizer (A : Set G))) :=
    OddStandard.isPGroup_sg.comap_subtype
  obtain ⟨Q, hQ⟩ := hRN.exists_le_sylow
  refine ⟨⟨R, c, hsec, (Q : Subgroup (normalizer (A : Set G))).map
    (normalizer (A : Set G)).subtype, ⟨Q, rfl⟩, ?_⟩⟩
  intro x hx
  exact ⟨⟨x, OddStandard.sg_le_normalizer hx⟩, hQ (mem_subgroupOf.mpr hx), rfl⟩

theorem facts (h : Hyp G A f) : Facts A (2 ^ f) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h.exists_mulEquiv
  have hf3 := h.three_le
  have hf1 : 1 ≤ f := by omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf1 hK
  rw [← hK]
  refine ⟨h.inf_centralizer_eq_bot,
    fun x hx y hy hx2 hy2 => exists_conj_of_mulEquiv e hx hy hx2 hy2,
    fun E hEN hE hcard => elem_inner_of_mulEquiv hf1 hK e hEN hE hcard,
    fun V hV => cent_sylow_of_mulEquiv e hV,
    fun V V₁ V₂ hV hR W hW => cent_radical_of_mulEquiv e hV hR hW,
    fun V hV => exists_radicals_of_mulEquiv e hV,
    fun V V₁ V₂ hV hR W hW => ⟨K, inferInstance, rfl, exists_leviData e hV hR hW⟩,
    fun y hyN hy2 hout c hc hyc => outer_fuse_of_mulEquiv hf1 hK e hyN hy2 hout hc hyc,
    fun y hyN hy2 hout => outer_perfect_of_mulEquiv hf3 hK e hyN hy2 hout,
    fun D hDN hD c hc hc2 => perfect_inv_of_mulEquiv e (fun S => h.cyc S) hDN hD hc hc2⟩

end Hyp

end CFSG.LocalAnalysis.EvenBN.LinearThree
