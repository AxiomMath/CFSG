module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidCore4

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

section Beta

variable {K : Type} [Field K] [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)} {s : K} (hs : s + h.bar s = 1) {p : G}
  {Θ : ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) →* stabE (ε := 2) h}
  (hΘ : ∀ x, psiU h (isHypTransport_uFrame h (le_refl 2) hs) (Θ x) =
    θ (Subgroup.inclusion (perfectCore_inf_le A p) x))
include hΘ

theorem exists_beta_conjAut (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    (hΘs : Function.Surjective Θ) {x : G}
    (hXx : rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) x =
      perfectCore (A ⊓ centralizer ({p} : Set G))) :
    ∃ β : MulAut (stabE (ε := 2) h), ∀ y, β (Θ y) = Θ (conjAut hXx y) := by
  have hXA := perfectCore_inf_le A p
  refine exists_mulAut_comp_eq_of_ker Θ hΘs (conjAut hXx) fun y hy => ?_
  have hyA : Subgroup.inclusion hXA y ∈ center ↥A := by
    rw [← hker, MonoidHom.mem_ker, ← hΘ, hy, map_one]
  have hyc : y ∈ center ↥(perfectCore (A ⊓ centralizer ({p} : Set G))) := by
    rw [mem_center_iff]
    intro z
    apply Subgroup.inclusion_injective hXA
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hyA _
  have hyo : Odd (orderOf y) := by
    rw [← orderOf_injective (Subgroup.inclusion hXA) (Subgroup.inclusion_injective hXA) y]
    have h1 := orderOf_dvd_natCard (⟨_, hyA⟩ : center ↥A)
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hodd h1
  refine theta_eq_one_of_mem_center h hΘs (mulAut_mem_center (conjAut hXx) hyc) ?_
  rwa [MulEquiv.orderOf_eq]

variable {x : G} {hXx : rightConjugate (perfectCore (A ⊓ centralizer ({p} : Set G))) x =
    perfectCore (A ⊓ centralizer ({p} : Set G))}
  {β : MulAut (stabE (ε := 2) h)} (hβ : ∀ y, β (Θ y) = Θ (conjAut hXx y))
  {a : G} (haA : a ∈ A) (hap : a ∈ centralizer ({p} : Set G)) {c : rootsOfUnity (2 ^ f + 1) K}
  (hθa : θ ⟨a, haA⟩ = uProj K (2 + 2) f (torusU K f c))
  (heN : x⁻¹ * a * x ∈ normalizer (A : Set G)) (hep : x⁻¹ * a * x ∈ centralizer ({p} : Set G))
include hβ hap hθa heN hep

theorem theta_conj_rightConjugate (y : ↥(perfectCore (A ⊓ centralizer ({p} : Set G)))) :
    Θ ⟨x⁻¹ * a * x * y * (x⁻¹ * a * x)⁻¹, conj_mem_perfectCore heN hep y.2⟩ =
      β (tconj h (le_refl 2) hs c (β.symm (Θ y))) := by
  set y' := (conjAut hXx).symm y
  have hy' : conjAut hXx y' = y := MulEquiv.apply_symm_apply _ _
  have h1 : β.symm (Θ y) = Θ y' := by
    rw [← hy', ← hβ, MulEquiv.symm_apply_apply]
  have h2 := theta_conj_eq_tconj h hs hΘ haA hap hθa y'
  have h3 : conjAut hXx ⟨a * y' * a⁻¹, conj_mem_perfectCore (Subgroup.le_normalizer haA) hap
      y'.2⟩ = ⟨x⁻¹ * a * x * y * (x⁻¹ * a * x)⁻¹, conj_mem_perfectCore heN hep y.2⟩ := by
    apply Subtype.ext
    have e : (y : G) = x⁻¹ * y' * x := by rw [← hy', coe_conjAut]
    rw [coe_conjAut]
    change x⁻¹ * (a * y' * a⁻¹) * x = x⁻¹ * a * x * y * (x⁻¹ * a * x)⁻¹
    rw [e]
    group
  rw [← h3, ← hβ, h2, h1]

theorem exists_alpha_tconj (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A)
    (hΘs : Function.Surjective Θ) :
    ∃ α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K)),
      (∀ g, psiU h (isHypTransport_uFrame h (le_refl 2) hs)
        (β (tconj h (le_refl 2) hs c (β.symm g))) =
          α (psiU h (isHypTransport_uFrame h (le_refl 2) hs) g)) ∧
      ∃ γ : MulAut ↥A, (∀ a' : ↥A, ((γ a' : ↥A) : G) = x⁻¹ * a * x * a' * (x⁻¹ * a * x)⁻¹) ∧
        ∀ a', α (θ a') = θ (γ a') := by
  obtain ⟨γ, hγ, α, hα⟩ := exists_alpha_of_normalizer hθ hker heN
  refine ⟨α, fun g => ?_, γ, hγ, hα⟩
  obtain ⟨y, rfl⟩ := hΘs g
  rw [← theta_conj_rightConjugate h hs hΘ hβ haA hap hθa heN hep y, hΘ, hΘ, hα]
  congr 1
  apply Subtype.ext
  rw [hγ]
  rfl

theorem tconj_fix_map_stdW {W : Subgroup G}
    (hWX : W ≤ perfectCore (A ⊓ centralizer ({p} : Set G)))
    (hWstd : (W.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ = stdW h)
    (haW : ∀ w ∈ W, a * w = w * a) :
    ∀ g ∈ (stdW h).map β.toMonoidHom, β (tconj h (le_refl 2) hs c (β.symm g)) = g := by
  have hWxX : rightConjugate W x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hWX).trans hXx.le
  rintro _ ⟨g, hg, rfl⟩
  rw [← hWstd] at hg
  obtain ⟨⟨w, hwX⟩, hw, rfl⟩ := hg
  have e1 : β.toMonoidHom (Θ ⟨w, hwX⟩) = Θ ⟨x⁻¹ * w * x, hWxX ⟨w, hw, by simp⟩⟩ := by
    change β (Θ ⟨w, hwX⟩) = _
    rw [hβ]
    congr 1
    exact Subtype.ext (coe_conjAut hXx _)
  rw [e1, ← theta_conj_rightConjugate h hs hΘ hβ haA hap hθa heN hep]
  congr 1
  apply Subtype.ext
  change x⁻¹ * a * x * (x⁻¹ * w * x) * (x⁻¹ * a * x)⁻¹ = x⁻¹ * w * x
  have hw' : a * w = w * a := haW w hw
  calc x⁻¹ * a * x * (x⁻¹ * w * x) * (x⁻¹ * a * x)⁻¹ = x⁻¹ * (a * w) * a⁻¹ * x := by group
    _ = x⁻¹ * (w * a) * a⁻¹ * x := by rw [hw']
    _ = x⁻¹ * w * x := by group

end Beta

section FixP

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ} (h : UnitaryFieldData 2 f K)

include h in
theorem fix_conj_uBarL {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))} {m : ℕ}
    (hm : Odd m) (hαm : α ^ m = 1) (y : StatedProj (StatedSU (2 + 2) (2 ^ f) K))
    (hW : ∀ u ∈ (uBarW K 2 f).map (MulAut.conj y).toMonoidHom, α u = u)
    (hN : ∀ S : StatedSU 2 (2 ^ f) K, (S : GL (Fin 2) K).val = 1 + onesM →
      y * uProj K (2 + 2) f (uL K 2 f S) * y⁻¹ = uProj K (2 + 2) f (uL K 2 f S) ∧
        α (uProj K (2 + 2) f (uL K 2 f S)) = uProj K (2 + 2) f (uL K 2 f S)) :
    ∀ u ∈ (uBarL K 2 f).map (MulAut.conj y).toMonoidHom, α u = u := by
  set α' := (MulAut.conj y)⁻¹ * α * MulAut.conj y with hα'
  have hα'app : ∀ z, α' z = y⁻¹ * α (y * z * y⁻¹) * y := fun z => by
    simp only [hα', MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
  have hα'W : ∀ w ∈ uBarW K 2 f, α' w = w := by
    intro w hw
    rw [hα'app, hW (y * w * y⁻¹) ⟨w, hw, rfl⟩]
    group
  have hα'N : ∀ S : StatedSU 2 (2 ^ f) K, (S : GL (Fin 2) K).val = 1 + onesM →
      α' (uProj K (2 + 2) f (uL K 2 f S)) = uProj K (2 + 2) f (uL K 2 f S) := by
    intro S hS
    obtain ⟨h1, h2⟩ := hN S hS
    rw [hα'app, h1, h2]
    calc y⁻¹ * uProj K (2 + 2) f (uL K 2 f S) * y =
        y⁻¹ * (y * uProj K (2 + 2) f (uL K 2 f S) * y⁻¹) * y := by rw [h1]
      _ = uProj K (2 + 2) f (uL K 2 f S) := by group
  have hα'm : α' ^ m = 1 := by
    rw [hα', show (MulAut.conj y)⁻¹ * α * MulAut.conj y =
      (MulAut.conj y)⁻¹ * α * (MulAut.conj y)⁻¹⁻¹ by rw [inv_inv], conj_pow, hαm, mul_one,
      mul_inv_cancel]
  have hα'L := fix_uBarL_of_fix_four h hm hα'm hα'W hα'N
  rintro _ ⟨l₀, hl₀, rfl⟩
  have h1 := hα'L l₀ hl₀
  rw [hα'app] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc α (y * l₀ * y⁻¹) = y * (y⁻¹ * α (y * l₀ * y⁻¹) * y) * y⁻¹ := by group
    _ = y * l₀ * y⁻¹ := by rw [h1]

end FixP

section DxL

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}

include h in
theorem conj_commute_of_levLift (hf : 2 ≤ f) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hodd : Odd (Nat.card (center ↥A))) {x a : G}
    (ha : a ∈ liftSub θ (uBarT K f)) {y : StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    {α : MulAut (StatedProj (StatedSU (2 + 2) (2 ^ f) K))} {γ : MulAut ↥A}
    (hγ : ∀ a' : ↥A, ((γ a' : ↥A) : G) = x⁻¹ * a * x * a' * (x⁻¹ * a * x)⁻¹)
    (hαγ : ∀ a', α (θ a') = θ (γ a'))
    (hW : ∀ u ∈ (uBarW K 2 f).map (MulAut.conj y).toMonoidHom, α u = u)
    (hN : ∀ S : StatedSU 2 (2 ^ f) K, (S : GL (Fin 2) K).val = 1 + onesM →
      y * uProj K (2 + 2) f (uL K 2 f S) * y⁻¹ = uProj K (2 + 2) f (uL K 2 f S) ∧
        α (uProj K (2 + 2) f (uL K 2 f S)) = uProj K (2 + 2) f (uL K 2 f S))
    {l : G} (hl : l ∈ levLift θ ((uBarL K 2 f).map (MulAut.conj y).toMonoidHom)) :
    x⁻¹ * a * x * l = l * (x⁻¹ * a * x) := by
  have hγpow : ∀ n : ℕ, ∀ a' : ↥A, (((γ ^ n) a' : ↥A) : G) =
      (x⁻¹ * a * x) ^ n * a' * ((x⁻¹ * a * x) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro a'; simp
    | succ n ih =>
      intro a'
      rw [show γ ^ (n + 1) = γ * γ ^ n from pow_succ' γ n, MulAut.mul_apply, hγ, ih]
      generalize x⁻¹ * a * x = b
      group
  have hγm : γ ^ orderOf a = 1 := by
    apply MulEquiv.ext
    intro a'
    apply Subtype.ext
    have he : (x⁻¹ * a * x) ^ orderOf a = 1 := by
      rw [show x⁻¹ * a * x = MulAut.conj x⁻¹ a by simp, ← map_pow, pow_orderOf_eq_one, map_one]
    rw [hγpow, he, one_mul, inv_one, mul_one]
    rfl
  have hαL := fix_conj_uBarL h (odd_orderOf_of_mem_liftSub_uBarT h hker hodd ha)
    (alpha_pow_eq_one hθ hαγ hγm) y hW hN
  have hLperf : ⁅(uBarL K 2 f).map (MulAut.conj y).toMonoidHom,
      (uBarL K 2 f).map (MulAut.conj y).toMonoidHom⁆ =
        (uBarL K 2 f).map (MulAut.conj y).toMonoidHom := by
    rw [← Subgroup.map_commutator, commutator_uBarL h.card_eq_sq hf (le_refl 2)]
  have hfixl := fix_of_levLift hker hαγ hαL (commutator_levLift hker hθ hLperf) hl
  have h2 : x⁻¹ * a * x * l * (x⁻¹ * a * x)⁻¹ = l := by
    have h3 := congrArg Subtype.val hfixl
    rwa [hγ] at h3
  calc x⁻¹ * a * x * l = x⁻¹ * a * x * l * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * a * x) := by group
    _ = l * (x⁻¹ * a * x) := by rw [h2]

end DxL

section DxW

variable {K : Type} [Field K] {f : ℕ} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}

theorem conj_commute_of_levLift_W (hker : θ.ker = center ↥A) {W : Subgroup G} {x : G}
    (hWxA : rightConjugate W x ≤ A)
    (hWxperf : ⁅rightConjugate W x, rightConjugate W x⁆ = rightConjugate W x)
    {y : StatedProj (StatedSU (2 + 2) (2 ^ f) K)}
    (hθW : ((rightConjugate W x).subgroupOf A).map θ =
      (uBarW K 2 f).map (MulAut.conj y).toMonoidHom)
    {l : G} (hl : l ∈ levLift θ ((uBarL K 2 f).map (MulAut.conj y).toMonoidHom)) {w : G}
    (hw : w ∈ W) :
    x⁻¹ * w * x * l = l * (x⁻¹ * w * x) := by
  have hlA := levLift_le hl
  have h1 := mem_centralizer_of_theta_commute hker hWxA hWxperf (a := ⟨l, hlA⟩) fun z hz => by
    have hθl : θ ⟨l, hlA⟩ ∈ (uBarL K 2 f).map (MulAut.conj y).toMonoidHom :=
      theta_mem_of_mem_levLift hl
    have hθz : θ ⟨z, hWxA hz⟩ ∈ (uBarW K 2 f).map (MulAut.conj y).toMonoidHom := by
      rw [← hθW]
      exact ⟨⟨z, hWxA hz⟩, hz, rfl⟩
    obtain ⟨l₀, hl₀, hl₀e⟩ := hθl
    obtain ⟨w₀, hw₀, hw₀e⟩ := hθz
    rw [← hl₀e, ← hw₀e]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * l₀ * y⁻¹ * (y * w₀ * y⁻¹) = y * (l₀ * w₀) * y⁻¹ := by group
      _ = y * (w₀ * l₀) * y⁻¹ := by rw [uBarW_commute_uBarL hw₀ hl₀]
      _ = y * w₀ * y⁻¹ * (y * l₀ * y⁻¹) := by group
  exact mem_centralizer_iff.mp h1 _ ⟨w, hw, by simp⟩

end DxW

end CFSG.ComponentClassification.RankTwoClassical.URigid
