module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordMatrix
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotPositionB
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect
  map_perfectCore)

section Act

variable {G H : Type*} [Group G] [Group H]

@[expose] def ActsAs (φ : H →* G) (y : G) (β : MulAut H) : Prop :=
  ∀ p, φ (β p) = y * φ p * y⁻¹

theorem ActsAs.mul {φ : H →* G} {y y' : G} {β β' : MulAut H} (h : ActsAs φ y β)
    (h' : ActsAs φ y' β') : ActsAs φ (y * y') (β * β') := by
  intro p
  rw [MulAut.mul_apply, h, h']
  group

theorem ActsAs.one (φ : H →* G) : ActsAs φ 1 1 := by
  intro p
  simp

theorem ActsAs.pow {φ : H →* G} {y : G} {β : MulAut H} (h : ActsAs φ y β) (k : ℕ) :
    ActsAs φ (y ^ k) (β ^ k) := by
  induction k with
  | zero => simpa using ActsAs.one φ
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem ActsAs.pow_eq_one {φ : H →* G} (hφ : Function.Injective φ) {y : G} {β : MulAut H}
    (h : ActsAs φ y β) {k : ℕ} (hk : y ^ k = 1) : β ^ k = 1 := by
  ext p
  apply hφ
  rw [(h.pow k) p, hk, MulAut.one_apply]
  group

theorem ActsAs.conj {φ : H →* G} {y : G} {β : MulAut H} (h : ActsAs φ y β) (c : H) :
    ActsAs (φ.comp (MulAut.conj c).toMonoidHom) y ((MulAut.conj c)⁻¹ * β * MulAut.conj c) := by
  intro p
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.mul_apply]
  rw [MulAut.conj_apply (c) ((MulAut.conj c)⁻¹ (β ((MulAut.conj c) p))), MulAut.conj_inv_apply,
    show c * (c⁻¹ * β ((MulAut.conj c) p) * c) * c⁻¹ = β ((MulAut.conj c) p) by group, h]

theorem ActsAs.mem_fixAut_iff {φ : H →* G} (hφ : Function.Injective φ) {y : G} {β : MulAut H}
    (h : ActsAs φ y β) (p : H) : p ∈ fixAut β ↔ φ p ∈ centralizer ({y} : Set G) := by
  rw [mem_fixAut, mem_centralizer_singleton_iff]
  constructor
  · intro hp
    have h1 := h p
    rw [hp] at h1
    calc φ p * y = y * φ p * y⁻¹ * y := by rw [← h1]
      _ = y * φ p := by group
  · intro hp
    apply hφ
    rw [h p, ← hp, mul_inv_cancel_right]

theorem ActsAs.map_fixAut {φ : H →* G} (hφ : Function.Injective φ) {y : G} {β : MulAut H}
    (h : ActsAs φ y β) : (fixAut β).map φ = φ.range ⊓ centralizer ({y} : Set G) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, rfl⟩, (h.mem_fixAut_iff hφ p).1 hp⟩
  · rintro ⟨⟨p, rfl⟩, hx⟩
    exact ⟨p, (h.mem_fixAut_iff hφ p).2 hx, rfl⟩

theorem ActsAs.map_le_centralizer {φ : H →* G} {y : G} {β : MulAut H} (h : ActsAs φ y β)
    {S : Subgroup H} (hS : S ≤ fixAut β) : S.map φ ≤ centralizer ({y} : Set G) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 := h p
  rw [hS hp] at h1
  calc φ p * y = y * φ p * y⁻¹ * y := by rw [← h1]
    _ = y * φ p := by group

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_actsAs {φ : projectiveSL n K →* G} (hφ : Function.Injective φ) {y : G}
    (hy : y ∈ normalizer (φ.range : Set G)) : ∃ β, ActsAs φ y β := by
  refine ⟨normalizerAut (MonoidHom.ofInjective hφ).symm ⟨y, hy⟩, fun p => ?_⟩
  have h := coe_symm_normalizerAut_apply (MonoidHom.ofInjective hφ).symm ⟨y, hy⟩
    (MonoidHom.ofInjective hφ p)
  rw [MulEquiv.symm_symm, MulEquiv.symm_apply_apply, MonoidHom.ofInjective_apply,
    MonoidHom.ofInjective_apply] at h
  exact h

theorem ActsAs.conj_proj {φ : projectiveSL n K →* G} {y : G} {A : GL (Fin n) K}
    (h : ActsAs φ y (conjAut n K A)) (W : SpecialLinearGroup (Fin n) K) :
    ActsAs (φ.comp (MulAut.conj (proj n K W)).toMonoidHom) y
      (conjAut n K ((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL W)) := by
  have e : conjAut n K ((SpecialLinearGroup.toGL W)⁻¹ * A * SpecialLinearGroup.toGL W) =
      (MulAut.conj (proj n K W))⁻¹ * conjAut n K A * MulAut.conj (proj n K W) := by
    rw [map_mul, map_mul, map_inv, conjAut_toGL]
  rw [e]
  exact h.conj _

end Act

section Common

variable {G : Type*} [Group G] {n : ℕ} {K : Type*} [Field K]

theorem map_inf_centralizer_singleton {H' : Type*} [Group H'] {φ : H' →* G}
    (hφ : Function.Injective φ) (H : Subgroup H') (x : H') :
    (H ⊓ centralizer ({x} : Set H')).map φ = H.map φ ⊓ centralizer ({φ x} : Set G) := by
  ext g
  simp only [mem_map, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h, ⟨hh, hx⟩, rfl⟩
    exact ⟨⟨h, hh, rfl⟩, by rw [← map_mul, ← map_mul, hx]⟩
  · rintro ⟨⟨h, hh, rfl⟩, hx⟩
    exact ⟨h, ⟨hh, hφ (by rw [map_mul, map_mul, hx])⟩, rfl⟩

theorem radicalP_ne_rootGroup (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    (pairPlacement hab).radicalP K ≠ rootGroup hab := by
  obtain ⟨j, hj⟩ : (({a, b} : Finset (Fin n))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
    omega
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  obtain ⟨hja, hjb⟩ := hj
  intro h
  have hmem : proj n K (SpecialLinearGroup.transvection (Ne.symm hja) 1) ∈
      (pairPlacement hab).radicalP K := by
    refine Subgroup.mem_map_of_mem _ ((pairPlacement hab).transvection_mem_radical _ ?_ 1)
    rw [pairPlacement_level_left, pairPlacement_level_of_ne hab hja hjb]
    omega
  rw [h] at hmem
  obtain ⟨c, hc⟩ := (mem_rootGroup hab).1 hmem
  rw [xab, proj_eq_proj_iff] at hc
  obtain ⟨s, -, hs⟩ := mem_scalars.1 hc
  have h1 : ((SpecialLinearGroup.transvection (Ne.symm hja) (1 : K) :
      SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (SpecialLinearGroup.transvection hab c : Matrix (Fin n) (Fin n) K) *
        scalar (Fin n) (s : K) := by
    rw [← hs, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have h2 := congrFun (congrFun h1 a) j
  rw [scalar_apply, mul_diagonal, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.add_apply,
    one_apply_ne (Ne.symm hja), single_apply_same, single_apply,
    ite_eq_right (fun h => hjb h.2.symm), zero_add, add_zero, zero_mul] at h2
  exact one_ne_zero h2

variable [Finite K]

theorem two_le_card_compl_pair (hn : 4 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    2 ≤ (({a, b} : Finset (Fin n))ᶜ).card := by
  rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
  omega

variable {φ φ' : projectiveSL n K →* G}

theorem map_radicalP_eq_of_map_perfectCore_eq [CharP K 2] (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') {a b : Fin n} (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ') :
    ((pairPlacement hab).radicalP K).map φ' = ((pairPlacement hab).radicalP K).map φ := by
  have hJ2 : 2 ≤ (pairPlacement hab).free.card := by
    rw [pairPlacement_free]
    exact two_le_card_compl_pair hn hab
  exact map_radicalP_eq hq hφ hφ' (pairPlacement hab) (pairPlacement hab) hJ2 hJ2
    (by rwa [pairPlacement_elt])

theorem map_rootGroup_eq_of_map_perfectCore_eq [CharP K 2] (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') {a b : Fin n} (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ') :
    (rootGroup (K := K) hab).map φ' = (rootGroup hab).map φ := by
  rw [rootGroup_eq_commutator_radicalP hab (by omega), Subgroup.map_commutator,
    Subgroup.map_commutator, map_radicalP_eq_of_map_perfectCore_eq hq hn hφ hφ' hab hΛ]

theorem sup_map_blockSL_eq_of_map_perfectCore_eq [Finite G] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hn : 4 ≤ n)
    (hφ : Function.Injective φ) (hφ' : Function.Injective φ') {a b : Fin n} (hab : a ≠ b)
    (hΛ : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ') :
    ((pairPlacement hab).radicalP K).map φ ⊔ (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ =
      ((pairPlacement hab).radicalP K).map φ ⊔ (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ' := by
  have hJ2 : 2 ≤ (pairPlacement hab).free.card := by
    rw [pairPlacement_free]
    exact two_le_card_compl_pair hn hab
  have h := sup_map_blockSL_eq hq hφ hφ' (pairPlacement hab) (pairPlacement hab) hJ2 hJ2
    (by rwa [pairPlacement_elt])
  rwa [pairPlacement_free] at h

end Common

section Shape

variable {G : Type*} [Group G] {n : ℕ} {K : Type*} [Field K] {φ φ' : projectiveSL n K →* G}

theorem exists_conjAut_actsAs [Finite K] (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (hφ' : Function.Injective φ') {y : G} (hyN : y ∈ normalizer (φ'.range : Set G))
    (hyX : (rootGroup (K := K) hab).map φ' ≤ centralizer ({y} : Set G)) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) :
    ∃ A : GL (Fin n) K, ActsAs φ' y (conjAut n K A) ∧
      Commute (single a b (1 : K)) (A : Matrix (Fin n) (Fin n) K) ∧
      ∃ μ : K, μ ≠ 0 ∧ (A : Matrix (Fin n) (Fin n) K) ^ m = μ • 1 := by
  obtain ⟨β, hβ⟩ := exists_actsAs hφ' hyN
  have hβm := hβ.pow_eq_one hφ' hym
  have hfix : ∀ c : K, β (xab hab c) = xab hab c := fun c =>
    (hβ.mem_fixAut_iff hφ' _).2 (hyX ⟨_, xab_mem_rootGroup hab c, rfl⟩)
  obtain ⟨A, rfl, hE, μ, hμ, hAm⟩ := exists_conjAut_of_fix_xab hn hab hm hβm hfix
  exact ⟨A, hβ, hE, μ, hμ, hAm⟩

theorem exists_isPairShape_of_actsAs {a b : Fin n} (hab : a ≠ b) (hφ' : Function.Injective φ')
    (hQ : ((pairPlacement hab).radicalP K).map φ' = ((pairPlacement hab).radicalP K).map φ)
    (hsup : ((pairPlacement hab).radicalP K).map φ ⊔ (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ =
      ((pairPlacement hab).radicalP K).map φ ⊔ (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ')
    {y : G} (hyQ : y ∈ normalizer ((((pairPlacement hab).radicalP K).map φ : Subgroup G) : Set G))
    (hyB : (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ ≤ centralizer ({y} : Set G))
    {A : GL (Fin n) K} (hA : ActsAs φ' y (conjAut n K A))
    (hE : Commute (single a b (1 : K)) (A : Matrix (Fin n) (Fin n) K)) :
    ∃ ν, IsPairShape a b (A : Matrix (Fin n) (Fin n) K) ((A : Matrix (Fin n) (Fin n) K) a a) ν := by
  refine isPairShape_of_conjAut_eq hab A hE fun X hX => ?_
  have h1 : φ' (proj n K X) ∈ ((pairPlacement hab).radicalP K).map φ ⊔
      (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ :=
    hsup ▸ mem_sup_right ⟨proj n K X, ⟨X, hX, rfl⟩, rfl⟩
  have hBN : (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n))).map φ ≤
      normalizer ((((pairPlacement hab).radicalP K).map φ : Subgroup G) : Set G) :=
    (map_mono (blockSL_compl_le_normalizer_radicalP hab)).trans (le_normalizer_map φ)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hBN] at h1
  obtain ⟨q, hq, s, hs, hqs⟩ := h1
  rw [← hQ] at hq
  obtain ⟨q₁, hq₁, rfl⟩ := hq
  have hyq : y * φ' q₁ * y⁻¹ ∈ ((pairPlacement hab).radicalP K).map φ :=
    (mem_normalizer_iff.1 hyQ _).1 (hQ ▸ ⟨q₁, hq₁, rfl⟩)
  rw [← hQ] at hyq
  obtain ⟨q₂, hq₂, hq₂eq⟩ := hyq
  have hys : y * s * y⁻¹ = s := by
    have h := mem_centralizer_singleton_iff.1 (hyB hs)
    rw [← h, mul_inv_cancel_right]
  have hconj : conjAut n K A (proj n K X) = q₂ * q₁⁻¹ * proj n K X := by
    apply hφ'
    rw [hA, map_mul, map_mul, map_inv, hq₂eq]
    have hs' : s = (φ' q₁)⁻¹ * φ' (proj n K X) := by
      simp only at hqs
      rw [← hqs, inv_mul_cancel_left]
    calc y * φ' (proj n K X) * y⁻¹ = y * (φ' q₁ * s) * y⁻¹ := by
          simp only at hqs
          rw [hqs]
      _ = (y * φ' q₁ * y⁻¹) * (y * s * y⁻¹) := by group
      _ = y * φ' q₁ * y⁻¹ * (φ' q₁)⁻¹ * φ' (proj n K X) := by rw [hys, hs']; group
  obtain ⟨r, hr, hreq⟩ : q₂ * q₁⁻¹ ∈ (pairPlacement hab).radicalP K := mul_mem hq₂ (inv_mem hq₁)
  refine ⟨r, hr, ?_⟩
  rw [hconj, map_mul, hreq]

theorem false_of_actsAs_of_isPairShape_self [CharP K 2] (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (hφ : Function.Injective φ)
    (hQ : ((pairPlacement hab).radicalP K).map φ' = ((pairPlacement hab).radicalP K).map φ)
    {y : G} (hyQ : ((pairPlacement hab).radicalP K).map φ ⊓ centralizer ({y} : Set G) =
      (rootGroup hab).map φ)
    {A : GL (Fin n) K} (hA : ActsAs φ' y (conjAut n K A)) {l : K}
    (hshape : IsPairShape a b (A : Matrix (Fin n) (Fin n) K) l l) {m : ℕ} (hm : Odd m) {μ : K}
    (hμ : μ ≠ 0) (hAm : (A : Matrix (Fin n) (Fin n) K) ^ m = μ • 1) : False := by
  have hAl := eq_smul_one_of_isPairShape hab hshape hm hμ hAm
  have hl : l ≠ 0 := by
    rintro rfl
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    have : Nonempty (Fin n) := ⟨a⟩
    rw [hAl, zero_smul, det_zero] at hdet
    exact hdet rfl
  have hA1 : conjAut n K A = 1 := by
    have e : A = Matrix.GeneralLinearGroup.scalar (Fin n) (Units.mk0 l hl) := by
      ext : 1
      rw [Matrix.GeneralLinearGroup.coe_scalar, hAl, Units.val_mk0, scalar_apply,
        smul_one_eq_diagonal]
    rw [e, conjAut_scalar]
  rw [hA1] at hA
  apply radicalP_ne_rootGroup (K := K) hn hab
  apply Subgroup.map_injective hφ
  rw [← hyQ]
  refine (inf_eq_left.2 fun x hx => ?_).symm
  rw [← hQ] at hx
  obtain ⟨p, -, rfl⟩ := hx
  rw [mem_centralizer_singleton_iff]
  have h := hA p
  rw [MulAut.one_apply] at h
  calc φ' p * y = y * φ' p * y⁻¹ * y := by rw [← h]
    _ = y * φ' p := by group

end Shape

section BlockScalar

theorem map_conj_eq_of_mem {H' : Type*} [Group H'] {H : Subgroup H'} {h : H'} (hh : h ∈ H) :
    H.map (MulAut.conj h).toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hh hy) (inv_mem hh)
  · intro hx
    refine ⟨h⁻¹ * x * h, mul_mem (mul_mem (inv_mem hh) hx) hh, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem map_le_centralizer_singleton_of_mem {G H' : Type*} [Group G] [Group H'] (φ : H' →* G)
    {H : Subgroup H'} {y : H'} (hy : y ∈ centralizer (H : Set H')) :
    H.map φ ≤ centralizer ({φ y} : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_iff.1 hy x hx]

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
  {φ φ' : projectiveSL n K →* G}

theorem radicalP_le_perfectCore_centralizer_xab (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n) {a b : Fin n}
    (hab : a ≠ b) :
    (pairPlacement hab).radicalP K ≤
      perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K))) := by
  obtain ⟨-, hΛ, -, -, -⟩ := (pairPlacement hab).centralizer_inv_perfectCore (K := K) hq
    (by omega : 2 ≤ n - 2 * 1)
  rw [pairPlacement_elt] at hΛ
  rw [hΛ]
  exact le_sup_left

omit [Finite K] [CharP K 2] in
theorem perfectCore_rootGroup_sup_blockSL_le {a b : Fin n} (hab : a ≠ b) :
    perfectCore (rootGroup (K := K) hab ⊔ blockSL ({a, b}ᶜ : Finset (Fin n))) ≤
      blockSL ({a, b}ᶜ : Finset (Fin n)) := by
  have hXJ : rootGroup (K := K) hab ≤
      normalizer (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) : Set (projectiveSL n K)) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup hab).1 hx
    have hc : xab hab c ∈ centralizer
        (blockSL (K := K) ({a, b}ᶜ : Finset (Fin n)) : Set (projectiveSL n K)) := by
      rw [mem_centralizer_iff]
      intro s hs
      exact (commute_blockSL_of_disjoint disjoint_compl_right (xab hab c)
        (xab_mem_blockSL hab (by simp) (by simp) c) s hs).eq.symm
    exact centralizer_le_normalizer _ hc
  have hsolv : Group.IsSolvable (rootGroup (K := K) hab) :=
    Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective
      ((proj n K).comp (SpecialLinearGroup.transvectionHom hab)))
  refine CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_right ?_ (sup_comm _ _) hsolv
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
    (sup_le hXJ le_normalizer)

theorem exists_coords_blockScalar_of_map (hq : 4 ≤ Nat.card K) (hn : 4 ≤ n)
    (hκ : ∃ κ : Kˣ, κ ^ n ≠ 1) {a b : Fin n} (hab : a ≠ b) (hφ : Function.Injective φ)
    (hφ' : Function.Injective φ')
    (hΛ : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ')
    (hY : (pairTorus (K := K) a b).map φ ≤ normalizer (φ'.range : Set G)) :
    ∃ φ'' : projectiveSL n K →* G, Function.Injective φ'' ∧ φ''.range = φ'.range ∧
      φ'' (xab hab 1) = φ' (xab hab 1) ∧
      (∀ y ∈ (pairTorus (K := K) a b).map φ, ∃ (D : GL (Fin n) K) (l ν : K),
        (D : Matrix (Fin n) (Fin n) K) = pairDiag a b l ν ∧ ActsAs φ'' y (conjAut n K D)) ∧
      (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ =
        (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ'' ∧
      perfectCore (φ'.range ⊓ centralizer ((pairTorus (K := K) a b).map φ : Set G)) =
        (blockSL ({a, b} : Finset (Fin n))).map φ'' ⊔
          (blockSL ({a, b}ᶜ : Finset (Fin n))).map φ := by
  classical
  set Q₀ := (pairPlacement hab).radicalP K with hQ₀
  set J : Finset (Fin n) := ({a, b} : Finset (Fin n))ᶜ with hJ
  set Y := (pairTorus (K := K) a b).map φ with hYdef
  have hJ2 : 2 ≤ J.card := two_le_card_compl_pair hn hab
  set m := Nat.card K - 1 with hm
  have hmodd : Odd m := odd_card_sub_one_of_charTwo
  have hYm : ∀ y ∈ Y, y ^ m = 1 := by
    rintro _ ⟨y₁, hy₁, rfl⟩
    rw [← map_pow, pow_card_sub_one_eq_one_of_mem_blockTorus (pairTorus_le_blockTorus a b hy₁),
      map_one]
  have hYX : ∀ y ∈ Y, (rootGroup (K := K) hab).map φ ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨y₁, hy₁, rfl⟩
    exact map_le_centralizer_singleton_of_mem φ (pairTorus_le_centralizer_rootGroup hab hy₁)
  have hYB : ∀ y ∈ Y, (blockSL (K := K) J).map φ ≤ centralizer ({y} : Set G) := by
    rintro _ ⟨y₁, hy₁, rfl⟩
    exact map_le_centralizer_singleton_of_mem φ (pairTorus_le_centralizer_blockSL_compl a b hy₁)
  have hYQ : ∀ y ∈ Y, y ∈ normalizer ((Q₀.map φ : Subgroup G) : Set G) := by
    rintro _ ⟨y₁, hy₁, rfl⟩
    exact le_normalizer_map φ ⟨y₁, pairTorus_le_normalizer_radicalP hab hy₁, rfl⟩
  have hQ := map_radicalP_eq_of_map_perfectCore_eq hq hn hφ hφ' hab hΛ
  have hX := map_rootGroup_eq_of_map_perfectCore_eq hq hn hφ hφ' hab hΛ
  have hsup := sup_map_blockSL_eq_of_map_perfectCore_eq hq hn hφ hφ' hab hΛ
  obtain ⟨y₀', hy₀', hQy₀'⟩ := exists_pairTorus_centralizer_radical_eq hκ hab
  have hy₀Y : φ y₀' ∈ Y := ⟨y₀', hy₀', rfl⟩
  have hy₀Q : Q₀.map φ ⊓ centralizer ({φ y₀'} : Set G) = (rootGroup hab).map φ := by
    rw [← map_inf_centralizer_singleton hφ, hQy₀']
  obtain ⟨A₀, hA₀, hE₀, μ₀, hμ₀, hA₀m⟩ := exists_conjAut_actsAs (by omega) hab hφ' (hY hy₀Y)
    (hX ▸ hYX _ hy₀Y) hmodd (hYm _ hy₀Y)
  obtain ⟨ν, hshape⟩ := exists_isPairShape_of_actsAs hab hφ' hQ hsup (hYQ _ hy₀Y) (hYB _ hy₀Y)
    hA₀ hE₀
  have hαν : (A₀ : Matrix (Fin n) (Fin n) K) a a ≠ ν := by
    intro h
    rw [h] at hshape
    exact false_of_actsAs_of_isPairShape_self (by omega) hab hφ hQ hy₀Q hA₀ hshape hmodd hμ₀
      hA₀m
  obtain ⟨W, hWR, hAW⟩ := exists_mul_eq_mul_pairDiag hab hshape hαν hmodd hμ₀ hA₀m
  set φ'' : projectiveSL n K →* G := φ'.comp (MulAut.conj (proj n K W)).toMonoidHom with hφ''def
  have hφ'' : Function.Injective φ'' := hφ'.comp (MulAut.conj (proj n K W)).injective
  have hrange : φ''.range = φ'.range := by
    rw [hφ''def, MonoidHom.range_comp,
      MonoidHom.range_eq_top.2 (MulAut.conj (proj n K W)).surjective, ← MonoidHom.range_eq_map]
  have hWQ : proj n K W ∈ Q₀ := ⟨W, hWR, rfl⟩
  have hWz : φ'' (xab hab 1) = φ' (xab hab 1) := by
    have hc : W * SpecialLinearGroup.transvection hab (1 : K) =
        SpecialLinearGroup.transvection hab 1 * W := by
      have h := (pairPlacement hab).radical_le_centralizer hWR
      rw [pairPlacement_mat, mem_centralizer_singleton_iff] at h
      exact h
    have hconj : (MulAut.conj (proj n K W)) (xab hab 1) = xab hab 1 := by
      rw [MulAut.conj_apply, xab, ← map_mul, hc, map_mul, mul_inv_cancel_right]
    show φ' ((MulAut.conj (proj n K W)) (xab hab 1)) = _
    rw [hconj]
  have hΛ'' : (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ =
      (perfectCore (centralizer ({xab hab 1} : Set (projectiveSL n K)))).map φ'' := by
    rw [hΛ, hφ''def, ← Subgroup.map_map,
      map_conj_eq_of_mem (radicalP_le_perfectCore_centralizer_xab hq hn hab hWQ)]
  have hQ'' := map_radicalP_eq_of_map_perfectCore_eq hq hn hφ hφ'' hab hΛ''
  have hX'' := map_rootGroup_eq_of_map_perfectCore_eq hq hn hφ hφ'' hab hΛ''
  have hsup'' := sup_map_blockSL_eq_of_map_perfectCore_eq hq hn hφ hφ'' hab hΛ''
  set D₀ : GL (Fin n) K := (SpecialLinearGroup.toGL W)⁻¹ * A₀ * SpecialLinearGroup.toGL W
    with hD₀def
  have hD₀ : (D₀ : Matrix (Fin n) (Fin n) K) =
      pairDiag a b ((A₀ : Matrix (Fin n) (Fin n) K) a a) ν := by
    have hinv : (((SpecialLinearGroup.toGL W)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((W⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← map_inv]
      rfl
    rw [hD₀def, Units.val_mul, Units.val_mul, hinv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.mul_assoc, hAW, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  have hy₀act : ActsAs φ'' (φ y₀') (conjAut n K D₀) := hA₀.conj_proj W
  have hBperf : ⁅(blockSL (K := K) J).map φ, (blockSL (K := K) J).map φ⁆ =
      (blockSL (K := K) J).map φ := by
    rw [← Subgroup.map_commutator, commutator_blockSL_eq_of_two_le hJ2 hq]
  have hB1 : (blockSL (K := K) J).map φ ≤
      ((Q₀ ⊔ blockSL (K := K) J) ⊓ fixAut (conjAut n K D₀)).map φ'' := by
    intro x hx
    have hx1 : x ∈ (Q₀ ⊔ blockSL (K := K) J).map φ'' := by
      rw [Subgroup.map_sup, hQ'', ← hsup'']
      exact mem_sup_right hx
    obtain ⟨p, hp, rfl⟩ := hx1
    exact ⟨p, ⟨hp, (hy₀act.mem_fixAut_iff hφ'' p).2 (hYB _ hy₀Y hx)⟩, rfl⟩
  have hB2 := hB1.trans
    (Subgroup.map_mono (radicalP_sup_blockSL_inf_fixAut_le (by omega) hab D₀ hαν hD₀))
  have hB3 : (blockSL (K := K) J).map φ ≤ (blockSL (K := K) J).map φ'' := by
    calc (blockSL (K := K) J).map φ
        ≤ perfectCore ((rootGroup hab ⊔ blockSL (K := K) J).map φ'') :=
          le_perfectCore_of_perfect hB2 hBperf
      _ = (perfectCore (rootGroup hab ⊔ blockSL (K := K) J)).map φ'' := (map_perfectCore _ _).symm
      _ ≤ (blockSL (K := K) J).map φ'' :=
          Subgroup.map_mono (perfectCore_rootGroup_sup_blockSL_le hab)
  have hBeq : (blockSL (K := K) J).map φ = (blockSL (K := K) J).map φ'' :=
    Subgroup.eq_of_le_of_card_ge hB3 (by
      rw [Subgroup.card_map_of_injective hφ'', Subgroup.card_map_of_injective hφ])
  have hact : ∀ y ∈ Y, ∃ (D : GL (Fin n) K) (l ν : K),
      (D : Matrix (Fin n) (Fin n) K) = pairDiag a b l ν ∧ ActsAs φ'' y (conjAut n K D) := by
    intro y hy
    obtain ⟨A, hA, hE, μ, hμ, hAm⟩ := exists_conjAut_actsAs (by omega) hab hφ''
      (hrange ▸ hY hy) (hX'' ▸ hYX y hy) hmodd (hYm y hy)
    have hfix : ∀ X ∈ blockSpecialLinear (K := K) J,
        conjAut n K A (proj n K X) = proj n K X := fun X hX =>
      (hA.mem_fixAut_iff hφ'' _).2 (hYB y hy (by rw [hBeq]; exact ⟨proj n K X, ⟨X, hX, rfl⟩, rfl⟩))
    obtain ⟨ν', hν'⟩ := eq_pairDiag_of_conjAut_fix hn hab A hE hmodd hμ hAm hfix
    exact ⟨A, _, ν', hν', hA⟩
  have hIY : ∀ y ∈ Y, (blockSL (K := K) ({a, b} : Finset (Fin n))).map φ'' ≤
      centralizer ({y} : Set G) := by
    intro y hy
    obtain ⟨D, l, ν', hD, hA⟩ := hact y hy
    refine hA.map_le_centralizer ?_
    rintro _ ⟨X, hX, rfl⟩
    exact conjAut_proj_eq_of_mem_blockDiagSL D hD (blockSpecialLinear_le_blockDiagSL _ hX)
  have hI2 : 2 ≤ ({a, b} : Finset (Fin n)).card := by rw [Finset.card_pair hab]
  refine ⟨φ'', hφ'', hrange, hWz, hact, hBeq, le_antisymm ?_ ?_⟩
  · calc perfectCore (φ'.range ⊓ centralizer (Y : Set G))
        ≤ perfectCore (φ''.range ⊓ centralizer ({φ y₀'} : Set G)) := by
          rw [hrange]
          exact CFSG.Quasithin.perfectCore_mono
            (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.2 hy₀Y)))
      _ = perfectCore ((fixAut (conjAut n K D₀)).map φ'') := by rw [hy₀act.map_fixAut hφ'']
      _ = (perfectCore (fixAut (conjAut n K D₀))).map φ'' := (map_perfectCore _ _).symm
      _ = (blockSL ({a, b} : Finset (Fin n)) ⊔ blockSL (K := K) J).map φ'' := by
          rw [perfectCore_fixAut_conjAut_eq hI2 hJ2 hq D₀ hαν hD₀]
      _ = _ := by rw [Subgroup.map_sup, ← hBeq]
  · refine le_perfectCore_of_perfect (le_inf (sup_le ?_ ?_) ?_) ?_
    · rw [← hrange]
      exact Subgroup.map_le_range _ _
    · rw [hBeq, ← hrange]
      exact Subgroup.map_le_range _ _
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact (mem_centralizer_singleton_iff.1 ((sup_le (hIY y hy) (hYB y hy)) hx)).symm
    · rw [hBeq, ← Subgroup.map_sup, ← Subgroup.map_commutator,
        commutator_sup_eq_of_perfect (commutator_blockSL_eq_of_two_le hI2 hq)
          (commutator_blockSL_eq_of_two_le hJ2 hq)]

end BlockScalar

end CFSG.SeitzReduction.LinearPilot
