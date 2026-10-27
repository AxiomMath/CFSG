module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.Quasithin (perfectCore)

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k) {K : Type*} [Field K]

theorem eq_of_pow_two_pow_eq [CharP K 2] {x y : K} {e : ℕ} (h : x ^ 2 ^ e = y ^ 2 ^ e) : x = y :=
  iterateFrobenius_inj K 2 e (by rw [iterateFrobenius_def, iterateFrobenius_def]; exact h)

theorem subsingleton_specialLinearGroup_of_le_one {m : ℕ} (hm : m ≤ 1) :
    Subsingleton (SpecialLinearGroup (Fin m) K) := by
  refine ⟨fun A B => Matrix.SpecialLinearGroup.ext A B fun i j => ?_⟩
  have hm1 : m = 1 := by have := i.2; omega
  have hij : i = j := Fin.ext (by have := i.2; have := j.2; omega)
  subst hij
  have hA := A.2
  have hB := B.2
  have : Unique (Fin m) := hm1 ▸ inferInstance
  rw [det_unique] at hA hB
  rw [Subsingleton.elim i default, hA, hB]

theorem le_center_of_normal_of_two_pow [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K) {m : ℕ}
    (N : Subgroup (SpecialLinearGroup (Fin m) K)) [hNn : N.Normal]
    (hN : ∀ a ∈ N, ∃ e : ℕ, a ^ 2 ^ e ∈ Subgroup.center (SpecialLinearGroup (Fin m) K)) :
    N ≤ Subgroup.center (SpecialLinearGroup (Fin m) K) := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have := subsingleton_specialLinearGroup_of_le_one (K := K) (m := m) (by omega)
    intro a _
    exact Subgroup.mem_center_iff.2 fun g => Subsingleton.elim _ _
  · obtain ⟨-, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) hm
      (Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four hq))
    set Z := Subgroup.center (SpecialLinearGroup (Fin m) K)
    have hnorm : (N.map (QuotientGroup.mk' Z)).Normal :=
      hNn.map _ (QuotientGroup.mk'_surjective Z)
    rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' Z)) with h | h
    · intro a ha
      have : QuotientGroup.mk' Z a = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.mem_map_of_mem _ ha
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    · exfalso
      obtain ⟨l, hl0, hl2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K hq
      set i₀ : Fin m := ⟨0, by omega⟩
      set i₁ : Fin m := ⟨1, by omega⟩
      have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
      set h₀ := SpecialLinearGroup.diag2n h01 l hl0
      obtain ⟨a, ha, hah⟩ : QuotientGroup.mk' Z h₀ ∈ N.map (QuotientGroup.mk' Z) :=
        h ▸ Subgroup.mem_top _
      obtain ⟨e, he⟩ := hN a ha
      have hz : a⁻¹ * h₀ ∈ Z := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hah
        exact hah
      have hcomm : Commute a (a⁻¹ * h₀) := (Subgroup.mem_center_iff.1 hz) a
      have hh : h₀ ^ 2 ^ e ∈ Z := by
        have : h₀ = a * (a⁻¹ * h₀) := (mul_inv_cancel_left a h₀).symm
        rw [this, hcomm.mul_pow]
        exact mul_mem he (pow_mem hz _)
      rw [Matrix.SpecialLinearGroup.mem_center_iff] at hh
      obtain ⟨r, -, hr⟩ := hh
      have hent : ∀ i : Fin m,
          r = (if i = i₀ then l else if i = i₁ then l⁻¹ else 1) ^ 2 ^ e := by
        intro i
        have := congrFun (congrFun hr i) i
        rwa [Matrix.SpecialLinearGroup.coe_pow, SpecialLinearGroup.diag2n_coe, diagonal_pow,
          scalar_apply, diagonal_apply_eq, diagonal_apply_eq, Pi.pow_apply] at this
      have h0 := hent i₀
      have h1 := hent i₁
      rw [ite_eq_left rfl] at h0
      rw [ite_eq_right h01.symm, ite_eq_left rfl] at h1
      have h01' : l ^ 2 ^ e = l⁻¹ ^ 2 ^ e := h0.symm.trans h1
      have hll : (l * l) ^ 2 ^ e = 1 ^ 2 ^ e :=
        calc (l * l) ^ 2 ^ e = l ^ 2 ^ e * l ^ 2 ^ e := mul_pow l l _
          _ = l⁻¹ ^ 2 ^ e * l ^ 2 ^ e := congrArg (· * l ^ 2 ^ e) h01'
          _ = (l⁻¹ * l) ^ 2 ^ e := (mul_pow _ _ _).symm
          _ = 1 ^ 2 ^ e := by rw [inv_mul_cancel₀ hl0]
      exact hl2 (by rw [sq]; exact eq_of_pow_two_pow_eq hll)

theorem blockTriangular_of_mem_core {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.core K) :
    (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
  P.mem_parabolic.1 (P.centralizer_le_parabolic (P.core_le_centralizer hB))

theorem submatrix_u_eq_one_of_mem_radical {r : SpecialLinearGroup (Fin n) K}
    (hr : r ∈ P.radical K) : (r : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = 1 := by
  ext x y
  rw [submatrix_apply, hr _ _ (by rw [level_u, level_u]), one_apply_of_injective P.u_injective]

theorem submatrix_free_eq_one_of_mem_radical {r : SpecialLinearGroup (Fin n) K}
    (hr : r ∈ P.radical K) :
    (r : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
      (Subtype.val : P.free → Fin n) = 1 := by
  ext x y
  rw [submatrix_apply, hr _ _ (by rw [P.mem_free.1 x.2, P.mem_free.1 y.2]),
    one_apply_of_injective Subtype.val_injective]

theorem submatrix_u_eq_one_of_mem_free {B : SpecialLinearGroup (Fin n) K}
    (hB : B ∈ blockSpecialLinear P.free) :
    (B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = 1 := by
  ext x y
  rw [submatrix_apply, hB _ _ (Or.inl (P.u_not_mem_free x)),
    one_apply_of_injective P.u_injective]

theorem det_blocks_of_mem_core {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.core K) :
    ((B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u).det = 1 ∧
      ((B : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n)).det = 1 := by
  set S : Subgroup (SpecialLinearGroup (Fin n) K) :=
    ((P.detU K).ker ⊓ (P.detFree K).ker).map (P.parabolic K).subtype
  have hS : ∀ {B : SpecialLinearGroup (Fin n) K} (hp : B ∈ P.parabolic K),
      ((B : Matrix (Fin n) (Fin n) K).submatrix P.u P.u).det = 1 →
      ((B : Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n)).det = 1 → B ∈ S :=
    fun hp h0 h1 => ⟨⟨_, hp⟩, ⟨h0, h1⟩, rfl⟩
  have hle : P.core K ≤ S := by
    refine sup_le (fun r hr => hS (P.radical_le_parabolic hr) ?_ ?_)
      (sup_le (fun _ ⟨a, ha⟩ => ?_) fun d hd => ?_)
    · rw [P.submatrix_u_eq_one_of_mem_radical hr, det_one]
    · rw [P.submatrix_free_eq_one_of_mem_radical hr, det_one]
    · subst ha
      refine hS (P.blockDiag_le_parabolic (P.leviOneHom_mem_blockDiag a)) ?_ ?_
      · rw [submatrix_u_leviOneHom]
        exact a.2
      · rw [submatrix_free_leviOneHom, det_one]
    · rw [← range_blockEmbed] at hd
      obtain ⟨d, rfl⟩ := hd
      refine hS (P.blockDiag_le_parabolic
        (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem d))) ?_ ?_
      · rw [submatrix_u_blockEmbed_free, det_one]
      · rw [submatrix_free_blockEmbed_free]
        exact d.2
  obtain ⟨p, ⟨h0, h1⟩, rfl⟩ := hle hB
  exact ⟨h0, h1⟩

variable (K) in
@[expose] noncomputable def coreU : P.core K →* SpecialLinearGroup (Fin k) K where
  toFun B := ⟨((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u,
    (P.det_blocks_of_mem_core B.2).1⟩
  map_one' := by
    apply Subtype.ext
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ P.u_injective]
  map_mul' B B' := by
    apply Subtype.ext
    show (((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix P.u P.u = _
    rw [Matrix.SpecialLinearGroup.coe_mul,
      P.submatrix_mul_u (P.blockTriangular_of_mem_core B.2) (P.blockTriangular_of_mem_core B'.2)]
    rfl

variable (K) in
@[expose] noncomputable def coreFree : P.core K →* SpecialLinearGroup P.free K where
  toFun B := ⟨((B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n),
    (P.det_blocks_of_mem_core B.2).2⟩
  map_one' := by
    apply Subtype.ext
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, submatrix_one _ Subtype.val_injective]
  map_mul' B B' := by
    apply Subtype.ext
    show (((B : SpecialLinearGroup (Fin n) K) * B' : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K).submatrix (Subtype.val : P.free → Fin n)
        (Subtype.val : P.free → Fin n) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, P.submatrix_mul_free (P.blockTriangular_of_mem_core B.2)
      (P.blockTriangular_of_mem_core B'.2)]
    rfl

theorem leviHom_mem_core (a : SpecialLinearGroup (Fin k) K) (d : SpecialLinearGroup P.free K) :
    P.leviHom K (a, d) ∈ P.core K := by
  have : P.leviHom K (a, d) ∈ P.leviOne K ⊔ blockSpecialLinear P.free := by
    rw [← P.range_leviHom]
    exact ⟨_, rfl⟩
  exact Subgroup.mem_sup_right this

theorem submatrix_free_leviHom (a : SpecialLinearGroup (Fin k) K)
    (d : SpecialLinearGroup P.free K) :
    ((P.leviHom K (a, d) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix
      (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) = d := by
  rw [leviHom, MonoidHom.noncommCoprod_apply, Matrix.SpecialLinearGroup.coe_mul,
    P.submatrix_mul_free (P.mem_parabolic.1 (P.blockDiag_le_parabolic
      (P.leviOneHom_mem_blockDiag a)))
      (P.mem_parabolic.1 (P.blockDiag_le_parabolic
        (P.blockSpecialLinear_free_le_blockDiag (P.blockEmbed_free_mem d)))),
    submatrix_free_leviOneHom, submatrix_free_blockEmbed_free, Matrix.one_mul]

theorem coreU_surjective : Function.Surjective (P.coreU K) := fun a =>
  ⟨⟨_, P.leviHom_mem_core a 1⟩, Subtype.ext (P.blockU_leviHom a 1)⟩

theorem coreFree_surjective : Function.Surjective (P.coreFree K) := fun d =>
  ⟨⟨_, P.leviHom_mem_core 1 d⟩, Subtype.ext (P.submatrix_free_leviHom 1 d)⟩

theorem mem_radical_of_blocks {B : SpecialLinearGroup (Fin n) K}
    (hB : B ∈ Subgroup.centralizer {P.mat K})
    (hu : ∀ a b, (B : Matrix (Fin n) (Fin n) K) (P.u a) (P.u b) =
      (1 : Matrix (Fin n) (Fin n) K) (P.u a) (P.u b))
    (hf : ∀ i j, i ∈ P.free → j ∈ P.free →
      (B : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    B ∈ P.radical K := by
  obtain ⟨hBT, hBuw⟩ := P.mem_centralizer_mat_iff.1 hB
  intro i j hij
  rcases lt_or_eq_of_le hij with h | h
  · rw [hBT h, one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  · have hi2 := P.level_le_two i
    rcases (by omega : P.level i = 0 ∨ P.level i = 1 ∨ P.level i = 2) with h0 | h1 | h2
    · obtain ⟨x, rfl⟩ := P.level_eq_zero_iff.1 h0
      obtain ⟨y, rfl⟩ := P.level_eq_zero_iff.1 (h.trans h0)
      exact hu x y
    · exact hf i j (P.mem_free.2 h1) (P.mem_free.2 (h.trans h1))
    · obtain ⟨x, rfl⟩ := P.level_eq_two_iff.1 h2
      obtain ⟨y, rfl⟩ := P.level_eq_two_iff.1 (h.trans h2)
      rw [hBuw, hu, one_apply_of_injective P.u_injective, one_apply_of_injective P.w_injective]

theorem le_radicalP_of_isPGroup [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hJ : P.free.Nonempty) {T : Subgroup (LinearFlag.projectiveSL n K)} (hT : IsPGroup 2 T)
    (hTΛ : T ≤ (P.core K).map (LinearFlag.proj n K))
    (hN : (P.core K).map (LinearFlag.proj n K) ≤
      Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K))) :
    T ≤ P.radicalP K := by
  set T' : Subgroup (P.core K) := T.comap ((LinearFlag.proj n K).comp (P.core K).subtype)
    with hT'
  have hT'n : T'.Normal := by
    constructor
    intro x hx c
    have hc : LinearFlag.proj n K c ∈ Subgroup.normalizer (T : Set _) := hN ⟨c, c.2, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hc
    have := (hc (LinearFlag.proj n K x)).1 hx
    show LinearFlag.proj n K ((c * x * c⁻¹ : P.core K) : SpecialLinearGroup (Fin n) K) ∈ T
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
  have h2pow : ∀ x ∈ T', ∃ e : ℕ,
      ((x : SpecialLinearGroup (Fin n) K) ^ 2 ^ e) ∈ LinearFlag.scalars n K := by
    intro x hx
    obtain ⟨e, he⟩ := hT ⟨LinearFlag.proj n K x, hx⟩
    refine ⟨e, ?_⟩
    rw [← LinearFlag.proj_eq_one_iff, map_pow]
    exact congrArg Subtype.val he
  have hscalU : ∀ x : P.core K, (x : SpecialLinearGroup (Fin n) K) ∈ LinearFlag.scalars n K →
      P.coreU K x ∈ Subgroup.center (SpecialLinearGroup (Fin k) K) := by
    intro x hx
    obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have : ((P.coreU K x : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        scalar (Fin k) (c : K) := by
      show ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).submatrix P.u P.u = _
      rw [hc]
      ext a b
      simp [scalar_apply, diagonal_apply, P.u_injective.eq_iff]
    rw [this]
    exact (scalar_commute (c : K) (fun _ => Commute.all _ _) _).symm
  have hscalF : ∀ x : P.core K, (x : SpecialLinearGroup (Fin n) K) ∈ LinearFlag.scalars n K →
      reindexSpecialLinear P.free.equivFin (P.coreFree K x) ∈
        Subgroup.center (SpecialLinearGroup (Fin P.free.card) K) := by
    intro x hx
    obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    have : ((reindexSpecialLinear P.free.equivFin (P.coreFree K x) :
        SpecialLinearGroup (Fin P.free.card) K) : Matrix (Fin P.free.card) (Fin P.free.card) K) =
        scalar (Fin P.free.card) (c : K) := by
      ext a b
      rw [coe_reindexSpecialLinear_apply]
      show ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        (P.free.equivFin.symm a) (P.free.equivFin.symm b) = _
      rw [hc]
      simp [scalar_apply, diagonal_apply, Subtype.val_injective.eq_iff]
    rw [this]
    exact (scalar_commute (c : K) (fun _ => Commute.all _ _) _).symm
  have hU : ∀ x ∈ T', P.coreU K x ∈ Subgroup.center (SpecialLinearGroup (Fin k) K) := by
    have : (T'.map (P.coreU K)).Normal := hT'n.map _ P.coreU_surjective
    have hle := le_center_of_normal_of_two_pow hq (T'.map (P.coreU K)) (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨e, he⟩ := h2pow x hx
      exact ⟨e, by rw [← map_pow]; exact hscalU _ he⟩)
    exact fun x hx => hle ⟨x, hx, rfl⟩
  have hF : ∀ x ∈ T', reindexSpecialLinear P.free.equivFin (P.coreFree K x) ∈
      Subgroup.center (SpecialLinearGroup (Fin P.free.card) K) := by
    set φ := (reindexSpecialLinear (K := K) P.free.equivFin).toMonoidHom.comp (P.coreFree K)
    have hφ : Function.Surjective φ := fun y => by
      obtain ⟨d, hd⟩ := (reindexSpecialLinear (K := K) P.free.equivFin).surjective y
      obtain ⟨x, rfl⟩ := P.coreFree_surjective d
      exact ⟨x, hd⟩
    have : (T'.map φ).Normal := hT'n.map _ hφ
    have hle := le_center_of_normal_of_two_pow hq (T'.map φ) (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨e, he⟩ := h2pow x hx
      exact ⟨e, by rw [← map_pow]; exact hscalF _ he⟩)
    exact fun x hx => hle ⟨x, hx, rfl⟩
  intro t ht
  obtain ⟨B, hB, rfl⟩ := hTΛ ht
  set x : P.core K := ⟨B, hB⟩
  have hx : x ∈ T' := ht
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hU x hx)
  obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 (hF x hx)
  have hBu : ∀ a b, (B : Matrix (Fin n) (Fin n) K) (P.u a) (P.u b) = if a = b then r else 0 := by
    intro a b
    have := congrFun (congrFun hr a) b
    rw [scalar_apply, diagonal_apply] at this
    exact this.symm
  have hBf : ∀ i j, i ∈ P.free → j ∈ P.free →
      (B : Matrix (Fin n) (Fin n) K) i j = if i = j then s else 0 := by
    intro i j hi hj
    have := congrFun (congrFun hs (P.free.equivFin ⟨i, hi⟩)) (P.free.equivFin ⟨j, hj⟩)
    rw [scalar_apply, diagonal_apply, coe_reindexSpecialLinear_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] at this
    have hBij : ((P.coreFree K x : SpecialLinearGroup P.free K) : Matrix P.free P.free K)
        ⟨i, hi⟩ ⟨j, hj⟩ = (B : Matrix (Fin n) (Fin n) K) i j := rfl
    rw [hBij] at this
    rw [← this]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right hij, ite_eq_right]
      intro h
      exact hij (congrArg Subtype.val ((P.free.equivFin).injective h))
  obtain ⟨e, he⟩ := h2pow x hx
  obtain ⟨c, hcn, hc⟩ := LinearFlag.mem_scalars.1 he
  obtain ⟨j₀, hj₀⟩ := hJ
  have hcs : (c : K) = s ^ 2 ^ e := by
    have h1 := congrArg (fun X : SpecialLinearGroup P.free K =>
      (X : Matrix P.free P.free K) ⟨j₀, hj₀⟩ ⟨j₀, hj₀⟩) (map_pow (P.coreFree K) x (2 ^ e))
    have hd : ((P.coreFree K x : SpecialLinearGroup P.free K) : Matrix P.free P.free K) =
        scalar P.free s := by
      ext i j
      show (B : Matrix (Fin n) (Fin n) K) i j = _
      rw [hBf i j i.2 j.2, scalar_apply, diagonal_apply]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hij, ite_eq_right fun h => hij (Subtype.ext h)]
    rw [Matrix.SpecialLinearGroup.coe_pow, hd, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
    rw [← h1]
    show (c : K) = ((x ^ 2 ^ e : P.core K) : SpecialLinearGroup (Fin n) K) j₀ j₀
    rw [Subgroup.coe_pow, hc, scalar_apply, diagonal_apply_eq]
  have hrs : ∀ a : Fin k, r = s := by
    intro a
    have h1 := congrArg (fun X : SpecialLinearGroup (Fin k) K =>
      (X : Matrix (Fin k) (Fin k) K) a a) (map_pow (P.coreU K) x (2 ^ e))
    have hd : ((P.coreU K x : SpecialLinearGroup (Fin k) K) : Matrix (Fin k) (Fin k) K) =
        scalar (Fin k) r := by
      ext i j
      show (B : Matrix (Fin n) (Fin n) K) (P.u i) (P.u j) = _
      rw [hBu i j, scalar_apply, diagonal_apply]
    rw [Matrix.SpecialLinearGroup.coe_pow, hd, ← map_pow, scalar_apply, diagonal_apply_eq] at h1
    have h2 : ((x ^ 2 ^ e : P.core K) : SpecialLinearGroup (Fin n) K) (P.u a) (P.u a) = c := by
      rw [Subgroup.coe_pow, hc, scalar_apply, diagonal_apply_eq]
    refine eq_of_pow_two_pow_eq (e := e) ?_
    rw [← hcs, ← h2]
    exact h1.symm
  have hsn : s ^ n = 1 := by
    refine eq_of_pow_two_pow_eq (e := e) ?_
    rw [← pow_mul, mul_comm, pow_mul, ← hcs, one_pow, ← Units.val_pow_eq_pow_val, hcn,
      Units.val_one]
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact j₀.elim0
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow hn0] at hsn
    exact zero_ne_one hsn
  set z := LinearFlag.scalarElement (n := n) (Units.mk0 s hs0)⁻¹ (by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, hsn, inv_one,
      Units.val_one])
  have hz : z ∈ LinearFlag.scalars n K := LinearFlag.scalarElement_mem_scalars _ _
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) :=
    LinearFlag.scalars_le_center n K hz
  have hcoe : ((B * z : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * scalar (Fin n) s⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, LinearFlag.coe_scalarElement, Units.val_inv_eq_inv_val,
      Units.val_mk0]
  have hBz : B * z ∈ P.radical K := by
    refine P.mem_radical_of_blocks (mul_mem (P.core_le_centralizer hB) ?_) (fun a b => ?_)
      (fun i j hi hj => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h _
      exact (Subgroup.mem_center_iff.1 hzc h)
    · rw [hcoe, scalar_apply, mul_diagonal, hBu a b, ← hrs a, one_apply_of_injective P.u_injective,
        one_apply]
      split_ifs with hab
      · exact mul_inv_cancel₀ (by rw [hrs a]; exact hs0)
      · exact zero_mul _
    · rw [hcoe, scalar_apply, mul_diagonal, hBf i j hi hj, one_apply]
      split_ifs with hij
      · exact mul_inv_cancel₀ hs0
      · exact zero_mul _
  have hπz : LinearFlag.proj n K z = 1 := LinearFlag.proj_eq_one_iff.2 hz
  refine ⟨B * z, hBz, ?_⟩
  rw [map_mul, hπz, mul_one]

theorem le_radicalP_of_isPGroup_perfectCore [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hJ : 2 ≤ P.free.card) {T : Subgroup (LinearFlag.projectiveSL n K)} (hT : IsPGroup 2 T)
    (hTΛ : T ≤ perfectCore (Subgroup.centralizer {P.elt K}))
    (hN : perfectCore (Subgroup.centralizer {P.elt K}) ≤
      Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K))) :
    T ≤ P.radicalP K := by
  have := isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have := isPerfect_specialLinearGroup_of_four_le hq P.free
  have hΛ := P.perfectCore_centralizer_elt (K := K) hJ
  rw [← map_core_eq] at hΛ
  exact P.le_radicalP_of_isPGroup hq (Finset.card_pos.1 (by omega)) hT (hΛ ▸ hTΛ) (hΛ ▸ hN)

theorem radicalP_eq_of_isPGroup [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (hJ : 2 ≤ P.free.card) {Q' : Subgroup (LinearFlag.projectiveSL n K)} (hQ' : IsPGroup 2 Q')
    (hQ'Λ : Q' ≤ perfectCore (Subgroup.centralizer {P.elt K}))
    (hN : perfectCore (Subgroup.centralizer {P.elt K}) ≤
      Subgroup.normalizer (Q' : Set (LinearFlag.projectiveSL n K)))
    (hmax : ∀ T : Subgroup (LinearFlag.projectiveSL n K), IsPGroup 2 T →
      T ≤ perfectCore (Subgroup.centralizer {P.elt K}) →
      perfectCore (Subgroup.centralizer {P.elt K}) ≤
        Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K)) → T ≤ Q') :
    Q' = P.radicalP K := by
  have := isPerfect_specialLinearGroup_of_four_le hq (Fin k)
  have := isPerfect_specialLinearGroup_of_four_le hq P.free
  have hΛ := P.perfectCore_centralizer_elt (K := K) hJ
  rw [← map_core_eq] at hΛ
  refine le_antisymm (P.le_radicalP_of_isPGroup_perfectCore hq hJ hQ' hQ'Λ hN)
    (hmax _ P.isPGroup_radicalP ?_ ?_)
  · rw [hΛ]
    exact Subgroup.map_mono le_sup_left
  · rw [hΛ, map_core_eq]
    exact sup_le (Subgroup.le_normalizer) P.levi_le_normalizer_radicalP

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
