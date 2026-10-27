module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerOTwo
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvectionCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)

variable {K : Type*} [Field K]

theorem isPerfect_specialLinearGroup_of_ne_two [Finite K] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι ≠ 2 ∨ 4 ≤ Nat.card K) : Group.IsPerfect (SpecialLinearGroup ι K) := by
  rcases h with h | h
  · rcases (by omega : Fintype.card ι ≤ 1 ∨ 3 ≤ Fintype.card ι) with h1 | h3
    · have : Subsingleton (SpecialLinearGroup ι K) := by
        have := InvPlacement.subsingleton_specialLinearGroup_of_le_one (K := K) h1
        exact (reindexSpecialLinear (K := K) (Fintype.equivFin ι)).toEquiv.subsingleton
      infer_instance
    · exact isPerfect_specialLinearGroup_of_three_le_card ι h3
  · exact InvPlacement.isPerfect_specialLinearGroup_of_four_le h ι

theorem le_center_of_normal_of_two_pow' [Finite K] {m : ℕ} (hm : m ≠ 2 ∨ 4 ≤ Nat.card K)
    (N : Subgroup (SpecialLinearGroup (Fin m) K)) [hNn : N.Normal]
    (hN : ∀ a ∈ N, ∃ e : ℕ, a ^ 2 ^ e ∈ Subgroup.center (SpecialLinearGroup (Fin m) K)) :
    N ≤ Subgroup.center (SpecialLinearGroup (Fin m) K) := by
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have := InvPlacement.subsingleton_specialLinearGroup_of_le_one (K := K) (m := m) (by omega)
    intro a _
    exact Subgroup.mem_center_iff.2 fun g => Subsingleton.elim _ _
  · have h34 : 3 ≤ m ∨ ∃ s : Finset K, s.card = 4 := by
      rcases hm with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (CFSG.LinearGroups.exists_finset_card_eq_four h)
    obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := K) hm2 h34
    have hperf := CFSG.LinearGroups.linear_projective_perfect (K := K) hm2 h34
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
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp : IsPGroup 2 (ProjectiveSpecialLinearGroup (Fin m) K) := by
        intro x
        obtain ⟨a, ha, rfl⟩ : x ∈ N.map (QuotientGroup.mk' Z) := h ▸ Subgroup.mem_top x
        obtain ⟨e, he⟩ := hN a ha
        refine ⟨e, ?_⟩
        rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact he
      exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k)

theorem le_radicalP_of_isPGroup' [Finite K] [CharP K 2] (hk : k ≠ 2 ∨ 4 ≤ Nat.card K)
    (hJ2 : P.free.card ≠ 2 ∨ 4 ≤ Nat.card K)
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
    have hle := le_center_of_normal_of_two_pow' hk (T'.map (P.coreU K)) (by
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
    have hle := le_center_of_normal_of_two_pow' hJ2 (T'.map φ) (by
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

theorem le_radicalP_of_isPGroup_perfectCore' [Finite K] [CharP K 2]
    (hk : k ≠ 2 ∨ 4 ≤ Nat.card K) (hJ2 : P.free.card ≠ 2 ∨ 4 ≤ Nat.card K)
    (hJ : 2 ≤ P.free.card) {T : Subgroup (LinearFlag.projectiveSL n K)} (hT : IsPGroup 2 T)
    (hTΛ : T ≤ perfectCore (Subgroup.centralizer {P.elt K}))
    (hN : perfectCore (Subgroup.centralizer {P.elt K}) ≤
      Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K))) :
    T ≤ P.radicalP K := by
  have := isPerfect_specialLinearGroup_of_ne_two (K := K) (Fin k) (by rwa [Fintype.card_fin])
  have := isPerfect_specialLinearGroup_of_ne_two (K := K) P.free (by rwa [Fintype.card_coe])
  have hΛ := P.perfectCore_centralizer_elt (K := K) hJ
  rw [← map_core_eq] at hΛ
  exact P.le_radicalP_of_isPGroup' hk hJ2 (Finset.card_pos.1 (by omega)) hT (hΛ ▸ hTΛ) (hΛ ▸ hN)

theorem centralizer_inv_perfectCore' [Finite K] [CharP K 2] (hk : k ≠ 2 ∨ 4 ≤ Nat.card K)
    (hJ2 : n - 2 * k ≠ 2 ∨ 4 ≤ Nat.card K) (hJ : 2 ≤ n - 2 * k) :
    IsPGroup 2 (P.radicalP K) ∧
      perfectCore (Subgroup.centralizer {P.elt K}) =
        P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) ∧
      Disjoint (P.radicalP K) (P.leviOneP K ⊔ blockSL P.free) ∧
      P.leviOneP K ⊔ blockSL P.free ≤
        Subgroup.normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) ∧
      blockSL P.free = perfectCore ((P.leviOneP K ⊔ blockSL P.free) ⊓
        Subgroup.centralizer ((⁅P.radicalP K, P.radicalP K⁆ :
          Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K))) := by
  have := isPerfect_specialLinearGroup_of_ne_two (K := K) (Fin k) (by rwa [Fintype.card_fin])
  have := isPerfect_specialLinearGroup_of_ne_two (K := K) P.free
    (by rwa [Fintype.card_coe, card_free])
  have hJ' : 2 ≤ P.free.card := by rw [card_free]; exact hJ
  exact ⟨P.isPGroup_radicalP, P.perfectCore_centralizer_elt hJ', P.disjoint_radicalP,
    P.levi_le_normalizer_radicalP,
    P.blockSL_free_eq_perfectCore (Finset.card_pos.1 (by omega))⟩

theorem centralizer_inv_perfectCore_of_rank_one [Finite K] [CharP K 2] (P : InvPlacement n 1)
    (hn : 5 ≤ n) :
    IsPGroup 2 (P.radicalP K) ∧
      perfectCore (Subgroup.centralizer {P.elt K}) =
        P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) ∧
      Disjoint (P.radicalP K) (P.leviOneP K ⊔ blockSL P.free) ∧
      P.leviOneP K ⊔ blockSL P.free ≤
        Subgroup.normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) ∧
      blockSL P.free = perfectCore ((P.leviOneP K ⊔ blockSL P.free) ⊓
        Subgroup.centralizer ((⁅P.radicalP K, P.radicalP K⁆ :
          Subgroup (LinearFlag.projectiveSL n K)) : Set (LinearFlag.projectiveSL n K))) :=
  P.centralizer_inv_perfectCore' (Or.inl (by norm_num)) (Or.inl (by omega)) (by omega)

theorem le_radicalP_of_isPGroup_perfectCore_of_rank_one [Finite K] [CharP K 2]
    (P : InvPlacement n 1) (hn : 5 ≤ n) {T : Subgroup (LinearFlag.projectiveSL n K)}
    (hT : IsPGroup 2 T) (hTΛ : T ≤ perfectCore (Subgroup.centralizer {P.elt K}))
    (hN : perfectCore (Subgroup.centralizer {P.elt K}) ≤
      Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K))) :
    T ≤ P.radicalP K :=
  P.le_radicalP_of_isPGroup_perfectCore' (Or.inl (by norm_num))
    (Or.inl (by rw [card_free]; omega)) (by rw [card_free]; omega) hT hTΛ hN

theorem leviOneP_eq_bot_of_rank_one (P : InvPlacement n 1) : P.leviOneP K = ⊥ := by
  have : Subsingleton (SpecialLinearGroup (Fin 1) K) :=
    subsingleton_specialLinearGroup_of_le_one le_rfl
  rw [eq_bot_iff]
  rintro _ ⟨m, ⟨a, rfl⟩, rfl⟩
  rw [Subsingleton.elim a 1, map_one, map_one]
  exact Subgroup.one_mem _

omit [Field K] in
private theorem eq_one_of_isUnit_card_two [Field K] (hK : Nat.card K = 2) {x : K}
    (hx : IsUnit x) : x = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  exact mul_left_cancel₀ hx.ne_zero (h.trans (mul_one x).symm)

theorem centralizer_mat_le_core_two (hK : Nat.card K = 2) :
    Subgroup.centralizer {P.mat K} ≤ P.core K := by
  intro B hB
  have hBp : B ∈ P.parabolic K := P.centralizer_le_parabolic hB
  have hunit : ∀ f : P.parabolic K →* K, IsUnit (f ⟨B, hBp⟩) := fun f =>
    (Group.isUnit (⟨B, hBp⟩ : P.parabolic K)).map f
  exact P.mem_core_of_det hB (eq_one_of_isUnit_card_two hK (hunit (P.detU K)))
    (eq_one_of_isUnit_card_two hK (hunit (P.detFree K)))

theorem centralizer_elt_eq_map_core_two [CharP K 2] (hK : Nat.card K = 2) :
    Subgroup.centralizer {P.elt K} = P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) := by
  rw [P.centralizer_elt, ← map_core_eq]
  exact le_antisymm (Subgroup.map_mono (P.centralizer_mat_le_core_two hK))
    (Subgroup.map_mono P.core_le_centralizer)

theorem centralizer_elt_eq_two [CharP K 2] (P : InvPlacement n 1) (hK : Nat.card K = 2) :
    Subgroup.centralizer {P.elt K} = P.radicalP K ⊔ blockSL P.free := by
  rw [P.centralizer_elt_eq_map_core_two hK, P.leviOneP_eq_bot_of_rank_one, bot_sup_eq]

theorem perfectCore_centralizer_elt_two [Finite K] [CharP K 2] (P : InvPlacement n 1)
    (hK : Nat.card K = 2) (hn : 5 ≤ n) :
    perfectCore (Subgroup.centralizer {P.elt K}) = Subgroup.centralizer {P.elt K} := by
  rw [(P.centralizer_inv_perfectCore_of_rank_one (K := K) hn).2.1,
    P.centralizer_elt_eq_map_core_two hK]

theorem commutator_centralizer_elt_two [Finite K] [CharP K 2] (P : InvPlacement n 1)
    (hK : Nat.card K = 2) (hn : 5 ≤ n) :
    ⁅Subgroup.centralizer {P.elt K}, Subgroup.centralizer {P.elt K}⁆ =
      Subgroup.centralizer {P.elt K} := by
  rw [← P.perfectCore_centralizer_elt_two hK hn]
  exact CFSG.Quasithin.perfectCore_perfect _

theorem eq_of_isInvolutionClass [CharP K 2] {k' : ℕ} (h : IsInvolutionClass k' (P.elt K)) :
    k = k' := by
  obtain ⟨g, hg, hgg, hrk⟩ := h
  have hs : (P.mat K)⁻¹ * g ∈ LinearFlag.scalars n K := LinearFlag.proj_eq_proj_iff.1 hg.symm
  set s := (P.mat K)⁻¹ * g with hsdef
  have hsc : s ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := LinearFlag.scalars_le_center n K hs
  have hgs : g = P.mat K * s := by rw [hsdef, mul_inv_cancel_left]
  have hss : s * s = 1 := by
    have e1 : g * g = P.mat K * P.mat K * (s * s) := by
      rw [hgs]
      have hcomm : s * P.mat K = P.mat K * s := (Subgroup.mem_center_iff.1 hsc (P.mat K)).symm
      calc P.mat K * s * (P.mat K * s) = P.mat K * (s * P.mat K) * s := by group
        _ = P.mat K * (P.mat K * s) * s := by rw [hcomm]
        _ = P.mat K * P.mat K * (s * s) := by group
    rw [hgg, P.mat_mul_self, one_mul] at e1
    exact e1.symm
  have hs1 : s = 1 := eq_one_of_mem_scalars_of_mul_self hs hss
  rw [hs1, mul_one] at hgs
  rw [hgs, coe_mat, add_sub_cancel_left] at hrk
  rw [← hrk]
  exact (rank_nilOf (K := K) P.u_injective P.w_injective).symm

end InvPlacement

private theorem centralizer_conj_eq_map {X : Type*} [Group X] (c y : X) :
    Subgroup.centralizer ({c * y * c⁻¹} : Set X) =
      (Subgroup.centralizer ({y} : Set X)).map (MulAut.conj c).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  constructor
  · intro h
    calc c⁻¹ * x * c * y = c⁻¹ * (x * (c * y * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * y * c⁻¹) * x) * c := by rw [h]
      _ = y * (c⁻¹ * x * c) := by group
  · intro h
    calc x * (c * y * c⁻¹) = c * ((c⁻¹ * x * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * x * c)) * c⁻¹ := by rw [h]
      _ = c * y * c⁻¹ * x := by group

theorem centralizer_transvection_perfect_two [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2)
    (hn : 5 ≤ n) {y : LinearFlag.projectiveSL n K} (hy : IsInvolutionClass 1 y) :
    ⁅Subgroup.centralizer ({y} : Set (LinearFlag.projectiveSL n K)),
        Subgroup.centralizer ({y} : Set (LinearFlag.projectiveSL n K))⁆ =
      Subgroup.centralizer ({y} : Set (LinearFlag.projectiveSL n K)) ∧
    ∃ (P : InvPlacement n 1) (c : LinearFlag.projectiveSL n K), c * y * c⁻¹ = P.elt K ∧
      P.free.card = n - 2 ∧ IsPGroup 2 (P.radicalP K) ∧
      Subgroup.centralizer {P.elt K} = P.radicalP K ⊔ blockSL P.free ∧
      Disjoint (P.radicalP K) (blockSL P.free) ∧
      blockSL P.free ≤ Subgroup.normalizer (P.radicalP K : Set (LinearFlag.projectiveSL n K)) ∧
      ∀ T : Subgroup (LinearFlag.projectiveSL n K), IsPGroup 2 T →
        T ≤ Subgroup.centralizer {P.elt K} →
        Subgroup.centralizer {P.elt K} ≤
          Subgroup.normalizer (T : Set (LinearFlag.projectiveSL n K)) →
        T ≤ P.radicalP K := by
  obtain ⟨P, c, hc⟩ := exists_conj_eq_elt_of_isInvolutionClass_one hy
  obtain ⟨hQ, -, hdisj, hMN, -⟩ := P.centralizer_inv_perfectCore_of_rank_one (K := K) hn
  have hC := P.centralizer_elt_eq_two hK
  have hΛ := P.perfectCore_centralizer_elt_two hK hn
  rw [P.leviOneP_eq_bot_of_rank_one, bot_sup_eq] at hdisj hMN
  refine ⟨?_, P, c, hc, by rw [P.card_free], hQ, hC, hdisj, hMN, fun T hT h1 h2 => ?_⟩
  · have hmap := centralizer_conj_eq_map c y
    rw [hc] at hmap
    apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_commutator, ← hmap]
    exact P.commutator_centralizer_elt_two hK hn
  · rw [← hΛ] at h1 h2
    exact P.le_radicalP_of_isPGroup_perfectCore_of_rank_one hn hT h1 h2

end CFSG.SeitzReduction.LinearPilot
