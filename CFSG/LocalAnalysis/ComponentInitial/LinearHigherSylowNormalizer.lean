module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Subgroup

variable {K : Type*} [Field K] {n : ℕ}

@[expose] def IsCompleteFlag (V : Fin (n + 1) → Submodule K (Fin n → K)) : Prop :=
  Monotone V ∧ ∀ i, finrank K (V i) = i

@[expose] def flagFamilyStabilizer (V : Fin (n + 1) → Submodule K (Fin n → K)) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  ⨅ i, stabilizer (V i)

@[expose] def projFlagFamilyStabilizer (V : Fin (n + 1) → Submodule K (Fin n → K)) :
    Subgroup (projectiveSL n K) :=
  (flagFamilyStabilizer V).map (proj n K)

@[expose] def standardFlag (n : ℕ) (K : Type*) [Field K] :
    Fin (n + 1) → Submodule K (Fin n → K) :=
  fun i => flagSpace n K i

theorem mem_flagFamilyStabilizer {V : Fin (n + 1) → Submodule K (Fin n → K)}
    {g : SpecialLinearGroup (Fin n) K} :
    g ∈ flagFamilyStabilizer V ↔ ∀ i, g ∈ stabilizer (V i) :=
  Subgroup.mem_iInf

theorem flagSpace_mono {i j : ℕ} (h : i ≤ j) : flagSpace n K i ≤ flagSpace n K j := by
  intro v hv
  rw [mem_flagSpace] at hv ⊢
  exact fun c hc => hv c (h.trans hc)

theorem isCompleteFlag_standardFlag : IsCompleteFlag (standardFlag n K) :=
  ⟨fun _ _ h => flagSpace_mono h, fun i => finrank_flagSpace (by omega)⟩

theorem flagFamilyStabilizer_standardFlag :
    flagFamilyStabilizer (standardFlag n K) = upperTriangular n K := by
  apply le_antisymm
  · intro g hg r c hcr
    have hmem : (g : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single c 1 ∈ flagSpace n K ((c : ℕ) + 1) := by
      have h := mem_stabilizer.mp (mem_flagFamilyStabilizer.mp hg ⟨(c : ℕ) + 1, by omega⟩)
      change (flagSpace n K ((c : ℕ) + 1)).map _ = flagSpace n K ((c : ℕ) + 1) at h
      rw [← h]
      exact ⟨_, Submodule.subset_span ⟨c, by simp, rfl⟩, rfl⟩
    rw [mem_flagSpace] at hmem
    have := hmem r (by rw [Fin.lt_def] at hcr; omega)
    rwa [mulVec_single_one, col_apply] at this
  · intro b hb
    exact mem_flagFamilyStabilizer.mpr fun i => mem_stabilizer_of_map_le (by
      rintro _ ⟨v, hv, rfl⟩
      exact flagSpace_invariant (i : ℕ) hb hv)

theorem exists_map_standardFlag_eq {V : Fin (n + 1) → Submodule K (Fin n → K)}
    (hV : IsCompleteFlag V) :
    ∃ g : SpecialLinearGroup (Fin n) K, ∀ i : Fin (n + 1),
      (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) = V i := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, fun i => Subsingleton.elim _ _⟩
  have hlt : ∀ c : Fin n, V c.castSucc < V c.succ := fun c => by
    refine lt_of_le_of_ne (hV.1 (Fin.castSucc_le_succ c)) fun h => ?_
    have := congrArg (fun W : Submodule K (Fin n → K) => finrank K W) h
    simp only [hV.2, Fin.val_castSucc, Fin.val_succ] at this
    omega
  choose v hvV hvnot using fun c => IsConcreteLE.exists_of_lt (hlt c)
  have hspan : ∀ i : ℕ, (hi : i ≤ n) →
      Submodule.span K (v '' {c : Fin n | (c : ℕ) < i}) = V ⟨i, by omega⟩ := by
    intro i
    induction i with
    | zero =>
      intro _
      have h0 : V ⟨0, by omega⟩ = ⊥ := Submodule.finrank_eq_zero.mp (hV.2 _)
      rw [h0, Submodule.span_eq_bot]
      rintro _ ⟨c, hc, rfl⟩
      exact absurd hc (Nat.not_lt_zero _)
    | succ i ih =>
      intro hi
      have hset : v '' {c : Fin n | (c : ℕ) < i + 1} =
          insert (v ⟨i, by omega⟩) (v '' {c : Fin n | (c : ℕ) < i}) := by
        rw [← Set.image_insert_eq]
        congr 1
        ext c
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      have hle : V ⟨i, by omega⟩ ≤ V ⟨i + 1, by omega⟩ := hV.1 (by rw [Fin.mk_le_mk]; omega)
      have hvi : v ⟨i, by omega⟩ ∈ V ⟨i + 1, by omega⟩ := hvV ⟨i, by omega⟩
      have hvi' : v ⟨i, by omega⟩ ∉ V ⟨i, by omega⟩ := hvnot ⟨i, by omega⟩
      rw [hset, Submodule.span_insert, ih (by omega)]
      apply Submodule.eq_of_le_of_finrank_eq
      · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hvi) hle
      · have hlt' : V ⟨i, by omega⟩ < K ∙ v ⟨i, by omega⟩ ⊔ V ⟨i, by omega⟩ :=
          lt_of_le_of_ne le_sup_right fun h => hvi' (h ▸ Submodule.mem_sup_left
            (Submodule.mem_span_singleton_self _))
        have h1 := Submodule.finrank_lt_finrank_of_lt hlt'
        have h2 := Submodule.finrank_mono (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
          hvi) hle)
        rw [hV.2] at h1 h2 ⊢
        simp only at h1 h2 ⊢
        omega
  set A : Matrix (Fin n) (Fin n) K := Matrix.of fun r c => v c r with hA
  have hAcol : ∀ c, A *ᵥ Pi.single c 1 = v c := fun c => by
    rw [mulVec_single_one]
    rfl
  have hAmap : ∀ i : ℕ, (hi : i ≤ n) →
      (flagSpace n K i).map (mulVecLin A) = V ⟨i, by omega⟩ := fun i hi => by
    rw [flagSpace, Submodule.map_span, ← hspan i hi, ← Set.image_comp]
    congr 1
    ext w
    simp [hAcol]
  have hAunit : IsUnit A := by
    rw [← mulVec_surjective_iff_isUnit]
    intro w
    have htop : V ⟨n, by omega⟩ = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [hV.2, finrank_fin_fun])
    have hw : w ∈ (flagSpace n K n).map (mulVecLin A) := by
      rw [hAmap n le_rfl, htop]
      exact Submodule.mem_top
    obtain ⟨u, -, hu⟩ := hw
    exact ⟨u, hu⟩
  have hd0 : A.det ≠ 0 := ((isUnit_iff_isUnit_det A).mp hAunit).ne_zero
  set e : Fin n → K := Pi.mulSingle ⟨0, hn⟩ A.det⁻¹ with he
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he, Pi.mulSingle_apply]
    split_ifs
    · exact inv_ne_zero hd0
    · exact one_ne_zero
  have hdet : (A * diagonal e).det = 1 := by
    rw [det_mul, det_diagonal, he, Fintype.prod_pi_mulSingle', mul_inv_cancel₀ hd0]
  refine ⟨⟨A * diagonal e, hdet⟩, fun i => ?_⟩
  change (flagSpace n K i).map (mulVecLin (A * diagonal e)) = V i
  rw [mulVecLin_mul, Submodule.map_comp, map_diagonal_flagSpace he0, hAmap i (by omega)]

theorem flagFamilyStabilizer_eq_map_conj {V : Fin (n + 1) → Submodule K (Fin n → K)}
    {g : SpecialLinearGroup (Fin n) K}
    (hg : ∀ i : Fin (n + 1), (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) =
      V i) :
    flagFamilyStabilizer V =
      (upperTriangular n K).map (MulAut.conj g : SpecialLinearGroup (Fin n) K →*
        SpecialLinearGroup (Fin n) K) := by
  rw [← flagFamilyStabilizer_standardFlag, Subgroup.map_equiv_eq_comap_symm]
  ext h
  rw [Subgroup.mem_comap, mem_flagFamilyStabilizer, mem_flagFamilyStabilizer]
  refine forall_congr' fun i => ?_
  rw [mem_stabilizer, mem_stabilizer, ← hg i]
  change _ ↔ (flagSpace n K i).map (mulVecLin ((g⁻¹ * h * g : SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K)) = flagSpace n K i
  simp only [SpecialLinearGroup.coe_mul, mulVecLin_mul, Submodule.map_comp]
  constructor
  · intro h1
    rw [h1, ← Submodule.map_comp, ← mulVecLin_mul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
      SpecialLinearGroup.coe_one, mulVecLin_one, Submodule.map_id]
  · intro h1
    have h2 := congrArg (Submodule.map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) h1
    rw [← Submodule.map_comp, ← mulVecLin_mul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
      SpecialLinearGroup.coe_one, mulVecLin_one, Submodule.map_id] at h2
    exact h2

theorem isCompleteFlag_map (g : SpecialLinearGroup (Fin n) K) :
    IsCompleteFlag fun i : Fin (n + 1) =>
      (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) :=
  ⟨fun _ _ h => Submodule.map_mono (flagSpace_mono h), fun i => by
    rw [show finrank K ((flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) =
      finrank K (flagSpace n K i) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _,
      finrank_flagSpace (by omega)]⟩

theorem conj_mem_unitriangular {b u : SpecialLinearGroup (Fin n) K}
    (hb : b ∈ upperTriangular n K) (hu : u ∈ unitriangular n K) :
    b * u * b⁻¹ ∈ unitriangular n K := by
  have hb' : (b : Matrix (Fin n) (Fin n) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hb
  have hu' : (u : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hu.1 _ _ h
  have hbinv := coe_inv_isUpperTriangular hb'
  refine ⟨(upperTriangular n K).mul_mem (mul_mem hb (unitriangular_le_upperTriangular n K hu))
    (inv_mem hb), fun i => ?_⟩
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
    mul_apply_self_of_isUpperTriangular (hb'.mul hu') hbinv,
    mul_apply_self_of_isUpperTriangular hb' hu', hu.2 i, mul_one,
    coe_inv_apply_self_of_isUpperTriangular hb' i]

theorem normalizer_unitriangular :
    normalizer (unitriangular n K : Set (SpecialLinearGroup (Fin n) K)) = upperTriangular n K := by
  apply le_antisymm
  · intro g hg
    rw [← flagFamilyStabilizer_standardFlag, mem_flagFamilyStabilizer]
    intro i
    have hinv : ∀ u ∈ unitriangular n K,
        ∀ v ∈ (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)),
          (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
            (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) := by
      rintro u hu _ ⟨v, hv, rfl⟩
      have hu' : g⁻¹ * u * g ∈ unitriangular n K := by
        have := (mem_normalizer_iff.mp (inv_mem hg) u).mp hu
        simpa using this
      refine ⟨((g⁻¹ * u * g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v,
        flagSpace_invariant i (unitriangular_le_upperTriangular n K hu') hv, ?_⟩
      rw [mulVecLin_apply, mulVecLin_apply, mulVec_mulVec, ← SpecialLinearGroup.coe_mul,
        show g * (g⁻¹ * u * g) = u * g by group, SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
    obtain ⟨m, hm, hW⟩ := eq_flagSpace_of_invariant hinv
    have hfin := congrArg (fun W : Submodule K (Fin n → K) => finrank K W) hW
    rw [show finrank K ((flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K))) =
      finrank K (flagSpace n K i) from LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g) _,
      finrank_flagSpace (by omega), finrank_flagSpace hm] at hfin
    rw [mem_stabilizer]
    change (flagSpace n K i).map _ = flagSpace n K i
    rw [hW, hfin]
  · intro b hb
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => conj_mem_unitriangular hb hu, fun hu => ?_⟩
    have := conj_mem_unitriangular (inv_mem hb) hu
    simpa [mul_assoc] using this

theorem normalizer_projUnitriangular [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    normalizer (projUnitriangular n K : Set (projectiveSL n K)) = projUpperTriangular n K := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  rw [← Nat.card_eq_fintype_card] at hk
  have hU : IsPGroup p (unitriangular n K) :=
    IsPGroup.of_card (n := k * (n * (n - 1) / 2)) (by rw [card_unitriangular, hk, pow_mul])
  have hZ : Nat.Coprime (Nat.card (scalars n K)) p := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : Nat.card (scalars 0 K) = 1 := Nat.card_unique
      rw [h1]
      exact Nat.coprime_one_left p
    refine Nat.Coprime.coprime_dvd_left (card_scalars_dvd hn) ?_
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    have hpq : p ∣ Nat.card K := hk ▸ dvd_pow_self p k.ne_zero
    have h1 : 1 ≤ Nat.card K := Finite.card_pos
    have := Nat.dvd_sub hpq hdvd
    rw [Nat.sub_sub_self h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have key : ∀ h : SpecialLinearGroup (Fin n) K,
      proj n K h ∈ normalizer (projUnitriangular n K : Set (projectiveSL n K)) →
        ∀ u ∈ unitriangular n K, h * u * h⁻¹ ∈ unitriangular n K := by
    intro h hh u hu
    have h1 : proj n K (h * u * h⁻¹) ∈ projUnitriangular n K := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hh (proj n K u)).mp (mem_map_of_mem _ hu)
    obtain ⟨u', hu', hu'eq⟩ := mem_map.mp h1
    set z := u'⁻¹ * (h * u * h⁻¹) with hz
    have hzZ : z ∈ scalars n K := by
      rw [← ker_proj, MonoidHom.mem_ker, hz, map_mul, map_inv, hu'eq, inv_mul_cancel]
    have hzc : z ∈ center (SpecialLinearGroup (Fin n) K) := scalars_le_center n K hzZ
    obtain ⟨a, ha⟩ := hU ⟨u, hu⟩
    obtain ⟨b, hb⟩ := hU ⟨u', hu'⟩
    have ha' : u ^ p ^ a = 1 := congrArg Subtype.val ha
    have hb' : u' ^ p ^ b = 1 := congrArg Subtype.val hb
    have hconj : h * u * h⁻¹ = u' * z := by rw [hz, mul_inv_cancel_left]
    have hzN : z ^ p ^ (a + b) = 1 := by
      have h2 : (h * u * h⁻¹) ^ p ^ (a + b) = 1 := by
        rw [conj_pow, pow_add, pow_mul, ha', one_pow, mul_one, mul_inv_cancel]
      rw [hconj, Commute.mul_pow (mem_center_iff.mp hzc u'), pow_add, mul_comm (p ^ a),
        pow_mul, hb', one_pow, one_mul, ← pow_add, add_comm] at h2
      exact h2
    have hzZcard : z ^ Nat.card (scalars n K) = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨z, hzZ⟩ : scalars n K)))
    have hz1 : z = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hzZcard, hzN⟩
      rwa [(hZ.pow_right (a + b)).gcd_eq_one, pow_one] at this
    rw [hconj, hz1, mul_one]
    exact hu'
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := proj_surjective n K x
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, ← normalizer_unitriangular, mem_normalizer_iff]
    intro u
    refine ⟨key g hx u, fun hu => ?_⟩
    have hx' : proj n K g⁻¹ ∈ normalizer (projUnitriangular n K : Set (projectiveSL n K)) := by
      rw [map_inv]
      exact inv_mem hx
    have := key g⁻¹ hx' _ hu
    simpa [mul_assoc] using this
  · rw [projUpperTriangular, projUnitriangular, ← normalizer_unitriangular]
    exact Subgroup.le_normalizer_map (proj n K)

theorem projFlagFamilyStabilizer_eq_map_conj {V : Fin (n + 1) → Submodule K (Fin n → K)}
    {g : SpecialLinearGroup (Fin n) K}
    (hg : ∀ i : Fin (n + 1), (flagSpace n K i).map (mulVecLin (g : Matrix (Fin n) (Fin n) K)) =
      V i) :
    projFlagFamilyStabilizer V = (projUpperTriangular n K).map
      (MulAut.conj (proj n K g) : projectiveSL n K →* projectiveSL n K) := by
  rw [projFlagFamilyStabilizer, flagFamilyStabilizer_eq_map_conj hg, projUpperTriangular,
    Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem scalars_le_flagFamilyStabilizer (V : Fin (n + 1) → Submodule K (Fin n → K)) :
    scalars n K ≤ flagFamilyStabilizer V := fun _ hg =>
  mem_flagFamilyStabilizer.mpr fun i => scalars_le_stabilizer (V i) hg

theorem coe_sylow_smul {G : Type*} [Group G] {p : ℕ} (x : G) (P : Sylow p G) :
    ((x • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj x : G →* G) := by
  rfl

theorem normalizer_map_conj {G : Type*} [Group G] (x : G) (H : Subgroup G) :
    normalizer ((H.map (MulAut.conj x : G →* G) : Subgroup G) : Set G) =
      (normalizer (H : Set G)).map (MulAut.conj x : G →* G) :=
  (Subgroup.map_equiv_normalizer_eq H (MulAut.conj x)).symm

theorem sylow_normalizers [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (hn : 1 ≤ n) :
    normalizer (unitriangular n K : Set (SpecialLinearGroup (Fin n) K)) = upperTriangular n K ∧
    normalizer (projUnitriangular n K : Set (projectiveSL n K)) = projUpperTriangular n K ∧
    {B₀ | ∃ x : projectiveSL n K, B₀ = (projUpperTriangular n K).map
        (MulAut.conj x : projectiveSL n K →* projectiveSL n K)} =
      {B₀ | ∃ V, IsCompleteFlag V ∧ B₀ = projFlagFamilyStabilizer V} ∧
    (∀ V V' : Fin (n + 1) → Submodule K (Fin n → K), IsCompleteFlag V → IsCompleteFlag V' →
      projFlagFamilyStabilizer V = projFlagFamilyStabilizer V' → V = V') ∧
    sylowNormalizers (projectiveSL n K) p =
      {B₀ | ∃ V, IsCompleteFlag V ∧ B₀ = projFlagFamilyStabilizer V} := by
  classical
  have hNU := normalizer_projUnitriangular (K := K) (n := n) p
  have hconj : {B₀ | ∃ x : projectiveSL n K, B₀ = (projUpperTriangular n K).map
        (MulAut.conj x : projectiveSL n K →* projectiveSL n K)} =
      {B₀ | ∃ V, IsCompleteFlag V ∧ B₀ = projFlagFamilyStabilizer V} := by
    ext B₀
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective n K x
      exact ⟨_, isCompleteFlag_map g, (projFlagFamilyStabilizer_eq_map_conj fun i => rfl).symm⟩
    · rintro ⟨V, hV, rfl⟩
      obtain ⟨g, hg⟩ := exists_map_standardFlag_eq hV
      exact ⟨proj n K g, projFlagFamilyStabilizer_eq_map_conj hg⟩
  refine ⟨normalizer_unitriangular, hNU, hconj, fun V V' hV hV' hVV' => ?_, ?_⟩
  ·
    have hS : flagFamilyStabilizer V = flagFamilyStabilizer V' := by
      have h1 := congrArg (Subgroup.comap (proj n K)) hVV'
      rwa [projFlagFamilyStabilizer, projFlagFamilyStabilizer,
        Subgroup.comap_map_eq_self (by rw [ker_proj]; exact scalars_le_flagFamilyStabilizer V),
        Subgroup.comap_map_eq_self (by rw [ker_proj]; exact scalars_le_flagFamilyStabilizer V')]
        at h1
    obtain ⟨g, hg⟩ := exists_map_standardFlag_eq hV
    set W : Fin (n + 1) → Submodule K (Fin n → K) := fun i =>
      (V' i).map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K))
      with hW
    have hWdim : ∀ i, finrank K (W i) = i := fun i => by
      rw [hW]
      change finrank K ((V' i).map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K))) = i
      rw [show finrank K ((V' i).map (mulVecLin ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K))) = finrank K (V' i) from
          LinearEquiv.finrank_map_eq (SpecialLinearGroup.toLin' g⁻¹) _, hV'.2]
    have hWinv : ∀ i, ∀ u ∈ unitriangular n K, ∀ v ∈ W i,
        (u : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W i := by
      rintro i u hu _ ⟨w, hw, rfl⟩
      have hgu : g * u * g⁻¹ ∈ flagFamilyStabilizer V' := by
        rw [← hS, flagFamilyStabilizer_eq_map_conj hg]
        exact ⟨u, unitriangular_le_upperTriangular n K hu, rfl⟩
      have hstab := mem_stabilizer.mp (mem_flagFamilyStabilizer.mp hgu i)
      have hmem : ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈
          V' i := by
        rw [← hstab]
        exact ⟨w, hw, rfl⟩
      refine ⟨_, hmem, ?_⟩
      change ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
        (u : Matrix (Fin n) (Fin n) K) *ᵥ
          (((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w)
      have hmat : ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((g * u * g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (u : Matrix (Fin n) (Fin n) K) *
            ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
        congrArg Subtype.val (show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group)
      rw [mulVec_mulVec, hmat, ← mulVec_mulVec]
    have hWF := (unitriangular_invariant_subspaces (K := K) (n := n)).2.2 W hWdim hWinv
    have hgg : (g : Matrix (Fin n) (Fin n) K) *
        ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      congrArg Subtype.val (mul_inv_cancel g)
    funext i
    rw [← hg i, ← hWF i, hW]
    beta_reduce
    rw [← Submodule.map_comp, ← mulVecLin_mul, hgg, mulVecLin_one, Submodule.map_id]
  ·
    rw [← hconj]
    obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) p (n := n) hn
    ext B₀
    constructor
    · rintro ⟨T, rfl⟩
      obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (projectiveSL n K) SU T
      refine ⟨x, ?_⟩
      rw [← hx, coe_sylow_smul, normalizer_map_conj, hSU, hNU]
    · rintro ⟨x, rfl⟩
      refine ⟨x • SU, ?_⟩
      rw [coe_sylow_smul, normalizer_map_conj, hSU, hNU]

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
