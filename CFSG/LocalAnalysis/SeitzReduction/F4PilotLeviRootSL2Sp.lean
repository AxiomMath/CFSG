module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauMat tauPair tauAut tauAut_proj)

section Conj

variable {G : Type*} [Group G]

private theorem map_conj_map_conj (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_mulAut_map_conj (H : Subgroup G) (g : G) (φ : MulAut G) :
    (H.map (MulAut.conj g).toMonoidHom).map φ.toMonoidHom =
      (H.map φ.toMonoidHom).map (MulAut.conj (φ g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

end Conj

@[expose] noncomputable def spRootSL2 (n : ℕ) (K : Type) [Field K] (v : Fin n → ℤ) :
    Subgroup (StatedSp n K) :=
  Symplectic.rootGroup n K v ⊔ Symplectic.rootGroup n K (-v)

@[expose] def IsSpRootSL2 (n : ℕ) (K : Type) [Field K] (H : Subgroup (StatedSp n K)) : Prop :=
  ∃ v ∈ roots (isFiniteType_cartanC n) ∅, ∃ g : StatedSp n K,
    H = (spRootSL2 n K v).map (MulAut.conj g).toMonoidHom

variable {K : Type} [Field K] {n : ℕ}

theorem isSpRootSL2_spRootSL2 {v : Fin n → ℤ} (hv : v ∈ roots (isFiniteType_cartanC n) ∅) :
    IsSpRootSL2 n K (spRootSL2 n K v) :=
  ⟨v, hv, 1, by ext x; simp⟩

theorem IsSpRootSL2.map_conj {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H)
    (h : StatedSp n K) : IsSpRootSL2 n K (H.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨v, hv, g, rfl⟩ := hH
  exact ⟨v, hv, h * g, map_conj_map_conj _ g h⟩

theorem IsSpRootSL2.map_of_forall {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H)
    (φ : MulAut (StatedSp n K))
    (hφ : ∀ v ∈ roots (isFiniteType_cartanC n) ∅, ∃ w ∈ roots (isFiniteType_cartanC n) ∅,
      (spRootSL2 n K v).map φ.toMonoidHom = spRootSL2 n K w) :
    IsSpRootSL2 n K (H.map φ.toMonoidHom) := by
  obtain ⟨v, hv, g, rfl⟩ := hH
  obtain ⟨w, hw, he⟩ := hφ v hv
  exact ⟨w, hw, φ g, by rw [map_mulAut_map_conj, he]⟩

theorem fieldSp_elt (σ : K ≃+* K) (r : RootSubgroupIndex n) (c : K) :
    fieldSp n K σ (elt r c) = elt r (σ c) := by
  apply mat_injective
  rw [mat_elt]
  change (mat n K (elt r c)).map σ = _
  rw [mat_elt]
  ext a b
  cases r <;> simp [E, Matrix.single_apply, Matrix.one_apply, apply_ite σ]

theorem map_fieldSp_rootGroup (σ : K ≃+* K) (v : Fin n → ℤ) :
    (Symplectic.rootGroup n K v).map (fieldSp n K σ).toMonoidHom = Symplectic.rootGroup n K v := by
  by_cases hv : ∃ r : RootSubgroupIndex n, stdVec r = toStd n v
  · obtain ⟨r, hr⟩ := hv
    ext x
    simp only [Subgroup.mem_map, mem_rootGroup_iff hr, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
      exact ⟨σ c, fieldSp_elt σ r c⟩
    · rintro ⟨c, rfl⟩
      exact ⟨elt r (σ.symm c), ⟨_, rfl⟩, by rw [fieldSp_elt, RingEquiv.apply_symm_apply]⟩
  · have hbot : Symplectic.rootGroup n K v = ⊥ := by
      rw [Symplectic.rootGroup]
      refine eq_bot_iff.2 (iSup₂_le fun r hr => absurd ⟨r, hr⟩ hv)
    rw [hbot, Subgroup.map_bot]

theorem map_fieldSp_spRootSL2 (σ : K ≃+* K) (v : Fin n → ℤ) :
    (spRootSL2 n K v).map (fieldSp n K σ).toMonoidHom = spRootSL2 n K v := by
  rw [spRootSL2, Subgroup.map_sup, map_fieldSp_rootGroup, map_fieldSp_rootGroup]

theorem IsSpRootSL2.map_fieldSp {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H)
    (σ : K ≃+* K) : IsSpRootSL2 n K (H.map (fieldSp n K σ).toMonoidHom) :=
  hH.map_of_forall _ fun v hv => ⟨v, hv, map_fieldSp_spRootSL2 σ v⟩

theorem center_statedSp_eq_bot_of_charTwo [NeZero n] [CharP K 2] :
    center (StatedSp n K) = ⊥ := by
  rw [Symplectic.center_eq]
  exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.spScalars_eq_bot_of_charTwo

@[expose] def negIdx : RootSubgroupIndex n → RootSubgroupIndex n
  | .positiveLong i => .negativeLong i
  | .negativeLong i => .positiveLong i
  | .difference i j h => .difference j i h.symm
  | .positiveSum i j h => .negativeSum i j h
  | .negativeSum i j h => .positiveSum i j h

theorem stdVec_negIdx (r : RootSubgroupIndex n) : stdVec (negIdx r) = -stdVec r := by
  cases r <;> simp [negIdx, stdVec]

theorem mem_rootGroup_iff_elt {v : Fin n → ℤ} {r : RootSubgroupIndex n}
    (hr : stdVec r = toStd n v) {x : StatedSp n K} :
    x ∈ Symplectic.rootGroup n K v ↔ ∃ c : K, elt r c = x := by
  rw [mem_rootGroup_iff hr]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem map_rootGroup_of_elt {m : ℕ} (φ : StatedSp n K →* StatedSp m K)
    {r : RootSubgroupIndex n} {r' : RootSubgroupIndex m} {f : K → K}
    (hf : Function.Surjective f) (hφ : ∀ c, φ (elt r c) = elt r' (f c))
    {v : Fin n → ℤ} {w : Fin m → ℤ} (hv : stdVec r = toStd n v) (hw : stdVec r' = toStd m w) :
    (Symplectic.rootGroup n K v).map φ = Symplectic.rootGroup m K w := by
  ext x
  simp only [Subgroup.mem_map, mem_rootGroup_iff_elt hv, mem_rootGroup_iff_elt hw]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨f c, (hφ c).symm⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨c, rfl⟩ := hf d
    exact ⟨elt r c, ⟨c, rfl⟩, hφ c⟩

@[expose] def tauIdx : RootSubgroupIndex 2 → RootSubgroupIndex 2
  | .positiveLong i => if i = 0 then .positiveSum 0 1 (by decide) else .difference 0 1 (by decide)
  | .negativeLong i => if i = 0 then .negativeSum 0 1 (by decide) else .difference 1 0 (by decide)
  | .difference i _ _ => if i = 0 then .positiveLong 1 else .negativeLong 1
  | .positiveSum _ _ _ => .positiveLong 0
  | .negativeSum _ _ _ => .negativeLong 0

@[expose] def tauExp : RootSubgroupIndex 2 → ℕ
  | .positiveLong _ => 1
  | .negativeLong _ => 1
  | .difference _ _ _ => 2
  | .positiveSum _ _ _ => 2
  | .negativeSum _ _ _ => 2

theorem negIdx_tauIdx (r : RootSubgroupIndex 2) : negIdx (tauIdx r) = tauIdx (negIdx r) := by
  cases r with
  | positiveLong i => fin_cases i <;> rfl
  | negativeLong i => fin_cases i <;> rfl
  | difference i j h => fin_cases i <;> fin_cases j <;> first | exact absurd rfl h | rfl
  | positiveSum i j h => fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | rfl
  | negativeSum i j h => fin_cases i <;> fin_cases j <;> first | exact absurd h (by decide) | rfl

theorem tauExp_negIdx (r : RootSubgroupIndex 2) : tauExp (negIdx r) = tauExp r := by
  cases r <;> rfl

theorem tauExp_eq (r : RootSubgroupIndex 2) : tauExp r = 1 ∨ tauExp r = 2 := by
  cases r <;> simp [tauExp]

section Tau

variable [CharP K 2]

theorem mat_tauSp (g : StatedSp 2 K) : mat 2 K (tauSp g) = tauMat (mat 2 K g) :=
  rfl

theorem tauSp_elt (r : RootSubgroupIndex 2) (c : K) :
    tauSp (elt r c) = elt (tauIdx r) (c ^ tauExp r) := by
  apply mat_injective
  rw [mat_elt, mat_tauSp, mat_elt]
  cases r with
  | positiveLong i =>
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq]
  | negativeLong i =>
    fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
        CharTwo.neg_eq]
  | difference i j h =>
    fin_cases i <;> fin_cases j
    · exact absurd rfl h
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
          CharTwo.neg_eq, pow_two]
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
          CharTwo.neg_eq, pow_two]
    · exact absurd rfl h
  | positiveSum i j h =>
    fin_cases i <;> fin_cases j
    · exact absurd h (by decide)
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
          CharTwo.neg_eq, pow_two]
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  | negativeSum i j h =>
    fin_cases i <;> fin_cases j
    · exact absurd h (by decide)
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [tauIdx, tauExp, tauMat, tauPair, E, Matrix.single_apply, Matrix.one_apply,
          CharTwo.neg_eq, pow_two]
    · exact absurd h (by decide)
    · exact absurd h (by decide)

variable [Finite K]

theorem pow_tauExp_surjective (r : RootSubgroupIndex 2) :
    Function.Surjective fun c : K => c ^ tauExp r := by
  rcases tauExp_eq r with h | h <;> rw [h]
  · exact fun c => ⟨c, pow_one c⟩
  · exact Finite.surjective_of_injective (CharTwo.sq_injective (R := K))

theorem exists_map_tauSp_spRootSL2 {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    ∃ w ∈ roots (isFiniteType_cartanC 2) ∅,
      (spRootSL2 2 K v).map (tauSp : StatedSp 2 K →* StatedSp 2 K) = spRootSL2 2 K w := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  obtain ⟨w, hw, hwr⟩ := CFSG.LieType.Steinberg.Sp.exists_root_of_stdVec (tauIdx r)
  refine ⟨w, hw, ?_⟩
  have hr' : stdVec (negIdx r) = toStd 2 (-v) := by rw [stdVec_negIdx, hr, toStd_neg']
  have hw' : stdVec (tauIdx (negIdx r)) = toStd 2 (-w) := by
    rw [← negIdx_tauIdx, stdVec_negIdx, toStd_neg', hwr]
  rw [spRootSL2, spRootSL2, Subgroup.map_sup,
    map_rootGroup_of_elt _ (pow_tauExp_surjective r) (tauSp_elt r) hr hwr.symm,
    map_rootGroup_of_elt _ (pow_tauExp_surjective (negIdx r)) (tauSp_elt (negIdx r)) hr' hw']

theorem IsSpRootSL2.map_tauEquiv {H : Subgroup (StatedSp 2 K)} (hH : IsSpRootSL2 2 K H) :
    IsSpRootSL2 2 K (H.map (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := K)).toMonoidHom) :=
  hH.map_of_forall _ fun _ hv => exists_map_tauSp_spRootSL2 hv

end Tau

section NormalForm

variable [Finite K] [CharP K 2]

theorem exists_eq_conj_mul_fieldSp (hn : 3 ≤ n) (α : MulAut (StatedSp n K)) :
    ∃ (s : StatedSp n K) (σ : K ≃+* K), ∀ g, α g = s * fieldSp n K σ g * s⁻¹ := by
  have : NeZero n := ⟨by omega⟩
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := n) (K := K)
  set πe := MulEquiv.ofBijective (proj n K) hπ with hπe
  obtain ⟨A, σ, hβ⟩ := (automorphism_generation (K := K) hn).2 (πe.symm.trans (α.trans πe))
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp A
  refine ⟨s, σ, fun g => hπ.1 ?_⟩
  have h1 : (πe.symm.trans (α.trans πe)) (proj n K g) = proj n K (α g) := by
    change πe (α (πe.symm (πe g))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [hβ, hs, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h1
  rw [← h1]
  rfl

theorem exists_eq_conj_mul_fieldSp_tauSp (α : MulAut (StatedSp 2 K)) :
    ∃ (s : StatedSp 2 K) (σ : K ≃+* K),
      (∀ g, α g = s * fieldSp 2 K σ g * s⁻¹) ∨ (∀ g, α g = s * fieldSp 2 K σ (tauSp g) * s⁻¹) := by
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := 2) (K := K)
  set πe := MulEquiv.ofBijective (proj 2 K) hπ with hπe
  obtain ⟨A, σ, ε, hε, hβ⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow
      (πe.symm.trans (α.trans πe))
  obtain ⟨s, hs⟩ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_conjAut_eq_statedSp A
  have h1 : ∀ g, (πe.symm.trans (α.trans πe)) (proj 2 K g) = proj 2 K (α g) := by
    intro g
    change πe (α (πe.symm (πe g))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  refine ⟨s, σ, ?_⟩
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · refine Or.inl fun g => hπ.1 ?_
    have h := h1 g
    rw [hβ, hs, pow_zero, mul_one, MulAut.mul_apply, fieldAut_proj, conjAut_proj] at h
    rw [← h]
    rfl
  · refine Or.inr fun g => hπ.1 ?_
    have h := h1 g
    rw [hβ, hs, pow_one, MulAut.mul_apply, MulAut.mul_apply, tauAut_proj, fieldAut_proj,
      conjAut_proj] at h
    rw [← h]
    rfl

theorem isSpRootSL2_map_mulAut_of_three_le (hn : 3 ≤ n) (α : MulAut (StatedSp n K))
    {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H) :
    IsSpRootSL2 n K (H.map α.toMonoidHom) := by
  obtain ⟨s, σ, h⟩ := exists_eq_conj_mul_fieldSp hn α
  have e : H.map α.toMonoidHom =
      (H.map (fieldSp n K σ).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [h g, MulAut.conj_apply]
  rw [e]
  exact (hH.map_fieldSp σ).map_conj s

theorem isSpRootSL2_map_mulAut_two (α : MulAut (StatedSp 2 K)) {H : Subgroup (StatedSp 2 K)}
    (hH : IsSpRootSL2 2 K H) : IsSpRootSL2 2 K (H.map α.toMonoidHom) := by
  obtain ⟨s, σ, h | h⟩ := exists_eq_conj_mul_fieldSp_tauSp α
  · have e : H.map α.toMonoidHom =
        (H.map (fieldSp 2 K σ).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext g
      simp [h g, MulAut.conj_apply]
    rw [e]
    exact (hH.map_fieldSp σ).map_conj s
  · have e : H.map α.toMonoidHom =
        ((H.map (CFSG.QuasithinUnique.Lin2.Five.tauEquiv (F := K)).toMonoidHom).map
          (fieldSp 2 K σ).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext g
      simp [h g, MulAut.conj_apply]
      rfl
    rw [e]
    exact (hH.map_tauEquiv.map_fieldSp σ).map_conj s

theorem isSpRootSL2_map_mulAut (hn : n = 2 ∨ 3 ≤ n) (α : MulAut (StatedSp n K))
    {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H) :
    IsSpRootSL2 n K (H.map α.toMonoidHom) := by
  rcases hn with rfl | hn
  · exact isSpRootSL2_map_mulAut_two α hH
  · exact isSpRootSL2_map_mulAut_of_three_le hn α hH

theorem exists_isSpRootSL2_map_mulEquiv (hn : n = 2 ∨ 3 ≤ n) {M M' : Type*} [Group M]
    [Group M'] (e : StatedSp n K ≃* M) (e' : StatedSp n K ≃* M') (ι : M ≃* M')
    {H : Subgroup (StatedSp n K)} (hH : IsSpRootSL2 n K H) :
    ∃ H' : Subgroup (StatedSp n K), IsSpRootSL2 n K H' ∧
      (H.map e.toMonoidHom).map ι.toMonoidHom = H'.map e'.toMonoidHom := by
  set α : MulAut (StatedSp n K) := (e.trans ι).trans e'.symm
  refine ⟨H.map α.toMonoidHom, isSpRootSL2_map_mulAut hn α hH, ?_⟩
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [α]

end NormalForm

end CFSG.SeitzReduction.F4Pilot
