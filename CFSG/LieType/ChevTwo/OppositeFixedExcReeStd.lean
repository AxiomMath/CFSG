module

public import CFSG.LieType.Ree.ReeHolds
public import CFSG.LieType.Ree.BorelOvergroupClassification
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.BorelTits CFSG.Open

theorem reeStd_le_sylow_of_le_normalizer {G : Type*} [Group G] {p : ℕ} (S : Sylow p G)
    {X : Subgroup G} (hX : IsPGroup p X)
    (hS : (S : Subgroup G) ≤ Subgroup.normalizer (X : Set G)) : X ≤ S :=
  sup_eq_right.mp (S.is_maximal' (hX.to_sup_of_normal_left' S.isPGroup' hS) le_sup_right)

theorem reeStd_fixedOrbitCount_le_two (t : ReeTag) : t.fixedOrbitCount ≤ 2 := by
  cases t <;> decide

section Cert

@[expose] def reeStdSet (t : ReeTag) : Option (Fin t.fixedOrbitCount) → Set (Fin t.tag.rank)
  | none => ∅
  | some j => t.fixedOrbitSet j

@[expose] def reeQJ (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)
    (j : Option (Fin t.fixedOrbitCount)) : Subgroup ↥(t.reeGamma K a) :=
  (parabolicRadical t.tag K (reeStdSet t j)).subgroupOf (t.reeGamma K a)

@[expose] def reePJ (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)
    (j : Option (Fin t.fixedOrbitCount)) : Subgroup ↥(t.reeGamma K a) :=
  (parabolicSubgroup t.tag K (reeStdSet t j)).subgroupOf (t.reeGamma K a)

theorem holds_reeGamma (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ) :
    Holds ↥(t.reeGamma K a) t.prime :=
  (holds_reeFixedGroup t K a).of_mulEquiv
    (MulEquiv.subgroupCongr (ReeTag.reeGamma_eq_reeFixedGroup (t := t) (K := K) (a := a)).symm)

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem reeStd_posUnipotent_le_parabolicRadical_empty :
    posUnipotent t.tag K ≤ parabolicRadical t.tag K (∅ : Set (Fin t.tag.rank)) := by
  refine rootSpan_mono fun α hα => ?_
  refine mem_parabolicRadicalRoots_iff.2 ⟨hα.1, hα.2, ?_⟩
  by_contra h
  have h0 : height α = 0 := Finset.sum_eq_zero fun i _ => by
    by_contra hi
    exact h ⟨i, Set.notMem_empty i, hi⟩
  exact absurd hα.2 (by omega)

theorem reeStd_mem_parabolicRadical_of_conj_mem (j : Fin t.fixedOrbitCount) {x : ModGL t.tag K}
    (hx : x ∈ posUnipotent t.tag K)
    (hnx : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * x *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ posUnipotent t.tag K) :
    x ∈ parabolicRadical t.tag K (t.fixedOrbitSet j) := by
  set n := canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) with hn
  have hnP : n ∈ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :=
    canonicalRep_mem_parabolicSubgroup (ReeTag.fixedOrbitElement_mem_fixedOrbitWeyl j)
  have hnN := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) (t.fixedOrbitSet j) hnP
  have hx' : x ∈ (posUnipotent t.tag K : Set (ModGL t.tag K)) := hx
  rw [posUnipotent_eq_mul_parabolic (t.fixedOrbitSet j)] at hx'
  obtain ⟨q, hq, v, hv, rfl⟩ := hx'
  have hq' : n * q * n⁻¹ ∈ parabolicRadical t.tag K (t.fixedOrbitSet j) :=
    (Subgroup.mem_normalizer_iff.1 hnN q).1 hq
  have hv1 : n * v * n⁻¹ ∈ posUnipotent t.tag K := by
    have h := mul_mem (inv_mem (parabolicRadical_le_posUnipotent _ hq')) hnx
    have e : (n * q * n⁻¹)⁻¹ * (n * (q * v) * n⁻¹) = n * v * n⁻¹ := by group
    rwa [e] at h
  have hv2 : n * v * n⁻¹ ∈ negUnipotent t.tag K := by
    have hmap := (canonical_weyl_root_transport t.tag K).1 (t.fixedOrbitElement j)
      (t.fixedOrbitRoots j) fun α hα => (ReeTag.mem_fixedOrbitRoots_iff.1 hα).1
    have hS : n * v * n⁻¹ ∈ rootSpan t.tag K
        ((fun α => t.fixedOrbitElement j • α) '' t.fixedOrbitRoots j) := by
      rw [← hmap]
      exact ⟨v, hv, rfl⟩
    refine rootSpan_mono ?_ hS
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.smul (ReeTag.mem_fixedOrbitRoots_iff.1 hα).1 _,
      ReeTag.height_fixedOrbitElement_smul_neg hα⟩
  have h1 : n * v * n⁻¹ ∈ posUnipotent t.tag K ⊓ negUnipotent t.tag K := ⟨hv1, hv2⟩
  rw [posUnipotent_inf_negUnipotent, Subgroup.mem_bot, mul_inv_eq_one, mul_eq_left] at h1
  subst h1
  simpa using hq

theorem pCoreOf_le_reeFixedPosUnipotent {P' : Subgroup ↥(t.reeGamma K a)}
    (hU : (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ≤ P') :
    pCoreOf t.prime P' ≤ (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) := by
  have hUp := isPGroup_reeFixedPosUnipotent_subgroupOf (t := t) (K := K) (a := a)
  have hUi := not_dvd_index_reeFixedPosUnipotent (t := t) (K := K) (a := a)
  exact reeStd_le_sylow_of_le_normalizer (hUp.toSylow hUi) (pCoreOf_isPGroup t.prime P')
    (hU.trans (le_normalizer_pCoreOf t.prime P'))

theorem pCoreOf_le_reeQJ_none {P' : Subgroup ↥(t.reeGamma K a)}
    (hU : (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ≤ P') :
    pCoreOf t.prime P' ≤ reeQJ t K a none := fun x hx =>
  Subgroup.mem_subgroupOf.2 (reeStd_posUnipotent_le_parabolicRadical_empty
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 (pCoreOf_le_reeFixedPosUnipotent hU hx))).1)

theorem pCoreOf_le_reeQJ_some {P' : Subgroup ↥(t.reeGamma K a)} (j : Fin t.fixedOrbitCount)
    (hU : (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ≤ P')
    (hn : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      P'.map (t.reeGamma K a).subtype) :
    pCoreOf t.prime P' ≤ reeQJ t K a (some j) := by
  intro x hx
  obtain ⟨n', hn'P, hnn⟩ := hn
  have hxU := pCoreOf_le_reeFixedPosUnipotent hU hx
  have hnx : n' * x * n'⁻¹ ∈ pCoreOf t.prime P' :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf t.prime P' hn'P) x).1 hx
  have hnxU := pCoreOf_le_reeFixedPosUnipotent hU hnx
  have h1 : (x : ModGL t.tag K) ∈ posUnipotent t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hxU)).1
  have h2 : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * (x : ModGL t.tag K) *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈ posUnipotent t.tag K := by
    have e : ((n' * x * n'⁻¹ : ↥(t.reeGamma K a)) : ModGL t.tag K) =
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * (x : ModGL t.tag K) *
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ := by
      rw [← hnn]
      rfl
    rw [← e]
    exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hnxU)).1
  exact Subgroup.mem_subgroupOf.2 (reeStd_mem_parabolicRadical_of_conj_mem j h1 h2)

theorem ree_QJ_pgroup (j : Option (Fin t.fixedOrbitCount)) : IsPGroup t.prime (reeQJ t K a j) :=
  ((isPGroup_posUnipotent (K := K) t.prime t.tag).to_le
    (parabolicRadical_le_posUnipotent _)).comap_subtype

theorem ree_PJ_le_normalizer (j : Option (Fin t.fixedOrbitCount)) :
    reePJ t K a j ≤ Subgroup.normalizer ((reeQJ t K a j : Subgroup ↥(t.reeGamma K a)) :
      Set ↥(t.reeGamma K a)) := by
  intro x hx
  have hxN := parabolicSubgroup_le_normalizer_parabolicRadical (K := K) (reeStdSet t j)
    (Subgroup.mem_subgroupOf.1 hx)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact Subgroup.mem_normalizer_iff.1 hxN (y : ModGL t.tag K)

@[simp] theorem reeStdSet_none (t : ReeTag) : reeStdSet t none = ∅ := rfl

@[simp] theorem reeStdSet_some (t : ReeTag) (j : Fin t.fixedOrbitCount) :
    reeStdSet t (some j) = t.fixedOrbitSet j := rfl

theorem mem_reeQJ {x : ↥(t.reeGamma K a)} {j : Option (Fin t.fixedOrbitCount)} :
    x ∈ reeQJ t K a j ↔ (x : ModGL t.tag K) ∈ parabolicRadical t.tag K (reeStdSet t j) :=
  Iff.rfl

theorem reeQJ_none :
    reeQJ t K a none = (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) := by
  have h : parabolicRadical t.tag K (∅ : Set (Fin t.tag.rank)) = posUnipotent t.tag K :=
    le_antisymm (parabolicRadical_le_posUnipotent _)
      reeStd_posUnipotent_le_parabolicRadical_empty
  ext x
  rw [mem_reeQJ, reeStdSet_none, h]
  exact ⟨fun hx => Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, x.2⟩),
    fun hx => (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1⟩

theorem reeQJ_some (j : Fin t.fixedOrbitCount) :
    reeQJ t K a (some j) =
      (t.reeFixedOrbitComplementUnipotent K a j).subgroupOf (t.reeGamma K a) := by
  ext x
  exact ⟨fun hx => Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, x.2⟩),
    fun hx => (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1⟩

theorem reePJ_some (j : Fin t.fixedOrbitCount) :
    reePJ t K a (some j) = (t.reeParabolic K a {j}).subgroupOf (t.reeGamma K a) := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : (x : ModGL t.tag K) ∈ ((t.reeGamma K a ⊓
        parabolicSubgroup t.tag K (t.fixedOrbitSet j) : Subgroup (ModGL t.tag K)) :
          Set (ModGL t.tag K)) := Subgroup.mem_inf.2 ⟨x.2, hx⟩
    rw [coe_reeGamma_inf_parabolicSubgroup j] at hx'
    refine Subgroup.mem_subgroupOf.2 ?_
    rcases hx' with hB | hD
    · exact t.reeFixedBorel_le_reeParabolic K a _ hB
    · obtain ⟨b, hb, b', hb', e⟩ := mem_reeFixedBruhatCell.1 hD
      rw [← e]
      exact mul_mem (mul_mem (t.reeFixedBorel_le_reeParabolic K a _ hb)
        (t.canonicalRep_mem_reeParabolic K a (Set.mem_singleton j)))
        (t.reeFixedBorel_le_reeParabolic K a _ hb')
  · exact (Subgroup.mem_inf.1 (reeParabolic_le_reeGamma_inf (K := K) (a := a)
      (subset_refl ({j} : Set (Fin t.fixedOrbitCount))) (Subgroup.mem_subgroupOf.1 hx))).2

theorem ree_standard_position (Q : Subgroup ↥(t.reeGamma K a)) (hQ : Q ≠ ⊥)
    (hQ2 : IsPGroup t.prime Q) :
    ∃ (g : ↥(t.reeGamma K a)) (j : Option (Fin t.fixedOrbitCount)),
      (∀ x ∈ Subgroup.normalizer (Q : Set ↥(t.reeGamma K a)), g⁻¹ * x * g ∈ reePJ t K a j) ∧
        ∀ q ∈ Q, g⁻¹ * q * g ∈ reeQJ t K a j := by
  classical
  have hUp := isPGroup_reeFixedPosUnipotent_subgroupOf (t := t) (K := K) (a := a)
  have hUi := not_dvd_index_reeFixedPosUnipotent (t := t) (K := K) (a := a)
  obtain ⟨S, P, hPtop, hNQ, -, hQP, hNS⟩ := holds_reeGamma t K a Q hQ hQ2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (t.reeGamma K a) (hUp.toSylow hUi) S
  have hSc : (S : Subgroup ↥(t.reeGamma K a)) =
      ((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a)).map
        (MulAut.conj c).toMonoidHom := by
    rw [← hc, coe_smul_sylow_eq_map]
    rfl
  have hBN : ∀ b : ↥(t.reeGamma K a), (b : ModGL t.tag K) ∈ t.reeFixedBorel K a →
      b ∈ Subgroup.normalizer
        (((t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) : Subgroup _) : Set _) := by
    intro b hb
    have hbN := reeFixedBorel_le_normalizer_reeFixedPosUnipotent hb
    rw [Subgroup.mem_normalizer_iff]
    intro u
    exact Subgroup.mem_normalizer_iff.1 hbN (u : ModGL t.tag K)
  obtain ⟨P', hP'⟩ : ∃ P' : Subgroup ↥(t.reeGamma K a),
      P' = P.map (MulAut.conj c⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hBP : ∀ b : ↥(t.reeGamma K a), (b : ModGL t.tag K) ∈ t.reeFixedBorel K a → b ∈ P' := by
    intro b hb
    have h1 : (MulAut.conj c) b ∈
        Subgroup.normalizer ((S : Subgroup ↥(t.reeGamma K a)) : Set _) := by
      rw [hSc, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.mem_map_of_mem _ (hBN b hb)
    rw [hP']
    refine ⟨(MulAut.conj c) b, hNS h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hUP : (t.reeFixedPosUnipotent K a).subgroupOf (t.reeGamma K a) ≤ P' := fun u hu =>
    hBP u (reeFixedPosUnipotent_le_reeFixedBorel (Subgroup.mem_subgroupOf.1 hu))
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (ModGL t.tag K), A = P'.map (t.reeGamma K a).subtype :=
    ⟨_, rfl⟩
  have hAmem : ∀ y : ↥(t.reeGamma K a), y ∈ P' → (y : ModGL t.tag K) ∈ A := fun y hy => by
    rw [hA]
    exact ⟨y, hy, rfl⟩
  have hAΓ : A ≤ t.reeGamma K a := by
    rw [hA]
    exact Subgroup.map_subtype_le _
  have hBA : t.reeFixedBorel K a ≤ A := fun b hb =>
    hAmem ⟨b, reeFixedBorel_le_reeGamma hb⟩ (hBP _ hb)
  obtain ⟨hAeq, -⟩ := ReeTag.ree_Borel_overgroup_classification t a K A hBA hAΓ
  obtain ⟨J₀, hAJ⟩ : ∃ J₀ : Set (Fin t.fixedOrbitCount), A = t.reeParabolic K a J₀ :=
    ⟨_, hAeq⟩
  have hNQ' : ∀ x ∈ Subgroup.normalizer (Q : Set ↥(t.reeGamma K a)), c⁻¹ * x * c ∈ P' := by
    intro x hx
    rw [hP']
    refine ⟨x, hNQ hx, ?_⟩
    simp [MulAut.conj_apply]
  have hQP' : ∀ q ∈ Q, c⁻¹ * q * c ∈ pCoreOf t.prime P' := by
    intro q hq
    rw [hP', pCoreOf_map_mulEquiv t.prime (MulAut.conj c⁻¹) P]
    refine ⟨q, hQP hq, ?_⟩
    simp [MulAut.conj_apply]
  by_cases hJe : J₀ = ∅
  ·
    have hAB : A = t.reeFixedBorel K a := by rw [hAJ, hJe, ReeTag.reeParabolic_empty]
    refine ⟨c, none, fun x hx => ?_, fun q hq => ?_⟩
    · have hy := hAmem _ (hNQ' x hx)
      rw [hAB] at hy
      exact Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _ (Subgroup.mem_inf.1 hy).1)
    · exact pCoreOf_le_reeQJ_none hUP (hQP' q hq)
  · by_cases hJu : J₀ = Set.univ
    ·
      exfalso
      have hΓP : t.reeGamma K a = t.reeParabolic K a Set.univ := by
        obtain ⟨h, -⟩ := ReeTag.ree_Borel_overgroup_classification t a K (t.reeGamma K a)
          reeFixedBorel_le_reeGamma le_rfl
        have hu : {j | canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
            t.reeGamma K a} = Set.univ :=
          Set.eq_univ_of_forall fun j =>
            (canonicalRep_mem_reeFixedMonomial t K a (ReeTag.fixedOrbitElement_mem j)).2
        rw [hu] at h
        exact h
      have hAΓ' : A = t.reeGamma K a := by rw [hAJ, hJu, hΓP]
      have hP'top : P' = ⊤ := by
        rw [eq_top_iff]
        intro y _
        have hy : (y : ModGL t.tag K) ∈ A := by rw [hAΓ']; exact y.2
        rw [hA] at hy
        obtain ⟨y', hy', hyy⟩ := hy
        have : y' = y := Subtype.ext hyy
        rwa [this] at hy'
      apply hPtop
      rw [eq_top_iff]
      intro x _
      have hx : (MulAut.conj c⁻¹) x ∈ P' := by rw [hP'top]; exact Subgroup.mem_top _
      rw [hP'] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have : z = x := (MulAut.conj c⁻¹).injective hzx
      rwa [this] at hz
    · obtain ⟨j, hj⟩ := Set.nonempty_iff_ne_empty.2 hJe
      have hJj : J₀ ⊆ {j} := by
        intro k hk
        by_contra hkj
        apply hJu
        have hr := reeStd_fixedOrbitCount_le_two t
        refine Set.eq_univ_of_forall fun l => ?_
        have hjk : (j : ℕ) ≠ k := fun e => hkj (Fin.ext e.symm)
        by_cases hlj : l = j
        · exact hlj ▸ hj
        · by_cases hlk : l = k
          · exact hlk ▸ hk
          · exfalso
            have hlj' : (l : ℕ) ≠ j := fun e => hlj (Fin.ext e)
            have hlk' : (l : ℕ) ≠ k := fun e => hlk (Fin.ext e)
            have := l.2
            have := j.2
            have := k.2
            omega
      have hAle : A ≤ t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) := by
        rw [hAJ]
        exact ReeTag.reeParabolic_le_reeGamma_inf (K := K) (a := a) hJj
      have hnA : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
          P'.map (t.reeGamma K a).subtype := by
        rw [← hA, hAJ]
        exact t.canonicalRep_mem_reeParabolic K a hj
      refine ⟨c, some j, fun x hx => ?_, fun q hq => ?_⟩
      · have hy := hAmem _ (hNQ' x hx)
        exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (hAle hy)).2
      · exact pCoreOf_le_reeQJ_some j hUP hnA (hQP' q hq)

end Cert

end CFSG.LieType.ChevTwo.Semi
