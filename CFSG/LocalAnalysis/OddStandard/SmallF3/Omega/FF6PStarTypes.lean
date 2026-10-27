module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PStarN1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private instance ffOutFF6PStarTypes_decEvenVec {n : ℕ} (v : Fin n → ZMod 2) :
    Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private noncomputable abbrev ffOutFF6PStarTypes_N (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) : Subgroup ↥(omegaProj hQ) :=
  Subgroup.normalizer ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))

private theorem ffOutFF6PStarTypes_exists_perm_permVec :
    ∀ v u : Fin 5 → ZMod 2, vecWeight v = vecWeight u →
      ∃ σ : Equiv.Perm (Fin 5), permVec σ v = u := by
  decide +kernel

private theorem ffOutFF6PStarTypes_exists_perm_act :
    ∀ J K : Finset (Fin 5), J.card = K.card → ∃ σ : Equiv.Perm (Fin 5), ffAct σ J = K := by
  decide +kernel

private theorem ffOutFF6PStarTypes_isEvenVec_permVec :
    ∀ (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2),
      IsEvenVec v → IsEvenVec (permVec σ v) := by
  decide +kernel

private theorem ffOutFF6PStarTypes_vecWeight_permVec :
    ∀ (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2),
      vecWeight (permVec σ v) = vecWeight v := by
  decide +kernel

private theorem ffOutFF6PStarTypes_C2 :
    Nat.card {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ vecWeight u = 2} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem ffOutFF6PStarTypes_C4 :
    Nat.card {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ vecWeight u = 4} = 5 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem ffOutFF6PStarTypes_Dcard (k : ℕ) :
    Nat.card {K : Finset (Fin 5) // K.card = k} = Nat.choose 5 k := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun K : Finset (Fin 5) => K.card = k) =
      Finset.univ.powersetCard k := by
    ext K
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    simp
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private noncomputable def ffOutFF6PStarTypes_cls (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (K : Finset (Fin 5)) (hK : Even K.card) :
    ↥(omegaProj hQ) :=
  omegaToProj hQ ⟨fr.signChange (ffOpt K),
    ffB0p_le_omega hQ fr ((mem_ffB0p_iff_ffOpt fr).mpr ⟨K, hK, rfl⟩)⟩

private theorem ffOutFF6PStarTypes_cls_coe (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (K : Finset (Fin 5)) (hK : Even K.card) :
    (ffOutFF6PStarTypes_cls hQ fr K hK : ProjOrth Q) =
      toProj Q (fr.signChange (ffOpt K)) :=
  coe_omegaToProj hQ _

private def ffOutFF6PStarTypes_O (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (k : ℕ) : Set ↥(omegaProj hQ) :=
  {x | ∃ K : Finset (Fin 5), K.card = k ∧
    (x : ProjOrth Q) = toProj Q (fr.signChange (ffOpt K))}

private theorem ffOutFF6PStarTypes_conjClassIn_eq (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ)}
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr) (ffOutFF6PStarTypes_N hQ fr) ⊤)
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    conjClassIn (ffOutFF6PStarTypes_N hQ fr) (ψ v) =
      {x | ∃ u : Fin 5 → ZMod 2, IsEvenVec u ∧ vecWeight u = vecWeight v ∧ ψ u = x} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨σ, -, hσv⟩ := hψ.2.2.2.1 n hn
    exact ⟨permVec σ v, ffOutFF6PStarTypes_isEvenVec_permVec σ v hv,
      ffOutFF6PStarTypes_vecWeight_permVec σ v, (hσv v hv).symm⟩
  · rintro ⟨u, hu, hwt, rfl⟩
    obtain ⟨σ, hσ⟩ := ffOutFF6PStarTypes_exists_perm_permVec v u hwt.symm
    obtain ⟨n, hn, hnσ⟩ := hψ.2.2.2.2 σ (Subgroup.mem_top σ)
    exact ⟨n, hn, by rw [hnσ v hv, hσ]⟩

private theorem ffOutFF6PStarTypes_conjClassIn_eq_O (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) {ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ)}
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr) (ffOutFF6PStarTypes_N hQ fr) ⊤)
    {v : Fin 5 → ZMod 2} {J : Finset (Fin 5)} (hJe : Even J.card)
    (hJv : (ψ v : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J))) :
    conjClassIn (ffOutFF6PStarTypes_N hQ fr) (ψ v) =
      ffOutFF6PStarTypes_O hQ fr J.card := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨σ, hσ⟩ := ff6p_star_normalizer_act hQ hdim hsgn fr hn
    have hKJ : Even (ffAct σ J).card := by rw [ffAct_card]; exact hJe
    refine ⟨ffAct σ J, ffAct_card σ J, ?_⟩
    have hb := hσ J (ψ v) (ffOutFF6PStarTypes_cls hQ fr (ffAct σ J) hKJ) hJe hJv
      (ffOutFF6PStarTypes_cls_coe hQ fr (ffAct σ J) hKJ)
    exact (congrArg Subtype.val hb).trans
      (ffOutFF6PStarTypes_cls_coe hQ fr (ffAct σ J) hKJ)
  · rintro ⟨K, hKcard, hKx⟩
    obtain ⟨σ, hσJ⟩ := ffOutFF6PStarTypes_exists_perm_act J K hKcard.symm
    obtain ⟨n, hn, hnσ⟩ := ff6p_star_exists_normalizer hQ hdim hsgn fr σ
    have hx' : (x : ProjOrth Q) = toProj Q (fr.signChange (ffOpt (ffAct σ J))) := by
      rw [hσJ]; exact hKx
    exact ⟨n, hn, (hnσ J (ψ v) x hJe hJv hx').symm⟩

private theorem ffOutFF6PStarTypes_O_card (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) (J : Finset (Fin 5)) (hJe : Even J.card) :
    Nat.card ↥(ffOutFF6PStarTypes_O hQ fr J.card) =
      Nat.card {K : Finset (Fin 5) // K.card = J.card} := by
  let g : {K : Finset (Fin 5) // K.card = J.card} →
      ↥(ffOutFF6PStarTypes_O hQ fr J.card) := fun K =>
    ⟨ffOutFF6PStarTypes_cls hQ fr K.1 (by rw [K.2]; exact hJe),
      ⟨K.1, K.2, ffOutFF6PStarTypes_cls_coe hQ fr K.1 _⟩⟩
  have hgc : ∀ K : {K : Finset (Fin 5) // K.card = J.card},
      ((g K : ↥(omegaProj hQ)) : ProjOrth Q) =
        toProj Q (fr.signChange (ffOpt K.1)) := by
    intro K
    dsimp only [g]
    exact ffOutFF6PStarTypes_cls_coe hQ fr K.1 (by rw [K.2]; exact hJe)
  have hg : Function.Bijective g := by
    constructor
    · intro K K' h
      have h2 : ((g K : ↥(omegaProj hQ)) : ProjOrth Q) =
          ((g K' : ↥(omegaProj hQ)) : ProjOrth Q) :=
        congrArg Subtype.val (congrArg Subtype.val h)
      have h1 : toProj Q (fr.signChange (ffOpt K.1)) =
          toProj Q (fr.signChange (ffOpt K'.1)) :=
        (hgc K).symm.trans (h2.trans (hgc K'))
      rcases (ff6p_toProj_signChange_eq_iff fr (ffOpt K.1) (ffOpt K'.1)).mp h1 with h3 | h3
      · exact Subtype.ext (ffOpt_injective h3)
      · exfalso
        have hmem : none ∈ ffOpt K.1 := by
          rw [h3, Finset.mem_compl]
          exact none_notMem_ffOpt K'.1
        exact none_notMem_ffOpt K.1 hmem
    · rintro ⟨x, K, hKcard, hKx⟩
      refine ⟨⟨K, hKcard⟩, ?_⟩
      apply Subtype.ext
      have h1 : ((g ⟨K, hKcard⟩ : ↥(omegaProj hQ)) : ProjOrth Q) =
          toProj Q (fr.signChange (ffOpt K)) := hgc ⟨K, hKcard⟩
      exact Subtype.ext (h1.trans hKx.symm)
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

private theorem ffOutFF6PStarTypes_orbit_card (hQ : Q.Nondegenerate)
    (fr : PFrame Q (Option (Fin 5)) ffC) {ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ)}
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr) (ffOutFF6PStarTypes_N hQ fr) ⊤)
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    Nat.card ↥(conjClassIn (ffOutFF6PStarTypes_N hQ fr) (ψ v)) =
      Nat.card {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ vecWeight u = vecWeight v} := by
  rw [ffOutFF6PStarTypes_conjClassIn_eq hQ fr hψ hv]
  let f : {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ vecWeight u = vecWeight v} →
      {x : ↥(omegaProj hQ) // ∃ u : Fin 5 → ZMod 2,
        IsEvenVec u ∧ vecWeight u = vecWeight v ∧ ψ u = x} :=
    fun u => ⟨ψ u.1, u.1, u.2.1, u.2.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (hψ.2.1 a.1 b.1 a.2.1 b.2.1 (congrArg Subtype.val hab))
    · rintro ⟨x, u, hu, hwt, rfl⟩
      exact ⟨⟨u, hu, hwt⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem ffOutFF6PStarTypes_card (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) {ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ)}
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr) (ffOutFF6PStarTypes_N hQ fr) ⊤)
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : vecWeight v = 2 ∨ vecWeight v = 4)
    {J : Finset (Fin 5)} (hJe : Even J.card)
    (hJv : (ψ v : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J))) :
    J.card = vecWeight v := by
  have hEq : Nat.card {u : Fin 5 → ZMod 2 // IsEvenVec u ∧ vecWeight u = vecWeight v} =
      Nat.card {K : Finset (Fin 5) // K.card = J.card} := by
    rw [← ffOutFF6PStarTypes_orbit_card hQ fr hψ hv,
      ffOutFF6PStarTypes_conjClassIn_eq_O hQ hdim hsgn fr hψ hJe hJv,
      ffOutFF6PStarTypes_O_card hQ fr J hJe]
  rw [ffOutFF6PStarTypes_Dcard J.card] at hEq
  have hcases : J.card = 0 ∨ J.card = 2 ∨ J.card = 4 := by
    obtain ⟨m, hm⟩ := hJe
    have hle : J.card ≤ 5 := by simpa using Finset.card_le_univ J
    omega
  rcases hw with hw2 | hw4
  · rw [hw2] at hEq ⊢
    rw [ffOutFF6PStarTypes_C2] at hEq
    rcases hcases with h0 | h2 | h4
    · rw [h0, show Nat.choose 5 0 = 1 from by decide] at hEq
      omega
    · exact h2
    · rw [h4, show Nat.choose 5 4 = 5 from by decide] at hEq
      omega
  · rw [hw4] at hEq ⊢
    rw [ffOutFF6PStarTypes_C4] at hEq
    rcases hcases with h0 | h2 | h4
    · rw [h0, show Nat.choose 5 0 = 1 from by decide] at hEq
      omega
    · rw [h2, show Nat.choose 5 2 = 10 from by decide] at hEq
      omega
    · exact h4

theorem ff6p_star_types (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) (fr : PFrame Q (Option (Fin 5)) ffC)
    (ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ))
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr)
      (Subgroup.normalizer
        ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) ⊤) :
    (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 2 →
        ∃ J : Finset (Fin 5), J.card = 2 ∧
          (ψ v : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J))) ∧
      (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 4 →
        ∃ J : Finset (Fin 5), J.card = 4 ∧
          (ψ v : ProjOrth Q) = toProj Q (fr.signChange (ffOpt J))) := by
  constructor
  · intro v hv hw
    obtain ⟨J, hJe, hJv⟩ := (mem_ffB1p_iff hQ fr).mp ((hψ.2.2.1 (ψ v)).mpr ⟨v, hv, rfl⟩)
    refine ⟨J, ?_, hJv⟩
    rw [ffOutFF6PStarTypes_card hQ hdim hsgn fr hψ hv (Or.inl hw) hJe hJv, hw]
  · intro v hv hw
    obtain ⟨J, hJe, hJv⟩ := (mem_ffB1p_iff hQ fr).mp ((hψ.2.2.1 (ψ v)).mpr ⟨v, hv, rfl⟩)
    refine ⟨J, ?_, hJv⟩
    rw [ffOutFF6PStarTypes_card hQ hdim hsgn fr hψ hv (Or.inr hw) hJe hJv, hw]

theorem ff6p_star_types_hasType (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = 1)
    (fr : PFrame Q (Option (Fin 5)) ffC) (ψ : (Fin 5 → ZMod 2) → ↥(omegaProj hQ))
    (hψ : IsPermModuleVia IsEvenVec ψ (ffB1p hQ fr)
      (Subgroup.normalizer
        ((ffB1p hQ fr : Subgroup ↥(omegaProj hQ)) : Set ↥(omegaProj hQ))) ⊤) :
    (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 2 →
        SimHasType (ffOmegaToSim hQ (ψ v)) 2 (-1)) ∧
      (∀ v : Fin 5 → ZMod 2, IsEvenVec v → vecWeight v = 4 →
        SimHasType (ffOmegaToSim hQ (ψ v)) 4 1) := by
  have htypes := ff6p_star_types hQ hdim hsgn fr ψ hψ
  constructor
  · intro v hv hw
    obtain ⟨J, hJ2, hJv⟩ := htypes.1 v hv hw
    have hne0 : ffOpt J ≠ ∅ := by
      intro h
      have hJ0 : J = ∅ := ffOpt_injective (by rw [h, ffOpt, Finset.map_empty])
      rw [hJ0, Finset.card_empty] at hJ2
      omega
    have hneu : ffOpt J ≠ Finset.univ := by
      intro h
      have hcard : (ffOpt J).card = 6 := by rw [h]; decide
      rw [ffOpt_card] at hcard
      have hle : J.card ≤ 5 := by simpa using Finset.card_le_univ J
      omega
    have hs := ff6p_simHasType_signChange hQ fr (K := ffOpt J) hne0 hneu
    have hcardK : (ffOpt J).card = 2 := by rw [ffOpt_card]; exact hJ2
    have hif : (if none ∈ ffOpt J then (-1 : ℤˣ) else 1) = 1 := if_neg (none_notMem_ffOpt J)
    rw [hcardK, hif, show (-1 : ℤˣ) ^ (2 / 2) = -1 from by decide, one_mul] at hs
    rw [ffOmegaToSim_apply, hJv]
    exact hs
  · intro v hv hw
    obtain ⟨J, hJ4, hJv⟩ := htypes.2 v hv hw
    have hne0 : ffOpt J ≠ ∅ := by
      intro h
      have hJ0 : J = ∅ := ffOpt_injective (by rw [h, ffOpt, Finset.map_empty])
      rw [hJ0, Finset.card_empty] at hJ4
      omega
    have hneu : ffOpt J ≠ Finset.univ := by
      intro h
      have hcard : (ffOpt J).card = 6 := by rw [h]; decide
      rw [ffOpt_card] at hcard
      have hle : J.card ≤ 5 := by simpa using Finset.card_le_univ J
      omega
    have hs := ff6p_simHasType_signChange hQ fr (K := ffOpt J) hne0 hneu
    have hcardK : (ffOpt J).card = 4 := by rw [ffOpt_card]; exact hJ4
    have hif : (if none ∈ ffOpt J then (-1 : ℤˣ) else 1) = 1 := if_neg (none_notMem_ffOpt J)
    rw [hcardK, hif, show (-1 : ℤˣ) ^ (4 / 2) = 1 from by decide, one_mul] at hs
    rw [ffOmegaToSim_apply, hJv]
    exact hs

end CFSG.OddStandard.SmallF3.Omega
