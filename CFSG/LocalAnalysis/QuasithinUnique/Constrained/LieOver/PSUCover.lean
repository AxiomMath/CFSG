module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.PSU
public import CFSG.Quasithin.H13.U4ParRecog

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (IsLinePerm epsAct)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (rootVec posRoots negRoots

  mem_negRoots simpleRefl simpleRefl_mem simpleRefl_mul_self simpleRootVec
  simpleRootVec_mem_posRoots epsAct_neg epsAct_epsAct_inv IsSpReducedWord signed_descents
  exists_word_length_eq spLength_eq_invCount rootVec_mem_posRoots_iff)
open Matrix
open scoped Pointwise

@[expose] def PSUTorusOvergroup : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (r ε : ℕ), 2 ≤ r → ε ≤ 1 →
    ∀ (c : K) (hc : c ∈ h.traceZero), c ≠ 0 → ∀ A : Subgroup (hypSU h r ε),
      hypUnitriangular h r ε ≤ A → (∀ k : Fin r, uWeylRep ε h k c hc ∈ A) → hypTorus h r ε ≤ A

section Helpers

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem lg_norm_ratio_inv (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (a : Fin r → Kˣ) :
    h.norm ((ratioHom h r a)⁻¹ : Kˣ) = 1 := by
  have hmem : ratioHom h r a ∈ (Units.map h.normHom).ker := by
    rw [← range_ratioHom hr]
    exact ⟨a, rfl⟩
  rw [UnitaryFieldData.mem_ker_normUnits] at hmem
  rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hmem, inv_one]

theorem lg_torusRatio_inv (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) :
    torusRatio h a (fun _ : Fin 1 => (ratioHom h r a)⁻¹) = 1 := by
  rw [torusRatio, ← coe_ratioHom, Fin.prod_univ_one, ← Units.val_mul, mul_inv_cancel,
    Units.val_one]

theorem lg_diag_torus (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {b : hypSU h r ε} (hb : b ∈ hypBorel h r ε) :
    ∃ (a : Fin r → Kˣ) (d : Fin ε → Kˣ), (∀ k, h.norm (d k : K) = 1) ∧
      torusRatio h a d = 1 ∧
      ∀ i : Fin r, (a i : K) =
        ((b : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) (.inl i) (.inl i) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · have hmem : hypDiagHom h r 0 hε ⟨b, hb⟩ ∈ evenDiagGroup h r := by
      rw [← range_hypDiagHom_even]
      exact ⟨⟨b, hb⟩, rfl⟩
    rw [mem_evenDiagGroup] at hmem
    have hratio : torusRatio h (hypDiagHom h r 0 hε ⟨b, hb⟩) (fun k : Fin 0 => isEmptyElim k) =
        1 := by
      simp only [torusRatio, Fin.prod_univ_zero, mul_one]
      exact hmem
    exact ⟨_, fun k : Fin 0 => isEmptyElim k, fun k => isEmptyElim k, hratio,
      fun i => coe_hypDiagHom hε ⟨b, hb⟩ i⟩
  · exact ⟨hypDiagHom h r 1 hε ⟨b, hb⟩, fun _ : Fin 1 => (ratioHom h r (hypDiagHom h r 1 hε
        ⟨b, hb⟩))⁻¹, fun _ => lg_norm_ratio_inv h hr (hypDiagHom h r 1 hε ⟨b, hb⟩),
      lg_torusRatio_inv h (hypDiagHom h r 1 hε ⟨b, hb⟩), fun i => coe_hypDiagHom hε ⟨b, hb⟩ i⟩

theorem lg_borel_eq_torus_mul (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {b : hypSU h r ε} (hb : b ∈ hypBorel h r ε) :
    ∃ t ∈ hypTorus h r ε, ∃ u ∈ hypUnitriangular h r ε, b = t * u := by
  obtain ⟨a, d, hd, hp, hdiag⟩ := lg_diag_torus h hr hε hb
  obtain ⟨t, ht, htmat⟩ := torusMat_mem_hypSU h a hd hp
  have htB : t ∈ hypBorel h r ε := hypTorus_le_hypBorel h ht
  have hEq : hypDiagHom h r ε hε ⟨t, htB⟩ = hypDiagHom h r ε hε ⟨b, hb⟩ := by
    funext i
    apply Units.ext
    rw [coe_hypDiagHom, coe_hypDiagHom]
    dsimp only
    rw [htmat, diagonal_apply_eq]
    exact hdiag i
  have hker : (⟨t, htB⟩ : hypBorel h r ε)⁻¹ * ⟨b, hb⟩ ∈ (hypDiagHom h r ε hε).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hEq, inv_mul_cancel]
  rw [ker_hypDiagHom hε, Subgroup.mem_subgroupOf] at hker
  exact ⟨t, ht, _, hker, (mul_inv_cancel_left t b).symm⟩

theorem lg_borel_eq_unip_mul_torus (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {b : hypSU h r ε} (hb : b ∈ hypBorel h r ε) :
    ∃ u ∈ hypUnitriangular h r ε, ∃ t ∈ hypTorus h r ε, b = u * t := by
  obtain ⟨t, ht, u, hu, heq⟩ := lg_borel_eq_torus_mul h hr hε (inv_mem hb)
  refine ⟨u⁻¹, inv_mem hu, t⁻¹, inv_mem ht, ?_⟩
  calc b = (b⁻¹)⁻¹ := (inv_inv b).symm
    _ = (t * u)⁻¹ := by rw [heq]
    _ = u⁻¹ * t⁻¹ := mul_inv_rev t u

theorem lg_uRootMat_apply_diag (h : UnitaryFieldData p f K) {a b : Fin r ⊕ Fin r} (hab : a ≠ b)
    (t : K) (x : HypIndex r ε) : uRootMat ε h a b t x x = 1 := by
  have h1 : ¬(lineCoord (ε := ε) a = x ∧ lineCoord (ε := ε) b = x) := fun hh =>
    hab (lineCoord_injective (hh.1.trans hh.2.symm))
  have h2 : ¬(lineCoord (ε := ε) b.swap = x ∧ lineCoord (ε := ε) a.swap = x) := fun hh => by
    have e : b.swap = a.swap := lineCoord_injective (hh.1.trans hh.2.symm)
    have e' := congrArg Sum.swap e
    rw [Sum.swap_swap, Sum.swap_swap] at e'
    exact hab e'.symm
  rw [uRootMat, Matrix.add_apply, one_apply_eq, uRootNil]
  split_ifs <;> simp [Matrix.single_apply, h1, h2]

theorem lg_uRootSubgroup_le_hypUnitriangular (h : UnitaryFieldData p f K) {α : Fin r → ℤ}
    (hα : α ∈ posRoots r) : uRootSubgroup ε h α ≤ hypUnitriangular h r ε := by
  refine iSup_le fun q => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := q
  rintro _ ⟨t, rfl⟩
  refine mem_hypUnitriangular.mpr ⟨?_, fun x => ?_⟩
  · change (uRootMat ε h a b t.toAdd).BlockTriangular fullPos
    exact uRootMat_blockTriangular h ((rootVec_mem_posRoots_iff hab).mp hα) _
  · change uRootMat ε h a b t.toAdd x x = 1
    exact lg_uRootMat_apply_diag h hab _ x

theorem lg_extract (h : UnitaryFieldData p f K) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    (A : Subgroup (hypSU h r ε)) (hU : hypUnitriangular h r ε ≤ A) :
    ∀ (l : List (Fin r)) (w : Equiv.Perm (Fin r ⊕ Fin r)), w ∈ hypWeyl r →
      ∀ z : hypSU h r ε, z ∈ A →
        IsLinePerm (weylPerm (ε := ε) w)
          ((z : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) →
        IsSpReducedWord w l → ∀ k ∈ l, uWeylRep ε h k c hc ∈ A := by
  intro l
  induction l with
  | nil =>
    intro _ _ _ _ _ _ k hk
    simp at hk
  | cons k l ih =>
    intro w hw z hzA hz hl k' hk'
    obtain ⟨hdesc, hred⟩ := (signed_descents hw).2.2 k l hl
    have hβ : -epsAct w⁻¹ (simpleRootVec r k) ∈ posRoots r := mem_negRoots.mp hdesc
    have hconj : (hypUnitriangular h r ε).map (MulAut.conj z).toMonoidHom ≤ A := by
      rintro _ ⟨u, hu, rfl⟩
      exact mul_mem (mul_mem hzA (hU hu)) (inv_mem hzA)
    have hneg : uRootSubgroup ε h (-simpleRootVec r k) ≤ A := by
      have h1 := map_conj_uRootSubgroup hw z hz (-epsAct w⁻¹ (simpleRootVec r k))
      rw [epsAct_neg, epsAct_epsAct_inv hw] at h1
      rw [← h1]
      exact (Subgroup.map_mono (lg_uRootSubgroup_le_hypUnitriangular h hβ)).trans hconj
    have hpos : uRootSubgroup ε h (simpleRootVec r k) ≤ A :=
      (lg_uRootSubgroup_le_hypUnitriangular h (simpleRootVec_mem_posRoots k)).trans hU
    have hnk : uWeylRep ε h k c hc ∈ A := uWeylRep_mem_of_le k hc hpos hneg
    have hzA' : (uWeylRep ε h k c hc)⁻¹ * z ∈ A := mul_mem (inv_mem hnk) hzA
    have hsinv : (weylPerm (ε := ε) (simpleRefl r k))⁻¹ = weylPerm (simpleRefl r k) :=
      inv_eq_of_mul_eq_one_left (by rw [← weylPerm_mul, simpleRefl_mul_self, weylPerm_one])
    have hmono : IsLinePerm (weylPerm (ε := ε) (simpleRefl r k * w))
        ((((uWeylRep ε h k c hc)⁻¹ * z : hypSU h r ε) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) := by
      have := (isLinePerm_uWeylRep hc hc0 k).inv.mul hz
      rw [hsinv, ← weylPerm_mul] at this
      rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
      exact this
    rcases List.mem_cons.mp hk' with rfl | hk''
    · exact hnk
    · exact ih _ (mul_mem (simpleRefl_mem k) hw) _ hzA' hmono hred k' hk''

theorem lg_le_flagStabilizer_cuts (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε))
    (hU : hypUnitriangular h r ε ≤ A) :
    A ≤ flagStabilizer h r ε (overgroupCuts ε h c hc A) := by
  set I := overgroupCuts ε h c hc A with hIdef
  have hI : I ⊆ Set.Icc 1 r := overgroupCuts_subset h hc A
  have hBF : hypBorel h r ε ≤ flagStabilizer h r ε I := hypBorel_le_flagStabilizer hI
  have hsub : {g : hypSU h r ε | ∃ k : Fin r, (k : ℕ) + 1 ∉ I ∧ uWeylRep ε h k c hc = g} ⊆
      flagStabilizer h r ε I := by
    rintro _ ⟨k, hk, rfl⟩
    exact (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hI k).mpr hk
  intro g hg
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_mem_uBruhatCell h hε hc hc0 g
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := lg_borel_eq_unip_mul_torus h hr hε hb₁
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := lg_borel_eq_torus_mul h hr hε hb₂
  have hwd : IsLinePerm (weylPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r)))
      (((weylElt h hc hc0 w.2 : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [coe_weylElt]
    exact isLinePerm_weylMat h hc0 _
  have hzA : t₁ * weylElt h hc hc0 w.2 * t₂ ∈ A := by
    have hm := mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (inv_mem (hU hu₂))
    have e : u₁⁻¹ * (u₁ * t₁ * weylElt h hc hc0 w.2 * (t₂ * u₂)) * u₂⁻¹ =
        t₁ * weylElt h hc hc0 w.2 * t₂ := by group
    rw [e] at hm
    exact hm
  have hz : IsLinePerm (weylPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r)))
      (((t₁ * weylElt h hc hc0 w.2 * t₂ : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    have h1 := ((isLinePerm_torus ht₁).mul hwd).mul (isLinePerm_torus ht₂)
    rw [weylPerm_one, one_mul, mul_one] at h1
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact h1
  obtain ⟨l, hl, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
  have hred : IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l :=
    ⟨hprod, by rw [hl, spLength_eq_invCount w.2]⟩
  have hPperm : IsLinePerm (weylPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r)))
      (((uWordProd ε h c hc l : hypSU h r ε) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) := by
    rw [← hprod]
    exact isLinePerm_uWordProd hc hc0 l
  have hall : ∀ k ∈ l, uWeylRep ε h k c hc ∈ A :=
    lg_extract h hc hc0 A hU l _ w.2 _ hzA hz hred
  have hl' : ∀ k ∈ l, (k : ℕ) + 1 ∉ I := fun k hk h' =>
    ((add_one_mem_overgroupCuts_iff h hc A k).mp h') (hall k hk)
  have hPmem : uWordProd ε h c hc l ∈ flagStabilizer h r ε I :=
    (Subgroup.closure_le (flagStabilizer h r ε I)).mpr hsub (uWordProd_mem_closure hc hl')
  obtain ⟨tP, htP, hP⟩ := exists_torus_of_isLinePerm hc hc0 w.2 hPperm
  obtain ⟨tz, htz, hzeq⟩ := exists_torus_of_isLinePerm hc hc0 w.2 hz
  have hzI : t₁ * weylElt h hc hc0 w.2 * t₂ ∈ flagStabilizer h r ε I := by
    have e : t₁ * weylElt h hc hc0 w.2 * t₂ = uWordProd ε h c hc l * (tP⁻¹ * tz) := by
      rw [hP, hzeq]
      group
    rw [e]
    exact mul_mem hPmem (hBF (hypTorus_le_hypBorel h (mul_mem (inv_mem htP) htz)))
  have e2 : u₁ * t₁ * weylElt h hc hc0 w.2 * (t₂ * u₂) =
      u₁ * (t₁ * weylElt h hc hc0 w.2 * t₂) * u₂ := by group
  rw [e2]
  exact mul_mem (mul_mem (hBF (hypUnitriangular_le_hypBorel h hu₁)) hzI)
    (hBF (hypUnitriangular_le_hypBorel h hu₂))

theorem lg_eq_top_of_torus (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (A : Subgroup (hypSU h r ε))
    (hU : hypUnitriangular h r ε ≤ A) (hT : hypTorus h r ε ≤ A)
    (hn : ∀ k : Fin r, uWeylRep ε h k c hc ∈ A) : A = ⊤ := by
  have hB : hypBorel h r ε ≤ A := by
    intro b hb
    obtain ⟨t, ht, u, hu, rfl⟩ := lg_borel_eq_torus_mul h hr hε hb
    exact mul_mem (hT ht) (hU hu)
  have hgen := (unitary_subflag_generation h hr hε hc hc0
    (Set.empty_subset (Set.Icc 1 r))).1
  rw [flagStabilizer_empty] at hgen
  rw [eq_top_iff, hgen]
  refine sup_le hB ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨k, -, rfl⟩
  exact hn k

end Helpers

theorem psuCover_all_of_torus (hT : PSUTorusOvergroup) (f : ℕ) (K : Type) [Field K]
    (h : UnitaryFieldData 2 f K) (r ε : ℕ) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (A : Subgroup (hypPSU h r ε)) (hA : A ≠ ⊤) (hU : hypProjUnitriangular h r ε ≤ A) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ r ∧ A ≤ projIsoStabilizer h r ε (hypFlag h r ε d) := by
  obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
  have hUM : hypUnitriangular h r ε ≤ A.comap (hypProj h r ε) := by
    intro u hu
    exact hU (Subgroup.mem_map_of_mem (hypProj h r ε) hu)
  have hMtop : A.comap (hypProj h r ε) ≠ ⊤ := by
    intro hMt
    apply hA
    rw [eq_top_iff]
    intro p _
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε p
    have hg : g ∈ A.comap (hypProj h r ε) := hMt ▸ Subgroup.mem_top g
    exact hg
  have hne : overgroupCuts ε h c hc (A.comap (hypProj h r ε)) ≠ ∅ := by
    intro he
    have hn : ∀ k : Fin r, uWeylRep ε h k c hc ∈ A.comap (hypProj h r ε) := by
      intro k
      by_contra hnot
      have hmem := (add_one_mem_overgroupCuts_iff h hc _ k).mpr hnot
      rw [he] at hmem
      simp at hmem
    exact hMtop (lg_eq_top_of_torus h (by omega) hε hc hc0 _ hUM
      (hT f K h r ε hr hε c hc hc0 _ hUM hn) hn)
  obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨hi1, hi2⟩ := overgroupCuts_subset h hc _ hi
  refine ⟨i, hi1, hi2, ?_⟩
  intro p hp
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε p
  have hgM : g ∈ A.comap (hypProj h r ε) := hp
  have hg := mem_flagStabilizer.mp
    (lg_le_flagStabilizer_cuts h (by omega) hε hc hc0 _ hUM hgM) i hi
  exact Subgroup.mem_map_of_mem (hypProj h r ε) (mem_isoStabilizer.mpr hg)

theorem psuCover_of_torus (hT : PSUTorusOvergroup) : PSUCover := by
  unfold PSUCover
  intro f K _ h r ε hr hε _ A hA hU
  exact psuCover_all_of_torus hT f K h r ε hr hε A hA hU

theorem psu42SylowFacts_of_torus (hT : PSUTorusOvergroup) : PSU42SylowFacts := by
  unfold PSU42SylowFacts
  intro K _ h
  have hsimp : IsSimpleGroup (hypPSU h 2 0) := by
    haveI := CFSG.Quasithin.H13.U4Par.isSimpleGroup_hypSU h
    exact (CFSG.Quasithin.H13.U4Par.hypSUEquivPSU h).symm.isSimpleGroup
  exact le_sylowFacts_generic h 2 0 (le_refl 2) (Nat.zero_le 1)
    (fun A hA hU => psuCover_all_of_torus hT 1 K h 2 0 (le_refl 2) (Nat.zero_le 1) A hA hU)
    (fun d hd hdn => psuFlagCharTwo_holds 1 K h 2 0 d (le_refl 2) (Nat.zero_le 1) hd hdn) hsimp

end CFSG.Quasithin.LieOver
