module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

theorem pairRootMat_apply_diag {a b : Fin r ⊕ Fin r} (hab : a ≠ b) (s : K) (x : Fin r ⊕ Fin r) :
    pairRootMat K a b s x x = 1 := by
  rw [pairRootMat, Matrix.add_apply, one_apply_eq, Matrix.smul_apply, rootNil]
  have h1 : ¬(a = x ∧ b = x) := fun h => hab (h.1.trans h.2.symm)
  have h2 : ¬(b.swap = x ∧ a.swap = x) := fun h =>
    hab (swap_injective' (h.1.trans h.2.symm)).symm
  split_ifs with h
  · simp [h1]
  · simp [h1, h2]

theorem rootSubgroup_le_unipotent {α : Fin r → ℤ} (hα : α ∈ posRoots r) :
    rootSubgroup K α ≤ unipotent r K := by
  refine iSup_le fun p => ?_
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := p
  rintro _ ⟨t, rfl⟩
  have hab' : (flagOrder r a : ℕ) < flagOrder r b := (rootVec_mem_posRoots_iff hab).mp hα
  rw [mem_unipotent_iff_isFlagUpper]
  exact ⟨isFlagUpper_pairRootMat hab' _, fun x => pairRootMat_apply_diag hab _ x⟩

theorem exists_unipotent_mul_torus {b : StatedSp r K} (hb : b ∈ borelSubgroup r K) :
    ∃ u ∈ unipotent r K, ∃ t ∈ torus r K, b = u * t := by
  set s : Fin r → Kˣ := diagHom r K ⟨b, hb⟩ with hs
  have hT : torusHom s ∈ borelSubgroup r K := torus_le_borelSubgroup ⟨s, rfl⟩
  have hdt : diagHom r K ⟨torusHom s, hT⟩ = s := by
    funext i
    apply Units.ext
    simp [diagHom, diagEntry, coe_torusHom]
  have hker : (⟨b * (torusHom s)⁻¹, (borelSubgroup r K).mul_mem hb
      ((borelSubgroup r K).inv_mem hT)⟩ : borelSubgroup r K) ∈ (diagHom r K).ker := by
    rw [MonoidHom.mem_ker]
    have : (⟨b * (torusHom s)⁻¹, (borelSubgroup r K).mul_mem hb ((borelSubgroup r K).inv_mem hT)⟩
        : borelSubgroup r K) = ⟨b, hb⟩ * ⟨torusHom s, hT⟩⁻¹ := rfl
    rw [this, map_mul, map_inv, hdt, ← hs, mul_inv_cancel]
  rw [ker_diagHom] at hker
  exact ⟨b * (torusHom s)⁻¹, hker, torusHom s, ⟨s, rfl⟩, (inv_mul_cancel_right b _).symm⟩

theorem weylRep_mem_of_monomial {A : Subgroup (StatedSp r K)} (hU : unipotent r K ≤ A)
    {w : signedPermGroup r} {z : StatedSp r K} (hzA : z ∈ A)
    (hz : IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) {k : Fin r}
    (hk : epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹ (simpleRootVec r k) ∈ negRoots r) :
    weylRep K k ∈ A ∧ (weylRep K k)⁻¹ * z ∈ A ∧
      IsLinePerm (simpleRefl r k * (w : Equiv.Perm (Fin r ⊕ Fin r)))
        ((((weylRep K k)⁻¹ * z : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have hw2 := w.2
  have hβ : -epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹ (simpleRootVec r k) ∈ posRoots r :=
    mem_negRoots.mp hk
  have hconj : (unipotent r K).map (MulAut.conj z).toMonoidHom ≤ A := by
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem hzA (hU hu)) (inv_mem hzA)
  have hneg : rootSubgroup K (-simpleRootVec r k) ≤ A := by
    have h1 := map_conj_rootSubgroup z hz (-epsAct (w : Equiv.Perm (Fin r ⊕ Fin r))⁻¹
      (simpleRootVec r k))
    rw [epsAct_neg, epsAct_epsAct_inv hw2] at h1
    rw [← h1]
    exact (Subgroup.map_mono (rootSubgroup_le_unipotent hβ)).trans hconj
  have hpos : rootSubgroup K (simpleRootVec r k) ≤ A :=
    (rootSubgroup_le_unipotent (simpleRootVec_mem_posRoots k)).trans hU
  have hnk : weylRep K k ∈ A := weylRep_mem_of_rootSubgroup_le k hpos hneg
  refine ⟨hnk, mul_mem (inv_mem hnk) hzA, ?_⟩
  have := (isLinePerm_weylRep (K := K) k).inv.mul hz
  rw [simpleRefl_inv] at this
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  exact this

theorem reduced_word_extraction_unipotent (A : Subgroup (StatedSp r K))
    (hU : unipotent r K ≤ A) :
    ∀ (l : List (Fin r)) (w : signedPermGroup r) (z : StatedSp r K), z ∈ A →
      IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
        ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l → ∀ k ∈ l, weylRep K k ∈ A := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ k hk; exact absurd hk List.not_mem_nil
  | cons k l ih =>
    intro w z hzA hz hl k' hk'
    obtain ⟨hdesc, hred⟩ := (signed_descents w.2).2.2 k l hl
    obtain ⟨hnk, hzA', hz'⟩ := weylRep_mem_of_monomial hU hzA hz hdesc
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hnk
    · exact ih ⟨simpleRefl r k * (w : Equiv.Perm (Fin r ⊕ Fin r)),
        mul_mem (simpleRefl_mem k) w.2⟩ _ hzA' hz' hred k' hk'

theorem le_flagStabilizer_borelCuts (M : Subgroup (StatedSp r K)) (hU : unipotent r K ≤ M) :
    M ≤ flagStabilizer r K (borelCuts K M) := by
  classical
  have hI : ∀ i ∈ borelCuts K M, i ≤ r := fun i hi => (borelCuts_le M i hi).2
  obtain ⟨-, hn, -⟩ := subflag_generation (K := K) (borelCuts K M) hI
  have hBQ := borelSubgroup_le_flagStabilizer (K := K) hI
  have hUI : ∀ u ∈ unipotent r K, u ∈ flagStabilizer r K (borelCuts K M) := fun u hu =>
    hBQ (unipotent_le_borelSubgroup hu)
  intro g hg
  obtain ⟨w, hw⟩ := (symplectic_bruhat (K := K)).1 g
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := exists_unipotent_mul_torus hb₁
  obtain ⟨u', hu', t', ht', hb₂'⟩ := exists_unipotent_mul_torus ((borelSubgroup r K).inv_mem hb₂)
  have hb₂eq : b₂ = t'⁻¹ * u'⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hb₂', inv_inv]
  set z : StatedSp r K := t₁ * dotW K w * t'⁻¹ with hz
  have hzM : z ∈ M := by
    have h1 : z = u₁⁻¹ * (u₁ * t₁ * dotW K w * b₂) * u' := by
      rw [hb₂eq, hz]; group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (hU hu')
  have hzmono : IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have h1 := ((isLinePerm_torusHom' ht₁).mul (isLinePerm_dotW (K := K) w)).mul
      (isLinePerm_torusHom' ht').inv
    rw [hz, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Subgroup.coe_inv]
    simpa using h1
  obtain ⟨l, hl, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
  have hred : IsSpReducedWord (w : Equiv.Perm (Fin r ⊕ Fin r)) l :=
    ⟨hprod, by rw [hl, spLength_eq_invCount w.2]⟩
  have hlA := reduced_word_extraction_unipotent M hU l w z hzM hzmono hred
  have hP : (l.map (weylRep K)).prod ∈ flagStabilizer r K (borelCuts K M) := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    refine (hn k).mpr fun hkI => ?_
    exact ((succ_mem_borelCuts_iff M k).mp hkI) (hlA k hk)
  have hlin := isLinePerm_prod_weylRep (K := K) l
  rw [hprod] at hlin
  obtain ⟨tρ, htρ, hρ⟩ := exists_torus_of_isLinePerm hlin
  obtain ⟨t₀, ht₀, hz0⟩ := exists_torus_of_isLinePerm hzmono
  have hzρ : z = (l.map (weylRep K)).prod * (tρ⁻¹ * t₀) := by
    rw [hz0, hρ]; group
  have hgz : u₁ * t₁ * dotW K w * b₂ = u₁ * z * u'⁻¹ := by
    rw [hb₂eq, hz]; group
  rw [hgz, hzρ]
  exact mul_mem (mul_mem (hUI _ hu₁) (mul_mem hP (hBQ (torus_le_borelSubgroup
    ((torus r K).mul_mem ((torus r K).inv_mem htρ) ht₀))))) (inv_mem (hUI _ hu'))

theorem transvection_zero_one (c : K) :
    (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) c :
      SpecialLinearGroup (Fin 2) K) = sl2Up K c := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Up]

theorem transvection_one_zero (c : K) :
    (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) c :
      SpecialLinearGroup (Fin 2) K) = sl2Low K c := by
  apply Subtype.ext
  rw [SpecialLinearGroup.transvection_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Low]

theorem eq_top_of_borelCuts_eq_empty (M : Subgroup (StatedSp r K)) (hU : unipotent r K ≤ M)
    (h : borelCuts K M = ∅) : M = ⊤ := by
  classical
  have hn : ∀ k : Fin r, weylRep K k ∈ M := by
    intro k
    by_contra hnot
    have : (k : ℕ) + 1 ∈ borelCuts K M := ⟨k, rfl, hnot⟩
    rw [h] at this
    exact this
  have hperm : ∀ w : signedPermGroup r, ∃ z ∈ M, IsLinePerm (w : Equiv.Perm (Fin r ⊕ Fin r))
      ((z : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    intro w
    obtain ⟨l, hl, hprod⟩ := exists_word_length_eq _ (w : Equiv.Perm (Fin r ⊕ Fin r)) w.2 rfl
    refine ⟨(l.map (weylRep K)).prod, ?_, ?_⟩
    · refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact hn k
    · have := isLinePerm_prod_weylRep (K := K) l
      rwa [hprod] at this
  have hpos : ∀ i : Fin r, rootVec (Sum.inl i : Fin r ⊕ Fin r) (Sum.inr i) ∈ posRoots r := by
    intro i
    rw [rootVec_mem_posRoots_iff Sum.inl_ne_inr, flagOrder_inl, flagOrder_inr]
    have := i.2
    omega
  have hup : ∀ (i : Fin r) (t : K), lam i (sl2Up K t) ∈ M := fun i t => by
    rw [← pairRootElt_long]
    exact hU (rootSubgroup_le_unipotent (hpos i) (pairRootElt_mem_rootSubgroup _ t))
  have hlow : ∀ (i : Fin r) (t : K), lam i (sl2Low K t) ∈ M := fun i t => by
    rw [← pairRootElt_long']
    obtain ⟨z, hzM, hz⟩ := hperm ⟨Equiv.swap (Sum.inl i) (Sum.inr i),
      swap_inl_inr_mem_signedPermGroup i⟩
    have hab : (Sum.inl i : Fin r ⊕ Fin r) ≠ Sum.inr i := Sum.inl_ne_inr
    have hmap := map_conj_range_pairRootHom z hz hab
    rw [range_pairRootHom_congr (a' := Sum.inr i) (b' := Sum.inl i)
      (Equiv.swap_apply_left _ _) (Equiv.swap_apply_right _ _) _ Sum.inr_ne_inl] at hmap
    have hmem : pairRootElt (Sum.inr_ne_inl : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inl i) t ∈
        (pairRootHom K (Sum.inr_ne_inl : (Sum.inr i : Fin r ⊕ Fin r) ≠ Sum.inl i)).range :=
      ⟨Multiplicative.ofAdd t, rfl⟩
    rw [← hmap] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyU : y ∈ unipotent r K :=
      rootSubgroup_le_unipotent (hpos i) (range_pairRootHom_le_rootSubgroup hab hy)
    rw [← hyeq]
    exact mul_mem (mul_mem hzM (hU hyU)) (inv_mem hzM)
  have hlam : ∀ (i : Fin r) (g : SpecialLinearGroup (Fin 2) K), lam i g ∈ M := by
    intro i g
    have hcomap : M.comap (lam i) = ⊤ := by
      rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := K),
        Subgroup.closure_le]
      rintro _ ⟨a, b, hab, c, rfl⟩
      fin_cases a <;> fin_cases b
      · exact absurd rfl hab
      · change lam i (SpecialLinearGroup.transvection _ c) ∈ M
        rw [transvection_zero_one]
        exact hup i c
      · change lam i (SpecialLinearGroup.transvection _ c) ∈ M
        rw [transvection_one_zero]
        exact hlow i c
      · exact absurd rfl hab
    have : g ∈ M.comap (lam i) := by rw [hcomap]; trivial
    exact this
  have hT : torus r K ≤ M := by
    rintro _ ⟨t, rfl⟩
    have ht : t ∈ M.comap (torusHom (r := r) (k := K)) := by
      rw [show t = ∏ i, Pi.mulSingle i (t i) from (Finset.univ_prod_mulSingle t).symm]
      exact Subgroup.prod_mem _ fun i _ => by
        show torusHom (Pi.mulSingle i (t i)) ∈ M
        rw [← lam_sl2Diag]
        exact hlam i _
    exact ht
  have hB : borelSubgroup r K ≤ M := fun b hb => by
    obtain ⟨u, hu, t, ht, rfl⟩ := exists_unipotent_mul_torus hb
    exact mul_mem (hU hu) (hT ht)
  have hgen := (subflag_generation (r := r) (K := K) (∅ : Set ℕ) (by simp)).1
  rw [flagStabilizer_empty] at hgen
  rw [eq_top_iff, hgen, Subgroup.closure_le]
  rintro g (hg | ⟨k, hk, rfl⟩)
  · exact hB hg
  · exact hn k

theorem symplectic_unitriangular_overgroup_subflag_containment :
    (∀ M : Subgroup (StatedSp r K), unipotent r K ≤ M →
      M ≤ flagStabilizer r K (borelCuts K M) ∧ (borelCuts K M = ∅ ↔ M = ⊤)) ∧
    ∀ A : Subgroup (StatedProj (StatedSp r K)), A ≠ ⊤ → projUnipotent r K ≤ A →
      ∃ i : ℕ, 1 ≤ i ∧ i ≤ r ∧ A ≤ projStabilizer r K (flag r K i) := by
  classical
  refine ⟨fun M hU => ⟨le_flagStabilizer_borelCuts M hU,
    ⟨eq_top_of_borelCuts_eq_empty M hU, fun hM => ?_⟩⟩, fun A hA hU => ?_⟩
  · refine Set.eq_empty_of_forall_notMem fun i hi => ?_
    obtain ⟨k, rfl, hnot⟩ := hi
    exact hnot (hM ▸ Subgroup.mem_top _)
  · set M := A.comap (proj r K) with hM
    have hUM : unipotent r K ≤ M := fun u hu => hU (Subgroup.mem_map_of_mem _ hu)
    have hMtop : M ≠ ⊤ := by
      intro hMt
      apply hA
      rw [eq_top_iff]
      intro p _
      obtain ⟨g, rfl⟩ := proj_surjective (r := r) (K := K) p
      have : g ∈ M := hMt ▸ Subgroup.mem_top g
      exact this
    have hne : borelCuts K M ≠ ∅ := fun he => hMtop (eq_top_of_borelCuts_eq_empty M hUM he)
    obtain ⟨i, hi⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨k, rfl, hnot⟩ := hi
    refine ⟨(k : ℕ) + 1, by omega, k.2, fun p hp => ?_⟩
    obtain ⟨g, rfl⟩ := proj_surjective (r := r) (K := K) p
    have hgM : g ∈ M := hp
    have hgQ := le_flagStabilizer_borelCuts M hUM hgM
    exact ⟨g, mem_flagStabilizer.mp hgQ _ ⟨k, rfl, hnot⟩, rfl⟩

end Symplectic

end CFSG.QuasithinUnique.Setup.X7a
