module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelEmbed
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longRootSp2 longRootSp2_eq_suppGroup
  mem_suppGroup coords mem_coords longBlock longBlock_injective)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section PSL

variable {m : ℕ} {F : Type} [Field F] [Finite F]

theorem perfectCore_centralizer_map_proj_eq (hF : 4 ≤ Nat.card F) {I : Finset (Fin m)}
    (hI : I.card = 2) (D : Subgroup (SpecialLinearGroup (Fin m) F))
    (hdiag : ∀ d ∈ D, ∀ i j, i ≠ j → (d : Matrix (Fin m) (Fin m) F) i j = 0)
    (hconst : ∀ d ∈ D, ∀ i ∈ I, ∀ j ∈ I,
      (d : Matrix (Fin m) (Fin m) F) i i = (d : Matrix (Fin m) (Fin m) F) j j)
    (hsep : ∀ i j, i ≠ j → (i ∉ I ∨ j ∉ I) →
      ∃ d ∈ D, (d : Matrix (Fin m) (Fin m) F) i i ≠ (d : Matrix (Fin m) (Fin m) F) j j) :
    perfectCore (centralizer ((D.map (proj m F) : Subgroup (projectiveSL m F)) :
      Set (projectiveSL m F))) = (blockSpecialLinear (K := F) I).map (proj m F) := by
  classical
  set T : Subgroup (projectiveSL m F) := D.map (proj m F) with hT
  have hlift : ∀ d : T, ∃ x ∈ D, proj m F x = (d : projectiveSL m F) :=
    fun d => Subgroup.mem_map.1 d.2
  choose ℓ hℓD hℓ using hlift
  set α : T → MulAut (SpecialLinearGroup (Fin m) F) := fun d => MulAut.conj (ℓ d) with hα
  have hαp : ∀ (d : T) (x : SpecialLinearGroup (Fin m) F),
      proj m F (α d x) = (d : projectiveSL m F) * proj m F x * (d : projectiveSL m F)⁻¹ := by
    intro d x
    simp only [hα, MulAut.conj_apply, map_mul, map_inv, hℓ]
  have hker : (proj m F).ker ≤ center (SpecialLinearGroup (Fin m) F) := by
    rw [ker_proj]
    exact scalars_le_center m F
  have h := LinearPilot.perfectCore_range_inf_centralizer (proj m F) hker α hαp
  rw [MonoidHom.range_eq_top.2 (proj_surjective m F), top_inf_eq] at h
  rw [h]
  congr 1
  have hfix : LinearPilot.fixAll α =
      blockSpecialLinear (K := F) Finset.univ ⊓ centralizer (Set.range ℓ) := by
    ext x
    simp only [LinearPilot.mem_fixAll, mem_inf, mem_centralizer_iff, Set.mem_range,
      forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · intro hx
      refine ⟨fun i j hij => by simp at hij, fun d => ?_⟩
      have h1 := hx d
      simp only [hα, MulAut.conj_apply] at h1
      calc ℓ d * x = ℓ d * x * (ℓ d)⁻¹ * ℓ d := by group
        _ = x * ℓ d := by rw [h1]
    · rintro ⟨-, hx⟩ d
      simp only [hα, MulAut.conj_apply]
      rw [hx d, mul_inv_cancel_right]
  rw [hfix]
  refine LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear (Finset.subset_univ I) _
    ?_ ?_ ?_ (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by omega) hF)
  · rintro _ ⟨d, rfl⟩
    exact hdiag _ (hℓD d)
  · rintro _ ⟨d, rfl⟩
    exact hconst _ (hℓD d)
  · intro i _ j _ hij hIJ
    obtain ⟨d₀, hd₀, hne⟩ := hsep i j hij hIJ
    set d : T := ⟨proj m F d₀, mem_map_of_mem _ hd₀⟩ with hd
    refine ⟨ℓ d, ⟨d, rfl⟩, ?_⟩
    have heq : proj m F d₀ = proj m F (ℓ d) := (hℓ d).symm
    obtain ⟨c, -, hc⟩ := proj_eq_proj_iff.1 heq
    have hmat : ((ℓ d : SpecialLinearGroup (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        (d₀ : Matrix (Fin m) (Fin m) F) * scalar (Fin m) (c : F) := by
      rw [← hc, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mul]
    rw [hmat, scalar_apply, mul_diagonal, mul_diagonal]
    intro h2
    exact hne (mul_right_cancel₀ c.ne_zero h2)

end PSL

section LongRoot

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

@[expose] def spModelPlane (n : ℕ) (k : Fin n) : Finset (Fin (2 * n)) :=
  {spModelIdx n (Sum.inl k), spModelIdx n (Sum.inr k)}

theorem mem_spModelPlane {k : Fin n} {a : Fin (2 * n)} :
    a ∈ spModelPlane n k ↔ (spModelIdx n).symm a ∈ coords k := by
  rw [spModelPlane, Finset.mem_insert, Finset.mem_singleton, mem_coords, Equiv.symm_apply_eq,
    Equiv.symm_apply_eq]

theorem card_spModelPlane (k : Fin n) : (spModelPlane n k).card = 2 := by
  rw [spModelPlane, Finset.card_pair]
  exact fun h => Sum.inl_ne_inr ((spModelIdx n).injective h)

theorem spModelSL_mem_blockSpecialLinear {k : Fin n} {x : StatedSp n F}
    (hx : x ∈ longRootSp2 F n k) :
    spModelSL n F x ∈ blockSpecialLinear (K := F) (spModelPlane n k) := by
  rw [longRootSp2_eq_suppGroup, mem_suppGroup] at hx
  rw [mem_blockSpecialLinear]
  intro a b hab
  rw [coe_spModelSL, submatrix_apply, ← mat_apply,
    hx _ _ (fun h => hab.elim (fun ha => ha (mem_spModelPlane.2 h.1))
      (fun hb => hb (mem_spModelPlane.2 h.2))), one_apply, one_apply]
  by_cases h : a = b
  · simp [h]
  · simp [h]

theorem map_spModelPSL_longRootSp2 [Finite F] (hn : 1 ≤ n) (k : Fin n) :
    (longRootSp2 F n k).map (spModelPSL n F) =
      (blockSpecialLinear (K := F) (spModelPlane n k)).map (proj (2 * n) F) := by
  have hle : (longRootSp2 F n k).map (spModelPSL n F) ≤
      (blockSpecialLinear (K := F) (spModelPlane n k)).map (proj (2 * n) F) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨_, spModelSL_mem_blockSpecialLinear hx, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card ((blockSpecialLinear (K := F) (spModelPlane n k)).map (proj (2 * n) F)) ≤
      Nat.card (blockSpecialLinear (K := F) (spModelPlane n k)) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
  have h2 : Nat.card (blockSpecialLinear (K := F) (spModelPlane n k)) =
      Nat.card (longRootSp2 F n k) := by
    rw [← Nat.card_congr (LinearPilot.blockSpecialLinearEquivOfCardTwo (K := F)
      (card_spModelPlane k)).toEquiv, longRootSp2,
      ← Nat.card_congr (MonoidHom.ofInjective (longBlock_injective (K := F) (n := n) k)).toEquiv]
  rw [Subgroup.card_map_of_injective (spModelPSL_injective hn)]
  omega

end LongRoot

section LeviTorus

variable {n : ℕ} {F : Type} [Field F] [CharP F 2]

theorem coe_spModelSL_diagSp (t : Fin n → Fˣ) :
    ((spModelSL n F (diagSp F n t) : SpecialLinearGroup (Fin (2 * n)) F) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      diagonal (fun a => diagSpEntry t ((spModelIdx n).symm a)) := by
  rw [coe_spModelSL, ← mat_apply, mat_diagSp, submatrix_diagonal_equiv]
  rfl

omit [CharP F 2] in
theorem diagSpEntry_mulSingle (i : Fin n) (κ : Fˣ) (s : Fin n ⊕ Fin n) :
    diagSpEntry (Pi.mulSingle i κ) s =
      if s = Sum.inl i then (κ : F) else if s = Sum.inr i then ((κ⁻¹ : Fˣ) : F) else 1 := by
  rcases s with j | j
  · by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  · by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]

theorem units_ne_inv_of_ne_one_of_charTwo {κ : Fˣ} (hκ : κ ≠ 1) : (κ : F) ≠ ((κ⁻¹ : Fˣ) : F) := by
  intro h
  have h2 : (κ : F) * κ = 1 := by
    calc (κ : F) * κ = κ * ((κ⁻¹ : Fˣ) : F) := by rw [← h]
      _ = 1 := by simp
  apply hκ
  apply Units.ext
  have h3 : ((κ : F) - 1) ^ 2 = 0 := by
    linear_combination h2 + (1 - (κ : F)) * CharTwo.two_eq_zero (R := F)
  rw [Units.val_one]
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.mp h3)

theorem exists_diagSpEntry_mulSingle_ne {κ : Fˣ} (hκ : κ ≠ 1) {last : Fin n}
    (hlast : last.val + 1 = n) {s s' : Fin n ⊕ Fin n} (hss' : s ≠ s')
    (h : s ∉ coords last ∨ s' ∉ coords last) :
    ∃ i : Fin n, i.val + 1 < n ∧
      diagSpEntry (Pi.mulSingle i κ) s ≠ diagSpEntry (Pi.mulSingle i κ) s' := by
  have hκ1 : (κ : F) ≠ 1 := fun h1 => hκ (Units.ext h1)
  have hκi : ((κ⁻¹ : Fˣ) : F) ≠ 1 := fun h1 => hκ (inv_eq_one.1 (Units.ext h1))
  have hκκ := units_ne_inv_of_ne_one_of_charTwo hκ
  have key : ∀ {a b : Fin n ⊕ Fin n}, a ≠ b → a ∉ coords last →
      ∃ i : Fin n, i.val + 1 < n ∧
        diagSpEntry (Pi.mulSingle i κ) a ≠ diagSpEntry (Pi.mulSingle i κ) b := by
    intro a b hab ha
    rcases a with i | i
    · have hil : i ≠ last := fun e => ha (e ▸ mem_coords.2 (Or.inl rfl))
      have hi : i.val + 1 < n := by
        have := i.isLt
        have : i.val ≠ last.val := fun e => hil (Fin.ext e)
        omega
      refine ⟨i, hi, ?_⟩
      rw [diagSpEntry_mulSingle, diagSpEntry_mulSingle]
      rcases b with j | j
      · have hji : j ≠ i := fun e => hab (by rw [e])
        simp only [Sum.inl.injEq, hji, ↓reduceIte, reduceCtorEq]
        exact hκ1
      · by_cases hji : j = i
        · subst hji
          simp only [reduceCtorEq, ↓reduceIte]
          exact hκκ
        · simp only [reduceCtorEq, Sum.inr.injEq, hji, ↓reduceIte]
          exact hκ1
    · have hil : i ≠ last := fun e => ha (e ▸ mem_coords.2 (Or.inr rfl))
      have hi : i.val + 1 < n := by
        have := i.isLt
        have : i.val ≠ last.val := fun e => hil (Fin.ext e)
        omega
      refine ⟨i, hi, ?_⟩
      rw [diagSpEntry_mulSingle, diagSpEntry_mulSingle]
      rcases b with j | j
      · by_cases hji : j = i
        · subst hji
          simp only [reduceCtorEq, ↓reduceIte]
          exact hκκ.symm
        · simp only [Sum.inl.injEq, hji, ↓reduceIte, reduceCtorEq]
          exact hκi
      · have hji : j ≠ i := fun e => hab (by rw [e])
        simp only [reduceCtorEq, Sum.inr.injEq, hji, ↓reduceIte]
        exact hκi
  rcases h with h | h
  · exact key hss' h
  · obtain ⟨i, hi, hne⟩ := key (Ne.symm hss') h
    exact ⟨i, hi, Ne.symm hne⟩

theorem perfectCore_centralizer_map_spModelPSL [Finite F] (hF : 4 ≤ Nat.card F) (hn : 1 ≤ n)
    {last : Fin n} (hlast : last.val + 1 = n) (T : Subgroup (StatedSp n F))
    (hT : T ≤ leviTorusSp F {last}) {κ : Fˣ} (hκ : κ ≠ 1)
    (hTκ : ∀ i : Fin n, i.val + 1 < n → diagSp F n (Pi.mulSingle i κ) ∈ T) :
    perfectCore (centralizer ((T.map (spModelPSL n F) : Subgroup (projectiveSL (2 * n) F)) :
      Set (projectiveSL (2 * n) F))) = (longRootSp2 F n last).map (spModelPSL n F) := by
  have hmap : T.map (spModelPSL n F) = (T.map (spModelSL n F)).map (proj (2 * n) F) :=
    (Subgroup.map_map _ _ _).symm
  rw [map_spModelPSL_longRootSp2 hn last, hmap]
  refine perfectCore_centralizer_map_proj_eq hF (card_spModelPlane last) _ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ a b hab
    obtain ⟨t, -, rfl⟩ := hT hx
    rw [coe_spModelSL_diagSp, diagonal_apply_ne _ hab]
  · rintro _ ⟨x, hx, rfl⟩ a ha b hb
    obtain ⟨t, ht, rfl⟩ := hT hx
    have htl : t last = 1 := (ht last (Finset.mem_singleton_self _)).2 hlast
    have hval : ∀ s ∈ coords last, diagSpEntry t s = 1 := by
      intro s hs
      rcases mem_coords.1 hs with rfl | rfl <;> simp [htl]
    rw [coe_spModelSL_diagSp, diagonal_apply_eq, diagonal_apply_eq,
      hval _ (mem_spModelPlane.1 ha), hval _ (mem_spModelPlane.1 hb)]
  · intro a b hab hI
    obtain ⟨i, hi, hne⟩ := exists_diagSpEntry_mulSingle_ne hκ hlast
      ((spModelIdx n).symm.injective.ne hab)
      (hI.imp (fun h h' => h (mem_spModelPlane.2 h')) (fun h h' => h (mem_spModelPlane.2 h')))
    refine ⟨_, ⟨_, hTκ i hi, rfl⟩, ?_⟩
    rw [coe_spModelSL_diagSp, diagonal_apply_eq, diagonal_apply_eq]
    exact hne

end LeviTorus

end CFSG.SeitzReduction.SymplecticPilot
