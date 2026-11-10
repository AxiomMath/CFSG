module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjPairAct
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjPairData
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.F4SylowGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.AdjPairLead

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg Module

@[expose] def adjFix (K : Type*) [Field K] (A : Subgroup ↥(adjointGroup .E6 K)) :
    Submodule K (RootModule .E6 K) where
  carrier := {v | ∀ a ∈ A, ((a : ModGL .E6 K) : Module.End K (RootModule .E6 K)) v = v}
  add_mem' := by
    intro v w hv hw a ha
    rw [map_add, hv a ha, hw a ha]
  zero_mem' := fun a _ => map_zero _
  smul_mem' := by
    intro c v hv a ha
    rw [map_smul, hv a ha]

section LevelE6

abbrev fE6 : (Fin Tag.E6.rank → ℤ) →+ ℤ := fWt Tag.E6.rank

theorem posS_finite : (posS fE6 : Set (Fin Tag.E6.rank → ℤ)).Finite :=
  isRoot_finite.subset fun _ h => h.1

theorem levelData_E6 {K : Type*} [Field K] :
    LevelData (rootSubgroup Tag.E6 K) (posS fE6) fE6 :=
  levelData_adj (Or.inr (Or.inl rfl)) posData_E6.inj

theorem mem_posS_iff {γ : Fin Tag.E6.rank → ℤ} :
    γ ∈ posS fE6 ↔ IsRoot .E6 γ ∧ 0 < ht γ :=
  ⟨fun h => ⟨h.1, (posData_E6.pos γ h.1).1 h.2⟩,
    fun h => ⟨h.1, (posData_E6.pos γ h.1).2 h.2⟩⟩

theorem fE6_ne_zero {μ : Fin Tag.E6.rank → ℤ} (hμ : IsRoot .E6 μ) : fE6 μ ≠ 0 := by
  have h1 : ∀ l ∈ Tag.E6.artifactRoots, horner l ≠ 0 := by decide +kernel
  have := h1 _ (isRoot_iff_mem_artifactRoots.1 hμ)
  rwa [horner_ofFn] at this

end LevelE6

section Abelian

theorem exists_mid_aux : ∀ g ∈ e6R, ∀ d ∈ e6R, List.zipWith (· + ·) g d ∈ Tag.E6.artifactRoots →
    ∃ m ∈ Tag.E6.artifactRoots, List.zipWith (· + ·) d m ∉ Tag.E6.artifactRoots ∧
      List.zipWith (· + ·) d m ≠ List.replicate 6 0 ∧
      List.zipWith (· + ·) g m ∈ Tag.E6.artifactRoots ∧
      List.zipWith (· + ·) d (List.zipWith (· + ·) g m) ∈ Tag.E6.artifactRoots := by
  decide +kernel

theorem exists_mid (γ δ : Fin Tag.E6.rank → ℤ) (hγ : γ ∈ posS fE6) (hδ : δ ∈ posS fE6)
    (h : IsRoot .E6 (γ + δ)) :
    ∃ μ : Fin Tag.E6.rank → ℤ, IsRoot .E6 μ ∧ ¬ IsRoot .E6 (δ + μ) ∧ δ + μ ≠ 0 ∧
      IsRoot .E6 (γ + μ) ∧ IsRoot .E6 (δ + (γ + μ)) := by
  have hg := posData_E6.mem γ |>.1 (mem_posS_iff.1 hγ)
  have hd := posData_E6.mem δ |>.1 (mem_posS_iff.1 hδ)
  have hs : List.zipWith (· + ·) (List.ofFn γ) (List.ofFn δ) ∈ Tag.E6.artifactRoots := by
    rw [zipWith_add_ofFn']; exact isRoot_iff_mem_artifactRoots.1 h
  obtain ⟨m, hm, h1, h2, h3, h4⟩ := exists_mid_aux _ hg _ hd hs
  have hlen : m.length = Tag.E6.rank := length_of_mem_artifactRoots hm
  refine ⟨toVec Tag.E6.rank m, ?_, ?_, ?_, ?_, ?_⟩
  · rw [isRoot_iff_mem_artifactRoots, ofFn_toVec hlen]; exact hm
  · rw [isRoot_iff_mem_artifactRoots, ← zipWith_add_ofFn', ofFn_toVec hlen]; exact h1
  · intro h0
    apply h2
    have := congrArg List.ofFn h0
    rw [← zipWith_add_ofFn', ofFn_toVec hlen] at this
    have hz : List.ofFn (0 : Fin Tag.E6.rank → ℤ) = List.replicate 6 0 := by decide
    exact this.trans hz
  · rw [isRoot_iff_mem_artifactRoots, ← zipWith_add_ofFn', ofFn_toVec hlen]; exact h3
  · rw [isRoot_iff_mem_artifactRoots, ← zipWith_add_ofFn', ← zipWith_add_ofFn', ofFn_toVec hlen]
    exact h4

end Abelian

section Abelian2

variable {K : Type*} [Field K] [CharP K 2] [Fintype (Label .E6)]

theorem isShiftL_pinnedE {τ : Tag} {f : (Fin τ.rank → ℤ) →+ ℤ} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) [Fintype (Label τ)] :
    IsShiftL (lblDeg f) (f α) (pinnedE τ K α) := by
  have := isShiftL_pinnedCoeff (K := K) (f := f) hα (k := 1) le_rfl
  rw [pinnedCoeff_one] at this
  simpa using this

theorem lblDeg_inr {τ : Tag} (f : (Fin τ.rank → ℤ) →+ ℤ) (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    lblDeg f (Sum.inr α : Label τ) = f α.1 := rfl

theorem lblDeg_inl {τ : Tag} (f : (Fin τ.rank → ℤ) →+ ℤ) (i : Fin τ.rank) :
    lblDeg f (Sum.inl i : Label τ) = 0 := by
  simp [lblDeg, Label.latticeWeight]

theorem leadSet_abelian {A₀ : Subgroup (Module.End K (RootModule .E6 K))ˣ}
    (hAc : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) {γ δ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ leadSet (X := rootSubgroup .E6 K) (lev := fE6) posS_finite A₀)
    (hδ : δ ∈ leadSet (X := rootSubgroup .E6 K) (lev := fE6) posS_finite A₀) :
    ¬ IsRoot .E6 (γ + δ) := by
  intro hr
  obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
  obtain ⟨hδP, -⟩ := mem_leadSet.1 hδ
  obtain ⟨a, haA, ha1, ha2⟩ := exists_of_mem_leadSet hγ
  obtain ⟨b, hbA, hb1, hb2⟩ := exists_of_mem_leadSet hδ
  obtain ⟨c, hc, na, hna, hspa⟩ := lead_split levelData_E6 hγP ha1 ha2
  obtain ⟨d, hd, nb, hnb, hspb⟩ := lead_split levelData_E6 hδP hb1 hb2
  have hfγ : 0 < fE6 γ := hγP.2
  have hfδ : 0 < fE6 δ := hδP.2
  obtain ⟨μ, hμ, hn1, hn2, hn3, hn4⟩ := exists_mid γ δ hγP hδP hr
  set Ea : Module.End K (RootModule .E6 K) := c • pinnedE .E6 K γ with hEa
  set Eb : Module.End K (RootModule .E6 K) := d • pinnedE .E6 K δ with hEb
  have hab : ((a : Module.End K (RootModule .E6 K)) * (b : Module.End K (RootModule .E6 K))) =
      (b : Module.End K (RootModule .E6 K)) * (a : Module.End K (RootModule .E6 K)) := by
    have := congrArg (fun u : (Module.End K (RootModule .E6 K))ˣ =>
      (u : Module.End K (RootModule .E6 K))) (hAc a haA b hbA)
    simpa only [Units.val_mul] using this
  have ea : (a : Module.End K (RootModule .E6 K)) = 1 + Ea + na := by
    calc (a : Module.End K (RootModule .E6 K)) = ((a : Module.End K (RootModule .E6 K)) - 1) + 1 := by
          abel
      _ = 1 + Ea + na := by rw [hspa, hEa]; abel
  have eb : (b : Module.End K (RootModule .E6 K)) = 1 + Eb + nb := by
    calc (b : Module.End K (RootModule .E6 K)) = ((b : Module.End K (RootModule .E6 K)) - 1) + 1 := by
          abel
      _ = 1 + Eb + nb := by rw [hspb, hEb]; abel
  have hmain : (Ea * Eb - Eb * Ea) + ((Ea * nb - nb * Ea) + (na * Eb - Eb * na) +
      (na * nb - nb * na)) = 0 := by
    have h := sub_eq_zero.2 hab
    rw [ea, eb] at h
    rw [← h]
    noncomm_ring
  have hEaS : IsShiftL (lblDeg fE6) (fE6 γ) Ea := (isShiftL_pinnedE hγP.1).smul c
  have hEbS : IsShiftL (lblDeg fE6) (fE6 δ) Eb := (isShiftL_pinnedE hδP.1).smul d
  set sh : ℤ := fE6 γ + fE6 δ + 1 with hsh
  have hrest : IsShiftL (lblDeg fE6) sh
      ((Ea * nb - nb * Ea) + (na * Eb - Eb * na) + (na * nb - nb * na)) := by
    have t1 := (hEaS.mul hnb).mono (t := sh) (by omega)
    have t2 := (hnb.mul hEaS).mono (t := sh) (by omega)
    have t3 := (hna.mul hEbS).mono (t := sh) (by omega)
    have t4 := (hEbS.mul hna).mono (t := sh) (by omega)
    have t5 := (hna.mul hnb).mono (t := sh) (by omega)
    have t6 := (hnb.mul hna).mono (t := sh) (by omega)
    exact ((t1.sub t2).add (t3.sub t4)).add (t5.sub t6)
  have hS : IsShiftL (lblDeg fE6) sh (Ea * Eb - Eb * Ea) := by
    rw [eq_neg_of_add_eq_zero_left hmain]
    exact hrest.neg
  obtain ⟨s, hs, hEγ⟩ := pinnedE_rootVec_of_add_root (K := K) γ μ hγP.1 hμ hn3
  obtain ⟨s2, hs2, hEδ⟩ := pinnedE_rootVec_of_add_root (K := K) δ (γ + μ) hδP.1
    hn3 hn4
  have hEδ0 := pinnedE_rootVec_of_not (K := K) δ μ hδP.1 hμ hn1 hn2
  have hval : (Ea * Eb - Eb * Ea) (rootVec .E6 K μ) =
      (-(c * d * s * s2)) • rootVec .E6 K (δ + (γ + μ)) := by
    simp only [hEa, hEb, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hEδ0,
      hEγ, map_smul, map_zero, smul_zero, hEδ, smul_smul]
    rw [zero_sub, ← neg_smul]
    congr 1
    ring
  have hbμ : rootVec .E6 K μ = Finsupp.single (Sum.inr ⟨μ, hμ⟩ : Label .E6) 1 :=
    rootVec_eq_single' hμ
  have hcoord : ((Ea * Eb - Eb * Ea) (Finsupp.single (Sum.inr ⟨μ, hμ⟩ : Label .E6) 1))
      (Sum.inr ⟨δ + (γ + μ), hn4⟩) ≠ 0 := by
    rw [← hbμ, hval, Finsupp.smul_apply, rootVec_eq_single' hn4, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hd) hs) hs2)
  have := hS _ _ hcoord
  rw [lblDeg_inr, lblDeg_inr, map_add, map_add] at this
  dsimp only at this
  omega

end Abelian2

section Labels

variable {ι : Type*} [Fintype ι] {k : Type*} [Field k]

open Classical in
@[expose] def leadLbl (F : ι → ℤ) (S : Submodule k (ι →₀ k)) : Finset ι :=
  Finset.univ.filter fun μ => ∃ v ∈ S, v μ ≠ 0 ∧ ∀ ν, v ν ≠ 0 → F μ ≤ F ν

theorem finrank_le_card_leadLbl (F : ι → ℤ) (S : Submodule k (ι →₀ k)) :
    Module.finrank k S ≤ (leadLbl F S).card := by
  classical
  let ψ : S →ₗ[k] (leadLbl F S → k) :=
    LinearMap.pi fun μ => (Finsupp.lapply (R := k) μ.1).comp S.subtype
  have hker0 : ∀ v : S, (∀ μ : leadLbl F S, (v : ι →₀ k) μ.1 = 0) → v = 0 := by
    intro v hv
    by_contra hne
    have hv' : (v : ι →₀ k) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨μ, hμ, hmin⟩ := Finset.exists_min_image (v : ι →₀ k).support F
      (Finsupp.support_nonempty_iff.2 hv')
    have hμ' : v.1 μ ≠ 0 := Finsupp.mem_support_iff.1 hμ
    have hmem : μ ∈ leadLbl F S := by
      simp only [leadLbl, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨v.1, v.2, hμ', fun ν hν => hmin ν (Finsupp.mem_support_iff.2 hν)⟩
    exact hμ' (hv ⟨μ, hmem⟩)
  have hinj : Function.Injective ψ := by
    intro v w hvw
    have h1 : ∀ μ : leadLbl F S, ((v : ι →₀ k) - w) μ.1 = 0 := fun μ => by
      have := congrFun hvw μ
      simp only [ψ, LinearMap.pi_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
        Submodule.subtype_apply] at this
      rw [Finsupp.sub_apply, this, sub_self]
    exact sub_eq_zero.1 (hker0 (v - w) h1)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this

end Labels

section Lead

variable {K : Type*} [Field K] [CharP K 2] [Fintype (Label .E6)]

theorem pinnedE_deg {τ : Tag} {f : (Fin τ.rank → ℤ) →+ ℤ} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (b j : Label τ) (h : pinnedE τ K α (Finsupp.single b 1) j ≠ 0) :
    lblDeg f j = lblDeg f b + f α := by
  have := pinnedCoeff_deg (f := f) (K := K) hα (k := 1) le_rfl b j (by rwa [pinnedCoeff_one])
  simpa using this

theorem pinnedE_lead_label {A₀ : Subgroup (Module.End K (RootModule .E6 K))ˣ}
    {γ : Fin Tag.E6.rank → ℤ}
    (hγ : γ ∈ leadSet (X := rootSubgroup .E6 K) (lev := fE6) posS_finite A₀)
    {v : RootModule .E6 K} (hv : ∀ a ∈ A₀, (a : Module.End K (RootModule .E6 K)) v = v)
    {μ : Fin Tag.E6.rank → ℤ} (hμ : IsRoot .E6 μ) (hμv : v (Sum.inr ⟨μ, hμ⟩) ≠ 0)
    (hmin : ∀ ν, v ν ≠ 0 → lblDeg fE6 (Sum.inr ⟨μ, hμ⟩ : Label .E6) ≤ lblDeg fE6 ν) :
    pinnedE .E6 K γ (rootVec .E6 K μ) = 0 := by
  obtain ⟨hγP, -⟩ := mem_leadSet.1 hγ
  obtain ⟨a, haA, ha1, ha2⟩ := exists_of_mem_leadSet hγ
  obtain ⟨c, hc, n, hn, hsp⟩ := lead_split levelData_E6 hγP ha1 ha2
  have hfγ : 0 < fE6 γ := hγP.2
  set E := pinnedE .E6 K γ with hE
  set bμ : Label .E6 := Sum.inr ⟨μ, hμ⟩ with hbμ
  have hzero : (c • E + n) v = 0 := by
    rw [← hsp, LinearMap.sub_apply, hv a haA]
    simp
  rw [rootVec_eq_single' hμ, ← hbμ]
  ext t
  rw [Finsupp.zero_apply]
  by_cases ht : lblDeg fE6 t = lblDeg fE6 bμ + fE6 γ
  · have h1 := congrArg (fun w => w t) hzero
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.zero_apply, smul_eq_mul] at h1
    have hnv : n v t = 0 := by
      rw [End_apply_coord n v t]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_contra hne
      have hvb : v b ≠ 0 := left_ne_zero_of_mul hne
      have hnb := right_ne_zero_of_mul hne
      have h2 := hn b t hnb
      have h3 := hmin b hvb
      omega
    have hEv : E v t = v bμ * E (Finsupp.single bμ 1) t := by
      rw [End_apply_coord E v t]
      refine Finset.sum_eq_single bμ (fun b _ hb => ?_) (fun h => absurd (Finset.mem_univ _) h)
      by_contra hne
      have hvb := left_ne_zero_of_mul hne
      have hEb := right_ne_zero_of_mul hne
      have hdeg : lblDeg fE6 t = lblDeg fE6 b + fE6 γ := pinnedE_deg hγP.1 b t hEb
      have hbdeg : lblDeg fE6 b = lblDeg fE6 bμ := by omega
      rcases b with i | β
      · rw [lblDeg_inl, hbμ, lblDeg_inr] at hbdeg
        exact fE6_ne_zero hμ hbdeg.symm
      · rw [hbμ, lblDeg_inr, lblDeg_inr] at hbdeg
        have := posData_E6.inj β.1 μ β.2 hμ hbdeg
        exact hb (by rw [hbμ]; exact congrArg Sum.inr (Subtype.ext this))
    rw [hnv, hEv, add_zero] at h1
    exact (mul_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hc)).resolve_left hμv
  · by_contra hne
    exact ht (pinnedE_deg hγP.1 bμ t hne)

end Lead

section Final

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def lblVec (b : Label .E6) : Fin Tag.E6.rank → ℤ :=
  Sum.elim (fun _ => 0) (fun α => α.1) b

theorem adj_pair_core (A : Subgroup ↥(adjointGroup .E6 K)) (hA : A ≠ ⊥)
    (hpos : ∀ a ∈ A, (a : ModGL .E6 K) ∈ CFSG.Blueprint.Chevalley.posUnipotent .E6 K)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ^ 2 * Nat.card ↥(adjFix K A) ≤ Nat.card K ^ 59 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (Label .E6) := Fintype.ofFinite _
  haveI : Finite (Module.End K (RootModule .E6 K)) := Module.finite_of_finite K
  let A₀ : Subgroup (Module.End K (RootModule .E6 K))ˣ := A.map (adjointGroup .E6 K).subtype
  have hA₀ : A₀ ≤ lvl (rootSubgroup .E6 K) (posS fE6) fE6 1 := by
    rintro _ ⟨a, ha, rfl⟩
    refine (?_ : CFSG.Blueprint.Chevalley.posUnipotent .E6 K ≤ _) (hpos a ha)
    unfold CFSG.Blueprint.Chevalley.posUnipotent rootSpan
    refine iSup₂_le fun α hα => le_lvl _ _ _ (mem_posS_iff.2 hα) ?_
    have := (mem_posS_iff.2 hα).2
    omega
  have hAc₀ : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm a ha b hb)
  set X := leadSet (X := rootSubgroup .E6 K) (lev := fE6) posS_finite A₀ with hX
  have hcardA : Nat.card A ≤ Nat.card K ^ X.card := by
    have h1 : Nat.card A = Nat.card A₀ :=
      Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv
    rw [h1]
    exact card_le_pow_leadSet levelData_E6 posS_finite Nat.card_pos
      (fun γ _ => (card_rootSubgroup γ).le) hA₀
  have hXne : X.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty, pow_zero] at hcardA
    exact hA ((Subgroup.card_le_one_iff_eq_bot A).1 hcardA)
  set Y := leadLbl (lblDeg fE6) (adjFix K A) with hY
  have hFcard : Nat.card ↥(adjFix K A) ≤ Nat.card K ^ Y.card := by
    rw [Module.natCard_eq_pow_finrank (K := K)]
    exact Nat.pow_le_pow_right Nat.card_pos (finrank_le_card_leadLbl _ _)
  set Yr : Finset (Fin Tag.E6.rank → ℤ) :=
    (Y.filter fun b => b.isRight = true).image lblVec with hYr
  have hYc : Y.card ≤ Yr.card + 6 := by
    rw [← Finset.card_filter_add_card_filter_not (s := Y) (fun b : Label .E6 => b.isRight = true)]
    refine Nat.add_le_add ?_ ?_
    · refine Finset.card_le_card_of_injOn lblVec (fun b hb => ?_) ?_
      · exact Finset.mem_image_of_mem _ hb
      · intro b hb b' hb' h
        obtain ⟨α, rfl⟩ := Sum.isRight_iff.1 (Finset.mem_filter.1 hb).2
        obtain ⟨α', rfl⟩ := Sum.isRight_iff.1 (Finset.mem_filter.1 hb').2
        exact congrArg Sum.inr (Subtype.ext h)
    · calc (Y.filter fun b => ¬ (b.isRight = true)).card
          ≤ ((Finset.univ : Finset (Fin Tag.E6.rank)).image Sum.inl).card := by
            refine Finset.card_le_card fun b hb => ?_
            obtain ⟨-, hb2⟩ := Finset.mem_filter.1 hb
            rcases b with i | α
            · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
            · exact absurd rfl hb2
        _ ≤ 6 := by
            refine (Finset.card_image_le).trans ?_
            rw [Finset.card_univ, Fintype.card_fin]
            decide
  have hXP : ∀ γ ∈ X, IsRoot .E6 γ ∧ 0 < ht γ := fun γ hγ =>
    mem_posS_iff.1 (mem_leadSet.1 hγ).1
  have hXX : ∀ γ ∈ X, ∀ δ ∈ X, ¬ IsRoot .E6 (γ + δ) := fun γ hγ δ hδ =>
    leadSet_abelian hAc₀ hγ hδ
  have hYW : ∀ μ ∈ Yr, IsRoot .E6 μ := by
    intro μ hμ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨α, rfl⟩ := Sum.isRight_iff.1 (Finset.mem_filter.1 hb).2
    exact α.2
  have hXY : ∀ γ ∈ X, ∀ μ ∈ Yr, ¬ IsRoot .E6 (γ + μ) ∧ γ + μ ≠ 0 := by
    intro γ hγ μ hμ
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hμ
    obtain ⟨hbY, hbα⟩ := Finset.mem_filter.1 hb
    obtain ⟨α, rfl⟩ := Sum.isRight_iff.1 hbα
    have hbY' := hbY
    simp only [hY, leadLbl, Finset.mem_filter, Finset.mem_univ, true_and] at hbY'
    obtain ⟨v, hvF, hvne, hmin⟩ := hbY'
    have hv : ∀ a ∈ A₀, (a : Module.End K (RootModule .E6 K)) v = v := by
      rintro _ ⟨a, ha, rfl⟩
      exact hvF a ha
    have hγr := (hXP γ hγ).1
    have hE0 := pinnedE_lead_label hγ hv α.2 hvne hmin
    have hlv : lblVec (Sum.inr α : Label .E6) = α.1 := rfl
    rw [hlv]
    refine ⟨fun hr => ?_, fun h0 => ?_⟩
    · obtain ⟨s, hs, hEs⟩ := pinnedE_rootVec_of_add_root (K := K) γ α.1 hγr α.2 hr
      rw [hE0] at hEs
      exact smul_ne_zero hs (rootVec_ne_zero hr) hEs.symm
    · exact pinnedE_rootVec_ne_zero_of_add_zero (K := K) γ α.1 hγr α.2 h0 hE0
  have hnum := e6_adj_numbers X Yr hXne hXP hXX hYW hXY
  calc Nat.card A ^ 2 * Nat.card ↥(adjFix K A)
      ≤ (Nat.card K ^ X.card) ^ 2 * Nat.card K ^ Y.card :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hcardA 2) hFcard
    _ = Nat.card K ^ (2 * X.card + Y.card) := by rw [← pow_mul, ← pow_add, mul_comm X.card 2]
    _ ≤ Nat.card K ^ 59 := Nat.pow_le_pow_right Nat.card_pos (by omega)

end Final

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem adjFix_conj (A : Subgroup ↥(adjointGroup .E6 K)) (g : ↥(adjointGroup .E6 K)) :
    Module.finrank K ↥(adjFix K (A.map (MulAut.conj g).toMonoidHom)) =
      Module.finrank K ↥(adjFix K A) := by
  let G : Module.End K (RootModule .E6 K) := ((g : ModGL .E6 K) : Module.End K (RootModule .E6 K))
  let Gi : Module.End K (RootModule .E6 K) :=
    (((g : ModGL .E6 K)⁻¹ : ModGL .E6 K) : Module.End K (RootModule .E6 K))
  have h1 : G * Gi = 1 := Units.mul_inv _
  have h2 : Gi * G = 1 := Units.inv_mul _
  let e : RootModule .E6 K ≃ₗ[K] RootModule .E6 K := LinearEquiv.ofLinearMap G Gi
    (LinearMap.ext fun v => by have := congrArg (fun m => m v) h1; simpa using this)
    (LinearMap.ext fun v => by have := congrArg (fun m => m v) h2; simpa using this)
  have key : ∀ a : ↥(adjointGroup .E6 K),
      ((((MulAut.conj g) a : ↥(adjointGroup .E6 K)) : ModGL .E6 K) :
        Module.End K (RootModule .E6 K)) =
        G * ((a : ModGL .E6 K) : Module.End K (RootModule .E6 K)) * Gi := by
    intro a
    have : (((MulAut.conj g) a : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (g : ModGL .E6 K) * (a : ModGL .E6 K) * (g : ModGL .E6 K)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [this, Units.val_mul, Units.val_mul]
  have hmap : (adjFix K A).map e.toLinearMap = adjFix K (A.map (MulAut.conj g).toMonoidHom) := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩ a' ⟨a, ha, rfl⟩
      have hw' := hw a ha
      show ((((MulAut.conj g) a : ↥(adjointGroup .E6 K)) : ModGL .E6 K) :
        Module.End K (RootModule .E6 K)) (G w) = G w
      rw [key a]
      calc (G * ((a : ModGL .E6 K) : Module.End K (RootModule .E6 K)) * Gi) (G w)
          = G (((a : ModGL .E6 K) : Module.End K (RootModule .E6 K)) ((Gi * G) w)) := by
            simp only [Module.End.mul_apply]
        _ = G w := by rw [h2, Module.End.one_apply]; exact congrArg G hw'
    · intro hv
      refine ⟨e.symm v, fun a ha => ?_, e.apply_symm_apply v⟩
      apply e.injective
      have hva : ((((MulAut.conj g) a : ↥(adjointGroup .E6 K)) : ModGL .E6 K) :
          Module.End K (RootModule .E6 K)) v = v := hv _ ⟨a, ha, rfl⟩
      rw [key a] at hva
      have hGe : G (e.symm v) = v := e.apply_symm_apply v
      show G (((a : ModGL .E6 K) : Module.End K (RootModule .E6 K)) (e.symm v)) = G (e.symm v)
      rw [hGe]
      have hGi : e.symm v = Gi v := rfl
      rw [hGi]
      simpa only [Module.End.mul_apply] using hva
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e _)

theorem adj_pair_bound_E6 (A : Subgroup ↥(adjointGroup .E6 K)) (hA : A ≠ ⊥)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hel : ∀ a ∈ A, a ^ 2 = 1) :
    Nat.card A ^ 2 * Nat.card K ^ Module.finrank K ↥(adjFix K A) ≤ Nat.card K ^ 59 := by
  have hp : IsPGroup 2 A := fun a => ⟨1, Subtype.ext (by simpa using hel a a.2)⟩
  obtain ⟨g, hg⟩ := adjoint_conj_into_U K Tag.E6 A hp
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'def
  have hinj := (MulAut.conj g).injective
  have hA' : A' ≠ ⊥ := fun h => hA ((Subgroup.map_eq_bot_iff_of_injective A hinj).1 h)
  have hpos : ∀ a ∈ A', (a : ModGL .E6 K) ∈ CFSG.Blueprint.Chevalley.posUnipotent .E6 K := fun a ha =>
    Subgroup.mem_subgroupOf.1 (hg ha)
  have hcomm' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have h := adj_pair_core A' hA' hpos hcomm'
  have hc : Nat.card A' = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv).symm
  rw [hc, Module.natCard_eq_pow_finrank (K := K) (V := ↥(adjFix K A')), adjFix_conj] at h
  exact h

end Conj

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc
