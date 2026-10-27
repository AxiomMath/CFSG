module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IMain

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Bound

variable {K : Type} [Field K] [Finite K]


theorem sgnB_zero (v : D4Vec) : sgnB (fun _ => false) v = false := by
  simp [sgnB]

theorem perm_cube (m : ℕ) (v : D4Vec) :
    permLattice (d4Rho ^ m) (permLattice (d4Rho ^ m) (permLattice (d4Rho ^ m) v)) = v := by
  rw [← permLattice_mul', ← permLattice_mul']
  have : d4Rho ^ m * d4Rho ^ m * d4Rho ^ m = 1 := by
    rw [← pow_add, ← pow_add, show m + m + m = 3 * m by ring, pow_mul, d4Rho_pow_three, one_pow]
  rw [this, permLattice_one']

theorem invariant_of_perm :
    ∀ m ∈ ({2, 4} : Finset ℕ), ∀ b : D4Idx → Bool, (∀ i, b ((d4Rho ^ m) i) = b i) →
      b 0 = b 1 ∧ b 1 = b 3 := by decide +kernel

theorem rA_isRoot : ∀ i : D4Idx, IsRoot Tag.D4 (rA i) := fun i => by
  have : ∀ i : D4Idx, rA i ∈ rootFinset Tag.D4 := by decide +kernel
  exact mem_rootFinset.1 (this i)

theorem two_ne_zero_of_charThree [CharP K 3] : (2 : K) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at this
  omega

theorem neg_one_ne_one_of_charThree [CharP K 3] : (-1 : K) ≠ 1 := by
  intro h
  apply two_ne_zero_of_charThree (K := K)
  linear_combination -h

theorem chev_card_le_inner_stable [CharP K 3] (α : MulAut ↥(adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (hnot : α ∉ inner ↥(adjointGroup Tag.D4 K))
    (hU : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map α.toMonoidHom =
      (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (g : ↥(adjointGroup Tag.D4 K)) (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hgU : ((posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K)).map
      (MulAut.conj g).toMonoidHom = (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hαg : α g = g) (A : Subgroup ↥(adjointGroup Tag.D4 K))
    (hAU : A ≤ (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K))
    (hfix : ∀ a ∈ A, α a = a) (hfixg : ∀ a ∈ A, g * a * g⁻¹ = a) :
    Nat.card A ≤ Nat.card K ^ 2 := by
  classical
  obtain ⟨σ, ε, la, hσ3, hε3, hinner, hr⟩ := exists_layerAct_of_stable α hα3 _ rfl hU
  have hgB := mem_borelGroup_of_stable g hgU
  set hs : BorelScalar (g : ModGL Tag.D4 K) := borelScalar_of_mem_borelGroup hgB with hshs
  have hg2' : (g : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K) = 1 := congrArg Subtype.val hg2
  have hsd := signData_of_involution hs hg2'
  obtain ⟨b, hb⟩ := signData_table (neg_one_ne_one_of_charThree (K := K)) hsd
  have hmemR : ∀ k (δ : UnitRoots Tag.D4 k), δ.1 ∈ d4RootsFrom 1 := fun k δ =>
    mem_d4RootsFrom.2 ⟨δ.2.1, (UnitRoots.pos Tag.D4 δ).2, by rw [δ.2.2]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)⟩
  have hbne : ∃ i, b i = true := by
    by_contra hcon
    push Not at hcon
    have hb0 : b = fun _ => false := funext fun i => by simpa using hcon i
    apply hg1
    refine eq_one_of_borelScalar_eq_one g hgB hg2 ?_
    intro v hv
    rw [hb v hv, hb0, sgnB_zero]
    simp
  have hβ : ∀ x : ↥(adjointGroup Tag.D4 K),
      (((MulAut.conj g) x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        (g : ModGL Tag.D4 K) * (MonoidHom.id (ModGL Tag.D4 K)) (x : ModGL Tag.D4 K) *
          (g : ModGL Tag.D4 K)⁻¹ := fun x => rfl
  let laG : LayerAct Tag.D4 (MulAut.conj g) 1 :=
    layerAct_of_borel_monomial hs (MonoidHom.id _) id (fun _ => 1) 1 (fun γ h => h)
      (fun γ => rfl) (fun γ γ' _ _ h => h)
      (fun γ _ c => by
        change pinnedX Tag.D4 K γ c = pinnedX Tag.D4 K γ (1 * c)
        rw [one_mul]) hβ (fun _ δ => δ) (fun _ _ => rfl)
  have hfixg' : ∀ a ∈ A, (MulAut.conj g) a = a := fun a ha => by
    rw [MulAut.conj_apply]; exact hfixg a ha
  have hsupp : ∀ k, ∀ q ∈ layerImage A k, ∀ δ : UnitRoots Tag.D4 k, sgnB b δ.1 = true →
      Multiplicative.toAdd q δ = 0 := by
    intro k q hq δ hδ
    have h := layerImage_fixed laG hfixg' k hq
    have h' := congrFun (congrArg Multiplicative.toAdd h) δ
    have hsδ : hs.s δ.1 = -1 := by rw [hb δ.1 (hmemR k δ), hδ]; simp
    change hs.s δ.1 * 1 * ((1 : K ≃+* K) (Multiplicative.toAdd q δ)) = Multiplicative.toAdd q δ at h'
    have h2 : (2 : K) * Multiplicative.toAdd q δ = 0 := by
      rw [hsδ] at h'
      have : (1 : K ≃+* K) (Multiplicative.toAdd q δ) = Multiplicative.toAdd q δ := rfl
      rw [this] at h'
      linear_combination -h'
    exact (mul_eq_zero.1 h2).resolve_left (two_ne_zero_of_charThree (K := K))
  haveI : ∀ k, Fintype (UnitRoots Tag.D4 k) := fun k => Fintype.ofFinite _
  let Sset : ∀ k, Finset (UnitRoots Tag.D4 k) :=
    fun k => Finset.univ.filter fun δ => sgnB b δ.1 = false
  have hSmem : ∀ k (δ : UnitRoots Tag.D4 k), δ ∈ Sset k ↔ sgnB b δ.1 = false := fun k δ => by
    simp [Sset]
  have hsuppS : ∀ k, ∀ q ∈ layerImage A k, ∀ j, j ∉ Sset k → Multiplicative.toAdd q j = 0 := by
    intro k q hq j hj
    apply hsupp k q hq j
    by_contra h
    exact hj ((hSmem k j).2 (by simpa using h))
  set d := (maxHeight Tag.D4).toNat with hd
  have hA0 : A ≤ unitN Tag.D4 K 0 := fun x hx =>
    unitN_zero_of_mem_pos (Subgroup.mem_subgroupOf.1 (hAU hx))
  have hprod := card_le_prod_of_filtration (unitN Tag.D4 K) (unitPhi Tag.D4 K) d
    (unitN_bot Tag.D4) (unitN_chain Tag.D4) (unitPhi_eq_one_iff) A hA0
    (fun k => Nat.card (layerImage A k)) (fun k _ => le_rfl)
  have hqpos : 0 < Nat.card K := Nat.card_pos
  by_cases hσ : σ = 1
  ·
    subst hσ
    have hε0 : ε ≠ 0 := fun h => hnot (hinner rfl h)
    have hε12 : ε = 1 ∨ ε = 2 := by omega
    have hm : 2 * ε ∈ ({2, 4} : Finset ℕ) := by
      rcases hε12 with h | h <;> subst h <;> simp
    have hbinv : ∀ i, b ((d4Rho ^ (2 * ε)) i) = b i := by
      intro i
      let δi : UnitRoots Tag.D4 0 := ⟨rA i, rA_isRoot i, by rw [height_rA]; rfl⟩
      have h1 := sign_perm_invariant la hs hαg 0 δi
      have h2 : (la.r 0 δi).1 = rA ((d4Rho ^ (2 * ε)) i) := by
        rw [hr, show δi.1 = rA i from rfl]
        exact permLattice_single _ i
      rw [h2] at h1
      change (1 : K ≃+* K) (hs.s (rA ((d4Rho ^ (2 * ε)) i))) = hs.s (rA i) at h1
      have h3 : hs.s (rA ((d4Rho ^ (2 * ε)) i)) = hs.s (rA i) := h1
      have hr1 : ∀ j : D4Idx, rA j ∈ d4RootsFrom 1 := fun j => by
        refine mem_d4RootsFrom.2 ⟨rA_isRoot j, ?_, ?_⟩ <;> rw [height_rA] <;> norm_num
      rw [hb _ (hr1 _), hb _ (hr1 _), sgnB_rA, sgnB_rA] at h3
      cases h4 : b ((d4Rho ^ (2 * ε)) i) <;> cases h5 : b i <;> simp [h4, h5] at h3 ⊢
      · exact neg_one_ne_one_of_charThree (K := K) h3.symm
      · exact neg_one_ne_one_of_charThree (K := K) h3
    obtain ⟨h01, h13⟩ := invariant_of_perm (2 * ε) hm b hbinv
    let Rset : ∀ k, Finset (UnitRoots Tag.D4 k) := fun k => Finset.univ.filter fun δ => orbRep δ.1
    let Tset : ∀ k, Finset (UnitRoots Tag.D4 k) := fun k =>
      (Rset k).filter fun j => j ∈ Sset k ∧ la.r k j ∈ Sset k ∧ la.r k (la.r k j) ∈ Sset k
    have hlay : ∀ k, Nat.card (layerImage A k) ≤ Nat.card K ^ (Tset k).card := by
      intro k
      have hr3 : ∀ j : UnitRoots Tag.D4 k, la.r k (la.r k (la.r k j)) = j := fun j => by
        apply Subtype.ext
        rw [hr, hr, hr]
        exact perm_cube _ _
      have hR : ∀ j, j ∈ Sset k → la.r k j ∈ Sset k → la.r k (la.r k j) ∈ Sset k →
          j ∈ Rset k ∨ la.r k j ∈ Rset k ∨ la.r k (la.r k j) ∈ Rset k := by
        intro j _ _ _
        have := orbRep_meets j.1 (hmemR k j) (2 * ε) hm
        have e1 : (la.r k j).1 = permLattice (d4Rho ^ (2 * ε)) j.1 := hr k j
        have e2 : (la.r k (la.r k j)).1 =
            permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) j.1) := by
          rw [hr, hr]
        simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [e2, e1]
        exact this
      have hmono := card_fixed_supp_orbit_le (la.r k) (la.f k) hr3 (Sset k) (Rset k) hR
      refine le_trans ?_ hmono
      refine Nat.card_le_card_of_injective (fun q => ⟨Multiplicative.toAdd q.1, ?_, ?_⟩) ?_
      · exact congrArg Multiplicative.toAdd (layerImage_fixed la hfix k q.2)
      · exact hsuppS k q.1 q.2
      · intro q q' hqq
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        exact congrArg (fun a => a.1) hqq
    have hsum : ∑ k ∈ Finset.range d, (Tset k).card ≤ 2 := by
      refine le_trans (sum_layer_filter_card_le (fun v => orbRep v ∧ sgnB b v = false) d Tset
        (fun k δ hδ => ?_)) (sgn_orbit_count_le b hbne h01 h13)
      obtain ⟨hS0, -, -⟩ := (Finset.mem_filter.1 hδ).2
      exact ⟨(by simpa [Rset] using (Finset.mem_filter.1 hδ).1), (hSmem k δ).1 hS0⟩
    calc Nat.card A ≤ ∏ k ∈ Finset.range d, Nat.card (layerImage A k) := hprod
      _ ≤ ∏ k ∈ Finset.range d, Nat.card K ^ (Tset k).card :=
          Finset.prod_le_prod' fun k _ => hlay k
      _ = Nat.card K ^ ∑ k ∈ Finset.range d, (Tset k).card := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_right hqpos hsum
  ·
    have hlay : ∀ k, Nat.card (layerImage A k) ^ 3 ≤ Nat.card K ^ (Sset k).card := by
      intro k
      have hmono := card_fixed_supp_pow_le σ hσ3 hσ (la.r k) (la.f k) (Sset k)
      refine le_trans (Nat.pow_le_pow_left ?_ 3) hmono
      refine Nat.card_le_card_of_injective (fun q => ⟨Multiplicative.toAdd q.1, ?_, ?_⟩) ?_
      · exact congrArg Multiplicative.toAdd (layerImage_fixed la hfix k q.2)
      · exact hsuppS k q.1 q.2
      · intro q q' hqq
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        exact congrArg (fun a => a.1) hqq
    have hsum : ∑ k ∈ Finset.range d, (Sset k).card ≤ 6 :=
      le_trans (sum_layer_filter_card_le (fun v => sgnB b v = false) d Sset
        (fun k δ hδ => (hSmem k δ).1 hδ)) (sgn_count_le b hbne)
    have h3 : Nat.card A ^ 3 ≤ (Nat.card K ^ 2) ^ 3 := by
      calc Nat.card A ^ 3 ≤ (∏ k ∈ Finset.range d, Nat.card (layerImage A k)) ^ 3 :=
            Nat.pow_le_pow_left hprod 3
        _ = ∏ k ∈ Finset.range d, Nat.card (layerImage A k) ^ 3 := (Finset.prod_pow _ _ _).symm
        _ ≤ ∏ k ∈ Finset.range d, Nat.card K ^ (Sset k).card :=
            Finset.prod_le_prod' fun k _ => hlay k
        _ = Nat.card K ^ ∑ k ∈ Finset.range d, (Sset k).card := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ Nat.card K ^ 6 := Nat.pow_le_pow_right hqpos hsum
        _ = (Nat.card K ^ 2) ^ 3 := by rw [← pow_mul]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 h3

end Bound

end CFSG.LocalAnalysis.GLTheoremA
