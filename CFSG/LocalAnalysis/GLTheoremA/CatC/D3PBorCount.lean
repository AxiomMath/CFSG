module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3PBorRigid

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Count

variable {K : Type} [Field K] [Finite K]



theorem sgn_orbit_count_gen :
    ∀ b : D4Idx → Bool, (∃ i, b i = true) → ∀ m ∈ ({2, 4} : Finset ℕ),
      ((d4RootsFrom 1).filter fun v => orbRep v ∧ sgnB b v = false ∧
        sgnB b (permLattice (d4Rho ^ m) v) = false ∧
        sgnB b (permLattice (d4Rho ^ m) (permLattice (d4Rho ^ m) v)) = false).card ≤ 2 ∨
      (∀ v ∈ (d4RootsFrom 1).filter fun v => orbRep v ∧ sgnB b v = false ∧
        sgnB b (permLattice (d4Rho ^ m) v) = false ∧
        sgnB b (permLattice (d4Rho ^ m) (permLattice (d4Rho ^ m) v)) = false,
        v = rA 2 ∨ v = rT4 ∨ v = rT5) := by
  decide +kernel

theorem borel_card_le [CharP K 3] (α t : MulAut ↥(adjointGroup Tag.D4 K)) (hα3 : α ^ 3 = 1)
    (hnot : α ∉ inner ↥(adjointGroup Tag.D4 K)) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hb3 : (t * α) ^ 3 = 1) (hUα : (unitU K).map α.toMonoidHom = unitU K)
    (hUt : (unitU K).map t.toMonoidHom = unitU K) (A : Subgroup ↥(adjointGroup Tag.D4 K))
    (hAU : A ≤ unitU K) (hcomm : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u) (hfix : ∀ a ∈ A, α a = a)
    (hfixt : ∀ a ∈ A, t a = a) : Nat.card A ≤ Nat.card K ^ 2 := by
  classical
  obtain ⟨σ, ε, la, hσ3, hε3, hinner, hr⟩ := exists_layerAct_of_stable α hα3 (unitU K) rfl hUα
  obtain ⟨laT, b, hrT, hbT⟩ := exists_sign_of_involution α t hα3 ht2 hb3 hUα hUt
  have hmemR : ∀ k (δ : UnitRoots Tag.D4 k), δ.1 ∈ d4RootsFrom 1 := fun k δ =>
    mem_d4RootsFrom.2 ⟨δ.2.1, (UnitRoots.pos Tag.D4 δ).2, by
      rw [δ.2.2]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)⟩
  have hbne : ∃ i, b i = true := by
    by_contra hcon
    push Not at hcon
    have hb0 : b = fun _ => false := funext fun i => by simpa using hcon i
    have hf1 : ∀ k δ, laT.f k δ = 1 := by
      intro k δ
      rw [hbT k δ, hb0, sgnB_zero]
      simp
    exact ht1 (eq_one_of_scalars_one t ht2 hUt laT hrT hf1)
  have hsupp : ∀ k, ∀ q ∈ layerImage A k, ∀ δ : UnitRoots Tag.D4 k, sgnB b δ.1 = true →
      Multiplicative.toAdd q δ = 0 := by
    intro k q hq δ hδ
    have h := layerImage_fixed laT hfixt k hq
    have h' := congrFun (congrArg Multiplicative.toAdd h) δ
    change laT.f k δ * (1 : K ≃+* K) (Multiplicative.toAdd q (laT.r k δ)) = Multiplicative.toAdd q δ
      at h'
    rw [hrT k δ, hbT k δ, if_pos hδ] at h'
    have h2 : (2 : K) * Multiplicative.toAdd q δ = 0 := by
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
  · subst hσ
    have hε0 : ε ≠ 0 := fun h => hnot (hinner rfl h)
    have hε12 : ε = 1 ∨ ε = 2 := by omega
    have hm : 2 * ε ∈ ({2, 4} : Finset ℕ) := by
      rcases hε12 with h | h <;> subst h <;> simp
    let Rset : ∀ k, Finset (UnitRoots Tag.D4 k) := fun k => Finset.univ.filter fun δ => orbRep δ.1
    have hr3 : ∀ k (j : UnitRoots Tag.D4 k), la.r k (la.r k (la.r k j)) = j := fun k j => by
      apply Subtype.ext
      rw [hr, hr, hr]
      exact perm_cube _ _
    have hRmeets : ∀ k (j : UnitRoots Tag.D4 k),
        j ∈ Rset k ∨ la.r k j ∈ Rset k ∨ la.r k (la.r k j) ∈ Rset k := by
      intro k j
      have := orbRep_meets j.1 (hmemR k j) (2 * ε) hm
      have e1 : (la.r k j).1 = permLattice (d4Rho ^ (2 * ε)) j.1 := hr k j
      have e2 : (la.r k (la.r k j)).1 =
          permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) j.1) := by rw [hr, hr]
      simp only [Rset, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [e2, e1]
      exact this
    have layer_card_le : ∀ k (S : Finset (UnitRoots Tag.D4 k)),
        (∀ q ∈ layerImage A k, ∀ j, j ∉ S → Multiplicative.toAdd q j = 0) →
        Nat.card (layerImage A k) ≤ Nat.card K ^
          ((Rset k).filter fun j => j ∈ S ∧ la.r k j ∈ S ∧ la.r k (la.r k j) ∈ S).card := by
      intro k S hS
      have hmono := card_fixed_supp_orbit_le (la.r k) (la.f k) (hr3 k) S (Rset k)
        (fun j _ _ _ => hRmeets k j)
      refine le_trans ?_ hmono
      refine Nat.card_le_card_of_injective (fun q => ⟨Multiplicative.toAdd q.1, ?_, ?_⟩) ?_
      · exact congrArg Multiplicative.toAdd (layerImage_fixed la hfix k q.2)
      · exact hS q.1 q.2
      · intro q q' hqq
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        exact congrArg (fun a => a.1) hqq
    let Tset : ∀ k, Finset (UnitRoots Tag.D4 k) := fun k =>
      (Rset k).filter fun j => j ∈ Sset k ∧ la.r k j ∈ Sset k ∧ la.r k (la.r k j) ∈ Sset k
    have hlay : ∀ k, Nat.card (layerImage A k) ≤ Nat.card K ^ (Tset k).card :=
      fun k => layer_card_le k (Sset k) (hsuppS k)
    have hTP : ∀ k, ∀ δ ∈ Tset k, orbRep δ.1 ∧ sgnB b δ.1 = false ∧
        sgnB b (permLattice (d4Rho ^ (2 * ε)) δ.1) = false ∧
        sgnB b (permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) δ.1)) = false := by
      intro k δ hδ
      obtain ⟨hR, hS0, hS1, hS2⟩ := Finset.mem_filter.1 hδ
      have e1 : (la.r k δ).1 = permLattice (d4Rho ^ (2 * ε)) δ.1 := hr k δ
      have e2 : (la.r k (la.r k δ)).1 =
          permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) δ.1) := by rw [hr, hr]
      refine ⟨by simpa [Rset] using hR, (hSmem k δ).1 hS0, ?_, ?_⟩
      · rw [← e1]; exact (hSmem k _).1 hS1
      · rw [← e2]; exact (hSmem k _).1 hS2
    rcases sgn_orbit_count_gen b hbne (2 * ε) hm with hc | hc
    · have hsum : ∑ k ∈ Finset.range d, (Tset k).card ≤ 2 :=
        le_trans (sum_layer_filter_card_le (fun v => orbRep v ∧ sgnB b v = false ∧
          sgnB b (permLattice (d4Rho ^ (2 * ε)) v) = false ∧
          sgnB b (permLattice (d4Rho ^ (2 * ε)) (permLattice (d4Rho ^ (2 * ε)) v)) = false) d Tset
          (fun k δ hδ => hTP k δ hδ)) hc
      calc Nat.card A ≤ ∏ k ∈ Finset.range d, Nat.card (layerImage A k) := hprod
        _ ≤ ∏ k ∈ Finset.range d, Nat.card K ^ (Tset k).card :=
            Finset.prod_le_prod' fun k _ => hlay k
        _ = Nat.card K ^ ∑ k ∈ Finset.range d, (Tset k).card := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_right hqpos hsum
    ·
      have hTfix : ∀ k, ∀ δ ∈ Tset k, δ.1 = rA 2 ∨ δ.1 = rT4 ∨ δ.1 = rT5 := fun k δ hδ =>
        hc δ.1 (Finset.mem_filter.2 ⟨hmemR k δ, hTP k δ hδ⟩)
      have hTk : ∀ k, ∀ δ ∈ Tset k,
          (δ.1 = rA 2 ∧ k = 0) ∨ (δ.1 = rT4 ∧ k = 3) ∨ (δ.1 = rT5 ∧ k = 4) := by
        intro k δ hδ
        have h := δ.2.2
        rcases hTfix k δ hδ with h2 | h2 | h2
        · refine Or.inl ⟨h2, ?_⟩
          rw [h2, height_rA] at h
          omega
        · refine Or.inr (Or.inl ⟨h2, ?_⟩)
          rw [h2, isPos_rT4.2] at h
          omega
        · refine Or.inr (Or.inr ⟨h2, ?_⟩)
          rw [h2, isPos_rT5.2] at h
          omega
      have hT1 : ∀ k, (Tset k).card ≤ 1 := by
        intro k
        refine Finset.card_le_one.2 fun x hx y hy => ?_
        apply Subtype.ext
        rcases hTk k x hx with ⟨h1, k1⟩ | ⟨h1, k1⟩ | ⟨h1, k1⟩ <;>
          rcases hTk k y hy with ⟨h2, k2⟩ | ⟨h2, k2⟩ | ⟨h2, k2⟩ <;>
          first | (exfalso; omega) | (rw [h1, h2])
      have hT0 : ∀ k, k ≠ 0 → k ≠ 3 → k ≠ 4 → (Tset k).card = 0 := by
        intro k h0 h3 h4
        by_contra hne
        obtain ⟨δ, hδ⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
        rcases hTk k δ hδ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
        · exact h0 h
        · exact h3 h
        · exact h4 h
      have hI1 : Nat.card (layerImage A 1) ≤ 1 := by
        have := hlay 1
        rwa [hT0 1 (by norm_num) (by norm_num) (by norm_num), pow_zero] at this
      have hI2 : Nat.card (layerImage A 2) ≤ 1 := by
        have := hlay 2
        rwa [hT0 2 (by norm_num) (by norm_num) (by norm_num), pow_zero] at this
      have hIK : ∀ k, Nat.card (layerImage A k) ≤ Nat.card K := fun k =>
        (hlay k).trans (by
          calc Nat.card K ^ (Tset k).card ≤ Nat.card K ^ 1 := Nat.pow_le_pow_right hqpos (hT1 k)
            _ = Nat.card K := pow_one _)
      have hd5 : d = 5 := by rw [hd, maxHeight_D4]; rfl
      rw [hd5] at hprod
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hprod
      by_cases hu : ∃ u ∈ A, pc (rA 2) (u : ModGL Tag.D4 K) ≠ 0
      · obtain ⟨u, huA, hu2⟩ := hu
        have hI3 : Nat.card (layerImage A 3) ≤ 1 := by
          rw [Finite.card_le_one_iff_subsingleton]
          refine ⟨fun x y => ?_⟩
          obtain ⟨x', hxA, hxq⟩ := x.2
          obtain ⟨y', hyA, hyq⟩ := y.2
          have hx4 := claim_three hA0 hcomm huA hu2 hxA x'.2
          have hy4 := claim_three hA0 hcomm huA hu2 hyA y'.2
          apply Subtype.ext
          rw [← hxq, ← hyq, unitPhi_triv Tag.D4 x' hx4, unitPhi_triv Tag.D4 y' hy4]
        calc Nat.card A ≤ Nat.card (layerImage A 0) * Nat.card (layerImage A 1) *
              Nat.card (layerImage A 2) * Nat.card (layerImage A 3) * Nat.card (layerImage A 4) :=
              hprod
          _ ≤ Nat.card K * 1 * 1 * 1 * Nat.card K :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hIK 0) hI1) hI2) hI3)
                (hIK 4)
          _ = Nat.card K ^ 2 := by ring
      · push Not at hu
        have hI0 : Nat.card (layerImage A 0) ≤ 1 := by
          let δ₂ : UnitRoots Tag.D4 0 := ⟨rA 2, (isPos_rA 2).1, by rw [height_rA]; rfl⟩
          let S' : Finset (UnitRoots Tag.D4 0) := (Sset 0).erase δ₂
          have hS' : ∀ q ∈ layerImage A 0, ∀ j, j ∉ S' → Multiplicative.toAdd q j = 0 := by
            intro q hq j hj
            by_cases hjS : j ∈ Sset 0
            · have hjd : j = δ₂ := by
                by_contra hne
                exact hj (Finset.mem_erase.2 ⟨hne, hjS⟩)
              subst hjd
              obtain ⟨x, hxA, rfl⟩ := hq
              have h0 := hu x hxA
              rw [pc_of_pos (isPos_rA 2 |> fun h => ⟨h.1, h.2⟩)] at h0
              exact h0
            · exact hsuppS 0 q hq j hjS
          have hcard := layer_card_le 0 S' hS'
          have hempty : ((Rset 0).filter fun j => j ∈ S' ∧ la.r 0 j ∈ S' ∧
              la.r 0 (la.r 0 j) ∈ S').card = 0 := by
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            rintro j hjR ⟨hj1, hj2, hj3⟩
            have hjT : j ∈ Tset 0 :=
              Finset.mem_filter.2 ⟨hjR, (Finset.mem_erase.1 hj1).2, (Finset.mem_erase.1 hj2).2,
                (Finset.mem_erase.1 hj3).2⟩
            rcases hTk 0 j hjT with ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
            · exact (Finset.mem_erase.1 hj1).1 (Subtype.ext h)
            · omega
            · omega
          rw [hempty, pow_zero] at hcard
          exact hcard
        calc Nat.card A ≤ Nat.card (layerImage A 0) * Nat.card (layerImage A 1) *
              Nat.card (layerImage A 2) * Nat.card (layerImage A 3) * Nat.card (layerImage A 4) :=
              hprod
          _ ≤ 1 * 1 * 1 * Nat.card K * Nat.card K :=
              Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hI0 hI1) hI2) (hIK 3))
                (hIK 4)
          _ = Nat.card K ^ 2 := by ring
  · have hlay : ∀ k, Nat.card (layerImage A k) ^ 3 ≤ Nat.card K ^ (Sset k).card := by
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

end Count

end CFSG.LocalAnalysis.GLTheoremA
