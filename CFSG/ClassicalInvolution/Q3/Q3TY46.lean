module

public import CFSG.ClassicalInvolution.Q3.Q3TY42
public import CFSG.ClassicalInvolution.Q3.Q3TY41
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixMod
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixNorm

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.E8D8
open CFSG.ClassicalInvolution.ModelFacts (map_longSL2_range)
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


section TwoPairs

theorem false_of_two_linear_pairs_six3
    (R : Fin 2 → Fin 2 → Subgroup (SpinM3 6))
    (hR : ∀ i j, R i j ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr 3 1)))
    (hadj : ∀ i, ModelAdj (Subgroup.center (SpinM3 6)) (R i 0) (R i 1))
    (hlin : ∀ i, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R i 0) (R i 1))
    (hcomm : ∀ i i', i ≠ i' → ∀ j j', Commutes (R i j) (R i' j')) : False := by
  classical
  have cq := ctx_centralQuot3 (by norm_num : 4 ≤ 6)
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Vm 6 (GaloisField 3 1)) := by
    rw [finrank_minus 3 1 6 (by omega)]
    omega
  choose ι hι using fun i j => cq.map_mem (R i j) (hR i j)
  have hadjV : ∀ i, ModelAdj (scalars (GaloisField 3 1) (Vm 6 (GaloisField 3 1)))
      ((R i 0).map (spinAction (QM3 6))) ((R i 1).map (spinAction (QM3 6))) := fun i =>
    cq.modelAdj (hR i 0) (hR i 1) (hadj i)
  have hdata := fun i => adj_data hodd hdim (hι i 0) (hι i 1) (hadjV i)
  have hsing : ∀ i, HasSingularVector (QM3 6) (negSpace (ι i 0) ⊓ negSpace (ι i 1)) := by
    intro i
    obtain ⟨W, hW⟩ := hlin i
    exact hasSingularVector_of_linearPair3 (hι i 0) (hι i 1) (hdata i).1
      (hdata i).2.1 (hdata i).2.2 ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
  have hpd : ∀ i, PairDecomposition (QM3 6) (ι i 0) (ι i 1) := fun i =>
    (lemma_6_10 hodd (hι i 0) (hι i 1) (hdata i).1 (hdata i).2.1 (hdata i).2.2).1
  have hU : ∀ i (k : Fin 3), HasSingularVector (QM3 6) (planeOf (ι i 0) (ι i 1) k) := by
    intro i k
    fin_cases k
    · exact (hpd i).type₁₂.mpr (hsing i)
    · exact hsing i
    · exact (hpd i).type₂₃.mp (hsing i)
  have hhyp : ∀ i (k : Fin 3), ∃ P : HypPair (QM3 6),
      P.e ∈ planeOf (ι i 0) (ι i 1) k ∧ P.f ∈ planeOf (ι i 0) (ι i 1) k := by
    intro i k
    obtain ⟨P, he, hf, -⟩ := exists_hypPair_of_hasSingularVector (planeOf_nondeg (hpd i) k)
      (planeOf_finrank (hpd i) k) (hU i k)
    exact ⟨P, he, hf⟩
  choose P hPe hPf using hhyp
  have horth : ∀ i i', i ≠ i' → ∀ j j', ∀ x ∈ negSpace (ι i j), ∀ y ∈ negSpace (ι i' j'),
      polar (QM3 6) x y = 0 := by
    intro i i' hii' j j' x hx y hy
    have h := polar_negSpace_eq_zero_of_commutes_adj hodd (hι i 0) (hι i 1) (hι i' j')
      (hdata i).1 (hadjV i).1 (hadjV i).2.1
      ((cq.commutes_iff (hR i' j')).mpr (hcomm i' i (Ne.symm hii') j' 0))
      ((cq.commutes_iff (hR i' j')).mpr (hcomm i' i (Ne.symm hii') j' 1))
    fin_cases j
    · exact h.1 x hx y hy
    · exact h.2 x hx y hy
  have hPorth : ∀ a b : Fin 2 × Fin 3, a ≠ b → (P a.1 a.2).Orth (P b.1 b.2) := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hkk : k ≠ k' := fun h => hne (by rw [h])
      exact TwinSmall.hypPair_orth_of_mem (planeOf_orth (hpd i) k k' hkk) (hPe i k) (hPf i k)
        (hPe i k') (hPf i k')
    · exact TwinSmall.hypPair_orth_of_mem (S := negSpace (ι i (planeSide k)))
        (T := negSpace (ι i' (planeSide k'))) (horth i i' hii _ _)
        (planeOf_le_negSpace (ι i) k (hPe i k)) (planeOf_le_negSpace (ι i) k (hPf i k))
        (planeOf_le_negSpace (ι i') k' (hPe i' k')) (planeOf_le_negSpace (ι i') k' (hPf i' k'))
  let e : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv
  refine TwinSmall.false_of_pairs_minus (minusCoeffs_irr 3 1) hodd (n := 6) (by norm_num)
    (fun a => P (e.symm a).1 (e.symm a).2) fun a b hab => hPorth _ _ fun h => hab (by
      have := congrArg e h
      simpa using this)

end TwoPairs

section Pair

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {π : KY →* (V ≃ₗ[F] V)}

theorem hpair_data3 (hodd : Odd (Nat.card F)) (hdim : 9 ≤ Module.finrank F V)
    (cq : CentralQuot3 π 𝓕 (fundSet Q) (scalars F V)) {R R' R₁ : Subgroup KY} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕) (hadj : ModelAdj (Subgroup.center KY) R R')
    (hc : Commutes R R₁) (hc' : Commutes R' R₁) {i₁ : V ≃ₗ[F] V}
    (hi₁ : IsFundamental Q (R₁.map π) i₁) {g : V ≃ₗ[F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hgR : ∀ y ∈ R, g * π y = π y * g) (hgR' : ∀ y ∈ R', g * π y = π y * g) :
    ∃ (T : Submodule F V) (s : F), 6 ≤ Module.finrank F T ∧ (∀ v ∈ T, g v = s • v) ∧
      ∀ v ∈ T, ∀ w ∈ negSpace i₁, polar Q v w = 0 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  obtain ⟨i', hi'⟩ := cq.map_mem R' hR'
  have hadjV := cq.modelAdj hR hR' hadj
  obtain ⟨cm, hN, hC⟩ := adj_data hodd hdim hi hi' hadjV
  have hfin : Module.finrank F ↥(negSpace i ⊓ negSpace i') = 2 :=
    finrank_inf_negSpace hodd hi hi' cm hN hC
  have h4 : Module.finrank F ↥(negSpace i) = 4 := finrank_negSpace hodd hi
  have h4' : Module.finrank F ↥(negSpace i') = 4 := finrank_negSpace hodd hi'
  obtain ⟨s, hs⟩ := TwinSmall.sign_on_negSpace h2 hi hgO hg2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact hgR y hy)
  obtain ⟨s', hs'⟩ := TwinSmall.sign_on_negSpace h2 hi' hgO hg2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact hgR' y hy)
  have hss : s = s' := by
    have hpos : 0 < Module.finrank F ↥(negSpace i ⊓ negSpace i') := by omega
    have hne : negSpace i ⊓ negSpace i' ≠ ⊥ := fun h =>
      (Nat.pos_iff_ne_zero.mp hpos) (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 : (s - s') • v = 0 := by
      rw [sub_smul, ← hs v hv.1, ← hs' v hv.2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv0)
  refine ⟨negSpace i ⊔ negSpace i', s, ?_, ?_, ?_⟩
  · have := Submodule.finrank_sup_add_finrank_inf_eq (negSpace i) (negSpace i')
    omega
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hs a ha, hs' b hb, ← hss, smul_add]
  · intro v hv w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have horth := polar_negSpace_eq_zero_of_commutes_adj hodd hi hi' hi₁ cm hadjV.1 hadjV.2.1
      ((cq.commutes_iff hR₁).mpr (commutes_symm hc)) ((cq.commutes_iff hR₁).mpr (commutes_symm hc'))
    rw [polar_add_left, horth.1 a ha w hw, horth.2 b hb w hw, add_zero]

end Pair

section Spin

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {Z' : Subgroup (V ≃ₗ[F] V)} {π : KY →* (V ≃ₗ[F] V)}

omit [Finite F] in
theorem normalizes_of_image_normalizes3 (cq : CentralQuot3 π 𝓕 (fundSet Q) Z') {R : Subgroup KY}
    (hR : R ∈ 𝓕) {r : KY}
    (hN : π r ∈ Subgroup.normalizer ((R.map π : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V))) :
    ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  have hst := mem_of_stable3 π cq.ker_le cq.cop (MulAut.conj r) (MulAut.conj (π r))
    (fun y => by simp) (cq.pow3 R hR) (fun y hy => by
      have h1 : (MulAut.conj (π r)) (π y) ∈ R.map π := by
        have := (Subgroup.mem_normalizer_iff.mp hN (π y)).mp ⟨y, hy, rfl⟩
        simpa [MulAut.conj_apply] using this
      exact h1)
  intro y hy
  exact hst y hy

end Spin

section Leaf

theorem exists_leaf_subgroup_norm3 {m : ℕ} (hm : 4 ≤ m)
    {i j : Fin (m - 1)} (hij : i ≠ j) (s t : Bool) :
    ∃ R : Subgroup (SpinM3 m),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)) ∧
      (∀ (k l : ℕ) (hk : k < m - 1) (hl : l < m - 1) (hkl : k ≠ l), k ≠ i.val → k ≠ j.val →
        l ≠ i.val → l ≠ j.val → ∀ s' t' : Bool,
          Commutes R (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) k l hk hl hkl
            s' t')) ∧
      ¬ Commutes (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t) R ∧
      R ≠ rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t ∧
      (∀ r', InvOf R r' → ∀ y ∈ rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t,
          r' * y * r'⁻¹ ∈ rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
            i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t) ∧
      (∀ r r', InvOf R r → InvOf (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t) r' → r * r' = r' * r) := by
  have cq := ctx_centralQuot3 hm
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  obtain ⟨F_N, hv₀, hα, hperp, hcomm, hfin, hncomm, hne⟩ :=
    TwinSmall.exists_leaf_frame (minusCoeffs_irr 3 1) hodd hij s t
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hL : F_N.La.range ∈ fundSet (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) := ⟨F_N.La (-1), IsFundamental.of_frame F_N⟩
  obtain ⟨R, hR, hRmap⟩ := cq.surj _ hL
  have hD : rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
      j.isLt (fun h => hij (Fin.ext h)) s t ∈
      fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)) :=
    rootSL2_mem_fund3 hm i.isLt j.isLt (fun h => hij (Fin.ext h)) s t
  have hDmap : (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
      j.isLt (fun h => hij (Fin.ext h)) s t).map (spinAction (quadMinus m (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) =
      ((minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toFrame hij s t).La.range :=
    map_longSL2_range _ hij s t
  have hFD : IsFundamental (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (((minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toFrame hij
        s t).La.range) (((minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toFrame hij s t).La
          (-1)) := IsFundamental.of_frame _
  have hFN : IsFundamental (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) F_N.La.range (F_N.La (-1)) := IsFundamental.of_frame _
  have hN : F_N.La (-1) ∈ Subgroup.normalizer
      ((((minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toFrame hij s t).La.range :
        Subgroup _) : Set _) := by
    refine (mem_normalizer_iff_even hodd hFD hFN hcomm).mpr ?_
    rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2, hfin]
    exact ⟨1, rfl⟩
  refine ⟨R, hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro k l hk hl hkl hki hkj hli hlj s' t'
    have hkl' : (⟨k, hk⟩ : Fin (m - 1)) ≠ ⟨l, hl⟩ := fun h => hkl (congrArg Fin.val h)
    have hmap : (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) k l hk hl hkl
        s' t').map (spinAction (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2)) =
        ((minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toFrame hkl' s' t').La.range :=
      map_longSL2_range _ hkl' s' t'
    refine (cq.commutes_iff hR).mp ?_
    rw [hRmap, hmap]
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    refine Frame.La_comm_of_orth (fun X Y => ?_) A B
    have hkI : (⟨k, hk⟩ : Fin (m - 1)) ≠ i := fun h => hki (congrArg Fin.val h)
    have hkJ : (⟨k, hk⟩ : Fin (m - 1)) ≠ j := fun h => hkj (congrArg Fin.val h)
    have hlI : (⟨l, hl⟩ : Fin (m - 1)) ≠ i := fun h => hli (congrArg Fin.val h)
    have hlJ : (⟨l, hl⟩ : Fin (m - 1)) ≠ j := fun h => hlj (congrArg Fin.val h)
    have hx : F_N.incl X ∈ F_N.span := ⟨X, rfl⟩
    generalize F_N.incl X = x at hx ⊢
    have h1 := hperp x hx ⟨k, hk⟩ hkI hkJ
    have h2' := hperp x hx ⟨l, hl⟩ hlI hlJ
    simp only [Frame.incl_apply, polar_add_right, polar_smul_right]
    simp [HypFrame.toFrame, h1, h2']
  · intro hc
    have := (cq.commutes_iff hR).mpr (commutes_symm hc)
    rw [hRmap, hDmap] at this
    exact hncomm (commutes_symm this)
  · intro h
    have := congrArg (Subgroup.map (spinAction (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))) h
    rw [hRmap, hDmap] at this
    exact hne this.symm
  · intro r' hr' y hy
    have hFN' : IsFundamental (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) (R.map (spinAction (quadMinus m (GaloisField 3 1)
          (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) (F_N.La (-1)) := by
      rw [hRmap]
      exact hFN
    have hπr' : spinAction (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) r' = F_N.La (-1) := map_invOf_eq3 hodd cq hR hFN' hr'
    exact normalizes_of_image_normalizes3 cq hD (r := r') (by rw [hπr', hDmap]; exact hN) y hy
  · intro r r' hr hr'
    have := invs_commute_of_normalizes3 hodd cq hD hR (i := ((minusHyp m (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).toFrame hij s t).La (-1)) (i' := F_N.La (-1))
      (by rw [hDmap]; exact hFD) (by rw [hRmap]; exact hFN) (by rw [hDmap]; exact hN) r' r hr' hr
    exact this.symm

end Leaf

section Glue

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {tY : StatedLieTag} {nY : ℕ}
  {N : Subgroup G} {x : G}

theorem conjSub_eq_of_normalizes3 (cx : Q3TC.TCtx3 tY nY Ω N x) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hR' : R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    (hLR : locImg Ω x L = R.map cx.d.ψ) (hLR' : locImg Ω x L' = R'.map cx.d.ψ) {w' : G}
    (hw' : IsClassicalMember3 L' w')
    (hnorm : ∀ r', InvOf R' r' → ∀ y ∈ R, r' * y * r'⁻¹ ∈ R) : conjSub w' L = L := by
  have hwx : w' ∈ locLayer Ω x := le_centralizingLayer hL' hw'.mem
  obtain ⟨r', hr', hψr'⟩ := exists_involution_of_fund3 cx hL' hR' hLR' hw'
  have hw'x : w' * x * w'⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hL'.2 hw'.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have hmem : conjSub w' L ∈ centralizingMembers Ω {x} := by
    have h := centralizingMembers_conj cx.hΩ.conjInvariant w' x
    rw [hw'x] at h
    rw [h]
    exact ⟨L, hL, rfl⟩
  refine cx.eq_of_locImg_eq hmem hL ?_
  rw [locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w', hwx⟩, hLR]
  have hψ : locMk Ω x ⟨w', hwx⟩ = cx.d.ψ r' := hψr'.symm
  rw [hψ, map_conj_map_hom]
  congr 1
  have hrr : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [hr'.2, pow_two] at this
  have hri : r'⁻¹ = r' := inv_eq_of_mul_eq_one_right hrr
  ext y
  rw [mem_conjSub_iff, hri]
  constructor
  · intro h
    have := hnorm r' hr' _ h
    rw [hri] at this
    rwa [show r' * (r' * y * r') * r' = y by
      calc r' * (r' * y * r') * r' = (r' * r') * y * (r' * r') := by group
        _ = y := by rw [hrr]; group] at this
  · intro h
    have := hnorm r' hr' y h
    rwa [hri] at this

end Glue

end CFSG.ClassicalInvolution.Q3.Q3TY
