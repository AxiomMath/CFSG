module

public import CFSG.ClassicalInvolution.Q3.Q3TY40
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLeafSpin
public import CFSG.ClassicalInvolution.RouteD.TwinSmallCross

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.ModelFacts (map_longSL2_range)
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Leaf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem leaf_commutes_beta_gen3 {m : ℕ} (hm : 7 ≤ m) (c : Q3TC.TCtx3 .POmegaMinus m Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β M : Subgroup G} (nd : DNodes3 (m - 1) Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {W₀ : Subgroup G} {x₀ : G} (hW₀ : W₀ ∈ Ω) (hx₀ : IsClassicalMember3 W₀ x₀)
    (hW0 : ∀ a (h : a < m - 1), a ≤ 2 → Commutes (nd.J ⟨a, h⟩) W₀)
    {E : Subgroup G} {wE : G} (hEΩ : E ∈ Ω) (hwE : IsClassicalMember3 E wE)
    (hEW : Commutes E W₀) (hEK : Commutes E K) (hEJ : ¬ Commutes E (nd.J ⟨2, by omega⟩))
    (hEne : E ≠ nd.J ⟨2, by omega⟩) (hEw : Commute wE (nd.w ⟨2, by omega⟩))
    {D N : Subgroup G} {wD wN : G} (hDΩ : D ∈ Ω) (hNΩ : N ∈ Ω)
    (hwD : IsClassicalMember3 D wD) (hwN : IsClassicalMember3 N wN)
    (hDW : Commutes D W₀) (hNW : Commutes N W₀) (hDK : Commutes D K)
    (hD2 : Commutes D (nd.J ⟨2, by omega⟩)) (hNK : Commutes N K)
    (hN2 : Commutes N (nd.J ⟨2, by omega⟩)) (hDne : D ≠ N) (hDNn : ¬ Commutes D N)
    (hDNw : Commute wD wN) : Commutes N β := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hF := orthCross_minus3 (by omega : 5 ≤ m)
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hW₀ hx₀
  have hmem : ∀ a (h : a < m - 1), a ≤ 2 → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {x₀} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) hx₀.mem (hW0 a h ha)
  have a01 : DNodes3.Adj (⟨0, by omega⟩ : Fin (m - 1)) ⟨1, by omega⟩ := by fr_idx
  have a12 : DNodes3.Adj (⟨1, by omega⟩ : Fin (m - 1)) ⟨2, by omega⟩ := by fr_idx
  have hK : K ∈ centralizingMembers Ω {x₀} := h0 ▸ hmem 0 (by omega) (by omega)
  have hβ : β ∈ centralizingMembers Ω {x₀} := h1 ▸ hmem 1 (by omega) (by omega)
  have hJ : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {x₀} := hmem 2 (by omega) (by omega)
  have hEx : E ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hEΩ hx₀.mem hEW
  have hDx : D ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hDΩ hx₀.mem hDW
  have hNx : N ∈ centralizingMembers Ω {x₀} := mem_centralizingMembers_of_commutes hNΩ hx₀.mem hNW
  have hwK : IsClassicalMember3 K (nd.w ⟨0, by omega⟩) := h0 ▸ nd.cl _
  have hwβ : IsClassicalMember3 β (nd.w ⟨1, by omega⟩) := h1 ▸ nd.cl _
  have hKN : K ≠ N := fun e => by
    rw [← e] at hNK
    exact not_commutes_self3 c.hz hNK
  have hJN : nd.J ⟨2, by omega⟩ ≠ N := fun e => by
    rw [← e] at hN2
    exact not_commutes_self3 (nd.cl _) hN2
  have hKD : K ≠ D := fun e => by
    rw [← e] at hDK
    exact not_commutes_self3 c.hz hDK
  have hJD : nd.J ⟨2, by omega⟩ ≠ D := fun e => by
    rw [← e] at hD2
    exact not_commutes_self3 (nd.cl _) hD2
  have hKE : K ≠ E := fun e => by
    rw [← e] at hEK
    exact not_commutes_self3 c.hz hEK
  have hKJ : Commutes K (nd.J ⟨2, by omega⟩) := by
    rw [← h0]
    exact nd.commutes_of_not_adj (by simp) (by fr_idx)
  refine cross_config3 cx hF (K := K) (β := β) (J := nd.J ⟨2, by omega⟩) (N := N) hK hβ hJ hNx
    hwK hwβ (nd.cl _) hwN ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩
    (by rw [← h0]; exact nd.ne_J (by simp)) hKJ hKN hNK hJN hN2 ?_ ?_ ?_
  · rw [← h0, ← h1]
    exact nd.ne_J (by simp)
  · rw [← h0, ← h1]
    exact nd.not_commutes_of_adj a01
  · exact nd.commute_w _ _
  · rw [← h0]
    exact nd.conjSub_w a01
  · rw [← h1]
    exact nd.ne_J (by simp)
  · rw [← h1]
    exact nd.not_commutes_of_adj a12
  · exact nd.commute_w _ _
  · rw [← h1]
    exact nd.conjSub_w a12
  ·
    refine ⟨E, wE, hEx, hwE, hKE.symm, hEne, ?_, hEw, hEK, hEJ⟩
    exact hEK _ hwE.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
  ·
    refine ⟨D, wD, hDx, hwD, hKD.symm, hDne, ?_, hDNw, hDK, hDNn⟩
    exact hDK wD hwD.mem _ (h0 ▸ (nd.cl ⟨0, by omega⟩).mem)
  ·
    refine ⟨D, wD, hDx, hwD, hJD.symm, hDne, ?_, hDNw, hD2, hDNn⟩
    exact hD2 wD hwD.mem _ (nd.cl ⟨2, by omega⟩).mem

end Leaf

section Spin

theorem rootSL2_mem_fund3 {m : ℕ} (hm : 4 ≤ m) {a b : ℕ} (ha : a < m - 1) (hb : b < m - 1)
    (hab : a ≠ b) (s t : Bool) :
    rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a b ha hb hab s t ∈
      fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)) := by
  have cq := centralQuot3_minus (show StatedLieAdmissible .POmegaMinus m 3 1 from
    ⟨Nat.prime_three, le_rfl, hm⟩)
  have := cq.rootSL2_conj_mem (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) ha hb hab s t
    (1 : spinGroup (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
  have hid : (MulAut.conj (1 : spinGroup (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))).toMonoidHom = MonoidHom.id _ := by
    ext
    simp
  rwa [hid, Subgroup.map_id] at this

theorem exists_leaf_subgroup3 {m : ℕ} (hm : 4 ≤ m)
    {i j : Fin (m - 1)} (hij : i ≠ j) (s t : Bool) :
    ∃ R : Subgroup (spinGroup (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)),
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum m (minusCoeffs_irr 3 1)) ∧
      (∃ F_N : OPFrame (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        R.map (spinAction (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2)) = F_N.La.range ∧ TwinSmall.leafV₀ m i ∈ F_N.span ∧
          ∀ w, planeVec m w ∈ F_N.span) ∧
      (∀ (k l : ℕ) (hk : k < m - 1) (hl : l < m - 1) (hkl : k ≠ l), k ≠ i.val → k ≠ j.val →
        l ≠ i.val → l ≠ j.val → ∀ s' t' : Bool,
          Commutes R (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) k l hk hl hkl
            s' t')) ∧
      ¬ Commutes (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t) R ∧
      R ≠ rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) i.val j.val i.isLt
        j.isLt (fun h => hij (Fin.ext h)) s t ∧
      (∀ r r', InvOf R r → InvOf (rootSL2 (minusHyp m (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        i.val j.val i.isLt j.isLt (fun h => hij (Fin.ext h)) s t) r' → r * r' = r' * r) := by
  have cq := centralQuot3_minus (show StatedLieAdmissible .POmegaMinus m 3 1 from
    ⟨Nat.prime_three, le_rfl, hm⟩)
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
  refine ⟨R, hR, ⟨F_N, hRmap, hv₀, hα⟩, ?_, ?_, ?_, ?_⟩
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
  ·
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
    intro r r' hr hr'
    have := invs_commute_of_normalizes3 hodd cq hD hR (i := ((minusHyp m (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).toFrame hij s t).La (-1)) (i' := F_N.La (-1))
      (by rw [hDmap]; exact hFD) (by rw [hRmap]; exact hFN) (by rw [hDmap]; exact hN) r' r hr' hr
    exact this.symm

end Spin

end CFSG.ClassicalInvolution.Q3.Q3TY
