module

public import CFSG.ClassicalInvolution.Q3.Q3WACore
public import CFSG.ClassicalInvolution.Q3.Q3WSimply

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CliffordAlgebra QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Spin
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

theorem pow_four_of_mem_center_spinPlus {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K]
    {z : spinGroup (quadPlus n K)} (hz : z ∈ Subgroup.center (spinGroup (quadPlus n K))) :
    z ^ 4 = 1 := by
  obtain ⟨-, hscal, hcen⟩ := spinToStatedProj_quadPlus (K := K) hn
  have hz1 : z ∈ (CFSG.Assembly.LowTwoRank.StatedScalars _ K).comap
      (spinMatrix (quadPlus n K)) := by
    rw [← hscal, hcen]
    exact hz
  rw [Subgroup.mem_comap, mem_statedScalars_iff, toLinEquiv_spinMatrix] at hz1
  obtain ⟨c, hc⟩ := mem_scalars.mp hz1
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero_of_hypPair _ (plusPair K (⟨0, by omega⟩ : Fin n))
  have hc2 : c * c = 1 := by
    have h := map_spinAction (quadPlus n K) z v₀
    rw [hc, map_smul_eq_sq] at h
    have h' : (c ^ 2 - 1) * (quadPlus n K) v₀ = 0 := by rw [sub_mul, h, one_mul, sub_self]
    linear_combination (mul_eq_zero.mp h').resolve_right hv₀
  have hzz : z * z ∈ (spinAction (quadPlus n K)).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun v => ?_
    rw [map_mul]
    show spinAction _ z (spinAction _ z v) = v
    rw [hc, hc, smul_smul, hc2, one_smul]
  have hzz' : z * z ∈ (spinMatrix (quadPlus n K)).ker := by
    rw [ker_spinMatrix]
    exact hzz
  rw [mem_ker_spinMatrix_quadPlus_iff] at hzz'
  have h4 : z ^ 4 = (z * z) * (z * z) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rcases hzz' with h | h
  · rw [h4, h, one_mul]
  · rw [h4]
    refine Subtype.ext ?_
    show ((z * z : spinGroup (quadPlus n K)) : CliffordAlgebra (quadPlus n K)) *
      ((z * z : spinGroup (quadPlus n K)) : CliffordAlgebra (quadPlus n K)) = 1
    rw [h]
    simp

theorem exists_theta_plusDatum3 {n : ℕ} (hn : 6 ≤ n) {F : Type} [Field F] [Finite F]
    (hadm : StatedLieAdmissible .POmegaPlus (n - 2) 3 1) (hF : Nat.card F = 3) :
    ∃ Θ : spinGroup (quadPlus (n - 2) F) →* spinGroup (quadPlus n F),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (n - 2), (rankOne (plusDatum (n - 2) F (by omega)).rootGroup k).map Θ =
        rankOne (plusDatum n F (by omega)).rootGroup (nodeD (n := n) (by omega) k)) ∧
      Θ.range = ⨆ k : Fin (n - 2),
        rankOne (plusDatum n F (by omega)).rootGroup (nodeD (n := n) (by omega) k) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set L : Fin (n - 2) → Subgroup (spinGroup (quadPlus n F)) := fun k =>
    rankOne (plusDatum n F hn3).rootGroup (nodeD (n := n) (by omega) k) with hL
  set X : Subgroup (spinGroup (quadPlus n F)) := ⨆ k, L k with hX
  have hLle : ∀ k, L k ≤ X := fun k => le_iSup L k
  obtain ⟨Ψ, hsurj, hker, -, -, -, hnodes⟩ := weakCT3_spinPlus (n := n - 2) hadm hn3' hF
    (X := ↥X) (fun k => (L k).subgroupOf X)
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self L)
    (fun i j hij h1 h2 a ha b hb => by
      have hc : cartanD n (nodeD (n := n) (by omega) i) (nodeD (n := n) (by omega) j) = 0 := by
        refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1
        · intro e
          exact hij (Fin.ext (by have := congrArg Fin.val e; simp only [nodeD] at this; omega))
        · exact fun e => h1 ((edgeD_shift (by omega)).mpr e)
        · exact fun e => h2 ((edgeD_shift (by omega)).mpr e)
      exact Subtype.ext (commutes_rankOne_plusDatum hn3 hc a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
        (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 ((edgeD_shift (by omega)).mp hij)
      have hWle : W ≤ X :=
        (linearBlockStandardPair_le_sup hW).trans (sup_le (hLle i) (hLle j))
      exact ⟨W.subgroupOf X, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf
        hWle hW⟩)
  refine ⟨X.subtype.comp Ψ, ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · intro k
    rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hLle k)]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

theorem nonempty_extModel3U_plus {n : ℕ} (hn : 6 ≤ n)
    (hscT : FundamentalSingleClass .POmegaPlus (plusDatum n (GaloisField 3 1) (by omega)))
    (hscY : FundamentalSingleClass .POmegaPlus (plusDatum (n - 2) (GaloisField 3 1) (by omega)))
    (hadmY : StatedLieAdmissible .POmegaPlus (n - 2) 3 1) :
    Nonempty (ExtModel3U .POmegaPlus .POmegaPlus
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) (by omega)⟩
      ⟨spinGroup (quadPlus (n - 2) (GaloisField 3 1)),
        plusDatum (n - 2) (GaloisField 3 1) (by omega)⟩ 2) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set F := GaloisField 3 1 with hFdef
  let n0 : Fin n := zeroD (by omega)
  obtain ⟨Θ, hker, hnode, hrange⟩ := exists_theta_plusDatum3 (n := n) hn (F := F) hadmY card_gf3
  let n0' : Fin (n - 2) := zeroD (by omega)
  set DT := plusDatum n F hn3 with hDT
  set DY := plusDatum (n - 2) F hn3' with hDY
  set X : Subgroup (spinGroup (quadPlus n F)) :=
    ⨆ k : Fin (n - 2), rankOne DT.rootGroup (nodeD (n := n) (by omega) k) with hX
  have hcommX0 : ∀ k : Fin (n - 2),
      Commutes (rankOne DT.rootGroup n0) (rankOne DT.rootGroup (nodeD (n := n) (by omega) k)) := by
    intro k
    refine commutes_rankOne_plusDatum hn3 ?_
    refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1
    · intro e
      have := congrArg Fin.val e
      simp only [nodeD, n0, zeroD_val] at this
      omega
    · intro e
      unfold edgeD at e
      simp only [nodeD, n0, zeroD_val] at e
      omega
    · intro e
      unfold edgeD at e
      simp only [nodeD, n0, zeroD_val] at e
      have := k.isLt
      omega
  have hcommXθ : Commutes X (rootθD n F hn3) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := nodeD (n := n) (by omega) k)
      (by simp only [nodeD]; omega)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup n0) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .POmegaPlus DY, ∃ g : spinGroup (quadPlus (n - 2) F),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeD (n := n) (by omega) n0')) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup n0')
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3' _) R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hnode]
  have h01 : edgeD n n0 (⟨1, by omega⟩ : Fin n) := by
    unfold edgeD
    left
    refine ⟨rfl, ?_⟩
    show 1 + 1 < n
    omega
  obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 h01
  have h01' : edgeD (n - 2) n0' (⟨1, by omega⟩ : Fin (n - 2)) := by
    unfold edgeD
    left
    refine ⟨rfl, ?_⟩
    show 1 + 1 < n - 2
    omega
  obtain ⟨W', hW'⟩ := standardPair_plusDatum_edge (F := F) hn3' h01'
  refine ⟨{
    Rθ := rootθD n F hn3
    twin := fun _ => rankOne DT.rootGroup n0
    Θ := Θ
    Rθ_mem := rootθD_mem_fundamentalSubgroups hn3 (by omega)
    twin_mem := fun _ => rankOne_mem_fundamentalSubgroups_plusDatum hn3 _
    Θ_ker := hker
    Θ_mem := ?_
    Θ_comm := ?_
    twin_comm := ?_
    twin_comm_Θ := ?_
    twin_inj := fun a b _ => Fin.ext (by have h1 := a.isLt; have h2 := b.isLt; omega)
    pow_T := pow3_of_mem_fundamental hscT
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3 n0) (pow3_of_stdPair card_gf3 hW).1
    pow_Y := pow3_of_mem_fundamental hscY
      (rankOne_mem_fundamentalSubgroups_plusDatum hn3' n0') (pow3_of_stdPair card_gf3 hW').1
    cop_T := fun z hz => ?_
    cop_Y := fun z hz => ?_ }⟩
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by
      rw [← hrange]
      exact ⟨g, rfl⟩
    have h1 : CFSG.ClassicalInvolution.Generic.conjSub (Θ g) (rootθD n F hn3) = rootθD n F hn3 :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2 : Commutes (rankOne DT.rootGroup (nodeD (n := n) (by omega) n0'))
        (rootθD n F hn3) :=
      (commutes_rootθD_rankOne hn3 (by omega) (k := nodeD (n := n) (by omega) n0')
        (by simp only [nodeD]; omega)).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · intro i
    exact (commutes_rootθD_rankOne hn3 (by omega) (k := n0) (by simp [n0, zeroD_val])).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by
      rw [← hrange]
      exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2 := hcommX0 n0'
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · have h4 := pow_four_of_mem_center_spinPlus hn3 hz
    intro h3
    exact absurd (h3.trans (orderOf_dvd_of_pow_eq_one h4)) (by norm_num)
  · have h4 := pow_four_of_mem_center_spinPlus hn3' hz
    intro h3
    exact absurd (h3.trans (orderOf_dvd_of_pow_eq_one h4)) (by norm_num)

end CFSG.ClassicalInvolution.Q3.Q3W
