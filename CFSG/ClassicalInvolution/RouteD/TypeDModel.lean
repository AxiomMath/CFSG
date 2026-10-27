module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.RouteD.TypeARecognition
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Spin
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.ModelFacts (lenSq)

section Roots

variable {n : ℕ}

@[expose] def thetaD (n : ℕ) : Fin n → ℤ := fun i => if i.val = 0 ∨ n ≤ i.val + 2 then 1 else 2

theorem toStdD_thetaD (hn : 4 ≤ n) :
    toStdD n (thetaD n) = Pi.single (⟨0, by omega⟩ : Fin n) 1 + Pi.single (⟨1, by omega⟩ : Fin n) 1 := by
  funext a
  simp only [toStdD, thetaD, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem thetaD_mem_roots (hn : 4 ≤ n) : thetaD n ∈ roots (isFiniteType_cartanD n) ∅ := by
  obtain ⟨γ, hγ, hγθ⟩ := exists_mem_rootsD_toStdD_eq (n := n) (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) (s := 1) (t := 1) (Fin.ne_of_val_ne (by simp)) (Or.inl rfl) (Or.inl rfl)
  have : γ = thetaD n := toStdD_injective n (hγθ.trans (toStdD_thetaD hn).symm)
  rwa [← this]

theorem coroot_thetaD (hn : 4 ≤ n) {k : Fin n} (hk : k.val ≠ 1) :
    coroot (cartanD n) k (thetaD n) = 0 := by
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanD_of_lt n h, toStdD_thetaD hn]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | omega | (exfalso; assumption)
  · have hk' := k.isLt
    rw [coroot_cartanD_of_not_lt n h, toStdD_thetaD hn]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

end Roots

section Datum

variable {n : ℕ} {K : Type} [Field K] (hn3 : 3 ≤ n)

theorem cartanD_symm (i j : Fin n) : cartanD n i j = cartanD n j i := by
  simp only [cartanD, Matrix.of_apply]
  split_ifs <;> omega

theorem isLongestRoot_single_plusDatum (i : Fin n) :
    CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot (plusDatum n K hn3) (Pi.single i 1) := by
  refine CFSG.ClassicalInvolution.ModelFacts.isLongest_single (plusDatum n K hn3).isFiniteType
    (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanD hn3) (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by
      have := cartanD_symm (n := n) i j
      rw [one_mul, one_mul]
      exact_mod_cast this) (fun _ => le_rfl)

end Datum

section Orthogonality

variable {n : ℕ} {K : Type} [Field K] (hn3 : 3 ≤ n)

theorem lenSq_roots_plusDatum (i₀ : Fin n) :
    ∀ γ ∈ (plusDatum n K hn3).roots, lenSq (plusDatum n K hn3).isFiniteType γ =
      lenSq (plusDatum n K hn3).isFiniteType (Pi.single i₀ 1) :=
  lenSq_eq_of_simplyLaced (plusDatum n K hn3) rfl (isLongestRoot_single_plusDatum hn3) i₀

theorem commutes_rankOne_plusDatum {i j : Fin n} (hij : cartanD n i j = 0) :
    Commutes (rankOne (plusDatum n K hn3).rootGroup i) (rankOne (plusDatum n K hn3).rootGroup j) :=
  commutes_rankOne_of_cartan_eq_zero (plusDatum n K hn3) (plusDatum_steinbergExtras hn3)
    (lenSq_roots_plusDatum hn3 ⟨0, by omega⟩) hij

@[expose] noncomputable def rootθD (n : ℕ) (K : Type) [Field K] (hn3 : 3 ≤ n) : Subgroup (spinGroup (quadPlus n K)) :=
  (plusDatum n K hn3).rootGroup (thetaD n) ⊔ (plusDatum n K hn3).rootGroup (-thetaD n)

theorem thetaD_mem_roots' (hn : 4 ≤ n) : thetaD n ∈ (plusDatum n K hn3).roots := by
  rw [plusDatum_roots hn3]
  exact thetaD_mem_roots hn

theorem commutes_rootθD_rankOne (hn : 4 ≤ n) {k : Fin n} (hk : k.val ≠ 1) :
    Commutes (rootθD n K hn3) (rankOne (plusDatum n K hn3).rootGroup k) := by
  have hsingle : (Pi.single k 1 : Fin n → ℤ) ∈ (plusDatum n K hn3).roots :=
    single_mem_roots (plusDatum n K hn3) k
  have hθ := thetaD_mem_roots' (K := K) hn3 hn
  have horth := form_toRat_single_eq_zero (plusDatum n K hn3) k (thetaD n) (coroot_thetaD hn hk)
  exact commutes_fund_of_orthogonal (plusDatum n K hn3) (plusDatum_steinbergExtras hn3)
    (lenSq_roots_plusDatum hn3 ⟨0, by omega⟩) hθ hsingle horth

end Orthogonality

section StandardPairs

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld.LevisSpin

theorem standardPair_plusDatum_edge {F : Type} [Field F] [Finite F] {n : ℕ} (hn3 : 3 ≤ n)
    {i j : Fin n} (h : edgeD n i j) :
    ∃ W, LinearBlockStandardPair F W (rankOne (plusDatum n F hn3).rootGroup i)
      (rankOne (plusDatum n F hn3).rootGroup j) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (plusDatum n F hn3).isFiniteType
    (Dv := (plusDatum n F hn3).divisible) rfl
  have hE := SpinPlus.chevalleyExtras hn3 O SpinPlus.commC (SpinPlus.commutatorFormula hn3 O)
  obtain ⟨k, hki, hkj, hk⟩ := edgeD_neighbour hn3 h
  obtain ⟨hij, hji⟩ := cartanD_of_edgeD h
  have hne : i ≠ j := fun e => by
    subst e
    unfold edgeD at h
    omega
  refine (CFSG.ClassicalInvolution.ModelFacts.standardPair_of_chevalleyExtras hE rfl (k := k) hne
    hij hji ?_).2
  show ¬ (3 : ℤ) ∣ cartanD n i k + 2 * cartanD n j k
  rcases hk with ⟨hjk, hik, hki'⟩ | ⟨hik, hjk, hkj'⟩
  · have h1 : cartanD n j k = -1 := by
      rcases hjk with e | e
      · exact (cartanD_of_edgeD e).1
      · exact (cartanD_of_edgeD e).2
    have h2 : cartanD n i k = 0 :=
      (cartanD_of_not_edgeD (Ne.symm hki) hik hki').1
    rw [h1, h2]
    omega
  · have h1 : cartanD n i k = -1 := by
      rcases hik with e | e
      · exact (cartanD_of_edgeD e).1
      · exact (cartanD_of_edgeD e).2
    have h2 : cartanD n j k = 0 :=
      (cartanD_of_not_edgeD (Ne.symm hkj) hjk hkj').1
    rw [h1, h2]
    omega

end StandardPairs

section Theta

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinPlus)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

@[expose] def zeroD {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨0, by omega⟩

@[simp] theorem zeroD_val {n : ℕ} (hn : 1 ≤ n) : (zeroD hn).val = 0 := rfl

@[expose] def nodeD {n : ℕ} (hn : 2 ≤ n) (k : Fin (n - 2)) : Fin n := ⟨k.val + 2, by have := k.isLt; omega⟩

theorem edgeD_shift {n : ℕ} (hn : 2 ≤ n) {i j : Fin (n - 2)} :
    edgeD (n - 2) i j ↔ edgeD n (nodeD hn i) (nodeD hn j) := by
  unfold edgeD nodeD
  have := i.isLt
  have := j.isLt
  simp only
  omega

theorem exists_theta_plusDatum {p f : ℕ} {n : ℕ} (hn : 6 ≤ n) {F : Type} [Field F] [Finite F]
    (hadm : StatedLieAdmissible .POmegaPlus (n - 2) p f) (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) :
    ∃ Θ : spinGroup (quadPlus (n - 2) F) →* spinGroup (quadPlus n F),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (n - 2), (rankOne (plusDatum (n - 2) F (by omega)).rootGroup k).map Θ =
        rankOne (plusDatum n F (by omega)).rootGroup (nodeD (n := n) (by omega) k)) ∧
      Θ.range = ⨆ k : Fin (n - 2), rankOne (plusDatum n F (by omega)).rootGroup (nodeD (n := n) (by omega) k) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set L : Fin (n - 2) → Subgroup (spinGroup (quadPlus n F)) := fun k =>
    rankOne (plusDatum n F hn3).rootGroup (nodeD (n := n) (by omega) k) with hL
  set X : Subgroup (spinGroup (quadPlus n F)) := ⨆ k, L k with hX
  have hLle : ∀ k, L k ≤ X := fun k => le_iSup L k
  obtain ⟨Ψ, hsurj, hker, -, -, -, hnodes⟩ := weakCT_spinPlus (n := n - 2) (p := p) (f := f) hadm
    hn3' hF hq (X := ↥X) (fun k => (L k).subgroupOf X) (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self L)
    (fun i j hij h1 h2 a ha b hb => by
      have hc : cartanD n (nodeD (n := n) (by omega) i) (nodeD (n := n) (by omega) j) = 0 := by
        refine (CFSG.Timmesfeld.LevisSpin.cartanD_of_not_edgeD ?_ ?_ ?_).1
        · intro e; exact hij (Fin.ext (by have := congrArg Fin.val e; simp only [nodeD] at this; omega))
        · exact fun e => h1 ((edgeD_shift (by omega)).mpr e)
        · exact fun e => h2 ((edgeD_shift (by omega)).mpr e)
      exact Subtype.ext (commutes_rankOne_plusDatum hn3 hc a.1 (Subgroup.mem_subgroupOf.mp ha) b.1
        (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 ((edgeD_shift (by omega)).mp hij)
      have hWle : W ≤ X :=
        (linearBlockStandardPair_le_sup hW).trans (sup_le (hLle i) (hLle j))
      exact ⟨W.subgroupOf X, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf hWle
        hW⟩)
  refine ⟨X.subtype.comp Ψ, ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · intro k
    rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hLle k)]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

end Theta

section Assembly

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {K : Type} [Field K] {n : ℕ}

theorem isLongestRoot_of_mem_roots_plusDatum (hn3 : 3 ≤ n) {γ : Fin n → ℤ}
    (hγ : γ ∈ (plusDatum n K hn3).roots) :
    CFSG.ClassicalInvolution.Generic.IsLongestRoot (plusDatum n K hn3) γ := by
  refine ⟨hγ, fun δ hδ => ?_⟩
  have h1 := lenSq_roots_plusDatum hn3 ⟨0, by omega⟩ δ hδ
  have h2 := lenSq_roots_plusDatum hn3 ⟨0, by omega⟩ γ hγ
  exact (h1.trans h2.symm).le

theorem rankOne_mem_fundamentalSubgroups_plusDatum (hn3 : 3 ≤ n) (i : Fin n) :
    rankOne (plusDatum n K hn3).rootGroup i ∈ fundamentalSubgroups .POmegaPlus (plusDatum n K hn3) := by
  have hi : (Pi.single i 1 : Fin n → ℤ) ∈ (plusDatum n K hn3).roots :=
    single_mem_roots (plusDatum n K hn3) i
  exact ⟨1, Pi.single i 1, Or.inl (isLongestRoot_of_mem_roots_plusDatum hn3 hi), by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_one]; rfl⟩

theorem rootθD_mem_fundamentalSubgroups (hn3 : 3 ≤ n) (hn : 4 ≤ n) :
    rootθD n K hn3 ∈ fundamentalSubgroups .POmegaPlus (plusDatum n K hn3) :=
  ⟨1, thetaD n, Or.inl (isLongestRoot_of_mem_roots_plusDatum hn3 (thetaD_mem_roots' hn3 hn)), by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_one]; rfl⟩

end Assembly

section ExtModel

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal (LieUniversal)

variable {p f : ℕ} [hp : Fact p.Prime]

theorem nonempty_extModelU_plus {n : ℕ} (hn : 6 ≤ n)
    (hscT : FundamentalSingleClass .POmegaPlus
      (plusDatum n (GaloisField p f) (by omega)))
    (hscY : FundamentalSingleClass .POmegaPlus
      (plusDatum (n - 2) (GaloisField p f) (by omega)))
    (hadmY : StatedLieAdmissible .POmegaPlus (n - 2) p f) (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModelU .POmegaPlus .POmegaPlus
      ⟨spinGroup (quadPlus n (GaloisField p f)), plusDatum n (GaloisField p f) (by omega)⟩
      ⟨spinGroup (quadPlus (n - 2) (GaloisField p f)),
        plusDatum (n - 2) (GaloisField p f) (by omega)⟩ 2) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set F := GaloisField p f with hFdef
  let n0 : Fin n := zeroD (by omega)
  have hf : f ≠ 0 := by have := hadmY.2.1; omega
  have hF : Nat.card F = p ^ f := GaloisField.card p f hf
  have hq' : 4 ≤ Nat.card F := hF ▸ hq
  obtain ⟨Θ, hker, hnode, hrange⟩ := exists_theta_plusDatum (p := p) (f := f) (n := n) hn
    (F := F) hadmY hF hq'
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
    · intro e; have := congrArg Fin.val e; simp only [nodeD, n0, zeroD_val] at this; omega
    · intro e; unfold edgeD at e; simp only [nodeD, n0, zeroD_val] at e; omega
    · intro e; unfold edgeD at e; simp only [nodeD, n0, zeroD_val] at e; have := k.isLt; omega
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
    perf_T := ?_
    perf_Y := ?_ }⟩
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    exact conjSub_mem_fundamentalSubgroups (rankOne_mem_fundamentalSubgroups_plusDatum hn3 _) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
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
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2 := hcommX0 n0'
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2
    rwa [h1] at h3
  · have h01 : edgeD n n0 (⟨1, by omega⟩ : Fin n) := by
      unfold edgeD
      left
      refine ⟨rfl, ?_⟩
      show 1 + 1 < n
      omega
    obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3 h01
    exact perfect_of_mem_fundamental hscT (rankOne_mem_fundamentalSubgroups_plusDatum hn3 n0)
      (linearBlockStandardPair_perfect hq' hW).1
  · have h01 : edgeD (n - 2) n0' (⟨1, by omega⟩ : Fin (n - 2)) := by
      unfold edgeD
      left
      refine ⟨rfl, ?_⟩
      show 1 + 1 < n - 2
      omega
    obtain ⟨W, hW⟩ := standardPair_plusDatum_edge (F := F) hn3' h01
    exact perfect_of_mem_fundamental hscY (rankOne_mem_fundamentalSubgroups_plusDatum hn3' n0')
      (linearBlockStandardPair_perfect hq' hW).1

end ExtModel

end CFSG.ClassicalInvolution.RouteD
