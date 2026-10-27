module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinSp
public import CFSG.ClassicalInvolution.RouteD.TypeARecognition
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
public import CFSG.ClassicalInvolution.WeakCT.SpinOdd

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open CFSG.ClassicalInvolution.ModelFacts (lenSq lenSq_single)

section Roots

variable {n : ℕ}

@[expose] def thetaB (n : ℕ) : Fin n → ℤ := fun i => if i.val = 0 then 1 else 2

theorem toStdB_thetaB (hn : 2 ≤ n) :
    toStdB n (thetaB n) =
      Pi.single (⟨0, by omega⟩ : Fin n) 1 + Pi.single (⟨1, by omega⟩ : Fin n) 1 := by
  funext a
  simp only [toStdB, thetaB, Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem thetaB_mem_roots (hn : 2 ≤ n) : thetaB n ∈ roots (isFiniteType_cartanB n) ∅ := by
  have h := ofStdB_mem_rootsB (n := n)
    (e := Pi.single (⟨0, by omega⟩ : Fin n) 1 + Pi.single (⟨1, by omega⟩ : Fin n) 1)
    (Or.inl ⟨⟨0, by omega⟩, ⟨1, by omega⟩, 1, 1, Fin.ne_of_val_ne (by simp), Or.inl rfl,
      Or.inl rfl, rfl⟩)
  have e : thetaB n = ofStdB n (Pi.single (⟨0, by omega⟩ : Fin n) 1 +
      Pi.single (⟨1, by omega⟩ : Fin n) 1) := (toStdB_eq_iff n _ _).mp (toStdB_thetaB hn)
  rwa [e]

theorem coroot_thetaB (hn : 3 ≤ n) {k : Fin n} (hk : k.val ≠ 1) :
    coroot (cartanB n) k (thetaB n) = 0 := by
  by_cases h : k.val + 1 < n
  · rw [coroot_cartanB_of_lt n h, toStdB_thetaB (by omega)]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | omega | (exfalso; assumption)
  · have hk' := k.isLt
    rw [coroot_cartanB_of_not_lt n h, toStdB_thetaB (by omega)]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem coroot_thetaB_one (hn : 3 ≤ n) :
    coroot (cartanB n) (⟨1, by omega⟩ : Fin n) (thetaB n) = 1 := by
  rw [coroot_cartanB_of_lt n (by simp only; omega), toStdB_thetaB (by omega)]
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

end Roots

section Datum

variable {n : ℕ} {K : Type} [Field K]

theorem cartanB_eq_zero_of_far {i j : Fin n} (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    cartanB n i j = 0 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem lenSq_le_oddDatum (hn : 3 ≤ n) {i : Fin n} (hi : i.val + 1 < n) :
    ∀ ε ∈ (oddDatum n K).roots, lenSq (oddDatum n K).isFiniteType ε ≤
      lenSq (oddDatum n K).isFiniteType (Pi.single i 1) := by
  have h := CFSG.ClassicalInvolution.ModelFacts.isLongest_single_cartanB (m := n) (by omega) rfl
    (oddDatum n K).isFiniteType hi
  intro ε hε
  exact h.2 ε hε

theorem commutes_rankOne_oddDatum (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) {i j : Fin n}
    (hij : cartanB n i j = 0) :
    Commutes (rankOne (oddDatum n K).rootGroup i) (rankOne (oddDatum n K).rootGroup j) := by
  by_cases hi : i.val + 1 < n
  · exact commutes_rankOne_of_cartan_eq_zero_of_longest (oddDatum n K) (oddDatum_steinbergExtras h2)
      (lenSq_le_oddDatum hn hi) hij
  · have hj : j.val + 1 < n := by
      have := j.isLt
      have := i.isLt
      by_contra hj
      have hne : i = j := Fin.ext (by omega)
      subst hne
      simp [cartanB] at hij
    have hji : cartanB n j i = 0 := by
      simp only [cartanB, Matrix.of_apply] at hij ⊢
      split_ifs at hij ⊢ <;> omega
    exact (commutes_rankOne_of_cartan_eq_zero_of_longest (oddDatum n K) (oddDatum_steinbergExtras h2)
      (lenSq_le_oddDatum hn hj) hji).symm

end Datum

section Theta

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def rootθB (n : ℕ) (K : Type) [Field K] : Subgroup (spinGroup (quadOdd n K)) :=
  (oddDatum n K).rootGroup (thetaB n) ⊔ (oddDatum n K).rootGroup (-thetaB n)

theorem thetaB_mem_roots' (hn : 3 ≤ n) : thetaB n ∈ (oddDatum n K).roots := by
  rw [oddDatum_roots]
  exact thetaB_mem_roots (by omega)

theorem lenSq_thetaB (hn : 3 ≤ n) :
    lenSq (oddDatum n K).isFiniteType (thetaB n) =
      lenSq (oddDatum n K).isFiniteType (Pi.single (⟨1, by omega⟩ : Fin n) 1) :=
  lenSq_eq_lenSq_single_of_coroot (oddDatum n K) (thetaB n) ⟨1, by show 1 < n; omega⟩
    (by simp [thetaB])
    (coroot_thetaB_one hn) (fun l hl => coroot_thetaB hn (fun h => hl (Fin.ext h)))

theorem lenSq_le_thetaB (hn : 3 ≤ n) :
    ∀ ε ∈ (oddDatum n K).roots, lenSq (oddDatum n K).isFiniteType ε ≤
      lenSq (oddDatum n K).isFiniteType (thetaB n) := by
  intro ε hε
  rw [lenSq_thetaB hn]
  exact lenSq_le_oddDatum hn (i := ⟨1, by omega⟩) (by simp only; omega) ε hε

theorem commutes_rootθB_rankOne (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) {k : Fin n} (hk : k.val ≠ 1) :
    Commutes (rootθB n K) (rankOne (oddDatum n K).rootGroup k) := by
  have hsingle : (Pi.single k 1 : Fin n → ℤ) ∈ (oddDatum n K).roots :=
    single_mem_roots (oddDatum n K) k
  have horth := form_toRat_single_eq_zero (oddDatum n K) k (thetaB n) (coroot_thetaB hn hk)
  exact commutes_fund_of_orthogonal_of_longest (oddDatum n K) (oddDatum_steinbergExtras h2)
    (thetaB_mem_roots' hn) hsingle (lenSq_le_thetaB hn) horth

end Theta

section StandardPairs

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)

theorem standardPair_oddDatum_edge {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 3 ≤ n) {i : ℕ}
    (hi : i + 2 < n) :
    ∃ W, LinearBlockStandardPair F W
      (rankOne (oddDatum n F).rootGroup (⟨i, by show i < n; omega⟩ : Fin (oddDatum n F).rank))
      (rankOne (oddDatum n F).rootGroup (⟨i + 1, by show i + 1 < n; omega⟩ :
        Fin (oddDatum n F).rank)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n F).isFiniteType
    (Dv := (oddDatum n F).divisible) rfl
  have hE := SpinOdd.chevalleyExtras (by omega : 2 ≤ n) O SpinOdd.commC
    (SpinOdd.commutatorFormula O)
  refine (CFSG.ClassicalInvolution.ModelFacts.standardPair_of_chevalleyExtras hE rfl
    (k := ⟨i + 2, by show i + 2 < n; omega⟩) ?_ ?_ ?_ ?_).2
  · intro h
    have := congrArg Fin.val h
    simp at this
  · show cartanB n ⟨i, by omega⟩ ⟨i + 1, by omega⟩ = -1
    simp [cartanB, Fin.ext_iff]
    omega
  · show cartanB n ⟨i + 1, by omega⟩ ⟨i, by omega⟩ = -1
    simp [cartanB, Fin.ext_iff]
    omega
  · show ¬ (3 : ℤ) ∣ cartanB n ⟨i, by omega⟩ ⟨i + 2, by omega⟩ +
      2 * cartanB n ⟨i + 1, by omega⟩ ⟨i + 2, by omega⟩
    simp [cartanB, Fin.ext_iff]
    omega

theorem symplecticPair_oddDatum {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 3 ≤ n) :
    ∃ W, SymplecticBlockStandardPair F W
      (rankOne (oddDatum n F).rootGroup
        (⟨n - 2, by show n - 2 < n; omega⟩ : Fin (oddDatum n F).rank))
      (rankOne (oddDatum n F).rootGroup
        (⟨n - 1, by show n - 1 < n; omega⟩ : Fin (oddDatum n F).rank)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (oddDatum n F).isFiniteType
    (Dv := (oddDatum n F).divisible) rfl
  have hE := SpinOdd.chevalleyExtras (by omega : 2 ≤ n) O SpinOdd.commC
    (SpinOdd.commutatorFormula O)
  exact exists_symplecticBlockStandardPair_rankOne hF h2 hE rfl
    (i := ⟨n - 1, by show n - 1 < n; omega⟩) (j := ⟨n - 2, by show n - 2 < n; omega⟩)
    (by show cartanB n ⟨n - 1, by omega⟩ ⟨n - 2, by omega⟩ = -2
        simp [cartanB, Fin.ext_iff]
        omega)
    (by show cartanB n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = -1
        simp [cartanB, Fin.ext_iff]
        omega)

end StandardPairs

section Theta2

open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair weakCT_spinOdd)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_subgroupOf symplecticBlockStandardPair_le_sup)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

@[expose] def zeroB {n : ℕ} (hn : 1 ≤ n) : Fin n := ⟨0, by omega⟩

@[simp] theorem zeroB_val {n : ℕ} (hn : 1 ≤ n) : (zeroB hn).val = 0 := rfl

@[expose] def nodeB {n : ℕ} (hn : 2 ≤ n) (k : Fin (n - 2)) : Fin n :=
  ⟨k.val + 2, by have := k.isLt; omega⟩

theorem exists_theta_oddDatum {p f : ℕ} {n : ℕ} (hn : 5 ≤ n) {F : Type} [Field F] [Finite F]
    (hadm : StatedLieAdmissible .POmegaOdd (n - 2) p f) (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0) :
    ∃ Θ : spinGroup (quadOdd (n - 2) F) →* spinGroup (quadOdd n F),
      Θ.ker ≤ Subgroup.center _ ∧
      (∀ k : Fin (n - 2), (rankOne (oddDatum (n - 2) F).rootGroup k).map Θ =
        rankOne (oddDatum n F).rootGroup (nodeB (n := n) (by omega) k)) ∧
      Θ.range = ⨆ k : Fin (n - 2),
        rankOne (oddDatum n F).rootGroup (nodeB (n := n) (by omega) k) := by
  have hn3 : 3 ≤ n := by omega
  set L : Fin (n - 2) → Subgroup (spinGroup (quadOdd n F)) := fun k =>
    rankOne (oddDatum n F).rootGroup (nodeB (n := n) (by omega) k) with hL
  set X : Subgroup (spinGroup (quadOdd n F)) := ⨆ k, L k with hX
  have hLle : ∀ k, L k ≤ X := fun k => le_iSup L k
  obtain ⟨Ψ, hsurj, hker, -, -, -, hnodes⟩ := weakCT_spinOdd (n := n - 2) (p := p) (f := f) hadm hF
    hq (X := ↥X) (fun k => (L k).subgroupOf X)
    (CFSG.ClassicalInvolution.Generic.iSup_subgroupOf_self L)
    (fun i j hij a ha b hb => by
      have hc : cartanB n (nodeB (n := n) (by omega) i) (nodeB (n := n) (by omega) j) = 0 := by
        have := i.isLt
        have := j.isLt
        simp only [cartanB, nodeB, Matrix.of_apply, Fin.ext_iff]
        split_ifs <;> omega
      exact Subtype.ext (commutes_rankOne_oddDatum hn3 h2 hc a.1 (Subgroup.mem_subgroupOf.mp ha)
        b.1 (Subgroup.mem_subgroupOf.mp hb)))
    (fun i j hij hj => by
      have hi' := i.isLt
      have hj'' := j.isLt
      obtain ⟨W, hW⟩ := standardPair_oddDatum_edge (F := F) hn3 (i := i.val + 2) (by omega)
      have hLi : L i = rankOne (oddDatum n F).rootGroup
          (⟨i.val + 2, by show i.val + 2 < n; omega⟩ : Fin (oddDatum n F).rank) := rfl
      have hLj : L j = rankOne (oddDatum n F).rootGroup
          (⟨i.val + 2 + 1, by show i.val + 2 + 1 < n; omega⟩ : Fin (oddDatum n F).rank) := by
        show rankOne _ (nodeB _ j) = _
        congr 1
        exact Fin.ext (by simp only [nodeB]; omega)
      have hWle : W ≤ X := by
        refine (linearBlockStandardPair_le_sup hW).trans (sup_le ?_ ?_)
        · rw [← hLi]; exact hLle i
        · rw [← hLj]; exact hLle j
      rw [hLi, hLj]
      exact ⟨W.subgroupOf X, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_subgroupOf
        hWle hW⟩)
    (fun i j hi hj => by
      have hi' := i.isLt
      have hj'' := j.isLt
      obtain ⟨W, hW⟩ := symplecticPair_oddDatum (F := F) hq h2 hn3
      have hLi : L i = rankOne (oddDatum n F).rootGroup
          (⟨n - 2, by show n - 2 < n; omega⟩ : Fin (oddDatum n F).rank) := by
        show rankOne _ (nodeB _ i) = _
        congr 1
        exact Fin.ext (by simp only [nodeB]; omega)
      have hLj : L j = rankOne (oddDatum n F).rootGroup
          (⟨n - 1, by show n - 1 < n; omega⟩ : Fin (oddDatum n F).rank) := by
        show rankOne _ (nodeB _ j) = _
        congr 1
        exact Fin.ext (by simp only [nodeB]; omega)
      have hWle : W ≤ X := by
        refine (symplecticBlockStandardPair_le_sup hW).trans (sup_le ?_ ?_)
        · rw [← hLi]; exact hLle i
        · rw [← hLj]; exact hLle j
      rw [hLi, hLj]
      exact ⟨W.subgroupOf X, symplecticBlockStandardPair_subgroupOf hWle hW⟩)
  refine ⟨X.subtype.comp Ψ, ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · intro k
    rw [← Subgroup.map_map, hnodes k, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hLle k)]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

end Theta2

section Assembly

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal (LieUniversal)

variable {K : Type} [Field K] {n : ℕ}

theorem rankOne_mem_fundamentalSubgroups_oddDatum (hn : 3 ≤ n) {i : Fin n} (hi : i.val + 1 < n) :
    rankOne (oddDatum n K).rootGroup i ∈ fundamentalSubgroups .POmegaOdd (oddDatum n K) := by
  have hmem : (Pi.single i 1 : Fin n → ℤ) ∈ (oddDatum n K).roots :=
    single_mem_roots (oddDatum n K) i
  exact ⟨1, Pi.single i 1, Or.inl ⟨hmem, fun δ hδ => lenSq_le_oddDatum hn hi δ hδ⟩, by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_one]; rfl⟩

theorem rootθB_mem_fundamentalSubgroups (hn : 3 ≤ n) :
    rootθB n K ∈ fundamentalSubgroups .POmegaOdd (oddDatum n K) :=
  ⟨1, thetaB n, Or.inl ⟨thetaB_mem_roots' hn, fun δ hδ => lenSq_le_thetaB hn δ hδ⟩, by
    rw [CFSG.ClassicalInvolution.Generic.conjSub_one]; rfl⟩

end Assembly

section ExtModel

open CFSG.ClassicalInvolution.Generic (fundamentalSubgroups FundamentalSingleClass)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal (LieUniversal)

variable {p f : ℕ} [hp : Fact p.Prime]

theorem nonempty_extModelU_odd {n : ℕ} (hn : 5 ≤ n) (h2 : (2 : GaloisField p f) ≠ 0)
    (hscT : FundamentalSingleClass .POmegaOdd (oddDatum n (GaloisField p f)))
    (hscY : FundamentalSingleClass .POmegaOdd (oddDatum (n - 2) (GaloisField p f)))
    (hadmY : StatedLieAdmissible .POmegaOdd (n - 2) p f) (hq : 4 ≤ p ^ f) :
    Nonempty (ExtModelU .POmegaOdd .POmegaOdd
      ⟨spinGroup (quadOdd n (GaloisField p f)), oddDatum n (GaloisField p f)⟩
      ⟨spinGroup (quadOdd (n - 2) (GaloisField p f)), oddDatum (n - 2) (GaloisField p f)⟩ 2) := by
  have hn3 : 3 ≤ n := by omega
  have hn3' : 3 ≤ n - 2 := by omega
  set F := GaloisField p f with hFdef
  have hf : f ≠ 0 := by have := hadmY.2.1; omega
  have hF : Nat.card F = p ^ f := GaloisField.card p f hf
  have hq' : 4 ≤ Nat.card F := hF ▸ hq
  obtain ⟨Θ, hker, hnode, hrange⟩ := exists_theta_oddDatum (p := p) (f := f) (n := n) hn
    (F := F) hadmY hF hq' h2
  let n0 : Fin n := zeroB (by omega)
  let n0' : Fin (n - 2) := zeroB (by omega)
  set DT := oddDatum n F with hDT
  set DY := oddDatum (n - 2) F with hDY
  set X : Subgroup (spinGroup (quadOdd n F)) :=
    ⨆ k : Fin (n - 2), rankOne DT.rootGroup (nodeB (n := n) (by omega) k) with hX
  have hlong0 : n0.val + 1 < n := by simp only [n0, zeroB_val]; omega
  have hcommX0 : ∀ k : Fin (n - 2),
      Commutes (rankOne DT.rootGroup n0) (rankOne DT.rootGroup (nodeB (n := n) (by omega) k)) := by
    intro k
    refine commutes_rankOne_oddDatum hn3 h2 (cartanB_eq_zero_of_far ?_)
    simp only [nodeB, n0, zeroB_val]
    omega
  have hcommXθ : Commutes X (rootθB n F) := by
    refine commutes_iSup_left.mpr fun k => ?_
    exact (commutes_rootθB_rankOne hn3 h2 (k := nodeB (n := n) (by omega) k)
      (by simp only [nodeB]; omega)).symm
  have hcommX0' : Commutes X (rankOne DT.rootGroup n0) :=
    commutes_iSup_left.mpr fun k => (hcommX0 k).symm
  have himg : ∀ R ∈ fundamentalSubgroups .POmegaOdd DY, ∃ g : spinGroup (quadOdd (n - 2) F),
      R.map Θ = conjSub (Θ g) (rankOne DT.rootGroup (nodeB (n := n) (by omega) n0')) := by
    intro R hR
    obtain ⟨g, hg⟩ := hscY (rankOne DY.rootGroup n0')
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3' (by simp only [n0', zeroB_val]; omega)) R hR
    refine ⟨g, ?_⟩
    rw [hg, ← CFSG.ClassicalInvolution.Generic.conjSub_map, hnode]
  have h02 : (nodeB (n := n) (by omega) n0').val ≠ 1 := by simp only [nodeB, n0', zeroB_val]; omega
  refine ⟨{
    Rθ := rootθB n F
    twin := fun _ => rankOne DT.rootGroup n0
    Θ := Θ
    Rθ_mem := rootθB_mem_fundamentalSubgroups hn3
    twin_mem := fun _ => rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0
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
    exact conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3 (i := nodeB (n := n) (by omega) n0')
        (by simp only [nodeB, n0', zeroB_val]; omega)) _
  · intro R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 : conjSub (Θ g) (rootθB n F) = rootθB n F :=
      CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommXθ
    have h2' : Commutes (rankOne DT.rootGroup (nodeB (n := n) (by omega) n0')) (rootθB n F) :=
      (commutes_rootθB_rankOne hn3 h2 (k := nodeB (n := n) (by omega) n0') h02).symm
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3
  · intro i
    exact (commutes_rootθB_rankOne hn3 h2 (k := n0) (by simp [n0])).symm
  · intro i R hR
    obtain ⟨g, hg⟩ := himg R hR
    rw [hg]
    have hgX : Θ g ∈ X := by rw [← hrange]; exact ⟨g, rfl⟩
    have h1 := CFSG.ClassicalInvolution.Generic.conjSub_eq_of_mem_of_commutes hgX hcommX0'
    have h2' := hcommX0 n0'
    have h3 := (CFSG.ClassicalInvolution.Generic.commutes_conjSub_iff (Θ g)).mpr h2'
    rwa [h1] at h3
  · obtain ⟨W, hW⟩ := standardPair_oddDatum_edge (F := F) hn3 (i := 0) (by omega)
    exact perfect_of_mem_fundamental hscT (rankOne_mem_fundamentalSubgroups_oddDatum hn3 hlong0)
      (linearBlockStandardPair_perfect hq' hW).1
  · obtain ⟨W, hW⟩ := standardPair_oddDatum_edge (F := F) hn3' (i := 0) (by omega)
    exact perfect_of_mem_fundamental hscY
      (rankOne_mem_fundamentalSubgroups_oddDatum hn3' (by show 0 + 1 < n - 2; omega))
      (linearBlockStandardPair_perfect hq' hW).1

end ExtModel

end CFSG.ClassicalInvolution.RouteD
