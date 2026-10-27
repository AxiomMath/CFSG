module

public import CFSG.LieType.Universal.Unitary.BinaryModel.FixedLine
public import CFSG.LieType.Universal.Unitary.BinaryModel.TypeLabel
public import CFSG.LieType.SpecialLinear.ExteriorModel.Weights
public import CFSG.Quasithin.Background.SmithCurtisMain
public import CFSG.LieType.Steinberg.CurtisDatum.RankOne
public import CFSG.LieType.Universal.Unitary.CurtisDatum.TorusSums
public import CFSG.LieType.RootSystem.Form
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.Open.QuasithinDefs
public import Lean.Elab.Tactic.Omega

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.SpecialLinear.ExteriorModel CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LieType.RootSystem

variable {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2] {k : Type} [Field k] [CharP k 2]
  {n : ℕ}

theorem upIdx_lt (n : ℕ) (s : Fin (n / 2)) : (s : ℕ) + 1 < n := by
  have h1 : (s : ℕ) + 1 ≤ n / 2 := Nat.succ_le_of_lt s.isLt
  have h2 : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
  omega

theorem downIdx_lt (n : ℕ) (s : Fin (n / 2)) : n - 1 - (s : ℕ) < n := by
  have h1 : (s : ℕ) + 1 < n := upIdx_lt n s
  omega

theorem node_val_lt (n : ℕ) (s : Fin (n / 2)) : (s : ℕ) < n := by
  have h1 : (s : ℕ) + 1 < n := upIdx_lt n s
  omega

abbrev upIdx {n : ℕ} (s : Fin (n / 2)) : Fin n := ⟨(s : ℕ) + 1, upIdx_lt n s⟩

abbrev downIdx {n : ℕ} (s : Fin (n / 2)) : Fin n := ⟨n - 1 - (s : ℕ), downIdx_lt n s⟩

omit [Finite F] [CharP k 2] in
theorem suFrob_prod_btop_eq (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n))
    (d : Fin n → F) :
    (∏ p : Fin f × Fin n,
        ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
          suFrob φ₀ f p.1 (d a)) = φ₀ (∏ a, d a ^ bExp ε a) := by
  classical
  have hS : ∀ p : Fin f × Fin n,
      ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)) =
        Finset.univ.filter (fun a : Fin n => (a : ℕ) < bdeg ε p) := fun _ => rfl
  have hstep : ∀ p : Fin f × Fin n,
      (∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
        suFrob φ₀ f p.1 (d a)) =
        ∏ a : Fin n, if (a : ℕ) < bdeg ε p then suFrob φ₀ f p.1 (d a) else 1 := by
    intro p
    rw [hS p, Finset.prod_filter]
  rw [Finset.prod_congr rfl fun p _ => hstep p]
  rw [Fintype.prod_prod_type]
  have hfilter : ∀ (r : Fin f) (a : Fin n),
      (Finset.univ.filter (fun j : Fin n => (a : ℕ) < bdeg ε (r, j))) =
        (ε r).filter (fun j => a < j) := by
    intro r a
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bdeg, Fin.lt_def]
    by_cases hj : j ∈ ε r
    · simp [hj]
    · simp only [hj, if_false, false_and, iff_false]
      intro h
      omega
  have hinner : ∀ r : Fin f,
      (∏ j : Fin n, ∏ a : Fin n,
        if (a : ℕ) < bdeg ε (r, j) then suFrob φ₀ f r (d a) else 1) =
        ∏ a : Fin n, suFrob φ₀ f r (d a) ^ ((ε r).filter (fun j => a < j)).card := by
    intro r
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← hfilter r a, ← Finset.prod_filter, Finset.prod_const]
  rw [Finset.prod_congr rfl fun r _ => hinner r]
  rw [Finset.prod_comm]
  have hinner2 : ∀ a : Fin n,
      (∏ r : Fin f, suFrob φ₀ f r (d a) ^ ((ε r).filter (fun j => a < j)).card) =
        φ₀ (d a) ^ bExp ε a := by
    intro a
    have hp : ∀ r : Fin f, suFrob φ₀ f r (d a) ^ ((ε r).filter (fun j => a < j)).card =
        φ₀ (d a) ^ (2 ^ (r : ℕ) * ((ε r).filter (fun j => a < j)).card) := by
      intro r
      rw [suFrob_apply, ← pow_mul]
    rw [Finset.prod_congr rfl fun r _ => hp r, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [Finset.prod_congr rfl fun a _ => hinner2 a]
  simp only [← map_pow, ← map_prod]

theorem signedPerm_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (φ : R →+* S)
    (π : Equiv.Perm (Fin m)) (e : Fin m → R) :
    (CFSG.LieType.Universal.SpecialLinear.signedPerm π e).map φ =
      CFSG.LieType.Universal.SpecialLinear.signedPerm π (fun a => φ (e a)) := by
  ext r s
  rw [Matrix.map_apply, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply,
    CFSG.LieType.Universal.SpecialLinear.signedPerm_apply]
  by_cases h : r = π s <;> simp [h]

omit [CharP k 2] in
theorem signedPerm_eq_permMatrix_mul_diagonal {m : ℕ} (π : Equiv.Perm (Fin m))
    (e : Fin m → k) :
    CFSG.LieType.Universal.SpecialLinear.signedPerm π e =
      (π⁻¹).permMatrix k * Matrix.diagonal e := by
  ext r s
  rw [Matrix.mul_diagonal, CFSG.LieType.Universal.SpecialLinear.signedPerm_apply]
  have hπ : (π⁻¹).permMatrix k r s = if r = π s then 1 else 0 := by
    rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_some_iff]
    refine if_congr ?_ rfl rfl
    change (π.symm r = s) ↔ (r = π s)
    rw [Equiv.symm_apply_eq]
  rw [hπ]
  by_cases h : r = π s <;> simp [h]

theorem suRep_bTop_of_mem_U (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) {u : SU (unitaryInvolution F 2 f) n}
    (hu : u ∈ (curtisDatum hF n hn ζ hζ).U) :
    suRep φ₀ n ε u (bTop ε) = bTop ε := by
  classical
  obtain ⟨h0, h1⟩ := (mem_curtisDatum_U_iff hF n hn ζ hζ u).mp hu
  have hbase : ∀ (r : Fin f) (a b : Fin n), b < a →
      ((suTwist φ₀ f n u r : Matrix (Fin n) (Fin n) k)) a b = 0 := by
    intro r a b hba
    rw [coe_suTwist_apply]
    simp only [Matrix.map_apply, h0 a b hba, map_zero]
  have hdiag : ∀ (r : Fin f) (a : Fin n),
      ((suTwist φ₀ f n u r : Matrix (Fin n) (Fin n) k)) a a = 1 := by
    intro r a
    rw [coe_suTwist_apply]
    simp only [Matrix.map_apply, h1 a, map_one]
  have hfix : bMat ε (fun r => (suTwist φ₀ f n u r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε =
      bvec ε :=
    bMat_mulVec_bvec_of_unitriangular ε hbase hdiag
  show bRep ε (suTwist φ₀ f n u) (bTop ε) = bTop ε
  rw [bTop, bRep_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simpa using hfix

theorem suRep_bTop_of_mem_H (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) {h : SU (unitaryInvolution F 2 f) n}
    (hh : h ∈ (curtisDatum hF n hn ζ hζ).H) :
    suRep φ₀ n ε h (bTop ε) = chiEps φ₀ ε h • bTop ε := by
  classical
  have hH : (curtisDatum hF n hn ζ hζ).H =
      ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s := rfl
  have hdiag : h ∈ diagSubgroup (unitaryInvolution F 2 f) n := by
    rw [hH] at hh
    exact (iSup_le fun s => levelTorus_le_diagSubgroup (σ := unitaryInvolution F 2 f)
      (n := n) s) hh
  obtain ⟨d, hd⟩ := hdiag
  have hd' : SUExtras.mat (unitaryInvolution F 2 f) n h = diagonal d := hd
  have hmat : ∀ r : Fin f, (suTwist φ₀ f n h r : Matrix (Fin n) (Fin n) k) =
      diagonal (fun a => suFrob φ₀ f r (d a)) := by
    intro r
    rw [coe_suTwist_apply, hd', Matrix.diagonal_map (map_zero _)]
  have hval : bMat ε (fun r => (suTwist φ₀ f n h r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε =
      (∏ p : Fin f × Fin n,
        ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
          suFrob φ₀ f p.1 (d a)) • bvec ε := by
    rw [show (fun r => (suTwist φ₀ f n h r : Matrix (Fin n) (Fin n) k)) =
        (fun r => Matrix.diagonal (fun a => suFrob φ₀ f r (d a))) from funext hmat]
    exact bMat_diagonal_mulVec_bvec ε _
  have hchi : chiEps φ₀ ε h = φ₀ (∏ a, d a ^ bExp ε a) := by
    simp only [chiEps, hd', Matrix.diagonal_apply_eq]
  show bRep ε (suTwist φ₀ f n h) (bTop ε) = chiEps φ₀ ε h • bTop ε
  have hvec : (⟨bMat ε (fun r => (suTwist φ₀ f n h r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε,
        bMat_mulVec_mem_bCyc ε (suTwist φ₀ f n h) (bvec_mem_bCyc ε)⟩ : bCyc (k := k) ε) =
      ⟨chiEps φ₀ ε h • bvec ε,
        Submodule.smul_mem (p := bCyc (k := k) ε) (chiEps φ₀ ε h) (bvec_mem_bCyc ε)⟩ := by
    apply Subtype.ext
    change bMat ε (fun r => (suTwist φ₀ f n h r : Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε =
      chiEps φ₀ ε h • bvec ε
    rw [hval, suFrob_prod_btop_eq, ← hchi]
  rw [bTop, bRep_mk, hvec]
  change Submodule.Quotient.mk
      (chiEps φ₀ ε h • (⟨bvec ε, bvec_mem_bCyc ε⟩ : bCyc (k := k) ε)) =
    chiEps φ₀ ε h • Submodule.Quotient.mk (⟨bvec ε, bvec_mem_bCyc ε⟩ : bCyc (k := k) ε)
  rw [Submodule.Quotient.mk_smul]

theorem map_filter_lt_eq_iff {m : ℕ} (π : Equiv.Perm (Fin m)) (j : Fin m) :
    (Finset.univ.filter (fun a : Fin m => a < j)).map π.toEmbedding =
        Finset.univ.filter (fun a : Fin m => a < j) ↔
      ∀ a : Fin m, π a < j ↔ a < j := by
  constructor
  · intro h a
    have hmem := congrArg (fun s : Finset (Fin m) => π a ∈ s) h
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    constructor
    · intro hpa
      obtain ⟨b, hb, hba⟩ := hmem.mpr hpa
      rwa [π.injective hba] at hb
    · intro ha
      exact hmem.mp ⟨a, ha, rfl⟩
  · intro H
    ext b
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (H a).mpr ha
    · intro hb
      exact ⟨π.symm b, (H (π.symm b)).mp (by simpa using hb), by simp⟩

theorem levelPerm_lt_iff {n : ℕ} (s : Fin (n / 2)) (j : Fin n) :
    (∀ a : Fin n, levelPerm s a < j ↔ a < j) ↔ j ≠ upIdx s ∧ j ≠ downIdx s := by
  have hs : (s : ℕ) < n := node_val_lt n s
  by_cases h : s.val + 1 < n / 2
  · have hup : upIdx s = lowIdx ⟨s.val + 1, h⟩ := rfl
    have hdown : downIdx s = Fin.rev (lowIdx s) := by
      refine Fin.ext ?_
      simp only [Fin.val_rev, val_lowIdx]
      omega
    have e2 : lowIdx s ≠ Fin.rev (lowIdx s) := lowIdx_ne_rev s s
    have e3 : lowIdx s ≠ Fin.rev (lowIdx ⟨s.val + 1, h⟩) := lowIdx_ne_rev s _
    have e4 : lowIdx ⟨s.val + 1, h⟩ ≠ Fin.rev (lowIdx s) := lowIdx_ne_rev _ s
    have e5 : lowIdx ⟨s.val + 1, h⟩ ≠ Fin.rev (lowIdx ⟨s.val + 1, h⟩) := lowIdx_ne_rev _ _
    have hlt1 : lowIdx s < lowIdx ⟨s.val + 1, h⟩ := by
      rw [Fin.lt_def]; simp [lowIdx]
    have hlt2 : Fin.rev (lowIdx ⟨s.val + 1, h⟩) < Fin.rev (lowIdx s) := by
      rw [Fin.lt_def]; simp [lowIdx]; omega
    have hp1 : levelPerm s (lowIdx s) = lowIdx ⟨s.val + 1, h⟩ := by
      rw [levelPerm, dite_eq_left h, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne e2 e3, Equiv.swap_apply_left]
    have hp2 : levelPerm s (Fin.rev (lowIdx ⟨s.val + 1, h⟩)) = Fin.rev (lowIdx s) := by
      rw [levelPerm, dite_eq_left h, Equiv.Perm.mul_apply,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm e2) (Ne.symm e4)]
    rw [hup, hdown]
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · intro hj
        subst hj
        have hlt := (H (lowIdx s)).mpr hlt1
        rw [hp1] at hlt
        exact absurd hlt (lt_irrefl _)
      · intro hj
        subst hj
        have hlt := (H (Fin.rev (lowIdx ⟨s.val + 1, h⟩))).mpr hlt2
        rw [hp2] at hlt
        exact absurd hlt (lt_irrefl _)
    · rintro ⟨hj1, hj2⟩ a
      rw [levelPerm, dite_eq_left h, Equiv.Perm.mul_apply]
      by_cases ha1 : a = lowIdx s
      · subst ha1
        rw [Equiv.swap_apply_of_ne_of_ne e2 e3, Equiv.swap_apply_left, Fin.lt_def, Fin.lt_def]
        have hv : (lowIdx ⟨s.val + 1, h⟩ : ℕ) = (lowIdx s : ℕ) + 1 := by simp [lowIdx]
        have hjv : (j : ℕ) ≠ (lowIdx ⟨s.val + 1, h⟩ : ℕ) := fun hh => hj1 (Fin.ext hh)
        omega
      by_cases ha2 : a = lowIdx ⟨s.val + 1, h⟩
      · subst ha2
        rw [Equiv.swap_apply_of_ne_of_ne e4 e5, Equiv.swap_apply_right, Fin.lt_def, Fin.lt_def]
        have hv : (lowIdx ⟨s.val + 1, h⟩ : ℕ) = (lowIdx s : ℕ) + 1 := by simp [lowIdx]
        have hjv : (j : ℕ) ≠ (lowIdx ⟨s.val + 1, h⟩ : ℕ) := fun hh => hj1 (Fin.ext hh)
        omega
      by_cases ha3 : a = Fin.rev (lowIdx s)
      · subst ha3
        rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm e3) (Ne.symm e5),
          Fin.lt_def, Fin.lt_def]
        have hv : (Fin.rev (lowIdx s) : ℕ) = (Fin.rev (lowIdx ⟨s.val + 1, h⟩) : ℕ) + 1 := by
          simp [lowIdx]; omega
        have hjv : (j : ℕ) ≠ (Fin.rev (lowIdx s) : ℕ) := fun hh => hj2 (Fin.ext hh)
        omega
      by_cases ha4 : a = Fin.rev (lowIdx ⟨s.val + 1, h⟩)
      · subst ha4
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm e2) (Ne.symm e4),
          Fin.lt_def, Fin.lt_def]
        have hv : (Fin.rev (lowIdx s) : ℕ) = (Fin.rev (lowIdx ⟨s.val + 1, h⟩) : ℕ) + 1 := by
          simp [lowIdx]; omega
        have hjv : (j : ℕ) ≠ (Fin.rev (lowIdx s) : ℕ) := fun hh => hj2 (Fin.ext hh)
        omega
      have hinner : Equiv.swap (Fin.rev (lowIdx s)) (Fin.rev (lowIdx ⟨s.val + 1, h⟩)) a = a :=
        Equiv.swap_apply_of_ne_of_ne ha3 ha4
      rw [hinner, Equiv.swap_apply_of_ne_of_ne ha1 ha2]
  · have hb1_ge : (Fin.rev (lowIdx s) : ℕ) ≥ (lowIdx s : ℕ) + 1 := by
      simp only [Fin.val_rev, val_lowIdx]
      rcases Nat.even_or_odd' n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> omega
    have hb1_le : (Fin.rev (lowIdx s) : ℕ) ≤ (lowIdx s : ℕ) + 2 := by
      simp only [Fin.val_rev, val_lowIdx]
      rcases Nat.even_or_odd' n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> omega
    have hdown : downIdx s = Fin.rev (lowIdx s) := by
      refine Fin.ext ?_
      simp only [Fin.val_rev, val_lowIdx]
      omega
    have hup : upIdx s = (⟨s.val + 1, upIdx_lt n s⟩ : Fin n) := rfl
    have hp1 : levelPerm s (lowIdx s) = Fin.rev (lowIdx s) := by
      rw [levelPerm, dite_eq_right h, Equiv.swap_apply_left]
    rw [hup, hdown]
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · intro hj
        subst hj
        have haj : lowIdx s < (⟨s.val + 1, upIdx_lt n s⟩ : Fin n) := by
          rw [Fin.lt_def]; simp [val_lowIdx]
        have hlt := (H (lowIdx s)).mpr haj
        rw [hp1] at hlt
        rw [Fin.lt_def] at hlt
        simp only [Fin.val_rev, val_lowIdx] at hlt
        omega
      · intro hj
        subst hj
        have haj : lowIdx s < Fin.rev (lowIdx s) := by
          rw [Fin.lt_def]; omega
        have hlt := (H (lowIdx s)).mpr haj
        rw [hp1] at hlt
        exact absurd hlt (lt_irrefl _)
    · rintro ⟨hj1, hj2⟩ a
      have hkey : Fin.rev (lowIdx s) < j ↔ lowIdx s < j := by
        rw [Fin.lt_def, Fin.lt_def]
        have hjA : (j : ℕ) ≠ (lowIdx s : ℕ) + 1 := by
          intro hh
          exact hj1 (Fin.ext (by
            show (j : ℕ) = (⟨s.val + 1, upIdx_lt n s⟩ : Fin n).val
            rw [hh]; simp [val_lowIdx]))
        have hjB : (j : ℕ) ≠ (Fin.rev (lowIdx s) : ℕ) := fun hh => hj2 (Fin.ext hh)
        omega
      rw [levelPerm, dite_eq_right h]
      by_cases ha : a = lowIdx s
      · subst ha
        rw [Equiv.swap_apply_left]
        exact hkey
      by_cases hb : a = Fin.rev (lowIdx s)
      · subst hb
        rw [Equiv.swap_apply_right]
        exact hkey.symm
      rw [Equiv.swap_apply_of_ne_of_ne ha hb]

theorem bPerm_btop_eq_iff (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2)) :
    bPerm ε (fun _ => levelPerm s) (btop ε) = btop ε ↔
      ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r := by
  have hbtop : ∀ (r : Fin f) (j : Fin n), j ∈ ε r →
      ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) =
        Finset.univ.filter (fun a : Fin n => a < j) := by
    intro r j hj
    have hbdeg : bdeg ε (r, j) = (j : ℕ) := by simp [bdeg, hj]
    rw [show ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
        Finset (Fin n)) =
        Finset.univ.filter (fun a : Fin n => (a : ℕ) < bdeg ε (r, j)) from rfl, hbdeg]
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.lt_def.symm
  constructor
  · intro h r
    constructor
    · intro h1
      have hcomp := congrArg Subtype.val (congrFun h (r, upIdx s))
      have hmap : ((btop ε (r, upIdx s) : Set.powersetCard (Fin n) (bdeg ε (r, upIdx s))) :
            Finset (Fin n)).map (levelPerm s).toEmbedding =
          ((btop ε (r, upIdx s) : Set.powersetCard (Fin n) (bdeg ε (r, upIdx s))) :
            Finset (Fin n)) := by
        simpa only [bPerm] using hcomp
      rw [hbtop r (upIdx s) h1] at hmap
      have H := (map_filter_lt_eq_iff (levelPerm s) (upIdx s)).mp hmap
      exact ((levelPerm_lt_iff s (upIdx s)).mp H).1 rfl
    · intro h2
      have hcomp := congrArg Subtype.val (congrFun h (r, downIdx s))
      have hmap : ((btop ε (r, downIdx s) : Set.powersetCard (Fin n) (bdeg ε (r, downIdx s))) :
            Finset (Fin n)).map (levelPerm s).toEmbedding =
          ((btop ε (r, downIdx s) : Set.powersetCard (Fin n) (bdeg ε (r, downIdx s))) :
            Finset (Fin n)) := by
        simpa only [bPerm] using hcomp
      rw [hbtop r (downIdx s) h2] at hmap
      have H := (map_filter_lt_eq_iff (levelPerm s) (downIdx s)).mp hmap
      exact ((levelPerm_lt_iff s (downIdx s)).mp H).2 rfl
  · intro h
    funext p
    obtain ⟨r, j⟩ := p
    apply Subtype.ext
    by_cases hj : j ∈ ε r
    · have hj1 : j ≠ upIdx s := fun hh => (h r).1 (hh ▸ hj)
      have hj2 : j ≠ downIdx s := fun hh => (h r).2 (hh ▸ hj)
      have hcut := (levelPerm_lt_iff s j).mpr ⟨hj1, hj2⟩
      have hmap : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)).map (levelPerm s).toEmbedding =
          ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) := by
        rw [hbtop r j hj]
        exact (map_filter_lt_eq_iff _ _).mpr hcut
      simpa only [bPerm] using hmap
    · have hbdeg : bdeg ε (r, j) = 0 := by simp [bdeg, hj]
      have hbtop' : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) = ∅ := by
        rw [show ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) =
            Finset.univ.filter (fun a : Fin n => (a : ℕ) < bdeg ε (r, j)) from rfl, hbdeg]
        ext a
        simp
      have hmap : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)).map (levelPerm s).toEmbedding =
          ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) : Finset (Fin n)) := by
        rw [hbtop']
        simp
      simpa only [bPerm] using hmap
theorem levelSign_eq_one_of_short {n : ℕ} {s : Fin (n / 2)} (h : s.val + 1 < n / 2) (z : F)
    (a : Fin n) : levelSign (unitaryInvolution F 2 f) z s a = 1 := by
  have hneg : (-1 : F) = 1 := by
    have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
    have h : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h
  rw [levelSign, dite_eq_left h]
  simp only [shortSign]
  split_ifs <;> simp [hneg, map_one]

theorem levelSign_eq_long {n : ℕ} {s : Fin (n / 2)} (h : ¬ s.val + 1 < n / 2) (z : F)
    (a : Fin n) :
    levelSign (unitaryInvolution F 2 f) z s a =
      if a = lowIdx s then -z⁻¹ else if a = Fin.rev (lowIdx s) then z else 1 := by
  rw [levelSign, dite_eq_right h]
  rfl

theorem rev_lowIdx_ge_of_long {n : ℕ} {s : Fin (n / 2)} (h : ¬ s.val + 1 < n / 2) :
    (Fin.rev (lowIdx s) : ℕ) ≥ (lowIdx s : ℕ) + 1 := by
  simp only [Fin.val_rev, val_lowIdx]
  rcases Nat.even_or_odd' n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> omega

theorem rev_lowIdx_le_of_long {n : ℕ} {s : Fin (n / 2)} (h : ¬ s.val + 1 < n / 2) :
    (Fin.rev (lowIdx s) : ℕ) ≤ (lowIdx s : ℕ) + 2 := by
  simp only [Fin.val_rev, val_lowIdx]
  rcases Nat.even_or_odd' n with ⟨m, hm⟩ | ⟨m, hm⟩ <;> omega

theorem lowIdx_lt_iff_rev_lt_of_long {n : ℕ} {s : Fin (n / 2)} (h : ¬ s.val + 1 < n / 2) {j : Fin n}
    (hj1 : j ≠ upIdx s) (hj2 : j ≠ downIdx s) :
    lowIdx s < j ↔ Fin.rev (lowIdx s) < j := by
  have hb1_ge := rev_lowIdx_ge_of_long h
  have hb1_le := rev_lowIdx_le_of_long h
  rw [Fin.lt_def, Fin.lt_def]
  have hjA : (j : ℕ) ≠ (lowIdx s : ℕ) + 1 := by
    intro hh
    exact hj1 (Fin.ext (by
      show (j : ℕ) = (upIdx s : Fin n).val
      rw [hh]; simp [val_lowIdx]))
  have hjB : (j : ℕ) ≠ (Fin.rev (lowIdx s) : ℕ) := by
    intro hh
    exact hj2 (Fin.ext (by
      show (j : ℕ) = (downIdx s : Fin n).val
      rw [hh]
      simp only [Fin.val_rev, val_lowIdx]
      omega))
  omega

omit [CharP k 2] in
theorem prod_btop_suFrob_levelSign_eq_one {n : ℕ}
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2))
    (hP : ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r) :
    (∏ p : Fin f × Fin n,
        ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
          suFrob φ₀ f p.1 (levelSign (unitaryInvolution F 2 f) (ζ : F) s a)) = 1 := by
  classical
  have hneg : (-1 : F) = 1 := by
    have h2 : (2 : F) = 0 := by simpa using (CharP.cast_eq_zero F 2)
    have h : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
    exact neg_eq_of_add_eq_zero_left h
  by_cases h : s.val + 1 < n / 2
  · refine Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun a _ => ?_
    rw [levelSign_eq_one_of_short h, suFrob_apply, map_one, one_pow]
  · refine Finset.prod_eq_one fun p _ => ?_
    obtain ⟨r, j⟩ := p
    by_cases hj : j ∈ ε r
    · have hbdeg : bdeg ε (r, j) = (j : ℕ) := by simp [bdeg, hj]
      have hbtop : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) = Finset.univ.filter (fun a : Fin n => a < j) := by
        rw [show ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) =
            Finset.univ.filter (fun a : Fin n => (a : ℕ) < bdeg ε (r, j)) from rfl, hbdeg]
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Fin.lt_def.symm
      have hj1 : j ≠ upIdx s := fun hh => (hP r).1 (hh ▸ hj)
      have hj2 : j ≠ downIdx s := fun hh => (hP r).2 (hh ▸ hj)
      have hiff : lowIdx s < j ↔ Fin.rev (lowIdx s) < j := lowIdx_lt_iff_rev_lt_of_long h hj1 hj2
      let b : Fin n := lowIdx s
      let b' : Fin n := Fin.rev (lowIdx s)
      have hbb' : b ≠ b' := by simpa [b, b'] using lowIdx_ne_rev s s
      have hb_eq : levelSign (unitaryInvolution F 2 f) (ζ : F) s b = -(ζ : F)⁻¹ := by
        rw [levelSign_eq_long h]; simp [b]
      have hb'_eq : levelSign (unitaryInvolution F 2 f) (ζ : F) s b' = (ζ : F) := by
        rw [levelSign_eq_long h]; simp [b', b, Ne.symm hbb']
      have hone : ∀ a : Fin n, a ≠ b → a ≠ b' →
          suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s a) = 1 := by
        intro a ha hab
        rw [levelSign_eq_long h,
          if_neg (fun hh => ha (by simpa [b] using hh)),
          if_neg (fun hh => hab (by simpa [b'] using hh)),
          suFrob_apply, map_one, one_pow]
      have hkey : suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b) *
          suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b') = 1 := by
        rw [hb_eq, hb'_eq, suFrob_apply, suFrob_apply, ← mul_pow, ← map_mul,
          show (-(ζ : F)⁻¹ * (ζ : F)) = (-1 : F) from by rw [neg_mul, inv_mul_cancel₀ hζ],
          hneg, map_one, one_pow]
      have hfac : (∏ a ∈ Finset.univ.filter (fun a : Fin n => a < j),
            suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s a)) =
          (if b ∈ Finset.univ.filter (fun a : Fin n => a < j) then
              suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b) else 1) *
            (if b' ∈ Finset.univ.filter (fun a : Fin n => a < j) then
              suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b') else 1) := by
        rw [← Finset.prod_ite_eq' (Finset.univ.filter (fun a : Fin n => a < j)) b
              (fun _ => suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b)),
            ← Finset.prod_ite_eq' (Finset.univ.filter (fun a : Fin n => a < j)) b'
              (fun _ => suFrob φ₀ f r (levelSign (unitaryInvolution F 2 f) (ζ : F) s b')),
            ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun a ha => ?_
        by_cases hab : a = b
        · subst hab; simp [hbb']
        · by_cases hab' : a = b'
          · subst hab'; simp [Ne.symm hbb']
          · rw [hone a hab hab']
            simp [hab, hab']
      rw [hbtop, hfac]
      by_cases hbS : b ∈ Finset.univ.filter (fun a : Fin n => a < j)
      · have hb'S : b' ∈ Finset.univ.filter (fun a : Fin n => a < j) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbS ⊢
          exact hiff.mp hbS
        rw [if_pos hbS, if_pos hb'S, hkey]
      · have hb'S : b' ∉ Finset.univ.filter (fun a : Fin n => a < j) := by
          intro hh
          exact hbS (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
            exact hiff.mpr hh)
        rw [if_neg hbS, if_neg hb'S, mul_one]
    · have hbdeg : bdeg ε (r, j) = 0 := by simp [bdeg, hj]
      have hbtop : ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) = ∅ := by
        rw [show ((btop ε (r, j) : Set.powersetCard (Fin n) (bdeg ε (r, j))) :
            Finset (Fin n)) =
            Finset.univ.filter (fun a : Fin n => (a : ℕ) < bdeg ε (r, j)) from rfl, hbdeg]
        ext a
        simp
      rw [hbtop, Finset.prod_empty]

theorem bForm_suRep_levelWeyl_bTop (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2)) :
    bForm (k := k) ε (suRep φ₀ n ε (levelWeyl (unitaryInvolution_involutive hF) ζ s) (bTop ε))
        (bTop ε) =
      if ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r then 1 else 0 := by
  classical
  have _ : 2 ≤ n := hn
  have hσ := unitaryInvolution_involutive hF
  have hmat : ∀ r : Fin f,
      (suTwist φ₀ f n (levelWeyl hσ ζ s) r : Matrix (Fin n) (Fin n) k) =
        ((levelPerm s)⁻¹).permMatrix k *
          Matrix.diagonal (fun a => suFrob φ₀ f r
            (levelSign (unitaryInvolution F 2 f) (ζ : F) s a)) := by
    intro r
    rw [coe_suTwist_apply, SUExtras.mat_apply, coe_levelWeyl hσ hζ, signedPerm_map,
      signedPerm_eq_permMatrix_mul_diagonal]
  have hbv : bMat ε (fun r => (suTwist φ₀ f n (levelWeyl hσ ζ s) r :
        Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε =
      (∏ p : Fin f × Fin n,
        ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
          suFrob φ₀ f p.1 (levelSign (unitaryInvolution F 2 f) (ζ : F) s a)) •
        Pi.single (bPerm ε (fun _ => levelPerm s) (btop ε)) (1 : k) := by
    rw [show (fun r => (suTwist φ₀ f n (levelWeyl hσ ζ s) r : Matrix (Fin n) (Fin n) k)) =
        (fun r => ((levelPerm s)⁻¹).permMatrix k *
          Matrix.diagonal (fun a => suFrob φ₀ f r
            (levelSign (unitaryInvolution F 2 f) (ζ : F) s a))) from funext hmat,
      bMat_mul, ← Matrix.mulVec_mulVec, bMat_diagonal_mulVec_bvec, Matrix.mulVec_smul]
    rw [show bvec ε = Pi.single (btop ε) (1 : k) from rfl,
      bMat_permMatrix_mulVec_single]
  have hform : bForm (k := k) ε (suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε)) (bTop ε) =
      if bPerm ε (fun _ => levelPerm s) (btop ε) = btop ε then
        (∏ p : Fin f × Fin n,
          ∏ a ∈ ((btop ε p : Set.powersetCard (Fin n) (bdeg ε p)) : Finset (Fin n)),
            suFrob φ₀ f p.1 (levelSign (unitaryInvolution F 2 f) (ζ : F) s a)) else 0 := by
    have h1 : suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε) =
        Submodule.Quotient.mk
          (⟨bMat ε (fun r => (suTwist φ₀ f n (levelWeyl hσ ζ s) r :
              Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε,
            bMat_mulVec_mem_bCyc ε (suTwist φ₀ f n (levelWeyl hσ ζ s))
              (bvec_mem_bCyc ε)⟩ : bCyc (k := k) ε) := by
      change bRep ε (suTwist φ₀ f n (levelWeyl hσ ζ s))
        (Submodule.Quotient.mk (⟨bvec ε, bvec_mem_bCyc ε⟩ : bCyc (k := k) ε)) = _
      rw [bRep_mk]
    rw [h1, show bTop ε = Submodule.Quotient.mk
        (⟨bvec ε, bvec_mem_bCyc ε⟩ : bCyc (k := k) ε) from rfl, bForm_mk]
    change (bMat ε (fun r => (suTwist φ₀ f n (levelWeyl hσ ζ s) r :
        Matrix (Fin n) (Fin n) k)) *ᵥ bvec ε) ⬝ᵥ bvec ε = _
    rw [hbv, smul_dotProduct, single_dotProduct, one_mul, bvec]
    by_cases hu : bPerm ε (fun _ => levelPerm s) (btop ε) = btop ε
    · rw [if_pos hu, hu, Pi.single_eq_same]
      simp
    · rw [if_neg hu, Pi.single_eq_of_ne hu, smul_zero]
  rw [hform]
  by_cases hP : ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r
  · rw [if_pos ((bPerm_btop_eq_iff ε s).mpr hP), if_pos hP,
      prod_btop_suFrob_levelSign_eq_one ζ hζ φ₀ ε s hP]
  · have hu : bPerm ε (fun _ => levelPerm s) (btop ε) ≠ btop ε :=
      fun hh => hP ((bPerm_btop_eq_iff ε s).mp hh)
    rw [if_neg hu, if_neg hP]

theorem bForm_suRep_mem_L_bTop (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) {l : SU (unitaryInvolution F 2 f) n}
    (hl : l ∈ (curtisDatum hF n hn ζ hζ).L) :
    bForm (k := k) ε (suRep φ₀ n ε l (bTop ε)) (bTop ε) = 1 := by
  classical
  obtain ⟨l', hl'SU, hl'mat⟩ := transpose_mem_SU (A := (l : GL (Fin n) F)) l.2
  let l'' : SU (unitaryInvolution F 2 f) n := ⟨l', hl'SU⟩
  have hl''mat : ((l'' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((l : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := hl'mat
  have hl'U : l'' ∈ (curtisDatum hF n hn ζ hζ).U := by
    rw [mem_curtisDatum_U_iff hF n hn ζ hζ]
    constructor
    · intro a b hba
      have h := (curtisDatum_L_lower hF n hn ζ hζ (g := l) hl).1 b a hba
      change ((l'' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b = 0
      rw [hl''mat, Matrix.transpose_apply]
      simpa only [SUExtras.mat_apply] using h
    · intro a
      have h := (curtisDatum_L_lower hF n hn ζ hζ (g := l) hl).2 a
      change ((l'' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a = 1
      rw [hl''mat, Matrix.transpose_apply]
      simpa only [SUExtras.mat_apply] using h
  have htrans : ∀ r, ((suTwist φ₀ f n l'') r : Matrix (Fin n) (Fin n) k) =
      ((suTwist φ₀ f n l) r : Matrix (Fin n) (Fin n) k)ᵀ := by
    intro r
    rw [coe_suTwist_apply, coe_suTwist_apply, SUExtras.mat_apply, SUExtras.mat_apply, hl''mat,
      Matrix.transpose_map]
  have hpair := bForm_bRep ε (suTwist φ₀ f n l) (suTwist φ₀ f n l'') htrans (bTop ε) (bTop ε)
  have hbTop'' : bRep ε (suTwist φ₀ f n l'') (bTop ε) = bTop ε := by
    rw [← show suRep φ₀ n ε l'' = bRep ε (suTwist φ₀ f n l'') from rfl]
    exact suRep_bTop_of_mem_U hF hn ζ hζ φ₀ ε hl'U
  rw [show suRep φ₀ n ε l = bRep ε (suTwist φ₀ f n l) from rfl]
  rw [hpair, hbTop'', bForm_bTop]

theorem heckeT_suRep_bTop (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2)) :
    (curtisDatum hF n hn ζ hζ).heckeT (suRep φ₀ n ε) s (bTop ε) =
      (bForm (k := k) ε (suRep φ₀ n ε (levelWeyl (unitaryInvolution_involutive hF) ζ s) (bTop ε))
          (bTop ε) +
        (curtisDatum hF n hn ζ hζ).dScalar (chiEps φ₀ ε) s) • bTop ε := by
  classical
  let D := curtisDatum hF n hn ζ hζ
  have hσ := unitaryInvolution_involutive hF
  change D.heckeT (suRep φ₀ n ε) s (bTop ε) =
    (bForm (k := k) ε (suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε)) (bTop ε) +
      D.dScalar (chiEps φ₀ ε) s) • bTop ε
  have : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  have hTfix : D.heckeT (suRep φ₀ n ε) s (bTop ε) ∈ D.fixU (suRep φ₀ n ε) := by
    refine D.heckeT_mem_fixU (ρ := suRep φ₀ n ε) s ?_
    exact (D.mem_fixU (ρ := suRep φ₀ n ε)).mpr fun u hu =>
      suRep_bTop_of_mem_U hF hn ζ hζ φ₀ ε hu
  have hx : ∀ g : SU (unitaryInvolution F 2 f) n,
      (∀ a b : Fin n, b < a → SUExtras.mat (unitaryInvolution F 2 f) n g a b = 0) →
      (∀ a : Fin n, SUExtras.mat (unitaryInvolution F 2 f) n g a a = 1) →
      suRep φ₀ n ε g (D.heckeT (suRep φ₀ n ε) s (bTop ε)) =
        D.heckeT (suRep φ₀ n ε) s (bTop ε) := by
    intro g hlow hdiag
    exact (D.mem_fixU (ρ := suRep φ₀ n ε)).mp hTfix g
      ((mem_curtisDatum_U_iff hF n hn ζ hζ g).mpr ⟨hlow, hdiag⟩)
  obtain ⟨c, hc⟩ := eq_smul_bTop_of_fixed hF φ₀ ε
    (D.heckeT (suRep φ₀ n ε) s (bTop ε)) hx
  have hc_eq : c = bForm (k := k) ε (D.heckeT (suRep φ₀ n ε) s (bTop ε)) (bTop ε) := by
    have h := congrArg (fun v => bForm (k := k) ε v (bTop ε)) hc
    rw [h]
    simp [bForm_bTop]
  have hsum : bForm (k := k) ε (D.heckeT (suRep φ₀ n ε) s (bTop ε)) (bTop ε) =
      bForm (k := k) ε (suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε)) (bTop ε) +
        ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, chiEps φ₀ ε (D.phi s x) := by
    let vec : D.X s → BModel k ε := fun x =>
      suRep φ₀ n ε ((x : SU (unitaryInvolution F 2 f) n) * D.n s) (bTop ε)
    let pair : D.X s → k := fun x => bForm (k := k) ε (vec x) (bTop ε)
    have h1n : ((1 : D.X s) : SU (unitaryInvolution F 2 f) n) * D.n s =
        levelWeyl hσ ζ s := by
      rw [Subgroup.coe_one, one_mul]
      rfl
    have hF1 : pair 1 = bForm (k := k) ε
        (suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε)) (bTop ε) := by
      change bForm (k := k) ε (vec 1) (bTop ε) = _
      rw [show vec 1 = suRep φ₀ n ε (levelWeyl hσ ζ s) (bTop ε) from by
        simp only [vec, h1n]]
    have hFx : ∀ x ∈ (Finset.univ : Finset (D.X s)).erase 1, pair x = chiEps φ₀ ε (D.phi s x) := by
      intro x hx'
      have hxne : (x : SU (unitaryInvolution F 2 f) n) ≠ 1 :=
        fun h => Finset.ne_of_mem_erase hx' (OneMemClass.coe_eq_one.mp h)
      obtain ⟨l, hl, u, hu, hlu⟩ := D.phi_spec s x x.2 hxne
      have hux : suRep φ₀ n ε u (bTop ε) = bTop ε :=
        suRep_bTop_of_mem_U hF hn ζ hζ φ₀ ε hu
      have hphix : suRep φ₀ n ε (D.phi s x) (bTop ε) =
          chiEps φ₀ ε (D.phi s x) • bTop ε :=
        suRep_bTop_of_mem_H hF hn ζ hζ φ₀ ε (D.phi_mem s x x.2 hxne)
      have hpair : bForm (k := k) ε (suRep φ₀ n ε l (bTop ε)) (bTop ε) = 1 :=
        bForm_suRep_mem_L_bTop hF hn ζ hζ φ₀ ε hl
      have hstep : suRep φ₀ n ε
            ((x : SU (unitaryInvolution F 2 f) n) * D.n s) (bTop ε) =
          chiEps φ₀ ε (D.phi s x) • suRep φ₀ n ε l (bTop ε) := by
        rw [show (x : SU (unitaryInvolution F 2 f) n) * D.n s = l * D.phi s x * u from hlu]
        rw [← act_mul, ← act_mul, hux, hphix, map_smul]
      change bForm (k := k) ε (vec x) (bTop ε) = chiEps φ₀ ε (D.phi s x)
      rw [show vec x = chiEps φ₀ ε (D.phi s x) • suRep φ₀ n ε l (bTop ε) from hstep,
        map_smul, LinearMap.smul_apply, hpair, smul_eq_mul, mul_one]
    rw [D.heckeT_apply]
    change bForm (k := k) ε (∑ x : D.X s, vec x) (bTop ε) = _
    rw [map_sum, LinearMap.sum_apply]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : D.X s))]
    change (∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, pair x) + pair 1 = _
    rw [hF1, Finset.sum_congr rfl hFx]
    rw [add_comm]
  have hd : D.dScalar (chiEps φ₀ ε) s =
      ∑ x ∈ (Finset.univ : Finset (D.X s)).erase 1, chiEps φ₀ ε (D.phi s x) := by
    unfold CurtisDatum.dScalar
    apply Finset.sum_congr
    · ext x; simp
    · intro x hx; rfl
  rw [hc, hc_eq, hsum, hd]

omit [CharP k 2] in
theorem exists_chiEps_ne_one_of_not_full_of_not_P (hF : Nat.card F = (2 ^ f) ^ 2)
    (φ₀ : F →+* k) {n : ℕ} (ε : Fin f → Finset (Fin n)) (s : Fin (n / 2))
    (hP : ¬ ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r) (hfull : ¬ IsFullNode ε s) :
    ∃ t ∈ levelTorus (unitaryInvolution F 2 f) s, chiEps φ₀ ε t ≠ 1 := by
  classical
  have hf_pos : 0 < f := by
    by_contra h
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos h
    subst hf0
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  set a : ℕ := bDigit ε (upIdx s) with ha
  set b : ℕ := bDigit ε (downIdx s) with hb
  have ha_lt : a < 2 ^ f := bDigit_lt ε _
  have hb_lt : b < 2 ^ f := bDigit_lt ε _
  have hb_le : b ≤ 2 ^ f := le_of_lt hb_lt
  have hne0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hP
    intro r
    exact ⟨(bDigit_eq_zero_iff ε _).mp h.1 r, (bDigit_eq_zero_iff ε _).mp h.2 r⟩
  have hnefull : a ≠ 2 ^ f - 1 ∨ b ≠ 2 ^ f - 1 := by
    by_contra h
    push Not at h
    apply hfull
    intro r
    exact ⟨(bDigit_eq_iff ε _).mp h.1 r, (bDigit_eq_iff ε _).mp h.2 r⟩
  by_cases hEven : 2 * (s : ℕ) + 2 = n
  · have hlt : ¬ s.val + 1 < n / 2 := by omega
    have hEven' : Even n := ⟨s + 1, by omega⟩
    have haeq : a = b := by
      simp only [ha, hb]
      congr 1
      refine Fin.ext ?_
      show (s : ℕ) + 1 = n - 1 - (s : ℕ)
      omega
    have ha0 : a ≠ 0 := by
      rcases hne0 with h | h
      · exact h
      · rwa [← haeq] at h
    have hafull : a ≠ 2 ^ f - 1 := by
      rcases hnefull with h | h
      · exact h
      · rwa [← haeq] at h
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (fixedSubfield F 2 f)ˣ)
    let c : F := ((g : (fixedSubfield F 2 f)ˣ) : fixedSubfield F 2 f)
    have hc0 : c ≠ 0 := by
      intro h0
      exact g.ne_zero (Subtype.ext h0)
    have hσc : unitaryInvolution F 2 f c = c :=
      mem_fixedSubfield.mp (g : fixedSubfield F 2 f).2
    have horderg : orderOf g = 2 ^ f - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
        card_fixedSubfield (p := 2) (f := f) hF]
    have hca : c ^ a ≠ 1 := by
      intro h1
      have h1' : g ^ a = 1 := by
        apply Units.ext
        apply Subtype.ext
        simpa [c] using h1
      have hdvd : orderOf g ∣ a := orderOf_dvd_iff_pow_eq_one.mpr h1'
      rw [horderg] at hdvd
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha0) (by omega) hdvd
    obtain ⟨t, ht, htmat⟩ := exists_mem_levelTorus_tFun_even hF s hlt hEven' hc0 hσc
    refine ⟨t, ht, ?_⟩
    rw [chiEps_of_tFun φ₀ ε s hc0 htmat, if_pos hEven, mul_one, ← map_pow]
    intro h1
    have h2 : c ^ a = 1 := by
      apply φ₀.injective
      simpa [a] using h1
    exact hca h2
  · have hne : ¬ (¬ s.val + 1 < n / 2 ∧ Even n) := by
      rintro ⟨h1, h2⟩
      apply hEven
      obtain ⟨k, hk⟩ := h2
      omega
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    let c : F := (g : F)
    have hc0 : c ≠ 0 := g.ne_zero
    have horderg : orderOf g = (2 ^ f) ^ 2 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    set N : ℕ := a + 2 ^ f * b with hN
    have hNpos : 0 < N := by
      rcases hne0 with h | h
      · have : 0 < a := Nat.pos_of_ne_zero h
        omega
      · have : 0 < b := Nat.pos_of_ne_zero h
        have : 0 < 2 ^ f := by positivity
        nlinarith
    have hN_le : N ≤ (2 ^ f) ^ 2 - 1 := by
      have h1 : a + 2 ^ f * b ≤ (2 ^ f - 1) + 2 ^ f * (2 ^ f - 1) := by
        gcongr <;> omega
      rw [hN]
      calc a + 2 ^ f * b ≤ (2 ^ f - 1) + 2 ^ f * (2 ^ f - 1) := h1
        _ = (2 ^ f) ^ 2 - 1 := by
            rw [← hF]
            exact two_pow_sub_one_add_mul_eq_natCard_sub_one (F := F) hF
    have hN_ne : N ≠ (2 ^ f) ^ 2 - 1 := by
      intro hEq
      have hb_le' : b ≤ 2 ^ f := hb_le
      have hNq : a + 2 ^ f * b + 1 = 2 ^ f * 2 ^ f := by
        have hsq : (2 ^ f) ^ 2 = 2 ^ f * 2 ^ f := by ring
        rw [← hsq]
        omega
      have h1 : a + 1 = 2 ^ f * (2 ^ f - b) := by
        rw [Nat.mul_sub_left_distrib]
        omega
      have hle1 : 2 ^ f - b ≤ 1 := by
        apply Nat.le_of_mul_le_mul_left _ (by positivity : 0 < 2 ^ f)
        rw [← h1, mul_one]
        exact Nat.succ_le_of_lt ha_lt
      have hge1 : 1 ≤ 2 ^ f - b := by omega
      have hb_eq : b = 2 ^ f - 1 := by omega
      have h2fb : 2 ^ f - b = 1 := by omega
      have ha_eq : a = 2 ^ f - 1 := by
        rw [h2fb, mul_one] at h1
        omega
      rcases hnefull with h | h
      · exact h ha_eq
      · exact h hb_eq
    have hNlt : N < (2 ^ f) ^ 2 - 1 := lt_of_le_of_ne hN_le hN_ne
    have hpow : g ^ N ≠ 1 := by
      intro h1
      have hdvd : orderOf g ∣ N := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [horderg] at hdvd
      exact Nat.not_dvd_of_pos_of_lt hNpos hNlt hdvd
    obtain ⟨t, ht, htmat⟩ := exists_mem_levelTorus_tFun hF s hc0 hne
    refine ⟨t, ht, ?_⟩
    have hχeq : chiEps φ₀ ε t = φ₀ (c ^ N) := by
      rw [chiEps_of_tFun φ₀ ε s hc0 htmat, if_neg hEven, unitaryInvolution_apply,
        ← map_pow, ← map_pow, ← map_mul, ← pow_mul, ← pow_add]
    rw [hχeq]
    intro h1
    have h2 : c ^ N = 1 := by
      apply φ₀.injective
      rwa [map_one]
    exact hpow (by
      apply Units.ext
      simpa [c] using h2)

theorem isCurtisType_suRep (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    (ε : Fin f → Finset (Fin n)) :
    (curtisDatum hF n hn ζ hζ).IsCurtisType (suRep φ₀ n ε) (bTop ε) (chiEps φ₀ ε)
      (muEps ε) := by
  classical
  let D := curtisDatum hF n hn ζ hζ
  have hf_pos : 0 < f := by
    by_contra h
    have hf0 : f = 0 := Nat.eq_zero_of_not_pos h
    subst hf0
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hχmul : ∀ a ∈ D.H, ∀ b ∈ D.H,
      chiEps φ₀ ε (a * b) = chiEps φ₀ ε a * chiEps φ₀ ε b := by
    intro a ha b hb
    have hH : D.H = ⨆ s, levelTorus (unitaryInvolution F 2 f) (n := n) s := by
      show (curtisDatum hF n hn ζ hζ).H = _
      unfold curtisDatum
      rfl
    rw [hH] at ha hb
    exact chiEps_mul φ₀ ε
      (iSup_le (fun s => levelTorus_le_diagSubgroup (σ := unitaryInvolution F 2 f)
        (n := n) s) ha)
      (iSup_le (fun s => levelTorus_le_diagSubgroup (σ := unitaryInvolution F 2 f)
        (n := n) s) hb)
  refine ⟨?_, bTop_ne_zero ε, ?_, ?_⟩
  · rw [D.mem_fixU]
    intro u hu
    exact suRep_bTop_of_mem_U hF hn ζ hζ φ₀ ε hu
  · intro h hh
    exact suRep_bTop_of_mem_H hF hn ζ hζ φ₀ ε hh
  · intro s
    have hmu : bForm (k := k) ε
        (suRep φ₀ n ε (levelWeyl (unitaryInvolution_involutive hF) ζ s) (bTop ε)) (bTop ε) +
          D.dScalar (chiEps φ₀ ε) s = muEps ε s := by
      have hform := bForm_suRep_levelWeyl_bTop hF hn ζ hζ φ₀ ε s
      by_cases hP : ∀ r, upIdx s ∉ ε r ∧ downIdx s ∉ ε r
      · have hnotfull : ¬ IsFullNode ε s := by
          intro hfs
          exact (hP ⟨0, hf_pos⟩).1 (hfs ⟨0, hf_pos⟩).1
        have htriv : ∀ t ∈ levelTorus (unitaryInvolution F 2 f) s, chiEps φ₀ ε t = 1 := by
          intro t ht
          obtain ⟨c, hc⟩ := SUExtras.exists_tFun_of_mem_levelTorus ht
          rw [chiEps_of_tFun φ₀ ε s c.ne_zero (by simpa using hc)]
          have hup0 : bDigit ε (upIdx s) = 0 :=
            (bDigit_eq_zero_iff ε _).mpr fun r => (hP r).1
          have hdown0 : bDigit ε (downIdx s) = 0 :=
            (bDigit_eq_zero_iff ε _).mpr fun r => (hP r).2
          rw [hup0, hdown0]
          simp
        have hneg := (curtisDatum_dScalar_eq_neg_one hF n hn ζ hζ
          (chiEps φ₀ ε) s htriv).1
        rw [hform, if_pos hP, hneg, muEps, if_neg hnotfull]
        simp
      · by_cases hfs : IsFullNode ε s
        · have htriv : ∀ t ∈ levelTorus (unitaryInvolution F 2 f) s, chiEps φ₀ ε t = 1 :=
            fun t ht => chiEps_eq_one_of_isFullNode hF φ₀ ε hfs ht
          have hneg := (curtisDatum_dScalar_eq_neg_one hF n hn ζ hζ
            (chiEps φ₀ ε) s htriv).1
          rw [hform, if_neg hP, hneg, muEps, if_pos hfs]
          simp
        · have hnt := exists_chiEps_ne_one_of_not_full_of_not_P hF φ₀ ε s hP hfs
          have hzero := (curtisDatum_dScalar_eq_zero hF n hn ζ hζ
            (chiEps φ₀ ε) hχmul s hnt).1
          rw [hform, if_neg hP, hzero, muEps, if_neg hfs]
          simp
    rw [heckeT_suRep_bTop hF hn ζ hζ φ₀ ε s, hmu]

theorem exists_iso_suRep (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F 2 f)) (hζ : (ζ : F) ≠ 0) (φ₀ : F →+* k)
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k (SU (unitaryInvolution F 2 f) n) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : SU (unitaryInvolution F 2 f) n → k} {μ : Fin (n / 2) → k}
    (ht : (curtisDatum hF n hn ζ hζ).IsCurtisType ρ y χ μ) :
    ∃ ε : Fin f → Finset (Fin n), (∀ r, (⟨0, by omega⟩ : Fin n) ∉ ε r) ∧
      (∀ h ∈ (curtisDatum hF n hn ζ hζ).H, χ h = chiEps φ₀ ε h) ∧ μ = muEps ε ∧
      ∃ β : V ≃ₗ[k] BModel k ε,
        ∀ (g : SU (unitaryInvolution F 2 f) n) (v : V), β (ρ g v) = suRep φ₀ n ε g (β v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let D := curtisDatum hF n hn ζ hζ
  obtain ⟨ε, h0, hχ, hμ⟩ := exists_eps_of_isCurtisType hF hn ζ hζ φ₀ ht
  rw [hμ] at ht ⊢
  have ht' : D.IsCurtisType ρ y (chiEps φ₀ ε) (muEps ε) :=
    (isCurtisType_congr_chi (D := D) hχ).mp ht
  refine ⟨ε, h0, hχ, rfl, ?_⟩
  exact D.iso_of_isCurtisType hρ (isSimpleRep_suRep hF φ₀ hn ε) ht'
    (isCurtisType_suRep hF hn ζ hζ φ₀ ε)

end CFSG.LieType.Universal.Unitary
