module

public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.KernelComponentRoots

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {K : Type} [Field K]

theorem torusRootChar_rootDiagUnit
    (l : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (rootDiagUnit τ l) α = ((rootChar l α : Kˣ) : K) :=
  torusRootChar_eq_of_apply hα (rootDiag_rootVec l hα)

theorem rootChar_single' (l : Fin τ.rank → Kˣ) (j : Fin τ.rank) :
    rootChar l (Pi.single j 1) = l j := by
  classical
  rw [rootChar, Finset.prod_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem rootChar_neg' (l : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar l (-v) = (rootChar l v)⁻¹ := by
  simp [rootChar, zpow_neg, Finset.prod_inv_distrib]

theorem eq_of_torusRootChar_single
    {g g' : ModGL τ K} (hg : g ∈ torusGroup τ K) (hg' : g' ∈ torusGroup τ K)
    (h : ∀ j, torusRootChar g (Pi.single j 1) = torusRootChar g' (Pi.single j 1)) : g = g' := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg'
  congr 1
  funext j
  have h1 := h j
  rw [torusRootChar_rootDiagUnit l (isRoot_single τ j),
    torusRootChar_rootDiagUnit l' (isRoot_single τ j), rootChar_single', rootChar_single'] at h1
  exact Units.ext h1

theorem mul_comm_of_mem_torusGroup
    {g g' : ModGL τ K} (hg : g ∈ torusGroup τ K) (hg' : g' ∈ torusGroup τ K) :
    g * g' = g' * g := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg
  obtain ⟨l', rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hg'
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem torusRootChar_zpow {h : ModGL τ K} (hh : h ∈ diagonalGroup) (α : Fin τ.rank → ℤ)
    {u : Kˣ} (hu : torusRootChar h α = u) (n : ℤ) :
    torusRootChar (h ^ n) α = ((u ^ n : Kˣ) : K) := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, zpow_zero, torusRootChar_one, Units.val_one]
  | succ n ih =>
    rw [zpow_add_one, torusRootChar_mul (zpow_mem hh n) hh, ih, hu, zpow_add_one, Units.val_mul]
  | pred n ih =>
    rw [zpow_sub_one, torusRootChar_mul (zpow_mem hh _) (inv_mem hh), ih,
      torusRootChar_inv hh, hu, zpow_sub_one, Units.val_mul, Units.val_inv_eq_inv_val]

theorem sq_eq_one_of_commute_pinnedX
    {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : ∀ α ∈ Ψ, IsRoot τ α)
    (h2 : ∀ j : Fin τ.rank, (2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ) ∈ AddSubgroup.closure Ψ)
    {z : ModGL τ K} (hz : z ∈ torusGroup τ K)
    (hc : ∀ α ∈ Ψ, ∀ c : K, z * pinnedX τ K α c = pinnedX τ K α c * z) : z ^ 2 = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hz
  let H : AddSubgroup (Fin τ.rank → ℤ) :=
    { carrier := {v | rootChar l v = 1}
      add_mem' := fun {u v} hu hv => by
        change rootChar l (u + v) = 1
        rw [rootChar_add, show rootChar l u = 1 from hu, show rootChar l v = 1 from hv, one_mul]
      zero_mem' := rootChar_zero l
      neg_mem' := fun {v} hv => by
        change rootChar l (-v) = 1
        rw [rootChar_neg', show rootChar l v = 1 from hv, inv_one] }
  have hΨH : AddSubgroup.closure Ψ ≤ H := by
    rw [AddSubgroup.closure_le]
    intro α hα
    have e := (commute_pinnedX_iff hz (hΨ α hα)).1 (hc α hα)
    rw [torusRootChar_rootDiagUnit l (hΨ α hα)] at e
    show rootChar l α = 1
    exact Units.ext e
  have hl : l * l = 1 := by
    funext j
    have e : rootChar l ((2 : ℤ) • (Pi.single j 1 : Fin τ.rank → ℤ)) = 1 := hΨH (h2 j)
    rw [two_zsmul, rootChar_add, rootChar_single'] at e
    exact e
  rw [sq, ← rootDiagUnit_mul, hl, rootDiagUnit_one]

theorem torusRootChar_conj_of_mapsRootLines
    {n h : ModGL τ K} {w : WeylGroup τ}
    (hn : MapsRootLines n w) (hh : h ∈ diagonalGroup) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (n * h * n⁻¹) α = torusRootChar h (w⁻¹ • α) := by
  obtain ⟨c, hc⟩ := hn.inv α hα
  have hα' : IsRoot τ (w⁻¹ • α) := CFSG.LieType.Chevalley.IsRoot.smul hα w⁻¹
  refine torusRootChar_eq_of_apply hα ?_
  have e2 : (n : Module.End K (RootModule τ K)) ((c : K) • rootVec τ K (w⁻¹ • α)) =
      rootVec τ K α := by
    rw [← hc]
    change ((n * n⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α) = _
    rw [mul_inv_cancel]
    rfl
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul,
    apply_rootVec_of_mem_diagonalGroup hh hα', smul_comm, map_smul, e2]

theorem torusRootChar_conj_torusElt
    (w : WeylGroup τ) (k : Fin τ.rank) (t : Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹) α =
      ((t ^ corootPair (w • (Pi.single k 1 : Fin τ.rank → ℤ)) α : Kˣ) : K) := by
  rw [torusRootChar_conj_of_mapsRootLines (mapsRootLines_canonicalRep w)
    (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup k t)) hα,
    torusRootChar_torusElt k t (CFSG.LieType.Chevalley.IsRoot.smul hα w⁻¹), corootPair_smul_single]

theorem sq_torusElt_mem_of_coroots
    {Ψ : Set (Fin τ.rank → ℤ)} {S : Subgroup (ModGL τ K)}
    (hS : ∀ (w : WeylGroup τ) (k : Fin τ.rank), w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ Ψ →
      ∀ t : Kˣ, canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ S)
    (hΨ : ∀ γ ∈ Ψ, IsRoot τ γ) (i : Fin τ.rank)
    (l : List ((Fin τ.rank → ℤ) × ℤ)) (hl : ∀ x ∈ l, x.1 ∈ Ψ)
    (hsum : ∀ j : Fin τ.rank,
      2 * τ.cartan i j = (l.map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum)
    (t : Kˣ) : torusElt τ K i t ^ 2 ∈ S := by
  classical
  have hex : ∀ x ∈ l, ∃ (w : WeylGroup τ) (k : Fin τ.rank),
      w • (Pi.single k 1 : Fin τ.rank → ℤ) = x.1 := fun x hx =>
    isRoot_iff_exists_smul_single.1 (hΨ _ (hl x hx))
  have hT : ∀ (w : WeylGroup τ) (k : Fin τ.rank), canonicalRep (coxeterSystem τ) K w *
      torusElt τ K k t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈ torusGroup τ K :=
    fun w k => (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) _).1
      (torusElt_mem_torusGroup k t)
  have key : ∀ l' : List ((Fin τ.rank → ℤ) × ℤ), (∀ x ∈ l', x ∈ l) →
      ∃ P : ModGL τ K, P ∈ S ∧ P ∈ torusGroup τ K ∧ ∀ j : Fin τ.rank,
        torusRootChar P (Pi.single j 1) =
          ((t ^ (l'.map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum : Kˣ) : K) := by
    intro l' hl'
    induction l' with
    | nil =>
      refine ⟨1, one_mem _, one_mem _, fun j => ?_⟩
      rw [torusRootChar_one, List.map_nil, List.sum_nil, zpow_zero, Units.val_one]
    | cons x l' ih =>
      obtain ⟨P, hPS, hPT, hPχ⟩ := ih fun y hy => hl' y (List.mem_cons_of_mem x hy)
      obtain ⟨w, k, hwk⟩ := hex x (hl' x List.mem_cons_self)
      set h := canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ with hh_def
      have hhS : h ∈ S := hS w k (hwk ▸ hl x (hl' x List.mem_cons_self)) t
      refine ⟨h ^ x.2 * P, mul_mem (zpow_mem hhS _) hPS, mul_mem (zpow_mem (hT w k) _) hPT,
        fun j => ?_⟩
      have hhχ := torusRootChar_conj_torusElt (K := K) w k t (isRoot_single τ j)
      rw [hwk] at hhχ
      rw [torusRootChar_mul (zpow_mem (torusGroup_le_diagonalGroup (hT w k)) _)
        (torusGroup_le_diagonalGroup hPT), torusRootChar_zpow (torusGroup_le_diagonalGroup
          (hT w k)) _ hhχ, hPχ, List.map_cons, List.sum_cons, ← Units.val_mul, ← zpow_mul,
        ← zpow_add, mul_comm (corootPair x.1 _)]
  obtain ⟨P, hPS, hPT, hPχ⟩ := key l fun x hx => hx
  have heq : torusElt τ K i t ^ 2 = P := by
    refine eq_of_torusRootChar_single (pow_mem (torusElt_mem_torusGroup i t) 2) hPT fun j => ?_
    have h1 := torusRootChar_torusElt (K := K) i t (isRoot_single τ j)
    have h2 : ∑ m, τ.cartan i m * (Pi.single j 1 : Fin τ.rank → ℤ) m = τ.cartan i j := by
      simp [Pi.single_apply]
    rw [h2] at h1
    rw [hPχ, ← hsum j, ← zpow_natCast, torusRootChar_zpow
      (torusGroup_le_diagonalGroup (torusElt_mem_torusGroup i t)) _ h1, ← zpow_mul, mul_comm]
    norm_num
  rw [heq]
  exact hPS

end CFSG.ComponentClassification.CatLeafProof
