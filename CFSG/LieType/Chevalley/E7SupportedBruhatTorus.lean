module

public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
open _root_.Classical in
@[expose] def supportedTorusHom
    (J : Set (Fin τ.rank)) : (J → Kˣ) →* ModGL τ K :=
  MonoidHom.noncommPiCoprod (fun j : J => torusEltHom τ K j)
    (show Pairwise fun i j : J => ∀ x y : Kˣ,
        Commute (torusEltHom τ K i x) (torusEltHom τ K j y) from
      fun i j _ t u => torusElt_mul_comm (i : Fin τ.rank) j t u)

variable (τ K) in
@[expose] def supportedTorus
    (J : Set (Fin τ.rank)) : Subgroup (ModGL τ K) :=
  (supportedTorusHom τ K J).range

theorem mem_supportedTorus
    {J : Set (Fin τ.rank)} {g : ModGL τ K} :
    g ∈ supportedTorus τ K J ↔ ∃ a : J → Kˣ, supportedTorusHom τ K J a = g :=
  Iff.rfl

theorem supportedTorusHom_mem
    (J : Set (Fin τ.rank)) (a : J → Kˣ) :
    supportedTorusHom τ K J a ∈ supportedTorus τ K J :=
  ⟨a, rfl⟩

open _root_.Classical in
theorem supportedTorusHom_apply
    (J : Set (Fin τ.rank)) (a : J → Kˣ) :
    supportedTorusHom τ K J a = (Finset.univ : Finset J).noncommProd
      (fun j => torusElt τ K j (a j))
      (fun i _ j _ _ => torusElt_mul_comm (i : Fin τ.rank) j (a i) (a j)) :=
  MonoidHom.noncommPiCoprod_apply _ _

theorem supportedTorusHom_mulSingle
    (J : Set (Fin τ.rank)) (j : J) (t : Kˣ) :
    supportedTorusHom τ K J (Pi.mulSingle j t) = torusElt τ K j t := by
  classical
  exact MonoidHom.noncommPiCoprod_mulSingle (fun j : J => torusEltHom τ K j) j t

theorem supportedTorus_eq_subsystemTorus
    (J : Set (Fin τ.rank)) :
    supportedTorus τ K J = subsystemTorus τ K J := by
  classical
  rw [supportedTorus, supportedTorusHom, MonoidHom.noncommPiCoprod_range]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    rintro _ ⟨t, rfl⟩
    exact torusElt_mem_subsystemTorus j.2 t
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, t, rfl⟩
    exact Subgroup.mem_iSup_of_mem (⟨i, hi⟩ : J) ⟨t, rfl⟩

theorem supportedTorus_le_torusGroup
    (J : Set (Fin τ.rank)) :
    supportedTorus τ K J ≤ torusGroup τ K := by
  rw [supportedTorus_eq_subsystemTorus]
  exact subsystemTorus_le_torusGroup

theorem supportedTorus_le_subsystemGroup
    (J : Set (Fin τ.rank)) :
    supportedTorus τ K J ≤ subsystemGroup τ K J := by
  rw [supportedTorus_eq_subsystemTorus]
  exact subsystemTorus_le_subsystemGroup

open _root_.Classical in
@[expose] def torusRootChar (h : ModGL τ K) (α : Fin τ.rank → ℤ) : K :=
  if hα : IsRoot τ α then (h : Module.End K (RootModule τ K)) (rootVec τ K α) (Sum.inr ⟨α, hα⟩)
  else 1

theorem torusRootChar_eq_of_apply {h : ModGL τ K} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    {c : K} (hc : (h : Module.End K (RootModule τ K)) (rootVec τ K α) = c • rootVec τ K α) :
    torusRootChar h α = c := by
  rw [torusRootChar, dite_eq_left hα, hc, rootVec_eq_single_of_isRoot hα, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem torusRootChar_of_not_isRoot (h : ModGL τ K) {α : Fin τ.rank → ℤ} (hα : ¬ IsRoot τ α) :
    torusRootChar h α = 1 :=
  dite_eq_right hα

theorem apply_rootVec_of_mem_diagonalGroup {h : ModGL τ K} (hh : h ∈ diagonalGroup)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (h : Module.End K (RootModule τ K)) (rootVec τ K α) = torusRootChar h α • rootVec τ K α := by
  obtain ⟨c, hc⟩ := hh.2 α hα
  rw [torusRootChar_eq_of_apply hα hc, hc]

theorem torusRootChar_ne_zero {h : ModGL τ K} (hh : h ∈ diagonalGroup) (α : Fin τ.rank → ℤ) :
    torusRootChar h α ≠ 0 := by
  by_cases hα : IsRoot τ α
  · obtain ⟨c, hc⟩ := hh.2 α hα
    rw [torusRootChar_eq_of_apply hα hc]
    exact c.ne_zero
  · rw [torusRootChar_of_not_isRoot h hα]
    exact one_ne_zero

theorem torusRootChar_one (α : Fin τ.rank → ℤ) : torusRootChar (1 : ModGL τ K) α = 1 := by
  by_cases hα : IsRoot τ α
  · exact torusRootChar_eq_of_apply hα (by rw [Units.val_one, Module.End.one_apply, one_smul])
  · exact torusRootChar_of_not_isRoot 1 hα

theorem torusRootChar_mul {h h' : ModGL τ K} (hh : h ∈ diagonalGroup) (hh' : h' ∈ diagonalGroup)
    (α : Fin τ.rank → ℤ) : torusRootChar (h * h') α = torusRootChar h α * torusRootChar h' α := by
  by_cases hα : IsRoot τ α
  · refine torusRootChar_eq_of_apply hα ?_
    rw [Units.val_mul, Module.End.mul_apply, apply_rootVec_of_mem_diagonalGroup hh' hα, map_smul,
      apply_rootVec_of_mem_diagonalGroup hh hα, smul_smul, mul_comm]
  · rw [torusRootChar_of_not_isRoot _ hα, torusRootChar_of_not_isRoot _ hα,
      torusRootChar_of_not_isRoot _ hα, one_mul]

theorem torusRootChar_inv {h : ModGL τ K} (hh : h ∈ diagonalGroup) (α : Fin τ.rank → ℤ) :
    torusRootChar h⁻¹ α = (torusRootChar h α)⁻¹ := by
  have h1 := torusRootChar_mul (inv_mem hh) hh α
  rw [inv_mul_cancel, torusRootChar_one] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem torusRootChar_torusElt
    (i : Fin τ.rank) (t : Kˣ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) :
    torusRootChar (torusElt τ K i t) α = ((t ^ (∑ j, τ.cartan i j * α j) : Kˣ) : K) :=
  torusRootChar_eq_of_apply hα (torusElt_rootVec i t hα)

theorem apply_rootVec_of_mem_torusGroup
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (h : Module.End K (RootModule τ K)) (rootVec τ K α) = torusRootChar h α • rootVec τ K α :=
  apply_rootVec_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh) hα

theorem conj_pinnedX_of_mem_torusGroup
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (torusRootChar h α * c) := by
  rw [torusGroup] at hh
  induction hh using Subgroup.closure_induction generalizing c with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    rw [root_torus_conjugation i hα t c, torusRootChar_torusElt i t hα]
  | one => rw [one_mul, inv_one, mul_one, torusRootChar_one, one_mul]
  | mul x y hx hy ihx ihy =>
    have hx' : x ∈ diagonalGroup := torusGroup_le_diagonalGroup hx
    have hy' : y ∈ diagonalGroup := torusGroup_le_diagonalGroup hy
    rw [torusRootChar_mul hx' hy', mul_assoc (torusRootChar x α), ← ihx, ← ihy]
    group
  | inv x hx ihx =>
    have hx' : x ∈ diagonalGroup := torusGroup_le_diagonalGroup hx
    have e := ihx ((torusRootChar x α)⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ (torusRootChar_ne_zero hx' α), one_mul] at e
    rw [torusRootChar_inv hx', ← e]
    group

theorem eq_torusRootChar_of_conj
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {s : K}
    (hs : ∀ c : K, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (s * c)) :
    s = torusRootChar h α := by
  have h1 := (hs 1).symm.trans (conj_pinnedX_of_mem_torusGroup hh hα 1)
  simpa using pinnedX_injective τ K α h1

theorem commute_pinnedX_iff
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : (∀ c : K, h * pinnedX τ K α c = pinnedX τ K α c * h) ↔
      torusRootChar h α = 1 := by
  constructor
  · intro hc
    refine (eq_torusRootChar_of_conj hh hα fun c => ?_).symm
    rw [hc, mul_inv_cancel_right, one_mul]
  · intro h1 c
    have e := conj_pinnedX_of_mem_torusGroup hh hα c
    rw [h1, one_mul] at e
    calc h * pinnedX τ K α c = h * pinnedX τ K α c * h⁻¹ * h := by group
      _ = pinnedX τ K α c * h := by rw [e]

theorem torusRootChar_supportedTorusHom
    (J : Set (Fin τ.rank)) [Fintype J] (a : J → Kˣ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusRootChar (supportedTorusHom τ K J a) α =
      ((∏ j : J, a j ^ (∑ i, τ.cartan j i * α i) : Kˣ) : K) := by
  have hdiag : ∀ b : J → Kˣ, supportedTorusHom τ K J b ∈ diagonalGroup := fun b =>
    torusGroup_le_diagonalGroup (supportedTorus_le_torusGroup J (supportedTorusHom_mem J b))
  let f : (J → Kˣ) →* K :=
    { toFun := fun b => torusRootChar (supportedTorusHom τ K J b) α
      map_one' := by simp only [map_one, torusRootChar_one]
      map_mul' := fun b b' => by
        simp only [map_mul]
        exact torusRootChar_mul (hdiag b) (hdiag b') α }
  let g : (J → Kˣ) →* K :=
    { toFun := fun b => ((∏ j : J, b j ^ (∑ i, τ.cartan j i * α i) : Kˣ) : K)
      map_one' := by simp
      map_mul' := fun b b' => by
        simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul] }
  have hfg : f = g := MonoidHom.functions_ext K f g fun j t => by
    simp only [f, g, MonoidHom.coe_mk, OneHom.coe_mk, supportedTorusHom_mulSingle,
      torusRootChar_torusElt _ _ hα]
    congr 1
    rw [Finset.prod_eq_single j (fun j' _ hj' => by rw [Pi.mulSingle_eq_of_ne hj', one_zpow])
      (fun h => absurd (Finset.mem_univ j) h), Pi.mulSingle_eq_same]
  exact DFunLike.congr_fun hfg a

theorem supportedTorusHom_eq_one_iff
    (J : Set (Fin τ.rank)) [Fintype J] (a : J → Kˣ) :
    supportedTorusHom τ K J a = 1 ↔ ∀ i : Fin τ.rank, ∏ j : J, a j ^ τ.cartan j i = 1 := by
  have hH : supportedTorusHom τ K J a ∈ torusGroup τ K :=
    supportedTorus_le_torusGroup J (supportedTorusHom_mem J a)
  constructor
  · intro h i
    have h1 := torusRootChar_supportedTorusHom J a (isRoot_single τ i)
    rw [h, torusRootChar_one] at h1
    have hs : ∀ j : J, ∑ k, τ.cartan j k * (Pi.single i 1 : Fin τ.rank → ℤ) k =
        τ.cartan j i := fun j => by
      rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one]
    simp only [hs] at h1
    exact Units.ext h1.symm
  · intro h
    have hprod : ∀ α : Fin τ.rank → ℤ, ∏ j : J, a j ^ (∑ i, τ.cartan j i * α i) = 1 := by
      intro α
      calc ∏ j : J, a j ^ (∑ i, τ.cartan j i * α i) =
            ∏ j : J, ∏ i, (a j ^ τ.cartan j i) ^ α i := by
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [← prod_zpow_eq_zpow_sum]
            exact Finset.prod_congr rfl fun i _ => zpow_mul _ _ _
        _ = ∏ i, ∏ j : J, (a j ^ τ.cartan j i) ^ α i := Finset.prod_comm
        _ = ∏ i, (∏ j : J, a j ^ τ.cartan j i) ^ α i :=
            Finset.prod_congr rfl fun i _ => Finset.prod_zpow _ _ _
        _ = 1 := by simp only [h, one_zpow, Finset.prod_const_one]
    refine Units.ext (rootModule_end_ext (fun k => ?_) (fun α hα => ?_))
    · rw [Units.val_one, Module.End.one_apply]
      exact (torusGroup_le_diagonalGroup hH).1 k
    · rw [apply_rootVec_of_mem_torusGroup hH hα, torusRootChar_supportedTorusHom J a hα, hprod,
        Units.val_one, one_smul, Units.val_one, Module.End.one_apply]

end CFSG.LieType.Chevalley
