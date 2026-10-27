module

public import CFSG.LieType.Steinberg.Adjoint.Unipotent
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem torus_commute {i j : Fin τ.rank} {g h : adjointGroup τ K} (hg : g ∈ torus K i)
    (hh : h ∈ torus K j) : Commute g h := by
  obtain ⟨t, rfl⟩ := hg
  obtain ⟨u, rfl⟩ := hh
  exact Subtype.ext (torusElt_mul_comm i j t u)

@[expose] def wtChar (t : Fin τ.rank → Kˣ) (μ : Fin τ.rank → ℤ) : Kˣ :=
  ∏ j, t j ^ (∑ l, τ.cartan j l * μ l)

theorem wtChar_one (μ : Fin τ.rank → ℤ) : wtChar (τ := τ) (fun _ => (1 : Kˣ)) μ = 1 := by
  simp [wtChar]

theorem wtChar_mul (t u : Fin τ.rank → Kˣ) (μ : Fin τ.rank → ℤ) :
    wtChar (t * u) μ = wtChar t μ * wtChar u μ := by
  simp only [wtChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem wtChar_inv (t : Fin τ.rank → Kˣ) (μ : Fin τ.rank → ℤ) :
    wtChar t⁻¹ μ = (wtChar t μ)⁻¹ := by
  simp only [wtChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem wtChar_mulSingle (j : Fin τ.rank) (s : Kˣ) (μ : Fin τ.rank → ℤ) :
    wtChar (Pi.mulSingle j s) μ = s ^ (∑ l, τ.cartan j l * μ l) := by
  rw [wtChar, Finset.prod_eq_single j]
  · rw [Pi.mulSingle_eq_same]
  · intro b _ hb
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]
  · intro h
    exact absurd (Finset.mem_univ j) h

variable (K) in
@[expose] def charSub (i : Fin τ.rank) : Subgroup (adjointGroup τ K) where
  carrier := {g | ∃ t : Fin τ.rank → Kˣ, t i = 1 ∧ ∀ b : Label τ,
    endHom K g (Finsupp.single b 1) = ((wtChar t (labelWt τ b) : Kˣ) : K) • Finsupp.single b 1}
  mul_mem' {g h} := by
    rintro ⟨t, ht, hg⟩ ⟨u, hu, hh⟩
    refine ⟨t * u, by simp [ht, hu], fun b => ?_⟩
    rw [map_mul, Module.End.mul_apply, hh, map_smul, hg, smul_smul, wtChar_mul, Units.val_mul,
      mul_comm]
  one_mem' := ⟨fun _ => 1, rfl, fun b => by simp [wtChar_one]⟩
  inv_mem' {g} := by
    rintro ⟨t, ht, hg⟩
    refine ⟨t⁻¹, by simp [ht], fun b => ?_⟩
    have h1 : endHom K g (endHom K g⁻¹ (Finsupp.single b 1)) = Finsupp.single b 1 := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h2 : endHom K g (((wtChar t⁻¹ (labelWt τ b) : Kˣ) : K) • Finsupp.single b 1) =
        Finsupp.single b 1 := by
      rw [map_smul, hg, smul_smul, wtChar_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_smul]
    have hinj : Function.Injective (endHom K g) := by
      intro x y hxy
      have := congrArg (endHom K g⁻¹) hxy
      rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, Module.End.one_apply] at this
    exact hinj (h1.trans h2.symm)

theorem torus_le_charSub {i j : Fin τ.rank} (hij : j ≠ i) : torus K j ≤ charSub K i := by
  rintro _ ⟨s, rfl⟩
  refine ⟨Pi.mulSingle j s, by simp [hij.symm], fun b => ?_⟩
  rw [wtChar_mulSingle]
  exact torusElt_single j s b

theorem zpow_finset_sum {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow_cartan {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hB : τ.cartan * B = 1) {u : Fin τ.rank → Kˣ}
    (hu : ∀ m, ∏ j, u j ^ τ.cartan j m = 1) (l : Fin τ.rank) : u l = 1 := by
  have key : ∏ m, (∏ j, u j ^ τ.cartan j m) ^ B m l = u l := by
    simp only [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    simp only [← zpow_finset_sum]
    have h : ∀ j, ∑ m, τ.cartan j m * B m l = if j = l then 1 else 0 := fun j => by
      have := congrFun (congrFun hB j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    simp only [h]
    rw [Finset.prod_eq_single l]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ l) h
  rw [← key]
  simp [hu]

theorem torus_iSupIndep {B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hB : τ.cartan * B = 1) :
    iSupIndep (torus (τ := τ) K) := by
  intro i
  rw [disjoint_iff]
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgi, hgj⟩ := Subgroup.mem_inf.1 hg
  have hle : (⨆ (j) (_ : j ≠ i), torus K j) ≤ charSub K i :=
    iSup₂_le fun j hj => torus_le_charSub hj
  obtain ⟨t, ht, hchar⟩ := hle hgj
  obtain ⟨s, rfl⟩ := hgi
  have hm : ∀ m, s ^ τ.cartan i m = ∏ j, t j ^ τ.cartan j m := by
    intro m
    have h1 := torusElt_single i s (Sum.inr ⟨Pi.single m 1, isRoot_single τ m⟩)
    have h2 := hchar (Sum.inr ⟨Pi.single m 1, isRoot_single τ m⟩)
    have hsum : ∀ j, ∑ l, τ.cartan j l * labelWt τ
        (Sum.inr ⟨Pi.single m 1, isRoot_single τ m⟩ : Label τ) l = τ.cartan j m := by
      intro j
      simp [labelWt, Pi.single_apply]
    simp only [hsum] at h1
    rw [wtChar] at h2
    simp only [hsum] at h2
    have h3 : (torusHom K i s : adjointGroup τ K) = torusElement τ K i s := rfl
    rw [endHom_apply, h3] at h2
    change (torusElt τ K i s : Module.End K (RootModule τ K)) _ = _ at h2
    rw [h1] at h2
    have h4 := congrArg (fun x : RootModule τ K =>
      x (Sum.inr ⟨Pi.single m 1, isRoot_single τ m⟩)) h2
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h4
    exact Units.ext h4
  set u : Fin τ.rank → Kˣ := Function.update t i s⁻¹ with hu_def
  have hu : ∀ m, ∏ j, u j ^ τ.cartan j m = 1 := by
    intro m
    have e : ∏ j, u j ^ τ.cartan j m = (s⁻¹) ^ τ.cartan i m * ∏ j, t j ^ τ.cartan j m := by
      rw [← Finset.mul_prod_erase Finset.univ (fun j => u j ^ τ.cartan j m) (Finset.mem_univ i),
        ← Finset.mul_prod_erase Finset.univ (fun j => t j ^ τ.cartan j m) (Finset.mem_univ i),
        ht, one_zpow, one_mul, hu_def, Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [e, ← hm, inv_zpow, inv_mul_cancel]
  have hs : s⁻¹ = 1 := by
    have := eq_one_of_prod_zpow_cartan hB hu i
    rwa [hu_def, Function.update_self] at this
  rw [inv_eq_one.1 hs, map_one]
  exact one_mem _

theorem iSup_torus_inf_unip (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    (⨆ i, torus (τ := τ) K i) ⊓ unip φ = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ (iSup_le fun i => torus_le_diag i)).trans
    (diag_inf_unip φ).le)

end CFSG.LieType.Steinberg.Adjoint
