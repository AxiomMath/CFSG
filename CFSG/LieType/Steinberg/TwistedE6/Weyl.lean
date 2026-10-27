module

public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {k : Type*} [Field k] (θ : k →+* k)

theorem twReflectHom_zero (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom (nf 0) v = reflect .E6 (nd 1) v := rfl

theorem twReflectHom_one (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom (nf 1) v = reflect .E6 (nd 3) v := rfl

theorem twReflectHom_two (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom (nf 2) v = reflect .E6 (nd 2) (reflect .E6 (nd 4) v) := rfl

theorem twReflectHom_three (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom (nf 3) v = reflect .E6 (nd 0) (reflect .E6 (nd 5) v) := rfl

theorem isRoot_twReflect (i : Fin (Tag.rank .F4)) {v : Fin (Tag.rank .E6) → ℤ}
    (hv : IsRoot .E6 v) : IsRoot .E6 (twReflectHom i v) := by
  fin_cases i
  · exact hv.reflect (nd 1)
  · exact hv.reflect (nd 3)
  · exact (hv.reflect (nd 4)).reflect (nd 2)
  · exact (hv.reflect (nd 5)).reflect (nd 0)

theorem twReflect_rho (i : Fin (Tag.rank .F4)) (v : Fin (Tag.rank .E6) → ℤ) :
    twReflectHom i (rho v) = rho (twReflectHom i v) := by
  have h : (twReflectHom i).comp rhoHom = rhoHom.comp (twReflectHom i) :=
    addMonoidHom_ext_single fun l => by
      revert i l
      decide
  exact DFunLike.congr_fun h v

theorem nHatE_conj_mem {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (i : Fin (Tag.rank .F4))
    {x : e6Data_valid.minGroup k} (hx : x ∈ e6Data_valid.rootGroup k γ) :
    nHatE k i * x * (nHatE k i)⁻¹ ∈ e6Data_valid.rootGroup k (twReflectHom i γ) := by
  have key : ∀ (a : Fin (Tag.rank .E6)) {δ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 δ →
      ∀ y ∈ e6Data_valid.rootGroup k δ, e6Data_valid.nm k a * y * (e6Data_valid.nm k a)⁻¹ ∈
        e6Data_valid.rootGroup k (reflect .E6 a δ) := by
    intro a δ hδ y hy
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
    obtain ⟨σ, -, h⟩ := e6Data_valid.nm_conj_xm k hδ a
    rw [h]
    exact e6Data_valid.xm_mem_rootGroup k _ _
  have key2 : ∀ (a b : Fin (Tag.rank .E6)) {δ : Fin (Tag.rank .E6) → ℤ}, IsRoot .E6 δ →
      ∀ y ∈ e6Data_valid.rootGroup k δ,
        e6Data_valid.nm k a * e6Data_valid.nm k b * y *
            (e6Data_valid.nm k a * e6Data_valid.nm k b)⁻¹ ∈
          e6Data_valid.rootGroup k (reflect .E6 a (reflect .E6 b δ)) := by
    intro a b δ hδ y hy
    have e : e6Data_valid.nm k a * e6Data_valid.nm k b * y *
        (e6Data_valid.nm k a * e6Data_valid.nm k b)⁻¹ =
          e6Data_valid.nm k a * (e6Data_valid.nm k b * y * (e6Data_valid.nm k b)⁻¹) *
            (e6Data_valid.nm k a)⁻¹ := by group
    rw [e]
    exact key a (hδ.reflect b) _ (key b hδ y hy)
  fin_cases i
  · exact key (nd 1) hγ x hx
  · exact key (nd 3) hγ x hx
  · exact key2 (nd 2) (nd 4) hγ x hx
  · exact key2 (nd 0) (nd 5) hγ x hx

theorem nHat_conj_mem (i : Fin (Tag.rank .F4)) {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    {x : fixedGroup k θ} (hx : x ∈ twistedRootGroup k θ β) :
    nHat θ i * x * (nHat θ i)⁻¹ ∈ twistedRootGroup k θ (reflect .F4 i β) := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  have hw := isRoot_twReflect i hα
  have hpw : proj (twReflectHom i α) = reflect .F4 i β := by rw [proj_twReflect, hp]
  rw [mem_twistedRootGroup_iff θ hα hp] at hx
  rw [mem_twistedRootGroup_iff θ hw hpw]
  have hle : ∀ γ, IsRoot .E6 γ → (e6Data_valid.rootGroup k γ).map
      (MulAut.conj (nHatE k i)).toMonoidHom ≤ e6Data_valid.rootGroup k (twReflectHom i γ) := by
    intro γ hγ
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    exact nHatE_conj_mem hγ i hy
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj (nHatE k i)).toMonoidHom hx
  rw [Subgroup.map_sup] at h1
  have h2 := sup_le_sup (hle α hα) (hle (rho α) (isRoot_rho hα)) h1
  rw [twReflect_rho] at h2
  exact h2

theorem braid_fold {G : Type*} [Group G] {a b c : G} (hac : a * c = c * a)
    (hab : a * b * a = b * a * b) (hcb : c * b * c = b * c * b) :
    b * (a * c) * b * (a * c) = a * c * b * (a * c) * b := by
  have hac' : ∀ x, a * (c * x) = c * (a * x) := fun x => by
    rw [← mul_assoc, hac, mul_assoc]
  have hab' : ∀ x, a * (b * (a * x)) = b * (a * (b * x)) := fun x => by
    calc a * (b * (a * x)) = a * b * a * x := by simp only [mul_assoc]
      _ = b * a * b * x := by rw [hab]
      _ = b * (a * (b * x)) := by simp only [mul_assoc]
  have hcb' : ∀ x, c * (b * (c * x)) = b * (c * (b * x)) := fun x => by
    calc c * (b * (c * x)) = c * b * c * x := by simp only [mul_assoc]
      _ = b * c * b * x := by rw [hcb]
      _ = b * (c * (b * x)) := by simp only [mul_assoc]
  have hab0 : a * (b * a) = b * (a * b) := by rw [← mul_assoc, hab, mul_assoc]
  simp only [mul_assoc]
  rw [hac, hcb' a, ← hab' (c * (b * a)), hac' (b * a), hab0, ← hcb' (a * b), ← hac' b]

theorem nHatE_zero : nHatE k (nf 0) = e6Data_valid.nm k (nd 1) := rfl

theorem nHatE_one : nHatE k (nf 1) = e6Data_valid.nm k (nd 3) := rfl

theorem nHatE_two : nHatE k (nf 2) = e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) := rfl

theorem nHatE_three : nHatE k (nf 3) = e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) :=
  rfl

theorem nm_commute {a b : Fin (Tag.rank .E6)} (hab : a ≠ b) (h : Tag.cartan .E6 a b = 0) :
    Commute (e6Data_valid.nm k a) (e6Data_valid.nm k b) :=
  e6Data_valid.nm_comm k hab h

theorem nHatE_comm_02 : nHatE k (nf 0) * nHatE k (nf 2) = nHatE k (nf 2) * nHatE k (nf 0) :=
  ((nm_commute (a := nd 1) (b := nd 2) (by decide) (by decide)).mul_right
    (nm_commute (a := nd 1) (b := nd 4) (by decide) (by decide))).eq

theorem nHatE_comm_03 : nHatE k (nf 0) * nHatE k (nf 3) = nHatE k (nf 3) * nHatE k (nf 0) :=
  ((nm_commute (a := nd 1) (b := nd 0) (by decide) (by decide)).mul_right
    (nm_commute (a := nd 1) (b := nd 5) (by decide) (by decide))).eq

theorem nHatE_comm_13 : nHatE k (nf 1) * nHatE k (nf 3) = nHatE k (nf 3) * nHatE k (nf 1) :=
  ((nm_commute (a := nd 3) (b := nd 0) (by decide) (by decide)).mul_right
    (nm_commute (a := nd 3) (b := nd 5) (by decide) (by decide))).eq

theorem nHatE_braid_01 : nHatE k (nf 1) * (nHatE k (nf 0) * nHatE k (nf 1)) =
    nHatE k (nf 0) * (nHatE k (nf 1) * nHatE k (nf 0)) := by
  rw [nHatE_zero, nHatE_one, ← mul_assoc, ← mul_assoc]
  exact (e6Data_valid.nm_braid k (i := nd 1) (j := nd 3) (by decide) (by decide)).symm

theorem nHatE_braid_12 : nHatE k (nf 1) * (nHatE k (nf 2) * (nHatE k (nf 1) * nHatE k (nf 2))) =
    nHatE k (nf 2) * (nHatE k (nf 1) * (nHatE k (nf 2) * nHatE k (nf 1))) := by
  have h := braid_fold (nm_comm_24 (k := k))
    (e6Data_valid.nm_braid k (i := nd 2) (j := nd 3) (by decide) (by decide))
    (e6Data_valid.nm_braid k (i := nd 4) (j := nd 3) (by decide) (by decide))
  rw [nHatE_one, nHatE_two]
  simp only [mul_assoc] at h ⊢
  exact h

theorem nHatE_braid_23 : nHatE k (nf 3) * (nHatE k (nf 2) * nHatE k (nf 3)) =
    nHatE k (nf 2) * (nHatE k (nf 3) * nHatE k (nf 2)) := by
  rw [nHatE_two, nHatE_three]
  have c25 := nm_commute (k := k) (a := nd 2) (b := nd 5) (by decide) (by decide)
  have c05 := nm_commute (k := k) (a := nd 0) (b := nd 5) (by decide) (by decide)
  have c04 := nm_commute (k := k) (a := nd 0) (b := nd 4) (by decide) (by decide)
  have c24 := nm_commute (k := k) (a := nd 2) (b := nd 4) (by decide) (by decide)
  calc e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) *
        (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) *
          (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5))) =
      e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5) *
        (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)) *
          (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)) := by
        rw [← mul_assoc]
    _ = e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 0) *
          (e6Data_valid.nm k (nd 5) * e6Data_valid.nm k (nd 4) * e6Data_valid.nm k (nd 5)) :=
        (mul_mul_mul_rearrange c25 c05 c04).symm
    _ = e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 2) *
          (e6Data_valid.nm k (nd 4) * e6Data_valid.nm k (nd 5) * e6Data_valid.nm k (nd 4)) := by
        rw [e6Data_valid.nm_braid k (i := nd 0) (j := nd 2) (by decide) (by decide),
          e6Data_valid.nm_braid k (i := nd 5) (j := nd 4) (by decide) (by decide)]
    _ = e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4) *
          (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)) *
            (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)) :=
        mul_mul_mul_rearrange c04 c24 c25
    _ = _ := by rw [mul_assoc]

theorem alternatingWord_two {ι : Type*} (i j : ι) :
    CoxeterSystem.alternatingWord i j 2 = [i, j] := by
  simp [CoxeterSystem.alternatingWord]

theorem alternatingWord_three {ι : Type*} (i j : ι) :
    CoxeterSystem.alternatingWord i j 3 = [j, i, j] := by
  simp [CoxeterSystem.alternatingWord]

theorem alternatingWord_four {ι : Type*} (i j : ι) :
    CoxeterSystem.alternatingWord i j 4 = [i, j, i, j] := by
  simp [CoxeterSystem.alternatingWord]

theorem nHatE_braidWord (i j : Fin (Tag.rank .F4)) :
    ((CoxeterSystem.braidWord (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      i j).map (nHatE k)).prod =
    ((CoxeterSystem.braidWord (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      j i).map (nHatE k)).prod := by
  have e01 : Tag.cartan .F4 (nf 0) (nf 1) * Tag.cartan .F4 (nf 1) (nf 0) = 1 := by decide
  have e10 : Tag.cartan .F4 (nf 1) (nf 0) * Tag.cartan .F4 (nf 0) (nf 1) = 1 := by decide
  have e02 : Tag.cartan .F4 (nf 0) (nf 2) * Tag.cartan .F4 (nf 2) (nf 0) = 0 := by decide
  have e20 : Tag.cartan .F4 (nf 2) (nf 0) * Tag.cartan .F4 (nf 0) (nf 2) = 0 := by decide
  have e03 : Tag.cartan .F4 (nf 0) (nf 3) * Tag.cartan .F4 (nf 3) (nf 0) = 0 := by decide
  have e30 : Tag.cartan .F4 (nf 3) (nf 0) * Tag.cartan .F4 (nf 0) (nf 3) = 0 := by decide
  have e12 : Tag.cartan .F4 (nf 1) (nf 2) * Tag.cartan .F4 (nf 2) (nf 1) = 2 := by decide
  have e21 : Tag.cartan .F4 (nf 2) (nf 1) * Tag.cartan .F4 (nf 1) (nf 2) = 2 := by decide
  have e13 : Tag.cartan .F4 (nf 1) (nf 3) * Tag.cartan .F4 (nf 3) (nf 1) = 0 := by decide
  have e31 : Tag.cartan .F4 (nf 3) (nf 1) * Tag.cartan .F4 (nf 1) (nf 3) = 0 := by decide
  have e23 : Tag.cartan .F4 (nf 2) (nf 3) * Tag.cartan .F4 (nf 3) (nf 2) = 1 := by decide
  have e32 : Tag.cartan .F4 (nf 3) (nf 2) * Tag.cartan .F4 (nf 2) (nf 3) = 1 := by decide
  simp only [CoxeterSystem.braidWord, coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [e01, e10, e02, e20, e03, e30, e12, e21, e13, e31, e23, e32,
      TauCeti.coxeterOrder_zero, TauCeti.coxeterOrder_one, TauCeti.coxeterOrder_two,
      alternatingWord_two, alternatingWord_three, alternatingWord_four, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exacts [nHatE_braid_01, nHatE_comm_02, nHatE_comm_03, nHatE_braid_01.symm, nHatE_braid_12,
    nHatE_comm_13, nHatE_comm_02.symm, nHatE_braid_12.symm, nHatE_braid_23, nHatE_comm_03.symm,
    nHatE_comm_13.symm, nHatE_braid_23.symm]

theorem nHat_braidWord (i j : Fin (Tag.rank .F4)) :
    ((CoxeterSystem.braidWord (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      i j).map (nHat θ)).prod =
    ((CoxeterSystem.braidWord (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      j i).map (nHat θ)).prod := by
  apply Subtype.ext
  rw [Subgroup.val_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map]
  exact nHatE_braidWord i j

theorem units_map_neg_one : Units.map (θ : k →* k) (-1) = -1 :=
  Units.ext (by rw [Units.coe_map, Units.val_neg, Units.val_one, MonoidHom.coe_ofClass, map_neg,
    map_one])

theorem neg_one_mem_fixedUnits : (-1 : kˣ) ∈ fixedUnits θ := by
  rw [mem_fixedUnits, Units.val_neg, Units.val_one, map_neg, map_one]

theorem nHat_sq_mem (i : Fin (Tag.rank .F4)) : nHat θ i ^ 2 ∈ hHat k θ i := by
  rw [hHat, Subgroup.mem_subgroupOf, Subgroup.coe_pow, nHat_val]
  fin_cases i
  · exact ⟨⟨-1, neg_one_mem_fixedUnits θ⟩, (e6Data_valid.nm_sq k (nd 1)).symm⟩
  · exact ⟨⟨-1, neg_one_mem_fixedUnits θ⟩, (e6Data_valid.nm_sq k (nd 3)).symm⟩
  · refine ⟨-1, ?_⟩
    change e6Data_valid.hm k (nd 2) (-1) * e6Data_valid.hm k (nd 4) (Units.map (θ : k →* k) (-1)) =
      (e6Data_valid.nm k (nd 2) * e6Data_valid.nm k (nd 4)) ^ 2
    rw [units_map_neg_one, (nm_commute (a := nd 2) (b := nd 4) (by decide) (by decide)).mul_pow,
      e6Data_valid.nm_sq, e6Data_valid.nm_sq]
  · refine ⟨-1, ?_⟩
    change e6Data_valid.hm k (nd 0) (-1) * e6Data_valid.hm k (nd 5) (Units.map (θ : k →* k) (-1)) =
      (e6Data_valid.nm k (nd 0) * e6Data_valid.nm k (nd 5)) ^ 2
    rw [units_map_neg_one, (nm_commute (a := nd 0) (b := nd 5) (by decide) (by decide)).mul_pow,
      e6Data_valid.nm_sq, e6Data_valid.nm_sq]

theorem hHatE_le_iSup_torus (i : Fin (Tag.rank .F4)) :
    hHatE k θ i ≤ ⨆ a, e6Data_valid.torus k a := by
  fin_cases i
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_iSup_of_mem (nd 1) (e6Data_valid.hm_mem_torus k _ _)
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.mem_iSup_of_mem (nd 3) (e6Data_valid.hm_mem_torus k _ _)
  · rintro _ ⟨t, rfl⟩
    exact mul_mem (Subgroup.mem_iSup_of_mem (nd 2) (e6Data_valid.hm_mem_torus k _ _))
      (Subgroup.mem_iSup_of_mem (nd 4) (e6Data_valid.hm_mem_torus k _ _))
  · rintro _ ⟨t, rfl⟩
    exact mul_mem (Subgroup.mem_iSup_of_mem (nd 0) (e6Data_valid.hm_mem_torus k _ _))
      (Subgroup.mem_iSup_of_mem (nd 5) (e6Data_valid.hm_mem_torus k _ _))

theorem conj_mem_rootGroup_of_mem_iSup_torus {g : e6Data_valid.minGroup k}
    (hg : g ∈ ⨆ a, e6Data_valid.torus k a) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ)
    {y : e6Data_valid.minGroup k} (hy : y ∈ e6Data_valid.rootGroup k γ) :
    g * y * g⁻¹ ∈ e6Data_valid.rootGroup k γ := by
  refine Subgroup.iSup_induction _ (C := fun g => ∀ y ∈ e6Data_valid.rootGroup k γ,
    g * y * g⁻¹ ∈ e6Data_valid.rootGroup k γ) hg (fun a x hx => ?_) (fun y hy => ?_)
    (fun x x' hx hx' y hy => ?_) y hy
  · intro y hy
    obtain ⟨t, rfl⟩ := (e6Data_valid.mem_torus k).1 hx
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hy
    rw [e6Data_valid.hm_conj_xm k hγ]
    exact e6Data_valid.xm_mem_rootGroup k _ _
  · rwa [one_mul, inv_one, mul_one]
  · have e : x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hx' y hy)

theorem hHat_conj_mem (l : Fin (Tag.rank .F4)) {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    {h : fixedGroup k θ} (hh : h ∈ hHat k θ l) {x : fixedGroup k θ}
    (hx : x ∈ twistedRootGroup k θ β) : h * x * h⁻¹ ∈ twistedRootGroup k θ β := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  rw [mem_twistedRootGroup_iff θ hα hp] at hx ⊢
  rw [hHat, Subgroup.mem_subgroupOf] at hh
  have hg := hHatE_le_iSup_torus θ l hh
  have hle : ∀ γ, IsRoot .E6 γ → (e6Data_valid.rootGroup k γ).map
      (MulAut.conj (h : e6Data_valid.minGroup k)).toMonoidHom ≤ e6Data_valid.rootGroup k γ := by
    intro γ hγ
    rw [Subgroup.map_le_iff_le_comap]
    intro y hy
    exact conj_mem_rootGroup_of_mem_iSup_torus hg hγ hy
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj (h : e6Data_valid.minGroup k)).toMonoidHom hx
  rw [Subgroup.map_sup] at h1
  exact sup_le_sup (hle α hα) (hle (rho α) (isRoot_rho hα)) h1

variable (k) in
@[expose] def torusHom : (Fin (Tag.rank .E6) → kˣ) →* e6Data_valid.minGroup k :=
  MonoidHom.noncommPiCoprod (fun a => e6Data_valid.hHom k a) (by
    intro a b _ s t
    exact hm_commute a b s t)

theorem torusHom_mulSingle (a : Fin (Tag.rank .E6)) (t : kˣ) :
    torusHom k (Pi.mulSingle a t) = e6Data_valid.hm k a t := by
  rw [torusHom, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

@[expose] def chiHom (c : Fin (Tag.rank .E6)) : (Fin (Tag.rank .E6) → kˣ) →* kˣ where
  toFun u := ∏ a, u a ^ (-Tag.cartan .E6 a c)
  map_one' := by simp
  map_mul' u v := by simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem chiHom_apply (c : Fin (Tag.rank .E6)) (u : Fin (Tag.rank .E6) → kˣ) :
    chiHom c u = ∏ a, u a ^ (-Tag.cartan .E6 a c) := rfl

theorem chiHom_mulSingle (c a : Fin (Tag.rank .E6)) (t : kˣ) :
    chiHom c (Pi.mulSingle a t) = t ^ (-Tag.cartan .E6 a c) := by
  rw [chiHom_apply, Finset.prod_eq_single a (fun b _ hb => by
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]) (by simp), Pi.mulSingle_eq_same]

theorem nm_conj_torusHom (c : Fin (Tag.rank .E6)) (u : Fin (Tag.rank .E6) → kˣ) :
    e6Data_valid.nm k c * torusHom k u * (e6Data_valid.nm k c)⁻¹ =
      torusHom k (u * Pi.mulSingle c (chiHom c u)) := by
  have h : (MulAut.conj (e6Data_valid.nm k c)).toMonoidHom.comp (torusHom k) =
      (torusHom k).comp
        (MonoidHom.id _ * (MonoidHom.mulSingle (fun _ => kˣ) c).comp (chiHom c)) := by
    refine MonoidHom.pi_ext fun a t => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.mulSingle_apply, map_mul,
      torusHom_mulSingle, chiHom_mulSingle]
    exact e6Data_valid.nm_conj_hm k c a t
  exact DFunLike.congr_fun h u

@[expose] def IsSymU (u : Fin (Tag.rank .E6) → kˣ) : Prop :=
  ∀ a, u (rhoPerm a) = Units.map (θ : k →* k) (u a)

theorem rhoPerm_apply_rhoPerm (a : Fin (Tag.rank .E6)) : rhoPerm (rhoPerm a) = a := by
  revert a
  decide

theorem cartan_rhoPerm_rhoPerm (a c : Fin (Tag.rank .E6)) :
    Tag.cartan .E6 (rhoPerm a) (rhoPerm c) = Tag.cartan .E6 a c :=
  TwistTag.cartan_perm .E6 a c

theorem chiHom_rho {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) (c : Fin (Tag.rank .E6)) :
    chiHom (rhoPerm c) u = Units.map (θ : k →* k) (chiHom c u) := by
  calc chiHom (rhoPerm c) u =
        ∏ a, u (rhoPerm a) ^ (-Tag.cartan .E6 (rhoPerm a) (rhoPerm c)) :=
      (Equiv.prod_comp rhoPerm (fun a => u a ^ (-Tag.cartan .E6 a (rhoPerm c)))).symm
    _ = ∏ a, Units.map (θ : k →* k) (u a ^ (-Tag.cartan .E6 a c)) :=
      Finset.prod_congr rfl fun a _ => by rw [hu a, map_zpow, cartan_rhoPerm_rhoPerm]
    _ = Units.map (θ : k →* k) (chiHom c u) := by rw [chiHom_apply, map_prod]

theorem isSymU_mulSingle_fixed {c : Fin (Tag.rank .E6)} (hc : rhoPerm c = c) {s : kˣ}
    (hs : Units.map (θ : k →* k) s = s) : IsSymU θ (Pi.mulSingle c s) := by
  intro a
  by_cases ha : a = c
  · subst ha
    rw [hc, Pi.mulSingle_eq_same, hs]
  · have ha' : rhoPerm a ≠ c := fun h => ha (by rw [← rhoPerm_apply_rhoPerm a, h, hc])
    rw [Pi.mulSingle_eq_of_ne ha', Pi.mulSingle_eq_of_ne ha, map_one]

theorem isSymU_mulSingle_pair (hθ : ∀ c, θ (θ c) = c) {c : Fin (Tag.rank .E6)}
    (hc : rhoPerm c ≠ c) (s : kˣ) :
    IsSymU θ (Pi.mulSingle c s * Pi.mulSingle (rhoPerm c) (Units.map (θ : k →* k) s)) := by
  intro a
  by_cases h1 : a = c
  · rw [h1]
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hc,
      Pi.mulSingle_eq_of_ne (Ne.symm hc), one_mul, mul_one]
  by_cases h2 : a = rhoPerm c
  · rw [h2, rhoPerm_apply_rhoPerm]
    simp only [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hc,
      Pi.mulSingle_eq_of_ne (Ne.symm hc), one_mul, mul_one, units_map_map θ hθ]
  · have h3 : rhoPerm a ≠ c := fun h => h2 (by rw [← h, rhoPerm_apply_rhoPerm])
    have h4 : rhoPerm a ≠ rhoPerm c := fun h => h1 (rhoPerm.injective h)
    simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne h3, Pi.mulSingle_eq_of_ne h4,
      Pi.mulSingle_eq_of_ne h1, Pi.mulSingle_eq_of_ne h2, mul_one, map_one]

theorem conj_torusHom_pair {c : Fin (Tag.rank .E6)}
    (hdc : Tag.cartan .E6 (rhoPerm c) c = 0) {u : Fin (Tag.rank .E6) → kˣ} (hu : IsSymU θ u) :
    e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c) * torusHom k u *
        (e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c))⁻¹ =
      torusHom k u * (e6Data_valid.hm k c (chiHom c u) *
        e6Data_valid.hm k (rhoPerm c) (Units.map (θ : k →* k) (chiHom c u))) := by
  calc e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c) * torusHom k u *
        (e6Data_valid.nm k c * e6Data_valid.nm k (rhoPerm c))⁻¹ =
      e6Data_valid.nm k c * (e6Data_valid.nm k (rhoPerm c) * torusHom k u *
        (e6Data_valid.nm k (rhoPerm c))⁻¹) * (e6Data_valid.nm k c)⁻¹ := by group
    _ = e6Data_valid.nm k c * torusHom k (u * Pi.mulSingle (rhoPerm c) (chiHom (rhoPerm c) u)) *
        (e6Data_valid.nm k c)⁻¹ := by rw [nm_conj_torusHom (rhoPerm c) u]
    _ = torusHom k (u * Pi.mulSingle (rhoPerm c) (chiHom (rhoPerm c) u) *
        Pi.mulSingle c (chiHom c u)) := by
      rw [nm_conj_torusHom c, map_mul (chiHom c), chiHom_mulSingle, hdc, neg_zero, zpow_zero,
        mul_one]
    _ = _ := by
      rw [chiHom_rho θ hu, map_mul, map_mul, torusHom_mulSingle, torusHom_mulSingle, mul_assoc,
        (hm_commute _ _ _ _).eq]

theorem exists_torusHom_of_mem_hHatE (hθ : ∀ c, θ (θ c) = c) {l : Fin (Tag.rank .F4)}
    {x : e6Data_valid.minGroup k} (hx : x ∈ hHatE k θ l) :
    ∃ u, IsSymU θ u ∧ torusHom k u = x := by
  fin_cases l
  · obtain ⟨t, rfl⟩ := hx
    exact ⟨Pi.mulSingle (nd 1) t, isSymU_mulSingle_fixed θ rfl t.2, torusHom_mulSingle _ _⟩
  · obtain ⟨t, rfl⟩ := hx
    exact ⟨Pi.mulSingle (nd 3) t, isSymU_mulSingle_fixed θ rfl t.2, torusHom_mulSingle _ _⟩
  · obtain ⟨t, rfl⟩ := hx
    refine ⟨_, isSymU_mulSingle_pair θ hθ (c := nd 2) (by decide) t, ?_⟩
    rw [map_mul, torusHom_mulSingle, torusHom_mulSingle]
    rfl
  · obtain ⟨t, rfl⟩ := hx
    refine ⟨_, isSymU_mulSingle_pair θ hθ (c := nd 0) (by decide) t, ?_⟩
    rw [map_mul, torusHom_mulSingle, torusHom_mulSingle]
    rfl

theorem exists_conj_torusHom (j : Fin (Tag.rank .F4)) {u : Fin (Tag.rank .E6) → kˣ}
    (hu : IsSymU θ u) :
    ∃ v ∈ hHatE k θ j, nHatE k j * torusHom k u * (nHatE k j)⁻¹ = torusHom k u * v := by
  have hfix : ∀ c, rhoPerm c = c → chiHom c u ∈ fixedUnits θ := fun c hc => by
    have h := chiHom_rho θ hu c
    rw [hc] at h
    exact h.symm
  fin_cases j
  · refine ⟨_, ⟨⟨chiHom (nd 1) u, hfix (nd 1) rfl⟩, rfl⟩, ?_⟩
    change e6Data_valid.nm k (nd 1) * torusHom k u * (e6Data_valid.nm k (nd 1))⁻¹ =
      torusHom k u * e6Data_valid.hm k (nd 1) (chiHom (nd 1) u)
    rw [nm_conj_torusHom, map_mul, torusHom_mulSingle]
  · refine ⟨_, ⟨⟨chiHom (nd 3) u, hfix (nd 3) rfl⟩, rfl⟩, ?_⟩
    change e6Data_valid.nm k (nd 3) * torusHom k u * (e6Data_valid.nm k (nd 3))⁻¹ =
      torusHom k u * e6Data_valid.hm k (nd 3) (chiHom (nd 3) u)
    rw [nm_conj_torusHom, map_mul, torusHom_mulSingle]
  · exact ⟨_, ⟨chiHom (nd 2) u, rfl⟩, conj_torusHom_pair θ (c := nd 2) (by decide) hu⟩
  · exact ⟨_, ⟨chiHom (nd 0) u, rfl⟩, conj_torusHom_pair θ (c := nd 0) (by decide) hu⟩

theorem nHat_conj_hHat_mem (hθ : ∀ c, θ (θ c) = c) (j l : Fin (Tag.rank .F4))
    {h : fixedGroup k θ} (hh : h ∈ hHat k θ l) :
    nHat θ j * h * (nHat θ j)⁻¹ ∈ hHat k θ j ⊔ hHat k θ l := by
  have hh' := hh
  rw [hHat, Subgroup.mem_subgroupOf] at hh'
  obtain ⟨u, hu, hTu⟩ := exists_torusHom_of_mem_hHatE θ hθ hh'
  obtain ⟨v, hv, he⟩ := exists_conj_torusHom θ j hu
  have hvj : (⟨v, hHatE_le_fixedGroup θ hθ j hv⟩ : fixedGroup k θ) ∈ hHat k θ j := by
    rw [hHat, Subgroup.mem_subgroupOf]
    exact hv
  have heq : nHat θ j * h * (nHat θ j)⁻¹ = h * ⟨v, hHatE_le_fixedGroup θ hθ j hv⟩ := by
    apply Subtype.ext
    change nHatE k j * (h : e6Data_valid.minGroup k) * (nHatE k j)⁻¹ = (h : _) * v
    rw [← hTu, he]
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hvj)

end CFSG.LieType.Steinberg.TwistedE6
