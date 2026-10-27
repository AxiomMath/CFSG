module

public import CFSG.LieType.Steinberg.TwistedD4.Unipotent
public import Mathlib.GroupTheory.NoncommPiCoprod

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

variable {K : Type} [Field K] (σ : K →+* K)

local notation "𝕏" => rootGroup (rootOperatorFamily d4) K

local notation "𝕩" => xPar (rootOperatorFamily d4)

local notation "𝕃" => CurtisTits.rankOne (rootGroup (rootOperatorFamily d4) K)

theorem nHatE_conj_mem
    (i : Fin (Tag.rank .G2)) {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    {x : adjointGroup d4 K} (hx : x ∈ 𝕏 γ) :
    nHatE K i * x * (nHatE K i)⁻¹ ∈ 𝕏 (twReflectHom i γ) := by
  have key : ∀ (a : Fin d4.rank) {δ : Fin d4.rank → ℤ}, IsRoot d4 δ → ∀ y ∈ 𝕏 δ,
      Chevalley.weylElement d4 K a * y * (Chevalley.weylElement d4 K a)⁻¹ ∈ 𝕏 (reflect d4 a δ) :=
    fun a _ hδ y hy => weylElement_conj_mem a hδ hy
  match i with
  | ⟨0, _⟩ => exact key (nd 2) hγ x hx
  | ⟨1, _⟩ =>
    have e : nHatE K (ng 1) * x * (nHatE K (ng 1))⁻¹ =
        Chevalley.weylElement d4 K (nd 0) * (Chevalley.weylElement d4 K (nd 1) *
          (Chevalley.weylElement d4 K (nd 3) * x * (Chevalley.weylElement d4 K (nd 3))⁻¹) *
            (Chevalley.weylElement d4 K (nd 1))⁻¹) * (Chevalley.weylElement d4 K (nd 0))⁻¹ := by
      rw [nHatE_one]
      group
    rw [e]
    exact key (nd 0) ((hγ.reflect (nd 3)).reflect (nd 1)) _
      (key (nd 1) (hγ.reflect (nd 3)) _ (key (nd 3) hγ x hx))

theorem nHat_conj_mem
    (i : Fin (Tag.rank .G2)) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : IsRoot .G2 β) {x : twistedGroup σ} (hx : x ∈ twistedRootGroup σ β) :
    nHat σ i * x * (nHat σ i)⁻¹ ∈ twistedRootGroup σ (reflect .G2 i β) := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  have hw := isRoot_twReflect i hα
  have hpw : proj (twReflectHom i α) = reflect .G2 i β := by rw [proj_twReflect, hp]
  rw [mem_twistedRootGroup] at hx ⊢
  obtain ⟨hx1, hx2⟩ := (mem_twistedRootSubgroupD4_iff σ hα hp _).1 hx
  refine (mem_twistedRootSubgroupD4_iff σ hw hpw _).2 ⟨?_, ?_⟩
  · have hle : ∀ γ, IsRoot d4 γ → (𝕏 γ).map (MulAut.conj (nHatE K i)).toMonoidHom ≤
        𝕏 (twReflectHom i γ) := by
      intro γ hγ
      rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      exact nHatE_conj_mem i hγ hy
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj (nHatE K i)).toMonoidHom hx1
    rw [Subgroup.map_sup, Subgroup.map_sup] at h1
    have h2 := sup_le_sup (sup_le_sup (hle α hα) (hle _ (isRoot_rho hα)))
      (hle _ (isRoot_rho (isRoot_rho hα))) h1
    rw [twReflect_rho, twReflect_rho, twReflect_rho] at h2
    exact h2
  · have hn : twistC .D4 K σ (nHatE K i) = nHatE K i :=
      twistedGroup_le_twistFixed σ (nHat σ i).2
    change twistC .D4 K σ (nHatE K i * (x : adjointGroup d4 K) * (nHatE K i)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hn, hx2]
    rfl

@[expose] def braidWordLeft : List (Fin d4.rank) :=
  [nd 2, nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3]

@[expose] def braidWordRight : List (Fin d4.rank) :=
  [nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3, nd 2, nd 0, nd 1, nd 3, nd 2]

theorem isReduced_braidWordLeft :
    (coxeterSystem d4).IsReduced braidWordLeft :=
  isReduced_of_reducedCheck (by decide +kernel)

theorem isReduced_braidWordRight :
    (coxeterSystem d4).IsReduced braidWordRight :=
  isReduced_of_reducedCheck (by decide +kernel)

theorem wordProd_braidWordLeft :
    (coxeterSystem d4).wordProd braidWordLeft = (coxeterSystem d4).wordProd braidWordRight := by
  refine ext_single fun k => ?_
  rw [wordProd_smul, wordProd_smul]
  revert k
  decide +kernel

theorem nHatE_braid :
    nHatE K (ng 0) * (nHatE K (ng 1) * (nHatE K (ng 0) * (nHatE K (ng 1) *
      (nHatE K (ng 0) * nHatE K (ng 1))))) =
    nHatE K (ng 1) * (nHatE K (ng 0) * (nHatE K (ng 1) * (nHatE K (ng 0) *
      (nHatE K (ng 1) * nHatE K (ng 0))))) := by
  have h := (nrep_eq_prod d4 K isReduced_braidWordLeft).symm.trans
    ((congrArg (nrep d4 K) wordProd_braidWordLeft).trans
      (nrep_eq_prod d4 K isReduced_braidWordRight))
  simp only [braidWordLeft, braidWordRight, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] at h
  simp only [nHatE_zero, nHatE_one, mul_assoc]
  exact h

theorem alternatingWord_six {ι : Type*} (i j : ι) :
    CoxeterSystem.alternatingWord i j 6 = [i, j, i, j, i, j] := by
  simp [CoxeterSystem.alternatingWord]

theorem nHatE_braidWord
    (i j : Fin (Tag.rank .G2)) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan .G2)) i j).map
      (nHatE K)).prod =
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan .G2)) j i).map
      (nHatE K)).prod := by
  have e00 : Tag.cartan .G2 (ng 0) (ng 0) * Tag.cartan .G2 (ng 0) (ng 0) = 4 := by decide
  have e11 : Tag.cartan .G2 (ng 1) (ng 1) * Tag.cartan .G2 (ng 1) (ng 1) = 4 := by decide
  have e01 : Tag.cartan .G2 (ng 0) (ng 1) * Tag.cartan .G2 (ng 1) (ng 0) = 3 := by decide
  have e10 : Tag.cartan .G2 (ng 1) (ng 0) * Tag.cartan .G2 (ng 0) (ng 1) = 3 := by decide
  simp only [CoxeterSystem.braidWord, coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => rfl
  | ⟨1, _⟩, ⟨1, _⟩ => rfl
  | ⟨0, _⟩, ⟨1, _⟩ =>
    simp only [e01, e10, TauCeti.coxeterOrder_three, alternatingWord_six, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact nHatE_braid
  | ⟨1, _⟩, ⟨0, _⟩ =>
    simp only [e01, e10, TauCeti.coxeterOrder_three, alternatingWord_six, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact nHatE_braid.symm

theorem nHat_braidWord
    (i j : Fin (Tag.rank .G2)) :
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan .G2)) i j).map
      (nHat σ)).prod =
    ((CoxeterSystem.braidWord (coxeterMatrix (isFiniteType_cartan .G2)) j i).map
      (nHat σ)).prod := by
  apply Subtype.ext
  rw [Subgroup.val_list_prod, Subgroup.val_list_prod, List.map_map, List.map_map]
  exact nHatE_braidWord i j

theorem weylElement_sq
    (a : Fin d4.rank) :
    Chevalley.weylElement d4 K a ^ 2 = torusElement d4 K a (-1) :=
  Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact weylElt_one_sq d4 K a)

theorem units_map_neg_one : Units.map σ.toMonoidHom (-1 : Kˣ) = -1 :=
  Units.ext (by simp)

theorem nHat_sq_mem
    (i : Fin (Tag.rank .G2)) : nHat σ i ^ 2 ∈ hHat σ i := by
  rw [hHat, Subgroup.mem_subgroupOf, Subgroup.coe_pow, nHat_val]
  match i with
  | ⟨0, _⟩ =>
    refine ⟨⟨-1, (mem_fixedUnits σ).2 (by simp)⟩, ?_⟩
    rw [nHatE_zero, weylElement_sq]
    rfl
  | ⟨1, _⟩ =>
    refine ⟨-1, ?_⟩
    have c01 := commute_rankOne_outer (K := K) (a := nd 0) (b := nd 1) (by decide) (by decide)
      (by decide) (weylElement_mem_rankOne' (nd 0)) (weylElement_mem_rankOne' (nd 1))
    have c03 := commute_rankOne_outer (K := K) (a := nd 0) (b := nd 3) (by decide) (by decide)
      (by decide) (weylElement_mem_rankOne' (nd 0)) (weylElement_mem_rankOne' (nd 3))
    have c13 := commute_rankOne_outer (K := K) (a := nd 1) (b := nd 3) (by decide) (by decide)
      (by decide) (weylElement_mem_rankOne' (nd 1)) (weylElement_mem_rankOne' (nd 3))
    rw [hShortHom_apply, units_map_neg_one, units_map_neg_one, nHatE_one,
      (c03.mul_left c13).mul_pow, c01.mul_pow, weylElement_sq, weylElement_sq, weylElement_sq]

theorem conj_mem_rootGroup_of_mem_iSup_torus
    {g : adjointGroup d4 K}
    (hg : g ∈ ⨆ a, Adjoint.torus (τ := d4) K a) {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ)
    {y : adjointGroup d4 K} (hy : y ∈ 𝕏 γ) : g * y * g⁻¹ ∈ 𝕏 γ := by
  refine Subgroup.iSup_induction _ (C := fun g => ∀ y ∈ 𝕏 γ, g * y * g⁻¹ ∈ 𝕏 γ) hg
    (fun a x hx => ?_) (fun y hy => ?_) (fun x x' hx hx' y hy => ?_) y hy
  · intro y hy
    obtain ⟨t, rfl⟩ := hx
    exact torusElement_conj_mem a t hγ hy
  · rwa [one_mul, inv_one, mul_one]
  · have e : x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ := by group
    rw [e]
    exact hx _ (hx' y hy)

theorem hHat_conj_mem
    (l : Fin (Tag.rank .G2)) {β : Fin (Tag.rank .G2) → ℤ}
    (hβ : IsRoot .G2 β) {h : twistedGroup σ} (hh : h ∈ hHat σ l) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ β) : h * x * h⁻¹ ∈ twistedRootGroup σ β := by
  obtain ⟨α, hα, hp⟩ := exists_proj_eq hβ
  rw [mem_twistedRootGroup] at hx ⊢
  obtain ⟨hx1, hx2⟩ := (mem_twistedRootSubgroupD4_iff σ hα hp _).1 hx
  rw [hHat, Subgroup.mem_subgroupOf] at hh
  have hg := hHatE_le_iSup_torus σ l hh
  refine (mem_twistedRootSubgroupD4_iff σ hα hp _).2 ⟨?_, ?_⟩
  · have hle : ∀ γ, IsRoot d4 γ → (𝕏 γ).map (MulAut.conj (h : adjointGroup d4 K)).toMonoidHom ≤
        𝕏 γ := by
      intro γ hγ
      rw [Subgroup.map_le_iff_le_comap]
      intro y hy
      exact conj_mem_rootGroup_of_mem_iSup_torus hg hγ hy
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj (h : adjointGroup d4 K)).toMonoidHom hx1
    rw [Subgroup.map_sup, Subgroup.map_sup] at h1
    exact sup_le_sup (sup_le_sup (hle α hα) (hle _ (isRoot_rho hα)))
      (hle _ (isRoot_rho (isRoot_rho hα))) h1
  · have hn : twistC .D4 K σ (h : adjointGroup d4 K) = h := twistedGroup_le_twistFixed σ h.2
    change twistC .D4 K σ ((h : adjointGroup d4 K) * (x : adjointGroup d4 K) *
      (h : adjointGroup d4 K)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hn, hx2]
    rfl

variable (K) in
@[expose] def torusT :
    (Fin d4.rank → Kˣ) →* adjointGroup d4 K :=
  MonoidHom.noncommPiCoprod (fun a => Adjoint.torusHom (τ := d4) K a) (by
    intro a b _ s t
    exact torusElement_commute a b s t)

theorem torusT_mulSingle
    (a : Fin d4.rank) (t : Kˣ) :
    torusT K (Pi.mulSingle a t) = torusElement d4 K a t := by
  rw [torusT, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

@[expose] def chiHom (c : Fin d4.rank) : (Fin d4.rank → Kˣ) →* Kˣ where
  toFun u := ∏ a, u a ^ (-d4.cartan a c)
  map_one' := by simp
  map_mul' u v := by simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem chiHom_apply (c : Fin d4.rank) (u : Fin d4.rank → Kˣ) :
    chiHom c u = ∏ a, u a ^ (-d4.cartan a c) := rfl

theorem chiHom_mulSingle (c a : Fin d4.rank) (t : Kˣ) :
    chiHom c (Pi.mulSingle a t) = t ^ (-d4.cartan a c) := by
  rw [chiHom_apply, Finset.prod_eq_single a (fun b _ hb => by
    rw [Pi.mulSingle_eq_of_ne hb, one_zpow]) (by simp), Pi.mulSingle_eq_same]

theorem weylElement_conj_torusElement
    (c a : Fin d4.rank) (t : Kˣ) :
    Chevalley.weylElement d4 K c * torusElement d4 K a t * (Chevalley.weylElement d4 K c)⁻¹ =
      torusElement d4 K a t * torusElement d4 K c (t ^ (-d4.cartan a c)) :=
  Subtype.ext (weylElt_one_mul_torusElt_mul_inv d4 K c a t)

theorem weylElement_conj_torusT
    (c : Fin d4.rank) (u : Fin d4.rank → Kˣ) :
    Chevalley.weylElement d4 K c * torusT K u * (Chevalley.weylElement d4 K c)⁻¹ =
      torusT K (u * Pi.mulSingle c (chiHom c u)) := by
  have h : (MulAut.conj (Chevalley.weylElement d4 K c)).toMonoidHom.comp (torusT K) =
      (torusT K).comp
        (MonoidHom.id _ * (MonoidHom.mulSingle (fun _ => Kˣ) c).comp (chiHom c)) := by
    refine MonoidHom.pi_ext fun a t => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.mulSingle_apply, map_mul,
      torusT_mulSingle, chiHom_mulSingle]
    exact weylElement_conj_torusElement c a t
  exact DFunLike.congr_fun h u

@[expose] def IsSymU (u : Fin d4.rank → Kˣ) : Prop :=
  ∀ a, u (rhoPerm a) = Units.map σ.toMonoidHom (u a)

theorem chiHom_rho {u : Fin d4.rank → Kˣ} (hu : IsSymU σ u) (c : Fin d4.rank) :
    chiHom (rhoPerm c) u = Units.map σ.toMonoidHom (chiHom c u) := by
  calc chiHom (rhoPerm c) u =
        ∏ a, u (rhoPerm a) ^ (-d4.cartan (rhoPerm a) (rhoPerm c)) :=
      (Equiv.prod_comp rhoPerm (fun a => u a ^ (-d4.cartan a (rhoPerm c)))).symm
    _ = ∏ a, Units.map σ.toMonoidHom (u a ^ (-d4.cartan a c)) :=
      Finset.prod_congr rfl fun a _ => by rw [hu a, map_zpow, TwistTag.cartan_perm .D4 a c]
    _ = Units.map σ.toMonoidHom (chiHom c u) := by rw [chiHom_apply, map_prod]

theorem chiHom_mul_mulSingle_of_eq_zero {c a : Fin d4.rank} (h : d4.cartan a c = 0)
    (u : Fin d4.rank → Kˣ) (t : Kˣ) : chiHom c (u * Pi.mulSingle a t) = chiHom c u := by
  rw [map_mul, chiHom_mulSingle, h, neg_zero, zpow_zero, mul_one]

theorem exists_torusT_of_mem_hHatE
    (hσ : ∀ c, σ (σ (σ c)) = c) {l : Fin (Tag.rank .G2)}
    {x : adjointGroup d4 K} (hx : x ∈ hHatE σ l) : ∃ u, IsSymU σ u ∧ torusT K u = x := by
  match l with
  | ⟨0, _⟩ =>
    obtain ⟨t, rfl⟩ := hx
    refine ⟨Pi.mulSingle (nd 2) (t : Kˣ), fun a => ?_, torusT_mulSingle _ _⟩
    by_cases ha : a = nd 2
    · subst ha
      rw [rhoPerm_two, Pi.mulSingle_eq_same]
      exact (Units.ext ((mem_fixedUnits σ).1 t.2)).symm
    · have ha' : rhoPerm a ≠ nd 2 := fun h => ha (by
        rw [← rhoPerm_rhoPerm_rhoPerm a, h]
        rfl)
      rw [Pi.mulSingle_eq_of_ne ha', Pi.mulSingle_eq_of_ne ha, map_one]
  | ⟨1, _⟩ =>
    obtain ⟨t, rfl⟩ := hx
    refine ⟨Pi.mulSingle (nd 0) t * Pi.mulSingle (nd 1) (Units.map σ.toMonoidHom t) *
      Pi.mulSingle (nd 3) (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)), ?_, ?_⟩
    · have h3 : Units.map σ.toMonoidHom (Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) =
          t := Units.ext (hσ t)
      intro a
      match a with
      | ⟨0, _⟩ =>
        rw [rhoPerm_zero]
        simp [Fin.ext_iff]
      | ⟨1, _⟩ =>
        rw [rhoPerm_one]
        simp [Fin.ext_iff]
      | ⟨2, _⟩ =>
        rw [rhoPerm_two]
        simp [Fin.ext_iff]
      | ⟨3, _⟩ =>
        rw [rhoPerm_three]
        simp [Fin.ext_iff]
        exact h3.symm
    · rw [map_mul, map_mul, torusT_mulSingle, torusT_mulSingle, torusT_mulSingle,
        hShortHom_apply]

theorem exists_conj_torusT
    (j : Fin (Tag.rank .G2)) {u : Fin d4.rank → Kˣ} (hu : IsSymU σ u) :
    ∃ v ∈ hHatE σ j, nHatE K j * torusT K u * (nHatE K j)⁻¹ = torusT K u * v := by
  match j with
  | ⟨0, _⟩ =>
    have hfix : chiHom (nd 2) u ∈ fixedUnits σ := by
      have h := chiHom_rho σ hu (nd 2)
      rw [rhoPerm_two] at h
      exact h.symm
    refine ⟨_, ⟨⟨chiHom (nd 2) u, hfix⟩, rfl⟩, ?_⟩
    change Chevalley.weylElement d4 K (nd 2) * torusT K u *
      (Chevalley.weylElement d4 K (nd 2))⁻¹ =
        torusT K u * torusElement d4 K (nd 2) (chiHom (nd 2) u)
    rw [weylElement_conj_torusT, map_mul, torusT_mulSingle]
  | ⟨1, _⟩ =>
    refine ⟨_, ⟨chiHom (nd 0) u, rfl⟩, ?_⟩
    have h1 : chiHom (nd 1) u = Units.map σ.toMonoidHom (chiHom (nd 0) u) := by
      rw [← chiHom_rho σ hu (nd 0), rhoPerm_zero]
    have h3 : chiHom (nd 3) u = Units.map σ.toMonoidHom (chiHom (nd 1) u) := by
      rw [← chiHom_rho σ hu (nd 1), rhoPerm_one]
    rw [hShortHom_apply, ← h1, ← h3, nHatE_one]
    calc Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
          Chevalley.weylElement d4 K (nd 3) * torusT K u *
          (Chevalley.weylElement d4 K (nd 0) * Chevalley.weylElement d4 K (nd 1) *
            Chevalley.weylElement d4 K (nd 3))⁻¹ =
        Chevalley.weylElement d4 K (nd 0) * (Chevalley.weylElement d4 K (nd 1) *
          (Chevalley.weylElement d4 K (nd 3) * torusT K u *
            (Chevalley.weylElement d4 K (nd 3))⁻¹) * (Chevalley.weylElement d4 K (nd 1))⁻¹) *
          (Chevalley.weylElement d4 K (nd 0))⁻¹ := by group
      _ = torusT K (u * Pi.mulSingle (nd 3) (chiHom (nd 3) u) *
            Pi.mulSingle (nd 1) (chiHom (nd 1) u) * Pi.mulSingle (nd 0) (chiHom (nd 0) u)) := by
          rw [weylElement_conj_torusT, weylElement_conj_torusT, weylElement_conj_torusT,
            chiHom_mul_mulSingle_of_eq_zero (c := nd 1) (a := nd 3) (by decide),
            chiHom_mul_mulSingle_of_eq_zero (c := nd 0) (a := nd 1) (by decide),
            chiHom_mul_mulSingle_of_eq_zero (c := nd 0) (a := nd 3) (by decide)]
      _ = torusT K (u * (Pi.mulSingle (nd 0) (chiHom (nd 0) u) *
            Pi.mulSingle (nd 1) (chiHom (nd 1) u) * Pi.mulSingle (nd 3) (chiHom (nd 3) u))) := by
          congr 1
          ac_rfl
      _ = _ := by
          rw [map_mul, map_mul, map_mul, torusT_mulSingle, torusT_mulSingle, torusT_mulSingle]

theorem nHat_conj_hHat_mem
    (hσ : ∀ c, σ (σ (σ c)) = c) (j l : Fin (Tag.rank .G2))
    {h : twistedGroup σ} (hh : h ∈ hHat σ l) :
    nHat σ j * h * (nHat σ j)⁻¹ ∈ hHat σ j ⊔ hHat σ l := by
  have hh' := hh
  rw [hHat, Subgroup.mem_subgroupOf] at hh'
  obtain ⟨u, hu, hTu⟩ := exists_torusT_of_mem_hHatE σ hσ hh'
  obtain ⟨v, hv, he⟩ := exists_conj_torusT σ j hu
  have hvj : (⟨v, hHatE_le_twistedGroup hσ j hv⟩ : twistedGroup σ) ∈ hHat σ j := by
    rw [hHat, Subgroup.mem_subgroupOf]
    exact hv
  have heq : nHat σ j * h * (nHat σ j)⁻¹ = h * ⟨v, hHatE_le_twistedGroup hσ j hv⟩ := by
    apply Subtype.ext
    change nHatE K j * (h : adjointGroup d4 K) * (nHatE K j)⁻¹ = (h : _) * v
    rw [← hTu, he]
  rw [heq]
  exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hvj)

end CFSG.LieType.Steinberg.TwistedD4
