module

public import CFSG.LieType.Multipliers.L34
public import CFSG.LieType.Multipliers.L34UpperCheck
import all CFSG.LieType.Multipliers.L34
import all CFSG.LieType.Multipliers.L34Model

public noncomputable section

namespace CFSG.LieType.Multipliers.L34Upper

open Subgroup CFSG.Fischer CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open scoped commutatorElement

section Central

variable {G E S : Type*} [Group G] [Group E] [Group S]

private theorem eq_of_mem_commutator (q : E →* S) (hker : q.ker ≤ center E) (φ φ' : G →* E)
    (h : q.comp φ = q.comp φ') {x : G} (hx : x ∈ commutator G) : φ x = φ' x := by
  have hc : ∀ y, (φ y)⁻¹ * φ' y ∈ center E := fun y => hker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, h, MonoidHom.comp_apply,
      inv_mul_cancel]
  have hle : commutator G ≤ MonoidHom.eqLocus φ φ' := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change φ ⁅a, b⁆ = φ' ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    have ha : φ' a = φ a * ((φ a)⁻¹ * φ' a) := by group
    have hb : φ' b = φ b * ((φ b)⁻¹ * φ' b) := by group
    rw [ha, hb, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc a) (hc b)]
  exact hle hx

private theorem hom_ext_of_perfect [Group.IsPerfect G] (q : E →* S) (hker : q.ker ≤ center E)
    {φ φ' : G →* E} (h : q.comp φ = q.comp φ') : φ = φ' :=
  MonoidHom.ext fun _ => eq_of_mem_commutator q hker φ φ' h Group.IsPerfect.mem_commutator

private theorem mem_center_of_map_mem_center [Group.IsPerfect E] (q : E →* S)
    (hker : q.ker ≤ center E) {y : E} (hy : q y ∈ center S) : y ∈ center E := by
  have h : q.comp (MulAut.conj y).toMonoidHom = q.comp (MonoidHom.id E) := by
    ext z
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, MonoidHom.id_apply]
    rw [← mem_center_iff.mp hy (q z), mul_inv_cancel_right]
  rw [mem_center_iff]
  intro z
  have hz : y * z * y⁻¹ = z := by
    simpa using eq_of_mem_commutator q hker _ _ h (x := z) Group.IsPerfect.mem_commutator
  calc z * y = y * z * y⁻¹ * y := by rw [hz]
    _ = y * z := by group

private theorem surjective_of_comp [Group.IsPerfect E] (q : E →* S) (hker : q.ker ≤ center E)
    (φ : G →* E) (hφ : Function.Surjective (q.comp φ)) : Function.Surjective φ := by
  have hc : ∀ y, ∃ c, (φ c)⁻¹ * y ∈ center E := fun y => by
    obtain ⟨c, hc⟩ := hφ (q y)
    refine ⟨c, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, hc, inv_mul_cancel]
  have hle : commutator E ≤ φ.range := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨c, hca⟩ := hc a
    obtain ⟨d, hdb⟩ := hc b
    have h : ⁅a, b⁆ = φ ⁅c, d⁆ := by
      rw [map_commutatorElement]
      calc ⁅a, b⁆ = ⁅φ c * ((φ c)⁻¹ * a), φ d * ((φ d)⁻¹ * b)⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅φ c, φ d⁆ := CFSG.SectionRank.commutatorElement_mul_mem_center _ _ hca hdb
    rw [h]
    exact ⟨_, rfl⟩
  exact fun y => MonoidHom.mem_range.mp (hle Group.IsPerfect.mem_commutator)

private theorem exists_mulEquiv_of_ker_eq {E' : Type*} [Group E'] (f : G →* E) (f' : G →* E')
    (hf : Function.Surjective f) (hf' : Function.Surjective f') (h : f.ker = f'.ker) :
    ∃ φ : E ≃* E', ∀ x, φ (f x) = f' x := by
  refine ⟨((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f' hf'), fun x => ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) = (x : G ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
  rfl

end Central

section OrderTwo

variable {E : Type*} [Group E] {K : Subgroup E}

private theorem sq_eq_one_of_card_two (hK : Nat.card K = 2) {y : E} (hy : y ∈ K) : y ^ 2 = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have h := pow_card_eq_one' (G := K) (x := ⟨y, hy⟩)
  rw [hK] at h
  exact congrArg Subtype.val h

private theorem eq_of_card_two (hK : Nat.card K = 2) {y y' : E} (hy : y ∈ K) (hy' : y' ∈ K)
    (h1 : y ≠ 1) (h1' : y' ≠ 1) : y = y' := by
  obtain ⟨a, b, -, hset⟩ := Nat.card_eq_two_iff.mp hK
  have hmem : ∀ z : K, z = a ∨ z = b := fun z => by
    have hz := Set.mem_univ z
    rw [← hset] at hz
    simpa using hz
  have hval : ∀ {z z' : K}, z = z' → (z : E) = z' := fun h => congrArg Subtype.val h
  rcases hmem 1 with h | h <;> rcases hmem ⟨y, hy⟩ with hya | hya <;>
    rcases hmem ⟨y', hy'⟩ with hyb | hyb
  all_goals first
    | exact hval (hya.trans hyb.symm)
    | exact absurd (hval (hya.trans h.symm)) h1
    | exact absurd (hval (hyb.trans h.symm)) h1'

private theorem eq_iff_of_card_two (hK : Nat.card K = 2) {y y' : E} (hy : y ∈ K)
    (hy' : y' ∈ K) : y = y' ↔ (y = 1 ↔ y' = 1) := by
  refine ⟨fun h => h ▸ Iff.rfl, fun h => ?_⟩
  by_cases h1 : y = 1
  · rw [h1, h.mp h1]
  · exact eq_of_card_two hK hy hy' h1 (fun h1' => h1 (h.mpr h1'))

private theorem pow_eq_one_iff_of_card_two (hK : Nat.card K = 2) {y : E} (hy : y ∈ K) (i : ℕ) :
    y ^ i = 1 ↔ (i % 2 = 0 ∨ y = 1) := by
  rw [pow_eq_pow_mod i (sq_eq_one_of_card_two hK hy)]
  rcases Nat.mod_two_eq_zero_or_one i with h | h <;> simp [h]

private theorem pow_mul_pow_eq_one_iff (hK : Nat.card K = 2) {u v : E} (hu : u ∈ K) (hv : v ∈ K)
    (i j : ℕ) :
    u ^ i * v ^ j = 1 ↔ ((i % 2 = 0 ∨ u = 1) ↔ (j % 2 = 0 ∨ v = 1)) := by
  have hv2 : (v ^ j)⁻¹ = v ^ j := by
    rw [inv_eq_iff_mul_eq_one, ← sq]
    exact sq_eq_one_of_card_two hK (pow_mem hv j)
  rw [mul_eq_one_iff_eq_inv, hv2, eq_iff_of_card_two hK (pow_mem hu i) (pow_mem hv j),
    pow_eq_one_iff_of_card_two hK hu, pow_eq_one_iff_of_card_two hK hv]

end OrderTwo

section Conj

variable {R : Type*} [CommRing R]

private def conjSL (g : GL (Fin 3) R) :
    Matrix.SpecialLinearGroup (Fin 3) R →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun A := ⟨(g : Matrix (Fin 3) (Fin 3) R) * (A : Matrix (Fin 3) (Fin 3) R) *
      ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one, ← Matrix.det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  map_one' := Subtype.ext <| by
    show (g : Matrix (Fin 3) (Fin 3) R) * 1 * ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      1
    rw [Matrix.mul_one, Units.mul_inv]
  map_mul' A B := Subtype.ext <| by
    show (g : Matrix (Fin 3) (Fin 3) R) *
        ((A : Matrix (Fin 3) (Fin 3) R) * (B : Matrix (Fin 3) (Fin 3) R)) *
          ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      ((g : Matrix (Fin 3) (Fin 3) R) * (A : Matrix (Fin 3) (Fin 3) R) *
          ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) *
        ((g : Matrix (Fin 3) (Fin 3) R) * (B : Matrix (Fin 3) (Fin 3) R) *
          ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R))
    simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]

private theorem coe_conjSL (g : GL (Fin 3) R) (A : Matrix.SpecialLinearGroup (Fin 3) R) :
    ((conjSL g A : Matrix.SpecialLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
      (g : Matrix (Fin 3) (Fin 3) R) * (A : Matrix (Fin 3) (Fin 3) R) *
        ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) :=
  rfl

private theorem conjSL_mul (g h : GL (Fin 3) R) (A : Matrix.SpecialLinearGroup (Fin 3) R) :
    conjSL (g * h) A = conjSL g (conjSL h A) := Subtype.ext <| by
  simp only [coe_conjSL, mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

private theorem conjSL_one (A : Matrix.SpecialLinearGroup (Fin 3) R) : conjSL 1 A = A :=
  Subtype.ext <| by simp [coe_conjSL]

private theorem conjSL_inv_conjSL (g : GL (Fin 3) R) (A : Matrix.SpecialLinearGroup (Fin 3) R) :
    conjSL g⁻¹ (conjSL g A) = A := by
  rw [← conjSL_mul, inv_mul_cancel, conjSL_one]

private theorem conjSL_conjSL_inv (g : GL (Fin 3) R) (A : Matrix.SpecialLinearGroup (Fin 3) R) :
    conjSL g (conjSL g⁻¹ A) = A := by
  rw [← conjSL_mul, mul_inv_cancel, conjSL_one]

private theorem conjSL_eq_one {g : GL (Fin 3) R} {A : Matrix.SpecialLinearGroup (Fin 3) R}
    (h : conjSL g A = 1) : A = 1 := by
  rw [← conjSL_inv_conjSL g A, h, map_one]

end Conj

theorem extraWs_eq_one :
    ∀ u ∈ extraWs, PresentedGroup.mk (wordSet hopfWs) (FreeGroup.mk u) = 1 :=
  relations_check

theorem lift_genSL_commWords (i : Fin 2) :
    FreeGroup.lift genSL (FreeGroup.mk (commWords (coverPairs i))) = genSL i := by
  have hmem : (i, false) :: commWords (coverPairs i) ∈ coverWs := by
    show _ ∈ coverWords rels (fun i => commWords (coverPairs i)) ++ extraWs
    exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  have h := lift_genSL_coverWs _ (List.mem_map_of_mem hmem)
  rw [← List.singleton_append, ← FreeGroup.mul_mk, map_mul,
    show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv,
    FreeGroup.lift_apply_of] at h
  exact (inv_mul_eq_one.mp h).symm

private theorem lift_genX_commWords (i : Fin 2) :
    FreeGroup.lift genX (FreeGroup.mk (commWords (coverPairs i))) = genX i := by
  rw [lift_genX, MonoidHom.comp_apply, lift_genSL_commWords]
  rfl

private theorem commWords_mem_commutator (i : Fin 2) :
    FreeGroup.mk (commWords (coverPairs i)) ∈ commutator (FreeGroup (Fin 2)) :=
  mk_commWords_mem_commutator _

theorem finite_card_presentedCover_le
    :
    Finite (PresentedCover (wordSet rels) fun i => FreeGroup.mk (commWords (coverPairs i))) ∧
      Nat.card (PresentedCover (wordSet rels) fun i => FreeGroup.mk (commWords (coverPairs i))) ≤
        967680 := by
  have h := card_le_of_append hopfWs extraWs extraWs_eq_one finite_card_cover_le
  rw [PresentedCover, coverRelators_wordSet]
  exact h

private theorem nonempty_mulEquiv_of_lieModel {X : Type} [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) : Nonempty (PSL3 ≃* X) := by
  rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact nonempty_mulEquiv_PSL3 hK e
  all_goals exact absurd h0 (by norm_num)

theorem card_griessHopfMultiplier_le
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ≤ 48 := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_lieModel h
  have hP := isPresentation_genX.mulEquiv ψ
  have hwg : ∀ i, FreeGroup.lift (fun j => ψ (genX j)) (FreeGroup.mk (commWords (coverPairs i))) =
      ψ (genX i) := fun i => by rw [lift_mulEquiv, lift_genX_commWords]
  have hc := card_presentedCover hP commWords_mem_commutator hwg
  obtain ⟨-, hle⟩ := finite_card_presentedCover_le
  have hX : 20160 ≤ Nat.card X := by
    rw [← Nat.card_congr ψ.toEquiv]
    exact card_PSL3_ge
  rw [hc] at hle
  by_contra! hlt
  nlinarith

theorem multiplier_PSL_three_four
    (X : Type) [Group X]
    (h : CFSG.Blueprint.LieModel X .PSL 3 2 2) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* Multiplicative (ZMod 3 × ZMod 4 × ZMod 4)) := by
  obtain ⟨ψ⟩ := nonempty_mulEquiv_of_lieModel h
  have hP := isPresentation_genX.mulEquiv ψ
  have hwg : ∀ i, FreeGroup.lift (fun j => ψ (genX j)) (FreeGroup.mk (commWords (coverPairs i))) =
      ψ (genX i) := fun i => by rw [lift_mulEquiv, lift_genX_commWords]
  refine ⟨(isPerfect_of_isPresentation hP commWords_mem_commutator hwg).commutator_eq_top, ?_⟩
  obtain ⟨hfin, hle⟩ := finite_card_presentedCover_le
  have hX : 20160 ≤ Nat.card X := by
    rw [← Nat.card_congr ψ.toEquiv]
    exact card_PSL3_ge
  have he : ∀ r ∈ coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (coverPairs i))),
      FreeGroup.lift (PresentedGroup.of : Fin 2 → Cover) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp (coverRelators_subset hr)
    rw [lift_of_mk]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  obtain ⟨eK⟩ := nonempty_ker_piX_mulEquiv
  have hK₀ : Nat.card piX.ker = 48 := by
    rw [Nat.card_congr eK.toEquiv]
    simp
  have hsurj : Function.Surjective (PresentedGroup.toGroup he) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of, closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, PresentedGroup.toGroup.of he⟩
  have hcomp : coverMap hP hwg = ψ.toMonoidHom.comp (piX.comp (PresentedGroup.toGroup he)) := by
    refine PresentedGroup.ext fun i => ?_
    rw [coverMap_of, MonoidHom.comp_apply, MonoidHom.comp_apply, PresentedGroup.toGroup.of]
    change ψ (genX i) = ψ (piX (PresentedGroup.mk _ (FreeGroup.of i)))
    rw [piX_mk, FreeGroup.lift_apply_of]
  have hK : piX.ker ≤ (coverMap hP hwg).ker.map (PresentedGroup.toGroup he) := by
    intro c hc
    obtain ⟨p, rfl⟩ := hsurj c
    refine ⟨p, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hcomp, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.mem_ker.mp hc, map_one]
  obtain ⟨eM⟩ := nonempty_griessHopfMultiplier_mulEquiv_of_card_le hP commWords_mem_commutator
    hwg (m := 48) (hle.trans (by nlinarith)) he hK₀ hK
  exact ⟨(eM.trans eK).trans ((MulEquiv.prodMultiplicative (ZMod 3) (ZMod 4 × ZMod 4)).trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.prodMultiplicative (ZMod 4) (ZMod 4)))).symm⟩

section Lift

variable {E : Type*} [Group E]

private def liftVals (x : Fin 2 → E) (i : Fin 2) : E :=
  FreeGroup.lift x (FreeGroup.mk (commWords (coverPairs i)))

private theorem comp_lift_eq
    (π : E →* SL3) {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) :
    π.comp (FreeGroup.lift x) = FreeGroup.lift genSL :=
  FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hx]

private theorem comp_lift_liftVals
    (π : E →* SL3) {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) :
    π.comp (FreeGroup.lift (liftVals x)) = FreeGroup.lift genSL :=
  FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, liftVals,
      ← MonoidHom.comp_apply, comp_lift_eq π hx, lift_genSL_commWords]

private theorem lift_hopfWs
    [Group.IsPerfect E] (π : E →* SL3) (hC : π.ker ≤ center E)
    {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) :
    ∀ r ∈ wordSet hopfWs, FreeGroup.lift (liftVals x) r = 1 := by
  rw [show wordSet hopfWs = coverRelators (wordSet rels)
    (fun i => FreeGroup.mk (commWords (coverPairs i))) from (coverRelators_wordSet rels _).symm]
  refine lift_coverRelators_eq_one_iff.mpr ⟨fun i r hr => ?_, fun i => ?_⟩
  · have hcen : FreeGroup.lift (liftVals x) r ∈ center E := by
      refine mem_center_of_map_mem_center π hC ?_
      rw [← MonoidHom.comp_apply, comp_lift_liftVals π hx]
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      exact lift_genSL_mem_center (List.all_eq_true.mp rels_isScalar w hw)
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hcen _)
  · exact eq_of_mem_commutator π hC _ _
      ((comp_lift_liftVals π hx).trans (comp_lift_eq π hx).symm) (commWords_mem_commutator i)

private theorem lift_coverWs
    [Group.IsPerfect E] (π : E →* SL3) (hC : π.ker ≤ center E)
    {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) :
    ∀ r ∈ wordSet coverWs, FreeGroup.lift (liftVals x) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rcases List.mem_append.mp hw with hw | hw
  · exact lift_hopfWs π hC hx _ (List.mem_map_of_mem hw)
  · have h := congrArg (PresentedGroup.toGroup (lift_hopfWs π hC hx)) (extraWs_eq_one w hw)
    rw [map_one] at h
    exact h

private def coverLift
    [Group.IsPerfect E] (π : E →* SL3) (hC : π.ker ≤ center E)
    {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) : Cover →* E :=
  PresentedGroup.toGroup (lift_coverWs π hC hx)

private theorem coverLift_of
    [Group.IsPerfect E] (π : E →* SL3) (hC : π.ker ≤ center E)
    {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) (i : Fin 2) :
    coverLift π hC hx (PresentedGroup.of i) = liftVals x i :=
  PresentedGroup.toGroup.of _

private theorem comp_coverLift
    [Group.IsPerfect E] (π : E →* SL3) (hC : π.ker ≤ center E)
    {x : Fin 2 → E} (hx : ∀ i, π (x i) = genSL i) : π.comp (coverLift π hC hx) = pSL := by
  refine PresentedGroup.ext fun i => ?_
  rw [MonoidHom.comp_apply, coverLift_of, liftVals, ← MonoidHom.comp_apply, comp_lift_eq π hx,
    lift_genSL_commWords]
  exact (PresentedGroup.toGroup.of _).symm

private instance : Group.IsPerfect Cover := ⟨commutator_cover⟩

private theorem cover_hom_ext
    {S : Type*} [Group S] (q : E →* S) (hker : q.ker ≤ center E)
    {φ φ' : Cover →* E} (h : q.comp φ = q.comp φ') : φ = φ' :=
  hom_ext_of_perfect q hker h

private def coverLiftOf
    [Group.IsPerfect E] {π : E →* SL3} (hπ : Function.Surjective π)
    (hC : π.ker ≤ center E) : Cover →* E :=
  coverLift π hC (x := fun i => Function.surjInv hπ (genSL i)) fun _ => Function.surjInv_eq hπ _

private theorem comp_coverLiftOf
    [Group.IsPerfect E] {π : E →* SL3} (hπ : Function.Surjective π)
    (hC : π.ker ≤ center E) : π.comp (coverLiftOf hπ hC) = pSL :=
  comp_coverLift π hC _

private theorem coverLiftOf_apply
    [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (c : Cover) :
    π (coverLiftOf hπ hC c) = pSL c := by
  rw [← MonoidHom.comp_apply, comp_coverLiftOf]

private theorem coverLiftOf_surjective
    [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) :
    Function.Surjective (coverLiftOf hπ hC) :=
  surjective_of_comp π hC _ (by rw [comp_coverLiftOf]; exact pSL_surjective)

private theorem coverLiftOf_mem_ker
    [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) {m : Cover} (hm : m ∈ pSL.ker) :
    coverLiftOf hπ hC m ∈ π.ker := by
  rw [MonoidHom.mem_ker, coverLiftOf_apply]
  exact hm

private theorem exists_of_mem_ker
    [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) {y : E} (hy : y ∈ π.ker) :
    ∃ m ∈ pSL.ker, coverLiftOf hπ hC m = y := by
  obtain ⟨m, rfl⟩ := coverLiftOf_surjective hπ hC y
  refine ⟨m, ?_, rfl⟩
  rw [MonoidHom.mem_ker, ← coverLiftOf_apply hπ hC]
  exact hy

private theorem ker_coverLiftOf_le
    [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) :
    (coverLiftOf hπ hC).ker ≤ pSL.ker := fun c hc => by
  rw [MonoidHom.mem_ker, ← coverLiftOf_apply hπ hC, MonoidHom.mem_ker.mp hc, map_one]

end Lift

private theorem commute_zOne_zTwo
    : Commute (zHat zOne) (zHat zTwo) :=
  (mem_center_iff.mp (ker_piX_le_center (ker_pSL_le_ker_piX zOne_mem)) _).symm

private def zHom
    : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* Cover :=
  (powHom (zHat zOne) 4 zOne_pow).noncommCoprod (powHom (zHat zTwo) 4 zTwo_pow) fun _ _ => by
    simp only [powHom_apply]
    exact (commute_zOne_zTwo.pow_left _).pow_right _

private theorem zHom_apply
    (p : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    zHom p = zHat zOne ^ p.1.toAdd.val * zHat zTwo ^ p.2.toAdd.val :=
  rfl

private theorem z4z4_involutions : ∀ d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
    d ≠ 1 → d * d = 1 → d = (Multiplicative.ofAdd 2, 1) ∨ d = (1, Multiplicative.ofAdd 2) ∨
      d = (Multiplicative.ofAdd 2, Multiplicative.ofAdd 2) := by
  decide

private theorem zHom_injective : Function.Injective zHom := by
  refine injective_of_forall_prime_pow _ fun d hd p hp hpd hdp => ?_
  have h16 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 2 ^ 4 := by simp
  rw [h16] at hpd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
  have v4 : (2 : ZMod 4).val = 2 := rfl
  rcases z4z4_involutions d hd (by rw [← sq]; exact hdp) with rfl | rfl | rfl
  · simpa [zHom_apply, v4] using zOne_sq_ne_one
  · simpa [zHom_apply, v4] using zTwo_sq_ne_one
  · simpa [zHom_apply, v4] using zOne_sq_mul_zTwo_sq_ne_one

private theorem exists_zOne_zTwo {m : Cover} (hm : m ∈ pSL.ker) :
    ∃ i j : ℕ, m = zHat zOne ^ i * zHat zTwo ^ j := by
  obtain ⟨eK⟩ := nonempty_ker_pSL_mulEquiv
  have hcardK : Nat.card pSL.ker = 16 := by
    rw [Nat.card_congr eK.toEquiv]
    simp
  have hle : zHom.range ≤ pSL.ker := by
    rintro _ ⟨p, rfl⟩
    rw [zHom_apply]
    exact pSL.ker.mul_mem (pSL.ker.pow_mem zOne_mem _) (pSL.ker.pow_mem zTwo_mem _)
  have hcardR : Nat.card zHom.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective zHom_injective).toEquiv]
    simp
  have : Finite pSL.ker := Nat.finite_of_card_ne_zero (by omega)
  have heq : zHom.range = pSL.ker := eq_of_le_of_card_ge hle (by omega)
  rw [← heq] at hm
  obtain ⟨p, hp⟩ := hm
  exact ⟨_, _, by rw [← hp, zHom_apply]⟩

private theorem card_ker_le_four_F4
    {E : Type*} [Group E] [Group.IsPerfect E] (η : E →* SL3)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : ∀ c ∈ η.ker, c ^ 2 = 1) :
    Nat.card η.ker ≤ 4 := by
  have hu := coverLiftOf_mem_ker hη hC zOne_mem
  have hv := coverLiftOf_mem_ker hη hC zTwo_mem
  let f : Fin 2 × Fin 2 → η.ker := fun p =>
    ⟨coverLiftOf hη hC (zHat zOne) ^ (p.1 : ℕ) * coverLiftOf hη hC (zHat zTwo) ^ (p.2 : ℕ),
      η.ker.mul_mem (η.ker.pow_mem hu _) (η.ker.pow_mem hv _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm, rfl⟩ := exists_of_mem_ker hη hC hy
    obtain ⟨i, j, rfl⟩ := exists_zOne_zTwo hm
    refine ⟨(⟨i % 2, Nat.mod_lt _ two_pos⟩, ⟨j % 2, Nat.mod_lt _ two_pos⟩), Subtype.ext ?_⟩
    change coverLiftOf hη hC (zHat zOne) ^ (i % 2) * coverLiftOf hη hC (zHat zTwo) ^ (j % 2) =
      coverLiftOf hη hC (zHat zOne ^ i * zHat zTwo ^ j)
    rw [map_mul, map_pow, map_pow, ← pow_eq_pow_mod i (h2 _ hu), ← pow_eq_pow_mod j (h2 _ hv)]
  calc Nat.card η.ker ≤ Nat.card (Fin 2 × Fin 2) := Nat.card_le_card_of_surjective f hf
    _ = 4 := by simp

private def dGL : GL (Fin 3) F4 :=
  ⟨dMat.toMatrix, dInvMat.toMatrix, by rw [← Mat3.toMatrix_mul, dMat_mul.1, Mat3.toMatrix_one],
    by rw [← Mat3.toMatrix_mul, dMat_mul.2, Mat3.toMatrix_one]⟩

private theorem dGL_pow_three : dGL ^ 3 = 1 := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, pow_two]
  change dMat.toMatrix * dMat.toMatrix * dMat.toMatrix = 1
  rw [← Mat3.toMatrix_mul, ← Mat3.toMatrix_mul, ← Mat3.toMatrix_one]
  exact congrArg Mat3.toMatrix rfl

private theorem coe_genSL_zero
    : ((genSL 0 : SL3) : M3) = aMat.toMatrix := by
  change ((aSL : SL3) : M3) = _
  rfl

private theorem coe_genSL_one
    : ((genSL 1 : SL3) : M3) = bMat.toMatrix := by
  change ((bSL : SL3) : M3) = _
  rfl

private def deltaLifts : Fin 2 → Cover :=
  fun j => PresentedGroup.mk (wordSet coverWs) (FreeGroup.mk ([uA, uB].getD j []))

private theorem conjSL_pSL_deltaLifts
    (i : Fin 2) :
    conjSL dGL⁻¹ (pSL (deltaLifts i)) = genSL i := by
  apply Subtype.ext
  rw [coe_conjSL, inv_inv]
  fin_cases i
  · change dInvMat.toMatrix * ((FreeGroup.lift genSL (FreeGroup.mk uA) : SL3) : M3) *
      dMat.toMatrix = ((genSL 0 : SL3) : M3)
    rw [coe_lift_genSL, words_check.1, coe_genSL_zero, ← Mat3.toMatrix_mul, ← Mat3.toMatrix_mul]
    exact congrArg Mat3.toMatrix rfl
  · change dInvMat.toMatrix * ((FreeGroup.lift genSL (FreeGroup.mk uB) : SL3) : M3) *
      dMat.toMatrix = ((genSL 1 : SL3) : M3)
    rw [coe_lift_genSL, words_check.2.1, coe_genSL_one, ← Mat3.toMatrix_mul, ← Mat3.toMatrix_mul]
    exact congrArg Mat3.toMatrix rfl

private theorem ker_conjSL_comp_pSL (g : GL (Fin 3) F4) :
    ((conjSL g).comp pSL).ker ≤ center Cover := fun c hc =>
  ker_piX_le_center <| ker_pSL_le_ker_piX <| conjSL_eq_one (A := pSL c) hc

private def deltaHat
    : Cover →* Cover :=
  coverLift (x := deltaLifts) ((conjSL dGL⁻¹).comp pSL) (ker_conjSL_comp_pSL _)
    conjSL_pSL_deltaLifts

private theorem pSL_deltaHat
    (c : Cover) : pSL (deltaHat c) = conjSL dGL (pSL c) := by
  have h : ((conjSL dGL⁻¹).comp pSL).comp deltaHat = pSL := comp_coverLift _ _ _
  have hc := DFunLike.congr_fun h c
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at hc
  rw [← hc, conjSL_conjSL_inv]

private theorem deltaHat_of
    (i : Fin 2) :
    deltaHat (PresentedGroup.of i) =
      PresentedGroup.mk (wordSet coverWs) (FreeGroup.mk (deltaWs.getD i [])) := by
  rw [deltaHat, coverLift_of, liftVals]
  unfold deltaLifts
  rw [lift_substWord]
  fin_cases i <;> rfl

private theorem deltaHat_zHat
    (w : List (Fin 2 × Bool)) :
    deltaHat (zHat w) = zHat (substWord deltaWs w) := by
  have h : deltaHat.comp (PresentedGroup.mk (wordSet coverWs)) = FreeGroup.lift
      (fun i : Fin 2 => PresentedGroup.mk (wordSet coverWs) (FreeGroup.mk (deltaWs.getD i []))) :=
    FreeGroup.ext_hom _ _ fun i => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact deltaHat_of i
  rw [zHat, zHat, ← MonoidHom.comp_apply, h, lift_substWord]

private theorem genSL_one_pow_five
    : genSL 1 ^ 5 = 1 := by
  have h := lift_genSL_coverWs (FreeGroup.mk bFive) (List.mem_map_of_mem
    (List.mem_append_right _ (by simp [extraWs])))
  rwa [words_check.2.2, show List.replicate 5 ((1 : Fin 2), true) = wpow [(1, true)] 5 from rfl,
    mk_wpow, map_pow, show FreeGroup.mk [((1 : Fin 2), true)] = FreeGroup.of 1 from rfl,
    FreeGroup.lift_apply_of] at h

private theorem orderOf_genSL_one
    : orderOf (genSL 1) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine orderOf_eq_prime genSL_one_pow_five fun h => bMat_ne_one (Mat3.toMatrix_injective ?_)
  rw [← coe_genSL_one, h, Mat3.toMatrix_one]
  rfl

private theorem of_one_pow_five
    : (PresentedGroup.of (1 : Fin 2) : Cover) ^ 5 = 1 := by
  have h := zHat_eq_one (w := bFive) (List.mem_append_right _ (by simp [extraWs]))
  rwa [zHat, words_check.2.2, show List.replicate 5 ((1 : Fin 2), true) = wpow [(1, true)] 5
    from rfl, mk_wpow, map_pow] at h

private theorem eq_one_of_mem_zpowers
    {c : Cover} (hc : c ∈ zpowers (PresentedGroup.of 1))
    (hk : pSL c = 1) : c = 1 := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
  rw [map_zpow, show pSL (PresentedGroup.of 1) = genSL 1 from PresentedGroup.toGroup.of _] at hk
  obtain ⟨q, rfl⟩ := orderOf_dvd_iff_zpow_eq_one.mpr hk
  rw [orderOf_genSL_one, zpow_mul, zpow_natCast, of_one_pow_five, one_zpow]

private theorem mem_zpowers_of_deltaWalks
    {u : List (Fin 2 × Bool)} (hu : (u, 1) ∈ deltaWalks) :
    zHat u ∈ zpowers (PresentedGroup.of 1) := by
  have h := delta_check _ hu
  refine (closure_le _).mpr ?_ h
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : x = 1 := by
    revert x
    decide
  rw [hx1]
  exact mem_zpowers _

private theorem pSL_zHat_substWord_eq_one
    {w : List (Fin 2 × Bool)} (hw : zHat w ∈ pSL.ker) :
    pSL (zHat (substWord deltaWs w)) = 1 := by
  rw [← deltaHat_zHat, pSL_deltaHat, MonoidHom.mem_ker.mp hw, map_one]

private theorem deltaHat_zOne
    : deltaHat (zHat zOne) = zHat zTwo := by
  have hmem := mem_zpowers_of_deltaWalks (List.mem_cons_self ..)
  rw [zHat_append, show zHat (FreeGroup.invRev zTwo) = (zHat zTwo)⁻¹ from by
    rw [zHat, zHat, ← FreeGroup.inv_mk, map_inv]] at hmem
  have h := eq_one_of_mem_zpowers hmem (by
    rw [map_mul, map_inv, pSL_zHat_substWord_eq_one zOne_mem, MonoidHom.mem_ker.mp zTwo_mem,
      inv_one, mul_one])
  rw [deltaHat_zHat]
  exact mul_inv_eq_one.mp h

private theorem deltaHat_zTwo
    : deltaHat (zHat zTwo) = (zHat zOne * zHat zTwo)⁻¹ := by
  have hmem := mem_zpowers_of_deltaWalks (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [zHat_append, zHat_append] at hmem
  have h := eq_one_of_mem_zpowers hmem (by
    rw [map_mul, map_mul, pSL_zHat_substWord_eq_one zTwo_mem, MonoidHom.mem_ker.mp zOne_mem,
      MonoidHom.mem_ker.mp zTwo_mem, one_mul, one_mul])
  rw [deltaHat_zHat, eq_inv_iff_mul_eq_one, ← mul_assoc]
  exact h

private theorem deltaHat_mem_ker
    {m : Cover} (hm : m ∈ pSL.ker) : deltaHat m ∈ pSL.ker := by
  rw [MonoidHom.mem_ker, pSL_deltaHat, MonoidHom.mem_ker.mp hm, map_one]

private theorem dGL_mul_three : dGL * dGL * dGL = 1 := by
  rw [← dGL_pow_three, pow_succ, pow_two]

private theorem deltaHat_surjective
    : Function.Surjective deltaHat := by
  have h3 : deltaHat.comp (deltaHat.comp deltaHat) = MonoidHom.id Cover := by
    refine cover_hom_ext pSL (ker_pSL_le_ker_piX.trans ker_piX_le_center)
      (MonoidHom.ext fun c => ?_)
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, pSL_deltaHat]
    rw [← conjSL_mul, ← conjSL_mul, dGL_mul_three, conjSL_one]
  intro c
  refine ⟨deltaHat (deltaHat c), ?_⟩
  have := DFunLike.congr_fun h3 c
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply] using this

private theorem ker_eq_of_iff
    {E E' : Type*} [Group E] [Group E'] {μ : Cover →* E}
    {ν : Cover →* E'} {K : Subgroup E} {K' : Subgroup E'} (hK : Nat.card K = 2)
    (hK' : Nat.card K' = 2) (hμ : ∀ m ∈ pSL.ker, μ m ∈ K) (hν : ∀ m ∈ pSL.ker, ν m ∈ K')
    (hμk : μ.ker ≤ pSL.ker) (hνk : ν.ker ≤ pSL.ker)
    (h1 : μ (zHat zOne) = 1 ↔ ν (zHat zOne) = 1) (h2 : μ (zHat zTwo) = 1 ↔ ν (zHat zTwo) = 1) :
    μ.ker = ν.ker := by
  have key : ∀ i j : ℕ, μ (zHat zOne ^ i * zHat zTwo ^ j) = 1 ↔
      ν (zHat zOne ^ i * zHat zTwo ^ j) = 1 := by
    intro i j
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
      pow_mul_pow_eq_one_iff hK (hμ _ zOne_mem) (hμ _ zTwo_mem),
      pow_mul_pow_eq_one_iff hK' (hν _ zOne_mem) (hν _ zTwo_mem), h1, h2]
  ext c
  constructor
  · intro hc
    obtain ⟨i, j, rfl⟩ := exists_zOne_zTwo (hμk hc)
    exact (key i j).mp hc
  · intro hc
    obtain ⟨i, j, rfl⟩ := exists_zOne_zTwo (hνk hc)
    exact (key i j).mpr hc

private theorem not_both_one
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (h2 : Nat.card π.ker = 2) :
    ¬ (coverLiftOf hπ hC (zHat zOne) = 1 ∧ coverLiftOf hπ hC (zHat zTwo) = 1) := by
  rintro ⟨hu, hv⟩
  have hbot : π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨m, hm, rfl⟩ := exists_of_mem_ker hπ hC hy
    obtain ⟨i, j, rfl⟩ := exists_zOne_zTwo hm
    rw [Subgroup.mem_bot, map_mul, map_pow, map_pow, hu, hv, one_pow, one_pow, one_mul]
  rw [hbot, Subgroup.card_bot] at h2
  omega

private def deltaPow
    : ℕ → Cover →* Cover
  | 0 => MonoidHom.id Cover
  | k + 1 => deltaHat.comp (deltaPow k)

private theorem pSL_deltaPow
    (k : ℕ) (c : Cover) :
    pSL (deltaPow k c) = conjSL (dGL ^ k) (pSL c) := by
  induction k with
  | zero => rw [pow_zero, conjSL_one]; rfl
  | succ k ih =>
    rw [deltaPow, MonoidHom.comp_apply, pSL_deltaHat, ih, pow_succ', conjSL_mul]

private theorem deltaPow_surjective
    (k : ℕ) : Function.Surjective (deltaPow k) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih => exact deltaHat_surjective.comp ih

private theorem deltaPow_mem_ker
    (k : ℕ) {m : Cover} (hm : m ∈ pSL.ker) :
    deltaPow k m ∈ pSL.ker := by
  rw [MonoidHom.mem_ker, pSL_deltaPow, MonoidHom.mem_ker.mp hm, map_one]

private theorem ker_comp_deltaPow_le
    {E' : Type*} [Group E'] [Group.IsPerfect E']
    {π' : E' →* SL3} (hπ' : Function.Surjective π') (hC' : π'.ker ≤ center E') (k : ℕ) :
    ((coverLiftOf hπ' hC').comp (deltaPow k)).ker ≤ pSL.ker := fun c hc => by
  have h : deltaPow k c ∈ pSL.ker :=
    ker_coverLiftOf_le hπ' hC' (show deltaPow k c ∈ (coverLiftOf hπ' hC').ker from hc)
  rw [MonoidHom.mem_ker, pSL_deltaPow] at h
  exact conjSL_eq_one h

private theorem prop_cases {p q p' q' : Prop} (hn : ¬(p ∧ q)) (hn' : ¬(p' ∧ q')) :
    ((p ↔ p') ∧ (q ↔ q')) ∨ ((p ↔ q') ∧ (q ↔ (p' ↔ q'))) ∨ ((p ↔ (p' ↔ q')) ∧ (q ↔ p')) := by
  tauto

private theorem exists_twist
    {E E' : Type*} [Group E] [Group E'] [Group.IsPerfect E]
    [Group.IsPerfect E'] {π : E →* SL3} {π' : E' →* SL3} (hπ : Function.Surjective π)
    (hπ' : Function.Surjective π') (hC : π.ker ≤ center E) (hC' : π'.ker ≤ center E')
    (h2 : Nat.card π.ker = 2) (h2' : Nat.card π'.ker = 2) :
    ∃ k < 3, (coverLiftOf hπ hC (zHat zOne) = 1 ↔
        coverLiftOf hπ' hC' (deltaPow k (zHat zOne)) = 1) ∧
      (coverLiftOf hπ hC (zHat zTwo) = 1 ↔ coverLiftOf hπ' hC' (deltaPow k (zHat zTwo)) = 1) := by
  have hu' := coverLiftOf_mem_ker hπ' hC' zOne_mem
  have hv' := coverLiftOf_mem_ker hπ' hC' zTwo_mem
  have hinv : coverLiftOf hπ' hC' ((zHat zOne * zHat zTwo)⁻¹) = 1 ↔
      (coverLiftOf hπ' hC' (zHat zOne) = 1 ↔ coverLiftOf hπ' hC' (zHat zTwo) = 1) := by
    have h := pow_mul_pow_eq_one_iff h2' hu' hv' 1 1
    rw [pow_one, pow_one] at h
    rw [map_inv, inv_eq_one, map_mul, h]
    simp
  have d1 : deltaPow 1 (zHat zOne) = zHat zTwo := deltaHat_zOne
  have d2 : deltaPow 1 (zHat zTwo) = (zHat zOne * zHat zTwo)⁻¹ := deltaHat_zTwo
  have d3 : deltaPow 2 (zHat zOne) = (zHat zOne * zHat zTwo)⁻¹ := by
    simp only [deltaPow, MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [deltaHat_zOne, deltaHat_zTwo]
  have d4 : deltaPow 2 (zHat zTwo) = zHat zOne := by
    simp only [deltaPow, MonoidHom.comp_apply, MonoidHom.id_apply]
    rw [deltaHat_zTwo, map_inv, map_mul, deltaHat_zOne, deltaHat_zTwo]
    group
  have e0 : deltaPow 0 (zHat zOne) = zHat zOne := rfl
  have e0' : deltaPow 0 (zHat zTwo) = zHat zTwo := rfl
  rcases prop_cases (not_both_one hπ hC h2) (not_both_one hπ' hC' h2') with h | h | h
  · exact ⟨0, by norm_num, by rw [e0]; exact h.1, by rw [e0']; exact h.2⟩
  · exact ⟨1, by norm_num, by rw [d1]; exact h.1, by rw [d2, hinv]; exact h.2⟩
  · exact ⟨2, by norm_num, by rw [d3, hinv]; exact h.1, by rw [d4]; exact h.2⟩

private theorem exists_mulEquiv_dPow
    {E E' : Type*} [Group E] [Group E'] [Group.IsPerfect E]
    [Group.IsPerfect E'] {π : E →* SL3} {π' : E' →* SL3} (hπ : Function.Surjective π)
    (hπ' : Function.Surjective π') (hC : π.ker ≤ center E) (hC' : π'.ker ≤ center E')
    (h2 : Nat.card π.ker = 2) (h2' : Nat.card π'.ker = 2) :
    ∃ k < 3, ∃ φ : E ≃* E', ∀ x, π' (φ x) = conjSL (dGL ^ k) (π x) := by
  obtain ⟨k, hk, h1, h1'⟩ := exists_twist hπ hπ' hC hC' h2 h2'
  have hker : (coverLiftOf hπ hC).ker = ((coverLiftOf hπ' hC').comp (deltaPow k)).ker :=
    ker_eq_of_iff h2 h2' (fun m hm => coverLiftOf_mem_ker hπ hC hm)
      (fun m hm => coverLiftOf_mem_ker hπ' hC' (deltaPow_mem_ker k hm))
      (ker_coverLiftOf_le hπ hC) (ker_comp_deltaPow_le hπ' hC' k) h1 h1'
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_ker_eq (coverLiftOf hπ hC)
    ((coverLiftOf hπ' hC').comp (deltaPow k)) (coverLiftOf_surjective hπ hC)
    ((coverLiftOf_surjective hπ' hC').comp (deltaPow_surjective k)) hker
  refine ⟨k, hk, φ, fun x => ?_⟩
  obtain ⟨c, rfl⟩ := coverLiftOf_surjective hπ hC x
  rw [hφ, MonoidHom.comp_apply, coverLiftOf_apply, pSL_deltaPow, coverLiftOf_apply]

private theorem not_exists_mulEquiv_d
    {E : Type*} [Group E] [Group.IsPerfect E] {π : E →* SL3}
    (hπ : Function.Surjective π) (hC : π.ker ≤ center E) (h2 : Nat.card π.ker = 2) :
    ¬ ∃ φ : E ≃* E, ∀ x, π (φ x) = conjSL dGL (π x) := by
  rintro ⟨φ, hφ⟩
  have hcomm : φ.toMonoidHom.comp (coverLiftOf hπ hC) = (coverLiftOf hπ hC).comp deltaHat := by
    refine cover_hom_ext π hC (MonoidHom.ext fun c => ?_)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hφ, coverLiftOf_apply,
      pSL_deltaHat]
  have hfix : ∀ y ∈ π.ker, φ y = y := by
    intro y hy
    have hφy : φ y ∈ π.ker := by
      rw [MonoidHom.mem_ker, hφ, MonoidHom.mem_ker.mp hy, map_one]
    by_cases h1 : y = 1
    · rw [h1, map_one]
    · exact eq_of_card_two h2 hφy hy (fun h => h1 (φ.injective (h.trans (map_one φ).symm)))
        h1
  have hl : ∀ m ∈ pSL.ker, coverLiftOf hπ hC (deltaHat m) = coverLiftOf hπ hC m := by
    intro m hm
    rw [← MonoidHom.comp_apply (coverLiftOf hπ hC) deltaHat, ← hcomm, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, hfix _ (coverLiftOf_mem_ker hπ hC hm)]
  have hu := coverLiftOf_mem_ker hπ hC zOne_mem
  have e1 : coverLiftOf hπ hC (zHat zTwo) = coverLiftOf hπ hC (zHat zOne) := by
    rw [← deltaHat_zOne, hl _ zOne_mem]
  have e2 : (coverLiftOf hπ hC (zHat zOne) * coverLiftOf hπ hC (zHat zTwo))⁻¹ =
      coverLiftOf hπ hC (zHat zTwo) := by
    rw [← map_mul, ← map_inv, ← deltaHat_zTwo, hl _ zTwo_mem]
  have hu1 : coverLiftOf hπ hC (zHat zOne) = 1 := by
    rw [e1, ← sq, sq_eq_one_of_card_two h2 hu, inv_one] at e2
    exact e2.symm
  exact not_both_one hπ hC h2 ⟨hu1, by rw [e1, hu1]⟩

private theorem conjSL_toGL {R : Type*} [CommRing R] (h A : Matrix.SpecialLinearGroup (Fin 3) R) :
    conjSL (Matrix.SpecialLinearGroup.toGL h) A = h * A * h⁻¹ :=
  Subtype.ext rfl

private theorem det_dGL : Matrix.GeneralLinearGroup.det dGL ^ 3 = 1 := by
  rw [← map_pow, dGL_pow_three, map_one]

private theorem exists_eq_mul_dPow {g : GL (Fin 3) F4} (hg : (g : M3).det ≠ 1) :
    ∃ j : ℕ, (j = 1 ∨ j = 2) ∧ ∃ h : SL3, g = Matrix.SpecialLinearGroup.toGL h * dGL ^ j := by
  have h0 : (g : M3).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hd : (dGL : M3).det = ⟨2⟩ := by
    change dMat.toMatrix.det = _
    rw [det_toMatrix]
    rfl
  have hcases : ∀ x : F4, x ≠ 0 → x ≠ 1 → x = ⟨2⟩ ∨ x = ⟨3⟩ := by
    rintro ⟨c⟩ h0 h1
    fin_cases c
    · exact absurd rfl h0
    · exact absurd rfl h1
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨j, hj, hdet⟩ : ∃ j : ℕ, (j = 1 ∨ j = 2) ∧
      (g : M3).det = ((dGL ^ j : GL (Fin 3) F4) : M3).det := by
    rcases hcases _ h0 hg with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, pow_one, hd]⟩
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [h, Units.val_pow_eq_pow_val, Matrix.det_pow, hd]
      rfl
  let h : SL3 := ⟨(g : M3) * (((dGL ^ j)⁻¹ : GL (Fin 3) F4) : M3), by
    rw [Matrix.det_mul, hdet, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one]⟩
  refine ⟨j, hj, h, Units.ext ?_⟩
  rw [Units.val_mul]
  change (g : M3) = (g : M3) * (((dGL ^ j)⁻¹ : GL (Fin 3) F4) : M3) *
    ((dGL ^ j : GL (Fin 3) F4) : M3)
  rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

private theorem not_exists_mulEquiv_conj_F4
    {E : Type*} [Group E] [Group.IsPerfect E]
    {π : E →* SL3} (hπ : Function.Surjective π) (hC : π.ker ≤ center E)
    (h2 : Nat.card π.ker = 2) {g : GL (Fin 3) F4} (hg : (g : M3).det ≠ 1) :
    ¬ ∃ φ : E ≃* E, ∀ x, π (φ x) = conjSL g (π x) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨j, hj, h, rfl⟩ := exists_eq_mul_dPow hg
  obtain ⟨y, hy⟩ := hπ h⁻¹
  have hφ₁ : ∀ x, π ((φ.trans (MulAut.conj y)) x) = conjSL (dGL ^ j) (π x) := by
    intro x
    rw [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hy, hφ, conjSL_mul,
      conjSL_toGL, inv_inv]
    group
  rcases hj with rfl | rfl
  · exact not_exists_mulEquiv_d hπ hC h2 ⟨_, fun x => by rw [hφ₁, pow_one]⟩
  · refine not_exists_mulEquiv_d hπ hC h2 ⟨(φ.trans (MulAut.conj y)).trans
      (φ.trans (MulAut.conj y)), fun x => ?_⟩
    rw [MulEquiv.trans_apply, hφ₁, hφ₁, ← conjSL_mul, ← pow_add,
      show dGL ^ (2 + 2) = dGL ^ 3 * dGL by rw [← pow_succ], dGL_pow_three, one_mul]

private theorem exists_mulEquiv_conj_pow_F4
    {E E' : Type*} [Group E] [Group E']
    [Group.IsPerfect E] [Group.IsPerfect E'] {π : E →* SL3} {π' : E' →* SL3}
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π') (hC : π.ker ≤ center E)
    (hC' : π'.ker ≤ center E') (h2 : Nat.card π.ker = 2) (h2' : Nat.card π'.ker = 2)
    {g : GL (Fin 3) F4} (hg : (g : M3).det ≠ 1) :
    ∃ k < 3, ∃ φ : E ≃* E', ∀ x, π' (φ x) = conjSL (g ^ k) (π x) := by
  obtain ⟨k, hk, φ, hφ⟩ := exists_mulEquiv_dPow hπ hπ' hC hC' h2 h2'
  obtain ⟨j, hj, h, rfl⟩ := exists_eq_mul_dPow hg
  have hk' : j * (j * k % 3) % 3 = k := by
    rcases hj with rfl | rfl <;> omega
  have hdet : Matrix.GeneralLinearGroup.det
      ((Matrix.SpecialLinearGroup.toGL h * dGL ^ j) ^ (j * k % 3) * (dGL ^ k)⁻¹) = 1 := by
    rw [map_mul, map_pow, map_mul, Matrix.SpecialLinearGroup.coeToGL_det, one_mul, map_inv, map_pow,
      map_pow, ← pow_mul, pow_eq_pow_mod (j * (j * k % 3)) det_dGL, hk', mul_inv_cancel]
  let h' : SL3 := ⟨(((Matrix.SpecialLinearGroup.toGL h * dGL ^ j) ^ (j * k % 3) * (dGL ^ k)⁻¹ :
    GL (Fin 3) F4) : M3), by rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]⟩
  have hg' : (Matrix.SpecialLinearGroup.toGL h * dGL ^ j) ^ (j * k % 3) =
      Matrix.SpecialLinearGroup.toGL h' * dGL ^ k :=
    Units.ext <| by
      rw [Units.val_mul]
      change _ = (((Matrix.SpecialLinearGroup.toGL h * dGL ^ j) ^ (j * k % 3) * (dGL ^ k)⁻¹ :
        GL (Fin 3) F4) : M3) * _
      rw [← Units.val_mul, inv_mul_cancel_right]
  obtain ⟨y, hy⟩ := hπ' h'
  refine ⟨j * k % 3, Nat.mod_lt _ (by norm_num), φ.trans (MulAut.conj y), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hy, hφ, hg',
    conjSL_mul, conjSL_toGL]

section Transfer

variable {K : Type*} [Field K]

private theorem nonempty_ringEquiv [Finite K] (hK : Nat.card K = 4) : Nonempty (F4 ≃+* K) := by
  have := Fintype.ofFinite K
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [F4.card, ← Nat.card_eq_fintype_card, hK])⟩

private def slK (e : F4 ≃+* K) : SL3 ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (MonoidHom.ext fun _ => Matrix.SpecialLinearGroup.ext _ _ fun _ _ => by simp)
    (MonoidHom.ext fun _ => Matrix.SpecialLinearGroup.ext _ _ fun _ _ => by simp)

private def glBack (e : F4 ≃+* K) : GL (Fin 3) K →* GL (Fin 3) F4 :=
  Matrix.GeneralLinearGroup.map e.symm.toRingHom

private theorem coe_glBack (e : F4 ≃+* K) (g : GL (Fin 3) K) :
    ((glBack e g : GL (Fin 3) F4) : M3) =
      e.symm.toRingHom.mapMatrix (g : Matrix (Fin 3) (Fin 3) K) :=
  rfl

private theorem mapMatrix_symm (e : F4 ≃+* K) (M : Matrix (Fin 3) (Fin 3) K) :
    e.toRingHom.mapMatrix (e.symm.toRingHom.mapMatrix M) = M := by
  ext i j
  simp

private theorem slK_conjSL (e : F4 ≃+* K) (g : GL (Fin 3) K) (A : SL3) :
    slK e (conjSL (glBack e g) A) = conjSL g (slK e A) := by
  apply Subtype.ext
  change e.toRingHom.mapMatrix (((glBack e g : GL (Fin 3) F4) : M3) * (A : M3) *
    (((glBack e g)⁻¹ : GL (Fin 3) F4) : M3)) =
      (g : Matrix (Fin 3) (Fin 3) K) * e.toRingHom.mapMatrix (A : M3) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [map_mul, map_mul, ← map_inv, coe_glBack, coe_glBack, mapMatrix_symm, mapMatrix_symm]

private theorem det_glBack (e : F4 ≃+* K) {g : GL (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 1) :
    ((glBack e g : GL (Fin 3) F4) : M3).det ≠ 1 := by
  rw [coe_glBack, ← RingHom.map_det]
  intro h
  apply hg
  have h' : e.symm ((g : Matrix (Fin 3) (Fin 3) K).det) = e.symm 1 := by
    rw [map_one]
    exact h
  exact e.symm.injective h'

private theorem ker_slK_symm_comp (e : F4 ≃+* K) {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 3) K) :
    ((slK e).symm.toMonoidHom.comp π).ker = π.ker := by
  ext x
  simp

private theorem slK_symm_comp_apply (e : F4 ≃+* K) {E : Type*} [Group E]
    (π : E →* Matrix.SpecialLinearGroup (Fin 3) K) (x : E) :
    slK e (((slK e).symm.toMonoidHom.comp π) x) = π x := by
  simp

end Transfer

theorem card_ker_le_four
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4) {E : Type*}
    [Group E] [Group.IsPerfect E] (η : E →* Matrix.SpecialLinearGroup (Fin 3) K)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : ∀ c ∈ η.ker, c ^ 2 = 1) :
    Nat.card η.ker ≤ 4 := by
  obtain ⟨e⟩ := nonempty_ringEquiv hK
  have hker := ker_slK_symm_comp e η
  have h := card_ker_le_four_F4 ((slK e).symm.toMonoidHom.comp η)
    ((slK e).symm.surjective.comp hη) (by rw [hker]; exact hC)
    (by rw [hker]; exact h2)
  rwa [hker] at h

theorem exists_mulEquiv_conj_pow
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (hg : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 1) {E E' : Type*} [Group E]
    [Group E'] [Group.IsPerfect E] [Group.IsPerfect E']
    (π : E →* Matrix.SpecialLinearGroup (Fin 3) K) (π' : E' →* Matrix.SpecialLinearGroup (Fin 3) K)
    (hπ : Function.Surjective π)
    (hπ' : Function.Surjective π') (hC : π.ker ≤ center E) (hC' : π'.ker ≤ center E')
    (h2 : Nat.card π.ker = 2) (h2' : Nat.card π'.ker = 2) :
    ∃ k < 3, ∃ φ : E ≃* E', ∀ x, (π' (φ x) : Matrix (Fin 3) (Fin 3) K) =
      ((g ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * π x *
        (((g ^ k)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨e⟩ := nonempty_ringEquiv hK
  have hker := ker_slK_symm_comp e π
  have hker' := ker_slK_symm_comp e π'
  obtain ⟨k, hk, φ, hφ⟩ := exists_mulEquiv_conj_pow_F4
    (π := (slK e).symm.toMonoidHom.comp π)
    (π' := (slK e).symm.toMonoidHom.comp π')
    ((slK e).symm.surjective.comp hπ) ((slK e).symm.surjective.comp hπ')
    (by rw [hker]; exact hC) (by rw [hker']; exact hC') (by rw [hker]; exact h2)
    (by rw [hker']; exact h2') (det_glBack e hg)
  refine ⟨k, hk, φ, fun x => ?_⟩
  have h := congrArg (slK e) (hφ x)
  rw [slK_symm_comp_apply, ← map_pow, slK_conjSL, slK_symm_comp_apply] at h
  rw [h, coe_conjSL]

theorem not_exists_mulEquiv_conj
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (g : GL (Fin 3) K) (hg : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 1) {E : Type*} [Group E]
    [Group.IsPerfect E] (π : E →* Matrix.SpecialLinearGroup (Fin 3) K) (hπ : Function.Surjective π)
    (hC : π.ker ≤ center E) (h2 : Nat.card π.ker = 2) :
    ¬ ∃ φ : E ≃* E, ∀ x, (π (φ x) : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * π x * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨e⟩ := nonempty_ringEquiv hK
  have hker := ker_slK_symm_comp e π
  rintro ⟨φ, hφ⟩
  refine not_exists_mulEquiv_conj_F4 (π := (slK e).symm.toMonoidHom.comp π)
    ((slK e).symm.surjective.comp hπ) (by rw [hker]; exact hC)
    (by rw [hker]; exact h2) (det_glBack e hg) ⟨φ, fun x => (slK e).injective ?_⟩
  rw [slK_symm_comp_apply, slK_conjSL, slK_symm_comp_apply]
  exact Subtype.ext (hφ x)

end CFSG.LieType.Multipliers.L34Upper
