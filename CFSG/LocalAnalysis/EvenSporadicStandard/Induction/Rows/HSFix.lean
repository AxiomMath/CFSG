module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fours
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second
public import Certificates.Certificate27020
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Recognition.HSMultiplier CFSG.LieType.Multipliers
  CFSG.ComponentClassification.PerfectAutomorphisms CFSG.EvenSporadicStandard.Solomon78

section General

theorem lift_eq_of_central {E : Type*} [Group E] {ι : Type*} (f f' : ι → E)
    (hz : ∀ j, (f j)⁻¹ * f' j ∈ Subgroup.center E) {w : FreeGroup ι}
    (hw : w ∈ commutator (FreeGroup ι)) : FreeGroup.lift f' w = FreeGroup.lift f w := by
  let χ : FreeGroup ι →* Subgroup.center E := FreeGroup.lift fun j => ⟨(f j)⁻¹ * f' j, hz j⟩
  have key : ∀ w : FreeGroup ι, FreeGroup.lift f' w = FreeGroup.lift f w * (χ w : E) := by
    intro w
    induction w using FreeGroup.induction_on with
    | one => simp
    | of j => simp [χ]
    | inv_of j ih =>
      have hc := Subgroup.mem_center_iff.1 (inv_mem (χ (FreeGroup.of j)).2)
      simp only [map_inv, Subgroup.coe_inv, ih, mul_inv_rev]
      exact (hc _).symm
    | mul x y ihx ihy =>
      have hc := Subgroup.mem_center_iff.1 (χ x).2
      simp only [map_mul, Subgroup.coe_mul, ihx, ihy]
      rw [mul_assoc, ← mul_assoc (χ x : E), ← hc, mul_assoc]
      simp only [mul_assoc]
  rw [key w, (MonoidHom.mem_ker.1 ((Abelianization.commutator_subset_ker χ) hw))]
  simp

theorem hom_lift {X Y : Type*} [Group X] [Group Y] {ι : Type*} (f : X →* Y) (g : ι → X)
    (w : FreeGroup ι) : f (FreeGroup.lift g w) = FreeGroup.lift (fun i => f (g i)) w := by
  have : f.comp (FreeGroup.lift g) = FreeGroup.lift (fun i => f (g i)) :=
    FreeGroup.ext_hom _ _ (fun i => by simp)
  exact DFunLike.congr_fun this w

theorem subsetProd_mem {G : Type*} [Group G] (S : Subgroup G) (x : Fin 4 → G)
    (hx : ∀ l, x l ∈ S) (m : ℕ) : subsetProd x m ∈ S := by
  have key : ∀ (L : List (Fin 4)) (a : G), a ∈ S →
      L.foldl (fun acc l => if m.testBit l.val then acc * x l else acc) a ∈ S := by
    intro L
    induction L with
    | nil => intro a ha; exact ha
    | cons l L ih =>
      intro a ha
      simp only [List.foldl_cons]
      cases hb : m.testBit l.val
      · simpa [hb] using ih a ha
      · simpa [hb] using ih (a * x l) (S.mul_mem ha (hx l))
  exact key _ _ S.one_mem

theorem closure_elemAbelian {G : Type*} [Group G] (s : Set G) (hsq : ∀ x ∈ s, x * x = 1)
    (hc : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    (∀ x ∈ closure s, ∀ y ∈ closure s, x * y = y * x) ∧ ∀ x ∈ closure s, x * x = 1 := by
  have h1 : closure s ≤ centralizer s := by
    rw [closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    exact hc y hy x hx
  have h2 : ∀ x ∈ closure s, ∀ y ∈ closure s, x * y = y * x := by
    intro x hx y hy
    have h3 : closure s ≤ centralizer ({x} : Set G) := by
      rw [closure_le]
      intro z hz
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (h1 hx) z hz
    exact (mem_centralizer_singleton_iff.1 (h3 hy)).symm
  refine ⟨h2, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hsq y hy
  | one => simp
  | mul y z hy hz ihy ihz =>
    calc y * z * (y * z) = y * (z * y) * z := by group
      _ = y * (y * z) * z := by rw [h2 z hz y hy]
      _ = (y * y) * (z * z) := by group
      _ = 1 := by rw [ihy, ihz, one_mul]
  | inv y hy ihy =>
    calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
      _ = 1 := by rw [ihy, inv_one]

end General

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.InvolutionFixesElem.of_mulEquiv
    {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') {n : ℕ} (h : InvolutionFixesElem K n) :
    InvolutionFixesElem K' n := by
  intro α hα1 hα2
  have hβ1 : (MulAut.congr e).symm α ≠ 1 := fun h1 =>
    hα1 ((MulAut.congr e).symm.map_eq_one_iff.1 h1)
  have hβ2 : (MulAut.congr e).symm α * (MulAut.congr e).symm α = 1 := by
    rw [← map_mul, hα2, map_one]
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := h _ hβ1 hβ2
  refine ⟨S.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h2 : α (e x) = e ((MulAut.congr e).symm α x) := by
      rw [MulAut.congr_symm_apply]
      exact (e.apply_symm_apply _).symm
    show α (e x) = e x
    rw [h2, hS1 x hx]
  · rintro _ ⟨x, hx, rfl⟩
    show e x * e x = 1
    rw [← map_mul, hS2 x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show e x * e y = e y * e x
    rw [← map_mul, ← map_mul, hS3 x hx y hy]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hS4

section Plain

variable {E : Type} [Group E]

@[expose] noncomputable def CoverMaps.autInd (M : CoverMaps E) : MulAut E →* MulAut ↥hsP :=
  (MulAut.congr M.centerQuotEquiv).toMonoidHom.comp (centerQuotientHom E)

theorem CoverMaps.autInd_apply (M : CoverMaps E) (α : MulAut E) (x : E) :
    M.autInd α (M.π x) = M.π (α x) := by
  change M.centerQuotEquiv (onCenterQuotient α (M.centerQuotEquiv.symm (M.π x))) = _
  have h1 : M.centerQuotEquiv.symm (M.π x) = QuotientGroup.mk' (center E) x :=
    (MulEquiv.symm_apply_eq _).2 rfl
  rw [h1, onCenterQuotient_apply_mk]
  rfl

theorem CoverMaps.autInd_injective (M : CoverMaps E) [Group.IsPerfect E] :
    Function.Injective M.autInd :=
  (MulAut.congr M.centerQuotEquiv).injective.comp (centerQuotientHom_injective E)

@[expose] noncomputable def CoverMaps.gv (M : CoverMaps E) (w : List (Fin 6 × Bool)) : E :=
  FreeGroup.lift M.g (FreeGroup.mk w)

end Plain

section Cover

variable
  {E : Type} [Group E]

theorem CoverMaps.rho_gv (M : CoverMaps E) (w : List (Fin 6 × Bool)) :
    M.ρ (M.gv w) = yVal w := by
  unfold CoverMaps.gv yVal
  rw [hom_lift]
  simp only [M.ρ_g]

theorem CoverMaps.pi_gv (M : CoverMaps E) (w : List (Fin 6 × Bool)) :
    ((M.π (M.gv w) : ↥hsP) : Equiv.Perm (Fin 3850)) =
      FreeGroup.lift harXPerm (FreeGroup.mk w) := by
  have h := hom_lift (hsP.subtype.comp M.π) M.g (FreeGroup.mk w)
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, M.π_g] at h
  exact h

theorem CoverModel.lift_comm (M : CoverModel E) (k : Fin 6) :
    FreeGroup.lift M.g (hsCommW k) = M.g k := by
  apply M.ρ_inj
  rw [hom_lift]
  simp only [M.ρ_g]
  exact (harY_relators.2 k)

theorem CoverModel.fixes_gens (M : CoverModel E) {i : Fin 4} (hs : HfxSound i) (α : MulAut E)
    (hπ : ∀ x : E, ((M.π (α x) : ↥hsP) : Equiv.Perm (Fin 3850)) =
      hfxRhoPerm i * (M.π x : Equiv.Perm (Fin 3850)) * (hfxRhoPerm i)⁻¹) (l : Fin 4) :
    α (M.gv (hfxE i l)) = M.gv (hfxE i l) := by
  have hcent : ∀ j, (M.gv (hfxW i j))⁻¹ * α (M.g j) ∈ Subgroup.center E := by
    intro j
    refine (M.π_ker _).1 (Subtype.ext ?_)
    rw [map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hπ, M.π_g, M.pi_gv, hs.pi_word]
    exact inv_mul_cancel _
  have hg : ∀ k, α (M.g k) =
      FreeGroup.lift (fun j => M.gv (hfxW i j)) (hsCommW k) := by
    intro k
    have h1 : α (M.g k) = FreeGroup.lift (fun j => α (M.g j)) (hsCommW k) := by
      conv_lhs => rw [← M.lift_comm k]
      exact hom_lift α.toMonoidHom M.g (hsCommW k)
    rw [h1]
    exact lift_eq_of_central (fun j => M.gv (hfxW i j)) (fun j => α (M.g j)) hcent
      (mk_commWords_mem_commutator (hsComm k))
  have hρA : ∀ k, M.ρ (α (M.g k)) = hfxAPerm i k := by
    intro k
    rw [hg k, hom_lift]
    have : (fun j => M.ρ (M.gv (hfxW i j))) = hfxTPerm i := funext fun j => M.rho_gv _
    rw [this]
    rfl
  apply M.ρ_inj
  have h1 : α (M.gv (hfxE i l)) =
      FreeGroup.lift (fun k => α (M.g k)) (FreeGroup.mk (hfxE i l)) :=
    hom_lift α.toMonoidHom M.g _
  rw [h1, hom_lift, M.rho_gv]
  have : (fun k => M.ρ (α (M.g k))) = hfxAPerm i := funext hρA
  rw [this]
  exact hs.fixed l

theorem CoverModel.exists_elemAbelian [Finite E] (M : CoverModel E) {i : Fin 4} (hs : HfxSound i)
    (α : MulAut E)
    (hπ : ∀ x : E, ((M.π (α x) : ↥hsP) : Equiv.Perm (Fin 3850)) =
      hfxRhoPerm i * (M.π x : Equiv.Perm (Fin 3850)) * (hfxRhoPerm i)⁻¹) :
    ∃ S : Subgroup E, (∀ x ∈ S, α x = x) ∧ (∀ x ∈ S, x * x = 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧ 16 ≤ Nat.card S := by
  set e : Fin 4 → E := fun l => M.gv (hfxE i l) with he
  have hρe : ∀ l, M.ρ (e l) = hfxEPerm i l := fun l => M.rho_gv _
  have hsq : ∀ l, e l * e l = 1 := fun l =>
    M.ρ_inj (by rw [map_mul, hρe, hs.sq, map_one])
  have hcomm : ∀ l l', e l * e l' = e l' * e l := fun l l' =>
    M.ρ_inj (by rw [map_mul, map_mul, hρe, hρe, hs.comm])
  have hfix : ∀ l, α (e l) = e l := fun l => M.fixes_gens hs α hπ l
  obtain ⟨hc1, hc2⟩ := closure_elemAbelian (Set.range e)
    (by rintro _ ⟨l, rfl⟩; exact hsq l)
    (by rintro _ ⟨l, rfl⟩ _ ⟨l', rfl⟩; exact hcomm l l')
  refine ⟨closure (Set.range e), ?_, hc2, hc1, ?_⟩
  · have hle : closure (Set.range e) ≤ α.toMonoidHom.eqLocus (MonoidHom.id E) := by
      rw [closure_le]
      rintro _ ⟨l, rfl⟩
      exact hfix l
    intro x hx
    exact hle hx
  · let P : Fin 16 → closure (Set.range e) := fun m =>
      ⟨subsetProd e m.val, subsetProd_mem _ e (fun l => subset_closure (Set.mem_range_self l)) _⟩
    have hinj : Function.Injective P := by
      intro a b hab
      by_contra hne
      apply hs.distinct a b hne
      have h1 : subsetProd e a.val = subsetProd e b.val := congrArg Subtype.val hab
      have h2 := congrArg M.ρ h1
      rw [map_subsetProd, map_subsetProd] at h2
      have h3 : (fun l => M.ρ (e l)) = hfxEPerm i := funext hρe
      rwa [h3] at h2
    simpa using Nat.card_le_card_of_injective P hinj

end Cover

section Main

variable
  {E : Type} [Group E]

theorem hfxCheck_true (i : Fin 4) : hfxCheck i = true := by
  have h : hfxOK = true := Certificates.certificate27020
  exact List.all_eq_true.1 h i (List.mem_finRange i)

theorem involutionFixesElem_of_coverModel [Finite E] (hperf : Group.IsPerfect E)
    (M : CoverModel E) : InvolutionFixesElem E 16 := by
  have := hperf
  intro α hα1 hα2
  obtain ⟨e, he, -⟩ := hs_full_automorphism_model
  obtain ⟨ν, hν⟩ : ∃ ν : hsR, e ν = M.autInd α := ⟨e.symm _, e.apply_symm_apply _⟩
  have hν1 : ν ≠ 1 := by
    rintro rfl
    apply hα1
    apply M.autInd_injective
    rw [← hν, map_one, map_one]
  have hν2 : ν * ν = 1 := by
    apply e.injective
    rw [map_mul, hν, ← map_mul, hα2, map_one, map_one]
  have hord : orderOf (ν : Equiv.Perm (Fin 3850)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hν2) hν1
  obtain ⟨-, -, -, -, -, -, hcov⟩ := HSStd.class_data_hs
  obtain ⟨g, hg, hcase⟩ := hcov ν ν.2 hord
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, (ν : Equiv.Perm (Fin 3850)) = g * hfxRhoPerm i * g⁻¹ := by
    rcases hcase with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨y, hy⟩ := M.π_surj ⟨g, hg⟩
  have hy' : ((M.π y : ↥hsP) : Equiv.Perm (Fin 3850)) = g := congrArg Subtype.val hy
  have hνπ : ∀ z : E, ((M.π (α z) : ↥hsP) : Equiv.Perm (Fin 3850)) =
      (ν : Equiv.Perm (Fin 3850)) * (M.π z : Equiv.Perm (Fin 3850)) *
        (ν : Equiv.Perm (Fin 3850))⁻¹ := by
    intro z
    rw [← M.autInd_apply α z, ← hν]
    exact he ν (M.π z)
  let α' : MulAut E := MulAut.conj y⁻¹ * α * MulAut.conj y
  have hα'x : ∀ x : E, α' x = y⁻¹ * α (y * x * y⁻¹) * y := by
    intro x
    simp [α', MulAut.mul_apply, MulAut.conj_apply]
  have hπ : ∀ x : E, ((M.π (α' x) : ↥hsP) : Equiv.Perm (Fin 3850)) =
      hfxRhoPerm i * (M.π x : Equiv.Perm (Fin 3850)) * (hfxRhoPerm i)⁻¹ := by
    intro x
    rw [hα'x]
    have hz := hνπ (y * x * y⁻¹)
    generalize α (y * x * y⁻¹) = z at hz ⊢
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hz ⊢
    rw [hz, hy', hi]
    group
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ :=
    M.exists_elemAbelian (hfx_sound i (hfxCheck_true i)) α' hπ
  refine ⟨S.map (MulAut.conj y).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    have h1 := hS1 s hs
    rw [hα'x] at h1
    show α (y * s * y⁻¹) = y * s * y⁻¹
    calc α (y * s * y⁻¹) = y * (y⁻¹ * α (y * s * y⁻¹) * y) * y⁻¹ := by group
      _ = y * s * y⁻¹ := by rw [h1]
  · rintro _ ⟨s, hs, rfl⟩
    show (y * s * y⁻¹) * (y * s * y⁻¹) = 1
    calc (y * s * y⁻¹) * (y * s * y⁻¹) = y * (s * s) * y⁻¹ := by group
      _ = 1 := by rw [hS2 s hs]; group
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    show (y * s * y⁻¹) * (y * t * y⁻¹) = (y * t * y⁻¹) * (y * s * y⁻¹)
    calc (y * s * y⁻¹) * (y * t * y⁻¹) = y * (s * t) * y⁻¹ := by group
      _ = y * (t * s) * y⁻¹ := by rw [hS3 s hs t ht]
      _ = (y * t * y⁻¹) * (y * s * y⁻¹) := by group
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    exact hS4

end Main

end CFSG.EvenSporadicStandard.TwoHS
