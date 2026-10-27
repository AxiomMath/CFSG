module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.CentralSection
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Components
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Core

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

section Helpers

variable {P : (S : Type) → [Group S] → Prop}

private theorem surjective_comp_subtype_iff {Y S : Type*} [Group Y] [Group S] (ψ : Y →* S)
    (H : Subgroup Y) : Function.Surjective (ψ.comp H.subtype) ↔ H.map ψ = ⊤ := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]

private theorem commutator_eq_top_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) : commutator S = ⊤ := by
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left fun h =>
    hS ((_root_.commutator_eq_bot_iff (G := S)).mp h)

private theorem isPerfect_of_minimal {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype)) :
    Group.IsPerfect Y := by
  refine ⟨by_contra fun h => hmin _ h ?_⟩
  rw [surjective_comp_subtype_iff, commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ, ← commutator_def]
  exact commutator_eq_top_of_simple hS

private theorem not_forall_mul_comm {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ ∀ a b : Q, a * b = b * a := by
  intro h
  obtain ⟨a, b, hab⟩ := hQ.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h a b])

private theorem ker_eq_center {Y S : Type*} [Group Y] [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) (hY : CFSG.IsQuasisimple Y) {ψ : Y →* S}
    (hψ : Function.Surjective ψ) : ψ.ker = Subgroup.center Y := by
  refine le_antisymm ?_ ((Subgroup.map_eq_bot_iff _).mp
    (map_eq_bot_of_isSolvable hS hψ inferInstance inferInstance))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hY ψ.normal_ker with h | h
  · obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨y, rfl⟩ := hψ s
    exact (hs (MonoidHom.mem_ker.mp (h.symm ▸ Subgroup.mem_top y))).elim
  · exact h

private theorem inv_mul_mem_centralizer {Y : Type*} [Group Y] {Q : Subgroup Y} [Q.Normal]
    (y : Y) (j : Q) (hj : (MulAut.conjNormal y : MulAut Q) = MulAut.conj j) :
    (j : Y)⁻¹ * y ∈ Subgroup.centralizer (Q : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have e : y * q * y⁻¹ = j * q * (j : Y)⁻¹ := by
    simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using
      congrArg Subtype.val (DFunLike.congr_fun hj ⟨q, hq⟩)
  calc q * ((j : Y)⁻¹ * y) = (j : Y)⁻¹ * (j * q * (j : Y)⁻¹) * y := by group
    _ = (j : Y)⁻¹ * (y * q * y⁻¹) * y := by rw [e]
    _ = (j : Y)⁻¹ * y * q := by group

private theorem map_centralizer_eq_bot_of_isComponent {Y S : Type*} [Group Y] [Group S]
    [IsSimpleGroup S]
    {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    {Q : Subgroup Y} (hQ : CFSG.IsComponent Q) [Q.Normal] :
    (Subgroup.centralizer (Q : Set Y)).map ψ = ⊥ := by
  refine (map_eq_bot_or_eq_top_of_normal hψ inferInstance).resolve_right fun h => ?_
  have htop : Subgroup.centralizer (Q : Set Y) = ⊤ :=
    by_contra fun hne => hmin _ hne ((surjective_comp_subtype_iff ψ _).mpr h)
  refine not_forall_mul_comm hQ.1 fun a b => Subtype.ext ?_
  have hb : (b : Y) ∈ Subgroup.centralizer (Q : Set Y) := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_centralizer_iff.mp hb a a.2

private theorem false_of_isComponent_of_map_eq_bot
    (hout : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], ¬ IsMulCommutative T → P T →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer T))
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] {S : Type} [Group S] [IsSimpleGroup S]
    {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    (ih : ∀ H : Subgroup Y, H ≠ ⊤ → ∀ (T : Type) [Group T] [IsSimpleGroup T],
      ¬ IsMulCommutative T → ∀ φ : ↥H →* T, Function.Surjective φ → P T)
    {Q : Subgroup Y} (hQ : CFSG.IsComponent Q) [Q.Normal] (hQψ : Q.map ψ = ⊥) : False := by
  have hQt : Q ≠ ⊤ := by
    rintro rfl
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ] at hQψ
    exact top_ne_bot hQψ
  have := hQ.1.2.1
  have := hQ.1.1
  have hab : ¬ IsMulCommutative (↥Q ⧸ Subgroup.center ↥Q) := by
    obtain ⟨a, b, hab⟩ := hQ.1.2.2
    exact fun h => hab (h.is_comm.comm a b)
  have := hout _ hab (ih Q hQt _ hab _ (QuotientGroup.mk'_surjective _))
  have := CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient Q
  have hC := map_centralizer_eq_bot_of_isComponent hψ hmin hQ
  have h1 : ∀ y : Y, ψ y = 1 := fun y => by
    obtain ⟨j, hj⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner
      (MulAut.conjNormal : Y →* MulAut Q) y
    have hc := (Subgroup.map_eq_bot_iff _).mp hC (inv_mul_mem_centralizer y j hj)
    have hjk := (Subgroup.map_eq_bot_iff _).mp hQψ j.2
    rw [MonoidHom.mem_ker] at hc hjk
    rw [← mul_inv_cancel_left (j : Y) y, map_mul, hjk, hc, one_mul]
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  obtain ⟨y, rfl⟩ := hψ s
  exact hs (h1 y)

private theorem of_isComponent_of_map_eq_top
    (hiso : ∀ {S T : Type} [Group S] [Group T], (S ≃* T) → P T → P S)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : Subgroup (GL ι K)}
    (hq : ∀ Y : Subgroup (GL ι K), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      P (↥Y ⧸ Subgroup.center ↥Y))
    {Y : Subgroup (GL ι K)} (hYX : Y ≤ X) (hirr : IsIrreducibleOn Y) {S : Type} [Group S]
    [IsSimpleGroup S] (hS : ¬ IsMulCommutative S) {ψ : Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    {Q : Subgroup Y} (hQ : CFSG.IsComponent Q) (hQψ : Q.map ψ = ⊤) : P S := by
  have hQt : Q = ⊤ := by_contra fun hne => hmin Q hne ((surjective_comp_subtype_iff ψ Q).mpr hQψ)
  subst hQt
  have hYq : CFSG.IsQuasisimple Y := hQ.1.of_mulEquiv Subgroup.topEquiv.symm
  exact hiso ((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (ker_eq_center hS hYq hψ))) (hq Y hYX hYq hirr)

private theorem simpleSectionsIn_of_not_isIrreducibleOn {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hlow : ∀ d < Fintype.card ι, SimpleSectionsIn P (GL (Fin d) K))
    {Y : Subgroup (GL ι K)} (hred : ¬ IsIrreducibleOn Y) : SimpleSectionsIn P Y := by
  simp only [IsIrreducibleOn, not_forall, not_or] at hred
  obtain ⟨U, hU, hbot, htop⟩ := hred
  have hle : ∀ g : Y, U ≤ U.comap (natRep Y g) := fun g u hu => hU g g.2 u hu
  have hV : Module.finrank K (ι → K) = Fintype.card ι := Module.finrank_fintype_fun_eq_card K
  have hd₁ : Module.finrank K U < Fintype.card ι := hV ▸ Submodule.finrank_lt htop
  have hd₂ : Module.finrank K ((ι → K) ⧸ U) < Fintype.card ι := by
    have := Submodule.finrank_quotient_add_finrank U
    have : 0 < Module.finrank K U :=
      Nat.pos_of_ne_zero fun h => hbot (Submodule.finrank_eq_zero.mp h)
    omega
  have := Fact.mk (CharP.char_is_prime K (ringChar K))
  have := (isPGroup_ker_redHom U hle).isNilpotent
  refine SimpleSectionsIn.of_isSolvable_ker (redHom U hle) inferInstance
    (SimpleSectionsIn.prod ?_ ?_)
  · exact SimpleSectionsIn.of_injective (Subgroup.subtype _) Subtype.val_injective (hlow _ hd₁)
  · exact SimpleSectionsIn.of_injective (Subgroup.subtype _) Subtype.val_injective (hlow _ hd₂)

private theorem fittingSubgroup_le_center_of_minimal
    (hiso : ∀ {S T : Type} [Group S] [Group T], (S ≃* T) → P T → P S)
    (hA5 : P (alternatingGroup (Fin 5))) (hA6 : P (alternatingGroup (Fin 6)))
    {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hι : Fintype.card ι ≤ 4) {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y)
    (hirr : IsIrreducibleOn Y) {S : Type} [Group S] [IsSimpleGroup S]
    (hS : ¬ IsMulCommutative S) {ψ : ↥Y →* S} (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype))
    (hP : ¬ P S) : CFSG.fittingSubgroup Y ≤ Subgroup.center Y := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  by_cases hp : p.1.1 = ringChar K
  · rw [eq_bot_of_normal_isPGroup_ringChar hirr CFSG.pCore_normal (hp ▸ CFSG.pCore_isPGroup)]
    exact bot_le
  · rcases le_center_or_alt_of_minimal hι hY hirr hS ψ hψ hmin
      (Nat.prime_of_mem_primeFactors p.1.2) hp CFSG.pCore_normal CFSG.pCore_isPGroup with
      h | h | h
    · exact h
    · exact (hP (hiso h.some hA5)).elim
    · exact (hP (hiso h.some hA6)).elim

private theorem exists_isComponent {G : Type*} [Group G] (hL : CFSG.layer G ≠ ⊥) :
    ∃ Q : Subgroup G, CFSG.IsComponent Q := by
  rw [CFSG.layer.eq_sSup] at hL
  by_contra h
  exact hL (sSup_eq_bot.mpr fun Q hQ => (h ⟨Q, hQ⟩).elim)

private theorem of_minimal
    (hiso : ∀ {S T : Type} [Group S] [Group T], (S ≃* T) → P T → P S)
    (hA5 : P (alternatingGroup (Fin 5))) (hA6 : P (alternatingGroup (Fin 6)))
    (hout : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], ¬ IsMulCommutative T → P T →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer T))
    {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (hι : Fintype.card ι ≤ 4) {X : Subgroup (GL ι K)}
    (hq : ∀ Y : Subgroup (GL ι K), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      P (↥Y ⧸ Subgroup.center ↥Y))
    {Y : Subgroup (GL ι K)} (hYX : Y ≤ X) (hirr : IsIrreducibleOn Y)
    (ih : ∀ H : Subgroup Y, H ≠ ⊤ → ∀ (T : Type) [Group T] [IsSimpleGroup T],
      ¬ IsMulCommutative T → ∀ φ : ↥H →* T, Function.Surjective φ → P T)
    {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S) {ψ : ↥Y →* S}
    (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → ¬ Function.Surjective (ψ.comp H.subtype)) : P S := by
  by_contra hP
  have := hψ.nontrivial
  have hY := isPerfect_of_minimal hS hψ hmin
  have hF := fittingSubgroup_le_center_of_minimal hiso hA5 hA6 hι hY hirr hS hψ hmin hP
  by_cases hL : CFSG.layer Y = ⊥
  · exact Group.IsPerfect.not_isSolvable Y
      (isSolvable_of_fittingSubgroup_le_center_of_layer_eq_bot hF hL)
  obtain ⟨Q, hQ⟩ := exists_isComponent hL
  have := normal_of_isComponent hι hY hQ
  rcases map_eq_bot_or_eq_top_of_normal hψ this with h | h
  · exact false_of_isComponent_of_map_eq_bot hout hψ hmin ih hQ h
  · exact hP (of_isComponent_of_map_eq_top hiso hq hYX hirr hS hψ hmin hQ h)

private theorem of_forall_ne_top
    (hiso : ∀ {S T : Type} [Group S] [Group T], (S ≃* T) → P T → P S)
    (hA5 : P (alternatingGroup (Fin 5))) (hA6 : P (alternatingGroup (Fin 6)))
    (hout : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], ¬ IsMulCommutative T → P T →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer T))
    {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 4) (hlow : ∀ d < Fintype.card ι, SimpleSectionsIn P (GL (Fin d) K))
    {X : Subgroup (GL ι K)}
    (hq : ∀ Y : Subgroup (GL ι K), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      P (↥Y ⧸ Subgroup.center ↥Y))
    {Y : Subgroup (GL ι K)} (hYX : Y ≤ X)
    (ih : ∀ H : Subgroup Y, H ≠ ⊤ → ∀ (T : Type) [Group T] [IsSimpleGroup T],
      ¬ IsMulCommutative T → ∀ φ : ↥H →* T, Function.Surjective φ → P T)
    {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S) (ψ : ↥Y →* S)
    (hψ : Function.Surjective ψ) : P S := by
  by_cases hmin : ∃ H : Subgroup Y, H ≠ ⊤ ∧ Function.Surjective (ψ.comp H.subtype)
  · obtain ⟨H, hH, hs⟩ := hmin
    exact ih H hH S hS _ hs
  push Not at hmin
  by_cases hirr : IsIrreducibleOn Y
  swap
  · exact simpleSectionsIn_of_not_isIrreducibleOn hlow hirr ⊤ S hS (ψ.comp (⊤ : Subgroup Y).subtype)
      ((surjective_comp_subtype_iff ψ ⊤).mpr
        (by rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ]))
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    have : Subsingleton (GL ι K) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
    exact (not_nontrivial (↥Y) hψ.nontrivial).elim
  | inr _ => exact of_minimal hiso hA5 hA6 hout hι hq hYX hirr ih hS hψ hmin

end Helpers

theorem simpleSectionsIn_of_core {P : (S : Type) → [Group S] → Prop}
    (hiso : ∀ {S T : Type} [Group S] [Group T], (S ≃* T) → P T → P S)
    (hA5 : P (alternatingGroup (Fin 5))) (hA6 : P (alternatingGroup (Fin 6)))
    (hout : ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], ¬ IsMulCommutative T → P T →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer T))
    {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 4) (hlow : ∀ d < Fintype.card ι, SimpleSectionsIn P (GL (Fin d) K))
    (X : Subgroup (GL ι K))
    (hq : ∀ Y : Subgroup (GL ι K), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      P (↥Y ⧸ Subgroup.center ↥Y)) :
    SimpleSectionsIn P X := by
  suffices h : ∀ n, ∀ Y : Subgroup (GL ι K), Y ≤ X → Nat.card Y = n →
      ∀ (S : Type) [Group S] [IsSimpleGroup S], ¬ IsMulCommutative S →
        ∀ ψ : ↥Y →* S, Function.Surjective ψ → P S by
    intro Y S _ _ hS ψ hψ
    let e := Y.equivMapOfInjective X.subtype X.subtype_injective
    exact h _ _ (Subgroup.map_subtype_le Y) rfl S hS (ψ.comp e.symm.toMonoidHom)
      (hψ.comp e.symm.surjective)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro Y hYX rfl S _ _ hS ψ hψ
  refine of_forall_ne_top hiso hA5 hA6 hout hι hlow hq hYX (fun H hH T _ _ hT φ hφ => ?_) hS ψ hψ
  have hc : Nat.card (H.map Y.subtype) < Nat.card Y := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, ← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
  let e := H.equivMapOfInjective Y.subtype Y.subtype_injective
  exact ih _ hc _ ((Subgroup.map_subtype_le H).trans hYX) rfl T hT (φ.comp e.symm.toMonoidHom)
    (hφ.comp e.symm.surjective)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
