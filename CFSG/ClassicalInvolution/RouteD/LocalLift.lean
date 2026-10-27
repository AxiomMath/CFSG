module

public import CFSG.ClassicalInvolution.RouteD.LocalPair
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement


@[expose] def OddCoverSL3 (F : Type) [Field F] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* SL(3, F)),
    Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥

section Cover

variable {R H : Type} [Group R] [Group H] (ρ : R →* H)

theorem surjective_comp_commutator' [Group.IsPerfect H] (hρ : Function.Surjective ρ) :
    Function.Surjective (ρ.comp (commutator R).subtype) := by
  have h : (commutator R).map ρ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ρ hρ,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  intro x
  have hx : x ∈ (commutator R).map ρ := by rw [h]; trivial
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩

theorem isPerfect_commutator' [Group.IsPerfect H] (hρ : Function.Surjective ρ)
    (hcen : ρ.ker ≤ Subgroup.center R) : Group.IsPerfect (commutator R) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
  have hdec : ∀ r : R, ∃ y ∈ commutator R, ∃ n ∈ Subgroup.center R, r = y * n := by
    intro r
    obtain ⟨y, hy⟩ := surjective_comp_commutator' ρ hρ (ρ r)
    refine ⟨y, y.2, (y : R)⁻¹ * r, hcen ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (ρ (y : R))⁻¹ * ρ r = 1
    rw [show ρ (y : R) = ρ r from hy, inv_mul_cancel]
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  obtain ⟨y₁, hy₁, n₁, hn₁, rfl⟩ := hdec g₁
  obtain ⟨y₂, hy₂, n₂, hn₂, rfl⟩ := hdec g₂
  have hzc : ∀ n ∈ Subgroup.center R, ∀ h ∈ (⊤ : Subgroup R), n * h = h * n := fun n hn h _ =>
    (Subgroup.mem_center_iff.mp hn h).symm
  rw [commutator_mul_of_central (H := ⊤) trivial trivial trivial (hzc _ hn₁) (hzc _ hn₂)]
  exact Subgroup.commutator_mem_commutator hy₁ hy₂

end Cover

theorem exists_lift_of_oddCoverSL3 {F : Type} [Field F] [Finite F] (hF : OddCoverSL3 F)
    [Group.IsPerfect SL(3, F)] {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hcen : π.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card π.ker)) (θ : SL(3, F) →* X)
    (hθ : θ.range ≤ π.range) : ∃ θ' : SL(3, F) →* Y, π.comp θ' = θ := by
  classical
  let P : Subgroup (SL(3, F) × Y) :=
    (θ.comp (MonoidHom.fst _ _)).eqLocus (π.comp (MonoidHom.snd _ _))
  have hmemP : ∀ x : SL(3, F) × Y, x ∈ P ↔ θ x.1 = π x.2 := fun x => Iff.rfl
  let pr : P →* SL(3, F) := (MonoidHom.fst _ _).comp P.subtype
  have hpr : Function.Surjective pr := by
    intro s
    obtain ⟨y, hy⟩ := hθ ⟨s, rfl⟩
    exact ⟨⟨(s, y), (hmemP _).mpr hy.symm⟩, rfl⟩
  have hker : ∀ q : P, q ∈ pr.ker → π (q : SL(3, F) × Y).2 = 1 := by
    intro q hq
    have h1 : (q : SL(3, F) × Y).1 = 1 := hq
    have := (hmemP _).mp q.2
    rw [h1, map_one] at this
    exact this.symm
  have hcen' : pr.ker ≤ Subgroup.center P := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    have h1 : (q : SL(3, F) × Y).1 = 1 := hq
    have h2 : (q : SL(3, F) × Y).2 ∈ Subgroup.center Y :=
      hcen (MonoidHom.mem_ker.mpr (hker q hq))
    apply Subtype.ext
    apply Prod.ext
    · simp [h1]
    · exact (Subgroup.mem_center_iff.mp h2 _)
  have hodd' : Odd (Nat.card pr.ker) := by
    refine hodd.of_dvd_nat ?_
    let g : pr.ker →* π.ker :=
      { toFun := fun q => ⟨(q.1 : SL(3, F) × Y).2, MonoidHom.mem_ker.mpr (hker q.1 q.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective g fun q₁ q₂ h => ?_
    have h1 : (q₁.1 : SL(3, F) × Y).1 = 1 := q₁.2
    have h2 : (q₂.1 : SL(3, F) × Y).1 = 1 := q₂.2
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (h1.trans h2.symm) (congrArg Subtype.val h)
  have hsurj' := surjective_comp_commutator' pr hpr
  have hperf : Group.IsPerfect (commutator P) := isPerfect_commutator' pr hpr hcen'
  have hcen'' : (pr.comp (commutator P).subtype).ker ≤ Subgroup.center (commutator P) := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hcen' hq) (r : P))
  have hodd'' : Odd (Nat.card (pr.comp (commutator P).subtype).ker) := by
    refine hodd'.of_dvd_nat ?_
    let g : (pr.comp (commutator P).subtype).ker →* pr.ker :=
      { toFun := fun q => ⟨(q.1 : P), q.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun q₁ q₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : pr.ker => (x : P)) h))
  have hbot := hF ↥(commutator P) (pr.comp (commutator P).subtype) hsurj' hcen'' hodd''
  have hinj : Function.Injective (pr.comp (commutator P).subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hbot
  let e : commutator P ≃* SL(3, F) := MulEquiv.ofBijective _ ⟨hinj, hsurj'⟩
  refine ⟨(MonoidHom.snd _ _).comp (P.subtype.comp ((commutator P).subtype.comp
    e.symm.toMonoidHom)), ?_⟩
  ext s
  have h1 : pr ((e.symm s : commutator P) : P) = s := e.apply_symm_apply s
  have h2 := (hmemP _).mp ((e.symm s : commutator P) : P).2
  have h3 : ((e.symm s : commutator P) : P).1.1 = s := h1
  rw [h3] at h2
  exact h2.symm



section StandardPair

variable {F : Type} [Field F]

theorem commutator_B12_eq [Finite F] (h4 : 4 ≤ Nat.card F) : ⁅B12 F, B12 F⁆ = B12 F := by
  let e : SL(2, F) ≃* B12 F := MonoidHom.ofInjective (blockSL_injective (K := F) (m := 3)
    (k := 2) (i := 0) (by omega))
  exact Subgroup.isPerfect_iff.mp (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e.symm)

theorem commutator_B23_eq [Finite F] (h4 : 4 ≤ Nat.card F) : ⁅B23 F, B23 F⁆ = B23 F := by
  let e : SL(2, F) ≃* B23 F := MonoidHom.ofInjective (blockSL_injective (K := F) (m := 3)
    (k := 2) (i := 1) (by omega))
  exact Subgroup.isPerfect_iff.mp (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 e.symm)

theorem linearBlockStandardPair_le_sup' {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) : W ≤ U ⊔ V := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  have hB : (B12 F).map (MulAut.conj c⁻¹).toMonoidHom ⊔ (B23 F).map (MulAut.conj c⁻¹).toMonoidHom =
      ⊤ := by
    rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.Models.B12_sup_B23]
    exact Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)
  have hW : W = ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ ⊔
      ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom).map θ := by
    rw [← hrange, MonoidHom.range_eq_map, ← hB, Subgroup.map_sup]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hW, h1, h2]
  · rw [hW, h1, h2, sup_comm]

theorem linearBlockStandardPair_lift [Finite F] (h4 : 4 ≤ Nat.card F) (hF : OddCoverSL3 F)
    {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] (hOc : O ≤ Subgroup.center Y)
    (hOodd : Odd (Nat.card O)) {A B : Subgroup Y} (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆)
    {W : Subgroup (Y ⧸ O)}
    (h : LinearBlockStandardPair F W (A.map (QuotientGroup.mk' O)) (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, LinearBlockStandardPair F W' A B := by
  have : Group.IsPerfect SL(3, F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  let π := QuotientGroup.mk' O
  let Y' : Subgroup Y := A ⊔ B
  let π' : ↥Y' →* Y ⧸ O := π.comp Y'.subtype
  have hW : W ≤ A.map π ⊔ B.map π := linearBlockStandardPair_le_sup' h
  obtain ⟨θb, c, hrange, hker, hcases⟩ := h
  have hθ : θb.range ≤ π'.range := by
    rw [hrange]
    refine hW.trans (sup_le ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, rfl⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨⟨b, Subgroup.mem_sup_right hb⟩, rfl⟩
  have hcen' : π'.ker ≤ Subgroup.center ↥Y' := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro r
    have : (y : Y) ∈ O := by
      have := MonoidHom.mem_ker.mp hy
      exact (QuotientGroup.eq_one_iff _).mp this
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hOc this) (r : Y))
  have hodd' : Odd (Nat.card π'.ker) := by
    refine hOodd.of_dvd_nat ?_
    let g : π'.ker →* O :=
      { toFun := fun y => ⟨(y.1 : Y), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp y.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Subgroup.card_dvd_of_injective g fun y₁ y₂ h =>
      Subtype.ext (Subtype.ext (congrArg (fun x : O => (x : Y)) h))
  obtain ⟨θ', hθ'⟩ := exists_lift_of_oddCoverSL3 hF π' hcen' hodd' θb hθ
  let θ : SL(3, F) →* Y := Y'.subtype.comp θ'
  have hπθ : π.comp θ = θb := by
    ext s
    exact DFunLike.congr_fun hθ' s
  have hmapθ : ∀ X : Subgroup SL(3, F), (X.map θ).map π = X.map θb := by
    intro X
    rw [Subgroup.map_map, hπθ]
  have hperf : ∀ X : Subgroup SL(3, F), X ≤ ⁅X, X⁆ → X.map θ ≤ ⁅X.map θ, X.map θ⁆ := by
    intro X hX
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hX
  have hB12 : ((B12 F).map (MulAut.conj c⁻¹).toMonoidHom) ≤
      ⁅(B12 F).map (MulAut.conj c⁻¹).toMonoidHom, (B12 F).map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator, commutator_B12_eq h4]
  have hB23 : ((B23 F).map (MulAut.conj c⁻¹).toMonoidHom) ≤
      ⁅(B23 F).map (MulAut.conj c⁻¹).toMonoidHom, (B23 F).map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator, commutator_B23_eq h4]
  refine ⟨θ.range, θ, c, rfl, ?_, ?_⟩
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker, ← hπθ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨eq_of_map_mk_eq_of_central hOc (hperf _ hB12) hA ?_,
        eq_of_map_mk_eq_of_central hOc (hperf _ hB23) hB ?_⟩
      · exact (hmapθ _).trans h1
      · exact (hmapθ _).trans h2
    · right
      refine ⟨eq_of_map_mk_eq_of_central hOc (hperf _ hB12) hB ?_,
        eq_of_map_mk_eq_of_central hOc (hperf _ hB23) hA ?_⟩
      · exact (hmapθ _).trans h1
      · exact (hmapθ _).trans h2

end StandardPair

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem linearBlockStandardPair_of_locImg [Finite G] (h4 : 4 ≤ p ^ f)
    (hF : OddCoverSL3 (GaloisField p f)) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {W : Subgroup (locQuot Ω x)}
    (h : LinearBlockStandardPair (GaloisField p f) W (locImg Ω x L) (locImg Ω x L')) :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' L L' := by
  have hf : f ≠ 0 := by rintro rfl; simp at h4
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hperf : ∀ M ∈ centralizingMembers Ω {x},
      M.subgroupOf (locLayer Ω x) ≤ ⁅M.subgroupOf (locLayer Ω x), M.subgroupOf (locLayer Ω x)⁆ := by
    intro M hM
    obtain ⟨z, hz⟩ := hΩ.classical M hM.1
    exact (commutator_eq_of_isClassicalMember (hz.subgroupOf p f (le_centralizingLayer hM))).ge
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_lift (F := GaloisField p f) (hcard ▸ h4) hF
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) (hperf L hL) (hperf L' hL') h
  have := linearBlockStandardPair_map hW' (locLayer Ω x).subtype (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (le_centralizingLayer hL), inf_eq_left.mpr (le_centralizingLayer hL')] at this
  exact ⟨_, this⟩

end Local

end CFSG.ClassicalInvolution.RouteD
