module

public import CFSG.ClassicalInvolution.RouteD.TypeURecognition
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Standard

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

@[expose] def OddCoverSU3 (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p] :
    Prop :=
  ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* Su K p f 3),
    Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥

section Cover

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem oddCoverSU3 (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    OddCoverSU3 K p f := by
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 3
  exact CFSG.ClassicalInvolution.ModelFacts.OddCover.NoCover.of_mulEquiv
    (CFSG.LieType.Universal.Unitary.conjEquiv P hP)
    (CFSG.ClassicalInvolution.ModelFacts.OddCover.noCover_odd_su3 hp2 hK hq)

theorem exists_lift_of_oddCoverSU3 (hF : OddCoverSU3 K p f) [Group.IsPerfect (Su K p f 3)]
    {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hcen : π.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card π.ker)) (θ : Su K p f 3 →* X)
    (hθ : θ.range ≤ π.range) : ∃ θ' : Su K p f 3 →* Y, π.comp θ' = θ := by
  classical
  let P : Subgroup (Su K p f 3 × Y) :=
    (θ.comp (MonoidHom.fst _ _)).eqLocus (π.comp (MonoidHom.snd _ _))
  have hmemP : ∀ x : Su K p f 3 × Y, x ∈ P ↔ θ x.1 = π x.2 := fun x => Iff.rfl
  let pr : P →* Su K p f 3 := (MonoidHom.fst _ _).comp P.subtype
  have hpr : Function.Surjective pr := by
    intro s
    obtain ⟨y, hy⟩ := hθ ⟨s, rfl⟩
    exact ⟨⟨(s, y), (hmemP _).mpr hy.symm⟩, rfl⟩
  have hker : ∀ q : P, q ∈ pr.ker → π (q : Su K p f 3 × Y).2 = 1 := by
    intro q hq
    have h1 : (q : Su K p f 3 × Y).1 = 1 := hq
    have := (hmemP _).mp q.2
    rw [h1, map_one] at this
    exact this.symm
  have hcen' : pr.ker ≤ Subgroup.center P := by
    intro q hq
    rw [Subgroup.mem_center_iff]
    intro r
    have h1 : (q : Su K p f 3 × Y).1 = 1 := hq
    have h2 : (q : Su K p f 3 × Y).2 ∈ Subgroup.center Y :=
      hcen (MonoidHom.mem_ker.mpr (hker q hq))
    apply Subtype.ext
    apply Prod.ext
    · simp [h1]
    · exact (Subgroup.mem_center_iff.mp h2 _)
  have hodd' : Odd (Nat.card pr.ker) := by
    refine hodd.of_dvd_nat ?_
    let g : pr.ker →* π.ker :=
      { toFun := fun q => ⟨(q.1 : Su K p f 3 × Y).2, MonoidHom.mem_ker.mpr (hker q.1 q.2)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine Subgroup.card_dvd_of_injective g fun q₁ q₂ h => ?_
    have h1 : (q₁.1 : Su K p f 3 × Y).1 = 1 := q₁.2
    have h2 : (q₂.1 : Su K p f 3 × Y).1 = 1 := q₂.2
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
  let e : commutator P ≃* Su K p f 3 := MulEquiv.ofBijective _ ⟨hinj, hsurj'⟩
  refine ⟨(MonoidHom.snd _ _).comp (P.subtype.comp ((commutator P).subtype.comp
    e.symm.toMonoidHom)), ?_⟩
  ext s
  have h1 : pr ((e.symm s : commutator P) : P) = s := e.apply_symm_apply s
  have h2 := (hmemP _).mp ((e.symm s : commutator P) : P).2
  have h3 : ((e.symm s : commutator P) : P).1.1 = s := h1
  rw [h3] at h2
  exact h2.symm

theorem isPerfect_su_gen (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hn3 : 3 ≤ n) :
    Group.IsPerfect (Su K p f n) := by
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := n) hK hn3
    (Transfer.pair_ne_three_two_of_five_le hq)).1
  have h2 := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n)).symm h
  exact h2.1

theorem isPerfect_su_two (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    Group.IsPerfect (Su K p f 2) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two (K := K) (p := p) (f := f) hK
  refine CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 ?_ e.symm
  rw [CFSG.LieType.Steinberg.card_fixedSubfield hK]
  omega

theorem typeU_range_perfect_of_perfect {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (φ : A →* B) : φ.range ≤ ⁅φ.range, φ.range⁆ := by
  have h1 : ⁅(⊤ : Subgroup A), (⊤ : Subgroup A)⁆ = ⊤ := by
    rw [← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]

theorem B12_perfect_su (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    B12 K p f ≤ ⁅B12 K p f, B12 K p f⁆ := by
  have := isPerfect_su_two (K := K) (p := p) (f := f) hK hq
  have h : B12 K p f = (blockEmb K p f 3 2 0 (by omega)).range := by
    rw [B12, embSUid_two_eq_blockEmb]
  rw [h]
  exact typeU_range_perfect_of_perfect _

theorem B23_perfect_su (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) :
    B23 K p f ≤ ⁅B23 K p f, B23 K p f⁆ := by
  have := isPerfect_su_two (K := K) (p := p) (f := f) hK hq
  have h : B23 K p f = (blockEmb K p f 3 2 1 (by omega)).range := by
    rw [B23, embSUid_zero_eq_blockEmb]
  rw [h]
  exact typeU_range_perfect_of_perfect _

theorem typeU_standardPair_lift (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hF : OddCoverSU3 K p f) {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal]
    (hOc : O ≤ Subgroup.center Y) (hOodd : Odd (Nat.card O)) {A B : Subgroup Y}
    (hA : A ≤ ⁅A, A⁆) (hB : B ≤ ⁅B, B⁆) {W : Subgroup (Y ⧸ O)}
    (h : UnitaryBlockStandardPair K p f W (A.map (QuotientGroup.mk' O))
      (B.map (QuotientGroup.mk' O))) :
    ∃ W' : Subgroup Y, UnitaryBlockStandardPair K p f W' A B := by
  have hperf3 : Group.IsPerfect (Su K p f 3) := isPerfect_su_gen hK hq (by omega)
  have hq2 : p ^ f ≠ 2 := by omega
  let π := QuotientGroup.mk' O
  let Y' : Subgroup Y := A ⊔ B
  let π' : ↥Y' →* Y ⧸ O := π.comp Y'.subtype
  have hW : W ≤ A.map π ⊔ B.map π := (typeU_standardPair_eq_sup hK hq2 h).le
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
  obtain ⟨θ', hθ'⟩ := exists_lift_of_oddCoverSU3 hF π' hcen' hodd' θb hθ
  let θ : Su K p f 3 →* Y := Y'.subtype.comp θ'
  have hπθ : π.comp θ = θb := by
    ext s
    exact DFunLike.congr_fun hθ' s
  have hmapθ : ∀ X : Subgroup (Su K p f 3), (X.map θ).map π = X.map θb := by
    intro X
    rw [Subgroup.map_map, hπθ]
  have hperf : ∀ X : Subgroup (Su K p f 3), X ≤ ⁅X, X⁆ → X.map θ ≤ ⁅X.map θ, X.map θ⁆ := by
    intro X hX
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hX
  have hB12 : ((B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom) ≤
      ⁅(B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom,
        (B12 K p f).map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (B12_perfect_su hK hq)
  have hB23 : ((B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom) ≤
      ⁅(B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom,
        (B23 K p f).map (MulAut.conj c⁻¹).toMonoidHom⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (B23_perfect_su hK hq)
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

end Cover

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem typeU_perfect_subgroupOf {H : Type*} [Group H] {Y A : Subgroup H} (hA : A ≤ Y)
    (hAp : A ≤ ⁅A, A⁆) : A.subgroupOf Y ≤ ⁅A.subgroupOf Y, A.subgroupOf Y⁆ := by
  apply (Subgroup.map_le_map_iff_of_injective Y.subtype_injective).mp
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA]
  exact hAp

theorem unitaryBlockStandardPair_of_locImg_perfect [Finite G] (hq : 5 ≤ p ^ f)
    (hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2)
    (hF : OddCoverSU3 (GaloisField p (2 * f)) p f) {x : G} (hP1 : LocalOddCentral Ω {x})
    {A B : Subgroup G} (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) (hAp : A ≤ ⁅A, A⁆)
    (hBp : B ≤ ⁅B, B⁆) {W : Subgroup (locQuot Ω x)}
    (h : UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W (locImg Ω x A) (locImg Ω x B)) :
    ∃ W' : Subgroup G, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W' A B := by
  obtain ⟨W', hW'⟩ := typeU_standardPair_lift hK hq hF
    (O := classicalInvolutionOddCore ↥(locLayer Ω x)) hP1
    (CFSG.ComponentClassification.OddCore.odd_card _) (typeU_perfect_subgroupOf hA hAp)
    (typeU_perfect_subgroupOf hB hBp) h
  have := unitaryBlockStandardPair_map hW' (locLayer Ω x).subtype
    (locLayer Ω x).subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hA,
    inf_eq_left.mpr hB] at this
  exact ⟨_, this⟩

end Local

end CFSG.ClassicalInvolution.RouteD
