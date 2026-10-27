module

public import CFSG.GH74.Uniqueness.Section12Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvolutionInner

public section

namespace CFSG.GH74.Uniqueness.Cor166

open Subgroup

@[expose] noncomputable def quotCenterAut (G : Type*) [Group G] :
    MulAut G →* MulAut (G ⧸ center G) where
  toFun σ := QuotientGroup.congr (center G) (center G) σ
    (Subgroup.characteristic_iff_map_eq.mp inferInstance σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem quotCenterAut_mk {G : Type*} [Group G] (σ : MulAut G) (x : G) :
    quotCenterAut G σ (x : G ⧸ center G) = ((σ x : G) : G ⧸ center G) := rfl

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem eq_of_mk_eq_of_sq (hodd : Odd (Nat.card (center G))) {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : (a : G ⧸ center G) = (b : G ⧸ center G)) : a = b := by
  have hz : a⁻¹ * b ∈ center G := QuotientGroup.eq.mp hab
  set ζ := a⁻¹ * b with hζ
  have hbζ : b = a * ζ := by rw [hζ]; group
  have hcomm : a * ζ = ζ * a := Subgroup.mem_center_iff.mp hz a
  have hζ2 : ζ * ζ = 1 := by
    have : b * b = (a * a) * (ζ * ζ) := by
      rw [hbζ]
      calc a * ζ * (a * ζ) = a * (ζ * a) * ζ := by group
        _ = a * (a * ζ) * ζ := by rw [hcomm]
        _ = (a * a) * (ζ * ζ) := by group
    rwa [hb, ha, one_mul, eq_comm] at this
  have hord : orderOf (⟨ζ, hz⟩ : center G) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simp [sq, hζ2]
  have hord2 : orderOf (⟨ζ, hz⟩ : center G) ∣ Nat.card (center G) := orderOf_dvd_natCard _
  have h1 : orderOf (⟨ζ, hz⟩ : center G) = 1 := by
    have hcop : Nat.Coprime 2 (Nat.card (center G)) := (Nat.coprime_two_left).mpr hodd
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord hcop) hord2
  have hζ1 : ζ = 1 := by
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  rw [hbζ, hζ1, mul_one]

omit [Finite G] in
theorem exists_sq_eq_one_lift (hodd : Odd (Nat.card (center G))) {y : G ⧸ center G}
    (hy : y * y = 1) : ∃ x : G, (x : G ⧸ center G) = y ∧ x * x = 1 := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hx2 : x₀ * x₀ ∈ center G := by
    have : ((x₀ * x₀ : G) : G ⧸ center G) = 1 := by
      rw [QuotientGroup.mk_mul]
      exact hy
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨k, hk⟩ := hodd
  refine ⟨x₀ ^ Nat.card (center G), ?_, ?_⟩
  · rw [QuotientGroup.mk_pow, hk, pow_succ, pow_mul, sq]
    have : ((x₀ : G ⧸ center G) * (x₀ : G ⧸ center G)) = 1 := hy
    rw [this, one_pow, one_mul]
  · have hc : (⟨x₀ * x₀, hx2⟩ : center G) ^ Nat.card (center G) = 1 := pow_card_eq_one'
    have hc' : (x₀ * x₀) ^ Nat.card (center G) = 1 := congrArg Subtype.val hc
    rw [← pow_two, ← pow_mul, mul_comm, pow_mul, pow_two]
    exact hc'

omit [Finite G] in
theorem exists_conj_of_isConj_mk (hodd : Odd (Nat.card (center G))) {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : IsConj (a : G ⧸ center G) (b : G ⧸ center G)) :
    ∃ c : G, c * a * c⁻¹ = b := by
  obtain ⟨c', hc⟩ := isConj_iff.mp hab
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c'
  refine ⟨c, eq_of_mk_eq_of_sq hodd ?_ hb ?_⟩
  · calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
      _ = 1 := by rw [ha]; group
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hc

end Generic

section Induced

variable {X : Type} [Group X]

@[expose] noncomputable def benderAut (F : Subgroup X) :
    ↥(normalizer (F : Set X)) →* MulAut (↥F ⧸ center ↥F) :=
  (quotCenterAut ↥F).comp F.normalizerMonoidHom

theorem benderAut_mk (F : Subgroup X) (g : ↥(normalizer (F : Set X))) (x y : ↥F)
    (hy : (y : X) = (g : X) * x * (g : X)⁻¹) :
    benderAut F g (x : ↥F ⧸ center ↥F) = (y : ↥F ⧸ center ↥F) := by
  have h : F.normalizerMonoidHom g x = y := Subtype.ext (by
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hy])
  change quotCenterAut ↥F (F.normalizerMonoidHom g) (x : ↥F ⧸ center ↥F) = _
  rw [quotCenterAut_mk, h]

theorem benderAut_of_mem (F : Subgroup X) (y : ↥F) :
    benderAut F ⟨y, Subgroup.le_normalizer y.2⟩ = MulAut.conj (y : ↥F ⧸ center ↥F) := by
  ext k
  induction k using QuotientGroup.induction_on with
  | H x =>
    rw [benderAut_mk F _ x (y * x * y⁻¹) (by simp), MulAut.conj_apply]
    rfl

variable [Finite X]

omit [Finite X] in
theorem mem_centralizer_of_benderAut_eq_one {F : Subgroup X} {S : Set X} (hFS : closure S = F)
    (hS : ∀ s ∈ S, s * s = 1) (hodd : Odd (Nat.card (center ↥F)))
    {g : ↥(normalizer (F : Set X))} (hg : benderAut F g = 1) :
    (g : X) ∈ centralizer (F : Set X) := by
  have hgen : ∀ s ∈ S, (g : X) * s = s * (g : X) := by
    intro s hs
    have hsF : s ∈ F := hFS ▸ subset_closure hs
    have hgs : (g : X) * s * (g : X)⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp g.2 s).mp hsF
    have h1 := benderAut_mk F g ⟨s, hsF⟩ ⟨_, hgs⟩ rfl
    rw [hg, MulAut.one_apply] at h1
    have h2 : (⟨(g : X) * s * (g : X)⁻¹, hgs⟩ : ↥F) = ⟨s, hsF⟩ := by
      refine eq_of_mk_eq_of_sq hodd ?_ ?_ h1.symm
      · apply Subtype.ext
        change (g : X) * s * (g : X)⁻¹ * ((g : X) * s * (g : X)⁻¹) = 1
        calc (g : X) * s * (g : X)⁻¹ * ((g : X) * s * (g : X)⁻¹) =
              (g : X) * (s * s) * (g : X)⁻¹ := by group
          _ = 1 := by rw [hS s hs]; group
      · exact Subtype.ext (hS s hs)
    have h3 : (g : X) * s * (g : X)⁻¹ = s := congrArg Subtype.val h2
    calc (g : X) * s = (g : X) * s * (g : X)⁻¹ * (g : X) := by group
      _ = s * (g : X) := by rw [h3]
  have hle : closure S ≤ centralizer ({(g : X)} : Set X) := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (hgen s hs).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ closure S := by rw [hFS]; exact hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx')

omit [Finite X] in
theorem mem_centralizer_of_benderAut_eq_conj {F : Subgroup X} {S : Set X} (hFS : closure S = F)
    (hS : ∀ s ∈ S, s * s = 1) (hodd : Odd (Nat.card (center ↥F)))
    {g : ↥(normalizer (F : Set X))} {y : ↥F}
    (hg : benderAut F g = MulAut.conj (y : ↥F ⧸ center ↥F)) :
    (y : X)⁻¹ * g ∈ centralizer (F : Set X) := by
  have h := mem_centralizer_of_benderAut_eq_one hFS hS hodd
    (g := (⟨y, Subgroup.le_normalizer y.2⟩ : ↥(normalizer (F : Set X)))⁻¹ * g) (by
      rw [map_mul, map_inv, hg, benderAut_of_mem, inv_mul_cancel])
  simpa using h

theorem exists_fixed_lift {F : Subgroup X} (hodd : Odd (Nat.card (center ↥F)))
    {g : ↥(normalizer (F : Set X))} (hg2 : (g : X) * g = 1) {x : ↥F}
    (hx : benderAut F g (x : ↥F ⧸ center ↥F) = x) :
    ∃ x' : ↥F, (x' : ↥F ⧸ center ↥F) = x ∧ (g : X) * x' = x' * g := by
  classical
  have hconj : ∀ y : ↥F, (g : X) * y * (g : X)⁻¹ ∈ F := fun y =>
    (Subgroup.mem_normalizer_iff.mp g.2 y).mp y.2
  let A := {y : ↥F // (y : ↥F ⧸ center ↥F) = x}
  let f : A → A := fun y => ⟨⟨(g : X) * y.1 * (g : X)⁻¹, hconj y.1⟩, by
    rw [← benderAut_mk F g y.1 _ rfl, y.2, hx]⟩
  have hgi : (g : X)⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hf : Function.Involutive f := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change (g : X) * ((g : X) * (y.1 : X) * (g : X)⁻¹) * (g : X)⁻¹ = y.1
    rw [hgi]
    calc (g : X) * ((g : X) * (y.1 : X) * (g : X)) * (g : X) =
          ((g : X) * g) * y.1 * ((g : X) * g) := by group
      _ = y.1 := by rw [hg2]; group
  have hcard : Nat.card A = Nat.card (center ↥F) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, QuotientGroup.eq.mp y.2.symm⟩
        invFun := fun c => ⟨x * c, by
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (c : ↥F)).mpr c.2, mul_one]⟩
        left_inv := fun y => by
          apply Subtype.ext
          change x * (x⁻¹ * y.1) = y.1
          group
        right_inv := fun c => by
          apply Subtype.ext
          change x⁻¹ * (x * c) = c
          group }
  have : Fintype A := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ 2 ∣ Fintype.card A := by
    rw [Fintype.card_eq_nat_card, hcard]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun y => hf y
  obtain ⟨y, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime hndvd hσ
  refine ⟨y.1, y.2, ?_⟩
  have h1 : (g : X) * y.1 * (g : X)⁻¹ = y.1 := congrArg (fun w : A => ((w.1 : ↥F) : X)) hy
  calc (g : X) * y.1 = (g : X) * y.1 * (g : X)⁻¹ * g := by group
    _ = y.1 * g := by rw [h1]

end Induced

section BenderSub

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M F : Subgroup X} {n i e : ℕ}

theorem benderSub_odd_card_center (hB : BenderSub Z M F n i e) : Odd (Nat.card (center ↥F)) := by
  have h := odd_card_pPrimeCoreIn F
  rw [hB.core, Subgroup.card_map_of_injective F.subtype_injective] at h
  exact h

omit [Finite X] in
theorem benderSub_closure_eq (hB : BenderSub Z M F n i e) : closure (Z ∩ (F : Set X)) = F :=
  hB.zhull

omit [Finite X] in
theorem benderSub_isBenderGroup (hB : BenderSub Z M F n i e) :
    CFSG.BenderSuzuki.IsBenderGroup (↥F ⧸ center ↥F) :=
  Bender.isBenderGroup_iff_exists_benderType.mpr ⟨n, i, e, hB.bender⟩

theorem benderSub_mem_centralizer_of_eq_conj (hZ : IsInvariantInvolutionSet Z)
    (hB : BenderSub Z M F n i e) {g : ↥(normalizer (F : Set X))} {y : ↥F}
    (hg : benderAut F g = MulAut.conj (y : ↥F ⧸ center ↥F)) :
    (y : X)⁻¹ * g ∈ centralizer (F : Set X) :=
  mem_centralizer_of_benderAut_eq_conj (benderSub_closure_eq hB)
    (fun _ hs => hZ.mul_self_eq_one hs.1) (benderSub_odd_card_center hB) hg

theorem benderSub_mem_centralizer_of_eq_one (hZ : IsInvariantInvolutionSet Z)
    (hB : BenderSub Z M F n i e) {g : ↥(normalizer (F : Set X))} (hg : benderAut F g = 1) :
    (g : X) ∈ centralizer (F : Set X) :=
  mem_centralizer_of_benderAut_eq_one (benderSub_closure_eq hB)
    (fun _ hs => hZ.mul_self_eq_one hs.1) (benderSub_odd_card_center hB) hg

theorem benderSub_exists_inner_of_fixed_le
    (hZ : IsInvariantInvolutionSet Z)
    (hB : BenderSub Z M F n i e) {g : ↥(normalizer (F : Set X))} (hg2 : (g : X) * g = 1)
    (hfix : ∀ x : ↥F, (g : X) * x = x * g → (x : X) ∈ M) :
    ∃ y : ↥F, (y : X)⁻¹ * g ∈ centralizer (F : Set X) := by
  have hodd := benderSub_odd_card_center hB
  set σ := benderAut F g with hσdef
  have hσ2 : σ * σ = 1 := by
    have h1 : g * g = 1 := Subtype.ext hg2
    rw [hσdef, ← map_mul, h1, map_one]
  obtain ⟨T, hT⟩ := hB.borel
  have hfixT : ∀ k : ↥F ⧸ center ↥F, σ k = k →
      k ∈ normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨x', hx', hgx'⟩ := exists_fixed_lift hodd hg2 hk
    have hx'M : (x' : X) ∈ M := hfix x' hgx'
    rw [← hT, ← hx']
    exact ⟨x', Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hx'M, x'.2⟩), rfl⟩
  obtain ⟨y', hy'⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.bender_involution_automorphism_inner
      (↥F ⧸ center ↥F) (CFSG.Open.fusionIsBenderGroup_of_isBenderGroup (benderSub_isBenderGroup hB))
      σ hσ2 ⟨T, hfixT⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y'
  exact ⟨y, benderSub_mem_centralizer_of_eq_conj hZ hB hy'⟩

end BenderSub

end CFSG.GH74.Uniqueness.Cor166
