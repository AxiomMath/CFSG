module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Hmod
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Recognition.HSMultiplier
  SemidirectProduct

section Cover


theorem HSCtx.of_doubleCover {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (hZ : Nat.card (center L) = 2) (hq : IsSporadic (L ⧸ center L) .HS) : HSCtx := by
  obtain ⟨e⟩ := nonempty_mulEquiv_cover_of_doubleCover_hs hperf hZ hq
  obtain ⟨e₀⟩ := hq
  refine ⟨?_, ?_, ?_⟩
  · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · rw [Nat.card_congr (centerCongr e).toEquiv]
    exact hZ
  · exact ⟨(QuotientGroup.congr (center HSCover) (center L) e
      (map_center_eq_of_mulEquiv e)).trans e₀⟩

end Cover

section Struct

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y : G}

theorem y_mem_normalizer (hF : FourHyp G L f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) :
    y ∈ normalizer (L : Set G) := by
  have : y ∈ centralizer ({f ^ 2} : Set G) := by
    rw [hN]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  rwa [hF.norm] at this

theorem H1_le_normalizer (hF : FourHyp G L f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) :
    L ⊔ zpowers y ≤ normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer (zpowers_le.2 (y_mem_normalizer hF hN))

theorem H1_cases (hF : FourHyp G L f) (hyy : y * y = 1)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) {x : G}
    (hx : x ∈ L ⊔ zpowers y) : x ∈ L ∨ ∃ a ∈ L, x = a * y :=
  mem_or_exists_of_mem_sup_zpowers hyy
    (fun a ha => (mem_normalizer_iff.1 (y_mem_normalizer hF hN) a).1 ha) hx

theorem comm_f_of_mem (hF : FourHyp G L f) {l : G} (hl : l ∈ L) : l * f = f * l :=
  mem_centralizer_iff.1 hF.mem_cent l hl

theorem H1_conj_f_of_mem (hF : FourHyp G L f) {l : G} (hl : l ∈ L) : l * f * l⁻¹ = f := by
  rw [comm_f_of_mem hF hl]
  group

theorem H1_conj_f_of_not_mem (hF : FourHyp G L f) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) {x : G}
    (hx : x ∈ L ⊔ zpowers y) (hxL : x ∉ L) : x * f * x⁻¹ = f⁻¹ := by
  rcases H1_cases hF hyy hN hx with h | ⟨a, ha, rfl⟩
  · exact absurd h hxL
  · have e : a * y * f * (a * y)⁻¹ = a * (y * f * y⁻¹) * a⁻¹ := by group
    rw [e, hyf]
    have : a * f⁻¹ * a⁻¹ = (a * f * a⁻¹)⁻¹ := by group
    rw [this, H1_conj_f_of_mem hF ha]

theorem f_not_mem_H1 (hF : FourHyp G L f) (hyy : y * y = 1)
    (hy : y ∉ L ⊔ zpowers f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) :
    f ∉ L ⊔ zpowers y := by
  intro hf
  rcases H1_cases hF hyy hN hf with h | ⟨a, ha, hfa⟩
  · rcases hF.eq_one_or_eq_sq_of_mem h hF.mem_cent with h1 | h1
    · have : f ^ 4 = 1 := hF.pow_four
      have h2 : f = 1 := h1
      rw [h2] at hF
      have := hF.order
      simp at this
    · have h4 : orderOf f ∣ 1 := by
        apply orderOf_dvd_of_pow_eq_one
        have : f ^ 1 = f ^ 2 := by simpa using h1
        have h3 : f ^ 2 = f ^ 1 := this.symm
        calc f ^ 1 = f ^ 2 * f⁻¹ := by group
          _ = f ^ 1 * f⁻¹ := by rw [h3]
          _ = 1 := by group
      rw [hF.order] at h4
      omega
  · apply hy
    have : y = a⁻¹ * f := by
      calc y = a⁻¹ * (a * y) := by group
        _ = a⁻¹ * f := by rw [← hfa]
    rw [this]
    exact mul_mem_sup (L.inv_mem ha) (mem_zpowers f)

theorem zpow_f_mem_H1 (hF : FourHyp G L f) (hyy : y * y = 1)
    (hy : y ∉ L ⊔ zpowers f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) {k : ℤ}
    (hk : f ^ k ∈ L ⊔ zpowers y) : f ^ k ∈ L := by
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have : f ^ (2 * m) = (f ^ 2) ^ m := by rw [zpow_mul]; norm_cast
    rw [this]
    exact zpow_mem (hF.sq_mem) m
  · exfalso
    apply f_not_mem_H1 hF hyy hy hN
    have h2 : (f ^ 2) ^ (-m) ∈ L ⊔ zpowers y :=
      Subgroup.mem_sup_left (zpow_mem hF.sq_mem (-m))
    have := mul_mem hk h2
    have e : f ^ (2 * m + 1) * (f ^ 2) ^ (-m) = f := by
      have h3 : (f ^ 2) ^ (-m) = f ^ (-(2 * m)) := by
        rw [show f ^ 2 = f ^ ((2 : ℕ) : ℤ) from (zpow_natCast f 2).symm, ← zpow_mul]
        congr 1
        push_cast
        ring
      rw [h3, ← zpow_add]
      convert zpow_one f using 2
      ring
    rwa [e] at this

end Struct

section Model

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y : G}

theorem y_not_mem_L (hy : y ∉ L ⊔ zpowers f) : y ∉ L := fun h => hy (Subgroup.mem_sup_left h)

theorem index_H1 (hF : FourHyp G L f) (hyy : y * y = 1) (hy : y ∉ L ⊔ zpowers f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) :
    (L.subgroupOf (L ⊔ zpowers y)).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨y, Subgroup.mem_sup_right (mem_zpowers y)⟩, fun b => ?_⟩
  have hyL := y_not_mem_L hy
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  rcases H1_cases hF hyy hN b.2 with hb | ⟨a, ha, hba⟩
  · right
    refine ⟨hb, fun h => hyL ?_⟩
    have := L.mul_mem (L.inv_mem hb) h
    simpa using this
  · left
    refine ⟨?_, ?_⟩
    · rw [hba]
      have : a * y * y = a := by rw [mul_assoc, hyy, mul_one]
      rw [this]
      exact ha
    · intro hbL
      apply hyL
      rw [hba] at hbL
      have := L.mul_mem (L.inv_mem ha) hbL
      simpa using this

theorem isHSCover_H1 (hF : FourHyp G L f) (hyy : y * y = 1) (hy : y ∉ L ⊔ zpowers f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y)
    (hq : IsSporadic (L ⧸ center L) .HS) :
    IsHSCover ↥(L ⊔ zpowers y) (L.subgroupOf (L ⊔ zpowers y)) := by
  have hLH : L ≤ L ⊔ zpowers y := le_sup_left
  have hEL : L.subgroupOf (L ⊔ zpowers y) ≃* L := subgroupOfEquivOfLe hLH
  have hidx := index_H1 hF hyy hy hN
  refine ⟨(normal_subgroupOf_iff_le_normalizer hLH).2 (H1_le_normalizer hF hN), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidx]
  · have : Group.IsPerfect L := Group.isPerfect_def.2 hF.std.standard.1.1
    exact Group.IsPerfect.ofSurjective (f := hEL.symm.toMonoidHom) hEL.symm.surjective
  · rw [Nat.card_congr (centerCongr hEL).toEquiv]
    exact hF.card_center
  · obtain ⟨e⟩ := hq
    exact ⟨(QuotientGroup.congr _ _ hEL (map_center_eq_of_mulEquiv hEL)).trans e⟩
  · intro x hx
    have hxL : (x : G) ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro l hl
      have := mem_centralizer_iff.1 hx ⟨l, hLH hl⟩ hl
      exact congrArg Subtype.val this
    rw [hF.cent] at hxL
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxL
    have hxH : (x : G) ∈ L ⊔ zpowers y := x.2
    rw [← hk] at hxH
    have := zpow_f_mem_H1 hF hyy hy hN hxH
    rw [Subgroup.mem_subgroupOf, ← hk]
    exact this

end Model

section Exists


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f y : G}

theorem exists_model (hHN : HNCentralizerFacts) (hF : FourHyp G L f) (hyy : y * y = 1)
    (hy : y ∉ L ⊔ zpowers f)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y)
    (hq : IsSporadic (L ⧸ center L) .HS) :
    ∃ (hΛ : HSCtx) (ι : L ≃* HSCover) (y₁ : G), y₁ ∈ L ⊔ zpowers y ∧ y₁ ∉ L ∧ y₁ * y₁ = 1 ∧
      ∀ x : L, y₁ * (x : G) * y₁⁻¹ = (ι.symm (hΛ.sigma (ι x)) : G) := by
  have hperf : Group.IsPerfect L := Group.isPerfect_def.2 hF.std.standard.1.1
  have hΛ : HSCtx := HSCtx.of_doubleCover hperf hF.card_center hq
  refine ⟨hΛ, ?_⟩
  have hLH : L ≤ L ⊔ zpowers y := le_sup_left
  have hyH : y ∈ L ⊔ zpowers y := Subgroup.mem_sup_right (mem_zpowers y)
  have hyL := y_not_mem_L hy
  have hH1 := isHSCover_H1 hF hyy hy hN hq
  have hi1 := index_H1 hF hyy hy hN
  have hv1 : (⟨y, hyH⟩ : ↥(L ⊔ zpowers y)) ∉ L.subgroupOf (L ⊔ zpowers y) := by
    rw [Subgroup.mem_subgroupOf]
    exact hyL
  have hv12 : (⟨y, hyH⟩ : ↥(L ⊔ zpowers y)) ^ 2 = 1 := by
    apply Subtype.ext
    simp [sq, hyy]
  have hv2 : hΛ.yMod ∉ hΛ.Emod := hΛ.yMod_not_mem
  have hv22 : hΛ.yMod ^ 2 = 1 := by rw [sq]; exact hΛ.yMod_mul_self
  obtain ⟨Ψ, hΨ⟩ := exists_mulEquiv_of_isHSCover hHN hH1 hΛ.isHSCover hi1 hΛ.Emod_index hv1 hv12
    hv2 hv22
  have hmemE : ∀ x : L, Ψ ⟨(x : G), hLH x.2⟩ ∈ hΛ.Emod := fun x =>
    (hΨ ⟨(x : G), hLH x.2⟩).1 (by rw [Subgroup.mem_subgroupOf]; exact x.2)
  let ψL : L →* hΛ.Hmod :=
    { toFun := fun x => Ψ ⟨(x : G), hLH x.2⟩
      map_one' := by
        have : (⟨((1 : L) : G), hLH (1 : L).2⟩ : ↥(L ⊔ zpowers y)) = 1 := rfl
        rw [this, map_one]
      map_mul' := fun a b => by
        have : (⟨((a * b : L) : G), hLH (a * b : L).2⟩ : ↥(L ⊔ zpowers y)) =
            ⟨(a : G), hLH a.2⟩ * ⟨(b : G), hLH b.2⟩ := rfl
        rw [this, map_mul] }
  let ιHom : L →* HSCover :=
    hΛ.eEmod.symm.toMonoidHom.comp (ψL.codRestrict hΛ.Emod hmemE)
  have hspec : ∀ x : L, (inl (ιHom x) : hΛ.Hmod) = Ψ ⟨(x : G), hLH x.2⟩ := by
    intro x
    have h3 := congrArg Subtype.val
      (hΛ.eEmod.apply_symm_apply (ψL.codRestrict hΛ.Emod hmemE x))
    have h2 : ((hΛ.eEmod (hΛ.eEmod.symm (ψL.codRestrict hΛ.Emod hmemE x)) : hΛ.Emod) :
        hΛ.Hmod) = inl (hΛ.eEmod.symm (ψL.codRestrict hΛ.Emod hmemE x)) := rfl
    rw [h2] at h3
    exact h3
  have hinj : Function.Injective ιHom := by
    intro a b hab
    have h1 := hspec a
    have h2 := hspec b
    rw [hab, h2] at h1
    have h3 := Ψ.injective h1.symm
    have h4 := congrArg Subtype.val h3
    exact Subtype.ext h4
  have hsurj : Function.Surjective ιHom := by
    intro z
    have hz : (inl z : hΛ.Hmod) ∈ hΛ.Emod := ⟨z, rfl⟩
    have hmem := (hΨ (Ψ.symm (inl z))).2 (by rw [MulEquiv.apply_symm_apply]; exact hz)
    rw [Subgroup.mem_subgroupOf] at hmem
    refine ⟨⟨((Ψ.symm (inl z) : ↥(L ⊔ zpowers y)) : G), hmem⟩, ?_⟩
    apply inl_injective (φ := hΛ.sigmaHom)
    rw [hspec]
    exact Ψ.apply_symm_apply (inl z)
  let ι : L ≃* HSCover := MulEquiv.ofBijective ιHom ⟨hinj, hsurj⟩
  have hι : ∀ x : L, (inl (ι x) : hΛ.Hmod) = Ψ ⟨(x : G), hLH x.2⟩ := hspec
  refine ⟨ι, ((Ψ.symm hΛ.yMod : ↥(L ⊔ zpowers y)) : G), (Ψ.symm hΛ.yMod).2, ?_, ?_, ?_⟩
  · intro hL
    have := (hΨ (Ψ.symm hΛ.yMod)).1 (by rw [Subgroup.mem_subgroupOf]; exact hL)
    rw [MulEquiv.apply_symm_apply] at this
    exact hv2 this
  · have h1 : Ψ.symm hΛ.yMod * Ψ.symm hΛ.yMod = 1 := by
      rw [← map_mul, hΛ.yMod_mul_self, map_one]
    have := congrArg Subtype.val h1
    simpa using this
  · intro x
    have hxH := hLH x.2
    set z : L := ι.symm (hΛ.sigma (ι x)) with hz
    have key : Ψ.symm hΛ.yMod * (⟨(x : G), hxH⟩ : ↥(L ⊔ zpowers y)) * (Ψ.symm hΛ.yMod)⁻¹ =
        ⟨(z : G), hLH z.2⟩ := by
      apply Ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hι x, hΛ.yMod_conj, ← hι z]
      simp [hz]
    have := congrArg Subtype.val key
    simpa using this

end Exists

end CFSG.EvenSporadicStandard.TwoHS
