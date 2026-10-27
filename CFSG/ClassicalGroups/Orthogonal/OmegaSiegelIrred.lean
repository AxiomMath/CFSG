module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelPointMeet
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelAbelianStab
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelAxis
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelCost
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeRootSub
public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeStab
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.ClassicalGroups.Orthogonal.SiegelSLBasic
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1
open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

local notation "𝒲[" a "]" => ⨆ (w : N) (_ : polar QN a w = 0), movedSpace (rhoE ρ a w)

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem exists_apply_eq_of_frame (hnd : (polarBilin QN).Nondegenerate)
    {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v) {a : N} (ha : QN a = 0)
    (ha0 : a ≠ 0) : ∃ g : ↥(elementaryGroup QN), (g : N ≃ₗ[K'] N) e = a := by
  let P₁ : HypPair QN := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  let P₂ : HypPair QN := ⟨p, p', hF.p_sing, hF.p'_sing, hF.pp'⟩
  obtain ⟨g, hg, hge⟩ := exists_mem_elementaryGroup_apply_eq hnd (P := P₁) (P' := P₂)
    ⟨hF.ep, hF.ep', hF.fp, hF.fp'⟩ P₁.e_ne_zero ha0 (hF.e_sing.trans ha.symm)
  exact ⟨⟨g, hg⟩, hge⟩

private theorem not_le_axis (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {U : Submodule K V} (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (hU0 : U ≠ ⊥) : ¬ U ≤ 𝒲[e] := by
  intro hle
  have hf0 : f ≠ 0 := by
    rintro rfl
    have := hF.ef
    rw [polar_zero_right] at this
    exact zero_ne_one this
  obtain ⟨g, hg⟩ := exists_apply_eq_of_frame hs.ndN hF hF.f_sing hf0
  have hmap := OmegaSetting.map_iSup_movedSpace_rhoE (ρ := ρ) g e
  rw [hg] at hmap
  have hUf : U ≤ 𝒲[f] := by
    intro x hx
    have h1 : (ρ g⁻¹) x ∈ U := hU _ _ hx
    have h2 : ρ g ((ρ g⁻¹) x) ∈ (𝒲[e]).map (ρ g : V →ₗ[K] V) :=
      Submodule.mem_map_of_mem (hle h1)
    rw [hmap] at h2
    simpa [← LinearEquiv.mul_apply, ← map_mul] using h2
  have hbot := OmegaSetting.iSup_inf_iSup_eq_bot hs htop hfix hK hF h8 hF.e_sing hF.f_sing
    (by rw [hF.ef]; exact one_ne_zero)
  exact hU0 (eq_bot_iff.mpr (hbot ▸ le_inf hle hUf))

private def perpAdd (QN : QuadraticForm K' N) (e f : N) : AddSubgroup N where
  carrier := {x | polar QN e x = 0 ∧ polar QN f x = 0}
  add_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨by rw [polar_add_right, h1, h1', add_zero], by rw [polar_add_right, h2, h2', add_zero]⟩
  zero_mem' := ⟨polar_zero_right QN e, polar_zero_right QN f⟩
  neg_mem' := by
    rintro a ⟨h1, h2⟩
    exact ⟨by rw [polar_neg_right, h1, neg_zero], by rw [polar_neg_right, h2, neg_zero]⟩

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] in
private theorem mem_perpAdd {e f x : N} :
    x ∈ perpAdd QN e f ↔ polar QN e x = 0 ∧ polar QN f x = 0 := Iff.rfl

omit [CharP K' 2] in
private theorem natCard_pow_four_le_perpAdd {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) : Nat.card K' ^ 4 ≤ Nat.card ↥(perpAdd QN e f) := by
  have : Finite N := Module.finite_of_finite K'
  have hfe : polar QN f e = 1 := by rw [polar_comm]; exact hF.ef
  let F : ↥(perpAdd QN e f) → ↥(rootGroup QN e) := fun x =>
    ⟨eichler QN e x, eichler_mem_rootGroup (mem_perpAdd.mp x.2).1⟩
  have hF' : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨y, hy, rfl⟩ := mem_rootGroup.mp hg
    refine ⟨⟨y + (-polar QN y f) • e, mem_perpAdd.mpr ⟨?_, ?_⟩⟩,
      Subtype.ext (eichler_add_smul_self hF.e_sing y _)⟩
    · rw [polar_add_right, hy, polar_smul_right_eq, polar_self_eq_zero hF.e_sing]
      simp
    · rw [polar_add_right, polar_smul_right_eq, hfe, polar_comm QN f y]
      ring
  rw [← hF.natCard_rootGroup]
  exact Nat.card_le_card_of_surjective F hF'

private theorem exists_addMonoidHom (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) (u₀ : V) :
    ∃ φ : ↥(perpAdd QN e f) →+ V, ∀ x : ↥(perpAdd QN e f), φ x = rhoE ρ e x u₀ - u₀ := by
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.ef
    rw [polar_zero_left] at this
    exact zero_ne_one this
  refine ⟨{ toFun := fun x => rhoE ρ e x u₀ - u₀, map_zero' := ?_, map_add' := ?_ },
    fun x => rfl⟩
  · simp only [ZeroMemClass.coe_zero, rhoE_zero_right]
    simp
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    have hx1 := (mem_perpAdd.mp hx).1
    have hy1 := (mem_perpAdd.mp hy).1
    have h1 := rhoE_mul (ρ := ρ) hx1 hy1
    have h2 := hs.rhoE_apply_sub_eq htop hfix hK hF h8 hF.e_sing he0 hx1 hy1 u₀
    rw [map_sub] at h2
    show rhoE ρ e (x + y) u₀ - u₀ = (rhoE ρ e x u₀ - u₀) + (rhoE ρ e y u₀ - u₀)
    rw [← h1, LinearEquiv.mul_apply]
    linear_combination (norm := module) h2

private theorem natCard_ker_le (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {u₀ : V} (hu₀ : u₀ ∉ 𝒲[e]) (φ : ↥(perpAdd QN e f) →+ V)
    (hφ : ∀ x, φ x = rhoE ρ e x u₀ - u₀) : Nat.card φ.ker ≤ Nat.card K' := by
  have he0 : e ≠ 0 := by
    rintro rfl
    have := hF.ef
    rw [polar_zero_left] at this
    exact zero_ne_one this
  have hW : ∀ w ∈ φ.ker.map (perpAdd QN e f).subtype,
      polar QN e w = 0 ∧ polar QN f w = 0 ∧ QN w = 0 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := mem_perpAdd.mp x.2
    refine ⟨hx1, hx2, ?_⟩
    by_contra hQ
    apply hu₀
    have hx' : φ x = 0 := hx
    rw [hφ, sub_eq_zero] at hx'
    exact (hs.rhoE_apply_eq_iff_mem_iSup htop hfix hK hF h8 hF.e_sing he0 hx1 hQ u₀).mp hx'
  have hcard := hF.natCard_le_of_forall_singular (φ.ker.map (perpAdd QN e f).subtype)
    (fun w hw => (hW w hw).1) (fun w hw => (hW w hw).2.1) fun w hw => (hW w hw).2.2
  rwa [AddSubgroup.card_map_of_injective (perpAdd QN e f).subtype_injective] at hcard

private theorem three_le_finrank_inf (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {U : Submodule K V} (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (hnot : ¬ U ≤ 𝒲[e]) : 3 ≤ finrank K ↥(U ⊓ 𝒲[e]) := by
  obtain ⟨u₀, hu₀U, hu₀⟩ : ∃ x ∈ U, x ∉ 𝒲[e] := by
    by_contra! h
    exact hnot fun x hx => h x hx
  have : Finite V := Module.finite_of_finite K
  obtain ⟨φ, hφ⟩ := exists_addMonoidHom hs htop hfix hK hF h8 u₀
  have hker := natCard_ker_le hs htop hfix hK hF h8 hu₀ φ hφ
  have hper := natCard_pow_four_le_perpAdd hF
  have hrange : ∀ y ∈ φ.range, y ∈ U ⊓ 𝒲[e] := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    refine ⟨U.sub_mem (hU ⟨eichler QN e x, eichler_mem_elementaryGroup QN e x⟩ u₀ hu₀U) hu₀U, ?_⟩
    exact le_iSup₂_of_le (f := fun (w : N) (_ : polar QN e w = 0) => movedSpace (rhoE ρ e w))
      x (mem_perpAdd.mp x.2).1 le_rfl (sub_mem_movedSpace _ u₀)
  have h1 : Nat.card φ.range ≤ Nat.card ↥(U ⊓ 𝒲[e]) :=
    Nat.card_le_card_of_injective (fun y => (⟨y.1, hrange y.1 y.2⟩ : ↥(U ⊓ 𝒲[e])))
      fun a b h => Subtype.ext (congrArg (fun z : ↥(U ⊓ 𝒲[e]) => (z : V)) h)
  have h2 : Nat.card ↥(U ⊓ 𝒲[e]) = Nat.card K' ^ finrank K ↥(U ⊓ 𝒲[e]) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hs.card]
  have h3 := AddSubgroup.card_ker_mul_card_range φ
  have hq : 0 < Nat.card K' := Nat.card_pos
  have h4 : Nat.card K' ^ 3 ≤ Nat.card φ.range := by
    have : Nat.card K' ^ 3 * Nat.card K' ≤ Nat.card φ.range * Nat.card K' :=
      calc Nat.card K' ^ 3 * Nat.card K' = Nat.card K' ^ 4 := by ring
        _ ≤ Nat.card ↥(perpAdd QN e f) := hper
        _ = Nat.card φ.ker * Nat.card φ.range := h3.symm
        _ ≤ Nat.card K' * Nat.card φ.range := Nat.mul_le_mul_right _ hker
        _ = Nat.card φ.range * Nat.card K' := mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this hq
  have h5 : Nat.card K' ^ 3 ≤ Nat.card K' ^ finrank K ↥(U ⊓ 𝒲[e]) :=
    h4.trans (h1.trans h2.le)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card K')).mp h5

omit [CharP K 2] [Finite K] in
private theorem finrank_le_two_mul_of_fixed (h : V ≃ₗ[K] V) (T Z : Submodule K V)
    (hfix : ∀ x, h x = x ↔ x ∈ Z) (hmov : ∀ x, h x - x ∈ Z) (hT : ∀ x ∈ T, h x ∈ T) :
    finrank K ↥T ≤ 2 * finrank K ↥(T ⊓ Z) := by
  let D : V →ₗ[K] V := (h : V →ₗ[K] V) - 1
  have hD : ∀ x, D x = h x - x := fun x => by simp [D]
  have hker : LinearMap.ker D = Z := by
    ext x
    rw [LinearMap.mem_ker, hD, sub_eq_zero, hfix]
  have h1 := LinearMap.finrank_range_add_finrank_ker (D.domRestrict T)
  have h2 : LinearMap.range (D.domRestrict T) ≤ T ⊓ Z := by
    rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · simp only [LinearMap.domRestrict_apply, hD]
      exact T.sub_mem (hT x x.2) x.2
    · simp only [LinearMap.domRestrict_apply, hD]
      exact hmov x
  have h3 := Submodule.finrank_mono h2
  have h4 : finrank K ↥(LinearMap.ker (D.domRestrict T)) = finrank K ↥(T ⊓ Z) := by
    rw [← Submodule.finrank_map_subtype_eq T (LinearMap.ker (D.domRestrict T)),
      LinearMap.ker_domRestrict, Submodule.map_comap_subtype, hker]
  omega

private theorem movedSpace_rhoE_le (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {U : Submodule K V} (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (h3 : 3 ≤ finrank K ↥(U ⊓ 𝒲[e])) : movedSpace (rhoE ρ e p) ≤ U := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hF.pp'
    rw [polar_zero_left] at this
    exact zero_ne_one this
  have hpu : polar QN p u = 0 := by
    rw [polar_comm]
    exact hF.u_perp.2.2.1
  have hQu : QN u ≠ 0 := by
    rw [hF.Qu]
    exact one_ne_zero
  have hfixp := fun x => hs.rhoE_apply_eq_iff_mem_iSup htop hfix hK hF h8 hF.p_sing hp0 hpu hQu x
  have hmovp : movedSpace (rhoE ρ p u) = 𝒲[p] :=
    hs.movedSpace_rhoE_eq_iSup htop hfix hK hF h8 hF.p_sing hp0 hpu hQu
  have hWe : ∀ x ∈ 𝒲[e], rhoE ρ p u x ∈ 𝒲[e] := by
    intro x hx
    set g : ↥(elementaryGroup QN) := ⟨eichler QN p u, eichler_mem_elementaryGroup QN p u⟩
    have hmap := OmegaSetting.map_iSup_movedSpace_rhoE (ρ := ρ) g e
    have hge : (g : N ≃ₗ[K'] N) e = e :=
      eichler_apply_of_polar_eq_zero hF.ep (by rw [polar_comm]; exact hF.u_perp.1)
    rw [hge] at hmap
    have hmem : ρ g x ∈ (𝒲[e]).map (ρ g : V →ₗ[K] V) := Submodule.mem_map_of_mem hx
    rw [hmap] at hmem
    exact hmem
  have hrank := finrank_le_two_mul_of_fixed (rhoE ρ p u) (U ⊓ 𝒲[e]) (𝒲[p]) hfixp
    (fun x => hmovp ▸ sub_mem_movedSpace _ x) fun x hx => ⟨hU _ _ hx.1, hWe x hx.2⟩
  have h2 : 2 ≤ finrank K ↥((U ⊓ 𝒲[e]) ⊓ 𝒲[p]) := by omega
  have hli : LinearIndependent K' ![e, p] :=
    linearIndependent_pair_of_polar (z₁ := f) (z₂ := p') (by rw [hF.ef]; exact one_ne_zero)
      (by rw [polar_comm]; exact hF.fp) (by rw [hF.pp']; exact one_ne_zero)
  have hdim := hs.finrank_movedSpace_rhoE hF.e_sing hF.p_sing hF.ep hli
  have hmeet := hs.iSup_inf_iSup_eq_movedSpace htop hfix hK hF h8
  have hle : (U ⊓ 𝒲[e]) ⊓ 𝒲[p] ≤ movedSpace (rhoE ρ e p) :=
    (inf_le_inf_right _ inf_le_right).trans hmeet.le
  have heq : (U ⊓ 𝒲[e]) ⊓ 𝒲[p] = movedSpace (rhoE ρ e p) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [← heq]
  exact inf_le_left.trans inf_le_left

private theorem axis_le_of_three_le (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {U : Submodule K V} (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (h3 : 3 ≤ finrank K ↥(U ⊓ 𝒲[e])) : 𝒲[e] ≤ U := by
  have h1 := movedSpace_rhoE_le hs htop hfix hK hF h8 hU h3
  have h2 := movedSpace_rhoE_le hs htop hfix hK hF.swapRight h8 hU h3
  rw [hs.iSup_movedSpace_rhoE_eq_of_caseII hfix hK hF
    (hs.caseII_of_six_lt_finrank htop hF (by omega))]
  exact sup_le h1 h2

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem movedSpace_rhoE_le_of_axis_le (hs : OmegaSetting QN Qf ρ) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {U : Submodule K V}
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (hW : 𝒲[e] ≤ U) (a w : N) :
    movedSpace (rhoE ρ a w) ≤ U := by
  by_cases h : QN a = 0 ∧ polar QN a w = 0 ∧ a ≠ 0
  · obtain ⟨ha, haw, ha0⟩ := h
    obtain ⟨g, hg⟩ := exists_apply_eq_of_frame hs.ndN hF ha ha0
    have hmap := OmegaSetting.map_iSup_movedSpace_rhoE (ρ := ρ) g e
    rw [hg] at hmap
    calc movedSpace (rhoE ρ a w) ≤ 𝒲[a] := le_iSup₂_of_le w haw le_rfl
      _ = (𝒲[e]).map (ρ g : V →ₗ[K] V) := hmap.symm
      _ ≤ U := by
        rintro _ ⟨x, hx, rfl⟩
        exact hU g x (hW hx)
  · have h1 : eichler QN a w = 1 := by
      by_cases h' : QN a = 0 ∧ polar QN a w = 0
      · have ha0 : a = 0 := by
          by_contra ha0
          exact h ⟨h'.1, h'.2, ha0⟩
        rw [ha0, eichler_zero_left]
      · exact eichler_of_not h'
    have h2 : rhoE ρ a w = 1 := by
      unfold rhoE
      rw [← map_one ρ]
      exact congrArg ρ (Subtype.ext h1)
    intro y hy
    obtain ⟨x, hx⟩ := mem_movedSpace_iff.mp hy
    rw [h2] at hx
    have : y = 0 := by simpa using hx.symm
    rw [this]
    exact U.zero_mem

omit [CharP K' 2] [Finite K'] [FiniteDimensional K' N] [Finite K] [FiniteDimensional K V] in
private theorem eq_top_of_axis_le (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' u v : N}
    (hF : MinusThreeFrame QN e f p p' u v) {U : Submodule K V}
    (hU : ∀ g x, x ∈ U → ρ g x ∈ U) (hW : 𝒲[e] ≤ U) : U = ⊤ := by
  have hle := top_le_iSup_of_generate (ρ := ρ) htop (ι := N × N) (fun i => i.1) (fun i => i.2)
    (A := fun _ => U) ?_ fun i c => movedSpace_rhoE_le_of_axis_le hs hF hU hW i.1 (c • i.2)
  · rw [iSup_const] at hle
    exact eq_top_iff.mpr hle
  · refine elementaryGroup_le_of_eichler_mem fun a w _ _ => ?_
    exact Subgroup.subset_closure ⟨(a, w), 1, by rw [one_smul]⟩

theorem OmegaSetting.eq_top_of_invariant (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {U : Submodule K V} (hU : ∀ g x, x ∈ U → ρ g x ∈ U)
    (hU0 : U ≠ ⊥) : U = ⊤ := by
  have hnot := not_le_axis hs htop hfix hK hF h8 hU hU0
  have h3 := three_le_finrank_inf hs htop hfix hK hF h8 hU hnot
  exact eq_top_of_axis_le hs htop hF hU (axis_le_of_three_le hs htop hfix hK hF h8 hU h3)

theorem OmegaSetting.eq_one_of_commute_of_mul_self (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) (hfix : ∀ x : V, (∀ g, ρ g x = x) → x = 0)
    (hK : 2 < Nat.card K') {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h8 : finrank K V = 8) {c : V ≃ₗ[K] V} (hc : c * c = 1)
    (hcomm : ∀ g, c * ρ g = ρ g * c) : c = 1 := by
  let U : Submodule K V := LinearMap.ker ((c : V →ₗ[K] V) - 1)
  have hmem : ∀ x, x ∈ U ↔ c x = x := fun x => by simp [U, sub_eq_zero]
  have hU : ∀ g x, x ∈ U → ρ g x ∈ U := by
    intro g x hx
    rw [hmem] at hx ⊢
    have := congrArg (fun m : V ≃ₗ[K] V => m x) (hcomm g)
    simp only [LinearEquiv.mul_apply] at this
    rw [this, hx]
  by_contra hne
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra! h
    exact hne (LinearEquiv.ext h)
  have hcc : c (c x) = x := by
    have := congrArg (fun m : V ≃ₗ[K] V => m x) hc
    simpa using this
  have hneg : ∀ y : V, -y = y := fun y => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul K y, CharTwo.two_eq_zero, zero_smul]
  have hU0 : U ≠ ⊥ := by
    intro hbot
    have hy : c x - x ∈ U := by
      rw [hmem, map_sub, hcc, ← neg_sub, hneg]
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hy
    exact hx hy
  have htop' := hs.eq_top_of_invariant htop hfix hK hF h8 hU hU0
  exact hx ((hmem x).mp (htop' ▸ Submodule.mem_top))

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
