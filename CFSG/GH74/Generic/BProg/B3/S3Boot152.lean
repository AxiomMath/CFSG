module

public import CFSG.GH74.Generic.BProg.B3.S3BootDefs
public import CFSG.GH74.GLS.C3.Layer1.Th2P61Obs
public import CFSG.GH74.GLS.C3.Layer1.St1Iv85
public import CFSG.GH74.Generic.BProg.B2.Lemma82Gen

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.Dichotomy
open scoped commutatorElement

namespace S3Boot152

section Local

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem conj_mem_centralizer_of_mem_normalizer {L : Subgroup Y} {n z : Y}
    (hn : n ∈ normalizer (L : Set Y)) (hz : z ∈ centralizer (L : Set Y)) :
    n * z * n⁻¹ ∈ centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ L := by
    rw [Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * x * n)]
    have : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [this]
    exact hx
  have h1 := Subgroup.mem_centralizer_iff.mp hz _ hx'
  calc x * (n * z * n⁻¹) = n * ((n⁻¹ * x * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = n * z * n⁻¹ * x := by group

theorem comm_mem_centralizer_of_weakLocBal {L : Subgroup Y} (hL : IsComponent L) {P : Subgroup Y}
    (hbal : IsLocBal32 (↥L ⧸ center ↥L) ((P.subgroupOf (normalizer (L : Set Y))).map (rhoL L)))
    {f : Y} (hfP : f ∈ P) (hfM : f ∈ normalizer (L : Set Y)) (hf2 : f * f = 1)
    (hfL : ¬ ∀ x ∈ L, f * x = x * f)
    {n : Y} (hnM : n ∈ normalizer (L : Set Y)) (hn : n ∈ involutionOddCore f)
    {a : Y} (haP : a ∈ P) (haM : a ∈ normalizer (L : Set Y)) :
    ∀ x ∈ L, ⁅n, a⁆ * x = x * ⁅n, a⁆ := by
  classical
  have : Group.IsPerfect L := hL.1.1
  set M : Subgroup Y := normalizer (L : Set Y) with hM
  let ρ : M →* MulAut (↥L ⧸ center ↥L) := rhoL L
  have hker : ρ.ker = (Subgroup.centralizer (L : Set Y)).subgroupOf M :=
    CFSG.LocalAnalysis.ComponentInitial.ker_centerQuotient_comp_normalizerConjHom L
  have hInn : (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range ≤ ρ.range :=
    CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* ρ.range := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hφker : φ.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  have hBH : (P.subgroupOf M).map ρ ≤ ρ.range := by
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  have key := (hbal ρ.range hInn hBH).1
  have hmemB : ∀ {u : Y} (hu : u ∈ P) (huM : u ∈ M),
      φ ⟨u, huM⟩ ∈ ((P.subgroupOf M).map ρ).subgroupOf ρ.range := by
    intro u hu huM
    rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hb1 : φ ⟨f, hfM⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨f, hfM⟩ : M) ∈ φ.ker := h1
    rw [hφker, hker, Subgroup.mem_subgroupOf] at h2
    exact hfL fun x hx => (Subgroup.mem_centralizer_iff.mp h2 x hx).symm
  have hc : φ ⟨n, hnM⟩ ∈ involutionOddCore (φ ⟨f, hfM⟩) := by
    refine map_involutionOddCore_le φ hφ (a := (⟨f, hfM⟩ : M))
      (isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hf2 : (⟨f, hfM⟩ : M) * ⟨f, hfM⟩ = 1))
      (Subgroup.mem_map_of_mem φ ?_)
    exact subgroupOf_involutionOddCore_le (⟨f, hfM⟩ : M) (Subgroup.mem_subgroupOf.mpr hn)
  have h2 := key (φ ⟨f, hfM⟩) (hmemB hfP hfM) hb1 (φ ⟨n, hnM⟩) hc (φ ⟨a, haM⟩) (hmemB haP haM)
  have h3 : (⁅(⟨n, hnM⟩ : M), (⟨a, haM⟩ : M)⁆) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact h2
  rw [hφker, hker, Subgroup.mem_subgroupOf] at h3
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp h3 x hx).symm

theorem commute_of_faithful_locBal {L : Subgroup Y} (hL : IsComponent L) {P : Subgroup Y}
    (hbal : IsLocBal32 (↥L ⧸ center ↥L) ((P.subgroupOf (normalizer (L : Set Y))).map (rhoL L)))
    {F : Subgroup Y} (hFP : F ≤ P) (hF4 : Nat.card ↥F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFL : ∀ f ∈ F, conjSub f L = L)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f)
    {D : Subgroup Y} (hD : ∀ d ∈ D, conjSub d L = L)
    (hDF : ∀ f ∈ F, f ≠ 1 → D ≤ involutionOddCore f) :
    ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
  classical
  have : Group.IsPerfect L := hL.1.1
  set M : Subgroup Y := normalizer (L : Set Y) with hM
  have hFM : F ≤ M := fun f hf => mem_normalizer_of_conjSub_eq (hFL f hf)
  have hDM : D ≤ M := fun d hd => mem_normalizer_of_conjSub_eq (hD d hd)
  let ρ : M →* MulAut (↥L ⧸ center ↥L) := rhoL L
  have hker : ρ.ker = (Subgroup.centralizer (L : Set Y)).subgroupOf M :=
    CFSG.LocalAnalysis.ComponentInitial.ker_centerQuotient_comp_normalizerConjHom L
  have hInn : (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)).range ≤ ρ.range :=
    CFSG.LocalAnalysis.ComponentInitial.inner_le_range_centerQuotient_comp L
  let φ : M →* ρ.range := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hφker : φ.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  have hBH : (P.subgroupOf M).map ρ ≤ ρ.range := by
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  set F' : Subgroup M := F.subgroupOf M with hF'
  have hFinj : ∀ m ∈ F', φ m = 1 → m = 1 := by
    intro m hm hm1
    have h1 : m ∈ ρ.ker := by rw [← hφker]; exact hm1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    by_contra hne
    refine hFfaith (m : Y) ((Subgroup.mem_subgroupOf).mp hm) (fun h => hne (Subtype.ext h)) ?_
    intro x hx
    exact (h1 x hx).symm
  have hcard : Nat.card (F'.map φ) = 4 := by
    have hbij : Function.Bijective (φ.subgroupMap F') := by
      refine ⟨?_, φ.subgroupMap_surjective F'⟩
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro m hm
      have := hFinj m m.2 (by
        have h2 := (MonoidHom.mem_ker.mp hm)
        have h3 := congrArg Subtype.val h2
        exact h3)
      exact Subtype.ext this
    have hc : Nat.card (F'.map φ) = Nat.card F := by
      rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
    rw [hc]
    exact hF4
  have hexp : ∀ g ∈ F'.map φ, g * g = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hF2 m ((Subgroup.mem_subgroupOf).mp hm))
    rw [this, map_one]
  have hsub : F'.map φ ≤ ((P.subgroupOf M).map ρ).subgroupOf ρ.range := by
    rintro _ ⟨m, hm, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨m, Subgroup.mem_subgroupOf.mpr (hFP ((Subgroup.mem_subgroupOf).mp hm)), rfl⟩
  have hdelta : deltaCore (F'.map φ) = ⊥ := (hbal ρ.range hInn hBH).2 (F'.map φ) hsub hcard hexp
  have hDle : (D.subgroupOf M).map φ ≤ deltaCore (F'.map φ) := by
    refine le_deltaCore fun g hg hg1 => ?_
    obtain ⟨m, hm, rfl⟩ := hg
    have hmF : (m : Y) ∈ F := (Subgroup.mem_subgroupOf).mp hm
    have hm1 : (m : Y) ≠ 1 := by
      intro h
      have hm1' : m = 1 := Subtype.ext h
      exact hg1 (by rw [hm1']; exact map_one φ)
    have hDm : D.subgroupOf M ≤ involutionOddCore m := fun u hu =>
      subgroupOf_involutionOddCore_le m
        ((Subgroup.mem_subgroupOf).mpr (hDF (m : Y) hmF hm1 ((Subgroup.mem_subgroupOf).mp hu)))
    exact (Subgroup.map_mono hDm).trans
      (map_involutionOddCore_le φ hφ (isPGroup_zpowers_of_mul_self_eq_one
        (Subtype.ext (hF2 (m : Y) hmF) : m * m = 1)))
  rw [hdelta] at hDle
  intro d hd x hx
  have hmem : φ ⟨d, hDM hd⟩ ∈ (⊥ : Subgroup (ρ.range)) :=
    hDle ⟨⟨d, hDM hd⟩, (Subgroup.mem_subgroupOf).mpr hd, rfl⟩
  have h1 : (⟨d, hDM hd⟩ : M) ∈ φ.ker := Subgroup.mem_bot.mp hmem
  rw [hφker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

end Local

section Quot

variable {X : Type} [Group X] [Finite X]

@[expose] def LocHyp (A : Subgroup X) (Jb : Subgroup (X ⧸ pPrimeCore 2 X)) : Prop :=
  (∃ F : Subgroup X, F ≤ A ∧ 2 * Nat.card ↥F ≥ Nat.card ↥A ∧
    F.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ centralizer (Jb : Set (X ⧸ pPrimeCore 2 X))) ∨
  ∃ _hN : A.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)),
    IsLocBal32 (↥Jb ⧸ center ↥Jb)
      (((A.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf
        (normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)))).map (rhoL Jb))

theorem card_map_of_injOn {X' Z : Type*} [Group X'] [Group Z] (f : X' →* Z) {S : Subgroup X'}
    (h : ∀ s ∈ S, f s = 1 → s = 1) : Nat.card ↥(S.map f) = Nat.card ↥S := by
  have hinj : Function.Injective (f.comp S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have h1 : f ((x : X')⁻¹ * y) = 1 := by
      rw [map_mul, map_inv]
      have : f x = f y := hxy
      rw [this, inv_mul_cancel]
    exact inv_mul_eq_one.mp (h _ (S.mul_mem (S.inv_mem x.2) y.2) h1)
  have hr : (f.comp S.subtype).range = S.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem mk_injOn_two {a : X} (ha : a * a = 1) (h : QuotientGroup.mk' (pPrimeCore 2 X) a = 1) :
    a = 1 :=
  eq_one_of_sq_of_mem_pPrimeCore ha ((QuotientGroup.eq_one_iff a).mp h)

theorem map_AG_le_deltaCore {D : Subgroup X} (hD2 : ∀ d ∈ D, d * d = 1) :
    (AG D).map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
      deltaCore (D.map (QuotientGroup.mk' (pPrimeCore 2 X))) := by
  refine le_deltaCore fun f hf hf1 => ?_
  obtain ⟨d, hd, rfl⟩ := hf
  have hd1 : d ≠ 1 := fun h => hf1 (by rw [h, map_one])
  have h1 : AG D ≤ involutionOddCore d := by
    rw [C3.Layer1.Iv85.involutionOddCore_eq_pPrimeCoreOf]
    exact Th2Sig6.AG_le_pPrimeCoreOf hd hd1
  exact (Subgroup.map_mono h1).trans (map_involutionOddCore_le _ (QuotientGroup.mk'_surjective _)
    (isPGroup_zpowers_of_mul_self_eq_one (hD2 d hd)))

theorem mem_or_mul_mem {A F : Subgroup X} (hFA : F ≤ A) (hcard : Nat.card ↥A ≤ 2 * Nat.card ↥F)
    {d : X} (hdA : d ∈ A) (hdF : d ∉ F) {α : X} (hα : α ∈ A) : α ∈ F ∨ α * d ∈ F := by
  by_cases hαF : α ∈ F
  · exact Or.inl hαF
  · right
    set F' : Subgroup ↥A := F.subgroupOf A with hF'
    have hc : Nat.card ↥F' = Nat.card ↥F :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFA).toEquiv
    have hmul := F'.card_mul_index
    have hpos : 0 < Nat.card ↥F := Nat.card_pos
    have hidx : F'.index = 2 := by
      have h1 : F'.index ≤ 2 := by
        by_contra h
        push Not at h
        rw [hc] at hmul
        have : Nat.card ↥F * 3 ≤ Nat.card ↥F * F'.index := Nat.mul_le_mul_left _ h
        omega
      have h2 : F'.index ≠ 1 := by
        intro h1
        have htop := Subgroup.index_eq_one.mp h1
        have hmem : (⟨d, hdA⟩ : ↥A) ∈ F' := by rw [htop]; exact Subgroup.mem_top _
        exact hdF (Subgroup.mem_subgroupOf.mp hmem)
      have h3 : F'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hiff := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨α, hα⟩ : ↥A)) (b := ⟨d, hdA⟩)).mpr
      (by
        have h1 : (⟨α, hα⟩ : ↥A) ∉ F' := fun h => hαF (Subgroup.mem_subgroupOf.mp h)
        have h2 : (⟨d, hdA⟩ : ↥A) ∉ F' := fun h => hdF (Subgroup.mem_subgroupOf.mp h)
        exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩)
    exact Subgroup.mem_subgroupOf.mp hiff

theorem exists_ne_of_card {E : Subgroup X} (hE4 : 4 ≤ Nat.card ↥E) {e₁ : X} (he₁ : e₁ * e₁ = 1) :
    ∃ e ∈ E, e ≠ 1 ∧ e ≠ e₁ := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers e₁ := by
    intro e he
    by_cases h1 : e = 1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [hcon e he h1]; exact Subgroup.mem_zpowers _
  have h2 : Nat.card ↥E ≤ Nat.card ↥(Subgroup.zpowers e₁) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers] at h2
  have h3 : orderOf e₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, he₁])
  have h4 : orderOf e₁ ≤ 2 := Nat.le_of_dvd (by norm_num) h3
  omega

theorem AG_le_pPrimeCore_of_loc {A : Subgroup X} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hloc : ∀ Jb : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent Jb → LocHyp A Jb)
    {E : Subgroup X} (hEA : E ≤ A) (hE4 : 4 ≤ Nat.card ↥E) : AG E ≤ pPrimeCore 2 X := by
  classical
  by_contra hne
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have hEel : CFSG.IsElementaryAbelian 2 ↥E := Th2Sig6.isElementaryAbelian_of_le hAel hEA
  have hE2 : ∀ e ∈ E, e * e = 1 := fun e he => hAsq e (hEA he)
  have hinj : ∀ a ∈ A, π a = 1 → a = 1 := fun a ha h => mk_injOn_two (hAsq a ha) h
  have hO : pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _
  have hF2 : ∀ f ∈ E.map π, f * f = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hE2 e he, map_one]
  have hNbot : (AG E).map π ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
    exact h
  obtain ⟨e₀, he₀E, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hbot, Subgroup.card_bot] at hE4
    omega
  have hf₀1 : π e₀ ≠ 1 := fun h => he₀1 (hinj e₀ (hEA he₀E) h)
  obtain ⟨L, hL, hFL, hfaith, hNL, hnc⟩ := exists_component_of_deltaCore hO hF2
    (Subgroup.mem_map_of_mem π he₀E) hf₀1 (map_AG_le_deltaCore hE2) hNbot
  rcases hloc L hL with ⟨Fh, hFhA, hFhcard, hFhcent⟩ | ⟨hAN, hbal⟩
  ·
    have hex : ∃ e ∈ E, e ≠ 1 ∧ e ∈ Fh := by
      by_contra hno
      push Not at hno
      have he₀F : e₀ ∉ Fh := fun h => hno e₀ he₀E he₀1 h
      obtain ⟨e₂, he₂E, he₂1, he₂ne⟩ := exists_ne_of_card hE4 (hE2 e₀ he₀E)
      have hor := mem_or_mul_mem hFhA hFhcard (hEA he₀E) he₀F (hEA he₂E)
      rcases hor with h | h
      · exact hno e₂ he₂E he₂1 h
      · refine hno (e₂ * e₀) (E.mul_mem he₂E he₀E) ?_ h
        intro h1
        apply he₂ne
        have := mul_eq_one_iff_eq_inv.mp h1
        rw [this]
        exact inv_eq_of_mul_eq_one_left (hE2 e₀ he₀E)
    obtain ⟨e, heE, he1, heF⟩ := hex
    have hπe1 : π e ≠ 1 := fun h => he1 (hinj e (hEA heE) h)
    apply hfaith (π e) (Subgroup.mem_map_of_mem π heE) hπe1
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hFhcent (Subgroup.mem_map_of_mem π heF)) x hx).symm
  ·
    have hr2 : 2 ≤ pRank 2 ↥E := by
      by_contra h
      push Not at h
      have h1 : pRank 2 ↥E ≤ 1 := by omega
      have h2 := C3.Layer1.Back.card_eq_two_pow_pRank hEel
      have h3 : 2 ^ pRank 2 ↥E ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      omega
    obtain ⟨S, hSE, hScard⟩ := Th2Sig6.exists_sub_card hEel hr2
    have hS4 : Nat.card ↥S = 4 := by rw [hScard]; norm_num
    have hSmap : Nat.card ↥(S.map π) = 4 := by
      rw [card_map_of_injOn π (fun s hs h => hinj s (hEA (hSE hs)) h), hS4]
    apply hnc
    intro n hn x hx
    exact commute_of_faithful_locBal hL (P := A.map π) hbal
      (Subgroup.map_mono (hSE.trans hEA)) hSmap
      (fun f hf => hF2 f (Subgroup.map_mono hSE hf))
      (fun f hf => hFL f (Subgroup.map_mono hSE hf))
      (fun f hf hf1 => hfaith f (Subgroup.map_mono hSE hf) hf1) (D := (AG E).map π) hNL
      (fun f hf hf1 => (map_AG_le_deltaCore hE2).trans
        (deltaCore_le_involutionOddCore (Subgroup.map_mono hSE hf) hf1)) n hn x hx

theorem comm_AG_le_pPrimeCore_of_loc {A : Subgroup X} (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hloc : ∀ Jb : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent Jb → LocHyp A Jb)
    {D₀ : Subgroup X} (hD₀A : D₀ ≤ A) (hD₀1 : ∃ d ∈ D₀, d ≠ 1) :
    ⁅AG D₀, A⁆ ≤ pPrimeCore 2 X := by
  classical
  by_contra hne
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hAel
  have hD₀2 : ∀ d ∈ D₀, d * d = 1 := fun d hd => hAsq d (hD₀A hd)
  have hinj : ∀ a ∈ A, π a = 1 → a = 1 := fun a ha h => mk_injOn_two (hAsq a ha) h
  have hO : pPrimeCore 2 (X ⧸ pPrimeCore 2 X) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _
  have hF2 : ∀ f ∈ D₀.map π, f * f = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, hD₀2 e he, map_one]
  have hcomm_le : ⁅AG D₀, A⁆ ≤ AG D₀ := by
    rw [Subgroup.commutator_le]
    intro y hy b hb
    have hcomm : ⁅y, b⁆ = y * (b * y⁻¹ * b⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [hcomm]
    exact (AG D₀).mul_mem hy
      (conj_mem_AG (fun d hd => hAc _ hb d (hD₀A hd)) ((AG D₀).inv_mem hy))
  have hN₁ : ⁅(AG D₀).map π, A.map π⁆ ≠ ⊥ := by
    intro h
    apply hne
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at h
    exact h
  have hN₁le : ⁅(AG D₀).map π, A.map π⁆ ≤ deltaCore (D₀.map π) := by
    rw [← Subgroup.map_commutator]
    exact (Subgroup.map_mono hcomm_le).trans (map_AG_le_deltaCore hD₀2)
  obtain ⟨d₀, hd₀D, hd₀1⟩ := hD₀1
  have hf₀1 : π d₀ ≠ 1 := fun h => hd₀1 (hinj d₀ (hD₀A hd₀D) h)
  have hf₀F : π d₀ ∈ D₀.map π := Subgroup.mem_map_of_mem π hd₀D
  obtain ⟨L, hL, hFL, hfaith, -, hnc⟩ := exists_component_of_deltaCore hO hF2 hf₀F hf₀1 hN₁le hN₁
  have hN₀odd : ∀ n ∈ (AG D₀).map π, n ∈ involutionOddCore (π d₀) := fun n hn =>
    ((map_AG_le_deltaCore hD₀2).trans (deltaCore_le_involutionOddCore hf₀F hf₀1)) hn
  have hN₀L : ∀ n ∈ (AG D₀).map π, n ∈ normalizer (L : Set (X ⧸ pPrimeCore 2 X)) := fun n hn =>
    mem_normalizer_of_conjSub_eq
      (conjSub_eq_of_mem_involutionOddCore hL (hF2 _ hf₀F) (hFL _ hf₀F) (hN₀odd n hn))
  have key : ∀ n ∈ (AG D₀).map π, ∀ α ∈ A,
      ⁅n, π α⁆ ∈ centralizer (L : Set (X ⧸ pPrimeCore 2 X)) := by
    intro n hn α hα
    rcases hloc L hL with ⟨Fh, hFhA, hFhcard, hFhcent⟩ | ⟨hAN, hbal⟩
    · have hd₀F : d₀ ∉ Fh := by
        intro h
        apply hfaith (π d₀) hf₀F hf₀1
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp (hFhcent (Subgroup.mem_map_of_mem π h)) x hx).symm
      have hcen : ∀ c ∈ centralizer (L : Set (X ⧸ pPrimeCore 2 X)),
          n * c * n⁻¹ * c⁻¹ ∈ centralizer (L : Set (X ⧸ pPrimeCore 2 X)) := fun c hc =>
        (centralizer (L : Set (X ⧸ pPrimeCore 2 X))).mul_mem
          (conj_mem_centralizer_of_mem_normalizer (hN₀L n hn) hc)
          ((centralizer (L : Set (X ⧸ pPrimeCore 2 X))).inv_mem hc)
      rcases mem_or_mul_mem hFhA hFhcard (hD₀A hd₀D) hd₀F hα with h | h
      · exact hcen (π α) (hFhcent (Subgroup.mem_map_of_mem π h))
      · have hc := hFhcent (Subgroup.mem_map_of_mem π h)
        have hcn : Commute n (π d₀) :=
          Subgroup.mem_centralizer_singleton_iff.mp
            (involutionOddCore_le_centralizer _ (hN₀odd n hn))
        have hπ' : π (α * d₀) = π α * π d₀ := map_mul π α d₀
        rw [hπ'] at hc
        have h1 := hcen _ hc
        have h2 : n * (π α * π d₀) * n⁻¹ * (π α * π d₀)⁻¹ = ⁅n, π α⁆ := by
          have e1 : n * (π α * π d₀) * n⁻¹ = n * π α * n⁻¹ * π d₀ := by
            calc n * (π α * π d₀) * n⁻¹ = n * π α * (π d₀ * n⁻¹) := by group
              _ = n * π α * (n⁻¹ * π d₀) := by rw [(hcn.inv_left).eq]
              _ = n * π α * n⁻¹ * π d₀ := by group
          rw [e1, commutatorElement_def]
          group
        rwa [h2] at h1
    · have hπα : π α ∈ A.map π := Subgroup.mem_map_of_mem π hα
      have hbal' := comm_mem_centralizer_of_weakLocBal hL (P := A.map π) hbal
        (Subgroup.mem_map_of_mem π (hD₀A hd₀D)) (hAN (Subgroup.mem_map_of_mem π (hD₀A hd₀D)))
        (hF2 _ hf₀F) (hfaith _ hf₀F hf₀1) (hN₀L n hn) (hN₀odd n hn) hπα (hAN hπα)
      exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hbal' x hx).symm
  apply hnc
  have hle : ⁅(AG D₀).map π, A.map π⁆ ≤ centralizer (L : Set (X ⧸ pPrimeCore 2 X)) := by
    rw [Subgroup.commutator_le]
    rintro n hn _ ⟨α, hα, rfl⟩
    exact key n hn α hα
  intro n hn x hx
  exact (Subgroup.mem_centralizer_iff.mp (hle hn) x hx).symm

end Quot

end S3Boot152

section SD

variable {G : Type} [Group G] [Finite G]

theorem exists_ne_one_of_isE_one {A D : Subgroup G} (hD : IsE 1 A D) : ∃ d ∈ D, d ≠ 1 := by
  obtain ⟨-, hDel, hDr⟩ := hD
  by_contra h
  push Not at h
  have hbot : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
  have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hDel
  rw [hbot, Subgroup.card_bot] at hcard
  have : 2 ≤ 2 ^ pRank 2 ↥D := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ pRank 2 ↥D := Nat.pow_le_pow_right (by norm_num) hDr
  rw [hbot] at this
  omega

theorem iii2_3_15 {X : Type} [Group X] [Finite X] {A : Subgroup X} (hA : IsE 3 ⊤ A)
    (hloc : ∀ Jb : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent Jb →
      (∃ F : Subgroup X, F ≤ A ∧ 2 * Nat.card ↥F ≥ Nat.card ↥A ∧
        F.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ centralizer (Jb : Set (X ⧸ pPrimeCore 2 X))) ∨
      ∃ _hN : A.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
          normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)),
        IsLocBal32 (↥Jb ⧸ center ↥Jb)
          (((A.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf
            (normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)))).map (rhoL Jb))) :
    thetaHalf 1 A ≤ pPrimeCore 2 X := by
  have hAel := hA.2.1
  refine sup_le (iSup_le fun D => iSup_le fun hD => ?_) ?_
  · exact S3Boot152.comm_AG_le_pPrimeCore_of_loc hAel hloc hD.1 (exists_ne_one_of_isE_one hD)
  · refine S3Boot152.AG_le_pPrimeCore_of_loc hAel hloc le_rfl ?_
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hAel
    have h2 : 2 ^ 3 ≤ 2 ^ pRank 2 ↥A := Nat.pow_le_pow_right (by norm_num) hA.2.2
    omega

theorem iii2_3_15_prime {X : Type} [Group X] [Finite X] {A : Subgroup X} (hA : IsE 3 ⊤ A)
    (hloc : ∀ Jb : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent Jb →
      (∃ F : Subgroup X, F ≤ A ∧ 2 * Nat.card ↥F ≥ Nat.card ↥A ∧
        F.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤ centralizer (Jb : Set (X ⧸ pPrimeCore 2 X))) ∨
      ∃ _hN : A.map (QuotientGroup.mk' (pPrimeCore 2 X)) ≤
          normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)),
        IsLocBal32 (↥Jb ⧸ center ↥Jb)
          (((A.map (QuotientGroup.mk' (pPrimeCore 2 X))).subgroupOf
            (normalizer (Jb : Set (X ⧸ pPrimeCore 2 X)))).map (rhoL Jb))) :
    thetaHalfPrime A ≤ pPrimeCore 2 X := by
  have hAel := hA.2.1
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun hDr => ?_
  refine sup_le (iSup_le fun D₀ => iSup_le fun hD₀ => ?_) ?_
  · exact (Subgroup.commutator_mono le_rfl hD.1).trans
      (S3Boot152.comm_AG_le_pPrimeCore_of_loc hAel hloc (hD₀.1.trans hD.1)
        (exists_ne_one_of_isE_one hD₀))
  · refine S3Boot152.AG_le_pPrimeCore_of_loc hAel hloc hD.1 ?_
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hD.2.1
    rw [hDr] at h1
    omega

end SD

namespace S3Boot152

section L153

variable {G : Type} [Group G] [Finite G]

theorem one_le_pRank_of_ne_one {E : Subgroup G} (hEel : CFSG.IsElementaryAbelian 2 ↥E) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) : 1 ≤ pRank 2 ↥E := by
  by_contra h
  push Not at h
  have h0 : pRank 2 ↥E = 0 := by omega
  have hcard := C3.Layer1.Back.card_eq_two_pow_pRank hEel
  rw [h0, pow_zero, Subgroup.card_eq_one] at hcard
  exact he1 (Subgroup.mem_bot.mp (hcard ▸ he))

theorem le_gammaK_self {B : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hr : 3 ≤ pRank 2 ↥B) : B ≤ gammaK 2 B 3 := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨Q, hQB, hQcard⟩ := Th2Sig6.exists_sub_card hBel (k := 3) hr
  have hQel := Th2Sig6.isElementaryAbelian_of_le hBel hQB
  have hQr : 3 ≤ pRank 2 ↥Q := (CFSG.pRank_eq_of_card_eq_pow one_lt_two hQcard).ge
  refine le_trans ?_ (le_iSup₂_of_le Q hQB (le_iSup_of_le hQr le_rfl))
  intro b hb
  exact Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun q hq => hBc q (hQB hq) b hb)

theorem pPrimeCoreOf_centralizer_le {B M : Subgroup G} (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hr4 : pRank 2 ↥B = 4) (hγ : gammaK 2 B 3 ≤ M) {b : G} (hbB : b ∈ B) :
    pPrimeCoreOf 2 (centralizer ({b} : Set G)) ≤ M := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set Y := pPrimeCoreOf 2 (centralizer ({b} : Set G)) with hY
  have hBC : B ≤ centralizer ({b} : Set G) := fun β hβ =>
    mem_centralizer_singleton_iff.mpr (hBc β hβ b hbB)
  have hBY : B ≤ normalizer (Y : Set G) := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore (hBC hβ) hy
    · intro hy
      have := CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore
        ((centralizer ({b} : Set G)).inv_mem (hBC hβ)) hy
      have e : β⁻¹ * (β * y * β⁻¹) * β⁻¹⁻¹ = y := by group
      rwa [e] at this
  have hYodd : Odd (Nat.card ↥Y) := Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _)
  refine (B2.le_iSup_centralizer_hyperplanes hBel (by omega) hBY hYodd).trans ?_
  refine iSup_le fun E => iSup_le fun hEB => iSup_le fun hEr => ?_
  have hEγ : normalizer (E : Set G) ≤ gammaK 2 B 3 :=
    le_iSup₂_of_le E hEB (le_iSup_of_le (by omega) le_rfl)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans (hEγ.trans hγ))

theorem AG_le_map_AG_subgroupOf {M D₀ : Subgroup G}
    (hY : ∀ d ∈ D₀, d ≠ 1 → pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤ M)
    (hD₀1 : ∃ d ∈ D₀, d ≠ 1) : AG D₀ ≤ (AG (D₀.subgroupOf M)).map M.subtype := by
  obtain ⟨d₁, hd₁, hd₁1⟩ := hD₀1
  intro y hy
  have hyM : y ∈ M := hY d₁ hd₁ hd₁1 (Th2Sig6.AG_le_pPrimeCoreOf hd₁ hd₁1 hy)
  refine ⟨⟨y, hyM⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Th2.mem_AG_iff]
  intro b hb hb1
  have hbD : (b : G) ∈ D₀ := Subgroup.mem_subgroupOf.mp hb
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hyb := Th2Sig6.AG_le_pPrimeCoreOf hbD hb1' hy
  rw [← C3.Layer1.Iv85.involutionOddCore_eq_pPrimeCoreOf]
  exact Th2.Obs.mem_involutionOddCore_of_mem_pPrimeCoreOf (M := M) (d := (b : G)) b.2 hyM hyb

theorem thetaHalf_le_map_subgroupOf {M D : Subgroup G} (hDM : D ≤ M) (hD1 : ∃ d ∈ D, d ≠ 1)
    (hDel : CFSG.IsElementaryAbelian 2 ↥D)
    (hY : ∀ d ∈ D, d ≠ 1 → pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤ M) :
    thetaHalf 1 D ≤ (thetaHalf 1 (D.subgroupOf M)).map M.subtype := by
  have hsub : ∀ D₀ : Subgroup G, D₀ ≤ D → (∃ d ∈ D₀, d ≠ 1) →
      AG D₀ ≤ (AG (D₀.subgroupOf M)).map M.subtype := fun D₀ hD₀D hD₀1 =>
    AG_le_map_AG_subgroupOf (fun d hd hd1 => hY d (hD₀D hd) hd1) hD₀1
  have hDD : D ≤ (D.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hDM).ge
  refine sup_le (iSup_le fun D₀ => iSup_le fun hD₀ => ?_) ?_
  · have hD₀1 := exists_ne_one_of_isE_one hD₀
    have h1 := hsub D₀ hD₀.1 hD₀1
    have hD₀el' : CFSG.IsElementaryAbelian 2 ↥(D₀.subgroupOf M) :=
      have := hDel
      have : CFSG.IsElementaryAbelian 2 ↥D₀ := Th2Sig6.isElementaryAbelian_of_le hDel hD₀.1
      CFSG.IsElementaryAbelian.subgroupOf (hD₀.1.trans hDM)
    have hD₀' : IsE 1 (D.subgroupOf M) (D₀.subgroupOf M) := by
      refine ⟨fun x hx => hD₀.1 hx, hD₀el', ?_⟩
      obtain ⟨d, hd, hd1⟩ := hD₀1
      exact one_le_pRank_of_ne_one hD₀el' (e := (⟨d, hD₀.1.trans hDM <| hd⟩ : ↥M))
        (Subgroup.mem_subgroupOf.mpr hd) (fun h => hd1 (congrArg Subtype.val h))
    calc ⁅AG D₀, D⁆
        ≤ ⁅(AG (D₀.subgroupOf M)).map M.subtype, (D.subgroupOf M).map M.subtype⁆ :=
          Subgroup.commutator_mono h1 hDD
      _ = (⁅AG (D₀.subgroupOf M), D.subgroupOf M⁆).map M.subtype :=
          (Subgroup.map_commutator _ _ _).symm
      _ ≤ (thetaHalf 1 (D.subgroupOf M)).map M.subtype :=
          Subgroup.map_mono (le_sup_of_le_left (le_iSup₂_of_le _ hD₀' le_rfl))
  · exact (hsub D le_rfl hD1).trans (Subgroup.map_mono le_sup_right)

end L153

end S3Boot152

section SD8

variable {G : Type} [Group G] [Finite G]

theorem lemma153 {x : G} {K A B M : Subgroup G} (h : Boot15B G x K A B M) :
    thetaHalfPrime A ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := h.B_E4.2.1
  have hγ : gammaK 2 B 3 ≤ M := (prop41_52 h.B_E4 h.bal52.1 h.bal52.2).2.1.trans h.M_norm
  have hBM : B ≤ M := (S3Boot152.le_gammaK_self hBel (by rw [h.B_rank]; norm_num)).trans hγ
  have hAM : A ≤ M := h.AB.trans hBM
  refine iSup_le fun D => iSup_le fun hD => iSup_le fun hDr => ?_
  have hDM : D ≤ M := hD.1.trans hAM
  have hD1 : ∃ d ∈ D, d ≠ 1 := exists_ne_one_of_isE_one (⟨hD.1, hD.2.1, by omega⟩ : IsE 1 A D)
  have hYM : ∀ d ∈ D, d ≠ 1 → pPrimeCoreOf 2 (centralizer ({d} : Set G)) ≤ M := fun d hd hd1 =>
    S3Boot152.pPrimeCoreOf_centralizer_le hBel h.B_rank hγ (h.AB (hD.1 hd))
  refine (S3Boot152.thetaHalf_le_map_subgroupOf hDM hD1 hD.2.1 hYM).trans ?_
  refine Subgroup.map_mono (le_trans ?_ h.locM')
  have hDel' : CFSG.IsElementaryAbelian 2 ↥(D.subgroupOf M) := by
    have := hD.2.1
    exact CFSG.IsElementaryAbelian.subgroupOf hDM
  have hcard : Nat.card ↥(D.subgroupOf M) = 2 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv,
      C3.Layer1.Back.card_eq_two_pow_pRank hD.2.1, hDr]
  have hD'r : pRank 2 ↥(D.subgroupOf M) = 2 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hcard
  have hD' : IsE 2 (A.subgroupOf M) (D.subgroupOf M) :=
    ⟨fun x hx => hD.1 hx, hDel', hD'r.ge⟩
  exact le_iSup₂_of_le (D.subgroupOf M) hD' (le_iSup_of_le hD'r le_rfl)

end SD8

end CFSG.GH74.Generic.BProg.B3
