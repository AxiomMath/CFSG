module

public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarComp
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.Goldschmidt.Final
import CFSG.Goldschmidt.Steps.IHConseq
import CFSG.Goldschmidt.Steps.Ind

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores CFSG.ABGLocalTools

namespace Qbar

section CompCentralizer

variable (Y : Type) [Group Y]

@[expose] def compCentralizer : Subgroup Y :=
  ⨅ K : ComponentIndex Y, centralizer (K.1 : Set Y)

variable {Y}

theorem mem_compCentralizer {g : Y} :
    g ∈ compCentralizer Y ↔ ∀ K : ComponentIndex Y, ∀ y ∈ K.1, y * g = g * y := by
  simp only [compCentralizer, mem_iInf, mem_centralizer_iff]
  exact Iff.rfl

theorem apply_mem_compCentralizer (e : MulAut Y) {g : Y} (hg : g ∈ compCentralizer Y) :
    e g ∈ compCentralizer Y := by
  rw [mem_compCentralizer] at hg ⊢
  intro K y hy
  have hK' : IsComponent (K.1.map e.symm.toMonoidHom) := isComponent_map_mulEquiv e.symm K.2
  have h1 := hg ⟨_, hK'⟩ (e.symm y) ⟨y, hy, rfl⟩
  have h2 := congrArg e h1
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2

end CompCentralizer

theorem natCard_map_le {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    [Finite K] : Nat.card (K.map f) ≤ Nat.card K :=
  Nat.card_le_card_of_surjective (fun x : K => (⟨f x, x, x.2, rfl⟩ : K.map f))
    (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)

end Qbar

open Qbar

theorem qbarNoComponentOfAction :
    QbarNoComponentOfAction := by
  intro G _ _ z Q T N hz hT hQT hzQ hQ7 hQab hcl hNC hNQ hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold QbarNoComponent QbarNoComponentIn qbarClosure
  set C := centralizer ({z} : Set G) with hCdef
  obtain ⟨T₀, hT₀⟩ := hT
  have hTC : T ≤ C := hT₀ ▸ map_subtype_le _
  have hQC : Q ≤ C := hQT.trans hTC
  set Q' := Q.subgroupOf C with hQ'
  have hQ'T : Q' ≤ (T₀ : Subgroup C) := by
    intro x hx
    have hxS : (x : G) ∈ T := hQT (mem_subgroupOf.mp hx)
    rw [← hT₀] at hxS
    obtain ⟨y, hy, hyx⟩ := hxS
    rwa [← Subtype.ext hyx]
  have hcl' : ∀ x ∈ Q', ∀ h : C, h⁻¹ * x * h ∈ (T₀ : Subgroup C) → h⁻¹ * x * h ∈ Q' :=
    fun x hx h hh => by
      rw [mem_subgroupOf]
      refine hcl _ (mem_subgroupOf.mp hx) _ h.2 ?_
      rw [← hT₀]
      exact ⟨_, hh, rfl⟩
  have hQab' : ∀ x ∈ Q', ∀ y ∈ Q', x * y * x⁻¹ * y⁻¹ ∈ zpowers (zC z) := fun x hx y hy => by
    rw [mem_zpowers_zC]
    exact hQab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy)
  set Zc := zpowers (zC z) with hZc
  set π₀ := QuotientGroup.mk' Zc with hπ₀
  have hπ₀s : Function.Surjective π₀ := QuotientGroup.mk'_surjective Zc
  have hker : π₀.ker = Zc := QuotientGroup.ker_mk' Zc
  have hZcQ' : Zc ≤ Q' := zpowers_le.mpr (mem_subgroupOf.mpr hzQ)
  have hZcT : Zc ≤ (T₀ : Subgroup C) := hZcQ'.trans hQ'T
  set Sb : Sylow 2 (C ⧸ Zc) := T₀.mapSurjective hπ₀s with hSb
  have hSbcoe : (Sb : Subgroup (C ⧸ Zc)) = (T₀ : Subgroup C).map π₀ :=
    Sylow.coe_mapSurjective _ _
  set Qb := Q'.map π₀ with hQb
  have hQbS : Qb ≤ Sb := by
    rw [hSbcoe]
    exact map_mono hQ'T
  have hQbab : IsMulCommutative Qb := by
    refine isMulCommutative_iff_of_setLike.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have := hQab' _ (Q'.inv_mem hb) _ (Q'.inv_mem ha)
    simpa [mul_assoc] using this
  have hQbcl : fusionStronglyClosed (Qb : Set (C ⧸ Zc)) (Sb : Subgroup (C ⧸ Zc)) := by
    rintro _ ⟨a, ha, rfl⟩ g hg
    obtain ⟨h, rfl⟩ := hπ₀s g
    rw [← map_inv, ← map_mul, ← map_mul] at hg ⊢
    rw [hSbcoe] at hg
    obtain ⟨s, hs, hse⟩ := hg
    have hmem : h⁻¹ * a * h ∈ (T₀ : Subgroup C) := by
      have h1 : s⁻¹ * (h⁻¹ * a * h) ∈ Zc := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
      have h2 := (T₀ : Subgroup C).mul_mem hs (hZcT h1)
      simpa [mul_assoc] using h2
    exact ⟨_, hcl' a ha h hmem, rfl⟩
  have hIH : IH (Nat.card (C ⧸ Zc) + 1) := fun Z _ _ _ => coreStatement_iff.mp coreStatement Z
  have hTsyl : fusionIsSylowIn 2 (Sb : Subgroup (C ⧸ Zc)) ⊤ :=
    ⟨le_top, Sb.isPGroup', fun P _ hP hTP => Sb.is_maximal' hP hTP⟩
  obtain ⟨hConc, -, -, hC3, -⟩ := N16_of N1 _ hIH (C ⧸ Zc) Sb Qb ⊤ Sb hQbS hQbab hQbcl hQbS hTsyl
    (by rw [card_top]; omega)
  set M : Subgroup (C ⧸ Zc) := normalClosureIn ⊤ Qb with hMdef
  have hMeq : M = normalClosure (Qb : Set (C ⧸ Zc)) := by
    rw [hMdef, normalClosureIn, map_normalClosure _ _ (fun y => ⟨⟨y, mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, mem_top y⟩, mem_subgroupOf.2 hy, rfl⟩
  suffices hgoal : goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) = ⊥ by
    have e : ∀ M₁ M₂ : Subgroup (C ⧸ Zc), M₁ = M₂ →
        goldschmidtLayer (↥M₁ ⧸ goldschmidtOddCore ↥M₁) = ⊥ →
        goldschmidtLayer (↥M₂ ⧸ goldschmidtOddCore ↥M₂) = ⊥ := by
      rintro M₁ M₂ rfl h
      exact h
    exact e M _ hMeq hgoal
  have hMn : M.Normal := by
    rw [hMeq]
    exact normalClosure_normal
  have hQbM : Qb ≤ M := by
    rw [hMeq]
    exact le_normalClosure
  set π := QuotientGroup.mk' (goldschmidtOddCore M) with hπ
  obtain ⟨PM, hPM⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Sb hMn.isSubnormal
  have hPMeq : (PM : Subgroup M) = (Sb : Subgroup (C ⧸ Zc)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hPM, subgroupOf_map_subtype]
  have hQbPM : Qb.subgroupOf M ≤ (PM : Subgroup M) := by
    rw [hPMeq]
    exact fun x hx => mem_subgroupOf.2 (hQbS (mem_subgroupOf.1 hx))
  have hclM := stronglyClosed_subgroupOf Sb hQbcl hQbM PM hQbPM
  obtain ⟨Sbar, hSbar, hclbar⟩ := CFSG.ShultStronglyClosedTI.quotient_stronglyClosed PM
    (Qb.subgroupOf M) (goldschmidtOddCore M) hQbPM hclM
  set A := (Qb.subgroupOf M).map π with hA
  have hASbar : A ≤ Sbar := by
    rw [hSbar]
    exact map_mono hQbPM
  have hAab : IsMulCommutative A := isMulCommutative_map (isMulCommutative_subgroupOf hQbab M) π
  have hO : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ :=
    goldschmidtOddCore_quotient_eq_bot M
  have hSbarT : (Sbar : Subgroup (M ⧸ goldschmidtOddCore M)) = barOf M Sb := by
    rw [hSbar, hPMeq]
    rfl
  have hopen : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), IsComponentOf K.1 ⊤ :=
    fun K => (CFSG.isComponent_iff_open K.1).mp K.2
  have htype : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M),
      goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K => hConc.2.2 K.1 (hopen K)
  have hind : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), InducesOmega1 A K.1 Sbar :=
    fun K => by
      rw [hSbarT]
      exact hC3 K.1 (hopen K)
  have hcover : ∀ K : ComponentIndex (M ⧸ goldschmidtOddCore M), ∀ a ∈ A, ∃ x ∈ A ⊓ K.1,
      ∀ y ∈ K.1, a⁻¹ * y * a = x⁻¹ * y * x :=
    fun K => N17_of N11b _ Sbar A K.1 hASbar hAab hclbar hO (hopen K) (htype K) (hind K)
  have hcard : Nat.card A < 4 ^ 5 := by
    have h1 : Nat.card A ≤ Nat.card (Qb.subgroupOf M) := natCard_map_le π _
    have h2 : Nat.card (Qb.subgroupOf M) = Nat.card Qb :=
      Nat.card_congr (subgroupOfEquivOfLe hQbM).toEquiv
    have h3 : Nat.card Qb ≤ Nat.card Q' := natCard_map_le π₀ Q'
    have h4 : Nat.card Q' = Nat.card Q := Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv
    have h5 : Nat.card Q ≤ 2 ^ 9 := by
      rcases hQ7 with h | h
      · rw [h]
        norm_num
      · exact h.le
    have h6 : (2 : ℕ) ^ 9 < 4 ^ 5 := by norm_num
    omega
  have hιM : ∀ x : Q, π₀ (inclusion hQC x) ∈ M := fun x =>
    hQbM (mem_map.mpr ⟨inclusion hQC x, mem_subgroupOf.mpr x.2, rfl⟩)
  set ι : Q →* M ⧸ goldschmidtOddCore M :=
    π.comp ((π₀.comp (inclusion hQC)).codRestrict M hιM) with hι
  have hιA : ∀ x : Q, ι x ∈ A := by
    intro x
    refine mem_map.mpr ⟨⟨π₀ (inclusion hQC x), hιM x⟩, ?_, rfl⟩
    rw [mem_subgroupOf]
    exact mem_map.mpr ⟨inclusion hQC x, mem_subgroupOf.mpr x.2, rfl⟩
  have hιsurj : ∀ a ∈ A, ∃ x : Q, ι x = a := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : C ⧸ Zc) ∈ Qb := hw
    obtain ⟨c, hc, hcw⟩ := mem_map.mp hw'
    refine ⟨⟨c, mem_subgroupOf.mp hc⟩, ?_⟩
    rw [hι, MonoidHom.comp_apply]
    exact congrArg π (Subtype.ext hcw)
  set σ : N →* MulAut (M ⧸ goldschmidtOddCore M) :=
    (MonoidHom.mk' (Asc76X.conjQuot hMn) (Asc76X.conjQuot_mul hMn)).comp
      (π₀.comp (inclusion hNC)) with hσ
  have hNQ' : ∀ (n : N) (x : Q), (n : G) * x * (n : G)⁻¹ ∈ Q := fun n x =>
    (mem_normalizer_iff.mp (hNQ n.2) x).mp x.2
  have hequiv : ∀ (n : N) (x : Q), σ n (ι x) = ι ⟨(n : G) * x * (n : G)⁻¹, hNQ' n x⟩ :=
    fun n x => rfl
  have hσA : ∀ n, ∀ a ∈ A, σ n a ∈ A := by
    intro n a ha
    obtain ⟨x, rfl⟩ := hιsurj a ha
    rw [hequiv]
    exact hιA _
  by_contra hne
  obtain ⟨K₀, hK₀⟩ : ∃ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [goldschmidtLayer, sSup_eq_bot]
    intro K hK
    exact absurd hK (hcon K)
  have hK₀' : IsComponent K₀ := (CFSG.isComponent_iff_open K₀).mpr hK₀
  set B : Subgroup G :=
    ((compCentralizer (M ⧸ goldschmidtOddCore M)).comap ι).map Q.subtype with hB
  have hmemB : ∀ x : Q, (x : G) ∈ B ↔ ι x ∈ compCentralizer (M ⧸ goldschmidtOddCore M) := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hBQ : B ≤ Q := map_subtype_le _
  have hzB : zpowers z ≤ B := by
    rw [zpowers_le]
    have h1 : (π₀.comp (inclusion hQC)).codRestrict M hιM ⟨z, hzQ⟩ = 1 := by
      apply Subtype.ext
      change π₀ (inclusion hQC ⟨z, hzQ⟩) = 1
      rw [hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_zpowers (zC z)
    have h2 : ι ⟨z, hzQ⟩ = 1 := by
      rw [hι, MonoidHom.comp_apply, h1, map_one]
    exact (hmemB ⟨z, hzQ⟩).mpr (by rw [h2]; exact one_mem _)
  have hBlt : B < Q := by
    refine lt_of_le_of_ne hBQ fun hBQeq => ?_
    obtain ⟨a, ha, y, hy, hay⟩ :=
      exists_mem_conj_ne Sbar hK₀' (htype ⟨K₀, hK₀'⟩) (hind ⟨K₀, hK₀'⟩)
    obtain ⟨x, rfl⟩ := hιsurj a ha
    have hxB : (x : G) ∈ B := by
      rw [hBQeq]
      exact x.2
    have h1 := (mem_compCentralizer.mp ((hmemB x).mp hxB)) ⟨K₀, hK₀'⟩ y hy
    apply hay
    rw [mul_assoc, h1, inv_mul_cancel_left]
  have hNB : N ≤ normalizer (B : Set G) := by
    intro n hn
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxQ := hBQ hx
      refine (hmemB ⟨_, hNQ' ⟨n, hn⟩ ⟨x, hxQ⟩⟩).mpr ?_
      rw [← hequiv ⟨n, hn⟩ ⟨x, hxQ⟩]
      exact apply_mem_compCentralizer (σ ⟨n, hn⟩) ((hmemB ⟨x, hxQ⟩).mp hx)
    · intro hx
      have hxQ' := hBQ hx
      have hxQ : x ∈ Q := (mem_normalizer_iff.mp (hNQ hn) x).mpr hxQ'
      refine (hmemB ⟨x, hxQ⟩).mpr ?_
      have h1 := (hmemB ⟨_, hxQ'⟩).mp hx
      rw [← hequiv ⟨n, hn⟩ ⟨x, hxQ⟩] at h1
      have h2 := apply_mem_compCentralizer (σ ⟨n, hn⟩)⁻¹ h1
      rwa [MulAut.inv_apply_self] at h2
  obtain ⟨m, hm⟩ := exists_derivedSeries_sameOn_components Sbar htype hind hcover hcard σ hσA
  obtain ⟨k, hk, x, hx, hkx⟩ := hN B hzB hBlt hNB m
  obtain ⟨k', hk', rfl⟩ := hk
  apply hkx
  have hwQ : (N.subtype k')⁻¹ * x * N.subtype k' * x⁻¹ ∈ Q :=
    Q.mul_mem (by simpa using hNQ' k'⁻¹ ⟨x, hx⟩) (Q.inv_mem hx)
  have hιw : ι ⟨_, hwQ⟩ = σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ := by
    have e1 : (⟨_, hwQ⟩ : Q) = ⟨_, hNQ' k'⁻¹ ⟨x, hx⟩⟩ * (⟨x, hx⟩ : Q)⁻¹ :=
      Subtype.ext (by simp)
    rw [e1, map_mul, map_inv, ← hequiv]
  refine (hmemB ⟨_, hwQ⟩).mpr ?_
  rw [hιw, mem_compCentralizer]
  intro K y hy
  have h1 := hm k'⁻¹ (inv_mem hk') (ι ⟨x, hx⟩) (hιA _) K y hy
  calc y * (σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹) =
      σ k'⁻¹ (ι ⟨x, hx⟩) * ((σ k'⁻¹ (ι ⟨x, hx⟩))⁻¹ * y * σ k'⁻¹ (ι ⟨x, hx⟩)) *
        (ι ⟨x, hx⟩)⁻¹ := by group
    _ = σ k'⁻¹ (ι ⟨x, hx⟩) * ((ι ⟨x, hx⟩)⁻¹ * y * ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ := by rw [h1]
    _ = σ k'⁻¹ (ι ⟨x, hx⟩) * (ι ⟨x, hx⟩)⁻¹ * y := by group

end CFSG.ComponentClassification.AS81
