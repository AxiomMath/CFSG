module

public import CFSG.Fischer.Classification.PartII.O2Count
public import CFSG.Fischer.Classification.PartII.O2Bridge

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin LocalR3 CFSG.Fischer.Classification.Unitary
open CFSG.ClassicalGroups.Unitary

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] def O2MuSectionInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 2 (LocalQuotient D d) →
      ∀ c ∈ D, c * d ≠ d * c →
        LocalU.TwinFree (LocalClass D d) (muSet D d c) ∧
          LocalU.MeetsTwins (LocalClass D d) (muSet D d c)

@[expose] def O2TwinFourInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), StatementBelow (Nat.card G) → Hyp G D →
    NonabelianCommutator G → ¬ IsSymplecticType D →
    ∀ d ∈ D, (LocalClass D d).Nonempty → HasNormalPSubgroup 2 (LocalQuotient D d) →
      ∀ a ∈ LocalClass D d, {b | LocalU.IsTwin (LocalClass D d) a b}.ncard = 4

namespace O2Mod

variable {H : Type} [Group H] {E μ : Set H}

theorem IsTwinSection.ncard_not_commute (hμ : IsTwinSection E μ) (hP : Pair H E)
    (h4 : ∀ a ∈ E, (twinClass E a).ncard = 4) {e₀ : H} (he₀ : e₀ ∈ E) :
    {f | f ∈ E ∧ f * e₀ ≠ e₀ * f}.ncard = 4 * {s | s ∈ μ ∧ s * e₀ ≠ e₀ * s}.ncard := by
  have := Pair.finite hP
  rw [O2Bridge.ncard_eq_four_mul hμ h4 (S := {f | f ∈ E ∧ f * e₀ ≠ e₀ * f})
    (fun f hf => hf.1) fun a ha b hab => ⟨hab.2.1, not_commute_of_isTwin hab he₀ ha.2⟩]
  congr 2
  ext s
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hμ.subset h.1, h.2⟩, h.1⟩⟩

end O2Mod

open O2Mod

theorem classicalConclusion_of_twins {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : NonabelianCommutator G) {d : G} (hd : d ∈ D)
    (hsec : ∀ c ∈ D, c * d ≠ d * c → LocalU.TwinFree (LocalClass D d) (muSet D d c) ∧
      LocalU.MeetsTwins (LocalClass D d) (muSet D d c))
    (h4 : ∀ a ∈ LocalClass D d, {b | LocalU.IsTwin (LocalClass D d) a b}.ncard = 4) :
    ClassicalConclusion G D := by
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have hfin := Pair.finite hP
  have hPH : Pair (LocalQuotient D d) (LocalImages D d) := Pair.pair_localQuotient hP hZ hS hna hd
  have hZH : Subgroup.center (LocalQuotient D d) = ⊥ := Pair.center_localQuotient hP hZ hS hd
  have hfinH := Pair.finite hPH
  have hi : Function.Injective (starImage D d) := Pair.starImage_injective_of_simple hP hZ hS hd
  have hch := Pair.isChart_lqMap hP hi
  obtain ⟨x, hx, hxd⟩ : ∃ x ∈ D, x * d ≠ d * x := by
    by_contra! h
    have hc : d ∈ Subgroup.center G := (Pair.mem_center_iff hP).2 fun e he => h e he
    rw [hZ, Subgroup.mem_bot] at hc
    exact Pair.ne_one hP hd hc
  have hsecH : ∀ c ∈ D, c * d ≠ d * c →
      IsTwinSection (LocalImages D d) (lqMap D d '' muSet D d c) := fun c hc hcd =>
    O2Bridge.isTwinSection_image hP hZ hS hd (hsec c hc hcd).1 (hsec c hc hcd).2
  have hμ := hsecH x hx hxd
  have h4H := O2Bridge.ncard_twinClass_image hP hZ hS hd h4
  obtain ⟨N, ⟨C⟩⟩ := hμ.exists_coords hPH h4H
  have hN2 : 2 ≤ N := C.two_le hZH
  have hN1 : 1 ≤ N := by omega
  have hm : 4 ≤ N + 2 := by omega
  have hmuS : muSet D d x ⊆ LocalClass D d := fun s hs => hs.1
  have hμcard : (lqMap D d '' muSet D d x).ncard = (muSet D d x).ncard :=
    (hch.injOn.mono hmuS).ncard_image
  have hEcard : (LocalImages D d).ncard = (LocalClass D d).ncard := by
    rw [← hch.image_eq, hch.injOn.ncard_image]
  have hE4 : (LocalImages D d).ncard = 4 * (lqMap D d '' muSet D d x).ncard := by
    rw [O2Bridge.ncard_eq_four_mul hμ h4H subset_rfl fun a _ b hab => hab.2.1,
      Set.inter_eq_right.2 hμ.subset]
  have hμpos : 0 < (lqMap D d '' muSet D d x).ncard := by
    obtain ⟨e, he⟩ := Pair.nonempty hPH
    obtain ⟨s, hs, -⟩ := hμ.exists_isTwin e he
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨s, hs⟩
  have hcount : ∀ e ∈ LocalClass D d, {c | c ∈ D ∧ c * d ≠ d * c}.ncard =
      16 * {s | s ∈ lqMap D d '' muSet D d x ∧ s * lqMap D d e ≠ lqMap D d e * s}.ncard := by
    intro e he
    have h1 := O2Bridge.ncard_far_mul_ncard_muSet hH hna hd he hx hxd
    have hF : {f | f ∈ LocalClass D d ∧ f * e ≠ e * f}.ncard =
        {f | f ∈ LocalImages D d ∧ f * lqMap D d e ≠ lqMap D d e * f}.ncard := by
      have himg : lqMap D d '' {f | f ∈ LocalClass D d ∧ f * e ≠ e * f} =
          {f | f ∈ LocalImages D d ∧ f * lqMap D d e ≠ lqMap D d e * f} := by
        ext q
        constructor
        · rintro ⟨f, ⟨hf, hfe⟩, rfl⟩
          exact ⟨hch.mem hf, fun h => hfe ((hch.comm_iff f hf e he).2 h)⟩
        · rintro ⟨hq, hqe⟩
          obtain ⟨f, hf, rfl⟩ := hch.exists_eq hq
          exact ⟨f, ⟨hf, fun h => hqe ((hch.comm_iff f hf e he).1 h)⟩, rfl⟩
      rw [← himg, (hch.injOn.mono fun f hf => hf.1).ncard_image]
    rw [hF, hμ.ncard_not_commute hPH h4H (hch.mem he), ← hμcard, ← hEcard, hE4] at h1
    have h2 : {c | c ∈ D ∧ c * d ≠ d * c}.ncard * (lqMap D d '' muSet D d x).ncard =
        (16 * {s | s ∈ lqMap D d '' muSet D d x ∧ s * lqMap D d e ≠ lqMap D d e * s}.ncard) *
          (lqMap D d '' muSet D d x).ncard := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hμpos h2
  have h8 : 4 ^ N / 8 * 8 = 4 ^ N := by
    refine Nat.div_mul_cancel ?_
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
    rw [pow_add]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨e₀, he₀⟩ := Pair.localClass_nonempty hP hS hna hd
  have hle : {c | c ∈ D ∧ c * d ≠ d * c}.ncard ≤ 2 * 4 ^ N := by
    rw [hcount e₀ he₀]
    have := C.ncard_sec_not_commute_le hZH (hch.mem he₀)
    omega
  have hconj : ∀ v : Fin N → K, ∃ x' ∈ D, x' * d ≠ d * x' ∧
      lqMap D d '' muSet D d x' = C.transSet v := by
    intro v
    obtain ⟨h, hh⟩ := C.exists_transSet_eq_conj hZH v
    obtain ⟨x', hx', hx'd, he⟩ := LocalU.exists_image_conj hP (MulEquiv.refl _) h hx hxd
    simp only [MulEquiv.coe_refl, Function.id_comp] at he
    exact ⟨x', hx', hx'd, he.symm.trans hh.symm⟩
  choose xf hxfD hxfd hxfeq using hconj
  have hinj : Function.Injective fun v => muSet D d (xf v) := by
    intro v w hvw
    apply C.transSet_injective
    rw [← hxfeq, ← hxfeq]
    exact congrArg (lqMap D d '' ·) hvw
  have hM : 4 ^ N ≤ ((fun c => muSet D d c) '' {c | c ∈ D ∧ c * d ≠ d * c}).ncard := by
    have hsub : Set.range (fun v => muSet D d (xf v)) ⊆
        (fun c => muSet D d c) '' {c | c ∈ D ∧ c * d ≠ d * c} := by
      rintro _ ⟨v, rfl⟩
      exact ⟨xf v, ⟨hxfD v, hxfd v⟩, rfl⟩
    have hcard := Set.ncard_le_ncard hsub ((Set.toFinite _).image _)
    rw [Set.ncard_range_of_injective hinj, Nat.card_fun, Nat.card_fin, card_K] at hcard
    norm_num at hcard
    exact hcard
  have hfib := O2Bridge.muSet_fib_of_ncard_le hP hd hM hle
  have hAeq := O2Bridge.ncard_far_eq_of_ncard_le hP hd hM hle
  have hall : ∀ e ∈ LocalImages D d,
      {s | s ∈ lqMap D d '' muSet D d x ∧ s * e ≠ e * s}.ncard = 4 ^ N / 8 := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := hch.exists_eq hq
    have := hcount e he
    omega
  have hiso : ∀ z : Fin N → K, z ≠ 0 → herm frob z z = 0 →
      ∃ s ∈ lqMap D d '' muSet D d x, ∃ c : K, z = c • C.cv s := fun z hz0 hz =>
    C.exists_eq_smul_cv hZH hall hz0 hz
  have hTE : TripleAt D d := O2Bridge.tripleAt_of_sections hP hZ hS hd hsecH hfib
  let φ₀ : LocalClass D d → LocalClass (DU (N + 2)) (tqU (v₀ N)) := fun f =>
    ⟨C.toModel (lqMap D d f), C.toModel_mem hZH hN1 (hch.mem f.2)⟩
  have hφ₀ : Function.Bijective φ₀ := by
    refine ⟨fun f g hfg => Subtype.ext (hch.injOn f.2 g.2
      (C.toModel_injOn hZH hN1 (hch.mem f.2) (hch.mem g.2) (congrArg Subtype.val hfg))),
      fun q => ?_⟩
    obtain ⟨e, he, hq⟩ := C.exists_toModel_eq hZH hiso q.2
    obtain ⟨f, hf, rfl⟩ := hch.exists_eq he
    exact ⟨⟨f, hf⟩, Subtype.ext hq⟩
  let φ := Equiv.ofBijective φ₀ hφ₀
  have hφ : ∀ f : LocalClass D d, (φ f : U2 (N + 2)) = C.toModel (lqMap D d f) := fun _ => rfl
  have hcomm : ∀ f g : LocalClass D d,
      (f : G) * g = g * f ↔ (φ f : U2 (N + 2)) * φ g = φ g * φ f := by
    intro f g
    rw [hφ, hφ, C.toModel_commute_iff hZH hN1 (hch.mem f.2) (hch.mem g.2)]
    exact hch.comm_iff f f.2 g g.2
  have htau : ∀ (f g : LocalClass D d) (h : (f : G) * g * f ∈ LocalClass D d),
      (φ ⟨_, h⟩ : U2 (N + 2)) = φ f * φ g * φ f := by
    intro f g h
    rw [hφ, hφ, hφ]
    show C.toModel (lqMap D d ((f : G) * g * f)) = _
    rw [lqMap_mul_mul f.2 g.2, C.toModel_mul_mul hZH (hch.mem f.2) (hch.mem g.2)]
  have hx' : tqU (u₀ N) ∈ DU (N + 2) := tqU_mem_DU u₀_ne_zero herm_u₀_u₀
  have hd' : tqU (v₀ N) ∈ DU (N + 2) := tqU_mem_DU v₀_ne_zero herm_v₀_v₀
  have hxd' : tqU (u₀ N) * tqU (v₀ N) ≠ tqU (v₀ N) * tqU (u₀ N) := fun h => by
    have := (tqU_commute_iff (by omega) u₀_ne_zero herm_u₀_u₀ v₀_ne_zero herm_v₀_v₀).1 h
    rw [herm_u₀_v₀] at this
    exact one_ne_zero this
  have hmu : starMap φ (muSet D d x) = muSet (DU (N + 2)) (tqU (v₀ N)) (tqU (u₀ N)) := by
    rw [← C.image_toModel_sec hZH hiso]
    ext y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨lqMap D d f, ⟨f, hf, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨⟨f, hmuS hf⟩, hf, rfl⟩
  have htrE := O2Bridge.exists_localGroup_conj_muSet hP hZ hS hna hd hx hxd
  obtain ⟨r, hr⟩ := coverRigid_DU hm hd'
  obtain ⟨ψ, hψ, -, -⟩ := Unitary.Pair.exists_mulEquiv_of_muSet_tripleAt hP (pair_DU hm) hZ
    (center_U2 hm) hTE (tripleProperty_DU hm) hd hd' (localClass_DU_nonempty hm hd') φ hcomm
    htau hx hxd hx' hxd' hmu htrE hr
  exact classicalConclusion_of_mulEquiv_U2 hm ψ hψ

theorem o2InputI_of_twins (h1 : O2MuSectionInput) (h2 : O2TwinFourInput) : O2InputI := by
  intro G _ D hb hH hna hs d hd hne hN
  exact classicalConclusion_of_twins hH hna hd (h1 G D hb hH hna hs d hd hne hN)
    (h2 G D hb hH hna hs d hd hne hN)

end CFSG.Fischer.Classification
