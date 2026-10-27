module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7TransL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Action

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

section Equiv

variable {K A B : Type*} [Group K] [Group A] [Group B] (α : K →* A) (β : K →* B)
  (hα : Function.Surjective α) (hβ : Function.Surjective β) (hker : α.ker = β.ker)

noncomputable def equivOfKerEq : A ≃* B :=
  (QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβ))

theorem equivOfKerEq_apply (k : K) : equivOfKerEq α β hα hβ hker (α k) = β k := by
  simp only [equivOfKerEq, MulEquiv.trans_apply]
  rw [show (QuotientGroup.quotientKerEquivOfSurjective α hα).symm (α k) = (k : K ⧸ α.ker) by
    rw [MulEquiv.symm_apply_eq]; rfl]
  rfl

end Equiv

theorem isOuterDiagonalPSL2_conj {Y Y' : Type} [Group Y] [Group Y'] (ι : Y' ≃* Y)
    {φ : Y ≃* Y} (hφ : IsOuterDiagonalPSL2 φ) : IsOuterDiagonalPSL2 ((ι.trans φ).trans ι.symm) := by
  obtain ⟨⟨F, hF, hFin, e, A, hA⟩, hout⟩ := hφ
  refine ⟨⟨F, hF, hFin, ι.trans e, A, fun M N hMN => ?_⟩, ?_⟩
  · have := hA M N hMN
    simpa [MulEquiv.trans_apply] using this
  · rintro ⟨g, hg⟩
    apply hout
    refine ⟨ι g, fun y => ?_⟩
    have h1 := hg (ι.symm y)
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg ι h1
    simpa using h2


section J0

variable {X : Type} [Group X] [Finite X] {J L J₀ : Subgroup X}

noncomputable abbrev toJbar (hJ0J : J₀ ≤ J) : ↥J₀ →* J ⧸ pPrimeCore 2 J :=
  (QuotientGroup.mk' (pPrimeCore 2 J)).comp (inclusion hJ0J)

noncomputable abbrev toLbar (hJ0L : J₀ ≤ L) : ↥J₀ →* L ⧸ pPrimeCore 2 L :=
  (QuotientGroup.mk' (pPrimeCore 2 L)).comp (inclusion hJ0L)

omit [Finite X] in
theorem toJbar_surjective (hJ0J : J₀ ≤ J) (hsup : J₀ ⊔ (pPrimeCore 2 J).map J.subtype = J) :
    Function.Surjective (toJbar hJ0J) := by
  have hsup' : J₀.subgroupOf J ⊔ pPrimeCore 2 ↥J = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hJ0J, hsup, ← MonoidHom.range_eq_map,
      range_subtype]
  intro x
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
  have hj : j ∈ ((J₀.subgroupOf J ⊔ pPrimeCore 2 ↥J : Subgroup ↥J) : Set ↥J) := by
    rw [hsup']; exact mem_top j
  rw [mul_normal] at hj
  obtain ⟨j₀, hj₀, o, ho, rfl⟩ := Set.mem_mul.mp hj
  refine ⟨⟨j₀, hj₀⟩, ?_⟩
  change ((⟨(j₀ : X), _⟩ : ↥J) : J ⧸ pPrimeCore 2 J) = ((j₀ * o : ↥J) : J ⧸ pPrimeCore 2 J)
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff o).mpr ho, mul_one]

omit [Finite X] in
theorem ker_toJbar (hJ0J : J₀ ≤ J)
    (hcore : (pPrimeCore 2 J₀).map J₀.subtype = J₀ ⊓ (pPrimeCore 2 J).map J.subtype) :
    (toJbar hJ0J).ker = pPrimeCore 2 ↥J₀ := by
  ext j
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hj
    have h1 : (j : X) ∈ (pPrimeCore 2 J₀).map J₀.subtype := by
      rw [hcore]
      exact mem_inf.mpr ⟨j.2, ⟨_, hj, rfl⟩⟩
    obtain ⟨k, hk, hkj⟩ := mem_map.mp h1
    rwa [← Subtype.ext hkj]
  · intro hj
    have h1 : (j : X) ∈ J₀ ⊓ (pPrimeCore 2 J).map J.subtype := by
      rw [← hcore]; exact mem_map_of_mem _ hj
    obtain ⟨k, hk, hkj⟩ := mem_map.mp (mem_inf.mp h1).2
    have : k = inclusion hJ0J j := Subtype.ext hkj
    rwa [← this]

theorem ker_toLbar (hJ0L : J₀ ≤ L) (hO : pPrimeCore 2 ↥(toLbar hJ0L).range = ⊥) :
    (toLbar hJ0L).ker = pPrimeCore 2 ↥J₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    refine le_sSup ⟨inferInstance, ?_⟩
    let e : ↥(toLbar hJ0L).ker →* ↥(pPrimeCore 2 ↥L) :=
      { toFun := fun k => ⟨inclusion hJ0L k, by
          have := k.2
          rwa [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq_one_iff] at this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have he : Function.Injective e := by
      intro u v huv
      have := congrArg (fun w : ↥(pPrimeCore 2 ↥L) => ((w : ↥L) : X)) huv
      exact Subtype.ext (Subtype.ext this)
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective e he)
      pPrimeCore_coprime_card
  ·
    intro j hj
    have h1 : (toLbar hJ0L).rangeRestrict j ∈ pPrimeCore 2 ↥(toLbar hJ0L).range := by
      have hle : (pPrimeCore 2 ↥J₀).map (toLbar hJ0L).rangeRestrict ≤
          pPrimeCore 2 ↥(toLbar hJ0L).range := by
        refine le_sSup ⟨(inferInstance : (pPrimeCore 2 ↥J₀).Normal).map _
          (toLbar hJ0L).rangeRestrict_surjective, ?_⟩
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) pPrimeCore_coprime_card
      exact hle (mem_map_of_mem _ hj)
    rw [hO, mem_bot] at h1
    have := congrArg Subtype.val h1
    exact this

variable (hJ0J : J₀ ≤ J) (hJ0L : J₀ ≤ L) (hsup : J₀ ⊔ (pPrimeCore 2 J).map J.subtype = J)
  (hcore : (pPrimeCore 2 J₀).map J₀.subtype = J₀ ⊓ (pPrimeCore 2 J).map J.subtype)
  (hO : pPrimeCore 2 ↥(toLbar hJ0L).range = ⊥)

noncomputable abbrev iota : J ⧸ pPrimeCore 2 J ≃* ↥(toLbar hJ0L).range :=
  equivOfKerEq (toJbar hJ0J) (toLbar hJ0L).rangeRestrict (toJbar_surjective hJ0J hsup)
    (toLbar hJ0L).rangeRestrict_surjective
    (by rw [ker_toJbar hJ0J hcore, MonoidHom.ker_rangeRestrict, ker_toLbar hJ0L hO])

theorem iota_apply (j : ↥J₀) :
    iota hJ0J hJ0L hsup hcore hO (toJbar hJ0J j) = (toLbar hJ0L).rangeRestrict j :=
  equivOfKerEq_apply _ _ _ _ _ j


abbrev conjJ0 {s : X} (hsJ0 : s ∈ normalizer (J₀ : Set X)) (j : ↥J₀) : ↥J₀ :=
  J₀.normalizerMonoidHom ⟨s, hsJ0⟩ j

omit [Finite X] in
theorem toLbar_conjJ0 {s : X} (hsJ0 : s ∈ normalizer (J₀ : Set X)) (hsL : s ∈ L) (j : ↥J₀) :
    toLbar hJ0L (conjJ0 hsJ0 j) = QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩ * toLbar hJ0L j *
      (QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩)⁻¹ := by
  change QuotientGroup.mk' (pPrimeCore 2 L) (inclusion hJ0L (conjJ0 hsJ0 j)) =
    QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩ * QuotientGroup.mk' (pPrimeCore 2 L)
      (inclusion hJ0L j) * (QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1

omit [Finite X] in
theorem mk_mem_normalizer_range {s : X} (hsJ0 : s ∈ normalizer (J₀ : Set X)) (hsL : s ∈ L) :
    QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩ ∈
      normalizer ((toLbar hJ0L).range : Set (L ⧸ pPrimeCore 2 L)) := by
  have key : ∀ {u : X} (huJ0 : u ∈ normalizer (J₀ : Set X)) (huL : u ∈ L),
      ∀ m ∈ (toLbar hJ0L).range, QuotientGroup.mk' (pPrimeCore 2 L) ⟨u, huL⟩ * m *
        (QuotientGroup.mk' (pPrimeCore 2 L) ⟨u, huL⟩)⁻¹ ∈ (toLbar hJ0L).range := by
    rintro u huJ0 huL _ ⟨j, rfl⟩
    rw [← toLbar_conjJ0 hJ0L huJ0 huL]
    exact ⟨_, rfl⟩
  rw [mem_normalizer_iff]
  intro m
  refine ⟨key hsJ0 hsL m, fun hm => ?_⟩
  have := key (inv_mem hsJ0) (inv_mem hsL) _ hm
  rwa [show (⟨s⁻¹, inv_mem hsL⟩ : ↥L) = (⟨s, hsL⟩ : ↥L)⁻¹ from rfl, map_inv, inv_inv,
    show (QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩)⁻¹ * (QuotientGroup.mk' (pPrimeCore 2 L)
      ⟨s, hsL⟩ * m * (QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩)⁻¹) *
      QuotientGroup.mk' (pPrimeCore 2 L) ⟨s, hsL⟩ = m by group] at this

theorem oddBarAction_eq_conj {s : X} (hsJ : s ∈ normalizer (J : Set X)) (hsL : s ∈ L)
    (hsJ0 : s ∈ normalizer (J₀ : Set X)) :
    Eight.oddBarAction J ⟨s, hsJ⟩ = ((iota hJ0J hJ0L hsup hcore hO).trans
      ((toLbar hJ0L).range.normalizerMonoidHom ⟨_, mk_mem_normalizer_range hJ0L hsJ0 hsL⟩)).trans
      (iota hJ0J hJ0L hsup hcore hO).symm := by
  ext x
  obtain ⟨j, rfl⟩ := toJbar_surjective hJ0J hsup x
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, iota_apply, eq_comm,
    MulEquiv.symm_apply_eq]
  have h1 : Eight.oddBarAction J ⟨s, hsJ⟩ (toJbar hJ0J j) = toJbar hJ0J (conjJ0 hsJ0 j) := by
    change Eight.oddBarAction J ⟨s, hsJ⟩ ((inclusion hJ0J j : ↥J) : J ⧸ pPrimeCore 2 J) = _
    rw [Eight.oddBarAction_apply_mk]
    congr 1
  rw [h1, iota_apply]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MonoidHom.coe_rangeRestrict,
    MonoidHom.coe_rangeRestrict, toLbar_conjJ0 hJ0L hsJ0 hsL]
end J0


section Outer

variable {X : Type} [Group X] [Finite X] {J₀ L : Subgroup X}

theorem IsSylowIn.subgroupOf {R Y L : Subgroup X} (hYL : Y ≤ L) (h : IsSylowIn R Y) :
    IsSylowIn (R.subgroupOf L) (Y.subgroupOf L) := by
  obtain ⟨hRY, R', hR'⟩ := h
  let e : ↥(Y.subgroupOf L) ≃* ↥Y := subgroupOfEquivOfLe hYL
  have hsurj : Function.Surjective (e.symm.toMonoidHom : ↥Y →* ↥(Y.subgroupOf L)) := by
    rw [MulEquiv.coe_toMonoidHom]; exact e.symm.surjective
  refine ⟨fun w hw => hRY hw, R'.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective, hR']
  ext w
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hw
    refine ⟨e w, hw, ?_⟩
    simp

omit [Finite X] in
theorem range_toLbar (hJ0L : J₀ ≤ L) :
    (toLbar hJ0L).range = (J₀.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 L)) := by
  rw [MonoidHom.range_comp, inclusion_range]

theorem exists_outer_of_cf (hComp : CFSp4Comp) (hOut : CFSp4Outer) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) {J L J₀ Y S : Subgroup X}
    (hLie : Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSp 2 p f)
    (hZJ : center (J ⧸ pPrimeCore 2 J) = ⊥) {t : X} (htL : t ∈ L) (ht : t * t = 1)
    (ht1 : t ≠ 1) (hJ0J : J₀ ≤ J) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y))
    (hsup : J₀ ⊔ (pPrimeCore 2 J).map J.subtype = J)
    (hcore : (pPrimeCore 2 J₀).map J₀.subtype = J₀ ⊓ (pPrimeCore 2 J).map J.subtype)
    (hSL : IsSylowIn (S ⊓ L) (L ⊓ centralizer ({t} : Set X)))
    (hSN : S ⊓ L ≤ normalizer (J : Set X) ⊓ normalizer (J₀ : Set X)) :
    ∃ s ∈ S ⊓ L, ∃ hs : s ∈ normalizer (J : Set X),
      IsOuterDiagonalPSL2 (Eight.oddBarAction J ⟨s, hs⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : ↥L := ⟨t, htL⟩ with ht'
  have ht'2 : t' * t' = 1 := Subtype.ext ht
  have ht'1 : t' ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf (centralizer ({t'} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({t'} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  rw [← range_toLbar hJ0L] at hMbt hMbpc
  have hO : pPrimeCore 2 ↥(toLbar hJ0L).range = ⊥ :=
    hComp _ p f hp hp2 hf hLie _ (orderOf_mk_eq_two ht'2 ht'1) _ hMbt hMbpc
  set ι := iota hJ0J hJ0L hsup hcore hO with hι
  have hZM : center ↥(toLbar hJ0L).range = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have h1 : ι.symm m ∈ center (J ⧸ pPrimeCore 2 J) := by
      rw [mem_center_iff]
      intro u
      apply ι.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (mem_center_iff.mp hm (ι u))
    rw [hZJ, mem_bot] at h1
    rw [mem_bot, ← ι.apply_symm_apply m, h1, map_one]
  have hSylL := hSL.subgroupOf (inf_le_left : L ⊓ centralizer ({t} : Set X) ≤ L)
  rw [inf_centralizer_subgroupOf htL] at hSylL
  obtain ⟨hRY, hR⟩ := hSylL
  obtain ⟨R', hR'⟩ := OddQuot.exists_sylow_map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) hRY hR
  have hSylb : IsSylowIn (((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥L) t'} : Set (L ⧸ pPrimeCore 2 L))) := by
    rw [OddQuot.centralizer_singleton_map_eq ht'2]
    exact ⟨map_mono hRY, R', hR'⟩
  obtain ⟨sb, hsbR, hsbN, hsbo⟩ := hOut _ p f hp hp2 hf hLie _ (orderOf_mk_eq_two ht'2 ht'1) _
    hMbt hMbpc hZM _ hSylb
  obtain ⟨s', hs'R, rfl⟩ := mem_map.mp hsbR
  have hsSL : (s' : X) ∈ S ⊓ L := mem_subgroupOf.mp hs'R
  obtain ⟨hsJ, hsJ0⟩ := mem_inf.mp (hSN hsSL)
  refine ⟨s', hsSL, hsJ, ?_⟩
  rw [oddBarAction_eq_conj hJ0J hJ0L hsup hcore hO hsJ s'.2 hsJ0]
  exact isOuterDiagonalPSL2_conj ι hsbo

end Outer

section Cent

variable {X : Type} [Group X] [Finite X] {J : Subgroup X}

omit [Finite X] in
theorem oddBarAction_pow_eq_one {g : normalizer (J : Set X)} {k : ℕ}
    (hg : (g : X) ^ 2 ^ k = 1) : Eight.oddBarAction J g ^ 2 ^ k = 1 := by
  rw [← map_pow]
  have : g ^ 2 ^ k = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, hg]; rfl)
  rw [this, map_one]

omit [Finite X] in
theorem oddBarAction_fix {g : normalizer (J : Set X)} {d : X} (hdJ : d ∈ J)
    (hgd : (g : X) * d = d * g) :
    Eight.oddBarAction J g ((⟨d, hdJ⟩ : ↥J) : J ⧸ pPrimeCore 2 J) =
      ((⟨d, hdJ⟩ : ↥J) : J ⧸ pPrimeCore 2 J) := by
  rw [Eight.oddBarAction_apply_mk]
  congr 1
  apply Subtype.ext
  change (g : X) * d * (g : X)⁻¹ = d
  rw [hgd, mul_inv_cancel_right]

theorem mem_kernel_of_cf (hCent : CFL2Cent) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h5 : 5 ≤ p ^ f) (hJLie : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    {D : Subgroup X} (hDsyl : ∃ R : Sylow 2 ↥J, (R : Subgroup ↥J) = D.subgroupOf J)
    {s w z : X} (hsJ : s ∈ normalizer (J : Set X)) (hwJ : w ∈ normalizer (J : Set X))
    (hzJ : z ∈ normalizer (J : Set X))
    (hso : IsOuterDiagonalPSL2 (Eight.oddBarAction J ⟨s, hsJ⟩))
    (hsD : s ∈ normalizer (D : Set X)) (hw2 : ∃ k : ℕ, w ^ 2 ^ k = 1)
    (hz2 : ∃ k : ℕ, z ^ 2 ^ k = 1) (hwD : ∀ d ∈ D, w * d = d * w)
    (hzD : ∀ d ∈ D, z * d = d * z) (hws : w * s = s * w) (hzs : z * s = s * z)
    (hz : z ∉ coreActionKernel J) :
    w ∈ coreActionKernel J ∨ z⁻¹ * w ∈ coreActionKernel J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := Eight.oddBarAction J with hρ
  set D₀ : Subgroup (J ⧸ pPrimeCore 2 J) := (D.subgroupOf J).map (QuotientGroup.mk' _) with hD₀
  have hD₀syl : ∃ R : Sylow 2 (J ⧸ pPrimeCore 2 J), (R : Subgroup _) = D₀ := by
    obtain ⟨R, hR⟩ := hDsyl
    refine ⟨R.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
    rw [Sylow.coe_mapSurjective, hR]
  have hσD : D₀.map (ρ ⟨s, hsJ⟩).toMonoidHom = D₀ := by
    have hle : ∀ (u : X) (huJ : u ∈ normalizer (J : Set X)), u ∈ normalizer (D : Set X) →
        D₀.map (ρ ⟨u, huJ⟩).toMonoidHom ≤ D₀ := by
      intro u huJ huD
      rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨⟨u * d * u⁻¹, (mem_normalizer_iff.mp huJ d).mp d.2⟩,
        (mem_normalizer_iff.mp huD d).mp (mem_subgroupOf.mp hd), ?_⟩
      exact (Eight.oddBarAction_apply_mk J ⟨u, huJ⟩ d).symm
    refine le_antisymm (hle s hsJ hsD) ?_
    intro x hx
    have h1 := hle s⁻¹ (inv_mem hsJ) (inv_mem hsD) (mem_map_of_mem _ hx)
    have h2 : (ρ ⟨s⁻¹, inv_mem hsJ⟩).toMonoidHom x = (ρ ⟨s, hsJ⟩)⁻¹ x := by
      rw [show (⟨s⁻¹, inv_mem hsJ⟩ : normalizer (J : Set X)) = (⟨s, hsJ⟩)⁻¹ from rfl, map_inv]
      rfl
    rw [h2] at h1
    refine ⟨_, h1, ?_⟩
    change ρ ⟨s, hsJ⟩ ((ρ ⟨s, hsJ⟩)⁻¹ x) = x
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  obtain ⟨kw, hkw⟩ := hw2
  obtain ⟨kz, hkz⟩ := hz2
  have hfix : ∀ (u : X) (huJ : u ∈ normalizer (J : Set X)), (∀ d ∈ D, u * d = d * u) →
      ∀ d ∈ D₀, ρ ⟨u, huJ⟩ d = d := by
    rintro u huJ huD _ ⟨d, hd, rfl⟩
    exact oddBarAction_fix d.2 (huD _ (mem_subgroupOf.mp hd))
  have hcomm : ∀ (u : X) (huJ : u ∈ normalizer (J : Set X)), u * s = s * u →
      ρ ⟨u, huJ⟩ * ρ ⟨s, hsJ⟩ = ρ ⟨s, hsJ⟩ * ρ ⟨u, huJ⟩ := by
    intro u huJ hus
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hus
  have hζ : ρ ⟨z, hzJ⟩ ≠ 1 := by
    intro h1
    apply hz
    have : (⟨z, hzJ⟩ : normalizer (J : Set X)) ∈ ρ.ker := h1
    exact Eight.mem_ker_oddBarAction.mp this
  rcases hCent _ p f hp hp2 hf h5 hJLie D₀ hD₀syl _ hso hσD (ρ ⟨w, hwJ⟩) (ρ ⟨z, hzJ⟩)
    ⟨kw, oddBarAction_pow_eq_one hkw⟩ ⟨kz, oddBarAction_pow_eq_one hkz⟩ (hcomm w hwJ hws)
    (hcomm z hzJ hzs) (hfix w hwJ hwD) (hfix z hzJ hzD) hζ with h1 | h1
  · left
    exact Eight.mem_ker_oddBarAction.mp h1
  · right
    have h2 : (⟨z⁻¹ * w, mul_mem (inv_mem hzJ) hwJ⟩ : normalizer (J : Set X)) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, show (⟨z⁻¹ * w, mul_mem (inv_mem hzJ) hwJ⟩ :
        normalizer (J : Set X)) = (⟨z, hzJ⟩)⁻¹ * ⟨w, hwJ⟩ from rfl, map_mul, map_inv, h1,
        inv_mul_cancel]
    exact Eight.mem_ker_oddBarAction.mp h2

end Cent
end Seven

end CFSG.ComponentClassification.GSThmB
