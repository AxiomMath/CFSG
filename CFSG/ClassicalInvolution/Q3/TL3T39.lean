module

public import CFSG.ClassicalInvolution.Q3.TL3T38
public import CFSG.ClassicalInvolution.Asc77.AscT8V1
public import CFSG.ClassicalInvolution.Asc77.AscT8V2
public import CFSG.ClassicalInvolution.Asc77.AscT8V3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FStarBasic
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.Q3DBFuzzyEdge
public import CFSG.ClassicalInvolution.Q3.Q3KCGen
public import CFSG.ClassicalInvolution.Q3.Q3NFLink
public import CFSG.ClassicalInvolution.Q3.Q3T6BSymEx
public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Q3.TL4D1Dis
public import CFSG.ClassicalInvolution.Q3.TL4Sep2FB
public import CFSG.ClassicalInvolution.Q3.TL4SepAlphaB

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G] [Finite G]

structure ThmDHypO (r : ℕ) (Ω : Set (Subgroup G)) : Prop where
  hyp : HypOmegaGen Ω
  two : ∀ J ∈ Ω, IsPGroup 2 J
  card : ∀ J ∈ Ω, Nat.card J = 2 ^ r
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  gen : pSpan Ω = ⊤
  inO2 : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
    ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q

section QuotZ

variable {r : ℕ} {Ω : Set (Subgroup G)} {Z : Subgroup G} [Z.Normal]

local notation "πz" => QuotientGroup.mk' Z

abbrev quotFamZ (Z : Subgroup G) [Z.Normal] (Ω : Set (Subgroup G)) : Set (Subgroup (G ⧸ Z)) :=
  (fun K : Subgroup G => K.map (QuotientGroup.mk' Z)) '' Ω

theorem aEmpty_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) (hΩ' : HypOmegaGen (quotFamZ Z Ω)) {K : Subgroup G} (hK : K ∈ Ω) :
    AEmpty (quotFamZ Z Ω) (K.map πz) := by
  have h2' : ∀ J ∈ quotFamZ Z Ω, IsPGroup 2 J := by
    rintro _ ⟨J, hJ, rfl⟩
    exact (hD.two J hJ).map _
  have hodd : ∀ L ∈ Ω, Odd (Nat.card ↥(Z ⊓ L)) := fun L hL => by
    rw [hZK L hL, Subgroup.card_bot]; exact odd_one
  intro J' hJ'star hJ'nbr zK' zJ' hzK' hzJ'
  obtain ⟨hJ'Ω, hne, U', hU', hU'J, hU'N⟩ := hJ'star
  obtain ⟨J, hJ, rfl⟩ := hJ'Ω
  beta_reduce at hJ'nbr hzJ' hne hU'J ⊢
  have hJK : J ≠ K := fun h => hne (by rw [h])
  obtain ⟨L', hL', hU'L', u', hu'U', hu'2, hzp'⟩ := exists_of_mem_USet hΩ' hU'
  obtain ⟨L, hL, rfl⟩ := hL'
  beta_reduce at hU'L'
  obtain ⟨u, huL, rfl⟩ := hU'L' hu'U'
  have hu2 : u * u ≠ 1 := fun h => hu'2 (by rw [← map_mul, h, map_one])
  set U := Subgroup.zpowers u with hUdef
  have hUmap : U.map πz = U' := by rw [hUdef, MonoidHom.map_zpowers, hzp']
  have hUL : U ≤ L := Subgroup.zpowers_le.mpr huL
  have hU : U ∈ USet Ω := by
    refine ⟨L, mem_RSet_of_isPGroup hL (hD.two L hL), hUL, inferInstance, ?_⟩
    obtain ⟨R', hR', hU'R', -, hidx'⟩ := hU'
    obtain ⟨L'', hL'', hR'L'', -, hmax'⟩ := mem_RSet_iff.mp hR'
    obtain ⟨L₂, hL₂, rfl⟩ := hL''
    beta_reduce at hR'L'' hmax'
    have hL₂2 : IsPGroup 2 ↥(L₂.map πz) := (hD.two L₂ hL₂).map _
    have hR'eq : L₂.map πz = R' := hmax' _ le_rfl hL₂2 hR'L''
    have hcardL : ∀ {M : Subgroup G}, M ∈ Ω → Nat.card ↥(M.map πz) = Nat.card M := by
      intro M hM
      have hinj := TwistQ.subgroupMap_injective (N := Z)
        (show M ⊓ Z = ⊥ by rw [inf_comm]; exact hZK M hM)
      exact (Nat.card_eq_of_bijective _ ⟨hinj, MonoidHom.subgroupMap_surjective πz M⟩).symm
    have hcU : Nat.card U = Nat.card U' := by
      rw [← hzp', Nat.card_zpowers, Nat.card_zpowers, orderOf_mk_eq (hZK L hL) huL]
    have h1 := Subgroup.relIndex_mul_card U' R'
    rw [inf_eq_left.mpr hU'R', hidx', ← hR'eq, hcardL hL₂, hD.card L₂ hL₂] at h1
    have h3 := Subgroup.relIndex_mul_card U L
    rw [inf_eq_left.mpr hUL, hcU, hD.card L hL] at h3
    have hpos : 0 < Nat.card U' := Nat.card_pos
    have h4 : U.relIndex L * Nat.card U' = 2 * Nat.card U' := by rw [h3, h1]
    exact Nat.eq_of_mul_eq_mul_right hpos h4
  have hLJ : L = J := by
    obtain ⟨j, hj, hju⟩ := hU'J hu'U'
    have hc : j⁻¹ * u ∈ Z := by
      rw [← QuotientGroup.eq]
      exact hju
    exact eq_of_mem_sup_center hD.hyp hD.two hZc hZK hL hJ huL hu2 hj hc (by group)
  subst hLJ
  have hUN : U ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hx' : πz x ∈ U' := hUmap ▸ ⟨x, hx, rfl⟩
    have h1 := (mem_normalizer_iff_conjSub_eq).mp (hU'N hx')
    rw [← TwistQ.conjSub_map] at h1
    exact (mem_normalizer_iff_conjSub_eq).mpr
      (eq_of_map_eq hD.hyp hD.two hZc hZK (hD.hyp.conjInvariant x K hK) hK h1)
  have hstar : L ∈ omegaStarNbr Ω K := ⟨hJ, hJK, U, hU, hUL, hUN⟩
  have hnbr : L ∉ omegaNbr Ω K := by
    intro h
    apply hJ'nbr
    obtain ⟨-, -, hLN⟩ := (TC.mem_omegaNbr_iff hD.hyp hD.two).mp h
    refine (TC.mem_omegaNbr_iff hΩ' h2').mpr ⟨⟨L, hJ, rfl⟩, hne, ?_⟩
    exact (Subgroup.map_mono hLN).trans (Subgroup.le_normalizer_map πz)
  obtain ⟨⟨zK, hzK⟩, -⟩ := hD.hyp.omega1 K hK
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hD.hyp.omega1 L hJ
  have hzK'' := isUniqueInvolution_map_mk_of_odd (hodd K hK) hzK
  have hzJ'' := isUniqueInvolution_map_mk_of_odd (hodd L hJ) hzJ
  rw [hzK'.eq hzK'', hzJ'.eq hzJ'']
  obtain ⟨g, hg, hgK⟩ := hD.aEmpty K hK L hstar hnbr zK zJ hzK hzJ
  refine ⟨πz g, ?_, by rw [← TwistQ.conjSub_map, hgK]⟩
  have hC : (Subgroup.closure ({zK, zJ} : Set G)).map πz =
      Subgroup.closure ({πz zK, πz zJ} : Set (G ⧸ Z)) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hle : (pairNormalizers K L zK zJ).map πz ≤
      pairNormalizers (K.map πz) (L.map πz) (πz zK) (πz zJ) := by
    unfold pairNormalizers
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)
      rw [← hC]
      exact Subgroup.le_normalizer_map πz
    · refine (Subgroup.map_inf_le _ _ _).trans (inf_le_inf_left _ ?_)
      rw [← hC]
      exact Subgroup.le_normalizer_map πz
  exact hle ⟨g, hg, rfl⟩

theorem thmDHypO_quotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) : ThmDHypO r (quotFamZ Z Ω) := by
  have hodd : ∀ L ∈ Ω, Odd (Nat.card ↥(Z ⊓ L)) := fun L hL => by
    rw [hZK L hL, Subgroup.card_bot]; exact odd_one
  have hΩ' : HypOmegaGen (quotFamZ Z Ω) :=
    PhilipHall.QuaternionBridge.CentQ.quotient_hypOmegaGen hD.hyp Z hZc hodd
  have hsurj := QuotientGroup.mk'_surjective Z
  refine ⟨hΩ', ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨J, hJ, rfl⟩
    exact (hD.two J hJ).map _
  · rintro _ ⟨M, hM, rfl⟩
    have hinj := TwistQ.subgroupMap_injective (N := Z)
      (show M ⊓ Z = ⊥ by rw [inf_comm]; exact hZK M hM)
    rw [← hD.card M hM]
    exact (Nat.card_eq_of_bijective _
      ⟨hinj, MonoidHom.subgroupMap_surjective πz M⟩).symm
  · rintro _ ⟨K, hK, rfl⟩
    exact aEmpty_quotZ hD hZc hZK hΩ' hK
  · rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ hsurj, ← hD.gen,
      Subgroup.map_le_iff_le_comap]
    refine pSpan_le fun K hK => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_pSpan ⟨K, hK, rfl⟩
  · rintro _ ⟨L, hL, rfl⟩ ū hū
    obtain ⟨⟨u, hu⟩, -⟩ := hD.hyp.omega1 L hL
    have hū' := isUniqueInvolution_map_mk_of_odd (hodd L hL) hu
    rw [hū.eq hū']
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hD.inO2 L hL u hu
    exact ⟨Q.map πz, hQn.map _ hsurj,
      hQ2.map _, ⟨u, huQ, rfl⟩⟩

theorem centralizes_of_mk_centralZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    {x : G} (hx : ∀ g : G, πz x * πz g = πz g * πz x) {K : Subgroup G} (hK : K ∈ Ω) :
    ∀ k ∈ K, x * k = k * x := by
  have hconj : conjSub x K = K := by
    apply eq_of_map_eq hD.hyp hD.two hZc hZK (hD.hyp.conjInvariant x K hK) hK
    rw [TwistQ.conjSub_map]
    ext y
    rw [mem_conjSub_iff]
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
    have h1 : (πz x)⁻¹ * πz g * πz x = πz g := by
      rw [mul_assoc, ← hx g]
      group
    rw [h1]
  intro k hk
  have hk' : x * k * x⁻¹ ∈ K := by
    rw [← hconj]
    exact conj_mem_conjSub hk
  have hc : (x * k * x⁻¹) * k⁻¹ ∈ Z := by
    rw [← QuotientGroup.eq_one_iff (N := Z)]
    show πz ((x * k * x⁻¹) * k⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx k]
    group
  have h1 : (x * k * x⁻¹) * k⁻¹ ∈ Z ⊓ K := ⟨hc, K.mul_mem hk' (K.inv_mem hk)⟩
  rw [hZK K hK, Subgroup.mem_bot] at h1
  calc x * k = (x * k * x⁻¹) * k⁻¹ * k * x := by group
    _ = k * x := by rw [h1, one_mul]

theorem pSpan_quotFamZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) :
    pSpan (quotFamZ Z Ω) = ⊤ := (thmDHypO_quotZ hD hZc hZK).gen

@[expose] noncomputable def spanQuotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) :
    ↥(pSpan Ω) →* ↥(pSpan (quotFamZ Z Ω)) :=
  (MonoidHom.comp πz (pSpan Ω).subtype).codRestrict (pSpan (quotFamZ Z Ω)) fun x => by
    rw [pSpan_quotFamZ hD hZc hZK]
    exact Subgroup.mem_top _

theorem spanQuotZ_coe (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    (x : ↥(pSpan Ω)) : (spanQuotZ hD hZc hZK x : G ⧸ Z) = πz (x : G) := rfl

theorem spanQuotZ_surjective (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) :
    Function.Surjective (spanQuotZ hD hZc hZK) := by
  intro y
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective Z (y : G ⧸ Z)
  refine ⟨⟨g, by rw [hD.gen]; exact Subgroup.mem_top g⟩, Subtype.ext ?_⟩
  rw [spanQuotZ_coe]
  exact hg

theorem map_spanQuotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    (L : Subgroup G) :
    (L.subgroupOf (pSpan Ω)).map (spanQuotZ hD hZc hZK) =
      (L.map πz).subgroupOf (pSpan (quotFamZ Z Ω)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  · intro hy
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨l, by rw [hD.gen]; exact Subgroup.mem_top l⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    apply Subtype.ext
    rw [spanQuotZ_coe]
    exact hly

theorem ker_comp_spanQuotZ_le {M : Type} [Group M] (hD : ThmDHypO r Ω)
    (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) {φ : ↥(pSpan (quotFamZ Z Ω)) →* M}
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (quotFamZ Z Ω))) :
    (φ.comp (spanQuotZ hD hZc hZK)).ker ≤ Subgroup.center ↥(pSpan Ω) := by
  intro x hx
  have h1 : spanQuotZ hD hZc hZK x ∈ Subgroup.center _ := hker hx
  have hc : ∀ g : G, πz (x : G) * πz g = πz g * πz (x : G) := by
    intro g
    have h2 := Subgroup.mem_center_iff.mp h1
      ⟨πz g, by rw [pSpan_quotFamZ hD hZc hZK]; exact Subgroup.mem_top _⟩
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, spanQuotZ_coe] at h3
    exact h3.symm
  have hle : pSpan Ω ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    refine pSpan_le fun K hK k hk => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (centralizes_of_mk_centralZ hD hZc hZK hc hK k hk).symm
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle y.2)
  simp only [Subgroup.coe_mul]
  exact this

theorem range_comp_spanQuotZ {M : Type} [Group M] (hD : ThmDHypO r Ω)
    (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥) (φ : ↥(pSpan (quotFamZ Z Ω)) →* M) :
    (φ.comp (spanQuotZ hD hZc hZK)).range = φ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (spanQuotZ_surjective hD hZc hZK),
    ← MonoidHom.range_eq_map]

noncomputable def AEIdentOn.ofQuotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    {n : ℕ} {𝒜 : Set (Finset (Fin n))} {H : Subgroup (AE.AEQ n)}
    (I : AEIdentOn (quotFamZ Z Ω) n 𝒜 H) : AEIdentOn Ω n 𝒜 H where
  φ := I.φ.comp (spanQuotZ hD hZc hZK)
  range_eq := by rw [range_comp_spanQuotZ, I.range_eq]
  ker_le := ker_comp_spanQuotZ_le hD hZc hZK I.ker_le
  label := by
    intro L hL
    obtain ⟨α, hα, h, b, hlab⟩ := I.label _ ⟨L, hL, rfl⟩
    exact ⟨α, hα, h, b, by rw [← Subgroup.map_map, map_spanQuotZ, hlab]⟩
  label_surj := by
    intro α hα h b
    obtain ⟨_, ⟨L, hL, rfl⟩, hlab⟩ := I.label_surj α hα h b
    exact ⟨L, hL, by rw [← Subgroup.map_map, map_spanQuotZ, hlab]⟩

noncomputable def AEIdent.ofQuotZ (hD : ThmDHypO r Ω) (hZc : Z ≤ Subgroup.center G)
    (hZK : ∀ K ∈ Ω, Z ⊓ K = ⊥)
    {n : ℕ} (I : AEIdent (quotFamZ Z Ω) n) : AEIdent Ω n where
  φ := I.φ.comp (spanQuotZ hD hZc hZK)
  range_eq := by rw [range_comp_spanQuotZ, I.range_eq]
  ker_le := ker_comp_spanQuotZ_le hD hZc hZK I.ker_le
  label := by
    intro L hL
    obtain ⟨α, h, b, hlab⟩ := I.label _ ⟨L, hL, rfl⟩
    exact ⟨α, h, b, by rw [← Subgroup.map_map, map_spanQuotZ, hlab]⟩
  label_surj := by
    intro α h b
    obtain ⟨_, ⟨L, hL, rfl⟩, hlab⟩ := I.label_surj α h b
    exact ⟨L, hL, by rw [← Subgroup.map_map, map_spanQuotZ, hlab]⟩

end QuotZ

section Span

variable {r : ℕ} {Ω : Set (Subgroup G)}

theorem thmDHypO_restrict (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 2 ^ r) (hA : ∀ J ∈ Ω, AEmpty Ω J)
    (hQ : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    ThmDHypO r (restrictFamily P (pSpan P)) := by
  have hLX : ∀ L ∈ P, L ≤ pSpan P := fun L hL => le_pSpan hL
  have hΩ' : HypOmegaGen (restrictFamily P (pSpan P)) := by
    refine TL4.hypOmegaGen_restrict_of (pSpan P) hLX (fun n hn L hL => hinv L hL n hn)
      (fun K hK => hΩ.omega1 K (hPΩ hK)) (fun K hK => ?_)
      (fun K hK J hJ => hΩ.omega3 K (hPΩ hK) J (hPΩ hJ))
      (fun K hK J hJ hne => hΩ.omega4 K (hPΩ hK) J (hPΩ hJ) hne)
      (fun K hK J hJ hne => hΩ.omega5 K (hPΩ hK) J (hPΩ hJ) hne)
    refine le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx => hx.1) fun x hx => ?_
    exact Subgroup.subset_closure ⟨hx, (h2 K (hPΩ hK)).to_le (Subgroup.zpowers_le.mpr hx)⟩
  have h2' : ∀ J ∈ restrictFamily P (pSpan P), IsPGroup 2 J := by
    rintro _ ⟨J, hJ, -, rfl⟩
    exact (h2 J (hPΩ hJ)).comap_subtype
  have h8' : ∀ J ∈ restrictFamily P (pSpan P), Nat.card J = 2 ^ r := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJX).toEquiv]
    exact h8 J (hPΩ hJ)
  have hA' : ∀ J ∈ restrictFamily P (pSpan P), AEmpty (restrictFamily P (pSpan P)) J := by
    rintro _ ⟨J, hJ, hJX, rfl⟩
    exact aEmpty_restrictFamily hΩ h2 hPΩ hJX (hA J (hPΩ hJ))
  have hmap : (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype = pSpan P := by
    refine le_antisymm (Subgroup.map_subtype_le _) (pSpan_le fun L hL => ?_)
    have h1 : L.subgroupOf (pSpan P) ≤ pSpan (restrictFamily P (pSpan P)) :=
      le_pSpan ⟨L, hL, hLX L hL, rfl⟩
    calc L = (L.subgroupOf (pSpan P)).map (pSpan P).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le (hLX L hL)).symm
      _ ≤ (pSpan (restrictFamily P (pSpan P))).map (pSpan P).subtype := Subgroup.map_mono h1
  have hgen : pSpan (restrictFamily P (pSpan P)) = ⊤ := by
    apply Subgroup.map_injective (pSpan P).subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine ⟨hΩ', h2', h8', hA', hgen, ?_⟩
  rintro _ ⟨L, hL, hLX', rfl⟩ u hu
  obtain ⟨Q, hQn, hQ2, huQ⟩ :=
    hQ L (hPΩ hL) (u : G) (isUniqueInvolution_of_subgroupOf hu hLX')
  refine ⟨Q.subgroupOf (pSpan P), ⟨fun q hq g => ?_⟩, hQ2.comap_subtype,
    Subgroup.mem_subgroupOf.mpr huQ⟩
  exact Subgroup.mem_subgroupOf.mpr (hQn.conj_mem _ (Subgroup.mem_subgroupOf.mp hq) g)

omit [Finite G] in
theorem trans_restrict {P : Set (Subgroup G)}
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L') :
    ∀ L ∈ restrictFamily P (pSpan P), ∀ L' ∈ restrictFamily P (pSpan P),
      ∃ g : ↥(pSpan P), conjSub g L = L' := by
  rintro _ ⟨L, hL, -, rfl⟩ _ ⟨L', hL', -, rfl⟩
  obtain ⟨x, hx, hxL⟩ := htrans L hL L' hL'
  exact ⟨⟨x, hx⟩, by rw [conjSub_subgroupOf, hxL]⟩

theorem oddCore_le_center (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hQ : ∀ L ∈ Ω, ∀ u : G, IsUniqueInvolution L u →
      ∃ Q : Subgroup G, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    classicalInvolutionOddCore ↥(pSpan P) ≤ Subgroup.center ↥(pSpan P) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' : (x : G) ∈ oddCoreImg (pSpan P) := ⟨x, hx, rfl⟩
  exact Subtype.ext (comm_of_mem_oddCoreImg hΩ h2 hQ hPΩ hinv x hx' y y.2).symm

theorem oddCore_inf_eq_bot {H : Type} [Group H] [Finite H] {L : Subgroup H}
    (hL : IsPGroup 2 L) : classicalInvolutionOddCore H ⊓ L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hL
  refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
  rw [hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr
    (QuaternionStructure.odd_natCard_oddCore H))

theorem thmDConcl_spanQuot (hD : ThmDHyp r Ω) (hbelow : ThmDAbsBelow r (Nat.card G))
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hlt : Nat.card ↥(pSpan P) < Nat.card G)
    (htrans : ∀ L ∈ P, ∀ L' ∈ P, ∃ x ∈ pSpan P, conjSub x L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    ThmDConcl (quotFamZ (classicalInvolutionOddCore ↥(pSpan P)) (restrictFamily P (pSpan P))) := by
  set R := classicalInvolutionOddCore ↥(pSpan P) with hR
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥(pSpan P) := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ K ∈ restrictFamily P (pSpan P), R ⊓ K = ⊥ := fun K hK =>
    oddCore_inf_eq_bot (hO.two K hK)
  have hQ := thmDHypO_quotZ hO hRc hRK
  have hcard : Nat.card (↥(pSpan P) ⧸ R) < Nat.card G :=
    lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card R)) hlt
  have htrans' : ∀ L ∈ quotFamZ R (restrictFamily P (pSpan P)),
      ∀ L' ∈ quotFamZ R (restrictFamily P (pSpan P)), ∃ g, conjSub g L = L' := by
    rintro _ ⟨K, hK, rfl⟩ _ ⟨K', hK', rfl⟩
    obtain ⟨g, hg⟩ := trans_restrict htrans K hK K' hK'
    exact ⟨QuotientGroup.mk' R g, by rw [← TwistQ.conjSub_map, hg]⟩
  have hodd : classicalInvolutionOddCore (↥(pSpan P) ⧸ R) = ⊥ :=
    QuaternionStructure.oddCore_quotient_oddCore_eq_bot _
  exact thmDAbsAt_iff.mp (hbelow _ hcard) _
    ⟨hQ.hyp, hQ.two, hQ.card, hQ.aEmpty, hQ.gen, htrans', hodd, hQ.inO2⟩

noncomputable def AEIdent.ofSpanQuot (hD : ThmDHyp r Ω) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) {m : ℕ}
    (I : AEIdent (quotFamZ (classicalInvolutionOddCore ↥(pSpan P))
      (restrictFamily P (pSpan P))) m) : AEIdent P m :=
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  AEIdent.ofRestrict hO.gen (fun _ hL => le_pSpan hL)
    (AEIdent.ofQuotZ hO (oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv)
      (fun K hK => oddCore_inf_eq_bot (hO.two K hK)) I)

theorem comm_of_not_conj_span (hD : ThmDHyp r Ω) (hd1 : ThmD1GenBelow r (Nat.card G))
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hlt : Nat.card ↥(pSpan P) < Nat.card G)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) {L L' : Subgroup G} (hL : L ∈ P)
    (hL' : L' ∈ P) (hnc : ¬ ∃ x ∈ pSpan P, conjSub x L = L') :
    ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := by
  set Y := pSpan P with hY
  set R := classicalInvolutionOddCore ↥Y with hR
  have hLY : ∀ M ∈ P, M ≤ Y := fun M hM => le_pSpan hM
  have hO := thmDHypO_restrict (r := r) hD.hyp hD.two hD.card hD.aEmpty hD.inO2 hPΩ hinv
  have hRc : R ≤ Subgroup.center ↥Y := oddCore_le_center hD.hyp hD.two hD.inO2 hPΩ hinv
  have hRK : ∀ K ∈ restrictFamily P Y, R ⊓ K = ⊥ := fun K hK =>
    oddCore_inf_eq_bot (hO.two K hK)
  have hQ := thmDHypO_quotZ hO hRc hRK
  set π := QuotientGroup.mk' R with hπ
  have hmemY : ∀ M ∈ P, M.subgroupOf Y ∈ restrictFamily P Y := fun M hM => ⟨M, hM, hLY M hM, rfl⟩
  have hmem : ∀ M ∈ P, (M.subgroupOf Y).map π ∈ quotFamZ R (restrictFamily P Y) :=
    fun M hM => ⟨_, hmemY M hM, rfl⟩
  have heq : ∀ {M M' : Subgroup G}, M ∈ P → M' ∈ P →
      (M.subgroupOf Y).map π = (M'.subgroupOf Y).map π → M = M' := by
    intro M M' hM hM' h
    have h1 := eq_of_map_eq hO.hyp hO.two hRc hRK (hmemY M hM) (hmemY M' hM') h
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr (hLY M hM), inf_eq_left.mpr (hLY M' hM')] at h2
  have hnc' : ¬ ∃ x ∈ pSpan (quotFamZ R (restrictFamily P Y)),
      conjSub x ((L.subgroupOf Y).map π) = (L'.subgroupOf Y).map π := by
    rintro ⟨x, -, hx⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R x
    apply hnc
    refine ⟨y, y.2, heq (hinv L hL y y.2) hL' ?_⟩
    rw [← hx, ← TwistQ.conjSub_map, conjSub_subgroupOf]
  have hcard : Nat.card ↥(pSpan (quotFamZ R (restrictFamily P Y))) < Nat.card G :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _)
      (lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card R)) hlt)
  have hinv' : ∀ M ∈ quotFamZ R (restrictFamily P Y),
      ∀ x ∈ pSpan (quotFamZ R (restrictFamily P Y)), conjSub x M ∈ quotFamZ R (restrictFamily P Y) :=
    fun M hM x _ => hQ.hyp.conjInvariant x M hM
  have hodd : classicalInvolutionOddCore ↥(pSpan (quotFamZ R (restrictFamily P Y))) = ⊥ := by
    rw [hQ.gen]
    exact classicalInvolutionOddCore_eq_bot_of_mulEquiv Subgroup.topEquiv.symm
      (QuaternionStructure.oddCore_quotient_oddCore_eq_bot _)
  have hE2 : ∀ M ∈ quotFamZ R (restrictFamily P Y), ∀ u, IsUniqueInvolution M u →
      ∃ Q : Subgroup (↥Y ⧸ R), Q ≤ pSpan (quotFamZ R (restrictFamily P Y)) ∧
        (∀ x ∈ pSpan (quotFamZ R (restrictFamily P Y)), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧
        IsPGroup 2 Q ∧ u ∈ Q := by
    intro M hM u hu
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hQ.inO2 M hM u hu
    refine ⟨Q, by rw [hQ.gen]; exact le_top, fun x _ q hq => hQn.conj_mem q hq x, hQ2, huQ⟩
  have hcomm := hd1 _ _ hQ.hyp hQ.two hQ.card hQ.aEmpty _ le_rfl hcard hinv' hodd hE2
    _ (hmem L hL) _ (hmem L' hL') hnc'
  have hnorm : ∀ {M M' : Subgroup G}, M ∈ P → M' ∈ P →
      (∀ a ∈ (M.subgroupOf Y).map π, ∀ b ∈ (M'.subgroupOf Y).map π, a * b = b * a) →
      ∀ b ∈ M', conjSub b M = M := by
    intro M M' hM hM' hc b hb
    have hbY : b ∈ Y := hLY M' hM' hb
    refine heq (hinv M hM b hbY) hM ?_
    have e : conjSub (⟨b, hbY⟩ : ↥Y) (M.subgroupOf Y) = (conjSub b M).subgroupOf Y :=
      conjSub_subgroupOf Y ⟨b, hbY⟩ M
    rw [← e, TwistQ.conjSub_map]
    ext w
    rw [mem_conjSub_iff]
    have hbm : π ⟨b, hbY⟩ ∈ (M'.subgroupOf Y).map π := ⟨⟨b, hbY⟩, hb, rfl⟩
    set β := π ⟨b, hbY⟩ with hβ
    constructor
    · intro hw
      have h2 := hc _ hw β hbm
      have e2 : w = β⁻¹ * w * β := by
        calc w = β * (β⁻¹ * w * β) * β⁻¹ := by group
          _ = (β⁻¹ * w * β) * β * β⁻¹ := by rw [h2]
          _ = β⁻¹ * w * β := by group
      rw [e2]
      exact hw
    · intro hw
      have h2 := hc _ hw β hbm
      have e2 : β⁻¹ * w * β = w := by
        calc β⁻¹ * w * β = β⁻¹ * (w * β) := by group
          _ = β⁻¹ * (β * w) := by rw [h2]
          _ = w := by group
      rw [e2]
      exact hw
  have hL'L := hnorm hL hL' hcomm
  intro a ha b hb
  have haY : a ∈ Y := hLY L hL ha
  have hbY : b ∈ Y := hLY L' hL' hb
  set c := a * b * a⁻¹ * b⁻¹ with hc
  have hcL : c ∈ L := by
    have h1 : b * a⁻¹ * b⁻¹ ∈ L := by
      rw [← hL'L b hb]
      exact conj_mem_conjSub (L.inv_mem ha)
    have : c = a * (b * a⁻¹ * b⁻¹) := by rw [hc]; group
    rw [this]
    exact L.mul_mem ha h1
  have hcR : (⟨c, Y.mul_mem (Y.mul_mem (Y.mul_mem haY hbY) (Y.inv_mem haY)) (Y.inv_mem hbY)⟩ :
      ↥Y) ∈ R := by
    rw [← QuotientGroup.eq_one_iff (N := R)]
    have h1 := hcomm (π ⟨a, haY⟩) ⟨⟨a, haY⟩, ha, rfl⟩ (π ⟨b, hbY⟩) ⟨⟨b, hbY⟩, hb, rfl⟩
    show π (⟨a, haY⟩ * ⟨b, hbY⟩ * ⟨a, haY⟩⁻¹ * ⟨b, hbY⟩⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
    group
  have hc1 : (⟨c, Y.mul_mem (Y.mul_mem (Y.mul_mem haY hbY) (Y.inv_mem haY)) (Y.inv_mem hbY)⟩ :
      ↥Y) = 1 := by
    have h1 : (⟨c, Y.mul_mem (Y.mul_mem (Y.mul_mem haY hbY) (Y.inv_mem haY)) (Y.inv_mem hbY)⟩ :
        ↥Y) ∈ R ⊓ L.subgroupOf Y := ⟨hcR, Subgroup.mem_subgroupOf.mpr hcL⟩
    rwa [hRK _ (hmemY L hL), Subgroup.mem_bot] at h1
  have hc1' : c = 1 := congrArg Subtype.val hc1
  calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
    _ = b * a := by rw [← hc, hc1', one_mul]

end Span

end CFSG.ClassicalInvolution.Q3.TC.Thin
