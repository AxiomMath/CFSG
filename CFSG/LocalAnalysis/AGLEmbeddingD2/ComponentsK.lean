module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.Closure
import CFSG.LocalAnalysis.AGLEmbeddingD2.SimpleQuotient
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectCoprimeLifts
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

theorem map_eq_one_of_surjective_simple {Γ Sg Λ : Type*} [Group Γ] [Finite Γ] [Group Sg]
    [IsSimpleGroup Sg] [Group Λ] [Finite Λ] {p : ℕ} (φ : Γ →* Sg) (hφ : Function.Surjective φ)
    (hnab : ∃ a b : Sg, a * b ≠ b * a) (hker : p.Coprime (Nat.card φ.ker))
    (hΛ : p.Coprime (Nat.card Λ)) (hout : Group.IsSolvable (Outer Λ)) (ρ : Γ →* MulAut Λ)
    {x : Γ} (hx : IsPGroup p (Subgroup.zpowers x)) : ρ x = 1 := by
  let e : Γ ⧸ φ.ker ≃* Sg := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have : IsSimpleGroup (Γ ⧸ φ.ker) := e.isSimpleGroup
  refine map_eq_one_of_simple_quotient φ.ker hker this ?_ hΛ hout ρ hx
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h

theorem sup_ker_eq_top_of_index_le {Γ Sg : Type*} [Group Γ] [Finite Γ] [Group Sg] [Finite Sg]
    [IsSimpleGroup Sg] (φ : Γ →* Sg) (hφ : Function.Surjective φ) (h6 : 6 < Nat.card Sg)
    {U : Subgroup Γ} (hU : U.index ≤ 3) : U ⊔ φ.ker = ⊤ := by
  have hU0 : U.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (U.map φ).index ≤ 3 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hU0) (Subgroup.index_map_dvd (H := U) hφ)).trans hU
  have htop : U.map φ = ⊤ := by
    by_contra hne
    exact absurd (three_lt_index_of_isSimpleGroup h6 hne) (not_lt.mpr hle)
  have := Subgroup.comap_map_eq φ U
  rw [htop, Subgroup.comap_top] at this
  exact this.symm

theorem index_inf_normalizer_le {G : Type*} [Group G] [Finite G] (H₁ L : Subgroup G) (B : ℕ)
    (hB : ∀ (m : ℕ) (g : Fin m → G), (∀ j, g j ∈ H₁) →
      Function.Injective (fun j => L.map (MulAut.conj (g j)).toMonoidHom) → m ≤ B) :
    ((H₁ ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H₁).index ≤ B := by
  set T := (H₁ ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H₁ with hT
  by_contra hlt
  push Not at hlt
  have hcard : B + 1 ≤ Nat.card (↥H₁ ⧸ T) := by
    rw [← Subgroup.index_eq_card]
    exact hlt
  have : Fintype (↥H₁ ⧸ T) := Fintype.ofFinite _
  obtain ⟨f⟩ : Nonempty (Fin (B + 1) ↪ ↥H₁ ⧸ T) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hcard
  let g : Fin (B + 1) → ↥H₁ := fun j => Quotient.out (f j)
  have hinj : Function.Injective (fun j => L.map (MulAut.conj ((g j : ↥H₁) : G)).toMonoidHom) := by
    intro i j hij
    apply f.injective
    rw [← Quotient.out_eq (f i), ← Quotient.out_eq (f j)]
    refine QuotientGroup.eq.mpr ?_
    refine Subgroup.mem_subgroupOf.mpr ⟨H₁.mul_mem (H₁.inv_mem (g i).2) (g j).2, ?_⟩
    change (((g i)⁻¹ * g j : ↥H₁) : G) ∈ Subgroup.normalizer (L : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hij' : L.map (MulAut.conj ((g i : ↥H₁) : G)).toMonoidHom =
        L.map (MulAut.conj ((g j : ↥H₁) : G)).toMonoidHom := hij
    have e : (((g i)⁻¹ * g j : ↥H₁) : G) = ((g i : ↥H₁) : G)⁻¹ * ((g j : ↥H₁) : G) := rfl
    rw [e]
    change L.map (MulAut.conj (((g i : ↥H₁) : G)⁻¹ * ((g j : ↥H₁) : G))).toMonoidHom = L
    rw [map_conj_mul_eq, ← hij', ← map_conj_mul_eq, inv_mul_cancel]
    ext x
    simp
  exact absurd (hB (B + 1) (fun j => ((g j : ↥H₁) : G)) (fun j => (g j).2) hinj) (by omega)

theorem isSubnormal_of_le_of_isSubnormal {G : Type*} [Group G] {L N M : Subgroup G}
    (h : IsSubnormal L M) (hLN : L ≤ N) (hNM : N ≤ M) : IsSubnormal L N := by
  have h1 := cfsg_isSubnormal_comap N.subtype h
  rw [show M.comap N.subtype = ⊤ from Subgroup.subgroupOf_eq_top.mpr hNM] at h1
  have h2 := cfsg_isSubnormal_map N.subtype h1
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype,
    show L.comap N.subtype = L.subgroupOf N from rfl,
    Subgroup.map_subgroupOf_eq_of_le hLN] at h2

theorem exists_surjective_stabilizer {G Sg : Type*} [Group G] [Finite G] [Group Sg] [Finite Sg]
    [IsSimpleGroup Sg] {H₁ L : Subgroup G} (φ : ↥H₁ →* Sg) (hφ : Function.Surjective φ)
    (h6 : 6 < Nat.card Sg)
    (hidx : ((H₁ ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H₁).index ≤ 3)
    (hSt : H₁ ⊓ Subgroup.normalizer (L : Set G) ≤ H₁) :
    Function.Surjective (φ.comp (Subgroup.inclusion hSt)) ∧
      Nat.card (φ.comp (Subgroup.inclusion hSt)).ker ∣ Nat.card φ.ker := by
  have hsup := sup_ker_eq_top_of_index_le φ hφ h6 hidx
  refine ⟨fun σ => ?_, ?_⟩
  · obtain ⟨γ, rfl⟩ := hφ σ
    have hγ : γ ∈ (H₁ ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H₁ ⊔ φ.ker :=
      hsup ▸ Subgroup.mem_top γ
    obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hγ
    refine ⟨⟨(s : G), Subgroup.mem_subgroupOf.mp hs⟩, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]
    rfl
  · have hle : (φ.comp (Subgroup.inclusion hSt)).ker.map (Subgroup.inclusion hSt) ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hSt)]
    exact Subgroup.card_dvd_of_le hle

section Component

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R L : Subgroup G}

omit [Finite G] in
theorem nonempty_mulEquiv_barM_of_inf_eq {M₁ M₂ : Subgroup G} (h₁ : L ≤ M₁) (h₂ : L ≤ M₂)
    (h : L ⊓ pCoreOf 2 M₁ = L ⊓ pCoreOf 2 M₂) : Nonempty (↥(barM M₁ L) ≃* ↥(barM M₂ L)) := by
  let f : (M : Subgroup G) → L ≤ M → ↥L →* ↥(barM M L) := fun M hM =>
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap (L.subgroupOf M)).comp
      (Subgroup.subgroupOfEquivOfLe hM).symm.toMonoidHom
  have hf : ∀ (M : Subgroup G) (hM : L ≤ M), Function.Surjective (f M hM) := fun M hM =>
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).subgroupMap_surjective _).comp
      (Subgroup.subgroupOfEquivOfLe hM).symm.surjective
  have hker : ∀ (M : Subgroup G) (hM : L ≤ M), ∀ l : L, f M hM l = 1 ↔ (l : G) ∈ pCoreOf 2 M := by
    intro M hM l
    have h1 : f M hM l = 1 ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(l : G), hM l.2⟩ = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1]
    exact mk_eq_one_iff_coe_mem_pCoreOf _
  have hker12 : (f M₁ h₁).ker = (f M₂ h₂).ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker, hker]
    constructor
    · intro hl
      have : (l : G) ∈ L ⊓ pCoreOf 2 M₂ := h ▸ ⟨l.2, hl⟩
      exact this.2
    · intro hl
      have : (l : G) ∈ L ⊓ pCoreOf 2 M₁ := h ▸ ⟨l.2, hl⟩
      exact this.2
  exact ⟨((QuotientGroup.quotientKerEquivOfSurjective _ (hf M₁ h₁)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker12)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (hf M₂ h₂))⟩

namespace AGLPair

theorem inf_twoCore_H_eq (h : AGLPair p M H R) (hL : IsTwoPrimeComponent M L) (hLH : L ≤ H) :
    L ⊓ pCoreOf 2 H = L ⊓ pCoreOf 2 M := by
  refine le_antisymm ?_ (inf_le_inf_left L h.twoCore_M_le)
  rw [hL.inf_twoCore]
  refine normal_pGroup_le_pCoreOf 2 _ L inf_le_left ?_
    ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
  exact common_normalizer_le_normalizer_inf L L _ Subgroup.le_normalizer
    (hLH.trans (localGroup_le_normalizer_pCoreOf 2 H))

theorem isTwoPrimeComponent_H (h : AGLPair p M H R) (hL : IsTwoPrimeComponent M L)
    (hLN : L ≤ GLBPrimeCore p H) : IsTwoPrimeComponent H L := by
  have hNH : GLBPrimeCore p H ≤ H := glbPrimeCore_le p H
  have hLH : L ≤ H := hLN.trans hNH
  have hNn : ((GLBPrimeCore p H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_glbPrimeCore p H)
  have hsub : IsSubnormal L H := isSubnormal_of_isSubnormal_of_normal
    (isSubnormal_of_le_of_isSubnormal hL.subnormal hLN h.primeCore_le) hNH hNn
  obtain ⟨e⟩ := nonempty_mulEquiv_barM_of_inf_eq hLH hL.le (h.inf_twoCore_H_eq hL hLH)
  refine ⟨hLH, hsub, hL.perfect, le_top, ?_, ?_⟩
  · have h1 := cfsg_isSubnormal_comap H.subtype hsub
    rw [show H.comap H.subtype = ⊤ from Subgroup.subgroupOf_self H] at h1
    have h2 := cfsg_isSubnormal_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv e hL.component.2.2

theorem isCatalogGroup_barM_center_quotient (h : AGLPair p M H R) (hLH : IsTwoPrimeComponent H L) :
    IsCatalogGroup (↥(barM H L) ⧸ Subgroup.center ↥(barM H L)) :=
  have hHtop : H ≠ ⊤ := fun hH => h.inf_lt_right.ne (by rw [hH, top_inf_eq])
  ((catalogSimpleSections_of_isKProper h.glob.kProper H hHtop).quotient
    (CFSG.pCore 2 ↥H)).isCatalogGroup_center_quotient hLH.component

end AGLPair

omit [Finite G] in
theorem exists_conjAction {S : Subgroup G} (hSH : S ≤ H)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ ρ : ↥S →* MulAut ↥(barM H L), ∀ (s : S) (w : ↥(barM H L)),
      ((ρ s w : ↥(barM H L)) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hSH s.2⟩ * w *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨s, hSH s.2⟩)⁻¹ := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  have hmem : ∀ s : S,
      mk ⟨s, hSH s.2⟩ ∈ Subgroup.normalizer ((barM H L : Subgroup _) : Set _) := by
    intro s
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have := congrArg (barM H) (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSL s.2))
    change barM H (L.map (MulAut.conj (s : G)).toMonoidHom) = barM H L at this
    rw [barM_map_conj (hSH s.2)] at this
    exact this
  let ψ : ↥S →* ↥(Subgroup.normalizer ((barM H L : Subgroup _) : Set _)) :=
    ((mk.comp (Subgroup.inclusion hSH)).codRestrict _ hmem)
  exact ⟨(barM H L).normalizerMonoidHom.comp ψ, fun s w => rfl⟩

end Component

section Conjugates

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R L : Subgroup G}

theorem le_pRank_of_injective_conj_of_normalizer {A : Subgroup G} (hAM : A ≤ M) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hLb : IsComponentOf Lb ⊤) (hLbA : Lb ≤ barM M A) {y l : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hyL : y ∈ Lb) (hyq : IsPGroup q (Subgroup.zpowers y)) (hlL : l ∈ Lb) (hyl : y * l ≠ l * y)
    {m : ℕ} (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M)
    (hg : ∀ j, g j ∈ Subgroup.normalizer ((barM M A : Subgroup _) : Set _))
    (hinj : Function.Injective fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank q A := by
  have h1 := le_pRank_of_components hq (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom)
    (fun j => (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (g j))
      Lb).mpr hLb) hinj (barM M A) (fun j => g j * y * (g j)⁻¹)
    (fun j => (Subgroup.mem_normalizer_iff.mp (hg j) y).mp (hLbA hyL))
    (fun j => ⟨y, hyL, rfl⟩)
    (fun j => by
      obtain ⟨k, hk⟩ := hyq ⟨y, Subgroup.mem_zpowers y⟩
      have hk' : y ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact isPGroup_zpowers_of_pow_eq_one (by rw [conj_pow, hk']; group))
    (fun j => ⟨g j * l * (g j)⁻¹, ⟨l, hlL, rfl⟩, fun he => hyl (by
      have := congrArg (fun z => (g j)⁻¹ * z * g j) he
      simpa [mul_assoc] using this)⟩)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (pRank_barM_le hq hq2 M A hAM)

namespace AGLPair

theorem card_le_three_of_injective_conj (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (h : AGLPair p M H R) (hLH : IsTwoPrimeComponent H L) (hLN : L ≤ GLBPrimeCore p H) {m : ℕ}
    (g : Fin m → G) (hg : ∀ j, g j ∈ H)
    (hinj : Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom) : m ≤ 3 := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  set Lb := barM H L with hLb
  have hLbC : IsComponentOf Lb ⊤ := hLH.component
  have hsimple : IsSimpleGroup (↥Lb ⧸ Subgroup.center ↥Lb) := hLbC.2.2.2
  obtain ⟨q, hq, hq2, hqdvd⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      q ∣ Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) := by
    rcases hα _ hsimple
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hLbC.2.2)
      (h.isCatalogGroup_barM_center_quotient hLH) with h3 | h5
    · exact ⟨3, Nat.prime_three, by decide, h3⟩
    · exact ⟨5, Nat.prime_five, by decide, h5⟩
  obtain ⟨y, hyL, hyq, l, hlL, hyl⟩ := exists_qElement_not_central hq hqdvd
  have hNH : GLBPrimeCore p H ≤ H := glbPrimeCore_le p H
  have hNn : ((GLBPrimeCore p H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_glbPrimeCore p H)
  have hbarN : (barM H (GLBPrimeCore p H)).Normal :=
    Subgroup.Normal.map hNn mk (QuotientGroup.mk'_surjective _)
  have hLbN : Lb ≤ barM H (GLBPrimeCore p H) := Subgroup.map_mono (fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hLN (Subgroup.mem_subgroupOf.mp hz)))
  have hinj' : Function.Injective fun j : Fin m =>
      Lb.map (MulAut.conj (mk ⟨g j, hg j⟩)).toMonoidHom := by
    intro i j hij
    apply hinj
    refine (hLH.map_conj (hg i)).eq_of_barM_eq (hLH.map_conj (hg j)) ?_
    rw [barM_map_conj (hg i), barM_map_conj (hg j)]
    exact hij
  have hm := le_pRank_of_injective_conj_of_normalizer hNH hq hq2 hLbC hLbN hyL hyq hlL hyl
    (fun j => mk ⟨g j, hg j⟩)
    (fun j => by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) hinj'
  by_contra hm3
  have hrk := CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq (le_inf hNH h.primeCore_le)
  exact h.false_of_four_le_pRank hD1 hq hq2 (by omega)

theorem mem_normalizer_of_isPGroup (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (h : AGLPair p M H R) (hLH : IsTwoPrimeComponent H L) (hLN : L ≤ GLBPrimeCore p H)
    (hp5 : 5 ≤ p) {x : G} (hxH : x ∈ H) (hx : IsPGroup p (Subgroup.zpowers x)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hxn
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.card_le_three_of_injective_conj hD1 hα hLH hLN (fun j : Fin p => x ^ (j : ℕ))
    (fun j => H.pow_mem hxH _) (injective_conj_pow_of_not_mem_normalizer hx hxn)
  omega

end AGLPair

end Conjugates

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R X : Subgroup G}

structure D2SimpleSection (p : ℕ) (H X : Subgroup G) : Prop where
  exists_hom : ∃ (Sg : Type) (_ : Group Sg) (_ : Finite Sg) (H₁ : Subgroup G) (φ : ↥H₁ →* Sg),
    H₁ ≤ H ∧ X ≤ H₁ ∧ Function.Surjective φ ∧ IsSimpleGroup Sg ∧ 6 < Nat.card Sg ∧
      (∃ a b : Sg, a * b ≠ b * a) ∧ p.Coprime (Nat.card φ.ker)

theorem AGLPair.barM_le_centralizer_of_simpleSection (hpair : AGLPair p M H R) {X : Subgroup G}
    (hXR : X ≤ R) (hperf : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H)
    (hsec : D2SimpleSection p H X) (hD1 : D1For G) (hp5 : 5 ≤ p) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hLK : L ≤ H ⊓ M) : barM M X ≤ Subgroup.centralizer (barM M L : Set _) := by
  obtain ⟨Sg, _, _, H₁, φ, hH₁H, hXH₁, hφ, hsimple, h6, hnab, hker⟩ := hsec.exists_hom
  have hLN : L ≤ GLBPrimeCore p H := hperf L hLK hL.perfect
  have hLH : IsTwoPrimeComponent H L := hpair.isTwoPrimeComponent_H hL hLN
  set Stab := H₁ ⊓ Subgroup.normalizer (L : Set G) with hStab
  have hStabH₁ : Stab ≤ H₁ := inf_le_left
  have hStabH : Stab ≤ H := hStabH₁.trans hH₁H
  have hidx : (Stab.subgroupOf H₁).index ≤ 3 := index_inf_normalizer_le H₁ L 3 fun m g hg hinj =>
    hpair.card_le_three_of_injective_conj hD1 hα hLH hLN g (fun j => hH₁H (hg j)) hinj
  obtain ⟨hψ, hψker⟩ := exists_surjective_stabilizer φ hφ h6 hidx hStabH₁
  have hψcop : p.Coprime (Nat.card (φ.comp (Subgroup.inclusion hStabH₁)).ker) :=
    Nat.Coprime.coprime_dvd_right hψker hker
  set Λ := barM H L with hΛ
  obtain ⟨ρ, hρ⟩ := exists_conjAction (H := H) (L := L) hStabH inf_le_right
  have hΛC : IsComponentOf Λ ⊤ := hLH.component
  have hΛcop : p.Coprime (Nat.card ↥Λ) := by
    have hcop : p.Coprime (Nat.card L) := Nat.Coprime.coprime_dvd_right
      (Subgroup.card_dvd_of_le hLN) (glbPrimeCore_coprime p H)
    have hdvd : Nat.card ↥Λ ∣ Nat.card L := by
      have := Subgroup.card_map_dvd (L.subgroupOf H) (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLH.le).toEquiv] at this
    exact Nat.Coprime.coprime_dvd_right hdvd hcop
  have hperfΛ : Group.IsPerfect ↥Λ := ⟨hΛC.2.2.1⟩
  have : Group.IsSolvable (Outer (↥Λ ⧸ Subgroup.center ↥Λ)) :=
    hSch _ hΛC.2.2.2 (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      _ hΛC.2.2) (hpair.isCatalogGroup_barM_center_quotient hLH)
  have hout : Group.IsSolvable (Outer ↥Λ) := solvable_of_centerQuotient ↥Λ
  rintro _ ⟨xm, hxm, rfl⟩ _ ⟨lm, hlm, rfl⟩
  have hxX : (xm : G) ∈ X := Subgroup.mem_subgroupOf.mp hxm
  have hlL : (lm : G) ∈ L := Subgroup.mem_subgroupOf.mp hlm
  have hxH : (xm : G) ∈ H := hH₁H (hXH₁ hxX)
  have hlH : (lm : G) ∈ H := hLH.le hlL
  have hxp : IsPGroup p (Subgroup.zpowers (xm : G)) :=
    hpair.isPGroup_R.to_le (Subgroup.zpowers_le.mpr (hXR hxX))
  have hxn : (xm : G) ∈ Subgroup.normalizer (L : Set G) :=
    hpair.mem_normalizer_of_isPGroup hD1 hα hLH hLN hp5 hxH hxp
  have hxStab : (xm : G) ∈ Stab := ⟨hXH₁ hxX, hxn⟩
  have hxp' : IsPGroup p (Subgroup.zpowers (⟨(xm : G), hxStab⟩ : Stab)) := by
    obtain ⟨k, hk⟩ := hxp ⟨(xm : G), Subgroup.mem_zpowers _⟩
    have hk' : (xm : G) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact isPGroup_zpowers_of_pow_eq_one (Subtype.ext (by simpa using hk'))
  have hρ1 : ρ ⟨(xm : G), hxStab⟩ = 1 :=
    map_eq_one_of_surjective_simple _ hψ hnab hψcop hΛcop hout ρ hxp'
  set mkH := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmkH
  have hw : mkH ⟨(lm : G), hlH⟩ ∈ Λ := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL)
  have h1 := hρ ⟨(xm : G), hxStab⟩ ⟨_, hw⟩
  rw [hρ1] at h1
  have h1' : mkH ⟨(xm : G), hxH⟩ * mkH ⟨(lm : G), hlH⟩ * (mkH ⟨(xm : G), hxH⟩)⁻¹ =
      mkH ⟨(lm : G), hlH⟩ := h1.symm
  have hcH : mkH (⟨(xm : G), hxH⟩ * ⟨(lm : G), hlH⟩ * (⟨(xm : G), hxH⟩)⁻¹ *
      (⟨(lm : G), hlH⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1', mul_inv_cancel]
  have hcS : (xm : G) * lm * (xm : G)⁻¹ * (lm : G)⁻¹ ∈ pCoreOf 2 H :=
    (mk_eq_one_iff_coe_mem_pCoreOf _).mp hcH
  have hcL : (xm : G) * lm * (xm : G)⁻¹ * (lm : G)⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hxn lm).mp hlL) (L.inv_mem hlL)
  have hcQ : (xm : G) * lm * (xm : G)⁻¹ * (lm : G)⁻¹ ∈ pCoreOf 2 M := by
    have hmem : (xm : G) * lm * (xm : G)⁻¹ * (lm : G)⁻¹ ∈ L ⊓ pCoreOf 2 H := ⟨hcL, hcS⟩
    rw [hpair.inf_twoCore_H_eq hL hLH.le] at hmem
    exact hmem.2
  have hcM := (mk_eq_one_iff_coe_mem_pCoreOf (xm * lm * xm⁻¹ * lm⁻¹)).mpr hcQ
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hcM
  refine (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [commutatorElement_def]
  exact hcM

theorem D2L2Data.barM_le_centralizer_of_le_inf [Fact p.Prime] (h : D2L2Data p M H R X)
    (hsec : D2SimpleSection p H X) (hD1 : D1For G) (hp5 : 5 ≤ p) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hLK : L ≤ H ⊓ M) : barM M X ≤ Subgroup.centralizer (barM M L : Set _) :=
  h.pair.barM_le_centralizer_of_simpleSection h.eq_R.le h.perfect_le hsec hD1 hp5 hα hSch hL hLK

end Main

section Escape

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.simpleSection_of_psl2 [Fact p.Prime] (h : D2Escape p P M A H R)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) : D2SimpleSection p H A := by
  set O := primeComplementCore (G := H) p with hO
  set mk := QuotientGroup.mk' O with hmk
  set H₁ : Subgroup G := (K.comap mk).map H.subtype with hH₁
  have hH₁H : H₁ ≤ H := Subgroup.map_subtype_le _
  have hmemK : ∀ g : H₁, mk ⟨g.1, hH₁H g.2⟩ ∈ K := by
    rintro ⟨_, ⟨k, hk, rfl⟩⟩
    exact hk
  let φ : ↥H₁ →* ↥K :=
    { toFun := fun g => ⟨mk ⟨g.1, hH₁H g.2⟩, hmemK g⟩
      map_one' := Subtype.ext (map_one mk)
      map_mul' := fun a b => Subtype.ext (map_mul mk ⟨a.1, hH₁H a.2⟩ ⟨b.1, hH₁H b.2⟩) }
  have : IsSimpleGroup (PSL2GF p 2) := isSimpleGroup_psl2GF_of_two_le le_rfl
  have hp3 : 3 ≤ p := by have := h.prime.two_le; have := h.ne_two; omega
  have hAK : (A.subgroupOf H).map mk ≤ K := hK.A_le_of_psl2 e
  have hK6 : 6 < Nat.card K := by
    have := Subgroup.card_le_of_le hAK
    rw [hK.card_A] at this
    nlinarith
  refine ⟨K, inferInstance, inferInstance, H₁, φ, hH₁H, fun a ha => ?_, fun κ => ?_,
    e.isSimpleGroup, hK6, ?_, ?_⟩
  · exact ⟨⟨a, h.A_le_H ha⟩, hAK ⟨⟨a, h.A_le_H ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩, rfl⟩
  · obtain ⟨hh, hhκ⟩ := QuotientGroup.mk'_surjective O κ.1
    have hhK : hh ∈ K.comap mk := by
      show mk hh ∈ K
      rw [hmk, hhκ]
      exact κ.2
    exact ⟨⟨(hh : G), ⟨hh, hhK, rfl⟩⟩, Subtype.ext hhκ⟩
  · have hcen : Subgroup.center K = ⊥ := hK.center_eq_bot
    let e' : K ≃* K ⧸ Subgroup.center K :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
        hK.component.2.2
    refine ⟨e'.symm a, e'.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e' hba
  · have hle : (φ.ker).map H₁.subtype ≤ GLBPrimeCore p H := by
      rintro _ ⟨g, hg, rfl⟩
      have h1 : mk ⟨g.1, hH₁H g.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      rw [glbPrimeCore_eq_primeComplementCoreOf p H]
      exact ⟨⟨g.1, hH₁H g.2⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
    rw [← Subgroup.card_map_of_injective H₁.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle) (glbPrimeCore_coprime p H)

theorem D2Escape.barM_le_centralizer_of_le_inf [Fact p.Prime] (h : D2Escape p P M A H R)
    (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* PSL2GF p 2) (hD1 : D1For G) (hp5 : 5 ≤ p) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier) {L : Subgroup G} (hL : IsTwoPrimeComponent M L)
    (hLK : L ≤ H ⊓ M) : barM M A ≤ Subgroup.centralizer (barM M L : Set _) :=
  (h.l2Data_of_psl2 hglob hRbar hK e).barM_le_centralizer_of_le_inf
    (h.simpleSection_of_psl2 hK e) hD1 hp5 hα hSch hL hLK

end Escape

end CFSG.AGLEmbeddingD2
