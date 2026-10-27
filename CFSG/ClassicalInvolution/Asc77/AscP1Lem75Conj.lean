module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G]

theorem conjSub_normalizer (g : G) (K : Subgroup G) :
    Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) =
      conjSub g (Subgroup.normalizer (K : Set G)) := by
  ext x
  rw [mem_conjSub_iff, mem_normalizer_iff_conjSub_eq, mem_normalizer_iff_conjSub_eq]
  constructor
  · intro h
    rw [show conjSub (g⁻¹ * x * g) K = conjSub g⁻¹ (conjSub x (conjSub g K)) by
      rw [← conjSub_mul, ← conjSub_mul, mul_assoc]]
    rw [h, conjSub_inv_conjSub]
  · intro h
    have h' : conjSub x (conjSub g K) = conjSub g (conjSub (g⁻¹ * x * g) K) := by
      rw [← conjSub_mul, ← conjSub_mul]
      congr 1
      group
    rw [h', h]

theorem conjSub_centralizer_conjSub (g : G) (W : Subgroup G) :
    conjSub g (Subgroup.centralizer (W : Set G)) =
      Subgroup.centralizer ((conjSub g W : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have hw' : g⁻¹ * w * g ∈ W := mem_conjSub_iff.mp hw
    have := h _ hw'
    calc w * x = g * ((g⁻¹ * w * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * w * g)) * g⁻¹ := by rw [this]
      _ = x * w := by group
  · intro h w hw
    have hw' : g * w * g⁻¹ ∈ conjSub g W := conj_mem_conjSub hw
    have := h _ hw'
    calc w * (g⁻¹ * x * g) = g⁻¹ * ((g * w * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * w * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * x * g) * w := by group

theorem conjSub_OCW (g : G) (W : Subgroup G) : conjSub g (OCW W) = OCW (conjSub g W) := by
  unfold OCW
  rw [← conjSub_centralizer_conjSub, oddCoreOf_conjSub_eq]

theorem conjSub_sup_OCW (g : G) (W : Subgroup G) :
    conjSub g (W ⊔ OCW W) = conjSub g W ⊔ OCW (conjSub g W) := by
  rw [conjSub_sup, conjSub_OCW]

@[expose] noncomputable def normalizerConj (g : G) {K K' : Subgroup G} (h : conjSub g K = K') :
    ↥(Subgroup.normalizer (K : Set G)) ≃* ↥(Subgroup.normalizer (K' : Set G)) :=
  (Subgroup.equivMapOfInjective _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr (by
      show conjSub g (Subgroup.normalizer (K : Set G)) = _
      rw [← h, conjSub_normalizer]))

theorem coe_normalizerConj (g : G) {K K' : Subgroup G} (h : conjSub g K = K')
    (x : ↥(Subgroup.normalizer (K : Set G))) :
    ((normalizerConj g h x : ↥(Subgroup.normalizer (K' : Set G))) : G) = g * (x : G) * g⁻¹ :=
  rfl

theorem map_subgroupOf_normalizerConj (g : G) {K K' : Subgroup G} (h : conjSub g K = K') :
    (K.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (normalizerConj g h : ↥(Subgroup.normalizer (K : Set G)) →* _) =
      K'.subgroupOf (Subgroup.normalizer (K' : Set G)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ K := hx
    show ((normalizerConj g h x : ↥(Subgroup.normalizer (K' : Set G))) : G) ∈ K'
    rw [coe_normalizerConj, ← h]
    exact conj_mem_conjSub hx'
  · intro hy
    have hy' : (y : G) ∈ K' := hy
    refine ⟨(normalizerConj g h).symm y, ?_, (normalizerConj g h).apply_symm_apply y⟩
    show (((normalizerConj g h).symm y : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ K
    have h1 : (((normalizerConj g h) ((normalizerConj g h).symm y) :
        ↥(Subgroup.normalizer (K' : Set G))) : G) = (y : G) := by
      rw [(normalizerConj g h).apply_symm_apply]
    rw [coe_normalizerConj] at h1
    have hy'' : (y : G) ∈ conjSub g K := by rw [h]; exact hy'
    have h2 := mem_conjSub_iff.mp hy''
    have h3 : g⁻¹ * (y : G) * g = (((normalizerConj g h).symm y : _) : G) := by
      rw [← h1]
      group
    rw [← h3]
    exact h2

@[expose] noncomputable def nquotConj (g : G) {K K' : Subgroup G} (h : conjSub g K = K') :
    NQuot K ≃* NQuot K' :=
  QuotientGroup.congr (K.subgroupOf (Subgroup.normalizer (K : Set G)))
    (K'.subgroupOf (Subgroup.normalizer (K' : Set G))) (normalizerConj g h)
    (map_subgroupOf_normalizerConj g h)

theorem nquotConj_mk (g : G) {K K' : Subgroup G} (h : conjSub g K = K')
    (x : ↥(Subgroup.normalizer (K : Set G))) :
    nquotConj g h (QuotientGroup.mk' (K.subgroupOf (Subgroup.normalizer (K : Set G))) x) =
      QuotientGroup.mk' (K'.subgroupOf (Subgroup.normalizer (K' : Set G)))
        (normalizerConj g h x) :=
  QuotientGroup.congr_mk _ _ _ (map_subgroupOf_normalizerConj g h) _

theorem nquotConj_piG (g : G) (W : Subgroup G) {m : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) :
    nquotConj g (conjSub_sup_OCW g W) (piG W m) = piG (conjSub g W) (g * m * g⁻¹) := by
  have hm' : g * m * g⁻¹ ∈ Subgroup.normalizer ((conjSub g W : Subgroup G) : Set G) := by
    rw [conjSub_normalizer]
    exact conj_mem_conjSub hm
  rw [piG_of_mem hm, piG_of_mem hm']
  show nquotConj g (conjSub_sup_OCW g W) (QuotientGroup.mk' _
      (Subgroup.inclusion (normalizer_le_normalizer_sup W) ⟨m, hm⟩)) =
    QuotientGroup.mk' _ (Subgroup.inclusion (normalizer_le_normalizer_sup (conjSub g W))
      ⟨g * m * g⁻¹, hm'⟩)
  rw [nquotConj_mk]
  rfl

section Mu

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem conjSub_mem_DSet_conj (hΩ : HypOmegaMod p f Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W)
    (g : G) : conjSub g R ∈ DSet Ω (conjSub g W) := by
  refine ⟨conjSub_mem_RSet hΩ hR.1 g, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 := hR.2 hx
  rw [conjSub_normalizer, mem_conjSub_iff]
  exact h1

theorem conjSub_MGrp (hΩ : HypOmegaMod p f Ω) (g : G) (W : Subgroup G) :
    conjSub g (MGrp Ω W) = MGrp Ω (conjSub g W) := by
  apply le_antisymm
  · unfold MGrp
    rw [conjSub, Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    exact le_iSup₂ (f := fun R (_ : R ∈ DSet Ω (conjSub g W)) => R) (conjSub g R)
      (conjSub_mem_DSet_conj hΩ hR g)
  · refine iSup₂_le fun R hR => ?_
    have hR' : conjSub g⁻¹ R ∈ DSet Ω W := by
      have := conjSub_mem_DSet_conj hΩ hR g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h1 : conjSub g⁻¹ R ≤ MGrp Ω W := le_MGrp_of_mem_D hR'
    have h2 := conjSub_mono (n := g) h1
    rwa [conjSub_conjSub_inv] at h2

noncomputable def muGroupConjEquiv (hΩ : HypOmegaMod p f Ω) (g : G) (W : Subgroup G) :
    ↥(muGroup Ω W) ≃* ↥(muGroup Ω (conjSub g W)) :=
  (MulEquiv.subgroupMap (nquotConj g (conjSub_sup_OCW g W)) (muGroup Ω W)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      constructor
      · rintro ⟨q₀, hq₀, rfl⟩
        obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq₀
        have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
        show nquotConj g (conjSub_sup_OCW g W) (piG W m) ∈ _
        rw [nquotConj_piG g W hmN]
        refine piG_mem_muGroup ?_
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← conjSub_sup]
        exact conj_mem_conjSub hm
      · intro hq
        obtain ⟨m', hm', rfl⟩ := mem_muGroup_iff.mp hq
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← conjSub_sup, mem_conjSub_iff] at hm'
        refine ⟨piG W (g⁻¹ * m' * g), piG_mem_muGroup hm', ?_⟩
        have hmN : g⁻¹ * m' * g ∈ Subgroup.normalizer (W : Set G) :=
          MGrp_sup_le_normalizer Ω W hm'
        show nquotConj g (conjSub_sup_OCW g W) (piG W (g⁻¹ * m' * g)) = _
        rw [nquotConj_piG g W hmN]
        congr 1
        group))

end Mu

end Thompson

end CFSG.ClassicalInvolution.Asc77
