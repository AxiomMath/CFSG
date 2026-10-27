module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128Cop

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Bender.Thm2
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def toHBar (z : G) {H : Subgroup G} (h : Cen z ≤ H) : ↥(Cen z) →* HBar H :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥H)).comp (Subgroup.inclusion h)

omit [Finite G] in
theorem toHBar_apply (z : G) {H : Subgroup G} (h : Cen z ≤ H) (c : ↥(Cen z)) :
    toHBar z h c = (QuotientGroup.mk ⟨c, h c.2⟩ : HBar H) := rfl

theorem toHBar_surjective {z : G} {H : Subgroup G} (hz2 : z * z = 1) (hc : CentMod H z) (h : Cen z ≤ H) :
    Function.Surjective (toHBar z h) := by
  intro x
  obtain ⟨c, hcz, hcx⟩ := L128.surj_of_centMod hz2 hc x
  exact ⟨⟨c, hcz⟩, hcx⟩

theorem ker_toHBar {z : G} {H : Subgroup G} (hz2 : z * z = 1) (hc : CentMod H z) (h : Cen z ≤ H) :
    (toHBar z h).ker = pPrimeCore 2 ↥(Cen z) := by
  ext c
  rw [MonoidHom.mem_ker, toHBar_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hcH
    have h1 : (c : G) ∈ pPrimeCoreOf 2 H := L128.mem_pPrimeCoreOf_iff.mpr hcH
    exact L128.mem_pPrimeCoreOf_iff.mp (L128.pPrimeCoreOf_inf_le h (Subgroup.mem_inf.mpr ⟨h1, c.2⟩))
  · intro hcC
    have h1 : (c : G) ∈ pPrimeCoreOf 2 (Cen z) := L128.mem_pPrimeCoreOf_iff.mpr hcC
    have h2 : pPrimeCoreOf 2 (Cen z) ≤ pPrimeCoreOf 2 H :=
      L129.le_pPrimeCoreOf_of_normalized (Y := H) (D := pPrimeCoreOf 2 (Cen z)) (Y₀ := Cen z)
        ((L128.pPrimeCoreOf_le (Cen z)).trans h) h
        (fun d hd => L129.odd_orderOf_of_mem_pPrimeCoreOf hd)
        (fun y hy d hd => (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_pPrimeCoreOf (Cen z) hy) d).mp hd)
        (fun y hy => by
          obtain ⟨c', hc', o, ho, hco⟩ := L128.exists_centralizer_mul hz2 hy (hc y hy)
          exact ⟨c', (Subgroup.mem_inf.mp hc').2, o, ho, hco⟩)
    exact L128.mem_pPrimeCoreOf_iff.mp (h2 h1)

@[expose] noncomputable def barEquiv {z : G} {H : Subgroup G} (hz2 : z * z = 1) (hc : CentMod H z) (h : Cen z ≤ H) :
    CentralizerBar z ≃* HBar H :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toHBar hz2 hc h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toHBar z h) (toHBar_surjective hz2 hc h))

theorem barEquiv_toBar {z : G} {H : Subgroup G} (hz2 : z * z = 1) (hc : CentMod H z) (h : Cen z ≤ H)
    (c : ↥(Cen z)) : barEquiv hz2 hc h (toBar z c) = (QuotientGroup.mk ⟨c, h c.2⟩ : HBar H) := rfl


omit [Finite G] in
theorem mk_mem_normalizer_barIn {H X : Subgroup G} {c : ↥H} (hc : (c : G) ∈ normalizer (X : Set G)) :
    (QuotientGroup.mk c : HBar H) ∈
      normalizer ((barIn H X : Subgroup (HBar H)) : Set (HBar H)) := by
  have fwd : ∀ c : ↥H, (c : G) ∈ normalizer (X : Set G) → ∀ y ∈ barIn H X,
      (QuotientGroup.mk c : HBar H) * y * (QuotientGroup.mk c)⁻¹ ∈ barIn H X := by
    intro c hc y hy
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨c * y' * c⁻¹, ?_, ?_⟩
    · have : (c : G) * (y' : G) * (c : G)⁻¹ ∈ X := ((mem_normalizer_iff.mp hc) (y' : G)).mp hy'
      exact this
    · simp
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fwd c hc y
  · intro hy
    have hc' : ((c⁻¹ : ↥H) : G) ∈ normalizer (X : Set G) := by
      have := (normalizer (X : Set G)).inv_mem hc
      simpa using this
    have := fwd c⁻¹ hc' _ hy
    simpa [mul_assoc] using this


theorem le_oddCore_of_star {z t : G} (hz2 : z * z = 1) (ht2 : t * t = 1)
    {H : Subgroup G} (h : Cen z ≤ H) (hc : CentMod H z) (ht : t ∈ Cen z) {p : ℕ} {X : Subgroup G}
    (hXH : X ≤ H) (hXp : IsPGroup p ↥X)
    (hXinv : ∀ c ∈ H, c ∈ centralizer ({t} : Set G) → c ∈ normalizer (X : Set G))
    (hXcomm : ⁅X, zpowers t⁆ = X)
    (hstar : ∀ Y : Subgroup (CentralizerBar z), IsPGroup p ↥Y →
        (∀ c : CentralizerBar z, c * toBar z ⟨t, ht⟩ = toBar z ⟨t, ht⟩ * c →
          c ∈ normalizer (Y : Set (CentralizerBar z))) →
        ⁅Y, zpowers (toBar z ⟨t, ht⟩)⁆ = Y → Y = ⊥) :
    X ≤ pPrimeCoreOf 2 H := by
  classical
  set e : CentralizerBar z ≃* HBar H := barEquiv hz2 hc h with he
  have htH : t ∈ H := h ht
  set Xb : Subgroup (HBar H) := barIn H X with hXb
  set Y : Subgroup (CentralizerBar z) := Xb.map e.symm.toMonoidHom with hY
  have hmemY : ∀ y, y ∈ Y ↔ e y ∈ Xb := by
    intro y
    rw [hY, Subgroup.mem_map_equiv]
    simp
  have hYp : IsPGroup p ↥Y := by
    have h1 : IsPGroup p ↥(X.subgroupOf H) :=
      hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
    exact (h1.map (QuotientGroup.mk' (pPrimeCore 2 ↥H))).map _
  have hnormY : ∀ c' : CentralizerBar z, c' * toBar z ⟨t, ht⟩ = toBar z ⟨t, ht⟩ * c' →
      c' ∈ normalizer (Y : Set (CentralizerBar z)) := by
    intro c' hcomm
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective c'
    have h1 : ⁅c₀, (⟨t, ht⟩ : ↥(Cen z))⁆ ∈ pPrimeCore 2 ↥(Cen z) := by
      have h0 : (toBar z) ⁅c₀, (⟨t, ht⟩ : ↥(Cen z))⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
      exact (QuotientGroup.eq_one_iff _).mp h0
    have h2 : ⁅c₀, (⟨t, ht⟩ : ↥(Cen z))⁆ ∈ (toHBar z h).ker := by
      rw [ker_toHBar hz2 hc h]
      exact h1
    have h3 : ⁅(c₀ : G), t⁆ ∈ pPrimeCoreOf 2 H := by
      rw [MonoidHom.mem_ker, toHBar_apply, QuotientGroup.eq_one_iff] at h2
      exact L128.mem_pPrimeCoreOf_iff.mpr h2
    obtain ⟨c, hcmem, o, ho, hco⟩ := L128.exists_centralizer_mul ht2 (h c₀.2) h3
    have hcN : c ∈ normalizer (X : Set G) := hXinv c (Subgroup.mem_inf.mp hcmem).1 (Subgroup.mem_inf.mp hcmem).2
    have hcH : c ∈ H := (Subgroup.mem_inf.mp hcmem).1
    have hoH : o ∈ H := L128.pPrimeCoreOf_le H ho
    have hec : e (QuotientGroup.mk c₀) = (QuotientGroup.mk (⟨c, hcH⟩ : ↥H) : HBar H) := by
      have hc₀ : (⟨c₀, h c₀.2⟩ : ↥H) = ⟨c, hcH⟩ * ⟨o, hoH⟩ := Subtype.ext hco
      show barEquiv hz2 hc h (toBar z c₀) = _
      rw [barEquiv_toBar, hc₀, QuotientGroup.mk_mul]
      have : (QuotientGroup.mk (⟨o, hoH⟩ : ↥H) : HBar H) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (L128.mem_pPrimeCoreOf_iff.mp ho)
      rw [this, mul_one]
    have hcn : (QuotientGroup.mk (⟨c, hcH⟩ : ↥H) : HBar H) ∈ normalizer ((Xb : Subgroup (HBar H)) : Set (HBar H)) :=
      mk_mem_normalizer_barIn (X := X) hcN
    rw [mem_normalizer_iff] at hcn ⊢
    intro y
    rw [hmemY, hmemY, map_mul, map_mul, map_inv]
    have : e (QuotientGroup.mk c₀ : CentralizerBar z) = QuotientGroup.mk (⟨c, hcH⟩ : ↥H) := hec
    rw [this]
    exact hcn (e y)
  have hcommY : ⁅Y, zpowers (toBar z ⟨t, ht⟩)⁆ = Y := by
    have h1 : ⁅X.subgroupOf H, zpowers (⟨t, htH⟩ : ↥H)⁆ = X.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hXH]
      simpa using hXcomm
    have h2 : ⁅Xb, zpowers (e (toBar z ⟨t, ht⟩))⁆ = Xb := by
      have : e (toBar z ⟨t, ht⟩) = QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨t, htH⟩ := rfl
      rw [this, ← MonoidHom.map_zpowers, hXb, barIn, ← Subgroup.map_commutator, h1]
    have h3 : zpowers (toBar z ⟨t, ht⟩) = (zpowers (e (toBar z ⟨t, ht⟩))).map e.symm.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp
    rw [h3, hY, ← Subgroup.map_commutator, h2]
  have hbot := hstar Y hYp hnormY hcommY
  intro x hx
  have hxH : x ∈ H := hXH hx
  have hmem : (⟨x, hxH⟩ : ↥H) ∈ X.subgroupOf H := hx
  have hx1 : (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hxH⟩ : HBar H) ∈ Xb := ⟨_, hmem, rfl⟩
  have : e.symm (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hxH⟩) ∈ Y := ⟨_, hx1, rfl⟩
  rw [hbot, Subgroup.mem_bot, map_eq_one_iff e.symm e.symm.injective] at this
  exact L128.mem_pPrimeCoreOf_iff.mpr ((QuotientGroup.eq_one_iff _).mp this)

end CFSG.GH74.GLS.Stage2.Signalizer.L48
