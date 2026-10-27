module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma114Layer
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma114
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma114Full

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

@[expose] def Input18_5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ Q : Subgroup X, IsPGroup p ↥Q →
      GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set X)) ≤
        Lemma114Layer.layerOf X ⊔ ⨆ (Q' : Subgroup X) (_ : IsSylowIn p (Lemma114Layer.layerOf X) Q'),
          GLAPPrimeCoreOf p (Subgroup.centralizer (Q' : Set X))

theorem comm_of_neg {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {H M X : Subgroup G}
    (hN : ∀ K : Subgroup G, GLAPComponent p H K →
      ⁅barX p H K, barX p H X⁆ ≠ ⊥ → barX p H K ≤ barX p H (M ⊓ H))
    (K : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H)) (hK : IsComponentOf K ⊤)
    (hKC : ¬ K ≤ barX p H (M ⊓ H)) :
    ∀ k ∈ K, ∀ x ∈ barX p H X, k * x = x * k := by
  obtain ⟨L, hL, hLK⟩ := exists_glaPComponent_barX_eq (p := p) H hK
  have hcomm : ⁅K, barX p H X⁆ = ⊥ := by
    by_contra hne
    apply hKC
    rw [← hLK]
    apply hN L hL
    rw [hLK]
    exact hne
  intro k hk x hx
  have hmem : k * x * k⁻¹ * x⁻¹ ∈ ⁅K, barX p H X⁆ := Subgroup.commutator_mem_commutator hk hx
  rw [hcomm, Subgroup.mem_bot] at hmem
  calc k * x = (k * x * k⁻¹ * x⁻¹) * (x * k) := by group
    _ = x * k := by rw [hmem, one_mul]

theorem isoInvariant_isCatalogGroup_of :
    CFSG.KCore.IsoInvariant (@CFSG.Open.IsCatalogGroup) := by
  intro X Y _ _ e h
  obtain ⟨i, ⟨f⟩⟩ := h
  exact ⟨i, ⟨e.trans f⟩⟩

theorem isKGroup_quotient_pPrime {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G}
    (hH : CFSG.Open.IsKGroup ↥H) : CFSG.Open.IsKGroup (↥H ⧸ GLAPPrimeCore p ↥H) :=
  CFSG.KCore.KGroupNonab.quotient isoInvariant_isCatalogGroup_of hH (GLAPPrimeCore p ↥H)

theorem exists_sylow_layer_normalized {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    {T : Subgroup Y} (hT : IsPGroup p ↥T) :
    ∃ Q : Subgroup Y, IsSylowIn p (Lemma114Layer.layerOf Y) Q ∧
      ∀ y ∈ T, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := by
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hT
  have hS' : IsSylowIn p (⊤ : Subgroup Y) (S : Subgroup Y) :=
    ⟨le_top, S.isPGroup', fun {R} _ hR hle => S.is_maximal' hR hle⟩
  have hNn : ∀ g ∈ (⊤ : Subgroup Y), ∀ x ∈ Lemma114Layer.layerOf Y,
      g * x * g⁻¹ ∈ Lemma114Layer.layerOf Y := by
    intro g _ x hx
    haveI := Lemma114Layer.layerOf_normal (Y := Y)
    exact Subgroup.Normal.conj_mem inferInstance x hx g
  refine ⟨(S : Subgroup Y) ⊓ Lemma114Layer.layerOf Y, ⟨inf_le_right, ?_, ?_⟩, ?_⟩
  · exact Lemma114Layer.isPGroup_of_le' S.isPGroup' inf_le_left
  · intro R hR hRp hle
    exact Lemma114Layer.sylow_inter_normal hS' le_top hNn R hR hRp hle
  · intro y hy x hx
    have hyS : y ∈ (S : Subgroup Y) := hS hy
    have hxS : x ∈ (S : Subgroup Y) := hx.1
    have hxL : x ∈ Lemma114Layer.layerOf Y := hx.2
    refine ⟨S.mul_mem (S.mul_mem hyS hxS) (S.inv_mem hyS), ?_⟩
    haveI := Lemma114Layer.layerOf_normal (Y := Y)
    exact Subgroup.Normal.conj_mem inferInstance x hxL y

theorem le_of_hyperplanes {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    {Z Ebar C0 : Subgroup Y} (hEb : IsElemAbelian p Ebar) (hEr : 3 ≤ CFSG.Open.pRank p Ebar)
    (hEZ : Ebar ≤ Subgroup.normalizer (Z : Set Y)) (hZcop : Nat.Coprime p (Nat.card ↥Z))
    (hC : ∀ B : Subgroup Y, B ≤ Ebar → Nat.card ↥B * p = Nat.card ↥Ebar →
      ∀ z ∈ Z, (∀ b ∈ B, b * z = z * b) → z ∈ C0) :
    Z ≤ C0 := by
  classical
  haveI : CFSG.IsElementaryAbelian p ↥Ebar := CFSG.Open.IsElemAbelian.isElementaryAbelian hEb
  letI : MulDistribMulAction ↥Ebar ↥Z :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer Ebar Z hEZ
  have hnontriv : Nontrivial ↥Ebar := by
    obtain ⟨E₀, hE₀le, _, hE₀card⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt Ebar
    have h1 : 1 < Nat.card ↥E₀ := by
      rw [hE₀card]
      have : p ^ 1 ≤ p ^ CFSG.Open.pRank p Ebar := Nat.pow_le_pow_right hp.out.pos (by omega)
      exact lt_of_lt_of_le (by simpa using hp.out.one_lt) this
    have h2 : Nat.card ↥E₀ ≤ Nat.card ↥Ebar := Subgroup.card_le_of_le hE₀le
    exact Finite.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le h1 h2)
  have hcop : ¬ p ∣ Nat.card ↥Z := fun h => (Nat.Prime.coprime_iff_not_dvd hp.out).1 hZcop h
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := ↥Ebar) (H := ↥Z) hcop
  have hsub : (⨆ (B : Subgroup ↥Ebar) (_ : B.index = p), CFSG.fixedPointSubgroup B ↥Z) ≤
      C0.subgroupOf Z := by
    refine iSup₂_le fun B hB => ?_
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hcomm : ∀ b ∈ B.map Ebar.subtype, b * (y : Y) = (y : Y) * b := by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      have hfix := (FixedPoints.mem_subgroup _ _ _).mp hy ⟨b', hb'⟩
      have hval : (b' : Y) * (y : Y) * (b' : Y)⁻¹ = (y : Y) :=
        congrArg (fun z : ↥Z => (z : Y)) hfix
      have h2 : (b' : Y) * (y : Y) = (y : Y) * (b' : Y) := by
        calc (b' : Y) * (y : Y) = ((b' : Y) * (y : Y) * (b' : Y)⁻¹) * (b' : Y) := by group
          _ = (y : Y) * (b' : Y) := by rw [hval]
      exact h2
    have hcard : Nat.card ↥(B.map Ebar.subtype) * p = Nat.card ↥Ebar := by
      rw [Subgroup.card_map_of_injective Ebar.subtype_injective, mul_comm]
      have h1 := Subgroup.index_mul_card (H := B)
      rw [hB] at h1
      exact h1
    exact hC (B.map Ebar.subtype) (Subgroup.map_subtype_le B) hcard (y : Y) y.2 hcomm
  have htop : (⊤ : Subgroup ↥Z) ≤ C0.subgroupOf Z := by
    rw [← hgen]
    exact hsub
  intro z hz
  exact Subgroup.mem_subgroupOf.mp (htop (Subgroup.mem_top (⟨z, hz⟩ : ↥Z)))

theorem l114f_isPGroup_elemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsPGroup p ↥E := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hE.2 g hg)
  rw [Subgroup.orderOf_mk]
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hd with h1 | h1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h1, pow_one]⟩

theorem l114f_card_eq_pow_pRank {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {E : Subgroup G} (hE : IsElemAbelian p E) : Nat.card E = p ^ CFSG.Open.pRank p E := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (l114f_isPGroup_elemAbelian hE)
  unfold CFSG.Open.pRank
  have hgr : IsGreatest {k | ∃ F : Subgroup G, F ≤ E ∧ IsElemAbelian p F ∧ Nat.card F = p ^ k} n := by
    refine ⟨⟨E, le_rfl, hE, hn⟩, ?_⟩
    rintro k ⟨F, hFE, -, hFk⟩
    have hle : p ^ k ≤ p ^ n := by
      rw [← hFk, ← hn]
      exact Subgroup.card_le_of_le hFE
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hle
  rw [hgr.csSup_eq, hn]

theorem l114f_isPGroup_barX {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {C S : Subgroup G}
    (hSC : S ≤ C) (hS : IsPGroup p ↥S) : IsPGroup p ↥(barX p C S) := by
  unfold barX
  exact (hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm).map _

theorem l114f_barX_mono {G : Type} [Group G] {p : ℕ} {C S T : Subgroup G} (h : S ≤ T) :
    barX p C S ≤ barX p C T := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx)), rfl⟩

theorem l114f_isPGroup_zpowers {Y : Type} [Group Y] {p : ℕ} [hp : Fact p.Prime] {g : Y}
    (hg : g ^ p = 1) : IsPGroup p ↥(Subgroup.zpowers g) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have hx : (x : Y) ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  simpa [pow_one] using hx

theorem l114f_sylow_glbConj {Y : Type} [Group Y] [Finite Y] {p : ℕ} [hp : Fact p.Prime]
    {L Q₁ Q₂ : Subgroup Y} (h₁ : IsSylowIn p L Q₁) (h₂ : IsSylowIn p L Q₂) :
    ∃ h ∈ L, GLBConj h Q₁ = Q₂ := by
  classical
  have hmax : ∀ Q : Subgroup Y, IsSylowIn p L Q → ∀ R : Subgroup ↥L, IsPGroup p ↥R →
      Q.subgroupOf L ≤ R → R = Q.subgroupOf L := by
    intro Q hQ R hR hle
    have hRL : R.map L.subtype ≤ L := Subgroup.map_subtype_le R
    have hRp : IsPGroup p ↥(R.map L.subtype) :=
      hR.of_equiv (Subgroup.equivMapOfInjective R L.subtype L.subtype_injective)
    have hQR : Q ≤ R.map L.subtype := by
      intro q hq
      exact Subgroup.mem_map.2 ⟨⟨q, hQ.1 hq⟩, hle (Subgroup.mem_subgroupOf.2 hq), rfl⟩
    have heq : R.map L.subtype = Q := hQ.2.2 _ hRL hRp hQR
    apply le_antisymm
    · intro r hr
      exact Subgroup.mem_subgroupOf.2 (by rw [← heq]; exact Subgroup.mem_map.2 ⟨r, hr, rfl⟩)
    · intro r hr
      have hrY : (r : Y) ∈ R.map L.subtype := by
        rw [heq]; exact Subgroup.mem_subgroupOf.1 hr
      obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.1 hrY
      have hxr' : x = r := Subtype.ext hxr
      rw [← hxr']; exact hx
  let S₁ : Sylow p ↥L := ⟨Q₁.subgroupOf L, Lemma114Layer.isPGroup_subgroupOf_of_le h₁.2.1 h₁.1,
    fun {R} hR hle => hmax Q₁ h₁ R hR hle⟩
  let S₂ : Sylow p ↥L := ⟨Q₂.subgroupOf L, Lemma114Layer.isPGroup_subgroupOf_of_le h₂.2.1 h₂.1,
    fun {R} hR hle => hmax Q₂ h₂ R hR hle⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L S₁ S₂
  refine ⟨(g : Y)⁻¹, L.inv_mem g.2, ?_⟩
  ext y
  simp only [GLBConj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxL : x ∈ L := h₁.1 hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ ((S₁ : Sylow p ↥L) : Subgroup ↥L) :=
      Subgroup.mem_subgroupOf.2 hx
    have hmem2 : MulAut.conj g • (⟨x, hxL⟩ : ↥L) ∈
        MulAut.conj g • ((S₁ : Sylow p ↥L) : Subgroup ↥L) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ hmem
    rw [← Sylow.coe_subgroup_smul, hg] at hmem2
    have := Subgroup.mem_subgroupOf.1 hmem2
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  · intro hy
    have hyL : y ∈ L := h₂.1 hy
    have hmem : (⟨y, hyL⟩ : ↥L) ∈ ((S₂ : Sylow p ↥L) : Subgroup ↥L) :=
      Subgroup.mem_subgroupOf.2 hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨z, hz, hzeq⟩ := hmem
    refine ⟨z.1, Subgroup.mem_subgroupOf.1 hz, ?_⟩
    have := congrArg (fun w : ↥L => (w : Y)) hzeq
    simpa [MulAut.smul_def, MulAut.conj_apply] using this

theorem l114f_glbConj_mem_sup {Y : Type} [Group Y] {L K : Subgroup Y} {h x : Y} (hh : h ∈ L)
    (hx : x ∈ GLBConj h K) : x ∈ L ⊔ K := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
  have hk' : k ∈ L ⊔ K := Subgroup.mem_sup_right hk
  have hh' : h ∈ L ⊔ K := Subgroup.mem_sup_left hh
  have hh'' : h⁻¹ ∈ L ⊔ K := (L ⊔ K).inv_mem hh'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact (L ⊔ K).mul_mem ((L ⊔ K).mul_mem hh'' hk') hh'

theorem l114f_centralizer_glbConj {Y : Type} [Group Y] (g : Y) (Q : Subgroup Y) :
    Subgroup.centralizer ((GLBConj g Q : Subgroup Y) : Set Y) =
      GLBConj g (Subgroup.centralizer (Q : Set Y)) := by
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.2 ⟨g * x * g⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqg : g⁻¹ * q * g ∈ GLBConj g Q :=
        Subgroup.mem_map.2 ⟨q, hq, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      have hc := Subgroup.mem_centralizer_iff.1 hx _ hqg
      calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
        _ = (g * x * g⁻¹) * q := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hh
    have hqc := Subgroup.mem_centralizer_iff.1 hc q hq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show g⁻¹ * q * g * (g⁻¹ * c * g) = g⁻¹ * (q * c) * g by group,
      show g⁻¹ * c * g * (g⁻¹ * q * g) = g⁻¹ * (c * q) * g by group, hqc]

theorem l114f_glaPPrimeCore_centralizer_glbConj {Y : Type} [Group Y] (p : ℕ) (g : Y)
    (Q : Subgroup Y) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ((GLBConj g Q : Subgroup Y) : Set Y)) =
      GLBConj g (GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set Y))) := by
  rw [l114f_centralizer_glbConj, glaPPrimeCoreOf_gLBConj]

theorem l114f_le_normalizer_glaPPrimeCore_centralizer {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [hp : Fact p.Prime] {T Q S : Subgroup Y} (hQ : ∀ y ∈ T, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q)
    (hST : S ≤ T) :
    S ≤ Subgroup.normalizer (GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set Y)) : Set Y) := by
  have h1 : S ≤ Subgroup.normalizer ((Subgroup.centralizer (Q : Set Y) : Subgroup Y) : Set Y) := by
    apply Lemma114Layer.le_normalizer_of_conj
    intro w hw c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    have hw' : w⁻¹ ∈ T := T.inv_mem (hST hw)
    have hq' : w⁻¹ * q * w⁻¹⁻¹ ∈ Q := hQ w⁻¹ hw' q hq
    rw [inv_inv] at hq'
    have hc' := hc _ hq'
    calc q * (w * c * w⁻¹) = w * ((w⁻¹ * q * w) * c) * w⁻¹ := by group
      _ = w * (c * (w⁻¹ * q * w)) * w⁻¹ := by rw [hc']
      _ = (w * c * w⁻¹) * q := by group
  exact h1.trans (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p _)

theorem l114f_barX_conj_mem {G : Type} [Group G] {p : ℕ} {C W : Subgroup G}
    {d : ↥C} (hd : (d : G) ∈ Subgroup.normalizer (W : Set G)) {n : ↥C ⧸ GLAPPrimeCore p ↥C}
    (hn : n ∈ barX p C W) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) d * n * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) d)⁻¹ ∈
      barX p C W := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hn
  refine Subgroup.mem_map.2 ⟨d * w * d⁻¹, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hd (w : G)).1 (Subgroup.mem_subgroupOf.1 hw)
  · simp only [map_mul, map_inv]

theorem l114f_coprime_barX {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {C W : Subgroup G} (hWC : W ≤ C) (hWp : ¬ p ∣ Nat.card ↥W) :
    Nat.Coprime p (Nat.card ↥(barX p C W)) := by
  have hcopW : Nat.Coprime p (Nat.card ↥W) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hWp
  have hdvd : Nat.card ↥(barX p C W) ∣ Nat.card ↥(W.subgroupOf C) := by
    unfold barX
    exact Subgroup.card_map_dvd (W.subgroupOf C) (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
  have hcard : Nat.card ↥(W.subgroupOf C) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  rw [hcard] at hdvd
  exact Nat.Coprime.coprime_dvd_right hdvd hcopW

theorem l114f_barX_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {C W : Subgroup G} {a : G} (haC : a ∈ C) (ha : a ^ p = 1) (hWC : W ≤ C)
    (hWa : ∀ x ∈ W, a * x = x * a) (hWp : ¬ p ∣ Nat.card ↥W)
    (hWN : ∀ c ∈ C, a * c = c * a → c ∈ Subgroup.normalizer (W : Set G)) :
    barX p C W ≤ GLAPPrimeCoreOf p (Subgroup.centralizer
      ((Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (⟨a, haC⟩ : ↥C)) :
        Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set (↥C ⧸ GLAPPrimeCore p ↥C))) := by
  classical
  let a0 : ↥C := ⟨a, haC⟩
  have ha0 : a0 ^ p = 1 := Subtype.ext ha
  have hU : IsPGroup p ↥(Subgroup.zpowers a0) := l114f_isPGroup_zpowers ha0
  have hVp : ¬ p ∣ Nat.card ↥(GLAPPrimeCore p ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C))
  have hVn : Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  have hUV : Subgroup.zpowers a0 ≤
      Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) := by
    rw [hVn]; exact le_top
  have hWK : barX p C W ≤ Subgroup.centralizer
      ((Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥C) a0) : Subgroup _) :
        Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hcomm1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) a0 * QuotientGroup.mk' (GLAPPrimeCore p ↥C) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) w * QuotientGroup.mk' (GLAPPrimeCore p ↥C) a0 := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hWa _ (Subgroup.mem_subgroupOf.1 hw))
    exact (Commute.zpow_left hcomm1 n).eq
  have hKN : Subgroup.centralizer
      ((Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥C) a0) : Subgroup _) :
        Set (↥C ⧸ GLAPPrimeCore p ↥C)) ≤
      Subgroup.normalizer ((barX p C W : Subgroup _) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro y hy
    obtain ⟨c0, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) y
    have hcomm : ∀ u ∈ Subgroup.zpowers a0, u * c0 * u⁻¹ * c0⁻¹ ∈ GLAPPrimeCore p ↥C := by
      intro u hu
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (a0 ^ n) ∈
          Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥C) a0) :=
        Subgroup.mem_zpowers_iff.2 ⟨n, by rw [map_zpow]⟩
      have hcm := Subgroup.mem_centralizer_iff.1 hy _ hmem
      have : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (a0 ^ n * c0 * (a0 ^ n)⁻¹ * c0⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [hcm]
        group
      exact (QuotientGroup.eq_one_iff _).1 this
    have hxV : c0 ∈ Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) := by
      rw [hVn]; exact Subgroup.mem_top _
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' hU hVp hUV hxV hcomm
    have hv1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) v = 1 := (QuotientGroup.eq_one_iff v).2 hv
    have hy' : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c0 * v) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) c0 := by
      rw [map_mul, hv1, mul_one]
    have hac : a0 * (c0 * v) = (c0 * v) * a0 := by
      have h1 := hfix a0 (Subgroup.mem_zpowers a0)
      calc a0 * (c0 * v) = (a0 * (c0 * v) * a0⁻¹) * a0 := by group
        _ = (c0 * v) * a0 := by rw [h1]
    have hcnorm : (((c0 * v : ↥C)) : G) ∈ Subgroup.normalizer (W : Set G) :=
      hWN _ (c0 * v).2 (congrArg Subtype.val hac)
    have hcinv : (((c0 * v)⁻¹ : ↥C) : G) ∈ Subgroup.normalizer (W : Set G) := by
      have := (Subgroup.normalizer (W : Set G)).inv_mem hcnorm
      simpa using this
    rw [← hy', Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact l114f_barX_conj_mem hcnorm hn
    · intro hn
      have h2 := l114f_barX_conj_mem hcinv hn
      have e : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c0 * v)⁻¹ *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c0 * v) * n *
            (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c0 * v))⁻¹) *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥C) (c0 * v)⁻¹)⁻¹ = n := by
        rw [map_inv]; group
      rw [e] at h2
      exact h2
  have hcop : Nat.Coprime p (Nat.card ↥(barX p C W)) := l114f_coprime_barX hWC hWp
  exact Lemma114Layer.le_glaPPrimeCoreOf_of_normal' hWK hKN hcop

theorem l114f_hyperplane {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {C E M : Subgroup G} (hEC : E ≤ C) (hEp : IsPGroup p ↥E) (hEel : IsElemAbelian p E)
    (hEr : 3 ≤ CFSG.Open.pRank p E) (hEM : GLBCore p 2 E ≤ M) :
    ∀ B : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), B ≤ barX p C E →
      Nat.card ↥B * p = Nat.card ↥(barX p C E) →
      ∀ z : ↥C ⧸ GLAPPrimeCore p ↥C, (∀ b ∈ B, b * z = z * b) → z ∈ barX p C (M ⊓ C) := by
  intro B hB hcard z hz
  obtain ⟨R, hRE, hRB, hRrank⟩ := exists_le_barX_eq hp.out hEp hEC hB
  have hRC : R ≤ C := hRE.trans hEC
  have hRp : IsPGroup p ↥R := Lemma114Layer.isPGroup_of_le' hEp hRE
  have hRel : IsElemAbelian p R := isElemAbelian_mono hEel hRE
  have hBel : IsElemAbelian p B := by
    rw [← hRB]; exact isElemAbelian_barX hRel
  have hEbel : IsElemAbelian p (barX p C E) := isElemAbelian_barX hEel
  have hcardB := l114f_card_eq_pow_pRank hBel
  have hcardE := l114f_card_eq_pow_pRank hEbel
  have hrkE : CFSG.Open.pRank p (barX p C E) = CFSG.Open.pRank p E :=
    rank_barX_of_isPGroup hp.out hEp hEC
  have hB2 : 2 ≤ CFSG.Open.pRank p B := by
    rw [hcardB, hcardE, hrkE] at hcard
    have h3 : p ^ (CFSG.Open.pRank p B + 1) = p ^ CFSG.Open.pRank p E := by
      rw [pow_succ]; exact hcard
    have h4 := Nat.pow_right_injective hp.out.two_le h3
    omega
  have hkR : 2 ≤ CFSG.Open.pRank p R := by rw [hRrank]; exact hB2
  obtain ⟨zt, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥C) z
  let U : Subgroup ↥C := R.subgroupOf C
  have hU : IsPGroup p ↥U := Lemma114Layer.isPGroup_subgroupOf_of_le hRp hRC
  have hVn : Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  have hUV : U ≤ Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) := by
    rw [hVn]; exact le_top
  have hxV : zt ∈ Subgroup.normalizer ((GLAPPrimeCore p ↥C : Subgroup ↥C) : Set ↥C) := by
    rw [hVn]; exact Subgroup.mem_top _
  have hcomm : ∀ u ∈ U, u * zt * u⁻¹ * zt⁻¹ ∈ GLAPPrimeCore p ↥C := by
    intro u hu
    have hub : QuotientGroup.mk' (GLAPPrimeCore p ↥C) u ∈ B := by
      rw [← hRB]; exact Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    have key := hz _ hub
    have : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (u * zt * u⁻¹ * zt⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [key]
      group
    exact (QuotientGroup.eq_one_iff _).1 this
  have hVp : ¬ p ∣ Nat.card ↥(GLAPPrimeCore p ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥C))
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' hU hVp hUV hxV hcomm
  have hv1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) v = 1 := (QuotientGroup.eq_one_iff v).2 hv
  obtain ⟨c, hc⟩ : ∃ c : ↥C, c = zt * v := ⟨_, rfl⟩
  have hcmk : QuotientGroup.mk' (GLAPPrimeCore p ↥C) c =
      QuotientGroup.mk' (GLAPPrimeCore p ↥C) zt := by
    rw [hc, map_mul, hv1, mul_one]
  have hfix' : ∀ u ∈ U, u * c * u⁻¹ = c := by
    intro u hu
    rw [hc]
    exact hfix u hu
  have hcR : ∀ r ∈ R, r * (c : G) = (c : G) * r := by
    intro r hr
    have h1 := congrArg Subtype.val (hfix' ⟨r, hRC hr⟩ (Subgroup.mem_subgroupOf.2 hr))
    have h2 : r * (c : G) * r⁻¹ = (c : G) := by simpa using h1
    calc r * (c : G) = (r * (c : G) * r⁻¹) * r := by group
      _ = (c : G) * r := by rw [h2]
  have hcN : (c : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : (c : G) * h * (c : G)⁻¹ = h := by
        rw [← hcR h hh]; group
      rw [e]; exact hh
    · intro hr
      have hrc := hcR _ hr
      have e2 : (c : G)⁻¹ * ((c : G) * h * (c : G)⁻¹) * (c : G) = (c : G) * h * (c : G)⁻¹ := by
        calc (c : G)⁻¹ * ((c : G) * h * (c : G)⁻¹) * (c : G)
            = (c : G)⁻¹ * (((c : G) * h * (c : G)⁻¹) * (c : G)) := by group
          _ = (c : G)⁻¹ * ((c : G) * ((c : G) * h * (c : G)⁻¹)) := by rw [hrc]
          _ = (c : G) * h * (c : G)⁻¹ := by group
      have e : h = (c : G) * h * (c : G)⁻¹ := by
        calc h = (c : G)⁻¹ * ((c : G) * h * (c : G)⁻¹) * (c : G) := by group
          _ = (c : G) * h * (c : G)⁻¹ := e2
      rw [e]; exact hr
  have hcM : (c : G) ∈ M := hEM (l114_normalizer_le_glbCore hRE hkR hcN)
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hcM, c.2⟩), hcmk⟩

theorem clause_iii_of {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {e a : G}
    (hI : Input18_5) (h : Fails112 G m p B M E A e a) :
    ∃ K : Subgroup G, GLAPComponent p (Cg e) K ∧
      ⁅barX p (Cg e) K, barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a))⁆ ≠ ⊥ ∧
        ¬ Covers p (Cg e) (M ⊓ Cg e) K := by
  classical
  haveI hp : Fact p.Prime := ⟨h.standing.prime⟩
  haveI := h.standing.simple
  have hp2 : p ≠ 2 := (show p.Prime ∧ p ≠ 2 ∧ _ from h.standing.beta).2.1
  have hOM : GLAPPrimeCoreOf p (Cg e) ≤ M := (lemma114_i_ii h).1
  have hE : inD p M E := h.pair.1.1
  have hA : inDp p M A := h.pair.1.2.1
  have hEel : IsElemAbelian p E := hE.1.1.2.1
  have hEr : 3 ≤ CFSG.Open.pRank p E := hE.1.2
  have hEM : GLBCore p 2 E ≤ M := hE.2.clause_d
  have hAel : IsElemAbelian p A := hA.1.1.2.1
  have heE : e ∈ E := (Subgroup.mem_inf.1 h.he.1).1
  have heA : e ∈ A := (Subgroup.mem_inf.1 h.he.1).2
  have he1 : e ≠ 1 := h.he.2
  have haA : a ∈ A := h.ha.1
  have hEC : E ≤ Cg e := fun x hx => Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]; exact elemAbelian_comm hEel heE hx
  have hAC : A ≤ Cg e := fun x hx => Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]; exact elemAbelian_comm hAel heA hx
  have hEp : IsPGroup p ↥E := l114f_isPGroup_elemAbelian hEel
  have hGz : Subgroup.center G = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a', b', hab⟩ := h.standing.nonabelian
      apply hab
      have hz : a' ∈ Subgroup.center G := by rw [h1]; exact Subgroup.mem_top a'
      exact ((Subgroup.mem_center_iff.1 hz) b').symm
  have hCne : Cg e ≠ ⊤ := by
    intro htop
    have hez : e ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg e := by rw [htop]; exact Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg e (Set.mem_singleton e)).symm
    rw [hGz, Subgroup.mem_bot] at hez
    exact he1 hez
  have hIsKC : CFSG.Open.IsKGroup ↥(Cg e) := isKGroup_of_isKProper h.standing.kProper hCne
  have hIsKY := isKGroup_quotient_pPrime (p := p) hIsKC
  have hOY : GLAPPrimeCore p (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) = ⊥ :=
    glaPPrimeCore_quotient_eq_bot hp.out
  have hT : IsPGroup p ↥(barX p (Cg e) (E ⊔ A)) :=
    l114f_isPGroup_barX (sup_le hEC hAC) (lemma104_i_holds h.toSec11.toSec10Fails h.pair)
  obtain ⟨Q, hQ, hQn⟩ := exists_sylow_layer_normalized (p := p) hT
  by_contra hne
  have hN : ∀ K : Subgroup G, GLAPComponent p (Cg e) K →
      ⁅barX p (Cg e) K, barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a))⁆ ≠ ⊥ →
        barX p (Cg e) K ≤ barX p (Cg e) (M ⊓ Cg e) := by
    intro K hK hcomm
    by_contra hK'
    exact hne ⟨K, hK, hcomm, hK'⟩
  have hZ : GLAPPrimeCoreOf p (Subgroup.centralizer
      (Q : Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)))) ≤ barX p (Cg e) (M ⊓ Cg e) := by
    refine le_of_hyperplanes (isElemAbelian_barX hEel) ?_
      (l114f_le_normalizer_glaPPrimeCore_centralizer hQn (l114f_barX_mono le_sup_left)) ?_ ?_
    · rw [rank_barX_of_isPGroup hp.out hEp hEC]; exact hEr
    · exact Lemma114Layer.coprime_card_glaPPrimeCoreOf _
    · exact fun B hB hcard z _ hz => l114f_hyperplane hEC hEp hEel hEr hEM B hB hcard z hz
  have hXC2 : GLAPPrimeCoreOf p (Cg2 e a) ≤ Cg2 e a := Lemma114Layer.glaPPrimeCoreOf_le_self p _
  have hCg2 : Cg2 e a ≤ Cg e := fun x hx => Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact Subgroup.mem_centralizer_iff.1 hx e (Set.mem_insert _ _)
  have hXC : GLAPPrimeCoreOf p (Cg2 e a) ≤ Cg e := hXC2.trans hCg2
  have hXN : ∀ c ∈ Cg e, a * c = c * a →
      c ∈ Subgroup.normalizer (GLAPPrimeCoreOf p (Cg2 e a) : Set G) := by
    intro c hc hac
    have hcW : c ∈ Cg2 e a := by
      refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rcases hg with hg | hg
      · rw [hg]; exact Subgroup.mem_centralizer_iff.1 hc _ (Set.mem_singleton _)
      · rw [Set.mem_singleton_iff.1 hg]; exact hac
    exact Lemma114Layer.le_normalizer_glaPPrimeCoreOf p (Cg2 e a) hcW
  have hXa : ∀ x ∈ GLAPPrimeCoreOf p (Cg2 e a), a * x = x * a := fun x hx =>
    Subgroup.mem_centralizer_iff.1 (hXC2 hx) a (Set.mem_insert_of_mem _ (Set.mem_singleton a))
  have hWp : ¬ p ∣ Nat.card ↥(GLAPPrimeCoreOf p (Cg2 e a)) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).1 (Lemma114Layer.coprime_card_glaPPrimeCoreOf (Cg2 e a))
  have hXL : barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a)) ≤
      Lemma114Layer.layerOf (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) ⊔
        GLAPPrimeCoreOf p (Subgroup.centralizer
          (Q : Set (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)))) := by
    have ha0p : (⟨a, hAC haA⟩ : ↥(Cg e)) ^ p = 1 := Subtype.ext (by simpa using hAel.2 a haA)
    have hmk : (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, hAC haA⟩ : ↥(Cg e))) ^ p = 1 := by
      rw [← map_pow, ha0p, map_one]
    have hcent := l114f_barX_le_centralizer (hAC haA) (hAel.2 a haA) hXC hXa hWp hXN
    have hI18 := hI (↥(Cg e) ⧸ GLAPPrimeCore p ↥(Cg e)) hIsKY p hp.out hp2 hOY
      (Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) (⟨a, hAC haA⟩ : ↥(Cg e))))
      (l114f_isPGroup_zpowers hmk)
    refine hcent.trans (hI18.trans (sup_le le_sup_left (iSup₂_le fun Q' hQ' => ?_)))
    obtain ⟨h₀, hh₀, hQ'eq⟩ := l114f_sylow_glbConj hQ hQ'
    rw [← hQ'eq, l114f_glaPPrimeCore_centralizer_glbConj]
    intro x hx
    exact l114f_glbConj_mem_sup hh₀ hx
  have hXp : ∀ x ∈ barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a)), ¬ p ∣ orderOf x := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hy
    have h1 : ¬ p ∣ orderOf (w : G) :=
      Lemma114Layer.not_dvd_orderOf_of_mem_glaPPrimeCoreOf (Subgroup.mem_subgroupOf.1 hw)
    have h2 : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg e)) w) ∣ orderOf w :=
      orderOf_map_dvd _ _
    intro hd
    exact h1 (by rw [Subgroup.orderOf_coe]; exact hd.trans h2)
  have hXQ : barX p (Cg e) (GLAPPrimeCoreOf p (Cg2 e a)) ≤ barX p (Cg e) (M ⊓ Cg e) :=
    Lemma114Layer.X_le_of_layer hQ hZ hXp hXL (fun K hK hKC => comm_of_neg hN K hK hKC)
  apply h.not_i
  intro x hx
  obtain ⟨j, hj, hjx⟩ := exists_of_barX_le hXQ hx (hXC hx)
  have h1 : j⁻¹ * x ∈ M := hOM hjx
  have h2 : x = j * (j⁻¹ * x) := by group
  rw [h2]
  exact M.mul_mem (Subgroup.mem_inf.1 hj).1 h1

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma114Full

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemma114_of_inputs (hI : Lemma114Full.Input18_5) : Lemma114Statement := by
  intro G _ _ m p B M E A e a h
  obtain ⟨h1, h2⟩ := lemma114_i_ii h
  exact ⟨h1, h2, Lemma114Full.clause_iii_of hI h⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
