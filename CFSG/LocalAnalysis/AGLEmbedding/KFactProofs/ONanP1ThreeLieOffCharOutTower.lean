module

public import CFSG.LieType.SeitzGeneration.HyperOuterFieldAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharAlmostSimple

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne.CTP

@[expose] def OutTowerAt (K : Type*) [Group K] (p : ℕ) : Prop :=
  ∃ D : Subgroup (MulAut K),
    (∀ γ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → γ * α * γ⁻¹ * α⁻¹ ∈ D) ∧
    ∀ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → ∀ δ ∈ D,
      α * δ * α⁻¹ * δ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range

theorem OutTowerAt.of_mulEquiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    (h : OutTowerAt L p) : OutTowerAt K p := by
  obtain ⟨D, hab, hcent⟩ := h
  refine ⟨D.comap (MulAut.congr e).toMonoidHom, fun γ α ⟨k, hk⟩ => ?_,
    fun α ⟨k, hk⟩ δ hδ => ?_⟩
  · have hk' : (MulAut.congr e α) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    change MulAut.congr e (γ * α * γ⁻¹ * α⁻¹) ∈ D
    simpa only [map_mul, map_inv] using hab (MulAut.congr e γ) (MulAut.congr e α) ⟨k, hk'⟩
  · have hk' : (MulAut.congr e α) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨g, hg⟩ := hcent (MulAut.congr e α) ⟨k, hk'⟩ (MulAut.congr e δ) hδ
    refine ⟨e.symm g, (eq_conj_of_congr_eq_conj e ?_).symm⟩
    simpa only [map_mul, map_inv] using hg.symm

theorem eq_of_pow_eq_one_of_card_le {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime]
    {f : Function.End α} {k : ℕ} (hf : f ^ (p ^ k) = 1) (hcard : Nat.card α ≤ p) {a : α}
    (ha : f a = a) (x : α) : f x = x := by
  classical
  have := Fintype.ofFinite α
  by_contra hx
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) hf
  have hlt : Fintype.card (Function.fixedPoints f) < Fintype.card α :=
    Fintype.card_subtype_lt (p := (· ∈ Function.fixedPoints f)) hx
  have hpos : 0 < Fintype.card (Function.fixedPoints f) :=
    Fintype.card_pos_iff.2 ⟨⟨a, ha⟩⟩
  have hle : Fintype.card α ≤ p := by rwa [← Nat.card_eq_fintype_card]
  have hdvd := (Nat.modEq_iff_dvd' hlt.le).1 hmod.symm
  have := Nat.le_of_dvd (by omega) hdvd
  omega

theorem outTowerAt_of_card_le {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (D : Subgroup (MulAut K))
    (hab : ∀ γ α : MulAut K, (∃ k : ℕ, α ^ (p ^ k) = 1) → γ * α * γ⁻¹ * α⁻¹ ∈ D)
    (hcard : Nat.card (D ⧸ ((MulAut.conj : K →* MulAut K).range).subgroupOf D) ≤ p) :
    OutTowerAt K p := by
  refine ⟨D, hab, fun α ⟨k, hk⟩ δ hδ => ?_⟩
  set I := (MulAut.conj : K →* MulAut K).range with hI
  have hIn : I.Normal := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K
  set N := I.subgroupOf D with hN
  have : Finite (MulAut K) := CFSG.RankThree.PartOne.OutStructure.instFiniteMulAut' K
  have hαD : ∀ x ∈ D, α * x * α⁻¹ ∈ D := by
    intro x hx
    have h1 := D.inv_mem (hab x α ⟨k, hk⟩)
    have e : α * x * α⁻¹ = (x * α * x⁻¹ * α⁻¹)⁻¹ * x := by group
    rw [e]
    exact D.mul_mem h1 hx
  let Φ₀ : D →* D :=
    { toFun := fun x => ⟨α * x * α⁻¹, hαD x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let Φ : Monoid.End D := Φ₀
  have hΦN : N ≤ N.comap Φ₀ := by
    intro x hx
    change ((Φ₀ x : D) : MulAut K) ∈ I
    exact hIn.conj_mem _ hx α
  let M : (D ⧸ N) →* (D ⧸ N) := QuotientGroup.map N N Φ₀ hΦN
  let f : Function.End (D ⧸ N) := ⇑M
  have hΦpow : ∀ (j : ℕ) (x : D), (((Φ ^ j) x : D) : MulAut K) = α ^ j * x * (α ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; rw [pow_zero, pow_zero, one_mul, inv_one, mul_one]; rfl
    | succ j ih =>
      intro x
      rw [pow_succ']
      change α * (((Φ ^ j) x : D) : MulAut K) * α⁻¹ = _
      rw [ih, pow_succ']
      group
  have hMpow : ∀ (j : ℕ) (x : D), (f ^ j) (x : D ⧸ N) = (((Φ ^ j) x : D) : D ⧸ N) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [pow_succ', pow_succ']
      change f ((f ^ j) (x : D ⧸ N)) = ((Φ ((Φ ^ j) x) : D) : D ⧸ N)
      rw [ih]
      rfl
  have hMp : f ^ (p ^ k) = 1 := by
    funext z
    induction z using QuotientGroup.induction_on with
    | H x =>
      rw [hMpow]
      change (((Φ ^ (p ^ k)) x : D) : D ⧸ N) = (x : D ⧸ N)
      congr 1
      apply Subtype.ext
      rw [hΦpow, hk, one_mul, inv_one, mul_one]
  have hfix := eq_of_pow_eq_one_of_card_le hMp hcard (a := 1) (map_one M)
    ((⟨δ, hδ⟩ : D) : D ⧸ N)
  change ((Φ₀ ⟨δ, hδ⟩ : D) : D ⧸ N) = _ at hfix
  have h6 := (QuotientGroup.eq).1 hfix
  have h7 : (α * δ * α⁻¹)⁻¹ * δ ∈ I := by
    have := Subgroup.mem_subgroupOf.1 h6
    simpa [Φ₀] using this
  have h8 := hIn.conj_mem _ (I.inv_mem h7) δ
  have h9 : δ * ((α * δ * α⁻¹)⁻¹ * δ)⁻¹ * δ⁻¹ = α * δ * α⁻¹ * δ⁻¹ := by group
  rwa [h9] at h8

section Criterion

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]

theorem sup_sylow_normal_of_outTower (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hT : OutTowerAt K p) (Rb : Sylow p Y) : (K ⊔ (Rb : Subgroup Y)).Normal := by
  classical
  obtain ⟨D, hab, hcent⟩ := hT
  have hinj := conjNormal_injective (K := K) hC
  set ρ : Y →* MulAut K := MulAut.conjNormal with hρ
  set YD := D.comap ρ with hYD
  set H := K ⊔ (Rb : Subgroup Y) with hH
  have hRp : ∀ r ∈ (Rb : Subgroup Y), ∃ k : ℕ, r ^ (p ^ k) = 1 := fun r hr => by
    obtain ⟨k, hk⟩ := Rb.isPGroup' ⟨r, hr⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hYDR : ∀ d ∈ YD, ∀ r ∈ (Rb : Subgroup Y), d * r * d⁻¹ ∈ H := by
    intro d hd r hr
    obtain ⟨k, hk⟩ := hRp r⁻¹ (Subgroup.inv_mem _ hr)
    have hk' : (ρ r⁻¹) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨g, hg⟩ := hcent (ρ r⁻¹) ⟨k, hk'⟩ (ρ d) hd
    have h2 : r⁻¹ * d * r * d⁻¹ = (g : Y) := by
      apply hinj
      rw [MulAut.conjNormal_val, hg]
      simp only [hρ, map_mul, map_inv, inv_inv]
    have h3 : d * r * d⁻¹ = r * (g : Y) := by
      calc d * r * d⁻¹ = r * (r⁻¹ * d * r * d⁻¹) := by group
        _ = r * (g : Y) := by rw [h2]
    rw [h3]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hr) (Subgroup.mem_sup_left g.2)
  have hpres : ∀ h ∈ YD ⊔ (Rb : Subgroup Y), ∀ x ∈ H, h * x * h⁻¹ ∈ H := by
    intro h hh
    rw [Subgroup.sup_eq_closure] at hh
    induction hh using Subgroup.closure_induction_left with
    | one => intro x hx; simpa using hx
    | mul_left a ha b _ ih =>
      intro x hx
      have h1 := ih x hx
      have key : ∀ y ∈ H, a * y * a⁻¹ ∈ H := by
        rcases ha with ha | ha
        · intro y hy
          rw [hH, Subgroup.sup_eq_closure] at hy
          induction hy using Subgroup.closure_induction with
          | mem z hz =>
            rcases hz with hz | hz
            · exact Subgroup.mem_sup_left (‹K.Normal›.conj_mem z hz a)
            · exact hYDR a ha z hz
          | one => simp
          | mul u v _ _ hu hv =>
            have : a * (u * v) * a⁻¹ = (a * u * a⁻¹) * (a * v * a⁻¹) := by group
            rw [this]
            exact Subgroup.mul_mem _ hu hv
          | inv u _ hu =>
            have : a * u⁻¹ * a⁻¹ = (a * u * a⁻¹)⁻¹ := by group
            rw [this]
            exact Subgroup.inv_mem _ hu
        · intro y hy
          have hrH : a ∈ H := Subgroup.mem_sup_right ha
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrH hy) (Subgroup.inv_mem _ hrH)
      have : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      rw [this]
      exact key _ h1
    | inv_mul_cancel a ha b _ ih =>
      intro x hx
      have h1 := ih x hx
      have key : ∀ y ∈ H, a⁻¹ * y * a⁻¹⁻¹ ∈ H := by
        rcases ha with ha | ha
        · intro y hy
          have ha' : a⁻¹ ∈ YD := Subgroup.inv_mem _ ha
          rw [hH, Subgroup.sup_eq_closure] at hy
          induction hy using Subgroup.closure_induction with
          | mem z hz =>
            rcases hz with hz | hz
            · exact Subgroup.mem_sup_left (‹K.Normal›.conj_mem z hz a⁻¹)
            · exact hYDR a⁻¹ ha' z hz
          | one => simp
          | mul u v _ _ hu hv =>
            have : a⁻¹ * (u * v) * a⁻¹⁻¹ = (a⁻¹ * u * a⁻¹⁻¹) * (a⁻¹ * v * a⁻¹⁻¹) := by group
            rw [this]
            exact Subgroup.mul_mem _ hu hv
          | inv u _ hu =>
            have : a⁻¹ * u⁻¹ * a⁻¹⁻¹ = (a⁻¹ * u * a⁻¹⁻¹)⁻¹ := by group
            rw [this]
            exact Subgroup.inv_mem _ hu
        · intro y hy
          have hrH : a⁻¹ ∈ H := Subgroup.mem_sup_right (Subgroup.inv_mem _ ha)
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrH hy) (Subgroup.inv_mem _ hrH)
      have : a⁻¹ * b * x * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * x * b⁻¹) * a⁻¹⁻¹ := by group
      rw [this]
      exact key _ h1
  refine ⟨fun x hx y => ?_⟩
  rw [hH, Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · exact Subgroup.mem_sup_left (‹K.Normal›.conj_mem z hz y)
    ·
      set w := y * z * y⁻¹ with hw
      obtain ⟨k, hk⟩ := hRp z hz
      have hwYD : w * z⁻¹ ∈ YD := by
        have hk' : (ρ z) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
        change ρ (y * z * y⁻¹ * z⁻¹) ∈ D
        simpa only [map_mul, map_inv] using hab (ρ y) (ρ z) ⟨k, hk'⟩
      have hwM : w ∈ YD ⊔ (Rb : Subgroup Y) := by
        have : w = (w * z⁻¹) * z := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hwYD) (Subgroup.mem_sup_right hz)
      have hwk : w ^ (p ^ k) = 1 := by rw [hw, conj_pow, hk, mul_one, mul_inv_cancel]
      set M := YD ⊔ (Rb : Subgroup Y) with hM
      have hRM : (Rb : Subgroup Y) ≤ M := le_sup_right
      set w' : M := ⟨w, hwM⟩ with hw'
      have hzp : IsPGroup p (Subgroup.zpowers w') := by
        rintro ⟨_, j, rfl⟩
        refine ⟨k, Subtype.ext ?_⟩
        change (w' ^ j) ^ (p ^ k) = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
        have : w' ^ (p ^ k) = 1 := Subtype.ext (by simpa [hw'] using hwk)
        rw [this, one_zpow]
      obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M Q (Rb.subtype hRM)
      have hgQ : ((g • Q : Sylow p M) : Subgroup M) =
          (Q : Subgroup M).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
      have hmem : g * w' * g⁻¹ ∈ ((Rb.subtype hRM : Sylow p M) : Subgroup M) := by
        rw [← hg, hgQ]
        exact ⟨w', hQ (Subgroup.mem_zpowers w'), rfl⟩
      rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
      have h1 := hpres (g⁻¹ : M) (Subgroup.inv_mem _ g.2) _ (Subgroup.mem_sup_right hmem)
      have h2 : ((g⁻¹ : M) : Y) * ((g * w' * g⁻¹ : M) : Y) * ((g⁻¹ : M) : Y)⁻¹ = w := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw']
        group
      rw [h2] at h1
      exact h1
  | one => simp
  | mul u v _ _ hu hv =>
    have : y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hu hv
  | inv u _ hu =>
    have : y * u⁻¹ * y⁻¹ = (y * u * y⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hu

end Criterion

@[expose] def P1OffCharAlmostSimpleNonNormalAt (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      Subgroup.centralizer (K : Set Y) = ⊥ →
      (¬ ∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3) →
      K ≤ Y₀ → ¬ (Rb : Subgroup Y) ≤ (K ⊔ (Rb : Subgroup Y)).normalCore →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      p ≠ d.1.characteristic →
      P1ThreeLieList p d

theorem p1OffCharAlmostSimpleNonNormal_of_at (h : ∀ d, P1OffCharAlmostSimpleNonNormalAt d) :
    P1OffCharAlmostSimpleNonNormal :=
  fun p _ Y _ _ Rb Y₀ hR hcat K hK huniq hnc hC hnoK hKY hN d hd hpd =>
    h d p Y Rb Y₀ hR hcat K hK huniq hnc hC hnoK hKY hN hd hpd

end CFSG.AGLEmbedding
