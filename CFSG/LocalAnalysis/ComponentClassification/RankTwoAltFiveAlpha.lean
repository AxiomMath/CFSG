module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveInner
public import CFSG.StronglyEmbedded.DihedralSylowNoStrongEmbedding

public section

open Subgroup Equiv CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

@[expose] def CoA (A : Subgroup G) (w₁ w₂ : G) : Prop :=
  w₁ * w₁ = 1 ∧ w₁ ≠ 1 ∧ w₂ * w₂ = 1 ∧ w₂ ≠ 1 ∧
    ∃ x : G, w₁ ∈ rightConjugate A x ∧ w₂ ∈ rightConjugate A x

omit [Finite G] in
theorem CoA.conj {A : Subgroup G} {w₁ w₂ : G} (h : CoA A w₁ w₂) (c : G) :
    CoA A (c * w₁ * c⁻¹) (c * w₂ * c⁻¹) := by
  obtain ⟨h1, h11, h2, h21, x, hx1, hx2⟩ := h
  have hsq : ∀ w : G, w * w = 1 → c * w * c⁻¹ * (c * w * c⁻¹) = 1 := fun w hw => by
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hne : ∀ w : G, w ≠ 1 → c * w * c⁻¹ ≠ 1 := fun w hw he => hw (by
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = 1 := by rw [he]; group)
  have hmem : ∀ w : G, w ∈ rightConjugate A x → c * w * c⁻¹ ∈ rightConjugate A (x * c⁻¹) :=
    fun w hw => by
      rw [mem_rightConjugate_iff] at hw ⊢
      rw [show x * c⁻¹ * (c * w * c⁻¹) * (x * c⁻¹)⁻¹ = x * w * x⁻¹ by group]
      exact hw
  exact ⟨hsq w₁ h1, hne w₁ h11, hsq w₂ h2, hne w₂ h21, x * c⁻¹, hmem w₁ hx1, hmem w₂ hx2⟩

omit [Finite G] in
theorem eqvGen_coA_conj {A : Subgroup G} {w₁ w₂ : G} (h : Relation.EqvGen (CoA A) w₁ w₂)
    (c : G) : Relation.EqvGen (CoA A) (c * w₁ * c⁻¹) (c * w₂ * c⁻¹) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (hxy.conj c)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

@[expose] def compStabA (A : Subgroup G) (z : G) : Subgroup G where
  carrier := {g | Relation.EqvGen (CoA A) (g * z * g⁻¹) z}
  one_mem' := by
    change Relation.EqvGen (CoA A) (1 * z * 1⁻¹) z
    rw [one_mul, inv_one, mul_one]
    exact Relation.EqvGen.refl z
  mul_mem' := by
    intro g k hg hk
    change Relation.EqvGen (CoA A) (g * k * z * (g * k)⁻¹) z
    have h1 := eqvGen_coA_conj hk g
    rw [show g * (k * z * k⁻¹) * g⁻¹ = g * k * z * (g * k)⁻¹ by group] at h1
    exact Relation.EqvGen.trans _ _ _ h1 hg
  inv_mem' := by
    intro g hg
    change Relation.EqvGen (CoA A) (g⁻¹ * z * g⁻¹⁻¹) z
    have h1 := eqvGen_coA_conj hg g⁻¹
    rw [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h1
    exact Relation.EqvGen.symm _ _ h1

omit [Finite G] in
theorem mem_compStabA {A : Subgroup G} {z g : G} :
    g ∈ compStabA A z ↔ Relation.EqvGen (CoA A) (g * z * g⁻¹) z := Iff.rfl

theorem exists_conj_of_equiv {B : Subgroup G} (e : ↥B ≃* A5) {w₁ w₂ : G} (h1 : w₁ ∈ B)
    (h12 : w₁ * w₁ = 1) (h11 : w₁ ≠ 1) (h2 : w₂ ∈ B) (h22 : w₂ * w₂ = 1) (h21 : w₂ ≠ 1) :
    ∃ a ∈ B, a * w₁ * a⁻¹ = w₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := exists_isSylowOf 2 B
  have hW4 : Nat.card W = 4 := by
    rw [hW.card_eq, Nat.card_congr e.toEquiv, fact_A5]
    rfl
  obtain ⟨a₁, ha₁, hw₁⟩ := exists_conj_mem_of_isSylowOf hW h1 (n := 1)
    (by rw [pow_one, sq]; exact h12)
  obtain ⟨a₂, ha₂, hw₂⟩ := exists_conj_mem_of_isSylowOf hW h2 (n := 1)
    (by rw [pow_one, sq]; exact h22)
  obtain ⟨b, hbB, -, -, hbtr, -⟩ := exists_klein_three e hW.le hW4
  have hne : ∀ (a w : G), w ≠ 1 → a * w * a⁻¹ ≠ 1 := fun a w hw he => hw (by
    calc w = a⁻¹ * (a * w * a⁻¹) * a := by group
      _ = 1 := by rw [he]; group)
  obtain ⟨k, hk⟩ := hbtr _ hw₁ _ hw₂ (hne a₁ w₁ h11) (hne a₂ w₂ h21)
  refine ⟨a₂⁻¹ * (b ^ k)⁻¹ * a₁, mul_mem (mul_mem (inv_mem ha₂) (inv_mem (pow_mem hbB k))) ha₁,
    ?_⟩
  calc a₂⁻¹ * (b ^ k)⁻¹ * a₁ * w₁ * (a₂⁻¹ * (b ^ k)⁻¹ * a₁)⁻¹ =
      a₂⁻¹ * ((b ^ k)⁻¹ * (a₁ * w₁ * a₁⁻¹) * b ^ k) * a₂ := by group
    _ = a₂⁻¹ * (a₂ * w₂ * a₂⁻¹) * a₂ := by rw [hk]
    _ = w₂ := by group

omit [Finite G] in
theorem le_conjSupThrough {A : Subgroup G} {w x : G} (hw : w ∈ rightConjugate A x) :
    rightConjugate A x ≤ conjSupThrough A w :=
  le_iSup₂ (f := fun (y : G) (_ : w ∈ rightConjugate A y) => rightConjugate A y) x hw

omit [Finite G] in
theorem conjSupThrough_le_of_conj {A : Subgroup G} {w a : G} (ha : a ∈ conjSupThrough A w) :
    conjSupThrough A (a * w * a⁻¹) ≤ conjSupThrough A w := by
  refine iSup₂_le fun y hy => ?_
  have hw : w ∈ rightConjugate A (y * a) := by
    rw [mem_rightConjugate_iff] at hy ⊢
    rw [show y * a * w * (y * a)⁻¹ = y * (a * w * a⁻¹) * y⁻¹ by group]
    exact hy
  have hle := le_conjSupThrough hw
  intro u hu
  have hu' : a⁻¹ * u * a ∈ rightConjugate A (y * a) := by
    rw [mem_rightConjugate_iff] at hu ⊢
    rw [show y * a * (a⁻¹ * u * a) * (y * a)⁻¹ = y * u * y⁻¹ by group]
    exact hu
  have h1 := hle hu'
  rw [show u = a * (a⁻¹ * u * a) * a⁻¹ by group]
  exact mul_mem (mul_mem ha h1) (inv_mem ha)

theorem conjSupThrough_eq_of_coA {A : Subgroup G} (e : ↥A ≃* A5) {w₁ w₂ : G}
    (h : CoA A w₁ w₂) : conjSupThrough A w₁ = conjSupThrough A w₂ := by
  obtain ⟨h12, h11, h22, h21, x, hx1, hx2⟩ := h
  obtain ⟨a, ha, haw⟩ := exists_conj_of_equiv ((conjEquiv A x).trans e) hx1 h12 h11 hx2 h22 h21
  apply le_antisymm
  · have h1 := conjSupThrough_le_of_conj (w := w₂) (a := a⁻¹)
      (inv_mem (le_conjSupThrough hx2 ha))
    rwa [show a⁻¹ * w₂ * a⁻¹⁻¹ = w₁ by rw [← haw]; group] at h1
  · have h1 := conjSupThrough_le_of_conj (w := w₁) (a := a) (le_conjSupThrough hx1 ha)
    rwa [haw] at h1

theorem conjSupThrough_eq_of_eqvGen {A : Subgroup G} (e : ↥A ≃* A5) {w₁ w₂ : G}
    (h : Relation.EqvGen (CoA A) w₁ w₂) : conjSupThrough A w₁ = conjSupThrough A w₂ := by
  induction h with
  | rel x y hxy => exact conjSupThrough_eq_of_coA e hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y w _ _ ih1 ih2 => exact ih1.trans ih2

omit [Finite G] in
theorem conj_mem_conjSupThrough {A : Subgroup G} {w u : G} (g : G)
    (hu : u ∈ conjSupThrough A w) : g * u * g⁻¹ ∈ conjSupThrough A (g * w * g⁻¹) := by
  have hle : conjSupThrough A w ≤
      (conjSupThrough A (g * w * g⁻¹)).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun y hy => ?_
    intro v hv
    have hw' : g * w * g⁻¹ ∈ rightConjugate A (y * g⁻¹) := by
      rw [mem_rightConjugate_iff] at hy ⊢
      rw [show y * g⁻¹ * (g * w * g⁻¹) * (y * g⁻¹)⁻¹ = y * w * y⁻¹ by group]
      exact hy
    have hv' : g * v * g⁻¹ ∈ rightConjugate A (y * g⁻¹) := by
      rw [mem_rightConjugate_iff] at hv ⊢
      rw [show y * g⁻¹ * (g * v * g⁻¹) * (y * g⁻¹)⁻¹ = y * v * y⁻¹ by group]
      exact hv
    exact le_conjSupThrough hw' hv'
  exact hle hu

theorem centralizer_le_of_sylow {M : Subgroup G} (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hC : ∀ t ∈ (S : Subgroup G), orderOf t = 2 → centralizer ({t} : Set G) ≤ M) :
    ∀ v ∈ M, orderOf v = 2 → centralizer ({v} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsyl : IsSylowOf 2 S M := by
    refine isSylowOf_of_card hSM ?_
    have h1 : Nat.card (S : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le hSM
    have h2 : Nat.card M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hM0 : Nat.card M ≠ 0 := Nat.card_pos.ne'
    rw [S.card_eq_multiplicity] at h1 ⊢
    congr 1
    apply le_antisymm
    · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hM0).mp h1
    · exact (Nat.factorization_le_iff_dvd hM0 hG0).mpr h2 2
  intro v hv hv2
  obtain ⟨m, hm, hmv⟩ := exists_conj_mem_of_isSylowOf hSsyl hv (n := 1)
    (by rw [pow_one, ← hv2, pow_orderOf_eq_one])
  have hmo : orderOf (m * v * m⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hv2]
  intro c hc
  have h1 : m * c * m⁻¹ ∈ centralizer ({m * v * m⁻¹} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    calc m * c * m⁻¹ * (m * v * m⁻¹) = m * (c * v) * m⁻¹ := by group
      _ = m * (v * c) * m⁻¹ := by rw [hc]
      _ = m * v * m⁻¹ * (m * c * m⁻¹) := by group
  have h2 := hC _ hmv hmo h1
  rw [show c = m⁻¹ * (m * c * m⁻¹) * m by group]
  exact mul_mem (mul_mem (inv_mem hm) h2) hm

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem oddCoreIn_centralizer_eq_bot
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} (hz : z ∈ V₀) (hz1 : z ≠ 1) (hzS : ∀ y ∈ (S : Subgroup G), z * y = y * z)
    (hconn : ∀ t ∈ (S : Subgroup G), t ∉ P → t * t = 1 → IsConj z t →
      Relation.EqvGen (CoA A) t z) :
    oddCoreIn (centralizer ({z} : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := h.equiv
  have hNA := h.normalizer_le_sup_of_eps_one hP hε
  have hR2 : ∀ x ∈ R, x * x = 1 := fun x hx => h.mul_self (mem_sup_left hx)
  obtain ⟨r₀, hr₀, hr₀1, -⟩ := exists_ne_one_ne h.cardR hR2 (one_mem R)
  have hcls : ∀ x : G, x ^ 2 = 1 → x ≠ 1 → IsConj z x ∨ IsConj r₀ x := fun x hx2 hx1 =>
    h.isConj_or_isConj hIIa hP hPC hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv hz hz1
      hr₀ hr₀1 hx2 hx1
  have hzA : z ∈ A := h.V₀_le_A hz
  have hz2 : z * z = 1 := h.mul_self (h.V₀_le hz)
  have hzSm : z ∈ (S : Subgroup G) := hPS (hVP (h.V₀_le hz))
  have hsq : ∀ (c w : G), w * w = 1 → c * w * c⁻¹ * (c * w * c⁻¹) = 1 := fun c w hw => by
    calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have hne : ∀ (c w : G), w ≠ 1 → c * w * c⁻¹ ≠ 1 := fun c w hw he => hw (by
    calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
      _ = 1 := by rw [he]; group)
  have hcoA : ∀ {w : G}, w ∈ A → w * w = 1 → w ≠ 1 → CoA A w z := fun hw hw2 hw1 =>
    ⟨hw2, hw1, hz2, hz1, 1, by rw [rightConjugate_one]; exact hw,
      by rw [rightConjugate_one]; exact hzA⟩
  obtain ⟨-, -, -, hswap, -, -⟩ := h.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
    hV'e hV'16 hinf hsup hV'inv S hPS
  have hPS' : P < S := lt_of_le_of_ne hPS (h.P_not_sylow hP hPC hGold hGs hIIa hP64 hVP S).symm
  obtain ⟨s₀, hs₀, hs₀P⟩ := IsConcreteLE.exists_of_lt hPS'
  obtain ⟨hVs, hV's⟩ := hswap s₀ hs₀ hs₀P
  have hV₀V' : V₀ ≤ V' := hinf ▸ inf_le_right
  have hPz : ∀ t ∈ P, t * t = 1 → IsConj z t → t ∈ V₀ := by
    intro t ht ht2 hzt
    have ht1 : t ≠ 1 := fun he => hz1 (by rw [he] at hzt; exact isConj_one_left.mp hzt)
    by_cases htV : t ∈ R ⊔ T
    · by_contra ht0
      exact h.not_isConj_of_mem_V₀ hz hz1 htV ht0 hzt
    · exfalso
      have htV' := hV'inv t ht ht2 htV
      have h1 : s₀ * t * s₀⁻¹ ∈ R ⊔ T := by
        rw [← hVs] at htV'
        exact (mem_rightConjugate_iff _ _ _).mp htV'
      have h2 : s₀ * t * s₀⁻¹ ∉ V₀ := by
        intro h0
        apply htV
        rw [← hV's, mem_rightConjugate_iff]
        exact hV₀V' h0
      exact h.not_isConj_of_mem_V₀ hz hz1 h1 h2 (hzt.trans (isConj_iff.mpr ⟨s₀, rfl⟩))
  have hSM : (S : Subgroup G) ≤ compStabA A z := fun s hs => by
    rw [mem_compStabA, show s * z * s⁻¹ = z by rw [← hzS s hs]; group]
    exact Relation.EqvGen.refl z
  have hNS : normalizer ((S : Subgroup G) : Set G) ≤ compStabA A z := by
    intro n hn
    have h1 : n * z * n⁻¹ ∈ (S : Subgroup G) := (mem_normalizer_iff.mp hn z).mp hzSm
    have h2 : ∀ y ∈ (S : Subgroup G), n * z * n⁻¹ * y = y * (n * z * n⁻¹) := by
      intro y hy
      have hy' : n⁻¹ * y * n ∈ (S : Subgroup G) := by
        have := (mem_normalizer_iff.mp (inv_mem hn) y).mp hy
        simpa using this
      have e := hzS _ hy'
      calc n * z * n⁻¹ * y = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by rw [e]
        _ = y * (n * z * n⁻¹) := by group
    have h3 := h.center_le_V₀ hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup hV'inv
      S hPS h1 h2
    rw [mem_compStabA]
    exact Relation.EqvGen.rel _ _ (hcoA (h.V₀_le_A h3) (hsq n z hz2) (hne n z hz1))
  have hCS : ∀ t ∈ (S : Subgroup G), orderOf t = 2 →
      centralizer ({t} : Set G) ≤ compStabA A z := by
    intro t ht ht2
    have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
    have ht1 : t ≠ 1 := fun he => by rw [he, orderOf_one] at ht2; exact absurd ht2 (by decide)
    rcases hcls t (by rw [sq]; exact htt) ht1 with hc | hc
    · have hconn' : Relation.EqvGen (CoA A) t z := by
        by_cases htP : t ∈ P
        · exact Relation.EqvGen.rel _ _ (hcoA (h.V₀_le_A (hPz t htP htt hc)) htt ht1)
        · exact hconn t ht htP htt hc
      intro c hc'
      rw [mem_compStabA]
      have h1 := eqvGen_coA_conj hconn' c
      rw [mem_centralizer_singleton_iff] at hc'
      rw [show c * t * c⁻¹ = t by rw [hc']; group] at h1
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1) hconn'
    · obtain ⟨d, hd⟩ := isConj_iff.mp hc
      have htK : t ∈ centralizer (rightConjugate A d⁻¹ : Set G) := by
        rw [centralizer_rightConjugate, mem_rightConjugate_iff, ← hd,
          show d⁻¹ * (d * r₀ * d⁻¹) * d⁻¹⁻¹ = r₀ by group]
        exact h.sylowR.le hr₀
      have hzAx := h.mem_of_isConj_of_commute hNA hz hz1 d⁻¹ htK ht1 htt hz2 (hzS t ht)
        (IsConj.refl z)
      intro c hc'
      have hcN := centralizer_le_normalizer_conj h.hyp.standard d⁻¹ htK ht1 htt hc'
      have hczA : c * z * c⁻¹ ∈ rightConjugate A d⁻¹ := (mem_normalizer_iff.mp hcN z).mp hzAx
      rw [mem_compStabA]
      exact Relation.EqvGen.rel _ _ ⟨hsq c z hz2, hne c z hz1, hz2, hz1, d⁻¹, hczA, hzAx⟩
  have hMtop : compStabA A z = ⊤ := by
    by_contra hMne
    have heven : Even (Nat.card (compStabA A z)) := by
      have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hz2) hz1
      rw [even_iff_two_dvd, ← hzo, ← Subgroup.orderOf_mk z (hSM hzSm)]
      exact orderOf_dvd_natCard _
    have hSE := CFSG.ProperTwoGeneratedCore.sylow_normalizer_involution_centralizer_strong_embedding
      (compStabA A z) hMne heven S hSM hNS (centralizer_le_of_sylow S hSM hCS)
    obtain ⟨c, hc, hc0⟩ : ∃ c ∈ V', c ∉ V₀ := by
      by_contra hno
      push Not at hno
      have := Subgroup.card_le_of_le (show V' ≤ V₀ from hno)
      rw [hV'16, h.card_V₀] at this
      omega
    have hcV : c ∉ R ⊔ T := fun hcV => hc0 (hinf ▸ mem_inf.mpr ⟨hcV, hc⟩)
    have hc2 : c * c = 1 := by rw [← sq]; exact hV'e.2 c hc
    have hr₀o : orderOf r₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hR2 r₀ hr₀) hr₀1
    have hcomm := CFSG.StronglyEmbedded.commute_of_mem_sylow_of_fusionStronglyEmbedded hSE S
      (hPS (hVP (mem_sup_left hr₀))) hr₀o (hPS (hV'P hc))
    have hfix : c * r₀ * c⁻¹ = r₀ := by rw [hcomm.eq]; group
    have hr₀0 := h.P_fixed hP hPC (hV'P hc) hcV (mem_sup_left hr₀) hfix
    have h1 : r₀ ∈ R ⊓ V₀ := mem_inf.mpr ⟨hr₀, hr₀0⟩
    rw [h.inf_R_V₀, mem_bot] at h1
    exact hr₀1 h1
  have hLn : (conjSupThrough A z).Normal := ⟨fun u hu x => by
    have h1 := conj_mem_conjSupThrough x hu
    have h2 : x ∈ compStabA A z := hMtop ▸ mem_top x
    rw [mem_compStabA] at h2
    rwa [conjSupThrough_eq_of_eqvGen eA h2] at h1⟩
  have hAL : A ≤ conjSupThrough A z := by
    have := le_conjSupThrough (A := A) (w := z) (x := 1) (by rw [rightConjugate_one]; exact hzA)
    rwa [rightConjugate_one] at this
  have hL1 : conjSupThrough A z ≠ ⊥ := fun h0 => hz1 (by
    have := hAL hzA
    rw [h0, mem_bot] at this
    exact this)
  have := hGs
  have hLtop : conjSupThrough A z = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (conjSupThrough A z)).resolve_left hL1
  have hO := oddCoreIn_centralizer_le_centralizer_conjSupThrough h.hyp.standard eA h.sylowR.le
    h.elemR h.cardR hz2 hz1
  rw [hLtop, coe_top, centralizer_univ] at hO
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hZ | hZ
    · exact hZ
    · exfalso
      have hk : k1 * y0 ≠ y0 * k1 := by decide
      apply hk
      apply eA.symm.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      simp only [coe_mul]
      exact (mem_center_iff.mp (hZ ▸ mem_top ((eA.symm y0 : ↥A) : G)) _).symm
  rw [hZ] at hO
  exact le_bot_iff.mp hO

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive

