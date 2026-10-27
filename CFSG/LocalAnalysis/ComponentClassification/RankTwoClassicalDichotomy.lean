module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSetup

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.Goldschmidt AS76b.Lemma36

variable {G : Type} [Group G]

theorem rightConjugate_le_iff {Q S : Subgroup G} {x : G} :
    rightConjugate Q x ≤ S ↔ Q ≤ rightConjugate S x⁻¹ := by
  constructor
  · intro h q hq
    rw [mem_rightConjugate_iff]
    apply h
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hq
  · intro h z hz
    rw [mem_rightConjugate_iff] at hz
    have := h hz
    rw [mem_rightConjugate_iff] at this
    simpa [mul_assoc] using this

theorem rightConjugate_le_rightConjugate_iff {Q S : Subgroup G} {x : G} :
    rightConjugate Q x ≤ rightConjugate S x ↔ Q ≤ S := by
  rw [rightConjugate_le_iff, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem rightConjugate_rightConjugate_inv (Q : Subgroup G) (x : G) :
    rightConjugate (rightConjugate Q x) x⁻¹ = Q := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem rightConjugate_inv_rightConjugate (Q : Subgroup G) (x : G) :
    rightConjugate (rightConjugate Q x⁻¹) x = Q := by
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]

theorem rightConjugate_zpowers (y x : G) :
    rightConjugate (zpowers y) x = zpowers (x⁻¹ * y * x) := by
  rw [rightConjugate, MonoidHom.map_zpowers]
  congr 1
  simp

theorem rightConjugate_sup (Q S : Subgroup G) (x : G) :
    rightConjugate (Q ⊔ S) x = rightConjugate Q x ⊔ rightConjugate S x :=
  Subgroup.map_sup _ _ _

theorem rightConjugate_inf (Q S : Subgroup G) (x : G) :
    rightConjugate (Q ⊓ S) x = rightConjugate Q x ⊓ rightConjugate S x :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj x⁻¹).injective

theorem sec3W_rightConjugate (R T : Subgroup G) (x : G) :
    sec3W (rightConjugate R x) (rightConjugate T x) = rightConjugate (sec3W R T) x := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    have h1 : rightConjugate (rightConjugate R x) y =
        rightConjugate (rightConjugate R (x * y * x⁻¹)) x := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    rw [h1]
    refine map_mono (le_sec3W ?_)
    rw [← rightConjugate_sup, centralizer_rightConjugate, h1,
      rightConjugate_le_rightConjugate_iff] at hy
    exact hy
  · rw [rightConjugate_le_iff]
    refine iSup₂_le fun z hz => ?_
    rw [← rightConjugate_le_iff]
    have h1 : rightConjugate (rightConjugate R z) x =
        rightConjugate (rightConjugate R x) (x⁻¹ * z * x) := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    rw [h1]
    refine le_sec3W ?_
    rw [← h1, ← rightConjugate_sup, centralizer_rightConjugate,
      rightConjugate_le_rightConjugate_iff]
    exact hz

theorem sec3V_rightConjugate (R T : Subgroup G) (x : G) :
    sec3V (rightConjugate R x) (rightConjugate T x) = rightConjugate (sec3V R T) x := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    have h1 : rightConjugate (rightConjugate R x) y =
        rightConjugate (rightConjugate R (x * y * x⁻¹)) x := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    rw [h1]
    refine map_mono (le_sec3V ?_)
    rw [sec3W_rightConjugate, centralizer_rightConjugate, h1,
      rightConjugate_le_rightConjugate_iff] at hy
    exact hy
  · rw [rightConjugate_le_iff]
    refine iSup₂_le fun z hz => ?_
    rw [← rightConjugate_le_iff]
    have h1 : rightConjugate (rightConjugate R z) x =
        rightConjugate (rightConjugate R x) (x⁻¹ * z * x) := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    rw [h1]
    refine le_sec3V ?_
    rw [← h1, sec3W_rightConjugate, centralizer_rightConjugate,
      rightConjugate_le_rightConjugate_iff]
    exact hz

theorem sec3W_symm {R T : Subgroup G} {w : G} (hT : T = rightConjugate R w) :
    sec3W T R = sec3W R T := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rw [hT, rightConjugate_mul] at hy ⊢
    exact le_sec3W (by rwa [sup_comm])
  · refine iSup₂_le fun z hz => ?_
    have h1 : rightConjugate R z = rightConjugate T (w⁻¹ * z) := by
      rw [hT, rightConjugate_mul, mul_inv_cancel_left]
    rw [h1] at hz ⊢
    exact le_sec3W (by rwa [sup_comm])

theorem sec3V_symm {R T : Subgroup G} {w : G} (hT : T = rightConjugate R w) :
    sec3V T R = sec3V R T := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => ?_
    rw [sec3W_symm hT] at hy
    rw [hT, rightConjugate_mul] at hy ⊢
    exact le_sec3V hy
  · refine iSup₂_le fun z hz => ?_
    have h1 : rightConjugate R z = rightConjugate T (w⁻¹ * z) := by
      rw [hT, rightConjugate_mul, mul_inv_cancel_left]
    rw [← sec3W_symm hT, h1] at hz
    rw [h1]
    exact le_sec3V hz

theorem mem_normalizer_sup {H K : Subgroup G} {x : G} (hH : x ∈ normalizer (H : Set G))
    (hK : x ∈ normalizer (K : Set G)) : x ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem mem_centralizer_sup {H K : Subgroup G} {x : G} (hH : x ∈ centralizer (H : Set G))
    (hK : x ∈ centralizer (K : Set G)) : x ∈ centralizer ((H ⊔ K : Subgroup G) : Set G) := by
  have h : zpowers x ≤ centralizer ((H ⊔ K : Subgroup G) : Set G) := by
    rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff, zpowers_le]
      exact hH
    · rw [← le_centralizer_iff, zpowers_le]
      exact hK
  exact h (mem_zpowers x)

theorem _root_.CFSG.ComponentClassification.AS76b.Lemma36.ConjData.rightConjugate [Finite G]
    {V Q B : Subgroup G} {y : G} (d : ConjData V Q B y) (x : G) :
    ConjData (rightConjugate V x) (rightConjugate Q x) (rightConjugate B x) (x⁻¹ * y * x) where
  elem := isElemAbelian_rightConjugate d.elem x
  le := map_mono d.le
  sup_eq := by rw [← rightConjugate_inf, ← rightConjugate_sup, d.sup_eq]
  le_centralizer := by
    rw [centralizer_rightConjugate]
    exact map_mono d.le_centralizer
  mem := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using d.mem
  mem_normalizer := by
    rw [mem_normalizer_rightConjugate_iff]
    simpa [mul_assoc] using d.mem_normalizer
  odd := by
    have h : x⁻¹ * y * x = x⁻¹ * y * x⁻¹⁻¹ := by rw [inv_inv]
    rw [h, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact d.odd
  trans := by
    intro b hb c hc' hb1 hc1
    rw [← rightConjugate_inf, mem_rightConjugate_iff] at hb hc'
    obtain ⟨k, hk⟩ := d.trans _ hb _ hc' (by simpa using hb1) (by simpa using hc1)
    refine ⟨k, ?_⟩
    have h1 : (x⁻¹ * y * x) ^ k = x⁻¹ * y ^ k * x := by
      have := conj_pow (a := x⁻¹) (b := y) (i := k)
      rwa [inv_inv] at this
    rw [h1]
    calc (x⁻¹ * y ^ k * x)⁻¹ * b * (x⁻¹ * y ^ k * x) =
        x⁻¹ * ((y ^ k)⁻¹ * (x * b * x⁻¹) * y ^ k) * x := by group
      _ = c := by rw [hk]; group
  four_le := by
    rw [rightConjugate_card]
    exact d.four_le
  card_lt := by
    rw [rightConjugate_card, rightConjugate_card]
    exact d.card_lt

structure JData (A R T : Subgroup G) (p : G) (J : Subgroup G) (y : G) : Prop where
  le : J ≤ A
  mem : p ∈ J
  ne_one : p ≠ 1
  aPart_mem : ∃ t ∈ T, t⁻¹ * p ∈ R
  aPart_le : ∀ t ∈ T, ∀ p' ∈ A, t⁻¹ * p' ∈ R → p' ∈ J
  le_centralizer : ∀ b ∈ A, Commute (b * p * b⁻¹) p →
    J ≤ centralizer ({b * p * b⁻¹} : Set G)
  le_normalizer : A ⊓ centralizer ({p} : Set G) ≤ normalizer (J : Set G)
  trans : ∀ j ∈ J, j ≠ 1 → ∀ j' ∈ J, j' ≠ 1 →
    ∃ a ∈ A ⊓ normalizer (J : Set G), a * j * a⁻¹ = j'
  free : ∀ a ∈ A ⊓ normalizer (J : Set G), ∀ j ∈ J, j ≠ 1 → a * j * a⁻¹ = j →
    a ∈ centralizer (J : Set G)
  y_mem : y ∈ A ⊓ normalizer (J : Set G)
  odd : Odd (orderOf y)
  cyclic : ∀ a ∈ A ⊓ normalizer (J : Set G), ∃ k : ℕ, (y ^ k)⁻¹ * a ∈ centralizer (J : Set G)
  sylow : ∀ x ∈ A ⊓ centralizer ({p} : Set G), (∀ b ∈ A, Commute (b * p * b⁻¹) p →
    x ∈ centralizer ({b * p * b⁻¹} : Set G)) → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ J

namespace Sec3

variable [Finite G] {A R T : Subgroup G} {g : G} (hc : Sec3 A R T g)
include hc

theorem exists_conj : ∃ w : G, T = rightConjugate R w := by
  obtain ⟨w, hw, -⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  exact ⟨w, hw⟩

theorem commute_of_mem {a r : G} (ha : a ∈ A) (hr : r ∈ R) : Commute a r :=
  (mem_centralizer_iff.mp (hc.sylowR.le hr) a ha)

theorem commute_T_R {t r : G} (ht : t ∈ T) (hr : r ∈ R) : Commute t r :=
  (mem_centralizer_iff.mp (hc.le_centralizer ht) r hr).symm

theorem commute_R (h32 : Lemma32) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R) : Commute r r' :=
  congrArg Subtype.val ((hc.elemR h32).1.is_comm.comm ⟨r, hr⟩ ⟨r', hr'⟩)

variable (h32 : Lemma32) (h4 : Asc75Theorem4) (h34 : Asc08Lemma34)
include h32 h4 h34

theorem exists_mul_of_mem {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) {z s : G}
    (hz : rightConjugate R z ≤ centralizer ((R ⊔ T : Subgroup G) : Set G))
    (hs : s ∈ rightConjugate R z) : ∃ r ∈ R, r⁻¹ * s ∈ A ⊓ centralizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSR : rightConjugate R z ≤ centralizer (R : Set G) :=
    hz.trans (centralizer_le fun r hr => mem_sup_left hr)
  have hSAK := conj_le_sup_centralizer (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR ⟨z, rfl⟩ hSR
  have hRS : IsPGroup 2 ↥(R ⊔ rightConjugate R z) :=
    IsPGroup.to_sup_of_normal_left' hc.sylowR.isPGroup (hc.sylowR.isPGroup.map _)
      (hSR.trans (centralizer_le_normalizer _))
  have hle := le_sup_of_isSylowOf (centralizer_le_normalizer _) hc.sylowR le_sup_left hRS
    (sup_le (hc.sylowR.le.trans le_sup_right) hSAK)
  have hRA : R ≤ normalizer (A : Set G) := hc.sylowR.le.trans (centralizer_le_normalizer _)
  have hs' : s ∈ ((R ⊔ A : Subgroup G) : Set G) := hle (mem_sup_right hs)
  rw [coe_mul_of_left_le_normalizer_right R A hRA] at hs'
  obtain ⟨r, hr, a, ha, rfl⟩ := hs'
  refine ⟨r, hr, ?_⟩
  rw [inv_mul_cancel_left]
  obtain ⟨t, ht, hρ⟩ := hJ.aPart_mem
  have hsC := hz hs
  have hst : Commute (r * a) t :=
    (mem_centralizer_iff.mp hsC t (mem_sup_right ht)).symm
  have hsρ : Commute (r * a) (t⁻¹ * p) :=
    (mem_centralizer_iff.mp hsC _ (mem_sup_left hρ)).symm
  have hrt : Commute r t := (hc.commute_T_R ht hr).symm
  have hrρ : Commute r (t⁻¹ * p) := hc.commute_R h32 hr hρ
  have hat : Commute a t := by
    have h1 : Commute (r⁻¹ * (r * a)) t := (hrt.inv_left).mul_left hst
    rwa [inv_mul_cancel_left] at h1
  have haρ : Commute a (t⁻¹ * p) := by
    have h1 : Commute (r⁻¹ * (r * a)) (t⁻¹ * p) := (hrρ.inv_left).mul_left hsρ
    rwa [inv_mul_cancel_left] at h1
  have hap : Commute a p := by
    have h1 : Commute a (t * (t⁻¹ * p)) := hat.mul_right haρ
    rwa [mul_inv_cancel_left] at h1
  have haN : a ∈ normalizer (J : Set G) :=
    hJ.le_normalizer (mem_inf.mpr ⟨ha, mem_centralizer_singleton_iff.mpr hap.eq⟩)
  refine mem_inf.mpr ⟨ha, hJ.free a (mem_inf.mpr ⟨ha, haN⟩) p hJ.mem hJ.ne_one ?_⟩
  rw [hap.eq, mul_inv_cancel_right]

theorem exists_aPart_mem {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) {t : G}
    (ht : t ∈ T) : ∃ p' ∈ J, t⁻¹ * p' ∈ R := by
  obtain ⟨p', hp'A, hρ'⟩ := hc.exists_aPart h32 h4 h34 ht
  exact ⟨p', hJ.aPart_le t ht p' hp'A hρ', hρ'⟩

theorem rightConjugate_le_centralizer {p y : G} {J : Subgroup G} (hJ : JData A R T p J y)
    {b : G} (hb : b ∈ A ⊓ normalizer (J : Set G)) :
    rightConjugate T b ≤ centralizer (sec3W R T : Set G) := by
  rw [le_centralizer_iff]
  refine iSup₂_le fun z hz => ?_
  intro s hs
  rw [mem_centralizer_iff]
  intro u hu
  obtain ⟨r, hr, hra⟩ := hc.exists_mul_of_mem h32 h4 h34 hJ hz hs
  obtain ⟨haA, haJ⟩ := mem_inf.mp hra
  rw [SetLike.mem_coe, mem_rightConjugate_iff] at hu
  obtain ⟨p', hp'J, hρ'⟩ := hc.exists_aPart_mem h32 h4 h34 hJ hu
  obtain ⟨hbA, hbJ⟩ := mem_inf.mp hb
  have hj : b⁻¹ * p' * b ∈ J := by
    have := (mem_normalizer_iff.mp (inv_mem hbJ) p').mp hp'J
    simpa using this
  have hbρ : Commute b ((b * u * b⁻¹)⁻¹ * p') := hc.commute_of_mem hbA hρ'
  have hu' : u = (b⁻¹ * p' * b) * ((b * u * b⁻¹)⁻¹ * p')⁻¹ := by
    have h1 : b⁻¹ * ((b * u * b⁻¹)⁻¹ * p')⁻¹ * b = ((b * u * b⁻¹)⁻¹ * p')⁻¹ := by
      rw [mul_assoc, ← hbρ.inv_right.eq, inv_mul_cancel_left]
    calc u = b⁻¹ * p' * (((b * u * b⁻¹)⁻¹ * p')⁻¹) * b := by group
      _ = (b⁻¹ * p' * b) * (b⁻¹ * ((b * u * b⁻¹)⁻¹ * p')⁻¹ * b) := by group
      _ = _ := by rw [h1]
  have hs' : s = r * (r⁻¹ * s) := by group
  have hjr : Commute (b⁻¹ * p' * b) r := hc.commute_of_mem (hJ.le hj) hr
  have hja : Commute (b⁻¹ * p' * b) (r⁻¹ * s) :=
    mem_centralizer_iff.mp haJ _ hj
  have hρr : Commute ((b * u * b⁻¹)⁻¹ * p')⁻¹ r :=
    (hc.commute_R h32 hρ' hr).inv_left
  have hρa : Commute ((b * u * b⁻¹)⁻¹ * p')⁻¹ (r⁻¹ * s) :=
    ((hc.commute_of_mem haA hρ').symm).inv_left
  have hcomm : Commute ((b⁻¹ * p' * b) * ((b * u * b⁻¹)⁻¹ * p')⁻¹) (r * (r⁻¹ * s)) :=
    (hjr.mul_right hja).mul_left (hρr.mul_right hρa)
  rw [← hs', ← hu'] at hcomm
  exact hcomm.eq

theorem rightConjugate_le_sec3V {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) {b : G}
    (hb : b ∈ A ⊓ normalizer (J : Set G)) : rightConjugate T b ≤ sec3V R T := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have h := hc.rightConjugate_le_centralizer h32 h4 h34 hJ hb
  rw [hw, rightConjugate_mul] at h ⊢
  exact le_sec3V h

theorem le_inf_sec3V {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    J ≤ sec3V R T ⊓ A := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hRV : R ≤ sec3V R T := le_sup_left.trans (le_sec3V_of ⟨w, hw⟩)
  intro j hj
  refine mem_inf.mpr ⟨?_, hJ.le hj⟩
  by_cases hj1 : j = 1
  · rw [hj1]
    exact one_mem _
  obtain ⟨a, ha, rfl⟩ := hJ.trans p hJ.mem hJ.ne_one j hj hj1
  obtain ⟨t, ht, hρ⟩ := hJ.aPart_mem
  have haA : a ∈ A := (mem_inf.mp ha).1
  have ha' : a⁻¹ ∈ A ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨inv_mem haA, inv_mem (mem_inf.mp ha).2⟩
  have hat : a * t * a⁻¹ ∈ sec3V R T := by
    apply hc.rightConjugate_le_sec3V h32 h4 h34 hJ ha'
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using ht
  have hcomm : Commute a (t⁻¹ * p) := hc.commute_of_mem haA hρ
  have h1 : a * p * a⁻¹ = (a * t * a⁻¹) * (t⁻¹ * p) := by
    calc a * p * a⁻¹ = a * t * (t⁻¹ * p) * a⁻¹ := by group
      _ = a * t * (a⁻¹ * (a * (t⁻¹ * p) * a⁻¹)) := by group
      _ = (a * t * a⁻¹) * (t⁻¹ * p) := by rw [hcomm.eq]; group
  rw [h1]
  exact mul_mem hat (hRV hρ)

theorem inf_sec3V_le {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    sec3V R T ⊓ A ≤ J := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hVe : IsElemAbelian 2 (sec3V R T) :=
    isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩
  have hJV := hc.le_inf_sec3V h32 h4 h34 hJ
  obtain ⟨t, ht, hρ⟩ := hJ.aPart_mem
  intro v hv
  obtain ⟨hvV, hvA⟩ := mem_inf.mp hv
  have hcommV : ∀ x ∈ sec3V R T, Commute v x := fun x hx =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hvV⟩ ⟨x, hx⟩)
  have hvp : v ∈ centralizer ({p} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hcommV p (mem_inf.mp (hJV hJ.mem)).1).eq
  have hvΔ : ∀ b ∈ A, Commute (b * p * b⁻¹) p →
      v ∈ centralizer ({b * p * b⁻¹} : Set G) := by
    intro b hbA hbp
    have hJb : ∀ j ∈ J, Commute (b * j * b⁻¹) p := by
      intro j hj
      have hc' : Commute (b⁻¹ * p * b⁻¹⁻¹) p := by
        have h1 : Commute (b⁻¹ * (b * p * b⁻¹) * b) (b⁻¹ * p * b) := by
          have := (hbp.conj b⁻¹)
          simpa [mul_assoc] using this
        simpa [mul_assoc] using h1.symm
      have hj' := mem_centralizer_singleton_iff.mp (hJ.le_centralizer b⁻¹ (inv_mem hbA) hc' hj)
      have h2 : Commute j (b⁻¹ * p * b) := by
        simp only [inv_inv] at hj'
        exact hj'
      have h3 := h2.conj b
      simpa [mul_assoc] using h3
    have hJJ : ∀ j ∈ J, ∀ j₀ ∈ J, Commute j (b * j₀ * b⁻¹) := by
      intro j hj j₀ hj₀
      by_cases h1 : j₀ = 1
      · rw [h1, mul_one, mul_inv_cancel]
        exact Commute.one_right j
      obtain ⟨a, ha, rfl⟩ := hJ.trans p hJ.mem hJ.ne_one j₀ hj₀ h1
      have hba : b * (a * p * a⁻¹) * b⁻¹ = (b * a) * p * (b * a)⁻¹ := by group
      have hc2 : Commute ((b * a) * p * (b * a)⁻¹) p := by
        rw [← hba]
        exact hJb _ hj₀
      have := hJ.le_centralizer (b * a) (mul_mem hbA (mem_inf.mp ha).1) hc2 hj
      rw [hba]
      exact mem_centralizer_singleton_iff.mp this
    have hT'W : rightConjugate T b⁻¹ ≤ sec3W R T := by
      have hcen : rightConjugate T b⁻¹ ≤ centralizer ((R ⊔ T : Subgroup G) : Set G) := by
        refine le_centralizer_sup ?_ ?_
        · intro u hu
          rw [mem_centralizer_iff]
          intro r hr
          rw [mem_rightConjugate_iff, inv_inv] at hu
          have hbr : Commute b r := hc.commute_of_mem hbA hr
          have h1 : Commute (b * (b⁻¹ * u * b) * b⁻¹) r :=
            (hbr.mul_left (hc.commute_T_R hu hr)).mul_left hbr.inv_left
          rw [show b * (b⁻¹ * u * b) * b⁻¹ = u by group] at h1
          exact h1.eq.symm
        · intro u hu
          rw [mem_centralizer_iff]
          intro t'' ht''
          rw [mem_rightConjugate_iff, inv_inv] at hu
          obtain ⟨p', hp'J, hρ'⟩ := hc.exists_aPart_mem h32 h4 h34 hJ hu
          obtain ⟨p'', hp''J, hρ''⟩ := hc.exists_aPart_mem h32 h4 h34 hJ ht''
          set t' := b⁻¹ * u * b with ht'
          have hu' : u = (b * p' * b⁻¹) * (t'⁻¹ * p')⁻¹ := by
            have hbρ : Commute b (t'⁻¹ * p') := hc.commute_of_mem hbA hρ'
            calc u = b * t' * b⁻¹ := by rw [ht']; group
              _ = b * p' * (t'⁻¹ * p')⁻¹ * b⁻¹ := by group
              _ = (b * p' * b⁻¹) * (b * (t'⁻¹ * p')⁻¹ * b⁻¹) := by group
              _ = _ := by rw [hbρ.inv_right.eq, mul_inv_cancel_right]
          have ht''' : t'' = p'' * (t''⁻¹ * p'')⁻¹ := by group
          have hbp'A : b * p' * b⁻¹ ∈ A := mul_mem (mul_mem hbA (hJ.le hp'J)) (inv_mem hbA)
          have h1 : Commute (b * p' * b⁻¹) p'' := (hJJ p'' hp''J p' hp'J).symm
          have h2 : Commute (b * p' * b⁻¹) (t''⁻¹ * p'')⁻¹ :=
            (hc.commute_of_mem hbp'A hρ'').inv_right
          have h3 : Commute (t'⁻¹ * p')⁻¹ p'' :=
            ((hc.commute_of_mem (hJ.le hp''J) hρ').symm).inv_left
          have h4' : Commute (t'⁻¹ * p')⁻¹ (t''⁻¹ * p'')⁻¹ :=
            (hc.commute_R h32 hρ' hρ'').inv_inv
          have h5 : Commute ((b * p' * b⁻¹) * (t'⁻¹ * p')⁻¹) (p'' * (t''⁻¹ * p'')⁻¹) :=
            (h1.mul_right h2).mul_left (h3.mul_right h4')
          rw [← hu', ← ht'''] at h5
          exact h5.eq.symm
      rw [hw, rightConjugate_mul] at hcen ⊢
      exact le_sec3W hcen
    have hbt : b * t * b⁻¹ ∈ rightConjugate T b⁻¹ := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using ht
    have hvbt : Commute v (b * t * b⁻¹) :=
      (mem_centralizer_iff.mp (sec3V_le_centralizer R T hvV) _ (hT'W hbt)).symm
    have hvρ : Commute v (t⁻¹ * p) := hc.commute_of_mem hvA hρ
    have hbρ : Commute b (t⁻¹ * p) := hc.commute_of_mem hbA hρ
    have hbp' : b * p * b⁻¹ = (b * t * b⁻¹) * (t⁻¹ * p) := by
      calc b * p * b⁻¹ = b * t * (t⁻¹ * p) * b⁻¹ := by group
        _ = (b * t * b⁻¹) * (b * (t⁻¹ * p) * b⁻¹) := by group
        _ = _ := by rw [hbρ.eq, mul_inv_cancel_right]
    rw [mem_centralizer_singleton_iff, hbp']
    exact (hvbt.mul_right hvρ).eq
  have hv2 : v ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact hVe.2 v hvV
  exact hJ.sylow v (mem_inf.mpr ⟨hvA, hvp⟩) hvΔ ⟨1, hv2⟩

theorem inf_sec3V_eq {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    sec3V R T ⊓ A = J :=
  le_antisymm (hc.inf_sec3V_le h32 h4 h34 hJ) (hc.le_inf_sec3V h32 h4 h34 hJ)

theorem sec3V_eq_sup {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    sec3V R T = R ⊔ J := by
  have h := (lemma35 h32 (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR hc.sylowT
    hc.le_centralizer).2.1
  rwa [hc.inf_sec3V_eq h32 h4 h34 hJ] at h

theorem y_mem_normalizer {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    y ∈ normalizer (sec3V R T : Set G) := by
  obtain ⟨hyA, hyJ⟩ := mem_inf.mp hJ.y_mem
  rw [hc.sec3V_eq_sup h32 h4 h34 hJ]
  refine mem_normalizer_sup (centralizer_le_normalizer _ ?_) hyJ
  rw [mem_centralizer_iff]
  intro r hr
  exact (hc.commute_of_mem hyA hr).eq.symm

omit h32 h4 h34 in
theorem card_mul_le : Nat.card R * Nat.card R ≤ Nat.card (sec3V R T) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have h1 := card_sup_eq_mul hc.le_normalizer_R hc.inf_eq_bot
  rw [hc.card_eq] at h1
  rw [← h1]
  exact card_le_of_le (le_sec3V_of ⟨w, hw⟩)

theorem conjData_R {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    ConjData (sec3V R T) R A y := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have hVe : IsElemAbelian 2 (sec3V R T) :=
    isElemAbelian_sec3V (hc.elemR h32) hc.le_centralizer ⟨w, hw⟩
  have hVA := hc.inf_sec3V_eq h32 h4 h34 hJ
  have hx : rightConjugate R 1 ≤ sec3V R T := by
    rw [rightConjugate_one]
    exact le_sup_left.trans (le_sec3V_of ⟨w, hw⟩)
  have hy : y ∈ rightConjugate A 1 ⊓ normalizer (sec3V R T : Set G) := by
    rw [rightConjugate_one]
    exact mem_inf.mpr ⟨(mem_inf.mp hJ.y_mem).1, hc.y_mem_normalizer h32 h4 h34 hJ⟩
  have htr : ∀ b ∈ sec3V R T ⊓ rightConjugate A 1, ∀ c ∈ sec3V R T ⊓ rightConjugate A 1,
      b ≠ 1 → c ≠ 1 → ∃ k : ℕ, (y ^ k)⁻¹ * b * y ^ k = c := by
    rw [rightConjugate_one, hVA]
    intro b hb c hc' hb1 hc1
    obtain ⟨a, ha, rfl⟩ := hJ.trans b hb hb1 c hc' hc1
    obtain ⟨k, hk⟩ := hJ.cyclic a⁻¹ (inv_mem ha)
    refine ⟨k, ?_⟩
    have hyk : y ^ k ∈ normalizer (J : Set G) := pow_mem (mem_inf.mp hJ.y_mem).2 k
    have hb' : (y ^ k)⁻¹ * b * y ^ k ∈ J := by
      have := (mem_normalizer_iff.mp (inv_mem hyk) b).mp hb
      simpa using this
    have hz := mem_centralizer_iff.mp hk _ hb'
    calc (y ^ k)⁻¹ * b * y ^ k =
        ((y ^ k)⁻¹ * a⁻¹)⁻¹ * (((y ^ k)⁻¹ * a⁻¹) * ((y ^ k)⁻¹ * b * y ^ k)) := by group
      _ = ((y ^ k)⁻¹ * a⁻¹)⁻¹ * (((y ^ k)⁻¹ * b * y ^ k) * ((y ^ k)⁻¹ * a⁻¹)) := by rw [← hz]
      _ = a * b * a⁻¹ := by group
  have h := Lemma36.conjData (lemma33Two_of h32 h4 h34) hc.hyp hc.sylowR hVe hc.card_mul_le
    hc.four_le hx hy hJ.odd htr
  rwa [rightConjugate_one, rightConjugate_one] at h

theorem normalizer_R {p y : G} {J : Subgroup G} (hJ : JData A R T p J y) :
    ∀ z ∈ normalizer (A : Set G) ⊓ normalizer (sec3V R T : Set G),
      z⁻¹ * y * z ∈ zpowers y ⊔ centralizer (sec3V R T : Set G) := by
  intro z hz
  obtain ⟨hzA, hzV⟩ := mem_inf.mp hz
  have hVA := hc.inf_sec3V_eq h32 h4 h34 hJ
  have hzJ : z ∈ normalizer (J : Set G) := by
    rw [← hVA, mem_normalizer_iff]
    intro x
    simp only [mem_inf]
    rw [mem_normalizer_iff.mp hzV x, mem_normalizer_iff.mp hzA x]
  obtain ⟨hyA, hyJ⟩ := mem_inf.mp hJ.y_mem
  have hmem : z⁻¹ * y * z ∈ A ⊓ normalizer (J : Set G) := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hzA) y).mp hyA
      simpa using this
    · exact mul_mem (mul_mem (inv_mem hzJ) hyJ) hzJ
  obtain ⟨k, hk⟩ := hJ.cyclic _ hmem
  have hkA : (y ^ k)⁻¹ * (z⁻¹ * y * z) ∈ A :=
    mul_mem (inv_mem (pow_mem hyA k)) (mem_inf.mp hmem).1
  have hkV : (y ^ k)⁻¹ * (z⁻¹ * y * z) ∈ centralizer (sec3V R T : Set G) := by
    rw [hc.sec3V_eq_sup h32 h4 h34 hJ]
    refine mem_centralizer_sup ?_ hk
    rw [mem_centralizer_iff]
    intro r hr
    exact (hc.commute_of_mem hkA hr).eq.symm
  have : z⁻¹ * y * z = y ^ k * ((y ^ k)⁻¹ * (z⁻¹ * y * z)) := by group
  rw [this]
  exact mul_mem (mem_sup_left (pow_mem (mem_zpowers y) k)) (mem_sup_right hkV)

theorem conjData_T {p' y' : G} {J' : Subgroup G}
    (hJ' : JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p' J' y') :
    ConjData (sec3V R T) T (rightConjugate A g) (g⁻¹ * y' * g) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  have d := (hc.swap.conjData_R h32 h4 h34 hJ').rightConjugate g
  rwa [sec3V_rightConjugate, rightConjugate_inv_rightConjugate,
    rightConjugate_inv_rightConjugate, sec3V_symm hw] at d

theorem normalizer_T {p' y' : G} {J' : Subgroup G}
    (hJ' : JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p' J' y') :
    ∀ z ∈ normalizer (rightConjugate A g : Set G) ⊓ normalizer (sec3V R T : Set G),
      z⁻¹ * (g⁻¹ * y' * g) * z ∈ zpowers (g⁻¹ * y' * g) ⊔ centralizer (sec3V R T : Set G) := by
  obtain ⟨w, hw⟩ := hc.exists_conj
  intro z hz
  obtain ⟨hzA, hzV⟩ := mem_inf.mp hz
  have hV' : sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) =
      rightConjugate (sec3V R T) g⁻¹ := by
    rw [sec3V_rightConjugate, sec3V_symm hw]
  have hz' : g * z * g⁻¹ ∈ normalizer (A : Set G) ⊓
      normalizer (sec3V (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) : Set G) := by
    refine mem_inf.mpr ⟨(mem_normalizer_rightConjugate_iff A g z).mp hzA, ?_⟩
    rw [hV', mem_normalizer_rightConjugate_iff]
    simpa [mul_assoc] using hzV
  have h := hc.swap.normalizer_R h32 h4 h34 hJ' _ hz'
  rw [hV'] at h
  have h2 : g⁻¹ * ((g * z * g⁻¹)⁻¹ * y' * (g * z * g⁻¹)) * g ∈
      rightConjugate (zpowers y' ⊔ centralizer (rightConjugate (sec3V R T) g⁻¹ : Set G)) g := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using h
  rw [rightConjugate_sup, rightConjugate_zpowers, centralizer_rightConjugate,
    rightConjugate_inv_rightConjugate] at h2
  have h3 : g⁻¹ * ((g * z * g⁻¹)⁻¹ * y' * (g * z * g⁻¹)) * g = z⁻¹ * (g⁻¹ * y' * g) * z := by
    group
  rwa [h3] at h2

omit h32 h4 h34 in
theorem R_ne_T : R ≠ T := by
  intro h
  apply hc.R_ne_bot
  have h1 := hc.inf_eq_bot
  rwa [← h, inf_idem] at h1

theorem pairData_RT {p y p' y' : G} {J J' : Subgroup G} (hJ : JData A R T p J y)
    (hJ' : JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p' J' y') :
    PairData (sec3V R T) R A T (rightConjugate A g) y (g⁻¹ * y' * g) := by
  obtain ⟨w, hw, hAw⟩ := Lemma36.exists_conj_eq hc.sylowR hc.sylowT
  have d₁ : ConjData (sec3V R T) (rightConjugate R 1) (rightConjugate A 1) y := by
    rw [rightConjugate_one, rightConjugate_one]
    exact hc.conjData_R h32 h4 h34 hJ
  have d₂ : ConjData (sec3V R T) (rightConjugate R w) (rightConjugate A w) (g⁻¹ * y' * g) := by
    rw [← hw, hAw]
    exact hc.conjData_T h32 h4 h34 hJ'
  have hn₁ : ∀ z ∈ normalizer (rightConjugate A 1 : Set G) ⊓ normalizer (sec3V R T : Set G),
      z⁻¹ * y * z ∈ zpowers y ⊔ centralizer (sec3V R T : Set G) := by
    rw [rightConjugate_one]
    exact hc.normalizer_R h32 h4 h34 hJ
  have hn₂ : ∀ z ∈ normalizer (rightConjugate A w : Set G) ⊓ normalizer (sec3V R T : Set G),
      z⁻¹ * (g⁻¹ * y' * g) * z ∈ zpowers (g⁻¹ * y' * g) ⊔
        centralizer (sec3V R T : Set G) := by
    rw [hAw]
    exact hc.normalizer_T h32 h4 h34 hJ'
  have hne : rightConjugate R 1 ≠ rightConjugate R w := by
    rw [rightConjugate_one, ← hw]
    exact hc.R_ne_T
  have h := Lemma36.pairData hc.hyp hc.sylowR d₁ d₂ hn₁ hn₂ hne
  rwa [rightConjugate_one, rightConjugate_one, ← hw, hAw] at h

theorem dichotomy {p y p' y' : G} {J J' : Subgroup G} (hJ : JData A R T p J y)
    (hJ' : JData A (rightConjugate T g⁻¹) (rightConjugate R g⁻¹) p' J' y') :
    T ⊓ A = ⊥ ∨ T = sec3V R T ⊓ A := by
  have hp := hc.pairData_RT h32 h4 h34 hJ hJ'
  by_cases hX : ∀ x ∈ pairGroup (sec3V R T) A (rightConjugate A g), conjSub x R = R
  · exact Or.inr (hp.eq_of_normalizes hX).1
  · push Not at hX
    obtain ⟨x₀, hx₀, hx₀R⟩ := hX
    have hle := hp.le_of_ne_bot₁ hx₀ hx₀R inf_le_left hp.normalizes₂ hp.d₂.inf_ne_bot
    refine Or.inl (eq_bot_iff.mpr fun t ht => ?_)
    obtain ⟨htT, htA⟩ := mem_inf.mp ht
    have h1 : t ∈ T ⊓ (sec3V R T ⊓ rightConjugate A g) :=
      mem_inf.mpr ⟨htT, hle (mem_inf.mpr ⟨hp.d₂.le htT, htA⟩)⟩
    rwa [hp.d₂.inf_eq_bot] at h1

end Sec3

end CFSG.ComponentClassification.RankTwoClassical
