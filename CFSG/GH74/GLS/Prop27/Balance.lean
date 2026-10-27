module

public import CFSG.GH74.GLS.Prop27.Defs
public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.Goldschmidt.Steps.AxB
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.GH74.GLS.Prop27

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.E2 CFSG.Blueprint Subgroup
  Assembly.LowTwoRank CFSG.Assembly.Dichotomy

theorem conj_mem_involutionOddCore' {Y : Type} [Group Y] {v a h : Y}
    (ha : a ∈ centralizer ({v} : Set Y)) (hh : h ∈ involutionOddCore v) :
    a * h * a⁻¹ ∈ involutionOddCore v := by
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  exact ⟨⟨a, ha⟩ * h₀ * ⟨a, ha⟩⁻¹,
    (CFSG.Assembly.oddCore_normal _).conj_mem h₀ hh₀ ⟨a, ha⟩, rfl⟩

theorem involutionOddCore_le_centralizer {Y : Type} [Group Y] (v : Y) :
    involutionOddCore v ≤ centralizer ({v} : Set Y) :=
  Subgroup.map_subtype_le _

theorem involutionOddCore_eq_bot_iff' {Y : Type} [Group Y] (v : Y) :
    involutionOddCore v = ⊥ ↔ pPrimeCore 2 ↥(centralizer ({v} : Set Y)) = ⊥ := by
  unfold involutionOddCore
  rw [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
    CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]

theorem le_involutionOddCore_of_normalized {Y : Type} [Group Y] [Finite Y] {v : Y}
    {W : Subgroup Y} (hWC : W ≤ centralizer ({v} : Set Y))
    (hWn : ∀ c ∈ centralizer ({v} : Set Y), ∀ w ∈ W, c * w * c⁻¹ ∈ W)
    (hWodd : Odd (Nat.card W)) : W ≤ involutionOddCore v := by
  set C : Subgroup Y := centralizer ({v} : Set Y) with hC
  have hnorm : (W.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hWn c c.2 n hn
  have hcard : Nat.card (W.subgroupOf C) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  have hle : W.subgroupOf C ≤ Assembly.oddCore C :=
    le_sSup ⟨hnorm, by rw [hcard]; exact hWodd⟩
  intro w hw
  exact ⟨⟨w, hWC hw⟩, hle (by simpa [Subgroup.mem_subgroupOf] using hw), rfl⟩

theorem involutionOddCore_inf_le_of_oddCoreFree {G : Type} [Group G] [Finite G] {a b : G}
    (ha : orderOf a = 2) (hab : a * b = b * a)
    (hP : ∀ v : CentralizerBar b, orderOf v = 2 → involutionOddCore v = ⊥) :
    involutionOddCore a ⊓ centralizer ({b} : Set G) ≤ involutionOddCore b := by
  classical
  set H : Subgroup G := centralizer ({b} : Set G) with hH
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  have hOn : O.Normal := pPrimeCore_normal
  set π : ↥H →* CentralizerBar b := QuotientGroup.mk' O with hπ
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hab
  set a' : ↥H := ⟨a, haH⟩ with ha'def
  set v : CentralizerBar b := π a' with hvdef
  have hOcop : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  have ha'2 : orderOf a' = 2 := by rw [← Subgroup.orderOf_coe]; exact ha
  have hpow : a' ^ 2 = 1 := by
    have := pow_orderOf_eq_one a'
    rwa [ha'2] at this
  have hv2 : orderOf v = 2 := by
    apply orderOf_eq_prime
    · show π a' ^ 2 = 1
      rw [← map_pow, hpow, map_one]
    · intro h1
      have hmem : a' ∈ O := by
        rw [hvdef, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hdvd : orderOf (⟨a', hmem⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, ha'2] at hdvd
      exact absurd (Nat.Coprime.eq_one_of_dvd hOcop hdvd) (by norm_num)
  have hfact : Fact (IsPGroup 2 ↥(zpowers a')) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha'2]; norm_num)⟩
  have hcen : centralizer (((zpowers a').map π : Subgroup (↥H ⧸ O)) : Set (↥H ⧸ O)) =
      (centralizer ((zpowers a' : Subgroup ↥H) : Set ↥H)).map π :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers a') O hOn hOcop
  have hmapz : (zpowers a').map π = zpowers v := MonoidHom.map_zpowers π a'
  rw [hmapz] at hcen
  have hcenv : centralizer ({v} : Set (CentralizerBar b)) =
      (centralizer ({a'} : Set ↥H)).map π := by
    have h1 : centralizer ((zpowers v : Subgroup (CentralizerBar b)) : Set (CentralizerBar b)) =
        centralizer ({v} : Set (CentralizerBar b)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : centralizer ((zpowers a' : Subgroup ↥H) : Set ↥H) =
        centralizer ({a'} : Set ↥H) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [← h1, hcen, h2]
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = involutionOddCore a ⊓ H := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup (CentralizerBar b), W = (D.subgroupOf H).map π := ⟨_, rfl⟩
  have hDa : D ≤ involutionOddCore a := hD ▸ inf_le_left
  have hDH : D ≤ H := hD ▸ inf_le_right
  have hWC : W ≤ centralizer ({v} : Set (CentralizerBar b)) := by
    rw [hW]
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hda : (d : G) * a = a * d := by
      have hd1 : (d : G) ∈ involutionOddCore a := hDa (Subgroup.mem_subgroupOf.mp hd)
      have hdc : (d : G) ∈ centralizer ({a} : Set G) :=
        involutionOddCore_le_centralizer a hd1
      exact Subgroup.mem_centralizer_singleton_iff.mp hdc
    rw [hvdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hda
  have hWn : ∀ c ∈ centralizer ({v} : Set (CentralizerBar b)), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hcv : c ∈ (centralizer ({a'} : Set ↥H)).map π := by
      rw [← hcenv]; exact hc
    obtain ⟨c₀, hc₀, rfl⟩ := hcv
    rw [hW] at hw ⊢
    obtain ⟨d, hd, rfl⟩ := hw
    refine ⟨c₀ * d * c₀⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have hc₀a : (c₀ : G) ∈ centralizer ({a} : Set G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₀
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hd1 : (d : G) ∈ involutionOddCore a := hDa (Subgroup.mem_subgroupOf.mp hd)
    show c₀ * d * c₀⁻¹ ∈ D.subgroupOf H
    rw [Subgroup.mem_subgroupOf]
    have hmem : (c₀ : G) * d * (c₀ : G)⁻¹ ∈ involutionOddCore a :=
      conj_mem_involutionOddCore' hc₀a hd1
    rw [hD]
    exact Subgroup.mem_inf.mpr ⟨hmem, (c₀ * d * c₀⁻¹).2⟩
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W ∣ Nat.card (D.subgroupOf H) := by
      rw [hW]; exact Subgroup.card_map_dvd _ π
    have h2 : Nat.card (D.subgroupOf H) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
    have h3 : Nat.card D ∣ Nat.card (involutionOddCore a) := Subgroup.card_dvd_of_le hDa
    exact Odd.of_dvd_nat (odd_card_involutionOddCore a) (h1.trans (h2 ▸ h3))
  have hWle : W ≤ involutionOddCore v := le_involutionOddCore_of_normalized hWC hWn hWodd
  rw [hP v hv2] at hWle
  intro d hd
  have hdD : d ∈ D := by rw [hD]; exact hd
  have hdH : d ∈ H := hDH hdD
  have hmem : (⟨d, hdH⟩ : ↥H) ∈ D.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]; exact hdD
  have hπd : π ⟨d, hdH⟩ ∈ W := by rw [hW]; exact ⟨_, hmem, rfl⟩
  have h1 : π ⟨d, hdH⟩ = 1 := Subgroup.mem_bot.mp (hWle hπd)
  have hdO : (⟨d, hdH⟩ : ↥H) ∈ O := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  unfold involutionOddCore
  refine ⟨⟨d, hdH⟩, ?_, rfl⟩
  rw [CFSG.Assembly.Dichotomy.oddCore_eq_pPrimeCore]
  exact hdO


theorem involutionOddCore_mul_central {Y : Type} [Group Y] {z v : Y}
    (hz : ∀ y : Y, y * z = z * y) : involutionOddCore (z * v) = involutionOddCore v := by
  have h : centralizer ({z * v} : Set Y) = centralizer ({v} : Set Y) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      have h3 : x * (z * v) = z * (x * v) := by rw [← mul_assoc, hz x, mul_assoc]
      rw [h3, mul_assoc] at h1
      exact mul_left_cancel h1
    · intro h1
      calc x * (z * v) = z * (x * v) := by rw [← mul_assoc, hz x, mul_assoc]
        _ = z * (v * x) := by rw [h1]
        _ = z * v * x := by rw [mul_assoc]
  unfold involutionOddCore
  rw [h]

theorem conj_mem_involutionOddCore_of_central {Y : Type} [Group Y] {v g z : Y}
    (hz : ∀ y : Y, y * z = z * y) (hg : g * v * g⁻¹ = z * v) {r : Y}
    (hr : r ∈ involutionOddCore v) : g * r * g⁻¹ ∈ involutionOddCore v := by
  have h := involutionOddCore_map (MulAut.conj g) v
  rw [MulAut.conj_apply, hg, involutionOddCore_mul_central hz] at h
  rw [← h]
  exact ⟨r, hr, rfl⟩

theorem mul_conj_mul_inv {S : Type*} [Group S] (φ : MulAut S) (s : S) :
    φ * MulAut.conj s * φ⁻¹ = MulAut.conj (φ s) := by
  ext x
  simp [MulAut.conj_apply]

theorem even_card_of_quasisimple {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K) :
    Even (Nat.card K) := by
  obtain ⟨-, hs, hnab⟩ := hK
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center K)
  rw [hk]
  exact heven.mul_right k

section Action

variable {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]

noncomputable def actQuot : Y →* MulAut (↥K ⧸ center ↥K) where
  toFun y := QuotientGroup.congr (center ↥K) (center ↥K) (MulAut.conjNormal y)
    (Subgroup.map_center_eq _)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => simp [QuotientGroup.congr_mk]
  map_mul' y₁ y₂ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAut.mul_apply, QuotientGroup.congr_mk, map_mul]

theorem actQuot_mk (y : Y) (k : ↥K) :
    actQuot K y (QuotientGroup.mk k) = QuotientGroup.mk (MulAut.conjNormal y k) := by
  simp [actQuot, QuotientGroup.congr_mk]

theorem actQuot_eq_one_iff (y : Y) :
    actQuot K y = 1 ↔ ∀ k : ↥K, (MulAut.conjNormal y k)⁻¹ * k ∈ center ↥K := by
  constructor
  · intro h k
    have := congrArg (fun φ => φ (QuotientGroup.mk k)) h
    simp only [actQuot_mk, MulAut.one_apply] at this
    exact QuotientGroup.eq.mp this
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      simp only [actQuot_mk, MulAut.one_apply]
      exact QuotientGroup.eq.mpr (h x)

theorem mul_comm_of_actQuot_eq_one (hK : Group.IsPerfect ↥K) {y : Y} (hy : actQuot K y = 1) :
    ∀ k ∈ K, y * k = k * y := by
  set X : Subgroup Y := (actQuot K).ker with hX
  set Zi : Subgroup Y := (center ↥K).map K.subtype with hZi
  have hZc : Zi ≤ centralizer (K : Set Y) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.mem_center_iff.mp hz ⟨k, hk⟩
    exact congrArg Subtype.val this
  have h1 : ⁅K, X⁆ ≤ Zi := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ x hx
    have hx1 : actQuot K x = 1 := hx
    have := (actQuot_eq_one_iff K x).mp hx1 ⟨g₁⁻¹, K.inv_mem hg₁⟩
    refine ⟨((MulAut.conjNormal x ⟨g₁⁻¹, K.inv_mem hg₁⟩)⁻¹ * ⟨g₁⁻¹, K.inv_mem hg₁⟩)⁻¹,
      Subgroup.inv_mem _ this, ?_⟩
    simp only [Subgroup.subtype_apply, Subgroup.coe_inv, Subgroup.coe_mul,
      MulAut.conjNormal_apply, commutatorElement_def]
    group
  have h2 : ⁅⁅K, X⁆, K⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (h1.trans hZc)
  have h3 := CFSG.LocalCores.perfect_double_commutator hK h2
  have h4 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3
  intro k hk
  have := Subgroup.mem_centralizer_iff.mp (h4 hk) y hy
  exact this

end Action

section Step

variable {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]

theorem actQuot_coe (k : ↥K) :
    actQuot K (k : Y) = MulAut.conj (QuotientGroup.mk k : ↥K ⧸ center ↥K) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    simp only [actQuot_mk, MulAut.conj_apply]
    rfl

theorem center_quotient_eq_bot {Q : Type*} [Group Q] (hq : IsQuasisimple Q) :
    center (Q ⧸ center Q) = ⊥ := by
  obtain ⟨-, hs, a, b, hab⟩ := hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (Q ⧸ center Q)) with h | h
  · exact h
  · exfalso
    apply hab
    have ha : a ∈ center (Q ⧸ center Q) := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem conj_injective_of_center_bot {S : Type*} [Group S] (h : center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro s t hst
  have h1 : MulAut.conj (t⁻¹ * s) = 1 := by rw [map_mul, map_inv, hst, inv_mul_cancel]
  have hc : t⁻¹ * s ∈ center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut S => φ g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * (t⁻¹ * s) = ((t⁻¹ * s) * g * (t⁻¹ * s)⁻¹) * (t⁻¹ * s) := by rw [this]
      _ = (t⁻¹ * s) * g := by group
  rw [h, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.mp hc).symm

theorem eq_one_of_isPGroup_two_of_odd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hodd : Odd (Nat.card P)) (x : P) : x = 1 := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n = 0 := by
    by_contra h
    have : 2 ∣ Nat.card P := hn ▸ dvd_pow_self 2 h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  have : Nat.card P = 1 := by rw [hn, hn0]; rfl
  exact (Nat.card_eq_one_iff_unique.mp this).1.elim x 1

variable [Finite Y]

theorem component_centralized_of_actQuot_eq_one (hq : IsQuasisimple ↥K)
    (hZ2 : IsPGroup 2 ↥(center ↥K)) {v : Y} (hρ : actQuot K v = 1) :
    ∀ r ∈ involutionOddCore v, ∀ k ∈ K, r * k = k * r := by
  set R : Subgroup Y := involutionOddCore v with hR
  set C : Subgroup Y := centralizer ({v} : Set Y) with hC
  have hRn : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R :=
    fun c hc r hr => conj_mem_involutionOddCore' hc hr
  have hRodd : Odd (Nat.card R) := odd_card_involutionOddCore v
  have hvK : ∀ k ∈ K, v * k = k * v := mul_comm_of_actQuot_eq_one K hq.1 hρ
  have hKC : K ≤ C := fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hvK k hk).symm
  intro r hr k hk
  set N : Subgroup Y := R ⊓ K with hN
  have hnorm : (N.subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, K.mul_mem (K.mul_mem g.2 (Subgroup.mem_inf.mp hn).2)
      (K.inv_mem g.2)⟩
    exact hRn g (hKC g.2) n (Subgroup.mem_inf.mp hn).1
  have hNodd : Odd (Nat.card (N.subgroupOf K)) := by
    have h1 : Nat.card (N.subgroupOf K) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ≤ K)).toEquiv
    rw [h1]
    exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le (inf_le_left : N ≤ R))
  have hbot : N.subgroupOf K = ⊥ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hnorm with h | h
    · exfalso
      have h1 : Nat.card (N.subgroupOf K) = Nat.card K := by rw [h]; exact Subgroup.card_top
      have h2 := even_card_of_quasisimple hq
      rw [← h1] at h2
      exact (Nat.not_even_iff_odd.mpr hNodd) h2
    · have hP : IsPGroup 2 ↥(N.subgroupOf K) :=
        hZ2.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)
      ext x
      simp only [Subgroup.mem_bot]
      constructor
      · intro hx
        have := eq_one_of_isPGroup_two_of_odd hP hNodd ⟨x, hx⟩
        exact congrArg Subtype.val this
      · rintro rfl; exact Subgroup.one_mem _
  have hcK : r * k * r⁻¹ * k⁻¹ ∈ K := by
    have hr' : r * k * r⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k hk r
    exact K.mul_mem hr' (K.inv_mem hk)
  have hcR : r * k * r⁻¹ * k⁻¹ ∈ R := by
    have h1 : k * r⁻¹ * k⁻¹ ∈ R := by
      have := hRn k (hKC hk) r⁻¹ (R.inv_mem hr)
      simpa using this
    have := R.mul_mem hr h1
    simpa [mul_assoc] using this
  have hcN : (⟨r * k * r⁻¹ * k⁻¹, hcK⟩ : ↥K) ∈ N.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_inf.mpr ⟨hcR, hcK⟩
  rw [hbot, Subgroup.mem_bot] at hcN
  have h1 : r * k * r⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hcN
  have := mul_inv_eq_one.mp h1
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this


theorem actQuot_eq_one_of_locBal (hq : IsQuasisimple ↥K)
    (hZY : ∀ z ∈ (center ↥K).map K.subtype, ∀ y : Y, y * z = z * y)
    (hLB : LocBal2 (fun S _ => Nonempty (S ≃* (↥K ⧸ center ↥K))))
    {v : Y} (hv : orderOf v = 2) (hρ : actQuot K v ≠ 1) :
    ∀ r ∈ involutionOddCore v, actQuot K r = 1 := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : Subgroup Y, R = involutionOddCore v := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Y, C = centralizer ({v} : Set Y) := ⟨_, rfl⟩
  have hRC : R ≤ C := by rw [hR, hC]; exact involutionOddCore_le_centralizer v
  have hRn : ∀ c ∈ C, ∀ r ∈ R, c * r * c⁻¹ ∈ R := by
    rw [hR, hC]; exact fun c hc r hr => conj_mem_involutionOddCore' hc hr
  have hRodd : Odd (Nat.card R) := by rw [hR]; exact odd_card_involutionOddCore v
  have hSZ : center (↥K ⧸ center ↥K) = ⊥ := center_quotient_eq_bot hq
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : Subgroup (MulAut (↥K ⧸ center ↥K)),
      X₁ = (K ⊔ C).map (actQuot K) := ⟨_, rfl⟩
  obtain ⟨Inn, hInn⟩ : ∃ Inn : Subgroup (MulAut (↥K ⧸ center ↥K)),
      Inn = (MulAut.conj : (↥K ⧸ center ↥K) →* MulAut (↥K ⧸ center ↥K)).range := ⟨_, rfl⟩
  have hInnX : Inn ≤ X₁ := by
    rw [hInn, hX₁]
    rintro _ ⟨s, rfl⟩
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨(k₀ : Y), Subgroup.mem_sup_left k₀.2, actQuot_coe K k₀⟩
  have hInnN : Inn.Normal := by
    rw [hInn]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨s, rfl⟩ := hn
    exact ⟨g s, (mul_conj_mul_inv g s).symm ▸ rfl⟩
  have hNn : (Inn.subgroupOf X₁).Normal := Subgroup.normal_subgroupOf
  have hiso : Nonempty (↥(Inn.subgroupOf X₁) ≃* (↥K ⧸ center ↥K)) := by
    refine ⟨(Subgroup.subgroupOfEquivOfLe hInnX).trans ?_⟩
    rw [hInn]
    exact (MonoidHom.ofInjective (conj_injective_of_center_bot hSZ)).symm
  have hcent : centralizer ((Inn.subgroupOf X₁ : Subgroup ↥X₁) : Set ↥X₁) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    refine MulEquiv.ext fun s => ?_
    have hconj : ∀ s : ↥K ⧸ center ↥K, MulAut.conj s ∈ Inn := fun s => by
      rw [hInn]; exact ⟨s, rfl⟩
    have hmem : ∀ s : ↥K ⧸ center ↥K,
        (⟨MulAut.conj s, hInnX (hconj s)⟩ : ↥X₁) ∈ Inn.subgroupOf X₁ := fun s => hconj s
    have h1 := Subgroup.mem_centralizer_iff.mp hφ _ (hmem s)
    have h2 : (MulAut.conj s) * (φ : MulAut (↥K ⧸ center ↥K)) =
        (φ : MulAut (↥K ⧸ center ↥K)) * MulAut.conj s := congrArg Subtype.val h1
    have h3 : MulAut.conj ((φ : MulAut (↥K ⧸ center ↥K)) s) = MulAut.conj s := by
      rw [← mul_conj_mul_inv, ← h2, mul_assoc, mul_inv_cancel, mul_one]
    have h4 := conj_injective_of_center_bot hSZ h3
    simpa using h4
  have hX₁mem : ∀ φ : MulAut (↥K ⧸ center ↥K), φ ∈ X₁ → φ ∈ (K ⊔ C).map (actQuot K) :=
    fun φ h => hX₁ ▸ h
  have hvX : actQuot K v ∈ X₁ := by
    rw [hX₁]; exact ⟨v, Subgroup.mem_sup_right (by rw [hC]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl), rfl⟩
  have hρv2 : orderOf (actQuot K v) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hv, pow_orderOf_eq_one, map_one]
    · exact hρ
  obtain ⟨e, he⟩ : ∃ e : ↥X₁, e = ⟨actQuot K v, hvX⟩ := ⟨_, rfl⟩
  have he2 : orderOf e = 2 := by
    rw [← Subgroup.orderOf_coe, he]; exact hρv2
  have hbot := hLB ↥X₁ (Inn.subgroupOf X₁) hNn hiso hcent e he2
  have hbot' : involutionOddCore e = ⊥ := (involutionOddCore_eq_bot_iff' e).mpr hbot
  have hRX : R.map (actQuot K) ≤ X₁ := by
    rw [hX₁]; exact Subgroup.map_mono (le_sup_of_le_right hRC)
  obtain ⟨W, hW⟩ : ∃ W : Subgroup ↥X₁, W = (R.map (actQuot K)).subgroupOf X₁ := ⟨_, rfl⟩
  have hWC : W ≤ centralizer ({e} : Set ↥X₁) := by
    intro w hw
    rw [hW, Subgroup.mem_subgroupOf] at hw
    obtain ⟨r, hr, hrw⟩ := hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    have hrC : (r : Y) * v = v * r := Subgroup.mem_centralizer_singleton_iff.mp (by rw [← hC]; exact hRC hr)
    rw [he]
    show (w : MulAut (↥K ⧸ center ↥K)) * actQuot K v = actQuot K v * (w : MulAut (↥K ⧸ center ↥K))
    rw [← hrw, ← map_mul, ← map_mul, hrC]
  have hWn : ∀ c ∈ centralizer ({e} : Set ↥X₁), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    rw [hW, Subgroup.mem_subgroupOf] at hw
    obtain ⟨r, hr, hrw⟩ := hw
    have hcX := hX₁mem _ c.2
    obtain ⟨y, hy, hyc⟩ := hcX
    obtain ⟨k₀, hk₀, c₀, hc₀, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    have hc₀v : c₀ * v = v * c₀ := by
      rw [hC] at hc₀; exact Subgroup.mem_centralizer_singleton_iff.mp hc₀
    have hcom : (c : MulAut (↥K ⧸ center ↥K)) * actQuot K v =
        actQuot K v * (c : MulAut (↥K ⧸ center ↥K)) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      have h2 := congrArg Subtype.val this
      rw [he] at h2
      exact h2
    rw [← hyc, map_mul] at hcom
    have hcv' : actQuot K c₀ * actQuot K v = actQuot K v * actQuot K c₀ := by
      rw [← map_mul, ← map_mul, hc₀v]
    have hkv : actQuot K k₀ * actQuot K v = actQuot K v * actQuot K k₀ := by
      have h3 : actQuot K k₀ * (actQuot K c₀ * actQuot K v) =
          actQuot K v * actQuot K k₀ * actQuot K c₀ := by
        rw [← mul_assoc, hcom, mul_assoc]
      rw [hcv', ← mul_assoc] at h3
      exact mul_right_cancel h3
    have hzK : k₀ * v * k₀⁻¹ * v⁻¹ ∈ K := by
      have h1 : k₀ * (v * k₀⁻¹ * v⁻¹) ∈ K :=
        K.mul_mem hk₀ ((inferInstance : K.Normal).conj_mem k₀⁻¹ (K.inv_mem hk₀) v)
      simpa [mul_assoc] using h1
    have hρz : actQuot K (k₀ * v * k₀⁻¹ * v⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hkv]
      group
    have hzcenter : k₀ * v * k₀⁻¹ * v⁻¹ ∈ (center ↥K).map K.subtype := by
      have h1 : actQuot K ((⟨_, hzK⟩ : ↥K) : Y) = 1 := hρz
      rw [actQuot_coe] at h1
      have h2 : (QuotientGroup.mk (⟨_, hzK⟩ : ↥K) : ↥K ⧸ center ↥K) = 1 :=
        conj_injective_of_center_bot hSZ (by rw [h1, map_one])
      exact ⟨⟨_, hzK⟩, QuotientGroup.eq_one_iff _ |>.mp h2, rfl⟩
    have hzY := hZY _ hzcenter
    have hg : k₀ * v * k₀⁻¹ = (k₀ * v * k₀⁻¹ * v⁻¹) * v := by group
    have hkR : ∀ r ∈ R, k₀ * r * k₀⁻¹ ∈ R := by
      intro r hr'
      rw [hR] at hr' ⊢
      exact conj_mem_involutionOddCore_of_central hzY hg hr'
    have hrR : (k₀ * c₀) * r * (k₀ * c₀)⁻¹ ∈ R := by
      have h1 : c₀ * r * c₀⁻¹ ∈ R := hRn c₀ hc₀ r hr
      have h2 := hkR _ h1
      simpa [mul_assoc] using h2
    rw [hW, Subgroup.mem_subgroupOf]
    refine ⟨(k₀ * c₀) * r * (k₀ * c₀)⁻¹, hrR, ?_⟩
    calc actQuot K ((k₀ * c₀) * r * (k₀ * c₀)⁻¹)
        = actQuot K (k₀ * c₀) * actQuot K r * (actQuot K (k₀ * c₀))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = (c : MulAut (↥K ⧸ center ↥K)) * (w : MulAut (↥K ⧸ center ↥K)) *
          (c : MulAut (↥K ⧸ center ↥K))⁻¹ := by rw [hyc, hrw]
      _ = ((c * w * c⁻¹ : ↥X₁) : MulAut (↥K ⧸ center ↥K)) := rfl
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W = Nat.card (R.map (actQuot K)) := by
      rw [hW]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
    rw [h1]
    exact Odd.of_dvd_nat hRodd (Subgroup.card_map_dvd R (actQuot K))
  have hWle : W ≤ involutionOddCore e := le_involutionOddCore_of_normalized hWC hWn hWodd
  rw [hbot'] at hWle
  intro r hr0
  have hr : r ∈ R := hR ▸ hr0
  have hmem : (⟨actQuot K r, hRX ⟨r, hr, rfl⟩⟩ : ↥X₁) ∈ W := by
    rw [hW, Subgroup.mem_subgroupOf]; exact ⟨r, hr, rfl⟩
  have := Subgroup.mem_bot.mp (hWle hmem)
  exact congrArg Subtype.val this

end Step


section Main

variable {Y : Type} [Group Y] [Finite Y]

theorem involutionOddCore_le_centralizer_pCore {v : Y} (hv : orderOf v = 2) :
    involutionOddCore v ≤ centralizer (pCore 2 Y : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ : ∃ R : Subgroup Y, R = involutionOddCore v := ⟨_, rfl⟩
  rw [← hR]
  have hRC : R ≤ centralizer ({v} : Set Y) := hR ▸ involutionOddCore_le_centralizer v
  have hRn : ∀ c ∈ centralizer ({v} : Set Y), ∀ r ∈ R, c * r * c⁻¹ ∈ R :=
    fun c hc r hr => hR ▸ conj_mem_involutionOddCore' hc (hR ▸ hr)
  have hRodd : Odd (Nat.card R) := hR ▸ odd_card_involutionOddCore v
  have hPnormal : (pCore 2 Y).Normal := pCore_normal
  have hP2 : IsPGroup 2 (pCore 2 Y) := pCore_isPGroup
  have hB : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv]; norm_num)
  have hcz : centralizer ((zpowers v : Subgroup Y) : Set Y) = centralizer ({v} : Set Y) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hRP : Disjoint R (pCore 2 Y) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr hRodd).symm.pow_right n
  have key := CFSG.Goldschmidt.N10 Y (pCore 2 Y) R (zpowers v) hP2
    (Nat.coprime_two_left.mpr hRodd).symm hB
    (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hPnormal]; exact Subgroup.mem_top x)
    (fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hPnormal]; exact Subgroup.mem_top x)
    (by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      rw [hcz]; exact hRC)
    (by
      rintro x ⟨hxP, hxC⟩
      rw [hcz] at hxC
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 : x * r⁻¹ * x⁻¹ ∈ R := by
        have := hRn x hxC r⁻¹ (R.inv_mem hr)
        exact this
      have h2 : r * (x * r⁻¹ * x⁻¹) ∈ R := R.mul_mem hr h1
      have h3 : r * (x * r⁻¹ * x⁻¹) ∈ pCore 2 Y := by
        have : r * (x * r⁻¹ * x⁻¹) = (r * x * r⁻¹) * x⁻¹ := by group
        rw [this]
        exact (pCore 2 Y).mul_mem (hPnormal.conj_mem x hxP r) ((pCore 2 Y).inv_mem hxP)
      have h4 := Subgroup.disjoint_def.mp hRP h2 h3
      have : r * x = x * r := by
        have h5 : r * (x * r⁻¹ * x⁻¹) = 1 := h4
        calc r * x = (r * (x * r⁻¹ * x⁻¹)) * x * r := by group
          _ = x * r := by rw [h5]; group
      exact this)
  exact fun r hr => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (key hx) r hr).symm

end Main

section Final

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_of_ne_one_of_card_le_two {A : Type*} [Group A] [Finite A] (h : Nat.card A ≤ 2)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have := Fintype.ofFinite A
  have h3 : ({1, a, b} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp [ha.symm, hb.symm]
  have h4 := Finset.card_le_univ ({1, a, b} : Finset A)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem center_component_central {K : Subgroup Y} [K.Normal] (hcard : Nat.card (center ↥K) ≤ 2) :
    ∀ z ∈ (center ↥K).map K.subtype, ∀ y : Y, y * z = z * y := by
  rintro _ ⟨z₀, hz₀, rfl⟩ y
  by_cases h1 : z₀ = 1
  · subst h1
    simp
  · have hc : y * (z₀ : Y) * y⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem _ z₀.2 y
    have hcen : (⟨_, hc⟩ : ↥K) ∈ center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      have hk : y⁻¹ * (k : Y) * y ∈ K := (inferInstance : K.Normal).conj_mem' _ k.2 y
      have hz := Subgroup.mem_center_iff.mp hz₀ ⟨_, hk⟩
      have hz' : (y⁻¹ * (k : Y) * y) * (z₀ : Y) = (z₀ : Y) * (y⁻¹ * (k : Y) * y) :=
        congrArg Subtype.val hz
      show (k : Y) * (y * z₀ * y⁻¹) = y * z₀ * y⁻¹ * k
      calc (k : Y) * (y * z₀ * y⁻¹) = y * ((y⁻¹ * k * y) * z₀) * y⁻¹ := by group
        _ = y * (z₀ * (y⁻¹ * k * y)) * y⁻¹ := by rw [hz']
        _ = y * z₀ * y⁻¹ * k := by group
    have hne : (⟨_, hc⟩ : ↥K) ≠ 1 := by
      intro h
      apply h1
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      have h2 : (z₀ : Y) = 1 := by
        have : y * (z₀ : Y) * y⁻¹ = 1 := this
        simpa using this
      exact Subtype.ext h2
    have heq := eq_of_ne_one_of_card_le_two hcard (a := ⟨_, hcen⟩) (b := ⟨z₀, hz₀⟩)
      (by intro h; exact hne (congrArg Subtype.val h)) (by intro h; exact h1 (congrArg Subtype.val h))
    have := congrArg (fun w : center ↥K => (w : ↥K).val) heq
    simp only at this
    calc y * (z₀ : Y) = (y * z₀ * y⁻¹) * y := by group
      _ = z₀ * y := by rw [this]

end Final

section Components

variable {Y : Type} [Group Y] [Finite Y]

theorem component_centralized (K : Subgroup Y) [K.Normal] (hq : IsQuasisimple ↥K)
    (hZ2 : IsPGroup 2 ↥(center ↥K))
    (hZY : ∀ z ∈ (center ↥K).map K.subtype, ∀ y : Y, y * z = z * y)
    (hLB : LocBal2 (fun S _ => Nonempty (S ≃* (↥K ⧸ center ↥K)))) {v : Y} (hv : orderOf v = 2) :
    ∀ r ∈ involutionOddCore v, ∀ k ∈ K, r * k = k * r := by
  by_cases hρ : actQuot K v = 1
  · exact component_centralized_of_actQuot_eq_one K hq hZ2 hρ
  · intro r hr k hk
    exact mul_comm_of_actQuot_eq_one K hq.1 (actQuot_eq_one_of_locBal K hq hZY hLB hv hρ r hr) k hk

omit [Finite Y] in
theorem eq_one_of_pow_two_pow {y : Y} (hodd : Odd (orderOf y)) {n : ℕ} (h : y ^ (2 ^ n) = 1) :
    y = 1 := by
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hne
    have : 2 ∣ orderOf y := hj ▸ dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
  rw [hj0] at hj
  exact orderOf_eq_one_iff.mp hj

theorem involutionOddCore_eq_bot_of_components (hO : pPrimeCore 2 Y = ⊥)
    (hcomp : ∀ K₁ K₂ : Subgroup Y, IsComponent K₁ → IsComponent K₂ → K₁ = K₂)
    (hK : ∀ K : Subgroup Y, IsComponent K → IsPGroup 2 ↥(center ↥K) ∧
      Nat.card (center ↥K) ≤ 2 ∧
        LocBal2 (fun S _ => Nonempty (S ≃* (↥K ⧸ center ↥K)))) :
    ∀ v : Y, orderOf v = 2 → involutionOddCore v = ⊥ := by
  intro v hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRQ := involutionOddCore_le_centralizer_pCore hv
  have hRodd := odd_card_involutionOddCore v
  have hPn : (pCore 2 Y).Normal := pCore_normal
  have hfit : fittingSubgroup Y = pCore 2 Y := Fitting_eq_pcore Y 2 hO
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hrodd : Odd (orderOf r) := by
    have hdvd : orderOf (⟨r, hr⟩ : involutionOddCore v) ∣ Nat.card (involutionOddCore v) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hdvd
    exact Odd.of_dvd_nat hRodd hdvd
  have hrP : ∀ x ∈ pCore 2 Y, x * r = r * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hRQ hr) x hx
  by_cases hex : ∃ K : Subgroup Y, IsComponent K
  · obtain ⟨K₀, hK₀⟩ := hex
    have hlayer : layer Y = K₀ := by
      have : {K : Subgroup Y | IsComponent K} = {K₀} :=
        Set.ext fun K => ⟨fun h => hcomp K K₀ h hK₀, fun h => h ▸ hK₀⟩
      simp only [CFSG.layer.eq_sSup]
      rw [this, sSup_singleton]
    have hKn : K₀.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h1 : IsComponent (K₀.map (MulAut.conj g).toMonoidHom) :=
        CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK₀
      have h2 := hcomp _ _ h1 hK₀
      have : g * n * g⁻¹ ∈ K₀.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
      rwa [h2] at this
    obtain ⟨hZ2, hZc, hLB⟩ := hK K₀ hK₀
    have hZY := center_component_central (K := K₀) hZc
    have hRK := component_centralized K₀ hK₀.1 hZ2 hZY hLB hv
    have hFr : generalizedFitting Y ≤ centralizer ({r} : Set Y) := by
      rw [generalizedFitting, hfit, hlayer]
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hrP x hx)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hRK r hr x hx).symm
    have hrC : r ∈ centralizer (generalizedFitting Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hFr hx)
    have hrF := centralizer_generalizedFitting_le Y hrC
    rw [generalizedFitting, hfit, hlayer] at hrF
    obtain ⟨q, hq, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hrF
    have hfl : ∀ x ∈ K₀, ∀ y ∈ pCore 2 Y, y * x = x * y := by
      intro x hx y hy
      have h1 := CFSG.LocalCores.fitting_layer_commute (G := Y)
      have h2 : fittingSubgroup Y ≤ centralizer (layer Y : Set Y) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
      rw [hfit, hlayer] at h2
      exact (Subgroup.mem_centralizer_iff.mp (h2 hy) x hx).symm
    have hkcenter : (⟨k, hk⟩ : ↥K₀) ∈ center ↥K₀ := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      have h1 : q * k * (x : Y) = (x : Y) * (q * k) := hRK _ hr x x.2
      have h2 : (x : Y) * q = q * x := (hfl x x.2 q hq).symm
      show (x : Y) * k = k * x
      have h3 : q * (k * x) = q * (x * k) := by
        calc q * (k * x) = q * k * x := by group
          _ = x * (q * k) := h1
          _ = (x * q) * k := by group
          _ = (q * x) * k := by rw [h2]
          _ = q * (x * k) := by group
      exact (mul_left_cancel h3).symm
    obtain ⟨a, ha⟩ := hZ2 ⟨⟨k, hk⟩, hkcenter⟩
    obtain ⟨b, hb⟩ := (pCore_isPGroup (p := 2) (G := Y)) ⟨q, hq⟩
    have ha' : k ^ (2 ^ a) = 1 := by
      have := congrArg (fun w : ↥(center ↥K₀) => ((w : ↥K₀) : Y)) ha
      simpa using this
    have hb' : q ^ (2 ^ b) = 1 := by
      have := congrArg (fun w : ↥(pCore 2 Y) => (w : Y)) hb
      simpa using this
    have hcomm : Commute q k := hfl k hk q hq
    have hq1 : q ^ (2 ^ (a + b)) = 1 := by
      rw [pow_add, mul_comm (2 ^ a) (2 ^ b), pow_mul, hb', one_pow]
    have hk1 : k ^ (2 ^ (a + b)) = 1 := by rw [pow_add, pow_mul, ha', one_pow]
    have hfin : (q * k) ^ (2 ^ (a + b)) = 1 := by rw [hcomm.mul_pow, hq1, hk1, mul_one]
    exact eq_one_of_pow_two_pow hrodd hfin
  · have hlayer : layer Y = ⊥ := by
      have : {K : Subgroup Y | IsComponent K} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun K hK => hex ⟨K, hK⟩
      simp only [CFSG.layer.eq_sSup]
      rw [this, sSup_empty]
    have hFr : generalizedFitting Y ≤ centralizer ({r} : Set Y) := by
      rw [generalizedFitting, hfit, hlayer, sup_bot_eq]
      exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hrP x hx)
    have hrC : r ∈ centralizer (generalizedFitting Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mp (hFr hx)
    have hrF := centralizer_generalizedFitting_le Y hrC
    rw [generalizedFitting, hfit, hlayer, sup_bot_eq] at hrF
    obtain ⟨b, hb⟩ := (pCore_isPGroup (p := 2) (G := Y)) ⟨r, hrF⟩
    have hb' : r ^ (2 ^ b) = 1 := by
      have := congrArg (fun w : ↥(pCore 2 Y) => (w : Y)) hb
      simpa using this
    exact eq_one_of_pow_two_pow hrodd hb'

end Components


end CFSG.GH74.GLS.Prop27
