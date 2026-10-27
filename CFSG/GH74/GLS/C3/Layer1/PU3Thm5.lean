module

public import CFSG.GH74.GLS.C3.Layer1.PU3Cfg
public import CFSG.Milestones.CL_LIT_Aschbacher_component_type_theorem_5
public import CFSG.GH74.GLS.C3.Layer1.Th2Struct
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv

public section

namespace CFSG.GH74.GLS.PU3.Thm5

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_fixed_of_odd_card {α : Type*} (σ : Equiv.Perm α) {k : ℕ} (hσ : σ ^ 2 ^ k = 1)
    (hodd : Odd (Nat.card α)) : ∃ x, σ x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers σ) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨k, Subtype.ext ?_⟩
    change (σ ^ n) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ, one_zpow]
  have hnd : ¬ 2 ∣ Nat.card α := by
    rintro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  obtain ⟨x, hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card α hnd
  exact ⟨x, by simpa using (MulAction.mem_fixedPoints.1 hx) ⟨σ, Subgroup.mem_zpowers σ⟩⟩

theorem exists_mul_mem_centralizer {A O : Subgroup G} (hOA : O ≤ A)
    (hAO : ∀ x ∈ A, ∀ o ∈ O, x * o * x⁻¹ ∈ O) (hodd : Odd (Nat.card O)) {t : G} {k : ℕ}
    (ht : t ^ 2 ^ k = 1) (hy : ∀ a ∈ A, t⁻¹ * a⁻¹ * t * a ∈ O) {l : G} (hl : l ∈ A) :
    ∃ x ∈ A ⊓ centralizer ({t} : Set G), ∃ o ∈ O, l = x * o := by
  have hO : ∀ o ∈ O, t⁻¹ * o * t ∈ O := fun o ho => by
    have h1 := hy o⁻¹ (hOA (O.inv_mem ho))
    rw [inv_inv] at h1
    have h2 := O.mul_mem h1 ho
    rwa [show t⁻¹ * o * t * o⁻¹ * o = t⁻¹ * o * t by group] at h2
  have hc : l⁻¹ * t⁻¹ * l * t ∈ O := by
    have h1 := hy l⁻¹ (A.inv_mem hl)
    rw [inv_inv] at h1
    have h2 := hAO l⁻¹ (A.inv_mem hl) _ h1
    rwa [show l⁻¹ * (t⁻¹ * l * t * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * t⁻¹ * l * t by group] at h2
  let φ : O → O := fun o => ⟨l⁻¹ * t⁻¹ * (l * o) * t, by
    rw [show l⁻¹ * t⁻¹ * (l * (o : G)) * t = (l⁻¹ * t⁻¹ * l * t) * (t⁻¹ * o * t) by group]
    exact O.mul_mem hc (hO o o.2)⟩
  have hφinj : Function.Injective φ := by
    intro o o' h
    have h1 : l⁻¹ * t⁻¹ * (l * (o : G)) * t = l⁻¹ * t⁻¹ * (l * (o' : G)) * t :=
      congrArg Subtype.val h
    apply Subtype.ext
    have h2 : (o : G) * t = o' * t := by
      have := mul_left_cancel (a := l⁻¹ * t⁻¹ * l) (by
        calc l⁻¹ * t⁻¹ * l * ((o : G) * t) = l⁻¹ * t⁻¹ * (l * (o : G)) * t := by group
          _ = l⁻¹ * t⁻¹ * (l * (o' : G)) * t := h1
          _ = l⁻¹ * t⁻¹ * l * ((o' : G) * t) := by group)
      exact this
    exact mul_right_cancel h2
  have hφbij : Function.Bijective φ := Finite.injective_iff_bijective.1 hφinj
  let σ : Equiv.Perm O := Equiv.ofBijective φ hφbij
  have hσpow : ∀ (n : ℕ) (o : O), ((σ ^ n) o : G) = l⁻¹ * (t ^ n)⁻¹ * (l * o) * t ^ n := by
    intro n
    induction n with
    | zero => intro o; simp
    | succ n ih =>
      intro o
      rw [pow_succ', Equiv.Perm.mul_apply]
      have h1 : (σ ((σ ^ n) o) : G) = l⁻¹ * t⁻¹ * (l * ((σ ^ n) o : O)) * t := rfl
      rw [h1, ih o, pow_succ]
      group
  have hσ : σ ^ 2 ^ k = 1 := by
    ext o
    rw [hσpow, ht]
    simp
  obtain ⟨o₀, ho₀⟩ := exists_fixed_of_odd_card σ hσ hodd
  have h1 : l⁻¹ * t⁻¹ * (l * (o₀ : G)) * t = o₀ := congrArg Subtype.val ho₀
  have h2 : t⁻¹ * (l * (o₀ : G)) * t = l * o₀ := by
    have := congrArg (fun z => l * z) h1
    simpa [mul_assoc] using this
  refine ⟨l * o₀, ⟨A.mul_mem hl (hOA o₀.2), ?_⟩, (o₀⁻¹ : O), (o₀⁻¹ : O).2, ?_⟩
  · show l * (o₀ : G) ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc l * (o₀ : G) * t = t * (t⁻¹ * (l * o₀) * t) := by group
      _ = t * (l * o₀) := by rw [h2]
  · simp

theorem isSylowOf_sup_of_le_normalizer {P K N : Subgroup G} (hP : IsSylowOf 2 P K)
    (hKN : K ≤ normalizer (N : Set G)) (hN : Odd (Nat.card N)) : IsSylowOf 2 P (K ⊔ N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hP2, hdvd⟩ := hP
  refine ⟨hPK.trans le_sup_left, hP2, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P K (K ⊔ N) hPK le_sup_left]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
  · exact hdvd h
  · have hNH : N ≤ K ⊔ N := le_sup_right
    have hKH : K ≤ K ⊔ N := le_sup_left
    have hHN : K ⊔ N ≤ normalizer (N : Set G) := sup_le hKN Subgroup.le_normalizer
    have hnormal : (N.subgroupOf (K ⊔ N)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
    have h1 := relIndex_sup_eq_relIndex_of_normal (N.subgroupOf (K ⊔ N)) (K.subgroupOf (K ⊔ N))
    have h2' : N.subgroupOf (K ⊔ N) ⊔ K.subgroupOf (K ⊔ N) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNH hKH, sup_comm]
      exact Subgroup.subgroupOf_self _
    rw [h2', Subgroup.relIndex_top_right] at h1
    have h3 : K.relIndex (K ⊔ N) = (K.subgroupOf (K ⊔ N)).index := rfl
    rw [h3, h1] at h
    have h4 := Subgroup.relIndex_mul_card (K.subgroupOf (K ⊔ N)) (N.subgroupOf (K ⊔ N))
    have h5 : Nat.card (N.subgroupOf (K ⊔ N)) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
    rw [h5] at h4
    have h6 : 2 ∣ Nat.card N := h.trans (Dvd.intro _ h4)
    exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h6)

omit [Finite G] in
theorem exists_pow_orderOf_eq_two {s : G} {k : ℕ} (hk : s ^ 2 ^ k = 1) (hs : s ≠ 1) :
    ∃ n : ℕ, orderOf (s ^ n) = 2 := by
  obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hn
    exact hs hn
  refine ⟨2 ^ (n - 1), ?_⟩
  rw [orderOf_pow_of_dvd (pow_pos (by norm_num) _).ne'
    (by rw [hn]; exact pow_dvd_pow 2 (by omega)), hn, Nat.pow_div (by omega) (by norm_num),
    show n - (n - 1) = 1 by omega, pow_one]

omit [Finite G] in
theorem commutator_pow_mem {M L : Subgroup G} {s : G} (hs : s ∈ M)
    (h : ∀ l ∈ L, ⁅l, s⁆ ∈ pPrimeCoreOf 2 M) (n : ℕ) : ∀ l ∈ L, ⁅l, s ^ n⁆ ∈ pPrimeCoreOf 2 M := by
  induction n with
  | zero => intro l _; simp [one_mem]
  | succ n ih =>
    intro l hl
    have e : ⁅l, s ^ (n + 1)⁆ = ⁅l, s ^ n⁆ * (s ^ n * ⁅l, s⁆ * (s ^ n)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (pPrimeCoreOf 2 M).mul_mem (ih l hl)
      (TwoThin.pPrimeCoreOf_normalized M (pow_mem hs n) (h l hl))

theorem two_dvd_card_of_good {M L : Subgroup G} (h : Good M L) : 2 ∣ Nat.card ↥L := by
  have h1 : CFSG.pRank 2 ↥L = CFSG.Open.pRank 2 L :=
    (SectionRank.pRank_eq_open_pRank_top 2 ↥L).trans (SectionRank.pRank_eq_pRank_top_subgroup L).symm
  have h2 : 2 ≤ CFSG.Open.pRank 2 L := h1 ▸ h.rank
  obtain ⟨E, hEL, -, hcard⟩ := SectionRank.exists_pRank one_lt_two L
  have h3 : 2 ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  exact h3.trans (Subgroup.card_dvd_of_le hEL)

theorem sylow_ne_bot_of_good {M L P : Subgroup G} (h : Good M L) (hP : IsSylowOf 2 P L) : P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hbot
  have hcard := hP.card_eq
  rw [Subgroup.card_eq_one.2 hbot] at hcard
  have hpos : 0 < Nat.card ↥L := Nat.card_pos
  have hf : 1 ≤ (Nat.card ↥L).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos.ne').1 (two_dvd_card_of_good h)
  have h2lt : 1 < 2 ^ (Nat.card ↥L).factorization 2 := Nat.one_lt_two_pow (by omega)
  omega

omit [Finite G] in
theorem oddCore_eq (X : Type*) [Group X] :
    CFSG.Open.aschbacherThm5OddCore X = pPrimeCore 2 X := by
  unfold CFSG.Open.aschbacherThm5OddCore CFSG.pPrimeCore
  congr 1
  ext K
  exact and_congr_right fun _ => Nat.coprime_two_left.symm

omit [Finite G] in
theorem core_eq (D : Subgroup G) : CFSG.Open.aschbacherThm5Core D = pPrimeCoreOf 2 D := by
  unfold CFSG.Open.aschbacherThm5Core pPrimeCoreOf
  rw [oddCore_eq]

omit [Finite G] in
theorem mem_pPrimeCoreOf_iff {X : Subgroup G} (x : X) :
    (x : G) ∈ pPrimeCoreOf 2 X ↔ x ∈ pPrimeCore 2 ↥X :=
  Subgroup.mem_map_iff_mem X.subtype_injective

omit [Finite G] in
theorem le_pPrimeCoreOf_of_normalized {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ≤ pPrimeCoreOf 2 X := by
  have hnormal : (N.subgroupOf X).Normal := ⟨fun a ha h => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hnorm (h : G) h.2 (a : G) ha⟩
  have hcop' : Nat.Coprime 2 (Nat.card ↥(N.subgroupOf X)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    exact Nat.coprime_two_left.2 hodd
  have hle : N.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

theorem inf_core_le {L D : Subgroup G} (hLD : L ≤ D) :
    L ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 L := by
  refine le_pPrimeCoreOf_of_normalized inf_le_left (fun x hx n hn => ?_)
    ((TwoThin.card_pPrimeCoreOf_odd D).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right))
  exact ⟨L.mul_mem (L.mul_mem hx hn.1) (L.inv_mem hx),
    TwoThin.pPrimeCoreOf_normalized D (hLD hx) hn.2⟩

theorem core_le_core {L D : Subgroup G} (hLD : L ≤ D)
    (hDL : D ≤ normalizer (pPrimeCoreOf 2 L : Set G)) :
    pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 D := by
  refine le_pPrimeCoreOf_of_normalized ((TwoThin.pPrimeCoreOf_le L).trans hLD)
    (fun x hx n hn => ?_) (TwoThin.card_pPrimeCoreOf_odd L)
  exact (Subgroup.mem_normalizer_iff.1 (hDL hx) n).1 hn

@[expose] def bar (D L : Subgroup G) : Subgroup (D ⧸ CFSG.Open.aschbacherThm5OddCore D) :=
  (L.subgroupOf D).map (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D))

omit [Finite G] in
theorem preimage_bar {D L : Subgroup G} (hLD : L ≤ D) :
    CFSG.Open.aschbacherThm5Preimage D (bar D L) = L ⊔ pPrimeCoreOf 2 D := by
  unfold CFSG.Open.aschbacherThm5Preimage bar
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hLD, ← core_eq]
  rfl

omit [Finite G] in
theorem nonempty_kBar_mulEquiv_bar {D L : Subgroup G} (hLD : L ≤ D)
    (h1 : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 D) (h2 : L ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 L) :
    Nonempty (kBar L ≃* bar D L) := by
  let φ : L →* D ⧸ CFSG.Open.aschbacherThm5OddCore D :=
    (QuotientGroup.mk' (CFSG.Open.aschbacherThm5OddCore D)).comp (Subgroup.inclusion hLD)
  have hker : φ.ker = pPrimeCore 2 L := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, oddCore_eq]
    have e1 : Subgroup.inclusion hLD m ∈ pPrimeCore 2 ↥D ↔ (m : G) ∈ pPrimeCoreOf 2 D :=
      (mem_pPrimeCoreOf_iff (Subgroup.inclusion hLD m)).symm
    rw [e1, ← mem_pPrimeCoreOf_iff m]
    constructor
    · intro hm
      exact h2 (Subgroup.mem_inf.mpr ⟨m.2, hm⟩)
    · intro hm
      exact h1 hm
  have hrange : φ.range = bar D L := by
    unfold bar
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem isQuasisimple_of_simple {X : Type*} [Group X] [IsSimpleGroup X]
    (hX : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨a, b, hab⟩ := hX
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (by rw [h]; exact mem_top b) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator X := by
        rw [_root_.commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite G] in
theorem bar_commute {D L L' : Subgroup G}
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b * a⁻¹ * b⁻¹ ∈ pPrimeCoreOf 2 D) :
    ∀ x ∈ bar D L, ∀ y ∈ bar D L', x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h1 : (a * b * a⁻¹ * b⁻¹ : D) ∈ CFSG.Open.aschbacherThm5OddCore D := by
    rw [oddCore_eq, ← mem_pPrimeCoreOf_iff]
    exact hc a ha b hb
  have h3 := (QuotientGroup.eq_one_iff _).mpr h1
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at h3
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  calc (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D) * b =
      (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D) * b * (a : D ⧸ CFSG.Open.aschbacherThm5OddCore D)⁻¹ *
        (b : D ⧸ CFSG.Open.aschbacherThm5OddCore D)⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

omit [Finite G] in
theorem bar_sup_eq_top {D L L' : Subgroup G} (h : D = L ⊔ L') : bar D L ⊔ bar D L' = ⊤ := by
  subst h
  have hsupD : L.subgroupOf (L ⊔ L') ⊔ L'.subgroupOf (L ⊔ L') = ⊤ := by
    apply Subgroup.map_injective (L ⊔ L').subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  unfold bar
  rw [← Subgroup.map_sup, hsupD, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

section CfgLemmas

variable {M L₁ L₂ : Subgroup G}

theorem conj_cases (h : Cfg M L₁ L₂) {m : G} (hm : m ∈ M) :
    (cj m L₁ = L₁ ∧ cj m L₂ = L₂) ∨ (cj m L₁ = L₂ ∧ cj m L₂ = L₁) := by
  have hcomp : ∀ L, IsPCompIn 2 M L → cj m L = L₁ ∨ cj m L = L₂ := fun L hL => by
    have := Stage1.Thm2.Recip.isPCompIn_map_conj hL m
    rw [C3.Layer1.Thm1.map_conj_eq_self_of_mem hm] at this
    exact h.only _ this
  have hinj : ∀ A B : Subgroup G, cj m A = cj m B → A = B := fun A B hAB =>
    Subgroup.map_injective (MulAut.conj m).injective hAB
  rcases hcomp L₁ h.good₁.comp with h1 | h1 <;> rcases hcomp L₂ h.good₂.comp with h2 | h2
  · exact absurd (hinj _ _ (h1.trans h2.symm)) h.ne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj _ _ (h1.trans h2.symm)) h.ne

omit [Finite G] in
theorem sup_le_M (h : Cfg M L₁ L₂) : L₁ ⊔ L₂ ≤ M := sup_le h.good₁.comp.1 h.good₂.comp.1

theorem le_normalizer_sup (h : Cfg M L₁ L₂) : M ≤ normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) := by
  intro m hm
  apply mem_normalizer_of_cj_eq
  have e : cj m (L₁ ⊔ L₂) = cj m L₁ ⊔ cj m L₂ := Subgroup.map_sup _ _ _
  rw [e]
  rcases conj_cases h hm with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, sup_comm]

theorem comm_mem (h : Cfg M L₁ L₂) {a b : G} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    ⁅a, b⁆ ∈ pPrimeCoreOf 2 L₁ ∧ ⁅a, b⁆ ∈ pPrimeCoreOf 2 L₂ := by
  have h12 : L₁ ≤ Stage1.Thm2.Recip.cSec L₂ :=
    Stage1.Thm2.Recip.le_cSec_of_ne h.good₁.comp h.good₂.comp h.ne
  have h21 : L₂ ≤ Stage1.Thm2.Recip.cSec L₁ :=
    Stage1.Thm2.Recip.le_cSec_of_ne h.good₂.comp h.good₁.comp h.ne.symm
  refine ⟨(h21 hb).2.2 a ha, ?_⟩
  have := (h12 ha).2.2 b hb
  rw [← commutatorElement_inv]
  exact (pPrimeCoreOf 2 L₂).inv_mem this

theorem le_normalizer_core₂ (h : Cfg M L₁ L₂) : L₂ ≤ normalizer (pPrimeCoreOf 2 L₁ : Set G) :=
  fun _ hb => (Stage1.Thm2.Recip.le_cSec_of_ne h.good₂.comp h.good₁.comp h.ne.symm hb).2.1

theorem sup_le_normalizer_core₁ (h : Cfg M L₁ L₂) :
    L₁ ⊔ L₂ ≤ normalizer (pPrimeCoreOf 2 L₁ : Set G) :=
  sup_le (fun _ hx => TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hx))
    (le_normalizer_core₂ h)

theorem sup_le_normalizer_core₂ (h : Cfg M L₁ L₂) :
    L₁ ⊔ L₂ ≤ normalizer (pPrimeCoreOf 2 L₂ : Set G) := by
  have := sup_le_normalizer_core₁ h.symm
  rwa [sup_comm] at this

theorem core_sup_le_core (h : Cfg M L₁ L₂) : pPrimeCoreOf 2 (L₁ ⊔ L₂) ≤ pPrimeCoreOf 2 M :=
  le_pPrimeCoreOf_of_normalized ((TwoThin.pPrimeCoreOf_le _).trans (sup_le_M h))
    (fun _ hx n hn => (Subgroup.mem_normalizer_iff.1
      (TwoThin.mem_normalizer_pPrimeCoreOf (le_normalizer_sup h hx)) n).1 hn)
    (TwoThin.card_pPrimeCoreOf_odd _)

theorem normalizer_sup_eq (hG : IsSimpleGroup G) (h : Cfg M L₁ L₂) :
    normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) = M := by
  refine le_antisymm ?_ (le_normalizer_sup h)
  by_contra hne
  have hlt : M < normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) :=
    lt_of_le_of_ne (le_normalizer_sup h) (fun e => hne (e ▸ le_rfl))
  have htop : normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G) = ⊤ := h.maximal.2 _ hlt
  have hDn : (L₁ ⊔ L₂).Normal := normalizer_eq_top_iff.1 htop
  have hL₁ : L₁ ≠ ⊥ := fun hb => by
    have := two_dvd_card_of_good h.good₁
    rw [hb, Subgroup.card_bot] at this
    omega
  rcases hDn.eq_bot_or_eq_top with h1 | h1
  · exact hL₁ (eq_bot_iff.2 (h1 ▸ le_sup_left))
  · exact h.maximal.1 (eq_top_iff.2 (h1 ▸ sup_le_M h))

end CfgLemmas

section Core

variable {M D Li Lj : Subgroup G}

theorem mem_M_of_centralizes (hDM : D ≤ M) (hLj : Lj ≤ D) (gj : Good M Lj) {s : G}
    (hs : ∀ a ∈ Lj ⊔ pPrimeCoreOf 2 D, s⁻¹ * a⁻¹ * s * a ∈ pPrimeCoreOf 2 D) : s ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOD : pPrimeCoreOf 2 D ≤ D := TwoThin.pPrimeCoreOf_le D
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 Lj
  have hNP : normalizer (P : Set G) ≤ M :=
    gj.normalizer_le P hP.le hP.isPGroup (sylow_ne_bot_of_good gj hP)
  have hLjN : Lj ≤ normalizer (pPrimeCoreOf 2 D : Set G) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => TwoThin.pPrimeCoreOf_normalized D (hLj hx) hn
    · intro hn
      have := TwoThin.pPrimeCoreOf_normalized D (D.inv_mem (hLj hx)) hn
      simpa [mul_assoc] using this
  have hPA : IsSylowOf 2 P (Lj ⊔ pPrimeCoreOf 2 D) :=
    isSylowOf_sup_of_le_normalizer hP hLjN (TwoThin.card_pPrimeCoreOf_odd D)
  have hAD : Lj ⊔ pPrimeCoreOf 2 D ≤ D := sup_le hLj hOD
  have hQA : cj s⁻¹ P ≤ Lj ⊔ pPrimeCoreOf 2 D := by
    intro x hx
    rw [mem_cj_iff, inv_inv] at hx
    have hpLj : s * x * s⁻¹ ∈ Lj := hP.le hx
    have hu := hs _ (Subgroup.mem_sup_left hpLj)
    have e : x = (s * x * s⁻¹) * (s⁻¹ * (s * x * s⁻¹)⁻¹ * s * (s * x * s⁻¹))⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hpLj)
      (Subgroup.mem_sup_right ((pPrimeCoreOf 2 D).inv_mem hu))
  have hQ2 : IsPGroup 2 ↥(cj s⁻¹ P) := hP.isPGroup.map (MulAut.conj s⁻¹).toMonoidHom
  obtain ⟨a, ha, haQ⟩ := Th2.exists_cj_le_of_isSylowOf hPA hQA hQ2
  have hcard : Nat.card ↥(cj (a * s⁻¹) P) = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj (a * s⁻¹)).injective
  have hle : cj (a * s⁻¹) P ≤ P := by
    have e : cj (a * s⁻¹) P = cj a (cj s⁻¹ P) := (Stage1.Thm3.Sec4.cmap_cmap a s⁻¹ P).symm
    rw [e]
    exact haQ
  have heq : cj (a * s⁻¹) P = P := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hmem : a * s⁻¹ ∈ M := hNP (mem_normalizer_of_cj_eq heq)
  have haM : a ∈ M := hDM (hAD ha)
  have h1 : s⁻¹ ∈ M := by
    have := M.mul_mem (M.inv_mem haM) hmem
    simpa using this
  simpa using M.inv_mem h1

omit [Finite G] in
theorem centralizer_le_of_centralizes (hOM : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 M) (gj : Good M Lj)
    {s : G} (hsM : s ∈ M) (hs1 : s ≠ 1) {k : ℕ} (hk : s ^ 2 ^ k = 1)
    (hs : ∀ a ∈ Lj ⊔ pPrimeCoreOf 2 D, s⁻¹ * a⁻¹ * s * a ∈ pPrimeCoreOf 2 D) :
    centralizer ({s} : Set G) ≤ M := by
  obtain ⟨n, hn⟩ := exists_pow_orderOf_eq_two hk hs1
  have hcomm : ∀ l ∈ Lj, ⁅l, s⁆ ∈ pPrimeCoreOf 2 M := by
    intro l hl
    have h1 := hs l⁻¹ (Subgroup.mem_sup_left (Lj.inv_mem hl))
    rw [inv_inv] at h1
    have e : ⁅l, s⁆ = s * (s⁻¹ * l * s * l⁻¹) * s⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact TwoThin.pPrimeCoreOf_normalized M hsM (hOM h1)
  have hC := gj.centralizer_le (s ^ n) (pow_mem hsM n) hn (commutator_pow_mem hsM hcomm n)
  intro x hx
  apply hC
  rw [mem_centralizer_singleton_iff]
  exact (Commute.pow_right (show Commute x s from mem_centralizer_singleton_iff.1 hx) n).eq

theorem mem_of_centralizes (hDM : D ≤ M) (hLi : Li ≤ D) (hLj : Lj ≤ D)
    (hOM : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 M) (gj : Good M Lj)
    (hcov : ∀ (g : G) (X : Subgroup G), X ≤ cj g⁻¹ M → Covers X Li (pPrimeCoreOf 2 M) → g ∈ M)
    {t g : G} (ht2 : ∃ k : ℕ, t ^ 2 ^ k = 1) (ht1 : t ≠ 1)
    (hti : ∀ a ∈ Li ⊔ pPrimeCoreOf 2 D, t⁻¹ * a⁻¹ * t * a ∈ pPrimeCoreOf 2 D)
    (htj : ∀ a ∈ Lj ⊔ pPrimeCoreOf 2 D,
      (g⁻¹ * t * g)⁻¹ * a⁻¹ * (g⁻¹ * t * g) * a ∈ pPrimeCoreOf 2 D) :
    g ∈ M := by
  obtain ⟨k, hk⟩ := ht2
  have hs_eq : g⁻¹ * t * g = MulAut.conj g⁻¹ t := by simp
  have hs1 : g⁻¹ * t * g ≠ 1 := by
    rw [hs_eq]
    exact fun e => ht1 ((MulAut.conj g⁻¹).injective (e.trans (map_one _).symm))
  have hsk : (g⁻¹ * t * g) ^ 2 ^ k = 1 := by
    rw [hs_eq, ← map_pow, hk, map_one]
  have hsM : g⁻¹ * t * g ∈ M := mem_M_of_centralizes hDM hLj gj htj
  have hCs := centralizer_le_of_centralizes hOM gj hsM hs1 hsk htj
  have hCt : centralizer ({t} : Set G) ≤ cj g M := by
    have e : cj g (centralizer ({g⁻¹ * t * g} : Set G)) = centralizer ({t} : Set G) := by
      rw [cj_centralizer_singleton, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    rw [← e]
    exact Subgroup.map_mono hCs
  have hAD : Li ⊔ pPrimeCoreOf 2 D ≤ D := sup_le hLi (TwoThin.pPrimeCoreOf_le D)
  have hcover : Covers ((Li ⊔ pPrimeCoreOf 2 D) ⊓ centralizer ({t} : Set G)) Li
      (pPrimeCoreOf 2 M) := fun a ha => by
    obtain ⟨x, hx, o, ho, e⟩ := exists_mul_mem_centralizer (A := Li ⊔ pPrimeCoreOf 2 D)
      (O := pPrimeCoreOf 2 D) le_sup_right
      (fun x hx o ho => TwoThin.pPrimeCoreOf_normalized D (hAD hx) ho)
      (TwoThin.card_pPrimeCoreOf_odd D) hk hti (Subgroup.mem_sup_left ha)
    exact ⟨x, hx, o, hOM ho, e⟩
  have hXg : (Li ⊔ pPrimeCoreOf 2 D) ⊓ centralizer ({t} : Set G) ≤ cj g⁻¹⁻¹ M := by
    rw [inv_inv]
    exact inf_le_right.trans hCt
  have := hcov g⁻¹ _ hXg hcover
  simpa using M.inv_mem this

end Core

end CFSG.GH74.GLS.PU3.Thm5

namespace CFSG.GH74.GLS.PU3

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.PU3.Thm5
open scoped commutatorElement

theorem cfg_false
    {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G) (hGn : ∃ a b : G, a * b ≠ b * a)
    {M L₁ L₂ : Subgroup G} (h : Cfg M L₁ L₂)
    (hcov₁ : ∀ (g : G) (X : Subgroup G), X ≤ cj g⁻¹ M → Covers X L₁ (pPrimeCoreOf 2 M) → g ∈ M)
    (hcov₂ : ∀ (g : G) (X : Subgroup G), X ≤ cj g⁻¹ M → Covers X L₂ (pPrimeCoreOf 2 M) → g ∈ M) :
    False := by
  have _ := hGn
  set D : Subgroup G := L₁ ⊔ L₂ with hD
  let Mi : Fin 2 → Subgroup G := ![L₁, L₂]
  have hMi : ∀ i, Mi i = L₁ ∨ Mi i = L₂ := fun i => by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hgood : ∀ i, Good M (Mi i) := fun i => by
    rcases hMi i with e | e <;> rw [e]
    exacts [h.good₁, h.good₂]
  have hMiD : ∀ i, Mi i ≤ D := fun i => by
    rcases hMi i with e | e <;> rw [e]
    exacts [le_sup_left, le_sup_right]
  have hcov : ∀ i : Fin 2, ∀ (g : G) (X : Subgroup G), X ≤ cj g⁻¹ M →
      Covers X (Mi i) (pPrimeCoreOf 2 M) → g ∈ M := fun i => by
    rcases hMi i with e | e <;> rw [e]
    exacts [hcov₁, hcov₂]
  have hDM : D ≤ M := sup_le_M h
  have hNM : normalizer (D : Set G) = M := normalizer_sup_eq hG h
  have hOM : pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 M := core_sup_le_core h
  have hnormO : ∀ i, D ≤ normalizer (pPrimeCoreOf 2 (Mi i) : Set G) := fun i => by
    rcases hMi i with e | e <;> rw [e]
    exacts [sup_le_normalizer_core₁ h, sup_le_normalizer_core₂ h]
  have hOD : ∀ i, pPrimeCoreOf 2 (Mi i) ≤ pPrimeCoreOf 2 D := fun i =>
    core_le_core (hMiD i) (hnormO i)
  have hDO : ∀ i, Mi i ⊓ pPrimeCoreOf 2 D ≤ pPrimeCoreOf 2 (Mi i) := fun i =>
    inf_core_le (hMiD i)
  let Abar : Fin 2 → Subgroup (D ⧸ CFSG.Open.aschbacherThm5OddCore D) := fun i => bar D (Mi i)
  have hpre : ∀ i, CFSG.Open.aschbacherThm5Preimage D (Abar i) = Mi i ⊔ pPrimeCoreOf 2 D :=
    fun i => preimage_bar (hMiD i)
  have hbar : ∀ i, IsSimpleGroup ↥(Abar i) ∧ ∃ a b : ↥(Abar i), a * b ≠ b * a := fun i => by
    obtain ⟨e⟩ := nonempty_kBar_mulEquiv_bar (hMiD i) (hOD i) (hDO i)
    have := (hgood i).simple
    refine ⟨e.symm.isSimpleGroup, ?_⟩
    obtain ⟨a, b, hab⟩ := (hgood i).nonab
    exact ⟨e a, e b, fun h1 => hab (e.injective (by rw [map_mul, map_mul, h1]))⟩
  have hss : ∀ i, CFSG.Open.aschbacherThm5IsSemisimple (Abar i) := fun i => by
    obtain ⟨hs, hn⟩ := hbar i
    have := hs
    exact ⟨1, fun _ => Abar i, one_pos, fun _ => ⟨le_rfl, isQuasisimple_of_simple hn⟩,
      fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩
  have hcommLL : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b * a⁻¹ * b⁻¹ ∈ pPrimeCoreOf 2 D := fun a ha b hb => by
    have h1 := (comm_mem h ha hb).1
    rw [commutatorElement_def] at h1
    exact hOD 0 h1
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact bar_commute hcommLL
    · intro x hx y hy
      exact (bar_commute hcommLL y hy x hx).symm
    · exact absurd rfl hij
  have hne : Abar 0 ≠ Abar 1 := by
    intro hij
    obtain ⟨-, a, b, hab⟩ := hbar 0
    apply hab
    apply Subtype.ext
    have hb' : (b : D ⧸ CFSG.Open.aschbacherThm5OddCore D) ∈ Abar 1 := by
      rw [← hij]
      exact b.2
    exact hcomm 0 1 (by decide) a a.2 b hb'
  have hinj : Function.Injective Abar := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hne
    · exact absurd hij.symm hne
    · rfl
  have hgen : ⨆ i, Abar i = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← bar_sup_eq_top (D := D) (L := L₁) (L' := L₂) hD]
    exact sup_le (le_iSup Abar 0) (le_iSup Abar 1)
  have hperm : ∀ x ∈ normalizer (D : Set G), ∀ i, ∃ j,
      (CFSG.Open.aschbacherThm5Preimage D (Abar i)).map (MulAut.conj x).toMonoidHom =
        CFSG.Open.aschbacherThm5Preimage D (Abar j) := by
    intro x hx i
    have hxO : cj x (pPrimeCoreOf 2 D) = pPrimeCoreOf 2 D :=
      cj_eq_of_mem_normalizer (TwoThin.mem_normalizer_pPrimeCoreOf hx)
    have hxM : x ∈ M := hNM ▸ hx
    have hmap : ∀ i, (Mi i ⊔ pPrimeCoreOf 2 D).map (MulAut.conj x).toMonoidHom =
        cj x (Mi i) ⊔ pPrimeCoreOf 2 D := fun i => by
      rw [Subgroup.map_sup]
      change cj x (Mi i) ⊔ cj x (pPrimeCoreOf 2 D) = _
      rw [hxO]
    have key : ∃ j, cj x (Mi i) = Mi j := by
      rcases conj_cases h hxM with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · fin_cases i
        · exact ⟨0, e1⟩
        · exact ⟨1, e2⟩
      · fin_cases i
        · exact ⟨1, e1⟩
        · exact ⟨0, e2⟩
    obtain ⟨j, hj⟩ := key
    refine ⟨j, ?_⟩
    rw [hpre, hpre, hmap, hj]
  have hi : ∀ (i j : Fin 2) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ center G →
      CFSG.Open.aschbacherThm5Centralizes (CFSG.Open.aschbacherThm5Core D)
        (CFSG.Open.aschbacherThm5Preimage D (Abar i)) t →
      CFSG.Open.aschbacherThm5Centralizes (CFSG.Open.aschbacherThm5Core D)
        (CFSG.Open.aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g) →
      g ∈ normalizer (D : Set G) := by
    intro i j t g ht2 htZ hti htj
    rw [hNM]
    have ht1 : t ≠ 1 := fun e => htZ (e ▸ one_mem _)
    unfold CFSG.Open.aschbacherThm5Centralizes at hti htj
    rw [core_eq, hpre] at hti htj
    exact mem_of_centralizes hDM (hMiD i) (hMiD j) hOM (hgood j) (hcov i) ht2 ht1 hti htj
  have hii : ∀ (i : Fin 2) (g : G) (X : Subgroup G),
      X ≤ (normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ CFSG.Open.aschbacherThm5Preimage D (Abar i), ∃ x ∈ X,
        ∃ o ∈ CFSG.Open.aschbacherThm5Core D, a = x * o) →
      g ∈ normalizer (D : Set G) := by
    intro i g X hX hcover
    rw [hNM] at hX ⊢
    rw [core_eq, hpre] at hcover
    refine hcov i g X hX (fun a ha => ?_)
    obtain ⟨x, hx, o, ho, e⟩ := hcover a (Subgroup.mem_sup_left ha)
    exact ⟨x, hx, o, hOM ho, e⟩
  have hH : normalizer (D : Set G) ≠ ⊤ := by
    rw [hNM]
    exact h.maximal.1
  rcases CFSG.Milestones.cl_lit_aschbacher_component_type_theorem_5 G D 2 (by norm_num) Abar
      hinj hss hcomm hgen hperm hi hii hH with h1 | ⟨-, h2⟩
  · omega
  · obtain ⟨-, hrk, -⟩ := h2 0 1 (by decide)
    rw [hpre] at hrk
    have hr1 : CFSG.pRank 2 ↥L₁ = CFSG.Open.pRank 2 L₁ :=
      (SectionRank.pRank_eq_open_pRank_top 2 ↥L₁).trans
        (SectionRank.pRank_eq_pRank_top_subgroup L₁).symm
    have h2' : 2 ≤ CFSG.Open.pRank 2 L₁ := hr1 ▸ h.good₁.rank
    have h3 : CFSG.Open.pRank 2 L₁ ≤ CFSG.Open.pRank 2 (Mi 0 ⊔ pPrimeCoreOf 2 D) :=
      SectionRank.pRank_mono one_lt_two le_sup_left
    omega

end CFSG.GH74.GLS.PU3
