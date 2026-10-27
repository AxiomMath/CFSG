module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped Pointwise

set_option linter.unusedSectionVars false

@[expose] def IsThreeOneTwo (R : Type*) [Group R] : Prop :=
  Nat.card R = 27 ∧ Nat.card (Subgroup.center R) = 3 ∧ commutator R = Subgroup.center R

@[expose] def IsMaxP {G : Type*} [Group G] (p : ℕ) (X Q : Subgroup G) : Prop :=
  Q ≤ X ∧ IsPGroup p Q ∧ ∀ Q' : Subgroup G, Q' ≤ X → IsPGroup p Q' → Q ≤ Q' → Q' = Q

@[expose] def Input11_2Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ (X B L : Subgroup G), IsElemAbelian 3 B → ∀ (hBX : B ≤ X),
      GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B → GLAPComponent 3 X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      (IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) →
      (∀ (b₀ : G) (hb₀ : b₀ ∈ B), ¬ b₀ ∈ Subgroup.normalizer (L : Set G) →
        Nonempty ((↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓
            Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b₀, hBX hb₀⟩} :
              Set (↥X ⧸ GLAPPrimeCore 3 ↥X)))) ⧸
          GLAPPrimeCore 3 ↥(GLAPLayer 3 (barX 3 X (bClosure B L) ⊓
            Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ⟨b₀, hBX hb₀⟩} :
              Set (↥X ⧸ GLAPPrimeCore 3 ↥X))))) ≃*
          (barOf 3 L ⧸ Subgroup.center (barOf 3 L)))) ∧
      (∀ R : Sylow 3 (barOf 3 L), IsThreeOneTwo ↥(R : Subgroup (barOf 3 L)) ∧
        (Subgroup.center ↥(R : Subgroup (barOf 3 L))).map (R : Subgroup (barOf 3 L)).subtype =
          Subgroup.center (barOf 3 L))

@[expose] def InputSylowCentreInn : Prop :=
  ∀ (Lb : Type) [Group Lb] [Finite Lb], (IsSLThreeExc Lb ∨ IsSUThreeExc Lb) →
    ∀ S : Subgroup (MulAut Lb), IsPGroup 3 S →
      (∀ P : Subgroup (MulAut Lb), P ≤ innerAut Lb → IsPGroup 3 P → S ⊓ innerAut Lb ≤ P →
        P = S ⊓ innerAut Lb) →
      ∀ σ ∈ S, (∀ s ∈ S, σ * s = s * σ) → σ ∈ innerAut Lb

structure Hyps : Prop where
  ft : InputFeitThompson
  l23 : Lemma23
  i112 : Input11_2Full
  i112s : Input11_2Struct
  isc : InputSylowCentreInn

structure Setup (G : Type) [Group G] [Finite G] (m : ℕ) (B : Subgroup G) (b : G)
    (L : Subgroup G) : Prop where
  std : GLStanding G m 3
  rank4 : GLATwoLocalRank 3 G = 4
  bz : IsBZeroMax 3 B
  mem : b ∈ B
  ne_one : b ≠ 1
  comp : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L
  exc : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)
  ne_closure : bClosure B L ≠ L


section K0

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem Setup.isElemAbelian (hs : Setup G m B b L) : IsElemAbelian 3 B := hs.bz.1.1

theorem Setup.isBOneMax (hs : Setup G m B b L) : IsBOneMax 3 B :=
  CFSG.HardMathSupport.Solomon.Proving.isBOneMax_of_isBZeroMax (by norm_num) hs.bz

theorem Setup.card_B (hs : Setup G m B b L) : Nat.card B = 3 ^ 4 := by
  have h := hs.bz.1.2.1
  rw [hs.rank4] at h
  exact h

theorem Setup.pRank_B (hs : Setup G m B b L) : CFSG.Open.pRank 3 B = 4 :=
  pRank_eq_of_card Nat.prime_three hs.isElemAbelian hs.card_B

theorem Setup.le_centralizer (hs : Setup G m B b L) :
    B ≤ Subgroup.centralizer ({b} : Set G) :=
  le_centralizer_of_mem hs.isElemAbelian hs.mem

theorem Setup.centralizer_ne_top (hs : Setup G m B b L) :
    Subgroup.centralizer ({b} : Set G) ≠ ⊤ := by
  have := hs.std.simple
  exact centralizer_ne_top_of_simple hs.std.nonabelian hs.ne_one

theorem Setup.rankX (hs : Setup G m B b L) :
    GLATwoLocalRank 3 ↥(Subgroup.centralizer ({b} : Set G)) ≤ CFSG.Open.pRank 3 B :=
  (glaTwoLocalRank_subgroup_le Nat.prime_three _).trans (by rw [hs.rank4, hs.pRank_B])

theorem Setup.isSC (hl : Lemma23) (hs : Setup G m B b L) : IsSCp 3 ⊤ B :=
  hl G m 3 hs.std B hs.isBOneMax

theorem Setup.not_normalizes (hs : Setup G m B b L) :
    ¬ B ≤ Subgroup.normalizer (L : Set G) := by
  intro h
  apply hs.ne_closure
  refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
  · rw [mem_normalizer_iff_gLBConj_eq.1 (h hg)]
  · exact le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])

theorem Setup.index_three (H : Hyps) (hs : Setup G m B b L) :
    (Subgroup.normalizer (L : Set G)).relIndex B = 3 :=
  (H.i112 G m 3 hs.std (Subgroup.centralizer ({b} : Set G)) B L hs.isElemAbelian
    hs.le_centralizer hs.rankX hs.comp hs.not_normalizes).2.1

theorem Setup.conj_cases (H : Hyps) (hs : Setup G m B b L) {L₂ L₃ : Subgroup G}
    (hL₂ : IsBConjugate B L L₂) (hL₃ : IsBConjugate B L L₃) (h12 : L ≠ L₂) (h13 : L ≠ L₃)
    (h23 : L₂ ≠ L₃) :
    ∀ Li : Subgroup G, IsBConjugate B L Li → Li = L ∨ Li = L₂ ∨ Li = L₃ := by
  obtain ⟨M₂, M₃, -, -, hM12, hM13, hM23, hall⟩ :=
    exists_three_conjugates hs.isElemAbelian.1 (hs.index_three H)
  intro Li hLi
  rcases hall L₂ hL₂ with h | h | h <;> rcases hall L₃ hL₃ with h' | h' | h' <;>
    rcases hall Li hLi with h'' | h'' | h'' <;> subst_vars <;> simp_all

theorem Setup.conj_comp (hs : Setup G m B b L) {g : G} (hg : g ∈ B) :
    GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) (GLBConj g L) := by
  have hcomm : g * b = b * g := elemAbelian_comm hs.isElemAbelian hg hs.mem
  have := glaPComponent_gLBConj g hs.comp
  rwa [gLBConj_centralizer_singleton_of_commute hcomm] at this

theorem Setup.conj_not_normalizes (hs : Setup G m B b L) {g : G} (hg : g ∈ B) :
    ¬ B ≤ Subgroup.normalizer (GLBConj g L : Set G) := by
  rw [le_normalizer_gLBConj_iff hs.isElemAbelian.1 hg]
  exact hs.not_normalizes

end K0

section Generic
variable {G : Type*} [Group G] [Finite G]

theorem G1_exists_fixed {p : ℕ} (hp : p.Prime) {A P : Subgroup G} (hA : IsPGroup p A)
    (hP : IsPGroup p P) (hPne : P ≠ ⊥) (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    ∃ x ∈ P, x ≠ 1 ∧ ∀ a ∈ A, a * x = x * a := by
  have : Fact p.Prime := ⟨hp⟩
  let φ : A →* MulAut P := (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hAP)
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P φ
  have hdvd : p ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq P h) hPne
    · exact h
  have h1 : (1 : P) ∈ MulAction.fixedPoints A P := by
    intro a
    exact smul_one a
  obtain ⟨b, hb, hne⟩ := hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := P) hdvd h1
  refine ⟨b, b.2, fun h => hne ?_, fun a ha => ?_⟩
  · exact (Subtype.ext h.symm)
  · have := congrArg (fun y : P => (y : G)) (hb ⟨a, ha⟩)
    have h2 : a * (b : G) * a⁻¹ = b := this
    calc a * (b : G) = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h2]

theorem G3_card_of_isMaxP {p : ℕ} (hp : p.Prime) {X Q : Subgroup G} (h : IsMaxP p X Q) :
    Nat.card Q = p ^ (Nat.card X).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQX, hQp, hmax⟩ := h
  have hQ' : IsPGroup p (Q.subgroupOf X) := hQp.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  let T : Subgroup G := (S : Subgroup X).map X.subtype
  have hTp : IsPGroup p T := S.isPGroup'.map _
  have hTX : T ≤ X := Subgroup.map_subtype_le _
  have hQT : Q ≤ T := by
    intro x hx
    exact ⟨⟨x, hQX hx⟩, hS (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hTQ : T = Q := hmax T hTX hTp hQT
  rw [← hTQ]
  change Nat.card ((S : Subgroup X).map X.subtype) = _
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact Sylow.card_eq_multiplicity S

theorem G3'_isMaxP_of_card {p : ℕ} (hp : p.Prime) {X Q : Subgroup G} (hQX : Q ≤ X)
    (hQ : IsPGroup p Q) (hc : Nat.card Q = p ^ (Nat.card X).factorization p) : IsMaxP p X Q := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hQX, hQ, fun Q' hQ'X hQ'p hQQ' => ?_⟩
  obtain ⟨k, hk⟩ := hQ'p.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card X := hk ▸ Subgroup.card_dvd_of_le hQ'X
  have hle : k ≤ (Nat.card X).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  have hge : Nat.card Q' ≤ Nat.card Q := by
    rw [hk, hc]; exact Nat.pow_le_pow_right hp.pos hle
  exact (Subgroup.eq_of_le_of_card_ge hQQ' hge).symm

omit [Finite G] in
theorem G4_aux_pow {K R : Subgroup G} (hRK : R ≤ Subgroup.normalizer (K : Set G)) {k r : G}
    (hk : k ∈ K) (hr : r ∈ R) (n : ℕ) : ∃ k' ∈ K, (k * r) ^ n = k' * r ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    have hrn : r ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ (hRK hr) n
    have hm : r ^ n * k * (r ^ n)⁻¹ ∈ K := by
      rw [Subgroup.mem_normalizer_iff] at hrn
      exact (hrn k).1 hk
    refine ⟨k' * (r ^ n * k * (r ^ n)⁻¹), K.mul_mem hk' hm, ?_⟩
    rw [pow_succ, h]
    group

theorem G4_mem_of_mem_sup {p : ℕ} (_hp : p.Prime) {K R : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hR : Nat.Coprime p (Nat.card R)) {x : G}
    (hx : x ∈ K ⊔ R) (hxp : x ^ p = 1) : x ∈ K := by
  have hx' : x ∈ ((K ⊔ R : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K R hRK] at hx'
  obtain ⟨k, hk, r, hr, rfl⟩ := hx'
  obtain ⟨k', hk', h⟩ := G4_aux_pow hRK hk hr p
  have hrp : r ^ p ∈ K := by
    have : r ^ p = k'⁻¹ := by
      rw [h] at hxp
      calc r ^ p = k'⁻¹ * (k' * r ^ p) := by group
        _ = k'⁻¹ := by rw [hxp]; simp
    rw [this]; exact K.inv_mem hk'
  have hrn : r ^ Nat.card R = 1 := by
    have := pow_card_eq_one' (G := R) (x := ⟨r, hr⟩)
    exact congrArg Subtype.val this
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hR
  have hrK : r ∈ K := by
    have : r = (r ^ p) ^ a * (r ^ Nat.card R) ^ b := by
      rw [← zpow_natCast, ← zpow_natCast r (Nat.card R), ← zpow_mul, ← zpow_mul, ← zpow_add]
      have : (p : ℤ) * a + (Nat.card R : ℤ) * b = 1 := by rw [mul_comm (p : ℤ), mul_comm (Nat.card R : ℤ)]; exact hab
      rw [this, zpow_one]
    rw [this, hrn, one_zpow, mul_one]
    exact K.zpow_mem hrp a
  exact K.mul_mem hk hrK

theorem G5_card_le {p : ℕ} (hp : p.Prime) {X Q : Subgroup G} (hQX : Q ≤ X) (hQ : IsPGroup p Q) :
    Nat.card Q ≤ p ^ (Nat.card X).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : p ^ k ∣ Nat.card X := hk ▸ Subgroup.card_dvd_of_le hQX
  have hle : k ≤ (Nat.card X).factorization p :=
    (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvd
  rw [hk]; exact Nat.pow_le_pow_right hp.pos hle

open scoped Pointwise in
theorem G5_conj_mem {K : Type*} [Group K] [Finite K] (p : ℕ) [Fact p.Prime] (Q P : Sylow p K)
    (g : K) (h : g • Q = P) (x : K) (hx : x ∈ (Q : Subgroup K)) : g * x * g⁻¹ ∈ (P : Subgroup K) := by
  subst h
  have key : (MulAut.conj g • x) ∈ ((g • Q : Sylow p K) : Set K) := by
    rw [Sylow.coe_smul]; exact Set.smul_mem_smul_set hx
  have k2 : g * x * g⁻¹ ∈ ((g • Q : Sylow p K) : Set K) := by simpa using key
  exact k2

theorem G5_card_inf_normal {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (N P : Subgroup K) [N.Normal] (hP : Nat.card P = p ^ (Nat.card K).factorization p) :
    Nat.card ↥(P ⊓ N) = p ^ (Nat.card N).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p P := IsPGroup.of_card hP
  apply le_antisymm
  · exact G5_card_le hp inf_le_right (hPp.to_le inf_le_left)
  · let Ps : Sylow p K := Sylow.ofCard P hP
    obtain ⟨S⟩ : Nonempty (Sylow p N) := inferInstance
    let U : Subgroup K := (S : Subgroup N).map N.subtype
    have hU : IsPGroup p U := S.isPGroup'.map _
    obtain ⟨Q, hUQ⟩ := hU.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Ps
    have hcU : Nat.card U = p ^ (Nat.card N).factorization p := by
      change Nat.card ((S : Subgroup N).map N.subtype) = _
      rw [Subgroup.card_map_of_injective N.subtype_injective]
      exact Sylow.card_eq_multiplicity S
    rw [← hcU]
    have hUle : U ≤ (Q : Subgroup K) ⊓ N := le_inf hUQ (Subgroup.map_subtype_le _)
    refine (Subgroup.card_le_of_le hUle).trans ?_
    let f : ↥((Q : Subgroup K) ⊓ N) → ↥(P ⊓ N) := fun x =>
      ⟨g * x * g⁻¹, G5_conj_mem p Q Ps g hg x x.2.1, (inferInstance : N.Normal).conj_mem x x.2.2 g⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this

theorem G5_isMaxP_step {p : ℕ} (hp : p.Prime) {H M Q : Subgroup G} (hHM : H ≤ M)
    (hN : (H.subgroupOf M).Normal) (hQ : IsMaxP p M Q) : IsMaxP p H (Q ⊓ H) := by
  have hc := G3_card_of_isMaxP hp hQ
  have hQM := hQ.1
  have hP : Nat.card (Q.subgroupOf M) = p ^ (Nat.card (⊤ : Subgroup M)).factorization p := by
    rw [Subgroup.card_top, ← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have h1 := G5_card_inf_normal hp (H.subgroupOf M) (Q.subgroupOf M) (by
    rw [Subgroup.card_top] at hP; exact hP)
  have e1 : Nat.card ↥(Q.subgroupOf M ⊓ H.subgroupOf M) = Nat.card ↥(Q ⊓ H) := by
    have : Q.subgroupOf M ⊓ H.subgroupOf M = (Q ⊓ H).subgroupOf M :=
      Subgroup.ext fun x => by simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hQM)).toEquiv
  have e2 : Nat.card ↥(H.subgroupOf M) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
  rw [e1, e2] at h1
  exact G3'_isMaxP_of_card hp inf_le_right (hQ.2.1.to_le inf_le_left) h1

theorem G2_exists_normalized_isMaxP {A H : Subgroup G} (hA : IsPGroup 3 A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) :
    ∃ P : Subgroup G, IsMaxP 3 H P ∧ A ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨S, hSH, hSc, hSn⟩ := exists_normalized_sylow hA hAH
  refine ⟨S, G3'_isMaxP_of_card Nat.prime_three hSH (IsPGroup.of_card hSc) hSc, fun a ha => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => ?_, fun hh => ?_⟩
  · have := hSn a ha h hh
    simpa [mul_assoc] using this
  · have := hSn a⁻¹ (inv_mem ha) _ hh
    simpa [mul_assoc] using this

theorem G5_isMaxP_inf_of_isSubnormal {p : ℕ} (hp : p.Prime) {X L Q : Subgroup G}
    (hL : IsSubnormal L X) (hQ : IsMaxP p X Q) : IsMaxP p L (Q ⊓ L) := by
  revert hQ
  induction hL with
  | refl H => intro hQ; rwa [inf_eq_left.2 hQ.1]
  | step hHM hN _ ih =>
    intro hQ
    have := G5_isMaxP_step hp hHM hN (ih hQ)
    rwa [inf_assoc, inf_eq_right.2 hHM] at this

end Generic

section C1Helpers
variable {G : Type*} [Group G]

theorem C1_card_sup_of_disjoint {P Q : Subgroup G} (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    (hd : ∀ x ∈ P, x ∈ Q → x = 1) :
    Nat.card ↥(P ⊔ Q) = Nat.card P * Nat.card Q := by
  let f : P →* G := P.subtype
  let g' : Q →* G := Q.subtype
  have hcomm : ∀ (m : P) (n : Q), Commute (f m) (g' n) := fun m n => hc m m.2 n n.2
  have hdisj : Disjoint P Q := by
    rw [Subgroup.disjoint_def]
    exact fun {x} hx hy => hd x hx hy
  have hinj : Function.Injective (MonoidHom.noncommCoprod f g' hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨P.subtype_injective, Q.subtype_injective, ?_⟩
    simpa [f, g'] using hdisj
  have hrange : (MonoidHom.noncommCoprod f g' hcomm).range = P ⊔ Q := by
    rw [MonoidHom.noncommCoprod_range]
    simp [f, g']
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

end C1Helpers

theorem C1_card_inf_centralizer_le {M : Type} [Group M] [Finite M] {E H : Subgroup M}
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup M, IsElemAbelian 3 E' → E ≤ E' → E' = E)
    (hEH : E ≤ Subgroup.normalizer (H : Set M))
    (hsyl : ∀ P : Subgroup M, IsMaxP 3 H P → IsElemAbelian 3 P ∧ Nat.card P = 9)
    (hZ : ∀ z ∈ H, (∀ h ∈ H, z * h = h * z) → z ^ 3 = 1 → z = 1) :
    9 * Nat.card ↥(E ⊓ Subgroup.centralizer (H : Set M)) ≤ Nat.card E := by
  set C : Subgroup M := E ⊓ Subgroup.centralizer (H : Set M) with hC
  have hCE : C ≤ E := inf_le_left
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨P, hPmax, hEP⟩ := G2_exists_normalized_isMaxP hE3 hEH
  obtain ⟨hPel, hP9⟩ := hsyl P hPmax
  have hPH : P ≤ H := hPmax.1
  have hPp : IsPGroup 3 P := hPmax.2.1
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h] at hP9
    simp at hP9
  obtain ⟨e, heP, he1, heE⟩ := G1_exists_fixed Nat.prime_three hE3 hPp hPne hEP
  have he3 : e ^ 3 = 1 := hPel.2 e heP
  have heE' : e ∈ E := by
    have hel := isElemAbelian_sup_zpowers hE he3 heE
    have := hmax _ hel le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have heC : e ∉ C := by
    intro h
    refine he1 (hZ e (hPH heP) (fun h' hh' => ?_) he3)
    exact (Subgroup.mem_centralizer_iff.1 h.2 h' hh').symm
  have hCP : ∀ c ∈ C, ∀ x ∈ P, c * x = x * c := fun c hc x hx =>
    (Subgroup.mem_centralizer_iff.1 hc.2 x (hPH hx)).symm
  have hcard := card_sup_zpowers_of_pow_three_eq_one he3 heC (fun h hh => hCP h hh e heP)
  have hle : C ⊔ Subgroup.zpowers e ≤ E :=
    sup_le hCE (Subgroup.zpowers_le.2 heE')
  have hge : 3 * Nat.card C ≤ Nat.card E := by
    have h := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rwa [hcard] at h
  have hEeq : C ⊔ Subgroup.zpowers e = E := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := E)).1 hE3
    have hCdvd : Nat.card C ∣ 3 ^ n := hn ▸ Subgroup.card_dvd_of_le hCE
    obtain ⟨k, hk, hCk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hCdvd
    have h1 : 3 ^ (k + 1) ≤ 3 ^ n := by
      rw [pow_succ, ← hCk, mul_comm, ← hn]; exact hge
    have h2 : 3 ^ n < 3 ^ (k + 2) := by
      rw [pow_add, ← hCk, ← hn]; linarith
    have h1' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h1
    have h2' := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 h2
    have hnk : n = k + 1 := by omega
    have hEcard : Nat.card E = 3 * Nat.card C := by
      rw [hn, hnk, hCk, pow_succ, mul_comm]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcard, hEcard]
  have hEcP : E ≤ Subgroup.centralizer (P : Set M) := by
    rw [← hEeq]
    refine sup_le ?_ ?_
    · intro c hc
      exact Subgroup.mem_centralizer_iff.2 fun x hx => (hCP c hc x hx).symm
    · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
      exact elemAbelian_comm hPel hx heP
  have hPE : P ≤ E := by
    intro x hx
    have hx3 : x ^ 3 = 1 := hPel.2 x hx
    have hcx : ∀ a ∈ E, a * x = x * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (hEcP ha) x hx).symm
    have hel := isElemAbelian_sup_zpowers hE hx3 hcx
    have := hmax _ hel le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hd : ∀ x ∈ P, x ∈ C → x = 1 := by
    intro x hx hxC
    refine hZ x (hPH hx) (fun h' hh' => ?_) (hPel.2 x hx)
    exact (Subgroup.mem_centralizer_iff.1 hxC.2 h' hh').symm
  have hcard2 := C1_card_sup_of_disjoint (P := P) (Q := C)
    (fun x hx c hc => (hCP c hc x hx).symm) hd
  have hle2 : P ⊔ C ≤ E := sup_le hPE hCE
  have : Nat.card ↥(P ⊔ C) ≤ Nat.card E :=
    Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle2)
  rw [hcard2, hP9] at this
  omega

section C2

@[expose] def c2_cent {G : Type*} [Group G] (N X J : Subgroup G)
    (hN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) : Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ y ∈ J, y * g * y⁻¹ * g⁻¹ ∈ N}
  one_mem' := ⟨one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
    refine ⟨mul_mem hgX hhX, fun y hy => ?_⟩
    have h1 : y * (g * h) * y⁻¹ * (g * h)⁻¹ =
        (y * g * y⁻¹ * g⁻¹) * (g * (y * h * y⁻¹ * h⁻¹) * g⁻¹) := by group
    rw [h1]
    exact N.mul_mem (hg y hy) (hN g hgX _ (hh y hy))
  inv_mem' := by
    rintro g ⟨hgX, hg⟩
    refine ⟨inv_mem hgX, fun y hy => ?_⟩
    have h1 : y * g⁻¹ * y⁻¹ * (g⁻¹)⁻¹ = g⁻¹ * (y * g * y⁻¹ * g⁻¹)⁻¹ * g := by group
    rw [h1]
    have := hN g⁻¹ (inv_mem hgX) _ (N.inv_mem (hg y hy))
    simpa using this

theorem C2_card_components_le_five (hft : InputFeitThompson) {G : Type} [Group G] [Finite G]
    (h4 : GLATwoLocalRank 3 G ≤ 4) {X : Subgroup G} (S : Finset (Subgroup G))
    (hS : ∀ J ∈ S, GLAPComponent 3 X J) : S.card ≤ 5 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨J₁, hJ₁⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  set S' := S.erase J₁ with hS'def
  have hS'card : 5 ≤ S'.card := by
    rw [hS'def, Finset.card_erase_of_mem hJ₁]; omega
  have hbot : IsElemAbelian 3 (⊥ : Subgroup G) :=
    ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx]; simp⟩
  obtain ⟨B', -, hB'X, hB'le, hB'el, hB'card, -, -⟩ := exists_extension (X := X) S'
    (fun J hJ => hS J (Finset.mem_of_mem_erase hJ)) hbot bot_le (fun L _ => bot_le)
    (fun J _ => bot_le)
  have hN : ∀ x ∈ X, ∀ n ∈ GLAPPrimeCoreOf 3 X, x * n * x⁻¹ ∈ GLAPPrimeCoreOf 3 X :=
    fun x hx n hn => mem_gLAPPrimeCoreOf_conj hn hx
  set W := c2_cent (GLAPPrimeCoreOf 3 X) X J₁ hN with hW
  have hJW : ∀ J ∈ S', J ≤ W := by
    intro J hJ g hg
    have hne : J₁ ≠ J := fun h => (Finset.mem_erase.1 hJ).1 h.symm
    have hc := commutator_le_gLAPPrimeCore_of_ne Nat.prime_three (hS J₁ hJ₁)
      (hS J (Finset.mem_of_mem_erase hJ)) hne
    refine ⟨(hS J (Finset.mem_of_mem_erase hJ)).1 hg, fun y hy => ?_⟩
    exact hc (Subgroup.commutator_mem_commutator hy hg)
  have hB'W : B' ≤ W := by
    refine hB'le.trans (sup_le bot_le (iSup₂_le fun J hJ => hJW J hJ))
  have hLA : ⁅J₁, B'⁆ ≤ GLAPPrimeCoreOf 3 X :=
    Subgroup.commutator_le.2 fun x hx y hy => (hB'W hy).2 x hx
  obtain ⟨T, hT, hT2, hB'T⟩ := exists_twoGroup_normalized_of_centralizes hft Nat.prime_three
    (by norm_num) (hS J₁ hJ₁) hB'X (GL83.isPGroup_of_isElemAbelian hB'el) hLA
  have h1 := pRank_le_glaTwoLocalRank_of_normalizes Nat.prime_three hT hT2 hB'T
  rw [pRank_eq_of_card Nat.prime_three hB'el (k := S'.card) (by simpa using hB'card)] at h1
  omega

end C2

section C4Helpers

theorem C4_card_center {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb) :
    Nat.card (Subgroup.center Lb) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ : Nonempty (Sylow 3 Lb) := inferInstance
  obtain ⟨h1, h2⟩ := hR R
  rw [← h2, Subgroup.card_map_of_injective (R : Subgroup Lb).subtype_injective]
  exact h1.2.1

theorem C4_factorization_Lb {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb) :
    (Nat.card Lb).factorization 3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R⟩ : Nonempty (Sylow 3 Lb) := inferInstance
  have h1 := (hR R).1.1
  have h2 := Sylow.card_eq_multiplicity R
  rw [h1] at h2
  have : (3 : ℕ) ^ 3 = 3 ^ (Nat.card Lb).factorization 3 := by
    rw [← h2]; norm_num
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm

theorem C4_card_Lb {Lb : Type} [Group Lb] [Finite Lb] :
    Nat.card Lb = Nat.card (Lb ⧸ Subgroup.center Lb) * Nat.card (Subgroup.center Lb) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem C4_factorization_S {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb) :
    (Nat.card (Lb ⧸ Subgroup.center Lb)).factorization 3 = 2 := by
  have h3 := C4_factorization_Lb hR
  have hc := C4_card_center hR
  rw [C4_card_Lb, hc] at h3
  have hpos : Nat.card (Lb ⧸ Subgroup.center Lb) ≠ 0 := Nat.card_pos.ne'
  rw [Nat.factorization_mul hpos (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_three] at h3
  omega

theorem C4_center_trivial {S : Type} [Group S] (hsimple : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (s : S) (hs : ∀ t, t * s = s * t) : s = 1 := by
  have hn : Subgroup.center S = ⊥ ∨ Subgroup.center S = ⊤ :=
    IsSimpleGroup.eq_bot_or_eq_top_of_normal _
  rcases hn with h | h
  · have : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]; exact fun t => hs t
    rw [h] at this
    simpa using this
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this) b).symm

theorem C4_card_comap {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    (T : Subgroup (Lb ⧸ Subgroup.center Lb)) :
    Nat.card (T.comap (QuotientGroup.mk' (Subgroup.center Lb))) = 3 * Nat.card T := by
  have hidx := Subgroup.index_comap_of_surjective (H := T)
    (QuotientGroup.mk'_surjective (Subgroup.center Lb))
  have h1 := Subgroup.card_mul_index (T.comap (QuotientGroup.mk' (Subgroup.center Lb)))
  have h2 := Subgroup.card_mul_index T
  rw [hidx] at h1
  have hpos : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [C4_card_Lb (Lb := Lb), C4_card_center hR, ← h2] at h1
  have : Nat.card (T.comap (QuotientGroup.mk' (Subgroup.center Lb))) * T.index =
      (3 * Nat.card T) * T.index := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) this

theorem C4_S_elemAbelian {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    (T : Subgroup (Lb ⧸ Subgroup.center Lb)) (hT : Nat.card T = 9) :
    IsElemAbelian 3 T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (Subgroup.center Lb) with hπ
  have hcard : Nat.card (T.comap π) = 3 ^ (Nat.card Lb).factorization 3 := by
    rw [C4_card_comap hR, hT, C4_factorization_Lb hR]; norm_num
  let R : Sylow 3 Lb := Sylow.ofCard (T.comap π) hcard
  obtain ⟨⟨h27, hZc, hcomm⟩, hZ⟩ := hR R
  have hmem : ∀ x : Lb, x ∈ (R : Subgroup Lb) ↔ π x ∈ T := fun x => Iff.rfl
  have hker : ∀ x : Lb, π x = 1 ↔ x ∈ Subgroup.center Lb := fun x => QuotientGroup.eq_one_iff x
  have hsurj : ∀ a ∈ T, ∃ r ∈ (R : Subgroup Lb), π r = a := by
    intro a ha
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨r, (hmem r).2 ha, rfl⟩
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    obtain ⟨r₁, hr₁, rfl⟩ := hsurj a ha
    obtain ⟨r₂, hr₂, rfl⟩ := hsurj b hb
    have h1 : (⟨r₁ * r₂ * r₁⁻¹ * r₂⁻¹, (R : Subgroup Lb).mul_mem
        ((R : Subgroup Lb).mul_mem ((R : Subgroup Lb).mul_mem hr₁ hr₂)
          ((R : Subgroup Lb).inv_mem hr₁)) ((R : Subgroup Lb).inv_mem hr₂)⟩ : (R : Subgroup Lb)) ∈
        Subgroup.center (R : Subgroup Lb) := by
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨r₁, hr₁⟩ : (R : Subgroup Lb)))
        (Subgroup.mem_top (⟨r₂, hr₂⟩ : (R : Subgroup Lb)))
    have h2 : r₁ * r₂ * r₁⁻¹ * r₂⁻¹ ∈ Subgroup.center Lb := by
      rw [← hZ]
      exact ⟨_, h1, rfl⟩
    have h3 : π (r₁ * r₂ * r₁⁻¹ * r₂⁻¹) = 1 := (hker _).2 h2
    simp only [map_mul, map_inv] at h3
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm ▸ rfl
  refine ⟨⟨⟨fun a b => Subtype.ext (hcommT a a.2 b b.2)⟩⟩, ?_⟩
  intro a ha
  by_contra hne
  have hord : orderOf a ∣ 9 := by
    have := Subgroup.orderOf_dvd_natCard T ha
    rwa [hT] at this
  have hord' : orderOf a ∣ 3 ^ 2 := by simpa using hord
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord'
  have hk2 : k = 2 := by
    interval_cases k
    · exfalso; apply hne
      have h0 : a = 1 := by simpa using hk'
      simp [h0]
    · exfalso; apply hne
      have := pow_orderOf_eq_one a
      rwa [hk', pow_one] at this
    · rfl
  subst hk2
  have hcyc : IsCyclic T := by
    refine isCyclic_of_orderOf_eq_card (⟨a, ha⟩ : T) ?_
    rw [hT, Subgroup.orderOf_mk, hk']; norm_num
  let f : (R : Subgroup Lb) →* T :=
    ((π.comp (R : Subgroup Lb).subtype).codRestrict T (fun x => (hmem x).1 x.2))
  have hfker : f.ker ≤ Subgroup.center (R : Subgroup Lb) := by
    intro x hx
    have h1 : π (x : Lb) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have h2 : (x : Lb) ∈ Subgroup.center Lb := (hker _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h2) g)
  have hcm := f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  have htop : Subgroup.center (R : Subgroup Lb) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    exact hcm.is_comm.comm g x
  have := hZc
  rw [htop, Subgroup.card_top, h27] at this
  omega

theorem C4_inf_trivial {X : Type*} [Group X] [Finite X] {N Q : Subgroup X}
    (hN : Nat.Coprime 3 (Nat.card N)) (hQ : IsPGroup 3 Q) {x : X} (hxQ : x ∈ Q) (hxN : x ∈ N) :
    x = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hQ) ⟨x, hxQ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hd : orderOf x ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hxN
  rw [hk] at hd
  have h1 : 3 ^ k = 1 := (Nat.Coprime.pow_left k hN).eq_one_of_dvd hd
  rw [h1] at hk
  exact orderOf_eq_one_iff.1 hk

theorem C4_factorization_H {M : Type} [Group M] [Finite M] {Lb : Type} [Group Lb] [Finite Lb]
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {H : Subgroup M} (e : (↥H ⧸ GLAPPrimeCore 3 ↥H) ≃* (Lb ⧸ Subgroup.center Lb)) :
    (Nat.card H).factorization 3 = 2 := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥H)
  have hNc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥H)) := coprime_card_gLAPPrimeCore_aux 3 ↥H
  have hNnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥H) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNc
  rw [hc, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hNnd, add_zero, Nat.card_congr e.toEquiv]
  exact C4_factorization_S hR

end C4Helpers
theorem C4_layer_structure_aux {M : Type} [Group M] [Finite M] {Lb : Type} [Group Lb] [Finite Lb]
    (hq : IsQuasisimple Lb)
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {H : Subgroup M} (e : (↥H ⧸ GLAPPrimeCore 3 ↥H) ≃* (Lb ⧸ Subgroup.center Lb)) :
    (∀ P : Subgroup M, IsMaxP 3 H P → IsElemAbelian 3 P ∧ Nat.card P = 9) ∧
      (∀ z ∈ H, (∀ h ∈ H, z * h = h * z) → z ^ 3 = 1 → z = 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥H →* Lb ⧸ Subgroup.center Lb :=
    e.toMonoidHom.comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H))
  have hfs : Function.Surjective f := fun s => by
    obtain ⟨q, rfl⟩ := e.surjective s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  have hfker : ∀ x : ↥H, f x = 1 → x ∈ GLAPPrimeCore 3 ↥H := fun x hx => by
    have : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥H)) x = 1 := e.injective (by simpa [f] using hx)
    exact (QuotientGroup.eq_one_iff x).1 this
  have hNc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥H)) := coprime_card_gLAPPrimeCore_aux 3 ↥H
  have hv := C4_factorization_H hR e
  refine ⟨fun P hP => ?_, fun z hz hzc hz3 => ?_⟩
  · obtain ⟨hPH, hPp, -⟩ := id hP
    have hcP : Nat.card P = 9 := by
      rw [G3_card_of_isMaxP Nat.prime_three hP, hv]; norm_num
    have hP'p : IsPGroup 3 (P.subgroupOf H) := hPp.comap_subtype
    have hcP' : Nat.card (P.subgroupOf H) = 9 := by
      rw [← hcP]; exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv)
    have hinj : Function.Injective (f.comp (P.subgroupOf H).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : (x : ↥H) ∈ GLAPPrimeCore 3 ↥H := hfker _ hx
      exact Subtype.ext (C4_inf_trivial hNc hP'p x.2 h1)
    set T := (f.comp (P.subgroupOf H).subtype).range with hT
    have hcT : Nat.card T = 9 := by
      rw [← hcP']
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hTea := C4_S_elemAbelian hR T hcT
    have hfT : ∀ x : ↥H, (x : M) ∈ P → f x ∈ T := fun x hx =>
      ⟨⟨x, hx⟩, rfl⟩
    have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
      intro x hx y hy
      have hxH := hPH hx
      have hyH := hPH hy
      let x' : ↥H := ⟨x, hxH⟩
      let y' : ↥H := ⟨y, hyH⟩
      have h1 : f (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
        have := hTea.1.is_comm.comm ⟨f x', hfT x' hx⟩ ⟨f y', hfT y' hy⟩
        have h2 : f x' * f y' = f y' * f x' := congrArg Subtype.val this
        simp only [map_mul, map_inv]
        rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, h2]
      have h3 : x' * y' * x'⁻¹ * y'⁻¹ ∈ P.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact P.mul_mem (P.mul_mem (P.mul_mem hx hy) (P.inv_mem hx)) (P.inv_mem hy)
      have h4 := C4_inf_trivial hNc hP'p h3 (hfker _ h1)
      have h5 : (x' * y' * x'⁻¹ * y'⁻¹ : ↥H) = 1 := h4
      have h6 : x * y * x⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h5
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h6
      exact h6.symm ▸ rfl
    have hcube : ∀ x ∈ P, x ^ 3 = 1 := by
      intro x hx
      have hxH := hPH hx
      let x' : ↥H := ⟨x, hxH⟩
      have h1 : f (x' ^ 3) = 1 := by
        have := hTea.2 (f x') (hfT x' hx)
        simpa using this
      have h3 : x' ^ 3 ∈ P.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact P.pow_mem hx 3
      have h4 := C4_inf_trivial hNc hP'p h3 (hfker _ h1)
      exact congrArg Subtype.val h4
    exact ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hcube⟩, hcP⟩
  · let z' : ↥H := ⟨z, hz⟩
    have hcen : ∀ t : Lb ⧸ Subgroup.center Lb, t * f z' = f z' * t := fun t => by
      obtain ⟨h, rfl⟩ := hfs t
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc h h.2).symm
    have h1 : f z' = 1 :=
      C4_center_trivial hq.2.1 hq.2.2 _ hcen
    have h2 : z' ∈ GLAPPrimeCore 3 ↥H := hfker _ h1
    have h3 : orderOf z' ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
    have h4 : orderOf z' ∣ Nat.card (GLAPPrimeCore 3 ↥H) := Subgroup.orderOf_dvd_natCard _ h2
    have h5 : orderOf z' = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h3 hNc) h4
    exact congrArg Subtype.val (orderOf_eq_one_iff.1 h5)

section C4KMain
variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem C4_nonabelian_of_open {Lb : Type} [Group Lb] (hq : CFSG.Open.IsQuasisimple Lb) :
    ∃ a b : Lb ⧸ Subgroup.center Lb, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have h1 : commutator Lb ≤ Subgroup.center Lb := by
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    have h3 : (QuotientGroup.mk g₁ : Lb ⧸ Subgroup.center Lb) * (QuotientGroup.mk g₂) *
        (QuotientGroup.mk g₁)⁻¹ * (QuotientGroup.mk g₂)⁻¹ = 1 := by
      rw [hcon (QuotientGroup.mk g₁) (QuotientGroup.mk g₂)]; group
    simpa [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h3
  have h2 : Subgroup.center Lb = ⊤ := top_le_iff.1 (hq.1 ▸ h1)
  have := hq.2.toNontrivial
  have : Subsingleton (Lb ⧸ Subgroup.center Lb) := by
    rw [h2]; exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton _ this

theorem C4_layer_structure {M : Type} [Group M] [Finite M] {Lb : Type} [Group Lb] [Finite Lb]
    (hq : CFSG.Open.IsQuasisimple Lb)
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {H : Subgroup M} (e : (↥H ⧸ GLAPPrimeCore 3 ↥H) ≃* (Lb ⧸ Subgroup.center Lb)) :
    (∀ P : Subgroup M, IsMaxP 3 H P → IsElemAbelian 3 P ∧ Nat.card P = 9) ∧
      (∀ z ∈ H, (∀ h ∈ H, z * h = h * z) → z ^ 3 = 1 → z = 1) :=
  C4_layer_structure_aux ⟨(Group.isPerfect_def (G := Lb)).2 hq.1, hq.2, C4_nonabelian_of_open hq⟩ hR e

theorem Kord_factorization_card (H : Hyps) (hs : Setup G m B b L) :
    (Nat.card L).factorization 3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := H.i112s G m hs.std (Subgroup.centralizer ({b} : Set G)) B L hs.isElemAbelian
    hs.le_centralizer hs.rankX hs.comp hs.not_normalizes hs.exc
  obtain ⟨R⟩ : Nonempty (Sylow 3 (barOf 3 L)) := inferInstance
  have h27 := (h.2 R).1.1
  have h2 := Sylow.card_eq_multiplicity R
  rw [h27] at h2
  have h3 : (3 : ℕ) ^ 3 = 3 ^ (Nat.card (barOf 3 L)).factorization 3 := by
    rw [← h2]; norm_num
  have h4 : (Nat.card (barOf 3 L)).factorization 3 = 3 :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3).symm
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L)
  have hNc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥L)) := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hNnd : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥L) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNc
  rw [hc, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hNnd, add_zero]
  exact h4

end C4KMain

section Conj

variable {G : Type*} [Group G]

theorem oPrimePOf_gLBConj_ge (p : ℕ) (g : G) (H : Subgroup G) :
    GLBConj g (oPrimePOf p H) ≤ oPrimePOf p (GLBConj g H) := by
  intro z hz
  rw [mem_gLBConj] at hz
  obtain ⟨x', hx', hxz⟩ := hz
  refine ⟨conjEquiv g H x', ?_, ?_⟩
  · show QuotientGroup.mk' (GLAPPrimeCore p ↥(GLBConj g H)) (conjEquiv g H x') ∈
      CFSG.pCore p (↥(GLBConj g H) ⧸ GLAPPrimeCore p ↥(GLBConj g H))
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(GLBConj g H)) (conjEquiv g H x') =
        conjQuotEquiv p g H (QuotientGroup.mk' (GLAPPrimeCore p ↥H) x') :=
      (QuotientGroup.congr_mk _ _ (conjEquiv g H) (glaPPrimeCore_map_iso p (conjEquiv g H)) x').symm
    rw [h1, ← CFSG.pCore_map_iso p (conjQuotEquiv p g H)]
    exact Subgroup.mem_map_of_mem _ hx'
  · show g⁻¹ * (x' : G) * g = z
    have : (x' : G) = g * z * g⁻¹ := hxz
    rw [this]; group

theorem oPrimePOf_gLBConj (p : ℕ) (g : G) (H : Subgroup G) :
    oPrimePOf p (GLBConj g H) = GLBConj g (oPrimePOf p H) :=
  gLBConj_eq_of_forall_ge (F := oPrimePOf p) (fun g H => oPrimePOf_gLBConj_ge p g H) g H

end Conj

section KQ2

variable {G : Type} [Group G] [Finite G]

theorem KQ2_isMaxP_top {Q : Subgroup G} {b : G} (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) (hbQ : b ∈ Q)
    (hQ : IsMaxP 3 (Subgroup.centralizer ({b} : Set G)) Q)
    (hcen : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z ^ 3 = 1 → z ∈ Subgroup.zpowers b) :
    IsMaxP 3 ⊤ Q := by
  obtain ⟨hQC, hQp, hQmax⟩ := hQ
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  have hPp : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hQeq : Q = P := by
    by_contra hne
    have hlt : Q < (P : Subgroup G) := lt_of_le_of_ne hQP hne
    have : Group.IsNilpotent ↥(P : Subgroup G) := hPp.isNilpotent
    have hltt : Q.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      rw [Subgroup.subgroupOf_eq_top] at h
      exact hne (le_antisymm hQP h) |>.elim
    have hnc := (Group.normalizerCondition_of_isNilpotent (G := ↥(P : Subgroup G))) _ hltt
    obtain ⟨x, hxN, hxQ⟩ := IsConcreteLE.exists_of_lt hnc
    rw [normalizer_subgroupOf_eq hQP] at hxN
    have hxN' : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hxN
    have hxQ' : (x : G) ∉ Q := fun h => hxQ h
    have hcb : (x : G) * b * (x : G)⁻¹ ∈ Subgroup.zpowers b := by
      refine hcen _ ?_ ?_ ?_
      · exact (Subgroup.mem_normalizer_iff.1 hxN' b).1 hbQ
      · intro q hq
        have hq' : (x : G)⁻¹ * q * (x : G) ∈ Q := by
          have := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN') q).1 hq
          simpa using this
        have hcq := Subgroup.mem_centralizer_singleton_iff.1 (hQC hq')
        calc q * ((x : G) * b * (x : G)⁻¹)
            = (x : G) * (((x : G)⁻¹ * q * (x : G)) * b) * (x : G)⁻¹ := by group
          _ = (x : G) * (b * ((x : G)⁻¹ * q * (x : G))) * (x : G)⁻¹ := by rw [← hcq]
          _ = ((x : G) * b * (x : G)⁻¹) * q := by group
      · rw [conj_pow, hb3]; group
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hPp x
    have hxo : orderOf (x : G) = 3 ^ k := by
      rw [← Subgroup.orderOf_coe x] at hk
      exact hk
    have hcomm := commute_of_conj_mem_zpowers hb3 hb1 hxo hcb
    have hxC : (x : G) ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm
    have hle : Q ⊔ Subgroup.zpowers (x : G) ≤ (P : Subgroup G) :=
      sup_le hQP (Subgroup.zpowers_le.2 x.2)
    have hp3 : IsPGroup 3 ↥(Q ⊔ Subgroup.zpowers (x : G)) := hPp.to_le hle
    have hC' : Q ⊔ Subgroup.zpowers (x : G) ≤ Subgroup.centralizer ({b} : Set G) :=
      sup_le hQC (Subgroup.zpowers_le.2 hxC)
    have := hQmax _ hC' hp3 le_sup_left
    exact hxQ' (this ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers (x : G)))
  refine ⟨le_top, hQp, fun Q' _ hQ'p hQQ' => ?_⟩
  obtain ⟨P', hQ'P'⟩ := hQ'p.exists_le_sylow
  have hcard : Nat.card (P' : Subgroup G) = Nat.card (P : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity P', Sylow.card_eq_multiplicity P]
  refine (Subgroup.eq_of_le_of_card_ge hQQ' ?_).symm
  calc Nat.card Q' ≤ Nat.card (P' : Subgroup G) := Subgroup.card_le_of_le hQ'P'
    _ = Nat.card (P : Subgroup G) := hcard
    _ = Nat.card Q := by rw [hQeq]

end KQ2

section KQ3

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem KQ3_nonInvariant (H : Hyps) (hs : Setup G m B b L) {Q : Subgroup G} (hBQ : B ≤ Q)
    (hQ : IsPGroup 3 Q) (hQC : Q ≤ Subgroup.centralizer ({b} : Set G))
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) J)
    (hJQ : ¬ Q ≤ Subgroup.normalizer (J : Set G)) : IsBConjugate B L J := by
  classical
  by_contra hnot
  set C := Subgroup.centralizer ({b} : Set G) with hCdef
  obtain ⟨L₂, L₃, ⟨g₂, hg₂, hL₂⟩, ⟨g₃, hg₃, hL₃⟩, h12, h13, h23, hall⟩ :=
    exists_three_conjugates hs.isElemAbelian.1 (hs.index_three H)
  let _inst : Fintype (Subgroup G) := Fintype.ofFinite _
  set S₀ : Finset (Subgroup G) :=
    Finset.univ.filter (fun K => GLAPComponent 3 C K ∧ ¬ Q ≤ Subgroup.normalizer (K : Set G))
    with hS₀
  have hmem : ∀ K, K ∈ S₀ ↔ GLAPComponent 3 C K ∧ ¬ Q ≤ Subgroup.normalizer (K : Set G) := by
    intro K; simp [hS₀]
  have hLmem : ∀ g ∈ B, GLBConj g L ∈ S₀ := fun g hg =>
    (hmem _).2 ⟨hs.conj_comp hg, fun h => hs.conj_not_normalizes hg (fun x hx => h (hBQ hx))⟩
  have hL1 : L ∈ S₀ := by
    have := hLmem 1 B.one_mem
    rwa [gLBConj_one] at this
  have hL2 : L₂ ∈ S₀ := hL₂ ▸ hLmem g₂ hg₂
  have hL3 : L₃ ∈ S₀ := hL₃ ▸ hLmem g₃ hg₃
  have hJmem : J ∈ S₀ := (hmem _).2 ⟨hJ, hJQ⟩
  have hJ1 : J ≠ L := fun h => hnot ⟨1, B.one_mem, by rw [gLBConj_one, h]⟩
  have hJ2 : J ≠ L₂ := fun h => hnot ⟨g₂, hg₂, h.trans hL₂⟩
  have hJ3 : J ≠ L₃ := fun h => hnot ⟨g₃, hg₃, h.trans hL₃⟩
  have h4 : 4 ≤ S₀.card := by
    have hsub : ({L, L₂, L₃, J} : Finset (Subgroup G)) ⊆ S₀ := by
      intro K hK
      simp only [Finset.mem_insert, Finset.mem_singleton] at hK
      rcases hK with rfl | rfl | rfl | rfl <;> assumption
    have hc : ({L, L₂, L₃, J} : Finset (Subgroup G)).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simpa using hJ3.symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h23, hJ2.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h12, h13, hJ1.symm⟩
    exact hc ▸ Finset.card_le_card hsub
  have h5 : S₀.card ≤ 5 :=
    C2_card_components_le_five H.ft (by rw [hs.rank4]) S₀ (fun K hK => ((hmem K).1 hK).1)
  have hconjC : ∀ q ∈ Q, GLBConj q C = C := fun q hq =>
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hQC hq))
  have hconjQ : ∀ q ∈ Q, GLBConj q Q = Q := fun q hq =>
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hq)
  have hpres : ∀ q ∈ Q, ∀ K ∈ S₀, GLBConj q⁻¹ K ∈ S₀ := by
    intro q hq K hK
    obtain ⟨hKc, hKQ⟩ := (hmem K).1 hK
    refine (hmem _).2 ⟨?_, fun h => hKQ ?_⟩
    · have := glaPComponent_gLBConj q⁻¹ hKc
      rwa [hconjC q⁻¹ (inv_mem hq)] at this
    · rw [normalizer_gLBConj] at h
      have h2 := gLBConj_mono q h
      rwa [gLBConj_gLBConj_inv, hconjQ q hq] at h2
  let act : Q → S₀ → S₀ := fun q K => ⟨GLBConj (q : G)⁻¹ K.1, hpres q q.2 K.1 K.2⟩
  let _inst2 : MulAction Q S₀ :=
    { smul := act
      one_smul := fun K => Subtype.ext (by
        show GLBConj ((1 : Q) : G)⁻¹ K.1 = K.1
        simp [gLBConj_one])
      mul_smul := fun q₁ q₂ K => Subtype.ext (by
        show GLBConj (((q₁ * q₂ : Q) : G))⁻¹ K.1 =
          GLBConj (q₁ : G)⁻¹ (GLBConj (q₂ : G)⁻¹ K.1)
        rw [gLBConj_gLBConj]
        simp [mul_inv_rev]) }
  have hfix : MulAction.fixedPoints Q S₀ = ∅ := by
    ext K
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hK
    have hKQ := ((hmem K.1).1 K.2).2
    apply hKQ
    intro q hq
    have h1 : GLBConj ((⟨q, hq⟩ : Q) : G)⁻¹ K.1 = K.1 := congrArg Subtype.val (hK ⟨q, hq⟩)
    have h2 : (q⁻¹) ∈ Subgroup.normalizer (K.1 : Set G) := mem_normalizer_iff_gLBConj_eq.2 h1
    simpa using inv_mem h2
  have hmod := (hQ.card_modEq_card_fixedPoints (α := S₀))
  rw [hfix] at hmod
  have hcardS : Nat.card S₀ = S₀.card := by simp
  have h3 : 3 ∣ S₀.card := by
    have := (Nat.modEq_zero_iff_dvd).1 (by simpa [hcardS] using hmod)
    exact this
  omega

end KQ3

section K1aHelpers

theorem K1a_mem_normalizer_layer {G : Type*} [Group G] {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  have key : GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
    refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g)
  rw [mem_normalizer_iff_gLBConj_eq, ← key, gLBConj_eq_of_mem_normalizer hg]

theorem K1a_layer_le {G : Type*} [Group G] (p : ℕ) (X : Subgroup G) : GLAPLayer p X ≤ X :=
  sSup_le fun _ hL => hL.1

theorem K1a_core {M : Type} [Group M] [Finite M] {E Kb : Subgroup M} {b0 : M}
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup M, IsElemAbelian 3 E' → E ≤ E' → E' = E)
    (hcard : Nat.card E = 3 ^ 4)
    (hEK : E ≤ Subgroup.normalizer (Kb : Set M)) (hb0 : b0 ∈ E)
    (hb0K : b0 ∉ Subgroup.centralizer (Kb : Set M))
    (hsyl : ∀ P : Subgroup M,
      IsMaxP 3 (GLAPLayer 3 (Kb ⊓ Subgroup.centralizer ({b0} : Set M))) P →
        IsElemAbelian 3 P ∧ Nat.card P = 9)
    (hZ : ∀ z ∈ GLAPLayer 3 (Kb ⊓ Subgroup.centralizer ({b0} : Set M)),
      (∀ h ∈ GLAPLayer 3 (Kb ⊓ Subgroup.centralizer ({b0} : Set M)), z * h = h * z) →
        z ^ 3 = 1 → z = 1) :
    Nat.card ↥(E ⊓ Subgroup.centralizer (Kb : Set M)) ≤ 3 := by
  set Y : Subgroup M := Kb ⊓ Subgroup.centralizer ({b0} : Set M) with hY
  set H₀ : Subgroup M := GLAPLayer 3 Y with hH₀
  have hcomm : ∀ e ∈ E, e * b0 = b0 * e := fun e he => elemAbelian_comm hE he hb0
  have hEC : E ≤ Subgroup.centralizer ({b0} : Set M) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (hcomm e he).symm
  have hEY : E ≤ Subgroup.normalizer (Y : Set M) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hEK he, Subgroup.le_normalizer (hEC he)⟩
  have hEH : E ≤ Subgroup.normalizer (H₀ : Set M) := fun e he =>
    K1a_mem_normalizer_layer (hEY he)
  have h1 := C1_card_inf_centralizer_le hE hmax hEH hsyl hZ
  set T : Subgroup M := E ⊓ Subgroup.centralizer (Kb : Set M) with hT
  have hb0T : b0 ∉ T := fun h => hb0K h.2
  have hb03 : b0 ^ 3 = 1 := hE.2 b0 hb0
  have hTc : ∀ h ∈ T, h * b0 = b0 * h := fun h hh => hcomm h hh.1
  have h2 := card_sup_zpowers_of_pow_three_eq_one hb03 hb0T hTc
  have hH₀Y : H₀ ≤ Y := K1a_layer_le 3 Y
  have hle : T ⊔ Subgroup.zpowers b0 ≤ E ⊓ Subgroup.centralizer (H₀ : Set M) := by
    refine sup_le ?_ ?_
    · refine le_inf (inf_le_left) ?_
      refine (Subgroup.centralizer_le (fun x hx => (hH₀Y.trans inf_le_left) hx)).trans' ?_
      exact inf_le_right
    · rw [Subgroup.zpowers_le]
      refine ⟨hb0, ?_⟩
      show b0 ∈ Subgroup.centralizer (H₀ : Set M)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_iff.1 (hH₀Y hh).2 b0 (Set.mem_singleton _)).symm
  have h3 := Subgroup.card_le_of_le hle
  rw [h2] at h3
  rw [hcard] at h1
  omega

end K1aHelpers

theorem K1a_le_normalizer_bClosure {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (L : Subgroup G) : B ≤ Subgroup.normalizer (bClosure B L : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have key : ∀ b ∈ B, ∀ y ∈ GLBConj b L, g * y * g⁻¹ ∈ bClosure B L := by
    intro b hb y hy
    have hb' : b * g⁻¹ ∈ B := B.mul_mem hb (B.inv_mem hg)
    have : g * y * g⁻¹ ∈ GLBConj (b * g⁻¹) L := by
      rw [mem_gLBConj] at hy ⊢
      simpa [mul_assoc] using hy
    exact le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) (b * g⁻¹) hb' this
  have hle : bClosure B L ≤ (bClosure B L).comap (MulAut.conj g).toMonoidHom :=
    iSup₂_le fun b hb y hy => by
      have := key b hb y hy
      simpa using this
  have := hle hx
  simpa using this

theorem K1a_comm_bar {G : Type*} [Group G] {C : Subgroup G} {k x : G} (hk : k ∈ C) (hx : x ∈ C)
    (h : k * x * k⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 C) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨x, hx⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨x, hx⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩ := by
  obtain ⟨r, hr, hrk⟩ := h
  have hr' : r = ⟨k, hk⟩ * ⟨x, hx⟩ * ⟨k, hk⟩⁻¹ * ⟨x, hx⟩⁻¹ := Subtype.ext (by simpa using hrk)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) r = 1 := (QuotientGroup.eq_one_iff _).2 hr
  rw [hr'] at h1
  simp only [map_mul, map_inv] at h1
  set a := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩
  set c := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨x, hx⟩
  calc a * c = (a * c * a⁻¹ * c⁻¹) * (c * a) := by group
    _ = c * a := by rw [h1, one_mul]

section K1aMain
variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem K1a_isPGroup_B (hs : Setup G m B b L) : IsPGroup 3 B := fun x =>
  ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hs.isElemAbelian.2 x x.2)⟩

theorem K1a_card_barX (hs : Setup G m B b L) :
    Nat.card (barX 3 (Subgroup.centralizer ({b} : Set G)) B) = 3 ^ 4 := by
  set C := Subgroup.centralizer ({b} : Set G)
  have hfi := injective_barX_comp Nat.prime_three (K1a_isPGroup_B hs) hs.le_centralizer
  have hrange : ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥C)).comp (B.subgroupOf C).subtype).range
      = barX 3 C B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.le_centralizer).toEquiv, hs.card_B]

theorem K1a_hinj (hs : Setup G m B b L) {y z : G} (hy : y ∈ B) (hz : z ∈ B)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))
        ⟨y, hs.le_centralizer hy⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))
        ⟨z, hs.le_centralizer hz⟩) : y = z := by
  have hfi := injective_barX_comp Nat.prime_three (K1a_isPGroup_B hs) hs.le_centralizer
  have := hfi (a₁ := ⟨⟨y, hs.le_centralizer hy⟩, (Subgroup.mem_subgroupOf).2 hy⟩)
    (a₂ := ⟨⟨z, hs.le_centralizer hz⟩, (Subgroup.mem_subgroupOf).2 hz⟩) h
  exact congrArg (fun w : ↥(B.subgroupOf (Subgroup.centralizer ({b} : Set G))) => ((w : ↥(Subgroup.centralizer ({b} : Set G))) : G)) this


theorem K1a_not_centralizes (hs : Setup G m B b L) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hb₀N : b₀ ∉ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))
        ⟨b₀, hs.le_centralizer hb₀⟩ ∉
      Subgroup.centralizer (barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L) :
        Set (↥(Subgroup.centralizer ({b} : Set G)) ⧸
          GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))) := by
  intro hcen
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hb₀C : b₀ ∈ C := hs.le_centralizer hb₀
  have hLC : L ≤ C := hs.comp.1
  have hLK : L ≤ bClosure B L := le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])
  have key : ∀ l ∈ L, ∀ (hl : l ∈ C) (hl' : b₀⁻¹ * l * b₀ ∈ C),
      π ⟨b₀⁻¹ * l * b₀, hl'⟩ = π ⟨l, hl⟩ := by
    intro l hl hlC hl'
    have hmem : π ⟨l, hlC⟩ ∈ barX 3 C (bClosure B L) :=
      ⟨⟨l, hlC⟩, (Subgroup.mem_subgroupOf).2 (hLK hl), rfl⟩
    have hc := (Subgroup.mem_centralizer_iff.1 hcen) _ hmem
    have h2 : (⟨b₀⁻¹ * l * b₀, hl'⟩ : ↥C) = ⟨b₀, hb₀C⟩⁻¹ * ⟨l, hlC⟩ * ⟨b₀, hb₀C⟩ := rfl
    rw [h2, map_mul, map_mul, map_inv]
    set u := π ⟨b₀, hb₀C⟩
    set v := π ⟨l, hlC⟩
    calc u⁻¹ * v * u = u⁻¹ * (v * u) := by rw [mul_assoc]
      _ = u⁻¹ * (u * v) := by rw [hc]
      _ = v := by rw [inv_mul_cancel_left]
  have hbar : barX 3 C (GLBConj b₀ L) = barX 3 C L := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : b₀ * (y : G) * b₀⁻¹ ∈ L := mem_gLBConj.1 ((Subgroup.mem_subgroupOf).1 hy)
      have hyC : (y : G) ∈ C := y.2
      have hlC : b₀ * (y : G) * b₀⁻¹ ∈ C := hLC hy'
      have := key _ hy' hlC (by simp [mul_assoc])
      refine ⟨⟨_, hlC⟩, (Subgroup.mem_subgroupOf).2 hy', ?_⟩
      rw [← this]
      congr 2
      simp [mul_assoc]
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ L := (Subgroup.mem_subgroupOf).1 hy
      have hyC : (y : G) ∈ C := y.2
      have hg : b₀⁻¹ * (y : G) * b₀ ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hb₀C) hyC) hb₀C
      refine ⟨⟨_, hg⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
      · rw [mem_gLBConj]
        simp [mul_assoc, hy']
      · exact key _ hy' hyC hg
  have heq : GLBConj b₀ L = L :=
    glaPComponent_uniqueAux (hs.conj_comp hb₀) hs.comp hbar
  exact hb₀N (mem_normalizer_iff_gLBConj_eq.2 heq)


theorem K1a_mem_T (hs : Setup G m B b L) {x : G} (hx : x ∈ B)
    (hcomm : ∀ k ∈ bClosure B L,
      k * x * k⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))
        ⟨x, hs.le_centralizer hx⟩ ∈
      barX 3 (Subgroup.centralizer ({b} : Set G)) B ⊓
        Subgroup.centralizer (barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L) :
          Set (↥(Subgroup.centralizer ({b} : Set G)) ⧸
            GLAPPrimeCore 3 ↥(Subgroup.centralizer ({b} : Set G)))) := by
  refine ⟨⟨⟨x, hs.le_centralizer hx⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩, ?_⟩
  show _ ∈ Subgroup.centralizer _
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ bClosure B L := (Subgroup.mem_subgroupOf).1 hk
  exact (K1a_comm_bar k.2 (hs.le_centralizer hx) (hcomm _ hk'))

theorem K1a_centralizer (H : Hyps) (hs : Setup G m B b L) :
    ∀ x ∈ B, (∀ k ∈ bClosure B L,
      k * x * k⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) →
      x ∈ Subgroup.zpowers b := by
  intro x hxB hcomm
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := hs.le_centralizer
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  obtain ⟨b₀, hb₀B, hb₀N⟩ : ∃ b₀ ∈ B, b₀ ∉ Subgroup.normalizer (L : Set G) :=
    IsConcreteLE.not_le_iff_exists.1 hs.not_normalizes
  have hb₀C : b₀ ∈ C := hBC hb₀B
  obtain ⟨hlay, hR⟩ := H.i112s G m hs.std C B L hs.isElemAbelian hBC hs.rankX hs.comp
    hs.not_normalizes hs.exc
  obtain ⟨e⟩ := hlay b₀ hb₀B hb₀N
  have hq : CFSG.Open.IsQuasisimple (barOf 3 L) := isQuasisimple_quotient_of_glaPComponent hs.comp
  obtain ⟨hsyl, hZ⟩ := C4_layer_structure hq hR e
  have hcore := K1a_core (E := barX 3 C B) (Kb := barX 3 C (bClosure B L))
    (b0 := π ⟨b₀, hb₀C⟩) (isElemAbelian_barX hs.isElemAbelian)
    (fun E' h1 h2 => eq_barX_of_isSCp Nat.prime_three hBC (hs.isSC H.l23) h1 h2)
    (K1a_card_barX hs)
    (barX_le_normalizer (K1a_le_normalizer_bClosure L))
    ⟨⟨b₀, hb₀C⟩, (Subgroup.mem_subgroupOf).2 hb₀B, rfl⟩
    (K1a_not_centralizes hs hb₀B hb₀N) hsyl hZ
  have hxT := K1a_mem_T hs hxB hcomm
  have hbC : b ∈ C := hBC hs.mem
  have hbT := K1a_mem_T hs hs.mem (fun k hk => by
    have hkC : k ∈ C := (iSup₂_le (fun g hg => (hs.conj_comp hg).1) : bClosure B L ≤ C) hk
    have hbk : b * k = k * b := Subgroup.mem_centralizer_iff.1 hkC b (Set.mem_singleton _)
    have : k * b * k⁻¹ * b⁻¹ = 1 := by
      rw [← hbk]; group
    rw [this]
    exact (GLAPPrimeCoreOf 3 C).one_mem)
  set bb := π ⟨b, hbC⟩ with hbb
  set xx := π ⟨x, hBC hxB⟩ with hxx
  have hb3 : bb ^ 3 = 1 := by
    rw [hbb, ← map_pow]
    have : (⟨b, hbC⟩ : ↥C) ^ 3 = 1 := Subtype.ext (by simpa using hs.isElemAbelian.2 b hs.mem)
    rw [this, map_one]
  have hb1 : bb ≠ 1 := by
    intro h
    have h1 : π ⟨b, hBC hs.mem⟩ = π ⟨1, hBC B.one_mem⟩ := by
      have : (⟨1, hBC B.one_mem⟩ : ↥C) = 1 := rfl
      rw [this, map_one]
      exact h
    exact hs.ne_one (K1a_hinj hs hs.mem B.one_mem h1)
  have hord : orderOf bb = 3 := orderOf_eq_prime hb3 hb1
  set T := barX 3 C B ⊓ Subgroup.centralizer (barX 3 C (bClosure B L) :
    Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) with hT
  have hzle : Subgroup.zpowers bb ≤ T := Subgroup.zpowers_le.2 hbT
  have hzcard : Nat.card (Subgroup.zpowers bb) = 3 := by rw [Nat.card_zpowers, hord]
  have hTeq : Subgroup.zpowers bb = T :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard]; exact hcore)
  have hxz : xx ∈ Subgroup.zpowers bb := by rw [hTeq]; exact hxT
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hxz
  have hbi : b ^ i ∈ B := B.zpow_mem hs.mem i
  have h1 : π ⟨b ^ i, hBC hbi⟩ = π ⟨x, hBC hxB⟩ := by
    have e1 : (⟨b ^ i, hBC hbi⟩ : ↥C) = ⟨b, hbC⟩ ^ i := Subtype.ext (by simp)
    rw [e1, map_zpow]
    exact hi
  have := K1a_hinj hs hbi hxB h1
  exact ⟨i, this⟩

end K1aMain

section K1

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem k1_R_normalizes_comp {C M : Subgroup G} (hM : GLAPComponent 3 C M) {r : G}
    (hr : r ∈ GLAPPrimeCoreOf 3 C) : r ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨r', hr', rfl⟩ := hr
  have hrC : (r' : G) ∈ C := r'.2
  have hCr : GLBConj (r' : G) C = C := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hrC)
  have hM' : GLAPComponent 3 C (GLBConj (r' : G) M) := by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj (r' : G) hM
    rwa [hCr] at this
  have hπr : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) r' = 1 := (QuotientGroup.eq_one_iff r').2 hr'
  have hbar : barX 3 C (GLBConj (r' : G) M) = barX 3 C M := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (r' : G) * (y : G) * (r' : G)⁻¹ ∈ M := mem_gLBConj.1 ((Subgroup.mem_subgroupOf).1 hy)
      have hyC : (r' : G) * (y : G) * (r' : G)⁻¹ ∈ C := hM.1 hy'
      refine ⟨⟨_, hyC⟩, (Subgroup.mem_subgroupOf).2 hy', ?_⟩
      have h2 : (⟨(r' : G) * (y : G) * (r' : G)⁻¹, hyC⟩ : ↥C) = r' * y * r'⁻¹ := rfl
      rw [h2, map_mul, map_mul, map_inv, hπr]
      simp
    · rintro ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ M := (Subgroup.mem_subgroupOf).1 hy
      have hyC : (y : G) ∈ C := y.2
      have hg : (r' : G)⁻¹ * (y : G) * (r' : G) ∈ C :=
        C.mul_mem (C.mul_mem (C.inv_mem hrC) hyC) hrC
      refine ⟨⟨_, hg⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
      · rw [mem_gLBConj]; simpa [mul_assoc] using hy'
      · have h2 : (⟨(r' : G)⁻¹ * (y : G) * (r' : G), hg⟩ : ↥C) = r'⁻¹ * y * r' := rfl
        show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) _ = _
        rw [h2, map_mul, map_mul, map_inv, hπr]
        simp
  have heq : GLBConj (r' : G) M = M := glaPComponent_uniqueAux hM' hM hbar
  exact mem_normalizer_iff_gLBConj_eq.2 heq

theorem k1_R_normalizes (hs : Setup G m B b L) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ≤
      Subgroup.normalizer (bClosure B L : Set G) := by
  intro r hr
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hle : bClosure B L ≤ (bClosure B L).comap (MulAut.conj r).toMonoidHom :=
    iSup₂_le fun g hg y hy => by
      have h1 : r * y * r⁻¹ ∈ GLBConj g L :=
        (Subgroup.mem_normalizer_iff.1 (k1_R_normalizes_comp (hs.conj_comp hg) hr) y).1 hy
      have h2 : r * y * r⁻¹ ∈ bClosure B L :=
        le_iSup₂ (f := fun b (_ : b ∈ B) => GLBConj b L) g hg h1
      simpa using h2
  have := hle hx
  simpa using this


theorem k1_comm_mem_R {C : Subgroup G} {k y : G} (hk : k ∈ C) (hy : y ∈ C)
    (h : QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨y, hy⟩ =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨y, hy⟩ * QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩) :
    k * y * k⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 3 C := by
  have hmem : (⟨k, hk⟩ * ⟨y, hy⟩ * ⟨k, hk⟩⁻¹ * ⟨y, hy⟩⁻¹ : ↥C) ∈ GLAPPrimeCore 3 ↥C := by
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) _ = 1
    simp only [map_mul, map_inv]
    set a := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨k, hk⟩
    set c := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨y, hy⟩
    rw [h]; group
  exact ⟨_, hmem, rfl⟩

theorem k1_exists_central (H : Hyps) (hs : Setup G m B b L) :
    ∃ z : ↥(barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L)),
      z ∈ Subgroup.center ↥(barX 3 (Subgroup.centralizer ({b} : Set G)) (bClosure B L)) ∧
        z ≠ 1 := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set K := bClosure B L with hK
  have hLC : L ≤ C := hs.comp.1
  have hLK : L ≤ K := le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])
  obtain ⟨-, hR⟩ := H.i112s G m hs.std C B L hs.isElemAbelian hs.le_centralizer hs.rankX hs.comp
    hs.not_normalizes hs.exc
  obtain ⟨R₀⟩ : Nonempty (Sylow 3 (barOf 3 L)) := inferInstance
  obtain ⟨hR3, hRc⟩ := hR R₀
  have hcenter : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    rw [← hRc, Subgroup.card_map_of_injective (R₀ : Subgroup (barOf 3 L)).subtype_injective]
    exact hR3.2.1
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ Subgroup.center (barOf 3 L), u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subgroup.center (barOf 3 L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [this, Subgroup.card_bot] at hcenter
    omega
  set e := quotEquivBarX Nat.prime_three hLC hs.comp.2.1 with he
  have hw : e u ∈ Subgroup.center ↥(barX 3 C L) := by
    have := Subgroup.map_center_eq e
    rw [← this]
    exact Subgroup.mem_map_of_mem _ hu
  have hw1 : e u ≠ 1 := fun h => hu1 (e.injective (by rw [h, map_one]))
  set w : ↥(barX 3 C L) := e u
  let Wsub : Subgroup G :=
    ((Subgroup.centralizer ({(w : (↥C ⧸ GLAPPrimeCore 3 ↥C))} :
      Set (↥C ⧸ GLAPPrimeCore 3 ↥C))).comap π).map C.subtype
  have hWL : ∀ g ∈ B, GLBConj g L ≤ Wsub := by
    intro g hg y hy
    have hyC : y ∈ C := (hs.conj_comp hg).1 hy
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show π ⟨y, hyC⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hgL : GLBConj g L = L
    · have hy' : y ∈ L := hgL ▸ hy
      have hmem : π ⟨y, hyC⟩ ∈ barX 3 C L := ⟨⟨y, hyC⟩, (Subgroup.mem_subgroupOf).2 hy', rfl⟩
      have h1 := Subgroup.mem_center_iff.1 hw ⟨π ⟨y, hyC⟩, hmem⟩
      exact (congrArg Subtype.val h1)
    · have hne : L ≠ GLBConj g L := fun h => hgL h.symm
      have hbar : barX 3 C L ≠ barX 3 C (GLBConj g L) := fun h =>
        hne (glaPComponent_uniqueAux hs.comp (hs.conj_comp hg) h)
      have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
        hs.comp.2.2.1 (hs.conj_comp hg).2.2.1 hbar
      have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
      have hwmem : (w : ↥C ⧸ GLAPPrimeCore 3 ↥C) ∈ barX 3 C L := w.2
      have hymem : π ⟨y, hyC⟩ ∈ barX 3 C (GLBConj g L) :=
        ⟨⟨y, hyC⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
      exact (Subgroup.mem_centralizer_iff.1 (hcen hwmem) _ hymem)
  have hKW : K ≤ Wsub := iSup₂_le fun g hg => hWL g hg
  refine ⟨⟨(w : ↥C ⧸ GLAPPrimeCore 3 ↥C), barX_mono 3 hLK w.2⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    rintro ⟨x, hx⟩
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨t', ht', htt⟩ := hKW ((Subgroup.mem_subgroupOf).1 ht)
    have htt' : t' = t := Subtype.ext htt
    subst htt'
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 ht'
    exact this
  · intro h
    apply hw1
    apply Subtype.ext
    simpa using congrArg Subtype.val h


theorem k1_normalizes_center {M : Type*} [Group M] [Finite M] {Kb : Subgroup M} {g : M}
    (hg : g ∈ Subgroup.normalizer (Kb : Set M)) :
    g ∈ Subgroup.normalizer (((Subgroup.center ↥Kb).map Kb.subtype : Subgroup M) : Set M) := by
  apply Subgroup.mem_normalizer_fintype
  rintro n ⟨c, hc, rfl⟩
  have h1 : g * (c : M) * g⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.1 hg (c : M)).1 c.2
  refine ⟨⟨_, h1⟩, ?_, rfl⟩
  refine Subgroup.mem_center_iff.2 ?_
  intro w
  apply Subtype.ext
  have hw : g⁻¹ * (w : M) * g ∈ Kb := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) (w : M)).1 w.2
    simpa using this
  have h2 := Subgroup.mem_center_iff.1 hc ⟨_, hw⟩
  have h3 : g⁻¹ * (w : M) * g * (c : M) = (c : M) * (g⁻¹ * (w : M) * g) := congrArg Subtype.val h2
  show (w : M) * (g * (c : M) * g⁻¹) = g * (c : M) * g⁻¹ * (w : M)
  calc (w : M) * (g * (c : M) * g⁻¹) = g * (g⁻¹ * (w : M) * g * (c : M)) * g⁻¹ := by group
    _ = g * ((c : M) * (g⁻¹ * (w : M) * g)) * g⁻¹ := by rw [h3]
    _ = g * (c : M) * g⁻¹ * (w : M) := by group

theorem K1_mem_bClosure (H : Hyps) (hs : Setup G m B b L) : b ∈ bClosure B L := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := hs.le_centralizer
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  set K := bClosure B L with hK
  have hKC : K ≤ C := iSup₂_le fun g hg => (hs.conj_comp hg).1
  have hbB := hs.mem
  have hbC : b ∈ C := hBC hbB
  have hb3 : b ^ 3 = 1 := hs.isElemAbelian.2 b hbB
  set Kb := barX 3 C K with hKb
  set Zb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := (Subgroup.center ↥Kb).map Kb.subtype with hZb
  have hElem : IsElemAbelian 3 (Subgroup.center ↥Kb) :=
    (H.i112 G m 3 hs.std C B L hs.isElemAbelian hBC hs.rankX hs.comp hs.not_normalizes).2.2.2.1.1
  have hZel : IsElemAbelian 3 Zb := isElemAbelian_map hElem Kb.subtype
  have hZp : IsPGroup 3 Zb := GL83.isPGroup_of_isElemAbelian hZel
  obtain ⟨z, hzc, hz1⟩ := k1_exists_central H hs
  have hZne : Zb ≠ ⊥ := by
    intro h
    apply hz1
    have : (z : ↥C ⧸ GLAPPrimeCore 3 ↥C) ∈ Zb := ⟨z, hzc, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hBel : IsElemAbelian 3 (barX 3 C B) := isElemAbelian_barX hs.isElemAbelian
  have hBp : IsPGroup 3 (barX 3 C B) := GL83.isPGroup_of_isElemAbelian hBel
  have hBN : barX 3 C B ≤ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    barX_le_normalizer (K1a_le_normalizer_bClosure L)
  have hBZ : barX 3 C B ≤ Subgroup.normalizer (Zb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    fun g hg => k1_normalizes_center (hBN hg)
  obtain ⟨z₀, hz₀Z, hz₀1, hz₀c⟩ := G1_exists_fixed Nat.prime_three hBp hZp hZne hBZ
  obtain ⟨c₀, hc₀, hc₀e⟩ := hz₀Z
  have hc₀e' : (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C) = z₀ := hc₀e
  subst hc₀e'
  have hz₀3 : (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C) ^ 3 = 1 := by
    have := hElem.2 c₀ hc₀
    exact congrArg Subtype.val this
  have hz₀B : (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C) ∈ barX 3 C B := by
    have hE := isElemAbelian_sup_zpowers (A := barX 3 C B) (x := (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C))
      hBel hz₀3 hz₀c
    have := eq_barX_of_isSCp Nat.prime_three hBC (hs.isSC H.l23) hE le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨w, hwB, hwπ⟩ := hz₀B
  set y : G := (w : G) with hy
  have hyB : y ∈ B := (Subgroup.mem_subgroupOf).1 hwB
  have hyC : y ∈ C := w.2
  have hwy : w = ⟨y, hyC⟩ := rfl
  have hycomm : ∀ k ∈ K, k * y * k⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf 3 C := by
    intro k hk
    have hkC : k ∈ C := hKC hk
    refine k1_comm_mem_R hkC hyC ?_
    have hkb : π ⟨k, hkC⟩ ∈ Kb := ⟨⟨k, hkC⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
    have h1 := Subgroup.mem_center_iff.1 hc₀ ⟨_, hkb⟩
    have h2 : π ⟨k, hkC⟩ * (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C) = (c₀ : ↥C ⧸ GLAPPrimeCore 3 ↥C) * π ⟨k, hkC⟩ :=
      congrArg Subtype.val h1
    rw [← hwπ] at h2
    exact h2
  have hyb : y ∈ Subgroup.zpowers b := K1a_centralizer H hs y hyB hycomm
  have hy1 : y ≠ 1 := by
    intro h
    apply hz₀1
    rw [← hwπ, hwy]
    have : (⟨y, hyC⟩ : ↥C) = 1 := Subtype.ext h
    rw [this, map_one]
  have hy3 : y ^ 3 = 1 := hs.isElemAbelian.2 y hyB
  have hzz : Subgroup.zpowers y = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyb) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hb3 hs.ne_one,
      orderOf_eq_prime hy3 hy1]
  have hbz : b ∈ Subgroup.zpowers y := hzz ▸ Subgroup.mem_zpowers b
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hbz
  have hbbar : π ⟨b, hbC⟩ ∈ Kb := by
    have e1 : (⟨b, hbC⟩ : ↥C) = ⟨y, hyC⟩ ^ j := Subtype.ext (by simp [hj.symm])
    rw [e1, map_zpow, ← hwy, hwπ]
    exact Subgroup.zpow_mem Kb c₀.2 j
  obtain ⟨t, ht, hte⟩ := hbbar
  have hkK : (t : G) ∈ K := (Subgroup.mem_subgroupOf).1 ht
  have hkb : (t : G)⁻¹ * b ∈ C := C.mul_mem (C.inv_mem t.2) hbC
  have hr : (t : G)⁻¹ * b ∈ GLAPPrimeCoreOf 3 C := by
    refine ⟨⟨(t : G)⁻¹ * b, hkb⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
    have h2 : (⟨(t : G)⁻¹ * b, hkb⟩ : ↥C) = t⁻¹ * ⟨b, hbC⟩ := rfl
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) _ = 1
    rw [h2, map_mul, map_inv, ← hπ, hte]
    simp
  have hbKR : b ∈ K ⊔ GLAPPrimeCoreOf 3 C := by
    have := Subgroup.mul_mem_sup hkK hr
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) := by
    have h1 : Nat.card (GLAPPrimeCoreOf 3 C) = Nat.card (GLAPPrimeCore 3 ↥C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [h1]
    exact coprime_card_gLAPPrimeCore_aux 3 ↥C
  exact G4_mem_of_mem_sup Nat.prime_three (k1_R_normalizes hs) hcop hbKR hb3

end K1

section K2Aux

theorem k2_barX_sup {G : Type*} [Group G] (p : ℕ) {C S T : Subgroup G} (hS : S ≤ C) (hT : T ≤ C) :
    barX p C (S ⊔ T) = barX p C S ⊔ barX p C T := by
  unfold barX
  rw [Subgroup.subgroupOf_sup hS hT, Subgroup.map_sup]

theorem k2_barX_conj {G : Type*} [Group G] {C A : Subgroup G} {g : G} (hg : g ∈ C) (hA : A ≤ C) :
    barX 3 C (GLBConj g A) =
      GLBConj (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hg⟩) (barX 3 C A) := by
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hAg : GLBConj g A ≤ C := by
    intro y hy
    have := mem_gLBConj.1 hy
    have h2 := C.mul_mem (C.mul_mem (C.inv_mem hg) (hA this)) hg
    simpa [mul_assoc] using h2
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : g * (w : G) * g⁻¹ ∈ A := mem_gLBConj.1 ((Subgroup.mem_subgroupOf).1 hw)
    rw [mem_gLBConj]
    refine ⟨⟨g * (w : G) * g⁻¹, hA hw'⟩, (Subgroup.mem_subgroupOf).2 hw', ?_⟩
    have h2 : (⟨g * (w : G) * g⁻¹, hA hw'⟩ : ↥C) = ⟨g, hg⟩ * w * ⟨g, hg⟩⁻¹ := rfl
    show π _ = _
    rw [h2, map_mul, map_mul, map_inv]
  · intro hx
    rw [mem_gLBConj] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have hwA : (w : G) ∈ A := (Subgroup.mem_subgroupOf).1 hw
    have hmem : g⁻¹ * (w : G) * g ∈ C := C.mul_mem (C.mul_mem (C.inv_mem hg) w.2) hg
    refine ⟨⟨_, hmem⟩, (Subgroup.mem_subgroupOf).2 ?_, ?_⟩
    · rw [mem_gLBConj]; simpa [mul_assoc] using hwA
    · have h2 : (⟨g⁻¹ * (w : G) * g, hmem⟩ : ↥C) = ⟨g, hg⟩⁻¹ * w * ⟨g, hg⟩ := rfl
      show π _ = x
      rw [h2, map_mul, map_mul, map_inv, hwx]
      group


theorem k2_mem_sup {M : Type*} [Group M] {A D : Subgroup M}
    (hc : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) {x : M} (hx : x ∈ A ⊔ D) :
    ∃ a ∈ A, ∃ d ∈ D, x = a * d := by
  have hAN : A ≤ Subgroup.normalizer (D : Set M) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : a * h = h * a := hc a ha h hh
      rw [h1]; simpa using hh
    · intro hh
      have h3 := hc a⁻¹ (A.inv_mem ha) _ hh
      have : h = a * h * a⁻¹ := by
        calc h = a⁻¹ * (a * h * a⁻¹) * a := by group
          _ = (a * h * a⁻¹) * a⁻¹ * a := by rw [h3]
          _ = a * h * a⁻¹ := by group
      rw [this]; exact hh
  have := Subgroup.coe_mul_of_left_le_normalizer_right A D hAN
  have hx' : x ∈ (↑(A ⊔ D) : Set M) := hx
  rw [this] at hx'
  obtain ⟨a, ha, d, hd, rfl⟩ := hx'
  exact ⟨a, ha, d, hd, rfl⟩


@[expose] def k2_Zs {M : Type*} [Group M] (S : Subgroup M) : Subgroup M :=
  (Subgroup.center ↥S).map S.subtype

theorem k2_mem_Zs {M : Type*} [Group M] {S : Subgroup M} {x : M} :
    x ∈ k2_Zs S ↔ x ∈ S ∧ ∀ y ∈ S, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun y hy => congrArg Subtype.val ((Subgroup.mem_center_iff.1 hc) ⟨y, hy⟩).symm⟩
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun w => ?_, rfl⟩
    exact Subtype.ext (h w w.2).symm

theorem k2_Zs_conj {M : Type*} [Group M] (u : M) (S : Subgroup M) :
    k2_Zs (GLBConj u S) = GLBConj u (k2_Zs S) := by
  ext x
  simp only [k2_mem_Zs, mem_gLBConj]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y' hy' => ?_⟩
    have := h (u⁻¹ * y' * u) (by simpa [mul_assoc] using hy')
    calc u * x * u⁻¹ * y' = u * (x * (u⁻¹ * y' * u)) * u⁻¹ := by group
      _ = u * ((u⁻¹ * y' * u) * x) * u⁻¹ := by rw [this]
      _ = y' * (u * x * u⁻¹) := by group
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := h (u * y * u⁻¹) hy
    have h2 : u * (x * y) * u⁻¹ = u * (y * x) * u⁻¹ := by
      calc u * (x * y) * u⁻¹ = (u * x * u⁻¹) * (u * y * u⁻¹) := by group
        _ = (u * y * u⁻¹) * (u * x * u⁻¹) := this
        _ = u * (y * x) * u⁻¹ := by group
    simpa using h2

theorem k2_card_Zs_conj {M : Type*} [Group M] (u : M) (S : Subgroup M) :
    Nat.card (k2_Zs (GLBConj u S)) = Nat.card (k2_Zs S) := by
  rw [k2_Zs_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj u⁻¹).injective

theorem k2_card_Zs {M : Type*} [Group M] (S : Subgroup M) :
    Nat.card (k2_Zs S) = Nat.card (Subgroup.center ↥S) :=
  Subgroup.card_map_of_injective S.subtype_injective


theorem k2_comm_of_ne {G : Type} [Group G] [Finite G] {C S T : Subgroup G}
    (hS : GLAPComponent 3 C S) (hT : GLAPComponent 3 C T) (hne : S ≠ T) :
    ∀ x ∈ barX 3 C S, ∀ y ∈ barX 3 C T, x * y = y * x := by
  have hbar : barX 3 C S ≠ barX 3 C T := fun h => hne (glaPComponent_uniqueAux hS hT h)
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
    hS.2.2.1 hT.2.2.1 hbar
  have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hcen hx) y hy).symm

theorem k2_R_normalizes_sup {G : Type} [Group G] [Finite G] {C S T : Subgroup G}
    (hS : GLAPComponent 3 C S) (hT : GLAPComponent 3 C T) {r : G}
    (hr : r ∈ GLAPPrimeCoreOf 3 C) : r ∈ Subgroup.normalizer ((S ⊔ T : Subgroup G) : Set G) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hle : S ⊔ T ≤ (S ⊔ T).comap (MulAut.conj r).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have := (Subgroup.mem_normalizer_iff.1 (k1_R_normalizes_comp hS hr) y).1 hy
      exact Subgroup.mem_sup_left (by simpa using this)
    · have := (Subgroup.mem_normalizer_iff.1 (k1_R_normalizes_comp hT hr) y).1 hy
      exact Subgroup.mem_sup_right (by simpa using this)
  have := hle hx
  simpa using this

theorem k2_card_Z1 {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G}
    {L : Subgroup G} (H : Hyps) (hs : Setup G m B b L) :
    Nat.card (k2_Zs (barX 3 (Subgroup.centralizer ({b} : Set G)) L)) = 3 := by
  set C := Subgroup.centralizer ({b} : Set G) with hC
  obtain ⟨-, hR⟩ := H.i112s G m hs.std C B L hs.isElemAbelian hs.le_centralizer hs.rankX hs.comp
    hs.not_normalizes hs.exc
  obtain ⟨R₀⟩ : Nonempty (Sylow 3 (barOf 3 L)) := inferInstance
  obtain ⟨hR3, hRc⟩ := hR R₀
  have hcenter : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    rw [← hRc, Subgroup.card_map_of_injective (R₀ : Subgroup (barOf 3 L)).subtype_injective]
    exact hR3.2.1
  set e := quotEquivBarX Nat.prime_three hs.comp.1 hs.comp.2.1 with he
  rw [k2_card_Zs, ← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact hcenter


theorem k2_comm_sup {M : Type*} [Group M] {S T : Subgroup M} {d : M}
    (hS : ∀ a ∈ S, a * d = d * a) (hT : ∀ a ∈ T, a * d = d * a) :
    ∀ a ∈ S ⊔ T, a * d = d * a := by
  have : S ⊔ T ≤ Subgroup.centralizer ({d} : Set M) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hS a ha))
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hT a ha))
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.1 (this ha)

theorem k2_Zs_sup {M : Type*} [Group M] {A₁ A₂ A₃ : Subgroup M} {x : M}
    (h₁ : ∀ a ∈ A₁, x * a = a * x) (h₂ : ∀ a ∈ A₂, x * a = a * x)
    (h₃ : ∀ a ∈ A₃, x * a = a * x) (hx : x ∈ A₁ ⊔ A₂ ⊔ A₃) : x ∈ k2_Zs (A₁ ⊔ A₂ ⊔ A₃) := by
  refine k2_mem_Zs.2 ⟨hx, fun y hy => ?_⟩
  have := k2_comm_sup (S := A₁ ⊔ A₂) (T := A₃) (d := x)
    (k2_comm_sup (fun a ha => (h₁ a ha).symm) (fun a ha => (h₂ a ha).symm)) (fun a ha => (h₃ a ha).symm) y hy
  exact this.symm

end K2Aux

section K2Main

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem K2_mem_sup (H : Hyps) (hs : Setup G m B b L) {L₂ L₃ : Subgroup G}
    (hL₂ : IsBConjugate B L L₂) (hL₃ : IsBConjugate B L L₃) (h12 : L ≠ L₂) (h13 : L ≠ L₃)
    (h23 : L₂ ≠ L₃) : b ∈ L₂ ⊔ L₃ := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := hs.le_centralizer
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hbB := hs.mem
  have hbC : b ∈ C := hBC hbB
  have hb3 : b ^ 3 = 1 := hs.isElemAbelian.2 b hbB
  have hbK := K1_mem_bClosure H hs
  have hcc := hs.conj_cases H hL₂ hL₃ h12 h13 h23
  obtain ⟨g₂, hg₂, hL₂e⟩ := hL₂
  obtain ⟨g₃, hg₃, hL₃e⟩ := hL₃
  have hLc : GLAPComponent 3 C L := hs.comp
  have hL₂c : GLAPComponent 3 C L₂ := hL₂e ▸ hs.conj_comp hg₂
  have hL₃c : GLAPComponent 3 C L₃ := hL₃e ▸ hs.conj_comp hg₃
  have hLC : L ≤ C := hLc.1
  have hL₂C : L₂ ≤ C := hL₂c.1
  have hL₃C : L₃ ≤ C := hL₃c.1
  have hK : bClosure B L = L ⊔ L₂ ⊔ L₃ := by
    refine le_antisymm (iSup₂_le fun g hg => ?_) ?_
    · rcases hcc _ ⟨g, hg, rfl⟩ with h | h | h <;> rw [h]
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])
      · exact le_iSup₂_of_le g₂ hg₂ (by rw [hL₂e])
      · exact le_iSup₂_of_le g₃ hg₃ (by rw [hL₃e])
  set A₁ := barX 3 C L with hA₁
  set A₂ := barX 3 C L₂ with hA₂
  set A₃ := barX 3 C L₃ with hA₃
  have hKb : barX 3 C (bClosure B L) = A₁ ⊔ A₂ ⊔ A₃ := by
    rw [hK, k2_barX_sup 3 (sup_le hLC hL₂C) hL₃C, k2_barX_sup 3 hLC hL₂C]
  have hc12 := k2_comm_of_ne hLc hL₂c h12
  have hc13 := k2_comm_of_ne hLc hL₃c h13
  have hc23 := k2_comm_of_ne hL₂c hL₃c h23
  have hc21 : ∀ x ∈ A₂, ∀ y ∈ A₁, x * y = y * x := fun x hx y hy => (hc12 y hy x hx).symm
  have hc31 : ∀ x ∈ A₃, ∀ y ∈ A₁, x * y = y * x := fun x hx y hy => (hc13 y hy x hx).symm
  have hc32 : ∀ x ∈ A₃, ∀ y ∈ A₂, x * y = y * x := fun x hx y hy => (hc23 y hy x hx).symm
  have hbbK : π ⟨b, hbC⟩ ∈ A₁ ⊔ A₂ ⊔ A₃ := by
    rw [← hKb]; exact ⟨⟨b, hbC⟩, (Subgroup.mem_subgroupOf).2 hbK, rfl⟩
  have hbcent : ∀ y : ↥C ⧸ GLAPPrimeCore 3 ↥C, π ⟨b, hbC⟩ * y = y * π ⟨b, hbC⟩ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥C) y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.1 w.2
    exact this.symm
  obtain ⟨y, hy, x₃, hx₃, hyx⟩ := k2_mem_sup (A := A₁ ⊔ A₂) (D := A₃)
    (fun a ha d hd => k2_comm_sup (fun a' ha' => (hc31 d hd a' ha').symm)
      (fun a' ha' => (hc32 d hd a' ha').symm) a ha) hbbK
  obtain ⟨x₁, hx₁, x₂, hx₂, hy12⟩ := k2_mem_sup (A := A₁) (D := A₂) hc12 hy
  have hbdec : π ⟨b, hbC⟩ = x₁ * x₂ * x₃ := by rw [hyx, hy12]
  have hx₁Z : x₁ ∈ k2_Zs A₁ := by
    refine k2_mem_Zs.2 ⟨hx₁, fun w hw => ?_⟩
    have h := hbcent w
    rw [hbdec] at h
    have e2 := hc21 x₂ hx₂ w hw
    have e3 := hc31 x₃ hx₃ w hw
    have : (w * x₁) * (x₂ * x₃) = (x₁ * w) * (x₂ * x₃) := by
      calc (w * x₁) * (x₂ * x₃) = w * (x₁ * x₂ * x₃) := by simp only [mul_assoc]
        _ = (x₁ * x₂ * x₃) * w := h.symm
        _ = x₁ * x₂ * (x₃ * w) := by simp only [mul_assoc]
        _ = x₁ * x₂ * (w * x₃) := by rw [e3]
        _ = x₁ * (x₂ * w) * x₃ := by simp only [mul_assoc]
        _ = x₁ * (w * x₂) * x₃ := by rw [e2]
        _ = (x₁ * w) * (x₂ * x₃) := by simp only [mul_assoc]
    exact (mul_right_cancel this).symm
  have hx₂Z : x₂ ∈ k2_Zs A₂ := by
    refine k2_mem_Zs.2 ⟨hx₂, fun w hw => ?_⟩
    have h := hbcent w
    rw [hbdec] at h
    have e1 := hc12 x₁ hx₁ w hw
    have e3 := hc32 x₃ hx₃ w hw
    have : x₁ * (x₂ * w) * x₃ = x₁ * (w * x₂) * x₃ := by
      calc x₁ * (x₂ * w) * x₃ = (x₁ * x₂ * x₃) * w := by
            calc x₁ * (x₂ * w) * x₃ = x₁ * x₂ * (w * x₃) := by simp only [mul_assoc]
              _ = x₁ * x₂ * (x₃ * w) := by rw [e3]
              _ = (x₁ * x₂ * x₃) * w := by simp only [mul_assoc]
        _ = w * (x₁ * x₂ * x₃) := h
        _ = (w * x₁) * x₂ * x₃ := by simp only [mul_assoc]
        _ = (x₁ * w) * x₂ * x₃ := by rw [← e1]
        _ = x₁ * (w * x₂) * x₃ := by simp only [mul_assoc]
    exact mul_left_cancel (mul_right_cancel this)
  have hx₃Z : x₃ ∈ k2_Zs A₃ := by
    refine k2_mem_Zs.2 ⟨hx₃, fun w hw => ?_⟩
    have h := hbcent w
    rw [hbdec] at h
    have e1 := hc13 x₁ hx₁ w hw
    have e2 := hc23 x₂ hx₂ w hw
    have : x₁ * x₂ * (x₃ * w) = x₁ * x₂ * (w * x₃) := by
      calc x₁ * x₂ * (x₃ * w) = (x₁ * x₂ * x₃) * w := by simp only [mul_assoc]
        _ = w * (x₁ * x₂ * x₃) := h
        _ = (w * x₁) * x₂ * x₃ := by simp only [mul_assoc]
        _ = (x₁ * w) * x₂ * x₃ := by rw [← e1]
        _ = x₁ * (w * x₂) * x₃ := by simp only [mul_assoc]
        _ = x₁ * (x₂ * w) * x₃ := by rw [← e2]
        _ = x₁ * x₂ * (w * x₃) := by simp only [mul_assoc]
    exact mul_left_cancel this
  set Zb := k2_Zs (A₁ ⊔ A₂ ⊔ A₃) with hZb
  have hZbcard : Nat.card Zb ≤ 9 := by
    rw [hZb, ← hKb, k2_card_Zs]
    exact (H.i112 G m 3 hs.std C B L hs.isElemAbelian hBC hs.rankX hs.comp
      hs.not_normalizes).2.2.2.1.2
  have hg₂C : g₂ ∈ C := hBC hg₂
  have hg₃C : g₃ ∈ C := hBC hg₃
  set u := π ⟨g₂, hg₂C⟩ with hu
  have hA₂u : A₂ = GLBConj u A₁ := by rw [hA₂, hL₂e]; exact k2_barX_conj hg₂C hLC
  have hA₃v : A₃ = GLBConj (π ⟨g₃, hg₃C⟩) A₁ := by rw [hA₃, hL₃e]; exact k2_barX_conj hg₃C hLC
  have hZ₁card : Nat.card (k2_Zs A₁) = 3 := k2_card_Z1 H hs
  have hZ₂card : Nat.card (k2_Zs A₂) = 3 := by rw [hA₂u, k2_card_Zs_conj]; exact hZ₁card
  have hZ₃card : Nat.card (k2_Zs A₃) = 3 := by rw [hA₃v, k2_card_Zs_conj]; exact hZ₁card
  have hZ₁le : k2_Zs A₁ ≤ Zb := by
    intro x hx
    obtain ⟨hxA, hxc⟩ := k2_mem_Zs.1 hx
    exact k2_Zs_sup (fun a ha => hxc a ha) (fun a ha => hc12 x hxA a ha) (fun a ha => hc13 x hxA a ha)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hxA))
  have hZ₂le : k2_Zs A₂ ≤ Zb := by
    intro x hx
    obtain ⟨hxA, hxc⟩ := k2_mem_Zs.1 hx
    exact k2_Zs_sup (fun a ha => hc21 x hxA a ha) (fun a ha => hxc a ha) (fun a ha => hc23 x hxA a ha)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hxA))
  have hZ₃le : k2_Zs A₃ ≤ Zb := by
    intro x hx
    obtain ⟨hxA, hxc⟩ := k2_mem_Zs.1 hx
    exact k2_Zs_sup (fun a ha => hc31 x hxA a ha) (fun a ha => hc32 x hxA a ha) (fun a ha => hxc a ha)
      (Subgroup.mem_sup_right hxA)
  have hZ₁ : k2_Zs A₁ ≤ k2_Zs A₂ ⊔ k2_Zs A₃ := by
    by_cases hZ23 : k2_Zs A₂ = k2_Zs A₃
    ·
      have hg₂3 : g₂ ^ 3 = 1 := hs.isElemAbelian.2 g₂ hg₂
      have hL₂₂ : GLBConj g₂ L₂ = L₃ := by
        have h1 : GLBConj g₂ L₂ = GLBConj (g₂ * g₂) L := by rw [hL₂e, gLBConj_gLBConj]
        rcases hcc _ ⟨g₂ * g₂, B.mul_mem hg₂ hg₂, rfl⟩ with h | h | h
        · exfalso
          have hN : g₂ * g₂ ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_iff_gLBConj_eq.2 h
          have hN2 : g₂ ∈ Subgroup.normalizer (L : Set G) := by
            have := Subgroup.mul_mem _ hN hN
            have e : g₂ * g₂ * (g₂ * g₂) = g₂ := by
              have e1 : g₂ * g₂ * (g₂ * g₂) = g₂ ^ 3 * g₂ := by
                simp only [pow_succ, pow_zero, one_mul, mul_assoc]
              rw [e1, hg₂3, one_mul]
            rwa [e] at this
          exact h12 (by rw [hL₂e]; exact (mem_normalizer_iff_gLBConj_eq.1 hN2).symm)
        · exfalso
          have : GLBConj g₂ (GLBConj g₂ L) = GLBConj g₂ L := by
            rw [← hL₂e, h1, h]
          have h3 := congrArg (GLBConj g₂⁻¹) this
          rw [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h3
          exact h12 (by rw [hL₂e]; exact h3.symm)
        · rw [h1, h]
      have hL₃₂ : GLBConj g₂ L₃ = L := by
        rw [← hL₂₂, hL₂e, gLBConj_gLBConj, gLBConj_gLBConj]
        have : g₂ * (g₂ * g₂) = 1 := by
          have e1 : g₂ * (g₂ * g₂) = g₂ ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          rw [e1, hg₂3]
        rw [this, gLBConj_one]
      have hA₃u : A₃ = GLBConj u A₂ := by rw [hA₃, ← hL₂₂]; exact k2_barX_conj hg₂C hL₂C
      have hA₁u : A₁ = GLBConj u A₃ := by rw [hA₁, ← hL₃₂]; exact k2_barX_conj hg₂C hL₃C
      have hZ₃eq : k2_Zs A₃ = GLBConj u (k2_Zs A₂) := by rw [hA₃u, k2_Zs_conj]
      have hZ₁eq : k2_Zs A₁ = GLBConj u (k2_Zs A₃) := by
        conv_lhs => rw [hA₁u]
        rw [k2_Zs_conj]
      have : k2_Zs A₁ = k2_Zs A₃ := by rw [hZ₁eq, ← hZ23, ← hZ₃eq]; exact hZ23.symm
      rw [this]; exact le_sup_right
    ·
      have hdis : ∀ x ∈ k2_Zs A₂, x ∈ k2_Zs A₃ → x = 1 := by
        intro x hx2 hx3
        by_contra hx1
        apply hZ23
        have hle : Subgroup.zpowers x ≤ k2_Zs A₂ := Subgroup.zpowers_le.2 hx2
        have hle' : Subgroup.zpowers x ≤ k2_Zs A₃ := Subgroup.zpowers_le.2 hx3
        have hx3' : x ^ 3 = 1 := by
          have := Subgroup.orderOf_dvd_natCard (k2_Zs A₂) hx2
          rw [hZ₂card] at this
          have h2 := orderOf_dvd_iff_pow_eq_one.1 this
          exact h2
        have hord : orderOf x = 3 := orderOf_eq_prime hx3' hx1
        have hcz : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hord]
        have e2 : Subgroup.zpowers x = k2_Zs A₂ :=
          Subgroup.eq_of_le_of_card_ge hle (by rw [hcz, hZ₂card])
        have e3 : Subgroup.zpowers x = k2_Zs A₃ :=
          Subgroup.eq_of_le_of_card_ge hle' (by rw [hcz, hZ₃card])
        rw [← e2, ← e3]
      have hcard9 : Nat.card ↥(k2_Zs A₂ ⊔ k2_Zs A₃) = 9 := by
        rw [C1_card_sup_of_disjoint (fun x hx y hy => (hc23 x (k2_mem_Zs.1 hx).1 y (k2_mem_Zs.1 hy).1))
          hdis, hZ₂card, hZ₃card]
      have hsupZ : k2_Zs A₂ ⊔ k2_Zs A₃ ≤ Zb := sup_le hZ₂le hZ₃le
      have heq : k2_Zs A₂ ⊔ k2_Zs A₃ = Zb :=
        Subgroup.eq_of_le_of_card_ge hsupZ (by rw [hcard9]; exact hZbcard)
      rw [heq]; exact hZ₁le
  have hbb23 : π ⟨b, hbC⟩ ∈ barX 3 C (L₂ ⊔ L₃) := by
    rw [k2_barX_sup 3 hL₂C hL₃C]
    rw [hbdec]
    have h1 : x₁ ∈ k2_Zs A₂ ⊔ k2_Zs A₃ := hZ₁ hx₁Z
    have h2 : x₂ ∈ k2_Zs A₂ ⊔ k2_Zs A₃ := Subgroup.mem_sup_left hx₂Z
    have h3 : x₃ ∈ k2_Zs A₂ ⊔ k2_Zs A₃ := Subgroup.mem_sup_right hx₃Z
    have hle : k2_Zs A₂ ⊔ k2_Zs A₃ ≤ A₂ ⊔ A₃ :=
      sup_le_sup (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
    exact hle (mul_mem (mul_mem h1 h2) h3)
  obtain ⟨t, ht, hte⟩ := hbb23
  have hkK : (t : G) ∈ L₂ ⊔ L₃ := (Subgroup.mem_subgroupOf).1 ht
  have hkb : (t : G)⁻¹ * b ∈ C := C.mul_mem (C.inv_mem t.2) hbC
  have hr : (t : G)⁻¹ * b ∈ GLAPPrimeCoreOf 3 C := by
    refine ⟨⟨(t : G)⁻¹ * b, hkb⟩, (QuotientGroup.eq_one_iff _).1 ?_, rfl⟩
    have h2 : (⟨(t : G)⁻¹ * b, hkb⟩ : ↥C) = t⁻¹ * ⟨b, hbC⟩ := rfl
    show QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) _ = 1
    rw [h2, map_mul, map_inv, ← hπ, hte]
    simp
  have hbKR : b ∈ (L₂ ⊔ L₃) ⊔ GLAPPrimeCoreOf 3 C := by
    have := Subgroup.mul_mem_sup hkK hr
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) := by
    have h1 : Nat.card (GLAPPrimeCoreOf 3 C) = Nat.card (GLAPPrimeCore 3 ↥C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [h1]
    exact coprime_card_gLAPPrimeCore_aux 3 ↥C
  exact G4_mem_of_mem_sup Nat.prime_three (fun r hr => k2_R_normalizes_sup hL₂c hL₃c hr) hcop hbKR hb3

end K2Main

section KF

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem kf_not_mem_W {J : Subgroup G} {a : G} (haJ : a ∈ J) (han : a ∉ oPrimePOf 3 J) :
    a ∉ centralizerQuot J (GLAPPrimeCoreOf 3 J) := fun h =>
  han (mem_oPrimePOf_of_forall_commutator_mem Nat.prime_three haJ fun y hy => by
    have := (GLAPPrimeCoreOf 3 J).inv_mem (h.2.2 y hy)
    simpa [mul_assoc] using this)

omit [Finite G] in
theorem kf_b_mem_W {b : G} {J : Subgroup G} (hJ : J ≤ Subgroup.centralizer ({b} : Set G)) :
    b ∈ centralizerQuot J (GLAPPrimeCoreOf 3 J) := by
  refine ⟨mem_normalizer_of_le_centralizer_singleton hJ, ?_, fun x hx => ?_⟩
  · exact mem_normalizer_of_le_centralizer_singleton
      ((Subgroup.map_subtype_le _).trans hJ)
  · have : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (hJ hx)
    have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by rw [this]; group
    rw [h2]; exact one_mem _

theorem KF_assembly (H : Hyps) (h28 : Lemma28) (h29 : Lemma29) (hs : Setup G m B b L)
    {L₂ L₃ : Subgroup G} (hL₂ : IsBConjugate B L L₂) (hL₃ : IsBConjugate B L L₃)
    (h12 : L ≠ L₂) (h13 : L ≠ L₃) (h23 : L₂ ≠ L₃)
    (hbK : b ∈ bClosure B L) (hbL : b ∈ L₂ ⊔ L₃)
    (hcore : ∀ y ∈ L₂ ⊔ L₃, orderOf y = 3 →
      b ∈ oPrimePOf 3 (Subgroup.centralizer ({y} : Set G))) :
    ∃ B' : Subgroup G, IsBZeroMax 3 B' ∧ b ∈ B' ∧ B' ≤ bClosure B L ∧
      (∀ Lᵢ : Subgroup G, IsBConjugate B L Lᵢ → ¬ B' ⊓ Lᵢ ≤ oPrimePOf 3 Lᵢ) ∧
      CFSG.Open.pRank 3 (B' ⊓ (L₂ ⊔ L₃)) = 3 ∧
      ∀ a ∈ B' ⊓ (L₂ ⊔ L₃), a ≠ 1 →
        b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hCdef
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hBel := hs.isElemAbelian
  have hBC := hs.le_centralizer
  have hCne := hs.centralizer_ne_top
  have hbB := hs.mem
  have hb1 := hs.ne_one
  have hrank : CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G := by rw [hs.pRank_B, hs.rank4]
  obtain ⟨Bs, hBsX, hBsel, hBsrank, hBsnorm, hBsJ⟩ := h29 G m hs.std B hBel hrank C hBC hCne
  have hzp : IsElemAbelian 3 (Subgroup.zpowers b) :=
    isElemAbelian_mono hBel (Subgroup.zpowers_le.2 hbB)
  have hBs_cent : Bs ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.1 (hBsX hx)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    exact (Commute.zpow_left (show Commute b x from hxb.symm) n).eq
  have hB'el : IsElemAbelian 3 (Bs ⊔ Subgroup.zpowers b) :=
    isElemAbelian_sup_of_commute hBsel hzp hBs_cent
  have hbB' : b ∈ Bs ⊔ Subgroup.zpowers b := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hbC : b ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hB'X : Bs ⊔ Subgroup.zpowers b ≤ C := sup_le hBsX (Subgroup.zpowers_le.2 hbC)
  have hB'norm : ∀ L' : Subgroup G, GLAPComponent 3 C L' →
      Bs ⊔ Subgroup.zpowers b ≤ Subgroup.normalizer (L' : Set G) := by
    intro L' hL'
    refine sup_le (hBsnorm L' hL') (Subgroup.zpowers_le.2 ?_)
    exact mem_normalizer_of_le_centralizer_singleton hL'.1
  have hB'rank : GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 (Bs ⊔ Subgroup.zpowers b) :=
    calc GLATwoLocalRank 3 G = CFSG.Open.pRank 3 B := hrank.symm
      _ ≤ CFSG.Open.pRank 3 Bs := hBsrank
      _ ≤ _ := CFSG.SectionRank.pRank_mono hp3.one_lt le_sup_left
  obtain ⟨g₂, hg₂, hL₂e⟩ := hL₂
  obtain ⟨g₃, hg₃, hL₃e⟩ := hL₃
  have hL₂c : GLAPComponent 3 C L₂ := hL₂e ▸ hs.conj_comp hg₂
  have hL₃c : GLAPComponent 3 C L₃ := hL₃e ▸ hs.conj_comp hg₃
  have hL₂n : ¬ B ≤ Subgroup.normalizer (L₂ : Set G) := hL₂e ▸ hs.conj_not_normalizes hg₂
  have hL₃n : ¬ B ≤ Subgroup.normalizer (L₃ : Set G) := hL₃e ▸ hs.conj_not_normalizes hg₃
  have hLc : GLAPComponent 3 C L := hs.comp
  obtain ⟨a₁, ha₁, ha₁n⟩ := IsConcreteLE.not_le_iff_exists.1 (hBsJ L hLc hs.not_normalizes)
  obtain ⟨a₂, ha₂, ha₂n⟩ := IsConcreteLE.not_le_iff_exists.1 (hBsJ L₂ hL₂c hL₂n)
  obtain ⟨a₃, ha₃, ha₃n⟩ := IsConcreteLE.not_le_iff_exists.1 (hBsJ L₃ hL₃c hL₃n)
  have hW₁a : a₁ ∉ centralizerQuot L (GLAPPrimeCoreOf 3 L) := kf_not_mem_W ha₁.2 ha₁n
  have hW₂a : a₂ ∉ centralizerQuot L₂ (GLAPPrimeCoreOf 3 L₂) := kf_not_mem_W ha₂.2 ha₂n
  have hW₃a : a₃ ∉ centralizerQuot L₃ (GLAPPrimeCoreOf 3 L₃) := kf_not_mem_W ha₃.2 ha₃n
  have hbW₁ := kf_b_mem_W (b := b) hLc.1
  have hbW₂ := kf_b_mem_W (b := b) hL₂c.1
  have hbW₃ := kf_b_mem_W (b := b) hL₃c.1
  have hx12 : ∀ g ∈ L₂, g ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := fun g hg =>
    mem_centralizerQuot_of_ne hp3 hLc hL₂c h12 hg
  have hx13 : ∀ g ∈ L₃, g ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := fun g hg =>
    mem_centralizerQuot_of_ne hp3 hLc hL₃c h13 hg
  have hx32 : ∀ g ∈ L₂, g ∈ centralizerQuot L₃ (GLAPPrimeCoreOf 3 L₃) := fun g hg =>
    mem_centralizerQuot_of_ne hp3 hL₃c hL₂c (Ne.symm h23) hg
  have hx23 : ∀ g ∈ L₃, g ∈ centralizerQuot L₂ (GLAPPrimeCoreOf 3 L₂) := fun g hg =>
    mem_centralizerQuot_of_ne hp3 hL₂c hL₃c h23 hg
  have hB'comm : ∀ x ∈ Bs ⊔ Subgroup.zpowers b, ∀ y ∈ Bs ⊔ Subgroup.zpowers b, x * y = y * x :=
    fun x hx y hy => elemAbelian_comm hB'el hx hy
  have hmemB' : ∀ x ∈ Bs, x ∈ Bs ⊔ Subgroup.zpowers b := fun x hx => Subgroup.mem_sup_left hx
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have ha₁3 : a₁ ^ 3 = 1 := hBsel.2 a₁ ha₁.1
  have ha₂3 : a₂ ^ 3 = 1 := hBsel.2 a₂ ha₂.1
  have ha₃3 : a₃ ^ 3 = 1 := hBsel.2 a₃ ha₃.1
  have hyx : a₂ ∉ Subgroup.zpowers b := fun h => hW₂a (Subgroup.zpowers_le.2 hbW₂ h)
  have hzxy : a₃ ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers a₂ := fun h => hW₃a
    ((sup_le (Subgroup.zpowers_le.2 hbW₃) (Subgroup.zpowers_le.2 (hx32 a₂ ha₂.2))) h)
  obtain ⟨hAel, hAcard⟩ := exists_isElemAbelian_card_three_of_independent
    (hB'comm b hbB' a₂ (hmemB' a₂ ha₂.1)) (hB'comm b hbB' a₃ (hmemB' a₃ ha₃.1))
    (hB'comm a₂ (hmemB' a₂ ha₂.1) a₃ (hmemB' a₃ ha₃.1)) hb3 ha₂3 ha₃3 hb1 hyx hzxy
  set A : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃ with hAdef
  have hAB' : A ≤ Bs ⊔ Subgroup.zpowers b :=
    sup_le (sup_le (Subgroup.zpowers_le.2 hbB') (Subgroup.zpowers_le.2 (hmemB' a₂ ha₂.1)))
      (Subgroup.zpowers_le.2 (hmemB' a₃ ha₃.1))
  have hAL : A ≤ L₂ ⊔ L₃ :=
    sup_le (sup_le (Subgroup.zpowers_le.2 hbL)
      (Subgroup.zpowers_le.2 (Subgroup.mem_sup_left ha₂.2)))
      (Subgroup.zpowers_le.2 (Subgroup.mem_sup_right ha₃.2))
  have hAW₁ : A ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) :=
    sup_le (sup_le (Subgroup.zpowers_le.2 hbW₁) (Subgroup.zpowers_le.2 (hx12 a₂ ha₂.2)))
      (Subgroup.zpowers_le.2 (hx13 a₃ ha₃.2))
  have hL23W₁ : L₂ ⊔ L₃ ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) :=
    sup_le (fun g hg => hx12 g hg) (fun g hg => hx13 g hg)
  have ha₁A : a₁ ∉ A := fun h => hW₁a (hAW₁ h)
  have ha₁L23 : a₁ ∉ L₂ ⊔ L₃ := fun h => hW₁a (hL23W₁ h)
  have hEcard : Nat.card ↥(A ⊔ Subgroup.zpowers a₁) = 3 ^ 4 := by
    rw [card_sup_zpowers_of_pow_three_eq_one ha₁3 ha₁A
      (fun h hh => hB'comm h (hAB' hh) a₁ (hmemB' a₁ ha₁.1)), hAcard]
    norm_num
  have hEB' : A ⊔ Subgroup.zpowers a₁ ≤ Bs ⊔ Subgroup.zpowers b :=
    sup_le hAB' (Subgroup.zpowers_le.2 (hmemB' a₁ ha₁.1))
  have hAEk : IsEkIn 3 3 (Bs ⊔ Subgroup.zpowers b) A := ⟨hAB', hAel, hAcard⟩
  have hNcore : ∀ x ∈ C, ∀ n ∈ GLAPPrimeCoreOf 3 C, x * n * x⁻¹ ∈ GLAPPrimeCoreOf 3 C :=
    fun x hx n hn => mem_gLAPPrimeCoreOf_conj hn hx
  have hLA : ⁅L, A⁆ ≤ GLAPPrimeCoreOf 3 C :=
    (Subgroup.commutator_mono le_rfl hAL).trans
      (commutator_sup_le_of_normalized hNcore hL₂c.1 hL₃c.1
        (commutator_le_gLAPPrimeCore_of_ne hp3 hLc hL₂c h12)
        (commutator_le_gLAPPrimeCore_of_ne hp3 hLc hL₃c h13))
  have hN2 := exists_twoGroup_normalized_of_centralizes H.ft hp3 (by norm_num) hLc
    (hAB'.trans hB'X) (GL83.isPGroup_of_isElemAbelian hAel) hLA
  have hbA : b ∈ A := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hcoreA : ∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G)) := by
    intro a ha ha1
    exact hcore a (hAL ha) (orderOf_eq_prime (hAel.2 a ha) ha1)
  have h28' := h28 G m hs.std (Bs ⊔ Subgroup.zpowers b) hB'el hB'rank b hbB' hb1 A 3 le_rfl hAEk
    hN2 hbA hcoreA (fun L' hL' => hB'norm L' hL')
  have hB'card : Nat.card ↥(Bs ⊔ Subgroup.zpowers b) = 3 ^ 4 := by
    have := h28'.1.1.2.1
    rwa [hs.rank4] at this
  have hEeq : A ⊔ Subgroup.zpowers a₁ = Bs ⊔ Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge hEB' (by rw [hB'card, hEcard])
  have hLK : L ≤ bClosure B L := le_iSup₂_of_le (1 : G) B.one_mem (by rw [gLBConj_one])
  have hL₂K : L₂ ≤ bClosure B L := le_iSup₂_of_le g₂ hg₂ (by rw [hL₂e])
  have hL₃K : L₃ ≤ bClosure B L := le_iSup₂_of_le g₃ hg₃ (by rw [hL₃e])
  refine ⟨Bs ⊔ Subgroup.zpowers b, h28'.1, hbB', ?_, ?_, ?_, ?_⟩
  · rw [← hEeq]
    refine sup_le (sup_le (sup_le (Subgroup.zpowers_le.2 hbK)
      (Subgroup.zpowers_le.2 (hL₂K ha₂.2))) (Subgroup.zpowers_le.2 (hL₃K ha₃.2)))
      (Subgroup.zpowers_le.2 (hLK ha₁.2))
  · rintro Lᵢ ⟨g, hg, rfl⟩ h
    exact hBsJ _ (hs.conj_comp hg) (hs.conj_not_normalizes hg)
      (fun y hy => h ⟨Subgroup.mem_sup_left hy.1, hy.2⟩)
  ·
    set A' : Subgroup G := (Bs ⊔ Subgroup.zpowers b) ⊓ (L₂ ⊔ L₃) with hA'
    have hAA' : A ≤ A' := le_inf hAB' hAL
    have hA'el : IsElemAbelian 3 A' := isElemAbelian_mono hB'el inf_le_left
    have hA'ne : A' ≠ Bs ⊔ Subgroup.zpowers b := by
      intro h
      apply ha₁L23
      have : a₁ ∈ A' := h ▸ hmemB' a₁ ha₁.1
      exact this.2
    have hd1 : 3 ^ 3 ∣ Nat.card A' := by
      rw [← hAcard]; exact Subgroup.card_dvd_of_le hAA'
    have hd2 : Nat.card A' ∣ 3 ^ 4 := by
      rw [← hB'card]; exact Subgroup.card_dvd_of_le inf_le_left
    have hlt : Nat.card A' < 3 ^ 4 := by
      rw [← hB'card]
      exact lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun h =>
        hA'ne (Subgroup.eq_of_le_of_card_ge inf_le_left h.ge)
    have hcA' : Nat.card A' = 3 ^ 3 := by
      obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow hp3).1 hd2
      rw [hjeq] at hd1 hlt ⊢
      have h3 : 3 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp3.one_lt).1 hd1
      have h4 : j < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
      have : j = 3 := by omega
      rw [this]
    exact pRank_eq_of_card hp3 hA'el hcA'
  · intro a ha ha1
    exact hcore a ha.2 (orderOf_eq_prime (hB'el.2 a ha.1) ha1)

end KF

section KQ1Abstract

variable {Lb : Type} [Group Lb] [Finite Lb]

theorem KQ1_conj_eq_one_iff (g : Lb) :
    (MulAut.conj g : MulAut Lb) = 1 ↔ g ∈ Subgroup.center Lb := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h x
    have := congrArg (fun σ : MulAut Lb => σ x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [← h x]; group

theorem KQ1_pCore_le_center (hq : CFSG.Open.IsQuasisimple Lb) :
    CFSG.pCore 3 Lb ≤ Subgroup.center Lb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (CFSG.pCore 3 Lb) with h | h
  · exact h
  · exfalso
    have hpg : IsPGroup 3 (⊤ : Subgroup Lb) := h ▸ CFSG.pCore_isPGroup (p := 3) (G := Lb)
    have := (hpg.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect Lb := ⟨hq.1⟩
    have : Nontrivial Lb := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable Lb inferInstance

theorem KQ1_card_le_27
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {T : Subgroup Lb} (hT : IsPGroup 3 T) : Nat.card T ≤ 27 := by
  have h := G5_card_le Nat.prime_three (le_top : T ≤ ⊤) hT
  rw [Subgroup.card_top, C4_factorization_Lb hR] at h
  simpa using h

theorem KQ1_comap_conj_isPGroup
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {P : Subgroup (MulAut Lb)} (hP : IsPGroup 3 P) :
    IsPGroup 3 (P.comap (MulAut.conj : Lb →* MulAut Lb)) := by
  intro g
  obtain ⟨n, hn⟩ := hP ⟨(MulAut.conj : Lb →* MulAut Lb) g, g.2⟩
  have h1 : (MulAut.conj : Lb →* MulAut Lb) ((g : Lb) ^ 3 ^ n) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  have h2 : (g : Lb) ^ 3 ^ n ∈ Subgroup.center Lb := (KQ1_conj_eq_one_iff _).1 h1
  have h3 : ((⟨_, h2⟩ : Subgroup.center Lb)) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center Lb) (x := ⟨_, h2⟩)
    rwa [C4_card_center hR] at this
  refine ⟨n + 1, Subtype.ext ?_⟩
  have := congrArg Subtype.val h3
  simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  show (g : Lb) ^ 3 ^ (n + 1) = 1
  rw [pow_succ, pow_mul, this]

theorem KQ1_maximal
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {Pb : Subgroup Lb} (hPb : Nat.card Pb = 27) {S : Subgroup (MulAut Lb)}
    (hPS : ∀ p ∈ Pb, (MulAut.conj p : MulAut Lb) ∈ S) :
    ∀ P : Subgroup (MulAut Lb), P ≤ innerAut Lb → IsPGroup 3 P → S ⊓ innerAut Lb ≤ P →
        P = S ⊓ innerAut Lb := by
  intro P hPin hP3 hSP
  have hPt := KQ1_comap_conj_isPGroup hR hP3
  have hle : Pb ≤ P.comap (MulAut.conj : Lb →* MulAut Lb) := fun p hp =>
    hSP ⟨hPS p hp, ⟨p, rfl⟩⟩
  have heq : Pb = P.comap (MulAut.conj : Lb →* MulAut Lb) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hPb]; exact KQ1_card_le_27 hR hPt)
  refine le_antisymm (fun σ hσ => ?_) hSP
  obtain ⟨g, rfl⟩ := hPin hσ
  have hg : g ∈ Pb := heq ▸ hσ
  exact ⟨hPS g hg, ⟨g, rfl⟩⟩

theorem KQ1_alpha_trivial (hisc : InputSylowCentreInn)
    (hexc : IsSLThreeExc Lb ∨ IsSUThreeExc Lb)
    (hR : ∀ R : Sylow 3 Lb, IsThreeOneTwo ↥(R : Subgroup Lb) ∧
      (Subgroup.center ↥(R : Subgroup Lb)).map (R : Subgroup Lb).subtype = Subgroup.center Lb)
    {Pb : Subgroup Lb} (hPb : Nat.card Pb = 27) {S : Subgroup (MulAut Lb)} (hS : IsPGroup 3 S)
    (hPS : ∀ p ∈ Pb, (MulAut.conj p : MulAut Lb) ∈ S)
    {α : MulAut Lb} (hαS : α ∈ S) (hαc : ∀ s ∈ S, α * s = s * α) (hα3 : α ^ 3 = 1)
    (hαP : ∀ p ∈ Pb, α p = p) : α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ℓ, rfl⟩ := hisc Lb hexc S hS (KQ1_maximal hR hPb hPS) α hαS hαc
  have hℓ3 : ℓ ^ 3 ∈ Subgroup.center Lb := by
    rw [← KQ1_conj_eq_one_iff, map_pow]
    exact hα3
  have hℓ9 : ℓ ^ 9 = 1 := by
    have h3 : (⟨_, hℓ3⟩ : Subgroup.center Lb) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center Lb) (x := ⟨_, hℓ3⟩)
      rwa [C4_card_center hR] at this
    have := congrArg Subtype.val h3
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, this]
  have hcomm : ∀ p ∈ Pb, ℓ * p = p * ℓ := by
    intro p hp
    have := hαP p hp
    simp only [MulAut.conj_apply] at this
    calc ℓ * p = ℓ * p * ℓ⁻¹ * ℓ := by group
      _ = p * ℓ := by rw [this]
  have hzp : IsPGroup 3 (Subgroup.zpowers ℓ) := by
    refine IsPGroup.of_card (n := Nat.log 3 (orderOf ℓ)) ?_
    rw [Nat.card_zpowers]
    have hd : orderOf ℓ ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hℓ9)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rw [hk, Nat.log_pow (by norm_num)]
  have hPbp : IsPGroup 3 Pb := IsPGroup.of_card (n := 3) (by rw [hPb]; norm_num)
  have hnorm : Pb ≤ Subgroup.normalizer (Subgroup.zpowers ℓ : Set Lb) := by
    intro p hp
    apply Subgroup.mem_normalizer_fintype
    rintro y ⟨n, rfl⟩
    have hc : Commute p ℓ := (hcomm p hp).symm
    have := (hc.zpow_right n).eq
    refine ⟨n, ?_⟩
    simp only
    rw [this]; group
  have hD : IsPGroup 3 (Pb ⊔ Subgroup.zpowers ℓ : Subgroup Lb) :=
    hPbp.to_sup_of_normal_right' hzp hnorm
  have hDeq : Pb = Pb ⊔ Subgroup.zpowers ℓ :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hPb]; exact KQ1_card_le_27 hR hD)
  have hℓP : ℓ ∈ Pb := by
    rw [hDeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ℓ)
  let Rs : Sylow 3 Lb := Sylow.ofCard Pb (by
    rw [hPb, C4_factorization_Lb hR]; norm_num)
  have hcen := (hR Rs).2
  have hℓR : ℓ ∈ (Rs : Subgroup Lb) := hℓP
  have hmem : ℓ ∈ (Subgroup.center ↥(Rs : Subgroup Lb)).map (Rs : Subgroup Lb).subtype := by
    refine ⟨⟨ℓ, hℓR⟩, Subgroup.mem_center_iff.2 ?_, rfl⟩
    intro r
    exact Subtype.ext (hcomm r r.2).symm
  rw [hcen] at hmem
  exact (KQ1_conj_eq_one_iff ℓ).2 hmem

end KQ1Abstract

section KQ1Main

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem KQ1_hR (H : Hyps) (hs : Setup G m B b L) :
    ∀ R : Sylow 3 (barOf 3 L), IsThreeOneTwo ↥(R : Subgroup (barOf 3 L)) ∧
      (Subgroup.center ↥(R : Subgroup (barOf 3 L))).map (R : Subgroup (barOf 3 L)).subtype =
        Subgroup.center (barOf 3 L) :=
  (H.i112s G m hs.std (Subgroup.centralizer ({b} : Set G)) B L hs.isElemAbelian hs.le_centralizer
    hs.rankX hs.comp hs.not_normalizes hs.exc).2

theorem KQ1_card_bar {P : Subgroup G} (hP : IsMaxP 3 L P) (hL : (Nat.card L).factorization 3 = 3) :
    Nat.card ((P.subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup ↥L := P.subgroupOf L with hT
  have hT3 : IsPGroup 3 T := hP.2.1.comap_subtype (K := L)
  have hTcard : Nat.card T = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv,
      G3_card_of_isMaxP Nat.prime_three hP, hL]
    norm_num
  set f : ↥T →* barOf 3 L := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp T.subtype with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (x : ↥L) ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT3 x
    have h1 : orderOf (x : ↥L) = 3 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
    have h2 := Subgroup.orderOf_dvd_natCard _ hx'
    rw [h1] at h2
    have h3 : 3 ^ k = 1 :=
      Nat.Coprime.eq_one_of_dvd ((coprime_card_gLAPPrimeCore_aux 3 ↥L).pow_left k) h2
    rw [h3, orderOf_eq_one_iff] at h1
    exact Subtype.ext h1
  have hmap : (T.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hTcard]


theorem KQ1_mem_B (H : Hyps) (hs : Setup G m B b L) {Q : Subgroup G} (hBQ : B ≤ Q)
    {z : G} (hzc : ∀ q ∈ Q, q * z = z * q) (hz3 : z ^ 3 = 1) : z ∈ B := by
  have hE := isElemAbelian_sup_zpowers (A := B) (x := z) hs.isElemAbelian hz3
    (fun a ha => hzc a (hBQ ha))
  have := (hs.isSC H.l23).2.2 _ le_top hE le_sup_left
  rw [← this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem KQ1_mem_normalizer (H : Hyps) (hs : Setup G m B b L) {Q : Subgroup G}
    (hQ : IsMaxP 3 (Subgroup.centralizer ({b} : Set G)) Q)
    {z : G} (hzB : z ∈ B) (hzc : ∀ q ∈ Q, q * z = z * q) :
    z ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hn
  have hL' : GLBConj z L ≠ L := fun h => hn (mem_normalizer_iff_gLBConj_eq.2 h)
  have hcomp' := hs.conj_comp hzB
  have hPmax : IsMaxP 3 L (Q ⊓ L) :=
    G5_isMaxP_inf_of_isSubnormal Nat.prime_three hs.comp.2.1 hQ
  have hle : Q ⊓ L ≤ oPrimePOf 3 L := by
    intro y hy
    refine inf_le_oPrimePOf_of_ne Nat.prime_three hs.comp hcomp' (Ne.symm hL') ⟨hy.2, mem_gLBConj.2 ?_⟩
    have := hzc y hy.1
    rw [← this]; group; exact hy.2
  have hq := isQuasisimple_quotient_of_glaPComponent hs.comp
  have hcard := KQ1_card_bar hPmax (Kord_factorization_card H hs)
  have hPb : ((Q ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) ≤
      Subgroup.center (barOf 3 L) := by
    rintro _ ⟨x, hx, rfl⟩
    apply KQ1_pCore_le_center hq
    obtain ⟨u, hu, hux⟩ := hle (Subgroup.mem_subgroupOf.1 hx)
    have : u = x := Subtype.ext hux
    subst this
    exact hu
  have h1 := Subgroup.card_le_of_le hPb
  rw [hcard, C4_card_center (KQ1_hR H hs)] at h1
  omega


theorem KQ1_barAut_apply (L : Subgroup G) (γ : G) (hγ : γ ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) (hx : γ * (x : G) * γ⁻¹ ∈ L) :
    barAut 3 L ⟨γ, hγ⟩ (QuotientGroup.mk x) = QuotientGroup.mk ⟨γ * (x : G) * γ⁻¹, hx⟩ := by
  rw [barAut_mk]
  rfl

theorem KQ1_barAut_conj (L : Subgroup G) (y : G) (hy : y ∈ L)
    (hγ : y ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨y, hγ⟩ = MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥L) : barOf 3 L) := by
  ext x
  induction x using QuotientGroup.induction_on with | H x => ?_
  rw [barAut_mk]
  simp only [MulAut.conj_apply]
  rfl

theorem KQ1_barAut_trivial (H : Hyps) (hs : Setup G m B b L) {Q : Subgroup G}
    (hQ : IsMaxP 3 (Subgroup.centralizer ({b} : Set G)) Q)
    {z : G} (hzQ : z ∈ Q) (hzc : ∀ q ∈ Q, q * z = z * q) (hz3 : z ^ 3 = 1)
    (hzN : z ∈ Subgroup.normalizer (L : Set G)) :
    barAut 3 L ⟨z, hzN⟩ = 1 := by
  have hPmax : IsMaxP 3 L (Q ⊓ L) :=
    G5_isMaxP_inf_of_isSubnormal Nat.prime_three hs.comp.2.1 hQ
  have hcard := KQ1_card_bar hPmax (Kord_factorization_card H hs)
  set Pb := ((Q ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)) with hPbdef
  let φ : ↥(Q ⊓ Subgroup.normalizer (L : Set G)) →* MulAut (barOf 3 L) :=
    (barAut 3 L).comp (Subgroup.inclusion inf_le_right)
  have hQ3 : IsPGroup 3 ↥(Q ⊓ Subgroup.normalizer (L : Set G)) := hQ.2.1.to_le inf_le_left
  have hS : IsPGroup 3 φ.range :=
    hQ3.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hφz : barAut 3 L ⟨z, hzN⟩ = φ ⟨z, hzQ, hzN⟩ := rfl
  refine KQ1_alpha_trivial H.isc hs.exc (KQ1_hR H hs) hcard hS ?_ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hxQ : (x : G) ∈ Q := (Subgroup.mem_subgroupOf.1 hx).1
    have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer x.2
    refine ⟨⟨(x : G), hxQ, hxN⟩, ?_⟩
    exact KQ1_barAut_conj L x x.2 hxN
  · exact ⟨⟨z, hzQ, hzN⟩, hφz.symm⟩
  · rintro _ ⟨q, rfl⟩
    rw [hφz, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc q q.2.1).symm
  · have : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hz3)
    rw [← map_pow, this, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    have hxQ : (x : G) ∈ Q := (Subgroup.mem_subgroupOf.1 hx).1
    have hzx : z * (x : G) * z⁻¹ = x := by
      rw [← hzc x hxQ]; group
    have hxz : z * (x : G) * z⁻¹ ∈ L := by rw [hzx]; exact x.2
    show barAut 3 L ⟨z, hzN⟩ (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [KQ1_barAut_apply L z hzN x hxz]
    congr 1
    exact Subtype.ext hzx


theorem KQ1_comm_mem_R (hs : Setup G m B b L) {z : G} (hzB : z ∈ B)
    (hL : ∀ x ∈ L, z * x * z⁻¹ * x⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) :
    ∀ k ∈ bClosure B L, k * z * k⁻¹ * z⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  classical
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hzC : z ∈ C := hs.le_centralizer hzB
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  let W : Subgroup G :=
    ((Subgroup.centralizer ({π ⟨z, hzC⟩} : Set (↥C ⧸ GLAPPrimeCore 3 ↥C))).comap π).map C.subtype
  have hKW : bClosure B L ≤ W := by
    refine iSup₂_le fun g hg y hy => ?_
    have hyC : y ∈ C := (hs.conj_comp hg).1 hy
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show π ⟨y, hyC⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine K1a_comm_bar hyC hzC ?_
    have hgz : g * z = z * g := elemAbelian_comm hs.isElemAbelian hg hzB
    have hgz' : g⁻¹ * z * g = z := by rw [mul_assoc, ← hgz]; group
    have hgC : g ∈ C := hs.le_centralizer hg
    have hx := hL _ (mem_gLBConj.1 hy)
    have hx' := mem_gLAPPrimeCoreOf_conj (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hgC)
    have e : g⁻¹ * ((z * (g * y * g⁻¹) * z⁻¹ * (g * y * g⁻¹)⁻¹)⁻¹) * g⁻¹⁻¹ =
        y * (g⁻¹ * z * g) * y⁻¹ * (g⁻¹ * z * g)⁻¹ := by group
    rw [e, hgz'] at hx'
    exact hx'
  intro k hk
  obtain ⟨k', hk', rfl⟩ := hKW hk
  exact k1_comm_mem_R k'.2 hzC (Subgroup.mem_centralizer_singleton_iff.1 hk')

theorem KQ1_center (H : Hyps) (hs : Setup G m B b L) {Q : Subgroup G} (hBQ : B ≤ Q)
    (hQ : IsMaxP 3 (Subgroup.centralizer ({b} : Set G)) Q) :
    ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z ^ 3 = 1 → z ∈ Subgroup.zpowers b := by
  intro z hzQ hzc hz3
  have hzB := KQ1_mem_B H hs hBQ hzc hz3
  have hzN := KQ1_mem_normalizer H hs hQ hzB hzc
  have hα := KQ1_barAut_trivial H hs hQ hzQ hzc hz3 hzN
  have hL : ∀ x ∈ L, z * x * z⁻¹ * x⁻¹ ∈
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    intro x hx
    have hxz : z * x * z⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hzN x).1 hx
    have h1 := congrArg (fun σ => σ (QuotientGroup.mk (⟨x, hx⟩ : ↥L))) hα
    simp only [MulAut.one_apply] at h1
    rw [KQ1_barAut_apply L z hzN ⟨x, hx⟩ hxz] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).1 h1
    have h3 : z * x * z⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf 3 L := ⟨_, h2, by simp [div_eq_mul_inv]⟩
    exact glaPPrimeCoreOf_le_of_isSubnormal 3 hs.comp.2.1 h3
  exact K1a_centralizer H hs z hzB (KQ1_comm_mem_R hs hzB hL)

end KQ1Main

section KC

variable {G : Type} [Group G] [Finite G] {m : ℕ} {B : Subgroup G} {b : G} {L : Subgroup G}

theorem kc_exists_sylow {B C : Subgroup G} (hBC : B ≤ C) (hB : IsPGroup 3 B) :
    ∃ Q : Subgroup G, B ≤ Q ∧ IsMaxP 3 C Q := by
  have hB' : IsPGroup 3 (B.subgroupOf C) := by
    obtain ⟨k, hk⟩ := hB.exists_card_eq
    exact IsPGroup.iff_card.2 ⟨k, by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv]; exact hk⟩
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  refine ⟨(S : Subgroup C).map C.subtype, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hBC hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · refine G3'_isMaxP_of_card Nat.prime_three (Subgroup.map_subtype_le _) (S.isPGroup'.map C.subtype) ?_
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Sylow.card_eq_multiplicity S

theorem kc_conj_of_isMaxP_top {Q₁ Q : Subgroup G} (h₁ : IsMaxP 3 ⊤ Q₁) (h : IsMaxP 3 ⊤ Q) :
    ∃ c : G, GLBConj c Q₁ = Q := by
  let P₁ : Sylow 3 G := ⟨Q₁, h₁.2.1, fun {Q'} hQ' hle => h₁.2.2 Q' le_top hQ' hle⟩
  let P : Sylow 3 G := ⟨Q, h.2.1, fun {Q'} hQ' hle => h.2.2 Q' le_top hQ' hle⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₁ P
  refine ⟨g⁻¹, ?_⟩
  have h2 : ((g • P₁ : Sylow 3 G) : Subgroup G) = (P : Subgroup G) := congrArg _ hg
  rw [Sylow.coe_subgroup_smul] at h2
  ext x
  rw [mem_gLBConj]
  have h3 : x ∈ (P : Subgroup G) ↔ (MulAut.conj g)⁻¹ • x ∈ (P₁ : Subgroup G) := by
    rw [← h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have h4 : x ∈ Q ↔ g⁻¹ * x * g ∈ Q₁ := by
    have := h3
    simpa [MulAut.smul_def, MulAut.conj_apply, MulAut.inv_apply] using this
  rw [h4]
  simp

theorem KC_core_of_conj (H : Hyps) {b₁ : G} {J : Subgroup G} (hs : Setup G m B b L)
    (hs₁ : Setup G m B b₁ J)
    (h27 : ∀ Jᵢ Jⱼ : Subgroup G, IsBConjugate B J Jᵢ → IsBConjugate B J Jⱼ →
      ∀ x ∈ Jᵢ ⊔ Jⱼ, orderOf x = 3 →
        b₁ ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)))
    {L₂ L₃ : Subgroup G} (hL₂ : IsBConjugate B L L₂) (hL₃ : IsBConjugate B L L₃)
    (h12 : L ≠ L₂) (h13 : L ≠ L₃) (h23 : L₂ ≠ L₃) :
    ∀ y ∈ L₂ ⊔ L₃, orderOf y = 3 →
      b ∈ oPrimePOf 3 (Subgroup.centralizer ({y} : Set G)) := by
  classical
  intro y hy hy3
  obtain ⟨Q, hBQ, hQ⟩ := kc_exists_sylow hs.le_centralizer
    (GL83.isPGroup_of_isElemAbelian hs.isElemAbelian)
  obtain ⟨Q₁, hBQ₁, hQ₁⟩ := kc_exists_sylow hs₁.le_centralizer
    (GL83.isPGroup_of_isElemAbelian hs₁.isElemAbelian)
  have hcen := KQ1_center H hs hBQ hQ
  have hcen₁ := KQ1_center H hs₁ hBQ₁ hQ₁
  have hb3 : b ^ 3 = 1 := hs.isElemAbelian.2 b hs.mem
  have hb₁3 : b₁ ^ 3 = 1 := hs₁.isElemAbelian.2 b₁ hs₁.mem
  have hQtop := KQ2_isMaxP_top hs.ne_one hb3 (hBQ hs.mem) hQ hcen
  have hQ₁top := KQ2_isMaxP_top hs₁.ne_one hb₁3 (hBQ₁ hs₁.mem) hQ₁ hcen₁
  obtain ⟨c, hc⟩ := kc_conj_of_isMaxP_top hQ₁top hQtop
  set β : G := c⁻¹ * b₁ * c with hβ
  have hβQ : β ∈ Q := by
    rw [← hc, mem_gLBConj]
    have : c * β * c⁻¹ = b₁ := by rw [hβ]; group
    rw [this]; exact hBQ₁ hs₁.mem
  have hβcen : ∀ q ∈ Q, q * β = β * q := by
    intro q hq
    rw [← hc, mem_gLBConj] at hq
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hQ₁.1 hq)
    calc q * β = c⁻¹ * ((c * q * c⁻¹) * b₁) * c := by rw [hβ]; group
      _ = c⁻¹ * (b₁ * (c * q * c⁻¹)) * c := by rw [← h1]
      _ = β * q := by rw [hβ]; group
  have hβ3 : β ^ 3 = 1 := by
    have h1 : β ^ 3 = c⁻¹ * b₁ ^ 3 * c := by
      have := conj_pow (a := c⁻¹) (b := b₁) (i := 3)
      simpa [hβ] using this
    rw [h1, hb₁3]; group
  have hβ1 : β ≠ 1 := by
    intro h; apply hs₁.ne_one
    have : b₁ = c * β * c⁻¹ := by rw [hβ]; group
    rw [this, h]; group
  have hβb : β ∈ Subgroup.zpowers b := hcen β hβQ hβcen hβ3
  have hzz : Subgroup.zpowers β = Subgroup.zpowers b := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hβb) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hb3 hs.ne_one,
      orderOf_eq_prime hβ3 hβ1]
  have hbβ : b ∈ Subgroup.zpowers β := hzz ▸ Subgroup.mem_zpowers b
  have hCβ : Subgroup.centralizer ({β} : Set G) = Subgroup.centralizer ({b} : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hzz,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨J₂, J₃, ⟨k₂, hk₂, hJ₂e⟩, ⟨k₃, hk₃, hJ₃e⟩, hJ12, hJ13, hJ23, hallJ⟩ :=
    exists_three_conjugates hs₁.isElemAbelian.1 (hs₁.index_three H)
  have hcases := hs.conj_cases H hL₂ hL₃ h12 h13 h23
  have hφ : ∀ J', IsBConjugate B J J' → IsBConjugate B L (GLBConj c J') := by
    rintro J' ⟨h, hh, rfl⟩
    have hcomp1 : GLAPComponent 3 (Subgroup.centralizer ({b₁} : Set G)) (GLBConj h J) :=
      hs₁.conj_comp hh
    have hcomp2 : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G))
        (GLBConj c (GLBConj h J)) := by
      have := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj c hcomp1
      rwa [← centralizer_singleton_gLBConj c b₁, hCβ] at this
    have hnn : ¬ Q ≤ Subgroup.normalizer (GLBConj c (GLBConj h J) : Set G) := by
      intro hQN
      apply hs₁.conj_not_normalizes hh
      intro x hx
      have hxQ₁ := hBQ₁ hx
      rw [normalizer_gLBConj] at hQN
      have h2 := gLBConj_mono c⁻¹ hQN
      have e1 : GLBConj c⁻¹ Q = Q₁ := by rw [← hc, gLBConj_inv_gLBConj]
      rw [e1, gLBConj_inv_gLBConj] at h2
      exact h2 hxQ₁
    exact KQ3_nonInvariant H hs hBQ hQ.2.1 hQ.1 hcomp2 hnn
  have hJmem : ∀ J' ∈ ({J, J₂, J₃} : Finset (Subgroup G)), IsBConjugate B J J' := by
    intro J' hJ'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hJ'
    rcases hJ' with rfl | rfl | rfl
    · exact ⟨1, B.one_mem, (gLBConj_one _).symm⟩
    · exact ⟨k₂, hk₂, hJ₂e⟩
    · exact ⟨k₃, hk₃, hJ₃e⟩
  have hsub : ({J, J₂, J₃} : Finset (Subgroup G)).image (GLBConj c) ⊆
      ({L, L₂, L₃} : Finset (Subgroup G)) := by
    intro K hK
    obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.1 hK
    have := hcases _ (hφ J' (hJmem J' hJ'))
    simpa using this
  have hinj : Function.Injective (GLBConj c : Subgroup G → Subgroup G) := fun A A' h => by
    have := congrArg (GLBConj c⁻¹) h
    rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at this
  have hcardJ : ({J, J₂, J₃} : Finset (Subgroup G)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hJ23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hJ12, hJ13⟩
  have hcardL : ({L, L₂, L₃} : Finset (Subgroup G)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using h23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h12, h13⟩
  have hEq : ({J, J₂, J₃} : Finset (Subgroup G)).image (GLBConj c) =
      ({L, L₂, L₃} : Finset (Subgroup G)) :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [Finset.card_image_of_injective _ hinj, hcardJ, hcardL])
  have hL₂mem : L₂ ∈ ({J, J₂, J₃} : Finset (Subgroup G)).image (GLBConj c) := by
    rw [hEq]; simp
  have hL₃mem : L₃ ∈ ({J, J₂, J₃} : Finset (Subgroup G)).image (GLBConj c) := by
    rw [hEq]; simp
  obtain ⟨J', hJ', hJ'e⟩ := Finset.mem_image.1 hL₂mem
  obtain ⟨J'', hJ'', hJ''e⟩ := Finset.mem_image.1 hL₃mem
  have hyc : c * y * c⁻¹ ∈ J' ⊔ J'' := by
    have : y ∈ GLBConj c (J' ⊔ J'') := by
      have e : GLBConj c (J' ⊔ J'') = GLBConj c J' ⊔ GLBConj c J'' := Subgroup.map_sup _ _ _
      rw [e, hJ'e, hJ''e]; exact hy
    exact mem_gLBConj.1 this
  have hxo : orderOf (c * y * c⁻¹) = 3 := by
    have := orderOf_injective (MulAut.conj c : G ≃* G).toMonoidHom (MulAut.conj c).injective y
    rw [← hy3]
    simpa [MulAut.conj_apply] using this
  have h27' := h27 J' J'' (hJmem _ hJ') (hJmem _ hJ'') (c * y * c⁻¹) hyc hxo
  have hCx : GLBConj c (Subgroup.centralizer ({c * y * c⁻¹} : Set G)) =
      Subgroup.centralizer ({y} : Set G) := by
    have := centralizer_singleton_gLBConj c (c * y * c⁻¹)
    rw [show c⁻¹ * (c * y * c⁻¹) * c = y by group] at this
    exact this.symm
  have hβmem : β ∈ oPrimePOf 3 (Subgroup.centralizer ({y} : Set G)) := by
    rw [← hCx, oPrimePOf_gLBConj, mem_gLBConj]
    have : c * β * c⁻¹ = b₁ := by rw [hβ]; group
    rw [this]; exact h27'
  exact Subgroup.zpowers_le.2 hβmem hbβ

end KC

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210Ns


namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma210Ns

theorem lemma210_bClosure_ne {G : Type} [Group G] [Finite G] {B J : Subgroup G}
    (h : ¬ B ≤ Subgroup.normalizer (J : Set G)) : bClosure B J ≠ J := by
  intro hJ
  apply h
  intro g hg
  have hle : GLBConj g J ≤ J :=
    (le_iSup₂_of_le (f := fun b (_ : b ∈ B) => GLBConj b J) g hg le_rfl).trans hJ.le
  have hcard : Nat.card J ≤ Nat.card (GLBConj g J) := by
    unfold GLBConj
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have := Subgroup.eq_of_le_of_card_ge hle hcard
  exact mem_normalizer_iff_gLBConj_eq.2 this

theorem lemma210_of_lemmas (hFT : InputFeitThompson) (h23 : Lemma23) (_h24 : Lemma24)
    (h26 : Lemma26Plus) (h27 : Lemma27) (h28 : Lemma28) (h29 : Lemma29)
    (h112 : Input11_2Full) (h112s : Lemma210Ns.Input11_2Struct)
    (hsc : Lemma210Ns.InputSylowCentreInn) : Lemma210 := by
  intro G _ _ m hS h4 B hB b hbB hb1 L hLc hexc hK L₂ L₃ hL₂ hL₃ h12 h13 h23'
  have H : Lemma210Ns.Hyps := ⟨hFT, h23, h112, h112s, hsc⟩
  have hs : Lemma210Ns.Setup G m B b L := ⟨hS, h4, hB, hbB, hb1, hLc, hexc, hK⟩
  have hbK := Lemma210Ns.K1_mem_bClosure H hs
  have hbL := Lemma210Ns.K2_mem_sup H hs hL₂ hL₃ h12 h13 h23'
  have hcore : ∀ y ∈ L₂ ⊔ L₃, orderOf y = 3 →
      b ∈ oPrimePOf 3 (Subgroup.centralizer ({y} : Set G)) := by
    by_cases hwb : IsWeaklyBalancedWrt 3 2 B
    · intro y hy hy3
      have hSL : IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L) := by
        rcases hexc with ⟨K, f, fin, -, e⟩ | ⟨K, f, fin, q, hq, -, e⟩
        · exact Or.inl ⟨K, f, fin, e⟩
        · exact Or.inr ⟨K, f, fin, q, hq, e⟩
      exact h27 G m hS B hB b hbB hb1 L hLc hs.not_normalizes hbK
        (Or.inr ⟨h4, hSL, Lemma210Ns.Kord_factorization_card H hs, hwb⟩) L₂ L₃ hL₂ hL₃ y hy hy3
    · obtain ⟨D, b₁, J, hset, hconc, hbK₁, hcen, -⟩ := h26 G m hS B hB hwb
      have hnot : ¬ B ≤ Subgroup.normalizer (J : Set G) := not_le_normalizer_of_relIndex_eq_three hconc.1
      have hs₁ : Lemma210Ns.Setup G m B b₁ J :=
        ⟨hS, h4, hB, hset.mem, hset.ne_one, hset.isComp, hconc.2.1, lemma210_bClosure_ne hnot⟩
      refine Lemma210Ns.KC_core_of_conj H hs hs₁ ?_ hL₂ hL₃ h12 h13 h23'
      intro Jᵢ Jⱼ hi hj x hx ho
      exact h27 G m hS B hB b₁ hset.mem hset.ne_one J hset.isComp hnot hbK₁
        (Or.inl ⟨D, hset, hconc, hcen⟩) Jᵢ Jⱼ hi hj x hx ho
  exact Lemma210Ns.KF_assembly H h28 h29 hs hL₂ hL₃ h12 h13 h23' hbK hbL hcore

end CFSG.HardMathSupport.Solomon.LocalBalance
