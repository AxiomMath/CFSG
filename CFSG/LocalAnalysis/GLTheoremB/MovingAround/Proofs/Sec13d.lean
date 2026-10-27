module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff)
open scoped MatrixGroups

@[expose] def InputPiCenter : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → IsPiGroup p X → ¬ IsHatSeven X →
    Subgroup.center X = ⊥

@[expose] def InputAbIdx2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ m : ℕ, (m ≤ 2 ∨ 5 ≤ m) ∧ IsAltType m X) ∨
      (∃ m : ℕ, Nonempty (X ≃* Equiv.Perm (Fin m))) ∨
      (∃ n : ℕ, Nonempty (X ≃* ↥(StatedSp n (ZMod 2)))) ∨
      (∃ (ε : Bool) (n : ℕ), 2 ≤ n ∧ IsOmegaTwo ε n X)) →
    ∃ j : ℕ, Subgroup.index (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ : Subgroup X) = 2 ^ j

@[expose] def Lemma137_noA7Statement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) {L : Subgroup G}, GLAPComponent p (Istar p M D) L → p = 3 →
      ¬ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin 7))

namespace Sec13d

section PiCore

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCore_eq_pCore_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (hpi : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L)) :
    GLAPPrimeCore p ↥L = CFSG.pCore 2 ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcop2 : Nat.Coprime p (Nat.card ↥(CFSG.pCore 2 ↥L)) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hle1 : CFSG.pCore 2 ↥L ≤ GLAPPrimeCore p ↥L :=
    CFSG.le_pPrimeCore_of_normal_coprime (CFSG.pCore_normal (p := 2) (G := ↥L)) hcop2
  refine le_antisymm (fun x hx => ?_) hle1
  set f : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hf
  haveI : ((GLAPPrimeCore p ↥L).map f).Normal :=
    Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  have hdvd : Nat.card ↥((GLAPPrimeCore p ↥L).map f) ∣ Nat.card ↥(GLAPPrimeCore p ↥L) :=
    Subgroup.card_map_dvd (GLAPPrimeCore p ↥L) f
  have hcopY : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥L).map f)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => not_dvd_card_pPrimeCore hp L (h.trans hdvd)
  have hsub := CFSG.le_pPrimeCore_of_normal_coprime inferInstance hcopY
  have hbot : GLAPPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := hpi.2.1
  have h1 : f x ∈ (⊥ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    (hsub.trans hbot.le) (Subgroup.mem_map_of_mem f hx)
  rw [Subgroup.mem_bot] at h1
  exact (QuotientGroup.eq_one_iff x).1 h1

end PiCore

section Helpers

variable {G : Type} [Group G]

theorem conj_mem_derivedInf {H : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ derivedInf H) :
    b * x * b⁻¹ ∈ derivedInf H := by
  let σ : ↥H →* ↥H := (H.normalizerMonoidHom ⟨b, hb⟩ : MulAut ↥H).toMonoidHom
  have hσ : ∀ y : ↥H, ((σ y : ↥H) : G) = b * (y : G) * b⁻¹ := fun y => rfl
  rw [derivedInf, Subgroup.mem_iInf] at hx ⊢
  intro n
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hx n)
  refine Subgroup.mem_map.2 ⟨σ y, map_derivedSeries_le_derivedSeries σ n
    (Subgroup.mem_map_of_mem σ hy), ?_⟩
  rw [← hyx]
  exact hσ y

theorem derivedInf_le (H : Subgroup G) : derivedInf H ≤ H := by
  intro x hx
  have h0 := (Subgroup.mem_iInf.1 hx) 0
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 h0
  exact y.2

theorem mem_of_pow_eq_one_of_pow_mem {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g : Γ} {m n : ℕ}
    (hcop : Nat.Coprime m n) (hm : g ^ m = 1) (hn : g ^ n ∈ H) : g ∈ H := by
  have hb : (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [Nat.Coprime.gcd_eq_one hcop] at h
    exact_mod_cast h.symm
  have key : g = (g ^ (m : ℤ)) ^ Nat.gcdA m n * (g ^ (n : ℤ)) ^ Nat.gcdB m n := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, hb, zpow_one]
  have hm' : g ^ (m : ℤ) = 1 := by rw [zpow_natCast]; exact hm
  have hn' : g ^ (n : ℤ) ∈ H := by rw [zpow_natCast]; exact hn
  rw [key, hm', one_zpow, one_mul]
  exact H.zpow_mem hn' _

end Helpers

theorem mem_of_index_coprime {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.Normal] {g : Γ} {m : ℕ}
    (hm : g ^ m = 1) (hcop : Nat.Coprime m H.index) : g ∈ H :=
  mem_of_pow_eq_one_of_pow_mem hcop hm (H.pow_index_mem g)

section Clause

variable {G : Type} [Group G] [Finite G]

theorem mem_derivedInf_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {N L : Subgroup G} {x : G}
    (hKc : barX p N (derivedInf (N ⊓ L)) = ⁅barX p N (N ⊓ L), barX p N (N ⊓ L)⁆)
    (hidx : ∃ j : ℕ, Subgroup.index (⁅(⊤ : Subgroup ↥(barX p N (N ⊓ L))),
      (⊤ : Subgroup ↥(barX p N (N ⊓ L)))⁆ : Subgroup ↥(barX p N (N ⊓ L))) = 2 ^ j)
    (hxN : x ∈ N) (hxL : x ∈ L) (hxp : x ^ p = 1) : x ∈ derivedInf (N ⊓ L) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := hidx
  have hxJ : x ∈ N ⊓ L := Subgroup.mem_inf.2 ⟨hxN, hxL⟩
  have hgJ : (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ : ↥N ⧸ GLAPPrimeCore p ↥N) ∈
      barX p N (N ⊓ L) := (mem_barX_iff p _).2 ⟨⟨x, hxN⟩, hxJ, rfl⟩
  let g : ↥(barX p N (N ⊓ L)) := ⟨_, hgJ⟩
  have hxNp : (⟨x, hxN⟩ : ↥N) ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ : ↥N ⧸ GLAPPrimeCore p ↥N) ^ p = 1
    rw [← map_pow, hxNp, map_one]
  have hcop2 : Nat.Coprime p (2 ^ j) :=
    Nat.Coprime.pow_right j ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hgC : g ∈ (⁅(⊤ : Subgroup ↥(barX p N (N ⊓ L))),
      (⊤ : Subgroup ↥(barX p N (N ⊓ L)))⁆ : Subgroup ↥(barX p N (N ⊓ L))) :=
    mem_of_index_coprime _ hgp (by rw [hj]; exact hcop2)
  have htop : (⊤ : Subgroup ↥(barX p N (N ⊓ L))).map (barX p N (N ⊓ L)).subtype =
      barX p N (N ⊓ L) := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hK' : (QuotientGroup.mk' (GLAPPrimeCore p ↥N) ⟨x, hxN⟩ : ↥N ⧸ GLAPPrimeCore p ↥N) ∈
      barX p N (derivedInf (N ⊓ L)) := by
    rw [hKc]
    have hmap := Subgroup.mem_map_of_mem (barX p N (N ⊓ L)).subtype hgC
    rw [Subgroup.map_commutator, htop] at hmap
    exact hmap
  obtain ⟨k, hkK, hk⟩ := (mem_barX_iff p _).1 hK'
  have hk' : (k⁻¹ * ⟨x, hxN⟩ : ↥N) ∈ GLAPPrimeCore p ↥N := QuotientGroup.eq.1 hk
  set s : G := ((k⁻¹ * ⟨x, hxN⟩ : ↥N) : G) with hs
  have hsx : x = (k : G) * s := by
    rw [hs]; simp
  have hkJ : (k : G) ∈ N ⊓ L := derivedInf_le _ hkK
  have hsJ : s ∈ N ⊓ L := by
    rw [hs]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (N ⊓ L).mul_mem ((N ⊓ L).inv_mem hkJ) hxJ
  set e : ℕ := Nat.card ↥(GLAPPrimeCore p ↥N) with he
  have hpe : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_pPrimeCore hp N)
  have hse : s ^ e = 1 := by
    have hy : (⟨k⁻¹ * ⟨x, hxN⟩, hk'⟩ : ↥(GLAPPrimeCore p ↥N)) ^ e = 1 := pow_card_eq_one'
    have h2 := congrArg (fun z : ↥(GLAPPrimeCore p ↥N) => ((z : ↥N) : G)) hy
    simpa [hs] using h2
  have hpow : ∀ n : ℕ, ∃ κ ∈ derivedInf (N ⊓ L), x ^ n = κ * s ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, (derivedInf (N ⊓ L)).one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨κ, hκ, hxn⟩ := ih
      have hsn : s ^ n ∈ Subgroup.normalizer ((N ⊓ L : Subgroup G) : Set G) :=
        Subgroup.le_normalizer ((N ⊓ L).pow_mem hsJ n)
      have hconj : s ^ n * (k : G) * (s ^ n)⁻¹ ∈ derivedInf (N ⊓ L) :=
        conj_mem_derivedInf hsn hkK
      refine ⟨κ * (s ^ n * (k : G) * (s ^ n)⁻¹), (derivedInf (N ⊓ L)).mul_mem hκ hconj, ?_⟩
      rw [pow_succ, hxn, hsx]
      group
  obtain ⟨κ, hκ, hxe⟩ := hpow e
  have hxe' : x ^ e ∈ derivedInf (N ⊓ L) := by
    rw [hxe, hse, mul_one]
    exact hκ
  exact mem_of_pow_eq_one_of_pow_mem hpe hxp hxe'

theorem mem_normalizer_inf_of {H1 H2 : Subgroup G} {c : G}
    (h1 : c ∈ Subgroup.normalizer (H1 : Set G)) (h2 : c ∈ Subgroup.normalizer (H2 : Set G)) :
    c ∈ Subgroup.normalizer ((H1 ⊓ H2 : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (h1 y) (h2 y)

theorem mem_normalizer_derivedInf {J : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (J : Set G)) :
    b ∈ Subgroup.normalizer ((derivedInf J : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_derivedInf hb hy
  · intro hy
    have hb' : b⁻¹ ∈ Subgroup.normalizer (J : Set G) := (Subgroup.normalizer (J : Set G)).inv_mem hb
    have := conj_mem_derivedInf hb' hy
    have e : b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this

theorem mem_centBar_iff {p : ℕ} {X L : Subgroup G} {c : G} :
    c ∈ centBar p X L ↔ c ∈ X ∧ ∃ γ : ↥(Subgroup.normalizer (L : Set G)), (γ : G) = c ∧
      barAut p L γ = 1 := by
  unfold centBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨γ, hγ, hγc⟩, hcX⟩
    exact ⟨hcX, γ, hγc, (MonoidHom.mem_ker).1 hγ⟩
  · rintro ⟨hcX, γ, hγc, hγ⟩
    exact ⟨⟨γ, (MonoidHom.mem_ker).2 hγ, hγc⟩, hcX⟩

theorem le_glaPPrimeCore_of_normal_coprime {p : ℕ} [Fact p.Prime] {K Y : Subgroup G} (hYK : Y ≤ K)
    (hY : (Y.subgroupOf K).Normal) (hcop : Nat.Coprime p (Nat.card Y)) :
    (Y.subgroupOf K) ≤ GLAPPrimeCore p ↥K := by
  have hc : Nat.Coprime p (Nat.card (Y.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYK).toEquiv]
    exact hcop
  exact CFSG.le_pPrimeCore_of_normal_coprime hY hc

theorem centBar_mono_of_normalizer {p : ℕ} (hp : p.Prime) [Fact p.Prime] {X L K : Subgroup G}
    (hKL : K ≤ L) {c : G} (hc : c ∈ centBar p X L)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) : c ∈ centBar p X K := by
  obtain ⟨hcX, γ, hγc, hγ⟩ := mem_centBar_iff.1 hc
  subst hγc
  rw [mem_centBar_iff]
  refine ⟨hcX, ⟨_, hcK⟩, rfl, ?_⟩
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.one_apply, barAut_mk]
  have hxL : (x : G) ∈ L := hKL x.2
  have hcx : (γ : G) * (x : G) * (γ : G)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hcK (x : G)).1 x.2
  have hwK : ((γ : G) * (x : G) * (γ : G)⁻¹)⁻¹ * (x : G) ∈ K := K.mul_mem (K.inv_mem hcx) x.2
  have hγx : barAut p L γ (QuotientGroup.mk (⟨x, hxL⟩ : ↥L)) = QuotientGroup.mk ⟨x, hxL⟩ := by
    rw [hγ, MulAut.one_apply]
  rw [barAut_mk] at hγx
  have hmem := QuotientGroup.eq.1 hγx
  have hwO : ((γ : G) * (x : G) * (γ : G)⁻¹)⁻¹ * (x : G) ∈ GLAPPrimeCoreOf p L :=
    (mem_gLAPPrimeCoreOf_iff p L _).2 ⟨_, hmem⟩
  have hYn : ((K ⊓ GLAPPrimeCoreOf p L).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    obtain ⟨hnK, hnO⟩ := hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨K.mul_mem (K.mul_mem g.2 hnK) (K.inv_mem g.2), ?_⟩
    exact conj_mem_glaPPrimeCoreOf p (Subgroup.le_normalizer (hKL g.2)) hnO
  have hcop : Nat.Coprime p (Nat.card ↥(K ⊓ GLAPPrimeCoreOf p L)) := by
    have hdvd : Nat.card ↥(K ⊓ GLAPPrimeCoreOf p L) ∣ Nat.card ↥(GLAPPrimeCoreOf p L) :=
      Subgroup.card_dvd_of_le inf_le_right
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      not_dvd_card_glaPPrimeCoreOf hp L (h.trans hdvd)
  have hsub := le_glaPPrimeCore_of_normal_coprime (p := p) (K := K) (Y := K ⊓ GLAPPrimeCoreOf p L)
    inf_le_left hYn hcop
  have hkey : ((γ : G) * (x : G) * (γ : G)⁻¹)⁻¹ * (x : G) ∈ K ⊓ GLAPPrimeCoreOf p L :=
    Subgroup.mem_inf.2 ⟨hwK, hwO⟩
  have hw : (K.normalizerMonoidHom ⟨_, hcK⟩ x)⁻¹ * x =
      (⟨((γ : G) * (x : G) * (γ : G)⁻¹)⁻¹ * (x : G), hwK⟩ : ↥K) :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rfl)
  rw [QuotientGroup.eq, hw]
  exact hsub (Subgroup.mem_subgroupOf.2 hkey)

theorem isOmegaTwo_of_mulEquiv {ε : Bool} {n : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsOmegaTwo ε n Y) : IsOmegaTwo ε n X := by
  cases ε with
  | true => obtain ⟨f⟩ := h; exact ⟨e.trans f⟩
  | false => obtain ⟨f⟩ := h; exact ⟨e.trans f⟩

theorem index_pow_two_of_piType {p : ℕ} (hPi : InputPiCenter) (hAb : InputAbIdx2) (hp : p.Prime)
    (hp2 : p ≠ 2) {X J : Type} [Group X] [Finite X] [Group J] [Finite J]
    (hpi : IsPiGroup p X) (hnh : ¬ IsHatSeven X)
    (hA7 : p = 3 → ¬ Nonempty (X ≃* alternatingGroup (Fin 7)))
    (hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) X →
      (IsOmegaTwo ε (n + 1) J ∨ Nonempty (J ≃* ↥(StatedSp n (ZMod 2)))))
    (hA : ∀ k : ℕ, IsAltType (k * p + 2) X →
      (IsAltType (k * p + 2) J ∨ Nonempty (J ≃* Equiv.Perm (Fin (k * p))))) :
    ∃ j : ℕ, Subgroup.index (⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ : Subgroup J) = 2 ^ j := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hZ : Subgroup.center X = ⊥ := hPi X p hp hp2 hpi hnh
  have hY : (X ⧸ Subgroup.center X) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  obtain ⟨-, -, hcases⟩ := hpi
  rcases hcases with ⟨k, ⟨e⟩⟩ | ⟨n, ε, hn, hΩX, -⟩ | ⟨h3, ⟨e⟩⟩
  · have hAX : IsAltType (k * p + 2) X := ⟨hY.symm.trans e⟩
    have hk : k * p + 2 ≤ 2 ∨ 5 ≤ k * p + 2 := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · left; simp [h0]
      · right
        have : 1 * 3 ≤ k * p := Nat.mul_le_mul h0 hp3
        omega
    rcases hA k hAX with hJ | ⟨f⟩
    · exact hAb J (Or.inl ⟨k * p + 2, hk, hJ⟩)
    · exact hAb J (Or.inr (Or.inl ⟨k * p, f⟩))
  · have hΩX' : IsOmegaTwo ε (n + 1) X := isOmegaTwo_of_mulEquiv hY.symm hΩX
    rcases hΩ ε n hΩX' with hJ | ⟨f⟩
    · exact hAb J (Or.inr (Or.inr (Or.inr ⟨ε, n + 1, by omega, hJ⟩)))
    · exact hAb J (Or.inr (Or.inr (Or.inl ⟨n, f⟩)))
  · exact (hA7 h3 ⟨hY.symm.trans e⟩).elim

end Clause

end Sec13d

open Sec13d

theorem lemma137_v_of_inputs (hL133 : Lemma133Statement) (hL137i : Lemma137_iStatement)
    (hL137ii : Lemma137_ii_iiiStatement) (hPi : InputPiCenter) (hAb : InputAbIdx2)
    (hNo7 : Lemma137_noA7Statement) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T : Subgroup G}
      (h : Sec13 G m p B M E A D T) {L : Subgroup G}
      (hL : GLAPComponent p (Istar p M D) L) (hL1 : 3 < p ∨ 2 ≤ CFSG.Open.pRank p L),
      (B = (B ⊓ L) ⊔ centBar p B L ∧ (B ⊓ L) ⊓ centBar p B L = ⊥) ∧
      (B = (B ⊓ derivedInf (Nof T ⊓ L)) ⊔ centBar p B (derivedInf (Nof T ⊓ L)) ∧
        CFSG.Open.pRank p (B ⊓ derivedInf (Nof T ⊓ L)) =
          CFSG.Open.pRank p (derivedInf (Nof T ⊓ L))) := by
  intro G _ _ m p B M E A D T h L hL hL1
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have h133 := (hL133 h).2 L hL
  have hBN : B ≤ Nof T := hL137i h
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have h137 := hL137ii h hL hL1
  have hΩ : ∀ (ε : Bool) (n : ℕ), IsOmegaTwo ε (n + 1) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsOmegaTwo ε (n + 1) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* ↥(StatedSp n (ZMod 2)))) := by
    intro ε n hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.1 ε n hX).1 hc)
    · exact Or.inr ((h137.2.2.2.1 ε n hX).2 hc)
  have hA : ∀ k : ℕ, IsAltType (k * p + 2) (↥L ⧸ CFSG.pCore 2 ↥L) →
      (IsAltType (k * p + 2) ↥(barX p (Nof T) (Nof T ⊓ L)) ∨
        Nonempty (↥(barX p (Nof T) (Nof T ⊓ L)) ≃* Equiv.Perm (Fin (k * p)))) := by
    intro k hX
    by_cases hc : barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact Or.inl ((h137.2.2.2.2 k hX).1 hc)
    · exact Or.inr ((h137.2.2.2.2 k hX).2 hc)
  have hidx := index_pow_two_of_piType hPi hAb hp hp2 h133.1.2.1 h133.1.2.2
    (fun h3 => hNo7 h hL h3) hΩ hA
  have hBK : B ⊓ L ≤ derivedInf (Nof T ⊓ L) := by
    intro x hx
    obtain ⟨hxB, hxL⟩ := Subgroup.mem_inf.1 hx
    exact mem_derivedInf_of_pow_eq_one hp hp2 h137.1 hidx (hBN hxB) hxL (hBel.2 x hxB)
  have hKL : derivedInf (Nof T ⊓ L) ≤ L := (derivedInf_le _).trans inf_le_right
  have hcJ : ∀ c ∈ centBar p B L, c ∈ Subgroup.normalizer ((Nof T ⊓ L : Subgroup G) : Set G) := by
    intro c hc
    obtain ⟨hcB, γ, hγc, -⟩ := mem_centBar_iff.1 hc
    subst hγc
    exact mem_normalizer_inf_of (Subgroup.le_normalizer (hBN hcB)) γ.2
  have hcent : centBar p B L ≤ centBar p B (derivedInf (Nof T ⊓ L)) := by
    intro c hc
    exact centBar_mono_of_normalizer hp hKL hc (mem_normalizer_derivedInf (hcJ c hc))
  have hBsub : B ≤ (B ⊓ derivedInf (Nof T ⊓ L)) ⊔ centBar p B (derivedInf (Nof T ⊓ L)) := by
    have hle : B ⊓ L ≤ B ⊓ derivedInf (Nof T ⊓ L) := fun x hx =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hBK hx⟩
    have := sup_le_sup hle hcent
    rw [← h133.2.2.1] at this
    exact this
  have hsup : (B ⊓ derivedInf (Nof T ⊓ L)) ⊔ centBar p B (derivedInf (Nof T ⊓ L)) ≤ B :=
    sup_le inf_le_left (fun c hc => (mem_centBar_iff.1 hc).1)
  have hpart2 : B = (B ⊓ derivedInf (Nof T ⊓ L)) ⊔ centBar p B (derivedInf (Nof T ⊓ L)) :=
    le_antisymm hBsub hsup
  have heq : B ⊓ derivedInf (Nof T ⊓ L) = B ⊓ L :=
    le_antisymm (inf_le_inf_left B hKL) (fun x hx =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hBK hx⟩)
  have hrank : CFSG.Open.pRank p (B ⊓ derivedInf (Nof T ⊓ L)) =
      CFSG.Open.pRank p (derivedInf (Nof T ⊓ L)) := by
    have hBKr : CFSG.Open.pRank p (B ⊓ derivedInf (Nof T ⊓ L)) ≤
        CFSG.Open.pRank p (derivedInf (Nof T ⊓ L)) :=
      CFSG.SectionRank.pRank_mono hp1 inf_le_right
    apply le_antisymm hBKr
    rw [heq, h133.2.2.2.2]
    exact CFSG.SectionRank.pRank_mono hp1 hKL
  exact ⟨⟨h133.2.2.1, h133.2.2.2.1⟩, hpart2, hrank⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
