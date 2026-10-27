module

public import CFSG.GroupTheory.SteinbergCBHHBTheoremB

public section

namespace CFSG.HardMathSupport.Dickson.I271

section LinAlg

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem sq_eq_zero_of_isNilpotent (hV : Module.finrank F V = 2) {N : Module.End F V}
    (hN : IsNilpotent N) : N ^ 2 = 0 := by
  have h := (LinearMap.isNilpotent_iff_charpoly N).1 hN
  rw [hV] at h
  have h2 := LinearMap.aeval_self_charpoly N
  rw [h] at h2
  simpa using h2

theorem exists_eq_add_smul_of_commute (hV : Module.finrank F V = 2) {N : Module.End F V}
    (hN0 : N ≠ 0) (hN2 : N ^ 2 = 0) {t : Module.End F V} (ht : t * N = N * t) :
    ∃ α β : F, t = α • (1 : Module.End F V) + β • N := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, N v ≠ 0 := by
    by_contra h
    push Not at h
    exact hN0 (LinearMap.ext h)
  have hNN : N (N v) = 0 := by
    have := congrArg (fun f : Module.End F V => f v) hN2
    simpa [pow_two] using this
  have hli : LinearIndependent F ![v, N v] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 : a • N v = 0 := by
      have := congrArg N hab
      simpa [hNN] using this
    have ha : a = 0 := by
      by_contra ha
      exact hv ((smul_eq_zero.1 h1).resolve_left ha)
    subst ha
    simp only [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.1 hab).resolve_right hv⟩
  have hspan : Submodule.span F (Set.range ![v, N v]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [hV])
  have hmem : t v ∈ Submodule.span F (Set.range ![v, N v]) := by rw [hspan]; trivial
  have hrange : Set.range ![v, N v] = {v, N v} := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  rw [hrange, Submodule.mem_span_pair] at hmem
  obtain ⟨α, β, hαβ⟩ := hmem
  refine ⟨α, β, ?_⟩
  have hs : (t - α • (1 : Module.End F V) - β • N) = 0 := by
    apply LinearMap.ext_on (s := Set.range ![v, N v]) hspan
    intro x hx
    rw [hrange] at hx
    rcases hx with h | h
    · rw [h]
      simp [← hαβ]
    · rw [h]
      have h1 : t (N v) = N (t v) := by
        have := congrArg (fun f : Module.End F V => f v) ht
        simpa using this
      simp [h1, ← hαβ, hNN]
  have := sub_eq_zero.1 (by simpa [sub_sub] using hs)
  simpa using this

theorem pow_add_smul_of_sq_eq_zero {N : Module.End F V} (hN2 : N ^ 2 = 0) (α β : F) (n : ℕ) :
    (α • (1 : Module.End F V) + β • N) ^ (n + 1) =
      α ^ (n + 1) • (1 : Module.End F V) + (((n + 1 : ℕ) : F) * α ^ n * β) • N := by
  have hNN : N * N = 0 := by rwa [pow_two] at hN2
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hNN,
      smul_zero, add_zero, smul_smul]
    push_cast
    module

variable {p : ℕ}

theorem coeff_eq_zero_of_pow_eq_one [CharP F p] (hV : Module.finrank F V = 2) {N : Module.End F V}
    (hN0 : N ≠ 0) (hN2 : N ^ 2 = 0) {α β : F} {m : ℕ} (hm : 0 < m) (hpm : ¬ p ∣ m)
    (h : (α • (1 : Module.End F V) + β • N) ^ m = 1) : β = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [pow_add_smul_of_sq_eq_zero hN2] at h
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hV]; norm_num)
  have hnot : ∀ c d : F, c • N = d • (1 : Module.End F V) → c = 0 ∧ d = 0 := by
    intro c d hcd
    by_cases hc : c = 0
    · subst hc
      refine ⟨rfl, ?_⟩
      simp only [zero_smul] at hcd
      by_contra hd
      have := congrArg (fun f : Module.End F V => f (Classical.choose (exists_ne (0 : V)))) hcd
      simp only [LinearMap.zero_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      have hne := Classical.choose_spec (exists_ne (0 : V))
      exact hne ((smul_eq_zero.1 this.symm).resolve_left hd)
    · exfalso
      have hNe : N = (d / c) • (1 : Module.End F V) := by
        have := congrArg (fun f : Module.End F V => c⁻¹ • f) hcd
        simpa [smul_smul, hc, div_eq_inv_mul] using this
      have h2 : (d / c) ^ 2 • (1 : Module.End F V) = 0 := by
        rw [← hN2, hNe, smul_pow, one_pow]
      have hdc : (d / c) ^ 2 = 0 := by
        by_contra hne
        have := congrArg (fun f : Module.End F V => f (Classical.choose (exists_ne (0 : V)))) h2
        simp only [LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at this
        exact Classical.choose_spec (exists_ne (0 : V)) ((smul_eq_zero.1 this).resolve_left hne)
      have : d / c = 0 := pow_eq_zero_iff (by norm_num) |>.1 hdc
      apply hN0
      rw [hNe, this, zero_smul]
  have h1 : (((n + 1 : ℕ) : F) * α ^ n * β) • N = (1 - α ^ (n + 1)) • (1 : Module.End F V) := by
    rw [sub_smul, one_smul, eq_sub_iff_add_eq, add_comm]
    exact h
  obtain ⟨hc0, hd0⟩ := hnot _ _ h1
  have hα : α ^ (n + 1) = 1 := by linear_combination -hd0
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  have hn0 : ((n + 1 : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F p]
    exact hpm
  rcases mul_eq_zero.1 hc0 with h' | h'
  · rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd h'' hn0
    · exact absurd h'' (pow_ne_zero n hα0)
  · exact h'

theorem exists_smul_one_of_commute [CharP F p] (hV : Module.finrank F V = 2) {N : Module.End F V}
    (hN0 : N ≠ 0) (hN2 : N ^ 2 = 0) {t : (Module.End F V)ˣ} (hp : ¬ p ∣ orderOf t)
    (ht : (t : Module.End F V) * N = N * (t : Module.End F V)) :
    ∃ c : F, (t : Module.End F V) = c • (1 : Module.End F V) := by
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_smul_of_commute hV hN0 hN2 ht
  have hpos : 0 < orderOf t := by
    rcases Nat.eq_zero_or_pos (orderOf t) with h | h
    · exact absurd (by rw [h]; exact dvd_zero p) hp
    · exact h
  have hpow : (α • (1 : Module.End F V) + β • N) ^ orderOf t = 1 := by
    rw [← hαβ, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hβ := coeff_eq_zero_of_pow_eq_one hV hN0 hN2 hpos hp hpow
  exact ⟨α, by rw [hαβ, hβ, zero_smul, add_zero]⟩

end LinAlg

section PSolv

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem isPSolvable_of_normal_index_dvd {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hidx : N.index ∣ p) : CFSG.HallHigman.IsPSolvable p G := by
  classical
  intro H _ T hT hs
  set M : Subgroup ↥H := N.subgroupOf H with hM
  haveI : M.Normal := inferInstance
  set f : ↥H →* ↥H ⧸ T := QuotientGroup.mk' T with hf
  have hfs : Function.Surjective f := QuotientGroup.mk'_surjective T
  haveI : (M.map f).Normal := Subgroup.Normal.map inferInstance f hfs
  have hMidx : M.index ∣ p := (Subgroup.relIndex_dvd_index_of_normal (H := N) (K := H)).trans hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map f) with hbot | htop
  ·
    have hMT : M ≤ T := by
      have := (Subgroup.map_eq_bot_iff M).1 hbot
      rwa [hf, QuotientGroup.ker_mk'] at this
    have hdvd : T.index ∣ p := (Subgroup.index_dvd_of_le hMT).trans hMidx
    rcases (Nat.dvd_prime hp.out).1 hdvd with h1 | h1
    · exfalso
      have : Subsingleton (↥H ⧸ T) := by
        rw [Subgroup.index_eq_one] at h1
        subst h1
        exact Subsingleton.intro fun a b => by
          obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
          obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
          exact (QuotientGroup.eq.2 (Subgroup.mem_top _))
      exact not_subsingleton _ this
    · exact Or.inl h1
  ·
    right
    have hsurj : Function.Surjective (f.comp M.subtype) := by
      intro q
      have hq : q ∈ M.map f := by rw [htop]; trivial
      obtain ⟨m, hm, rfl⟩ := hq
      exact ⟨⟨m, hm⟩, rfl⟩
    have h1 : Nat.card (↥H ⧸ T) ∣ Nat.card M := Subgroup.card_dvd_of_surjective hsurj
    have h2 : Nat.card M ∣ Nat.card N := by
      let g : ↥M →* ↥N :=
        { toFun := fun m => ⟨((m : ↥H) : G), Subgroup.mem_subgroupOf.1 m.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hginj : Function.Injective g := by
        intro a b h
        have h' : (((a : ↥H) : G)) = (((b : ↥H) : G)) := congrArg (fun z : ↥N => (z : G)) h
        exact Subtype.ext (Subtype.ext h')
      exact Subgroup.card_dvd_of_injective g hginj
    rw [← Subgroup.index_eq_card] at h1
    exact Nat.Coprime.coprime_dvd_right (h1.trans h2) ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)

theorem piCore_eq_bot_or_commute {N : Subgroup G} [N.Normal] (hN : ¬ p ∣ Nat.card N)
    (hidx : N.index ∣ p) {x : G} (hxp : x ^ p = 1) :
    CFSG.piCore {q : Nat.Primes | q.val = p} G = ⊥ ∨ ∀ n ∈ N, n * x = x * n := by
  classical
  by_cases hP : CFSG.piCore {q : Nat.Primes | q.val = p} G = ⊥
  · exact Or.inl hP
  right
  set P : Subgroup G := CFSG.piCore {q : Nat.Primes | q.val = p} G with hPdef
  haveI : P.Normal := inferInstance
  have hset : {q : Nat.Primes | q.val = p} = {(⟨p, hp.out⟩ : Nat.Primes)} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]⟩
  have hPπ : IsPiSubgroup {(⟨p, hp.out⟩ : Nat.Primes)} P := by
    rw [← hset]
    exact CFSG.LocalCores.piCore_isPiSubgroup _
  have hPp : IsPGroup p P := by
    have hpos : Nat.card P ≠ 0 := Nat.card_pos.ne'
    have heq := Nat.eq_prime_pow_of_unique_prime_dvd hpos (p := p) fun {d} hd hdvd => by
      have h2 : (⟨d, hd⟩ : Nat.Primes) = ⟨p, hp.out⟩ := hPπ ⟨d, hd⟩ hdvd
      exact congrArg Subtype.val h2
    exact IsPGroup.of_card heq
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hPp
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hP
    rw [pow_zero] at hk
    exact (Subgroup.card_eq_one).1 hk
  have hGcard : Nat.card N * N.index = Nat.card G := Subgroup.card_mul_index N
  have hPdvd : Nat.card P ∣ Nat.card G := Subgroup.card_subgroup_dvd_card P
  have hGdvd : Nat.card G ∣ Nat.card N * p := by
    rw [← hGcard]
    exact mul_dvd_mul_left _ hidx
  have hPcard : Nat.card P = p := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : p ^ k' * p ∣ Nat.card N * p := by
      rw [← pow_succ, ← hk]
      exact hPdvd.trans hGdvd
    have h2 : p ^ k' ∣ Nat.card N := Nat.dvd_of_mul_dvd_mul_right hp.out.pos h1
    have hk' : k' = 0 := by
      by_contra hne
      exact hN ((dvd_pow_self p hne).trans h2)
    rw [hk, hk', zero_add, pow_one]
  have hcopN : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hN
  have hxP : x ∈ P := by
    have hquot : Nat.card G = Nat.card (G ⧸ P) * p := by
      rw [← hPcard]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup P
    have hpq : ¬ p ∣ Nat.card (G ⧸ P) := by
      intro hdvd
      have h1 : p * p ∣ Nat.card N * p := by
        have : Nat.card (G ⧸ P) * p ∣ Nat.card N * p := by
          rw [← hquot]
          exact hGdvd
        exact (mul_dvd_mul_right hdvd p).trans this
      exact hN (Nat.dvd_of_mul_dvd_mul_right hp.out.pos h1)
    have hord1 : orderOf (QuotientGroup.mk x : G ⧸ P) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, hxp, QuotientGroup.mk_one])
    have hord2 : orderOf (QuotientGroup.mk x : G ⧸ P) ∣ Nat.card (G ⧸ P) := orderOf_dvd_natCard _
    have hcop : Nat.Coprime p (Nat.card (G ⧸ P)) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpq
    have h1 : orderOf (QuotientGroup.mk x : G ⧸ P) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hord1 hord2
    exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h1)
  intro n hn
  have hc1 : n * x * n⁻¹ * x⁻¹ ∈ N := by
    have : x * n⁻¹ * x⁻¹ ∈ N := by
      have := ‹N.Normal›.conj_mem n⁻¹ (N.inv_mem hn) x
      simpa using this
    simpa [mul_assoc] using N.mul_mem hn this
  have hc2 : n * x * n⁻¹ * x⁻¹ ∈ P := by
    have h1 : n * x * n⁻¹ ∈ P := by
      have := ‹P.Normal›.conj_mem x hxP n
      simpa using this
    exact P.mul_mem h1 (P.inv_mem hxP)
  have hbot : n * x * n⁻¹ * x⁻¹ = 1 := by
    have h1 : orderOf (n * x * n⁻¹ * x⁻¹) ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hc1
      simpa [Subgroup.orderOf_mk] using this
    have h2 : orderOf (n * x * n⁻¹ * x⁻¹) ∣ p := by
      have := Subgroup.orderOf_dvd_natCard P hc2
      rw [hPcard] at this
      simpa [Subgroup.orderOf_mk] using this
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcopN h2 h1)
  calc n * x = (n * x * n⁻¹ * x⁻¹) * x * n := by group
    _ = x * n := by rw [hbot]; group

end PSolv

section Core

variable {F : Type} [Field F] [Finite F] {p : ℕ} [hp : Fact p.Prime] [CharP F p]

noncomputable instance finiteEndFinTwo : Finite (Module.End F (Fin 2 → F)) :=
  Finite.of_equiv _ (Matrix.toLin' (R := F) (m := Fin 2) (n := Fin 2)).toEquiv

theorem pow_conj_mem {M : Type*} [Group M] {x : M} {Tt : Subgroup M}
    (hnorm : ∀ g ∈ Tt, x * g * x⁻¹ ∈ Tt) {g : M} (hg : g ∈ Tt) (k : ℕ) :
    x ^ k * g * (x ^ k)⁻¹ ∈ Tt := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h : x ^ (k + 1) * g * (x ^ (k + 1))⁻¹ = x * (x ^ k * g * (x ^ k)⁻¹) * x⁻¹ := by
      rw [pow_succ']
      group
    rw [h]
    exact hnorm _ ih

theorem mem_normalizer_of_pow_eq_one {M : Type*} [Group M] {x : M} {Tt : Subgroup M} {p : ℕ}
    (hp0 : 0 < p) (hxp : x ^ p = 1) (hnorm : ∀ g ∈ Tt, x * g * x⁻¹ ∈ Tt) :
    x ∈ Subgroup.normalizer (Tt : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hnorm g, fun h => ?_⟩
  have hinv : x⁻¹ = x ^ (p - 1) := by
    have : x ^ (p - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp0, hxp]
    exact (eq_inv_of_mul_eq_one_left this).symm
  have h2 := pow_conj_mem hnorm h (p - 1)
  have h3 : x ^ (p - 1) * (x * g * x⁻¹) * (x ^ (p - 1))⁻¹ = g := by
    rw [← hinv]
    group
  rwa [h3] at h2

open Polynomial in
theorem sub_one_pow_eq_zero {M : Type*} [Ring M] [Algebra F M] {x : M} (hxp : x ^ p = 1) :
    (x - 1) ^ p = 0 := by
  have h1 : ((X - 1 : F[X])) ^ p = X ^ p - 1 := by
    have := sub_pow_char (p := p) (X : F[X]) 1
    simpa using this
  have h2 := congrArg (Polynomial.aeval x) h1
  simpa [hxp] using h2

theorem scalar_of_normalized_unipotent (hp5 : 5 ≤ p) (x : (Module.End F (Fin 2 → F))ˣ)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (Tt : Subgroup (Module.End F (Fin 2 → F))ˣ)
    (hTp : ∀ g ∈ Tt, ¬ p ∣ orderOf g) (hnorm : ∀ g ∈ Tt, x * g * x⁻¹ ∈ Tt) :
    ∀ g ∈ Tt, ∃ c : F, (g : Module.End F (Fin 2 → F)) = c • (1 : Module.End F (Fin 2 → F)) := by
  classical
  have hV : Module.finrank F (Fin 2 → F) = 2 := by simp
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  set N₀ : Module.End F (Fin 2 → F) := (x : Module.End F (Fin 2 → F)) - 1 with hN₀
  have hN0 : N₀ ≠ 0 := by
    intro h
    exact hx1 (Units.ext (sub_eq_zero.1 h))
  have hxp' : ((x : Module.End F (Fin 2 → F))) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hxp, Units.val_one]
  have hnil : IsNilpotent N₀ := ⟨p, sub_one_pow_eq_zero (F := F) hxp'⟩
  have hN2 : N₀ ^ 2 = 0 := sq_eq_zero_of_isNilpotent hV hnil
  have hxT : x ∉ Tt := fun h => hTp x h (by rw [hxo])
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (Tt : Set (Module.End F (Fin 2 → F))ˣ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_of_pow_eq_one hp.out.pos hxp hnorm
  set G : Subgroup (Module.End F (Fin 2 → F))ˣ := Subgroup.zpowers x ⊔ Tt with hG
  set NG : Subgroup ↥G := Tt.subgroupOf G with hNG
  haveI : NG.Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
  have hxG : x ∈ G := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hTG : Tt ≤ G := le_sup_right
  have hidx : NG.index ∣ p := by
    have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers x) Tt hle
    have h1 : Nat.card (↥G ⧸ NG) = Nat.card (↥(Subgroup.zpowers x) ⧸ Tt.subgroupOf (Subgroup.zpowers x)) :=
      (Nat.card_congr e.toEquiv).symm
    rw [Subgroup.index_eq_card, h1]
    have h2 := Subgroup.card_quotient_dvd_card (Tt.subgroupOf (Subgroup.zpowers x))
    rwa [Nat.card_zpowers, hxo] at h2
  have hNGcop : ¬ p ∣ Nat.card NG := by
    intro hdvd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv] at hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Tt) p hdvd
    exact hTp (g : (Module.End F (Fin 2 → F))ˣ) g.2 (by rw [Subgroup.orderOf_coe, hg])
  let xG : ↥G := ⟨x, hxG⟩
  have hxGp : xG ^ p = 1 := Subtype.ext (by simpa using hxp)
  have hxGo : orderOf xG = p := by
    rw [← Subgroup.orderOf_coe xG]
    exact hxo
  rcases piCore_eq_bot_or_commute hNGcop hidx hxGp with hO | hcomm
  · exfalso
    have hPS : CFSG.HallHigman.IsPSolvable p ↥G := isPSolvable_of_normal_index_dvd hNGcop hidx
    obtain ⟨r, -, -, -, -, -, hfin⟩ :=
      CFSG.GroupTheory.HallHigmanB.hall_higman_theorem_B_minimal_polynomial G hPS hO xG
        (n := 1) le_rfl (by rw [hxGo, pow_one])
    exact hfin hp5 hN2
  · intro g hg
    have hgN : (⟨g, hTG hg⟩ : ↥G) ∈ NG := Subgroup.mem_subgroupOf.2 hg
    have hgx : g * x = x * g := congrArg (fun z : ↥G => (z : (Module.End F (Fin 2 → F))ˣ))
      (hcomm _ hgN)
    refine exists_smul_one_of_commute hV hN0 hN2 (hTp g hg) ?_
    have h1 : (g : Module.End F (Fin 2 → F)) * (x : Module.End F (Fin 2 → F)) =
        (x : Module.End F (Fin 2 → F)) * (g : Module.End F (Fin 2 → F)) := by
      rw [← Units.val_mul, ← Units.val_mul, hgx]
    rw [hN₀, mul_sub, sub_mul, mul_one, one_mul, h1]

end Core

end CFSG.HardMathSupport.Dickson.I271
