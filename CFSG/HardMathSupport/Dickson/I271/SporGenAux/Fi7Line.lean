module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

section Core

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem pelt_mem_of_normal {C F : Subgroup X} {m : ℕ} (hFC : F ≤ C) (hFcard : Nat.card F = p ^ 3)
    (hC : Nat.card C = p ^ 3 * m) (hm : ¬ p ∣ m)
    (hFn : ∀ c ∈ C, ∀ f ∈ F, c * f * c⁻¹ ∈ F) :
    ∀ c ∈ C, (∃ n : ℕ, c ^ (p ^ n) = 1) → c ∈ F := by
  intro c hc ⟨n, hn⟩
  have hp' := hp.out
  have hfac : (Nat.card C).factorization p = 3 := by
    rw [hC, Nat.factorization_mul (pow_ne_zero 3 hp'.ne_zero) (by
      rintro rfl; exact hm (dvd_zero p)), Finsupp.add_apply, hp'.factorization_pow,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  set S : Subgroup C := F.subgroupOf C with hS
  have hScard : Nat.card S = p ^ (Nat.card C).factorization p := by
    rw [hfac, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFcard]
  let P : Sylow p C := Sylow.ofCard S hScard
  have hPnorm : P.Normal := ⟨fun x hx g => by
    have hx' : (x : C) ∈ S := hx
    rw [hS, Subgroup.mem_subgroupOf] at hx'
    show g * x * g⁻¹ ∈ S
    rw [hS, Subgroup.mem_subgroupOf]
    have := hFn g g.2 x hx'
    simpa using this⟩
  haveI : Finite (Sylow p C) := inferInstance
  set c' : C := ⟨c, hc⟩ with hc'
  have hcyc : IsPGroup p (Subgroup.zpowers c') := by
    have hn' : c' ^ (p ^ n) = 1 := Subtype.ext (by simpa using hn)
    have hord : orderOf c' ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp').1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S', hS'⟩ := hcyc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P S'
  have hS'eq : S' = P := by
    rw [← hg, Sylow.smul_eq_of_normal]
  have hc'S : c' ∈ (P : Subgroup C) := by
    rw [← hS'eq]
    exact hS' (Subgroup.mem_zpowers c')
  have : c' ∈ S := hc'S
  rw [hS, Subgroup.mem_subgroupOf] at this
  exact this

theorem normal_of_card_lt {C F : Subgroup X} {m : ℕ} (hFC : F ≤ C) (hFcard : Nat.card F = p ^ 3)
    (hC : Nat.card C = p ^ 3 * m) (hmp : m < p) : ∀ c ∈ C, ∀ f ∈ F, c * f * c⁻¹ ∈ F := by
  have hp' := hp.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have : 0 < Nat.card C := Nat.card_pos
      rw [hC, h, mul_zero] at this
      exact absurd this (lt_irrefl 0)
    · exact h
  have hm : ¬ p ∣ m := fun h => absurd (Nat.le_of_dvd hm0 h) (not_le.2 hmp)
  have hfac : (Nat.card C).factorization p = 3 := by
    rw [hC, Nat.factorization_mul (pow_ne_zero 3 hp'.ne_zero) hm0.ne', Finsupp.add_apply,
      hp'.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
      add_zero]
  set S : Subgroup C := F.subgroupOf C with hS
  have hScard : Nat.card S = p ^ (Nat.card C).factorization p := by
    rw [hfac, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFcard]
  let P : Sylow p C := Sylow.ofCard S hScard
  haveI : Finite (Sylow p C) := inferInstance
  have hidx : (P : Subgroup C).index = m := by
    have h1 := Subgroup.card_mul_index (P : Subgroup C)
    have h2 : Nat.card (P : Subgroup C) = p ^ 3 := by
      show Nat.card S = p ^ 3
      rw [hScard, hfac]
    rw [h2, hC] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp'.pos 3) h1
  have hmod := card_sylow_modEq_one p C
  have hdvd := Sylow.card_dvd_index P
  rw [hidx] at hdvd
  have hpos : 0 < Nat.card (Sylow p C) := Nat.card_pos
  have hle : Nat.card (Sylow p C) ≤ m := Nat.le_of_dvd hm0 hdvd
  have hone : Nat.card (Sylow p C) = 1 := by
    have h1 : Nat.card (Sylow p C) % p = 1 % p := hmod
    rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hle hmp), Nat.mod_eq_of_lt hp'.one_lt] at h1
    exact h1
  haveI : Subsingleton (Sylow p C) := (Nat.card_eq_one_iff_unique.1 hone).1
  have hPn : P.Normal := Sylow.normal_of_subsingleton P
  intro c hc f hf
  have hf' : (⟨f, hFC hf⟩ : C) ∈ S := Subgroup.mem_subgroupOf.2 hf
  have := hPn.conj_mem ⟨f, hFC hf⟩ hf' ⟨c, hc⟩
  have h3 : (⟨c, hc⟩ * ⟨f, hFC hf⟩ * ⟨c, hc⟩⁻¹ : C) ∈ S := this
  rw [hS, Subgroup.mem_subgroupOf] at h3
  simpa using h3

end Core

section Center

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem center_eq_zpowers_of_nonabelian {Q : Subgroup X} {c : X} (hQ : Nat.card Q = p ^ 3)
    (hc : c ∈ Q) (hc7 : orderOf c = p) (hcc : ∀ q ∈ Q, c * q = q * c)
    (hnab : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    ∀ x ∈ Q, (∀ q ∈ Q, x * q = q * x) → x ∈ Subgroup.zpowers c := by
  have hp' := hp.out
  intro x hx hxc
  by_contra hxn
  set Z : Subgroup Q := Subgroup.center Q with hZ
  set c' : Q := ⟨c, hc⟩ with hc'
  set x' : Q := ⟨x, hx⟩ with hx'
  have hc'Z : c' ∈ Z := by
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcc g.1 g.2).symm
  have hx'Z : x' ∈ Z := by
    rw [hZ, Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hxc g.1 g.2).symm
  have hxn' : x' ∉ Subgroup.zpowers c' := by
    intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    apply hxn
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa [hc', hx'] using congrArg Subtype.val hn⟩
  have hzc : Nat.card (Subgroup.zpowers c') = p := by
    rw [Nat.card_zpowers, hc', Subgroup.orderOf_mk, hc7]
  have hZge : Subgroup.zpowers c' < Z := by
    refine lt_of_le_of_ne ((Subgroup.zpowers_le).2 hc'Z) ?_
    intro h
    exact hxn' (h ▸ hx'Z)
  have hZgt : p < Nat.card Z := by
    have := Subgroup.card_lt_of_lt hZge
    rwa [hzc] at this
  have hZdvd : Nat.card Z ∣ p ^ 3 := by
    rw [← hQ]
    exact Subgroup.card_subgroup_dvd_card Z
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp').1 hZdvd
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    have : p ^ k ≤ p := by simpa using Nat.pow_le_pow_right hp'.pos (by omega : k ≤ 1)
    omega
  have hidx : Z.index = 1 ∨ Z.index = p := by
    have h1 := Subgroup.card_mul_index Z
    rw [hk, hQ] at h1
    have h2 : Z.index = p ^ (3 - k) := by
      refine Nat.eq_of_mul_eq_mul_left (pow_pos hp'.pos k) ?_
      rw [h1, ← pow_add]
      congr 1
      omega
    interval_cases k
    · right; simpa using h2
    · left; simpa using h2
  have hcyc : IsCyclic (Q ⧸ Z) := by
    rcases hidx with h1 | h1
    · haveI : Subsingleton (Q ⧸ Z) :=
        (Nat.card_eq_one_iff_unique.1 (show Nat.card (Q ⧸ Z) = 1 from h1)).1
      infer_instance
    · exact isCyclic_of_prime_card (p := p) (show Nat.card (Q ⧸ Z) = p from h1)
  haveI := hcyc
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hcomm := commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z)
    (QuotientGroup.ker_mk' Z).le ⟨a, ha⟩ ⟨b, hb⟩
  exact hab (congrArg Subtype.val hcomm)

end Center


section CentCore

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem cent_of_core {C F : Subgroup X} {w : X} {m : ℕ} (hFC : F ≤ C)
    (hFcard : Nat.card F = p ^ 3) (hC : Nat.card C = p ^ 3 * m) (hm : ¬ p ∣ m)
    (hFn : ∀ c ∈ C, ∀ f ∈ F, c * f * c⁻¹ ∈ F) (hw1 : w ≠ 1) (hw7 : w ^ p = 1) (hwF : w ∈ F)
    (hwC : ∀ c ∈ C, c * w = w * c)
    (hZ : ∀ x ∈ F, (∀ q ∈ F, x * q = q * x) → x ∈ Subgroup.zpowers w)
    (hcore : GLAPPrimeCoreOf p C = ⊥) :
    ∀ c ∈ C, (∀ f ∈ F, c * f = f * c) → c ∈ Subgroup.zpowers w := by
  have hp' := hp.out
  have hsyl := pelt_mem_of_normal hFC hFcard hC hm hFn
  have hw0 : orderOf w = p := orderOf_eq_prime hw7 hw1
  set K : Subgroup X := C ⊓ Subgroup.centralizer (F : Set X) with hK
  have hKmem : ∀ x, x ∈ K ↔ x ∈ C ∧ ∀ f ∈ F, x * f = f * x := by
    intro x
    rw [hK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun f hf => (h2 f hf).symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun f hf => (h2 f hf).symm⟩
  have hwK : w ∈ K := (hKmem w).2 ⟨hFC hwF, fun f hf => (hwC f (hFC hf)).symm⟩
  have hKp : ∀ x ∈ K, (∃ n : ℕ, x ^ (p ^ n) = 1) → x ∈ Subgroup.zpowers w := by
    intro x hx hxp
    obtain ⟨hxC, hxF⟩ := (hKmem x).1 hx
    exact hZ x (hsyl x hxC hxp) fun q hq => hxF q hq
  have hKnorm : ∀ c ∈ C, ∀ x ∈ K, c * x * c⁻¹ ∈ K := by
    intro c hc x hx
    obtain ⟨hxC, hxF⟩ := (hKmem x).1 hx
    refine (hKmem _).2 ⟨C.mul_mem (C.mul_mem hc hxC) (C.inv_mem hc), fun f hf => ?_⟩
    have hf' : c⁻¹ * f * c ∈ F := by
      have := hFn c⁻¹ (C.inv_mem hc) f hf
      simpa using this
    have h1 := hxF _ hf'
    calc c * x * c⁻¹ * f = c * (x * (c⁻¹ * f * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * f * c) * x) * c⁻¹ := by rw [h1]
      _ = f * (c * x * c⁻¹) := by group
  have hK2 : ¬ p ^ 2 ∣ Nat.card K := by
    intro hdvd
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    have hle : S.map K.subtype ≤ Subgroup.zpowers w := by
      rintro _ ⟨s, hs, rfl⟩
      refine hKp s.1 s.2 ⟨2, ?_⟩
      have : (⟨s, hs⟩ : S) ^ (p ^ 2) = 1 := by rw [← hS]; exact pow_card_eq_one'
      have := congrArg (fun t : S => ((t : K) : X)) this
      simpa using this
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective K.subtype_injective, hS, Nat.card_zpowers, hw0] at h1
    have : p ^ 2 ≤ p ^ 1 := by simpa using h1
    have h2 := Nat.pow_lt_pow_right hp'.one_lt (show 1 < 2 by norm_num)
    omega
  set w' : K := ⟨w, hwK⟩ with hw'
  have hw'0 : orderOf w' = p := by rw [hw', Subgroup.orderOf_mk, hw0]
  have hPcard : Nat.card (Subgroup.zpowers w') = p := by rw [Nat.card_zpowers, hw'0]
  have hKfac : (Nat.card K).factorization p = 1 := by
    have h0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have h1 : p ∣ Nat.card K := hPcard ▸ Subgroup.card_subgroup_dvd_card (Subgroup.zpowers w')
    have h2 : 1 ≤ (Nat.card K).factorization p :=
      (hp'.dvd_iff_one_le_factorization h0).1 h1
    have h3 : ¬ 2 ≤ (Nat.card K).factorization p := fun h =>
      hK2 ((hp'.pow_dvd_iff_le_factorization h0).2 h)
    omega
  let P : Sylow p K := Sylow.ofCard (Subgroup.zpowers w') (by rw [hPcard, hKfac, pow_one])
  have hPeq : (P : Subgroup K) = Subgroup.zpowers w' := rfl
  have hwcent : ∀ g : K, w' * g = g * w' := fun g =>
    Subtype.ext ((hwC g.1 (((hKmem g.1).1 g.2).1)).symm)
  have hPcenter : ∀ h ∈ (P : Subgroup K), ∀ g : K, h * g = g * h := by
    intro h hh g
    rw [hPeq] at hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact Commute.zpow_left (show Commute w' g from hwcent g) n
  have hP : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hPcenter h hh g
  set τ : K →* P := MonoidHom.transferSylow P hP with hτ
  set ker : Subgroup K := τ.ker with hker
  have hkercop : ¬ p ∣ Nat.card ker := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hcomp : ker.IsComplement' (P : Subgroup K) := MonoidHom.ker_transferSylow_isComplement' P hP
  have hchar : ∀ k : K, Nat.Coprime p (orderOf k) → k ∈ ker := by
    intro k hk
    rw [hker, MonoidHom.mem_ker]
    have h1 : orderOf (τ k) ∣ orderOf k := orderOf_map_dvd τ k
    have h2 : orderOf (τ k) ∣ p := by
      have : orderOf (τ k) ∣ Nat.card P := orderOf_dvd_natCard (τ k)
      rwa [show Nat.card P = p from hPcard] at this
    have h3 := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one hk] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  set N : Subgroup X := ker.map K.subtype with hN
  have hNK : ∀ x ∈ N, x ∈ K := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hNnorm : ∀ g ∈ C, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    rintro g hg _ ⟨k, hk, rfl⟩
    have hy : g * (k : X) * g⁻¹ ∈ K := hKnorm g hg k k.2
    refine ⟨⟨_, hy⟩, ?_, rfl⟩
    apply hchar
    have hord : orderOf (⟨g * (k : X) * g⁻¹, hy⟩ : K) = orderOf k := by
      rw [Subgroup.orderOf_mk]
      have := (MulAut.conj g).orderOf_eq (k : X)
      rw [MulAut.conj_apply] at this
      rw [this, Subgroup.orderOf_coe]
    rw [hord]
    have hdvd : orderOf k ∣ Nat.card ker := Subgroup.orderOf_dvd_natCard ker hk
    exact (Nat.Prime.coprime_iff_not_dvd hp').2 fun h => hkercop (h.trans hdvd)
  have hNcop : Nat.Coprime p (Nat.card N) := by
    rw [hN, Subgroup.card_map_of_injective K.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd hp').2 hkercop
  have hNle : N ≤ GLAPPrimeCoreOf p C :=
    le_GLAPPrimeCoreOf_of_normal (fun x hx => ((hKmem x).1 (hNK x hx)).1) hNnorm hNcop
  rw [hcore] at hNle
  have hkerbot : ker = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 (le_bot_iff.1 hNle)
  have hPc : Nat.card (P : Subgroup K) = p := hPcard
  have hcardK : Nat.card K = p := by
    have := hcomp.card_mul_card
    rw [hkerbot, Subgroup.card_bot, hPc, one_mul] at this
    exact this.symm
  intro c hc hcf
  have hcK : c ∈ K := (hKmem c).2 ⟨hc, hcf⟩
  have htop : (P : Subgroup K) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [hPc, hcardK])
  have hcP : (⟨c, hcK⟩ : K) ∈ (P : Subgroup K) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hPeq] at hcP
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hcP
  exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa [hw'] using congrArg Subtype.val hn⟩

end CentCore


section Line

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]

theorem sevenLine_of_core {w : X} {F : Subgroup X} {m : ℕ} (hw1 : w ≠ 1) (hw7 : w ^ p = 1)
    (hwF : w ∈ F) (hFC : F ≤ Subgroup.centralizer ({w} : Set X)) (hFcard : Nat.card F = p ^ 3)
    (hC : Nat.card (Subgroup.centralizer ({w} : Set X)) = p ^ 3 * m) (hmp : m < p)
    (hZ : ∀ x ∈ F, (∀ q ∈ F, x * q = q * x) → x ∈ Subgroup.zpowers w)
    (hcore : GLAPPrimeCoreOf p (Subgroup.centralizer ({w} : Set X)) = ⊥) : SevenLine p w F := by
  have hp' := hp.out
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · have : 0 < Nat.card (Subgroup.centralizer ({w} : Set X)) := Nat.card_pos
      rw [hC, h, mul_zero] at this
      exact absurd this (lt_irrefl 0)
    · exact h
  have hm : ¬ p ∣ m := fun h => absurd (Nat.le_of_dvd hm0 h) (not_le.2 hmp)
  have hFn := normal_of_card_lt hFC hFcard hC hmp
  have hwC : ∀ c ∈ Subgroup.centralizer ({w} : Set X), c * w = w * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.1 hc
  exact sevenLine_of_data hw1 hw7 hwF hC hm hFC hFcard hFn
    (cent_of_core hFC hFcard hC hm hFn hw1 hw7 hwF hwC hZ hcore)

theorem SevenLine.conj {w : X} {F : Subgroup X} (h : SevenLine p w F) (g : X) :
    SevenLine p (g * w * g⁻¹) (F.map (MulAut.conj g).toMonoidHom) := by
  have key : ∀ f : X, g⁻¹ * (g * f * g⁻¹) * g = f := fun f => by group
  have hmemF' : ∀ y, y ∈ F.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ F := by
    intro y
    constructor
    · rintro ⟨f, hf, rfl⟩
      simpa [MulAut.conj_apply, key] using hf
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply]; group⟩
  have hcentG : ∀ c, c ∈ Subgroup.centralizer ({g * w * g⁻¹} : Set X) ↔
      g⁻¹ * c * g ∈ Subgroup.centralizer ({w} : Set X) := by
    intro c
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      calc g⁻¹ * c * g * w = g⁻¹ * (c * (g * w * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * w * g⁻¹) * c) * g := by rw [hc]
        _ = w * (g⁻¹ * c * g) := by group
    · intro hc
      calc c * (g * w * g⁻¹) = g * ((g⁻¹ * c * g) * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * c * g)) * g⁻¹ := by rw [hc]
        _ = (g * w * g⁻¹) * c := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    apply h.ne_one
    have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
    rw [this, h1]; group
  · calc (g * w * g⁻¹) ^ p = g * w ^ p * g⁻¹ := by rw [conj_pow]
      _ = 1 := by rw [h.pow_eq]; group
  · exact ⟨w, h.mem, by simp [MulAut.conj_apply]⟩
  · intro f' hf'
    rw [hmemF'] at hf'
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hf')
    calc f' * (g * w * g⁻¹) = g * ((g⁻¹ * f' * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * f' * g)) * g⁻¹ := by rw [h1]
      _ = (g * w * g⁻¹) * f' := by group
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective F (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv.symm, h.card_eq]
  · intro c hc ⟨n, hn⟩
    rw [hcentG] at hc
    rw [hmemF']
    refine h.syl _ hc ⟨n, ?_⟩
    calc (g⁻¹ * c * g) ^ (p ^ n) = g⁻¹ * c ^ (p ^ n) * g := by
          have := conj_pow (a := g⁻¹) (b := c) (i := p ^ n)
          simpa using this
      _ = 1 := by rw [hn]; group
  · intro c hc f' hf'
    rw [hcentG] at hc
    rw [hmemF'] at hf'
    have := h.norm _ hc _ hf'
    rw [hmemF']
    have e : g⁻¹ * (c * f' * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * f' * g) * (g⁻¹ * c * g)⁻¹ := by
      group
    rw [e]
    exact this
  · intro c hc hcf
    rw [hcentG] at hc
    have hc' : g⁻¹ * c * g ∈ Subgroup.zpowers w := by
      refine h.cent _ hc fun f hf => ?_
      have := hcf (g * f * g⁻¹) ((hmemF' _).2 (by rw [key]; exact hf))
      calc g⁻¹ * c * g * f = g⁻¹ * (c * (g * f * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f * g⁻¹) * c) * g := by rw [this]
        _ = f * (g⁻¹ * c * g) := by group
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hc'
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    calc (g * w * g⁻¹) ^ n = g * w ^ n * g⁻¹ := by rw [conj_zpow]
      _ = c := by rw [hn]; group

end Line

end CFSG.HardMathSupport.Dickson.I271
