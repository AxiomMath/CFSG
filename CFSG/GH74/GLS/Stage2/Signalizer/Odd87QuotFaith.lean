module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87QuotTools
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.RankThree.PartOne.FTL.Frattini

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

section Frattini

variable {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}

@[expose] def QuotCfg.restr (h : QuotCfg p α Xh) : ↥Xh →* ↥Xh :=
  (α.toMonoidHom.comp Xh.subtype).codRestrict Xh (fun x => h.inv x.1 x.2)

@[simp] theorem QuotCfg.coe_restr (h : QuotCfg p α Xh) (x : ↥Xh) : ((h.restr x : ↥Xh) : P) = α x := rfl

theorem QuotCfg.restr_restr (h : QuotCfg p α Xh) (x : ↥Xh) : h.restr (h.restr x) = x :=
  Subtype.ext (by simp [h.invol])

theorem QuotCfg.fixed_mem_frattini [Finite P] (h : QuotCfg p α Xh) {x : ↥Xh} (hx : α (x : P) = x) :
    x ∈ frattini ↥Xh := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, hcomm, hexp, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient h.pgroup
  let π : ↥Xh →* ↥Xh ⧸ frattini ↥Xh := QuotientGroup.mk' _
  set S₀ : Set ↥Xh := {w | ∃ y : ↥Xh, w = y * (h.restr y)⁻¹} with hS₀
  have key : ∀ w ∈ Subgroup.closure S₀, π (h.restr w) = (π w)⁻¹ := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨y, rfl⟩ := hw
      have e : h.restr (y * (h.restr y)⁻¹) = (y * (h.restr y)⁻¹)⁻¹ := by
        rw [map_mul, map_inv, h.restr_restr, mul_inv_rev, inv_inv]
      rw [e, map_inv]
    | one => simp
    | mul a b ha hb iha ihb =>
      rw [map_mul, map_mul, map_mul, iha, ihb, mul_inv_rev]
      exact hcomm.is_comm.comm _ _
    | inv a ha iha => rw [map_inv, map_inv, map_inv, iha]
  have hxS : x ∈ Subgroup.closure S₀ := by
    have h1 := h.comm x x.2
    have h2 : {w : P | ∃ y ∈ Xh, w = y * (α y)⁻¹} = Xh.subtype '' S₀ := by
      ext w
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩ * (h.restr ⟨y, hy⟩)⁻¹, ⟨⟨y, hy⟩, rfl⟩, by simp⟩
      · rintro ⟨u, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, y.2, by simp⟩
    rw [h2, ← MonoidHom.map_closure] at h1
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp h1
    have : x' = x := Subtype.ext hxx'
    rwa [this] at hx'
  have h1 := key x hxS
  have hα : h.restr x = x := Subtype.ext hx
  rw [hα] at h1
  have h2 : π x ^ 2 = 1 := by
    rw [pow_two]
    calc π x * π x = π x * (π x)⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel _
  have h3 : π x ^ p = 1 := hexp _
  have h4 : π x ^ (Nat.gcd 2 p) = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two h.prime).mpr (Ne.symm h.odd)
  rw [hcop.gcd_eq_one, pow_one] at h4
  exact (QuotientGroup.eq_one_iff x).mp h4


theorem QuotCfg.card_bound [Finite P] (h : QuotCfg p α Xh) {E : Subgroup P}
    (hEN : E ≤ normalizer (Xh : Set P)) (hEα : ∀ e ∈ E, α e = e) :
    ∃ r : ℕ, 1 ≤ r ∧ Nat.card (↥Xh ⧸ frattini ↥Xh) = p ^ r ∧ p ^ r * Nat.card ↥E ∣ Nat.card P := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, -, -, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient h.pgroup
  have hnt : Nontrivial ↥Xh := (Subgroup.nontrivial_iff_ne_bot Xh).mpr h.ne_bot
  have hfr : frattini ↥Xh ≠ ⊤ := by
    intro htop
    have hbt : (⊥ : Subgroup ↥Xh) = ⊤ := frattini_nongenerating (K := (⊥ : Subgroup ↥Xh)) (by rw [htop]; simp)
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥Xh)
    apply hy
    have : y ∈ (⊤ : Subgroup ↥Xh) := trivial
    rw [← hbt] at this
    exact Subgroup.mem_bot.mp this
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      apply hfr
      rw [h0, pow_zero] at hd
      rw [eq_top_iff]
      intro x _
      have h1 : Subsingleton (↥Xh ⧸ frattini ↥Xh) := Finite.card_le_one_iff_subsingleton.mp (by rw [hd])
      exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
    · exact h0
  refine ⟨d, hd1, hd, ?_⟩
  have hcount := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hEN
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥Xh)
  set Φ' : Subgroup P := (frattini ↥Xh).map Xh.subtype with hΦ'
  have hΦcard : Nat.card ↥Φ' = Nat.card ↥(frattini ↥Xh) :=
    Nat.card_congr ((frattini ↥Xh).equivMapOfInjective Xh.subtype Xh.subtype_injective).toEquiv.symm
  have hinfle : Xh ⊓ E ≤ Φ' := by
    intro z hz
    have hzf : (⟨z, hz.1⟩ : ↥Xh) ∈ frattini ↥Xh := h.fixed_mem_frattini (hEα z hz.2)
    exact ⟨⟨z, hz.1⟩, hzf, rfl⟩
  have hidvd : Nat.card ↥(Xh ⊓ E) ∣ Nat.card ↥(frattini ↥Xh) := hΦcard ▸ Subgroup.card_dvd_of_le hinfle
  obtain ⟨k, hk⟩ := hidvd
  have hXE : Nat.card ↥(Xh ⊔ E) ∣ Nat.card P := Subgroup.card_subgroup_dvd_card _
  have hpos : 0 < Nat.card ↥(Xh ⊓ E) := Nat.card_pos
  have key : Nat.card ↥(Xh ⊔ E) = p ^ d * k * Nat.card ↥E := by
    have h1 : Nat.card ↥(Xh ⊔ E) * Nat.card ↥(Xh ⊓ E) = (p ^ d * k * Nat.card ↥E) * Nat.card ↥(Xh ⊓ E) := by
      rw [hcount, hlag, hd, hk]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hXE' : p ^ d * k * Nat.card ↥E ∣ Nat.card P := key ▸ hXE
  exact (Dvd.intro k (by ring)).trans hXE'

theorem QuotCfg.exists_pow_dvd_of_nontrivial [Finite P] (h : QuotCfg p α Xh) {g : P}
    (hg : g ∈ normalizer (Xh : Set P)) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hgq : g ^ q = 1)
    (hnt : ∃ x ∈ Xh, g * x * g⁻¹ ≠ x) :
    ∃ r k : ℕ, Nat.card (↥Xh ⧸ frattini ↥Xh) = p ^ r ∧ 1 ≤ k ∧ k ≤ r ∧ q ∣ p ^ k - 1 := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, -, -, -, r, hr, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient h.pgroup
  let τ : MulAut ↥Xh := Xh.normalizerMonoidHom ⟨g, hg⟩
  have hτq : τ ^ q = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : normalizer (Xh : Set P)) ^ q = 1 := Subtype.ext (by simpa using hgq)
    rw [this, map_one]
  let ψ : MulAut (↥Xh ⧸ frattini ↥Xh) := quotientAutomorphism (frattini ↥Xh) τ
  have hψq : ψ ^ q = 1 := by rw [← map_pow, hτq, map_one]
  have hψ1 : ψ ≠ 1 := by
    intro hψ
    have hcop : Nat.Coprime q p := (Nat.coprime_primes hq h.prime).mpr hqp
    have h1 := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini h.pgroup hτq hcop hψ
    obtain ⟨x, hx, hne⟩ := hnt
    apply hne
    have h2 := congrArg (fun σ : MulAut ↥Xh => ((σ ⟨x, hx⟩ : ↥Xh) : P)) h1
    simpa [τ] using h2
  set F : Subgroup (↥Xh ⧸ frattini ↥Xh) := fixSub ψ with hF
  have hFdvd : Nat.card ↥F ∣ p ^ r := hr ▸ Subgroup.card_subgroup_dvd_card F
  obtain ⟨s, hsr, hs⟩ := (Nat.dvd_prime_pow h.prime).mp hFdvd
  have hsr' : s < r := by
    rcases hsr.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply hψ1
      have hFtop : F = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hs, hr, heq]
      refine MulEquiv.ext fun v => ?_
      have : v ∈ F := hFtop ▸ Subgroup.mem_top v
      exact this
  let _ : Fintype (↥Xh ⧸ frattini ↥Xh) := Fintype.ofFinite _
  let f : Function.End (↥Xh ⧸ frattini ↥Xh) := fun v => ψ v
  have hfpow : ∀ n : ℕ, ∀ v, (f ^ n) v = (ψ ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, pow_succ]
      exact (ih _)
  have hf : f ^ q ^ 1 = 1 := by
    funext v
    rw [pow_one, hfpow, hψq]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥Xh ⧸ frattini ↥Xh) (f := f) (p := q) (n := 1) hf
  have hcardV : Fintype.card (↥Xh ⧸ frattini ↥Xh) = p ^ r := by
    rw [← Nat.card_eq_fintype_card, hr]
  have hcardF : Fintype.card (Function.fixedPoints f) = p ^ s := by
    rw [← Nat.card_eq_fintype_card, ← hs]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => Iff.rfl)
  rw [hcardV, hcardF] at hmod
  have hle : p ^ s ≤ p ^ r := Nat.pow_le_pow_right h.prime.pos hsr
  have hdvd : q ∣ p ^ r - p ^ s := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  have e : p ^ r - p ^ s = p ^ s * (p ^ (r - s) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_of_le hsr]
  rw [e] at hdvd
  have hcop : Nat.Coprime q (p ^ s) := Nat.Coprime.pow_right s ((Nat.coprime_primes hq h.prime).mpr hqp)
  exact ⟨r, r - s, hr, by omega, by omega, hcop.dvd_of_dvd_mul_left hdvd⟩

end Frattini


section Perfect

theorem perfect_le_closure_odd {P : Type} [Group P] [Finite P] (E : Subgroup P)
    (hE : Group.IsPerfect ↥E) :
    E ≤ Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)} := by
  classical
  set S : Set ↥E := {c : ↥E | Odd (orderOf c)} with hS
  set N : Subgroup ↥E := Subgroup.closure S with hN
  have hnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      show Odd (orderOf (g * y * g⁻¹))
      have h1 : orderOf (g * y * g⁻¹) = orderOf y := by
        have := MulEquiv.orderOf_eq (MulAut.conj g) y
        simpa [MulAut.conj_apply] using this
      rw [h1]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]; exact N.mul_mem ihx ihy
    | inv x hx ih =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]; exact N.inv_mem ih
  have h2 : IsPGroup 2 (↥E ⧸ N) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
    refine ⟨a, ?_⟩
    have hordpow : orderOf (c ^ (2 ^ a)) = m := by
      rw [orderOf_pow_of_dvd (by positivity) ⟨m, hcm⟩, hcm, Nat.mul_div_cancel_left _ (by positivity)]
    have hmem : c ^ 2 ^ a ∈ N := Subgroup.subset_closure (by
      show Odd (orderOf (c ^ 2 ^ a))
      rw [hordpow]; exact hm)
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hmem
  have hperfQ : Group.IsPerfect (↥E ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := (QuotientGroup.mk' N)) (QuotientGroup.mk'_surjective N)
  have hnil : Group.IsNilpotent (↥E ⧸ N) := h2.isNilpotent
  have hsub : Subsingleton (↥E ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent _ hnil
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (Subsingleton.elim _ _)
  have key : ∀ (c : ↥E), c ∈ N → (c : P) ∈ Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)} := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem y hy =>
      apply Subgroup.subset_closure
      refine ⟨y.2, ?_⟩
      have : orderOf (y : P) = orderOf y := Subgroup.orderOf_coe y
      rw [this]; exact hy
    | one => simp
    | mul x y hx hy ihx ihy => simpa using Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => simpa using Subgroup.inv_mem _ ih
  intro y hy
  exact key ⟨y, hy⟩ (hNtop ▸ Subgroup.mem_top _)

end Perfect


section Quasisimple

variable {P : Type} [Group P] {p : ℕ} {α : MulAut P} {Xh : Subgroup P}

theorem exists_noncentralizing_of_quasisimple {E : Subgroup P} (hE : CFSG.IsQuasisimple ↥E)
    (hEN : E ≤ normalizer (Xh : Set P)) {e₀ : P} (he₀ : e₀ ∈ E)
    (hnt₀ : ∃ x ∈ Xh, e₀ * x * e₀⁻¹ ≠ x) {g : P} (hg : g ∈ E)
    (hgZ : (⟨g, hg⟩ : ↥E) ∉ Subgroup.center ↥E) : ∃ x ∈ Xh, g * x * g⁻¹ ≠ x := by
  by_contra hall
  have hall' : ∀ x ∈ Xh, g * x * g⁻¹ = x := fun x hx => by_contra fun hne => hall ⟨x, hx, hne⟩
  let ψ : ↥E →* MulAut ↥Xh := Xh.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hDn : ψ.ker.Normal := ψ.normal_ker
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hE hDn with htop | hle
  · obtain ⟨x, hx, hne⟩ := hnt₀
    have h1 : (⟨e₀, he₀⟩ : ↥E) ∈ ψ.ker := htop ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker] at h1
    apply hne
    have h2 := congrArg (fun σ : MulAut ↥Xh => ((σ ⟨x, hx⟩ : ↥Xh) : P)) h1
    simpa [ψ] using h2
  · apply hgZ
    apply hle
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simpa [ψ] using hall' x.1 x.2

theorem QuotCfg.false_of_nontrivial_prime_elt [Finite P] (h : QuotCfg p α Xh) {E : Subgroup P}
    (hEclos : E ≤ Subgroup.closure {y : P | y ∈ E ∧ Odd (orderOf y)})
    (hEα : ∀ e ∈ E, α e = e) {g : P} (hg : g ∈ E) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hgq : orderOf g = q) (hnt : ∃ x ∈ Xh, g * x * g⁻¹ ≠ x) {N M : ℕ} (hN : Nat.card P = N)
    (hM : Nat.card ↥E = M)
    (hnum : ∀ r k : ℕ, p ^ r * M ∣ N → 1 ≤ k → k ≤ r → ¬ q ∣ p ^ k - 1) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hEN : E ≤ normalizer (Xh : Set P) := by
    refine hEclos.trans ?_
    refine (Subgroup.closure_mono ?_).trans h.closure_odd_le_normalizer
    rintro y ⟨hy, hyo⟩
    exact ⟨hEα y hy, hyo⟩
  have hgpow : g ^ q = 1 := hgq ▸ pow_orderOf_eq_one g
  obtain ⟨r, k, hr, hk1, hkr, hqk⟩ := h.exists_pow_dvd_of_nontrivial (hEN hg) hq hqp hgpow hnt
  obtain ⟨r', -, hr', hdiv⟩ := h.card_bound hEN hEα
  have hrr : r = r' := Nat.pow_right_injective h.prime.two_le (hr.symm.trans hr')
  subst hrr
  rw [hN, hM] at hdiv
  exact hnum r k hdiv hk1 hkr hqk

theorem QuotCfg.false_of_quasisimple_row [Finite P] (h : QuotCfg p α Xh) {E : Subgroup P}
    (hE : CFSG.IsQuasisimple ↥E) (hEα : ∀ e ∈ E, α e = e) {t : P} (htE : t ∈ E)
    (htα : ∀ x, t * x * t⁻¹ = α x) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (hqE : q ∣ Nat.card ↥E)
    (hqZ : ¬ q ∣ Nat.card ↥(Subgroup.center ↥E)) {N M : ℕ} (hN : Nat.card P = N)
    (hM : Nat.card ↥E = M)
    (hnum : ∀ r k : ℕ, p ^ r * M ∣ N → 1 ≤ k → k ≤ r → ¬ q ∣ p ^ k - 1) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hEclos := perfect_le_closure_odd E hE.1
  have hEN : E ≤ normalizer (Xh : Set P) := by
    refine hEclos.trans ?_
    refine (Subgroup.closure_mono ?_).trans h.closure_odd_le_normalizer
    rintro y ⟨hy, hyo⟩
    exact ⟨hEα y hy, hyo⟩
  obtain ⟨g, hgq⟩ := exists_prime_orderOf_dvd_card' q hqE
  have hgE : (g : P) ∈ E := g.2
  have hgZ : (⟨(g : P), hgE⟩ : ↥E) ∉ Subgroup.center ↥E := by
    intro hz
    apply hqZ
    have := orderOf_dvd_natCard (⟨g, hz⟩ : ↥(Subgroup.center ↥E))
    rwa [Subgroup.orderOf_mk, hgq] at this
  obtain ⟨x, hx, hne⟩ : ∃ x ∈ Xh, α x ≠ x := by
    by_contra hcon
    apply h.not_fixed
    intro x hx
    by_contra hne
    exact hcon ⟨x, hx, hne⟩
  have hnt₀ : ∃ x ∈ Xh, t * x * t⁻¹ ≠ x := ⟨x, hx, by rw [htα]; exact hne⟩
  have hnt := exists_noncentralizing_of_quasisimple hE hEN htE hnt₀ hgE hgZ
  exact h.false_of_nontrivial_prime_elt hEclos hEα hgE hq hqp (by rw [← hgq]; exact Subgroup.orderOf_coe g) hnt hN hM hnum

theorem QuotCfg.false_of_simple_row [Finite P] (h : QuotCfg p α Xh) {E : Subgroup P}
    (hE : IsSimpleGroup ↥E) (hEnab : ∃ a b : ↥E, a * b ≠ b * a) (hEα : ∀ e ∈ E, α e = e)
    (hnc : ∃ e ∈ E, ∃ x ∈ Xh, e * x * e⁻¹ ≠ x) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqE : q ∣ Nat.card ↥E) {N M : ℕ} (hN : Nat.card P = N) (hM : Nat.card ↥E = M)
    (hnum : ∀ r k : ℕ, p ^ r * M ∣ N → 1 ≤ k → k ≤ r → ¬ q ∣ p ^ k - 1) : False := by
  have : Fact q.Prime := ⟨hq⟩
  have hperf : Group.IsPerfect ↥E := isPerfect_of_simple_nonab hEnab
  have hEclos := perfect_le_closure_odd E hperf
  have hEN : E ≤ normalizer (Xh : Set P) := by
    refine hEclos.trans ?_
    refine (Subgroup.closure_mono ?_).trans h.closure_odd_le_normalizer
    rintro y ⟨hy, hyo⟩
    exact ⟨hEα y hy, hyo⟩
  obtain ⟨g, hgq⟩ := exists_prime_orderOf_dvd_card' q hqE
  have hgE : (g : P) ∈ E := g.2
  let ψ : ↥E →* MulAut ↥Xh := Xh.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  have hDn : ψ.ker.Normal := ψ.normal_ker
  have hDbot : ψ.ker = ⊥ := by
    have := hE
    have := hDn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨e, he, x, hx, hne⟩ := hnc
      have h2 : (⟨e, he⟩ : ↥E) ∈ ψ.ker := h1 ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at h2
      apply hne
      have h3 := congrArg (fun σ : MulAut ↥Xh => ((σ ⟨x, hx⟩ : ↥Xh) : P)) h2
      simpa [ψ] using h3
  have hnt : ∃ x ∈ Xh, (g : P) * x * (g : P)⁻¹ ≠ x := by
    by_contra hall
    have hall' : ∀ x ∈ Xh, (g : P) * x * (g : P)⁻¹ = x := fun x hx => by_contra fun hne => hall ⟨x, hx, hne⟩
    have h1 : g ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      refine MulEquiv.ext fun x => Subtype.ext ?_
      simpa [ψ] using hall' x.1 x.2
    rw [hDbot, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hgq
    exact hq.one_lt.ne hgq
  exact h.false_of_nontrivial_prime_elt hEclos hEα hgE hq hqp (by rw [← hgq]; exact Subgroup.orderOf_coe g) hnt hN hM hnum

end Quasisimple

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
