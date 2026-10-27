module

public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.CGT.T75H

open scoped commutatorElement

section MinimalNormal

variable {H : Type} [Group H] [Finite H]

theorem exists_minimal_normal_le (N : Subgroup H) [N.Normal] (hN1 : N ≠ ⊥) :
    ∃ M : Subgroup H, M ≤ N ∧ M.Normal ∧ M ≠ ⊥ ∧
      ∀ M' : Subgroup H, M' ≤ M → M'.Normal → M' ≠ ⊥ → M' = M := by
  classical
  have hex : ∃ k, ∃ M : Subgroup H, M ≤ N ∧ M.Normal ∧ M ≠ ⊥ ∧ Nat.card M = k :=
    ⟨_, N, le_rfl, inferInstance, hN1, rfl⟩
  obtain ⟨M, hMN, hMn, hM1, hMk⟩ := Nat.find_spec hex
  refine ⟨M, hMN, hMn, hM1, fun M' hM' hn' h1' => ?_⟩
  have h1 : Nat.find hex ≤ Nat.card M' := Nat.find_min' hex ⟨M', hM'.trans hMN, hn', h1', rfl⟩
  have h2 : Nat.card M' ≤ Nat.card M := Subgroup.card_le_of_le hM'
  exact Subgroup.eq_of_le_of_card_ge hM' (by omega)

omit [Finite H] in
theorem comm_of_minimal_normal {N M : Subgroup H} [N.Normal] [M.Normal] (hMN : M ≤ N)
    (hsol : Group.IsSolvable N) (hM1 : M ≠ ⊥)
    (hmin : ∀ M' : Subgroup H, M' ≤ M → M'.Normal → M' ≠ ⊥ → M' = M) :
    ∀ u ∈ M, ∀ v ∈ M, u * v = v * u := by
  have hMsol : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMN)
  have hnt : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM1
  have hD : ⁅M, M⁆ = ⊥ := by
    by_contra hD1
    have hDM : ⁅M, M⁆ = M := hmin _ (Subgroup.commutator_le_left M M) inferInstance hD1
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial M
    apply hlt.ne
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subtype_commutator, hDM, Subgroup.map_top, Subgroup.range_subtype]
  intro u hu v hv
  have h1 : ⁅u, v⁆ ∈ ⁅M, M⁆ := Subgroup.commutator_mem_commutator hu hv
  rw [hD, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

end MinimalNormal

section Main

variable {q : ℕ}

theorem bender_aux (hq : q.Prime) :
    ∀ (n : ℕ) (H : Type) [Group H] [Finite H] (N : Subgroup H) [N.Normal],
      Nat.card H = n → Odd (Nat.card N) → ∀ x : H, x * x = 1 →
      Subgroup.normalClosure ({x} : Set H) = ⊤ → ¬ q ∣ N.index →
      ¬ q ∣ ((Subgroup.centralizer ({x} : Set H)).subgroupOf N).index → ¬ q ∣ Nat.card N := by
  have : Fact q.Prime := ⟨hq⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ N _ hn hNodd x hx2 hxcl hNidx hxidx hqN
  have hN1 : N ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hqN
    exact hq.not_dvd_one hqN
  have hNsol : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  obtain ⟨M, hMN, hMn, hM1, hMmin⟩ := exists_minimal_normal_le N hN1
  have hMcomm := comm_of_minimal_normal hMN hNsol hM1 hMmin
  set π := QuotientGroup.mk' M with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective M
  have hcardH : Nat.card H = Nat.card (H ⧸ M) * Nat.card M :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hMcard : 2 ≤ Nat.card M := by
    have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM1
    have := Finite.one_lt_card (α := M)
    omega
  have hlt : Nat.card (H ⧸ M) < n := by
    have : 0 < Nat.card (H ⧸ M) := Nat.card_pos
    rw [← hn, hcardH]
    nlinarith
  have hÑn : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  have hidxÑ : (N.map π).index = N.index := by
    rw [← Subgroup.index_comap_of_surjective (N.map π) hπ, Subgroup.comap_map_eq,
      QuotientGroup.ker_mk', sup_eq_left.2 hMN]
  have hNcard : Nat.card N = Nat.card (N.map π) * Nat.card M := by
    have e1 := N.card_mul_index
    have e2 := (N.map π).card_mul_index
    have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card N * N.index = Nat.card H := e1
      _ = Nat.card (H ⧸ M) * Nat.card M := hcardH
      _ = (Nat.card (N.map π) * (N.map π).index) * Nat.card M := by rw [e2]
      _ = Nat.card (N.map π) * Nat.card M * N.index := by rw [hidxÑ]; ring
  have hodd' : Odd (Nat.card (N.map π)) := Odd.of_dvd_nat hNodd ⟨_, hNcard⟩
  have hx2' : π x * π x = 1 := by rw [← map_mul, hx2, map_one]
  have hxcl' : Subgroup.normalClosure ({π x} : Set (H ⧸ M)) = ⊤ := by
    have h := Subgroup.map_normalClosure ({x} : Set H) π hπ
    rw [Set.image_singleton, hxcl, Subgroup.map_top_of_surjective π hπ] at h
    exact h.symm
  have hidx' : ¬ q ∣ (N.map π).index := hidxÑ ▸ hNidx
  have hxidx' : ¬ q ∣
      ((Subgroup.centralizer ({π x} : Set (H ⧸ M))).subgroupOf (N.map π)).index := by
    set f := π.subgroupMap N with hf
    have hfsurj : Function.Surjective f := MonoidHom.subgroupMap_surjective π N
    set Cx := (Subgroup.centralizer ({x} : Set H)).subgroupOf N with hCx
    have h1 : (Cx.map f).index ∣ Cx.index := Subgroup.index_map_dvd Cx hfsurj
    have hle : Cx.map f ≤
        (Subgroup.centralizer ({π x} : Set (H ⧸ M))).subgroupOf (N.map π) := by
      rintro _ ⟨c, hc, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have hc' : (c : H) * x = x * (c : H) :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hc)
      show π c * π x = π x * π c
      rw [← map_mul, ← map_mul, hc']
    intro hdvd
    exact hxidx (hdvd.trans ((Subgroup.index_dvd_of_le hle).trans h1))
  have hqÑ : ¬ q ∣ Nat.card (N.map π) := ih _ hlt (H ⧸ M) (N.map π) rfl hodd' (π x) hx2' hxcl'
    hidx' hxidx'
  have hqM : q ∣ Nat.card M := by
    have : q ∣ Nat.card (N.map π) * Nat.card M := hNcard ▸ hqN
    rcases (Nat.Prime.dvd_mul hq).1 this with h | h
    · exact absurd h hqÑ
    · exact h
  have hqodd : q ≠ 2 := by
    intro h2
    have := Odd.of_dvd_nat hNodd (h2 ▸ hqN)
    exact absurd this (by decide)
  obtain ⟨m, hm⟩ := exists_prime_orderOf_dvd_card' (G := M) q hqM
  have hm1 : (m : H) ≠ 1 := by
    intro h
    have : m = 1 := Subtype.ext h
    rw [this, orderOf_one] at hm
    exact hq.ne_one hm.symm
  have hmq : (m : H) ^ q = 1 := by
    have : m ^ q = 1 := hm ▸ pow_orderOf_eq_one m
    simpa using congrArg Subtype.val this
  let E : Subgroup H :=
    { carrier := {y | y ∈ M ∧ y ^ q = 1}
      mul_mem' := fun {a b} ha hb => ⟨M.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hMcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨M.one_mem, one_pow _⟩
      inv_mem' := fun {a} ha => ⟨M.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hEn : E.Normal :=
    ⟨fun y hy c => ⟨hMn.conj_mem y hy.1 c, by
      show (c * y * c⁻¹) ^ q = 1
      rw [conj_pow, hy.2]; group⟩⟩
  have hEM : E ≤ M := fun y hy => hy.1
  have hE1 : E ≠ ⊥ := by
    intro hE
    have hmE : (m : H) ∈ E := ⟨m.2, hmq⟩
    rw [hE, Subgroup.mem_bot] at hmE
    exact hm1 hmE
  have hEeq : E = M := hMmin E hEM hEn hE1
  have hMexp : ∀ y ∈ M, y ^ q = 1 := fun y hy => (show y ∈ E by rw [hEeq]; exact hy).2
  have hMq : IsPGroup q M := fun y => ⟨1, Subtype.ext (by simpa using hMexp (y : H) y.2)⟩
  have hMC : ∀ y ∈ M, x * y = y * x := by
    set A : Subgroup N := (Subgroup.centralizer ({x} : Set H)).subgroupOf N with hA
    let _ : MulAction M (N ⧸ A) := MulAction.compHom (N ⧸ A) (Subgroup.inclusion hMN)
    obtain ⟨c, hc⟩ := hMq.nonempty_fixed_point_of_prime_not_dvd_card (N ⧸ A) hxidx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective c
    intro y hy
    have hyN : y ∈ N := hMN hy
    have hm' : (n : H) * y⁻¹ * (n : H)⁻¹ ∈ M := hMn.conj_mem _ (M.inv_mem hy) _
    have hfix := MulAction.mem_fixedPoints.1 hc ⟨_, hm'⟩
    have hfix2 : (QuotientGroup.mk (Subgroup.inclusion hMN ⟨_, hm'⟩ * n) : N ⧸ A) =
        QuotientGroup.mk n := hfix
    have hmem := QuotientGroup.eq.1 hfix2
    have hyA : (⟨y, hyN⟩ : N) ∈ A := by
      have e : (Subgroup.inclusion hMN ⟨_, hm'⟩ * n)⁻¹ * n = (⟨y, hyN⟩ : N) := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
        group
      rw [← e]
      exact hmem
    exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_subgroupOf.1 hyA)).symm
  have hMcent : ∀ y ∈ M, ∀ h : H, h * y = y * h := by
    have hCn : (Subgroup.centralizer (M : Set H)).Normal := by
      refine ⟨fun c hc g => ?_⟩
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ M := by simpa using hMn.conj_mem y hy g⁻¹
      have h1 := hc _ hy'
      calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * c * g⁻¹ * y := by group
    have hxC : x ∈ Subgroup.centralizer (M : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hMC y hy).symm
    have hle : Subgroup.normalClosure ({x} : Set H) ≤ Subgroup.centralizer (M : Set H) :=
      Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2 hxC)
    intro y hy h
    have hh : h ∈ Subgroup.centralizer (M : Set H) := hle (by rw [hxcl]; exact Subgroup.mem_top h)
    exact (Subgroup.mem_centralizer_iff.1 hh y hy).symm
  have hMzp : M = Subgroup.zpowers (m : H) := by
    have hzn : (Subgroup.zpowers (m : H)).Normal := by
      refine ⟨fun z hz g => ?_⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      have hcg : g * (m : H) = (m : H) * g := hMcent m m.2 g
      have hcj : g * (m : H) ^ j = (m : H) ^ j * g :=
        (Commute.zpow_right (show Commute g (m : H) from hcg) j).eq
      rw [hcj, mul_inv_cancel_right]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j
    have hzM : Subgroup.zpowers (m : H) ≤ M := Subgroup.zpowers_le.2 m.2
    have hz1 : Subgroup.zpowers (m : H) ≠ ⊥ := fun h => hm1 (Subgroup.zpowers_eq_bot.1 h)
    exact (hMmin _ hzM hzn hz1).symm
  have hMcardq : Nat.card M = q := by
    rw [hMzp]
    simp [hm]
  have hMidx : ¬ q ∣ M.index := by
    have e := Subgroup.relIndex_mul_index hMN
    have e2 := (M.subgroupOf N).card_mul_index
    have e3 : Nat.card (M.subgroupOf N) = Nat.card M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
    rw [e3] at e2
    have hrel : M.relIndex N = Nat.card (N.map π) := by
      apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card M from Nat.card_pos)
      rw [show Nat.card M * M.relIndex N = Nat.card N from e2, hNcard, mul_comm]
    rw [← e, hrel]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · exact hqÑ h
    · exact hNidx h
  let P : Sylow q H := hMq.toSylow hMidx
  have hPM : (P : Subgroup H) = M := IsPGroup.toSylow_coe hMq hMidx
  have hP : Subgroup.normalizer ((P : Subgroup H) : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyM : y ∈ M := by rw [← hPM]; exact hy
    exact (hMcent y hyM g).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hKn : (MonoidHom.transferSylow P hP).ker.Normal := MonoidHom.normal_ker _
  obtain ⟨⟨⟨k, hk⟩, ⟨p, hp⟩⟩, hkp⟩ := hcompl.2 x
  have hpM : p ∈ M := by rw [← hPM]; exact hp
  have hxkp : k * p = x := hkp
  have hp2 : p ^ 2 = 1 := by
    have hcomm : p * k = k * p := (hMcent p hpM k).symm
    have h1 : (k * p) * (k * p) = 1 := by rw [hxkp]; exact hx2
    have h2 : (k * k) * (p * p) = 1 := by
      calc (k * k) * (p * p) = k * (k * p) * p := by group
        _ = k * (p * k) * p := by rw [← hcomm]
        _ = (k * p) * (k * p) := by group
        _ = 1 := h1
    have hkk : k * k ∈ (MonoidHom.transferSylow P hP).ker := Subgroup.mul_mem _ hk hk
    have hpp : p * p ∈ (P : Subgroup H) := Subgroup.mul_mem _ hp hp
    have hpp' : p * p = (k * k)⁻¹ := eq_inv_of_mul_eq_one_right h2
    have hmem : p * p ∈ (MonoidHom.transferSylow P hP).ker := by
      rw [hpp']; exact Subgroup.inv_mem _ hkk
    have hdis := hcompl.disjoint
    have : p * p ∈ (MonoidHom.transferSylow P hP).ker ⊓ (P : Subgroup H) := ⟨hmem, hpp⟩
    rw [hdis.eq_bot, Subgroup.mem_bot] at this
    rw [sq]; exact this
  have hp1 : p = 1 := by
    have hpq : p ^ q = 1 := hMexp p hpM
    have hcop : Nat.Coprime q 2 := by
      rw [Nat.Prime.coprime_iff_not_dvd hq]
      intro h
      exact hqodd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h)
    have := pow_gcd_eq_one.2 ⟨hpq, hp2⟩
    rwa [hcop, pow_one] at this
  have hxK : x ∈ (MonoidHom.transferSylow P hP).ker := by
    rw [← hxkp, hp1, mul_one]; exact hk
  have hle : Subgroup.normalClosure ({x} : Set H) ≤ (MonoidHom.transferSylow P hP).ker :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.2 hxK)
  rw [hxcl, top_le_iff] at hle
  have hPbot : (P : Subgroup H) = ⊥ := by
    have hdis := hcompl.disjoint
    rw [hle] at hdis
    exact disjoint_top.1 hdis.symm
  exact hM1 (by rw [← hPM]; exact hPbot)

theorem bender_two_one {G : Type} [Group G] [Finite G] {H N P : Subgroup G} {x : G} {q : ℕ}
    (hq : q.Prime) (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) (hxH : x ∈ H) (hx2 : x * x = 1)
    (hgen : H ≤ Subgroup.closure {y | ∃ h ∈ H, y = h * x * h⁻¹})
    (hqHN : ¬ q ∣ N.relIndex H) (hPidx : ¬ q ∣ P.relIndex N)
    (hPx : ∀ p ∈ P, p * x = x * p) : ¬ q ∣ Nat.card N := by
  classical
  let x' : H := ⟨x, hxH⟩
  have hnorm : (N.subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hNodd
  have hx2' : x' * x' = 1 := Subtype.ext hx2
  have hxcl : Subgroup.normalClosure ({x'} : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hle : H ≤ (Subgroup.normalClosure ({x'} : Set H)).map H.subtype := by
      refine hgen.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨h, hh, rfl⟩
      refine ⟨⟨h, hh⟩ * x' * ⟨h, hh⟩⁻¹, ?_, rfl⟩
      exact (Subgroup.normalClosure_normal).conj_mem x'
        (Subgroup.subset_normalClosure (Set.mem_singleton x')) ⟨h, hh⟩
    obtain ⟨c, hc, hce⟩ := hle g.2
    have : c = g := Subtype.ext hce
    rwa [this] at hc
  have hidx' : ¬ q ∣ (N.subgroupOf H).index := hqHN
  have hxidx' : ¬ q ∣ ((Subgroup.centralizer ({x'} : Set H)).subgroupOf
      (N.subgroupOf H)).index := by
    have hle : (P.subgroupOf H).subgroupOf (N.subgroupOf H) ≤
        (Subgroup.centralizer ({x'} : Set H)).subgroupOf (N.subgroupOf H) := by
      intro p hp
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      have hp' : ((p : N.subgroupOf H) : H) ∈ P.subgroupOf H := Subgroup.mem_subgroupOf.1 hp
      have := hPx _ (Subgroup.mem_subgroupOf.1 hp')
      exact Subtype.ext this
    have hrel : ((P.subgroupOf H).subgroupOf (N.subgroupOf H)).index = P.relIndex N := by
      have := Subgroup.relIndex_subgroupOf (H := P) hNH
      exact this
    intro hdvd
    exact hPidx (hrel ▸ hdvd.trans (Subgroup.index_dvd_of_le hle))
  have := bender_aux hq _ H (N.subgroupOf H) rfl hodd' x' hx2' hxcl hidx' hxidx'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv] at this

end Main

end CFSG.CGT.T75H
