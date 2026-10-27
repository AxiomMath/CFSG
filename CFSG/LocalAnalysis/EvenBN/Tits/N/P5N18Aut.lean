module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Aut
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Lin
public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

section Aut

variable {U : Type*} [Group U] [Finite U]

theorem eq_one_of_fixed_orderOf_five (hU : Nat.card U = 16) {q : MulAut U} (hq : orderOf q = 5)
    {u : U} (hu : q u = u) : u = 1 := by
  classical
  have hq5 : q ^ 5 = 1 := by
    rw [← hq]
    exact pow_orderOf_eq_one q
  have hit : ∀ n : ℕ, ∀ a : U, (q ^ n) a = (fun b : U => q b)^[n] a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, Function.iterate_succ_apply', ih]
  have hf : ∀ a : U, (fun b : U => q b)^[5] a = a := fun a => by
    rw [← hit, hq5]
    rfl
  have hmod := CFSG.LocalAnalysis.EvenBN.Tits.N.P4.card_modEq_five_fixed (fun b : U => q b) hf
  have hcard : (Function.fixedPoints (fun b : U => q b)).ncard = Nat.card (fixSub q) := by
    rw [← Nat.card_coe_set_eq]
    rfl
  rw [hcard, hU] at hmod
  have hdvd : Nat.card (fixSub q) ∣ 16 := hU ▸ Subgroup.card_subgroup_dvd_card (fixSub q)
  have hdvd' : Nat.card (fixSub q) ∣ 2 ^ 4 := by norm_num; exact hdvd
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 4)).1 hdvd'
  have hcases : Nat.card (fixSub q) = 1 ∨ Nat.card (fixSub q) = 16 := by
    interval_cases i <;> simp_all [Nat.ModEq]
  rcases hcases with h1 | h16
  · have := Subgroup.card_eq_one.1 h1
    have hmem : u ∈ fixSub q := hu
    rw [this] at hmem
    exact Subgroup.mem_bot.1 hmem
  · exfalso
    have htop : fixSub q = ⊤ := (Subgroup.card_eq_iff_eq_top (fixSub q)).1 (by rw [h16, hU])
    have h1 : q = 1 := MulEquiv.ext fun a => by
      have : a ∈ fixSub q := by rw [htop]; trivial
      exact this
    rw [h1, orderOf_one] at hq
    exact absurd hq (by norm_num)

theorem card_le_five_of_isPGroup (hU : Nat.card U = 16) (P : Subgroup (MulAut U)) (hP : IsPGroup 5 P) :
    Nat.card P ≤ 5 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, u₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card U = 1 := Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
    omega
  have hinj : Function.Injective (fun p : P => (⟨(p : MulAut U) u₀, fun h => hu₀ ((map_eq_one_iff _
      (MulEquiv.injective _)).1 h)⟩ : {u : U // u ≠ 1})) := by
    intro p p' h
    have h' : (p : MulAut U) u₀ = (p' : MulAut U) u₀ := congrArg Subtype.val h
    by_contra hne
    set q : P := p⁻¹ * p' with hq
    have hq1 : q ≠ 1 := fun h1 => hne (by
      have : p' = p := by
        calc p' = p * (p⁻¹ * p') := by group
          _ = p * 1 := by rw [← hq, h1]
          _ = p := mul_one p
      exact this.symm)
    have hqu : ((q : P) : MulAut U) u₀ = u₀ := by
      show (((p⁻¹ * p' : P) : MulAut U)) u₀ = u₀
      have : ((p⁻¹ * p' : P) : MulAut U) = (p : MulAut U)⁻¹ * (p' : MulAut U) := rfl
      rw [this, MulAut.mul_apply, ← h']
      simp
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) q
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      rw [this, pow_zero, orderOf_eq_one_iff] at hk
      exact hq1 hk
    set q' : P := q ^ (5 ^ (k - 1)) with hq'
    have hq'ord : orderOf q' = 5 := by
      rw [hq', orderOf_pow_of_dvd (by positivity) (by
        rw [hk]
        exact pow_dvd_pow 5 (Nat.sub_le k 1)), hk]
      rw [show 5 ^ k = 5 ^ (k - 1 + 1) by rw [Nat.sub_add_cancel hk1], pow_succ]
      exact Nat.mul_div_cancel_left 5 (by positivity)
    have hq'ord' : orderOf ((q' : P) : MulAut U) = 5 := by
      rw [Subgroup.orderOf_coe]
      exact hq'ord
    have hq'u : ((q' : P) : MulAut U) u₀ = u₀ := by
      have : ∀ n : ℕ, (((q ^ n : P)) : MulAut U) u₀ = u₀ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Subgroup.coe_mul, MulAut.mul_apply, ih, hqu]
      exact this _
    exact hu₀ (eq_one_of_fixed_orderOf_five hU hq'ord' hq'u)
  have hcard15 : Nat.card {u : U // u ≠ 1} = 15 := by
    haveI := Fintype.ofFinite U
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, hU]
  have hle : Nat.card P ≤ 15 := hcard15 ▸ Nat.card_le_card_of_injective _ hinj
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.1 hP)
  rw [hn] at hle ⊢
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have : 5 ^ 2 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) h
    omega
  calc 5 ^ n ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 5 := by norm_num

end Aut

section NoOdd

variable {X : Type*} [Group X] [Finite X]

theorem no_odd_normal {U K : Subgroup X} {x : X} (hU : IsElemAbelian 2 U) (hU16 : Nat.card U = 16)
    (hxN : x ∈ normalizer (U : Set X)) (hx5 : x ^ 5 = 1)
    (hfpf : ∀ u ∈ U, x * u * x⁻¹ = u → u = 1) (hKN : K ≤ normalizer (U : Set X)) (hxK : x ∈ K)
    (h5 : ∀ N : Subgroup (MulAut ↥U), N ≤ imgIn U K →
      (∀ h ∈ imgIn U K, ∀ n ∈ N, h * n * h⁻¹ ∈ N) → actFun U x ∈ N → Even (Nat.card N))
    {B₀ : Subgroup (MulAut ↥U)} (hB₀ : B₀ ≤ imgIn U (normalizer (U : Set X)))
    (hBn : ∀ h ∈ imgIn U (normalizer (U : Set X)), ∀ b ∈ B₀, h * b * h⁻¹ ∈ B₀)
    (hodd : Odd (Nat.card B₀)) (htr : ∀ a b : ↥U, a ≠ 1 → b ≠ 1 → ∃ g ∈ B₀, g a = b) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set B₁ := imgIn U (normalizer (U : Set X)) with hB₁
  have hxB₁ : actFun U x ∈ B₁ := actFun_mem_imgIn hxN hxN
  have hxh1 : actFun U x ≠ 1 := by
    intro h1
    have hc := (actFun_eq_one_iff U hxN).1 h1
    have hall : ∀ u ∈ U, u = 1 := fun u hu =>
      hfpf u hu (by
        have := mem_centralizer_iff.1 hc u hu
        rw [← this]
        group)
    have : Nat.card U = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)⟩, ⟨1⟩⟩
    omega
  have hxh5 : actFun U x ^ 5 = 1 := by
    rw [← actFun_pow U hxN, hx5, actFun_one]
  have hxhord : orderOf (actFun U x) = 5 := orderOf_eq_prime hxh5 hxh1
  have h15 : 15 ∣ Nat.card B₀ := by
    obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ↥U, u₀ ≠ 1 := by
      by_contra h
      push Not at h
      have : Nat.card U = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => (h a).trans (h b).symm⟩, ⟨1⟩⟩
      omega
    have horb : MulAction.orbit B₀ u₀ = {u : ↥U | u ≠ 1} := by
      ext u
      constructor
      · rintro ⟨g, rfl⟩
        intro h1
        apply hu₀
        have : (g : MulAut ↥U) u₀ = 1 := h1
        exact (map_eq_one_iff _ (MulEquiv.injective _)).1 this
      · intro hu
        obtain ⟨g, hg, hgu⟩ := htr u₀ u hu₀ hu
        exact ⟨⟨g, hg⟩, hgu⟩
    have hcard : Nat.card (MulAction.orbit B₀ u₀) = 15 := by
      rw [horb]
      haveI := Fintype.ofFinite ↥U
      have : Nat.card ↥{u : ↥U | u ≠ 1} = Nat.card {u : ↥U // u ≠ 1} := rfl
      rw [this, Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        ← Nat.card_eq_fintype_card, hU16]
    have := Subgroup.card_mul_index (MulAction.stabilizer B₀ u₀)
    have hnc : (MulAction.orbit B₀ u₀).ncard = 15 := by
      rw [← Nat.card_coe_set_eq]
      exact hcard
    rw [MulAction.index_stabilizer, hnc] at this
    exact ⟨Nat.card (MulAction.stabilizer B₀ u₀), by rw [← this, mul_comm]⟩
  have h5B : 5 ∣ Nat.card B₀ := (Dvd.intro 3 (by norm_num)).trans h15
  set B₀' : Subgroup ↥B₁ := B₀.subgroupOf B₁ with hB₀'
  haveI hnorm : B₀'.Normal := ⟨fun n hn g => by
    have := hBn g.1 g.2 n.1 hn
    exact this⟩
  have hcardB₀' : Nat.card B₀' = Nat.card B₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀).toEquiv
  have hm : ¬ 5 ∣ B₀'.index := by
    intro hm5
    have h25 : 5 ^ 2 ∣ Nat.card ↥B₁ := by
      rw [← Subgroup.card_mul_index B₀', hcardB₀', pow_two]
      exact Nat.mul_dvd_mul h5B hm5
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 5 h25
    have hP : IsPGroup 5 ↥(K'.map B₁.subtype) :=
      IsPGroup.of_card (n := 2) (by rw [Subgroup.card_map_of_injective B₁.subtype_injective, hK'])
    have := card_le_five_of_isPGroup hU16 _ hP
    rw [Subgroup.card_map_of_injective B₁.subtype_injective, hK'] at this
    omega
  have hxhB₀ : actFun U x ∈ B₀ := by
    have hcop : (B₀'.index).Coprime (orderOf (⟨actFun U x, hxB₁⟩ : ↥B₁)) := by
      rw [Subgroup.orderOf_mk, hxhord]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hm).symm
    have hmem := pow_index_mem B₀' (⟨actFun U x, hxB₁⟩ : ↥B₁)
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime hcop
    have := pow_mem hmem k
    rw [hk] at this
    exact this
  have hKB : imgIn U K ≤ B₁ := imgIn_mono U hKN
  have hxKimg : actFun U x ∈ imgIn U K := actFun_mem_imgIn hxK hxN
  have hev := h5 (B₀ ⊓ imgIn U K) inf_le_right
    (fun h hh n hn => ⟨hBn h (hKB hh) n hn.1, mul_mem (mul_mem hh hn.2) (Subgroup.inv_mem _ hh)⟩)
    ⟨hxhB₀, hxKimg⟩
  have hdvd : Nat.card ↥(B₀ ⊓ imgIn U K) ∣ Nat.card B₀ := Subgroup.card_dvd_of_le inf_le_left
  exact (Nat.not_even_iff_odd.2 (Odd.of_dvd_nat hodd hdvd)) hev

end NoOdd


end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
