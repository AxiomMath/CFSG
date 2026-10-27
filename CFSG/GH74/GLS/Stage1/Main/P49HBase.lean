module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.GLS.Basic

public section

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H

theorem oPrimeResidual_two_normal (X : Type*) [Group X] : (oPrimeResidual 2 X).Normal := by
  constructor
  intro n hn g
  unfold oPrimeResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨k, ?_⟩
    rw [conj_pow, hk]
    group
  | one => simp
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ ha

section Generic

variable {Y : Type} [Group Y]

theorem isPGroup_le_oPrimeResidual {H : Subgroup Y} (hH : IsPGroup 2 H) : H ≤ oPrimeResidual 2 Y := by
  intro x hx
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  exact Subgroup.subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem le_oPrimeResidual_of_quasisimple [Finite Y] {Kb : Subgroup Y} (hKq : IsQuasisimple ↥Kb) : Kb ≤ oPrimeResidual 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (oPrimeResidual 2 Y).Normal := oPrimeResidual_two_normal Y
  set M : Subgroup ↥Kb := (oPrimeResidual 2 Y).subgroupOf Kb with hM
  have : M.Normal := Subgroup.Normal.subgroupOf inferInstance Kb
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥Kb) := inferInstance
  have hSM : (S : Subgroup ↥Kb) ≤ M := by
    intro x hx
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx⟩
    refine Subgroup.subset_closure ⟨k, ?_⟩
    have := congrArg (fun z : ↥S => ((z : ↥Kb) : Y)) hk
    simpa using this
  have hodd : Odd M.index := by
    have h1 : M.index ∣ (S : Subgroup ↥Kb).index := Subgroup.index_dvd_of_le hSM
    have h2 : ¬ 2 ∣ (S : Subgroup ↥Kb).index := S.not_dvd_index
    exact Odd.of_dvd_nat (Nat.odd_iff.2 (by omega)) h1
  have : Group.IsPerfect ↥Kb := hKq.1
  have : Group.IsPerfect (↥Kb ⧸ M) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective M)
  have : Group.IsSolvable (↥Kb ⧸ M) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hsub : Subsingleton (↥Kb ⧸ M) := by
    by_contra hns
    have : Nontrivial (↥Kb ⧸ M) := not_subsingleton_iff_nontrivial.1 hns
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (↥Kb ⧸ M)
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  have hMtop : M = ⊤ := by
    rw [← Subgroup.index_eq_one]
    have : Nat.card (↥Kb ⧸ M) = 1 := Nat.card_unique
    exact this
  intro x hx
  have : (⟨x, hx⟩ : ↥Kb) ∈ M := hMtop ▸ Subgroup.mem_top _
  exact this


theorem exists_sylow_eq_of_isSylowOf_top [Finite Y] {T : Subgroup Y} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ P : Sylow 2 Y, (P : Subgroup Y) = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hP, hdvd⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (G := Y) (p := 2) (P := T) (K := ⊤)).1
    (by convert hT)
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, rfl⟩

theorem exists_conj_mem_sylow [Finite Y] {T : Subgroup Y} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {g : Y}
    {k : ℕ} (hg : g ^ (2 ^ k) = 1) : ∃ y : Y, y * g * y⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P0, hP0⟩ := exists_sylow_eq_of_isSylowOf_top hT
  have hz : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card_dvd_pow (n := k) (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨P', hP'⟩ := hz.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P' P0
  refine ⟨y, ?_⟩
  rw [← hP0, ← hy, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨g, hP' (mem_zpowers g), by simp [MulAut.smul_def, MulAut.conj_apply]⟩

end Generic

section Out

variable {Y : Type} [Group Y]

theorem commutator_mem_sup {Kb : Subgroup Y} (hKn : Kb.Normal)
    (hout : ∀ α β : MulAut ↥Kb, ∃ k : ↥Kb, α * β * α⁻¹ * β⁻¹ = MulAut.conj k) (y₁ y₂ : Y) :
    ⁅y₁, y₂⁆ ∈ Kb ⊔ centralizer (Kb : Set Y) := by
  have := hKn
  obtain ⟨k, hk⟩ := hout (MulAut.conjNormal y₁) (MulAut.conjNormal y₂)
  set c : Y := ⁅y₁, y₂⁆ with hcdef
  have hcomm : (MulAut.conjNormal c : MulAut ↥Kb) =
      MulAut.conjNormal y₁ * MulAut.conjNormal y₂ * (MulAut.conjNormal y₁)⁻¹ *
        (MulAut.conjNormal y₂)⁻¹ := by
    rw [hcdef, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  have key : ∀ x ∈ Kb, c * x * c⁻¹ = (k : Y) * x * (k : Y)⁻¹ := by
    intro x hx
    have h1 : ((MulAut.conjNormal c : MulAut ↥Kb) ⟨x, hx⟩ : Y) =
        ((MulAut.conj k : MulAut ↥Kb) ⟨x, hx⟩ : Y) := by rw [hcomm, hk]
    rw [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    exact h1
  have hd : (k : Y)⁻¹ * c ∈ centralizer (Kb : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : c * x = (k : Y) * x * (k : Y)⁻¹ * c := by
      have := key x hx
      calc c * x = (c * x * c⁻¹) * c := by group
        _ = (k : Y) * x * (k : Y)⁻¹ * c := by rw [this]
    calc x * ((k : Y)⁻¹ * c) = (k : Y)⁻¹ * ((k : Y) * x * (k : Y)⁻¹ * c) := by group
      _ = (k : Y)⁻¹ * (c * x) := by rw [h1]
      _ = (k : Y)⁻¹ * c * x := by group
  have hsplit : c = (k : Y) * ((k : Y)⁻¹ * c) := by group
  rw [hsplit]
  exact Subgroup.mul_mem_sup k.2 hd

theorem oPrimeResidual_le_sup [Finite Y] {Kb : Subgroup Y} (hKn : Kb.Normal)
    (hout : ∀ α β : MulAut ↥Kb, ∃ k : ↥Kb, α * β * α⁻¹ * β⁻¹ = MulAut.conj k) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    oPrimeResidual 2 Y ≤ (Kb ⊔ centralizer (Kb : Set Y)) ⊔ T := by
  unfold oPrimeResidual
  rw [Subgroup.closure_le]
  rintro g ⟨k, hk⟩
  obtain ⟨y, hy⟩ := exists_conj_mem_sylow hT hk
  have hc := commutator_mem_sup hKn hout y⁻¹ (y * g * y⁻¹)
  have hg : g = ⁅y⁻¹, y * g * y⁻¹⁆ * (y * g * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hg]
  exact Subgroup.mul_mem_sup hc hy

theorem mem_of_pow_three [Finite Y] {N₀ T : Subgroup Y} [N₀.Normal]
    (hres : oPrimeResidual 2 Y ≤ N₀ ⊔ T) (hT2 : IsPGroup 2 T) {c : Y} (hc : c ∈ oPrimeResidual 2 Y)
    {a : ℕ} (hc3 : c ^ (3 ^ a) = 1) : c ∈ N₀ := by
  obtain ⟨m, hm, t, ht, hmt⟩ := Subgroup.mem_sup_of_normal_left.1 (hres hc)
  obtain ⟨f, hf⟩ := hT2 ⟨t, ht⟩
  have htf : t ^ (2 ^ f) = 1 := by simpa using congrArg Subtype.val hf
  have h1 : (QuotientGroup.mk' N₀ c) ^ (3 ^ a) = 1 := by rw [← map_pow, hc3, map_one]
  have h2 : (QuotientGroup.mk' N₀ c) ^ (2 ^ f) = 1 := by
    have hm1 : QuotientGroup.mk' N₀ m = 1 := (QuotientGroup.eq_one_iff m).2 hm
    have : QuotientGroup.mk' N₀ c = QuotientGroup.mk' N₀ t := by
      rw [← hmt, map_mul, hm1, one_mul]
    rw [this, ← map_pow, htf, map_one]
  have hcop : Nat.Coprime (3 ^ a) (2 ^ f) := Nat.Coprime.pow a f (by norm_num)
  have h3 : (QuotientGroup.mk' N₀ c) ^ (Nat.gcd (3 ^ a) (2 ^ f)) = 1 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [hcop, pow_one] at h3
  exact (QuotientGroup.eq_one_iff c).1 h3

end Out

section Orders

variable {Y : Type} [Group Y] [Finite Y]

theorem factorization_eq_of_isSylowOf {P K : Subgroup Y} {n : ℕ} (h : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hcard : Nat.card P = 2 ^ n) : (Nat.card K).factorization 2 = n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := h.card_eq
  rw [hcard] at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm

omit [Finite Y] in
theorem card_sup_centralizer_mul {Kb : Subgroup Y} (hKn : Kb.Normal) :
    Nat.card ↥(Kb ⊔ centralizer (Kb : Set Y)) * Nat.card ↥(Kb ⊓ centralizer (Kb : Set Y)) =
      Nat.card ↥Kb * Nat.card ↥(centralizer (Kb : Set Y)) := by
  have := hKn
  set D := centralizer (Kb : Set Y) with hD
  have h1 := Subgroup.relIndex_mul_card Kb (Kb ⊔ D)
  rw [inf_eq_left.2 le_sup_left, Subgroup.relIndex_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card Kb D
  calc Nat.card ↥(Kb ⊔ D) * Nat.card ↥(Kb ⊓ D)
      = (Kb.relIndex D * Nat.card ↥Kb) * Nat.card ↥(Kb ⊓ D) := by rw [h1]
    _ = Nat.card ↥Kb * (Kb.relIndex D * Nat.card ↥(Kb ⊓ D)) := by ring
    _ = Nat.card ↥Kb * Nat.card ↥D := by rw [h2]

theorem card_inf_sup {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hP : Nat.card ↥(T ⊓ Kb) = 2 ^ n)
    (hQ : Nat.card ↥(T ⊓ centralizer (Kb : Set Y)) = 2 ^ n)
    (hZ : Nat.card ↥(Kb ⊓ centralizer (Kb : Set Y)) = 2) :
    Nat.card ↥(T ⊓ (Kb ⊔ centralizer (Kb : Set Y))) = 2 ^ (2 * n - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hKn
  set D := centralizer (Kb : Set Y) with hD
  have : D.Normal := inferInstance
  have : (Kb ⊔ D).Normal := inferInstance
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ Kb) Kb :=
    hT.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hSD : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ D) D :=
    hT.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hSN : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ (Kb ⊔ D)) (Kb ⊔ D) :=
    hT.inf_of_le_normalizer le_top Subgroup.le_normalizer_of_normal
  have hvK := factorization_eq_of_isSylowOf hSK hP
  have hvD := factorization_eq_of_isSylowOf hSD hQ
  have hprod := card_sup_centralizer_mul hKn
  rw [hZ] at hprod
  have h0 : Nat.card ↥(Kb ⊔ D) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card ↥Kb ≠ 0 := Nat.card_pos.ne'
  have hD0 : Nat.card ↥D ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card ↥(Kb ⊔ D)).factorization 2 = 2 * n - 1 := by
    have h1 : (Nat.card ↥(Kb ⊔ D) * 2).factorization 2 = (Nat.card ↥Kb * Nat.card ↥D).factorization 2 := by
      rw [hprod]
    rw [Nat.factorization_mul h0 two_ne_zero, Nat.factorization_mul hK0 hD0] at h1
    simp only [Finsupp.add_apply, hvK, hvD, Nat.Prime.factorization_self Nat.prime_two] at h1
    omega
  rw [hSN.card_eq, hv]

theorem relIndex_sup_centralizer_eq_two {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hP : Nat.card ↥(T ⊓ Kb) = 2 ^ n)
    (hQ : Nat.card ↥(T ⊓ centralizer (Kb : Set Y)) = 2 ^ n)
    (hZ : Nat.card ↥(Kb ⊓ centralizer (Kb : Set Y)) = 2) (hTcard : Nat.card ↥T = 2 ^ (2 * n))
    (hn : 1 ≤ n) : (Kb ⊔ centralizer (Kb : Set Y)).relIndex T = 2 := by
  have hc := card_inf_sup hKn hT hP hQ hZ
  set N₀ := Kb ⊔ centralizer (Kb : Set Y) with hN₀
  set H : Subgroup ↥T := (T ⊓ N₀).subgroupOf T with hH
  have hHcard : Nat.card ↥H = 2 ^ (2 * n - 1) := by
    rw [← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ N₀ ≤ T)).toEquiv
  have hidx : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    rw [hHcard, hTcard] at h1
    have h2 : 2 ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  calc N₀.relIndex T = (N₀ ⊓ T).relIndex T := (Subgroup.inf_relIndex_right N₀ T).symm
    _ = (T ⊓ N₀).relIndex T := by rw [inf_comm]
    _ = 2 := hidx

theorem sq_mem_sup_centralizer {Kb : Subgroup Y} (hKn : Kb.Normal) {T : Subgroup Y}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {n : ℕ} (hP : Nat.card ↥(T ⊓ Kb) = 2 ^ n)
    (hQ : Nat.card ↥(T ⊓ centralizer (Kb : Set Y)) = 2 ^ n)
    (hZ : Nat.card ↥(Kb ⊓ centralizer (Kb : Set Y)) = 2) (hTcard : Nat.card ↥T = 2 ^ (2 * n))
    (hn : 1 ≤ n) {s : Y} (hs : s ∈ T) : s ^ 2 ∈ Kb ⊔ centralizer (Kb : Set Y) := by
  have hidx := relIndex_sup_centralizer_eq_two hKn hT hP hQ hZ hTcard hn
  set N₀ := Kb ⊔ centralizer (Kb : Set Y) with hN₀
  set H : Subgroup ↥T := N₀.subgroupOf T with hH
  have hidx' : H.index = 2 := hidx
  have : H.Normal := Subgroup.normal_of_index_eq_two hidx'
  have h3 := Subgroup.pow_index_mem H (⟨s, hs⟩ : ↥T)
  rw [hidx'] at h3
  exact Subgroup.mem_subgroupOf.1 h3

end Orders

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.P49H
