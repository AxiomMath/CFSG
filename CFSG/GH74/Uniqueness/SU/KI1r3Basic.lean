module

public import CFSG.GH74.Uniqueness.SU.SU1Graph
public import CFSG.GH74.Uniqueness.SU.SU1NormalFour
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralizerSylow
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.Uniqueness.SU.K.R3

open Subgroup CFSG CFSG.GH74.Uniqueness.SU
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

structure Cfg (H : Type) [Group H] [Finite H] (T : Sylow 2 H) (x : H) : Prop where
  odd : pPrimeCore 2 H = ⊥
  rank : 3 ≤ Open.twoRank H
  cen : center H = ⊥
  xT : x ∈ (T : Subgroup H)
  x2 : orderOf x = 2
  crk : Open.pRank 2 (centralizer ({x} : Set H)) = 2

omit [Finite H] in
theorem isElemAbelian_map_conj {E : Subgroup H} (hE : Open.IsElemAbelian 2 E) (g : H) :
    Open.IsElemAbelian 2 (E.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _

theorem Cfg.no_E8 {T : Sylow 2 H} {x : H} (h : Cfg H T x) {E : Subgroup H}
    (hE : Open.IsElemAbelian 2 E) (hcard : 8 ≤ Nat.card E) (g : H) : g⁻¹ * x * g ∉ E := by
  intro hmem
  set E' := E.map (MulAut.conj g).toMonoidHom with hE'
  have hE'el : Open.IsElemAbelian 2 E' := isElemAbelian_map_conj hE g
  have hxE' : x ∈ E' := ⟨g⁻¹ * x * g, hmem, by simp [MulAut.conj_apply]; group⟩
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hE'el
  have hk3 : 3 ≤ k := by
    have h8 : 8 ≤ 2 ^ k := hk ▸ hcardE' ▸ hcard
    by_contra hlt
    push Not at hlt
    interval_cases k <;> omega
  have hle : E' ≤ centralizer ({x} : Set H) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((SU1.isElemAbelian_iff.mp hE'el).1 x hxE' e he).symm
  have h1 := SU1.le_pRank (p := 2) (by norm_num) hle hE'el hk
  have h2 := h.crk
  omega

theorem card_ge_eight {E : Subgroup H} (hE : Open.IsElemAbelian 2 E) (h4 : 4 < Nat.card E) :
    8 ≤ Nat.card E := by
  obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hE
  rw [hk] at h4 ⊢
  by_contra hlt
  push Not at hlt
  have : k ≤ 2 := by
    by_contra hk3
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem sup_zpowers_ge_eight {U : Subgroup H} (hU : Open.IsElemAbelian 2 U) (hU4 : 4 ≤ Nat.card U)
    {x' : H} (hx' : x' * x' = 1) (hcomm : ∀ u ∈ U, u * x' = x' * u) (hxU : x' ∉ U) :
    Open.IsElemAbelian 2 (U ⊔ zpowers x') ∧ 8 ≤ Nat.card ↥(U ⊔ zpowers x') := by
  have hx2 : x' ^ 2 = 1 := by rw [pow_two]; exact hx'
  have hcomm' : ∀ u ∈ U, ∀ t ∈ zpowers x', u * t = t * u := by
    rintro u hu t ⟨n, rfl⟩
    exact ((Commute.zpow_right (show Commute u x' from hcomm u hu) n)).eq
  have hel := SU1.IsElemAbelian.sup hU (SU1.isElemAbelian_zpowers hx2) hcomm'
  refine ⟨hel, card_ge_eight hel ?_⟩
  have hlt : U < U ⊔ zpowers x' :=
    lt_of_le_of_ne le_sup_left (fun h => hxU (h ▸ Subgroup.mem_sup_right (mem_zpowers x')))
  have := SU1.card_lt_of_lt hlt
  omega

theorem Cfg.mul_self_x {T : Sylow 2 H} {x : H} (h : Cfg H T x) : x * x = 1 := by
  have hx2 : x ^ 2 = 1 := h.x2 ▸ pow_orderOf_eq_one x
  rw [← pow_two]; exact hx2

theorem Cfg.exists_normal {T : Sylow 2 H} {x : H} (h : Cfg H T x) :
    ∃ N : Subgroup H, N.Normal ∧ (∀ g : H, g ^ 2 ∈ N) ∧ x ∉ N := by
  have hxx := h.mul_self_x
  have hT2 : IsPGroup 2 (T : Subgroup H) := T.isPGroup'
  have hTrank : 3 ≤ Open.pRank 2 (T : Subgroup H) := by
    rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq T]
    exact h.rank
  obtain ⟨U, hUT, hTU, hUel, hUcard⟩ := SU1.exists_normal_fourGroup_of_pRank_ge_three hT2 hTrank
  have hNEp : SU1.IsNormalEp2 2 (T : Subgroup H) U := ⟨hUT, hTU, hUel, by simpa using hUcard⟩
  obtain ⟨-, hrel, hrk⟩ := SU1.ig10_20_ii Nat.prime_two hT2 hNEp
  obtain ⟨E, hEQ, hEel, hEcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two
    (H := centralizer (U : Set H) ⊓ (T : Subgroup H)) (k := 3) (by rw [hrk]; exact hTrank)
  have hEcomm : ∀ e ∈ E, ∀ u ∈ U, e * u = u * e := by
    intro e he u hu
    have := (Subgroup.mem_inf.mp (hEQ he)).1
    exact (Subgroup.mem_centralizer_iff.mp this u hu).symm
  have hQu : ∀ a : H, a⁻¹ * x * a ∉ centralizer (U : Set H) ⊓ (T : Subgroup H) := by
    intro a ha
    have haC := (Subgroup.mem_inf.mp ha).1
    have hx'x' : a⁻¹ * x * a * (a⁻¹ * x * a) = 1 := by
      calc a⁻¹ * x * a * (a⁻¹ * x * a) = a⁻¹ * (x * x) * a := by group
        _ = 1 := by rw [hxx]; group
    have hcomm : ∀ u ∈ U, u * (a⁻¹ * x * a) = (a⁻¹ * x * a) * u :=
      fun u hu => Subgroup.mem_centralizer_iff.mp haC u hu
    by_cases hx'U : a⁻¹ * x * a ∈ U
    · have hEU := SU1.IsElemAbelian.sup hEel hUel hEcomm
      have hcard : 8 ≤ Nat.card ↥(E ⊔ U) := by
        have h1 : Nat.card E ≤ Nat.card ↥(E ⊔ U) := Subgroup.card_le_of_le le_sup_left
        omega
      exact h.no_E8 hEU hcard a (Subgroup.mem_sup_right hx'U)
    · obtain ⟨hel, hc8⟩ := sup_zpowers_ge_eight hUel hUcard.ge hx'x' hcomm hx'U
      exact h.no_E8 hel hc8 a (Subgroup.mem_sup_right (mem_zpowers _))
  have hindex : (centralizer (U : Set H) ⊓ (T : Subgroup H)).relIndex (T : Subgroup H) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    have h0 := SU1.relIndex_ne_zero_of_finite (centralizer (U : Set H)) (T : Subgroup H)
    have h1 : (centralizer (U : Set H)).relIndex (T : Subgroup H) ≠ 1 := by
      intro h1
      have hle := (Subgroup.relIndex_eq_one.mp h1) h.xT
      exact hQu 1 (by simpa using Subgroup.mem_inf.mpr ⟨hle, h.xT⟩)
    omega
  exact Quasithin.thompson_transfer_exists_normal T inf_le_right hindex h.x2 hQu

omit [Finite H] in
theorem commutator_mem_of_sq_mem {N : Subgroup H} [N.Normal] (hsq : ∀ g : H, g ^ 2 ∈ N) (a b : H) :
    ⁅a, b⁆ ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  have hq : ∀ g : H, ((g : H ⧸ N)) ^ 2 = 1 := fun g => by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hsq g
  have ha := hq a
  have hb := hq b
  have hab := hq (a * b)
  have hinv : ∀ g : H ⧸ N, g ^ 2 = 1 → g⁻¹ = g := fun g hg =>
    (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hg))
  have hcomm : (a : H ⧸ N) * (b : H ⧸ N) = (b : H ⧸ N) * (a : H ⧸ N) := by
    have h1 : ((a : H ⧸ N) * (b : H ⧸ N))⁻¹ = (a : H ⧸ N) * (b : H ⧸ N) := by
      rw [← QuotientGroup.mk_mul]; exact hinv _ hab
    have h2 : ((a : H ⧸ N) * (b : H ⧸ N))⁻¹ = (b : H ⧸ N) * (a : H ⧸ N) := by
      rw [mul_inv_rev, hinv _ ha, hinv _ hb]
    rw [← h1, h2]
  rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm]
  group

theorem Cfg.x_notMem_of_perfect {T : Sylow 2 H} {x : H} (h : Cfg H T x) {K : Subgroup H}
    (hK : ⁅K, K⁆ = K) : x ∉ K := by
  obtain ⟨N, hN, hsq, hxN⟩ := h.exists_normal
  intro hxK
  apply hxN
  have : K ≤ N := by
    rw [← hK]
    refine (Subgroup.commutator_le).mpr ?_
    intro a _ b _
    exact commutator_mem_of_sq_mem hsq a b
  exact this hxK

end CFSG.GH74.Uniqueness.SU.K.R3
