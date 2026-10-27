module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SolStdInL

public section

namespace CFSG.EvenSporadicStandard.Induction.TMem

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem map_conj_eq_of_centralizes {A : Subgroup H} {c : H} (hc : ∀ a ∈ A, a * c = c * a) :
    A.map (MulAut.conj c).toMonoidHom = A := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    have : c * a * c⁻¹ = a := by
      have := hc a ha
      calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [this]
        _ = a := by group
    simpa [MulAut.conj_apply, this] using ha
  · intro hy
    refine ⟨y, hy, ?_⟩
    have : c * y * c⁻¹ = y := by
      have := hc y hy
      calc c * y * c⁻¹ = (y * c) * c⁻¹ := by rw [this]
        _ = y := by group
    simpa [MulAut.conj_apply] using this

omit [Finite H] in
theorem conj_centralizes {A : Subgroup H} {x u z : H} (hz : x * u * x⁻¹ = z)
    (h : ∀ k ∈ A, k * z = z * k) :
    ∀ k ∈ A.map (MulAut.conj x⁻¹).toMonoidHom, k * u = u * k := by
  rintro _ ⟨k, hk, rfl⟩
  have h1 := h k hk
  rw [← hz] at h1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc x⁻¹ * k * x * u = x⁻¹ * (k * (x * u * x⁻¹)) * x := by group
    _ = x⁻¹ * ((x * u * x⁻¹) * k) * x := by rw [h1]
    _ = u * (x⁻¹ * k * x) := by group

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  hA.of_mulEquiv e.symm

omit [Finite H] in
theorem card_centralizer_subgroupOf {N K : Subgroup H} (hKN : K ≤ N) :
    Nat.card ↥(centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N)) =
      Nat.card ↥(N ⊓ centralizer (K : Set H)) := by
  have h : (centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N)).map N.subtype =
      N ⊓ centralizer (K : Set H) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype, mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun k hk => ?_⟩
      have := hy ⟨k, hKN hk⟩ (by simpa [mem_subgroupOf] using hk)
      exact congrArg Subtype.val this
    · rintro ⟨hxN, hx⟩
      refine ⟨⟨x, hxN⟩, fun k hk => ?_, rfl⟩
      exact Subtype.ext (hx k (mem_subgroupOf.1 hk))
  rw [← h, Subgroup.card_map_of_injective N.subtype_injective]

theorem lt_two_pow_twoAdic {K : Subgroup H} {m n : ℕ} (hdvd : 2 ^ m ∣ Nat.card ↥K)
    (hn : n < 2 ^ m) : n < 2 ^ twoAdic K := by
  have h1 : m ≤ twoAdic K :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  exact hn.trans_le (Nat.pow_le_pow_right (by norm_num) h1)

omit [Finite H] in
theorem inL_of_solStd' {X : Type} [Group X] {M : Subgroup X} (h : SolStd M) : InL M :=
  h.inL

structure TMemData (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (u : H) : Prop where
  LN : L ≤ N
  odd : OddCN N L
  u_mem : u ∈ L
  u_order : orderOf u = 2
  h38 : centralizer ({u} : Set H) ≤ normalizer (L : Set H)
  MK : ∀ b ∈ normalizer (L : Set H), (∀ k ∈ K, b * k = k * b) → b ∈ L ⊔ centralizer (L : Set H)
  Mperf : ∀ P : Subgroup H, P ≤ normalizer (L : Set H) → Group.IsPerfect ↥P →
    P ≤ L ⊔ centralizer (L : Set H)
  KL : K ≤ L
  Kperf : Group.IsPerfect ↥K
  Ku : ∀ k ∈ K, k * u = u * k
  conj : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) → ∃ x ∈ L, x * u * x⁻¹ = w
  uniq : ∀ K'' : Subgroup H, K'' ≤ L → (∀ k ∈ K'', k * u = u * k) → Group.IsPerfect ↥K'' →
    Nat.card ↥K'' = Nat.card ↥K → K'' = K

namespace TMemData

variable {N L K : Subgroup H} {u : H} (D : TMemData H N L K u)
include D

theorem centralizer_le (w : H) (hwL : w ∈ L) (hw2 : orderOf w = 2)
    (hwK : ∀ k ∈ K, k * w = w * k) : centralizer ({w} : Set H) ≤ normalizer (L : Set H) := by
  obtain ⟨x, hx, hxw⟩ := D.conj w hwL hw2 hwK
  exact centralizer_le_normalizer_of_conj hx hxw D.h38

theorem eq_of_perfect {Y : Subgroup H} (hY2 : IsPGroup 2 ↥Y) (hYne : Y ≠ ⊥)
    (hYL : Y ≤ L ⊓ centralizer (K : Set H))
    (hYmax : ∀ E : Subgroup H, E ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥E → Y ≤ E →
      E = Y)
    {t' : H} (ht'N : t' ∈ N) (ht'K : ∀ k ∈ K, k * t' = t' * k) (ht'2 : orderOf t' = 2)
    {K'' : Subgroup H} (hK''N : K'' ≤ N) (hK''t : ∀ k ∈ K'', k * t' = t' * k)
    (hK''perf : Group.IsPerfect ↥K'') (hK''card : Nat.card ↥K'' = Nat.card ↥K) : K'' = K := by
  obtain ⟨c, hcZ, hcY⟩ := exists_conj_mem_of_involution D.LN D.odd D.centralizer_le D.MK hY2 hYne
    hYL hYmax (t' := t') ⟨ht'N, mem_centralizer_iff.2 fun k hk => ht'K k hk⟩ ht'2
  set z := c * t' * c⁻¹ with hz
  have hzL : z ∈ L := (hYL hcY).1
  have hzK : ∀ k ∈ K, k * z = z * k := fun k hk => mem_centralizer_iff.1 (hYL hcY).2 k hk
  have hz2 : orderOf z = 2 := by
    have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective t'
    simpa [hz, MulAut.conj_apply] using this.trans ht'2
  obtain ⟨x, hxL, hxz⟩ := D.conj z hzL hz2 hzK
  have hcK : ∀ k ∈ K, k * c = c * k := fun k hk => mem_centralizer_iff.1 hcZ.2 k hk
  set K3 : Subgroup H := K''.map (MulAut.conj c).toMonoidHom with hK3
  have hK3N : K3 ≤ N := by
    rintro _ ⟨k, hk, rfl⟩
    have hcN : c ∈ N := hcZ.1
    exact N.mul_mem (N.mul_mem hcN (hK''N hk)) (N.inv_mem hcN)
  have hK3z : ∀ k ∈ K3, k * z = z * k := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 := hK''t k hk
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz]
    calc c * k * c⁻¹ * (c * t' * c⁻¹) = c * (k * t') * c⁻¹ := by group
      _ = c * (t' * k) * c⁻¹ := by rw [h1]
      _ = c * t' * c⁻¹ * (c * k * c⁻¹) := by group
  have hK3perf : Group.IsPerfect ↥K3 := Group.IsPerfect.map _
  have hK3card : Nat.card ↥K3 = Nat.card ↥K := by
    rw [hK3, Subgroup.card_map_of_injective (MulAut.conj c).injective, hK''card]
  have hK3M : K3 ≤ normalizer (L : Set H) := fun k hk =>
    D.centralizer_le z hzL hz2 hzK (mem_centralizer_singleton_iff.2 (hK3z k hk))
  have hK3L : K3 ≤ L := perfect_le_of_oddCN D.LN D.odd hK3N (D.Mperf K3 hK3M hK3perf)
  have hxL' : x⁻¹ ∈ L := L.inv_mem hxL
  have h4 : K3.map (MulAut.conj x⁻¹).toMonoidHom = K := by
    refine D.uniq _ ?_ (conj_centralizes hxz hK3z) (Group.IsPerfect.map _) ?_
    · rintro _ ⟨k, hk, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact L.mul_mem (L.mul_mem hxL' (hK3L hk)) (by simpa using L.inv_mem hxL')
    · rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hK3card]
  have h5 : K.map (MulAut.conj x⁻¹).toMonoidHom = K := by
    have := D.Kperf
    refine D.uniq _ ?_ (conj_centralizes hxz hzK) (Group.IsPerfect.map _) ?_
    · rintro _ ⟨k, hk, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact L.mul_mem (L.mul_mem hxL' (D.KL hk)) (by simpa using L.inv_mem hxL')
    · rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
  have h6 : K3 = K := Subgroup.map_injective (MulAut.conj x⁻¹).injective (h4.trans h5.symm)
  have h7 : K''.map (MulAut.conj c).toMonoidHom = K.map (MulAut.conj c).toMonoidHom := by
    rw [← hK3, h6, map_conj_eq_of_centralizes hcK]
  exact Subgroup.map_injective (MulAut.conj c).injective h7

theorem standard_subgroupOf (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hsmall : ∀ S : Subgroup H, S ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥S →
      Nat.card ↥S < 2 ^ twoAdic K) :
    CFSG.Open.standardComponentIsStandard (K.subgroupOf N) := by
  obtain ⟨Y, hY2, hYne, hYL, hYmax⟩ := exists_sylow_Y D.u_order D.u_mem D.Ku
  have hKN : K ≤ N := D.KL.trans D.LN
  have huN : u ∈ N := D.LN D.u_mem
  have hcardK : Nat.card ↥(K.subgroupOf N) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  refine standard_of_unique (u := ⟨u, huN⟩)
    (isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKN).symm hKq)
    (by rw [Subgroup.orderOf_mk]; exact D.u_order) ?_ ?_ ?_
  · refine mem_centralizer_iff.2 fun k hk => Subtype.ext ?_
    exact D.Ku k (mem_subgroupOf.1 hk)
  · intro tN htN2 htNC K' hK'C hK'perf hK'card
    have ht'2 : orderOf (tN : H) = 2 := by rw [Subgroup.orderOf_coe]; exact htN2
    have ht'K : ∀ k ∈ K, k * (tN : H) = (tN : H) * k := by
      intro k hk
      have := mem_centralizer_iff.1 htNC ⟨k, hKN hk⟩ (by simpa [mem_subgroupOf] using hk)
      exact congrArg Subtype.val this
    have hK'N : K'.map N.subtype ≤ N := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hK't : ∀ k ∈ K'.map N.subtype, k * (tN : H) = (tN : H) * k := by
      rintro _ ⟨x, hx, rfl⟩
      have := mem_centralizer_singleton_iff.1 (hK'C hx)
      show (x : H) * (tN : H) = (tN : H) * (x : H)
      exact congrArg Subtype.val this
    have hK'perf' : Group.IsPerfect ↥(K'.map N.subtype) := Group.IsPerfect.map _
    have hK'card' : Nat.card ↥(K'.map N.subtype) = Nat.card ↥K := by
      rw [Subgroup.card_map_of_injective N.subtype_injective, hK'card, hcardK]
    have heq := D.eq_of_perfect hY2 hYne hYL hYmax tN.2 ht'K ht'2 hK'N hK't hK'perf' hK'card'
    have hcomap : K' = (K'.map N.subtype).comap N.subtype :=
      (Subgroup.comap_map_eq_self_of_injective N.subtype_injective K').symm
    rw [hcomap, heq]
    rfl
  · have h1 := card_eq_pow_twoAdic D.LN D.odd D.centralizer_le D.MK hY2 hYne hYL hYmax
    have h2 := hsmall Y hYL hY2
    rw [h1] at h2
    have h3 : twoAdic (N ⊓ centralizer (K : Set H)) < twoAdic K :=
      (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
    have h4 : twoAdic (K.subgroupOf N) = twoAdic K := by
      unfold twoAdic
      rw [hcardK]
    have h5 : twoAdic (centralizer ((K.subgroupOf N : Subgroup ↥N) : Set ↥N)) =
        twoAdic (N ⊓ centralizer (K : Set H)) := by
      unfold twoAdic
      rw [card_centralizer_subgroupOf hKN]
    rw [h4, h5]
    exact h3

theorem maximal (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hsmall : ∀ S : Subgroup H, S ≤ L ⊓ centralizer (K : Set H) → IsPGroup 2 ↥S →
      Nat.card ↥S < 2 ^ twoAdic K) :
    K ≤ N ∧ Maximal (K.subgroupOf N) := by
  have hsol : SolStd (K.subgroupOf N) :=
    solStd_of_standardComponentIsStandard (D.standard_subgroupOf hKq hsmall)
  exact ⟨D.KL.trans D.LN, maximal_of_stdBare (inL_of_solStd' hsol) hsol.stdBare⟩

end TMemData

theorem TMemData.of_inner {N L K : Subgroup H} {t u : H} (hhyp : SolomonHypQ H N L K t u)
    (htN : t ∉ N) (huL : u ∈ L) (hinn : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l)
    (hKperf : Group.IsPerfect ↥K) (hKu : ∀ k ∈ K, k * u = u * k)
    (hconj : ∀ w ∈ L, orderOf w = 2 → (∀ k ∈ K, k * w = w * k) → ∃ x ∈ L, x * u * x⁻¹ = w)
    (huniq : ∀ K'' : Subgroup H, K'' ≤ L → (∀ k ∈ K'', k * u = u * k) →
      Group.IsPerfect ↥K'' → Nat.card ↥K'' = Nat.card ↥K → K'' = K) :
    TMemData H N L K u := by
  have : N.Normal := hhyp.fstar.normal
  have hperfL : Group.IsPerfect ↥L := hhyp.quasisimpleL.1
  have hMK := normalizer_le_sup_centralizer_of_mulAut_inner hinn
  exact
  { LN := le_of_perfect_of_index_le_two hhyp.index_le_two
    odd := oddCN_of_not_mem hhyp.index_le_two hhyp.cyclicSylow hhyp.t_mem hhyp.t_order htN
    u_mem := huL
    u_order := hhyp.u_order
    h38 := hhyp.hyp38_2
    MK := fun b hb _ => hMK hb
    Mperf := fun P hP _ => hP.trans hMK
    KL := hhyp.K_le
    Kperf := hKperf
    Ku := hKu
    conj := hconj
    uniq := huniq }

end CFSG.EvenSporadicStandard.Induction.TMem
