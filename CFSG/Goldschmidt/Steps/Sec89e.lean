module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec87c
import CFSG.Goldschmidt.Steps.Sec89a
import CFSG.Goldschmidt.Steps.Sec89c
import CFSG.Goldschmidt.Steps.Sec89d
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec89

open CFSG.Open

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem sq_mem_of_commutator_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hZ : (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ A)
    (hD : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s ^ 2 ∈ A := by
  refine hZ ⟨(S : Subgroup G).pow_mem hs 2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hc : s⁻¹ * w⁻¹ * s * w ∈ A := hD (by
    have := Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem hs)
      ((S : Subgroup G).inv_mem hw)
    simpa [commutatorElement_def] using this)
  have hcs := comm_of_mem hset h4 hs hc
  have hc2 : (s⁻¹ * w⁻¹ * s * w) ^ 2 = 1 := hset.elem.2 _ hc
  have e : w⁻¹ * s * w = s * (s⁻¹ * w⁻¹ * s * w) := by group
  have e2 : w⁻¹ * s ^ 2 * w = s ^ 2 := by
    calc w⁻¹ * s ^ 2 * w = (w⁻¹ * s * w) * (w⁻¹ * s * w) := by rw [pow_two]; group
      _ = s * ((s⁻¹ * w⁻¹ * s * w) * s) * (s⁻¹ * w⁻¹ * s * w) := by rw [e]; group
      _ = s ^ 2 * (s⁻¹ * w⁻¹ * s * w) ^ 2 := by rw [hcs, pow_two, pow_two]; group
      _ = s ^ 2 := by rw [hc2, mul_one]
  calc w * s ^ 2 = w * (w⁻¹ * s ^ 2 * w) := by rw [e2]
    _ = s ^ 2 * w := by group

omit [Finite G] in
theorem isElemAbelian_of_sq {C : Subgroup G} (hC : ∀ c ∈ C, c ^ 2 = 1) : IsElemAbelian 2 C :=
  ⟨⟨⟨fun a b => Subtype.ext (mul_comm_of_sq_eq_one (hC _ a.2) (hC _ b.2)
    (hC _ (C.mul_mem a.2 b.2)))⟩⟩, hC⟩

theorem card_le_thirtyTwo (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3)
    (hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G), z * t = t * z →
      z ^ 2 ∈ A → z ^ 2 = 1)
    (hZ : (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ A)
    (hD : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) : Nat.card (S : Subgroup G) ≤ 32 := by
  obtain ⟨t, htS, ht2, htA⟩ := exists_sq_eq_one_not_mem hset h4
  set C := (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hC2 : ∀ c ∈ C, c ^ 2 = 1 := fun c hc => hL t htS ht2 htA c hc.1
    (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
    (sq_mem_of_commutator_le hset h4 hZ hD hc.1)
  have hC8 : Nat.card C ≤ 8 := by
    obtain ⟨k, hk⟩ := (S.isPGroup'.to_le (inf_le_left : C ≤ _)).exists_card_eq
    have hk3 := CFSG.SectionRank.le_pRank one_lt_two inf_le_left (isElemAbelian_of_sq hC2) hk
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hk3.trans hrank)
      _ = 8 := by norm_num
  have hmemA : ∀ s : (S : Subgroup G), t⁻¹ * (s : G)⁻¹ * t * s ∈ A := fun s => hD (by
    have := Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem htS)
      ((S : Subgroup G).inv_mem s.2)
    simpa [commutatorElement_def] using this)
  let f : (S : Subgroup G) →* A := MonoidHom.mk' (fun s => ⟨_, hmemA s⟩) fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have hca := comm_of_mem hset h4 b.2 (hmemA a)
    calc t⁻¹ * ((a : G) * b)⁻¹ * t * (a * b)
        = (t⁻¹ * (b : G)⁻¹ * t * b) * ((b : G)⁻¹ * (t⁻¹ * (a : G)⁻¹ * t * a) * b) := by
          group
      _ = (t⁻¹ * (a : G)⁻¹ * t * a) * (t⁻¹ * (b : G)⁻¹ * t * b) := by
        rw [show (b : G)⁻¹ * (t⁻¹ * (a : G)⁻¹ * t * a) * b = t⁻¹ * (a : G)⁻¹ * t * a by
          rw [mul_assoc, hca]; group]
        exact (Sec8.comm hset.elem (hmemA b) (hmemA a))
  have hker : Nat.card f.ker ≤ Nat.card C := by
    refine Nat.card_le_card_of_injective (fun k => ⟨((k : (S : Subgroup G)) : G),
      ((k : (S : Subgroup G))).2, ?_⟩) fun k k' h => ?_
    · show ((k : (S : Subgroup G)) : G) ∈ Subgroup.centralizer ({t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hk : t⁻¹ * ((k : (S : Subgroup G)) : G)⁻¹ * t * k = 1 :=
        congrArg Subtype.val (f.mem_ker.mp k.2)
      calc ((k : (S : Subgroup G)) : G) * t
          = (k : G) * t * (t⁻¹ * ((k : (S : Subgroup G)) : G)⁻¹ * t * k) := by
            rw [hk, mul_one]
        _ = t * k := by group
    · have h' : ((k : (S : Subgroup G)) : G) = ((k' : (S : Subgroup G)) : G) :=
        congrArg (fun c : C => (c : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hrange : Nat.card f.range ≤ 4 := h4 ▸ Subgroup.card_le_card_group _
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  rw [← h1]
  calc Nat.card f.ker * Nat.card f.range ≤ 8 * 4 :=
        Nat.mul_le_mul (hker.trans hC8) hrange
    _ = 32 := by norm_num

omit [Finite G] in
theorem iterate_three_eq {Q : Type*} [Finite Q] (f : Q → Q) {b : ℕ} (hb : f^[3 ^ b] = id)
    (hQ : Nat.card Q ≤ 8) (q : Q) : f^[3] q = q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hinj : Function.Injective f := by
    have hl : Function.LeftInverse f^[3 ^ b - 1] f := fun a => by
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ (by norm_num)), hb, id]
    exact hl.injective
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin 9 => f^[k] q)
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; omega)
  have heq' : f^[(i : ℕ)] q = f^[(j : ℕ)] q := heq
  have hper : ∀ m n : ℕ, m < n → n ≤ 8 → f^[m] q = f^[n] q →
      ∃ d, 0 < d ∧ d ≤ 8 ∧ Function.IsPeriodicPt f d q := fun m n hmn hn h => by
    refine ⟨n - m, by omega, by omega, ?_⟩
    apply hinj.iterate m
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hmn.le]
    exact h.symm
  obtain ⟨d, hd0, hd8, hd⟩ : ∃ d, 0 < d ∧ d ≤ 8 ∧ Function.IsPeriodicPt f d q := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hper _ _ h (by omega) heq'
    · exact hper _ _ h (by omega) heq'.symm
  have h3b : Function.IsPeriodicPt f (3 ^ b) q := by
    change f^[3 ^ b] q = q
    rw [hb, id]
  have hg := hd.gcd h3b
  have hdvd : Nat.gcd d (3 ^ b) ∣ 3 := by
    obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (Nat.gcd_dvd_right d (3 ^ b))
    have hle : Nat.gcd d (3 ^ b) ≤ 8 := (Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d _)).trans hd8
    rw [he] at hle ⊢
    have : e ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases e <;> norm_num
  obtain ⟨k, hk⟩ := hdvd
  have := hg.mul_const k
  rw [← hk] at this
  exact this

theorem false_of_commutator_le (hset : GoldSetting G S A) (h4 : Nat.card A = 4)
    (hrank : CFSG.Open.pRank 2 (S : Subgroup G) ≤ 3)
    (hL : ∀ t ∈ (S : Subgroup G), t ^ 2 = 1 → t ∉ A → ∀ z ∈ (S : Subgroup G), z * t = t * z →
      z ^ 2 ∈ A → z ^ 2 = 1)
    (hZ : (S : Subgroup G) ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ A)
    (hD : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A) : False := by
  obtain ⟨x, hxS, hxC, b, hb⟩ := exists_mem_normalizer_pow hset h4
  have hxA := Sec8.normalizer_le_normalizer hset hxS
  have hidx : (A.subgroupOf (S : Subgroup G)).index ≤ 8 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf (S : Subgroup G))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hset.le).toEquiv, h4] at h1
    have h2 := card_le_thirtyTwo hset h4 hrank hL hZ hD
    omega
  have : (A.subgroupOf (S : Subgroup G)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hset.le).mpr (Sec8.le_normalizer hset)
  obtain ⟨φ, hφ⟩ := exists_conjHom hxS
  have hφA : A.subgroupOf (S : Subgroup G) ≤ (A.subgroupOf (S : Subgroup G)).comap φ :=
    fun a ha => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, hφ]
      exact conj_mem_of_mem_normalizer hxA ha
  set f := QuotientGroup.map _ _ φ hφA with hf
  have hiter : ∀ (n : ℕ) (s : (S : Subgroup G)),
      ((φ^[n] s : (S : Subgroup G)) : G) = (x ^ n)⁻¹ * s * x ^ n := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', hφ, ih, pow_succ]
      group
  have hfit : ∀ (n : ℕ) (s : (S : Subgroup G)),
      (⇑f)^[n] (s : (S : Subgroup G) ⧸ A.subgroupOf (S : Subgroup G)) = (φ^[n] s : _) := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', ih, hf, QuotientGroup.map_mk,
        Function.iterate_succ_apply']
  have hb' : (⇑f)^[3 ^ b] = id := by
    funext q
    induction q using QuotientGroup.induction_on with | H s => ?_
    rw [hfit, id]
    congr 1
    apply Subtype.ext
    rw [hiter, ← hb, pow_orderOf_eq_one]
    group
  have hcard : Nat.card ((S : Subgroup G) ⧸ A.subgroupOf (S : Subgroup G)) ≤ 8 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hx3 : ∀ s ∈ (S : Subgroup G), x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x = s := by
    intro s hs
    have h3 := iterate_three_eq (⇑f) hb' hcard (⟨s, hs⟩ : (S : Subgroup G))
    rw [hfit, QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      hiter] at h3
    have hw : s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) ∈ A := by
      have := A.inv_mem h3
      simpa using this
    have hgA := Sec8.pow_three_mem_centralizer hset h4 hxA
    have hwg : (x ^ 3)⁻¹ * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) * x ^ 3 =
        s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) := by
      have hc := Subgroup.mem_centralizer_iff.mp hgA _ hw
      calc (x ^ 3)⁻¹ * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) * x ^ 3
          = (x ^ 3)⁻¹ * ((s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) * x ^ 3) := by group
        _ = (x ^ 3)⁻¹ * (x ^ 3 * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3))) := by rw [hc]
        _ = s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3) := by group
    have hodd : Odd (orderOf (x ^ 3)) :=
      Odd.of_dvd_nat (by rw [hb]; exact Odd.pow (by decide)) (orderOf_pow_dvd 3)
    have h1 := eq_one_of_conj_eq_mul
      (show (x ^ 3)⁻¹ * s * x ^ 3 = s * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) by group) hwg hodd
      (k := 1) (by rw [pow_one]; exact hset.elem.2 _ hw)
    calc x⁻¹ * (x⁻¹ * (x⁻¹ * s * x) * x) * x = s * (s⁻¹ * ((x ^ 3)⁻¹ * s * x ^ 3)) := by
          simp only [pow_succ, pow_zero, one_mul]; group
      _ = s := by rw [h1, mul_one]
  obtain ⟨t, htS, ht2, htA, hm⟩ := exists_orbitProd_mem hset h4 hrank hxS hxA hxC hx3 hset.le
    (Sec8.le_normalizer hset) hxA (fun s hs => sq_mem_of_commutator_le hset h4 hZ hD hs)
    (fun c hc hcx => eq_one_of_conj_eq hset h4 hxA hxC hc hcx)
  exact false_of_mul_conj_mem hset h4 hrank hxS hxA htS ht2 htA hm

end CFSG.Goldschmidt.Sec89
