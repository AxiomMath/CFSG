module

public import CFSG.ClassicalInvolution.Q3.Sec13EndS3
import CFSG.ClassicalInvolution.Q3.TL4SepTwoD
import CFSG.ClassicalInvolution.Q3.TL3T28
public import CFSG.ClassicalInvolution.Q3.TL4D1ME8C

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

theorem surjective_of_card_ker {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] (f : Γ →* M)
    (hΓ : Nat.card Γ = 8) (hM : Nat.card M = 4) (hker : Nat.card f.ker ≤ 2) :
    Function.Surjective f := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hΓ] at h1
  have h2 : 0 < Nat.card f.ker := Nat.card_pos
  have h3 : Nat.card f.range ≤ 4 := hM ▸ Subgroup.card_le_card_group f.range
  have h4 : 4 ≤ Nat.card f.range := by nlinarith
  omega

theorem exists_q8_gen {K : Subgroup G} {z : G}
    (hz : IsUniqueInvolution K z) (hQ : IsQuatSub K) (hK8 : Nat.card K = 8) :
    ∃ i j : G, i ∈ K ∧ j ∈ K ∧ i * i = z ∧ j * j = z ∧ j * i = z * (i * j) ∧
      ∀ x ∈ K, x = 1 ∨ x = z ∨ x = i ∨ x = z * i ∨ x = j ∨ x = z * j ∨ x = i * j ∨
        x = z * (i * j) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hQ
  have hcard : Nat.card K = 2 ^ (k + 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    ring
  have hk1 : k = 1 := by
    rw [hK8] at hcard
    have h3 : 2 ^ (k + 2) = 2 ^ 3 := by rw [← hcard]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h3
    omega
  subst hk1
  let e2 : K ≃* QuaternionGroup 2 := e
  let ψ : QuaternionGroup 2 → G := fun w => ((e2.symm w : K) : G)
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    simp [ψ, map_mul]
  have hψmem : ∀ w, ψ w ∈ K := fun w => (e2.symm w).2
  have hψone : ψ 1 = 1 := by simp [ψ]
  have hψz : ψ (QuaternionGroup.a 2) = z := by
    have hne : ψ (QuaternionGroup.a 2) ≠ 1 := by
      intro h
      have h' : e2.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
      have h'' := congrArg e2 h'
      rw [MulEquiv.apply_symm_apply, map_one] at h''
      exact absurd (QuaternionGroup.a.inj (h''.trans (QuaternionGroup.one_def).symm))
        (by decide)
    have h22 : (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 := by
      decide
    have hsq : ψ (QuaternionGroup.a 2) * ψ (QuaternionGroup.a 2) = 1 := by
      rw [← hψmul, h22, hψone]
    exact (hz.unique _ (hψmem _) hsq).resolve_left hne
  have hψi : ∀ w, ψ w = ((e2.symm w : K) : G) := fun w => rfl
  have e1 : (QuaternionGroup.a 3 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * QuaternionGroup.a 1 := by
    decide
  have e2' : (QuaternionGroup.xa 2 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * QuaternionGroup.xa 0 := by
    decide
  have e3 : (QuaternionGroup.xa 3 : QuaternionGroup 2) =
      QuaternionGroup.a 1 * QuaternionGroup.xa 0 := by
    decide
  have e4 : (QuaternionGroup.xa 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * QuaternionGroup.xa 3 := by
    decide
  have hψ3 : ψ (QuaternionGroup.a 3) = z * ψ (QuaternionGroup.a 1) := by
    rw [e1, hψmul, hψz]
  have hψ2j : ψ (QuaternionGroup.xa 2) = z * ψ (QuaternionGroup.xa 0) := by
    rw [e2', hψmul, hψz]
  have hψ3j : ψ (QuaternionGroup.xa 3) = ψ (QuaternionGroup.a 1) * ψ (QuaternionGroup.xa 0) := by
    rw [e3, hψmul]
  have hψ1j : ψ (QuaternionGroup.xa 1) =
      z * (ψ (QuaternionGroup.a 1) * ψ (QuaternionGroup.xa 0)) := by
    rw [e4, hψmul, hψz, hψ3j]
  have hcases : ∀ w : QuaternionGroup 2, w = 1 ∨ w = QuaternionGroup.a 2 ∨
      w = QuaternionGroup.a 1 ∨ w = QuaternionGroup.a 3 ∨ w = QuaternionGroup.xa 0 ∨
      w = QuaternionGroup.xa 2 ∨ w = QuaternionGroup.xa 3 ∨ w = QuaternionGroup.xa 1 := by
    decide
  have key : (QuaternionGroup.xa 0 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 * (QuaternionGroup.a 1 * QuaternionGroup.xa 0) := by
    decide
  refine ⟨ψ (QuaternionGroup.a 1), ψ (QuaternionGroup.xa 0), hψmem _, hψmem _, ?_, ?_, ?_, ?_⟩
  · rw [← hψmul, show (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide, hψz]
  · rw [← hψmul, show (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide, hψz]
  · have h := congrArg ψ key
    rw [hψmul, hψmul, hψmul, hψz] at h
    exact h
  · intro x hx
    have hx' : x = ψ (e2 ⟨x, hx⟩) := by simp [ψ]
    rw [hx']
    rcases hcases (e2 ⟨x, hx⟩) with h | h | h | h | h | h | h | h <;> rw [h] <;>
      simp only [hψone, hψz, hψ3, hψ2j, hψ3j, hψ1j] <;> simp

private theorem conj_eq_mul_aux {K : Subgroup G} {z i j : G} (f : G → G)
    (hz : IsUniqueInvolution K z) (hi : i ∈ K) (hj : j ∈ K) (hii : i * i = z)
    (hjj : j * j = z) (hji : j * i = z * (i * j))
    (hNF : ∀ x ∈ K, x = 1 ∨ x = z ∨ x = i ∨ x = z * i ∨ x = j ∨ x = z * j ∨ x = i * j ∨
      x = z * (i * j))
    (hfmul : ∀ x y, f (x * y) = f x * f y) (hff : ∀ x, f (f x) = x)
    (hfK : ∀ x ∈ K, f x ∈ K) (hf1 : f 1 = 1) (hfz : f z = z) (hfix : ∃ x ∈ K, f x ≠ x) :
    ∃ k ∈ K, f k = z * k := by
  have hzz : z * z = 1 := hz.sq
  have hzi : z * i = i * z := by rw [← hii, mul_assoc]
  have hzj : z * j = j * z := by rw [← hjj, mul_assoc]
  have D1 : ∀ x, i * (z * x) = z * (i * x) := fun x => by
    rw [← mul_assoc i z x, ← hzi, mul_assoc z i x]
  have D2 : ∀ x, j * (z * x) = z * (j * x) := fun x => by
    rw [← mul_assoc j z x, ← hzj, mul_assoc z j x]
  have D3 : ∀ x, z * (z * x) = x := fun x => by
    rw [← mul_assoc z z x, hzz, one_mul]
  have him : i * (i * j) = z * j := by rw [← mul_assoc i i j, hii]
  have hmi : i * j * i = j := by
    calc i * j * i = i * (j * i) := mul_assoc i j i
      _ = i * (z * (i * j)) := by rw [hji]
      _ = z * (i * (i * j)) := D1 _
      _ = z * (z * j) := by rw [him]
      _ = j := D3 j
  have hmj : i * j * j = z * i := by
    calc i * j * j = i * (j * j) := mul_assoc i j j
      _ = i * z := by rw [hjj]
      _ = z * i := hzi.symm
  have hmm : i * j * (i * j) = z := by rw [← mul_assoc (i * j) i j, hmi, hjj]
  have Dm : ∀ x, i * j * (z * x) = z * (i * j * x) := fun x => by
    calc i * j * (z * x) = i * (j * (z * x)) := mul_assoc i j (z * x)
      _ = i * (z * (j * x)) := by rw [D2 x]
      _ = z * (i * (j * x)) := D1 (j * x)
      _ = z * (i * j * x) := by rw [mul_assoc i j x]
  have zc : ∀ x y, z * x = y → x = z * y := fun x y h => by rw [← h, D3 x]
  have L_a : j = z * i → False := by
    intro h
    have h1 : z * i * i = z * (i * (z * i)) := by rw [← h]; exact hji
    have e1 : z * i * i = 1 := by rw [mul_assoc, hii, hzz]
    have e2 : z * (i * (z * i)) = z := by rw [D1 i, hii, D3 z]
    exact hz.ne_one (e2.symm.trans (h1.symm.trans e1))
  have L_b : j = i → False := by
    intro h
    rw [h, hii, hzz] at hji
    exact hz.ne_one hji
  have L_c : z * i = i → False := fun h =>
    hz.ne_one (mul_right_cancel (h.trans (one_mul i).symm))
  have L_d : z * j = j → False := fun h =>
    hz.ne_one (mul_right_cancel (h.trans (one_mul j).symm))
  have L_e : z = i → False := by
    intro h
    rw [← h] at hii
    exact hz.ne_one (hz.sq.symm.trans hii).symm
  have L_f : i = 1 → False := by
    intro h
    rw [h, mul_one] at hii
    exact hz.ne_one hii.symm
  have L_g : z * i = 1 → False := by
    intro h
    apply L_f
    calc i = 1 * i := (one_mul i).symm
      _ = z * i * i := by rw [h]
      _ = z * (i * i) := mul_assoc z i i
      _ = z * z := by rw [hii]
      _ = 1 := hzz
  obtain ⟨p, hp⟩ : ∃ p, f i = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, f j = q := ⟨_, rfl⟩
  have hpK : p ∈ K := by rw [← hp]; exact hfK i hi
  have hqK : q ∈ K := by rw [← hq]; exact hfK j hj
  have hfzmul : ∀ x, f (z * x) = z * f x := fun x => by rw [hfmul, hfz]
  have hpp : p * p = z := by rw [← hp, ← hfmul, hii, hfz]
  have hqq : q * q = z := by rw [← hq, ← hfmul, hjj, hfz]
  have hfp : f p = i := by rw [← hp, hff]
  have hfq : f q = j := by rw [← hq, hff]
  have hfij : f (i * j) = p * q := by rw [hfmul, hp, hq]
  rcases hNF p hpK with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  ·
    rw [h1] at hpp
    exact (hz.ne_one (by rw [← hpp, mul_one])).elim
  ·
    rw [h1] at hpp
    exact (hz.ne_one (hpp.symm.trans hz.sq)).elim
  ·
    rw [h1] at hp hpK hpp hfp hfij
    rcases hNF q hqK with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
    · rw [h2] at hqq
      exact (hz.ne_one (by rw [← hqq, mul_one])).elim
    · rw [h2] at hqq
      exact (hz.ne_one (hqq.symm.trans hz.sq)).elim
    · rw [h2] at hq hfq
      exact (L_b (hfq.symm.trans hp)).elim
    · rw [h2] at hq hfq
      rw [hfzmul, hp] at hfq
      exact (L_a hfq.symm).elim
    · rw [h2] at hq hfq
      obtain ⟨x, hx, hfx⟩ := hfix
      exfalso
      apply hfx
      have hfall : ∀ y ∈ K, f y = y := by
        intro y hy
        rcases hNF y hy with h | h | h | h | h | h | h | h <;> rw [h]
        · exact hf1
        · exact hfz
        · exact hp
        · rw [hfzmul, hp]
        · exact hq
        · rw [hfzmul, hq]
        · rw [hfmul, hp, hq]
        · rw [hfzmul, hfmul, hp, hq]
      exact hfall x hx
    · rw [h2] at hq
      exact ⟨j, hj, hq⟩
    · rw [h2] at hq hfq
      have h3 : f (i * j) = i * (i * j) := by rw [hfmul, hp, hq]
      exact (L_d (him.symm.trans (h3.symm.trans hfq))).elim
    · rw [h2] at hq hfq
      rw [hfzmul, hfmul, hp, hq] at hfq
      have h4 : i * (z * (i * j)) = j := by rw [D1, him, D3]
      rw [h4] at hfq
      exact (L_d hfq).elim
  ·
    rw [h1] at hp
    exact ⟨i, hi, hp⟩
  ·
    rw [h1] at hp hfp hpp hfij
    have hqi : q = i := hq.symm.trans hfp
    refine ⟨i * j, K.mul_mem hi hj, ?_⟩
    rw [hfij, hqi]
    exact hji
  ·
    rw [h1] at hp hfp hpp hfij
    rw [hfzmul, hq] at hfp
    have hqzi : q = z * i := zc q i hfp
    have e : z * j * (z * i) = j * i := by
      calc z * j * (z * i) = z * (j * (z * i)) := mul_assoc z j (z * i)
        _ = z * (z * (j * i)) := by rw [D2 i]
        _ = j * i := D3 (j * i)
    refine ⟨i * j, K.mul_mem hi hj, ?_⟩
    rw [hfij, hqzi, e, hji]
  ·
    rw [h1] at hp hfp hpp hfij
    have hmq : i * j * q = i := hfij.symm.trans hfp
    rcases hNF q hqK with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
    · rw [h2] at hqq
      exact (hz.ne_one (by rw [← hqq, mul_one])).elim
    · rw [h2] at hqq
      exact (hz.ne_one (hqq.symm.trans hz.sq)).elim
    · rw [h2] at hmq
      exact (L_b (hmi.symm.trans hmq)).elim
    · rw [h2] at hmq
      have e : i * j * (z * i) = z * j := by rw [Dm i, hmi]
      exact (L_a (zc j i (e.symm.trans hmq))).elim
    · rw [h2] at hmq
      exact (L_c (hmj.symm.trans hmq)).elim
    · rw [h2] at hq
      exact ⟨j, hj, hq⟩
    · rw [h2] at hmq
      exact (L_e (hmm.symm.trans hmq)).elim
    · rw [h2] at hmq
      have e : i * j * (z * (i * j)) = 1 := by rw [Dm (i * j), hmm, hz.sq]
      exact (L_f (hmq.symm.trans e)).elim
  ·
    rw [h1] at hp hfp hpp hfij
    rw [hfzmul, hfij] at hfp
    have hmq : z * (i * j) * q = z * i := zc _ _ hfp
    rcases hNF q hqK with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
    · rw [h2] at hqq
      exact (hz.ne_one (by rw [← hqq, mul_one])).elim
    · rw [h2] at hqq
      exact (hz.ne_one (hqq.symm.trans hz.sq)).elim
    · rw [h2] at hmq
      have e : z * (i * j) * i = z * j := by rw [mul_assoc, hmi]
      exact (L_b (mul_left_cancel (e.symm.trans hmq))).elim
    · rw [h2] at hmq
      have e : z * (i * j) * (z * i) = j := by rw [mul_assoc, Dm i, hmi, D3]
      exact (L_a (e.symm.trans hmq)).elim
    · rw [h2] at hmq
      have e : z * (i * j) * j = i := by rw [mul_assoc, hmj, D3]
      exact (L_c (e.symm.trans hmq).symm).elim
    · rw [h2] at hq
      exact ⟨j, hj, hq⟩
    · rw [h2] at hmq
      have e : z * (i * j) * (i * j) = 1 := by rw [mul_assoc, hmm, hzz]
      exact (L_g (hmq.symm.trans e)).elim
    · rw [h2] at hmq
      have e : z * (i * j) * (z * (i * j)) = z := by
        rw [mul_assoc, Dm (i * j), hmm, D3]
      exact (L_f (mul_left_cancel ((mul_one z).trans (e.symm.trans hmq))).symm).elim

theorem exists_conj_eq_mul_of_not_comm {K : Subgroup G} {z i j t : G}
    (hz : IsUniqueInvolution K z) (hi : i ∈ K) (hj : j ∈ K) (hii : i * i = z) (hjj : j * j = z)
    (hji : j * i = z * (i * j))
    (hNF : ∀ x ∈ K, x = 1 ∨ x = z ∨ x = i ∨ x = z * i ∨ x = j ∨ x = z * j ∨ x = i * j ∨
      x = z * (i * j))
    (ht : t * t = 1) (htK : ∀ x ∈ K, t * x * t⁻¹ ∈ K) (hnc : ∃ x ∈ K, t * x ≠ x * t) :
    ∃ k ∈ K, t * k * t⁻¹ = z * k := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨f, hf⟩ : ∃ f : G → G, ∀ x, f x = t * x * t⁻¹ :=
    ⟨fun x => t * x * t⁻¹, fun x => rfl⟩
  have hfmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    rw [hf, hf, hf, ht']
    calc t * (x * y) * t = t * x * y * t := by group
      _ = t * x * (t * t) * y * t := by rw [ht]; group
      _ = t * x * t * (t * y * t) := by group
  have hff : ∀ x, f (f x) = x := by
    intro x
    rw [hf, hf, ht']
    calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  have hf1 : f 1 = 1 := by rw [hf]; simp
  have hfK : ∀ x ∈ K, f x ∈ K := fun x hx => by rw [hf]; exact htK x hx
  have hfz : f z = z := by
    have hsq : f z * f z = 1 := by rw [← hfmul, hz.sq, hf1]
    have hne : f z ≠ 1 := by
      intro h
      apply hz.ne_one
      rw [← hff z, h, hf1]
    exact (hz.unique _ (hfK z hz.mem) hsq).resolve_left hne
  have hfix : ∃ x ∈ K, f x ≠ x := by
    obtain ⟨x, hx, hxt⟩ := hnc
    refine ⟨x, hx, ?_⟩
    intro hfx
    apply hxt
    rw [hf] at hfx
    exact mul_inv_eq_iff_eq_mul.mp hfx
  obtain ⟨k, hk, hkf⟩ :=
    conj_eq_mul_aux f hz hi hj hii hjj hji hNF hfmul hff hfK hf1 hfz hfix
  refine ⟨k, hk, ?_⟩
  rw [← hf k]
  exact hkf

@[expose] def dComm (d k : G) : G := d * k * d⁻¹ * k⁻¹

structure Q8Data (K : Subgroup G) (z i j : G) : Prop where
  inv : IsUniqueInvolution K z
  mem_i : i ∈ K
  mem_j : j ∈ K
  sq_i : i * i = z
  sq_j : j * j = z
  comm : j * i = z * (i * j)
  nf : ∀ x ∈ K, x = 1 ∨ x = z ∨ x = i ∨ x = z * i ∨ x = j ∨ x = z * j ∨ x = i * j ∨
    x = z * (i * j)

theorem conj_eq_self_of_normalizer {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) : x * z * x⁻¹ = z := by
  have hc : conjSub x K = K := mem_normalizer_iff_conjSub_eq.mp hx
  have h1 := hz.conj x
  rw [hc] at h1
  exact (hz.eq h1).symm

theorem conj_of_mem_mem {K : Subgroup G} {z x c : G} (hz : IsUniqueInvolution K z)
    (hx : x ∈ K) (hc : c = 1 ∨ c = z) : x * c * x⁻¹ = c := by
  rcases hc with rfl | rfl
  · exact by group
  · exact conj_eq_self_of_normalizer hz (Subgroup.le_normalizer hx)

theorem dComm_mem {K : Subgroup G} {d k : G} (hd : d ∈ Subgroup.normalizer (K : Set G))
    (hk : k ∈ K) : dComm d k ∈ K :=
  K.mul_mem ((Subgroup.mem_normalizer_iff.mp hd k).mp hk) (K.inv_mem hk)

theorem dComm_mul_left {K : Subgroup G} {z d d' k : G} (hz : IsUniqueInvolution K z)
    (hd : d ∈ Subgroup.normalizer (K : Set G)) (hc : dComm d' k = 1 ∨ dComm d' k = z) :
    dComm (d * d') k = dComm d' k * dComm d k := by
  have hc' : d' * k * d'⁻¹ = dComm d' k * k := by unfold dComm; group
  have hdc : d * dComm d' k * d⁻¹ = dComm d' k := by
    rcases hc with h1 | h1 <;> rw [h1]
    · group
    · exact conj_eq_self_of_normalizer hz hd
  calc dComm (d * d') k = d * (d' * k * d'⁻¹) * d⁻¹ * k⁻¹ := by unfold dComm; group
    _ = d * (dComm d' k * k) * d⁻¹ * k⁻¹ := by rw [hc']
    _ = (d * dComm d' k * d⁻¹) * (d * k * d⁻¹ * k⁻¹) := by group
    _ = dComm d' k * dComm d k := by rw [hdc]; rfl

theorem dComm_mul_right {K : Subgroup G} {z d x y : G} (hz : IsUniqueInvolution K z)
    (hx : x ∈ K) (hy : y ∈ K) (hd : d ∈ Subgroup.normalizer (K : Set G))
    (hc : dComm d y = 1 ∨ dComm d y = z) :
    dComm d (x * y) = dComm d x * dComm d y := by
  have hxc := conj_of_mem_mem hz hx hc
  calc dComm d (x * y) = dComm d x * (x * dComm d y * x⁻¹) := by unfold dComm; group
    _ = dComm d x * dComm d y := by rw [hxc]

theorem dComm_z {K : Subgroup G} {z d : G} (hz : IsUniqueInvolution K z)
    (hd : d ∈ Subgroup.normalizer (K : Set G)) : dComm d z = 1 := by
  unfold dComm
  rw [conj_eq_self_of_normalizer hz hd]
  group

theorem dComm_eq_one_iff {d k : G} : dComm d k = 1 ↔ d * k = k * d := by
  unfold dComm
  constructor
  · intro h1
    calc d * k = (d * k * d⁻¹ * k⁻¹) * k * d := by group
      _ = k * d := by rw [h1]; group
  · intro h1
    calc d * k * d⁻¹ * k⁻¹ = k * d * d⁻¹ * k⁻¹ := by rw [h1]
      _ = 1 := by group

theorem card_zpowers_of_involution {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1]

theorem card_zpowers_prod_eq_four {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z)) = 4 := by
  rw [Nat.card_prod, card_zpowers_of_involution hz2 hz1]

theorem seven_orbit_false {Γ X Y : Type} [Group Γ] [MulAction Γ X] [MulAction Γ Y]
    [Fintype X] [Fintype Y] (hX : Fintype.card X = 8) (hY : Fintype.card Y = 7)
    (htr : ∀ y y' : Y, ∃ g : Γ, g • y = y') (R : X → Y → Prop)
    (hR : ∀ (g : Γ) (x : X) (y : Y), R x y → R (g • x) (g • y))
    (hcent : ∀ x : X, (∀ y : Y, R x y) → ∀ g : Γ, g • x = x)
    (hfree : ∀ x : X, ∃ g : Γ, g • x ≠ x)
    (hex : ∃ x : X, ∃ y : Y, R x y) : False := by
  classical
  have key : ∀ (g : Γ) (x : X) (y : Y), R (g • x) y ↔ R x (g⁻¹ • y) := by
    intro g x y
    constructor
    · intro h
      simpa [inv_smul_smul] using hR g⁻¹ _ _ h
    · intro h
      simpa [smul_inv_smul] using hR g _ _ h
  obtain ⟨x0, y0, h0⟩ := hex
  obtain ⟨c, hc⟩ : ∃ c : X → ℕ, ∀ x, c x = (Finset.univ.filter fun y => R x y).card :=
    ⟨fun x => (Finset.univ.filter fun y => R x y).card, fun x => rfl⟩
  have hcinv : ∀ (g : Γ) (x : X), c (g • x) = c x := by
    intro g x
    rw [hc, hc]
    apply Finset.card_nbij' (fun y => g⁻¹ • y) (fun y => g • y)
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact (key g x y).mp hy
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact hR g x y hy
    · intro y _
      simp [smul_inv_smul]
    · intro y _
      simp [inv_smul_smul]
  have hc_le : c x0 ≤ 7 := by
    rw [hc]
    exact (Finset.card_le_univ _).trans hY.le
  have hc_pos : 0 < c x0 := by
    rw [hc]
    exact Finset.card_pos.mpr ⟨y0, by simp [h0]⟩
  have hc_ne : c x0 ≠ 7 := by
    intro h7
    rw [hc] at h7
    have hfull : Finset.univ.filter (fun y => R x0 y) = Finset.univ :=
      Finset.eq_univ_of_card _ (h7.trans hY.symm)
    have hall : ∀ y : Y, R x0 y := by
      intro y
      have hy : y ∈ Finset.univ.filter (fun y => R x0 y) := by
        rw [hfull]
        exact Finset.mem_univ y
      exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, hg⟩ := hfree x0
    exact hg (hcent x0 hall g)
  have hc_lt : c x0 < 7 := lt_of_le_of_ne hc_le hc_ne
  obtain ⟨S, hS⟩ : ∃ S : Finset X, ∀ x, x ∈ S ↔ c x = c x0 :=
    ⟨Finset.univ.filter fun x => c x = c x0, fun x => by simp⟩
  have hSinv : ∀ (g : Γ) (x : X), g • x ∈ S ↔ x ∈ S := by
    intro g x
    rw [hS, hS, hcinv]
  obtain ⟨m, hm⟩ : ∃ m : Y → ℕ, ∀ y, m y = (S.filter fun x => R x y).card :=
    ⟨fun y => (S.filter fun x => R x y).card, fun y => rfl⟩
  have hminv : ∀ (g : Γ) (y : Y), m (g • y) = m y := by
    intro g y
    rw [hm, hm]
    apply Finset.card_nbij' (fun x => g⁻¹ • x) (fun x => g • x)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨(hSinv g⁻¹ x).mpr hx.1, (key g⁻¹ x y).mpr (by rw [inv_inv]; exact hx.2)⟩
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      exact ⟨(hSinv g x).mpr hx.1, hR g x y hx.2⟩
    · intro x _
      simp [smul_inv_smul]
    · intro x _
      simp [inv_smul_smul]
  have hdouble : ∑ x ∈ S, c x = ∑ y : Y, m y := by
    have h1 : ∀ x, c x = ∑ y : Y, if R x y then 1 else 0 := by
      intro x
      rw [hc, Finset.card_filter]
    have h2 : ∀ y, m y = ∑ x ∈ S, if R x y then 1 else 0 := by
      intro y
      rw [hm, Finset.card_filter]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hsumS : ∑ x ∈ S, c x = S.card * c x0 := by
    have h : ∑ x ∈ S, c x = ∑ _x ∈ S, c x0 := Finset.sum_congr rfl fun x hx => (hS x).mp hx
    rw [h, Finset.sum_const, smul_eq_mul]
  have hsumY : ∑ y : Y, m y = 7 * m y0 := by
    have h : ∀ y : Y, m y = m y0 := by
      intro y
      obtain ⟨g, hg⟩ := htr y0 y
      rw [← hg, hminv]
    have h' : ∑ y : Y, m y = ∑ _y : Y, m y0 := Finset.sum_congr rfl fun y _ => h y
    rw [h', Finset.sum_const, Finset.card_univ, hY, smul_eq_mul]
  have hmain : S.card * c x0 = 7 * m y0 := by
    rw [← hsumS, hdouble, hsumY]
  have hp : Nat.Prime 7 := by norm_num
  have h7dvd : 7 ∣ S.card * c x0 := ⟨m y0, hmain⟩
  have h7S : 7 ∣ S.card := by
    rcases (Nat.Prime.dvd_mul hp).mp h7dvd with h | h
    · exact h
    · omega
  have hSle : S.card ≤ 8 := by
    have h := Finset.card_le_univ S
    omega
  have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨x0, (hS x0).mpr rfl⟩
  have hS7 : S.card = 7 := by omega
  obtain ⟨x1, hx1⟩ : ∃ x1 : X, Sᶜ = {x1} := by
    apply Finset.card_eq_one.mp
    have h := Finset.card_compl S
    omega
  have hx1S : x1 ∉ S := by
    have hmem : x1 ∈ Sᶜ := by
      rw [hx1]
      exact Finset.mem_singleton_self x1
    exact Finset.mem_compl.mp hmem
  obtain ⟨g, hg⟩ := hfree x1
  refine hg ?_
  have hgS : g • x1 ∉ S := fun h => hx1S ((hSinv g x1).mp h)
  have hmem : g • x1 ∈ Sᶜ := Finset.mem_compl.mpr hgS
  rw [hx1, Finset.mem_singleton] at hmem
  exact hmem

private theorem perm_fin3_three_conj :
    ∀ a : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 →
      ∃ b c : Equiv.Perm (Fin 3), a ≠ b * a * b⁻¹ ∧ a ≠ c * a * c⁻¹ ∧
        b * a * b⁻¹ ≠ c * a * c⁻¹ := by
  decide

theorem three_le_ncard_DSet {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) : 3 ≤ (DSet Ω W).ncard := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  obtain ⟨phi⟩ : Nonempty (↥(muGroup Ω W) ≃* Equiv.Perm (Fin 3)) := hS3
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ Asc77.Thompson.muDelta Ω W, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : Subgroup.closure (Asc77.Thompson.muDelta Ω W) ≤ ⊥ := by
      rw [Subgroup.closure_le]
      exact fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
    have hmem : phi.symm (Equiv.swap (0 : Fin 3) 1) ∈
        Subgroup.closure (Asc77.Thompson.muDelta Ω W) := by
      rw [Asc77.Thompson.closure_muDelta_eq_top]
      exact Subgroup.mem_top _
    have h1 : phi.symm (Equiv.swap (0 : Fin 3) 1) = 1 := Subgroup.mem_bot.mp (hbot hmem)
    exact absurd (phi.symm.map_eq_one_iff.mp h1) (by decide)
  have ht2 : phi t * phi t = 1 := by
    rw [← map_mul, Q3T6.Mu.muDelta_mul_self hΩ hW ht, map_one]
  have ht1' : phi t ≠ 1 := fun h => ht1 (phi.map_eq_one_iff.mp h)
  obtain ⟨b, c, hb, hc, hbc⟩ := perm_fin3_three_conj (phi t) ht2 ht1'
  have hconj : ∀ x : Equiv.Perm (Fin 3), ∃ s ∈ Asc77.Thompson.muDelta Ω W,
      phi s = x * phi t * x⁻¹ := by
    intro x
    refine ⟨phi.symm x * t * (phi.symm x)⁻¹, Q3T6.Mu.muDelta_conj_mem hΩ ht (phi.symm x), ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨t2, ht2m, ht2φ⟩ := hconj b
  obtain ⟨t3, ht3m, ht3φ⟩ := hconj c
  have hdist : ∀ s s' : ↥(muGroup Ω W), phi s ≠ phi s' → s ≠ s' :=
    fun s s' h hss => h (congrArg phi hss)
  have hne12 : t ≠ t2 := hdist _ _ (by rw [ht2φ]; exact hb)
  have hne13 : t ≠ t3 := hdist _ _ (by rw [ht3φ]; exact hc)
  have hne23 : t2 ≠ t3 := hdist _ _ (by rw [ht2φ, ht3φ]; exact hbc)
  obtain ⟨R1, hR1, r1, hr1, hr1W, hq1⟩ := ht
  obtain ⟨R2, hR2, r2, hr2, hr2W, hq2⟩ := ht2m
  obtain ⟨R3, hR3, r3, hr3, hr3W, hq3⟩ := ht3m
  have hR12 : R1 ≠ R2 := by
    intro h
    have hr2' : r2 ∈ R1 := by rw [h]; exact hr2
    apply hne12
    apply Subtype.ext
    rw [hq1, hq2]
    exact Q3CL.Thompson.D_piG_eq hΩ hW hR1 hr1 hr2' hr1W hr2W
  have hR13 : R1 ≠ R3 := by
    intro h
    have hr3' : r3 ∈ R1 := by rw [h]; exact hr3
    apply hne13
    apply Subtype.ext
    rw [hq1, hq3]
    exact Q3CL.Thompson.D_piG_eq hΩ hW hR1 hr1 hr3' hr1W hr3W
  have hR23 : R2 ≠ R3 := by
    intro h
    have hr3' : r3 ∈ R2 := by rw [h]; exact hr3
    apply hne23
    apply Subtype.ext
    rw [hq2, hq3]
    exact Q3CL.Thompson.D_piG_eq hΩ hW hR2 hr2 hr3' hr2W hr3W
  have h3 : 2 < (DSet Ω W).ncard :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).2 ⟨R1, R2, R3, hR1, hR2, hR3, hR12, hR13, hR23⟩
  omega

theorem commute_sq_of_dComm {K : Subgroup G} {z i x c : G} (hz : IsUniqueInvolution K z)
    (hxz : x * z = z * x) (hc : c = 1 ∨ c = z) (hdc : dComm x i = c) :
    Commute (x ^ 2) i := by
  have hcx : x * c * x⁻¹ = c := by
    rcases hc with h1 | h1 <;> rw [h1]
    · group
    · rw [hxz, mul_inv_cancel_right]
  have h1 : x * i * x⁻¹ = c * i := by
    unfold dComm at hdc
    calc x * i * x⁻¹ = (x * i * x⁻¹ * i⁻¹) * i := by group
      _ = c * i := by rw [hdc]
  have h2 : x ^ 2 * i * (x ^ 2)⁻¹ = i := by
    rw [pow_two, mul_inv_rev]
    calc x * x * i * (x⁻¹ * x⁻¹) = x * (x * i * x⁻¹) * x⁻¹ := by group
      _ = x * (c * i) * x⁻¹ := by rw [h1]
      _ = (x * c * x⁻¹) * (x * i * x⁻¹) := by group
      _ = c * (c * i) := by rw [hcx, h1]
      _ = i := by
        rcases hc with h3 | h3 <;> rw [h3]
        · group
        · calc z * (z * i) = (z * z) * i := by group
            _ = i := by rw [hz.sq, one_mul]
  exact mul_inv_eq_iff_eq_mul.mp h2

theorem commute_sq_of_gen {K : Subgroup G} {z i j x : G} (hQ : Q8Data K z i j)
    (hcz : Commute (x ^ 2) z) (hci : Commute (x ^ 2) i) (hcj : Commute (x ^ 2) j) {y : G}
    (hy : y ∈ K) : Commute (x ^ 2) y := by
  rcases hQ.nf y hy with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · exact Commute.one_right _
  · exact hcz
  · exact hci
  · exact hcz.mul_right hci
  · exact hcj
  · exact hcz.mul_right hcj
  · exact hci.mul_right hcj
  · exact hcz.mul_right (hci.mul_right hcj)

theorem dComm_eq_one_of_gens {K : Subgroup G} {z i j x : G} (hQ : Q8Data K z i j)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hc : ∀ k ∈ K, dComm x k = 1 ∨ dComm x k = z)
    (hi : dComm x i = 1) (hj : dComm x j = 1) {k : G} (hk : k ∈ K) : dComm x k = 1 := by
  have hij : dComm x (i * j) = 1 := by
    rw [dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hxN (hc j hQ.mem_j), hi, hj, one_mul]
  rcases hQ.nf k hk with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1]
  · unfold dComm
    group
  · exact dComm_z hQ.inv hxN
  · exact hi
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_i hxN (hc i hQ.mem_i), dComm_z hQ.inv hxN, hi,
      one_mul]
  · exact hj
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_j hxN (hc j hQ.mem_j), dComm_z hQ.inv hxN, hj,
      one_mul]
  · exact hij
  · rw [dComm_mul_right hQ.inv hQ.inv.mem (K.mul_mem hQ.mem_i hQ.mem_j) hxN
      (hc (i * j) (K.mul_mem hQ.mem_i hQ.mem_j)), dComm_z hQ.inv hxN, hij, one_mul]

theorem fin3_cover : ∀ i j k m : Fin 3, i ≠ j → k ≠ i → k ≠ j → m = i ∨ m = j ∨ m = k := by
  decide

theorem fin3_third : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  decide

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem exists_isUniqueInvolution {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ z : G, IsUniqueInvolution L z :=
  Sec6Gen.exists_uniqueInvolution h.thmD.hyp hL

theorem isQuatSub_of_mem {L : Subgroup G} (hL : L ∈ Ω) : IsQuatSub L :=
  Sec6Gen.isQuatSub_of_mem_RSet h.thmD.hyp (TC.mem_RSet_of_isPGroup hL (h.thmD.two L hL))

theorem not_mem_USet {K : Subgroup G} (hK : K ∈ Ω) : K ∉ USet Ω := by
  rintro ⟨R, hR, hKR, -, hrel⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRJeq : R = J := (hRJ.2.2 J le_rfl (h.thmD.two J hJ) hRJ.1).symm
  have hcard : Nat.card R = Nat.card K := by
    rw [hRJeq, h.card_eq_eight hJ, h.card_eq_eight hK]
  have hKR' : K = R := Subgroup.eq_of_le_of_card_ge hKR hcard.le
  rw [← hKR', Subgroup.relIndex_self] at hrel
  norm_num at hrel

theorem exists_not_commute_of_ne (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {a b : G} (ha : IsUniqueInvolution K a)
    (hb : IsUniqueInvolution L b) (hab : a ≠ b) : ∃ x ∈ K, b * x ≠ x * b := by
  by_contra hcon
  push Not at hcon
  have hKc : K ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcon x hx).symm
  have hV' : IsSylow2In K (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [inf_eq_left.mpr hKc]
    exact ⟨le_rfl, h.thmD.two K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hnot : K ∉ twinSet Ω L := by
    rw [hV L hL, Set.mem_singleton_iff]
    rintro rfl
    exact hab (ha.eq hb)
  rcases Sec6Gen.l6_2Gen G Ω h.thmD.hyp L hL b hb K hK hnot a ha K hV' ha.mem with
    ⟨hVt, -⟩ | ⟨hVt, -⟩ | ⟨hVU, -⟩ | ⟨-, hVL⟩
  · have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha.sq) ha.ne_one
    have h8 := h.card_eq_eight hK
    rw [hVt, Nat.card_zpowers, hord] at h8
    norm_num at h8
  · have hord : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact ha.sq) ha.ne_one
    have h8 := h.card_eq_eight hK
    rw [hVt, Nat.card_zpowers, hord] at h8
    norm_num at h8
  · exact h.not_mem_USet hK hVU
  · have hbot : oddCoreOf L = ⊥ := TL4.oddCoreOf_eq_bot_of_isPGroup (h.thmD.two L hL)
    have hc : Commutes K L := fun x hx y hy => by
      have hm := hVL (Subgroup.commutator_mem_commutator hx hy)
      rw [hbot, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.mp hm
    exact hab (h9 K hK L hL hc a b ha hb)

theorem exists_involution_mul (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω) {a b : G} (ha : IsUniqueInvolution K a)
    (hb : IsUniqueInvolution L b) (hab : a ≠ b) :
    ∃ M ∈ Ω, ∃ u : G, IsUniqueInvolution M u ∧ u = a * b := by
  have hbN : b ∈ Subgroup.normalizer (K : Set G) :=
    h.pCore_le_normalizer h9 hV hK (h.mem_pCore hL hb)
  have htK : ∀ x ∈ K, b * x * b⁻¹ ∈ K := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hbN x).mp hx
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen ha (h.isQuatSub_of_mem hK) (h.card_eq_eight hK)
  obtain ⟨k, -, hkb⟩ := exists_conj_eq_mul_of_not_comm ha hi hj hii hjj hji hNF hb.sq htK
    (h.exists_not_commute_of_ne h9 hV hK hL ha hb hab)
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.sq
  have hconj : k * b * k⁻¹ = a * b := by
    have h1 : b * k⁻¹ * b⁻¹ = k⁻¹ * a := by
      calc b * k⁻¹ * b⁻¹ = (b * k * b⁻¹)⁻¹ := by group
        _ = (a * k)⁻¹ := by rw [hkb]
        _ = k⁻¹ * a := by rw [mul_inv_rev, hinv]
    calc k * b * k⁻¹ = k * (b * k⁻¹ * b⁻¹) * b := by group
      _ = a * b := by rw [h1]; group
  exact ⟨conjSub k L, h.thmD.hyp.conjInvariant k L hL, k * b * k⁻¹, hb.conj k, hconj⟩

theorem mem_zGroup_iff (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {x : G} :
    x ∈ zGroup Ω ↔ x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x := by
  have hmul : ∀ x y : G, (x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x) →
      (y = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L y) →
      (x * y = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L (x * y)) := by
    rintro x y (rfl | ⟨K, hK, ha⟩) (rfl | ⟨L, hL, hb⟩)
    · exact Or.inl (mul_one 1)
    · exact Or.inr ⟨L, hL, by rw [one_mul]; exact hb⟩
    · exact Or.inr ⟨K, hK, by rw [mul_one]; exact ha⟩
    · by_cases hxy : x = y
      · subst hxy
        exact Or.inl ha.sq
      · obtain ⟨M, hM, u, hu, rfl⟩ := h.exists_involution_mul h9 hV hK hL ha hb hxy
        exact Or.inr ⟨M, hM, hu⟩
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun x _ => x = 1 ∨ ∃ L ∈ Ω, IsUniqueInvolution L x) ?_ ?_ ?_ ?_ hx
    · intro x hx
      exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy
      exact hmul x y hx hy
    · intro x _ hx
      rcases hx with rfl | ⟨L, hL, hu⟩
      · exact Or.inl inv_one
      · exact Or.inr ⟨L, hL, by rw [inv_eq_of_mul_eq_one_right hu.sq]; exact hu⟩
  · rintro (rfl | ⟨L, hL, hu⟩)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨L, hL, hu⟩

theorem card_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) :
    Nat.card (zGroup Ω) = Set.ncard Ω + 1 := by
  classical
  set S : Set G := {u | ∃ L ∈ Ω, IsUniqueInvolution L u} with hSdef
  have h1 : ((zGroup Ω : Subgroup G) : Set G) = insert 1 S := by
    ext x
    rw [SetLike.mem_coe, h.mem_zGroup_iff h9 hV, Set.mem_insert_iff]
    rfl
  have hone : (1 : G) ∉ S := by
    rintro ⟨L, -, hu⟩
    exact hu.ne_one rfl
  have h2 : S.ncard = Set.ncard Ω := by
    let f : Subgroup G → G := fun L => if hL : ∃ u, IsUniqueInvolution L u then hL.choose else 1
    have hf : ∀ L ∈ Ω, IsUniqueInvolution L (f L) := by
      intro L hL
      have hex : ∃ u, IsUniqueInvolution L u := h.exists_isUniqueInvolution hL
      simp only [f, dif_pos hex]
      exact hex.choose_spec
    have himg : S = f '' Ω := by
      ext u
      constructor
      · rintro ⟨L, hL, hu⟩
        exact ⟨L, hL, hu.eq (hf L hL) ▸ rfl⟩
      · rintro ⟨L, hL, rfl⟩
        exact ⟨L, hL, hf L hL⟩
    rw [himg]
    refine Set.InjOn.ncard_image ?_
    intro L hL M hM hLM
    have hmem : M ∈ ({L} : Set (Subgroup G)) := by
      rw [← hV L hL]
      refine ⟨hM, f L, hf L hL, ?_⟩
      have := hf M hM
      rw [show f M = f L from hLM.symm] at this
      exact this
    exact (Set.mem_singleton_iff.mp hmem).symm
  have hD : Nat.card (zGroup Ω) = ((zGroup Ω : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [hD, h1, Set.ncard_insert_of_notMem hone, h2]

theorem zGroup_normal (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) :
    (zGroup Ω).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [h.mem_zGroup_iff h9 hV] at hn ⊢
  rcases hn with rfl | ⟨L, hL, hu⟩
  · exact Or.inl (by group)
  · exact Or.inr ⟨conjSub g L, h.thmD.hyp.conjInvariant g L hL, hu.conj g⟩

theorem zGroup_isPGroup : IsPGroup 2 (zGroup Ω) :=
  CFSG.pCore_isPGroup.to_le (h.zGroup_le_pCore)

theorem zGroup_le_normalizer (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) : zGroup Ω ≤ Subgroup.normalizer (K : Set G) :=
  h.zGroup_le_pCore.trans (h.pCore_le_normalizer h9 hV hK)

theorem eq_one_or_eq_of_mem_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z) (hxD : x ∈ zGroup Ω)
    (hxK : x ∈ K) : x = 1 ∨ x = z := by
  rcases (h.mem_zGroup_iff h9 hV).mp hxD with rfl | ⟨M, hM, hu⟩
  · exact Or.inl rfl
  · exact hz.unique x hxK hu.sq

theorem eq_one_or_eq_of_centralizes (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    {K : Subgroup G} (hK : K ∈ Ω) {z d : G} (hz : IsUniqueInvolution K z) (hd : d ∈ zGroup Ω)
    (hc : ∀ x ∈ K, d * x = x * d) : d = 1 ∨ d = z := by
  rcases (h.mem_zGroup_iff h9 hV).mp hd with rfl | ⟨M, hM, hu⟩
  · exact Or.inl rfl
  · by_cases hMK : M = K
    · subst hMK
      exact Or.inr (hz.eq hu).symm
    · by_contra hne
      have hdz : d ≠ z := fun e => hne (Or.inr e)
      obtain ⟨x, hx, hxd⟩ := h.exists_not_commute_of_ne h9 hV hK hM hz hu
        (fun e => hdz e.symm)
      exact hxd (hc x hx)

theorem dComm_eq_one_or (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {d k : G} (hd : d ∈ zGroup Ω)
    (hk : k ∈ K) : dComm d k = 1 ∨ dComm d k = z := by
  have hdN := h.zGroup_le_normalizer h9 hV hK hd
  have hcK : dComm d k ∈ K := dComm_mem hdN hk
  have hcD : dComm d k ∈ zGroup Ω := by
    have e : dComm d k = d * (k * d⁻¹ * k⁻¹) := by unfold dComm; group
    rw [e]
    exact (zGroup Ω).mul_mem hd ((h.zGroup_normal h9 hV).conj_mem _ ((zGroup Ω).inv_mem hd) k)
  exact h.eq_one_or_eq_of_mem_zGroup h9 hV hz hcD hcK

theorem dComm_mem_zpowers (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {d k : G} (hd : d ∈ zGroup Ω)
    (hk : k ∈ K) : dComm d k ∈ Subgroup.zpowers z := by
  rcases h.dComm_eq_one_or h9 hV hK hz hd hk with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact Subgroup.mem_zpowers z

@[expose] noncomputable def phiHom (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) :
    zGroup Ω →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) where
  toFun d := (⟨dComm (d : G) i, h.dComm_mem_zpowers h9 hV hK hQ.inv d.2 hQ.mem_i⟩,
    ⟨dComm (d : G) j, h.dComm_mem_zpowers h9 hV hK hQ.inv d.2 hQ.mem_j⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((1 : zGroup Ω) : G) i = 1
      simp [dComm]
    · show dComm ((1 : zGroup Ω) : G) j = 1
      simp [dComm]
  map_mul' a b := by
    have hb := h.dComm_eq_one_or h9 hV hK hQ.inv b.2 hQ.mem_i
    have hb' := h.dComm_eq_one_or h9 hV hK hQ.inv b.2 hQ.mem_j
    have ha := h.zGroup_le_normalizer h9 hV hK a.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((a * b : zGroup Ω) : G) i = dComm (a : G) i * dComm (b : G) i
      rw [Subgroup.coe_mul, dComm_mul_left hQ.inv ha hb]
      rcases hb with h1 | h1 <;> rcases h.dComm_eq_one_or h9 hV hK hQ.inv a.2 hQ.mem_i with
        h2 | h2 <;> rw [h1, h2] <;> simp
    · show dComm ((a * b : zGroup Ω) : G) j = dComm (a : G) j * dComm (b : G) j
      rw [Subgroup.coe_mul, dComm_mul_left hQ.inv ha hb']
      rcases hb' with h1 | h1 <;> rcases h.dComm_eq_one_or h9 hV hK hQ.inv a.2 hQ.mem_j with
        h2 | h2 <;> rw [h1, h2] <;> simp

theorem exists_q8Data {K : Subgroup G} (hK : K ∈ Ω) : ∃ z i j : G, Q8Data K z i j := by
  obtain ⟨z, hz⟩ := h.exists_isUniqueInvolution hK
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (h.isQuatSub_of_mem hK) (h.card_eq_eight hK)
  exact ⟨z, i, j, ⟨hz, hi, hj, hii, hjj, hji, hNF⟩⟩

theorem card_ker_phiHom_le (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) :
    Nat.card (h.phiHom h9 hV hK hQ).ker ≤ 2 := by
  have key : ∀ d : zGroup Ω, h.phiHom h9 hV hK hQ d = 1 → (d : G) = 1 ∨ (d : G) = z := by
    intro d hd
    have hi : dComm (d : G) i = 1 := congrArg Subtype.val (congrArg Prod.fst hd)
    have hj : dComm (d : G) j = 1 := congrArg Subtype.val (congrArg Prod.snd hd)
    have hdN := h.zGroup_le_normalizer h9 hV hK d.2
    have hgen : ∀ x ∈ K, dComm (d : G) x = 1 := by
      intro x hx
      rcases hQ.nf x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp [dComm]
      · exact dComm_z hQ.inv hdN
      · exact hi
      · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_i hdN
          (h.dComm_eq_one_or h9 hV hK hQ.inv d.2 hQ.mem_i), dComm_z hQ.inv hdN, hi, one_mul]
      · exact hj
      · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_j hdN
          (h.dComm_eq_one_or h9 hV hK hQ.inv d.2 hQ.mem_j), dComm_z hQ.inv hdN, hj, one_mul]
      · rw [dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hdN
          (h.dComm_eq_one_or h9 hV hK hQ.inv d.2 hQ.mem_j), hi, hj, one_mul]
      · rw [dComm_mul_right hQ.inv hQ.inv.mem (K.mul_mem hQ.mem_i hQ.mem_j) hdN
          (h.dComm_eq_one_or h9 hV hK hQ.inv d.2 (K.mul_mem hQ.mem_i hQ.mem_j)),
          dComm_z hQ.inv hdN, dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hdN
          (h.dComm_eq_one_or h9 hV hK hQ.inv d.2 hQ.mem_j), hi, hj, one_mul, one_mul]
    exact h.eq_one_or_eq_of_centralizes h9 hV hK hQ.inv d.2
      (fun x hx => dComm_eq_one_iff.mp (hgen x hx))
  have hmem : ∀ d : (h.phiHom h9 hV hK hQ).ker, (d.1 : G) ∈ Subgroup.zpowers z := by
    intro d
    rcases key d.1 (MonoidHom.mem_ker.mp d.2) with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  have hinj : Function.Injective (fun d : (h.phiHom h9 hV hK hQ).ker =>
      (⟨(d.1 : G), hmem d⟩ : ↥(Subgroup.zpowers z))) := by
    intro a b hab
    have hval : ((a.1 : zGroup Ω) : G) = ((b.1 : zGroup Ω) : G) := by
      have := congrArg Subtype.val hab
      simpa using this
    exact Subtype.ext (Subtype.ext hval)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_zpowers_of_involution hQ.inv.sq hQ.inv.ne_one] at this

theorem phiHom_surjective (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) (hD : Nat.card (zGroup Ω) = 8) :
    Function.Surjective (h.phiHom h9 hV hK hQ) :=
  surjective_of_card_ker _ hD (card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one)
    (h.card_ker_phiHom_le h9 hV hK hQ)

theorem card_zGroup_le (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) :
    Nat.card (zGroup Ω) ≤ 8 := by
  obtain ⟨K, hK, -, -, -⟩ := h.exists_ne
  obtain ⟨z, i, j, hQ⟩ := h.exists_q8Data hK
  have h1 := Subgroup.card_mul_index (h.phiHom h9 hV hK hQ).ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card (h.phiHom h9 hV hK hQ).range ≤ 4 := by
    have := Subgroup.card_le_card_group (h.phiHom h9 hV hK hQ).range
    rwa [card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one] at this
  have h3 := h.card_ker_phiHom_le h9 hV hK hQ
  rw [← h1]
  exact (Nat.mul_le_mul h3 h2).trans (by norm_num)

theorem exists_dComm_pair (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j) (hD : Nat.card (zGroup Ω) = 8) {p q : G}
    (hp : p = 1 ∨ p = z) (hq : q = 1 ∨ q = z) :
    ∃ d ∈ zGroup Ω, dComm d i = p ∧ dComm d j = q := by
  have hpm : p ∈ Subgroup.zpowers z := by
    rcases hp with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  have hqm : q ∈ Subgroup.zpowers z := by
    rcases hq with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  obtain ⟨d, hd⟩ := h.phiHom_surjective h9 hV hK hQ hD ⟨⟨p, hpm⟩, ⟨q, hqm⟩⟩
  exact ⟨d, d.2, congrArg (fun y => (y.1 : G)) (congrArg Prod.fst hd),
    congrArg (fun y => (y.1 : G)) (congrArg Prod.snd hd)⟩

theorem eq_one_or_eq_of_centralizes_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    {K : Subgroup G} (hK : K ∈ Ω) {z i j : G} (hQ : Q8Data K z i j)
    (hD : Nat.card (zGroup Ω) = 8) {x : G} (hxK : x ∈ K) (hx : ∀ d ∈ zGroup Ω, d * x = x * d) :
    x = 1 ∨ x = z := by
  obtain ⟨d₁, hd₁, e1, e2⟩ := h.exists_dComm_pair h9 hV hK hQ hD (p := z) (q := 1)
    (Or.inr rfl) (Or.inl rfl)
  obtain ⟨d₂, hd₂, e3, e4⟩ := h.exists_dComm_pair h9 hV hK hQ hD (p := 1) (q := z)
    (Or.inl rfl) (Or.inr rfl)
  have hN1 := h.zGroup_le_normalizer h9 hV hK hd₁
  have hN2 := h.zGroup_le_normalizer h9 hV hK hd₂
  have c1 : dComm d₁ x = 1 := dComm_eq_one_iff.mpr (hx d₁ hd₁)
  have c2 : dComm d₂ x = 1 := dComm_eq_one_iff.mpr (hx d₂ hd₂)
  have hz1 := hQ.inv.ne_one
  rcases hQ.nf x hxK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · rw [e1] at c1
    exact absurd c1 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_i hN1
      (h.dComm_eq_one_or h9 hV hK hQ.inv hd₁ hQ.mem_i), dComm_z hQ.inv hN1, e1, one_mul] at c1
    exact absurd c1 hz1
  · rw [e4] at c2
    exact absurd c2 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem hQ.mem_j hN2
      (h.dComm_eq_one_or h9 hV hK hQ.inv hd₂ hQ.mem_j), dComm_z hQ.inv hN2, e4, one_mul] at c2
    exact absurd c2 hz1
  · rw [dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hN1
      (h.dComm_eq_one_or h9 hV hK hQ.inv hd₁ hQ.mem_j), e1, e2, mul_one] at c1
    exact absurd c1 hz1
  · rw [dComm_mul_right hQ.inv hQ.inv.mem (K.mul_mem hQ.mem_i hQ.mem_j) hN1
      (h.dComm_eq_one_or h9 hV hK hQ.inv hd₁ (K.mul_mem hQ.mem_i hQ.mem_j)),
      dComm_z hQ.inv hN1, dComm_mul_right hQ.inv hQ.mem_i hQ.mem_j hN1
      (h.dComm_eq_one_or h9 hV hK hQ.inv hd₁ hQ.mem_j), e1, e2, mul_one, one_mul] at c1
    exact absurd c1 hz1

theorem zGroup_card (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) :
    Nat.card (zGroup Ω) = 8 := by
  obtain ⟨L, hL, L', hL', hLL'⟩ := h.exists_ne
  have h2 : 2 ≤ Set.ncard Ω := by
    have hsub : ({L, L'} : Set (Subgroup G)) ⊆ Ω := by
      intro x hx
      rcases hx with rfl | rfl
      · exact hL
      · exact hL'
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair hLL'] at hle
  have hcard := h.card_zGroup h9 hV
  have hle8 := h.card_zGroup_le h9 hV
  have h3 : 3 ≤ Nat.card (zGroup Ω) := by rw [hcard]; omega
  obtain ⟨n, hn⟩ := h.zGroup_isPGroup.exists_card_eq
  have hpow : Nat.card (zGroup Ω) = 4 ∨ Nat.card (zGroup Ω) = 8 := by
    rw [hn] at h3 hle8 ⊢
    have hn4 : n < 4 := by
      by_contra hc
      push Not at hc
      have h16 : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
      have := h16.trans hle8
      norm_num at this
    interval_cases n
    · norm_num at h3
    · norm_num at h3
    · left; norm_num
    · right; norm_num
  rcases hpow with h4 | h8
  · exfalso
    have hΩ3 : Set.ncard Ω = 3 := by omega
    have hDW3 := three_le_ncard_DSet h.thmD.hyp hW hS3
    have hsub : DSet Ω W ⊆ Ω := fun R hR => ((h.mem_dSet_iff).mp hR).1
    have hle : Set.ncard Ω ≤ Set.ncard (DSet Ω W) := by omega
    have heq : DSet Ω W = Ω := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
    have hnorm : ∀ M ∈ Ω, M ≤ Subgroup.normalizer (W : Set G) := fun M hM => by
      have hMD : M ∈ DSet Ω W := by
        rw [heq]
        exact hM
      exact ((h.mem_dSet_iff).mp hMD).2
    have hWn : W.Normal := by
      have htop : (⊤ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
        rw [← h.thmD.gen]
        exact pSpan_le hnorm
      exact ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (htop (Subgroup.mem_top g)) n).mp hn⟩
    exact h.wSet_ne W (TC.Thin.wSet_eq_singleton_of_normal h.thmD.hyp h.thmD.two
      h.thmD.trans h.thmD.gen (fun hall => hLL' (hall L hL L' hL')) hW hWn)
  · exact h8

theorem centralizer_zGroup_normal (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) :
    (Subgroup.centralizer (zGroup Ω : Set G)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro d hd
  have hd' : g⁻¹ * d * g ∈ zGroup Ω := by
    have := (h.zGroup_normal h9 hV).conj_mem d hd g⁻¹
    rwa [inv_inv] at this
  have key := hc _ hd'
  calc d * (g * c * g⁻¹) = g * ((g⁻¹ * d * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * d * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * d := by group

theorem eq_one_of_odd_mem_centralizer (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) {x : G}
    (hx : x ∈ Subgroup.centralizer (zGroup Ω : Set G)) {m : ℕ} (hxp : x ^ (2 * m + 1) = 1) :
    x = 1 := by
  have hxD : ∀ d ∈ zGroup Ω, d * x = x * d := Subgroup.mem_centralizer_iff.mp hx
  have hC := h.centralizer_zGroup_normal h9 hV
  have hmem : ∀ L ∈ Ω, ∀ y ∈ L, Commute x y := by
    intro L hL y hy
    obtain ⟨z, i, j, hQ⟩ := h.exists_q8Data hL
    have hzD : z ∈ zGroup Ω := (h.mem_zGroup_iff h9 hV).mpr (Or.inr ⟨L, hL, hQ.inv⟩)
    have hxz : x * z = z * x := (hxD z hzD).symm
    have hxzc : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
    have hnorm : x ∈ Subgroup.normalizer (L : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq]
      have hc2 := hQ.inv.conj x
      rw [hxzc] at hc2
      have hc : conjSub x L ∈ twinSet Ω L := ⟨h.thmD.hyp.conjInvariant x L hL, z, hQ.inv, hc2⟩
      rw [hV L hL, Set.mem_singleton_iff] at hc
      exact hc
    have hcomm : ∀ w ∈ L, dComm x w = 1 ∨ dComm x w = z := by
      intro w hw
      have hwL : dComm x w ∈ L := dComm_mem hnorm hw
      have hwC : dComm x w ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
        have e : dComm x w = x * (w * x⁻¹ * w⁻¹) := by unfold dComm; group
        rw [e]
        exact (Subgroup.centralizer (zGroup Ω : Set G)).mul_mem hx
          (hC.conj_mem x⁻¹ ((Subgroup.centralizer (zGroup Ω : Set G)).inv_mem hx) w)
      exact h.eq_one_or_eq_of_centralizes_zGroup h9 hV hL hQ hD8 hwL
        (fun d hd => (Subgroup.mem_centralizer_iff.mp hwC) d hd)
    have hxzp : Commute x z := hxz
    have hcz : Commute (x ^ 2) z := hxzp.pow_left 2
    have hci : Commute (x ^ 2) i :=
      commute_sq_of_dComm hQ.inv hxz (hcomm i hQ.mem_i) rfl
    have hcj : Commute (x ^ 2) j :=
      commute_sq_of_dComm hQ.inv hxz (hcomm j hQ.mem_j) rfl
    have hsq : Commute (x ^ 2) y := commute_sq_of_gen hQ hcz hci hcj hy
    have hpow : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hxp, one_mul]
    have hxy := hsq.pow_left (m + 1)
    rw [hpow] at hxy
    exact hxy
  have hcent : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [← h.thmD.gen]
    apply pSpan_le
    intro L hL y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hmem L hL y hy).eq.symm
  have hxcenter : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent (Subgroup.mem_top g))
  rw [h.center, Subgroup.mem_bot] at hxcenter
  exact hxcenter

theorem isPGroup_centralizer_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) :
    IsPGroup 2 (Subgroup.centralizer (zGroup Ω : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd
      (Nat.card (Subgroup.centralizer (zGroup Ω : Set G))) with hpow | ⟨p, hp, hdvd, hodd⟩
  · exact hpow
  · exfalso
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hord : orderOf (c : G) = p := (Subgroup.orderOf_coe c).trans hc
    obtain ⟨m, hm⟩ := hodd
    have hxp : (c : G) ^ (2 * m + 1) = 1 := by
      rw [← hm, ← hord, pow_orderOf_eq_one]
    have hx1 := h.eq_one_of_odd_mem_centralizer h9 hV hD8 c.2 hxp
    rw [hx1, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm

theorem centralizer_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) :
    Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G := by
  have hD8 := h.zGroup_card h9 hV hW hS3
  apply le_antisymm
  · exact le_sSup ⟨h.centralizer_zGroup_normal h9 hV,
      h.isPGroup_centralizer_zGroup h9 hV hD8⟩
  · exact h.pCore_le_centralizer_zGroup h9

theorem dComm_pCore_inter (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G) {K : Subgroup G} (hK : K ∈ Ω)
    {z i j : G} (hQ : Q8Data K z i j) {f w : G} (hf : f ∈ pCore 2 G) (hw : w ∈ K) :
    dComm f w = 1 ∨ dComm f w = z := by
  have hfN := (h.pCore_le_normalizer h9 hV hK) hf
  have hwK : dComm f w ∈ K := dComm_mem hfN hw
  have hwQ : dComm f w ∈ pCore 2 G := by
    have e : dComm f w = f * (w * f⁻¹ * w⁻¹) := by unfold dComm; group
    rw [e]
    exact (pCore 2 G).mul_mem hf (CFSG.pCore_normal.conj_mem f⁻¹ ((pCore 2 G).inv_mem hf) w)
  have hwC : dComm f w ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    rw [hC]
    exact hwQ
  exact h.eq_one_or_eq_of_centralizes_zGroup h9 hV hK hQ hD8 hwK
    (fun d hd => (Subgroup.mem_centralizer_iff.mp hwC) d hd) |> fun e => by
      rcases e with e | e
      · exact Or.inl e
      · exact Or.inr e

theorem dComm_pCore_mem (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G) {L : Subgroup G} (hL : L ∈ Ω)
    {q y : G} (hq : q ∈ pCore 2 G) (hy : y ∈ L) : dComm q y ∈ zGroup Ω := by
  obtain ⟨z, i, j, hQ⟩ := h.exists_q8Data hL
  rcases h.dComm_pCore_inter h9 hV hD8 hC hL hQ hq hy with e | e
  · rw [e]
    exact (zGroup Ω).one_mem
  · rw [e]
    exact (h.mem_zGroup_iff h9 hV).mpr (Or.inr ⟨L, hL, hQ.inv⟩)

theorem dComm_all_mem (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G) (g : G) {q : G}
    (hq : q ∈ pCore 2 G) : dComm g q ∈ zGroup Ω := by
  let T : Subgroup G :=
    { carrier := {g | ∀ q ∈ pCore 2 G, dComm g q ∈ zGroup Ω}
      mul_mem' := by
        intro a b ha hb q hq
        have e : dComm (a * b) q = (a * dComm b q * a⁻¹) * dComm a q := by
          unfold dComm
          group
        rw [e]
        exact (zGroup Ω).mul_mem ((h.zGroup_normal h9 hV).conj_mem _ (hb q hq) a) (ha q hq)
      one_mem' := by
        intro q _
        unfold dComm
        simp
      inv_mem' := by
        intro a ha q hq
        have e : dComm a⁻¹ q = a⁻¹ * (dComm a q)⁻¹ * a⁻¹⁻¹ := by
          unfold dComm
          group
        rw [e]
        exact (h.zGroup_normal h9 hV).conj_mem _ ((zGroup Ω).inv_mem (ha q hq)) a⁻¹ }
  have hLT : ∀ L ∈ Ω, L ≤ T := by
    intro L hL y hy q hq
    have e : dComm y q = (dComm q y)⁻¹ := by
      unfold dComm
      group
    show dComm y q ∈ zGroup Ω
    rw [e]
    exact (zGroup Ω).inv_mem (h.dComm_pCore_mem h9 hV hD8 hC hL hq hy)
  have hTtop : (⊤ : Subgroup G) ≤ T := by
    rw [← h.thmD.gen]
    exact pSpan_le hLT
  exact (hTtop (Subgroup.mem_top g)) q hq

theorem pCore_le_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8)
    (hC : Subgroup.centralizer (zGroup Ω : Set G) = pCore 2 G) : pCore 2 G ≤ zGroup Ω := by
  intro f hfQ
  by_contra hfD
  have hact : ∀ g : G, ∀ x : G, (∃ d ∈ zGroup Ω, x = f * d) →
      ∃ d ∈ zGroup Ω, g * x * g⁻¹ = f * d := by
    rintro g x ⟨d, hd, rfl⟩
    have hc := h.dComm_all_mem h9 hV hD8 hC g hfQ
    refine ⟨f⁻¹ * dComm g f * f⁻¹⁻¹ * (g * d * g⁻¹), ?_, ?_⟩
    · exact (zGroup Ω).mul_mem ((h.zGroup_normal h9 hV).conj_mem _ hc f⁻¹)
        ((h.zGroup_normal h9 hV).conj_mem _ hd g)
    · have e : g * (f * d) * g⁻¹ = (dComm g f * f) * (g * d * g⁻¹) := by
        unfold dComm
        group
      rw [e]
      group
  letI : MulAction G {x : G // ∃ d ∈ zGroup Ω, x = f * d} :=
    { smul := fun g x => ⟨g * x.1 * g⁻¹, hact g x.1 x.2⟩
      one_smul := fun x => Subtype.ext (by show 1 * x.1 * 1⁻¹ = x.1; simp)
      mul_smul := fun g g' x => Subtype.ext (by
        show g * g' * x.1 * (g * g')⁻¹ = g * (g' * x.1 * g'⁻¹) * g⁻¹
        group) }
  letI : MulAction G {L : Subgroup G // L ∈ Ω} :=
    { smul := fun g L => ⟨conjSub g L.1, h.thmD.hyp.conjInvariant g L.1 L.2⟩
      one_smul := fun L => Subtype.ext (conjSub_one L.1)
      mul_smul := fun g g' L => Subtype.ext (conjSub_mul g g' L.1) }
  have hXcard : Nat.card {x : G // ∃ d ∈ zGroup Ω, x = f * d} = Nat.card (zGroup Ω) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨f⁻¹ * x.1, by
          obtain ⟨d, hd, hx⟩ := x.2
          rw [hx, inv_mul_cancel_left]
          exact hd⟩
        invFun := fun d => ⟨f * d.1, d.1, d.2, rfl⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun d => Subtype.ext (by simp) }
  haveI : Fintype {x : G // ∃ d ∈ zGroup Ω, x = f * d} := Fintype.ofFinite _
  haveI : Fintype {L : Subgroup G // L ∈ Ω} := Fintype.ofFinite _
  have hX8 : Fintype.card {x : G // ∃ d ∈ zGroup Ω, x = f * d} = 8 := by
    rw [← Nat.card_eq_fintype_card, hXcard, hD8]
  have hY7 : Fintype.card {L : Subgroup G // L ∈ Ω} = 7 := by
    have h7 : Nat.card (Ω : Set (Subgroup G)) = 7 := by
      rw [Nat.card_coe_set_eq]
      have := h.card_zGroup h9 hV
      omega
    rw [← Nat.card_eq_fintype_card]
    exact h7
  have htr : ∀ L L' : {L : Subgroup G // L ∈ Ω}, ∃ g : G, g • L = L' := by
    intro L L'
    obtain ⟨g, hg⟩ := h.thmD.trans L.1 L.2 L'.1 L'.2
    exact ⟨g, Subtype.ext hg⟩
  have hR : ∀ (g : G) (x : {x : G // ∃ d ∈ zGroup Ω, x = f * d})
      (L : {L : Subgroup G // L ∈ Ω}), (∀ y ∈ L.1, x.1 * y = y * x.1) →
      ∀ y ∈ (g • L).1, (g • x).1 * y = y * (g • x).1 := by
    intro g x L hxL y hy
    have hy' : g⁻¹ * y * g ∈ L.1 := (mem_conjSub_iff).mp hy
    show g * x.1 * g⁻¹ * y = y * (g * x.1 * g⁻¹)
    calc g * x.1 * g⁻¹ * y = g * (x.1 * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x.1) * g⁻¹ := by rw [hxL _ hy']
      _ = y * (g * x.1 * g⁻¹) := by group
  have hcent : ∀ x : {x : G // ∃ d ∈ zGroup Ω, x = f * d},
      (∀ L : {L : Subgroup G // L ∈ Ω}, ∀ y ∈ L.1, x.1 * y = y * x.1) → ∀ g : G, g • x = x := by
    intro x hx g
    have hcz : (⊤ : Subgroup G) ≤ Subgroup.centralizer ({x.1} : Set G) := by
      rw [← h.thmD.gen]
      apply pSpan_le
      intro L hL y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hx ⟨L, hL⟩ y hy).symm
    have hgx := Subgroup.mem_centralizer_singleton_iff.mp (hcz (Subgroup.mem_top g))
    apply Subtype.ext
    show g * x.1 * g⁻¹ = x.1
    rw [hgx, mul_inv_cancel_right]
  have hfree : ∀ x : {x : G // ∃ d ∈ zGroup Ω, x = f * d}, ∃ g : G, g • x ≠ x := by
    intro x
    by_contra hall
    push Not at hall
    have hcen : x.1 ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g * x.1 * g⁻¹ = x.1 := congrArg Subtype.val (hall g)
      calc g * x.1 = (g * x.1 * g⁻¹) * g := by group
        _ = x.1 * g := by rw [hg]
    rw [h.center, Subgroup.mem_bot] at hcen
    obtain ⟨d, hd, hx⟩ := x.2
    apply hfD
    have hfd1 : f * d = 1 := by
      rw [← hx]
      exact hcen
    have hfd : f = d⁻¹ := eq_inv_of_mul_eq_one_left hfd1
    rw [hfd]
    exact (zGroup Ω).inv_mem hd
  have hex : ∃ x : {x : G // ∃ d ∈ zGroup Ω, x = f * d},
      ∃ L : {L : Subgroup G // L ∈ Ω}, ∀ y ∈ L.1, x.1 * y = y * x.1 := by
    obtain ⟨K, hK, -, -, -⟩ := h.exists_ne
    obtain ⟨z, i, j, hQ⟩ := h.exists_q8Data hK
    have hpi := h.dComm_pCore_inter h9 hV hD8 hC hK hQ hfQ hQ.mem_i
    have hpj := h.dComm_pCore_inter h9 hV hD8 hC hK hQ hfQ hQ.mem_j
    obtain ⟨d, hd, hdi, hdj⟩ := h.exists_dComm_pair h9 hV hK hQ hD8 hpi hpj
    have hdN := h.zGroup_le_normalizer h9 hV hK hd
    have hfN := (h.pCore_le_normalizer h9 hV hK) hfQ
    have hxN : d * f ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ hdN hfN
    have hcomm1 : ∀ k ∈ K, dComm (d * f) k = 1 ∨ dComm (d * f) k = z := by
      intro k hk
      rw [dComm_mul_left hQ.inv hdN (h.dComm_pCore_inter h9 hV hD8 hC hK hQ hfQ hk)]
      rcases h.dComm_pCore_inter h9 hV hD8 hC hK hQ hfQ hk with e1 | e1 <;>
        rcases h.dComm_eq_one_or h9 hV hK hQ.inv hd hk with e2 | e2 <;> rw [e1, e2] <;>
        simp [hQ.inv.sq]
    have hi : dComm (d * f) i = 1 := by
      rw [dComm_mul_left hQ.inv hdN hpi, hdi]
      rcases hpi with e1 | e1 <;> rw [e1] <;> simp [hQ.inv.sq]
    have hj : dComm (d * f) j = 1 := by
      rw [dComm_mul_left hQ.inv hdN hpj, hdj]
      rcases hpj with e1 | e1 <;> rw [e1] <;> simp [hQ.inv.sq]
    have hall : ∀ k ∈ K, dComm (d * f) k = 1 :=
      fun k hk => dComm_eq_one_of_gens hQ hxN hcomm1 hi hj hk
    have hmemX : d * f = f * (f⁻¹ * d * f⁻¹⁻¹) := by group
    have hdmem : f⁻¹ * d * f⁻¹⁻¹ ∈ zGroup Ω := (h.zGroup_normal h9 hV).conj_mem d hd f⁻¹
    exact ⟨⟨d * f, f⁻¹ * d * f⁻¹⁻¹, hdmem, hmemX⟩, ⟨K, hK⟩, fun y hy =>
      dComm_eq_one_iff.mp (hall y hy)⟩
  exact seven_orbit_false hX8 hY7 htr (fun x L => ∀ y ∈ L.1, x.1 * y = y * x.1) hR hcent hfree
    hex

theorem pCore_eq_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) :
    pCore 2 G = zGroup Ω := by
  have hD8 := h.zGroup_card h9 hV hW hS3
  have hC := h.centralizer_zGroup h9 hV hW hS3
  exact le_antisymm (h.pCore_le_zGroup h9 hV hD8 hC) h.zGroup_le_pCore


@[expose] noncomputable def rhoD (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) : G →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) where
  toFun x := ⟨TL4.conjMat he x,
    TL4.det_conjMat he (fun y hy => (h.zGroup_normal h9 hV).conj_mem y hy x)
      (fun y hy => (h.zGroup_normal h9 hV).conj_mem y hy x⁻¹)⟩
  map_one' := Subtype.ext (TL4.conjMat_one he)
  map_mul' x y := Subtype.ext (TL4.conjMat_mul he
    (fun z hz => (h.zGroup_normal h9 hV).conj_mem z hz x)
    (fun z hz => (h.zGroup_normal h9 hV).conj_mem z hz y))

theorem rhoD_val (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) (x : G) :
    ((h.rhoD h9 hV he x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3)
      (ZMod 2)) = TL4.conjMat he x := rfl

theorem rhoD_ker (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hCD : Subgroup.centralizer (zGroup Ω : Set G) ≤ zGroup Ω) {e : Fin 3 → G}
    (he : TL4.E8Basis (zGroup Ω) e) : (h.rhoD h9 hV he).ker = zGroup Ω := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hc : TL4.conjMat he x = 1 := congrArg Subtype.val hx
    apply hCD
    refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
    obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hd
    have h1 := TL4.conj_e8Coord he (fun y hy => (h.zGroup_normal h9 hV).conj_mem y hy x) v
    rw [hc, Matrix.one_mulVec] at h1
    calc TL4.e8Coord e v * x = (x * TL4.e8Coord e v * x⁻¹) * x := by rw [h1]
      _ = x * TL4.e8Coord e v := by group
  · intro hx
    apply Subtype.ext
    show TL4.conjMat he x = 1
    refine TL4.matrix_ext_mulVec fun v => ?_
    rw [Matrix.one_mulVec]
    refine TL4.e8Coord_injective he ?_
    rw [← TL4.conj_e8Coord he (fun y hy => (h.zGroup_normal h9 hV).conj_mem y hy x) v]
    have hcomm := h.zGroup_comm h9 x hx (TL4.e8Coord e v) (TL4.e8Coord_mem he v)
    rw [hcomm]
    group

theorem dComm_left_mem (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {x d : G} (hx : x ∈ K)
    (hd : d ∈ zGroup Ω) : dComm x d = 1 ∨ dComm x d = z := by
  have hdN := h.zGroup_le_normalizer h9 hV hK hd
  have hcK : dComm x d ∈ K := by
    have e : dComm x d = x * (d * x⁻¹ * d⁻¹) := by unfold dComm; group
    rw [e]
    exact K.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hdN x⁻¹).mp (K.inv_mem hx))
  have hcD : dComm x d ∈ zGroup Ω :=
    (zGroup Ω).mul_mem ((h.zGroup_normal h9 hV).conj_mem d hd x) ((zGroup Ω).inv_mem hd)
  exact h.eq_one_or_eq_of_mem_zGroup h9 hV hz hcD hcK

theorem dComm_mul_left_K {K : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) {x y d : G}
    (hx : x ∈ K) (hc : dComm y d = 1 ∨ dComm y d = z) :
    dComm (x * y) d = dComm y d * dComm x d := by
  have hxc := conj_of_mem_mem hz hx hc
  calc dComm (x * y) d = (x * dComm y d * x⁻¹) * dComm x d := by unfold dComm; group
    _ = dComm y d * dComm x d := by rw [hxc]

@[expose] noncomputable def psiHom (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {d₁ d₂ : G} (hd₁ : d₁ ∈ zGroup Ω)
    (hd₂ : d₂ ∈ zGroup Ω) : K →* ↥(Subgroup.zpowers z) × ↥(Subgroup.zpowers z) where
  toFun x := (⟨dComm (x : G) d₁, by
      rcases h.dComm_left_mem h9 hV hK hz x.2 hd₁ with e | e
      · rw [e]
        exact Subgroup.one_mem _
      · rw [e]
        exact Subgroup.mem_zpowers z⟩,
    ⟨dComm (x : G) d₂, by
      rcases h.dComm_left_mem h9 hV hK hz x.2 hd₂ with e | e
      · rw [e]
        exact Subgroup.one_mem _
      · rw [e]
        exact Subgroup.mem_zpowers z⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((1 : K) : G) d₁ = 1
      simp [dComm]
    · show dComm ((1 : K) : G) d₂ = 1
      simp [dComm]
  map_mul' a b := by
    have hb₁ := h.dComm_left_mem h9 hV hK hz b.2 hd₁
    have hb₂ := h.dComm_left_mem h9 hV hK hz b.2 hd₂
    have ha₁ := h.dComm_left_mem h9 hV hK hz a.2 hd₁
    have ha₂ := h.dComm_left_mem h9 hV hK hz a.2 hd₂
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show dComm ((a * b : K) : G) d₁ = dComm (a : G) d₁ * dComm (b : G) d₁
      rw [Subgroup.coe_mul, h.dComm_mul_left_K hz a.2 hb₁]
      rcases hb₁ with e | e <;> rcases ha₁ with e' | e' <;> rw [e, e'] <;> simp [hz.sq]
    · show dComm ((a * b : K) : G) d₂ = dComm (a : G) d₂ * dComm (b : G) d₂
      rw [Subgroup.coe_mul, h.dComm_mul_left_K hz a.2 hb₂]
      rcases hb₂ with e | e <;> rcases ha₂ with e' | e' <;> rw [e, e'] <;> simp [hz.sq]


theorem centralizes_of_basis {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {x : G}
    (h1 : ∀ m : Fin 3, x * e m = e m * x) : x ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hd
  have hc : ∀ m : Fin 3, Commute x (e m) := fun m => h1 m
  unfold TL4.e8Coord
  exact ((((hc 0).pow_right _).mul_right ((hc 1).pow_right _)).mul_right
    ((hc 2).pow_right _)).symm.eq

theorem card_ker_psiHom_le (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) {K : Subgroup G} (hK : K ∈ Ω) {z a b : G}
    (hQ : Q8Data K z a b) {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {i j k : Fin 3}
    (hi : e i = z) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Nat.card (h.psiHom h9 hV hK hQ.inv (he.mem j) (he.mem k)).ker ≤ 2 := by
  have key : ∀ x : K, h.psiHom h9 hV hK hQ.inv (he.mem j) (he.mem k) x = 1 →
      (x : G) = 1 ∨ (x : G) = z := by
    intro x hx
    have hxj : dComm (x : G) (e j) = 1 := congrArg Subtype.val (congrArg Prod.fst hx)
    have hxk : dComm (x : G) (e k) = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
    have hxz : x * z = z * x := isUniqueInvolution_comm hQ.inv x.2
    have hcomm : ∀ m : Fin 3, (x : G) * e m = e m * (x : G) := by
      intro m
      rcases fin3_cover i j k m hij hik.symm hjk.symm with rfl | rfl | rfl
      · rw [hi]
        exact hxz
      · exact dComm_eq_one_iff.mp hxj
      · exact dComm_eq_one_iff.mp hxk
    have hC : (x : G) ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      h.centralizes_of_basis he (fun m => hcomm m)
    exact h.eq_one_or_eq_of_centralizes_zGroup h9 hV hK hQ hD8 x.2
      (fun d hd => (Subgroup.mem_centralizer_iff.mp hC) d hd)
  have hmem : ∀ x : (h.psiHom h9 hV hK hQ.inv (he.mem j) (he.mem k)).ker,
      ((x : K) : G) ∈ Subgroup.zpowers z := by
    intro x
    rcases key x.1 (MonoidHom.mem_ker.mp x.2) with h1 | h1 <;> rw [h1]
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers z
  have hinj : Function.Injective (fun x : (h.psiHom h9 hV hK hQ.inv (he.mem j) (he.mem k)).ker =>
      (⟨((x : K) : G), hmem x⟩ : ↥(Subgroup.zpowers z))) := by
    intro x y hxy
    have hval : ((x.1 : K) : G) = ((y.1 : K) : G) := by
      have := congrArg Subtype.val hxy
      simpa using this
    exact Subtype.ext (Subtype.ext hval)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [card_zpowers_of_involution hQ.inv.sq hQ.inv.ne_one] at this

theorem psiHom_surjective (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) {K : Subgroup G} (hK : K ∈ Ω) {z a b : G}
    (hQ : Q8Data K z a b) {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {i j k : Fin 3}
    (hi : e i = z) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Surjective (h.psiHom h9 hV hK hQ.inv (he.mem j) (he.mem k)) :=
  surjective_of_card_ker _ (h.card_eq_eight hK) (card_zpowers_prod_eq_four hQ.inv.sq hQ.inv.ne_one)
    (h.card_ker_psiHom_le h9 hV hD8 hK hQ he hi hij hik hjk)

theorem conjMat_eq_transvection {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {x : G}
    (hxN : ∀ y ∈ zGroup Ω, x * y * x⁻¹ ∈ zGroup Ω) (hxj : dComm x (e j) = e i)
    (hxk : dComm x (e k) = 1) (hxi : dComm x (e i) = 1) :
    TL4.conjMat he x = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) + Matrix.single i j 1 := by
  have hcol : ∀ c : Fin 3, x * e c * x⁻¹ =
      TL4.e8Coord e ((if c = j then Pi.single i 1 else 0) + Pi.single c 1) := by
    intro c
    by_cases hc : c = j
    · rw [hc, if_pos rfl, TL4.e8Coord_add he, TL4.e8Coord_single, TL4.e8Coord_single]
      have e1 : x * e j * x⁻¹ = dComm x (e j) * e j := by unfold dComm; group
      rw [e1, hxj]
    · rw [if_neg hc, zero_add, TL4.e8Coord_single]
      rcases fin3_cover i j k c hij hik.symm hjk.symm with rfl | rfl | rfl
      · have e1 : x * e c * x⁻¹ = dComm x (e c) * e c := by unfold dComm; group
        rw [e1, hxi, one_mul]
      · exact absurd rfl hc
      · have e1 : x * e c * x⁻¹ = dComm x (e c) * e c := by unfold dComm; group
        rw [e1, hxk, one_mul]
  have hcm : ∀ r c, TL4.conjMat he x r c = TL4.e8Inv he (x * e c * x⁻¹) r := by
    intro r c
    have h1 := TL4.conj_e8Coord he hxN (Pi.single c 1)
    rw [TL4.e8Coord_single] at h1
    rw [h1, TL4.e8Inv_e8Coord he, Matrix.mulVec_single_one]
    rfl
  ext r c
  rw [hcm, hcol c, TL4.e8Inv_e8Coord he]
  clear hcm hcol hxN hxj hxk hxi
  revert hij
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases c <;> decide

theorem transvection_mem_range (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {i j : Fin 3}
    (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) ∈ (h.rhoD h9 hV he).range := by
  obtain ⟨k, hki, hkj⟩ := fin3_third i j hij
  have hik : i ≠ k := fun e' => hki e'.symm
  have hjk : j ≠ k := fun e' => hkj e'.symm
  have hne1 : ∀ m, e m ≠ 1 := by
    intro m
    fin_cases m
    · exact he.ne0
    · exact he.ne1.1
    · exact he.ne2.1
  obtain ⟨K, hK, hKz⟩ : ∃ K ∈ Ω, IsUniqueInvolution K (e i) := by
    rcases (h.mem_zGroup_iff h9 hV).mp (he.mem i) with h1 | h1
    · exact absurd h1 (hne1 i)
    · exact h1
  obtain ⟨z', a, b, hQ⟩ := h.exists_q8Data hK
  have hzz : z' = e i := hQ.inv.eq hKz
  subst hzz
  obtain ⟨x, hx⟩ := h.psiHom_surjective h9 hV hD8 hK hQ he rfl hij hik hjk
    (⟨⟨e i, Subgroup.mem_zpowers _⟩, ⟨1, Subgroup.one_mem _⟩⟩)
  have hxj : dComm (x : G) (e j) = e i := congrArg Subtype.val (congrArg Prod.fst hx)
  have hxk : dComm (x : G) (e k) = 1 := congrArg Subtype.val (congrArg Prod.snd hx)
  have hxi : dComm (x : G) (e i) = 1 := by
    rw [dComm_eq_one_iff]
    exact isUniqueInvolution_comm hQ.inv x.2
  refine ⟨(x : G), Subtype.ext ?_⟩
  rw [h.rhoD_val, Matrix.SpecialLinearGroup.transvection_coe]
  exact h.conjMat_eq_transvection he hij hik hjk
    (fun y hy => (h.zGroup_normal h9 hV).conj_mem y hy x) hxj hxk hxi

theorem rhoD_range (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L})
    (hD8 : Nat.card (zGroup Ω) = 8) {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) :
    (h.rhoD h9 hV he).range = ⊤ := by
  rw [eq_top_iff, ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (ι := Fin 3) (K := ZMod 2), Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rcases TL4.zmod_two_cases c with rfl | rfl
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact (h.rhoD h9 hV he).range.one_mem
  · rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
    exact h.transvection_mem_range h9 hV hD8 he hij


theorem index_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) :
    (zGroup Ω).index = 168 := by
  have hD8 := h.zGroup_card h9 hV hW hS3
  have hC := h.centralizer_zGroup h9 hV hW hS3
  have hpD := h.pCore_eq_zGroup h9 hV hW hS3
  have hCD : Subgroup.centralizer (zGroup Ω : Set G) ≤ zGroup Ω := by
    rw [hC, hpD]
  have hsq : ∀ x ∈ zGroup Ω, x * x = 1 := fun x hx => by
    rcases (h.mem_zGroup_iff h9 hV).mp hx with rfl | ⟨M, hM, hu⟩
    · simp
    · exact hu.sq
  obtain ⟨e, he⟩ := TL4.exists_e8Basis hsq hD8
  rw [← h.rhoD_ker h9 hV hCD he, Subgroup.index_ker, h.rhoD_range h9 hV hD8 he,
    Subgroup.card_top, TL4.card_sl3Two]

theorem e8Struct_zGroup (h9 : Perp9 Ω) (hV : ∀ L ∈ Ω, twinSet Ω L = {L}) {W : Subgroup G}
    (hW : W ∈ WSet Ω) (hS3 : MuIsoS3 Ω W) :
    E8Struct ⊤ (zGroup Ω) := by
  have hD8 := h.zGroup_card h9 hV hW hS3
  have hC := h.centralizer_zGroup h9 hV hW hS3
  have hpD := h.pCore_eq_zGroup h9 hV hW hS3
  refine ⟨le_top, fun x _ e he => (h.zGroup_normal h9 hV).conj_mem e he x, hD8, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases (h.mem_zGroup_iff h9 hV).mp he with rfl | ⟨M, hM, hu⟩
    · simp
    · exact hu.sq
  · intro x _ hx
    have hxC : x ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun d hd => (hx d hd).symm
    rw [hC, hpD] at hxC
    exact hxC
  · intro Q' _ hQ' hP
    have hN : Q'.Normal := ⟨fun n hn g => hQ' g (Subgroup.mem_top g) n hn⟩
    have hle : Q' ≤ pCore 2 G := le_sSup ⟨hN, hP⟩
    rw [hpD] at hle
    exact hle
  · rw [Subgroup.relIndex_top_right]
    exact h.index_zGroup h9 hV hW hS3

theorem false_of_muIsoS3 (h9 : Perp9 Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hS3 : MuIsoS3 Ω W) : False := by
  have hDW := three_le_ncard_DSet h.thmD.hyp hW hS3
  obtain ⟨K, hK⟩ : (DSet Ω W).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have hKΩ : K ∈ Ω := ((h.mem_dSet_iff).mp hK).1
  have hV1 : twinSet Ω K = {K} := h.twinSet_eq_of_muIsoS3 h9 hW hS3 hK
  have hV : ∀ L ∈ Ω, twinSet Ω L = {L} := fun L hL => h.twinSet_eq_of_twinSet_eq hKΩ hV1 hL
  exact h.no_e8 (zGroup Ω) (h.e8Struct_zGroup h9 hV hW hS3)

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
