module

public import CFSG.GroupTheory.CyclicDiagonal
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

private theorem nat_coprime_add_mul {p m : ℕ} (h : p.Coprime m) :
    Nat.Coprime (p + m) (p * m) :=
  Nat.Coprime.mul_right (Nat.coprime_self_add_left.mpr h.symm)
    (Nat.coprime_add_self_left.mpr h)

theorem mem_of_forall_prime_orderOf_pow_mem {H : Subgroup G} {b : G}
    (hb : Squarefree (orderOf b))
    (h : ∀ k : ℕ, (orderOf (b ^ k)).Prime → b ^ k ∈ H) : b ∈ H := by
  classical
  suffices hv : ∀ n : ℕ, Squarefree n → ∀ b : G, orderOf b = n →
      (∀ k : ℕ, (orderOf (b ^ k)).Prime → b ^ k ∈ H) → b ∈ H by
    exact hv (orderOf b) hb b rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hsq b hbord hprime
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · exact absurd hsq not_squarefree_zero
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hnpos.ne') with rfl | hn1
    · have hb1 : b = 1 := orderOf_eq_one_iff.mp hbord
      rw [hb1]
      exact H.one_mem
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
    set m := n / p with hm
    have hnm : n = p * m := (Nat.mul_div_cancel' hpdvd).symm
    have hmlt : m < n := Nat.div_lt_self hnpos hp.one_lt
    have hmsq : Squarefree m :=
      Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpdvd) (hbord ▸ hsq)
    have hpdvdb : p ∣ orderOf b := hbord ▸ hpdvd
    have hsqb : Squarefree (orderOf b) := hbord ▸ hsq
    have hc_ord : orderOf (b ^ p) = m := by
      rw [orderOf_pow_of_dvd hp.ne_zero hpdvdb, hbord, hm]
    have hc_mem : b ^ p ∈ H := by
      refine ih m hmlt hmsq (b ^ p) hc_ord ?_
      intro k hk
      rw [← pow_mul] at hk ⊢
      exact hprime (p * k) hk
    have hd_ord : orderOf (b ^ m) = p := by
      have h := orderOf_pow_orderOf_div (x := b) hsqb.ne_zero (n := p) hpdvdb
      rwa [hbord, hnm, Nat.mul_div_cancel_left m hp.pos] at h
    have hd_mem : b ^ m ∈ H := hprime m (hd_ord ▸ hp)
    have hcop : Nat.Coprime m p :=
      (Nat.coprime_of_squarefree_mul (m := p) (n := m) (hnm ▸ hsq)).symm
    have hpm : Nat.Coprime (p + m) (orderOf b) := by
      rw [hbord, hnm]
      exact nat_coprime_add_mul hcop.symm
    obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := b) (n := p + m) hpm
    rw [← hk, show b ^ (p + m) = b ^ p * b ^ m by rw [pow_add]]
    exact H.pow_mem (H.mul_mem hc_mem hd_mem) k

theorem conjugatePower_injOn {L : Subgroup G} {a : G}
    (hr : (orderOf a).Prime) (haL : a ∉ Subgroup.normalizer (L : Set G)) :
    Set.InjOn (conjugatePower a L) (Set.Iio (orderOf a)) := by
  intro i hi j hj hij
  rw [Set.mem_Iio] at hi hj
  have main : ∀ i j : ℕ, i < orderOf a → j < orderOf a → i ≤ j →
      conjugatePower a L i = conjugatePower a L j → i = j := by
    intro i j hi hj hle hij
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      have hpos : 0 < j - i := Nat.sub_pos_of_lt hlt
      have hlt' : j - i < orderOf a := by omega
      have hcop : Nat.Coprime (j - i) (orderOf a) := by
        refine ((hr.coprime_iff_not_dvd).2 ?_).symm
        intro hd
        exact (Nat.not_le_of_lt hlt') (Nat.le_of_dvd hpos hd)
      have hsub : conjugatePower a L j =
          (conjugatePower a L (j - i)).map (MulAut.conj (a ^ i)).toMonoidHom := by
        have h := conjugatePower_add a L i (j - i)
        rwa [Nat.add_sub_cancel' hle] at h
      have hmap : conjugatePower a L i =
          (conjugatePower a L (j - i)).map (MulAut.conj (a ^ i)).toMonoidHom := by
        rw [hij, hsub]
      have hLmap : L.map (MulAut.conj (a ^ (j - i))).toMonoidHom = L := by
        have hinj : Function.Injective
            (Subgroup.map (MulAut.conj (a ^ i)).toMonoidHom) :=
          Subgroup.map_injective (MulAut.conj (a ^ i)).injective
        have := hinj (by simpa [conjugatePower] using hmap)
        simpa [conjugatePower] using this.symm
      have hN : a ^ (j - i) ∈ Subgroup.normalizer (L : Set G) :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).2 hLmap
      obtain ⟨k, hk⟩ := exists_pow_eq_self_of_coprime (x := a) (n := j - i) hcop
      have ha_mem : a ∈ Subgroup.zpowers (a ^ (j - i)) :=
        Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by simpa using hk⟩
      exact haL (Subgroup.zpowers_le.mpr hN ha_mem)
    · exact heq
  rcases le_total i j with hle | hle
  · exact main i j hi hj hle hij
  · exact (main j i hj hi hle hij.symm).symm

end CFSG.GroupTheory

end
