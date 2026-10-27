module

public import CFSG.ClassicalInvolution.Asc77.AscT7QGen
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.Asc77.T7Q

open CFSG.ClassicalInvolution.Asc77.T7C2 CFSG.ClassicalInvolution.Asc77.T7DR

section Arith

theorem exists_inv_of_odd (n : ℕ) {κ : ℤ} (hκ : Odd κ) :
    ∃ κ' q : ℤ, κ * κ' = 1 + q * 2 ^ (n + 1) := by
  obtain ⟨c, rfl⟩ := hκ
  have h2 : IsCoprime (2 * c + 1) (2 : ℤ) := ⟨1, -c, by ring⟩
  obtain ⟨u, v, huv⟩ := h2.pow_right (n := n + 1)
  exact ⟨u, -v, by linarith⟩

variable {Q : Type*} [Group Q]

theorem zpow_zpow_eq_self {y : Q} {n : ℕ} (hy : y ^ (2 ^ (n + 1)) = 1) {κ κ' q : ℤ}
    (h : κ * κ' = 1 + q * 2 ^ (n + 1)) : (y ^ κ) ^ κ' = y := by
  rw [← zpow_mul, h, zpow_add, zpow_one]
  have : y ^ (q * 2 ^ (n + 1)) = 1 := by
    rw [mul_comm, zpow_mul]
    have e : y ^ ((2 : ℤ) ^ (n + 1)) = 1 := by
      rw [← hy]
      norm_cast
    rw [e, one_zpow]
  rw [this, mul_one]

theorem inv_conj_of_odd {y s : Q} {n : ℕ} (hy : y ^ (2 ^ (n + 1)) = 1) {i : ℤ} (hi : Odd i)
    (hs : s * y * s⁻¹ = y ^ i) : ∃ i' : ℤ, s⁻¹ * y * s = y ^ i' := by
  obtain ⟨i', q, h⟩ := exists_inv_of_odd n hi
  refine ⟨i', ?_⟩
  have h1 : s * y ^ i' * s⁻¹ = y := by
    calc s * y ^ i' * s⁻¹ = (s * y * s⁻¹) ^ i' := by rw [conj_zpow]
      _ = (y ^ i) ^ i' := by rw [hs]
      _ = y := zpow_zpow_eq_self hy h
  calc s⁻¹ * y * s = s⁻¹ * (s * y ^ i' * s⁻¹) * s := by rw [h1]
    _ = y ^ i' := by group

end Arith

section Core

variable {Q : Type*} [Group Q] [Finite Q]

theorem genLE_four_of_conj {a b s t x : Q} (hgen : Subgroup.closure ({a, b, s, t} : Set Q) = ⊤)
    (hxa : x * a * x⁻¹ ∈ Subgroup.zpowers a) (hxa' : x⁻¹ * a * x ∈ Subgroup.zpowers a)
    (hconj : ∀ g ∈ ({a, b, s, t} : Set Q), g * a * g⁻¹ ∈ Subgroup.closure ({a, x} : Set Q) ∧
      g * x * g⁻¹ ∈ Subgroup.closure ({a, x} : Set Q))
    (hbb : b * b ∈ Subgroup.closure ({a, x} : Set Q))
    (htt : t * t ∈ Subgroup.closure ({a, x} : Set Q))
    (hs : s ∈ Subgroup.closure ((Subgroup.closure ({a, x} : Set Q) : Set Q) ∪ {b, t})) :
    ∀ B : Subgroup Q, GenLE B 4 := by
  set W : Subgroup Q := Subgroup.closure ({a, x} : Set Q) with hWdef
  have haW : a ∈ W := Subgroup.subset_closure (by simp)
  have hxW : x ∈ W := Subgroup.subset_closure (by simp)
  have hWn : W.Normal :=
    normal_of_conj_gens hgen (fun g hg w hw =>
      conj_mem_closure_pair (hconj g hg).1 (hconj g hg).2 w hw)
  intro B
  refine genLE_four_of_ext (W := W) (fun B' hB' =>
    genLE_two_of_sub_normalizes haW hxW rfl hxa hxa' hB') hbb htt ?_ B
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact Subgroup.subset_closure (Or.inl haW)
  rcases hg with rfl | hg
  · exact Subgroup.subset_closure (Or.inr (by simp))
  rcases hg with rfl | hg
  · exact hs
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact Subgroup.subset_closure (Or.inr (by simp))

end Core

section Shape

variable {Q : Type*} [Group Q] [Finite Q]

theorem genLE_four_of_shape {n : ℕ} {a b s t a' b' : Q}
    (hgen : Subgroup.closure ({a, b, s, t} : Set Q) = ⊤)
    (hbab : b * a * b⁻¹ = a⁻¹) (hbb : b * b = a ^ (2 ^ n)) (ha : a ^ (2 ^ (n + 1)) = 1)
    (ht2 : t * t = 1) (htz : t * a ^ (2 ^ n) * t⁻¹ = a ^ (2 ^ n))
    (ha' : t * a * t⁻¹ = a') (hb' : t * b * t⁻¹ = b')
    (hc1 : a * a' = a' * a) (hc2 : a * b' = b' * a) (hc3 : b * a' = a' * b)
    (hc4 : b * b' = b' * b)
    {i m k δ : ℤ} (hi : Odd i) (hm : Odd m) (hsa : s * a * s⁻¹ = a ^ i)
    (hsb : s * b * s⁻¹ = b * a ^ m) (hst : s * t = t * s)
    (hs2 : s * s = a ^ k * a' ^ k * a ^ ((2 ^ n : ℤ) * δ)) :
    ∀ B : Subgroup Q, GenLE B 4 := by
  have hti : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
  have hta : t * a' * t⁻¹ = a := by
    rw [← ha']
    calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t⁻¹ * t⁻¹) := by group
      _ = a := by rw [ht2, hti]; group
  have htb : t * b' * t⁻¹ = b := by
    rw [← hb']
    calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) := by group
      _ = b := by rw [ht2, hti]; group
  have ha'N : a' ^ (2 ^ (n + 1)) = 1 := by
    rw [← ha', conj_pow, ha]; group
  have ha'z : a' ^ (2 ^ n) = a ^ (2 ^ n) := by
    rw [← ha', conj_pow]; exact htz
  have hb'a' : b' * a' * b'⁻¹ = a'⁻¹ := by
    rw [← ha', ← hb']
    calc t * b * t⁻¹ * (t * a * t⁻¹) * (t * b * t⁻¹)⁻¹ = t * (b * a * b⁻¹) * t⁻¹ := by group
      _ = t * a⁻¹ * t⁻¹ := by rw [hbab]
      _ = (t * a * t⁻¹)⁻¹ := by group
  have hb'b' : b' * b' = a' ^ (2 ^ n) := by
    rw [ha'z, ← hb']
    calc t * b * t⁻¹ * (t * b * t⁻¹) = t * (b * b) * t⁻¹ := by group
      _ = t * a ^ (2 ^ n) * t⁻¹ := by rw [hbb]
      _ = a ^ (2 ^ n) := htz
  have hts : t⁻¹ * s⁻¹ = s⁻¹ * t⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hst]
  have hsa' : s * a' * s⁻¹ = a' ^ i := by
    rw [← ha']
    calc s * (t * a * t⁻¹) * s⁻¹ = (s * t) * a * (t⁻¹ * s⁻¹) := by group
      _ = (t * s) * a * (s⁻¹ * t⁻¹) := by rw [hst, hts]
      _ = t * (s * a * s⁻¹) * t⁻¹ := by group
      _ = t * a ^ i * t⁻¹ := by rw [hsa]
      _ = (t * a * t⁻¹) ^ i := by rw [conj_zpow]
  have hsb' : s * b' * s⁻¹ = b' * a' ^ m := by
    rw [← hb', ← ha']
    calc s * (t * b * t⁻¹) * s⁻¹ = (s * t) * b * (t⁻¹ * s⁻¹) := by group
      _ = (t * s) * b * (s⁻¹ * t⁻¹) := by rw [hst, hts]
      _ = t * (s * b * s⁻¹) * t⁻¹ := by group
      _ = t * (b * a ^ m) * t⁻¹ := by rw [hsb]
      _ = (t * b * t⁻¹) * (t * a ^ m * t⁻¹) := by group
      _ = (t * b * t⁻¹) * (t * a * t⁻¹) ^ m := by rw [conj_zpow]
  have hsbm : s * b = b * a ^ m * s := by
    calc s * b = (s * b * s⁻¹) * s := by group
      _ = b * a ^ m * s := by rw [hsb]
  have hsbm' : s * b' = b' * a' ^ m * s := by
    calc s * b' = (s * b' * s⁻¹) * s := by group
      _ = b' * a' ^ m * s := by rw [hsb']
  have hts' : t * s * t⁻¹ = s := by
    calc t * s * t⁻¹ = s * t * t⁻¹ := by rw [hst]
      _ = s := by group
  have cA : ∀ j l : ℤ, a' ^ j * a ^ l = a ^ l * a' ^ j := fun j l =>
    ((Commute.zpow_zpow (show Commute a' a from hc1.symm) j l).eq)
  have cb'a : ∀ j : ℤ, b' * a ^ j = a ^ j * b' := fun j =>
    ((Commute.zpow_left (show Commute a b' from hc2) j).eq).symm
  have cbb' : b' * b = b * b' := hc4.symm
  obtain ⟨i', hi'⟩ := inv_conj_of_odd ha hi hsa
  obtain ⟨i'', hi''⟩ := inv_conj_of_odd ha'N hi hsa'
  have hxa_s : s⁻¹ * a * s ∈ Subgroup.zpowers a := ⟨i', hi'.symm⟩
  have hbab' : b⁻¹ * a * b = a⁻¹ := by
    have h2 : b * a⁻¹ * b⁻¹ = a := by
      calc b * a⁻¹ * b⁻¹ = (b * a * b⁻¹)⁻¹ := by group
        _ = (a⁻¹)⁻¹ := by rw [hbab]
        _ = a := inv_inv a
    calc b⁻¹ * a * b = b⁻¹ * (b * a⁻¹ * b⁻¹) * b := by rw [h2]
      _ = a⁻¹ := by group
  have hbs : b * s * b⁻¹ = a ^ m * s := by
    calc b * s * b⁻¹ = b * (s * b * s⁻¹)⁻¹ * s := by group
      _ = b * (b * a ^ m)⁻¹ * s := by rw [hsb]
      _ = (b * a ^ (-m) * b⁻¹) * s := by rw [mul_inv_rev, zpow_neg]; group
      _ = (b * a * b⁻¹) ^ (-m) * s := by rw [conj_zpow]
      _ = a ^ m * s := by rw [hbab, inv_zpow, zpow_neg, inv_inv]
  have hsinv : ∀ (y : Q) (j : ℤ), s⁻¹ * y ^ j * s = (s⁻¹ * y * s) ^ j := fun y j => by
    simpa using (conj_zpow (a := s⁻¹) (b := y) (i := j)).symm
  have hbmem : ∀ j : ℤ, b * a ^ j * b⁻¹ = a ^ (-j) := fun j => by
    rw [← conj_zpow, hbab, inv_zpow, zpow_neg]
  rcases Int.even_or_odd k with hke | hko
  ·
    have hmk : Odd (m + k) := hm.add_even hke
    obtain ⟨e, he⟩ : ∃ e : Q, e = b * b' * s := ⟨_, rfl⟩
    have hb'ainv : b'⁻¹ * a⁻¹ * b' = a⁻¹ := by
      have h1 : b'⁻¹ * a * b' = a := by
        calc b'⁻¹ * a * b' = b'⁻¹ * (a * b') := by group
          _ = b'⁻¹ * (b' * a) := by rw [hc2]
          _ = a := by group
      calc b'⁻¹ * a⁻¹ * b' = (b'⁻¹ * a * b')⁻¹ := by group
        _ = a⁻¹ := by rw [h1]
    have hb'ai : ∀ j : ℤ, b' * a ^ j * b'⁻¹ = a ^ j := fun j => by
      rw [cb'a j]; group
    have hxa_eq : e * a * e⁻¹ = a ^ (-i) := by
      calc e * a * e⁻¹ = b * (b' * (s * a * s⁻¹) * b'⁻¹) * b⁻¹ := by rw [he]; group
        _ = b * (b' * a ^ i * b'⁻¹) * b⁻¹ := by rw [hsa]
        _ = b * a ^ i * b⁻¹ := by rw [hb'ai]
        _ = a ^ (-i) := hbmem i
    have hxa'_eq : e⁻¹ * a * e = a ^ (-i') := by
      calc e⁻¹ * a * e = s⁻¹ * (b'⁻¹ * (b⁻¹ * a * b) * b') * s := by rw [he]; group
        _ = s⁻¹ * (b'⁻¹ * a⁻¹ * b') * s := by rw [hbab']
        _ = s⁻¹ * a⁻¹ * s := by rw [hb'ainv]
        _ = (s⁻¹ * a * s)⁻¹ := by group
        _ = a ^ (-i') := by rw [hi', zpow_neg]
    have hxa : e * a * e⁻¹ ∈ Subgroup.zpowers a := ⟨-i, hxa_eq.symm⟩
    have hxa' : e⁻¹ * a * e ∈ Subgroup.zpowers a := ⟨-i', hxa'_eq.symm⟩
    have hP : b * b' * b * a ^ m * b' * a' ^ m = a ^ m * a' ^ m := by
      calc b * b' * b * a ^ m * b' * a' ^ m
          = b * (b' * b) * a ^ m * b' * a' ^ m := by group
        _ = b * (b * b') * a ^ m * b' * a' ^ m := by rw [cbb']
        _ = b * b * (b' * a ^ m) * b' * a' ^ m := by group
        _ = b * b * (a ^ m * b') * b' * a' ^ m := by rw [cb'a m]
        _ = (b * b) * a ^ m * (b' * b') * a' ^ m := by group
        _ = a ^ (2 ^ n) * a ^ m * a' ^ (2 ^ n) * a' ^ m := by rw [hbb, hb'b']
        _ = a ^ (2 ^ n) * a ^ m * a ^ (2 ^ n) * a' ^ m := by rw [ha'z]
        _ = a ^ m * (a ^ (2 ^ n) * a ^ (2 ^ n)) * a' ^ m := by group
        _ = a ^ m * a ^ (2 ^ (n + 1)) * a' ^ m := by rw [← pow_add, ← two_mul, ← pow_succ']
        _ = a ^ m * a' ^ m := by rw [ha]; group
    have hee : e * e = a ^ m * a' ^ m * (s * s) := by
      rw [← hP]
      calc e * e = b * b' * (s * b) * b' * s := by rw [he]; group
        _ = b * b' * (b * a ^ m * s) * b' * s := by rw [hsbm]
        _ = b * b' * b * a ^ m * (s * b') * s := by group
        _ = b * b' * b * a ^ m * (b' * a' ^ m * s) * s := by rw [hsbm']
        _ = b * b' * b * a ^ m * b' * a' ^ m * (s * s) := by group
    set W : Subgroup Q := Subgroup.closure ({a, e} : Set Q) with hW
    have haW1 : a ∈ W := Subgroup.subset_closure (by simp)
    have haW : ∀ j : ℤ, a ^ j ∈ W := fun j => zpow_mem haW1 j
    have heW : e ∈ W := Subgroup.subset_closure (by simp)
    have ha'W : a' ∈ W := by
      obtain ⟨κ', q, hκ⟩ := exists_inv_of_odd n hmk
      have h1 : a' ^ (m + k) ∈ W := by
        have : a' ^ (m + k) = a ^ (-(m + k)) * (e * e) * a ^ (-((2 ^ n : ℤ) * δ)) := by
          rw [hee, hs2]
          symm
          calc a ^ (-(m + k)) * (a ^ m * a' ^ m * (a ^ k * a' ^ k * a ^ ((2 ^ n : ℤ) * δ))) *
                a ^ (-((2 ^ n : ℤ) * δ))
              = a ^ (-(m + k)) * a ^ m * (a' ^ m * a ^ k) * a' ^ k := by group
            _ = a ^ (-(m + k)) * a ^ m * (a ^ k * a' ^ m) * a' ^ k := by rw [cA m k]
            _ = a' ^ (m + k) := by group
        rw [this]
        exact W.mul_mem (W.mul_mem (haW _) (W.mul_mem heW heW)) (haW _)
      have h2 : (a' ^ (m + k)) ^ κ' = a' := zpow_zpow_eq_self ha'N hκ
      rw [← h2]
      exact zpow_mem h1 κ'
    have ha'pW : ∀ j : ℤ, a' ^ j ∈ W := fun j => zpow_mem ha'W j
    refine genLE_four_of_conj hgen hxa hxa' ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · refine ⟨by simpa using haW1, ?_⟩
        have e1 : e * g⁻¹ = g ^ i * e := by
          calc e * g⁻¹ = (e * g * e⁻¹)⁻¹ * e := by group
            _ = g ^ i * e := by rw [hxa_eq, ← zpow_neg, neg_neg]
        have : g * e * g⁻¹ = g ^ (1 + i) * e := by
          calc g * e * g⁻¹ = g * (e * g⁻¹) := by group
            _ = g * (g ^ i * e) := by rw [e1]
            _ = g ^ (1 + i) * e := by group
        rw [this]
        exact W.mul_mem (haW _) heW
      · refine ⟨?_, ?_⟩
        · rw [hbab]; exact W.inv_mem haW1
        · have hsbinv : s * g⁻¹ = a ^ (-m) * g⁻¹ * s := by
            calc s * g⁻¹ = (s * g * s⁻¹)⁻¹ * s := by group
              _ = (g * a ^ m)⁻¹ * s := by rw [hsb]
              _ = a ^ (-m) * g⁻¹ * s := by rw [mul_inv_rev, zpow_neg]
          have hbbb' : g * g * b' = b' * g * g := by
            calc g * g * b' = g * (g * b') := by group
              _ = g * (b' * g) := by rw [hc4]
              _ = (g * b') * g := by group
              _ = (b' * g) * g := by rw [hc4]
          have h1 : g * e * g⁻¹ = g * b' * a ^ m * s := by
            calc g * e * g⁻¹ = g * g * b' * (s * g⁻¹) := by rw [he]; group
              _ = g * g * b' * (a ^ (-m) * g⁻¹ * s) := by rw [hsbinv]
              _ = (g * g * b') * a ^ (-m) * g⁻¹ * s := by group
              _ = (b' * g * g) * a ^ (-m) * g⁻¹ * s := by rw [hbbb']
              _ = b' * g * (g * a ^ (-m) * g⁻¹) * s := by group
              _ = b' * g * a ^ m * s := by rw [hbmem, neg_neg]
              _ = g * b' * a ^ m * s := by rw [cbb']
          have h2 : g * b' * a ^ m * s = e * (s⁻¹ * a ^ m * s) := by
            rw [he]; group
          rw [h1, h2, hsinv, hi']
          exact W.mul_mem heW (by rw [← zpow_mul]; exact haW _)
      · refine ⟨?_, ?_⟩
        · rw [hsa]; exact haW _
        · have h1 : g * e * g⁻¹ = (g * b * g⁻¹) * (g * b' * g⁻¹) * g := by rw [he]; group
          have h2 : (b * a ^ m) * (b' * a' ^ m) * g = b * b' * (a ^ m * a' ^ m) * g := by
            calc (b * a ^ m) * (b' * a' ^ m) * g = b * (a ^ m * b') * a' ^ m * g := by group
              _ = b * (b' * a ^ m) * a' ^ m * g := by rw [cb'a m]
              _ = b * b' * (a ^ m * a' ^ m) * g := by group
          have h3 : b * b' * (a ^ m * a' ^ m) * g
              = e * ((g⁻¹ * a ^ m * g) * (g⁻¹ * a' ^ m * g)) := by
            rw [he]; group
          rw [h1, hsb, hsb', h2, h3, hsinv, hsinv, hi', hi'']
          refine W.mul_mem heW (W.mul_mem ?_ ?_)
          · rw [← zpow_mul]; exact haW _
          · rw [← zpow_mul]; exact ha'pW _
      · refine ⟨?_, ?_⟩
        · rw [ha']; exact ha'W
        · have : g * e * g⁻¹ = e := by
            calc g * e * g⁻¹ = (g * b * g⁻¹) * (g * b' * g⁻¹) * (g * s * g⁻¹) := by
                  rw [he]; group
              _ = b' * b * s := by rw [hb', htb, hts']
              _ = e := by rw [cbb', he]
          rw [this]; exact heW
    · have : b * b = a ^ (2 ^ n) := hbb
      rw [this]; exact pow_mem haW1 _
    · rw [ht2]; exact W.one_mem
    · have hbm : b ∈ Subgroup.closure ((W : Set Q) ∪ {b, t}) :=
        Subgroup.subset_closure (Or.inr (by simp))
      have htm : t ∈ Subgroup.closure ((W : Set Q) ∪ {b, t}) :=
        Subgroup.subset_closure (Or.inr (by simp))
      have hb'm : b' ∈ Subgroup.closure ((W : Set Q) ∪ {b, t}) := by
        rw [← hb']
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htm hbm) (Subgroup.inv_mem _ htm)
      have hem : e ∈ Subgroup.closure ((W : Set Q) ∪ {b, t}) :=
        Subgroup.subset_closure (Or.inl heW)
      have : s = (b * b')⁻¹ * e := by rw [he]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hbm hb'm)) hem
  ·
    have hxa : s * a * s⁻¹ ∈ Subgroup.zpowers a := ⟨i, hsa.symm⟩
    set W : Subgroup Q := Subgroup.closure ({a, s} : Set Q) with hW
    have haW1 : a ∈ W := Subgroup.subset_closure (by simp)
    have haW : ∀ j : ℤ, a ^ j ∈ W := fun j => zpow_mem haW1 j
    have hsW : s ∈ W := Subgroup.subset_closure (by simp)
    have ha'W : a' ∈ W := by
      obtain ⟨κ', q, hκ⟩ := exists_inv_of_odd n hko
      have h1 : a' ^ k ∈ W := by
        have : a' ^ k = a ^ (-k) * (s * s) * a ^ (-((2 ^ n : ℤ) * δ)) := by
          rw [hs2]; group
        rw [this]
        exact W.mul_mem (W.mul_mem (haW _) (W.mul_mem hsW hsW)) (haW _)
      have h2 : (a' ^ k) ^ κ' = a' := zpow_zpow_eq_self ha'N hκ
      rw [← h2]
      exact zpow_mem h1 κ'
    refine genLE_four_of_conj hgen hxa hxa_s ?_ ?_ ?_ ?_
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · refine ⟨by simpa using haW1, ?_⟩
        have e1 : s * g⁻¹ = g ^ (-i) * s := by
          calc s * g⁻¹ = (s * g * s⁻¹)⁻¹ * s := by group
            _ = g ^ (-i) * s := by rw [hsa, zpow_neg]
        have : g * s * g⁻¹ = g ^ (1 - i) * s := by
          calc g * s * g⁻¹ = g * (s * g⁻¹) := by group
            _ = g * (g ^ (-i) * s) := by rw [e1]
            _ = g ^ (1 - i) * s := by group
        rw [this]
        exact W.mul_mem (haW _) hsW
      · refine ⟨?_, ?_⟩
        · rw [hbab]; exact W.inv_mem haW1
        · rw [hbs]; exact W.mul_mem (haW _) hsW
      · refine ⟨?_, ?_⟩
        · rw [hsa]; exact haW _
        · have : g * g * g⁻¹ = g := by group
          rw [this]; exact hsW
      · refine ⟨?_, ?_⟩
        · rw [ha']; exact ha'W
        · rw [hts']; exact hsW
    · have : b * b = a ^ (2 ^ n) := hbb
      rw [this]; exact pow_mem haW1 _
    · rw [ht2]; exact W.one_mem
    · exact Subgroup.subset_closure (Or.inl hsW)

theorem closure_eq_top_of_image {G : Type*} [Group G] {T : Subgroup G} {s : Set ↥T}
    (h : Subgroup.closure (T.subtype '' s) = T) : Subgroup.closure s = ⊤ := by
  apply Subgroup.map_injective T.subtype_injective
  rw [MonoidHom.map_closure, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem genLE_four_of_shape_sub {G : Type*} [Group G] [Finite G] {T : Subgroup G} {n : ℕ}
    {a b s t a' b' : G} (hT : Subgroup.closure ({a, b, s, t} : Set G) = T)
    (hbab : b * a * b⁻¹ = a⁻¹) (hbb : b * b = a ^ (2 ^ n)) (ha : a ^ (2 ^ (n + 1)) = 1)
    (ht2 : t * t = 1) (htz : t * a ^ (2 ^ n) * t⁻¹ = a ^ (2 ^ n))
    (ha' : t * a * t⁻¹ = a') (hb' : t * b * t⁻¹ = b')
    (hc1 : a * a' = a' * a) (hc2 : a * b' = b' * a) (hc3 : b * a' = a' * b)
    (hc4 : b * b' = b' * b)
    {i m k δ : ℤ} (hi : Odd i) (hm : Odd m) (hsa : s * a * s⁻¹ = a ^ i)
    (hsb : s * b * s⁻¹ = b * a ^ m) (hst : s * t = t * s)
    (hs2 : s * s = a ^ k * a' ^ k * a ^ ((2 ^ n : ℤ) * δ)) {B : Subgroup G} (hB : B ≤ T) :
    GenLE B 4 := by
  have hmem : ∀ x ∈ ({a, b, s, t} : Set G), x ∈ T := fun x hx => hT ▸ Subgroup.subset_closure hx
  have haT : a ∈ T := hmem a (by simp)
  have hbT : b ∈ T := hmem b (by simp)
  have hsT : s ∈ T := hmem s (by simp)
  have htT : t ∈ T := hmem t (by simp)
  have ha'T : a' ∈ T := ha' ▸ T.mul_mem (T.mul_mem htT haT) (T.inv_mem htT)
  have hb'T : b' ∈ T := hb' ▸ T.mul_mem (T.mul_mem htT hbT) (T.inv_mem htT)
  have hgen : Subgroup.closure ({(⟨a, haT⟩ : ↥T), ⟨b, hbT⟩, ⟨s, hsT⟩, ⟨t, htT⟩} : Set ↥T) = ⊤ := by
    apply closure_eq_top_of_image
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    exact hT
  have key := genLE_four_of_shape (Q := ↥T) (n := n) (a := ⟨a, haT⟩) (b := ⟨b, hbT⟩)
    (s := ⟨s, hsT⟩) (t := ⟨t, htT⟩) (a' := ⟨a', ha'T⟩) (b' := ⟨b', hb'T⟩) hgen
    (Subtype.ext (by simpa using hbab)) (Subtype.ext (by simpa using hbb))
    (Subtype.ext (by simpa using ha)) (Subtype.ext (by simpa using ht2))
    (Subtype.ext (by simpa using htz)) (Subtype.ext (by simpa using ha'))
    (Subtype.ext (by simpa using hb')) (Subtype.ext (by simpa using hc1))
    (Subtype.ext (by simpa using hc2)) (Subtype.ext (by simpa using hc3))
    (Subtype.ext (by simpa using hc4)) hi hm (Subtype.ext (by simpa using hsa))
    (Subtype.ext (by simpa using hsb)) (Subtype.ext (by simpa using hst))
    (Subtype.ext (by simpa using hs2)) (B.subgroupOf T)
  exact GenLE.of_subgroupOf hB key

end Shape

end CFSG.ClassicalInvolution.Asc77.T7Q
