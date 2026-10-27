module

public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P310

open Subgroup

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {P D : Subgroup G} (h : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p) {u : G}
    (hu : u ∈ P ⊔ D) : ∃ p ∈ P, ∃ d ∈ D, u = p * d := by
  let S : Subgroup G :=
    { carrier := {u | ∃ p ∈ P, ∃ d ∈ D, u = p * d}
      one_mem' := ⟨1, P.one_mem, 1, D.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨p₁, hp₁, d₁, hd₁, rfl⟩ ⟨p₂, hp₂, d₂, hd₂, rfl⟩
        refine ⟨p₁ * p₂, P.mul_mem hp₁ hp₂, d₁ * d₂, D.mul_mem hd₁ hd₂, ?_⟩
        calc p₁ * d₁ * (p₂ * d₂) = p₁ * (d₁ * p₂) * d₂ := by group
          _ = p₁ * (p₂ * d₁) * d₂ := by rw [← h p₂ hp₂ d₁ hd₁]
          _ = p₁ * p₂ * (d₁ * d₂) := by group
      inv_mem' := by
        rintro _ ⟨p, hp, d, hd, rfl⟩
        refine ⟨p⁻¹, P.inv_mem hp, d⁻¹, D.inv_mem hd, ?_⟩
        calc (p * d)⁻¹ = d⁻¹ * p⁻¹ := by group
          _ = p⁻¹ * d⁻¹ := (h p⁻¹ (P.inv_mem hp) d⁻¹ (D.inv_mem hd)).symm }
  have hle : P ⊔ D ≤ S :=
    sup_le (fun p hp => ⟨p, hp, 1, D.one_mem, by simp⟩) (fun d hd => ⟨1, P.one_mem, d, hd, by simp⟩)
  exact hle hu

theorem conj_mul_exp {a v w : G} {j k : ℤ} (hv : v * a * v⁻¹ = a ^ j) (hw : w * a * w⁻¹ = a ^ k) :
    (v * w) * a * (v * w)⁻¹ = a ^ (j * k) := by
  calc (v * w) * a * (v * w)⁻¹ = v * (w * a * w⁻¹) * v⁻¹ := by group
    _ = v * a ^ k * v⁻¹ := by rw [hw]
    _ = (v * a * v⁻¹) ^ k := conj_zpow.symm
    _ = (a ^ j) ^ k := by rw [hv]
    _ = a ^ (j * k) := by rw [← zpow_mul]

theorem exp_inv_modEq {a v : G} {j k : ℤ} (hv : v * a * v⁻¹ = a ^ j) (hk : v⁻¹ * a * v = a ^ k) :
    1 ≡ k * j [ZMOD (orderOf a)] := by
  have h1 : a ^ (1 : ℤ) = a ^ (k * j) := by
    calc a ^ (1 : ℤ) = a := zpow_one a
      _ = v⁻¹ * (v * a * v⁻¹) * v := by group
      _ = v⁻¹ * a ^ j * v := by rw [hv]
      _ = (v⁻¹ * a * v⁻¹⁻¹) ^ j := by rw [conj_zpow, inv_inv]
      _ = (a ^ k) ^ j := by rw [inv_inv, hk]
      _ = a ^ (k * j) := by rw [← zpow_mul]
  exact zpow_eq_zpow_iff_modEq.1 h1


theorem exists_V0_of_cyclic_maximal [Finite G]
    {V P D : Subgroup G} {a x f : G}
    (hDV : D ≤ V) (hPV : P ≤ V)
    (hPD : P ⊓ D = ⊥) (hcomm : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p)
    (haD : a ∈ D) (hVa : ∀ v ∈ V, v * a * v⁻¹ ∈ zpowers a)
    (h4 : 4 ∣ orderOf a)
    (hxD : x ∈ D)
    (hDx : ∀ d ∈ D, d ∈ zpowers a ∨ x⁻¹ * d ∈ zpowers a)
    (hfa : f ∈ zpowers a) (hf2 : f * f = 1) (hf1 : f ≠ 1)
    (hCx : ∀ d ∈ D, d * x = x * d → d * d = 1)
    (hinv : ∀ u ∈ V, u * u = 1 → u ∈ P ⊔ D) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ (∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) ∧ x ∉ V₀ ∧
      (∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) ∧ P ⊔ zpowers f ≤ V₀ ∧
      ∀ u ∈ V₀, u * u = 1 → u ∈ P ⊔ zpowers f := by
  classical
  have hnpos : 0 < orderOf a := orderOf_pos a
  have h4z : ((4 : ℕ) : ℤ) ∣ (orderOf a : ℤ) := Int.natCast_dvd_natCast.2 h4
  have h4z' : (4 : ℤ) ∣ (orderOf a : ℤ) := by exact_mod_cast h4z
  have h2z : (2 : ℤ) ∣ (orderOf a : ℤ) := (by norm_num : (2 : ℤ) ∣ 4).trans h4z'
  have hconj : ∀ v ∈ V, ∃ j : ℤ, v * a * v⁻¹ = a ^ j := fun v hv => by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hVa v hv)
    exact ⟨j, hj.symm⟩
  have hmod4 : ∀ {j k : ℤ}, j ≡ k [ZMOD (orderOf a)] → j % 4 = k % 4 := by
    intro j k h
    exact Int.ModEq.of_dvd h4z' h
  have hpair : ∀ {v : G} {j k : ℤ}, v * a * v⁻¹ = a ^ j → v⁻¹ * a * v = a ^ k →
      (k * j) % 4 = 1 ∧ Odd j := by
    intro v j k hv hk
    have h1 := exp_inv_modEq hv hk
    refine ⟨?_, ?_⟩
    · have := hmod4 h1
      simpa using this.symm
    · have h2 : (1 : ℤ) ≡ k * j [ZMOD 2] := Int.ModEq.of_dvd h2z h1
      have h3 : (k * j) % 2 = 1 := by
        have := h2.symm
        unfold Int.ModEq at this
        simpa using this
      rcases Int.emod_two_eq_zero_or_one j with hj | hj
      · exfalso
        have : (k * j) % 2 = 0 := by rw [Int.mul_emod, hj]; simp
        omega
      · exact Int.odd_iff.2 hj
  let V₀ : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∃ j : ℤ, j % 4 = 1 ∧ v * a * v⁻¹ = a ^ j}
      one_mem' := ⟨V.one_mem, 1, by norm_num, by simp⟩
      mul_mem' := by
        rintro v w ⟨hv, j, hj, hvj⟩ ⟨hw, k, hk, hwk⟩
        refine ⟨V.mul_mem hv hw, j * k, ?_, conj_mul_exp hvj hwk⟩
        rw [Int.mul_emod, hj, hk]; norm_num
      inv_mem' := by
        rintro v ⟨hv, j, hj, hvj⟩
        obtain ⟨k, hk⟩ := hconj v⁻¹ (V.inv_mem hv)
        refine ⟨V.inv_mem hv, k, ?_, hk⟩
        rw [inv_inv] at hk
        have h1 := (hpair hvj hk).1
        rw [Int.mul_emod, hj] at h1
        simpa using h1 }
  have hmemV₀ : ∀ {v : G}, v ∈ V₀ ↔ v ∈ V ∧ ∃ j : ℤ, j % 4 = 1 ∧ v * a * v⁻¹ = a ^ j := Iff.rfl
  have haV : a ∈ V := hDV haD
  have hxV : x ∈ V := hDV hxD
  have hxnot : ∀ j : ℤ, x * a * x⁻¹ = a ^ j → j % 4 ≠ 1 := by
    intro j hxj hj
    obtain ⟨m, hm⟩ := h4
    have hm0 : 0 < m := by omega
    obtain ⟨s, hs⟩ : ∃ s : ℤ, j = 1 + 4 * s := ⟨j / 4, by omega⟩
    have ha4m : a ^ (4 * m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one a
    have hxc : a ^ m * x = x * a ^ m := by
      have h1 : x * a ^ m * x⁻¹ = a ^ m := by
        calc x * a ^ m * x⁻¹ = (x * a * x⁻¹) ^ m := (conj_pow).symm
          _ = (a ^ j) ^ m := by rw [hxj]
          _ = a ^ (j * (m : ℤ)) := by rw [← zpow_natCast, ← zpow_mul]
          _ = a ^ ((m : ℤ) + ((4 * m : ℕ) : ℤ) * s) := by
              congr 1; rw [hs]; push_cast; ring
          _ = a ^ m := by
              rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, ha4m, one_zpow, mul_one]
      calc a ^ m * x = (x * a ^ m * x⁻¹) * x := by rw [h1]
        _ = x * a ^ m := by group
    have hsq := hCx (a ^ m) (D.pow_mem haD m) hxc
    have h2m : a ^ (2 * m) = 1 := by rw [two_mul, pow_add]; exact hsq
    exact pow_ne_one_of_lt_orderOf (by omega) (by omega) h2m
  have hxV₀ : x ∉ V₀ := by
    rintro ⟨-, j, hj, hxj⟩
    exact hxnot j hxj hj
  obtain ⟨jx, hjx⟩ := hconj x hxV
  obtain ⟨kx, hkx⟩ := hconj x⁻¹ (V.inv_mem hxV)
  rw [inv_inv] at hkx
  obtain ⟨hkxjx, hjxodd⟩ := hpair hjx hkx
  have hjx3 : jx % 4 = 3 := by
    have h1 := hxnot jx hjx
    have h2 : jx % 2 = 1 := Int.odd_iff.1 hjxodd
    omega
  have hkx3 : kx % 4 = 3 := by
    rw [Int.mul_emod, hjx3] at hkxjx
    omega
  refine ⟨V₀, fun v hv => hv.1, ?_, hxV₀, ⟨x, hxV, ?_⟩, ?_, ?_⟩
  ·
    rintro u hu w ⟨hw, j, hj, hwj⟩
    obtain ⟨ju, hju⟩ := hconj u hu
    obtain ⟨ku, hku⟩ := hconj u⁻¹ (V.inv_mem hu)
    have hku' := hku
    rw [inv_inv] at hku'
    have hmu := (hpair hju hku').1
    refine ⟨V.mul_mem (V.mul_mem hu hw) (V.inv_mem hu), ju * j * ku, ?_,
      conj_mul_exp (conj_mul_exp hju hwj) hku⟩
    have : ju * j * ku = (ku * ju) * j := by ring
    rw [this, Int.mul_emod, hmu, hj]; norm_num
  ·
    intro v hv
    obtain ⟨jv, hjv⟩ := hconj v hv
    obtain ⟨kv, hkv⟩ := hconj v⁻¹ (V.inv_mem hv)
    rw [inv_inv] at hkv
    obtain ⟨hkvjv, hjvodd⟩ := hpair hjv hkv
    have hjv13 : jv % 4 = 1 ∨ jv % 4 = 3 := by
      have h2 : jv % 2 = 1 := Int.odd_iff.1 hjvodd
      omega
    rcases hjv13 with h1 | h3
    · refine ⟨0, ?_⟩
      simp only [zpow_zero, inv_one, one_mul]
      exact ⟨hv, jv, h1, hjv⟩
    · refine ⟨1, ?_⟩
      simp only [zpow_one]
      refine ⟨V.mul_mem (V.inv_mem hxV) hv, kx * jv, ?_, ?_⟩
      · rw [Int.mul_emod, hkx3, h3]; norm_num
      ·
        calc x⁻¹ * v * a * (x⁻¹ * v)⁻¹ = x⁻¹ * (v * a * v⁻¹) * x := by group
          _ = x⁻¹ * a ^ jv * x := by rw [hjv]
          _ = (x⁻¹ * a * x⁻¹⁻¹) ^ jv := by rw [conj_zpow, inv_inv]
          _ = (a ^ kx) ^ jv := by rw [inv_inv, hkx]
          _ = a ^ (kx * jv) := by rw [← zpow_mul]
  ·
    refine sup_le (fun p hp => ?_) ((zpowers_le).2 ?_)
    · refine ⟨hPV hp, 1, by norm_num, ?_⟩
      have := hcomm p hp a haD
      rw [zpow_one]
      calc p * a * p⁻¹ = a * p * p⁻¹ := by rw [this]
        _ = a := by group
    · have hfD : f ∈ V := by
        obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hfa
        rw [← hi]
        exact V.zpow_mem haV i
      refine ⟨hfD, 1, by norm_num, ?_⟩
      obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hfa
      rw [zpow_one, ← hi]
      have hc : a ^ i * a = a * a ^ i := ((Commute.self_zpow a i).eq).symm
      calc a ^ i * a * (a ^ i)⁻¹ = a * a ^ i * (a ^ i)⁻¹ := by rw [hc]
        _ = a := by group
  ·
    rintro u ⟨hu, j, hj, huj⟩ huu
    obtain ⟨p, hp, d, hd, rfl⟩ := exists_mul_of_mem_sup hcomm (hinv u hu huu)
    have hpd := hcomm p hp d hd
    have hpa : p * a = a * p := hcomm p hp a haD
    have hua : (p * d) * a * (p * d)⁻¹ = d * a * d⁻¹ := by
      calc (p * d) * a * (p * d)⁻¹ = p * (d * a * d⁻¹) * p⁻¹ := by group
        _ = d * a * d⁻¹ := by
            have hmem : d * a * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd haD) (D.inv_mem hd)
            have := hcomm p hp _ hmem
            rw [this]; group
    have hdaj : d * a * d⁻¹ = a ^ j := hua.symm.trans huj
    have hdA : d ∈ zpowers a := by
      rcases hDx d hd with h | h
      · exact h
      · exfalso
        obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h
        have hdi : d = x * a ^ i := by rw [hi, mul_inv_cancel_left]
        have hc : a ^ i * a = a * a ^ i := ((Commute.self_zpow a i).eq).symm
        have h1 : d * a * d⁻¹ = a ^ jx := by
          calc d * a * d⁻¹ = x * (a ^ i * a * (a ^ i)⁻¹) * x⁻¹ := by rw [hdi]; group
            _ = x * a * x⁻¹ := by rw [hc]; group
            _ = a ^ jx := hjx
        have h2 : a ^ jx = a ^ j := h1.symm.trans hdaj
        have h3 := hmod4 (zpow_eq_zpow_iff_modEq.1 h2)
        omega
    have hsq : p * p * (d * d) = 1 := by
      calc p * p * (d * d) = p * (p * d) * d := by group
        _ = p * (d * p) * d := by rw [← hpd]
        _ = (p * d) * (p * d) := by group
        _ = 1 := huu
    have hpp : p * p ∈ P ⊓ D := by
      refine ⟨P.mul_mem hp hp, ?_⟩
      have : p * p = (d * d)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact D.inv_mem (D.mul_mem hd hd)
    rw [hPD, Subgroup.mem_bot] at hpp
    have hdd : d * d = 1 := by rw [hpp, one_mul] at hsq; exact hsq
    have hd1f : d = 1 ∨ d = f := by
      by_cases hd1 : d = 1
      · exact Or.inl hd1
      · right
        have := CFSG.GH74.GLS.IVK.DihedralAux.cyclic_unique_involution (G := ↥(zpowers a))
          (a := ⟨d, hdA⟩) (b := ⟨f, hfa⟩) (fun h => hd1 (congrArg Subtype.val h))
          (fun h => hf1 (congrArg Subtype.val h)) (Subtype.ext hdd) (Subtype.ext hf2)
        exact congrArg Subtype.val this
    rcases hd1f with rfl | rfl
    · rw [mul_one]; exact Subgroup.mem_sup_left hp
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right (mem_zpowers _))



theorem eq_one_or_eq_of_mem_zpowers {g w : G} (hg : g * g = 1) (hw : w ∈ zpowers g) :
    w = 1 ∨ w = g := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    simp [sq, hg]
  · right
    rw [zpow_add_one, zpow_mul]
    simp [sq, hg]

theorem exists_V0_of_four
    {V P D : Subgroup G} {x f : G}
    (hDV : D ≤ V) (hPV : P ≤ V)
    (hPn : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P)
    (hDn : ∀ v ∈ V, ∀ d ∈ D, v * d * v⁻¹ ∈ D)
    (hPD : P ⊓ D = ⊥) (hcomm : ∀ p ∈ P, ∀ d ∈ D, p * d = d * p)
    (hDeq : D = zpowers x ⊔ zpowers f) (hx2 : x * x = 1) (hf2 : f * f = 1) (hxf : x * f = f * x)
    (hx1 : x ≠ 1) (hxfne : x ≠ f)
    (hfc : ∀ v ∈ V, v * f = f * v)
    (hinv : ∀ u ∈ V, u * u = 1 → u ∈ P ⊔ D)
    (hcyc : ∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ P ⊔ D) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ (∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) ∧ x ∉ V₀ ∧
      (∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) ∧ P ⊔ zpowers f ≤ V₀ ∧
      ∀ u ∈ V₀, u * u = 1 → u ∈ P ⊔ zpowers f := by
  classical
  obtain ⟨b, hbV, hb⟩ := hcyc
  have hfD : f ∈ D := by rw [hDeq]; exact Subgroup.mem_sup_right (mem_zpowers f)
  have hxD : x ∈ D := by rw [hDeq]; exact Subgroup.mem_sup_left (mem_zpowers x)
  have hfV : f ∈ V := hDV hfD
  have hxV : x ∈ V := hDV hxD
  have hzf : zpowers f ≤ D := (zpowers_le).2 hfD
  have hPf : ∀ p ∈ P, ∀ c ∈ zpowers f, p * c = c * p := fun p hp c hc => hcomm p hp c (hzf hc)
  have hDel : ∀ d ∈ D, d = 1 ∨ d = x ∨ d = f ∨ d = x * f := by
    intro d hd
    rw [hDeq] at hd
    obtain ⟨u, hu, w, hw, rfl⟩ := exists_mul_of_mem_sup (P := zpowers x) (D := zpowers f)
      (fun u hu w hw => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
        exact (Commute.zpow_zpow (show Commute x f from hxf) i j).eq) hd
    rcases eq_one_or_eq_of_mem_zpowers hx2 hu with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers hf2 hw with rfl | rfl <;> simp
  set N : Subgroup G := P ⊔ zpowers f with hN
  have hNV : N ≤ V := sup_le hPV ((zpowers_le).2 hfV)
  have hNel : ∀ n ∈ N, ∃ p ∈ P, n = p ∨ n = p * f := by
    intro n hn
    obtain ⟨p, hp, c, hc, rfl⟩ := exists_mul_of_mem_sup hPf hn
    rcases eq_one_or_eq_of_mem_zpowers hf2 hc with rfl | rfl
    · exact ⟨p, hp, Or.inl (mul_one p)⟩
    · exact ⟨p, hp, Or.inr rfl⟩
  have hNn : ∀ v ∈ V, ∀ n ∈ N, v * n * v⁻¹ ∈ N := by
    intro v hv n hn
    obtain ⟨p, hp, hpn⟩ := hNel n hn
    have hvp : v * p * v⁻¹ ∈ N := Subgroup.mem_sup_left (hPn v hv p hp)
    rcases hpn with rfl | rfl
    · exact hvp
    · have : v * (p * f) * v⁻¹ = (v * p * v⁻¹) * f := by
        calc v * (p * f) * v⁻¹ = (v * p * v⁻¹) * (v * f * v⁻¹) := by group
          _ = (v * p * v⁻¹) * f := by rw [hfc v hv]; group
      rw [this]
      exact N.mul_mem hvp (Subgroup.mem_sup_right (mem_zpowers f))
  have hfN : f ∈ N := Subgroup.mem_sup_right (mem_zpowers f)
  have hPN : P ≤ N := le_sup_left
  have hxN : x ∉ N := by
    intro hx
    obtain ⟨p, hp, hpn⟩ := hNel x hx
    rcases hpn with h | h
    · have : x ∈ P ⊓ D := ⟨h ▸ hp, hxD⟩
      rw [hPD, Subgroup.mem_bot] at this
      exact hx1 this
    · have hpD : p ∈ D := by
        have : p = x * f⁻¹ := by rw [h]; group
        rw [this]
        exact D.mul_mem hxD (D.inv_mem hfD)
      have : p ∈ P ⊓ D := ⟨hp, hpD⟩
      rw [hPD, Subgroup.mem_bot] at this
      subst this
      apply hxfne
      rw [one_mul] at h
      exact h
  have hvx : ∀ v ∈ V, ∃ n ∈ N, v * x * v⁻¹ = x * n := by
    intro v hv
    have hmem : v * x * v⁻¹ ∈ D := hDn v hv x hxD
    rcases hDel _ hmem with h | h | h | h
    · exfalso
      apply hx1
      have : x = v⁻¹ * (v * x * v⁻¹) * v := by group
      rw [this, h]; group
    · exact ⟨1, N.one_mem, by rw [h, mul_one]⟩
    · exfalso
      apply hxfne
      have h1 : v⁻¹ * f * v = f := by
        calc v⁻¹ * f * v = v⁻¹ * (f * v) := by group
          _ = v⁻¹ * (v * f) := by rw [hfc v hv]
          _ = f := by group
      calc x = v⁻¹ * (v * x * v⁻¹) * v := by group
        _ = v⁻¹ * f * v := by rw [h]
        _ = f := h1
    · exact ⟨f, hfN, h⟩
  have hV : ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ N ∨ ∃ n ∈ N, (b ^ k)⁻¹ * v = x * n := by
    intro v hv
    obtain ⟨k, hk⟩ := hb v hv
    refine ⟨k, ?_⟩
    obtain ⟨p, hp, d, hd, hpd⟩ := exists_mul_of_mem_sup hcomm hk
    rcases hDel d hd with h | h | h | h
    · left; rw [hpd, h, mul_one]; exact hPN hp
    · right
      refine ⟨p, hPN hp, ?_⟩
      rw [hpd, h]; exact hcomm p hp x hxD
    · left; rw [hpd, h]; exact N.mul_mem (hPN hp) hfN
    · right
      refine ⟨p * f, N.mul_mem (hPN hp) hfN, ?_⟩
      rw [hpd, h]
      calc p * (x * f) = (p * x) * f := by group
        _ = (x * p) * f := by rw [hcomm p hp x hxD]
        _ = x * (p * f) := by group
  let T' : Subgroup G :=
    { carrier := {v | v ∈ V ∧ b * v * b⁻¹ * v⁻¹ ∈ N}
      one_mem' := ⟨V.one_mem, by simp⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨hv₁, h₁⟩ ⟨hv₂, h₂⟩
        refine ⟨V.mul_mem hv₁ hv₂, ?_⟩
        have : b * (v₁ * v₂) * b⁻¹ * (v₁ * v₂)⁻¹ =
            (b * v₁ * b⁻¹ * v₁⁻¹) * (v₁ * (b * v₂ * b⁻¹ * v₂⁻¹) * v₁⁻¹) := by group
        rw [this]
        exact N.mul_mem h₁ (hNn v₁ hv₁ _ h₂)
      inv_mem' := by
        rintro v ⟨hv, h⟩
        refine ⟨V.inv_mem hv, ?_⟩
        have h' := hNn v⁻¹ (V.inv_mem hv) _ (N.inv_mem h)
        have : b * v⁻¹ * b⁻¹ * v⁻¹⁻¹ = v⁻¹ * (b * v * b⁻¹ * v⁻¹)⁻¹ * v⁻¹⁻¹ := by group
        rw [this]
        exact h' }
  have hT'b : b ∈ T' := ⟨hbV, by simp⟩
  have hT'x : x ∈ T' := by
    refine ⟨hxV, ?_⟩
    obtain ⟨n, hn, hbx⟩ := hvx b hbV
    have : b * x * b⁻¹ * x⁻¹ = x * n * x⁻¹ := by rw [hbx]
    rw [this]
    have h' := hNn x hxV n hn
    exact h'
  have hT'f : f ∈ T' := by
    refine ⟨hfV, ?_⟩
    have : b * f * b⁻¹ * f⁻¹ = 1 := by
      rw [hfc b hbV]; group
    rw [this]; exact N.one_mem
  have hT'P : P ≤ T' := fun p hp => ⟨hPV hp, by
    have := hPn b hbV p hp
    exact N.mul_mem (hPN this) (N.inv_mem (hPN hp))⟩
  have hT'D : D ≤ T' := by
    rw [hDeq]
    exact sup_le ((zpowers_le).2 hT'x) ((zpowers_le).2 hT'f)
  have hVT' : ∀ v ∈ V, v ∈ T' := by
    intro v hv
    obtain ⟨k, hk⟩ := hb v hv
    obtain ⟨p, hp, d, hd, hpd⟩ := exists_mul_of_mem_sup hcomm hk
    have h1 : (b ^ k)⁻¹ * v ∈ T' := by rw [hpd]; exact T'.mul_mem (hT'P hp) (hT'D hd)
    have h2 : v = b ^ k * ((b ^ k)⁻¹ * v) := by group
    rw [h2]
    exact T'.mul_mem (T'.zpow_mem hT'b k) h1
  let S : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ N}
      one_mem' := ⟨V.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro v₁ v₂ ⟨hv₁, k, hk⟩ ⟨hv₂, l, hl⟩
        refine ⟨V.mul_mem hv₁ hv₂, k + l, ?_⟩
        have h1 := hNn (b ^ l)⁻¹ (V.inv_mem (V.zpow_mem hbV l)) _ hk
        have h2 := N.mul_mem h1 hl
        have : (b ^ (k + l))⁻¹ * (v₁ * v₂) =
            (b ^ l)⁻¹ * ((b ^ k)⁻¹ * v₁) * (b ^ l)⁻¹⁻¹ * ((b ^ l)⁻¹ * v₂) := by
          rw [zpow_add, mul_inv_rev]; group
        rw [this]
        exact h2
      inv_mem' := by
        rintro v ⟨hv, k, hk⟩
        refine ⟨V.inv_mem hv, -k, ?_⟩
        have h1 := hNn (b ^ k) (V.zpow_mem hbV k) _ (N.inv_mem hk)
        have : (b ^ (-k))⁻¹ * v⁻¹ = b ^ k * ((b ^ k)⁻¹ * v)⁻¹ * (b ^ k)⁻¹ := by
          rw [zpow_neg, inv_inv]; group
        rw [this]
        exact h1 }
  have hSV : S ≤ V := fun v hv => hv.1
  have hNS : N ≤ S := fun n hn => ⟨hNV hn, 0, by simpa using hn⟩
  have hbS : b ∈ S := ⟨hbV, 1, by simp⟩
  have hSdef : ∀ {v : G}, v ∈ S ↔ v ∈ V ∧ ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ N := Iff.rfl
  have hconjb : ∀ v ∈ V, v * b * v⁻¹ ∈ S := by
    intro v hv
    obtain ⟨-, hc⟩ := hVT' v hv
    refine ⟨?_, 1, ?_⟩
    · exact V.mul_mem (V.mul_mem hv hbV) (V.inv_mem hv)
    · have h1 := hNn b⁻¹ (V.inv_mem hbV) _ (N.inv_mem hc)
      have : (b ^ (1 : ℤ))⁻¹ * (v * b * v⁻¹) = b⁻¹ * (b * v * b⁻¹ * v⁻¹)⁻¹ * b⁻¹⁻¹ := by
        rw [zpow_one]; group
      rw [this]
      exact h1
  have hSconj : ∀ v ∈ V, ∀ w ∈ S, v * w * v⁻¹ ∈ S := by
    intro v hv w hw
    obtain ⟨hwV, k, hk⟩ := hw
    have hw' : w = b ^ k * ((b ^ k)⁻¹ * w) := by group
    have : v * w * v⁻¹ = (v * b * v⁻¹) ^ k * (v * ((b ^ k)⁻¹ * w) * v⁻¹) := by
      calc v * w * v⁻¹ = v * (b ^ k * ((b ^ k)⁻¹ * w)) * v⁻¹ := by rw [← hw']
        _ = (v * b ^ k * v⁻¹) * (v * ((b ^ k)⁻¹ * w) * v⁻¹) := by group
        _ = (v * b * v⁻¹) ^ k * (v * ((b ^ k)⁻¹ * w) * v⁻¹) := by rw [conj_zpow]
    rw [this]
    exact S.mul_mem (S.zpow_mem (hconjb v hv) k) (hNS (hNn v hv _ hk))
  by_cases hxS : x ∈ S
  ·
    refine ⟨N, hNV, hNn, hxN, ⟨b, hbV, ?_⟩, le_rfl, fun u hu _ => hu⟩
    intro v hv
    rcases hV v hv with ⟨k, hk | ⟨n, hn, hkn⟩⟩
    · exact ⟨k, hk⟩
    · have hv' : v = b ^ k * (x * n) := by rw [← hkn]; group
      have hvS : v ∈ S := by
        rw [hv']
        exact S.mul_mem (S.zpow_mem hbS k) (S.mul_mem hxS (hNS hn))
      obtain ⟨-, k', hk'⟩ := hvS
      exact ⟨k', hk'⟩
  · refine ⟨S, hSV, hSconj, hxS, ⟨x, hxV, ?_⟩, hNS, ?_⟩
    · intro v hv
      rcases hV v hv with ⟨k, hk | ⟨n, hn, hkn⟩⟩
      · refine ⟨0, ?_⟩
        have hv' : v = b ^ k * ((b ^ k)⁻¹ * v) := by group
        have : v ∈ S := by
          rw [hv']
          exact S.mul_mem (S.zpow_mem hbS k) (hNS hk)
        simpa using this
      · refine ⟨1, ?_⟩
        have hv' : v = b ^ k * (x * n) := by rw [← hkn]; group
        have h2 : x⁻¹ * b * x⁻¹⁻¹ ∈ S := hconjb x⁻¹ (V.inv_mem hxV)
        have h3 : (x ^ (1 : ℤ))⁻¹ * v = (x⁻¹ * b * x⁻¹⁻¹) ^ k * n := by
          calc (x ^ (1 : ℤ))⁻¹ * v = x⁻¹ * (b ^ k * (x * n)) := by rw [zpow_one, hv']
            _ = (x⁻¹ * b ^ k * x⁻¹⁻¹) * n := by group
            _ = (x⁻¹ * b * x⁻¹⁻¹) ^ k * n := by rw [conj_zpow]
        rw [h3]
        exact S.mul_mem (S.zpow_mem h2 k) (hNS hn)
    · intro u huS huu
      obtain ⟨p, hp, d, hd, hpd⟩ := exists_mul_of_mem_sup hcomm (hinv u (hSV huS) huu)
      rcases hDel d hd with h | h | h | h
      · rw [hpd, h, mul_one]; exact hPN hp
      · exfalso
        apply hxS
        have : x = p⁻¹ * u := by rw [hpd, h]; group
        rw [this]
        exact S.mul_mem (S.inv_mem (hNS (hPN hp))) huS
      · rw [hpd, h]; exact N.mul_mem (hPN hp) hfN
      · exfalso
        apply hxS
        have : x = p⁻¹ * u * f⁻¹ := by rw [hpd, h]; group
        rw [this]
        exact S.mul_mem (S.mul_mem (S.inv_mem (hNS (hPN hp))) huS) (S.inv_mem (hNS hfN))


end CFSG.GH74.GLS.C3.Layer1.Thm1P310
