module

public import CFSG.CGT.PushingUpLit.SYMB.ProdCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Even

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

section Involutions

variable {G : Type*} [Group G]

theorem exists_zpow_conj_of_involutions {h h' : G} (hh : h * h = 1) (hh' : h' * h' = 1)
    (hodd : Odd (orderOf (h' * h⁻¹))) :
    ∃ d ∈ zpowers (h' * h⁻¹), h' = d * h * d⁻¹ := by
  have hh_inv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh
  have hh'_inv : h'⁻¹ = h' := inv_eq_of_mul_eq_one_right hh'
  let n : G := h' * h⁻¹
  have hoddn : Odd (orderOf n) := hodd
  obtain ⟨k, hk⟩ := hoddn
  have hn_pow : n ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one n
  have hn_inv : n⁻¹ = h * h' := by
    show (h' * h⁻¹)⁻¹ = h * h'
    rw [mul_inv_rev, inv_inv, hh'_inv]
  have hconj : h * n * h⁻¹ = n⁻¹ := by
    rw [hn_inv]
    show h * (h' * h⁻¹) * h⁻¹ = h * h'
    rw [hh_inv, ← mul_assoc h h' h, mul_assoc (h * h') h h, hh, mul_one]
  have hconj_aut : MulAut.conj h n = n⁻¹ := by
    rw [MulAut.conj_apply]
    exact hconj
  have hd : h * n ^ (k + 1) * h⁻¹ = (n ^ (k + 1))⁻¹ := by
    calc h * n ^ (k + 1) * h⁻¹ = MulAut.conj h (n ^ (k + 1)) := by
          rw [MulAut.conj_apply]
      _ = (MulAut.conj h n) ^ (k + 1) := by rw [map_pow]
      _ = (n⁻¹) ^ (k + 1) := by rw [hconj_aut]
      _ = (n ^ (k + 1))⁻¹ := by rw [inv_pow]
  have hd' : h * (n ^ (k + 1))⁻¹ * h⁻¹ = n ^ (k + 1) := by
    have hinv := congrArg Inv.inv hd
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hinv
  have hdd : n ^ (k + 1) * n ^ (k + 1) = n := by
    rw [← pow_add]
    have hexp : k + 1 + (k + 1) = 2 * k + 1 + 1 := by ring
    rw [hexp, pow_succ, hn_pow, one_mul]
  have hfinal : n ^ (k + 1) * h * (n ^ (k + 1))⁻¹ = h' := by
    calc n ^ (k + 1) * h * (n ^ (k + 1))⁻¹
        = n ^ (k + 1) * (h * (n ^ (k + 1))⁻¹ * h⁻¹) * h := by group
      _ = n ^ (k + 1) * n ^ (k + 1) * h := by rw [hd']
      _ = n * h := by rw [hdd]
      _ = h' := by
          show (h' * h⁻¹) * h = h'
          rw [mul_assoc, inv_mul_cancel, mul_one]
  exact ⟨n ^ (k + 1), Subgroup.pow_mem (zpowers n) (Subgroup.mem_zpowers n) (k + 1),
    hfinal.symm⟩

theorem mem_closure_pair_of_commute_involutions {a b g : G} (hab : a * b = b * a)
    (ha : a * a = 1) (hb : b * b = 1) (hg : g ∈ closure ({a, b} : Set G)) :
    g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have hba : b * a = a * b := hab.symm
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have haba : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have habb : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have habab : (a * b) * (a * b) = 1 := by rw [mul_assoc, hbab, ha]
  refine closure_induction (p := fun g _ => g = 1 ∨ g = a ∨ g = b ∨ g = a * b)
    ?_ ?_ ?_ ?_ hg
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl
  · intro x y hx hy ihx ihy
    rcases ihx with rfl | rfl | rfl | rfl <;>
      rcases ihy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, ha, hb, hba, haab, hbab, haba, habb, habab,
        or_true, true_or, or_false, false_or]
  · intro x hx ih
    rcases ih with rfl | rfl | rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right ha))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right hb)))
    · exact Or.inr (Or.inr (Or.inr (inv_eq_of_mul_eq_one_right habab)))

theorem eq_of_mem_zpowers_of_orderOf_eq_two {a b : G} (ha : orderOf a = 2) (hb : b ∈ zpowers a)
    (hb1 : b ≠ 1) : b = a := by
  have h2 : (orderOf a : ℤ) = 2 := by rw [ha]; rfl
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
  have hk' : a ^ (k % 2) = b := by
    rw [← hk, ← h2]
    exact zpow_mod_orderOf a k
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hmod with h | h
  · rw [h, zpow_zero] at hk'
    exact absurd hk'.symm hb1
  · rw [h, zpow_one] at hk'
    exact hk'.symm

theorem card_centralizer_conj (u c : G) :
    Nat.card ↥(centralizer ({c * u * c⁻¹} : Set G)) = Nat.card ↥(centralizer ({u} : Set G)) := by
  have hmap : (centralizer ({u} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * u * c⁻¹} : Set G) := by
    ext z
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc
        z * (c * u * c⁻¹) = c * ((c⁻¹ * z * c) * u) * c⁻¹ := by group
        _ = c * (u * (c⁻¹ * z * c)) * c⁻¹ := by rw [h]
        _ = (c * u * c⁻¹) * z := by group
    · intro h
      calc
        (c⁻¹ * z * c) * u = c⁻¹ * (z * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * z) * c := by rw [h]
        _ = u * (c⁻¹ * z * c) := by group
  rw [← hmap]
  exact Subgroup.card_map_of_injective (MulAut.conj c).injective

theorem card_mul_card_dvd_of_commute {A B C : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) (hA : A ≤ C) (hB : B ≤ C) :
    Nat.card ↥A * Nat.card ↥B ∣ Nat.card ↥C := by
  have h1 := CFSG.CGT.PushingUpLit.SYMB.card_sup_mul_card_inf_of_commute hc
  rw [hinf, Subgroup.card_bot, mul_one] at h1
  rw [← h1]
  exact Subgroup.card_dvd_of_le (sup_le hA hB)

end Involutions

section OddCore

theorem map_oddCore_le_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom ≤ CFSG.oddCore B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  apply le_sSup
  refine ⟨hN.1.map e.toMonoidHom e.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hN.2

theorem map_oddCore_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.oddCore A).map e.toMonoidHom = CFSG.oddCore B := by
  refine le_antisymm (map_oddCore_le_mulEquiv e) fun x hx => ?_
  rw [Subgroup.mem_map_equiv]
  exact map_oddCore_le_mulEquiv e.symm (Subgroup.mem_map_of_mem e.symm.toMonoidHom hx)

end OddCore

section Conj

variable {G : Type} [Group G]

theorem map_centralizer_conj (T : Subgroup G) (g : G) :
    (centralizer (T : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro w hw
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hw
    change (g * t * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * t * g⁻¹)
    calc (g * t * g⁻¹) * (g * x * g⁻¹)
        = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [hx t ht]
      _ = (g * x * g⁻¹) * (g * t * g⁻¹) := by group
  · intro hz
    rw [Subgroup.mem_map_equiv]
    rw [Subgroup.mem_centralizer_iff] at hz ⊢
    intro t ht
    have h : (g * t * g⁻¹) * z = z * (g * t * g⁻¹) :=
      hz (g * t * g⁻¹) (Subgroup.mem_map.2 ⟨t, ht, rfl⟩)
    rw [MulAut.conj_symm_apply]
    calc t * (g⁻¹ * z * g)
        = g⁻¹ * ((g * t * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * t * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * z * g) * t := by group

theorem isCompIn_centralizer_map_conj {K T : Subgroup G}
    (h : IsCompIn K (centralizer (T : Set G))) (g : G) :
    IsCompIn (K.map (MulAut.conj g).toMonoidHom)
      (centralizer ((T.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  rw [← map_centralizer_conj]
  exact Hyp.isCompIn_map_mulEquiv (MulAut.conj g) h

theorem linkData_conj {K T₀ : Subgroup G} {s₀ g : G} (hg : g ∈ centralizer (K : Set G))
    (hT : T₀ ≠ ⊥) (hT2 : IsPGroup 2 T₀) (hK : IsCompIn K (centralizer (T₀ : Set G)))
    (hs2 : IsPGroup 2 (zpowers s₀)) (hsN : s₀ ∈ normalizer (T₀ : Set G)) (hs : s₀ ^ 2 ∈ T₀)
    (hswap : K ≠ K.map (MulAut.conj s₀).toMonoidHom) :
    T₀.map (MulAut.conj g).toMonoidHom ≠ ⊥ ∧ IsPGroup 2 (T₀.map (MulAut.conj g).toMonoidHom) ∧
      IsCompIn K (centralizer ((T₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) ∧
      IsPGroup 2 (zpowers (g * s₀ * g⁻¹)) ∧
      g * s₀ * g⁻¹ ∈ normalizer ((T₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      (g * s₀ * g⁻¹) ^ 2 ∈ T₀.map (MulAut.conj g).toMonoidHom ∧
      K ≠ K.map (MulAut.conj (g * s₀ * g⁻¹)).toMonoidHom := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hT ((Subgroup.map_eq_bot_iff_of_injective T₀
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).1 hbot)
  · exact hT2.map (MulAut.conj g).toMonoidHom
  · have hKg : K.map (MulAut.conj g).toMonoidHom = K := by
      ext k
      constructor
      · rintro ⟨y, hy, rfl⟩
        change g * y * g⁻¹ ∈ K
        have hcomm : y * g = g * y := Subgroup.mem_centralizer_iff.1 hg y hy
        rwa [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      · intro hk
        refine ⟨k, hk, ?_⟩
        change g * k * g⁻¹ = k
        have hcomm : k * g = g * k := Subgroup.mem_centralizer_iff.1 hg k hk
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h := isCompIn_centralizer_map_conj hK g
    rwa [hKg] at h
  · have key : zpowers (g * s₀ * g⁻¹) = (zpowers s₀).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [key]
    exact hs2.map (MulAut.conj g).toMonoidHom
  · rw [Subgroup.mem_set_normalizer_iff]
    intro w
    have hsN' : ∀ n, n ∈ T₀ ↔ s₀ * n * s₀⁻¹ ∈ T₀ :=
      Subgroup.mem_set_normalizer_iff.1 hsN
    change w ∈ T₀.map (MulAut.conj g).toMonoidHom ↔
      (g * s₀ * g⁻¹) * w * (g * s₀ * g⁻¹)⁻¹ ∈ T₀.map (MulAut.conj g).toMonoidHom
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have key : (MulAut.conj g).symm ((g * s₀ * g⁻¹) * w * (g * s₀ * g⁻¹)⁻¹)
        = s₀ * (MulAut.conj g).symm w * s₀⁻¹ := by
      simp only [MulAut.conj_symm_apply]
      group
    rw [key]
    exact hsN' _
  · have key : (g * s₀ * g⁻¹) ^ 2 = (MulAut.conj g).toMonoidHom (s₀ ^ 2) := by
      rw [map_pow]
      rfl
    rw [key]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hs
  · intro hconj
    set c : G := g * s₀ * g⁻¹ with hc
    have hconj_id : ∀ k ∈ K, s₀ * k * s₀⁻¹ = g⁻¹ * (c * k * c⁻¹) * g := by
      intro k hk
      have hkg : g⁻¹ * k * g = k := by
        have hcomm : k * g = g * k := Subgroup.mem_centralizer_iff.1 hg k hk
        rw [mul_assoc, hcomm, inv_mul_cancel_left]
      have hid : g⁻¹ * ((g * s₀ * g⁻¹) * k * (g * s₀ * g⁻¹)⁻¹) * g
          = s₀ * (g⁻¹ * k * g) * s₀⁻¹ := by
        group
      rw [hc, hid, hkg]
    have hle : K.map (MulAut.conj s₀).toMonoidHom ≤ K := by
      rintro _ ⟨k, hk, rfl⟩
      change s₀ * k * s₀⁻¹ ∈ K
      rw [hconj_id k hk]
      have hkK : c * k * c⁻¹ ∈ K := by
        rw [hconj]
        exact Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hk
      have hcomm : (c * k * c⁻¹) * g = g * (c * k * c⁻¹) :=
        Subgroup.mem_centralizer_iff.1 hg _ hkK
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
      exact hkK
    have hge : K ≤ K.map (MulAut.conj s₀).toMonoidHom := by
      intro x hx
      have hx' : x ∈ K.map (MulAut.conj c).toMonoidHom := hconj ▸ hx
      obtain ⟨k, hk, hkx⟩ := hx'
      change c * k * c⁻¹ = x at hkx
      refine ⟨k, hk, ?_⟩
      change s₀ * k * s₀⁻¹ = x
      rw [hconj_id k hk, hkx]
      have hcomm : x * g = g * x := Subgroup.mem_centralizer_iff.1 hg x hx
      rw [mul_assoc, hcomm, inv_mul_cancel_left]
    exact hswap (le_antisymm hle hge).symm

end Conj

end CFSG.EvenSporadicStandard.M12Std.Rbc
