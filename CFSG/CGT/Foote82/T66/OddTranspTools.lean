module

public import CFSG.Quasithin.Background.G11Defs
import CFSG.Quasithin.Background.G11Basic
import CFSG.RankThree.GF2n.DihedralCompl
import CFSG.CGT.Foote82.Lemma62Tools

public section

namespace CFSG.CGT.Foote82

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {g : G}
    (hg : orderOf g = 2) : g * g = 1 := by
  rw [← sq, ← hg]
  exact pow_orderOf_eq_one g

private theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {g k : G} (hg : orderOf g = 2)
    (hk : k ∈ Subgroup.zpowers g) : k = 1 ∨ k = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : (orderOf g : ℤ) = 2 := by rw [hg]; rfl
  have h : g ^ n = g ^ (n % 2) := by rw [← h2, zpow_mod_orderOf]
  rw [h]
  rcases Int.emod_two_eq_zero_or_one n with h0 | h0
  · left
    rw [h0, zpow_zero]
  · right
    rw [h0, zpow_one]

private theorem commSpace_zpowers_eq_map {d : GLV V} (hd : orderOf d = 2)
    (U : Submodule (ZMod 2) V) :
    commSpace (Subgroup.zpowers d) U = U.map ((d : V →ₗ[ZMod 2] V) - 1) := by
  apply le_antisymm
  · refine commSpace_le_iff.2 fun k hk u hu => ?_
    rcases eq_one_or_eq_of_mem_zpowers hd hk with rfl | rfl
    · simp
    · exact ⟨u, hu, by simp⟩
  · rintro _ ⟨u, hu, rfl⟩
    simpa using sub_mem_commSpace (Subgroup.mem_zpowers d) hu

private theorem apply_mem_commSpace_of_inverts {x c : GLV V} (h : x * c * x⁻¹ = c⁻¹) {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers c) ⊤) : x w ∈ commSpace (Subgroup.zpowers c) ⊤ := by
  have hle : commSpace (Subgroup.zpowers c) ⊤ ≤
      (commSpace (Subgroup.zpowers c) ⊤).comap (x : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u _ => ?_
    show x (k u - u) ∈ commSpace (Subgroup.zpowers c) ⊤
    have e : x (k u - u) = (x * k * x⁻¹) (x u) - x u := by simp [mul_assoc]
    rw [e]
    refine sub_mem_commSpace ?_ Submodule.mem_top
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [← conj_zpow, h, inv_zpow]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) n)
  exact hle hw

private theorem finrank_eq_two_mul_finrank_inf_ker {a b : Module.End (ZMod 2) V}
    (ha : a * a = 1) (hb : b * b = 1) {P : Submodule (ZMod 2) V} (hPa : P ≤ P.comap a)
    (hPb : P ≤ P.comap b) (hfix : ∀ v ∈ P, a v = v → b v = v → v = 0) :
    Module.finrank (ZMod 2) P =
      2 * Module.finrank (ZMod 2) ↥(P ⊓ LinearMap.ker (a - 1)) := by
  have h1 := CFSG.RankThree.GF2n.finrank_le_two_mul_finrank_inf_ker ha hPa
  have h2 := CFSG.RankThree.GF2n.finrank_le_two_mul_finrank_inf_ker hb hPb
  have hdis : (P ⊓ LinearMap.ker (a - 1)) ⊓ (P ⊓ LinearMap.ker (b - 1)) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨hvP, hva⟩, ⟨-, hvb⟩⟩
    exact (Submodule.mem_bot (ZMod 2)).2 (hfix v hvP
      (CFSG.RankThree.GF2n.mem_ker_sub_one.1 hva) (CFSG.RankThree.GF2n.mem_ker_sub_one.1 hvb))
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊓ LinearMap.ker (a - 1))
    (P ⊓ LinearMap.ker (b - 1))
  rw [hdis, finrank_bot, add_zero] at h3
  have hle : (P ⊓ LinearMap.ker (a - 1)) ⊔ (P ⊓ LinearMap.ker (b - 1)) ≤ P :=
    sup_le inf_le_left inf_le_left
  have h4 := Submodule.finrank_mono hle
  omega

theorem s3_trick {d e : GLV V} (hd : orderOf d = 2) (he : orderOf e = 2)
    (hc : Odd (orderOf (d * e))) (hc1 : d * e ≠ 1)
    (hde : commSpace (Subgroup.zpowers d) ⊤ ⊓ commSpace (Subgroup.zpowers e) ⊤ = ⊥) :
    (∀ w ∈ fixedSpace (Subgroup.zpowers (d * e)), d w = w) ∧
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (d * e)) ⊤) =
        2 * Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers d) ⊤) := by
  have hdd : d * d = 1 := mul_self_eq_one_of_orderOf_eq_two hd
  have hee : e * e = 1 := mul_self_eq_one_of_orderOf_eq_two he
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right hee
  have hd' : ∀ v, d (d v) = v := fun v => by
    have := congrArg (fun f : GLV V => f v) hdd
    simpa using this
  have hfix : ∀ w ∈ fixedSpace (Subgroup.zpowers (d * e)), d w = w := by
    intro w hw
    have hcw : (d * e) w = w := hw _ (Subgroup.mem_zpowers _)
    have h1 : d (e w) = w := hcw
    have h2 : e w = d w := by
      calc e w = d (d (e w)) := (hd' _).symm
        _ = d w := by rw [h1]
    have h3 : d w - w ∈ commSpace (Subgroup.zpowers d) ⊤ ⊓ commSpace (Subgroup.zpowers e) ⊤ :=
      ⟨sub_mem_commSpace (Subgroup.mem_zpowers d) Submodule.mem_top, by
        rw [← h2]
        exact sub_mem_commSpace (Subgroup.mem_zpowers e) Submodule.mem_top⟩
    rw [hde, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  refine ⟨hfix, ?_⟩
  set c : GLV V := d * e with hcdef
  set W : Submodule (ZMod 2) V := commSpace (Subgroup.zpowers c) ⊤ with hW
  have hcompl : IsCompl (fixedSpace (Subgroup.zpowers c)) W :=
    isCompl_fixedSpace_commSpace (by rwa [Nat.card_zpowers])
  have hdc : d * c * d⁻¹ = c⁻¹ := by
    rw [hcdef, mul_inv_rev, hdinv, heinv]
    calc d * (d * e) * d = (d * d) * e * d := by simp only [mul_assoc]
      _ = e * d := by rw [hdd, one_mul]
  have hec : e * c * e⁻¹ = c⁻¹ := by
    rw [hcdef, mul_inv_rev, hdinv, heinv]
    calc e * (d * e) * e = e * d * (e * e) := by simp only [mul_assoc]
      _ = e * d := by rw [hee, mul_one]
  have hWd : W ≤ W.comap (d : V →ₗ[ZMod 2] V) := fun w hw => apply_mem_commSpace_of_inverts hdc hw
  have hWe : W ≤ W.comap (e : V →ₗ[ZMod 2] V) := fun w hw => apply_mem_commSpace_of_inverts hec hw
  have ha : (d : V →ₗ[ZMod 2] V) * (d : V →ₗ[ZMod 2] V) = 1 := by
    ext v
    exact hd' v
  have hb : (e : V →ₗ[ZMod 2] V) * (e : V →ₗ[ZMod 2] V) = 1 := by
    ext v
    have := congrArg (fun f : GLV V => f v) hee
    simpa using this
  have hfixW : ∀ v ∈ W, (d : V →ₗ[ZMod 2] V) v = v → (e : V →ₗ[ZMod 2] V) v = v → v = 0 := by
    intro v hvW hdv hev
    have hcv : c v = v := by
      show d (e v) = v
      rw [show e v = v from hev]
      exact hdv
    have hvF : v ∈ fixedSpace (Subgroup.zpowers c) := by
      intro k hk
      have : k ∈ MulAction.stabilizer (GLV V) v :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hcv) hk
      exact MulAction.mem_stabilizer_iff.1 this
    exact (Submodule.mem_bot (ZMod 2)).1 (hcompl.inf_eq_bot ▸ (⟨hvF, hvW⟩ : v ∈ _ ⊓ W))
  have hmap : (⊤ : Submodule (ZMod 2) V).map ((d : V →ₗ[ZMod 2] V) - 1) =
      W.map ((d : V →ₗ[ZMod 2] V) - 1) := by
    refine le_antisymm ?_ (Submodule.map_mono le_top)
    rintro _ ⟨v, -, rfl⟩
    have hv : v ∈ fixedSpace (Subgroup.zpowers c) ⊔ W := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨f, hf, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
    refine ⟨w, hw, ?_⟩
    simp [hfix f hf]
  have h1 := CFSG.RankThree.GF2n.finrank_map_add_finrank_inf_ker ((d : V →ₗ[ZMod 2] V) - 1) W
  have h2 := finrank_eq_two_mul_finrank_inf_ker ha hb hWd hWe hfixW
  rw [commSpace_zpowers_eq_map hd, hmap]
  omega

theorem exists_conj_eq_mul_of_unique_involution {G : Type*} [Group G] [Finite G]
    {S : Subgroup G} {y z : G} (hS : IsPGroup 2 S) (hzS : z ∈ S) (hz : orderOf z = 2)
    (huniq : ∀ x ∈ S, orderOf x = 2 → x = z) (hy : orderOf y = 2)
    (hyN : y ∈ Subgroup.normalizer (S : Set G))
    (hnc : ∃ r ∈ S, r * y ≠ y * r) : ∃ d ∈ S, d⁻¹ * y * d = y * z := by
  obtain ⟨r, hrS, hr⟩ := hnc
  have hyy : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hy
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  obtain ⟨c, hc⟩ : ∃ c : G, c = y * r⁻¹ * y * r := ⟨_, rfl⟩
  have hcS : c ∈ S := by
    have h1 : y * r⁻¹ * y⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hyN r⁻¹).1 (S.inv_mem hrS)
    have h2 : c = (y * r⁻¹ * y⁻¹) * r := by rw [hc, hyinv]
    rw [h2]
    exact S.mul_mem h1 hrS
  have hc1 : c ≠ 1 := by
    intro h
    apply hr
    have h' : y * r⁻¹ * y * r = 1 := hc ▸ h
    calc r * y = r * y * (y * r⁻¹ * y * r) := by rw [h', mul_one]
      _ = r * (y * y) * r⁻¹ * y * r := by group
      _ = y * r := by rw [hyy]; group
  have hycy : y * c * y = c⁻¹ := by
    calc y * c * y = (y * y) * r⁻¹ * y * r * y := by rw [hc]; group
      _ = r⁻¹ * y⁻¹ * r * y⁻¹ := by rw [hyy, hyinv]; group
      _ = c⁻¹ := by rw [hc]; group
  have hycpow : ∀ m : ℕ, y * c ^ m * y = (c ^ m)⁻¹ := by
    intro m
    have h1 : (y * c * y⁻¹) ^ m = y * c ^ m * y⁻¹ := conj_pow
    rw [hyinv, hycy, inv_pow] at h1
    exact h1.symm
  by_cases hcz : c = z
  ·
    refine ⟨r, hrS, ?_⟩
    rw [← hcz, hc]
    calc r⁻¹ * y * r = (y * y) * r⁻¹ * y * r := by rw [hyy, one_mul]
      _ = y * (y * r⁻¹ * y * r) := by group
  ·
    obtain ⟨k, hk⟩ : ∃ k : ℕ, orderOf c = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨c, hcS⟩
      exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
    have hk2 : 2 ≤ k := by
      by_contra hlt
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · exact hc1 (orderOf_eq_one_iff.1 (by simpa using hk))
      · exact hcz (huniq c hcS (by simpa using hk))
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
    set d : G := c ^ 2 ^ j with hd
    have hdS : d ∈ S := S.pow_mem hcS _
    have hd2 : d ^ 2 = z := by
      have hdd : d ^ 2 = c ^ 2 ^ (j + 1) := by rw [hd, ← pow_mul, pow_succ]
      have hord : orderOf (c ^ 2 ^ (j + 1)) = 2 := by
        rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
          (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk,
          show 2 ^ (j + 2) = 2 ^ (j + 1) * 2 from pow_succ 2 (j + 1)]
        exact Nat.mul_div_cancel_left 2 (by positivity)
      exact huniq _ (hdd ▸ S.pow_mem hcS _) (hdd ▸ hord)
    have hyd : y * d * y = d⁻¹ := by rw [hd]; exact hycpow _
    refine ⟨d, hdS, ?_⟩
    calc d⁻¹ * y * d = (y * d * y) * y * d := by rw [hyd]
      _ = y * d * (y * y) * d := by group
      _ = y * (d * d) := by rw [hyy]; group
      _ = y * z := by rw [← sq, hd2]

end CFSG.CGT.Foote82
