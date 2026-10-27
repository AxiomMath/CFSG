module

public import CFSG.GH74.GLS.IVK.Lifted.Alt51Lift
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Equiv CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm4 CFSG.GH74.GLS.Stage1.Thm3.Sec4

variable {H : Type} [Group H] [Finite H]

theorem not_central_of_conj_mul {T : Subgroup H} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) {w z g : H}
    (hz1 : z ≠ 1) (hz2 : z * z = 1) (hzc : ∀ x : H, x * z = z * x) (hg : g⁻¹ * w * g = z * w)
    (hwT : ∀ s ∈ T, s * w = w * s) : False := by
  classical
  have hS := syl2In_of_isSylowOf hT
  have hcz : ∀ x : H, x⁻¹ * z * x = z := fun x => by
    calc x⁻¹ * z * x = x⁻¹ * (z * x) := by group
      _ = x⁻¹ * (x * z) := by rw [hzc x]
      _ = z := by group
  have hcz' : ∀ x : H, x * z * x⁻¹ = z := fun x => by
    calc x * z * x⁻¹ = (x * z) * x⁻¹ := rfl
      _ = (z * x) * x⁻¹ := by rw [hzc x]
      _ = z := by group
  let Y : Subgroup H :=
    { carrier := {x | x⁻¹ * w * x = w ∨ x⁻¹ * w * x = z * w}
      one_mem' := Or.inl (by group)
      mul_mem' := fun {a b} ha hb => by
        have e : (a * b)⁻¹ * w * (a * b) = b⁻¹ * (a⁻¹ * w * a) * b := by group
        show (a * b)⁻¹ * w * (a * b) = w ∨ (a * b)⁻¹ * w * (a * b) = z * w
        rcases ha with ha | ha
        · rw [e, ha]
          exact hb
        · rw [e, ha]
          have e2 : b⁻¹ * (z * w) * b = z * (b⁻¹ * w * b) := by
            calc b⁻¹ * (z * w) * b = (b⁻¹ * z * b) * (b⁻¹ * w * b) := by group
              _ = z * (b⁻¹ * w * b) := by rw [hcz b]
          rw [e2]
          rcases hb with hb | hb
          · rw [hb]
            exact Or.inr rfl
          · rw [hb]
            left
            calc z * (z * w) = (z * z) * w := by group
              _ = w := by rw [hz2, one_mul]
      inv_mem' := fun {a} ha => by
        show (a⁻¹)⁻¹ * w * a⁻¹ = w ∨ (a⁻¹)⁻¹ * w * a⁻¹ = z * w
        rcases ha with ha | ha
        · left
          calc (a⁻¹)⁻¹ * w * a⁻¹ = a * w * a⁻¹ := by rw [inv_inv]
            _ = a * (a⁻¹ * w * a) * a⁻¹ := by rw [ha]
            _ = w := by group
        · right
          calc (a⁻¹)⁻¹ * w * a⁻¹ = a * (z * (z * w)) * a⁻¹ := by
                rw [← mul_assoc z z w, hz2, one_mul]; group
            _ = a * (z * (a⁻¹ * w * a)) * a⁻¹ := by rw [← ha]
            _ = (a * z * a⁻¹) * w := by group
            _ = z * w := by rw [hcz'] }
  let X : Subgroup H := Subgroup.centralizer ({w} : Set H)
  have hTX : T ≤ X := fun s hs => Subgroup.mem_centralizer_singleton_iff.2 (hwT s hs)
  have hXY : X ≤ Y := by
    intro x hx
    left
    have := Subgroup.mem_centralizer_singleton_iff.1 hx
    calc x⁻¹ * w * x = x⁻¹ * (w * x) := by group
      _ = x⁻¹ * (x * w) := by rw [this]
      _ = w := by group
  have hgY : g ∈ Y := Or.inr hg
  have hzw : z * w ≠ w := by
    intro h
    apply hz1
    calc z = (z * w) * w⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hindex : (X.subgroupOf Y).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨g, hgY⟩, ?_⟩
    rintro ⟨b, hbY⟩
    have hcoe : ((⟨b, hbY⟩ * ⟨g, hgY⟩ : ↥Y) : H) = b * g := rfl
    by_cases hb : b ∈ X
    · right
      refine ⟨Subgroup.mem_subgroupOf.2 hb, fun hbg => ?_⟩
      have hbg' : b * g ∈ X := by
        have := Subgroup.mem_subgroupOf.1 hbg
        rwa [hcoe] at this
      have h1 := Subgroup.mem_centralizer_singleton_iff.1 hbg'
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hb
      apply hzw
      have hb2 : b⁻¹ * w * b = w := by
        calc b⁻¹ * w * b = b⁻¹ * (w * b) := by group
          _ = b⁻¹ * (b * w) := by rw [h2]
          _ = w := by group
      have e : (b * g)⁻¹ * w * (b * g) = z * w := by
        calc (b * g)⁻¹ * w * (b * g) = g⁻¹ * (b⁻¹ * w * b) * g := by group
          _ = g⁻¹ * w * g := by rw [hb2]
          _ = z * w := hg
      have e2 : (b * g)⁻¹ * w * (b * g) = w := by
        calc (b * g)⁻¹ * w * (b * g) = (b * g)⁻¹ * (w * (b * g)) := by group
          _ = (b * g)⁻¹ * ((b * g) * w) := by rw [h1]
          _ = w := by group
      rw [← e, e2]
    · left
      have hb1 : b⁻¹ * w * b = z * w := by
        rcases hbY with h | h
        · exfalso
          apply hb
          apply Subgroup.mem_centralizer_singleton_iff.2
          calc b * w = b * (b⁻¹ * w * b) := by rw [h]
            _ = w * b := by group
        · exact h
      refine ⟨?_, fun h => hb (Subgroup.mem_subgroupOf.1 h)⟩
      apply Subgroup.mem_subgroupOf.2
      rw [hcoe]
      apply Subgroup.mem_centralizer_singleton_iff.2
      have e : (b * g)⁻¹ * w * (b * g) = w := by
        calc (b * g)⁻¹ * w * (b * g) = g⁻¹ * (b⁻¹ * w * b) * g := by group
          _ = g⁻¹ * (z * w) * g := by rw [hb1]
          _ = z * (g⁻¹ * w * g) := by
            calc g⁻¹ * (z * w) * g = (g⁻¹ * z * g) * (g⁻¹ * w * g) := by group
              _ = z * (g⁻¹ * w * g) := by rw [hcz g]
          _ = z * (z * w) := by rw [hg]
          _ = w := by
            calc z * (z * w) = (z * z) * w := by group
              _ = w := by rw [hz2, one_mul]
      calc (b * g) * w = (b * g) * ((b * g)⁻¹ * w * (b * g)) := by rw [e]
        _ = w * (b * g) := by group
  have h1 : X.relIndex Y * Y.index = X.index := Subgroup.relIndex_mul_index hXY
  have h2 : T.relIndex X * X.index = T.index := Subgroup.relIndex_mul_index hTX
  have h3 : 2 ∣ X.relIndex Y := by rw [Subgroup.relIndex, hindex]
  apply hS.2.2
  rw [Subgroup.relIndex_top_right, ← h2, ← h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h3 _) _

theorem ivk_5_1g : IVK_5_1g := by
  intro H _ _ K n hH T hT w hwT hwc
  classical
  obtain ⟨R⟩ := exists_permRep hH
  obtain ⟨z, hz⟩ := R.exists_kerData
  have hn8 : 8 ≤ n := hH.n_ge
  suffices hρ : R.ρ w = 1 by
    obtain ⟨k, hk, hk1⟩ := R.ker_ρ w hρ
    have hkc : k ∈ Subgroup.center ↥K := R.cover.ker_le_center (MonoidHom.mem_ker.2 hk1)
    refine ⟨hk ▸ k.2, fun k' hk' => ?_⟩
    have h := congrArg Subtype.val (Subgroup.mem_center_iff.1 hkc ⟨k', hk'⟩)
    simpa [hk] using h
  by_contra hne
  have hT2 : IsPGroup 2 ↥T := (syl2In_of_isSylowOf hT).2.1
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hT2) ⟨w, hwT⟩
  have hwo : orderOf w = 2 ^ e := by rw [← Subgroup.orderOf_mk w hwT]; exact he
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    ((orderOf_map_dvd R.ρ w).trans (dvd_of_eq hwo))
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hne
    exact orderOf_eq_one_iff.1 (by rw [hf]; rfl)
  set w' : H := w ^ (2 ^ (f - 1)) with hw'
  have hρw' : R.ρ w' = (R.ρ w) ^ (2 ^ (f - 1)) := by rw [hw', map_pow]
  have hlt : 2 ^ (f - 1) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw2 : R.ρ w' * R.ρ w' = 1 := by
    rw [hρw', ← pow_add]
    have : 2 ^ (f - 1) + 2 ^ (f - 1) = orderOf (R.ρ w) := by
      rw [hf, ← two_mul, ← pow_succ']
      congr 1
      omega
    rw [this, pow_orderOf_eq_one]
  have hw1 : R.ρ w' ≠ 1 := by
    intro h1
    rw [hρw'] at h1
    have h2 := Nat.le_of_dvd (by positivity) (hf ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  have hw'c : ∀ s ∈ T, s * w' = w' * s := fun s hs =>
    ((show Commute s w from hwc s hs).pow_right _).eq
  obtain ⟨g, hg⟩ := hz.exists_conj_mul_z hn8 hw2 hw1
  exact not_central_of_conj_mul hT hz.ne_one hz.sq hz.central hg hw'c

end CFSG.GH74.GLS.IVK.Lifted
