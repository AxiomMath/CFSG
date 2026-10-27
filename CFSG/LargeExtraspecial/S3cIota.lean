module

public import CFSG.LargeExtraspecial.S3cD
public import CFSG.LargeExtraspecial.S3cOdd
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

section Generic

theorem pow_two_pow_apply_ne {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {f : V ≃ₗ[ZMod 2] V} {a p : V} (h1 : f a = p) (h2 : f p = p + a) (hp0 : p ≠ 0)
    (hpa : p ≠ a) (k : ℕ) : (f ^ (2 ^ k)) a ≠ a := by
  have hf3 : f^[3] a = a := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h1, h2, map_add]
    calc p + a + p = a + (p + p) := by abel
      _ = a := by rw [vec_add_self, add_zero]
  have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    have h0 : 2 ^ k % 3 ≠ 0 := by
      intro h0
      have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h0)
      omega
    omega
  rw [LinearEquiv.coe_pow, ← Nat.mod_add_div (2 ^ k) 3, Function.iterate_add_apply,
    Function.iterate_mul, Function.iterate_fixed hf3]
  rcases hmod with h | h <;> rw [h]
  · simpa [h1] using hpa
  · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h1, h2]
    intro h'
    exact hp0 (by simpa using h')

theorem exists_odd_pow_inverted {X : Type*} [Group X] [Finite X] {x y : X} (hx : x * x = 1)
    (hy : y * y = 1) (h2 : ∀ k : ℕ, (x * y) ^ (2 ^ k) ≠ 1) :
    ∃ j m : ℕ, Odd m ∧ ((x * y) ^ j) ^ m = 1 ∧ (x * y) ^ j ≠ 1 ∧
      x * (x * y) ^ j * x = ((x * y) ^ j)⁻¹ := by
  obtain ⟨k, m, hm, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x * y)).ne'
  refine ⟨2 ^ k, m, hm, ?_, h2 k, ?_⟩
  · rw [← pow_mul, ← hN, pow_orderOf_eq_one]
  · have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
    have e : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
      calc x * (x * y) * x⁻¹ = (x * x) * y * x⁻¹ := by group
        _ = y * x := by rw [hx, one_mul, hxinv]
        _ = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv, hyinv]
    calc x * (x * y) ^ 2 ^ k * x = x * (x * y) ^ 2 ^ k * x⁻¹ := by rw [hxinv]
      _ = (x * (x * y) * x⁻¹) ^ 2 ^ k := conj_pow.symm
      _ = ((x * y) ^ 2 ^ k)⁻¹ := by rw [e, inv_pow]

end Generic

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem conj_mem_Dbar_mul {g h : G} (hh : h ∈ S.M) (haQ : g * S.z * g⁻¹ ∈ S.QG) {s : S.O}
    (hs : s ∈ S.Dbar g) : S.ρ ⟨h, hh⟩ * s * (S.ρ ⟨h, hh⟩)⁻¹ ∈ S.Dbar (h * g) := by
  refine ⟨S.conj_mem_Lbar_mul hh hs.1, ?_⟩
  show ((S.ρ ⟨h, hh⟩ * s * (S.ρ ⟨h, hh⟩)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
    pointRadical S.q (S.cl ((h * g) * S.z * (h * g)⁻¹))
  have := conj_mem_pointRadical (m := ((S.ρ ⟨h, hh⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (S.ρ ⟨h, hh⟩).2 hs.2
  rw [S.ρ_cl_conj_z hh haQ] at this
  simpa using this

theorem eq_one_or_eq_conj_of_mem_Lbar_mul {g h : G} (hh : h ∈ S.M)
    (haQ : g * S.z * g⁻¹ ∈ S.QG) {x : S.O}
    (hD : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1 ∨ s = x)
    {s : S.O} (hs : s ∈ S.Lbar (h * g))
    (hsN : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl ((h * g) * S.z * (h * g)⁻¹))) :
    s = 1 ∨ s = S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹ := by
  have hh' : h⁻¹ ∈ S.M := S.M.inv_mem hh
  have hρ : S.ρ ⟨h⁻¹, hh'⟩ = (S.ρ ⟨h, hh⟩)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    have e : (⟨h⁻¹, hh'⟩ : S.M) * ⟨h, hh⟩ = 1 := Subtype.ext (inv_mul_cancel h)
    rw [e, map_one]
  have h1 : S.ρ ⟨h⁻¹, hh'⟩ * s * (S.ρ ⟨h⁻¹, hh'⟩)⁻¹ ∈ S.Dbar g := by
    have := S.conj_mem_Dbar_mul hh' (S.conj_mul_mem_QG hh haQ) ⟨hs, hsN⟩
    rwa [inv_mul_cancel_left] at this
  rw [hρ, inv_inv] at h1
  rcases hD _ h1.1 h1.2 with h2 | h2
  · left
    calc s = S.ρ ⟨h, hh⟩ * ((S.ρ ⟨h, hh⟩)⁻¹ * s * S.ρ ⟨h, hh⟩) * (S.ρ ⟨h, hh⟩)⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · right
    calc s = S.ρ ⟨h, hh⟩ * ((S.ρ ⟨h, hh⟩)⁻¹ * s * S.ρ ⟨h, hh⟩) * (S.ρ ⟨h, hh⟩)⁻¹ := by group
      _ = _ := by rw [h2]

theorem card_Lbar_fix_le_two (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width)
    {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) (hh : h ∈ S.M)
    (hab : g * S.z * g⁻¹ * ((h * g) * S.z * (h * g)⁻¹) =
      (h * g) * S.z * (h * g)⁻¹ * (g * S.z * g⁻¹))
    {x : S.O} (hx : x ∈ S.Lbar g) (hx1 : x ≠ 1)
    (hxN : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)))
    (hD : ∀ s ∈ S.Lbar g,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1 ∨ s = x)
    (hxb : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) ≠
      S.cl ((h * g) * S.z * (h * g)⁻¹)) :
    Nat.card {s : S.Qt ≃ₗ[ZMod 2] S.Qt // s ∈ S.LbarLin g ∧
      s (S.cl ((h * g) * S.z * (h * g)⁻¹)) = S.cl ((h * g) * S.z * (h * g)⁻¹)} ≤ 2 := by
  classical
  have : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    Finite.of_injective (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => (e : S.Qt → S.Qt))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  have hbQ : (h * g) * S.z * (h * g)⁻¹ ∈ S.QG := S.conj_mul_mem_QG hh haQ
  have hbne : (h * g) * S.z * (h * g)⁻¹ ≠ S.z := S.conj_mul_ne_z hh hne
  have hno' : ¬ S.HasTypeAInL (h * g) := fun h1 => hno (S.hasTypeAInL_of_mul hh h1)
  have hyD := S.conj_mem_Dbar_mul hh haQ ⟨hx, hxN⟩
  set y := S.ρ ⟨h, hh⟩ * x * (S.ρ ⟨h, hh⟩)⁻¹ with hy
  have hy1 : y ≠ 1 := fun h1 => hx1 (by
    calc x = (S.ρ ⟨h, hh⟩)⁻¹ * y * S.ρ ⟨h, hh⟩ := by rw [hy]; group
      _ = 1 := by rw [h1]; group)
  have hD' : ∀ s ∈ S.Lbar (h * g), (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈
      pointRadical S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) → s = 1 ∨ s = y :=
    fun s hs hsN => S.eq_one_or_eq_conj_of_mem_Lbar_mul hh haQ hD hs hsN
  have hperp : polar S.q (S.cl (g * S.z * g⁻¹)) (S.cl ((h * g) * S.z * (h * g)⁻¹)) = 0 :=
    (S.polar_cl_eq_zero_iff haQ hbQ).mpr hab
  have hperp' : polar S.q (S.cl ((h * g) * S.z * (h * g)⁻¹)) (S.cl (g * S.z * g⁻¹)) = 0 := by
    rw [polar_comm]
    exact hperp
  have hxa : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    (mem_pointRadical.mp hxN).2.1
  have hyb : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) := (mem_pointRadical.mp hyD.2).2.1
  have hxb' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
    rcases mem_span_singleton_iff.mp ((mem_pointRadical.mp hxN).2.2.1 _ hperp) with h0 | h1
    · exact absurd (sub_eq_zero.mp h0) hxb
    · rw [← h1]
      abel
  have hya : (y : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) + S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    rcases mem_span_singleton_iff.mp ((mem_pointRadical.mp hyD.2).2.2.1 _ hperp') with h0 | h1
    · exfalso
      apply hxb
      have hc := S.commute_of_fix_of_Lbar_inf_eq haQ hne hx hx1 hxN hD
        (S.Lbar_le_Mbar _ hyD.1) (sub_eq_zero.mp h0)
      exact S.fixes_of_commute_mem_pointRadical hbQ hbne hno' hyD.1 hy1 hyD.2 hc.symm
    · rw [← h1]
      abel
  have hb0 := S.cl_conj_z_ne_zero hbQ hbne
  have hba : S.cl ((h * g) * S.z * (h * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) := fun e =>
    hxb (by rw [e, hxa])
  have hcyc1 : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hya, map_add, hxa, hxb']
    calc S.cl (g * S.z * g⁻¹) + (S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹)) =
        S.cl ((h * g) * S.z * (h * g)⁻¹) + (S.cl (g * S.z * g⁻¹) + S.cl (g * S.z * g⁻¹)) := by
          abel
      _ = _ := by rw [vec_add_self, add_zero]
  have hcyc2 : ((x * y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h * g) * S.z * (h * g)⁻¹)) =
      S.cl ((h * g) * S.z * (h * g)⁻¹) + S.cl (g * S.z * g⁻¹) := by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hyb, hxb']
  have h2 : ∀ k : ℕ, (x * y) ^ (2 ^ k) ≠ 1 := by
    intro k h1
    apply pow_two_pow_apply_ne hcyc1 hcyc2 hb0 hba k
    rw [← Subgroup.coe_pow, h1]
    rfl
  have hxx : x * x = 1 := by
    have := S.sq_eq_one_of_mem_Lbar haQ hx
    rwa [pow_two] at this
  have hyy : y * y = 1 := by
    have := S.sq_eq_one_of_mem_Lbar hbQ hyD.1
    rwa [pow_two] at this
  obtain ⟨j, m, hm, hpow, hι1, hinv⟩ := exists_odd_pow_inverted hxx hyy h2
  have hιM : (x * y) ^ j ∈ S.Mbar :=
    pow_mem (mul_mem (S.Lbar_le_Mbar g hx) (S.Lbar_le_Mbar _ hyD.1)) j
  have hle := S.card_Lbar_commute_le_two hTI hn haQ hne hno hirr hx hx1 hxN hD hιM hm hpow hinv
    hι1
  let f : {s : S.Qt ≃ₗ[ZMod 2] S.Qt // s ∈ S.LbarLin g ∧
      s (S.cl ((h * g) * S.z * (h * g)⁻¹)) = S.cl ((h * g) * S.z * (h * g)⁻¹)} →
      {s : S.Qt ≃ₗ[ZMod 2] S.Qt // s ∈ S.LbarLin g ∧
        s * (((x * y) ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
          (((x * y) ^ j : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) * s} := fun s =>
    ⟨s.1, s.2.1, by
      obtain ⟨t, ht, hts⟩ := S.mem_LbarLin_iff.mp s.2.1
      have htx : Commute t x := S.Lbar_comm haQ ht hx
      have hty : Commute t y := S.commute_of_fix_of_Lbar_inf_eq hbQ hbne hyD.1 hy1 hyD.2 hD'
        (S.Lbar_le_Mbar g ht) (by rw [hts]; exact s.2.2)
      have := congrArg Subtype.val ((htx.mul_right hty).pow_right j).eq
      rw [← hts]
      exact this⟩
  have hf : Function.Injective f := fun s s' hss' => by
    have e := congrArg Subtype.val hss'
    exact Subtype.ext e
  exact (Nat.card_le_card_of_injective f hf).trans hle

end Setting

end CFSG.LargeExtraspecial
