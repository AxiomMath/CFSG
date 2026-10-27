module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.F4TransvectionAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule binRep_injective binRep_apply)

section Mod

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {z : Module.End (ZMod 2) V}

theorem natCard_modEq_one_of_invariant [Finite V] (hz3 : ∀ v, z (z (z v)) = v)
    (hfpf : ∀ v, z v = v → v = 0) (S : Submodule (ZMod 2) V) (hS : ∀ s ∈ S, z s ∈ S) :
    Nat.card S ≡ 1 [MOD 3] := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun s => ⟨z s, hS s s.2⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext s
    apply Subtype.ext
    have e : (f ^ 3 ^ 1) s = f (f (f s)) := rfl
    rw [e]
    exact hz3 s
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 3) (n := 1) hf3
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  have h1 : Nat.card (Function.fixedPoints f) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨0, ?_⟩, ?_⟩
    · apply Subtype.ext
      simp [f]
    · intro y
      apply Subtype.ext
      apply Subtype.ext
      exact hfpf _ (congrArg Subtype.val y.2)
  rwa [h1] at h

end Mod

theorem even_of_two_pow_modEq_one {m : ℕ} (h : 2 ^ m ≡ 1 [MOD 3]) : Even m := by
  rcases Nat.even_or_odd m with he | ⟨k, hk⟩
  · exact he
  · exfalso
    have h4 : 4 ^ k ≡ 1 [MOD 3] := by
      have := (show 4 ≡ 1 [MOD 3] by decide).pow k
      simpa using this
    have h2 : 2 ^ m ≡ 2 [MOD 3] := by
      rw [hk, pow_succ, pow_mul]
      have := (h4.mul_right 2)
      simpa [mul_comm] using this
    have := h2.symm.trans h
    revert this
    decide

section Conj

variable {W : Type} [CommGroup W] [Finite W]

theorem index_fixV_conj (g a : MulAut W) :
    (fixV (Subgroup.zpowers (g * a * g⁻¹))).index = (fixV (Subgroup.zpowers a)).index :=
  CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj g a

theorem sixteen_le_index_of_conj_order (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    {z a : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    (hzL : ∀ l ∈ L, l * z = z * l) (haL : a ∈ L) (ha1 : a ≠ 1) (ha2 : a * a = 1)
    (hF1 : ∃ g ∈ L, 5 < orderOf (a * (g * a * g⁻¹))) :
    16 ≤ (fixV (Subgroup.zpowers a)).index := by
  obtain ⟨m, hm⟩ := QuasithinUnique.Setup.X1.index_fixV_eq_two_pow hW (Subgroup.zpowers a)
  let _ : Module (ZMod 2) (Additive W) := binModule (fun v => by rw [pow_two]; exact hW v)
  have hz3' : ∀ v, binRep W z (binRep W z (binRep W z v)) = v := by
    intro v
    have h : (binRep W z) ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
    simpa [pow_succ, Module.End.mul_apply] using congrArg (fun f : Module.End (ZMod 2) _ => f v) h
  have hfpf' : ∀ v, binRep W z v = v → v = 0 := fun v h => by
    have := hfpf (Additive.toMul v) (by simpa [binRep_apply] using congrArg Additive.toMul h)
    exact Additive.toMul.injective (by simpa using this)
  have hcomm : ∀ v, binRep W z (binRep W a v) = binRep W a (binRep W z v) := fun v => by
    have := congrArg (fun f : Module.End (ZMod 2) _ => f v)
      (show binRep W z * binRep W a = binRep W a * binRep W z by
        rw [← map_mul, ← map_mul, ← hzL a haL])
    simpa [Module.End.mul_apply] using this
  have hS : ∀ s ∈ LinearMap.range (binRep W a - 1), binRep W z s ∈
      LinearMap.range (binRep W a - 1) := by
    rintro s ⟨v, rfl⟩
    refine ⟨binRep W z v, ?_⟩
    simp [hcomm]
  have hmod := natCard_modEq_one_of_invariant hz3' hfpf' _ hS
  rw [card_range_binRep_sub_one, hm] at hmod
  have hev := even_of_two_pow_modEq_one hmod
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply ha1
    have h1 : (fixV (Subgroup.zpowers a)).index = 1 := by simpa using hm
    have htop := Subgroup.index_eq_one.1 h1
    ext v
    have : v ∈ fixV (Subgroup.zpowers a) := by rw [htop]; trivial
    simpa using (mem_fixV_zpowers_iff.1 this)
  have hm2 : m ≠ 2 := by
    rintro rfl
    obtain ⟨g, hg, hord⟩ := hF1
    have hginv : Commute g⁻¹ z := (show Commute g z from hzL g hg).inv_left
    have hcomm' : (g * a * g⁻¹) * z = z * (g * a * g⁻¹) :=
      ((show Commute g z from hzL g hg).mul_left (show Commute a z from hzL a haL)).mul_left
        hginv
    have ha'2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
      have : (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      rw [this, ha2]; group
    have hA : (fixV (Subgroup.zpowers a)).index = 4 := by simpa using hm
    have hA' : (fixV (Subgroup.zpowers (g * a * g⁻¹))).index = 4 := by
      rw [index_fixV_conj]; exact hA
    have := orderOf_mul_le_five_of_index_four hW hz3 hfpf (hzL a haL) hcomm' ha2 ha'2 hA hA'
    omega
  have hm4 : 4 ≤ m := by
    obtain ⟨k, hk⟩ := hev
    omega
  rw [hm]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4

end Conj

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
