module

public import CFSG.Certificates.Kernel.KDenseP.Glue
public import CFSG.Monster.AxisCount.DenseModSeven

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense CFSG.Monster.AxisCount

noncomputable abbrev to7 : ZMod (2 ^ 3 - 1) →+* ZMod 7 := ZMod.castHom (by norm_num) (ZMod 7)

theorem res7_eq (v : Native.DVec) (k : ℕ) : DVec.res7 v k = to7 (resN 3 v k) := by
  simp only [resN, DVec.res7, map_mul, map_pow, map_intCast, map_ofNat]
  norm_num

theorem cong7D_of_resN {u v : Native.DVec} (h : ∀ k < 196884, resN 3 u k = resN 3 v k) :
    Cong7D u v :=
  fun k hk => by rw [res7_eq, res7_eq, h k hk]

theorem res7_ne_of_castHom {u v : Native.DVec} (hq : 7 ∣ 2 ^ 3 - 1)
    (h : ∃ k < 196884,
      ZMod.castHom hq (ZMod 7) (resN 3 u k) ≠ ZMod.castHom hq (ZMod 7) (resN 3 v k)) :
    ∃ k < 196884, DVec.res7 u k ≠ DVec.res7 v k := by
  obtain ⟨k, hk, hne⟩ := h
  exact ⟨k, hk, by rwa [res7_eq, res7_eq]⟩

theorem val7_sound {v : Native.DVec} {s : St} {t u : ℕ} (hs : RepN 3 v s)
    (h : valOK 3 s t u = true) :
    (t : ZMod 7) = ∑ i ∈ Finset.range 24, ∑ j ∈ Finset.range 24, DVec.res7 v (Native.aIdx i j) ^ 2 ∧
      (u : ZMod 7) = DVec.res7 v 300 := by
  obtain ⟨h1, h2⟩ := valOK_sound hs h
  refine ⟨?_, ?_⟩
  · rw [← map_natCast to7 t, h1]
    simp only [map_sum, map_pow, res7_eq]
  · rw [← map_natCast to7 u, h2, res7_eq]

end CFSG.KC.KDenseP

end
