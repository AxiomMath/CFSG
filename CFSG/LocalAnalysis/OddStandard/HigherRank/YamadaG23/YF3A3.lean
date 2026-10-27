module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3A2b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3K

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f3_conj_mem_B_of_mem_X0 {s : Setting3 G L} {e : Setting3.Ext s}
    (hH : F33Hyp s e) {a : G} (haH : a ∈ s.H)
    (haC : a ∈ Subgroup.centralizer (cen s.fr.B : Set G)) :
    ∀ b ∈ s.fr.B, a * b * a⁻¹ ∈ s.fr.B := by
  have hBcent : s.fr.B ≤ Subgroup.centralizer (cen s.fr.B : Set G) := by
    have hle : centIn L (cen s.fr.B) ≤ Subgroup.centralizer (cen s.fr.B : Set G) := by
      rw [centIn]
      exact inf_le_right
    rwa [f3_centIn_L_V hH] at hle
  intro b hb
  have hbL : b ∈ L := f3_B_le_L s hb
  have habL : a * b * a⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (s3_H_le_N s hH.hS haH) b).mp hbL
  rw [← f3_centIn_L_V hH, centIn]
  refine Subgroup.mem_inf.mpr ⟨habL, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hva : a * v = v * a := (Subgroup.mem_centralizer_iff.mp haC v hv).symm
  have hbv : v * b = b * v := Subgroup.mem_centralizer_iff.mp (hBcent hb) v hv
  have hav : a * v * a⁻¹ = v := by rw [hva]; group
  have ha'v : a⁻¹ * v * a = v := by
    have h := (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.centralizer (cen s.fr.B : Set G)).inv_mem haC) v hv).symm
    rw [h]; group
  calc v * (a * b * a⁻¹)
      = a * ((a⁻¹ * v * a) * b) * a⁻¹ := by group
    _ = a * (v * b) * a⁻¹ := by rw [ha'v]
    _ = a * (b * v) * a⁻¹ := by rw [hbv]
    _ = (a * b * a⁻¹) * (a * v * a⁻¹) := by group
    _ = (a * b * a⁻¹) * v := by rw [hav]

private theorem f3X0_le_N_aux {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3X0 s ≤ f3N s := by
  intro a ha
  rw [f3X0, centIn] at ha
  simp only [Subgroup.mem_inf] at ha
  obtain ⟨haH, haC⟩ := ha
  have haH' : a⁻¹ ∈ s.H := s.H.inv_mem haH
  have haC' : a⁻¹ ∈ Subgroup.centralizer (cen s.fr.B : Set G) :=
    (Subgroup.centralizer (cen s.fr.B : Set G)).inv_mem haC
  rw [f3N, normIn]
  refine Subgroup.mem_inf.mpr ⟨haH, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  exact ⟨f3_conj_mem_B_of_mem_X0 hH haH haC b, fun hb => by
    have h := f3_conj_mem_B_of_mem_X0 hH haH' haC' (a * b * a⁻¹) hb
    have he : a⁻¹ * (a * b * a⁻¹) * (a⁻¹)⁻¹ = b := by group
    rwa [he] at h⟩

theorem f3_Y_normal {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ y ∈ f3Y s, x * y * x⁻¹ ∈ f3Y s := by
  intro x hx y hy
  rw [f3Y, centIn] at hy
  simp only [Subgroup.mem_inf] at hy
  obtain ⟨hyX, hyC⟩ := hy
  rw [f3Y, centIn]
  refine Subgroup.mem_inf.mpr ⟨s.X.mul_mem (s.X.mul_mem hx hyX) (s.X.inv_mem hx), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvx : x⁻¹ * v * x ∈ cen s.fr.B := by
    simpa using f3_X_norm_V hH x⁻¹ (s.X.inv_mem hx) v hv
  have hcomm : y * (x⁻¹ * v * x) = (x⁻¹ * v * x) * y :=
    (Subgroup.mem_centralizer_iff.mp hyC _ hvx).symm
  calc v * (x * y * x⁻¹)
      = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [← hcomm]
    _ = (x * y * x⁻¹) * v := by group

theorem f3_Y_inf_H {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3Y s ⊓ s.H = f3X0 s := by
  apply le_antisymm
  · intro y hy
    rw [f3Y, centIn] at hy
    simp only [Subgroup.mem_inf] at hy
    obtain ⟨⟨hyX, hyC⟩, hyH⟩ := hy
    rw [f3X0, centIn]
    exact Subgroup.mem_inf.mpr ⟨hyH, hyC⟩
  · intro a ha
    rw [f3X0, centIn] at ha
    simp only [Subgroup.mem_inf] at ha
    obtain ⟨haH, haC⟩ := ha
    have haN : a ∈ f3N s := f3X0_le_N_aux hH (by
      rw [f3X0, centIn]
      exact Subgroup.mem_inf.mpr ⟨haH, haC⟩)
    have haX : a ∈ s.X := f3_N_le_X s haN
    refine Subgroup.mem_inf.mpr ⟨?_, haH⟩
    rw [f3Y, centIn]
    exact Subgroup.mem_inf.mpr ⟨haX, haC⟩

theorem f3_X0_normal {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∀ a ∈ f3X0 s, x * a * x⁻¹ ∈ f3X0 s := by
  intro x hx a ha
  rw [f3X0, centIn] at ha
  simp only [Subgroup.mem_inf] at ha
  obtain ⟨haH, haC⟩ := ha
  have haXt : a * s.t = s.t * a := Subgroup.mem_centralizer_singleton_iff.mp haH
  rw [f3X0, centIn]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · change (x * a * x⁻¹) ∈ Subgroup.centralizer ({s.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨v', hv', hv'eq⟩ := f3_tX_sub hH x⁻¹ (s.X.inv_mem hx)
    have hv'eq' : x⁻¹ * s.t * x = v' * s.t := by simpa using hv'eq
    have hav' : a * v' = v' * a := (Subgroup.mem_centralizer_iff.mp haC v' hv').symm
    have hcomm : a * (v' * s.t) = (v' * s.t) * a := by
      calc a * (v' * s.t) = (a * v') * s.t := by group
        _ = (v' * a) * s.t := by rw [hav']
        _ = v' * (a * s.t) := by group
        _ = v' * (s.t * a) := by rw [haXt]
        _ = (v' * s.t) * a := by group
    have ht_eq : s.t = x * (v' * s.t) * x⁻¹ := by rw [← hv'eq']; group
    rw [ht_eq]
    calc (x * a * x⁻¹) * (x * (v' * s.t) * x⁻¹)
        = x * (a * (v' * s.t)) * x⁻¹ := by group
      _ = x * ((v' * s.t) * a) * x⁻¹ := by rw [hcomm]
      _ = (x * (v' * s.t) * x⁻¹) * (x * a * x⁻¹) := by group
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvx : x⁻¹ * v * x ∈ cen s.fr.B := by
      simpa using f3_X_norm_V hH x⁻¹ (s.X.inv_mem hx) v hv
    have hcomm : a * (x⁻¹ * v * x) = (x⁻¹ * v * x) * a :=
      (Subgroup.mem_centralizer_iff.mp haC _ hvx).symm
    calc v * (x * a * x⁻¹)
        = x * ((x⁻¹ * v * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * v * x)) * x⁻¹ := by rw [← hcomm]
      _ = (x * a * x⁻¹) * v := by group

theorem f3_X0_le_N {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3X0 s ≤ f3N s :=
  f3X0_le_N_aux hH

private theorem mem_centralizer_of_fixes {V : Subgroup G} {z w : G}
    (hV : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = w ∨ v = z * w)
    {y : G} (hyz : y * z * y⁻¹ = z) (hyw : y * w * y⁻¹ = w) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases hV v hv with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact (mul_inv_eq_iff_eq_mul.mp hyz).symm
  · exact (mul_inv_eq_iff_eq_mul.mp hyw).symm
  · have hzw : y * (z * w) * y⁻¹ = z * w := by
      calc y * (z * w) * y⁻¹ = (y * z * y⁻¹) * (y * w * y⁻¹) := by group
        _ = z * w := by rw [hyz, hyw]
    exact (mul_inv_eq_iff_eq_mul.mp hzw).symm

theorem f3_exists_u {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ u ∈ e.T₁, u ∈ f3Y s ∧ u * s.t * u⁻¹ = s.fr.z * s.t := by
  have hA : LFactsA s := lfactsA_of_setting hH.hS hH.hZ s
  obtain ⟨w, hwV, hzV, hw1, hz1, hwz, _, _, _, hVcases⟩ := f3_V_elems hH
  have hVcases' := hVcases
  have hcenS : cen s.fr.S = s.fr.Z := s3_cen_S s hA
  have hzCen : s.fr.z ∈ cen s.fr.S := by rw [hcenS]; exact Subgroup.mem_zpowers s.fr.z
  have hclass : s.fr.z * s.t ∈ conjClass e.T₁ s.t := by
    rw [hH.hDef.2.2]
    exact ⟨s.fr.z, hzCen, rfl⟩
  obtain ⟨x₀, hx₀T1, hx₀eq⟩ := hclass
  have hx₀eq' : x₀ * s.t * x₀⁻¹ = s.fr.z * s.t := hx₀eq.symm
  have hx₀X : x₀ ∈ s.X := f3_T1_le_X hH hx₀T1
  have hx₀fixz : x₀ * s.fr.z * x₀⁻¹ = s.fr.z := s3_conj_z s hA e hH.h32 hx₀T1
  have hc_mem : x₀ * w * x₀⁻¹ ∈ cen s.fr.B := f3_X_norm_V hH x₀ hx₀X w hwV
  rcases hVcases (x₀ * w * x₀⁻¹) hc_mem with hc1 | hcz | hcw | hczw
  · exfalso
    apply hw1
    calc w = x₀⁻¹ * (x₀ * w * x₀⁻¹) * x₀ := by group
      _ = 1 := by rw [hc1]; group
  · exfalso
    apply hwz
    have hx₀invz : x₀⁻¹ * s.fr.z * x₀ = s.fr.z := by
      calc x₀⁻¹ * s.fr.z * x₀ = x₀⁻¹ * (x₀ * s.fr.z * x₀⁻¹) * x₀ := by rw [hx₀fixz]
        _ = s.fr.z := by group
    calc w = x₀⁻¹ * (x₀ * w * x₀⁻¹) * x₀ := by group
      _ = x₀⁻¹ * s.fr.z * x₀ := by rw [hcz]
      _ = s.fr.z := hx₀invz
  · have huY : x₀ ∈ f3Y s := by
      rw [f3Y, centIn]
      exact Subgroup.mem_inf.mpr ⟨hx₀X, mem_centralizer_of_fixes hVcases' hx₀fixz hcw⟩
    exact ⟨x₀, hx₀T1, huY, hx₀eq'⟩
  · obtain ⟨τ, hτT, hτS, _, hτmove⟩ := f3_exists_tau hH
    have hτT1 : τ ∈ e.T₁ := hH.h32.2.1.1 hτS
    have hτX : τ ∈ s.X := f3_N_le_X s (f3_T_le_N hH hτT)
    have hτfixz : τ * s.fr.z * τ⁻¹ = s.fr.z := by
      have hzc : s.fr.z ∈ cen s.fr.S := by rw [hcenS]; exact Subgroup.mem_zpowers s.fr.z
      rw [cen] at hzc
      have hzcen : s.fr.z ∈ Subgroup.centralizer (s.fr.S : Set G) :=
        (Subgroup.mem_inf.mp hzc).2
      have h := Subgroup.mem_centralizer_iff.mp hzcen τ hτS
      rw [h]; group
    have hτw : τ * w * τ⁻¹ = s.fr.z * w := hτmove w hwV hw1 hwz
    have hx₀w : x₀ * w * x₀⁻¹ = s.fr.z * w := hczw
    have huz : (x₀ * τ) * s.fr.z * (x₀ * τ)⁻¹ = s.fr.z := by
      calc (x₀ * τ) * s.fr.z * (x₀ * τ)⁻¹
          = x₀ * (τ * s.fr.z * τ⁻¹) * x₀⁻¹ := by group
        _ = x₀ * s.fr.z * x₀⁻¹ := by rw [hτfixz]
        _ = s.fr.z := hx₀fixz
    have huw : (x₀ * τ) * w * (x₀ * τ)⁻¹ = w := by
      calc (x₀ * τ) * w * (x₀ * τ)⁻¹
          = x₀ * (τ * w * τ⁻¹) * x₀⁻¹ := by group
        _ = x₀ * (s.fr.z * w) * x₀⁻¹ := by rw [hτw]
        _ = (x₀ * s.fr.z * x₀⁻¹) * (x₀ * w * x₀⁻¹) := by group
        _ = s.fr.z * (s.fr.z * w) := by rw [hx₀fixz, hx₀w]
        _ = w := by
              rw [← mul_assoc, show s.fr.z * s.fr.z = 1 from by
                rw [← pow_two, ← s3_z_order s hA]; exact pow_orderOf_eq_one s.fr.z]
              exact one_mul w
    have huY : x₀ * τ ∈ f3Y s := by
      rw [f3Y, centIn]
      exact Subgroup.mem_inf.mpr ⟨s.X.mul_mem hx₀X hτX,
        mem_centralizer_of_fixes hVcases' huz huw⟩
    refine ⟨x₀ * τ, e.T₁.mul_mem hx₀T1 hτT1, huY, ?_⟩
    have hτt : τ * s.t * τ⁻¹ = s.t := by
      have h := s3_comm_t_of_mem_L s (s3_S_le_L s hτS)
      rw [h]; group
    calc (x₀ * τ) * s.t * (x₀ * τ)⁻¹
        = x₀ * (τ * s.t * τ⁻¹) * x₀⁻¹ := by group
      _ = x₀ * s.t * x₀⁻¹ := by rw [hτt]
      _ = s.fr.z * s.t := hx₀eq'

theorem f3_Y_orbit {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ v ∈ cen s.fr.B, ∃ y ∈ f3Y s, y * s.t * y⁻¹ = v * s.t := by
  intro v hv
  by_cases hv1 : v = 1
  · rw [hv1]
    exact ⟨1, (f3Y s).one_mem, by group⟩
  · obtain ⟨u, _, huY, hut⟩ := f3_exists_u (s := s) (e := e) hH
    obtain ⟨k, hkN, _, _, _, hktrans, _⟩ := f3_exists_k hH
    obtain ⟨_, _, hzV, _, hz1, _, _, _, _, _⟩ := f3_V_elems hH
    obtain ⟨i, hi⟩ := hktrans s.fr.z hzV hz1 v hv hv1
    have hkL : k ∈ L := by
      have h := hkN
      rw [normIn] at h
      exact (Subgroup.mem_inf.mp h).1
    have hkiL : k ^ i ∈ L := L.pow_mem hkL i
    have hkiN : k ^ i ∈ normalizer (s.fr.B : Set G) := by
      have h := hkN
      rw [normIn] at h
      exact (Subgroup.normalizer (s.fr.B : Set G)).pow_mem (Subgroup.mem_inf.mp h).2 i
    have hkiH : k ^ i ∈ s.H := s3_L_le_H s hH.hS hkiL
    have hkiX : k ^ i ∈ s.X := f3_N_le_X s (by
      rw [f3N, normIn]
      exact Subgroup.mem_inf.mpr ⟨hkiH, hkiN⟩)
    refine ⟨k ^ i * u * (k ^ i)⁻¹, f3_Y_normal hH (k ^ i) hkiX u huY, ?_⟩
    have hkt : k ^ i * s.t * (k ^ i)⁻¹ = s.t := by
      have hcomm : k ^ i * s.t = s.t * k ^ i := s3_comm_t_of_mem_L s hkiL
      rw [hcomm]; group
    have hAt : k ^ i * s.t = s.t * k ^ i := mul_inv_eq_iff_eq_mul.mp hkt
    have hinvt : (k ^ i)⁻¹ * s.t * k ^ i = s.t := by
      calc (k ^ i)⁻¹ * s.t * k ^ i = (k ^ i)⁻¹ * (s.t * k ^ i) := by group
        _ = (k ^ i)⁻¹ * (k ^ i * s.t) := by rw [← hAt]
        _ = s.t := by group
    calc k ^ i * u * (k ^ i)⁻¹ * s.t * (k ^ i * u * (k ^ i)⁻¹)⁻¹
        = k ^ i * (u * ((k ^ i)⁻¹ * s.t * k ^ i) * u⁻¹) * (k ^ i)⁻¹ := by group
      _ = k ^ i * (u * s.t * u⁻¹) * (k ^ i)⁻¹ := by rw [hinvt]
      _ = k ^ i * (s.fr.z * s.t) * (k ^ i)⁻¹ := by rw [hut]
      _ = (k ^ i * s.fr.z * (k ^ i)⁻¹) * (k ^ i * s.t * (k ^ i)⁻¹) := by group
      _ = v * s.t := by rw [hi, hkt]

theorem f3_X_eq_YN {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ x ∈ s.X, ∃ y ∈ f3Y s, ∃ n ∈ f3N s, x = y * n := by
  intro x hx
  obtain ⟨v, hv, hvx⟩ := f3_tX_sub hH x hx
  obtain ⟨y, hyY, hyv⟩ := f3_Y_orbit hH v hv
  have hyX : y ∈ s.X := by
    have h := hyY
    rw [f3Y, centIn] at h
    exact (Subgroup.mem_inf.mp h).1
  have hnX : y⁻¹ * x ∈ s.X := s.X.mul_mem (s.X.inv_mem hyX) hx
  refine ⟨y, hyY, y⁻¹ * x, ?_, by group⟩
  rw [f3N, normIn]
  refine Subgroup.mem_inf.mpr ⟨?_, f3_X_le_normB hH hnX⟩
  change (y⁻¹ * x) ∈ Subgroup.centralizer ({s.t} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : (x⁻¹ * y) * s.t * (x⁻¹ * y)⁻¹ = s.t := by
    have h1 : y * s.t * y⁻¹ = x * s.t * x⁻¹ := hyv.trans hvx.symm
    calc (x⁻¹ * y) * s.t * (x⁻¹ * y)⁻¹
        = x⁻¹ * (y * s.t * y⁻¹) * x := by group
      _ = x⁻¹ * (x * s.t * x⁻¹) * x := by rw [h1]
      _ = s.t := by group
  have hB : (x⁻¹ * y) * s.t = s.t * (x⁻¹ * y) := mul_inv_eq_iff_eq_mul.mp hconj
  have hn_inv : (x⁻¹ * y)⁻¹ * s.t * (x⁻¹ * y) = s.t := by
    calc (x⁻¹ * y)⁻¹ * s.t * (x⁻¹ * y)
        = (x⁻¹ * y)⁻¹ * (s.t * (x⁻¹ * y)) := by group
      _ = (x⁻¹ * y)⁻¹ * ((x⁻¹ * y) * s.t) := by rw [← hB]
      _ = s.t := by group
  have hn : y⁻¹ * x = (x⁻¹ * y)⁻¹ := by group
  rw [hn]
  exact mul_inv_eq_iff_eq_mul.mp (by simpa only [inv_inv] using hn_inv)

end CFSG.OddStandard.HigherRank.YamadaG23
