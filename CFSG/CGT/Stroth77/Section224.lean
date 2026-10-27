module

public import CFSG.CGT.Stroth77.Stroth2Mho
public import CFSG.CGT.Stroth77.StrothFrameNE

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {X : StrothAmbient G}

theorem exists_two_mul_of_two_mul_eq_zero {k : ℕ} (hk : 2 ≤ k) {x : ZMod (2 ^ k)}
    (h : (2 : ℕ) * x = 0) : ∃ y : ZMod (2 ^ k), (2 : ℕ) * y = x := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = (n : ZMod (2 ^ k)) :=
    ⟨x.val, (ZMod.natCast_zmod_val x).symm⟩
  have hdvd : 2 ^ k ∣ 2 * n := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
  have h4dvd : 4 ∣ 2 * n := h4.trans hdvd
  obtain ⟨t, ht⟩ := h4dvd
  have h2 : 2 ∣ n := by
    refine ⟨t, ?_⟩
    have h4 : 2 * n = 2 * (2 * t) := by rw [ht]; ring
    omega
  obtain ⟨t, rfl⟩ := h2
  refine ⟨(t : ZMod (2 ^ k)), ?_⟩
  push_cast
  ring

theorem omegaIn_one_le_mhoOne_of_two_le_k (Z : StrothDatum X)
    (hk : ∀ i, 2 ≤ Z.τ.k i) : omegaIn 1 Z.D ≤ mhoOne Z.D := by
  have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  intro x hx
  obtain ⟨hxD, hx2⟩ := (mem_omegaIn_iff_of_comm hcomm).mp hx
  set v : Torus Z.τ.k := Z.dataD.e (Additive.ofMul ⟨x, hxD⟩) with hv
  have hv2 : (2 : ℤ) • v = 0 := by
    calc (2 : ℤ) • v
        = Z.dataD.e ((2 : ℤ) • Additive.ofMul (⟨x, hxD⟩ : Z.D)) := by
          rw [hv, map_zsmul]
      _ = Z.dataD.e (Additive.ofMul ((⟨x, hxD⟩ : Z.D) ^ 2)) := by
          rw [ofMul_pow]
          norm_num
      _ = Z.dataD.e (Additive.ofMul (1 : Z.D)) := by
          rw [show (⟨x, hxD⟩ : Z.D) ^ 2 = 1 from Subtype.ext hx2]
      _ = 0 := by simp
  obtain ⟨V, hV⟩ : ∃ V : Fin 3 → ℤ, v = Torus.ofInt Z.τ.k V := by
    choose V hV using fun i => ZMod.intCast_surjective (v i)
    exact ⟨V, funext fun i => by simpa [Torus.ofInt_apply] using (hV i).symm⟩
  have hdiv : ∀ i, ((2 ^ Z.τ.k i : ℕ) : ℤ) ∣ 2 * V i := by
    intro i
    have hi : ((2 * V i : ℤ) : ZMod (2 ^ Z.τ.k i)) = 0 := by
      have h := congrFun (hV ▸ hv2) i
      simpa only [Torus.ofInt_apply, Pi.smul_apply, Pi.zero_apply, zsmul_eq_mul,
        Int.cast_ofNat, Int.cast_mul, Int.cast_natCast] using h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * V i) (2 ^ Z.τ.k i)).mp hi
  have hEven : ∀ i, Even (V i) := by
    intro i
    have h4 : (4 : ℤ) ∣ ((2 ^ Z.τ.k i : ℕ) : ℤ) := by
      have h := pow_dvd_pow (2 : ℕ) (hk i)
      exact_mod_cast h
    have h4dvd : (4 : ℤ) ∣ 2 * V i := h4.trans (hdiv i)
    obtain ⟨t, ht⟩ := h4dvd
    refine ⟨t, ?_⟩
    have h4 : 2 * V i = 2 * (2 * t) := by rw [ht]; ring
    linarith
  obtain ⟨w, hw⟩ := (Torus.exists_two_zsmul_eq_iff
    (fun i => le_trans (by norm_num : 1 ≤ 2) (hk i)) V).mpr hEven
  have hwv : (2 : ℤ) • w = v := by rw [hV]; exact hw
  set y : Z.D := Additive.toMul (Z.dataD.e.symm w) with hy
  have hy2 : (y : G) * (y : G) = x := by
    have hy2' : y * y = ⟨x, hxD⟩ := by
      apply Additive.ofMul.injective
      apply Z.dataD.e.injective
      have hyw : Additive.ofMul y = Z.dataD.e.symm w := by
        rw [hy]
        simp
      have h1 : Z.dataD.e (Additive.ofMul (y * y)) = w + w := by
        rw [ofMul_mul, map_add, hyw]
        simp
      rw [h1]
      show w + w = v
      rw [← hwv, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, natCast_zsmul, two_nsmul]
    exact congrArg Subtype.val hy2'
  rw [← hy2]
  simpa [pow_two] using
    CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := Z.D) (n := 2) y.2

theorem commutator_mem_omegaIn_one_of_mem_centralizerInMho {Z : StrothDatum X} {x : G}
    (hx : x ∈ Z.centralizerInMho) {d : G} (hd : d ∈ Z.D) :
    x * d * x⁻¹ * d⁻¹ ∈ omegaIn 1 Z.D := by
  have hxN : x ∈ Subgroup.normalizer (Z.D : Set G) := hx.1.2
  have hxd : x * d * x⁻¹ ∈ Z.D := (Subgroup.mem_normalizer_iff.mp hxN d).mp hd
  have hd2 : d * d ∈ mhoOne Z.D := by
    simpa [pow_two] using
      CFSG.GroupTheory.HuppertProduct.pow_mem_mho (S := Z.D) (n := 2) hd
  have hcomm : (d * d) * x = x * (d * d) :=
    Subgroup.mem_centralizer_iff.mp hx.2 (d * d) hd2
  have hv2 : (x * d * x⁻¹) * (x * d * x⁻¹) = d * d := by
    have h1 : x * (d * d) * x⁻¹ = d * d := by rw [← hcomm]; group
    calc (x * d * x⁻¹) * (x * d * x⁻¹)
        = x * (d * d) * x⁻¹ := by group
      _ = d * d := h1
  have hcommD : (x * d * x⁻¹) * d = d * (x * d * x⁻¹) :=
    congrArg Subtype.val
      (Z.dataD.isMulCommutative.is_comm.comm (⟨x * d * x⁻¹, hxd⟩ : Z.D) ⟨d, hd⟩)
  have hvdinv : (x * d * x⁻¹) * d⁻¹ = d⁻¹ * (x * d * x⁻¹) := by
    have h' : d⁻¹ * ((x * d * x⁻¹) * d) * d⁻¹ = d⁻¹ * (d * (x * d * x⁻¹)) * d⁻¹ := by
      rw [hcommD]
    simpa [mul_assoc] using h'.symm
  have hu2 : ((x * d * x⁻¹) * d⁻¹) * ((x * d * x⁻¹) * d⁻¹) = 1 := by
    calc ((x * d * x⁻¹) * d⁻¹) * ((x * d * x⁻¹) * d⁻¹)
        = (x * d * x⁻¹) * (d⁻¹ * (x * d * x⁻¹)) * d⁻¹ := by group
      _ = (x * d * x⁻¹) * ((x * d * x⁻¹) * d⁻¹) * d⁻¹ := by rw [← hvdinv]
      _ = ((x * d * x⁻¹) * (x * d * x⁻¹)) * (d⁻¹ * d⁻¹) := by group
      _ = (d * d) * (d⁻¹ * d⁻¹) := by rw [hv2]
      _ = 1 := by group
  have hmem : x * d * x⁻¹ * d⁻¹ ∈ Z.D :=
    Subgroup.mul_mem Z.D hxd (Z.D.inv_mem hd)
  have hsq : (x * d * x⁻¹ * d⁻¹) * (x * d * x⁻¹ * d⁻¹) = 1 := hu2
  exact mem_omegaIn_one_of_mul_self hmem hsq

theorem sq_mem_D_of_mem_centralizerInMho {Z : StrothDatum X}
    (hk : ∀ i, 2 ≤ Z.τ.k i) {s : G} (hs : s ∈ Z.centralizerInMho) : s * s ∈ Z.D := by
  have hsS : s ∈ (X.S : Subgroup G) := hs.1.1
  have hsOmega : s ∈ Subgroup.centralizer ((omegaIn 1 Z.D : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (omegaIn_one_le_mhoOne_of_two_le_k Z hk) hs.2
  have hs2cent : s * s ∈ Subgroup.centralizer (Z.D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    set u : G := s * d * s⁻¹ * d⁻¹ with hu
    have huOmega : u ∈ omegaIn 1 Z.D :=
      commutator_mem_omegaIn_one_of_mem_centralizerInMho hs hd
    have hsu : s * u * s⁻¹ = u := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hsOmega u huOmega
      calc s * u * s⁻¹ = u * s * s⁻¹ := by rw [hcomm]
        _ = u := by group
    have hsd' : s * d * s⁻¹ = u * d := by rw [hu]; group
    have hsq : (s * s) * d * (s * s)⁻¹ * d⁻¹ = 1 := by
      calc (s * s) * d * (s * s)⁻¹ * d⁻¹
          = s * (s * d * s⁻¹) * s⁻¹ * d⁻¹ := by group
        _ = s * (u * d) * s⁻¹ * d⁻¹ := by rw [hsd']
        _ = (s * u * s⁻¹) * (s * d * s⁻¹) * d⁻¹ := by group
        _ = u * (u * d) * d⁻¹ := by rw [hsu, hsd']
        _ = u * u := by group
        _ = 1 := by
          rw [hu]
          have hcomm : ∀ a ∈ Z.D, ∀ b ∈ Z.D, a * b = b * a :=
            fun a ha b hb => congrArg Subtype.val
              (Z.dataD.isMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
          have h2 := ((mem_omegaIn_iff_of_comm hcomm).mp huOmega).2
          simpa [pow_two] using h2
    have h3 : (s * s) * d * (s * s)⁻¹ = d := by
      have h4 := congrArg (· * d) hsq
      simpa [mul_assoc] using h4
    have h5 : (s * s) * d = d * (s * s) := by
      have h6 := congrArg (· * (s * s)) h3
      simpa [mul_assoc] using h6
    exact h5.symm
  exact Z.centralizerIn_eq ▸ (show s * s ∈ Z.centralizerIn from ⟨X.S.mul_mem hsS hsS, hs2cent⟩)

end CFSG.CGT.Stroth77
