module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.InvertedAbelian
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin

variable {W : Type} [CommGroup W] [Finite W]

theorem card_fixV_sq_le_of_inverts_fpf {z t : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hinv : t * z * t⁻¹ = z⁻¹) :
    Nat.card (fixV (Subgroup.zpowers t)) * Nat.card (fixV (Subgroup.zpowers t)) ≤ Nat.card W := by
  set C := fixV (Subgroup.zpowers t) with hC
  have htz : ∀ w : W, t (z w) = z⁻¹ (t w) := by
    intro w
    have h1 : t * z = z⁻¹ * t := by
      have := congrArg (· * t) hinv
      simpa [mul_assoc] using this
    exact congrArg (fun f : MulAut W => f w) h1
  have hz2 : ∀ c : W, z (z (z c)) = c := by
    intro c
    have := congrArg (fun f : MulAut W => f c) hz3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hmemC : ∀ c : W, c ∈ C ↔ t c = c := fun c => mem_fixV_zpowers_iff
  let f : ↥C × ↥C → W := fun p => (p.1 : W) * z (p.2 : W)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f] at h
    have hc : ((b' : W) / (b : W)) ∈ C := C.div_mem b'.2 b.2
    have hd : ((a : W) / (a' : W)) ∈ C := C.div_mem a.2 a'.2
    have hdz : (a : W) / (a' : W) = z ((b' : W) / (b : W)) := by
      rw [map_div, div_eq_div_iff_mul_eq_mul]
      rw [mul_comm (z (b' : W)) (a' : W)]
      exact h
    set c : W := (b' : W) / (b : W) with hcdef
    have h1 : t c = c := (hmemC c).1 hc
    have h2 : t (z c) = z c := by rw [← hdz]; exact (hmemC _).1 hd
    rw [htz, h1] at h2
    have h3 : z (z c) = c := by
      have := congrArg z h2
      simpa using this.symm
    have h4 : z c = c := by
      have := hz2 c
      rwa [h3] at this
    have hc1 : c = 1 := hfpf c h4
    have hbb : (b' : W) = b := by
      rw [hcdef, div_eq_one] at hc1
      exact hc1
    have hdd : (a : W) = a' := by
      rw [hc1, map_one, div_eq_one] at hdz
      exact hdz
    exact Prod.ext (Subtype.ext hdd) (Subtype.ext hbb.symm)
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using this

theorem weight_lt_of_inverts_fpf {z t : MulAut W} (hz3 : z ^ 3 = 1)
    (hfpf : ∀ w : W, z w = w → w = 1) (hinv : t * z * t⁻¹ = z⁻¹) {E : Subgroup (MulAut W)}
    (htE : t ∈ E) (hE : Nat.card E ^ 2 < Nat.card W) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  apply QuasithinUnique.Setup.X1.weight_lt_of_lt_index
  have hsq := card_fixV_sq_le_of_inverts_fpf hz3 hfpf hinv
  have hmul := Subgroup.card_mul_index (fixV (Subgroup.zpowers t))
  have hpos : 0 < Nat.card (fixV (Subgroup.zpowers t)) := Nat.card_pos
  have h1 : Nat.card (fixV (Subgroup.zpowers t)) ≤ (fixV (Subgroup.zpowers t)).index := by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have := Nat.mul_lt_mul_of_pos_left hlt hpos
    omega
  have h2 : Nat.card W ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
    rw [← hmul, sq]
    exact Nat.mul_le_mul_right _ h1
  have h3 : Nat.card E < (fixV (Subgroup.zpowers t)).index :=
    lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) (lt_of_lt_of_le hE h2)
  exact h3.trans_le (Subgroup.index_antitone
    (QuasithinUnique.Setup.X1.fixV_anti ((Subgroup.zpowers_le).2 htE)))

open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 (binRep binModule binRep_injective)

theorem exists_card_mulAut_dvd (hW : ∀ w : W, w * w = 1) :
    ∃ n : ℕ, Nat.card W = 2 ^ n ∧ ∀ L : Subgroup (MulAut W),
      Nat.card L ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  let _ : Module (ZMod 2) (Additive W) := binModule (fun v => by rw [pow_two]; exact hW v)
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  refine ⟨Module.finrank (ZMod 2) (Additive W), ?_, ?_⟩
  · have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at this
    rw [← this]
    exact (Nat.card_congr (Additive.toMul : Additive W ≃ W)).symm
  · intro L
    set n := Module.finrank (ZMod 2) (Additive W)
    let φ : MulAut W →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) :=
      (binRep W).toHomUnits
    have hφ : Function.Injective φ := by
      intro a b h
      apply binRep_injective
      exact Units.ext_iff.1 h
    let e : Additive W ≃ₗ[ZMod 2] (Fin n → ZMod 2) := (Module.finBasis (ZMod 2) (Additive W)).equivFun
    let ψ : LinearMap.GeneralLinearGroup (ZMod 2) (Additive W) ≃*
        Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e).trans Matrix.GeneralLinearGroup.toLin.symm
    let χ : MulAut W →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) := ψ.toMonoidHom.comp φ
    have hinj : Function.Injective χ := ψ.injective.comp hφ
    have h1 : Nat.card L = Nat.card (L.map χ) :=
      Nat.card_congr (L.equivMapOfInjective _ hinj).toEquiv
    have hq := Matrix.card_GL_field (𝔽 := ZMod 2) n
    simp only [ZMod.card] at hq
    rw [h1, ← hq]
    exact Subgroup.card_subgroup_dvd_card _

theorem not_three_pow_seven_dvd_GL_two {n : ℕ} (hn : n ≤ 11) :
    ¬ 3 ^ 7 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> simp [Fin.prod_univ_succ]

theorem two_pow_twelve_le_card_of_three_pow_seven_dvd (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (hL : 3 ^ 7 ∣ Nat.card L) : 2 ^ 12 ≤ Nat.card W := by
  obtain ⟨n, hn, hdvd⟩ := exists_card_mulAut_dvd (W := W) hW
  rw [hn]
  have : 12 ≤ n := by
    by_contra hlt
    exact not_three_pow_seven_dvd_GL_two (by omega) (hL.trans (hdvd L))
  exact Nat.pow_le_pow_right (by norm_num) this

theorem weight_lt_of_inverts_fpf_of_three_pow_seven_dvd (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hL : 3 ^ 7 ∣ Nat.card L) (hE : Nat.card E ≤ 2 ^ 5)
    {z t : MulAut W} (hz3 : z ^ 3 = 1) (hfpf : ∀ w : W, z w = w → w = 1)
    (hinv : t * z * t⁻¹ = z⁻¹) (htE : t ∈ E) : Nat.card E * Nat.card (fixV E) < Nat.card W := by
  refine weight_lt_of_inverts_fpf hz3 hfpf hinv htE ?_
  have h12 := two_pow_twelve_le_card_of_three_pow_seven_dvd hW hL
  have : Nat.card E ^ 2 ≤ (2 ^ 5) ^ 2 := Nat.pow_le_pow_left hE 2
  omega

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
