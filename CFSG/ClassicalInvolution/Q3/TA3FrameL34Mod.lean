module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Cert

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.ComponentClassification.PSL3Four
open scoped Pointwise

namespace L34


theorem conj_r₁ {t : Equiv.Perm (Fin 42)} (ht : t ∈ S) (ht2 : orderOf t = 2) :
    ∃ k ∈ R, k * t * k⁻¹ = r₁ := by
  obtain ⟨-, -, hSR, -, -, hord, -, -, -, -, -, -, hnot, -⟩ := involution_enumeration
  have h2 : orderOf (⟨t, hSR ht⟩ : R) = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  rcases (hord _).1 h2 with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    exact ⟨c, c.2, congrArg Subtype.val hc⟩
  · exact absurd ht (hnot _ h)

theorem card_le_conj {t k : Equiv.Perm (Fin 42)} (hk : k ∈ R) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 42)))) ≤
      Nat.card ↥(S ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set (Equiv.Perm (Fin 42)))) := by
  rw [← Subgroup.card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective]
  refine Subgroup.card_le_of_le ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hwS, hwt⟩ := Subgroup.mem_inf.mp hw
  refine Subgroup.mem_inf.mpr ⟨conj_mem_S hk hwS, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hwt ⊢
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc k * w * k⁻¹ * (k * t * k⁻¹) = k * (w * t) * k⁻¹ := by group
    _ = k * (t * w) * k⁻¹ := by rw [hwt]
    _ = k * t * k⁻¹ * (k * w * k⁻¹) := by group

theorem card_centralizer {t : Equiv.Perm (Fin 42)} (ht : t ∈ S) (ht2 : orderOf t = 2) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 42)))) = 64 := by
  obtain ⟨k, hk, hkt⟩ := conj_r₁ ht ht2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hC₁, -⟩ := involution_enumeration
  have hC : Nat.card ↥(S ⊓ Subgroup.centralizer ({r₁} : Set (Equiv.Perm (Fin 42)))) = 64 := by
    rw [← hC₁, C₁, inf_comm]
  have h1 := card_le_conj (t := t) hk
  have h2 := card_le_conj (t := r₁) (R.inv_mem hk)
  rw [hkt] at h1
  have e : k⁻¹ * r₁ * k⁻¹⁻¹ = t := by rw [← hkt]; group
  rw [e] at h2
  omega

theorem card_centralizer_r₁R : Nat.card (Subgroup.centralizer ({r₁R} : Set R)) = 768 := by
  obtain ⟨-, hR, -, -, -, -, -, h315, -⟩ := involution_enumeration
  have e2 := Subgroup.card_mul_index (MulAction.stabilizer (ConjAct R) r₁R)
  rw [MulAction.index_stabilizer, ConjAct.orbit_eq_carrier_conjClasses, ← Nat.card_coe_set_eq,
    h315, ← Nat.card_congr (ConjAct.toConjAct : R ≃* ConjAct R).toEquiv, hR,
    ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at e2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 315) (e2.trans (by norm_num))

theorem card_le_four {s r : Equiv.Perm (Fin 42)} (hs : s ∈ S) (hs2 : orderOf s = 2) (hr : r ∈ R)
    (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1) (hrs : r * s = s * r) {W : Subgroup (Equiv.Perm (Fin 42))}
    (hWS : W ≤ S) (hW2 : IsPGroup 2 W) (hWr : ∀ w ∈ W, w * r = r * w) : Nat.card W ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC₃, -⟩ := involution_enumeration
  obtain ⟨z₀, hz₀⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.l34Facts
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := C₃) 2 (by rw [hC₃]; norm_num)
  have hdS : (d : Equiv.Perm (Fin 42)) ∈ S := (Subgroup.mem_inf.mp d.2).2
  have hd2 : orderOf (d : Equiv.Perm (Fin 42)) = 2 := by rw [Subgroup.orderOf_coe]; exact hd
  have hdz : (d : Equiv.Perm (Fin 42)) * z₀ = z₀ * d := hz₀.z_comm d d.2
  obtain ⟨k₁, hk₁R, hk₁⟩ := conj_r₁ hs hs2
  obtain ⟨k₂, hk₂R, hk₂⟩ := conj_r₁ hdS hd2
  have hr'R : k₁ * r * k₁⁻¹ ∈ R := R.mul_mem (R.mul_mem hk₁R hr) (R.inv_mem hk₁R)
  have hz'R : k₂ * z₀ * k₂⁻¹ ∈ R := R.mul_mem (R.mul_mem hk₂R hz₀.z_mem) (R.inv_mem hk₂R)
  have hca : (⟨_, hr'R⟩ : R) ∈ Subgroup.centralizer ({r₁R} : Set R) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    change k₁ * r * k₁⁻¹ * r₁ = r₁ * (k₁ * r * k₁⁻¹)
    rw [← hk₁]
    calc k₁ * r * k₁⁻¹ * (k₁ * s * k₁⁻¹) = k₁ * (r * s) * k₁⁻¹ := by group
      _ = k₁ * (s * r) * k₁⁻¹ := by rw [hrs]
      _ = k₁ * s * k₁⁻¹ * (k₁ * r * k₁⁻¹) := by group
  have hcb : (⟨_, hz'R⟩ : R) ∈ Subgroup.centralizer ({r₁R} : Set R) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    refine Subtype.ext ?_
    change k₂ * z₀ * k₂⁻¹ * r₁ = r₁ * (k₂ * z₀ * k₂⁻¹)
    rw [← hk₂]
    calc k₂ * z₀ * k₂⁻¹ * (k₂ * d * k₂⁻¹) = k₂ * (z₀ * d) * k₂⁻¹ := by group
      _ = k₂ * (d * z₀) * k₂⁻¹ := by rw [hdz]
      _ = k₂ * d * k₂⁻¹ * (k₂ * z₀ * k₂⁻¹) := by group
  set H := Subgroup.centralizer ({r₁R} : Set R) with hH
  set a : H := ⟨⟨_, hr'R⟩, hca⟩ with ha
  set b : H := ⟨⟨_, hz'R⟩, hcb⟩ with hb
  have ha3 : orderOf a = 3 := by
    rw [ha, Subgroup.orderOf_mk, Subgroup.orderOf_mk,
      show k₁ * r * k₁⁻¹ = MulAut.conj k₁ r from rfl, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hr3 hr1
  have hb3 : orderOf b = 3 := by
    rw [hb, Subgroup.orderOf_mk, Subgroup.orderOf_mk,
      show k₂ * z₀ * k₂⁻¹ = MulAut.conj k₂ z₀ from rfl, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hz₀.z_cube hz₀.z_ne
  have hsyl : ∀ x : H, orderOf x = 3 → ¬ 3 ∣ (Subgroup.zpowers x).index := by
    intro x hx
    have e := Subgroup.card_mul_index (Subgroup.zpowers x)
    have hHc : Nat.card H = 768 := card_centralizer_r₁R
    rw [Nat.card_zpowers, hx, hHc] at e
    omega
  have hp : ∀ x : H, orderOf x = 3 → IsPGroup 3 (Subgroup.zpowers x) := fun x hx =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  set PA := (hp a ha3).toSylow (hsyl a ha3) with hPA
  set PB := (hp b hb3).toSylow (hsyl b hb3) with hPB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H PB PA
  have h1 : MulAut.conj g • b ∈ MulAut.conj g • (PB : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul b _ _ (show b ∈ (PB : Subgroup H) from Subgroup.mem_zpowers b)
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  obtain ⟨j, hj⟩ :=
    Subgroup.mem_zpowers_iff.mp (show MulAut.conj g • b ∈ Subgroup.zpowers a from h1)
  have hj' : (k₁ * r * k₁⁻¹) ^ j = ((g : R) : Equiv.Perm (Fin 42)) * (k₂ * z₀ * k₂⁻¹) *
      ((g : R) : Equiv.Perm (Fin 42))⁻¹ := by
    have := congrArg (fun x : H => ((x : R) : Equiv.Perm (Fin 42))) hj
    simpa [ha, hb] using this
  set n := ((g : R) : Equiv.Perm (Fin 42)) * k₂ with hn
  have hnR : n ∈ R := R.mul_mem (g : R).2 hk₂R
  have hle : W.map (MulAut.conj (n⁻¹ * k₁)).toMonoidHom ≤ C₃ := by
    rintro _ ⟨w, hw, rfl⟩
    have hmR : n⁻¹ * k₁ ∈ R := R.mul_mem (R.inv_mem hnR) hk₁R
    have hwS : (MulAut.conj (n⁻¹ * k₁)).toMonoidHom w ∈ S := conj_mem_S hmR (hWS hw)
    have hx : Commute (k₁ * w * k₁⁻¹) (k₁ * r * k₁⁻¹) := by
      change k₁ * w * k₁⁻¹ * (k₁ * r * k₁⁻¹) = k₁ * r * k₁⁻¹ * (k₁ * w * k₁⁻¹)
      calc k₁ * w * k₁⁻¹ * (k₁ * r * k₁⁻¹) = k₁ * (w * r) * k₁⁻¹ := by group
        _ = k₁ * (r * w) * k₁⁻¹ := by rw [hWr w hw]
        _ = k₁ * r * k₁⁻¹ * (k₁ * w * k₁⁻¹) := by group
    have hxj := (hx.zpow_right j).eq
    rw [hj'] at hxj
    have hcz : (MulAut.conj (n⁻¹ * k₁)).toMonoidHom w * z₀ =
        z₀ * (MulAut.conj (n⁻¹ * k₁)).toMonoidHom w := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hn]
      calc (((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ * k₁ * w *
            ((((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ * k₁)⁻¹ * z₀ =
          (((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ * ((k₁ * w * k₁⁻¹) *
            (((g : R) : Equiv.Perm (Fin 42)) * (k₂ * z₀ * k₂⁻¹) *
              ((g : R) : Equiv.Perm (Fin 42))⁻¹)) * (((g : R) : Equiv.Perm (Fin 42)) * k₂) := by
            group
        _ = (((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ *
            ((((g : R) : Equiv.Perm (Fin 42)) * (k₂ * z₀ * k₂⁻¹) *
              ((g : R) : Equiv.Perm (Fin 42))⁻¹) * (k₁ * w * k₁⁻¹)) *
                (((g : R) : Equiv.Perm (Fin 42)) * k₂) := by rw [hxj]
        _ = z₀ * ((((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ * k₁ * w *
            ((((g : R) : Equiv.Perm (Fin 42)) * k₂)⁻¹ * k₁)⁻¹) := by group
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hz₀.cent_le _ hwS hcz), hwS⟩
  have hcard := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (f := (MulAut.conj (n⁻¹ * k₁)).toMonoidHom)
    (MulAut.conj _).injective, hC₃] at hcard
  obtain ⟨m, hm⟩ := hW2.exists_card_eq
  rw [hm] at hcard ⊢
  have hm2 : m ≤ 2 := by
    by_contra h
    push Not at h
    have h8 : 2 ^ 3 ∣ 60 := (Nat.pow_dvd_pow 2 h).trans hcard
    norm_num at h8
  calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 4 := by norm_num

end L34

end CFSG.ClassicalInvolution.Q3.TA3.Frame
