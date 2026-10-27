module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CNilp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3b
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4S3

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

namespace Data

variable {H₁ : h.L81Hyp} (d : Data H₁)

theorem dihData_P {v : H} (hst : d.Stage7 v) : Nine81.DihData h.P d.p d.b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbP : d.b ∈ h.P := (h.B_le (d.B_eq ▸ mem_zpowers d.b : d.b ∈ h.B))
  have hP2 : IsPGroup 2 h.P := h.isPGroup_S.to_le inf_le_left
  have hp4 : 4 ≤ orderOf d.p := by
    have h1 := d.card_P
    have h2 := H₁.eight_le
    omega
  refine
    { hp := d.p_mem
      hb := hbP
      hcard := d.card_P
      hbp := ?_
      hb2 := by rw [← pow_two, ← d.b_ord, pow_orderOf_eq_one]
      hrel := hst.dihedral
      hp4 := hp4
      hpow := ?_ }
  · intro hb
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
    have h1 := hst.dihedral
    rw [← hk, show d.p ^ k * d.p * (d.p ^ k)⁻¹ = d.p by group] at h1
    have h2 : d.p ^ 2 = 1 := by
      calc d.p ^ 2 = d.p * d.p := pow_two _
        _ = d.p * d.p⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel _
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨d.p, d.p_mem⟩
    exact ⟨n, by rw [← Subgroup.orderOf_mk d.p d.p_mem]; exact hn⟩

theorem comm_of_odd_of_le_Y9 {v : H} (hst : d.Stage7 v) {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    (hQY : Q ≤ Y9 h) {y : H} (hya : y * h.a = h.a * y) (ho : Odd (orderOf y))
    (hyN : y ∈ normalizer (Q : Set H)) {x : H} (hx : x ∈ Q) : y * x * y⁻¹ = x := by
  have D := d.dihData_P hst
  obtain ⟨g, hgY, hgQ⟩ := exists_conjugate_le_of_sylow (P_sylow_Y9 H₁) hQY hQ
  have hga : g * h.a = h.a * g := mem_centralizer_singleton_iff.mp (mem_inf.mp hgY).1
  have hy'N : g⁻¹ * y * g ∈ normalizer ((conjugate Q g : Subgroup H) : Set H) := by
    rw [mem_normalizer_iff]
    intro w
    rw [mem_conjugate_iff, mem_conjugate_iff,
      show g * (g⁻¹ * y * g * w * (g⁻¹ * y * g)⁻¹) * g⁻¹ = y * (g * w * g⁻¹) * y⁻¹ by group]
    exact mem_normalizer_iff.mp hyN _
  have hy'o : Odd (orderOf (g⁻¹ * y * g)) := by
    rwa [← SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * y = g⁻¹ * y * g * g⁻¹ by group)]
  have hpa : d.p ^ (orderOf d.p / 2) = h.a := d.p_a
  have hy'a : g⁻¹ * y * g * d.p ^ (orderOf d.p / 2) = d.p ^ (orderOf d.p / 2) * (g⁻¹ * y * g) := by
    rw [hpa]
    have hga' : g⁻¹ * h.a = h.a * g⁻¹ := by
      calc g⁻¹ * h.a = g⁻¹ * (h.a * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * h.a) * g⁻¹ := by rw [hga]
        _ = h.a * g⁻¹ := by group
    calc g⁻¹ * y * g * h.a = g⁻¹ * y * (h.a * g) := by rw [mul_assoc, hga]
      _ = g⁻¹ * (y * h.a) * g := by group
      _ = g⁻¹ * (h.a * y) * g := by rw [hya]
      _ = (g⁻¹ * h.a) * y * g := by group
      _ = h.a * (g⁻¹ * y * g) := by rw [hga']; group
  have hx' : g⁻¹ * x * g ∈ conjugate Q g := by
    rw [mem_conjugate_iff, show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    exact hx
  have h1 := D.comm_of_odd_of_le hgQ hy'N hy'o hy'a hx'
  calc y * x * y⁻¹ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g) * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    _ = x := by rw [h1]; group

theorem hasNormalPComplement_centralizer_a_az {v : H} (hst : d.Stage7 v) :
    HasNormalPComplement 2
      ↥(centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := centralizer ({h.a} : Set H) ⊓ centralizer ({h.a * d.z} : Set H) with hW
  have hWN : W ≤ normalizer (h.J : Set H) := inf_le_left.trans H₁.centralizer_le_normalizer_J
  have : Finite (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J)) :=
    Finite.of_injective (fun σ : MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J) =>
      (σ : ↥h.J ⧸ pPrimeCore 2 ↥h.J → ↥h.J ⧸ pPrimeCore 2 ↥h.J))
      (fun σ τ hστ => MulEquiv.ext (congrFun hστ))
  set φ : ↥W →* MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J) :=
    (Eight.oddBarAction h.J).comp (inclusion hWN) with hφ
  have hφρ : ∀ w : ↥W, φ w = rhoE h.J (w : H) := fun w => (rhoE_of_mem (hWN w.2)).symm
  have hzN : d.z ∈ normalizer (h.J : Set H) := le_normalizer d.z_mem_J
  obtain ⟨p', f', hp', hp2', hf', hJL⟩ := H₁.exists_lieModel_J_sq
  have hΓ := CatFactsL4U4.Cat81.cent2Nilp_body _ p' f' hp' hp2' hf' hJL _ d.orderOf_zbar
  rw [← rhoE_of_mem_J d.z_mem_J] at hΓ
  have hφC : ∀ w : ↥W,
      φ w ∈ centralizer ({rhoE h.J d.z} : Set (MulAut (↥h.J ⧸ pPrimeCore 2 ↥h.J))) := by
    intro w
    have h1 := d.comm_z_of_mem_W w.2
    have h2 : rhoE h.J ((w : H) * d.z) = rhoE h.J (d.z * (w : H)) := by rw [h1]
    rw [rhoE_mul (hWN w.2) hzN, rhoE_mul hzN (hWN w.2)] at h2
    rw [mem_centralizer_singleton_iff, hφρ]
    exact h2
  refine X10CNilp.hasNormalPComplement_of_ker φ hφC hΓ ?_
  intro y hyo Q₀ hQ₀ hQ₀K hyN x hx
  have hQ : IsPGroup 2 (Q₀.map W.subtype) := hQ₀.map _
  have hQY : Q₀.map W.subtype ≤ Y9 h := by
    rintro _ ⟨w, hw, rfl⟩
    refine mem_inf.mpr ⟨(mem_inf.mp w.2).1, (rhoE_eq_one_iff (hWN w.2)).mp ?_⟩
    rw [← hφρ]
    exact hQ₀K hw
  have hya : (y : H) * h.a = h.a * (y : H) := mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).1
  have hyo' : Odd (orderOf (y : H)) := by rwa [Subgroup.orderOf_coe]
  have hyN' : (y : H) ∈ normalizer ((Q₀.map W.subtype : Subgroup H) : Set H) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨y * u * y⁻¹, (mem_normalizer_iff.mp hyN u).mp hu, rfl⟩
    · rintro ⟨u, hu, hue⟩
      have hu' : y⁻¹ * u * y ∈ Q₀ := by
        have := (mem_normalizer_iff.mp (inv_mem hyN) u).mp hu
        rwa [inv_inv] at this
      refine ⟨y⁻¹ * u * y, hu', ?_⟩
      have hue' : (u : H) = (y : H) * w * (y : H)⁻¹ := hue
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hue']
      group
  have h1 := d.comm_of_odd_of_le_Y9 hst hQ hQY hya hyo' hyN' ⟨x, hx, rfl⟩
  exact Subtype.ext h1

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
