module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13EV1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E64e

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

namespace IsRs

variable {c}

theorem not_conj_z_of_even {Rs : Subgroup G} (hR : c.IsRs Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hD1 : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range → π a = π b)
    (hE64 : c.OE64Statement)
    (hrank : ∀ {u : G}, (∃ g : G, u = g * z * g⁻¹) → ∀ {A : Subgroup G},
      A ≤ centralizer ({u} : Set G) → (∀ a ∈ A, a * a = 1) → Nat.card ↥A ≤ 32)
    {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1) (hyQ : y ∉ c.Qs)
    (hev : Equiv.Perm.sign (π (c.rho ⟨y, hy.2⟩).1) = 1) (hyz : ∃ g : G, y = g * z * g⁻¹) :
    False := by
  classical
  have hyN : y ∈ c.N1 := hy.2
  have hmem : ((c.rho ⟨y, hyN⟩).1, (c.rho ⟨y, hyN⟩).2) ∈ c.rho.range :=
    MonoidHom.mem_range.2 ⟨⟨y, hyN⟩, rfl⟩
  have hDD : π (c.rho ⟨y, hyN⟩).1 = π (c.rho ⟨y, hyN⟩).2 := hD1 _ _ hmem
  have hψsq : c.rho ⟨y, hyN⟩ * c.rho ⟨y, hyN⟩ = 1 := by
    rw [← map_mul, ← map_one c.rho]
    congr 1
    exact Subtype.ext hy2
  have hd1' : π (c.rho ⟨y, hyN⟩).1 ≠ 1 := by
    intro hd
    obtain ⟨e₁, he₁⟩ := (hπ.ker _).1 hd
    obtain ⟨e₂, he₂⟩ := (hπ.ker _).1 (hDD.symm.trans hd)
    obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs e₁ e₂
    have hρeq : c.rho ⟨q, c.Qs_le_N1 hq⟩ = c.rho ⟨y, hyN⟩ := by
      rw [hρq]
      exact Prod.ext he₁ he₂
    have hkN : q⁻¹ * y ∈ c.N1 := mul_mem (inv_mem (c.Qs_le_N1 hq)) hyN
    have hk1 : c.rho ⟨q⁻¹ * y, hkN⟩ = 1 := by
      show c.rho ((⟨q, c.Qs_le_N1 hq⟩ : ↥c.N1)⁻¹ * ⟨y, hyN⟩) = 1
      rw [map_mul, map_inv, hρeq, inv_mul_cancel]
    have hkK : q⁻¹ * y ∈ c.KR := c.mem_KR.2 ⟨hkN, hk1⟩
    have hqR : q ∈ Rs := hR.Qs_le hq
    have hkRS : q⁻¹ * y ∈ Rs ⊓ c.N1 := ⟨Rs.mul_mem (Rs.inv_mem hqR) hy.1, hkN⟩
    have hkZ : q⁻¹ * y ∈ c.Zs := hR.R_inf_KR_le ⟨hkRS, hkK⟩
    apply hyQ
    have := mul_mem hq (c.Zs_le_Qs hkZ)
    simpa using this
  obtain ⟨d, hd⟩ : ∃ d, π (c.rho ⟨y, hyN⟩).1 = d := ⟨_, rfl⟩
  have hdA : Equiv.Perm.sign d = 1 := by
    rw [← hd]
    exact hev
  have hd1 : d ≠ 1 := by
    rw [← hd]
    exact hd1'
  have hd2 : d * d = 1 := by
    have h := congrArg Prod.fst hψsq
    rw [Prod.fst_mul, Prod.fst_one] at h
    rw [← hd, ← map_mul, h, map_one]
  obtain ⟨b₁, b₂, hb₁, hb₂, h11, h22, h12, h1, h2, h3, hκ₁⟩ :=
    c.exists_klein_pi hπ hdA hd2 hd1
  have hA1 : π ((c.rho ⟨y, hyN⟩).1 * (c.kappa ⟨b₁, hb₁⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, hd, hκ₁, mul_inv_cancel]
  have hA2 : π ((c.rho ⟨y, hyN⟩).2 * (c.kappa ⟨b₁, hb₁⟩)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hDD, hd, hκ₁, mul_inv_cancel]
  obtain ⟨e₃, he₃⟩ := (hπ.ker _).1 hA1
  obtain ⟨e₄, he₄⟩ := (hπ.ker _).1 hA2
  have hψ1 : (c.rho ⟨y, hyN⟩).1 = MulAut.conj e₃ * c.kappa ⟨b₁, hb₁⟩ := by
    rw [he₃]
    group
  have hψ2 : (c.rho ⟨y, hyN⟩).2 = MulAut.conj e₄ * c.kappa ⟨b₁, hb₁⟩ := by
    rw [he₄]
    group
  obtain ⟨q, hq, hρq⟩ := c.exists_rho_Qs e₃ e₄
  have hqbN : q * b₁ ∈ c.N1 := mul_mem (c.Qs_le_N1 hq) (c.B_le_N1 hb₁)
  have hqbS : q * b₁ ∈ c.QB1 b₁ b₂ :=
    mul_mem (c.Qs_le_QB1 hq) (c.B1_le_QB1 (mem_sup_left (mem_zpowers b₁)))
  have hρb₁ : c.rho ⟨b₁, c.B_le_N1 hb₁⟩ = (c.kappa ⟨b₁, hb₁⟩, c.kappa ⟨b₁, hb₁⟩) :=
    c.rho_B ⟨b₁, hb₁⟩
  have hval : c.rho ⟨q * b₁, hqbN⟩ = c.rho ⟨y, hyN⟩ := by
    have e : (⟨q * b₁, hqbN⟩ : ↥c.N1) = ⟨q, c.Qs_le_N1 hq⟩ * ⟨b₁, c.B_le_N1 hb₁⟩ := rfl
    rw [e, map_mul, hρq, hρb₁]
    exact Prod.ext hψ1.symm hψ2.symm
  have hyTh : c.rho ⟨y, hyN⟩ ∈ c.Rhat (c.QB1 b₁ b₂) :=
    c.mem_Rhat.2 ⟨⟨q * b₁, hqbN⟩, hqbS, hval⟩
  have hyT : y ∈ c.ThetaS (c.QB1 b₁ b₂) := c.mem_ThetaS.2 ⟨hyN, hyTh⟩
  have hSN : c.QB1 b₁ b₂ ≤ c.N1 := c.QB1_le_N1 hb₁ hb₂
  have hSp : IsPGroup 2 (c.QB1 b₁ b₂) := c.QB1_pgroup hb₁ hb₂ h11 h22 h12
  have hSΘ : c.QB1 b₁ b₂ ≤ c.ThetaS (c.QB1 b₁ b₂) := c.le_ThetaS hSN
  have hSmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ c.ThetaS (c.QB1 b₁ b₂) →
      c.QB1 b₁ b₂ ≤ P → P ≤ c.QB1 b₁ b₂ :=
    fun P hP hPT hSP => hR.ThetaS_max c.Zs_le_QB1 hP hPT hSP
  have hz : IsPGroup 2 (zpowers y) := by
    have hord : orderOf y ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨M, ⟨hM2, hMΘ, hyM⟩, hMmax⟩ :=
    (Set.toFinite {M : Subgroup G | IsPGroup 2 M ∧ M ≤ c.ThetaS (c.QB1 b₁ b₂) ∧
      zpowers y ≤ M}).exists_maximalFor id _
      ⟨zpowers y, hz, zpowers_le.2 hyT, le_rfl⟩
  have hMmax' : ∀ M' : Subgroup G, IsPGroup 2 M' → M' ≤ c.ThetaS (c.QB1 b₁ b₂) → M ≤ M' →
      M' ≤ M :=
    fun M' hM' hM'Θ hMM' => hMmax ⟨hM', hM'Θ, hyM.trans hMM'⟩ hMM'
  obtain ⟨g, hgΘ, hg⟩ := sylow_conj hSΘ hMΘ hSp hM2 hSmax hMmax'
  have hy' : g⁻¹ * y * g ∈ c.QB1 b₁ b₂ := (hg y).1 (hyM (mem_zpowers y))
  have hgN : g ∈ c.N1 := c.ThetaS_le_N1 hgΘ
  have hy'N : g⁻¹ * y * g ∈ c.N1 := mul_mem (mul_mem (inv_mem hgN) hyN) hgN
  have hy'2 : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    calc (g⁻¹ * y * g) * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
      _ = 1 := by rw [hy2]; group
  have hy'z : ∃ k : G, g⁻¹ * y * g = k * z * k⁻¹ := by
    obtain ⟨g0, hg0⟩ := hyz
    exact ⟨g⁻¹ * g0, by rw [hg0]; group⟩
  have hy'Q : g⁻¹ * y * g ∉ c.Qs := by
    intro hq'
    obtain ⟨e₅, e₆, h56⟩ := c.rho_Qs_mem hq'
    have hπ5 : π (c.rho ⟨g⁻¹ * y * g, c.Qs_le_N1 hq'⟩).1 = 1 := by
      rw [h56]
      show π (MulAut.conj e₅) = 1
      exact (hπ.ker _).2 ⟨e₅, rfl⟩
    have hfst : (c.rho ⟨g⁻¹ * y * g, hy'N⟩).1 =
        ((c.rho ⟨g, hgN⟩).1)⁻¹ * (c.rho ⟨y, hyN⟩).1 * (c.rho ⟨g, hgN⟩).1 := by
      have e : (⟨g⁻¹ * y * g, hy'N⟩ : ↥c.N1) =
          (⟨g, hgN⟩ : ↥c.N1)⁻¹ * ⟨y, hyN⟩ * ⟨g, hgN⟩ := rfl
      rw [e, map_mul, map_mul, map_inv]
      rfl
    have hπ5' : π (((c.rho ⟨g, hgN⟩).1)⁻¹ * (c.rho ⟨y, hyN⟩).1 * (c.rho ⟨g, hgN⟩).1) = 1 := by
      rw [← hfst]
      exact hπ5
    rw [map_mul, map_mul, map_inv, hd] at hπ5'
    apply hd1
    calc d = π (c.rho ⟨g, hgN⟩).1 * ((π (c.rho ⟨g, hgN⟩).1)⁻¹ * d * π (c.rho ⟨g, hgN⟩).1) *
          (π (c.rho ⟨g, hgN⟩).1)⁻¹ := by group
      _ = 1 := by rw [hπ5']; group
  obtain ⟨q0, hq0, b, hb, hx'⟩ := c.mem_QB1 hb₁ hb₂ h11 h22 h12 hy'
  have hb' : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂ := by
    rcases hb with h | h | h | h
    · exfalso
      apply hy'Q
      rw [hx', h, mul_one]
      exact hq0
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hsq' : (q0 * b) * (q0 * b) = 1 := by
    rw [← hx']
    exact hy'2
  have hconj : ∃ k : G, q0 * b = k * z * k⁻¹ := by
    rw [← hx']
    exact hy'z
  obtain ⟨A, hAc, hA2', hA64⟩ := hE64 hb₁ hb₂ h11 h22 h12 h1 h2 h3 hq0 hb' hsq'
  have hA32 := hrank hconj hAc hA2'
  omega

end IsRs

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
