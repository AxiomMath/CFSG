module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fE24
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS.Th2.P43f

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.Th2 Equiv Equiv.Perm
  CFSG.LieType.SteinbergBR.SmallAlt

variable {G : Type} [Group G] {x : G} {K T S : Subgroup G} {a z : G} {psi : G → Perm (Fin 7)}

omit [Group G] in
theorem mem_normalizer_of_map_le {G : Type} [Group G] [Finite G] {H : Subgroup G} {n : G}
    (h : ∀ h ∈ H, n * h * n⁻¹ ∈ H) : n ∈ normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj n).toMonoidHom ≤ H := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using h y hy
  have hcard : Nat.card ↥(H.map (MulAut.conj n).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have heq : H.map (MulAut.conj n).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact h y hy
  · intro hy
    have : n * y * n⁻¹ ∈ H.map (MulAut.conj n).toMonoidHom := by rw [heq]; exact hy
    obtain ⟨w, hw, hwe⟩ := this
    have : w = y := by
      have h1 : n * w * n⁻¹ = n * y * n⁻¹ := by simpa [MulAut.conj_apply] using hwe
      exact mul_left_cancel (mul_right_cancel h1)
    rw [← this]
    exact hw

omit [Group G] in
theorem mem_sup_mul_of_le_normalizer {G : Type} [Group G] {S X : Subgroup G}
    (h : S ≤ normalizer (X : Set G)) {g : G} (hg : g ∈ S ⊔ X) : ∃ s ∈ S, ∃ t ∈ X, g = s * t := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right S X h] at hg
  obtain ⟨s, hs, t, ht, rfl⟩ := Set.mem_mul.1 hg
  exact ⟨s, hs, t, ht, rfl⟩

theorem a7P_rho' {g : Perm (Fin 7)} (hg : (g = a7P 2 ∨ g = a7P 3) ∨ (g = a7P 6 ∨ g = a7P 7)) :
    ∃ ρ : Perm (Fin 7), sign ρ = 1 ∧ ρ * a7P 1 * ρ⁻¹ = g ∧ ρ * g * ρ⁻¹ = a7P 1 * g := by
  rcases hg with (rfl | rfl) | (rfl | rfl)
  · exact a7P_rho (Or.inl rfl)
  · exact a7P_rho (Or.inr (Or.inl rfl))
  · exact a7P_rho (Or.inr (Or.inr (Or.inl rfl)))
  · exact a7P_rho (Or.inr (Or.inr (Or.inr rfl)))

namespace Frame

variable (F : Frame x K T S a z psi)

include F

theorem mem_normalizer_Y {c : G} (hc : c ∈ centralizer ({x} : Set G)) :
    c ∈ normalizer (pPrimeCoreOf 2 K : Set G) := by
  have h1 : c ∈ normalizer (K : Set G) := by
    refine mem_normalizer_of_two_sided (fun k hk => F.K_norm c hc k hk) (fun k hk => ?_)
    have := F.K_norm c⁻¹ ((centralizer ({x} : Set G)).inv_mem hc) k hk
    simpa using this
  exact TwoThin.mem_normalizer_pPrimeCoreOf h1

theorem isSylowOf_sup_Y [Finite G] {B : Subgroup G} (hB : IsPGroup 2 ↥B)
    (hBC : B ≤ centralizer ({x} : Set G)) : IsSylowOf 2 B (B ⊔ pPrimeCoreOf 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBY : B ≤ normalizer (pPrimeCoreOf 2 K : Set G) := fun b hb => F.mem_normalizer_Y (hBC hb)
  have hinf : pPrimeCoreOf 2 K ⊓ B = ⊥ := by
    rw [inf_comm]
    exact C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hB
  have hfac := C3.Layer1.Back.Setup91.factorization_two_card_sup hBY
    (by rw [hinf, Subgroup.card_bot]; exact odd_one)
  have hY : (Nat.card ↥(pPrimeCoreOf 2 K)).factorization 2 = 0 :=
    C3.Layer1.Back.Setup91.factorization_two_of_odd (TwoThin.card_pPrimeCoreOf_odd K)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hB
  have hle : B ≤ B ⊔ pPrimeCoreOf 2 K := le_sup_left
  refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
  rw [sup_comm B (pPrimeCoreOf 2 K), hfac, hY, zero_add, hn,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem mul_inv_mem_Y [Finite G] {g₁ g₂ : G} (h₁ : g₁ ∈ K) (h₂ : g₂ ∈ K) (h : psi g₁ = psi g₂) :
    g₁ * g₂⁻¹ ∈ pPrimeCoreOf 2 K := by
  refine (F.psi_K_ker _ (K.mul_mem h₁ (K.inv_mem h₂))).1 ?_
  rw [F.psi_mul g₁ (F.K_le h₁) g₂⁻¹ ((centralizer ({x} : Set G)).inv_mem (F.K_le h₂)),
    F.psi_inv (F.K_le h₂), h, mul_inv_cancel]

theorem frat_lift [Finite G] {D : Subgroup G} (hD : IsFourSub (T ⊓ K) D)
    (hθ : ∀ w ∈ D, psi (a⁻¹ * w * a) = 1) {u : G} (hu : u ∈ D) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ n ∈ normalizer ((D ⊔ conjugate D a : Subgroup G) : Set G), n * z * n⁻¹ = u := by
  classical
  have hCC : (centralizer ({x} : Set G)) = centralizer ({x} : Set G) := rfl
  set B : Subgroup G := D ⊔ conjugate D a with hB
  set Y : Subgroup G := pPrimeCoreOf 2 K with hY
  have huP : u ∈ T ⊓ K := hD.1 hu
  have hu2 : u * u = 1 := (forall_of_isElementaryAbelian hD.2.1).2 u hu
  have hzD : z ∈ D := F.z_mem_four hD
  have hDel := F.four_eq hD hu hu1 huz
  have hzuD : z * u ∈ D := Subgroup.mul_mem _ hzD hu
  have huz' : u * u⁻¹ = 1 := mul_inv_cancel u
  obtain ⟨ρ, hρs, hρ1, hρ2⟩ : ∃ ρ : Perm (Fin 7), sign ρ = 1 ∧ ρ * psi z * ρ⁻¹ = psi u ∧
      ρ * psi u * ρ⁻¹ = psi (z * u) := by
    rw [F.psi_z, F.psi_zmul huP]
    obtain ⟨ρ, h1, h2, h3⟩ := a7P_rho' (F.nc_side huP hu2 hu1 huz)
    exact ⟨ρ, h1, h2, h3⟩
  obtain ⟨k, hk, hkρ⟩ := F.psi_surj ρ hρs
  have hkC : k ∈ centralizer ({x} : Set G) := F.K_le hk
  have hkinv : k⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem hkC
  have hconj : ∀ g ∈ centralizer ({x} : Set G), psi (k * g * k⁻¹) = ρ * psi g * ρ⁻¹ := by
    intro g hg
    rw [F.psi_mul (k * g) ((centralizer ({x} : Set G)).mul_mem hkC hg) k⁻¹ hkinv,
      F.psi_mul k hkC g hg, F.psi_inv hkC, hkρ]
  have hDP : ∀ d ∈ D, d ∈ T ⊓ K := fun d hd => hD.1 hd
  have hDC : ∀ d ∈ D, d ∈ centralizer ({x} : Set G) := fun d hd => F.P_le_C (hDP d hd)
  have hkdK : ∀ d ∈ D, k * d * k⁻¹ ∈ K := fun d hd => F.K_norm k hkC d (hDP d hd).2
  have hz_img : k * z * k⁻¹ * u⁻¹ ∈ Y :=
    F.mul_inv_mem_Y (hkdK z hzD) huP.2 (by rw [hconj z (hDC z hzD), hρ1])
  have hzu_eq : u * (z * u) = z := by
    calc u * (z * u) = (u * z) * u := by group
      _ = (z * u) * u := by rw [F.z_central u huP]
      _ = z * (u * u) := by group
      _ = z := by rw [hu2, mul_one]
  have hDimg : ∀ d ∈ D, ∃ d₂ ∈ D, k * d * k⁻¹ * d₂⁻¹ ∈ Y := by
    intro d hd
    rcases hDel d hd with h | h | h | h
    · refine ⟨1, one_mem _, ?_⟩
      rw [h]
      simp
    · exact ⟨u, hu, by rw [h]; exact hz_img⟩
    · exact ⟨z * u, hzuD, F.mul_inv_mem_Y (hkdK d hd) (hDP _ hzuD).2
        (by rw [hconj d (hDC d hd), h, hρ2])⟩
    · refine ⟨z, hzD, F.mul_inv_mem_Y (hkdK d hd) F.z_mem.2 ?_⟩
      have hpd : psi (z * u) = psi z * psi u := F.psi_mul z (F.P_le_C F.z_mem) u (hDC u hu)
      rw [hconj d (hDC d hd), h, hpd]
      calc ρ * (psi z * psi u) * ρ⁻¹ = (ρ * psi z * ρ⁻¹) * (ρ * psi u * ρ⁻¹) := by group
        _ = psi u * psi (z * u) := by rw [hρ1, hρ2]
        _ = psi (u * (z * u)) := (F.psi_mul u (hDC u hu) (z * u) (hDC _ hzuD)).symm
        _ = psi z := by rw [hzu_eq]
  have hDaP : ∀ q ∈ conjugate D a, q ∈ conjugate (T ⊓ K) a := fun q hq => by
    rw [mem_conjugate_iff'] at hq ⊢
    exact hD.1 hq
  have hqpsi : ∀ q ∈ conjugate D a, psi q = 1 := fun q hq => by
    have h1 : a * q * a⁻¹ ∈ D := mem_conjugate_iff'.1 hq
    have h2 := hθ _ h1
    have e : a⁻¹ * (a * q * a⁻¹) * a = q := by group
    rwa [e] at h2
  have hqC : ∀ q ∈ conjugate D a, q ∈ centralizer ({x} : Set G) := fun q hq =>
    F.T_le_C (F.core.conj_le F.core.P_le (hDaP q hq))
  have hQimg : ∀ q ∈ conjugate D a, k * q * k⁻¹ * q⁻¹ ∈ Y := by
    intro q hq
    have hqk : q * k⁻¹ * q⁻¹ ∈ K := F.K_norm q (hqC q hq) k⁻¹ (K.inv_mem hk)
    have hmem : k * q * k⁻¹ * q⁻¹ ∈ K := by
      have e : k * q * k⁻¹ * q⁻¹ = k * (q * k⁻¹ * q⁻¹) := by group
      rw [e]
      exact K.mul_mem hk hqk
    refine (F.psi_K_ker _ hmem).1 ?_
    have hqinv : q⁻¹ ∈ centralizer ({x} : Set G) := (centralizer ({x} : Set G)).inv_mem (hqC q hq)
    have hq1 := hqpsi q hq
    have hq1' : psi q⁻¹ = 1 := by rw [F.psi_inv (hqC q hq), hq1, inv_one]
    rw [F.psi_mul (k * q * k⁻¹) ((centralizer ({x} : Set G)).mul_mem
      ((centralizer ({x} : Set G)).mul_mem hkC (hqC q hq)) hkinv) q⁻¹ hqinv,
      hconj q (hqC q hq), hq1', hq1]
    group
  have hBC : B ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun d hd => hDC d hd) (fun q hq => hqC q hq)
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := by
    have hDa_el : CFSG.IsElementaryAbelian 2 ↥(conjugate D a) := isElementaryAbelian_conjugate hD.2.1 a
    exact isElementaryAbelian_sup_of_commute hD.2.1 hDa_el
      (fun d hd d' hd' => F.core.comm_P_conj d (hD.1 hd) d' (hDaP d' hd'))
  have hBp : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hkB : ∀ b ∈ B, k * b * k⁻¹ ∈ B ⊔ Y := by
    intro b hb
    obtain ⟨d, hd, q, hq, rfl⟩ :=
      CFSG.GH74.GLS.C3.Layer1.Bk.mem_sup_of_commute
        (fun d hd q hq => F.core.comm_P_conj d (hD.1 hd) q (hDaP q hq)) hb
    obtain ⟨d₂, hd₂, hy₁⟩ := hDimg d hd
    have e : k * (d * q) * k⁻¹ = (k * d * k⁻¹ * d₂⁻¹) * d₂ * ((k * q * k⁻¹ * q⁻¹) * q) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hy₁)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd₂))) (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (hQimg q hq)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right hq)))
  have hSyl := F.isSylowOf_sup_Y hBp hBC
  have hW : B.map (MulAut.conj k).toMonoidHom ≤ B ⊔ Y := by
    rintro _ ⟨b, hb, rfl⟩
    simpa [MulAut.conj_apply] using hkB b hb
  have hWp : IsPGroup 2 ↥(B.map (MulAut.conj k).toMonoidHom) := hBp.map _
  obtain ⟨g, hgBY, hgW⟩ := Th2.exists_cj_le_of_isSylowOf hSyl hW hWp
  have hn : ∀ b ∈ B, g * k * b * (g * k)⁻¹ ∈ B := by
    intro b hb
    have hmem : g * (k * b * k⁻¹) * g⁻¹ ∈ cj g (B.map (MulAut.conj k).toMonoidHom) :=
      ⟨k * b * k⁻¹, ⟨b, hb, rfl⟩, by simp [MulAut.conj_apply]⟩
    have := hgW hmem
    have e : g * k * b * (g * k)⁻¹ = g * (k * b * k⁻¹) * g⁻¹ := by group
    rwa [e]
  refine ⟨g * k, mem_normalizer_of_map_le (fun b hb => hn b hb), ?_⟩
  have hBY : B ≤ normalizer (Y : Set G) := fun b hb => F.mem_normalizer_Y (hBC hb)
  obtain ⟨b₁, hb₁, y₁, hy₁, hg⟩ := mem_sup_mul_of_le_normalizer hBY hgBY
  have hzB : z ∈ B := Subgroup.mem_sup_left hzD
  have huB : u ∈ B := Subgroup.mem_sup_left hu
  have hmB : (g * k) * z * (g * k)⁻¹ ∈ B := hn z hzB
  set y₀ : G := k * z * k⁻¹ * u⁻¹ with hy₀
  have hkz : k * z * k⁻¹ = y₀ * u := by rw [hy₀]; group
  have hb₁u : b₁ * u = u * b₁ := by
    obtain ⟨hcomm, -⟩ := forall_of_isElementaryAbelian hBel
    exact hcomm b₁ hb₁ u huB
  have hb₁u' : b₁⁻¹ * u⁻¹ = u⁻¹ * b₁⁻¹ := by
    calc b₁⁻¹ * u⁻¹ = (u * b₁)⁻¹ := by group
      _ = (b₁ * u)⁻¹ := by rw [hb₁u]
      _ = u⁻¹ * b₁⁻¹ := by group
  have huC : u ∈ centralizer ({x} : Set G) := hDC u hu
  have hmY : (g * k) * z * (g * k)⁻¹ * u⁻¹ ∈ Y := by
    have e : (g * k) * z * (g * k)⁻¹ * u⁻¹ =
        b₁ * (y₁ * y₀ * (u * y₁⁻¹ * u⁻¹)) * b₁⁻¹ := by
      calc (g * k) * z * (g * k)⁻¹ * u⁻¹ = g * (k * z * k⁻¹) * g⁻¹ * u⁻¹ := by group
        _ = (b₁ * y₁) * (y₀ * u) * (b₁ * y₁)⁻¹ * u⁻¹ := by rw [hg, hkz]
        _ = b₁ * y₁ * y₀ * u * y₁⁻¹ * (b₁⁻¹ * u⁻¹) := by group
        _ = b₁ * y₁ * y₀ * u * y₁⁻¹ * (u⁻¹ * b₁⁻¹) := by rw [hb₁u']
        _ = b₁ * (y₁ * y₀ * (u * y₁⁻¹ * u⁻¹)) * b₁⁻¹ := by group
    rw [e]
    have hyu : u * y₁⁻¹ * u⁻¹ ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.1 (F.mem_normalizer_Y huC) y₁⁻¹).1 (Y.inv_mem hy₁)
      exact this
    have hb₁Y := (Subgroup.mem_normalizer_iff.1 (hBY hb₁) (y₁ * y₀ * (u * y₁⁻¹ * u⁻¹))).1
      (Y.mul_mem (Y.mul_mem hy₁ hz_img) hyu)
    exact hb₁Y
  have hmBY : (g * k) * z * (g * k)⁻¹ * u⁻¹ ∈ B ⊓ Y := ⟨B.mul_mem hmB (B.inv_mem huB), hmY⟩
  rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot K hBp, Subgroup.mem_bot] at hmBY
  exact mul_inv_eq_one.1 hmBY

end Frame

end CFSG.GH74.GLS.Th2.P43f
