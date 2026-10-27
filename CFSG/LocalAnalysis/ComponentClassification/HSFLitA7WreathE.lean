module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7WreathSylow

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

namespace A7Data

variable {t : X} {L : Subgroup X} (A : A7Data t L)

theorem eR_z {z : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = a0 ^ 2)
    (eR : A.R ≃* DihedralGroup 4) : eR ⟨z, hz⟩ = r 2 := by
  apply eq_r_two_of_central
  · intro d
    obtain ⟨y, rfl⟩ := eR.surjective d
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (A.commute_z hz hψz y.2)
  · rw [← map_pow]
    have : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
    have h1 : (⟨z, hz⟩ : A.R) ^ 2 = 1 := Subtype.ext this
    rw [h1, map_one]
  · intro h1
    have := eR.injective (h1.trans (map_one eR).symm)
    have hz1 : z = 1 := congrArg Subtype.val this
    have h2 := hψz
    simp only [hz1] at h2
    rw [show (⟨1, _⟩ : A.T) = 1 from rfl, map_one] at h2
    exact absurd h2 (by decide)

theorem gen4_of_swap (hH : HaradaInput) {z : X} (hz : z ∈ A.R) (hψz : A.ψ ⟨z, hz.1⟩ = a0 ^ 2)
    {a : X} (ha : a ∈ A.R) (hψa : A.ψ ⟨a, ha.1⟩ = a0 * b0) (eR : A.R ≃* DihedralGroup 4)
    {B : Subgroup X} (hBT : B ≤ A.T) (hRB : A.R ⊓ B = ⊥)
    (hcomm : ∀ r ∈ A.R, ∀ b ∈ B, r * b = b * r)
    (hdec : ∀ h ∈ A.T, ∃ r ∈ A.R, ∃ b ∈ B, h = r * b) {u : X} (hu2 : u ^ 2 = 1)
    (huT : u ∉ A.T) (huR : ∀ r ∈ A.R, u * r * u⁻¹ ∈ B) (huB : ∀ b ∈ B, u * b * u⁻¹ ∈ A.R)
    (huz : u * z * u⁻¹ = t) (hut : u * t * u⁻¹ = z) (huN : u ∈ normalizer (A.T : Set X))
    (S : Sylow 2 X) (hS : (S : Subgroup X) = A.T ⊔ zpowers u) (P : Subgroup X)
    (hP : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  have huinv : u⁻¹ = u := by rw [inv_eq_iff_mul_eq_one, ← pow_two, hu2]
  have hz2 : z ^ 2 = 1 := A.sq_eq_one_of_mem_R hz (by rw [hψz]; decide)
  have ha2 : a ^ 2 = 1 := A.sq_eq_one_of_mem_R ha (by rw [hψa]; decide)
  have ht2 : t ^ 2 = 1 := by rw [← A.orderOf_t, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    rintro rfl
    have : A.ψ ⟨1, hz.1⟩ = 1 := map_one A.ψ
    rw [hψz] at this
    exact absurd this (by decide)
  have ha1 : a ≠ 1 := by
    rintro rfl
    have : A.ψ ⟨1, ha.1⟩ = 1 := map_one A.ψ
    rw [hψa] at this
    exact absurd this (by decide)
  have haz : a ≠ z := by
    intro h
    have h' : A.ψ ⟨a, ha.1⟩ = A.ψ ⟨z, hz.1⟩ := by congr 1; exact Subtype.ext h
    rw [hψa, hψz] at h'
    exact absurd h' (by decide)
  have htB : t ∈ B := huz ▸ huR z hz
  have hztc : z * t = t * z := A.commute_t hz.1
  set a' := u * a * u⁻¹ with ha'
  have ha'B : a' ∈ B := huR a ha
  have ha'2 : a' ^ 2 = 1 := by rw [ha', conj_pow, ha2]; group
  have haa : a * a' = a' * a := hcomm a ha a' ha'B
  have hζ2 : (z * t) ^ 2 = 1 := by
    calc (z * t) ^ 2 = z * (t * z) * t := by rw [pow_two]; group
      _ = z * (z * t) * t := by rw [← hztc]
      _ = z ^ 2 * t ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [hz2, ht2, one_mul]
  have hζ1 : z * t ≠ 1 := by
    intro h
    obtain ⟨h1, -⟩ := A.eq_of_mul_eq hRB hz (one_mem _) htB (one_mem _) (h.trans (mul_one 1).symm)
    exact hz1 h1
  have haa2 : (a * a') ^ 2 = 1 := by
    calc (a * a') ^ 2 = a * (a' * a) * a' := by rw [pow_two]; group
      _ = a * (a * a') * a' := by rw [← haa]
      _ = a ^ 2 * a' ^ 2 := by rw [pow_two, pow_two]; group
      _ = 1 := by rw [ha2, ha'2, one_mul]
  have hζT : ∀ h ∈ A.T, z * t * h = h * (z * t) := by
    intro h hh
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hdec h hh
    have e1 : z * h₁ = h₁ * z := A.commute_z hz hψz hh₁
    have e2 : t * h₂ = h₂ * t := A.commute_t (hBT hh₂) |>.symm
    have e3 : z * h₂ = h₂ * z := hcomm z hz h₂ hh₂
    have e4 : t * h₁ = h₁ * t := (A.commute_t hh₁.1).symm
    calc z * t * (h₁ * h₂) = (z * (t * h₁)) * h₂ := by group
      _ = (z * h₁) * (t * h₂) := by rw [e4]; group
      _ = (h₁ * z) * (h₂ * t) := by rw [e1, e2]
      _ = h₁ * (z * h₂) * t := by group
      _ = h₁ * h₂ * (z * t) := by rw [e3]; group
  obtain ⟨hV1, hV1m, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers hζ2
    (fun h => hζ1 (mem_bot.mp h)) (fun x hx => by rw [mem_bot.mp hx, one_mul, mul_one])
  have haaV1 : a * a' ∉ (⊥ ⊔ zpowers (z * t) : Subgroup X) := by
    intro h
    rcases hV1m _ h with h1 | h1
    · have h2 : a * a' = 1 * 1 := (mem_bot.mp h1).trans (mul_one 1).symm
      exact ha1 (A.eq_of_mul_eq hRB ha (one_mem _) ha'B (one_mem _) h2).1
    · have h2 : a * a' = z * t := by
        have h3 : a * a' * (z * t) = 1 := mem_bot.mp h1
        calc a * a' = a * a' * (z * t) * (z * t) := by
              rw [mul_assoc (a * a'), ← pow_two, hζ2, mul_one]
          _ = z * t := by rw [h3, one_mul]
      exact haz (A.eq_of_mul_eq hRB ha hz ha'B htB h2).1
  obtain ⟨hV2, hV2m, hV2c⟩ := hV1.sup_zpowers haa2 haaV1 (by
    intro x hx
    rcases hV1m x hx with h1 | h1
    · rw [mem_bot.mp h1, mul_one, one_mul]
    · have hx' : x = z * t := by
        have h3 : x * (z * t) = 1 := mem_bot.mp h1
        calc x = x * (z * t) * (z * t) := by rw [mul_assoc x, ← pow_two, hζ2, mul_one]
          _ = z * t := by rw [h3, one_mul]
      rw [hx']
      exact (hζT _ (mul_mem ha.1 (hBT ha'B))).symm)
  have hV2T : (⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') : Subgroup X) ≤ A.T :=
    sup_le (sup_le bot_le (zpowers_le.mpr (mul_mem hz.1 A.t_mem_T)))
      (zpowers_le.mpr (mul_mem ha.1 (hBT ha'B)))
  have hζu : u * (z * t) = z * t * u := by
    have : u * (z * t) * u⁻¹ = z * t := by
      rw [show u * (z * t) * u⁻¹ = (u * z * u⁻¹) * (u * t * u⁻¹) by group, huz, hut, hztc]
    calc u * (z * t) = u * (z * t) * u⁻¹ * u := by group
      _ = z * t * u := by rw [this]
  have hau : u * (a * a') = a * a' * u := by
    have h1 : u * a' * u⁻¹ = a := by
      rw [ha', show u * (u * a * u⁻¹) * u⁻¹ = u ^ 2 * a * (u ^ 2)⁻¹ by rw [pow_two]; group, hu2]
      group
    have : u * (a * a') * u⁻¹ = a * a' := by
      rw [show u * (a * a') * u⁻¹ = (u * a * u⁻¹) * (u * a' * u⁻¹) by group, h1, ← ha', haa]
    calc u * (a * a') = u * (a * a') * u⁻¹ * u := by group
      _ = a * a' * u := by rw [this]
  have hV2u : (⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') : Subgroup X) ≤
      centralizer ({u} : Set X) := by
    refine sup_le (sup_le bot_le ?_) ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
    · exact hζu.symm
    · exact hau.symm
  obtain ⟨hE, -, hEc⟩ := hV2.sup_zpowers hu2 (fun h => huT (hV2T h))
    (fun x hx => (mem_centralizer_singleton_iff.mp (hV2u hx)).symm)
  set E : Subgroup X := ⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') ⊔ zpowers u with hEdef
  have hcardE : Nat.card E = 8 := by rw [hEc, hV2c, hV1c, Subgroup.card_bot]
  have hES : E ≤ S := by
    rw [hS]
    exact sup_le (hV2T.trans le_sup_left) (zpowers_le.mpr (mem_sup_right (mem_zpowers u)))
  have hζE : z * t ∈ E := le_sup_left (a := (⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') :
    Subgroup X)) (le_sup_left (a := (⊥ ⊔ zpowers (z * t) : Subgroup X))
      (le_sup_right (a := (⊥ : Subgroup X)) (mem_zpowers (z * t))))
  have haaE : a * a' ∈ E := le_sup_left (a := (⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') :
    Subgroup X)) (le_sup_right (a := (⊥ ⊔ zpowers (z * t) : Subgroup X)) (mem_zpowers _))
  have huE : u ∈ E := le_sup_right (a := (⊥ ⊔ zpowers (z * t) ⊔ zpowers (a * a') :
    Subgroup X)) (mem_zpowers u)
  refine gen4_of_harada hH S hES hE hcardE (fun g hg hgE => ?_) P hP
  have hgu : g * u = u * g := hgE u huE
  have hga : g * (a * a') = a * a' * g := hgE _ haaE
  have key : ∀ h ∈ A.T, h * u = u * h → h * (a * a') = a * a' * h → h ∈ E := by
    intro h hh hhu hha
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hdec h hh
    have hu1 : u * h₁ * u⁻¹ ∈ B := huR h₁ hh₁
    have hu2' : u * h₂ * u⁻¹ ∈ A.R := huB h₂ hh₂
    have hfix : (u * h₂ * u⁻¹) * (u * h₁ * u⁻¹) = h₁ * h₂ := by
      calc (u * h₂ * u⁻¹) * (u * h₁ * u⁻¹) = (u * h₁ * u⁻¹) * (u * h₂ * u⁻¹) :=
            hcomm _ hu2' _ hu1
        _ = u * (h₁ * h₂) * u⁻¹ := by group
        _ = h₁ * h₂ := by rw [← hhu]; group
    obtain ⟨-, h₂eq⟩ := A.eq_of_mul_eq hRB hu2' hh₁ hu1 hh₂ hfix
    have hcomm₁ : h₁ * a = a * h₁ := by
      have e1 : (h₁ * a) * (h₂ * a') = (a * h₁) * (a' * h₂) := by
        calc (h₁ * a) * (h₂ * a') = h₁ * (a * h₂) * a' := by group
          _ = h₁ * (h₂ * a) * a' := by rw [hcomm a ha h₂ hh₂]
          _ = h₁ * h₂ * (a * a') := by group
          _ = a * a' * (h₁ * h₂) := hha
          _ = a * (a' * h₁) * h₂ := by group
          _ = a * (h₁ * a') * h₂ := by rw [hcomm h₁ hh₁ a' ha'B]
          _ = (a * h₁) * (a' * h₂) := by group
      exact (A.eq_of_mul_eq hRB (mul_mem hh₁ ha) (mul_mem ha hh₁) (mul_mem hh₂ ha'B)
        (mul_mem ha'B hh₂) e1).1
    have hd2 : eR ⟨a, ha⟩ ^ 2 = 1 := by
      rw [← map_pow]
      have h1 : (⟨a, ha⟩ : A.R) ^ 2 = 1 := Subtype.ext ha2
      rw [h1, map_one]
    have hd1 : eR ⟨a, ha⟩ ≠ 1 := fun h1 => ha1 (congrArg Subtype.val
      (eR.injective (h1.trans (map_one eR).symm)))
    have hdr : eR ⟨a, ha⟩ ≠ r 2 := fun h1 => haz (congrArg Subtype.val
      (eR.injective (h1.trans (A.eR_z hz hψz eR).symm)))
    have hpd : eR ⟨h₁, hh₁⟩ * eR ⟨a, ha⟩ = eR ⟨a, ha⟩ * eR ⟨h₁, hh₁⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm₁
    have hz' := A.eR_z hz hψz eR
    have hh₁E : h₁ = 1 ∨ h₁ = z ∨ h₁ = a ∨ h₁ = z * a := by
      rcases eq_of_commute_noncentral _ _ hd2 hd1 hdr hpd with h1 | h1 | h1 | h1
      · exact Or.inl (congrArg Subtype.val (eR.injective (h1.trans (map_one eR).symm)))
      · exact Or.inr (Or.inl (congrArg Subtype.val (eR.injective (h1.trans hz'.symm))))
      · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val (eR.injective h1))))
      · have : (⟨h₁, hh₁⟩ : A.R) = ⟨z * a, mul_mem hz ha⟩ := eR.injective (by
          rw [h1, show (⟨z * a, mul_mem hz ha⟩ : A.R) = ⟨z, hz⟩ * ⟨a, ha⟩ from rfl, map_mul, hz'])
        exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val this)))
    have hh₂' : h₂ = u * h₁ * u⁻¹ := h₂eq.symm
    rw [hh₂']
    rcases hh₁E with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel, one_mul]
      exact one_mem _
    · rw [huz]
      exact hζE
    · exact haaE
    · rw [show u * (z * a) * u⁻¹ = (u * z * u⁻¹) * a' by rw [ha']; group, huz]
      have : z * a * (t * a') = z * t * (a * a') := by
        calc z * a * (t * a') = z * (a * t) * a' := by group
          _ = z * (t * a) * a' := by rw [(A.commute_t ha.1)]
          _ = z * t * (a * a') := by group
      rw [this]
      exact mul_mem hζE haaE
  have hgT : g ∈ A.T ⊔ zpowers u := hS ▸ hg
  rcases mem_or_mul_mem_of_mem_sup_zpowers hu2 huN hgT with h1 | h1
  · exact key g h1 hgu hga
  · have h2 : g * u * u = u * (g * u) := by
      rw [show u * (g * u) = (u * g) * u by group, ← hgu]
    have h3 : g * u * (a * a') = a * a' * (g * u) := by
      calc g * u * (a * a') = g * (u * (a * a')) := by group
        _ = g * (a * a' * u) := by rw [hau]
        _ = g * (a * a') * u := by group
        _ = a * a' * g * u := by rw [hga]
        _ = a * a' * (g * u) := by group
    have := key _ h1 h2 h3
    have h4 := mul_mem this huE
    rwa [mul_assoc, ← pow_two, hu2, mul_one] at h4

theorem gen4_of_dihedral (e : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7))
    (hH : HaradaInput) (hK : Nat.card A.K = 4) {c : X} (hc : c ∈ A.K) (hco : orderOf c = 4)
    {i : X} (hi : i ∈ A.T) (hi2 : i ^ 2 = 1) (hic : c * i ≠ i * c) (P : Subgroup X)
    (hP : IsPGroup 2 P) : ∃ s : Finset X, s.card ≤ 4 ∧ closure (s : Set X) = P := by
  obtain ⟨k, hk, hk2, hψk, hkc⟩ := A.exists_dihedral_partner hK hc hco hi hi2 hic
  obtain ⟨z, hz, hψz⟩ := A.exists_mem_R_ψ_eq a0_sq_mem_R0
  obtain ⟨a, ha, hψa⟩ := A.exists_mem_R_ψ_eq a0_b0_mem_R0
  have hrho : rho0 ∈ R0 := by
    rw [show rho0 = (a0 * b0) * (c0 * b0) by decide]
    exact mul_mem a0_b0_mem_R0 c0_b0_mem_R0
  obtain ⟨x, hx, hψx⟩ := A.exists_mem_R_ψ_eq hrho
  have hx2 : x ^ 2 = z := by
    have hm : x ^ 2 ∈ A.R := pow_mem hx 2
    refine A.eq_of_ψ_eq hm hz ?_
    have : (⟨x ^ 2, hm.1⟩ : A.T) = (⟨x, hx.1⟩ : A.T) ^ 2 := rfl
    rw [this, map_pow, hψx, hψz]
    decide
  obtain ⟨φ, hφz, hφt⟩ := A.exists_coords hK hc hco hk hk2 hψk hkc hz hψz
  by_cases hS : ∃ S : Sylow 2 X, (S : Subgroup X) = A.T
  · obtain ⟨S, hS⟩ := hS
    exact A.config.gen4_of_coe_sylow_eq e A.syl S hS P hP
  push Not at hS
  obtain ⟨w, hwN, hwT, hwp⟩ := exists_mem_normalizer_not_mem A.isPGroup_T hS
  have hwt : w * t ≠ t * w := fun h =>
    hwT (A.mem_T_of_commute hwp le_sup_left (mem_sup_right (mem_zpowers w)) h)
  obtain ⟨hwtz, hwzt⟩ := A.conj_t_eq_z hz.1 φ hφz hφt hwN hwt
  obtain ⟨eR⟩ := A.config.inf_L_mulEquiv_dihedral A.syl
  have hRB := A.inf_conj_eq_bot hz eR (A.eR_z hz hψz eR) hwN hwtz
  have hcardT : Nat.card A.T = 64 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  have hcardB : Nat.card (A.R.map (MulAut.conj w).toMonoidHom) = 8 := by
    rw [card_map_of_injective (MulAut.conj w).injective, A.card_R]
  obtain ⟨hcomm, hdec⟩ := A.commute_and_exists_mul_eq (A.map_conj_le_T hwN) hRB
    (fun g hg b hb => A.conj_mem_map hwN hg hb) hcardB hcardT
  obtain ⟨u, hu2, huN, huT, hup, huR, huB, huz, hut⟩ :=
    A.exists_swap hz hψz hwN hwT hwp hwtz hwzt hRB hcomm hdec
  obtain ⟨S, hS⟩ := A.exists_sylow_sup hz.1 φ hφz hφt hx.1 hx2 hu2 huN hup huz hut
  exact A.gen4_of_swap hH hz hψz ha hψa eR (A.map_conj_le_T hwN) hRB hcomm hdec hu2 huT huR
    huB huz hut huN S hS P hP

end A7Data

end CFSG.ComponentClassification.HSFLit
