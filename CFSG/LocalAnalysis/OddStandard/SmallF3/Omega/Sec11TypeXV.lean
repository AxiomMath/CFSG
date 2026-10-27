module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeXZ2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43
  Certificates.OmegaInv Certificates.OmegaT11

local notation "P45" => Equiv.Perm (Fin 45)

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G}
  {K1 K2 T R : Subgroup G} {h z' : G}

theorem t11_exists_ys
    (D : T11Frame t L S z K1 K2 T R h z') :
    ∃ l ∈ L, ∃ y₁ ∈ L, ∃ y₂ ∈ L, y₁ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₁ ∧
      y₂ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₂ ∧ y₁ ^ 3 = 1 ∧ y₂ ^ 3 = 1 ∧
      y₁ * y₂ * (y₁ * y₂) = 1 ∧ y₁ * y₂ ≠ 1 ∧
      (h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) * l = y₁ * y₂ * z' := by
  obtain ⟨lam, hlam, b₁, hb₁, b₂, hb₂, hc₁, hc₂, h₁3, h₂3, hsq, hne, hcomm⟩ := t11_exists_comm
  obtain ⟨⟨l, hl⟩, hle⟩ := D.F.ψ_surj hlam
  obtain ⟨⟨y₁, hy₁⟩, hye₁⟩ := D.F.ψ_surj hb₁
  obtain ⟨⟨y₂, hy₂⟩, hye₂⟩ := D.F.ψ_surj hb₂
  have hcs : ∀ {y : G} (hy : y ∈ L) {b : P45}, D.F.ψ ⟨y, hy⟩ = b → b * r3 () = r3 () * b →
      y * (h⁻¹ * t * h) = h⁻¹ * t * h * y := by
    intro y hy b hyb hbr
    have e : D.F.φ ⟨h⁻¹ * t * h, t11_s_norm D.hyp⟩ * D.F.ψ ⟨y, hy⟩ =
        D.F.ψ ⟨y, hy⟩ * D.F.φ ⟨h⁻¹ * t * h, t11_s_norm D.hyp⟩ := by
      rw [D.hF, hyb]
      exact hbr.symm
    exact ((D.F.comm_phi_psi_iff _ _).1 e).symm
  have hpow : ∀ {y : G} (hy : y ∈ L) {b : P45}, D.F.ψ ⟨y, hy⟩ = b → b ^ 3 = 1 → y ^ 3 = 1 := by
    intro y hy b hyb hb3
    have e : D.F.ψ (⟨y, hy⟩ ^ 3) = D.F.ψ 1 := by rw [map_pow, hyb, hb3, map_one]
    simpa using congrArg Subtype.val (D.F.ψ_injective e)
  have h12 : D.F.ψ ⟨y₁ * y₂, L.mul_mem hy₁ hy₂⟩ = b₁ * b₂ := by
    rw [t11_psi_mul D.F hy₁ hy₂, hye₁, hye₂]
  refine ⟨l, hl, y₁, hy₁, y₂, hy₂, hcs hy₁ hye₁ hc₁, hcs hy₂ hye₂ hc₂, hpow hy₁ hye₁ h₁3,
    hpow hy₂ hye₂ h₂3, ?_, ?_, ?_⟩
  · have e : D.F.ψ ⟨y₁ * y₂ * (y₁ * y₂), L.mul_mem (L.mul_mem hy₁ hy₂) (L.mul_mem hy₁ hy₂)⟩ =
        D.F.ψ ⟨1, L.one_mem⟩ := by
      rw [t11_psi_mul D.F (L.mul_mem hy₁ hy₂) (L.mul_mem hy₁ hy₂), h12,
        show (⟨1, L.one_mem⟩ : ↥L) = 1 from rfl, map_one]
      exact hsq
    exact t11_eq_of_psi D.F _ _ e
  · intro e
    apply hne
    rw [← h12]
    have e' : (⟨y₁ * y₂, L.mul_mem hy₁ hy₂⟩ : ↥L) = 1 := Subtype.ext e
    rw [e', map_one]
  · have hsN := t11_s_norm D.hyp
    have hsl : (h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) ∈ L := by
      have e := (Subgroup.mem_normalizer_iff.1 ((normalizer (L : Set G)).inv_mem hsN) l⁻¹).1
        (L.inv_mem hl)
      rwa [inv_inv] at e
    have hmem : (h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) * l ∈ L := L.mul_mem hsl hl
    have hmem' : y₁ * y₂ * z' ∈ L := L.mul_mem (L.mul_mem hy₁ hy₂) D.mem
    apply t11_eq_of_psi D.F hmem hmem'
    have eL : D.F.ψ ⟨(h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) * l, hmem⟩ =
        (r3 ())⁻¹ * lam⁻¹ * r3 () * lam := by
      have e1 : (⟨(h⁻¹ * t * h)⁻¹ * l⁻¹ * (h⁻¹ * t * h) * l, Subgroup.le_normalizer hmem⟩ :
          ↥(normalizer (L : Set G))) = (⟨h⁻¹ * t * h, hsN⟩)⁻¹ *
            (⟨l, Subgroup.le_normalizer hl⟩)⁻¹ * ⟨h⁻¹ * t * h, hsN⟩ *
            ⟨l, Subgroup.le_normalizer hl⟩ := rfl
      have e2 : D.F.φ ⟨l, Subgroup.le_normalizer hl⟩ = lam := hle
      show D.F.φ ⟨_, Subgroup.le_normalizer hmem⟩ = _
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, D.hF, e2]
    have eR : D.F.ψ ⟨y₁ * y₂ * z', hmem'⟩ = b₁ * b₂ * zeta0 () := by
      rw [t11_psi_mul D.F (L.mul_mem hy₁ hy₂) D.mem, h12, D.psi]
    rw [eL, eR]
    exact hcomm

private theorem t11v_split (H : T11Hyp t L S z K1 K2 T R h)
    (F' : PspFrame (CFSG.conjugate L h)) {y : G} (hys : y * (h⁻¹ * t * h) = h⁻¹ * t * h * y)
    (hy3 : y ^ 3 = 1) :
    ∃ y' ∈ CFSG.conjugate L h, ∃ k ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G),
      y = y' * k ∧ k * (h⁻¹ * t * h) = h⁻¹ * t * h * k ∧ k ^ 3 = 1 := by
  have hyN := t11_norm' H (Subgroup.mem_centralizer_singleton_iff.mpr hys)
  have h3 := t11_phi_pow3 F' hyN hy3
  obtain ⟨⟨y', hy'⟩, hye⟩ := F'.ψ_surj (t11_mem_P_of_pow3 (F'.mem_A _) h3)
  obtain ⟨k, hk⟩ : ∃ k, k = y'⁻¹ * y := ⟨_, rfl⟩
  have hkN : k ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    rw [hk]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer hy')) hyN
  have hkC : k ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    refine (F'.ker_iff ⟨k, hkN⟩).1 ?_
    have e1 : (⟨k, hkN⟩ : ↥(normalizer ((CFSG.conjugate L h : Subgroup G) : Set G))) =
        (⟨y', Subgroup.le_normalizer hy'⟩)⁻¹ * ⟨y, hyN⟩ := Subtype.ext hk
    have e2 : F'.φ ⟨y', Subgroup.le_normalizer hy'⟩ = F'.φ ⟨y, hyN⟩ := hye
    rw [e1, map_mul, map_inv, e2, inv_mul_cancel]
  have hy'3 : y' ^ 3 = 1 := by
    have e : F'.ψ (⟨y', hy'⟩ ^ 3) = F'.ψ 1 := by rw [map_pow, hye, h3, map_one]
    simpa using congrArg Subtype.val (F'.ψ_injective e)
  have hyk : y = y' * k := by
    rw [hk]
    group
  have hy's : Commute y' (h⁻¹ * t * h) :=
    Subgroup.mem_centralizer_singleton_iff.mp (t11_le_cent' H hy')
  have hys' : Commute y (h⁻¹ * t * h) := hys
  refine ⟨y', hy', k, hkC, hyk, ?_, ?_⟩
  · rw [hk]
    exact hy's.inv_left.mul_left hys'
  · have hc : Commute y' k := Subgroup.mem_centralizer_iff.mp hkC y' hy'
    have e : y ^ 3 = y' ^ 3 * k ^ 3 := by
      rw [hyk]
      exact hc.mul_pow 3
    rw [hy3, hy'3, one_mul] at e
    exact e.symm

theorem t11_prod_mem' (H : T11Hyp t L S z K1 K2 T R h)
    {y₁ y₂ : G} (h₁s : y₁ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₁)
    (h₂s : y₂ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₂) (h₁3 : y₁ ^ 3 = 1) (h₂3 : y₂ ^ 3 = 1)
    (hsq : y₁ * y₂ * (y₁ * y₂) = 1) : y₁ * y₂ ∈ CFSG.conjugate L h := by
  obtain ⟨F'⟩ := exists_pspFrame (t11_psp' H)
  obtain ⟨a₁, ha₁, k₁, hk₁, e₁, hk₁s, hk₁3⟩ := t11v_split H F' h₁s h₁3
  obtain ⟨a₂, ha₂, k₂, hk₂, e₂, hk₂s, hk₂3⟩ := t11v_split H F' h₂s h₂3
  have hc₁ : k₁ * a₂ = a₂ * k₁ := (Subgroup.mem_centralizer_iff.mp hk₁ a₂ ha₂).symm
  have hprod : y₁ * y₂ = a₁ * a₂ * (k₁ * k₂) := by
    rw [e₁, e₂]
    calc a₁ * k₁ * (a₂ * k₂) = a₁ * (k₁ * a₂) * k₂ := by group
      _ = a₁ * (a₂ * k₁) * k₂ := by rw [hc₁]
      _ = a₁ * a₂ * (k₁ * k₂) := by group
  have hkC : k₁ * k₂ ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hk₁ hk₂
  have haL : a₁ * a₂ ∈ CFSG.conjugate L h := Subgroup.mul_mem _ ha₁ ha₂
  have hk2 : k₁ * k₂ * (k₁ * k₂) = 1 := by
    have hc : a₁ * a₂ * (k₁ * k₂) = k₁ * k₂ * (a₁ * a₂) :=
      Subgroup.mem_centralizer_iff.mp hkC _ haL
    have e : a₁ * a₂ * (a₁ * a₂) * (k₁ * k₂ * (k₁ * k₂)) = 1 := by
      calc a₁ * a₂ * (a₁ * a₂) * (k₁ * k₂ * (k₁ * k₂))
          = a₁ * a₂ * (a₁ * a₂ * (k₁ * k₂)) * (k₁ * k₂) := by group
        _ = a₁ * a₂ * (k₁ * k₂ * (a₁ * a₂)) * (k₁ * k₂) := by rw [hc]
        _ = a₁ * a₂ * (k₁ * k₂) * (a₁ * a₂ * (k₁ * k₂)) := by group
        _ = y₁ * y₂ * (y₁ * y₂) := by rw [← hprod]
        _ = 1 := hsq
    have e' : a₁ * a₂ * (a₁ * a₂) = (k₁ * k₂ * (k₁ * k₂))⁻¹ := eq_inv_of_mul_eq_one_left e
    have haa : a₁ * a₂ * (a₁ * a₂) = 1 := by
      refine t11_eq_one F' (Subgroup.mul_mem _ haL haL) ?_
      rw [e']
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hkC hkC)
    rw [haa, one_mul] at e
    exact e
  by_cases hk1 : k₁ * k₂ = 1
  · rw [hprod, hk1, mul_one]
    exact haL
  · exfalso
    have hk₁s' : Commute k₁ (h⁻¹ * t * h) := hk₁s
    have hk₂s' : Commute k₂ (h⁻¹ * t * h) := hk₂s
    have e := t11_invol_eq' H hkC (hk₁s'.mul_left hk₂s') hk2 hk1
    have hk₂e : k₂ = k₁⁻¹ * (h⁻¹ * t * h) := by
      rw [← e]
      group
    have hs3 : (h⁻¹ * t * h) ^ 3 = h⁻¹ * t * h := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two, t11_s_sq H, one_mul]
    have h3 : k₂ ^ 3 = h⁻¹ * t * h := by
      rw [hk₂e, hk₁s'.inv_left.mul_pow, inv_pow, hk₁3, inv_one, one_mul, hs3]
    exact t11_s_ne_one H (h3.symm.trans hk₂3)

theorem t11_type_v
    (D : T11Frame t L S z K1 K2 T R h z')
    (F' : PspFrame (CFSG.conjugate L h)) (hF' : F'.φ ⟨t, t11_t_norm' D.hyp⟩ = r3 ())
    {y₁ y₂ : G} (h₁s : y₁ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₁)
    (h₂s : y₂ * (h⁻¹ * t * h) = h⁻¹ * t * h * y₂) (h₁t : y₁ * t = t * y₁)
    (h₂t : y₂ * t = t * y₂) (h₁3 : y₁ ^ 3 = 1) (h₂3 : y₂ ^ 3 = 1)
    (hsq : y₁ * y₂ * (y₁ * y₂) = 1) (hne : y₁ * y₂ ≠ 1) (hmem : y₁ * y₂ ∈ CFSG.conjugate L h) :
    InducesTypeSome (CFSG.conjugate L h) (y₁ * y₂ * z') 5 1 2 (-1) := by
  have H := D.hyp
  have hm := t11_zp_mem' D
  have h₁N := t11_norm' H (Subgroup.mem_centralizer_singleton_iff.mpr h₁s)
  have h₂N := t11_norm' H (Subgroup.mem_centralizer_singleton_iff.mpr h₂s)
  have hzN : z' ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hm
  have hr : ∀ {y : G} (hyN : y ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G)),
      y * t = t * y → F'.φ ⟨y, hyN⟩ * r3 () = r3 () * F'.φ ⟨y, hyN⟩ := by
    intro y hyN hyt
    rw [← hF']
    exact t11_phi_comm F' hyN (t11_t_norm' H) hyt
  have hsq' : F'.φ ⟨y₁, h₁N⟩ * F'.φ ⟨y₂, h₂N⟩ * (F'.φ ⟨y₁, h₁N⟩ * F'.φ ⟨y₂, h₂N⟩) = 1 := by
    rw [← map_mul, ← map_mul]
    have e : (⟨y₁, h₁N⟩ : ↥(normalizer ((CFSG.conjugate L h : Subgroup G) : Set G))) *
        ⟨y₂, h₂N⟩ * (⟨y₁, h₁N⟩ * ⟨y₂, h₂N⟩) = 1 := Subtype.ext hsq
    rw [e, map_one]
  have hne' : F'.φ ⟨y₁, h₁N⟩ * F'.φ ⟨y₂, h₂N⟩ ≠ 1 := by
    intro e
    apply hne
    rw [← map_mul] at e
    exact t11_eq_one F' hmem ((F'.ker_iff _).1 e)
  have hI := t11_invCent192 (F'.mem_A _) (F'.mem_A _) (hr h₁N h₁t) (hr h₂N h₂t)
    (t11_phi_pow3 F' h₁N h₁3) (t11_phi_pow3 F' h₂N h₂3) hsq' hne'
  rw [← t11_zp_psi' D F' hF'] at hI
  refine (TyDict.inducesTypeSome_two_minus_iff (t11_psp' H) F' _).2
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁N h₂N) hzN, ?_⟩
  rw [t11_phi_mul F' (Subgroup.mul_mem _ h₁N h₂N) hzN, t11_phi_mul F' h₁N h₂N]
  exact hI

end CFSG.OddStandard.SmallF3.Omega
