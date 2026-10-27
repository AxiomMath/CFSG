module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Orb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Aut

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

theorem inf_conjugate_P_eq_bot (H₁ : h.L81Hyp) {w : H} (hwN : w ∈ normalizer (h.S : Set H))
    (hwa : w * h.a * w⁻¹ ≠ h.a) : h.P ⊓ conjugate h.P w = ⊥ := by
  by_contra hne'
  obtain ⟨x, hx, hx1, hxZ⟩ := Seven.exists_mem_center_of_normal h.toHyp52.isPGroup_S
    (inf_le_left.trans inf_le_left)
    (fun t ht y hy => mem_inf.mpr ⟨h.toHyp52.conj_mem_P' ht (mem_inf.mp hy).1,
      h.toHyp52.sec8_conj_mem_conjugate_P hwN ht (mem_inf.mp hy).2⟩) hne'
  obtain ⟨hxP, hxw⟩ := mem_inf.mp hx
  rw [mem_conjugate_iff] at hxw
  have hxa : x = h.a := by
    have hv' : x ∈ h.P ⊓ centralizer (h.S : Set H) :=
      mem_inf.mpr ⟨hxP, mem_centralizer_iff.mpr fun t ht => hxZ t ht⟩
    rw [H₁.C_eq] at hv'
    exact (mem_zpowers_two h.orderOf_a hv').resolve_left hx1
  have hwxZ : w * x * w⁻¹ ∈ h.P ⊓ centralizer (h.S : Set H) := by
    refine mem_inf.mpr ⟨hxw, mem_centralizer_iff.mpr fun t ht => ?_⟩
    have htw : w⁻¹ * t * w ∈ h.S := by
      have := (mem_normalizer_iff.mp (inv_mem hwN) t).mp ht
      rwa [inv_inv] at this
    have h1 := hxZ _ htw
    calc t * (w * x * w⁻¹) = w * ((w⁻¹ * t * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * t * w)) * w⁻¹ := by rw [h1]
      _ = w * x * w⁻¹ * t := by group
  rw [H₁.C_eq, hxa] at hwxZ
  rcases mem_zpowers_two h.orderOf_a hwxZ with h1 | h1
  · apply Data.a_ne_one' (h := h)
    calc h.a = w⁻¹ * (w * h.a * w⁻¹) * w := by group
      _ = 1 := by rw [h1]; group
  · exact hwa h1

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem p_mem_S : d.p ∈ h.S := (mem_inf.mp d.p_mem).1

omit [Finite H] in
theorem orderOf_conj_inv (v x : H) : orderOf (v⁻¹ * x * v) = orderOf x := by
  have := orderOf_injective (MulAut.conj v⁻¹).toMonoidHom (MulAut.conj v⁻¹).injective x
  simpa [MulAut.conj_apply] using this

theorem exists_sylow_innOf : ∃ T : Sylow 2 (h.J ⧸ pPrimeCore 2 h.J),
    innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Seven.rhoImg h.J h.D ∧
      Nat.card (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) = Nat.card h.D := by
  obtain ⟨T, hT, hTD⟩ := h.toHyp52.sec8_exists_sylow_Dbar
  exact ⟨T, by rw [hT, Seven.rhoImg_eq_innOf (inf_le_right : h.D ≤ h.J)], hTD⟩

section Five

variable {v : H} (hv : d.IsV v) (I : In81) (F : d.Facts)
  (h3 : ∀ c : H, c⁻¹ * (h.a * d.sigma) * c ≠ d.sigma)
include I F h3

omit I F h3 in
theorem sigma_mem_R0 : d.sigma ∈ d.R0 := mem_sup_right (mem_zpowers _)

theorem sigma_comm_p : d.sigma * d.p * d.sigma⁻¹ = d.p := by
  rcases d.sigma_p I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 F with h1 | h1
  · exact h1
  · exfalso
    set s := d.sigma with hs
    have hpa : d.p⁻¹ * h.a * d.p = h.a := by
      rw [mul_assoc, ← h.toHyp52.comm_a d.p_mem_S, inv_mul_cancel_left]
    have h2 : d.p⁻¹ * s * d.p = h.a * s := by
      calc d.p⁻¹ * s * d.p = d.p⁻¹ * (s * d.p * s⁻¹) * s := by group
        _ = d.p⁻¹ * (h.a * d.p) * s := by rw [h1]
        _ = (d.p⁻¹ * h.a * d.p) * s := by group
        _ = h.a * s := by rw [hpa]
    apply h3 d.p⁻¹
    rw [← h2]
    group

theorem sigma_comm_P {π : H} (hπ : π ∈ h.P) : d.sigma * π = π * d.sigma :=
  d.sigma_comm_R0_of_comm (sigma_comm_p I F h3) (mem_sup_left hπ)

include hv

theorem v_conj_sigma :
    v * d.sigma * v⁻¹ = d.sigma ∨ v * d.sigma * v⁻¹ = h.a * d.z * d.sigma := by
  have hvN : v⁻¹ ∈ normalizer (h.F32 : Set H) :=
    inv_mem (h.normalizer_S_le_normalizer_F32 hv.mem_N)
  have := conj_sigma_cases hv I F h3 hvN
  rwa [inv_inv] at this

theorem card_P_le_card_D (hFO : CF81FieldOrd) : Nat.card h.P ≤ Nat.card h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hP⟩ := d.pres
  have hva : v * h.a * v⁻¹ ≠ h.a := by
    rw [show v * h.a * v⁻¹ = d.z by rw [← hv.conj_z]; group]
    exact d.z_ne_a
  have hPP := H₁.inf_conjugate_P_eq_bot hv.mem_N hva
  have hvS : ∀ x ∈ h.S, v⁻¹ * x * v ∈ h.S := fun x hx => by
    have := (mem_normalizer_iff.mp (inv_mem hv.mem_N) x).mp hx
    rwa [inv_inv] at this
  have hPvS : conjugate h.P v ≤ h.S := fun x hx => by
    rw [mem_conjugate_iff] at hx
    have := hvS _ ((mem_inf.mp hx).1)
    rwa [show v⁻¹ * (v * x * v⁻¹) * v = x by group] at this
  have hPvN : conjugate h.P v ≤ normalizer (h.J : Set H) := hPvS.trans h.toHyp52.S_le_normalizer
  set f : ↥(conjugate h.P v) →* MulAut (h.J ⧸ pPrimeCore 2 h.J) :=
    (Eight.oddBarAction h.J).comp (inclusion hPvN) with hf
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxP : (x : H) ∈ h.P := (rho_eq_one_iff (h := h) (hPvS x.2)).mp hx
    have : (x : H) ∈ h.P ⊓ conjugate h.P v := mem_inf.mpr ⟨hxP, x.2⟩
    rw [hPP] at this
    exact Subtype.ext (mem_bot.mp this)
  set p' := v⁻¹ * d.p * v with hp'
  have hp'P : p' ∈ conjugate h.P v := by
    rw [mem_conjugate_iff, hp', show v * (v⁻¹ * d.p * v) * v⁻¹ = d.p by group]
    exact d.p_mem
  have hp'S : p' ∈ h.S := hPvS hp'P
  have hfp : f ⟨p', hp'P⟩ = rhoS hp'S := rfl
  have hord : orderOf (rhoS hp'S) = orderOf d.p := by
    rw [← hfp, orderOf_injective f hfinj, Subgroup.orderOf_mk, hp', orderOf_conj_inv]
  have hpσ : Commute d.p d.sigma := (sigma_comm_P I F h3 d.p_mem).symm
  have hpa : Commute d.p h.a := h.toHyp52.comm_a d.p_mem_S
  have hpz : Commute d.p d.z := d.comm_z_of_mem_S d.p_mem_S
  have hc : Commute d.p (v * d.sigma * v⁻¹) := by
    rcases v_conj_sigma hv I F h3 with h1 | h1 <;> rw [h1]
    · exact hpσ
    · exact (hpa.mul_right hpz).mul_right hpσ
  have hp'σ : p' * d.sigma = d.sigma * p' := by
    have h1 := hc.map (MulAut.conj v⁻¹).toMonoidHom
    have e1 : (MulAut.conj v⁻¹).toMonoidHom d.p = p' := by
      rw [hp']; simp
    have e2 : (MulAut.conj v⁻¹).toMonoidHom (v * d.sigma * v⁻¹) = d.sigma := by
      show (MulAut.conj v⁻¹) (v * d.sigma * v⁻¹) = d.sigma
      rw [MulAut.conj_apply, inv_inv]
      exact Eight.inv_conj_cancel v d.sigma
    rw [e1, e2] at h1
    exact h1.eq
  have hσS := d.sigma_mem_S
  have hcomm : rhoS hp'S * rhoS hσS = rhoS hσS * rhoS hp'S := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hp'σ
  obtain ⟨T, hinn, hTD⟩ := exists_sylow_innOf (h := h)
  obtain ⟨p₀, f₀, hp₀, hp₀2, hf₀, hJL⟩ := H₁.exists_lieModel_Jbar
  have hσC : rhoS hσS ∈ centralizer
      (innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) : Set (MulAut (h.J ⧸ pPrimeCore 2 h.J))) := by
    rw [hinn, mem_centralizer_iff]
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (d.D_comm_R0 F e (mem_subgroupOf.mp he) d.sigma sigma_mem_R0)
  have hσnot : rhoS hσS ∉ innOf (T : Subgroup (h.J ⧸ pPrimeCore 2 h.J)) := by
    rw [hinn]
    rintro ⟨⟨e, heN⟩, he, heq⟩
    have heS : e ∈ h.S := h.toHyp52.D_le_S (mem_subgroupOf.mp he)
    have h1 : rhoS (mul_mem (inv_mem heS) hσS) = 1 := by
      show Eight.oddBarAction h.J ((⟨e, heN⟩ : ↥(normalizer (h.J : Set H)))⁻¹ *
        ⟨d.sigma, h.toHyp52.S_le_normalizer hσS⟩) = 1
      rw [map_mul, map_inv, heq, inv_mul_cancel]
    have h2 := (rho_eq_one_iff (h := h) (mul_mem (inv_mem heS) hσS)).mp h1
    apply d.sigma_not_mem_DP I.cf1 I.cf2 F
    have h3' := mul_mem_sup (mem_subgroupOf.mp he) h2
    rwa [mul_inv_cancel_left] at h3'
  have h2grp : IsPGroup 2 (zpowers (rhoS hp'S)) := by
    obtain ⟨k, hk⟩ := hP.two_pow
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord, hk])
  have key := hFO _ p₀ f₀ hp₀ hp₀2 hf₀ hJL T (hTD ▸ F.eight_le) (rhoS hσS)
    (rhoS_mul_self hσS d.sigma_mul_self) hσC hσnot (rhoS hp'S) hcomm h2grp
  rw [hord, hTD] at key
  rw [← hP.card]
  exact key

end Five

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
