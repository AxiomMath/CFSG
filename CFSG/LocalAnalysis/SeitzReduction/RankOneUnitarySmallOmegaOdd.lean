module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallParity
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaRegularMain

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

theorem card_dvd_card_sub_one_of_semiregular {H X : Type*} [Group H] [Finite H] [Finite X]
    [MulAction H X] (x₀ : X) (hx₀ : ∀ g : H, g • x₀ = x₀)
    (hfree : ∀ g : H, ∀ x : X, g • x = x → x ≠ x₀ → g = 1) :
    Nat.card H ∣ Nat.card X - 1 := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let : Fintype X := Fintype.ofFinite X
  let : Fintype (Quotient (MulAction.orbitRel H X)) := Fintype.ofFinite _
  let : ∀ b : X, Fintype (MulAction.stabilizer H b) := fun b => Fintype.ofFinite _
  have hcf := MulAction.card_eq_sum_card_group_div_card_stabilizer H X
  set ω₀ : Quotient (MulAction.orbitRel H X) := Quotient.mk'' x₀ with hω₀
  have hout₀ : ω₀.out = x₀ := by
    have h1 : MulAction.orbitRel H X ω₀.out x₀ := Quotient.exact' (by
      rw [hω₀]; exact Quotient.out_eq' _)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h1
    rw [← hg, hx₀]
  have hterm₀ : Fintype.card H / Fintype.card (MulAction.stabilizer H ω₀.out) = 1 := by
    have htop : MulAction.stabilizer H ω₀.out = ⊤ := by
      rw [hout₀, eq_top_iff]
      intro g _
      exact hx₀ g
    have hc : Fintype.card (MulAction.stabilizer H ω₀.out) = Fintype.card H := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, htop, card_top]
    rw [hc, Nat.div_self Fintype.card_pos]
  have hterm : ∀ ω ∈ (Finset.univ.erase ω₀),
      Fintype.card H / Fintype.card (MulAction.stabilizer H ω.out) = Fintype.card H := by
    intro ω hω
    have hne : ω.out ≠ x₀ := by
      intro h1
      apply (Finset.mem_erase.mp hω).1
      rw [hω₀, ← h1]
      exact (Quotient.out_eq' ω).symm
    have hbot : MulAction.stabilizer H ω.out = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      exact hfree g ω.out (MulAction.mem_stabilizer_iff.mp hg) hne
    rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer H ω.out), hbot, card_bot,
      Nat.div_one]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ω₀), hterm₀,
    Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hcf
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcf, Nat.add_sub_cancel_left]
  exact Dvd.intro_left _ rfl

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_cartan_card_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ D : Subgroup G, D ≤ L ⊓ normalizer (szT₁ L T : Set G) ∧
      Nat.card D = (2 ^ f - 1) * ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) ∧
      ∀ d ∈ D, d ≠ 1 → ∀ x ∈ szT₁ L T, d * x * d⁻¹ * x⁻¹ ∈ szA₁ (szT₁ L T) →
        x ∈ szA₁ (szT₁ L T) := by
  obtain ⟨e, Q, hB, hmemQ, hmemZ⟩ := h.exists_bender_of_card_sylow hS2
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q
  have hT₁L : szT₁ L T ≤ L := szT₁_le_right L T
  have he : e = (2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1) := by
    rcases hB.cases' with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, he, -⟩
    · omega
    · omega
    · exact he
  refine ⟨(cartan (Q : Subgroup L) t₀).map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact mem_inf.mpr ⟨d.2, (mem_borel_iff_mem_normalizer hmemQ hT₁L d).mp
      (cartan_le_borel _ _ hd)⟩
  · rw [card_map_of_injective L.subtype_injective, hc.card_cartan, he]
  · rintro _ ⟨d, hd, rfl⟩ hd1 x hx hdx
    have hxL : x ∈ L := hT₁L hx
    have hd1' : d ≠ 1 := fun h1 => hd1 (by rw [h1]; rfl)
    have := hB.fixedPointFree_unitary Q hc.sq_eq_one hc.not_mem hd hd1' ((hmemQ ⟨x, hxL⟩).mpr hx)
      ((hmemZ _).mpr (by simpa using hdx))
    exact (hmemZ _).mp this

section Certificates


theorem dvd_ncard_u3Omega_sub_one_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    (2 ^ f - 1) * ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1)) ∣ (u3Omega L T R₂ t).ncard - 1 := by
  classical
  obtain ⟨D, hDle, hDcard, hDfpf⟩ := h.exists_cartan_card_of_card_sylow hS2
  obtain ⟨-, -, -, hNR₁, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  have hdt : ∀ d ∈ D, d * t = t * d := fun d hd =>
    mem_centralizer_iff.mp h.mem d (mem_inf.mp (hDle hd)).1
  have hDA : D ≤ normalizer (szA L T t : Set G) := by
    intro d hd
    have hdT := (mem_inf.mp (hDle hd)).2
    have hdA₁ : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
      normalizer_le_normalizer_inf_centralizer (szT₁ L T) hdT
    have hdtN : d ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact ((Commute.zpow_right (hdt d hd) k).eq).symm
    exact mem_normalizer_sup_of_mem_inf hdA₁ hdtN
  have hDY : D ≤ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) :=
    hDA.trans hNR₁
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  have : Finite (u3Omega L T R₂ t) := hfin.to_subtype
  let ψ : D →* Equiv.Perm (u3Omega L T R₂ t) :=
    (u3OmegaAction L T R₂ t).comp (Subgroup.inclusion hDY)
  let : MulAction D (u3Omega L T R₂ t) := MulAction.compHom _ ψ
  have hsmul : ∀ (d : D) (X : u3Omega L T R₂ t),
      ((d • X : u3Omega L T R₂ t) : Subgroup G) =
        (X : Subgroup G).map (MulAut.conj (d : G)).toMonoidHom := fun d X => rfl
  set x₀ : u3Omega L T R₂ t := ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ with hx₀
  have hfix : ∀ d : D, d • x₀ = x₀ := by
    intro d
    apply Subtype.ext
    rw [hsmul, hx₀, map_conj_sup_zpowers (hNR₂ (hDA d.2)), hdt d d.2, mul_inv_cancel_right]
  have hfree : ∀ (d : D) (X : u3Omega L T R₂ t), d • X = X → X ≠ x₀ → d = 1 := by
    intro d X hdX hX
    by_contra hd1
    have hd1' : (d : G) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
    obtain ⟨q, hq⟩ := h.u3Omega_subset_range_of_card_sylow hS2 hR X.2
    induction q using QuotientGroup.induction_on with | H w => ?_
    rw [u3OmegaPoint_mk] at hq
    have hdwT : (d : G) * w * (d : G)⁻¹ ∈ szT₁ L T :=
      (mem_normalizer_iff.mp (mem_inf.mp (hDle d.2)).2 w).mp w.2
    have hXw : (X : Subgroup G) = R₂ ⊔ zpowers ((w : G) * t) := hq.symm
    have h2 : (X : Subgroup G).map (MulAut.conj (d : G)).toMonoidHom = X := by
      have := congrArg (fun Z : u3Omega L T R₂ t => (Z : Subgroup G)) hdX
      simpa only [hsmul] using this
    rw [hXw, map_conj_sup_zpowers (hNR₂ (hDA d.2))] at h2
    have e1 : (d : G) * ((w : G) * t) * (d : G)⁻¹ = ((d : G) * w * (d : G)⁻¹) * t := by
      have hdt' : (d : G) * t * (d : G)⁻¹ = t := by rw [hdt d d.2, mul_inv_cancel_right]
      calc (d : G) * ((w : G) * t) * (d : G)⁻¹ =
            ((d : G) * w * (d : G)⁻¹) * ((d : G) * t * (d : G)⁻¹) := by group
        _ = ((d : G) * w * (d : G)⁻¹) * t := by rw [hdt']
    rw [e1] at h2
    have h1 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁
          (QuotientGroup.mk ⟨(d : G) * w * (d : G)⁻¹, hdwT⟩) =
        u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk w) := by
      rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
      exact h2
    have h3 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h1
    rw [QuotientGroup.eq, mem_subgroupOf] at h3
    set z := ((d : G) * w * (d : G)⁻¹)⁻¹ * w with hz
    have h4 : z ∈ szA₁ (szT₁ L T) := by simpa [hz] using h3
    have hzc : z * ((d : G) * w * (d : G)⁻¹) = ((d : G) * w * (d : G)⁻¹) * z :=
      (mem_centralizer_iff.mp (mem_szA₁.mp h4).2 _ hdwT).symm
    have h5 : (d : G) * w * (d : G)⁻¹ * (w : G)⁻¹ ∈ szA₁ (szT₁ L T) := by
      have e2 : (d : G) * w * (d : G)⁻¹ * (w : G)⁻¹ = z⁻¹ := by
        have e3 : (w : G) = ((d : G) * w * (d : G)⁻¹) * z := by rw [hz]; group
        calc (d : G) * w * (d : G)⁻¹ * (w : G)⁻¹ =
              (d : G) * w * (d : G)⁻¹ * (((d : G) * w * (d : G)⁻¹) * z)⁻¹ := by rw [← e3]
          _ = (d : G) * w * (d : G)⁻¹ * (z * ((d : G) * w * (d : G)⁻¹))⁻¹ := by rw [hzc]
          _ = z⁻¹ := by group
      rw [e2]
      exact inv_mem h4
    have hwA := hDfpf d d.2 hd1' w w.2 h5
    apply hX
    apply Subtype.ext
    rw [← hq, hx₀]
    have hwt : (w : G) * t = t * w := hR.t_comm w w.2
    show R₂ ⊔ zpowers ((w : G) * t) = R₂ ⊔ zpowers t
    rw [hwt, sup_zpowers_mul_eq (hR.le hwA)]
  have hdvd := card_dvd_card_sub_one_of_semiregular x₀ hfix hfree
  rwa [hDcard, Nat.card_coe_set_eq] at hdvd

theorem ncard_u3Omega_of_odd_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hf : Odd f)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) :
    (u3Omega L T R₂ t).ncard = ((2 ^ f) ^ 2 + 2) / 3 ∨ (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 := by
  have hdvd := h.dvd_ncard_u3Omega_sub_one_of_card_sylow hS2 hR
  have hle := h.ncard_u3Omega_le_of_card_sylow hS2 hR
  have hlt := h.one_lt_ncard_u3Omega_of_card_sylow hS2 hR hmove
  have hev := h.even_ncard_u3Omega_of_card_sylow hS2 hR hmove
  set N := (u3Omega L T R₂ t).ncard with hN
  set a := 2 ^ f with ha
  have h3 : 3 ∣ a + 1 := by
    obtain ⟨k, hk⟩ := hf
    rw [ha, hk, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_succ, Nat.mul_mod, pow_mul,
      Nat.pow_mod]
    norm_num
  have hg : Nat.gcd 3 (a + 1) = 3 := Nat.gcd_eq_left h3
  rw [hg] at hdvd
  obtain ⟨b, hb⟩ := h3
  rw [hb, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hdvd
  have ha1 : 1 ≤ a := Nat.one_le_two_pow
  have hbodd : Odd b := by
    rcases Nat.even_or_odd b with ⟨c, hc⟩ | hb'
    · exfalso
      have : Even (a + 1) := ⟨3 * c, by rw [hb, hc]; ring⟩
      have ha2 : Even a := by
        rw [ha]
        exact (Nat.even_pow' (by have := h.two_le; omega)).mpr even_two
      exact Nat.not_even_one ((Nat.even_add.mp this).mp ha2)
    · exact hb'
  have haodd : Odd (a - 1) := by
    have ha2 : Even a := by
      rw [ha]
      exact (Nat.even_pow' (by have := h.two_le; omega)).mpr even_two
    obtain ⟨c, hc⟩ := ha2
    exact ⟨c - 1, by have : 1 ≤ c := by omega
                     omega⟩
  obtain ⟨j, hj⟩ := hdvd
  have hm3 : 3 * ((a - 1) * b) = a ^ 2 - 1 := by
    have e1 : a ^ 2 - 1 = (a - 1) * (a + 1) := by
      rw [sq, show a * a - 1 = a * a - 1 * 1 by rw [one_mul], Nat.mul_self_sub_mul_self_eq,
        mul_comm]
    rw [e1, hb]
    ring
  have hmpos : 0 < (a - 1) * b := by
    apply Nat.mul_pos
    · have : 2 ≤ a := by rw [ha]; exact Nat.le_self_pow (by have := h.two_le; omega) 2
      omega
    · rcases hbodd with ⟨c, hc⟩; omega
  have hj3 : j ≤ 3 := by
    by_contra hj3
    push Not at hj3
    have : (a - 1) * b * 4 ≤ (a - 1) * b * j := Nat.mul_le_mul_left _ hj3
    omega
  have hmodd : Odd ((a - 1) * b) := haodd.mul hbodd
  have hNodd : Odd (N - 1) := by
    obtain ⟨c, hc⟩ := hev
    exact ⟨c - 1, by omega⟩
  interval_cases j
  · omega
  · left
    have : a ^ 2 + 2 = 3 * N := by omega
    omega
  · exfalso
    rw [hj] at hNodd
    exact Nat.not_even_iff_odd.mpr hNodd ⟨(a - 1) * b, by ring⟩
  · right
    omega

end Certificates

end U3Start


@[expose] def U3OmegaOddDegreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → Odd f →
    (∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) →
    (u3Omega L T R₂ t).ncard ≠ ((2 ^ f) ^ 2 + 2) / 3

@[expose] def U3OmegaOddRegularInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → Odd f →
    (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 →
    HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range

section Certificates


theorem u3OmegaOddInput_of_degree_of_regular (hdeg : U3OmegaOddDegreeInput)
    (hreg : U3OmegaOddRegularInput) : U3OmegaOddInput := by
  intro G _ _ L f t T R₂ h hS2 hR hc hf hmove
  have hN : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2 :=
    (h.ncard_u3Omega_of_odd_of_card_sylow hS2 hR hf hmove).resolve_left
      (hdeg G L f t T R₂ h hS2 hR hc hf hmove)
  exact ⟨hN, hreg G L f t T R₂ h hS2 hR hc hf hN⟩

end Certificates

end CFSG.SeitzReduction.RankOne
