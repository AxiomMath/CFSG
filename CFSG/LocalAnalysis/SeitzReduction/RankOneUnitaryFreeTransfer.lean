module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Elem

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates


theorem not_isCyclic_quot_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    (hreg : HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range) :
    ¬ ∃ b ∈ T, ∀ s ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ szT₁ L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hcyc
  obtain ⟨U₁, hYU₁, hHU₁, hU₁C, htU₁, hU₁card, hU₁R₁, -, hfixR₁, -, -, -, -, hnot, hconj⟩ :=
    h.exists_u3U₁_export_of_regular_of_card_sylow hS2 hR hc hΩ hreg
  obtain ⟨-, -, -, hNA, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hTA : T ≤ normalizer (szA L T t : Set G) :=
    Subgroup.le_normalizer.trans (h.normalizer_le_normalizer_szA_of_card_sylow hS2)
  have hTU₁ : T ≤ normalizer (U₁ : Set G) := fun s hs => hYU₁ (hNA (hTA hs))
  have htN : t ∈ normalizer (U₁ : Set G) := hTU₁ htT
  set P := U₁ ⊔ T with hPdef
  have hPmem : ∀ x ∈ P, ∃ u ∈ U₁, ∃ s ∈ T, x = u * s := by
    intro x hx
    have hx' : x ∈ ((U₁ ⊔ T : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left _ _ hTU₁] at hx'
    obtain ⟨u, hu, s, hs, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨u, hu, s, hs, rfl⟩
  have hCt : ∀ x ∈ U₁, x * t = t * x → x ∈ szT₁ L T := by
    intro x hx hxt
    have hxR : x ∈ normalizer (R₂ : Set G) := centralizer_le_normalizer _ (hU₁C hx)
    have hxR₁ := hfixR₁ x (mem_sup_left hx) (by
      rw [map_conj_sup_zpowers hxR, hxt, mul_inv_cancel_right])
    have hxH : x ∈ szT₁ L T ⊔ R₂ := by rw [← hU₁R₁]; exact mem_inf.mpr ⟨hx, hxR₁⟩
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hxH
    have hwt : w * t = t * w := hR.t_comm w hw
    have hrt : r * t = t * r := by
      calc r * t = w⁻¹ * (w * r * t) := by group
        _ = w⁻¹ * (t * (w * r)) := by rw [hxt]
        _ = w⁻¹ * (t * w) * r := by group
        _ = w⁻¹ * (w * t) * r := by rw [hwt]
        _ = t * r := by group
    exact mul_mem hw (szA₁_le _ (hR.rho_ker r hr hrt))
  have hinvP : ∀ x ∈ P, x ^ 2 = 1 → x ∈ U₁ ∨ x * t⁻¹ ∈ U₁ := by
    intro x hx hx2
    obtain ⟨v, hv, s, hs, rfl⟩ := hPmem x hx
    have hs2U : s ^ 2 ∈ U₁ := by
      have e : s ^ 2 = (s * v⁻¹ * s⁻¹) * v⁻¹ * (v * s) ^ 2 := by rw [sq, sq]; group
      rw [e, hx2, mul_one]
      exact mul_mem ((mem_normalizer_iff.mp (hTU₁ hs) _).mp (inv_mem hv)) (inv_mem hv)
    have hs2 : s ^ 2 ∈ szT₁ L T :=
      hCt _ hs2U (mem_centralizer_singleton_iff.mp (h.le (pow_mem hs 2)))
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁
      (h.mem_sup_zpowers_of_sq_mem_of_card_sylow hS2 hcyc hs hs2)
    have hwU : w ∈ U₁ := hHU₁ (mem_sup_left hw)
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · left
      rw [hz1, mul_one]
      exact mul_mem hv hwU
    · right
      rw [hz1, show v * (w * t) * t⁻¹ = v * w by group]
      exact mul_mem hv hwU
  have hU₁2 : IsPGroup 2 U₁ := IsPGroup.of_card (n := 6 * f) (by rw [hU₁card, ← pow_mul, mul_comm])
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hU₁2 h.isPGroup hTU₁
  have hPsyl : ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
    by_contra hns
    obtain ⟨z, hzN, hzP, Q, hQ2, hPQ, hzQ⟩ := exists_normalizer_not_mem_of_not_isSylow hP2 hns
    have hztP : z * t * z⁻¹ ∈ P := (mem_normalizer_iff.mp hzN t).mp (mem_sup_right htT)
    have hzt2 : (z * t * z⁻¹) ^ 2 = 1 := by
      rw [show (z * t * z⁻¹) ^ 2 = z * t ^ 2 * z⁻¹ by rw [sq, sq]; group, hR.t_sq, mul_one,
        mul_inv_cancel]
    have hztU : z * t * z⁻¹ ∈ U₁ ⊔ zpowers t := by
      rcases hinvP _ hztP hzt2 with h1 | h1
      · exact absurd h1 (hnot z)
      · have e : z * t * z⁻¹ = (z * t * z⁻¹ * t⁻¹) * t := by group
        rw [e]
        exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))
    obtain ⟨u, hu, hut⟩ := hconj z hztU
    have hmt : u⁻¹ * z ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc u⁻¹ * z * t = u⁻¹ * (z * t * z⁻¹) * z := by group
        _ = u⁻¹ * (u * t * u⁻¹) * z := by rw [hut]
        _ = t * (u⁻¹ * z) := by group
    have hmQ : u⁻¹ * z ∈ Q := mul_mem (inv_mem (hPQ (mem_sup_left hu))) hzQ
    have hRT : Q ⊓ centralizer ({t} : Set G) = T := by
      have hR2 : IsPGroup 2 (Q ⊓ centralizer ({t} : Set G) : Subgroup G) :=
        hQ2.to_le inf_le_left
      obtain ⟨a, -, ha⟩ :=
        exists_conj_mem_of_isSylowOf h.isSylowOf_centralizer inf_le_right hR2
      have hle : (Q ⊓ centralizer ({t} : Set G)).map (MulAut.conj a⁻¹).toMonoidHom ≤ T := by
        rintro _ ⟨x, hx, rfl⟩
        simpa [MulAut.conj_apply] using ha x hx
      have h1 := Subgroup.card_le_of_le hle
      rw [Subgroup.card_map_of_injective (MulAut.conj a⁻¹).injective] at h1
      exact (Subgroup.eq_of_le_of_card_ge (le_inf ((le_sup_right : T ≤ P).trans hPQ) h.le)
        h1).symm
    have hmT : u⁻¹ * z ∈ T := by rw [← hRT]; exact mem_inf.mpr ⟨hmQ, hmt⟩
    apply hzP
    have e : z = u * (u⁻¹ * z) := by group
    rw [e]
    exact mul_mem (mem_sup_left hu) (mem_sup_right hmT)
  obtain ⟨S, hSeq⟩ := hPsyl
  have hG : IsSimpleGroup G := h.setting.1
  obtain ⟨a₀, b₀, hab⟩ : ∃ a b : G, a * b ≠ b * a := h.setting.2.1
  have hPidx : ¬ 2 ∣ P.index := hSeq ▸ S.not_dvd_index
  have hPU₁ : P ≤ normalizer (U₁ : Set G) := sup_le Subgroup.le_normalizer hTU₁
  have hcycP : ∃ b ∈ P, ∀ s ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ U₁ := by
    obtain ⟨b, hbT, hb⟩ := hcyc
    refine ⟨b, mem_sup_right hbT, fun x hx => ?_⟩
    obtain ⟨u, hu, s, hs, rfl⟩ := hPmem x hx
    obtain ⟨k, hk⟩ := hb s hs
    refine ⟨k, ?_⟩
    have hbk : (b ^ k)⁻¹ * u * (b ^ k) ∈ U₁ :=
      (mem_normalizer_iff''.mp (hTU₁ (zpow_mem hbT k)) u).mp hu
    rw [show (b ^ k)⁻¹ * (u * s) = ((b ^ k)⁻¹ * u * b ^ k) * ((b ^ k)⁻¹ * s) by group]
    exact mul_mem hbk (hHU₁ (mem_sup_left hk))
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) (P := P) (Q := U₁) (u := t)
      hP2 hPidx (fun s hs q hq => (mem_normalizer_iff.mp (hPU₁ hs) q).mp hq) hcycP
      (mem_sup_right htT) htU₁
      (fun g k _ => by
        rw [pow_mul, h.sq_eq_one, one_pow, mul_one, inv_mul_cancel]
        exact one_mem _)
      (fun g hgP _ => by
        have hy2 : (g⁻¹ * t * g) ^ 2 = 1 := by
          rw [show (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g by rw [sq, sq]; group, h.sq_eq_one,
            mul_one, inv_mul_cancel]
        rcases hinvP _ hgP hy2 with h1 | h1
        · exact Or.inl h1
        · right
          have h2 := (mem_normalizer_iff''.mp htN _).mp h1
          rwa [show t⁻¹ * (g⁻¹ * t * g * t⁻¹) * t = t⁻¹ * (g⁻¹ * t * g) by group] at h2)
    with ⟨N, hN, hNcyc, -, htN'⟩ | ⟨g, hgQ, -⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hN1 | hN1
    · apply hab
      have : IsCyclic (G ⧸ N) := hNcyc
      have hcomm := (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center (by
        rw [QuotientGroup.ker_mk', hN1]
        exact bot_le)
      exact hcomm.is_comm.comm a₀ b₀
    · exact htN' (hN1 ▸ mem_top t)
  · exact hnot g⁻¹ (by rwa [inv_inv])

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
