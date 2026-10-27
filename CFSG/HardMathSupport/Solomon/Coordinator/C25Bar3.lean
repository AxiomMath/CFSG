module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar1
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal
  CFSG.HardMathSupport.Solomon.LocalBalance

section Ranks

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem c25_isPGroup_of_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E) : IsPGroup 3 ↥E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

theorem c25_pRank_eq {E : Subgroup G} (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : CFSG.pRank 3 ↥E = k := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine le_antisymm (CFSG.SectionRank.pRank_le (by norm_num) fun E' _ _ => ?_)
    (CFSG.SectionRank.le_pRank (by norm_num) le_rfl ?_ ?_)
  · rw [← hk]
    exact Subgroup.card_le_card_group E'
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x _ => ?_⟩
    · apply Subtype.ext
      exact hE.1.is_comm.comm a.1 b.1
    · exact Subtype.ext (by simpa using hE.2 x x.2)
  · rw [Subgroup.card_top, hk]

omit [Finite G] in
theorem c25_isElemAbelian_map {H : Type*} [Group H] (f : G →* H) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.map f) := CFSG.Open.IsElemAbelian.map hE _

omit [Finite G] in
theorem c25_isElemAbelian_subgroupOf {E : Subgroup G} (N : Subgroup G) (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 (E.subgroupOf N) := CFSG.Open.IsElemAbelian.subgroupOf hE N

omit [Finite G] in
theorem c25_isElemAbelian_mono {E F : Subgroup G} (h : E ≤ F) (hF : IsElemAbelian 3 F) :
    IsElemAbelian 3 E := CFSG.Open.IsElemAbelian.mono hF h

end Ranks

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem c25Img_isElemAbelian {K B : Subgroup G} (hBel : IsElemAbelian 3 B) :
    IsElemAbelian 3 (c25Img K B) :=
  c25_isElemAbelian_map _ (c25_isElemAbelian_subgroupOf _ hBel)

omit [Finite G] in
theorem card_c25Img {K B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (c25Img K B) = (dQ K).relIndex B := by
  rw [← c25Rho_range hBN, ← Subgroup.index_ker, c25Rho_ker]
  rfl

theorem c25_exists_sub {K B : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) {S : Subgroup (MulAut (barOf 3 K))}
    (hS : S ≤ c25Img K B) (hcard : Nat.card (c25Img K B) ≤ 3 * Nat.card S) :
    ∃ E : Subgroup G, E ≤ B ∧ c25Img K E = S ∧ pRank 3 B - 1 ≤ pRank 3 E := by
  set ρ := c25Rho hBN with hρ
  have hrange : ρ.range = c25Img K B := c25Rho_range hBN
  set EB : Subgroup ↥B := S.comap ρ with hEB
  set E : Subgroup G := EB.map B.subtype with hE
  have hEB' : E ≤ B := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨E, hEB', ?_, ?_⟩
  ·
    unfold c25Img
    ext s
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨b, hbEB, hbγ⟩ := Subgroup.mem_subgroupOf.1 hγ
      have hbS : ρ b ∈ S := hbEB
      have : ρ b = barAut 3 K γ := by
        show barAut 3 K (Subgroup.inclusion hBN b) = barAut 3 K γ
        congr 1
        exact Subtype.ext hbγ
      rwa [← this]
    · intro hs
      have hsr : s ∈ ρ.range := by rw [hrange]; exact hS hs
      obtain ⟨b, rfl⟩ := hsr
      refine ⟨Subgroup.inclusion hBN b, Subgroup.mem_subgroupOf.2 ⟨b, hs, rfl⟩, rfl⟩
  ·
    have hEel : IsElemAbelian 3 E := c25_isElemAbelian_mono hEB' hBel
    obtain ⟨m, hm⟩ := (c25_isPGroup_of_elemAbelian hBel).exists_card_eq
    obtain ⟨e, he⟩ := (c25_isPGroup_of_elemAbelian hEel).exists_card_eq
    have hcardE : Nat.card E = Nat.card EB := Subgroup.card_map_of_injective B.subtype_injective
    have hidx : Nat.card EB * EB.index = Nat.card B := Subgroup.card_mul_index EB
    have hSA : S ≤ ρ.range := by rw [hrange]; exact hS
    have hidx2 : EB.index * Nat.card S = Nat.card (c25Img K B) := by
      rw [hEB, Subgroup.index_comap, ← hrange]
      have h1 := Subgroup.card_mul_index (S.subgroupOf ρ.range)
      have h2 : Nat.card (S.subgroupOf ρ.range) = Nat.card S :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv
      rw [h2] at h1
      rw [hrange] at h1 ⊢
      unfold Subgroup.relIndex
      rw [mul_comm]
      exact h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    have hidx3 : EB.index ≤ 3 := by
      by_contra hcon
      push Not at hcon
      have := Nat.mul_le_mul_right (Nat.card S) hcon
      omega
    have hdvd : EB.index ∣ 3 ^ m := ⟨Nat.card EB, by rw [← hm, ← hidx, mul_comm]⟩
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj1 : j ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    have hee : 3 ^ e * 3 ^ j = 3 ^ m := by
      rw [← he, hcardE, ← hjeq, hidx, hm]
    have hem : e + j = m := by
      rw [← pow_add] at hee
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hee
    rw [c25_pRank_eq hBel hm, c25_pRank_eq hEel he]
    omega

theorem c25_transfer {K B : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hBN : B ≤ Subgroup.normalizer (K : Set G)) (τ : Subgroup G → Subgroup G)
    (σ : Subgroup (barOf 3 K) → Subgroup (barOf 3 K)) (hτ : ∀ X, τ X ≤ X)
    (hτσ : ∀ E : Subgroup G, E ≤ B →
      σ (barX 3 K (K ⊓ Subgroup.centralizer (E : Set G))) ≤
        barX 3 K (τ (K ⊓ Subgroup.centralizer (E : Set G))))
    (hY : ⊤ ≤ ⨆ (S : Subgroup (MulAut (barOf 3 K)))
      (_ : S ≤ c25Img K B ∧ Nat.card (c25Img K B) ≤ 3 * Nat.card S), σ (c25Fix S)) :
    K ≤ (⨆ (E : Subgroup G) (_ : E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E),
      τ (K ⊓ Subgroup.centralizer (E : Set G))) ⊔ GLAPPrimeCoreOf 3 K := by
  set Γ : Subgroup G := ⨆ (E : Subgroup G) (_ : E ≤ B ∧ pRank 3 B - 1 ≤ pRank 3 E),
      τ (K ⊓ Subgroup.centralizer (E : Set G)) with hΓ
  have hΓK : Γ ≤ K := by
    refine iSup₂_le fun E _ => (hτ _).trans inf_le_left
  have hle : ⨆ (S : Subgroup (MulAut (barOf 3 K)))
      (_ : S ≤ c25Img K B ∧ Nat.card (c25Img K B) ≤ 3 * Nat.card S), σ (c25Fix S) ≤
        barX 3 K Γ := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨E, hEB, hES, hrk⟩ := c25_exists_sub hBel hBN hS.1 hS.2
    have hE3 : IsPGroup 3 ↥E := c25_isPGroup_of_elemAbelian (c25_isElemAbelian_mono hEB hBel)
    have hEN : E ≤ Subgroup.normalizer (K : Set G) := hEB.trans hBN
    rw [← hES, ← c25_barX_centralizer hEN hE3]
    refine (hτσ E hEB).trans (barX_mono 3 ?_)
    exact le_iSup₂_of_le E ⟨hEB, hrk⟩ le_rfl
  intro k hk
  have hkY : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) ∈ barX 3 K Γ := hle (hY (Subgroup.mem_top _))
  obtain ⟨x, hx, hxk⟩ := hkY
  have hxΓ : (x : G) ∈ Γ := Subgroup.mem_subgroupOf.1 hx
  have hxk' : x⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore 3 ↥K := by
    have : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) x =
        (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : barOf 3 K) := hxk
    exact QuotientGroup.eq.1 this
  have hn : (x : G)⁻¹ * k ∈ GLAPPrimeCoreOf 3 K := ⟨_, hxk', rfl⟩
  have : k = (x : G) * ((x : G)⁻¹ * k) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxΓ) (Subgroup.mem_sup_right hn)

end Transfer

end CFSG.HardMathSupport.Solomon.Coordinator
