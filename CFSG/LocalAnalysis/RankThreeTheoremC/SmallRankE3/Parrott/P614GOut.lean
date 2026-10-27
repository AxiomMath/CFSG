module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614GA5
public import CFSG.LieType.ChevTwo.OutData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {M B H S K : Subgroup G} {z : G}

theorem isPGroup_rhoS (c : Ctx M B H S K z) : IsPGroup 2 c.rhoS :=
  (c.isPGroup_S.comap_subtype (K := H)).map _

theorem rhoS_inf_inner (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H) :
    c.rhoS ⊓ (MulAut.conj : Kbar K →* MulAut (Kbar K)).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨⟨t, ht⟩, htS, rfl⟩, hinn⟩
  rw [mem_bot, c.rho_eq_one_of_mem_core (c.mem_core_of_inner hR0 (mem_subgroupOf.mp htS) hinn)]

theorem comm_S_B (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    (hKD : CFSG.LieType.ChevTwo.Chev2KDOut) :
    ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ * b⁻¹ ∈ pCoreOf 2 H := by
  intro s hs b hb
  set P := (B.subgroupOf H).map c.rho with hP
  have hP3 : IsPGroup 3 P := (c.B_three.comap_subtype (K := H)).map _
  have hPT : P ≤ normalizer (c.rhoS : Set (MulAut (Kbar K))) := by
    refine le_normalizer_of_conj ?_
    rintro _ ⟨⟨b', hb'H⟩, hb', rfl⟩ _ ⟨⟨s', hs'H⟩, hs', rfl⟩
    have hb'S := c.B_le_normalizer_S (mem_subgroupOf.mp hb')
    have hmem : b' * s' * b'⁻¹ ∈ S :=
      (mem_normalizer_iff.mp hb'S _).1 (mem_subgroupOf.mp hs')
    have e : c.rho ⟨b', hb'H⟩ * c.rho ⟨s', hs'H⟩ * (c.rho ⟨b', hb'H⟩)⁻¹ =
        c.rho ⟨b' * s' * b'⁻¹, c.S_le hmem⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact c.rho_mem_rhoS hmem
  have h := hKD (Kbar K) c.isSimpleGroup c.exists_ne_comm c.isChevTwo 3 Nat.prime_three
    (by norm_num) P c.rhoS hP3 c.isPGroup_rhoS hPT
  have hbS := c.B_le_normalizer_S hb
  have hcS : s * b * s⁻¹ * b⁻¹ ∈ S := by
    have e : s * b * s⁻¹ * b⁻¹ = s * (b * s⁻¹ * b⁻¹) := by group
    rw [e]
    exact S.mul_mem hs ((mem_normalizer_iff.mp hbS _).1 (S.inv_mem hs))
  refine c.mem_core_of_inner hR0 hcS ?_
  have hmem := h (Subgroup.commutator_mem_commutator (c.rho_mem_rhoS hs)
    (mem_map_of_mem c.rho (mem_subgroupOf.mpr hb : (⟨b, c.B_le hb⟩ : ↥H) ∈ B.subgroupOf H)))
  have e : ⁅c.rho ⟨s, c.S_le hs⟩, c.rho ⟨b, c.B_le hb⟩⁆ =
      c.rho ⟨s * b * s⁻¹ * b⁻¹, c.S_le hcS⟩ := by
    rw [← map_commutatorElement]
    rfl
  rw [e] at hmem
  exact hmem

theorem comm_S_S (c : Ctx M B H S K z) (hR0 : kRad H S K = pCoreOf 2 H)
    (hOut : CFSG.LieType.ChevTwo.Chev2OutTwoRank) :
    ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ pCoreOf 2 H := by
  intro s hs t ht
  have h := (hOut (Kbar K) c.isSimpleGroup c.exists_ne_comm c.isChevTwo c.rhoS
    c.isPGroup_rhoS).1 _ (c.rho_mem_rhoS hs) _ (c.rho_mem_rhoS ht)
  have hcS : s * t * s⁻¹ * t⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht)
  refine c.mem_core_of_inner hR0 hcS ?_
  have e : ⁅c.rho ⟨s, c.S_le hs⟩, c.rho ⟨t, c.S_le ht⟩⁆ =
      c.rho ⟨s * t * s⁻¹ * t⁻¹, c.S_le hcS⟩ := by
    rw [← map_commutatorElement]
    rfl
  rw [e] at h
  exact h

theorem mem_normalizer_zpowers_sup (c : Ctx M B H S K z) {t g : G} (ht : t ∈ H) (hg : g ∈ H)
    (h : g * t * g⁻¹ * t⁻¹ ∈ pCoreOf 2 H) :
    g ∈ normalizer ((zpowers t ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  have key : ∀ n : G, n ∈ H → n * t * n⁻¹ * t⁻¹ ∈ pCoreOf 2 H →
      ∀ x ∈ zpowers t ⊔ pCoreOf 2 H, n * x * n⁻¹ ∈ zpowers t ⊔ pCoreOf 2 H := by
    intro n hn hc x hx
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (zpowers t) (pCoreOf 2 H)
      (zpowers_le.mpr (c.H_le_normalizer_core ht))] at hx
    obtain ⟨y, hy, o, ho, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    have e : n * (t ^ j * o) * n⁻¹ = (n * t * n⁻¹) ^ j * (n * o * n⁻¹) := by
      rw [conj_zpow]
      group
    rw [e]
    have hnt : n * t * n⁻¹ ∈ zpowers t ⊔ pCoreOf 2 H := by
      have e2 : n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t := by group
      rw [e2]
      exact mul_mem (mem_sup_right hc) (mem_sup_left (mem_zpowers t))
    exact mul_mem (zpow_mem hnt j) (mem_sup_right (c.core_conj_mem hn ho))
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg h x, fun hx => ?_⟩
  have hc' : g⁻¹ * t * g⁻¹⁻¹ * t⁻¹ ∈ pCoreOf 2 H := by
    have e : g⁻¹ * t * g⁻¹⁻¹ * t⁻¹ = g⁻¹ * (g * t * g⁻¹ * t⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact c.core_conj_mem (H.inv_mem hg) (inv_mem h)
  have := key g⁻¹ (H.inv_mem hg) hc' _ hx
  simpa [mul_assoc] using this

theorem fix_mem_kbarM (c : Ctx M B H S K z)
    (hSS : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ pCoreOf 2 H)
    (hSB : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ * b⁻¹ ∈ pCoreOf 2 H) {t : G} (ht : t ∈ S)
    (htO : t ∉ pCoreOf 2 H) (q : Kbar K) (hq : c.rho ⟨t, c.S_le ht⟩ q = q) : q ∈ kbarM K M := by
  have htH := c.S_le ht
  have hN : normalizer ((zpowers t ⊔ pCoreOf 2 H : Subgroup G) : Set G) ≤ M := by
    refine c.norm_le _ (lt_of_le_of_ne le_sup_right fun h => htO (h ▸ mem_sup_left
      (mem_zpowers t))) (sup_le (zpowers_le.mpr ht) c.core_le) (sup_le (fun s hs => ?_)
        (fun b hb => ?_))
    · exact c.mem_normalizer_zpowers_sup htH (c.S_le hs) (hSS s hs t ht)
    · refine c.mem_normalizer_zpowers_sup htH (c.B_le hb) ?_
      have e : b * t * b⁻¹ * t⁻¹ = (t * b * t⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem (hSB t ht b hb)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [c.rho_mk, c.mk_eq_mk_iff] at hq
  have hkt : (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ pCoreOf 2 H := by
    have e : (k : G) * t * (k : G)⁻¹ * t⁻¹ = k * ((t * k * t⁻¹)⁻¹ * k) * (k : G)⁻¹ := by group
    rw [e]
    exact c.core_conj_mem (c.K_le k.2) hq
  exact mk_mem_kbarM k.2 (hN (c.mem_normalizer_zpowers_sup htH (c.K_le k.2) hkt))

end Ctx

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614G
