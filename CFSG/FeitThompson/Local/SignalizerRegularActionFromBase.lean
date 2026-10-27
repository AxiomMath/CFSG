module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.CentralizerTransitiveOnMaximalsSigmaCoreQ
import CFSG.FeitThompson.Local.SigmaOvergroupConjugacy
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.OddOrder.MaximalSubgroupsSelfNormalizing
import CFSG.FeitThompson.Foundations.NormalHallIntersectionHall
import CFSG.FeitThompson.Local.SigmaCoreConjugation

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep09

universe u

variable {G : Type*} [Group G]

theorem conjSub_eq_self_of_mem {M : Subgroup G} {g : G} (hg : g ∈ M) : conjSub g M = M := by
  rw [conjSub_def]; exact map_conj_eq_self (inv_mem hg)

theorem mem_normalizer_of_conjSub_eq {M : Subgroup G} {a b : G}
    (h : conjSub a M = conjSub b M) : b * a⁻¹ ∈ normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 : (a⁻¹ * y * a) ∈ conjSub a M ↔ (a⁻¹ * y * a) ∈ conjSub b M := by rw [h]
  rw [mem_conjSub, mem_conjSub] at h1
  simpa [mul_assoc] using h1

theorem sigmaCore_conjSub [Finite G] (g : G) (M : Subgroup G) :
    sigmaCore (conjSub g M) = conjSub g (sigmaCore M) := by
  rw [conjSub_def, conjSub_def, sigmaCore_map_conj]

theorem normal_subgroupOf_inf_of_le_normalizer {S C : Subgroup G}
    (h : C ≤ normalizer (S : Set G)) : ((S ⊓ C).subgroupOf C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
  exact ⟨(Subgroup.mem_normalizer_iff.1 (h g.2) _).1 hn.1,
    mul_mem (mul_mem g.2 hn.2) (inv_mem g.2)⟩

theorem relIndex_inf_dvd_index [Finite G] {S C N : Subgroup G} [(S.subgroupOf N).Normal]
    (hSN : S ≤ N) (hCN : C ≤ N) : (S ⊓ C).relIndex C ∣ S.index := by
  have e : S.relIndex C
      = ((S.subgroupOf N ⊓ C.subgroupOf N).subgroupOf (C.subgroupOf N)).index := by
    rw [index_inf_subgroupOf, Subgroup.relIndex_subgroupOf hCN]
  rw [Subgroup.inf_relIndex_right S C, e]
  exact (index_inf_subgroupOf_dvd_index (S.subgroupOf N) (C.subgroupOf N)).trans
    (Subgroup.relIndex_dvd_index_of_le hSN)

theorem FTS_signalizer_regular_action_from_base
    (h₁ : Statements.FTS_sigma_prime_separation.{u}) :
    Statements.FTS_signalizer_regular_action_from_base.{u} := by
  intro G _ _ hG x _hxU M hM N hNco hCN hxMN hsd hQ
  have := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hodd := hG.odd_natCard
  have hsolv := hG.isSolvable_of_ne_top
  obtain ⟨hMco, hxM⟩ := mem_sigmaSupportingMaximals.1 hM
  obtain ⟨Q, hQx, hQp, hQN⟩ := hQ
  have hSM : sigmaCore N ⊓ M = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hsd.inf_eq_bot]
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (sigmaCore_le N)))
  have hR₀S : centIn (sigmaCore N) {x} ≤ sigmaCore N := centIn_le _ _
  have hR₀C : centIn (sigmaCore N) {x} ≤ centralizer ({x} : Set G) := centIn_le_centralizer _ _
  have hcomm : ∀ r ∈ centIn (sigmaCore N) {x}, r * x * r⁻¹ = x := by
    intro r hr
    have h := mem_centralizer_singleton_iff.1 (hR₀C hr)
    rw [h, mul_inv_cancel_right]
  have htrans : ∀ T ∈ sigmaSupportingMaximals (G := G) x,
      ∃ v ∈ centIn (sigmaCore N) {x}, conjSub v M = T := by
    intro T hT
    obtain ⟨hTco, hxT⟩ := mem_sigmaSupportingMaximals.1 hT
    obtain ⟨u, hu, huMT⟩ := FTS_sigma_prime_centralizer_transitivity h₁ G hG (Nat.card Q) hQp Q rfl
      ⟨M, hMco, hQx.trans (zpowers_le.2 hxM)⟩ M ⟨hMco, hQx.trans (zpowers_le.2 hxM)⟩
      T ⟨hTco, hQx.trans (zpowers_le.2 hxT)⟩
    have huN : u ∈ N := hQN hu
    obtain ⟨s, hs, t, ht, rfl⟩ := hsd.exists_mul huN
    have htN : t ∈ N := (inf_le_right : M ⊓ N ≤ N) ht
    have htM : t ∈ M := (inf_le_left : M ⊓ N ≤ M) ht
    have hv : t⁻¹ * s * t ∈ sigmaCore N := by
      have h := (Subgroup.mem_normalizer_iff.1 (le_normalizer_sigmaCore N (inv_mem htN)) s).1 hs
      simpa using h
    have hst : s * t = t * (t⁻¹ * s * t) := by group
    have hTv : conjSub (t⁻¹ * s * t) M = T :=
      calc conjSub (t⁻¹ * s * t) M = conjSub (t⁻¹ * s * t) (conjSub t M) := by
            rw [conjSub_eq_self_of_mem htM]
        _ = conjSub (t * (t⁻¹ * s * t)) M := conjSub_conjSub _ _ _
        _ = T := by rw [← hst, huMT]
    refine ⟨t⁻¹ * s * t, mem_centIn.2 ⟨hv, ?_⟩, hTv⟩
    set v := t⁻¹ * s * t with hvdef
    have hxT' : v * x * v⁻¹ ∈ M := mem_conjSub.1 (hTv ▸ sigmaCore_le T hxT)
    have hxN : x ∈ N := (inf_le_right : M ⊓ N ≤ N) hxMN
    have hw1 : v * x * v⁻¹ * x⁻¹ ∈ sigmaCore N := by
      have h2 : x * v⁻¹ * x⁻¹ ∈ sigmaCore N :=
        (Subgroup.mem_normalizer_iff.1 (le_normalizer_sigmaCore N hxN) v⁻¹).1 (inv_mem hv)
      have h3 : v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) := by group
      rw [h3]
      exact mul_mem hv h2
    have hw2 : v * x * v⁻¹ * x⁻¹ ∈ M := mul_mem hxT' (inv_mem ((inf_le_left : M ⊓ N ≤ M) hxMN))
    have hw : v * x * v⁻¹ = x := by
      have hb : v * x * v⁻¹ * x⁻¹ ∈ (⊥ : Subgroup G) := hSM ▸ Subgroup.mem_inf.2 ⟨hw1, hw2⟩
      rw [Subgroup.mem_bot] at hb
      exact mul_inv_eq_one.1 hb
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (mul_inv_eq_iff_eq_mul.1 hw).symm
  have hkey : ∀ v ∈ centIn (sigmaCore N) {x}, ∀ r ∈ centIn (sigmaCore N) {x},
      ∀ r' ∈ centIn (sigmaCore N) {x},
      conjSub r (conjSub v M) = conjSub r' (conjSub v M) → r = r' := by
    intro v hv r hr r' hr' heq
    rw [conjSub_conjSub, conjSub_conjSub] at heq
    have hmem : v * r' * (v * r)⁻¹ ∈ M := by
      have h := mem_normalizer_of_conjSub_eq heq
      rwa [normalizer_coe_eq_of_isCoatom hna hMco] at h
    have hmemS : v * r' * (v * r)⁻¹ ∈ sigmaCore N := by
      have h : v * r' * (v * r)⁻¹ = v * (r' * r⁻¹) * v⁻¹ := by group
      rw [h]
      exact mul_mem (mul_mem (hR₀S hv) (mul_mem (hR₀S hr') (inv_mem (hR₀S hr)))) (inv_mem (hR₀S hv))
    have hb : v * r' * (v * r)⁻¹ ∈ (⊥ : Subgroup G) := hSM ▸ Subgroup.mem_inf.2 ⟨hmemS, hmem⟩
    rw [Subgroup.mem_bot] at hb
    exact (mul_left_cancel (mul_inv_eq_one.1 hb)).symm
  have hact : ∀ r ∈ centIn (sigmaCore N) {x}, ∀ N₁ ∈ sigmaSupportingMaximals (G := G) x,
      conjSub r N₁ ∈ sigmaSupportingMaximals (G := G) x := by
    intro r hr N₁ hN₁
    obtain ⟨hN₁co, hxN₁⟩ := mem_sigmaSupportingMaximals.1 hN₁
    refine mem_sigmaSupportingMaximals.2 ⟨isCoatom_conjSub hN₁co r, ?_⟩
    rw [sigmaCore_conjSub, mem_conjSub, hcomm r hr]
    exact hxN₁
  refine ⟨⟨hR₀C, ?_, ?_⟩, hact, ?_, ?_⟩
  ·
    rw [centIn_def]
    exact normal_subgroupOf_inf_of_le_normalizer (hCN.trans (le_normalizer_sigmaCore N))
  ·
    have hπ : IsPiNumber (sigmaPrimes N) (Nat.card (centIn (sigmaCore N) {x})) :=
      (isPiSubgroup_iff_isPiNumber.1 (isPiSubgroup_sigmaCore N)).of_dvd
        (Subgroup.card_dvd_of_le hR₀S) Nat.card_pos.ne'
    have hdvd : (centIn (sigmaCore N) {x}).relIndex (centralizer ({x} : Set G))
        ∣ (sigmaCore N).index := by
      rw [centIn_def]
      exact relIndex_inf_dvd_index (sigmaCore_le N) hCN
    have hπ' : IsPiNumber (sigmaPrimes N)ᶜ
        ((centIn (sigmaCore N) {x}).relIndex (centralizer ({x} : Set G))) :=
      (isHallSubgroup_sigmaCore hna hodd hsolv hNco).index.of_dvd hdvd
        Subgroup.index_ne_zero_of_finite
    refine hπ.coprime_of_compl hπ' Nat.card_pos.ne' ?_
    exact fun h => Subgroup.index_ne_zero_of_finite
      (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.relIndex_dvd_index_of_le hR₀C))
  ·
    intro N₁ hN₁ N₂ hN₂
    obtain ⟨v₁, hv₁, hv₁eq⟩ := htrans N₁ hN₁
    obtain ⟨v₂, hv₂, hv₂eq⟩ := htrans N₂ hN₂
    refine ⟨v₁⁻¹ * v₂, ⟨mul_mem (inv_mem hv₁) hv₂, ?_⟩, ?_⟩
    · rw [← hv₁eq, conjSub_conjSub, mul_inv_cancel_left, hv₂eq]
    · rintro r ⟨hr, hrN⟩
      refine hkey v₁ hv₁ r hr (v₁⁻¹ * v₂) (mul_mem (inv_mem hv₁) hv₂) ?_
      rw [conjSub_conjSub (v₁⁻¹ * v₂) v₁ M, mul_inv_cancel_left, hv₂eq, hv₁eq, hrN]
  ·
    rw [sigmaMultiplicity_eq_ncard, ← Nat.card_coe_set_eq]
    refine Nat.card_eq_of_bijective
      (fun r : centIn (sigmaCore N) {x} => (⟨conjSub (r : G) M, hact r r.2 M hM⟩ :
        sigmaSupportingMaximals (G := G) x)) ⟨?_, ?_⟩
    · intro r r' h
      refine Subtype.ext (hkey 1 (one_mem _) r r.2 r' r'.2 ?_)
      simpa using congrArg Subtype.val h
    · intro T
      obtain ⟨v, hv, hvT⟩ := htrans T T.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvT⟩

end

end CFSG.FeitThompson.Proofs
