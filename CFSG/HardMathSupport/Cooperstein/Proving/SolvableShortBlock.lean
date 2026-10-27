module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H]

theorem commutator_eq_of_index_three [Finite H] (Q : Subgroup H) [Q.Normal]
    (hQ2 : ∀ q ∈ Q, ∃ k : ℕ, q ^ 2 ^ k = 1) (hidx : Q.index = 3)
    (hcl1 : ∀ (N : Subgroup H) [N.Normal],
      (∀ g : H, ∃ k : ℕ, (QuotientGroup.mk g : H ⧸ N) ^ 2 ^ k = 1) → N = ⊤) :
    ⁅Q, (⊤ : Subgroup H)⁆ = Q := by
  classical
  have := Fintype.ofFinite H
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set U : Subgroup H := ⁅Q, (⊤ : Subgroup H)⁆ with hU
  have hUn : U.Normal := by rw [hU]; infer_instance
  have hUQ : U ≤ Q := commutator_le_left Q ⊤
  have h3dvd : 3 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← index_mul_card (H := Q), hidx]
    exact dvd_mul_right 3 _
  obtain ⟨t, ht3⟩ := exists_prime_orderOf_dvd_card 3 h3dvd
  have ht3pow : t ^ 3 = 1 := by rw [← ht3]; exact pow_orderOf_eq_one t
  have htQ : t ∉ Q := by
    intro h
    obtain ⟨k, hk⟩ := hQ2 t h
    have h1 : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    rw [ht3] at h1
    have h2 : 3 ∣ 2 ^ k := h1
    have h3 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    norm_num at h3
  have hPtop : Q ⊔ zpowers t = ⊤ := by
    have hle : Q ≤ Q ⊔ zpowers t := le_sup_left
    have hrel := relIndex_mul_index hle
    rw [hidx] at hrel
    have hdvd : Q.relIndex (Q ⊔ zpowers t) ∣ 3 := Dvd.intro _ hrel
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      exact htQ (relIndex_eq_one.mp h1 (mem_sup_right (mem_zpowers t)))
    · have h4 : (Q ⊔ zpowers t).index = 1 := by
        rw [h3] at hrel; omega
      exact index_eq_one.mp h4
  have hdec : ∀ g : H, ∃ q ∈ Q, ∃ s ∈ zpowers t, q * s = g := by
    intro g
    have hg : g ∈ Q ⊔ zpowers t := by rw [hPtop]; exact mem_top g
    exact mem_sup_of_normal_left.mp hg
  set M : Subgroup H := U ⊔ zpowers t with hM
  have hconj_zpow : ∀ (s : H), s ∈ zpowers t → ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro s hs m hm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨u, hu, s', hs', rfl⟩ := mem_sup_of_normal_left.mp hm
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs'
    have e : t ^ n * (u * t ^ k) * (t ^ n)⁻¹ = (t ^ n * u * (t ^ n)⁻¹) * t ^ k := by group
    rw [e]
    exact mul_mem (mem_sup_left (hUn.conj_mem u hu _)) (mem_sup_right (mem_zpowers_iff.mpr ⟨k, rfl⟩))
  have htconj : ∀ q ∈ Q, q * t * q⁻¹ ∈ M := by
    intro q hq
    have hcomm : ⁅t⁻¹, q⁆ ∈ U := by
      have h1 : ⁅q, t⁻¹⁆ ∈ U := commutator_mem_commutator hq (mem_top _)
      rw [← commutatorElement_inv] at h1
      exact inv_mem_iff.mp h1
    have e : q * t * q⁻¹ = t * ⁅t⁻¹, q⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hcomm)
  have hconj_Q : ∀ q ∈ Q, ∀ m ∈ M, q * m * q⁻¹ ∈ M := by
    intro q hq m hm
    obtain ⟨u, hu, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
    have e : q * (u * t ^ n) * q⁻¹ = (q * u * q⁻¹) * (q * t ^ n * q⁻¹) := by group
    have hpow : q * t ^ n * q⁻¹ = (q * t * q⁻¹) ^ n := by
      rw [conj_zpow]
    have hpowmem : q * t ^ n * q⁻¹ ∈ M := by
      rw [hpow]
      exact zpow_mem (htconj q hq) n
    rw [e]
    exact mul_mem (mem_sup_left (hUn.conj_mem u hu _)) hpowmem
  have hMn : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨q, hq, s, hs, rfl⟩ := hdec g
    have e : q * s * m * (q * s)⁻¹ = q * (s * m * s⁻¹) * q⁻¹ := by group
    rw [e]
    exact hconj_Q q hq _ (hconj_zpow s hs m hm)
  have hMtop : M = ⊤ := by
    refine hcl1 M (fun g => ?_)
    obtain ⟨q, hq, s, hs, hg⟩ := hdec g
    obtain ⟨k, hk⟩ := hQ2 q hq
    have hsM : s ∈ M := mem_sup_right hs
    have hs1 : (QuotientGroup.mk s : H ⧸ M) = 1 := (QuotientGroup.eq_one_iff s).mpr hsM
    have hgq : (QuotientGroup.mk g : H ⧸ M) = QuotientGroup.mk q := by
      rw [← hg, QuotientGroup.mk_mul, hs1, mul_one]
    refine ⟨k, ?_⟩
    rw [hgq, ← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
  have hQU : Q ≤ U := by
    intro q hq
    have hqM : q ∈ M := by rw [hMtop]; exact mem_top q
    obtain ⟨u, hu, s, hs, hus⟩ := mem_sup_of_normal_left.mp hqM
    have hsQ : s ∈ Q := by
      have : s = u⁻¹ * q := by rw [← hus]; group
      rw [this]
      exact Q.mul_mem (Q.inv_mem (hUQ hu)) hq
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hs
    obtain ⟨k, hk⟩ := hQ2 _ hsQ
    have h3 : (t ^ n) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht3pow, one_zpow]
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2)
    have h1 : t ^ n = 1 := by
      have := pow_gcd_eq_one.mpr ⟨h3, hk⟩
      rw [hcop, pow_one] at this
      exact this
    rw [← hus, h1, mul_one]
    exact hu
  exact le_antisymm hUQ hQU

variable {G : Type} [Group G]

theorem index_pCore_eq_three {L : Subgroup G} (hL : CFSG.QuasithinUnique.IsShort2 L)
    (hs : Group.IsSolvable L) : (CFSG.pCore 2 L).index = 3 := by
  rcases hL.2.2.2.1 with hq | h3
  · exfalso
    obtain ⟨hperf, _, a, b, hab⟩ := hq
    have hsolv : Group.IsSolvable (L ⧸ CFSG.pCore 2 L) := inferInstance
    obtain ⟨n, hn⟩ := hsolv.solvable
    have htop : derivedSeries (L ⧸ CFSG.pCore 2 L) n = ⊤ :=
      Group.IsPerfect.derivedSeries_eq_top (L ⧸ CFSG.pCore 2 L) n
    have hbt : (⊥ : Subgroup (L ⧸ CFSG.pCore 2 L)) = ⊤ := hn.symm.trans htop
    have hsub : ∀ x y : L ⧸ CFSG.pCore 2 L, x = y := by
      intro x y
      have hx : x ∈ (⊥ : Subgroup (L ⧸ CFSG.pCore 2 L)) := by
        rw [hbt]; exact Subgroup.mem_top x
      have hy : y ∈ (⊥ : Subgroup (L ⧸ CFSG.pCore 2 L)) := by
        rw [hbt]; exact Subgroup.mem_top y
      rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hy]
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [hsub x y])
  · exact h3

theorem blockU_eq_blockQ_of_solvable [Finite G] {L : Subgroup G}
    (hL : CFSG.QuasithinUnique.IsShort2 L) (hs : Group.IsSolvable L) :
    CFSG.QuasithinUnique.blockU L = CFSG.QuasithinUnique.blockQ L := by
  set Q' : Subgroup L := CFSG.pCore 2 L with hQ'
  have hQ2 : ∀ q ∈ Q', ∃ k : ℕ, q ^ 2 ^ k = 1 := by
    intro q hq
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (⟨q, hq⟩ : Q')
    exact ⟨k, congrArg Subtype.val hk⟩
  have hcl1 : ∀ (N : Subgroup L) [N.Normal],
      (∀ g : L, ∃ k : ℕ, (QuotientGroup.mk g : L ⧸ N) ^ 2 ^ k = 1) → N = ⊤ := by
    intro N _ h
    refine hL.1 N (show IsPGroup 2 (L ⧸ N) from fun y => ?_)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact h g
  have hcore : ⁅Q', (⊤ : Subgroup L)⁆ = Q' :=
    commutator_eq_of_index_three Q' hQ2 (index_pCore_eq_three hL hs) hcl1
  have hQmap : CFSG.QuasithinUnique.blockQ L = Q'.map L.subtype := by
    show CFSG.Open.pCoreOf 2 L = _
    rw [CFSG.Open.pCoreOf]
  have hLtop : (⊤ : Subgroup L).map L.subtype = L := by
    ext x
    simp
  have key : ⁅CFSG.QuasithinUnique.blockQ L, L⁆ = (⁅Q', (⊤ : Subgroup L)⁆).map L.subtype := by
    rw [Subgroup.map_commutator, hQmap, hLtop]
  show ⁅CFSG.QuasithinUnique.blockQ L, L⁆ = CFSG.QuasithinUnique.blockQ L
  rw [key, hcore, hQmap]

end CFSG.HardMathSupport.Cooperstein.Proving
