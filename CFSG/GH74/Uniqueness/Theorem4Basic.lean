module

public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Section5Prop52

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem exists_t4Cand_of_inverted (hZ : IsInvariantInvolutionSet Z) {z : X} (hzZ : z ∈ Z)
    (hzM : z ∈ M) {k : X} (hkM : k ∈ M) (hk1 : k ≠ 1) (hkodd : Odd (orderOf k))
    (hzk : z * k * z⁻¹ = k⁻¹) (hΩ : 2 ≤ (omegaFix M (zpowers k : Set X)).ncard) :
    ∃ (p : ℕ) (W : Subgroup X), T4Cand Z M z p W := by
  have hn1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  have hn0 : orderOf k ≠ 0 := (orderOf_pos k).ne'
  have hpp : (orderOf k).minFac.Prime := Nat.minFac_prime hn1
  have hpn : (orderOf k).minFac ∣ orderOf k := Nat.minFac_dvd _
  have hp2 : (orderOf k).minFac ≠ 2 := fun h => by
    rw [h] at hpn
    exact (Nat.not_even_iff_odd.mpr hkodd) (even_iff_two_dvd.mpr hpn)
  set p := (orderOf k).minFac with hp
  have : Fact p.Prime := ⟨hpp⟩
  set κ := k ^ (orderOf k / p) with hκ
  have hκord : orderOf κ = p := orderOf_pow_orderOf_div hn0 hpn
  have hzz : z * z = 1 := mul_self_of_orderOf_eq_two (hZ.1 z hzZ)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzκ : z * κ * z⁻¹ = κ⁻¹ := by rw [hκ, ← conj_pow, hzk, inv_pow]
  have hκM : κ ∈ M := M.pow_mem hkM _
  have hzW : z ∈ normalizer ((zpowers κ : Subgroup X) : Set X) := by
    have hmap : ∀ y ∈ zpowers κ, z * y * z⁻¹ ∈ zpowers κ := by
      intro y hy
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
      have : z * κ ^ j * z⁻¹ = (κ ^ j)⁻¹ := by rw [← conj_zpow, hzκ, inv_zpow]
      rw [this]
      exact (zpowers κ).inv_mem (zpow_mem_zpowers κ j)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hmap y hy, fun hy => ?_⟩
    have h1 := hmap _ hy
    have e : z * (z * y * z⁻¹) * z⁻¹ = y := by
      rw [hzinv]
      calc z * (z * y * z) * z = (z * z) * y * (z * z) := by group
        _ = y := by rw [hzz]; group
    rwa [e] at h1
  have hcard : Nat.card (zpowers κ) = p := by rw [Nat.card_zpowers, hκord]
  refine ⟨p, zpowers κ, ⟨hzZ, hzM, hpp, hp2, ?_, ?_, hzW, ?_, ?_, ?_⟩⟩
  · exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  · exact (zpowers_le).mpr hκM
  · have hodd : Odd (Nat.card (zpowers κ)) := by rw [hcard]; exact hpp.odd_of_ne_two hp2
    rw [← closure_invertedSet_eq_commutator (hZ.1 z hzZ) hodd hzW]
    refine le_antisymm ((Subgroup.closure_le _).mpr fun d hd => hd.1) ?_
    exact (zpowers_le).mpr (Subgroup.subset_closure ⟨mem_zpowers κ, hzκ⟩)
  · intro hbot
    have : κ = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [this, orderOf_one] at hκord
    exact hpp.one_lt.ne hκord
  · refine hΩ.trans (Set.ncard_le_ncard (omegaFix_anti ?_) (Set.toFinite _))
    intro y hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    rw [hκ, ← zpow_natCast, ← zpow_mul]
    exact zpow_mem_zpowers k _

theorem not_t4Cand_of_prop71 (hZ : IsInvariantInvolutionSet Z) (h71 : Prop71Stmt Z M)
    (z : X) (p : ℕ) (W : Subgroup X) : ¬ T4Cand Z M z p W := by
  intro hW
  obtain ⟨W', hW'c, hW'max⟩ := Set.exists_max_image {W' : Subgroup X | T4Cand Z M z p W'}
    (fun W' => Nat.card (CFSG.OddInversion.invertedSet W' z)) (Set.toFinite _) ⟨W, hW⟩
  have hmax : T4Max Z M z p W' := ⟨hW'c, fun W'' hW'' => hW'max W'' hW''⟩
  have h1 := h71 z p W' hmax
  have h2 := hW'c.one_lt_card_invertedSet hZ
  omega

theorem ZDSetup.theorem4b_of_noCand (S : ZDSetup X Z M)
    (hno : ∀ z p W, ¬ T4Cand Z M z p W) : Theorem4bStmt Z M := by
  intro z hzZ hzM W hWodd hWM hzW
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨w, hw, hwne⟩, ⟨β, hβ, hβM⟩⟩ := hcon
  have hz2 : orderOf z = 2 := S.invariant.1 z hzZ
  have hkI := commutator_mem_invertedSet hz2 hzW hw
  have hk1 : z * w * z⁻¹ * w⁻¹ ≠ 1 := by
    intro h1
    apply hwne
    have : z * w = w * z := by
      have h2 : z * w * z⁻¹ = w := by
        have := congrArg (· * w) h1
        simpa using this
      calc z * w = (z * w * z⁻¹) * z := by group
        _ = w * z := by rw [h2]
    exact this
  have hkodd : Odd (orderOf (z * w * z⁻¹ * w⁻¹)) :=
    Odd.of_dvd_nat hWodd (Subgroup.orderOf_dvd_natCard W hkI.1)
  have hMW : M ∈ omegaFix M (W : Set X) :=
    ⟨self_mem_omega M, fun g hg =>
      conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hWM hg))⟩
  have hkW : zpowers (z * w * z⁻¹ * w⁻¹) ≤ W := (zpowers_le).mpr hkI.1
  have hsub : ({M, β} : Set (Subgroup X)) ⊆ omegaFix M (zpowers (z * w * z⁻¹ * w⁻¹) : Set X) := by
    intro y hy
    rcases hy with rfl | rfl
    · exact omegaFix_anti (fun g hg => hkW hg) hMW
    · exact omegaFix_anti (fun g hg => hkW hg) hβ
  have h2 : 2 ≤ (omegaFix M (zpowers (z * w * z⁻¹ * w⁻¹) : Set X)).ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_pair hβM.symm] at this
  obtain ⟨p, W', hW'⟩ := exists_t4Cand_of_inverted S.invariant hzZ hzM (hWM hkI.1) hk1 hkodd hkI.2 h2
  exact hno z p W' hW'

theorem ZDSetup.exists_t4Cand_of_not_doublyTransitive (S : ZDSetup X Z M) (h57 : Cor57Stmt Z M)
    (hnd : ¬ DoublyTransitive M) : ∃ (z : X) (p : ℕ) (W : Subgroup X), T4Cand Z M z p W := by
  classical
  have hZ := S.invariant
  have h := S.prodDisc
  obtain ⟨t₀, ht₀, ht₀M⟩ := S.exists_mem_not_mem
  obtain ⟨z₀, hz₀, hz₀M⟩ := S.exists_mem_inter
  obtain ⟨hmodd, hmge, hmgt⟩ := h.prop36e hZ S.gen S.two_le_twoRank ht₀ ht₀M hz₀ hz₀M
  have hm1 : zNum Z M ≠ 1 := by omega
  have hm0 : zNum Z M ≠ 0 := hmodd.pos.ne'
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpm
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hpm)
  obtain ⟨s, hs, Q, hQp, hQ3, hsQ, hcnt, hQfix⟩ := (h57 hnd p hp hp2).1
  obtain ⟨lam, ⟨hlamΩ, hlams⟩, -⟩ := h.existsUnique_fixed_point hZ hs
  obtain ⟨g, hg⟩ := hlamΩ
  have hsl : s ∈ lam := (h.conjugate_eq_iff_mem ⟨g, hg⟩).mp hlams
  have hzM : g * s * g⁻¹ ∈ M := by
    rw [← hg, mem_conjugate_iff] at hsl
    exact hsl
  have hzZ : g * s * g⁻¹ ∈ Z := by
    have := hZ.2 s hs g⁻¹
    rwa [inv_inv] at this
  have hQM : conjugate Q g⁻¹ ≤ M := by
    have h1 : Q ≤ lam := hQfix lam ⟨g, hg⟩ hlams
    have h2 : conjugate Q g⁻¹ ≤ conjugate lam g⁻¹ := conjugate_mono h1 g⁻¹
    rwa [← hg, conjugate_conjugate_inv] at h2
  have hzQ : g * s * g⁻¹ ∈ normalizer ((conjugate Q g⁻¹ : Subgroup X) : Set X) := by
    rw [normalizer_conjugate, mem_conjugate_iff]
    have : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
    rw [this]
    exact hsQ
  have hQ'p : IsPGroup p (conjugate Q g⁻¹) := isPGroup_conjugate hQp g⁻¹
  have hQ'odd : Odd (Nat.card (conjugate Q g⁻¹)) := odd_card_of_isPGroup hp hp2 hQ'p
  have hQ'3 : 3 ≤ (omegaFix M ((conjugate Q g⁻¹ : Subgroup X) : Set X)).ncard := by
    rwa [ncard_omegaFix_conjugate]
  have hcnt' : zCosetNum Z (conjugate Q g⁻¹) (g * s * g⁻¹) = zNumShare Z M p := by
    have := zCosetNum_conjugate hZ Q s g⁻¹
    rw [inv_inv] at this
    rw [this]
    exact hcnt
  have hI : Nat.card (CFSG.OddInversion.invertedSet (conjugate Q g⁻¹) (g * s * g⁻¹)) =
      zNumShare Z M p := by
    rw [← zCosetNum_eq_card_invertedSet hZ hzZ hQ'odd hzQ]
    exact hcnt'
  have hshare : 1 < zNumShare Z M p := by
    unfold zNumShare
    exact Nat.one_lt_pow (Nat.Prime.factorization_pos_of_dvd hp hm0 hpm).ne' hp.one_lt
  obtain ⟨k, hkI, hk1⟩ : ∃ k ∈ CFSG.OddInversion.invertedSet (conjugate Q g⁻¹) (g * s * g⁻¹),
      k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : CFSG.OddInversion.invertedSet (conjugate Q g⁻¹) (g * s * g⁻¹) ⊆ {1} :=
      fun k hk => hcon k hk
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton, ← Nat.card_coe_set_eq, hI] at this
    omega
  have hkodd : Odd (orderOf k) :=
    Odd.of_dvd_nat hQ'odd (Subgroup.orderOf_dvd_natCard _ hkI.1)
  have hkQ : zpowers k ≤ conjugate Q g⁻¹ := (zpowers_le).mpr hkI.1
  have h2 : 2 ≤ (omegaFix M (zpowers k : Set X)).ncard :=
    (by omega : 2 ≤ 3).trans (hQ'3.trans
      (Set.ncard_le_ncard (omegaFix_anti (fun x hx => hkQ hx)) (Set.toFinite _)))
  obtain ⟨p', W', hW'⟩ := exists_t4Cand_of_inverted hZ hzZ hzM (hQM hkI.1) hk1 hkodd hkI.2 h2
  exact ⟨_, p', W', hW'⟩

theorem ZDSetup.theorem4a_of_noCand (S : ZDSetup X Z M) (h57 : Cor57Stmt Z M)
    (hno : ∀ z p W, ¬ T4Cand Z M z p W) : DoublyTransitive M := by
  by_contra hnd
  obtain ⟨z, p, W, hW⟩ := S.exists_t4Cand_of_not_doublyTransitive h57 hnd
  exact hno z p W hW

theorem ZDSetup.theorem4_of_noCand (S : ZDSetup X Z M) (h57 : Cor57Stmt Z M)
    (hno : ∀ z p W, ¬ T4Cand Z M z p W) : Theorem4Stmt Z M :=
  ⟨S.theorem4a_of_noCand h57 hno, S.theorem4b_of_noCand hno⟩

theorem ZDSetup.theorem4_of_prop71 (S : ZDSetup X Z M) (h57 : Cor57Stmt Z M)
    (h71 : Prop71Stmt Z M) : Theorem4Stmt Z M :=
  S.theorem4_of_noCand h57 (not_t4Cand_of_prop71 S.invariant h71)

@[expose] def Cor3Stmt (Z : Set X) (M : Subgroup X) : Prop :=
  ¬ DoublyTransitive M → ∃ t ∈ Z, t ∉ M ∧ ∀ z ∈ Z, z ∈ M → lSubgroup M z t = ⊤

theorem ZDSetup.cor3 (S : ZDSetup X Z M) (h57 : Cor57Stmt Z M) (h63 : Prop63Stmt Z M) :
    Cor3Stmt Z M := by
  intro hnd
  have hZ := S.invariant
  have h := S.prodDisc
  obtain ⟨z₀, p, W, hW⟩ := S.exists_t4Cand_of_not_doublyTransitive h57 hnd
  obtain ⟨β, hβ, hβM⟩ := hW.exists_ne_base
  have hβΩ : β ∈ omega M := (h.mem_omegaFix_iff.mp hβ).1
  obtain ⟨t, ht, hMt⟩ := h.exists_swap hZ (self_mem_omega M) hβΩ
  have htM : t ∉ M := fun htM =>
    hβM (by rw [← hMt]; exact (h.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM)
  have h1 : lSubgroup M z₀ t = ⊤ := h63 z₀ p W hW t ht htM (hMt ▸ hβ)
  refine ⟨t, ht, htM, fun z hz hzM => ?_⟩
  have hz₀L : z₀ ∈ lSubgroup M z t :=
    h.inter_le_lSubgroup hZ ht htM hz hzM ⟨hW.mem_Z, hW.mem_M⟩
  have htL : t ∈ lSubgroup M z t :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  rw [eq_top_iff, ← h1]
  exact sup_le (sup_le ((Subgroup.zpowers_le).mpr hz₀L) ((Subgroup.zpowers_le).mpr htL)) le_sup_right

end CFSG.GH74.Uniqueness
