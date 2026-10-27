module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIISetup
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIOmega
public import CFSG.ClassicalInvolution.Asc77.AscT3CIIC7
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

section Commutators

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_singleton_of_conj_eq {c z : G} (h : c * z * c⁻¹ = z) :
    c ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem commutator_mem_oddCore_sup {M M' T : Subgroup G}
    (hM'M : M' ≤ Subgroup.normalizer (M : Set G)) (hMM' : M ≤ Subgroup.normalizer (M' : Set G))
    (hc : ∀ x ∈ T, ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M)
    (hc' : ∀ x ∈ T, ∀ m ∈ M', ⁅x, m⁆ ∈ oddCoreOf M') :
    ∀ x ∈ T, ∀ n ∈ M ⊔ M', ⁅x, n⁆ ∈ oddCoreOf (M ⊔ M') := by
  have hN : M ⊔ M' ≤ Subgroup.normalizer (M : Set G) := sup_le Subgroup.le_normalizer hM'M
  have hN' : M ⊔ M' ≤ Subgroup.normalizer (M' : Set G) := sup_le hMM' Subgroup.le_normalizer
  have hOM : oddCoreOf M ≤ oddCoreOf (M ⊔ M') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self M).trans le_sup_left)
      (fun g hg => mem_normalizer_oddCore_of_mem_normalizer (hN hg)) (oddCoreOf_odd_natCard M)
  have hOM' : oddCoreOf M' ≤ oddCoreOf (M ⊔ M') :=
    Balance.le_oddCoreIn_of_normalizes ((oddCoreOf_le_self M').trans le_sup_right)
      (fun g hg => mem_normalizer_oddCore_of_mem_normalizer (hN' hg)) (oddCoreOf_odd_natCard M')
  intro x hx n hn
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M M' hM'M] at hn
  obtain ⟨m, hm, m', hm', rfl⟩ := hn
  rw [commutatorElement_mul_right']
  refine (oddCoreOf _).mul_mem (hOM (hc x hx m hm)) ?_
  exact mem_normalizer_oddCoreOf_of_mem_normalizer
    (Subgroup.le_normalizer (Subgroup.mem_sup_left hm)) (hOM' (hc' x hx m' hm'))

end Commutators

section Step

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem mem_sup_of_hexagon (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {J M Ms : Subgroup G}
    {zJ v : G} (hzJ : IsUniqueInvolution J zJ) (hVU : Subgroup.zpowers v ∈ USet Ω)
    (hVJ : Subgroup.zpowers v ≤ J) (hvv : v * v ∈ M ⊔ Ms) : zJ ∈ M ⊔ Ms := by
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := hΩ.isPGroup_of_mem_USet hp hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := hΩ.exists_data_of_mem_USet hp hVU
  obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic hzJ hVJ hVc hV2 h4V
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hww, ← (Commute.refl v).mul_zpow]
  exact Subgroup.zpow_mem _ hvv k

theorem aSet_mem_dComp (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {M : Subgroup G}
    (hM : M ∈ Ω) (hL : ∃ L ∈ omegaNbr Ω M, L ∉ twinSet Ω M) {J' : Subgroup G}
    (hJ' : J' ∈ aSet Ω M) : J' ∈ dComp Ω M := by
  obtain ⟨L, hLnbr, hLtw⟩ := hL
  obtain ⟨zM, zJ, hv⟩ := hJ'
  obtain ⟨v, Ms, hVU, hVJ, -, hMsM, htw, hvv⟩ :=
    exists_hexagon_data hp hq hΩ hM hv.mem hv.hzK hv.hzJ hv.star hv.not_nbr hv.no_conj
  have hMsT : Ms ∈ twinSet Ω M := by rw [htw]; exact Or.inr rfl
  have hMsΩ : Ms ∈ Ω := hMsT.1
  have hzMs : IsUniqueInvolution Ms zM := isUniqueInvolution_of_mem_twinSet hv.hzK hMsT
  have hzJM : zJ ∈ M ⊔ Ms := mem_sup_of_hexagon hp hΩ hv.hzJ hVU hVJ hvv
  have hLnbr' := hLnbr
  obtain ⟨hLΩ, hLM, T, hTR, hTL, hTN⟩ := hLnbr'
  have hTsyl : IsSylow2In T L :=
    Disconnected.AschTight.Sec7.isSylow2In_of_mem_RSet_of_le hp hΩ hTR hLΩ hTL
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hp hTR
  have hLMs : L ≠ Ms := fun h => hLtw (by rw [htw]; exact Or.inr h)
  have hTC : T ≤ Subgroup.centralizer ({zM} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq
      (hv.hzK.conj_eq (mem_normalizer_iff_conjSub_eq.mp (hTN hx)))
  have hTMs : T ≤ Subgroup.normalizer (Ms : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hMsΩ hLΩ (Ne.symm hLMs) hzMs hTL hT2 (by omega) hTC
  obtain ⟨zL, hzL⟩ := hΩ.exists_uniqueInvolution hp hq hLΩ
  have hcM : ∀ x ∈ T, ∀ m ∈ M, ⁅x, m⁆ ∈ oddCoreOf M := fun x hx m hm =>
    Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hM hLΩ (Ne.symm hLM) hv.hzK hzL
      hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hcMs : ∀ x ∈ T, ∀ m ∈ Ms, ⁅x, m⁆ ∈ oddCoreOf Ms := fun x hx m hm =>
    Thompson.comm_le_oddCore_of_isSylow2In (l6_2 p f) hp hq hΩ hMsΩ hLΩ (Ne.symm hLMs) hzMs hzL
      hTsyl hTC (Subgroup.commutator_mem_commutator hx hm)
  have hMsN : Ms ≤ Subgroup.normalizer (M : Set G) :=
    hΩ.le_normalizer_of_twin hMsΩ hM hMsM hzMs hv.hzK
  have hMN : M ≤ Subgroup.normalizer (Ms : Set G) :=
    hΩ.le_normalizer_of_twin hM hMsΩ (Ne.symm hMsM) hv.hzK hzMs
  have hcN := commutator_mem_oddCore_sup hMsN hMN hcM hcMs
  obtain ⟨q, hqN₀, hqfix⟩ := exists_conj_fixed_involution (N₀ := M ⊔ Ms) hT2 hzJM hv.hzJ.sq
    (fun x hx => mem_normalizer_sup (hTN hx) (hTMs hx)) (fun x hx => hcN x hx zJ hzJM)
  have hqM : q ∈ Subgroup.normalizer (M : Set G) := (sup_le Subgroup.le_normalizer hMsN) hqN₀
  have hJ''Ω : conjSub q J' ∈ Ω := hΩ.conjInvariant q J' hv.mem
  have hzJ'' : IsUniqueInvolution (conjSub q J') (q * zJ * q⁻¹) := hv.hzJ.conj q
  have hcent : T ≤ Subgroup.centralizer ({q * zJ * q⁻¹} : Set G) := fun x hx =>
    mem_centralizer_singleton_of_conj_eq (hqfix x hx)
  have hqMinv : conjSub q⁻¹ M = M :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (M : Set G)).inv_mem hqM)
  have hJ''L : conjSub q J' ≠ L := by
    intro h
    have h1 : conjSub q J' ∈ omegaNbr Ω M := h ▸ hLnbr
    have h2 := omegaNbr_conj hΩ.conjInvariant h1 q⁻¹
    rw [conjSub_inv_conjSub, hqMinv] at h2
    exact hv.not_nbr h2
  have hTJ'' : T ≤ Subgroup.normalizer ((conjSub q J' : Subgroup G) : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hp hq hJ''Ω hLΩ hJ''L hzJ'' hTL hT2 (by omega) hcent
  have hpath : conjSub q J' ∈ dComp Ω M :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single ⟨hLΩ, Or.inl hLnbr⟩)
      ⟨hJ''Ω, Or.inr ⟨hLΩ, hJ''L.symm, T, hTR, hTL, hTJ''⟩⟩
  have hqσ : q ∈ sigmaNorm Ω M := T8.normalizer_le_sigmaNorm hΩ.conjInvariant hM hqM
  exact (hqσ J').mpr hpath

end Step

end CFSG.ClassicalInvolution.Asc77.T3CII
