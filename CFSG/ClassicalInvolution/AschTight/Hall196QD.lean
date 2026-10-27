module

public import CFSG.ClassicalInvolution.AschTight.S1916Sec
public import CFSG.ClassicalInvolution.AschTight.Hall196Main

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mem_W_of_sec19DataT [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V) : z ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hcard := S1911.card_inf_eq_card hDT
  have h2 : IsPGroup 2 ↥(K ⊓ W) := S.isPGroup'.to_le (inf_le_right.trans hd.hWS)
  have hz := AscL62.mem_of_uniqueInvolution_of_pGroup hI inf_le_left h2
    (by rw [hcard]; have := ef.four; omega)
  exact hz.2

theorem exists_quat_elem [IsSimpleGroup G] (hstar : C19_11aTmp p f)
    (hDT : Sec19DataT p f K z S W L t V) (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) :
    ∃ q ∈ (S : Subgroup G) ⊓ sec19Y K z, q ∉ W ⊓ sec19Y K z ∧ q * q = z ∧
      q * t * q⁻¹ = z * t ∧ (∀ c ∈ W ⊓ sec19Y K z, q * c * q⁻¹ = c⁻¹) ∧
      (∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, x ∉ W ⊓ sec19Y K z → q⁻¹ * x ∈ W ⊓ sec19Y K z) ∧
      Nat.card ↥((S : Subgroup G) ⊓ sec19Y K z) = 2 * Nat.card ↥(W ⊓ sec19Y K z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  have hcomm : ∀ x ∈ (S : Subgroup G) ⊓ sec19Y K z, ∀ w ∈ W,
      x * w * x⁻¹ * w⁻¹ ∈ W ⊓ sec19Y K z := by
    intro x hx w hw
    refine ⟨W.mul_mem ((Subgroup.mem_normalizer_iff.mp (ef.normalizes hx) w).mp hw)
      (W.inv_mem hw), ?_⟩
    have hw' : w * x⁻¹ * w⁻¹ ∈ sec19Y K z := by
      rw [← conjSub_sec19Y hd.tight (hd.hSz (hd.hWS hw))]
      exact conj_mem_conjSub (Subgroup.inv_mem _ hx.2)
    have e : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx.2 hw'
  have hstar' := fun x hx hxt => mem_inf_of_commute hstar hDT ef (x := x) hx hxt
  have hCP : W ⊓ sec19Y K z ≤ (S : Subgroup G) ⊓ sec19Y K z := inf_le_inf_right _ hd.hWS
  have hC4 : 4 ≤ Nat.card ↥(W ⊓ sec19Y K z) := ef.card ▸ ef.four
  have hC2 : IsPGroup 2 ↥(W ⊓ sec19Y K z) := S.isPGroup'.to_le (inf_le_left.trans hd.hWS)
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hd.hWS)
  have hPC : ¬ (S : Subgroup G) ⊓ sec19Y K z ≤ W ⊓ sec19Y K z := by
    intro h
    obtain ⟨a, b, ha4, -, -, hbab, hcl⟩ := hQ
    have haP : a ∈ (S : Subgroup G) ⊓ sec19Y K z := hcl ▸ Subgroup.subset_closure (by simp)
    have hbP : b ∈ (S : Subgroup G) ⊓ sec19Y K z := hcl ▸ Subgroup.subset_closure (by simp)
    have hab := ef.comm a (h haP).1 b (h hbP).1
    have h2 : a ^ 2 = 1 := by
      have e : a⁻¹ = a := by
        rw [← hbab]
        calc b * a * b⁻¹ = a * b * b⁻¹ := by rw [hab]
          _ = a := by group
      rw [sq]
      nth_rewrite 2 [← e]
      exact mul_inv_cancel a
    have := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
    omega
  obtain ⟨q, hqP, hqC, zc, hzcC, hzc1, hzc2, hzcu, hqt, hqinv, -, hq2, hcoset, hcardP, -⟩ :=
    exists_swap_of_not_le ef.comm hDT.leW inf_le_left ef.cyclic hVcyc ef.card.symm hC4 hC2 hV2
      hDT.memT hDT.invL.ne_one hDT.invL.sq hCP ef.normalizes hcomm hstar' hPC
  have hzz : z = zc :=
    (hzcu z ⟨mem_W_of_sec19DataT hDT, S1916.sd_mem_Y hd⟩ hI.sq).resolve_left hI.ne_one
  have hq1 : q ≠ 1 := fun h => hqC (h ▸ Subgroup.one_mem _)
  have hq2' : q * q = zc := hq2.resolve_left fun h => hqC
    ((IsQuaternionSub.eq_of_mul_self_eq_one hQ hqP (hCP hzcC) h hzc2 hq1 hzc1) ▸ hzcC)
  rw [← hzz] at hq2' hqt
  exact ⟨q, hqP, hqC, hq2', hqt, hqinv, hcoset, hcardP⟩

theorem mul_conj_mem_of_quat [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V) {q : G}
    (hqP : q ∈ (S : Subgroup G) ⊓ sec19Y K z) (hq2 : q * q = z) (hqt : q * t * q⁻¹ = z * t)
    {v : G} (hv : v ∈ V) : v * (q * v * q⁻¹) ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hzW := mem_W_of_sec19DataT hDT
  have hvW : v ∈ W := hDT.leW hv
  have hqN := ef.normalizes hqP
  have hqvW : q * v * q⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hqN v).mp hvW
  set w := v * (q * v * q⁻¹) with hw
  have hwW : w ∈ W := W.mul_mem hvW hqvW
  have hqw : q * w * q⁻¹ = w := by
    have h1 : q * (q * v * q⁻¹) * q⁻¹ = v := by
      have e : q * (q * v * q⁻¹) * q⁻¹ = (q * q) * v * (q * q)⁻¹ := by group
      rw [e, hq2, ef.comm z hzW v hvW]
      group
    calc q * w * q⁻¹ = (q * v * q⁻¹) * (q * (q * v * q⁻¹) * q⁻¹) := by rw [hw]; group
      _ = (q * v * q⁻¹) * v := by rw [h1]
      _ = w := by rw [hw, ef.comm _ hqvW v hvW]
  have hVN : V ≤ Subgroup.normalizer ((W ⊓ K : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyW := hDT.leW hy
    constructor
    · rintro ⟨hxW, hxK⟩
      have e : y * x * y⁻¹ = x := by rw [ef.comm y hyW x hxW]; group
      rw [e]
      exact ⟨hxW, hxK⟩
    · rintro ⟨hxW, hxK⟩
      have hx' : x ∈ W := by
        have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
        rw [e]
        exact W.mul_mem (W.mul_mem (W.inv_mem hyW) hxW) hyW
      have e : y * x * y⁻¹ = x := by rw [ef.comm y hyW x hx']; group
      rw [e] at hxW hxK
      exact ⟨hx', hxK⟩
  have hwmem : w ∈ (((W ⊓ K) ⊔ V : Subgroup G) : Set G) := ef.supU ▸ hwW
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (W ⊓ K) V hVN] at hwmem
  obtain ⟨u, hu, v', hv', huv⟩ := Set.mem_mul.mp hwmem
  have hqu : u * q = q * u := S1916.sd_commute_R_Q hd u ⟨hd.hWS hu.1, hu.2⟩ q hqP
  have hqv' : q * v' * q⁻¹ = v' := by
    have e : v' = u⁻¹ * w := by rw [← huv]; group
    have h2 : q * u⁻¹ * q⁻¹ = u⁻¹ := by
      have : q * u * q⁻¹ = u := by rw [← hqu]; group
      calc q * u⁻¹ * q⁻¹ = (q * u * q⁻¹)⁻¹ := by group
        _ = u⁻¹ := by rw [this]
    calc q * v' * q⁻¹ = (q * u⁻¹ * q⁻¹) * (q * w * q⁻¹) := by rw [e]; group
      _ = v' := by rw [h2, hqw, e]
  by_contra hwK
  have hv'1 : v' ≠ 1 := by
    rintro rfl
    apply hwK
    rw [← huv, mul_one]
    exact hu.2
  have hV2 : IsPGroup 2 (Subgroup.zpowers v') :=
    (S.isPGroup'.to_le (hDT.leW.trans hd.hWS)).to_le (Subgroup.zpowers_le.mpr hv')
  have htv := mem_zpowers_of_isUniqueInvolution hDT.invL (le_of_sec19DataT hDT hv') hV2 hv'1
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp htv
  have hqti : q * t * q⁻¹ = t := by
    rw [← hi, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hqv']
  rw [hqt] at hqti
  have : z = 1 := by
    calc z = z * t * t⁻¹ := by group
      _ = 1 := by rw [hqti]; group
  exact hI.ne_one this

theorem eq_one_or_eq_of_mem_inf (hd : Sec19Data p f K z S W)
    (hQ : IsQuaternionSub ((S : Subgroup G) ⊓ sec19Y K z)) {r : G}
    (hr : r ∈ (S : Subgroup G) ⊓ K) (hrY : r ∈ sec19Y K z) : r = 1 ∨ r = z := by
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hr2 : r * r = 1 := S1916.IsQuaternionSub.mul_self_eq_one_of_central hQ ⟨hr.1, hrY⟩
    (fun y hy => S1916.sd_commute_R_Q hd r hr y hy)
  exact hI.unique r hr.2 hr2

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
