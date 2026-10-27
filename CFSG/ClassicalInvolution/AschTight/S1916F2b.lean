module

public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.Quasithin.Recognition.M12AscTrans
public import CFSG.ClassicalInvolution.AschTight.S1911Case2c

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mul_self_eq_of_conj_eq_mul [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V) {r : G}
    (hrR : r ∈ (S : Subgroup G) ⊓ K) (hrt : r * t * r⁻¹ = t * z) : r * r = z := by
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hrinv := S1911.conj_eq_inv_of_conj_eq_mul hDT hrR hrt
  have hrW : r ∉ W := fun hrW => by
    have : r * t * r⁻¹ = t := by rw [S1911.comm_of_mem hd r hrW t (S1911.mem_W hDT)]; group
    rw [this] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hUR : K ⊓ W ≤ (S : Subgroup G) ⊓ K := fun x hx => ⟨hd.hWS hx.2, hx.1⟩
  have hidxU : ((K ⊓ W).subgroupOf ((S : Subgroup G) ⊓ K)).index = 2 := by
    have h2 := Subgroup.relIndex_mul_card (H := K ⊓ W) (K := (S : Subgroup G) ⊓ K)
    rw [inf_eq_left.mpr hUR, S1911.card_inf_eq hd] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hr2U : r * r ∈ K ⊓ W := by
    have key := (Subgroup.mul_mem_iff_of_index_two hidxU
      (a := (⟨r, hrR⟩ : ↥((S : Subgroup G) ⊓ K))) (b := ⟨r, hrR⟩)).mpr Iff.rfl
    exact Subgroup.mem_subgroupOf.mp key
  have h3 := hrinv _ hr2U
  have e1 : r * (r * r) * r⁻¹ = r * r := by group
  rw [e1] at h3
  have h4 : (r * r) * (r * r) = 1 := by
    calc (r * r) * (r * r) = (r * r) * (r * r)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  rcases hI.unique _ (K.mul_mem hrR.2 hrR.2) h4 with h5 | h5
  · exfalso
    rcases hI.unique r hrR.2 h5 with h6 | h6
    · exact hrW (h6 ▸ W.one_mem)
    · exact hrW (h6 ▸ Hall196.mem_W_of_sec19DataT hDT)
  · exact h5

omit [Finite G] in
theorem mul_self_mem_of_coset {X X₀ : Subgroup G} {e : G} (heX : e ∈ X) (he2 : e * e = 1)
    (hn : ∀ x ∈ X, ∀ w ∈ X₀, x * w * x⁻¹ ∈ X₀) (hcos : ∀ a ∈ X, a ∈ X₀ ∨ a * e ∈ X₀) :
    ∀ x ∈ X, x * x ∈ X₀ := by
  intro x hx
  rcases hcos x hx with h | h
  · exact X₀.mul_mem h h
  · have hee : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    have h' : e * x ∈ X₀ := by
      have h2 := hn e heX (x * e) h
      have e1 : e * (x * e) * e⁻¹ = e * x := by rw [hee, mul_assoc, mul_assoc, he2, mul_one]
      rwa [e1] at h2
    have e2 : x * x = (x * e) * (e * x) := by
      rw [mul_assoc, ← mul_assoc e, he2, one_mul]
    rw [e2]
    exact X₀.mul_mem h h'

theorem exists_conj_mem_W [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {e : G}
    (heA : e ∈ (S : Subgroup G) ⊓ sec19X K z) (heW : e ∉ W) (he2 : e * e = 1) :
    ∃ a ∈ sec19X K z, a⁻¹ * e * a ∈ W := by
  by_contra hcon
  push Not at hcon
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have ef := S1911.etaYForm p f G K z S W L t V hDT
  have hKX := le_sec19X hd.tight.branch.member
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    hd.hSz.trans (sd_normalizer_eq hd).ge
  have hzW := Hall196.mem_W_of_sec19DataT hDT
  have hWA : W ≤ (S : Subgroup G) ⊓ sec19X K z := le_inf hd.hWS (S1911.le_sec19X hd)
  have hindex : W.relIndex ((S : Subgroup G) ⊓ sec19X K z) = 2 := by
    have h2 := Subgroup.relIndex_mul_card (H := W) (K := (S : Subgroup G) ⊓ sec19X K z)
    rw [inf_eq_left.mpr hWA, S1911.inf_sec19X_eq_of_case2 hDT h1, S1911.card_inf_sup hDT,
      ← S1911.inf_sec19X_eq_of_case2 hDT h1] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  obtain ⟨X₀, -, hX₀n, -, heX₀, hcos, -⟩ := CFSG.Quasithin.thompson_transfer_index_two_sub
    (sec19X K z) ((S : Subgroup G) ⊓ sec19X K z) W inf_le_right (S.isPGroup'.to_le inf_le_left)
    (fun R hRX hR2 hle => (isSylow2In_inf_sec19X hd).2.2 R hRX hR2 hle) hindex he2 heA hcon
  have hsq := mul_self_mem_of_coset heA.2 he2 hX₀n hcos
  have hcomm : ∀ x ∈ sec19X K z, ∀ y ∈ sec19X K z, x * y * x⁻¹ * y⁻¹ ∈ X₀ := by
    intro x hx y hy
    have e1 : x * y * x⁻¹ * y⁻¹ = (x * x) * ((x⁻¹ * y) * (x⁻¹ * y)) * (y⁻¹ * y⁻¹) := by group
    rw [e1]
    exact X₀.mul_mem (X₀.mul_mem (hsq x hx) (hsq _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy)))
      (hsq _ (Subgroup.inv_mem _ hy))
  have hKX₀ : K ≤ X₀ := by
    have hperf := hd.tight.branch.member.perfect
    rw [← Subgroup.commutator_eq_self (H := K)]
    refine Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_
    rw [commutatorElement_def]
    exact hcomm g₁ (hKX h₁) g₂ (hKX h₂)
  obtain ⟨-, -, -, hVcyc, -⟩ := hDT.memV
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le (hDT.leW.trans hd.hWS)
  obtain ⟨w₀, hw₀V, hw₀t⟩ :=
    exists_mul_self_eq_of_isCyclic hDT.invL (S1911.le_member hDT) hVcyc hV2 ef.four
  have htX₀ : t ∈ X₀ := hw₀t ▸ hsq w₀ (S1911.le_sec19X hd (hDT.leW hw₀V))
  obtain ⟨r, hrR, hrt⟩ := S1911.exists_conj_eq_mul hDT
  have hrr := mul_self_eq_of_conj_eq_mul hDT hrR hrt
  have hrW : r ∉ W := fun hrW => by
    have : r * t * r⁻¹ = t := by rw [S1911.comm_of_mem hd r hrW t (S1911.mem_W hDT)]; group
    rw [this] at hrt
    exact hI.ne_one (mul_eq_left.mp hrt.symm)
  have hrA : r ∈ (S : Subgroup G) ⊓ sec19X K z := ⟨hrR.1, hKX hrR.2⟩
  obtain ⟨w, hw⟩ : ∃ w, w = r⁻¹ * e := ⟨_, rfl⟩
  have hwW : w ∈ W := by
    have hidx : (W.subgroupOf ((S : Subgroup G) ⊓ sec19X K z)).index = 2 := hindex
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨r⁻¹, ((S : Subgroup G) ⊓ sec19X K z).inv_mem hrA⟩ :
        ↥((S : Subgroup G) ⊓ sec19X K z))) (b := ⟨e, heA⟩)).mpr
      (iff_of_false (fun h => hrW (by
          have := W.inv_mem (Subgroup.mem_subgroupOf.mp h)
          simpa using this)) (fun h => heW (Subgroup.mem_subgroupOf.mp h)))
    rw [hw]
    exact Subgroup.mem_subgroupOf.mp key
  have hew : r * w = e := by rw [hw]; group
  have hrz : r⁻¹ = r * z := by
    calc r⁻¹ = r⁻¹ * (z * z) := by rw [hI.sq, mul_one]
      _ = r⁻¹ * ((r * r) * (r * r)) := by rw [hrr]
      _ = r * (r * r) := by group
      _ = r * z := by rw [hrr]
  have hwrw : w * r * w = r * z := by
    have h1 : r * w * (r * w) = 1 := by rw [hew]; exact he2
    calc w * r * w = r⁻¹ * (r * w * (r * w)) := by group
      _ = r⁻¹ := by rw [h1, mul_one]
      _ = r * z := hrz
  have hww : w * w = (r⁻¹ * (w * r * w⁻¹ * r⁻¹)⁻¹ * r) * z := by
    calc w * w = w * r⁻¹ * w⁻¹ * (w * r * w) := by group
      _ = w * r⁻¹ * w⁻¹ * (r * z) := by rw [hwrw]
      _ = (r⁻¹ * (w * r * w⁻¹ * r⁻¹)⁻¹ * r) * z := by group
  have hwN : w ∈ Subgroup.normalizer (K : Set G) := hSN (hd.hWS hwW)
  have hcK : w * r * w⁻¹ * r⁻¹ ∈ K :=
    K.mul_mem ((Subgroup.mem_normalizer_iff.mp hwN r).mp hrR.2) (K.inv_mem hrR.2)
  have hrWW : ∀ x ∈ W, r * x * r⁻¹ ∈ W := fun x hx =>
    S1911.conjSub_eq_of_mem_inf hd hrR ▸ conj_mem_conjSub hx
  have hcW : w * r * w⁻¹ * r⁻¹ ∈ W := by
    have e1 : w * r * w⁻¹ * r⁻¹ = w * (r * w⁻¹ * r⁻¹) := by group
    rw [e1]
    exact W.mul_mem hwW (hrWW _ (W.inv_mem hwW))
  have hrU : ∀ x ∈ K ⊓ W, r⁻¹ * x * r ∈ K ⊓ W := by
    intro x hx
    have hr' : r⁻¹ ∈ (S : Subgroup G) ⊓ K := ((S : Subgroup G) ⊓ K).inv_mem hrR
    refine ⟨K.mul_mem (K.mul_mem (K.inv_mem hrR.2) hx.1) hrR.2, ?_⟩
    have h2 : r⁻¹ * x * r⁻¹⁻¹ ∈ conjSub r⁻¹ W := conj_mem_conjSub (n := r⁻¹) hx.2
    rw [S1911.conjSub_eq_of_mem_inf hd hr', inv_inv] at h2
    exact h2
  have hwwU : w * w ∈ K ⊓ W := by
    rw [hww]
    exact (K ⊓ W).mul_mem (hrU _ ((K ⊓ W).inv_mem ⟨hcK, hcW⟩)) ⟨hI.mem, hzW⟩
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
  obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hwmem
  have hvW : v ∈ W := hDT.leW hv
  have hvv : v * v = 1 := by
    have h2 : v * v = (u * u)⁻¹ * (w * w) := by
      rw [← huv]
      have hc := ef.comm u hu.1 v hvW
      calc v * v = (u * u)⁻¹ * (u * (u * v) * v) := by group
        _ = (u * u)⁻¹ * (u * (v * u) * v) := by rw [hc]
        _ = (u * u)⁻¹ * (u * v * (u * v)) := by group
    have h3 : v * v ∈ K := by
      rw [h2]
      exact K.mul_mem (K.inv_mem (K.mul_mem hu.2 hu.2)) hwwU.1
    have h4 : v * v ∈ V ⊓ K := ⟨V.mul_mem hv hv, h3⟩
    rw [S1911.inf_member_eq_bot hDT, Subgroup.mem_bot] at h4
    exact h4
  have hvX₀ : v ∈ X₀ := by
    rcases hDT.invL.unique v (S1911.le_member hDT hv) hvv with h | h
    · rw [h]
      exact X₀.one_mem
    · rw [h]
      exact htX₀
  apply heX₀
  rw [← hew, ← huv]
  exact X₀.mul_mem (hKX₀ hrR.2) (X₀.mul_mem (hKX₀ hu.2) hvX₀)

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
