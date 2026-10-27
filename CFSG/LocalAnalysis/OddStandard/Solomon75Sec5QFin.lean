module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QPair
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QQuot

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem R2_of_RCore (h : PairCtx X n z s A A' M M') (hR : h.RCore) {x : X} (hx : x ∈ h.R)
    {j : ℕ} (hj : x ^ (2 ^ j) = 1) : x ∈ zpowers s := by
  obtain ⟨hxz, hxs, hxm⟩ := h.mem_R_iff.1 hx
  rcases hR x hx ⟨j, hj⟩ with h1 | h1
  · rw [h.ker_two hx h1 hj]
    exact one_mem _
  · have hxs' : Commute x s := Subgroup.mem_centralizer_singleton_iff.1 hxs
    have hq : x * s⁻¹ ∈ h.R := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ h.s_mem_R)
    have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
    have hperm : M.permX (x * s⁻¹) = 1 := by
      rw [M.permX_mul h.hn (h.hNz hxz) (Subgroup.inv_mem _ hsN), M.permX_inv h.hn hsN, h1]
      group
    have hj' : (x * s⁻¹) ^ (2 ^ (j + 1)) = 1 := by
      have hsq : s ^ (2 ^ (j + 1)) = 1 := by
        have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact h.sq_s
        rw [pow_succ', pow_mul, hs2, one_pow]
      rw [hxs'.inv_right.mul_pow, inv_pow, hsq, inv_one, mul_one, pow_succ, pow_mul, hj, one_pow]
    have := h.ker_two hq hperm hj'
    have hxe : x = s := by
      have : x * s⁻¹ = 1 := this
      exact mul_inv_eq_one.1 this
    rw [hxe]
    exact Subgroup.mem_zpowers s

theorem exists_decomp (h : PairCtx X n z s A A' M M') (hP : h.swap.RCore) :
    ∃ a ∈ A, ∃ u ∈ zpowers z, ∃ v ∈ oddCoreOf A, s * a = a * s ∧ s = a * u * v := by
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  have hind : M.C.Induces (M.autOf s hsN) (M.permX s) := by
    have := M.induces_perm h.hn s hsN
    rwa [← M.permX_of_mem hsN] at this
  obtain ⟨ā, hā⟩ := M.C.exists_ρ_eq h.hsgn
  have hfix : M.autOf s hsN ā = ā := by
    rw [hind.apply_eq_conj hā ā]
    group
  obtain ⟨a, haA, hsa, hae⟩ := M.exists_lift_cent hsN h.sq_s hfix
  have hperm_a : M.permX a = M.permX s := by rw [M.permX_of_mem_A h.hn haA, hae, hā]
  have haz : a ∈ centralizer ({z} : Set X) := h.hAz haA
  have haN : a ∈ normalizer (A : Set X) := h.hNz haz
  set s₂ : X := a⁻¹ * s with hs₂
  have hsa' : s * a⁻¹ = a⁻¹ * s := by
    calc s * a⁻¹ = a⁻¹ * (a * s) * a⁻¹ := by group
      _ = a⁻¹ * (s * a) * a⁻¹ := by rw [hsa]
      _ = a⁻¹ * s := by group
  have hs₂P : s₂ ∈ h.P := by
    rw [h.mem_P_iff]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mul_mem _ (Subgroup.inv_mem _ haz) h.s_mem_C, ?_⟩
    · calc s₂ * s = (a⁻¹ * s) * s := by rw [hs₂]
        _ = (s * a⁻¹) * s := by rw [hsa']
        _ = s * (a⁻¹ * s) := by group
    · have hz₂ : s₂ ∈ centralizer ({z} : Set X) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ haz) h.s_mem_C
      rw [← M.permX_eq_one_iff h.hn (h.hNz hz₂), hs₂,
        M.permX_mul h.hn (Subgroup.inv_mem _ haN) hsN, M.permX_inv h.hn haN, hperm_a]
      group
  obtain ⟨u, v, hu, hv, huv, ⟨j, hj⟩, hvodd⟩ := exists_twoPart s₂
  have hmemP : ∀ w ∈ zpowers s₂, w ∈ h.P := fun w hw => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact Subgroup.zpow_mem _ hs₂P k
  have huz : u ∈ zpowers z := h.swap.R2_of_RCore hP (hmemP u hu) hj
  have huu : u * u = 1 := by
    rcases (mem_zpowers_iff_of_orderOf_two h.hz).1 huz with h1 | h1
    · rw [h1, one_mul]
    · rw [h1]; exact h.sq_z
  have huv' : u * v = v * u := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.zpow_zpow_self s₂ k l)).eq
  have has₂ : a * s₂ = s := by rw [hs₂]; group
  have hcomm : a * s₂ = s₂ * a := by
    rw [has₂, hs₂]
    calc s = a⁻¹ * (a * s) := by group
      _ = a⁻¹ * (s * a) := by rw [hsa]
      _ = a⁻¹ * s * a := by group
  have h1 : (a * a) * (s₂ * s₂) = 1 := by
    calc (a * a) * (s₂ * s₂) = (a * s₂) * (a * s₂) := by
          calc (a * a) * (s₂ * s₂) = a * (a * s₂) * s₂ := by group
            _ = a * (s₂ * a) * s₂ := by rw [hcomm]
            _ = (a * s₂) * (a * s₂) := by group
      _ = 1 := by rw [has₂]; exact h.sq_s
  have hs₂s₂ : s₂ * s₂ = v * v := by
    rw [huv]
    calc u * v * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [← huv']
      _ = (u * u) * (v * v) := by group
      _ = v * v := by rw [huu, one_mul]
  have hvv : v * v = (a * a)⁻¹ := by
    rw [hs₂s₂] at h1
    exact eq_inv_of_mul_eq_one_right h1
  obtain ⟨t, ht⟩ := hvodd
  have hvA : v ∈ A := by
    have hv1 : v ^ (orderOf v) = 1 := pow_orderOf_eq_one v
    have : v = (v * v) ^ (t + 1) := by
      have e1 : (v * v) ^ (t + 1) = v ^ (2 * t + 2) := by
        rw [← sq, ← pow_mul, show 2 * (t + 1) = 2 * t + 2 by ring]
      rw [e1]
      have : v ^ (2 * t + 2) = v ^ (2 * t + 1) * v := by rw [← pow_succ]
      rw [this, ← ht, hv1, one_mul]
    rw [this, hvv]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ haA haA)) _
  have hvP : v ∈ h.P := hmemP v hv
  have hvO : v ∈ oddCoreOf A := by
    obtain ⟨hvs, hvz, hvm⟩ := h.mem_P_iff.1 hvP
    have hperm_v : M.permX v = 1 := (M.permX_eq_one_iff h.hn (h.hNz hvz)).2 hvm
    set vb : M.K := M.e (QuotientGroup.mk (⟨v, hvA⟩ : ↥A)) with hvb
    have hρ : M.C.ρ vb = 1 := by rw [hvb, ← M.permX_of_mem_A h.hn hvA, hperm_v]
    have hvc : vb ∈ center M.K := (M.C.ρ_eq_one_iff).1 hρ
    have hv2 : vb * vb = 1 := M.C.sq_of_mem_center hvc
    have hvbo : vb ^ (orderOf v) = 1 := by
      have : vb ^ (orderOf v) = M.e (QuotientGroup.mk ((⟨v, hvA⟩ : ↥A) ^ (orderOf v))) := by
        rw [hvb, ← map_pow, ← QuotientGroup.mk_pow]
      rw [this]
      have : (⟨v, hvA⟩ : ↥A) ^ (orderOf v) = 1 := Subtype.ext (by simp)
      rw [this]
      simp
    have hvb1 : vb = 1 := by
      have e : vb ^ (2 * t + 1) = vb := by
        rw [pow_succ, pow_mul, sq, hv2, one_pow, one_mul]
      rw [← e, ← ht, hvbo]
    have h2 : (QuotientGroup.mk (⟨v, hvA⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) = 1 :=
      M.e.injective (by rw [map_one]; exact hvb1)
    exact mem_oddCoreOf_iff.2 ⟨hvA, (QuotientGroup.eq_one_iff _).1 h2⟩
  refine ⟨a, haA, u, huz, v, hvO, hsa, ?_⟩
  calc s = a * s₂ := has₂.symm
    _ = a * (u * v) := by rw [← huv]
    _ = a * u * v := by group

theorem O_le_Qz (h : PairCtx X n z s A A' M M') :
    oddCoreOf (centralizer ({z} : Set X)) ≤ h.Qz := by
  intro c hc
  have hcz : c ∈ centralizer ({z} : Set X) := oddCoreOf_le _ hc
  rw [mem_Qz_iff]
  refine ⟨hcz, commutator_mem_oddCoreOf (W := oddCoreOf (centralizer ({z} : Set X)))
    (h.hNz hcz) (odd_card_oddCoreOf _) (fun a ha => ?_)⟩
  have h1 := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ (h.hAz ha)) c).1 hc
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hc)

theorem oddCoreOf_A_le (h : PairCtx X n z s A A' M M') :
    oddCoreOf A ≤ oddCoreOf (centralizer ({z} : Set X)) :=
  le_oddCoreOf_of_normalized ((oddCoreOf_le A).trans h.hAz)
    (fun _ hc => mem_normalizer_oddCoreOf_of_mem_normalizer (h.hNz hc)) (odd_card_oddCoreOf A)

theorem mem_normalizer_Qz (h : PairCtx X n z s A A' M M') {c : X}
    (hc : c ∈ centralizer ({z} : Set X)) : c ∈ normalizer (h.Qz : Set X) := by
  have hQ : c ∈ normalizer (QOf A : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => conj_mem_QOf (h.hNz hc) hy
    · intro hy
      have := conj_mem_QOf (Subgroup.inv_mem _ (h.hNz hc)) hy
      simpa [mul_assoc] using this
  exact mem_normalizer_inf (Subgroup.le_normalizer hc) hQ

theorem comm_s_mem_O (h : PairCtx X n z s A A' M M') (hP : h.swap.RCore) {q : X}
    (hq : q ∈ h.Qz) : ⁅q, s⁆ ∈ oddCoreOf (centralizer ({z} : Set X)) := by
  obtain ⟨a, haA, u, huz, v, hvO, -, hs⟩ := h.exists_decomp hP
  obtain ⟨hqz, hqm⟩ := h.mem_Qz_iff.1 hq
  have hqN : q ∈ normalizer (A : Set X) := h.hNz hqz
  have hqz' : q * z = z * q := Subgroup.mem_centralizer_singleton_iff.1 hqz
  have hzC : z ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hqu : q * u = u * q := by
    rcases (mem_zpowers_iff_of_orderOf_two h.hz).1 huz with rfl | rfl
    · simp
    · exact hqz'
  have huC : u ∈ centralizer ({z} : Set X) := by
    rcases (mem_zpowers_iff_of_orderOf_two h.hz).1 huz with rfl | rfl
    · exact one_mem _
    · exact hzC
  have hqu' : q⁻¹ * u * q = u := by
    calc q⁻¹ * u * q = q⁻¹ * (u * q) := by group
      _ = q⁻¹ * (q * u) := by rw [hqu]
      _ = u := by group
  have e1 : ⁅q, a⁆ ∈ oddCoreOf A := by
    have h1 := hqm a haA
    rw [← commutatorElement_inv a q]
    exact Subgroup.inv_mem _ h1
  have e2 : ⁅q, v⁆ ∈ oddCoreOf A := by
    have h1 := (Subgroup.mem_normalizer_iff.1
      (mem_normalizer_oddCoreOf_of_mem_normalizer hqN) v).1 hvO
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hvO)
  have hau : a * u ∈ normalizer (oddCoreOf A : Set X) :=
    Subgroup.mul_mem _
      (mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer haA))
      (mem_normalizer_oddCoreOf_of_mem_normalizer (h.hNz huC))
  have e3 : ⁅q, a * u * v⁆ = ⁅q, a⁆ * ((a * u) * ⁅q, v⁆ * (a * u)⁻¹) := by
    simp only [commutatorElement_def]
    calc q * (a * u * v) * q⁻¹ * (a * u * v)⁻¹
        = q * a * u * v * q⁻¹ * v⁻¹ * u⁻¹ * a⁻¹ := by group
      _ = q * a * (q⁻¹ * u * q) * v * q⁻¹ * v⁻¹ * u⁻¹ * a⁻¹ := by rw [hqu']
      _ = q * a * q⁻¹ * a⁻¹ * (a * u * (q * v * q⁻¹ * v⁻¹) * (a * u)⁻¹) := by group
  rw [hs, e3]
  refine h.oddCoreOf_A_le (Subgroup.mul_mem _ e1 ?_)
  have h4 := (Subgroup.mem_normalizer_iff.1 hau _).1 e2
  simpa [mul_assoc] using h4

theorem Qz_eq_of_RCore (h : PairCtx X n z s A A' M M') (hP : h.swap.RCore) :
    h.Qz = oddCoreOf (centralizer ({z} : Set X)) ⊔ zpowers z ∧
      Nat.card h.Qz = 2 * Nat.card (oddCoreOf (centralizer ({z} : Set X))) := by
  have hQC : h.Qz ≤ centralizer ({z} : Set X) := inf_le_left
  have hOn : ∀ q ∈ h.Qz, q ∈ normalizer (oddCoreOf (centralizer ({z} : Set X)) : Set X) :=
    fun _ hq => le_normalizer_oddCoreOf _ (hQC hq)
  have hzQ : z ∈ h.Qz := by
    refine h.mem_Qz_iff.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, fun a ha => ?_⟩
    have : ⁅a, z⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_singleton_iff.1 (h.hAz ha))
    rw [this]
    exact one_mem _
  refine Qz_structure_abstract h.Qz (oddCoreOf (centralizer ({z} : Set X))) z h.O_le_Qz hOn
    (odd_card_oddCoreOf _) hzQ h.hz
    (fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)) ?_ ?_
  · refine hall_of_centralizer h.Qz _ z s h.O_le_Qz hOn (odd_card_oddCoreOf _) h.hz h.sq_s
      (le_normalizer_oddCoreOf _ h.s_mem_C) (fun q hq => ?_) (fun x hx hxs j hj => ?_)
    · have := h.comm_s_mem_O hP (Subgroup.inv_mem _ hq)
      simpa [commutatorElement_def, mul_assoc] using this
    · exact h.swap.R2_of_RCore hP (show x ∈ h.P from
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hxs, hx⟩) hj
  · intro B hBQ hBn hBodd
    have h1 : B ≤ oddCoreOf h.Qz := le_oddCoreOf_of_normalized hBQ (fun q hq => hBn q hq) hBodd
    have h2 : oddCoreOf h.Qz ≤ oddCoreOf (centralizer ({z} : Set X)) :=
      le_oddCoreOf_of_normalized ((oddCoreOf_le _).trans hQC)
        (fun c hc => mem_normalizer_oddCoreOf_of_mem_normalizer (h.mem_normalizer_Qz hc))
        (odd_card_oddCoreOf _)
    exact h1.trans h2

end PairCtx

end CFSG.OddStandard.Solomon75
