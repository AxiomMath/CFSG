module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RowsFin
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecQuot
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecOddFree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.Q3CH
open scoped commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' J J' : Subgroup G}
  {z u t : G}

theorem frameData_twin_J (hΩ : HypOmegaGen Ω) (hf : TwinFrameData Ω K K' z u J t)
    (hJ' : J' ∈ twinSet Ω J) : TwinFrameData Ω K K' z u J' t := by
  have htJ' : IsUniqueInvolution J' t := isUniqueInvolution_of_mem_twinSet hf.ht hJ'
  refine ⟨hf.mem, hf.hz, hf.hK', hf.hne, hf.hu, hf.hu2, hf.hu1, hf.huz, ⟨hJ'.1, ?_⟩, htJ',
    hf.htu⟩
  intro M hM
  have hMΩ : M ∈ Ω := hM.1
  have hJM : J ∈ omegaNbr Ω M := hf.hJ.2 M hM
  have hMJ : M ∈ omegaNbr Ω J :=
    Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hMΩ hf.hJ.1 hJM
  have hperp : KPerp Ω J = KPerp Ω J' := A7Q.Gen.kPerp_eq_of_twin hΩ hf.hJ.1 hJ'
  have hMJ' : M ∈ KPerp Ω J' := hperp ▸ Set.mem_insert_of_mem _ hMJ
  have hMne : M ≠ J' := by
    intro e
    obtain ⟨-, z', hz'K, hz'M⟩ := hM
    rw [e] at hz'M
    exact hf.t_ne_z ((htJ'.eq hz'M).trans (hf.hz.eq hz'K).symm)
  have hMn : M ∈ omegaNbr Ω J' := by
    rcases Set.mem_insert_iff.mp hMJ' with h | h
    · exact absurd h hMne
    · exact h
  exact Q3.Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ'.1 hMΩ hMn

theorem u_not_mem_closure_zt (hΩ : HypOmegaGen Ω) (hd : TwinFrameData Ω K K' z u J t) :
    u ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hu
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ hd
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  have hnt := Hat2A7S.twinFrame_t_not_mem_closure hΩ hd
  have hzcl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hucl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  rcases ChainFrame.mem_closure_four hz2 ht2 hzt hu with h | h | h | h
  · exact hd.hu1 h
  · exact hd.huz h
  · exact hnt (h ▸ hucl)
  · apply hnt
    have : t = z * u := by
      rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hzcl hucl

theorem ucoset_facts (hΩ : HypOmegaGen Ω) (hd : TwinFrameData Ω K K' z u J t) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) :
    c ∈ Subgroup.closure ({z, u, t} : Set G) ∧ c ≠ 1 ∧ z ≠ c ∧ t ≠ c ∧ z * t ≠ c ∧
      Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({z, t, c} : Set G) := by
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ hd
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  have hnu := u_not_mem_closure_zt hΩ hd
  have hz' : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht' : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hzB := TwinFrame.z_mem z u t
  have huB := TwinFrame.u_mem z u t
  have htB := TwinFrame.t_mem z u t
  obtain ⟨w, hw, hcw, huw⟩ : ∃ w : G, w ∈ Subgroup.closure ({z, t} : Set G) ∧ c = u * w ∧
      u = c * w := by
    rcases hc with hc | hc | hc | hc
    · exact ⟨1, Subgroup.one_mem _, by rw [hc, mul_one], by rw [hc, mul_one]⟩
    · refine ⟨z, hz', ?_, ?_⟩
      · rw [hc]
        have := hd.comm_zu
        rw [this]
      · rw [hc]
        have := hd.comm_zu
        rw [this, mul_assoc, hz2, mul_one]
    · refine ⟨t, ht', hc, ?_⟩
      rw [hc, mul_assoc, ht2, mul_one]
    · refine ⟨z * t, Subgroup.mul_mem _ hz' ht', ?_, ?_⟩
      · rw [hc]
        have := hd.comm_zu
        calc z * u * t = u * z * t := by rw [this]
          _ = u * (z * t) := by group
      · have hsq : (z * t) * (z * t) = 1 := mul_involution_of_commute hz2 ht2 hzt
        have := hd.comm_zu
        rw [hc]
        calc u = u * ((z * t) * (z * t)) := by rw [hsq, mul_one]
          _ = z * u * t * (z * t) := by
              calc u * ((z * t) * (z * t)) = u * z * t * (z * t) := by group
                _ = z * u * t * (z * t) := by rw [← this]
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
    rw [hcw]
    refine Subgroup.mul_mem _ huB ?_
    exact (Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl))) hw
  have hncl : c ∉ Subgroup.closure ({z, t} : Set G) := by
    intro hcl
    apply hnu
    rw [huw]
    exact Subgroup.mul_mem _ hcl hw
  refine ⟨hcB, fun h => hncl (h ▸ Subgroup.one_mem _), fun h => hncl (h ▸ hz'),
    fun h => hncl (h ▸ ht'), fun h => hncl (h ▸ Subgroup.mul_mem _ hz' ht'), ?_⟩
  refine TwinFrame.closure_three_eq (a := z) (b := t) (c := c) hzB htB hcB
    (Subgroup.subset_closure (by simp)) ?_ (Subgroup.subset_closure (by simp))
  rw [huw]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ?_
  refine (Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl))) hw

end Frame

section Unique

variable {G : Type} [Group G] [Finite G]

open scoped MatrixGroups in
theorem sl23_involution : ∀ x : SL(2, ZMod 3), x * x = 1 → x = 1 ∨ x = -1 := by decide

theorem eq_one_of_mem_oddCore_sq {X : Type} [Group X] [Finite X] {y : X}
    (hy : y ∈ classicalInvolutionOddCore X) (h : y * y = 1) : y = 1 := by
  have hd := Subgroup.orderOf_dvd_natCard _ hy
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h1] at hd
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card X))
      (even_iff_two_dvd.mpr hd)

open scoped MatrixGroups in
theorem isUniqueInvolution_of_sectionMember3 {Y K : Subgroup G} {z : G}
    (h : Q3NL.IsSectionMember3 Y K z) : IsUniqueInvolution K z := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [h.orderOf_eq_two] at this
    simpa [pow_two] using this
  have hz1 : z ≠ 1 := by
    intro e
    have := h.orderOf_eq_two
    rw [e, orderOf_one] at this
    omega
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) :=
    (isSubnormal_le h.subnormal).trans inf_le_left
  have hzc : ∀ k ∈ K, k * z = z * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
  refine ⟨h.mem, hz1, hz2, fun y hy hy2 => ?_⟩
  obtain ⟨e⟩ := h.nonempty_equiv
  set N := classicalInvolutionOddCore ↥K with hN
  set φ : ↥K →* SL(2, ZMod 3) := (e : ↥K ⧸ N →* SL(2, ZMod 3)).comp (QuotientGroup.mk' N) with hφ
  have hker : ∀ w : ↥K, φ w = 1 → w ∈ N := by
    intro w hw
    have h1 : QuotientGroup.mk' N w = 1 := by
      have := e.injective (hw.trans (map_one e).symm)
      exact this
    exact (QuotientGroup.eq_one_iff w).mp h1
  set zK : ↥K := ⟨z, h.mem⟩ with hzK
  have hzK2 : zK * zK = 1 := Subtype.ext hz2
  have hφz : φ zK = -1 := by
    rcases sl23_involution (φ zK) (by rw [← map_mul, hzK2, map_one]) with h1 | h1
    · exfalso
      exact hz1 (congrArg Subtype.val (eq_one_of_mem_oddCore_sq (hker _ h1) hzK2))
    · exact h1
  set yK : ↥K := ⟨y, hy⟩ with hyK
  have hyK2 : yK * yK = 1 := Subtype.ext hy2
  rcases sl23_involution (φ yK) (by rw [← map_mul, hyK2, map_one]) with h1 | h1
  · left
    exact congrArg Subtype.val (eq_one_of_mem_oddCore_sq (hker _ h1) hyK2)
  · right
    have hyz : yK * zK = zK * yK := Subtype.ext (hzc y hy)
    have h3 : φ (yK * zK) = 1 := by rw [map_mul, h1, hφz]; simp
    have h4 : (yK * zK) * (yK * zK) = 1 := by
      calc (yK * zK) * (yK * zK) = yK * (zK * yK) * zK := by group
        _ = yK * (yK * zK) * zK := by rw [← hyz]
        _ = (yK * yK) * (zK * zK) := by group
        _ = 1 := by rw [hyK2, hzK2, one_mul]
    have h5 := eq_one_of_mem_oddCore_sq (hker _ h3) h4
    have h6 : y * z = 1 := congrArg Subtype.val h5
    have h7 : y = z⁻¹ := eq_inv_of_mul_eq_one_left h6
    rw [h7, inv_eq_of_mul_eq_one_right hz2]

end Unique

section Classical

variable {G : Type} [Group G] [Finite G]

theorem alpha_of_lifted_u (hBelow : CIT3Below (Nat.card G)) (hZ : Subgroup.center G = ⊥)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) {c z t a : G} (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hzB : z ∈ B) (htB : t ∈ B) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzc : z ≠ c) (htc : t ≠ c)
    (hztc : z * t ≠ c) (hzt1 : z * t ≠ 1) (hBeq : B = Subgroup.closure ({z, t, c} : Set G))
    {M M' : Subgroup G}
    (hM : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M t)
    (hM' : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) M' t)
    (hne : modOdd c M ≠ modOdd c M')
    (hcomm : ∀ x ∈ modOdd c M, ∀ y ∈ modOdd c M', x * y = y * x)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (ha2 : a * a = z) (hat : a * t = t * a)
    (hcommM : ∀ x ∈ modOdd c M, oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    (hcommM' : ∀ x ∈ modOdd c M', oddQuotMk c ⟨a, haC⟩ * x = x * oddQuotMk c ⟨a, haC⟩)
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L) (hmov : MovedByAll B c L) :
    alphaOf (inducedImage L (modOdd c B)) = ⊥ := by
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hc1 (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 hM hM' hM
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c M M' M)
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB htB
  have htj : oddQuotMk c ⟨t, htC⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hM.mem htC)
  have htmov : ∃ w ∈ L, oddQuotMk c ⟨t, htC⟩ * w ≠ w * oddQuotMk c ⟨t, htC⟩ :=
    hmov _ (oddQuotMk_mem_modOdd htB htC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 htB ht1 htc htC)
  have hLj : L = secComp hΦ D j := eq_secComp_of_not_commute hΦ D htj hL htmov
  subst hLj
  exact Q3T7.alpha_of_twinOuter3 Q3T7.twinOuterAlphaAll3_proved hΦ D hB hcB hc1 hzB htB hz1 ht1
    hzc htc hztc hzt1 hBeq (mem_sFamily3_one c M M' M) (mem_sFamily3_two c M M' M)
    (isUniqueInvolution_of_sectionMember3 hM) (isUniqueInvolution_of_sectionMember3 hM')
    hne hcomm haC ha2 hat hcommM hcommM' hj hmov hL

end Classical

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
