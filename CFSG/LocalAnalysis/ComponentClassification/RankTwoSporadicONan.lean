module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.Sporadic.Schreier.SteinbergBIONOuterTwo
public import CFSG.Sporadic.ONOddCore.Involutions
public import CFSG.LocalAnalysis.SteinbergBSONInvolutionLocalComponents
public import CFSG.RankThree.Native.ONTripleRed

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.ONan

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ONSchreier CFSG.Sporadic.ONOddCore

section Abstract

variable {T : Type*} [Group T] [Finite T]

theorem mem_zpowers_cases {q t : T} (hq4 : orderOf q = 4) (ht : t ∈ zpowers q) :
    t = 1 ∨ t = q ∨ t = q ^ 2 ∨ t = q ^ 3 := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hq4, Finset.mem_image] at ht
  obtain ⟨k, hk, rfl⟩ := ht
  rw [Finset.mem_range] at hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · left
    exact pow_zero _
  · right; left
    exact pow_one _
  · right; right; left
    rfl
  · right; right; right
    rfl

theorem eq_one_or_eq_conj_of_fix {M L : Subgroup T} {z q s : T}
    (hMz : ∀ g : T, g ∈ M ↔ g * z = z * g) (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L)
    (hsM : s ∈ M) (hML : ∀ m ∈ M, m ∈ L ∨ m * s ∈ L)
    (hqL : q ∈ L) (hCL : ∀ m ∈ M, (∀ l ∈ L, m * l = l * m) → m ∈ zpowers q)
    (hqc : ∀ l ∈ L, q * l = l * q) (hz : z = q ^ 2) (hq4 : orderOf q = 4)
    (hqM : ∃ m ∈ M, q * m ≠ m * q)
    (hpt : ∀ α : MulAut T, (∀ m ∈ M, α m = m) → α = 1 ∨ α = MulAut.conj z)
    (hz1 : MulAut.conj z ≠ 1) {α : MulAut T} (hα2 : α * α = 1) (hαL : ∀ l ∈ L, α l = l) :
    α = 1 ∨ α = MulAut.conj z := by
  have hzL : z ∈ L := hz ▸ pow_mem hqL 2
  have hαz : α z = z := hαL z hzL
  have hαM : ∀ m ∈ M, α m ∈ M := by
    intro m hm
    rw [hMz] at hm ⊢
    rw [← hαz, ← map_mul, ← map_mul, hm]
  have hq4' : q ^ 4 = 1 := hq4 ▸ pow_orderOf_eq_one q
  have hq2 : q ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq4]; norm_num)
  have hfixM : ∀ β : MulAut T, β s = s → (∀ l ∈ L, β l = l) → ∀ m ∈ M, β m = m := by
    intro β hβs hβL m hm
    rcases hML m hm with h | h
    · exact hβL m h
    · have h1 := hβL _ h
      rw [map_mul, hβs] at h1
      exact mul_right_cancel h1
  set d := s⁻¹ * α s with hd
  have hdM : d ∈ M := M.mul_mem (inv_mem hsM) (hαM s hsM)
  have hdc : ∀ l ∈ L, d * l = l * d := by
    intro l hl
    have h1 : α (s * l * s⁻¹) = s * l * s⁻¹ := hαL _ (hLn s hsM l hl)
    rw [map_mul, map_mul, map_inv, hαL l hl] at h1
    calc d * l = s⁻¹ * (α s * l * (α s)⁻¹) * α s := by rw [hd]; group
      _ = s⁻¹ * (s * l * s⁻¹) * α s := by rw [h1]
      _ = l * d := by rw [hd]; group
  have hdq : d ∈ zpowers q := hCL d hdM hdc
  have hdL : d ∈ L := (zpowers_le.mpr hqL) hdq
  have hαs : α s = s * d := by rw [hd]; group
  have hdd : d * d = 1 := by
    have h1 : α (α s) = s := by
      rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    rw [hαs, map_mul, hαs, hαL d hdL] at h1
    calc d * d = s⁻¹ * (s * d * d) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  rcases mem_zpowers_cases hq4 hdq with h | h | h | h
  ·
    exact hpt α (hfixM α (by rw [hαs, h, mul_one]) hαL)
  · exfalso
    rw [h, ← sq] at hdd
    exact hq2 hdd
  ·
    exfalso
    have hαs' : α s = s * q ^ 2 := by rw [hαs, h]
    set t := s * q * s⁻¹ with ht
    have htL : t ∈ L := hLn s hsM q hqL
    have htc : ∀ l ∈ L, t * l = l * t := by
      intro l hl
      have hl' : s⁻¹ * l * s ∈ L := by
        simpa using hLn s⁻¹ (inv_mem hsM) l hl
      have hq := hqc _ hl'
      calc t * l = s * (q * (s⁻¹ * l * s)) * s⁻¹ := by rw [ht]; group
        _ = s * ((s⁻¹ * l * s) * q) * s⁻¹ := by rw [hq]
        _ = l * t := by rw [ht]; group
    have hto : orderOf t = 4 := by
      rw [ht, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hq4]
    have ht2 : t ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hto]; norm_num)
    rcases mem_zpowers_cases hq4 (hCL t (hLM htL) htc) with h1 | h1 | h1 | h1
    · exact ht2 (by rw [h1, one_pow])
    ·
      obtain ⟨m, hm, hqm⟩ := hqM
      apply hqm
      have hsq : q * s = s * q := by
        have : s * q * s⁻¹ = q := by rw [← ht, h1]
        calc q * s = s * q * s⁻¹ * s := by rw [this]
          _ = s * q := by group
      rcases hML m hm with h2 | h2
      · exact hqc m h2
      · have h3 := hqc _ h2
        calc q * m = q * (m * s) * s⁻¹ := by group
          _ = m * s * q * s⁻¹ := by rw [h3]
          _ = m * (s * q) * s⁻¹ := by group
          _ = m * (q * s) * s⁻¹ := by rw [hsq]
          _ = m * q := by group
    · exact ht2 (by rw [h1, ← pow_mul, show 2 * 2 = 4 from rfl, hq4'])
    ·
      have hq3 : q ^ 3 = q⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hq4']
      have hsq : s * q = q⁻¹ * s := by
        have : s * q * s⁻¹ = q⁻¹ := by rw [← ht, h1, hq3]
        calc s * q = s * q * s⁻¹ * s := by group
          _ = q⁻¹ * s := by rw [this]
      set β := (MulAut.conj q)⁻¹ * α with hβ
      have hβx : ∀ x, β x = q⁻¹ * α x * q := by
        intro x
        rw [hβ, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
      have hβL : ∀ l ∈ L, β l = l := by
        intro l hl
        rw [hβx, hαL l hl]
        calc q⁻¹ * l * q = q⁻¹ * (q * l) := by rw [hqc l hl]; group
          _ = l := by group
      have hβs : β s = s := by
        rw [hβx, hαs']
        calc q⁻¹ * (s * q ^ 2) * q = q⁻¹ * ((s * q) * q * q) := by
              rw [sq]; simp only [mul_assoc]
          _ = q⁻¹ * ((q⁻¹ * s) * q * q) := by rw [hsq]
          _ = q⁻¹ * q⁻¹ * ((s * q) * q) := by group
          _ = q⁻¹ * q⁻¹ * ((q⁻¹ * s) * q) := by rw [hsq]
          _ = q⁻¹ * q⁻¹ * q⁻¹ * (s * q) := by group
          _ = q⁻¹ * q⁻¹ * q⁻¹ * (q⁻¹ * s) := by rw [hsq]
          _ = (q ^ 4)⁻¹ * s := by group
          _ = s := by rw [hq4', inv_one, one_mul]
      have hαβ : α = MulAut.conj q * β := by rw [hβ, mul_inv_cancel_left]
      have hzq : z * q = q * z := by rw [hz, ← pow_succ, ← pow_succ']
      have hzz : z * z = 1 := by
        rw [hz, ← pow_add]
        exact hq4'
      have hqzqz : q * z * (q * z) = z := by
        calc q * z * (q * z) = q * (z * q) * z := by group
          _ = q * (q * z) * z := by rw [hzq]
          _ = q * q * (z * z) := by group
          _ = z := by rw [hzz, mul_one, hz, sq]
      rcases hpt β (hfixM β hβs hβL) with h2 | h2
      · apply hz1
        rw [← hα2, hαβ, h2, mul_one, ← map_mul, ← sq, ← hz]
      · apply hz1
        rw [← hα2, hαβ, h2, ← map_mul, ← map_mul, hqzqz]
  · exfalso
    rw [h, ← pow_add, show 3 + 3 = 4 + 2 from rfl, pow_add, hq4', one_mul] at hdd
    exact hq2 hdd

end Abstract

theorem center_Pv :
    center ↥Pv = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥Pv) with h | h
  · exact h
  · exfalso
    apply r3e_on_involution_centralizer_pointwise_automorphisms_inner.2.1
    ext x
    have hx := mem_center_iff.mp (h ▸ mem_top zP) x
    simp [MulAut.conj_apply, ← hx]

theorem orderOf_zP :
    orderOf zP = 2 := by
  rw [← Subgroup.orderOf_coe, show (zP : Equiv.Perm (Fin N)) = onz from rfl, onz_eq_q2]
  have hq4 := orderOf_onq
  refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hq4]; norm_num))
  rw [← pow_mul, show 2 * 2 = 4 from rfl, ← hq4, pow_orderOf_eq_one]

theorem fusion_zP :
    ∀ t : ↥Pv, orderOf t = 2 → ∃ x : ↥Pv, x * zP * x⁻¹ = t := by
  intro t ht
  obtain ⟨g, hg, he⟩ := cti_on_all_involutions_conjugate (t : Equiv.Perm (Fin N)) t.2
    (by rw [Subgroup.orderOf_coe, ht])
  exact ⟨⟨g, hg⟩, Subtype.ext he.symm⟩

@[expose] noncomputable def LP :
    Subgroup ↥Pv :=
  onL.subgroupOf Pv

theorem map_centralizer_zP :
    (centralizer {zP}).map Pv.subtype = onM := by
  rw [CFSG.ONSchreier.centralizer_zP, subgroupOf_map_subtype, inf_comm, ← onM_eq_centralizer_z]

theorem map_LP :
    LP.map Pv.subtype = onL := by
  rw [LP, subgroupOf_map_subtype, inf_eq_left.mpr onL_le]

theorem LP_eq_commutator :
    LP = ⁅centralizer {zP}, centralizer {zP}⁆ := by
  apply Subgroup.map_injective Pv.subtype_injective
  rw [map_LP, map_commutator, map_centralizer_zP, onL_eq_commutator]

theorem LP_commutator :
    ⁅LP, LP⁆ = LP := by
  apply Subgroup.map_injective Pv.subtype_injective
  rw [map_commutator, map_LP, onL_commutator]

theorem fourProp_LP :
    FourProp LP := by
  rw [← fourProp_map_iff Pv.subtype Pv.subtype_injective, map_LP]
  have := CFSG.LocalAnalysis.SteinbergBS.onX_isSimpleGroup
  exact fourProp_of_quasisimple ⟨Group.isPerfect_def.mp onL_isPerfect, lQuotEquiv.isSimpleGroup⟩
    ⟨onq, onq_mem_L, by rw [orderOf_onq]⟩

theorem exists_index_two_rep :
    ∃ s ∈ onM, ∀ m ∈ onM, m ∈ onL ∨ m * s ∈ onL := by
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp onL_relIndex
  refine ⟨a, a.2, fun m hm => ?_⟩
  rcases (ha ⟨m, hm⟩).or with h | h
  · right
    exact h
  · left
    exact h

theorem fix_LP :
    ∀ α : MulAut ↥Pv, α * α = 1 → (∀ l ∈ LP, α l = l) → α = 1 ∨ α = MulAut.conj zP := by
  intro α hα2 hαL
  have hC : ∀ g : ↥Pv, g ∈ centralizer {zP} ↔ (g : Equiv.Perm (Fin N)) ∈ onM := by
    intro g
    rw [← map_centralizer_zP]
    exact ⟨fun h => ⟨g, h, rfl⟩, fun ⟨g', hg', he⟩ => Subtype.ext he ▸ hg'⟩
  have hLmem : ∀ g : ↥Pv, g ∈ LP ↔ (g : Equiv.Perm (Fin N)) ∈ onL := fun g => mem_subgroupOf
  obtain ⟨s, hsM, hs⟩ := exists_index_two_rep
  have hqPv : onq ∈ Pv := onL_le onq_mem_L
  set qP : ↥Pv := ⟨onq, hqPv⟩ with hqP
  have hqQ : onq ∈ onM ⊓ centralizer (onL : Set (Equiv.Perm (Fin N))) := by
    rw [onM_centralizer_L]
    exact mem_zpowers onq
  refine eq_one_or_eq_conj_of_fix (M := centralizer {zP}) (L := LP) (q := qP)
    (s := ⟨s, onM_le hsM⟩) (fun g => mem_centralizer_singleton_iff) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ hα2 hαL
  · rw [LP_eq_commutator]
    exact Subgroup.commutator_le_self _
  · intro m hm l hl
    rw [LP_eq_commutator] at hl ⊢
    exact conj_mem_commutator_of_mem_right hl hm
  · rw [hC]
    exact hsM
  · intro m hm
    rw [hC] at hm
    rw [hLmem, hLmem]
    exact hs _ hm
  · rw [hLmem]
    exact onq_mem_L
  · intro m hm hml
    rw [hC] at hm
    have hmQ : (m : Equiv.Perm (Fin N)) ∈ onM ⊓ centralizer (onL : Set (Equiv.Perm (Fin N))) := by
      refine ⟨hm, mem_centralizer_iff.mpr fun l hl => ?_⟩
      have := hml ⟨l, onL_le hl⟩ ((hLmem _).mpr hl)
      exact (congrArg Subtype.val this).symm
    rw [onM_centralizer_L] at hmQ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmQ
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [← hk]; rfl)⟩
  · intro l hl
    exact Subtype.ext ((mem_centralizer_iff.mp hqQ.2) l ((hLmem l).mp hl)).symm
  · exact Subtype.ext onz_eq_q2
  · rw [hqP, Subgroup.orderOf_mk, orderOf_onq]
  · by_contra hcon
    push Not at hcon
    have hqM : onq ∈ onM := hqQ.1
    have hmem : (⟨onq, hqM⟩ : ↥onM) ∈ center ↥onM := by
      rw [mem_center_iff]
      intro y
      have h := hcon ⟨y, onM_le y.2⟩ ((hC _).mpr y.2)
      exact Subtype.ext (congrArg Subtype.val h).symm
    have hdvd := (center ↥onM).orderOf_dvd_natCard hmem
    rw [Subgroup.orderOf_mk, orderOf_onq, card_center_M] at hdvd
    exact absurd hdvd (by norm_num)
  · intro β hβ
    have h := r3e_on_involution_centralizer_pointwise_automorphisms_inner.1
    have hmem : β ∈ {α : MulAut Pv | ∀ m : Pv, (m : Equiv.Perm (Fin N)) ∈ onM → α m = m} :=
      fun m hm => hβ m ((hC m).mpr hm)
    rw [h] at hmem
    simpa using hmem
  · exact r3e_on_involution_centralizer_pointwise_automorphisms_inner.2.1.symm

theorem yCensus_Pv :
    YCensus (OuterAutomorphisms.inner ↥Pv) (fun _ => False) :=
  yCensus_inner_of_derived center_Pv CFSG.Sporadic.SteinbergBI.card_outer_Pv_dvd_two orderOf_zP
    fusion_zP rfl LP_eq_commutator LP_commutator fourProp_LP fix_LP

theorem autModel_Pv :
    AutModel (Blueprint.NativeSporadic.Carrier .ONan) (MulAut ↥Pv)
      (OuterAutomorphisms.inner ↥Pv) :=
  autModel_mulAut_of_center (X₀ := Blueprint.NativeSporadic.Carrier .ONan) onEquivPv.symm center_Pv

instance finite_mulAut_Pv :
    Finite (MulAut ↥Pv) :=
  Finite.of_injective (fun f : MulAut ↥Pv => (f : ↥Pv → ↥Pv)) DFunLike.coe_injective

theorem sporadicCaseOdd_ONan
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .ONan :=
  sporadicCaseOdd_of_yCensus h32 h33 autModel_Pv yCensus_Pv

end CFSG.ComponentClassification.RankTwoSporadic.ONan
