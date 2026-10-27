module

public import CFSG.ClassicalInvolution.Q3.Q3T6FusSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

section Edge

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem false_of_le_inf_centralizer3 (hΩg : HypOmegaGen (CoreAssembly.conjClass K))
    (hDE : DEdgeless (CoreAssembly.conjClass K)) (hI : IsUniqueInvolution K z)
    (hN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G)) {a b : G}
    (hab : conjSub a K ≠ conjSub b K) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRnc : ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x) (hR8 : 2 < Nat.card R) (hRb : R ≤ conjSub b K)
    (hRa : R ≤ Subgroup.centralizer ({a * z * a⁻¹} : Set G)) : False := by
  obtain ⟨V, hV, hRV⟩ := IsSylow2In.exists_ge hR2 (le_inf hRb hRa)
  have hz₂R : b * z * b⁻¹ ∈ R :=
    AscL62.mem_of_uniqueInvolution_of_pGroup (hI.conj b) hRb hR2 (by omega)
  have hz₂V : b * z * b⁻¹ ∈ V := hRV hz₂R
  have hzne : a * z * a⁻¹ ≠ b * z * b⁻¹ := fun h => hab (conjSub_eq_of_conj_eq hN h)
  have hKaΩ : conjSub a K ∈ CoreAssembly.conjClass K := ⟨a, rfl⟩
  have hKbΩ : conjSub b K ∈ CoreAssembly.conjClass K := ⟨b, rfl⟩
  have hcard : Nat.card R ≤ Nat.card V := Subgroup.card_le_of_le hRV
  obtain ⟨x, hx, y, hy, hxy⟩ := hRnc
  rcases Sec6Gen.Pair.six_two hΩg ⟨hKaΩ, hKbΩ, hI.conj a, hI.conj b, hzne⟩ hV hz₂V with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hV3, -⟩ | ⟨hV4, -⟩
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact (hI.conj b).sq)
      (hI.conj b).ne_one] at hcard
    omega
  · rw [hV1, Nat.card_zpowers, orderOf_eq_prime (by rw [_root_.sq]; exact (hI.conj b).sq)
      (hI.conj b).ne_one] at hcard
    omega
  · obtain ⟨-, -, -, hcyc, -⟩ := hV3
    exact hxy (commute_of_isCyclic hcyc (hRV hx) (hRV hy))
  · exact hDE _ hKaΩ _ hKbΩ (Or.inl ⟨hKbΩ, hab.symm, V, hV4, hV.1.trans inf_le_left,
      (hV.1.trans inf_le_right).trans (centralizer_le_normalizer_conj hN a)⟩)

end Edge

section Act

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G} {C : Subgroup G}

namespace FusSec3

variable (h : FusSec3 K z C)

include h

theorem false_of_fixes_nonabelian {t : ↥C} (ht : ∃ g : G, (t : G) = g * z * g⁻¹)
    (htz : (t : G) * z = z * (t : G)) (ht2 : t * t = 1) (htne : (t : G) ≠ z)
    {P : Subgroup (↥(conjGen (secL K C)) ⧸ classicalInvolutionOddCore ↥(conjGen (secL K C)))}
    (hP2 : IsPGroup 2 P) (hPL : P ≤ secImg (conjGen (secL K C)) (secL K C))
    (hfix : ∀ x ∈ P, secAct (conjGen (secL K C)) t x = x)
    (hnc : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) : False := by
  have hLY : secL K C ≤ conjGen (secL K C) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨Q, hQL, hQc, hQ2, ⟨e⟩⟩ := exists_lift_of_fixed (conjGen (secL K C)) ht2 hLY
    (h.mem_normalizer_sec htz) hP2 hPL hfix
  obtain ⟨g, hg⟩ := ht
  have hI := h.isUniqueInvolution
  have hIg := hI.conj g
  rw [← hg] at hIg
  have hJne : conjSub g K ≠ conjSub 1 K := by
    rw [conjSub_one]
    intro h'
    apply htne
    have hmem := hIg.mem
    rw [h'] at hmem
    exact (hI.unique _ hmem hIg.sq).resolve_left hIg.ne_one
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  have hR2 : IsPGroup 2 (Q.map C.subtype) := hQ2.map _
  have hnc' : ∃ x' ∈ Q.map C.subtype, ∃ y' ∈ Q.map C.subtype, x' * y' ≠ y' * x' := by
    refine ⟨((e.symm ⟨x, hx⟩ : ↥Q) : G), ⟨_, (e.symm ⟨x, hx⟩).2, rfl⟩,
      ((e.symm ⟨y, hy⟩ : ↥Q) : G), ⟨_, (e.symm ⟨y, hy⟩).2, rfl⟩, fun h' => hxy ?_⟩
    have h'' : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ :=
      Subtype.ext (Subtype.ext h')
    have h3 := congrArg e h''
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h3
    exact congrArg Subtype.val h3
  refine false_of_le_inf_centralizer3 h.hypGen h.edgeless hI h.tight hJne hR2 hnc'
    (two_lt_card_of_noncomm hnc') ?_ ?_
  · rw [conjSub_one]
    intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    exact (Subgroup.mem_subgroupOf.mp (hQL hq)).1
  · intro r hr
    obtain ⟨q, hq, rfl⟩ := hr
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    exact (congrArg Subtype.val (hQc q hq)).symm

theorem exists_nonabelian_two_subgroup :
    ∃ R : Subgroup ↥C, R ≤ secL K C ∧ IsPGroup 2 R ∧ 8 ≤ Nat.card R ∧
      ∃ x ∈ R, ∃ y ∈ R, x * y ≠ y * x := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥(secL K C)) := inferInstance
  have hR : (T : Subgroup _).map (secL K C).subtype ∈ RSet (conjFamily (secL K C)) :=
    ⟨_, ⟨1, conjSub_one _⟩, T, rfl⟩
  have hq := Sec6Gen.isQuatSub_of_mem_RSet h.hypGenC hR
  exact ⟨_, Subgroup.map_subtype_le _, isPGroup_of_mem_rSet hR, hq.eight_le,
    hq.exists_not_commute⟩

theorem exists_noncomm_secImg :
    ∃ x ∈ secImg (conjGen (secL K C)) (secL K C),
      ∃ y ∈ secImg (conjGen (secL K C)) (secL K C), x * y ≠ y * x := by
  have hLY : secL K C ≤ conjGen (secL K C) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨R, hRL, hR2, -, x, hx, y, hy, hxy⟩ := h.exists_nonabelian_two_subgroup
  have hxL : x ∈ secL K C := hRL hx
  have hyL : y ∈ secL K C := hRL hy
  refine ⟨QuotientGroup.mk' _ ⟨x, hLY hxL⟩, ⟨⟨x, hLY hxL⟩, hxL, rfl⟩,
    QuotientGroup.mk' _ ⟨y, hLY hyL⟩, ⟨⟨y, hLY hyL⟩, hyL, rfl⟩, fun h' => hxy ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ↥(conjGen (secL K C)), x' = ⟨x, hLY hxL⟩ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(conjGen (secL K C)), y' = ⟨y, hLY hyL⟩ := ⟨_, rfl⟩
  rw [← hx', ← hy'] at h'
  have hc : x' * y' * x'⁻¹ * y'⁻¹ ∈ classicalInvolutionOddCore ↥(conjGen (secL K C)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have h'' : (QuotientGroup.mk x' : _ ⧸ classicalInvolutionOddCore _) * QuotientGroup.mk y' =
        QuotientGroup.mk y' * QuotientGroup.mk x' := h'
    rw [h'']
    group
  have hc' : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (conjGen (secL K C)) := by
    refine ⟨x' * y' * x'⁻¹ * y'⁻¹, hc, ?_⟩
    rw [hx', hy']
    rfl
  have hcR : x * y * x⁻¹ * y⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc'
    (hR2.to_le (Subgroup.zpowers_le.mpr hcR))
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem eq_of_secAct_fixes {t : ↥C} (ht : ∃ g : G, (t : G) = g * z * g⁻¹)
    (htz : (t : G) * z = z * (t : G)) (ht2 : t * t = 1)
    (hfix : ∀ x ∈ secImg (conjGen (secL K C)) (secL K C),
      secAct (conjGen (secL K C)) t x = x) : (t : G) = z := by
  by_contra htne
  have hLY : secL K C ≤ conjGen (secL K C) := le_conjGen ⟨1, conjSub_one _⟩
  obtain ⟨R, hRL, hR2, -, x, hx, y, hy, hxy⟩ := h.exists_nonabelian_two_subgroup
  have hP2 : IsPGroup 2 (secImg (conjGen (secL K C)) R) := hR2.comap_subtype.map _
  have hPL : secImg (conjGen (secL K C)) R ≤ secImg (conjGen (secL K C)) (secL K C) :=
    Subgroup.map_mono (Subgroup.comap_mono hRL)
  have hxY := hLY (hRL hx)
  have hyY := hLY (hRL hy)
  refine h.false_of_fixes_nonabelian ht htz ht2 htne hP2 hPL (fun w hw => hfix w (hPL hw))
    ⟨QuotientGroup.mk' _ ⟨x, hxY⟩, ⟨⟨x, hxY⟩, hx, rfl⟩,
      QuotientGroup.mk' _ ⟨y, hyY⟩, ⟨⟨y, hyY⟩, hy, rfl⟩, fun h' => hxy ?_⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ↥(conjGen (secL K C)), x' = ⟨x, hxY⟩ := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ↥(conjGen (secL K C)), y' = ⟨y, hyY⟩ := ⟨_, rfl⟩
  rw [← hx', ← hy'] at h'
  have hc : x' * y' * x'⁻¹ * y'⁻¹ ∈ classicalInvolutionOddCore ↥(conjGen (secL K C)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    have h'' : (QuotientGroup.mk x' : _ ⧸ classicalInvolutionOddCore _) * QuotientGroup.mk y' =
        QuotientGroup.mk y' * QuotientGroup.mk x' := h'
    rw [h'']
    group
  have hc' : x * y * x⁻¹ * y⁻¹ ∈ oddCoreOf (conjGen (secL K C)) := by
    refine ⟨x' * y' * x'⁻¹ * y'⁻¹, hc, ?_⟩
    rw [hx', hy']
    rfl
  have hcR : x * y * x⁻¹ * y⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
  have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc'
    (hR2.to_le (Subgroup.zpowers_le.mpr hcR))
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem exists_conj_eq_of_secAct_eq {t : ↥C} (ht : ∃ g : G, (t : G) = g * z * g⁻¹)
    (ht2 : t * t = 1) {c' : ↥C}
    (hφ : secAct (conjGen (secL K C)) t =
      secAct (conjGen (secL K C)) (c' * (⟨z, h.zC⟩ : C) * c'⁻¹)) :
    ∃ d : ↥C, t = d * (⟨z, h.zC⟩ : C) * d⁻¹ := by
  have hu := h.isUniqueInvolution_conj_sec c'
  have huY : c' * (⟨z, h.zC⟩ : C) * c'⁻¹ ∈ conjGen (secL K C) := le_conjGen ⟨c', rfl⟩ hu.mem
  have hφu : secAct (conjGen (secL K C)) t (QuotientGroup.mk ⟨_, huY⟩) =
      QuotientGroup.mk ⟨_, huY⟩ := by
    rw [hφ, secAct_of_mem _ huY, MulAut.conj_apply, mul_inv_cancel_right]
  obtain ⟨v, hvO, hv⟩ := exists_conj_commute_of_odd (oddCoreOf_odd_natCard _) ht2 hu.sq
    (mem_normalizer_oddCoreOf_conjGen _ t) (mem_normalizer_oddCoreOf_conjGen _ _)
    (mem_oddCoreOf_of_secAct huY hφu)
  set d := v * c' with hd'
  have hvd : v * (c' * (⟨z, h.zC⟩ : C) * c'⁻¹) * v⁻¹ = d * (⟨z, h.zC⟩ : C) * d⁻¹ := by
    rw [hd']
    group
  rw [hvd] at hv
  have hv1 := secAct_eq_one_of_mem (conjGen (secL K C)) hvO
  have hφ₂ : secAct (conjGen (secL K C)) (d⁻¹ * t * d) =
      secAct (conjGen (secL K C)) (⟨z, h.zC⟩ : C) := by
    rw [map_mul, map_mul, hφ, map_inv, hd', map_mul, hv1, one_mul, map_mul, map_mul, map_inv]
    group
  obtain ⟨g, hg⟩ := ht
  have ht₂ : ∃ g : G, ((d⁻¹ * t * d : ↥C) : G) = g * z * g⁻¹ := ⟨(d : G)⁻¹ * g, by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group⟩
  have ht₂z : ((d⁻¹ * t * d : ↥C) : G) * z = z * ((d⁻¹ * t * d : ↥C) : G) := by
    have h1 : d⁻¹ * t * d * (⟨z, h.zC⟩ : C) = (⟨z, h.zC⟩ : C) * (d⁻¹ * t * d) := by
      calc d⁻¹ * t * d * (⟨z, h.zC⟩ : C) = d⁻¹ * (t * (d * (⟨z, h.zC⟩ : C) * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * (⟨z, h.zC⟩ : C) * d⁻¹) * t) * d := by rw [hv]
        _ = (⟨z, h.zC⟩ : C) * (d⁻¹ * t * d) := by group
    exact congrArg Subtype.val h1
  have ht₂2 : d⁻¹ * t * d * (d⁻¹ * t * d) = 1 := by
    calc d⁻¹ * t * d * (d⁻¹ * t * d) = d⁻¹ * (t * t) * d := by group
      _ = 1 := by rw [ht2]; group
  have hfix := h.secAct_z_fixes
  rw [← hφ₂] at hfix
  have heq := h.eq_of_secAct_fixes ht₂ ht₂z ht₂2 hfix
  refine ⟨d, ?_⟩
  have h2 : d⁻¹ * t * d = (⟨z, h.zC⟩ : C) := Subtype.ext heq
  calc t = d * (d⁻¹ * t * d) * d⁻¹ := by group
    _ = d * (⟨z, h.zC⟩ : C) * d⁻¹ := by rw [h2]

end FusSec3

end Act

end CFSG.ClassicalInvolution.Q3.Q3T6
