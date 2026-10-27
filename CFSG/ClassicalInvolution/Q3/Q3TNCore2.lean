module

public import CFSG.ClassicalInvolution.Q3.Q3TNCore1
public import CFSG.ClassicalInvolution.Q3.Q3TNGen
public import CFSG.ClassicalInvolution.Uniform.UTwinSolv

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped commutatorElement MatrixGroups

theorem odd_orderOf_of_mem_oddCore {X : Type*} [Group X] [Finite X] {g : X}
    (hg : g ∈ classicalInvolutionOddCore X) : Odd (orderOf g) := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : classicalInvolutionOddCore X)
  rw [Subgroup.orderOf_mk] at h
  exact (OddCore.odd_card X).of_dvd_nat h

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_eq_mul {T : Subgroup G} (hTc : IsComponent T) {z v o : G}
    (hz2 : z * z = 1) (hzT : z ∈ Subgroup.normalizer (T : Set G))
    (hv : v ∈ layer G ⊓ Subgroup.centralizer (T : Set G)) (ho : Odd (orderOf o))
    (hzvo : z = v * o) :
    z ∈ Subgroup.centralizer (T : Set G) := by
  have hvN : v ∈ Subgroup.normalizer (T : Set G) := layer_le_normalizer hTc hv.1
  have hoN : o ∈ Subgroup.normalizer (T : Set G) := by
    have : o = v⁻¹ * z := by rw [hzvo]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvN) hzT
  refine mem_centralizer_of_acts_as ho hz2
    (fun a ha => (Subgroup.mem_normalizer_iff.mp hzT a).mp ha) fun a ha => ?_
  have hoa : o * a * o⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hoN a).mp ha
  have hc := Subgroup.mem_centralizer_iff.mp hv.2 _ hoa
  rw [hzvo]
  calc o * a * o⁻¹ = (o * a * o⁻¹) * v * v⁻¹ := by group
    _ = v * (o * a * o⁻¹) * v⁻¹ := by rw [hc]
    _ = v * o * a * (v * o)⁻¹ := by group

omit [Finite G] in
theorem le_centralizer_of_conj {T : Subgroup G} {σ z : G} (hσz : σ * z = z * σ)
    (h : z ∈ Subgroup.centralizer (conjSub σ T : Set G)) :
    T ≤ Subgroup.centralizer ({z} : Set G) := by
  intro t ht
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := Subgroup.mem_centralizer_iff.mp h _ (conj_mem_conjSub (n := σ) ht)
  have hσz' : σ⁻¹ * z = z * σ⁻¹ := by
    calc σ⁻¹ * z = σ⁻¹ * (z * σ) * σ⁻¹ := by group
      _ = σ⁻¹ * (σ * z) * σ⁻¹ := by rw [hσz]
      _ = z * σ⁻¹ := by group
  calc t * z = σ⁻¹ * (σ * t * σ⁻¹) * (σ * z) := by group
    _ = σ⁻¹ * (σ * t * σ⁻¹ * z) * σ := by rw [hσz]; group
    _ = σ⁻¹ * (z * (σ * t * σ⁻¹)) * σ := by rw [hc]
    _ = σ⁻¹ * z * (σ * t * σ⁻¹) * σ := by group
    _ = z * σ⁻¹ * (σ * t * σ⁻¹) * σ := by rw [hσz']
    _ = z * t := by group

theorem false_of_map_eq {L : Subgroup G} {z : G} (hz : IsClassicalMember3 L z)
    {T : Subgroup G} (hTc : IsComponent T) (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set G))
    {x : G} (hxT : x ∈ T) (hx2 : x * x = 1) (hxc : x ∉ Subgroup.centralizer (T : Set G))
    {σ : G} (hσL : σ ∈ L) (hσ : Odd (orderOf σ)) (hσT : conjSub σ T ≠ T)
    (hdC : σ⁻¹ * (x * σ * x⁻¹) ∈ Subgroup.centralizer ({z} : Set G))
    (hdL : QuotientGroup.mk' (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G)))
        ⟨σ⁻¹ * (x * σ * x⁻¹), hdC⟩ ∈ (L.subgroupOf (Subgroup.centralizer ({z} : Set G))).map
          (QuotientGroup.mk' (classicalInvolutionOddCore (Subgroup.centralizer ({z} : Set G))))) :
    False := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  set π := QuotientGroup.mk' (classicalInvolutionOddCore C) with hπ
  set Lb := (L.subgroupOf C).map π with hLb
  set T1 := conjSub σ T with hT1
  have hT1c : IsComponent T1 := isComponent_map_mulEquiv (MulAut.conj σ) hTc
  have hLC : L ≤ C := isSubnormal_le hz.subnormal
  obtain ⟨e1⟩ := Uniform.nonempty_quotEquiv_subgroupOf hLC (Classical.choice hz.nonempty_equiv)
  let eL : Lb ≃* SL(2, ZMod 3) := (Components.oddCore_image_equiv (L.subgroupOf C)
    (Uniform.isSubnormal_subgroupOf_top hz.subnormal)).symm.trans e1
  set W : Subgroup C := (layer G).subgroupOf C with hW
  set V : Subgroup C := (layer G ⊓ Subgroup.centralizer (T1 : Set G)).subgroupOf C with hV
  have := layer_characteristic (G := G)
  have hWm : (W.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  set Nb : Subgroup Lb := (W.map π).subgroupOf Lb with hNb
  set Kb : Subgroup Lb := (V.map π).subgroupOf Lb with hKb
  have hKN : Kb ≤ Nb := fun h hh =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
      (Subgroup.mem_subgroupOf.mp hh))
  have hKNn : (Kb.subgroupOf Nb).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKN]
    intro h k hh hk
    obtain ⟨v, hv, hvh⟩ := Subgroup.mem_subgroupOf.mp hh
    obtain ⟨w, hw, hwk⟩ := Subgroup.mem_subgroupOf.mp hk
    refine Subgroup.mem_subgroupOf.mpr ⟨w * v * w⁻¹, ?_, ?_⟩
    · have hv' : (v : G) ∈ layer G ⊓ Subgroup.centralizer (T1 : Set G) := hv
      have hw' : (w : G) ∈ layer G := hw
      show ((w * v * w⁻¹ : C) : G) ∈ layer G ⊓ Subgroup.centralizer (T1 : Set G)
      have hwN := layer_le_normalizer hT1c hw'
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hw' hv'.1) (Subgroup.inv_mem _ hw'),
        Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have hb' : (w : G)⁻¹ * b * (w : G) ∈ T1 := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwN) b).mp hb
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hv'.2 _ hb'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc b * ((w : G) * v * (w : G)⁻¹) = (w : G) * ((w : G)⁻¹ * b * (w : G) * v) * (w : G)⁻¹ := by
            group
        _ = (w : G) * (v * ((w : G)⁻¹ * b * (w : G))) * (w : G)⁻¹ := by rw [hc]
        _ = (w : G) * v * (w : G)⁻¹ * b := by group
    · simp [map_mul, map_inv, hvh, hwk]
  have hKsub : IsSubnormal Kb ⊤ :=
    IsSubnormal.step hKN hKNn (isSubnormal_of_normal_subgroupOf le_top inferInstance)
  by_cases hKbot : Kb = ⊥
  · have hdV : (⟨σ⁻¹ * (x * σ * x⁻¹), hdC⟩ : C) ∈ V := by
      show σ⁻¹ * (x * σ * x⁻¹) ∈ layer G ⊓ Subgroup.centralizer (T1 : Set G)
      refine ⟨?_, (acts_as_d hTc hσ hσT hxT hx2).2⟩
      have hu := (conj_inv_mem (σ := σ) hxT).1
      have hTm1 : IsComponent (conjSub σ⁻¹ T) := isComponent_map_mulEquiv (MulAut.conj σ⁻¹) hTc
      rw [show σ⁻¹ * (x * σ * x⁻¹) = (σ⁻¹ * x * σ) * x⁻¹ by group]
      exact Subgroup.mul_mem _ (component_le_layer hTm1 hu)
        (component_le_layer hTc (T.inv_mem hxT))
    have hdK : (⟨_, hdL⟩ : Lb) ∈ Kb := Subgroup.mem_subgroupOf.mpr ⟨_, hdV, rfl⟩
    rw [hKbot, Subgroup.mem_bot] at hdK
    have hdO : (⟨σ⁻¹ * (x * σ * x⁻¹), hdC⟩ : C) ∈ classicalInvolutionOddCore C :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hdK)
    have hodd := odd_orderOf_of_mem_oddCore hdO
    rw [Subgroup.orderOf_mk] at hodd
    exact hxc (mem_centralizer_of_acts_as hodd hx2
      (fun a ha => T.mul_mem (T.mul_mem hxT ha) (T.inv_mem hxT)) (acts_as_d hTc hσ hσT hxT hx2).1)
  · set zC : C := ⟨z, hLC hz.mem⟩ with hzC
    have hzLb : π zC ∈ Lb := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hz.mem)
    have hzO : π zC ≠ 1 := by
      intro h1
      have hodd := odd_orderOf_of_mem_oddCore ((QuotientGroup.eq_one_iff _).mp h1)
      rw [hzC, Subgroup.orderOf_mk, hz.orderOf_eq_two] at hodd
      exact (Nat.not_odd_iff_even.mpr even_two) hodd
    have hz2 : π zC ^ 2 = 1 := by
      rw [← map_pow]
      have : zC ^ 2 = 1 := Subtype.ext (by simpa [hzC] using hz.sq_eq_one)
      rw [this, map_one]
    have hzord : orderOf (⟨π zC, hzLb⟩ : Lb) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hz2 hzO
    have hzK := mem_of_isSubnormal_of_mulEquiv_sl2 eL hKsub hKbot hzord
    obtain ⟨v, hv, hvz⟩ := Subgroup.mem_subgroupOf.mp hzK
    have h1 : π (v⁻¹ * zC) = 1 := by rw [map_mul, map_inv, hvz, inv_mul_cancel]
    have hoO : v⁻¹ * zC ∈ classicalInvolutionOddCore C := (QuotientGroup.eq_one_iff _).mp h1
    have hodd := odd_orderOf_of_mem_oddCore hoO
    rw [← Subgroup.orderOf_coe] at hodd
    have hzT1 : z ∈ Subgroup.centralizer (T1 : Set G) :=
      mem_centralizer_of_eq_mul hT1c (by rw [← pow_two]; exact hz.sq_eq_one)
        (hz.mem_normalizer_of_isComponent ((isComponent_iff_open T1).mp hT1c))
        hv hodd (by simp [hzC])
    exact hTz (le_centralizer_of_conj (hz.commute_involution hσL) hzT1)

theorem core_false {L : Subgroup G} {z : G} (hz : IsClassicalMember3 L z) {T : Subgroup G}
    (hTc : IsComponent T) (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set G)) {x : G}
    (hxT : x ∈ T) (hxz : x * z = z * x) (hx2 : x * x = 1)
    (hxc : x ∉ Subgroup.centralizer (T : Set G)) {σ : G} (hσL : σ ∈ L) (hσ : Odd (orderOf σ))
    (hσT : conjSub σ T ≠ T) : False := by
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  have hxzx : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  have hL' : IsClassicalMember3 (conjSub x L) z := hxzx ▸ hz.conj x
  have hLC : L ≤ C := isSubnormal_le hz.subnormal
  have hL'C : conjSub x L ≤ C := isSubnormal_le hL'.subnormal
  have hσC : σ ∈ C := hLC hσL
  have hσ'L' : x * σ * x⁻¹ ∈ conjSub x L := conj_mem_conjSub hσL
  have hσ'C : x * σ * x⁻¹ ∈ C := hL'C hσ'L'
  have hdC : σ⁻¹ * (x * σ * x⁻¹) ∈ C := C.mul_mem (C.inv_mem hσC) hσ'C
  obtain ⟨e1⟩ := hz.nonempty_equiv
  obtain ⟨e2⟩ := hL'.nonempty_equiv
  have hxN : ∀ a ∈ T, x * a * x⁻¹ ∈ T := fun a ha => T.mul_mem (T.mul_mem hxT ha) (T.inv_mem hxT)
  rcases Uniform.twin_modOdd3_images (K := L.subgroupOf C) (J := (conjSub x L).subgroupOf C)
      (z := ⟨z, hLC hz.mem⟩) (Uniform.isSubnormal_subgroupOf_top hz.subnormal)
      (Uniform.isSubnormal_subgroupOf_top hL'.subnormal)
      (by rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two)
      (Subgroup.mem_subgroupOf.mpr hz.mem) (Subgroup.mem_subgroupOf.mpr hL'.mem)
      (Uniform.nonempty_quotEquiv_subgroupOf hLC e1)
      (Uniform.nonempty_quotEquiv_subgroupOf hL'C e2) with h | h
  · refine false_of_map_eq hz hTc hTz hxT hx2 hxc hσL hσ hσT hdC ?_
    have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (classicalInvolutionOddCore C))
      (Subgroup.mem_subgroupOf.mpr hσL : (⟨σ, hσC⟩ : C) ∈ L.subgroupOf C)
    have h2 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (classicalInvolutionOddCore C))
      (Subgroup.mem_subgroupOf.mpr hσ'L' :
        (⟨x * σ * x⁻¹, hσ'C⟩ : C) ∈ (conjSub x L).subgroupOf C)
    rw [← h] at h2
    have : (⟨σ⁻¹ * (x * σ * x⁻¹), hdC⟩ : C) = (⟨σ, hσC⟩ : C)⁻¹ * ⟨x * σ * x⁻¹, hσ'C⟩ := rfl
    rw [this, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) h2
  · set s : C := ⟨σ, hσC⟩ with hs
    set s' : C := ⟨x * σ * x⁻¹, hσ'C⟩ with hs'
    have hcomm : ⁅s, s'⁆ ∈ classicalInvolutionOddCore C :=
      h (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hσL)
        (Subgroup.mem_subgroupOf.mpr hσ'L'))
    have heO : (s⁻¹ * s⁻¹) * ⁅s, s'⁆⁻¹ * (s⁻¹ * s⁻¹)⁻¹ ∈ classicalInvolutionOddCore C :=
      (classicalInvolutionOddCore_normal C).conj_mem _ (Subgroup.inv_mem _ hcomm) _
    have he : (((s⁻¹ * s⁻¹) * ⁅s, s'⁆⁻¹ * (s⁻¹ * s⁻¹)⁻¹ : C) : G) =
        σ⁻¹ * (σ⁻¹ * (x * σ * x⁻¹)) * σ * (σ⁻¹ * (x * σ * x⁻¹))⁻¹ := by
      simp only [hs, hs', Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    have hodd := odd_orderOf_of_mem_oddCore heO
    rw [← Subgroup.orderOf_coe, he] at hodd
    exact hxc (mem_centralizer_of_acts_as hodd hx2 hxN (acts_as_e hTc hσ hσT hxT))

end CFSG.ClassicalInvolution.Q3.Q3T
