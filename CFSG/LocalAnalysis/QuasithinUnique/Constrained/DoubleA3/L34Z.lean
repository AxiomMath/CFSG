module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34Cls

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem centralizerElem_map_conj (z g : G) :
    (centralizerElem z).map (MulAut.conj g⁻¹).toMonoidHom = centralizerElem (g⁻¹ * z * g) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * x * g * (g⁻¹ * z * g) = g⁻¹ * (x * z) * g := by group
      _ = g⁻¹ * (z * x) * g := by rw [hx']
      _ = g⁻¹ * z * g * (g⁻¹ * x * g) := by group
  · intro hy
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine ⟨g * y * g⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc g * y * g⁻¹ * z = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by rw [hy']
        _ = z * (g * y * g⁻¹) := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group

theorem charTwo_centralizerElem_of_mem_conjClass {z u : G} (hz : CharTwo (centralizerElem z))
    (hu : u ∈ conjClass z) : CharTwo (centralizerElem u) := by
  obtain ⟨g, rfl⟩ := hu
  have h1 := Ch1.charTwo_map_mulEquiv (MulAut.conj g⁻¹) hz
  rwa [centralizerElem_map_conj] at h1

theorem exists_card_three_normalized {Y Hc : Subgroup G} (hY : Nat.card Y = 6)
    (hH : Hc ≤ normalizer (Y : Set G)) :
    ∃ A ≤ Y, Nat.card A = 3 ∧ Hc ≤ normalizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by omega)
  have h3 : 3 ∣ Nat.card Y := by rw [hY]; norm_num
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have haG : orderOf (a : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  set A : Subgroup G := Subgroup.zpowers (a : G) with hAdef
  have hAY : A ≤ Y := Subgroup.zpowers_le.mpr a.2
  have hA3 : Nat.card A = 3 := by rw [hAdef, Nat.card_zpowers, haG]
  have hidx : (A.subgroupOf Y).index = 2 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hA3, hY] at h1
    omega
  have hw3 : ∀ w ∈ A, w ^ 3 = 1 := fun w hw => by
    have h1 := pow_card_eq_one' (G := ↥A) (x := ⟨w, hw⟩)
    rw [hA3] at h1
    simpa using congrArg Subtype.val h1
  have hmem : ∀ v ∈ Y, v ^ 3 = 1 → v ∈ A := by
    intro v hv hv3
    have h1 : (⟨v, hv⟩ : ↥Y) ^ 2 ∈ A.subgroupOf Y := Subgroup.sq_mem_of_index_two hidx ⟨v, hv⟩
    have h2 : v ^ 2 ∈ A := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3' : v = (v ^ 2) ^ 2 := by
      calc v = v ^ 3 * v := by rw [hv3, one_mul]
        _ = (v ^ 2) ^ 2 := by group
    rw [h3']
    exact pow_mem h2 2
  refine ⟨A, hAY, hA3, fun h hh => ?_⟩
  have hhY : h ∈ normalizer (Y : Set G) := hH hh
  have key : ∀ k ∈ Hc, ∀ w ∈ A, k * w * k⁻¹ ∈ A := by
    intro k hk w hw
    have hkY : k ∈ normalizer (Y : Set G) := hH hk
    have hwY : k * w * k⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hkY w).mp (hAY hw)
    apply hmem _ hwY
    rw [conj_pow, hw3 w hw]
    group
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact key h hh w
  · intro hw
    have := key h⁻¹ (Hc.inv_mem hh) _ hw
    have e : h⁻¹ * (h * w * h⁻¹) * h⁻¹⁻¹ = w := by group
    rwa [e] at this

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section Z

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))

theorem A3A3K.charTwo_centralizerElem_z (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hK : A3A3K T M H S L s x z₁ z₂ K) : CharTwo (centralizerElem (z₁ * z₂)) := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hzT := z_central hB hK.toA3A3x
  have hz1 : z₁ * z₂ ≠ 1 := hK.toA3A3x.z_ne
  have hz2 : (z₁ * z₂) ^ 2 = 1 := hK.toA3A3x.sq_z
  have hTc : T ≤ centralizerElem (z₁ * z₂) := fun t ht =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT.2 t ht)
  have hpc : pCoreOf 2 (centralizerElem (z₁ * z₂)) ≠ ⊥ := pCoreOf_centralizerElem_ne_bot hz1 hz2
  exact charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hcs.setting.qtke.2.1 hcs.setting.sylow hTc hpc

include hD h27_1 hI hK hc

theorem A3A3K.not_mem_conjClass_z_of_outer
    {u : G} (hu2 : u * u = 1)
    (huK : u ∈ normalizer (K : Set G)) (huz₂ : u * z₂ = z₂ * u)
    (hout : ¬ ∃ k ∈ K, ∀ y ∈ K, u⁻¹ * y * u = k⁻¹ * y * k) : u ∉ conjClass (z₁ * z₂) := by
  intro hu
  have hchar : CharTwo (centralizerElem u) :=
    charTwo_centralizerElem_of_mem_conjClass (hK.charTwo_centralizerElem_z hD h27_1) hu
  have hz₂ord : orderOf z₂ = 2 := orderOf_eq_prime hK.toA3A3x.sq₂ hK.toA3A3x.z₂_ne
  have hX : IsPGroup 2 (Subgroup.zpowers z₂) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hz₂ord]
    exact ⟨1, by simp⟩
  have hXu : Subgroup.zpowers z₂ ≤ centralizerElem u := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr huz₂.symm
  have hHc : CharTwo (centralizerElem u ⊓ Subgroup.centralizer ((Subgroup.zpowers z₂ : Subgroup G) : Set G)) :=
    CharTwo.inf_centralizer hchar hXu hX
  have hY6 := card_inf_centralizer_eq_six (hK.l27Aut_K hD h27_1 hI hc) huK hu2 hout
  have hKz : K ≤ centralizerElem z₂ := hK.K_comp.1
  have hczX : ∀ a ∈ centralizerElem z₂, a ∈ Subgroup.centralizer ((Subgroup.zpowers z₂ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have hz : z₂ * a = a * z₂ := (Subgroup.mem_centralizer_singleton_iff.mp ha).symm
    exact (Commute.zpow_left (show Commute z₂ a from hz) k).eq
  have hHcY : (centralizerElem u ⊓ Subgroup.centralizer ((Subgroup.zpowers z₂ : Subgroup G) : Set G)) ≤
      normalizer ((K ⊓ centralizerElem u : Subgroup G) : Set G) := by
    intro h hh
    have hhz₂ : h ∈ centralizerElem z₂ :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z₂)) hh.2
    have hhK : h ∈ normalizer (K : Set G) := hK.K_norm hhz₂
    have hhu : h ∈ centralizerElem u := hh.1
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp hhK y).mp hy.1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hhu) y).mp hy.2⟩
    · intro hy
      exact ⟨(Subgroup.mem_normalizer_iff.mp hhK y).mpr hy.1,
        (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hhu) y).mpr hy.2⟩
  obtain ⟨A, hAY, hA3, hAn⟩ := exists_card_three_normalized hY6 hHcY
  have hAHc : A ≤ centralizerElem u ⊓ Subgroup.centralizer ((Subgroup.zpowers z₂ : Subgroup G) : Set G) :=
    fun a ha => ⟨(hAY ha).2, hczX a (hKz (hAY ha).1)⟩
  have hbot := hHc.eq_bot_of_odd_card hAHc hAn (by rw [hA3]; decide)
  rw [hbot, Subgroup.card_bot] at hA3
  omega

end Z

end Main

end CFSG.QuasithinUnique.DoubleA3
