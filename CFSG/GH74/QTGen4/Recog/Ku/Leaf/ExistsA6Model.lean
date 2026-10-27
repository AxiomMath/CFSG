module

public import CFSG.GH74.QTGen4.Recog.Ku.PolarityE
public import CFSG.GH74.QTGen4.Recog.Ku.A6ModelC
public import CFSG.GH74.QTGen4.Recog.Ku.A6ModelE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem coordinates_C4C5
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ (ω : G → G → ZMod 2) (Φ : SpV → G), A6.CoordHyp (kuA P H) ω Φ ∧ Φ (spE 0) = z ∧
      (∀ v, Φ v ∈ kuW P H ↔ spForm (spE 0) v = 0) ∧
      (∀ v, Φ v ∈ kuV2 T M ↔ InV2m v) := by
  haveI hcomm : IsMulCommutative (kuA P H) := h.isMulCommutative_kuA
  letI : CommGroup (kuA P H) := IsMulCommutative.instCommGroup
  have hsq : ∀ x : kuA P H, x * x = 1 := fun x => by
    apply Subtype.ext
    have hx2 := h.isElemAbelian_kuA.2 (x : G) x.2
    rw [pow_two] at hx2
    exact hx2
  have hωA : A6.IsPolarForm (fun x y : kuA P H => kuPolar P H z (x : G) (y : G)) :=
    { mul_left := fun x y w => h.kuPolar_mul_left x.2 y.2 w.2
      mul_right := fun w x y => h.kuPolar_mul x.2 y.2 (w : G)
      alt := fun x => h.kuPolar_self (x : G) }
  have hnd : ∀ x : kuA P H, (∀ w : kuA P H, kuPolar P H z (x : G) (w : G) = 0) → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨y, hy, hne⟩ := h.exists_kuPolar_ne_zero_right x.2 (fun e => hx1 (Subtype.ext e))
    exact hne (hx ⟨y, hy⟩)
  obtain ⟨zA, hzA⟩ : ∃ zA : kuA P H, (zA : G) = z := ⟨⟨z, h.z_mem_kuA⟩, rfl⟩
  obtain ⟨z', hz'V, hz'1, hz'z, -⟩ := h.exists_z'
  obtain ⟨z'A, hz'A⟩ : ∃ z'A : kuA P H, (z'A : G) = z' :=
    ⟨⟨z', h.kuW_le_kuA (h.kuV2_le_kuW hz'V)⟩, rfl⟩
  have hzA1 : zA ≠ 1 := by
    intro e
    apply h.z_ne_one
    have e' := congrArg Subtype.val e
    rw [hzA] at e'
    exact e'
  have hz'A1 : z'A ≠ 1 := by
    intro e
    apply hz'1
    have e' := congrArg Subtype.val e
    rw [hz'A] at e'
    exact e'
  have hzzA : z'A ≠ zA := by
    intro e
    apply hz'z
    have e' := congrArg Subtype.val e
    rw [hz'A, hzA] at e'
    exact e'
  have hzz' : kuPolar P H z (zA : G) (z'A : G) = 0 := by
    rw [hzA, hz'A]
    exact (h.kuPolar_z_eq_zero_iff z').mpr (h.kuV2_le_kuW hz'V)
  have hW : ∀ x : kuA P H, x ∈ {x : kuA P H | (x : G) ∈ kuW P H} ↔
      kuPolar P H z (zA : G) (x : G) = 0 := by
    intro x
    rw [hzA]
    exact (h.kuPolar_z_eq_zero_iff (x : G)).symm
  have hzz_mul : z * z = 1 := h.z_mul_z
  have hzz1 : z * z' ≠ 1 := by
    intro e
    apply hz'z
    calc z' = (z * z) * z' := by rw [hzz_mul, one_mul]
      _ = z * (z * z') := by group
      _ = z := by rw [e, mul_one]
  have hS : (kuV2 T M : Set G) = {1, z, z', z * z'} := by
    have hsub : ({1, z, z', z * z'} : Set G) ⊆ (kuV2 T M : Set G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact (kuV2 T M).one_mem
      · exact h.z_mem_kuV2
      · exact hz'V
      · exact (kuV2 T M).mul_mem h.z_mem_kuV2 hz'V
    have h1S : (1 : G) ∉ ({z, z', z * z'} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun e => h.z_ne_one e.symm, fun e => hz'1 e.symm, fun e => hzz1 e.symm⟩
    have h2S : z ∉ ({z', z * z'} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨fun e => hz'z e.symm, fun e => hz'1 ?_⟩
      calc z' = z⁻¹ * (z * z') := by group
        _ = z⁻¹ * z := by rw [← e]
        _ = 1 := by group
    have h3S : z' ≠ z * z' := by
      intro e
      apply h.z_ne_one
      calc z = (z * z') * z'⁻¹ := by group
        _ = z' * z'⁻¹ := by rw [← e]
        _ = 1 := by group
    have hcard4 : ({1, z, z', z * z'} : Set G).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem h1S (Set.toFinite _),
        Set.ncard_insert_of_notMem h2S (Set.toFinite _), Set.ncard_pair h3S]
    have hcardV : (kuV2 T M : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h.card_kuV2
    exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm
  have hV : ∀ x : kuA P H, x ∈ {x : kuA P H | (x : G) ∈ kuV2 T M} ↔
      ∃ a c : ZMod 2, x = A6.zp zA a * A6.zp z'A c := by
    intro x
    show (x : G) ∈ (kuV2 T M : Set G) ↔ _
    rw [hS]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h1 | h1 | h1 | h1)
      · exact ⟨0, 0, by rw [A6.zp_zero, A6.zp_zero, mul_one]; exact Subtype.ext h1⟩
      · exact ⟨1, 0, by
          rw [A6.zp_one, A6.zp_zero, mul_one]; exact Subtype.ext (h1.trans hzA.symm)⟩
      · exact ⟨0, 1, by
          rw [A6.zp_zero, A6.zp_one, one_mul]; exact Subtype.ext (h1.trans hz'A.symm)⟩
      · exact ⟨1, 1, by
          rw [A6.zp_one, A6.zp_one]
          exact Subtype.ext (by rw [Subgroup.coe_mul, hzA, hz'A]; exact h1)⟩
    · rintro ⟨a, c, rfl⟩
      rcases A6.zmod2_cases a with rfl | rfl <;> rcases A6.zmod2_cases c with rfl | rfl <;>
        simp [A6.zp_zero, A6.zp_one, hzA, hz'A]
  obtain ⟨b, hb0, _hb3, hG, hbij, hWcl, hV2cl⟩ :=
    A6.coordinates_of_polar hωA hsq hnd h.card_kuA hzA1 hz'A1 hzzA hzz'
      {x : kuA P H | (x : G) ∈ kuW P H} {x : kuA P H | (x : G) ∈ kuV2 T M} hW hV
  have hmem : ∀ v : SpV, ((A6.coordMap b v : kuA P H) : G) ∈ kuA P H :=
    fun v => (A6.coordMap b v).2
  have hinj : Function.Injective (fun v : SpV => ((A6.coordMap b v : kuA P H) : G)) :=
    fun u v huv => hbij.1 (Subtype.ext huv)
  have hadd : ∀ v w : SpV, ((A6.coordMap b (v + w) : kuA P H) : G) =
      ((A6.coordMap b v : kuA P H) : G) * ((A6.coordMap b w : kuA P H) : G) :=
    fun v w => congrArg Subtype.val (A6.coordMap_add (fun k => hsq (b k)) v w)
  have hsurj : ∀ x ∈ kuA P H, ∃ v : SpV, ((A6.coordMap b v : kuA P H) : G) = x := by
    intro x hx
    obtain ⟨v, hv⟩ := hbij.2 ⟨x, hx⟩
    exact ⟨v, congrArg Subtype.val hv⟩
  have hform : ∀ u v : SpV, kuPolar P H z ((A6.coordMap b u : kuA P H) : G)
      ((A6.coordMap b v : kuA P H) : G) = spForm u v :=
    fun u v => A6.coordMap_gram hωA hG u v
  have hinv : ∀ n ∈ Subgroup.normalizer (kuA P H : Set G), ∀ x ∈ kuA P H, ∀ y ∈ kuA P H,
      kuPolar P H z (n * x * n⁻¹) (n * y * n⁻¹) = kuPolar P H z x y :=
    fun n hn x _ y _ => kuPolar_conj_conj hn x y
  have hcomm' : ∀ x ∈ kuA P H, ∀ y ∈ kuA P H, x * y = y * x :=
    fun x hx y hy => h.kuA_comm hx hy
  have hcent : Subgroup.centralizer (kuA P H : Set G) ≤ kuA P H :=
    h.centralizer_kuA_eq.le
  have he0 : ((A6.coordMap b (spE 0) : kuA P H) : G) = z := by
    rw [A6.coordMap_spE, hb0, hzA]
  exact ⟨kuPolar P H z, fun v => ((A6.coordMap b v : kuA P H) : G),
    ⟨hmem, hinj, hadd, hsurj, hform, hinv, hcomm', hcent⟩, he0,
    fun v => hWcl v, fun v => hV2cl v⟩

end KuHyp

theorem leafExistsA6Model
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafHInfCentralizerKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafExistsA6Model := by
  intro G _ _ T M H P z h
  obtain ⟨ω, Φ, hΦ, he0, hpol, hv2⟩ := h.coordinates_C4C5
  exact A6.nonempty_kuA6Model h.card_kuN h.card_kuA hΦ he0 hpol hv2


end CFSG.GH74.QTGen4.Ku
