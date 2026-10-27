module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesBasic
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelBasic

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open scoped commutatorElement

section Ambient

variable {H H' : Type*} [Group H] [Group H']

structure SuzukiSylowFacts (V : Subgroup H) : Prop where
  center_mul_self : ∀ z ∈ zIn V, z * z = 1
  mul_self_mem : ∀ c ∈ V, c * c ∈ ⁅V, V⁆
  commutator_le : ⁅V, V⁆ ≤ zIn V
  mem_center : ∀ v ∈ V, v * v = 1 → v ∈ zIn V

namespace SuzukiSylowFacts

variable {φ : H →* H'} (hφ : Function.Injective φ) {V : Subgroup H}
include hφ

theorem map (h : SuzukiSylowFacts V) : SuzukiSylowFacts (V.map φ) := by
  have hZ := map_zIn hφ V
  have hC : ⁅V.map φ, V.map φ⁆ = ⁅V, V⁆.map φ := (map_commutator V V φ).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [← hZ] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [← map_mul, h.center_mul_self z₀ hz₀, map_one]
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_mul, hC]
    exact mem_map_of_mem φ (h.mul_self_mem c hc)
  · rw [hC, ← hZ]
    exact map_mono h.commutator_le
  · rintro _ ⟨v, hv, rfl⟩ hvv
    rw [← map_mul, ← map_one φ] at hvv
    rw [← hZ]
    exact mem_map_of_mem φ (h.mem_center v hv (hφ hvv))

theorem of_map (h : SuzukiSylowFacts (V.map φ)) : SuzukiSylowFacts V := by
  have hZ := map_zIn hφ V
  have hC : ⁅V.map φ, V.map φ⁆ = ⁅V, V⁆.map φ := (map_commutator V V φ).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    apply hφ
    rw [map_mul, map_one]
    exact h.center_mul_self _ (by rw [← hZ]; exact mem_map_of_mem φ hz)
  · intro c hc
    have := h.mul_self_mem _ (mem_map_of_mem φ hc)
    rwa [← map_mul, hC, mem_map_iff_mem hφ] at this
  · intro c hc
    have := h.commutator_le (by rw [hC]; exact mem_map_of_mem φ hc)
    rwa [← hZ, mem_map_iff_mem hφ] at this
  · intro v hv hvv
    have := h.mem_center _ (mem_map_of_mem φ hv) (by rw [← map_mul, hvv, map_one])
    rwa [← hZ, mem_map_iff_mem hφ] at this

end SuzukiSylowFacts

namespace BenderSylow

variable {φ : H →* H'} (hφ : Function.Injective φ) {D : Subgroup H} {a : H} {V W : Subgroup H}
include hφ

omit hφ in
theorem self (h : BenderSylow D a V W) : BenderSylow W a V W :=
  { h with le_D := le_rfl, not_mem := h.not_mem_W, unique := fun _ hSW _ _ => hSW }

theorem map (h : BenderSylow D a V W) : BenderSylow (D.map φ) (φ a) (V.map φ) (W.map φ) := by
  have hZW := map_zIn hφ W
  have hZV := map_zIn hφ V
  have hcomm : ⁅W.map φ, W.map φ⁆ ⊔ V.map φ = (⁅W, W⁆ ⊔ V).map φ := by
    rw [Subgroup.map_sup, map_commutator]
  have hconj : ∀ x, (φ a)⁻¹ * φ x * φ a = φ (a⁻¹ * x * a) := fun x => by
    rw [map_mul, map_mul, map_inv]
  refine
    { mul_self := by rw [← map_mul, h.mul_self, map_one]
      not_mem := fun ha => h.not_mem ((mem_map_iff_mem hφ).1 ha)
      le_D := map_mono h.le_D
      isPGroup := h.isPGroup.map φ
      le := map_mono h.le
      unique := ?_
      conj_mem := ?_
      inf_centralizer := ?_
      center_mul_self := ?_
      mul_self_mem := ?_
      center_comm_mem := ?_
      exists_center_comm := ?_
      comm_mem := ?_
      le_commutator := ?_
      exists_comm_mod := ?_
      mem_of_comm := ?_
      mem_center := ?_ }
  · intro S hSD hS hVS
    have hSr : S ≤ φ.range := hSD.trans (map_le_range φ D)
    have hS₀ : IsPGroup 2 (S.comap φ) := hS.comap_of_injective φ hφ
    have hVS₀ : V ≤ S.comap φ := fun v hv => hVS (mem_map_of_mem φ hv)
    have hSD₀ : S.comap φ ≤ D := fun x hx => (mem_map_iff_mem hφ).1 (hSD hx)
    rw [← map_comap_eq_self hSr]
    exact map_mono (h.unique _ hSD₀ hS₀ hVS₀)
  · rintro _ ⟨w, hw, rfl⟩
    rw [hconj]
    exact mem_map_of_mem φ (h.conj_mem w hw)
  · ext x
    constructor
    · intro hx
      obtain ⟨⟨w, hw, rfl⟩, hxa⟩ := mem_inf.mp hx
      have h1 : φ (w * a) = φ (a * w) := by
        rw [map_mul, map_mul]
        exact mem_centralizer_singleton_iff.mp hxa
      have hwV : w ∈ V := by
        rw [← h.inf_centralizer]
        exact mem_inf.mpr ⟨hw, mem_centralizer_singleton_iff.mpr (hφ h1)⟩
      exact mem_map_of_mem φ hwV
    · rintro ⟨v, hv, rfl⟩
      have hv' : v ∈ W ⊓ centralizer ({a} : Set H) := h.inf_centralizer ▸ hv
      obtain ⟨hvW, hva⟩ := mem_inf.mp hv'
      refine mem_inf.mpr ⟨mem_map_of_mem φ hvW, mem_centralizer_singleton_iff.mpr ?_⟩
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hva]
  · intro z hz
    rw [← hZW] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [← map_mul, h.center_mul_self z₀ hz₀, map_one]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← hZW]
    exact mem_map_of_mem φ (h.mul_self_mem w hw)
  · intro z hz
    rw [← hZW] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [hconj, ← map_inv, ← map_mul, ← hZV]
    exact mem_map_of_mem φ (h.center_comm_mem z₀ hz₀)
  · intro v hv
    rw [← hZV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    obtain ⟨z₀, hz₀, hv₀z⟩ := h.exists_center_comm v₀ hv₀
    refine ⟨φ z₀, by rw [← hZW]; exact mem_map_of_mem φ hz₀, ?_⟩
    rw [hconj, ← map_inv, ← map_mul, hv₀z]
  · rintro _ ⟨w, hw, rfl⟩
    rw [hconj, ← map_inv, ← map_mul, hcomm]
    exact mem_map_of_mem φ (h.comm_mem w hw)
  · rw [hcomm, ← MonoidHom.map_zpowers, ← map_commutator]
    exact map_mono h.le_commutator
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hy, hvy⟩ := h.exists_comm_mod v hv
    refine ⟨φ y, mem_map_of_mem φ hy, ?_⟩
    rw [hconj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← hZW]
    exact mem_map_of_mem φ hvy
  · rintro _ ⟨w, hw, rfl⟩ hwc
    rw [hconj, ← map_inv, ← map_mul, ← hZW, mem_map_iff_mem hφ] at hwc
    rw [← hZW, ← Subgroup.map_sup]
    exact mem_map_of_mem φ (h.mem_of_comm w hw hwc)
  · rintro _ ⟨v, hv, rfl⟩ hvv
    rw [← map_mul, ← map_one φ] at hvv
    rw [← hZW]
    exact mem_map_of_mem φ (h.mem_center v hv (hφ hvv))

theorem comap {D' : Subgroup H'} (h : BenderSylow D' (φ a) (V.map φ) (W.map φ)) :
    BenderSylow (D'.comap φ) a V W := by
  have hZW := map_zIn hφ W
  have hZV := map_zIn hφ V
  have hcomm : ⁅W.map φ, W.map φ⁆ ⊔ V.map φ = (⁅W, W⁆ ⊔ V).map φ := by
    rw [Subgroup.map_sup, map_commutator]
  have hconj : ∀ x, (φ a)⁻¹ * φ x * φ a = φ (a⁻¹ * x * a) := fun x => by
    rw [map_mul, map_mul, map_inv]
  have hzW : ∀ {z}, z ∈ zIn W → φ z ∈ zIn (W.map φ) := fun hz => by
    rw [← hZW]; exact mem_map_of_mem φ hz
  refine
    { mul_self := hφ (by rw [map_mul, h.mul_self, map_one])
      not_mem := fun ha => h.not_mem ha
      le_D := fun w hw => h.le_D (mem_map_of_mem φ hw)
      isPGroup := h.isPGroup.of_equiv (W.equivMapOfInjective φ hφ).symm
      le := (map_le_map_iff_of_injective hφ).1 h.le
      unique := fun S hSD hS hVS => (map_le_map_iff_of_injective hφ).1
        (h.unique _ (map_le_iff_le_comap.2 hSD) (hS.map φ) (map_mono hVS))
      conj_mem := fun w hw => by
        have := h.conj_mem _ (mem_map_of_mem φ hw)
        rwa [hconj, mem_map_iff_mem hφ] at this
      inf_centralizer := ?_
      center_mul_self := fun z hz => hφ (by
        rw [map_mul, map_one]
        exact h.center_mul_self _ (hzW hz))
      mul_self_mem := fun w hw => by
        have := h.mul_self_mem _ (mem_map_of_mem φ hw)
        rwa [← map_mul, ← hZW, mem_map_iff_mem hφ] at this
      center_comm_mem := fun z hz => by
        have := h.center_comm_mem _ (hzW hz)
        rwa [hconj, ← map_inv, ← map_mul, ← hZV, mem_map_iff_mem hφ] at this
      exists_center_comm := ?_
      comm_mem := fun w hw => by
        have := h.comm_mem _ (mem_map_of_mem φ hw)
        rwa [hconj, ← map_inv, ← map_mul, hcomm, mem_map_iff_mem hφ] at this
      le_commutator := (map_le_map_iff_of_injective hφ).1 (by
        rw [← hcomm, map_commutator, MonoidHom.map_zpowers]
        exact h.le_commutator)
      exists_comm_mod := ?_
      mem_of_comm := fun w hw hwc => by
        have := h.mem_of_comm _ (mem_map_of_mem φ hw) (by
          rw [hconj, ← map_inv, ← map_mul]
          exact hzW hwc)
        rwa [← hZW, ← Subgroup.map_sup, mem_map_iff_mem hφ] at this
      mem_center := fun v hv hvv => by
        have := h.mem_center _ (mem_map_of_mem φ hv) (by rw [← map_mul, hvv, map_one])
        rwa [← hZW, mem_map_iff_mem hφ] at this }
  · ext x
    constructor
    · intro hx
      obtain ⟨hxW, hxa⟩ := mem_inf.mp hx
      have h1 : φ x ∈ W.map φ ⊓ centralizer ({φ a} : Set H') := by
        refine mem_inf.mpr ⟨mem_map_of_mem φ hxW, mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hxa]
      rw [h.inf_centralizer, mem_map_iff_mem hφ] at h1
      exact h1
    · intro hx
      have h1 : φ x ∈ W.map φ ⊓ centralizer ({φ a} : Set H') := by
        rw [h.inf_centralizer]
        exact mem_map_of_mem φ hx
      obtain ⟨hxW, hxa⟩ := mem_inf.mp h1
      refine mem_inf.mpr ⟨(mem_map_iff_mem hφ).1 hxW, mem_centralizer_singleton_iff.mpr ?_⟩
      apply hφ
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hxa
  · intro v hv
    have hv' : φ v ∈ zIn (V.map φ) := by rw [← hZV]; exact mem_map_of_mem φ hv
    obtain ⟨z', hz', hvz⟩ := h.exists_center_comm _ hv'
    rw [← hZW] at hz'
    obtain ⟨z, hz, rfl⟩ := hz'
    refine ⟨z, hz, hφ ?_⟩
    rw [hvz, hconj, ← map_inv, ← map_mul]
  · intro v hv
    obtain ⟨y', hy', hvy⟩ := h.exists_comm_mod _ (mem_map_of_mem φ hv)
    obtain ⟨y, hy, rfl⟩ := hy'
    refine ⟨y, hy, ?_⟩
    rwa [hconj, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← hZW, mem_map_iff_mem hφ] at hvy

end BenderSylow

end Ambient

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem fourCoordG_zero_zero (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4) :
    fourCoordG a f (0 : K) 0 = 1 := by
  have e := fourCoordG_mul_fourCoordG hK f (0 : K) 0 0 0
  simp only [add_zero, largeReeSigma_zero, zero_mul] at e
  exact mul_eq_left.mp e

theorem fourCoordG_mul_self (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4) (b c : K) :
    fourCoordG a f b c * fourCoordG a f b c = fourCoordG a f 0 (largeReeSigma a b * b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [fourCoordG_mul_fourCoordG hK]
  congr 1
  · linear_combination b * h2
  · linear_combination c * h2

theorem fourCoordG_commutator (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : Fin 4) (b c b' c' : K) :
    ⁅fourCoordG a f b c, fourCoordG a f b' c'⁆ =
      fourCoordG a f 0 (largeReeSigma a b * b' + largeReeSigma a b' * b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have e : fourCoordG a f b c * fourCoordG a f b' c' =
      fourCoordG a f 0 (largeReeSigma a b * b' + largeReeSigma a b' * b) *
        (fourCoordG a f b' c' * fourCoordG a f b c) := by
    rw [fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK,
      largeReeSigma_zero, zero_mul, add_zero, zero_add]
    congr 1
    · ring
    · linear_combination (-(largeReeSigma a b' * b)) * h2
  rw [commutatorElement_def, e]
  group

theorem exists_eq_fourCoordG_of_mem_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) {g : ModGL F4.tag K} (hg : g ∈ rootV K a i) :
    ∃ b c : K, g = fourCoordG a i.fourIdx b c := by
  have hg' : g ∈ (rootV K a i : Set (ModGL F4.tag K)) := hg
  rw [coe_rootV hK] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  exact ⟨_, _, (sylowVec_eq_of_supp i hx).1 hi⟩

theorem exists_eq_fourCoordG_of_mem_rootV_center (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) {g : ModGL F4.tag K} (hg : g ∈ rootV K a i.center) :
    ∃ c : K, g = fourCoordG a i.fourIdx 0 c := by
  have hci : i.center.isCenter = true := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter]
  have hf : i.center.fourIdx = i.fourIdx := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.fourIdx]
  have hcsz : i.center.isSz = false := by cases i <;> simp_all [Idx.isSz, Idx.center]
  have hg' : g ∈ (rootV K a i.center : Set (ModGL F4.tag K)) := hg
  rw [coe_rootV hK] at hg'
  obtain ⟨x, hx, rfl⟩ := hg'
  rw [(sylowVec_eq_of_supp i.center hx).2 hcsz, (rootElt_eq_coord _ _).2.1 hci, hf]
  exact ⟨_, rfl⟩

theorem fourCoordG_mem_rootV (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx} (hi : i.isSz = true)
    (b c : K) : fourCoordG a i.fourIdx b c ∈ rootV K a i := by
  have hci : i.center.isCenter = true := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter]
  have hf : i.center.fourIdx = i.fourIdx := by
    cases i <;> simp_all [Idx.isSz, Idx.center, Idx.fourIdx]
  rw [fourCoordG_eq_mul hK]
  refine mul_mem ?_ ((rootV_center_le hK i).1 ?_)
  · rw [← (rootElt_eq_coord i b).1 hi]
    exact rootElt_mem_rootV _ _
  · rw [← hf, ← (rootElt_eq_coord i.center c).2.1 hci]
    exact rootElt_mem_rootV _ _

theorem zIn_rootV (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) : zIn (rootV K a i) = rootV K a i.center := by
  rw [zIn, inf_comm]
  exact rootV_inf_centralizer ha hK hi

theorem fourCoordG_zero_mem_zIn (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) (c : K) : fourCoordG a i.fourIdx 0 c ∈ zIn (rootV K a i) := by
  refine mem_zIn.mpr ⟨fun w hw => ?_, fourCoordG_mem_rootV hK hi 0 c⟩
  obtain ⟨b', c', rfl⟩ := exists_eq_fourCoordG_of_mem_rootV hK hi hw
  rw [fourCoordG_mul_fourCoordG hK, fourCoordG_mul_fourCoordG hK, largeReeSigma_zero, zero_mul,
    mul_zero, add_zero, add_zero, zero_add, add_zero, add_comm c' c]

theorem suzukiSylowFacts_rootV (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {i : Idx}
    (hi : i.isSz = true) : SuzukiSylowFacts (rootV K a i) := by
  have hZ := zIn_rootV ha hK hi
  have hmemZ : ∀ c : K, fourCoordG a i.fourIdx 0 c ∈ zIn (rootV K a i) :=
    fourCoordG_zero_mem_zIn hK hi
  have hcomm : ∀ e : K, fourCoordG a i.fourIdx 0 e ∈ ⁅rootV K a i, rootV K a i⁆ := by
    intro e
    obtain ⟨l, hl⟩ := exists_largeReeSigma_ne ha hK
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hd : l + largeReeSigma a l ≠ 0 := by
      intro h0
      apply hl
      linear_combination h0 - l * h2
    obtain ⟨x, hx⟩ := exists_largeReeSigma_mul_self_eq hK (e / (l + largeReeSigma a l))
    have key := fourCoordG_commutator hK i.fourIdx x 0 (x * l) 0
    have hσ : largeReeSigma a (x * l) = largeReeSigma a x * largeReeSigma a l := by
      simp only [largeReeSigma, mul_pow]
    have he : largeReeSigma a x * (x * l) + largeReeSigma a (x * l) * x = e := by
      rw [hσ]
      calc largeReeSigma a x * (x * l) + largeReeSigma a x * largeReeSigma a l * x =
          largeReeSigma a x * x * (l + largeReeSigma a l) := by ring
        _ = e := by rw [hx, div_mul_cancel₀ _ hd]
    rw [he] at key
    rw [← key]
    exact commutator_mem_commutator (fourCoordG_mem_rootV hK hi _ _)
      (fourCoordG_mem_rootV hK hi _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hZ] at hz
    obtain ⟨c, rfl⟩ := exists_eq_fourCoordG_of_mem_rootV_center hK hi hz
    rw [fourCoordG_mul_self hK, largeReeSigma_zero, zero_mul, fourCoordG_zero_zero hK]
  · intro g hg
    obtain ⟨b, c, rfl⟩ := exists_eq_fourCoordG_of_mem_rootV hK hi hg
    rw [fourCoordG_mul_self hK]
    exact hcomm _
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨b, c, rfl⟩ := exists_eq_fourCoordG_of_mem_rootV hK hi hx
    obtain ⟨b', c', rfl⟩ := exists_eq_fourCoordG_of_mem_rootV hK hi hy
    rw [fourCoordG_commutator hK]
    exact hmemZ _
  · intro v hv hvv
    obtain ⟨b, c, rfl⟩ := exists_eq_fourCoordG_of_mem_rootV hK hi hv
    rw [fourCoordG_mul_self hK, ← fourCoordG_zero_zero hK i.fourIdx] at hvv
    have hb : largeReeSigma a b * b = 0 := (fourCoordG_injective hK _ hvv).2
    have hb0 : b = 0 := by
      rcases mul_eq_zero.mp hb with h | h
      · exact (largeReeSigma_eq_zero_iff b).mp h
      · exact h
    rw [hb0]
    exact hmemZ c

end Model

end CFSG.LocalAnalysis.EvenBN.TwoF4
