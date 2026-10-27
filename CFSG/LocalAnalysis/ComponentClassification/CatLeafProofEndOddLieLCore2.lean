module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.CatLeafProof.EndOddCore

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped commutatorElement

variable {S : Type*} [Group S] {Z : Subgroup S} [Z.Normal]

theorem mem_centralizer_mk_iff (T g : S) :
    QuotientGroup.mk' Z g ∈ centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)) ↔
      g * T * g⁻¹ * T⁻¹ ∈ Z := by
  rw [mem_centralizer_singleton_iff, ← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  change QuotientGroup.mk' Z g * QuotientGroup.mk' Z T = QuotientGroup.mk' Z T *
      QuotientGroup.mk' Z g ↔ QuotientGroup.mk' Z g * QuotientGroup.mk' Z T *
      (QuotientGroup.mk' Z g)⁻¹ * (QuotientGroup.mk' Z T)⁻¹ = 1
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc QuotientGroup.mk' Z g * QuotientGroup.mk' Z T =
        (QuotientGroup.mk' Z g * QuotientGroup.mk' Z T * (QuotientGroup.mk' Z g)⁻¹ *
          (QuotientGroup.mk' Z T)⁻¹) * (QuotientGroup.mk' Z T * QuotientGroup.mk' Z g) := by group
      _ = QuotientGroup.mk' Z T * QuotientGroup.mk' Z g := by rw [h, one_mul]

theorem conj_mem_centralizer (hZ : Z ≤ center S) {T g c : S}
    (hg : QuotientGroup.mk' Z g ∈ centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)))
    (hc : c ∈ centralizer ({T} : Set S)) : g * c * g⁻¹ ∈ centralizer ({T} : Set S) := by
  rw [mem_centralizer_mk_iff] at hg
  set w := g * T * g⁻¹ * T⁻¹ with hw
  have hwc : ∀ y : S, w * y = y * w := fun y => (mem_center_iff.mp (hZ hg) y).symm
  have hgT : g * T * g⁻¹ = w * T := by rw [hw]; group
  have hcT : c * T = T * c := mem_centralizer_singleton_iff.mp hc
  rw [mem_centralizer_singleton_iff]
  have h1 : (g * c * g⁻¹) * (g * T * g⁻¹) = (g * T * g⁻¹) * (g * c * g⁻¹) := by
    calc (g * c * g⁻¹) * (g * T * g⁻¹) = g * (c * T) * g⁻¹ := by group
      _ = g * (T * c) * g⁻¹ := by rw [hcT]
      _ = (g * T * g⁻¹) * (g * c * g⁻¹) := by group
  rw [hgT] at h1
  set x := g * c * g⁻¹ with hx
  have h3 : w * (x * T) = w * (T * x) := by
    rw [← mul_assoc, hwc x, mul_assoc, h1, mul_assoc]
  exact mul_left_cancel h3

theorem centralizer_normal_map (hZ : Z ≤ center S) (T : S) :
    (((centralizer ({T} : Set S)).map (QuotientGroup.mk' Z)).subgroupOf
      (centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)))).Normal := by
  constructor
  intro x hx y
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨c, hc, hcx⟩ := mem_map.mp hx
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective Z (y : S ⧸ Z)
  have hgC : QuotientGroup.mk' Z g ∈ centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)) := by
    rw [hg]
    exact y.2
  refine mem_map.mpr ⟨g * c * g⁻¹, conj_mem_centralizer hZ hgC hc, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hcx, hg]

theorem map_le_centralizer_mk {T : S} {F : Subgroup S} (hFT : F ≤ centralizer ({T} : Set S)) :
    F.map (QuotientGroup.mk' Z) ≤ centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)) := by
  rintro _ ⟨f, hf, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    mem_centralizer_singleton_iff.mp (hFT hf)]

theorem isTwoComponentAt_map_mk [Finite S] (hZ : Z ≤ center S) {T : S}
    (hT : orderOf (QuotientGroup.mk' Z T) = 2) {F : Subgroup S}
    (hFT : F ≤ centralizer ({T} : Set S))
    (hFn : ∀ c ∈ centralizer ({T} : Set S), ∀ f ∈ F, c * f * c⁻¹ ∈ F)
    (hq : IsQuasisimple (F.map (QuotientGroup.mk' Z)))
    (he : Even (Nat.card (F.map (QuotientGroup.mk' Z)))) :
    IsTwoComponentAt (QuotientGroup.mk' Z T) (F.map (QuotientGroup.mk' Z)) := by
  set C := centralizer ({QuotientGroup.mk' Z T} : Set (S ⧸ Z)) with hC
  set B := (centralizer ({T} : Set S)).map (QuotientGroup.mk' Z) with hB
  have hBC : B ≤ C := map_le_centralizer_mk le_rfl
  have hFB : F.map (QuotientGroup.mk' Z) ≤ B := map_mono hFT
  refine ⟨hT, map_le_centralizer_mk hFT,
    CatFactsSp4.isPComponent_two_of_quasisimple' (map_le_centralizer_mk hFT) hq ?_ he⟩
  have hBn : (B.subgroupOf C).Normal := centralizer_normal_map hZ T
  have hFB' : (F.map (QuotientGroup.mk' Z)).subgroupOf C ≤ B.subgroupOf C := fun x hx => by
    rw [mem_subgroupOf] at hx ⊢
    exact hFB hx
  refine Subgroup.IsSubnormal.step _ (B.subgroupOf C) hFB' hBn.isSubnormal ?_
  rw [Subgroup.normal_subgroupOf_iff hFB']
  intro h k hh hk
  rw [mem_subgroupOf] at hh hk ⊢
  obtain ⟨f, hf, hfh⟩ := mem_map.mp hh
  obtain ⟨c, hc, hck⟩ := mem_map.mp hk
  refine mem_map.mpr ⟨c * f * c⁻¹, hFn c hc f hf, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hfh, hck]

omit [Z.Normal] in
theorem commute_of_commutator_mem (hZ : Z ≤ center S) {F : Subgroup S} (hF : ⁅F, F⁆ = F) {g : S}
    (hg : ∀ x ∈ F, g * x * g⁻¹ * x⁻¹ ∈ Z) : ∀ x ∈ F, g * x = x * g := by
  have hcen : ∀ x ∈ F, ∀ y : S, (g * x * g⁻¹ * x⁻¹) * y = y * (g * x * g⁻¹ * x⁻¹) :=
    fun x hx y => (mem_center_iff.mp (hZ (hg x hx)) y).symm
  let φ : F →* S :=
    { toFun := fun x => g * x * g⁻¹ * (x : S)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Subgroup.coe_mul]
        calc g * (x * y : S) * g⁻¹ * (x * y : S)⁻¹ =
            (g * x * g⁻¹) * (g * y * g⁻¹ * (y : S)⁻¹) * (x : S)⁻¹ := by group
          _ = (g * x * g⁻¹) * (x : S)⁻¹ * (g * y * g⁻¹ * (y : S)⁻¹) := by
            rw [mul_assoc (g * x * g⁻¹), hcen y y.2 (x : S)⁻¹, ← mul_assoc] }
  have hφ : ∀ x : F, φ x = g * x * g⁻¹ * (x : S)⁻¹ := fun _ => rfl
  have hcomm : ⁅F, F⁆ ≤ φ.ker.map F.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : F), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm, hφ, hφ]
    exact hcen a ha _
  intro x hx
  rw [← hF] at hx
  obtain ⟨y, hy, rfl⟩ := hcomm hx
  have h1 : g * y * g⁻¹ * (y : S)⁻¹ = 1 := by rw [← hφ]; exact hy
  calc g * (y : S) = (g * y * g⁻¹ * (y : S)⁻¹) * y * g := by group
    _ = y * g := by rw [h1, one_mul]

end CFSG.ComponentClassification.CatLeafProof.EndOddCore
