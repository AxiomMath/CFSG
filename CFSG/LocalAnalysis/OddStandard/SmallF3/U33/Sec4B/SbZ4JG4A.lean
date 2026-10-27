module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem z4j_sylow_of_fusion {P D : Subgroup G} {s : G} (hP : IsPGroup 2 P) (hsP : s ∈ P)
    (hs2 : s * s = 1) (hsD : s ∉ D)
    (hD : ∀ z ∈ normalizer (P : Set G), ∀ x ∈ P, x ∉ D → z * x * z⁻¹ ∉ D)
    (hfus : ∀ x ∈ P, x * x = 1 → x ∉ D → (∃ g : G, x = g * s * g⁻¹) →
      ∃ w ∈ P, x = w * s * w⁻¹)
    (hcard : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer ({s} : Set G) →
      Nat.card R ≤ Nat.card ↥(P ⊓ centralizer ({s} : Set G))) :
    ¬ 2 ∣ P.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sy, hPSy⟩ := hP.exists_le_sylow
  have hle : (Sy : Subgroup G) ≤ P := by
    by_contra hnotle
    have hlt : P.subgroupOf (Sy : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hnotle
      intro x hx
      have : (⟨x, hx⟩ : Sy) ∈ P.subgroupOf (Sy : Subgroup G) := by
        rw [htop]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have hnil : Group.IsNilpotent Sy := Sy.isPGroup'.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := Sy)
    obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
    have hyN' : (y : G) ∈ normalizer (P : Set G) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro w
      constructor
      · intro hw
        have h1 : (⟨w, hPSy hw⟩ : Sy) ∈ P.subgroupOf Sy := Subgroup.mem_subgroupOf.mpr hw
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mp h1)
      · intro hw
        have hwSy : w ∈ (Sy : Subgroup G) := by
          have h1 : (y : G) * w * (y : G)⁻¹ ∈ (Sy : Subgroup G) := hPSy hw
          have h2 := mul_mem (mul_mem (inv_mem y.2) h1) y.2
          rwa [show (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * (y : G) = w by group] at h2
        have h1 : y * (⟨w, hwSy⟩ : Sy) * y⁻¹ ∈ P.subgroupOf Sy :=
          Subgroup.mem_subgroupOf.mpr (by simpa using hw)
        exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hyN _).mpr h1)
    have hyP' : (y : G) ∉ P := fun h => hyP (Subgroup.mem_subgroupOf.mpr h)
    have hs'P : (y : G) * s * (y : G)⁻¹ ∈ P :=
      (Subgroup.mem_set_normalizer_iff.mp hyN' s).mp hsP
    have hs'2 : ((y : G) * s * (y : G)⁻¹) * ((y : G) * s * (y : G)⁻¹) = 1 := by
      have h : (y : G) * s * (y : G)⁻¹ * ((y : G) * s * (y : G)⁻¹)
          = (y : G) * (s * s) * (y : G)⁻¹ := by group
      rw [h, hs2]; group
    have hs'D : (y : G) * s * (y : G)⁻¹ ∉ D := hD (y : G) hyN' s hsP hsD
    obtain ⟨w, hwP, hw_eq⟩ := hfus ((y : G) * s * (y : G)⁻¹) hs'P hs'2 hs'D ⟨(y : G), rfl⟩
    set n : G := w⁻¹ * (y : G) with hn
    have hn_s : n * s * n⁻¹ = s := by
      rw [hn]
      have h1 : w⁻¹ * (y : G) * s * (w⁻¹ * (y : G))⁻¹
          = w⁻¹ * ((y : G) * s * (y : G)⁻¹) * w := by group
      rw [h1, hw_eq]; group
    have hnC : n ∈ centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * s = (n * s * n⁻¹) * n := by group
        _ = s * n := by rw [hn_s]
    have hnSy : n ∈ (Sy : Subgroup G) := by
      rw [hn]
      exact mul_mem (inv_mem (hPSy hwP)) y.2
    set R : Subgroup G := (Sy : Subgroup G) ⊓ centralizer ({s} : Set G) with hR
    have hRp : IsPGroup 2 R := (Sy.isPGroup').to_le inf_le_left
    have hRC : R ≤ centralizer ({s} : Set G) := inf_le_right
    have hleR : P ⊓ centralizer ({s} : Set G) ≤ R :=
      le_inf (inf_le_left.trans hPSy) inf_le_right
    have hcardR : Nat.card R ≤ Nat.card ↥(P ⊓ centralizer ({s} : Set G)) := hcard R hRp hRC
    have hcardP : Nat.card ↥(P ⊓ centralizer ({s} : Set G)) ≤ Nat.card R :=
      Subgroup.card_le_of_le hleR
    have heqR : P ⊓ centralizer ({s} : Set G) = R :=
      Subgroup.eq_of_le_of_card_ge hleR hcardR
    have hnR : n ∈ R := by
      change n ∈ (Sy : Subgroup G) ⊓ centralizer ({s} : Set G)
      exact Subgroup.mem_inf.mpr ⟨hnSy, hnC⟩
    have hnPC : n ∈ P ⊓ centralizer ({s} : Set G) := by rw [heqR]; exact hnR
    have hnP : n ∈ P := (Subgroup.mem_inf.mp hnPC).1
    have hyP_final : (y : G) ∈ P := by
      have : (y : G) = w * n := by rw [hn]; group
      rw [this]; exact mul_mem hwP hnP
    exact hyP' hyP_final
  have heq : (Sy : Subgroup G) = P := le_antisymm hle hPSy
  rw [← heq]
  exact Sy.not_dvd_index

theorem z4j_char_of_unique {Vg V : Subgroup G} (hVV : V ≤ Vg) (hVd : V ≤ ⁅Vg, Vg⁆)
    (hVn : ∀ g ∈ Vg, ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hV4 : Nat.card V = 4)
    (hVe : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a ∧ a * a = 1)
    (huniq : ∀ W : Subgroup G, W ≤ Vg → (∀ g ∈ Vg, ∀ w ∈ W, g * w * g⁻¹ ∈ W) →
      W ≤ ⁅Vg, Vg⁆ → Nat.card W = 4 → (∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1) → W = V) :
    ∀ z ∈ normalizer (Vg : Set G), ∀ v ∈ V, z * v * z⁻¹ ∈ V := by
  intro z hz v hv
  set W : Subgroup G := V.map (MulAut.conj z).toMonoidHom with hW
  have hWVg : W ≤ Vg := by
    intro w hw
    rw [hW, Subgroup.mem_map] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    change (MulAut.conj z) a ∈ Vg
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_set_normalizer_iff.mp hz a).mp (hVV ha)
  have hWn : ∀ g ∈ Vg, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    rw [hW, Subgroup.mem_map] at hw ⊢
    obtain ⟨a, ha, rfl⟩ := hw
    refine ⟨(z⁻¹ * g * z) * a * (z⁻¹ * g * z)⁻¹, hVn (z⁻¹ * g * z) ?_ a ha, ?_⟩
    · have hzg : z⁻¹ * g * (z⁻¹)⁻¹ ∈ Vg :=
        (Subgroup.mem_set_normalizer_iff.mp (inv_mem hz) g).mp hg
      simpa only [inv_inv] using hzg
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hWmap : Vg.map (MulAut.conj z).toMonoidHom = Vg :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hz
  have hW_le : W ≤ ⁅Vg, Vg⁆ := by
    rw [hW]
    calc V.map (MulAut.conj z).toMonoidHom
        ≤ ⁅Vg, Vg⁆.map (MulAut.conj z).toMonoidHom := Subgroup.map_mono hVd
      _ = ⁅Vg.map (MulAut.conj z).toMonoidHom, Vg.map (MulAut.conj z).toMonoidHom⁆ :=
            Subgroup.map_commutator (H₁ := Vg) (H₂ := Vg) _
      _ = ⁅Vg, Vg⁆ := by rw [hWmap]
  have hWcard : Nat.card W = 4 := by
    rw [hW, Subgroup.card_map_of_injective (f := (MulAut.conj z).toMonoidHom)
      (fun a b h => (MulAut.conj z).injective h)]
    exact hV4
  have hWe : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a ∧ a * a = 1 := by
    intro a ha b hb
    rw [hW, Subgroup.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨hab, haa⟩ := hVe a' ha' b' hb'
    constructor
    · rw [← map_mul, ← map_mul, hab]
    · rw [← map_mul, haa, map_one]
  have hWV : W = V := huniq W hWVg hWn hW_le hWcard hWe
  have hvW : (MulAut.conj z).toMonoidHom v ∈ W := Subgroup.mem_map.mpr ⟨v, hv, rfl⟩
  rw [hWV] at hvW
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hvW

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
