module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Ind

section Bar
variable {X : Type} [Group X] {W K : Subgroup X} [W.Normal]

theorem toBar_coe (k : ↥K) : ((toBar W K k : ↥(bar W K)) : X ⧸ W) = QuotientGroup.mk (k : X) := rfl

theorem toBar_surj : Function.Surjective (toBar W K) := by
  rintro ⟨y, k, hk, rfl⟩
  exact ⟨⟨k, hk⟩, rfl⟩

theorem toBar_eq_iff {k k' : ↥K} : toBar W K k = toBar W K k' ↔ (k : X)⁻¹ * k' ∈ W := by
  rw [← Subtype.coe_inj, toBar_coe, toBar_coe, QuotientGroup.eq]

theorem comm_mem_iff (b k : X) :
    ⁅b, k⁆ ∈ W ↔ (QuotientGroup.mk b : X ⧸ W) * QuotientGroup.mk k =
      QuotientGroup.mk k * QuotientGroup.mk b := by
  rw [← QuotientGroup.eq_one_iff, ← commutatorElement_eq_one_iff_mul_comm]
  exact Iff.rfl

theorem mk_mem_normalizer_bar {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    (QuotientGroup.mk b : X ⧸ W) ∈
      Subgroup.normalizer ((bar W K : Subgroup (X ⧸ W)) : Set (X ⧸ W)) :=
  Subgroup.le_normalizer_map (QuotientGroup.mk' W) ⟨b, hb, rfl⟩

@[expose] noncomputable def indHom (W K B : Subgroup X) [W.Normal]
    (hB : B ≤ Subgroup.normalizer (K : Set X)) : ↥B →* MulAut ↥(bar W K) :=
  (bar W K).normalizerMonoidHom.comp
    (((QuotientGroup.mk' W).comp B.subtype).codRestrict _
      (fun b => mk_mem_normalizer_bar (hB b.2)))

theorem indHom_apply (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) :
    indHom W K B hB b = (bar W K).normalizerMonoidHom
      ⟨QuotientGroup.mk (b : X), mk_mem_normalizer_bar (hB b.2)⟩ := rfl

theorem indHom_toBar (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) (k : ↥K) :
    ((indHom W K B hB b (toBar W K k) : ↥(bar W K)) : X ⧸ W) =
      QuotientGroup.mk ((b : X) * k * (b : X)⁻¹) := by
  rw [indHom_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp [toBar_coe]

theorem indHom_eq_one_iff (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) (b : ↥B) :
    indHom W K B hB b = 1 ↔ ∀ k ∈ K, ⁅(b : X), k⁆ ∈ W := by
  constructor
  · intro h k hk
    have h1 := congrArg
      (fun φ : MulAut ↥(bar W K) => ((φ (toBar W K ⟨k, hk⟩) : ↥(bar W K)) : X ⧸ W)) h
    simp only [indHom_toBar, MulAut.one_apply, toBar_coe] at h1
    rw [comm_mem_iff]
    have h2 : (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk k *
        (QuotientGroup.mk (b : X))⁻¹ = QuotientGroup.mk k := by
      simpa using h1
    calc (QuotientGroup.mk (b : X) : X ⧸ W) * QuotientGroup.mk k
        = (QuotientGroup.mk (b : X) * QuotientGroup.mk k * (QuotientGroup.mk (b : X))⁻¹) *
            QuotientGroup.mk (b : X) := by group
      _ = _ := by rw [h2]
  · intro h
    ext y
    obtain ⟨k, rfl⟩ := toBar_surj y
    rw [indHom_toBar, MulAut.one_apply, toBar_coe]
    have h1 := (comm_mem_iff _ _).mp (h k k.2)
    calc (QuotientGroup.mk ((b : X) * k * (b : X)⁻¹) : X ⧸ W)
        = QuotientGroup.mk (b : X) * QuotientGroup.mk (k : X) *
            (QuotientGroup.mk (b : X))⁻¹ := by simp
      _ = QuotientGroup.mk (k : X) := by rw [h1]; group

theorem range_indHom (B : Subgroup X) (hB : B ≤ Subgroup.normalizer (K : Set X)) :
    (indHom W K B hB).range = indAut W K B := by
  ext φ
  simp only [MonoidHom.mem_range, indAut, inducedAutGroup, Subgroup.mem_map,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨QuotientGroup.mk (b : X), mk_mem_normalizer_bar (hB b.2)⟩, ⟨b, b.2, rfl⟩, rfl⟩
  · rintro ⟨⟨y, hyN⟩, ⟨b, hbB, hby⟩, rfl⟩
    refine ⟨⟨b, hbB⟩, ?_⟩
    simp only [indHom, MonoidHom.comp_apply]
    congr 1
    exact Subtype.ext hby

end Bar

section CardInd
variable {X : Type} [Group X] {W K S : Subgroup X} [W.Normal]

theorem ker_indHom (h : Setup28 W K S) {B : Subgroup X} (hB : B ≤ S) :
    (indHom W K B (hB.trans h.hN)).ker = (kerAct W K S).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, indHom_eq_one_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun hb => ⟨hB b.2, hb⟩, fun hb => hb.2⟩

theorem card_indAut (h : Setup28 W K S) {B : Subgroup X} (hB : B ≤ S) :
    Nat.card ↥(indAut W K B) = (kerAct W K S).relIndex B := by
  rw [← range_indHom B (hB.trans h.hN), ← Subgroup.index_ker, ker_indHom h hB]
  rfl

theorem commutator_K (h : Setup28 W K S) : commutator ↥K = ⊤ := by
  have h1 : (commutator ↥K).map K.subtype = K := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact h.hK.2.1
  have h2 : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  exact Subgroup.map_injective K.subtype_injective (h1.trans h2.symm)

end CardInd

theorem aut_eq_one {G : Type*} [Group G] (hG : commutator G = ⊤) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) (α : MulAut G) (h : ∀ x : G, x⁻¹ * α x ∈ Z) : α = 1 := by
  have hc : ∀ x y : G, y * (x⁻¹ * α x) = (x⁻¹ * α x) * y := fun x y =>
    Subgroup.mem_center_iff.mp (hZ (h x)) y
  let f : G →* G :=
    { toFun := fun x => x⁻¹ * α x
      map_one' := by simp
      map_mul' := fun x y => by
        have := hc x y⁻¹
        simp only [mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [this]
          _ = _ := by group }
  have hker : commutator G ≤ f.ker := by
    show ⁅(⊤ : Subgroup G), ⊤⁆ ≤ f.ker
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc g₂ (f g₁)
  ext x
  have hx : x ∈ f.ker := hker (hG ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, inv_mul_eq_one] at hx
  simpa using hx.symm

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.A5Ind
