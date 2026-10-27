module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Core

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Generic

theorem card_sup_of_commute {Y : Type*} [Group Y] [Finite Y] {A B : Subgroup Y}
    (hAB : A ≤ Subgroup.centralizer (B : Set Y)) (hdisj : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup Y) = Nat.card A * Nat.card B := by
  have comm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (hAB a.2) b b.2).symm
  have hinj : Function.Injective (MonoidHom.noncommCoprod A.subtype B.subtype comm) :=
    (MonoidHom.noncommCoprod_injective _ _ comm).mpr ⟨A.subtype_injective, B.subtype_injective,
      by rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]; exact hdisj⟩
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype comm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

theorem eq_bot_of_le_layer_of_centralizes {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pCore 3 Y = ⊥) {B : Subgroup Y} (hB3 : IsPGroup 3 B)
    (hBL : B ≤ CFSG.ComponentClassification.Layer.subgroup Y)
    (hBC : ∀ C : Subgroup Y, IsComponentOf C ⊤ → B ≤ Subgroup.centralizer (C : Set Y)) :
    B = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ly := CFSG.ComponentClassification.Layer.subgroup Y with hLy
  have : Ly.Normal := CFSG.ComponentClassification.Layer.normal Y
  have hBCL : B ≤ Subgroup.centralizer (Ly : Set Y) := by
    rw [Subgroup.le_centralizer_iff]
    exact sSup_le fun C hC => Subgroup.le_centralizer_iff.mp (hBC C hC)
  have hnd := not_dvd_card_center_of_normal (p := 3) (Lb := Ly) hO
  by_contra hne
  apply hnd
  set Zb := (Subgroup.center Ly).map Ly.subtype with hZb
  have hBZ : B ≤ Zb := by
    intro b hb
    refine ⟨⟨b, hBL hb⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hBCL hb) g g.2)
  have hc : Nat.card Zb = Nat.card (Subgroup.center Ly) :=
    Subgroup.card_map_of_injective Ly.subtype_injective
  obtain ⟨n, hn⟩ := hB3.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hne hn
  rw [← hc]
  exact (dvd_pow_self 3 hn0).trans (hn ▸ Subgroup.card_dvd_of_le hBZ)

theorem eq_one_of_mem_center_component {Y : Type*} [Group Y] [Finite Y]
    (hO : CFSG.pCore 3 Y = ⊥) {C : Subgroup Y} (hC : IsComponentOf C ⊤) {c : Y} (hcC : c ∈ C)
    (hcZ : c ∈ Subgroup.centralizer (C : Set Y)) (hc3 : IsPGroup 3 (Subgroup.zpowers c)) :
    c = 1 := by
  have hbot := eq_bot_of_le_layer_of_centralizes hO hc3
    (Subgroup.zpowers_le.mpr (CFSG.ComponentClassification.Layer.component_le hC hcC))
    (fun C' hC' => by
      rw [Subgroup.zpowers_le]
      by_cases hCC : C' = C
      · rw [hCC]
        exact hcZ
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hC hC' (Ne.symm hCC))
          hcC)
  rw [Subgroup.zpowers_eq_bot] at hbot
  exact hbot

end Generic

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Inner2

theorem relIndex_dvd_of_inner {Y : Type*} [Group Y] [Finite Y] {Lb I J : Subgroup Y}
    (hI : I ≤ Subgroup.normalizer (Lb : Set Y)) (hJ : J ≤ Subgroup.normalizer (Lb : Set Y))
    (hIJ : ∀ x ∈ I, ∃ l ∈ J, x * l⁻¹ ∈ Subgroup.centralizer (Lb : Set Y)) :
    (Subgroup.centralizer (Lb : Set Y)).relIndex I ∣ Nat.card J := by
  set Nn := Subgroup.normalizer (Lb : Set Y) with hNn
  set ρ : Nn →* MulAut Lb := Lb.normalizerMonoidHom with hρ
  have hker : ∀ g : Nn, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro g
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun f : MulAut Lb => ((f ⟨w, hw⟩ : Lb) : Y)) h1
      simp only [hρ, MulAut.one_apply] at h2
      change (g : Y) * w * (g : Y)⁻¹ = w at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro hg
      ext ⟨w, hw⟩
      change (g : Y) * w * (g : Y)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hg w hw).symm
  set f : I →* MulAut Lb := ρ.comp (Subgroup.inclusion hI) with hf
  have hfker : f.ker = (Subgroup.centralizer (Lb : Set Y)).subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker (Subgroup.inclusion hI x)
  have hrange : f.range ≤ (J.subgroupOf Nn).map ρ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl, hxl⟩ := hIJ x x.2
    refine ⟨⟨l, hJ hl⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    have h1 : ρ (Subgroup.inclusion hI x * (⟨l, hJ hl⟩ : Nn)⁻¹) = 1 := (hker _).mpr hxl
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  rw [Subgroup.relIndex, ← hfker, Subgroup.index_ker]
  exact (Subgroup.card_dvd_of_le hrange).trans ((Subgroup.card_map_dvd _ _).trans
    (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv)))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_of_barM_le_of_isPGroup {M A Z W : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hAM : A ≤ M) (hA : IsPGroup p A) (hZA : Z ≤ A) (hWA : W ≤ A)
    (hle : barM M Z ≤ barM M W) : Z ≤ W := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hle (Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr hz : (⟨z, hAM (hZA hz)⟩ : M) ∈ Z.subgroupOf M))
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (w⁻¹ * ⟨z, hAM (hZA hz)⟩) = 1 := by
    rw [map_mul, map_inv, hwz, inv_mul_cancel]
  have hwA : (w : G) ∈ A := hWA (Subgroup.mem_subgroupOf.mp hw)
  have hx : ((w⁻¹ * ⟨z, hAM (hZA hz)⟩ : M) : G) ∈ A := by
    simpa using A.mul_mem (A.inv_mem hwA) (hZA hz)
  have h2 := eq_one_of_mem_pCoreOf_two hp hp2 hA hx (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have h3 : (w : G)⁻¹ * z = 1 := by simpa using h2
  rw [inv_mul_eq_one] at h3
  rw [← h3]
  exact Subgroup.mem_subgroupOf.mp hw

omit [Finite G] in
theorem orderOf_mk_of_isPGroup {M A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hAM : A ≤ M) (hA : IsPGroup p A) {a : G} (ha : a ∈ A) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨a, hAM ha⟩) = orderOf a := by
  set f : A →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hAM) with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hAM x) = 1 := hx
    have h2 := eq_one_of_mem_pCoreOf_two hp hp2 hA x.2
      (coe_mem_pCoreOf_two_of_mk_eq_one (Subgroup.inclusion hAM x) h1)
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  have := orderOf_injective f hfinj ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at this
  exact this

end Inner2

end CFSG.AGLEmbedding
