module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem conj_mem_map_of_characteristic_aux {G : Type*} [Group G] {X : Subgroup G}
    {D : Subgroup X} [hD : D.Characteristic] {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ D.map X.subtype) :
    g * x * g⁻¹ ∈ D.map X.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  let φ := Subgroup.normalizerMonoidHom X ⟨g, hg⟩
  have hfix : D.map φ.toMonoidHom = D := (Subgroup.characteristic_iff_map_eq.mp hD) φ
  refine ⟨φ y, ?_, ?_⟩
  · rw [← hfix]
    exact Subgroup.mem_map_of_mem _ hy
  · rw [Subgroup.coe_subtype, Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem map_pCore_le_pCore_of_isSubnormal_aux {H : Type*} [Group H] (p : ℕ)
    {K : Subgroup H} (hK : K.IsSubnormal) : (pCore p K).map K.subtype ≤ pCore p H := by
  have key : ∀ {X Y : Subgroup H}, X ≤ Y → Y ≤ normalizer (X : Set H) →
      (pCore p X).map X.subtype ≤ (pCore p Y).map Y.subtype := by
    intro X Y hXY hYN
    have hLY : (pCore p X).map X.subtype ≤ Y := (Subgroup.map_subtype_le _).trans hXY
    have hle : ((pCore p X).map X.subtype).subgroupOf Y ≤ pCore p Y := by
      apply le_sSup
      refine ⟨⟨fun l hl y => ?_⟩, ?_⟩
      · rw [Subgroup.mem_subgroupOf] at hl ⊢
        simpa using conj_mem_map_of_characteristic_aux (hYN y.2) hl
      · exact ((pCore_isPGroup (p := p) (G := X)).map X.subtype).of_equiv
          (Subgroup.subgroupOfEquivOfLe hLY).symm
    calc (pCore p X).map X.subtype
        = (((pCore p X).map X.subtype).subgroupOf Y).map Y.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hLY).symm
      _ ≤ (pCore p Y).map Y.subtype := Subgroup.map_mono hle
  induction hK with
  | top =>
    apply le_sSup
    refine ⟨⟨fun l hl g => conj_mem_map_of_characteristic_aux ?_ hl⟩,
      (pCore_isPGroup (p := p) (G := (⊤ : Subgroup H))).map _⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  | step X Y hXY hY hN ih =>
    exact (key hXY ((Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hN)).trans ih

private theorem le_pCore_of_normal_aux {X : Type*} [Group X] (p : ℕ) (S : Subgroup X) [S.Normal]
    (hS : IsPGroup p ↥S) : S ≤ pCore p X :=
  le_sSup ⟨inferInstance, hS⟩

private lemma map_subgroupOf_subgroupMap {M B : Type} [Group M] [Group B] (f : M →* B)
    {K L : Subgroup M} (hKL : K ≤ L) :
    (K.subgroupOf L).map (f.subgroupMap L) = (K.map f).subgroupOf (L.map f) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp hx
    rw [← hkx]
    exact Subgroup.mem_map.mpr ⟨(k : M), hk, rfl⟩
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨m, hKL hm⟩, hm, ?_⟩
    exact Subtype.ext hmx

theorem l34g_subnormal_map {M B : Type} [Group M] [Group B] (f : M →* B) {K L : Subgroup M}
    (hKL : K ≤ L) (h : (K.subgroupOf L).IsSubnormal) :
    ((K.map f).subgroupOf (L.map f)).IsSubnormal := by
  have hmap := Subgroup.IsSubnormal.map (MonoidHom.subgroupMap_surjective f L) h
  rwa [map_subgroupOf_subgroupMap f hKL] at hmap

theorem l34g_exists_normal_pGroup {A : Type} [Group A] [Finite A] {P B : Subgroup A}
    (hPB : P ≤ B) (hP : IsPGroup 3 ↥P) (hsub : (P.subgroupOf B).IsSubnormal) :
    ∃ R : Subgroup A, P ≤ R ∧ R ≤ B ∧ IsPGroup 3 ↥R ∧ ∀ b ∈ B, ∀ r ∈ R, b * r * b⁻¹ ∈ R := by
  have hKpg : IsPGroup 3 ↥(P.subgroupOf B) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPB).symm
  refine ⟨(pCore 3 ↥B).map B.subtype, ?_, Subgroup.map_subtype_le (pCore 3 ↥B), ?_, ?_⟩
  · intro a ha
    refine Subgroup.mem_map.mpr ⟨⟨a, hPB ha⟩, ?_, rfl⟩
    have hle := map_pCore_le_pCore_of_isSubnormal_aux (H := ↥B) 3 hsub
    apply hle
    refine Subgroup.mem_map.mpr ⟨⟨⟨a, hPB ha⟩, ha⟩, ?_, rfl⟩
    have htop : (⊤ : Subgroup ↥(P.subgroupOf B)) ≤ pCore 3 ↥(P.subgroupOf B) :=
      le_pCore_of_normal_aux 3 ⊤ (hKpg.to_subgroup ⊤)
    exact htop (Subgroup.mem_top _)
  · exact (pCore_isPGroup (p := 3) (G := ↥B)).map B.subtype
  · intro b hb r hr
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨⟨b, hb⟩ * x * ⟨b, hb⟩⁻¹, ?_, rfl⟩
    exact (pCore_normal (p := 3) (G := ↥B)).conj_mem x hx ⟨b, hb⟩

theorem l34g_exists_O3 {A : Type} [Group A] [Finite A] {C0 F : Subgroup A} (hC0F : C0 ≤ F)
    (hn : ∀ f ∈ F, ∀ c ∈ C0, f * c * f⁻¹ ∈ C0) :
    ∃ R : Subgroup A, R ≤ C0 ∧ IsPGroup 3 ↥R ∧ (∀ f ∈ F, ∀ r ∈ R, f * r * f⁻¹ ∈ R) ∧
      ∀ N : Subgroup A, N ≤ C0 → IsPGroup 3 ↥N → (∀ c ∈ C0, ∀ n ∈ N, c * n * c⁻¹ ∈ N) → N ≤ R := by
  refine ⟨(pCore 3 ↥C0).map C0.subtype, Subgroup.map_subtype_le (pCore 3 ↥C0),
    (pCore_isPGroup (p := 3) (G := ↥C0)).map C0.subtype, ?_, ?_⟩
  · intro f hf r hr
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hr
    have hf' : f⁻¹ ∈ F := F.inv_mem hf
    let φ : ↥C0 ≃* ↥C0 :=
      { toFun := fun c => ⟨f * (c : A) * f⁻¹, hn f hf c c.2⟩
        invFun := fun c => ⟨f⁻¹ * (c : A) * f, by simpa using hn f⁻¹ hf' c c.2⟩
        left_inv := fun c => Subtype.ext (by
          change f⁻¹ * (f * (c : A) * f⁻¹) * f = (c : A)
          group)
        right_inv := fun c => Subtype.ext (by
          change f * (f⁻¹ * (c : A) * f) * f⁻¹ = (c : A)
          group)
        map_mul' := fun a b => Subtype.ext (by
          change f * ((a : A) * (b : A)) * f⁻¹ =
            (f * (a : A) * f⁻¹) * (f * (b : A) * f⁻¹)
          group) }
    have hfix := (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (pCore 3 ↥C0).Characteristic)) φ
    have hmem : φ x ∈ pCore 3 ↥C0 := by
      rw [← hfix]
      exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    exact Subgroup.mem_map.mpr ⟨φ x, hmem, rfl⟩
  · intro N hNle hNpg hNnorm
    have hnormal : (N.subgroupOf C0).Normal :=
      ⟨fun n hn c => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hNnorm c c.2 n hn⟩
    have hNpg' : IsPGroup 3 ↥(N.subgroupOf C0) :=
      hNpg.of_equiv (Subgroup.subgroupOfEquivOfLe hNle).symm
    have hle : N.subgroupOf C0 ≤ pCore 3 ↥C0 :=
      le_pCore_of_normal_aux 3 (N.subgroupOf C0) hNpg'
    intro n hn
    exact Subgroup.map_mono hle (by
      rw [Subgroup.map_subgroupOf_eq_of_le hNle]
      exact hn)

end CFSG.OddStandard.SmallF3.Omega
