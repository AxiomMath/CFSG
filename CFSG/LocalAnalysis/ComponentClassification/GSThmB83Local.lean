module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Action
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Setup
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8Statements
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCentral
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

@[expose] def fixSubgroup {Y : Type*} [Group Y] (e : MulAut Y) : Subgroup Y where
  carrier := {y | e y = y}
  mul_mem' {x y} hx hy := by
    change e x = x at hx
    change e y = y at hy
    change e (x * y) = x * y
    rw [map_mul, hx, hy]
  one_mem' := by
    change e 1 = 1
    rw [map_one]
  inv_mem' {x} hx := by
    change e x = x at hx
    change e x⁻¹ = x⁻¹
    rw [map_inv, hx]

theorem mem_fixSubgroup {Y : Type*} [Group Y] {e : MulAut Y} {y : Y} :
    y ∈ fixSubgroup e ↔ e y = y := Iff.rfl

variable {G : Type*} [Group G]

theorem sup_zpowers_le_normalizer {K : Subgroup G} {a : G} (ha : a ∈ normalizer (K : Set G)) :
    K ⊔ zpowers a ≤ normalizer (K : Set G) :=
  sup_le le_normalizer (zpowers_le.mpr ha)

@[expose] noncomputable def modelHom (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G)) :
    ↥(K ⊔ zpowers a) →* MulAut (K ⧸ pPrimeCore 2 K) :=
  (oddBarAction K).comp (inclusion (sup_zpowers_le_normalizer ha))

theorem modelHom_apply_mk (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G))
    (m : ↥(K ⊔ zpowers a)) (l : K) :
    modelHom K ha m (l : K ⧸ pPrimeCore 2 K) =
      ((⟨(m : G) * l * (m : G)⁻¹,
        (mem_normalizer_iff.mp (sup_zpowers_le_normalizer ha m.2) l).mp l.2⟩ : K) :
        K ⧸ pPrimeCore 2 K) := rfl

theorem modelHom_of_mem_K (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G)) (l : K) :
    modelHom K ha ⟨l, mem_sup_left l.2⟩ = MulAut.conj ((l : K) : K ⧸ pPrimeCore 2 K) := by
  ext y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [modelHom_apply_mk, MulAut.conj_apply]
  rfl

theorem mem_sup_zpowers_cases {K : Subgroup G} {a : G} (ha : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) {m : G} (hm : m ∈ K ⊔ zpowers a) : ∃ k ∈ K, m = k ∨ m = k * a := by
  have hKa : ∀ k ∈ K, a * k * a⁻¹ ∈ K := fun k hk => (mem_normalizer_iff.mp ha k).mp hk
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  let N : Subgroup G :=
    { carrier := {y | ∃ k ∈ K, y = k ∨ y = k * a}
      mul_mem' := by
        rintro y z ⟨k, hk, hy⟩ ⟨l, hl, hz⟩
        rcases hy with hy | hy <;> rcases hz with hz | hz <;> rw [hy, hz]
        · exact ⟨k * l, mul_mem hk hl, Or.inl rfl⟩
        · exact ⟨k * l, mul_mem hk hl, Or.inr (by group)⟩
        · refine ⟨k * (a * l * a⁻¹), mul_mem hk (hKa l hl), Or.inr ?_⟩
          group
        · refine ⟨k * (a * l * a⁻¹), mul_mem hk (hKa l hl), Or.inl ?_⟩
          calc k * a * (l * a) = k * (a * l * a⁻¹) * (a * a) := by group
            _ = k * (a * l * a⁻¹) := by rw [haa, mul_one]
      one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
      inv_mem' := by
        rintro y ⟨k, hk, hy⟩
        rcases hy with hy | hy <;> rw [hy]
        · exact ⟨k⁻¹, inv_mem hk, Or.inl rfl⟩
        · refine ⟨a * k⁻¹ * a⁻¹, hKa _ (inv_mem hk), Or.inr ?_⟩
          calc (k * a)⁻¹ = a⁻¹ * k⁻¹ := mul_inv_rev _ _
            _ = a * k⁻¹ := by rw [ha']
            _ = a * k⁻¹ * a⁻¹ * a := by group }
  have hle : K ⊔ zpowers a ≤ N := by
    refine sup_le (fun k hk => ⟨k, hk, Or.inl rfl⟩) ?_
    rw [zpowers_le]
    exact ⟨1, one_mem _, Or.inr (one_mul _).symm⟩
  exact hle hm

theorem range_modelHom (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) :
    (modelHom K ha).range =
      (MulAut.conj : (K ⧸ pPrimeCore 2 K) →* MulAut (K ⧸ pPrimeCore 2 K)).range ⊔
        zpowers (modelHom K ha ⟨a, mem_sup_right (mem_zpowers a)⟩) := by
  have haM : a ∈ K ⊔ zpowers a := mem_sup_right (mem_zpowers a)
  apply le_antisymm
  · rintro _ ⟨⟨m, hm⟩, rfl⟩
    obtain ⟨k, hk, hmk⟩ := mem_sup_zpowers_cases ha haa hm
    rcases hmk with hmk | hmk
    · rw [show (⟨m, hm⟩ : ↥(K ⊔ zpowers a)) = ⟨(⟨k, hk⟩ : K), mem_sup_left hk⟩ from
        Subtype.ext hmk, modelHom_of_mem_K]
      exact mem_sup_left ⟨_, rfl⟩
    · rw [show (⟨m, hm⟩ : ↥(K ⊔ zpowers a)) =
          ⟨(⟨k, hk⟩ : K), mem_sup_left hk⟩ * ⟨a, haM⟩ from Subtype.ext hmk, map_mul,
        modelHom_of_mem_K]
      exact mul_mem (mem_sup_left ⟨_, rfl⟩) (mem_sup_right (mem_zpowers _))
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨⟨l, mem_sup_left l.2⟩, modelHom_of_mem_K K ha l⟩
    · rw [zpowers_le]
      exact ⟨_, rfl⟩

theorem ker_modelHom (K : Subgroup G) {a : G} (ha : a ∈ normalizer (K : Set G))
    (haa : a * a = 1) (hZ : center (K ⧸ pPrimeCore 2 K) = ⊥)
    (hout : modelHom K ha ⟨a, mem_sup_right (mem_zpowers a)⟩ ∉
      (MulAut.conj : (K ⧸ pPrimeCore 2 K) →* MulAut (K ⧸ pPrimeCore 2 K)).range) :
    (modelHom K ha).ker = (oddCoreIn K).subgroupOf (K ⊔ zpowers a) := by
  have haM : a ∈ K ⊔ zpowers a := mem_sup_right (mem_zpowers a)
  ext ⟨m, hm⟩
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h1
    obtain ⟨k, hk, hmk⟩ := mem_sup_zpowers_cases ha haa hm
    rcases hmk with hmk | hmk
    · rw [show (⟨m, hm⟩ : ↥(K ⊔ zpowers a)) = ⟨(⟨k, hk⟩ : K), mem_sup_left hk⟩ from
        Subtype.ext hmk, modelHom_of_mem_K] at h1
      have hc : (((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K)) ∈ center (K ⧸ pPrimeCore 2 K) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h2 := congrArg (fun φ : MulAut (K ⧸ pPrimeCore 2 K) => φ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        calc y * (((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K)) =
            (((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K)) * y *
              (((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K))⁻¹ *
              (((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K)) := by rw [h2]
          _ = _ := by group
      rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
      change m ∈ (pPrimeCore 2 K).map K.subtype
      rw [hmk]
      exact ⟨⟨k, hk⟩, hc, rfl⟩
    · exfalso
      rw [show (⟨m, hm⟩ : ↥(K ⊔ zpowers a)) =
          ⟨(⟨k, hk⟩ : K), mem_sup_left hk⟩ * ⟨a, haM⟩ from Subtype.ext hmk, map_mul,
        modelHom_of_mem_K] at h1
      apply hout
      refine ⟨(((⟨k, hk⟩ : K) : K ⧸ pPrimeCore 2 K))⁻¹, ?_⟩
      rw [map_inv]
      exact (eq_inv_of_mul_eq_one_right h1).symm
  · intro h1
    obtain ⟨⟨k, hk⟩, hkO, hkm⟩ := mem_map.mp h1
    change (k : G) = m at hkm
    have hkK : (k : G) ∈ K := hk
    rw [show (⟨m, hm⟩ : ↥(K ⊔ zpowers a)) = ⟨(⟨k, hk⟩ : K), mem_sup_left hk⟩ from
      Subtype.ext hkm.symm, modelHom_of_mem_K]
    rw [(QuotientGroup.eq_one_iff (N := pPrimeCore 2 K) ⟨k, hk⟩).mpr hkO, map_one]

theorem not_two_dvd_card_ker_modelHom [Finite G] (K : Subgroup G) {a : G}
    (ha : a ∈ normalizer (K : Set G)) (haa : a * a = 1)
    (hZ : center (K ⧸ pPrimeCore 2 K) = ⊥)
    (hout : modelHom K ha ⟨a, mem_sup_right (mem_zpowers a)⟩ ∉
      (MulAut.conj : (K ⧸ pPrimeCore 2 K) →* MulAut (K ⧸ pPrimeCore 2 K)).range) :
    ¬ 2 ∣ Nat.card (modelHom K ha).ker := by
  rw [ker_modelHom K ha haa hZ hout]
  have hle : oddCoreIn K ≤ K ⊔ zpowers a := (map_subtype_le _).trans le_sup_left
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, oddCoreIn,
    card_map_of_injective K.subtype_injective]
  intro h2
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (pPrimeCore_coprime_card (p := 2) (G := K)) h2

end Eight

end CFSG.ComponentClassification.GSThmB
