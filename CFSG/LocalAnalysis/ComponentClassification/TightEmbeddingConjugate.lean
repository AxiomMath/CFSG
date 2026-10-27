module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.StandardSubgroupAPI

open Subgroup ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G]

theorem tightlyEmbedded_rightConjugate {K : Subgroup G}
    (hK : TightlyEmbedded K) (g : G) :
    TightlyEmbedded (rightConjugate K g) := by
  refine ⟨by rw [rightConjugate_card]; exact hK.1, fun x hx => ?_⟩
  have hy : g * x * g⁻¹ ∉ normalizer (K : Set G) := by
    intro hy
    apply hx
    rw [← rightConjugate_eq_self_iff] at hy ⊢
    calc rightConjugate (rightConjugate K g) x
        = rightConjugate K (g * x) :=
          rightConjugate_mul _ _ _
      _ = rightConjugate K (g * x * g⁻¹ * g) := by
          rw [show g * x * g⁻¹ * g = g * x by group]
      _ = rightConjugate
            (rightConjugate K (g * x * g⁻¹)) g :=
          (rightConjugate_mul _ _ _).symm
      _ = rightConjugate K g := by rw [hy]
  have hiso : (rightConjugate K g ⊓
      rightConjugate (rightConjugate K g) x :
        Subgroup G) =
      rightConjugate
        (K ⊓ rightConjugate K (g * x * g⁻¹)) g := by
    ext y
    simp only [mem_inf, mem_rightConjugate_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa [mul_assoc] using h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by simpa [mul_assoc] using h2⟩
  rw [hiso, rightConjugate_card]
  exact hK.2 _ hy

theorem tightlyEmbedded_subgroupOf {K X : Subgroup G} (hKX : K ≤ X) (hK : TightlyEmbedded K) :
    TightlyEmbedded (K.subgroupOf X) := by
  have hcard : Nat.card (K.subgroupOf X) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKX).toEquiv
  refine ⟨hcard ▸ hK.1, fun x hx => ?_⟩
  have hx' : (x : G) ∉ normalizer (K : Set G) := by
    intro h
    apply hx
    rw [← subgroupOf_normalizer_eq hKX]
    exact h
  have heq : (K.subgroupOf X ⊓ rightConjugate (K.subgroupOf X) x : Subgroup X) =
      (K ⊓ rightConjugate K (x : G)).subgroupOf X := by
    ext y
    simp only [mem_inf, mem_subgroupOf, mem_rightConjugate_iff, coe_mul, coe_inv]
  rw [heq, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hKX)).toEquiv]
  exact hK.2 x hx'

theorem tightlyEmbedded_inf_subgroupOf_of_le {Q M M' : Subgroup G} (hMM' : M ≤ M')
    (htight : TightlyEmbedded (Q.subgroupOf M')) (heven : Even (Nat.card (Q ⊓ M : Subgroup G))) :
    TightlyEmbedded ((Q ⊓ M).subgroupOf M) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rwa [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
  set y' : M' := ⟨y, hMM' y.2⟩ with hy'
  have hy'N : y' ∉ normalizer ((Q.subgroupOf M' : Subgroup M') : Set M') := by
    intro hN
    apply hy
    rw [mem_normalizer_iff]
    intro z
    have h1 := (mem_normalizer_iff.mp hN) ⟨z, hMM' z.2⟩
    simp only [mem_subgroupOf, coe_mul, coe_inv, mem_inf] at h1 ⊢
    constructor
    · rintro ⟨hzQ, hzM⟩
      exact ⟨h1.mp hzQ, M.mul_mem (M.mul_mem y.2 hzM) (M.inv_mem y.2)⟩
    · rintro ⟨hzQ, -⟩
      exact ⟨h1.mpr hzQ, z.2⟩
  have hodd := htight.2 y' hy'N
  refine hodd.of_dvd_nat ?_
  rw [← card_map_of_injective M.subtype_injective,
    ← card_map_of_injective M'.subtype_injective (K := Q.subgroupOf M' ⊓ _)]
  refine card_dvd_of_le ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : x ∈ (Q ⊓ M).subgroupOf M := (mem_inf.mp hx).1
  have hx2 : x ∈ rightConjugate ((Q ⊓ M).subgroupOf M) y := (mem_inf.mp hx).2
  refine ⟨⟨x, hMM' x.2⟩, mem_inf.mpr ⟨?_, ?_⟩, rfl⟩
  · exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp hx1)).1
  · refine (mem_rightConjugate_iff _ _ _).mpr ?_
    have h2 := (mem_rightConjugate_iff _ _ _).mp hx2
    exact mem_subgroupOf.mpr (mem_inf.mp (mem_subgroupOf.mp h2)).1

theorem tightlyEmbedded_of_involution [Finite G] {Q : Subgroup G} (hev : Even (Nat.card Q))
    (h : ∀ g : G, ∀ z ∈ Q ⊓ rightConjugate Q g, orderOf z = 2 → g ∈ normalizer (Q : Set G)) :
    TightlyEmbedded Q := by
  refine ⟨hev, fun g hg => ?_⟩
  by_contra hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q ⊓ rightConjugate Q g)) 2
    (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd))
  exact hg (h g z z.2 (by rw [Subgroup.orderOf_coe]; exact hz))

theorem centralizer_le_normalizer_of_mem_of_orderOf_eq_two [Finite G] {Q : Subgroup G}
    (hQ : TightlyEmbedded Q) {t : G} (htQ : t ∈ Q) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ normalizer (Q : Set G) := by
  have hne : zpowers t ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot.mp h, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have := centralizer_two_subgroup_le Q (zpowers t) hQ
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; rfl)) (zpowers_le.mpr htQ) hne
  rwa [zpowers_eq_closure, centralizer_closure] at this

theorem tightlyEmbedded_subgroupOf_iff {R L : Subgroup G} (hRL : R ≤ L) :
    TightlyEmbedded (R.subgroupOf L) ↔ Even (Nat.card R) ∧ ∀ g ∈ L,
      g ∉ normalizer (R : Set G) → Odd (Nat.card (R ⊓ rightConjugate R g : Subgroup G)) := by
  have hcard : Nat.card (R.subgroupOf L) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv
  have hN : ∀ x : L, x ∈ normalizer ((R.subgroupOf L : Subgroup L) : Set L) ↔
      (x : G) ∈ normalizer (R : Set G) := fun x => by
    rw [← subgroupOf_normalizer_eq hRL]
    rfl
  have hinf : ∀ x : L, Nat.card (R.subgroupOf L ⊓ rightConjugate (R.subgroupOf L) x :
      Subgroup L) = Nat.card (R ⊓ rightConjugate R (x : G) : Subgroup G) := fun x => by
    have heq : (R.subgroupOf L ⊓ rightConjugate (R.subgroupOf L) x : Subgroup L) =
        (R ⊓ rightConjugate R (x : G)).subgroupOf L := by
      ext y
      simp only [mem_inf, mem_subgroupOf, mem_rightConjugate_iff, coe_mul, coe_inv]
    rw [heq]
    exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hRL)).toEquiv
  constructor
  · rintro ⟨heven, hodd⟩
    exact ⟨hcard ▸ heven, fun g hg hgN =>
      hinf ⟨g, hg⟩ ▸ hodd ⟨g, hg⟩ fun h => hgN ((hN ⟨g, hg⟩).1 h)⟩
  · rintro ⟨heven, hodd⟩
    exact ⟨hcard ▸ heven, fun x hx => (hinf x).symm ▸ hodd x x.2 fun h => hx ((hN x).2 h)⟩

theorem tightlyEmbedded_subgroupOf_top_iff (Q : Subgroup G) :
    TightlyEmbedded (Q.subgroupOf ⊤) ↔ TightlyEmbedded Q :=
  (tightlyEmbedded_subgroupOf_iff le_top).trans
    ⟨fun ⟨h1, h2⟩ => ⟨h1, fun g hg => h2 g (mem_top g) hg⟩,
      fun ⟨h1, h2⟩ => ⟨h1, fun g _ hg => h2 g hg⟩⟩

theorem tightlyEmbedded_inf_subgroupOf {Q M : Subgroup G}
    (hQ : TightlyEmbedded Q) (heven : Even (Nat.card (Q ⊓ M : Subgroup G))) :
    TightlyEmbedded ((Q ⊓ M).subgroupOf M) :=
  tightlyEmbedded_inf_subgroupOf_of_le le_top ((tightlyEmbedded_subgroupOf_top_iff Q).2 hQ) heven

theorem rightConjugate_map_mulEquiv {H : Type*} [Group H] (Q : Subgroup G) (e : G ≃* H) (g : H) :
    rightConjugate (Q.map e.toMonoidHom) g = (rightConjugate Q (e.symm g)).map e.toMonoidHom := by
  ext x
  simp only [mem_rightConjugate_iff, Subgroup.mem_map_equiv]
  rw [_root_.map_mul, _root_.map_mul, _root_.map_inv]

theorem tightlyEmbedded_map_mulEquiv {H : Type*} [Group H] {Q : Subgroup G}
    (hQ : TightlyEmbedded Q) (e : G ≃* H) : TightlyEmbedded (Q.map e.toMonoidHom) := by
  refine ⟨by rw [Subgroup.card_map_of_injective e.injective]; exact hQ.1, fun g hg => ?_⟩
  have houtside : e.symm g ∉ normalizer (Q : Set G) := by
    intro hmem
    apply hg
    rw [← Subgroup.map_equiv_normalizer_eq Q e]
    exact Subgroup.mem_map.mpr ⟨e.symm g, hmem, e.apply_symm_apply g⟩
  rw [rightConjugate_map_mulEquiv, ← Subgroup.map_inf _ _ _ e.injective,
    Subgroup.card_map_of_injective e.injective]
  exact hQ.2 (e.symm g) houtside

theorem normalizer_le_normalizer_of_le_of_even {K Q : Subgroup G} (hK : TightlyEmbedded K)
    (hQK : Q ≤ K) (hQ : Even (Nat.card Q)) : normalizer (Q : Set G) ≤ normalizer (K : Set G) := by
  intro x hx
  by_contra hxK
  have hle : Q ≤ K ⊓ rightConjugate K x := by
    refine le_inf hQK fun q hq => ?_
    rw [mem_rightConjugate_iff]
    exact hQK ((mem_normalizer_iff.mp hx q).mp hq)
  exact (Nat.not_even_iff_odd.mpr ((hK.2 x hxK).of_dvd_nat (card_dvd_of_le hle))) hQ

end CFSG.StandardSubgroupAPI
