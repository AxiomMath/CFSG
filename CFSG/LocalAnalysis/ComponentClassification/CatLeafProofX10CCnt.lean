module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CVal
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpTools

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CC

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h := Pump516.mem_normalizer_sSup (S := {A, B}) (t := g) (by
    intro K hK
    rcases Set.mem_insert_iff.mp hK with rfl | hK
    · exact hA
    · rw [Set.mem_singleton_iff.mp hK]
      exact hB)
  rwa [sSup_pair] at h

variable [Finite G]

omit [Finite G] in
theorem layer_le_normalizer_sup {A B : Subgroup G} (hA : layer G ≤ normalizer (A : Set G))
    (hB : layer G ≤ normalizer (B : Set G)) :
    layer G ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_sup (hA hg) (hB hg)

omit [Finite G] in
theorem mem_normalizer_layer (g : G) : g ∈ normalizer ((layer G : Subgroup G) : Set G) := by
  have : (layer G).Characteristic := LocalCores.layer_characteristic
  rw [normalizer_eq_top_iff.mpr inferInstance]
  exact mem_top g

theorem not_mem_layer {t : G} {W : Subgroup G} (hW : IsComponent W)
    (hne : W.map (MulAut.conj t).toMonoidHom ≠ W) : t ∉ layer G := fun htE =>
  hne (X10CV.map_conj_eq_of_mem_normalizer (Pump516.layer_le_normalizer hW htE))

theorem nu_le_card (p : ℕ) [Fact p.Prime] (X : Subgroup G) :
    padicValNat p (Nat.card X) ≤ padicValNat p (Nat.card G) :=
  X10CV.padicValNat_le_of_dvd' p Nat.card_pos.ne' (card_subgroup_dvd_card X)

theorem nu_add_diag {t : G} (ht : t * t = 1) {W M X : Subgroup G}
    (hc : ∀ x ∈ W, ∀ y ∈ W.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hMt : M ≤ centralizer ({t} : Set G)) (hMW : M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom)
    (hMp : ⁅M, M⁆ = M) (hZ : padicValNat 2 (Nat.card (center M)) ≤ 1)
    (hXW : X ≤ centralizer (W : Set G))
    (hWtX : W.map (MulAut.conj t).toMonoidHom ≤ normalizer (X : Set G)) :
    padicValNat 2 (Nat.card X) + padicValNat 2 (Nat.card M) ≤
      padicValNat 2 (Nat.card (X ⊔ W : Subgroup G)) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W' := W.map (MulAut.conj t).toMonoidHom with hW'
  set X' := X ⊔ W' with hX'
  have hM := X10CV.le_range_diagHom ht hc hMt hMW hMp
  have hW'W : W' ≤ centralizer (W : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have hX'W : X' ≤ centralizer (W : Set G) := sup_le hXW hW'W
  have hWX' : W ≤ normalizer (X' : Set G) :=
    (le_centralizer_iff.mp hX'W).trans (centralizer_le_normalizer _)
  have hW'X' : W' ≤ normalizer (X' : Set G) := fun g hg =>
    mem_normalizer_sup (hWtX hg) (le_normalizer hg)
  have hMX' : M ≤ normalizer (X' : Set G) := hMW.trans (sup_le hWX' hW'X')
  have h1 := X10CV.nu_sup_add_nu_inf 2 hWX'
  have h2 := X10CV.nu_add_le 2 (A := W) (hMW.trans (sup_le_sup_left le_sup_right W)) hMX'
  have h3 : padicValNat 2 (Nat.card (M ⊓ X' : Subgroup G)) ≤ 1 := by
    have hle : M ⊓ X' ≤ (center M).map M.subtype := by
      intro m hm
      refine ⟨⟨m, (mem_inf.mp hm).1⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro y
      exact Subtype.ext (X10CV.commute_of_mem_inf hc hM hMW hX'W le_sup_right hm y.2).symm
    have h4 := X10CV.nu_le_of_le 2 hle
    rw [card_map_of_injective M.subtype_injective] at h4
    exact h4.trans hZ
  have h5 := X10CV.nu_le_of_le 2 (inf_le_inf_right W (le_sup_left : X ≤ X'))
  have h6 := X10CV.nu_sup_add_nu_inf 2
    ((le_centralizer_iff.mp hXW).trans (centralizer_le_normalizer _) : W ≤ normalizer (X : Set G))
  rw [sup_comm W X'] at h2
  rw [← hX'] at h2 h5
  omega

theorem nu_add_component (p : ℕ) [Fact p.Prime] {L X : Subgroup G}
    (hXL : X ≤ centralizer (L : Set G)) :
    padicValNat p (Nat.card X) + padicValNat p (Nat.card L) ≤
      padicValNat p (Nat.card (X ⊔ L : Subgroup G)) + padicValNat p (Nat.card (center L)) := by
  have hLX : L ≤ normalizer (X : Set G) :=
    (le_centralizer_iff.mp hXL).trans (centralizer_le_normalizer _)
  have h1 := X10CV.nu_sup_add_nu_inf p hLX
  have hle : X ⊓ L ≤ (center L).map L.subtype := by
    intro y hy
    obtain ⟨hyX, hyL⟩ := mem_inf.mp hy
    refine ⟨⟨y, hyL⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.mp (hXL hyX)) g g.2)
  have h2 := X10CV.nu_le_of_le p hle
  rw [card_map_of_injective L.subtype_injective] at h2
  omega

theorem nu_sup_zpowers {E : Subgroup G} {t : G} (ht : t * t = 1) (htE : t ∉ E)
    (htN : t ∈ normalizer (E : Set G)) :
    padicValNat 2 (Nat.card (E ⊔ zpowers t : Subgroup G)) = padicValNat 2 (Nat.card E) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := X10CV.nu_sup_add_nu_inf 2 (zpowers_le.mpr htN : zpowers t ≤ normalizer (E : Set G))
  have ht1 : t ≠ 1 := fun h => htE (h ▸ one_mem E)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hinf : E ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyE, hyt⟩ := mem_inf.mp hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hyt
    rw [mem_bot]
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul, zpow_two, ht, one_zpow]
    · rw [zpow_add, zpow_mul, zpow_two, ht, one_zpow, one_mul, zpow_one] at hyE
      exact absurd hyE htE
  rw [hinf, Subgroup.card_bot, padicValNat_one_right, Nat.card_zpowers, hord,
    padicValNat_self] at h1
  omega

theorem nu_eq_center_add (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    padicValNat p (Nat.card L) =
      padicValNat p (Nat.card (center L)) + padicValNat p (Nat.card (L ⧸ center L)) := by
  rw [card_eq_card_quotient_mul_card_subgroup (center L),
    padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', add_comm]

theorem isPGroup_center_of_isComponent (hO : pPrimeCore 2 G = ⊥) {L : Subgroup G}
    (hL : IsComponent L) : pPrimeCore 2 L = ⊥ ∧ IsPGroup 2 (center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pPrimeCore 2 L = ⊥ := by
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 L hL.2, hO, bot_subgroupOf]
  exact ⟨h1, TBLit.center_isPGroup_two_of_pPrimeCore_eq_bot h1⟩

end CFSG.ComponentClassification.CatLeafProof.X10CC
