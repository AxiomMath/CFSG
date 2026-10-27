module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCGen
public import CFSG.GF2Type.Aschbacher1976Full.HSVDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.PartC

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G]

section Sq

variable {z : G} {Z A : Subgroup G} {T V : Subgroup G}

theorem V_le_W (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2) (hF2 : IsPGroup 2 (Fz z))
    (hV : HSV z T V) : V ≤ WT T z := by
  intro v hv
  by_cases h1 : v = 1
  · rw [h1]
    exact one_mem _
  · exact hV.ZF_le_W v hv h1 (ZF_props hD hz hF2 (hV.isConj v hv h1)).2.2.1

theorem exists_sq_in_W (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hV : HSV z T V) :
    ∀ v ∈ V, ∃ y ∈ WT T z, y * y = v := by
  intro v hv
  by_cases h1 : v = 1
  · exact ⟨1, one_mem _, by rw [h1, one_mul]⟩
  · have hconj := hV.isConj v hv h1
    obtain ⟨y, hy⟩ := exists_gen hD hz hF2 hconj
    have hyW : y ∈ WT T z := hV.ZF_le_W v hv h1 (hy ▸ mem_zpowers y)
    exact ⟨y, hyW, by rw [← pow_two]; exact (gen_props hD hz hF2 hconj hy).2⟩

theorem mem_V_of_sq_eq_one (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hV : HSV z T V) {c : G} (hc : c ∈ WT T z) (hc2 : c * c = 1) :
    c ∈ V := by
  have hWc := hV.W_comm
  let φ : ↥(WT T z) →* ↥(WT T z) := MonoidHom.mk' (fun x => x * x) (fun a b => by
    have hab : Commute b a := Subtype.ext (hWc b b.2 a a.2)
    exact hab.mul_mul_mul_comm a b)
  have hVW : V ≤ WT T z := V_le_W hD hz hF2 hV
  have hcardV : Nat.card (V.subgroupOf (WT T z)) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv, hV.card_eq]
  have hker : V.subgroupOf (WT T z) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have h2 := hV.isElem.2 x hx
    refine Subtype.ext ?_
    show (x : G) * (x : G) = 1
    rw [← pow_two]
    exact h2
  have hrange : V.subgroupOf (WT T z) ≤ φ.range := by
    intro x hx
    obtain ⟨y, hyW, hy⟩ := exists_sq_in_W hD hz hF2 hV (x : G) hx
    exact ⟨⟨y, hyW⟩, Subtype.ext hy⟩
  have h1 := Subgroup.card_ker_mul_card_range φ
  rw [hV.card_W] at h1
  have h2 : 8 ≤ Nat.card φ.range := hcardV ▸ Subgroup.card_le_of_le hrange
  have h3 : Nat.card φ.ker ≤ 8 := by
    have : Nat.card φ.ker * 8 ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul_left _ h2
    omega
  have heq : V.subgroupOf (WT T z) = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hker (by rw [hcardV]; exact h3)
  have hmem : (⟨c, hc⟩ : ↥(WT T z)) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact Subtype.ext hc2
  rw [← heq] at hmem
  exact hmem

theorem W_le_centralizer (hD : Width.Z4Data z 2 Z A) (hz : orderOf z = 2)
    (hF2 : IsPGroup 2 (Fz z)) (hV : HSV z T V) :
    WT T z ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact hV.W_comm v (V_le_W hD hz hF2 hV hv) x hx

end Sq

end CFSG.GF2Type.Aschbacher1976Full.HS.PartC
