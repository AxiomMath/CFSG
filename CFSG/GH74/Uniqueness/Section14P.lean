module

public import CFSG.GH74.Uniqueness.Bender.Sylow2SpecialSuzuki
public import CFSG.GH74.Uniqueness.Bender.OddCentralizer
public import CFSG.GH74.Uniqueness.Section12Transport
public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section RootData

theorem sq_inj_of_rootData {R : Type*} [Group R] [Finite R] {q : ℕ}
    (hR : ProperTwoGeneratedCore.Lemma37.BenderRootData R q q) (Z : Subgroup R)
    (hZc : ∀ z ∈ Z, ∀ g : R, z * g = g * z) (hZsq : ∀ z ∈ Z, z * z = 1)
    (hZcard : Nat.card Z = q) (hsqZ : ∀ x : R, x * x ∈ Z) :
    ∀ x y : R, x * x = y * y → x⁻¹ * y ∈ Z := by
  intro x y hxy
  by_cases hr : x * x = 1
  ·
    have hsurj : Function.Surjective (fun z : Z => (⟨(z : R), by
        rw [sq]; exact hZsq z z.2⟩ : {w : R // w ^ 2 = 1})) := by
      have hinj : Function.Injective (fun z : Z => (⟨(z : R), by
          rw [sq]; exact hZsq z z.2⟩ : {w : R // w ^ 2 = 1})) := by
        intro a b hab
        apply Subtype.ext
        have := congrArg (fun w : {w : R // w ^ 2 = 1} => (w : R)) hab
        simpa using this
      exact (hinj.bijective_of_nat_card_le (by rw [hR.card_sq_one, hZcard])).2
    have hmem : ∀ w : R, w * w = 1 → w ∈ Z := by
      intro w hw
      obtain ⟨z, hz⟩ := hsurj ⟨w, by rw [sq]; exact hw⟩
      have := congrArg Subtype.val hz
      simp only at this
      rw [← this]
      exact z.2
    have hx := hmem x hr
    have hy := hmem y (hxy ▸ hr)
    exact Z.mul_mem (Z.inv_mem hx) hy
  ·
    set r := x * x with hrdef
    have hr2 : r ^ 2 = 1 := by rw [sq]; exact hZsq r (hsqZ x)
    have hcard := hR.card_sq r hr (hr2)
    have hmap : ∀ z : Z, (x * z) ^ 2 = r := by
      intro z
      rw [sq]
      calc x * z * (x * z) = x * (z * x) * z := by group
        _ = x * (x * z) * z := by rw [hZc z z.2 x]
        _ = (x * x) * (z * z) := by group
        _ = r := by rw [hZsq z z.2, mul_one]
    have hinj : Function.Injective (fun z : Z => (⟨x * z, hmap z⟩ : {w : R // w ^ 2 = r})) := by
      intro a b hab
      have := congrArg Subtype.val hab
      simp only [mul_right_inj] at this
      exact Subtype.ext this
    have hsurj := (hinj.bijective_of_nat_card_le (by rw [hcard, hZcard])).2
    obtain ⟨z, hz⟩ := hsurj ⟨y, by rw [sq]; exact hxy.symm⟩
    have hyz : x * z = y := congrArg Subtype.val hz
    rw [← hyz, inv_mul_cancel_left]
    exact z.2

end RootData

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

abbrev pGrp (c : Ctx12 Z M) (Q : Sylow 2 ↥c.L) : Subgroup X :=
  (Q : Subgroup ↥c.L).map c.L.subtype

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L}

theorem mem_pGrp_iff {x : X} : x ∈ pGrp c Q ↔ ∃ y ∈ (Q : Subgroup ↥c.L), (y : X) = x := by
  simp [pGrp]

theorem Mo_eq (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    zHull Z M = (Bender.rootCenter (Q : Subgroup ↥c.L)).map c.L.subtype :=
  (h.map_subtype_rootCenter S.invariant hQ).symm

theorem Mo_le_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    zHull Z M ≤ pGrp c Q := by
  rw [Mo_eq S h hQ]
  exact map_mono inf_le_left

theorem P_le_L : pGrp c Q ≤ c.L := map_subtype_le _

theorem P_le_M (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    pGrp c Q ≤ M := fun _ hx => (Ctx12.map_sylow_le hQ hx).2

theorem isPGroup_P : IsPGroup 2 (pGrp c Q) := Q.isPGroup'.map c.L.subtype

theorem card_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    Nat.card (pGrp c Q) = 2 ^ (2 * n) := by
  rw [card_map_of_injective c.L.subtype_injective, (h.benderCore S.invariant hQ).card_eq,
    ← pow_mul, mul_comm]

theorem Mo_central (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ pGrp c Q, ∀ m ∈ zHull Z M, x * m = m * x := by
  intro x hx m hm
  rw [Mo_eq S h hQ] at hm
  obtain ⟨y, hy, rfl⟩ := mem_pGrp_iff.mp hx
  obtain ⟨w, hw, rfl⟩ := mem_map.mp hm
  have h1 := (mem_centralizer_iff.mp (mem_inf.mp hw).2) y hy
  exact congrArg Subtype.val h1

theorem center_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ pGrp c Q, (∀ y ∈ pGrp c Q, x * y = y * x) → x ∈ zHull Z M := by
  intro x hx hc
  rw [Mo_eq S h hQ]
  obtain ⟨y, hy, rfl⟩ := mem_pGrp_iff.mp hx
  refine mem_map_of_mem _ (mem_inf.mpr ⟨hy, mem_centralizer_iff.mpr fun w hw => ?_⟩)
  apply Subtype.ext
  exact (hc w (mem_map_of_mem _ hw)).symm

theorem comm_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ⁅pGrp c Q, pGrp c Q⁆ = zHull Z M := by
  rw [Mo_eq S h hQ, pGrp, ← map_commutator, (h.bender.lemma_3_5_a (by norm_num) Q).1]

theorem P_sq (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ pGrp c Q, x * x ∈ zHull Z M := by
  intro x hx
  rw [Mo_eq S h hQ]
  obtain ⟨y, hy, rfl⟩ := mem_pGrp_iff.mp hx
  exact mem_map_of_mem c.L.subtype (h.bender.sq_mem_rootCenter_suzuki Q hy)

theorem P_sq_ne (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ pGrp c Q, x ∉ zHull Z M → x * x ≠ 1 := by
  intro x hx hxM hx1
  apply hxM
  rw [Mo_eq S h hQ]
  obtain ⟨y, hy, rfl⟩ := mem_pGrp_iff.mp hx
  have hy1 : y * y = 1 := Subtype.ext (by simpa using hx1)
  exact mem_map_of_mem c.L.subtype
    ((h.benderCore S.invariant hQ).mem_rootCenter_of_mul_self hy hy1)

theorem P_sq_inj (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ pGrp c Q, ∀ y ∈ pGrp c Q, x * x = y * y → x⁻¹ * y ∈ zHull Z M := by
  intro x hx y hy hxy
  rw [Mo_eq S h hQ]
  obtain ⟨x', hx', rfl⟩ := mem_pGrp_iff.mp hx
  obtain ⟨y', hy', rfl⟩ := mem_pGrp_iff.mp hy
  have hc := h.benderCore S.invariant hQ
  set R := ↥(Q : Subgroup ↥c.L)
  let Z' : Subgroup R := (Bender.rootCenter (Q : Subgroup ↥c.L)).subgroupOf (Q : Subgroup ↥c.L)
  have hZc : ∀ z ∈ Z', ∀ g : R, z * g = g * z := by
    intro z hz g
    apply Subtype.ext
    have := (mem_centralizer_iff.mp (mem_inf.mp (mem_subgroupOf.mp hz)).2) g g.2
    exact this.symm
  have hZsq : ∀ z ∈ Z', z * z = 1 := by
    intro z hz
    exact Subtype.ext (hc.center_sq z (mem_subgroupOf.mp hz))
  have hZcard : Nat.card Z' = 2 ^ n := by
    rw [← hc.card_center]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsqZ : ∀ w : R, w * w ∈ Z' := by
    intro w
    exact mem_subgroupOf.mpr (h.bender.sq_mem_rootCenter_suzuki Q w.2)
  have key := sq_inj_of_rootData (h.bender.suzuki_rootData Q) Z' hZc hZsq hZcard hsqZ
    ⟨x', hx'⟩ ⟨y', hy'⟩ (Subtype.ext (Subtype.ext (by simpa using hxy)))
  have := mem_subgroupOf.mp key
  refine ⟨_, this, ?_⟩
  simp

theorem K_eq_map (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    kGrp M c.t = (Bender.cartan (Q : Subgroup ↥c.L) c.tL).map c.L.subtype := by
  rw [Ctx12.map_subtype_cartan hQ, h.k_eq']

theorem K_trans (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ a ∈ zHull Z M, a ≠ 1 → ∀ b ∈ zHull Z M, b ≠ 1 → ∃ k ∈ kGrp M c.t, k * a * k⁻¹ = b := by
  intro a ha ha1 b hb hb1
  rw [Mo_eq S h hQ] at ha hb
  obtain ⟨a', ha', rfl⟩ := mem_map.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_map.mp hb
  have ha1' : a' ≠ 1 := fun h1 => ha1 (by rw [h1]; rfl)
  have hb1' : b' ≠ 1 := fun h1 => hb1 (by rw [h1]; rfl)
  obtain ⟨d, hd, hdd⟩ := (h.benderCore S.invariant hQ).exists_cartan_conj ha' ha1' hb' hb1'
  refine ⟨(d⁻¹ : ↥c.L), ?_, ?_⟩
  · rw [K_eq_map h hQ]
    exact mem_map_of_mem _ (inv_mem hd)
  · rw [hdd]
    simp

theorem K_fpf_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ k ∈ kGrp M c.t, k ≠ 1 → ∀ x ∈ pGrp c Q, k * x = x * k → x = 1 := by
  intro k hk hk1 x hx hkx
  rw [K_eq_map h hQ] at hk
  obtain ⟨k', hk', rfl⟩ := mem_map.mp hk
  obtain ⟨x', hx', rfl⟩ := mem_pGrp_iff.mp hx
  have hc := h.benderCore S.invariant hQ
  have hk1' : k' ≠ 1 := fun h1 => hk1 (by rw [h1]; rfl)
  have hcent := hc.centralizer_cartan_eq Q.isPGroup' hk' hk1'
  have hx'C : x' ∈ centralizer ({k'} : Set ↥c.L) :=
    mem_centralizer_singleton_iff.mpr (Subtype.ext hkx.symm)
  rw [hcent] at hx'C
  have : x' ∈ (Q : Subgroup ↥c.L) ⊓ Bender.cartan (Q : Subgroup ↥c.L) c.tL := ⟨hx', hx'C⟩
  rw [hc.inf_eq, mem_bot] at this
  rw [this]
  rfl

theorem NL_P (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ l ∈ c.L, l ∈ normalizer (pGrp c Q : Set X) →
      ∃ p ∈ pGrp c Q, ∃ k ∈ kGrp M c.t, l = p * k := by
  intro l hl hlN
  have hlB : (⟨l, hl⟩ : ↥c.L) ∈ Bender.borel (Q : Subgroup ↥c.L) := by
    rw [Bender.borel, mem_normalizer_iff]
    intro y
    have := (mem_normalizer_iff.mp hlN) (y : X)
    constructor
    · intro hy
      have h1 := this.mp (mem_map_of_mem _ hy)
      obtain ⟨w, hw, hwe⟩ := mem_pGrp_iff.mp h1
      have : w = ⟨l, hl⟩ * y * (⟨l, hl⟩ : ↥c.L)⁻¹ := Subtype.ext (by simpa using hwe)
      rw [← this]
      exact hw
    · intro hy
      have h1 : l * (y : X) * l⁻¹ ∈ pGrp c Q := mem_map.mpr ⟨_, hy, by simp⟩
      obtain ⟨w, hw, hwe⟩ := mem_pGrp_iff.mp (this.mpr h1)
      have : w = y := Subtype.ext hwe
      rw [← this]
      exact hw
  obtain ⟨p, hp, d, hd, hpd⟩ := (h.benderCore S.invariant hQ).exists_mul_of_mem_borel hlB
  refine ⟨p, mem_map_of_mem _ hp, d, ?_, ?_⟩
  · rw [K_eq_map h hQ]
    exact mem_map_of_mem _ hd
  · have := congrArg Subtype.val hpd
    simpa using this

theorem D_norm_P (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    c.D ≤ normalizer (pGrp c Q : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d hd
  have hdN : d ∈ normalizer (c.L : Set X) := by
    have : d ∈ ((normalizer (c.L : Set X) : Subgroup X) : Set X) := by
      rw [h.normalizer_eq]
      exact ⟨1, c.L.one_mem, d, hd, one_mul d⟩
    exact this
  have hdM : d ∈ M := (mem_inf.mp hd).1
  have hsyl := Ctx12.isSylowOf_map_sylow hQ
  have hPn : ∀ g ∈ c.L ⊓ M, ∀ x ∈ pGrp c Q, g * x * g⁻¹ ∈ pGrp c Q := by
    intro g hg x hx
    obtain ⟨hgL, hgM⟩ := mem_inf.mp hg
    have hgB : (⟨g, hgL⟩ : ↥c.L) ∈ normalizer ((Q : Subgroup c.L) : Set c.L) := by
      rw [← hQ]
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hgM, hgL⟩)
    obtain ⟨y, hy, rfl⟩ := mem_pGrp_iff.mp hx
    have := (mem_normalizer_iff.mp hgB y).mp hy
    exact mem_map.mpr ⟨_, this, by simp⟩
  let P' : Subgroup X := (pGrp c Q).map (MulAut.conj d).toMonoidHom
  have hP'le : P' ≤ c.L ⊓ M := by
    rintro _ ⟨x, hx, rfl⟩
    have hxLM := Ctx12.map_sylow_le hQ hx
    obtain ⟨hxL, hxM⟩ := mem_inf.mp hxLM
    refine mem_inf.mpr ⟨?_, ?_⟩
    · simpa using (mem_normalizer_iff.mp hdN x).mp hxL
    · simpa using M.mul_mem (M.mul_mem hdM hxM) (M.inv_mem hdM)
  have hP'syl : ABGLocalTools.IsSylowOf 2 P' (c.L ⊓ M) := by
    apply ABGLocalTools.isSylowOf_of_card hP'le
    rw [← hsyl.card_eq]
    exact card_map_of_injective (MulAut.conj d).injective
  have heq := isSylowOf_eq_of_normal hsyl hPn hP'syl
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : d * x * d⁻¹ ∈ P' := ⟨x, hx, by simp⟩
    rwa [heq] at this
  · intro hx
    have hx' : d * x * d⁻¹ ∈ P' := by rw [heq]; exact hx
    obtain ⟨y, hy, hye⟩ := hx'
    have : y = x := by
      have := congrArg (fun w => d⁻¹ * w * d) hye
      simpa [mul_assoc] using this
    rwa [← this]

end Sec14

end CFSG.GH74.Uniqueness
