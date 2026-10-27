module

public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped Pointwise

section Ext2

variable {G : Type} [Group G]

def ext2 (A : Subgroup G) (a : G) (ha2 : a * a = 1) (hconj : ∀ x ∈ A, a * x * a ∈ A) :
    Subgroup G where
  carrier := {x | x ∈ A ∨ a * x ∈ A}
  mul_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (A.mul_mem hx hy)
    · right
      have e : (a * x * a) * (a * y) = a * (x * y) := by
        calc (a * x * a) * (a * y) = a * x * (a * a) * y := by group
          _ = a * (x * y) := by rw [ha2]; group
      rw [← e]
      exact A.mul_mem (hconj x hx) hy
    · right
      rw [← mul_assoc]
      exact A.mul_mem hx hy
    · left
      have e : (a * (a * x) * a) * (a * y) = x * y := by
        calc (a * (a * x) * a) * (a * y) = (a * a) * x * (a * a) * y := by group
          _ = x * y := by rw [ha2]; group
      rw [← e]
      exact A.mul_mem (hconj _ hx) hy
  one_mem' := Or.inl A.one_mem
  inv_mem' := by
    rintro x (hx | hx)
    · exact Or.inl (A.inv_mem hx)
    · right
      have e : a * x⁻¹ = a * (a * x)⁻¹ * a := by
        rw [mul_inv_rev]
        group
      rw [e]
      exact hconj _ (A.inv_mem hx)

variable {A B : Subgroup G} {a : G} {ha2 : a * a = 1} {hA : ∀ x ∈ A, a * x * a ∈ A}
  {hB : ∀ x ∈ B, a * x * a ∈ B}

theorem mem_ext2 {x : G} : x ∈ ext2 A a ha2 hA ↔ x ∈ A ∨ a * x ∈ A := Iff.rfl

theorem le_ext2 : A ≤ ext2 A a ha2 hA := fun _ hx => Or.inl hx

theorem a_mem_ext2 : a ∈ ext2 A a ha2 hA := Or.inr (by rw [ha2]; exact A.one_mem)

theorem ext2_mono (hAB : A ≤ B) : ext2 A a ha2 hA ≤ ext2 B a ha2 hB := by
  rintro x (hx | hx)
  · exact Or.inl (hAB hx)
  · exact Or.inr (hAB hx)

theorem ext2_inf_eq (hAB : A ≤ B) (haB : a ∉ B) {x : G} (hx : x ∈ ext2 A a ha2 hA)
    (hxB : x ∈ B) : x ∈ A := by
  rcases hx with hx | hx
  · exact hx
  · exfalso
    apply haB
    have : a = (a * x) * x⁻¹ := by group
    rw [this]
    exact B.mul_mem (hAB hx) (B.inv_mem hxB)

@[expose] noncomputable def sylowOfIsSylow2In {V P : Subgroup G} (h : IsSylow2In V P) :
    Sylow 2 ↥P where
  toSubgroup := V.subgroupOf P
  isPGroup' := h.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hVQ : V ≤ Q.map P.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
      exact Subgroup.map_mono hle
    have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
    rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
    rfl

theorem coe_sylowOfIsSylow2In {V P : Subgroup G} (h : IsSylow2In V P) :
    (sylowOfIsSylow2In h : Subgroup ↥P) = V.subgroupOf P := rfl

variable [Finite G]

theorem isPGroup_ext2 (hA2 : IsPGroup 2 A) : IsPGroup 2 (ext2 A a ha2 hA) := by
  rintro ⟨x, hx⟩
  rcases hx with hx | hx
  · obtain ⟨k, hk⟩ := hA2 ⟨x, hx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  · have hy : a * x ∈ A := hx
    have hxx : x * x ∈ A := by
      have e : x * x = (a * (a * x) * a) * (a * x) := by
        calc x * x = (a * a) * x * (a * a) * x := by rw [ha2]; group
          _ = (a * (a * x) * a) * (a * x) := by group
      rw [e]
      exact A.mul_mem (hA _ hy) hy
    obtain ⟨k, hk⟩ := hA2 ⟨x * x, hxx⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_succ, pow_mul', pow_two]
    exact h1

theorem isSylow2In_ext2 (hR : IsSylow2In A B) :
    IsSylow2In (ext2 A a ha2 hA) (ext2 B a ha2 hB) := by
  refine ⟨ext2_mono hR.1, isPGroup_ext2 hR.2.1, fun V hVH hV2 hPV => ?_⟩
  refine le_antisymm (fun x hx => ?_) hPV
  have haV : a ∈ V := hPV a_mem_ext2
  have hAV : A ≤ V := le_ext2.trans hPV
  have hVB : V ⊓ B = A := hR.2.2 (V ⊓ B) inf_le_right (hV2.to_le inf_le_left)
    (le_inf hAV hR.1)
  rcases hVH hx with hxB | hxB
  · exact Or.inl (hVB ▸ (⟨hx, hxB⟩ : x ∈ V ⊓ B))
  · refine Or.inr ?_
    have haxV : a * x ∈ V := V.mul_mem haV hx
    exact hVB ▸ (⟨haxV, hxB⟩ : a * x ∈ V ⊓ B)

theorem exists_twist_of_sylow {K R R₁ : Subgroup G} {a : G} (ha2 : a * a = 1) (haK : a ∉ K)
    (hK : ∀ x ∈ K, a * x * a ∈ K) (hR : IsSylow2In R K) (hR₁ : IsSylow2In R₁ K)
    (hRa : ∀ x ∈ R, a * x * a ∈ R) (hR₁a : ∀ x ∈ R₁, a * x * a ∈ R₁) :
    ∃ g : G, conjSub g R₁ = R ∧ ∃ r ∈ R, g * a * g⁻¹ = a * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := ext2 K a ha2 hK with hH
  set P := ext2 R a ha2 hRa with hP
  set P₁ := ext2 R₁ a ha2 hR₁a with hP₁
  have hPs : IsSylow2In P H := isSylow2In_ext2 hR
  have hP₁s : IsSylow2In P₁ H := isSylow2In_ext2 hR₁
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (sylowOfIsSylow2In hP₁s)
    (sylowOfIsSylow2In hPs)
  have hconjP : ∀ x : G, x ∈ P ↔ (g : G)⁻¹ * x * (g : G) ∈ P₁ := by
    intro x
    have h1 : ((g • sylowOfIsSylow2In hP₁s : Sylow 2 ↥H) : Subgroup ↥H) =
        (sylowOfIsSylow2In hPs : Subgroup ↥H) := by rw [hg]
    rw [Sylow.coe_subgroup_smul, coe_sylowOfIsSylow2In, coe_sylowOfIsSylow2In] at h1
    have hmemSub : ∀ y : ↥H, y ∈ P.subgroupOf H ↔ g⁻¹ * y * g ∈ P₁.subgroupOf H := by
      intro y
      have h2 : y ∈ MulAut.conj g • P₁.subgroupOf H ↔ y ∈ P.subgroupOf H := by rw [h1]
      rw [Subgroup.mem_smul_pointwise_iff_exists] at h2
      constructor
      · intro hy
        obtain ⟨b, hb, hby⟩ := h2.mpr hy
        have hb' : b = g⁻¹ * y * g := by
          rw [← hby]
          simp only [MulAut.smul_def, MulAut.conj_apply]
          group
        rw [← hb']
        exact hb
      · intro hy
        refine h2.mp ⟨g⁻¹ * y * g, hy, ?_⟩
        simp only [MulAut.smul_def, MulAut.conj_apply]
        group
    constructor
    · intro hx
      have hxH : x ∈ H := hPs.1 hx
      exact (hmemSub ⟨x, hxH⟩).mp hx
    · intro hx
      have hgH : (g : G) ∈ H := g.2
      have hxH : x ∈ H := by
        have h1 : (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ = x := by group
        rw [← h1]
        exact H.mul_mem (H.mul_mem hgH (hP₁s.1 hx)) (H.inv_mem hgH)
      exact (hmemSub ⟨x, hxH⟩).mpr hx
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hK' : ∀ x : G, x ∈ K ↔ a * x * a ∈ K := fun x =>
    ⟨hK x, fun hx => by
      have := hK _ hx
      have e : a * (a * x * a) * a = x := by
        calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
          _ = x := by rw [ha2]; group
      rwa [e] at this⟩
  have hnorm : ∀ h : G, h ∈ H → ∀ x : G, x ∈ K ↔ h * x * h⁻¹ ∈ K := by
    intro h hh x
    rcases hh with hh | hh
    · constructor
      · intro hx
        exact K.mul_mem (K.mul_mem hh hx) (K.inv_mem hh)
      · intro hx
        have := K.mul_mem (K.mul_mem (K.inv_mem hh) hx) hh
        simpa [mul_assoc] using this
    · have hk : a * h ∈ K := hh
      have hhk : h = a * (a * h) := by
        calc h = (a * a) * h := by rw [ha2, one_mul]
          _ = a * (a * h) := by group
      have e : h * x * h⁻¹ = a * ((a * h) * x * (a * h)⁻¹) * a := by
        calc h * x * h⁻¹ = (a * a) * h * x * h⁻¹ * (a * a) := by rw [ha2]; group
          _ = a * ((a * h) * x * (a * h)⁻¹) * a := by
            rw [mul_inv_rev, hai]; group
      rw [e, ← hK']
      constructor
      · intro hx
        exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
      · intro hx
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
        simpa [mul_assoc] using this
  have hgH : (g : G) ∈ H := g.2
  have hKnorm : ∀ x : G, x ∈ K ↔ (g : G)⁻¹ * x * (g : G) ∈ K := by
    intro x
    have := hnorm ((g : G)⁻¹) (H.inv_mem hgH) x
    simpa only [inv_inv] using this
  have hRK : ∀ x : G, x ∈ P → x ∈ K → x ∈ R := fun x hx hxK => ext2_inf_eq hR.1 haK hx hxK
  have hR₁K : ∀ x : G, x ∈ P₁ → x ∈ K → x ∈ R₁ := fun x hx hxK =>
    ext2_inf_eq hR₁.1 haK hx hxK
  have hconjR : conjSub (g : G) R₁ = R := by
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have hxP : x ∈ P := (hconjP x).mpr (le_ext2 hx)
      have hxK : x ∈ K := (hKnorm x).mpr (hR₁.1 hx)
      exact hRK x hxP hxK
    · intro hx
      have h1 : (g : G)⁻¹ * x * (g : G) ∈ P₁ := (hconjP x).mp (le_ext2 hx)
      have h2 : (g : G)⁻¹ * x * (g : G) ∈ K := (hKnorm x).mp (hR.1 hx)
      exact hR₁K _ h1 h2
  have haP₁ : a ∈ P₁ := a_mem_ext2
  have hgag : (g : G) * a * (g : G)⁻¹ ∈ P := by
    rw [hconjP]
    have e : (g : G)⁻¹ * ((g : G) * a * (g : G)⁻¹) * (g : G) = a := by group
    rw [e]
    exact haP₁
  have hagK : a * ((g : G) * a * (g : G)⁻¹) ∈ K := by
    rcases hgH with hg1 | hg1
    · have e : a * ((g : G) * a * (g : G)⁻¹) = (a * (g : G) * a) * (g : G)⁻¹ := by group
      rw [e]
      exact K.mul_mem (hK _ hg1) (K.inv_mem hg1)
    · have hk : a * (g : G) ∈ K := hg1
      have hgk : (g : G) = a * (a * (g : G)) := by
        calc (g : G) = (a * a) * (g : G) := by rw [ha2, one_mul]
          _ = a * (a * (g : G)) := by group
      have e : a * ((g : G) * a * (g : G)⁻¹) =
          (a * (g : G)) * (a * (a * (g : G))⁻¹ * a) := by
        calc a * ((g : G) * a * (g : G)⁻¹)
            = a * ((a * (a * (g : G))) * a * (a * (a * (g : G)))⁻¹) := by rw [← hgk]
          _ = (a * a) * (a * (g : G)) * a * (a * (g : G))⁻¹ * a⁻¹ := by
            rw [mul_inv_rev]; group
          _ = (a * (g : G)) * a * (a * (g : G))⁻¹ * a := by rw [ha2, one_mul, hai]
          _ = (a * (g : G)) * (a * (a * (g : G))⁻¹ * a) := by group
      rw [e]
      exact K.mul_mem hk (hK _ (K.inv_mem hk))
  have hrR : a * ((g : G) * a * (g : G)⁻¹) ∈ R := by
    rcases hgag with h1 | h1
    · exfalso
      apply haK
      have h2 : (g : G) * a * (g : G)⁻¹ ∈ K := hR.1 h1
      have e : a = (a * ((g : G) * a * (g : G)⁻¹)) * ((g : G) * a * (g : G)⁻¹)⁻¹ := by group
      rw [e]
      exact K.mul_mem hagK (K.inv_mem h2)
    · exact h1
  refine ⟨g, hconjR, a * ((g : G) * a * (g : G)⁻¹), hrR, ?_⟩
  calc (g : G) * a * (g : G)⁻¹ = (a * a) * ((g : G) * a * (g : G)⁻¹) := by rw [ha2, one_mul]
    _ = a * (a * ((g : G) * a * (g : G)⁻¹)) := by group

end Ext2

end CFSG.ClassicalInvolution.Asc77.C25V
