module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.LongestElement
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3951

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

@[expose] def G2Conj (x y : ModGL .G2 K) : Prop :=
  ∃ g ∈ adjointGroup .G2 K, g * x * g⁻¹ = y

namespace G2Conj

omit [CharP K 2] in
theorem trans {x y z : ModGL .G2 K} (h₁ : G2Conj x y) (h₂ : G2Conj y z) : G2Conj x z := by
  obtain ⟨g, hg, rfl⟩ := h₁
  obtain ⟨h, hh, rfl⟩ := h₂
  exact ⟨h * g, mul_mem hh hg, by group⟩

omit [CharP K 2] in
theorem of_eq {x y z : ModGL .G2 K} (h : x = y) (h' : G2Conj y z) : G2Conj x z := h ▸ h'

omit [CharP K 2] in
theorem or_of {x y a b : ModGL .G2 K} (h : G2Conj x y) (h' : G2Conj y a ∨ G2Conj y b) :
    G2Conj x a ∨ G2Conj x b :=
  h'.imp h.trans h.trans

omit [CharP K 2] in
theorem or_of_eq {x y a b : ModGL .G2 K} (h : x = y) (h' : G2Conj y a ∨ G2Conj y b) :
    G2Conj x a ∨ G2Conj x b :=
  h ▸ h'

theorem pinnedX (α : Fin Tag.G2.rank → ℤ) (s : K) (x : ModGL .G2 K) :
    G2Conj x (X α s * x * X α s) :=
  ⟨X α s, pinnedX_mem_adjointGroup α s, by rw [pinnedX_inv_eq]⟩

omit [CharP K 2] in
theorem c_one {x : K} (hx : x ≠ 0) : G2Conj (X g2c x) (X g2c 1) :=
  ⟨torusElt .G2 K g2ia (Units.mk0 x hx)⁻¹, torusElt_mem_adjointGroup _ _, by
    rw [torus_a_c, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx]⟩

omit [CharP K 2] in
theorem v_one {x : K} (hx : x ≠ 0) : G2Conj (X g2v x) (X g2v 1) :=
  ⟨torusElt .G2 K g2ir (Units.mk0 x hx)⁻¹, torusElt_mem_adjointGroup _ _, by
    rw [torus_r_v, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx]⟩

theorem b_c (x : K) : G2Conj (X g2b x) (X g2c x) :=
  ⟨weylElt .G2 K g2ia 1, weylElt_mem_adjointGroup _ _, by
    rw [weylElt_conj g2ia isRoot_g2b, reflect_a_b]⟩

theorem a_b (x : K) : G2Conj (X g2a x) (X g2b x) :=
  ⟨weylElt .G2 K g2ir 1, weylElt_mem_adjointGroup _ _, by
    rw [weylElt_conj g2ir isRoot_g2a, reflect_r_a]⟩

theorem u_v (x : K) : G2Conj (X g2u x) (X g2v x) :=
  ⟨weylElt .G2 K g2ir 1, weylElt_mem_adjointGroup _ _, by
    rw [weylElt_conj g2ir isRoot_g2u, reflect_r_u]⟩

theorem r_u (x : K) : G2Conj (X g2r x) (X g2u x) :=
  ⟨weylElt .G2 K g2ia 1, weylElt_mem_adjointGroup _ _, by
    rw [weylElt_conj g2ia isRoot_g2r, reflect_a_r]⟩

theorem b_one {x : K} (hx : x ≠ 0) : G2Conj (X g2b x) (X g2c 1) := (b_c x).trans (c_one hx)

theorem a_one {x : K} (hx : x ≠ 0) : G2Conj (X g2a x) (X g2c 1) := (a_b x).trans (b_one hx)

theorem u_one {x : K} (hx : x ≠ 0) : G2Conj (X g2u x) (X g2v 1) := (u_v x).trans (v_one hx)

theorem r_one {x : K} (hx : x ≠ 0) : G2Conj (X g2r x) (X g2v 1) := (r_u x).trans (u_one hx)

end G2Conj

theorem conj_nr_av (h B D : K) :
    X g2nr h * g2N 0 B 0 D 0 0 * X g2nr h = g2N 0 (B + D * h ^ 2) 0 D 0 (D ^ 2 * h) := by
  have e : g2N 0 B 0 D 0 0 = X g2a B * X g2v D := by
    simp only [g2N, pinnedX_zero, mul_one, one_mul]
  have e' : g2N 0 (B + D * h ^ 2) 0 D 0 (D ^ 2 * h) =
      X g2a B * (X g2a (D * h ^ 2) * (X g2v D * X g2c (D ^ 2 * h))) := by
    simp only [g2N, pinnedX_zero, mul_one, one_mul, pinnedX_add, mul_assoc]
  rw [e, e', ← mul_assoc, (commute_a_nr B h).symm.eq, mul_assoc, mul_assoc,
    ← mul_assoc _ _ (X g2nr h), conj_nr_v, ← mul_assoc (X g2v D),
    ← (commute_a_v (D * h ^ 2) D).eq, mul_assoc]

theorem g2Conj_of_involution [Finite K] {A B C D E F : K}
    (hsq : g2N A B C D E F * g2N A B C D E F = 1) (hne : g2N A B C D E F ≠ 1) :
    G2Conj (g2N A B C D E F) (X g2c 1) ∨ G2Conj (g2N A B C D E F) (X g2v 1) := by
  rw [g2N_mul_self, ← g2N_zero] at hsq
  obtain ⟨-, -, h1, -, h3, h4⟩ := g2N_injective hsq
  have hsqrt : ∀ y : K, ∃ r : K, r * r = y := fun y => by
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' y
    exact ⟨r, hr.symm⟩
  have h2 : (2 : K) = 0 := two_eq_zero_K
  by_cases hA : A = 0
  swap
  ·
    have hB : B = 0 := (mul_eq_zero.1 h1).resolve_left hA
    subst hB
    have hD : D = A * C := by
      have h' : A * (A * C + D) = 0 := by linear_combination h3
      linear_combination (mul_eq_zero.1 h').resolve_left hA - A * C * h2
    subst hD
    right
    refine (G2Conj.pinnedX g2a (C / A) _).trans (G2Conj.of_eq (conj_a _ _ _ _ _ _ _) ?_)
    obtain ⟨s, hs⟩ := hsqrt ((F + A ^ 3 * 0 * (C / A) + A ^ 2 * C * (C / A) + E * (C / A)) / A)
    refine G2Conj.of_eq (g2N_eq_g2N (C' := 0) (D' := 0) rfl rfl (by field_simp; char2_ring)
      (by field_simp; char2_ring) rfl rfl) ?_
    refine (G2Conj.pinnedX g2u s _).trans (G2Conj.of_eq (conj_u _ _ _ _ _ _ _) ?_)
    refine (G2Conj.pinnedX g2v ((E + A ^ 3 * (C / A) + A ^ 2 * s) / A) _).trans
      (G2Conj.of_eq (conj_v _ _ _ _ _ _ _) ?_)
    refine G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by field_simp; char2_ring) ?_).trans
      (pinnedX_r_eq_g2N A).symm) (G2Conj.r_one hA)
    rw [show s ^ 2 = s * s from sq s, hs]
    field_simp
    char2_ring
  subst hA
  have h4' : B * E + C * D = 0 := by linear_combination h4
  by_cases hB : B = 0
  swap
  ·
    refine (G2Conj.pinnedX g2r (C / B) _).or_of (G2Conj.or_of_eq (conj_r _ _ _ _ _ _ _) ?_)
    have hE : E + B * (C / B) ^ 3 + C * (C / B) ^ 2 + D * (C / B) = 0 := by
      have e : E + B * (C / B) ^ 3 + C * (C / B) ^ 2 + D * (C / B) =
          (B * E + C * D) / B + 2 * (C ^ 3 / B ^ 2) := by
        field_simp
        ring
      rw [e, h4', h2]
      simp
    refine G2Conj.or_of_eq (g2N_eq_g2N (C' := 0) (E' := 0) rfl rfl (by field_simp; char2_ring)
      rfl hE rfl) ?_
    generalize D + B * (C / B) ^ 2 = D₁
    generalize F + B ^ 2 * (C / B) ^ 3 + B * C * (C / B) ^ 2 + C ^ 2 * (C / B) = F₁
    refine (G2Conj.pinnedX g2b (F₁ / B) _).or_of (G2Conj.or_of_eq (conj_b _ _ _ _ _ _ _) ?_)
    refine G2Conj.or_of_eq (g2N_eq_g2N (F' := 0) rfl rfl rfl rfl rfl
      (by field_simp; char2_ring)) ?_
    by_cases hD₁ : D₁ = 0
    · left
      exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl hD₁ rfl rfl).trans (pinnedX_a_eq_g2N B).symm)
        (G2Conj.a_one hB)
    · right
      obtain ⟨h, hh⟩ := hsqrt (B / D₁)
      refine (G2Conj.pinnedX g2nr h _).trans (G2Conj.of_eq (conj_nr_av _ _ _) ?_)
      refine G2Conj.of_eq (g2N_eq_g2N (B' := 0) rfl
        (by rw [show h ^ 2 = h * h from sq h, hh]; field_simp; char2_ring) rfl rfl rfl rfl) ?_
      refine (G2Conj.pinnedX g2u (D₁ * h) _).trans (G2Conj.of_eq (conj_u _ _ _ _ _ _ _) ?_)
      exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by char2_ring) (by char2_ring)).trans
        (pinnedX_v_eq_g2N D₁).symm) (G2Conj.v_one hD₁)
  subst hB
  have hCD : C * D = 0 := by linear_combination h4'
  by_cases hC : C = 0
  · subst hC
    by_cases hD : D = 0
    · subst hD
      by_cases hE : E = 0
      · subst hE
        have hF : F ≠ 0 := fun h => hne (by rw [h, g2N_zero])
        exact Or.inl (G2Conj.of_eq (pinnedX_c_eq_g2N F).symm (G2Conj.c_one hF))
      · left
        refine (G2Conj.pinnedX g2a (F / E) _).trans (G2Conj.of_eq (conj_a _ _ _ _ _ _ _) ?_)
        exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) (by char2_ring)
          (by field_simp; char2_ring)).trans (pinnedX_b_eq_g2N E).symm) (G2Conj.b_one hE)
    · right
      refine (G2Conj.pinnedX g2r (E / D) _).trans (G2Conj.of_eq (conj_r _ _ _ _ _ _ _) ?_)
      refine G2Conj.of_eq (g2N_eq_g2N (C' := 0) (D' := D) (E' := 0) (F' := F) rfl rfl
        (by char2_ring) (by char2_ring) (by field_simp; char2_ring) (by char2_ring)) ?_
      refine (G2Conj.pinnedX g2u (F / D) _).trans (G2Conj.of_eq (conj_u _ _ _ _ _ _ _) ?_)
      exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by char2_ring)
        (by field_simp; char2_ring)).trans (pinnedX_v_eq_g2N D).symm) (G2Conj.v_one hD)
  · have hD : D = 0 := (mul_eq_zero.1 hCD).resolve_left hC
    subst hD
    right
    obtain ⟨s, hs⟩ := hsqrt (E / C)
    refine (G2Conj.pinnedX g2r s _).trans (G2Conj.of_eq (conj_r _ _ _ _ _ _ _) ?_)
    refine G2Conj.of_eq (g2N_eq_g2N (C' := C) (D' := 0) (E' := 0) (F' := F + C ^ 2 * s) rfl rfl
      (by char2_ring) (by char2_ring)
      (by rw [show s ^ 2 = s * s from sq s, hs]; field_simp; char2_ring) (by char2_ring)) ?_
    refine (G2Conj.pinnedX g2v ((F + C ^ 2 * s) / C) _).trans
      (G2Conj.of_eq (conj_v _ _ _ _ _ _ _) ?_)
    exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by char2_ring)
      (by field_simp; char2_ring)).trans (pinnedX_u_eq_g2N C).symm) (G2Conj.u_one hC)

theorem exists_conj_mem_posUnipotent [Finite K] (z : adjointGroup .G2 K) (hz : orderOf z = 2) :
    ∃ g : adjointGroup .G2 K,
      ((g * z * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) ∈ posUnipotent .G2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element .G2
  obtain ⟨P, hP⟩ := (exceptional_ordinary_Sylow_opposition .G2 K 2 w₀ hw₀).1
  have hp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) Q P
  refine ⟨g, ?_⟩
  have hmem : g * z * g⁻¹ ∈ (P : Subgroup (adjointGroup .G2 K)) := by
    rw [← hg, coe_smul_sylow_eq_map]
    exact ⟨z, hQ (Subgroup.mem_zpowers z), rfl⟩
  rw [hP] at hmem
  exact Subgroup.mem_subgroupOf.1 hmem

theorem even_G2_involutions_conjugate_to_root_elements (K : Type) [Field K] [Finite K]
    (hK : ringChar K = 2) (z : adjointGroup .G2 K) (hz : orderOf z = 2) :
    IsConj z ⟨pinnedX .G2 K g2c 1, pinnedX_mem_adjointGroup g2c 1⟩ ∨
      IsConj z ⟨pinnedX .G2 K g2v 1, pinnedX_mem_adjointGroup g2v 1⟩ := by
  have : CharP K 2 := ringChar.eq_iff.1 hK
  obtain ⟨g, hg⟩ := exists_conj_mem_posUnipotent z hz
  obtain ⟨A, B, C, D, E, F, hN⟩ := exists_g2N_of_mem_posUnipotent hg
  have hz1 : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hsq : g2N A B C D E F * g2N A B C D E F = 1 := by
    have e : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
      rw [show g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ by group, hz1, mul_one,
        mul_inv_cancel]
    rw [hN]
    exact congrArg Subtype.val e
  have hne : g2N A B C D E F ≠ 1 := by
    rw [hN]
    intro h
    have h' : g * z * g⁻¹ = 1 := Subtype.ext h
    have hz' : z = 1 := by
      rw [mul_inv_eq_one, mul_eq_left] at h'
      exact h'
    rw [hz', orderOf_one] at hz
    exact absurd hz (by decide)
  have key : ∀ y : ModGL .G2 K, (hy : y ∈ adjointGroup .G2 K) →
      G2Conj (g2N A B C D E F) y → IsConj z ⟨y, hy⟩ := by
    rintro y hy ⟨h, hh, rfl⟩
    refine isConj_iff.2 ⟨⟨h, hh⟩ * g, Subtype.ext ?_⟩
    show _ = h * g2N A B C D E F * h⁻¹
    rw [hN]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  rcases g2Conj_of_involution hsq hne with h | h
  · exact Or.inl (key _ _ h)
  · exact Or.inr (key _ _ h)

end CFSG.ComponentClassification.UnbalancedCatalog
