module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LieType.Chevalley.G2FieldFourCoverRoots
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Chevalley.G2FieldFour

@[expose] def hyp {K : Type} [Field K] (w : K × K × K × K) : K :=
  w.1 * w.2.2.2 + w.2.1 * w.2.2.1

theorem card_hyperbolic_F4 :
    ∀ c : CFSG.Fischer.F4, c ≠ 0 → Fintype.card {w : CFSG.Fischer.F4 × CFSG.Fischer.F4 ×
      CFSG.Fischer.F4 × CFSG.Fischer.F4 // hyp w = c} = 60 := by
  unfold hyp
  decide +kernel

theorem card_hyperbolic {K : Type} [Field K] (hK : Nat.card K = 4) {F₀ : K} (hF : F₀ ≠ 0) :
    Nat.card {w : K × K × K × K // hyp w = F₀} = 60 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card CFSG.Fischer.F4 := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hK]
  let ρ : K ≃+* CFSG.Fischer.F4 := FiniteField.ringEquivOfCardEq hc
  have e : {w : K × K × K × K // hyp w = F₀} ≃
      {w : CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 × CFSG.Fischer.F4 //
        hyp w = ρ F₀} :=
    (ρ.toEquiv.prodCongr (ρ.toEquiv.prodCongr (ρ.toEquiv.prodCongr ρ.toEquiv))).subtypeEquiv
      fun w => by
        change hyp w = F₀ ↔ ρ w.1 * ρ w.2.2.2 + ρ w.2.1 * ρ w.2.2.1 = ρ F₀
        rw [← map_mul, ← map_mul, ← map_add, ρ.injective.eq_iff]
        rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_hyperbolic_F4 _ ((map_ne_zero ρ).2 hF)

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem conj_eq_of_commute {G : Type*} [Group G] {g x : G} (hg : g * g = 1)
    (hc : x * g = g * x) : g * x * g = x := by
  rw [← hc, mul_assoc, hg, mul_one]

theorem g2N_eq_of_commute
    {A B C D E F : K}
    (hr : g2N A B C D E F * X g2r 1 = X g2r 1 * g2N A B C D E F)
    (hv : g2N A B C D E F * X g2v 1 = X g2v 1 * g2N A B C D E F)
    (ha : g2N A B C D E F * X g2a 1 = X g2a 1 * g2N A B C D E F) :
    g2N A B C D E F = X g2c F := by
  have hr' := (conj_r 1 A B C D E F).symm.trans
    (conj_eq_of_commute (pinnedX_mul_self _ _) hr)
  have hv' := (conj_v 1 A B C D E F).symm.trans
    (conj_eq_of_commute (pinnedX_mul_self _ _) hv)
  have ha' := (conj_a 1 A B C D E F).symm.trans
    (conj_eq_of_commute (pinnedX_mul_self _ _) ha)
  obtain ⟨-, -, hC, -, hE, hF⟩ := g2N_injective hr'
  obtain ⟨-, -, -, -, hE', -⟩ := g2N_injective hv'
  obtain ⟨-, -, -, -, -, hF'⟩ := g2N_injective ha'
  simp only [one_pow, mul_one] at hC hE hF hE' hF'
  have hB : B = 0 := by linear_combination hC
  have hA : A = 0 := by linear_combination hE'
  subst hA hB
  have hCD : C + D = 0 := by linear_combination hE
  have hC2 : C ^ 2 = 0 := by linear_combination hF
  have hC0 : C = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hC2
  subst hC0
  have hD : D = 0 := by linear_combination hCD
  subst hD
  have hE0 : E = 0 := by linear_combination hF'
  subst hE0
  exact pinnedX_c_eq_g2N F |>.symm

abbrev posU
    (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  (posUnipotent .G2 K).subgroupOf (adjointGroup .G2 K)

omit [CharP K 2] in
theorem rootX_mem_posU
    {d : Fin Tag.G2.rank → ℤ} (hd : d ∈ G2FieldFour.posRoots) (s : K) :
    rootX d s ∈ posU K := by
  change pinnedX .G2 K d s ∈ posUnipotent .G2 K
  rcases Finset.mem_insert.1 hd with rfl | hd
  · rw [show rootA = g2a from rfl, pinnedX_a_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _
  rcases Finset.mem_insert.1 hd with rfl | hd
  · rw [show rootR = g2r from rfl, pinnedX_r_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _
  rcases Finset.mem_insert.1 hd with rfl | hd
  · rw [show rootU = g2u from rfl, pinnedX_u_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _
  rcases Finset.mem_insert.1 hd with rfl | hd
  · rw [show rootV = g2v from rfl, pinnedX_v_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _
  rcases Finset.mem_insert.1 hd with rfl | hd
  · rw [show rootB = g2b from rfl, pinnedX_b_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _
  rw [Finset.mem_singleton.1 hd, show rootC = g2c from rfl, pinnedX_c_eq_g2N]
  exact g2N_mem_posUnipotent _ _ _ _ _ _

theorem eq_rootX_c_of_commute
    {u : adjointGroup .G2 K} (hu : u ∈ posU K)
    (hr : u * rootX rootR 1 = rootX rootR 1 * u) (hv : u * rootX rootV 1 = rootX rootV 1 * u)
    (ha : u * rootX rootA 1 = rootX rootA 1 * u) : ∃ F : K, u = rootX rootC F := by
  obtain ⟨A, B, C, D, E, F, hN⟩ := exists_g2N_of_mem_posUnipotent (Subgroup.mem_subgroupOf.1 hu)
  refine ⟨F, Subtype.ext ?_⟩
  rw [coe_rootX, ← hN]
  refine g2N_eq_of_commute ?_ ?_ ?_
  · have := congrArg Subtype.val hr
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_rootX, ← hN] at this
  · have := congrArg Subtype.val hv
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_rootX, ← hN] at this
  · have := congrArg Subtype.val ha
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, coe_rootX, ← hN] at this

theorem g2N_mul_self_eq_iff
    {A B C D E F F₀ : K} (hF : F₀ ≠ 0) :
    g2N A B C D E F * g2N A B C D E F = X g2c F₀ ↔ A = 0 ∧ B * E + C * D = F₀ := by
  rw [g2N_mul_self, pinnedX_c_eq_g2N]
  constructor
  · intro h
    obtain ⟨-, -, h1, -, h3, h4⟩ := g2N_injective h
    by_cases hA : A = 0
    · subst hA
      refine ⟨rfl, ?_⟩
      linear_combination h4
    · exfalso
      have hB : B = 0 := (mul_eq_zero.1 h1).resolve_left hA
      subst hB
      have hD : D = A * C := by
        have h' : A * (A * C + D) = 0 := by linear_combination h3
        have := (mul_eq_zero.1 h').resolve_left hA
        linear_combination this - A * C * (CharTwo.two_eq_zero (R := K))
      subst hD
      apply hF
      linear_combination -h4 + A * C ^ 2 * (CharTwo.two_eq_zero (R := K))
  · rintro ⟨rfl, h⟩
    refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · linear_combination h

theorem card_sq_eq_rootX_c
    (hK : Nat.card K = 4) {F₀ : K} (hF : F₀ ≠ 0) :
    Nat.card {u : adjointGroup .G2 K // u ∈ posU K ∧ u * u = rootX rootC F₀} = 240 := by
  let f : {w : K × K × K × K // hyp w = F₀} × K →
      {u : adjointGroup .G2 K // u ∈ posU K ∧ u * u = rootX rootC F₀} := fun p =>
    ⟨⟨g2N 0 p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.2,
        posUnipotent_le_adjointGroup (g2N_mem_posUnipotent _ _ _ _ _ _)⟩,
      Subgroup.mem_subgroupOf.2 (g2N_mem_posUnipotent _ _ _ _ _ _), Subtype.ext (by
        rw [Subgroup.coe_mul, coe_rootX]
        exact (g2N_mul_self_eq_iff hF).2 ⟨rfl, p.1.2⟩)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun u => ?_⟩
    · have h := congrArg (fun x => ((x.1 : adjointGroup .G2 K) : ModGL .G2 K)) hpq
      obtain ⟨-, h1, h2, h3, h4, h5⟩ := g2N_injective h
      obtain ⟨⟨⟨B, C, D, E⟩, hw⟩, F⟩ := p
      obtain ⟨⟨⟨B', C', D', E'⟩, hw'⟩, F'⟩ := q
      simp only at h1 h2 h3 h4 h5
      subst h1 h2 h3 h4 h5
      rfl
    · obtain ⟨u, hu, hsq⟩ := u
      obtain ⟨A, B, C, D, E, F, hN⟩ :=
        exists_g2N_of_mem_posUnipotent (Subgroup.mem_subgroupOf.1 hu)
      have h := congrArg Subtype.val hsq
      rw [Subgroup.coe_mul, coe_rootX, ← hN] at h
      obtain ⟨rfl, hBE⟩ := (g2N_mul_self_eq_iff hF).1 h
      exact ⟨⟨⟨(B, C, D, E), hBE⟩, F⟩, Subtype.ext (Subtype.ext hN)⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, card_hyperbolic hK hF, hK]

theorem g2Conj_family_one
    [Finite K] {A : K} (hA : A ≠ 0) (C E F : K) :
    G2Conj (g2N A 0 C (A * C) E F) (X g2v 1) := by
  have hsqrt : ∀ y : K, ∃ r : K, r * r = y := fun y => by
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' y
    exact ⟨r, hr.symm⟩
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

theorem g2Conj_family_two
    {D : K} (hD : D ≠ 0) (E F : K) :
    G2Conj (g2N 0 0 0 D E F) (X g2v 1) := by
  refine (G2Conj.pinnedX g2r (E / D) _).trans (G2Conj.of_eq (conj_r _ _ _ _ _ _ _) ?_)
  refine G2Conj.of_eq (g2N_eq_g2N (C' := 0) (D' := D) (E' := 0) (F' := F) rfl rfl
    (by char2_ring) (by char2_ring) (by field_simp; char2_ring) (by char2_ring)) ?_
  refine (G2Conj.pinnedX g2u (F / D) _).trans (G2Conj.of_eq (conj_u _ _ _ _ _ _ _) ?_)
  exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by char2_ring)
    (by field_simp; char2_ring)).trans (pinnedX_v_eq_g2N D).symm) (G2Conj.v_one hD)

theorem g2Conj_family_three
    [Finite K] {C : K} (hC : C ≠ 0) (E F : K) :
    G2Conj (g2N 0 0 C 0 E F) (X g2v 1) := by
  have hsqrt : ∀ y : K, ∃ r : K, r * r = y := fun y => by
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' y
    exact ⟨r, hr.symm⟩
  obtain ⟨s, hs⟩ := hsqrt (E / C)
  refine (G2Conj.pinnedX g2r s _).trans (G2Conj.of_eq (conj_r _ _ _ _ _ _ _) ?_)
  refine G2Conj.of_eq (g2N_eq_g2N (C' := C) (D' := 0) (E' := 0) (F' := F + C ^ 2 * s) rfl rfl
    (by char2_ring) (by char2_ring)
    (by rw [show s ^ 2 = s * s from sq s, hs]; field_simp; char2_ring) (by char2_ring)) ?_
  refine (G2Conj.pinnedX g2v ((F + C ^ 2 * s) / C) _).trans
    (G2Conj.of_eq (conj_v _ _ _ _ _ _ _) ?_)
  exact G2Conj.of_eq ((g2N_eq_g2N rfl rfl rfl rfl (by char2_ring)
    (by field_simp; char2_ring)).trans (pinnedX_u_eq_g2N C).symm) (G2Conj.u_one hC)

omit [CharP K 2] in
theorem isConj_of_g2Conj {x y : adjointGroup .G2 K} (h : G2Conj (x : ModGL .G2 K) y) :
    IsConj x y := by
  obtain ⟨g, hg, hgxy⟩ := h
  exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using hgxy)⟩

theorem le_card_isConj_rootX_v
    (hK : Nat.card K = 4) :
    288 ≤ Nat.card {u : adjointGroup .G2 K // u ∈ posU K ∧ IsConj u (rootX rootV 1)} := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let T := {u : adjointGroup .G2 K // u ∈ posU K ∧ IsConj u (rootX rootV 1)}
  let coeT : T → ModGL .G2 K := fun x => ((x.1 : adjointGroup .G2 K) : ModGL .G2 K)
  let g₁ : Kˣ × K × K × K → T := fun p =>
    ⟨⟨g2N p.1 0 p.2.1 (p.1 * p.2.1) p.2.2.1 p.2.2.2,
        posUnipotent_le_adjointGroup (g2N_mem_posUnipotent _ _ _ _ _ _)⟩,
      Subgroup.mem_subgroupOf.2 (g2N_mem_posUnipotent _ _ _ _ _ _),
      isConj_of_g2Conj (g2Conj_family_one p.1.ne_zero _ _ _)⟩
  let g₂ : Kˣ × K × K → T := fun p =>
    ⟨⟨g2N 0 0 0 p.1 p.2.1 p.2.2, posUnipotent_le_adjointGroup (g2N_mem_posUnipotent _ _ _ _ _ _)⟩,
      Subgroup.mem_subgroupOf.2 (g2N_mem_posUnipotent _ _ _ _ _ _),
      isConj_of_g2Conj (g2Conj_family_two p.1.ne_zero _ _)⟩
  let g₃ : Kˣ × K × K → T := fun p =>
    ⟨⟨g2N 0 0 p.1 0 p.2.1 p.2.2, posUnipotent_le_adjointGroup (g2N_mem_posUnipotent _ _ _ _ _ _)⟩,
      Subgroup.mem_subgroupOf.2 (g2N_mem_posUnipotent _ _ _ _ _ _),
      isConj_of_g2Conj (g2Conj_family_three p.1.ne_zero _ _)⟩
  have h₁ : ∀ p : Kˣ × K × K × K,
      coeT (g₁ p) = g2N (p.1 : K) 0 p.2.1 (p.1 * p.2.1) p.2.2.1 p.2.2.2 := fun _ => rfl
  have h₂ : ∀ p : Kˣ × K × K, coeT (g₂ p) = g2N 0 0 0 (p.1 : K) p.2.1 p.2.2 := fun _ => rfl
  have h₃ : ∀ p : Kˣ × K × K, coeT (g₃ p) = g2N 0 0 (p.1 : K) 0 p.2.1 p.2.2 := fun _ => rfl
  have hg₁ : Function.Injective g₁ := fun p q h => by
    have h' := congrArg coeT h
    rw [h₁, h₁] at h'
    obtain ⟨hA, -, hC, -, hE, hF⟩ := g2N_injective h'
    exact Prod.ext (Units.ext hA) (Prod.ext hC (Prod.ext hE hF))
  have hg₂ : Function.Injective g₂ := fun p q h => by
    have h' := congrArg coeT h
    rw [h₂, h₂] at h'
    obtain ⟨-, -, -, hD, hE, hF⟩ := g2N_injective h'
    exact Prod.ext (Units.ext hD) (Prod.ext hE hF)
  have hg₃ : Function.Injective g₃ := fun p q h => by
    have h' := congrArg coeT h
    rw [h₃, h₃] at h'
    obtain ⟨-, -, hC, -, hE, hF⟩ := g2N_injective h'
    exact Prod.ext (Units.ext hC) (Prod.ext hE hF)
  have h₁₂ : ∀ a b, g₁ a ≠ g₂ b := fun a b h => by
    have h' := congrArg coeT h
    rw [h₁, h₂] at h'
    exact a.1.ne_zero (g2N_injective h').1
  have h₁₃ : ∀ a b, g₁ a ≠ g₃ b := fun a b h => by
    have h' := congrArg coeT h
    rw [h₁, h₃] at h'
    exact a.1.ne_zero (g2N_injective h').1
  have h₂₃ : ∀ a b, g₂ a ≠ g₃ b := fun a b h => by
    have h' := congrArg coeT h
    rw [h₂, h₃] at h'
    exact a.1.ne_zero (g2N_injective h').2.2.2.1
  have hf : Function.Injective (Sum.elim g₁ (Sum.elim g₂ g₃)) :=
    hg₁.sumElim (hg₂.sumElim hg₃ h₂₃) fun a b => by
      rcases b with b | b
      exacts [h₁₂ a b, h₁₃ a b]
  have hcard : Nat.card ((Kˣ × K × K × K) ⊕ (Kˣ × K × K) ⊕ (Kˣ × K × K)) = 288 := by
    simp [Nat.card_sum, Nat.card_prod, Nat.card_units, hK]
  rw [← hcard]
  exact Nat.card_le_card_of_injective _ hf

end CFSG.EvenSmallLie.GTwoFour
