module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic
public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.RankThree.PartOne.K128.D4Arith
public import CFSG.RankThree.PartOne.KE8F.MultiStab
public import CFSG.RankThree.PartOne.KEXC.TorusParam
public import CFSG.RankThree.PartOne.KF4.B2Native
public import CFSG.RankThree.PartOne.KLC.TwistedTorusRank
public import CFSG.RankThree.PartOne.KLR.SL2Gen

public noncomputable section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KF4

section Z

variable {L : Type} [Field L]

@[expose] def charKer (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) : Subgroup (Fin ReeTag.F4.tag.rank → Lˣ) where
  carrier := {c | ∀ α ∈ S, rootChar c α = 1}
  mul_mem' := fun {a b} ha hb α hα => by
    rw [CTTorus.rootChar_mul, ha α hα, hb α hα, one_mul]
  one_mem' := fun α _ => CTTorus.rootChar_one α
  inv_mem' := fun {a} ha α hα => by
    have h := CTTorus.rootChar_mul a⁻¹ a α
    rw [inv_mul_cancel, CTTorus.rootChar_one, ha α hα, mul_one] at h
    exact h.symm

@[expose] def ZGrp (S : Set (Fin ReeTag.F4.tag.rank → ℤ)) : Subgroup (ModGL ReeTag.F4.tag L) :=
  (charKer (L := L) S).map (rootDiagUnitHom ReeTag.F4.tag L)

theorem mem_ZGrp {S : Set (Fin ReeTag.F4.tag.rank → ℤ)} {x : ModGL ReeTag.F4.tag L} :
    x ∈ ZGrp S ↔ ∃ c : Fin ReeTag.F4.tag.rank → Lˣ, (∀ α ∈ S, rootChar c α = 1) ∧
      rootDiagUnit ReeTag.F4.tag c = x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem mem_charKer_b2 {c : Fin ReeTag.F4.tag.rank → Lˣ} :
    c ∈ charKer (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support) ↔
      c (f4Index 1) = 1 ∧ c (f4Index 2) = 1 := by
  constructor
  · intro h
    have h1 := h (Pi.single (f4Index 1) 1) ⟨isRoot_single _ _, fun i hi => Pi.single_eq_of_ne
      (fun e => hi ((mem_f4B2Support _).2 (Or.inl e))) _⟩
    have h2 := h (Pi.single (f4Index 2) 1) ⟨isRoot_single _ _, fun i hi => Pi.single_eq_of_ne
      (fun e => hi ((mem_f4B2Support _).2 (Or.inr e))) _⟩
    exact ⟨(CTTorus.rootChar_single c _).symm.trans h1, (CTTorus.rootChar_single c _).symm.trans h2⟩
  · rintro ⟨h1, h2⟩ α ⟨-, hα⟩
    unfold rootChar
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i ∈ f4B2Support
    · rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [h1, one_zpow]
      · rw [h2, one_zpow]
    · rw [hα i hi, zpow_zero]

theorem cartan_f4_matrix : ∀ i j : Fin 4, Tag.F4.cartan i j =
    (![![2, -1, 0, 0], ![-1, 2, -1, 0], ![0, -2, 2, -1], ![0, 0, -1, 2]] :
      Fin 4 → Fin 4 → ℤ) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem prod_cartan_aux (t : Fin 4 → Lˣ) (h0 : t 0 = 1) (h3 : t 3 = 1) :
    (∏ j : Fin 4, t j ^ Tag.F4.cartan j (1 : Fin 4)) = t 1 ^ (2 : ℤ) * t 2 ^ (-2 : ℤ) ∧
    (∏ j : Fin 4, t j ^ Tag.F4.cartan j (2 : Fin 4)) = t 1 ^ (-1 : ℤ) * t 2 ^ (2 : ℤ) := by
  simp only [cartan_f4_matrix]
  simp [Fin.prod_univ_four, h0, h3]

theorem cartan_f4_vals : ∀ l : Fin 4,
    Tag.F4.cartan (f4Index 1) l = (![-1, 2, -1, 0] : Fin 4 → ℤ) l ∧
    Tag.F4.cartan (f4Index 2) l = (![0, -2, 2, -1] : Fin 4 → ℤ) l := by
  intro l
  fin_cases l <;> constructor <;> decide

theorem torus2Elt_eq_rootDiagUnit (s₁ s₂ : Lˣ) :
    torus2Elt (f4Index 1) (f4Index 2) s₁ s₂ = rootDiagUnit ReeTag.F4.tag
      (![s₁ ^ (-1 : ℤ), s₁ ^ (2 : ℤ) * s₂ ^ (-2 : ℤ), s₁ ^ (-1 : ℤ) * s₂ ^ (2 : ℤ),
        s₂ ^ (-1 : ℤ)] : Fin 4 → Lˣ) := by
  rw [torus2Elt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  refine funext fun (l : Fin 4) => ?_
  show s₁ ^ Tag.F4.cartan (f4Index 1) l * s₂ ^ Tag.F4.cartan (f4Index 2) l = _
  rw [(cartan_f4_vals l).1, (cartan_f4_vals l).2]
  fin_cases l <;> simp

theorem exists_unit_sq [IsAlgClosed L] (x : Lˣ) : ∃ y : Lˣ, y ^ 2 = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : L) (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
    exact x.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

theorem unit_cancel_aux1 (r d : Lˣ) :
    r ^ 2 * ((r ^ 2 * d) ^ 2 * (r * d) ^ (-2 : ℤ))⁻¹ = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
  module

theorem unit_cancel_aux2 (r d : Lˣ) :
    d * ((r ^ 2 * d) ^ (-1 : ℤ) * (r * d) ^ 2)⁻¹ = 1 := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
  module

theorem rootDiagUnit_eq_mul_ZGrp_b2 [IsAlgClosed L] (c : Fin ReeTag.F4.tag.rank → Lˣ) :
    ∃ z ∈ ZGrp (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support),
      ∃ q ∈ subsystemGroup ReeTag.F4.tag L f4B2Support,
        rootDiagUnit ReeTag.F4.tag c = z * q := by
  obtain ⟨r, hr⟩ := exists_unit_sq (c (f4Index 1))
  set s₁ : Lˣ := c (f4Index 1) * c (f4Index 2) with hs₁
  set s₂ : Lˣ := r * c (f4Index 2) with hs₂
  set t : Fin ReeTag.F4.tag.rank → Lˣ :=
    (![s₁ ^ (-1 : ℤ), s₁ ^ (2 : ℤ) * s₂ ^ (-2 : ℤ), s₁ ^ (-1 : ℤ) * s₂ ^ (2 : ℤ),
        s₂ ^ (-1 : ℤ)] : Fin 4 → Lˣ) with ht
  refine ⟨rootDiagUnit ReeTag.F4.tag (c * t⁻¹), ?_, torus2Elt (f4Index 1) (f4Index 2) s₁ s₂,
    torus2Elt_mem_f4B2 s₁ s₂, ?_⟩
  · refine mem_ZGrp.2 ⟨c * t⁻¹, mem_charKer_b2.2 ⟨?_, ?_⟩, rfl⟩
    · show c (f4Index 1) * (s₁ ^ (2 : ℤ) * s₂ ^ (-2 : ℤ))⁻¹ = 1
      rw [hs₁, hs₂, ← hr]
      exact_mod_cast unit_cancel_aux1 r (c (f4Index 2))
    · show c (f4Index 2) * (s₁ ^ (-1 : ℤ) * s₂ ^ (2 : ℤ))⁻¹ = 1
      rw [hs₁, hs₂, ← hr]
      exact_mod_cast unit_cancel_aux2 r (c (f4Index 2))
  · have e := torus2Elt_eq_rootDiagUnit (L := L) s₁ s₂
    calc rootDiagUnit ReeTag.F4.tag c =
        rootDiagUnit ReeTag.F4.tag (c * t⁻¹) * rootDiagUnit ReeTag.F4.tag t := by
          rw [← rootDiagUnit_mul]
          congr 1
          funext l
          simp
      _ = _ := congrArg _ e.symm

theorem unit_sq_eq_one_charTwo [CharP L 2] {x : Lˣ} (hx : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have h1 : ((x : L) - 1) ^ 2 = 0 := by
    have : (x : L) ^ 2 = 1 := by simpa using congrArg Units.val hx
    linear_combination this + (1 - (x : L)) * h2
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

theorem ZGrp_inf_subsystemGroup_b2 [CharP L 2] [IsAlgClosed L] :
    ZGrp (L := L) (parabolicRoots ReeTag.F4.tag f4B2Support) ⊓
      subsystemGroup ReeTag.F4.tag L f4B2Support = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨hz, hq⟩
  obtain ⟨e, he, rfl⟩ := mem_ZGrp.1 hz
  obtain ⟨he1, he2⟩ := mem_charKer_b2.1 he
  have hH : rootDiagUnit ReeTag.F4.tag e ∈ torusGroup ReeTag.F4.tag L :=
    rootDiagUnit_mem_torusGroup e
  have hT : rootDiagUnit Tag.F4 e ∈ subsystemTorus Tag.F4 L f4B2Support := by
    have h := subsystemGroup_inf_torusGroup (τ := Tag.F4) (K := L) (A := f4B2Support)
    have hmem : rootDiagUnit Tag.F4 e ∈ subsystemGroup Tag.F4 L f4B2Support ⊓ torusGroup Tag.F4 L :=
      ⟨hq, hH⟩
    rwa [h] at hmem
  obtain ⟨s, ⟨hs, hprod⟩, -⟩ := existsUnique_subsystemTorus_coords_F4 (M := L) (J := f4B2Support) hT
  have hcart : e = cartanChar s := by
    apply rootDiagUnit_injective (τ := Tag.F4) (K := L)
    rw [hprod, List.ofFn_eq_map, list_prod_torusElt_eq_rootDiagUnit]
  have hs0 : s (f4Index 0) = 1 := hs _ (fun h => by
    rcases (mem_f4B2Support _).1 h with h | h <;> exact absurd (congrArg Fin.val h) (by simp [f4Index]))
  have hs3 : s (f4Index 3) = 1 := hs _ (fun h => by
    rcases (mem_f4B2Support _).1 h with h | h <;> exact absurd (congrArg Fin.val h) (by simp [f4Index]))
  have e1 : e (f4Index 1) = s (f4Index 1) ^ (2 : ℤ) * s (f4Index 2) ^ (-2 : ℤ) := by
    rw [hcart]
    exact (prod_cartan_aux s hs0 hs3).1
  have e2 : e (f4Index 2) = s (f4Index 1) ^ (-1 : ℤ) * s (f4Index 2) ^ (2 : ℤ) := by
    rw [hcart]
    exact (prod_cartan_aux s hs0 hs3).2
  rw [he1] at e1
  rw [he2] at e2
  have h1 : s (f4Index 1) ^ (2 : ℤ) * s (f4Index 2) ^ (-2 : ℤ) = 1 := e1.symm
  have h2 : s (f4Index 1) ^ (-1 : ℤ) * s (f4Index 2) ^ (2 : ℤ) = 1 := e2.symm
  have hsq : s (f4Index 2) ^ 2 = 1 := by
    have e : s (f4Index 2) ^ 2 = (s (f4Index 1) ^ (2 : ℤ) * s (f4Index 2) ^ (-2 : ℤ)) *
        (s (f4Index 1) ^ (-1 : ℤ) * s (f4Index 2) ^ (2 : ℤ)) ^ 2 := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_pow]
      module
    rw [e, h1, h2]
    simp
  have hs2 : s (f4Index 2) = 1 := unit_sq_eq_one_charTwo hsq
  have hs1 : s (f4Index 1) = 1 := by
    rw [hs2] at h2
    simpa using h2
  have hall : ∀ i, s i = 1 := by
    intro i
    fin_cases i
    · exact hs0
    · exact hs1
    · exact hs2
    · exact hs3
  show rootDiagUnit ReeTag.F4.tag e = 1
  rw [hcart]
  have : s = 1 := funext hall
  rw [this]
  have hc1 : cartanChar (τ := ReeTag.F4.tag) (1 : Fin ReeTag.F4.tag.rank → Lˣ) = 1 := by
    funext l
    simp [cartanChar]
  exact (congrArg (rootDiagUnit ReeTag.F4.tag) hc1).trans rootDiagUnit_one

end Z
end CFSG.HardMathSupport.Malle.LocalAction
