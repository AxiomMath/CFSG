module

public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.ExactNormalFormE

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K : Type} [Field K]

theorem diagramMap_mul_rootDiagUnit
    {t : TwistTag} (b : Fin t.tag.rank → Kˣ) :
    diagramMap t K * rootDiagUnit t.tag b =
      rootDiagUnit t.tag (fun i => b (t.perm.symm i)) * diagramMap t K :=
  Units.ext (diagramMap_mul_rootDiag b)

theorem rootDiagUnit_conj_rootDiagUnit_mul_diagramMap
    {t : TwistTag} (c a : Fin t.tag.rank → Kˣ) :
    rootDiagUnit t.tag c * (rootDiagUnit t.tag a * diagramMap t K) * (rootDiagUnit t.tag c)⁻¹ =
      rootDiagUnit t.tag (fun i => c i * a i * (c (t.perm.symm i))⁻¹) * diagramMap t K := by
  rw [rootDiagUnit_inv, mul_assoc, mul_assoc, diagramMap_mul_rootDiagUnit, ← mul_assoc,
    ← mul_assoc, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

theorem weylElt_conj_rootDiagUnit
    {τ : Tag} (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      rootDiagUnit τ (fun j => a j * a i ^ (-τ.cartan i j)) := by
  have h := rootDiagUnit_conj_weylElt_one a i
  have h1 : rootDiagUnit τ a * weylElt τ K i 1 =
      torusElt τ K i (a i) * weylElt τ K i 1 * rootDiagUnit τ a := by
    calc rootDiagUnit τ a * weylElt τ K i 1 =
          (rootDiagUnit τ a * weylElt τ K i 1 * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by
          group
      _ = _ := by rw [h]
  have h2 : weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹ =
      (torusElt τ K i (a i))⁻¹ * rootDiagUnit τ a := by
    rw [eq_inv_mul_iff_mul_eq]
    calc torusElt τ K i (a i) * (weylElt τ K i 1 * rootDiagUnit τ a * (weylElt τ K i 1)⁻¹) =
          (torusElt τ K i (a i) * weylElt τ K i 1 * rootDiagUnit τ a) *
            (weylElt τ K i 1)⁻¹ := by group
      _ = rootDiagUnit τ a := by rw [← h1]; group
  rw [h2, torusElt_eq_rootDiagUnit, rootDiagUnit_inv, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, zpow_neg]
  rw [mul_comm]

theorem diagramMap_mul_weylElt_one
    {t : TwistTag} (i : Fin t.tag.rank) :
    diagramMap t K * weylElt t.tag K i 1 = weylElt t.tag K (t.perm i) 1 * diagramMap t K := by
  have h := twistHom_weylElt_one t K (RingHom.id K) i
  rw [← conj_diagramMap_eq_twistHom] at h
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [← h]
  group

theorem weylElt_conj_rootDiagUnit_mul_diagramMap
    {t : TwistTag} (a : Fin t.tag.rank → Kˣ)
    {i : Fin t.tag.rank} (hi : t.perm i = i) :
    weylElt t.tag K i 1 * (rootDiagUnit t.tag a * diagramMap t K) * (weylElt t.tag K i 1)⁻¹ =
      rootDiagUnit t.tag (fun j => a j * a i ^ (-t.tag.cartan i j)) * diagramMap t K := by
  have hP : weylElt t.tag K i 1 * diagramMap t K * (weylElt t.tag K i 1)⁻¹ = diagramMap t K := by
    have := diagramMap_mul_weylElt_one (K := K) i
    rw [hi] at this
    rw [← this]
    group
  calc weylElt t.tag K i 1 * (rootDiagUnit t.tag a * diagramMap t K) * (weylElt t.tag K i 1)⁻¹ =
        (weylElt t.tag K i 1 * rootDiagUnit t.tag a * (weylElt t.tag K i 1)⁻¹) *
          (weylElt t.tag K i 1 * diagramMap t K * (weylElt t.tag K i 1)⁻¹) := by group
    _ = _ := by rw [weylElt_conj_rootDiagUnit, hP]

theorem units_eq_one_or_neg_one_of_mul_self {u : Kˣ} (h : u * u = 1) : u = 1 ∨ u = -1 := by
  have h' : (u : K) * u = 1 := by rw [← Units.val_mul, h, Units.val_one]
  rcases mul_self_eq_one_iff.1 h' with h1 | h1
  · exact Or.inl (Units.ext h1)
  · exact Or.inr (Units.ext (by rw [h1, Units.val_neg, Units.val_one]))

theorem E6_cartan_row_one :
    ∀ j : Fin 6, Tag.E6.cartan (1 : Fin 6) j = (![0, 2, 0, -1, 0, 0] : Fin 6 → ℤ) j := by
  intro j
  fin_cases j <;> decide

theorem E6_cartan_row_three :
    ∀ j : Fin 6, Tag.E6.cartan (3 : Fin 6) j = (![0, -1, -1, 2, -1, 0] : Fin 6 → ℤ) j := by
  intro j
  fin_cases j <;> decide

theorem E6_perm_symm :
    ∀ i : Fin 6, TwistTag.E6.perm.symm i = (![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) i := by
  intro i
  fin_cases i <;> rfl

theorem E6_perm_one : TwistTag.E6.perm (1 : Fin 6) = (1 : Fin 6) := rfl

theorem E6_perm_three : TwistTag.E6.perm (3 : Fin 6) = (3 : Fin 6) := rfl

theorem E6_diagramMap_mul_rootDiagUnit
    (b : Fin 6 → Kˣ) :
    diagramMap TwistTag.E6 K * rootDiagUnit TwistTag.E6.tag b =
      rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => b (TwistTag.E6.perm.symm i)) *
        diagramMap TwistTag.E6 K :=
  diagramMap_mul_rootDiagUnit (t := TwistTag.E6) b

theorem E6_rootDiagUnit_mul (a b : Fin 6 → Kˣ) :
    rootDiagUnit TwistTag.E6.tag (a * b) =
      rootDiagUnit TwistTag.E6.tag a * rootDiagUnit TwistTag.E6.tag b :=
  rootDiagUnit_mul (τ := TwistTag.E6.tag) a b

theorem E6_rootDiagUnit_one : rootDiagUnit TwistTag.E6.tag (1 : Fin 6 → Kˣ) = 1 :=
  rootDiagUnit_one (τ := TwistTag.E6.tag)

theorem E6_rootDiagUnit_conj
    (c a : Fin 6 → Kˣ) :
    rootDiagUnit TwistTag.E6.tag c * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K) *
        (rootDiagUnit TwistTag.E6.tag c)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => c i * a i * (c (TwistTag.E6.perm.symm i))⁻¹) *
        diagramMap TwistTag.E6 K :=
  rootDiagUnit_conj_rootDiagUnit_mul_diagramMap (t := TwistTag.E6) c a

theorem E6_weylElt_conj
    (a : Fin 6 → Kˣ) {i : Fin 6} (hi : TwistTag.E6.perm i = i) :
    weylElt TwistTag.E6.tag K i 1 * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 K) *
        (weylElt TwistTag.E6.tag K i 1)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun j : Fin 6 => a j * a i ^ (-Tag.E6.cartan i j)) *
        diagramMap TwistTag.E6 K :=
  weylElt_conj_rootDiagUnit_mul_diagramMap (t := TwistTag.E6) a hi

theorem E6_toral_graph_involution_two_representatives
    (k : Type) [Field k] [IsAlgClosed k]
    (a : Fin TwistTag.E6.tag.rank → kˣ)
    (ha : (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    ∃ g ∈ adjointGroup TwistTag.E6.tag k,
      g * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) * g⁻¹ =
          diagramMap TwistTag.E6 k ∨
        g * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) * g⁻¹ =
          rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k := by
  suffices H : ∀ a : Fin 6 → kˣ,
      (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) ^ 2 = 1 →
      ∃ g ∈ adjointGroup TwistTag.E6.tag k,
        g * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) * g⁻¹ =
            diagramMap TwistTag.E6 k ∨
          g * (rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 k) * g⁻¹ =
            rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k from
    H a ha
  clear a ha
  intro a ha
  set P := diagramMap TwistTag.E6 k with hP
  let R : (Fin 6 → kˣ) → (Fin 6 → kˣ) → Prop := fun a a' =>
    ∃ g ∈ adjointGroup TwistTag.E6.tag k,
      g * (rootDiagUnit TwistTag.E6.tag a * P) * g⁻¹ = rootDiagUnit TwistTag.E6.tag a' * P
  have Rtrans : ∀ a a' a'', R a a' → R a' a'' → R a a'' := by
    rintro a a' a'' ⟨g, hg, h⟩ ⟨g', hg', h'⟩
    refine ⟨g' * g, mul_mem hg' hg, ?_⟩
    rw [← h', ← h]
    group
  have RC : ∀ a c a' : Fin 6 → kˣ,
      (∀ i, c i * a i * (c (TwistTag.E6.perm.symm i))⁻¹ = a' i) → R a a' := by
    intro a c a' h
    refine ⟨_, (exceptional_Lang_adjoint_diagonal_lift TwistTag.E6.tag k c).1,
      (E6_rootDiagUnit_conj c a).trans ?_⟩
    congr 2
    exact funext h
  have RN : ∀ (i : Fin 6) (a a' : Fin 6 → kˣ), TwistTag.E6.perm i = i →
      (∀ j, a j * a i ^ (-Tag.E6.cartan i j) = a' j) → R a a' := by
    intro i a a' hi h
    refine ⟨_, weylElt_mem_adjointGroup (τ := TwistTag.E6.tag) i 1,
      (E6_weylElt_conj a hi).trans ?_⟩
    congr 2
    exact funext h
  have hsq : ∀ i, a i * a (TwistTag.E6.perm.symm i) = 1 := by
    have e : (rootDiagUnit TwistTag.E6.tag a * P) ^ 2 =
        rootDiagUnit TwistTag.E6.tag (a * fun i : Fin 6 => a (TwistTag.E6.perm.symm i)) := by
      rw [sq, E6_rootDiagUnit_mul]
      calc rootDiagUnit TwistTag.E6.tag a * P * (rootDiagUnit TwistTag.E6.tag a * P) =
            rootDiagUnit TwistTag.E6.tag a * (P * rootDiagUnit TwistTag.E6.tag a) * P := by
            group
        _ = rootDiagUnit TwistTag.E6.tag a *
            (rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => a (TwistTag.E6.perm.symm i)) * P) *
              P := by
            rw [hP, E6_diagramMap_mul_rootDiagUnit]
        _ = rootDiagUnit TwistTag.E6.tag a *
            rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => a (TwistTag.E6.perm.symm i)) *
              (P * P) := by
            group
        _ = _ := by rw [hP, diagramMap_E6_mul_self, mul_one]
    rw [e, ← E6_rootDiagUnit_one] at ha
    exact congrFun (rootDiagUnit_injective ha)
  have h05 : a 0 * a 5 = 1 := by simpa [E6_perm_symm] using hsq 0
  have h11 : a 1 * a 1 = 1 := by simpa [E6_perm_symm] using hsq 1
  have h24 : a 2 * a 4 = 1 := by simpa [E6_perm_symm] using hsq 2
  have h33 : a 3 * a 3 = 1 := by simpa [E6_perm_symm] using hsq 3
  have hnorm : R a ![1, a 1, 1, a 3, 1, 1] := by
    refine RC a ![(a 0)⁻¹, 1, (a 2)⁻¹, 1, 1, 1] _ fun i => ?_
    fin_cases i <;> simp [E6_perm_symm]
    all_goals first
      | (rw [mul_comm]; exact h05)
      | (rw [mul_comm]; exact h24)
  suffices hfin : R a 1 ∨ R a ![1, -1, 1, 1, 1, 1] by
    rcases hfin with ⟨g, hg, h⟩ | ⟨g, hg, h⟩
    · exact ⟨g, hg, Or.inl (by rw [h, E6_rootDiagUnit_one, one_mul])⟩
    · exact ⟨g, hg, Or.inr h⟩
  have hone : (![1, 1, 1, 1, 1, 1] : Fin 6 → kˣ) = 1 := by
    funext i
    fin_cases i <;> rfl
  rcases units_eq_one_or_neg_one_of_mul_self h11 with hA | hA <;>
    rcases units_eq_one_or_neg_one_of_mul_self h33 with hB | hB <;> rw [hA, hB] at hnorm
  ·
    left
    rwa [hone] at hnorm
  ·
    right
    have h1 : R ![1, 1, 1, -1, 1, 1] ![1, -1, -1, -1, -1, 1] :=
      RN 3 _ _ E6_perm_three fun j => by fin_cases j <;> simp [E6_cartan_row_three]
    have h2 : R ![1, -1, -1, -1, -1, 1] ![1, -1, -1, 1, -1, 1] :=
      RN 1 _ _ E6_perm_one fun j => by fin_cases j <;> simp [E6_cartan_row_one]
    have h3 : R ![1, -1, -1, 1, -1, 1] ![1, -1, 1, 1, 1, 1] :=
      RC _ ![1, 1, -1, 1, 1, 1] _ fun i => by fin_cases i <;> simp [E6_perm_symm]
    exact Rtrans _ _ _ hnorm (Rtrans _ _ _ h1 (Rtrans _ _ _ h2 h3))
  ·
    right
    exact hnorm
  ·
    right
    refine Rtrans _ _ _ hnorm (RN 1 _ _ E6_perm_one fun j => ?_)
    fin_cases j <;> simp [E6_cartan_row_one]

end CFSG.LieType.Chevalley
