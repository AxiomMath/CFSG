module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionSymmetric

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix MatrixExtension

theorem stab_eq_mul : ∀ a b c d e f : ZMod 2, c * f + d * e = 1 →
    (!![1, a, b; 0, c, d; 0, e, f] : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      !![1, a * f + b * e, a * d + b * c; 0, 1, 0; 0, 0, 1] * !![1, 0, 0; 0, c, d; 0, e, f] := by
  decide

theorem stab_unipotent_mul_self : ∀ x y : ZMod 2,
    (!![1, x, y; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      !![1, x, y; 0, 1, 0; 0, 0, 1] = 1 := by
  decide

theorem stab_levi_mul_self : ∀ c d e f : ZMod 2, c * f + d * e = 1 →
    ∃ s ∈ [(1 : Matrix (Fin 3) (Fin 3) (ZMod 2)), !![1, 0, 0; 0, 0, 1; 0, 1, 0]],
      (s * !![1, 0, 0; 0, c, d; 0, e, f]) * (s * !![1, 0, 0; 0, c, d; 0, e, f]) = 1 := by
  decide

theorem stab_fix : ∀ a b c d e f : ZMod 2,
    (!![1, a, b; 0, c, d; 0, e, f] : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 := by
  decide

theorem stab_det : ∀ a b c d e f : ZMod 2,
    (!![1, a, b; 0, c, d; 0, e, f] : Matrix (Fin 3) (Fin 3) (ZMod 2)).det ≠ 0 →
      c * f + d * e = 1 := by
  intro a b c d e f h
  rw [det_fin_three] at h
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
    cons_val_two, one_mul, zero_mul, mul_zero, ne_eq] at h
  revert h
  revert a b c d e f
  decide

@[expose] def involutionGL {m : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hm : m * m = 1) :
    GL (Fin 3) (ZMod 2) :=
  ⟨m, m, hm, hm⟩

theorem mem_closure_involutions {h : GL (Fin 3) (ZMod 2)}
    (hh : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    h ∈ Subgroup.closure {t : GL (Fin 3) (ZMod 2) |
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ t * t = 1} := by
  have hcol : ∀ i, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) i 0 = (Pi.single 0 1 : Fin 3 → ZMod 2) i :=
    fun i => by rw [← hh, mulVec_single_one, col_apply]
  have hmat : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      !![1, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2;
        0, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2;
        0, (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1,
          (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hcol]
  set a := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 1
  set b := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 0 2
  set c := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 1
  set d := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 2
  set e := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1
  set f := (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 2
  have hdet : c * f + d * e = 1 := by
    refine stab_det a b c d e f ?_
    rw [← hmat]
    exact ((isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  obtain ⟨s, hs, hsl⟩ := stab_levi_mul_self c d e f hdet
  have hss : s * s = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Matrix.mul_one 1
    · decide
  have hsfix : s *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact one_mulVec _
    · decide
  set n := !![1, a * f + b * e, a * d + b * c; 0, 1, 0; 0, 0, 1]
  set l : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, c, d; 0, e, f]
  have hn := stab_unipotent_mul_self (a * f + b * e) (a * d + b * c)
  have hfac : h = involutionGL hn * involutionGL hss * involutionGL hsl := by
    apply Units.ext
    simp only [Units.val_mul, involutionGL]
    rw [hmat, stab_eq_mul a b c d e f hdet, Matrix.mul_assoc, ← Matrix.mul_assoc s s, hss,
      Matrix.one_mul]
  have hmem : ∀ {m : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hm : m * m = 1),
      m *ᵥ Pi.single 0 1 = Pi.single 0 1 →
      involutionGL hm ∈ Subgroup.closure {t : GL (Fin 3) (ZMod 2) |
        (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 ∧ t * t = 1} :=
    fun hm hfix => Subgroup.subset_closure ⟨hfix, Units.ext hm⟩
  rw [hfac]
  refine mul_mem (mul_mem (hmem hn (stab_fix _ _ 1 0 0 1)) (hmem hss hsfix)) (hmem hsl ?_)
  rw [← mulVec_mulVec, stab_fix 0 0 c d e f, hsfix]

@[expose] def transMat (v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if v 0 = 1 then !![1, 0, 0; v 1, 1, 0; v 2, 0, 1]
  else if v 1 = 1 then !![0, 1, 0; 1, 0, 0; v 2, 0, 1] else !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def transMatInv (v : Fin 3 → ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  if v 0 = 1 then !![1, 0, 0; v 1, 1, 0; v 2, 0, 1]
  else if v 1 = 1 then !![0, 1, 0; 1, 0, 0; 0, v 2, 1] else !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem transMat_spec : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    transMat v * transMatInv v = 1 ∧ transMatInv v * transMat v = 1 ∧
      transMat v *ᵥ Pi.single 0 1 = v := by
  decide

theorem exists_mulVec_single_zero {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 2), (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = v := by
  obtain ⟨h₁, h₂, h₃⟩ := transMat_spec v hv
  exact ⟨⟨transMat v, transMatInv v, h₁, h₂⟩, h₃⟩

theorem sum_seven_vecMulVec :
    vecMulVec (Pi.single 0 1) (Pi.single 0 1) + vecMulVec (Pi.single 1 1) (Pi.single 1 1) +
      vecMulVec (Pi.single 2 1) (Pi.single 2 1) +
      vecMulVec (Pi.single 0 1 + Pi.single 1 1) (Pi.single 0 1 + Pi.single 1 1) +
      vecMulVec (Pi.single 0 1 + Pi.single 2 1) (Pi.single 0 1 + Pi.single 2 1) +
      vecMulVec (Pi.single 1 1 + Pi.single 2 1) (Pi.single 1 1 + Pi.single 2 1) +
      vecMulVec (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1)
        (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) =
      (0 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  decide

theorem vec_three_cases : ∀ v : Fin 3 → ZMod 2, v = 0 ∨ v = Pi.single 0 1 ∨ v = Pi.single 1 1 ∨
    v = Pi.single 2 1 ∨ v = Pi.single 0 1 + Pi.single 1 1 ∨ v = Pi.single 0 1 + Pi.single 2 1 ∨
    v = Pi.single 1 1 + Pi.single 2 1 ∨ v = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 := by
  decide

theorem seven_ne_zero :
    (Pi.single 0 1 : Fin 3 → ZMod 2) ≠ 0 ∧ (Pi.single 1 1 : Fin 3 → ZMod 2) ≠ 0 ∧
      (Pi.single 2 1 : Fin 3 → ZMod 2) ≠ 0 ∧
      (Pi.single 0 1 + Pi.single 1 1 : Fin 3 → ZMod 2) ≠ 0 ∧
      (Pi.single 0 1 + Pi.single 2 1 : Fin 3 → ZMod 2) ≠ 0 ∧
      (Pi.single 1 1 + Pi.single 2 1 : Fin 3 → ZMod 2) ≠ 0 ∧
      (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 : Fin 3 → ZMod 2) ≠ 0 := by
  decide

section Complement

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  {act : GL (Fin 3) (ZMod 2) →* AddMonoid.End M} {π : M →+ Matrix (Fin 3) (Fin 3) (ZMod 2)}

theorem mulVec_ne_zero (g : GL (Fin 3) (ZMod 2)) {v : Fin 3 → ZMod 2} (hv : v ≠ 0) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  rw [← one_mulVec v, ← Units.inv_mul g, ← mulVec_mulVec, h, mulVec_zero]

theorem sym_three_exists_invariant_complement
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * π x *
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hlift : ∀ X ∈ binarySymMatrices 3, ∃ x, π x = X)
    (hstab : ∀ x, π x = single 0 0 1 → ∀ g : GL (Fin 3) (ZMod 2),
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 → act g x = x) :
    ∃ S : AddSubgroup M, (∀ g, ∀ x ∈ S, act g x ∈ S) ∧ (∀ x ∈ S, π x = 0 → x = 0) ∧
      ∀ X ∈ binarySymMatrices 3, ∃ x ∈ S, π x = X := by
  classical
  obtain ⟨x₁, hx₁⟩ := hlift _ (single_mem_binarySymMatrices 0)
  choose! gv hgv using fun (v : Fin 3 → ZMod 2) (hv : v ≠ 0) => exists_mulVec_single_zero hv
  set s₀ : (Fin 3 → ZMod 2) → M := fun v => if v = 0 then 0 else act (gv v) x₁ with hs₀
  have hπs₀ : ∀ v, π (s₀ v) = vecMulVec v v := by
    intro v
    by_cases hv : v = 0
    · simp [hs₀, hv]
    · rw [hs₀]
      simp only [hv, ↓reduceIte]
      rw [hπact, hx₁, ← vecMulVec_single_single, mul_vecMulVec_mul_transpose, hgv v hv]
  have hs₀eq : ∀ (h : GL (Fin 3) (ZMod 2)) v,
      s₀ ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = act h (s₀ v) := by
    intro h v
    by_cases hv : v = 0
    · simp [hs₀, hv]
    have hv' := mulVec_ne_zero h hv
    simp only [hs₀, hv, hv', ↓reduceIte]
    have h₁' := hgv _ hv'
    generalize gv ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = g' at h₁' ⊢
    have h₂ := hgv v hv
    set k := g'⁻¹ * (h * gv v)
    have hk : (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
      simp only [k, Units.val_mul]
      rw [← mulVec_mulVec, ← mulVec_mulVec, h₂, ← h₁', mulVec_mulVec, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_mulVec]
    have hkx := hstab x₁ hx₁ k hk
    have hhk : h * gv v = g' * k := by
      simp only [k, mul_inv_cancel_left]
    rw [← act_mul_apply, hhk, act_mul_apply, hkx]
  set δ := s₀ (Pi.single 0 1) + s₀ (Pi.single 1 1) + s₀ (Pi.single 2 1) +
    s₀ (Pi.single 0 1 + Pi.single 1 1) + s₀ (Pi.single 0 1 + Pi.single 2 1) +
    s₀ (Pi.single 1 1 + Pi.single 2 1) + s₀ (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1)
    with hδ
  have hπδ : π δ = 0 := by
    simp only [hδ, map_add, hπs₀]
    exact sum_seven_vecMulVec
  have hδfix : ∀ h, act h δ = δ := fun h => hC h δ hπδ
  set s : (Fin 3 → ZMod 2) → M := fun v => if v = 0 then 0 else s₀ v + δ with hsdef
  have hs0 : s 0 = 0 := by simp [hsdef]
  have hsne : ∀ v, v ≠ 0 → s v = s₀ v + δ := fun v hv => by simp [hsdef, hv]
  have hπs : ∀ v, π (s v) = vecMulVec v v := by
    intro v
    by_cases hv : v = 0
    · simp [hsdef, hv]
    · rw [hsne v hv, map_add, hπs₀, hπδ, add_zero]
  have hseq : ∀ (h : GL (Fin 3) (ZMod 2)) v,
      s ((h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) = act h (s v) := by
    intro h v
    by_cases hv : v = 0
    · simp [hsdef, hv]
    · rw [hsne _ (mulVec_ne_zero h hv), hsne v hv, map_add, hs₀eq, hδfix]
  have hsum : s (Pi.single 0 1) + s (Pi.single 1 1) + s (Pi.single 2 1) +
      s (Pi.single 0 1 + Pi.single 1 1) + s (Pi.single 0 1 + Pi.single 2 1) +
      s (Pi.single 1 1 + Pi.single 2 1) + s (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) =
      0 := by
    obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆, n₇⟩ := seven_ne_zero
    rw [hsne _ n₁, hsne _ n₂, hsne _ n₃, hsne _ n₄, hsne _ n₅, hsne _ n₆, hsne _ n₇]
    have h8 : δ + δ + δ + δ + δ + δ + δ + δ = 0 := by
      have h2 : δ + δ = 0 := zmod_two_add_self δ
      rw [h2, zero_add, h2, zero_add, h2, zero_add, h2]
    rw [← h8, hδ]
    abel
  obtain ⟨d, hd⟩ : ∃ d : Fin 3 → M, ∀ i, d i = s (Pi.single i 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨o, ho⟩ : ∃ o : Fin 3 → Fin 3 → M, ∀ i j,
      o i j = s (Pi.single i 1 + Pi.single j 1) - s (Pi.single i 1) - s (Pi.single j 1) :=
    ⟨_, fun _ _ => rfl⟩
  have hos : ∀ i j, o i j = o j i := fun i j => by
    rw [ho, ho, add_comm (Pi.single i 1 : Fin 3 → ZMod 2) (Pi.single j 1)]
    abel
  have hπo : ∀ i j, π (o i j) = binaryOff i j := fun i j => by
    rw [ho, map_sub, map_sub, hπs, hπs, hπs, vecMulVec_single_add_single, vecMulVec_single_single,
      vecMulVec_single_single]
    abel
  have hπd : ∀ k, π (d k) = single k k 1 := fun k => by
    rw [hd, hπs, vecMulVec_single_single]
  obtain ⟨hinj, hsurj⟩ := symSection_closure_spec o d hos π hπo hπd
  set S := AddSubgroup.closure (Set.range fun p : Fin 3 × Fin 3 =>
    if p.1 = p.2 then d p.1 else o p.1 p.2) with hS
  have hdS : ∀ i, s (Pi.single i 1) ∈ S := fun i => by
    have h : (if (i, i).1 = (i, i).2 then d (i, i).1 else o (i, i).1 (i, i).2) ∈ S :=
      AddSubgroup.subset_closure ⟨(i, i), rfl⟩
    rwa [ite_eq_left rfl, hd] at h
  have hoS : ∀ i j, i ≠ j → o i j ∈ S := fun i j hij => by
    have h : (if (i, j).1 = (i, j).2 then d (i, j).1 else o (i, j).1 (i, j).2) ∈ S :=
      AddSubgroup.subset_closure ⟨(i, j), rfl⟩
    rwa [ite_eq_right hij] at h
  have hpair : ∀ i j, i ≠ j → s (Pi.single i 1 + Pi.single j 1) ∈ S := fun i j hij => by
    have h := add_mem (add_mem (hoS i j hij) (hdS j)) (hdS i)
    rwa [ho, sub_add_cancel, sub_add_cancel] at h
  have hsS : ∀ v, s v ∈ S := by
    intro v
    rcases vec_three_cases v with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hs0]
      exact zero_mem _
    · exact hdS 0
    · exact hdS 1
    · exact hdS 2
    · exact hpair 0 1 (by decide)
    · exact hpair 0 2 (by decide)
    · exact hpair 1 2 (by decide)
    · have h : s (Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1) =
          -(s (Pi.single 0 1) + s (Pi.single 1 1) + s (Pi.single 2 1) +
            s (Pi.single 0 1 + Pi.single 1 1) + s (Pi.single 0 1 + Pi.single 2 1) +
            s (Pi.single 1 1 + Pi.single 2 1)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hsum
      rw [h]
      refine neg_mem (add_mem (add_mem (add_mem (add_mem (add_mem (hdS 0) (hdS 1)) (hdS 2))
        (hpair 0 1 (by decide))) (hpair 0 2 (by decide))) (hpair 1 2 (by decide)))
  refine ⟨S, fun g x hx => ?_, hinj, hsurj⟩
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨i, j⟩, rfl⟩ := hy
    dsimp only
    split_ifs with hij
    · rw [hd, ← hseq]
      exact hsS _
    · rw [ho, map_sub, map_sub, ← hseq, ← hseq, ← hseq]
      exact sub_mem (sub_mem (hsS _) (hsS _)) (hsS _)
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | neg y _ hy => rw [map_neg]; exact neg_mem hy

end Complement

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
