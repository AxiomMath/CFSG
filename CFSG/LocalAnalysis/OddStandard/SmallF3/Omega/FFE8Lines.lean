module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Dim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8Eig
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalComponents

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma ffE8Lines_zsmul_eq_cast (x : V) (z : ℤ) :
    (z : ZMod 3) • x = z • x :=
  Int.cast_smul_eq_zsmul (R := ZMod 3) z x

private lemma ffE8Lines_vec_cast (k : Fin 4) :
    ((![1, -1, 1, -1] : Fin 4 → ℤ) k : ZMod 3) =
      (![1, -1, 1, -1] : Fin 4 → ZMod 3) k := by
  fin_cases k <;> decide

private lemma ffE8Lines_vec_cast' (k : Fin 4) :
    ((![1, 1, -1, -1] : Fin 4 → ℤ) k : ZMod 3) =
      (![1, 1, -1, -1] : Fin 4 → ZMod 3) k := by
  fin_cases k <;> decide

private lemma ffE8Lines_sign_sub_ne {k l : Fin 4} (h : k ≠ l) :
    (![1, -1, 1, -1] : Fin 4 → ZMod 3) l -
        (![1, -1, 1, -1] : Fin 4 → ZMod 3) k ≠ 0 ∨
      (![1, 1, -1, -1] : Fin 4 → ZMod 3) l -
        (![1, 1, -1, -1] : Fin 4 → ZMod 3) k ≠ 0 := by
  fin_cases k <;> fin_cases l <;>
    first
      | (exfalso; exact h rfl)
      | decide

private lemma ffE8Lines_sign_mul {k l : Fin 4} (h : k ≠ l) :
    (![1, -1, 1, -1] : Fin 4 → ZMod 3) k *
        (![1, -1, 1, -1] : Fin 4 → ZMod 3) l = -1 ∨
      (![1, 1, -1, -1] : Fin 4 → ZMod 3) k *
        (![1, 1, -1, -1] : Fin 4 → ZMod 3) l = -1 := by
  fin_cases k <;> fin_cases l <;>
    first
      | (exfalso; exact h rfl)
      | decide

private lemma ffE8Lines_polar_eq_zero {g : OGroup Q} {x y : V} {u v : ZMod 3}
    (huv : u * v = -1) (hx : (g : V ≃ₗ[ZMod 3] V) x = u • x)
    (hy : (g : V ≃ₗ[ZMod 3] V) y = v • y) :
    QuadraticMap.polar Q x y = 0 := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 x y
  rw [hx, hy, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right] at h1
  simp only [smul_eq_mul] at h1
  rw [← mul_assoc, huv, neg_one_mul] at h1
  have h2 : (2 : ZMod 3) * QuadraticMap.polar Q x y = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp h1.symm
  exact (mul_eq_zero.mp h2).resolve_left (by decide)

private lemma ffE8Lines_coeff_eq_zero {f : Fin 4 → V} (hli : LinearIndependent (ZMod 3) f)
    {g e : OGroup Q} {c : Fin 4 → ZMod 3} {k : Fin 4} {σ : Fin 4 → ZMod 3}
    (hc : ∑ l, c l • f l = (e : V ≃ₗ[ZMod 3] V) (f k))
    (hcomm : (g : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) (f k)) =
      (e : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (f k)))
    (hσ : ∀ l, (g : V ≃ₗ[ZMod 3] V) (f l) = σ l • f l) :
    ∀ l, c l * (σ l - σ k) = 0 := by
  have hL : (g : V ≃ₗ[ZMod 3] V) (∑ l, c l • f l) = ∑ l, (c l * σ l) • f l := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hσ l, smul_smul]
  have hR : (g : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) (f k)) =
      ∑ l, (σ k * c l) • f l := by
    rw [hcomm, hσ k, map_smul, ← hc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]
  have hkey : ∑ l, (c l * σ l) • f l = ∑ l, (σ k * c l) • f l := by rw [← hL, hc, hR]
  have hzero : ∑ l, (c l * σ l - σ k * c l) • f l = 0 := by
    have h1 : ∑ l, (c l * σ l - σ k * c l) • f l =
        ∑ l, ((c l * σ l) • f l - (σ k * c l) • f l) :=
      Finset.sum_congr rfl fun l _ => by rw [sub_smul]
    rw [h1, Finset.sum_sub_distrib, hkey, sub_self]
  intro l
  have hcoeff := (Fintype.linearIndependent_iff.mp hli)
    (fun l => c l * σ l - σ k * c l) hzero l
  rw [mul_sub, mul_comm (c l) (σ k)]
  exact hcoeff

theorem ffE8Lines_exists (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {E : Subgroup (OGroup Q)} {t ν : OGroup Q} (h : FFE8VData hQ E t ν) :
    ∃ (a b : V) (f : Fin 4 → V) (e₁ e₂ : OGroup Q), e₁ ∈ E ∧ e₂ ∈ E ∧
      a ∈ fixSp t ∧ b ∈ fixSp t ∧ Q a = 1 ∧ Q b = -1 ∧ QuadraticMap.polar Q a b = 0 ∧
      (∀ v ∈ fixSp t, ∃ x y : ZMod 3, v = x • a + y • b) ∧
      (∀ k, f k ∈ commSp t ∧ Q (f k) ≠ 0) ∧
      (∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0) ∧
      LinearIndependent (ZMod 3) f ∧ Submodule.span (ZMod 3) (Set.range f) = commSp t ∧
      (∀ k, (e₁ : V ≃ₗ[ZMod 3] V) (f k) = ![1, -1, 1, -1] k • f k) ∧
      (∀ k, (e₂ : V ≃ₗ[ZMod 3] V) (f k) = ![1, 1, -1, -1] k • f k) ∧
      (∀ e ∈ E, ∀ k, ∃ c : ZMod 3, (e : V ≃ₗ[ZMod 3] V) (f k) = c • f k) := by
  obtain ⟨a, b, ha_fix, hb_fix, hQa, hQb, hpolar_ab, hspan_ab⟩ :=
    ffE8Hyp_exists_ab hQ hdim hsgn h.t_sq h.t_dim h.t_sign
  haveI : IsMulCommutative ↥E := h.elemAb.1.1
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (h.elemAb.1.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    simpa [pow_two] using h.elemAb.1.2 x hx
  have hEcard : (E : Set (OGroup Q)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card E = 8
    rw [h.elemAb.2]
    norm_num
  have hpair2 : ({1, t} : Set (OGroup Q)).ncard ≤ 2 := by
    calc ({1, t} : Set (OGroup Q)).ncard
        = (insert (1 : OGroup Q) ({t} : Set (OGroup Q))).ncard := rfl
      _ ≤ ({t} : Set (OGroup Q)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  have hex1 : ∃ e₁ : OGroup Q, e₁ ∈ E ∧ e₁ ≠ 1 ∧ e₁ ≠ t := by
    by_contra hc
    have hsub : (E : Set (OGroup Q)) ⊆ ({1, t} : Set (OGroup Q)) := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · have h2 : x = t := by
          by_contra h2
          exact hc ⟨x, hx, h1, h2⟩
        simp [h2]
    have hle := Set.ncard_le_ncard hsub
    rw [hEcard] at hle
    omega
  obtain ⟨e₁, he₁E, he₁ne1, he₁net⟩ := hex1
  have hpair4 : ({e₁, e₁ * t} : Set (OGroup Q)).ncard ≤ 2 := by
    calc ({e₁, e₁ * t} : Set (OGroup Q)).ncard
        = (insert e₁ ({e₁ * t} : Set (OGroup Q))).ncard := rfl
      _ ≤ ({e₁ * t} : Set (OGroup Q)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  have hfour : ({1, t, e₁, e₁ * t} : Set (OGroup Q)).ncard ≤ 4 := by
    calc ({1, t, e₁, e₁ * t} : Set (OGroup Q)).ncard
        = ({1, t} ∪ {e₁, e₁ * t} : Set (OGroup Q)).ncard := by
          congr 1
          ext x
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
          tauto
      _ ≤ ({1, t} : Set (OGroup Q)).ncard + ({e₁, e₁ * t} : Set (OGroup Q)).ncard :=
          Set.ncard_union_le _ _
      _ ≤ 4 := by omega
  have hex2 : ∃ e₂ : OGroup Q, e₂ ∈ E ∧ e₂ ≠ 1 ∧ e₂ ≠ t ∧ e₂ ≠ e₁ ∧ e₂ ≠ e₁ * t := by
    by_contra hc
    have hsub : (E : Set (OGroup Q)) ⊆ ({1, t, e₁, e₁ * t} : Set (OGroup Q)) := by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · by_cases h2 : x = t
        · simp [h2]
        · by_cases h3 : x = e₁
          · simp [h3]
          · have h4 : x = e₁ * t := by
              by_contra h4
              exact hc ⟨x, hx, h1, h2, h3, h4⟩
            simp [h4]
    have hle := Set.ncard_le_ncard hsub
    rw [hEcard] at hle
    omega
  obtain ⟨e₂, he₂E, he₂ne1, he₂net, he₂ne₁, he₂ne1t⟩ := hex2
  have he₁sq : e₁ * e₁ = 1 := hsq e₁ he₁E
  have he₂sq : e₂ * e₂ = 1 := hsq e₂ he₂E
  have he1e2_mem : e₁ * e₂ ∈ E := E.mul_mem he₁E he₂E
  have he1e2_ne1 : e₁ * e₂ ≠ 1 := by
    intro hh
    apply he₂ne₁
    have h2 : e₂ = e₁⁻¹ := by
      have := congrArg (fun x => e₁⁻¹ * x) hh
      simpa [← mul_assoc] using this
    calc e₂ = e₁⁻¹ := h2
      _ = e₁ := inv_eq_of_mul_eq_one_right he₁sq
  have he1e2_net : e₁ * e₂ ≠ t := by
    intro hh
    apply he₂ne1t
    have h2 : e₂ = e₁⁻¹ * t := by
      have := congrArg (fun x => e₁⁻¹ * x) hh
      simpa [← mul_assoc] using this
    calc e₂ = e₁⁻¹ * t := h2
      _ = e₁ * t := by rw [inv_eq_of_mul_eq_one_right he₁sq]
  have hd₁ : invDim e₁ = 2 := ffE8Dim_invDim hQ hdim hsgn h he₁E he₁ne1 he₁net
  have hd₂ : invDim e₂ = 2 := ffE8Dim_invDim hQ hdim hsgn h he₂E he₂ne1 he₂net
  have hd₃ : invDim (e₁ * e₂) = 2 :=
    ffE8Dim_invDim hQ hdim hsgn h he1e2_mem he1e2_ne1 he1e2_net
  have hle₁ : commSp e₁ ≤ commSp t := ffE8Dim_commSp_le hQ hdim hsgn h he₁E
  have hle₂ : commSp e₂ ≤ commSp t := ffE8Dim_commSp_le hQ hdim hsgn h he₂E
  have hle₃ : commSp (e₁ * e₂) ≤ commSp t := ffE8Dim_commSp_le hQ hdim hsgn h he1e2_mem
  obtain ⟨f, hfcomm, hfli, hfspan, hfe1, hfe2⟩ :=
    ffE8Eig_lines h.t_sq he₁sq he₂sq (hcommE t h.t_mem e₁ he₁E) (hcommE t h.t_mem e₂ he₂E)
      (hcommE e₁ he₁E e₂ he₂E) h.t_dim hd₁ hd₂ hd₃ hle₁ hle₂ hle₃
  have hfe1' : ∀ k, (e₁ : V ≃ₗ[ZMod 3] V) (f k) =
      (![1, -1, 1, -1] : Fin 4 → ZMod 3) k • f k := by
    intro k
    have h := hfe1 k
    rw [← ffE8Lines_zsmul_eq_cast (f k) ((![1, -1, 1, -1] : Fin 4 → ℤ) k)] at h
    rwa [ffE8Lines_vec_cast k] at h
  have hfe2' : ∀ k, (e₂ : V ≃ₗ[ZMod 3] V) (f k) =
      (![1, 1, -1, -1] : Fin 4 → ZMod 3) k • f k := by
    intro k
    have h := hfe2 k
    rw [← ffE8Lines_zsmul_eq_cast (f k) ((![1, 1, -1, -1] : Fin 4 → ℤ) k)] at h
    rwa [ffE8Lines_vec_cast' k] at h
  have horth : ∀ k l, k ≠ l → QuadraticMap.polar Q (f k) (f l) = 0 := by
    intro k l hkl
    rcases ffE8Lines_sign_mul hkl with hmul | hmul
    · exact ffE8Lines_polar_eq_zero hmul (hfe1' k) (hfe1' l)
    · exact ffE8Lines_polar_eq_zero hmul (hfe2' k) (hfe2' l)
  have hQfk : ∀ k, Q (f k) ≠ 0 := by
    intro k h0
    have hfk_mem : f k ∈ commSp t := (hfcomm k).1
    have hpol : ∀ w ∈ commSp t, QuadraticMap.polar Q (f k) w = 0 := by
      intro w hw
      have hw' : w ∈ Submodule.span (ZMod 3) (Set.range f) := by rwa [hfspan]
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hw'
      rw [← hc, ← QuadraticMap.polarBilin_apply_apply, map_sum]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [map_smul, QuadraticMap.polarBilin_apply_apply]
      by_cases hl : l = k
      · subst hl
        simp [QuadraticMap.polar_self, h0]
      · rw [horth k l (Ne.symm hl), smul_zero]
    have hrad : (⟨f k, hfk_mem⟩ : commSp t) ∈ (Q.restrict (commSp t)).radical := by
      rw [QuadraticMap.mem_radical_iff']
      refine ⟨?_, ?_⟩
      · rw [QuadraticMap.restrict_apply]; exact h0
      · intro n
        rw [QuadraticMap.restrict_apply, QuadraticMap.restrict_apply]
        change Q (f k + (n : V)) = Q (n : V)
        rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq Q (f k) (n : V), h0, zero_add,
          hpol (n : V) n.2, add_zero]
    have hbot := (nondegenerate_restrict_commSp hQ h.t_sq).radical_eq_bot
    rw [hbot, Submodule.mem_bot] at hrad
    exact (hfcomm k).2 (Subtype.ext_iff.mp hrad)
  have hscalar : ∀ e ∈ E, ∀ k : Fin 4, ∃ c : ZMod 3,
      (e : V ≃ₗ[ZMod 3] V) (f k) = c • f k := by
    intro e he k
    have hfk_mem : f k ∈ commSp t := (hfcomm k).1
    have htfk : (t : V ≃ₗ[ZMod 3] V) (f k) = -f k := (mem_commSp_iff h.t_sq).mp hfk_mem
    have hte' : (t : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) =
        (e : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) := by
      simpa only [Subgroup.coe_mul] using
        congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) (hcommE t h.t_mem e he)
    have hefk_mem : (e : V ≃ₗ[ZMod 3] V) (f k) ∈ commSp t := by
      rw [mem_commSp_iff h.t_sq]
      have h1 : (t : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) (f k)) =
          (e : V ≃ₗ[ZMod 3] V) ((t : V ≃ₗ[ZMod 3] V) (f k)) := by
        have := congrArg (fun (g : V ≃ₗ[ZMod 3] V) => g (f k)) hte'
        simpa only [LinearEquiv.mul_apply] using this
      rw [h1, htfk, map_neg]
    obtain ⟨c, hc⟩ :=
      (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp (by rw [hfspan]; exact hefk_mem)
    have hcomm1 : (e₁ : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) (f k)) =
        (e : V ≃ₗ[ZMod 3] V) ((e₁ : V ≃ₗ[ZMod 3] V) (f k)) := by
      have h' : (e₁ : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) =
          (e : V ≃ₗ[ZMod 3] V) * (e₁ : V ≃ₗ[ZMod 3] V) := by
        simpa only [Subgroup.coe_mul] using
          congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) (hcommE e₁ he₁E e he)
      have := congrArg (fun (g : V ≃ₗ[ZMod 3] V) => g (f k)) h'
      simpa only [LinearEquiv.mul_apply] using this
    have hcomm2 : (e₂ : V ≃ₗ[ZMod 3] V) ((e : V ≃ₗ[ZMod 3] V) (f k)) =
        (e : V ≃ₗ[ZMod 3] V) ((e₂ : V ≃ₗ[ZMod 3] V) (f k)) := by
      have h' : (e₂ : V ≃ₗ[ZMod 3] V) * (e : V ≃ₗ[ZMod 3] V) =
          (e : V ≃ₗ[ZMod 3] V) * (e₂ : V ≃ₗ[ZMod 3] V) := by
        simpa only [Subgroup.coe_mul] using
          congrArg (fun g : OGroup Q => (g : V ≃ₗ[ZMod 3] V)) (hcommE e₂ he₂E e he)
      have := congrArg (fun (g : V ≃ₗ[ZMod 3] V) => g (f k)) h'
      simpa only [LinearEquiv.mul_apply] using this
    have hc1 : ∀ l, c l * ((![1, -1, 1, -1] : Fin 4 → ZMod 3) l -
        (![1, -1, 1, -1] : Fin 4 → ZMod 3) k) = 0 :=
      ffE8Lines_coeff_eq_zero hfli hc hcomm1 (fun l => hfe1' l)
    have hc2 : ∀ l, c l * ((![1, 1, -1, -1] : Fin 4 → ZMod 3) l -
        (![1, 1, -1, -1] : Fin 4 → ZMod 3) k) = 0 :=
      ffE8Lines_coeff_eq_zero hfli hc hcomm2 (fun l => hfe2' l)
    refine ⟨c k, ?_⟩
    rw [← hc]
    refine Finset.sum_eq_single k (fun l _ hl => ?_)
      (fun hk => absurd (Finset.mem_univ k) hk)
    rcases ffE8Lines_sign_sub_ne (Ne.symm hl) with h1 | h1
    · rw [(mul_eq_zero.mp (hc1 l)).resolve_right h1, zero_smul]
    · rw [(mul_eq_zero.mp (hc2 l)).resolve_right h1, zero_smul]
  exact ⟨a, b, f, e₁, e₂, he₁E, he₂E, ha_fix, hb_fix, hQa, hQb, hpolar_ab, hspan_ab,
    fun k => ⟨(hfcomm k).1, hQfk k⟩, horth, hfli, hfspan, hfe1, hfe2, hscalar⟩

end CFSG.OddStandard.SmallF3.Omega