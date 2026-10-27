module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Regular
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

open Matrix

variable {F : Type} [Field F] [Finite F]

theorem charP_three (hF : Nat.card F = 9) : CharP F 3 := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hq⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, hF] at hq
  have hdvd : ringChar F ∣ 9 := by
    rw [hq]
    exact dvd_pow_self _ n.pos.ne'
  have h3 : ringChar F ∣ 3 ^ 2 := by simpa using hdvd
  have : ringChar F = 3 := by
    have := (Nat.Prime.dvd_of_dvd_pow hp h3)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this
  exact ringChar.eq_iff.mp this

noncomputable def frob (hF : Nat.card F = 9) : F →+* F :=
  haveI := charP_three hF
  haveI : ExpChar F 3 := ExpChar.prime Nat.prime_three
  frobenius F 3

theorem frob_apply (hF : Nat.card F = 9) (x : F) : frob hF x = x ^ 3 := by
  haveI := charP_three hF
  haveI : ExpChar F 3 := ExpChar.prime Nat.prime_three
  simp [frob, frobenius_def]

open CFSG.Assembly.LowTwoRank in
theorem mem_statedSU_iff (hF : Nat.card F = 9) (g : GL (Fin 3) F) :
    g ∈ StatedSU 3 3 F ↔ adj (frob hF) (g : Matrix (Fin 3) (Fin 3) F) * g = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have h := CFSG.LinearGroups.UnitaryThreeOverNine.coe_statedSU hF
  rw [← SetLike.mem_coe, h]
  have hadj : ∀ A : Matrix (Fin 3) (Fin 3) F, adj (frob hF) A = (A.map (· ^ 3))ᵀ := fun A => by
    have : (frob hF : F → F) = (· ^ 3) := funext (frob_apply hF)
    simp [adj, this]
  simp only [Set.mem_setOf_eq, hadj]

theorem poly_cube (hF : Nat.card F = 9) (ν : Matrix (Fin 3) (Fin 3) F) (hν3 : ν ^ 3 = 0)
    (a b c : F) :
    (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2) ^ 3 =
      (a ^ 3) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  haveI := charP_three hF
  have h3 : (3 : F) = 0 := by
    have := CharP.cast_eq_zero F 3
    simpa using this
  set m : Matrix (Fin 3) (Fin 3) F := a • (1 : Matrix (Fin 3) (Fin 3) F) + b • ν + c • ν ^ 2
  have e2 : m ^ 2 = (a * a) • (1 : Matrix (Fin 3) (Fin 3) F) + (a * b + b * a) • ν +
      (a * c + b * b + c * a) • ν ^ 2 := by
    rw [pow_two]
    exact poly_mul ν hν3 a b c a b c
  have e3 : m ^ 3 = ((a * a) * a) • (1 : Matrix (Fin 3) (Fin 3) F) +
      ((a * a) * b + (a * b + b * a) * a) • ν +
      ((a * a) * c + (a * b + b * a) * b + (a * c + b * b + c * a) * a) • ν ^ 2 := by
    rw [pow_succ, e2]
    exact poly_mul ν hν3 _ _ _ a b c
  rw [e3]
  have z1 : (a * a) * b + (a * b + b * a) * a = 0 := by
    linear_combination (a ^ 2 * b) * h3
  have z2 : (a * a) * c + (a * b + b * a) * b + (a * c + b * b + c * a) * a = 0 := by
    linear_combination (a ^ 2 * c + a * b ^ 2) * h3
  rw [z1, z2]
  simp [pow_succ, mul_assoc]

abbrev SU (F : Type) [Field F] : Subgroup (GL (Fin 3) F) := CFSG.Assembly.LowTwoRank.StatedSU 3 3 F

theorem card_zeros_le (p : Polynomial F) (hp : p.natDegree = 3) (s : Finset F)
    (h : ∀ x ∈ s, p.eval x = 0) : s.card ≤ 3 := by
  have hp0 : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (n := 0) (by omega)
  have := Polynomial.card_le_degree_of_subset_roots (p := p) (Z := s) (by
    intro x hx
    exact (Polynomial.mem_roots hp0).mpr (h x (Finset.mem_val.mp hx)))
  omega

theorem card_centralizer_regular_le (hF : Nat.card F = 9) (y : ↥(SU F))
    (hν3 : (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1) ^ 3 = 0)
    (hν2 : (((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1) ^ 2 ≠ 0) :
    Nat.card (Subgroup.centralizer ({y} : Set ↥(SU F))) ≤ 9 := by
  classical
  haveI := charP_three hF
  set σ : F →+* F := frob hF with hσdef
  set ν : Matrix (Fin 3) (Fin 3) F := ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - 1 with hν
  set C := Subgroup.centralizer ({y} : Set ↥(SU F)) with hC
  have hyU : adj σ ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := ((mem_statedSU_iff hF y.1).mp y.2).1
  have key : ∀ m : C, ∃ b c : F, (((m : ↥(SU F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 + b • ν + c • ν ^ 2 ∧ σ b = b ∧ c + σ c = b ^ 2 - b := by
    intro m
    set mm : Matrix (Fin 3) (Fin 3) F := (((m : ↥(SU F)) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    have hcomm' : y * (m : ↥(SU F)) = (m : ↥(SU F)) * y :=
      Subgroup.mem_centralizer_iff.mp m.2 y rfl
    have hcomm : mm * ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * mm := by
      have := congrArg (fun z : ↥(SU F) => ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hcomm'
      simpa using this.symm
    have hcommν : mm * ν = ν * mm := by
      rw [hν, mul_sub, sub_mul, hcomm]
      simp
    obtain ⟨a, b, c, hm⟩ := exists_poly_of_commute ν mm hν3 hν2 hcommν
    have hmem := (mem_statedSU_iff hF (m : ↥(SU F)).1).mp (m : ↥(SU F)).2
    have hmu : adj σ (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • (((y : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) - 1) + c • (((y : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) - 1) ^ 2) *
        (a • (1 : Matrix (Fin 3) (Fin 3) F) + b • (((y : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) - 1) + c • (((y : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) - 1) ^ 2) = 1 := by
      have h1 : adj σ mm * mm = 1 := hmem.1
      rw [← hν]
      rw [hm] at h1
      exact h1
    obtain ⟨r1, r2, r3⟩ := unitary_poly_relations σ _ hyU hν3 hν2 a b c hmu
    have hdet : mm.det = 1 := hmem.2
    haveI := Fintype.ofFinite F
    have hcube := poly_cube hF ν hν3 a b c
    have hmm3 : mm ^ 3 = (a ^ 3) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [hm]; exact hcube
    have h1 : a ^ 9 = 1 := by
      have := congrArg Matrix.det hmm3
      rw [Matrix.det_pow, hdet, Matrix.det_smul, Matrix.det_one] at this
      simpa [Fintype.card_fin, ← pow_mul] using this.symm
    have ha9 : a ^ 9 = a := by
      have := FiniteField.pow_card a
      rwa [← Nat.card_eq_fintype_card, hF] at this
    have ha : a = 1 := by rw [← ha9]; exact h1
    subst ha
    have hσ1 : σ 1 = 1 := map_one σ
    rw [hσ1] at r2 r3
    have hσb : σ b = b := by linear_combination -r2
    rw [hσb] at r3
    refine ⟨b, c, by rw [hm]; simp [hν], hσb, ?_⟩
    linear_combination r3
  choose fb fc hfb using key
  haveI : Fintype C := Fintype.ofFinite C
  have hσx : ∀ x : F, σ x = x ^ 3 := frob_apply hF
  have hinj : Function.Injective (fun m : C => (fb m, fc m)) := by
    intro m m' h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [(hfb m).1, (hfb m').1, h.1, h.2]
  have himg_b : (Finset.univ.image fb).card ≤ 3 := by
    apply card_zeros_le (Polynomial.X ^ 3 - Polynomial.X) (by compute_degree!)
    intro x hx
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hx
    have := (hfb m).2.1
    rw [hσx] at this
    simp [this]
  have hfiber : ∀ b ∈ Finset.univ.image fb,
      (Finset.univ.filter (fun m : C => fb m = b)).card ≤ 3 := by
    intro b hb
    have hinj' : Set.InjOn fc (Finset.univ.filter (fun m : C => fb m = b) : Set C) := by
      intro m hm m' hm' h
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hm hm'
      exact hinj (Prod.ext (hm.trans hm'.symm) h)
    rw [← Finset.card_image_of_injOn hinj']
    apply card_zeros_le (Polynomial.X ^ 3 + Polynomial.X - Polynomial.C (b ^ 2 - b))
      (by compute_degree!)
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
    have := (hfb m).2.2
    rw [hσx, hm] at this
    simp
    linear_combination this
  rw [Nat.card_eq_fintype_card]
  calc Fintype.card C = (Finset.univ : Finset C).card := Finset.card_univ.symm
    _ ≤ 3 * (Finset.univ.image fb).card := Finset.card_le_mul_card_image _ 3 hfiber
    _ ≤ 3 * 3 := by omega
    _ = 9 := by norm_num

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
