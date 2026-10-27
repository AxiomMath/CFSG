module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionFiveMain
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma38

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

structure FieldHyps (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (t g : G) : Prop where
  mem : t ∈ Subgroup.normalizer (D : Set G)
  two : orderOf t = 2
  not_mem : g ∉ Subgroup.normalizer (D : Set G)
  cent : ∃ j : Fin r, aschbacherThm5Centralizes (aschbacherThm5Core D)
    (aschbacherThm5Preimage D (Abar j)) (g * t * g⁻¹)
  norm : ∀ k : Fin r, (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj t).toMonoidHom =
    aschbacherThm5Preimage D (Abar k)

omit [Finite G] in
theorem rightConjugate_rightConjugate_inv (Q : Subgroup G) (g : G) :
    rightConjugate (rightConjugate Q g) g⁻¹ = Q := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

omit [Finite G] in
theorem preimage_conjFactors_inv (g : G) (k : Fin r) :
    aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k) =
      aschbacherThm5Preimage D (Abar k) := by
  rw [preimage_conjFactors, preimage_conjFactors, rightConjugate_rightConjugate_inv]

omit [Finite G] in
theorem core_conj_inv (g : G) :
    aschbacherThm5Core (rightConjugate (rightConjugate D g) g⁻¹) = aschbacherThm5Core D := by
  rw [core_conj, core_conj, rightConjugate_rightConjugate_inv]

omit [Finite G] in
theorem centralizes_pow {A : Subgroup G} (hAD : A ≤ D) {y : G}
    (hy : y ∈ Subgroup.normalizer (D : Set G))
    (hyc : aschbacherThm5Centralizes (aschbacherThm5Core D) A y) (n : ℕ) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) A (y ^ n) := by
  induction n with
  | zero =>
    intro a _
    rw [pow_zero, inv_one, one_mul, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  | succ n ih =>
    rw [pow_succ]
    exact centralizes_mul hAD (Subgroup.pow_mem _ hy n) hy ih hyc

namespace FieldHyps

variable {t g : G}

theorem hyp71 (hC : Counterexample G D r Abar) (hF : FieldHyps D Abar t g) : Hyp71 D t g :=
  hyp71_of_field_hyps hC hF.mem hF.two hF.not_mem hF.cent

theorem r_eq_two (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    (hF : FieldHyps D Abar t g) : r = 2 :=
  (r_eq_two_and_rank hin hC (hF.hyp71 hC)).1

theorem two_le_pRank (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    (hF : FieldHyps D Abar t g) (k : Fin r) :
    2 ≤ CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar k)) :=
  (r_eq_two_and_rank hin hC (hF.hyp71 hC)).2 k

theorem not_centralizes_conj (hin : SectionSevenBase) (hC : Counterexample G D r Abar)
    (hF : FieldHyps D Abar t g) {k l : Fin r} {u : G}
    (hu : u ∈ aschbacherThm5Preimage D (Abar k)) (htwo : ∃ n : ℕ, u ^ (2 ^ n) = 1)
    (hu1 : u ≠ 1) :
    ¬ aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g l)) u := by
  intro hcent
  have hC' := hC.conj g
  have hN' := normalizer_rightConjugate D g
  obtain ⟨n, hn⟩ := htwo
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have hm1 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    exact hu1 hm
  set u₀ := u ^ (2 ^ (m - 1)) with hu₀
  have hu₀2 : orderOf u₀ = 2 := by
    rw [hu₀, orderOf_pow' u (pow_ne_zero _ two_ne_zero), hm]
    have h2 : 2 ^ m = 2 ^ (m - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm1)]
    rw [Nat.gcd_eq_right (by rw [h2]; exact Dvd.intro 2 rfl), h2,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hu₀A : u₀ ∈ aschbacherThm5Preimage D (Abar k) := Subgroup.pow_mem _ hu _
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu₀2
    omega
  have huN : u ∈ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) :=
    centralizer_le_of_centralizes hC' l ⟨n, hn⟩ hu1 hcent
      (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hcent₀ := centralizes_pow (preimage_le _ _) huN hcent (2 ^ (m - 1))
  have hCu₀ : Subgroup.centralizer ({u₀} : Set G) ≤
      rightConjugate (Subgroup.normalizer (D : Set G)) g :=
    hN' ▸ centralizer_le_of_centralizes hC' l (two_power_of_orderOf hu₀2) hu₀1 hcent₀
  have h2 := AschbacherKnownGroup.Lemma38.two_le_pRank_centralizer_involution
    (hF.two_le_pRank hin hC k) hu₀A (by rw [← hu₀2, pow_orderOf_eq_one])
  have h1 := pRank_le_one_of_conjugate hin hC hF.not_mem (X := aschbacherThm5Preimage D (Abar k) ⊓
      Subgroup.centralizer ({u₀} : Set G)) (inf_le_right.trans hCu₀)
    (fun x hx hx1 hx2 => centralizer_le_of_mem_factor hC hx.1 hx2 hx1)
  omega

theorem mirror (hC : Counterexample G D r Abar) (hF : FieldHyps D Abar t g) {i i' : Fin r}
    (hii' : i ≠ i') {c : G} (hci : c ∈ aschbacherThm5Preimage D (Abar i))
    (hc2 : orderOf c = 2) (hct : c * t = t * c)
    (hcnorm : ∀ k : Fin r,
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)).map
          (MulAut.conj c).toMonoidHom =
        aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k)) :
    FieldHyps (rightConjugate D g) (conjFactors D Abar g) c g⁻¹ where
  mem := by
    rw [normalizer_rightConjugate]
    exact (hF.hyp71 hC).centralizer_le (Subgroup.mem_centralizer_singleton_iff.mpr hct)
  two := hc2
  not_mem := by
    rw [normalizer_rightConjugate, mem_rightConjugate_iff, mul_inv_cancel, one_mul]
    intro h
    exact hF.not_mem (by simpa using (Subgroup.normalizer (D : Set G)).inv_mem h)
  cent := by
    refine ⟨i', (centralizes_conj_iff D Abar g i' _).mpr ?_⟩
    have he : g * (g⁻¹ * c * g⁻¹⁻¹) * g⁻¹ = c := by group
    rw [he]
    exact cross_factor_centralizes D Abar hC.hyp.hcomm i' i hii'.symm c hci
  norm := hcnorm

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour
