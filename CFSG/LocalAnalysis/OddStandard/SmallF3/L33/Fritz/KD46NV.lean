module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46ND
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NV

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

structure Pre6 (H : Hyp S R) where
  S₁ : Subgroup X
  isPGroup : IsPGroup 2 S₁
  le : S₁ ≤ normalizer (I.E : Set X)
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → S₁ ≤ Q → Q ≤ normalizer (I.E : Set X) → Q = S₁
  T₁_le : R ≤ S₁
  card : Nat.card S₁ = 256
  inf_C : S₁ ⊓ centralizer (I.E : Set X) = I.E
  d : X
  d_mat : I.Mat d dCols
  d_Q₁ : d ∈ normalizer ((S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X)
  d_pow : ∃ a : ℕ, d ^ (3 ^ a) = 1
  d_inv : I.ui * d * I.ui⁻¹ = d⁻¹

theorem exists_pre6 (H : Hyp S R) : Nonempty (I.Pre6 H) := by
  obtain ⟨S₁, hp, hN, hmax, hTS, hcard, hC⟩ := I.exists_S₁ H
  obtain ⟨d, hd, hdQ, hpow, hinv⟩ := I.exists_d₁₁ H hTS hN hcard hC
  exact ⟨⟨S₁, hp, hN, hmax, hTS, hcard, hC, d, hd, hdQ, hpow, hinv⟩⟩

variable {I} {H : Hyp S R} (P : I.Pre6 H)

namespace Pre6

@[expose] noncomputable def Q₁ : Subgroup X := P.S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X))

theorem Q₁_le_S₁ : P.Q₁ ≤ P.S₁ := inf_le_left

theorem Q₁_le_N : P.Q₁ ≤ normalizer (I.E : Set X) := P.Q₁_le_S₁.trans P.le

theorem isPGroup_Q₁ : IsPGroup 2 P.Q₁ := P.isPGroup.to_le P.Q₁_le_S₁

theorem card_Q₁ : Nat.card P.Q₁ = 128 := (I.Q₁_props H P.le P.card P.inf_C).1

theorem Q₁_inf_C : P.Q₁ ⊓ centralizer (I.E : Set X) = I.E := (I.Q₁_props H P.le P.card P.inf_C).2.1

theorem E_le_Q₁ : I.E ≤ P.Q₁ := fun e he => by
  have : e ∈ P.Q₁ ⊓ centralizer (I.E : Set X) := by rw [P.Q₁_inf_C]; exact he
  exact this.1

theorem mem_E_of_mem_Q₁ {q : X} (hq : q ∈ P.Q₁) (hqC : q ∈ centralizer (I.E : Set X)) :
    q ∈ I.E := by
  rw [← P.Q₁_inf_C]; exact ⟨hq, hqC⟩

theorem d_mem_Q₁ {q : X} (hq : q ∈ P.Q₁) : P.d * q * P.d⁻¹ ∈ P.Q₁ :=
  (mem_normalizer_iff.mp P.d_Q₁ q).mp hq

theorem conj_mem_Q₁ {s q : X} (hs : s ∈ P.S₁) (hq : q ∈ P.Q₁) : s * q * s⁻¹ ∈ P.Q₁ :=
  mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hq).1) (inv_mem hs),
    conj_mem_oddTwoCoreIn' (P.le hs) (mem_inf.mp hq).2⟩

theorem S₁_le_normalizer_Q₁ : P.S₁ ≤ normalizer (P.Q₁ : Set X) := fun _ hs =>
  mem_normalizer_of_conj_mem fun _ hq => P.conj_mem_Q₁ hs hq

theorem mem_Q₁_of_Mat {s : X} (hs : s ∈ P.S₁) {c : Fin 4 → V4} (hc : I.Mat s c)
    (htr : ∀ j, blk (lin c (pt j)) = j + blk (lin c (pt 0))) : s ∈ P.Q₁ := by
  refine ⟨hs, ?_⟩
  rw [I.oddTwoCoreIn_eq H]
  refine ⟨⟨s, hc.mem⟩, ?_, rfl⟩
  show I.blockHom H ⟨s, hc.mem⟩ ∈ transl
  intro j
  have hcols : (fun i => I.μ ⟨s, hc.mem⟩ (bas i)) = c := funext hc.2
  rw [I.blockHom_apply, I.blockHom_apply, I.μ_eq_lin, I.μ_eq_lin _ (pt 0), hcols]
  exact htr j

theorem exists_mem_Q₁ {n : X} {c : Fin 4 → V4} (hn : I.Mat n c)
    (htr : ∀ j, blk (lin c (pt j)) = j + blk (lin c (pt 0))) : ∃ q ∈ P.Q₁, I.Mat q c := by
  have hnK : n ∈ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) := by
    rw [I.oddTwoCoreIn_eq H]
    refine ⟨⟨n, hn.mem⟩, ?_, rfl⟩
    show I.blockHom H ⟨n, hn.mem⟩ ∈ transl
    intro j
    have hcols : (fun i => I.μ ⟨n, hn.mem⟩ (bas i)) = c := funext hn.2
    rw [I.blockHom_apply, I.blockHom_apply, I.μ_eq_lin, I.μ_eq_lin _ (pt 0), hcols]
    exact htr j
  obtain ⟨q, hq, hqn⟩ := (I.Q₁_props H P.le P.card P.inf_C).2.2 n hnK
  refine ⟨q, hq, ?_⟩
  have := hn.mul_central (inv_mem hqn)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at this

theorem d_mem_C_t : P.d ∈ centralizer ({t} : Set X) :=
  P.d_mat.mem_centralizer_t (by decide)

theorem exists_v : ∃ v ∈ R, I.Mat v vC ∧ v * P.d = P.d * v := by
  obtain ⟨ε, -, v₀, hv₀, -, -, -, -, hv₀c, -, -⟩ := I.exists_vww H
  have hv₀M : I.Mat v₀ vC := ⟨I.R_le H hv₀, hv₀c⟩
  have hv₀Q : v₀ ∈ P.Q₁ := P.mem_Q₁_of_Mat (P.T₁_le hv₀) hv₀M transl_vC
  set d := P.d with hd
  have hdM := P.d_mat
  have hE : ∀ {e : X}, e ∈ I.E → d * e * d⁻¹ ∈ I.E := fun he =>
    (mem_normalizer_iff.mp hdM.mem _).mp he
  have hE' : ∀ {e : X}, e ∈ I.E → d⁻¹ * e * d ∈ I.E := fun he => by
    have := (mem_normalizer_iff.mp (inv_mem hdM.mem) _).mp he
    simpa using this
  have he₀ : v₀⁻¹ * d * v₀ * d⁻¹ ∈ I.E := by
    refine P.mem_E_of_mem_Q₁ ?_ ?_
    · have := mul_mem (inv_mem hv₀Q) (P.d_mem_Q₁ hv₀Q)
      simpa [mul_assoc] using this
    · apply Mat.mem_centralizer
      have := ((hv₀M.inv vC_vC).mul hdM).mul hv₀M |>.mul (hdM.inv dCols_ddCols)
      rwa [show comp (comp (comp vC dCols) vC) ddCols = bas from funext vC_dCols] at this
  have he₁ : v₀⁻¹ * d⁻¹ * v₀ * d ∈ I.E := by
    have := hE' (inv_mem he₀)
    have e : d⁻¹ * (v₀⁻¹ * d * v₀ * d⁻¹)⁻¹ * d = v₀⁻¹ * d⁻¹ * v₀ * d := by group
    rwa [e] at this
  obtain ⟨a, ha⟩ := P.d_pow
  classical
  have : Fintype I.E := Fintype.ofFinite _
  let σ : Perm I.E :=
    { toFun := fun e => ⟨v₀⁻¹ * d * (v₀ * e) * d⁻¹, by
        have e' : v₀⁻¹ * d * (v₀ * e) * d⁻¹ = (v₀⁻¹ * d * v₀ * d⁻¹) * (d * e * d⁻¹) := by group
        rw [e']; exact mul_mem he₀ (hE e.2)⟩
      invFun := fun e => ⟨v₀⁻¹ * d⁻¹ * (v₀ * e) * d, by
        have e' : v₀⁻¹ * d⁻¹ * (v₀ * e) * d = (v₀⁻¹ * d⁻¹ * v₀ * d) * (d⁻¹ * e * d) := by group
        rw [e']; exact mul_mem he₁ (hE' e.2)⟩
      left_inv := fun e => Subtype.ext (by simp only; group)
      right_inv := fun e => Subtype.ext (by simp only; group) }
  have hσn : ∀ n : ℕ, ∀ e : I.E, ((σ ^ n) e : X) = v₀⁻¹ * d ^ n * (v₀ * e) * (d ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ, Perm.mul_apply, ih]
      show v₀⁻¹ * d ^ n * (v₀ * (v₀⁻¹ * d * (v₀ * e) * d⁻¹)) * (d ^ n)⁻¹ = _
      group
  have hσ : σ ^ 3 ^ a = 1 := by
    ext e
    rw [hσn, ha]
    simp
  have hcard : Fintype.card I.E = 16 := by
    rw [← Nat.card_eq_fintype_card, Inst.E, (KD46.card_E S) I.yi_mem I.yi_sq I.yi_not_mem_B]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e, he⟩ := Perm.exists_fixed_point_of_prime (p := 3) (n := a)
    (by rw [hcard]; norm_num) hσ
  have he' : v₀⁻¹ * d * (v₀ * e) * d⁻¹ = e := congrArg Subtype.val he
  refine ⟨v₀ * e, mul_mem hv₀ (H.le (I.E_le_TE e.2)), hv₀M.mul_central (I.E_le_centralizer e.2),
    ?_⟩
  calc v₀ * e * d = v₀ * (v₀⁻¹ * d * (v₀ * e) * d⁻¹) * d := by rw [he']
    _ = d * (v₀ * e) := by group

end Pre6

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
