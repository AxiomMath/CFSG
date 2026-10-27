module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open Matrix

@[expose] def stabL {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) (u : Fin r → F) : Subgroup L where
  carrier := {l | (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u = u}
  mul_mem' {a b} ha hb := by
    show (Mat (a * b) : Matrix (Fin r) (Fin r) F) *ᵥ u = u
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    have hb' : (Mat b : Matrix (Fin r) (Fin r) F) *ᵥ u = u := hb
    have ha' : (Mat a : Matrix (Fin r) (Fin r) F) *ᵥ u = u := ha
    rw [hb', ha']
  one_mem' := by
    show (Mat 1 : Matrix (Fin r) (Fin r) F) *ᵥ u = u
    simp
  inv_mem' {a} ha := by
    have ha' : (Mat a : Matrix (Fin r) (Fin r) F) *ᵥ u = u := ha
    show (Mat a⁻¹ : Matrix (Fin r) (Fin r) F) *ᵥ u = u
    rw [map_inv]
    calc (((Mat a)⁻¹ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ u
        = (((Mat a)⁻¹ : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ
            ((Mat a : Matrix (Fin r) (Fin r) F) *ᵥ u) := by
          rw [ha']
      _ = u := by
          rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def PerfStab {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) : Prop :=
  ∀ u : Fin r → F, ⁅stabL Mat u, stabL Mat u⁆ = stabL Mat u

@[expose] def NatSchur {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) : Prop :=
  ∀ c : (Fin r → F) →+ (Fin r → F),
    (∀ (l : L) (u : Fin r → F),
      c ((Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) = (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ c u) →
    ∃ lam : F, ∀ u, c u = lam • u

@[expose] def NatOut {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) : Prop :=
  ∀ M : Matrix.GeneralLinearGroup (Fin r) F, M * M = 1 →
    (∀ l : L, ∃ l' : L, Mat l' = M * Mat l * M⁻¹) → ∃ l₀ : L, Mat l₀ = M

structure NatQuot {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : Type*) [Field F] (r : ℕ) where
  Mat : ↥L →* Matrix.GeneralLinearGroup (Fin r) F
  mat_inj : Function.Injective Mat
  I : Submodule (ZMod 2) V
  inv : ∀ l ∈ L, ∀ v ∈ I, ρ l v ∈ I
  π : ↥I →+ (Fin r → F)
  surj : Function.Surjective π
  equiv : ∀ (l : ↥L) (v : ↥I),
    π ⟨ρ l v, inv l l.2 v v.2⟩ = (Mat l : Matrix (Fin r) (Fin r) F) *ᵥ π v
  ker_iff : ∀ v : ↥I, π v = 0 ↔ ∀ l ∈ L, ρ l v = v

private lemma natq_rho_comm {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {c l : G} (hcl : c * l = l * c) (y : V) :
    ρ c (ρ l y) = ρ l (ρ c y) := by
  have h : (ρ c : V →ₗ[ZMod 2] V) * ρ l = ρ l * ρ c := by
    rw [← map_mul, hcl, map_mul]
  simpa only [Module.End.mul_apply] using congrArg (fun f : V →ₗ[ZMod 2] V => f y) h

private lemma natq_theta_add {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) (v : ↥N.I) (a b : ↥L)
    (hb : b ∈ stabL N.Mat (N.π v)) :
    ρ (a * b) v - v = (ρ a v - v) + (ρ b v - v) := by
  have hfix_b := N.equiv b v
  have h2b : (N.Mat b : Matrix (Fin r) (Fin r) F) *ᵥ N.π v = N.π v := hb
  rw [h2b] at hfix_b
  have hkerb : N.π (⟨ρ b v, N.inv b b.2 v v.2⟩ - v) = 0 := by
    rw [map_sub, hfix_b, sub_self]
  have hLfixb : ∀ l ∈ L, ρ l (ρ b v - v) = ρ b v - v := by
    intro l hl
    have := (N.ker_iff (⟨ρ b v, N.inv b b.2 v v.2⟩ - v)).mp hkerb l hl
    simpa using this
  have hcomm' : ρ a (ρ b v - v) = ρ b v - v := hLfixb a a.2
  calc ρ (a * b) v - v
      = ρ a (ρ b v) - v := by simp only [map_mul, Module.End.mul_apply]
    _ = ρ a ((ρ b v - v) + v) - v := by rw [sub_add_cancel]
    _ = (ρ a (ρ b v - v) + ρ a v) - v := by rw [map_add]
    _ = ((ρ b v - v) + ρ a v) - v := by rw [hcomm']
    _ = (ρ a v - v) + (ρ b v - v) := by abel

theorem NatQuot.rho_eq_of_mat_fixes {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    {r : ℕ} (N : NatQuot ρ L F r) (hperf : PerfStab N.Mat) (l : ↥L) (v : ↥N.I)
    (hl : (N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ N.π v = N.π v) : ρ l v = v := by
  have hlS : l ∈ stabL N.Mat (N.π v) := hl
  let θ : ↥(stabL N.Mat (N.π v)) →* Multiplicative V :=
    { toFun := fun s => Multiplicative.ofAdd (ρ (s : ↥L) v - v)
      map_one' := by
        rw [ofAdd_eq_one]
        simp
      map_mul' := by
        intro a b
        rw [← ofAdd_add]
        apply congrArg Multiplicative.ofAdd
        exact natq_theta_add N v a b b.2 }
  have : Group.IsPerfect ↥(stabL N.Mat (N.π v)) :=
    Subgroup.isPerfect_iff.mpr (hperf (N.π v))
  have hle : ⁅(⊤ : Subgroup ↥(stabL N.Mat (N.π v))), ⊤⁆ ≤ θ.ker :=
    Subgroup.commutator_le.mpr (fun a _ b _ => by
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _))
  have htop : ⁅(⊤ : Subgroup ↥(stabL N.Mat (N.π v))), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top
  have htop_le : ⊤ ≤ θ.ker := htop ▸ hle
  have hθ : θ ⟨l, hlS⟩ = 1 := MonoidHom.mem_ker.mp (htop_le (Subgroup.mem_top _))
  have hzero : ρ (l : ↥L) v - v = 0 := by
    change Multiplicative.ofAdd (ρ (l : ↥L) v - v) = 1 at hθ
    exact ofAdd_eq_one.mp hθ
  exact sub_eq_zero.mp hzero

theorem NatQuot.rho_eq_of_commute_sq {G : Type*} [Group G] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G} {F : Type*} [Field F]
    [CharP F 2] {r : ℕ} (N : NatQuot ρ L F r) (hS : NatSchur N.Mat)
    (hIcomm : ∀ v ∈ N.I, v ∈ Submodule.span (ZMod 2)
      {w | ∃ l ∈ L, ∃ x ∈ N.I, w = ρ l x - x})
    (c : G) (hc : ∀ l ∈ L, c * l = l * c) (hcI : ∀ v ∈ N.I, ρ c v ∈ N.I)
    (hc2 : ∀ v ∈ N.I, ρ c (ρ c v) = v) : ∀ v ∈ N.I, ρ c v = v := by
  intro v hv
  let ρcI : ↥N.I →+ ↥N.I :=
    { toFun := fun x => ⟨ρ c (x : V), hcI x x.2⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Submodule.coe_add]
        exact map_add (ρ c) (x : V) (y : V) }
  let g : ↥N.I →+ (Fin r → F) := N.π.comp ρcI
  have hg : N.π.ker ≤ g.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    change N.π (ρcI x) = 0
    apply (N.ker_iff (ρcI x)).mpr
    intro l hl
    have hxl : ρ l (x : V) = (x : V) := (N.ker_iff x).mp hx l hl
    have hcommx : ρ c (ρ l (x : V)) = ρ l (ρ c (x : V)) := natq_rho_comm (hc l hl) (x : V)
    change ρ l (ρ c (x : V)) = ρ c (x : V)
    rw [← hcommx, hxl]
  let ψ : (Fin r → F) →+ (Fin r → F) := (N.π.liftOfSurjective N.surj) ⟨g, hg⟩
  have hψ : ∀ x : ↥N.I, ψ (N.π x) = N.π ⟨ρ c (x : V), hcI x x.2⟩ := by
    intro x
    exact AddMonoidHom.liftOfRightInverse_comp_apply N.π (Function.surjInv N.surj)
      (Function.rightInverse_surjInv N.surj) ⟨g, hg⟩ x
  have hψ2 : ∀ u : Fin r → F, ψ (ψ u) = u := by
    intro u
    obtain ⟨x, rfl⟩ := N.surj u
    rw [hψ, hψ]
    apply congrArg N.π
    apply Subtype.ext
    exact hc2 x x.2
  have hψcomm : ∀ (l : ↥L) (u : Fin r → F),
      ψ ((N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (N.Mat l : Matrix (Fin r) (Fin r) F) *ᵥ ψ u := by
    intro l u
    obtain ⟨x, rfl⟩ := N.surj u
    rw [← N.equiv l x, hψ, hψ, ← N.equiv l ⟨ρ c (x : V), hcI x x.2⟩]
    apply congrArg N.π
    apply Subtype.ext
    exact natq_rho_comm (hc l l.2) (x : V)
  have hπfix : ∀ x : ↥N.I, N.π ⟨ρ c (x : V), hcI x x.2⟩ = N.π x := by
    intro x
    by_cases hr : r = 0
    · have : Subsingleton (Fin r → F) := by
        cases hr
        exact ⟨fun f g => funext fun i => i.elim0⟩
      exact Subsingleton.elim _ _
    · obtain ⟨lam, hlam⟩ := hS ψ hψcomm
      have hψ2u : ∀ u : Fin r → F, (lam * lam) • u = u := by
        intro u
        have h := hψ2 u
        rw [hlam u, hlam (lam • u), smul_smul] at h
        exact h
      have hsq : lam * lam = 1 := by
        have h := congrFun (hψ2u (Pi.single ⟨0, Nat.pos_of_ne_zero hr⟩ (1 : F)))
          ⟨0, Nat.pos_of_ne_zero hr⟩
        simpa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] using h
      have hlam1 : lam = 1 := by
        have h2 : lam ^ 2 = 1 := by rw [pow_two]; exact hsq
        rcases (sq_eq_one_iff.mp h2) with h | h
        · exact h
        · rw [h]; exact CharTwo.neg_eq 1
      rw [← hψ x, hlam (N.π x), hlam1, one_smul]
  have hgen : ∀ (l : G) (hl : l ∈ L) (x : V) (hx : x ∈ N.I),
      ρ c (ρ l x - x) = ρ l x - x := by
    intro l hl x hx
    have hdx : ρ l (ρ c x - x) = ρ c x - x := by
      have hker : N.π (⟨ρ c x, hcI x hx⟩ - ⟨x, hx⟩) = 0 := by
        rw [map_sub, hπfix ⟨x, hx⟩, sub_self]
      have := (N.ker_iff (⟨ρ c x, hcI x hx⟩ - ⟨x, hx⟩)).mp hker l hl
      simpa using this
    have hcommx : ρ c (ρ l x) = ρ l (ρ c x) := natq_rho_comm (hc l hl) x
    have hdx' : ρ l (ρ c x) - ρ l x = ρ c x - x := by simpa [map_sub] using hdx
    have hdx'' : ρ l (ρ c x) = (ρ c x - x) + ρ l x := sub_eq_iff_eq_add.mp hdx'
    calc ρ c (ρ l x - x)
        = ρ c (ρ l x) - ρ c x := map_sub (ρ c) _ _
      _ = ρ l (ρ c x) - ρ c x := by rw [hcommx]
      _ = ((ρ c x - x) + ρ l x) - ρ c x := by rw [hdx'']
      _ = ρ l x - x := by abel
  refine Submodule.span_induction (p := fun x _ => ρ c x = x) ?_ ?_ ?_ ?_ (hIcomm v hv)
  · intro w hw
    rcases hw with ⟨l, hl, x, hx, rfl⟩
    exact hgen l hl x hx
  · simp
  · intro x y hx hy hpx hpy
    rw [map_add, hpx, hpy]
  · intro a x hx hpx
    rw [map_smul, hpx]

end CFSG.LocalAnalysis.RankThreeUC.S15

end
