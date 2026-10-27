module

public import CFSG.ClassicalInvolution.Q3.Q3TNGen
public import CFSG.ClassicalInvolution.Q3.Q3T6BTwinP

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6B

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Uniform.U4
open scoped commutatorElement MatrixGroups

variable {F : Type} [Group F] [Finite F]

theorem exAt_conj {a : F} (h : ExAt a) (g : F) : ExAt (g * a * g⁻¹) := by
  have h1 := Balance.Bootstrap.oddCoreIn_conjSub_eq g (Subgroup.centralizer ({a} : Set F))
  have h2 : conjSub g (Subgroup.centralizer ({a} : Set F)) =
      Subgroup.centralizer ({g * a * g⁻¹} : Set F) := map_conj_centralizer_singleton g a
  rw [h2] at h1
  unfold ExAt at h ⊢
  rw [h1, h]
  exact Subgroup.map_bot _

theorem Mem3.exAt_iff {K : Subgroup F} {z : F} (hK : Mem3 K z) :
    ExAt z ↔ classicalInvolutionOddCore K = ⊥ := by
  have h1 : Balance.oddCoreIn K = Balance.oddCoreIn (Subgroup.centralizer ({z} : Set F)) :=
    Uniform.oddCoreIn_eq_of_intrinsic hK.member (hK.intrinsic solvableType_three)
  constructor
  · intro h
    have h2 : Balance.oddCoreIn K = ⊥ := h1.trans h
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp h2
  · intro h
    unfold ExAt
    rw [← h1]
    show (classicalInvolutionOddCore ↥K).map K.subtype = ⊥
    rw [h]
    exact Subgroup.map_bot _

section Twins

variable {Q : Subgroup F} {r u : F}

theorem Swap.comm_twin (hs : Swap Q r u) (hex : ExAt r) :
    ∀ a ∈ Q, ∀ b ∈ conjSub u Q, a * b = b * a :=
  fun _ ha _ hb =>
    Mem3.commute_of_twin_exact hs.member hs.twin hex (fun h => hs.moves h.symm) ha hb

theorem diag_mul_of_comm (hc : ∀ a ∈ Q, ∀ b ∈ conjSub u Q, a * b = b * a) {a b : F} (ha : a ∈ Q)
    (hb : b ∈ Q) : diag u (a * b) = diag u a * diag u b := by
  have hcb : b * (u * a * u⁻¹) = (u * a * u⁻¹) * b := hc b hb _ (conj_mem_conjSub ha)
  unfold diag
  calc a * b * (u * (a * b) * u⁻¹) = a * (b * (u * a * u⁻¹)) * (u * b * u⁻¹) := by group
    _ = a * ((u * a * u⁻¹) * b) * (u * b * u⁻¹) := by rw [hcb]
    _ = (a * (u * a * u⁻¹)) * (b * (u * b * u⁻¹)) := by group

theorem diag_pow_eq_one (hc : ∀ a ∈ Q, ∀ b ∈ conjSub u Q, a * b = b * a) {s : F} (hs : s ∈ Q)
    {n : ℕ} (hn : s ^ n = 1) : diag u s ^ n = 1 := by
  have hcomm : Commute s (u * s * u⁻¹) := hc s hs _ (conj_mem_conjSub hs)
  unfold diag
  rw [hcomm.mul_pow, hn, conj_pow, hn]
  simp

@[expose] def diagOddSet (Q : Subgroup F) (u : F) : Set F :=
  {d | ∃ s ∈ Q, ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ s ^ p ^ k = 1 ∧ d = diag u s}

theorem diag_mem_closure_odd (hs : Swap Q r u) (hex : ExAt r) {q : F} (hq : q ∈ Q) :
    diag u q ∈ Subgroup.closure (diagOddSet Q u) := by
  have hc := hs.comm_twin hex
  let f : ↥Q →* F :=
    { toFun := fun a => diag u (a : F)
      map_one' := by simp [diag]
      map_mul' := fun a b => diag_mul_of_comm hc a.2 b.2 }
  let H : Subgroup F := ((Subgroup.closure (diagOddSet Q u)).comap f).map Q.subtype
  have hle : Q ≤ H :=
    Q3T.le_of_forall_oddPrimePow_mem (hs.member.member.toQ3 (by norm_num))
      fun g hg p k hp hp2 hgp =>
        ⟨⟨g, hg⟩, Subgroup.subset_closure ⟨g, hg, p, k, hp, hp2, hgp, rfl⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hle hq
  exact hx

theorem odd_orderOf_diag (hc : ∀ a ∈ Q, ∀ b ∈ conjSub u Q, a * b = b * a) {s : F} (hs : s ∈ Q)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hsp : s ^ p ^ k = 1) : Odd (orderOf (diag u s)) :=
  ((hp.odd_of_ne_two hp2).pow).of_dvd_nat (orderOf_dvd_of_pow_eq_one (diag_pow_eq_one hc hs hsp))

theorem diag_comm_both (hs : Swap Q r u) (hex : ExAt r) {s : F} (hsQ : s ∈ Q) :
    diag u s * r = r * diag u s ∧ diag u s * u = u * diag u s := by
  have hc := hs.comm_twin hex
  have h1 : s * r = r * s := hs.member.mul_comm_of_mem hsQ
  have h2 : (u * s * u⁻¹) * r = r * (u * s * u⁻¹) :=
    hs.twin.mul_comm_of_mem (conj_mem_conjSub hsQ)
  refine ⟨(diag_comm_x h1 h2).symm, ?_⟩
  exact (diag_comm_y hs.sq (hc s hsQ _ (conj_mem_conjSub hsQ))).symm

end Twins

end CFSG.ClassicalInvolution.Q3.Q3T6B
