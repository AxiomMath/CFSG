module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410TrH

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup _root_.Certificates

namespace Fz410Mod

variable {G : Type} [Group G] [Finite G] {t tau lam rho s : G} {Z E W Q R T P : Subgroup G}
  {emb : FzL410.A → G} (M : Fz410Mod t tau lam rho s Z E W Q R T P emb)

include M

theorem sqZ_transfer (h : FzL410.SqZ) : ∀ x ∈ R, x ^ 2 ∈ Z := by
  intro x hx
  obtain ⟨y, rfl⟩ := (M.mem_T x).mp (M.str.RT hx)
  have hz := h y ((M.mem_R y).mp hx)
  rw [M.mu_sq]
  have h2 : FzL410.mulT y y = FzL410.pe (FzL410.mulT y y).1 := Prod.ext rfl hz.1
  rw [h2, M.mu_pe]
  exact (M.mem_Z _).mpr hz.2

theorem rq_transfer (h : FzL410.RQ) : ∀ x ∈ R, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ E := by
  intro x hx y hy
  obtain ⟨x', rfl⟩ := (M.mem_T x).mp (M.str.RT hx)
  obtain ⟨y', rfl⟩ := (M.mem_T y).mp (M.str.RT (M.str.QR hy))
  obtain ⟨a, b, hab⟩ := h x' ((M.mem_R x').mp hx) y' ((M.mem_Q y').mp hy)
  have h1 : fz410Mu emb t s lam x' * fz410Mu emb t s lam y' =
      (emb (a, b, 0, 0) * fz410Mu emb t s lam y') * fz410Mu emb t s lam x' := by
    rw [← M.mu_mul, hab, M.mu_mul, M.mu_mul, M.mu_eE]
  have h2 : fz410Mu emb t s lam x' * fz410Mu emb t s lam y' * (fz410Mu emb t s lam x')⁻¹ *
      (fz410Mu emb t s lam y')⁻¹ = emb (a, b, 0, 0) := by
    rw [h1]
    group
  rw [h2]
  exact M.eE_mem a b

theorem qc_transfer (h : FzL410.QC) : ∀ x ∈ R, ((∀ e ∈ E, x * e = e * x) ↔ x ∈ Q) := by
  intro x hx
  obtain ⟨x', rfl⟩ := (M.mem_T x).mp (M.str.RT hx)
  refine Iff.trans ?_ ((M.mem_Q x').symm)
  refine Iff.trans ?_ (h x' ((M.mem_R x').mp hx))
  constructor
  · intro hc a b
    apply M.mu_inj
    rw [M.mu_mul, M.mu_mul, M.mu_eE]
    exact hc _ (M.eE_mem a b)
  · intro hc e he
    obtain ⟨a, b, rfl⟩ := M.exists_eE he
    have := congrArg (fz410Mu emb t s lam) (hc a b)
    rwa [M.mu_mul, M.mu_mul, M.mu_eE] at this

theorem ef_transfer (h : FzL410.EF) : ∀ a ∈ E, a ∈ fz410F P t s → a ∈ Z := by
  intro a ha haF
  obtain ⟨a', rfl⟩ := (M.emb.mem a).mp (M.pf.EP ha)
  exact (M.mem_Z a').mpr (h a' ((M.mem_E a').mp ha) ((M.mem_F a').mp haF))

theorem centP_transfer (h : FzL410.CentP) : ∀ i ∈ R, i ∉ P →
    ((∀ a ∈ P, (i * a = a * i ↔ a ∈ E)) ∨ (∀ a ∈ P, (i * a = a * i ↔ a ∈ fz410F P t s)) ∨
      (∀ a ∈ P, i * a = a * i → a ^ 2 = 1)) := by
  intro i hi hiP
  obtain ⟨y, rfl⟩ := (M.mem_T i).mp (M.str.RT hi)
  have hyP : ¬ FzL410.inP y := fun h' => hiP ((M.mem_P y).mpr h')
  rcases h y ((M.mem_R y).mp hi) hyP with h1 | h2 | h3
  · left
    intro a ha
    obtain ⟨a', rfl⟩ := (M.emb.mem a).mp ha
    rw [M.mu_comm_pe]
    exact ⟨fun hc => (M.mem_E a').mpr ((h1 a').mp hc),
      fun haE => (h1 a').mpr ((M.mem_E a').mp haE)⟩
  · right
    left
    intro a ha
    obtain ⟨a', rfl⟩ := (M.emb.mem a).mp ha
    rw [M.mu_comm_pe]
    exact ⟨fun hc => (M.mem_F a').mpr ((h2 a').mp hc),
      fun haF => (h2 a').mpr ((M.mem_F a').mp haF)⟩
  · right
    right
    intro a ha hc
    obtain ⟨a', rfl⟩ := (M.emb.mem a).mp ha
    have h4 := h3 a' ((M.mu_comm_pe y a').mp hc)
    rw [← M.emb.emb_nsmul 2 a', h4, M.emb.emb_zero]

theorem invF_transfer (h : FzL410.InvF) : ∀ i ∈ R, i ∉ P → i ^ 2 = 1 →
    (∀ a ∈ P, (i * a = a * i ↔ a ∈ fz410F P t s)) → ∃ e ∈ E, i = e * (t * s) := by
  intro i hi hiP hi2 hF
  obtain ⟨y, rfl⟩ := (M.mem_T i).mp (M.str.RT hi)
  have hyP : ¬ FzL410.inP y := fun h' => hiP ((M.mem_P y).mpr h')
  have hyy : FzL410.mulT y y = FzL410.oneT := by
    apply M.mu_inj
    rw [← M.mu_sq, M.mu_one]
    exact hi2
  have hcent : FzL410.CentOf y FzL410.FA := by
    intro a'
    rw [← M.mem_F a', ← M.mu_comm_pe]
    exact hF _ (M.emb.emb_mem a')
  obtain ⟨a, b, hab⟩ := h y ((M.mem_R y).mp hi) hyP hyy hcent
  refine ⟨emb (a, b, 0, 0), M.eE_mem a b, ?_⟩
  rw [hab, M.mu_mul, M.mu_eE, M.mu_tsM]

end Fz410Mod

end CFSG.OddStandard.SmallF3.FritzII
