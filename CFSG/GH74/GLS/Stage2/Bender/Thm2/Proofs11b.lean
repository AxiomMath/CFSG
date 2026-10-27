module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Assemble
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Axb
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Conj

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Facts

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem Ctx10.t_mem_U (h : Ctx10 G z k S M p Q T U t g) : t ∈ U := by
  rw [h.choice.U_gen]
  exact Subgroup.mem_sup_right (mem_zpowers t)

theorem Ctx10.U_le_Cen (h : Ctx10 G z k S M p Q T U t g) : U ≤ Cen z :=
  h.choice.U_le.trans h.ctx9.ctx.S_le_Cen

theorem Ctx10.U_le_M (h : Ctx10 G z k S M p Q T U t g) : U ≤ M := h.U_le_Cen.trans h.ctx9.cen_le

theorem Ctx10.t_mul_t (h : Ctx10 G z k S M p Q T U t g) : t * t = 1 := by
  rw [h.choice.t_conj]
  calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [h.ctx9.z_mul_z]; group

theorem Ctx10.z_comm_t (h : Ctx10 G z k S M p Q T U t g) : z * t = t * z :=
  (Subgroup.mem_centralizer_singleton_iff.mp (h.U_le_Cen h.t_mem_U)).symm

theorem Ctx10.t_ne_z (h : Ctx10 G z k S M p Q T U t g) : t ≠ z := fun e =>
  h.choice.t_out 1 (one_mem M) (by rw [e]; simp)

theorem Ctx10.t_ne_one (h : Ctx10 G z k S M p Q T U t g) : t ≠ 1 := by
  intro e
  have h1 : z = g * t * g⁻¹ := by
    rw [h.choice.t_conj]
    group
  rw [e] at h1
  exact z_ne_one_of_ctx h.ctx9.ctx (by rw [h1]; group)

theorem Ctx10.cenU_le_cenz (h : Ctx10 G z k S M p Q T U t g) : centralizer (U : Set G) ≤ Cen z :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.z_mem_U)

theorem Ctx10.cenU_le_M (h : Ctx10 G z k S M p Q T U t g) : centralizer (U : Set G) ≤ M :=
  h.cenU_le_cenz.trans h.ctx9.cen_le

theorem Ctx10.T_eq_S (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k) : T = S :=
  (h.choice.T_one hone).1

theorem Ctx10.S_le_normalizer_U (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k) :
    S ≤ normalizer (U : Set G) := fun s hs =>
  mem_normalizer_of_forall fun u hu => (h.choice.T_one hone).2 s hs u hu

theorem Ctx10.exists_swap (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k) :
    ∃ n ∈ normalizer (U : Set G), n * z * n⁻¹ = t :=
  h.choice.trans hone z h.z_mem_U (z_ne_one_of_ctx h.ctx9.ctx) t h.t_mem_U h.t_ne_one

theorem Ctx10.not_normalizer_U_le_M (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k) :
    ¬ normalizer (U : Set G) ≤ M := by
  intro hle
  obtain ⟨n, hn, hnz⟩ := h.exists_swap hone
  exact h.choice.t_out n⁻¹ (inv_mem (hle hn)) (by rw [inv_inv]; exact hnz)

end Facts

section CaseA

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {Q T U : Subgroup G} {t g : G}

theorem exists_R_of_Op_ne_bot (h : Ctx10 G z k S M p Q T U t g) (hone : TypeOneCase G k)
    (hne : Op p (centralizer (U : Set G)) ≠ ⊥) :
    ∃ R : Subgroup G, Rp z k p T U Q M R ∧
      Covers (normalizer (R : Set G)) (normalizer (U : Set G)) (centralizer (U : Set G)) := by
  have hp := h.ctx9.prime
  have hp2 := h.ctx9.odd
  have hNU : normalizer (U : Set G) ≤ normalizer ((Op p (centralizer (U : Set G)) : Subgroup G) : Set G) :=
    le_normalizer_of_characteristic (normalizer_le_normalizer_centralizer U)
      (pCore p ↥(centralizer (U : Set G)))
  have hRC : Op p (centralizer (U : Set G)) ≤ centralizer (U : Set G) := Op_le' p _
  have hRM : Op p (centralizer (U : Set G)) ≤ M := hRC.trans h.cenU_le_M
  have hTU : T ≤ normalizer (U : Set G) := (h.T_eq_S hone).le.trans (h.S_le_normalizer_U hone)
  have hRp : IsPGroup p ↥(Op p (centralizer (U : Set G))) := op_isPGroup _
  refine ⟨Op p (centralizer (U : Set G)), ⟨⟨hne, hRp, hRM, fun x hx => hNU (hTU hx), fun hn => absurd hone hn⟩, ?_⟩,
    fun x hx => Subgroup.mem_sup_left ⟨hNU hx, hx⟩⟩
  intro hb
  have hQcen : Q ⊓ normalizer ((Op p (centralizer (U : Set G)) : Subgroup G) : Set G) ≤ Cen z :=
    commutator_zpowers_eq_bot_iff.mp hb
  have hcop : Nat.Coprime p (Nat.card ↥(zpowers z)) := by
    rw [Nat.card_zpowers, h.ctx9.orderOf_z]
    exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  have hAQ : zpowers z ≤ normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (h.M_le_normalizer_Q h.ctx9.z_mem)
  have hBQ : Op p (centralizer (U : Set G)) ≤ normalizer (Q : Set G) := fun x hx => h.M_le_normalizer_Q (hRM hx)
  have hAB : ∀ a ∈ zpowers z, ∀ b ∈ Op p (centralizer (U : Set G)), a * b = b * a := by
    intro a ha b hb'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hbz : b * z = z * b := Subgroup.mem_centralizer_singleton_iff.mp (h.cenU_le_cenz (hRC hb'))
    exact ((Commute.zpow_left (show Commute z b from hbz.symm) n).eq)
  have hfix : zpowers z ≤ centralizer (((Q ⊓ centralizer ((Op p (centralizer (U : Set G)) : Subgroup G) : Set G)
      : Subgroup G)) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    have hxN : x ∈ normalizer ((Op p (centralizer (U : Set G)) : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ hx.2
    have hxz : x ∈ Cen z := hQcen ⟨hx.1, hxN⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hxz
  have hzQ := Thm1.ig_11_7_thm G p hp (zpowers z) (Op p (centralizer (U : Set G))) Q h.Q_pgroup hRp hcop hAQ hBQ
    hAB hfix
  apply h.not_Q_le_Cen
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (hzQ (mem_zpowers z)) x hx)

end CaseA

end CFSG.GH74.GLS.Stage2.Bender.Thm2
