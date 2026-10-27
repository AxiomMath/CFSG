module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem96
public import CFSG.GH74.GLS.Stage2.Signalizer.L64Sub

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace L915

section A1

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {N A B : Subgroup G}

@[expose] def A1 (z : G) (M N : Subgroup G) (p : ℕ) : Subgroup G := ⁅Op p M ⊓ N, zpowers z⁆

omit [Finite G] in
theorem z_mem_N (h : Hyp95 z M p N A B) : z ∈ N := h.B_norm h.B_inv

theorem z_mem_normalizer_PN (hC : Ctx9 G z k S M p) (hzN : z ∈ N) :
    z ∈ normalizer ((Op p M ⊓ N : Subgroup G) : Set G) :=
  Thm1.mem_normalizer_inf (le_normalizer_Op' p M hC.z_mem) (Subgroup.le_normalizer hzN)

theorem A1_le (hC : Ctx9 G z k S M p) (hzN : z ∈ N) : A1 z M N p ≤ Op p M ⊓ N :=
  commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr (z_mem_normalizer_PN hC hzN))

theorem A1_comm (hC : Ctx9 G z k S M p) (hzN : z ∈ N) : ⁅A1 z M N p, zpowers z⁆ = A1 z M N p :=
  commutator_zpowers_idem hC.orderOf_z hC.prime hC.odd (hC.P_pgroup.to_le inf_le_left)
    (z_mem_normalizer_PN hC hzN)

omit [Finite G] in
theorem A_le_A1 (h : Hyp95 z M p N A B) : A ≤ A1 z M N p := by
  conv_lhs => rw [← h.A_comm]
  exact Subgroup.commutator_mono (le_inf h.A_le h.A_N) le_rfl

omit [Finite G] in
theorem A1_ne_bot (h : Hyp95 z M p N A B) : A1 z M N p ≠ ⊥ := fun hb =>
  h.A_ne (le_bot_iff.mp (hb ▸ A_le_A1 h))

theorem isPGroup_A1 (hC : Ctx9 G z k S M p) (hzN : z ∈ N) : IsPGroup p ↥(A1 z M N p) :=
  hC.P_pgroup.to_le ((A1_le hC hzN).trans inf_le_left)

theorem inv_A1 (hC : Ctx9 G z k S M p) {c : G} (hcN : c ∈ N)
    (hcz : c ∈ centralizer ({z} : Set G)) : c ∈ normalizer ((A1 z M N p : Subgroup G) : Set G) := by
  have hcM : c ∈ M := hC.cen_le hcz
  have hcPN : c ∈ normalizer ((Op p M ⊓ N : Subgroup G) : Set G) :=
    Thm1.mem_normalizer_inf (le_normalizer_Op' p M hcM) (Subgroup.le_normalizer hcN)
  exact mem_normalizer_commutator hcPN
    (mem_normalizer_zpowers_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hcz))

theorem sig4Sub_A1 (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B) :
    Sig4Sub G z N p (A1 z M N p) := by
  have hzN : z ∈ N := z_mem_N h
  exact ⟨h.coatom.1, ⟨hC.prime, hC.odd, hzN, (A1_le hC hzN).trans inf_le_right,
    isPGroup_A1 hC hzN, A1_ne_bot h, fun c hcN hcz => inv_A1 hC hcN hcz, A1_comm hC hzN⟩⟩

omit [Finite G] in
theorem Em_comm_A1_ne_bot (hAE : ¬ A ≤ centralizer (Em N : Set G)) (h : Hyp95 z M p N A B) :
    ⁅Em N, A1 z M N p⁆ ≠ ⊥ := by
  intro hb
  apply hAE
  have h1 : Em N ≤ centralizer ((A1 z M N p : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
  have h2 : A1 z M N p ≤ centralizer (Em N : Set G) := Subgroup.le_centralizer_iff.mp h1
  exact (A_le_A1 h).trans h2

theorem concl43E_A1 (h43E : Prop4_3E) (hC : Ctx9 G z k S M p) (h : Hyp95 z M p N A B)
    (hAE : ¬ A ≤ centralizer (Em N : Set G)) :
    Concl43E k (zSec z N (z_mem_N h) (pCore p ↥N)) p (xBar p N (A1 z M N p)) :=
  L64.prop4_3Esub_of h43E hC.ctx (sig4Sub_A1 hC h) (Em_comm_A1_ne_bot hAE h)

end A1

end L915

end CFSG.GH74.GLS.Stage2.Bender.Thm2
