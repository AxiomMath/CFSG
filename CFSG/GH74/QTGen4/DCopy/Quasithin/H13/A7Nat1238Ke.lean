module

public import CFSG.Quasithin.H13.A7Nat1238Ke
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Statements

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

section Ke

variable (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)

theorem T_le_normalizer_Kv_F4 (h1225 : Stmt12_2_5_F4) {v : G} (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hvZ : v ∈ quasithinOmegaOneCenter T) : T ≤ normalizer (Kv hyp v : Set G) := by
  obtain ⟨-, hMeN, -, -, -⟩ := h1225 G T L V hyp v hvV hv1
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ hyp.Gv v := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hvZ) t ht))
  exact ((le_inf hyp.normalizes hTe).trans hMeN).trans (normalizer_le_normalizer_perfectCore _)

end Ke

end CFSG.Quasithin.H13.A7
