
module

public import CFSG.Literature.GL52BFS
public import CFSG.Literature.GL52Pass
public import CFSG.Literature.GL52Elements
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public meta import CFSG.Literature.GL52BFS
public meta import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Elements
public meta import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Literature.GL52IsosInputs
public import Certificates.Certificate2001

public section

namespace CFSG.Literature.GL52

open Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem gl3Elems_check : (gl3Elems.map keyGL3).Nodup ∧ gl3Elems.length = 168 :=
  Certificates.certificate2001.1

theorem mem_gl3Elems (M : GL (Fin 3) (ZMod 2)) : M ∈ gl3Elems := by
  classical
  have hnd : gl3Elems.Nodup := gl3Elems_check.1.of_map _
  have h1 : gl3Elems.toFinset.card = 168 := by
    rw [List.toFinset_card_of_nodup hnd, gl3Elems_check.2]
  have h2 : gl3Elems.toFinset = Finset.univ := Finset.eq_univ_of_card _ (by
    rw [h1, ← Nat.card_eq_fintype_card,
      CFSG.LocalAnalysis.ComponentInitial.card_GL_three_zmod_two])
  have := Finset.mem_univ M
  rw [← h2] at this
  exact List.mem_toFinset.1 this

local instance (priority := high) fastGL3 :
    Fintype (GL (Fin 3) (ZMod 2)) :=
  ⟨⟨gl3Elems, gl3Elems_check.1.of_map _⟩, mem_gl3Elems⟩

theorem mulOK_K1' : ∀ q r : alternatingGroup (Fin 5),
    tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 (q * r))
      (compT 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (lkTableT tbK1 tbiK1 keyA5 tblA5 r)) =
      true :=
  Certificates.certificate2001.2.1

theorem mulOK_K1 : lkMulOK gensK1 keyA5 tblA5 := mulOK_K1'

theorem injOK_K1' : ∀ q : alternatingGroup (Fin 5),
    tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (idT 31) = true → q = 1 :=
  Certificates.certificate2001.2.2.1

theorem injOK_K1 : lkInjOK gensK1 keyA5 tblA5 := injOK_K1'

theorem mulOK_K2' : ∀ q r : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 (q * r))
      (compT 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (lkTableT tbK2 tbiK2 keyGL3 tblGL3 r)) =
      true :=
  Certificates.certificate2001.2.2.2.1

theorem mulOK_K2 : lkMulOK gensK2 keyGL3 tblGL3 := mulOK_K2'

theorem injOK_K2' : ∀ q : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (idT 31) = true → q = 1 :=
  Certificates.certificate2001.2.2.2.2.1

theorem injOK_K2 : lkInjOK gensK2 keyGL3 tblGL3 := injOK_K2'

@[expose] def homK1 : alternatingGroup (Fin 5) →* G := lkHom gensK1 keyA5 tblA5 mulOK_K1

@[expose] def homK2 : GL (Fin 3) (ZMod 2) →* G := lkHom gensK2 keyGL3 tblGL3 mulOK_K2

theorem homK1_injective : Function.Injective homK1 := lkHom_injective _ _ _ _ injOK_K1

theorem homK2_injective : Function.Injective homK2 := lkHom_injective _ _ _ _ injOK_K2

end CFSG.Literature.GL52
