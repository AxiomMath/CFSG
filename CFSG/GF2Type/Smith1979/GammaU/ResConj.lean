module

public import CFSG.GF2Type.Smith1979.GammaU.PairCensus
public import Certificates.Certificate16970

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem resConj_nlMem {i : ℕ} (hi : i = 0 ∨ i = 1) {c : Array ℕ}
    (hc : c ∈ ResPair.resConj i) (h1 : mulR c (Viol.invR c) = idR)
    (h2 : mulR (Viol.invR c) c = idR) : NLMem i (Viol.eqvOf c (Viol.invR c) h1 h2) := by
  have h := Certificates.certificate16970
  unfold resConjCheck at h
  have hi' := List.all_eq_true.1 h i (by rcases hi with rfl | rfl <;> simp)
  have hc' : (c, CFSG.GammaU.Native.invR c) ∈
      (CFSG.GammaU.Native.resConj i).map fun c => (c, CFSG.GammaU.Native.invR c) :=
    List.mem_map.2 ⟨c, by rw [native_resConj]; exact hc, rfl⟩
  obtain ⟨hg, -, hmul, -, ha, hd, hdi, hcn, hci⟩ := nlOKAt_spec hi' _ hc'
  have heq : Viol.eqvOf c (Viol.invR c) h1 h2 = toU c hg := LinearEquiv.ext fun _ => rfl
  rw [heq]
  exact nlMem_gen hg hmul ha hd hdi hcn hci

end CFSG.GF2Type.Smith1979.GammaU.StepA
