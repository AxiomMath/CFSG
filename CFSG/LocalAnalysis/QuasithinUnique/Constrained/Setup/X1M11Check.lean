module

public import CFSG.Sporadic.Schreier.M11Data
public meta import CFSG.Sporadic.Schreier.M11Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M11CheckInputs
public import Certificates.Certificate4135

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu

theorem m11_pair_count :
    ((m11Elements.filter (orderIs · 2) ×ˢ m11Elements.filter (orderIs · 4)).filter
      fun q => orderIs (q.1 * q.2) 11 && orderIs (m11Word q.1 q.2) 3).length = 7920 :=
  Certificates.certificate4135.1

theorem m11_orders_ab :
    orderIs m11gA 2 = true ∧ orderIs m11gB 4 = true ∧ orderIs (m11gA * m11gB) 11 = true ∧
      orderIs (m11Word m11gA m11gB) 3 = true :=
  Certificates.certificate4135.2.1

theorem m11_no_indep_triple :
    (m11Invs.all fun x => m11Invs.all fun y =>
      !(x * y == y * x) || m11Invs.all fun z =>
        !(x * z == z * x && y * z == z * y) ||
          (x == z || x == y || x == y * z || y == z)) = true :=
  Certificates.certificate4135.2.2.1

theorem m11_conj_class :
    (m11Invs.all fun x => m11ConjsA.contains x) = true :=
  Certificates.certificate4135.2.2.2.1

theorem m11_gen_check :
    (List.finRange 3).all (fun i => m11Invs.contains (m11G i)) = true ∧
    (m11WordA.map m11G).prod = m11gA ∧ (m11WordB.map m11G).prod = m11gB :=
  Certificates.certificate4135.2.2.2.2

end CFSG.QuasithinUnique.Setup.X1
