module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldON
public import Certificates.Certificate6135

public section

namespace CFSG.OddStandard.ChengHeld

namespace ONSylow

theorem onPres_check : Finite ONPres ∧ Nat.card ONPres ≤ 512 :=
  Certificates.certificate6135

end ONSylow

open CFSG.Blueprint ONSylow

theorem exists_mulEquiv_onSylow_cert
    {G : Type} [Group G] [Finite G]
    {t pi tau mu lam ze xi z : G}
    (hf : Frame4 0 t pi tau mu lam ze xi) (hz2 : z * z = 1)
    (hz : Kind.unitary.Act 0 t pi tau mu lam ze xi z)
    {X : Subgroup G} (hX : X = Subgroup.closure ({t, pi, tau, mu, lam, ze, xi, z} : Set G))
    (hcard : Nat.card X = 512) :
    ∃ T : Sylow 2 NativeSporadic.ON, Nonempty (X ≃* (T : Subgroup NativeSporadic.ON)) :=
  exists_mulEquiv_onSylow hf hz2 hz hX hcard onPres_check

end CFSG.OddStandard.ChengHeld
