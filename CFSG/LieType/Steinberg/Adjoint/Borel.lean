module

public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.BruhatWeyl
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} (F : RootOperatorFamily τ) (K : Type) [Field K]

theorem adjDatum_bruhatExtras : BruhatExtras (adjDatum F K) (torus K) where
  borel_inf_negUnipotent := eq_bot_iff.2 ((inf_le_inf
    (sup_le (iSup_le fun i => (torus_le_diag i).trans (diag_le_tri htHom))
      ((iSup₂_le fun γ hγ => rootGroup_le_unip htHom hγ.2).trans (unip_le_tri htHom)))
    (iSup₂_le fun γ hγ => rootGroup_le_unip (-htHom) (by
      rw [AddMonoidHom.neg_apply, htHom_apply]
      exact neg_pos.2 hγ.2))).trans (tri_inf_unip_neg htHom).le)

theorem f4_bruhatExtras : BruhatExtras (f4Datum K) (torus (τ := .F4) K) :=
  adjDatum_bruhatExtras _ K

theorem e8_bruhatExtras : BruhatExtras (e8Datum K) (torus (τ := .E8) K) :=
  adjDatum_bruhatExtras _ K

end CFSG.LieType.Steinberg.Adjoint
