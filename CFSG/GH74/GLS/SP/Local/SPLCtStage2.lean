module

public import CFSG.GH74.GLS.SP.Local.SPLCtStage

public section

namespace CFSG.GH74.GLS.SP.Local

variable {G : Type} [Group G]

structure SPLCtUD (D : SPLNot1 G) (u : G) : Prop where
  U : SPLCtU D u
  d : ∃ g : G, g⁻¹ * u * g = u ∧ g⁻¹ * D.z * g = D.t * u ∧ g⁻¹ * D.t * g = D.z * u
  K3 : SPLCenUAt D u

end CFSG.GH74.GLS.SP.Local
