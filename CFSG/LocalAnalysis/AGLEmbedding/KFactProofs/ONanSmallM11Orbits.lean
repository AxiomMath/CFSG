module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitTrans

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open Certificates.ONanSmallM11 CFSG.Blueprint

section Local


theorem orbitTrans_m11T0 {T : Sylow 3 ↥NativeSporadic.M11}
    (hT : (T : Subgroup ↥NativeSporadic.M11) = m11T0) : OrbitTrans 3 ↥NativeSporadic.M11 T := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, htrans, -⟩ := m11_facts
  intro x hx hx1 y hy hy1
  rw [hT] at hx hy ⊢
  obtain ⟨n, hn, hnst, hnxy⟩ := htrans (x : Equiv.Perm (Fin 11))
    (mem_m11T0_iff_mem_m11E.1 hx) (fun h => hx1 (Subtype.ext h)) (y : Equiv.Perm (Fin 11))
    (mem_m11T0_iff_mem_m11E.1 hy) (fun h => hy1 (Subtype.ext h))
  refine ⟨⟨n, hn⟩, ?_, Subtype.ext hnxy⟩
  rw [normalizer_m11T0]
  exact (mem_stabilizer_duad_iff _ (by decide)).2 hnst

end Local

section Certified


theorem orbitTrans_m11 {K : Type} [Group K] [Finite K] (hK : IsSporadicGroup .M11 K)
    (T : Sylow 3 K) : OrbitTrans 3 K T := by
  obtain ⟨e⟩ := nonempty_equiv_m11 hK
  obtain ⟨T₀, hT₀⟩ := exists_sylow_m11T0
  exact OrbitTrans.of_equiv_all Nat.prime_three e ⟨T₀, orbitTrans_m11T0 hT₀⟩ T

end Certified

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
