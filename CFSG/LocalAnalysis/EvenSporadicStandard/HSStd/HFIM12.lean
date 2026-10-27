module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIM12Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIBasic
public import Certificates.Certificate27220

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open Subgroup CFSG.PSL3Four.Native

theorem exists_fusing_of_good_triple_m12 {K : Type} [Group K]
    (hK : CFSG.Blueprint.NativeSporadic.IsSporadic K .M12) {a b : K}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (hcomm : a * b = b * a)
    (ea : Nonempty (↥(centralizer ({a} : Set K)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (eb : Nonempty (↥(centralizer ({b} : Set K)) ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 5)))
    (eab : Nonempty (↥(centralizer ({a * b} : Set K)) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 5))) :
    ∃ h : K, h * a * h⁻¹ = b ∧ h * b * h⁻¹ = a * b := by
  obtain ⟨φ⟩ := hK
  let φ' : K ≃* ↥M12G := φ
  have hord : ∀ {x : K}, orderOf x = 2 → orderOf (φ' x) = 2 := fun {x} hx =>
    (orderOf_injective φ'.toMonoidHom φ'.injective x).trans hx
  obtain ⟨g, hg1, hg2⟩ := m12_triple_spec (EM := enumBFS 12 m12Gens 95040)
    (OA := orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12a₀T 891)
    (OB := orbitBFS 12 m12Gens (m12Gens.map (invTab 12)) m12b₀T 891)
    Certificates.certificate27220 (a := φ' a) (b := φ' b) (hord ha) (hord hb)
    (fun h => hab (φ'.injective h))
    (by rw [← map_mul, ← map_mul, hcomm])
    (by rw [card_centralizer_singleton_map φ' a]; exact card_centralizer_of_good ea)
    (by rw [card_centralizer_singleton_map φ' b]; exact card_centralizer_of_good eb)
    (by
      rw [← map_mul, card_centralizer_singleton_map φ' (a * b)]
      exact card_centralizer_of_good eab)
  refine ⟨φ'.symm g, ?_, ?_⟩
  · apply φ'.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hg1
  · apply φ'.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_mul]
    exact hg2

end CFSG.EvenSporadicStandard.HSStd.HFI
