module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Stage
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BCo2Conj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Sporadic.Co2Cert
open CFSG.Sporadic.Co2Schreier (locZ)
open CFSG.LocalAnalysis.GLTheoremA.H301B.Co2Stage

section Model


theorem rowCo2_model : Co2ModelStmt := by
  intro B K R0 R1 y hBP hKP hR0P hR1P h
  obtain ⟨z', hz2, hz1, rfl⟩ := exists_zpowers_of_card_two h.card_R0
  have hz'P : z' ∈ co2P := hR0P (Subgroup.mem_zpowers z')
  have hcomm : ∀ g ∈ K ⊔ B, g * z' = z' * g := fun g hg =>
    mul_comm_of_mem_normalizer_zpowers hz2 hz1 (h.norm_R0 hg)
  have h27 : 27 ∣ Nat.card ↥(co2P ⊓ Subgroup.centralizer
      ({z'} : Set (Equiv.Perm (Fin 2300)))) := by
    rw [← h.card_B]
    exact Subgroup.card_dvd_of_le fun b hb => Subgroup.mem_inf.2 ⟨hBP hb,
      Subgroup.mem_centralizer_singleton_iff.2 (hcomm b (Subgroup.mem_sup_right hb))⟩
  obtain ⟨g, hgP, hg⟩ := Co2Conj.exists_conj_locZ hz'P (by rw [← pow_two]; exact hz2) hz1 h27
  set ψ : Equiv.Perm (Fin 2300) →* Equiv.Perm (Fin 2300) := (MulAut.conj g).toMonoidHom
    with hψdef
  have hψ : Function.Injective ψ := (MulAut.conj g).injective
  have h' := h.map ψ hψ
  rw [MonoidHom.map_zpowers, show ψ z' = locZ from hg] at h'
  exact isExtraSpec2_of_map ψ hψ
    (stage_z h' (map_conj_le hgP hBP) (map_conj_le hgP hKP) (map_conj_le hgP hR1P))

end Model

section Row


theorem rowCo2_holds : I301BRow .co2 := rowCo2_of_model rowCo2_model

end Row

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
