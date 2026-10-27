module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L120A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

private theorem sec120_t_not_mem_B (F : Sec12Frame t L S) : t ∉ secB S L :=
  fun htB => sec120_t_not_mem_L F (F.bdata.1 htB)

theorem sec120_relIndex_BA (F : Sec12Frame t L S) :
    (secB S L).relIndex (secA t S L) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), ?_⟩
  intro b hbA
  rw [Xor]
  rcases (sec12E_mem_A F).mp hbA with hbB | ⟨b0, hb0, rfl⟩
  · refine Or.inr ⟨hbB, ?_⟩
    intro hbt
    have hmem : b⁻¹ * (b * t) ∈ secB S L :=
      (secB S L).mul_mem ((secB S L).inv_mem hbB) hbt
    exact sec120_t_not_mem_B F (by simpa [mul_assoc] using hmem)
  · refine Or.inl ⟨?_, ?_⟩
    · have hbt : (t * b0) * t = b0 := by
        rw [mul_assoc, ← sec12E_t_comm_B F hb0, ← mul_assoc, sec12E_t_sq F, one_mul]
      rw [hbt]
      exact hb0
    · intro htb
      have hmem : (t * b0) * b0⁻¹ ∈ secB S L :=
        (secB S L).mul_mem htb ((secB S L).inv_mem hb0)
      exact sec120_t_not_mem_B F (by simpa [mul_assoc] using hmem)

theorem sec120_relIndex_A (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) : (secA t S L).relIndex E = 16 := by
  let ψ : ↥E →* ↥(secB S L) :=
    { toFun := fun e => ⟨sec12f t (e : G), sec12E_f_mem F (hE.1 e.2)⟩
      map_one' := by
        apply Subtype.ext
        simp [sec12f]
      map_mul' := by
        intro e e'
        apply Subtype.ext
        exact sec12E_f_mul F (hE.1 e.2) (hE.1 e'.2) }
  have hsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨e, he, hfe⟩ := sec120_f_surj_E F hE b.2
    exact ⟨⟨e, he⟩, Subtype.ext hfe⟩
  have hker : ψ.ker = (secA t S L).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    exact sec120_f_eq_one_iff F hE e.2
  calc (secA t S L).relIndex E = ((secA t S L).subgroupOf E).index := rfl
    _ = ψ.ker.index := by rw [hker]
    _ = Nat.card ψ.range := Subgroup.index_ker ψ
    _ = Nat.card ↥(secB S L) := by
          rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    _ = 2 ^ 4 := F.bdata.2.1
    _ = 16 := by norm_num

theorem sec120_relIndex_B (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) : (secB S L).relIndex E = 32 := by
  have h := Subgroup.relIndex_mul_relIndex (H := secB S L) (K := secA t S L) (L := E)
    le_sup_left (sec120_A_le_E F hE)
  rw [sec120_relIndex_BA F, sec120_relIndex_A F hE] at h
  norm_num at h
  exact h.symm

end CFSG.OddStandard.SmallF3.Omega
