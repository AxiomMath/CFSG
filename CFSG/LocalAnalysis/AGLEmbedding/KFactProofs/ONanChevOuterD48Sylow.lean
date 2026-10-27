module

public import Certificates.Certificate9640

public section

open CFSG.Open

namespace CFSG.AGLEmbedding.ChevOuterD48

theorem sylowGroup_facts :
    Nat.card sylowGroup = 3 ^ 6 ∧
      ∀ E : Subgroup (GL (Fin 8) GF512), E ≤ sylowGroup → IsElemAbelian 3 E →
        Nat.card E ≤ 3 ^ 2 :=
  Certificates.certificate9640

theorem isElemAbelian_of_equiv_le_d48 {p : ℕ} {G H : Type*} [Group G] [Group H] {U : Subgroup H}
    (hU : IsElemAbelian p U) {D : Subgroup H} (hDU : D ≤ U) {D₀ : Subgroup G} (f : D₀ ≃* D) :
    IsElemAbelian p D₀ := by
  refine ⟨⟨⟨fun y z => ?_⟩⟩, fun y hy => ?_⟩
  · apply f.injective
    rw [map_mul, map_mul]
    have := hU.1.is_comm.comm ⟨(f y : H), hDU (f y).2⟩ ⟨(f z : H), hDU (f z).2⟩
    have h := congrArg Subtype.val this
    exact Subtype.ext h
  · have h1 := hU.2 (f ⟨y, hy⟩ : H) (hDU (f ⟨y, hy⟩).2)
    have h2 : f ((⟨y, hy⟩ : D₀) ^ p) = f 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using h1)
    have h3 := f.injective h2
    simpa using congrArg Subtype.val h3

theorem rank_le_of_sylow_card {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    (S : Subgroup G) (hS : Nat.card S = p ^ (Nat.card G).factorization p)
    (h : ∀ E : Subgroup G, E ≤ S → IsElemAbelian p E → Nat.card E ≤ p ^ k)
    (E : Subgroup G) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ k := by
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x.1 x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (Sylow.ofCard S hS)
  have hQ : ((g • Q : Sylow p G) : Subgroup G) =
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ S := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEQ
    rw [← hQ, hg] at this
    exact this
  have hf : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have := h _ hle (isElemAbelian_of_equiv_le_d48 hE le_rfl
    (Subgroup.equivMapOfInjective E _ hf).symm)
  rwa [Subgroup.card_map_of_injective hf] at this

theorem sylowGroup_le_range {L : Type*} [Group L] (ψ : L →* GL (Fin 8) GF512)
    (hmem : ∀ k, k < 24 → letterGL k ∈ ψ.range) : sylowGroup ≤ ψ.range := by
  have hw : ∀ w : List ℕ, (∀ l ∈ w, l < 24) → wordGL w ∈ ψ.range := fun w hw =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact hmem l (hw l hl)
  rw [sylowGroup, Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact hw _ sylowWordA_lt
  · exact Subgroup.pow_mem _ (hw _ sylowWordT_lt) _

theorem rank_le_nine_of_letters {L : Type*} [Group L] [Finite L]
    (ψ : L →* GL (Fin 8) GF512) (hψ : Function.Injective ψ)
    (hmem : ∀ k, k < 24 → letterGL k ∈ ψ.range)
    (hcard : (Nat.card L).factorization 3 = 6) :
    ∀ E : Subgroup L, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hP, hrank⟩ := sylowGroup_facts
  have hle := sylowGroup_le_range ψ hmem
  have hmap : (sylowGroup.comap ψ).map ψ = sylowGroup := Subgroup.map_comap_eq_self hle
  refine fun E hE => rank_le_of_sylow_card (sylowGroup.comap ψ) ?_ ?_ E hE
  · have h1 : Nat.card (sylowGroup.comap ψ) = Nat.card sylowGroup := by
      have := Subgroup.card_map_of_injective (K := sylowGroup.comap ψ) hψ
      rw [hmap] at this
      exact this.symm
    rw [h1, hP, hcard]
  · intro E' hE' hEA
    have hmap' : E'.map ψ ≤ sylowGroup := by
      rw [← hmap]
      exact Subgroup.map_mono hE'
    have := hrank (E'.map ψ) hmap'
      (isElemAbelian_of_equiv_le_d48 hEA le_rfl (Subgroup.equivMapOfInjective E' ψ hψ).symm)
    rwa [Subgroup.card_map_of_injective hψ] at this

end CFSG.AGLEmbedding.ChevOuterD48
