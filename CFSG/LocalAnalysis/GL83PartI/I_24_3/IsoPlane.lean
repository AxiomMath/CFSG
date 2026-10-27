module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.Main

public section

namespace GL83.I243

open CFSG CFSG.Open CFSG.PreuniquenessRankFour.Helpers Subgroup CFSG.LieType.SeitzGeneration

section Rank

theorem le_pRank_sylow_of_isElemAbelian {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (R : Sylow p X) {E : Subgroup X} (hE : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ Open.pRank p (R : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hEQ⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R Q
  have hSg : ((g • R : Sylow p X) : Subgroup X) =
      (R : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hEP : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ (R : Subgroup X) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup X) := hEQ hx
    rw [← hg, hSg] at hxQ
    obtain ⟨y, hy, rfl⟩ := hxQ
    have hyR : y ∈ (R : Subgroup X) := hy
    have hconj : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom y) = y := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hconj]
    exact hyR
  exact CFSG.SectionRank.le_pRank hp.one_lt hEP (hE.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hk])

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.pRank_top_le (h : Cfg p R B K z) :
    Open.pRank p (⊤ : Subgroup ↥K) ≤ Open.pRank p (R : Subgroup X) := by
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank h.prime.one_lt (⊤ : Subgroup ↥K)
  exact le_pRank_sylow_of_isElemAbelian h.prime R (hE.map K.subtype)
    (by rw [Subgroup.card_map_of_injective K.subtype_injective, hEc])

theorem Cfg.pow_le_card_of_le_pRank (h : Cfg p R B K z) {k : ℕ}
    (hk : k ≤ Open.pRank p (⊤ : Subgroup ↥K)) : p ^ k ≤ Nat.card B := by
  rw [h.card_eq]
  exact Nat.pow_le_pow_right h.prime.pos (hk.trans h.pRank_top_le)

end Rank

section Planes

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {B K : Subgroup X} {z : X}

theorem Cfg.false_of_largePlane (h : Cfg p R B K z) {d : TauCeti.ValidLieTypeIndex}
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Cat d) (hB : p ^ 5 ≤ Nat.card B)
    (hplane : ∀ Ē : Subgroup (MulAut (Cat d)), IsElemAbelian p Ē → p ^ 4 ≤ Nat.card Ē →
      ∃ E : Subgroup (MulAut (Cat d)), E ≤ Ē ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
        PlaneGen E) :
    False := by
  have hperf : Group.IsPerfect ↥K := ⟨h.comp.2.2.1⟩
  obtain ⟨E4, hE4el, hE4card, hE4B⟩ := exists_elemAbelian_image (n := 4) h.prime h.normalizes
    h.elem h.mem_B h.order h.cen_le hB
  set ρ : MulAut ↥K →* MulAut (Cat d) := (MulAut.congr e).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥K) with hρdef
  have hρ : Function.Injective ρ := (MulAut.congr e).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective _)
  obtain ⟨E', hE'le, hE'el, hE'card, hE'gen⟩ := hplane (E4.map ρ) (hE4el.map ρ)
    (by rw [Subgroup.card_map_of_injective hρ, hE4card])
  set E : Subgroup (MulAut ↥K) := (E'.comap ρ) ⊓ E4 with hE
  have hmapE : E.map ρ = E' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨x, hx4, rfl⟩ := hE'le hy
      exact ⟨x, ⟨hy, hx4⟩, rfl⟩
  have hEel : IsElemAbelian p E := hE4el.mono inf_le_right
  have hEcard : Nat.card E = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hρ (K := E), hmapE, hE'card]
  have hcl := closure_fix_lift (p := p) hperf e (fun E'' => PlaneGen E'')
    (fun E'' _ _ hQ => hQ) E hEel hEcard (by rw [hmapE]; exact hE'gen)
  exact h.false_of_closure
    (h.closure_gens_eq_top (fun ε hε => hE4B ε (Subgroup.mem_inf.mp hε).2) hcl)

theorem Cfg.false_of_scope (h : Cfg p R B K z)
    {S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop}
    (hS : SeitzPlanes S) {d : TauCeti.ValidLieTypeIndex} (hchar : p ≠ d.1.characteristic)
    (hnex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException p d.1) (hsc : ∀ E, S d p E)
    (e : ↥K ⧸ Subgroup.center ↥K ≃* Cat d) : False := by
  have hperf : Group.IsPerfect ↥K := ⟨h.comp.2.2.1⟩
  obtain ⟨E, hEel, hEcard, hEB⟩ := exists_plane_image h.prime h.normalizes h.elem
    h.mem_B h.order h.cen_le h.three_le_card
  have hcl := closure_fix_lift hperf e (fun _ => True)
    (fun E' hE' hc _ => hS d p h.prime h.ne_two hchar hnex E' hE' hc (hsc E')) E hEel hEcard
    trivial
  exact h.false_of_closure (h.closure_gens_eq_top hEB hcl)

end Planes

end GL83.I243
