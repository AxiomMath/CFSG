module

public import CFSG.LargeExtraspecial.S13Hyp
public import CFSG.LargeExtraspecial.S4Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

omit [Finite G] in
theorem clSub_inf {A B : Subgroup G} (hzB : S.z ∈ B) :
    S.clSub A ⊓ S.clSub B = S.clSub (A ⊓ B) := by
  refine le_antisymm (fun v ⟨hv₁, hv₂⟩ => ?_) (le_inf (S.clSub_mono inf_le_left)
    (S.clSub_mono inf_le_right))
  obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv₁
  obtain ⟨y, hy, hyQ, hyx⟩ := S.mem_clSub_iff.mp hv₂
  rcases (S.cl_eq_cl_iff hyQ hxQ).mp hyx with e | e
  · exact S.cl_mem_clSub ⟨hx, e ▸ hy⟩ hxQ
  · exact S.cl_mem_clSub ⟨hx, e ▸ mul_mem hy hzB⟩ hxQ

namespace Hyp13

variable (Y : Hyp13 S g K)
include Y

theorem exists_ρ_eq {k : S.O} (hk : k ∈ K) : ∃ m : S.M, S.ρ m = k :=
  MonoidHom.mem_range.mp (Y.K_le hk)

omit Y in
theorem Ebar_le_Lbar_mul {m : S.M} (hm : S.ρ m ∈ K) : Ebar S g K ≤ S.Lbar ((m : G) * g) := by
  intro x hx
  rw [mem_Lbar_mul_iff S m g]
  have hc := ((mem_Ebar).mp hx).2 _ hm
  have e : (S.ρ m)⁻¹ * x * S.ρ m = x := by
    calc (S.ρ m)⁻¹ * x * S.ρ m = (S.ρ m)⁻¹ * (S.ρ m * x) := by rw [hc]; group
      _ = x := by group
  rw [e]
  exact Ebar_le_Lbar hx

theorem cl_mul_ne {m : S.M} (hm : S.ρ m ∈ K) (hm1 : S.ρ m ≠ 1) :
    S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹) := by
  rw [← ρ_cl_conj_z S m Y.haQ]
  intro e
  exact cl_conj_z_ne_zero S Y.haQ Y.hne (fix_eq_zero Y.card_K Y.fpf hm hm1 _ e)

theorem mem_Qa {m : S.M} (hm : S.ρ m ∈ K) :
    (m : G) * g * S.z * ((m : G) * g)⁻¹ ∈ S.Qa g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEL := Ebar_le_Lbar_mul (g := g) hm
  refine lemma_4_3_core Y.H Y.C m (D := Ebar S g K) ((isPGroup_Lbar S Y.haQ).to_le Ebar_le_Lbar)
    (Ebar_le_Lbar.trans le_sup_left) (sup_le ?_ ?_) ?_ ?_
  · intro x hx
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have hc := S4.Lbar_comm S Y.haQ hx (Ebar_le_Lbar he)
      rw [hc, mul_inv_cancel_right]; exact he
    · intro he
      have he' : e = x⁻¹ * (x * e * x⁻¹) * x := by group
      have hc := S4.Lbar_comm S Y.haQ (inv_mem hx) (Ebar_le_Lbar he)
      rw [he', hc, inv_mul_cancel_right]; exact he
  · intro x hx
    have haQ' := conj_mem_QG' S m.2 Y.haQ
    rw [mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have hc := S4.Lbar_comm S haQ' hx (hEL he)
      rw [hc, mul_inv_cancel_right]; exact he
    · intro he
      have he' : e = x⁻¹ * (x * e * x⁻¹) * x := by group
      have hc := S4.Lbar_comm S haQ' (inv_mem hx) (hEL he)
      rw [he', hc, inv_mul_cancel_right]; exact he
  · intro hle
    obtain ⟨x, hx, hxE⟩ := exists_not_mem_Ebar Y.H Y.fpf (K := K)
    exact hxE (hle hx)
  · intro x hx y hy hxE hyE
    exact Y.mul_mem_E hx hxE hy hyE

theorem Ebar_eq_inf {m : S.M} (hm : S.ρ m ∈ K) (hm1 : S.ρ m ≠ 1) :
    Ebar S g K = S.Lbar g ⊓ S.Lbar ((m : G) * g) := by
  refine le_antisymm (le_inf Ebar_le_Lbar (Ebar_le_Lbar_mul (g := g) hm)) ?_
  rintro x ⟨hxL, hxL'⟩
  by_contra hxE
  apply Y.cl_mul_ne hm hm1
  have hle : S.Lbar g ≤ S.Lbar ((m : G) * g) := by
    intro y hy
    by_cases hyE : y ∈ Ebar S g K
    · exact Ebar_le_Lbar_mul (g := g) hm hyE
    · have h1 := Ebar_le_Lbar_mul (g := g) hm (Y.mul_mem_E hy hyE hxL hxE)
      have e : y = y * x * x⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 (inv_mem hxL')
  have hcard : Nat.card (S.Lbar ((m : G) * g)) = Nat.card (S.Lbar g) := by
    rw [Lbar_mul S m g, Subgroup.card_map_of_injective (MulAut.conj (S.ρ m)).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
  have h1 := (Y.H.mul m).fixSub_eq
  rw [← heq, Y.H.fixSub_eq] at h1
  have hmem : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rw [h1]; exact Submodule.mem_span_singleton_self _
  rcases mem_span_cl_iff.mp hmem with h0 | h0
  · exact absurd h0 (cl_conj_z_ne_zero S (conj_mem_QG' S m.2 Y.haQ) (conj_ne_z' S m.2 Y.hne))
  · exact h0

theorem timmesfeld_13_1 {m : S.M} (hm : S.ρ m ∈ K) (hm1 : S.ρ m ≠ 1) :
    S.clSub (S.QG ⊓ S.Qa g ⊓ S.Qa ((m : G) * g)) = Fbar S g K := by
  have hαQ := conj_mem_QG' S m.2 Y.haQ
  have hαz := conj_ne_z' S m.2 Y.hne
  have hαa := Y.mem_Qa hm
  have hne : (m : G) * g * S.z * ((m : G) * g)⁻¹ ≠ g * S.z * g⁻¹ := fun e =>
    Y.cl_mul_ne hm hm1 (by rw [e])
  have haα : g * S.z * g⁻¹ ∈ S.Qa ((m : G) * g) := S.mem_Qa_symm hne hαa
  refine le_antisymm ?_ ?_
  ·
    intro v hv e he
    obtain ⟨x, hx, hxQ, rfl⟩ := S.mem_clSub_iff.mp hv
    have h1 := Lbar_apply_sub_mem_span' Y.haQ (S.cl_mem_clSub ⟨hxQ, hx.1.2⟩ hxQ)
      (Ebar_le_Lbar he)
    have h2 := Lbar_apply_sub_mem_span' hαQ (S.cl_mem_clSub ⟨hxQ, hx.2⟩ hxQ)
      (Ebar_le_Lbar_mul (g := g) hm he)
    rcases mem_span_cl_iff.mp h1 with h1 | h1
    · exact sub_eq_zero.mp h1
    · rcases mem_span_cl_iff.mp h2 with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd (h1.symm.trans h2) (Y.cl_mul_ne hm hm1).symm
  · obtain ⟨k, hk⟩ : ∃ k, k = S.ρ m := ⟨_, rfl⟩
    rw [Fbar_eq_span Y.H Y.card_K Y.normal Y.fpf (hk ▸ hm) (hk ▸ hm1), Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact S.cl_mem_clSub ⟨⟨Y.haQ, S.conj_z_mem_Qa g⟩, haα⟩ Y.haQ
    · simp only [hk]
      rw [ρ_cl_conj_z S m Y.haQ]
      exact S.cl_mem_clSub ⟨⟨hαQ, hαa⟩, S.conj_z_mem_Qa _⟩ hαQ

theorem Ebar_apply_sub_mem_Fbar {v : S.Qt} (hv : ∀ f ∈ Fbar S g K, polar S.q v f = 0)
    {e : S.O} (he : e ∈ Ebar S g K) : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Fbar S g K := by
  obtain ⟨k, hk, hk1⟩ := Y.exists_K
  obtain ⟨m, rfl⟩ := Y.exists_ρ_eq hk
  have hαQ := conj_mem_QG' S m.2 Y.haQ
  obtain ⟨x, hxQ, rfl⟩ := S.exists_cl v
  have hxa : x ∈ S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G) := by
    refine ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩
    have := hv _ (cl_mem_Fbar Y.H)
    exact (S.polar_cl_eq_zero_iff hxQ Y.haQ).mp this
  have hxα : x ∈ S.QG ⊓ centralizer ({(m : G) * g * S.z * ((m : G) * g)⁻¹} : Set G) := by
    refine ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩
    have hαF : S.cl ((m : G) * g * S.z * ((m : G) * g)⁻¹) ∈ Fbar S g K := by
      rw [← ρ_cl_conj_z S m Y.haQ]
      exact apply_mem_Fbar_of_mem_K hk (cl_mem_Fbar Y.H)
    have := hv _ hαF
    exact (S.polar_cl_eq_zero_iff hxQ hαQ).mp this
  have h1 := Y.C.comm_le x hxa e (Ebar_le_Lbar he)
  have h2 := (Y.C.mul m).comm_le x hxα e (Ebar_le_Lbar_mul (g := g) hk he)
  rw [← Y.timmesfeld_13_1 hk hk1, ← clSub_inf (S.z_mem_Qa hαQ (conj_ne_z' S m.2 Y.hne))]
  exact ⟨h1, S.clSub_mono inf_le_right h2⟩

end Hyp13

end CFSG.LargeExtraspecial.S13
