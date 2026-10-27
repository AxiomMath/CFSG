module

public import CFSG.Certificates.CentralizerPresented
public import CFSG.Certificates.CosetTableRelations

public section

namespace CFSG.Certificates

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

@[expose] def centState {m : ℕ} (ws : List (List (Fin m × Bool))) (i cap : ℕ) : St :=
  enumerateHLT (mkParams (2 * m) (invArr m) (codes ws) (centWords (2 * i) (codes ws))) cap

@[expose] def walkAll {m : ℕ} (ws : List (List (Fin m × Bool))) (i cap : ℕ)
    (us : List (List ℕ)) : Bool :=
  let st := centState ws i cap
  us.all fun w => walkRoot (2 * m) st.tab st.fwd st.next 1 w == some 1

theorem commute_of_walk {m : ℕ} (ws : List (List (Fin m × Bool))) {i : ℕ} (hi : i < m) (cap : ℕ)
    (hlet : ∀ s ∈ centWords (2 * i) (codes ws), ∀ c ∈ s, c < 2 * m)
    {us : List (List ℕ)} (h : walkAll ws i cap us = true) {w : List ℕ} (hw : w ∈ us)
    (hl : ∀ c ∈ w, c < 2 * m) :
    Commute (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk} (2 * i))
      (evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) w) := by
  set rels := {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
  set gen := presLetter rels
  set cw := centWords (2 * i) (codes ws) with hcw
  set x : PG m ws := PresentedGroup.of ⟨i, hi⟩
  have hx : gen (2 * i) = x := presLetter_two_mul hi
  set H : Subgroup (PG m ws) := Subgroup.closure {g | ∃ s ∈ cw, g = evalWord gen s}
  have hH : H ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have : Commute (gen (2 * i)) (evalWord gen s) := commute_of_mem_centWords (ws := ws) hi hs
    rw [hx] at this
    exact this.eq.symm
  have hg := goodParams ws [] H (by simp)
  have hgood : Good gen H (mkParams (2 * m) (invArr m) (codes ws) cw) := by
    refine ⟨hg.inv_lt, hg.gen_inv, ?_, ?_, ?_⟩
    · intro x' p hp
      exact hg.scans x' p (by simpa [presParams, mkParams] using hp)
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_subs hp
      exact ⟨hp1, hlet _ hp2, Subgroup.subset_closure ⟨_, hp2, rfl⟩⟩
    · intro p hp
      exact hg.rels p (by simpa [presParams, mkParams] using hp)
  have hinv := enumerateHLT_inv hgood cap
  unfold walkAll at h
  simp only [List.all_eq_true, beq_iff_eq] at h
  have hwalk := h w hw
  have hrel := walkRoot_spec hinv (centState ws i cap).next w 1 1 hl (by
    have := hinv.next_two; omega) hwalk
  rw [rel_iff, Inv.rep_one hinv, one_mul, inv_one, mul_one] at hrel
  have hmem := hH hrel
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  show Commute (gen (2 * i)) (evalWord gen w)
  rw [hx]
  exact hmem.symm

theorem conj_eq_of_commute_mul_inv {G : Type*} [Group G] (a g g' : G)
    (h : Commute a (g * g'⁻¹)) : g⁻¹ * a * g = g'⁻¹ * a * g' := by
  have h3 : (g * g'⁻¹)⁻¹ * a * (g * g'⁻¹) = a := by
    have := h.eq
    calc (g * g'⁻¹)⁻¹ * a * (g * g'⁻¹) = (g * g'⁻¹)⁻¹ * (a * (g * g'⁻¹)) := by group
      _ = (g * g'⁻¹)⁻¹ * ((g * g'⁻¹) * a) := by rw [this]
      _ = a := by group
  calc g⁻¹ * a * g = g'⁻¹ * ((g * g'⁻¹)⁻¹ * a * (g * g'⁻¹)) * g' := by group
    _ = g'⁻¹ * a * g' := by rw [h3]

end CFSG.Certificates
