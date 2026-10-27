module

public import CFSG.ClassicalInvolution.Q3.TL3T50
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Vec

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr CFSG.ClassicalInvolution.Generic

variable {n k : ℕ}

theorem perm_eq_one_of_fix_four (hn : 5 ≤ n) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ α : Finset (Fin n), α.card = 4 → α.map σ.toEmbedding = α) : σ = 1 := by
  classical
  refine Equiv.ext fun a => ?_
  by_contra hne
  rw [Equiv.Perm.one_apply] at hne
  obtain ⟨α, hαs, haα, hcard⟩ : ∃ α : Finset (Fin n), α ⊆ (Finset.univ.erase (σ a)) ∧ a ∈ α ∧
      α.card = 4 := by
    have hcu : 4 ≤ (Finset.univ.erase (σ a)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨α, h1, h2, h3⟩ := Finset.exists_subsuperset_card_eq (s := {a})
      (t := Finset.univ.erase (σ a))
      (by rw [Finset.singleton_subset_iff]; exact Finset.mem_erase.mpr ⟨fun h => hne h.symm,
        Finset.mem_univ _⟩)
      (by rw [Finset.card_singleton]; norm_num) hcu
    exact ⟨α, h2, Finset.singleton_subset_iff.mp h1, h3⟩
  have h1 : σ a ∈ α.map σ.toEmbedding := Finset.mem_map_of_mem _ haα
  rw [hσ α hcard] at h1
  exact (Finset.mem_erase.mp (hαs h1)).1 rfl

theorem exists_conj_memBar_map (w : Wr n) (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∃ b' : Bool, conjSub (mkQ n w) (memBar α h b) =
      memBar (α.map w.perm.toEmbedding) (by rw [Finset.card_map]; exact h) b' := by
  have hw : w = ofVec w.vec * ofPerm w.perm := (ofVec_mul_ofPerm w).symm
  obtain ⟨b₁, hb₁⟩ := exists_conj_ofPerm_memBar w.perm α h b
  have e1 : conjSub (mkQ n w) (memBar α h b) =
      conjSub (mkQ n (ofVec w.vec)) (memBar (α.map w.perm.toEmbedding)
        (by rw [Finset.card_map]; exact h) b₁) := by
    rw [← hb₁]
    conv_lhs => rw [hw]
    rw [map_mul, Generic.conjSub_mul]
    rfl
  rw [e1]
  rcases TL4.AECov.conjSub_memBar_of_perm_eq_one (w := ofVec w.vec) rfl (α.map w.perm.toEmbedding)
    (by rw [Finset.card_map]; exact h) b₁ with h2 | h2
  · exact ⟨true, h2⟩
  · exact ⟨false, h2⟩

@[expose] def pointVec (p : Fin n) : Fin n → ZMod 2 := fun x => if x = p then 1 else 0

@[expose] noncomputable def evenExt (c : Fin k ↪ Fin n) (p : Fin n) (v : Fin k → ZMod 2) :
    Fin n → ZMod 2 :=
  embWVec c v + (∑ i, v i) • pointVec p

theorem sum_embWVec (c : Fin k ↪ Fin n) (v : Fin k → ZMod 2) :
    ∑ x, embWVec c v x = ∑ i, v i := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map c))]
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => embWVec_apply c v i
  · intro x _ hx
    apply embWVec_of_not_mem
    rintro ⟨i, rfl⟩
    exact hx (Finset.mem_map_of_mem c (Finset.mem_univ i))

theorem sum_pointVec (p : Fin n) : ∑ x, pointVec p x = 1 := by
  classical
  rw [Finset.sum_eq_single p]
  · simp [pointVec]
  · intro x _ hx
    simp [pointVec, hx]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

theorem ofVec_evenExt_mem (c : Fin k ↪ Fin n) (p : Fin n) (v : Fin k → ZMod 2) :
    ofVec (evenExt c p v) ∈ aeSub n := by
  refine ⟨?_, ?_⟩
  · show ∑ x, evenExt c p v x = 0
    simp only [evenExt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_embWVec, sum_pointVec, mul_one]
    exact zmod_two_add_self _
  · show Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) = 1
    exact Equiv.Perm.sign_one

theorem embW_ofVec (c : Fin k ↪ Fin n) (v : Fin k → ZMod 2) :
    embW c (ofVec v) = ofVec (embWVec c v) := by
  refine Wr.ext rfl ?_
  show embWPerm c 1 = 1
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hx
    rw [embWPerm_apply]
    rfl
  · exact embWPerm_of_not_mem c 1 hx

theorem ofVec_comm_embW (c : Fin k ↪ Fin n) {u : Fin n → ZMod 2}
    (hu : ∀ x ∈ Set.range c, u x = 0) (a : Wr k) : ofVec u * embW c a = embW c a * ofVec u := by
  classical
  refine Wr.ext (funext fun x => ?_) ?_
  · rw [mul_vec, mul_vec]
    show u x + (embW c a).vec x = (embW c a).vec x + u ((embWPerm c a.perm).symm x)
    rw [add_comm]
    congr 1
    by_cases hx : x ∈ Set.range c
    · obtain ⟨i, rfl⟩ := hx
      rw [hu _ ⟨i, rfl⟩, hu]
      refine ⟨a.perm.symm i, ?_⟩
      rw [eq_comm, Equiv.symm_apply_eq, embWPerm_apply, Equiv.apply_symm_apply]
    · rw [show (embWPerm c a.perm).symm x = x by
        rw [Equiv.symm_apply_eq, embWPerm_of_not_mem c _ hx]]
  · show 1 * (embW c a).perm = (embW c a).perm * 1
    rw [one_mul, mul_one]

theorem conj_ofVec_evenExt (c : Fin k ↪ Fin n) {p : Fin n} (hp : p ∉ Set.range c)
    (v : Fin k → ZMod 2) (a : Wr k) :
    ofVec (evenExt c p v) * embW c a * (ofVec (evenExt c p v))⁻¹ =
      embW c (ofVec v * a * (ofVec v)⁻¹) := by
  have hs : ∀ x ∈ Set.range c, ((∑ i, v i) • pointVec p) x = 0 := by
    rintro _ ⟨i, rfl⟩
    have : c i ≠ p := fun h => hp ⟨i, h⟩
    simp [pointVec, this]
  have e : ofVec (evenExt c p v) = embW c (ofVec v) * ofVec ((∑ i, v i) • pointVec p) := by
    rw [evenExt, TL4.Mdl117.ofVec_add, embW_ofVec]
  have hc := ofVec_comm_embW c hs a
  rw [e, map_mul, map_mul, map_inv]
  calc embW c (ofVec v) * ofVec ((∑ i, v i) • pointVec p) * embW c a *
        (embW c (ofVec v) * ofVec ((∑ i, v i) • pointVec p))⁻¹
      = embW c (ofVec v) * (ofVec ((∑ i, v i) • pointVec p) * embW c a) *
          (ofVec ((∑ i, v i) • pointVec p))⁻¹ * (embW c (ofVec v))⁻¹ := by group
    _ = embW c (ofVec v) * embW c a * (embW c (ofVec v))⁻¹ := by rw [hc]; group

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {P Q : Set (Subgroup G)} {n k : ℕ}

theorem SubHyp.isPGroup_ker_restrict {I : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    (hk : 5 ≤ k) (hk2 : IsPGroup 2 I.φ.ker) : IsPGroup 2 (I.restrict hk h).φ.ker := by
  intro x
  have hx : (I.restrict hk h).φ (x : ↥(pSpan Q)) = 1 := x.2
  rw [AEIdent.restrict_apply] at hx
  have hp : h.pre x ∈ piSub k := (QuotientGroup.eq_one_iff _).mp hx
  have hsq : h.pre ((x : ↥(pSpan Q)) ^ 2) = 1 := by
    rw [map_pow]
    rcases mem_piSub.mp hp with h1 | h1
    · rw [h1, one_pow]
    · rw [h1, sq, allOnes_mul_self]
  obtain ⟨a, ha⟩ := h.isPGroup_ker_pre hk2 ⟨(x : ↥(pSpan Q)) ^ 2, hsq⟩
  refine ⟨a + 1, Subtype.ext ?_⟩
  have e := congrArg Subtype.val ha
  rw [Subgroup.coe_pow, Subgroup.coe_one] at e
  rw [Subgroup.coe_pow, Subgroup.coe_one, pow_succ', pow_mul]
  exact e

theorem SubHyp.restrict_label {I : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    (hk : 5 ≤ k) {L : Subgroup G} (hL : L ∈ Q) {α : Finset (Fin k)} (hα' : (α.map c).card = 4)
    {b : Bool} (hlab : (L.subgroupOf (pSpan P)).map I.φ = memBar (α.map c) hα' b) :
    ∃ (hα : α.card = 4) (b' : Bool), (L.subgroupOf (pSpan Q)).map (I.restrict hk h).φ =
      memBar α hα b' := by
  have hα : α.card = 4 := by rwa [Finset.card_map] at hα'
  obtain ⟨b', hb⟩ := exists_memBar_map_eq c α hα hα' b
  refine ⟨hα, b', ?_⟩
  rw [show (I.restrict hk h).φ = (mkQ k).comp h.pre from rfl, ← Subgroup.map_map,
    h.map_pre hL hα hα' hlab hb]
  rfl

omit [Finite G] in
theorem conj_mem_pSpan_of_conj {Z : Set (Subgroup G)} {g : G} (hg : ∀ L ∈ Z, conjSub g L ∈ Z)
    {y : G} (hy : y ∈ pSpan Z) : g * y * g⁻¹ ∈ pSpan Z := by
  have hle : pSpan Z ≤ (pSpan Z).comap (MulAut.conj g).toMonoidHom :=
    pSpan_le fun L hL l hl => le_pSpan (hg L hL) (conj_mem_conjSub hl)
  exact hle hy

end CFSG.ClassicalInvolution.Q3.TC.Thin
