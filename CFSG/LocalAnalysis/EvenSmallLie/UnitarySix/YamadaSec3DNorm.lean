module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DObj

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open scoped commutatorElement

section Perm

theorem chP2_le : chP2.grp ≤ chLam.grp ⊔ chSig.grp ⊔ chA3.grp := by
  refine grp_le fun w hw => ?_
  have hw' : w ∈ chLam.gens ∨ w ∈ chSig.gens ∨ w ∈ chA3.gens := by
    revert w
    decide
  rcases hw' with h | h | h
  · exact mem_sup_left (mem_sup_left (wP_mem_grp h))
  · exact mem_sup_left (mem_sup_right (wP_mem_grp h))
  · exact mem_sup_right (wP_mem_grp h)

theorem chP2_le_normalizer : chP2.grp ≤ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
  chP2_le.trans (sup_le (sup_le xNorm_spec.2.1 xNorm_spec.2.2.1) le_normalizer)

theorem chA1_le_chP2 : chA1.grp ≤ chP2.grp := grp_le_of_subset (by decide)

theorem normalizer_fixF {g : Equiv.Perm (Fin 693)}
    (hg : g ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693)))) {p : Fin 693}
    (hp : (p : ℕ) ∈ fixF) : ((g p : Fin 693) : ℕ) ∈ fixF := by
  refine (xFix_spec.1 (g p)).1 fun w hw => ?_
  have h1 : g⁻¹ * wP w * g⁻¹⁻¹ ∈ chA3.grp :=
    (mem_normalizer_iff.1 (inv_mem hg) (wP w)).1 (wP_mem_grp hw)
  have h2 := (xFix_spec.1 p).2 hp
  have h3 : ∀ x ∈ chA3.grp, x p = p := fun x hx => by
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w', hw', rfl⟩ := hx
      exact h2 w' hw'
    | one => rfl
    | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
    | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]
  have := h3 _ h1
  simp only [inv_inv, Equiv.Perm.mul_apply] at this
  rw [Equiv.Perm.inv_eq_iff_eq] at this
  exact this

theorem normalizer_chA3_le {g : Equiv.Perm (Fin 693)} (hT : g ∈ T46)
    (hg : g ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693)))) : g ∈ chP2.grp := by
  obtain ⟨q, hq, hq0⟩ := xFix_spec.2 (g 0) (normalizer_fixF hg (by decide))
  have hqlt : ∀ k ∈ q, k < 18 ∧ [k] ∈ chP2.gens := by
    have : ∀ q' ∈ qF, ∀ k ∈ q', k < 18 ∧ [k] ∈ chP2.gens := by decide
    exact this q hq
  have hqP : wP q ∈ chP2.grp := wP_mem_of_letters q fun k hk => (hqlt k hk).2
  have hqT : wP q ∈ T46 := wP_mem_T46 q fun k hk => (hqlt k hk).1
  set h := wP q * g with hdef
  have hh0 : h 0 = 0 := by rw [hdef, Equiv.Perm.mul_apply, hq0]
  have hhT : h ∈ T46 := mul_mem hqT hT
  have hhN : h ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
    mul_mem (chP2_le_normalizer hqP) hg
  have hhKA : h ∈ chK1A1.grp := by
    rw [← stabilizer_zero_eq]
    exact ⟨⟨h, hhT⟩, MulAction.mem_stabilizer_iff.2 (by
      show (h : Equiv.Perm (Fin 693)) 0 = 0
      exact hh0), rfl⟩
  rw [chK1A1_eq] at hhKA
  have hx2 : h ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hhKA
  rw [coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
  obtain ⟨k, hk, a, ha, hka⟩ := hx2
  have haP : a ∈ chP2.grp := chA1_le_chP2 ha
  have hkN : k ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) := by
    have : k = h * a⁻¹ := by rw [← hka]; group
    rw [this]
    exact mul_mem hhN (inv_mem (chP2_le_normalizer haP))
  have hkP : k ∈ chP2.grp :=
    p2_spec k hk fun w hw => (mem_normalizer_iff.1 hkN (wP w)).1 (wP_mem_grp hw)
  have hgP : g = (wP q)⁻¹ * h := by rw [hdef]; group
  rw [hgP, ← hka]
  exact mul_mem (inv_mem hqP) (mul_mem hkP haP)

end Perm

section GLevel

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem d_NLA₃_le_gen :
    (sec3DData e t).NLA₃ ≤ (sec3DData e t).Λ ⊔ (sec3DData e t).Sig ⊔ (sec3DData e t).A₃ := by
  intro x hx
  have hx' : x ∈ normalizer ((sec3DData e t).A₃ : Set G) ⊓ L := ⟨hx.2, hx.1⟩
  rw [show (sec3DData e t).A₃ = toG e chA3.grp from rfl, normalizer_toG (grp_le_T46 gensOK_chA3)]
    at hx'
  have hle : toG e (normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) ⊓ T46) ≤
      toG e chLam.grp ⊔ toG e chSig.grp ⊔ toG e chA3.grp := by
    rw [← toG_sup (grp_le_T46 gensOK_chLam) (grp_le_T46 gensOK_chSig),
      ← toG_sup (sup_le (grp_le_T46 gensOK_chLam) (grp_le_T46 gensOK_chSig))
        (grp_le_T46 gensOK_chA3)]
    exact toG_mono fun g hg => chP2_le (normalizer_chA3_le hg.2 hg.1)
  exact hle hx'

end GLevel

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
