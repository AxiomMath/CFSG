module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
import CFSG.Sporadic.Bridge.Fi24Surj
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BFi24TwoA
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.Sporadic.Fi24 (R J jR jR_injective range_jR card_R card_J)
open CFSG.Sporadic.FischerOddCore (fi24R2 fi24AutEquiv fi24_mem_JR_iff)

private theorem coe_mem_of_mem_commutator {G : Type*} [Group G] {N : Subgroup G}
    (hN : N.index = 2) {H : Subgroup G} {x : H} (hx : x ∈ commutator H) : (x : G) ∈ N := by
  have hle : commutator H ≤ N.comap H.subtype := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def,
      Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN,
      Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff, inv_mem_iff]
    tauto
  exact hle hx

private theorem isElemAbelian_comap_of_inj {G H : Type*} [Group G] [Group H] {p : ℕ}
    {B : Subgroup H} (hB : IsElemAbelian p B) {f : G →* H} (hf : Function.Injective f) :
    IsElemAbelian p (B.comap f) := by
  have := hB.1
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩,
    fun x hx => hf (by rw [map_pow, hB.2 _ hx, map_one])⟩
  have hc := congrArg Subtype.val (mul_comm' (⟨f a, a.2⟩ : B) ⟨f b, b.2⟩)
  simpa using hc

private theorem mulAutCongr_conj {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) :=
  MulEquiv.ext fun y => by simp

private theorem exists_mulEquiv_of_index_two {A G H : Type} [Group A] [Group G] [Group H]
    (e : A ≃* H) (j : G →* H) (hj : Function.Injective j) (hcard : Nat.card H = 2 * Nat.card G)
    (hG : Nat.card G ≠ 0) {P : Subgroup A} (hinn : ∀ x ∈ P, e x ∈ j.range)
    {R0 : Subgroup A} (hR0 : IsExtraSpec2 R0) (hR0c : 16 ≤ Nat.card R0) {z : A} (hz : z ∈ R0)
    (hzc : ∀ r ∈ R0, r * z = z * r) (hz1 : z ≠ 1) {B : Subgroup A} (hBP : B ≤ P)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 5) (hBz : ∀ b ∈ B, b * z = z * b)
    (hBR : B ≤ Subgroup.normalizer (R0 : Set A)) {r : G}
    (hconj : ∀ t : G, t * t = 1 → t ≠ 1 → ∀ E T : Subgroup G,
      E ≤ Subgroup.centralizer {t} → IsElemAbelian 3 E → Nat.card E = 3 ^ 5 → IsPGroup 2 T →
      T ≤ Subgroup.centralizer {t} → E ≤ Subgroup.normalizer (T : Set G) → 8 ≤ Nat.card T →
      IsConj t r) :
    ∃ e' : A ≃* H, e' z = j r ∧ ∀ x ∈ P, e' x ∈ j.range := by
  set f := e.symm.toMonoidHom.comp j with hfdef
  have hf : Function.Injective f := e.symm.injective.comp hj
  have hPf : P ≤ f.range := fun x hx => by
    obtain ⟨g, hg⟩ := hinn x hx
    exact ⟨g, by rw [hfdef, MonoidHom.comp_apply, hg]; exact e.symm_apply_apply x⟩
  have hidx : f.range.index = 2 := by
    have h := Subgroup.card_mul_index f.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_congr e.toEquiv,
      hcard] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hG) (h.trans (mul_comm 2 _))
  have hzZ : (⟨z, hz⟩ : R0) ∈ Subgroup.center R0 :=
    Subgroup.mem_center_iff.2 fun x => Subtype.ext (hzc x x.2)
  have hz2 : z * z = 1 := by
    have h := pow_card_eq_one' (G := Subgroup.center R0) (x := ⟨_, hzZ⟩)
    rw [hR0.2.2.2, pow_two] at h
    exact congrArg (fun y : Subgroup.center R0 => ((y : R0) : A)) h
  obtain ⟨t, rfl⟩ : z ∈ f.range :=
    coe_mem_of_mem_commutator hidx (x := ⟨z, hz⟩) (by rw [hR0.2.1, hR0.2.2.1]; exact hzZ)
  have ht2 : t * t = 1 := hf (by rw [map_mul, hz2, map_one])
  have ht1 : t ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hEc : Nat.card (B.comap f) = 3 ^ 5 := by
    rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq_self (hBP.trans hPf), hBc]
  have hTc : 8 ≤ Nat.card (R0.comap f) := by
    haveI := Subgroup.normal_of_index_eq_two hidx
    have h1 := Subgroup.relIndex_mul_card f.range R0
    have h2 := Nat.le_of_dvd (by norm_num)
      (hidx ▸ Subgroup.relIndex_dvd_index_of_normal f.range R0)
    rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq]
    by_contra hlt
    have := Nat.mul_le_mul h2 (Nat.le_of_lt_succ (not_le.1 hlt))
    omega
  obtain ⟨c, hc⟩ := isConj_iff.1 (hconj t ht2 ht1 (B.comap f) (R0.comap f)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (hf (by rw [map_mul, map_mul]; exact hBz _ hx)))
    (isElemAbelian_comap_of_inj hB hf) hEc (hR0.1.comap_of_injective f hf)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
      (hf (by rw [map_mul, map_mul]; exact hzc _ hx)))
    ((Subgroup.comap_mono hBR).trans (Subgroup.le_normalizer_comap f)) hTc)
  refine ⟨e.trans (MulAut.conj (j c)), ?_, fun x hx => ?_⟩
  · show j c * e (e.symm (j t)) * (j c)⁻¹ = j r
    rw [MulEquiv.apply_symm_apply, ← map_inv, ← map_mul, ← map_mul, hc]
  · rw [MulEquiv.trans_apply, MulAut.conj_apply]
    exact j.range.mul_mem (j.range.mul_mem ⟨c, rfl⟩ (hinn x hx)) (j.range.inv_mem ⟨c, rfl⟩)


theorem exists_mulEquiv_fi24R {S : Type} [Group S] [Finite S]
    (hS : catalogIs S (sporIs .Fi24Prime)) {R0 : Subgroup (MulAut S)} (hR0 : IsExtraSpec2 R0)
    (hR0c : 16 ≤ Nat.card R0) {z : MulAut S} (hz : z ∈ R0) (hzc : ∀ r ∈ R0, r * z = z * r)
    (hz1 : z ≠ 1) {B : Subgroup (MulAut S)} (hBi : B ≤ (MulAut.conj : S →* MulAut S).range)
    (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 5) (hBz : ∀ b ∈ B, b * z = z * b)
    (hBR : B ≤ Subgroup.normalizer (R0 : Set (MulAut S))) :
    ∃ e : MulAut S ≃* CFSG.Sporadic.Fi24.R, e z = jR fi24R2 ∧
      ∀ x ∈ (MulAut.conj : S →* MulAut S).range, e x ∈ jR.range := by
  obtain ⟨e₀, hinn⟩ : ∃ e₀ : MulAut S ≃* R,
      ∀ x ∈ (MulAut.conj : S →* MulAut S).range, e₀ x ∈ jR.range := by
    obtain ⟨i, hi, ⟨φ⟩⟩ := hS
    simp only [sporIs] at hi
    subst hi
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    refine ⟨(@MulAut.congr S _ Blueprint.NativeSporadic.Fi24prime Units.instGroup
      (φ.trans b.symm)).trans fi24AutEquiv.symm, ?_⟩
    rintro _ ⟨s, rfl⟩
    rw [range_jR]
    refine (fi24_mem_JR_iff _).2 ⟨(φ.trans b.symm) s, ?_⟩
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact @mulAutCongr_conj S _ _ Units.instGroup (φ.trans b.symm) s
  have key := exists_mulEquiv_of_index_two (A := MulAut S) (G := J) (H := R)
  exact key e₀ jR jR_injective (by rw [card_R, card_J]) (by rw [card_J]; norm_num) hinn hR0
    hR0c hz hzc hz1 hBi hB hBc hBz hBR fun t ht2 ht1 E T h1 h2 h3 h4 h5 h6 h7 =>
      isConj_fi24R2_of_elemAbelian ht2 ht1 h1 h2 h3 h4 h5 h6 h7

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
