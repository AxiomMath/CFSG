module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuInv

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.BenderSuzuki.PFAppendixIII
open CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ

namespace RuQCode

@[expose] def ppTab : List (List Nat) := [[], [1, 2, 3], [4, 8, 12], [10, 69, 79], [16, 32, 48],
  [33, 210, 243], [20, 168, 188], [117, 171, 222]]

@[expose] def ppOf (t : Fin 8) : List Nat := ppTab.getD t.val []

theorem ppOf_xor : ∀ t : Fin 8, ∀ a ∈ 0 :: ppOf t, ∀ b ∈ 0 :: ppOf t, a ^^^ b ∈ 0 :: ppOf t := by
  decide

theorem ppOf_sing : ∀ t : Fin 8, ∀ m ∈ ppOf t, qC m = 0 := by
  decide

theorem ppOf_orth : ∀ t : Fin 8, ∀ a ∈ ppOf t, ∀ b ∈ ppOf t, bC a b = 0 := by
  decide

theorem ppOf_length : ∀ t : Fin 8, t ≠ 0 → (0 :: ppOf t).length = 4 := by
  decide

theorem ppOf_nodup : ∀ t : Fin 8, (0 :: ppOf t).Nodup := by
  decide

theorem ppOf_lt : ∀ t : Fin 8, ∀ m ∈ ppOf t, m < 256 := by
  decide

theorem ppOf_equiv_check : (glList.all fun r => let A := adMat r
    all8.all fun t => (ppOf t).all fun m => (ppOf (linApply r t)).contains (maskApply A m)) =
      true := by
  decide +kernel

theorem ppOf_equiv {r : Lin8} (hr : r ∈ glList) {t : Fin 8} {m : Nat} (hm : m ∈ ppOf t) :
    maskApply (adMat r) m ∈ ppOf (linApply r t) := by
  have h := ppOf_equiv_check
  simp only [List.all_eq_true, List.contains_iff_mem] at h
  exact h r hr t (by simp [all8]) m hm

theorem bC_zero_left (n : Nat) : bC 0 n = 0 := by
  simp only [bC, Nat.zero_xor]
  rw [show qC 0 = 0 from rfl, RuSimCode.fin8_xor_zero, RuSimCode.fin8_xor_self]

theorem bC_zero_right (m : Nat) : bC m 0 = 0 := by
  simp only [bC, Nat.xor_zero]
  rw [show qC 0 = 0 from rfl, RuSimCode.fin8_xor_self, RuSimCode.fin8_zero_xor]

theorem maskApply_zero (cols : List Nat) : maskApply cols 0 = 0 := by
  simp [maskApply, sel]

end RuQCode

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_length_mul_card {α : Type*} [DecidableEq α] {H K : Subgroup G} (hKH : K ≤ H)
    (f : G → α) (l : List α) (hl : l.Nodup) (hf : ∀ a ∈ H, f a ∈ l)
    (hsurj : ∀ c ∈ l, ∃ a ∈ H, f a = c)
    (hiff : ∀ a ∈ H, ∀ b ∈ H, f a = f b ↔ a⁻¹ * b ∈ K) :
    Nat.card H = l.length * Nat.card K := by
  have hF : ∀ q : H ⧸ K.subgroupOf H, f ((q.out : H) : G) ∈ l.toFinset := fun q =>
    List.mem_toFinset.mpr (hf _ (q.out).2)
  have hbij : Function.Bijective
      (fun q : H ⧸ K.subgroupOf H => (⟨f ((q.out : H) : G), hF q⟩ : l.toFinset)) := by
    constructor
    · intro q q' h
      have h1 : f ((q.out : H) : G) = f ((q'.out : H) : G) := congrArg Subtype.val h
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
        mem_subgroupOf]
      exact (hiff _ (q.out).2 _ (q'.out).2).mp h1
    · rintro ⟨c, hc⟩
      obtain ⟨a, ha, rfl⟩ := hsurj c (List.mem_toFinset.mp hc)
      refine ⟨QuotientGroup.mk (⟨a, ha⟩ : H), Subtype.ext ?_⟩
      show f (((QuotientGroup.mk (⟨a, ha⟩ : H) : H ⧸ K.subgroupOf H).out : H) : G) = f a
      have h1 := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
      obtain ⟨k, hk⟩ := h1
      have h2 : ((((QuotientGroup.mk (⟨a, ha⟩ : H) : H ⧸ K.subgroupOf H).out : H) : G)) =
          a * ((k : H) : G) := by rw [hk]; rfl
      rw [h2]
      refine (hiff _ (mul_mem ha (hKH k.2)) _ ha).mpr ?_
      rw [mul_inv_rev, inv_mul_cancel_right]
      exact inv_mem k.2
  have hidx : (K.subgroupOf H).index = l.length := by
    rw [← List.toFinset_card_of_nodup hl, ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  have h1 := (K.subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv, hidx] at h1
  rw [← h1, mul_comm]

namespace Sec3.SzR.MaskCoords

variable {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8} (hM : MaskCoords L T R μ ν)
include hM

omit [Finite G] in
theorem exists_plane (f : G) :
    ∃ X : Subgroup G, ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f) := by
  refine ⟨{ carrier := {x | x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    show μ (a * b) ∈ 0 :: RuQCode.ppOf (ν f)
    rw [hM.mul _ ha _ hb]
    exact RuQCode.ppOf_xor _ _ ha' _ hb'
  · refine ⟨one_mem _, ?_⟩
    show μ 1 ∈ 0 :: RuQCode.ppOf (ν f)
    rw [(hM.ker _ (one_mem _)).mpr (one_mem _)]
    exact List.mem_cons_self
  · rintro a ⟨ha, ha'⟩
    exact ⟨inv_mem ha, by show μ a⁻¹ ∈ _; rw [hM.μ_inv ha]; exact ha'⟩

variable {f : G} {X : Subgroup G} (hX : ∀ x, x ∈ X ↔ x ∈ R ∧ μ x ∈ 0 :: RuQCode.ppOf (ν f))
include hX

omit [Finite G] hM in
theorem plane_le : X ≤ R := fun x hx => ((hX x).mp hx).1

omit [Finite G] in
theorem gmsA_le_plane : gmsA L T ≤ X := fun b hb =>
  (hX b).mpr ⟨hM.le hb, by rw [(hM.ker _ (hM.le hb)).mpr hb]; exact List.mem_cons_self⟩

omit [Finite G] in
theorem isElemAbelian_plane : IsElemAbelian 2 X := by
  have hsq : ∀ x ∈ X, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨hxR, hxm⟩ := (hX x).mp hx
    rw [hM.sq_eq_one_iff hxR]
    rcases List.mem_cons.mp hxm with h | h
    · rw [h]
      rfl
    · exact RuQCode.ppOf_sing _ _ h
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hsq⟩
  obtain ⟨haR, ham⟩ := (hX a).mp a.2
  obtain ⟨hbR, hbm⟩ := (hX b).mp b.2
  show (a : G) * b = b * a
  rw [hM.commute_iff haR hbR]
  rcases List.mem_cons.mp ham with h | h
  · rw [h]
    exact RuQCode.bC_zero_left _
  · rcases List.mem_cons.mp hbm with h' | h'
    · rw [h']
      exact RuQCode.bC_zero_right _
    · exact RuQCode.ppOf_orth _ _ h _ h'

omit [Finite G] in
theorem card_plane (hf : f ∈ gmsA L T) (hf1 : f ≠ 1) : Nat.card X = 32 := by
  classical
  have ht : ν f ≠ 0 := fun h => hf1 (hM.ν_inj f hf h)
  have h := card_eq_length_mul_card (hM.gmsA_le_plane hX) μ (0 :: RuQCode.ppOf (ν f))
    (RuQCode.ppOf_nodup _) (fun a ha => ((hX a).mp ha).2) (fun c hc => by
      have hc' : c < 256 := by
        rcases List.mem_cons.mp hc with h | h
        · rw [h]; norm_num
        · exact RuQCode.ppOf_lt _ _ h
      obtain ⟨x, hx, hxc⟩ := hM.surj c hc'
      exact ⟨x, (hX x).mpr ⟨hx, by rw [hxc]; exact hc⟩, hxc⟩)
    (fun a ha b hb => by
      have haR := ((hX a).mp ha).1
      have hbR := ((hX b).mp hb).1
      rw [← hM.ker _ (mul_mem (inv_mem haR) hbR), hM.mul _ (inv_mem haR) _ hbR, hM.μ_inv haR]
      constructor
      · intro h
        rw [h]
        exact Nat.xor_self _
      · exact RuQCode.nat_eq_of_xor_eq_zero)
  rw [RuQCode.ppOf_length _ ht, hM.card_gmsA] at h
  exact h

omit [Finite G] in
theorem mem_normalizer_plane {g : G} (hg : g ∈ normalizer (R : Set G)) (hgf : g * f * g⁻¹ = f)
    (hf : f ∈ gmsA L T) : g ∈ normalizer (X : Set G) := by
  obtain ⟨r, hr, hrA, hrR⟩ := hM.act g hg
  have hrf : linApply r (ν f) = ν f := by rw [← hrA f hf, hgf]
  have hgX : ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
    intro x hx
    obtain ⟨hxR, hxm⟩ := (hX x).mp hx
    refine (hX _).mpr ⟨(mem_normalizer_iff.mp hg x).mp hxR, ?_⟩
    rw [hrR x hxR]
    rcases List.mem_cons.mp hxm with h | h
    · rw [h, RuQCode.maskApply_zero]
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      rw [← hrf]
      exact RuQCode.ppOf_equiv hr h
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact hgX x
  · intro hx
    have hgR : g⁻¹ ∈ normalizer (R : Set G) := inv_mem hg
    obtain ⟨r', hr', hrA', hrR'⟩ := hM.act g⁻¹ hgR
    have hxR : x ∈ R := by
      have := (mem_normalizer_iff.mp hgR (g * x * g⁻¹)).mp ((hX _).mp hx).1
      simpa [mul_assoc] using this
    have hrf' : linApply r' (ν f) = ν f := by
      rw [← hrA' f hf]
      congr 1
      calc g⁻¹ * f * g⁻¹⁻¹ = g⁻¹ * (g * f * g⁻¹) * g := by rw [hgf, inv_inv]
        _ = f := by group
    have h1 := (hX _).mp hx
    refine (hX x).mpr ⟨hxR, ?_⟩
    have h2 := hrR' _ h1.1
    rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2
    rw [h2]
    rcases List.mem_cons.mp h1.2 with h | h
    · rw [h, RuQCode.maskApply_zero]
      exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      rw [← hrf']
      exact RuQCode.ppOf_equiv hr' h

end Sec3.SzR.MaskCoords

end CFSG.ComponentClassification.GMS78
