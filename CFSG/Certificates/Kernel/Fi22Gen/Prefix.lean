module

public import CFSG.Certificates.Kernel.Fi22Gen.Sound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 4000

namespace CFSG.KS.Fi22Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22L
open scoped Pointwise

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

theorem orbit_prefix_ge_of_chainK [Finite G] {UL w1 w2 p1 p2 : List Nat}
    {lvW : List (List (List Nat))} {lvO lvP lvG : List (List Nat)} (hul : ulK UL = true)
    (hord : ordK w1 w2 = true) (htr : traceK UL w1 w2 p1 p2 = true)
    (hch : chainK p1 p2 lvW lvO lvP lvG = true) (m : Nat → G)
    (hm : ∀ c < 2, ∀ x (hx : x < 3510), (m c • (⟨x, hx⟩ : Fin 3510)).val = AB c x)
    (H : Subgroup G) (h1 : wG m w1 ∈ H) (h2 : wG m w2 ^ 2 ∈ H) (n : Nat) (hn : n ≤ 5) :
    ∏ i ∈ Finset.range n, lvS i ≤ Nat.card (MulAction.orbit H fun j : Fin n => tP UL j) := by
  obtain ⟨hl1, hl2, -⟩ := ordK_spec hord
  obtain ⟨-, huinc, hulast⟩ := ulK_spec hul
  have hUlt : ∀ j < 22, gD UL j < 3510 := by
    intro j hj
    rcases Nat.lt_or_ge j 21 with h | h
    · exact (lt_of_inc huinc j 21 h (by omega)).trans hulast
    · rw [show j = 21 by omega]; exact hulast
  have hUinj : ∀ i j, i < 22 → j < 22 → gD UL i = gD UL j → i = j := by
    intro i j hi hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd e (lt_of_inc huinc i j h hj).ne
    · exact absurd e (lt_of_inc huinc j i h hi).ne'
  have htP : ∀ j < 22, (tP UL j).val = gD UL j := fun j hj => Nat.mod_eq_of_lt (hUlt j hj)
  have s1 := wG_smul m AB 2 hm w1 hl1
  have s2 := wG_smul m AB 2 hm w2 hl2
  let ψ : Nat → G := fun c => if c = 0 then wG m w1 else wG m w2 ^ 2
  have hψH : ∀ c, ψ c ∈ H := by
    intro c
    by_cases hc : c = 0
    · simp only [ψ, if_pos hc]; exact h1
    · simp only [ψ, if_neg hc]; exact h2
  have hψ : ∀ c < 2, ∀ j < 22, PP p1 p2 c j < 22 ∧ ψ c • tP UL j = tP UL (PP p1 p2 c j) := by
    intro c hc j hj
    obtain ⟨hj1, hj2, hv1, hv2⟩ := traceK_spec htr j hj
    rw [PP_eq]
    by_cases hc0 : c = 0
    · simp only [ψ, if_pos hc0]
      refine ⟨hj1, Fin.ext ?_⟩
      have e : tP UL j = ⟨gD UL j, hUlt j hj⟩ := Fin.ext (htP j hj)
      rw [e, s1, hv1, htP _ hj1]
    · simp only [ψ, if_neg hc0]
      refine ⟨hj2, Fin.ext ?_⟩
      have e : tP UL j = ⟨gD UL j, hUlt j hj⟩ := Fin.ext (htP j hj)
      rw [e, pow_smul_val s2 2 _ (hUlt j hj), Function.iterate_succ_apply, Function.iterate_one,
        htP _ hj2, hv2]
  have hword : ∀ w : List Nat, (∀ l ∈ w, l < 2) → ∀ j < 22,
      wAp (PP p1 p2) w j < 22 ∧ wG ψ w • tP UL j = tP UL (wAp (PP p1 p2) w j) := by
    intro w
    induction w with
    | nil => intro _ j hj; simp [wG, wAp, hj]
    | cons l w ih =>
      intro hw j hj
      obtain ⟨hlt, he⟩ := ih (fun z hz => hw z (List.mem_cons_of_mem l hz)) j hj
      obtain ⟨hlt', he'⟩ := hψ l (hw l List.mem_cons_self) _ hlt
      refine ⟨hlt', ?_⟩
      have e : wG ψ (l :: w) = ψ l * wG ψ w := by simp [wG]
      rw [e, mul_smul, he, he', wAp_cons]
  have hwH : ∀ w : List Nat, wG ψ w ∈ H := by
    intro w
    induction w with
    | nil =>
      rw [wG, List.map_nil, List.prod_nil]
      exact H.one_mem
    | cons l w ih =>
      have e : wG ψ (l :: w) = ψ l * wG ψ w := by simp [wG]
      rw [e]
      exact H.mul_mem (hψH l) ih
  unfold chainK at hch
  refine chain_card H n (tP UL) lvS fun i hi => ?_
  have hi5 : i < 5 := by omega
  have hlv := levelK_spec (Raw.Orb.allN_iff.1 hch i hi5)
  set W := lvW.getD i []
  set O := lvO.getD i []
  set P := lvP.getD i []
  set Gl := lvG.getD i []
  obtain ⟨hWl, hWfix, hO0, hOlt, hOne, htree⟩ := hlv
  have hWS : ∀ c < W.length, wG ψ (W.getD c []) ∈ H ⊓ preS (tP UL) i := by
    intro c hc
    have hmem : W.getD c [] ∈ W := getD_mem hc
    refine Subgroup.mem_inf.2 ⟨hwH _, mem_preS.2 fun j hj => ?_⟩
    rw [(hword _ (hWl _ hmem) j (by omega)).2, hWfix _ hmem j hj]
  have reach : ∀ a, a < lvS i → ∃ x ∈ H ⊓ preS (tP UL) i, x • tP UL i = tP UL (gD O a) := by
    intro a
    refine Nat.strong_induction_on a ?_
    intro a ih ha
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by rw [one_smul, hO0]⟩
    · obtain ⟨hp, hc, he⟩ := htree a hpos ha
      obtain ⟨x, hx, hxe⟩ := ih _ hp (by omega)
      refine ⟨wG ψ (W.getD (gD Gl a) []) * x, Subgroup.mul_mem _ (hWS _ hc) hx, ?_⟩
      have hmem : W.getD (gD Gl a) [] ∈ W := getD_mem hc
      rw [mul_smul, hxe, (hword _ (hWl _ hmem) _ (hOlt _ (by omega))).2, he]
  choose! f hf hfe using reach
  let F : Fin (lvS i) → MulAction.orbit ↥(H ⊓ preS (tP UL) i) (tP UL i) := fun a =>
    ⟨tP UL (gD O a), ⟨⟨f a, hf a a.isLt⟩, hfe a a.isLt⟩⟩
  have hF : Function.Injective F := by
    intro a b e
    have e' : tP UL (gD O a) = tP UL (gD O b) := congrArg Subtype.val e
    have e'' := congrArg Fin.val e'
    rw [htP _ (hOlt _ a.isLt), htP _ (hOlt _ b.isLt)] at e''
    have hab := hUinj _ _ (hOlt _ a.isLt) (hOlt _ b.isLt) e''
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hOne _ b.isLt _ h hab.symm
    · exact hOne _ a.isLt _ h hab
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fin] at this

theorem exists_smul_eq_of_orbit (U : Finset (Fin 3510)) {k : Nat} (t : Fin k → Fin 3510)
    (ht : Function.Injective t) (htU : ∀ j, t j ∈ U)
    (hcard : U.card.descFactorial k ≤
      Nat.card (MulAction.orbit (MulAction.stabilizer G U) t))
    (f : Fin k → Fin 3510) (hf : Function.Injective f) (hfU : ∀ j, f j ∈ U) :
    ∃ x : G, x • U = U ∧ x • t = f := by
  let φ : (Fin k ↪ U) → (Fin k → Fin 3510) := fun e j => (e j : Fin 3510)
  have hφ : Function.Injective φ := fun e e' h =>
    Function.Embedding.ext fun j => Subtype.ext (congrFun h j)
  have hsub : MulAction.orbit (MulAction.stabilizer G U) t ⊆ Set.range φ := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : G) • U = U := MulAction.mem_stabilizer_iff.1 x.2
    have hmem : ∀ j, (x : G) • t j ∈ U := fun j => by
      have h := Finset.smul_mem_smul_finset (a := (x : G)) (htU j)
      rwa [hx] at h
    refine ⟨⟨fun j => ⟨(x : G) • t j, hmem j⟩, fun i j h => ?_⟩, ?_⟩
    · exact ht (smul_left_cancel _ (congrArg Subtype.val h))
    · funext j
      rfl
  have hle : (Set.range φ).ncard ≤ (MulAction.orbit (MulAction.stabilizer G U) t).ncard := by
    have hemb : Nat.card (Fin k ↪ U) = U.card.descFactorial k := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
    rw [← Nat.card_coe_set_eq (Set.range φ), Nat.card_range_of_injective hφ, hemb,
      ← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hfr : f ∈ Set.range φ :=
    ⟨⟨fun j => ⟨f j, hfU j⟩, fun i j h => hf (congrArg Subtype.val h)⟩, rfl⟩
  rw [← heq] at hfr
  obtain ⟨x, hx⟩ := hfr
  exact ⟨x, MulAction.mem_stabilizer_iff.1 x.2, hx⟩

theorem exists_smul_finset_of_tuples (U : Finset (Fin 3510))
    (htr : ∀ k ≤ 3, ∃ t : Fin k → Fin 3510, ∀ f : Fin k → Fin 3510, Function.Injective f →
      (∀ j, f j ∈ U) → ∃ x : G, x • U = U ∧ x • t = f)
    (s s' : Finset (Fin 3510)) (hs : s ⊆ U) (hs' : s' ⊆ U) (hc : s.card = s'.card)
    (h3 : s.card ≤ 3) : ∃ x : G, x • U = U ∧ x • s = s' := by
  obtain ⟨t, ht⟩ := htr s.card h3
  obtain ⟨x, hxU, hx⟩ := ht (s.orderEmbOfFin rfl) (s.orderEmbOfFin rfl).injective
    fun j => hs (s.orderEmbOfFin_mem rfl j)
  obtain ⟨y, hyU, hy⟩ := ht (s'.orderEmbOfFin hc.symm) (s'.orderEmbOfFin hc.symm).injective
    fun j => hs' (s'.orderEmbOfFin_mem hc.symm j)
  refine ⟨y * x⁻¹, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 hxU.symm, hyU]
  · have hz : ∀ j, (y * x⁻¹) • s.orderEmbOfFin rfl j = s'.orderEmbOfFin hc.symm j := fun j => by
      have e1 := congrFun hx j
      have e2 := congrFun hy j
      rw [Pi.smul_apply] at e1 e2
      rw [mul_smul, ← e1, ← e2, inv_smul_smul]
    calc (y * x⁻¹) • s = (y * x⁻¹) • Finset.univ.image (s.orderEmbOfFin rfl) := by
          rw [Finset.image_orderEmbOfFin_univ]
      _ = Finset.univ.image fun j => (y * x⁻¹) • s.orderEmbOfFin rfl j := by
          rw [Finset.smul_finset_def, Finset.image_image]
          rfl
      _ = Finset.univ.image (s'.orderEmbOfFin hc.symm) := by
          congr 1
          funext j
          exact hz j
      _ = s' := Finset.image_orderEmbOfFin_univ s' hc.symm

end CFSG.KS.Fi22Gen

end
