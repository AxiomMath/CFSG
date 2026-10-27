module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec5Types

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

variable {V : Type} [AddCommGroup V] {X : Type} [Group X] [DistribMulAction X V]
  {A B : Subgroup X} {R U W : AddSubgroup V}

theorem smul_mem_fused_iff {x : X} {v : V} : x • v ∈ fused X R ↔ v ∈ fused X R :=
  ⟨fun hv => by simpa using smul_mem_fused hv x⁻¹, fun hv => smul_mem_fused hv x⟩

namespace Hyp51

variable (h : Hyp51 X A B R U W)

@[expose] def Occ (p : Bool × Bool × Bool) : Prop :=
  ∃ v ∈ fused X R, h.decomp.pat v = p

include h

theorem exists_AB_smul {y y' : V} (hR : h.decomp.cR y = h.decomp.cR y')
    (hp : h.decomp.pat y = h.decomp.pat y') : ∃ a ∈ A, ∃ b ∈ B, (a * b) • y = y' := by
  set hd := h.decomp
  obtain ⟨-, hU, hW⟩ := (hd.pat_eq_iff y y').1 hp
  have hb : ∃ b ∈ B, b • (hd.cU y : V) = hd.cU y' := by
    by_cases h0 : hd.cU y = 0
    · exact ⟨1, B.one_mem, by rw [one_smul, h0, hU.1 h0]⟩
    · exact h.B_trans _ (hd.cU y).2 _ (hd.cU y').2 (by simpa using h0)
        (by simpa using fun h' => h0 (hU.2 h'))
  have ha : ∃ a ∈ A, a • (hd.cW y : V) = hd.cW y' := by
    by_cases h0 : hd.cW y = 0
    · exact ⟨1, A.one_mem, by rw [one_smul, h0, hW.1 h0]⟩
    · exact h.A_trans _ (hd.cW y).2 _ (hd.cW y').2 (by simpa using h0)
        (by simpa using fun h' => h0 (hW.2 h'))
  obtain ⟨b, hbB, hb'⟩ := hb
  obtain ⟨a, haA, ha'⟩ := ha
  exact ⟨a, haA, b, hbB, by rw [h.AB_smul haA hbB, hb', ha', hR, hd.coord_sum]⟩

theorem pat_of_mem_R {r : V} (hr : r ∈ R) (h0 : r ≠ 0) :
    h.decomp.pat r = (true, false, false) := by
  set hd := h.decomp
  obtain ⟨h2, h3⟩ := (hd.mem_R_iff r).1 hr
  have h1 : hd.cR r ≠ 0 := fun h1 => h0 (by rw [← hd.coord_sum r, h1, h2, h3]; simp)
  simp [Decomp.pat, nz_of_ne h1, h2, h3]

theorem occ_R : h.Occ (true, false, false) := by
  obtain ⟨r, hr, hr0⟩ : ∃ r ∈ R, r ≠ 0 := by
    rcases R.bot_or_exists_ne_zero with hR | hR
    · have := h.two_lt
      rw [hR] at this
      simp at this
    · exact hR
  exact ⟨r, mem_fused_of_mem hr hr0, h.pat_of_mem_R hr hr0⟩

theorem not_occ_zero : ¬h.Occ (false, false, false) := by
  rintro ⟨v, hv, hp⟩
  exact (mem_fused_iff.1 hv).1 ((h.decomp.pat_eq_zero_iff v).1 hp)

variable [Finite V]

theorem mem_fused_of_pat_eq {v v' : V} (hv : v ∈ fused X R)
    (hp : h.decomp.pat v' = h.decomp.pat v) : v' ∈ fused X R := by
  set hd := h.decomp
  obtain ⟨hv0, T, hT, hvT⟩ := mem_fused_iff.1 hv
  obtain ⟨p, hpT⟩ := h.pat_uniform hT
  obtain ⟨hR', -, -⟩ := (hd.pat_eq_iff v' v).1 hp
  obtain ⟨t, ht, ht0, htR, htp⟩ : ∃ t ∈ T, t ≠ 0 ∧ hd.cR t = hd.cR v' ∧ hd.pat t = hd.pat v' := by
    by_cases hR : hd.cR v = 0
    · exact ⟨v, hvT, hv0, by rw [hR, hR'.2 hR], hp.symm⟩
    ·
      have hTR : ∀ y ∈ T, y ≠ 0 → hd.cR y ≠ 0 := by
        intro y hy hy0 h0
        have hpy : hd.pat y = hd.pat v := by rw [hpT y hy hy0, hpT v hvT hv0]
        exact hR (((hd.pat_eq_iff y v).1 hpy).1.1 h0)
      have hinj : Function.Injective (fun y : T => hd.cR y) := by
        intro y₁ y₂ hy
        have hy' : hd.cR y₁ = hd.cR y₂ := hy
        by_contra hne
        have hne' : (y₁ : V) + y₂ ≠ 0 := fun h0 => hne (Subtype.ext (h.eq_of_add_eq_zero' h0))
        apply hTR _ (T.add_mem y₁.2 y₂.2) hne'
        rw [hd.cR_add, hy']
        exact Subtype.ext (h.two _)
      have hbij := (Nat.bijective_iff_injective_and_card _).2
        ⟨hinj, card_of_mem_members hT⟩
      obtain ⟨y, hy⟩ := hbij.2 (hd.cR v')
      have hy' : hd.cR y = hd.cR v' := hy
      have hv'R : hd.cR v' ≠ 0 := fun h0 => hR (hR'.1 h0)
      have hy0 : (y : V) ≠ 0 := fun h0 => hv'R (by rw [← hy', h0]; simp [Decomp.cR])
      refine ⟨y, y.2, hy0, hy', ?_⟩
      rw [hpT y y.2 hy0, hp, hpT v hvT hv0]
  obtain ⟨a, -, b, -, hab⟩ := h.exists_AB_smul htR htp
  rw [← hab]
  exact smul_mem_fused (mem_fused_iff.2 ⟨ht0, T, hT, ht⟩) _

theorem mem_fused_iff_occ (v : V) : v ∈ fused X R ↔ h.Occ (h.decomp.pat v) := by
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v', hv', hp⟩
    exact h.mem_fused_of_pat_eq hv' hp.symm

theorem ncard_fused : (fused X R).ncard = (members X R).ncard * (Nat.card R - 1) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have : Finite (AddSubgroup V) := Finite.of_injective _ SetLike.coe_injective
  have hfin : (members X R).Finite := Set.toFinite _
  let F : AddSubgroup V → Finset V := fun T => (Finset.univ.filter (fun v => v ∈ T)).erase 0
  have hF : ∀ T : AddSubgroup V, (F T).card = Nat.card T - 1 := by
    intro T
    simp only [F]
    rw [Finset.card_erase_of_mem (by simp [zero_mem]), Nat.card_eq_fintype_card,
      Fintype.card_of_subtype (Finset.univ.filter (fun v => v ∈ T)) (by simp)]
  have hunion : fused X R = ↑(hfin.toFinset.biUnion F) := by
    ext v
    simp only [mem_fused_iff, Finset.coe_biUnion, Set.Finite.coe_toFinset, Set.mem_iUnion,
      Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
      Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_prop, F]
    constructor
    · rintro ⟨hv0, T, hT, hvT⟩
      exact ⟨T, hT, hvT, hv0⟩
    · rintro ⟨T, hT, hvT, hv0⟩
      exact ⟨hv0, T, hT, hvT⟩
  have hdisj : (hfin.toFinset : Set (AddSubgroup V)).PairwiseDisjoint F := by
    intro T hT T' hT' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, F] at hv hv'
    simp only [Set.Finite.coe_toFinset] at hT hT'
    exact hne (h.eq_of_mem_of_mem hT hT' hv.2 hv'.2 hv.1)
  rw [hunion, Set.ncard_coe_finset, Finset.card_biUnion hdisj,
    Set.ncard_eq_toFinset_card _ hfin, Finset.sum_congr rfl (g := fun _ => Nat.card R - 1)
      fun T hT => by rw [hF, card_of_mem_members ((Set.Finite.mem_toFinset hfin).1 hT)],
    Finset.sum_const, smul_eq_mul]

end Hyp51

end CFSG.ComponentClassification.AS76b.Sec5
