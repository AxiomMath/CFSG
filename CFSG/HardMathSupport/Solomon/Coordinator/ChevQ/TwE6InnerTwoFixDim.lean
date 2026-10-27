module

public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2ConjDim

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix)

section Orbits

private theorem fd_exists_reps {ι : Type*} [Fintype ι] (σ : ι → ι) (h3 : ∀ x, σ (σ (σ x)) = x)
    (h1 : ∀ x, σ x ≠ x) :
    ∃ R : Finset ι, 3 * R.card = Fintype.card ι ∧
      (∀ x, ∃ r ∈ R, x = r ∨ x = σ r ∨ x = σ (σ r)) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ≠ σ r ∧ r' ≠ σ (σ r) := by
  classical
  obtain ⟨rep, hrep, hrepσ⟩ : ∃ rep : ι → ι, (∀ x, rep x = x ∨ rep x = σ x ∨ rep x = σ (σ x)) ∧
      ∀ x, rep (σ x) = rep x := by
    set e := Fintype.equivFin ι
    refine ⟨fun x => e.symm (min (e x) (min (e (σ x)) (e (σ (σ x))))), fun x => ?_, fun x => ?_⟩
    · dsimp only
      rcases min_choice (e x) (min (e (σ x)) (e (σ (σ x)))) with h | h <;> rw [h]
      · exact Or.inl (e.symm_apply_apply x)
      · rcases min_choice (e (σ x)) (e (σ (σ x))) with h' | h' <;> rw [h']
        · exact Or.inr (Or.inl (e.symm_apply_apply _))
        · exact Or.inr (Or.inr (e.symm_apply_apply _))
    · dsimp only
      rw [h3, min_comm (e (σ (σ x))) (e x), min_left_comm]
  have hrr : ∀ x, rep (rep x) = rep x := by
    intro x
    rcases hrep x with h | h | h <;> rw [h]
    · exact h
    · rw [hrepσ, h]
    · rw [hrepσ, hrepσ, h]
  have hσσ : ∀ x, σ (σ x) ≠ x := fun x h => h1 x (by
    have h' := congrArg σ h
    rwa [h3, eq_comm] at h')
  have hfib : ∀ r, rep r = r → Finset.univ.filter (fun x => rep x = r) = {r, σ r, σ (σ r)} := by
    intro r hr
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      rcases hrep x with h | h | h
      · exact Or.inl (h.symm.trans hx)
      · refine Or.inr (Or.inr ?_)
        rw [← hx, h, h3]
      · refine Or.inr (Or.inl ?_)
        rw [← hx, h, h3]
    · rintro (rfl | rfl | rfl)
      · exact hr
      · rw [hrepσ, hr]
      · rw [hrepσ, hrepσ, hr]
  refine ⟨Finset.univ.filter (fun x => rep x = x), ?_, fun x => ?_, fun r hr r' hr' => ?_⟩
  · have hcard : Fintype.card ι = ∑ r ∈ Finset.univ.filter (fun x => rep x = x),
        (Finset.univ.filter (fun x => rep x = r)).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_fiberwise (fun x _ => by simp [hrr])
    have h3c : ∀ r ∈ Finset.univ.filter (fun x => rep x = x),
        (Finset.univ.filter (fun x => rep x = r)).card = 3 := by
      intro r hr
      rw [hfib r (Finset.mem_filter.1 hr).2, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using (h1 (σ r)).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(h1 r).symm, (hσσ r).symm⟩
    rw [hcard, Finset.sum_congr rfl h3c, Finset.sum_const, smul_eq_mul, mul_comm]
  · refine ⟨rep x, by simp [hrr], ?_⟩
    rcases hrep x with h | h | h
    · exact Or.inl h.symm
    · refine Or.inr (Or.inr ?_)
      rw [h, h3]
    · refine Or.inr (Or.inl ?_)
      rw [h, h3]
  · have hr0 : rep r = r := (Finset.mem_filter.1 hr).2
    have hr0' : rep r' = r' := (Finset.mem_filter.1 hr').2
    refine ⟨fun h => h1 r ?_, fun h => hσσ r ?_⟩
    · rw [← h, ← hr0', h, hrepσ, hr0]
    · rw [← h, ← hr0', h, hrepσ, hrepσ, hr0]

private theorem fd_exists_reps_on {ι : Type*} [Fintype ι] (π : ι → ι)
    (hπ3 : ∀ x, π (π (π x)) = x) (P : ι → Prop)
    (hP : ∀ x, P x → P (π x)) (hP1 : ∀ x, P x → π x ≠ x) :
    ∃ R : Finset ι, (∀ r ∈ R, P r) ∧ 3 * R.card = Nat.card {x // P x} ∧
      (∀ x, P x → ∃ r ∈ R, x = r ∨ x = π r ∨ x = π (π r)) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ≠ π r ∧ r' ≠ π (π r) := by
  classical
  let σ : {x // P x} → {x // P x} := fun x => ⟨π x.1, hP x.1 x.2⟩
  obtain ⟨R, hRc, hR1, hR2⟩ := fd_exists_reps σ (fun x => Subtype.ext (hπ3 x.1))
    (fun x h => hP1 x.1 x.2 (congrArg Subtype.val h))
  refine ⟨R.map (Function.Embedding.subtype P), ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨r', -, rfl⟩ := Finset.mem_map.1 hr
    exact r'.2
  · rw [Finset.card_map, hRc, Nat.card_eq_fintype_card]
  · intro x hx
    obtain ⟨r, hr, h⟩ := hR1 ⟨x, hx⟩
    refine ⟨r.1, Finset.mem_map_of_mem _ hr, ?_⟩
    rcases h with h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (congrArg Subtype.val h))
  · intro r hr r' hr'
    obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_map.1 hr
    obtain ⟨r₀', hr₀', rfl⟩ := Finset.mem_map.1 hr'
    obtain ⟨h1, h2⟩ := hR2 r₀ hr₀ r₀' hr₀'
    exact ⟨fun h => h1 (Subtype.ext h), fun h => h2 (Subtype.ext h)⟩

end Orbits

section Abstract

variable {L : Type*} [Field L] {κ ι : Type*} [Fintype κ] [Fintype ι]

private theorem fd_mem_inl (x : κ ⊕ ι →₀ L) :
    x ∈ Finsupp.supported L L (Set.range Sum.inl) ↔ ∀ i, x (Sum.inr i) = 0 := by
  rw [Finsupp.mem_supported']
  constructor
  · intro h i
    exact h _ (by rintro ⟨j, hj⟩; exact Sum.inl_ne_inr hj)
  · rintro h (j | i) hb
    · exact absurd ⟨j, rfl⟩ hb
    · exact h i

private theorem fd_mem_inr (x : κ ⊕ ι →₀ L) :
    x ∈ Finsupp.supported L L (Set.range Sum.inr) ↔ ∀ j, x (Sum.inl j) = 0 := by
  rw [Finsupp.mem_supported']
  constructor
  · intro h j
    exact h _ (by rintro ⟨i, hi⟩; exact Sum.inr_ne_inl hi)
  · rintro h (j | i) hb
    · exact h j
    · exact absurd ⟨i, rfl⟩ hb

private theorem fd_eq_sum (x : κ ⊕ ι →₀ L) :
    x = (∑ j, x (Sum.inl j) • Finsupp.single (Sum.inl j) 1) +
      ∑ i, x (Sum.inr i) • Finsupp.single (Sum.inr i) 1 := by
  classical
  ext b
  rcases b with k | k <;> simp [Finsupp.single_apply]

private theorem fd_split (S : Module.End L (κ ⊕ ι →₀ L))
    (hSl : ∀ j, S (Finsupp.single (Sum.inl j) 1) ∈ Finsupp.supported L L (Set.range Sum.inl))
    (hSr : ∀ i, S (Finsupp.single (Sum.inr i) 1) ∈ Finsupp.supported L L (Set.range Sum.inr)) :
    Module.finrank L (LinearMap.ker (S - 1)) =
      Module.finrank L ↥(LinearMap.ker (S - 1) ⊓ Finsupp.supported L L (Set.range Sum.inl)) +
      Module.finrank L ↥(LinearMap.ker (S - 1) ⊓ Finsupp.supported L L (Set.range Sum.inr)) := by
  classical
  set F := LinearMap.ker (S - 1) with hF
  set Vl := Finsupp.supported L L (Set.range (Sum.inl : κ → κ ⊕ ι)) with hVl
  set Vr := Finsupp.supported L L (Set.range (Sum.inr : ι → κ ⊕ ι)) with hVr
  have hdisj : Disjoint Vl Vr := Finsupp.disjoint_supported_supported
    (Set.disjoint_left.2 (by rintro _ ⟨j, rfl⟩ ⟨i, hi⟩; exact Sum.inr_ne_inl hi))
  have hmem : ∀ x, x ∈ F ↔ S x = x := fun x => by
    rw [hF, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hsup : F ⊓ Vl ⊔ F ⊓ Vr = F := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
    set xl := ∑ j, x (Sum.inl j) • Finsupp.single (Sum.inl j) (1 : L) with hxl
    set xr := ∑ i, x (Sum.inr i) • Finsupp.single (Sum.inr i) (1 : L) with hxr
    have hx' : x = xl + xr := fd_eq_sum x
    have hxlV : xl ∈ Vl := Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported L _ ⟨j, rfl⟩)
    have hxrV : xr ∈ Vr := Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Finsupp.single_mem_supported L _ ⟨i, rfl⟩)
    have hSxl : S xl ∈ Vl := by
      rw [hxl, map_sum]
      exact Submodule.sum_mem _ fun j _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hSl j)
    have hSxr : S xr ∈ Vr := by
      rw [hxr, map_sum]
      exact Submodule.sum_mem _ fun i _ => by rw [map_smul]; exact Submodule.smul_mem _ _ (hSr i)
    have hSx : S xl + S xr = xl + xr := by rw [← map_add, ← hx', (hmem x).1 hx]
    have hd : S xl - xl = xr - S xr := by
      rw [sub_eq_sub_iff_add_eq_add, hSx, add_comm]
    have h0 : S xl - xl = 0 := by
      have h1 : S xl - xl ∈ Vl := Submodule.sub_mem _ hSxl hxlV
      have h2 : S xl - xl ∈ Vr := by rw [hd]; exact Submodule.sub_mem _ hxrV hSxr
      exact (Submodule.disjoint_def.1 hdisj) _ h1 h2
    have h0' : S xr - xr = 0 := by
      rw [← neg_sub, ← hd, h0, neg_zero]
    rw [hx']
    exact Submodule.add_mem_sup ⟨(hmem xl).2 (sub_eq_zero.1 h0), hxlV⟩
      ⟨(hmem xr).2 (sub_eq_zero.1 h0'), hxrV⟩
  have hinf : F ⊓ Vl ⊓ (F ⊓ Vr) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    exact (Submodule.disjoint_def.1 hdisj) x hx.1.2 hx.2.2
  have h := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ Vl) (F ⊓ Vr)
  rw [hsup, hinf, finrank_bot, add_zero] at h
  exact h

private theorem fd_finrank_inr (S : Module.End L (κ ⊕ ι →₀ L)) (π : ι → ι)
    (hπ3 : ∀ i, π (π (π i)) = i) (c : ι → L)
    (hSr : ∀ i, S (Finsupp.single (Sum.inr i) 1) = c i • Finsupp.single (Sum.inr (π i)) 1)
    (hSh : ∀ j i, S (Finsupp.single (Sum.inl j) 1) (Sum.inr i) = 0) :
    Module.finrank L ↥(LinearMap.ker (S - 1) ⊓ Finsupp.supported L L (Set.range Sum.inr)) =
      Nat.card {i // π i = i ∧ c i = 1} +
        Nat.card {i // π i ≠ i ∧ c i * c (π i) * c (π (π i)) = 1} / 3 := by
  classical
  set Q := LinearMap.ker (S - 1) ⊓ Finsupp.supported L L (Set.range (Sum.inr : ι → κ ⊕ ι))
    with hQ
  have hπinj : Function.Injective π := fun a b h => by rw [← hπ3 a, ← hπ3 b, h]
  have hmemQ : ∀ x, x ∈ Q ↔ S x = x ∧ ∀ j, x (Sum.inl j) = 0 := fun x => by
    rw [hQ, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, fd_mem_inr]
  have hsingle : ∀ (b : κ ⊕ ι) (a : L), Finsupp.single b a = a • Finsupp.single b 1 :=
    fun b a => by rw [Finsupp.smul_single_one]
  have hcoef : ∀ (x : κ ⊕ ι →₀ L) (i : ι), S x (Sum.inr (π i)) = c i * x (Sum.inr i) := by
    intro x i
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
    | single b a =>
      rw [hsingle b a, map_smul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
        smul_eq_mul]
      rcases b with j | i'
      · rw [hSh, Finsupp.single_apply, if_neg Sum.inl_ne_inr]
        ring
      · rw [hSr, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
        by_cases hi : i' = i
        · subst hi
          simp only [if_true]
          ring
        · rw [if_neg (fun h => hi (hπinj (Sum.inr_injective h))),
            if_neg (fun h => hi (Sum.inr_injective h))]
          ring
  set hol : ι → L := fun i => c i * c (π i) * c (π (π i)) with hhol
  have hholπ : ∀ i, hol (π i) = hol i := fun i => by
    simp only [hhol, hπ3]
    ring
  obtain ⟨R, hRP, hRc, hR1, hR2⟩ : ∃ R : Finset ι, (∀ r ∈ R, π r ≠ r ∧ hol r = 1) ∧
      3 * R.card = Nat.card {i // π i ≠ i ∧ c i * c (π i) * c (π (π i)) = 1} ∧
      (∀ x, π x ≠ x ∧ hol x = 1 → ∃ r ∈ R, x = r ∨ x = π r ∨ x = π (π r)) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ≠ π r ∧ r' ≠ π (π r) :=
    fd_exists_reps_on π hπ3 (fun i => π i ≠ i ∧ hol i = 1)
      (fun x hx => ⟨fun h => hx.1 (hπinj h), by rw [hholπ]; exact hx.2⟩) (fun x hx => hx.1)
  have hFr : ∀ x ∈ Q, ∀ i, x (Sum.inr (π i)) = c i * x (Sum.inr i) := fun x hx i => by
    rw [← hcoef x i, ((hmemQ x).1 hx).1]
  have hFl : ∀ x ∈ Q, ∀ j, x (Sum.inl j) = 0 := fun x hx => ((hmemQ x).1 hx).2
  have hFfix : ∀ x ∈ Q, ∀ i, π i = i → c i ≠ 1 → x (Sum.inr i) = 0 := by
    intro x hx i hi hc
    have h := hFr x hx i
    rw [hi] at h
    have h' : (c i - 1) * x (Sum.inr i) = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hc)
  have hFmov : ∀ x ∈ Q, ∀ i, hol i ≠ 1 → x (Sum.inr i) = 0 := by
    intro x hx i hh
    have h1 := hFr x hx i
    have h2 := hFr x hx (π i)
    have h3 := hFr x hx (π (π i))
    rw [hπ3] at h3
    have h' : (hol i - 1) * x (Sum.inr i) = 0 := by
      simp only [hhol]
      linear_combination (-1 : L) * h3 - c (π (π i)) * h2 - c (π i) * c (π (π i)) * h1
    exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hh)
  set T := Finset.univ.filter fun i => π i = i ∧ c i = 1 with hT
  have hTm : ∀ t ∈ T, π t = t ∧ c t = 1 := fun t ht => (Finset.mem_filter.1 ht).2
  let idx : ↥T ⊕ ↥R → ι := Sum.elim Subtype.val Subtype.val
  let Ψ : Q →ₗ[L] (↥T ⊕ ↥R → L) :=
    { toFun := fun x s => (x : κ ⊕ ι →₀ L) (Sum.inr (idx s))
      map_add' := fun x y => by
        funext s
        simp
      map_smul' := fun a x => by
        funext s
        simp }
  have hΨ : Function.Injective Ψ := by
    have key : Function.Injective Ψ ↔ ∀ x, Ψ x = 0 → x = 0 := injective_iff_map_eq_zero Ψ
    refine key.2 fun x hx => ?_
    have h0 : ∀ s, (x : κ ⊕ ι →₀ L) (Sum.inr (idx s)) = 0 := fun s => congrFun hx s
    refine Subtype.ext (Finsupp.ext fun b => ?_)
    rw [Submodule.coe_zero, Finsupp.zero_apply]
    rcases b with j | i
    · exact hFl x x.2 j
    · by_cases hfix : π i = i
      · by_cases hc : c i = 1
        · exact h0 (Sum.inl ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfix, hc⟩⟩)
        · exact hFfix x x.2 i hfix hc
      · by_cases hh : hol i = 1
        · obtain ⟨r, hr, hi⟩ := hR1 i ⟨hfix, hh⟩
          have hr0 : (x : κ ⊕ ι →₀ L) (Sum.inr r) = 0 := h0 (Sum.inr ⟨r, hr⟩)
          rcases hi with rfl | rfl | rfl
          · exact hr0
          · rw [hFr x x.2, hr0, mul_zero]
          · rw [hFr x x.2, hFr x x.2, hr0, mul_zero, mul_zero]
        · exact hFmov x x.2 i hh
  let e : ι → (κ ⊕ ι →₀ L) := fun i => Finsupp.single (Sum.inr i) 1
  have hSe : ∀ i, S (e i) = c i • e (π i) := hSr
  have hS3e : ∀ i, S (S (S (e i))) = hol i • e i := by
    intro i
    simp only [hSe, map_smul, hπ3, smul_smul, hhol, mul_assoc]
  have he_inl : ∀ i j, e i (Sum.inl j) = 0 := fun i j => by
    simp [e, Finsupp.single_apply]
  have hval : ∀ r i, (e r + S (e r) + S (S (e r))) (Sum.inr i) =
      (if r = i then 1 else 0) + c r * (if π r = i then 1 else 0) +
        c r * c (π r) * (if π (π r) = i then 1 else 0) := by
    intro r i
    rw [hSe, map_smul, hSe, smul_smul]
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, e, Finsupp.single_apply,
      Sum.inr.injEq, mul_ite, mul_one, mul_zero]
  have hvalinl : ∀ r j, (e r + S (e r) + S (S (e r))) (Sum.inl j) = 0 := by
    intro r j
    rw [hSe, map_smul, hSe, smul_smul]
    simp [e, Finsupp.single_apply]
  let fam : ↥T ⊕ ↥R → Q := Sum.elim
    (fun t => ⟨e t.1, (hmemQ _).2
      ⟨by rw [hSe, (hTm t.1 t.2).1, (hTm t.1 t.2).2, one_smul], he_inl t.1⟩⟩)
    (fun r => ⟨e r + S (e r) + S (S (e r)), (hmemQ _).2
      ⟨by rw [map_add, map_add, hS3e, (hRP r r.2).2, one_smul]; abel, hvalinl r⟩⟩)
  have hmov : ∀ r ∈ R, π r ≠ r := fun r hr => (hRP r hr).1
  have hmov2 : ∀ r ∈ R, π (π r) ≠ r := fun r hr h => hmov r hr (by
    have h' := congrArg π h
    rwa [hπ3, eq_comm] at h')
  have hΨfam : ∀ s s', Ψ (fam s) s' = (Pi.single s 1 : ↥T ⊕ ↥R → L) s' := by
    rintro (t | r) (t' | r')
    · change e t.1 (Sum.inr t'.1) = _
      simp only [e, Finsupp.single_apply, Sum.inr.injEq, Pi.single_apply, Sum.inl.injEq]
      by_cases h : t = t'
      · subst h
        simp
      · rw [if_neg (fun h' => h (Subtype.ext h')), if_neg (Ne.symm h)]
    · change e t.1 (Sum.inr r'.1) = _
      simp only [e, Finsupp.single_apply, Sum.inr.injEq, Pi.single_apply]
      rw [if_neg (fun h => hmov r'.1 r'.2 (by rw [← h]; exact (hTm t.1 t.2).1)),
        if_neg Sum.inr_ne_inl]
    · change (e r.1 + S (e r.1) + S (S (e r.1))) (Sum.inr t'.1) = _
      rw [hval, Pi.single_apply, if_neg Sum.inl_ne_inr]
      have ht' := (hTm t'.1 t'.2).1
      rw [if_neg (fun h => hmov r.1 r.2 (by rw [h]; exact ht')),
        if_neg (fun h => hmov r.1 r.2 (by rw [hπinj (h.trans ht'.symm)]; exact ht')),
        if_neg (fun h => hmov2 r.1 r.2 (by
          have h' := congrArg π h
          rw [hπ3, ht'] at h'
          rw [h]
          exact h'.symm))]
      ring
    · change (e r.1 + S (e r.1) + S (S (e r.1))) (Sum.inr r'.1) = _
      rw [hval, Pi.single_apply]
      by_cases h : r = r'
      · subst h
        rw [if_pos rfl, if_neg (hmov r.1 r.2), if_neg (hmov2 r.1 r.2), if_pos rfl]
        ring
      · obtain ⟨h1, h2⟩ := hR2 r.1 r.2 r'.1 r'.2
        rw [if_neg (fun h' => h (Subtype.ext h')), if_neg (Ne.symm h1), if_neg (Ne.symm h2),
          if_neg (fun h' => h (Sum.inr_injective h').symm)]
        ring
  have hle : Module.finrank L Q ≤ Fintype.card (↥T ⊕ ↥R) := by
    have h := LinearMap.finrank_le_finrank_of_injective hΨ
    rwa [Module.finrank_fintype_fun_eq_card] at h
  have hge : Fintype.card (↥T ⊕ ↥R) ≤ Module.finrank L Q := by
    have hli : LinearIndependent L fam := by
      refine LinearIndependent.of_comp Ψ ?_
      have e' : (Ψ ∘ fam) = ⇑(Pi.basisFun L (↥T ⊕ ↥R)) := funext fun s => by
        rw [Function.comp_apply, Pi.basisFun_apply]
        funext s'
        exact hΨfam s s'
      rw [e']
      exact (Pi.basisFun L _).linearIndependent
    exact hli.fintype_card_le_finrank
  have hT1 : Nat.card {i // π i = i ∧ c i = 1} = T.card := by
    rw [← Fintype.card_coe T, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i => by simp [hT])
  rw [le_antisymm hle hge, Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, hT1, ← hRc]
  omega

end Abstract

section Cartan

open CFSG.LieType.Chevalley.RootWalk (hVecSum hStep hVecSum_single prod_weylElt_hVecSum)

private def fdEps (k : Fin Tag.E6.rank) : ℤ :=
  if k.val = 1 ∨ k.val = 2 ∨ k.val = 4 then -1 else 1

private theorem fdEps_mul_self : fdEps * fdEps = 1 := by
  funext k
  revert k
  decide +kernel

private theorem fdEps_cartan : ∀ i j : Fin Tag.E6.rank,
    ((Tag.E6.cartan j i).natAbs : ℤ) = fdEps i * fdEps j * Tag.E6.cartan i j := by
  decide +kernel

private theorem fd_hStep (i : Fin Tag.E6.rank) (c : Fin Tag.E6.rank → ℤ) :
    hStep Tag.E6 i c = fdEps * reflect Tag.E6 i (fdEps * c) := by
  have hε : ∀ k, fdEps k * fdEps k = 1 := fun k => congrFun fdEps_mul_self k
  funext k
  simp only [hStep, reflect, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  by_cases hki : k = i
  · subst hki
    simp only [if_true, mul_one]
    have hs : ∑ j, ((Tag.E6.cartan j k).natAbs : ℤ) * c j =
        fdEps k * ∑ j, Tag.E6.cartan k j * (fdEps j * c j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fdEps_cartan k j]
      ring
    rw [hs]
    linear_combination (-c k) * hε k
  · simp only [hki, if_false, mul_zero, sub_zero]
    rw [← mul_assoc, hε k, one_mul]

private theorem fd_foldr_hStep (μ : List (Fin Tag.E6.rank)) (c : Fin Tag.E6.rank → ℤ) :
    μ.foldr (hStep Tag.E6) c =
      fdEps * ((coxeterSystem Tag.E6).wordProd μ • (fdEps * c)) := by
  induction μ with
  | nil => rw [List.foldr_nil, CoxeterSystem.wordProd_nil, one_smul, ← mul_assoc,
      fdEps_mul_self, one_mul]
  | cons i μ ih =>
    rw [List.foldr_cons, ih, fd_hStep, ← mul_assoc, fdEps_mul_self, one_mul,
      CoxeterSystem.wordProd_cons, mul_smul]
    rfl

variable {L : Type} [Field L]

private theorem fd_canonicalRep_hVec (w : WeylGroup Tag.E6) (j : Fin Tag.E6.rank) :
    (canonicalRep (coxeterSystem Tag.E6) L w : Module.End L (RootModule Tag.E6 L))
        (hVec Tag.E6 L j) =
      ∑ k, ((fdEps k * fdEps j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k : ℤ) : L) •
        hVec Tag.E6 L k := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω, ← hVecSum_single, prod_weylElt_hVecSum L ω, fd_foldr_hStep]
  simp only [hVecSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : fdEps * (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = fdEps j • Pi.single j 1 := by
    funext m
    by_cases hm : m = j
    · subst hm
      simp
    · simp [Pi.single_apply, hm]
  rw [h1, smul_comm ((coxeterSystem Tag.E6).wordProd ω) (fdEps j), Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (fdEps k) (fdEps j)]

private def fdPhi (L : Type) [Field L] : (Fin Tag.E6.rank → L) →ₗ[L] RootModule Tag.E6 L where
  toFun d := ∑ j, ((fdEps j : L) * d j) • hVec Tag.E6 L j
  map_add' d d' := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' a d := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_left_comm]

private theorem fdPhi_inl (d : Fin Tag.E6.rank → L) (k : Fin Tag.E6.rank) :
    fdPhi L d (Sum.inl k) = (fdEps k : L) * d k := by
  classical
  change (∑ j, ((fdEps j : L) * d j) • hVec Tag.E6 L j) (Sum.inl k) = _
  simp [hVec, Finsupp.single_apply]

private theorem fdPhi_inr (d : Fin Tag.E6.rank → L)
    (i : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) : fdPhi L d (Sum.inr i) = 0 := by
  classical
  change (∑ j, ((fdEps j : L) * d j) • hVec Tag.E6 L j) (Sum.inr i) = _
  simp [hVec, Finsupp.single_apply]

private theorem fdEps_cast_mul_self (k : Fin Tag.E6.rank) :
    ((fdEps k : ℤ) : L) * (fdEps k : L) = 1 := by
  have := congrFun fdEps_mul_self k
  simp only [Pi.mul_apply, Pi.one_apply] at this
  rw [← Int.cast_mul, this, Int.cast_one]

private theorem fdPhi_injective : Function.Injective (fdPhi L) := by
  intro d d' h
  funext k
  have h1 := fdPhi_inl d k
  rw [h, fdPhi_inl] at h1
  have hε := fdEps_cast_mul_self (L := L) k
  linear_combination (fdEps k : L) * h1.symm + (d' k - d k) * hε

private theorem fd_monomial_fdPhi (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6)
    (d : Fin Tag.E6.rank → L) :
    ((rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w : ModGL Tag.E6 L) :
        Module.End L (RootModule Tag.E6 L)) (fdPhi L d) =
      fdPhi L (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) d) := by
  have hy : ∀ j, ((rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w :
      ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) (hVec Tag.E6 L j) =
      ∑ k, ((fdEps k * fdEps j * (w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k : ℤ) : L) •
        hVec Tag.E6 L k := by
    intro j
    rw [Units.val_mul, Module.End.mul_apply]
    change rootDiag a ((canonicalRep (coxeterSystem Tag.E6) L w :
      Module.End L (RootModule Tag.E6 L)) (hVec Tag.E6 L j)) = _
    rw [rootDiag_canonicalRep_hVec, fd_canonicalRep_hVec]
  change _ = ∑ k, ((fdEps k : L) * (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) d k)) •
    hVec Tag.E6 L k
  change ((rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w : ModGL Tag.E6 L) :
    Module.End L (RootModule Tag.E6 L)) (∑ j, ((fdEps j : L) * d j) • hVec Tag.E6 L j) = _
  simp only [map_sum, map_smul, hy, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hε := fdEps_cast_mul_self (L := L) j
  simp only [Matrix.map_apply, CFSG.RankThree.E6.weylMatrix_apply, Int.cast_mul]
  linear_combination ((fdEps k : L) * ((w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) k : L) *
    d j) * hε

private theorem fd_finrank_inl (Y : Module.End L (RootModule Tag.E6 L))
    (W : Module.End L (Fin Tag.E6.rank → L)) (hYΦ : ∀ d, Y (fdPhi L d) = fdPhi L (W d)) :
    Module.finrank L ↥(LinearMap.ker (Y - 1) ⊓ Finsupp.supported L L (Set.range Sum.inl)) =
      Module.finrank L (LinearMap.ker (W - 1)) := by
  have heq : LinearMap.ker (Y - 1) ⊓ Finsupp.supported L L (Set.range Sum.inl) =
      (LinearMap.ker (W - 1)).map (fdPhi L) := by
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_map]
    constructor
    · rintro ⟨hx, hxl⟩
      have hxl' := (fd_mem_inl x).1 hxl
      set d : Fin Tag.E6.rank → L := fun k => (fdEps k : L) * x (Sum.inl k) with hd
      have hΦd : fdPhi L d = x := by
        ext b
        rcases b with k | i
        · rw [fdPhi_inl, hd]
          simp only
          rw [← mul_assoc, fdEps_cast_mul_self, one_mul]
        · rw [fdPhi_inr, hxl']
      refine ⟨d, fdPhi_injective ?_, hΦd⟩
      rw [← hYΦ, hΦd, hx]
    · rintro ⟨d, hd, rfl⟩
      refine ⟨by rw [hYΦ, hd], (fd_mem_inl _).2 fun i => fdPhi_inr d i⟩
  rw [heq]
  exact (Submodule.equivMapOfInjective (fdPhi L) fdPhi_injective _).finrank_eq.symm

private theorem fd_single_inl_eq (j : Fin Tag.E6.rank) :
    (Finsupp.single (Sum.inl j) 1 : RootModule Tag.E6 L) =
      fdPhi L (Pi.single j (fdEps j : L)) := by
  classical
  ext b
  rcases b with k | i
  · rw [fdPhi_inl, Finsupp.single_apply, Pi.single_apply]
    by_cases hk : k = j
    · subst hk
      rw [if_pos rfl, if_pos rfl, fdEps_cast_mul_self]
    · rw [if_neg (fun h => hk (Sum.inl_injective h).symm), if_neg hk, mul_zero]
  · rw [fdPhi_inr, Finsupp.single_apply, if_neg Sum.inl_ne_inr]

end Cartan

section Main

variable {L : Type} [Field L]

private theorem fd_root_coef (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) :
    ∃ c : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} → L, ∀ γ,
      ((rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w : ModGL Tag.E6 L) :
          Module.End L (RootModule Tag.E6 L)) (Finsupp.single (Sum.inr γ) 1) =
        c γ • Finsupp.single (Sum.inr ⟨w • γ.1, IsRoot.smul γ.2 w⟩) 1 := by
  have h := mapsRootLines_canonicalRep (R := L) (τ := Tag.E6) w
  choose c hc using fun γ : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} => h γ.1 γ.2
  refine ⟨fun γ => ((c γ : Lˣ) : L) * (rootChar a (w • γ.1) : L), fun γ => ?_⟩
  have h1 := rootDiagUnit_canonicalRep_rootVec a w γ.2 (hc γ)
  rw [FourGroupChevalley.rootVec_eq_single γ.2,
    FourGroupChevalley.rootVec_eq_single (IsRoot.smul γ.2 w)] at h1
  rw [Units.val_mul, Module.End.mul_apply]
  exact h1

private theorem fd_card_roots (Q : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} → Prop)
    (P : (Fin Tag.E6.rank → ℤ) → Prop) [DecidablePred P] (hPQ : ∀ γ, Q γ ↔ P γ.1) :
    Nat.card {γ // Q γ} = ((rootFinset Tag.E6).filter P).card := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    { toFun := fun γ => ⟨γ.1.1, Finset.mem_filter.2 ⟨mem_rootFinset.2 γ.1.2, (hPQ γ.1).1 γ.2⟩⟩
      invFun := fun v => ⟨⟨v.1, mem_rootFinset.1 (Finset.mem_filter.1 v.2).1⟩,
        (hPQ _).2 (Finset.mem_filter.1 v.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

open scoped Classical in
theorem finrank_ker_monomial_sub_one_of_eq {τ : Tag} (hτ : τ = Tag.E6) {a : Fin τ.rank → Lˣ}
    {w : WeylGroup τ} (hw3 : w ^ 3 = 1) {y : ModGL τ L}
    (hy : y = rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w) :
    Module.finrank L (LinearMap.ker ((y : Module.End L (RootModule τ L)) - 1)) =
      Module.finrank L (LinearMap.ker
        (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) - 1)) +
      ((rootFinset τ).filter fun γ => w • γ = γ ∧
        (y : Module.End L (RootModule τ L)) (rootVec τ L γ) = rootVec τ L γ).card +
      ((rootFinset τ).filter fun γ => w • γ ≠ γ ∧
        ((y ^ 3 : ModGL τ L) : Module.End L (RootModule τ L))
          (rootVec τ L γ) = rootVec τ L γ).card / 3 := by
  subst hτ
  set Y : Module.End L (RootModule Tag.E6 L) := (y : Module.End L (RootModule Tag.E6 L))
    with hYdef
  have hYΦ : ∀ d, Y (fdPhi L d) =
      fdPhi L (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) d) := by
    intro d
    rw [hYdef, hy]
    exact fd_monomial_fdPhi a w d
  obtain ⟨c, hc⟩ := fd_root_coef a w
  let π : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} →
      {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v} := fun γ => ⟨w • γ.1, IsRoot.smul γ.2 w⟩
  have hπ3 : ∀ γ, π (π (π γ)) = γ := fun γ => Subtype.ext (by
    change w • w • w • γ.1 = γ.1
    rw [smul_smul, smul_smul, ← pow_three', hw3, one_smul])
  have hYr : ∀ γ, Y (Finsupp.single (Sum.inr γ) 1) = c γ • Finsupp.single (Sum.inr (π γ)) 1 := by
    intro γ
    rw [hYdef, hy]
    exact hc γ
  have hSl : ∀ j, Y (Finsupp.single (Sum.inl j) 1) ∈ Finsupp.supported L L (Set.range Sum.inl) := by
    intro j
    rw [fd_single_inl_eq, hYΦ]
    exact (fd_mem_inl _).2 fun i => fdPhi_inr _ i
  have hSh : ∀ j i, Y (Finsupp.single (Sum.inl j) 1) (Sum.inr i) = 0 :=
    fun j i => (fd_mem_inl _).1 (hSl j) i
  have hSr : ∀ γ, Y (Finsupp.single (Sum.inr γ) 1) ∈ Finsupp.supported L L (Set.range Sum.inr) := by
    intro γ
    rw [hYr]
    exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported L _ ⟨_, rfl⟩)
  have hrv : ∀ γ : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v},
      rootVec Tag.E6 L γ.1 = Finsupp.single (Sum.inr γ) 1 :=
    fun γ => FourGroupChevalley.rootVec_eq_single γ.2
  have hY3 : ∀ γ, ((y ^ 3 : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
      (Finsupp.single (Sum.inr γ) 1) =
        (c γ * c (π γ) * c (π (π γ))) • Finsupp.single (Sum.inr γ) 1 := by
    intro γ
    rw [Units.val_pow_eq_pow_val, pow_three, Module.End.mul_apply, Module.End.mul_apply]
    change Y (Y (Y (Finsupp.single (Sum.inr γ) 1))) = _
    simp only [hYr, map_smul, hπ3, smul_smul, mul_assoc]
  have hsmul : ∀ (γ : {v : Fin Tag.E6.rank → ℤ // IsRoot Tag.E6 v}) (t : L),
      t • (Finsupp.single (Sum.inr γ) 1 : RootModule Tag.E6 L) = Finsupp.single (Sum.inr γ) 1 ↔
        t = 1 := by
    intro γ t
    constructor
    · intro h
      have h1 := congrArg (fun v : RootModule Tag.E6 L => v (Sum.inr γ)) h
      simpa using h1
    · rintro rfl
      exact one_smul _ _
  have hcard1 : Nat.card {γ // π γ = γ ∧ c γ = 1} = ((rootFinset Tag.E6).filter fun γ =>
      w • γ = γ ∧ Y (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ).card := by
    refine fd_card_roots _ _ fun γ => ?_
    have hπγ : π γ = γ ↔ w • γ.1 = γ.1 :=
      ⟨congrArg Subtype.val, fun h => Subtype.ext (show (π γ).1 = γ.1 from h)⟩
    rw [hπγ, hrv, hYr]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [Subtype.ext (show (π γ).1 = γ.1 from h1), h2, one_smul]
    · rintro ⟨h1, h2⟩
      rw [Subtype.ext (show (π γ).1 = γ.1 from h1)] at h2
      exact ⟨h1, (hsmul γ _).1 h2⟩
  have hcard2 : Nat.card {γ // π γ ≠ γ ∧ c γ * c (π γ) * c (π (π γ)) = 1} =
      ((rootFinset Tag.E6).filter fun γ => w • γ ≠ γ ∧
        ((y ^ 3 : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
          (rootVec Tag.E6 L γ) = rootVec Tag.E6 L γ).card := by
    refine fd_card_roots _ _ fun γ => ?_
    have hπγ : π γ ≠ γ ↔ w • γ.1 ≠ γ.1 :=
      not_congr ⟨congrArg Subtype.val, fun h => Subtype.ext (show (π γ).1 = γ.1 from h)⟩
    rw [hπγ, hrv, hY3, hsmul]
  rw [fd_split Y hSl hSr, fd_finrank_inl Y _ hYΦ, fd_finrank_inr Y π hπ3 c hYr hSh, hcard1,
    hcard2, add_assoc]

end Main

section HTerm

variable {L : Type} [Field L]

theorem finrank_ker_weylMatrix_sub_one_eq_zero (h3 : (3 : L) ≠ 0) {τ : Tag} {w : WeylGroup τ}
    (hN : ∀ β : Fin τ.rank → ℤ, β + w • β + w • w • β = 0) :
    Module.finrank L (LinearMap.ker
      (Matrix.toLin' ((weylMatrix w).map (Int.cast : ℤ → L)) - 1)) = 0 := by
  set M := (weylMatrix w).map (Int.cast : ℤ → L) with hM
  have hMM : M * M = (weylMatrix (w * w)).map (Int.cast : ℤ → L) := by
    rw [CFSG.RankThree.E6.weylMatrix_mul, hM]
    exact (Matrix.map_mul (f := Int.castRingHom L)).symm
  have hsum : 1 + M + M * M = 0 := by
    rw [hMM]
    ext i j
    have h := congrFun (hN (Pi.single j 1)) i
    simp only [Pi.add_apply, Pi.zero_apply] at h
    simp only [Matrix.add_apply, Matrix.one_apply, hM, Matrix.map_apply,
      CFSG.RankThree.E6.weylMatrix_apply, Matrix.zero_apply, mul_smul]
    have h' := congrArg (Int.cast : ℤ → L) h
    rw [Int.cast_add, Int.cast_add, Int.cast_zero, Pi.single_apply] at h'
    simp only [Int.cast_ite, Int.cast_one, Int.cast_zero] at h'
    exact h'
  rw [Submodule.finrank_eq_zero, eq_bot_iff]
  intro d hd
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    Matrix.toLin'_apply] at hd
  have h0 : Matrix.mulVec (1 + M + M * M) d = 0 := by rw [hsum, Matrix.zero_mulVec]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hd,
    hd] at h0
  rw [Submodule.mem_bot]
  have h3d : (3 : L) • d = 0 := by
    rw [← h0]
    funext k
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  exact (smul_eq_zero.1 h3d).resolve_left h3

end HTerm

section BaseChange

theorem finrank_ker_conj_baseChangeGL_sub_one {τ : Tag} {K L : Type} [Field K] [Field L]
    [Algebra K L] (g₀ : ModGL τ L) (g : ModGL τ K) :
    Module.finrank L (LinearMap.ker (((g₀⁻¹ * baseChangeGL (algebraMap K L) g * g₀ :
        ModGL τ L) : Module.End L (RootModule τ L)) - 1)) =
      Module.finrank K (LinearMap.ker ((g : Module.End K (RootModule τ K)) - 1)) := by
  have e : g₀⁻¹ * baseChangeGL (algebraMap K L) g * g₀ =
      g₀⁻¹ * baseChangeGL (algebraMap K L) g * g₀⁻¹⁻¹ := by rw [inv_inv]
  have h := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.finrank_ker_baseChangeEnd
    (L := L) ((g : Module.End K (RootModule τ K)) - 1)
  rw [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.baseChangeEnd_sub_aux,
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.baseChangeEnd_one_aux,
    ← coe_baseChangeGL] at h
  rw [e, CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.finrank_ker_conj_sub_one]
  exact h

end BaseChange

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
