
module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Three

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

noncomputable abbrev ctx : Ctx := mkCtx CFSG.Sporadic.Fi24.orb

theorem packedN_eq : packedN = fo24Packed := by
  funext O
  unfold packedN fo24Packed
  rfl

theorem tPTableN_eq : tPTableN = tPTable := by
  funext O tA tB
  unfold tPTableN tPTable
  rfl

theorem ctx_O : ctx.O = CFSG.Sporadic.Fi24.orb := by unfold ctx mkCtx; rfl

theorem ctx_L : ctx.L = CFSG.Sporadic.Fi24.letters := by unfold ctx mkCtx; rfl

theorem ctx_bInv : ctx.bInv = fo24BInv := by unfold ctx mkCtx; rfl

theorem ctx_pl : ctx.pl = fo24PL := by unfold ctx mkCtx; rw [packedN_eq]

theorem ctx_tP : ctx.tP = fi24TP := by
  unfold ctx mkCtx
  simp only
  rw [tPTableN_eq]
  rfl

theorem clsAtN_ctx (k : ℕ) (q : Array ℕ) :
    clsAtN ctx.O ctx.bInv ctx.pl ctx.tP k q = fo24Cls k q := by
  rw [ctx_O, ctx_bInv, ctx_pl, ctx_tP]
  rfl

theorem clsPt_eq (k : Fin 306936) {p : ℕ} (hp : p < 306936) :
    clsPt ctx k p = idx 306936 (cls k) p := by
  have hq : ∀ j < (#[p] : Array ℕ).size, (#[p] : Array ℕ)[j]! < 306936 := by
    intro j hj
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add,
      Nat.lt_one_iff] at hj
    subst hj
    simpa using hp
  have h := (fo24Cls_spec k #[p] hq).2 0 (by simp)
  unfold clsPt
  rw [clsAtN_ctx, h]
  simp

theorem clsPt_eq_smul (k p : Fin 306936) : clsPt ctx k p = (cls k • p).val := by
  rw [clsPt_eq k p.2, idx_of_lt _ p.2]

theorem commB_iff (k l : Fin 306936) : commB ctx k l = true ↔ cls k * cls l = cls l * cls k := by
  unfold commB
  rw [beq_iff_eq, clsPt_eq_smul, ← cls_smul_eq_iff, Fin.val_eq_val]

theorem rep_clsTab (k : Fin 306936) : Rep 306936 (clsTab ctx k) (cls k) := by
  intro i hi
  have h := rep_fo24Cls k i hi
  have hs : (fo24Cls k (Array.range nPts)).size = nPts := by
    rw [(fo24Cls_spec k (Array.range nPts) fun j hj => by
      rw [getElem!_pos _ j hj, Array.getElem_range]
      rw [Array.size_range] at hj
      exact hj).1, Array.size_range]
  have hi' : i < (fo24Cls k (Array.range nPts)).size := by rw [hs]; exact hi
  unfold clsTab ap
  rw [clsAtN_ctx, getElem!_pos _ i (by simpa using hi'), Array.getElem_map,
    ← getElem!_pos _ i hi', h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt]
  exact lt_trans (idx_lt _ hi) (by norm_num)

theorem letters_size_eq : CFSG.Sporadic.Fi24.letters.size = 26 := by
  rw [CFSG.Sporadic.Fi24.letters_size, CFSG.Sporadic.Fi24.actionFacts.words_size]

theorem rep_letter {l : ℕ} (hl : l < CFSG.Sporadic.Fi24.letters.size) :
    Rep 306936 CFSG.Sporadic.Fi24.letters[l]! (pairG CFSG.Sporadic.Fi24.gs l) :=
  CFSG.Sporadic.Fi24.rep_pairG_all l hl

theorem rep_wordTab (w : List ℕ) (hw : ∀ l ∈ w, l < CFSG.Sporadic.Fi24.letters.size) :
    Rep 306936 (wordTab ctx w) (wordElt w) := by
  induction w with
  | nil =>
    have e : wordTab ctx [] = idT nPts := by
      unfold wordTab
      exact List.foldr_nil
    have e' : wordElt [] = 1 := by
      unfold wordElt
      rw [List.map_nil, List.prod_nil]
    rw [e, e']
    exact Rep.idT (by norm_num)
  | cons l w ih =>
    have e : wordTab ctx (l :: w) = compT nPts ctx.L[l]! (wordTab ctx w) := by
      unfold wordTab
      exact List.foldr_cons
    have e' : wordElt (l :: w) = pairG CFSG.Sporadic.Fi24.gs l * wordElt w := by
      unfold wordElt
      rw [List.map_cons, List.prod_cons]
    rw [e, e', ctx_L]
    exact Rep.compT (rep_letter (hw l List.mem_cons_self))
      (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem smul_val_of_rep {T : Table} {g : J} (hT : Rep 306936 T g) (p : Fin 306936) :
    (g • p).val = ap T p := by
  rw [hT p p.2, idx_of_lt _ p.2]

theorem smul_val_of_rep_R {T : Table} {g : R} (hT : Rep 306936 T g) (p : Fin 306936) :
    (g • p).val = ap T p := by
  rw [hT p p.2, idx_of_lt _ p.2]

theorem cls_not_mem_JR (k : Fin 306936) : cls k ∉ JR := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.Sporadic.Fi24.cls_mem k)
  apply CFSG.Sporadic.Fi24.tR_not_mem_JR
  have h' := CFSG.Sporadic.Fi24.normal_JR.conj_mem _ h c⁻¹
  rwa [← hc, show c⁻¹ * (c * tR * c⁻¹) * c⁻¹⁻¹ = tR by group] at h'

theorem cls_mul_cls_mem_JR (k l : Fin 306936) : cls k * cls l ∈ JR :=
  (Subgroup.mul_mem_iff_of_index_two CFSG.Sporadic.Fi24.index_JR).2
    (iff_of_false (cls_not_mem_JR k) (cls_not_mem_JR l))

theorem exists_jR_of_mem {x : R} (hx : x ∈ JR) : ∃ g : J, jR g = x := by
  rw [← CFSG.Sporadic.Fi24.range_jR] at hx
  exact hx

theorem smul_eq_iff_commute (g : J) (k : Fin 306936) :
    g • k = k ↔ jR g * cls k = cls k * jR g := by
  rw [← CFSG.Sporadic.Fi24.jR_smul]
  constructor
  · intro h
    have e := CFSG.Sporadic.Fi24.cls_smul_R (jR g) k
    rw [h] at e
    calc jR g * cls k = jR g * cls k * (jR g)⁻¹ * jR g := by group
      _ = cls k * jR g := by rw [← e]
  · intro h
    apply CFSG.Sporadic.Fi24.cls_injective
    rw [CFSG.Sporadic.Fi24.cls_smul_R, h, mul_inv_cancel_right]

theorem smul_eq_iff_commute_R (r : R) (k : Fin 306936) :
    r • k = k ↔ r * cls k = cls k * r := by
  constructor
  · intro h
    have e := CFSG.Sporadic.Fi24.cls_smul_R r k
    rw [h] at e
    calc r * cls k = r * cls k * r⁻¹ * r := by group
      _ = cls k * r := by rw [← e]
  · intro h
    apply CFSG.Sporadic.Fi24.cls_injective
    rw [CFSG.Sporadic.Fi24.cls_smul_R, h, mul_inv_cancel_right]

theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)

noncomputable def conjHom (r : R) : R →* R :=
  MonoidHom.mk' (fun x => r * x * r⁻¹) (by intro a b; group)

theorem conj_mem_gLAPPrimeCoreOf {s : J} {r : R} (hr : r * jR s = jR s * r) {n : J}
    (hn : n ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J))) :
    ∃ m ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set J)), jR m = r * jR n * r⁻¹ := by
  have := finite_J
  set C := Subgroup.centralizer ({s} : Set J) with hC
  set N := GLAPPrimeCoreOf 3 C with hN
  set X : Subgroup R := (N.map jR).map (conjHom r) with hX
  set S : Subgroup J := X.comap jR with hS
  have hXJ : X ≤ JR := by
    rintro _ ⟨_, ⟨m, -, rfl⟩, rfl⟩
    exact CFSG.Sporadic.Fi24.normal_JR.conj_mem _ (CFSG.Sporadic.Fi24.jR_mem_JR m) r
  have hr' : r⁻¹ * jR s = jR s * r⁻¹ := by
    calc r⁻¹ * jR s = r⁻¹ * (jR s * r) * r⁻¹ := by group
      _ = r⁻¹ * (r * jR s) * r⁻¹ := by rw [hr]
      _ = jR s * r⁻¹ := by group
  have hcomm : ∀ g : J, jR g * jR s = jR s * jR g → g ∈ C := by
    intro g hg
    rw [CFSG.Sporadic.Fi24.mem_centralizer_J]
    apply CFSG.Sporadic.Fi24.jR_injective
    rw [map_mul, map_mul, hg]
  have hcommC : ∀ g ∈ C, jR g * jR s = jR s * jR g := by
    intro g hg
    rw [← map_mul, ← map_mul, CFSG.Sporadic.Fi24.mem_centralizer_J.1 hg]
  have hconj : ∀ c ∈ C, ∃ c' ∈ C, jR c' = r⁻¹ * jR c * r := by
    intro c hc
    obtain ⟨c', hc'⟩ := exists_jR_of_mem (CFSG.Sporadic.Fi24.normal_JR.conj_mem _
      (CFSG.Sporadic.Fi24.jR_mem_JR c) r⁻¹)
    refine ⟨c', hcomm c' ?_, by rw [hc', inv_inv]⟩
    rw [hc', inv_inv]
    have hcs := hcommC c hc
    calc r⁻¹ * jR c * r * jR s = r⁻¹ * jR c * (r * jR s) := by group
      _ = r⁻¹ * jR c * (jR s * r) := by rw [hr]
      _ = r⁻¹ * (jR c * jR s) * r := by group
      _ = r⁻¹ * (jR s * jR c) * r := by rw [hcs]
      _ = (r⁻¹ * jR s) * jR c * r := by group
      _ = (jR s * r⁻¹) * jR c * r := by rw [hr']
      _ = jR s * (r⁻¹ * jR c * r) := by group
  have hSN : S ≤ N := by
    apply le_GLAPPrimeCoreOf_of_normal
    · intro g hg
      obtain ⟨_, ⟨m, hm, rfl⟩, hgm⟩ := hg
      have hgm' : jR g = r * jR m * r⁻¹ := hgm.symm
      apply hcomm
      rw [hgm']
      have hms := hcommC m (GLAPPrimeCoreOf_le C hm)
      calc r * jR m * r⁻¹ * jR s = r * jR m * (r⁻¹ * jR s) := by group
        _ = r * jR m * (jR s * r⁻¹) := by rw [hr']
        _ = r * (jR m * jR s) * r⁻¹ := by group
        _ = r * (jR s * jR m) * r⁻¹ := by rw [hms]
        _ = (r * jR s) * jR m * r⁻¹ := by group
        _ = (jR s * r) * jR m * r⁻¹ := by rw [hr]
        _ = jR s * (r * jR m * r⁻¹) := by group
    · intro c hc g hg
      obtain ⟨_, ⟨m, hm, rfl⟩, hgm⟩ := hg
      have hgm' : jR g = r * jR m * r⁻¹ := hgm.symm
      obtain ⟨c', hc'C, hc'⟩ := hconj c hc
      refine ⟨jR (c' * m * c'⁻¹), ⟨c' * m * c'⁻¹, GLAPPrimeCoreOf_conj_mem c' hc'C m hm, rfl⟩, ?_⟩
      show r * jR (c' * m * c'⁻¹) * r⁻¹ = jR (c * g * c⁻¹)
      rw [map_mul, map_mul, map_inv, hc', map_mul, map_mul, map_inv, hgm']
      group
    · have h1 : Nat.card S = Nat.card X := by
        have hmap : S.map jR = X := Subgroup.map_comap_eq_self (by
          rw [CFSG.Sporadic.Fi24.range_jR]; exact hXJ)
        rw [← hmap, Subgroup.card_map_of_injective CFSG.Sporadic.Fi24.jR_injective]
      have hinj : Function.Injective (conjHom r) := by
        intro a b hab
        have : r * a * r⁻¹ = r * b * r⁻¹ := hab
        simpa using this
      have h2 : Nat.card X = Nat.card N := by
        rw [hX, Subgroup.card_map_of_injective hinj,
          Subgroup.card_map_of_injective CFSG.Sporadic.Fi24.jR_injective]
      rw [h1, h2]
      exact coprime_card_GLAPPrimeCoreOf Nat.prime_three C
  obtain ⟨m, hm⟩ := exists_jR_of_mem (CFSG.Sporadic.Fi24.normal_JR.conj_mem _
    (CFSG.Sporadic.Fi24.jR_mem_JR n) r)
  refine ⟨m, hSN ?_, hm⟩
  show jR m ∈ X
  rw [hm]
  exact ⟨jR n, ⟨n, hn, rfl⟩, rfl⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
