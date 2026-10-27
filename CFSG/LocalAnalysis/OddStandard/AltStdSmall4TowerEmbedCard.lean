module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4TowerDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4GL62Code
import Mathlib.Data.List.GetD

public section

namespace CFSG.OddStandard.AltStdSmall4.Tower

open Subgroup GL62.Code

section Closure

private def wordGL (gens : List (GL (Fin 6) (ZMod 2))) (w : List ℕ) : GL (Fin 6) (ZMod 2) :=
  (w.map fun i => gens.getD i 1).prod

private def wordCode (gc w : List ℕ) : ℕ :=
  w.foldr (fun i acc => mul (gc.getD i one) acc) one

private def closedB (codes gc : List ℕ) : Bool :=
  codes.all fun c => gc.all fun g => codes.contains (mul c g)

private theorem wordGL_mem (gens : List (GL (Fin 6) (ZMod 2))) (w : List ℕ) :
    wordGL gens w ∈ closure {x | x ∈ gens} := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  rw [List.getD_eq_getElem?_getD]
  cases h : gens[i]? with
  | none => exact one_mem _
  | some g => exact subset_closure (List.mem_of_getElem? h)

private theorem mat_getD {gens : List (GL (Fin 6) (ZMod 2))} {gc : List ℕ}
    (hgc : gc.map mat = gens.map Units.val) (i : ℕ) :
    mat (gc.getD i one) = (gens.getD i 1).val := by
  rw [← List.getD_map gc one mat, hgc, mat_one, ← Units.val_one, List.getD_map]

private theorem mat_wordCode {gens : List (GL (Fin 6) (ZMod 2))} {gc : List ℕ}
    (hgc : gc.map mat = gens.map Units.val) (w : List ℕ) :
    mat (wordCode gc w) = (wordGL gens w).val := by
  induction w with
  | nil => simp [wordCode, wordGL, mat_one]
  | cons i w ih =>
    have h : wordGL gens (i :: w) = gens.getD i 1 * wordGL gens w := by simp [wordGL]
    rw [h, Units.val_mul, ← ih, ← mat_getD hgc, ← mat_mul]
    rfl

private theorem wordCode_lt (gc w : List ℕ) : wordCode gc w < 2 ^ 36 := by
  cases w with
  | nil => exact one_lt
  | cons i w => exact mul_lt _ _

private theorem card_closure_of_codes {gens : List (GL (Fin 6) (ZMod 2))} {gc codes : List ℕ}
    {words : List (List ℕ)}
    (hgc : gc.map mat = gens.map Units.val)
    (hcl : closedB codes gc = true) (hone : one ∈ codes) (hw : words.map (wordCode gc) = codes)
    (hnd : codes.Nodup) :
    Nat.card (closure {x | x ∈ gens}) = codes.length := by
  classical
  simp only [closedB, List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hcl
  set P : GL (Fin 6) (ZMod 2) → Prop := fun x =>
    ∃ c ∈ codes, mat c = (x : Matrix (Fin 6) (Fin 6) (ZMod 2)) with hP
  have hgen : ∀ y ∈ gens, ∃ g ∈ gc, mat g = y.val := by
    intro y hy
    have h : y.val ∈ gc.map mat := by
      rw [hgc]
      exact List.mem_map_of_mem hy
    exact List.mem_map.1 h
  have hstep : ∀ x, P x → ∀ y ∈ gens, P (x * y) := by
    rintro x ⟨c, hc, hcx⟩ y hy
    obtain ⟨g, hg, hgy⟩ := hgen y hy
    exact ⟨mul c g, hcl c hc g hg, by rw [mat_mul, hcx, hgy, Units.val_mul]⟩
  have hpow : ∀ x, P x → ∀ y ∈ gens, ∀ k : ℕ, P (x * y ^ k) := by
    intro x hx y hy k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      exact hstep _ ih y hy
  have hmem : ∀ x ∈ closure {x | x ∈ gens}, P x := by
    intro x hx
    induction hx using Subgroup.closure_induction_right with
    | one => exact ⟨one, hone, by rw [mat_one, Units.val_one]⟩
    | mul_right x _ y hy ih => exact hstep x ih y hy
    | mul_inv_cancel x _ y hy ih =>
      have h1 : y⁻¹ = y ^ (orderOf y - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos y), pow_orderOf_eq_one]
      rw [h1]
      exact hpow x ih y hy _
  have hlt : ∀ c ∈ codes, c < 2 ^ 36 := by
    intro c hc
    rw [← hw] at hc
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hc
    exact wordCode_lt gc w
  let f : closure {x | x ∈ gens} → codes.toFinset := fun x =>
    ⟨Classical.choose (hmem x x.2), List.mem_toFinset.2 (Classical.choose_spec (hmem x x.2)).1⟩
  have hf : ∀ x, mat (f x : ℕ) = ((x : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
    fun x => (Classical.choose_spec (hmem x x.2)).2
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply Units.ext
      rw [← hf x, ← hf y, h]
    · rintro ⟨c, hc⟩
      have hc' := List.mem_toFinset.1 hc
      have hc'' := hc'
      rw [← hw] at hc''
      obtain ⟨w, -, hwc⟩ := List.mem_map.1 hc''
      refine ⟨⟨wordGL gens w, wordGL_mem gens w⟩, Subtype.ext ?_⟩
      apply eq_of_mat_eq (hlt _ (List.mem_toFinset.1 (f _).2)) (hlt c hc')
      rw [hf, ← hwc, mat_wordCode hgc]
  rw [Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hnd]

end Closure

section Data

private def wrGc : List ℕ :=
  [38959071361, 34764505281, 51810164865, 43220299905, 43220226753]

private def wrCodes : List ℕ :=
  [34630287489, 38959071361, 34764505281, 51810164865, 43220299905, 43220226753, 39110066369,
   58286432385, 48622817409, 48622752385, 60534321345, 43354546369, 43354444417, 51944382657,
   60400160897, 60400104129, 67950178433, 43354517697, 34630361793, 48773747393, 60400132801,
   34630398657, 68101107905, 48773845185, 58437427393, 67950113409, 48773812417, 38959137409,
   67950146177, 38959170177, 60400103553, 51944476865, 51944383105, 58437525697, 43220328577,
   34764616321, 51944419969, 34764579457, 43354443969, 60534407361, 60534321793, 60534378689,
   51810222785, 68101108417, 43220255425, 51810259649, 68101173441, 58286498433, 51944440001,
   34764542145, 58437493441, 58437460673, 39110132417, 60534350465, 51810201729, 68101206721,
   67950112897, 58437427905, 48622850177, 39110165185, 48773746881, 68101206209, 48622785153,
   58286531201, 58437492929, 39110099137, 51944440449, 68101141185, 58286465153, 60534407809,
   43220226177, 51810222209, 51810165441, 51810259073, 58286432897, 43354473089, 60534379137,
   58286530689, 60400189569, 34630324353, 67950211713, 51810202305, 60534350017, 34764615873,
   34764505729, 39110164673, 51944477313, 34764542593, 34764579009, 51944419521, 39110099649,
   48773845697, 39110131905, 58437460161, 48773779649, 58286465665, 68101140673, 67950145665,
   48622751873, 58286497921, 48773780161, 68101173953, 67950211201, 38959104129, 60400190145,
   39110066881, 58437526209, 43354546817, 43354472641, 60400132225, 34630361217, 34630288065,
   38959136897, 60400161473, 34630324929, 34630398081, 38959104641, 48622817921, 38959169665,
   48622784641, 38959071873, 43354518145, 48622850689, 48773812929, 67950178945, 43220300481,
   43220254849, 43220329153]

private def wrWords : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 1],
   [2, 3], [2, 4], [3, 0], [3, 1], [3, 4], [4, 0], [4, 2], [4, 3], [0, 1, 2], [0, 1, 3], [0, 2, 1],
   [0, 2, 4], [0, 3, 1], [0, 3, 4], [0, 4, 2], [0, 4, 3], [1, 2, 1], [1, 2, 3], [1, 2, 4],
   [1, 3, 0], [1, 3, 1], [1, 3, 4], [1, 4, 2], [1, 4, 3], [2, 1, 2], [2, 1, 3], [2, 1, 4],
   [2, 3, 1], [2, 3, 4], [2, 4, 0], [2, 4, 2], [2, 4, 3], [3, 0, 1], [3, 0, 4], [3, 1, 2],
   [3, 1, 3], [3, 4, 0], [4, 0, 2], [4, 0, 3], [4, 2, 1], [4, 2, 4], [4, 3, 0], [0, 1, 2, 1],
   [0, 1, 2, 4], [0, 1, 3, 1], [0, 1, 3, 4], [0, 2, 1, 2], [0, 2, 1, 3], [0, 2, 4, 2], [0, 2, 4, 3],
   [0, 3, 1, 2], [0, 3, 1, 3], [0, 3, 4, 0], [0, 4, 2, 1], [0, 4, 2, 4], [0, 4, 3, 0], [1, 2, 1, 2],
   [1, 2, 1, 3], [1, 2, 1, 4], [1, 2, 3, 1], [1, 2, 4, 0], [1, 2, 4, 2], [1, 2, 4, 3], [1, 3, 0, 1],
   [1, 3, 1, 2], [1, 3, 1, 3], [1, 3, 4, 0], [1, 4, 2, 1], [1, 4, 2, 4], [2, 1, 2, 3], [2, 1, 2, 4],
   [2, 1, 3, 0], [2, 1, 3, 4], [2, 1, 4, 2], [2, 3, 1, 2], [2, 3, 1, 3], [2, 4, 0, 2], [2, 4, 3, 0],
   [3, 0, 1, 2], [3, 0, 1, 3], [3, 1, 3, 0], [4, 0, 2, 1], [4, 0, 2, 4], [4, 2, 4, 0],
   [0, 1, 2, 1, 2], [0, 1, 2, 1, 3], [0, 1, 2, 4, 2], [0, 1, 2, 4, 3], [0, 1, 3, 1, 2],
   [0, 1, 3, 1, 3], [0, 1, 3, 4, 0], [0, 2, 1, 2, 4], [0, 2, 1, 3, 4], [0, 2, 4, 3, 0],
   [0, 3, 1, 3, 0], [0, 4, 2, 4, 0], [1, 2, 1, 2, 3], [1, 2, 1, 2, 4], [1, 2, 1, 3, 0],
   [1, 2, 1, 3, 4], [1, 2, 1, 4, 2], [1, 2, 3, 1, 2], [1, 2, 4, 0, 2], [1, 2, 4, 3, 0],
   [1, 3, 0, 1, 2], [1, 3, 1, 3, 0], [2, 1, 2, 4, 0], [2, 1, 2, 4, 3], [2, 1, 3, 4, 0],
   [3, 0, 1, 2, 4], [4, 0, 2, 1, 3], [0, 1, 2, 4, 3, 0], [0, 1, 3, 1, 3, 0], [0, 2, 1, 3, 4, 0]]

private def slGc : List ℕ :=
  [38959071361, 34764505281, 51810164865, 43371221633, 56290009281]

private def slCodes : List ℕ :=
  [34630287489, 38959071361, 34764505281, 51810164865, 43371221633, 56290009281, 39110066369,
   58286432385, 48756970177, 54091923649, 60534321345, 43237003969, 64728985729, 51944382657,
   60551099009, 41257615553, 48639529601, 53034939009, 56273232577, 36912062657, 56139014273,
   50921296065, 65819472513, 61473874049, 68101107905, 63621415041, 58437427393, 68084331201,
   59494425281, 54108701313, 53957705857, 45502001345, 62564422337, 66876403841, 60400103553,
   51826942657, 42180395137, 61490651841, 64745763457, 37851623553, 64879980737, 49696592001,
   57347007169, 53018161345, 43354443969, 60416881345, 67966890625, 35855061633, 41240838849,
   41106620545, 65953689793, 50787078785, 44293996673, 66893181569, 63638192833, 52900721345,
   42314613441, 36794622657, 56155792001, 49830810305, 65802694785, 36777844865, 62681862337,
   45384561345, 47549042817, 65936913089, 50770301057, 41123398273, 35704066177, 45518779009,
   49713369729, 59360206977, 61608091841, 42331390145, 67950112897, 58303210113, 63755632833,
   46441554049, 55182480001, 59511201985, 48773746881, 40167064257, 36928840321, 59376984705,
   38002619009, 53974483649, 46592549505, 62547644545, 62698640001, 45367783553, 40032845953,
   50904519361, 46458331841, 52883943553, 67027398849, 37985841345, 43220226177, 51961160321,
   58420650689, 35720843969, 42197172865, 57212788865, 44428214465, 61624869505, 64863204033,
   57363783873, 55031484545, 47700037825, 57229566593, 49847587009, 35838283969, 34647065281,
   44310774465, 47565820545, 67010622145, 63772410497, 55165702337, 55048262337, 40049623681,
   44444992129, 39093289665, 46575771841, 48622751873, 37868401345, 40183840961, 38975849089,
   47683261121, 34781282945]

private def slWords : List (List ℕ) :=
  [[], [0], [1], [2], [3], [4], [0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 1],
   [2, 3], [2, 4], [3, 0], [3, 2], [3, 4], [4, 0], [4, 1], [4, 2], [4, 3], [4, 4], [0, 1, 2],
   [0, 1, 4], [0, 2, 1], [0, 2, 3], [0, 3, 2], [0, 3, 4], [0, 4, 1], [0, 4, 2], [0, 4, 3],
   [0, 4, 4], [1, 2, 1], [1, 2, 3], [1, 2, 4], [1, 3, 2], [1, 3, 4], [1, 4, 0], [1, 4, 1],
   [1, 4, 2], [1, 4, 3], [1, 4, 4], [2, 1, 2], [2, 1, 3], [2, 3, 0], [2, 3, 2], [2, 3, 4],
   [2, 4, 1], [2, 4, 2], [2, 4, 3], [2, 4, 4], [3, 0, 2], [3, 0, 4], [3, 2, 1], [3, 2, 4],
   [3, 4, 0], [3, 4, 1], [3, 4, 2], [3, 4, 3], [4, 0, 1], [4, 0, 2], [4, 0, 3], [4, 0, 4],
   [4, 1, 3], [4, 2, 1], [4, 2, 3], [4, 2, 4], [4, 3, 0], [4, 3, 2], [4, 4, 0], [4, 4, 1],
   [4, 4, 4], [0, 1, 2, 1], [0, 1, 2, 3], [0, 1, 4, 1], [0, 1, 4, 2], [0, 1, 4, 3], [0, 1, 4, 4],
   [0, 2, 1, 2], [0, 2, 3, 2], [0, 2, 3, 4], [0, 3, 2, 1], [0, 3, 2, 4], [0, 3, 4, 1], [0, 3, 4, 2],
   [0, 3, 4, 3], [0, 4, 1, 3], [0, 4, 2, 1], [0, 4, 2, 4], [0, 4, 3, 0], [0, 4, 3, 2], [0, 4, 4, 0],
   [0, 4, 4, 1], [0, 4, 4, 4], [1, 2, 1, 2], [1, 2, 1, 3], [1, 2, 3, 0], [1, 2, 3, 2], [1, 2, 3, 4],
   [1, 2, 4, 2], [1, 2, 4, 4], [1, 3, 2, 1], [1, 3, 4, 1], [1, 3, 4, 3], [1, 4, 0, 2], [1, 4, 0, 4],
   [1, 4, 1, 3], [1, 4, 2, 1], [1, 4, 2, 4], [2, 1, 2, 3], [2, 1, 3, 2], [2, 3, 0, 2], [3, 0, 2, 1],
   [3, 0, 4, 1], [3, 0, 4, 3], [3, 4, 0, 2], [3, 4, 0, 4], [3, 4, 2, 4], [4, 3, 0, 4], [4, 4, 0, 4],
   [0, 1, 2, 1, 2], [0, 1, 2, 3, 4], [0, 1, 4, 2, 4], [0, 2, 1, 2, 3], [0, 3, 4, 2, 4],
   [0, 4, 3, 0, 4]]
end Data

private theorem wrS_eq :
    wrS = closure {x | x ∈ [GL62.z₀, GL62.dg e12, GL62.dg e23, wrH₁, wrH₂]} := by
  rw [wrS]
  congr 1
  ext x
  simp

private theorem slS_eq :
    slS = closure {x | x ∈ [GL62.z₀, GL62.dg e12, GL62.dg e23, slH₁, slH₂]} := by
  rw [slS]
  congr 1
  ext x
  simp

private theorem wrGc_eq : wrGc.map mat = [GL62.z₀, GL62.dg e12, GL62.dg e23, wrH₁, wrH₂].map
    Units.val := by
  decide

private theorem slGc_eq : slGc.map mat = [GL62.z₀, GL62.dg e12, GL62.dg e23, slH₁, slH₂].map
    Units.val := by
  decide

theorem card_wrS : Nat.card wrS = 2 ^ 7 := by
  rw [wrS_eq, card_closure_of_codes (codes := wrCodes) (words := wrWords) wrGc_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

theorem card_slS : Nat.card slS = 2 ^ 7 := by
  rw [slS_eq, card_closure_of_codes (codes := slCodes) (words := slWords) slGc_eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end CFSG.OddStandard.AltStdSmall4.Tower
