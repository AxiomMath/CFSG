module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinTbl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs

public section

namespace CFSG.QuasithinUnique.Unc25G2

namespace M2x

open Equiv Tbl

variable {n : ℕ}

@[expose] def parsePairs (s : String) : List (ℕ × ℕ) :=
  (s.splitOn " ").filterMap fun w =>
    match w.splitOn "," with
    | [p, k] => some (p.toNat!, k.toNat!)
    | _ => none

@[expose] def letterT (n : ℕ) (ta tb : List ℕ) : ℕ → List ℕ
  | 0 => ta
  | 1 => tb
  | 2 => invT n ta
  | _ => invT n tb

@[expose] def wordT (n : ℕ) (ta tb : List ℕ) (w : List ℕ) : List ℕ :=
  w.foldl (fun acc l => mulT acc (letterT n ta tb l)) (List.range n)

@[expose] def conjT (n : ℕ) (s y : List ℕ) : List ℕ := mulT (mulT s y) (invT n s)

@[expose] def bfs (op : List ℕ → List ℕ → List ℕ) (d : List ℕ) (gens : List (List ℕ))
    (start : List ℕ) (par : List (ℕ × ℕ)) : List (List ℕ) :=
  par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) [start]

@[expose] def spanT (n : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => [List.range n]
  | e :: l => spanT n l ++ (spanT n l).map (mulT e)

theorem getD_mem_or {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (not_lt.mp h)

theorem bfs_prop (R : List ℕ → Prop) {op : List ℕ → List ℕ → List ℕ} {d : List ℕ}
    {gens : List (List ℕ)} {start : List ℕ} (par : List (ℕ × ℕ)) (hstart : R start)
    (hop : ∀ x g, R x → (g = d ∨ g ∈ gens) → R (op x g)) :
    ∀ t ∈ bfs op d gens start par, R t := by
  unfold bfs
  suffices h : ∀ (par : List (ℕ × ℕ)) (acc : List (List ℕ)), (∀ t ∈ acc, R t) →
      ∀ t ∈ par.foldl (fun acc pk => acc ++ [op (acc.getD pk.1 start) (gens.getD pk.2 d)]) acc, R t from
    h par [start] (by simpa using hstart)
  intro par
  induction par with
  | nil => intro acc h; simpa using h
  | cons pk par ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    intro t ht
    rw [List.mem_append] at ht
    rcases ht with ht | ht
    · exact hacc t ht
    · rw [List.mem_singleton] at ht
      subst ht
      apply hop
      · rcases getD_mem_or acc pk.1 start with h | h
        · exact hacc _ h
        · rw [h]; exact hstart
      · rcases getD_mem_or gens pk.2 d with h | h
        · exact Or.inr h
        · exact Or.inl h

section Real

variable (M : Subgroup (Perm (Fin n)))

@[expose] def Real (t : List ℕ) : Prop := ∃ σ ∈ M, tbl σ = t

variable {M}

theorem real_one : Real M (List.range n) := ⟨1, M.one_mem, tbl_one⟩

theorem Real.mul {s t : List ℕ} (hs : Real M s) (ht : Real M t) : Real M (mulT s t) := by
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨τ, hτ, rfl⟩ := ht
  exact ⟨σ * τ, M.mul_mem hσ hτ, tbl_mul σ τ⟩

theorem Real.inv {t : List ℕ} (ht : Real M t) : Real M (invT n t) := by
  obtain ⟨σ, hσ, rfl⟩ := ht
  exact ⟨σ⁻¹, M.inv_mem hσ, tbl_inv σ⟩

theorem real_letter {ta tb : List ℕ} (ha : Real M ta) (hb : Real M tb) (l : ℕ) :
    Real M (letterT n ta tb l) := by
  rcases l with _ | _ | _ | l
  · exact ha
  · exact hb
  · exact ha.inv
  · exact hb.inv

theorem real_wordT {ta tb : List ℕ} (ha : Real M ta) (hb : Real M tb) (w : List ℕ) :
    Real M (wordT n ta tb w) := by
  unfold wordT
  suffices h : ∀ (acc : List ℕ), Real M acc →
      Real M (w.foldl (fun acc l => mulT acc (letterT n ta tb l)) acc) from h _ real_one
  induction w with
  | nil => intro acc h; exact h
  | cons l w ih => intro acc h; exact ih _ (h.mul (real_letter ha hb l))

theorem ncard_tables {L : List (List ℕ)} (hnd : L.Nodup) (hreal : ∀ t ∈ L, Real M t) :
    ({x : ↥M | tbl (x : Perm (Fin n)) ∈ L} : Set ↥M).ncard = L.length := by
  have hinj : Function.Injective (fun x : ↥M => tbl (x : Perm (Fin n))) :=
    fun x y h => Subtype.ext (tbl_injective h)
  have himg : (fun x : ↥M => tbl (x : Perm (Fin n))) ''
      {x : ↥M | tbl (x : Perm (Fin n)) ∈ L} = (L.toFinset : Set (List ℕ)) := by
    ext t
    simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro ht
      obtain ⟨σ, hσ, rfl⟩ := hreal t ht
      exact ⟨⟨σ, hσ⟩, ht, rfl⟩
  rw [← Set.ncard_image_of_injective _ hinj, himg, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hnd]

end Real

abbrev TabClosed (n : ℕ) (L : List (List ℕ)) : Prop :=
  List.range n ∈ L ∧ (∀ s ∈ L, ∀ t ∈ L, mulT s t ∈ L) ∧ (∀ t ∈ L, invT n t ∈ L)

@[expose] def tabSubM (M : Subgroup (Perm (Fin n))) (L : List (List ℕ)) (h : TabClosed n L) :
    Subgroup ↥M where
  carrier := {x | tbl (x : Perm (Fin n)) ∈ L}
  mul_mem' := by
    intro x y hx hy
    show tbl ((x : Perm (Fin n)) * (y : Perm (Fin n))) ∈ L
    rw [tbl_mul]
    exact h.2.1 _ hx _ hy
  one_mem' := by
    show tbl (1 : Perm (Fin n)) ∈ L
    rw [tbl_one]
    exact h.1
  inv_mem' := by
    intro x hx
    show tbl ((x : Perm (Fin n))⁻¹) ∈ L
    rw [tbl_inv]
    exact h.2.2 _ hx

theorem mem_tabSubM {M : Subgroup (Perm (Fin n))} {L : List (List ℕ)} {h : TabClosed n L}
    {x : ↥M} : x ∈ tabSubM M L h ↔ tbl (x : Perm (Fin n)) ∈ L := Iff.rfl

theorem card_tabSubM {M : Subgroup (Perm (Fin n))} {L : List (List ℕ)} {h : TabClosed n L}
    (hnd : L.Nodup) (hreal : ∀ t ∈ L, Real M t) : Nat.card (tabSubM M L h) = L.length :=
  (Nat.card_coe_set_eq ((tabSubM M L h : Subgroup ↥M) : Set ↥M)).trans (ncard_tables hnd hreal)

theorem elemAb_tabSubM {M : Subgroup (Perm (Fin n))} {E : List (List ℕ)} {h : TabClosed n E}
    (hcomm : ∀ s ∈ E, ∀ t ∈ E, mulT s t = mulT t s) (hsq : ∀ t ∈ E, mulT t t = List.range n) :
    ElemAb (tabSubM M E h) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    exact (mul_comm_iff_tbl (x : Perm (Fin n)) y).mpr (hcomm _ hx _ hy)
  · apply Subtype.ext
    apply tbl_injective
    show tbl ((x : Perm (Fin n)) * (x : Perm (Fin n))) = tbl (1 : Perm (Fin n))
    rw [tbl_mul, tbl_one]
    exact hsq _ hx

theorem mem_normalizer_of_forall {Γ : Type*} [Group Γ] [Finite Γ] {E : Subgroup Γ} {g : Γ}
    (h : ∀ e ∈ E, g * e * g⁻¹ ∈ E) : g ∈ Subgroup.normalizer (E : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact map_eq_of_forall_mem (MulAut.conj g) h

theorem centralizer_tables {M : Subgroup (Perm (Fin n))} {a : Perm (Fin n)} (ha : a ∈ M)
    {cl Hl : List (List ℕ)} (hclnd : cl.Nodup) (hHnd : Hl.Nodup)
    (hclreal : ∀ t ∈ cl, ∃ σ ∈ M, tbl (σ * a * σ⁻¹) = t) (hHreal : ∀ t ∈ Hl, Real M t)
    (hHcomm : ∀ h ∈ Hl, mulT h (tbl a) = mulT (tbl a) h)
    (hord : Nat.card M = cl.length * Hl.length) (hclpos : 0 < cl.length) :
    ∀ x : ↥M, (⟨a, ha⟩ : ↥M) * x = x * ⟨a, ha⟩ → tbl (x : Perm (Fin n)) ∈ Hl := by
  set z' : ↥M := ⟨a, ha⟩ with hz'
  set Cz : Subgroup ↥M := Subgroup.centralizer ({z'} : Set ↥M) with hCz
  have hHsub : {x : ↥M | tbl (x : Perm (Fin n)) ∈ Hl} ⊆ (Cz : Set ↥M) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := (mul_comm_iff_tbl (x : Perm (Fin n)) a).mpr (hHcomm _ hx)
    exact Subtype.ext this.symm
  have hHcard : ({x : ↥M | tbl (x : Perm (Fin n)) ∈ Hl} : Set ↥M).ncard = Hl.length :=
    ncard_tables hHnd hHreal
  have hclreal' : ∀ t ∈ cl, Real M t := fun t ht => by
    obtain ⟨σ, hσ, h⟩ := hclreal t ht
    exact ⟨σ * a * σ⁻¹, M.mul_mem (M.mul_mem hσ ha) (M.inv_mem hσ), h⟩
  have hclsub : {x : ↥M | tbl (x : Perm (Fin n)) ∈ cl} ⊆ conjugatesOf z' := by
    intro x hx
    obtain ⟨σ, hσ, h⟩ := hclreal _ hx
    have hx' : (x : Perm (Fin n)) = σ * a * σ⁻¹ := (tbl_injective h).symm
    show IsConj z' x
    rw [isConj_iff]
    refine ⟨⟨σ, hσ⟩, Subtype.ext ?_⟩
    simpa using hx'.symm
  have hclcard : cl.length ≤ (conjugatesOf z').ncard := by
    rw [← ncard_tables hclnd hclreal']
    exact Set.ncard_le_ncard hclsub (Set.toFinite _)
  have hidx : cl.length ≤ Cz.index := by
    rw [hCz, Subgroup.index_centralizer_eq_ncard]
    exact hclcard
  have hmul : Nat.card Cz * Cz.index = cl.length * Hl.length := by
    rw [Subgroup.card_mul_index, hord]
  have hCzle : Nat.card Cz ≤ Hl.length := by
    have h1 : cl.length * Nat.card Cz ≤ cl.length * Hl.length := by
      calc cl.length * Nat.card Cz ≤ Cz.index * Nat.card Cz := Nat.mul_le_mul_right _ hidx
        _ = Nat.card Cz * Cz.index := Nat.mul_comm _ _
        _ = cl.length * Hl.length := hmul
    exact Nat.le_of_mul_le_mul_left h1 hclpos
  have heq : {x : ↥M | tbl (x : Perm (Fin n)) ∈ Hl} = (Cz : Set ↥M) := by
    apply Set.eq_of_subset_of_ncard_le hHsub
    have h1 : (Cz : Set ↥M).ncard = Nat.card Cz := (Nat.card_coe_set_eq _).symm
    rw [h1, hHcard]
    exact hCzle
  intro x hx
  have : x ∈ (Cz : Set ↥M) := by
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hx
  rw [← heq] at this
  exact this

theorem map_tbl_spanList {M : Subgroup (Perm (Fin n))} (l : List ↥M) :
    (spanList l).map (fun x : ↥M => tbl (x : Perm (Fin n))) =
      spanT n (l.map fun x : ↥M => tbl (x : Perm (Fin n))) := by
  induction l with
  | nil => simp [spanList, spanT, tbl_one]
  | cons e l ih =>
    simp only [spanList, spanT, List.map_cons, List.map_append, List.map_map, ← ih]
    congr 1
    apply List.map_congr_left
    intro y _
    exact tbl_mul _ _


theorem tbl_conj (σ τ : Perm (Fin n)) : tbl (σ * τ * σ⁻¹) = conjT n (tbl σ) (tbl τ) := by
  simp only [conjT, tbl_mul, tbl_inv]

structure Dat where
  ta : List ℕ
  tb : List ℕ
  order : ℕ
  clPar : List (ℕ × ℕ)
  hGensW : List (List ℕ)
  hPar : List (ℕ × ℕ)
  pGensW : List (List ℕ)
  pPar : List (ℕ × ℕ)
  eaGens : List (List ℕ)
  ebGens : List (List ℕ)
  gaW : List ℕ
  gbW : List ℕ

namespace Dat

variable (n : ℕ) (D : Dat)

@[expose] def letters : List (List ℕ) := [D.ta, D.tb, invT n D.ta, invT n D.tb]

@[expose] def cl : List (List ℕ) :=
  bfs (fun x g => conjT n g x) (List.range n) (D.letters n) D.ta D.clPar

@[expose] def hGens : List (List ℕ) := D.hGensW.map (wordT n D.ta D.tb)

@[expose] def Hl : List (List ℕ) := bfs mulT (List.range n) (D.hGens n) (List.range n) D.hPar

@[expose] def pGens : List (List ℕ) := D.pGensW.map (wordT n D.ta D.tb)

@[expose] def Pl : List (List ℕ) := bfs mulT (List.range n) (D.pGens n) (List.range n) D.pPar

@[expose] def Ea : List (List ℕ) := spanT n D.eaGens

@[expose] def Eb : List (List ℕ) := spanT n D.ebGens

@[expose] def gaT : List ℕ := wordT n D.ta D.tb D.gaW

@[expose] def gbT : List ℕ := wordT n D.ta D.tb D.gbW

end Dat

@[expose] def invsOf (n : ℕ) (Pl : List (List ℕ)) : List (List ℕ) :=
  Pl.filter fun t => decide (mulT t t = List.range n)

abbrev EOK (n : ℕ) (Pl E : List (List ℕ)) : Prop :=
  E.Nodup ∧ E.length = 16 ∧ (∀ t ∈ E, t ∈ Pl) ∧ (∀ s ∈ E, ∀ t ∈ E, mulT s t = mulT t s) ∧
    ∀ t ∈ E, mulT t t = List.range n

abbrev SelfCent (Hl E : List (List ℕ)) : Prop :=
  ∀ h ∈ Hl, (∀ e ∈ E, mulT h e = mulT e h) → h ∈ E

abbrev Wit (n : ℕ) (g : List ℕ) (E₁ E₂ : List (List ℕ)) : Prop :=
  (∀ e ∈ E₂, conjT n g e ∈ E₂) ∧ ∃ e ∈ E₁, conjT n g e ∉ E₁

abbrev ClassOK (n : ℕ) (Pl Ea Eb : List (List ℕ)) : Prop :=
  ∀ t1 ∈ invsOf n Pl, ∀ t2 ∈ invsOf n Pl, mulT t1 t2 = mulT t2 t1 →
  ∀ t3 ∈ invsOf n Pl, mulT t1 t3 = mulT t3 t1 → mulT t2 t3 = mulT t3 t2 →
  ∀ t4 ∈ invsOf n Pl, mulT t1 t4 = mulT t4 t1 → mulT t2 t4 = mulT t4 t2 →
    mulT t3 t4 = mulT t4 t3 →
    (spanT n [t1, t2, t3, t4]).dedup.length < 16 ∨
      (∀ s ∈ spanT n [t1, t2, t3, t4], s ∈ Ea) ∨ ∀ s ∈ spanT n [t1, t2, t3, t4], s ∈ Eb

abbrev Check (n : ℕ) (D : Dat) : Prop :=
  (D.cl n).Nodup ∧ (D.Hl n).Nodup ∧ (D.cl n).length * (D.Hl n).length = D.order ∧
  (∀ h ∈ D.Hl n, mulT h D.ta = mulT D.ta h) ∧
  (D.Pl n).Nodup ∧ (D.Pl n).length = 128 ∧ ¬ 2 ∣ D.order / 128 ∧ TabClosed n (D.Pl n) ∧
  TabClosed n (D.Ea n) ∧ TabClosed n (D.Eb n) ∧
  EOK n (D.Pl n) (D.Ea n) ∧ EOK n (D.Pl n) (D.Eb n) ∧
  D.ta ∈ D.Ea n ∧ D.ta ∈ D.Eb n ∧ (∃ t ∈ D.Ea n, t ∉ D.Eb n) ∧
  SelfCent (D.Hl n) (D.Ea n) ∧ SelfCent (D.Hl n) (D.Eb n) ∧
  Wit n (D.gaT n) (D.Ea n) (D.Eb n) ∧ Wit n (D.gbT n) (D.Eb n) (D.Ea n) ∧
  ClassOK n (D.Pl n) (D.Ea n) (D.Eb n)

section Sound

variable {M : Subgroup (Perm (Fin n))}

theorem real_of_mem {Pl : List (List ℕ)} (hPreal : ∀ t ∈ Pl, Real M t) {t : List ℕ}
    (ht : t ∈ Pl) : ∃ x : ↥M, tbl (x : Perm (Fin n)) = t := by
  obtain ⟨σ, hσ, h⟩ := hPreal t ht
  exact ⟨⟨σ, hσ⟩, h⟩

theorem Efields {a : Perm (Fin n)} (ha : a ∈ M) {Pl Hl E : List (List ℕ)} (hPcl : TabClosed n Pl)
    (hPreal : ∀ t ∈ Pl, Real M t) (hcl : TabClosed n E)
    (hcen : ∀ x : ↥M, (⟨a, ha⟩ : ↥M) * x = x * ⟨a, ha⟩ → tbl (x : Perm (Fin n)) ∈ Hl)
    (hE : EOK n Pl E) (haE : tbl a ∈ E) (hSC : SelfCent Hl E) :
    tabSubM M E hcl ≤ tabSubM M Pl hPcl ∧ ElemAb (tabSubM M E hcl) ∧
      Nat.card (tabSubM M E hcl) = 16 ∧
      ∀ x : ↥M, (∀ e ∈ tabSubM M E hcl, x * e = e * x) → x ∈ tabSubM M E hcl := by
  obtain ⟨hnd, hlen, hsub, hcomm, hsq⟩ := hE
  have hEreal : ∀ t ∈ E, Real M t := fun t ht => hPreal t (hsub t ht)
  refine ⟨fun x hx => hsub _ hx, elemAb_tabSubM hcomm hsq,
    (card_tabSubM hnd hEreal).trans hlen, fun x hx => ?_⟩
  have hz : (⟨a, ha⟩ : ↥M) ∈ tabSubM M E hcl := haE
  have hxz := hx _ hz
  have hH := hcen x hxz.symm
  refine hSC _ hH (fun e he => ?_)
  obtain ⟨y, hy⟩ := real_of_mem hEreal he
  have hyE : y ∈ tabSubM M E hcl := by rw [mem_tabSubM, hy]; exact he
  have := hx y hyE
  have h2 := (mul_comm_iff_tbl (x : Perm (Fin n)) y).mp (congrArg Subtype.val this)
  rw [hy] at h2
  exact h2

theorem classification {Pl Ea Eb : List (List ℕ)} (hPcl : TabClosed n Pl)
    (hPreal : ∀ t ∈ Pl, Real M t) (hEacl : TabClosed n Ea) (hEbcl : TabClosed n Eb)
    (hEa : EOK n Pl Ea) (hEb : EOK n Pl Eb) (hcls : ClassOK n Pl Ea Eb) :
    ∀ E : Subgroup ↥M, E ≤ tabSubM M Pl hPcl → ElemAb E → Nat.card E = 16 →
      E = tabSubM M Ea hEacl ∨ E = tabSubM M Eb hEbcl := by
  intro E hEP hEab hE16
  obtain ⟨l, hl, hlE, hspan⟩ := exists_span 4 E hEab.1 hEab.2 (by rw [hE16]; norm_num)
  obtain ⟨x1, x2, x3, x4, rfl⟩ : ∃ x1 x2 x3 x4, l = [x1, x2, x3, x4] := by
    rcases l with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, l⟩⟩⟩⟩⟩ <;> simp at hl
    exact ⟨x1, x2, x3, x4, rfl⟩
  have h1 : x1 ∈ E := hlE x1 (by simp)
  have h2 : x2 ∈ E := hlE x2 (by simp)
  have h3 : x3 ∈ E := hlE x3 (by simp)
  have h4 : x4 ∈ E := hlE x4 (by simp)
  have hinv : ∀ x ∈ E, tbl (x : Perm (Fin n)) ∈ invsOf n Pl := by
    intro x hx
    unfold invsOf
    rw [List.mem_filter]
    refine ⟨hEP hx, ?_⟩
    simp only [decide_eq_true_eq]
    have h2 : tbl ((x : Perm (Fin n)) * (x : Perm (Fin n))) = tbl (1 : Perm (Fin n)) :=
      congrArg (fun y : ↥M => tbl (y : Perm (Fin n))) (hEab.2 x hx)
    rwa [tbl_mul, tbl_one] at h2
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, mulT (tbl (x : Perm (Fin n))) (tbl (y : Perm (Fin n))) =
      mulT (tbl (y : Perm (Fin n))) (tbl (x : Perm (Fin n))) := by
    intro x hx y hy
    exact (mul_comm_iff_tbl (x : Perm (Fin n)) y).mp (congrArg Subtype.val (hEab.1 x hx y hy))
  have key := hcls _ (hinv x1 h1) _ (hinv x2 h2) (hcomm x1 h1 x2 h2) _ (hinv x3 h3)
    (hcomm x1 h1 x3 h3) (hcomm x2 h2 x3 h3) _ (hinv x4 h4) (hcomm x1 h1 x4 h4)
    (hcomm x2 h2 x4 h4) (hcomm x3 h3 x4 h4)
  have hspan' : ∀ x ∈ E, tbl (x : Perm (Fin n)) ∈ spanT n [tbl (x1 : Perm (Fin n)),
      tbl (x2 : Perm (Fin n)), tbl (x3 : Perm (Fin n)), tbl (x4 : Perm (Fin n))] := by
    intro x hx
    have := List.mem_map_of_mem (f := fun y : ↥M => tbl (y : Perm (Fin n))) (hspan x hx)
    rw [map_tbl_spanList] at this
    exact this
  have hEareal : ∀ t ∈ Ea, Real M t := fun t ht => hPreal t (hEa.2.2.1 t ht)
  have hEbreal : ∀ t ∈ Eb, Real M t := fun t ht => hPreal t (hEb.2.2.1 t ht)
  rcases key with hlt | hA | hB
  · exfalso
    have hinj : Function.Injective (fun y : ↥M => tbl (y : Perm (Fin n))) :=
      fun x y h => Subtype.ext (tbl_injective h)
    have hsubset : (fun y : ↥M => tbl (y : Perm (Fin n))) '' (E : Set ↥M) ⊆
        ((spanT n [tbl (x1 : Perm (Fin n)), tbl (x2 : Perm (Fin n)), tbl (x3 : Perm (Fin n)),
          tbl (x4 : Perm (Fin n))]).toFinset : Set (List ℕ)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, List.mem_toFinset]
      exact hspan' x hx
    have hle := Set.ncard_le_ncard hsubset (Finset.finite_toSet _)
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, List.card_toFinset] at hle
    have : (E : Set ↥M).ncard = 16 := (Nat.card_coe_set_eq _).symm.trans hE16
    omega
  · left
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => hA _ (hspan' x hx)) ?_
    rw [card_tabSubM hEa.1 hEareal, hEa.2.1, hE16]
  · right
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => hB _ (hspan' x hx)) ?_
    rw [card_tabSubM hEb.1 hEbreal, hEb.2.1, hE16]

theorem wit_fields {a b : Perm (Fin n)} (ha : a ∈ M) (hb : b ∈ M) {D : Dat}
    (hta : tbl a = D.ta) (htb : tbl b = D.tb) {W : List ℕ} {E₁ E₂ : List (List ℕ)}
    (hcl₁ : TabClosed n E₁) (hcl₂ : TabClosed n E₂) (hreal₁ : ∀ t ∈ E₁, Real M t)
    (hwit : Wit n (wordT n D.ta D.tb W) E₁ E₂) :
    ∃ g : ↥M, g ∈ Subgroup.normalizer ((tabSubM M E₂ hcl₂ : Subgroup ↥M) : Set ↥M) ∧
      g ∉ Subgroup.normalizer ((tabSubM M E₁ hcl₁ : Subgroup ↥M) : Set ↥M) := by
  obtain ⟨σ, hσ, hσt⟩ := real_wordT (M := M) ⟨a, ha, hta⟩ ⟨b, hb, htb⟩ W
  refine ⟨⟨σ, hσ⟩, ?_, ?_⟩
  · apply mem_normalizer_of_forall
    intro e he
    rw [mem_tabSubM] at he ⊢
    have := hwit.1 _ he
    rw [← hσt] at this
    show tbl (σ * (e : Perm (Fin n)) * σ⁻¹) ∈ E₂
    rwa [tbl_conj]
  · intro hmem
    obtain ⟨t, ht, htn⟩ := hwit.2
    obtain ⟨y, hy⟩ := real_of_mem hreal₁ ht
    have hyE : y ∈ tabSubM M E₁ hcl₁ := by rw [mem_tabSubM, hy]; exact ht
    have h1 := (Subgroup.mem_normalizer_iff.mp hmem y).mp hyE
    rw [mem_tabSubM] at h1
    have h2 : tbl (σ * (y : Perm (Fin n)) * σ⁻¹) = conjT n (wordT n D.ta D.tb W) t := by
      rw [tbl_conj, hσt, hy]
    exact htn (h2 ▸ h1)


theorem twoE_of_check (M : Subgroup (Perm (Fin n))) {a b : Perm (Fin n)} (ha : a ∈ M) (hb : b ∈ M)
    (D : Dat) (hta : tbl a = D.ta) (htb : tbl b = D.tb) (hcard : Nat.card M = D.order)
    (hc : Check n D) : TwoE ↥M := by
  obtain ⟨hclnd, hHnd, hord, hHcomm, hPnd, hPlen, hodd, hPcl, hEacl, hEbcl, hEa, hEb, haEa, haEb,
    hne, hSCa, hSCb, hWa, hWb, hcls⟩ := hc
  have hRa : Real M D.ta := ⟨a, ha, hta⟩
  have hRb : Real M D.tb := ⟨b, hb, htb⟩
  have hid : ∀ g : List ℕ, g = List.range n ∨ g ∈ D.letters n → Real M g := by
    intro g hg
    rcases hg with rfl | hg
    · exact real_one
    · simp only [Dat.letters, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hRa
      · exact hRb
      · exact hRa.inv
      · exact hRb.inv
  have hHreal : ∀ t ∈ D.Hl n, Real M t := by
    refine bfs_prop (Real M) D.hPar real_one (fun x g hx hg => hx.mul ?_)
    rcases hg with rfl | hg
    · exact real_one
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
      exact real_wordT hRa hRb w
  have hPreal : ∀ t ∈ D.Pl n, Real M t := by
    refine bfs_prop (Real M) D.pPar real_one (fun x g hx hg => hx.mul ?_)
    rcases hg with rfl | hg
    · exact real_one
    · obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
      exact real_wordT hRa hRb w
  have hclreal : ∀ t ∈ D.cl n, ∃ σ ∈ M, tbl (σ * a * σ⁻¹) = t := by
    refine bfs_prop (fun t => ∃ σ ∈ M, tbl (σ * a * σ⁻¹) = t) D.clPar ⟨1, M.one_mem, by simp [hta]⟩ ?_
    intro x g hx hg
    obtain ⟨σ, hσ, rfl⟩ := hx
    obtain ⟨τ, hτ, rfl⟩ := hid g (by
      rcases hg with h | h
      · exact Or.inl h
      · exact Or.inr h)
    refine ⟨τ * σ, M.mul_mem hτ hσ, ?_⟩
    show tbl (τ * σ * a * (τ * σ)⁻¹) = conjT n (tbl τ) (tbl (σ * a * σ⁻¹))
    rw [← tbl_conj]
    exact congrArg tbl (by group)
  have hMpos : 0 < Nat.card ↥M := Nat.card_pos
  have hclpos : 0 < (D.cl n).length := by
    rcases Nat.eq_zero_or_pos (D.cl n).length with h | h
    · rw [h, zero_mul] at hord
      omega
    · exact h
  have hcen := centralizer_tables ha hclnd hHnd hclreal hHreal
    (fun h hh => by rw [hta]; exact hHcomm h hh) (hcard.trans hord.symm) hclpos
  have hEareal : ∀ t ∈ D.Ea n, Real M t := fun t ht => hPreal t (hEa.2.2.1 t ht)
  have hEbreal : ∀ t ∈ D.Eb n, Real M t := fun t ht => hPreal t (hEb.2.2.1 t ht)
  obtain ⟨hEaP, hEaab, hEa16, hEacen⟩ :=
    Efields ha hPcl hPreal hEacl hcen hEa (by rw [hta]; exact haEa) hSCa
  obtain ⟨hEbP, hEbab, hEb16, hEbcen⟩ :=
    Efields ha hPcl hPreal hEbcl hcen hEb (by rw [hta]; exact haEb) hSCb
  obtain ⟨ga, hga1, hga2⟩ := wit_fields ha hb hta htb hEacl hEbcl hEareal hWa
  obtain ⟨gb, hgb1, hgb2⟩ := wit_fields ha hb hta htb hEbcl hEacl hEbreal hWb
  refine ⟨tabSubM M (D.Pl n) hPcl, ?_, ?_, ?_⟩
  · exact IsPGroup.of_card (n := 7) (by rw [card_tabSubM hPnd hPreal, hPlen]; norm_num)
  · intro h2
    have := (tabSubM M (D.Pl n) hPcl).card_mul_index
    rw [card_tabSubM hPnd hPreal, hPlen, hcard] at this
    omega
  · refine ⟨tabSubM M (D.Ea n) hEacl, tabSubM M (D.Eb n) hEbcl, ga, gb, hEaP, hEbP, ?_, hEaab,
      hEbab, hEa16, hEb16, classification hPcl hPreal hEacl hEbcl hEa hEb hcls, hEacen, hEbcen,
      ⟨hga1, hga2⟩, ⟨hgb1, hgb2⟩⟩
    intro heq
    obtain ⟨t, ht, htn⟩ := hne
    obtain ⟨y, hy⟩ := real_of_mem hEareal ht
    have h1 : y ∈ tabSubM M (D.Ea n) hEacl := by rw [mem_tabSubM, hy]; exact ht
    rw [heq, mem_tabSubM, hy] at h1
    exact htn h1


end Sound


end M2x

end CFSG.QuasithinUnique.Unc25G2
