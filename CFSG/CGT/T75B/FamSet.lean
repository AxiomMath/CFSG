module

public import CFSG.CGT.Timmesfeld75.Sec3Results

public section

namespace CFSG.CGT.T75B

open CFSG.Open CFSG.CGT.Timmesfeld75

section Basic

variable {G : Type} [Group G]

@[expose] def famFS (S : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  ⨅ M ∈ S, normIn A M

theorem mem_famFS {S : Set (Subgroup G)} {A : Subgroup G} {u : G} :
    u ∈ famFS S A ↔ ∀ M ∈ S, u ∈ A ∧ u ∈ Subgroup.normalizer (M : Set G) := by
  simp only [famFS, Subgroup.mem_iInf, mem_normIn]

theorem mem_famFS_iff {S : Set (Subgroup G)} (hS : S.Nonempty) {A : Subgroup G} {u : G} :
    u ∈ famFS S A ↔ u ∈ A ∧ ∀ M ∈ S, u ∈ Subgroup.normalizer (M : Set G) := by
  rw [mem_famFS]
  constructor
  · intro h
    obtain ⟨M₀, hM₀⟩ := hS
    exact ⟨(h M₀ hM₀).1, fun M hM => (h M hM).2⟩
  · rintro ⟨hA, hM⟩ M hMS
    exact ⟨hA, hM M hMS⟩

theorem famFS_le {S : Set (Subgroup G)} {A : Subgroup G} (hA : A ∈ S) : famFS S A ≤ A :=
  fun _ hu => (mem_famFS.1 hu A hA).1

theorem mem_normalizer_of_mem_famFS {S : Set (Subgroup G)} {A M : Subgroup G} {u : G}
    (hu : u ∈ famFS S A) (hM : M ∈ S) : u ∈ Subgroup.normalizer (M : Set G) :=
  (mem_famFS.1 hu M hM).2

end Basic

section Fin

variable {G : Type} [Group G] [Finite G]

theorem exists_fin_family (S : Set (Subgroup G)) :
    ∃ (r : ℕ) (Ts : Fin r → Subgroup G), Function.Injective Ts ∧ Set.range Ts = S := by
  classical
  have hfinS : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfin : S.Finite := Set.toFinite S
  let e := hfin.toFinset.equivFin
  refine ⟨hfin.toFinset.card, fun i => ((e.symm i : ↥hfin.toFinset) : Subgroup G), ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · ext M
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (e.symm i).2
    · intro hM
      exact ⟨e ⟨M, hfin.mem_toFinset.2 hM⟩, by simp⟩

omit [Finite G] in
theorem famF_eq_famFS {r : ℕ} {Ts : Fin r → Subgroup G} {S : Set (Subgroup G)}
    (hS : Set.range Ts = S) (j : Fin r) : (⨅ i, normIn (Ts j) (Ts i)) = famFS S (Ts j) := by
  rw [famFS, ← hS, iInf_range]

theorem cfg313_of_set [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {T : Subgroup G}
    (hT : IsWC T) (hglob : Sec3Global T) (hiso : Sec3IsoGlobal T) (h16 : Nat.card T ≠ 16)
    {S : Set (Subgroup G)} (hTS : T ∈ S) (hconj : ∀ M ∈ S, ∃ g : G, M = conjSubgroup g T)
    (hne : ∀ A ∈ S, famFS S A ≠ ⊥) :
    IsElemAbelian 2 (⨆ A ∈ S, famFS S A) ∧
      ∀ z ∈ (⨆ M ∈ S, M), conjSubgroup z (⨆ A ∈ S, famFS S A) = ⨆ A ∈ S, famFS S A := by
  obtain ⟨r, Ts, hinj, hrange⟩ := exists_fin_family S
  subst hrange
  obtain ⟨i₀, hi₀⟩ : T ∈ Set.range Ts := hTS
  have hr : 0 < r := Nat.pos_of_ne_zero fun h => by subst h; exact i₀.elim0
  have hTsS : ∀ i, Ts i ∈ Set.range Ts := fun i => Set.mem_range_self i
  have hsup : (⨆ A ∈ Set.range Ts, famFS (Set.range Ts) A) = ⨆ j, ⨅ i, normIn (Ts j) (Ts i) := by
    rw [iSup_range]
    exact iSup_congr fun j => (famF_eq_famFS rfl j).symm
  have hsupR : (⨆ M ∈ Set.range Ts, M) = ⨆ i, Ts i := by rw [iSup_range]
  obtain ⟨hQ, hQn, -⟩ := lemma313 G hnab T hT hglob hiso h16 r Ts hr hinj
    (fun i => hconj _ (hTsS i)) ⟨i₀, hi₀⟩
    (fun j => by rw [famF_eq_famFS rfl j]; exact hne _ (hTsS j))
  rw [hsup, hsupR]
  exact ⟨hQ, hQn⟩

end Fin

end CFSG.CGT.T75B
