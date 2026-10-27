module

public import CFSG.LieType.Steinberg.CoreBasic
public import CFSG.LieType.Steinberg.PartB
public import CFSG.LieType.Steinberg.PartBRankOne
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal
open scoped commutatorElement

section Functional

variable {ι : Type*} [Fintype ι]

theorem exists_addHom_eq_zero_pos {α β : ι → ℤ} (h : LinIndepPair α β) :
    ∃ f : (ι → ℤ) →+ ℤ, f α = 0 ∧ 0 < f β := by
  obtain ⟨l, hl⟩ := exists_apply_ne_zero h.ne_zero_left
  obtain ⟨j, hj⟩ : ∃ j, α j * β l - α l * β j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 := (h (β l) (-α l) (funext fun m => ?_)).2
    · exact hl (neg_eq_zero.1 h0)
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination hc m
  refine ⟨AddMonoidHom.mk' (fun v => (α j * β l - α l * β j) * (α j * v l - α l * v j))
    fun u v => by simp only [Pi.add_apply]; ring, by simp only [AddMonoidHom.mk'_apply]; ring, ?_⟩
  simp only [AddMonoidHom.mk'_apply]
  exact mul_self_pos.2 hj

theorem exists_addHom_pos_pos {α β : ι → ℤ} (h : LinIndepPair α β) :
    ∃ f : (ι → ℤ) →+ ℤ, 0 < f α ∧ 0 < f β := by
  obtain ⟨f, hf0, hf⟩ := exists_addHom_eq_zero_pos h
  obtain ⟨g, hg0, hg⟩ := exists_addHom_eq_zero_pos (α := β) (β := α) fun a b hab =>
    (h b a (by rw [add_comm, hab])).symm
  exact ⟨f + g, by simp [hf0, hg], by simp [hg0, hf]⟩

omit [Fintype ι] in
theorem pos_apply_nsmul_add_nsmul {f : (ι → ℤ) →+ ℤ} {a b : ι → ℤ} (ha : 0 < f a)
    (hb : 0 < f b) {m n : ℕ} (hmn : 0 < m + n) : 0 < f (m • a + n • b) := by
  rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have : (0 : ℤ) < n := by omega
    simp only [Nat.cast_zero, zero_mul, zero_add]
    positivity
  · have : (0 : ℤ) < m := by exact_mod_cast hm
    have : (0 : ℤ) ≤ n := by exact_mod_cast Nat.zero_le n
    nlinarith

@[expose] def htHom : (ι → ℤ) →+ ℤ :=
  AddMonoidHom.mk' ht fun u v => by simp [ht, Finset.sum_add_distrib]

theorem htHom_apply (v : ι → ℤ) : htHom v = ht v := rfl

theorem RootSystem.exists_addHom_pos [DecidableEq ι] (Φ : RootSystem ι) {γ : ι → ℤ}
    (hγ : γ ∈ Φ.roots) : ∃ f : (ι → ℤ) →+ ℤ, 0 < f γ := by
  rcases Φ.mem_pos_or_mem_neg hγ with h | h
  · exact ⟨htHom, h.2⟩
  · exact ⟨-htHom, by simpa [htHom_apply] using h.2⟩

end Functional

section Reduced

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem two_smul_notMem_roots {Dv : Set I} (hDv : Dv = ∅) {γ : I → ℤ} (hγ : γ ∈ roots hA Dv) :
    2 • γ ∉ roots hA Dv := by
  subst hDv
  have h0 := ne_zero_of_mem_roots hA ∅ hγ
  rintro (⟨w', j, h2⟩ | ⟨_, _, hj, _⟩)
  · rcases hγ with ⟨w, i, rfl⟩ | ⟨_, _, hi, _⟩
    · apply h0
      funext l
      have h3 := congrFun h2 l
      rcases OfCartan.eq_or_eq_neg_of_smul_eq_smul hA w w' i j (p := 2) (q := 1) one_ne_zero
          (by rw [one_smul, ← h2, two_zsmul, two_nsmul]) with h | h <;>
        have h4 := congrFun h l <;>
        simp only [Pi.smul_apply, nsmul_eq_mul, Pi.neg_apply, Nat.cast_ofNat] at h3 h4 <;>
        simp only [Pi.zero_apply] <;> omega
    · exact hi.elim
  · exact hj.elim

theorem eq_or_eq_neg_of_not_linIndepPair {Dv : Set I} (hDv : Dv = ∅) {γ δ : I → ℤ}
    (hγ : γ ∈ roots hA Dv) (hδ : δ ∈ roots hA Dv) (h : ¬ LinIndepPair γ δ) :
    δ = γ ∨ δ = -γ := by
  have hneg := (RootSystem.ofCartan hA Dv).neg_mem
  rcases (RootSystem.ofCartan hA Dv).proportional γ hγ δ hδ h with e | e | e | e | e | e
  · exact Or.inl e.symm
  · exact Or.inr (by rw [e, neg_neg])
  · exact absurd (e ▸ hγ) (two_smul_notMem_roots hA hDv hδ)
  · refine absurd ?_ (two_smul_notMem_roots hA hDv hδ)
    rw [← neg_neg (2 • δ), ← e]
    exact hneg γ hγ
  · exact absurd (e ▸ hδ) (two_smul_notMem_roots hA hDv hγ)
  · refine absurd ?_ (two_smul_notMem_roots hA hDv hγ)
    rw [← neg_neg (2 • γ), ← e]
    exact hneg δ hδ

theorem exists_addHom_pos_of_not_isNegMultiple {Dv : Set I} (hDv : Dv = ∅) {α β : I → ℤ}
    (hα : α ∈ roots hA Dv) (hβ : β ∈ roots hA Dv) (h : ¬ IsNegMultiple α β) :
    ∃ f : (I → ℤ) →+ ℤ, 0 < f α ∧ 0 < f β := by
  by_cases hli : LinIndepPair α β
  · exact exists_addHom_pos_pos hli
  rcases eq_or_eq_neg_of_not_linIndepPair hA hDv hα hβ hli with rfl | rfl
  · obtain ⟨f, hf⟩ := (RootSystem.ofCartan hA Dv).exists_addHom_pos hα
    exact ⟨f, hf, hf⟩
  · exact absurd ⟨-1, by norm_num, fun j => by simp⟩ h

theorem not_isNegMultiple_of_add_ne_zero {Dv : Set I} (hDv : Dv = ∅) {α β : I → ℤ}
    (hα : α ∈ roots hA Dv) (hβ : β ∈ roots hA Dv) (h : α + β ≠ 0) : ¬ IsNegMultiple α β := by
  intro hn
  have hli : ¬ LinIndepPair α β := fun hli => hli.not_isNegMultiple hn
  rcases eq_or_eq_neg_of_not_linIndepPair hA hDv hα hβ hli with rfl | rfl
  · exact not_isNegMultiple_self (ne_zero_of_mem_roots hA Dv hα) hn
  · exact h (add_neg_cancel α)

end Reduced

section ChevSub

variable {ι : Type*} {k : Type*} {G : Type*} [Group G]

@[expose] def chevRoot (xh : (ι → ℤ) → k → G) (γ : ι → ℤ) : Subgroup G :=
  Subgroup.closure (Set.range (xh γ))

@[expose] def chevSub (xh : (ι → ℤ) → k → G) (S : Set (ι → ℤ)) : Subgroup G :=
  ⨆ γ ∈ S, chevRoot xh γ

@[expose] def posSet (R : Set (ι → ℤ)) (f : (ι → ℤ) →+ ℤ) : Set (ι → ℤ) := {γ | γ ∈ R ∧ 0 < f γ}

omit [Group G] in
theorem mem_posSet {R : Set (ι → ℤ)} {f : (ι → ℤ) →+ ℤ} {γ : ι → ℤ} :
    γ ∈ posSet R f ↔ γ ∈ R ∧ 0 < f γ :=
  Iff.rfl

variable {xh : (ι → ℤ) → k → G}

theorem xh_mem_chevRoot (γ : ι → ℤ) (c : k) : xh γ c ∈ chevRoot xh γ :=
  Subgroup.subset_closure ⟨c, rfl⟩

theorem chevRoot_le_chevSub {S : Set (ι → ℤ)} {γ : ι → ℤ} (h : γ ∈ S) :
    chevRoot xh γ ≤ chevSub xh S :=
  le_iSup₂ (f := fun γ _ => chevRoot xh γ) γ h

theorem xh_mem_chevSub {S : Set (ι → ℤ)} {γ : ι → ℤ} (h : γ ∈ S) (c : k) : xh γ c ∈ chevSub xh S :=
  chevRoot_le_chevSub h (xh_mem_chevRoot γ c)

theorem chevSub_mono {S S' : Set (ι → ℤ)} (h : S ⊆ S') : chevSub xh S ≤ chevSub xh S' :=
  biSup_mono fun _ hγ => h hγ

end ChevSub

theorem conj_eq_commutatorElement_mul {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅a, b⁆ * b := by
  rw [commutatorElement_def]
  group

section ChevRels

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {G : Type*} [Group G]

structure ChevRels (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ)
    (xh : (ι → ℤ) → k → G) : Prop where
  add : ∀ γ ∈ Φ.roots, ∀ c d, xh γ (c + d) = xh γ c * xh γ d
  comm : CommutatorFormula xh O C

namespace ChevRels

variable {xh : (ι → ℤ) → k → G} {O : CommOrder Φ} {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
  (hR : ChevRels O C xh)
include hR

theorem xh_zero {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) : xh γ 0 = 1 := by
  have h := hR.add γ hγ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xh_neg {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) (c : k) : xh γ (-c) = (xh γ c)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hR.add γ hγ, neg_add_cancel, hR.xh_zero hγ])

theorem mem_chevRoot_iff {γ : ι → ℤ} (hγ : γ ∈ Φ.roots) {g : G} :
    g ∈ chevRoot xh γ ↔ ∃ c, xh γ c = g := by
  refine ⟨fun hg => ?_, fun ⟨c, hc⟩ => hc ▸ xh_mem_chevRoot γ c⟩
  induction hg using Subgroup.closure_induction with
  | mem _ h => exact h
  | one => exact ⟨0, hR.xh_zero hγ⟩
  | mul _ _ _ _ h1 h2 =>
    obtain ⟨c, rfl⟩ := h1
    obtain ⟨d, rfl⟩ := h2
    exact ⟨c + d, hR.add γ hγ c d⟩
  | inv _ _ h =>
    obtain ⟨c, rfl⟩ := h
    exact ⟨-c, hR.xh_neg hγ c⟩

theorem commutator_mem {γ δ : ι → ℤ} (hγ : γ ∈ Φ.roots) (hδ : δ ∈ Φ.roots) (hγδ : γ + δ ≠ 0)
    (c d : k) {T : Subgroup G}
    (hT : ∀ p ∈ expPairs Φ γ δ, ∀ e, xh (p.1 • γ + p.2 • δ) e ∈ T) : ⁅xh γ c, xh δ d⁆ ∈ T := by
  rw [hR.comm γ hγ δ hδ hγδ c d]
  refine Subgroup.list_prod_mem _ fun z hz => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
  exact hT p ((O.mem_iff γ hγ δ hδ hγδ p).1 hp) _

theorem chevRoot_le_normalizer (f : (ι → ℤ) →+ ℤ) {γ : ι → ℤ} (hγ : γ ∈ Φ.roots)
    (hf : 0 ≤ f γ) :
    chevRoot xh γ ≤ Subgroup.normalizer (chevSub xh (posSet Φ.roots f) : Set G) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  obtain ⟨c, rfl⟩ := (hR.mem_chevRoot_iff hγ).1 hg
  simp only [chevSub, Subgroup.map_iSup]
  refine iSup₂_le fun δ hδ => ?_
  rw [chevRoot, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
  change xh γ c * xh δ d * (xh γ c)⁻¹ ∈ _
  have hγδ : γ + δ ≠ 0 := fun h => by
    have := congrArg f h
    rw [map_add, _root_.map_zero] at this
    linarith [hδ.2]
  rw [conj_eq_commutatorElement_mul]
  refine mul_mem (hR.commutator_mem hγ hδ.1 hγδ c d fun p hp e =>
    xh_mem_chevSub (S := posSet Φ.roots f) (mem_posSet.2 ⟨hp.2.2, ?_⟩) e) (xh_mem_chevSub hδ d)
  rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have h1 : (0 : ℤ) < p.2 := by exact_mod_cast hp.2.1
  nlinarith [hδ.2]

end ChevRels

end ChevRels

section Lemma36

theorem exists_sorted_list {V : Type*} {S : Set V} (hS : S.Finite) (f : V → ℤ) :
    ∃ L : List V, L.Nodup ∧ (∀ v, v ∈ L ↔ v ∈ S) ∧ L.Pairwise (fun a b => f a ≤ f b) := by
  classical
  refine ⟨hS.toFinset.toList.mergeSort (fun a b => decide (f a ≤ f b)),
    List.nodup_mergeSort.2 (Finset.nodup_toList _), fun v => by simp, ?_⟩
  refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp
    (fun h => by simpa using h)
  · simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total _ _

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
  {G : Type*} [Group G] {xh : (Fin D.rank → ℤ) → k → G} {π : G →* K}

theorem ChevalleyExtras.x_zero (hE : ChevalleyExtras D k x C O) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) : x γ 0 = 1 := by
  have h := (hE.param γ hγ).2.1 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem eq_one_of_mem_chevRoot (hE : ChevalleyExtras D k x C O) (hR : ChevRels O C xh)
    (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    {g : G} (hg : g ∈ chevRoot xh γ) (h1 : π g = 1) : g = 1 := by
  obtain ⟨c, rfl⟩ := (hR.mem_chevRoot_iff hγ).1 hg
  rw [hπ γ hγ] at h1
  rw [(hE.param γ hγ).2.2 (h1.trans (hE.x_zero hγ).symm), hR.xh_zero hγ]

theorem eq_one_of_mem_chevSub_posSet (hE : ChevalleyExtras D k x C O) (hR : ChevRels O C xh)
    (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (f : (Fin D.rank → ℤ) →+ ℤ) {g : G}
    (hg : g ∈ chevSub xh (posSet D.roots f)) (h1 : π g = 1) : g = 1 := by
  obtain ⟨L, hnd, hmem, hs⟩ := exists_sorted_list (S := posSet D.roots f)
    ((RootSystem.ofCartan D.isFiniteType D.divisible).finite_roots.subset fun _ h => h.1) f
  have hsub : chevSub xh (posSet D.roots f) = ⨆ v ∈ L, chevRoot xh v := by
    simp only [chevSub, ← hmem]
  rw [hsub] at hg
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a ≠ b → ∀ y ∈ chevRoot xh a, ∀ z ∈ chevRoot xh b,
      ⁅y, z⁆ ∈ ⨆ c ∈ L, ⨆ (_ : min (f a) (f b) < f c), chevRoot xh c := by
    intro a ha b hb _ y hy z hz
    obtain ⟨ha1, ha2⟩ := (hmem a).1 ha
    obtain ⟨hb1, hb2⟩ := (hmem b).1 hb
    obtain ⟨c, rfl⟩ := (hR.mem_chevRoot_iff ha1).1 hy
    obtain ⟨d, rfl⟩ := (hR.mem_chevRoot_iff hb1).1 hz
    have hab : a + b ≠ 0 := fun h => by
      have := congrArg f h
      rw [map_add, map_zero] at this
      linarith
    refine hR.commutator_mem ha1 hb1 hab c d fun p hp e => ?_
    have hf : min (f a) (f b) < f (p.1 • a + p.2 • b) := by
      rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
      have h1 : (1 : ℤ) ≤ p.1 := by exact_mod_cast hp.1
      have h2 : (1 : ℤ) ≤ p.2 := by exact_mod_cast hp.2.1
      have := min_le_left (f a) (f b)
      nlinarith
    have hL : p.1 • a + p.2 • b ∈ L := (hmem _).2 ⟨hp.2.2, (min_lt_iff.1 hf).elim
      (fun h => ha2.trans h) (fun h => hb2.trans h)⟩
    exact Subgroup.mem_iSup_of_mem _ (Subgroup.mem_iSup_of_mem hL
      (Subgroup.mem_iSup_of_mem hf (xh_mem_chevRoot _ e)))
  obtain ⟨F, hF, rfl⟩ := exists_prod_eq_of_commutator_mem (chevRoot xh) f hnd hs hcomm g hg
  have hroot : ∀ v ∈ L, v ∈ D.roots := fun v hv => ((hmem v).1 hv).1
  have hFK : ∀ v ∈ L, π (F v) ∈ D.rootGroup v := fun v hv => by
    obtain ⟨c, hc⟩ := (hR.mem_chevRoot_iff (hroot v hv)).1 (hF v hv)
    rw [← hc, hπ v (hroot v hv)]
    exact ((hE.param v (hroot v hv)).1 _).2 ⟨c, rfl⟩
  have hprod : (L.map fun v => π (F v)).prod = (L.map fun _ => (1 : K)).prod := by
    have e : (L.map fun v => π (F v)) = (L.map F).map π := by
      rw [List.map_map]
      rfl
    rw [e, ← map_list_prod, h1]
    simp
  have hK := hE.prodInjective f L hnd (fun v hv => (hmem v).1 hv) hs (fun v => π (F v))
    (fun _ => 1) hFK (fun _ _ => one_mem _) hprod
  rw [List.map_congr_left fun v hv =>
    eq_one_of_mem_chevRoot hE hR hπ (hroot v hv) (hF v hv) (hK v hv)]
  simp

theorem injOn_chevSub_posSet (hE : ChevalleyExtras D k x C O) (hR : ChevRels O C xh)
    (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (f : (Fin D.rank → ℤ) →+ ℤ) :
    Set.InjOn π (chevSub xh (posSet D.roots f)) :=
  injOn_of_eq_one fun _ hg h1 => eq_one_of_mem_chevSub_posSet hE hR hπ f hg h1

theorem injOn_chevSub_cone (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hR : ChevRels O C xh) (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c)
    {α β : Fin D.rank → ℤ} (hα : α ∈ D.roots) (hβ : β ∈ D.roots) (h : ¬ IsNegMultiple α β) :
    Set.InjOn π (chevSub xh (cone D.roots α β)) := by
  obtain ⟨f, hfα, hfβ⟩ := exists_addHom_pos_of_not_isNegMultiple D.isFiniteType hD hα hβ h
  refine (injOn_chevSub_posSet hE hR hπ f).mono
    (chevSub_mono (S' := posSet D.roots f) fun γ hγ => mem_posSet.2 ⟨hγ.1, ?_⟩)
  obtain ⟨hγ, a, b, rfl⟩ := hγ
  refine pos_apply_nsmul_add_nsmul hfα hfβ (Nat.pos_of_ne_zero fun h => ?_)
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
  exact CFSG.LieType.RootSystem.ne_zero_of_mem_roots D.isFiniteType D.divisible hγ (by simp)

end Lemma36

section Pairs

open CFSG.LieType.RootSystem

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

omit [Fintype I] [DecidableEq I] in
theorem LinIndepPair.eq_of_smul_add_smul_eq {δ γ : I → ℤ} (hli : LinIndepPair δ γ)
    {m n m' n' : ℕ} (h : m • δ + n • γ = m' • δ + n' • γ) : m = m' ∧ n = n' := by
  have := hli ((m : ℤ) - m') ((n : ℤ) - n') (funext fun l => by
    have hl := congrFun h l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hl ⊢
    simp only [nsmul_eq_mul, smul_eq_mul] at hl ⊢
    linear_combination hl)
  omega

omit [Fintype I] [DecidableEq I] in
theorem LinIndepPair.smul_add_smul_ne_neg {δ γ : I → ℤ} (hli : LinIndepPair δ γ) {m n m' n' : ℕ}
    (h0 : 0 < m') (h : m • δ + n • γ = -(m' • δ + n' • γ)) : False := by
  have := hli ((m : ℤ) + m') ((n : ℤ) + n') (funext fun l => by
    have hl := congrFun h l
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply] at hl ⊢
    simp only [nsmul_eq_mul, smul_eq_mul] at hl ⊢
    linear_combination hl)
  omega

theorem linIndepPair_of_add_smul_mem {Dv : Set I} (hDv : Dv = ∅) {δ γ : I → ℤ}
    (hδ : δ ∈ roots hA Dv) (hγ : γ ∈ roots hA Dv) (hδγ : δ + γ ≠ 0) {j : ℕ} (hj : 0 < j)
    (hα : δ + j • γ ∈ roots hA Dv) : LinIndepPair δ γ := by
  by_contra hli
  rcases eq_or_eq_neg_of_not_linIndepPair hA hDv hδ hγ hli with h | h
  · rw [h] at hα
    obtain ⟨l, hl⟩ := exists_apply_ne_zero (ne_zero_of_mem_roots hA Dv hδ)
    have hli2 : ¬ LinIndepPair δ (δ + j • δ) := fun h2 => by
      have := (h2 ((1 + j : ℕ) : ℤ) (-1) (funext fun l => by simp; ring)).1
      omega
    have hj' : (0 : ℤ) < j := by exact_mod_cast hj
    rcases eq_or_eq_neg_of_not_linIndepPair hA hDv hδ hα hli2 with h' | h' <;>
      have h'' := congrFun h' l <;>
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply] at h'' <;>
      simp only [nsmul_eq_mul] at h''
    · exact mul_ne_zero hj'.ne' hl (by linarith)
    · exact mul_ne_zero (by positivity : (j : ℤ) + 2 ≠ 0) hl (by linarith)
  · exact hδγ (by rw [h, add_neg_cancel])

end Pairs

section Lemma37

@[expose] def chevWeyl {ι k G : Type*} [DecidableEq ι] [Field k] [Group G]
    (xh : (ι → ℤ) → k → G) (i : ι) (t : k) : G :=
  xh (Pi.single i 1) t * xh (-Pi.single i 1) (-t⁻¹) * xh (Pi.single i 1) t

theorem weylElement_eq_chevWeyl {k G : Type*} [Field k] [Group G] {r : ℕ}
    (xh : (Fin r → ℤ) → k → G) (i : Fin r) (t : kˣ) : weylElement xh i t = chevWeyl xh i t := by
  simp [weylElement, chevWeyl]

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K} {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
  {G : Type*} [Group G] {xh : (Fin D.rank → ℤ) → k → G} {π : G →* K}

local notation "ΦD" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem map_chevWeyl (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (i : Fin D.rank) (t : k) :
    π (chevWeyl xh i t) = chevWeyl x i t := by
  simp only [chevWeyl, map_mul, hπ _ ((ΦD).single_mem i),
    hπ _ ((ΦD).neg_mem _ ((ΦD).single_mem i))]

theorem ChevalleyExtras.chevWeyl_conj_single (hE : ChevalleyExtras D k x C O) (i : Fin D.rank)
    {t : k} (ht : t ≠ 0) (u : k) :
    chevWeyl x i t * x (Pi.single i 1) u * (chevWeyl x i t)⁻¹ =
      x (-Pi.single i 1) (-(t ^ 2)⁻¹ * u) := by
  obtain ⟨φ, -, hU, hL⟩ := hE.rankOne i
  have hW : sl2Upper t * sl2Lower (-t⁻¹) * sl2Upper t * sl2Upper u =
      sl2Lower (-(t ^ 2)⁻¹ * u) * (sl2Upper t * sl2Lower (-t⁻¹) * sl2Upper t) := by
    ext a b
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
    fin_cases a <;> fin_cases b <;> simp <;> field_simp <;> first | ring1 | simp
  rw [mul_inv_eq_iff_eq_mul, chevWeyl]
  simp only [← hU, ← hL, ← map_mul, hW]

theorem exists_chevWeyl_conj (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hR : ChevRels O C xh) (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (i : Fin D.rank)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (h1 : β ≠ Pi.single i 1) (h2 : β ≠ -Pi.single i 1)
    {t : k} (ht : t ≠ 0) (u : k) :
    ∃ c, chevWeyl xh i t * xh β u * (chevWeyl xh i t)⁻¹ = xh ((ΦD).refl i β) c := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).single_mem i
  have hα' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).neg_mem _ hα
  have hli : LinIndepPair (Pi.single i 1) β := by
    by_contra hli
    rcases eq_or_eq_neg_of_not_linIndepPair D.isFiniteType hD hα hβ hli with h | h
    exacts [h1 h, h2 h]
  obtain ⟨f, hf0, hfβ⟩ := exists_addHom_eq_zero_pos hli
  have hfr : 0 < f ((ΦD).refl i β) := by
    have hrefl : (ΦD).refl i β = β - (∑ j, D.cartan i j * β j) • Pi.single i 1 :=
      CFSG.LieType.RootSystem.reflection_apply _ _ _
    rw [hrefl, map_sub, map_zsmul, hf0, smul_zero, sub_zero]
    exact hfβ
  have hrβ : (ΦD).refl i β ∈ D.roots := (ΦD).refl_mem i β hβ
  have hN : ∀ {γ}, γ ∈ D.roots → f γ = 0 → ∀ c,
      xh γ c ∈ Subgroup.normalizer (chevSub xh (posSet D.roots f) : Set G) :=
    fun hγ hfγ c => hR.chevRoot_le_normalizer f hγ hfγ.ge (xh_mem_chevRoot _ c)
  have hfα' : f (-Pi.single i 1) = 0 := by rw [map_neg, hf0, neg_zero]
  have hw : chevWeyl xh i t ∈ Subgroup.normalizer (chevSub xh (posSet D.roots f) : Set G) :=
    mul_mem (mul_mem (hN hα hf0 t) (hN hα' hfα' _)) (hN hα hf0 t)
  obtain ⟨ε, -, hε⟩ := hE.weyl i β hβ
  refine ⟨(ε : k) * ((Units.mk0 t ht ^ (-(∑ j, D.cartan i j * β j)) : kˣ) : k) * u, ?_⟩
  apply injOn_chevSub_posSet hE hR hπ f
  · exact (Subgroup.mem_normalizer_iff.1 hw _).1 (xh_mem_chevSub (mem_posSet.2 ⟨hβ, hfβ⟩) u)
  · exact xh_mem_chevSub (mem_posSet.2 ⟨hrβ, hfr⟩) _
  · have h := hε (Units.mk0 t ht) u
    rw [weylElement_eq_chevWeyl, Units.val_mk0] at h
    rw [map_mul, map_mul, map_inv, map_chevWeyl hπ, hπ β hβ, hπ _ hrβ]
    exact h

theorem chevWeyl_conj_mem_chevSub (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hR : ChevRels O C xh) (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (i : Fin D.rank)
    {β : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (h1 : β ≠ Pi.single i 1) (h2 : β ≠ -Pi.single i 1)
    {t : k} (ht : t ≠ 0) (c : k) {f : (Fin D.rank → ℤ) →+ ℤ} (hf : 0 < f ((ΦD).refl i β)) :
    chevWeyl xh i t * xh β c * (chevWeyl xh i t)⁻¹ ∈ chevSub xh (posSet D.roots f) := by
  obtain ⟨c', hc'⟩ := exists_chevWeyl_conj hD hE hR hπ i hβ h1 h2 ht c
  rw [hc']
  exact xh_mem_chevSub (mem_posSet.2 ⟨(ΦD).refl_mem i _ hβ, hf⟩) c'

theorem chevWeyl_conj_single (hD : D.divisible = ∅) (hE : ChevalleyExtras D k x C O)
    (hR : ChevRels O C xh) (hπ : ∀ γ ∈ D.roots, ∀ c, π (xh γ c) = x γ c) (i : Fin D.rank)
    {t : k} (ht : t ≠ 0) (u : k) :
    chevWeyl xh i t * xh (Pi.single i 1) u * (chevWeyl xh i t)⁻¹ =
      xh (-Pi.single i 1) (-(t ^ 2)⁻¹ * u) := by
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).single_mem i
  have hα' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := (ΦD).neg_mem _ hα
  obtain ⟨δ, hδ, γ, hγ, hδγ, j, hj, hαeq, hunit⟩ := hE.rankTwo i
  have hj0 : 0 < j := by rcases hj with rfl | rfl <;> norm_num
  have hli : LinIndepPair δ γ :=
    linIndepPair_of_add_smul_mem D.isFiniteType hD hδ hγ hδγ hj0 (hαeq ▸ hα)
  have hli' : LinIndepPair ((ΦD).refl i δ) ((ΦD).refl i γ) := fun a b hab => hli a b (by
    rw [← (ΦD).refl_refl i (a • δ + b • γ), map_add, map_zsmul, map_zsmul, hab, map_zero])
  obtain ⟨f, hfδ, hfγ⟩ := exists_addHom_pos_pos hli'
  set M := chevSub xh (posSet D.roots f)
  set w := chevWeyl xh i t with hwdef
  set M' := M.comap (MulAut.conj w).toMonoidHom
  have hM' : ∀ {z}, z ∈ M' ↔ w * z * w⁻¹ ∈ M := Iff.rfl
  have hfac : ∀ m n : ℕ, (m, n) ≠ (1, j) → 0 < m + n → m • δ + n • γ ∈ D.roots → ∀ c,
      xh (m • δ + n • γ) c ∈ M' := by
    intro m n hmn hpos hroot c
    have hne1 : m • δ + n • γ ≠ Pi.single i 1 := fun h => hmn (by
      obtain ⟨h1, h2⟩ := hli.eq_of_smul_add_smul_eq (m := m) (n := n) (m' := 1) (n' := j)
        (by rw [one_smul, h, hαeq])
      rw [h1, h2])
    have hne2 : m • δ + n • γ ≠ -Pi.single i 1 := fun h =>
      hli.smul_add_smul_ne_neg (m := m) (n := n) (m' := 1) (n' := j) one_pos
        (by rw [one_smul, h, hαeq])
    rw [hM']
    refine chevWeyl_conj_mem_chevSub hD hE hR hπ i hroot hne1 hne2 ht c ?_
    rw [map_add, map_nsmul, map_nsmul]
    exact pos_apply_nsmul_add_nsmul hfδ hfγ hpos
  have hδM : ∀ c, xh δ c ∈ M' := fun c => by
    simpa using hfac 1 0 (by simp; omega) one_pos (by simpa using hδ) c
  have hγM : ∀ c, xh γ c ∈ M' := fun c => by
    simpa using hfac 0 1 (by simp) one_pos (by simpa using hγ) c
  have hc₀ : (C δ γ (1, j) : k) ≠ 0 := hunit.ne_zero
  have hmem : (1, j) ∈ O.list δ γ :=
    (O.mem_iff δ hδ γ hγ hδγ (1, j)).2 ⟨one_pos, hj0, by rw [one_smul, ← hαeq]; exact hα⟩
  obtain ⟨P₁, P₂, hsplit⟩ := List.mem_iff_append.1 hmem
  have hnd := O.nodup δ γ
  rw [hsplit, List.nodup_middle, List.nodup_cons] at hnd
  have hcomm := hR.comm δ hδ γ hγ hδγ ((C δ γ (1, j) : k)⁻¹ * u) 1
  rw [hsplit, List.map_append, List.map_cons, List.prod_append, List.prod_cons] at hcomm
  set F : ℕ × ℕ → G := fun p =>
    xh (p.1 • δ + p.2 • γ) ((C δ γ p : k) * ((C δ γ (1, j) : k)⁻¹ * u) ^ p.1 * 1 ^ p.2)
  have hF : xh ((1, j).1 • δ + (1, j).2 • γ)
      ((C δ γ (1, j) : k) * ((C δ γ (1, j) : k)⁻¹ * u) ^ (1, j).1 * 1 ^ (1, j).2) =
      xh (Pi.single i 1) u := by
    simp only [one_smul, ← hαeq, pow_one, one_pow, mul_one]
    congr 1
    field_simp
  rw [hF] at hcomm
  have hPM : ∀ P : List (ℕ × ℕ), (∀ p ∈ P, p ∈ O.list δ γ ∧ p ≠ (1, j)) →
      (P.map F).prod ∈ M' := fun P hP => Subgroup.list_prod_mem _ fun z hz => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    obtain ⟨hpO, hpne⟩ := hP p hp
    obtain ⟨hp1, hp2, hproot⟩ := (O.mem_iff δ hδ γ hγ hδγ p).1 hpO
    exact hfac p.1 p.2 hpne (by omega) hproot _
  have hP₁ := hPM P₁ fun p hp =>
    ⟨by rw [hsplit]; simp [hp], fun h => hnd.1 (by simp [← h, hp])⟩
  have hP₂ := hPM P₂ fun p hp =>
    ⟨by rw [hsplit]; simp [hp], fun h => hnd.1 (by simp [← h, hp])⟩
  have hx : xh (Pi.single i 1) u = (P₁.map F).prod⁻¹ *
      ⁅xh δ ((C δ γ (1, j) : k)⁻¹ * u), xh γ 1⁆ * (P₂.map F).prod⁻¹ := by
    rw [hcomm]
    group
  have hxM : xh (Pi.single i 1) u ∈ M' := by
    rw [hx, commutatorElement_def]
    exact mul_mem (mul_mem (inv_mem hP₁) (mul_mem (mul_mem (mul_mem (hδM _) (hγM _))
      (inv_mem (hδM _))) (inv_mem (hγM _)))) (inv_mem hP₂)
  have hfα : 0 < f (-Pi.single i 1) := by
    rw [← (ΦD).refl_single i, hαeq, map_add, map_nsmul, map_add, map_nsmul, nsmul_eq_mul]
    have : (0 : ℤ) < j := by exact_mod_cast hj0
    positivity
  apply injOn_chevSub_posSet hE hR hπ f (hM'.1 hxM) (xh_mem_chevSub (mem_posSet.2 ⟨hα', hfα⟩) _)
  rw [map_mul, map_mul, map_inv, hwdef, map_chevWeyl hπ, hπ _ hα, hπ _ hα']
  exact hE.chevWeyl_conj_single i ht u

end Lemma37

end CFSG.LieType.Steinberg
