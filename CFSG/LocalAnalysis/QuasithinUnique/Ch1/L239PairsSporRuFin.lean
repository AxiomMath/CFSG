module

public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Certificate4095
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs

open Equiv

section Generic

variable {G : Type*} [Group G]

theorem closure_subset_of_closed (gens L : List G) (h1 : (1 : G) ∈ L)
    (hg : ∀ g ∈ gens, ∀ x ∈ L, g * x ∈ L ∧ g⁻¹ * x ∈ L) :
    ∀ x ∈ Subgroup.closure {g | g ∈ gens}, x ∈ L := by
  have key : ∀ x ∈ Subgroup.closure {g | g ∈ gens}, ∀ y ∈ L, x * y ∈ L ∧ x⁻¹ * y ∈ L := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem g hg' => exact fun y hy => hg g hg' y hy
    | one => intro y hy; simpa using hy
    | mul a b _ _ ha hb =>
      intro y hy
      refine ⟨?_, ?_⟩
      · have := (ha _ (hb y hy).1).1
        simpa [mul_assoc] using this
      · have := (hb _ (ha y hy).2).2
        simpa [mul_assoc] using this
    | inv a _ ha =>
      intro y hy
      exact ⟨by simpa using (ha y hy).2, by simpa using (ha y hy).1⟩
  intro x hx
  simpa using (key x hx 1 h1).1

end Generic

theorem rep_blockPerm0 :
    CFSG.Monster.B.Co2.Rep 6 #[5, 3, 0, 2, 4, 1] blockPerm0 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_blockPerm1 :
    CFSG.Monster.B.Co2.Rep 6 #[2, 5, 0, 4, 3, 1] blockPerm1 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_blockTau2 :
    CFSG.Monster.B.Co2.Rep 6 #[4, 5, 3, 2, 0, 1] blockTau2 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_blockTau3 :
    CFSG.Monster.B.Co2.Rep 6 #[0, 2, 3, 5, 4, 1] blockTau3 := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_one6 :
    CFSG.Monster.B.Co2.Rep 6 #[0, 1, 2, 3, 4, 5] (1 : Perm (Fin 6)) := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem one_mem_closureList {X : Type*} [Group X] {E : Type*} [DecidableEq E] (nrm : X → X)
    (enc : X → E) (gens : List X) : ∀ k, (1 : X) ∈ closureList nrm enc gens k
  | 0 => by simp [closureList]
  | k + 1 => by
    simp only [closureList, closureStep, List.mem_append]
    exact Or.inl (one_mem_closureList nrm enc gens k)

theorem block_check_H :
    ∀ g ∈ [blockPerm0, blockPerm1], ∀ x ∈ blockHList,
    g * x ∈ blockHList ∧ g⁻¹ * x ∈ blockHList :=
  Certificates.certificate4095.1

theorem block_check_T :
    ∀ g ∈ [blockTau2, blockTau3], ∀ x ∈ blockTList,
    g * x ∈ blockTList ∧ g⁻¹ * x ∈ blockTList :=
  Certificates.certificate4095.2.1

theorem block_check_N : ∀ x ∈ blockHList,
    (∀ t ∈ [blockTau2, blockTau3], x * t * x⁻¹ ∈ blockTList) → x ∈ blockTList :=
  Certificates.certificate4095.2.2

theorem closure_pair_eq_list {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a, b} : Set G) = Subgroup.closure {g | g ∈ [a, b]} := by
  congr 1
  ext g
  simp

theorem block_normalizer {x : Perm (Fin 6)}
    (hx : x ∈ Subgroup.closure ({blockPerm0, blockPerm1} : Set (Perm (Fin 6))))
    (hn : ∀ t ∈ ({blockTau2, blockTau3} : Set (Perm (Fin 6))),
      x * t * x⁻¹ ∈ Subgroup.closure ({blockTau2, blockTau3} : Set (Perm (Fin 6)))) :
    x ∈ Subgroup.closure ({blockTau2, blockTau3} : Set (Perm (Fin 6))) := by
  have h1 : (1 : Perm (Fin 6)) ∈ blockTList := one_mem_closureList _ _ _ _
  have h1H : (1 : Perm (Fin 6)) ∈ blockHList := one_mem_closureList _ _ _ _
  have hxH : x ∈ blockHList := by
    rw [closure_pair_eq_list] at hx
    exact closure_subset_of_closed _ _ h1H block_check_H x hx
  have hnL : ∀ t ∈ [blockTau2, blockTau3], x * t * x⁻¹ ∈ blockTList := by
    intro t ht
    have ht' : t ∈ ({blockTau2, blockTau3} : Set (Perm (Fin 6))) := by simpa using ht
    have := hn t ht'
    rw [closure_pair_eq_list] at this
    exact closure_subset_of_closed _ _ h1 block_check_T _ this
  have hxT : x ∈ blockTList := block_check_N x hxH hnL
  rw [closure_pair_eq_list]
  exact closureList_subset_closure id (fun _ => rfl) id [blockTau2, blockTau3] 6 x hxT

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
