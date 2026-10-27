module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S10M

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] noncomputable def t1 (C : StdCfg T M H S L) : G := ((C.iV w04w : ↥H) : G)

theorem t1_mem_S (C : StdCfg T M H S L) : C.t1 ∈ S :=
  blockU_le_S C.hcs C.hj (C.iV_mem_U w04w)

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] noncomputable def s01 : G := ((X.s sa : ↥H) : G)

theorem s01_mem_S : X.s01 ∈ S := X.s_mem_S sa_mem

theorem rg_t1
    : ((X.rg C.t1 : GL (Fin 4) (ZMod 2)) : Mat4) = Mt1 := by
  have hM : C.t1 ∈ M := C.M1_le_M C.t1_mem_M1
  rw [X.rg_of_mem hM]
  have := X.rho'_eq_rho ⟨((C.iV w04w : ↥H) : G), C.t1_mem_M1⟩
  rw [X.rho_t1] at this
  exact this

theorem rg_s01
    : ((X.rg X.s01 : GL (Fin 4) (ZMod 2)) : Mat4) = Ms01 := by
  have hM : X.s01 ∈ M := C.M1_le_M X.s01_mem_M1
  rw [X.rg_of_mem hM]
  have := X.rho'_eq_rho ⟨((X.s sa : ↥H) : G), X.s01_mem_M1⟩
  rw [X.rho_s01] at this
  exact this

theorem rg_t1_s01
    : ((X.rg (C.t1 * X.s01) : GL (Fin 4) (ZMod 2)) : Mat4) = Mt1 * Ms01 := by
  have h1 : C.t1 ∈ M := C.M1_le_M C.t1_mem_M1
  have h2 : X.s01 ∈ M := C.M1_le_M X.s01_mem_M1
  rw [X.rg_mul h1 h2, Units.val_mul, X.rg_t1, X.rg_s01]

theorem card_rgS
    : Nat.card ((X.rho'.comp (Subgroup.inclusion C.S_le_M)).range) = 4 := by
  set ρS : ↥S →* GL (Fin 4) (ZMod 2) := X.rho'.comp (Subgroup.inclusion C.S_le_M) with hρS
  have hker : ρS.ker = (borelP M L).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have : ρS s = X.rg (s : G) := (X.rg_of_mem (C.S_le_M s.2)).symm
    rw [this]
    exact X.rg_eq_one_iff (C.S_le_M s.2)
  have h1 := Subgroup.card_ker_mul_card_range ρS
  have h2 : Nat.card ρS.ker = 32 := by
    rw [hker, ← X.card_P]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe X.P_le_S).toEquiv
  rw [h2, X.card_S] at h1
  omega

theorem rg_S_cases {s : G} (hs : s ∈ S) :
    X.rg s = 1 ∨ X.rg s = X.rg C.t1 ∨ X.rg s = X.rg X.s01 ∨ X.rg s = X.rg (C.t1 * X.s01) := by
  classical
  set ρS : ↥S →* GL (Fin 4) (ZMod 2) := X.rho'.comp (Subgroup.inclusion C.S_le_M) with hρS
  have hcard := X.card_rgS
  have h1M : C.t1 ∈ M := C.M1_le_M C.t1_mem_M1
  have h2M : X.s01 ∈ M := C.M1_le_M X.s01_mem_M1
  let a1 : GL (Fin 4) (ZMod 2) := X.rg C.t1
  let a2 : GL (Fin 4) (ZMod 2) := X.rg X.s01
  let a3 : GL (Fin 4) (ZMod 2) := X.rg (C.t1 * X.s01)
  have hrg : ∀ s' : ↥S, ρS s' = X.rg (s' : G) := fun s' => (X.rg_of_mem (C.S_le_M s'.2)).symm
  have ha1 : a1 ∈ ρS.range := ⟨⟨C.t1, C.t1_mem_S⟩, by rw [hrg]⟩
  have ha2 : a2 ∈ ρS.range := ⟨⟨X.s01, X.s01_mem_S⟩, by rw [hrg]⟩
  have ha3 : a3 ∈ ρS.range :=
    ⟨⟨C.t1 * X.s01, S.mul_mem C.t1_mem_S X.s01_mem_S⟩, by rw [hrg]⟩
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := S4_distinct
  have hne : ∀ {a b : GL (Fin 4) (ZMod 2)}, (a : Mat4) ≠ (b : Mat4) → a ≠ b := fun h hab =>
    h (congrArg Units.val hab)
  have n01 : (1 : GL (Fin 4) (ZMod 2)) ≠ a1 := hne (by rw [X.rg_t1]; exact d01)
  have n02 : (1 : GL (Fin 4) (ZMod 2)) ≠ a2 := hne (by rw [X.rg_s01]; exact d02)
  have n03 : (1 : GL (Fin 4) (ZMod 2)) ≠ a3 := hne (by rw [X.rg_t1_s01]; exact d03)
  have n12 : a1 ≠ a2 := hne (by rw [X.rg_t1, X.rg_s01]; exact d12)
  have n13 : a1 ≠ a3 := hne (by rw [X.rg_t1, X.rg_t1_s01]; exact d13)
  have n23 : a2 ≠ a3 := hne (by rw [X.rg_s01, X.rg_t1_s01]; exact d23)
  let F : Finset (GL (Fin 4) (ZMod 2)) := {1, a1, a2, a3}
  have hFcard : F.card = 4 := by
    simp [F, Finset.card_insert_of_notMem, n01, n02, n03, n12, n13, n23]
  have hsub : (F : Set (GL (Fin 4) (ZMod 2))) ⊆ (ρS.range : Set (GL (Fin 4) (ZMod 2))) := by
    intro x hx
    simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact ha1
    · exact ha2
    · exact ha3
  have hncard : (ρS.range : Set (GL (Fin 4) (ZMod 2))).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [Set.ncard_coe_finset, hFcard, hncard]) (Set.toFinite _)
  have hmem : X.rg s ∈ (ρS.range : Set (GL (Fin 4) (ZMod 2))) :=
    ⟨⟨s, hs⟩, hrg ⟨s, hs⟩⟩
  rw [← heq] at hmem
  simp only [F, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hmem
  exact hmem

theorem rg_S_mem_VSL
    {s : G} (hs : s ∈ S) : ((X.rg s : GL (Fin 4) (ZMod 2)) : Mat4) ∈ VSL := by
  rw [mem_VSL]
  rcases X.rg_S_cases hs with h | h | h | h
  · left; rw [h]; rfl
  · right; left; rw [h, X.rg_t1]
  · right; right; left; rw [h, X.rg_s01]
  · right; right; right; rw [h, X.rg_t1_s01]

theorem exists_S_of_VSL {V : Mat4} (hV : V ∈ VSL) :
    ∃ s ∈ S, ((X.rg s : GL (Fin 4) (ZMod 2)) : Mat4) = V := by
  rw [mem_VSL] at hV
  rcases hV with rfl | rfl | rfl | rfl
  · exact ⟨1, one_mem _, by rw [X.rg_one]; rfl⟩
  · exact ⟨C.t1, C.t1_mem_S, X.rg_t1⟩
  · exact ⟨X.s01, X.s01_mem_S, X.rg_s01⟩
  · exact ⟨C.t1 * X.s01, S.mul_mem C.t1_mem_S X.s01_mem_S, X.rg_t1_s01⟩

end Sec

end CFSG.QuasithinUnique.A5
