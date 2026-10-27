module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique CFSG.Open

structure Mem where
  order : ℕ
  o2 : ℕ
  quot2 : ℕ
  deriving DecidableEq

@[expose] def MemStmt {X : Type} [Group X] (Y : Subgroup X) (m : Mem) : Prop :=
  Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 ∧
    ∀ (N : Subgroup Y) [N.Normal], IsPGroup 2 (Y ⧸ N) → Nat.card (Y ⧸ N) ≤ m.quot2

section Transfer

variable {X Γ : Type} [Group X] [Group Γ]

theorem MemStmt.of_map (e : X ≃* Γ) {Y : Subgroup X} {m : Mem}
    (h : MemStmt (Y.map e.toMonoidHom) m) : MemStmt Y m := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]
    exact (Subgroup.card_map_of_injective e.injective).symm
  · rw [← h2, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 e Y]
    exact (Subgroup.card_map_of_injective e.injective).symm
  · intro N hN hp
    let φ : Y ≃* Y.map e.toMonoidHom := e.subgroupMap Y
    let N' : Subgroup (Y.map e.toMonoidHom) := N.map φ.toMonoidHom
    have : N'.Normal := Subgroup.Normal.map hN φ.toMonoidHom φ.surjective
    have hq : (Y ⧸ N) ≃* ((Y.map e.toMonoidHom) ⧸ N') :=
      QuotientGroup.congr N N' φ rfl
    have hp' : IsPGroup 2 ((Y.map e.toMonoidHom) ⧸ N') := hp.of_equiv hq
    have := h3 N' hp'
    rwa [← Nat.card_congr hq.toEquiv] at this

theorem isSylowTwoOf_map (e : X ≃* Γ) {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) :
    IsSylowTwoOf (T.map e.toMonoidHom) ⊤ := by
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map e.toMonoidHom, ?_⟩
  rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  exact hi

end Transfer

theorem overgroups_of_lattice {Γ : Type} [Group Γ] [Finite Γ] (S : Subgroup Γ)
    (hS : IsSylowTwoOf S ⊤) (J : ℕ) (Y : ℕ → Subgroup Γ) (mems : List Mem)
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j)
    (hmem : ∀ j < J, ∃ m ∈ mems, MemStmt (Y j) m)
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* Γ)) {T Z : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hTZ : T ≤ Z) :
    Z = ⊤ ∨ ∃ m ∈ mems, MemStmt Z m := by
  obtain ⟨e⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map e hT
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp.toSylow hi) (hp₀.toSylow hi₀)
  have hST : S = (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg
    exact this.symm
  let ψ : X ≃* Γ := e.trans (MulAut.conj g)
  have hψ : T.map ψ.toMonoidHom = S := by
    rw [hST, Subgroup.map_map]
    rfl
  have hSZ : S ≤ Z.map ψ.toMonoidHom := by
    rw [← hψ]; exact Subgroup.map_mono hTZ
  obtain ⟨j, hj, hZ⟩ := hall _ hSZ
  by_cases hjJ : j < J
  · right
    have hm : memberOrTop J Y j = Y j := by simp [memberOrTop, hjJ]
    rw [hm] at hZ
    obtain ⟨m, hmm, hrow⟩ := hmem j hjJ
    refine ⟨m, hmm, MemStmt.of_map ψ ?_⟩
    rw [hZ]; exact hrow
  · left
    have hm : memberOrTop J Y j = ⊤ := by simp [memberOrTop, hjJ]
    rw [hm] at hZ
    have := congrArg (Subgroup.comap ψ.toMonoidHom) hZ
    rw [Subgroup.comap_map_eq_self_of_injective ψ.injective, Subgroup.comap_top] at this
    exact this

end CFSG.QuasithinUnique.Ch1.SporLat
