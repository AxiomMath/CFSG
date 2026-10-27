module

public import CFSG.ClassicalInvolution.Balance.QNineLocal
public import CFSG.ClassicalInvolution.RouteD.TypeCLocal

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Models
open scoped MatrixGroups commutatorElement

section Linear

variable {F : Type} [Field F]

theorem exists_linearBlockStandardPair_rootSL2_map {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X]
    (ψ : SL(n, F) →* X) (hψ : ψ.ker ≤ Subgroup.center SL(n, F)) :
    ∃ V W : Subgroup X, WeakCT.LinearBlockStandardPair F W
      ((rootSL2 F (by omega : 2 ≤ n)).map ψ) V := by
  obtain ⟨θ, hker, hθ⟩ : ∃ θ : SL(3, F) →* X, θ.ker ≤ Subgroup.center SL(3, F) ∧
      (WeakCT.B12 F).map θ = (rootSL2 F (by omega : 2 ≤ n)).map ψ := by
    rcases Nat.eq_or_lt_of_le hn with rfl | hlt
    · exact ⟨ψ, hψ, rfl⟩
    · have h3 : 0 + 3 ≤ n := by omega
      refine ⟨ψ.comp (WeakCT.blockSL F n 3 0 h3), fun x hx => ?_, ?_⟩
      · rw [WeakCT.eq_one_of_blockSL_mem_center h3 hlt (hψ hx)]
        exact one_mem _
      · have e : (WeakCT.blockSL F n 3 0 h3).comp (WeakCT.blockSL F 3 2 0 (by omega)) =
            WeakCT.blockSL F n 2 0 (by omega) := WeakCT.blockSL_comp h3 (by omega)
        rw [WeakCT.B12, rootSL2, ← Subgroup.map_map, MonoidHom.map_range, e]
  refine ⟨(WeakCT.B23 F).map θ, θ.range, θ, 1, rfl, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [SymplecticPairs.map_conj_one, hθ]
  · rw [SymplecticPairs.map_conj_one]

end Linear

section Symplectic

open CFSG.ClassicalInvolution.Models.SymplecticPairs

theorem symplecticLongBlockImage_planeGroup_map {F : Type} [Field F] {m : ℕ} (hm : 2 ≤ m)
    {X : Type} [Group X] (ψ : CFSG.Assembly.LowTwoRank.StatedSp m F →* X)
    (hψ : ψ.ker ≤ Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp m F))
    {P : Submodule F (Fin m ⊕ Fin m → F)} (hP : IsHyperbolicPlane P) :
    SymplecticLongBlockImage F ((planeGroup P).map ψ) := by
  let j : Fin m := ⟨m - 1, by omega⟩
  let i : Fin m := ⟨m - 2, by omega⟩
  have hij : i ≠ j := fun h => by
    have := congrArg Fin.val h
    simp only [i, j] at this
    omega
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP j
  refine ⟨(ψ.comp (MulAut.conj g).toMonoidHom).comp
    (spEmbed (pairMap i j) (pairMap_injective hij)), fun x hx => ?_, ?_⟩
  · have h1 : g * spEmbed (pairMap i j) (pairMap_injective hij) x * g⁻¹ ∈
        Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSp m F) := hψ hx
    have h2 := mem_center_of_conj_mem_center h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply spEmbed_injective (pairMap_injective hij)
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp h2 _
  · rw [hg, Subgroup.map_map, ← Subgroup.map_map, MonoidHom.map_range,
      spEmbed_comp_longBlock hij]

end Symplectic

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_member_leviBlockImage_of_psl (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (i : Fin D.card) (ht : D.tag i = .PSL) {k : ℕ} (hr : D.rank i = k + 1) (hk : 2 ≤ k) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨ψ, hker, -, hfund⟩ := exists_psl_hom D i ht hr
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  refine ⟨L, hL, ?_⟩
  obtain ⟨R', hR', hRR'⟩ := (hfund (R.map (D.hom i))).mp ⟨R, hR, rfl⟩
  have hk2 : 2 ≤ k + 1 := by omega
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hk2).mp (fundamentalSubgroups_psl_subset hk2 hR')
  rw [hLR, hRR', Subgroup.map_map]
  obtain ⟨V, W, hVW⟩ := exists_linearBlockStandardPair_rootSL2_map (by omega : 3 ≤ k + 1)
    (ψ.comp (MulAut.conj g).toMonoidHom) (WeakCT.ker_comp_mulEquiv_le_center hker _)
  exact Or.inl ⟨V, W, hVW⟩

theorem exists_member_leviBlockImage_of_psp (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (i : Fin D.card) (ht : D.tag i = .PSp) {m : ℕ} (hr : D.rank i = m) (hm : 2 ≤ m) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨ψ, hker, -, hfund⟩ := exists_psp_hom D i ht hr
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  refine ⟨L, hL, ?_⟩
  obtain ⟨P, hP, hRP⟩ := (hfund (R.map (D.hom i))).mp ⟨R, hR, rfl⟩
  rw [hLR, hRP]
  exact Or.inr (Or.inr (symplecticLongBlockImage_planeGroup_map hm ψ hker hP))

theorem exists_member_leviBlockImage_of_model (hq : 5 ≤ p ^ f)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i : Fin D.card) (hexp : D.exp i = f)
    (hmodel : ∀ R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, LeviBlockImage p (D.exp i) R) :
    ∃ L ∈ centralizingMembers Ω {x}, LeviBlockImage p f (locImg Ω x L) := by
  obtain ⟨R, hR, hRΦ⟩ := D.meets i
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp hRΦ
  refine ⟨L, hL, ?_⟩
  rw [hLR]
  exact LeviBlockImage.congr_exp hexp (LeviBlockImage.map (by rw [hexp]; exact hq) (hmodel R hR)
    (D.hom i) (D.ker_le_center i))

end Component

end CFSG.ClassicalInvolution.Balance
