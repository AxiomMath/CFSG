module

public import CFSG.ClassicalInvolution.Q3.Q3URTwG
public import CFSG.ClassicalInvolution.Q3.Q3URTwE
public import CFSG.ClassicalInvolution.Q3.Q3URPhanA3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.BorelTits
open scoped MatrixGroups

section Triple

variable {G : Type} [Group G]

theorem exists_triple_of_completion (hC : PhanA3Completion3) {A B C : Subgroup G}
    (hiA : Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* A))
    (hiB : Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* B))
    (hiC : Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* C)) (hAC : Commutes A C)
    (p₁ : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W A B)
    (p₂ : ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W B C)
    (hA1 : ∃ a ∈ A, a ≠ 1)
    (hcen : ∀ u : G, (∃ k : ℕ, u ^ 3 ^ k = 1) → A ≤ Subgroup.centralizer ({u} : Set G) →
      C ≤ Subgroup.centralizer ({u} : Set G) → u = 1) :
    ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G, θ.range = (A ⊔ B) ⊔ (B ⊔ C) ∧
      θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = A ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = B ∧
      (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = C := by
  classical
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_gf9
  have hq2 : 3 ^ 1 ≠ 2 := by norm_num
  let U : Fin 3 → Subgroup G := ![A, B, C]
  set Gs : Subgroup G := ⨆ i, U i with hGsdef
  have hUle : ∀ i, U i ≤ Gs := fun i => le_iSup U i
  have hGs : Gs = (A ⊔ B) ⊔ (B ⊔ C) := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right.trans le_sup_right
    · exact sup_le (sup_le (le_iSup U 0) (le_iSup U 1)) (sup_le (le_iSup U 1) (le_iSup U 2))
  have hiso : ∀ i, Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* U i) := by
    intro i
    fin_cases i
    exacts [hiA, hiB, hiC]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → Commutes (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    exact hAC
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact p₁
    · exact p₂
  have hW : WeakPhanA (GaloisField 3 2) 3 1 3 (fun i => (U i).subgroupOf Gs)
      (fun i j => (U i).subgroupOf Gs ⊔ (U j).subgroupOf Gs) :=
    { iso := fun i => ⟨((hiso i).some.trans (Subgroup.subgroupOfEquivOfLe (hUle i)).symm)⟩
      join := fun i j _ => rfl
      comm := fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy)
      pair := fun i j hj => by
        obtain ⟨W, hWp⟩ := hpair i j hj
        have hWe := typeU_standardPair_eq_sup hK hq2 hWp
        have := typeU_standardPair_subgroupOf (J := Gs)
          (hWe ▸ sup_le (hUle i) (hUle j)) hWp
        rw [hWe, typeU_subgroupOf_sup_of_le (hUle i) (hUle j)] at this
        exact this
      gen := iSup_subgroupOf_self U }
  obtain ⟨E, instE, p, ε, V, hpsurj, hker, hVp, hVε⟩ := hC hW
  have hεsurj : Function.Surjective ε := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hW.gen]
    refine iSup_le fun i => ?_
    have h1 := Subgroup.map_le_range ε (V i)
    rwa [hVε i] at h1
  have hkerε : p.ker ≤ ε.ker := by
    intro e he
    obtain ⟨hecen, k, hek⟩ := hker e he
    rw [MonoidHom.mem_ker]
    have hgcen : ∀ y : ↥Gs, ε e * y = y * ε e := by
      intro y
      obtain ⟨e', rfl⟩ := hεsurj y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hecen e')]
    have hg3 : ((ε e : ↥Gs) : G) ^ 3 ^ k = 1 := by
      have h1 : (ε e) ^ 3 ^ k = 1 := by rw [← map_pow, hek, map_one]
      have h2 := congrArg Subtype.val h1
      simpa using h2
    have hcentr : ∀ X : Subgroup G, X ≤ Gs →
        X ≤ Subgroup.centralizer ({((ε e : ↥Gs) : G)} : Set G) := by
      intro X hX x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val (hgcen ⟨x, hX hx⟩)).symm
    have h1 : ((ε e : ↥Gs) : G) = 1 :=
      hcen _ ⟨k, hg3⟩ (hcentr A (hUle 0)) (hcentr C (hUle 2))
    exact Subtype.ext h1
  let θ₀ : Su (GaloisField 3 2) 3 1 4 →* ↥Gs :=
    MonoidHom.liftOfRightInverse p (Function.surjInv hpsurj) (Function.rightInverse_surjInv hpsurj)
      ⟨ε, hkerε⟩
  have hθ₀ : ∀ e, θ₀ (p e) = ε e := fun e =>
    MonoidHom.liftOfRightInverse_comp_apply p (Function.surjInv hpsurj)
      (Function.rightInverse_surjInv hpsurj) ⟨ε, hkerε⟩ e
  have hθ₀comp : θ₀.comp p = ε := MonoidHom.ext hθ₀
  have hθ₀range : θ₀.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨e, rfl⟩ := hεsurj y
    exact ⟨p e, hθ₀ e⟩
  have hquasi : CFSG.IsQuasisimple (Su (GaloisField 3 2) 3 1 4) := by
    have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK (n := 4)
      (by norm_num) (by
        intro h
        have : (4 : ℕ) = 3 := (Prod.mk.inj h).1
        omega)).1
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4)).symm h
  have hnontriv : ∃ k, θ₀ k ≠ 1 := by
    obtain ⟨a, haA, ha1⟩ := hA1
    by_contra hall
    push Not at hall
    obtain ⟨e, he⟩ := hεsurj ⟨a, hUle 0 haA⟩
    have h2 : ε e = 1 := by rw [← hθ₀, hall]
    rw [h2] at he
    exact ha1 (congrArg Subtype.val he).symm
  have hkerθ₀ : θ₀.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hquasi hnontriv
  have hmap : ∀ a : Fin 3, (blockEmb2 (GaloisField 3 2) 3 1 3 a).range.map θ₀ =
      (U a).subgroupOf Gs := by
    intro a
    rw [← hVp a, Subgroup.map_map, hθ₀comp]
    exact hVε a
  refine ⟨Gs.subtype.comp θ₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hθ₀range, Subgroup.map_top, Subgroup.range_subtype]
    exact hGs
  · intro x hx
    apply hkerθ₀
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  · rw [← Subgroup.map_map, hmap 0, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle 0)]
    try rfl
  · rw [← Subgroup.map_map, hmap 1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle 1)]
    try rfl
  · rw [← Subgroup.map_map, hmap 2, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hUle 2)]
    try rfl

end Triple

section Row

theorem chainRow3U_two (h3 : OddThreeFreeInput) (hP : Q3TC.ProductP1Input3)
    (hC : PhanA3Completion3) : ChainRow3U 2 := by
  intro G _ _ _ hnab K z hR hshape
  obtain ⟨d⟩ := UChain2.nonempty h3 hP hnab hR hshape
  obtain ⟨hex, -⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hiso : ∀ L ∈ conjClass3 K, Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* L) := fun L hL =>
    nonempty_su_two_equiv_of_member3 hR.inClass hex hL
  have hcen : ∀ A B : Subgroup G, A ∈ conjClass3 K → B ∈ conjClass3 K → Commutes A B → A ≠ B →
      ∀ u : G, (∃ k : ℕ, u ^ 3 ^ k = 1) → A ≤ Subgroup.centralizer ({u} : Set G) →
        B ≤ Subgroup.centralizer ({u} : Set G) → u = 1 := by
    intro A B hA hB hAB hne u hu hAu hBu
    obtain ⟨k, hk⟩ := hu
    exact centralizer_pow_eq_one h3 hnab hR hshape hA hB hAB hne
      (n := 3 ^ k) (Nat.Coprime.pow_left k (by norm_num)) hk hAu hBu
  have hne1 : ∀ (L : Subgroup G) (w : G), IsClassicalMember3 L w → ∃ a ∈ L, a ≠ 1 := by
    intro L w hw
    refine ⟨w, hw.mem, fun h => ?_⟩
    have := hw.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have T₀ := exists_triple_of_completion hC (hiso K hK) (hiso d.β d.hβ) (hiso d.j0 d.hj0) d.c0
    d.pKβ d.pβ0 (hne1 K z hR.cls) (hcen K d.j0 hK d.hj0 d.c0 d.neK0)
  have T₁ := exists_triple_of_completion hC (hiso d.β d.hβ) (hiso d.j0 d.hj0) (hiso d.j1 d.hj1)
    d.cβ1 d.pβ0 d.p01 (hne1 d.β d.t d.clβ) (hcen d.β d.j1 d.hβ d.hj1 d.cβ1 d.neβ1)
  refine ⟨![K, d.β, d.j0, d.j1], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hK
    · exact d.hβ
    · exact d.hj0
    · exact d.hj1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact d.c0
    · exact d.c1
    · exact d.cβ1
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | (exfalso; exact absurd hij (by decide)) | skip
    · exact d.pKβ
    · exact d.pβ0
    · exact d.p01
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | (exfalso; exact absurd hij (by decide)) | (exfalso; exact absurd hjk (by decide)) |
        skip
    · exact T₀
    · exact T₁

end Row

end CFSG.ClassicalInvolution.Q3.Q3W
