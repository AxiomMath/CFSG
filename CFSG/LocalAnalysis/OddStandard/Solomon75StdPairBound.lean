module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPairRep
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermDiag
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermArith
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdBasicSolv

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS AhatData

section Bounds

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

theorem StdPair.exists_pi (M : AhatModel G n L) (M' : AhatModel G n L') {σ : Perm (Fin n)}
    (hσ : M.perm a P.a_mem_norm = σ) {r : M.K} (hr : IsPairLift M.C σ r) {H : Subgroup M.K}
    {hH : H ≤ fixSub (M.autOf a P.a_mem_norm)} (hHr : ∀ x ∈ H, x * r = r * x) :
    ∃ π : Perm (Fin n), π * π = M'.perm z P.z_mem_norm' ∧ π ^ 4 = 1 ∧
      ∀ d : ↥H, P.rep M M' H hH d * π = π * P.rep M M' H hH d := by
  subst hσ
  obtain ⟨hsq, hcomm⟩ := P.emb_pairLift M hr
  have hrN : P.setup.emb M r ∈ normalizer (L' : Set G) :=
    P.setup'.mem_normalizer_of_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.2 hcomm)
  have hππ : M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN =
      M'.perm z P.z_mem_norm' := by
    rw [← M'.perm_mul P.setup'.hn hrN hrN]
    exact M'.perm_congr hsq _ _
  refine ⟨M'.perm (P.setup.emb M r) hrN, hππ, ?_, fun d => P.rep_comm hHr hrN d⟩
  have h4 : M'.perm (P.setup.emb M r) hrN ^ 4 =
      (M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN) *
        (M'.perm (P.setup.emb M r) hrN * M'.perm (P.setup.emb M r) hrN) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rw [h4, hππ]
  exact P.perm_z_sq M'

theorem StdPair.rep_zK (M : AhatModel G n L) (M' : AhatModel G n L') {H : Subgroup M.K}
    {hH : H ≤ fixSub (M.autOf a P.a_mem_norm)} (hzH : P.setup.zK M ∈ H) :
    P.rep M M' H hH ⟨P.setup.zK M, hzH⟩ = M'.perm z P.z_mem_norm' :=
  P.rep_eq_perm _ (P.setup.emb_zK M) _

theorem StdPair.bound_i (M : AhatModel G n L) (M' : AhatModel G n L')
    (hf : 5 ≤ fixCount (M.perm a P.a_mem_norm)) :
    2 * fixCount (M.perm a P.a_mem_norm) ≤ transCount (M'.perm z P.z_mem_norm') := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  have hm2 := P.two_le_transCount M M'
  have hind := M.induces_perm hn a P.a_mem_norm
  have hσ'1 := P.perm_z_ne_one M'
  have hn1 := card_eq_of_involution hσ2
  have hsupp := card_support_eq_two_mul_transCount hσ2
  generalize hσg : M.perm a P.a_mem_norm = σ at hσ2 hind hm2 hf hn1 hsupp ⊢
  obtain ⟨r, hr⟩ := exists_isPairLift M.C hσ2 hsupp hm2
  have hf5 : 5 ≤ n - 2 * transCount σ := by omega
  obtain ⟨hDfix, hDcov, hDmap⟩ := hind.fixedCompOf_isDoubleCover M.C hn hσ2 hsupp hf5
  have hcen : center M.K ≤ M.C.fixedCompOf σ :=
    M.C.center_le_of_doubleCover hDmap hDcov (by omega) (by omega)
  have hzD : P.setup.zK M ∈ M.C.fixedCompOf σ := hcen (P.setup.zK_mem_center M)
  obtain ⟨π, hππ, hπ4, hι⟩ := P.exists_pi M M' hσg hr (hH := hDfix)
    (fun x hx => hr.comm_of_mem_fixedCompOf hx)
  have hιz : P.rep M M' _ hDfix ⟨P.setup.zK M, hzD⟩ = π ^ 2 := by
    rw [P.rep_zK M M' hzD, pow_two, hππ]
  have hπ2 : π ^ 2 ≠ 1 := by
    rw [pow_two, hππ]
    exact hσ'1
  have h := four_mul_le_card_support_sq_of_doubleCover (by omega) hDcov hπ4
    (P.rep M M' _ hDfix) hι hιz hπ2
  rw [pow_two, hππ, card_support_eq_two_mul_transCount hσ'2] at h
  omega

theorem StdPair.bound_ii (M : AhatModel G n L) (M' : AhatModel G n L')
    (hf : fixCount (M.perm a P.a_mem_norm) = 4) :
    6 ≤ transCount (M'.perm z P.z_mem_norm') := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  have hm2 := P.two_le_transCount M M'
  have hind := M.induces_perm hn a P.a_mem_norm
  have hσ'1 := P.perm_z_ne_one M'
  have hn1 := card_eq_of_involution hσ2
  have hsupp := card_support_eq_two_mul_transCount hσ2
  generalize hσg : M.perm a P.a_mem_norm = σ at hσ2 hind hm2 hf hn1 hsupp ⊢
  obtain ⟨r, hr⟩ := exists_isPairLift M.C hσ2 hsupp hm2
  have hf4 : σ.support.card + 4 ≤ n := by omega
  have hEfix := altFixOf_comap_le_fixSub M.C hn hind hf4
  have hzE : P.setup.zK M ∈ (altFixOf σ).comap M.C.ρ :=
    center_le_altFixOf_comap M.C σ (P.setup.zK_mem_center M)
  obtain ⟨π, hππ, hπ4, hι⟩ := P.exists_pi M M' hσg hr (hH := hEfix)
    (fun x hx => hr.comm_of_mem_altFixOf_comap hn hf4 hx)
  have hιz : P.rep M M' _ hEfix ⟨P.setup.zK M, hzE⟩ = π ^ 2 := by
    rw [P.rep_zK M M' hzE, pow_two, hππ]
  have hπ2 : π ^ 2 ≠ 1 := by
    rw [pow_two, hππ]
    exact hσ'1
  have h := twelve_le_card_support_sq (oddGenerated_altFixOf_comap M.C hn hf4) hπ4
    (P.rep M M' _ hEfix) hι hιz hπ2
  rw [pow_two, hππ, card_support_eq_two_mul_transCount hσ'2] at h
  omega

theorem StdPair.bound_iii (M : AhatModel G n L) (M' : AhatModel G n L')
    (hm : 7 ≤ transCount (M.perm a P.a_mem_norm)) :
    transCount (M.perm a P.a_mem_norm) - 2 ≤
      max (transCount (M'.perm z P.z_mem_norm') / 2) (fixCount (M'.perm z P.z_mem_norm')) := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  have hind := M.induces_perm hn a P.a_mem_norm
  have hn1 := card_eq_of_involution hσ2
  have hn2 := card_eq_of_involution hσ'2
  have hsupp := card_support_eq_two_mul_transCount hσ2
  generalize hσg : M.perm a P.a_mem_norm = σ at hσ2 hind hm hn1 hsupp ⊢
  obtain ⟨r, hr, Y, hY, hYr, -, β, hβ1, hβ2, hβc, θ, hθ⟩ :=
    exists_diag M.C hind hσ2 hsupp hm
  obtain ⟨π, hππ, hπ4, hι⟩ := P.exists_pi M M' hσg hr (hH := hY) hYr
  have hker : Group.IsSolvable (P.rep M M' Y hY).ker := by
    have := P.setup'.isSolvable_centralizer
    let e : ↥(P.rep M M' Y hY).ker →* ↥(centralizer (L' : Set G)) :=
      (((P.setup.emb M).comp Y.subtype).comp (P.rep M M' Y hY).ker.subtype).codRestrict
        (centralizer (L' : Set G)) (fun x => (P.rep_eq_one_iff x.1).1 x.2)
    refine Group.isSolvable_of_isSolvable_injective (f := e) ?_
    intro x y hxy
    have h1 : ((e x : ↥(centralizer (L' : Set G))) : G) =
        ((e y : ↥(centralizer (L' : Set G))) : G) := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (P.setup.emb_injective M h1))
  have h := card_le_max_of_surjective_alternating (π := π) (by omega) θ hθ hπ4 (P.rep M M' Y hY)
    hι hker
  rw [pow_two, hππ, card_support_eq_two_mul_transCount hσ'2, Fintype.card_fin, hβc] at h
  have h3 : 2 * transCount (M'.perm z P.z_mem_norm') / 4 =
      transCount (M'.perm z P.z_mem_norm') / 2 := by omega
  have h4 : n - 2 * transCount (M'.perm z P.z_mem_norm') =
      fixCount (M'.perm z P.z_mem_norm') := by omega
  rw [h3, h4] at h
  exact h

end Bounds

section Table

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L L' : Subgroup G} {n : ℕ} {z a : G}
  (P : StdPair G L L' n z a)

theorem StdPair.arith (M : AhatModel G n L) (M' : AhatModel G n L') :
    (transCount (M.perm a P.a_mem_norm) = 4 ∨ transCount (M.perm a P.a_mem_norm) = 6) ∧
      (transCount (M'.perm z P.z_mem_norm') = 4 ∨ transCount (M'.perm z P.z_mem_norm') = 6) ∧
      n ≤ 16 ∧ (12 ≤ n → transCount (M.perm a P.a_mem_norm) = 6 ∨
        transCount (M'.perm z P.z_mem_norm') = 6) := by
  have hn := P.setup.hn
  have hσ2 := P.perm_a_sq M
  have hσ'2 := P.perm_z_sq M'
  have h1 := card_eq_of_involution hσ2
  have h2 := card_eq_of_involution hσ'2
  exact pair_arith hn h1 h2 (P.symm.even_transCount' M' M) (P.two_le_transCount M M')
    (P.even_transCount' M M') (P.symm.two_le_transCount M' M) (P.bound_i M M')
    (P.symm.bound_i M' M) (P.bound_ii M M') (P.symm.bound_ii M' M) (P.bound_iii M M')
    (P.symm.bound_iii M' M)

end Table

end CFSG.OddStandard.Solomon75
