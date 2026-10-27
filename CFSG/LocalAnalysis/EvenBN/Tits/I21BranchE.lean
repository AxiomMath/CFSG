module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Filter
public import CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchE

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits
open scoped MatrixGroups Pointwise

section TwoGroupP

variable {G : Type} [Group G] {M : Subgroup G} {t : G}

theorem mem_normalizer_of_involution (ht : orderOf t = 2) (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) :
    t ∈ normalizer M := by
  have hti := inv_eq_self_of_orderOf_eq_two ht
  have ht2 : t * t = 1 := mul_eq_one_iff_eq_inv.mpr hti.symm
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨hMt g, fun hg => ?_⟩
  have h1 := hMt _ hg
  have e : t * (t * g * t⁻¹) * t⁻¹ = g := by
    rw [hti]
    calc t * (t * g * t) * t = (t * t) * g * (t * t) := by simp only [mul_assoc]
      _ = g := by rw [ht2, one_mul, mul_one]
  rwa [e] at h1

theorem relIndex_sup_zpowers (ht : orderOf t = 2) (htM : t ∉ M)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) : M.relIndex (M ⊔ zpowers t) = 2 := by
  have ht2 : t * t = 1 := mul_eq_one_iff_eq_inv.mpr (inv_eq_self_of_orderOf_eq_two ht).symm
  have hnorm : zpowers t ≤ normalizer M :=
    Subgroup.zpowers_le.mpr (mem_normalizer_of_involution ht hMt)
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left M (zpowers t) hnorm
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), htM, fun b hb => ?_⟩
  have hb' : b ∈ (M : Set G) * (zpowers t : Set G) := hcoe ▸ hb
  obtain ⟨m, hm, y, hy, rfl⟩ := hb'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · right
    simpa [hk] using hm
  · left
    simpa [hk, mul_assoc, ht2] using hm

theorem isPGroup_sup_zpowers [Finite G] (hM2 : IsPGroup 2 M) (ht : orderOf t = 2) (htM : t ∉ M)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) :
    IsPGroup 2 ↥(M ⊔ zpowers t) ∧ Nat.card ↥(M ⊔ zpowers t) = 2 * Nat.card M := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hM2
  have hidx := relIndex_sup_zpowers ht htM hMt
  have hc := Subgroup.relIndex_mul_card M (M ⊔ zpowers t)
  rw [inf_of_le_left le_sup_left, hidx] at hc
  exact ⟨IsPGroup.of_card (n := n + 1) (by rw [← hc, hn]; ring), hc.symm⟩

end TwoGroupP

section Shapes

theorem card_le_sixteen {G : Type} [Group G] {P : Subgroup G}
    (hexp : ∀ g : G, (∃ k : ℕ, orderOf g = 2 ^ k) → g ^ 8 = 1)
    (hP : (∃ m : ℕ, 1 ≤ m ∧ Nonempty (P ≃* DihedralGroup (2 ^ m))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* SemidihedralGroup n)) : Nat.card P ≤ 16 := by
  have key : ∀ (g : P) (k : ℕ), orderOf g = 2 ^ k → k ≤ 3 := by
    intro g k hg
    have h8 : (g : G) ^ 8 = 1 := hexp g ⟨k, by rw [Subgroup.orderOf_coe]; exact hg⟩
    have h8' : g ^ 8 = 1 := Subtype.ext (by simpa using h8)
    have hd : 2 ^ k ∣ 2 ^ 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one h8'
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hd
  rcases hP with ⟨m, hm, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · haveI : NeZero (2 ^ m) := ⟨by positivity⟩
    have hk := key (e.symm (DihedralGroup.r 1)) m
      (by rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one])
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have : 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · have hk := key (e.symm (CFSG.Semidihedral.r n)) (n - 1)
      (by rw [MulEquiv.orderOf_eq, CFSG.Semidihedral.orderOf_r n (by omega)]; rfl)
    rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card n (by omega)]
    have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem uniqueInv_of_isCyclic {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hc : IsCyclic M) : Sec622UniqueInv M := by
  intro a ha b hb hao hbo
  have h := CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution.eq_of_orderOf_eq_two_of_isCyclic
    (P := M) (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (by rwa [Subgroup.orderOf_mk])
    (by rwa [Subgroup.orderOf_mk])
  exact congrArg Subtype.val h

theorem uniqueInv_of_quaternion {G : Type} [Group G] [Finite G] {M : Subgroup G} {n : ℕ}
    (e : M ≃* QuaternionGroup (2 ^ (n - 2))) : Sec622UniqueInv M := by
  haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  intro a ha b hb hao hbo
  have h := CFSG.GF2Type.Aschbacher1976Full.LeafUniqueInvolution.eq_of_orderOf_eq_two_of_quaternion
    e (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (by rwa [Subgroup.orderOf_mk])
    (by rwa [Subgroup.orderOf_mk])
  exact congrArg Subtype.val h

end Shapes

section Main

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem dihedral_shape (h : Sec622Bar G t u x) {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (htL : t ∉ L) (hM : fusionIsSylowIn 2 M L)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M) (hE : M ⊓ centralizer ({t} : Set G) = zpowers (u ^ 2)) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 2 ∧ Nonempty (M ≃* DihedralGroup (2 ^ m)) ∧ Nat.card M ≤ 8 := by
  have ht : orderOf t = 2 := h.secTwo.orderOf_t
  have hu : orderOf u = 4 := h.secTwo.orderOf_u
  have htM : t ∉ M := fun hm => htL (hM.1 hm)
  obtain ⟨hP2, hPcard⟩ := isPGroup_sup_zpowers hM.2.1 ht htM hMt
  have hMP : M ≤ M ⊔ zpowers t := le_sup_left
  have htP : t ∈ M ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hidx := relIndex_sup_zpowers ht htM hMt
  have hzo : orderOf (u ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hu]; norm_num), hu]
  have hC : Nat.card ↥(M ⊓ centralizer ({t} : Set G)) = 2 := by
    rw [hE, Nat.card_zpowers, hzo]
  have hzM : u ^ 2 ∈ M := by
    have : u ^ 2 ∈ M ⊓ centralizer ({t} : Set G) := hE ▸ Subgroup.mem_zpowers (u ^ 2)
    exact this.1
  have hinv : ∃ e ∈ M, orderOf e = 2 := ⟨u ^ 2, hzM, hzo⟩
  obtain ⟨hMshape, hPshape⟩ := CFSG.Holt.suzuki_index_two hP2 hMP hidx htP htM ht hC
  have hP16 : Nat.card ↥(M ⊔ zpowers t) ≤ 16 := card_le_sixteen h.exp_two hPshape
  have hM8 : Nat.card M ≤ 8 := by omega
  rcases hMshape with hcyc | ⟨m, hm, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
  · exact (sec622_not_uniqueInv hnonab hM hinv (uniqueInv_of_isCyclic hcyc)).elim
  · haveI : NeZero (2 ^ m) := ⟨by positivity⟩
    have hcard : Nat.card M = 2 * 2 ^ m := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ⟨m, hm, hm2, ⟨e⟩, hM8⟩
  · exact (sec622_not_uniqueInv hnonab hM hinv (uniqueInv_of_quaternion e)).elim

theorem exists_sylow_dihedral {L M : Subgroup G} (hM : fusionIsSylowIn 2 M L) {m : ℕ}
    (e : M ≃* DihedralGroup (2 ^ m)) :
    ∃ S : Sylow 2 L, Nonempty ((S : Subgroup L) ≃* DihedralGroup (2 ^ m)) := by
  obtain ⟨S, hS⟩ := I21.Excl.exists_sylow hM
  exact ⟨S, ⟨((MulEquiv.subgroupCongr hS).trans (Subgroup.subgroupOfEquivOfLe hM.1)).trans e⟩⟩

theorem conclusion_of_recognition {L M : Subgroup G} [IsSimpleGroup L]
    (hM : fusionIsSylowIn 2 M L) (hLdvd : Nat.card L ∣ sec622N) (hM8 : Nat.card M ≤ 8)
    (hrec : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel L .PSL 2 p f) ∨
      Nonempty (L ≃* alternatingGroup (Fin 7))) :
    IsPSLTwo L 5 ∨ IsPSLTwo L 7 ∨ IsPSLTwo L 9 ∨ Nonempty (L ≃* alternatingGroup (Fin 7)) := by
  rcases hrec with ⟨p, f, hp, hp2, hf, hmodel⟩ | hA7
  swap
  · exact Or.inr (Or.inr (Or.inr hA7))
  obtain ⟨⟨-, -, -, h22, h23⟩, K, hKfield, hKfin, hKcard, ⟨eK⟩⟩ := hmodel
  let eL : L ≃* PSL(2, K) :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hLK : Nat.card L = Nat.card (PSL(2, K)) := Nat.card_congr eL.toEquiv
  have hodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ Nat.card K := by
    have h2 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
    have h3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨S, hS⟩ := I21.Excl.exists_sylow hM
  have hSM : Nat.card (S : Subgroup L) = Nat.card M :=
    Nat.card_congr ((MulEquiv.subgroupCongr hS).trans
      (Subgroup.subgroupOfEquivOfLe hM.1)).toEquiv
  have hv : (Nat.card L).factorization 2 ≤ 3 := by
    have h1 : 2 ^ (Nat.card L).factorization 2 ≤ 2 ^ 3 := by
      rw [← Sylow.card_eq_multiplicity S, hSM]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hPSL : ∀ q : ℕ, Nat.card K = q → IsPSLTwo L q := fun q hq =>
    ⟨K, hKfield, hKfin, hq, ⟨eL⟩⟩
  rw [hLK] at hv
  rcases sec622_filter_psl_odd hodd h5 (hLK ▸ hLdvd) with ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ |
      ⟨-, hv'⟩ | ⟨-, hv'⟩ | ⟨-, hv'⟩ | ⟨-, hv'⟩
  · exact Or.inl (hPSL 5 hq)
  · exact Or.inr (Or.inl (hPSL 7 hq))
  · exact Or.inr (Or.inr (Or.inl (hPSL 9 hq)))
  all_goals omega

end Main

end CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchE

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_branch_E
    (h : Sec622Bar G t u x) {L M : Subgroup G} (hLn : L.Normal)
    [IsSimpleGroup L] (hnonab : ∃ a b : L, a * b ≠ b * a) (htL : t ∉ L)
    (hM : fusionIsSylowIn 2 M L) (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hE : M ⊓ centralizer ({t} : Set G) = zpowers (u ^ 2)) :
    (Nonempty (M ≃* DihedralGroup 2) ∨ Nonempty (M ≃* DihedralGroup 4)) ∧
      (IsPSLTwo L 5 ∨ IsPSLTwo L 7 ∨ IsPSLTwo L 9 ∨
        Nonempty (L ≃* alternatingGroup (Fin 7))) := by
  have _ := hLn
  obtain ⟨m, hm1, hm2, ⟨e⟩, hM8⟩ := I21.BranchE.dihedral_shape h hnonab htL hM hMt hE
  obtain ⟨S, hSd⟩ := I21.BranchE.exists_sylow_dihedral hM e
  have hrec := CFSG.Milestones.lr_dihedral_simple_recognition L hnonab S (m + 1) (by omega)
    (by simpa using hSd)
  refine ⟨?_, I21.BranchE.conclusion_of_recognition hM
    ((Subgroup.card_subgroup_dvd_card L).trans h.card_dvd) hM8 hrec⟩
  interval_cases m
  · exact Or.inl ⟨e⟩
  · exact Or.inr ⟨e⟩

end CFSG.LocalAnalysis.EvenBN.Tits
