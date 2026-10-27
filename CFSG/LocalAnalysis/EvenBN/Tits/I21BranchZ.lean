module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Filter
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Outer
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
public import CFSG.Milestones.LR_semidihedral_simple_recognition

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchZ

open Subgroup CFSG.Open
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G]

theorem orderOf_sq_of_orderOf_four {w : G} (hw4 : orderOf w = 4) : orderOf (w ^ 2) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul]
    show w ^ 4 = 1
    rw [← hw4]
    exact pow_orderOf_eq_one w
  · intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hw4] at this
    omega

theorem uniqueInv_zpowers [Finite G] {w : G} (hw4 : orderOf w = 4) :
    Sec622UniqueInv (zpowers w) := by
  have key : ∀ a ∈ zpowers w, orderOf a = 2 → a = w ^ 2 := by
    intro a ha ha2
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
      (mem_powers_iff_mem_zpowers.mpr ha)
    have hsq : (w ^ n) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (w ^ n)
      rwa [ha2] at this
    have hne : w ^ n ≠ 1 := fun h => by
      rw [h, orderOf_one] at ha2
      omega
    have h1 : 4 ∣ n * 2 := by
      rw [← hw4]
      exact orderOf_dvd_of_pow_eq_one (by rw [← pow_mul] at hsq; exact hsq)
    have h2 : ¬ 4 ∣ n := fun h => hne (orderOf_dvd_iff_pow_eq_one.mp (hw4 ▸ h))
    have h3 : n % 4 = 2 := by omega
    rw [← pow_mod_orderOf, hw4, h3]
  exact fun a ha b hb ha2 hb2 => (key a ha ha2).trans (key b hb hb2).symm

theorem eq_zpowers_of_card [Finite G] {M : Subgroup G} {w : G} (hwM : w ∈ M)
    (hw4 : orderOf w = 4) (hM4 : Nat.card M = 4) : M = zpowers w := by
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwM) ?_).symm
  rw [Nat.card_zpowers, hw4, hM4]

theorem orderOf_w {t u w : G} (h : SecTwoHyp G t u) (hw : w = u ∨ w = t * u) :
    orderOf w = 4 := by
  rcases hw with hw | hw
  · rw [hw]
    exact h.orderOf_u
  · have h2 : (t * u) ^ 2 = u ^ 2 := by rw [h.commute_tu.mul_pow, h.t_sq, one_mul]
    have h4 : (t * u) ^ 2 ^ (1 + 1) = 1 := by
      rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, ← pow_mul]
      exact h.u_pow_four
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := t * u)
      (by rw [pow_one, h2]; exact h.z_ne_one) h4
    rw [hw]
    simpa using this

theorem w_mem {M : Subgroup G} {t w : G}
    (hZ : M ⊓ centralizer ({t} : Set G) = zpowers w) : w ∈ M := by
  have : w ∈ M ⊓ centralizer ({t} : Set G) := by
    rw [hZ]
    exact mem_zpowers w
  exact this.1

theorem isMulCommutative_subgroupOf {M L : Subgroup G} (hab : IsMulCommutative M) :
    IsMulCommutative (M.subgroupOf L) :=
  IsMulCommutative.of_comm fun a b => by
    refine Subtype.ext (Subtype.ext ?_)
    exact congrArg (Subtype.val : M → G)
      (isMulCommutative_iff.mp hab ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)

theorem card_eq_pow_factorization [Finite G] {M L : Subgroup G} (hM : fusionIsSylowIn 2 M L) :
    Nat.card M = 2 ^ (Nat.card L).factorization 2 := by
  obtain ⟨S, hS⟩ := I21.Excl.exists_sylow hM
  have h1 := Sylow.card_eq_multiplicity S
  rw [hS] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM.1).toEquiv).symm

theorem factorization_eq_of_card [Finite G] {M L : Subgroup G} (hM : fusionIsSylowIn 2 M L)
    {k : ℕ} (hk : Nat.card M = 2 ^ k) : (Nat.card L).factorization 2 = k := by
  have := (card_eq_pow_factorization hM).symm.trans hk
  exact Nat.pow_right_injective (le_refl 2) this

theorem exists_sylow_equiv {M L : Subgroup G} (hM : fusionIsSylowIn 2 M L) {X : Type*}
    [Group X] (e : M ≃* X) : ∃ S : Sylow 2 L, Nonempty ((S : Subgroup L) ≃* X) := by
  obtain ⟨S, hS⟩ := I21.Excl.exists_sylow hM
  exact ⟨S, ⟨(MulEquiv.subgroupCongr hS).trans ((Subgroup.subgroupOfEquivOfLe hM.1).trans e)⟩⟩

end Generic

section Recognition

theorem abelian_false {G : Type} [Group G] [Finite G] {L M : Subgroup G} [IsSimpleGroup L]
    (hnonab : ∃ a b : L, a * b ≠ b * a) (hM : fusionIsSylowIn 2 M L)
    (hdvd : Nat.card L ∣ sec622N) {w : G} (hwM : w ∈ M) (hw4 : orderOf w = 4)
    (hW : (∃ f : ℕ, 2 ≤ f ∧ Nonempty (↥L ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p f : ℕ, ∃ _hp : Fact p.Prime, Odd p ∧ 0 < f ∧ 5 ≤ p ^ f ∧
        (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ Nonempty (↥L ≃* PSL(2, GaloisField p f))) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nat.card L = ordRee (3 ^ (2 * m + 1))) ∨
      Nonempty (↥L ≃* walterJ1)) : False := by
  have hwL : w ∈ L := hM.1 hwM
  have hwo : orderOf (⟨w, hwL⟩ : L) = 4 := by
    rw [Subgroup.orderOf_mk]
    exact hw4
  rcases hW with ⟨f, -, ⟨e⟩⟩ | ⟨p, f, hp, hpodd, hf, h5le, hmod, ⟨e⟩⟩ | ⟨m, hm, hree⟩ | ⟨⟨e⟩⟩
  ·
    have hchar : ringChar (GaloisField 2 f) = 2 := ringChar.eq (GaloisField 2 f) 2
    have hg4 : e ⟨w, hwL⟩ ^ 4 = 1 := by
      rw [← map_pow, ← hwo, pow_orderOf_eq_one, map_one]
    have hg2 := sec622_psl2_even_no_order_four hchar _ hg4
    rw [← map_pow, ← map_one e] at hg2
    have h2 := e.injective hg2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hwo] at this
    omega
  ·
    have hcardK : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf.ne'
    have hodd : Odd (Nat.card (GaloisField p f)) := hcardK ▸ hpodd.pow
    have h5 : 5 ≤ Nat.card (GaloisField p f) := hcardK ▸ h5le
    have hcardL : Nat.card L = Nat.card (PSL(2, GaloisField p f)) := Nat.card_congr e.toEquiv
    have hdvd' : Nat.card (PSL(2, GaloisField p f)) ∣ sec622N := hcardL ▸ hdvd
    have hmod' : Nat.card (GaloisField p f) % 8 = 3 ∨ Nat.card (GaloisField p f) % 8 = 5 := by
      rw [hcardK]
      exact hmod
    rcases sec622_filter_psl_odd hodd h5 hdvd' with ⟨-, hv⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ |
      ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩
    · have hM4 : Nat.card M = 4 := by
        rw [card_eq_pow_factorization hM, hcardL, hv]
        norm_num
      have hMeq := eq_zpowers_of_card hwM hw4 hM4
      refine sec622_not_uniqueInv hnonab hM ⟨w ^ 2, pow_mem hwM 2,
        orderOf_sq_of_orderOf_four hw4⟩ ?_
      rw [hMeq]
      exact uniqueInv_zpowers hw4
    all_goals
      rw [hq] at hmod'
      omega
  · exact sec622_not_ree hm (hree ▸ hdvd)
  · exact sec622_not_J1 e hdvd

theorem semidihedral_false {L : Type} [Group L]
    (hdvd : Nat.card L ∣ sec622N)
    (hS : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
          StatedClassicalModel L .PSL 3 p f) ∨
      (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
          StatedClassicalModel L .PSU 3 p f) ∨
      Nonempty (L ≃* StatedM11)) : False := by
  rcases hS with ⟨p, f, hp, hp2, -, -, hm⟩ | ⟨p, f, hp, hp2, -, h4, hm⟩ | ⟨⟨e⟩⟩
  · exact sec622_not_psl_three hp hp2 hm hdvd
  · have h3 := sec622_psu_three hp hp2 hm hdvd
    rw [h3] at h4
    omega
  · exact sec622_not_M11 e hdvd

theorem dihedral_false {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}
    (hLn : L.Normal) (hcent : centralizer (L : Set G) = ⊥)
    (htL : t ∉ L) (ht2 : t ^ 2 = 1) (hdvd : Nat.card L ∣ sec622N)
    (hv : (Nat.card L).factorization 2 = 3)
    (hcard : Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 4 ∨
      Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 20)
    (hD : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ StatedClassicalModel ↥L .PSL 2 p f) ∨
      Nonempty (↥L ≃* alternatingGroup (Fin 7))) : False := by
  rcases hD with ⟨p, f, hp, hp2, hf, hadm, K, hKf, hKfin, hK, ⟨φ⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨-, -, -, -, h23⟩ := hadm
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    have hodd : Odd (Nat.card K) := hK ▸ hpodd.pow
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hp3 : p ≤ p ^ f := Nat.le_self_pow (Nat.one_le_iff_ne_zero.mp hf) p
    have h5 : 5 ≤ Nat.card K := by
      have h1 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
      have h2 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
      rw [hK] at h2 ⊢
      omega
    let e2 : ↥L ≃* PSL(2, K) :=
      φ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
    have hcardL : Nat.card L = Nat.card (PSL(2, K)) := Nat.card_congr e2.toEquiv
    have hdvd' : Nat.card (PSL(2, K)) ∣ sec622N := hcardL ▸ hdvd
    have hv' : (Nat.card (PSL(2, K))).factorization 2 = 3 := hcardL ▸ hv
    rcases sec622_filter_psl_odd hodd h5 hdvd' with ⟨-, hvq⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ |
      ⟨-, hvq⟩ | ⟨-, hvq⟩ | ⟨-, hvq⟩ | ⟨-, hvq⟩
    · exact absurd (hvq.symm.trans hv') (by norm_num)
    · have h6 := sec622_outer_L2_seven hLn hcent ⟨K, hKf, hKfin, hq, ⟨e2⟩⟩ ht2 htL
      omega
    · rcases sec622_outer_L2_nine hLn hcent ⟨K, hKf, hKfin, hq, ⟨e2⟩⟩ ht2 htL with ⟨h10, -⟩ | h24
      · omega
      · omega
    all_goals exact absurd (hvq.symm.trans hv') (by norm_num)
  · rcases sec622_outer_A7 hLn hcent ⟨e⟩ ht2 htL with h | h <;> omega

end Recognition

end CFSG.LocalAnalysis.EvenBN.Tits.I21.BranchZ

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_branch_Z_false_of
    (h : Sec622Bar G t u x) {L M : Subgroup G} (hLn : L.Normal)
    [IsSimpleGroup L] (hnonab : ∃ a b : L, a * b ≠ b * a)
    (hcent : centralizer (L : Set G) = ⊥) (htL : t ∉ L) (hM : fusionIsSylowIn 2 M L)
    (hMt : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (_hMC : fusionIsSylowIn 2 (M ⊓ centralizer ({t} : Set G)) (L ⊓ centralizer ({t} : Set G)))
    {w : G} (hw : w = u ∨ w = t * u) (hZ : M ⊓ centralizer ({t} : Set G) = zpowers w)
    (hcard : Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 4 ∨
      Nat.card (L ⊓ centralizer ({t} : Set G) : Subgroup G) = 20)
    (h62 : ∀ {L' M' : Subgroup G}, L'.Normal → t ∉ L' → IsPGroup 2 M' → M' ≤ L' →
      (∀ m ∈ M', t * m * t⁻¹ ∈ M') → ∀ {w' : G}, (w' = u ∨ w' = t * u) →
      M' ⊓ centralizer ({t} : Set G) = zpowers w' →
      Sec622UniqueInv M' ∨ IsMulCommutative M' ∨ Nonempty (M' ≃* SemidihedralGroup 4) ∨
        Nonempty (M' ≃* DihedralGroup 4) ∨ Sec622Order16 M' ∨ Sec622CentralInv M' ∨
        Sec622ProdDihedral M' 3) : False := by
  have hw4 : orderOf w = 4 := I21.BranchZ.orderOf_w h.secTwo hw
  have hwM : w ∈ M := I21.BranchZ.w_mem hZ
  have hdvd : Nat.card L ∣ sec622N := (Subgroup.card_subgroup_dvd_card L).trans h.card_dvd
  rcases h62 hLn htL hM.2.1 hM.1 hMt hw hZ with huniq | hab | hsd | hdih | h16 | hcen | hprod
  ·
    exact sec622_not_uniqueInv hnonab hM
      ⟨w ^ 2, pow_mem hwM 2, I21.BranchZ.orderOf_sq_of_orderOf_four hw4⟩ huniq
  ·
    obtain ⟨S, hS⟩ := I21.Excl.exists_sylow hM
    have hP : IsMulCommutative (S : Subgroup L) :=
      hS ▸ I21.BranchZ.isMulCommutative_subgroupOf hab
    exact I21.BranchZ.abelian_false hnonab hM hdvd hwM hw4
      (CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple ↥L hnonab S hP)
  ·
    obtain ⟨e⟩ := hsd
    obtain ⟨S, ⟨e'⟩⟩ := I21.BranchZ.exists_sylow_equiv hM e
    exact I21.BranchZ.semidihedral_false hdvd
      (CFSG.Milestones.lr_semidihedral_simple_recognition_1 ↥L hnonab ⟨S, 4, le_refl 4, ⟨e'⟩⟩)
  ·
    obtain ⟨e⟩ := hdih
    obtain ⟨S, ⟨e'⟩⟩ := I21.BranchZ.exists_sylow_equiv hM e
    have hM8 : Nat.card M = 2 ^ 3 := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      norm_num
    exact I21.BranchZ.dihedral_false hLn hcent htL h.secTwo.t_sq hdvd
      (I21.BranchZ.factorization_eq_of_card hM hM8) hcard
      (CFSG.Milestones.lr_dihedral_simple_recognition ↥L hnonab S 3 (by norm_num) ⟨e'⟩)
  · exact sec622_not_order16 hnonab hM h16
  · exact sec622_not_centralInv hnonab hM hcen
  · exact sec622_not_prodDihedral hnonab hM hprod

end CFSG.LocalAnalysis.EvenBN.Tits
