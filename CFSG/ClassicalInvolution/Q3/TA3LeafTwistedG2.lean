module

public import CFSG.ClassicalInvolution.Q3.TA3SmallDefs
public import CFSG.ClassicalInvolution.SmallCases.NobqSmall
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeWardKleidman
public import CFSG.LocalAnalysis.QuasithinUnique.ComponentSplitting
public import CFSG.Walter.JRFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.LiteratureLocal
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

theorem outTwoCyclic_of_odd {F : Type*} [Group F] [Finite F] (h : Odd (Nat.card (Outer F))) :
    Nobq.OutTwoCyclic F := by
  intro P hP
  have : Finite (MulAut F) := Nobq.finite_mulAut_of_finite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card (Outer F) := Subgroup.card_subgroup_dvd_card P
  rcases k with _ | k
  · rw [pow_zero] at hk
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
    infer_instance
  · exfalso
    rw [hk] at hdvd
    have h2 : 2 ∣ Nat.card (Outer F) := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
    exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr h2)

theorem noUniqueInvNormal_twistedG2 {X : Type} [Group X] {f : ℕ}
    (hree : ReeTitsModel X .twistedG2 3 f) : Nobq.NoUniqueInvNormal X := by
  intro t N ht hU
  obtain ⟨-, -, -, -, -, h3⟩ := hree.1
  obtain ⟨a, hea, -⟩ := hree.2
  subst hea
  have ha : 1 ≤ a := by omega
  obtain ⟨hfin, -, hcen, -⟩ := ward_kleidman_small_Ree_involution_centralizer_maximal a ha X hree
  obtain ⟨L, hLC, -, hsup, ⟨eL⟩, hZ⟩ := hcen t ht
  have hE4 : 4 ≤ Nat.card (GaloisField 3 (2 * a + 1)) := by
    rw [GaloisField.card 3 (2 * a + 1) (by omega)]
    calc 4 ≤ 3 ^ 2 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : IsSimpleGroup PSL(2, GaloisField 3 (2 * a + 1)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hE4
  have : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hLnab : ∃ u v : ↥L, u * v ≠ v * u := CFSG.Walter.exists_mul_ne_mul_of_mulEquiv_psl2 hE4 eL
  set C := Subgroup.centralizer ({t} : Set X) with hCdef
  have hNC : N ≤ C := hU.le_centralizer
  have hconjN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N := hU.conj_mem
  have hn : ((N ⊓ L).subgroupOf L).Normal := ⟨fun k hk l => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact ⟨hconjN l (hLC l.2) k hk.1, L.mul_mem (L.mul_mem l.2 hk.2) (L.inv_mem l.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ L).subgroupOf L) with h | h
  ·
    have hNL : ∀ x ∈ N, x ∈ L → x = 1 := by
      intro x hxN hxL
      have : (⟨x, hxL⟩ : L) ∈ (N ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr ⟨hxN, hxL⟩
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ x ∈ Subgroup.zpowers t, ∀ l ∈ L, x * l = l * x := by
      intro x hx l hl
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((show Commute t l from
        (Subgroup.mem_centralizer_singleton_iff.mp (hLC hl)).symm).zpow_left n).eq
    have hdec : ∀ c ∈ C, ∃ x ∈ Subgroup.zpowers t, ∃ l ∈ L, c = x * l := by
      intro c hc
      rw [← hsup] at hc
      obtain ⟨x, hx, l, hl, rfl⟩ :=
        (CFSG.QuasithinUnique.ComponentSplitting.mem_sup_iff_of_commute hcomm).mp hc
      exact ⟨x, hx, l, hl, rfl⟩
    have hCL : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L := by
      intro c hc l hl
      obtain ⟨x, hx, l', hl', rfl⟩ := hdec c hc
      have e : x * l' * l * (x * l')⁻¹ = l' * l * l'⁻¹ := by
        have h1 := hcomm x hx (l' * l * l'⁻¹) (L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl'))
        calc x * l' * l * (x * l')⁻¹ = x * (l' * l * l'⁻¹) * x⁻¹ := by group
          _ = l' * l * l'⁻¹ := by rw [h1, mul_inv_cancel_right]
      rw [e]
      exact L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
    have hNLc : ∀ n ∈ N, ∀ l ∈ L, n * l = l * n := by
      intro n hn l hl
      have h1 : n * l * n⁻¹ * l⁻¹ ∈ L := L.mul_mem (hCL n (hNC hn) l hl) (L.inv_mem hl)
      have h2 : n * l * n⁻¹ * l⁻¹ ∈ N := by
        have := N.mul_mem hn (hconjN l (hLC hl) n⁻¹ (N.inv_mem hn))
        simpa [mul_assoc] using this
      have := hNL _ h2 h1
      calc n * l = n * l * n⁻¹ * l⁻¹ * (l * n) := by group
        _ = l * n := by rw [this, one_mul]
    have hNt : ∀ n ∈ N, n ∈ Subgroup.zpowers t := by
      intro n hn
      have hcen : (⟨n, hNC hn⟩ : C) ∈ Subgroup.center C := by
        rw [Subgroup.mem_center_iff]
        intro c
        apply Subtype.ext
        obtain ⟨x, hx, l, hl, hcx⟩ := hdec c c.2
        have hxn : x * n = n * x := by
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
          exact ((show Commute t n from
            (Subgroup.mem_centralizer_singleton_iff.mp (hNC hn)).symm).zpow_left m).eq
        show (c : X) * n = n * c
        rw [hcx, mul_assoc, ← hNLc n hn l hl, ← mul_assoc, hxn, mul_assoc]
      have : n ∈ (Subgroup.center C).map C.subtype := ⟨_, hcen, rfl⟩
      rwa [hZ] at this
    obtain ⟨s, hsN, hs4⟩ := hU.exists_orderOf_eq_four
    have hdvd := orderOf_dvd_of_mem_zpowers (hNt s hsN)
    rw [hs4, ht] at hdvd
    exact absurd hdvd (by norm_num)
  ·
    have hLN : L ≤ N := fun l hl => by
      have : (⟨l, hl⟩ : L) ∈ (N ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    have h2L : 2 ∣ Nat.card L := by
      by_contra hodd
      have hodd' : Odd (Nat.card L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
      have hsol := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
      obtain ⟨u, v, huv⟩ := hLnab
      exact huv ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) u v)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2L
    have hu' : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
    have hut : (u : X) = t := hU.eq_of_orderOf_eq_two u (hLN u.2) hu'
    have huc : u ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hg := Subgroup.mem_centralizer_singleton_iff.mp (hLC g.2)
      show (g : X) * u = u * g
      rw [hut]
      exact hg
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with hc | hc
    · rw [hc, Subgroup.mem_bot] at huc
      rw [huc, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · obtain ⟨a', b', hab⟩ := hLnab
      exact hab ((Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b')) a')

theorem noDatum_twistedG2 {X : Type} [Group X] {f : ℕ} (hree : ReeTitsModel X .twistedG2 3 f) :
    Nobq.NoDatum X := by
  have hree' := hree
  obtain ⟨-, -, -, -, -, h3⟩ := hree'.1
  obtain ⟨a, hea, -⟩ := hree'.2
  subst hea
  obtain ⟨hfin, -, -, -, -, -, hodd⟩ :=
    ward_kleidman_small_Ree_involution_centralizer_maximal a (by omega) X hree
  exact Nobq.noDatum_of_noUniqueInvNormal (noUniqueInvNormal_twistedG2 hree)
    (outTwoCyclic_of_odd hodd)

theorem smallSimpleLeaf_of_noDatum {P : ∀ (F : Type) [Group F], Prop}
    (h : ∀ (F : Type) [Group F], P F → Nobq.NoDatum F) : SmallSimpleLeaf P := by
  intro Y _ _ _ _ hnab _ hPF R S t hd _ _
  exfalso
  have := genFittingFStar_normal Y
  obtain ⟨r, hr, ⟨eS⟩⟩ := hd.quat
  exact h _ hPF Y (genFittingFStar Y) ⟨MulEquiv.refl _⟩
    (Nobq.centralizer_genFittingFStar_eq_bot hnab) R S r hr ⟨eS⟩ t hd.mem hd.order hd.cent
    hd.normal

theorem noDatum_smallTwistedG2 : ∀ (F : Type) [Group F], SmallTwistedG2 F → Nobq.NoDatum F := by
  intro F _ hF
  obtain ⟨f, hm⟩ := hF
  rcases hm with ⟨htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, -, hr⟩ | ⟨-, htag, -⟩
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact noDatum_twistedG2 hr
  · exact absurd htag (by decide)

theorem smallSimpleLeaf_twistedG2 : SmallSimpleLeaf SmallTwistedG2 :=
  smallSimpleLeaf_of_noDatum noDatum_smallTwistedG2

end CFSG.ClassicalInvolution.Q3.TA3
