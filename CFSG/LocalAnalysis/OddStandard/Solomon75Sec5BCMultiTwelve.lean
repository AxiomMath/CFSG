module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiMirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiPiece
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BCMultiLu
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FracZero

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

section Twelve

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))}

theorem frac53_multi_12 (hTC : Solomon75TwoComp) (h : Sec5Data X n z Z S) (hk : ¬ Sec5One X n Z)
    (hn : n = 12) {s : X} (hs : IsSec5Inv X Z s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) (hsA : s ∈ normalizer (A : Set X))
    (M : AhatModel X n A)
    (hσ : fixCount (M.perm s hsA) = 4 ∨
      (transCount (M.perm s hsA) = 3 ∧ fixCount (M.perm s hsA) ≤ 3)) : False := by
  classical
  have hn8 : 8 ≤ n := h.maxdeg.1
  have hn16 : n < 16 := by omega
  have hσ4 : fixCount (M.perm s hsA) = 4 := by
    rcases hσ with h4 | ⟨h3, hf⟩
    · exact h4
    · exfalso
      have hadd := fixCount_add_support (M.perm s hsA)
      unfold transCount at h3
      omega
  have hk' : ∃ A₁ A₂ : Subgroup X, Sec5Comp X n (normalizer (Z : Set X)) A₁ ∧
      Sec5Comp X n (normalizer (Z : Set X)) A₂ ∧ A₁ ≠ A₂ := by
    by_contra hcon
    exact hk fun A₁ A₂ hA₁ hA₂ => by
      by_contra hne
      exact hcon ⟨A₁, A₂, hA₁, hA₂, hne⟩
  obtain ⟨u, hu, huZ, hu1, hus⟩ := h.exists_witness_Z hs hA hsA
  have hu2 : u * u = 1 := h.Z_sq_eq_one huZ
  have hs2 : s * s = 1 := hs.sq
  have hsu : s * u = u * s := hus.symm
  obtain ⟨L, E, hL, htL, M', huE, hEAL, hEcov, htE, hperm⟩ :=
    exists_Lu_model h hA huZ hu1 hu hsA hsu M
  have hbad : fixCount (M'.perm s htL) = 4 ∨
      (transCount (M'.perm s htL) = 3 ∧ fixCount (M'.perm s htL) ≤ 3) :=
    Or.inl (by rw [hperm]; exact hσ4)
  have hEL : E ≤ L := fun x hx => (hEAL hx).2
  obtain ⟨Q, hQE, hQ2, hQ8, huQ, hQpow, -, -, hQlp, -⟩ :=
    exists_sl23_piece hn8 hu2 hu1 hs2 hsu hL.isPCompIn hEL huE hEcov htL htE M' hbad
  have hQs : Q ≤ centralizer ({s} : Set X) := hQE.trans inf_le_right
  have hQn : ∀ B, Sec5Comp X n (centralizer ({s} : Set X)) B → Q ≤ normalizer (B : Set X) :=
    fun B hB => le_normalizer_of_le_lPlus_inf hu2 hus hQlp hB.isPCompIn
  obtain ⟨g, Zs, S₁, hZs, hQN, hQC, hS₁, hinv, hnorm, hdata⟩ :=
    mirror_package h hs huZ hu1 hus hQs hQ2 hQ8 huQ hQpow hQn (by omega)
  have hsZs : s ∈ Zs := hS₁.z_mem
  have key : ∀ E', Sec5Comp X n (normalizer (Zs : Set X)) E' → ∀ w,
      IsIntrinsicIn X (normalizer (Zs : Set X)) E' w → w ∈ Zs → w = s := by
    intro E' hE' w hw hwZs
    have hw1 : w ≠ 1 := by
      intro h1
      have := hw.1
      rw [h1, orderOf_one] at this
      omega
    have hw2 : w * w = 1 := hS₁.Z_sq_eq_one hwZs
    have hwu : w * u = u * w := Subgroup.mem_centralizer_iff.1 (hQC huQ) w hwZs
    have hu_E' : u ∈ normalizer (E' : Set X) := hnorm E' hE'
    obtain ⟨-, hfixE, -⟩ := hdata E' hE' hu_E' (AhatModel.ofCover hE'.2)
    have hfix4 : fixCount ((AhatModel.ofCover hE'.2).perm u hu_E') = 4 := by
      rw [hfixE]; omega
    obtain ⟨L', E'', hL', htL', M'', huE'', hEE'', hEcov'', htE'', hperm''⟩ :=
      exists_Lu_model hS₁ hE' hwZs hw1 hw hu_E' hwu.symm (AhatModel.ofCover hE'.2)
    have hbad'' : fixCount (M''.perm u htL') = 4 ∨
        (transCount (M''.perm u htL') = 3 ∧ fixCount (M''.perm u htL') ≤ 3) :=
      Or.inl (by rw [hperm'']; exact hfix4)
    have hEL'' : E'' ≤ L' := fun x hx => (hEE'' hx).2
    obtain ⟨Q', hQ'E, hQ'2, hQ'8, hwQ', hQ'pow, -, -, hQ'lp, -⟩ :=
      exists_sl23_piece hn8 hw2 hw1 hu2 hwu.symm hL'.isPCompIn hEL'' huE'' hEcov'' htL' htE''
        M'' hbad''
    have hQ'N : ∀ B, Sec5Comp X n (centralizer ({u} : Set X)) B → Q' ≤ normalizer (B : Set X) :=
      fun B hB => le_normalizer_of_le_lPlus_inf hw2 hwu hQ'lp hB.isPCompIn
    have hQ'L : Q' ≤ normalizer (L : Set X) := hQ'N L hL
    have hwL : w ∈ normalizer (L : Set X) := hQ'L hwQ'
    have hτ : M'.perm w hwL ≠ 1 := perm_ne_one_of_mem_Z hS₁ hinv hwZs hw1 hwu hL hwL M'
    obtain ⟨W, hW8, hτW, hWτ, hWc, -, hWrange⟩ :=
      q8_perm_data_range hn8 M' hQ'L hQ'8 hwQ' hQ'pow hw2 hτ
    have hsupp : (M'.perm w hwL).support.card = 8 := q8_support_card_eq hn16 hτ hW8 hWτ hWc
    have hτ2 : M'.perm w hwL * M'.perm w hwL = 1 := perm_sq_eq_one hn8 M' hwL hw2
    have hσ2 : M'.perm s htL * M'.perm s htL = 1 := perm_sq_eq_one hn8 M' htL hs2
    have hE'K : E' ≤ K0 X n (normalizer (Zs : Set X)) := le_sSup hE'
    have hσW : ∀ g' ∈ W, g' * M'.perm s htL = M'.perm s htL * g' := by
      intro g' hg'
      obtain ⟨q, hq, rfl⟩ := hWrange g' hg'
      have hqE' : q ∈ E' := (hEE'' (hQ'E hq).1).1
      have hqs : s * q = q * s := hS₁.Z_le_center_K0 hsZs (hE'K hqE')
      let a : ↥(normalizer (L : Set X)) := ⟨q, hQ'L hq⟩
      let b : ↥(normalizer (L : Set X)) := ⟨s, htL⟩
      have hab : b * a = a * b := Subtype.ext hqs
      have := congrArg (M'.permHom hn8) hab
      rw [map_mul, map_mul] at this
      exact this.symm
    have hfixσ : fixCount (M'.perm s htL) = n - 8 := by
      rw [hperm]; omega
    have heq : M'.perm s htL = M'.perm w hwL :=
      eq_of_commute_of_fixCount hn16 hτ2 hτW hsupp hW8 hWτ hσ2 hσW hfixσ
    have hswL : s * w ∈ normalizer (L : Set X) := Subgroup.mul_mem _ htL hwL
    have hsw1 : M'.perm (s * w) hswL = 1 := by
      rw [M'.perm_mul hn8 htL hwL, heq]; exact hτ2
    have hcent : CentModOdd L (s * w) := (M'.perm_eq_one_iff hn8 hswL).1 hsw1
    by_cases hsw : s * w = 1
    · have : w = s⁻¹ := eq_inv_of_mul_eq_one_right hsw
      rw [this]; exact inv_eq_of_mul_eq_one_right hs2
    · exfalso
      have hwsc : w * s = s * w := hS₁.Z_comm hwZs hsZs
      have hsw2 : (s * w) ^ 2 = 1 := by
        rw [pow_two]
        calc s * w * (s * w) = s * (w * s) * w := by group
          _ = s * (s * w) * w := by rw [hwsc]
          _ = (s * s) * (w * w) := by group
          _ = 1 := by rw [hs2, hw2, one_mul]
      have hswZs : s * w ∈ Zs := Subgroup.mul_mem _ hsZs hwZs
      have hswu : (s * w) * u = u * (s * w) := by
        calc (s * w) * u = s * (w * u) := by group
          _ = s * (u * w) := by rw [hwu]
          _ = (s * u) * w := by group
          _ = (u * s) * w := by rw [hsu]
          _ = u * (s * w) := by group
      have hne := K0_ne_bot_of_centralizerSection (n := n) hsw2 hL
        (show s * w ∈ centralizerSection L (pPrimeCoreOf 2 L) from mem_QOf_iff.2 ⟨hswL, hcent⟩)
      exact hne (sec5_K0_inf_eq_bot hS₁ hinv hswZs hsw hswu)
  have hZs_le : Zs ≤ Subgroup.zpowers s := by
    refine hS₁.pair.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 ?_)
    rintro u' ⟨hu'Z, L₀, hL₀, hL₀n⟩
    obtain ⟨h1, h2, -⟩ := hS₁.pair.isIntrinsicIn_normalizer hu'Z hL₀ hL₀n
    have hu'eq : u' = s := key _ ⟨⟨u', h1⟩, h2⟩ u' h1 hu'Z
    rw [hu'eq]
    exact Subgroup.mem_zpowers s
  have hs1 : s ≠ 1 := fun h1 => hs.notMem (h1 ▸ one_mem Z)
  have hord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hc1 : Nat.card Zs ≤ Nat.card (Subgroup.zpowers s) := Subgroup.card_le_of_le hZs_le
  rw [Nat.card_zpowers, hord] at hc1
  have hc2 : Nat.card Z = Nat.card Zs := by
    rw [hZs]
    exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm
  have hz2 : orderOf z = 2 := h.orderOf_z
  have hzZ : Subgroup.zpowers z ≤ Z := (Subgroup.zpowers_le).2 h.z_mem
  have hZz : Z = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge hzZ (by rw [Nat.card_zpowers, hz2]; omega)).symm
  subst hZz
  have hNc : normalizer ((Subgroup.zpowers z : Subgroup X) : Set X) = centralizer ({z} : Set X) :=
    normalizer_zpowers_eq_centralizer h.orderOf_z
  obtain ⟨A₁, A₂, hA₁, hA₂, hne⟩ := hk'
  have hA₁' : Sec5Comp X n (centralizer ({z} : Set X)) A₁ := by rw [← hNc]; exact hA₁
  have hA₂' : Sec5Comp X n (centralizer ({z} : Set X)) A₂ := by rw [← hNc]; exact hA₂
  exact hTC X n z S h ⟨A₁, A₂, hA₁', hA₂', hne⟩

end Twelve

end CFSG.OddStandard.Solomon75
