module

public import CFSG.CGT.A8S.LocalStmt
public import CFSG.Holt.H78.Defs
import CFSG.Holt.H78.Bridge

public section

namespace CFSG.CGT.A8S

open CFSG.Holt.General CFSG.Holt.H78

section Elementary

variable {G : Type} [Group G]

private theorem card_mod_four_of_sign_eq_one {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]
    {σ : Equiv.Perm Ψ} (hσ2 : σ ^ 2 = 1) {ψ₀ : Ψ} (hfix : ∀ ψ, σ ψ = ψ ↔ ψ = ψ₀)
    (hsign : Equiv.Perm.sign σ = 1) : Fintype.card Ψ % 4 = 1 := by
  have hsupp : σ.support = Finset.univ.erase ψ₀ := by
    ext ψ
    simp [Equiv.Perm.mem_support, hfix]
  have hcard : σ.support.card = Fintype.card Ψ - 1 := by
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hσ2
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hct, Multiset.sum_replicate, smul_eq_mul, hcard] at hsum
  have hs := Equiv.Perm.sign_of_cycleType σ
  rw [hsign, hct, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hs
  have hev := (neg_one_pow_eq_one_iff_even (by decide)).mp hs.symm
  have hpos : 1 ≤ Fintype.card Ψ := Fintype.card_pos_iff.mpr ⟨ψ₀⟩
  obtain ⟨k, hk⟩ := hev
  omega

private theorem eq_nine_of_factorial {n N : ℕ} (hn4 : n % 4 = 1) (hn7 : 7 ≤ n)
    (hN : N = n.factorial / 2) (h7 : ¬ 2 ^ 7 ∣ N) : n = 9 := by
  by_contra h9
  have h10 : 10 ≤ n := by omega
  apply h7
  obtain ⟨k, hk⟩ := (show 2 ^ 8 ∣ Nat.factorial 10 by decide).trans
    (Nat.factorial_dvd_factorial h10)
  rw [hN, hk, show 2 ^ 8 * k = 2 * (2 ^ 7 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
  exact Dvd.intro k rfl

private theorem card_center_le_two {S : Subgroup G} {z : G}
    (hZ : ∀ x ∈ S, ((∀ y ∈ S, x * y = y * x) ↔ (x = 1 ∨ x = z))) :
    Nat.card (Subgroup.center S) ≤ 2 := by
  classical
  have hmem : ∀ c : Subgroup.center S, ((c : S) : G) = 1 ∨ ((c : S) : G) = z := fun c =>
    (hZ _ (c : S).2).mp fun y hy => by
      have := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
  let f : Subgroup.center S → Bool := fun c => decide (((c : S) : G) = 1)
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : ((a : S) : G) = 1 ↔ ((b : S) : G) = 1 := by simpa [f] using hab
    apply Subtype.ext
    apply Subtype.ext
    by_cases ha1 : ((a : S) : G) = 1
    · rw [ha1, hab'.mp ha1]
    · rw [(hmem a).resolve_left ha1, (hmem b).resolve_left fun h => ha1 (hab'.mpr h)]
  calc Nat.card (Subgroup.center S) ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf
    _ = 2 := by simp

end Elementary

theorem holtA9Statement_of_holt (hHolt : CFSG.Holt.H78.HoltTheorem1) : HoltA9Statement := by
  intro G _ _ _ M hM S z hS hZ hTrip
  have : FaithfulSMul G (G ⧸ M) :=
    CFSG.RankThree.PartTwo.Sec21.faithfulSMul_quotient_of_simple hM
  have : Nontrivial (G ⧸ M) := QuotientGroup.nontrivial_iff.mpr hM
  obtain ⟨D⟩ := hHolt G (G ⧸ M)
    (IsHoltTriple.isStarGroup hTrip (IsHoltTriple.three_le_card hTrip))
  have hJ := jHull_eq_top_of_isSimpleGroup D.t_mem
  have hO := jOddCore_eq_bot_of_isSimpleGroup D.t_mem
  have hLi : ∀ i, D.L i = ⊤ := fun i => by
    have hn : (D.L i).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hJ ▸ D.le_normalizer i))
    have := HoltData.isSimpleGroup_L (D := D) hO i
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.L i) with h' | h'
    · exact absurd h' ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)
    · exact h'
  obtain ⟨i₀, hι⟩ := D.exists_forall_eq_of_le_L hO (B := ⊤) top_ne_bot fun i => (hLi i).ge
  let e : G ≃* D.M i₀ := Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (hLi i₀).symm).trans (D.lEquiv hO i₀))
  rcases D.factor i₀ with ⟨hA, h7⟩ | ⟨q, k, hB⟩
  ·
    have hMA : D.M i₀ = alternatingGroup (D.Ψc i₀) := hA
    have hzL : z ∈ D.L i₀ := by rw [hLi i₀]; exact Subgroup.mem_top z
    set c := D.coordEquiv hO hι with hc
    set σ : Equiv.Perm (D.Ψc i₀) := (D.lEquiv hO i₀ ⟨z, hzL⟩ : Equiv.Perm (D.Ψc i₀)) with hσ
    have hσc : ∀ ω, σ (c ω) = c (z • ω) := fun ω =>
      (D.coordEquiv_smul hO hι ⟨z, hzL⟩ ω).symm
    have hfixσ : ∀ ψ, σ ψ = ψ ↔ ψ = c ((1 : G) : G ⧸ M) := fun ψ => by
      obtain ⟨ω, rfl⟩ := c.surjective ψ
      rw [hσc, c.injective.eq_iff, c.injective.eq_iff]
      exact hTrip.smul_eq_iff ω
    have hσ2 : σ ^ 2 = 1 := by
      have hl : (⟨z, hzL⟩ : D.L i₀) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hTrip.orderOf_eq_two ▸ pow_orderOf_eq_one z)
      rw [hσ, ← Subgroup.coe_pow, ← map_pow, hl, map_one, Subgroup.coe_one]
    have hsign : Equiv.Perm.sign σ = 1 := by
      have hσM : σ ∈ D.M i₀ := (D.lEquiv hO i₀ ⟨z, hzL⟩).2
      rw [hMA] at hσM
      exact Equiv.Perm.mem_alternatingGroup.mp hσM
    have hmod := card_mod_four_of_sign_eq_one hσ2 hfixσ hsign
    have : Nontrivial (D.Ψc i₀) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hcardG : Nat.card G = (Fintype.card (D.Ψc i₀)).factorial / 2 := by
      rw [Nat.card_congr e.toEquiv, hMA, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    have hS6 : Nat.card (S : Subgroup G) = 2 ^ 6 := hS
    have h7' : ¬ 2 ^ 7 ∣ Nat.card G := fun hd => by
      have hd' := Sylow.pow_dvd_card_of_pow_dvd_card S hd
      rw [hS6] at hd'
      exact absurd (Nat.le_of_dvd (by positivity) hd') (by norm_num)
    have h9 := eq_nine_of_factorial hmod h7 hcardG h7'
    refine ⟨?_, ⟨e.trans ((MulEquiv.subgroupCongr hMA).trans
      (Equiv.altCongrHom (Fintype.equivFinOfCardEq h9)))⟩⟩
    rw [Subgroup.index, Nat.card_congr c, Nat.card_eq_fintype_card, h9]
  ·
    exfalso
    let S' : Sylow 2 (D.M i₀) := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have h4 := hB.four_le_card_center_sylow S'
    let eS : (S : Subgroup G) ≃* (S' : Subgroup (D.M i₀)) :=
      (Subgroup.equivMapOfInjective (S : Subgroup G) e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective e.surjective S).symm)
    have hcen : Nat.card (Subgroup.center (S : Subgroup G)) =
        Nat.card (Subgroup.center (S' : Subgroup (D.M i₀))) :=
      Nat.card_congr (Subgroup.centerCongr eS).toEquiv
    have h4' : 4 ≤ Nat.card (Subgroup.center (S : Subgroup G)) := by
      rw [hcen]
      exact h4
    have h2 := card_center_le_two hZ
    omega

end CFSG.CGT.A8S
