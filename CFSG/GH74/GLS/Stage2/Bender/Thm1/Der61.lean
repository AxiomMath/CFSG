module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section P61

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inverts_comm {z : G} {A : Subgroup G} (h : Inverts z A) :
    ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  intro x hx y hy
  have h1 := h (x * y) (A.mul_mem hx hy)
  have h2 : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
  rw [h2, h x hx, h y hy, mul_inv_rev] at h1
  have h3 := congrArg (fun t => t⁻¹) h1
  simpa using h3.symm

theorem prime_dvd_card_of_Op_ne_bot {r : ℕ} (hr : r.Prime) {X : Subgroup G} (h : Op r X ≠ ⊥) :
    r ∣ Nat.card ↥X := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_Op r hr X)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h (Subgroup.eq_bot_of_card_eq _ (by rw [hn, pow_zero]))
  have h1 : Nat.card ↥(Op r X) ∣ Nat.card ↥X := Subgroup.card_dvd_of_le (Op_le r X)
  rw [hn] at h1
  exact (dvd_pow_self r hn0).trans h1

theorem prop6_1_of (hB12 : Bender12) (hB13 : Bender13) (h118 : IG_11_8) : Prop6_1 := by
  intro G _ _ z k S M p hC X hXP hX0 hXC
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_two hC.orderOf_z
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hXF : X ≤ Fm M := hXP.trans (Op_le_Fm p hp M)
  have hXM : X ≤ M := hXF.trans (Fm_le M)
  have hzP : z ∈ normalizer ((Op p M : Subgroup G) : Set G) := le_normalizer_Op p M hC.z_mem
  refine ⟨hXF, hX0, hXC (mem_Cen_self z), ?_⟩
  by_contra hNX
  have hXn : normalizer (X : Set G) ≠ ⊤ := normalizer_ne_top hC hX0 hXM
  obtain ⟨N, hN, hXN⟩ : ∃ N : Subgroup G, IsCoatom N ∧ normalizer (X : Set G) ≤ N := by
    rcases eq_top_or_exists_le_coatom (normalizer (X : Set G)) with h | h
    · exact absurd h hXn
    · exact h
  have hNM : N ≠ M := fun h => hNX (h ▸ hXN)
  have hCN : Cen z ≤ N := hXC.trans hXN
  have hNmem : N ∈ maximalOverCentralizer z := ⟨hN, hCN⟩
  have hXFN : Fs M ⊓ normalizer (X : Set G) ≤ N := inf_le_right.trans hXN
  have hLink : Links M N := ⟨X, hXF, hXFN⟩
  obtain ⟨hD1, hU, -⟩ := hB12 G hC.ctx.std.kps M N hC.coatom X hXF hXFN
  have hnp : ¬ ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥(Fs M) := by
    rintro ⟨q, hq, hqP⟩
    rw [hC.Fs_eq hC.mem] at hqP
    exact not_isPGroup_of_twoPrimes hC.twoPrimes hq hqP
  have hUM : Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm M)} N ≤ M := hU.resolve_left hnp
  have hFN : Fm N ≤ Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm M)} N ⊔
      Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm M)} N :=
    Fm_le_Fpi_sup (fun q => q ∣ Nat.card ↥(Fm M)) N
  have hDF : Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm M)} N ≤ Fm N := Fpi_le_Fm _ N
  have hND : N ≤ normalizer ((Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm M)} N : Subgroup G) : Set G) :=
    le_normalizer_Fpi (fun q hq => hq.1) N
  have hFsN : Fs N = Fm N := hC.Fs_eq hNmem
  generalize hUdef : Fpi {q | q.Prime ∧ q ∣ Nat.card ↥(Fm M)} N = U at hUM hFN
  generalize hDdef : Fpi {q | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm M)} N = D at hD1 hFN hDF hND
  by_cases hD0 : D = ⊥
  ·
    have hFNM : Fm N ≤ M := hFN.trans (sup_le hUM ((le_of_eq hD0).trans bot_le))
    have hLink' : Links N M := ⟨⊥, bot_le, inf_le_left.trans (hFsN.le.trans hFNM)⟩
    rcases hB13 G hC.ctx.std.kps M N hC.coatom hN hLink hLink' with h | ⟨q, hq, hqM, -⟩
    · exact hNM h.symm
    · rw [hC.Fs_eq hC.mem] at hqM
      exact not_isPGroup_of_twoPrimes hC.twoPrimes hq hqM
  have hzN : z ∈ N := hCN (mem_Cen_self z)
  have hzD : z ∈ normalizer (D : Set G) := hND hzN
  have hinvD : Inverts z D := by
    refine inverts_of_fixed_free hz2 hzD fun d hd hzd => ?_
    have hdC : d ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm
    have : d ∈ D ⊓ M := ⟨hd, hC.cen_le hdC⟩
    rw [hD1, Subgroup.mem_bot] at this
    exact this
  by_cases hU0 : U = ⊥
  ·
    have hFND : Fm N = D := by
      refine le_antisymm ?_ hDF
      simpa [hU0] using hFN
    have hNPX : Op p M ⊓ normalizer (X : Set G) ≤ Cen z := by
      intro u hu
      have huN : u ∈ N := hXN hu.2
      have hcomm := commutator_centralizes_of_inverts hz2 hinvD (hND huN)
      have hwN : u * z * u⁻¹ * z⁻¹ ∈ N :=
        N.mul_mem (N.mul_mem (N.mul_mem huN hzN) (N.inv_mem huN)) (N.inv_mem hzN)
      have hwF : u * z * u⁻¹ * z⁻¹ ∈ Fm N := by
        refine mem_Fm_of_centralizes_Fs hwN ?_
        rw [hFsN, hFND]
        intro d hd
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm d hd).symm
      have hwP : u * z * u⁻¹ * z⁻¹ ∈ Op p M := by
        have h1 := (Op p M).mul_mem hu.1 ((mem_normalizer_iff.mp hzP u⁻¹).mp ((Op p M).inv_mem hu.1))
        simpa [mul_assoc] using h1
      have hwDM : u * z * u⁻¹ * z⁻¹ ∈ D ⊓ M := ⟨hFND ▸ hwF, Op_le p M hwP⟩
      rw [hD1, Subgroup.mem_bot] at hwDM
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc u * z = (u * z * u⁻¹ * z⁻¹) * z * u := by group
        _ = z * u := by rw [hwDM, one_mul]
    have hcop : Nat.Coprime p (Nat.card ↥(zpowers z)) := by
      rw [Nat.card_zpowers, hC.orderOf_z]
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have hcen : X ⊔ (Op p M ⊓ centralizer (X : Set G)) ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
      have h1 : X ⊔ (Op p M ⊓ centralizer (X : Set G)) ≤ Cen z :=
        (sup_le (le_inf hXP Subgroup.le_normalizer)
          (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _))).trans hNPX
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_zpowers_eq_bot_iff.mpr h1)
    have := h118 G p hp (zpowers z) (Op p M) X hPp hcop (Subgroup.zpowers_le.mpr hzP)
      (Subgroup.zpowers_le.mpr (hXC (mem_Cen_self z))) hXP hcen
    exact hC.not_cen (this.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z))))
  ·
    obtain ⟨r, hr, hrne⟩ : ∃ r ∈ {q : ℕ | q.Prime ∧ q ∣ Nat.card ↥(Fm M)}, Op r (Fm N) ≠ ⊥ := by
      by_contra hno
      push Not at hno
      apply hU0
      rw [← hUdef]
      exact le_bot_iff.mp (iSup₂_le fun q hq => (hno q hq).le)
    obtain ⟨q, hq, hqne⟩ : ∃ q ∈ {q : ℕ | q.Prime ∧ ¬ q ∣ Nat.card ↥(Fm M)}, Op q (Fm N) ≠ ⊥ := by
      by_contra hno
      push Not at hno
      apply hD0
      rw [← hDdef]
      exact le_bot_iff.mp (iSup₂_le fun q hq => (hno q hq).le)
    have hrd : r ∣ Nat.card ↥(Fm N) := prime_dvd_card_of_Op_ne_bot hr.1 hrne
    have hqd : q ∣ Nat.card ↥(Fm N) := prime_dvd_card_of_Op_ne_bot hq.1 hqne
    rw [Op_Fm_eq hq.1 N] at hqne
    have hrq : r ≠ q := fun h => hq.2 (h ▸ hr.2)
    have hTwo : TwoPrimes (Fm N) := by
      have hsub : ({r, q} : Set ℕ) ⊆ piOf (Fm N) := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hr.1, hrd⟩
        · exact ⟨hq.1, hqd⟩
      have hfin : (piOf (Fm N)).Finite := by
        refine Set.Finite.subset (Set.finite_Iic (Nat.card ↥(Fm N))) fun x hx => ?_
        exact Nat.le_of_dvd Nat.card_pos hx.2
      unfold TwoPrimes
      calc 2 = ({r, q} : Set ℕ).ncard := (Set.ncard_pair hrq).symm
        _ ≤ (piOf (Fm N)).ncard := Set.ncard_le_ncard hsub hfin
    have hOqD : Op q N ≤ D := by
      rw [← hDdef, ← Op_Fm_eq hq.1 N]
      exact le_iSup₂_of_le q hq le_rfl
    have hOqM : ¬ Op q N ≤ Cen z := by
      intro hle
      have h1 : Op q N ≤ D ⊓ M := le_inf hOqD (hle.trans hC.cen_le)
      rw [hD1] at h1
      exact hqne (le_bot_iff.mp h1)
    have hadm : Adm z N q := ⟨hNmem, hTwo, hq.1, hOqM⟩
    have hinvq : Inverts z (Op q N) := fun x hx => hinvD x (hOqD hx)
    have hinvP : Inverts z (Op p M) := hC.choice.inv ⟨N, q, hadm, hinvq⟩
    have hPab := inverts_comm hinvP
    have hPN : Op p M ≤ N := by
      intro x hx
      refine hXN ?_
      refine mem_normalizer_of_forall fun y hy => ?_
      have h1 := hPab x hx y (hXP hy)
      have e : x * y * x⁻¹ = y := by rw [h1]; group
      rw [e]
      exact hy
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · exact h
    have hPD : Op p M ≤ centralizer (D : Set G) := by
      intro u hu
      have huN : u ∈ N := hPN hu
      have hcomm := commutator_centralizes_of_inverts hz2 hinvD (hND huN)
      have hsq : u * z * u⁻¹ * z⁻¹ = u ^ 2 := by
        have h1 : z * u⁻¹ * z⁻¹ = u := by
          have := hinvP (u⁻¹) ((Op p M).inv_mem hu)
          rw [inv_inv] at this
          exact this
        calc u * z * u⁻¹ * z⁻¹ = u * (z * u⁻¹ * z⁻¹) := by group
          _ = u ^ 2 := by rw [h1, pow_two]
      have hu2 : u ^ 2 ∈ centralizer (D : Set G) := by
        rw [← hsq, Subgroup.mem_centralizer_iff]
        intro d hd
        exact (hcomm d hd).symm
      obtain ⟨k, hk⟩ := hPp ⟨u, hu⟩
      have hu1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact mem_of_sq_mem (hpodd.pow) hu1 hu2
    have hP0 : Op p M ≠ ⊥ := fun h => hC.not_cen (h ▸ bot_le)
    have hnormP : normalizer ((Op p M : Subgroup G) : Set G) = M :=
      normalizer_eq_of_normalized hC hP0 (Op_le p M) (le_normalizer_Op p M)
    have hDM' : D ≤ M := by
      intro d hd
      have hdc : d ∈ centralizer ((Op p M : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (Subgroup.mem_centralizer_iff.mp (hPD hu) d hd).symm
      rw [← hnormP]
      exact Subgroup.centralizer_le_normalizer _ hdc
    apply hD0
    have h2 : D ≤ D ⊓ M := le_inf le_rfl hDM'
    rw [hD1] at h2
    exact le_bot_iff.mp h2

end P61

end CFSG.GH74.GLS.Stage2.Bender.Thm1
