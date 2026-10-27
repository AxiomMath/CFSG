module

public import CFSG.ClassicalInvolution.Asc77.AscT3RStd
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10C

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section TX

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}



theorem Std20.r10b_odd_f (d : Std20 p f K K' J S R R' W V z t) (h8 : Nat.card R = 8) :
    Odd f := by
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.late_mem_K
  obtain ⟨eK⟩ := hz₀.nonempty_equiv
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 SL(2, GaloisField p f)))
  have hcard : Nat.card R = Nat.card Q := natCard_isSylow2In_eq_natCard_sylow (e := eK) Q d.hR
  have h1 : 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2 = 2 ^ 3 := by
    rw [← Sylow.card_eq_multiplicity Q, ← hcard, h8]
    norm_num
  have h2 : (Nat.card SL(2, GaloisField p f)).factorization 2 = 3 :=
    Nat.pow_right_injective (le_refl 2) h1
  rw [card_sl2_eq, hFcard] at h2
  exact odd_of_factorization_two_eq_three ((Fact.out : p.Prime).odd_of_ne_two hp) h2


theorem Std20.r10b_TX (d : Std20 p f K K' J S R R' W V z t) (c8 : Concl20_8 S K' R)
    (h8 : Nat.card R = 8) : ∀ g ∈ (S : Subgroup G), conjSub g K = K →
      g ∈ sec20X (CoreAssembly.conjClass K) z K K' := by
  classical
  intro g hg hgK
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hFodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField hp hq
  have hKop : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.one_le_iff_ne_zero.mpr hf, hFcard⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hFcard]
    omega
  obtain ⟨z₀, hz₀⟩ := d.hyp.classical K d.late_mem_K
  obtain ⟨eK⟩ := hz₀.nonempty_equiv
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  obtain ⟨v, hv, hord, hvN⟩ := d.r9_vdata
  obtain ⟨hεv, hρv⟩ := d.r9_eps_v c8 hu huK eK hFodd hKop h4 hv hord hvN
  have hvV : v ∈ V := hv ▸ Subgroup.mem_zpowers v
  have hV2 : IsPGroup 2 V := d.hyp.isPGroup_of_mem_USet hp d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  set T : Subgroup G := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hT
  have hT2 : IsPGroup 2 ↥T := S.isPGroup'.to_le inf_le_left
  have hTN : T ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hRT : R ≤ T := le_inf d.hRS (d.hR.1.trans Subgroup.le_normalizer)
  have hVT : V ≤ T := le_inf d.hVS (d.hVW.trans d.late_W_le_N_K)
  have hvT : v ∈ T := hVT hvV
  have hRp : ∀ y ∈ T, phiG K eK y = 1 → y ∈ R' := fun y hyT hy1 =>
    d.r9_cStar_S c8 hu huK hyT.1 ((phiG_eq_one_iff hyT.2).mp hy1)
  have hRR'V_le_X : R ⊔ R' ⊔ V ≤ sec20X (CoreAssembly.conjClass K) z K K' :=
    sup_le (sup_le (d.hR.1.trans le_sec20X_left) (d.hR'.1.trans le_sec20X_right)) tw.hVX
  have hgT : g ∈ T := ⟨hg, mem_normalizer_iff_conjSub_eq.mpr hgK⟩
  have hgN : g ∈ Subgroup.normalizer (K : Set G) := hTN hgT
  obtain ⟨n, hn⟩ := S.isPGroup' ⟨g, hg⟩
  have hgn : g ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 : (psi hKop K eK v g) ^ 2 ^ n = 1 := by
    rw [← psi_pow hρv hgN, hgn, psi_one]
  have hcyc : Nat.card (GaloisField p f ≃+* GaloisField p f) = f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic (Fact.out : p.Prime)
      (GaloisField p f) hFcard).1
  have hfin : Finite (GaloisField p f ≃+* GaloisField p f) := finite_ringAut _
  have h2 : (psi hKop K eK v g) ^ f = 1 := by
    have := pow_card_eq_one' (G := GaloisField p f ≃+* GaloisField p f) (x := psi hKop K eK v g)
    rwa [hcyc] at this
  have hcop : Nat.Coprime (2 ^ n) f :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr (d.r10b_odd_f h8))
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hcop] at h3
  have hψ1 : psi hKop K eK v g = 1 := by simpa using h3
  exact hRR'V_le_X (mem_of_psi_eq_one hFodd h4 hT2 hTN hRT d.hR hRp hvV hvT hεv hgT hψ1)

end TX

end CFSG.ClassicalInvolution.Asc77.T3CII
