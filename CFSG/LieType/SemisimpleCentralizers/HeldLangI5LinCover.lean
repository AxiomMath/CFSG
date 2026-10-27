module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCover
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Lin
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.Adapters.LinearCatalog
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldPieces
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms

theorem card_center_SL_le {K : Type} [Field K] [Finite K] {N : ℕ} [NeZero N] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin N) K)) ≤ Nat.gcd N (Nat.card K - 1) := by
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin N) (R := K)
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  rw [Nat.card_congr e.toEquiv, Fintype.card_fin]
  haveI : NeZero (Nat.gcd N (Nat.card K - 1)) :=
    ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N))).ne'⟩
  have hle : rootsOfUnity N K ≤ rootsOfUnity (Nat.gcd N (Nat.card K - 1)) K := by
    intro ζ hζ
    rw [mem_rootsOfUnity] at hζ ⊢
    have h2 : ζ ^ (Nat.card K - 1) = 1 := by
      have : ζ ^ Nat.card Kˣ = 1 := pow_card_eq_one'
      rwa [Nat.card_units] at this
    exact pow_gcd_eq_one.2 ⟨hζ, h2⟩
  calc Nat.card (rootsOfUnity N K) ≤ Nat.card (rootsOfUnity (Nat.gcd N (Nat.card K - 1)) K) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    _ ≤ Nat.gcd N (Nat.card K - 1) := card_rootsOfUnity K _

theorem nonempty_SL_mulEquiv_of_cover {K : Type} [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (hK2 : Nat.card K ≠ 2) (h4 : ¬(m = 2 ∧ Nat.card K = 4)) (h3 : ¬(m = 3 ∧ Nat.card K = 3))
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L)
    (πL : L →* Matrix.SpecialLinearGroup (Fin (m + 1)) K ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) K))
    (hL : Function.Surjective πL) (hcL : πL.ker ≤ Subgroup.center L)
    (hcard : Nat.card πL.ker = Nat.gcd (m + 1) (Nat.card K - 1)) :
    Nonempty (Matrix.SpecialLinearGroup (Fin (m + 1)) K ≃* L) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  refine nonempty_mulEquiv_of_central_covers (QuotientGroup.mk' _) πL (QuotientGroup.mk'_surjective _) hL hcL
    hperf (fun E _ _ π hπ hc => CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating hm
      (CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card hm hK2 h4 h3) hπ hc) ?_
  rw [QuotientGroup.ker_mk', hcard]
  exact card_center_SL_le

theorem i5CoverIsSL_of_ne (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.A n q).Valid)
    (h3n : 3 ∣ n + 1) (h3q : 3 ∣ q.card - 1) (hne : ¬(n = 2 ∧ q.card = 4))
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.A n q, hd⟩ L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q.card ∧
      Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin (n + 1)) K) := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hL.2.1
  let eL : L ⧸ Subgroup.center L ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd)
  have hcardK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hn : 2 ≤ n := by
    have := Nat.le_of_dvd (by omega) h3n
    omega
  have hq2 : 2 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact (q.prime_p.two_le).trans (Nat.le_self_pow q.exponent_pos.ne' q.p)
  let πL : L →* Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) (GaloisField q.p q.exponent)) :=
    eL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : πL.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eL.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcardK, ?_⟩
  obtain ⟨e⟩ := nonempty_SL_mulEquiv_of_cover (m := n) hn
    (by rw [hcardK]; omega)
    (by rw [hcardK]; exact hne)
    (by rw [hcardK]; omega)
    (Group.isPerfect_def.2 hL.1.1) πL
    (eL.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ le_rfl)
    (by
      rw [hker, hL.2.2.2, hcardK]
      rfl)
  exact ⟨e.symm⟩

theorem false_of_outer_three_A_small (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.A n q).Valid) (h3n : 3 ∣ n + 1) (hq8 : q.card < 8)
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.A n q, hd⟩ L)
    (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) : False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e0⟩ := hL.2.1
  let e' : L ⧸ Subgroup.center L ≃* projectiveSL (n + 1) (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL n q hd)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (n + 1) _)
  have hN : 3 ≤ n + 1 := Nat.le_of_dvd (by omega) h3n
  have hβbar3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom L) hβ3
    rwa [map_pow, map_one] at this
  have hβ'3 : MulAut.congr e' (onCenterQuotient β) ^ 3 = 1 := by
    rw [← map_pow, hβbar3, map_one]
  have hout' : MulAut.congr e' (onCenterQuotient β) ∉
      innAutDerived (projectiveSL (n + 1) (GaloisField q.p q.exponent)) :=
    fun h => hout ((mem_innAutDerived_congr e').1 h)
  obtain ⟨A, σ, -, hσ, -⟩ := exists_sigma_of_outer_three hN _ hβ'3 hout'
  have hdvd := orderOf_dvd_of_card q.prime_p q.exponent_pos
    (GaloisField.card q.p q.exponent q.exponent_pos.ne') σ
  rw [hσ] at hdvd
  have h3e : 3 ≤ q.exponent := Nat.le_of_dvd q.exponent_pos hdvd
  have h8 : 2 ^ 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact (Nat.pow_le_pow_left q.prime_p.two_le 3).trans (Nat.pow_le_pow_right q.prime_p.pos h3e)
  omega

end CFSG.LieType.SemisimpleCentralizers.HeldLang
