module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291R3ExRank
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SU3Basic
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossRank
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.Steinberg.CentralExt.UnitaryField
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.Universal.Unitary

section Transport

variable {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] {p : ℕ}

theorem pRank_centralizer_le_of_mulEquiv (hp : 1 < p) (e : A ≃* B) (x : A) :
    CFSG.Open.pRank p (centralizer ({e x} : Set B)) ≤
      CFSG.Open.pRank p (centralizer ({x} : Set A)) := by
  refine (CFSG.SectionRank.pRank_le_map hp e.symm.toMonoidHom e.symm.injective _).trans
    (CFSG.SectionRank.pRank_mono hp ?_)
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w * e x = e x * w := Subgroup.mem_centralizer_singleton_iff.1 hw
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply e.injective
  simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
  exact hw'

end Transport

section Scalars

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem eq_one_of_pow_eq_one_of_mk_eq_one (H : Subgroup (GL (Fin 3) K)) (h : H) {k : ℕ}
    (hh : h ^ p ^ k = 1)
    (hq : (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf H)) h = 1) : h = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range] at hq
  obtain ⟨c, hc⟩ := hq
  have h1 : ((h : GL (Fin 3) K)) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hh
    simpa using this
  rw [← hc, ← map_pow] at h1
  have h2 : c ^ p ^ k = 1 := by
    have h7 := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K) 0 0)) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h7
    exact Units.ext h7
  have h3 : ((c : K)) = 1 := by
    have h4 : ((c : K)) ^ p ^ k = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h2
      simpa using this
    have h5 : ((c : K) - 1) ^ p ^ k = 0 := by
      rw [sub_pow_char_pow, h4, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero) |>.mp h5)
  have h6 : c = 1 := Units.ext h3
  apply Subtype.ext
  rw [← hc, h6, map_one]
  rfl

end Scalars

section Field

theorem charP_of_card_eq_prime_pow {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) : CharP K p := by
  have := Fintype.ofFinite K
  obtain ⟨r, hchar⟩ := CharP.exists K
  have hr : r.Prime := CharP.char_is_prime K r
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card K r
  have h1 : r ∣ p ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self r n.pos.ne'
  have h2 : r = p := (Nat.prime_dvd_prime_iff_eq hr hp.out).1 (hr.dvd_of_dvd_pow h1)
  subst h2
  exact hchar

end Field

section L2

theorem three_le_pRank_centralizer_of_psl2GF {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) {S : Type}
    [Group S] [Finite S] (e : S ≃* CFSG.AGLEmbedding.PSL2GF p n)
    (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup S)) {x : S} (hx : x ^ p = 1) :
    3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) :=
  three_le_pRank_centralizer_of_sylow_abelian
    (fun P => isMulCommutative_sylow_of_mulEquiv e
      (fun R => (CFSG.AGLEmbedding.psl2GF_sylow p n hn R).1.1) P) h3 hx

end L2

section L3

variable {K : Type} [Field K] {p f : ℕ} [Fact p.Prime]

theorem uSL_zero_pow (b : K) (n : ℕ) : (uSL 0 b 0) ^ n = uSL 0 (n * b) 0 := by
  induction n with
  | zero => simp [uSL_zero]
  | succ n ih =>
    rw [pow_succ, ih, uSL_mul]
    congr 1 <;> push_cast <;> ring

theorem card_Zsl_eq : Nat.card (Zsl K) = Nat.card K := by
  let g : K → Zsl K := fun b => ⟨uSL 0 b 0, uSL_mem_Zsl b⟩
  have hg : Function.Bijective g := by
    refine ⟨fun a b h => ?_, fun z => ?_⟩
    · exact (uSL_injective (congrArg Subtype.val h)).2.1
    · obtain ⟨z, b, rfl⟩ := z
      exact ⟨b, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem three_le_pRank_centralizer_of_statedSL_three [Finite K] (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSL 3 K)) (h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S))
    {x : S} (hx : x ^ p = 1) : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : CharP K p := charP_of_card_eq_prime_pow hf hK
  let φ := specialLinearGroupEquivStatedSL 3 K
  let π : Matrix.SpecialLinearGroup (Fin 3) K →* StatedProj (StatedSL 3 K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))).comp φ.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hU : IsPGroup p (Usl K) := isPGroup_Usl hK
  have hidx : ¬ p ∣ (Usl K).index := not_dvd_index_Usl hK hf
  have hinj : ∀ u ∈ Usl K, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    exact φ.injective (by
      rw [map_one]
      exact eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 hπu)
  have hcard : Nat.card (Usl K) = p ^ (3 * f) := by
    rw [card_Usl, hK, ← pow_mul, mul_comm]
  have h4' : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 3 K))) := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  have h3f := pRank_top_le_of_heis π hπ hU hidx hinj hcard
  have hf2 : 2 ≤ f := by omega
  have hZ : p ^ 2 ≤ Nat.card (Zsl K) := by
    rw [card_Zsl_eq, hK]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
  have hZc : ∀ z ∈ Zsl K, ∀ u ∈ Usl K, z * u = u * z := by
    rintro _ ⟨β, rfl⟩ _ ⟨a, b, c, rfl⟩
    rw [uSL_mul, uSL_mul]
    congr 1 <;> ring
  have hZexp : ∀ z ∈ Zsl K, z ^ p = 1 := by
    rintro _ ⟨β, rfl⟩
    rw [uSL_zero_pow, CharP.cast_eq_zero, zero_mul, uSL_zero]
  have key := three_le_pRank_centralizer_of_heis π hπ hU hidx Zsl_le_Usl hZc hZexp hZ hinj
    (by omega) (x := e x) (by rw [← map_pow, hx, map_one])
  exact key.trans (pRank_centralizer_le_of_mulEquiv hp1 e x)

end L3

section U3

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]

theorem zSU_pow {σ : K ≃+* K} (H : SUInv σ) (β : traceZero σ) (n : ℕ) :
    (zSU H β) ^ n = zSU H (n • β) := by
  induction n with
  | zero => simp [zSU_zero]
  | succ n ih => rw [pow_succ, ih, zSU_mul, succ_nsmul]

theorem card_Zsu_eq {σ : K ≃+* K} (H : SUInv σ) : Nat.card (Zsu H) = Nat.card (traceZero σ) := by
  let g : traceZero σ → Zsu H := fun β => ⟨zSU H β, zSU_mem_Zsu H β⟩
  have hg : Function.Bijective g := by
    refine ⟨fun a b h => ?_, fun z => ?_⟩
    · have h1 : xSU H 0 * zSU H a = xSU H 0 * zSU H b := by
        rw [xSU_zero, one_mul, one_mul]
        exact congrArg Subtype.val h
      exact (xSU_mul_zSU_injective H h1).2
    · obtain ⟨z, β, rfl⟩ := z
      exact ⟨β, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective g hg)).symm

theorem three_le_pRank_centralizer_of_statedSU_three (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSU 3 (p ^ f) K)) (h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup S))
    {x : S} (hx : x ^ p = 1) : 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set S)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : CharP K p :=
    charP_of_card_eq_prime_pow (f := 2 * f) (by omega) (by rw [hK, pow_mul'])
  have H : SUInv (CFSG.LieType.BorelTits.unitaryInvolution K p f) := suInv_unitary hK hp2
  let φ := equivStatedSU hK 3
  let π : SU (CFSG.LieType.BorelTits.unitaryInvolution K p f) 3 →*
      StatedProj (StatedSU 3 (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))).comp
      φ.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp φ.surjective
  have hU : IsPGroup p (Usu H) := isPGroup_Usu hK H
  have hidx : ¬ p ∣ (Usu H).index := not_dvd_index_Usu hK hf H
  have hinj : ∀ u ∈ Usu H, π u = 1 → u = 1 := by
    intro u hu hπu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have h1 : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (φ u) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
    exact φ.injective (by
      rw [map_one]
      exact eq_one_of_pow_eq_one_of_mk_eq_one _ (φ u) h2 hπu)
  have hcard : Nat.card (Usu H) = p ^ (3 * f) := by
    rw [card_Usu_unitary hK H, ← pow_mul, mul_comm]
  have h4' : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 3 (p ^ f) K))) := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 e]
  have h3f := pRank_top_le_of_heis π hπ hU hidx hinj hcard
  have hf2 : 2 ≤ f := by omega
  have hZ : p ^ 2 ≤ Nat.card (Zsu H) := by
    rw [card_Zsu_eq, CFSG.LieType.Steinberg.card_traceZero hK]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hf2
  have hZc : ∀ z ∈ Zsu H, ∀ u ∈ Usu H, z * u = u * z := by
    rintro _ ⟨β, rfl⟩ u hu
    have := zSU_comm_of_mem_Usu H hu β
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hZexp : ∀ z ∈ Zsu H, z ^ p = 1 := by
    rintro _ ⟨β, rfl⟩
    have hβ : p • β = 0 := by
      apply Subtype.ext
      simp [nsmul_eq_mul]
    rw [zSU_pow, hβ, zSU_zero]
  have key := three_le_pRank_centralizer_of_heis π hπ hU hidx (Zsu_le_Usu H) hZc hZexp hZ hinj
    (by omega) (x := e x) (by rw [← map_pow, hx, map_one])
  exact key.trans (pRank_centralizer_le_of_mulEquiv hp1 e x)

end U3

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
