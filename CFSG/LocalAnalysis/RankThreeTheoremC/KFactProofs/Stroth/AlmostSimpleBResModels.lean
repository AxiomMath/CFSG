module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResFieldLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResFieldUnitary
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofL3
public import CFSG.RankThree.PartTwo.Sec20.KFactL3OddRank
public import CFSG.RankThree.OddKernel.SimpleQuotient
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.TwistedA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Open (StatedProj StatedSU StatedScalars)

section Transport

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]

theorem eq_bot_of_inverted_model {P : Type} [Group P] (eL : ↥L ≃* P) {d : X}
    (hP : ∀ t : P, t ^ 2 = 1 → t ≠ 1 →
      MulAut.congr eL (MulAut.conjNormal d) t = t →
      ∃ y : P, MulAut.congr eL (MulAut.conjNormal d) y = y ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧
        t * y * t⁻¹ = y⁻¹)
    {S : Subgroup X} (hS : S ≤ relPPrimeCore 3 (L ⊓ Subgroup.centralizer ({d} : Set X)))
    (hS2 : IsPGroup 2 S) : S = ⊥ := by
  classical
  have hSH : S ≤ L ⊓ Subgroup.centralizer ({d} : Set X) :=
    hS.trans (by unfold relPPrimeCore; exact sSup_le fun N hN => hN.1)
  refine eq_bot_of_forall_inverted Nat.prime_three (by norm_num) hSH hS hS2 ?_
  intro t ht ht2 ht1
  obtain ⟨htL, htC⟩ := Subgroup.mem_inf.1 ht
  set α : MulAut P := MulAut.congr eL (MulAut.conjNormal d) with hα
  have hαapp : ∀ u : ↥L, α (eL u) = eL (MulAut.conjNormal d u) := fun u => by
    simp [hα, MulAut.congr_apply]
  have hdt : d * t = t * d := Subgroup.mem_centralizer_iff.1 htC d (Set.mem_singleton d)
  set u₀ : ↥L := ⟨t, htL⟩ with hu₀
  have hu₀fix : MulAut.conjNormal d u₀ = u₀ := by
    refine Subtype.ext ?_
    rw [MulAut.conjNormal_apply]
    change d * t * d⁻¹ = t
    rw [hdt]
    group
  have hu₀2 : u₀ ^ 2 = 1 := Subtype.ext (by simpa [hu₀] using ht2)
  have hu₀1 : u₀ ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have ht'2 : eL u₀ ^ 2 = 1 := by rw [← map_pow, hu₀2, map_one]
  have ht'1 : eL u₀ ≠ 1 := fun h => hu₀1 (eL.injective (h.trans (map_one eL).symm))
  have hαt : α (eL u₀) = eL u₀ := by rw [hαapp, hu₀fix]
  obtain ⟨y', hy'fix, hy'3, hy'1, hy'inv⟩ := hP (eL u₀) ht'2 ht'1 hαt
  set u : ↥L := eL.symm y' with hu
  have hy'u : y' = eL u := (eL.apply_symm_apply y').symm
  have hufix : MulAut.conjNormal d u = u := by
    apply eL.injective
    rw [← hαapp, ← hy'u]
    exact hy'fix
  refine ⟨(u : X), Subgroup.mem_inf.2 ⟨u.2, ?_⟩, ?_, ?_, ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg Subtype.val hufix
    rw [MulAut.conjNormal_apply] at this
    calc h * (u : X) = h * u * h⁻¹ * h := by group
      _ = u * h := by rw [this]
  · have : u ^ 3 = 1 := by
      apply eL.injective
      rw [map_pow, ← hy'u, hy'3, map_one]
    exact congrArg Subtype.val this
  · intro h
    apply hy'1
    have : u = 1 := Subtype.ext h
    rw [hy'u, this, map_one]
  · have h1 : u₀ * u * u₀⁻¹ = u⁻¹ := by
      apply eL.injective
      rw [map_mul, map_mul, map_inv, map_inv, ← hy'u]
      exact hy'inv
    exact congrArg Subtype.val h1

end Transport

section Models

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]

theorem conjNormal_injective_of_centralizer_eq_bot'
    (hC : Subgroup.centralizer (L : Set X) = ⊥) :
    Function.Injective (MulAut.conjNormal : X →* MulAut ↥L) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have : x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (DFunLike.congr_fun hx ⟨l, hl⟩)
    rw [MulAut.conjNormal_apply] at this
    change x * l * x⁻¹ = l at this
    calc l * x = x * l * x⁻¹ * x := by rw [this]
      _ = x * l := by group
  rw [hC] at this
  exact this

theorem exists_mem_map_conj {P : Type} [Group P] (eL : ↥L ≃* P) (y : P) :
    ∃ l ∈ L, ((MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal) l = MulAut.conj y := by
  refine ⟨((eL.symm y : ↥L) : X), (eL.symm y).2, ?_⟩
  ext z
  change MulAut.congr eL (MulAut.conjNormal ((eL.symm y : ↥L) : X)) z = (MulAut.conj y) z
  rw [MulAut.conjNormal_val, MulAut.congr_apply]
  simp [MulAut.conj_apply]

theorem eq_bot_of_linear_model {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 X) (eL : ↥L ≃* projectiveSL 3 K) {d : X}
    (hd3 : d ^ 3 = 1) {S : Subgroup X}
    (hS : S ≤ relPPrimeCore 3 (L ⊓ Subgroup.centralizer ({d} : Set X))) (hS2 : IsPGroup 2 S) :
    S = ⊥ := by
  classical
  set ψ : X →* MulAut (projectiveSL 3 K) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal with hψdef
  have hψ : Function.Injective ψ :=
    (MulAut.congr eL).injective.comp (conjNormal_injective_of_centralizer_eq_bot' hC)
  have hL : ∀ y : projectiveSL 3 K, ∃ l ∈ L, ψ l = MulAut.conj y := exists_mem_map_conj eL
  have hmem : ψ d ∈ linearAutGroup 3 K := linear_three_mem_linearAut hω hrk ψ hψ L hL hd3
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.1 hmem
  have hAψ : MulAut.congr eL (MulAut.conjNormal d) = conjAut 3 K A := hA.symm
  have hA3 : conjAut 3 K A ^ 3 = 1 := by rw [hA, ← map_pow, hd3, map_one]
  refine eq_bot_of_inverted_model eL (fun t ht2 ht1 hAt => ?_) hS hS2
  rw [hAψ] at hAt ⊢
  exact exists_inverted_three_linear A hA3 ht2 ht1 hAt

theorem conj_injective_of_centralizer_eq_bot' (hC : Subgroup.centralizer (L : Set X) = ⊥)
    {P : Type} [Group P] (e : ↥L ≃* P) : Function.Injective (MulAut.conj : P →* MulAut P) := by
  intro a b hab
  obtain ⟨c, hcdef⟩ : ∃ c : P, c = b⁻¹ * a := ⟨_, rfl⟩
  have hc : ∀ z : P, c * z = z * c := by
    intro z
    have h1 := congrArg (fun φ : MulAut P => φ z) hab
    simp only [MulAut.conj_apply] at h1
    rw [hcdef]
    calc b⁻¹ * a * z = b⁻¹ * (a * z * a⁻¹) * a := by group
      _ = b⁻¹ * (b * z * b⁻¹) * a := by rw [h1]
      _ = z * (b⁻¹ * a) := by group
  have hl : ((e.symm c : ↥L) : X) ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 := hc (e ⟨g, hg⟩)
    have h3 : e.symm c * ⟨g, hg⟩ = ⟨g, hg⟩ * e.symm c := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h2
    exact (congrArg Subtype.val h3).symm
  rw [hC, Subgroup.mem_bot] at hl
  have h4 : e.symm c = 1 := Subtype.ext hl
  have h5 : c = 1 := e.symm.injective (by rw [h4, map_one])
  rw [hcdef] at h5
  exact (inv_mul_eq_one.1 h5).symm

theorem eq_bot_of_unitary_model {f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (hf : f ≠ 1) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hωb : hU.bar ω * ω = 1)
    (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hrk : CFSG.LieType.SeitzGeneration.RankLE2 3 X) (eL : ↥L ≃* primeFormP hU (idC K)) {d : X}
    (hd3 : d ^ 3 = 1) {S : Subgroup X}
    (hS : S ≤ relPPrimeCore 3 (L ⊓ Subgroup.centralizer ({d} : Set X))) (hS2 : IsPGroup 2 S) :
    S = ⊥ := by
  classical
  set ψ : X →* MulAut (primeFormP hU (idC K)) :=
    (MulAut.congr eL).toMonoidHom.comp MulAut.conjNormal with hψdef
  have hψ : Function.Injective ψ :=
    (MulAut.congr eL).injective.comp (conjNormal_injective_of_centralizer_eq_bot' hC)
  have hL : ∀ y : primeFormP hU (idC K), ∃ l ∈ L, ψ l = MulAut.conj y := exists_mem_map_conj eL
  have hconj := conj_injective_of_centralizer_eq_bot' hC eL
  have hmem : ψ d ∈ primeFormD hU (idC K) :=
    unitary_three_mem_primeFormD hU hf hω hωb hconj hrk ψ hψ L hL hd3
  obtain ⟨A, hA⟩ := hmem
  have hAψ : MulAut.congr eL (MulAut.conjNormal d) = primeFormConjHom hU (idC K) A := hA.symm
  have hA3 : primeFormConjHom hU (idC K) A ^ 3 = 1 := by rw [hA, ← map_pow, hd3, map_one]
  refine eq_bot_of_inverted_model eL (fun t ht2 ht1 hAt => ?_) hS hS2
  rw [hAψ] at hAt ⊢
  exact exists_inverted_three_unitary hU hf A hA3 ht2 ht1 hAt

end Models

section Rank

theorem exists_cube_root_of_unity {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3'
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h => by
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  refine ⟨(u : K), ?_, ?_, ?_⟩
  · have := congrArg (fun v : Kˣ => (v : K)) hu3
    simpa using this
  · intro h
    exact hu1 (Units.ext h)
  · have h1 : (u : K) ^ 3 = 1 := by
      have := congrArg (fun v : Kˣ => (v : K)) hu3
      simpa using this
    have h2 : (u : K) ≠ 1 := fun h => hu1 (Units.ext h)
    have : ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h2)

theorem exists_omega_of_pRank_linear {X : Type} [Group X] [Finite X] {L : Subgroup X} {f : ℕ}
    (hf : 1 ≤ f) (eL : ↥L ≃* projectiveSL 3 (GaloisField 2 f))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) :
    ∃ ω : GaloisField 2 f, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hodd : Odd f
  · exfalso
    have h := CFSG.RankThree.PartTwo.Sec20.kFactL3OddThreeRank f hodd ↥L
      ⟨eL.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3
        (GaloisField 2 f)).symm⟩
    omega
  · obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.1 hodd
    have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    have h3 : 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
      rw [hK, hk, ← two_mul, pow_mul]
      have h4 : (1 : ℕ) ≡ 4 ^ k [MOD 3] := by
        have := Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide)
        simpa using this.symm
      have := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).1 h4
      simpa using this
    obtain ⟨ω, -, -, hω⟩ := exists_cube_root_of_unity h3
    exact ⟨ω, hω⟩

theorem statedScalars_subgroupOf_statedSU_eq_bot' {p e : ℕ} {K : Type} [Field K]
    (hU : UnitaryFieldData p e K) (h3 : ¬ 3 ∣ p ^ e + 1) :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ e) K) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgs
  rw [Subgroup.mem_subgroupOf] at hgs
  obtain ⟨l, hl⟩ := hgs
  have hl' : Matrix.GeneralLinearGroup.scalar (Fin 3) l ∈ StatedSU 3 (p ^ e) K := by
    change Matrix.GeneralLinearGroup.scalar (Fin 3) l = g at hl
    rw [hl]
    exact hg
  obtain ⟨hdet, hunit⟩ := (CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hU).mp hl'
  have hl3 : (l : K) ^ 3 = 1 := by
    have : (Matrix.scalar (Fin 3) (l : K)).det = 1 := by simpa using hdet
    simpa [Matrix.det_smul] using this
  have hlq : (l : K) ^ (p ^ e + 1) = 1 := by
    have h00 := congrFun (congrFun hunit 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, UnitaryFieldData.bar_apply] at h00
    rw [pow_succ]
    exact h00
  have hpow : ∀ k : ℕ, (l : K) ^ k = (l : K) ^ (k % 3) := fun k => by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, hl3, one_pow, one_mul]
  have hl1 : (l : K) = 1 := by
    rw [hpow] at hlq
    rcases (show (p ^ e + 1) % 3 = 1 ∨ (p ^ e + 1) % 3 = 2 by omega) with h | h
    · rw [h, pow_one] at hlq
      exact hlq
    · rw [h] at hlq
      have h32 : (l : K) ^ 3 = (l : K) ^ 2 * l := by ring
      rw [hl3, hlq, one_mul] at h32
      exact h32.symm
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change g = 1
  have hl2 : Matrix.GeneralLinearGroup.scalar (Fin 3) l = g := hl
  rw [← hl2, show l = 1 from Units.ext hl1, map_one]

theorem exists_omega_of_pRank_unitary {X : Type} [Group X] [Finite X] {L : Subgroup X} {f : ℕ}
    {K : Type} [Field K] (hU : UnitaryFieldData 2 f K)
    (eS : ↥L ≃* StatedProj (StatedSU 3 (2 ^ f) K))
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) :
    ∃ ω : K, ω ^ 2 + ω + 1 = 0 ∧ hU.bar ω * ω = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := hU.charP
  haveI := hU.finite
  have hq3 : 2 ^ f % 3 = 1 ∨ 2 ^ f % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ f := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h)
      omega
    omega
  rcases hq3 with hq | hq
  · exfalso
    have hbot := statedScalars_subgroupOf_statedSU_eq_bot' hU (by omega)
    let e2 : StatedProj (StatedSU 3 (2 ^ f) K) ≃* StatedSU 3 (2 ^ f) K :=
      (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
    have hle := CFSG.RankThree.OddKernel.pRank_le_of_injective (p := 3) (by norm_num)
      (eS.trans e2).toMonoidHom (eS.trans e2).injective
    have h1 := CFSG.RankThree.PartTwo.Sec4.Res417Four.pRank_statedSU_three_le_one hU hq
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hle
    omega
  · have hK : Nat.card K = 2 ^ (2 * f) := hU.card
    have h3 : 3 ∣ Nat.card K - 1 := by
      rw [hK, pow_mul']
      have h4 : (1 : ℕ) ≡ (2 ^ f) ^ 2 [MOD 3] := by
        have h2f : 2 ^ f ≡ 2 [MOD 3] := by simpa [Nat.ModEq] using hq
        have := Nat.ModEq.pow 2 h2f
        exact (show 1 ≡ 2 ^ 2 [MOD 3] by decide).trans this.symm
      have := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by positivity))).1 h4
      simpa using this
    obtain ⟨ω, hω3, -, hω⟩ := exists_cube_root_of_unity h3
    refine ⟨ω, hω, ?_⟩
    have hb : hU.bar ω = ω ^ 2 := by
      rw [UnitaryFieldData.bar_apply]
      have : ω ^ (2 ^ f) = ω ^ (2 ^ f % 3) := by
        conv_lhs => rw [← Nat.div_add_mod (2 ^ f) 3, pow_add, pow_mul, hω3, one_pow, one_mul]
      rw [this, hq]
    rw [hb]
    calc ω ^ 2 * ω = ω ^ 3 := by ring
      _ = 1 := hω3

end Rank

section Assembly

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [L.Normal]

theorem eq_bot_of_lThreeTwo (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hE : ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 2)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2)
    (hL3 : ∃ q : TauCeti.PrimePower, q.p = 2 ∧
      (CFSG.RankThree.PartOne.Census3.IsoLie ↥L (.A 2 q) ∨
        CFSG.RankThree.PartOne.Census3.IsoLie ↥L (.twistedA 2 q)))
    {d : X} (hd3 : d ^ 3 = 1) {S : Subgroup X}
    (hS : S ≤ relPPrimeCore 3 (L ⊓ Subgroup.centralizer ({d} : Set X))) (hS2 : IsPGroup 2 S) :
    S = ⊥ := by
  classical
  have hE' : CFSG.LieType.SeitzGeneration.RankLE2 3 X := hE
  obtain ⟨⟨p, ex, hp, hex⟩, hq2, h | h⟩ := hL3
  ·
    obtain ⟨hv, ⟨e⟩⟩ := h
    have hp2 : p = 2 := hq2
    subst hp2
    haveI : Fact (Nat.Prime 2) := ⟨hp⟩
    let eL : ↥L ≃* projectiveSL 3 (GaloisField 2 ex) :=
      e.trans ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2
        (⟨2, ex, hp, hex⟩ : TauCeti.PrimePower) hv).trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _))
    obtain ⟨ω, hω⟩ := exists_omega_of_pRank_linear hex eL hrk
    exact eq_bot_of_linear_model hω hC hE' eL hd3 hS hS2
  ·
    obtain ⟨hv, ⟨e⟩⟩ := h
    have hp2 : p = 2 := hq2
    subst hp2
    have hmodel := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2
      (⟨2, ex, hp, hex⟩ : TauCeti.PrimePower) hv e
    obtain ⟨K, _, hU, ⟨eS⟩, ⟨eP⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.exists_primeFormP_mulEquiv_of_statedModel
        hmodel
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hf : ex ≠ 1 := by
      rintro rfl
      have h3 := hrange.2 rfl
      simp [TauCeti.PrimePower.card_def] at h3
    obtain ⟨ω, hω, hωb⟩ := exists_omega_of_pRank_unitary hU eS hrk
    exact eq_bot_of_unitary_model hU hf hω hωb hC hE' eP hd3 hS hS2

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
