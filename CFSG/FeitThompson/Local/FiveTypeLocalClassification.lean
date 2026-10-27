module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.OddOrder.ExponentComplementCyclicHallAction
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
import CFSG.FeitThompson.OddOrder.SigmaHallSubgroupNormalizer
import CFSG.FeitThompson.OddOrder.InvariantHallComplement
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Representations.AbelianizationLayerUniformCoherent
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace Proofs

open Subgroup Pointwise CFSG.FeitThompson

universe u

variable {X : Type*} [Group X] [Finite X]

theorem coprime_natCard_index_of_isHallPiSubgroup {π : Set ℕ} {A B : Subgroup X}
    (hA : IsHallPiSubgroup π A) (hB : IsHallPiSubgroup π B) :
    Nat.Coprime (Nat.card A) B.index := by
  by_contra hc
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact hB.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨hp, hp2, Subgroup.index_ne_zero_of_finite⟩)
    (isPiSubgroup_iff.1 hA.isPiSubgroup p (Nat.mem_primeFactors.2 ⟨hp, hp1, Nat.card_pos.ne'⟩))

theorem natCard_eq_of_isHallPiSubgroup {π : Set ℕ} {A B : Subgroup X}
    (hA : IsHallPiSubgroup π A) (hB : IsHallPiSubgroup π B) : Nat.card A = Nat.card B := by
  have key : ∀ {C D : Subgroup X}, IsHallPiSubgroup π C → IsHallPiSubgroup π D →
      Nat.card C ∣ Nat.card D := fun {C D} hC hD =>
    (coprime_natCard_index_of_isHallPiSubgroup hC hD).dvd_of_dvd_mul_right
      (by rw [Subgroup.card_mul_index]; exact Subgroup.card_subgroup_dvd_card C)
  exact Nat.dvd_antisymm (key hA hB) (key hB hA)

variable {G : Type*} [Group G] [Finite G]

theorem natCard_eq_of_isLocalKappaSetup {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) :
    Nat.card ↥M = Nat.card ↥(sigmaCore M) * (Nat.card ↥U * Nat.card ↥K) := by
  rw [h.semidirect_M.natCard_eq_mul, h.semidirect_UK.natCard_eq_mul]

theorem natCard_K_eq_of_isLocalKappaSetup {M K U K' U' : Subgroup G}
    (h : IsLocalKappaSetup M K U) (h' : IsLocalKappaSetup M K' U') :
    Nat.card ↥K = Nat.card ↥K' := by
  have hK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥(K'.subgroupOf M) :=
    natCard_eq_of_isHallPiSubgroup h.hall_K h'.hall_K
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le_M_K).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h'.le_M_K).toEquiv] at hK

theorem natCard_U_eq_of_isLocalKappaSetup {M K U K' U' : Subgroup G}
    (h : IsLocalKappaSetup M K U) (h' : IsLocalKappaSetup M K' U') :
    Nat.card ↥U = Nat.card ↥U' := by
  have hKK' := natCard_K_eq_of_isLocalKappaSetup h h'
  have hcard := (natCard_eq_of_isLocalKappaSetup h).symm.trans
    (natCard_eq_of_isLocalKappaSetup h')
  rw [hKK'] at hcard
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard)

omit [Finite G] in
theorem eq_bot_iff_natCard_eq_one {A : Subgroup G} : A = ⊥ ↔ Nat.card ↥A = 1 :=
  ⟨fun h => by rw [h, Subgroup.card_bot], Subgroup.card_eq_one.1⟩

theorem eq_bot_K_iff_of_isLocalKappaSetup {M K U K' U' : Subgroup G}
    (h : IsLocalKappaSetup M K U) (h' : IsLocalKappaSetup M K' U') : K = ⊥ ↔ K' = ⊥ := by
  rw [eq_bot_iff_natCard_eq_one, eq_bot_iff_natCard_eq_one,
    natCard_K_eq_of_isLocalKappaSetup h h']

theorem eq_bot_U_iff_of_isLocalKappaSetup {M K U K' U' : Subgroup G}
    (h : IsLocalKappaSetup M K U) (h' : IsLocalKappaSetup M K' U') : U = ⊥ ↔ U' = ⊥ := by
  rw [eq_bot_iff_natCard_eq_one, eq_bot_iff_natCard_eq_one,
    natCard_U_eq_of_isLocalKappaSetup h h']

omit [Finite G] in
theorem inf_subgroupOf (A B Y : Subgroup G) :
    (A ⊓ B).subgroupOf Y = A.subgroupOf Y ⊓ B.subgroupOf Y := by
  ext z; simp [Subgroup.mem_subgroupOf]

omit [Finite G] in
theorem subgroupOf_ne_bot {A B : Subgroup G} (hAB : A ≤ B) (hA : A ≠ ⊥) : A.subgroupOf B ≠ ⊥ := by
  rw [Ne, Subgroup.subgroupOf_eq_bot]
  exact fun h => hA (disjoint_self.1 (h.mono_right hAB))

omit [Finite G] in
theorem exponent_subgroupOf {A B : Subgroup G} (hAB : A ≤ B) :
    Monoid.exponent ↥(A.subgroupOf B) = Monoid.exponent ↥A :=
  Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAB)

omit [Finite G] in
theorem centralizer_singleton_subgroupOf (Y : Subgroup G) {y : G} (hy : y ∈ Y) :
    (Subgroup.centralizer ({y} : Set G)).subgroupOf Y
      = Subgroup.centralizer ({(⟨y, hy⟩ : ↥Y)} : Set ↥Y) := by
  ext z
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, Subtype.ext_iff, Subgroup.coe_mul]
  exact ⟨fun h w hw => hw ▸ h, fun h => h ⟨y, hy⟩ rfl⟩

omit [Finite G] in
theorem mem_normalizer_of_conj_smul_eq {E : Subgroup G} {k : G} (h : MulAut.conj k • E = E) :
    k ∈ normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h ▸ ⟨x, hx, rfl⟩, fun hx => ?_⟩
  rw [← h] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  exact (mul_left_cancel (mul_right_cancel (hyx : k * y * k⁻¹ = k * x * k⁻¹)) : y = x) ▸ hy

omit [Finite G] in
theorem map_subtype_conj_smul {Y : Subgroup G} (S : Subgroup ↥Y) (r : ↥Y) :
    ((MulAut.conj r • S : Subgroup ↥Y)).map Y.subtype
      = MulAut.conj (r : G) • (S.map Y.subtype) := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨(z : G), ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨r * z * r⁻¹, ⟨z, hz, rfl⟩, by simp⟩

omit [Finite G] in
private theorem normal_subgroupOf_subgroupOf {D E E₁ : Subgroup G} (hE₁E : E₁ ≤ E)
    (h : (E₁.subgroupOf E).Normal) :
    ((E₁.subgroupOf D).subgroupOf (E.subgroupOf D)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  exact h.conj_mem (⟨((n : ↥D) : G), hE₁E hn⟩ : ↥E) hn ⟨((g : ↥D) : G), g.2⟩

omit [Finite G] in
private theorem subgroupOf_hallCoreIn (M : Subgroup G) : (hallCoreIn M).subgroupOf M = hallCore ↥M :=
  Subgroup.comap_map_eq_self_of_injective M.subtype_injective _

omit [Finite G] in
theorem hallCoreIn_bot : hallCoreIn (⊥ : Subgroup G) = ⊥ := by
  rw [hallCoreIn_eq, Subgroup.eq_bot_of_subsingleton (hallCore ↥(⊥ : Subgroup G)),
    Subgroup.map_bot]

noncomputable def hallCoreMulEquiv (M : Subgroup G) : ↥(hallCore ↥M) ≃* ↥(hallCoreIn M) :=
  (hallCore ↥M).equivMapOfInjective M.subtype M.subtype_injective

omit [Finite G] in
theorem natCard_hallCoreIn (M : Subgroup G) :
    Nat.card ↥(hallCoreIn M) = Nat.card ↥(hallCore ↥M) :=
  (Nat.card_congr (hallCoreMulEquiv M).toEquiv).symm

omit [Finite G] in
theorem isMulCommutative_hallCoreIn_iff (M : Subgroup G) :
    IsMulCommutative ↥(hallCoreIn M) ↔ IsMulCommutative ↥(hallCore ↥M) :=
  ⟨fun _ => isMulCommutative_of_mulEquiv (hallCoreMulEquiv M),
   fun _ => isMulCommutative_of_mulEquiv (hallCoreMulEquiv M).symm⟩

omit [Finite G] in
theorem isCyclic_hallCoreIn_iff (M : Subgroup G) :
    IsCyclic ↥(hallCoreIn M) ↔ IsCyclic ↥(hallCore ↥M) := ((hallCoreMulEquiv M).isCyclic).symm

theorem maxElementaryAbelianPRank_hallCoreIn (M : Subgroup G) :
    maxElementaryAbelianPRank ↥(hallCoreIn M) = maxElementaryAbelianPRank ↥(hallCore ↥M) :=
  maxElementaryAbelianPRank_eq_of_mulEquiv (hallCoreMulEquiv M).symm

theorem map_pComplCore_hallCoreMulEquiv (M : Subgroup G) (r : ℕ) :
    (pComplCore r ↥(hallCore ↥M)).map (hallCoreMulEquiv M : _ →* _)
      = pComplCore r ↥(hallCoreIn M) := by
  rw [pComplCore_eq_piCore, pComplCore_eq_piCore]; exact map_piCore_of_mulEquiv _ _

noncomputable def pComplCoreMulEquiv (M : Subgroup G) (r : ℕ) :
    ↥(pComplCore r ↥(hallCore ↥M)) ≃* ↥(pComplCore r ↥(hallCoreIn M)) :=
  ((hallCoreMulEquiv M).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_pComplCore_hallCoreMulEquiv M r))

noncomputable def pCoreMulEquiv (M : Subgroup G) (r : ℕ) :
    ↥(pCore r ↥(hallCore ↥M)) ≃* ↥(pCore r ↥(hallCoreIn M)) :=
  ((hallCoreMulEquiv M).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_pCore_of_mulEquiv r (hallCoreMulEquiv M)))

theorem isCyclic_pComplCoreIn_iff (M : Subgroup G) (r : ℕ) :
    IsCyclic ↥(CFSG.FeitThompson.pComplCoreIn r (hallCoreIn M)) ↔
      IsCyclic ↥(pComplCore r ↥(hallCore ↥M)) := by
  rw [CFSG.FeitThompson.pComplCoreIn_eq]
  exact (((pComplCoreMulEquiv M r).trans
    ((pComplCore r ↥(hallCoreIn M)).equivMapOfInjective _
      (hallCoreIn M).subtype_injective)).isCyclic).symm

theorem natCard_pCoreIn_hallCoreIn (M : Subgroup G) (r : ℕ) :
    Nat.card ↥(CFSG.FeitThompson.pCoreIn r (hallCoreIn M))
      = Nat.card ↥(pCore r ↥(hallCore ↥M)) := by
  rw [CFSG.FeitThompson.pCoreIn_eq,
    Subgroup.card_map_of_injective (hallCoreIn M).subtype_injective]
  exact (Nat.card_congr (pCoreMulEquiv M r).toEquiv).symm

theorem isFrobeniusType_subgroupOf {D H E : Subgroup G} (hHD : H ≤ D) (hED : E ≤ D)
    (hHhall : H.subgroupOf D = hallCore ↥D) (hHbot : H ≠ ⊥) (hHD' : H ≠ D)
    (hsup : H ⊔ E = D) (hinf : H ⊓ E = ⊥)
    {E₁ : Subgroup G} (hE₁E : E₁ ≤ E) (hE₁norm : (E₁.subgroupOf E).Normal)
    (hE₁comm : IsMulCommutative ↥E₁)
    (hE₁cent : ∀ h ∈ H, h ≠ 1 → E ⊓ centralizer ({h} : Set G) ≤ E₁)
    {E₀ : Subgroup G} (hE₀E : E₀ ≤ E) (hexp : Monoid.exponent ↥E₀ = Monoid.exponent ↥E)
    (hE₀free : ∀ x ∈ E₀, x ≠ 1 → H ⊓ centralizer ({x} : Set G) = ⊥) :
    IsFrobeniusType ↥D (E.subgroupOf D) := by
  have hHnorm : (H.subgroupOf D).Normal := hHhall ▸ hallCore_normal
  constructor
  case bot_lt_hallCore =>
    rw [← hHhall, bot_lt_iff_ne_bot, Ne, Subgroup.subgroupOf_eq_bot]
    exact fun h => hHbot (disjoint_self.1 (h.mono_right hHD))
  case hallCore_lt_top =>
    rw [← hHhall, lt_top_iff_ne_top]
    intro hc
    exact hHD' (le_antisymm hHD fun x hx =>
      (hc ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥D) : (⟨x, hx⟩ : ↥D) ∈ H.subgroupOf D))
  case isComplement' =>
    rw [← hHhall]
    refine (isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_).symm
    · rw [← Subgroup.subgroupOf_sup hHD hED, hsup, Subgroup.subgroupOf_self]
    · rw [← inf_subgroupOf, hinf, Subgroup.bot_subgroupOf]
  case exists_abelian_normal =>
    refine ⟨E₁.subgroupOf D, Subgroup.subgroupOf_mono D hE₁E,
      normal_subgroupOf_subgroupOf hE₁E hE₁norm,
      isMulCommutative_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hE₁E.trans hED)), ?_⟩
    intro h hh hh1
    rw [← hHhall, Subgroup.mem_subgroupOf] at hh
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxc : (x : G) ∈ centralizer ({(h : G)} : Set G) := by
      have h2 := hx.2
      rw [Subgroup.mem_centralizer_iff] at h2 ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact congrArg Subtype.val (h2 (h : ↥D) rfl)
    exact hE₁cent (h : G) hh (fun hc => hh1 (Subtype.ext hc)) ⟨hx.1, hxc⟩
  case exists_exponent_eq =>
    refine ⟨E₀.subgroupOf D, Subgroup.subgroupOf_mono D hE₀E, ?_, ?_⟩
    · rw [exponent_subgroupOf (hE₀E.trans hED), exponent_subgroupOf hED]; exact hexp
    · intro e he he1
      rw [Subgroup.mem_subgroupOf] at he
      rw [← hHhall, ← centralizer_singleton_subgroupOf D e.2, ← inf_subgroupOf,
        hE₀free (e : G) he (fun hc => he1 (Subtype.ext hc)), Subgroup.bot_subgroupOf]

theorem isWitnessedPConfiguration_of_data {M K E W₂ : Subgroup G}
    (hMtop : M < ⊤) (hKbot : K ≠ ⊥) (hKcyc : IsCyclic ↥K)
    (hKhall : (Nat.card ↥K).Coprime (K.relIndex M))
    (hsupK : (⁅M, M⁆ : Subgroup G) ⊔ K = M)
    (hdisjK : Disjoint (⁅M, M⁆ : Subgroup G) K)
    (hEnil : Group.IsNilpotent ↥E) (hEMM : E ≤ (⁅M, M⁆ : Subgroup G))
    (hKnormE : K ≤ normalizer (E : Set G))
    (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G))
    (hdisjE : Disjoint (hallCoreIn M) E)
    (hHnotcyc : ¬ IsCyclic ↥(hallCoreIn M))
    (hMM2 : ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ mixedFitting M)
    (hFeq : ((mixedFitting M : Set G)) =
      (hallCoreIn M : Set G) * ((centralizerWithin M (hallCoreIn M) : Subgroup G) : Set G))
    (hFle : mixedFitting M ≤ (⁅M, M⁆ : Subgroup G))
    (hW₂bot : W₂ ≠ ⊥) (hW₂cyc : IsCyclic ↥W₂)
    (hW₂le : W₂ ≤ hallCoreIn M ⊓ ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆)
    (hW₂cent : ∀ k ∈ K, k ≠ 1 → (⁅M, M⁆ : Subgroup G) ⊓ centralizer ({k} : Set G) = W₂)
    (hdp : IsInternalDirectProduct (K ⊔ W₂) K W₂)
    (hti : IsTIWithNormalizer (cyclicTIset K W₂) (K ⊔ W₂)) :
    IsWitnessedPConfiguration M E K W₂ where
  lt_top := hMtop
  ne_bot_W₁ := hKbot
  isCyclic_W₁ := hKcyc
  hall_W₁ := hKhall
  sup_commutator_W₁ := hsupK
  disjoint_commutator_W₁ := hdisjK
  isNilpotent_E := hEnil
  le_commutator_E := hEMM
  le_normalizer_E := hKnormE
  sup_hallCore_E := by rw [← hallCoreIn_eq]; exact hsupE
  disjoint_hallCore_E := by rw [← hallCoreIn_eq]; exact hdisjE
  not_isCyclic_hallCore := by rw [← hallCoreIn_eq]; exact hHnotcyc
  commutator_commutator_le_fittingRaw := by rw [← mixedFitting_eq]; exact hMM2
  coe_fittingRaw_eq := by
    rw [← mixedFitting_eq, ← hallCoreIn_eq, ← centralizerWithin_eq]; exact hFeq
  fittingRaw_le_commutator := by rw [← mixedFitting_eq]; exact hFle
  ne_bot_W₂ := hW₂bot
  isCyclic_W₂ := hW₂cyc
  le_W₂ := by rw [← hallCoreIn_eq]; exact hW₂le
  inf_centralizer_eq_W₂ := hW₂cent
  isInternalDirectProduct_sup := hdp
  isTIWithNormalizer_cyclicTIset := hti

omit [Finite G] in
theorem natCard_commutator_mul_natCard {M K : Subgroup G}
    (hKM : K ≤ M) (hsupK : (⁅M, M⁆ : Subgroup G) ⊔ K = M)
    (hdisjK : Disjoint (⁅M, M⁆ : Subgroup G) K) :
    Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K = Nat.card ↥M := by
  have hnorm : K ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_self (hKM.trans Subgroup.le_normalizer)
  have hset : ((⁅M, M⁆ : Subgroup G) : Set G) * (K : Set G) = (M : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm, hsupK]
  have hkey := natCard_mul_mul_natCard_inf (⁅M, M⁆ : Subgroup G) K
  rw [hdisjK.eq_bot, Subgroup.card_bot, mul_one,
    show Nat.card ↥(((⁅M, M⁆ : Subgroup G) : Set G) * (K : Set G)) = Nat.card ↥M from
      Nat.card_congr (Equiv.cast (congrArg (fun s : Set G => {x // x ∈ s}) hset))] at hkey
  exact hkey.symm

theorem coprime_natCard_index_subgroupOf_commutator {M K : Subgroup G}
    (hKM : K ≤ M) (hsupK : (⁅M, M⁆ : Subgroup G) ⊔ K = M)
    (hdisjK : Disjoint (⁅M, M⁆ : Subgroup G) K)
    (hKhall : (Nat.card ↥K).Coprime (K.relIndex M)) :
    (Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)).Coprime
      ((⁅M, M⁆ : Subgroup G).subgroupOf M).index := by
  have hprod := natCard_commutator_mul_natCard hKM hsupK hdisjK
  have hcardD : Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M) =
      Nat.card ↥(⁅M, M⁆ : Subgroup G) := natCard_subgroupOf (Subgroup.commutator_le_self M)
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K := natCard_subgroupOf hKM
  have hidxD : ((⁅M, M⁆ : Subgroup G).subgroupOf M).index = Nat.card ↥K := by
    have h1 := Subgroup.card_mul_index ((⁅M, M⁆ : Subgroup G).subgroupOf M)
    rw [hcardD] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans hprod.symm)
  have hidxK : (K.subgroupOf M).index = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    have h1 := Subgroup.card_mul_index (K.subgroupOf M)
    rw [hcardK] at h1
    refine Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥K) Nat.card_pos (h1.trans ?_)
    rw [← hprod, mul_comm]
  rw [hcardD, hidxD]
  rw [show K.relIndex M = Nat.card ↥(⁅M, M⁆ : Subgroup G) by rw [← index_subgroupOf, hidxK]]
    at hKhall
  exact hKhall.symm

theorem exists_invariant_complement_hallCoreIn {M K : Subgroup G} (hsolv : Group.IsSolvable ↥M)
    (hKM : K ≤ M) (hsupK : (⁅M, M⁆ : Subgroup G) ⊔ K = M)
    (hdisjK : Disjoint (⁅M, M⁆ : Subgroup G) K)
    (hHMM : hallCoreIn M ≤ (⁅M, M⁆ : Subgroup G))
    (hDhall : (Nat.card ↥((⁅M, M⁆ : Subgroup G).subgroupOf M)).Coprime
      ((⁅M, M⁆ : Subgroup G).subgroupOf M).index) :
    ∃ E : Subgroup G, E ≤ (⁅M, M⁆ : Subgroup G) ∧ hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G) ∧
      hallCoreIn M ⊓ E = ⊥ ∧ K ≤ normalizer (E : Set G) := by
  have := hsolv
  have hDnormal : ((⁅M, M⁆ : Subgroup G).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.commutator_le_self M)).2
      (Subgroup.normalizer_commutator_ge_left M M)
  have hHnormal : (hallCore ↥M).Normal := hallCore_normal
  have hHD : hallCore ↥M ≤ (⁅M, M⁆ : Subgroup G).subgroupOf M := fun x hx =>
    hHMM (Subgroup.mem_map_of_mem _ hx)
  have hDKuniv : (((⁅M, M⁆ : Subgroup G).subgroupOf M : Subgroup ↥M) : Set ↥M) *
      ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) = Set.univ := by
    have hsup : (⁅M, M⁆ : Subgroup G).subgroupOf M ⊔ K.subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (Subgroup.commutator_le_self M) hKM, hsupK,
        Subgroup.subgroupOf_self]
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (le_trans le_top (le_of_eq (Subgroup.normalizer_eq_top_iff.2 hDnormal).symm)), hsup]
    exact Subgroup.coe_top
  have hDKbot : (⁅M, M⁆ : Subgroup G).subgroupOf M ⊓ K.subgroupOf M = ⊥ := by
    rw [← inf_subgroupOf, hdisjK.eq_bot, Subgroup.bot_subgroupOf]
  have hHrel : (Nat.card ↥(hallCore ↥M)).Coprime
      ((hallCore ↥M).relIndex ((⁅M, M⁆ : Subgroup G).subgroupOf M)) :=
    coprime_natCard_index_hallCore.coprime_dvd_right (Subgroup.relIndex_dvd_index_of_le hHD)
  obtain ⟨E1, hED, hsupE, hdisjE, hinv⟩ :=
    exists_invariant_complement_sup_of_coprime hDKuniv hDKbot hDhall hHD hHrel
  refine ⟨E1.map M.subtype, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩; exact hED hy
  · rw [hallCoreIn_eq, ← Subgroup.map_sup, hsupE,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_self M)]
  · rw [hallCoreIn_eq, ← Subgroup.map_inf _ _ M.subtype M.subtype_injective, hdisjE,
      Subgroup.map_bot]
  · intro k hk
    refine mem_normalizer_of_conj_smul_eq (E := E1.map M.subtype) ?_
    have h2 := congrArg (Subgroup.map M.subtype)
      (hinv (⟨k, hKM hk⟩ : ↥M) (show (⟨k, hKM hk⟩ : ↥M) ∈ K.subgroupOf M from hk))
    rwa [map_subtype_conj_smul] at h2

theorem isNilpotent_of_isNilpotentQuotient {D H E : Subgroup G} (hHD : H ≤ D) (hED : E ≤ D)
    (hsup : H ⊔ E = D) (hinf : H ⊓ E = ⊥)
    (hnil : IsNilpotentQuotient D H) : Group.IsNilpotent ↥E := by
  obtain ⟨hnorm, hq⟩ := hnil
  have := hnorm
  have hcompl : (E.subgroupOf D).IsComplement' (H.subgroupOf D) := by
    refine isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_
    · rw [← Subgroup.subgroupOf_sup hHD hED, hsup, Subgroup.subgroupOf_self]
    · rw [← inf_subgroupOf, hinf, Subgroup.bot_subgroupOf]
  have := hq
  exact Group.nilpotent_of_mulEquiv
    (((Subgroup.subgroupOfEquivOfLe hED).symm).trans hcompl.QuotientMulEquiv.symm).symm

omit [Finite G] in
noncomputable def quotientMulEquivOfComplement {S H E : Subgroup G} (hHS : H ≤ S) (hES : E ≤ S)
    (hnorm : (H.subgroupOf S).Normal) (hsup : H ⊔ E = S) (hinf : H ⊓ E = ⊥) :
    (↥S ⧸ H.subgroupOf S) ≃* ↥E :=
  have hcompl : (E.subgroupOf S).IsComplement' (H.subgroupOf S) := by
    have := hnorm
    refine isComplement'_of_sup_eq_top_of_inf_eq_bot ?_ ?_
    · rw [← Subgroup.subgroupOf_sup hHS hES, hsup, Subgroup.subgroupOf_self]
    · rw [← inf_subgroupOf, hinf, Subgroup.bot_subgroupOf]
  have := hnorm
  hcompl.QuotientMulEquiv.trans (Subgroup.subgroupOfEquivOfLe hES)

omit [Finite G] in
theorem isMulCommutativeQuotient_iff_of_complement {S H E : Subgroup G} (hHS : H ≤ S) (hES : E ≤ S)
    (hnorm : (H.subgroupOf S).Normal) (hsup : H ⊔ E = S) (hinf : H ⊓ E = ⊥) :
    IsMulCommutativeQuotient S H ↔ IsMulCommutative ↥E := by
  have e := quotientMulEquivOfComplement hHS hES hnorm hsup hinf
  constructor
  · rintro ⟨hn, hq⟩
    have := hn
    have := hq
    exact isMulCommutative_of_mulEquiv e.symm
  · intro hq
    have := hq
    exact ⟨hnorm, isMulCommutative_of_mulEquiv e⟩

variable {M : Subgroup G}

theorem exists_isWitnessedPConfiguration_of_isTypeIIToV
    (h : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    ∃ E W₁ W₂ : Subgroup G, IsWitnessedPConfiguration M E W₁ W₂ := by
  rcases h with h | h | h | h
  · obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨E, W₁, W₂, hc⟩ := h.exists_isPConfiguration
    exact ⟨E, W₁, W₂, hc.isWitnessedPConfiguration⟩
  · obtain ⟨W₁, W₂, hc, -⟩ := h.exists_isWitnessedPConfiguration
    exact ⟨⊥, W₁, W₂, hc⟩

theorem not_isTypeI_of_isWitnessedPConfiguration {E W₁ W₂ : Subgroup G}
    (hsolv : Group.IsSolvable ↥M) (hc : IsWitnessedPConfiguration M E W₁ W₂) :
    ¬ IsTypeI M := by
  intro hI
  have := hsolv
  obtain ⟨E₁, hfrob, -⟩ := hI.exists_isFrobeniusType
  obtain ⟨E₀, hE₀E, hexp, hfree⟩ := hfrob.exists_exponent_eq
  set K : Subgroup ↥M := W₁.subgroupOf M with hK
  have hcycK : IsCyclic ↥K :=
    have := hc.isCyclic_W₁
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁)).mpr this
  have hcardK : Nat.card ↥K = Nat.card ↥W₁ := natCard_subgroupOf hc.le_M_W₁
  have hHle : hallCore ↥M ≤ (⁅M, M⁆ : Subgroup G).subgroupOf M := fun x hx =>
    hc.hallCore_le_commutator (Subgroup.mem_map_of_mem _ hx)
  have hKH : (Nat.card ↥K).Coprime (Nat.card ↥(hallCore ↥M)) := by
    refine (hcardK ▸ hc.coprime_natCard_W₁_natCard_commutator).coprime_dvd_right ?_
    have h1 := Subgroup.card_dvd_of_le hHle
    rwa [natCard_subgroupOf (Subgroup.commutator_le_self M)] at h1
  have hbot : hallCore ↥M ⊓ Subgroup.centralizer ((K : Set ↥M)) = ⊥ :=
    inf_centralizer_eq_bot_of_exponent_eq coprime_natCard_index_hallCore
      hfrob.sup_eq_top hfrob.inf_eq_bot hE₀E hexp hfree
      (subgroupOf_ne_bot hc.le_M_W₁ hc.ne_bot_W₁)
      (by rw [show K.index = W₁.relIndex M from rfl, hcardK]; exact hc.hall_W₁) hKH
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc.ne_bot_W₂
  have hwM : (w : G) ∈ M := hc.le_M_W₂ w.2
  have hwH : (⟨(w : G), hwM⟩ : ↥M) ∈ hallCore ↥M := by
    obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.1 (hc.le_hallCore_W₂ w.2)
    exact (Subtype.ext hyw : y = (⟨(w : G), hwM⟩ : ↥M)) ▸ hy
  have hwC : (⟨(w : G), hwM⟩ : ↥M) ∈ Subgroup.centralizer ((K : Set ↥M)) :=
    Subgroup.mem_centralizer_iff.2 fun x hx =>
      Subtype.ext (by simpa using (hc.commute_W₁_W₂ (hx : (x : G) ∈ W₁) w.2).eq)
  have hmem : (⟨(w : G), hwM⟩ : ↥M) ∈ (⊥ : Subgroup ↥M) :=
    hbot ▸ Subgroup.mem_inf.2 ⟨hwH, hwC⟩
  rw [Subgroup.mem_bot] at hmem
  exact hw (Subtype.ext (by simpa using congrArg (Subtype.val) hmem))

theorem not_isTypeI_of_isTypeIIToV (hsolv : Group.IsSolvable ↥M)
    (h : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) : ¬ IsTypeI M := by
  obtain ⟨E, W₁, W₂, hc⟩ := exists_isWitnessedPConfiguration_of_isTypeIIToV h
  exact not_isTypeI_of_isWitnessedPConfiguration hsolv hc

theorem not_isTypeIII_of_isTypeII (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeII M) :
    ¬ IsTypeIII M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ := exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inl h1)
  exact (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.2.2.1
    (h2.clauses_of_isWitnessedPConfiguration hsolv hc).2.2.2

theorem not_isTypeIV_of_isTypeII (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeII M) :
    ¬ IsTypeIV M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ := exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inl h1)
  exact (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.2.2.1
    (h2.clauses_of_isWitnessedPConfiguration hsolv hc).2.2

theorem not_isTypeV_of_isTypeII (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeII M) :
    ¬ IsTypeV M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ := exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inl h1)
  exact (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.1
    (h2.clauses_of_isWitnessedPConfiguration hsolv hc).1

theorem not_isTypeIV_of_isTypeIII (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeIII M) :
    ¬ IsTypeIV M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ :=
    exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inr (Or.inl h1))
  exact (h2.clauses_of_isWitnessedPConfiguration hsolv hc).2.1
    (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.2.1

theorem not_isTypeV_of_isTypeIII (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeIII M) :
    ¬ IsTypeV M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ :=
    exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inr (Or.inl h1))
  exact (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.1
    (h2.clauses_of_isWitnessedPConfiguration hsolv hc).1

theorem not_isTypeV_of_isTypeIV (hsolv : Group.IsSolvable ↥M) (h1 : IsTypeIV M) :
    ¬ IsTypeV M := fun h2 => by
  obtain ⟨E, W₁, W₂, hc⟩ :=
    exists_isWitnessedPConfiguration_of_isTypeIIToV (Or.inr (Or.inr (Or.inl h1)))
  exact (h1.clauses_of_isWitnessedPConfiguration hsolv hc).2.1
    (((h2.clauses_of_isWitnessedPConfiguration hsolv hc).1) ▸ inferInstance)

theorem localTypes_unique (hsolv : Group.IsSolvable ↥M) {i j : Fin 5}
    (hi : localTypes M i) (hj : localTypes M j) : i = j := by
  fin_cases i <;> fin_cases j <;>
    simp only [localTypes_zero, localTypes_one, localTypes_two, localTypes_three,
      localTypes_four] at hi hj <;> first
    | rfl
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inl hi))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inl hi)))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inl hi))))
    | exact absurd hj (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inr hi))))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inl hj))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inl hj)))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inl hj))))
    | exact absurd hi (not_isTypeI_of_isTypeIIToV hsolv (Or.inr (Or.inr (Or.inr hj))))
    | exact absurd hj (not_isTypeIII_of_isTypeII hsolv hi)
    | exact absurd hj (not_isTypeIV_of_isTypeII hsolv hi)
    | exact absurd hj (not_isTypeV_of_isTypeII hsolv hi)
    | exact absurd hi (not_isTypeIII_of_isTypeII hsolv hj)
    | exact absurd hi (not_isTypeIV_of_isTypeII hsolv hj)
    | exact absurd hi (not_isTypeV_of_isTypeII hsolv hj)
    | exact absurd hj (not_isTypeIV_of_isTypeIII hsolv hi)
    | exact absurd hj (not_isTypeV_of_isTypeIII hsolv hi)
    | exact absurd hi (not_isTypeIV_of_isTypeIII hsolv hj)
    | exact absurd hi (not_isTypeV_of_isTypeIII hsolv hj)
    | exact absurd hj (not_isTypeV_of_isTypeIV hsolv hi)
    | exact absurd hi (not_isTypeV_of_isTypeIV hsolv hj)

variable {K U : Subgroup G}

theorem structure_data_of_ne_bot (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥) :
    sigmaCore M ⊔ U = (⁅M, M⁆ : Subgroup G) ∧ sigmaCore M ⊓ U = ⊥ ∧
      (⁅M, M⁆ : Subgroup G) ⊔ K = M ∧ Disjoint (⁅M, M⁆ : Subgroup G) K := by
  obtain ⟨⟨-, -, hSMM, -⟩, -⟩ := h₃ G hamb M K U h
  obtain ⟨-, -, -, -, hMM, -⟩ := h₄ G hamb M K U h hK
  have hUMM : U ≤ (⁅M, M⁆ : Subgroup G) := fun x hx => by
    rw [← SetLike.mem_coe, hMM]; exact ⟨1, one_mem _, x, hx, one_mul x⟩
  have hSU : sigmaCore M ⊓ U = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_left _ (le_sup_left : U ≤ U ⊔ K)).trans
      h.semidirect_M.inf_eq_bot.le)
  have hsupSU : sigmaCore M ⊔ U = (⁅M, M⁆ : Subgroup G) := by
    refine le_antisymm (sup_le hSMM hUMM) fun x hx => ?_
    rw [← SetLike.mem_coe, hMM] at hx
    obtain ⟨s, hs, v, hv, rfl⟩ := hx
    exact Subgroup.mul_mem _ (le_sup_left (α := Subgroup G) hs)
      (le_sup_right (α := Subgroup G) hv)
  have hsupK : (⁅M, M⁆ : Subgroup G) ⊔ K = M :=
    le_antisymm (sup_le (Subgroup.commutator_le_self M) h.le_M_K)
      (le_trans (le_of_eq h.semidirect_M.sup_eq.symm)
        (sup_le (hSMM.trans le_sup_left) (sup_le_sup_right hUMM K)))
  refine ⟨hsupSU, hSU, hsupK, ?_⟩
  have hcardM := natCard_eq_of_isLocalKappaSetup h
  have hcardMM : Nat.card ↥(⁅M, M⁆ : Subgroup G) = Nat.card ↥(sigmaCore M) * Nat.card ↥U := by
    have hc := natCard_mul_mul_natCard_inf (sigmaCore M) U
    rw [hSU, Subgroup.card_bot, mul_one] at hc
    rw [← hc]
    exact Nat.card_congr (Equiv.cast (congrArg (fun s : Set G => {x // x ∈ s}) hMM))
  have hnorm : K ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_self (h.le_M_K.trans Subgroup.le_normalizer)
  have hset : ((⁅M, M⁆ : Subgroup G) : Set G) * (K : Set G) = (M : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm, hsupK]
  have hkey := natCard_mul_mul_natCard_inf (⁅M, M⁆ : Subgroup G) K
  rw [show Nat.card ↥(((⁅M, M⁆ : Subgroup G) : Set G) * (K : Set G)) = Nat.card ↥M from
    Nat.card_congr (Equiv.cast (congrArg (fun s : Set G => {x // x ∈ s}) hset))] at hkey
  rw [disjoint_iff, ← Subgroup.card_eq_one]
  refine Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥M) Nat.card_pos ?_
  rw [mul_one, hkey, hcardMM, hcardM]
  ring

theorem coprime_natCard_relIndex_K {G : Type u} [Group G] [Finite G] {M K U : Subgroup G}
    (h : IsLocalKappaSetup M K U) : (Nat.card ↥K).Coprime (K.relIndex M) := by
  have h2 := h.hall_K.coprime_natCard_index
  rwa [natCard_subgroupOf h.le_M_K, index_subgroupOf] at h2

theorem isWitnessedPConfiguration_of_isLocalKappaSetup
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    {E : Subgroup G} (hEMM : E ≤ (⁅M, M⁆ : Subgroup G)) (hKnormE : K ≤ normalizer (E : Set G))
    (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G)) (hdisjE : hallCoreIn M ⊓ E = ⊥) :
    IsWitnessedPConfiguration M E K (centralizerWithin (sigmaCore M) K) := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨⟨hHbot, hHS, hSMM, hnil, hMM2, hFeq, hFle⟩, -⟩ := h₃ G hamb M K U h
  obtain ⟨hW₂bot, hW₂cyc, hW₂le, hHnotcyc, -, hcent⟩ := h₄ G hamb M K U h hK
  obtain ⟨-, -, hsupK, hdisjK⟩ := structure_data_of_ne_bot h₃ h₄ hamb h hK
  have hG : IsOddOrderMinimalSimple G :=
    ⟨hamb.odd_natCard, hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.isSolvable⟩
  obtain ⟨Mstar, -, -, -, -, hinf, hdp, hcycW, hti, -⟩ :=
    h₈ G hG M h.isCoatom K U ⟨h.le_M_K, h.hall_K⟩ h.le_M_U h.semidirect_M h.semidirect_UK
      h.le_normalizer_U hK (centralizerWithin (sigmaCore M) K) (centralizerWithin_eq _ _)
  rw [hinf] at hdp hcycW hti
  have hKcyc : IsCyclic ↥K :=
    have := hcycW
    isCyclic_of_le (le_sup_left : K ≤ K ⊔ centralizerWithin (sigmaCore M) K)
  refine isWitnessedPConfiguration_of_data h.isCoatom.1.lt_top hK hKcyc
    (coprime_natCard_relIndex_K h) hsupK hdisjK
    (isNilpotent_of_isNilpotentQuotient (hHS.trans hSMM) hEMM hsupE hdisjE hnil)
    hEMM hKnormE hsupE (disjoint_iff.2 hdisjE) hHnotcyc hMM2 hFeq (hFle hK) hW₂bot hW₂cyc
    hW₂le ?_ hdp hti
  intro k hk hk1
  have h2 := hcent k hk hk1
  rwa [centralizerWithinElem_eq] at h2

theorem exists_isWitnessedPConfiguration_of_ne_bot
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥) :
    ∃ E : Subgroup G,
      IsWitnessedPConfiguration M E K (centralizerWithin (sigmaCore M) K) := by
  have hsolv : Group.IsSolvable ↥M := hamb.isSolvable M h.isCoatom.1
  obtain ⟨⟨-, hHS, hSMM, -⟩, -⟩ := h₃ G hamb M K U h
  obtain ⟨-, -, hsupK, hdisjK⟩ := structure_data_of_ne_bot h₃ h₄ hamb h hK
  obtain ⟨E, hEMM, hsupE, hdisjE, hKnormE⟩ :=
    exists_invariant_complement_hallCoreIn hsolv h.le_M_K hsupK hdisjK (hHS.trans hSMM)
      (coprime_natCard_index_subgroupOf_commutator h.le_M_K hsupK hdisjK
        (coprime_natCard_relIndex_K h))
  exact ⟨E, isWitnessedPConfiguration_of_isLocalKappaSetup h₃ h₄ h₈ hamb h hK hEMM hKnormE
    hsupE hdisjE⟩

theorem ne_bot_U_of_eq_bot_K (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    {G : Type u} [Group G] [Finite G] (hamb : IsFBGAmbient G) {M K U : Subgroup G}
    (h : IsLocalKappaSetup M K U) (hK : K = ⊥) : U ≠ ⊥ := by
  intro hU
  obtain ⟨⟨hHbot, -, hSMM, -⟩, -⟩ := h₃ G hamb M K U h
  have hMS : sigmaCore M = M := by
    have h1 := h.semidirect_M.sup_eq
    rw [hK, hU] at h1
    simpa using h1
  have := hamb.isSolvable M h.isCoatom.1
  have hMbot : M ≠ ⊥ := by
    intro hc
    rw [hc, hallCoreIn_bot] at hHbot
    exact absurd hHbot (lt_irrefl _)
  rw [hMS] at hSMM
  exact (commutator_lt_self_of_ne_bot hMbot).not_ge hSMM

theorem sup_hallCoreIn_U_of_eq_bot_K (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    {G : Type u} [Group G] [Finite G] (hamb : IsFBGAmbient G) {M K U : Subgroup G}
    (h : IsLocalKappaSetup M K U) (hK : K = ⊥) (hU : U ≠ ⊥) :
    hallCoreIn M ⊔ U = M ∧ hallCoreIn M ⊓ U = ⊥ := by
  obtain ⟨hHS, -⟩ := h₂ G hamb M K U h hU
  have h1 := h.semidirect_M.sup_eq
  have h2 := h.semidirect_M.inf_eq_bot
  rw [hK] at h1 h2
  simp only [sup_bot_eq] at h1 h2
  exact ⟨hHS ▸ h1, hHS ▸ h2⟩

theorem isTypeI_of_eq_bot_K (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K = ⊥) :
    IsTypeI M := by
  have hU : U ≠ ⊥ := ne_bot_U_of_eq_bot_K h₃ hamb h hK
  obtain ⟨hHS, U₁, U₀, hU₁U, hU₀U, hU₁comm, hU₁norm, hU₁cent, hexp, hfree⟩ :=
    h₂ G hamb M K U h hU
  obtain ⟨⟨hHbot, -⟩, -⟩ := h₃ G hamb M K U h
  obtain ⟨hsup, hinf⟩ := sup_hallCoreIn_U_of_eq_bot_K h₂ hamb h hK hU
  have hHM : hallCoreIn M ≠ M := by
    intro hc
    refine hU (le_bot_iff.1 ?_)
    rw [← hinf]
    exact le_inf (by rw [hc]; exact h.le_M_U) le_rfl
  have hfrob : IsFrobeniusType ↥M (U.subgroupOf M) :=
    isFrobeniusType_subgroupOf (hallCoreIn_le M) h.le_M_U (subgroupOf_hallCoreIn M)
      hHbot.ne' hHM hsup hinf hU₁U hU₁norm hU₁comm
      (fun x hx hx1 => by
        have := hU₁cent x hx hx1; rwa [centralizerWithinElem_eq] at this)
      hU₀U hexp
      (fun x hx hx1 => by
        have := hfree x hx hx1; rwa [centralizerWithinElem_eq] at this)
  rcases h₇ G hamb M K U h hK with hti | ⟨hcomm, hrank⟩ | ⟨hexpdvd, r, hr, hcyc⟩
  · refine IsTypeI.of_isTIWithNormalizer (E := U.subgroupOf M) h.isCoatom.1.lt_top hfrob ?_
    rwa [hallCoreSharp_eq_sharp_hallCoreIn]
  · refine IsTypeI.of_abelian_rank_eq_two (E := U.subgroupOf M) h.isCoatom.1.lt_top hfrob
      ((isMulCommutative_hallCoreIn_iff M).1 hcomm) ?_
    rwa [← maxElementaryAbelianPRank_hallCoreIn M]
  · refine IsTypeI.of_exponent_dvd_of_isCyclic (E := U.subgroupOf M) h.isCoatom.1.lt_top hfrob
      (fun s hs => ?_) ⟨r, ?_, ?_⟩
    · rw [exponent_subgroupOf h.le_M_U]
      exact hexpdvd s (by rwa [natCard_hallCoreIn M])
    · rwa [← natCard_hallCoreIn M]
    · exact (isCyclic_pComplCoreIn_iff M r).1 hcyc

theorem sup_hallCoreIn_U (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U ≠ ⊥) :
    hallCoreIn M ⊔ U = (⁅M, M⁆ : Subgroup G) ∧ hallCoreIn M ⊓ U = ⊥ := by
  obtain ⟨-, -, -, hHS⟩ := h₅ G hamb M K U h hK hU
  obtain ⟨hsupSU, hSU, -, -⟩ := structure_data_of_ne_bot h₃ h₄ hamb h hK
  exact ⟨hHS ▸ hsupSU, hHS ▸ hSU⟩

theorem isFrobeniusType_commutator
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U ≠ ⊥) :
    IsFrobeniusType ↥(⁅M, M⁆ : Subgroup G) (U.subgroupOf (⁅M, M⁆ : Subgroup G)) := by
  obtain ⟨-, -, hHMM, -⟩ := h₅ G hamb M K U h hK hU
  obtain ⟨hsup, hinf⟩ := sup_hallCoreIn_U h₃ h₄ h₅ hamb h hK hU
  obtain ⟨⟨hHbot, -⟩, -⟩ := h₃ G hamb M K U h
  obtain ⟨-, U₁, U₀, hU₁U, hU₀U, hU₁comm, hU₁norm, hU₁cent, hexp, hfree⟩ := h₂ G hamb M K U h hU
  have hUMM : U ≤ (⁅M, M⁆ : Subgroup G) := hsup ▸ le_sup_right
  have hHMMle : hallCoreIn M ≤ (⁅M, M⁆ : Subgroup G) := hsup ▸ le_sup_left
  have hne : hallCoreIn M ≠ (⁅M, M⁆ : Subgroup G) := by
    intro hc
    refine hU (le_bot_iff.1 ?_)
    rw [← hinf]
    exact le_inf (by rw [hc]; exact hUMM) le_rfl
  exact isFrobeniusType_subgroupOf hHMMle hUMM (hHMM ▸ subgroupOf_hallCoreIn _)
    hHbot.ne' hne hsup hinf hU₁U hU₁norm hU₁comm
    (fun x hx hx1 => by have := hU₁cent x hx hx1; rwa [centralizerWithinElem_eq] at this)
    hU₀U hexp
    (fun x hx hx1 => by have := hfree x hx hx1; rwa [centralizerWithinElem_eq] at this)

theorem isTypeII_of_ne_bot
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U ≠ ⊥) (hUcomm : IsMulCommutative ↥U) (hUnorm : ¬ normalizer (U : Set G) ≤ M) :
    IsTypeII M := by
  obtain ⟨hKprime, hFti, hHMM, -⟩ := h₅ G hamb M K U h hK hU
  obtain ⟨hsup, hinf⟩ := sup_hallCoreIn_U h₃ h₄ h₅ hamb h hK hU
  have hpc := isWitnessedPConfiguration_of_isLocalKappaSetup h₃ h₄ h₈ hamb h hK
    (hsup ▸ le_sup_right) h.le_normalizer_U hsup hinf
  refine IsTypeII.mk' ⟨hpc, hKprime, ?_⟩ hU hUcomm hUnorm
    (isFrobeniusType_commutator h₂ h₃ h₄ h₅ hamb h hK hU) ?_
  · rwa [fittingRawSharp_eq, ← sharp_eq, ← mixedFitting_eq]
  · rw [← hallCoreIn_eq, ← hallCoreIn_eq, hHMM]

theorem sigmaCore_eq_commutator_of_eq_bot_U
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U = ⊥) : sigmaCore M = (⁅M, M⁆ : Subgroup G) := by
  obtain ⟨hsupSU, -⟩ := structure_data_of_ne_bot h₃ h₄ hamb h hK
  rw [hU, sup_bot_eq] at hsupSU
  exact hsupSU

omit [Finite G] in
theorem le_normalizer_bot (K : Subgroup G) : K ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
  intro k _
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem isTypeV_of_eq_bot_U (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U = ⊥) (hHS : hallCoreIn M = sigmaCore M) : IsTypeV M := by
  have hSM := sigmaCore_eq_commutator_of_eq_bot_U h₃ h₄ hamb h hK hU
  have hsup : hallCoreIn M ⊔ (⊥ : Subgroup G) = (⁅M, M⁆ : Subgroup G) := by
    rw [sup_bot_eq, hHS, hSM]
  have hpc := isWitnessedPConfiguration_of_isLocalKappaSetup h₃ h₄ h₈ hamb h hK bot_le
    (le_normalizer_bot K) hsup (inf_bot_eq _)
  rcases h₆ G hamb M K U h hK hU hHS with hti | ⟨r, hr, hcyc, hdvd⟩ | ⟨r, hr, hcyc, hcard, hdvd⟩
  · exact IsTypeV.of_isTIWithNormalizer hpc (by rwa [hallCoreSharp_eq_sharp_hallCoreIn])
  · exact IsTypeV.of_dvd_sub_one hpc (by rwa [← natCard_hallCoreIn M])
      ((isCyclic_pComplCoreIn_iff M r).1 hcyc) hdvd
  · exact IsTypeV.of_dvd_add_one hpc (by rwa [← natCard_hallCoreIn M])
      ((isCyclic_pComplCoreIn_iff M r).1 hcyc)
      (by rwa [← natCard_pCoreIn_hallCoreIn M r]) hdvd

theorem eq_bot_E_iff (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U = ⊥) {E : Subgroup G} (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G))
    (hdisjE : hallCoreIn M ⊓ E = ⊥) : E = ⊥ ↔ hallCoreIn M = sigmaCore M := by
  have hSM := sigmaCore_eq_commutator_of_eq_bot_U h₃ h₄ hamb h hK hU
  refine ⟨fun hE => ?_, fun hHS => ?_⟩
  · rw [hE, sup_bot_eq] at hsupE
    rw [hsupE, hSM]
  · rw [hHS, hSM] at hdisjE
    refine le_bot_iff.1 ?_
    rw [← hdisjE]
    exact le_inf (hsupE ▸ le_sup_right) le_rfl

omit [Finite G] in
theorem natCard_hallCoreIn_mul_natCard_E {M E : Subgroup G}
    (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G)) (hdisjE : hallCoreIn M ⊓ E = ⊥) :
    Nat.card ↥(hallCoreIn M) * Nat.card ↥E = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
  have hnorm : E ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) :=
    (hsupE ▸ le_sup_right : E ≤ (⁅M, M⁆ : Subgroup G)).trans
      ((Subgroup.commutator_le_self M).trans (le_normalizer_map_subtype_hallCore M))
  have hset : ((hallCoreIn M : Subgroup G) : Set G) * (E : Set G)
      = ((⁅M, M⁆ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm, hsupE]
  have hkey := natCard_mul_mul_natCard_inf (hallCoreIn M) E
  rw [hdisjE, Subgroup.card_bot, mul_one,
    show Nat.card ↥(((hallCoreIn M : Subgroup G) : Set G) * (E : Set G))
        = Nat.card ↥(⁅M, M⁆ : Subgroup G) from
      Nat.card_congr (Equiv.cast (congrArg (fun s : Set G => {x // x ∈ s}) hset))] at hkey
  exact hkey.symm

theorem coprime_natCard_relIndex_E {M K E : Subgroup G} (hEM : E ≤ M) (hKM : K ≤ M)
    (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G)) (hdisjE : hallCoreIn M ⊓ E = ⊥)
    (hprod : Nat.card ↥(⁅M, M⁆ : Subgroup G) * Nat.card ↥K = Nat.card ↥M)
    (hKhall : (Nat.card ↥K).Coprime (K.relIndex M)) :
    (Nat.card ↥E).Coprime (E.relIndex M) := by
  have hHE := natCard_hallCoreIn_mul_natCard_E hsupE hdisjE
  have hcardM : Nat.card ↥(hallCoreIn M) * (Nat.card ↥E * Nat.card ↥K) = Nat.card ↥M := by
    rw [← mul_assoc, hHE, hprod]
  have hidx : E.relIndex M = Nat.card ↥(hallCoreIn M) * Nat.card ↥K := by
    have h1 := Subgroup.card_mul_index (E.subgroupOf M)
    rw [natCard_subgroupOf hEM, index_subgroupOf] at h1
    refine Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥E) Nat.card_pos (h1.trans ?_)
    rw [← hcardM]; ring
  rw [hidx]
  refine Nat.Coprime.mul_right ?_ ?_
  · have hcop : (Nat.card ↥(hallCoreIn M)).Coprime ((hallCoreIn M).relIndex M) := by
      have h2 := coprime_natCard_index_hallCore (X := ↥M)
      rwa [← natCard_hallCoreIn M, ← subgroupOf_hallCoreIn M, index_subgroupOf] at h2
    refine (Nat.Coprime.coprime_dvd_right ?_ hcop).symm
    have h1 := Subgroup.card_mul_index ((hallCoreIn M).subgroupOf M)
    rw [natCard_subgroupOf (hallCoreIn_le M), index_subgroupOf] at h1
    rw [show (hallCoreIn M).relIndex M = Nat.card ↥E * Nat.card ↥K from
      Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥(hallCoreIn M)) Nat.card_pos
        (h1.trans hcardM.symm)]
    exact Dvd.intro _ rfl
  · have hidxK : K.relIndex M = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
      have h1 := Subgroup.card_mul_index (K.subgroupOf M)
      rw [natCard_subgroupOf hKM, index_subgroupOf] at h1
      refine Nat.eq_of_mul_eq_mul_left (n := Nat.card ↥K) Nat.card_pos (h1.trans ?_)
      rw [← hprod, mul_comm]
    rw [hidxK] at hKhall
    exact (hKhall.coprime_dvd_right (Dvd.intro_left _ hHE)).symm

theorem isMulCommutativeQuotient_iff_of_eq_bot_U
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U = ⊥) {E : Subgroup G} (hsupE : hallCoreIn M ⊔ E = (⁅M, M⁆ : Subgroup G))
    (hdisjE : hallCoreIn M ⊓ E = ⊥) :
    IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) ↔ IsMulCommutative ↥E := by
  have hSM := sigmaCore_eq_commutator_of_eq_bot_U h₃ h₄ hamb h hK hU
  have hHMM : hallCoreIn M ≤ (⁅M, M⁆ : Subgroup G) := hsupE ▸ le_sup_left
  rw [hSM]
  exact isMulCommutativeQuotient_iff_of_complement hHMM (hsupE ▸ le_sup_right)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hHMM).2
      (commutator_le_normalizer_hallCore M)) hsupE hdisjE

theorem isTypeIII_or_isTypeIV_of_eq_bot_U
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥)
    (hU : U = ⊥) (hHS : hallCoreIn M ≠ sigmaCore M) :
    (IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIII M) ∧
      (¬ IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIV M) := by
  have hsolv : Group.IsSolvable ↥M := hamb.isSolvable M h.isCoatom.1
  have hSM := sigmaCore_eq_commutator_of_eq_bot_U h₃ h₄ hamb h hK hU
  obtain ⟨⟨-, hHSle, hSMM, -⟩, hsecond⟩ := h₃ G hamb M K U h
  obtain ⟨-, -, hsupK, hdisjK⟩ := structure_data_of_ne_bot h₃ h₄ hamb h hK
  obtain ⟨-, hKprime, hFti⟩ := hsecond hHS
  obtain ⟨E, hEMM, hsupE, hdisjE, hKnormE⟩ :=
    exists_invariant_complement_hallCoreIn hsolv h.le_M_K hsupK hdisjK (hHSle.trans hSMM)
      (coprime_natCard_index_subgroupOf_commutator h.le_M_K hsupK hdisjK
        (coprime_natCard_relIndex_K h))
  have hpc := isWitnessedPConfiguration_of_isLocalKappaSetup h₃ h₄ h₈ hamb h hK hEMM hKnormE
    hsupE hdisjE
  have hEbot : E ≠ ⊥ := fun hE => hHS ((eq_bot_E_iff h₃ h₄ hamb h hK hU hsupE hdisjE).1 hE)
  have hEnorm : normalizer (E : Set G) ≤ M :=
    normalizer_le_of_le_sigmaCore hEbot (hSM ▸ hEMM)
      (coprime_natCard_relIndex_E (hEMM.trans (Subgroup.commutator_le_self M)) h.le_M_K
        hsupE hdisjE (natCard_commutator_mul_natCard h.le_M_K hsupK hdisjK)
        (coprime_natCard_relIndex_K h))
  have hcfg : IsPConfigurationIIToIV M E K (centralizerWithin (sigmaCore M) K) := by
    refine ⟨hpc, hKprime, ?_⟩
    rwa [fittingRawSharp_eq, ← sharp_eq, ← mixedFitting_eq]
  have hiff := isMulCommutativeQuotient_iff_of_eq_bot_U h₃ h₄ hamb h hK hU hsupE hdisjE
  exact ⟨fun hab => IsTypeIII.mk' hcfg hEbot (hiff.1 hab) hEnorm,
    fun hab => IsTypeIV.mk' hcfg (fun hc => hab (hiff.2 hc)) hEnorm⟩

theorem exists_good_isLocalKappaSetup (h₁ : Statements.FBG_kappa_complement_structure.{u})
    {G : Type u} [Group G] [Finite G] (hamb : IsFBGAmbient G) {M : Subgroup G}
    (hM : IsCoatom M) :
    ∃ K U : Subgroup G, IsLocalKappaSetup M K U ∧
      (K ≠ ⊥ → IsMulCommutative ↥U ∧ ¬ normalizer (U : Set G) ≤ M) := by
  obtain ⟨K, U, hKM, -, hKhall, hUM, hsemi1, hsemi2, -, hextra⟩ := h₁ G hamb M hM
  exact ⟨K, U, ⟨hM, hKM, hKhall, hUM, hsemi2.right_le_normalizer, hsemi1, hsemi2⟩,
    fun hK => ⟨(hextra hK).1, (hextra hK).2.1⟩⟩

theorem isTypeIIToV_of_ne_bot_K (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) (hK : K ≠ ⊥) :
    IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M := by
  by_cases hU : U = ⊥
  · by_cases hHS : hallCoreIn M = sigmaCore M
    · exact Or.inr (Or.inr (Or.inr (isTypeV_of_eq_bot_U h₃ h₄ h₆ h₈ hamb h hK hU hHS)))
    · by_cases hab : IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M)
      · exact Or.inr (Or.inl
          ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).1 hab))
      · exact Or.inr (Or.inr (Or.inl
          ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).2 hab)))
  ·
    obtain ⟨K₀, U₀, h₀, hextra⟩ := exists_good_isLocalKappaSetup h₁ hamb h.isCoatom
    have hK₀ : K₀ ≠ ⊥ := fun hc => hK ((eq_bot_K_iff_of_isLocalKappaSetup h h₀).2 hc)
    have hU₀ : U₀ ≠ ⊥ := fun hc => hU ((eq_bot_U_iff_of_isLocalKappaSetup h h₀).2 hc)
    exact Or.inl (isTypeII_of_ne_bot h₂ h₃ h₄ h₅ h₈ hamb h₀ hK₀ hU₀
      (hextra hK₀).1 (hextra hK₀).2)

theorem localTypes_iff_of_isLocalKappaSetup
    (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M K U : Subgroup G} (h : IsLocalKappaSetup M K U) :
    (IsTypeI M ↔ K = ⊥) ∧ (IsTypeII M ↔ K ≠ ⊥ ∧ U ≠ ⊥) ∧
      (K ≠ ⊥ → U = ⊥ →
        (IsTypeV M ↔ hallCoreIn M = sigmaCore M) ∧
          (hallCoreIn M ≠ sigmaCore M →
            (IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIII M) ∧
            (¬ IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M) → IsTypeIV M))) := by
  have hsolv : Group.IsSolvable ↥M := hamb.isSolvable M h.isCoatom.1
  refine ⟨⟨fun hI => ?_, fun hK => isTypeI_of_eq_bot_K h₂ h₃ h₇ hamb h hK⟩, ?_,
    fun hK hU => ⟨?_, isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU⟩⟩
  · by_contra hK
    exact not_isTypeI_of_isTypeIIToV hsolv
      (isTypeIIToV_of_ne_bot_K h₁ h₂ h₃ h₄ h₅ h₆ h₈ hamb h hK) hI
  · refine ⟨fun hII => ⟨?_, ?_⟩, fun ⟨hK, hU⟩ => ?_⟩
    · exact fun hK => not_isTypeI_of_isTypeIIToV hsolv (Or.inl hII)
        (isTypeI_of_eq_bot_K h₂ h₃ h₇ hamb h hK)
    · intro hU
      by_cases hK : K = ⊥
      · exact not_isTypeI_of_isTypeIIToV hsolv (Or.inl hII)
          (isTypeI_of_eq_bot_K h₂ h₃ h₇ hamb h hK)
      · by_cases hHS : hallCoreIn M = sigmaCore M
        · exact not_isTypeV_of_isTypeII hsolv hII
            (isTypeV_of_eq_bot_U h₃ h₄ h₆ h₈ hamb h hK hU hHS)
        · by_cases hab : IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M)
          · exact not_isTypeIII_of_isTypeII hsolv hII
              ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).1 hab)
          · exact not_isTypeIV_of_isTypeII hsolv hII
              ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).2 hab)
    · obtain ⟨K₀, U₀, h₀, hextra⟩ := exists_good_isLocalKappaSetup h₁ hamb h.isCoatom
      have hK₀ : K₀ ≠ ⊥ := fun hc => hK ((eq_bot_K_iff_of_isLocalKappaSetup h h₀).2 hc)
      have hU₀ : U₀ ≠ ⊥ := fun hc => hU ((eq_bot_U_iff_of_isLocalKappaSetup h h₀).2 hc)
      exact isTypeII_of_ne_bot h₂ h₃ h₄ h₅ h₈ hamb h₀ hK₀ hU₀ (hextra hK₀).1 (hextra hK₀).2
  · refine ⟨fun hV => ?_, isTypeV_of_eq_bot_U h₃ h₄ h₆ h₈ hamb h hK hU⟩
    by_contra hHS
    by_cases hab : IsMulCommutativeQuotient (sigmaCore M) (hallCoreIn M)
    · exact not_isTypeV_of_isTypeIII hsolv
        ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).1 hab) hV
    · exact not_isTypeV_of_isTypeIV hsolv
        ((isTypeIII_or_isTypeIV_of_eq_bot_U h₃ h₄ h₈ hamb h hK hU hHS).2 hab) hV

theorem exists_localTypes (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) {G : Type u} [Group G] [Finite G]
    (hamb : IsFBGAmbient G) {M : Subgroup G} (hM : IsCoatom M) :
    ∃ i : Fin 5, localTypes M i := by
  obtain ⟨K, U, h, -⟩ := exists_good_isLocalKappaSetup h₁ hamb hM
  by_cases hK : K = ⊥
  · exact ⟨0, isTypeI_of_eq_bot_K h₂ h₃ h₇ hamb h hK⟩
  rcases isTypeIIToV_of_ne_bot_K h₁ h₂ h₃ h₄ h₅ h₆ h₈ hamb h hK with hc | hc | hc | hc
  · exact ⟨1, hc⟩
  · exact ⟨2, hc⟩
  · exact ⟨3, hc⟩
  · exact ⟨4, hc⟩

private theorem FBG_five_type_local_classification_aux
    (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) :
    Statements.FBG_five_type_local_classification.{u} := by
  intro G _ _ hamb
  refine ⟨fun M hM => ?_, fun M K U h =>
    localTypes_iff_of_isLocalKappaSetup h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hamb h⟩
  obtain ⟨i, hi⟩ := exists_localTypes h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hamb hM
  exact ⟨i, hi, fun j hj => localTypes_unique (hamb.isSolvable M hM.1) hj hi⟩

theorem FBG_five_type_local_classification
    (h₁ : Statements.FBG_kappa_complement_structure.{u})
    (h₂ : Statements.FBG_local_inertia_and_exponent_complement.{u})
    (h₃ : Statements.FBG_local_nilpotent_hall_core.{u})
    (h₄ : Statements.FBG_local_p_core_centralizer.{u})
    (h₅ : Statements.FBG_local_p_nontrivial_U_case.{u})
    (h₆ : Statements.FBG_local_p_trivial_U_alternative.{u})
    (h₇ : Statements.FBG_local_type_I_alternative.{u})
    (h₈ : Statements.FBG_paired_local_geometry.{u}) :
    Statements.FBG_five_type_local_classification.{u} :=
  FBG_five_type_local_classification_aux h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈

end Proofs

end

end CFSG.FeitThompson
