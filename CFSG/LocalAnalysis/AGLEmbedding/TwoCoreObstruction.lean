module

public import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

section Abstract

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem pCore_quotient_pCore_eq_bot' (p : ℕ) : CFSG.pCore p (X ⧸ CFSG.pCore p X) = ⊥ := by
  let Q := CFSG.pCore p X
  let K := (CFSG.pCore p (X ⧸ Q)).comap (QuotientGroup.mk' Q)
  have hKn : K.Normal := CFSG.pCore_normal.comap _
  have hKp : IsPGroup p K := IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup _
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hKQ : K ≤ Q := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff y).mpr (hKQ hx)

omit [Finite X] in
theorem le_pCore_of_isPGroup_of_le_commutative_normal {p : ℕ} {W T : Subgroup X} (hWn : W.Normal)
    (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hTW : T ≤ W) (hT : IsPGroup p T) :
    T ≤ CFSG.pCore p X := by
  let Wp : Subgroup X :=
    { carrier := {x | x ∈ W ∧ ∃ n : ℕ, x ^ p ^ n = 1}
      mul_mem' := by
        rintro a b ⟨ha, m, hm⟩ ⟨hb, n, hn⟩
        refine ⟨W.mul_mem ha hb, m + n, ?_⟩
        rw [(Commute.mul_pow (hW a ha b hb) _), pow_add, pow_mul, hm, one_pow, one_mul,
          mul_comm, pow_mul, hn, one_pow]
      one_mem' := ⟨W.one_mem, 0, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, n, hn⟩
        exact ⟨W.inv_mem ha, n, by rw [inv_pow, hn, inv_one]⟩ }
  have hWpn : Wp.Normal := ⟨fun x hx g => by
    obtain ⟨hxW, n, hn⟩ := hx
    exact ⟨hWn.conj_mem x hxW g, n, by rw [conj_pow, hn, mul_one, mul_inv_cancel]⟩⟩
  have hWpp : IsPGroup p Wp := fun x => by
    obtain ⟨n, hn⟩ := x.property.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  refine fun x hx => (le_sSup (s := {K : Subgroup X | K.Normal ∧ IsPGroup p K})
    ⟨hWpn, hWpp⟩ : Wp ≤ CFSG.pCore p X) ⟨hTW hx, ?_⟩
  obtain ⟨n, hn⟩ := hT ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem fitting_le_pPrimeCore_two (hX : CFSG.pCore 2 X = ⊥) :
    ComponentClassification.Fitting.subgroup X ≤ CFSG.pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  refine le_sSup (s := {K : Subgroup X | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hN, ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hT⟩ := hxp.exists_le_sylow
  have hmap := Sylow.map_le_pCore hN hnil 2 T
  rw [hX] at hmap
  have hx1 : (x : X) = 1 :=
    (Subgroup.mem_bot.mp (hmap (Subgroup.mem_map_of_mem _ (hT (Subgroup.mem_zpowers x)))))
  have : x = 1 := Subtype.ext hx1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem commutator_eq_bot_of_le_normalizer {L T : Subgroup X} (hL : IsComponentOf L ⊤)
    (hT : IsPGroup 2 T) (hLT : L ≤ Subgroup.normalizer (T : Set X)) : ⁅L, T⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := L ⊔ T
  have hLZ : L ≤ Z := le_sup_left
  have hTZ : T ≤ Z := le_sup_right
  have hZN : Z ≤ Subgroup.normalizer (T : Set X) := sup_le hLT Subgroup.le_normalizer
  have hcomp := ComponentClassification.LocalComponents.of_overgroup hL hLZ
  have hTn : (T.subgroupOf Z).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTZ).mpr hZN
  have hTp : IsPGroup 2 (T.subgroupOf Z) := hT.comap_subtype
  have : Group.IsNilpotent (T.subgroupOf Z) := hTp.isNilpotent
  have hc := ComponentClassification.LocalComponents.commutes_with_solvable_subnormal _ _ hcomp
    (ComponentClassification.Components.chain_of_mathlib_subnormal hTn.isSubnormal)
  have hmap := congrArg (Subgroup.map Z.subtype) hc
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLZ,
    Subgroup.map_subgroupOf_eq_of_le hTZ, Subgroup.map_bot] at hmap

theorem eq_bot_of_normalized_by_components (hX : CFSG.pCore 2 X = ⊥) {T : Subgroup X}
    (hT : IsPGroup 2 T)
    (hL : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ Subgroup.normalizer (T : Set X))
    (hO : CFSG.pPrimeCore 2 X ≤ Subgroup.centralizer (T : Set X)) : T = ⊥ := by
  let Fs := ComponentClassification.GeneralizedFitting.subgroup X
  have hFs : Fs ≤ Subgroup.centralizer (T : Set X) := by
    refine sup_le ((fitting_le_pPrimeCore_two hX).trans hO) (sSup_le fun L hLc => ?_)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_le_normalizer hLc hT (hL L hLc))
  have hTC : T ≤ Subgroup.centralizer (Fs : Set X) := Subgroup.le_centralizer_iff.mp hFs
  have hTF : T ≤ Fs := hTC.trans (ComponentClassification.GeneralizedFitting.centralizer_le X)
  have : Fs.Normal := ComponentClassification.GeneralizedFitting.normal X
  have hWn : (Fs ⊓ Subgroup.centralizer (Fs : Set X)).Normal := Subgroup.normal_inf_normal _ _
  have hW : ∀ x ∈ Fs ⊓ Subgroup.centralizer (Fs : Set X),
      ∀ y ∈ Fs ⊓ Subgroup.centralizer (Fs : Set X), x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp hy.2 x hx.1
  have hle := le_pCore_of_isPGroup_of_le_commutative_normal hWn hW (le_inf hTF hTC) hT
  rw [hX] at hle
  exact le_bot_iff.mp hle

theorem exists_component_not_le_normalizer_or_not_le_centralizer {S : Subgroup X}
    (hS : IsPGroup 2 S) (hSQ : ¬ S ≤ CFSG.pCore 2 X) :
    (∃ L : Subgroup (X ⧸ CFSG.pCore 2 X), IsComponentOf L ⊤ ∧
        ¬ L ≤ Subgroup.normalizer
          ((S.map (QuotientGroup.mk' (CFSG.pCore 2 X)) : Subgroup (X ⧸ CFSG.pCore 2 X)) :
            Set (X ⧸ CFSG.pCore 2 X))) ∨
      ¬ CFSG.pPrimeCore 2 (X ⧸ CFSG.pCore 2 X) ≤ Subgroup.centralizer
          ((S.map (QuotientGroup.mk' (CFSG.pCore 2 X)) : Subgroup (X ⧸ CFSG.pCore 2 X)) :
            Set (X ⧸ CFSG.pCore 2 X)) := by
  by_contra hcon
  rw [not_or, not_not] at hcon
  obtain ⟨hL, hO⟩ := hcon
  have hbot := eq_bot_of_normalized_by_components (pCore_quotient_pCore_eq_bot' 2)
    (hS.map _) (fun L hLc => by_contra fun hn => hL ⟨L, hLc, hn⟩) hO
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hSQ hbot

end Abstract

namespace TwoLocalPair

variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

theorem twoCore_subgroupOf_not_le (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ (pCoreOf 2 H).subgroupOf M ≤ CFSG.pCore 2 M := by
  intro hle
  apply h.twoCore_M_ne
  refine le_antisymm (h.twoCore_M_le hS) ?_
  rw [← CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_subgroupOf] at hle
  intro x hx
  have hxM : x ∈ M := h.twoCore_le hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr (show (⟨x, hxM⟩ : M).1 ∈ _
    from hx)))

theorem exists_component_or_oddCore (h : TwoLocalPair M H)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (∃ L : Subgroup (M ⧸ CFSG.pCore 2 M), IsComponentOf L ⊤ ∧
        ¬ L ≤ Subgroup.normalizer
          ((((pCoreOf 2 H).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
            Subgroup (M ⧸ CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M))) ∨
      ¬ CFSG.pPrimeCore 2 (M ⧸ CFSG.pCore 2 M) ≤ Subgroup.centralizer
          ((((pCoreOf 2 H).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
            Subgroup (M ⧸ CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M)) :=
  exists_component_not_le_normalizer_or_not_le_centralizer
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H).comap_subtype
    (h.twoCore_subgroupOf_not_le hS)

end TwoLocalPair

namespace D1Escape

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem twoCore_subgroupOf_not_le (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    ¬ (pCoreOf 2 H).subgroupOf M ≤ CFSG.pCore 2 M :=
  h.toTwoLocalPair.twoCore_subgroupOf_not_le hS

theorem exists_component_or_oddCore (h : D1Escape p P M H R)
    (hS : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H) :
    (∃ L : Subgroup (M ⧸ CFSG.pCore 2 M), IsComponentOf L ⊤ ∧
        ¬ L ≤ Subgroup.normalizer
          ((((pCoreOf 2 H).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
            Subgroup (M ⧸ CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M))) ∨
      ¬ CFSG.pPrimeCore 2 (M ⧸ CFSG.pCore 2 M) ≤ Subgroup.centralizer
          ((((pCoreOf 2 H).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) :
            Subgroup (M ⧸ CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M)) :=
  h.toTwoLocalPair.exists_component_or_oddCore hS

end D1Escape

end CFSG.AGLEmbedding
