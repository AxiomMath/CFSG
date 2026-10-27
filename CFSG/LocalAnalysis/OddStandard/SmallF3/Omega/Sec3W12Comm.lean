module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3W12Ord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem centralizer_pair_le_left' (x y : G) :
    centralizer ({x, y} : Set G) ≤ centralizer ({x} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Set.mem_insert x {y}))

private theorem le_centralizer_pair' {K : Subgroup G} {x y : G}
    (hx : K ≤ centralizer ({x} : Set G)) (hy : K ≤ centralizer ({y} : Set G)) :
    K ≤ centralizer ({x, y} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rcases hw with rfl | hw
  · exact Subgroup.mem_centralizer_iff.mp (hx hz) _ (Set.mem_singleton _)
  · rw [Set.mem_singleton_iff.mp hw]
    exact Subgroup.mem_centralizer_iff.mp (hy hz) _ (Set.mem_singleton _)

theorem commutator_zpowers_eq_self_or_le_centralizer {K : Subgroup G} (hK : IsQuasisimple K)
    {x : G} (hx : CFSG.conjugate K x = K) :
    ⁅K, zpowers x⁆ = K ∨ K ≤ centralizer ({x} : Set G) := by
  have hnorm : x ∈ normalizer (K : Set G) := by
    have h : x⁻¹ ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hx
    have h' := (normalizer (K : Set G)).inv_mem h
    rwa [inv_inv] at h'
  have hle : zpowers x ≤ normalizer (K : Set G) := Subgroup.zpowers_le.mpr hnorm
  have hNK : ⁅K, zpowers x⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hle
  have hnormal : (⁅K, zpowers x⁆.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr
      (Subgroup.normalizer_commutator_ge_left K (zpowers x))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hnormal with htop | hcen
  · exact Or.inl (le_antisymm hNK (Subgroup.subgroupOf_eq_top.mp htop))
  · right
    have hcomm : ⁅⁅K, zpowers x⁆, K⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hn' : (⟨n, hNK hn⟩ : ↥K) ∈ ⁅K, zpowers x⁆.subgroupOf K := hn
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hn') ⟨k, hk⟩)
    have h0 := CFSG.LocalCores.perfect_double_commutator hK.1 hcomm
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x)))

theorem isComponentIn_centralizer_of_commute [Finite G] (h36 : Asc82Lemma36) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) {X : Subgroup G} (hX : InCStar X)
    (hXF : InFStar X) (hpk : InF X ∨ IsL3Eps3 X) {x₀ x : G} (hx₀ : orderOf x₀ = 2)
    (hx : orderOf x = 2) (hcomm : x₀ * x = x * x₀)
    (hXx₀ : IsComponentIn X (centralizer ({x₀} : Set G)))
    (hxX : x ∈ centralizer (X : Set G)) : IsComponentIn X (centralizer ({x} : Set G)) := by
  have hXx : X ≤ centralizer ({x} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxX a ha)
  have hXpair : IsComponentIn X (centralizer ({x₀, x} : Set G)) :=
    hXx₀.mono (le_centralizer_pair' hXx₀.le hXx) (centralizer_pair_le_left' x₀ x)
  obtain ⟨K, hK, hXle⟩ := hS.lBalance x₀ x hx₀ hx hcomm X hXpair
  have hKF : InFStar K := hS.a2 x₀ x hx₀ hx hcomm X K hXpair hK hXle hXF
  by_cases hKx : CFSG.conjugate K x₀ = K
  · have hXK : X ≤ K := by
      rw [hKx, sup_idem] at hXle
      exact hXle
    rcases commutator_zpowers_eq_self_or_le_centralizer hK.isQuasisimple hKx with hcK | hKc
    · exfalso
      have harrow : WalterArrow X K := ⟨x₀, x, hx₀, hx, hcomm, hXx₀, hK, hXK, hcK⟩
      obtain ⟨e⟩ := hX.2 K (Relation.ReflTransGen.single (Or.inl harrow))
      exact (ctrQ_dvd_of_walterArrow harrow).2 (Nat.card_congr e.toEquiv)
    · have hXK' : IsComponentIn X K := hXx₀.mono hXK hKc
      have hKK : IsComponentIn K K := isComponentIn_of_normal le_rfl hK.isQuasisimple (by
        rw [Subgroup.subgroupOf_self]
        infer_instance)
      rw [hXK'.eq_of_le hKK hXK]
      exact hK
  · exfalso
    have hx₀x : x₀ ∈ centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hK' : IsComponentIn (CFSG.conjugate K x₀) (centralizer ({x} : Set G)) :=
      hK.conjugate hx₀x
    have hne : K ⊔ CFSG.conjugate K x₀ ≠ K := by
      intro heq
      exact hKx (hK'.eq_of_le hK (le_sup_right.trans heq.le))
    have hdiag : WalterArrowDiag X K := ⟨x₀, x, hx₀, hx, hcomm, hXx₀, hK, hXle, hne⟩
    obtain ⟨e⟩ := hX.2 K (Relation.ReflTransGen.single (Or.inr hdiag))
    have hctr : ctrQ X = ctrQ K := Nat.card_congr e.toEquiv
    by_cases hKp : InF K ∨ IsL3Eps3 K
    · obtain ⟨-, huniq⟩ := h36 G t L hS x K hx hK hKp
      exact hKx (huniq _ hK' (hKF.conjugate x₀))
    · rw [not_or] at hKp
      exact ctrQ_ne_of_pocketed hXF hpk hKF hKp.1 hKp.2 hctr

end CFSG.OddStandard.SmallF3.Omega
