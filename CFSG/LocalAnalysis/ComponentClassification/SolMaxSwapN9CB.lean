module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapP3

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem mem_klein_cases [Finite X] {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) {e₀ e₁ y : X}
    (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E) (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) (hy : y ∈ E) :
    y = 1 ∨ y = e₀ ∨ y = e₁ ∨ y = e₀ * e₁ := by
  classical
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein hE
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact hE2 e₀ he₀
  have h1 : e₀ * e₁ ≠ 1 := by
    intro h
    apply h01
    calc e₀ = e₀ * (e₀ * e₁) := by rw [h, mul_one]
      _ = e₁ := by rw [← mul_assoc, he₀2, one_mul]
  have h2 : e₀ * e₁ ≠ e₀ := fun h => he₁1 (mul_left_cancel (h.trans (mul_one e₀).symm))
  have h3 : e₀ * e₁ ≠ e₁ := fun h => he₀1 (mul_right_cancel (h.trans (one_mul e₁).symm))
  set T : Set X := {1, e₀, e₁, e₀ * e₁} with hTdef
  have hTE : T ⊆ (E : Set X) := by
    intro z hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact one_mem E
    · exact he₀
    · exact he₁
    · exact mul_mem he₀ he₁
  have hT4 : T.ncard = 4 := by
    rw [hTdef, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair h3.symm]
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      push Not
      exact ⟨h01, h2.symm⟩
    · rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      push Not
      exact ⟨Ne.symm he₀1, Ne.symm he₁1, Ne.symm h1⟩
  have hEn : (E : Set X).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hE4
  have hTeq : T = (E : Set X) :=
    Set.eq_of_subset_of_ncard_le hTE (by rw [hT4, hEn]) (Set.toFinite _)
  have hyT : y ∈ T := by rw [hTeq]; exact hy
  rcases hyT with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem inf_centralizer_le_normalizer_of_klein [Finite X] {E : Subgroup X}
    (hE : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) {e₀ e₁ : X}
    (he₀ : e₀ ∈ E) (he₁ : e₁ ∈ E) (he₀1 : e₀ ≠ 1) (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    centralizer ({e₀} : Set X) ⊓ centralizer ({e₁} : Set X) ≤ normalizer (E : Set X) := by
  intro x hx
  have hc0 : e₀ * x = x * e₀ := (mem_centralizer_singleton_iff.mp hx.1).symm
  have hc1 : e₁ * x = x * e₁ := (mem_centralizer_singleton_iff.mp hx.2).symm
  have h0 : x * e₀ * x⁻¹ = e₀ := by rw [← hc0, mul_inv_cancel_right]
  have h1 : x * e₁ * x⁻¹ = e₁ := by rw [← hc1, mul_inv_cancel_right]
  have hxy : ∀ y ∈ E, x * y * x⁻¹ = y := by
    intro y hy
    rcases mem_klein_cases hE he₀ he₁ he₀1 he₁1 h01 hy with rfl | rfl | rfl | rfl
    · group
    · exact h0
    · exact h1
    · calc x * (e₀ * e₁) * x⁻¹ = (x * e₀ * x⁻¹) * (x * e₁ * x⁻¹) := by group
        _ = e₀ * e₁ := by rw [h0, h1]
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hxy y hy]
    exact hy
  · intro hy
    have h2 := hxy _ hy
    have h3 : x * y * x⁻¹ = y := by
      have h4 : x⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * x = x⁻¹ * (x * y * x⁻¹) * x := by rw [h2]
      rwa [show x⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * x = x * y * x⁻¹ by group,
        show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h4
    rw [← h3]
    exact hy

theorem fusionZStar_eq_pPrimeCore_of_five {L : Type*} [Group L]
    (χ : L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 5)) :
    Open.fusionZStar L = pPrimeCore 2 L := by
  rw [Sol78.fusionZStar_eq_iff, eq_bot_iff]
  intro z hz
  have h1 : χ z ∈ center (alternatingGroup (Fin 5)) := by
    rw [← Subgroup.map_center_eq χ]
    exact ⟨z, hz, rfl⟩
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), mem_bot] at h1
  rw [mem_bot]
  exact χ.injective (h1.trans (map_one χ).symm)

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

structure FiveLayer (S : Sig36 X t J n e E D) (e₀ : X) (L₀ F : Subgroup X) : Prop where
  L₀J : L₀ ≤ J
  L₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X)
  L₀pc : IsPComponent 2 (L₀.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X)))
  type : Nonempty (↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 5))
  norm : ∀ y ∈ J, y * e₀ = e₀ * y → y ∈ normalizer (L₀ : Set X)
  ker : E ≤ UnbalancedLayer.coreActionKernel L₀
  FL₀ : F ≤ L₀
  Fk : Nonempty (F ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  FD : ∃ DF : Finset (Fin n), DF.card = 4 ∧ ∀ x : J, (x : X) ∈ F → ∀ ω ∉ DF,
    ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Perm (Fin n)) ω = ω

variable (S : Sig36 X t J n e E D)
include S

theorem exists_fiveLayer (hn : n = 9) {e₀ : X} (he₀E : e₀ ∈ E) (he₀1 : e₀ ≠ 1) :
    ∃ L₀ F : Subgroup X, S.FiveLayer e₀ L₀ F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact (card_sq_of_klein S.klein).2 e₀ he₀E
  have he₀J : e₀ ∈ J := S.le he₀E
  have h4 := S.card_support_coreImage_E he₀E he₀1
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isElementaryAbelian_of_klein S.klein).toIsMulCommutative.is_comm.comm
      ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨L₀, hL₀J, hL₀pc, hinv, hsupp, χ, -⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 e (le_normalizer he₀J) he₀2
      he₀J (by rw [mul_inv_cancel]; exact one_mem _) (by rw [h4]; omega)
  have hβ : Fintype.card ↥((coreImage e he₀J).supportᶜ : Finset (Fin n)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, h4]
    omega
  have hL₀Ct : L₀ ≤ centralizer ({t} : Set X) := (hL₀J.trans inf_le_left).trans S.pair.1.2.1
  have hL₀C : L₀ ≤ centralizer ({t} : Set X) ⊓ centralizer ({e₀} : Set X) :=
    le_inf hL₀Ct (hL₀J.trans inf_le_right)
  have hperf : ⁅L₀, L₀⁆ = L₀ := UnbalancedCorr.commutator_eq_of_isPComponent hL₀C hL₀pc
  let χ₅ : ↥L₀ ⧸ pPrimeCore 2 ↥L₀ ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hL₀q : Nontrivial (↥L₀ ⧸ pPrimeCore 2 ↥L₀) := by
    have : Nontrivial (Fin 5) := Fin.nontrivial_iff_two_le.mpr (by norm_num)
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact χ₅.toEquiv.nontrivial
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by omega) (by omega) e
  have hρe₀ : ρJ ⟨e₀, le_normalizer he₀J⟩ = coreImage e he₀J :=
    hρJ.apply_of_mem (by omega) ⟨e₀, he₀J⟩
  obtain ⟨hflC, hflpc, -⟩ := fixedLayer_facts_of_perm S.pair.1.2.1 S.pair.1.2.2.1 hρJ
    (le_normalizer he₀J) he₀2 (by rw [hρe₀, h4]) (by rw [hρe₀, h4]; omega)
  have hL₀fl : L₀ ≤ GSLit.fixedLayer J (zpowers e₀) := by
    unfold GSLit.fixedLayer
    rw [centralizer_zpowers_eq' e₀]
    have hpc : IsPComponent 2 (L₀.subgroupOf (J ⊓ centralizer ({e₀} : Set X))) :=
      CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hL₀J
        (inf_le_inf_right _ S.pair.1.2.1) hL₀pc
    have h1 : L₀.subgroupOf (J ⊓ centralizer ({e₀} : Set X)) ≤
        pLayer ↥(J ⊓ centralizer ({e₀} : Set X)) 2 := le_sSup hpc
    intro x hx
    exact ⟨⟨x, hL₀J hx⟩, h1 hx, rfl⟩
  have heq : L₀ = GSLit.fixedLayer J (zpowers e₀) :=
    eq_of_isPComponent_of_le_inf hL₀C hflC hL₀pc hflpc le_rfl hL₀fl hperf hL₀q
  have hnorm : ∀ y ∈ J, y * e₀ = e₀ * y → y ∈ normalizer (L₀ : Set X) := by
    intro y hy hye
    rw [heq]
    refine GSLit.mem_normalizer_fixedLayer (le_normalizer hy) ?_
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
      have h1 : y * e₀ ^ k * y⁻¹ = e₀ ^ k := by
        rw [(Commute.zpow_right hye k).eq, mul_inv_cancel_right]
      rw [h1]
      exact zpow_mem (mem_zpowers e₀) k
    · intro hz
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz
      have h1 : z = y⁻¹ * e₀ ^ k * y := by rw [hk]; group
      rw [h1]
      have h2 : y⁻¹ * e₀ ^ k * y = e₀ ^ k := by
        have h3 : Commute y⁻¹ e₀ := (Commute.inv_left hye)
        rw [(Commute.zpow_right h3 k).eq, inv_mul_cancel_right]
      rw [h2]
      exact zpow_mem (mem_zpowers e₀) k
  have hsD : (coreImage e he₀J).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨e₀, he₀J⟩ he₀E ω hωD)
  have hsDeq : (coreImage e he₀J).support = D :=
    Finset.eq_of_subset_of_card_le hsD (by rw [h4, S.card])
  have hker : E ≤ UnbalancedLayer.coreActionKernel L₀ := by
    intro y hyE
    have hyJ : y ∈ J := S.le hyE
    have hyN := hnorm y hyJ (hcomm y hyE e₀ he₀E)
    refine ⟨hyN, fun l hl => ?_⟩
    have hlJ : l ∈ J := (hL₀J hl).1
    have hw : l⁻¹ * y⁻¹ * l * y ∈ L₀ := by
      have h1 : y⁻¹ * l * y ∈ L₀ := by
        have h2 := (mem_normalizer_iff.mp (inv_mem hyN) l).mp hl
        rwa [inv_inv] at h2
      have h3 := mul_mem (inv_mem hl) h1
      rwa [show l⁻¹ * (y⁻¹ * l * y) = l⁻¹ * y⁻¹ * l * y by group] at h3
    obtain ⟨hlJ', hls⟩ := hsupp l hl
    have hys : (coreImage e hyJ).support ⊆ D := by
      intro ω hω
      by_contra hωD
      exact (Perm.mem_support.mp hω) (S.supp ⟨y, hyJ⟩ hyE ω hωD)
    have hdisj : Perm.Disjoint (coreImage e hlJ') (coreImage e hyJ) := by
      rw [Perm.disjoint_iff_disjoint_support]
      refine Finset.disjoint_left.mpr fun ω h1 h2 => ?_
      have h5 := hls h1
      rw [Finset.mem_compl, hsDeq] at h5
      exact h5 (hys h2)
    have hcm := hdisj.commute
    have hJw : l⁻¹ * y⁻¹ * l * y ∈ J :=
      mul_mem (mul_mem (mul_mem (inv_mem hlJ) (inv_mem hyJ)) hlJ) hyJ
    have hO : l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 ↥J).map J.subtype := by
      refine ⟨⟨_, hJw⟩, (QuotientGroup.eq_one_iff _).mp ?_, rfl⟩
      apply e.injective
      rw [map_one]
      apply Subtype.ext
      have h1 : ((⟨l⁻¹ * y⁻¹ * l * y, hJw⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) =
          ((⟨l, hlJ'⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)⁻¹ *
            ((⟨y, hyJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)⁻¹ *
            ((⟨l, hlJ'⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
            ((⟨y, hyJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := rfl
      rw [h1, map_mul, map_mul, map_mul, map_inv, map_inv]
      change (coreImage e hlJ')⁻¹ * (coreImage e hyJ)⁻¹ * coreImage e hlJ' *
        coreImage e hyJ = 1
      rw [show (coreImage e hlJ')⁻¹ * (coreImage e hyJ)⁻¹ * coreImage e hlJ' * coreImage e hyJ =
          (coreImage e hyJ * coreImage e hlJ')⁻¹ * (coreImage e hlJ' * coreImage e hyJ) by group,
        hcm.eq, inv_mul_cancel]
    exact inf_pPrimeCore_le (hL₀J.trans inf_le_left) (mem_inf.mpr ⟨hw, hO⟩)
  obtain ⟨F, DF, hFJ, hF4, hFsq, hDF, hdisj, hFs, hFE⟩ :=
    exists_commuting_four_subgroup S.nine_le e S.le S.isPGroup S.card S.supp
  have hDFc : DF ⊆ (coreImage e he₀J).supportᶜ := by
    intro ω hω
    rw [Finset.mem_compl]
    intro h
    exact Finset.disjoint_left.mp hdisj (hsD h) hω
  have hFL₀ : F ≤ L₀ := by
    intro x hx
    have hxJ : x ∈ J := hFJ hx
    refine hinv x hxJ ?_ ⟨1, by rw [pow_one, sq]; exact hFsq x hx⟩ ?_
    · exact (mem_centralizer_iff.mp (hFE hx) e₀ he₀E).symm
    · intro ω hω
      refine hDFc ?_
      by_contra hωF
      exact (Perm.mem_support.mp hω) (hFs ⟨x, hxJ⟩ hx ω hωF)
  exact ⟨L₀, F, hL₀J.trans inf_le_left, hL₀C, hL₀pc, ⟨χ₅⟩, hnorm, hker, hFL₀,
    klein_of_card_sq hF4 hFsq, ⟨DF, hDF, hFs⟩⟩

end Sig36

end CFSG.ComponentClassification.SolMax
