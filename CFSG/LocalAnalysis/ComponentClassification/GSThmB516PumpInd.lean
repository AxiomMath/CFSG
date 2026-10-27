module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpSq
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB51
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrTwoLocalTools

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Pump516

variable {Y : Type} [Group Y] [Finite Y]

theorem pumpUpAt_of_sq (hS : SchreierFor Blueprint.Catalog) (hInv : CF516PumpUpInv)
    (hY : SectionRank.IsKGroupCat Y) {L : Subgroup Y} (hL : IsComponent L) {β : Y}
    (hβ : ∃ n : ℕ, β ^ 2 ^ n = 1) (hN : β ∈ normalizer (L : Set Y))
    (hIH : CF516PumpUpAt Y L (β ^ 2)) : CF516PumpUpAt Y L β := by
  intro p f hp hp2 hf K hKLC hK hKt t htK ht2 J hJLC hJ hJt hβJ JB hJBJK hJBp hJsup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβγ : β ∈ centralizer ({β ^ 2} : Set Y) :=
    mem_centralizer_singleton_iff.mpr (Commute.self_pow β 2).eq
  set M := L ⊓ centralizer ({β ^ 2} : Set Y) with hM
  have hLβM : L ⊓ centralizer ({β} : Set Y) ≤ M :=
    inf_le_inf_left _ (centralizer_le_centralizer_sq β)
  have hKM : K ≤ M := hKLC.trans hLβM
  have hβM : β ∈ normalizer (M : Set Y) := mem_normalizer_inf hN (le_normalizer hβγ)
  set X₀ := M ⊔ zpowers β with hX₀
  have hMX : M ≤ X₀ := le_sup_left
  have hβX : β ∈ X₀ := mem_sup_right (mem_zpowers β)
  have hX₀N : X₀ ≤ normalizer (M : Set Y) := sup_le le_normalizer (zpowers_le.mpr hβM)
  have hX₀γ : X₀ ≤ centralizer ({β ^ 2} : Set Y) := sup_le inf_le_right (zpowers_le.mpr hβγ)
  have hX₀K : SectionRank.IsKGroupCat X₀ := hY.subgroup X₀
  have hXS := schreierSections_of_isKGroupCat hS hX₀K
  set β' : X₀ := ⟨β, hβX⟩ with hβ'
  have hβ2 : ∃ n : ℕ, β' ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hβ
    exact ⟨n, Subtype.ext (by simpa [hβ'] using hn)⟩
  have hγZ : β' ^ 2 ∈ center X₀ := mem_center_iff.mpr fun y => Subtype.ext (by
    simpa [hβ'] using mem_centralizer_singleton_iff.mp (hX₀γ y.2))
  have hAt : ∀ L₀ : Subgroup (X₀ ⧸ pPrimeCore 2 X₀), IsComponent L₀ →
      QuotientGroup.mk' (pPrimeCore 2 X₀) β' ∈ normalizer (L₀ : Set (X₀ ⧸ pPrimeCore 2 X₀)) →
        CF516PumpUpAt (X₀ ⧸ pPrimeCore 2 X₀) L₀ (QuotientGroup.mk' (pPrimeCore 2 X₀) β') := by
    intro L₀ hL₀ hN₀
    obtain ⟨n, hn⟩ := hβ2
    refine hInv _ (hX₀K.quotient _) L₀ hL₀ _ ⟨n, by rw [← map_pow, hn, map_one]⟩ hN₀ ?_
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 X₀) y
    rw [mem_centralizer_singleton_iff, ← map_pow, ← map_mul, ← map_mul,
      mem_center_iff.mp hγZ x]
  have hLβX : L ⊓ centralizer ({β} : Set Y) ≤ X₀ ⊓ centralizer ({β} : Set Y) :=
    le_inf (hLβM.trans hMX) inf_le_right
  have hn1 : ((L ⊓ centralizer ({β} : Set Y)).subgroupOf
      (X₀ ⊓ centralizer ({β} : Set Y))).Normal := by
    refine (normal_subgroupOf_iff_le_normalizer hLβX).mpr fun x hx => ?_
    have heq : L ⊓ centralizer ({β} : Set Y) = M ⊓ centralizer ({β} : Set Y) := by
      rw [hM, inf_assoc, inf_eq_right.mpr (centralizer_le_centralizer_sq β)]
    rw [heq]
    exact mem_normalizer_inf (hX₀N (mem_inf.mp hx).1) (le_normalizer (mem_inf.mp hx).2)
  have hK1 := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hKLC hLβX hn1.isSubnormal hK
  have hKC' : K.subgroupOf X₀ ≤ centralizer ({β'} : Set X₀) := by
    rw [← centralizer_subgroupOf_eq hβX]
    exact fun x hx => (mem_inf.mp (hKLC hx)).2
  have hK' : IsPComponent 2 ((K.subgroupOf X₀).subgroupOf (centralizer ({β'} : Set X₀))) := by
    rw [← centralizer_subgroupOf_eq hβX, ← inf_subgroupOf_left (centralizer ({β} : Set Y)) X₀]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hK1
  have htX : t ∈ X₀ := hMX (hKM htK)
  set t' : X₀ := ⟨t, htX⟩ with ht'
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have ht2' : t' * t' = 1 := Subtype.ext htt
  have htK' : t' * 1 ∈ K.subgroupOf X₀ := by rw [mul_one]; exact htK
  have hto : orderOf (t' * 1) = 2 := by rw [mul_one, ← Subgroup.orderOf_coe]; exact ht2
  have hβt : β ∈ centralizer ({t} : Set Y) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hKLC htK).2).symm
  have hJBβ : JB ≤ centralizer ({β} : Set Y) := fun x hx => (hKLC (mem_inf.mp (hJBJK hx)).2).2
  obtain ⟨hJ'D, hJ'2, hJBJ', hJ'sup, hβJ', ⟨eJ⟩⟩ := fixedLayer_sq_data hβ hN hβt hJLC hJ hβJ
    (hJBJK.trans inf_le_left) hJBβ hJBp hJsup
  set J' := GSLit.fixedLayer J (zpowers (β ^ 2)) with hJ'
  have hDX : M ⊓ centralizer ({t} : Set Y) ≤ X₀ ⊓ centralizer ({t} : Set Y) :=
    inf_le_inf_right _ hMX
  have hn2 : ((M ⊓ centralizer ({t} : Set Y)).subgroupOf
      (X₀ ⊓ centralizer ({t} : Set Y))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDX).mpr fun x hx =>
      mem_normalizer_inf (hX₀N (mem_inf.mp hx).1) (le_normalizer (mem_inf.mp hx).2)
  have hJ'X := UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hJ'D hDX hn2.isSubnormal
    hJ'2
  have hJ'C' : J'.subgroupOf X₀ ≤ centralizer ({t'} : Set X₀) := by
    rw [← centralizer_subgroupOf_eq htX]
    exact fun x hx => (mem_inf.mp (hJ'D hx)).2
  have hJ'' : IsPComponent 2 ((J'.subgroupOf X₀).subgroupOf (centralizer ({t'} : Set X₀))) := by
    rw [← centralizer_subgroupOf_eq htX, ← inf_subgroupOf_left (centralizer ({t} : Set Y)) X₀]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hJ'X
  have hJBX : JB ≤ X₀ := fun x hx => hMX (hKM (mem_inf.mp (hJBJK hx)).2)
  have hJ'Xle : J' ≤ X₀ := hJ'D.trans (inf_le_left.trans hMX)
  have hJBK' : JB.subgroupOf X₀ ≤ K.subgroupOf X₀ := fun x hx => (mem_inf.mp (hJBJK hx)).2
  have hJBJ'' : JB.subgroupOf X₀ ≤ J'.subgroupOf X₀ := fun x hx => hJBJ' hx
  have hJBp' : ⁅JB.subgroupOf X₀, JB.subgroupOf X₀⁆ = JB.subgroupOf X₀ := by
    apply map_injective X₀.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJBX, hJBp]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    have hJO : J ≤ oddCoreIn J := by simpa [hbot] using hJsup
    have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp
      (B5a.isPerfect_of_isPComponent_subgroupOf hJLC hJ)
    have hodd : Odd (Nat.card ↥(oddCoreIn J)) := by
      rw [oddCoreIn, card_map_of_injective J.subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    have h1 := eq_bot_of_perfect_of_le_odd hJp hJO hodd
    have := B5a.nontrivial_of_isPComponent_subgroupOf hJLC hJ
    rw [h1] at this
    exact not_nontrivial _ this
  have hJB1' : JB.subgroupOf X₀ ≠ ⊥ := by
    intro hbot
    apply hJB1
    rw [← map_subgroupOf_eq_of_le hJBX, hbot, Subgroup.map_bot]
  have hJsup' : J'.subgroupOf X₀ ≤ JB.subgroupOf X₀ ⊔ oddCoreIn (J'.subgroupOf X₀) := by
    rw [← map_le_map_iff_of_injective X₀.subtype_injective, Subgroup.map_sup,
      map_subgroupOf_eq_of_le hJ'Xle, map_subgroupOf_eq_of_le hJBX, oddCoreIn,
      pPrimeCore_map_subgroupOf 2 J' X₀ hJ'Xle]
    exact hJ'sup
  have hβJ'' : β' ∈ coreActionKernel (J'.subgroupOf X₀) := by
    refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_normalizer_iff.mp (mem_coreActionKernel.mp hβJ').1 y
    · rw [← mem_map_iff_mem X₀.subtype_injective, pPrimeCore_map_subgroupOf 2 J' X₀ hJ'Xle]
      exact (mem_coreActionKernel.mp hβJ').2 j hj
  have eK : ↥(K.subgroupOf X₀) ⧸ pPrimeCore 2 ↥(K.subgroupOf X₀) ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe (hKM.trans hMX))
  have hKt' : (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = p ^ f ∧ Nonempty (↥(K.subgroupOf X₀) ⧸ pPrimeCore 2
          ↥(K.subgroupOf X₀) ≃* StatedProj (StatedSL 4 F))) ∨
      (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
        Nonempty (↥(K.subgroupOf X₀) ⧸ pPrimeCore 2 ↥(K.subgroupOf X₀) ≃*
          StatedProj (StatedSU 4 (p ^ f) F))) := by
    rcases hKt with ⟨h4, F, i1, i2, hF, ⟨e⟩⟩ | ⟨h4, F, i1, hF, ⟨e⟩⟩
    · exact Or.inl ⟨h4, F, i1, i2, hF, ⟨eK.trans e⟩⟩
    · exact Or.inr ⟨h4, F, i1, hF, ⟨eK.trans e⟩⟩
  have hJt' : Blueprint.LieModel (↥(J'.subgroupOf X₀) ⧸ pPrimeCore 2 ↥(J'.subgroupOf X₀))
      .PSL 2 p (2 * f) :=
    OddQuot.lieModel_of_equiv (((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe hJ'Xle)).trans eJ).symm) hJt
  obtain ⟨N₀, hN₀, hKN₀, hN₀K⟩ := exists_pComponent_of_pumpUp hXS hAt hβ2 ht2' (one_mem _) hKC'
    hK' hJ'C' hJ'' htK' hto hJBK' hJBJ'' hJBp' hJB1' hJsup' hβJ'' hp hp2 hf hKt' hJt'
  set N := N₀.map X₀.subtype with hNdef
  have hNX : N ≤ X₀ := map_subtype_le _
  have hN2 : IsPComponent 2 (N.subgroupOf X₀) := by
    rwa [hNdef, show (N₀.map X₀.subtype).subgroupOf X₀ = N₀ from
      comap_map_eq_self_of_injective X₀.subtype_injective N₀]
  have : Group.IsPerfect N := B5a.isPerfect_of_isPComponent_subgroupOf hNX hN2
  have hNM : N ≤ M := LBalance.Asm.le_of_perfect_le_sup_zpowers hβM hNX
  have hNM2 : IsPComponent 2 (N.subgroupOf M) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hNM hMX hN2
  have hKN : K ≤ N := fun k hk => ⟨⟨k, hKM.trans hMX hk⟩, hKN₀ hk, rfl⟩
  have hNKO : N ≤ K ⊔ oddCoreIn N := by
    have h1 : N ≤ K ⊔ oddCoreIn X₀ := by
      refine (map_mono hN₀K).trans ?_
      rw [Subgroup.map_sup, subgroupOf_map_subtype]
      exact sup_le_sup_right inf_le_left _
    intro x hx
    have hKN' : K ≤ normalizer (oddCoreIn X₀ : Set Y) := fun k hk =>
      Over516.normalizer_le_normalizer_oddCoreIn X₀ (le_normalizer (hKM.trans hMX hk))
    have h2 : x ∈ ((K ⊔ oddCoreIn X₀ : Subgroup Y) : Set Y) := h1 hx
    rw [coe_mul_of_left_le_normalizer_right _ _ hKN'] at h2
    obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.mp h2
    have hoN : o ∈ N := by
      have := mul_mem (inv_mem (hKN hk)) hx
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left hk) (mem_sup_right (Over516.inf_oddCoreIn_le hNX ⟨hoN, ho⟩))
  have hNt : (p ^ f % 4 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F),
        Fintype.card F = p ^ f ∧ Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* StatedProj (StatedSL 4 F))) ∨
      (p ^ f % 4 = 1 ∧ ∃ (F : Type) (_ : Field F), UnitaryFieldData p f F ∧
        Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* StatedProj (StatedSU 4 (p ^ f) F))) := by
    obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hKN
      (le_antisymm (sup_le hKN (map_subtype_le _)) hNKO)
    rcases hKt with ⟨h4, F, i1, i2, hF, ⟨eF⟩⟩ | ⟨h4, F, i1, hF, ⟨eF⟩⟩
    · exact Or.inl ⟨h4, F, i1, i2, hF, ⟨e.symm.trans eF⟩⟩
    · exact Or.inr ⟨h4, F, i1, hF, ⟨e.symm.trans eF⟩⟩
  have hNL : N = L := hIH p f hp hp2 hf N hNM hNM2 hNt t (hKN htK) ht2 J hJLC hJ hJt
    (pow_mem hβJ 2) JB (le_inf (hJBJK.trans inf_le_left) ((hJBJK.trans inf_le_right).trans hKN))
    hJBp hJsup
  have hLγ : L ≤ centralizer ({β ^ 2} : Set Y) := hNL ▸ (hNM.trans inf_le_right)
  exact hInv Y hY L hL β hβ hN hLγ p f hp hp2 hf K hKLC hK hKt t htK ht2 J hJLC hJ hJt hβJ JB
    hJBJK hJBp hJsup

end Pump516

theorem Pump516.pumpUpAt_of_inv (hS : SchreierFor Blueprint.Catalog) (hInv : CF516PumpUpInv)
    (n : ℕ) : ∀ (Z : Type) [Group Z] [Finite Z], SectionRank.IsKGroupCat Z →
      ∀ L : Subgroup Z, IsComponent L → ∀ β : Z, β ^ 2 ^ n = 1 →
        β ∈ normalizer (L : Set Z) → CF516PumpUpAt Z L β := by
  induction n with
  | zero =>
    intro Z _ _ hZ L hL β hβ hN
    have hβ1 : β = 1 := by simpa using hβ
    refine hInv Z hZ L hL β ⟨0, hβ⟩ hN fun x _ => ?_
    rw [hβ1, one_pow]
    exact mem_centralizer_singleton_iff.mpr (by rw [mul_one, one_mul])
  | succ n ih =>
    intro Z _ _ hZ L hL β hβ hN
    exact Pump516.pumpUpAt_of_sq hS hInv hZ hL ⟨n + 1, hβ⟩ hN (ih Z hZ L hL (β ^ 2)
      (by rw [← pow_mul, ← pow_succ']; exact hβ) (pow_mem hN 2))

theorem cf516PumpUp_of_inv (hS : SchreierFor Blueprint.Catalog) (hInv : CF516PumpUpInv) :
    CF516PumpUp :=
  fun Z _ _ hZ L hL β ⟨n, hn⟩ hN => Pump516.pumpUpAt_of_inv hS hInv n Z hZ L hL β hn hN

end CFSG.ComponentClassification.GSThmB
