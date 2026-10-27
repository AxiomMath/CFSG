module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3a
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3d

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Sub71Aux

theorem subMk_mem_map_iff {Y : Subgroup X} (hBY : h.secB0 y ≤ Y) (w : ↥(h.secSub y)) :
    h.subMk y w ∈ (Y.subgroupOf (h.secSub y)).map (h.subMk y) ↔ (w : X) ∈ Y := by
  constructor
  · intro hw
    obtain ⟨v, hv, hvw⟩ := mem_map.mp hw
    have hvw' : h.secMk y ⟨v, h.secSub_le_G0 y v.2⟩ = h.secMk y ⟨w, h.secSub_le_G0 y w.2⟩ :=
      congrArg Subtype.val hvw
    have h1 : h.secMk y ⟨w, h.secSub_le_G0 y w.2⟩ ∈ h.secImage y Y := by
      rw [← hvw']
      exact mem_map_of_mem _ (show (⟨v, h.secSub_le_G0 y v.2⟩ : ↥(h.secG0 y)) ∈
        Y.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr (mem_subgroupOf.mp hv))
    exact (Hyp52.secMk_mem_secImage_iff hBY _).mp h1
  · intro hw
    exact mem_map_of_mem _ (show w ∈ Y.subgroupOf (h.secSub y) from mem_subgroupOf.mpr hw)

theorem isPGroup_B2_of_involution {g : ↥(h.secG0 y)} (hg1 : h.secMk y g ≠ 1)
    (hg2 : h.secMk y g * h.secMk y g = 1) : IsPGroup 2 (B2 h y g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (h.secMk y g) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (h.isPGroup_secB0 y)
  refine IsPGroup.of_card (n := n + 1) ?_
  rw [card_B2 hord, hn, pow_succ, mul_comm]

theorem centralizer_subMk_eq {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1) :
    centralizer ({h.subMk y ⟨g, hgH⟩} : Set ↥(h.secSubImg y)) =
      ((normalizer (B2 h y g : Set X)).subgroupOf (h.secSub y)).map (h.subMk y) := by
  ext z
  obtain ⟨w, rfl⟩ := h.subMk_surjective y z
  rw [subMk_mem_map_iff ((secB0_le_B2 g).trans le_normalizer) w, mem_centralizer_singleton_iff]
  have hw := mem_normalizer_B2_iff hg1 hg2 (⟨w, h.secSub_le_G0 y w.2⟩ : ↥(h.secG0 y))
  refine Iff.trans ?_ hw.symm
  constructor
  · intro hc
    exact congrArg Subtype.val hc
  · intro hc
    exact Subtype.ext hc

end Sub71Aux

theorem centralizer_subQ_eq {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1) :
    centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)) =
      ((normalizer (B2 h y g : Set X)).subgroupOf (h.secSub y)).map (h.subQ y) := by
  have h1 := OddQuot.centralizer_singleton_map_eq (H := ↥(h.secSubImg y))
    (t := h.subMk y ⟨g, hgH⟩) (Subtype.ext hg2)
  rw [Sub71Aux.centralizer_subMk_eq hgH hg1 hg2, Subgroup.map_map] at h1
  exact h1

theorem isPComponent_subQ_of_normalizer_B2 {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1) {N : Subgroup X}
    (hNN : N ≤ normalizer (B2 h y g : Set X)) (hNc : N ≤ centralizer (h.secB0 y : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (normalizer (B2 h y g : Set X)))) :
    IsPComponent 2 (((N.subgroupOf (h.secSub y)).map (h.subQ y)).subgroupOf
      (centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNL : N ≤ h.secL0 y :=
    Sub58.le_layerIn_centralizer_of_isPComponent (Sub71Aux.isPGroup_B2_of_involution hg1 hg2)
      (secB0_le_B2 g) (B2_le_G0 g) hNN hN
  have hNH : N ≤ h.secSub y := hNL.trans (h.secL0_le_secSub y)
  set Y := normalizer (B2 h y g : Set X) ⊓ h.secSub y with hY
  have hNY : N ≤ Y := le_inf hNN hNH
  have hYH : Y ≤ h.secSub y := inf_le_right
  have hYG : Y ≤ h.secG0 y := hYH.trans (h.secSub_le_G0 y)
  have h1 : IsPComponent 2 (N.subgroupOf Y) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hNY inf_le_left hN
  have h2 := Hyp52.secImage_isPComponent hNY hYG hNc h1
  have hYI : h.secImage y Y ≤ h.secSubImg y := Hyp52.secImage_mono hYH
  have h3 : IsPComponent 2 (((h.secImage y N).subgroupOf (h.secSubImg y)).subgroupOf
      ((h.secImage y Y).subgroupOf (h.secSubImg y))) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hYI 2 Nat.prime_two).mpr h2
  have hLX : (h.secImage y N).subgroupOf (h.secSubImg y) ≤
      (h.secImage y Y).subgroupOf (h.secSubImg y) :=
    fun z hz => mem_subgroupOf.mpr (Hyp52.secImage_mono hNY (mem_subgroupOf.mp hz))
  have h4 := OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))
    OddQuot.not_two_dvd_card_ker hLX h3
  rw [← Hyp52.map_subQ hNH, ← Hyp52.map_subQ hYH, hY, inf_subgroupOf_right] at h4
  rw [centralizer_subQ_eq hgH hg1 hg2]
  exact h4

theorem card_S_inf_normalizer_B2_sub {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y)
    (hgS : (g : X) ∈ h.S) (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1) :
    Nat.card ↥(((h.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ⊓
        centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y))) * Nat.card (h.secB0 y) =
      Nat.card ↥(h.S ⊓ normalizer (B2 h y g : Set X) ⊓ h.secG0 y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := h.S ⊓ normalizer (B2 h y g : Set X) ⊓ h.secG0 y with hY
  have hBS : h.secB0 y ≤ h.S := (h.secB0_le_B y).trans (h.B_le.trans inf_le_left)
  have hBN : h.secB0 y ≤ normalizer (B2 h y g : Set X) := (secB0_le_B2 g).trans le_normalizer
  have hBY : h.secB0 y ≤ Y := le_inf (le_inf hBS hBN) (h.secB0_le_G0 y)
  have hYS : Y ≤ h.S ⊓ h.secG0 y := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hYH : Y ≤ h.secSub y := hYS.trans (h.S_inf_le_secSub y)
  have hY2 : IsPGroup 2 Y := h.isPGroup_S.to_le (inf_le_left.trans inf_le_left)
  have hA : IsPGroup 2 (h.subS y) :=
    (((h.isPGroup_S).comap_subtype (K := h.secG0 y)).map (h.secMk y)).comap_subtype
  have hgA : h.subMk y ⟨g, hgH⟩ ∈ h.subS y :=
    mem_subgroupOf.mpr (mem_map_of_mem _ (show g ∈ h.S.subgroupOf (h.secG0 y) from hgS))
  have h1 := map_inf_centralizer_of_isPGroup hA hgA
  have hAC : h.subS y ⊓ centralizer ({h.subMk y ⟨g, hgH⟩} : Set ↥(h.secSubImg y)) =
      (Y.subgroupOf (h.secSub y)).map (h.subMk y) := by
    rw [Sub71Aux.centralizer_subMk_eq hgH hg1 hg2]
    apply le_antisymm
    · rintro z ⟨hzS, hzN⟩
      obtain ⟨w, rfl⟩ := h.subMk_surjective y z
      have hwN : (w : X) ∈ normalizer (B2 h y g : Set X) :=
        (Sub71Aux.subMk_mem_map_iff hBN w).mp hzN
      have hwS : (w : X) ∈ h.S :=
        (Hyp52.secMk_mem_secImage_iff hBS ⟨w, h.secSub_le_G0 y w.2⟩).mp (mem_subgroupOf.mp hzS)
      exact mem_map_of_mem _ (show w ∈ Y.subgroupOf (h.secSub y) from
        mem_subgroupOf.mpr (mem_inf.mpr ⟨mem_inf.mpr ⟨hwS, hwN⟩, h.secSub_le_G0 y w.2⟩))
    · intro z hz
      obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
      have hwY : (w : X) ∈ Y := mem_subgroupOf.mp hw
      have hwSN := mem_inf.mp (mem_inf.mp hwY).1
      refine mem_inf.mpr ⟨?_, mem_map_of_mem _ (show w ∈ _ from mem_subgroupOf.mpr hwSN.2)⟩
      exact mem_subgroupOf.mpr (mem_map_of_mem _ (show (⟨w, h.secSub_le_G0 y w.2⟩ : ↥(h.secG0 y)) ∈
        h.S.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr hwSN.1))
  have e : ((h.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ⊓
      centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)) =
        (Y.subgroupOf (h.secSub y)).map (h.subQ y) := by
    have h2 : (Y.subgroupOf (h.secSub y)).map (h.subQ y) =
        ((Y.subgroupOf (h.secSub y)).map (h.subMk y)).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) := (Subgroup.map_map _ _ _).symm
    rw [Hyp52.map_subQ_S, h2, ← hAC]
    exact h1.symm
  rw [e]
  exact Hyp52.card_map_subQ_mul hY2 hBY hYH

theorem exists_lift_sub {t : h.subQuot y}
    (ht : t ∈ ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y)) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) :
    ∃ g : ↥(h.secG0 y), ∃ hgH : (g : X) ∈ h.secSub y, (g : X) ∈ h.P ∧ h.subQ y ⟨g, hgH⟩ = t ∧
      h.secMk y g ≠ 1 ∧ h.secMk y g * h.secMk y g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwP, rfl⟩ := mem_map.mp ht
  have hwP' : (w : X) ∈ h.P ⊓ h.secG0 y := mem_subgroupOf.mp hwP
  have hwP2 : (w : X) ∈ h.P := (mem_inf.mp hwP').1
  refine ⟨⟨w, h.secSub_le_G0 y w.2⟩, w.2, hwP2, rfl, fun h1 => ht1 ?_, ?_⟩
  · have h2 : h.subMk y w = 1 := Subtype.ext h1
    show QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) (h.subMk y w) = 1
    rw [h2, map_one]
  · have hP2 : IsPGroup 2 ((h.secImage y h.P).subgroupOf (h.secSubImg y)) :=
      (((h.isPGroup_S.to_le inf_le_left).comap_subtype).map _).comap_subtype
    have hmem : h.subMk y w ∈ (h.secImage y h.P).subgroupOf (h.secSubImg y) :=
      mem_subgroupOf.mpr (mem_map_of_mem _ (show (⟨w, h.secSub_le_G0 y w.2⟩ : ↥(h.secG0 y)) ∈
        h.P.subgroupOf (h.secG0 y) from mem_subgroupOf.mpr hwP2))
    have h3 : h.subMk y w * h.subMk y w = 1 := by
      refine OddQuot.injOn_of_isPGroup hP2 (mul_mem hmem hmem) (one_mem _) ?_
      rw [map_mul, map_one]
      exact ht2
    exact congrArg Subtype.val h3

theorem not_fixedLayer_le_sub (hc : h.SecCond y)
    (hLB : Assembly.ComponentType.LocalBProperty (h.subQuot y)) (hZJ : center (OddBar h.J) = ⊥)
    {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y) (hgP : (g : X) ∈ h.P)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1)
    (ht : orderOf (h.subQ y ⟨g, hgH⟩) = 2) {M : Subgroup (h.subQuot y)}
    (hMC : M ≤ centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))
    (hM : IsComponent (M.subgroupOf (centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))))
    (hMa : conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩) ≠ M)
    (hJM : ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤
      M ⊔ conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩))
    {N : Subgroup X} (hNN : N ≤ normalizer (B2 h y g : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (normalizer (B2 h y g : Set X))))
    (hNa : conjugate N h.a = N) : ¬ GSLit.fixedLayer h.J (B2 h y g) ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hJN
  set B₂ := B2 h y g with hB₂
  set C := centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)) with hC
  have haH : h.a ∈ h.secSub y := hc.a_mem_secSub
  have hB₂P : B₂ ≤ h.P := B2_le_P hgP hg2
  have hB₂2 : IsPGroup 2 B₂ := (h.isPGroup_S.to_le inf_le_left).to_le hB₂P
  have hB₂C : B₂ ≤ coreActionKernel h.J := hB₂P.trans inf_le_right
  have hNlay : N ≤ layerIn (normalizer (B₂ : Set X)) := by
    intro n hn
    have hle : N.subgroupOf (normalizer (B₂ : Set X)) ≤ pLayer ↥(normalizer (B₂ : Set X)) 2 :=
      le_sSup (show N.subgroupOf (normalizer (B₂ : Set X)) ∈
        {L : Subgroup ↥(normalizer (B₂ : Set X)) | IsPComponent 2 L} from hN)
    exact ⟨⟨n, hNN hn⟩, hle (mem_subgroupOf.mpr hn), rfl⟩
  have hbal := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) B₂ hB₂2
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at hbal
  have hNcB₂ : N ≤ centralizer (B₂ : Set X) := hNlay.trans (hbal.trans (map_subtype_le _))
  have hNc : N ≤ centralizer (h.secB0 y : Set X) :=
    hNcB₂.trans (centralizer_le (SetLike.coe_subset_coe.mpr (secB0_le_B2 g)))
  set N' := (N.subgroupOf (h.secSub y)).map (h.subQ y) with hN'
  have hpc := isPComponent_subQ_of_normalizer_B2 hgH hg1 hg2 hNN hNc hN
  have hWt : normalizer ((zpowers (h.subQ y ⟨g, hgH⟩) : Subgroup (h.subQuot y)) :
      Set (h.subQuot y)) = C := UnbalancedCorr.normalizer_zpowers_eq_centralizer ht
  have hN'C : N' ≤ C := by
    rw [hC, centralizer_subQ_eq hgH hg1 hg2]
    exact map_mono fun w hw => mem_subgroupOf.mpr (hNN (mem_subgroupOf.mp hw))
  have hcomp : IsComponent (N'.subgroupOf C) := by
    rw [← hC, ← hWt] at hpc
    rw [← hWt]
    have hne : (zpowers (h.subQ y ⟨g, hgH⟩) : Subgroup (h.subQuot y)) ≠ ⊥ := by
      intro h0
      rw [zpowers_eq_bot] at h0
      rw [h0, orderOf_one] at ht
      exact absurd ht (by norm_num)
    have h2 : IsPGroup 2 (zpowers (h.subQ y ⟨g, hgH⟩)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    exact (AssemblyBPredicates.isComponentOf_top_iff_native _).mp
      (hLB _ hne h2 _ (isTwoPComponent_of_isPComponent' hpc))
  have hN'a : conjugate N' (h.subQ y ⟨h.a, haH⟩) = N' := by
    rw [hN', ← map_conjugate, conjugate_subgroupOf_eq]
    simp only
    rw [hNa]
  have hcomm := commutator_sup_eq_bot_of_components hN'C hMC hcomp hM hN'a hMa
  have hJq : IsQuasisimple (h.J ⧸ pPrimeCore 2 h.J) := h.isQuasisimple_J
  have hB₀B₂ : h.secB0 y ≤ B₂ := secB0_le_B2 g
  have hnest := (GSLit.fixedLayer_nested hJq hB₂C hB₂2 hB₀B₂).1
  set T := ((GSLit.fixedLayer h.J B₂).subgroupOf (h.secSub y)).map (h.subQ y) with hT
  have hTJ : T ≤ M ⊔ conjugate M (h.subQ y ⟨h.a, haH⟩) :=
    (map_mono fun w hw => mem_subgroupOf.mpr (hnest (mem_subgroupOf.mp hw))).trans hJM
  have hTN : T ≤ N' := map_mono fun w hw => mem_subgroupOf.mpr (hJN (mem_subgroupOf.mp hw))
  have hJB₂a : B₂ ≤ centralizer ({h.a} : Set X) :=
    hB₂P.trans (inf_le_left.trans (h.S_le.trans inf_le_left))
  have hperf : Group.IsPerfect (GSLit.fixedLayer h.J B₂) :=
    B5a.isPerfect_of_isPComponent_subgroupOf
      ((GSLit.fixedLayer_le_inf h.J B₂).trans (inf_le_inf_right _ h.J_le))
      (GSLit.fixedLayer_isPComponent h.J_le (id h.isPComponent_J).choose_spec.2.1 hJB₂a hB₂C
        hB₂2 hJq)
  have hJB₂H : GSLit.fixedLayer h.J B₂ ≤ h.secSub y := hnest.trans (h.secJ0_le_secSub y)
  have hTperf : Group.IsPerfect T := by
    have : Group.IsPerfect ((GSLit.fixedLayer h.J B₂).subgroupOf (h.secSub y)) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJB₂H).symm.toMonoidHom)
        (subgroupOfEquivOfLe hJB₂H).symm.surjective
    exact Group.IsPerfect.map _
  have hTbot : T = ⊥ := by
    have h1 : ⁅T, T⁆ = T := Subgroup.commutator_eq_self
    have h2 : ⁅T, T⁆ ≤ ⁅M ⊔ conjugate M (h.subQ y ⟨h.a, haH⟩), N'⁆ := commutator_mono hTJ hTN
    rw [hcomm, le_bot_iff, h1] at h2
    exact h2
  obtain ⟨z, hzD, hzS, hz2⟩ := h.exists_involution_D_center
  have hzJ : z ∈ h.J := (mem_inf.mp hzD).2
  have hzB₂ : z ∈ centralizer (B₂ : Set X) := by
    rw [mem_centralizer_iff]
    intro b hb
    exact hzS b ((hB₂P.trans inf_le_left) hb)
  have hzT : z ∈ GSLit.fixedLayer h.J B₂ := by
    rw [GSLit.fixedLayer_eq_closure hJq hB₂C hB₂2]
    exact subset_closure ⟨mem_inf.mpr ⟨hzJ, hzB₂⟩, 1, by rw [hz2, pow_one]⟩
  have hzH : z ∈ h.secSub y := hJB₂H hzT
  have hθz : h.subQ y ⟨z, hzH⟩ = 1 := by
    have : h.subQ y ⟨z, hzH⟩ ∈ T := mem_map_of_mem _ (show (⟨z, hzH⟩ : ↥(h.secSub y)) ∈
      (GSLit.fixedLayer h.J B₂).subgroupOf (h.secSub y) from hzT)
    rwa [hTbot, mem_bot] at this
  have hzsq : z ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← hz2]
    exact pow_orderOf_eq_one z
  have hzB₀ : z ∈ h.secB0 y := Hyp52.subQ_eq_one_of_two (w := ⟨z, hzH⟩) (k := 1) hzsq hθz
  have hzP : z ∈ h.D ⊓ h.P := mem_inf.mpr ⟨hzD, h.secB0_le_P hzB₀⟩
  rw [h.D_inf_P_eq_bot hZJ, mem_bot] at hzP
  rw [hzP, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

theorem not_isoCorrSub_B2_sub (hc : h.SecCond y)
    (hLB : Assembly.ComponentType.LocalBProperty (h.subQuot y)) (hZJ : center (OddBar h.J) = ⊥)
    {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y) (hgP : (g : X) ∈ h.P)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1)
    (ht : orderOf (h.subQ y ⟨g, hgH⟩) = 2) {M : Subgroup (h.subQuot y)}
    (hMC : M ≤ centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))
    (hM : IsComponent (M.subgroupOf (centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))))
    (hMa : conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩) ≠ M)
    (hJM : ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤
      M ⊔ conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩))
    (L : Subgroup X) : ¬ IsoCorrSub h.a h.J (B2 h y g) L := by
  rintro ⟨hLN, hLpc, hLa, hsup, -⟩
  exact not_fixedLayer_le_sub hc hLB hZJ hgH hgP hg1 hg2 ht hMC hM hMa hJM hLN hLpc hLa
    (hsup ▸ le_sup_left)

theorem conjugate_K_ne_of_B2_sub (hc : h.SecCond y)
    (hLB : Assembly.ComponentType.LocalBProperty (h.subQuot y)) (hZJ : center (OddBar h.J) = ⊥)
    {g : ↥(h.secG0 y)} (hgH : (g : X) ∈ h.secSub y) (hgP : (g : X) ∈ h.P)
    (hg1 : h.secMk y g ≠ 1) (hg2 : h.secMk y g * h.secMk y g = 1)
    (ht : orderOf (h.subQ y ⟨g, hgH⟩) = 2) {M : Subgroup (h.subQuot y)}
    (hMC : M ≤ centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))
    (hM : IsComponent (M.subgroupOf (centralizer ({h.subQ y ⟨g, hgH⟩} : Set (h.subQuot y)))))
    (hMa : conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩) ≠ M)
    (hJM : ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤
      M ⊔ conjugate M (h.subQ y ⟨h.a, hc.a_mem_secSub⟩))
    (h₂ : Hyp52 X) (ha : h₂.a = h.a) (hJ : h₂.J = h.J) (hB : h₂.B = B2 h y g) :
    conjugate h₂.K h₂.a ≠ h₂.K := by
  intro hKa
  obtain ⟨hKW, hKpc⟩ := h₂.isPComponent_K
  have hlay : h₂.K = layerIn (normalizer (h₂.B : Set X)) := by
    rw [← h₂.layer_eq_K, hKa, sup_idem]
  have hJK : GSLit.fixedLayer h₂.J h₂.B ≤ h₂.K := by
    rw [hlay, ← h₂.conjClosure_eq]
    refine le_iSup₂_of_le (1 : X) (one_mem _) fun w hw => ?_
    rw [mem_conjugate_iff, one_mul, inv_one, mul_one]
    exact hw
  rw [ha, hJ, hB] at *
  exact not_fixedLayer_le_sub hc hLB hZJ hgH hgP hg1 hg2 ht hMC hM hMa hJM hKW hKpc hKa hJK

end Seven

end CFSG.ComponentClassification.GSThmB
