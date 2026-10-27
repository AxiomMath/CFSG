module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25Quot
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25Diag

public section

namespace CFSG.ComponentClassification.GrSLit.Sol25

open CFSG Subgroup CFSG.LocalCores CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {S T : Subgroup G}

theorem commutatorElement_mem_of_mem_pCore (hS2 : ∀ s ∈ S, s * s = 1)
    (hST : S ≤ centralizer (T : Set G)) {y d : ↥(centralizer (T : Set G))}
    (hy : solπ T y ∈ pCore 2 (QC T))
    (hd : d ∈ (solD S T).subgroupOf (centralizer (T : Set G))) :
    ⁅y, d⁆ ∈ pPrimeCore 2 ↥(centralizer (T : Set G)) := by
  have h := commutator_mem_commutator hy (mem_map_of_mem (solπ T) hd)
  rw [commutator_pCore_imageD hS2 hST, mem_bot, ← map_commutatorElement] at h
  exact (QuotientGroup.eq_one_iff _).mp h

theorem commutator_O22_le (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G)) :
    ⁅((pCore 2 (↥(centralizer (T : Set G)) ⧸ pPrimeCore 2 ↥(centralizer (T : Set G)))).comap
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer (T : Set G))))).map
        (centralizer (T : Set G)).subtype, solD S T⁆ ≤
      (pPrimeCore 2 ↥(centralizer (T : Set G))).map (centralizer (T : Set G)).subtype := by
  rw [commutator_le]
  rintro _ ⟨y, hy, rfl⟩ d hd
  have h := commutatorElement_mem_of_mem_pCore hS2 hST (y := y)
    (d := ⟨d, (mem_inf.mp hd).2⟩) hy (mem_subgroupOf.mpr hd)
  exact ⟨_, h, rfl⟩

theorem commutator_pCore_eq_bot (hS2 : ∀ s ∈ S, s * s = 1)
    (hST : S ≤ centralizer (T : Set G)) :
    ⁅(pCore 2 ↥(centralizer (T : Set G))).map (centralizer (T : Set G)).subtype, solD S T⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff, commutator_le]
  rintro _ ⟨y, hy, rfl⟩ d hd
  set d' : ↥(centralizer (T : Set G)) := ⟨d, (mem_inf.mp hd).2⟩
  have hle : (pCore 2 ↥(centralizer (T : Set G))).map (solπ T) ≤ pCore 2 (QC T) :=
    le_sSup ⟨pCore_normal.map _ (QuotientGroup.mk'_surjective _), pCore_isPGroup.map _⟩
  have h1 := commutatorElement_mem_of_mem_pCore hS2 hST (y := y) (d := d')
    (hle (mem_map_of_mem _ hy)) (mem_subgroupOf.mpr hd)
  have h2 : ⁅y, d'⁆ ∈ pCore 2 ↥(centralizer (T : Set G)) := by
    rw [show ⁅y, d'⁆ = y * (d' * y⁻¹ * d'⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem hy (pCore_normal.conj_mem _ (inv_mem hy) d')
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := ↥(centralizer (T : Set G))) ⟨_, h2⟩
  have h3 : ⁅y, d'⁆ = 1 := eq_one_of_mem_odd_of_pow
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1 (n := n) (congrArg Subtype.val hn)
  rw [mem_bot]
  exact congrArg Subtype.val h3

theorem commutator_le_of_le_normalizer {X : Type*} [Group X] {L B : Subgroup X}
    (hBN : B ≤ normalizer (L : Set X)) : ⁅L, B⁆ ≤ L := by
  rw [commutator_le]
  intro l hl b hb
  rw [show ⁅l, b⁆ = l * (b * l⁻¹ * b⁻¹) by rw [commutatorElement_def]; group]
  exact mul_mem hl ((mem_normalizer_iff.mp (hBN hb) l⁻¹).mp (inv_mem hl))

omit [Finite G] in
theorem mem_normalizer_subgroupOf {H L : Subgroup G} {c : ↥H}
    (hc : (c : G) ∈ normalizer (L : Set G)) : c ∈ normalizer (L.subgroupOf H : Set ↥H) := by
  rw [mem_normalizer_iff] at hc ⊢
  intro x
  rw [mem_subgroupOf, mem_subgroupOf]
  simpa using hc x

theorem inf_le_oddIn {L C : Subgroup G} (hLC : L ≤ C) :
    (pPrimeCore 2 C).map C.subtype ⊓ L ≤ (pPrimeCore 2 L).map L.subtype :=
  le_map_pPrimeCore inf_le_right (fun _ hh _ hd => mem_inf.mpr
    ⟨GrS4.conj_mem_oddIn (hLC hh) (mem_inf.mp hd).1,
      mul_mem (mul_mem hh (mem_inf.mp hd).2) (inv_mem hh)⟩)
    ((odd_card_map_pPrimeCore C).of_dvd_nat (card_dvd_of_le inf_le_left))

theorem oddIn_le_of_isPComponent {M C : Subgroup G} (hMC : M ≤ C)
    (hM : IsPComponent 2 (M.subgroupOf C)) :
    (pPrimeCore 2 M).map M.subtype ≤ (pPrimeCore 2 C).map C.subtype := by
  rw [← pPrimeCore_map_subgroupOf 2 M C hMC]
  obtain ⟨-, -, hsn, -, -⟩ := hM
  exact map_mono (Walter.map_pPrimeCore_le_of_isSubnormal hsn)

omit [Finite G] in
theorem commutator_eq_of_ne_bot {X : Type*} [Group X] {K B : Subgroup X} (hK : IsQuasisimple K)
    (hB : B ≤ normalizer (K : Set X)) (hne : ⁅K, B⁆ ≠ ⊥) : ⁅K, B⁆ = K := by
  have hle : ⁅K, B⁆ ≤ K := commutator_le_of_le_normalizer hB
  have hnorm : (⁅K, B⁆.subgroupOf K).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hle]
    exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer (commutator_le_sup K B)).mp
      (commutator_normal_in_sup K B))
  rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hK hnorm with htop | hcen
  · exact le_antisymm hle (subgroupOf_eq_top.mp htop)
  · exfalso
    refine hne (LocalAnalysis.ComponentInitial.perfect_double_commutator
      (isPerfect_iff.mp hK.1) ?_)
    rw [commutator_eq_bot_iff_le_centralizer]
    intro n hn k hk
    have hz : (⟨n, hle hn⟩ : K) ∈ center K := hcen (mem_subgroupOf.mpr hn)
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)

theorem solD_le_normalizer (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G))
    {L : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G)))) :
    solD S T ≤ normalizer (L : Set G) := by
  intro d hd
  have hd' : (⟨d, (mem_inf.mp hd).2⟩ : ↥(centralizer (T : Set G))) ∈
      (solD S T).subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hd
  exact mem_normalizer_of_image hLC hL
    (imageD_le_normalizer hS2 hST (isComponent_image hL) (mem_map_of_mem _ hd'))

theorem commutator_le_oddIn_of_image (hS2 : ∀ s ∈ S, s * s = 1)
    (hST : S ≤ centralizer (T : Set G)) {L : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G))))
    (h : imageD S T ≤ centralizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T))) :
    ⁅L, solD S T⁆ ≤ (pPrimeCore 2 L).map L.subtype := by
  refine le_trans ?_ (inf_le_oddIn hLC)
  rw [commutator_le]
  intro l hl d hd
  refine mem_inf.mpr ⟨?_, commutator_le_of_le_normalizer (solD_le_normalizer hS2 hST hLC hL)
    (commutator_mem_commutator hl hd)⟩
  have hd' : (⟨d, (mem_inf.mp hd).2⟩ : ↥(centralizer (T : Set G))) ∈
      (solD S T).subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hd
  have hl' : (⟨l, hLC hl⟩ : ↥(centralizer (T : Set G))) ∈
      L.subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hl
  have hc := mem_centralizer_iff.mp (h (mem_map_of_mem _ hd')) _ (mem_map_of_mem _ hl')
  have h1 : solπ T ⁅(⟨l, hLC hl⟩ : ↥(centralizer (T : Set G))), ⟨d, (mem_inf.mp hd).2⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, hc]
    group
  exact ⟨_, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

omit [Finite G] in
theorem commutator_eq_self_of_image {L B : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G))))
    (hBN : B ≤ normalizer (L : Set G))
    (hne : ¬ (B.subgroupOf (centralizer (T : Set G))).map (solπ T) ≤ centralizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T))) :
    ⁅L, B⁆ = L := by
  obtain ⟨K, hK, hsn, hmap, hmin⟩ := hL
  have hBK : (B.subgroupOf (centralizer (T : Set G))).map (solπ T) ≤
      normalizer (K : Set (QC T)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← hmap]
    exact Subgroup.le_normalizer_map _ (mem_map_of_mem _
      (mem_normalizer_subgroupOf (hBN (mem_subgroupOf.mp hb))))
  have hne' : ⁅K, (B.subgroupOf (centralizer (T : Set G))).map (solπ T)⁆ ≠ ⊥ := by
    intro h
    apply hne
    rw [hmap, ← commutator_eq_bot_iff_le_centralizer, commutator_comm, h]
  have hKB := commutator_eq_of_ne_bot hK.1 hBK hne'
  have hNL : ⁅L, B⁆ ≤ L := commutator_le_of_le_normalizer hBN
  have hle1 : ⁅L.subgroupOf (centralizer (T : Set G)), B.subgroupOf (centralizer (T : Set G))⁆ ≤
      ⁅L, B⁆.subgroupOf (centralizer (T : Set G)) := by
    rw [commutator_le]
    intro l hl b hb
    exact mem_subgroupOf.mpr (commutator_mem_commutator (mem_subgroupOf.mp hl)
      (mem_subgroupOf.mp hb))
  have hle2 : ⁅L, B⁆.subgroupOf (centralizer (T : Set G)) ≤
      L.subgroupOf (centralizer (T : Set G)) :=
    fun x hx => mem_subgroupOf.mpr (hNL (mem_subgroupOf.mp hx))
  have himage : (⁅L, B⁆.subgroupOf (centralizer (T : Set G))).map (solπ T) = K := by
    refine le_antisymm (hmap ▸ map_mono hle2) ?_
    calc K = ⁅K, (B.subgroupOf (centralizer (T : Set G))).map (solπ T)⁆ := hKB.symm
      _ = ⁅L.subgroupOf (centralizer (T : Set G)),
          B.subgroupOf (centralizer (T : Set G))⁆.map (solπ T) := by
        rw [map_commutator, hmap]
      _ ≤ _ := map_mono hle1
  have hnorm : ((⁅L, B⁆.subgroupOf (centralizer (T : Set G))).subgroupOf
      (L.subgroupOf (centralizer (T : Set G)))).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hle2]
    intro c hc
    apply mem_normalizer_subgroupOf
    exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer (commutator_le_sup L B)).mp
      (commutator_normal_in_sup L B)) (mem_subgroupOf.mp hc)
  by_contra hne2
  refine hmin _ (lt_of_le_of_ne hle2 fun h => hne2 ?_) (IsSubnormal.step _ _ hle2 hsn hnorm)
    himage
  have := subgroupOf_inj.mp h
  rwa [inf_eq_left.mpr (hNL.trans hLC), inf_eq_left.mpr hLC] at this

theorem component_part (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G))
    {L : Subgroup G} (hLC : L ≤ centralizer (T : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer (T : Set G)))) :
    solD S T ≤ normalizer (L : Set G) ∧
      (¬ ⁅L, solD S T⁆ ≤ (pPrimeCore 2 L).map L.subtype →
        S ⊓ normalizer (L : Set G) ≠ ⊥ ∧ (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, solD S T⁆ = L ∧
          (pPrimeCore 2 L).map L.subtype ⊔ ⁅L, S ⊓ normalizer (L : Set G)⁆ = L) := by
  have hDN := solD_le_normalizer hS2 hST hLC hL
  refine ⟨hDN, fun hnot => ?_⟩
  have hK := isComponent_image hL
  have hne : ¬ imageD S T ≤ centralizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T)) :=
    fun h => hnot (commutator_le_oddIn_of_image hS2 hST hLC hL h)
  have hex : ∃ a ∈ imageS S T, a ∈ normalizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T)) ∧
      a ∉ centralizer
      (((L.subgroupOf (centralizer (T : Set G))).map (solπ T) : Subgroup (QC T)) : Set (QC T)) := by
    by_contra hcon
    push Not at hcon
    exact hne (le_centralizer_of_stabilizer_le hK odd_card_imageD
      (fun _ hy _ ha => imageD_commute hy ha) (normalizer_imageD hS2 hST)
      (imageD_le_normalizer hS2 hST hK) hcon)
  obtain ⟨_, ⟨s, hs, rfl⟩, haN, haC⟩ := hex
  have hsSN : (s : G) ∈ S ⊓ normalizer (L : Set G) :=
    mem_inf.mpr ⟨mem_subgroupOf.mp hs, mem_normalizer_of_image hLC hL haN⟩
  have hO : (pPrimeCore 2 L).map L.subtype ≤ L := map_subtype_le _
  refine ⟨fun hbot => haC ?_, ?_, ?_⟩
  · rw [hbot, mem_bot] at hsSN
    rw [show s = 1 from Subtype.ext hsSN, map_one]
    exact one_mem _
  · rw [commutator_eq_self_of_image hLC hL hDN hne, sup_eq_right.mpr hO]
  · have hs' : s ∈ (S ⊓ normalizer (L : Set G)).subgroupOf (centralizer (T : Set G)) :=
      mem_subgroupOf.mpr hsSN
    rw [commutator_eq_self_of_image hLC hL inf_le_right fun h => haC (h (mem_map_of_mem _ hs')),
      sup_eq_right.mpr hO]

theorem le_oddIn_of_forall (hS2 : ∀ s ∈ S, s * s = 1) (hST : S ≤ centralizer (T : Set G))
    (h : ∀ M : Subgroup G, M ≤ centralizer (T : Set G) →
      IsPComponent 2 (M.subgroupOf (centralizer (T : Set G))) →
        ⁅M, solD S T⁆ ≤ (pPrimeCore 2 M).map M.subtype) :
    solD S T ≤
      (pPrimeCore 2 ↥(centralizer (T : Set G))).map (centralizer (T : Set G)).subtype := by
  have hDC : solD S T ≤ centralizer (T : Set G) := inf_le_right
  have hodd : Odd (Nat.card ((solD S T).subgroupOf (centralizer (T : Set G)))) := by
    rw [← card_map_of_injective (centralizer (T : Set G)).subtype_injective,
      subgroupOf_map_subtype, inf_of_le_left hDC]
    exact odd_card_solD S T
  have hle := le_pPrimeCore_of_commutators hodd (fun y hy d hd => by
      have h1 := commutatorElement_mem_of_mem_pCore hS2 hST (y := y⁻¹) (d := d⁻¹)
        (by rw [map_inv]; exact inv_mem (mem_comap.mp hy)) (inv_mem hd)
      rwa [commutatorElement_def, inv_inv, inv_inv] at h1)
    (fun M' hM' y hy d hd => by
      have hMM : (M'.map (centralizer (T : Set G)).subtype).subgroupOf
          (centralizer (T : Set G)) = M' :=
        comap_map_eq_self_of_injective (centralizer (T : Set G)).subtype_injective M'
      rw [← hMM] at hM'
      have h1 : ((⁅y⁻¹, d⁻¹⁆ : ↥(centralizer (T : Set G))) : G) ∈
          ⁅M'.map (centralizer (T : Set G)).subtype, solD S T⁆ :=
        commutator_mem_commutator (mem_map_of_mem _ (inv_mem hy))
          (mem_subgroupOf.mp (inv_mem hd))
      have h2 := oddIn_le_of_isPComponent (map_subtype_le M') hM'
        (h _ (map_subtype_le M') hM' h1)
      have h3 : ⁅y⁻¹, d⁻¹⁆ ∈ pPrimeCore 2 ↥(centralizer (T : Set G)) :=
        (mem_map_iff_mem (centralizer (T : Set G)).subtype_injective).mp h2
      rwa [commutatorElement_def, inv_inv, inv_inv] at h3)
  intro d hd
  have hd' : (⟨d, hDC hd⟩ : ↥(centralizer (T : Set G))) ∈
      (solD S T).subgroupOf (centralizer (T : Set G)) := mem_subgroupOf.mpr hd
  exact ⟨_, hle hd', rfl⟩

end CFSG.ComponentClassification.GrSLit.Sol25

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup Sol25

theorem solomonCommutingCoreInput : SolomonCommutingCoreInput := by
  intro G _ _ S T _ _ _ hS2 _ _ hST
  have hST' : S ≤ centralizer (T : Set G) := fun s hs =>
    mem_centralizer_iff.mpr fun t ht => (hST s hs t ht).symm
  refine ⟨⟨commutator_O22_le hS2 hST', commutator_pCore_eq_bot hS2 hST'⟩,
    fun L hLC hL => component_part hS2 hST' hLC hL, fun hnot => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnot (le_oddIn_of_forall hS2 hST' hcon)

end CFSG.ComponentClassification.GrSLit
