module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4EndGCentral
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma39

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup

open CFSG.Open Subgroup
open Lemma39
open scoped Pointwise

theorem lemma_3_9_of_outer
    {G : Type} [Group G] [Finite G]
    (L : Subgroup G) [IsSimpleGroup L] (hLd : HasDihedralSylowTwo L) {a b : G}
    (haN : a ∈ normalizer (L : Set G)) (hbN : b ∈ normalizer (L : Set G))
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a)
    (hca : HasCyclicSylowTwo (L ⊓ centralizer ({a} : Set G) : Subgroup G))
    (hcb : HasCyclicSylowTwo (L ⊓ centralizer ({b} : Set G) : Subgroup G))
    (hgen : ¬ L ≤ (L ⊓ centralizer ({a} : Set G)) ⊔ (L ⊓ centralizer ({b} : Set G))) :
    a * b ∈ centralizer (L : Set G) := by
  obtain ⟨hout, hmax, hcenter, hcoset⟩ :=
    AschbacherKnownGroup.FactsL2.dihedral_outer_involution_holds G L a inferInstance hLd haN ha hca
  obtain ⟨houtb, hmaxb, -, -⟩ :=
    AschbacherKnownGroup.FactsL2.dihedral_outer_involution_holds G L b inferInstance hLd hbN hb hcb
  set Ca := L ⊓ centralizer ({a} : Set G) with hCa
  set Cb := L ⊓ centralizer ({b} : Set G) with hCb
  set M := zpowers a ⊔ Ca with hM
  have haL : a ∉ L := fun h => hout (mem_sup_left h)
  have hbL : b ∉ L := fun h => houtb (mem_sup_left h)
  have hasq : a * a = 1 := by rw [← pow_two]; exact ha
  have hba : Cb ≤ Ca := centralizer_le_of_maximal ha haN hab haL hmax hgen
  have hab' : Ca ≤ Cb := centralizer_le_of_maximal hb hbN hab.symm hbL hmaxb
    (by rwa [sup_comm])
  have hlc : a * b ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _
      (Subgroup.centralizer_le_normalizer (L : Set G))]
    exact hcoset b hbN hb hcb
  obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_mul.1 hlc
  set y := a * l with hy
  have hbyc : b = y * c := by
    calc b = a⁻¹ * (a * b) := by group
      _ = a * (l * c) := by rw [← hlc, inv_eq_of_mul_eq_one_left hasq]
      _ = y * c := by rw [hy, mul_assoc]
  have hcL : ∀ x ∈ L, c * x = x * c := fun x hx => ((mem_centralizer_iff.1 hc) x hx).symm
  have hyact : ∀ x ∈ L, y * x * y⁻¹ = b * x * b⁻¹ := by
    intro x hx
    rw [hbyc]
    calc y * x * y⁻¹ = y * (x * c) * c⁻¹ * y⁻¹ := by group
      _ = y * (c * x) * c⁻¹ * y⁻¹ := by rw [hcL x hx]
      _ = y * c * x * (y * c)⁻¹ := by group
  have hALN : zpowers a ⊔ L ≤ normalizer (L : Set G) :=
    sup_le (zpowers_le.2 haN) le_normalizer
  have hyAL : y ∈ zpowers a ⊔ L := mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right hl)
  have hcentral : ∀ w ∈ zpowers a ⊔ L, w ∈ centralizer (L : Set G) → w = 1 := by
    intro w hw hwC
    rcases mem_zpowers_sup ha haN hw with hwL | ⟨l', hl', rfl⟩
    · exact eq_one_of_mem_of_mem_centralizer hLd hwL hwC
    · exfalso
      apply hout
      have : a = (a * l') * l'⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_right hwC) (mem_sup_left (L.inv_mem hl'))
  have hanC : ∀ z ∈ centralizer (L : Set G), a * z * a⁻¹ ∈ centralizer (L : Set G) := by
    intro z hz
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : a⁻¹ * x * a ∈ L := by
      have := (mem_normalizer_iff.1 (inv_mem haN) x).1 hx
      simpa using this
    have hzx := (mem_centralizer_iff.1 hz) (a⁻¹ * x * a) hx'
    calc x * (a * z * a⁻¹) = a * ((a⁻¹ * x * a) * z) * a⁻¹ := by group
      _ = a * (z * (a⁻¹ * x * a)) * a⁻¹ := by rw [hzx]
      _ = a * z * a⁻¹ * x := by group
  have hya : y * a = a * y := by
    have hrel : y⁻¹ * a * y = c * a * c⁻¹ := by
      calc y⁻¹ * a * y = y⁻¹ * (a * (y * c)) * c⁻¹ := by group
        _ = y⁻¹ * ((y * c) * a) * c⁻¹ := by rw [← hbyc, hab, hbyc]
        _ = c * a * c⁻¹ := by group
    have hwC : c * a * c⁻¹ * a⁻¹ ∈ centralizer (L : Set G) := by
      have : c * a * c⁻¹ * a⁻¹ = c * (a * c⁻¹ * a⁻¹) := by group
      rw [this]
      exact mul_mem hc (hanC _ (inv_mem hc))
    have hwAL : c * a * c⁻¹ * a⁻¹ ∈ zpowers a ⊔ L := by
      rw [← hrel]
      exact mul_mem (mul_mem (mul_mem (inv_mem hyAL) (mem_sup_left (mem_zpowers a))) hyAL)
        (inv_mem (mem_sup_left (mem_zpowers a)))
    have h1 := hcentral _ hwAL hwC
    rw [← hrel] at h1
    calc y * a = y * (y⁻¹ * a * y * a⁻¹) * a := by rw [h1]; group
      _ = a * y := by group
  have hyN : y ∈ normalizer (M : Set G) := by
    refine mem_normalizer_sup ?_ (mem_normalizer_inf_centralizer (hALN hyAL) hya)
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (y * a * y⁻¹) = zpowers a
    rw [hya, mul_inv_cancel_right]
  have haCa : a ∈ normalizer (Ca : Set G) := mem_normalizer_inf_centralizer haN rfl
  have hyM : y ∈ M := by
    have hMAL : M ≤ zpowers a ⊔ L := sup_le le_sup_left (inf_le_left.trans le_sup_right)
    rcases hmax (M ⊔ zpowers y) le_sup_left (sup_le hMAL (zpowers_le.2 hyAL)) with h | h
    · exact h ▸ mem_sup_right (mem_zpowers y)
    · exfalso
      have hLN : L ≤ normalizer (M : Set G) := by
        calc L ≤ zpowers a ⊔ L := le_sup_right
          _ = M ⊔ zpowers y := h.symm
          _ ≤ normalizer (M : Set G) := sup_le le_normalizer (zpowers_le.2 hyN)
      have hconj : ∀ l' ∈ L, ∀ x ∈ Ca, l' * x * l'⁻¹ ∈ Ca := by
        intro l' hl' x hx
        have hxM : l' * x * l'⁻¹ ∈ M :=
          (mem_normalizer_iff.1 (hLN hl') x).1 (mem_sup_right hx)
        exact mem_of_mem_zpowers_sup_of_mem ha haCa inf_le_left haL hxM
          (L.mul_mem (L.mul_mem hl' (mem_inf.1 hx).1) (L.inv_mem hl'))
      have hnormal : (Ca.subgroupOf L).Normal := by
        refine ⟨fun x hx g => ?_⟩
        rw [mem_subgroupOf] at hx ⊢
        simpa using hconj g g.2 x hx
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Ca.subgroupOf L) with h0 | h0
      ·
        obtain ⟨l₀, hl₀⟩ := exists_ne (1 : L)
        apply hl₀
        have hla : (l₀ : G) * a * (l₀ : G)⁻¹ ∈ M :=
          (mem_normalizer_iff.1 (hLN l₀.2) a).1 (mem_sup_left (mem_zpowers a))
        rcases mem_zpowers_sup ha haCa hla with h1 | ⟨x, hx, h1⟩
        · exfalso
          apply haL
          have hx1 : (⟨_, (mem_inf.1 h1).1⟩ : L) ∈ Ca.subgroupOf L := h1
          rw [h0, mem_bot] at hx1
          have h2 : (l₀ : G) * a * (l₀ : G)⁻¹ = 1 := congrArg Subtype.val hx1
          have : a = 1 := by
            calc a = (l₀ : G)⁻¹ * ((l₀ : G) * a * (l₀ : G)⁻¹) * l₀ := by group
              _ = 1 := by rw [h2]; group
          rw [this]
          exact L.one_mem
        · have hx1 : (⟨x, (mem_inf.1 hx).1⟩ : L) ∈ Ca.subgroupOf L := hx
          rw [h0, mem_bot] at hx1
          have hx0 : x = 1 := congrArg Subtype.val hx1
          rw [hx0, mul_one] at h1
          have hl₀C : l₀ ∈ Ca.subgroupOf L := by
            rw [mem_subgroupOf]
            refine mem_inf.2 ⟨l₀.2, mem_centralizer_singleton_iff.2 ?_⟩
            calc (l₀ : G) * a = (l₀ : G) * a * (l₀ : G)⁻¹ * l₀ := by group
              _ = a * l₀ := by rw [h1]
          rw [h0, mem_bot] at hl₀C
          exact hl₀C
      ·
        apply hout
        apply mem_sup_right
        rw [mem_centralizer_iff]
        intro x hx
        have hx1 : (⟨x, hx⟩ : L) ∈ Ca.subgroupOf L := h0 ▸ mem_top _
        exact mem_centralizer_singleton_iff.1 (mem_inf.1 hx1).2
  have hyZ : y ∈ zpowers a := by
    refine hcenter y hyM (fun m hm => ?_)
    have hMC : M ≤ centralizer ({y} : Set G) := by
      refine sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hya.symm)) ?_
      intro x hx
      rw [mem_centralizer_singleton_iff]
      have hxb : x * b = b * x := mem_centralizer_singleton_iff.1 (mem_inf.1 (hab' hx)).2
      have := hyact x (mem_inf.1 hx).1
      symm
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = (b * x * b⁻¹) * y := by rw [this]
        _ = x * y := by rw [← hxb]; group
    exact (mem_centralizer_singleton_iff.1 (hMC hm)).symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hyZ
  rcases zpow_eq_one_or_self ha k with h1 | h1
  ·
    exfalso
    apply houtb
    rw [hbyc, ← hk, h1, one_mul]
    exact mem_sup_right hc
  · rw [hbyc, ← hk, h1, ← mul_assoc, hasq, one_mul]
    exact hc



end CFSG.ComponentClassification.AschbacherKnownGroup

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup)
open CFSG.ComponentClassification.AschbacherKnownGroup (HasDihedralSylowTwo HasCyclicSylowTwo)

variable {G : Type} [Group G] [Finite G]

theorem MainSetting.conj {Q : Subgroup G} (hS : MainSetting Q) (g : G) :
    MainSetting (rightConjugate Q g) where
  tight := rightConjugate_tightlyEmbedded Q hS.tight g
  proper := by
    intro h
    apply hS.proper
    rw [← AschbacherTheorem3.rightConjugate_normalizer, rightConjugate_eq_top_iff] at h
    exact h
  four := hS.four_rightConjugate g
  caseI a b := by
    have h := hS.caseI (g * a) (g * b)
    rwa [← rightConjugate_mul, ← rightConjugate_mul] at h
  star a b X hX hXc hXa hXb := by
    simp only [rightConjugate_mul] at hXa hXb ⊢
    exact hS.star (g * a) (g * b) X hX hXc hXa hXb

theorem linkedClass_rightConjugate {Q : Subgroup G} (hC : linkedClass Q = {Q}) (g : G) :
    linkedClass (rightConjugate Q g) = {rightConjugate Q g} := by
  ext A
  constructor
  · rintro ⟨⟨c, rfl⟩, hL⟩
    have h1 : Linked (rightConjugate (rightConjugate Q g) g⁻¹)
        (rightConjugate (rightConjugate (rightConjugate Q g) c) g⁻¹) :=
      linked_rightConjugate_iff.mpr hL
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    have h2 : rightConjugate Q (g * c * g⁻¹) ∈ linkedClass Q := ⟨⟨_, rfl⟩, h1⟩
    rw [hC, Set.mem_singleton_iff] at h2
    rw [Set.mem_singleton_iff, rightConjugate_mul]
    calc rightConjugate Q (g * c) = rightConjugate (rightConjugate Q (g * c * g⁻¹)) g := by
          rw [rightConjugate_mul, show g * c * g⁻¹ * g = g * c by group]
      _ = rightConjugate Q g := by rw [h2]
  · rintro rfl
    exact self_mem_linkedClass _

omit [Finite G] in
theorem not_oddNormalizerOverlaps_rightConjugate {Q : Subgroup G}
    (h : ¬ OddNormalizerOverlaps Q) (g : G) : ¬ OddNormalizerOverlaps (rightConjugate Q g) := by
  intro h'
  apply h
  intro x hx
  have hx' : g⁻¹ * x * g ∉ normalizer (rightConjugate Q g : Set G) := by
    rw [← AschbacherTheorem3.rightConjugate_normalizer, mem_rightConjugate_iff]
    simpa [mul_assoc] using hx
  have h1 := h' _ hx'
  rwa [rightConjugate_mul, show g * (g⁻¹ * x * g) = x * g by group, ← rightConjugate_mul,
    ← AschbacherTheorem3.rightConjugate_normalizer, ← AschbacherTheorem3.rightConjugate_inf,
    rightConjugate_card] at h1

theorem EndSetting.conj {Q : Subgroup G} (hE : EndSetting Q) (g : G) :
    EndSetting (rightConjugate Q g) :=
  ⟨hE.main.conj g, linkedClass_rightConjugate hE.linked g,
    not_oddNormalizerOverlaps_rightConjugate hE.even g⟩

omit [Finite G] in
theorem toBar_sq_eq_one {Q : Subgroup G} {x : G} (hxN : x ∈ normalizer (Q : Set G))
    (hx : x ^ 2 = 1) : toBar Q ⟨x, hxN⟩ ^ 2 = 1 := by
  rw [← map_pow]
  have : (⟨x, hxN⟩ : normalizer (Q : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using hx)
  rw [this, map_one]

namespace EndSetting

variable {Q : Subgroup G} (hE : EndSetting Q)
include hE

theorem normalizer_le_of_coversLayer {X : Subgroup G} (hX : IsPGroup 2 X)
    (hXc : centralizer (X : Set G) ≠ ⊤) {b : G} (hXb : CoversLayer X (rightConjugate Q b)) :
    normalizer (X : Set G) ≤ normalizer (rightConjugate Q b : Set G) := by
  intro n hn
  have hXn : rightConjugate X n = X := (rightConjugate_eq_self_iff X n).mpr hn
  have hXbn : CoversLayer X (rightConjugate Q (b * n)) := by
    have h := (coversLayer_rightConjugate_iff (g := n)).mpr hXb
    rwa [hXn, rightConjugate_mul] at h
  rcases hE.main.star b (b * n) X hX hXc hXb hXbn with h | h
  · rw [← rightConjugate_eq_self_iff, rightConjugate_mul, ← h]
  · have h1 : Linked (rightConjugate (rightConjugate Q b) b⁻¹)
        (rightConjugate (rightConjugate Q (b * n)) b⁻¹) := linked_rightConjugate_iff.mpr h
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    have h2 : rightConjugate Q (b * n * b⁻¹) ∈ linkedClass Q := ⟨⟨_, rfl⟩, h1⟩
    rw [hE.linked, Set.mem_singleton_iff] at h2
    rw [← rightConjugate_eq_self_iff, rightConjugate_mul,
      show b * n = b * n * b⁻¹ * b by group, ← rightConjugate_mul, h2]

omit hE in
theorem coversLayer_zpowers {a : G} (haN : a ∈ normalizer (Q : Set G)) {k : ℕ}
    (ha : a ^ 2 ^ k = 1)
    (haC : toBar Q ⟨a, haN⟩ ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q))) :
    CoversLayer (zpowers a) Q := by
  refine coversLayer_of_commutator (isPGroup_zpowers_of_pow_eq_one ha) ((zpowers_le).mpr haN)
    fun x hx y hy => ?_
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
  have hyN : y ∈ normalizer (Q : Set G) := (twoPrimeLayerIn_le Q).trans le_normalizer hy
  have hcomm : toBar Q ⟨y, hyN⟩ * toBar Q ⟨a, haN⟩ = toBar Q ⟨a, haN⟩ * toBar Q ⟨y, hyN⟩ :=
    mem_centralizer_iff.mp haC _ (toBar_mem_bar Q hy)
  have h1 : toBar Q (⟨a, haN⟩ ^ i * ⟨y, hyN⟩ * (⟨a, haN⟩ ^ i)⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_zpow,
      ((show Commute (toBar Q ⟨y, hyN⟩) (toBar Q ⟨a, haN⟩) from hcomm).symm.zpow_left i).eq]
    group
  rw [toBar_eq_one_iff] at h1
  simp only [coe_mul, coe_inv, SubgroupClass.coe_zpow] at h1
  exact h1

theorem centralizer_le_of_bar_mem_centralizer {a : G} (haN : a ∈ normalizer (Q : Set G))
    {k : ℕ} (ha : a ^ 2 ^ k = 1)
    (haC : toBar Q ⟨a, haN⟩ ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))
    (hacen : a ∉ center G) : centralizer ({a} : Set G) ≤ normalizer (Q : Set G) := by
  have h := hE.normalizer_le_of_coversLayer (isPGroup_zpowers_of_pow_eq_one ha)
    (MainSetting.centralizer_zpowers_ne_top_of_not_mem_center hacen) (b := 1)
    (by rw [rightConjugate_one]; exact coversLayer_zpowers haN ha haC)
  rw [rightConjugate_one] at h
  exact (centralizer_le_normalizer_zpowers a).trans h

theorem hasCyclicSylowTwo_of_not_hasFourGroup {y : G} (hyN : y ∈ normalizer (Q : Set G))
    {k : ℕ} (hy : y ^ 2 ^ k = 1)
    (h4 : ¬ HasFourGroup (twoPrimeLayerIn Q ⊓ centralizer ({y} : Set G))) :
    HasCyclicSylowTwo (bar Q (twoPrimeLayerIn Q) ⊓
      centralizer ({toBar Q ⟨y, hyN⟩} : Set (Bar Q)) : Subgroup (Bar Q)) := by
  by_contra hnc
  obtain ⟨R, hR, hRd⟩ := hE.main.exists_isDihedral_sylow hE.linked hE.even
  have hV := hasFourGroup_of_not_hasCyclicSylowTwo hR hRd
    (inf_le_left.trans (bar_mono Q (twoPrimeLayerIn_le Q))) hnc
  have hlift := bar_inf_centralizer_singleton_le (Y := twoPrimeLayerIn Q)
    (oddCoreIn_le_twoPrimeLayerIn Q)
    ((twoPrimeLayerIn_le Q).trans (normalIn_le_normalizer (oddCoreIn_normalIn Q))) hyN hy
  exact h4 (HasFourGroup.of_bar_of_le (inf_le_left.trans ((twoPrimeLayerIn_le Q).trans
    le_normalizer)) (hV.mono hlift))

theorem mem_center_of_commute
    {a t z : G} (haN : a ∈ normalizer (Q : Set G)) (ha2 : a ^ 2 = 1)
    (haC : toBar Q ⟨a, haN⟩ ∈ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)))
    (ht : IsOverlapInv Q t) (hzQ : z ∈ Q) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (hat : a * t = t * a) (hzt : z * t = t * z) (haz : a * z = z * a) : a ∈ center G := by
  by_contra hacen
  obtain ⟨g, hg, htQg⟩ := ht.2.2.2
  have hE' := hE.conj g
  have ha21 : a ^ 2 ^ 1 = 1 := by simpa using ha2
  have hz21 : z ^ 2 ^ 1 = 1 := by simpa using hz2
  have hCa := hE.centralizer_le_of_bar_mem_centralizer haN ha21 haC hacen
  have hCz := centralizer_le_of_involution hE.main.tight hzQ (orderOf_eq_prime hz2 hz1)
  have hCt := centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q hE.main.tight g)
    htQg ht.orderOf_eq
  have haN' : a ∈ normalizer (rightConjugate Q g : Set G) :=
    hCt (mem_centralizer_singleton_iff.mpr hat)
  have hzN' : z ∈ normalizer (rightConjugate Q g : Set G) :=
    hCt (mem_centralizer_singleton_iff.mpr hzt)
  have hno : ¬ HasFourGroup (rightConjugate Q g ⊓ normalizer (Q : Set G)) :=
    hE.main.not_hasFourGroup_of_linkedClass_eq hE.linked hg
  set Q' := rightConjugate Q g with hQ'
  set K' := twoPrimeLayerIn Q' with hK'
  set L' := bar Q' K' with hL'
  have hK'Q' : K' ≤ Q' := twoPrimeLayerIn_le Q'
  have hca : HasCyclicSylowTwo (L' ⊓ centralizer ({toBar Q' ⟨a, haN'⟩} : Set (Bar Q')) :
      Subgroup (Bar Q')) :=
    hE'.hasCyclicSylowTwo_of_not_hasFourGroup haN' ha21 fun h =>
      hno (h.mono (inf_le_inf hK'Q' hCa))
  have hcz : HasCyclicSylowTwo (L' ⊓ centralizer ({toBar Q' ⟨z, hzN'⟩} : Set (Bar Q')) :
      Subgroup (Bar Q')) :=
    hE'.hasCyclicSylowTwo_of_not_hasFourGroup hzN' hz21 fun h =>
      hno (h.mono (inf_le_inf hK'Q' hCz))
  have hOK : oddCoreIn Q' ≤ K' := oddCoreIn_le_twoPrimeLayerIn Q'
  have hKO : K' ≤ normalizer (oddCoreIn Q' : Set G) :=
    hK'Q'.trans (normalIn_le_normalizer (oddCoreIn_normalIn Q'))
  have hgen : ¬ L' ≤ (L' ⊓ centralizer ({toBar Q' ⟨a, haN'⟩} : Set (Bar Q'))) ⊔
      (L' ⊓ centralizer ({toBar Q' ⟨z, hzN'⟩} : Set (Bar Q'))) := by
    intro hle
    have h1 : (L' ⊓ centralizer ({toBar Q' ⟨a, haN'⟩} : Set (Bar Q'))) ⊔
        (L' ⊓ centralizer ({toBar Q' ⟨z, hzN'⟩} : Set (Bar Q'))) ≤
          bar Q' (K' ⊓ normalizer (Q : Set G)) :=
      sup_le ((bar_inf_centralizer_singleton_le hOK hKO haN' ha21).trans
          (bar_mono Q' (inf_le_inf_left K' hCa)))
        ((bar_inf_centralizer_singleton_le hOK hKO hzN' hz21).trans
          (bar_mono Q' (inf_le_inf_left K' hCz)))
    have h4 := (hE'.main.hasFourGroup_bar).mono (hle.trans h1)
    exact hno ((HasFourGroup.of_bar_of_le (inf_le_left.trans (hK'Q'.trans le_normalizer))
      h4).mono (inf_le_inf_right _ hK'Q'))
  have := hE'.isSimpleGroup_bar
  have h39 := AschbacherKnownGroup.lemma_3_9_of_outer L' hE'.hasDihedralSylowTwo_bar
    (mem_normalizer_bar_twoPrimeLayerIn Q' _) (mem_normalizer_bar_twoPrimeLayerIn Q' _)
    (toBar_sq_eq_one haN' ha2) (toBar_sq_eq_one hzN' hz2)
    (by rw [← map_mul, ← map_mul]; exact congrArg (toBar Q') (Subtype.ext haz)) hca hcz hgen
  have hazN' : a * z ∈ normalizer (Q' : Set G) := mul_mem haN' hzN'
  have haz2 : (a * z) ^ 2 ^ 1 = 1 := by
    rw [pow_one, (show Commute a z from haz).mul_pow, ha2, hz2, one_mul]
  have hazC : toBar Q' ⟨a * z, hazN'⟩ ∈ centralizer (L' : Set (Bar Q')) := by
    have : toBar Q' ⟨a * z, hazN'⟩ = toBar Q' ⟨a, haN'⟩ * toBar Q' ⟨z, hzN'⟩ := by
      rw [← map_mul]
      rfl
    rw [this]
    exact h39
  have hazcen : a * z ∉ center G := by
    intro h
    have haN0 : a * z ∈ normalizer (Q : Set G) := mul_mem haN (le_normalizer hzQ)
    have h1 := toBar_mem_centralizer_of_mem_center (Q := Q) h haN0
    have h2 : toBar Q ⟨z, le_normalizer hzQ⟩ ∈
        bar Q Q ⊓ centralizer (bar Q (twoPrimeLayerIn Q) : Set (Bar Q)) := by
      refine mem_inf.mpr ⟨toBar_mem_bar Q hzQ, ?_⟩
      have : toBar Q ⟨z, le_normalizer hzQ⟩ = (toBar Q ⟨a, haN⟩)⁻¹ * toBar Q ⟨a * z, haN0⟩ := by
        rw [← map_inv, ← map_mul]
        congr 1
        exact Subtype.ext (by simp)
      rw [this]
      exact mul_mem (inv_mem haC) h1
    rw [hE.inf_centralizer_bar_eq_bot, mem_bot, toBar_eq_one_iff] at h2
    have h3 : orderOf z ∣ Nat.card (oddCoreIn Q) := by
      have h2' : z ∈ oddCoreIn Q := h2
      have := orderOf_dvd_natCard (⟨z, h2'⟩ : oddCoreIn Q)
      rwa [Subgroup.orderOf_mk] at this
    rw [orderOf_eq_prime hz2 hz1] at h3
    exact Nat.not_even_iff_odd.mpr (odd_card_oddCoreIn Q) (even_iff_two_dvd.mpr h3)
  have hCaz : centralizer ({a * z} : Set G) ≤ normalizer (Q' : Set G) := by
    have h := hE'.normalizer_le_of_coversLayer (isPGroup_zpowers_of_pow_eq_one haz2)
      (MainSetting.centralizer_zpowers_ne_top_of_not_mem_center hazcen) (b := 1)
      (by rw [rightConjugate_one]; exact coversLayer_zpowers hazN' haz2 hazC)
    rw [rightConjugate_one] at h
    exact (centralizer_le_normalizer_zpowers (a * z)).trans h
  apply hE.main.not_hasFourGroup_inf_normalizer hE.linked hg
  set V := zpowers a ⊔ zpowers z with hV
  have hVN : V ≤ normalizer (Q : Set G) := sup_le ((zpowers_le).mpr haN)
    ((zpowers_le).mpr (le_normalizer hzQ))
  have hV2 : IsPGroup 2 V := by
    have hcomm : zpowers a ≤ centralizer (zpowers z : Set G) := (zpowers_le).mpr
      (mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
        exact ((show Commute z a from haz.symm).zpow_left j).eq)
    have hsq : ∀ v ∈ V, v ^ 2 = 1 := by
      intro v hv
      rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _
        (hcomm.trans (centralizer_le_normalizer _))] at hv
      obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hv
      rw [(show Commute x y from mem_centralizer_iff.mp (hcomm hx) y hy |>.symm).mul_pow,
        sq_eq_one_of_mem_zpowers ha2 hx, sq_eq_one_of_mem_zpowers hz2 hy, one_mul]
    exact isPGroup_of_sq_eq_one hsq
  have hlift := bar_inf_centralizer_le (Y := Q) (oddCoreIn_le Q)
    (normalIn_le_normalizer (oddCoreIn_normalIn Q)) hV2 hVN
  have hzbar : toBar Q ⟨z, le_normalizer hzQ⟩ ∈ bar Q Q := toBar_mem_bar Q hzQ
  have h4 := hE.hasFourGroup_bar_inf_centralizer_of_sq hzbar (toBar_sq_eq_one _ hz2)
  have hCC := hE.centralizer_le_centralizer_bar
  have hle : bar Q Q ⊓ centralizer ({toBar Q ⟨z, le_normalizer hzQ⟩} : Set (Bar Q)) ≤
      bar Q Q ⊓ centralizer (bar Q V : Set (Bar Q)) := by
    intro x hx
    obtain ⟨hxQ, hxz⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨hxQ, ?_⟩
    have hxa : x ∈ centralizer (bar Q (zpowers a) : Set (Bar Q)) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨h, hh, rfl⟩ := (mem_bar_iff Q _ y).mp hy
      obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hh
      have hhi : h = (⟨a, haN⟩ : normalizer (Q : Set G)) ^ i := Subtype.ext (by simp [hi])
      rw [hhi, map_zpow]
      exact (((show Commute (toBar Q ⟨a, haN⟩) x from
        (mem_centralizer_iff.mp (hCC haC) x hxQ).symm)).zpow_left i).eq
    have hxz' : x ∈ centralizer (bar Q (zpowers z) : Set (Bar Q)) :=
      centralizer_singleton_le_centralizer_bar_zpowers Q (le_normalizer hzQ) hxz
    rw [hV, bar_sup ((zpowers_le).mpr haN) ((zpowers_le).mpr (le_normalizer hzQ))]
    rw [← zpowers_le, le_centralizer_iff] at hxa hxz' ⊢
    exact sup_le hxa hxz'
  have h4' := HasFourGroup.of_bar_of_le (inf_le_left.trans le_normalizer)
    ((h4.mono hle).mono hlift)
  refine h4'.mono (inf_le_inf_left Q ?_)
  refine (Subgroup.centralizer_le ?_).trans hCaz
  rw [Set.singleton_subset_iff]
  exact mul_mem (mem_sup_left (mem_zpowers a)) (mem_sup_right (mem_zpowers z))

end EndSetting

end CFSG.ComponentClassification.Asc75T4
