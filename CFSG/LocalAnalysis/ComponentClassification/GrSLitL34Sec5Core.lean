module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Setup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Balance
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Four

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_commute {x : G} {H : Subgroup G} (h : ∀ y ∈ H, x * y = y * x) :
    x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [h1, mul_assoc, ← h _ hy, inv_mul_cancel_left]
    exact hy

theorem elemTwo_zpowers_sup {x : G} {H : Subgroup G} (hx : x * x = 1) (hH : IsElemTwo H)
    (hxH : ∀ y ∈ H, x * y = y * x) (hxn : x ∉ H) :
    IsElemTwo (zpowers x ⊔ H) ∧ Nat.card ↥(zpowers x ⊔ H) = 2 * Nat.card H := by
  refine ⟨IsElemTwo.sup (isElemTwo_zpowers hx) hH ?_, card_zpowers_sup_eq hx
    (mem_normalizer_of_commute hxH) hxn⟩
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  exact (Commute.zpow_left (hxH b hb) i).eq

omit [Finite G] in
theorem mem_zpowers_sup {z : G} {H : Subgroup G} (hzH : ∀ y ∈ H, z * y = y * z) {x : G}
    (hx : x ∈ zpowers z ⊔ H) : ∃ i : ℤ, ∃ h ∈ H, x = z ^ i * h := by
  have hle : zpowers z ≤ normalizer (H : Set G) := zpowers_le.mpr (mem_normalizer_of_commute hzH)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers z) H hle
  have hx' : x ∈ ((zpowers z : Set G) * (H : Set G)) := by
    rw [← hset]
    exact hx
  obtain ⟨a, ha, h, hh, rfl⟩ := hx'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  exact ⟨i, h, hh, rfl⟩

theorem rank3 {F : Subgroup G} (hF : IsElemTwo F) (h8 : 8 ≤ Nat.card F) :
    IsAbelianTwoOfRank 3 F :=
  hF.isAbelianTwoOfRank h8

theorem wGroup_four_eq_bot (hGWb : GWTwoBalanced G) (hGW : GorensteinWalterConnectedInput)
    {L W : Subgroup G} {t y z : G}
    (hW8 : ∀ A : Subgroup G, IsEightGroup A → A ≤ L ⊔ zpowers t → wGroup A = ⊥)
    (hWL : W ≤ L) (hW : IsElemTwo W) (hW4 : Nat.card W = 4)
    (hWC : W ⊓ centralizer (L : Set G) = ⊥) (ht : t ∈ centralizer (L : Set G)) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) (hy : y ∈ centralizer (L : Set G)) (hz : z ∈ centralizer (L : Set G))
    (hy2 : y * y = 1) (hz2 : z * z = 1) (hyz : y * z = z * y) (htz : t * z = z * t)
    (hz1 : z ≠ 1) (hyn : y ∉ zpowers z) :
    wGroup (zpowers y ⊔ zpowers z) = ⊥ := by
  have hcomL : ∀ c ∈ centralizer (L : Set G), ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
    ((mem_centralizer_iff.mp hc) w (hWL hw)).symm
  have hnotW : ∀ c ∈ centralizer (L : Set G), c ≠ 1 → c ∉ W := by
    intro c hc hc1 hcW
    have : c ∈ W ⊓ centralizer (L : Set G) := mem_inf.mpr ⟨hcW, hc⟩
    rw [hWC] at this
    exact hc1 (mem_bot.mp this)
  obtain ⟨hE₁, hE₁c⟩ := elemTwo_zpowers_sup ht2 hW (hcomL t ht) (hnotW t ht ht1)
  have hE₁8 : 8 ≤ Nat.card ↥(zpowers t ⊔ W) := by rw [hE₁c, hW4]
  have hE₁L : zpowers t ⊔ W ≤ L ⊔ zpowers t := sup_le le_sup_right (hWL.trans le_sup_left)
  have hWE₁ : wGroup (zpowers t ⊔ W) = ⊥ :=
    hW8 _ ⟨hE₁, by rw [hE₁c, hW4]⟩ hE₁L
  have hzE₁ : ∀ g ∈ zpowers t ⊔ W, z * g = g * z := by
    intro g hg
    have hle : zpowers t ⊔ W ≤ centralizer ({z} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htz))
      fun w hw => mem_centralizer_singleton_iff.mpr (hcomL z hz w hw).symm
    exact (mem_centralizer_singleton_iff.mp (hle hg)).symm
  have hB : IsElemTwo (zpowers z ⊔ (zpowers t ⊔ W)) := IsElemTwo.sup (isElemTwo_zpowers hz2) hE₁
    (by
      intro a ha b hb
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (hzE₁ b hb) i).eq)
  have hB8 : 8 ≤ Nat.card ↥(zpowers z ⊔ (zpowers t ⊔ W)) :=
    hE₁8.trans (card_le_of_le le_sup_right)
  obtain ⟨hC, hCc⟩ := elemTwo_zpowers_sup hz2 hW (hcomL z hz) (hnotW z hz hz1)
  have hC8 : 8 ≤ Nat.card ↥(zpowers z ⊔ W) := by rw [hCc, hW4]
  have hyC : ∀ g ∈ zpowers z ⊔ W, y * g = g * y := by
    intro g hg
    have hle : zpowers z ⊔ W ≤ centralizer ({y} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyz.symm))
      fun w hw => mem_centralizer_singleton_iff.mpr (hcomL y hy w hw).symm
    exact (mem_centralizer_singleton_iff.mp (hle hg)).symm
  have hynC : y ∉ zpowers z ⊔ W := by
    intro hyC'
    obtain ⟨i, w, hw, hyw⟩ := mem_zpowers_sup (hcomL z hz) hyC'
    have hwC : w ∈ centralizer (L : Set G) := by
      have : w = (z ^ i)⁻¹ * y := by rw [hyw]; group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem hz i)) hy
    by_cases hw1 : w = 1
    · exact hyn (by rw [hyw, hw1, mul_one]; exact zpow_mem (mem_zpowers z) i)
    · exact hnotW w hwC hw1 hw
  obtain ⟨hA, hAc⟩ := elemTwo_zpowers_sup hy2 hC hyC hynC
  have hA16 : 16 ≤ Nat.card ↥(zpowers y ⊔ (zpowers z ⊔ W)) := by rw [hAc, hCc, hW4]
  have hconn : AbelianConnected 3 (zpowers t ⊔ W) (zpowers y ⊔ (zpowers z ⊔ W)) := by
    refine ⟨rank3 hE₁ hE₁8, ?_⟩
    have s1 : Relation.ReflTransGen (fun A' B' : Subgroup G => IsAbelianTwoOfRank 3 B' ∧
        ∀ x ∈ A', ∀ y ∈ B', x * y = y * x) (zpowers t ⊔ W) (zpowers z ⊔ (zpowers t ⊔ W)) :=
      Relation.ReflTransGen.single ⟨rank3 hB hB8, fun a ha b hb => hB.1 a (mem_sup_right ha) b hb⟩
    have hCB : zpowers z ⊔ W ≤ zpowers z ⊔ (zpowers t ⊔ W) :=
      sup_le le_sup_left (le_sup_right.trans le_sup_right)
    refine Relation.ReflTransGen.tail (b := zpowers z ⊔ W)
      (Relation.ReflTransGen.tail (b := zpowers z ⊔ (zpowers t ⊔ W)) s1 ?_) ?_
    · exact ⟨rank3 hC hC8, fun a ha b hb => hB.1 a ha b (hCB hb)⟩
    · exact ⟨rank3 hA (by omega), fun a ha b hb => hA.1 a (mem_sup_right ha) b hb⟩
  have hself : AbelianConnected 3 (zpowers y ⊔ (zpowers z ⊔ W)) (zpowers y ⊔ (zpowers z ⊔ W)) :=
    ⟨rank3 hA (by omega), Relation.ReflTransGen.refl⟩
  obtain ⟨hGW1, -⟩ := hGW G hGWb _ hA.1 hA.2 hA16
  obtain ⟨-, hWeq, -⟩ := hGW1 _ _ hself hconn
  rw [hWE₁] at hWeq
  apply le_bot_iff.mp
  rw [hWeq]
  exact wGroup_mono (sup_le le_sup_left (zpowers_le.mpr
    (mem_sup_right (mem_sup_left (mem_zpowers z)))))

theorem oddIn_le_center_of_four (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hK : Assembly.KProper Blueprint.Catalog G) (hZ : ∀ g : G, g ≠ 1 → g ∉ center G)
    {L : Subgroup G} {b y : G} (hb : orderOf b = 2) (hLb : L ≤ centralizer ({b} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set G))))
    (hbL : b ∈ centralizer (L : Set G)) (hy : y ∈ centralizer (L : Set G)) (hy2 : y * y = 1)
    (hyb : y * b = b * y) (hyn : y ∉ zpowers b) (hW : wGroup (zpowers y ⊔ zpowers b) = ⊥) :
    oddIn L ≤ (center ↥L).map L.subtype := by
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hb1 : b ≠ 1 := by rintro rfl; simp at hb
  obtain ⟨hE, hEc⟩ := elemTwo_zpowers_sup hy2 (isElemTwo_zpowers hb2)
    (fun g hg => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
      exact (Commute.zpow_right hyb i).eq) hyn
  set E := zpowers y ⊔ zpowers b with hEdef
  have hEL : E ≤ centralizer (L : Set G) := sup_le (zpowers_le.mpr hy) (zpowers_le.mpr hbL)
  have hEb : E ≤ centralizer ({b} : Set G) := sup_le
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyb))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hE4 : 4 ≤ Nat.card E := by rw [hEc, Nat.card_zpowers, hb]
  have hEN : E ≤ normalizer (L : Set G) := fun c hc =>
    mem_normalizer_of_commute fun l hl => ((mem_centralizer_iff.mp (hEL hc)) l hl).symm
  have hEcen : ∀ e ∈ E, ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype := by
    intro e he l hl
    rw [show e * l = l * e from ((mem_centralizer_iff.mp (hEL he)) l hl).symm,
      mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hbal : ∀ e ∈ E, e ≠ 1 →
      ⁅(pPrimeCore 2 L).map L.subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
          (L ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype := by
    intro e he he1
    have htop : centralizer ({e} : Set G) ≠ ⊤ := by
      intro h
      apply hZ e he1
      rw [mem_center_iff]
      intro g
      exact mem_centralizer_singleton_iff.mp (h ▸ mem_top g)
    exact commutator_oddCore_pLayer_le hS hU hheld hK hb hLb hL
      (mem_centralizer_singleton_iff.mp (hEb he)).symm htop
  have hcom := oddCore_le_center_of_wGroup_eq_bot hLb hL hEb hE.1 hE.2 hE4 hEN hEcen hW hbal
    (Or.inl hEL)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x, mem_center_iff.mpr fun g => ?_, rfl⟩
  exact Subtype.ext (hcom _ ⟨x, hx, rfl⟩ g g.2).symm

omit [Finite G] in
theorem not_mem_center_of_ne_one [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) {g : G}
    (hg : g ≠ 1) : g ∉ center G := by
  intro hgc
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · rw [h, mem_bot] at hgc
    exact hg hgc
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ center G := h ▸ mem_top a
    exact hab ((mem_center_iff.mp ha b).symm)

omit [Finite G] in
theorem centralizer_ne_top_of_not_mem_center {g : G} (hg : g ∉ center G) :
    centralizer ({g} : Set G) ≠ ⊤ := by
  intro h
  apply hg
  rw [mem_center_iff]
  intro x
  exact mem_centralizer_singleton_iff.mp (h ▸ mem_top x)

omit [Finite G] in
theorem conj_mem_oddIn_of_mem_coreActionKernel {L : Subgroup G} {e : G}
    (he : e ∈ coreActionKernel L) :
    ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype := by
  intro l hl
  have h1 := (mem_coreActionKernel.mp (inv_mem he)).2 l hl
  rw [inv_inv] at h1
  have hlN : l ∈ normalizer (oddIn L : Set G) :=
    normalizer_le_normalizer_oddIn L (le_normalizer hl)
  have h2 := (mem_normalizer_iff.mp hlN _).mp h1
  have e1 : l * (l⁻¹ * e * l * e⁻¹) * l⁻¹ = e * l * e⁻¹ * l⁻¹ := by group
  rw [e1] at h2
  exact h2

omit [Finite G] in
theorem IsSylowTwoIn.isPGroup {S H : Subgroup G} (hS : IsSylowTwoIn S H) : IsPGroup 2 S := by
  obtain ⟨hSH, P, hP⟩ := hS
  have h := P.isPGroup'.map H.subtype
  rwa [hP, map_subgroupOf_eq_of_le hSH] at h

omit [Finite G] in
theorem conj_mem_centralizer {L : Subgroup G} {n c : G} (hn : n ∈ normalizer (L : Set G))
    (hc : c ∈ centralizer (L : Set G)) : n * c * n⁻¹ ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  have hl' : n⁻¹ * l * n⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hn) l).mp hl
  have h := (mem_centralizer_iff.mp hc) _ hl'
  rw [inv_inv] at h
  calc l * (n * c * n⁻¹) = n * ((n⁻¹ * l * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * l * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * l := by group

theorem eq_of_mem_inf_centralizer (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) :
    (∀ s ∈ S ⊓ centralizer (L : Set G), orderOf s = 2 → s = t) ∧
      L ≤ centralizer ({t} : Set G) ∧
      IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hfam, -, hSyl, htS, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, hloc, -, -⟩ := hbase
  obtain ⟨⟨a, x, J, -, -, hto, -, hLeq⟩, htype, ⟨⟨a', ha', hLa', hLpa'⟩, -⟩, hX, hW8'⟩ := hfam
  have : IsSimpleGroup G := hsimple
  have hZ : ∀ g : G, g ≠ 1 → g ∉ center G := fun g hg => not_mem_center_of_ne_one hnonab hg
  have hLt : L ≤ centralizer ({t} : Set G) := hLeq ▸ pumpUp_le_centralizer J t
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by rintro rfl; simp at hto
  have hW8 : ∀ A : Subgroup G, IsEightGroup A → A ≤ L ⊔ zpowers t → wGroup A = ⊥ :=
    fun A hA hAL => hW8' A hA (Or.inl hAL)
  have hGWb : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hloc
  obtain ⟨W, hWL, hWe, hW4, hWC⟩ := exists_four_inf_centralizer htype
  have ha'L : a' ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLa' hl)
  have ha'N : a' ∈ normalizer (L : Set G) :=
    mem_normalizer_of_commute fun l hl => ((mem_centralizer_iff.mp ha'L) l hl).symm
  have ha'2 : IsPGroup 2 (zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ha', pow_one]
  obtain ⟨n, hn, hbS⟩ := exists_conj_mem_of_isSylowTwoIn hSyl ha'N ha'2
  set b := n⁻¹ * a' * n with hbdef
  obtain ⟨hLb, hLpb⟩ := isPComponent_centralizer_conj hLa' hLpa' hn
  have hb : orderOf b = 2 := by rw [hbdef, GSLit.orderOf_conj_inv, ha']
  have hbL : b ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLb hl)
  have hb2 : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  set P := S ⊓ centralizer (L : Set G) with hPdef
  have hP2 : IsPGroup 2 P := (IsSylowTwoIn.isPGroup hSyl).to_le inf_le_left
  have htP : t ∈ P := mem_inf.mpr ⟨htS, htL⟩
  have hbP : b ∈ P := mem_inf.mpr ⟨hbS, hbL⟩
  have : Nontrivial P := ⟨⟨⟨t, htP⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
  have hcen : Nontrivial (center P) := hP2.center_nontrivial
  have h2dvd : 2 ∣ Nat.card (center P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(center P))).mp
      (hP2.to_subgroup (center P))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hcen).ne' hk
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  set z : G := ((z₀ : P) : G) with hzdef
  have hzP : z ∈ P := (z₀ : P).2
  have hzc : ∀ p ∈ P, p * z = z * p := fun p hp =>
    congrArg Subtype.val (mem_center_iff.mp z₀.2 ⟨p, hp⟩)
  have hz : orderOf z = 2 := by
    rw [hzdef, orderOf_coe, orderOf_coe]
    exact hz₀
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by rintro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hzL : z ∈ centralizer (L : Set G) := (mem_inf.mp hzP).2
  have hkey : ∀ c ∈ P, orderOf c = 2 → (∀ p ∈ P, p * c = c * p) → ∀ y ∈ P, y * y = 1 →
      y ∉ zpowers c → wGroup (zpowers y ⊔ zpowers c) = ⊥ := by
    intro c hcP hc hcc y hyP hy2 hyn
    have hc2 : c * c = 1 := by rw [← pow_two, ← hc, pow_orderOf_eq_one]
    have hc1 : c ≠ 1 := by rintro h; rw [h, orderOf_one] at hc; exact absurd hc (by norm_num)
    exact wGroup_four_eq_bot hGWb hGW hW8 hWL hWe hW4 hWC htL ht2 ht1 (mem_inf.mp hyP).2
      (mem_inf.mp hcP).2 hy2 hc2 (hcc y hyP) (hcc t htP) hc1 hyn
  have hcontra : ∀ y ∈ P, orderOf y = 2 → y * b = b * y → y ∉ zpowers b →
      wGroup (zpowers y ⊔ zpowers b) = ⊥ → False := by
    intro y hyP hy hyb hyn hWy
    have hy2 : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
    exact hX (oddIn_le_center_of_four hS hU hheld hK hZ hb hLb hLpb hbL (mem_inf.mp hyP).2 hy2
      hyb hyn hWy)
  have hmem2 : ∀ c y : G, orderOf c = 2 → y ≠ 1 → y ≠ c → y ∉ zpowers c := by
    intro c y hc hy1 hyc hy
    rcases (LocalB.mem_zpowers_iff_of_involution c y hc).mp hy with h | h
    · exact hy1 h
    · exact hyc h
  have hbz : b = z := by
    by_contra hne
    have hb1 : b ≠ 1 := by rintro h; rw [h, orderOf_one] at hb; exact absurd hb (by norm_num)
    have h1 := hkey z hzP hz hzc b hbP hb2 (hmem2 z b hz hb1 hne)
    exact hcontra z hzP hz (hzc b hbP).symm (hmem2 b z hb hz1 (Ne.symm hne))
      (by rw [sup_comm]; exact h1)
  have hbc : ∀ p ∈ P, p * b = b * p := by rw [hbz]; exact hzc
  have hall : ∀ s ∈ P, orderOf s = 2 → s = b := by
    intro s hsP hs
    by_contra hne
    have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
    have hs1 : s ≠ 1 := by rintro h; rw [h, orderOf_one] at hs; exact absurd hs (by norm_num)
    have hsn := hmem2 b s hb hs1 hne
    exact hcontra s hsP hs (hbc s hsP) hsn (hkey b hbP hb hbc s hsP hs2 hsn)
  have htb : t = b := hall t htP hto
  refine ⟨fun s hs hs2 => (hall s hs hs2).trans htb.symm, htb ▸ hLb, htb ▸ hLpb⟩

theorem mem_center_of_setting (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) :
    ∀ s ∈ S, s * t = t * s := by
  obtain ⟨huniq, hLt, -⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, ⟨hSN, -⟩, htS, -, -⟩ := hset
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  intro s hs
  have h1 : s * t * s⁻¹ ∈ S ⊓ centralizer (L : Set G) :=
    mem_inf.mpr ⟨mul_mem (mul_mem hs htS) (inv_mem hs), conj_mem_centralizer (hSN hs) htL⟩
  have h2 : orderOf (s * t * s⁻¹) = 2 := by
    rw [show s * t * s⁻¹ = s⁻¹⁻¹ * t * s⁻¹ by rw [inv_inv], GSLit.orderOf_conj_inv, hto]
  have h3 := huniq _ h1 h2
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [h3]

theorem exists_eightGroup_of_three_le_pRank {Q : Subgroup G} (h : 3 ≤ pRank 2 ↥Q) :
    ∃ F : Subgroup G, F ≤ Q ∧ IsEightGroup F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := {r : ℕ | ∃ B : Subgroup ↥Q, IsElementaryAbelian 2 ↥B ∧ Nat.card B = 2 ^ r} with hs
  have hne : s.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty] at hn
    have h3 : 3 ≤ sSup s := h
    rw [hn, csSup_empty] at h3
    exact absurd h3 (by decide)
  have hbdd : BddAbove s := by
    refine ⟨Nat.card Q, ?_⟩
    rintro k ⟨B, -, hB⟩
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card Q := card_le_card_group B
  obtain ⟨B, hBe, hBc⟩ := Nat.sSup_mem hne hbdd
  have h8 : 2 ^ 3 ∣ Nat.card B := by
    rw [hBc]
    exact pow_dvd_pow 2 h
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 h8
  refine ⟨(K.map B.subtype).map Q.subtype, (map_subtype_le _), ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩ _ ⟨_, ⟨y, -, rfl⟩, rfl⟩
    have h := hBe.toIsMulCommutative.is_comm.comm x y
    exact congrArg (fun w : B => ((w : ↥Q) : G)) h
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) x.1 x.2
    have h2' := congrArg Subtype.val h2
    rw [← pow_two]
    exact h2'
  · rw [card_map_of_injective Q.subtype_injective, card_map_of_injective B.subtype_injective, hK]
    norm_num

end CFSG.ComponentClassification.GrSLit.GrS5
