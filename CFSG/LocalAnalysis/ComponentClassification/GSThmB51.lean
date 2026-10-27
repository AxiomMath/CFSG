module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBIsoAt
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitTools
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKGroup

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Open CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

theorem schreierSections_of_isKGroupCat (hS : SchreierFor Blueprint.Catalog) {Y : Type}
    [Group Y] [Finite Y] (hY : SectionRank.IsKGroupCat Y) : LBalance.SchreierSections Y := by
  intro A B _ _ hsimple hnc
  have : IsSimpleGroup (A ⧸ B.subgroupOf A) := hsimple
  exact hS _ hnc (hY A (B.subgroupOf A) hsimple)

variable {X : Type} [Group X] [Finite X]

theorem lBalancePLayer_inf_centralizer_le_of_sections {p : ℕ} [Fact p.Prime] {M : Subgroup X}
    (hM : LBalance.SchreierSections ↥M) {x : X} (hxM : x ∈ M) (hx : ∃ n : ℕ, x ^ p ^ n = 1) :
    lBalancePLayer p (M ⊓ centralizer ({x} : Set X)) ≤ lBalancePLayer p M := by
  have hx' : ∃ n : ℕ, (⟨x, hxM⟩ : M) ^ p ^ n = 1 :=
    hx.imp fun n hn => Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hn)
  have hC : (M ⊓ centralizer ({x} : Set X)).subgroupOf M =
      centralizer ({(⟨x, hxM⟩ : M)} : Set M) := by
    ext y
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, true_and,
      mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [← LBalance.pLayer_nested_map p (M ⊓ centralizer ({x} : Set X)) M inf_le_left, hC,
    ← LBalance.pLayer_nested_map p M M le_rfl, subgroupOf_self]
  exact map_mono (LBalance.lBalancePLayer_centralizer_element_le hM hx')

theorem lBalancePLayer_centralizer_sup_le {p : ℕ} [Fact p.Prime] {A' : Subgroup X} {y : X}
    (hyN : y ∈ normalizer (A' : Set X)) (hy : ∃ n : ℕ, y ^ p ^ n = 1)
    (hM : LBalance.SchreierSections ↥(centralizer (A' : Set X) ⊔ zpowers y)) :
    lBalancePLayer p (centralizer ((A' ⊔ zpowers y : Subgroup X) : Set X)) ≤
      lBalancePLayer p (centralizer (A' : Set X)) := by
  have hxY := LBalance.Asm.mem_normalizer_centralizer hyN
  have hYM : centralizer (A' : Set X) ≤ centralizer (A' : Set X) ⊔ zpowers y := le_sup_left
  have hxM : y ∈ centralizer (A' : Set X) ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hMN : centralizer (A' : Set X) ⊔ zpowers y ≤
      normalizer (centralizer (A' : Set X) : Set X) :=
    sup_le le_normalizer (zpowers_le.mpr hxY)
  have hCP : centralizer ((A' ⊔ zpowers y : Subgroup X) : Set X) =
      centralizer (A' : Set X) ⊓ centralizer ({y} : Set X) := by
    refine le_antisymm (le_inf (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers y))))) ?_
    rintro z ⟨hzQ, hzx⟩
    have hle : A' ⊔ zpowers y ≤ centralizer ({z} : Set X) := by
      refine sup_le (fun q hq => mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hzQ q hq)) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hzx).symm
    exact mem_centralizer_iff.mpr fun g hg => mem_centralizer_singleton_iff.mp (hle hg)
  rw [hCP]
  have : ((centralizer (A' : Set X) ⊓ centralizer ({y} : Set X)).subgroupOf
      ((centralizer (A' : Set X) ⊔ zpowers y) ⊓ centralizer ({y} : Set X))).Normal := by
    refine (normal_subgroupOf_iff (inf_le_inf_right _ hYM)).mpr fun z c hz hc =>
      mem_inf.mpr ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hMN (mem_inf.mp hc).1) z).mp (mem_inf.mp hz).1
    · exact mul_mem (mul_mem (mem_inf.mp hc).2 (mem_inf.mp hz).2) (inv_mem (mem_inf.mp hc).2)
  have h1 := LBalance.pLayer_relative_normal_mono p _ _
    (inf_le_inf_right (centralizer ({y} : Set X)) hYM)
  have h2 := lBalancePLayer_inf_centralizer_le_of_sections (p := p) hM hxM hy
  have : ((centralizer (A' : Set X)).subgroupOf (centralizer (A' : Set X) ⊔ zpowers y)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYM).mpr hMN
  have h3 : lBalancePLayer p (centralizer (A' : Set X) ⊔ zpowers y) ≤
      lBalancePLayer p (centralizer (A' : Set X)) := by
    refine LBalance.Asm.pLayer_le_of_pComponents_le p _ _ hYM fun L hL => ?_
    have : Group.IsPerfect L := LBalance.pComponent_perfect p _ L hL
    exact LBalance.Asm.le_of_perfect_le_sup_zpowers hxY (LBalance.subnormal_le hL.1)
  exact h1.trans (h2.trans h3)

theorem lBalancePLayer_centralizer_le_of_le
    (hsch : ∀ M : Subgroup X, M ≠ ⊤ → LBalance.SchreierSections ↥M)
    (hN : ∀ A' : Subgroup X, A' ≠ ⊥ → IsPGroup 2 A' → normalizer (A' : Set X) ≠ ⊤)
    {A : Subgroup X} (hA : IsPGroup 2 A) :
    ∀ A' : Subgroup X, A' ≤ A → A' ≠ ⊥ →
      lBalancePLayer 2 (centralizer (A : Set X)) ≤ lBalancePLayer 2 (centralizer (A' : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro A'
  induction hn : Nat.card A - Nat.card A' using Nat.strong_induction_on generalizing A' with
  | h n ih =>
  intro hA'A hA'
  by_cases heq : A' = A
  · rw [heq]
  have hlt : A' < A := lt_of_le_of_ne hA'A heq
  have : Group.IsNilpotent A := hA.isNilpotent
  have hsub : A'.subgroupOf A < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => heq (le_antisymm hA'A fun z hz => ?_)
    have h1 : (⟨z, hz⟩ : A) ∈ A'.subgroupOf A := htop ▸ mem_top _
    exact h1
  obtain ⟨y, hyN, hyA'⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (A'.subgroupOf A) hsub)
  have hyN' : (y : X) ∈ normalizer (A' : Set X) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (mem_normalizer_iff.mp hyN ⟨z, hA'A hz⟩).mp hz
      exact h1
    · intro hz
      have hzA : z ∈ A := by
        have h2 : y * z * (y : X)⁻¹ ∈ A := hA'A hz
        have h3 := mul_mem (mul_mem (inv_mem y.2) h2) y.2
        rwa [show (y : X)⁻¹ * (y * z * (y : X)⁻¹) * y = z by group] at h3
      exact (mem_normalizer_iff.mp hyN ⟨z, hzA⟩).mpr hz
  have hyA : (y : X) ∉ A' := hyA'
  set A'' := A' ⊔ zpowers (y : X) with hA''def
  have hA''A : A'' ≤ A := sup_le hA'A (zpowers_le.mpr y.2)
  have hA'A'' : A' < A'' := lt_of_le_of_ne le_sup_left fun h =>
    hyA (h ▸ mem_sup_right (mem_zpowers (y : X)))
  have hcardlt : Nat.card A' < Nat.card A'' :=
    card_lt_of_lt hA'A''
  have hcardle : Nat.card A'' ≤ Nat.card A := card_le_of_le hA''A
  have hstep : lBalancePLayer 2 (centralizer (A'' : Set X)) ≤
      lBalancePLayer 2 (centralizer (A' : Set X)) := by
    have hy2 : ∃ n : ℕ, (y : X) ^ 2 ^ n = 1 := by
      obtain ⟨k, hk⟩ := hA y
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hMne : centralizer (A' : Set X) ⊔ zpowers (y : X) ≠ ⊤ := by
      intro htop
      apply hN A' hA' (hA.to_le hA'A)
      refine eq_top_iff.mpr (htop ▸ sup_le ?_ (zpowers_le.mpr hyN'))
      exact Subgroup.centralizer_le_normalizer (A' : Set X)
    exact lBalancePLayer_centralizer_sup_le hyN' hy2 (hsch _ hMne)
  have hrest : lBalancePLayer 2 (centralizer (A : Set X)) ≤
      lBalancePLayer 2 (centralizer (A'' : Set X)) :=
    ih (Nat.card A - Nat.card A'') (by omega) A'' rfl hA''A
      (fun h => hA' (eq_bot_iff.mpr (h ▸ le_of_lt hA'A'')))
  exact hrest.trans hstep

theorem isKGroupCat_of_ne_top' (hK : Assembly.KProper Blueprint.Catalog X) {M : Subgroup X}
    (hM : M ≠ ⊤) : SectionRank.IsKGroupCat ↥M :=
  UnbalancingLocal.kGroupOver_of_kProper (fun e h => SectionRank.catalog_of_mulEquiv e h)
    (fun S _ _ _ hcomm => UnbalancingLocal.catalog_of_abelian_simple S hcomm) hK M hM

theorem normalizer_ne_top_of_simple [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    {A : Subgroup X} (hA1 : A ≠ ⊥) (hA : IsPGroup 2 A) : normalizer (A : Set X) ≠ ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htop
  have hAn : A.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with h | h
  · exact hA1 h
  · obtain ⟨u, v, huv⟩ := hnonab
    have hX : IsPGroup 2 X := by
      rw [h] at hA
      exact hA.of_equiv Subgroup.topEquiv
    have : Nontrivial X := ⟨⟨u * v, v * u, huv⟩⟩
    have hZ := hX.bot_lt_center
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hc | hc
    · exact (ne_of_gt hZ) hc
    · exact huv ((mem_center_iff.mp (hc ▸ mem_top v : v ∈ center X)) u)

omit [Finite X] in
theorem mem_normalizer_of_gsUnbalancingTriple {a x : X} {J : Subgroup X}
    (hU : GSUnbalancingTriple a x J) : x ∈ normalizer (J : Set X) := by
  obtain ⟨-, hx, -, -, -, hJx, -⟩ := gsUnbalancingTriple_iff.mp hU
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hfwd : ∀ n ∈ J, x * n * x⁻¹ ∈ J := by
    intro n hn
    have h1 : ⁅n⁻¹, x⁆ ∈ ⁅J, zpowers x⁆ :=
      commutator_mem_commutator (inv_mem hn) (mem_zpowers x)
    rw [hJx, commutatorElement_def, inv_inv] at h1
    have h2 := mul_mem hn h1
    rwa [show n * (n⁻¹ * x * n * x⁻¹) = x * n * x⁻¹ by group] at h2
  rw [mem_normalizer_iff]
  intro n
  refine ⟨hfwd n, fun hn => ?_⟩
  have h1 := hfwd _ hn
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  rwa [hxinv, show x * (x * n * x) * x = (x * x) * n * (x * x) by group, hxx, one_mul,
    mul_one] at h1

theorem exists_involution_commute {C : Subgroup X} (hC : IsPGroup 2 C) (hC1 : C ≠ ⊥) {t : X}
    (ht : orderOf t = 2) (htC : t ∈ normalizer (C : Set X)) :
    ∃ b ∈ C, orderOf b = 2 ∧ b * t = t * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (zpowers t) := IsPGroup.of_card (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hD : IsPGroup 2 ↥(C ⊔ zpowers t) :=
    hC.to_sup_of_normal_left' ht2 (zpowers_le.mpr htC)
  set D := C ⊔ zpowers t with hDdef
  have hCD : C ≤ D := le_sup_left
  have htD : t ∈ D := mem_sup_right (mem_zpowers t)
  have : Group.IsNilpotent D := hD.isNilpotent
  have hDN : D ≤ normalizer (C : Set X) := sup_le le_normalizer (zpowers_le.mpr htC)
  have : (C.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hCD).mpr hDN
  have hne : C.subgroupOf D ≠ ⊥ := by
    intro h
    apply hC1
    rw [eq_bot_iff]
    intro c hc
    have h1 : (⟨c, hCD hc⟩ : D) ∈ C.subgroupOf D := hc
    rw [h, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  set E := C ⊓ centralizer ({t} : Set X) with hEdef
  have hE2 : IsPGroup 2 E := hC.to_le inf_le_left
  have hE1 : E ≠ ⊥ := by
    obtain ⟨⟨c, hc⟩, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
    obtain ⟨hcC, hcZ⟩ := mem_inf.mp hc
    have hct : (c : X) * t = t * c := by
      have h1 := mem_center_iff.mp hcZ ⟨t, htD⟩
      exact (congrArg Subtype.val h1).symm
    intro hEb
    have hcE : (c : X) ∈ E := mem_inf.mpr ⟨hcC, mem_centralizer_singleton_iff.mpr hct⟩
    rw [hEb, mem_bot] at hcE
    exact hc1 (Subtype.ext (Subtype.ext hcE))
  have : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hE1
  have hdvd : 2 ∣ Nat.card E := hE2.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨g, (mem_inf.mp g.2).1, by rw [← hg, Subgroup.orderOf_coe], ?_⟩
  exact mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).2

omit [Finite X] in
theorem commutator_le_oddCoreIn {L T : Subgroup X} {a : X} (haL : a ∈ normalizer (L : Set X))
    (hTL : T ≤ L) (hTa : T ≤ centralizer ({a} : Set X))
    (hsup : T ⊔ (pPrimeCore 2 L).map L.subtype = L) :
    ⁅L, zpowers a⁆ ≤ oddCoreIn L := by
  have hON : ∀ g ∈ normalizer (L : Set X), g ∈ normalizer (oddCoreIn L : Set X) := fun g hg =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) hg
  have haO : a ∈ normalizer (oddCoreIn L : Set X) := hON a haL
  rw [commutator_le]
  intro l hl z hz
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hlmul : l ∈ (T : Set X) * ((pPrimeCore 2 L).map L.subtype : Set X) := by
    rw [← UnbalancedGS.coe_sup_primeCore_eq_mul hTL, hsup]
    exact hl
  obtain ⟨j, hj, o, ho, rfl⟩ := hlmul
  have hjL : j ∈ L := hTL hj
  have hja : j * a = a * j := mem_centralizer_singleton_iff.mp (hTa hj)
  have hjak : j * a ^ k = a ^ k * j :=
    ((Commute.zpow_right (show Commute j a from hja) k))
  have haOk : a ^ k ∈ normalizer (oddCoreIn L : Set X) := zpow_mem haO k
  have h1 : a ^ k * o⁻¹ * (a ^ k)⁻¹ ∈ oddCoreIn L :=
    (mem_normalizer_iff.mp haOk _).mp (inv_mem ho)
  have h2 : o * (a ^ k * o⁻¹ * (a ^ k)⁻¹) ∈ oddCoreIn L := mul_mem ho h1
  have hjO : j ∈ normalizer (oddCoreIn L : Set X) := hON j (le_normalizer hjL)
  have h3 := (mem_normalizer_iff.mp hjO _).mp h2
  have heq : ⁅j * o, a ^ k⁆ = j * (o * (a ^ k * o⁻¹ * (a ^ k)⁻¹)) * j⁻¹ := by
    rw [commutatorElement_def]
    calc j * o * a ^ k * (j * o)⁻¹ * (a ^ k)⁻¹
        = j * o * (a ^ k * o⁻¹) * (j⁻¹ * (a ^ k)⁻¹) := by group
      _ = j * o * (a ^ k * o⁻¹) * ((a ^ k)⁻¹ * j⁻¹) := by
        rw [show j⁻¹ * (a ^ k)⁻¹ = (a ^ k * j)⁻¹ by group,
          show (a ^ k)⁻¹ * j⁻¹ = (j * a ^ k)⁻¹ by group, hjak]
      _ = j * (o * (a ^ k * o⁻¹ * (a ^ k)⁻¹)) * j⁻¹ := by group
  rw [heq]
  exact h3

theorem inf_conjugate_eq_bot [IsSimpleGroup X] (hS : SchreierFor Blueprint.Catalog)
    (hnonab : ∃ u v : X, u * v ≠ v * u) (hK : Assembly.KProper Blueprint.Catalog X)
    {a x : X} {J : Subgroup X} (hmax : GSMaximalUnbalancingTriple a x J)
    (hiso : GSIsoAt a J)
    {B : Subgroup X} (hB2 : IsPGroup 2 B) (hBa : B ≤ centralizer ({a} : Set X))
    (hBJ : B ≤ coreActionKernel J)
    (hcl : conjClosure (GSLit.fixedLayer J B) (layerIn (normalizer (B : Set X))) =
      layerIn (normalizer (B : Set X)))
    (hcomm : ⁅layerIn (normalizer (B : Set X)), zpowers a⁆ =
      layerIn (normalizer (B : Set X))) :
    B ⊓ conjugate B x = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := hmax.1
  obtain ⟨ha, hx, hax, hJa, hJ, -, -⟩ := gsUnbalancingTriple_iff.mp hU
  have hxx : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxJ : x ∈ normalizer (J : Set X) := mem_normalizer_of_gsUnbalancingTriple hU
  have hxa : x ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hax.symm
  have hJq := GSLit.isQuasisimple_of_gsUnbalancingTriple hU
  by_contra hne
  set C := B ⊓ conjugate B x with hCdef
  have hxC : x ∈ normalizer (C : Set X) := by
    rw [mem_normalizer_iff]
    intro z
    simp only [hCdef, mem_inf, mem_conjugate_iff]
    rw [show x * (x * z * x⁻¹) * x⁻¹ = z by
      calc x * (x * z * x⁻¹) * x⁻¹ = (x * x) * z * (x * x)⁻¹ := by group
        _ = z := by rw [hxx]; group]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  obtain ⟨b, hbC, hb, hbx⟩ := exists_involution_commute (hB2.to_le inf_le_left) hne hx hxC
  have hbB : b ∈ B := (mem_inf.mp hbC).1
  have hab : a * b = b * a := (mem_centralizer_singleton_iff.mp (hBa hbB)).symm
  obtain ⟨L, hL, -⟩ := hiso x b (mem_inf.mpr ⟨hxa, hxJ⟩) hU hb hab hbx.symm (hBJ hbB)
  obtain ⟨hC', hLa, hsupL⟩ := UnbalancedGS.gsIsoCorr_iff_sup.mp hL
  have hLb : L ≤ centralizer ({b} : Set X) := hC'.2.2.2.2.2.1
  have hLpc : IsPComponent 2 (L.subgroupOf (centralizer ({b} : Set X))) := hC'.2.2.2.2.2.2.1
  have hJBb : GSLit.fixedLayer J B ≤ UnbalancedGS.gsFixedLayer J b := by
    rw [← GSLit.fixedLayer_zpowers]
    exact (GSLit.fixedLayer_nested hJq hBJ hB2 (zpowers_le.mpr hbB)).1
  have hJbL : UnbalancedGS.gsFixedLayer J b ≤ L := hC'.gsFixedLayer_le hLa
  have hJBL : GSLit.fixedLayer J B ≤ L := hJBb.trans hJbL
  have hsch : ∀ M : Subgroup X, M ≠ ⊤ → LBalance.SchreierSections ↥M := fun M hM =>
    schreierSections_of_isKGroupCat hS (isKGroupCat_of_ne_top' hK hM)
  have hNt : ∀ A' : Subgroup X, A' ≠ ⊥ → IsPGroup 2 A' → normalizer (A' : Set X) ≠ ⊤ :=
    fun A' h1 h2 => normalizer_ne_top_of_simple hnonab h1 h2
  have hb1 : zpowers b ≠ ⊥ := by
    intro h
    have : b = 1 := by
      have h1 : b ∈ zpowers b := mem_zpowers b
      rwa [h, mem_bot] at h1
    rw [this, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hVle : layerIn (normalizer (B : Set X)) ≤ layerIn (centralizer ({b} : Set X)) := by
    have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) B hB2
    have h2 := lBalancePLayer_centralizer_le_of_le hsch hNt hB2 (zpowers b)
      (zpowers_le.mpr hbB) hb1
    rw [centralizer_zpowers_eq] at h2
    have h3 := h1.trans h2
    rwa [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h3
  have hEN : layerIn (centralizer ({b} : Set X)) ≤ normalizer (L : Set X) :=
    UGSChain.map_pLayer_le_normalizer hLb hLpc
  have hVL : layerIn (normalizer (B : Set X)) ≤ L := by
    rw [← hcl]
    refine iSup₂_le fun v hv => ?_
    have hvN : v ∈ normalizer (L : Set X) := hEN (hVle hv)
    calc conjugate (GSLit.fixedLayer J B) v ≤ conjugate L v := map_mono hJBL
      _ = L := by
        have hvN' : v⁻¹ ∈ normalizer (L : Set X) := inv_mem hvN
        exact UnbalancedLayer.conjugate_eq_of_mem_normalizer hvN
  have haL : a ∈ normalizer (L : Set X) := by
    have hle : conjugate L a ≤ L := by
      have h2 := hLa
      rw [sup_eq_left] at h2
      exact h2
    have hcard : Nat.card L ≤ Nat.card (conjugate L a) := by
      rw [conjugate, card_map_of_injective (MulAut.conj a⁻¹).injective]
    have heq : conjugate L a = L := eq_of_le_of_card_ge hle hcard
    rw [mem_normalizer_iff]
    intro z
    rw [← mem_conjugate_iff, heq]
  have hTa : UnbalancedGS.gsFixedLayer J b ≤ centralizer ({a} : Set X) :=
    (UnbalancedGS.gsFixedLayer_le_inf J b).trans (inf_le_left.trans hJa)
  have hLO : ⁅L, zpowers a⁆ ≤ oddCoreIn L := commutator_le_oddCoreIn haL hJbL hTa hsupL
  have hVO : layerIn (normalizer (B : Set X)) ≤ oddCoreIn L := by
    rw [← hcomm]
    exact (commutator_mono hVL le_rfl).trans hLO
  have hJBV : GSLit.fixedLayer J B ≤ layerIn (normalizer (B : Set X)) := by
    rw [← hcl]
    refine le_trans ?_ (le_iSup₂_of_le (1 : X) (one_mem _) le_rfl)
    intro z hz
    refine ⟨z, hz, ?_⟩
    simp
  have hJBO : GSLit.fixedLayer J B ≤ oddCoreIn L := hJBV.trans hVO
  have hodd : Odd (Nat.card (oddCoreIn L)) := by
    rw [oddCoreIn, card_map_of_injective L.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (pPrimeCore_coprime_card (p := 2)
        (G := L)) h)
  have hJBbot : GSLit.fixedLayer J B = ⊥ := by
    rw [GSLit.fixedLayer_eq_closure hJq hBJ hB2, closure_eq_bot_iff]
    rintro z ⟨hz, k, hk⟩
    have hzJB : z ∈ GSLit.fixedLayer J B := by
      rw [GSLit.fixedLayer_eq_closure hJq hBJ hB2]
      exact subset_closure ⟨hz, k, hk⟩
    have hdvd : orderOf z ∣ Nat.card (oddCoreIn L) := Subgroup.orderOf_dvd_natCard _ (hJBO hzJB)
    rw [hk] at hdvd
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · exfalso
      have h2 : 2 ∣ Nat.card (oddCoreIn L) := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hsupJ := (GSLit.fixedLayer_sup_pPrimeCore hJq hBJ hB2).1
  rw [hJBbot, bot_sup_eq] at hsupJ
  have htop : ∀ j : J, j ∈ pPrimeCore 2 J := by
    intro j
    have hj : (j : X) ∈ (pPrimeCore 2 J).map J.subtype := by
      rw [hsupJ]
      exact j.2
    obtain ⟨o, ho, hoj⟩ := mem_map.mp hj
    rwa [show o = j from Subtype.ext hoj] at ho
  obtain ⟨u, v, huv⟩ := hJq.2.2
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  have hu : ((u : J ⧸ pPrimeCore 2 J) : (J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) =
      1 := by
    rw [(QuotientGroup.eq_one_iff (N := pPrimeCore 2 J) u).mpr (htop u)]
    rfl
  rw [hu, one_mul, mul_one]

end CFSG.ComponentClassification.GSThmB
