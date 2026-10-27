module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5STwoSuzPerfect
public import CFSG.Sporadic.Recognition.LyonsAS44ConjPerm
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSupport

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pRank_centralizer_le_of_zStarAutRank
    (hS : SchreierFor Blueprint.Catalog) (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hheld : KProperRelativeB.HeldInput) {t : G} {P : Subgroup G} {r : ℕ}
    (hbase : L34BaseSetting G) (ht2 : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hPc : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hPn : (P.subgroupOf (centralizer ({t} : Set G))).Normal)
    (hAut : pRank 2 (MulAut (↥P ⧸ Open.fusionZStar ↥P)) ≤ r)
    (hW : ∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
      8 ≤ Nat.card E → wGroup E = ⊥)
    (hD : ⁅oddIn P, P⁆ ≠ ⊥) :
    pRank 2 ↥(centralizer ({t} : Set G)) ≤ r + 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  set C := centralizer ({t} : Set G) with hC
  have hCN : C ≤ normalizer (P : Set G) := (normal_subgroupOf_iff_le_normalizer hPt).mp hPn
  set φ : ↥C →* MulAut (↥P ⧸ Open.fusionZStar ↥P) :=
    (GSThmB.A10T.zStarAct P).comp (Subgroup.inclusion hCN) with hφ
  have : Finite (MulAut (↥P ⧸ Open.fusionZStar ↥P)) :=
    Finite.of_injective (fun f : MulAut (↥P ⧸ Open.fusionZStar ↥P) =>
      (f : ↥P ⧸ Open.fusionZStar ↥P → ↥P ⧸ Open.fusionZStar ↥P))
      fun f g h => MulEquiv.ext (congrFun h)
  have himg : pRank 2 (↥C ⧸ φ.ker) ≤ r := by
    have hinj : Function.Injective ((φ.range.subtype).comp
        (QuotientGroup.quotientKerEquivRange φ).toMonoidHom) :=
      (Subgroup.subtype_injective _).comp (QuotientGroup.quotientKerEquivRange φ).injective
    exact (RankThree.OddKernel.pRank_le_of_injective (by norm_num) _ hinj).trans hAut
  have hker : pRank 2 ↥φ.ker ≤ 2 := by
    by_contra hlt
    push Not at hlt
    rw [SectionRank.pRank_eq_open_pRank_top] at hlt
    obtain ⟨E, -, hE, hEc⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup ↥φ.ker)
    set E' : Subgroup G := (E.map φ.ker.subtype).map C.subtype with hE'
    have hE'C : E' ≤ C := map_subtype_le _
    have hE'card : Nat.card E' = 2 ^ Open.pRank 2 (⊤ : Subgroup ↥φ.ker) := by
      rw [hE', card_map_of_injective C.subtype_injective,
        card_map_of_injective φ.ker.subtype_injective, hEc]
    have hE'ab : Open.IsElemAbelian 2 E' := by
      have h1 := SectionRank.isElemAbelian_map hE φ.ker.subtype
      exact SectionRank.isElemAbelian_map h1 C.subtype
    have hE'8 : 8 ≤ Nat.card E' := by
      rw [hE'card]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ Open.pRank 2 (⊤ : Subgroup ↥φ.ker) := Nat.pow_le_pow_right (by norm_num) hlt
    have hWE := hW E' hE'C hE'ab hE'8
    have hE'K : ∀ e ∈ E', e ∈ coreActionKernel P := by
      rintro _ ⟨c, ⟨k, hk, rfl⟩, rfl⟩
      have h1 : φ k = 1 := k.2
      have h2 := (GSThmB.A10T.zStarAct_eq_one_iff hPt hPc (Subgroup.inclusion hCN k)).mp h1
      exact h2
    have hcom := oddCore_le_center_of_wGroup_eq_bot hPt hPc hE'C
      (isMulCommutative_iff_of_setLike.mp hE'ab.1)
      (fun x hx => by rw [← pow_two]; exact hE'ab.2 x hx) (by omega)
      (hE'C.trans hCN) (fun e he => GrS5.conj_mem_oddIn_of_mem_coreActionKernel (hE'K e he))
      hWE
      (fun e he he1 => GrS5.commutator_oddCore_pLayer_le hS hU hheld hK ht2 hPt hPc
        ((mem_centralizer_singleton_iff.mp (hE'C he)).symm)
        (GrS5.centralizer_ne_top_of_not_mem_center (GrS5.not_mem_center_of_ne_one hnonab he1)))
      (Or.inr hE'8)
    apply hD
    rw [eq_bot_iff, commutator_le]
    intro x hx l hl
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcom x hx l hl
  calc pRank 2 ↥C ≤ pRank 2 ↥φ.ker + pRank 2 (↥C ⧸ φ.ker) :=
        RankThree.OddKernel.pRank_le_add_of_normal Nat.prime_two φ.ker
    _ ≤ 2 + r := Nat.add_le_add hker himg
    _ = r + 2 := by ring

end

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_oddIn_centralizer_of_trivial_on_active {t a : G} (ht : orderOf t = 2)
    (ha : orderOf a = 2) (hta : t * a = a * t) {Y K : Subgroup G}
    (hY : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G)) (hKY : K ≤ Y)
    (hK : ∀ k ∈ K, ∀ J ∈ activeTwoComponents a Y, k ∈ coreActionKernel J) :
    K ≤ oddIn (centralizer ({a} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) with hH
  have hsol := GrS5.solomon_involutions solomonCommutingCoreInput ht ha hta
  have hYH : Y ≤ H := hY.trans inf_le_right
  have hKH : K ≤ H := hKY.trans hYH
  have hYodd : Odd (Nat.card Y) := by
    have h1 : Nat.card Y ∣ Nat.card ↥(oddIn (centralizer ({t} : Set G))) :=
      Subgroup.card_dvd_of_le (hY.trans inf_le_left)
    refine Odd.of_dvd_nat ?_ h1
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  set D : Subgroup ↥H := K.subgroupOf H with hD
  have hDodd : Odd (Nat.card D) := by
    rw [hD, Nat.card_congr (subgroupOfEquivOfLe hKH).toEquiv]
    exact hYodd.of_dvd_nat (Subgroup.card_dvd_of_le hKY)
  have hDmem : ∀ d ∈ D, (d : G) ∈ K := fun d hd => mem_subgroupOf.mp hd
  have hpull : ∀ x : ↥H, (x : G) ∈ oddIn H → x ∈ pPrimeCore 2 ↥H := fun x hx =>
    (mem_map_iff_mem H.subtype_injective).mp hx
  have hDle : D ≤ pPrimeCore 2 ↥H := by
    refine GrS5.le_pPrimeCore_of_commute hDodd ?_ ?_
    · intro m hm d hd
      apply hpull
      have h1 := hsol.1 (commutator_mem_commutator (mem_map_of_mem H.subtype hm)
        (Subgroup.mem_inf.mpr ⟨(hY (hKY (hDmem d hd))).1, d.2⟩))
      simpa [commutatorElement_def] using h1
    · intro M hM m hm d hd
      apply hpull
      set M' : Subgroup G := M.map H.subtype with hM'
      have hM'H : M' ≤ H := map_subtype_le _
      have hM's : M'.subgroupOf H = M := comap_map_eq_self_of_injective H.subtype_injective _
      have hM'c : IsPComponent 2 (M'.subgroupOf H) := hM's ▸ hM
      have hmM' : (m : G) ∈ M' := mem_map_of_mem _ hm
      have hO : oddIn M' ≤ oddIn H := GSLit.map_pPrimeCore_le_of_isPComponent hM'H hM'c
      by_cases hact : M' ∈ activeTwoComponents a Y
      · have hdK : (d : G) ∈ coreActionKernel M' := hK _ (hDmem d hd) M' hact
        have h1 := GrS5.conj_mem_oddIn_of_mem_coreActionKernel hdK (m : G) hmM'
        have h2 := hO ((oddIn M').inv_mem h1)
        have e : ((m * d * m⁻¹ * d⁻¹ : ↥H) : G) =
            ((d : G) * m * (d : G)⁻¹ * (m : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact h2
      · have hinact : ⁅M', Y⁆ ≤ oddIn M' := by
          by_contra hc
          exact hact ⟨hM'H, hM'c, hc⟩
        have h1 := hO (hinact (commutator_mem_commutator hmM' (hKY (hDmem d hd))))
        simpa [commutatorElement_def] using h1
  intro x hx
  have hxD : (⟨x, hKH hx⟩ : ↥H) ∈ D := mem_subgroupOf.mpr hx
  exact ⟨_, hDle hxD, rfl⟩

theorem inf_oddIn_eq_bot_of_wGroup_eq_bot {t v : G} {B : Subgroup G} (ht : orderOf t = 2)
    (hv : orderOf v = 2) (htv : t * v = v * t) (hne : t ≠ v) (htB : t ∈ B) (hvB : v ∈ B)
    (hW : wGroup B = ⊥) :
    oddIn (centralizer ({t} : Set G)) ⊓ oddIn (centralizer ({v} : Set G)) ⊓
      oddIn (centralizer ({t * v} : Set G)) = ⊥ := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by norm_num)
  have hpow2 : ∀ x : G, orderOf x = 2 → ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro x hx k
    rw [← zpow_mod_orderOf, hx]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [Nat.cast_ofNat, h0, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h1, zpow_one]
  have htnv : t ∉ zpowers v := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    rcases hpow2 v hv k with h0 | h1
    · rw [h0] at hk
      exact ht1 hk.symm
    · rw [h1] at hk
      exact hne hk.symm
  have htzv : ∀ y ∈ zpowers v, t * y = y * t := fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_right htv k).eq
  obtain ⟨hF2, hFcard⟩ := GrS5.elemTwo_zpowers_sup htt (isElemTwo_zpowers hvv) htzv htnv
  have hF4 : 4 ≤ Nat.card ↥(zpowers t ⊔ zpowers v) := by
    rw [hFcard, Nat.card_zpowers, hv]
  have hFB : zpowers t ⊔ zpowers v ≤ B :=
    sup_le (zpowers_le.mpr htB) (zpowers_le.mpr hvB)
  have hΔ := iInf_oddIn_le_wGroup hFB hF4 hF2.2
  rw [hW] at hΔ
  have hFmem : ∀ b ∈ zpowers t ⊔ zpowers v, b ≠ 1 → b = t ∨ b = v ∨ b = t * v := by
    intro b hb hb1
    obtain ⟨i, h, hh, rfl⟩ := GrS5.mem_zpowers_sup htzv hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh
    rcases hpow2 t ht i with hi | hi <;> rcases hpow2 v hv j with hj | hj <;>
      rw [hi, hj] at hb1 ⊢
    · exact absurd (one_mul 1) hb1
    · exact Or.inr (Or.inl (one_mul v))
    · exact Or.inl (mul_one t)
    · exact Or.inr (Or.inr rfl)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hy' : y ∈ ⨅ (b : G) (_ : b ∈ zpowers t ⊔ zpowers v) (_ : b ≠ 1),
      oddIn (centralizer ({b} : Set G)) := by
    simp only [mem_iInf]
    intro b hb hb1
    rcases hFmem b hb hb1 with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  exact hΔ hy'

end

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement
open CFSG.Sporadic.Recognition.LyonsSims (conjSub conjPerm mem_conjSub_iff)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem commute_conj_act {k x t : G} (hk : Commute k t) (hx : Commute x t) :
    Commute (k * x * k⁻¹) t :=
  (hk.mul_left hx).mul_left hk.inv_left

omit [Finite G] in
private theorem map_oddIn_conj (c : G ≃* G) (J : Subgroup G) :
    (oddIn J).map c.toMonoidHom = oddIn (J.map c.toMonoidHom) :=
  GSLit.map_map_pPrimeCore c J

omit [Finite G] in
private theorem map_centralizer_eq_of_commute {t x : G} (hx : Commute x t) :
    (centralizer ({t} : Set G)).map (MulAut.conj x).toMonoidHom =
      centralizer ({t} : Set G) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (commute_conj_act hx (mem_centralizer_singleton_iff.mp hz))
  · intro hy
    refine ⟨x⁻¹ * y * x⁻¹⁻¹, mem_centralizer_singleton_iff.mpr
      (commute_conj_act hx.inv_left (mem_centralizer_singleton_iff.mp hy)), ?_⟩
    show x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y
    group

omit [Finite G] in
private theorem conj_mem_inf_oddIn_centralizer {t a : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    {h y : G} (hh : h ∈ H)
    (hy : y ∈ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G)) :
    h * y * h⁻¹ ∈ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) := by
  obtain ⟨hyt, hya⟩ := Subgroup.mem_inf.mp hy
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : h * y * h⁻¹ ∈ (oddIn (centralizer ({t} : Set G))).map
        (MulAut.conj h).toMonoidHom := Subgroup.mem_map_of_mem _ hyt
    rwa [map_oddIn_conj,
      map_centralizer_eq_of_commute (mem_centralizer_singleton_iff.mp (hHt hh))] at h1
  · exact mem_centralizer_singleton_iff.mpr (commute_conj_act
      (mem_centralizer_singleton_iff.mp (hHa hh)) (mem_centralizer_singleton_iff.mp hya))

omit [Finite G] in
private theorem map_inf_oddIn_centralizer_conj {t a : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    {g : G} (hg : g ∈ H) :
    (oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G)).map
        (MulAut.conj g).toMonoidHom =
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact conj_mem_inf_oddIn_centralizer hHt hHa hg hy
  · intro hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹,
      conj_mem_inf_oddIn_centralizer hHt hHa (H.inv_mem hg) hx, ?_⟩
    show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group

omit [Finite G] in
private theorem activeTwoComponents_conjSub_mem {t a : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    {g : G} (hg : g ∈ H) {B : Subgroup G}
    (hB : B ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))) :
    conjSub g B ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)) := by
  have hga : g⁻¹ * a = a * g⁻¹ :=
    (show Commute g a from mem_centralizer_singleton_iff.mp (hHa hg)).inv_left
  obtain ⟨hBa, hBc, hBn⟩ := hB
  obtain ⟨h1, h2⟩ := UGSChain.conjugate_isPComponent_centralizer hga hBa hBc
  have hcj : CFSG.conjugate B g⁻¹ = conjSub g B := by
    show B.map (MulAut.conj g⁻¹⁻¹).toMonoidHom = B.map (MulAut.conj g).toMonoidHom
    rw [inv_inv]
  rw [hcj] at h1 h2
  refine ⟨h1, h2, fun hc => hBn ?_⟩
  have key : (⁅B, oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      (oddIn B).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, map_inf_oddIn_centralizer_conj hHt hHa hg,
      map_oddIn_conj]
    exact hc
  exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).mp key

private theorem activeTwoComponents_conjSub_eq_self {t a : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcnt : (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))).ncard ≤ 8) :
    ∀ g ∈ H, ∀ J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)), conjSub g J = J := by
  classical
  have hHperf : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hHp
  set Aset : Set (Subgroup G) := activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
    centralizer ({a} : Set G)) with hAset
  have hstab : ∀ g ∈ H, ∀ B ∈ Aset, conjSub g B ∈ Aset := fun g hg B hB =>
    activeTwoComponents_conjSub_mem hHt hHa hg hB
  have hcardA : Nat.card ↥Aset ≤ 8 := (Nat.card_coe_set_eq Aset).trans_le hcnt
  have hφ := perm_eq_one_of_perfect hHperf hH3 hcardA (conjPerm H Aset hstab)
  intro g hg J hJ
  have h1 : conjPerm H Aset hstab ⟨g, hg⟩ = 1 :=
    congrArg (fun F : H →* Equiv.Perm ↥Aset => F ⟨g, hg⟩) hφ
  exact congrArg (fun σ : Equiv.Perm ↥Aset =>
    ((σ ⟨J, hJ⟩ : ↥Aset) : Subgroup G)) h1

private theorem le_normalizer_of_active_conjSub {t a : G} {H : Subgroup G}
    (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcnt : (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))).ncard ≤ 8) :
    ∀ J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)), ∀ g ∈ H, g ∈ normalizer (J : Set G) := by
  intro J hJ g hg
  have hc := activeTwoComponents_conjSub_eq_self hHt hHa hHp hH3 hcnt g hg J hJ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key := mem_conjSub_iff (g := g) (B := J) (x := g * x * g⁻¹)
  rw [hc] at key
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at key
  exact key.symm

private theorem zStarAct_eq_one_of_active_support {t a : G} {H : Subgroup G}
    (ht : orderOf t = 2) (ha : orderOf a = 2) (hta : t * a = a * t)
    (htypes : ∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hnorm : ∀ J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)), ∀ g ∈ H, g ∈ normalizer (J : Set G))
    {J : Subgroup G}
    (hJ : J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))) {g : G} (hg : g ∈ H) :
    GSThmB.A10T.zStarAct J ⟨g, hnorm J hJ g hg⟩ = 1 := by
  have hJH : J ≤ centralizer ({a} : Set G) := hJ.1
  have hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) := hJ.2.1
  have hHJ : H ≤ normalizer (J : Set G) := fun x hx => hnorm J hJ x hx
  have hT : GSUnbalancingTriple a t J :=
    GrS5.gsUnbalancingTriple_of_not_le solomonCommutingCoreInput ht ha hta hJH hJc
      (le_refl _) hJ.2.2
  have : Group.IsPerfect ↥J := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJc
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJH).toMonoidHom)
      (subgroupOfEquivOfLe hJH).surjective
  have hdvd : Nat.card (MulAut (↥J ⧸ Open.fusionZStar ↥J)) ∣ 2 ^ 8 * 945 :=
    card_mulAut_fusionZStar_dvd (htypes J hT)
  let ψ : ↥H →* MulAut (↥J ⧸ Open.fusionZStar ↥J) :=
    (GSThmB.A10T.zStarAct J).comp (Subgroup.inclusion hHJ)
  have hf : ¬ 3 ^ 4 ∣ Nat.card ψ.range := by
    intro hd
    have h1 := hd.trans ((Subgroup.card_subgroup_dvd_card ψ.range).trans hdvd)
    exact absurd h1 (by decide)
  have hψ : ψ = 1 := eq_one_of_perfect_of_hasSimpleQuotient
    (Subgroup.isPerfect_iff.mpr hHp) hH3 ψ hf
  exact congrArg (fun F : ↥H →* MulAut (↥J ⧸ Open.fusionZStar ↥J) => F ⟨g, hg⟩) hψ

theorem zStarAct_eq_one_of_perfect_active {t a : G} (ht : orderOf t = 2)
    (ha : orderOf a = 2) (hta : t * a = a * t)
    (htypes : ∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J))
    {H : Subgroup G} (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcnt : (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))).ncard ≤ 8) :
    ∀ J ∈ activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G)), ∀ g ∈ H, ∃ hg : g ∈ normalizer (J : Set G),
        GSThmB.A10T.zStarAct J ⟨g, hg⟩ = 1 := by
  have hnorm := le_normalizer_of_active_conjSub hHt hHa hHp hH3 hcnt
  intro J hJ g hg
  exact ⟨hnorm J hJ g hg,
    zStarAct_eq_one_of_active_support ht ha hta htypes hHp hH3 hnorm hJ hg⟩

theorem commutator_le_oddIn_of_perfect_active {t a : G} (ht : orderOf t = 2)
    (ha : orderOf a = 2) (hta : t * a = a * t)
    (htypes : ∀ J : Subgroup G, GSUnbalancingTriple a t J →
      IsL2Type 5 (J ⧸ pPrimeCore 2 J) ∨ IsL2Type 7 (J ⧸ pPrimeCore 2 J) ∨
      IsL34Type (J ⧸ Open.fusionZStar J))
    {H : Subgroup G} (hHt : H ≤ centralizer ({t} : Set G)) (hHa : H ≤ centralizer ({a} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H)
    (hcnt : (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
      centralizer ({a} : Set G))).ncard ≤ 8) :
    ⁅H, oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G)⁆ ≤
      oddIn (centralizer ({a} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({a} : Set G) with hYdef
  set Aset : Set (Subgroup G) := activeTwoComponents a Y with hAset
  have hsol := GrS5.solomon_involutions solomonCommutingCoreInput ht ha hta
  have hNY : ∀ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y := by
    intro h hh y hy
    rw [hYdef] at hy ⊢
    exact conj_mem_inf_oddIn_centralizer hHt hHa hh hy
  have hKY : ⁅H, Y⁆ ≤ Y := by
    rw [Subgroup.commutator_le]
    intro h hh y hy
    rw [commutatorElement_def]
    exact Y.mul_mem (hNY h hh y hy) (Y.inv_mem hy)
  have hhz := zStarAct_eq_one_of_perfect_active ht ha hta htypes hHt hHa hHp hH3 hcnt
  have hcomm_ker : ∀ J ∈ Aset, ∀ g ∈ H, ∀ y ∈ Y, ⁅g, y⁆ ∈ coreActionKernel J := by
    intro J hJ g hg y hy
    have hJH : J ≤ centralizer ({a} : Set G) := hJ.1
    have hJc : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))) := hJ.2.1
    have hyN : y ∈ normalizer (J : Set G) := (hsol.2 J hJH hJc).1 hy
    obtain ⟨hgn, hzgn⟩ := hhz J hJ g hg
    have hcomm : GSThmB.A10T.zStarAct J
        ⁅(⟨g, hgn⟩ : ↥(normalizer (J : Set G))), ⟨y, hyN⟩⁆ = 1 := by
      rw [map_commutatorElement, hzgn, commutatorElement_one_left]
    have hmem := (GSThmB.A10T.zStarAct_eq_one_iff hJH hJc _).mp hcomm
    have e : ((⁅(⟨g, hgn⟩ : ↥(normalizer (J : Set G))), ⟨y, hyN⟩⁆ :
        ↥(normalizer (J : Set G))) : G) = ⁅g, y⁆ := by
      simp [commutatorElement_def]
    rw [e] at hmem
    exact hmem
  have hK : ∀ k ∈ ⁅H, Y⁆, ∀ J ∈ Aset, k ∈ coreActionKernel J := by
    intro k hk J hJ
    have hle : ⁅H, Y⁆ ≤ coreActionKernel J := by
      rw [Subgroup.commutator_le]
      intro h hh y hy
      exact hcomm_ker J hJ h hh y hy
    exact hle hk
  exact le_oddIn_centralizer_of_trivial_on_active ht ha hta (le_refl Y) hKY hK

end

section

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_bot_of_perfect_twoInvolutions
    (hbase : L34BaseSetting G) {t v : G} (ht : orderOf t = 2) (hv : orderOf v = 2)
    (htv : t * v = v * t) (hne : t ≠ v) {B : Subgroup G} (htB : t ∈ B) (hvB : v ∈ B)
    (hW : wGroup B = ⊥) (hrank : pRank 2 ↥(centralizer ({t} : Set G)) ≤ 8)
    {H : Subgroup G} (hHt : H ≤ centralizer ({t} : Set G)) (hHv : H ≤ centralizer ({v} : Set G))
    (hHp : ⁅H, H⁆ = H) (hH3 : HasSimpleQuotient3Quart ↥H) :
    ⁅H, oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({v} : Set G)⁆ = ⊥ := by
  have htypes := hbase.2.2.2.2.2.2.2
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have htv2 : orderOf (t * v) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, show t * v * (t * v) = t * t * (v * v) by
        rw [mul_assoc, ← mul_assoc v t v, ← htv]; group, htt, hvv, one_mul]
    · intro h
      apply hne
      calc t = t * (v * v) := by rw [hvv, mul_one]
        _ = t * v * v := by rw [mul_assoc]
        _ = v := by rw [h, one_mul]
  have htvt : t * (t * v) = t * v * t := ((Commute.refl t).mul_right htv).eq
  have hOt : oddIn (centralizer ({t} : Set G)) ≤ centralizer ({t} : Set G) := map_subtype_le _
  have hY' : oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({v} : Set G) =
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({t * v} : Set G) := by
    ext y
    simp only [mem_inf]
    constructor
    · rintro ⟨hy, hyv⟩
      have hyt : Commute y t := mem_centralizer_singleton_iff.mp (hOt hy)
      have hyv' : Commute y v := mem_centralizer_singleton_iff.mp hyv
      exact ⟨hy, mem_centralizer_singleton_iff.mpr (hyt.mul_right hyv').eq⟩
    · rintro ⟨hy, hytv⟩
      have hyt : Commute y t := mem_centralizer_singleton_iff.mp (hOt hy)
      have hytv' : Commute y (t * v) := mem_centralizer_singleton_iff.mp hytv
      have h := hyt.inv_right.mul_right hytv'
      rw [inv_mul_cancel_left] at h
      exact ⟨hy, mem_centralizer_singleton_iff.mpr h.eq⟩
  have hcnt : ∀ a : G, orderOf a = 2 → t * a = a * t →
      (activeTwoComponents a (oddIn (centralizer ({t} : Set G)) ⊓
        centralizer ({a} : Set G))).ncard ≤ 8 := fun a ha hta =>
    (l34ActiveSupportCount_holds G t a ht ha hta (fun J hJ => htypes a t J hJ) _ le_rfl).trans
      ((pRank_two_le_of_le inf_le_left).trans hrank)
  have h1 := commutator_le_oddIn_of_perfect_active ht hv htv (fun J hJ => htypes v t J hJ) hHt hHv
    hHp hH3 (hcnt v hv htv)
  have hHtv : H ≤ centralizer ({t * v} : Set G) := fun h hh => by
    have h1 : Commute h t := mem_centralizer_singleton_iff.mp (hHt hh)
    have h2 : Commute h v := mem_centralizer_singleton_iff.mp (hHv hh)
    exact mem_centralizer_singleton_iff.mpr (h1.mul_right h2).eq
  have h2 := commutator_le_oddIn_of_perfect_active ht htv2 htvt
    (fun J hJ => htypes (t * v) t J hJ) hHt hHtv hHp hH3 (hcnt (t * v) htv2 htvt)
  rw [← hY'] at h2
  have h3 : ⁅H, oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({v} : Set G)⁆ ≤
      oddIn (centralizer ({t} : Set G)) := by
    rw [commutator_le]
    intro h hh y hy
    obtain ⟨y', hy', rfl⟩ := (mem_inf.mp hy).1
    set h' : ↥(centralizer ({t} : Set G)) := ⟨h, hHt hh⟩ with hh'
    have hconj : h' * y' * h'⁻¹ ∈ pPrimeCore 2 ↥(centralizer ({t} : Set G)) :=
      (inferInstance : (pPrimeCore 2 ↥(centralizer ({t} : Set G))).Normal).conj_mem y' hy' h'
    exact ⟨_, mul_mem hconj (inv_mem hy'), by simp [commutatorElement_def, hh']⟩
  have hbot := inf_oddIn_eq_bot_of_wGroup_eq_bot ht hv htv hne htB hvB hW
  rw [eq_bot_iff, ← hbot]
  exact le_inf (le_inf h3 h1) h2

end

end CFSG.ComponentClassification.GrSLit.L34Sec5S
