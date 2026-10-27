module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cfg
public import CFSG.GH74.GLS.Stage2.Local.P34Stmt
public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Local.P34Kind
public import CFSG.GH74.GLS.C3.Layer1.Thm1Layer
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.LieType.SteinbergBRSemidirectSL2
public import CFSG.LocalAnalysis.ComponentClassification.Sp4RecTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint


theorem odd_card_of_forall_odd {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y)
    (h : ∀ y ∈ N, Odd (orderOf y)) : Odd (Nat.card ↥N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have h2 : 2 ∣ Nat.card ↥N := by
    rcases Nat.even_or_odd (Nat.card ↥N) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 h2
  have hg' : orderOf (g : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hg
  have := h (g : Y) g.2
  rw [hg'] at this
  exact absurd this (by decide)

theorem pPrimeCore_eq_ker {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) : pPrimeCore 2 Y' = ρ.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_le : ρ.ker ≤ pPrimeCore 2 Y' :=
    GroupTheory.le_pPrimeCore_of_normal (MonoidHom.normal_ker ρ)
      (Nat.coprime_two_left.2 (odd_card_of_forall_odd ρ.ker hodd))
  have hO_le : pPrimeCore 2 Y' ≤ ρ.ker := by
    have hN : ((pPrimeCore 2 Y').map ρ).Normal :=
      (inferInstance : (pPrimeCore 2 Y').Normal).map ρ hρ
    have hcop : Nat.Coprime 2 (Nat.card ↥((pPrimeCore 2 Y').map ρ)) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd (pPrimeCore 2 Y') ρ)
        pPrimeCore_coprime_card
    have h1 := GroupTheory.le_pPrimeCore_of_normal hN hcop
    rw [hY] at h1
    intro x hx
    have := h1 (Subgroup.mem_map_of_mem ρ hx)
    rw [Subgroup.mem_bot] at this
    exact this
  exact le_antisymm hO_le hker_le

@[expose] noncomputable def quotEquivOfHom {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) : (Y' ⧸ pPrimeCore 2 Y') ≃* Y :=
  (QuotientGroup.quotientMulEquivOfEq (pPrimeCore_eq_ker ρ hρ hodd hY)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)

theorem quotEquivOfHom_mk {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) (y : Y') :
    quotEquivOfHom ρ hρ hodd hY (QuotientGroup.mk' (pPrimeCore 2 Y') y) = ρ y := rfl

theorem exists_pComponent_lift {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hρ : Function.Surjective ρ) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y))
    (hY : pPrimeCore 2 Y = ⊥) {Kh : Subgroup Y} (hKh : IsComponent Kh) :
    ∃ L : Subgroup Y', IsPComponent 2 L ∧ L.map ρ = Kh := by
  let e := quotEquivOfHom ρ hρ hodd hY
  have hcm : Kh.comap e.toMonoidHom = Kh.map e.symm.toMonoidHom := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hmap : ↥(Kh.comap e.toMonoidHom) ≃* ↥Kh :=
    (MulEquiv.subgroupCongr hcm).trans (e.symm.subgroupMap Kh).symm
  have hKq : IsComponent (Kh.comap e.toMonoidHom) :=
    ⟨C3.Layer1.Thm1.isQuasisimple_of_mulEquiv' hmap.symm hKh.1,
      isSubnormal_comap e.toMonoidHom hKh.2⟩
  obtain ⟨L, hL, hLmap⟩ := C3.Layer1.Thm1.exists_pComponent_of_quotient_component hKq
  refine ⟨L, hL, ?_⟩
  have h1 : L.map ρ = (L.map (QuotientGroup.mk' (pPrimeCore 2 Y'))).map e.toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  rw [h1, hLmap, Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective, top_inf_eq]

theorem exists_perfect_lift {X Y : Type} [Group X] [Finite X] [Group Y] (f : X →* Y)
    {M : Subgroup Y} (hM : ⁅M, M⁆ = M) (hle : M ≤ f.range) :
    ∃ P : Subgroup X, P.map f = M ∧ ⁅P, P⁆ = P := by
  let S : Set (Subgroup X) := {P | P.map f = M}
  have hS : S.Nonempty :=
    ⟨M.comap f, show (M.comap f).map f = M by rw [Subgroup.map_comap_eq]; exact inf_eq_right.2 hle⟩
  obtain ⟨P, hPS, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X)) S hS
  refine ⟨P, hPS, ?_⟩
  have h1 : (⁅P, P⁆).map f = M := by rw [Subgroup.map_commutator, hPS, hM]
  have hle' : ⁅P, P⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  by_contra hne
  exact hmin _ h1 (lt_of_le_of_ne hle' hne)

theorem perfect_le_J {G : Type} [Group G] [Finite G] {H : Subgroup G} (hP : PerfInJ H)
    {M : Subgroup (HBar H)} (hM : ⁅M, M⁆ = M) : M ≤ generalizedFitting (HBar H) := by
  obtain ⟨P, hPM, hPP⟩ := exists_perfect_lift (mkH H) hM
    (by rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
  have hP' : ⁅P.map H.subtype, P.map H.subtype⁆ = P.map H.subtype := by
    rw [← Subgroup.map_commutator, hPP]
  have hperf : Group.IsPerfect ↥(P.map H.subtype) := Subgroup.isPerfect_iff.mpr hP'
  have h := hP (P.map H.subtype) (by rintro _ ⟨a, -, rfl⟩; exact a.2) hperf
  have hbar : barIn H (P.map H.subtype) = M := by
    have hsub : (P.map H.subtype).subgroupOf H = P :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective P
    unfold barIn
    rw [hsub]
    exact hPM
  rwa [hbar] at h


section Pair

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem card_center_of_hasSL2Model {K : Type} [Group K] {q : ℕ} (hq : Odd q)
    (hK : HasSL2Model K (fun r => r = q)) : Nat.card ↥(center K) = 2 := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model hK
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  have hchar : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  exact CFSG.LieType.SteinbergBR.card_center_SL2_eq_two hchar

theorem zbarC_mem_inf (hp : Stage1Pair G z S q L₁ L₂) :
    toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ := by
  have hc := toBar_z_mem_center z
  have hF : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) := by
    refine CFSG.centralizer_generalizedFitting_le (CentralizerBar z) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f _
    exact Subgroup.mem_center_iff.mp hc f
  rw [hp.fitting, ← hp.prod.1] at hF
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute' hp.prod.2.1 hF
  have hcen := Subgroup.mem_center_iff.mp hc
  have hacen : ∀ c ∈ L₁, a * c = c * a := by
    intro c hc1
    have h1 := hcen c
    rw [hab] at h1
    have h2 : b * c = c * b := (hp.prod.2.1 c hc1 b hb).symm
    have : a * c * b = c * a * b := by
      calc a * c * b = a * (c * b) := by rw [mul_assoc]
        _ = a * (b * c) := by rw [h2]
        _ = a * b * c := by rw [mul_assoc]
        _ = c * (a * b) := h1.symm
        _ = c * a * b := by rw [mul_assoc]
    exact mul_right_cancel this
  have hbcen : ∀ d ∈ L₂, b * d = d * b := by
    intro d hd
    have h1 := hcen d
    rw [hab] at h1
    have h2 : a * d = d * a := hp.prod.2.1 a ha d hd
    have : a * (b * d) = a * (d * b) := by
      calc a * (b * d) = a * b * d := by rw [mul_assoc]
        _ = d * (a * b) := h1.symm
        _ = d * a * b := by rw [mul_assoc]
        _ = a * d * b := by rw [h2]
        _ = a * (d * b) := by rw [mul_assoc]
    exact mul_left_cancel this
  have key : ∀ {L M : Subgroup (CentralizerBar z)}, (∀ a ∈ L, ∀ b ∈ M, a * b = b * a) →
      Nat.card ↥(L ⊓ M) = 2 → HasSL2Model ↥L (fun r => r = q) → ∀ a ∈ L,
      (∀ c ∈ L, a * c = c * a) → a ∈ M := by
    intro L M hLM hW hsl a ha hac
    have hZc : Nat.card ↥((center ↥L).map L.subtype) = 2 := by
      rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact card_center_of_hasSL2Model hp.odd hsl
    have hle : L ⊓ M ≤ (center ↥L).map L.subtype := by
      intro w hw
      refine Subgroup.mem_map.2 ⟨⟨w, hw.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hLM c.1 c.2 w hw.2)
    have heq : L ⊓ M = (center ↥L).map L.subtype :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hW, hZc])
    have haZ : a ∈ (center ↥L).map L.subtype := by
      refine Subgroup.mem_map.2 ⟨⟨a, ha⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro c
      exact Subtype.ext (hac c.1 c.2).symm
    rw [← heq] at haZ
    exact haZ.2
  have haL₂ : a ∈ L₂ := key hp.prod.2.1 hp.prod.2.2 hp.sl₁ a ha hacen
  have hbL₁ : b ∈ L₁ := by
    refine key (L := L₂) (M := L₁) (fun x hx y hy => (hp.prod.2.1 y hy x hx).symm) ?_ hp.sl₂ b hb hbcen
    rw [inf_comm]
    exact hp.prod.2.2
  rw [hab]
  exact ⟨L₁.mul_mem ha hbL₁, L₂.mul_mem haL₂ hb⟩

end Pair


theorem mem_of_central_involution_of_hom {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y]
    (ρ : Y' →* Y) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y)) {A : Subgroup Y'} {x₀ : Y'}
    (hx₀ : x₀ * x₀ = 1) (hcen : ∀ y : Y', y * x₀ = x₀ * y) (hρ : ρ x₀ ∈ A.map ρ) : x₀ ∈ A := by
  obtain ⟨ℓ, hℓ, hℓx⟩ := hρ
  set k : Y' := ℓ⁻¹ * x₀ with hk
  have hkker : k ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_inv, hℓx, inv_mul_cancel]
  obtain ⟨j, hj⟩ := hodd k hkker
  have hℓk : ℓ = x₀ * k⁻¹ := by rw [hk]; group
  have hc : Commute x₀ k⁻¹ := (hcen k⁻¹).symm
  have hsq : x₀ ^ 2 = 1 := by rw [pow_two]; exact hx₀
  have hpow : ℓ ^ (orderOf k) = x₀ := by
    rw [hℓk, hc.mul_pow, inv_pow, pow_orderOf_eq_one, inv_one, mul_one, hj, pow_succ, pow_mul, hsq,
      one_pow, one_mul]
  rw [← hpow]
  exact A.pow_mem hℓ _

theorem pPrimeCore_eq_bot_of_hasSL2Model {K : Type} [Group K] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : HasSL2Model K (fun r => r = q)) : pPrimeCore 2 K = ⊥ := by
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := exists_sl2_equiv_of_hasSL2Model hK
  have hodd : Odd (Nat.card F) := hFq ▸ hq
  have h2 : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  rw [← CFSG.pPrimeCore_map_iso 2 e, CatFactsSp4.pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]

theorem hasSL2Model_quot_of_hom {Y' Y : Type} [Group Y'] [Finite Y'] [Group Y] [Finite Y]
    (ρ : Y' →* Y) (hodd : ∀ y ∈ ρ.ker, Odd (orderOf y)) {A : Subgroup Y'} {L : Subgroup Y}
    (hmap : A.map ρ = L) {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hsl : HasSL2Model ↥L (fun r => r = q)) :
    HasSL2Model (↥A ⧸ pPrimeCore 2 ↥A) (fun r => r = q) := by
  let ρ₁ : ↥A →* ↥L := (ρ.comp A.subtype).codRestrict L (fun u => by
    rw [← hmap]; exact ⟨u, u.2, rfl⟩)
  have hρ₁ : Function.Surjective ρ₁ := by
    intro y
    have hy : (y : Y) ∈ A.map ρ := by rw [hmap]; exact y.2
    obtain ⟨u, hu, huy⟩ := hy
    exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
  have hodd₁ : ∀ u ∈ ρ₁.ker, Odd (orderOf u) := by
    intro u hu
    have hu1 : ρ (u : Y') = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 hu)
      exact this
    have := hodd (u : Y') (MonoidHom.mem_ker.2 hu1)
    rwa [Subgroup.orderOf_coe] at this
  have hY₁ : pPrimeCore 2 ↥L = ⊥ := pPrimeCore_eq_bot_of_hasSL2Model hq h5 hsl
  obtain ⟨F, hF, hFin, hFq, ⟨e⟩⟩ := hsl
  exact ⟨F, hF, hFin, hFq, ⟨(quotEquivOfHom ρ₁ hρ₁ hodd₁ hY₁).trans e⟩⟩

theorem hasSL2Model_quot_of_equiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {q : ℕ} (h : HasSL2Model (A ⧸ pPrimeCore 2 A) (fun r => r = q)) :
    HasSL2Model (B ⧸ pPrimeCore 2 B) (fun r => r = q) := by
  obtain ⟨F, hF, hFin, hFq, ⟨f⟩⟩ := h
  exact ⟨F, hF, hFin, hFq,
    ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).symm.trans f⟩⟩


section Lift

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem centralizer_singleton_subgroupOf {X : Type} [Group X] {J : Subgroup X} {x : X} (hx : x ∈ J) :
    centralizer ({(⟨x, hx⟩ : ↥J)} : Set ↥J) = (centralizer ({x} : Set X)).subgroupOf J := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem lift_comp (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    {L : Subgroup (CentralizerBar z)} (hL : IsComponent L)
    (hzL : toBar z ⟨z, mem_Cen_self z⟩ ∈ L) :
    ∃ B : Subgroup (HBar H), B ≤ generalizedFitting (HBar H) ∧ B ≤ barIn H (Cen z) ∧
      mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ B ∧
      IsPComponent 2 (B.subgroupOf (barIn H (Cen z))) ∧
      (B.subgroupOf (barIn H (Cen z))).map (cenToBar H hCH) = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hxC' : x ∈ C' := by
    rw [← hcent]
    exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hρ := cenToBar_surjective H hCH
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have hY : pPrimeCore 2 (CentralizerBar z) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  obtain ⟨A, hA, hAmap⟩ := exists_pComponent_lift (cenToBar H hCH) hρ hodd hY hL
  set B : Subgroup (HBar H) := A.map C'.subtype with hB
  have hBC' : B ≤ C' := by rintro _ ⟨a, -, rfl⟩; exact a.2
  have hBA : B.subgroupOf C' = A := Subgroup.comap_map_eq_self_of_injective C'.subtype_injective A
  have hperf : ⁅B, B⁆ = B := by
    rw [hB, ← Subgroup.map_commutator,
      Subgroup.isPerfect_iff.mp (CatalogueBAlternating.pComponent_perfect hA)]
  have hBJ : B ≤ generalizedFitting (HBar H) := perfect_le_J hPerf hperf
  let x₀ : ↥C' := ⟨x, hxC'⟩
  have hρx : cenToBar H hCH x₀ = toBar z ⟨z, mem_Cen_self z⟩ :=
    cenToBar_cenMk H hCH ⟨z, mem_Cen_self z⟩
  have hx₀A : x₀ ∈ A := by
    refine mem_of_central_involution_of_hom (cenToBar H hCH) hodd (A := A) ?_ ?_ ?_
    · exact Subtype.ext (by
        have h2 : x * x = 1 := by
          have := pow_orderOf_eq_one x
          rwa [(orderOf_mk_eq_two H (show orderOf (⟨z, hzmem⟩ : ↥H) = 2 by
            rw [← Subgroup.orderOf_coe]; exact hz2)), pow_two] at this
        exact h2)
    · intro y
      have hy : (y : HBar H) ∈ centralizer ({x} : Set (HBar H)) := by
        rw [hcent]; exact y.2
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hy)
    · rw [hAmap, hρx]
      exact hzL
  have hxB : x ∈ B := ⟨x₀, hx₀A, rfl⟩
  exact ⟨B, hBJ, hBC', hxB, by rw [hBA]; exact hA, by rw [hBA]; exact hAmap⟩


theorem exists_cfg (hz2 : orderOf z = 2) {H : Subgroup G} (hCH : Cen z ≤ H) (hPerf : PerfInJ H)
    (hp : Stage1Pair G z S q L₁ L₂) :
    ∃ (hzJ : mkH H ⟨z, hCH (mem_Cen_self z)⟩ ∈ generalizedFitting (HBar H))
      (L₁' L₂' : Subgroup ↥(generalizedFitting (HBar H))),
      Ivk93Cfg (⟨mkH H ⟨z, hCH (mem_Cen_self z)⟩, hzJ⟩ : ↥(generalizedFitting (HBar H))) q L₁' L₂' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem : z ∈ H := hCH (mem_Cen_self z)
  set x : HBar H := mkH H ⟨z, hzmem⟩ with hx
  set C' : Subgroup (HBar H) := barIn H (Cen z) with hC'
  have hc₁ : IsComponent L₁ := (Set.ext_iff.1 hp.comps L₁).2 (Or.inl rfl)
  have hc₂ : IsComponent L₂ := (Set.ext_iff.1 hp.comps L₂).2 (Or.inr rfl)
  have hzbar := zbarC_mem_inf hp
  obtain ⟨B₁, hB₁J, hB₁C, hxB₁, hB₁comp, hB₁map⟩ := lift_comp hz2 hCH hPerf hc₁ hzbar.1
  obtain ⟨B₂, hB₂J, hB₂C, hxB₂, hB₂comp, hB₂map⟩ := lift_comp hz2 hCH hPerf hc₂ hzbar.2
  have hxJ : x ∈ generalizedFitting (HBar H) := hB₁J hxB₁
  refine ⟨hxJ, B₁.subgroupOf _, B₂.subgroupOf _, ?_⟩
  have hx2 : orderOf x = 2 := orderOf_mk_eq_two H (by rw [← Subgroup.orderOf_coe]; exact hz2)
  have hcent : centralizer ({x} : Set (HBar H)) = C' := centralizer_mk_eq H hz2 hzmem
  have hcJ := centralizer_singleton_subgroupOf (J := generalizedFitting (HBar H)) hxJ
  rw [hcent] at hcJ
  have hq5 : 5 ≤ q := by
    obtain ⟨m, hm⟩ := hp.odd
    have := hp.gt3
    omega
  have hodd : ∀ y ∈ (cenToBar H hCH).ker, Odd (orderOf y) := fun y hy =>
    odd_orderOf_of_cenToBar_eq_one H hCH y hy
  have comp : ∀ {B : Subgroup (HBar H)}, B ≤ generalizedFitting (HBar H) → B ≤ C' →
      IsPComponent 2 (B.subgroupOf C') →
      IsPCompIn 2 (centralizer ({(⟨x, hxJ⟩ : ↥(generalizedFitting (HBar H)))} :
        Set ↥(generalizedFitting (HBar H)))) (B.subgroupOf (generalizedFitting (HBar H))) := by
    intro B hBJ hBC h
    rw [hcJ]
    exact ⟨fun y hy => hBC hy, ComponentClassification.Sp4Rec.isPComponent_subgroupOf_restrict hBC hBJ h⟩
  have sl : ∀ {B : Subgroup (HBar H)} {L : Subgroup (CentralizerBar z)},
      B ≤ generalizedFitting (HBar H) → B ≤ C' → (B.subgroupOf C').map (cenToBar H hCH) = L →
      HasSL2Model ↥L (fun r => r = q) →
      HasSL2Model (↥(B.subgroupOf (generalizedFitting (HBar H))) ⧸
        pPrimeCore 2 ↥(B.subgroupOf (generalizedFitting (HBar H)))) (fun r => r = q) := by
    intro B L hBJ hBC hmap hsl
    exact hasSL2Model_quot_of_equiv
      ((Subgroup.subgroupOfEquivOfLe hBC).trans (Subgroup.subgroupOfEquivOfLe hBJ).symm)
      (hasSL2Model_quot_of_hom (cenToBar H hCH) hodd hmap hp.odd hq5 hsl)
  refine ⟨?_, hp.odd, hq5, ?_, comp hB₁J hB₁C hB₁comp, comp hB₂J hB₂C hB₂comp,
    Subgroup.mem_subgroupOf.2 hxB₁, Subgroup.mem_subgroupOf.2 hxB₂,
    sl hB₁J hB₁C hB₁map hp.sl₁, sl hB₂J hB₂C hB₂map hp.sl₂⟩
  · rw [← Subgroup.orderOf_coe]
    exact hx2
  · intro h
    have hB : B₁ = B₂ := by
      ext y
      constructor
      · intro hy
        have : (⟨y, hB₁J hy⟩ : ↥(generalizedFitting (HBar H))) ∈ B₁.subgroupOf _ :=
          Subgroup.mem_subgroupOf.2 hy
        rw [h] at this
        exact Subgroup.mem_subgroupOf.1 this
      · intro hy
        have : (⟨y, hB₂J hy⟩ : ↥(generalizedFitting (HBar H))) ∈ B₂.subgroupOf _ :=
          Subgroup.mem_subgroupOf.2 hy
        rw [← h] at this
        exact Subgroup.mem_subgroupOf.1 this
    apply hp.ne
    rw [← hB₁map, ← hB₂map, hB]

end Lift

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
