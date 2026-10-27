module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81R
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6a
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6c

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Q81

theorem zBar_mem_centerJoin {z : X} (hz : orderOf z = 2) {Rb : Subgroup (MBar z)}
    (hRb : IsSylowOf 2 Rb ⊤)
    (hZ : Rb ⊓ centralizer (Rb : Set (MBar z)) =
      zpowers (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z))
    {A : Subgroup (MBar z)} (hA : IsComponent A) :
    (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) ∈
      ⨆ g : MBar z, centerIn (conjSub A g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hOA := pPrimeCore_eq_bot_of_isSubnormal hO hA.2
  have hB := join_normal A
  have hBN : (⊤ : Subgroup (MBar z)) ≤ normalizer ((⨆ g : MBar z, conjSub A g : Subgroup
      (MBar z)) : Set (MBar z)) := fun x _ => by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hB.conj_mem h hh x, fun hh => ?_⟩
    have h2 := hB.conj_mem _ hh x⁻¹
    rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at h2
  have hRB := hRb.inf_of_le_normalizer le_top hBN
  have hA1 : conjSub A 1 = A := by
    ext x
    rw [mem_conjSub]
    simp
  have hAB : A ≤ ⨆ g : MBar z, conjSub A g :=
    hA1.symm.le.trans (le_iSup (fun g : MBar z => conjSub A g) 1)
  have hnt := LocalCores.isQuasisimple_nontrivial hA.1
  have h2B : 2 ∣ Nat.card ↥(⨆ g : MBar z, conjSub A g) :=
    (two_dvd_card_of_pPrimeCore_eq_bot hOA).trans (Subgroup.card_dvd_of_le hAB)
  have hRB1 : Rb ⊓ (⨆ g : MBar z, conjSub A g) ≠ ⊥ := by
    intro hbot
    have h1 := (isSylowOf_iff.mp hRB).2.2
    rw [hbot, relIndex_bot_left] at h1
    exact h1 h2B
  have hzRB := mem_of_normalized hRb.isPGroup (orderOf_mk_self hz) hZ inf_le_left
    (le_normalizer_inf hB) hRB1
  exact mem_centerJoin_of_central hA (mem_inf.mp hzRB).2
    fun y _ => (mem_center_iff.mp (mk_center z) y).symm

end Q81

namespace Setting46e

variable {p f : ℕ} {S : Subgroup X} {w z : X} {V : Subgroup X} {i j : ℕ}

theorem not_isOfType_component
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hCI : GSLit.ClassicalInvolutionInput) (h219 : Harris82Lemma219Input)
    (hP2 : Harris81Lemma33Simple) (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hT2 : Harris82Theorem2SLTwo)
    (hs : Setting46e t L p f S w z V i j) {R : Subgroup X} (hR : IsSylowOf 2 R ⊤)
    (hRz : R ≤ centralizer ({z} : Set X)) (hZR : R ⊓ centralizer (R : Set X) = zpowers z)
    (hTR : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ R) {A : Subgroup (MBar z)}
    (hA : IsComponent A) : ¬ IsOfType (HarrisF 3) ↥A := by
  intro hAt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 (MBar z) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hOA := pPrimeCore_eq_bot_of_isSubnormal hO hA.2
  have hz : orderOf z = 2 := hs.setup.z_order
  have ht : orderOf t = 2 := hs.standing.config.orderOf_eq
  have htz : t ∈ centralizer ({z} : Set X) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hs.sylow.le hs.setup.z_mem.1)).symm
  have hC := hs.lemma44a_z.1
  have hRp : IsPGroup 2 R := hR.isPGroup
  have htR : t ∈ R := hTR (mem_sup_left (mem_sup_left (mem_zpowers t)))
  have hzR : z ∈ R := by
    have h1 : z ∈ R ⊓ centralizer (R : Set X) := by rw [hZR]; exact mem_zpowers z
    exact (mem_inf.mp h1).1
  have hzZB := Q81.zBar_mem_centerJoin hz (Q81.isSylowOf_barR hR hRz)
    (Q81.center_barR hRp hRz hZR) hA
  have hZ1 : center ↥A ≠ ⊥ := by
    intro hbot
    have hle : (⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) ≤ ⊥ := by
      refine iSup_le fun g x hx => ?_
      rw [Q81.centerIn_conjSub, Q81.mem_conjSub, Q81.centerIn, hbot, Subgroup.map_bot,
        mem_bot] at hx
      rw [mem_bot]
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [hx]; group
    have h1 := hle hzZB
    rw [mem_bot] at h1
    have h2 := Q81.orderOf_mk_self hz
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  obtain ⟨m, -, hm, -, hZ2⟩ := Q81.component_psl_two h219 hP2 hGO htz ht hC hA hAt hZ1
  have hzA := Q81.zBar_not_mem_component hnonab hcat hCI h219 hP2 hGO hGC hz htz ht hC hA hAt
  have hZA : Nat.card ↥(center ↥A) = 2 := by
    have h1 : 1 < Nat.card ↥(center ↥A) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ1
    omega
  obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a₀ ∈ Q81.centerIn A, a₀ ≠ 1 := by
    obtain ⟨⟨a', ha'⟩, ha'1⟩ := ne_bot_iff_exists_ne_one.mp hZ1
    exact ⟨a', ⟨a', ha', rfl⟩, fun h => ha'1 (Subtype.ext (Subtype.ext h))⟩
  have hZBe := Q81.isElemTwo_centerJoin hA hZ2
  have hZBn := Q81.centerJoin_normal A
  have hZBp : IsPGroup 2 ↥(⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq]; exact hZBe.2 _ g.2)⟩
  have hZBR : (⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) ≤
      (R.subgroupOf (centralizer {z})).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set X)))) := by
    have hRb := Q81.isSylowOf_barR hR hRz
    have hsup := hRb.isPGroup.to_sup_of_normal_right hZBp
    exact le_sup_right.trans (hRb.eq_of_le le_sup_left le_top hsup).le
  set E := Q81.liftIn R z (⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) with hEdef
  have hER : E ≤ R := Q81.liftIn_le
  have hEn : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ ∈ E := fun r hr e he =>
    Q81.conj_mem_liftIn hRz hZBn hr he
  have hEmul : ∀ e ∈ E, e * e = 1 := fun e he =>
    Q81.mul_self_eq_one_of_mem_liftIn hRp hRz hZBe.2 he
  have hE2 : ∀ e ∈ E, e ^ 2 = 1 := fun e he => by rw [sq]; exact hEmul e he
  have hZBt : (⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) ≤
      centralizer {(QuotientGroup.mk ⟨t, hRz htR⟩ : MBar z)} :=
    Q81.mem_centralizer_centerJoin hZ2 fun g =>
      (Q81.component_tBar h219 htz ht hC (Q81.isComponent_conj hA g)).1
  have hEt : E ≤ centralizer ({t} : Set X) := fun e he =>
    mem_centralizer_singleton_iff.mpr (Q81.comm_of_mem_liftIn hRp hRz htR hZBt he)
  have hEX := hs.le_X_of_normal_R hRp hRz hTR hER hEt hEn hE2
  have htE : t ∉ E := by
    intro htE'
    obtain ⟨_, -, htZB⟩ := Q81.mem_liftIn.mp htE'
    apply Q81.component_not_le_centralizer h219 htz ht hC hA
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (Q81.centerJoin_le_centralizer hA htZB) x hx)
  have hE4 : Nat.card E ≤ 4 :=
    Q81.card_le_four hEX hs.setup.card_X (subset_closure (Set.mem_insert t _)) htE
  obtain ⟨g, b, hbg, hbA⟩ : ∃ g : MBar z, ∃ b ∈ Q81.centerIn (Q81.conjSub A g),
      b ∉ Q81.centerIn A := by
    by_contra hne
    have hle : (⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g)) ≤ Q81.centerIn A :=
      iSup_le fun g b hb => by
        by_contra hb'
        exact hne ⟨g, b, hb, hb'⟩
    exact hzA (Q81.mem_centerIn.mp (hle hzZB)).1
  have hA1 : Q81.conjSub A 1 = A := by
    ext x
    rw [Q81.mem_conjSub]
    simp
  have ha₀ZB : a₀ ∈ ⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g) := by
    have h2 := le_iSup (fun g : MBar z => Q81.centerIn (Q81.conjSub A g)) 1
    rw [hA1] at h2
    exact h2 ha₀
  have hbZB : b ∈ ⨆ g : MBar z, Q81.centerIn (Q81.conjSub A g) :=
    le_iSup (fun g : MBar z => Q81.centerIn (Q81.conjSub A g)) g hbg
  obtain ⟨a₁, ha₁E, ha₁z, rfl⟩ := Q81.exists_mem_liftIn hZBR ha₀ZB
  obtain ⟨b₁, hb₁E, hb₁z, rfl⟩ := Q81.exists_mem_liftIn hZBR hbZB
  have hzE : z ∈ E := Q81.mem_liftIn.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hzR, hzZB⟩
  have ha₁1 : a₁ ≠ 1 := by
    intro h
    apply ha₀1
    rw [show (⟨a₁, ha₁z⟩ : ↥(centralizer ({z} : Set X))) = 1 from Subtype.ext h,
      QuotientGroup.mk_one]
  have ha₁2 : orderOf a₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hEmul a₁ ha₁E) ha₁1
  have ha₁ne : a₁ ≠ z := by
    intro h
    apply hzA
    have h1 := (Q81.mem_centerIn.mp ha₀).1
    rwa [show (⟨a₁, ha₁z⟩ : ↥(centralizer ({z} : Set X))) =
      ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ from Subtype.ext h] at h1
  have hza₁ : z * a₁ = a₁ * z := (mem_centralizer_singleton_iff.mp ha₁z).symm
  have hW := Lemma47.fourGroup_closure_pair hz ha₁2 ha₁ne hza₁
  have hVE : closure {z, a₁} ≤ E := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact hzE
    · exact ha₁E
  have hVeq : closure {z, a₁} = E :=
    Subgroup.eq_of_le_of_card_ge hVE (by rw [hW.2]; exact hE4)
  have hb₁V : b₁ ∈ closure {z, a₁} := by rw [hVeq]; exact hb₁E
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hb₁eq : b₁ = z * a₁ := by
    rcases Q81.mem_closure_pair_cases hzz (hEmul a₁ ha₁E) hza₁ hb₁V with h | h | h | h
    · exfalso
      apply hbA
      rw [show (⟨b₁, hb₁z⟩ : ↥(centralizer ({z} : Set X))) = 1 from Subtype.ext h,
        QuotientGroup.mk_one]
      exact one_mem _
    · exfalso
      apply hzA
      have h1 := (Q81.mem_centerIn.mp hbg).1
      rw [show (⟨b₁, hb₁z⟩ : ↥(centralizer ({z} : Set X))) =
        ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ from Subtype.ext h, Q81.mem_conjSub] at h1
      rwa [show g⁻¹ * (QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ : MBar z) *
          g = QuotientGroup.mk ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ by
        rw [mem_center_iff.mp (Q81.mk_center z) g⁻¹, mul_assoc, inv_mul_cancel, mul_one]] at h1
    · exfalso
      apply hbA
      rw [show (⟨b₁, hb₁z⟩ : ↥(centralizer ({z} : Set X))) = ⟨a₁, ha₁z⟩ from Subtype.ext h]
      exact ha₀
    · exact h
  have hb₁1 : b₁ ≠ 1 := by
    intro h
    apply hbA
    rw [show (⟨b₁, hb₁z⟩ : ↥(centralizer ({z} : Set X))) = 1 from Subtype.ext h,
      QuotientGroup.mk_one]
    exact one_mem _
  have hb₁2 : orderOf b₁ = 2 := orderOf_eq_prime (by rw [sq]; exact hEmul b₁ hb₁E) hb₁1
  have hAp : IsPComponent 2 A :=
    (isTwoComponent_iff_isPComponent A).mp ((isTwoComponent_iff_isComponent hO A).mpr hA)
  have hAle : A ≤ centralizer {(QuotientGroup.mk ⟨a₁, ha₁z⟩ : MBar z)} := fun x hx =>
    mem_centralizer_singleton_iff.mpr ((Q81.mem_centerIn.mp ha₀).2 x hx).symm
  obtain ⟨J₁, hJ₁le, hJ₁, ha₁J₁, -, g₁, hg₁, hg₁k⟩ := Lemma47.exists_lift_two_component ha₁z
    ha₁2 hAle (Q81.isPComponent_subgroupOf hAle hAp) (Q81.mem_centerIn.mp ha₀).1
  have hA'c := Q81.isComponent_conj hA g
  have hA'p : IsPComponent 2 (Q81.conjSub A g) :=
    (isTwoComponent_iff_isPComponent _).mp ((isTwoComponent_iff_isComponent hO _).mpr hA'c)
  have hA'le : Q81.conjSub A g ≤ centralizer {(QuotientGroup.mk ⟨b₁, hb₁z⟩ : MBar z)} :=
    fun x hx => mem_centralizer_singleton_iff.mpr ((Q81.mem_centerIn.mp hbg).2 x hx).symm
  obtain ⟨J₂, hJ₂le, hJ₂, hb₁J₂, -, g₂, hg₂, hg₂k⟩ := Lemma47.exists_lift_two_component hb₁z
    hb₁2 hA'le (Q81.isPComponent_subgroupOf hA'le hA'p) (Q81.mem_centerIn.mp hbg).1
  have hCW := Lemma47.centralizer_closure_pair z a₁
  have hL₁ : IsTwoComponentIn J₁ (centralizer ((closure {z, a₁} : Subgroup X) : Set X)) := by
    rw [hCW]
    exact (isTwoComponentIn_iff hJ₁le).mpr hJ₁
  have hCC := Q81.centralizer_inf_mul z a₁
  rw [hb₁eq, hCC] at hJ₂le hJ₂
  have hL₂ : IsTwoComponentIn J₂ (centralizer ((closure {z, a₁} : Subgroup X) : Set X)) := by
    rw [hCW]
    exact (isTwoComponentIn_iff hJ₂le).mpr hJ₂
  have hM₁ : IsMTypeSchur 3 ↥J₁ := isMTypeSchur_of_surjective hGO Nat.prime_three
    (by norm_num) g₁ hg₁ hg₁k hL₁.2.2.1 hA.1 hOA hZA hm
  have hOA' := pPrimeCore_eq_bot_of_isSubnormal hO hA'c.2
  have hZA' : Nat.card ↥(center ↥(Q81.conjSub A g)) = 2 := by
    have h1 : Nat.card ↥(Q81.centerIn (Q81.conjSub A g)) = Nat.card ↥(Q81.centerIn A) := by
      rw [Q81.centerIn_conjSub, card_map_of_injective (MulAut.conj g).injective]
    rw [Q81.centerIn, Q81.centerIn, card_map_of_injective (subtype_injective _),
      card_map_of_injective (subtype_injective _)] at h1
    rw [h1, hZA]
  let eA : ↥A ≃* ↥(Q81.conjSub A g) :=
    A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hmA' : Blueprint.LieModel (↥(Q81.conjSub A g) ⧸ center ↥(Q81.conjSub A g)) .PSL 2 3 m :=
    GSThmB.OddQuot.lieModel_of_equiv
      (QuotientGroup.congr (center ↥A) (center ↥(Q81.conjSub A g)) eA
        (Q81.map_center_equiv eA)) hm
  have hM₂ : IsMTypeSchur 3 ↥J₂ := isMTypeSchur_of_surjective hGO Nat.prime_three
    (by norm_num) g₂ hg₂ hg₂k hL₂.2.2.1 hA'c.1 hOA' hZA' hmA'
  have ha₁W : a₁ ∈ (closure {z, a₁} : Subgroup X) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hb₁W : b₁ ∈ (closure {z, a₁} : Subgroup X) := by
    rw [hb₁eq]
    exact mul_mem (subset_closure (Set.mem_insert _ _)) ha₁W
  have hne : a₁ ≠ b₁ := by
    intro h
    apply hbA
    rw [show (⟨b₁, hb₁z⟩ : ↥(centralizer ({z} : Set X))) = ⟨a₁, ha₁z⟩ from Subtype.ext h.symm]
    exact ha₀
  obtain ⟨eZ₁⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective g₁ hg₁ hg₁k
  have hmJ₁ : Blueprint.LieModel (↥J₁ ⧸ Open.fusionZStar ↥J₁) .PSL 2 3 m :=
    GSThmB.OddQuot.lieModel_of_equiv (eZ₁.trans (QuotientGroup.quotientMulEquivOfEq
      (fusionZStar_eq_center_of_pPrimeCore_eq_bot hOA))).symm hm
  exact hcat (hT2 X hnonab hK _ hW.1 hW.2 a₁ ha₁W b₁ hb₁W ha₁1 hb₁1 hne J₁ J₂ hL₁ hL₂ ha₁J₁
    hb₁J₂ 3 Nat.prime_three (by norm_num) hM₁ hM₂ ⟨m, hmJ₁⟩)

end Setting46e

end CFSG.ComponentClassification.HarrisLit
