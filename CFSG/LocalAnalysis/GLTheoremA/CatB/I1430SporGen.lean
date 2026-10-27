module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ClsRed
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cHN

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp)

@[expose] def A6Free {Q : Type} [Group Q] (k : Q) : Prop :=
  ∀ I : Subgroup Q, GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) I →
    Nat.card (PSimple 3 I) = 360 → Nat.card (Subgroup.center (PQuot 3 I)) = 1 → False

@[expose] def A6Row (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      catalogIs (PSimple 3 J) isA6 → Nat.card (Subgroup.center (PQuot 3 J)) = 1 → False

theorem i1430SporS_of_rows (hB : LieOrderBridge)
    (h : ∀ s : TauCeti.SporadicName, s ≠ .J3 → s ≠ .ONan → s ≠ .Suz → A6Row s) :
    ClsRed.I1430SporS := by
  intro S _ _ s e β hβ hβ1 J hJ hT hZ
  by_contra hs
  push Not at hs
  exact h s hs.1 hs.2.1 hs.2.2 S e β hβ hβ1 J hJ hT hZ

section Card

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B]

theorem card_pQuot_congr (e : A ≃* B) :
    Nat.card (A ⧸ GLAPPrimeCore 3 A) = Nat.card (B ⧸ GLAPPrimeCore 3 B) :=
  Nat.dvd_antisymm
    (Subgroup.card_dvd_of_surjective
      (pQuotMapOfSurjective_surjective Nat.prime_three e.symm.toMonoidHom e.symm.surjective))
    (Subgroup.card_dvd_of_surjective
      (pQuotMapOfSurjective_surjective Nat.prime_three e.toMonoidHom e.surjective))

end Card

variable {Q : Type} [Group Q] [Finite Q]

theorem card_center_pQuot (I : Subgroup Q) :
    Nat.card (PQuot 3 I) = Nat.card (PSimple 3 I) * Nat.card (Subgroup.center (PQuot 3 I)) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup _

theorem a6Free_of_mulEquiv {Q' : Type} [Group Q'] [Finite Q'] (σ : Q ≃* Q') {k : Q} (h : A6Free k) :
    A6Free (σ k) := by
  intro I hI hc hZ
  have hI' := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three σ.symm hI
  rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at hI'
  let eI := I.equivMapOfInjective σ.symm.toMonoidHom σ.symm.injective
  have e := CFSG.HardMathSupport.Dickson.I271.pSimpleEquiv 3 eI
  have hc' : Nat.card (PSimple 3 (I.map σ.symm.toMonoidHom)) = 360 :=
    (Nat.card_congr e.toEquiv).symm.trans hc
  refine h _ hI' hc' ?_
  have h1 := card_center_pQuot I
  have h2 := card_center_pQuot (I.map σ.symm.toMonoidHom)
  have h3 : Nat.card (PQuot 3 I) = Nat.card (PQuot 3 (I.map σ.symm.toMonoidHom)) :=
    card_pQuot_congr eI
  rw [hZ, mul_one, hc] at h1
  rw [← h3, h1, hc'] at h2
  have hpos : 0 < Nat.card (Subgroup.center (PQuot 3 (I.map σ.symm.toMonoidHom))) := Nat.card_pos
  omega

theorem a6Free_of_mulEquiv_apply {Q' : Type} [Group Q'] [Finite Q'] (σ : Q ≃* Q') {k : Q}
    (h : A6Free (σ k)) : A6Free k := by
  have h' := a6Free_of_mulEquiv σ.symm h
  rwa [MulEquiv.symm_apply_apply] at h'

theorem a6Free_conj {c : Q} (h : A6Free c) (g : Q) : A6Free (g * c * g⁻¹) :=
  a6Free_of_mulEquiv (MulAut.conj g) h

theorem a6Free_of_noCardComp {k : Q} (h : NoCardComp 360 k) : A6Free k :=
  fun I hI hc _ => h I hI hc

theorem not_mem_of_center {k : Q} (hk : orderOf k = 3) {I : Subgroup Q}
    (hI : GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) I)
    (hZ : Nat.card (Subgroup.center (PQuot 3 I)) = 1) : k ∉ I := by
  intro hkI
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set k' : ↥I := ⟨k, hkI⟩
  have hcen : (QuotientGroup.mk k' : PQuot 3 I) ∈ Subgroup.center (PQuot 3 I) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hw := Subgroup.mem_centralizer_singleton_iff.1 (hI.1 w.2)
    simp only [Subgroup.coe_mul, k']
    first
      | exact hw
      | exact hw.symm
  have hZbot : Subgroup.center (PQuot 3 I) = ⊥ := Subgroup.eq_bot_of_card_eq _ hZ
  rw [hZbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥I)) := CFSG.pPrimeCore_coprime_card
  have hdvd : orderOf (⟨k', hcen⟩ : GLAPPrimeCore 3 ↥I) ∣ Nat.card (GLAPPrimeCore 3 ↥I) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hk] at hdvd
  exact absurd (hcop.coprime_dvd_right hdvd) (by norm_num)

@[expose] noncomputable def prodHom (k : Q) (I : Subgroup Q)
    (hI : I ≤ Subgroup.centralizer ({k} : Set Q)) : ↥(Subgroup.zpowers k) × ↥I →* Q :=
  MonoidHom.noncommCoprod (Subgroup.zpowers k).subtype I.subtype (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hbk := Subgroup.mem_centralizer_singleton_iff.1 (hI hb)
    exact ((Commute.zpow_left (by first | exact hbk.symm | exact hbk) m)))

theorem prodHom_apply (k : Q) (I : Subgroup Q) (hI : I ≤ Subgroup.centralizer ({k} : Set Q))
    (u : ↥(Subgroup.zpowers k) × ↥I) : prodHom k I hI u = (u.1 : Q) * (u.2 : Q) := rfl

theorem prodHom_injective {k : Q} (hk : orderOf k = 3) {I : Subgroup Q}
    (hI : I ≤ Subgroup.centralizer ({k} : Set Q)) (hkI : k ∉ I) :
    Function.Injective (prodHom k I hI) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h
  rw [prodHom_apply] at h
  simp only at h
  have hab : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
  have haI : a ∈ I := hab ▸ I.inv_mem hb
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have ha1 : k ^ m = 1 := by
    by_contra hne
    have hord : orderOf (k ^ m) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hd : orderOf (k ^ m) ∣ 3 := by
        have h3 : k ^ 3 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hne
      · exact h1
    have hmem : k ∈ Subgroup.zpowers (k ^ m) := by
      have hle : Subgroup.zpowers (k ^ m) ≤ Subgroup.zpowers k :=
        Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers k m)
      have hc : Nat.card (Subgroup.zpowers (k ^ m)) = Nat.card (Subgroup.zpowers k) := by
        rw [Nat.card_zpowers, Nat.card_zpowers, hord, hk]
      have := Subgroup.eq_of_le_of_card_ge hle hc.ge
      rw [this]
      exact Subgroup.mem_zpowers k
    exact hkI ((Subgroup.zpowers_le.2 haI) hmem)
  have hb1 : b = 1 := by
    rw [ha1, one_mul] at h
    exact h
  ext <;> simp [ha1, hb1]

theorem dvd_card_of_component {k : Q} (hk : orderOf k = 3) {I : Subgroup Q}
    (hI : GLAPComponent 3 (Subgroup.centralizer ({k} : Set Q)) I)
    (hc : Nat.card (PSimple 3 I) = 360) (hZ : Nat.card (Subgroup.center (PQuot 3 I)) = 1) :
    1080 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q)) := by
  have hkI := not_mem_of_center hk hI hZ
  have hIC : I ≤ Subgroup.centralizer ({k} : Set Q) := hI.1
  have hinj := prodHom_injective hk hIC hkI
  have hrange : (prodHom k I hIC).range ≤ Subgroup.centralizer ({k} : Set Q) := by
    rintro _ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, rfl⟩
    rw [prodHom_apply]
    refine Subgroup.mul_mem _ ?_ (hIC hb)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact Subgroup.zpow_mem _ (Subgroup.mem_centralizer_singleton_iff.2 rfl) m
  have hcard : Nat.card (prodHom k I hIC).range = 3 * Nat.card I := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers, hk]
  have hPQ : Nat.card (PQuot 3 I) = 360 := by
    rw [card_center_pQuot, hc, hZ]
  have h360 : 360 ∣ Nat.card I := by
    rw [← hPQ]
    exact Subgroup.card_quotient_dvd_card _
  have h1 := Subgroup.card_dvd_of_le hrange
  rw [hcard] at h1
  exact (Nat.mul_dvd_mul_left 3 h360).trans h1

theorem a6Free_of_not_dvd {k : Q} (hk : orderOf k = 3)
    (h : ¬ 1080 ∣ Nat.card (Subgroup.centralizer ({k} : Set Q))) : A6Free k :=
  fun _ hI hc hZ => h (dvd_card_of_component hk hI hc hZ)

theorem a6Row_of_model (hB : LieOrderBridge) {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (h : ∀ k : Q, orderOf k = 3 → A6Free k) : A6Row s := by
  intro S _ _ ⟨e⟩ β hβ hβ1 J hJ hT hZ
  let φ : S ≃* Q := e.trans b.symm
  haveI : IsSimpleGroup S := (MulEquiv.isSimpleGroup_congr φ).2 inferInstance
  have hncS : ∃ a c : S, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    refine ⟨φ.symm a, φ.symm c, fun h' => hac ?_⟩
    have := congrArg φ h'
    simpa using this
  have hcen : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h' | h'
    · exact h'
    · obtain ⟨a, c, hac⟩ := hncS
      exact absurd ((Subgroup.mem_center_iff.1 (h' ▸ Subgroup.mem_top c)) a) hac
  have hout := hOut S inferInstance hncS s ⟨e⟩
  obtain ⟨x, rfl, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow Nat.prime_three (by norm_num)
      hcen hout β hβ
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hβ1 (map_one MulAut.conj)
  have hxo : orderOf x = 3 := orderOf_eq_prime hxp hx1
  have heq : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj x) =
      Subgroup.centralizer ({x} : Set S) := by
    ext g
    rw [CFSG.LocalAnalysis.GLTheoremA.AltDown.mem_fixSubgroup_conj,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      first
        | exact h.eq
        | exact h.eq.symm
    · intro h
      first
        | exact h
        | exact h.symm
  rw [heq] at hJ
  have hk : orderOf (φ x) = 3 := by rw [MulEquiv.orderOf_eq, hxo]
  have := a6Free_of_mulEquiv φ.symm (h _ hk)
  rw [MulEquiv.symm_apply_apply] at this
  exact this J hJ (ClsRed.card_a6 hB hT) hZ

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.A6Spor

end
