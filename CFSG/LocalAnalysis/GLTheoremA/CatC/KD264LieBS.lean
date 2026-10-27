module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCoreS
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.GroupTheory.PLayer.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.FixSubgroupInf
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQResidueJZeroA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.GroupActions

variable {p : ℕ} {S : Type} [Group S] [Finite S]
variable {A : Subgroup (MulAut S)} {β : MulAut S} {J : Subgroup S}

private theorem isGood_zpowers_sup_zpowers (a : MulAut S) :
    IsGood p (Subgroup.zpowers β ⊔ Subgroup.zpowers a) ↔
      GLAPLayer p (fixSubgroup β ⊓ fixSubgroup a) ≠ ⊥ := by
  unfold IsGood
  rw [iInf_fixSubgroup_zpowers_sup]

private theorem isGood_sup_zpowers_of_glaPLayer_inf_ne_bot
    (hp : p.Prime) (hJ : GLAPComponent p (fixSubgroup β) J) {a : MulAut S}
    (h : GLAPLayer p (J ⊓ fixSubgroup a) ≠ ⊥) :
    IsGood p (Subgroup.zpowers β ⊔ Subgroup.zpowers a) := by
  have hsub : IsSubnormal (J ⊓ fixSubgroup a) (fixSubgroup β ⊓ fixSubgroup a) :=
    hJ.2.1.inf _
  have hle := CFSG.LocalAnalysis.GLTheoremA.glaPLayer_le_of_isSubnormal hp hsub
  have hne : GLAPLayer p (fixSubgroup β ⊓ fixSubgroup a) ≠ ⊥ :=
    fun hbot => h (le_bot_iff.1 (hbot ▸ hle))
  exact (isGood_zpowers_sup_zpowers (p := p) a).2 hne

private theorem kd264BS_stab (hp : p.Prime) (hA : IsElemAbelian p A)
    (hnoGood : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hβA : β ∈ A) (hβ1 : β ≠ 1) (hJ : GLAPComponent p (fixSubgroup β) J) :
    A ≤ CFSG.GroupActions.subgroupStabAut J := by
  intro a ha
  by_contra hnot
  have hJa : J.map a.toMonoidHom ≠ J := hnot
  have hβp : β ^ p = 1 := hA.2 β hβA
  have hap : a ^ p = 1 := hA.2 a ha
  haveI : IsMulCommutative ↥A := hA.1
  have hcomm : a * β = β * a := by
    have hc := mul_comm' (⟨a, ha⟩ : A) (⟨β, hβA⟩ : A)
    exact congrArg Subtype.val hc
  have hX : (fixSubgroup β).map a.toMonoidHom = fixSubgroup β :=
    map_fixSubgroup_eq_of_commute a β hcomm
  have hβ_stab : β ∈ CFSG.GroupActions.subgroupStabAut J := by
    show J.map β.toMonoidHom = J
    exact map_eq_self_of_fix (fun x hx => hJ.1 hx)
  have haβ : a ∉ Subgroup.zpowers β := by
    intro haβ
    exact hnot ((Subgroup.zpowers_le.2 hβ_stab) haβ)
  have ha1 : a ≠ 1 := by
    rintro rfl
    change J.map (MonoidHom.id S) ≠ J at hJa
    exact hJa (Subgroup.map_id J)
  have hFgood : IsGood p (Subgroup.zpowers β ⊔ Subgroup.zpowers a) :=
    (isGood_zpowers_sup_zpowers (p := p) a).2
      (glaPLayer_inf_fixSubgroup_ne_bot_of_map_ne hp hJ hX hJa hap ha1)
  have hFle : Subgroup.zpowers β ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.2 hβA) (Subgroup.zpowers_le.2 ha)
  have hFcard : Nat.card (Subgroup.zpowers β ⊔ Subgroup.zpowers a :
      Subgroup (MulAut S)) = p ^ 2 :=
    card_zpowers_sup_zpowers_eq_prime_sq hp hβp hap hβ1 haβ hcomm.symm
  exact hnoGood _ hFle hFcard hFgood

private noncomputable def kd264BS_phi (hstab : A ≤ CFSG.GroupActions.subgroupStabAut J) :
    A →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
  (centerQuotientHom ↥J).comp
    ((CFSG.GroupActions.subgroupStabRestrict J).comp (Subgroup.inclusion hstab))

private theorem kd264BS_ker_eq (hp : p.Prime) (hA : IsElemAbelian p A)
    (hnoGood : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hβA : β ∈ A) (hβ1 : β ≠ 1) (hJ : GLAPComponent p (fixSubgroup β) J)
    (hstab : A ≤ CFSG.GroupActions.subgroupStabAut J) (hpJ : p ∣ Nat.card J) :
    (kd264BS_phi (A := A) (J := J) hstab).ker =
      Subgroup.zpowers (⟨β, hβA⟩ : A) := by
  have hperfJ : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hβp : β ^ p = 1 := hA.2 β hβA
  haveI : IsMulCommutative ↥A := hA.1
  have hzple : Subgroup.zpowers (⟨β, hβA⟩ : A) ≤
      (kd264BS_phi (A := A) (J := J) hstab).ker := by
    apply Subgroup.zpowers_le.2
    rw [MonoidHom.mem_ker]
    have hres : CFSG.GroupActions.subgroupStabRestrict J ⟨β, hstab hβA⟩ = 1 := by
      ext x
      rw [MulAut.one_apply]
      exact hJ.1 x.2
    simp only [kd264BS_phi, MonoidHom.comp_apply]
    rw [show (Subgroup.inclusion hstab) ⟨β, hβA⟩ = ⟨β, hstab hβA⟩ from rfl, hres, map_one]
  apply le_antisymm _ hzple
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  by_contra haβ
  simp only [kd264BS_phi, MonoidHom.comp_apply] at ha
  change (centerQuotientHom ↥J) (CFSG.GroupActions.subgroupStabRestrict J
    ⟨(a : MulAut S), hstab a.2⟩) = 1 at ha
  have hafix : J ≤ fixSubgroup (a : MulAut S) :=
    (centerQuotientHom_subgroupStabRestrict_eq_one_iff hperfJ (hstab a.2)).1 ha
  have hJlayer : GLAPLayer p J ≠ ⊥ := by
    intro hbot
    have hJself : GLAPComponent p J J :=
      CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp hJ le_rfl hJ.1
    have hJle : J ≤ GLAPLayer p J := by
      unfold GLAPLayer
      exact le_sSup (s := {L : Subgroup S | GLAPComponent p J L}) hJself
    have hJbot : J = ⊥ := le_bot_iff.1 (by simpa [hbot] using hJle)
    rw [hJbot, Subgroup.card_bot] at hpJ
    exact hp.not_dvd_one hpJ
  have hJne : GLAPLayer p (J ⊓ fixSubgroup (a : MulAut S)) ≠ ⊥ := by
    rwa [inf_eq_left.mpr hafix]
  have hFgood : IsGood p (Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S)) :=
    isGood_sup_zpowers_of_glaPLayer_inf_ne_bot hp hJ hJne
  have hcomm : (a : MulAut S) * β = β * a := by
    have hc := mul_comm' a ⟨β, hβA⟩
    exact congrArg Subtype.val hc
  have hFle : Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S) ≤ A :=
    sup_le (Subgroup.zpowers_le.2 hβA) (Subgroup.zpowers_le.2 a.2)
  have haβ' : (a : MulAut S) ∉ Subgroup.zpowers β := by
    intro h
    apply haβ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      apply Subtype.ext
      simpa using hk⟩
  have hFcard : Nat.card (Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S) :
      Subgroup (MulAut S)) = p ^ 2 :=
    card_zpowers_sup_zpowers_eq_prime_sq hp hβp (hA.2 a a.2) hβ1 haβ' hcomm.symm
  exact hnoGood _ hFle hFcard hFgood

private theorem kd264BS_D_noGood (hp : p.Prime) (hA : IsElemAbelian p A)
    (hnoGood : ∀ F ≤ A, Nat.card F = p ^ 2 → ¬ IsGood p F)
    (hβA : β ∈ A) (hβ1 : β ≠ 1) (hJ : GLAPComponent p (fixSubgroup β) J)
    (hstab : A ≤ CFSG.GroupActions.subgroupStabAut J)
    (hker : (kd264BS_phi (A := A) (J := J) hstab).ker =
      Subgroup.zpowers (⟨β, hβA⟩ : A))
    {i : TauCeti.CFSGIndex} (eJ : (↥J ⧸ Subgroup.center ↥J) ≃* i.Group) :
    ∀ d ∈ (kd264BS_phi (A := A) (J := J) hstab).range.map
        (MulAut.congr eJ).toMonoidHom, d ≠ 1 →
      GLAPLayer p (fixSubgroup d) = ⊥ := by
  haveI : Finite i.Group := Finite.of_equiv _ eJ.toEquiv
  haveI : IsMulCommutative ↥A := hA.1
  intro d hdD hd1
  obtain ⟨c, hc, hdc⟩ := Subgroup.mem_map.1 hdD
  obtain ⟨a, rfl⟩ := hc
  have hφa1 : (kd264BS_phi (A := A) (J := J) hstab) a ≠ 1 := by
    intro h
    apply hd1
    rw [← hdc, h, map_one]
  have haKer : a ∉ (kd264BS_phi (A := A) (J := J) hstab).ker :=
    fun h => hφa1 (MonoidHom.mem_ker.1 h)
  have haβA : a ∉ Subgroup.zpowers (⟨β, hβA⟩ : A) := by
    rw [hker] at haKer
    exact haKer
  have haβ : (a : MulAut S) ∉ Subgroup.zpowers β := by
    intro h
    apply haβA
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨k, by
      apply Subtype.ext
      simpa using hk⟩
  have hgoodφ : GLAPLayer p (fixSubgroup ((kd264BS_phi (A := A) (J := J) hstab) a)) = ⊥ := by
    by_contra hne
    change GLAPLayer p (fixSubgroup (centerQuotientHom ↥J
      (CFSG.GroupActions.subgroupStabRestrict J ⟨(a : MulAut S), hstab a.2⟩))) ≠ ⊥ at hne
    have hFlayer := glaPLayer_inf_fixSubgroup_ne_bot_of_centerQuotient_ne_bot
      hp hJ (hstab a.2) hne
    have hFgood : IsGood p (Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S)) :=
      (isGood_zpowers_sup_zpowers (p := p) (a : MulAut S)).2 hFlayer
    have hcomm : (a : MulAut S) * β = β * a := by
      have hc := mul_comm' a ⟨β, hβA⟩
      exact congrArg Subtype.val hc
    have hFle : Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S) ≤ A :=
      sup_le (Subgroup.zpowers_le.2 hβA) (Subgroup.zpowers_le.2 a.2)
    have hFcard : Nat.card (Subgroup.zpowers β ⊔ Subgroup.zpowers (a : MulAut S) :
        Subgroup (MulAut S)) = p ^ 2 :=
      card_zpowers_sup_zpowers_eq_prime_sq hp (hA.2 β hβA) (hA.2 a a.2) hβ1 haβ hcomm.symm
    exact hnoGood _ hFle hFcard hFgood
  rw [← hdc]
  change GLAPLayer p (fixSubgroup (MulAut.congr eJ ((kd264BS_phi (A := A) (J := J) hstab) a))) = ⊥
  rw [glaPLayer_fixSubgroup_congr hp eJ ((kd264BS_phi (A := A) (J := J) hstab) a), hgoodφ,
    Subgroup.map_bot]

theorem kd264BS_of_excNoGood {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hExc : KD264ExcNoGood p) : KD264BS p := by
  intro S _ _ A hA hAcard hnoGood β hβA hβ1 J hJ hpJ i heJ
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥A := hA.1
  have hstab := kd264BS_stab (p := p) hp hA hnoGood hβA hβ1 hJ
  let φ := kd264BS_phi (A := A) (J := J) hstab
  have hker := kd264BS_ker_eq (p := p) hp hA hnoGood hβA hβ1 hJ hstab hpJ
  have hperfJ : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hβp : β ^ p = 1 := hA.2 β hβA
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hkercard : Nat.card φ.ker = p := by
    rw [hker, Nat.card_zpowers, Subgroup.orderOf_mk, hβord]
  have hAcardφ : Nat.card A = p * Nat.card φ.range := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hkercard] at h
    exact h.symm
  obtain ⟨eJ⟩ := heJ
  let D : Subgroup (MulAut i.Group) := φ.range.map (MulAut.congr eJ).toMonoidHom
  have hAtop : IsElemAbelian p (⊤ : Subgroup ↥A) := by
    simpa using hA.subgroupOf A
  have hrange_el : IsElemAbelian p φ.range := by
    rw [MonoidHom.range_eq_map]
    exact hAtop.map φ
  have hDel : IsElemAbelian p D := by
    simpa [D] using hrange_el.map (MulAut.congr eJ).toMonoidHom
  have hDcard : Nat.card D = Nat.card φ.range := by
    change Nat.card (φ.range.map (MulAut.congr eJ).toMonoidHom) = Nat.card φ.range
    exact Subgroup.card_map_of_injective (MulAut.congr eJ).injective
  have hAcardD : Nat.card A = p * Nat.card D := by
    rw [hAcardφ, hDcard]
  have hD2 : p ^ 2 ≤ Nat.card D := by
    have h : p * p ^ 2 ≤ p * Nat.card D := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ ≤ Nat.card A := hAcard
        _ = p * Nat.card D := hAcardD
    exact Nat.le_of_mul_le_mul_left h hp.pos
  refine ⟨hstab, ⟨D, hDel, hAcardD⟩, ?_⟩
  intro e hi hchar
  subst i
  haveI : Finite (TauCeti.CFSGIndex.lie e).Group := Finite.of_equiv _ eJ.toEquiv
  have hp_dvd : p ∣ Nat.card (TauCeti.CFSGIndex.lie e).Group := by
    have hdvd := CFSG.LocalAnalysis.RankThreeTheoremC.InnerQ.ResidueJZero.dvd_card_quotient_center_of_perfect
      (Y := ↥J) hperfJ.commutator_eq_top (p := p) hpJ
    have hcardeq : Nat.card (↥J ⧸ Subgroup.center ↥J) =
        Nat.card (TauCeti.CFSGIndex.lie e).Group := Nat.card_congr eJ.toEquiv
    rwa [hcardeq] at hdvd
  have hDnogood := kd264BS_D_noGood hp hA hnoGood hβA hβ1 hJ hstab hker eJ
  have hexc := hExc e hchar hp_dvd D hDel hD2 hDnogood
  rcases hexc with h1 | h2 | h3 | h4
  · exact Or.inl h1
  · refine Or.inr (Or.inl ?_)
    rcases h2 with ⟨hp3, hex8, d, hdD, hdnot⟩
    refine ⟨hp3, hex8, ?_⟩
    obtain ⟨c, hc, hdc⟩ := Subgroup.mem_map.1 hdD
    obtain ⟨a, rfl⟩ := hc
    rw [← hdc] at hdnot
    have hφnot : φ a ∉ innAutDerived (↥J ⧸ Subgroup.center ↥J) := by
      intro hmem
      exact hdnot ((mem_innAutDerived_congr eJ).2 hmem)
    change centerQuotientHom ↥J (subgroupStabRestrict J
      ⟨(a : MulAut S), hstab a.2⟩) ∉ _ at hφnot
    exact ⟨a, a.2, hstab a.2, hφnot⟩
  · exact Or.inr (Or.inr (Or.inl h3))
  · refine Or.inr (Or.inr (Or.inr ⟨h4.1, ?_⟩))
    rw [hAcardD, h4.2]
    ring

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
