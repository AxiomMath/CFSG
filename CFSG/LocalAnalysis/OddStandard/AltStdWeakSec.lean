module

public import CFSG.LocalAnalysis.OddStandard.AltStdWeakMain
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermFinal

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Quot

variable {H : Type} [Group H] [Finite H]

theorem weakShape_quotient_oddCore {t : H} {B : Subgroup H} {m : ℕ} (h : WeakShape t B m)
    (hm : 5 ≤ m) :
    WeakShape (QuotientGroup.mk t : H ⧸ CFSG.oddCore H)
      (B.map (QuotientGroup.mk' (CFSG.oddCore H))) m := by
  classical
  obtain ⟨e⟩ := h.iso
  set P := CFSG.oddCore H with hPdef
  have hPodd : ∀ x ∈ P, Odd (orderOf x) := fun x hx => orderOf_odd_of_mem_oddCore hx
  have ht1 : t * t = 1 := by rw [← sq, ← h.order]; exact pow_orderOf_eq_one t
  have hBP : B ⊓ P = ⊥ := inf_oddCore_eq_bot_of_alt hm e
  have hinj : Function.Injective ((QuotientGroup.mk' P).domRestrict B) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have hb1 : (QuotientGroup.mk' P) (b : H) = 1 := hb
    have : (b : H) ∈ B ⊓ P := ⟨b.2, (QuotientGroup.eq_one_iff _).1 hb1⟩
    rw [hBP] at this
    exact Subtype.ext this
  have hconj : ∀ c ∈ normalizer (B : Set H), ∀ y : H ⧸ P,
      y ∈ B.map (QuotientGroup.mk' P) ↔
        (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ ∈ B.map (QuotientGroup.mk' P) := by
    intro c hc y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    constructor
    · rintro ⟨b, hb, hby⟩
      refine ⟨c * b * c⁻¹, (mem_normalizer_iff.1 hc b).1 hb, ?_⟩
      rw [← hby]
      simp
    · rintro ⟨b, hb, hby⟩
      refine ⟨c⁻¹ * b * c, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hc) b).1 hb
        simpa using this
      · have h1 : (b : H ⧸ P) = (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ := hby
        have : ((c⁻¹ * b * c : H) : H ⧸ P) = (c : H ⧸ P)⁻¹ * b * (c : H ⧸ P) := by simp
        simp only [QuotientGroup.mk'_apply, this, h1]
        group
  have hcB : ∀ c ∈ centralizer ({t} : Set H),
      (c : H ⧸ P) ∈ centralizer ((B.map (QuotientGroup.mk' P) : Subgroup (H ⧸ P)) :
        Set (H ⧸ P)) → c ∈ centralizer (B : Set H) := by
    intro c hc hxB
    have hcN : c ∈ normalizer (B : Set H) := h.cent_le_norm hc
    rw [mem_centralizer_iff]
    intro b hb
    have hcomm : (b : H ⧸ P) * (c : H ⧸ P) = (c : H ⧸ P) * (b : H ⧸ P) :=
      mem_centralizer_iff.1 hxB (b : H ⧸ P) ⟨b, hb, rfl⟩
    have h1 : c * b * c⁻¹ * b⁻¹ ∈ B :=
      mul_mem ((mem_normalizer_iff.1 hcN b).1 hb) (inv_mem hb)
    have h2 : c * b * c⁻¹ * b⁻¹ ∈ P := by
      rw [← QuotientGroup.eq_one_iff]
      have : ((c * b * c⁻¹ * b⁻¹ : H) : H ⧸ P) =
          (c : H ⧸ P) * b * (c : H ⧸ P)⁻¹ * (b : H ⧸ P)⁻¹ := by simp
      rw [this, ← hcomm]
      group
    have h3 : c * b * c⁻¹ * b⁻¹ ∈ B ⊓ P := ⟨h1, h2⟩
    rw [hBP] at h3
    have h4 : c * b * c⁻¹ * b⁻¹ = 1 := h3
    calc b * c = (c * b * c⁻¹ * b⁻¹)⁻¹ * (c * b) := by group
      _ = c * b := by rw [h4]; group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · have h2 : t ^ 2 = 1 := by rw [← h.order]; exact pow_orderOf_eq_one t
      rw [← QuotientGroup.mk_pow, h2]
      rfl
    · intro h1
      exact ClassicalInvolution.QuaternionStructure.not_mem_oddCore_of_orderOf_eq_two h.order
        ((QuotientGroup.eq_one_iff t).1 h1)
  · exact ⟨(ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective
      (QuotientGroup.mk' P) B hinj).symm.trans e⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (h.le_cent hb)
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage hPodd ht1 hx
    rw [mem_normalizer_iff]
    exact hconj c (h.cent_le_norm hc)
  · rintro y ⟨hyB, hyt⟩ k hyk
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage hPodd ht1 hyt
    have hcB' := hcB c hc hyB
    have hck : c ^ 2 ^ k ∈ P :=
      (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hyk)
    have hrodd : Odd (orderOf (c ^ 2 ^ k)) := hPodd _ hck
    have hc' : (c ^ orderOf (c ^ 2 ^ k)) ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one]
    have hmem : c ^ orderOf (c ^ 2 ^ k) ∈ zpowers t :=
      h.two_mem _ ⟨pow_mem hcB' _, pow_mem hc _⟩ k hc'
    have hmem' : (c : H ⧸ P) ^ orderOf (c ^ 2 ^ k) ∈ zpowers (t : H ⧸ P) := by
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' P) hmem
      rw [MonoidHom.map_zpowers] at this
      simpa [QuotientGroup.mk_pow] using this
    have hcop : (orderOf (c ^ 2 ^ k)).Coprime (orderOf (c : H ⧸ P)) :=
      (Nat.Coprime.pow_right k hrodd.coprime_two_right).coprime_dvd_right
        (orderOf_dvd_of_pow_eq_one hyk)
    obtain ⟨s, hs⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hs]
    exact pow_mem hmem' s

end Quot

section Section

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {n : ℕ}

theorem weakShape_section (h : WeakShape t A n) {R B : Subgroup X}
    (hBA : B ≤ A ⊓ centralizer (R : Set X)) {m : ℕ}
    (hBiso : Nonempty (B ≃* alternatingGroup (Fin m))) (hm : 5 ≤ m)
    (hnorm : centralizer ({t} : Set X) ⊓ centralizer (R : Set X) ≤ normalizer (B : Set X))
    (hcc : ∀ c ∈ centralizer (B : Set X) ⊓ centralizer ({t} : Set X) ⊓ centralizer (R : Set X),
      ∀ k : ℕ, c ^ 2 ^ k = 1 → c ∈ zpowers t)
    (ht : t ∈ centralizer (R : Set X)) :
    WeakShape (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (R : Set X))) : Sec X R)
      ((B.subgroupOf (centralizer (R : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (R : Set X))))) m := by
  obtain ⟨e⟩ := hBiso
  set C := centralizer (R : Set X) with hC
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  have hBt : ∀ b ∈ B, b * t = t * b := fun b hb =>
    mem_centralizer_singleton_iff.1 (h.le_cent (hBA hb).1)
  let t₀ : ↥C := ⟨t, ht⟩
  have ht₀ : orderOf t₀ = 2 := by rw [Subgroup.orderOf_mk]; exact h.order
  let e₀ : B.subgroupOf C ≃* alternatingGroup (Fin m) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans e
  refine weakShape_quotient_oddCore (t := t₀) (B := B.subgroupOf C) ⟨ht₀, ⟨e₀⟩, ?_, ?_, ?_⟩ hm
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact hBt x (Subgroup.mem_subgroupOf.1 hx)
  · intro c hc
    have hcX : (c : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      exact congrArg Subtype.val hc
    have hcN : (c : X) ∈ normalizer (B : Set X) := hnorm (Subgroup.mem_inf.2 ⟨hcX, c.2⟩)
    rw [mem_normalizer_iff]
    intro b
    have := mem_normalizer_iff.1 hcN b
    simpa [Subgroup.mem_subgroupOf] using this
  · intro c hc k hck
    obtain ⟨hcB, hct⟩ := Subgroup.mem_inf.1 hc
    have hcX : (c : X) ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hct ⊢
      exact congrArg Subtype.val hct
    have hcBX : (c : X) ∈ centralizer (B : Set X) := by
      rw [mem_centralizer_iff]
      intro b hb
      have := mem_centralizer_iff.1 hcB ⟨b, hBC hb⟩ (Subgroup.mem_subgroupOf.2 hb)
      exact congrArg Subtype.val this
    have hckX : (c : X) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hck
      simpa using this
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1
      (hcc _ (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcBX, hcX⟩, c.2⟩) k hckX)
    exact mem_zpowers_iff.2 ⟨j, Subtype.ext (by simpa using hj)⟩

end Section

section Perm

variable {X : Type} [Group X] {A : Subgroup X} {n : ℕ} {t : X} (e : A ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n) (h : WeakShape t A n)

include hn h in
theorem hnorm_of_perm_of_weakShape {R' T : Subgroup (Equiv.Perm (Fin n))}
    (hR' : R' ≤ alternatingGroup (Fin n))
    (hRT : ∀ σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))),
      σ ∈ normalizer (T : Set (Equiv.Perm (Fin n)))) :
    centralizer ({t} : Set X) ⊓ centralizer (corr (X := X) e R' : Set X) ≤
      normalizer (corr (X := X) e T : Set X) := by
  intro c hc
  obtain ⟨hct, hcR⟩ := Subgroup.mem_inf.1 hc
  have hcN := h.cent_le_norm hct
  exact mem_normalizer_corr e hn hcN (hRT _ (rho_mem_centralizer e hn hR' hcN hcR))

include hn h in
theorem two_mem_of_perm_of_weakShape {R' T : Subgroup (Equiv.Perm (Fin n))}
    (hR' : R' ≤ alternatingGroup (Fin n)) (hT : T ≤ alternatingGroup (Fin n))
    (htriv : ∀ σ ∈ centralizer (T : Set (Equiv.Perm (Fin n))),
      σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))) → σ = 1) :
    ∀ c ∈ centralizer (corr (X := X) e T : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e R' : Set X), ∀ k : ℕ, c ^ 2 ^ k = 1 → c ∈ zpowers t := by
  intro c hc k hck
  obtain ⟨⟨hcB, hct⟩, hcR⟩ := (Subgroup.mem_inf.1 hc).imp_left Subgroup.mem_inf.1
  have hcN := h.cent_le_norm hct
  have h1 : rho e hn ⟨c, hcN⟩ = 1 :=
    htriv _ (rho_mem_centralizer e hn hT hcN hcB) (rho_mem_centralizer e hn hR' hcN hcR)
  have hcA : c ∈ centralizer (A : Set X) := (rho_eq_one_iff e hn ⟨c, hcN⟩).1 h1
  exact h.two_mem c ⟨hcA, hct⟩ k hck

include hn h in
theorem two_mem_of_perm_le_of_weakShape {R' T : Subgroup (Equiv.Perm (Fin n))}
    (hR' : R' ≤ alternatingGroup (Fin n)) (hT : T ≤ alternatingGroup (Fin n))
    (hodd : Odd (Nat.card R'))
    (hle : ∀ σ ∈ centralizer (T : Set (Equiv.Perm (Fin n))),
      σ ∈ centralizer (R' : Set (Equiv.Perm (Fin n))) → σ ∈ R') :
    ∀ c ∈ centralizer (corr (X := X) e T : Set X) ⊓ centralizer ({t} : Set X) ⊓
      centralizer (corr (X := X) e R' : Set X), ∀ k : ℕ, c ^ 2 ^ k = 1 → c ∈ zpowers t := by
  intro c hc k hck
  obtain ⟨⟨hcB, hct⟩, hcR⟩ := (Subgroup.mem_inf.1 hc).imp_left Subgroup.mem_inf.1
  have hcN := h.cent_le_norm hct
  set σ := rho e hn ⟨c, hcN⟩ with hσ
  have hσR : σ ∈ R' :=
    hle _ (rho_mem_centralizer e hn hT hcN hcB) (rho_mem_centralizer e hn hR' hcN hcR)
  have hσk : σ ^ 2 ^ k = 1 := by
    have : (⟨c, hcN⟩ : normalizer (A : Set X)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hck)
    rw [hσ, ← map_pow, this, map_one]
  have h1 : σ = 1 := by
    have hdvd1 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hσk
    have hdvd2 : orderOf σ ∣ Nat.card R' := by
      have := orderOf_dvd_natCard (⟨σ, hσR⟩ : R')
      rwa [Subgroup.orderOf_mk] at this
    have hcop : (orderOf σ).Coprime (Nat.card R') :=
      Nat.Coprime.coprime_dvd_left hdvd1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
    exact orderOf_eq_one_iff.1 (hcop.eq_one_of_dvd hdvd2)
  have hcA : c ∈ centralizer (A : Set X) := (rho_eq_one_iff e hn ⟨c, hcN⟩).1 h1
  exact h.two_mem c ⟨hcA, hct⟩ k hck

end Perm

section Root

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {n : ℕ}

theorem weakShape_section_root (h : WeakShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : 4 ≤ S.card) (hSc : 5 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X)) :
    WeakShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) := by
  have hSc' : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; exact hSc
  have hSc4 : 4 ≤ Sᶜ.card := by omega
  have hn : 8 ≤ n := eight_le_of_cards hS hSc4 (by omega)
  have hdisj : ∀ g ∈ altSub S, ∀ g' ∈ altSub Sᶜ, g * g' = g' * g := fun g hg g' hg' =>
    comm_of_altSub_disjoint disjoint_compl_right hg hg'
  have hBA := corr_le_centralizer_corr (X := X) e hdisj
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := X) e Sᶜ
  have hnorm := hnorm_of_perm_of_weakShape e hn h (altSub_le_alternatingGroup S)
    (fun σ hσ => mem_normalizer_altSub
      (compl_iff_of_fixes ((mem_centralizer_altSub_iff hS).1 hσ)))
  have hcc := two_mem_of_perm_of_weakShape e hn h (altSub_le_alternatingGroup S)
    (altSub_le_alternatingGroup Sᶜ) (fun σ hσT hσR => by
      have h1 := (mem_centralizer_altSub_iff hSc4).1 hσT
      have h2 := (mem_centralizer_altSub_iff hS).1 hσR
      refine Equiv.ext fun i => ?_
      by_cases hi : i ∈ S
      · simpa using h2 i hi
      · simpa using h1 i (by simpa using hi))
  have := weakShape_section h hBA ⟨eB⟩ hSc' hnorm hcc ht
  rwa [card_compl_fin] at this

theorem exactShape_section_root_of_weakShape (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (h : WeakShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : 4 ≤ S.card) (hSc : 9 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X))
    (hK : CFSG.SectionRank.IsKGroupCat (Sec X (corr (X := X) e (altSub S)))) :
    ExactShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) :=
  exactShape_of_weakShape hlookup hHN hOut hFour hK
    (ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _)
    (weakShape_section_root h e hS (by omega) ht) hSc

theorem weakShape_section_three (h : WeakShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X)) :
    WeakShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) := by
  have hSc' : 5 ≤ Sᶜ.card := by rw [card_compl_fin]; exact hSc
  have hn : 8 ≤ n := eight_le_of_cards (le_of_eq hS.symm) hSc' (by omega)
  have hdisj : ∀ g ∈ altSub S, ∀ g' ∈ altSub Sᶜ, g * g' = g' * g := fun g hg g' hg' =>
    comm_of_altSub_disjoint disjoint_compl_right hg hg'
  have hBA := corr_le_centralizer_corr (X := X) e hdisj
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := X) e Sᶜ
  have hnorm := hnorm_of_perm_of_weakShape e hn h (altSub_le_alternatingGroup S)
    (fun σ hσ => mem_normalizer_altSub (T := Sᶜ) (fun i => by
      simpa using (mem_iff_of_centralizer_altSub_card_three hS hσ i).not))
  have hcc := two_mem_of_perm_le_of_weakShape e hn h (altSub_le_alternatingGroup S)
    (altSub_le_alternatingGroup Sᶜ) (by rw [card_altSub_of_card_three hS]; decide)
    (fun σ hσT hσR => by
      have h1 := (mem_centralizer_altSub_iff (by omega : 4 ≤ Sᶜ.card)).1 hσT
      refine mem_altSub_of_card_three hS (fun i hi => h1 i (by simpa using hi))
        (fun x hx y hy z hz hxy hyz hxz => ?_)
      exact (mem_centralizer_iff.1 hσR _ (cyc3_mem_altSub hx hy hz hxy hyz hxz)).symm)
  have := weakShape_section h hBA ⟨eB⟩ hSc' hnorm hcc ht
  rwa [card_compl_fin] at this

theorem exactShape_section_three_of_weakShape (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (h : WeakShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 9 ≤ n - S.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X))
    (hK : CFSG.SectionRank.IsKGroupCat (Sec X (corr (X := X) e (altSub S)))) :
    ExactShape
      (QuotientGroup.mk (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) :
        Sec X (corr (X := X) e (altSub S)))
      (((corr (X := X) e (altSub Sᶜ)).subgroupOf
          (centralizer (corr (X := X) e (altSub S) : Set X))).map
        (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)))))
      (n - S.card) :=
  exactShape_of_weakShape hlookup hHN hOut hFour hK
    (ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _)
    (weakShape_section_three h e hS (by omega) ht) hSc

end Root

end CFSG.OddStandard.AltStdSec
