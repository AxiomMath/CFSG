module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenLiftB
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupDefs
public import CFSG.LocalAnalysis.OddStandard.AltStdSecPermFinal
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] noncomputable def secComp (e : L ≃* alternatingGroup (Fin n)) (S : Finset (Fin n)) :
    Subgroup (Sec G (corr (X := G) e (altSub S))) :=
  ((corr (X := G) e (altSub Sᶜ)).subgroupOf
      (centralizer (corr (X := G) e (altSub S) : Set G))).map
    (QuotientGroup.mk' (CFSG.oddCore ↥(centralizer (corr (X := G) e (altSub S) : Set G))))

@[expose] def CaseIIIAt (e : L ≃* alternatingGroup (Fin n)) (z : G) (S : Finset (Fin n)) : Prop :=
  ∃ ht : z ∈ centralizer (corr (X := G) e (altSub S) : Set G),
    WreathOutcome (QuotientGroup.mk ⟨z, ht⟩ : Sec G (corr (X := G) e (altSub S)))
      (secComp e S) (n - S.card)

end Defs

section Oddc

variable {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X} {n : ℕ}

omit [Finite X] in
theorem mem_of_odd_mem_zpowers_sup {R : Subgroup X} (ht2 : t * t = 1)
    (hcomm : ∀ r ∈ R, t * r = r * t) {u : X} (hu : u ∈ zpowers t ⊔ R)
    (hodd : Odd (orderOf u)) : u ∈ R := by
  let D : Subgroup X :=
    { carrier := {x | ∃ i : ℤ, ∃ r ∈ R, x = t ^ i * r}
      mul_mem' := by
        rintro _ _ ⟨i, r, hr, rfl⟩ ⟨j, r', hr', rfl⟩
        refine ⟨i + j, r * r', R.mul_mem hr hr', ?_⟩
        have hc : Commute (t ^ j) r := Commute.zpow_left (hcomm r hr) j
        calc t ^ i * r * (t ^ j * r') = t ^ i * (r * t ^ j) * r' := by group
          _ = t ^ i * (t ^ j * r) * r' := by rw [← hc.eq]
          _ = t ^ (i + j) * (r * r') := by rw [zpow_add]; group
      one_mem' := ⟨0, 1, R.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, r, hr, rfl⟩
        refine ⟨-i, r⁻¹, R.inv_mem hr, ?_⟩
        have hc : Commute (t ^ i) r := Commute.zpow_left (hcomm r hr) i
        calc (t ^ i * r)⁻¹ = r⁻¹ * (t ^ i)⁻¹ := by group
          _ = (t ^ i)⁻¹ * r⁻¹ := hc.inv_inv.eq.symm
          _ = t ^ (-i) * r⁻¹ := by rw [zpow_neg] }
  have hle : zpowers t ⊔ R ≤ D := sup_le
    (by rintro _ ⟨i, rfl⟩; exact ⟨i, 1, R.one_mem, by simp⟩)
    (fun r hr => ⟨0, r, hr, by simp⟩)
  obtain ⟨i, r, hr, rfl⟩ := hle hu
  have hc : Commute (t ^ i) r := Commute.zpow_left (hcomm r hr) i
  have hsq : (t ^ i * r) ^ 2 = r ^ 2 := by
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht2]
    have htz : (t ^ i) ^ 2 = 1 := by
      calc (t ^ i) ^ 2 = t ^ i * t ^ i := pow_two _
        _ = t ^ (i + i) := (zpow_add t i i).symm
        _ = t ^ (2 * i) := by rw [two_mul]
        _ = (t ^ (2 : ℤ)) ^ i := zpow_mul t 2 i
        _ = 1 := by rw [h2, one_zpow]
    rw [hc.mul_pow, htz, one_mul]
  obtain ⟨k, hk⟩ := hodd
  have hpow : (t ^ i * r) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have hu2 : t ^ i * r = ((t ^ i * r) ^ 2) ^ (k + 1) := by
    calc t ^ i * r = (t ^ i * r) ^ (2 * k + 1) * (t ^ i * r) := by rw [hpow, one_mul]
      _ = (t ^ i * r) ^ (2 * k + 1 + 1) := (pow_succ _ _).symm
      _ = (t ^ i * r) ^ (2 * (k + 1)) := by congr 1
      _ = ((t ^ i * r) ^ 2) ^ (k + 1) := pow_mul _ _ _
  rw [hu2, hsq]
  exact R.pow_mem (R.pow_mem hr 2) _

theorem centralizer_oddCore_le_root (h : ExactShape t A n) (e : A ≃* alternatingGroup (Fin n))
    {S : Finset (Fin n)} (hS : S.card = 3) (hSc : 5 ≤ Sᶜ.card)
    (ht : t ∈ centralizer (corr (X := X) e (altSub S) : Set X)) :
    ∀ u ∈ CFSG.oddCore ↥(centralizer (corr (X := X) e (altSub S) : Set X)),
      (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X))) * u *
        (⟨t, ht⟩ : ↥(centralizer (corr (X := X) e (altSub S) : Set X)))⁻¹ = u →
      u ∈ (corr (X := X) e (altSub S)).subgroupOf
        (centralizer (corr (X := X) e (altSub S) : Set X)) := by
  set R : Subgroup X := corr (X := X) e (altSub S) with hR
  set C : Subgroup X := centralizer (R : Set X) with hC
  set B : Subgroup X := corr (X := X) e (altSub Sᶜ) with hB
  intro u hu hzu
  have hBA : B ≤ A ⊓ C := corr_le_centralizer_corr (X := X) e
    (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg')
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := X) e Sᶜ
  let eB' : B.subgroupOf C ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
  have hbot : B.subgroupOf C ⊓ CFSG.oddCore ↥C = ⊥ :=
    inf_oddCore_eq_bot_of_alt (by omega) eB'
  have hzu' : (⟨t, ht⟩ : ↥C) * u = u * (⟨t, ht⟩ : ↥C) := mul_inv_eq_iff_eq_mul.1 hzu
  have hut : (u : X) ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val hzu').symm
  have hnormB : (u : X) ∈ normalizer (B : Set X) :=
    hnorm_three h e hS hSc (Subgroup.mem_inf.2 ⟨hut, u.2⟩)
  have hucB : (u : X) ∈ centralizer (B : Set X) := by
    rw [mem_centralizer_iff]
    intro b hb
    set b' : ↥C := ⟨b, hBC hb⟩ with hb'
    have hcO : u * b' * u⁻¹ * b'⁻¹ ∈ CFSG.oddCore ↥C := by
      have h1 : b' * u⁻¹ * b'⁻¹ ∈ CFSG.oddCore ↥C :=
        (inferInstance : (CFSG.oddCore ↥C).Normal).conj_mem _ (inv_mem hu) b'
      have : u * b' * u⁻¹ * b'⁻¹ = u * (b' * u⁻¹ * b'⁻¹) := by group
      rw [this]
      exact mul_mem hu h1
    have hcB : u * b' * u⁻¹ * b'⁻¹ ∈ B.subgroupOf C := by
      rw [Subgroup.mem_subgroupOf]
      have h1 : (u : X) * b * (u : X)⁻¹ ∈ B := by
        have := (mem_normalizer_iff.1 hnormB b).1 hb
        simpa using this
      have h2 : (u : X) * b * (u : X)⁻¹ * b⁻¹ ∈ B := B.mul_mem h1 (B.inv_mem hb)
      simpa using h2
    have hc1 : u * b' * u⁻¹ * b'⁻¹ ∈ B.subgroupOf C ⊓ CFSG.oddCore ↥C := ⟨hcB, hcO⟩
    rw [hbot] at hc1
    have hc2 : u * b' * u⁻¹ * b'⁻¹ = 1 := hc1
    have hc3 : u * b' = b' * u := by
      have h5 : u * b' * u⁻¹ = b' := mul_inv_eq_one.1 hc2
      calc u * b' = (u * b' * u⁻¹) * u := by group
        _ = b' * u := by rw [h5]
    exact (congrArg Subtype.val hc3).symm
  have hcc : (u : X) ∈ zpowers t ⊔ R := by
    refine hcc_three h e hS hSc ?_
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hucB, hut⟩, u.2⟩
  have hodd : Odd (orderOf (u : X)) := by
    rw [Subgroup.orderOf_coe]; exact orderOf_odd_of_mem_oddCore hu
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order, pow_two] at this
  have hcomm : ∀ r ∈ R, t * r = r * t := fun r hr =>
    (mem_centralizer_iff.1 ht r hr).symm
  exact Subgroup.mem_subgroupOf.2 (mem_of_odd_mem_zpowers_sup ht2 hcomm hcc hodd)

end Oddc

section SecLift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem exists_sec_lift (h : ExactShape z L n) (e : L ≃* alternatingGroup (Fin n))
    (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3) (hIII : CaseIIIAt e z S) :
    ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, Function.Injective ψ ∧
      (∀ b, ψ b * (z * ψ b * z⁻¹) = b) ∧
      (∀ a b, ψ a * (z * ψ b * z⁻¹) = (z * ψ b * z⁻¹) * ψ a) ∧
      (∀ x, ψ x = z * ψ x * z⁻¹ → x = 1) ∧
      (∀ b, ψ b ∈ centralizer (corr (X := G) e (altSub S) : Set G)) := by
  obtain ⟨ht, K, hKc, hKne, -, ⟨eK⟩, hdiag⟩ := hIII
  set R : Subgroup G := corr (X := G) e (altSub S) with hR
  set C : Subgroup G := centralizer (R : Set G) with hC
  set B : Subgroup G := corr (X := G) e (altSub Sᶜ) with hB
  have hSc : 5 ≤ Sᶜ.card := by rw [card_compl_fin, hS]; omega
  have hBA : B ≤ L ⊓ C := corr_le_centralizer_corr (X := G) e
    (fun g hg g' hg' => comm_of_altSub_disjoint disjoint_compl_right hg hg')
  have hBC : B ≤ C := fun b hb => (hBA hb).2
  have hBL : B ≤ L := fun b hb => (hBA hb).1
  have hOodd : Odd (Nat.card (CFSG.oddCore ↥C)) :=
    ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore ↥C
  have ht2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.order, pow_two] at this
  have hRO : R.subgroupOf C ≤ CFSG.oddCore ↥C := by
    intro x hx
    have hxR : (x : G) ∈ R := hx
    obtain ⟨y, hy, hyx⟩ := corr_altSub_le_oddCoreOf (X := G) e hS hxR
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hRc : R.subgroupOf C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (mem_centralizer_iff.1 g.2 (x : G) hx).symm
  obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e Sᶜ
  let eB' : B.subgroupOf C ≃* alternatingGroup (Fin Sᶜ.card) :=
    (Subgroup.subgroupOfEquivOfLe hBC).trans eB
  have hBperf : ⁅B.subgroupOf C, B.subgroupOf C⁆ = B.subgroupOf C :=
    Subgroup.isPerfect_iff.1 ⟨(isQuasisimple_of_alt hSc eB').1⟩
  have hBz : ∀ b ∈ B.subgroupOf C, (⟨z, ht⟩ : ↥C) * b * (⟨z, ht⟩ : ↥C)⁻¹ = b := by
    intro b hb
    have hbL : (b : G) ∈ L := hBL hb
    have h1 : (b : G) * z = z * b :=
      mem_centralizer_singleton_iff.1 (h.le_cent hbL)
    have : (⟨z, ht⟩ : ↥C) * b = b * (⟨z, ht⟩ : ↥C) := Subtype.ext h1.symm
    rw [this]; group
  set zq : Sec G R := QuotientGroup.mk (⟨z, ht⟩ : ↥C) with hzq
  have hKK : ∀ a ∈ K, ∀ b ∈ K, a * (zq * b * zq⁻¹) = (zq * b * zq⁻¹) * a := by
    have hK'c : CFSG.IsComponent (K.map (MulAut.conj zq).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj zq) hKc
    rcases CFSG.LocalCores.distinct_components_commute hKc hK'c with h1 | h1
    · exact absurd h1.symm hKne
    · intro a ha b hb
      have h2 : a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹ ∈
          ⁅K, K.map (MulAut.conj zq).toMonoidHom⁆ := by
        have := Subgroup.commutator_mem_commutator ha
          (show zq * b * zq⁻¹ ∈ K.map (MulAut.conj zq).toMonoidHom from ⟨b, hb, by simp⟩)
        simpa [commutatorElement_def] using this
      rw [h1] at h2
      have h3 : a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹ = 1 := h2
      calc a * (zq * b * zq⁻¹) = (a * (zq * b * zq⁻¹) * a⁻¹ * (zq * b * zq⁻¹)⁻¹) *
            ((zq * b * zq⁻¹) * a) := by group
        _ = (zq * b * zq⁻¹) * a := by rw [h3, one_mul]
  have hB' : ∀ g : Sec G R, g ∈ (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.oddCore ↥C)) ↔
      ∃ k ∈ K, g = k * (zq * k * zq⁻¹) := by
    intro g
    have := Set.ext_iff.1 hdiag g
    simpa [secComp] using this
  obtain ⟨Q, ψN, hQmap, hQperf, hQbot, hQO, hQQz, hQQzbot, hψQ, hinj, hdN⟩ :=
    exists_wreath_lift (O := CFSG.oddCore ↥C) (R := R.subgroupOf C) (B := B.subgroupOf C)
      hOodd hRO hRc (z := (⟨z, ht⟩ : ↥C)) (Subtype.ext ht2) (fun u hu hzu =>
        centralizer_oddCore_le_root h e hS hSc ht u hu hzu)
      (m := n - S.card) (by omega) eK hKK hBperf hBz hB'
  let eBN : ↥B ≃* ↥(B.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hBC).symm
  have hcoe : ∀ b : ↥B, (((eBN b : ↥(B.subgroupOf C)) : ↥C) : G) = (b : G) := fun b => rfl
  let ψ : ↥B →* G := C.subtype.comp (ψN.comp eBN.toMonoidHom)
  have hψ : ∀ b : ↥B, ψ b = ((ψN (eBN b) : ↥C) : G) := fun b => rfl
  refine ⟨ψ, Subtype.val_injective.comp (hinj.comp eBN.injective), ?_, ?_, ?_, ?_⟩
  · intro b
    have h2 := congrArg Subtype.val (hdN (eBN b))
    simpa [hψ, hcoe] using h2
  · intro a b
    have hmemx : (⟨z, ht⟩ : ↥C) * ψN (eBN b) * (⟨z, ht⟩ : ↥C)⁻¹ ∈
        zConjSub (⟨z, ht⟩ : ↥C) Q := mem_zConjSub.2 ⟨ψN (eBN b), hψQ _, rfl⟩
    have h2 := congrArg Subtype.val (hQQz (ψN (eBN a)) (hψQ _) _ hmemx)
    simpa [hψ] using h2
  · intro x hx
    have h1 : ψN (eBN x) = (⟨z, ht⟩ : ↥C) * ψN (eBN x) * (⟨z, ht⟩ : ↥C)⁻¹ := by
      apply Subtype.ext
      simpa [hψ] using hx
    have h2 : ψN (eBN x) ∈ Q ⊓ zConjSub (⟨z, ht⟩ : ↥C) Q :=
      ⟨hψQ _, mem_zConjSub.2 ⟨ψN (eBN x), hψQ _, h1.symm⟩⟩
    rw [hQQzbot] at h2
    have h3 : ψN (eBN x) = 1 := Subgroup.mem_bot.1 h2
    have h4 : eBN x = 1 := hinj (h3.trans (map_one ψN).symm)
    exact eBN.injective (h4.trans (map_one eBN).symm)
  · intro b
    exact (ψN (eBN b)).2

end SecLift

section RootLift

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

structure IsRootLift (e : L ≃* alternatingGroup (Fin n)) (z : G) (S : Finset (Fin n))
    (ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G) : Prop where
  inj : Function.Injective ψ
  diag : ∀ b, ψ b * (z * ψ b * z⁻¹) = b
  comm : ∀ a b, ψ a * (z * ψ b * z⁻¹) = (z * ψ b * z⁻¹) * ψ a
  rigid : ∀ x, ψ x = z * ψ x * z⁻¹ → x = 1
  cent : ∀ b, ψ b ∈ centralizer (corr (X := G) e (altSub S) : Set G)

theorem exists_rootLift [Finite G] {z : G} (h : ExactShape z L n)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {S : Finset (Fin n)} (hS : S.card = 3)
    (hIII : CaseIIIAt e z S) :
    ∃ ψ : ↥(corr (X := G) e (altSub Sᶜ)) →* G, IsRootLift e z S ψ := by
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := exists_sec_lift h e hn hS hIII
  exact ⟨ψ, ⟨h1, h2, h3, h4, h5⟩⟩

end RootLift

end CFSG.OddStandard.AltStdSec
