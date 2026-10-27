module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddZeroCover
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Basic
public import CFSG.GroupTheory.ElementaryAbelianBasis
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mul_self_eq_one_of_orderOf_eq_two {g : G} (hg : orderOf g = 2) : g * g = 1 := by
  rw [← pow_two]
  have h := pow_orderOf_eq_one g
  rwa [hg] at h

omit [Finite G] in
private theorem exists_involution_conj_eq_or_fixed {Q : Subgroup G} {b q : G}
    (hb2 : b * b = 1) (hQodd : Odd (Nat.card (center ↥Q))) (hqQ : q ∈ Q)
    (hinner : ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹) :
    (∃ e ∈ Q, orderOf e = 2 ∧ ∀ z ∈ Q, e * z * e⁻¹ = b * z * b⁻¹) ∨
      ∀ z ∈ Q, b * z * b⁻¹ = z := by
  have hbq : b * q * b⁻¹ = q := by simpa using hinner q hqQ
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hq2comm : ∀ z ∈ Q, (q * q) * z = z * (q * q) := by
    intro z hz
    have hzq : q * z * q⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hqQ hz) (Q.inv_mem hqQ)
    have h1 : b * (q * z * q⁻¹) * b⁻¹ = q * (q * z * q⁻¹) * q⁻¹ := hinner _ hzq
    have h2 : b * (q * z * q⁻¹) * b⁻¹ = z := by
      calc b * (q * z * q⁻¹) * b⁻¹ = b * (b * z * b⁻¹) * b⁻¹ := by rw [hinner z hz]
        _ = z := by rw [show b * (b * z * b⁻¹) * b⁻¹ = (b * b) * z * (b⁻¹ * b⁻¹) by group,
              hb2, hbinv, hb2]; simp
    have h3 : q * (q * z * q⁻¹) * q⁻¹ = (q * q) * z * (q * q)⁻¹ := by group
    have h4 : (q * q) * z * (q * q)⁻¹ = z := by rw [← h3, ← h1, h2]
    calc (q * q) * z = ((q * q) * z * (q * q)⁻¹) * (q * q) := by group
      _ = z * (q * q) := by rw [h4]
  have hq2center : (⟨q * q, Q.mul_mem hqQ hqQ⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (hq2comm (y : G) y.2).symm
  have hdvd : orderOf (q * q) ∣ Nat.card (Subgroup.center ↥Q) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Q) hq2center
    rwa [← Subgroup.orderOf_coe (⟨q * q, Q.mul_mem hqQ hqQ⟩ : ↥Q)] at h
  have hnodd : Odd (orderOf (q * q)) := hQodd.of_dvd_nat hdvd
  have hbMapQ : ∀ y ∈ Q, MulAut.conj b y ∈ Q := by
    intro y hy
    rw [MulAut.conj_apply, hinner y hy]
    exact Q.mul_mem (Q.mul_mem hqQ hy) (Q.inv_mem hqQ)
  have hbpowQ : ∀ m : ℕ, ∀ z ∈ Q, (MulAut.conj b ^ m) z ∈ Q := by
    intro m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
        intro z hz
        rw [pow_succ', MulAut.mul_apply]
        exact hbMapQ _ (ih z hz)
  have hpow : ∀ m : ℕ, ∀ z ∈ Q, (MulAut.conj q ^ m) z = (MulAut.conj b ^ m) z := by
    intro m
    induction m with
    | zero => intro z hz; simp
    | succ m ih =>
        intro z hz
        have hwQ : (MulAut.conj b ^ m) z ∈ Q := hbpowQ m z hz
        calc (MulAut.conj q ^ (m + 1)) z
            = MulAut.conj q ((MulAut.conj q ^ m) z) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = MulAut.conj q ((MulAut.conj b ^ m) z) := by rw [ih z hz]
          _ = MulAut.conj b ((MulAut.conj b ^ m) z) := by
              rw [MulAut.conj_apply, MulAut.conj_apply]
              exact (hinner _ hwQ).symm
          _ = (MulAut.conj b ^ (m + 1)) z := by
              rw [pow_succ', MulAut.mul_apply]
  let e : G := q ^ orderOf (q * q)
  have heQ : e ∈ Q := Q.pow_mem hqQ _
  have hee : e * e = 1 := by
    change q ^ orderOf (q * q) * q ^ orderOf (q * q) = 1
    rw [← pow_add, show orderOf (q * q) + orderOf (q * q) = 2 * orderOf (q * q) by omega,
      pow_mul, pow_two]
    exact pow_orderOf_eq_one (q * q)
  have hbpow : MulAut.conj b ^ orderOf (q * q) = MulAut.conj b := by
    obtain ⟨k, hk⟩ := hnodd
    have hb2pow : b ^ 2 = 1 := by rw [pow_two]; exact hb2
    have hf2 : MulAut.conj b ^ 2 = 1 := by
      rw [← map_pow (MulAut.conj) b 2, hb2pow, map_one]
    rw [hk, pow_succ, pow_mul, hf2, one_pow, one_mul]
  have hconjq : MulAut.conj e = MulAut.conj q ^ orderOf (q * q) := by
    change MulAut.conj (q ^ orderOf (q * q)) = _
    rw [map_pow]
  have heact : ∀ z ∈ Q, e * z * e⁻¹ = b * z * b⁻¹ := by
    intro z hz
    have h1 := hpow (orderOf (q * q)) z hz
    rw [← hconjq, hbpow] at h1
    simpa [MulAut.conj_apply] using h1
  by_cases he1 : e = 1
  · right
    intro z hz
    have h := heact z hz
    rw [he1] at h
    simpa using h.symm
  · left
    refine ⟨e, heQ, ?_, heact⟩
    exact orderOf_eq_prime (by rwa [pow_two]) he1

private theorem exists_elemAbelian_eight_of_inner {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b : G} (hb2 : b * b = 1)
    (hInner : ∃ q ∈ Q, ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹) :
    ∃ F : Subgroup G, F ≤ centralizer (P : Set G) ∧ F ≤ centralizer ({b} : Set G) ∧
      Open.IsElemAbelian 2 F ∧ 8 ≤ Nat.card F := by
  obtain ⟨q, hqQ, hqconj⟩ := hInner
  have hQleCP : Q ≤ centralizer (P : Set G) := le_centralizer_iff.mp hcfg.le_centralizer
  have hcenter : Odd (Nat.card (center ↥Q)) := hcfg.odd_card_center_right
  have hQ : IsQuasisimple ↥Q := hcfg.isQuasisimple_right
  have hQL : IsL34Type (↥Q ⧸ center ↥Q) := hcfg.isL34Type_right
  rcases exists_involution_conj_eq_or_fixed (Q := Q) hb2 hcenter hqQ hqconj with
    ⟨e, heQ, he2, heact⟩ | hfix
  · obtain ⟨E, hE, -, hEea, hEcard⟩ := exists_elemAbelian_sixteen_of_l34Odd hQ hcenter hQL heQ he2
    have hEP : E ≤ centralizer (P : Set G) := hE.trans (inf_le_left.trans hQleCP)
    have hEb : E ≤ centralizer ({b} : Set G) := by
      intro z hz
      have hzQ : z ∈ Q := (mem_inf.mp (hE hz)).1
      have hze : z * e = e * z := mem_centralizer_singleton_iff.mp (mem_inf.mp (hE hz)).2
      have hzconj : e * z * e⁻¹ = z := by
        calc e * z * e⁻¹ = (z * e) * e⁻¹ := by rw [hze]
          _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]
      have hbz : b * z * b⁻¹ = z := by rw [← heact z hzQ, hzconj]
      exact mem_centralizer_singleton_iff.mpr (by
        calc z * b = (b * z * b⁻¹) * b := by rw [hbz]
          _ = b * z := by group)
    exact ⟨E, hEP, hEb, hEea, by rw [hEcard]; norm_num⟩
  · obtain ⟨e, heQ, he2⟩ := exists_involution_mem_of_l34Odd hQ hcenter hQL
    obtain ⟨E, hE, -, hEea, hEcard⟩ := exists_elemAbelian_sixteen_of_l34Odd hQ hcenter hQL heQ he2
    have hEP : E ≤ centralizer (P : Set G) := hE.trans (inf_le_left.trans hQleCP)
    have hEb : E ≤ centralizer ({b} : Set G) := by
      intro z hz
      have hzQ : z ∈ Q := (mem_inf.mp (hE hz)).1
      have hbz : b * z * b⁻¹ = z := hfix z hzQ
      exact mem_centralizer_singleton_iff.mpr (by
        calc z * b = (b * z * b⁻¹) * b := by rw [hbz]
          _ = b * z := by group)
    exact ⟨E, hEP, hEb, hEea, by rw [hEcard]; norm_num⟩

private theorem not_mem_closure_pair_of_outer {Q : Subgroup G} {b r x : G}
    (hOuter : ¬ ∃ q ∈ Q, ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹)
    (hb1 : b ≠ 1) (hr2 : r * r = 1) (hx2 : x * x = 1) (hrx : r * x = x * r)
    (hr1 : r ≠ 1) (hx1 : x ≠ 1) (hne : x ≠ r)
    (hrQ : r ∈ centralizer (Q : Set G)) (hxQ : x ∈ Q) :
    b ∉ Subgroup.closure ({r, x} : Set G) := by
  intro hbN
  have hNset : (Subgroup.closure ({r, x} : Set G) : Set G) = {1, r, x, r * x} :=
    CFSG.GroupTheory.coe_closure_pair_eq hr2 hx2 hrx hr1 hx1 hne.symm
  change b ∈ (Subgroup.closure ({r, x} : Set G) : Set G) at hbN
  rw [hNset] at hbN
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbN
  rcases hbN with hb | hb | hb | hb
  · exact hb1 hb
  · refine hOuter ⟨1, Q.one_mem, fun z hz => ?_⟩
    rw [hb]
    have hzr : z * r = r * z := Subgroup.mem_centralizer_iff.mp hrQ z hz
    calc r * z * r⁻¹ = (z * r) * r⁻¹ := by rw [hzr]
      _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = 1 * z * 1⁻¹ := by simp
  · refine hOuter ⟨x, hxQ, fun z hz => ?_⟩
    rw [hb]
  · refine hOuter ⟨x, hxQ, fun z hz => ?_⟩
    rw [hb]
    have hrz : r * (x * z * x⁻¹) = (x * z * x⁻¹) * r := by
      have hxzx : x * z * x⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hxQ hz) (Q.inv_mem hxQ)
      exact (Subgroup.mem_centralizer_iff.mp hrQ _ hxzx).symm
    calc (r * x) * z * (r * x)⁻¹ = r * (x * z * x⁻¹) * r⁻¹ := by group
      _ = (x * z * x⁻¹) * r * r⁻¹ := by rw [hrz]
      _ = x * z * x⁻¹ := by group

private theorem exists_elemAbelian_eight_of_three {P Q : Subgroup G} {b r x : G}
    (hbP : b ∈ centralizer (P : Set G)) (hrP : r ∈ centralizer (P : Set G))
    (hxQ : x ∈ Q) (hQleCP : Q ≤ centralizer (P : Set G))
    (hb2 : b * b = 1) (hr2 : r * r = 1) (hx2 : x * x = 1)
    (hbr : r * b = b * r) (hbx : x * b = b * x) (hrx : r * x = x * r)
    (hb1 : b ≠ 1) (hr1 : r ≠ 1) (hx1 : x ≠ 1) (hne : x ≠ r)
    (hrQ : r ∈ centralizer (Q : Set G))
    (hOuter : ¬ ∃ q ∈ Q, ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹) :
    ∃ F : Subgroup G, F ≤ centralizer (P : Set G) ∧ F ≤ centralizer ({b} : Set G) ∧
      Open.IsElemAbelian 2 F ∧ 8 ≤ Nat.card F := by
  let N : Subgroup G := Subgroup.closure ({r, x} : Set G)
  let F : Subgroup G := Subgroup.closure ({b, r, x} : Set G)
  have hNcard : Nat.card N = 4 :=
    CFSG.GroupTheory.card_closure_pair_of_involutions hr2 hx2 hrx hr1 hx1 hne
  have hNnorm : b ∈ Subgroup.normalizer (N : Set G) := by
    have hbCent : b ∈ Subgroup.centralizer (N : Set G) := by
      change b ∈ Subgroup.centralizer (Subgroup.closure ({r, x} : Set G) : Set G)
      rw [Subgroup.centralizer_closure]
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hbr
      · exact hbx
    exact Subgroup.centralizer_le_normalizer _ hbCent
  have hbN : b ∉ N :=
    not_mem_closure_pair_of_outer (Q := Q) hOuter hb1 hr2 hx2 hrx hr1 hx1 hne hrQ hxQ
  have hcardSup : Nat.card ↥(N ⊔ Subgroup.zpowers b) = 2 * Nat.card N :=
    CFSG.GroupTheory.card_sup_zpowers_of_sq_mem hNnorm (by rw [hb2]; exact N.one_mem) hbN
  have hleF : N ⊔ Subgroup.zpowers b ≤ F := by
    apply sup_le
    · exact Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hcardF : 8 ≤ Nat.card F := by
    have hle := Subgroup.card_le_of_le hleF
    rw [hNcard] at hcardSup
    omega
  have hFelem : Open.IsElemAbelian 2 F := by
    refine Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hc
      rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
      · rfl
      · exact hbr.symm
      · exact hbx.symm
      · exact hbr
      · rfl
      · exact hrx
      · exact hbx
      · exact hrx.symm
      · rfl
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · rw [pow_two]; exact hb2
      · rw [pow_two]; exact hr2
      · rw [pow_two]; exact hx2
  have hFP : F ≤ centralizer (P : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hbP
    · exact hrP
    · exact hQleCP hxQ
  have hFb : F ≤ centralizer ({b} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact mem_centralizer_singleton_iff.mpr hbr
    · exact mem_centralizer_singleton_iff.mpr hbx
  exact ⟨F, hFP, hFb, hFelem, hcardF⟩

private theorem exists_elemAbelian_eight_of_outer {V P Q : Subgroup G}
    (hcfg : L34PartnerConfig V P Q) {b : G} (hb : orderOf b = 2)
    (hbP : b ∈ centralizer (P : Set G)) (hbQ : Q.map (MulAut.conj b).toMonoidHom = Q)
    (hOuter : ¬ ∃ q ∈ Q, ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹) :
    ∃ F : Subgroup G, F ≤ centralizer (P : Set G) ∧ F ≤ centralizer ({b} : Set G) ∧
      Open.IsElemAbelian 2 F ∧ 8 ≤ Nat.card F := by
  have hb2 : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two hb
  have hQleCP : Q ≤ centralizer (P : Set G) := le_centralizer_iff.mp hcfg.le_centralizer
  obtain ⟨x, hxcomm, hx2⟩ :=
    exists_involution_mem_commutator_inf_centralizer_of_l34Odd hcfg.isQuasisimple_right
      hcfg.odd_card_center_right hcfg.isL34Type_right hb hbQ
  have hxH : x ∈ Q ⊓ centralizer ({b} : Set G) :=
    Subgroup.commutator_le_of_le le_rfl le_rfl hxcomm
  have hxQ : x ∈ Q := (mem_inf.mp hxH).1
  have hbx : x * b = b * x := mem_centralizer_singleton_iff.mp (mem_inf.mp hxH).2
  let X : Subgroup G := centralizer (P : Set G) ⊓ centralizer (Q : Set G)
  have hVX : V ≤ X := le_inf hcfg.le_centralizer_left hcfg.le_centralizer_right
  have hEvenX : Even (Nat.card X) := by
    have h4 : 4 ∣ Nat.card X := by
      have h := Subgroup.card_dvd_of_le hVX
      rwa [hcfg.card_V] at h
    exact even_iff_two_dvd.mpr (dvd_trans (by norm_num) h4)
  have hbNX : b ∈ Subgroup.normalizer (X : Set G) := by
    have hbPnorm : b ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.centralizer_le_normalizer (P : Set G) hbP
    have hbQnorm : b ∈ Subgroup.normalizer (Q : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbQ
    have hbCP : b ∈ Subgroup.normalizer (centralizer (P : Set G) : Set G) :=
      CFSG.ComponentClassification.AS76b.Lemma22.normalizer_le_normalizer_centralizer P hbPnorm
    have hbCQ : b ∈ Subgroup.normalizer (centralizer (Q : Set G) : Set G) :=
      CFSG.ComponentClassification.AS76b.Lemma22.normalizer_le_normalizer_centralizer Q hbQnorm
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hbCP, hbCQ⟩
  obtain ⟨r, hrX, hr2, hbr⟩ :=
    CFSG.ComponentClassification.AS76b.Lemma34.exists_involution_commute hb2 hbNX hEvenX
  have hrP : r ∈ centralizer (P : Set G) := (mem_inf.mp hrX).1
  have hrQ : r ∈ centralizer (Q : Set G) := (mem_inf.mp hrX).2
  have hrNotQ : r ∉ Q := by
    intro hrQmem
    have hrCenter : (⟨r, hrQmem⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hrQ (y : G) y.2
    have hdvd : orderOf r ∣ Nat.card (Subgroup.center ↥Q) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥Q) hrCenter
      rwa [← Subgroup.orderOf_coe (⟨r, hrQmem⟩ : ↥Q)] at h
    rw [hr2] at hdvd
    exact hcfg.odd_card_center_right.not_two_dvd_nat hdvd
  have hr2m : r * r = 1 := mul_self_eq_one_of_orderOf_eq_two hr2
  have hx2m : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2
  have hr1 : r ≠ 1 := by rintro rfl; norm_num at hr2
  have hx1 : x ≠ 1 := by rintro rfl; norm_num at hx2
  have hb1 : b ≠ 1 := by rintro rfl; norm_num at hb
  have hne : x ≠ r := by intro h; exact hrNotQ (h ▸ hxQ)
  have hrx : r * x = x * r := (Subgroup.mem_centralizer_iff.mp hrQ x hxQ).symm
  exact exists_elemAbelian_eight_of_three (Q := Q) hbP hrP hxQ hQleCP hb2 hr2m hx2m hbr hbx
    hrx hb1 hr1 hx1 hne hrQ hOuter

theorem exists_elemAbelian_eight_of_mem_normalizer_of_l34PartnerConfig
    {V P Q : Subgroup G} (hcfg : L34PartnerConfig V P Q) {b : G} (hb : orderOf b = 2)
    (hbP : b ∈ centralizer (P : Set G)) (hbQ : Q.map (MulAut.conj b).toMonoidHom = Q) :
    ∃ F : Subgroup G, F ≤ centralizer (P : Set G) ∧ F ≤ centralizer ({b} : Set G) ∧
      Open.IsElemAbelian 2 F ∧ 8 ≤ Nat.card F := by
  have hb2 : b * b = 1 := mul_self_eq_one_of_orderOf_eq_two hb
  by_cases hInner : ∃ q ∈ Q, ∀ z ∈ Q, b * z * b⁻¹ = q * z * q⁻¹
  · exact exists_elemAbelian_eight_of_inner hcfg hb2 hInner
  · exact exists_elemAbelian_eight_of_outer hcfg hb hbP hbQ hInner

end CFSG.ComponentClassification.GrSLit.L34Sec5S
