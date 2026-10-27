module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma96B

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9.L96

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_sq_eq_one {q : ℕ} (hq2 : q ≠ 2) (hq : q.Prime) {a : G} (h2 : a ^ 2 = 1)
    (hq1 : a ^ q = 1) : a = 1 := by
  obtain ⟨m, hm⟩ := hq.odd_of_ne_two hq2
  have : a ^ q = a := by
    rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul]
  rw [← this]; exact hq1

theorem inverts_of_inf_centralizer_eq_bot {A : Subgroup G} {t : G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (ht : t ∈ Subgroup.normalizer (A : Set G))
    (ht2 : t ^ 2 = 1) (h : A ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    ∀ a ∈ A, t * a * t⁻¹ = a⁻¹ := by
  intro a ha
  have ha' : t * a * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 ht a).1 ha
  have hy : a * (t * a * t⁻¹) ∈ A ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨A.mul_mem ha ha', Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    rw [Set.mem_singleton_iff] at hh; rw [hh]
    have hsq : t * t = 1 := by rw [← sq]; exact ht2
    calc t * (a * (t * a * t⁻¹)) = (t * a * t⁻¹) * (t * (t * a * t⁻¹ ) * t⁻¹ ) * t := by group
      _ = (t * a * t⁻¹) * a * t := by
        have : t * (t * a * t⁻¹) * t⁻¹ = a := by
          calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ := by group
            _ = a := by rw [hsq]; group
        rw [this]
      _ = a * (t * a * t⁻¹) * t := by rw [hAc _ ha' _ ha]
  rw [h, Subgroup.mem_bot] at hy
  exact eq_inv_of_mul_eq_one_right hy

theorem exists_fixed_by_four_group {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {A₀ U : Subgroup G}
    (hab : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) (hexp : ∀ a ∈ A₀, a ^ q = 1) (hne : A₀ ≠ ⊥)
    (hU : IsElemAbelian 2 U) (hUc : Nat.card U = 4) (hUN : U ≤ Subgroup.normalizer (A₀ : Set G)) :
    ∃ t ∈ U, t ≠ 1 ∧ A₀ ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥ := by
  by_contra hcon
  have hall : ∀ t ∈ U, t ≠ 1 → ∀ a ∈ A₀, t * a * t⁻¹ = a⁻¹ := by
    intro t htU ht1
    have hbot : A₀ ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
      by_contra hb
      exact hcon ⟨t, htU, ht1, hb⟩
    exact inverts_of_inf_centralizer_eq_bot hab (hUN htU) (by simpa using hU.2 t htU) hbot
  have hU1 : (⊥ : Subgroup G) ≠ U := by
    intro h; rw [← h, Subgroup.card_bot] at hUc; omega
  obtain ⟨t₁, ht₁U, ht₁⟩ : ∃ t ∈ U, t ≠ 1 := by
    by_contra h
    push Not at h
    exact hU1 (eq_bot_iff.2 (fun g hg => (Subgroup.mem_bot).2 (h g hg))).symm
  have hZ1 : Subgroup.zpowers t₁ ≠ U := by
    intro h
    have : Nat.card (Subgroup.zpowers t₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by simpa using hU.2 t₁ ht₁U) ht₁
    rw [h, hUc] at this; omega
  have hle : Subgroup.zpowers t₁ ≤ U := Subgroup.zpowers_le.2 ht₁U
  obtain ⟨t₂, ht₂U, ht₂Z⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hZ1)
  have ht₂1 : t₂ ≠ 1 := fun h => ht₂Z (h ▸ (Subgroup.zpowers t₁).one_mem)
  have ht₁₂ : t₁ * t₂ ≠ 1 := by
    intro h
    apply ht₂Z
    have h1 : t₂ = t₁⁻¹ := by
      have := congrArg (fun y => t₁⁻¹ * y) h
      simpa using this
    have h2 : t₁ ^ 2 = 1 := by simpa using hU.2 t₁ ht₁U
    have h3 : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact h2)
    rw [h1, h3]; exact Subgroup.mem_zpowers t₁
  apply hne
  rw [eq_bot_iff]
  intro a ha
  have e1 := hall t₁ ht₁U ht₁ a ha
  have e2 := hall t₂ ht₂U ht₂1 a ha
  have ha' : t₂ * a * t₂⁻¹ ∈ A₀ := (Subgroup.mem_normalizer_iff.1 (hUN ht₂U) a).1 ha
  have e3 := hall (t₁ * t₂) (U.mul_mem ht₁U ht₂U) ht₁₂ a ha
  have e4 : t₁ * t₂ * a * (t₁ * t₂)⁻¹ = a := by
    calc t₁ * t₂ * a * (t₁ * t₂)⁻¹ = t₁ * (t₂ * a * t₂⁻¹) * t₁⁻¹ := by group
      _ = t₁ * a⁻¹ * t₁⁻¹ := by rw [e2]
      _ = (t₁ * a * t₁⁻¹)⁻¹ := by group
      _ = a := by rw [e1]; simp
  have e5 : a = a⁻¹ := by rw [← e3, e4] 
  have e6 : a ^ 2 = 1 := by
    rw [sq]; nth_rewrite 1 [e5]; exact inv_mul_cancel a
  exact (Subgroup.mem_bot).2 (eq_one_of_sq_eq_one hq2 hq e6 (hexp a ha))

theorem inf_centralizer_eq_bot_of_commutator {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G}
    {z : G} (hz2 : z ^ 2 = 1) (hzN : z ∈ Subgroup.normalizer (Q : Set G))
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hexp : ∀ a ∈ Q, a ^ q = 1)
    (hcomm : (⁅Q, Subgroup.zpowers z⁆ : Subgroup G) = Q) :
    Q ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ := by
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  let D : Subgroup G :=
    { carrier := {y | y ∈ Q ∧ z * y * z⁻¹ = y⁻¹}
      one_mem' := ⟨Q.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haQ, ha⟩ ⟨hbQ, hb⟩
        refine ⟨Q.mul_mem haQ hbQ, ?_⟩
        calc z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha, hb]
          _ = (a * b)⁻¹ := by rw [mul_inv_rev, hab _ (Q.inv_mem haQ) _ (Q.inv_mem hbQ)]
      inv_mem' := by
        rintro a ⟨haQ, ha⟩
        refine ⟨Q.inv_mem haQ, ?_⟩
        calc z * a⁻¹ * z⁻¹ = (z * a * z⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [ha] }
  have hQD : Q ≤ D := by
    rw [← hcomm]
    refine Subgroup.commutator_le.2 (fun a ha k hk => ?_)
    have haN : z * a * z⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.1 hzN a).1 ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : z ^ (j + j) = 1 := by
        rw [← two_mul, zpow_mul]; simp [hz2]
      rw [this]
      have h1 : ⁅a, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
      rw [h1]; exact D.one_mem
    · have : z ^ (2 * j + 1) = z := by
        rw [zpow_add, zpow_mul]; simp [hz2]
      rw [this]
      have hcomm' : ⁅a, z⁆ = a * (z * a * z⁻¹)⁻¹ := by
        simp only [commutatorElement_def]; group
      refine ⟨by rw [hcomm']; exact Q.mul_mem ha (Q.inv_mem haN), ?_⟩
      rw [hcomm']
      have hzaz : z * (z * a * z⁻¹) * z⁻¹ = a := by
        calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
          _ = a := by rw [hzz]; group
      calc z * (a * (z * a * z⁻¹)⁻¹) * z⁻¹
          = (z * a * z⁻¹) * (z * (z * a * z⁻¹) * z⁻¹)⁻¹ := by group
        _ = (z * a * z⁻¹) * a⁻¹ := by rw [hzaz]
        _ = (a * (z * a * z⁻¹)⁻¹)⁻¹ := by group
  rw [eq_bot_iff]
  intro c hc
  have h1 := (hQD hc.1).2
  have h2 : z * c * z⁻¹ = c := by
    have := Subgroup.mem_centralizer_iff.1 hc.2 z (Set.mem_singleton z)
    rw [this]; group
  have h3 : c = c⁻¹ := by rw [← h1, h2]
  have h4 : c ^ 2 = 1 := by
    rw [sq]; nth_rewrite 1 [h3]; exact inv_mul_cancel c
  exact (Subgroup.mem_bot).2 (eq_one_of_sq_eq_one hq2 hq h4 (hexp c hc.1))

theorem five_le_pRank_of_disjoint {q : ℕ} (hq : q.Prime) {D W R : Subgroup G}
    (hD : IsElemAbelian q D) (hWD : W ≤ D) (hRD : R ≤ D) (hW : W ≠ ⊥) (hWR : W ⊓ R = ⊥)
    (hR : q ^ 4 ≤ Nat.card R) : 5 ≤ CFSG.Open.pRank q D := by
  have hprod := card_sup_mul_card_inf_of_le_elemAbelian hD hWD hRD
  rw [hWR, Subgroup.card_bot, mul_one] at hprod
  have hWcard : q ≤ Nat.card W := by
    obtain ⟨j, hj⟩ := exists_card_eq_pow_of_isElemAbelian hq (isElemAbelian_mono hD hWD)
    have hj0 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hj
      exact hW (Subgroup.eq_bot_of_card_eq _ hj)
    rw [hj]
    exact Nat.le_self_pow hj0 q
  have hE : q ^ 5 ≤ Nat.card ↥(W ⊔ R) := by
    rw [hprod]
    calc q ^ 5 = q * q ^ 4 := by ring
      _ ≤ Nat.card W * Nat.card R := Nat.mul_le_mul hWcard hR
  obtain ⟨i, hi⟩ := exists_card_eq_pow_of_isElemAbelian hq
    (isElemAbelian_mono hD (sup_le hWD hRD))
  have hi5 : 5 ≤ i := by
    rw [hi] at hE
    exact (Nat.pow_le_pow_iff_right hq.one_lt).1 hE
  exact hi5.trans (CFSG.SectionRank.le_pRank hq.one_lt (sup_le hWD hRD)
    (isElemAbelian_mono hD (sup_le hWD hRD)) hi)

theorem normalizer_le_normalizer_center (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∀ a ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
      g * a * g⁻¹ ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    intro g hg a ha
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg a).1 ha.1, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    have hh' : g⁻¹ * h * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) h).1 hh
      simpa using this
    have := Subgroup.mem_centralizer_iff.1 ha.2 _ hh'
    calc h * (g * a * g⁻¹) = g * ((g⁻¹ * h * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * h * g)) * g⁻¹ := by rw [this]
      _ = g * a * g⁻¹ * h := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  exact ⟨fun ha => key g hg a ha, fun ha => by
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ ha
    simpa [mul_assoc] using this⟩

theorem inf_centralizer_le_core {p : ℕ} (hp : p.Prime) {X L A : Subgroup G}
    (hL : GLAPComponent p X L) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p L)))
    (hZ : Subgroup.center (PQuot p L) = ⊥) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hnc : ¬ L ≤ Subgroup.centralizer (A : Set G)) :
    L ⊓ Subgroup.centralizer (A : Set G) ≤ GLAPPrimeCoreOf p L := by
  classical
  haveI hKnormal : ((L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf L).Normal :=
    normal_inf_centralizer hLA
  set Og : Subgroup ↥L := GLAPPrimeCore p ↥L with hOg
  set Kg : Subgroup ↥L := (L ⊓ Subgroup.centralizer (A : Set G)).subgroupOf L with hKg
  have hKO : Kg ≤ Og := by
    have hq : CFSG.Open.IsQuasisimple (PQuot p L) := isQuasisimple_pQuot_of_glaPComponent hp hL
    have hs : IsSimpleGroup (PQuot p L ⧸ Subgroup.center (PQuot p L)) := hq.2
    set π₂ : ↥L →* (PQuot p L ⧸ Subgroup.center (PQuot p L)) :=
      (QuotientGroup.mk' (Subgroup.center (PQuot p L))).comp (QuotientGroup.mk' Og) with hπ₂
    have hπ₂ker : π₂.ker = Og := by
      ext g
      rw [MonoidHom.mem_ker, hπ₂, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have hπ₂surj : Function.Surjective π₂ :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hKbar : (Kg.map π₂).Normal := Subgroup.Normal.map hKnormal π₂ hπ₂surj
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (Kg.map π₂) hKbar with h | h
    · rwa [Subgroup.map_eq_bot_iff, hπ₂ker] at h
    · exfalso
      have hsup : Kg ⊔ Og = ⊤ := by
        have := Subgroup.comap_map_eq π₂ Kg
        rwa [h, Subgroup.comap_top, hπ₂ker, eq_comm] at this
      have hOgcard : Nat.card ↥Og = Nat.card (GLAPPrimeCoreOf p L) := by
        rw [GLAPPrimeCoreOf]
        exact (Subgroup.card_map_of_injective L.subtype_injective).symm
      haveI hOgsolv : Group.IsSolvable ↥Og :=
        CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hOgcard ▸ hodd)
      set f : ↥Og →* (↥L ⧸ Kg) := (QuotientGroup.mk' Kg).comp Og.subtype with hf
      have hfsurj : Function.Surjective f := by
        intro y
        induction y using QuotientGroup.induction_on with
        | H g =>
          have hg : g ∈ Kg ⊔ Og := by rw [hsup]; exact Subgroup.mem_top g
          obtain ⟨k, hk, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
          refine ⟨⟨o, ho⟩, ?_⟩
          rw [hf, MonoidHom.comp_apply]
          change (QuotientGroup.mk' Kg) o = (QuotientGroup.mk' Kg) (k * o)
          have hk1 : (QuotientGroup.mk' Kg) k = 1 := (QuotientGroup.eq_one_iff k).2 hk
          rw [map_mul, hk1, one_mul]
      haveI : Group.IsSolvable (↥L ⧸ Kg) := Group.isSolvable_of_surjective hfsurj
      have hperf : (commutator (↥L ⧸ Kg)) = ⊤ := by
        have h1 : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) = ⊤ := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
          exact glaPComponent_perfect hL
        have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) (QuotientGroup.mk' Kg)
        rw [h1, Subgroup.map_top, MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective Kg)] at h2
        rw [commutator_def]
        exact h2.symm
      have htriv : Subsingleton (↥L ⧸ Kg) := by
        by_contra hns
        haveI : Nontrivial (↥L ⧸ Kg) := not_subsingleton_iff_nontrivial.1 hns
        exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (↥L ⧸ Kg)).ne hperf
      have hKtop : Kg = ⊤ := by
        rw [eq_top_iff]
        intro g _
        have : (QuotientGroup.mk g : ↥L ⧸ Kg) = QuotientGroup.mk 1 := Subsingleton.elim _ _
        rw [QuotientGroup.eq] at this
        simpa using this
      apply hnc
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ Kg := by rw [hKtop]; exact Subgroup.mem_top _
      rw [hKg, Subgroup.mem_subgroupOf] at this
      exact this.2
  intro k hk
  have : (⟨k, hk.1⟩ : ↥L) ∈ Kg := by
    rw [hKg, Subgroup.mem_subgroupOf]; exact hk
  obtain ⟨o, ho, hok⟩ := Subgroup.mem_map.1 (Subgroup.mem_map_of_mem L.subtype (hKO this))
  exact ⟨o, ho, hok⟩

theorem mem_core_of_mem_coreOf {p : ℕ} {L : Subgroup G} {k : G} (hkL : k ∈ L)
    (hk : k ∈ GLAPPrimeCoreOf p L) : (⟨k, hkL⟩ : ↥L) ∈ GLAPPrimeCore p ↥L := by
  obtain ⟨o, ho, hok⟩ := Subgroup.mem_map.1 hk
  have : o = ⟨k, hkL⟩ := Subtype.ext hok
  rwa [← this]

theorem not_inverts {p : ℕ} (hp : p.Prime) {X L A : Subgroup G} (hL : GLAPComponent p X L)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p L))) (hZ : Subgroup.center (PQuot p L) = ⊥)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hnc : ¬ L ≤ Subgroup.centralizer (A : Set G))
    {z : G} (hzL : z ∈ L) (hzO : z ∉ GLAPPrimeCoreOf p L) :
    ¬ ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ := by
  intro hinv
  have hcore := inf_centralizer_le_core hp hL hodd hZ hLA hnc
  apply hzO
  have hinv' : ∀ a ∈ A, z⁻¹ * a * z = a⁻¹ := by
    intro a ha
    have hb : z⁻¹ * a * z ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (hLA (L.inv_mem hzL)) a).1 ha
      simpa using this
    have h1 := hinv _ hb
    have h2 : z * (z⁻¹ * a * z) * z⁻¹ = a := by group
    rw [h2] at h1
    exact inv_eq_iff_eq_inv.1 h1.symm
  have hcentral : QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨z, hzL⟩ ∈ Subgroup.center (PQuot p L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H l =>
      have hlL : (l : G) ∈ L := l.2
      have hconj : ∀ a ∈ A, ((l : G)⁻¹ * z * l) * a * ((l : G)⁻¹ * z * l)⁻¹ = a⁻¹ := by
        intro a ha
        have ha' : (l : G) * a * (l : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hLA hlL) a).1 ha
        have h1 := hinv _ ha'
        calc ((l : G)⁻¹ * z * l) * a * ((l : G)⁻¹ * z * l)⁻¹
            = (l : G)⁻¹ * (z * ((l : G) * a * (l : G)⁻¹) * z⁻¹) * l := by group
          _ = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹)⁻¹ * l := by rw [h1]
          _ = a⁻¹ := by group
      have hcA : (l : G)⁻¹ * z * l * z⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
        refine Subgroup.mem_centralizer_iff.2 (fun a ha => ?_)
        have e1 := hconj a ha
        have e2 := hinv' a ha
        have : ((l : G)⁻¹ * z * l * z⁻¹) * a * ((l : G)⁻¹ * z * l * z⁻¹)⁻¹ = a := by
          calc ((l : G)⁻¹ * z * l * z⁻¹) * a * ((l : G)⁻¹ * z * l * z⁻¹)⁻¹
              = ((l : G)⁻¹ * z * l) * (z⁻¹ * a * z) * ((l : G)⁻¹ * z * l)⁻¹ := by group
            _ = ((l : G)⁻¹ * z * l) * a⁻¹ * ((l : G)⁻¹ * z * l)⁻¹ := by rw [e2]
            _ = (((l : G)⁻¹ * z * l) * a * ((l : G)⁻¹ * z * l)⁻¹)⁻¹ := by group
            _ = a := by rw [e1]; simp
        have h3 : a * ((l : G)⁻¹ * z * l * z⁻¹) = ((l : G)⁻¹ * z * l * z⁻¹) * a := by
          have := congrArg (fun y => y * ((l : G)⁻¹ * z * l * z⁻¹)) this
          calc a * ((l : G)⁻¹ * z * l * z⁻¹)
              = (((l : G)⁻¹ * z * l * z⁻¹) * a * ((l : G)⁻¹ * z * l * z⁻¹)⁻¹) * ((l : G)⁻¹ * z * l * z⁻¹) := by rw [this]
            _ = ((l : G)⁻¹ * z * l * z⁻¹) * a := by group
        exact h3
      have hcL : (l : G)⁻¹ * z * l * z⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem hlL) hzL) hlL) (L.inv_mem hzL)
      have hcO := mem_core_of_mem_coreOf hcL (hcore ⟨hcL, hcA⟩)
      change (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) l *
          (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) ⟨z, hzL⟩ =
        (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) ⟨z, hzL⟩ * (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) l
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have hN := (inferInstance : (GLAPPrimeCore p ↥L).Normal).conj_mem _ hcO
        (⟨z, hzL⟩ : ↥L)⁻¹
      have : (l * (⟨z, hzL⟩ : ↥L))⁻¹ * ((⟨z, hzL⟩ : ↥L) * l) =
          (⟨z, hzL⟩ : ↥L)⁻¹ * (⟨(l : G)⁻¹ * z * l * z⁻¹, hcL⟩ : ↥L) * ((⟨z, hzL⟩ : ↥L)⁻¹)⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, InvMemClass.coe_inv]
        group
      rw [this]; exact hN
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcentral
  exact Subgroup.mem_map_of_mem _ hcentral

theorem center_le_of_U5 {q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G 3)
    (hC : Contra92 3 B x L q Q₁) (h95 : GLATwoLocalRank q G ≤ GLATwoLocalRank 3 G)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 L))) (hB : Nat.card B = 3 ^ 4)
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) (hext : ExtraspecialU5D4At G)
    (hrep : ExtraspecialRepAt) (hL : catalogIs (PSimple 3 L) S9.isU5two) :
    Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) ≤ Subgroup.centralizer (L : Set G) := by
  by_contra hnot
  set A : Subgroup G := Q₁ ⊓ Subgroup.centralizer (Q₁ : Set G) with hA
  have hq := hC.setup.prime
  have hq2 := hC.setup.ne_two
  have hX : CFSG.Open.IsKGroup ↥(S9.cx x) := isKGroup_cx hc hC.h.ne_one
  have hm : GLATwoLocalRank 3 G = 4 := twoLocalRank_eq_four hC.h.bmax hB
  have hLN : L ≤ Subgroup.normalizer (Q₁ : Set G) := Subgroup.le_normalizer.trans hC.setup.char
  have hLA : L ≤ Subgroup.normalizer (A : Set G) := hLN.trans (normalizer_le_normalizer_center Q₁)
  have hnc : ¬ L ≤ Subgroup.centralizer (A : Set G) := by
    intro h
    apply hnot
    exact fun a ha => Subgroup.mem_centralizer_iff.2
      (fun l hl => (Subgroup.mem_centralizer_iff.1 (h hl) a ha).symm)
  obtain ⟨T, hTL, hT, U, hUT, hU, hUcard, hUZ⟩ := (hext (S9.cx x) L hX hC.h.comp hodd).1 hL
  obtain ⟨z, hzZ, hz1, hz2⟩ := exists_central_involution hT
  have hT2 : IsPGroup 2 T := hT.1.1
  have hTO : T ⊓ GLAPPrimeCoreOf 3 L = ⊥ := inf_core_eq_bot hodd hT2
  have hcoreA : L ⊓ Subgroup.centralizer (A : Set G) ≤ GLAPPrimeCoreOf 3 L :=
    inf_centralizer_le_core hc.ctx.prime hC.h.comp hodd hZ hLA hnc
  have hTA : T ⊓ Subgroup.centralizer (A : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ T ⊓ GLAPPrimeCoreOf 3 L := ⟨hg.1, hcoreA ⟨hTL hg.1, hg.2⟩⟩
    rw [hTO] at h1
    exact h1
  have hTNA : T ≤ Subgroup.normalizer (A : Set G) := hTL.trans hLA
  have hzL : z ∈ L := hTL hzZ.1
  have hzO : z ∉ GLAPPrimeCoreOf 3 L := fun h => hz1 (by
    have h1 : z ∈ T ⊓ GLAPPrimeCoreOf 3 L := ⟨hzZ.1, h⟩
    rw [hTO] at h1
    exact h1)
  have hninv := not_inverts hc.ctx.prime hC.h.comp hodd hZ hLA hnc hzL hzO
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 ha.2 b hb.1).symm
  have hAexp : ∀ a ∈ A, a ^ q = 1 := fun a ha => hC.setup.exp a ha.1
  have hAle : A ≤ Q₁ := inf_le_left
  set A₀ : Subgroup G := A ⊓ Subgroup.centralizer ({z} : Set G) with hA₀
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot
    exact hninv (inverts_of_inf_centralizer_eq_bot hAab (hTNA hzZ.1) hz2 hbot)
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (Subgroup.mem_centralizer_iff.1 hzZ.2 t ht).symm)
  have hUN₀ : U ≤ Subgroup.normalizer (A₀ : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.le_normalizer_inf (fun g hg => hTNA (hUT hg))
      (fun g hg => Subgroup.le_normalizer (hTz (hUT hg)))
  obtain ⟨t, htU, ht1, hW⟩ := exists_fixed_by_four_group hq hq2 (A₀ := A₀)
    (fun a ha b hb => hAab a ha.1 b hb.1) (fun a ha => hAexp a ha.1) hA₀ne hU hUcard hUN₀
  have htT : t ∈ T := hUT htU
  have ht2 : t ^ 2 = 1 := by simpa using hU.2 t htU
  have htZ : t ∉ T ⊓ Subgroup.centralizer (T : Set G) := fun h => ht1 (by
    have h1 : t ∈ U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨htU, h⟩
    rw [hUZ] at h1
    exact h1)
  have hne : (⁅A, Subgroup.zpowers z⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    have hzC : z ∈ T ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨hzZ.1, Subgroup.mem_centralizer_iff.2 (fun g hg => by
        have := Subgroup.mem_centralizer_iff.1 (h1 hg) z (Subgroup.mem_zpowers z)
        exact this.symm)⟩
    rw [hTA, Subgroup.mem_bot] at hzC
    exact hz1 hzC
  obtain ⟨Q₂, hQ₂le, hQ₂ne, hQ₂N, hQ₂eq, hmin⟩ :=
    exists_minimal_Q2 hq hq2 hzZ hz2 hAexp hTNA hne
  have hexp₂ : ∀ g ∈ Q₂, g ^ q = 1 := fun g hg => hAexp g (hQ₂le hg)
  have hQ₂ab : ∀ a ∈ Q₂, ∀ b ∈ Q₂, a * b = b * a := fun a ha b hb =>
    hAab a (hQ₂le ha) b (hQ₂le hb)
  have hcl₂ : ∀ a ∈ Q₂, ∀ b ∈ Q₂, ∀ c ∈ Q₂, ⁅a, b⁆ * c = c * ⁅a, b⁆ := by
    intro a ha b hb c hc
    have : ⁅a, b⁆ = 1 := by
      rw [commutatorElement_def, hQ₂ab a ha b hb]; group
    rw [this, one_mul, mul_one]
  obtain ⟨-, hCt⟩ := hrep G q 3 T Q₂ z hq hq2 hT hzZ hz1 hexp₂ hcl₂ hQ₂N hQ₂ne hQ₂eq hmin
  have h4 := hCt t htT ht2 htZ
  have hQ₂comm : (⁅Q₂, Q₂⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    exact Subgroup.mem_centralizer_iff.2 (fun b hb => hQ₂ab b hb a ha)
  have hRcard : Nat.card ↥(Q₂ ⊓ Subgroup.centralizer ({t} : Set G)) = q ^ 4 := by
    rw [h4, hQ₂comm, inf_bot_eq, Subgroup.card_bot]
    norm_num
  have hQ₂z : Q₂ ⊓ Subgroup.centralizer ({z} : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_commutator hq hq2 hz2 (hQ₂N hzZ.1) hQ₂ab hexp₂ hQ₂eq
  have hWR : (A₀ ⊓ Subgroup.centralizer ({t} : Set G)) ⊓
      (Q₂ ⊓ Subgroup.centralizer ({t} : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : g ∈ Q₂ ⊓ Subgroup.centralizer ({z} : Set G) := ⟨hg.2.1, hg.1.1.2⟩
    rw [hQ₂z] at h1
    exact h1
  have hD : IsElemAbelian q (A ⊓ Subgroup.centralizer ({t} : Set G)) :=
    ⟨⟨⟨fun a b => Subtype.ext (hAab a a.2.1 b b.2.1)⟩⟩, fun a ha => hAexp a ha.1⟩
  have hWD : A₀ ⊓ Subgroup.centralizer ({t} : Set G) ≤ A ⊓ Subgroup.centralizer ({t} : Set G) :=
    inf_le_inf_right _ inf_le_left
  have hRD : Q₂ ⊓ Subgroup.centralizer ({t} : Set G) ≤ A ⊓ Subgroup.centralizer ({t} : Set G) :=
    inf_le_inf_right _ hQ₂le
  have h5 := five_le_pRank_of_disjoint hq hD hWD hRD hW hWR (by rw [hRcard])
  have h6 := pRank_le_twoLocalRank_of_involution hq ht1 ht2
    (R := A ⊓ Subgroup.centralizer ({t} : Set G)) inf_le_right
  omega

end CFSG.LocalAnalysis.GLTheoremA.S9.L96
