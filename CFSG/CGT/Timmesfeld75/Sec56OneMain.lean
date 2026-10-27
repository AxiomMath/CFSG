module

public import CFSG.CGT.Timmesfeld75.Sec56OneNormal
public import CFSG.CGT.Timmesfeld75.Sec56OneCount
public import CFSG.CGT.Timmesfeld75.JLemmaGen
public import CFSG.CGT.Timmesfeld75.A6Klein
public import CFSG.CGT.Timmesfeld75.Sec57Basic
public import CFSG.CGT.Timmesfeld75.Sec5SixB

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G] {R T : Subgroup G}

theorem exists_mem_normalizer_conj_of_map (hT : IsWC T) (hTR : T ≤ R) {x₂ x₃ : G} (hx₂ : x₂ ∈ R)
    (hx₃ : x₃ ∈ R) {k : jQuot ↥R}
    (hk : conjSubgroup k ((T.subgroupOf R).map (jMap ↥R)) = (T.subgroupOf R).map (jMap ↥R))
    (hk₂ : conjSubgroup k (((conjSubgroup x₂ T).subgroupOf R).map (jMap ↥R)) =
      ((conjSubgroup x₃ T).subgroupOf R).map (jMap ↥R)) :
    ∃ r ∈ R, conjSubgroup r T = T ∧ conjSubgroup r (conjSubgroup x₂ T) = conjSubgroup x₃ T := by
  obtain ⟨r, rfl⟩ := jMap_surjective (R := ↥R) k
  have hconj : ∀ {c : G} (hc : c ∈ R), conjSubgroup (⟨c, hc⟩ : ↥R) (T.subgroupOf R) =
      (conjSubgroup c T).subgroupOf R := fun {c} hc => conjSubgroup_subgroupOf R T ⟨c, hc⟩
  have hwc := isWC_subgroupOf hT R hTR
  have e1 : conjSubgroup r (T.subgroupOf R) = conjSubgroup 1 (T.subgroupOf R) := by
    refine eq_of_map_jMap_le hwc (le_of_eq ?_)
    rw [conjSubgroup_one, map_conjSubgroup]
    exact hk
  have hrT : conjSubgroup (r : G) T = T := by
    rw [conjSubgroup_one, conjSubgroup_subgroupOf] at e1
    have := Subgroup.subgroupOf_inj.1 e1
    rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem hTR r.2), inf_of_le_left hTR] at this
  have e2 : conjSubgroup (r * ⟨x₂, hx₂⟩) (T.subgroupOf R) =
      conjSubgroup (⟨x₃, hx₃⟩ : ↥R) (T.subgroupOf R) := by
    refine eq_of_map_jMap_le hwc (le_of_eq ?_)
    rw [← conjSubgroup_conjSubgroup, hconj hx₂, map_conjSubgroup, hk₂, hconj hx₃]
  refine ⟨(r : G), r.2, hrT, ?_⟩
  rw [← conjSubgroup_conjSubgroup, hconj hx₂, hconj hx₃, conjSubgroup_subgroupOf] at e2
  have := Subgroup.subgroupOf_inj.1 e2
  rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem (conjSubgroup_le_of_le_of_mem hTR hx₂) r.2),
    inf_of_le_left (conjSubgroup_le_of_le_of_mem hTR hx₃)] at this

omit [Finite G] in
theorem map_conjSubgroup_subgroupOf {x : G} (hx : x ∈ R) :
    ((conjSubgroup x T).subgroupOf R).map (jMap ↥R) =
      conjSubgroup (jMap ↥R ⟨x, hx⟩) ((T.subgroupOf R).map (jMap ↥R)) := by
  rw [← map_conjSubgroup, conjSubgroup_subgroupOf]

theorem map_conjSubgroup_ne_map (hT : IsWC T) (hTR : T ≤ R) {x : G} (hx : x ∈ R)
    (hne : conjSubgroup x T ≠ T) :
    ((conjSubgroup x T).subgroupOf R).map (jMap ↥R) ≠ (T.subgroupOf R).map (jMap ↥R) := by
  intro h
  apply hne
  have e := eq_of_map_jMap_le (isWC_subgroupOf hT R hTR) (a := ⟨x, hx⟩) (b := 1)
    (le_of_eq (by rw [conjSubgroup_subgroupOf, conjSubgroup_one]; exact h))
  rw [conjSubgroup_subgroupOf, conjSubgroup_one] at e
  have := Subgroup.subgroupOf_inj.1 e
  rwa [inf_of_le_left (conjSubgroup_le_of_le_of_mem hTR hx), inf_of_le_left hTR] at this

end Lift

section Triple

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem exists_mem_normalizer_conj_of_triple (h215 : Lemma215Stmt) (h26 : Lemma26Input)
    (hA6 : A6KleinOrbit) (hy : StepHyp T T₁) (hS : Sec3Global T) (hI : Sec3IsoGlobal T)
    (hA1 : secA T T₁ ≠ ⊥) {g h : G} (hg : IsUIdx T T₁ g) (hh : IsUIdx T T₁ h)
    (hgh : conjSubgroup g T ≠ conjSubgroup h T)
    (hcomm : ∀ a ∈ conjSubgroup g (secA T T₁), ∀ b ∈ conjSubgroup h (secA T T₁),
      a * b = b * a)
    (hq : 2 * Nat.card ↥(normIn T (conjSubgroup g T) ⊓ normIn T (conjSubgroup h T)) <
      Nat.card T) :
    ∃ n ∈ Subgroup.normalizer (T : Set G),
      conjSubgroup n (conjSubgroup g T) = conjSubgroup h T := by
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hT := hP.wc
  set A := secA T T₁ with hAdef
  set T₂ := conjSubgroup g T with hT₂def
  set T₃ := conjSubgroup h T with hT₃def
  have hAg : conjSubgroup g A ≠ ⊥ := fun h0 => hA1 (conjSubgroup_eq_bot_iff.1 h0)
  have hAh : conjSubgroup h A ≠ ⊥ := fun h0 => hA1 (conjSubgroup_eq_bot_iff.1 h0)
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAg
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAh
  have ha1' : a ≠ 1 := fun h' => ha1 (Subtype.ext h')
  have hb1' : b ≠ 1 := fun h' => hb1 (Subtype.ext h')
  have haT₂ : a ∈ T₂ := conjSubgroup_mono secA_le_left ha
  have hbT₃ : b ∈ T₃ := conjSubgroup_mono secA_le_left hb
  have hAgN : conjSubgroup g A ≤ Subgroup.normalizer (T₃ : Set G) := fun x hx =>
    (hT.conj h).centralizer_le_normalizer hbT₃ hb1'
      (Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx b hb))
  have hAhN : conjSubgroup h A ≤ Subgroup.normalizer (T₂ : Set G) := fun y hy' =>
    (hT.conj g).centralizer_le_normalizer haT₂ ha1'
      (Subgroup.mem_centralizer_singleton_iff.2 (hcomm a ha y hy').symm)
  have hL₂ : normIn T₂ T ≠ ⊥ := hg.normIn_conj_ne_bot hP
  have hL₃ : normIn T₃ T ≠ ⊥ := hh.normIn_conj_ne_bot hP
  have hL₂₃ : normIn T₂ T₃ ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨a, mem_normIn.2 ⟨haT₂, hAgN ha⟩⟩,
      fun h' => ha1' (congrArg Subtype.val h')⟩
  have hL₃₂ : normIn T₃ T₂ ≠ ⊥ :=
    Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨b, mem_normIn.2 ⟨hbT₃, hAhN hb⟩⟩,
      fun h' => hb1' (congrArg Subtype.val h')⟩
  have hJ := normalizer_sup_secA_triple hP hS hI hg.1 hh.1 hgh hL₂ hL₃ hL₂₃ hL₃₂
  have hS₂ : Sec3 T T₂ := hg.sec3 hP hS
  have hS₃ : Sec3 T T₃ := hh.sec3 hP hS
  obtain ⟨x₂, hx₂X, hx₂⟩ := hS₂.conj
  obtain ⟨x₃, hx₃X, hx₃⟩ := hS₃.conj
  set R : Subgroup G := T ⊔ T₂ ⊔ T₃ with hR
  have hTR : T ≤ R := le_sup_left.trans le_sup_left
  have hT₂R : T₂ ≤ R := le_sup_right.trans le_sup_left
  have hT₃R : T₃ ≤ R := le_sup_right
  have hx₂R : x₂ ∈ R := (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) :
    T ⊔ T₂ ≤ R) hx₂X
  have hx₃R : x₃ ∈ R := (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
    T ⊔ T₃ ≤ R) hx₃X
  have hRfam : (⨆ i, sec57Fam T T₂ T₃ i) = R := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact hTR
      · exact hT₂R
      · exact hT₃R
    · exact sup_le (sup_le (le_iSup (sec57Fam T T₂ T₃) 0) (le_iSup (sec57Fam T T₂ T₃) 1))
        (le_iSup (sec57Fam T T₂ T₃) 2)
  have hRconj : ∀ i, ∃ g' ∈ R, sec57Fam T T₂ T₃ i = conjSubgroup g' T := by
    intro i
    fin_cases i
    · exact ⟨1, R.one_mem, (conjSubgroup_one T).symm⟩
    · exact ⟨x₂, hx₂R, hx₂⟩
    · exact ⟨x₃, hx₃R, hx₃⟩
  have hAg2 : IsElemAbelian 2 (conjSubgroup g A) :=
    isElemAbelian_of_le (hT.conj g).1 (conjSubgroup_mono secA_le_left)
  have hAh2 : IsElemAbelian 2 (conjSubgroup h A) :=
    isElemAbelian_of_le (hT.conj h).1 (conjSubgroup_mono secA_le_left)
  have hA2 : IsElemAbelian 2 A := isElemAbelian_of_le hT.1 secA_le_left
  have c1 : ∀ a' ∈ A, ∀ b' ∈ conjSubgroup g A, a' * b' = b' * a' :=
    secA_comm_conjSubgroup_secA hP hS hg.1 hL₂
  have c2 : ∀ a' ∈ A, ∀ b' ∈ conjSubgroup h A, a' * b' = b' * a' :=
    secA_comm_conjSubgroup_secA hP hS hh.1 hL₃
  have hc13 : ∀ x ∈ A ⊔ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, x * y = y * x := by
    have hle : A ⊔ conjSubgroup g A ≤ Subgroup.centralizer (conjSubgroup h A : Set G) :=
      sup_le (fun a' ha' => Subgroup.mem_centralizer_iff.2 fun b' hb' => (c2 a' ha' b' hb').symm)
        (fun a' ha' => Subgroup.mem_centralizer_iff.2 fun b' hb' =>
          (hcomm a' ha' b' hb').symm)
    exact fun x hx y hy' => (Subgroup.mem_centralizer_iff.1 (hle hx) y hy').symm
  have hQ2 : IsElemAbelian 2 (A ⊔ conjSubgroup g A ⊔ conjSubgroup h A) :=
    isElemAbelian_sup_of_comm (isElemAbelian_sup_of_comm hA2 hAg2 c1) hAh2 hc13
  have hQR : A ⊔ conjSubgroup g A ⊔ conjSubgroup h A ≤ R := by
    refine sup_le (sup_le (secA_le_left.trans hTR) ?_) ?_
    · exact (conjSubgroup_mono secA_le_left : conjSubgroup g A ≤ T₂).trans hT₂R
    · exact (conjSubgroup_mono secA_le_left : conjSubgroup h A ≤ T₃).trans hT₃R
  have hQn : ∀ x ∈ R, conjSubgroup x (A ⊔ conjSubgroup g A ⊔ conjSubgroup h A) =
      A ⊔ conjSubgroup g A ⊔ conjSubgroup h A := fun x hx =>
    mem_normalizer_iff_conjSubgroup_eq.1 (hJ hx)
  have hAgL : conjSubgroup g A ≤ normIn T₂ T := conjSubgroup_secA_le_normIn hP hS hg.1 hL₂
  have hQT : ⁅A ⊔ conjSubgroup g A ⊔ conjSubgroup h A, T⁆ ≠ ⊥ := by
    obtain ⟨x, hxT, hxL⟩ : ∃ x ∈ T, x ∉ normIn T T₂ := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show T ≤ normIn T T₂ from hcon)
      have h2 := two_mul_card_normIn_le_of_maxPair hP
      have h3 : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
      have h4 : Nat.card ↥(normIn T T₂) = Nat.card ↥(normIn T T₁) := hg.card_normIn hP hS
      omega
    intro hbot
    have haQ : a ∈ A ⊔ conjSubgroup g A ⊔ conjSubgroup h A :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)
    have hmem : ⁅a, x⁆ ∈ ⁅A ⊔ conjSubgroup g A ⊔ conjSubgroup h A, T⁆ :=
      Subgroup.commutator_mem_commutator haQ hxT
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxl : x ∈ T ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hxT, Subgroup.mem_centralizer_singleton_iff.2
        (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm⟩
    rw [hS₂.cfg.inf_centralizer_eq_normIn (hAgL ha) ha1'] at hxl
    exact hxL hxl
  have hq' : 2 * Nat.card ↥(⨅ i, normIn T (sec57Fam T T₂ T₃ i)) < Nat.card T := by
    have hle : (⨅ i, normIn T (sec57Fam T T₂ T₃ i)) ≤ normIn T T₂ ⊓ normIn T T₃ :=
      le_inf (iInf_le (fun i => normIn T (sec57Fam T T₂ T₃ i)) 1)
        (iInf_le (fun i => normIn T (sec57Fam T T₂ T₃ i)) 2)
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨hsimple, -, hhyp, hconcl, -, hker⟩ := jLemma35_inf h215 h26 hy.ind hT hS (r := 3)
    (Ts := sec57Fam T T₂ T₃) ⟨0, rfl⟩ hRfam hRconj hQR (isPGroup_two_of_isElemAbelian hQ2) hQn hQT
    hq'
  have hker₂ : ∀ w : ↥R, w ∈ (jMap ↥R).ker → conjSubgroup (w : G) T₂ = T₂ := fun w hw =>
    hker w hw 1
  have hker₃ : ∀ w : ↥R, w ∈ (jMap ↥R).ker → conjSubgroup (w : G) T₃ = T₃ := fun w hw =>
    hker w hw 2
  by_cases hA6' : Nonempty (jQuot ↥R ⧸ Subgroup.center (jQuot ↥R) ≃* alternatingGroup (Fin 6))
  · obtain ⟨e0⟩ := hA6'
    have hcenter : Subgroup.center (jQuot ↥R) = ⊥ := by
      rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (jQuot ↥R)) with
        h0 | h0
      · exact h0
      · exfalso
        have h360 : Nat.card (jQuot ↥R ⧸ Subgroup.center (jQuot ↥R)) = 360 := by
          rw [Nat.card_congr e0.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
          simp [Nat.factorial]
        have h1 : Nat.card (jQuot ↥R ⧸ Subgroup.center (jQuot ↥R)) = 1 := by
          rw [← Subgroup.index_eq_card, h0, Subgroup.index_top]
        omega
    let e : jQuot ↥R ≃* alternatingGroup (Fin 6) :=
      (QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter.symm)).trans e0
    have hconj₂ := map_conjSubgroup_subgroupOf (R := R) (T := T) hx₂R
    have hconj₃ := map_conjSubgroup_subgroupOf (R := R) (T := T) hx₃R
    rw [← hx₂] at hconj₂
    rw [← hx₃] at hconj₃
    have hne₂ := map_conjSubgroup_ne_map hT hTR hx₂R (by rw [← hx₂]; exact hg.1)
    have hne₃ := map_conjSubgroup_ne_map hT hTR hx₃R (by rw [← hx₃]; exact hh.1)
    rw [← hx₂] at hne₂
    rw [← hx₃] at hne₃
    have hc₂ := card_normIn_eq_mul_card_ker hT hTR hx₂R hx₂ hker₂
    have hc₃ := card_normIn_eq_mul_card_ker hT hTR hx₃R hx₃ hker₃
    have h23 : Nat.card ↥(normIn T T₂) = Nat.card ↥(normIn T T₃) :=
      (hg.card_normIn hP hS).trans (hh.card_normIn hP hS).symm
    have hpos : 0 < Nat.card ↥(T.subgroupOf R ⊓ (jMap ↥R).ker) := Nat.card_pos
    have hcard : Nat.card ↥((T.subgroupOf R).map (jMap ↥R) ⊓ Subgroup.normalizer
          (((T₂.subgroupOf R).map (jMap ↥R) : Subgroup (jQuot ↥R)) : Set (jQuot ↥R))) =
        Nat.card ↥((T.subgroupOf R).map (jMap ↥R) ⊓ Subgroup.normalizer
          (((T₃.subgroupOf R).map (jMap ↥R) : Subgroup (jQuot ↥R)) : Set (jQuot ↥R))) := by
      rw [hc₂, hc₃] at h23
      exact Nat.eq_of_mul_eq_mul_right hpos h23
    obtain ⟨k, hkN, hk⟩ := hA6 (jQuot ↥R) ⟨e⟩ ((T.subgroupOf R).map (jMap ↥R))
      ((T₂.subgroupOf R).map (jMap ↥R)) ((T₃.subgroupOf R).map (jMap ↥R)) hhyp.1.1 hhyp.2.1
      ⟨_, hconj₂⟩ ⟨_, hconj₃⟩ hne₂ hne₃ hcard
    obtain ⟨r, hrR, hrT, hrT₂⟩ := exists_mem_normalizer_conj_of_map hT hTR hx₂R hx₃R
      (mem_normalizer_iff_conjSubgroup_eq.1 hkN) (by rw [← hx₂, ← hx₃]; exact hk)
    exact ⟨r, mem_normalizer_of_conjSubgroup_eq hrT, by rw [hx₂, hx₃]; exact hrT₂⟩
  · obtain ⟨r, hrR, h1, h2⟩ := exists_mem_conj_of_jMap_sub hT hTR hconcl hA6' (a₁ := 1) (a₂ := x₂)
      (b₁ := 1) (b₂ := x₃) R.one_mem hx₂R R.one_mem hx₃R
      (by rw [conjSubgroup_one, ← hx₂]; exact hg.1.symm)
      (by rw [conjSubgroup_one, ← hx₃]; exact hh.1.symm)
    rw [conjSubgroup_one] at h1
    refine ⟨r, mem_normalizer_of_conjSubgroup_eq h1, ?_⟩
    rw [← hx₂, ← hx₃] at h2
    exact h2

end Triple

section Final

theorem sec56StepOne_proved (h215 : Lemma215Stmt) (h26 : Lemma26Input) (hA6 : A6KleinOrbit)
    (hTO : CFSG.Timmesfeld.Bridge.Asc72.TheoremOne) (hBW : BenderWCInput) : Sec56StepOne := by
  intro G _ T T₁ hy hS hI hnab h2grp hR' hcard hplus g h hg hh hcent
  have hfin : Finite G := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hP := hy.pair
  have hA1 : secA T T₁ ≠ ⊥ := fun h0 => hnab (by
    have h1 := secR₁_eq_bot_of_secA_eq_bot h0
    intro x hx y hy'
    rw [h1, Subgroup.mem_bot] at hx hy'
    subst hx
    subst hy'
    simp)
  have hAL : secA T T₁ ≠ normIn T T₁ := secA_ne_normIn hTO hBW hy.nonab hP hS
  have hR₁ : ∀ k : G, IsUIdx T T₁ k → conjSubgroup k (secA T T₁) ≤ secR₁ T T₁ := fun k hk => by
    unfold secR₁
    exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) k hk
  have hcent' : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ k : G,
      (∀ a ∈ conjSubgroup k (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a) →
      ∀ a ∈ conjSubgroup (n * k) (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a := by
    intro n hn k hk a ha x hx
    have ha' : n⁻¹ * a * n ∈ conjSubgroup k (secA T T₁) := by
      rw [← conjSubgroup_conjSubgroup] at ha
      exact mem_conjSubgroup.1 ha
    have hx' : n⁻¹ * x * n ∈ secR₁ T T₁ := by
      have h5 := conjSubgroup_secR₁ (T₁ := T₁) ((Subgroup.normalizer (T : Set G)).inv_mem hn)
      have h6 := conj_mem_conjSubgroup n⁻¹ hx
      rw [h5] at h6
      simpa using h6
    have h7 := hk _ ha' _ hx'
    calc a * x = n * ((n⁻¹ * a * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * x * n) * (n⁻¹ * a * n)) * n⁻¹ := by rw [h7]
      _ = x * a := by group
  have key : ∀ g h : G, IsUIdx T T₁ g → IsUIdx T T₁ h →
      (∀ a ∈ conjSubgroup g (secA T T₁), ∀ x ∈ secR₁ T T₁, a * x = x * a) →
      ∃ n ∈ Subgroup.normalizer (T : Set G),
        conjSubgroup n (conjSubgroup g T) = conjSubgroup h T := by
    intro g h hg hh hcent
    by_cases hgh : conjSubgroup g T = conjSubgroup h T
    · exact ⟨1, Subgroup.one_mem _, by rw [conjSubgroup_one]; exact hgh⟩
    have hcomm : ∀ a ∈ conjSubgroup g (secA T T₁), ∀ b ∈ conjSubgroup h (secA T T₁),
        a * b = b * a := fun a ha b hb => hcent a ha b (hR₁ h hh hb)
    by_cases hq : 2 * Nat.card ↥(normIn T (conjSubgroup g T) ⊓ normIn T (conjSubgroup h T)) <
        Nat.card T
    · exact exists_mem_normalizer_conj_of_triple h215 h26 hA6 hy hS hI hA1 hg hh hgh hcomm hq
    push Not at hq
    have hL2 := two_mul_card_normIn_le_of_maxPair hP
    have hg' := hg.card_normIn hP hS
    have hh' := hh.card_normIn hP hS
    have hinf : Nat.card ↥(normIn T (conjSubgroup g T) ⊓ normIn T (conjSubgroup h T)) ≤
        Nat.card ↥(normIn T (conjSubgroup g T)) := Subgroup.card_le_of_le inf_le_left
    have hPeq : normIn T (conjSubgroup g T) = normIn T (conjSubgroup h T) := by
      have h1 : normIn T (conjSubgroup g T) ⊓ normIn T (conjSubgroup h T) =
          normIn T (conjSubgroup g T) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      have h2 : normIn T (conjSubgroup g T) ⊓ normIn T (conjSubgroup h T) =
          normIn T (conjSubgroup h T) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      rw [← h1, h2]
    set P := normIn T (conjSubgroup g T) with hPdef
    obtain ⟨n, hn, hnP⟩ : ∃ n ∈ Subgroup.normalizer (T : Set G), conjSubgroup n P ≠ P := by
      by_contra hcon
      push Not at hcon
      have hPT : P < T := by
        have hPle : P ≤ T := normIn_le T _
        refine lt_of_le_of_ne hPle fun h1 => ?_
        have := Subgroup.card_le_of_le (show T ≤ P from h1.ge)
        have h3 : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
        omega
      have hAP : ¬ P ≤ secA T T₁ := fun hle => by
        have h1 := Subgroup.card_le_of_le hle
        have h2 : Nat.card (secA T T₁) ≤ Nat.card ↥(normIn T T₁) :=
          Subgroup.card_le_of_le secA_le_normIn
        exact hAL (Subgroup.eq_of_le_of_card_ge secA_le_normIn (by omega))
      obtain ⟨x, hxP, hxA⟩ := IsConcreteLE.not_le_iff_exists.1 hAP
      obtain ⟨y, hyT, hyP⟩ := IsConcreteLE.exists_of_lt hPT
      have hxT : x ∈ T := normIn_le T _ hxP
      have hPinv : ∀ z ∈ Subgroup.normalizer (T : Set G), ∀ u ∈ P, z * u * z⁻¹ ∈ P := by
        intro z hz u hu
        have := conj_mem_conjSubgroup z hu
        rwa [hcon z hz] at this
      by_cases hyA : y ∈ secA T T₁
      ·
        have hxy : x * y ∈ T := T.mul_mem hxT hyT
        have hxyA : x * y ∉ secA T T₁ := fun h1 => hxA (by
          have := (secA T T₁).mul_mem h1 ((secA T T₁).inv_mem hyA)
          simpa using this)
        obtain ⟨z, hz, hzx⟩ := secA_transitive hP hS hxT hxA hxy hxyA
        have := hPinv z hz x hxP
        rw [hzx] at this
        exact hyP (by simpa using P.mul_mem (P.inv_mem hxP) this)
      · obtain ⟨z, hz, hzx⟩ := secA_transitive hP hS hxT hxA hyT hyA
        have := hPinv z hz x hxP
        rw [hzx] at this
        exact hyP this
    have hgn : IsUIdx T T₁ (n * g) := hg.mul_normalizer hn
    by_cases hngh : conjSubgroup (n * g) T = conjSubgroup h T
    · exact ⟨n, hn, by rw [conjSubgroup_conjSubgroup]; exact hngh⟩
    have hNn : normIn T (conjSubgroup (n * g) T) = conjSubgroup n P := by
      rw [← conjSubgroup_conjSubgroup]
      exact normIn_conjSubgroup_of_mem_normalizer hn (conjSubgroup g T)
    have hcn : Nat.card ↥(conjSubgroup n P) = Nat.card ↥P := card_conjSubgroup n P
    have hq' : 2 * Nat.card ↥(normIn T (conjSubgroup (n * g) T) ⊓ normIn T (conjSubgroup h T)) <
        Nat.card T := by
      rw [hNn, ← hPeq]
      have hlt : conjSubgroup n P ⊓ P < conjSubgroup n P := by
        refine lt_of_le_of_ne inf_le_left fun h1 => hnP ?_
        have h2 : conjSubgroup n P ≤ P := by
          rw [← h1]
          exact inf_le_right
        exact Subgroup.eq_of_le_of_card_ge h2 (by omega)
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : conjSubgroup n P ⊓ P ≤
        conjSubgroup n P)
      have hk2 : 2 ≤ k := by
        by_contra hk1
        push Not at hk1
        have hcl := Subgroup.card_lt_of_lt hlt
        have hle1 : Nat.card ↥(conjSubgroup n P) ≤ Nat.card ↥(conjSubgroup n P ⊓ P) := by
          rw [hk]
          calc Nat.card ↥(conjSubgroup n P ⊓ P) * k ≤ Nat.card ↥(conjSubgroup n P ⊓ P) * 1 :=
                Nat.mul_le_mul_left _ (by omega)
            _ = Nat.card ↥(conjSubgroup n P ⊓ P) := mul_one _
        omega
      have hpos : 0 < Nat.card ↥(conjSubgroup n P ⊓ P) := Nat.card_pos
      nlinarith
    obtain ⟨m, hm, hmeq⟩ := exists_mem_normalizer_conj_of_triple h215 h26 hA6 hy hS hI hA1 hgn hh
      hngh (fun a ha b hb => hcent' n hn g hcent a ha b (hR₁ h hh hb)) hq'
    exact ⟨m * n, (Subgroup.normalizer (T : Set G)).mul_mem hm hn, by
      rw [← conjSubgroup_conjSubgroup m n, conjSubgroup_conjSubgroup n g]
      exact hmeq⟩
  obtain ⟨n, hn, hnT⟩ := key g h hg hh hcent
  refine ⟨n, hn, ?_⟩
  have e1 : conjSubgroup (n * g) T = conjSubgroup h T := by
    rw [← conjSubgroup_conjSubgroup]
    exact hnT
  have hmem : h⁻¹ * (n * g) ∈ Subgroup.normalizer (T : Set G) := by
    apply mem_normalizer_of_conjSubgroup_eq
    rw [← conjSubgroup_conjSubgroup, e1, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
  calc conjSubgroup n (conjSubgroup g (secA T T₁)) = conjSubgroup (n * g) (secA T T₁) :=
        conjSubgroup_conjSubgroup n g _
    _ = conjSubgroup h (conjSubgroup (h⁻¹ * (n * g)) (secA T T₁)) := by
        rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
    _ = conjSubgroup h (secA T T₁) := by rw [conjSubgroup_secA hmem]

end Final

end CFSG.CGT.Timmesfeld75
