module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeGen

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

section Mono

variable {Lab : Type} [DecidableEq Lab] {n : ℕ} {act : Array ℕ → Lab → Lab} {L : List (Array ℕ)}
  {lbls lbls' : List Lab}

theorem Wit3Ok.mono_lbls {b q₁ q₂ : QuotGen} (h : Wit3Ok n act L lbls b q₁ q₂)
    (hsub : ∀ x ∈ lbls', x ∈ lbls) : Wit3Ok n act L lbls' b q₁ q₂ := by
  obtain ⟨h1, h2, h3, h4, hq, h5⟩ := h
  exact ⟨h1, h2, h3, h4, fun q hqm => ⟨(hq q hqm).1, fun x hx => (hq q hqm).2 x (hsub x hx)⟩, h5⟩

theorem WitPOk.mono_lbls {p : ℕ} {b q : QuotGen} (h : WitPOk n act L lbls p b q)
    (hsub : ∀ x ∈ lbls', x ∈ lbls) : WitPOk n act L lbls' p b q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, fun x hx => h4 x (hsub x hx), h5⟩

theorem CntOk.mono_lbls {r₁ r₂ : QuotGen} {qs : List QuotGen} (h : CntOk n act L lbls r₁ r₂ qs)
    (hsub : ∀ x ∈ lbls', x ∈ lbls) : CntOk n act L lbls' r₁ r₂ qs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hq, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    fun q hqm => ⟨(hq q hqm).1, (hq q hqm).2.1, (hq q hqm).2.2.1,
      fun x hx => (hq q hqm).2.2.2 x (hsub x hx)⟩, h11⟩

end Mono

section Pcore

variable {X : Type*} [Group X]

theorem card_commutator_pCoreOf (Y : Subgroup X) (b : ↥Y) :
    Nat.card ↥⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ =
      Nat.card ↥⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆ := by
  have hcoreY : pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := by
    unfold pCoreOf
    try with_reducible rfl
  have h : (⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆).map Y.subtype =
      ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hcoreY]
    rfl
  rw [← h]
  exact Subgroup.card_map_of_injective Y.subtype_injective

end Pcore

end CFSG.QuasithinUnique.Vol2Native.L239

namespace CFSG.QuasithinUnique.Ch1.SporLat.LatCtx

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.K1.SporadicPerm
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab] (C : LatCtx Γ n Lab)

theorem cnt_sound {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1) {B : List ℕ}
    (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    {r₁ r₂ : QuotGen} {qs : List QuotGen}
    (h : CntOk n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) r₁ r₂ qs) :
    ∃ s₁ s₂ : ↥(C.Y j), s₁ ^ 3 = 1 ∧ s₂ ^ 3 = 1 ∧ s₁ * s₂ = s₂ * s₁ ∧ s₁ ≠ 1 ∧ s₂ ≠ 1 ∧
      s₂ ≠ s₁ ∧ s₂ ≠ s₁ ^ 2 ∧ ∀ i < 3, ∀ j' < 3, (i ≠ 0 ∨ j' ≠ 0) →
        4 < Nat.card ↥⁅CFSG.pCore 2 ↥(C.Y j), Subgroup.zpowers (s₁ ^ i * s₂ ^ j')⁆ := by
  classical
  obtain ⟨hw1, hw2, hr1, hr2, h13, h23, hcomm, h21, h212, hlen, hq, hcm⟩ := h
  rw [← C.Y_letters hj] at hw1 hw2 hr1 hr2 h13 h23 hcomm h21 h212 hq hcm
  set E : List Γ := C.sg ++ C.gens j with hE
  have hw1' : ∀ l ∈ r₁.w, l < E.length := fun l hl => by
    simpa [genTabs_length] using hw1 l hl
  have hw2' : ∀ l ∈ r₂.w, l < E.length := fun l hl => by
    simpa [genTabs_length] using hw2 l hl
  have hT1 := quotGt_eq (n := n) E r₁ hw1'
  have hT2 := quotGt_eq (n := n) E r₂ hw2'
  set x₁ : Γ := quotElt E r₁ with hx₁
  set x₂ : Γ := quotElt E r₂ with hx₂
  have hx₁Y : x₁ ∈ C.Y j := C.quotElt_mem r₁ hw1'
  have hx₂Y : x₂ ∈ C.Y j := C.quotElt_mem r₂ hw2'
  have hx₁3 : x₁ ^ 3 = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hT1]
    exact h13
  have hx₂3 : x₂ ^ 3 = 1 := by
    apply eq_of_tabArr_eq hB hbase
    rw [tab_pow, tab_one_toArray, ← hT2]
    exact h23
  have hx₁1 : x₁ ≠ 1 := by
    intro h1
    apply hr1
    rw [hT1, h1, tab_one_toArray]
  have hx₂1 : x₂ ≠ 1 := by
    intro h1
    apply hr2
    rw [hT2, h1, tab_one_toArray]
  have hcomm' : x₁ * x₂ = x₂ * x₁ := by
    apply eq_of_tabArr_eq hB hbase
    rw [tabArr_mul, tabArr_mul, ← hT1, ← hT2]
    exact hcomm
  have hne21 : x₂ ≠ x₁ := by
    intro h1
    apply h21
    rw [hT1, hT2, h1]
  have hne212 : x₂ ≠ x₁ ^ 2 := by
    intro h1
    apply h212
    rw [hT2, h1, tab_pow, hT1]
  have hqdata : ∀ q ∈ qs, (∀ l ∈ q.w, l < E.length) ∧ quotElt E q ∈ pCoreOf 2 (C.Y j) ∧
      (tab n (quotElt E q)⁻¹).toArray = quotGi n (genTabs n E) q := by
    intro q hq'
    obtain ⟨hqw, hm, hpow, hfix⟩ := hq q hq'
    have hqw' : ∀ l ∈ q.w, l < E.length := fun l hl => by
      simpa [genTabs_length] using hqw l hl
    obtain ⟨-, hinv⟩ := quotGi_eq (n := n) hB hbase E q hqw' hm hpow
    refine ⟨hqw', ?_, hinv.symm⟩
    apply C.mem_pCoreOf_of_fix hj hodd
    rw [← quotGt_eq (n := n) E q hqw']
    exact hfix
  have hmain : ∀ i < 3, ∀ j' < 3, (i ≠ 0 ∨ j' ≠ 0) →
      4 < Nat.card ↥⁅pCoreOf 2 (C.Y j), Subgroup.zpowers (x₁ ^ i * x₂ ^ j')⁆ := by
    intro i hi j' hj' hne
    set x : Γ := x₁ ^ i * x₂ ^ j' with hx
    have hxc : Commute (x₁ ^ i) (x₂ ^ j') := Commute.pow_pow (show Commute x₁ x₂ from hcomm') i j'
    have hx3 : x ^ 3 = 1 := by
      rw [hx, hxc.mul_pow]
      have e1 : (x₁ ^ i) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx₁3, one_pow]
      have e2 : (x₂ ^ j') ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx₂3, one_pow]
      rw [e1, e2, one_mul]
    have hxinv : x⁻¹ = x ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      exact hx3
    have hxtab : (tab n x).toArray =
        rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j' := by
      rw [hx, tabArr_mul, tab_pow, tab_pow, ← hT1, ← hT2]
      rfl
    have hxitab : (tab n x⁻¹).toArray =
        powTab n (rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j') 2 := by
      rw [hxinv, tab_pow, hxtab]
    have hcomms : ∀ q ∈ qs, (tab n ⁅quotElt E q, x⁆).toArray =
        commTab (quotGt n (genTabs n E) q)
          (rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j')
          (quotGi n (genTabs n E) q)
          (powTab n (rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j') 2) := by
      intro q hq'
      obtain ⟨hqw', -, hqi⟩ := hqdata q hq'
      rw [commutatorElement_def, tabArr_comm, hqi, hxtab, hxitab, quotGt_eq (n := n) E q hqw']
    have hnd : (qs.map fun q => ⁅quotElt E q, x⁆).Nodup := by
      apply List.Nodup.of_map (fun c : Γ => (tab n c).toArray)
      have hmapeq : (qs.map fun q => ⁅quotElt E q, x⁆).map (fun c : Γ => (tab n c).toArray) =
          qs.map fun q => commTab (quotGt n (genTabs n E) q)
            (rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j')
            (quotGi n (genTabs n E) q)
            (powTab n (rijTab n (quotGt n (genTabs n E) r₁) (quotGt n (genTabs n E) r₂) i j')
              2) := by
        rw [List.map_map]
        exact List.map_congr_left fun q hq' => hcomms q hq'
      rw [hmapeq]
      exact hcm i hi j' hj' hne
    have hsub : ∀ c ∈ (qs.map fun q => ⁅quotElt E q, x⁆),
        c ∈ ⁅pCoreOf 2 (C.Y j), Subgroup.zpowers x⁆ := by
      intro c hc
      obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hc
      exact Subgroup.commutator_mem_commutator (hqdata q hq').2.1 (Subgroup.mem_zpowers x)
    have h1 := Set.ncard_le_ncard
      (s := (↑(qs.map fun q => ⁅quotElt E q, x⁆).toFinset : Set Γ))
      (t := ((⁅pCoreOf 2 (C.Y j), Subgroup.zpowers x⁆ : Subgroup Γ) : Set Γ))
      (fun c hc => hsub c (List.mem_toFinset.1 hc)) (Set.toFinite _)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, ← Nat.card_coe_set_eq] at h1
    have h2 : Nat.card ↥((⁅pCoreOf 2 (C.Y j), Subgroup.zpowers x⁆ : Subgroup Γ) : Set Γ) =
        Nat.card ↥⁅pCoreOf 2 (C.Y j), Subgroup.zpowers x⁆ := rfl
    rw [List.length_map] at h1
    omega
  refine ⟨⟨x₁, hx₁Y⟩, ⟨x₂, hx₂Y⟩, Subtype.ext hx₁3, Subtype.ext hx₂3, Subtype.ext hcomm', ?_, ?_,
    ?_, ?_, ?_⟩
  · intro h1
    exact hx₁1 (congrArg Subtype.val h1)
  · intro h1
    exact hx₂1 (congrArg Subtype.val h1)
  · intro h1
    exact hne21 (congrArg Subtype.val h1)
  · intro h1
    exact hne212 (congrArg Subtype.val h1)
  · intro i hi j' hj' hne
    rw [← card_commutator_pCoreOf]
    exact hmain i hi j' hj' hne

theorem goodLocal_of_cnt_nine {j : ℕ} (hj : j < C.J) (hodd : C.D.Om[j]!.lbl.size % 2 = 1)
    {B : List ℕ} (hB : ∀ b ∈ B, b < n) (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1)
    (hcard : C.D.Om[j]!.lbl.size = 9)
    (hO2 : 2 ^ C.k * 9 < 60 * Nat.card ↥(pCoreOf 2 (C.Y j))) {r₁ r₂ : QuotGen}
    {qs : List QuotGen} (h : CntOk n C.A.act (C.D.sTabs ++ C.D.mt[j]!) (C.Λ j) r₁ r₂ qs) :
    GoodLocal (C.Y j) := by
  obtain ⟨s₁, s₂, h₁, h₂, hc, h1a, h2a, h2b, h2c, hP⟩ := C.cnt_sound hj hodd hB hbase h
  have hY : Nat.card ↥(C.Y j) = 9 * 2 ^ C.k := by
    rw [C.Y_card hj, hcard]
  have hm : ¬ 3 ∣ 2 ^ C.k := by
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hA3 := hA3_of_sylow_three hY hm (CFSG.pCore 2 ↥(C.Y j)) s₁ s₂ h₁ h₂ hc h1a h2a h2b h2c hP
  have hq : Nat.card (↥(C.Y j) ⧸ CFSG.pCore 2 ↥(C.Y j)) < 60 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(C.Y j))
    have h2 : Nat.card ↥(pCoreOf 2 (C.Y j)) = Nat.card ↥(CFSG.pCore 2 ↥(C.Y j)) := by
      have : pCoreOf 2 (C.Y j) = (CFSG.pCore 2 ↥(C.Y j)).map (C.Y j).subtype := by
        unfold pCoreOf
        try with_reducible rfl
      rw [this]
      exact Subgroup.card_map_of_injective (C.Y j).subtype_injective
    rw [hY, ← h2] at h1
    have hpos : 0 < Nat.card ↥(pCoreOf 2 (C.Y j)) := Nat.card_pos
    by_contra hcon
    have h3 : 60 ≤ Nat.card (↥(C.Y j) ⧸ CFSG.pCore 2 ↥(C.Y j)) := not_lt.1 hcon
    have : 60 * Nat.card ↥(pCoreOf 2 (C.Y j)) ≤
        Nat.card (↥(C.Y j) ⧸ CFSG.pCore 2 ↥(C.Y j)) * Nat.card ↥(pCoreOf 2 (C.Y j)) :=
      Nat.mul_le_mul_right _ h3
    have h4 : 9 * 2 ^ C.k = Nat.card (↥(C.Y j) ⧸ CFSG.pCore 2 ↥(C.Y j)) *
        Nat.card ↥(pCoreOf 2 (C.Y j)) := h1
    omega
  exact goodLocal_of_count (C.Y j) (a := C.k) (c := 2) (by rw [hY]; ring) hq hA3

end CFSG.QuasithinUnique.Ch1.SporLat.LatCtx
