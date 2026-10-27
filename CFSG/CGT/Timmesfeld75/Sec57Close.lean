module

public import CFSG.CGT.Timmesfeld75.Sec57Normal
public import CFSG.CGT.Timmesfeld75.Sec57YLift
public import CFSG.CGT.Timmesfeld75.Sec57YAlg
public import CFSG.CGT.Timmesfeld75.JLemma35
public import CFSG.CGT.Timmesfeld75.Sec5SevenB

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

theorem sec57Y_proved (h215 : Lemma215Stmt) (h26 : Lemma26Input) : Sec57Y := by
  intro G _ T T₁ hy hS hI hA1 hab g hg hgT hnR hcard hcomm
  have hnu : ¬ IsUIdx T T₁ g := fun hu => hnR (by
    unfold secR₁
    exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) g hu)
  have c : Sec57Cfg T T₁ g := ⟨hy, hS, hI, hA1, hab, hg, hgT, hnu, hcard, hcomm⟩
  have hfin := hy.finite
  have : IsSimpleGroup G := hy.simple
  have hT := hy.pair.wc
  have hS₁ : Sec3 T T₁ := hy.pair.sec3 hS
  obtain ⟨s, hsX, -, hsT, hsT₁⟩ := hS₁.exists_swap
  have hQn := sec57Prelim G T T₁ g c s hsT.symm
  have hS₃ := c.sec3₃
  set T₃ := conjSubgroup g T with hT₃
  set R : Subgroup G := T ⊔ T₁ ⊔ T₃ with hR
  have hTR : T ≤ R := le_sup_left.trans le_sup_left
  have hT₁R : T₁ ≤ R := le_sup_right.trans le_sup_left
  have hT₃R : T₃ ≤ R := le_sup_right
  have hsR : s ∈ R := (le_sup_left : T ⊔ T₁ ≤ R) hsX
  obtain ⟨y₃, hy₃X, hy₃⟩ := hS₃.conj
  have hy₃R : y₃ ∈ R := (sup_le (le_sup_left.trans le_sup_left) le_sup_right : T ⊔ T₃ ≤ R) hy₃X
  have hRfam : (⨆ i, sec57Fam T T₁ T₃ i) = R := by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      fin_cases i
      · exact hTR
      · exact hT₁R
      · exact hT₃R
    · exact sup_le (sup_le (le_iSup (sec57Fam T T₁ T₃) 0) (le_iSup (sec57Fam T T₁ T₃) 1))
        (le_iSup (sec57Fam T T₁ T₃) 2)
  have hRconj : ∀ i, ∃ g' ∈ R, sec57Fam T T₁ T₃ i = conjSubgroup g' T := by
    intro i
    fin_cases i
    · exact ⟨1, R.one_mem, (conjSubgroup_one T).symm⟩
    · exact ⟨s, hsR, hsT.symm⟩
    · exact ⟨y₃, hy₃R, hy₃⟩
  set A := secA T T₁ with hA
  have hsne : conjSubgroup s T ≠ T := by
    rw [hsT]
    exact hy.pair.ne
  have hAs₁ : conjSubgroup s A ≤ normIn T₁ T := by
    have := conjSubgroup_secA_le_normIn hy.pair hS hsne (by rw [hsT]; exact hS₁.cfg.ne₁)
    rwa [hsT] at this
  have hAg : conjSubgroup g A ≤ normIn T₃ T :=
    conjSubgroup_secA_le_normIn hy.pair hS hgT c.normIn_ne_bot
  have hsu : IsUIdx T T₁ s := ⟨hsne, by rw [hsT, hS₁.card_normIn_swap]⟩
  have c1 : ∀ a ∈ A, ∀ b ∈ conjSubgroup s A, a * b = b * a := fun a ha b hb =>
    hS₁.cfg.comm_L_L₁ (secA_le_normIn ha) (hAs₁ hb)
  have c2 : ∀ a ∈ A, ∀ b ∈ conjSubgroup g A, a * b = b * a := fun a ha b hb =>
    hS₃.cfg.comm_L_L₁ (c.secA_le_normIn₃ ha) (hAg hb)
  have c3 : ∀ a ∈ conjSubgroup s A, ∀ x ∈ conjSubgroup g A, a * x = x * a := hcomm s hsu
  have hT₁ : IsWC T₁ := hsT ▸ hT.conj s
  have hA2 : IsElemAbelian 2 A := isElemAbelian_of_le hT.1 secA_le_left
  have hA₁2 : IsElemAbelian 2 (conjSubgroup s A) :=
    isElemAbelian_of_le hT₁.1 (hsT ▸ conjSubgroup_mono secA_le_left)
  have hAg2 : IsElemAbelian 2 (conjSubgroup g A) :=
    isElemAbelian_of_le (hT.conj g).1 (conjSubgroup_mono secA_le_left)
  have hc13 : ∀ x ∈ A ⊔ conjSubgroup s A, ∀ y ∈ conjSubgroup g A, x * y = y * x := by
    have hle : A ⊔ conjSubgroup s A ≤ Subgroup.centralizer (conjSubgroup g A : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (c2 a ha b hb).symm)
        (fun a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (c3 a ha b hb).symm)
    exact fun x hx y hy' => (Subgroup.mem_centralizer_iff.1 (hle hx) y hy').symm
  have hQ2 : IsElemAbelian 2 (A ⊔ conjSubgroup s A ⊔ conjSubgroup g A) :=
    isElemAbelian_sup_of_comm (isElemAbelian_sup_of_comm hA2 hA₁2 c1) hAg2 hc13
  have hQR : A ⊔ conjSubgroup s A ⊔ conjSubgroup g A ≤ R := by
    refine sup_le (sup_le (secA_le_left.trans hTR) ?_) ?_
    · exact (show conjSubgroup s A ≤ T₁ from hsT ▸ conjSubgroup_mono secA_le_left).trans hT₁R
    · exact (conjSubgroup_mono secA_le_left : conjSubgroup g A ≤ T₃).trans hT₃R
  have hQT : ⁅A ⊔ conjSubgroup s A ⊔ conjSubgroup g A, T⁆ ≠ ⊥ := by
    have hA₁ne : conjSubgroup s A ≠ ⊥ := fun h => hA1 (conjSubgroup_eq_bot_iff.1 h)
    obtain ⟨⟨l, hl⟩, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₁ne
    have hl1' : l ≠ 1 := fun h => hl1 (Subtype.ext h)
    obtain ⟨x, hxT, hxL⟩ : ∃ x ∈ T, x ∉ normIn T T₁ := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show T ≤ normIn T T₁ from hcon)
      have h2 := two_mul_card_normIn_le_of_maxPair hy.pair
      have h3 : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
      omega
    intro hbot
    have hlQ : l ∈ A ⊔ conjSubgroup s A ⊔ conjSubgroup g A :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_right hl)
    have hmem : ⁅l, x⁆ ∈ ⁅A ⊔ conjSubgroup s A ⊔ conjSubgroup g A, T⁆ :=
      Subgroup.commutator_mem_commutator hlQ hxT
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxl : x ∈ T ⊓ Subgroup.centralizer ({l} : Set G) :=
      ⟨hxT, Subgroup.mem_centralizer_singleton_iff.2
        (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm⟩
    rw [hS₁.cfg.inf_centralizer_eq_normIn (hAs₁ hl) hl1'] at hxl
    exact hxL hxl
  have h7 : Nat.card ↥(normIn T T₃) < Nat.card ↥(normIn T T₁) := by
    rw [← hS₃.card_normIn_swap]
    exact c.card_normIn_lt
  have hq : ∃ j, 2 * Nat.card ↥(normIn T (sec57Fam T T₁ T₃ j)) < Nat.card T := by
    refine ⟨2, ?_⟩
    have h2 := two_mul_card_normIn_le_of_maxPair hy.pair
    show 2 * Nat.card ↥(normIn T T₃) < Nat.card T
    omega
  obtain ⟨-, -, -, -, htrans, hker⟩ := jLemma35 h215 h26 hy.ind hT hS (r := 3)
    (Ts := sec57Fam T T₁ T₃) ⟨0, rfl⟩ hRfam hRconj hQR (isPGroup_two_of_isElemAbelian hQ2) hQn hQT
    hq
  have hker1 : ∀ w : ↥R, w ∈ (jMap ↥R).ker → conjSubgroup (w : G) T₁ = T₁ :=
    fun w hw => hker w hw 1
  have hker2 : ∀ w : ↥R, w ∈ (jMap ↥R).ker → conjSubgroup (w : G) T₃ = T₃ :=
    fun w hw => hker w hw 2
  have hLT : normIn T T₁ ≤ T := normIn_le T T₁
  have h2 : ((normIn T T₁).subgroupOf R).map (jMap ↥R) ≠ (T.subgroupOf R).map (jMap ↥R) := by
    intro h
    have hTL : T ≤ normIn T T₁ := by
      intro t ht
      have htR : t ∈ R := hTR ht
      have hmem : jMap ↥R ⟨t, htR⟩ ∈ ((normIn T T₁).subgroupOf R).map (jMap ↥R) := by
        rw [h]
        exact Subgroup.mem_map.2 ⟨⟨t, htR⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩
      obtain ⟨l, hl, hlt⟩ := Subgroup.mem_map.1 hmem
      have hw : l⁻¹ * ⟨t, htR⟩ ∈ (jMap ↥R).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hlt, inv_mul_cancel]
      have hlN : (l : G) ∈ Subgroup.normalizer (T₁ : Set G) :=
        (mem_normIn.1 (Subgroup.mem_subgroupOf.1 hl)).2
      have hwN : ((l⁻¹ * ⟨t, htR⟩ : ↥R) : G) ∈ Subgroup.normalizer (T₁ : Set G) :=
        mem_normalizer_iff_conjSubgroup_eq.2 (hker1 _ hw)
      have e : t = (l : G) * ((l⁻¹ * ⟨t, htR⟩ : ↥R) : G) := by simp
      exact mem_normIn.2 ⟨ht, by rw [e]; exact (Subgroup.normalizer (T₁ : Set G)).mul_mem hlN hwN⟩
    have hLeq : normIn T T₁ = T := le_antisymm hLT hTL
    have h5 := two_mul_card_normIn_le_of_maxPair hy.pair
    rw [hLeq] at h5
    have : 0 < Nat.card T := Nat.card_pos
    omega
  have h1 : ((normIn T T₁).subgroupOf R).map (jMap ↥R) ≠ ⊥ := by
    intro h
    have hLsub : normIn T T₁ ≤ normIn T T₃ := by
      intro l hl
      have hlR : l ∈ R := hTR (hLT hl)
      have hmem : jMap ↥R ⟨l, hlR⟩ ∈ ((normIn T T₁).subgroupOf R).map (jMap ↥R) :=
        Subgroup.mem_map.2 ⟨⟨l, hlR⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      have hw := hker2 ⟨l, hlR⟩ (MonoidHom.mem_ker.2 hmem)
      exact mem_normIn.2 ⟨hLT hl, mem_normalizer_iff_conjSubgroup_eq.2 hw⟩
    have h6 := Subgroup.card_le_of_le hLsub
    omega
  obtain ⟨n, hnRm, hnT, hnL⟩ := exists_mem_normalizer_conj_ne hT hTR hLT htrans h1 h2
  have hnN : n ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_iff_conjSubgroup_eq.2 hnT
  have hyu : IsUIdx T T₁ (n * s) := hsu.mul_normalizer hnN
  have hyR : n * s ∈ R := R.mul_mem hnRm hsR
  have hT₂ : conjSubgroup (n * s) T = conjSubgroup n T₁ := by
    rw [← conjSubgroup_conjSubgroup, hsT]
  have hNT₂ : normIn T (conjSubgroup (n * s) T) = conjSubgroup n (normIn T T₁) := by
    rw [hT₂]
    exact normIn_conjSubgroup_of_mem_normalizer hnN T₁
  have hSL : ∀ z ∈ A ⊔ conjSubgroup s A, ∀ l ∈ normIn T T₁, l * z = z * l := by
    have hle : A ⊔ conjSubgroup s A ≤ Subgroup.centralizer (normIn T T₁ : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun l hl =>
          elemAbelian_mul_comm hT.1 (hLT hl) (secA_le_left ha))
        (fun a ha => Subgroup.mem_centralizer_iff.2 fun l hl =>
          hS₁.cfg.comm_L_L₁ hl (hAs₁ ha))
    exact fun z hz l hl => Subgroup.mem_centralizer_iff.1 (hle hz) l hl
  have key : ∀ T' : Subgroup G, IsWC T' → ∀ z ∈ T', z ≠ 1 → z ∈ A ⊔ conjSubgroup s A →
      normIn T T₁ ≤ normIn T T' := by
    intro T' hT' z hzT' hz1 hzS l hl
    exact mem_normIn.2 ⟨hLT hl, hT'.centralizer_le_normalizer hzT' hz1
      (Subgroup.mem_centralizer_singleton_iff.2 (hSL z hzS l hl))⟩
  have hA₃S : conjSubgroup g A ⊓ (A ⊔ conjSubgroup s A) = ⊥ := by
    by_contra hne
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have h6 := Subgroup.card_le_of_le
      (key T₃ (hT.conj g) z (conjSubgroup_mono secA_le_left hz.1) hz1' hz.2)
    omega
  have hA₂S : conjSubgroup (n * s) A ⊓ (A ⊔ conjSubgroup s A) = ⊥ := by
    by_contra hne
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have hLle := key (conjSubgroup (n * s) T) (hT.conj (n * s)) z
      (conjSubgroup_mono secA_le_left hz.1) hz1' hz.2
    rw [hNT₂] at hLle
    exact hnL (Subgroup.eq_of_le_of_card_ge hLle (card_conjSubgroup n _).le).symm
  have hAA₁ : A ⊓ conjSubgroup s A = ⊥ := by
    refine eq_bot_iff.2 ((inf_le_inf secA_le_left (hsT ▸ conjSubgroup_mono secA_le_left)).trans
      hS₁.cfg.inf.le)
  have hScard : Nat.card ↥(A ⊔ conjSubgroup s A) = Nat.card A * Nat.card A := by
    rw [card_sup_eq_mul_of_commute c1 hAA₁, card_conjSubgroup]
  have hA₂N : conjSubgroup (n * s) A ≤ A ⊔ conjSubgroup s A ⊔ conjSubgroup g A :=
    (conjSubgroup_mono (le_sup_left.trans le_sup_left)).trans (hQn (n * s) hyR).le
  have hSc₃ : Nat.card ↥(A ⊔ conjSubgroup s A ⊔ conjSubgroup g A) =
      Nat.card A * Nat.card A * Nat.card A := by
    rw [card_sup_eq_mul_of_commute hc13 (by rw [inf_comm]; exact hA₃S), hScard,
      card_conjSubgroup]
  have hSc₂ : Nat.card ↥(A ⊔ conjSubgroup s A ⊔ conjSubgroup (n * s) A) =
      Nat.card A * Nat.card A * Nat.card A := by
    rw [card_sup_eq_mul_of_commute (fun x hx y hy => elemAbelian_mul_comm hQ2
      ((le_sup_left : A ⊔ conjSubgroup s A ≤ _) hx) (hA₂N hy)) (by rw [inf_comm]; exact hA₂S),
      hScard, card_conjSubgroup]
  have heq : A ⊔ conjSubgroup s A ⊔ conjSubgroup (n * s) A =
      A ⊔ conjSubgroup s A ⊔ conjSubgroup g A :=
    Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hA₂N) (by rw [hSc₃, hSc₂])
  have hR₁ : ∀ h : G, IsUIdx T T₁ h → conjSubgroup h A ≤ secR₁ T T₁ := fun h hu => by
    unfold secR₁
    exact le_iSup₂ (f := fun (h : G) (_ : IsUIdx T T₁ h) => conjSubgroup h (secA T T₁)) h hu
  have hSc₂R : A ⊔ conjSubgroup s A ⊔ conjSubgroup (n * s) A ≤ secR₁ T T₁ :=
    sup_le (sup_le (secA_le_secR₁ hy.pair hS hI) (hR₁ s hsu)) (hR₁ (n * s) hyu)
  exact hnR ((le_sup_right : conjSubgroup g A ≤ A ⊔ conjSubgroup s A ⊔ conjSubgroup g A).trans
    ((le_of_eq heq.symm).trans hSc₂R))

end CFSG.CGT.Timmesfeld75
