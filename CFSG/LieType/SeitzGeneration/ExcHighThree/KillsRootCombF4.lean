module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootComb

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

namespace F4Cfg

structure Cfg where
  l0 : Bool
  l1 : Bool
  l2 : Bool
  l3 : Bool
  e01 : Bool
  e02 : Bool
  e03 : Bool
  e12 : Bool
  e13 : Bool
  e23 : Bool

def Cfg.lg (c : Cfg) : ℕ → Bool
  | 0 => c.l0
  | 1 => c.l1
  | 2 => c.l2
  | 3 => c.l3
  | _ => false

def Cfg.ed (c : Cfg) : ℕ → ℕ → Bool
  | 0, 1 => c.e01
  | 1, 0 => c.e01
  | 0, 2 => c.e02
  | 2, 0 => c.e02
  | 0, 3 => c.e03
  | 3, 0 => c.e03
  | 1, 2 => c.e12
  | 2, 1 => c.e12
  | 1, 3 => c.e13
  | 3, 1 => c.e13
  | 2, 3 => c.e23
  | 3, 2 => c.e23
  | _, _ => false

def act (k i : ℕ) : Bool := decide (i < k)

def edk (k : ℕ) (c : Cfg) (i j : ℕ) : Bool := act k i && act k j && c.ed i j

def gram (k : ℕ) (c : Cfg) (i j : ℕ) : ℤ :=
  if i = j then (if c.lg i then 4 else 2)
  else if edk k c i j then (if c.lg i || c.lg j then -2 else -1) else 0

def quad (k : ℕ) (c : Cfg) (x : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, x i * x j * gram k c i j

def xOf (m i : ℕ) : ℤ := (((m / 3 ^ i) % 3 : ℕ) : ℤ)

def pdOK (k : ℕ) (c : Cfg) : Bool :=
  (List.range 81).all fun m =>
    if (List.range 4).all (fun i => act k i || xOf m i == 0) &&
        (List.range 4).any (fun i => F4Cfg.xOf m i != 0) then
      decide (0 < quad k c (F4Cfg.xOf m))
    else true

def bitS (s i : ℕ) : Bool := (s / 2 ^ i) % 2 == 1

def closedS (k : ℕ) (c : Cfg) (s : ℕ) : Bool :=
  (List.range 4).all fun a => (List.range 4).all fun b =>
    !(edk k c a b && bitS s a) || bitS s b

def connOK (k : ℕ) (c : Cfg) : Bool :=
  (List.range 16).all fun s =>
    !(closedS k c s && (List.range 4).any (fun i => act k i && bitS s i)) ||
      (List.range 4).all (fun j => !act k j || bitS s j)

def stepS (k : ℕ) (c : Cfg) (s : ℕ → Bool) : ℕ → Bool :=
  fun j => s j || (List.range 4).any (fun a => s a && edk k c a j && (c.lg a == c.lg j))

def reachFrom (k : ℕ) (c : Cfg) (i : ℕ) : ℕ → Bool :=
  stepS k c (stepS k c (stepS k c (fun j => decide (j = i))))

def reachAll (k : ℕ) (c : Cfg) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun j =>
    !(act k i && act k j && (c.lg i == c.lg j)) || reachFrom k c i j

def Pcfg (k : ℕ) (c : Cfg) : Bool := !connOK k c || reachAll k c || !pdOK k c

def checkAll : Bool :=
  [0, 1, 2, 3, 4].all fun k => [false, true].all fun l0 => [false, true].all fun l1 =>
    [false, true].all fun l2 => [false, true].all fun l3 => [false, true].all fun e01 =>
      [false, true].all fun e02 => [false, true].all fun e03 => [false, true].all fun e12 =>
        [false, true].all fun e13 => [false, true].all fun e23 =>
          Pcfg k ⟨l0, l1, l2, l3, e01, e02, e03, e12, e13, e23⟩

theorem checkAll_eq : checkAll = true := by decide +kernel

end F4Cfg



theorem f4_iform_self {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    iform γ γ = 2 ∨ iform γ γ = 4 :=
  iform_self_cases noG2_F4 hγ

theorem f4_adj_value {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {δ ε : Fin Tag.F4.rank → ℤ} (hδ : δ ∈ simpleRoots Ψ) (hε : ε ∈ simpleRoots Ψ)
    (hne : δ ≠ ε) (hnz : iform δ ε ≠ 0) :
    (iform δ δ = 2 ∧ iform ε ε = 2 ∧ iform δ ε = -1) ∨
      ((iform δ δ = 4 ∨ iform ε ε = 4) ∧ iform δ ε = -2) := by
  have hδr := simpleRoots_isRoot hδ
  have hεr := simpleRoots_isRoot hε
  have hle : iform δ ε ≤ 0 := iform_simpleRoots_nonpos hΨ hδ hε hne
  have ha := f4_iform_self hδr
  have hb := f4_iform_self hεr
  have hda : iform δ δ ∣ 2 * iform δ ε := iform_dvd_of_isRoot hδr ε
  have hdb : iform ε ε ∣ 2 * iform δ ε := by
    have := iform_dvd_of_isRoot hεr δ
    rwa [iform_comm ε δ] at this
  have hpos : 0 < iform (δ + ε) (δ + ε) := by
    apply iform_self_pos
    intro h0
    have hδ' : δ = -ε := add_eq_zero_iff_eq_neg.1 h0
    have h1 := simpleRoots_height_pos hδ
    have h2 := simpleRoots_height_pos hε
    rw [hδ', height_neg] at h1
    omega
  rw [kr_iform_add_add] at hpos
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rw [ha] at hda <;> rw [hb] at hdb <;> rw [ha, hb] at hpos <;> omega

theorem f4_smul_of_values {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {δ ε : Fin Tag.F4.rank → ℤ} (hδ : δ ∈ simpleRoots Ψ) (hε : ε ∈ simpleRoots Ψ)
    (hv : (iform δ δ = 2 ∧ iform ε ε = 2 ∧ iform δ ε = -1) ∨
      (iform δ δ = 4 ∧ iform ε ε = 4 ∧ iform δ ε = -2)) :
    ∃ x ∈ componentWeylGroup Ψ, x • δ = ε := by
  have hδr := simpleRoots_isRoot hδ
  have hεr := simpleRoots_isRoot hε
  have hcomm : iform ε δ = iform δ ε := iform_comm ε δ
  have hc1 : corootPair ε δ = -1 := by
    unfold corootPair
    rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h2, hcomm, h3] <;> norm_num
  have hc2 : corootPair δ (δ + ε) = 1 := by
    unfold corootPair
    rw [iform_add_right]
    rcases hv with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rw [h1, h3] <;> norm_num
  have hre : rootReflection ε • δ = δ + ε := by
    rw [rootReflection_smul hεr, hc1, neg_one_smul, sub_neg_eq_add]
  have hrd : rootReflection δ • (δ + ε) = ε := by
    rw [rootReflection_smul hδr, hc2, one_smul]
    abel
  exact ⟨rootReflection δ * rootReflection ε,
    mul_mem (rootReflection_mem_componentWeylGroup hδ) (rootReflection_mem_componentWeylGroup hε),
    by rw [mul_smul, hre, hrd]⟩

theorem f4_smul_of_adj_same {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {δ ε : Fin Tag.F4.rank → ℤ} (hδ : δ ∈ simpleRoots Ψ) (hε : ε ∈ simpleRoots Ψ)
    (hne : δ ≠ ε) (hnz : iform δ ε ≠ 0) (hlen : iform δ δ = iform ε ε) :
    ∃ x ∈ componentWeylGroup Ψ, x • δ = ε := by
  rcases f4_adj_value hΨ hδ hε hne hnz with h | ⟨h, h2⟩
  · exact f4_smul_of_values hΨ hδ hε (Or.inl h)
  · exact f4_smul_of_values hΨ hδ hε (Or.inr ⟨by omega, by omega, h2⟩)


noncomputable def f4Vtx (Ψ : Set (Fin Tag.F4.rank → ℤ)) (i : ℕ) : Fin Tag.F4.rank → ℤ :=
  if h : i < (simpleRoots Ψ).card then ((simpleRoots Ψ).equivFin.symm ⟨i, h⟩).1 else 0

theorem f4Vtx_mem {Ψ : Set (Fin Tag.F4.rank → ℤ)} {i : ℕ} (h : i < (simpleRoots Ψ).card) :
    f4Vtx Ψ i ∈ simpleRoots Ψ := by
  unfold f4Vtx
  rw [dif_pos h]
  exact ((simpleRoots Ψ).equivFin.symm ⟨i, h⟩).2

theorem exists_f4Vtx {Ψ : Set (Fin Tag.F4.rank → ℤ)} {x : Fin Tag.F4.rank → ℤ}
    (hx : x ∈ simpleRoots Ψ) : ∃ i, i < (simpleRoots Ψ).card ∧ f4Vtx Ψ i = x := by
  set e := (simpleRoots Ψ).equivFin ⟨x, hx⟩ with he
  refine ⟨e.1, e.2, ?_⟩
  unfold f4Vtx
  rw [dif_pos e.2]
  have h1 : (⟨e.1, e.2⟩ : Fin (simpleRoots Ψ).card) = e := Fin.eta _ _
  rw [h1, Equiv.symm_apply_apply]

theorem f4Vtx_inj {Ψ : Set (Fin Tag.F4.rank → ℤ)} {i j : ℕ} (hi : i < (simpleRoots Ψ).card)
    (hj : j < (simpleRoots Ψ).card) (h : f4Vtx Ψ i = f4Vtx Ψ j) : i = j := by
  unfold f4Vtx at h
  rw [dif_pos hi, dif_pos hj] at h
  have h2 : (simpleRoots Ψ).equivFin.symm ⟨i, hi⟩ = (simpleRoots Ψ).equivFin.symm ⟨j, hj⟩ :=
    Subtype.ext h
  exact congrArg Fin.val ((simpleRoots Ψ).equivFin.symm.injective h2)

theorem card_simpleRoots_le {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    (simpleRoots Ψ).card ≤ 4 := by
  classical
  have hli : LinearIndependent ℝ (fun β : simpleRoots Ψ => toReal (β : Fin Tag.F4.rank → ℤ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg β
    set c : (Fin Tag.F4.rank → ℤ) → ℝ := fun x => if h : x ∈ simpleRoots Ψ then g ⟨x, h⟩ else 0
      with hcdef
    have hc : ∑ x ∈ simpleRoots Ψ, c x • toReal x = 0 := by
      rw [← Finset.sum_coe_sort (simpleRoots Ψ)]
      convert hg using 2 with x
      simp [hcdef, x.2]
    have := eq_zero_of_sum_smul_simpleRoots hΨ hc β.1 β.2
    simpa [hcdef, β.2] using this
  have h := hli.fintype_card_le_finrank
  simp only [Module.finrank_fin_fun, Fintype.card_coe] at h
  exact h

set_option maxRecDepth 8000 in
theorem f4_indep_vtx {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) (g : ℕ → ℝ)
    (h : ∑ i ∈ Finset.range (simpleRoots Ψ).card, g i • toReal (f4Vtx Ψ i) = 0) :
    ∀ i < (simpleRoots Ψ).card, g i = 0 := by
  classical
  set k := (simpleRoots Ψ).card with hk
  set c : (Fin Tag.F4.rank → ℤ) → ℝ :=
    fun x => if hx : x ∈ simpleRoots Ψ then
      g (((simpleRoots Ψ).equivFin ⟨x, hx⟩ : Fin k) : ℕ) else 0
      with hcdef
  have hsum : ∑ x ∈ simpleRoots Ψ, c x • toReal x = 0 := by
    rw [← Finset.sum_coe_sort (simpleRoots Ψ), ← Equiv.sum_comp (simpleRoots Ψ).equivFin.symm]
    rw [← Fin.sum_univ_eq_sum_range (fun i => g i • toReal (f4Vtx Ψ i)) k] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hv : f4Vtx Ψ (j : ℕ) = ((simpleRoots Ψ).equivFin.symm j).1 := by
      unfold f4Vtx
      rw [dif_pos j.2]
    have hc' : c ((simpleRoots Ψ).equivFin.symm j).1 = g j := by
      simp only [hcdef, dif_pos ((simpleRoots Ψ).equivFin.symm j).2]
      rw [Subtype.coe_eta, Equiv.apply_symm_apply]
    rw [hc', hv]
  have hz := eq_zero_of_sum_smul_simpleRoots hΨ hsum
  intro i hi
  have hmem := f4Vtx_mem (Ψ := Ψ) hi
  have hz' := hz (f4Vtx Ψ i) hmem
  have hc' : c (f4Vtx Ψ i) = g i := by
    have hv : f4Vtx Ψ i = ((simpleRoots Ψ).equivFin.symm ⟨i, hi⟩).1 := by
      unfold f4Vtx
      rw [dif_pos hi]
    have he' : (simpleRoots Ψ).equivFin ⟨f4Vtx Ψ i, hmem⟩ = ⟨i, hi⟩ :=
      ((simpleRoots Ψ).equivFin.eq_symm_apply).1 (Subtype.ext hv)
    simp only [hcdef, dif_pos hmem, he']
  rw [hc'] at hz'
  exact hz'

noncomputable def f4Cfg (Ψ : Set (Fin Tag.F4.rank → ℤ)) : F4Cfg.Cfg :=
  ⟨decide (iform (f4Vtx Ψ 0) (f4Vtx Ψ 0) = 4), decide (iform (f4Vtx Ψ 1) (f4Vtx Ψ 1) = 4),
    decide (iform (f4Vtx Ψ 2) (f4Vtx Ψ 2) = 4), decide (iform (f4Vtx Ψ 3) (f4Vtx Ψ 3) = 4),
    decide (iform (f4Vtx Ψ 0) (f4Vtx Ψ 1) ≠ 0), decide (iform (f4Vtx Ψ 0) (f4Vtx Ψ 2) ≠ 0),
    decide (iform (f4Vtx Ψ 0) (f4Vtx Ψ 3) ≠ 0), decide (iform (f4Vtx Ψ 1) (f4Vtx Ψ 2) ≠ 0),
    decide (iform (f4Vtx Ψ 1) (f4Vtx Ψ 3) ≠ 0), decide (iform (f4Vtx Ψ 2) (f4Vtx Ψ 3) ≠ 0)⟩

theorem f4Cfg_lg (Ψ : Set (Fin Tag.F4.rank → ℤ)) {i : ℕ} (hi : i < 4) :
    (f4Cfg Ψ).lg i = decide (iform (f4Vtx Ψ i) (f4Vtx Ψ i) = 4) := by
  interval_cases i <;> simp [f4Cfg, F4Cfg.Cfg.lg]

theorem f4Cfg_ed (Ψ : Set (Fin Tag.F4.rank → ℤ)) {i j : ℕ} (hi : i < 4) (hj : j < 4)
    (hij : i ≠ j) : (f4Cfg Ψ).ed i j = decide (iform (f4Vtx Ψ i) (f4Vtx Ψ j) ≠ 0) := by
  interval_cases i <;> interval_cases j <;> first
    | exact absurd rfl hij
    | rfl
    | (rw [iform_comm (f4Vtx Ψ _) (f4Vtx Ψ _)]; rfl)

theorem F4Cfg_ed_self (c : F4Cfg.Cfg) (a : ℕ) : c.ed a a = false := by
  match a with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => rfl

theorem f4_gram_eq {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) {i j : ℕ}
    (hi : i < (simpleRoots Ψ).card) (hj : j < (simpleRoots Ψ).card) (hi4 : i < 4) (hj4 : j < 4) :
    F4Cfg.gram (simpleRoots Ψ).card (f4Cfg Ψ) i j = iform (f4Vtx Ψ i) (f4Vtx Ψ j) := by
  by_cases hij : i = j
  · subst hij
    have hr := simpleRoots_isRoot (f4Vtx_mem (Ψ := Ψ) hi)
    unfold F4Cfg.gram
    rw [if_pos rfl, f4Cfg_lg Ψ hi4]
    rcases f4_iform_self hr with h | h <;> rw [h] <;> simp
  · have hne : f4Vtx Ψ i ≠ f4Vtx Ψ j := fun h => hij (f4Vtx_inj hi hj h)
    have hedk : F4Cfg.edk (simpleRoots Ψ).card (f4Cfg Ψ) i j =
        decide (iform (f4Vtx Ψ i) (f4Vtx Ψ j) ≠ 0) := by
      unfold F4Cfg.edk F4Cfg.act
      rw [decide_eq_true hi, decide_eq_true hj, f4Cfg_ed Ψ hi4 hj4 hij]
      simp
    unfold F4Cfg.gram
    rw [if_neg hij, hedk]
    by_cases hnz : iform (f4Vtx Ψ i) (f4Vtx Ψ j) = 0
    · rw [hnz]
      simp
    · rcases f4_adj_value hΨ (f4Vtx_mem hi) (f4Vtx_mem hj) hne hnz with
        ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
      · simp [f4Cfg_lg Ψ hi4, f4Cfg_lg Ψ hj4, h1, h2, h3]
      · have hlg : ((f4Cfg Ψ).lg i || (f4Cfg Ψ).lg j) = true := by
          rw [f4Cfg_lg Ψ hi4, f4Cfg_lg Ψ hj4]
          rcases h1 with h1 | h1 <;> simp [h1]
        simp [hlg, h3, hnz]


theorem band_iff' (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem bor_iff' (a b : Bool) : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp

theorem bool_mem' (b : Bool) : b ∈ [false, true] := by
  cases b <;> simp

theorem f4cfg_Pcfg (k : ℕ) (hk : k ≤ 4) (c : F4Cfg.Cfg) : F4Cfg.Pcfg k c = true := by
  have hk' : k ∈ [0, 1, 2, 3, 4] := by interval_cases k <;> decide
  have h := F4Cfg.checkAll_eq
  unfold F4Cfg.checkAll at h
  simp only [List.all_eq_true] at h
  exact h k hk' c.l0 (bool_mem' _) c.l1 (bool_mem' _) c.l2 (bool_mem' _) c.l3 (bool_mem' _)
    c.e01 (bool_mem' _) c.e02 (bool_mem' _) c.e03 (bool_mem' _) c.e12 (bool_mem' _)
    c.e13 (bool_mem' _) c.e23 (bool_mem' _)

theorem f4cfg_reachFrom {k : ℕ} {c : F4Cfg.Cfg} (h : F4Cfg.reachAll k c = true) {i j : ℕ}
    (hi : i < 4) (hj : j < 4)
    (hcond : (F4Cfg.act k i && F4Cfg.act k j && (c.lg i == c.lg j)) = true) :
    F4Cfg.reachFrom k c i j = true := by
  unfold F4Cfg.reachAll at h
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (h i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  simpa [hcond] using h2

theorem f4cfg_reach_sound (k : ℕ) (c : F4Cfg.Cfg) (S : ℕ → Bool)
    (hS : ∀ a b, F4Cfg.act k a = true → F4Cfg.act k b = true → (c.lg a == c.lg b) = true →
      F4Cfg.edk k c a b = true → S a = true → S b = true)
    {i j : ℕ} (hi : S i = true) (hr : F4Cfg.reachFrom k c i j = true) : S j = true := by
  have step : ∀ s : ℕ → Bool, (∀ j, s j = true → S j = true) →
      ∀ j, F4Cfg.stepS k c s j = true → S j = true := by
    intro s hs j hj
    unfold F4Cfg.stepS at hj
    rcases (bor_iff' _ _).1 hj with hj | hj
    · exact hs j hj
    · obtain ⟨a, _, ha⟩ := List.any_eq_true.1 hj
      obtain ⟨h12, hlg⟩ := (band_iff' _ _).1 ha
      obtain ⟨hsa, hed⟩ := (band_iff' _ _).1 h12
      have hk := hed
      unfold F4Cfg.edk at hk
      obtain ⟨hk1, _⟩ := (band_iff' _ _).1 hk
      obtain ⟨hka, hkj⟩ := (band_iff' _ _).1 hk1
      exact hS a j hka hkj hlg hed (hs a hsa)
  have hs0 : ∀ j, (fun j => decide (j = i)) j = true → S j = true := by
    intro j hj
    have hji : j = i := of_decide_eq_true hj
    subst hji
    exact hi
  have h1 := step _ hs0
  have h2 := step _ h1
  unfold F4Cfg.reachFrom at hr
  exact step _ h2 j hr

theorem f4_quad_eq {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) (x : ℕ → ℤ)
    (hx : ∀ i < 4, ¬ i < (simpleRoots Ψ).card → x i = 0) :
    F4Cfg.quad (simpleRoots Ψ).card (f4Cfg Ψ) x =
      iform (∑ i ∈ Finset.range 4, x i • f4Vtx Ψ i) (∑ i ∈ Finset.range 4, x i • f4Vtx Ψ i) := by
  unfold F4Cfg.quad
  rw [iform_finset_sum_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [iform_smul_left, iform_smul_right]
  have hi4 : i < 4 := Finset.mem_range.1 hi
  have hj4 : j < 4 := Finset.mem_range.1 hj
  by_cases hik : i < (simpleRoots Ψ).card
  · by_cases hjk : j < (simpleRoots Ψ).card
    · rw [← f4_gram_eq hΨ hik hjk hi4 hj4]
      ring
    · rw [hx j hj4 hjk]
      ring
  · rw [hx i hi4 hik]
    ring

theorem f4_s_ne_zero {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) (x : ℕ → ℤ)
    (hx : ∀ i < 4, ¬ i < (simpleRoots Ψ).card → x i = 0) (hne : ∃ i < 4, x i ≠ 0) :
    ∑ i ∈ Finset.range 4, x i • f4Vtx Ψ i ≠ 0 := by
  intro hs
  have hk4 := card_simpleRoots_le hΨ
  have h0 : toReal (∑ i ∈ Finset.range 4, x i • f4Vtx Ψ i) = 0 := by
    rw [hs]
    ext j
    simp [toReal]
  rw [toReal_sum_smul] at h0
  have hsub : ∑ i ∈ Finset.range (simpleRoots Ψ).card, ((x i : ℤ) : ℝ) • toReal (f4Vtx Ψ i) =
      ∑ i ∈ Finset.range 4, ((x i : ℤ) : ℝ) • toReal (f4Vtx Ψ i) := by
    apply Finset.sum_subset
    · exact Finset.range_mono hk4
    · intro i hi hni
      have hi4 : i < 4 := Finset.mem_range.1 hi
      have hik : ¬ i < (simpleRoots Ψ).card := fun h => hni (Finset.mem_range.2 h)
      rw [hx i hi4 hik]
      simp
  have hind := f4_indep_vtx hΨ (fun i => ((x i : ℤ) : ℝ)) (by simpa [hsub] using h0)
  obtain ⟨i, hi4, hxi⟩ := hne
  by_cases hik : i < (simpleRoots Ψ).card
  · have h1 := hind i hik
    simp only [Int.cast_eq_zero] at h1
    exact hxi h1
  · exact hxi (hx i hi4 hik)

theorem f4_quad_pos {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) (x : ℕ → ℤ)
    (hx : ∀ i < 4, ¬ i < (simpleRoots Ψ).card → x i = 0) (hne : ∃ i < 4, x i ≠ 0) :
    0 < F4Cfg.quad (simpleRoots Ψ).card (f4Cfg Ψ) x := by
  rw [f4_quad_eq hΨ x hx]
  exact iform_self_pos (f4_s_ne_zero hΨ x hx hne)

theorem f4_pdOK {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    F4Cfg.pdOK (simpleRoots Ψ).card (f4Cfg Ψ) = true := by
  unfold F4Cfg.pdOK
  rw [List.all_eq_true]
  intro m _
  split_ifs with h
  · obtain ⟨h1, h2⟩ := (band_iff' _ _).1 h
    have hx : ∀ i < 4, ¬ i < (simpleRoots Ψ).card → F4Cfg.xOf m i = 0 := by
      intro i hi hik
      have h3 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
      have hk : F4Cfg.act (simpleRoots Ψ).card i = false := by
        unfold F4Cfg.act
        exact decide_eq_false hik
      rw [hk, Bool.false_or] at h3
      exact beq_iff_eq.1 h3
    have hne : ∃ i < 4, F4Cfg.xOf m i ≠ 0 := by
      obtain ⟨i, hi, hi'⟩ := List.any_eq_true.1 h2
      exact ⟨i, List.mem_range.1 hi, bne_iff_ne.1 hi'⟩
    simpa using f4_quad_pos hΨ (F4Cfg.xOf m) hx hne
  · rfl

theorem f4_conn_prop {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) (s : ℕ)
    (hcl : F4Cfg.closedS (simpleRoots Ψ).card (f4Cfg Ψ) s = true) {i j : ℕ}
    (hi : i < (simpleRoots Ψ).card) (hj : j < (simpleRoots Ψ).card)
    (his : F4Cfg.bitS s i = true) : F4Cfg.bitS s j = true := by
  have hk4 := card_simpleRoots_le hΨ
  have hcl' : ∀ a < 4, ∀ b < 4,
      (!(F4Cfg.edk (simpleRoots Ψ).card (f4Cfg Ψ) a b && F4Cfg.bitS s a) ||
        F4Cfg.bitS s b) = true := by
    intro a ha b hb
    unfold F4Cfg.closedS at hcl
    rw [List.all_eq_true] at hcl
    exact List.all_eq_true.1 (hcl a (List.mem_range.2 ha)) b (List.mem_range.2 hb)
  have key : ∀ y, Relation.ReflTransGen (SimpleAdj Ψ) (f4Vtx Ψ i) y →
      ∃ a, a < (simpleRoots Ψ).card ∧ f4Vtx Ψ a = y ∧ F4Cfg.bitS s a = true := by
    intro y hy
    induction hy with
    | refl => exact ⟨i, hi, rfl, his⟩
    | tail _ hbc ih =>
      obtain ⟨a, ha, hva, hsa⟩ := ih
      obtain ⟨_, hy', hne⟩ := hbc
      obtain ⟨b, hb, hvb⟩ := exists_f4Vtx hy'
      refine ⟨b, hb, hvb, ?_⟩
      by_cases hab : a = b
      · subst hab
        exact hsa
      · have ha4 : a < 4 := by omega
        have hb4 : b < 4 := by omega
        have hne' : iform (f4Vtx Ψ a) (f4Vtx Ψ b) ≠ 0 := by
          rw [hva, hvb]
          exact hne
        have hed : F4Cfg.edk (simpleRoots Ψ).card (f4Cfg Ψ) a b = true := by
          unfold F4Cfg.edk F4Cfg.act
          rw [decide_eq_true ha, decide_eq_true hb, f4Cfg_ed Ψ ha4 hb4 hab]
          simpa using hne'
        have h5 := hcl' a ha4 b hb4
        rw [hed, hsa] at h5
        simpa using h5
  obtain ⟨a, ha, hva, hsa⟩ :=
    key _ (simpleRoots_connected hΨ (f4Vtx_mem hi) (f4Vtx_mem hj))
  have haj : a = j := f4Vtx_inj ha hj hva
  subst haj
  exact hsa

theorem f4_connOK {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ) :
    F4Cfg.connOK (simpleRoots Ψ).card (f4Cfg Ψ) = true := by
  unfold F4Cfg.connOK
  rw [List.all_eq_true]
  intro s _
  rcases Bool.eq_false_or_eq_true (F4Cfg.closedS (simpleRoots Ψ).card (f4Cfg Ψ) s &&
      (List.range 4).any (fun i => F4Cfg.act (simpleRoots Ψ).card i && F4Cfg.bitS s i)) with hX | hX
  · obtain ⟨hcl, hany⟩ := (band_iff' _ _).1 hX
    obtain ⟨i, _, hi⟩ := List.any_eq_true.1 hany
    obtain ⟨hai, hbi⟩ := (band_iff' _ _).1 hi
    have hik : i < (simpleRoots Ψ).card := by simpa [F4Cfg.act] using hai
    simp only [hX, Bool.not_true, Bool.false_or]
    rw [List.all_eq_true]
    intro j _
    by_cases hjk : F4Cfg.act (simpleRoots Ψ).card j = true
    · have hjk' : j < (simpleRoots Ψ).card := by simpa [F4Cfg.act] using hjk
      have := f4_conn_prop hΨ s hcl hik hjk' hbi
      simp [hjk, this]
    · simp [hjk]
  · simp only [hX, Bool.not_false, Bool.true_or]

theorem f4_same_length_conj {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {δ ε : Fin Tag.F4.rank → ℤ} (hδ : δ ∈ simpleRoots Ψ) (hε : ε ∈ simpleRoots Ψ)
    (hlen : iform δ δ = iform ε ε) : ∃ y ∈ componentWeylGroup Ψ, y • δ = ε := by
  classical
  obtain ⟨i0, hi0, rfl⟩ := exists_f4Vtx hδ
  obtain ⟨j0, hj0, rfl⟩ := exists_f4Vtx hε
  have hk4 := card_simpleRoots_le hΨ
  by_cases hij : i0 = j0
  · subst hij
    exact ⟨1, one_mem _, one_smul _ _⟩
  have hi04 : i0 < 4 := by omega
  have hj04 : j0 < 4 := by omega
  have hPc := f4cfg_Pcfg _ hk4 (f4Cfg Ψ)
  have hreachAll : F4Cfg.reachAll (simpleRoots Ψ).card (f4Cfg Ψ) = true := by
    unfold F4Cfg.Pcfg at hPc
    rw [f4_connOK hΨ, f4_pdOK hΨ] at hPc
    simpa using hPc
  have hlg : ((f4Cfg Ψ).lg i0 == (f4Cfg Ψ).lg j0) = true := by
    rw [f4Cfg_lg Ψ hi04, f4Cfg_lg Ψ hj04, hlen]
    simp
  let S : ℕ → Bool := fun a =>
    decide (∃ y ∈ componentWeylGroup Ψ, y • f4Vtx Ψ i0 = f4Vtx Ψ a)
  have hS : ∀ a b, F4Cfg.act (simpleRoots Ψ).card a = true →
      F4Cfg.act (simpleRoots Ψ).card b = true → ((f4Cfg Ψ).lg a == (f4Cfg Ψ).lg b) = true →
      F4Cfg.edk (simpleRoots Ψ).card (f4Cfg Ψ) a b = true → S a = true → S b = true := by
    intro a b ha hb hab hed hSa
    have ha' : a < (simpleRoots Ψ).card := by simpa [F4Cfg.act] using ha
    have hb' : b < (simpleRoots Ψ).card := by simpa [F4Cfg.act] using hb
    have ha4 : a < 4 := by omega
    have hb4 : b < 4 := by omega
    have hcd : (f4Cfg Ψ).ed a b = true := by
      unfold F4Cfg.edk at hed
      exact ((band_iff' _ _).1 hed).2
    have hab_ne : a ≠ b := by
      intro h
      subst h
      rw [F4Cfg_ed_self] at hcd
      exact Bool.false_ne_true hcd
    have hiff : iform (f4Vtx Ψ a) (f4Vtx Ψ b) ≠ 0 := by
      rw [f4Cfg_ed Ψ ha4 hb4 hab_ne] at hcd
      simpa using hcd
    have hl := beq_iff_eq.1 hab
    rw [f4Cfg_lg Ψ ha4, f4Cfg_lg Ψ hb4] at hl
    have hA := f4_iform_self (simpleRoots_isRoot (f4Vtx_mem ha'))
    have hB := f4_iform_self (simpleRoots_isRoot (f4Vtx_mem hb'))
    have hlen' : iform (f4Vtx Ψ a) (f4Vtx Ψ a) = iform (f4Vtx Ψ b) (f4Vtx Ψ b) := by
      have hl' := decide_eq_decide.1 hl
      rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp_all
    have hne : f4Vtx Ψ a ≠ f4Vtx Ψ b := fun h => hab_ne (f4Vtx_inj ha' hb' h)
    obtain ⟨z, hz, hzab⟩ := f4_smul_of_adj_same hΨ (f4Vtx_mem ha') (f4Vtx_mem hb') hne hiff hlen'
    have hSa' : ∃ y ∈ componentWeylGroup Ψ, y • f4Vtx Ψ i0 = f4Vtx Ψ a := by
      simpa [S] using hSa
    obtain ⟨y, hy, hyδ⟩ := hSa'
    simp only [S, decide_eq_true_eq]
    exact ⟨z * y, mul_mem hz hy, by rw [mul_smul, hyδ, hzab]⟩
  have hS0 : S i0 = true := by
    simp only [S, decide_eq_true_eq]
    exact ⟨1, one_mem _, one_smul _ _⟩
  have hr := f4cfg_reachFrom hreachAll (i := i0) (j := j0) hi04 hj04
    (by simpa [F4Cfg.act, hi0, hj0] using hlg)
  have hfin := f4cfg_reach_sound (simpleRoots Ψ).card (f4Cfg Ψ) S hS hS0 hr
  simpa [S] using hfin

theorem f4_smul_of_mem_component {Ψ : Set (Fin Tag.F4.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {α β : Fin Tag.F4.rank → ℤ} (hα : α ∈ Ψ) (hβ : β ∈ Ψ) (hlen : iform α α = iform β β) :
    ∃ x ∈ componentWeylGroup Ψ, x • α = β := by
  obtain ⟨u, hu, δ, hδ, rfl⟩ := exists_smul_simpleRoot hΨ hα
  obtain ⟨v, hv, ε, hε, rfl⟩ := exists_smul_simpleRoot hΨ hβ
  rw [iform_smul u δ δ, iform_smul v ε ε] at hlen
  obtain ⟨y, hy, hyδ⟩ := f4_same_length_conj hΨ hδ hε hlen
  exact ⟨v * y * u⁻¹, mul_mem (mul_mem hv hy) (inv_mem hu),
    by rw [mul_smul, mul_smul, inv_smul_smul, hyδ]⟩


theorem f4_exists_kill_root_cycle {τ : Tag} (hτ : τ = .F4) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (w : WeylGroup τ)
    (hw : (fun α => w • α) '' kernelRoots χ = kernelRoots χ)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots χ) :
    ∃ x ∈ Subgroup.closure (rootReflection '' kernelRoots χ), ∃ (n : ℕ) (hn : 0 < n),
      ∃ β : Fin n → Fin τ.rank → ℤ, β ⟨0, hn⟩ = α ∧ (∀ k, β k ∈ kernelRoots χ) ∧
        (∀ i j, i ≠ j → iform (β i) (β j) = 0 ∧ β i ≠ β j ∧ β i ≠ -β j ∧
          ∀ a b : ℕ, 0 < a → 0 < b → ¬ IsRoot τ (a • β i + b • β j)) ∧
        ∀ k : Fin n, (x * w) • β k = β ⟨((k : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ := by
  subst hτ
  classical
  have hw1 : ∀ a ∈ kernelRoots χ, w • a ∈ kernelRoots χ := by
    intro a ha
    have h : w • a ∈ (fun γ => w • γ) '' kernelRoots χ := ⟨a, ha, rfl⟩
    rwa [hw] at h
  have hw2 : ∀ a ∈ kernelRoots χ, w⁻¹ • a ∈ kernelRoots χ := by
    intro a ha
    have h : a ∈ (fun γ => w • γ) '' kernelRoots χ := by rwa [hw]
    obtain ⟨b, hb, hba⟩ := h
    dsimp only at hba
    rw [← hba, inv_smul_smul]
    exact hb
  have hP := kr_stab_pow hw1 hw2
  have hr : ∀ m : ℕ, (w ^ m) • α ∈ kernelRoots χ := fun m => (hP m).1 α hα
  obtain ⟨cl, hcl⟩ : ∃ cl : ℕ → KernelComponent χ,
      ∀ m, cl m = ⟦⟨(w ^ m) • α, hr m⟩⟧ := ⟨_, fun m => rfl⟩
  obtain ⟨N, hNpos, hNeq⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite w)
  have hex : ∃ m, 0 < m ∧ cl m = ⟦⟨α, hα⟩⟧ :=
    ⟨N, hNpos, (hcl N).trans (kr_mk_of_eq (hr N) hα (by rw [hNeq, one_smul]))⟩
  obtain ⟨n, hn0, hncl, hmin⟩ : ∃ n, 0 < n ∧ cl n = ⟦⟨α, hα⟩⟧ ∧
      ∀ m, 0 < m → m < n → cl m ≠ ⟦⟨α, hα⟩⟧ :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      fun m hm0 hmn hc => Nat.find_min hex hmn ⟨hm0, hc⟩⟩
  have hdist : ∀ i j : ℕ, i < j → j < n → cl i ≠ cl j := by
    intro i j hij hjn heq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
    have hd : 0 < d := by omega
    have hdn : d < n := by omega
    have c1 : (⟦⟨α, hα⟩⟧ : KernelComponent χ) =
        ⟦⟨(w ^ i)⁻¹ • ((w ^ i) • α), (hP i).2 _ (hr i)⟩⟧ :=
      kr_mk_of_eq hα ((hP i).2 _ (hr i)) (inv_smul_smul (w ^ i) α).symm
    have c2 : (⟦⟨(w ^ i)⁻¹ • ((w ^ i) • α), (hP i).2 _ (hr i)⟩⟧ : KernelComponent χ) =
        ⟦⟨(w ^ i)⁻¹ • ((w ^ (i + d)) • α), (hP i).2 _ (hr (i + d))⟩⟧ :=
      kr_mk_map χ ((w ^ i)⁻¹) (hP i).2 (hr i) (hr (i + d))
        ((hcl i).symm.trans (heq.trans (hcl (i + d))))
    have c3 : (⟦⟨(w ^ i)⁻¹ • ((w ^ (i + d)) • α), (hP i).2 _ (hr (i + d))⟩⟧ :
        KernelComponent χ) = ⟦⟨(w ^ d) • α, hr d⟩⟧ :=
      kr_mk_of_eq ((hP i).2 _ (hr (i + d))) (hr d)
        (by rw [pow_add, mul_smul, inv_smul_smul])
    exact hmin d hd hdn ((hcl d).trans (c1.trans (c2.trans c3)).symm)
  have hdistc : ∀ i j : ℕ, i < n → j < n → i ≠ j →
      (⟦⟨(w ^ i) • α, hr i⟩⟧ : KernelComponent χ) ≠ ⟦⟨(w ^ j) • α, hr j⟩⟧ := by
    intro i j hi hj hij heq
    have hcl_eq : cl i = cl j := (hcl i).trans (heq.trans (hcl j).symm)
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hdist i j h hj hcl_eq
    · exact hdist j i h hi hcl_eq.symm
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  have hwnΨ : (w ^ n) • α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ :=
    ⟨hr n, (hcl n).symm.trans hncl⟩
  obtain ⟨x0, hx0, hx0α⟩ :=
    f4_smul_of_mem_component (isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧) hwnΨ hαΨ
      (iform_smul (w ^ n) α α)
  have hfix : ∀ m : ℕ, 0 < m → m < n → x0 • ((w ^ m) • α) = (w ^ m) • α := by
    intro m hm0 hmn
    refine kr_fix_of_orth hx0 (fun γ hγ => ?_)
    obtain ⟨hγk, hγc⟩ := hγ
    refine iform_eq_zero_of_mk_ne (α := ⟨γ, hγk⟩) (β := ⟨(w ^ m) • α, hr m⟩) ?_
    intro hne
    exact hmin m hm0 hmn ((hcl m).trans (hne.symm.trans hγc))
  refine ⟨x0, kr_componentWeylGroup_le _ hx0, n, hn0, fun k => (w ^ (k : ℕ)) • α, ?_,
    fun k => hr k, ?_, ?_⟩
  · simp
  · intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := fun e => hij (Fin.ext e)
    have hc := hdistc (i : ℕ) (j : ℕ) i.2 j.2 hne
    have h0 : iform ((w ^ (i : ℕ)) • α) ((w ^ (j : ℕ)) • α) = 0 :=
      iform_eq_zero_of_mk_ne (α := ⟨(w ^ (i : ℕ)) • α, hr i⟩) (β := ⟨(w ^ (j : ℕ)) • α, hr j⟩) hc
    refine ⟨h0, fun h => hc (kr_mk_of_eq (hr i) (hr j) h), ?_,
      fun a b ha hb => not_isRoot_of_mk_ne hc ha hb⟩
    intro h
    have h' : (w ^ (i : ℕ)) • α = -((w ^ (j : ℕ)) • α) := h
    have hpos : 0 < iform ((w ^ (j : ℕ)) • α) ((w ^ (j : ℕ)) • α) :=
      iform_self_pos (IsRoot.smul hα.1 (w ^ (j : ℕ))).ne_zero
    have hneg : iform (-((w ^ (j : ℕ)) • α)) ((w ^ (j : ℕ)) • α) =
        -iform ((w ^ (j : ℕ)) • α) ((w ^ (j : ℕ)) • α) := by
      rw [← neg_one_smul ℤ ((w ^ (j : ℕ)) • α), iform_smul_left]
      ring
    rw [h'] at h0
    rw [hneg] at h0
    linarith
  · intro k
    show (x0 * w) • ((w ^ (k : ℕ)) • α) = (w ^ (((k : ℕ) + 1) % n)) • α
    rw [mul_smul, ← mul_smul w, ← pow_succ']
    by_cases hkn : (k : ℕ) + 1 < n
    · rw [Nat.mod_eq_of_lt hkn]
      exact hfix _ (by omega) hkn
    · have hk : (k : ℕ) + 1 = n := by omega
      rw [hk, Nat.mod_self, pow_zero, one_smul]
      exact hx0α

end CFSG.LieType.SeitzGeneration.ExcHighThree
