module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34Cert
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

section Quat

variable {G : Type*} [Group G]

@[expose] def quatLift (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a)
    (hba : b * a * b⁻¹ = a⁻¹) : QuaternionGroup 2 →* G where
  toFun x := match x with
    | QuaternionGroup.a i => a ^ i.val
    | QuaternionGroup.xa i => b * a ^ i.val
  map_one' := by
    show a ^ (0 : ZMod (2 * 2)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ i j : ZMod (2 * 2), a ^ i.val * a ^ j.val = a ^ (i + j).val := fun i j => by
      rw [← pow_add, pow_eq_pow_mod (i.val + j.val) ha, ← ZMod.val_add]
    have hB : ∀ i j : ZMod (2 * 2), a ^ (j - i).val = (a ^ i.val)⁻¹ * a ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hab : a * b = b * a⁻¹ := by
      have h1 : b * a = a⁻¹ * b := mul_inv_eq_iff_eq_mul.mp hba
      calc a * b = a * (b * a) * a⁻¹ := by group
        _ = a * (a⁻¹ * b) * a⁻¹ := by rw [h1]
        _ = b * a⁻¹ := by group
    have hC : ∀ k : ℕ, a ^ k * b = b * (a ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc a ^ (k + 1) * b = a ^ k * (a * b) := by rw [pow_succ, mul_assoc]
          _ = a ^ k * b * a⁻¹ := by rw [hab, mul_assoc]
          _ = b * (a ^ k)⁻¹ * a⁻¹ := by rw [ih]
          _ = b * (a ^ (k + 1))⁻¹ := by rw [pow_succ', mul_inv_rev, mul_assoc]
    rintro (i | i) (j | j)
    · show a ^ (i + j).val = a ^ i.val * a ^ j.val
      rw [hA]
    · show b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [hB, ← mul_assoc (a ^ i.val) b, hC, mul_assoc]
    · show b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [mul_assoc, hA]
    · show a ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val = b * a ^ i.val * (b * a ^ j.val)
      have h2 : (((2 : ℕ) : ZMod (2 * 2))).val = 2 := rfl
      calc a ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val
          = a ^ (((2 : ℕ) : ZMod (2 * 2)) + (j - i)).val := by rw [add_sub_assoc]
        _ = a ^ 2 * ((a ^ i.val)⁻¹ * a ^ j.val) := by rw [← hA, h2, hB]
        _ = b * b * ((a ^ i.val)⁻¹ * a ^ j.val) := by rw [hb, sq]
        _ = b * (b * (a ^ i.val)⁻¹) * a ^ j.val := by group
        _ = b * a ^ i.val * (b * a ^ j.val) := by rw [← hC]; group

theorem quatLift_a (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a) (hba : b * a * b⁻¹ = a⁻¹)
    (i : ZMod (2 * 2)) : quatLift a b ha hb hba (QuaternionGroup.a i) = a ^ i.val := rfl

theorem quatLift_xa (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a) (hba : b * a * b⁻¹ = a⁻¹)
    (i : ZMod (2 * 2)) : quatLift a b ha hb hba (QuaternionGroup.xa i) = b * a ^ i.val := rfl

theorem injective_quatLift (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a)
    (hba : b * a * b⁻¹ = a⁻¹) (hao : orderOf a = 4) (hbn : b ∉ zpowers a) :
    Function.Injective (quatLift a b ha hb hba) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro (i | i) hi <;> rw [MonoidHom.mem_ker] at hi
  · rw [quatLift_a] at hi
    have h1 : orderOf a ∣ i.val := orderOf_dvd_of_pow_eq_one hi
    rw [hao] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [ZMod.val_eq_zero] at h2
    rw [h2, mem_bot, QuaternionGroup.a_zero]
  · exfalso
    rw [quatLift_xa] at hi
    apply hbn
    rw [eq_inv_of_mul_eq_one_left hi]
    exact inv_mem (pow_mem (mem_zpowers a) _)

theorem range_quatLift (a b : G) (ha : a ^ 4 = 1) (hb : b * b = a * a)
    (hba : b * a * b⁻¹ = a⁻¹) : (quatLift a b ha hb hba).range = zpowers a ⊔ zpowers b := by
  apply le_antisymm
  · rintro _ ⟨i | i, rfl⟩
    · rw [quatLift_a]
      exact mem_sup_left (pow_mem (mem_zpowers a) _)
    · rw [quatLift_xa]
      exact mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left (pow_mem (mem_zpowers a) _))
  · refine sup_le (zpowers_le.mpr ⟨QuaternionGroup.a 1, ?_⟩)
      (zpowers_le.mpr ⟨QuaternionGroup.xa 0, ?_⟩)
    · rw [quatLift_a, show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
    · rw [quatLift_xa, ZMod.val_zero, pow_zero, mul_one]

end Quat

@[expose] def l34qa : Equiv.Perm (Fin 42) :=
  g₂ * g₁ * g₃ * g₁ * g₃ * g₁ * g₁ * g₂ * g₁ * g₁ * g₂

@[expose] def l34qb : Equiv.Perm (Fin 42) :=
  g₂ * g₁ * g₁ * g₃ * g₁ * g₁ * g₃ * g₁ * g₂ * g₁ * g₂

@[expose] def l34qaT : Tab :=
  comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42
    g₂T g₁T) g₃T) g₁T) g₃T) g₁T) g₁T) g₂T) g₁T) g₁T) g₂T

@[expose] def l34qbT : Tab :=
  comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42 (comp 42
    g₂T g₁T) g₁T) g₃T) g₁T) g₁T) g₃T) g₁T) g₂T) g₁T) g₂T

theorem tabRep_l34qa : TabRep l34qaT l34qa :=
  (((((((((tabRep_g₂.comp tabRep_g₁).comp tabRep_g₃).comp tabRep_g₁).comp tabRep_g₃).comp
    tabRep_g₁).comp tabRep_g₁).comp tabRep_g₂).comp tabRep_g₁).comp tabRep_g₁).comp tabRep_g₂

theorem tabRep_l34qb : TabRep l34qbT l34qb :=
  (((((((((tabRep_g₂.comp tabRep_g₁).comp tabRep_g₁).comp tabRep_g₃).comp tabRep_g₁).comp
    tabRep_g₁).comp tabRep_g₃).comp tabRep_g₁).comp tabRep_g₂).comp tabRep_g₁).comp tabRep_g₂

theorem l34q_tab_facts :
    comp 42 l34qaT (comp 42 l34qaT (comp 42 l34qaT l34qaT)) = idTab 42 ∧
      comp 42 l34qaT l34qaT ≠ idTab 42 ∧
      comp 42 l34qbT l34qbT = comp 42 l34qaT l34qaT ∧
      comp 42 l34qbT l34qaT = comp 42 (comp 42 l34qaT (comp 42 l34qaT l34qaT)) l34qbT ∧
      l34qbT ≠ idTab 42 ∧ l34qbT ≠ l34qaT ∧ l34qbT ≠ comp 42 l34qaT l34qaT ∧
      l34qbT ≠ comp 42 l34qaT (comp 42 l34qaT l34qaT) ∧
      comp 42 l34qaT r₄T = comp 42 r₄T l34qaT ∧ comp 42 l34qbT r₄T = comp 42 r₄T l34qbT ∧
      comp 42 g₅T g₆T = comp 42 g₆T g₅T := by
  decide +kernel

theorem g₅_mul_g₆ : g₅ * g₆ = g₆ * g₅ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := l34q_tab_facts
  exact ((tabRep_g₅.comp tabRep_g₆).eq_iff (tabRep_g₆.comp tabRep_g₅)).mp h

theorem l34q_mem_C₄ : l34qa ∈ C₄ ∧ l34qb ∈ C₄ := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -⟩ := l34q_tab_facts
  have hc1 : l34qa * r₄ = r₄ * l34qa :=
    ((tabRep_l34qa.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_l34qa)).mp h1
  have hc2 : l34qb * r₄ = r₄ * l34qb :=
    ((tabRep_l34qb.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_l34qb)).mp h2
  have h1S := g₁_mem_S
  have h2S := g₂_mem_S
  have h3S := g₃_mem_S
  refine ⟨mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc1, ?_⟩,
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc2, ?_⟩⟩
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem h2S h1S) h3S) h1S) h3S) h1S) h1S) h2S) h1S) h1S) h2S
  · exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
      (mul_mem h2S h1S) h1S) h3S) h1S) h1S) h3S) h1S) h2S) h1S) h2S

theorem l34q_relations : l34qa ^ 4 = 1 ∧ orderOf l34qa = 4 ∧ l34qb * l34qb = l34qa * l34qa ∧
    l34qb * l34qa * l34qb⁻¹ = l34qa⁻¹ ∧ l34qb ∉ zpowers l34qa := by
  obtain ⟨h4, h2, hbb, hba, h0, h1', h2', h3', -, -, -⟩ := l34q_tab_facts
  have hx := tabRep_l34qa
  have hx2 := hx.comp hx
  have hx3 := hx.comp hx2
  have hx4 := hx.comp hx3
  have hp4 : l34qa ^ 4 = 1 := by
    rw [show l34qa ^ 4 = l34qa * (l34qa * (l34qa * l34qa)) by
      simp only [pow_succ', pow_zero, mul_one]]
    exact (hx4.eq_iff TabRep.idTab).mp h4
  have hp2 : l34qa ^ 2 ≠ 1 := by
    rw [pow_two]
    exact fun h => h2 ((hx2.eq_iff TabRep.idTab).mpr h)
  have hord : orderOf l34qa = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := l34qa) (by simpa using hp2)
      (by simpa using hp4)
    simpa using this
  have hbb' : l34qb * l34qb = l34qa * l34qa :=
    ((tabRep_l34qb.comp tabRep_l34qb).eq_iff hx2).mp hbb
  have hba' : l34qb * l34qa = l34qa * (l34qa * l34qa) * l34qb :=
    ((tabRep_l34qb.comp hx).eq_iff (hx3.comp tabRep_l34qb)).mp hba
  have hinv : l34qa * (l34qa * l34qa) = l34qa⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc l34qa * (l34qa * l34qa) * l34qa = l34qa ^ 4 := by
          simp only [pow_succ', pow_zero, mul_one, mul_assoc]
      _ = 1 := hp4
  have hrel : l34qb * l34qa * l34qb⁻¹ = l34qa⁻¹ := by
    rw [hba', hinv, mul_inv_cancel_right]
  refine ⟨hp4, hord, hbb', hrel, fun hmem => ?_⟩
  rw [mem_zpowers_iff_mem_range_orderOf, hord] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hkx⟩ := hmem
  interval_cases k
  · exact h0 ((tabRep_l34qb.eq_iff TabRep.idTab).mpr (by simpa using hkx.symm))
  · exact h1' ((tabRep_l34qb.eq_iff hx).mpr (by simpa using hkx.symm))
  · exact h2' ((tabRep_l34qb.eq_iff hx2).mpr (by rw [← hkx, pow_two]))
  · exact h3' ((tabRep_l34qb.eq_iff hx3).mpr
      (by rw [← hkx]; simp only [pow_succ', pow_zero, mul_one]))

theorem nonempty_quaternion_sylow_C₄ (P : Sylow 2 ↥C₄) :
    Nonempty (QuaternionGroup 2 ≃* ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, hord, hbb, hrel, hnot⟩ := l34q_relations
  obtain ⟨haC, hbC⟩ := l34q_mem_C₄
  have hinj := injective_quatLift l34qa l34qb h4 hbb hrel hord hnot
  have hrange := range_quatLift l34qa l34qb h4 hbb hrel
  set Q := zpowers l34qa ⊔ zpowers l34qb with hQ
  have hQC : Q ≤ C₄ := sup_le (zpowers_le.mpr haC) (zpowers_le.mpr hbC)
  have hQcard : Nat.card Q = 8 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hfac : (Nat.card C₄).factorization 2 = 3 := by
    rw [card_C₄, show (72 : ℕ) = 2 ^ 3 * 9 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcard : Nat.card (Q.subgroupOf C₄) = 2 ^ (Nat.card C₄).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv, hQcard, hfac]
    norm_num
  have e₀ : QuaternionGroup 2 ≃* ↥(Q.subgroupOf C₄) :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
      (subgroupOfEquivOfLe hQC).symm
  exact ⟨(e₀.trans (MulEquiv.subgroupCongr (Sylow.coe_ofCard _ hcard).symm)).trans
    (Sylow.equiv (Sylow.ofCard _ hcard) P)⟩

theorem card_centralizer_r₂R : Nat.card (centralizer ({r₂R} : Set R)) = 672 := by
  have h1 := MulAction.index_stabilizer (ConjAct R) r₂R
  rw [ConjAct.orbit_eq_carrier_conjClasses, ← Nat.card_coe_set_eq, conjClass₂.2] at h1
  have h2 := (MulAction.stabilizer (ConjAct R) r₂R).card_mul_index
  rw [h1, Nat.card_congr (ConjAct.toConjAct : R ≃* ConjAct R).toEquiv.symm, card_R] at h2
  have h3 : Nat.card (MulAction.stabilizer (ConjAct R) r₂R) = 672 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h2.trans (by norm_num))
  rw [centralizer_eq_comap_stabilizer, ← h3]
  have hs : Function.Surjective (ConjAct.toConjAct : R ≃* ConjAct R).toMonoidHom :=
    (ConjAct.toConjAct : R ≃* ConjAct R).surjective
  have h4 := Subgroup.card_map_of_injective (K := (MulAction.stabilizer (ConjAct R) r₂R).comap
    (ConjAct.toConjAct : R ≃* ConjAct R).toMonoidHom)
    (f := (ConjAct.toConjAct : R ≃* ConjAct R).toMonoidHom)
    (ConjAct.toConjAct : R ≃* ConjAct R).injective
  rw [map_comap_eq_self_of_surjective hs] at h4
  exact h4.symm

theorem card_centralizer_r₂R_inf_S :
    Nat.card ↥(centralizer ({r₂R} : Set R) ⊓ S.subgroupOf R) = 168 := by
  have hmap : (centralizer ({r₂R} : Set R) ⊓ S.subgroupOf R).map R.subtype = C₂ := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, mem_subgroupOf, C₂]
    constructor
    · rintro ⟨y, ⟨hy, hyS⟩, rfl⟩
      exact ⟨congrArg Subtype.val hy, hyS⟩
    · rintro ⟨hx, hxS⟩
      exact ⟨⟨x, S_le_R hxS⟩, ⟨Subtype.ext hx, hxS⟩, rfl⟩
  rw [← card_C₂, ← hmap, Subgroup.card_map_of_injective R.subtype_injective]

theorem mem_cosets_of_comm_g₅ {s : Equiv.Perm (Fin 42)} (hs : s ∈ R) (hc : s * g₅ = g₅ * s) :
    s ∈ S ∨ g₅⁻¹ * s ∈ S ∨ g₆⁻¹ * s ∈ S ∨ (g₅ * g₆)⁻¹ * s ∈ S := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h0, h1, h2, h3⟩ := hcon
  set C := centralizer ({r₂R} : Set R) with hCdef
  set H := (centralizer ({r₂R} : Set R) ⊓ S.subgroupOf R).subgroupOf C with hHdef
  have hidx : H.index = 4 := by
    have h := H.card_mul_index
    have hH : Nat.card H = 168 := by
      rw [hHdef, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,
        card_centralizer_r₂R_inf_S]
    have hC : Nat.card C = 672 := card_centralizer_r₂R
    rw [hH, hC] at h
    omega
  have hg5 : g₅ * g₅ = 1 := g₅_mul_g₅
  have hg6 : g₆ * g₆ = 1 := g₆_mul_g₆
  have hcomm := g₅_mul_g₆
  have hmem : ∀ (y : Equiv.Perm (Fin 42)) (hy : y ∈ R), y * g₅ = g₅ * y →
      (⟨y, hy⟩ : R) ∈ C := fun y hy hyc => by
    rw [hCdef, mem_centralizer_singleton_iff]
    exact Subtype.ext hyc
  have hR5 : g₅ ∈ R := g₅_mem_R
  have hR6 : g₆ ∈ R := g₆_mem_R
  let e : Fin 5 → Equiv.Perm (Fin 42) := ![1, g₅, g₆, g₅ * g₆, s]
  have heR : ∀ k, e k ∈ R := by
    intro k
    fin_cases k
    exacts [one_mem _, hR5, hR6, mul_mem hR5 hR6, hs]
  have hec : ∀ k, e k * g₅ = g₅ * e k := by
    intro k
    fin_cases k
    · show 1 * g₅ = g₅ * 1
      rw [one_mul, mul_one]
    · rfl
    · exact hcomm.symm
    · show g₅ * g₆ * g₅ = g₅ * (g₅ * g₆)
      rw [mul_assoc, ← hcomm]
    · exact hc
  let f : Fin 5 → ↥C ⧸ H := fun k => (⟨⟨e k, heR k⟩, hmem _ (heR k) (hec k)⟩ : C)
  have hnS : ∀ k l : Fin 5, k < l → (e k)⁻¹ * e l ∉ S := by
    have n56 : g₅⁻¹ * g₆ ∉ S := CatFactsL4U4.repP_inv_mul_not_mem (i := 1) (j := 4)
      (by norm_num) (by norm_num) (by norm_num)
    have n67 : g₆⁻¹ * (g₅ * g₆) ∉ S := CatFactsL4U4.repP_inv_mul_not_mem (i := 4) (j := 7)
      (by norm_num) (by norm_num) (by norm_num)
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first | exact absurd hkl (by decide) | skip
    · show (1 : Equiv.Perm (Fin 42))⁻¹ * g₅ ∉ S
      rw [inv_one, one_mul]
      exact not_mem_S_r₂
    · show (1 : Equiv.Perm (Fin 42))⁻¹ * g₆ ∉ S
      rw [inv_one, one_mul]
      exact not_mem_S_r₃
    · show (1 : Equiv.Perm (Fin 42))⁻¹ * (g₅ * g₆) ∉ S
      rw [inv_one, one_mul]
      exact not_mem_S_r₄
    · show (1 : Equiv.Perm (Fin 42))⁻¹ * s ∉ S
      rw [inv_one, one_mul]
      exact h0
    · exact n56
    · show g₅⁻¹ * (g₅ * g₆) ∉ S
      rw [← mul_assoc, inv_mul_cancel, one_mul]
      exact not_mem_S_r₃
    · exact h1
    · exact n67
    · exact h2
    · exact h3
  have hf : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have hmemH : ∀ k l : Fin 5, f k = f l → (e k)⁻¹ * e l ∈ S := by
      intro k l h
      have h' := QuotientGroup.eq.mp h
      rw [hHdef, mem_subgroupOf, mem_inf, mem_subgroupOf] at h'
      exact h'.2
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hnS k l hlt (hmemH k l hkl)
    · exact hnS l k hlt (hmemH l k hkl.symm)
  have h5 : Nat.card (Fin 5) ≤ H.index := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hidx] at h5
  omega

theorem conj_r₃_r₄_of_comm_g₅ {s : Equiv.Perm (Fin 42)} (hs : s ∈ R) (hs2 : s * s = 1)
    (hc : s * g₅ = g₅ * s) (h0 : s ∉ S) (h1 : g₅⁻¹ * s ∉ S) :
    ((∃ y ∈ S, y * r₃ * y⁻¹ = s) ∧ ∃ y ∈ S, y * r₄ * y⁻¹ = s * g₅) ∨
      ((∃ y ∈ S, y * r₄ * y⁻¹ = s) ∧ ∃ y ∈ S, y * r₃ * y⁻¹ = s * g₅) := by
  have hg5 : g₅ * g₅ = 1 := g₅_mul_g₅
  have hg6 : g₆ * g₆ = 1 := g₆_mul_g₆
  have hcomm := g₅_mul_g₆
  have hg5i : g₅⁻¹ = g₅ := inv_eq_of_mul_eq_one_right hg5
  have hg6i : g₆⁻¹ = g₆ := inv_eq_of_mul_eq_one_right hg6
  have hR5 : g₅ ∈ R := g₅_mem_R
  have hR6 : g₆ ∈ R := g₆_mem_R
  have hs1 : s ≠ 1 := fun h => h0 (h ▸ one_mem _)
  have hsg : s * g₅ ∈ R := mul_mem hs hR5
  have hsg2 : s * g₅ * (s * g₅) = 1 := by
    calc s * g₅ * (s * g₅) = s * (g₅ * s) * g₅ := by group
      _ = s * (s * g₅) * g₅ := by rw [hc]
      _ = (s * s) * (g₅ * g₅) := by group
      _ = 1 := by rw [hs2, hg5, one_mul]
  have hsg1 : s * g₅ ≠ 1 := by
    intro h
    apply h1
    rw [show s = g₅⁻¹ from eq_inv_of_mul_eq_one_left h, hg5i, hg5]
    exact one_mem _
  have hr3 : r₃ * r₃ = 1 := hg6
  have hr4 : r₄ * r₄ = 1 := by
    change g₅ * g₆ * (g₅ * g₆) = 1
    calc g₅ * g₆ * (g₅ * g₆) = g₅ * (g₆ * g₅) * g₆ := by group
      _ = g₅ * (g₅ * g₆) * g₆ := by rw [hcomm]
      _ = (g₅ * g₅) * (g₆ * g₆) := by group
      _ = 1 := by rw [hg5, hg6, one_mul]
  have hr3R : r₃ ∈ R := hR6
  have hr4R : r₄ ∈ R := mul_mem hR5 hR6
  have hr31 : r₃ ≠ 1 := fun h => not_mem_S_r₃ (h ▸ one_mem _)
  have hr41 : r₄ ≠ 1 := fun h => not_mem_S_r₄ (h ▸ one_mem _)
  rcases mem_cosets_of_comm_g₅ hs hc with h | h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · left
    refine ⟨CatFactsL4U4.conj_of_mul_mem_S hr3R hs hr3 hs2 hr31 hs1 h,
      CatFactsL4U4.conj_of_mul_mem_S hr4R hsg hr4 hsg2 hr41 hsg1 ?_⟩
    change (g₅ * g₆)⁻¹ * (s * g₅) ∈ S
    have e1 : (g₅ * g₆)⁻¹ * (s * g₅) = g₆⁻¹ * (g₅⁻¹ * s * g₅) := by group
    rw [e1, hg5i, ← hc, mul_assoc s, hg5, mul_one]
    exact h
  · right
    refine ⟨CatFactsL4U4.conj_of_mul_mem_S hr4R hs hr4 hs2 hr41 hs1 h,
      CatFactsL4U4.conj_of_mul_mem_S hr3R hsg hr3 hsg2 hr31 hsg1 ?_⟩
    change g₆⁻¹ * (s * g₅) ∈ S
    have e1 : (g₅ * g₆)⁻¹ * s = g₆⁻¹ * (g₅⁻¹ * s) := by group
    rw [hc, ← mul_assoc, ← hg5i, mul_assoc, ← e1]
    exact h

end CFSG.ComponentClassification.HarrisLit.HarrisEnd
