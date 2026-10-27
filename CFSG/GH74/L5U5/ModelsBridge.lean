module

public import CFSG.GH74.L5U5.ModelsInvolution

public section

namespace CFSG.GH74.L5U5

open CFSG.GH74 CFSG.GH74.Filter CFSG.GH74.Filter.ClassicalOdd
  CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

section Counting

variable {C : Type*} [Group C]

theorem q8Frattini_a_two : q8Frattini (QuaternionGroup.a 2) = 1 := by decide

theorem q8Frattini_eq_one_of_central (g : Q8) (hg : ∀ x, g * x = x * g) : q8Frattini g = 1 := by
  rcases quaternion_center g hg with rfl | rfl
  · exact map_one _
  · exact q8Frattini_a_two

theorem V4_sq : ∀ a : V4, a ^ 2 = 1 := by decide

theorem central_of_comm_q8q8 {φ : Q8 × Q8 →* C} (hφ : Function.Injective φ) {g : Q8 × Q8}
    (hg : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a) : ∀ a : Q8 × Q8, g * a = a * g := by
  intro a
  apply hφ
  rw [map_mul, map_mul]
  exact (hg a).symm

theorem q8q8_commuting_two_subgroup_le [Finite C] (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : Function.Injective φ) (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) : T ≤ φ.range := by
  by_contra hnot
  set M : Subgroup T := φ.range.subgroupOf T with hM
  have hMc : ∀ t ∈ M, ∀ s : T, s * t = t * s := by
    intro t ht s
    obtain ⟨a, ha⟩ := (Subgroup.mem_subgroupOf.1 ht)
    apply Subtype.ext
    change (s : C) * (t : C) = (t : C) * (s : C)
    rw [← ha]
    exact (hcomm a s s.2).symm
  have hMn : M.Normal :=
    ⟨fun n hn g => by
      have : g * n * g⁻¹ = n := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hMc n hn g
      rw [this]
      exact hn⟩
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply hnot
    intro t ht
    have : (⟨t, ht⟩ : T) ∈ M := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hQ : IsPGroup 2 (T ⧸ M) := hT.to_quotient M
  have hnil : Group.IsNilpotent (T ⧸ M) := hQ.isNilpotent
  have hdvd : 2 ∣ Nat.card (T ⧸ M) := by
    rcases hQ.card_eq_or_dvd with h | h
    · exfalso
      apply hMtop
      rw [← Subgroup.index_eq_one, Subgroup.index_eq_card]
      exact h
    · exact h
  obtain ⟨H, hHidx, hHn⟩ :=
    Group.IsNilpotent.exists_normal_index_eq_of_dvd_card (G := T ⧸ M) (k := 2) hdvd
  have _ := hHn
  have hEcard : Nat.card ((T ⧸ M) ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card]; exact hHidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEcyc : IsCyclic ((T ⧸ M) ⧸ H) := isCyclic_of_prime_card hEcard
  let _ : CommGroup ((T ⧸ M) ⧸ H) := IsCyclic.commGroup
  have hEsq : ∀ e : (T ⧸ M) ⧸ H, e ^ 2 = 1 := fun e => by
    rw [← hEcard]; exact pow_card_eq_one'
  let τ : T →* (T ⧸ M) ⧸ H := (QuotientGroup.mk' H).comp (QuotientGroup.mk' M)
  have hτ : Function.Surjective τ :=
    (QuotientGroup.mk'_surjective H).comp (QuotientGroup.mk'_surjective M)
  let α : (Q8 × Q8) × T →* C :=
    MonoidHom.noncommCoprod φ T.subtype (fun a t => (hcomm a t t.2 : _))
  let β : (Q8 × Q8) × T →* (V4 × V4) × ((T ⧸ M) ⧸ H) :=
    (q8Frattini.prodMap q8Frattini).prodMap τ
  have hβ : Function.Surjective β :=
    (q8Frattini_surjective.prodMap q8Frattini_surjective).prodMap hτ
  refine not_gen4_of_surjection α β hβ ?_ ?_ ?_ ?_ hC
  · intro a b
    exact Prod.ext (Prod.ext (mul_comm _ _) (mul_comm _ _)) (mul_comm _ _)
  · intro a
    exact Prod.ext (Prod.ext (V4_sq _) (V4_sq _)) (hEsq _)
  · rw [Nat.card_prod, Nat.card_prod, card_V4, hEcard]
    norm_num
  · rintro ⟨g, t⟩ hgt
    rw [MonoidHom.mem_ker] at hgt ⊢
    have h1 : φ g * (t : C) = 1 := hgt
    have htg : (t : C) = (φ g)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have htM : t ∈ M := by
      rw [hM, Subgroup.mem_subgroupOf, htg]
      exact φ.range.inv_mem ⟨g, rfl⟩
    have hcent : ∀ a : Q8 × Q8, φ a * φ g = φ g * φ a := by
      intro a
      have hgT : φ g ∈ T := by
        have : (φ g) = ((t : C))⁻¹ := by rw [htg, inv_inv]
        rw [this]
        exact T.inv_mem t.2
      exact hcomm a (φ g) hgT
    have hgc := central_of_comm_q8q8 hφ hcent
    have hg1 : ∀ x : Q8, g.1 * x = x * g.1 := fun x => by
      have := congrArg Prod.fst (hgc (x, 1))
      simpa using this
    have hg2 : ∀ x : Q8, g.2 * x = x * g.2 := fun x => by
      have := congrArg Prod.snd (hgc (1, x))
      simpa using this
    change ((q8Frattini g.1, q8Frattini g.2), τ t) = 1
    refine Prod.ext (Prod.ext (q8Frattini_eq_one_of_central _ hg1)
      (q8Frattini_eq_one_of_central _ hg2)) ?_
    change τ t = 1
    have : (QuotientGroup.mk' M) t = 1 := (QuotientGroup.eq_one_iff t).2 htM
    change (QuotientGroup.mk' H) ((QuotientGroup.mk' M) t) = 1
    rw [this, map_one]

end Counting

section Consequences

variable {C : Type*} [Group C] [Finite C]

theorem q8q8_commuting_two_subgroup_le_center (hC : Gen4 C) (φ : Q8 × Q8 →* C)
    (hφ : Function.Injective φ) (T : Subgroup C) (hT : IsPGroup 2 T)
    (hcomm : ∀ (a : Q8 × Q8) (t : C), t ∈ T → φ a * t = t * φ a) :
    ∀ t ∈ T, ∃ g : Q8 × Q8, φ g = t ∧ ∀ a : Q8 × Q8, g * a = a * g := by
  intro t ht
  obtain ⟨g, hg⟩ := q8q8_commuting_two_subgroup_le hC φ hφ T hT hcomm ht
  refine ⟨g, hg, central_of_comm_q8q8 hφ fun a => ?_⟩
  rw [hg]
  exact hcomm a t ht

omit [Finite C] in
theorem isPGroup_zpowers_of_orderOf_eq_two {g : C} (h : orderOf g = 2) :
    IsPGroup 2 (Subgroup.zpowers g) := by
  have hg : g ^ 2 = 1 := h ▸ pow_orderOf_eq_one g
  rintro ⟨a, ha⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine ⟨1, ?_⟩
  apply Subtype.ext
  change (g ^ n) ^ (2 ^ 1) = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

omit [Finite C] in
theorem isPGroup_two_sup_zpowers (A : Subgroup C) (hA : IsPGroup 2 A) (w : C) (hw : w * w = 1)
    (hnorm : ∀ a ∈ A, w * a * w⁻¹ ∈ A) : IsPGroup 2 ↥(A ⊔ Subgroup.zpowers w) := by
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hnorm' : ∀ a ∈ A, w * a * w ∈ A := fun a ha => by
    have := hnorm a ha
    rwa [hwinv] at this
  have key : ∀ g ∈ A ⊔ Subgroup.zpowers w, g ∈ A ∨ g * w ∈ A := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · exact Or.inl hg
      · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        have hw2 : w ^ 2 = 1 := by rw [sq]; exact hw
        obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
        · left
          rw [zpow_mul, zpow_ofNat, hw2, one_zpow]
          exact A.one_mem
        · right
          rw [zpow_add_one, zpow_mul, zpow_ofNat, hw2, one_zpow, one_mul, hw]
          exact A.one_mem
    | one => exact Or.inl A.one_mem
    | mul g₁ g₂ _ _ h₁ h₂ =>
      rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
      · exact Or.inl (A.mul_mem h₁ h₂)
      · exact Or.inr (by rw [mul_assoc]; exact A.mul_mem h₁ h₂)
      · refine Or.inr ?_
        have : g₁ * g₂ * w = (g₁ * w) * (w * g₂ * w) := by
          calc g₁ * g₂ * w = g₁ * (w * w) * g₂ * w := by rw [hw, mul_one]
            _ = (g₁ * w) * (w * g₂ * w) := by group
        rw [this]
        exact A.mul_mem h₁ (hnorm' _ h₂)
      · refine Or.inl ?_
        have : g₁ * g₂ = (g₁ * w) * (w * (g₂ * w) * w) := by
          calc g₁ * g₂ = g₁ * (w * w) * g₂ * (w * w) := by rw [hw]; group
            _ = (g₁ * w) * (w * (g₂ * w) * w) := by group
        rw [this]
        exact A.mul_mem h₁ (hnorm' _ h₂)
    | inv g _ h =>
      rcases h with h | h
      · exact Or.inl (A.inv_mem h)
      · refine Or.inr ?_
        have : g⁻¹ * w = w * (w * g⁻¹) * w := by
          calc g⁻¹ * w = (w * w) * g⁻¹ * w := by rw [hw, one_mul]
            _ = w * (w * g⁻¹) * w := by group
        have h' : w * g⁻¹ ∈ A := by
          have := A.inv_mem h
          rwa [mul_inv_rev, hwinv] at this
        rw [this]
        exact hnorm' _ h'
  rintro ⟨g, hg⟩
  rcases key g hg with hgA | hgw
  · obtain ⟨k, hk⟩ := hA ⟨g, hgA⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  · have hg2 : g ^ 2 ∈ A := by
      have : g ^ 2 = (g * w) * (w * (g * w) * w) := by
        calc g ^ 2 = g * g := sq g
          _ = g * (w * w) * g * (w * w) := by rw [hw]; group
          _ = (g * w) * (w * (g * w) * w) := by group
      rw [this]
      exact A.mul_mem hgw (hnorm' _ hgw)
    obtain ⟨k, hk⟩ := hA ⟨g ^ 2, hg2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : (g ^ 2) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    change g ^ (2 ^ (k + 1)) = 1
    rw [pow_succ, mul_comm, pow_mul]
    exact h1

omit [Finite C] in
theorem card_Q8 : Nat.card Q8 = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

omit [Finite C] in
theorem isPGroup_range_q8q8 (φ : Q8 × Q8 →* C) : IsPGroup 2 φ.range := by
  rintro ⟨c, a, rfl⟩
  refine ⟨6, Subtype.ext ?_⟩
  change (φ a) ^ (2 ^ 6) = 1
  have h64 : a ^ 64 = 1 := by
    have := pow_card_eq_one' (G := Q8 × Q8) (x := a)
    rwa [Nat.card_prod, card_Q8] at this
  rw [← map_pow, show (2 : ℕ) ^ 6 = 64 by norm_num, h64, map_one]

omit [Finite C] in
theorem exists_conj_sylow {p : ℕ} [Fact p.Prime] [Finite C] (P Q : Sylow p C) :
    ∃ g : C, ∀ m : C, m ∈ (Q : Subgroup C) ↔ g⁻¹ * m * g ∈ (P : Subgroup C) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P Q
  refine ⟨g, fun m => ?_⟩
  rw [← hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hs
  · intro h
    refine ⟨g⁻¹ * m * g, h, ?_⟩
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]

end Consequences

section Bridge

open CFSG

variable {G : Type} [Group G]

@[expose] def xbar (x : G) : CentralizerBar x :=
  QuotientGroup.mk
    (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G)))

theorem xbar_mem_center (x : G) : xbar x ∈ Subgroup.center (CentralizerBar x) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  change (QuotientGroup.mk g' : CentralizerBar x) * QuotientGroup.mk _ =
    QuotientGroup.mk _ * QuotientGroup.mk g'
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_iff.1 g'.2 x (Set.mem_singleton x)).symm

theorem xbar_mul_self {x : G} (hx : orderOf x = 2) : xbar x * xbar x = 1 := by
  change (QuotientGroup.mk _ : CentralizerBar x) * QuotientGroup.mk _ = 1
  rw [← QuotientGroup.mk_mul]
  have : (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G))) *
      ⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ = 1 :=
    Subtype.ext (by
      change x * x = 1
      rw [← sq, ← hx]
      exact pow_orderOf_eq_one x)
  rw [this]
  exact (QuotientGroup.mk_one _)

theorem xbar_ne_one [Finite G] {x : G} (hx : orderOf x = 2) : xbar x ≠ 1 := by
  intro h
  have hmem := (QuotientGroup.eq_one_iff _).1 h
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  have hord : orderOf (⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh; rw [hh]⟩ : ↥(Subgroup.centralizer ({x} : Set G))) = 2 := by
    rw [← hx]
    exact Subgroup.orderOf_mk _ _
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥(Subgroup.centralizer ({x} : Set G)))
  rw [hord] at hdvd
  exact absurd (hcop.eq_one_of_dvd hdvd) (by norm_num)

theorem orderOf_xbar [Finite G] {x : G} (hx : orderOf x = 2) : orderOf (xbar x) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact xbar_mul_self hx) (xbar_ne_one hx)

theorem gen4_centralizerBar [Finite G] (hG : Gen4 G) (x : G) : Gen4 (CentralizerBar x) :=
  Gen4.quotient _ (Gen4.subgroup _ hG)

theorem commute_of_mem_zpowers_xbar (x : G) (c : CentralizerBar x) {t : CentralizerBar x}
    (ht : t ∈ Subgroup.zpowers (xbar x)) : c * t = t * c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have h : Commute c (xbar x) := Subgroup.mem_center_iff.1 (xbar_mem_center x) c
  exact (h.zpow_right k).eq

variable [Finite G]

theorem layer_frame (hG : Gen4 G) {x : G} (hx : orderOf x = 2) (hL : IsSL4Model ↥(layerBar x)) :
    ∃ (z : ↥(layerBar x)) (φ : Q8 × Q8 →* ↥(layerBar x)) (w : ↥(layerBar x)),
      orderOf z = 2 ∧ (∀ g, g ∈ Subgroup.center ↥(layerBar x) ↔ g = 1 ∨ g = z) ∧
      Function.Injective φ ∧ φ (QuaternionGroup.a 2, QuaternionGroup.a 2) = z ∧ w * w = 1 ∧
      (∀ g h : Q8, w * φ (g, h) * w⁻¹ = φ (h, g)) ∧ (z : CentralizerBar x) = xbar x := by
  obtain ⟨z, φ, w, hz2, hcenter, hφ, hφz, hww, hsw⟩ := hL.exists_q8_frame
  let Φ : Q8 × Q8 →* CentralizerBar x := (layerBar x).subtype.comp φ
  have hΦ : Function.Injective Φ := (layerBar x).subtype_injective.comp hφ
  have hC := gen4_centralizerBar hG x
  have hT : Subgroup.zpowers (xbar x) ≤ Φ.range :=
    q8q8_commuting_two_subgroup_le hC Φ hΦ _
      (isPGroup_zpowers_of_orderOf_eq_two (orderOf_xbar hx))
      (fun a t ht => commute_of_mem_zpowers_xbar x (Φ a) ht)
  have hmem : xbar x ∈ layerBar x := by
    obtain ⟨a, ha⟩ := hT (Subgroup.mem_zpowers _)
    rw [← ha]
    exact (φ a).2
  have hcentral : (⟨xbar x, hmem⟩ : ↥(layerBar x)) ∈ Subgroup.center ↥(layerBar x) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center x) (g : CentralizerBar x))
  have hne : (⟨xbar x, hmem⟩ : ↥(layerBar x)) ≠ 1 := fun h =>
    xbar_ne_one hx (congrArg Subtype.val h)
  have hzz : (⟨xbar x, hmem⟩ : ↥(layerBar x)) = z :=
    ((hcenter _).1 hcentral).resolve_left hne
  exact ⟨z, φ, w, hz2, hcenter, hφ, hφz, hww, hsw, by rw [← hzz]⟩

theorem layer_isFrame (hG : Gen4 G) {x : G} (hx : orderOf x = 2) (hL : IsSL4Model ↥(layerBar x)) :
    ∃ (q : ℕ) (F' : Type) (_ : Field F') (_ : Finite F') (z y : ↥(layerBar x))
      (J₂ J₄ : Subgroup ↥(layerBar x)),
      (z : CentralizerBar x) = xbar x ∧ Nat.card F' = q ∧ Odd q ∧ IsFrame F' z y J₂ J₄ := by
  obtain ⟨z, -, -, -, hcenter, -, -, -, -, hzx⟩ := layer_frame hG hx hL
  obtain ⟨q, F', _, _, x', y, J₂, J₄, hq, hodd, hfr⟩ := hL.exists_frame
  have hx'z : x' = z := ((hcenter x').1 hfr.x_mem_center).resolve_left (fun h => by
    have := hfr.orderOf_x
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num))
  subst hx'z
  exact ⟨q, F', inferInstance, inferInstance, x', y, J₂, J₄, hzx, hq, hodd, hfr⟩

theorem xbar_mem_layerBar (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) : xbar x ∈ layerBar x := by
  obtain ⟨z, -, -, -, -, -, -, -, -, hzx⟩ := layer_frame hG hx hL
  rw [← hzx]
  exact z.2

theorem centralizer_layer_twoSubgroup_le (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) (T : Subgroup (CentralizerBar x)) (hT : IsPGroup 2 T)
    (hTc : ∀ t ∈ T, ∀ l ∈ layerBar x, t * l = l * t) : T ≤ Subgroup.zpowers (xbar x) := by
  obtain ⟨z, φ, w, hz2, hcenter, hφ, -, -, -, hzx⟩ := layer_frame hG hx hL
  let Φ : Q8 × Q8 →* CentralizerBar x := (layerBar x).subtype.comp φ
  have hΦ : Function.Injective Φ := (layerBar x).subtype_injective.comp hφ
  have hC := gen4_centralizerBar hG x
  intro t ht
  obtain ⟨g, hg, -⟩ := q8q8_commuting_two_subgroup_le_center hC Φ hΦ T hT
    (fun a t' ht' => (hTc t' ht' (Φ a) (φ a).2).symm) t ht
  have hcent : φ g ∈ Subgroup.center ↥(layerBar x) := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    change (l : CentralizerBar x) * ((φ g : ↥(layerBar x)) : CentralizerBar x) =
      ((φ g : ↥(layerBar x)) : CentralizerBar x) * (l : CentralizerBar x)
    have : ((φ g : ↥(layerBar x)) : CentralizerBar x) = t := hg
    rw [this]
    exact (hTc t ht l l.2).symm
  have hgt : ((φ g : ↥(layerBar x)) : CentralizerBar x) = t := hg
  rcases (hcenter _).1 hcent with h | h
  · rw [← hgt, h]
    exact Subgroup.one_mem _
  · rw [← hgt, h, hzx]
    exact Subgroup.mem_zpowers _

theorem center_sylow_centralizerBar (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) (S : Sylow 2 (CentralizerBar x)) :
    ∀ s ∈ (S : Subgroup (CentralizerBar x)),
      ((∀ s' ∈ (S : Subgroup (CentralizerBar x)), s' * s = s * s') ↔
        s ∈ Subgroup.zpowers (xbar x)) := by
  intro s hs
  constructor
  · intro hsc
    obtain ⟨z, φ, w, hz2, hcenter, hφ, hφz, hww, hsw, hzx⟩ := layer_frame hG hx hL
    let Φ : Q8 × Q8 →* CentralizerBar x := (layerBar x).subtype.comp φ
    have hΦ : Function.Injective Φ := (layerBar x).subtype_injective.comp hφ
    have hC := gen4_centralizerBar hG x
    let w' : CentralizerBar x := (w : CentralizerBar x)
    have hw' : w' * w' = 1 := congrArg Subtype.val hww
    have hnorm : ∀ a ∈ Φ.range, w' * a * w'⁻¹ ∈ Φ.range := by
      rintro _ ⟨⟨g, h⟩, rfl⟩
      refine ⟨(h, g), ?_⟩
      change ((φ (h, g) : ↥(layerBar x)) : CentralizerBar x) = _
      rw [← hsw g h]
      rfl
    have hP := isPGroup_two_sup_zpowers Φ.range (isPGroup_range_q8q8 Φ) w' hw' hnorm
    obtain ⟨S₁, hS₁⟩ := hP.exists_le_sylow
    have hAS : Φ.range ≤ S₁ := le_trans le_sup_left hS₁
    have hwS : w' ∈ (S₁ : Subgroup (CentralizerBar x)) :=
      hS₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w'))
    obtain ⟨g, hg⟩ := exists_conj_sylow S₁ S
    have hs₁ : g⁻¹ * s * g ∈ (S₁ : Subgroup (CentralizerBar x)) := (hg s).1 hs
    have hs₁c : ∀ u ∈ (S₁ : Subgroup (CentralizerBar x)),
        u * (g⁻¹ * s * g) = (g⁻¹ * s * g) * u := by
      intro u hu
      have hm : g * u * g⁻¹ ∈ (S : Subgroup (CentralizerBar x)) := by
        rw [hg]
        simpa [mul_assoc] using hu
      have := hsc _ hm
      calc u * (g⁻¹ * s * g) = g⁻¹ * ((g * u * g⁻¹) * s) * g := by group
        _ = g⁻¹ * (s * (g * u * g⁻¹)) * g := by rw [this]
        _ = (g⁻¹ * s * g) * u := by group
    have hTle : Subgroup.zpowers (g⁻¹ * s * g) ≤ (S₁ : Subgroup (CentralizerBar x)) :=
      (Subgroup.zpowers_le).2 hs₁
    have hT2 : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * s * g)) :=
      S₁.isPGroup'.to_le hTle
    have hcomm : ∀ (a : Q8 × Q8) (t : CentralizerBar x), t ∈ Subgroup.zpowers (g⁻¹ * s * g) →
        Φ a * t = t * Φ a := by
      intro a t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have h1 : Commute (Φ a) (g⁻¹ * s * g) := hs₁c (Φ a) (hAS ⟨a, rfl⟩)
      exact (h1.zpow_right k).eq
    obtain ⟨a, ha, hac⟩ := q8q8_commuting_two_subgroup_le_center hC Φ hΦ _ hT2 hcomm
      (g⁻¹ * s * g) (Subgroup.mem_zpowers _)
    have ha1 : a.1 = 1 ∨ a.1 = QuaternionGroup.a 2 := quaternion_center a.1 (fun y => by
      have := congrArg Prod.fst (hac (y, 1))
      simpa using this)
    have ha2 : a.2 = 1 ∨ a.2 = QuaternionGroup.a 2 := quaternion_center a.2 (fun y => by
      have := congrArg Prod.snd (hac (1, y))
      simpa using this)
    have hswap : w' * (g⁻¹ * s * g) * w'⁻¹ = g⁻¹ * s * g := by
      have := hs₁c w' hwS
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hfix : a.1 = a.2 := by
      have h1 : Φ (a.2, a.1) = Φ a := by
        have hconj : w' * Φ a * w'⁻¹ = Φ (a.2, a.1) := by
          change w' * ((φ a : ↥(layerBar x)) : CentralizerBar x) * w'⁻¹ =
            ((φ (a.2, a.1) : ↥(layerBar x)) : CentralizerBar x)
          have := congrArg (fun u : ↥(layerBar x) => (u : CentralizerBar x)) (hsw a.1 a.2)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
          exact this
        rw [← hconj, ha]
        exact hswap
      have := hΦ h1
      exact congrArg Prod.snd this
    have hs₁x : g⁻¹ * s * g ∈ Subgroup.zpowers (xbar x) := by
      rw [← ha]
      rcases ha1 with h1 | h1
      · have : a = 1 := Prod.ext h1 (by rw [← hfix]; exact h1)
        rw [this, map_one]
        exact Subgroup.one_mem _
      · have : a = (QuaternionGroup.a 2, QuaternionGroup.a 2) :=
          Prod.ext h1 (by rw [← hfix]; exact h1)
        rw [this]
        change ((φ (QuaternionGroup.a 2, QuaternionGroup.a 2) : ↥(layerBar x)) :
          CentralizerBar x) ∈ _
        rw [hφz, hzx]
        exact Subgroup.mem_zpowers _
    have hcomm' := commute_of_mem_zpowers_xbar x g hs₁x
    have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
    rw [this]
    have h2 : g * (g⁻¹ * s * g) = (g⁻¹ * s * g) * g := hcomm'
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
    exact hs₁x
  · intro hsx s' _
    exact commute_of_mem_zpowers_xbar x s' hsx

section SylowG

@[expose] def xH (x : G) : ↥(Subgroup.centralizer ({x} : Set G)) :=
  ⟨x, Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff] at hh; rw [hh]⟩

omit [Finite G] in
theorem mk_xH (x : G) :
    (QuotientGroup.mk (xH x) : CentralizerBar x) = xbar x := rfl

omit [Finite G] in
theorem xH_mul_self {x : G} (hx : orderOf x = 2) : xH x * xH x = 1 :=
  Subtype.ext (by
    change x * x = 1
    rw [← sq, ← hx]
    exact pow_orderOf_eq_one x)

omit [Finite G] in
theorem orderOf_xH {x : G} (hx : orderOf x = 2) : orderOf (xH x) = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact xH_mul_self hx) ?_
  intro h
  have : x = 1 := congrArg Subtype.val h
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

omit [Finite G] in
theorem xH_central (x : G) (g : ↥(Subgroup.centralizer ({x} : Set G))) : g * xH x = xH x * g :=
  Subtype.ext (Subgroup.mem_centralizer_iff.1 g.2 x (Set.mem_singleton x)).symm

omit [Finite G] in
theorem xH_mem_sylow {x : G} (hx : orderOf x = 2)
    (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) : xH x ∈ (S : Subgroup _) := by
  have hN : (Subgroup.zpowers (xH x)).Normal :=
    ⟨fun n hn g => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      have h : Commute g (xH x) := xH_central x g
      have : g * xH x ^ k * g⁻¹ = xH x ^ k := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (h.zpow_right k).eq
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _⟩
  exact (isPGroup_zpowers_of_orderOf_eq_two (orderOf_xH hx)).le_sylow_of_normal S
    (Subgroup.mem_zpowers _)

theorem eq_one_of_mem_sylow_of_mem_pPrimeCore {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    {n : H} (hS : n ∈ (S : Subgroup H)) (hN : n ∈ pPrimeCore 2 H) : n = 1 := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨n, hS⟩
  have hk' : n ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf n ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf n ∣ Nat.card (pPrimeCore 2 H) := Subgroup.orderOf_dvd_natCard _ hN
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 H)) := pPrimeCore_coprime_card
  have : Nat.Coprime (orderOf n) (2 ^ k) :=
    (Nat.Coprime.pow_right k (hcop.coprime_dvd_right h2).symm)
  have h3 := this.eq_one_of_dvd h1
  exact orderOf_eq_one_iff.1 h3

theorem central_sylow_le_zpowers (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G)))
    (s : ↥(Subgroup.centralizer ({x} : Set G))) (hs : s ∈ (S : Subgroup _))
    (hsc : ∀ s' ∈ (S : Subgroup _), s' * s = s * s') : s ∈ Subgroup.zpowers (xH x) := by
  let π : ↥(Subgroup.centralizer ({x} : Set G)) →* CentralizerBar x :=
    QuotientGroup.mk' (pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)))
  let Sbar : Sylow 2 (CentralizerBar x) := S.mapSurjective (QuotientGroup.mk'_surjective _)
  have hSbar : (Sbar : Subgroup (CentralizerBar x)) = (S : Subgroup _).map π := rfl
  have hmem : π s ∈ (Sbar : Subgroup (CentralizerBar x)) := ⟨s, hs, rfl⟩
  have hcent : ∀ u ∈ (Sbar : Subgroup (CentralizerBar x)), u * π s = π s * u := by
    intro u hu
    rw [hSbar] at hu
    obtain ⟨s', hs', rfl⟩ := hu
    rw [← map_mul, ← map_mul, hsc s' hs']
  have h1 := (center_sylow_centralizerBar hG hx hL Sbar (π s) hmem).1 hcent
  have hπx : xbar x = π (xH x) := rfl
  rw [hπx, ← MonoidHom.map_zpowers] at h1
  obtain ⟨y, hy, hys⟩ := h1
  have hyS : y ∈ (S : Subgroup _) :=
    (Subgroup.zpowers_le).2 (xH_mem_sylow hx S) hy
  have hn : y⁻¹ * s ∈ pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G)) :=
    (QuotientGroup.eq).1 hys
  have hnS : y⁻¹ * s ∈ (S : Subgroup _) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hs
  have h0 := eq_one_of_mem_sylow_of_mem_pPrimeCore S hnS hn
  have : s = y := by
    rw [inv_mul_eq_one] at h0
    exact h0.symm
  rw [this]
  exact hy

omit [Finite G] in
theorem isPGroup_subgroupOf {p : ℕ} {K : Subgroup G} (hK : IsPGroup p K) (H : Subgroup G) :
    IsPGroup p ↥(K.subgroupOf H) := by
  rintro ⟨h, hh⟩
  obtain ⟨k, hk⟩ := hK ⟨(h : G), Subgroup.mem_subgroupOf.1 hh⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

omit [Finite G] in
theorem zpow_eq_one_or_self {x : G} (hx : x * x = 1) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have hx2 : x ^ 2 = 1 := by rw [sq]; exact hx
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_ofNat, hx2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_ofNat, hx2, one_zpow, one_mul]

theorem sylow_centralizer_isSylow (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) (S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) :
    ∃ T : Sylow 2 G,
      (T : Subgroup G) = (S : Subgroup ↥(Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype ∧
      x ∈ (T : Subgroup G) ∧ (∀ t ∈ (T : Subgroup G), t * x = x * t) ∧
      ∀ c ∈ (T : Subgroup G), (∀ t ∈ (T : Subgroup G), t * c = c * t) →
        c ∈ Subgroup.zpowers x := by
  let H : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let St : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hSt : IsPGroup 2 ↥St := S.isPGroup'.map H.subtype
  obtain ⟨T₁, hT₁⟩ := hSt.exists_le_sylow
  have hxSt : x ∈ St := ⟨xH x, xH_mem_sylow hx S, rfl⟩
  have hxT₁ : x ∈ (T₁ : Subgroup G) := hT₁ hxSt
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have key : ∀ c ∈ (T₁ : Subgroup G), (∀ t ∈ (T₁ : Subgroup G), t * c = c * t) →
      c ∈ Subgroup.zpowers x := by
    intro c hcT hcc
    have hcH : c ∈ H := Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcc h hxT₁)
    let c₀ : ↥H := ⟨c, hcH⟩
    have hle : St ⊔ Subgroup.zpowers c ≤ (T₁ : Subgroup G) :=
      sup_le hT₁ ((Subgroup.zpowers_le).2 hcT)
    have hQ2 : IsPGroup 2 ↥((St ⊔ Subgroup.zpowers c).subgroupOf H) :=
      isPGroup_subgroupOf (T₁.isPGroup'.to_le hle) H
    have hSQ : (S : Subgroup ↥H) ≤ (St ⊔ Subgroup.zpowers c).subgroupOf H := fun s hs =>
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (⟨s, hs, rfl⟩ : (s : G) ∈ St))
    have hQS := S.is_maximal' hQ2 hSQ
    have hc₀S : c₀ ∈ (S : Subgroup ↥H) := by
      rw [← hQS]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
    have hc₀c : ∀ s' ∈ (S : Subgroup ↥H), s' * c₀ = c₀ * s' := fun s' hs' =>
      Subtype.ext (hcc _ (hT₁ ⟨s', hs', rfl⟩))
    have h1 := central_sylow_le_zpowers hG hx hL S c₀ hc₀S hc₀c
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : ((xH x ^ k : ↥H) : G) = ((c₀ : ↥H) : G) := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at h2
    exact Subgroup.mem_zpowers_iff.2 ⟨k, h2⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have : Nontrivial ↥(T₁ : Subgroup G) := ⟨⟨⟨x, hxT₁⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have := T₁.isPGroup'.center_nontrivial
  obtain ⟨⟨c, hc⟩, hcne⟩ := exists_ne (1 : ↥(Subgroup.center ↥(T₁ : Subgroup G)))
  have hcc : ∀ t ∈ (T₁ : Subgroup G), t * (c : G) = (c : G) * t := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨t, ht⟩)
  have hcx := key (c : G) c.2 hcc
  have hcx' : (c : G) = x := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hcx
    rcases zpow_eq_one_or_self hxx k with h | h
    · exfalso
      apply hcne
      apply Subtype.ext
      apply Subtype.ext
      rw [← hk, h]
      rfl
    · rw [← hk, h]
  have hxc : ∀ t ∈ (T₁ : Subgroup G), t * x = x * t := fun t ht => hcx' ▸ hcc t ht
  have hT₁H : (T₁ : Subgroup G) ≤ H := fun t ht =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hxc t ht).symm)
  have hQ2 : IsPGroup 2 ↥((T₁ : Subgroup G).subgroupOf H) :=
    isPGroup_subgroupOf T₁.isPGroup' H
  have hSQ : (S : Subgroup ↥H) ≤ (T₁ : Subgroup G).subgroupOf H := fun s hs =>
    Subgroup.mem_subgroupOf.2 (hT₁ (⟨s, hs, rfl⟩ : (s : G) ∈ St))
  have hQS := S.is_maximal' hQ2 hSQ
  refine ⟨T₁, ?_, hxT₁, hxc, key⟩
  apply le_antisymm
  · intro g hg
    have : (⟨g, hT₁H hg⟩ : ↥H) ∈ (T₁ : Subgroup G).subgroupOf H := hg
    rw [hQS] at this
    exact ⟨⟨g, hT₁H hg⟩, this, rfl⟩
  · exact hT₁

theorem isCentralInvolution_of_layer (hG : Gen4 G) {x : G} (hx : orderOf x = 2)
    (hL : IsSL4Model ↥(layerBar x)) : IsCentralInvolution x := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) := inferInstance
  obtain ⟨T, -, hxT, hcomm, -⟩ := sylow_centralizer_isSylow hG hx hL S
  exact ⟨hx, T, hxT, hcomm⟩

end SylowG

end Bridge

end CFSG.GH74.L5U5
