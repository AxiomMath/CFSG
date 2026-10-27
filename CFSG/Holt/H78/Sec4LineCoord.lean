module

public import CFSG.Holt.H78.Sec4Defs
public import CFSG.Holt.H78.AltModelSylow
public import CFSG.Holt.H78.Sections

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open Equiv
open scoped Pointwise

section JClosed

variable (G : Type*) [Group G] (Ω : Type*) [MulAction G Ω]

@[expose] def IsJClosed (Λ : Set Ω) : Prop := ∀ x ∈ Λ, ∀ t ∈ longInvAt G Ω x, t • Λ = Λ

variable {G Ω}

theorem IsJClosed.smul {Λ : Set Ω} (hΛ : IsJClosed G Ω Λ) (g : G) : IsJClosed G Ω (g • Λ) := by
  intro x hx t ht
  obtain ⟨y, hy, rfl⟩ := hx
  have h := hΛ y hy (g⁻¹ * t * g) (by simpa using conj_mem_longInvAt ht g⁻¹)
  calc t • g • Λ = g • (g⁻¹ * t * g) • Λ := by rw [smul_smul, smul_smul]; group
    _ = g • Λ := by rw [h]

theorem IsJClosed.mem_stabilizer {Λ : Set Ω} (hΛ : IsJClosed G Ω Λ) {x : Ω} (hx : x ∈ Λ)
    {t : G} (ht : t ∈ longInvAt G Ω x) : t ∈ stabilizer G Λ :=
  hΛ x hx t ht

end JClosed

section Star

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]

theorem isStarGroup_inducedPerm_of_isJClosed (hG : IsStarGroup G Ω) {Λ : Set Ω}
    (hΛ : IsJClosed G Ω Λ) (hodd : Odd (Nat.card Λ)) (h3 : 3 ≤ Nat.card Λ) :
    IsStarGroup ↥(inducedPerm (stabilizer G Λ) Λ le_rfl) ↥Λ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hodd, h3, fun β R hR hRβ hR3 => ?_⟩
  obtain ⟨R', hR'X, hR', hlift, hlift'⟩ := exists_isPGroup_lift_inducedPerm hR
  have hR'β : R' ≤ stabilizer G (β : Ω) := fun r hr => by
    obtain ⟨y, hy, hyr⟩ := hlift r hr
    rw [mem_stabilizer_iff, ← hyr β]
    exact congrArg Subtype.val (mem_stabilizer_iff.mp (hRβ hy))
  have h3R : 3 ≤ Nat.card (fixSet Ω R') := by
    refine hR3.trans (Nat.card_le_card_of_injective (fun δ => ⟨((δ : Λ) : Ω), ?_⟩) ?_)
    · intro r hr
      obtain ⟨y, hy, hyr⟩ := hlift r hr
      rw [← hyr]
      exact congrArg Subtype.val (δ.2 y hy)
    · intro δ δ' h
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val h
  obtain ⟨t, htβ, htR⟩ := hG.star β R' hR' hR'β h3R
  have htX : t ∈ stabilizer G Λ := hΛ β β.2 t htβ
  have : Nontrivial Λ := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨⟨inducedHom (stabilizer G Λ) Λ le_rfl ⟨t, htX⟩, ⟨t, htX⟩, rfl⟩,
    mem_longInvAt_subgroup_iff.mpr (inducedHom_mem_longInvAt _ (x := ⟨t, htX⟩) htβ
      (exists_ne β)), Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hlift' y hy
  refine Subtype.ext (Equiv.ext fun δ => Subtype.ext ?_)
  simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply, hry,
    coe_inducedHom_apply]
  rw [← mul_smul, ← mul_smul, Subgroup.mem_centralizer_iff.mp htR r hr]

omit [Finite Ω] in
theorem card_stabilizer_lt_of_ne_univ [IsPretransitive G Ω] {Λ : Set Ω} {α : Ω} (hα : α ∈ Λ)
    (hne : Λ ≠ Set.univ) : Nat.card (stabilizer G Λ) < Nat.card G := by
  obtain ⟨γ, hγ⟩ : ∃ γ, γ ∉ Λ := by
    by_contra! h
    exact hne (Set.eq_univ_of_forall h)
  obtain ⟨g, hg⟩ := exists_smul_eq G α γ
  refine (Subgroup.card_le_card_group _).lt_of_ne fun h => hγ ?_
  have hg' : g • Λ = Λ := by
    rw [← mem_stabilizer_iff, Subgroup.eq_top_of_card_eq _ h]
    exact Subgroup.mem_top g
  rw [← hg, ← hg']
  exact Set.smul_mem_smul_set hα

omit [Finite G] [Finite Ω] in
theorem IsJClosed.exists_inducedHom_mem_longInvAt (hG : IsStarGroup G Ω) {Λ : Set Ω}
    (hΛ : IsJClosed G Ω Λ) {α : Ω} (hα : α ∈ Λ) (hΛ2 : ∃ δ ∈ Λ, δ ≠ α) :
    ∃ t : stabilizer G Λ, (t : G) ∈ longInvAt G Ω α ∧
      inducedHom (stabilizer G Λ) Λ le_rfl t ∈ longInvAt (Perm Λ) Λ ⟨α, hα⟩ := by
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  refine ⟨⟨t, hΛ α hα t ht⟩, ht, inducedHom_mem_longInvAt le_rfl ht ?_⟩
  obtain ⟨δ, hδ, hδα⟩ := hΛ2
  exact ⟨⟨δ, hδ⟩, fun h => hδα (congrArg Subtype.val h)⟩

omit [Finite G] in
theorem IsJClosed.odd_card (hG : IsStarGroup G Ω) {Λ : Set Ω} (hΛ : IsJClosed G Ω Λ) {α : Ω}
    (hα : α ∈ Λ) (hΛ2 : ∃ δ ∈ Λ, δ ≠ α) : Odd (Nat.card Λ) := by
  classical
  have : Fintype Λ := Fintype.ofFinite Λ
  obtain ⟨t, -, ht⟩ := hΛ.exists_inducedHom_mem_longInvAt hG hα hΛ2
  rw [Nat.card_eq_fintype_card]
  exact odd_card_of_mem_longInv_perm ht.1

end Star

section LineSection

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

theorem Sec4Setting.exists_mem_longInv_inducedHom_eq (hS : Sec4Setting G Ω) {Λ : Set Ω}
    [DecidablePred (· ∈ Λ)] {α : Ω} (hα : α ∈ Λ) (h3 : 3 ≤ Λ.ncard) (hJ : IsJClosed G Ω Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) (hne : Λ ≠ Set.univ)
    {σ : Perm Λ} (hσ : σ ∈ longInv (Perm Λ) Λ) :
    ∃ t : stabilizer G Λ, (t : G) ∈ longInv G Ω ∧ inducedHom (stabilizer G Λ) Λ le_rfl t = σ := by
  have hT := hS.star.isPretransitive
  have h3' : 3 ≤ Nat.card Λ := by rwa [Nat.card_coe_set_eq]
  have hΛ2 : ∃ δ ∈ Λ, δ ≠ α := Set.exists_ne_of_one_lt_ncard (by omega) α
  obtain ⟨t, htJ, ht⟩ := hJ.exists_inducedHom_mem_longInvAt hS.star hα hΛ2
  have hstar := isStarGroup_inducedPerm_of_isJClosed hS.star hJ (hJ.odd_card hS.star hα hΛ2) h3'
  have hlt : Nat.card (inducedPerm (stabilizer G Λ) Λ le_rfl) < Nat.card G :=
    card_inducedPerm_le.trans_lt (card_stabilizer_lt_of_ne_univ hα hne)
  have hσX : σ ∈ inducedPerm (stabilizer G Λ) Λ le_rfl :=
    longInv_perm_subset_of_alternatingGroup_le hA ⟨t, rfl⟩ ht.1 hσ
  exact (hS.longInv_inducedPerm le_rfl hlt hstar ⟨t, t.2, htJ.1⟩ ⟨σ, hσX⟩).mp
    (mem_longInv_subgroup_perm_iff.mpr hσ)

theorem Sec4Setting.exists_mem_longInvAt_inducedHom_eq (hS : Sec4Setting G Ω) {Λ : Set Ω}
    [DecidablePred (· ∈ Λ)] {α : Ω} (hα : α ∈ Λ) (h3 : 3 ≤ Λ.ncard) (hJ : IsJClosed G Ω Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) (hne : Λ ≠ Set.univ)
    {x : Λ} {σ : Perm Λ} (hσ : σ ∈ longInvAt (Perm Λ) Λ x) :
    ∃ t : stabilizer G Λ, (t : G) ∈ longInvAt G Ω x ∧
      inducedHom (stabilizer G Λ) Λ le_rfl t = σ := by
  obtain ⟨t, htJ, rfl⟩ := hS.exists_mem_longInv_inducedHom_eq hα h3 hJ hA hne hσ.1
  refine ⟨t, ⟨htJ, ?_⟩, rfl⟩
  have h := congrArg Subtype.val hσ.2
  rwa [Perm.smul_def, coe_inducedHom_apply] at h

end LineSection

section AltStab

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

open Equiv.Perm

theorem alternatingGroup_inf_stabilizer_le_of_isThreeCycle {X : Subgroup (Perm Δ)} {x : Δ}
    (hX : ∀ σ : Perm Δ, σ.IsThreeCycle → σ x = x → σ ∈ X) :
    alternatingGroup Δ ⊓ stabilizer (Perm Δ) x ≤ X := by
  rw [← map_ofSubtype_alternatingGroup, ← closure_three_cycles_eq_alternating,
    MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨σ, hσ, rfl⟩
  refine hX _ ?_ (ofSubtype_apply_of_not_mem σ (not_not.2 rfl))
  rw [Perm.IsThreeCycle, cycleType_ofSubtype]
  exact hσ

theorem eq_one_of_forall_commute_alternatingGroup_inf_stabilizer (h5 : 5 ≤ Fintype.card Δ)
    {x : Δ} {g : Perm Δ} (hgx : g x = x)
    (hg : ∀ a ∈ alternatingGroup Δ ⊓ stabilizer (Perm Δ) x, g * a = a * g) : g = 1 := by
  have h₁ : ∀ y, g y ≠ x ↔ y ≠ x := fun y =>
    not_congr ⟨fun h => g.injective (h.trans hgx.symm), fun h => by rw [h, hgx]⟩
  have h₂ : ∀ y, g y ≠ y → y ≠ x := by
    rintro y hy rfl
    exact hy hgx
  have hg' : ofSubtype (subtypePerm g h₁) = g := ofSubtype_subtypePerm h₁ h₂
  have hc : subtypePerm g h₁ ∈
      Subgroup.centralizer (alternatingGroup {y // y ≠ x} : Set (Perm {y // y ≠ x})) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply ofSubtype_injective
    rw [map_mul, map_mul, hg']
    exact (hg (ofSubtype a) (by rw [← map_ofSubtype_alternatingGroup]; exact ⟨a, ha, rfl⟩)).symm
  rw [centralizer_alternatingGroup_perm_eq_bot (by simp; omega), Subgroup.mem_bot] at hc
  rw [← hg', hc, map_one]

theorem alternatingGroup_inf_stabilizer_le_or_eq_bot (h6 : 6 ≤ Fintype.card Δ) {x : Δ}
    {N : Subgroup (Perm Δ)} (hNx : N ≤ stabilizer (Perm Δ) x)
    (hN : ∀ a ∈ alternatingGroup Δ ⊓ stabilizer (Perm Δ) x, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    alternatingGroup Δ ⊓ stabilizer (Perm Δ) x ≤ N ∨ N = ⊥ := by
  set A := alternatingGroup Δ ⊓ stabilizer (Perm Δ) x with hAdef
  have hsimple : IsSimpleGroup A := isSimpleGroup_alternatingGroup_inf_stabilizer h6 x
  have hnorm : (N.subgroupOf A).Normal := ⟨fun n hn a => by
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact hN a a.2 n hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · right
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    have hnx : n x = x := hNx hn
    refine eq_one_of_forall_commute_alternatingGroup_inf_stabilizer (by omega) hnx
      fun a ha => ?_
    have hconj : n * a * n⁻¹ ∈ A := by
      refine Subgroup.mem_inf.mpr ⟨(inferInstance : (alternatingGroup Δ).Normal).conj_mem a
        (Subgroup.mem_inf.mp ha).1 n, ?_⟩
      have hax : a x = x := (Subgroup.mem_inf.mp ha).2
      have hnx' : n⁻¹ x = x := by rw [Perm.inv_eq_iff_eq, hnx]
      rw [mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply, Perm.mul_apply, hnx', hax, hnx]
    have hA : n * a * n⁻¹ * a⁻¹ ∈ A := A.mul_mem hconj (A.inv_mem ha)
    have hNmem : n * a * n⁻¹ * a⁻¹ ∈ N := by
      have := N.mul_mem hn (hN a ha n⁻¹ (N.inv_mem hn))
      simpa [mul_assoc] using this
    have hmem : (⟨_, hA⟩ : A) ∈ N.subgroupOf A := hNmem
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : n * a * n⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hmem
    calc n * a = (n * a * n⁻¹ * a⁻¹) * (a * n) := by group
      _ = a * n := by rw [h1, one_mul]
  · left
    intro a ha
    have hmem : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := by
      rw [h]
      exact Subgroup.mem_top _
    exact hmem

end AltStab

section Line

variable {Ω : Type*} [DecidableEq Ω]

abbrev cyc3 (a b c : Ω) : Perm Ω := swap a b * swap b c

theorem cyc3_apply_of_ne {a b c y : Ω} (ha : y ≠ a) (hb : y ≠ b) (hc : y ≠ c) :
    cyc3 a b c y = y := by
  simp [cyc3, swap_apply_of_ne_of_ne, ha, hb, hc]

theorem cyc3_apply_left {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c) : cyc3 a b c a = b := by
  simp [cyc3, swap_apply_of_ne_of_ne, hab, hac]

theorem cyc3_apply_mid {a b c : Ω} (hac : a ≠ c) (hbc : b ≠ c) : cyc3 a b c b = c := by
  simp [cyc3, swap_apply_of_ne_of_ne, hac.symm, hbc.symm]

theorem cyc3_apply_right (a b c : Ω) : cyc3 a b c c = a := by
  simp [cyc3]

theorem cyc3_mem {L : Set Ω} {a b c : Ω} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) {y : Ω}
    (hy : y ∈ L) : cyc3 a b c y ∈ L := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]
  split_ifs <;> assumption

theorem cyc3_symm_mem {L : Set Ω} {a b c : Ω} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) {y : Ω}
    (hy : y ∈ L) : (cyc3 a b c).symm y ∈ L := by
  simp only [cyc3, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap, swap_apply_def]
  split_ifs <;> assumption

theorem smul_cyc3 {G : Type*} [Group G] [MulAction G Ω] (g : G) (a b c y : Ω) :
    g • cyc3 a b c y = cyc3 (g • a) (g • b) (g • c) (g • y) := by
  simp only [cyc3, Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

variable {G : Type*} [Group G] [MulAction G Ω]

@[expose] def Realizes3 (A : Subgroup G) (x : Ω) (L : Set Ω) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, a ≠ x → b ≠ x → c ≠ x → a ≠ b → a ≠ c → b ≠ c →
    ∃ k ∈ A, ∀ y ∈ L, k • y = cyc3 a b c y

theorem Realizes3.mono {A B : Subgroup G} {x : Ω} {L : Set Ω} (h : Realizes3 A x L)
    (hAB : A ≤ B) : Realizes3 B x L := by
  intro a ha b hb c hc hax hbx hcx hab hac hbc
  obtain ⟨k, hk, hky⟩ := h a ha b hb c hc hax hbx hcx hab hac hbc
  exact ⟨k, hAB hk, hky⟩

variable (G) in
structure IsLine (L : Set Ω) : Prop where
  jClosed : IsJClosed G Ω L
  seven_le : 7 ≤ L.ncard
  exists_smul_eq : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L, y ≠ x → z ≠ x → y ≠ z →
    ∃ t ∈ longInvAt G Ω x, t • y = z
  threeCycle : ∀ x ∈ L, Realizes3 (Subgroup.closure (longInvAt G Ω x)) x L

omit [DecidableEq Ω] in
theorem conj_mem_closure_longInvAt {x : Ω} {k : G}
    (hk : k ∈ Subgroup.closure (longInvAt G Ω x)) (g : G) :
    g * k * g⁻¹ ∈ Subgroup.closure (longInvAt G Ω (g • x)) := by
  have h : (Subgroup.closure (longInvAt G Ω x)).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure (longInvAt G Ω (g • x)) := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_longInvAt ht g
  exact h ⟨k, hk, rfl⟩

theorem IsLine.smul {L : Set Ω} (hL : IsLine G L) (g : G) : IsLine G (g • L) where
  jClosed := hL.jClosed.smul g
  seven_le := by rw [Set.ncard_smul_set]; exact hL.seven_le
  exists_smul_eq := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hyx hzx hyz
    simp only [ne_eq, smul_left_cancel_iff] at hyx hzx hyz
    obtain ⟨t, ht, hty⟩ := hL.exists_smul_eq x hx y hy z hz hyx hzx hyz
    exact ⟨g * t * g⁻¹, conj_mem_longInvAt ht g, by simp [mul_smul, hty]⟩
  threeCycle := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hax hbx hcx hab hac hbc
    simp only [ne_eq, smul_left_cancel_iff] at hax hbx hcx hab hac hbc
    obtain ⟨k, hk, hky⟩ := hL.threeCycle x hx a ha b hb c hc hax hbx hcx hab hac hbc
    refine ⟨g * k * g⁻¹, conj_mem_closure_longInvAt hk g, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [mul_smul, mul_smul, inv_smul_smul, hky y hy, smul_cyc3]

theorem coe_swap {L : Set Ω} (p q y : L) : ((swap p q y : L) : Ω) = swap (p : Ω) q y := by
  simp only [swap_apply_def]
  split_ifs <;> simp_all [Subtype.ext_iff]

theorem coe_swap_mk {L : Set Ω} {a b : Ω} (ha : a ∈ L) (hb : b ∈ L) (y : L) :
    ((swap (⟨a, ha⟩ : L) ⟨b, hb⟩ y : L) : Ω) = swap a b y :=
  coe_swap _ _ y

end Line

section LineOf

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

theorem Sec4Setting.isLine (hS : Sec4Setting G Ω) {Λ : Set Ω} [DecidablePred (· ∈ Λ)] {α : Ω}
    (hα : α ∈ Λ) (h7 : 7 ≤ Λ.ncard) (hJ : IsJClosed G Ω Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) (hne : Λ ≠ Set.univ) :
    IsLine G Λ := by
  have h3 : 3 ≤ Λ.ncard := by omega
  have hΛ2 : ∀ x ∈ Λ, ∃ δ ∈ Λ, δ ≠ x := fun x _ => Set.exists_ne_of_one_lt_ncard (by omega) x
  have hcard : Fintype.card Λ = Λ.ncard := by rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  refine ⟨hJ, h7, fun x hx y hy z hz hyx hzx hyz => ?_, ?_⟩
  · obtain ⟨t₀, -, hs⟩ := hJ.exists_inducedHom_mem_longInvAt hS.star hx (hΛ2 x hx)
    obtain ⟨σ, hσ, hσy⟩ := exists_mem_longInvAt_perm_apply_eq hs (x := ⟨y, hy⟩) (y := ⟨z, hz⟩)
      (by simpa [Subtype.ext_iff] using hyx) (by simpa [Subtype.ext_iff] using hzx)
      (by simpa [Subtype.ext_iff] using hyz.symm)
    obtain ⟨t, ht, htσ⟩ := hS.exists_mem_longInvAt_inducedHom_eq hα h3 hJ hA hne hσ
    refine ⟨t, ht, ?_⟩
    have h := congrArg (fun π : Perm Λ => ((π ⟨y, hy⟩ : Λ) : Ω)) htσ
    simpa [hσy] using h
  · intro x hx a ha b hb c hc hax hbx hcx hab hac hbc
    obtain ⟨t₀, -, hs⟩ := hJ.exists_inducedHom_mem_longInvAt hS.star hx (hΛ2 x hx)
    have hodd : Odd (Fintype.card Λ) := odd_card_of_mem_longInv_perm hs.1
    set σ : Perm Λ := swap ⟨a, ha⟩ ⟨b, hb⟩ * swap ⟨b, hb⟩ ⟨c, hc⟩ with hσdef
    have hσ : σ ∈ alternatingGroup Λ ⊓ stabilizer (Perm Λ) (⟨x, hx⟩ : Λ) := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [Perm.mem_alternatingGroup, hσdef, Perm.sign_mul,
          Perm.sign_swap (by simpa [Subtype.ext_iff] using hab),
          Perm.sign_swap (by simpa [Subtype.ext_iff] using hbc)]
        rfl
      · rw [mem_stabilizer_iff, Perm.smul_def, hσdef, Perm.mul_apply]
        have h1 : swap (⟨b, hb⟩ : Λ) ⟨c, hc⟩ ⟨x, hx⟩ = ⟨x, hx⟩ :=
          swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hbx.symm)
            (by simpa [Subtype.ext_iff] using hcx.symm)
        rw [h1]
        exact swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hax.symm)
          (by simpa [Subtype.ext_iff] using hbx.symm)
    rw [← closure_mul_longInvAt_perm_eq hodd (by omega)] at hσ
    have hle : Subgroup.closure {g : Perm Λ | ∃ u ∈ longInvAt (Perm Λ) Λ ⟨x, hx⟩,
        ∃ v ∈ longInvAt (Perm Λ) Λ ⟨x, hx⟩, u * v = g} ≤
        ((Subgroup.closure (longInvAt G Ω x)).subgroupOf (stabilizer G Λ)).map
          (inducedHom (stabilizer G Λ) Λ le_rfl) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨u, hu, v, hv, rfl⟩
      obtain ⟨tu, htu, rfl⟩ := hS.exists_mem_longInvAt_inducedHom_eq hα h3 hJ hA hne hu
      obtain ⟨tv, htv, rfl⟩ := hS.exists_mem_longInvAt_inducedHom_eq hα h3 hJ hA hne hv
      exact ⟨tu * tv, Subgroup.mul_mem _ (Subgroup.subset_closure htu)
        (Subgroup.subset_closure htv), map_mul _ _ _⟩
    obtain ⟨k, hk, hkσ⟩ := hle hσ
    refine ⟨k, hk, fun y hy => ?_⟩
    have h := congrArg (fun π : Perm Λ => ((π ⟨y, hy⟩ : Λ) : Ω)) hkσ
    simp only [coe_inducedHom_apply] at h
    rw [h, hσdef, Perm.mul_apply, coe_swap_mk, coe_swap_mk]
    rfl

end LineOf

section Realize

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

theorem cyc3_commutator {a b c d e : Ω} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) :
    cyc3 a b d * cyc3 a c e * (cyc3 a b d)⁻¹ * (cyc3 a c e)⁻¹ = cyc3 a b c := by
  ext y
  simp only [cyc3, mul_inv_rev, swap_inv, Perm.mul_apply]
  by_cases h1 : y = a
  · subst h1; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  by_cases h2 : y = b
  · subst h2; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  by_cases h3 : y = c
  · subst h3; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  by_cases h4 : y = d
  · subst h4; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  by_cases h5 : y = e
  · subst h5; simp [swap_apply_of_ne_of_ne, *, Ne.symm]
  simp [swap_apply_of_ne_of_ne, *]

omit [DecidableEq Ω] in
theorem exists_mem_notMem_of_card_lt_ncard {L : Set Ω} (s : Finset Ω) (h : s.card < L.ncard) :
    ∃ d ∈ L, d ∉ s := by
  by_contra! hc
  have := Set.ncard_le_ncard (fun d hd => hc d hd) (Finset.finite_toSet s)
  rw [Set.ncard_coe_finset] at this
  omega

omit [DecidableEq Ω] in
theorem inv_smul_eq_of_forall_smul_eq {k : G} {σ : Perm Ω} {L : Set Ω}
    (hσ : ∀ y ∈ L, σ⁻¹ y ∈ L) (hk : ∀ y ∈ L, k • y = σ y) : ∀ y ∈ L, k⁻¹ • y = σ⁻¹ y := by
  intro y hy
  rw [inv_smul_eq_iff, hk _ (hσ y hy), Perm.inv_def, Equiv.apply_symm_apply]

theorem Realizes3.commutator {A B : Subgroup G} {x : Ω} {L : Set Ω} (hL : 7 ≤ L.ncard)
    (hA : Realizes3 A x L) (hB : Realizes3 B x L) : Realizes3 ⁅A, B⁆ x L := by
  intro a ha b hb c hc hax hbx hcx hab hac hbc
  obtain ⟨d, hd, hd'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, a, b, c}
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd'
  obtain ⟨hdx, hda, hdb, hdc⟩ := hd'
  obtain ⟨e, he, he'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, a, b, c, d}
    ((Finset.card_le_five).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he'
  obtain ⟨hex, hea, heb, hec, hed⟩ := he'
  obtain ⟨k₁, hk₁, h₁⟩ := hA a ha b hb d hd hax hbx hdx hab (Ne.symm hda) (Ne.symm hdb)
  obtain ⟨k₂, hk₂, h₂⟩ := hB a ha c hc e he hax hcx hex hac (Ne.symm hea) (Ne.symm hec)
  refine ⟨k₁ * k₂ * k₁⁻¹ * k₂⁻¹, Subgroup.commutator_mem_commutator hk₁ hk₂, fun y hy => ?_⟩
  have hi₁ := inv_smul_eq_of_forall_smul_eq (fun z hz => by
    rw [Perm.inv_def]; exact cyc3_symm_mem ha hb hd hz) h₁
  have hi₂ := inv_smul_eq_of_forall_smul_eq (fun z hz => by
    rw [Perm.inv_def]; exact cyc3_symm_mem ha hc he hz) h₂
  have hy₁ : (cyc3 a c e)⁻¹ y ∈ L := by rw [Perm.inv_def]; exact cyc3_symm_mem ha hc he hy
  have hy₂ : (cyc3 a b d)⁻¹ ((cyc3 a c e)⁻¹ y) ∈ L := by
    rw [Perm.inv_def]; exact cyc3_symm_mem ha hb hd hy₁
  rw [mul_smul, mul_smul, mul_smul, hi₂ y hy, hi₁ _ hy₁, h₂ _ hy₂, h₁ _ (cyc3_mem ha hc he hy₂),
    ← cyc3_commutator hab hac (Ne.symm hda) (Ne.symm hea) hbc (Ne.symm hdb) (Ne.symm heb)
      (Ne.symm hdc) (Ne.symm hec) (Ne.symm hed)]
  rfl

theorem swap_mul_swap_mem_alternatingGroup_inf_stabilizer {L : Set Ω} [Fintype L] {x a b c : Ω}
    (hx : x ∈ L) (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hax : a ≠ x) (hbx : b ≠ x)
    (hcx : c ≠ x) (hab : a ≠ b) (hbc : b ≠ c) :
    swap (⟨a, ha⟩ : L) ⟨b, hb⟩ * swap ⟨b, hb⟩ ⟨c, hc⟩ ∈
      alternatingGroup L ⊓ stabilizer (Perm L) (⟨x, hx⟩ : L) := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_mul,
      Perm.sign_swap (by simpa [Subtype.ext_iff] using hab),
      Perm.sign_swap (by simpa [Subtype.ext_iff] using hbc)]
    rfl
  · rw [mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply]
    have h1 : swap (⟨b, hb⟩ : L) ⟨c, hc⟩ ⟨x, hx⟩ = ⟨x, hx⟩ :=
      swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hbx.symm)
        (by simpa [Subtype.ext_iff] using hcx.symm)
    rw [h1]
    exact swap_apply_of_ne_of_ne (by simpa [Subtype.ext_iff] using hax.symm)
      (by simpa [Subtype.ext_iff] using hbx.symm)

theorem Realizes3.alternatingGroup_inf_stabilizer_le {A : Subgroup G} {x : Ω} {L : Set Ω}
    [Fintype L] (hx : x ∈ L) (hAL : A ≤ stabilizer G L) (h : Realizes3 A x L) :
    alternatingGroup L ⊓ stabilizer (Perm L) (⟨x, hx⟩ : L) ≤ inducedPerm A L hAL := by
  refine alternatingGroup_inf_stabilizer_le_of_isThreeCycle fun σ hσ hσx => ?_
  obtain ⟨p, hp⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos, hσ.card_support]
    norm_num
  have hnd := hσ.nodup_iff_mem_support.mpr hp
  have heq := hσ.eq_swap_mul_swap_iff_mem_support.mpr hp
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨h01, h02⟩, h12⟩ := hnd
  have hpx : p ≠ ⟨x, hx⟩ := by
    rintro rfl
    exact (Perm.mem_support.mp hp) hσx
  have h1x : σ p ≠ ⟨x, hx⟩ := fun h => hpx (σ.injective (h.trans hσx.symm))
  have h2x : σ (σ p) ≠ ⟨x, hx⟩ := fun h => h1x (σ.injective (h.trans hσx.symm))
  have hne : ∀ {u v : L}, u ≠ v → (u : Ω) ≠ v := fun h h' => h (Subtype.ext h')
  obtain ⟨k, hk, hky⟩ := h p p.2 (σ p) (σ p).2 (σ (σ p)) (σ (σ p)).2 (hne hpx) (hne h1x)
    (hne h2x) (hne h01) (hne h02) (hne h12.1)
  refine mem_inducedPerm.mpr ⟨k, hk, fun y => ?_⟩
  rw [hky y y.2]
  conv_lhs => rw [heq]
  rw [Perm.mul_apply, coe_swap, coe_swap]
  rfl

variable [Finite Ω]

theorem Realizes3.of_normal {A N : Subgroup G} {x : Ω} {L : Set Ω} (h7 : 7 ≤ L.ncard)
    (hx : x ∈ L) (hAL : A ≤ stabilizer G L) (hA : Realizes3 A x L) (hNL : N ≤ stabilizer G L)
    (hNx : N ≤ stabilizer G x) (hAN : ∀ k ∈ A, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hmove : ∃ n ∈ N, ∃ y ∈ L, n • y ≠ y) : Realizes3 N x L := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have hcard : 7 ≤ Fintype.card L := by rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hXx : inducedPerm N L hNL ≤ stabilizer (Perm L) (⟨x, hx⟩ : L) := by
    rintro _ ⟨n, rfl⟩
    exact Subtype.ext (hNx n.2)
  have hnorm : ∀ a ∈ alternatingGroup L ⊓ stabilizer (Perm L) (⟨x, hx⟩ : L),
      ∀ m ∈ inducedPerm N L hNL, a * m * a⁻¹ ∈ inducedPerm N L hNL := by
    intro a ha m hm
    obtain ⟨k, hk, hka⟩ := mem_inducedPerm.mp (hA.alternatingGroup_inf_stabilizer_le hx hAL ha)
    obtain ⟨n, hn, hnm⟩ := mem_inducedPerm.mp hm
    refine mem_inducedPerm.mpr ⟨k * n * k⁻¹, hAN k hk n hn, fun y => ?_⟩
    have hainv : ((a⁻¹ y : L) : Ω) = k⁻¹ • (y : Ω) := by
      rw [eq_inv_smul_iff, ← hka]
      simp
    rw [Perm.mul_apply, Perm.mul_apply, hka, hnm, hainv, mul_smul, mul_smul]
  rcases alternatingGroup_inf_stabilizer_le_or_eq_bot (by omega) hXx hnorm with h | h
  · intro a ha b hb c hc hax hbx hcx hab hac hbc
    obtain ⟨n, hn, hny⟩ := mem_inducedPerm.mp
      (h (swap_mul_swap_mem_alternatingGroup_inf_stabilizer hx ha hb hc hax hbx hcx hab hbc))
    refine ⟨n, hn, fun y hy => ?_⟩
    have hy' := hny ⟨y, hy⟩
    rw [Perm.mul_apply, coe_swap_mk, coe_swap_mk] at hy'
    exact hy'.symm
  · exfalso
    obtain ⟨n, hn, y, hy, hny⟩ := hmove
    have hmem : inducedHom N L hNL ⟨n, hn⟩ ∈ inducedPerm N L hNL := ⟨⟨n, hn⟩, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hny (congrArg (fun π : Perm L => ((π ⟨y, hy⟩ : L) : Ω)) hmem)

omit [DecidableEq Ω] [Finite Ω] in
theorem exists_four_of_seven_le {L : Set Ω} (h7 : 7 ≤ L.ncard) (x : Ω) :
    ∃ a ∈ L, ∃ b ∈ L, ∃ c ∈ L, ∃ d ∈ L, a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧ a ≠ b ∧ a ≠ c ∧
      a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  obtain ⟨a, ha, ha'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x}
    ((Finset.card_singleton _).trans_lt (by omega))
  obtain ⟨b, hb, hb'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, a}
    ((Finset.card_le_two).trans_lt (by omega))
  obtain ⟨c, hc, hc'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, a, b}
    ((Finset.card_le_three).trans_lt (by omega))
  obtain ⟨d, hd, hd'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, a, b, c}
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha' hb' hc' hd'
  exact ⟨a, ha, b, hb, c, hc, d, hd, ha', hb'.1, hc'.1, hd'.1, Ne.symm hb'.2, Ne.symm hc'.2.1,
    Ne.symm hd'.2.1, Ne.symm hc'.2.2, Ne.symm hd'.2.2.1, Ne.symm hd'.2.2.2⟩

theorem Realizes3.smul_eq_of_odd {A N : Subgroup G} {x : Ω} {L : Set Ω} (h7 : 7 ≤ L.ncard)
    (hx : x ∈ L) (hAL : A ≤ stabilizer G L) (hA : Realizes3 A x L) (hNL : N ≤ stabilizer G L)
    (hNx : N ≤ stabilizer G x) (hAN : ∀ k ∈ A, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) : ∀ n ∈ N, ∀ y ∈ L, n • y = y := by
  by_contra! hc
  have hN := Realizes3.of_normal h7 hx hAL hA hNL hNx hAN hc
  obtain ⟨a, ha, b, hb, c, hc', d, hd, hax, hbx, hcx, hdx, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_of_seven_le h7 x
  obtain ⟨n₁, hn₁, h₁⟩ := hN a ha b hb c hc' hax hbx hcx hab hac hbc
  obtain ⟨n₂, hn₂, h₂⟩ := hN a ha b hb d hd hax hbx hdx hab had hbd
  have hga : (n₁ * n₂) • a = c := by
    rw [mul_smul, h₂ a ha, cyc3_apply_left hab had, h₁ b hb, cyc3_apply_mid hac hbc]
  have hgc : (n₁ * n₂) • c = a := by
    rw [mul_smul, h₂ c hc', cyc3_apply_of_ne (Ne.symm hac) (Ne.symm hbc) hcd, h₁ c hc',
      cyc3_apply_right]
  have hg2 : (n₁ * n₂) ^ 2 ∈ stabilizer G c := by
    rw [mem_stabilizer_iff, pow_two, mul_smul, hgc, hga]
  have hdvd : orderOf (n₁ * n₂) ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk (n₁ * n₂) (N.mul_mem hn₁ hn₂)]
    exact orderOf_dvd_natCard _
  obtain ⟨q, hq⟩ := Odd.of_dvd_nat hodd hdvd
  have h1 : (n₁ * n₂) ^ orderOf (n₁ * n₂) • a = c := by
    rw [hq, pow_succ, mul_smul, hga, pow_mul]
    exact mem_stabilizer_iff.mp (Subgroup.pow_mem _ hg2 q)
  rw [pow_orderOf_eq_one, one_smul] at h1
  exact hac h1

theorem Realizes3.smul_eq_of_commute {A N : Subgroup G} {x : Ω} {L : Set Ω} (h7 : 7 ≤ L.ncard)
    (hx : x ∈ L) (hAL : A ≤ stabilizer G L) (hA : Realizes3 A x L) (hNL : N ≤ stabilizer G L)
    (hNx : N ≤ stabilizer G x) (hAN : ∀ k ∈ A, ∀ n ∈ N, k * n * k⁻¹ ∈ N)
    (hcomm : ∀ n ∈ N, ∀ n' ∈ N, n * n' = n' * n) : ∀ n ∈ N, ∀ y ∈ L, n • y = y := by
  by_contra! hc
  have hN := Realizes3.of_normal h7 hx hAL hA hNL hNx hAN hc
  obtain ⟨a, ha, b, hb, c, hc', d, hd, hax, hbx, hcx, hdx, hab, hac, had, hbc, hbd, hcd⟩ :=
    exists_four_of_seven_le h7 x
  obtain ⟨n₁, hn₁, h₁⟩ := hN a ha b hb c hc' hax hbx hcx hab hac hbc
  obtain ⟨n₂, hn₂, h₂⟩ := hN a ha b hb d hd hax hbx hdx hab had hbd
  have h := congrArg (· • a) (hcomm n₁ hn₁ n₂ hn₂)
  simp only [mul_smul] at h
  rw [h₂ a ha, cyc3_apply_left hab had, h₁ b hb, cyc3_apply_mid hac hbc, h₁ a ha,
    cyc3_apply_left hab hac, h₂ b hb, cyc3_apply_mid had hbd] at h
  exact hcd h

end Realize

section Geometry

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

theorem IsLine.subset_of_mem_of_mem {L L' : Set Ω} (hL : IsLine G L) (hL' : IsJClosed G Ω L')
    {x y : Ω} (hx : x ∈ L) (hx' : x ∈ L') (hy : y ∈ L) (hy' : y ∈ L') (hxy : x ≠ y) :
    L ⊆ L' := by
  intro z hz
  rcases eq_or_ne z x with rfl | hzx
  · exact hx'
  rcases eq_or_ne z y with rfl | hzy
  · exact hy'
  obtain ⟨t, ht, hty⟩ := hL.exists_smul_eq x hx y hy z hz hxy.symm hzx (Ne.symm hzy)
  rw [← hty, ← hL' x hx' t ht]
  exact Set.smul_mem_smul_set hy'

theorem IsLine.eq_of_mem_of_mem {L L' : Set Ω} (hL : IsLine G L) (hL' : IsLine G L') {x y : Ω}
    (hx : x ∈ L) (hx' : x ∈ L') (hy : y ∈ L) (hy' : y ∈ L') (hxy : x ≠ y) : L = L' :=
  (hL.subset_of_mem_of_mem hL'.jClosed hx hx' hy hy' hxy).antisymm
    (hL'.subset_of_mem_of_mem hL.jClosed hx' hx hy' hy hxy)

theorem IsLine.exists_mem_stabilizer_smul_eq {L : Set Ω} (hL : IsLine G L) {y z : Ω}
    (hy : y ∈ L) (hz : z ∈ L) : ∃ g ∈ stabilizer G L, g • y = z := by
  rcases eq_or_ne y z with rfl | hyz
  · exact ⟨1, Subgroup.one_mem _, one_smul G y⟩
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {y, z}
    ((Finset.card_le_two).trans_lt (by have := hL.seven_le; omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
  obtain ⟨t, ht, hty⟩ := hL.exists_smul_eq x hx y hy z hz (Ne.symm hx'.1) (Ne.symm hx'.2) hyz
  exact ⟨t, hL.jClosed x hx t ht, hty⟩

theorem IsLine.exists_mem_stabilizer_smul_eq_smul {L : Set Ω} (hL : IsLine G L) {α : Ω}
    (hα : α ∈ L) {g : G} (hg : α ∈ g • L) : ∃ h ∈ stabilizer G α, h • L = g • L := by
  have hg' : g⁻¹ • α ∈ L := Set.mem_smul_set_iff_inv_smul_mem.mp hg
  obtain ⟨k, hk, hkα⟩ := hL.exists_mem_stabilizer_smul_eq hα hg'
  refine ⟨g * k, ?_, ?_⟩
  · rw [mem_stabilizer_iff, mul_smul, hkα, smul_inv_smul]
  · rw [mul_smul, mem_stabilizer_iff.mp hk]

theorem IsLine.exists_mem_longInvAt {L : Set Ω} (hL : IsLine G L) {x : Ω} (hx : x ∈ L) :
    ∃ t ∈ longInvAt G Ω x, t ∈ stabilizer G L := by
  obtain ⟨a, ha, b, hb, -, -, -, -, hax, hbx, -, -, hab, -, -, -, -, -⟩ :=
    exists_four_of_seven_le hL.seven_le x
  obtain ⟨t, ht, -⟩ := hL.exists_smul_eq x hx a ha b hb hax hbx hab
  exact ⟨t, ht, hL.jClosed x hx t ht⟩

theorem IsLine.eq_univ_of_forall_smul_eq [IsPreprimitive G Ω] {L : Set Ω} (hL : IsLine G L)
    {α : Ω} (hα : α ∈ L) (h : ∀ g ∈ stabilizer G α, g • L = L) : L = Set.univ := by
  obtain ⟨x, hx, -, -, -, -, -, -, hxα, -, -, -, -, -, -, -, -, -⟩ :=
    exists_four_of_seven_le hL.seven_le α
  have : Nontrivial Ω := ⟨⟨x, α, hxα⟩⟩
  obtain ⟨t, ht, htL⟩ := hL.exists_mem_longInvAt hx
  have hle : stabilizer G α ≤ stabilizer G L := fun g hg => h g hg
  have hlt : stabilizer G α < stabilizer G L := by
    refine lt_of_le_of_ne hle fun heq => hxα ?_
    have htα : t • α = α := mem_stabilizer_iff.mp (heq ▸ htL : t ∈ stabilizer G α)
    exact (ht.1.2.unique ht.2 htα)
  have htop := (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G α).2 _ hlt
  refine Set.eq_univ_of_forall fun ω => ?_
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G α ω
  have hg : g ∈ stabilizer G L := htop ▸ Subgroup.mem_top g
  rw [← mem_stabilizer_iff.mp hg]
  exact Set.smul_mem_smul_set hα

end Geometry

section LineKer

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
@[expose] def linesThrough (Λ : Set Ω) (x : Ω) : Set (Set Ω) :=
  {L | (∃ g : G, g • Λ = L) ∧ x ∈ L}

variable (G) in
@[expose] def lineKer (Λ : Set Ω) (x : Ω) (L : Set Ω) : Subgroup G :=
  Subgroup.closure (longInvAt G Ω x) ⊓
    ⨅ L' ∈ {L' | L' ∈ linesThrough G Λ x ∧ L' ≠ L}, fixingSubgroup G L'

variable {Λ : Set Ω}

theorem mem_linesThrough {x : Ω} {L : Set Ω} :
    L ∈ linesThrough G Λ x ↔ (∃ g : G, g • Λ = L) ∧ x ∈ L := Iff.rfl

theorem smul_mem_linesThrough {x : Ω} {L : Set Ω} (hL : L ∈ linesThrough G Λ x) (g : G) :
    g • L ∈ linesThrough G Λ (g • x) := by
  obtain ⟨⟨h, rfl⟩, hx⟩ := hL
  exact ⟨⟨g * h, mul_smul g h Λ⟩, Set.smul_mem_smul_set hx⟩

theorem mem_lineKer {x : Ω} {L : Set Ω} {k : G} :
    k ∈ lineKer G Λ x L ↔ k ∈ Subgroup.closure (longInvAt G Ω x) ∧
      ∀ L' ∈ linesThrough G Λ x, L' ≠ L → k ∈ fixingSubgroup G L' := by
  simp only [lineKer, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_ofPred_eq, and_imp]

theorem lineKer_le_closure {x : Ω} {L : Set Ω} :
    lineKer G Λ x L ≤ Subgroup.closure (longInvAt G Ω x) := inf_le_left

theorem closure_longInvAt_le_stabilizer {x : Ω} {L : Set Ω} (hL : IsJClosed G Ω L)
    (hx : x ∈ L) : Subgroup.closure (longInvAt G Ω x) ≤ stabilizer G L :=
  (Subgroup.closure_le _).mpr fun t ht => hL x hx t ht

theorem closure_longInvAt_le_stabilizer_point (x : Ω) :
    Subgroup.closure (longInvAt G Ω x) ≤ stabilizer G x :=
  (Subgroup.closure_le _).mpr fun _ ht => ht.2

theorem conj_mem_lineKer {x : Ω} {L : Set Ω} {k : G} (hk : k ∈ lineKer G Λ x L) (g : G) :
    g * k * g⁻¹ ∈ lineKer G Λ (g • x) (g • L) := by
  rw [mem_lineKer] at hk ⊢
  refine ⟨conj_mem_closure_longInvAt hk.1 g, fun L'' hL'' hne => ?_⟩
  have hL' : g⁻¹ • L'' ∈ linesThrough G Λ x := by
    simpa using smul_mem_linesThrough hL'' g⁻¹
  have hne' : g⁻¹ • L'' ≠ L := fun h => hne (by rw [← h, smul_inv_smul])
  have hfix := hk.2 _ hL' hne'
  rw [mem_fixingSubgroup_iff] at hfix ⊢
  intro y hy
  have hy' : g⁻¹ • y ∈ g⁻¹ • L'' := Set.smul_mem_smul_set hy
  rw [mul_smul, mul_smul, hfix _ hy', smul_inv_smul]

theorem lineKer_smul_eq {x : Ω} {L L' : Set Ω} {k : G} (hk : k ∈ lineKer G Λ x L)
    (hL' : L' ∈ linesThrough G Λ x) (hne : L' ≠ L) {y : Ω} (hy : y ∈ L') : k • y = y :=
  (mem_fixingSubgroup_iff G).mp ((mem_lineKer.mp hk).2 L' hL' hne) y hy

end LineKer

section LineKerAlt

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

variable (G) in
@[expose] def LineNonDiagonal (Λ : Set Ω) : Prop :=
  ∀ x : Ω, ∀ L ∈ linesThrough G Λ x, ∀ L' ∈ linesThrough G Λ x, L ≠ L' →
    ∃ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' ∧ ∃ y ∈ L, h • y ≠ y

variable {Λ : Set Ω}

omit [DecidableEq Ω] in
theorem conj_mem_fixingSubgroup {L : Set Ω} {a b : G} (ha : a ∈ stabilizer G L)
    (hb : b ∈ fixingSubgroup G L) : a * b * a⁻¹ ∈ fixingSubgroup G L := by
  rw [mem_fixingSubgroup_iff] at hb ⊢
  intro y hy
  have hy' : a⁻¹ • y ∈ L := Set.mem_smul_set_iff_inv_smul_mem.mp (by rwa [ha])
  rw [mul_smul, mul_smul, hb _ hy', smul_inv_smul]

omit [DecidableEq Ω] in
theorem IsLine.of_mem_linesThrough {G : Type*} [Group G] [MulAction G Ω] [DecidableEq Ω]
    {Λ : Set Ω} (hΛ : IsLine G Λ) {x : Ω} {L : Set Ω} (hL : L ∈ linesThrough G Λ x) :
    IsLine G L := by
  obtain ⟨⟨g, rfl⟩, -⟩ := hL
  exact hΛ.smul g

variable [Finite Ω]

theorem realizes3_closure_inf_fixingSubgroup (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ)
    {x : Ω} {L L' : Set Ω} (hL : L ∈ linesThrough G Λ x) (hL' : L' ∈ linesThrough G Λ x)
    (hne : L ≠ L') :
    Realizes3 (Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G L') x L := by
  have hLl := hΛ.of_mem_linesThrough hL
  have hL'l := hΛ.of_mem_linesThrough hL'
  have hcl : Subgroup.closure (longInvAt G Ω x) ≤ stabilizer G L :=
    closure_longInvAt_le_stabilizer hLl.jClosed hL.2
  have hcl' : Subgroup.closure (longInvAt G Ω x) ≤ stabilizer G L' :=
    closure_longInvAt_le_stabilizer hL'l.jClosed hL'.2
  obtain ⟨h, hh, hfix, y, hy, hmove⟩ := hND x L hL L' hL' hne
  refine Realizes3.of_normal hLl.seven_le hL.2 hcl (hLl.threeCycle x hL.2)
    (inf_le_left.trans hcl) (inf_le_left.trans (closure_longInvAt_le_stabilizer_point x))
    (fun k hk n hn => ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hn.1) (Subgroup.inv_mem _ hk),
      conj_mem_fixingSubgroup (hcl' hk) hn.2⟩) ⟨h, ⟨hh, hfix⟩, y, hy, hmove⟩

theorem realizes3_closure_inf_iInf (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {x : Ω}
    {L : Set Ω} (hL : L ∈ linesThrough G Λ x) (F : Finset (Set Ω))
    (hF : ∀ L' ∈ F, L' ∈ linesThrough G Λ x ∧ L' ≠ L) :
    Realizes3 (Subgroup.closure (longInvAt G Ω x) ⊓ ⨅ L' ∈ F, fixingSubgroup G L') x L := by
  have hLl := hΛ.of_mem_linesThrough hL
  induction F using Finset.induction_on with
  | empty => simpa using hLl.threeCycle x hL.2
  | insert L' F hL'F ih =>
    have ih' := ih fun L'' h => hF L'' (Finset.mem_insert_of_mem h)
    have hL' := hF L' (Finset.mem_insert_self L' F)
    have hK := realizes3_closure_inf_fixingSubgroup hΛ hND hL hL'.1 hL'.2.symm
    refine (ih'.commutator hLl.seven_le hK).mono ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hstab : ∀ {L'' : Set Ω}, L'' ∈ linesThrough G Λ x → ∀ {c : G},
        c ∈ Subgroup.closure (longInvAt G Ω x) → c ∈ stabilizer G L'' := fun hL'' _ hc =>
      closure_longInvAt_le_stabilizer (hΛ.of_mem_linesThrough hL'').jClosed hL''.2 hc
    rw [Finset.iInf_insert]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha.1 hb.1)
      (Subgroup.inv_mem _ ha.1)) (Subgroup.inv_mem _ hb.1), ?_, ?_⟩
    · exact Subgroup.mul_mem _ (conj_mem_fixingSubgroup (hstab hL'.1 ha.1) hb.2)
        (Subgroup.inv_mem _ hb.2)
    · have ha2 := (Subgroup.mem_inf.mp ha).2
      show a * b * a⁻¹ * b⁻¹ ∈ ⨅ L'' ∈ F, fixingSubgroup G L''
      simp only [Subgroup.mem_iInf] at ha2 ⊢
      intro L'' hL''
      have hb'' : b ∈ stabilizer G L'' := hstab (hF L'' (Finset.mem_insert_of_mem hL'')).1 hb.1
      have h1 : b * a⁻¹ * b⁻¹ ∈ fixingSubgroup G L'' :=
        conj_mem_fixingSubgroup hb'' (Subgroup.inv_mem _ (ha2 L'' hL''))
      have h2 : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [h2]
      exact Subgroup.mul_mem _ (ha2 L'' hL'') h1

theorem realizes3_lineKer (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {x : Ω} {L : Set Ω}
    (hL : L ∈ linesThrough G Λ x) : Realizes3 (lineKer G Λ x L) x L := by
  classical
  have hfin : {L' | L' ∈ linesThrough G Λ x ∧ L' ≠ L}.Finite := Set.toFinite _
  refine (realizes3_closure_inf_iInf hΛ hND hL hfin.toFinset fun L' hL' =>
    hfin.mem_toFinset.mp hL').mono (le_of_eq ?_)
  rw [lineKer]
  congr 1
  ext k
  simp only [Subgroup.mem_iInf, Set.Finite.mem_toFinset]

end LineKerAlt

section RealizeMore

variable {G : Type*} [Group G] {Ω : Type*} [DecidableEq Ω] [MulAction G Ω]

omit [DecidableEq Ω] in
theorem exists_two_of_seven_le {L : Set Ω} (h7 : 7 ≤ L.ncard) (x y z : Ω) :
    ∃ b ∈ L, ∃ c ∈ L, b ≠ x ∧ b ≠ y ∧ b ≠ z ∧ c ≠ x ∧ c ≠ y ∧ c ≠ z ∧ b ≠ c := by
  classical
  obtain ⟨b, hb, hb'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, y, z}
    ((Finset.card_le_three).trans_lt (by omega))
  obtain ⟨c, hc, hc'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) {x, y, z, b}
    ((Finset.card_le_four).trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb' hc'
  exact ⟨b, hb, c, hc, hb'.1, hb'.2.1, hb'.2.2, hc'.1, hc'.2.1, hc'.2.2.1, Ne.symm hc'.2.2.2⟩

theorem Realizes3.exists_smul_eq {A : Subgroup G} {x : Ω} {L : Set Ω} (h7 : 7 ≤ L.ncard)
    (h : Realizes3 A x L) {y z : Ω} (hy : y ∈ L) (hz : z ∈ L) (hyx : y ≠ x) (hzx : z ≠ x) :
    ∃ k ∈ A, k • y = z := by
  rcases eq_or_ne y z with rfl | hyz
  · exact ⟨1, Subgroup.one_mem _, one_smul G y⟩
  obtain ⟨w, hw, -, -, hwx, hwy, hwz, -, -, -, -⟩ := exists_two_of_seven_le h7 x y z
  obtain ⟨k, hk, hky⟩ := h y hy z hz w hw hyx hzx hwx hyz (Ne.symm hwy) (Ne.symm hwz)
  exact ⟨k, hk, by rw [hky y hy, cyc3_apply_left hyz (Ne.symm hwy)]⟩

theorem Realizes3.exists_smul_ne {A : Subgroup G} {x : Ω} {L : Set Ω} (h7 : 7 ≤ L.ncard)
    (h : Realizes3 A x L) {y : Ω} (hy : y ∈ L) (hyx : y ≠ x) : ∃ k ∈ A, k • y ≠ y := by
  obtain ⟨z, hz, -, -, hzx, hzy, -, -, -, -, -⟩ := exists_two_of_seven_le h7 x y y
  obtain ⟨k, hk, hkz⟩ := h.exists_smul_eq h7 hy hz hyx hzx
  exact ⟨k, hk, by rw [hkz]; exact hzy⟩

end RealizeMore

section LineFix

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

variable (G) in
@[expose] def lineFix (Λ : Set Ω) (x : Ω) : Subgroup G :=
  stabilizer G x ⊓ ⨅ L ∈ linesThrough G Λ x, fixingSubgroup G L

variable {Λ : Set Ω}

theorem mem_lineFix {x : Ω} {g : G} :
    g ∈ lineFix G Λ x ↔ g • x = x ∧ ∀ L ∈ linesThrough G Λ x, ∀ y ∈ L, g • y = y := by
  simp only [lineFix, Subgroup.mem_inf, mem_stabilizer_iff, Subgroup.mem_iInf,
    mem_fixingSubgroup_iff]

theorem conj_mem_lineFix {x : Ω} {z : G} (hz : z ∈ lineFix G Λ x) (g : G) :
    g * z * g⁻¹ ∈ lineFix G Λ (g • x) := by
  rw [mem_lineFix] at hz ⊢
  refine ⟨by rw [mul_smul, mul_smul, inv_smul_smul, hz.1], fun L hL y hy => ?_⟩
  have hL' : g⁻¹ • L ∈ linesThrough G Λ x := by simpa using smul_mem_linesThrough hL g⁻¹
  rw [mul_smul, mul_smul, hz.2 _ hL' _ (Set.smul_mem_smul_set hy), smul_inv_smul]

theorem lineFix_le_fixingSubgroup {x : Ω} {L : Set Ω} (hL : L ∈ linesThrough G Λ x) :
    lineFix G Λ x ≤ fixingSubgroup G L := fun _ hz =>
  (mem_fixingSubgroup_iff G).mpr ((mem_lineFix.mp hz).2 L hL)

theorem mem_lineFix_of_mem_lineKer {x : Ω} {L : Set Ω} {k : G} (hk : k ∈ lineKer G Λ x L)
    (hkL : k ∈ fixingSubgroup G L) : k ∈ lineFix G Λ x := by
  refine mem_lineFix.mpr ⟨closure_longInvAt_le_stabilizer_point x (lineKer_le_closure hk),
    fun L' hL' y hy => ?_⟩
  rcases eq_or_ne L' L with rfl | hne
  · exact (mem_fixingSubgroup_iff G).mp hkL y hy
  · exact lineKer_smul_eq hk hL' hne hy

variable [DecidableEq Ω] [Finite Ω]

theorem le_lineFix_of_odd [Finite G] (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ)
    {L₀ : Set Ω} {y : Ω} (hL₀ : L₀ ∈ linesThrough G Λ y) {N : Subgroup G}
    (hNP : N ≤ fixingSubgroup G L₀)
    (hPN : ∀ p ∈ fixingSubgroup G L₀, ∀ n ∈ N, p * n * p⁻¹ ∈ N) (hodd : Odd (Nat.card N)) :
    N ≤ lineFix G Λ y := by
  intro n hn
  have hny : n • y = y := (mem_fixingSubgroup_iff G).mp (hNP hn) y hL₀.2
  refine mem_lineFix.mpr ⟨hny, fun L hL => ?_⟩
  rcases eq_or_ne L L₀ with rfl | hLL₀
  · exact (mem_fixingSubgroup_iff G).mp (hNP hn)
  have hLl := hΛ.of_mem_linesThrough hL
  have hK := realizes3_lineKer hΛ hND hL
  have hKL : lineKer G Λ y L ≤ stabilizer G L :=
    lineKer_le_closure.trans (closure_longInvAt_le_stabilizer hLl.jClosed hL.2)
  have hKP : ∀ {k : G}, k ∈ lineKer G Λ y L → k ∈ fixingSubgroup G L₀ := fun hk =>
    (mem_fixingSubgroup_iff G).mpr fun z hz => lineKer_smul_eq hk hL₀ (Ne.symm hLL₀) hz
  have hN' : ∀ m ∈ N ⊓ stabilizer G L, ∀ z ∈ L, m • z = z :=
    Realizes3.smul_eq_of_odd hLl.seven_le hL.2 hKL hK inf_le_right
      (fun m hm => mem_stabilizer_iff.mpr ((mem_fixingSubgroup_iff G).mp (hNP hm.1) y hL₀.2))
      (fun k hk m hm => ⟨hPN k (hKP hk) m hm.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKL hk)
        hm.2) (Subgroup.inv_mem _ (hKL hk))⟩)
      (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left))
  have hnL : n • L = L := by
    by_contra hne
    obtain ⟨z, hz, -, -, -, -, -, -, hzy, -, -, -, -, -, -, -, -, -⟩ :=
      exists_four_of_seven_le hLl.seven_le y
    obtain ⟨h, hh, hhz⟩ := hK.exists_smul_ne hLl.seven_le hz hzy
    have hcN : n * h * n⁻¹ * h⁻¹ ∈ N := by
      have h2 : n * h * n⁻¹ * h⁻¹ = n * (h * n⁻¹ * h⁻¹) := by group
      rw [h2]
      exact N.mul_mem hn (hPN h (hKP hh) n⁻¹ (N.inv_mem hn))
    have hncl : n * h * n⁻¹ ∈ Subgroup.closure (longInvAt G Ω y) := by
      have := conj_mem_closure_longInvAt (lineKer_le_closure hh) n
      rwa [hny] at this
    have hcL : n * h * n⁻¹ * h⁻¹ ∈ stabilizer G L :=
      closure_longInvAt_le_stabilizer hLl.jClosed hL.2
        (Subgroup.mul_mem _ hncl (Subgroup.inv_mem _ (lineKer_le_closure hh)))
    have hnhn : n * h * n⁻¹ ∈ lineKer G Λ y (n • L) := by
      have := conj_mem_lineKer hh n
      rwa [hny] at this
    have hfix : (n * h * n⁻¹) • z = z := lineKer_smul_eq hnhn hL (Ne.symm hne) hz
    have hhzL : h • z ∈ L := by
      rw [← mem_stabilizer_iff.mp (hKL hh)]
      exact Set.smul_mem_smul_set hz
    have hc := hN' _ ⟨hcN, hcL⟩ (h • z) hhzL
    have hc' : (n * h * n⁻¹ * h⁻¹) • (h • z) = (n * h * n⁻¹) • z := by
      rw [mul_smul, inv_smul_smul]
    rw [hc', hfix] at hc
    exact hhz hc.symm
  exact hN' n ⟨hn, hnL⟩

end LineFix

section LineFixBot

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] {Λ : Set Ω}

omit [Finite G] in
theorem Sec4Setting.odd_card_lineFix (hS : Sec4Setting G Ω) {x : Ω} {L₀ : Set Ω}
    (hL₀ : L₀ ∈ linesThrough G Λ x) {β : Ω} (hβ : β ∈ L₀) (hβx : β ≠ x) :
    Odd (Nat.card (lineFix G Λ x)) := by
  have hodd := hS.odd_fixingSubgroup_orbit ⟨β, mem_orbit_self β, hβx, rfl⟩
  refine Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le fun z hz => ⟨(mem_lineFix.mp hz).1, ?_⟩)
  show z ∈ fixingSubgroup G _
  rw [mem_fixingSubgroup_iff]
  rintro _ ⟨h, rfl⟩
  have hL : (h : G) • L₀ ∈ linesThrough G Λ x := by
    have := smul_mem_linesThrough hL₀ (h : G)
    rwa [mem_stabilizer_iff.mp h.2] at this
  exact (mem_lineFix.mp hz).2 _ hL _ (Set.smul_mem_smul_set hβ)

omit [Finite G] in
theorem mem_normalizer_of_conj {Z : Subgroup G} {g : G} (h1 : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z)
    (h2 : ∀ z ∈ Z, g⁻¹ * z * g⁻¹⁻¹ ∈ Z) : g ∈ Subgroup.normalizer (Z : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun z => ⟨h1 z, fun hz => ?_⟩
  have := h2 _ hz
  simpa [mul_assoc] using this

omit [Finite G] [Fintype Ω] [DecidableEq Ω] in
theorem eq_bot_of_normal_of_le_stabilizer [FaithfulSMul G Ω] [IsPretransitive G Ω]
    {Z : Subgroup G} (hZ : Z.Normal) {x : Ω} (hZx : Z ≤ stabilizer G x) : Z = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine FaithfulSMul.eq_of_smul_eq_smul (α := Ω) fun ω => ?_
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x ω
  have h := mem_stabilizer_iff.mp (hZx (hZ.conj_mem z hz g⁻¹))
  rw [one_smul]
  calc z • g • x = g • (g⁻¹ * z * g⁻¹⁻¹) • x := by simp [mul_smul]
    _ = g • x := by rw [h]

theorem Sec4Setting.lineFix_eq_bot [FaithfulSMul G Ω] (hS : Sec4Setting G Ω)
    (hΛ : IsLine G Λ) (hND : LineNonDiagonal G Λ) {x : Ω} {L₀ : Set Ω}
    (hL₀ : L₀ ∈ linesThrough G Λ x) : lineFix G Λ x = ⊥ := by
  have hpre := hS.preprimitive
  have htr := hS.star.isPretransitive
  have hL₀l := hΛ.of_mem_linesThrough hL₀
  have hoddAt : ∀ {y : Ω}, y ∈ L₀ → Odd (Nat.card (lineFix G Λ y)) := fun {y} hy => by
    obtain ⟨β, hβ, -, -, -, -, -, -, hβy, -⟩ := exists_four_of_seven_le hL₀l.seven_le y
    exact hS.odd_card_lineFix ⟨hL₀.1, hy⟩ hβ hβy
  have hle : ∀ {y z : Ω}, y ∈ L₀ → z ∈ L₀ → lineFix G Λ y ≤ lineFix G Λ z := fun {y z} hy hz =>
    le_lineFix_of_odd hΛ hND ⟨hL₀.1, hz⟩ (lineFix_le_fixingSubgroup ⟨hL₀.1, hy⟩)
      (fun p hp m hm => by
        have hpy : p • y = y := (mem_fixingSubgroup_iff G).mp hp y hy
        simpa [hpy] using conj_mem_lineFix hm p)
      (hoddAt hy)
  have hGx : stabilizer G x ≤ Subgroup.normalizer (lineFix G Λ x : Set G) := by
    intro g hg
    have hgx : g • x = x := hg
    have hgx' : g⁻¹ • x = x := mem_stabilizer_iff.mp (Subgroup.inv_mem _ hg)
    refine mem_normalizer_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · have := conj_mem_lineFix hz g
      rwa [hgx] at this
    · have := conj_mem_lineFix hz g⁻¹
      rwa [hgx'] at this
  have hGL : stabilizer G L₀ ≤ Subgroup.normalizer (lineFix G Λ x : Set G) := by
    intro g hg
    have hgx : g • x ∈ L₀ := by rw [← mem_stabilizer_iff.mp hg]; exact Set.smul_mem_smul_set hL₀.2
    have hgx' : g⁻¹ • x ∈ L₀ := by
      rw [← mem_stabilizer_iff.mp (Subgroup.inv_mem _ hg)]; exact Set.smul_mem_smul_set hL₀.2
    exact mem_normalizer_of_conj (fun z hz => hle hgx hL₀.2 (conj_mem_lineFix hz g))
      (fun z hz => hle hgx' hL₀.2 (conj_mem_lineFix hz g⁻¹))
  obtain ⟨y, hy, -, -, -, -, -, -, hyx, -⟩ := exists_four_of_seven_le hL₀l.seven_le x
  obtain ⟨t, ht, htL⟩ := hL₀l.exists_mem_longInvAt hy
  have hlt : stabilizer G x < Subgroup.normalizer (lineFix G Λ x : Set G) := by
    refine lt_of_le_of_ne hGx fun heq => hyx ?_
    have htx : t • x = x := mem_stabilizer_iff.mp (heq ▸ hGL htL)
    exact ht.1.2.unique ht.2 htx
  have : Nontrivial Ω := ⟨⟨x, y, Ne.symm hyx⟩⟩
  have htop := (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G x).2 _ hlt
  exact eq_bot_of_normal_of_le_stabilizer (Subgroup.normalizer_eq_top_iff.mp htop)
    (fun z hz => (mem_lineFix.mp hz).1)

end LineFixBot

end CFSG.Holt.H78
