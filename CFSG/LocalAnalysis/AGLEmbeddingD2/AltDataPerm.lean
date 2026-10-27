module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor

public section

namespace CFSG.AGLEmbeddingD2

namespace AltData

open AltSurvivor Equiv

section Swap

theorem sign_mulLeft₀_of_orderOf {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {g : ZMod p}
    (hg : orderOf g = p - 1) (hg0 : g ≠ 0) : Perm.sign (Equiv.mulLeft₀ g hg0) = -1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  set f := Equiv.mulLeft₀ g hg0 with hf
  have hfapp : ∀ y, f y = g * y := fun y => rfl
  have hsupp : f.support = Finset.univ.erase 0 := by
    ext y
    rw [Perm.mem_support, hfapp]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hy h0
      apply hy
      rw [h0, mul_zero]
    · intro hy h
      have : (g - 1) * y = 0 := by rw [sub_mul, h, one_mul, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact hg1 (sub_eq_zero.mp h')
      · exact hy h'
  have hpow : ∀ n : ℕ, (f ^ n) 1 = g ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Perm.mul_apply, ih, hfapp, pow_succ']
  have hcyc : f.IsCycle := by
    refine ⟨1, ?_, fun y hy => ?_⟩
    · rw [hfapp, mul_one]
      exact hg1
    · have hy0 : y ≠ 0 := by
        intro h0
        apply hy
        rw [hfapp, h0, mul_zero]
      let u : (ZMod p)ˣ := Units.mk0 g hg0
      have hu : orderOf u = p - 1 := by rw [← hg, ← orderOf_units]; rfl
      have hcard : Nat.card (Subgroup.zpowers u) = Nat.card (ZMod p)ˣ := by
        rw [Nat.card_zpowers, hu, Nat.card_eq_fintype_card, ZMod.card_units]
      have htop : Subgroup.zpowers u = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
      have hmem : Units.mk0 y hy0 ∈ Subgroup.zpowers u := by rw [htop]; exact Subgroup.mem_top _
      rw [← mem_powers_iff_mem_zpowers] at hmem
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, ?_⟩
      rw [zpow_natCast, hpow]
      have := congrArg Units.val hn
      simpa [u] using this
  rw [hcyc.sign, hsupp, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ZMod.card]
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  have : p - 1 = 2 * k := by omega
  rw [this, pow_mul]
  simp

theorem pow_val_add_of_pow_eq_one {α : Type*} [Monoid α] {p : ℕ} [NeZero p] {b : α}
    (hb : b ^ p = 1) (i j : ZMod p) : b ^ (i + j).val = b ^ i.val * b ^ j.val := by
  rw [ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ hb).symm

theorem pow_val_apply_injective {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ} [Fact p.Prime]
    {b : Perm Ω} (hb : b.IsCycle) (hbp : b ^ p = 1) {x : Ω} (hx : b x ≠ x) {i j : ZMod p}
    (h : (b ^ i.val) x = (b ^ j.val) x) : i = j := by
  have hord : orderOf b = p := orderOf_eq_prime hbp hb.ne_one
  have h1 : b ^ i.val = b ^ j.val := hb.pow_eq_pow_iff.mpr ⟨x, hx, h⟩
  rw [pow_inj_mod, hord, Nat.mod_eq_of_lt (ZMod.val_lt i), Nat.mod_eq_of_lt (ZMod.val_lt j)]
    at h1
  exact ZMod.val_injective p h1

theorem exists_swap_perm {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {g : ℕ}
    (hg : orderOf (g : ZMod p) = p - 1) {b₁ b₂ : Perm (Fin (2 * p))}
    {O₁ O₂ : Finset (Fin (2 * p))} (hb₁ : b₁.IsCycle) (hb₂ : b₂.IsCycle) (hp₁ : b₁ ^ p = 1)
    (hp₂ : b₂ ^ p = 1) (hs₁ : ∀ x, b₁ x ≠ x ↔ x ∈ O₁) (hs₂ : ∀ x, b₂ x ≠ x ↔ x ∈ O₂)
    (hO₁ : O₁.card = p) (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂) :
    ∃ σ : Perm (Fin (2 * p)), Perm.sign σ = 1 ∧ σ * b₁ = b₂ * σ ∧ σ * b₂ = b₁ ^ g * σ ∧
      ∀ x, x ∈ O₁ ↔ σ x ∈ O₂ := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨x₁, hx₁⟩ : O₁.Nonempty := Finset.card_pos.mp (by rw [hO₁]; exact hp.pos)
  obtain ⟨x₂, hx₂⟩ : O₂.Nonempty := Finset.card_pos.mp (by rw [hO₂]; exact hp.pos)
  have hbx₁ : b₁ x₁ ≠ x₁ := (hs₁ x₁).mpr hx₁
  have hbx₂ : b₂ x₂ ≠ x₂ := (hs₂ x₂).mpr hx₂
  have hn₁₂ : ∀ x, x ∈ O₂ → x ∉ O₁ := fun x hx hx' => Finset.disjoint_left.mp hd hx' hx
  have hn₂₁ : ∀ x, x ∈ O₁ → x ∉ O₂ := fun x hx hx' => Finset.disjoint_left.mp hd hx hx'
  have hfix₁ : ∀ x, x ∈ O₂ → b₁ x = x := fun x hx => by
    by_contra h
    exact hn₁₂ x hx ((hs₁ x).mp h)
  have hfix₂ : ∀ x, x ∈ O₁ → b₂ x = x := fun x hx => by
    by_contra h
    exact hn₂₁ x hx ((hs₂ x).mp h)
  have hmem₁ : ∀ (k : ℕ) x, (b₁ ^ k) x ∈ O₁ ↔ x ∈ O₁ := fun k x =>
    apply_mem_iff_of_commute hs₁ ((Commute.refl b₁).pow_left k).eq x
  have hmem₂ : ∀ (k : ℕ) x, (b₂ ^ k) x ∈ O₂ ↔ x ∈ O₂ := fun k x =>
    apply_mem_iff_of_commute hs₂ ((Commute.refl b₂).pow_left k).eq x
  let E : ZMod p × Fin 2 → Fin (2 * p) := fun t =>
    if t.2 = 0 then (b₁ ^ t.1.val) x₁ else (b₂ ^ t.1.val) x₂
  have hE0 : ∀ i : ZMod p, E (i, 0) = (b₁ ^ i.val) x₁ := fun i => by simp [E]
  have hE1 : ∀ i : ZMod p, E (i, 1) = (b₂ ^ i.val) x₂ := fun i => by simp [E]
  have hE0mem : ∀ i : ZMod p, E (i, 0) ∈ O₁ := fun i => by
    rw [hE0, hmem₁]; exact hx₁
  have hE1mem : ∀ i : ZMod p, E (i, 1) ∈ O₂ := fun i => by
    rw [hE1, hmem₂]; exact hx₂
  have hinj : Function.Injective E := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    fin_cases j <;> fin_cases j'
    · simp only [Fin.zero_eta, hE0] at h
      rw [pow_val_apply_injective hb₁ hp₁ hbx₁ h]
    · exfalso
      simp only [Fin.zero_eta, Fin.mk_one] at h
      exact hn₂₁ _ (hE0mem i) (h ▸ hE1mem i')
    · exfalso
      simp only [Fin.zero_eta, Fin.mk_one] at h
      exact hn₂₁ _ (hE0mem i') (h ▸ hE1mem i)
    · simp only [Fin.mk_one, hE1] at h
      rw [pow_val_apply_injective hb₂ hp₂ hbx₂ h]
  have hbij : Function.Bijective E := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [ZMod.card, Fintype.card_prod, mul_comm]
  let Eq' : ZMod p × Fin 2 ≃ Fin (2 * p) := Equiv.ofBijective E hbij
  have hb₁E0 : ∀ i : ZMod p, b₁ (E (i, 0)) = E (i + 1, 0) := by
    intro i
    rw [hE0, hE0, pow_val_add_of_pow_eq_one hp₁, ZMod.val_one, pow_one, Perm.mul_apply,
      ← Perm.mul_apply, ← Perm.mul_apply, (Commute.self_pow b₁ _).eq]
  have hb₂E1 : ∀ i : ZMod p, b₂ (E (i, 1)) = E (i + 1, 1) := by
    intro i
    rw [hE1, hE1, pow_val_add_of_pow_eq_one hp₂, ZMod.val_one, pow_one, Perm.mul_apply,
      ← Perm.mul_apply, ← Perm.mul_apply, (Commute.self_pow b₂ _).eq]
  have hb₁E1 : ∀ i : ZMod p, b₁ (E (i, 1)) = E (i, 1) := fun i => hfix₁ _ (hE1mem i)
  have hb₂E0 : ∀ i : ZMod p, b₂ (E (i, 0)) = E (i, 0) := fun i => hfix₂ _ (hE0mem i)
  have hpow0 : ∀ (n : ℕ) (i : ZMod p), (b₁ ^ n) (E (i, 0)) = E (i + n, 0) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ', Perm.mul_apply, ih, hb₁E0]
      congr 2
      push_cast
      ring
  have hpow1 : ∀ (n : ℕ) (i : ZMod p), (b₁ ^ n) (E (i, 1)) = E (i, 1) := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih => intro i; rw [pow_succ', Perm.mul_apply, ih, hb₁E1]
  set g' : ZMod p := (g : ZMod p) with hg'
  have hg0 : g' ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hg
    omega
  let ρ₀ : Perm (ZMod p × Fin 2) := prodCongrLeft
    (fun j : Fin 2 => if j = 0 then Equiv.mulLeft₀ g' hg0 else Equiv.refl (ZMod p))
  let τ₀ : Perm (ZMod p × Fin 2) := prodCongrRight (fun _ : ZMod p => swap (0 : Fin 2) 1)
  let σ₀ : Perm (ZMod p × Fin 2) := ρ₀ * τ₀
  have hσ₀0 : ∀ i : ZMod p, σ₀ (i, 0) = (i, 1) := by
    intro i
    simp [σ₀, ρ₀, τ₀]
  have hσ₀1 : ∀ i : ZMod p, σ₀ (i, 1) = (g' * i, 0) := by
    intro i
    simp [σ₀, ρ₀, τ₀]
  let σ : Perm (Fin (2 * p)) := Eq'.permCongr σ₀
  have hσE : ∀ t, σ (E t) = E (σ₀ t) := fun t => by
    show Eq' (σ₀ (Eq'.symm (Eq' t))) = Eq' (σ₀ t)
    rw [Equiv.symm_apply_apply]
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  ·
    have hs : Perm.sign σ = Perm.sign σ₀ := Perm.sign_permCongr Eq' σ₀
    rw [hs]
    show Perm.sign (ρ₀ * τ₀) = 1
    rw [map_mul]
    have h1 : Perm.sign ρ₀ = -1 := by
      rw [Perm.sign_prodCongrLeft, Fin.prod_univ_two]
      simp [sign_mulLeft₀_of_orderOf hp2 hg hg0]
    have h2 : Perm.sign τ₀ = -1 := by
      rw [Perm.sign_prodCongrRight, Finset.prod_const, Perm.sign_swap (by decide), Finset.card_univ,
        ZMod.card]
      exact (hp.eq_two_or_odd'.resolve_left hp2).neg_one_pow
    rw [h1, h2]
    norm_num
  · refine Equiv.ext fun x => ?_
    obtain ⟨⟨i, j⟩, rfl⟩ := hbij.2 x
    fin_cases j
    · simp only [Fin.zero_eta, Perm.mul_apply]
      rw [hb₁E0, hσE, hσE, hσ₀0, hσ₀0, hb₂E1]
    · simp only [Fin.mk_one, Perm.mul_apply]
      rw [hb₁E1, hσE, hσ₀1, hb₂E0]
  · refine Equiv.ext fun x => ?_
    obtain ⟨⟨i, j⟩, rfl⟩ := hbij.2 x
    fin_cases j
    · simp only [Fin.zero_eta, Perm.mul_apply]
      rw [hb₂E0, hσE, hσ₀0, hpow1]
    · simp only [Fin.mk_one, Perm.mul_apply]
      rw [hb₂E1, hσE, hσE, hσ₀1, hσ₀1, hpow0]
      congr 2
      rw [hg']
      ring
  · intro x
    obtain ⟨⟨i, j⟩, rfl⟩ := hbij.2 x
    fin_cases j
    · simp only [Fin.zero_eta]
      rw [hσE, hσ₀0]
      exact ⟨fun _ => hE1mem i, fun _ => hE0mem i⟩
    · simp only [Fin.mk_one]
      rw [hσE, hσ₀1]
      exact ⟨fun h => absurd h (hn₁₂ _ (hE1mem i)), fun h => absurd (hE0mem _) (hn₁₂ _ h)⟩

end Swap

section AltOnLemmas

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_one_of_mem_altOn_of_mem_altOn {O₁ O₂ : Finset Ω} (hd : Disjoint O₁ O₂) {g : Perm Ω}
    (h₁ : g ∈ altOn O₁) (h₂ : g ∈ altOn O₂) : g = 1 := by
  rw [mem_altOn] at h₁ h₂
  ext x
  by_cases hx : x ∈ O₁
  · exact h₂.2 x (Finset.disjoint_left.mp hd hx)
  · exact h₁.2 x hx

theorem commute_of_mem_altOn {O₁ O₂ : Finset Ω} (hd : Disjoint O₁ O₂) {a b : Perm Ω}
    (ha : a ∈ altOn O₁) (hb : b ∈ altOn O₂) : Commute a b := by
  rw [mem_altOn] at ha hb
  refine (Perm.Disjoint.commute fun x => ?_)
  by_cases hx : x ∈ O₁
  · exact Or.inr (hb.2 x (Finset.disjoint_left.mp hd hx))
  · exact Or.inl (ha.2 x hx)

theorem altOn_eq_map (O : Finset Ω) :
    altOn O = (alternatingGroup O).map (Perm.ofSubtype : Perm O →* Perm Ω) := by
  ext g
  rw [mem_altOn, alternatingGroup.map_ofSubtype, Subgroup.mem_inf, Perm.mem_range_ofSubtype_iff,
    Perm.mem_alternatingGroup, and_comm]
  refine and_congr_left fun _ => ?_
  constructor
  · intro h x hx
    by_contra hxO
    exact (Perm.mem_support.mp hx) (h x hxO)
  · intro h x hx
    by_contra hne
    exact hx (h (Perm.mem_support.mpr hne))

theorem commutator_altOn {O : Finset Ω} (hO : 5 ≤ O.card) : ⁅altOn O, altOn O⁆ = altOn O := by
  rw [altOn_eq_map, ← Subgroup.map_commutator, commutator_alternatingGroup_eq_self]
  simpa using hO

theorem commutator_le_self_of {G : Type*} [Group G] (B : Subgroup G) : ⁅B, B⁆ ≤ B :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem ha hb) (B.inv_mem ha)) (B.inv_mem hb)

theorem commutator_altOn_sup {O₁ O₂ : Finset Ω} (h₁ : 5 ≤ O₁.card) (h₂ : 5 ≤ O₂.card) :
    ⁅altOn O₁ ⊔ altOn O₂, altOn O₁ ⊔ altOn O₂⁆ = altOn O₁ ⊔ altOn O₂ :=
  le_antisymm (commutator_le_self_of _) (sup_le
    ((commutator_altOn h₁).symm.le.trans (Subgroup.commutator_mono le_sup_left le_sup_left))
    ((commutator_altOn h₂).symm.le.trans (Subgroup.commutator_mono le_sup_right le_sup_right)))

end AltOnLemmas

section AltEquiv

variable {p : ℕ}

@[expose] noncomputable def altEquiv (O : Finset (Fin (2 * p))) (hO : O.card = p) :
    alternatingGroup (Fin p) ≃* altOn O :=
  ((Equiv.altCongrHom (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hO])).symm).trans
    (Subgroup.equivMapOfInjective _ (Perm.ofSubtype : Perm O →* Perm (Fin (2 * p)))
      Perm.ofSubtype_injective)).trans (MulEquiv.subgroupCongr (altOn_eq_map O).symm)

@[expose] noncomputable def altPairHom {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂) :
    alternatingGroup (Fin p) × alternatingGroup (Fin p) →* Perm (Fin (2 * p)) :=
  MonoidHom.noncommCoprod ((altOn O₁).subtype.comp (altEquiv O₁ hO₁).toMonoidHom)
    ((altOn O₂).subtype.comp (altEquiv O₂ hO₂).toMonoidHom)
    (fun u v => commute_of_mem_altOn hd (altEquiv O₁ hO₁ u).2 (altEquiv O₂ hO₂ v).2)

theorem altPairHom_apply {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂)
    (t : alternatingGroup (Fin p) × alternatingGroup (Fin p)) :
    altPairHom hO₁ hO₂ hd t = (altEquiv O₁ hO₁ t.1 : Perm (Fin (2 * p))) *
      (altEquiv O₂ hO₂ t.2 : Perm (Fin (2 * p))) := rfl

theorem altPairHom_injective {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂) : Function.Injective (altPairHom hO₁ hO₂ hd) := by
  rw [altPairHom, MonoidHom.noncommCoprod_injective]
  refine ⟨(Subtype.val_injective.comp (altEquiv O₁ hO₁).injective),
    (Subtype.val_injective.comp (altEquiv O₂ hO₂).injective), ?_⟩
  rw [Subgroup.disjoint_def]
  intro x hx₁ hx₂
  obtain ⟨u, rfl⟩ := hx₁
  obtain ⟨v, hv⟩ := hx₂
  exact eq_one_of_mem_altOn_of_mem_altOn hd (altEquiv O₁ hO₁ u).2 (hv ▸ (altEquiv O₂ hO₂ v).2)

theorem range_altEquiv (O : Finset (Fin (2 * p))) (hO : O.card = p) :
    ((altOn O).subtype.comp (altEquiv O hO).toMonoidHom).range = altOn O := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (altEquiv O hO).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem altPairHom_range {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂) :
    (altPairHom hO₁ hO₂ hd).range = altOn O₁ ⊔ altOn O₂ := by
  rw [altPairHom, MonoidHom.noncommCoprod_range, range_altEquiv, range_altEquiv]

@[expose] noncomputable def altPairEquiv {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂) :
    alternatingGroup (Fin p) × alternatingGroup (Fin p) ≃* ↥(altOn O₁ ⊔ altOn O₂) :=
  (MonoidHom.ofInjective (altPairHom_injective hO₁ hO₂ hd)).trans
    (MulEquiv.subgroupCongr (altPairHom_range hO₁ hO₂ hd))

theorem coe_altPairEquiv {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂)
    (t : alternatingGroup (Fin p) × alternatingGroup (Fin p)) :
    (altPairEquiv hO₁ hO₂ hd t : Perm (Fin (2 * p))) = altPairHom hO₁ hO₂ hd t := rfl

theorem altPairEquiv_mem_left_iff {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂)
    (t : alternatingGroup (Fin p) × alternatingGroup (Fin p)) :
    (altPairEquiv hO₁ hO₂ hd t : Perm (Fin (2 * p))) ∈ altOn O₁ ↔ t.2 = 1 := by
  rw [coe_altPairEquiv, altPairHom_apply]
  constructor
  · intro h
    have h2 : (altEquiv O₂ hO₂ t.2 : Perm (Fin (2 * p))) ∈ altOn O₁ := by
      have := (altOn O₁).mul_mem ((altOn O₁).inv_mem (altEquiv O₁ hO₁ t.1).2) h
      simpa using this
    have h3 := eq_one_of_mem_altOn_of_mem_altOn hd h2 (altEquiv O₂ hO₂ t.2).2
    exact (altEquiv O₂ hO₂).injective (Subtype.ext (by simpa using h3))
  · intro h
    rw [h]
    simp

theorem altPairEquiv_mem_right_iff {O₁ O₂ : Finset (Fin (2 * p))} (hO₁ : O₁.card = p)
    (hO₂ : O₂.card = p) (hd : Disjoint O₁ O₂)
    (t : alternatingGroup (Fin p) × alternatingGroup (Fin p)) :
    (altPairEquiv hO₁ hO₂ hd t : Perm (Fin (2 * p))) ∈ altOn O₂ ↔ t.1 = 1 := by
  rw [coe_altPairEquiv, altPairHom_apply]
  constructor
  · intro h
    have h2 : (altEquiv O₁ hO₁ t.1 : Perm (Fin (2 * p))) ∈ altOn O₂ := by
      have := (altOn O₂).mul_mem h ((altOn O₂).inv_mem (altEquiv O₂ hO₂ t.2).2)
      simpa using this
    have h3 := eq_one_of_mem_altOn_of_mem_altOn hd (altEquiv O₁ hO₁ t.1).2 h2
    exact (altEquiv O₁ hO₁).injective (Subtype.ext (by simpa using h3))
  · intro h
    rw [h]
    simp

end AltEquiv

theorem mem_normalizer_of_conj_mem {Y : Type*} [Group Y] [Finite Y] {A : Subgroup Y} {k : Y}
    (h : ∀ x ∈ A, k * x * k⁻¹ ∈ A) : k ∈ Subgroup.normalizer (A : Set Y) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]

theorem exists_perfect_lift {Y Q : Type*} [Group Y] [Finite Y] [Group Q] (π : Y →* Q)
    {B : Subgroup Q} (hB : ⁅B, B⁆ = B) (hBπ : B ≤ π.range) :
    ∃ W : Subgroup Y, W ≤ B.comap π ∧ ⁅W, W⁆ = W ∧ W.map π = B ∧
      ∀ L : Subgroup Y, L ≤ B.comap π → ⁅L, L⁆ = L → L ≤ W := by
  obtain ⟨L₀, ⟨hL₀, hL₀B⟩, hmin⟩ := Set.exists_min_image
    {L : Subgroup Y | L ≤ B.comap π ∧ L.map π = B} (fun L => Nat.card L) (Set.toFinite _)
    ⟨B.comap π, le_rfl, Subgroup.map_comap_eq_self hBπ⟩
  have hperf : ⁅L₀, L₀⁆ = L₀ := by
    have hle : ⁅L₀, L₀⁆ ≤ L₀ := Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact L₀.mul_mem (L₀.mul_mem (L₀.mul_mem ha hb) (L₀.inv_mem ha)) (L₀.inv_mem hb)
    have hmem : ⁅L₀, L₀⁆ ∈ {L : Subgroup Y | L ≤ B.comap π ∧ L.map π = B} :=
      ⟨hle.trans hL₀, by rw [Subgroup.map_commutator, hL₀B, hB]⟩
    exact Subgroup.eq_of_le_of_card_ge hle (hmin _ hmem)
  refine ⟨sSup {L : Subgroup Y | L ≤ B.comap π ∧ ⁅L, L⁆ = L}, ?_, ?_, ?_, ?_⟩
  · exact sSup_le fun L hL => hL.1
  · refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      set W := sSup {L : Subgroup Y | L ≤ B.comap π ∧ ⁅L, L⁆ = L}
      exact W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)
    · refine sSup_le fun L hL => ?_
      calc L = ⁅L, L⁆ := hL.2.symm
        _ ≤ ⁅sSup {L : Subgroup Y | L ≤ B.comap π ∧ ⁅L, L⁆ = L},
            sSup {L : Subgroup Y | L ≤ B.comap π ∧ ⁅L, L⁆ = L}⁆ :=
          Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (sSup_le fun L hL => hL.1)) ?_
    exact hL₀B.symm.le.trans (Subgroup.map_mono (le_sSup ⟨hL₀, hperf⟩))
  · intro L hL hLL
    exact le_sSup ⟨hL, hLL⟩

theorem mem_normalizer_of_perfect_lift {Y Q : Type*} [Group Y] [Finite Y] [Group Q] (π : Y →* Q)
    {B : Subgroup Q} {W : Subgroup Y}
    (hmax : ∀ L : Subgroup Y, L ≤ B.comap π → ⁅L, L⁆ = L → L ≤ W) (hW : W ≤ B.comap π)
    (hWW : ⁅W, W⁆ = W) {y : Y} (hy : π y ∈ Subgroup.normalizer (B : Set Q)) :
    y ∈ Subgroup.normalizer (W : Set Y) := by
  have key : ∀ y : Y, π y ∈ Subgroup.normalizer (B : Set Q) → ∀ x ∈ W, y * x * y⁻¹ ∈ W := by
    intro y hy x hx
    have hle : W.map (MulAut.conj y).toMonoidHom ≤ W := by
      refine hmax _ ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        show π (y * x * y⁻¹) ∈ B
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp hy _).mp (hW hx)
      · rw [← Subgroup.map_commutator, hWW]
    exact hle ⟨x, hx, rfl⟩
  exact mem_normalizer_of_conj_mem (key y hy)

theorem exists_hom_onto {Y Q S T : Type*} [Group Y] [Group Q] [Group S] [Group T] (π : Y →* Q)
    (ι : Q →* S) (hι : Function.Injective ι) {Bhat : Subgroup S} (Λe : T ≃* Bhat)
    (hBhat : Bhat ≤ ι.range) (W : Subgroup Y) (hW : W.map π = Bhat.comap ι) :
    ∃ ψ : W →* T, Function.Surjective ψ ∧ ψ.ker = π.ker.subgroupOf W ∧
      ∀ w : W, ((Λe (ψ w) : Bhat) : S) = ι (π w) := by
  have hf : ∀ w : W, ι (π w) ∈ Bhat := fun w => by
    have : π w ∈ W.map π := Subgroup.mem_map_of_mem π w.2
    rw [hW] at this
    exact this
  let f' : W →* Bhat := (ι.comp (π.comp W.subtype)).codRestrict Bhat hf
  have hf' : ∀ w : W, ((f' w : Bhat) : S) = ι (π w) := fun w => rfl
  refine ⟨Λe.symm.toMonoidHom.comp f', ?_, ?_, ?_⟩
  · intro t
    obtain ⟨q, hq⟩ := hBhat (Λe t).2
    have hqW : q ∈ W.map π := by
      rw [hW]
      show ι q ∈ Bhat
      rw [hq]
      exact (Λe t).2
    obtain ⟨w, hw, hwq⟩ := hqW
    refine ⟨⟨w, hw⟩, ?_⟩
    have : f' ⟨w, hw⟩ = Λe t := Subtype.ext (by rw [hf', ← hq]; simp [hwq])
    simp [this]
  · ext w
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.mem_subgroupOf, map_eq_one_iff _ Λe.symm.injective]
    constructor
    · intro h
      have : ((f' w : Bhat) : S) = 1 := by rw [h]; rfl
      rw [hf'] at this
      exact (map_eq_one_iff _ hι).mp this
    · intro h
      apply Subtype.ext
      rw [hf']
      show ι (π w) = 1
      rw [show π w = 1 from h, map_one]
  · intro w
    simp [hf']

end AltData

end CFSG.AGLEmbeddingD2
