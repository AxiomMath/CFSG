module

public import CFSG.Holt.H78.Sec4LineCoord
public import CFSG.Holt.H78.SEModelFive
public import CFSG.Holt.H78.Sec4Prop49

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise


section Count

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Finite Ω] [MulAction G Ω]

theorem card_longInvAt_eq_mul {α β γ₀ : Ω}
    (hΔ' : holtDelta' G Ω α β = orbit ↥(stabilizer G α ⊓ stabilizer G β) γ₀) :
    Nat.card (longInvAt G Ω α) =
      Nat.card {s : longInvAt G Ω α // (s : G) • β = γ₀} * Nat.card (holtDelta' G Ω α β) := by
  set f : longInvAt G Ω α → Ω := fun s => (s : G) • β
  have huniv : f ⁻¹' holtDelta' G Ω α β = Set.univ :=
    Set.eq_univ_of_forall fun s => ⟨s, s.2, rfl⟩
  have hl : ∀ γ ∈ holtDelta' G Ω α β, Nat.card {s // f s = γ} =
      Nat.card {s : longInvAt G Ω α // (s : G) • β = γ₀} := by
    intro γ hγ
    rw [hΔ'] at hγ
    obtain ⟨⟨g, hg⟩, rfl⟩ := hγ
    have hgα : g • α = α := (Subgroup.mem_inf.mp hg).1
    have hgβ : g • β = β := (Subgroup.mem_inf.mp hg).2
    have hc : ∀ {s : G}, s ∈ longInvAt G Ω α → g⁻¹ * s * g ∈ longInvAt G Ω α := fun hs => by
      have := conj_mem_longInvAt hs g⁻¹
      rwa [inv_smul_eq_iff.mpr hgα.symm, inv_inv] at this
    have hc' : ∀ {s : G}, s ∈ longInvAt G Ω α → g * s * g⁻¹ ∈ longInvAt G Ω α := fun hs => by
      have := conj_mem_longInvAt hs g
      rwa [hgα] at this
    refine Nat.card_congr
      { toFun := fun s => ⟨⟨g⁻¹ * s.1 * g, hc s.1.2⟩, ?_⟩
        invFun := fun s => ⟨⟨g * s.1 * g⁻¹, hc' s.1.2⟩, ?_⟩
        left_inv := fun s => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
        right_inv := fun s => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
    · have h := s.2
      simp only [f] at h
      show (g⁻¹ * s.1 * g) • β = γ₀
      rw [mul_smul, mul_smul, hgβ, h, show ((⟨g, hg⟩ : ↥(stabilizer G α ⊓ stabilizer G β)) •
        γ₀ : Ω) = g • γ₀ from rfl, inv_smul_smul]
    · show (g * s.1 * g⁻¹) • β = _
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hgβ.symm, s.2]
      rfl
  have := card_preimage_eq_mul f hl
  rw [huniv, Nat.card_univ] at this
  exact this

theorem card_longInvSwap_eq_mul {α β γ₀ : Ω} (hγ₀ : γ₀ ∈ holtDelta G Ω α β) :
    Nat.card (longInvSwap G Ω α β) =
      Nat.card {t : longInvSwap G Ω α β // (t : G) • γ₀ = γ₀} * Nat.card (holtDelta G Ω α β) := by
  set f : longInvSwap G Ω α β → Ω := fun t => Classical.choose (t.2.1.2.exists)
  have hf : ∀ t : longInvSwap G Ω α β, (t : G) • f t = f t := fun t =>
    Classical.choose_spec t.2.1.2.exists
  have hf' : ∀ (t : longInvSwap G Ω α β) (ω : Ω), (t : G) • ω = ω → f t = ω := fun t ω hω =>
    t.2.1.2.unique (hf t) hω
  have huniv : f ⁻¹' holtDelta G Ω α β = Set.univ :=
    Set.eq_univ_of_forall fun t => ⟨t, t.2, hf t⟩
  have hfib : ∀ γ, Nat.card {t // f t = γ} =
      Nat.card {t : longInvSwap G Ω α β // (t : G) • γ = γ} :=
    fun γ => Nat.card_congr (Equiv.subtypeEquivRight fun t =>
      ⟨fun h => h ▸ hf t, fun h => hf' t γ h⟩)
  have hl : ∀ γ ∈ holtDelta G Ω α β, Nat.card {t // f t = γ} =
      Nat.card {t : longInvSwap G Ω α β // (t : G) • γ₀ = γ₀} := by
    intro γ hγ
    rw [hfib, holtDelta_eq_orbit_of_mem hγ₀] at *
    obtain ⟨⟨g, hg⟩, rfl⟩ := hγ
    have hgα : g • α = α := (Subgroup.mem_inf.mp hg).1
    have hgβ : g • β = β := (Subgroup.mem_inf.mp hg).2
    have hc : ∀ {t : G}, t ∈ longInvSwap G Ω α β → g⁻¹ * t * g ∈ longInvSwap G Ω α β :=
      fun ht => by
        have := conj_mem_longInvSwap ht g⁻¹
        rwa [inv_smul_eq_iff.mpr hgα.symm, inv_smul_eq_iff.mpr hgβ.symm, inv_inv] at this
    have hc' : ∀ {t : G}, t ∈ longInvSwap G Ω α β → g * t * g⁻¹ ∈ longInvSwap G Ω α β :=
      fun ht => by
        have := conj_mem_longInvSwap ht g
        rwa [hgα, hgβ] at this
    refine Nat.card_congr
      { toFun := fun t => ⟨⟨g⁻¹ * t.1 * g, hc t.1.2⟩, ?_⟩
        invFun := fun t => ⟨⟨g * t.1 * g⁻¹, hc' t.1.2⟩, ?_⟩
        left_inv := fun t => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
        right_inv := fun t => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
    · have h : (t.1 : G) • g • γ₀ = g • γ₀ := t.2
      show (g⁻¹ * t.1 * g) • γ₀ = γ₀
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    · show (g * t.1 * g⁻¹) • ((⟨g, hg⟩ : ↥(stabilizer G α ⊓ stabilizer G β)) • γ₀) =
        (⟨g, hg⟩ : ↥(stabilizer G α ⊓ stabilizer G β)) • γ₀
      show (g * t.1 * g⁻¹) • g • γ₀ = g • γ₀
      rw [mul_smul, mul_smul, inv_smul_smul, t.2]
  have := card_preimage_eq_mul f hl
  rw [huniv, Nat.card_univ] at this
  exact this

end Count

section SETriple

variable {X : Type} [Group X] [Finite X] {Ψ : Type}
  [MulAction X Ψ] {n k e : ℕ}

theorem IsBenderAction.exists_triple (hA : IsBenderAction X Ψ n k e) {a b : Ψ} (hab : a ≠ b) :
    ∃ y ∈ longInvAt X Ψ a, ∃ m : X, m • b = a ∧ m • y • b = b ∧ m • a ∈ holtDelta X Ψ a b := by
  have := hA.finite
  have hne : (longInvAt X Ψ a).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hA.ncard_longInvAt]
    have := hA.four_le_q
    omega
  obtain ⟨y, hy⟩ := hne
  have hyb : y • b ≠ b := fun h => hab (hy.1.2.unique hy.2 h)
  have := hA.isPretransitive
  obtain ⟨x, hx⟩ := exists_smul_eq X b a
  have hxyb : x • y • b ≠ a := fun h => hyb (smul_left_cancel x (h.trans hx.symm))
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer a
  obtain ⟨p, hp, hpx⟩ := hA.exists_mem_smul_eq hQ hxyb (Ne.symm hab)
  have hpa : p • a = a := hQ hp
  have hm : (p * x) • b = a := by rw [mul_smul, hx, hpa]
  have hm' : (p * x)⁻¹ • a = b := by rw [inv_smul_eq_iff, hm]
  refine ⟨y, hy, p * x, hm, by rw [mul_smul, hpx], (p * x) * y * (p * x)⁻¹,
    ⟨conj_mem_longInv hy.1 _, ?_⟩, ?_⟩
  · rw [mul_smul, mul_smul, hm', mul_smul, hpx]
  · rw [mul_smul, mul_smul, inv_smul_smul, hy.2]

end SETriple

section SEGen


theorem IsNaturalSE.le_closure_longInv {Δ : Type} [Finite Δ] {M : Subgroup (Equiv.Perm Δ)}
    (hM : IsNaturalSE M) :
    M ≤ Subgroup.closure {y | y ∈ M ∧ y ∈ longInv (Equiv.Perm Δ) Δ} := by
  obtain ⟨n, k, e, hA⟩ := hM.exists_isBenderAction
  have := hA.benderType.isSimple
  set S : Set (Equiv.Perm Δ) := {y | y ∈ M ∧ y ∈ longInv (Equiv.Perm Δ) Δ}
  set N : Subgroup M := (Subgroup.closure S).subgroupOf M
  have hN : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hle : Subgroup.closure S ≤
        (Subgroup.closure S).comap (MulAut.conj (g : Equiv.Perm Δ)).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      exact Subgroup.subset_closure ⟨M.mul_mem (M.mul_mem g.2 hy.1) (M.inv_mem g.2),
        conj_mem_longInv hy.2 _⟩
    simpa using hle hx
  have hne : N ≠ ⊥ := by
    obtain ⟨ψ⟩ : Nonempty Δ := by
      have h := hA.card_eq
      exact Nat.card_pos_iff.mp (by omega) |>.1
    have hJ : (longInvAt (↥M) Δ ψ).Nonempty := by
      have := hA.finite
      apply Set.nonempty_of_ncard_ne_zero
      rw [hA.ncard_longInvAt]
      have := hA.four_le_q
      omega
    obtain ⟨y, hy⟩ := hJ
    refine (Subgroup.ne_bot_iff_exists_ne_one).mpr ⟨⟨y, Subgroup.mem_subgroupOf.mpr
      (Subgroup.subset_closure ⟨y.2, mem_longInv_subgroup_iff.mp hy.1⟩)⟩, fun h1 => ?_⟩
    have h2 := hy.1.1
    have : y = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact absurd h hne
  · intro m hm
    have : (⟨m, hm⟩ : M) ∈ N := h ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end SEGen

namespace P49Config

section Line

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

@[expose] noncomputable def lpt (ψ : C.D.Ψc C.i) : fixSet Ω (Subgroup.zpowers v) :=
  Function.surjInv C.D.coord_surjective (Function.update (C.D.coord C.a) C.i ψ)

@[expose] def line : Set Ω := Set.range fun ψ => (C.lpt ψ : Ω)

@[expose] def LineActs (g : G) (m : Equiv.Perm (C.D.Ψc C.i)) : Prop :=
  ∀ ψ, g • (C.lpt ψ : Ω) = C.lpt (m ψ)

theorem coord_lpt (ψ : C.D.Ψc C.i) :
    C.D.coord (C.lpt ψ) = Function.update (C.D.coord C.a) C.i ψ :=
  Function.surjInv_eq C.D.coord_surjective _

theorem coord_lpt_self (ψ : C.D.Ψc C.i) : C.D.coord (C.lpt ψ) C.i = ψ := by
  rw [coord_lpt, Function.update_self]

theorem coord_lpt_of_ne (ψ : C.D.Ψc C.i) {j : C.D.ι} (hj : j ≠ C.i) :
    C.D.coord (C.lpt ψ) j = C.D.coord C.a j := by
  rw [coord_lpt, Function.update_of_ne hj]

theorem lpt_injective : Function.Injective C.lpt := fun ψ ψ' h => by
  rw [← C.coord_lpt_self ψ, ← C.coord_lpt_self ψ', h]

theorem lpt_mem_line (ψ : C.D.Ψc C.i) : (C.lpt ψ : Ω) ∈ C.line := ⟨ψ, rfl⟩

theorem lpt_coe_injective : Function.Injective fun ψ => (C.lpt ψ : Ω) :=
  Subtype.val_injective.comp C.lpt_injective

theorem line_subset_fixSet : C.line ⊆ fixSet Ω (Subgroup.zpowers v) := by
  rintro _ ⟨ψ, rfl⟩
  exact (C.lpt ψ).2

theorem lineActs_one : C.LineActs 1 1 := fun ψ => by rw [one_smul, Equiv.Perm.one_apply]

variable {C}

theorem LineActs.mul {g g' : G} {m m' : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m)
    (h' : C.LineActs g' m') : C.LineActs (g * g') (m * m') := fun ψ => by
  rw [mul_smul, h', h, Equiv.Perm.mul_apply]

theorem LineActs.inv {g : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m) :
    C.LineActs g⁻¹ m⁻¹ := fun ψ => by
  rw [inv_smul_eq_iff, h]
  simp

theorem LineActs.smul_mem {g : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m)
    {ω : Ω} (hω : ω ∈ C.line) : g • ω ∈ C.line := by
  obtain ⟨ψ, rfl⟩ := hω
  exact ⟨m ψ, (h ψ).symm⟩

theorem LineActs.smul_line {g : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m) :
    g • C.line = C.line := by
  refine Set.Subset.antisymm ?_ fun ω hω => ?_
  · rintro _ ⟨ω, hω, rfl⟩
    exact h.smul_mem hω
  · refine ⟨g⁻¹ • ω, h.inv.smul_mem hω, smul_inv_smul g ω⟩

theorem LineActs.unique {g : G} {m m' : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs g m)
    (h' : C.LineActs g m') : m = m' :=
  Equiv.ext fun ψ => C.lpt_injective (Subtype.ext ((h ψ).symm.trans (h' ψ)))

end Line

section Coord

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [MulAction G Ω] {α : Ω} {v : G}
  (C : P49Config G Ω α v)

theorem lpt_coord_a : C.lpt (C.D.coord C.a C.i) = C.a :=
  C.coord_injective (by rw [coord_lpt]; exact Function.update_eq_self _ _)

theorem lpt_coord_b : C.lpt (C.D.coord C.b C.i) = C.b :=
  C.coord_injective (funext fun j => by
    rcases eq_or_ne j C.i with rfl | hj
    · rw [coord_lpt_self]
    · rw [coord_lpt_of_ne _ _ hj, C.coord_eq j hj])

theorem α_mem_line : α ∈ C.line :=
  ⟨C.D.coord C.a C.i, by simp only [lpt_coord_a, C.coe_a]⟩

theorem β_mem_line : C.β ∈ C.line :=
  ⟨C.D.coord C.b C.i, by simp only [lpt_coord_b]⟩

theorem lpt_eq_of_coord {x : fixSet Ω (Subgroup.zpowers v)}
    (hx : ∀ j, j ≠ C.i → C.D.coord x j = C.D.coord C.a j) : C.lpt (C.D.coord x C.i) = x :=
  C.coord_injective (funext fun j => by
    rcases eq_or_ne j C.i with rfl | hj
    · rw [coord_lpt_self]
    · rw [coord_lpt_of_ne _ _ hj, hx j hj])

variable {C} in
theorem LineActs.smul_α {c : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs c m) :
    c • α = C.lpt (m (C.D.coord C.a C.i)) := by
  have e := h (C.D.coord C.a C.i)
  rwa [C.lpt_coord_a, C.coe_a] at e

variable {C} in
theorem LineActs.smul_β {c : G} {m : Equiv.Perm (C.D.Ψc C.i)} (h : C.LineActs c m) :
    c • C.β = C.lpt (m (C.D.coord C.b C.i)) := by
  have e := h (C.D.coord C.b C.i)
  rwa [C.lpt_coord_b] at e

theorem smul_lpt {π : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v))}
    (hπ : ∀ j, j ≠ C.i → C.D.ρ j π (C.D.coord C.a j) = C.D.coord C.a j) (ψ : C.D.Ψc C.i) :
    (π : typeLSection G Ω v) • C.lpt ψ = C.lpt (C.D.ρ C.i π ψ) :=
  C.coord_injective (funext fun j => by
    rw [C.D.coord_smul]
    rcases eq_or_ne j C.i with rfl | hj
    · rw [coord_lpt_self, coord_lpt_self]
    · rw [coord_lpt_of_ne _ _ hj, coord_lpt_of_ne _ _ hj, hπ j hj])

theorem exists_lineActs_of_mem {m : Equiv.Perm (C.D.Ψc C.i)} (hm : m ∈ C.D.M C.i) :
    ∃ c ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G), C.LineActs c m := by
  obtain ⟨h, hhL, hρ⟩ := mem_factorImage.mp hm
  obtain ⟨c, hc, hch⟩ := mem_centralizerImage.mp (h : typeLSection G Ω v).2
  refine ⟨c, hc, fun ψ => ?_⟩
  have h1 : (h : typeLSection G Ω v) • C.lpt ψ = C.lpt (m ψ) := by
    rw [← hρ]
    exact C.smul_lpt (fun j hj => by
      rw [C.D.rho_eq_one_of_mem_L (Ne.symm hj) hhL, Equiv.Perm.one_apply]) ψ
  rw [← hch, ← h1]
  rfl

end Coord

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

theorem exists_lineActs_longInvAt (hS : Sec4Setting G Ω) {y : Equiv.Perm (C.D.Ψc C.i)}
    (hyM : y ∈ C.D.M C.i) {ψ₀ : C.D.Ψc C.i}
    (hy : y ∈ longInvAt (Equiv.Perm (C.D.Ψc C.i)) (C.D.Ψc C.i) ψ₀) :
    ∃ s ∈ longInvAt G Ω (C.lpt ψ₀ : Ω),
      s ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ∧ C.LineActs s y := by
  obtain ⟨t₀, ht₀⟩ := C.D.longInvAt_nonempty C.a
  set t₀H : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
  set Y : ∀ j, Equiv.Perm (C.D.Ψc j) :=
    Function.update (fun j => C.D.ρ j t₀H) C.i y with hY
  have hYrange : ∀ j, Y j ∈ (C.D.ρ j).range := fun j => by
    rcases eq_or_ne j C.i with rfl | hj
    · rw [hY, Function.update_self,
        C.D.range_rho_of_not_isOuterFactor (C.isNaturalSE _).not_isOuterFactor]
      exact hyM
    · rw [hY, Function.update_of_ne hj]
      exact ⟨t₀H, rfl⟩
  have hYJ : ∀ j, Y j ∈ longInvAt (Equiv.Perm (C.D.Ψc j)) (C.D.Ψc j)
      (C.D.coord (C.lpt ψ₀) j) := fun j => by
    rcases eq_or_ne j C.i with rfl | hj
    · rw [hY, Function.update_self, coord_lpt_self]
      exact hy
    · rw [hY, Function.update_of_ne hj, coord_lpt_of_ne _ _ hj]
      exact C.D.rho_mem_longInvAt ht₀ j
  obtain ⟨π, hπ, hρπ⟩ := C.D.exists_mem_longInvAt_rho_eq (C.lpt ψ₀) Y hYrange hYJ
  obtain ⟨s, hs, hsv, hsπ⟩ := (hS.mem_longInvAt_centralizerImage_iff C.isPGroup_zpowers
    (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) (π : typeLSection G Ω v)).mp hπ
  refine ⟨s, hs, hsv, fun ψ => ?_⟩
  have hfix : ∀ j, j ≠ C.i → C.D.ρ j π (C.D.coord C.a j) = C.D.coord C.a j := fun j hj => by
    rw [hρπ, hY, Function.update_of_ne hj]
    exact (C.D.rho_mem_longInvAt ht₀ j).2
  have h1 := C.smul_lpt hfix ψ
  rw [hρπ, hY, Function.update_self] at h1
  rw [← hsπ, ← h1]
  rfl

end Lift

section Transitive

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} (C : P49Config G Ω α v)

theorem holtDelta_eq_image (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) :
    holtDelta G Ω α C.β = (fun ψ => (C.lpt ψ : Ω)) ''
      holtDelta (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i) (C.D.coord C.b C.i) := by
  obtain ⟨D'⟩ := hS.holtData_twoPoint (C.three_le_card_holtDelta hS)
  have hι : IsEmpty D'.ι := D'.isEmpty_ι_iff.mpr hT
  ext δ
  constructor
  · intro hδ
    have hδF : δ ∈ fixSet Ω (Subgroup.zpowers v) :=
      (C.mem_fixSet_iff_rho hS D' ⟨δ, hδ⟩).mpr fun j => isEmptyElim j
    obtain ⟨hline, hM⟩ := (C.mem_holtDelta_iff hS ⟨δ, hδF⟩).mp hδ
    exact ⟨_, hM, by simp only [C.lpt_eq_of_coord hline]⟩
  · rintro ⟨ψ, hψ, rfl⟩
    exact (C.mem_holtDelta_iff hS (C.lpt ψ)).mpr
      ⟨fun j hj => C.coord_lpt_of_ne ψ hj, by rw [coord_lpt_self]; exact hψ⟩

theorem holtDelta'_subset_line (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) :
    holtDelta' G Ω α C.β ⊆ C.line := by
  obtain ⟨n, k, e, hA⟩ := (C.isNaturalSE C.i).exists_isBenderAction
  have hab : C.D.coord C.a C.i ≠ C.D.coord C.b C.i := C.coord_ne
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  have hβb : (C.lpt (C.D.coord C.b C.i) : Ω) = C.β := by rw [C.lpt_coord_b]
  have hlift : ∀ y ∈ longInvAt (C.D.M C.i) (C.D.Ψc C.i) (C.D.coord C.a C.i),
      ∃ s ∈ longInvAt G Ω α, C.LineActs s (y : Equiv.Perm (C.D.Ψc C.i)) := by
    intro y hy
    obtain ⟨s, hs, -, hsy⟩ := C.exists_lineActs_longInvAt hS y.2
      (mem_longInvAt_subgroup_iff.mp hy)
    exact ⟨s, hαa ▸ hs, hsy⟩
  have hsub : (fun ψ => (C.lpt ψ : Ω)) '' holtDelta' (C.D.M C.i) (C.D.Ψc C.i)
      (C.D.coord C.a C.i) (C.D.coord C.b C.i) ⊆ holtDelta' G Ω α C.β := by
    rintro _ ⟨γ, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨s, hs, hsy⟩ := hlift y hy
    exact ⟨s, hs, by rw [← hβb, hsy]; rfl⟩
  obtain ⟨y, hy, m, hmb, hmy, hma⟩ := hA.exists_triple hab
  obtain ⟨s₀, hs₀, hs₀y⟩ := hlift y hy
  obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem m.2
  set γ := (C.lpt ((y : Equiv.Perm (C.D.Ψc C.i)) (C.D.coord C.b C.i)) : Ω) with hγdef
  set γ' := (C.lpt ((m : Equiv.Perm (C.D.Ψc C.i)) (C.D.coord C.a C.i)) : Ω) with hγ'def
  have hs₀β : s₀ • C.β = γ := by rw [← hβb, hs₀y]
  have hγ : γ ∈ holtDelta' G Ω α C.β := ⟨s₀, hs₀, hs₀β⟩
  have hγ' : γ' ∈ holtDelta G Ω α C.β := by
    rw [C.holtDelta_eq_image hS hT]
    exact ⟨_, hma, rfl⟩
  have hcβ : c • C.β = α := by
    rw [← hβb, hcm]
    exact (congrArg (fun ψ => (C.lpt ψ : Ω)) hmb).trans hαa
  have hcγ : c • γ = C.β := by
    rw [hγdef, hcm]
    exact (congrArg (fun ψ => (C.lpt ψ : Ω)) hmy).trans hβb
  have hcα : c • α = γ' := by
    have h := hcm (C.D.coord C.a C.i)
    rw [hαa] at h
    exact h
  have hcβ' : c⁻¹ • α = C.β := by rw [inv_smul_eq_iff, hcβ]
  have hcγ' : c⁻¹ • C.β = γ := by rw [inv_smul_eq_iff, hcγ]
  have hcα' : c⁻¹ • γ' = α := by rw [inv_smul_eq_iff, hcα]
  have hn : Nat.card {s : longInvAt G Ω α // (s : G) • C.β = γ} =
      Nat.card {t : longInvSwap G Ω α C.β // (t : G) • γ' = γ'} := by
    refine Nat.card_congr
      { toFun := fun s => ⟨⟨c * s.1 * c⁻¹, conj_mem_longInv s.1.2.1 c, ?_⟩, ?_⟩
        invFun := fun t => ⟨⟨c⁻¹ * t.1 * c,
          ⟨by simpa using conj_mem_longInv t.1.2.1 c⁻¹, ?_⟩⟩, ?_⟩
        left_inv := fun s => Subtype.ext (Subtype.ext (by simp [mul_assoc]))
        right_inv := fun t => Subtype.ext (Subtype.ext (by simp [mul_assoc])) }
    · show (c * s.1 * c⁻¹) • α = C.β
      rw [mul_smul, mul_smul, hcβ', s.2, hcγ]
    · show (c * s.1 * c⁻¹) • γ' = γ'
      rw [mul_smul, mul_smul, hcα', s.1.2.2, hcα]
    · show (c⁻¹ * t.1 * c) • α = α
      rw [mul_smul, mul_smul, hcα, t.2, hcα']
    · show (c⁻¹ * t.1 * c) • C.β = γ
      rw [mul_smul, mul_smul, hcβ, t.1.2.2, hcγ']
  have h1 := card_longInvAt_eq_mul (hS.holtDelta'_eq_orbit C.ne hγ)
  have h2 := card_longInvSwap_eq_mul hγ'
  have h3 : Nat.card (longInvSwap G Ω α C.β) = Nat.card (longInvAt G Ω α) := by
    have := hS.card_longInvSwap_typeL C.isTypeL.orderOf_eq_two C.D C.jOddCore_eq_bot
      (i := C.i) (a := C.a) (b := C.b) fun j hj => (C.coord_eq j hj).symm
    rwa [C.coe_a] at this
  have hpos : 0 < Nat.card {s : longInvAt G Ω α // (s : G) • C.β = γ} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨⟨s₀, hs₀⟩, hs₀β⟩⟩, inferInstance⟩
  have hcard : Nat.card (holtDelta' G Ω α C.β) = Nat.card (holtDelta G Ω α C.β) := by
    rw [h3, h1, hn] at h2
    exact Nat.eq_of_mul_eq_mul_left (hn ▸ hpos) h2
  have himg : (fun ψ => (C.lpt ψ : Ω)) '' holtDelta' (C.D.M C.i) (C.D.Ψc C.i)
      (C.D.coord C.a C.i) (C.D.coord C.b C.i) = holtDelta' G Ω α C.β := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [Set.ncard_image_of_injective _ C.lpt_coe_injective, hA.ncard_holtDelta' hab,
      ← Nat.card_coe_set_eq, hcard, Nat.card_coe_set_eq, C.holtDelta_eq_image hS hT,
      Set.ncard_image_of_injective _ C.lpt_coe_injective, hA.ncard_holtDelta hab]
  rw [← himg]
  rintro _ ⟨ψ, -, rfl⟩
  exact C.lpt_mem_line ψ

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_M_fix_apply_eq {ψ₀ ψ ψ' : C.D.Ψc C.i} (hψ : ψ ≠ ψ₀) (hψ' : ψ' ≠ ψ₀) :
    ∃ m ∈ C.D.M C.i, m ψ = ψ' ∧ m ψ₀ = ψ₀ := by
  obtain ⟨n, k, e, hA⟩ := (C.isNaturalSE C.i).exists_isBenderAction
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer ψ₀
  obtain ⟨p, hp, hpψ⟩ := hA.exists_mem_smul_eq hQ hψ hψ'
  exact ⟨p, p.2, hpψ, hQ hp⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_M_apply_eq' (ψ ψ' : C.D.Ψc C.i) : ∃ m ∈ C.D.M C.i, m ψ = ψ' := by
  obtain ⟨n, k, e, hA⟩ := (C.isNaturalSE C.i).exists_isBenderAction
  have := hA.isPretransitive
  obtain ⟨m, hm⟩ := exists_smul_eq (C.D.M C.i) ψ ψ'
  exact ⟨m, m.2, hm⟩

theorem smul_mem_line_of_mem_longInvAt (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) {s : G} (hs : s ∈ longInvAt G Ω α) {ω : Ω} (hω : ω ∈ C.line) :
    s • ω ∈ C.line := by
  obtain ⟨ψ, rfl⟩ := hω
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  have hβb : (C.lpt (C.D.coord C.b C.i) : Ω) = C.β := by rw [C.lpt_coord_b]
  rcases eq_or_ne ψ (C.D.coord C.a C.i) with rfl | hψ
  · simp only [hαa, hs.2]
    exact C.α_mem_line
  obtain ⟨m, hm, hmb, hma⟩ := C.exists_mem_M_fix_apply_eq (Ne.symm C.coord_ne) hψ
  obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem hm
  have hcα : c • α = α := by rw [hcm.smul_α, hma, hαa]
  have hcβ : c • C.β = C.lpt ψ := by rw [hcm.smul_β, hmb]
  have hs' : c⁻¹ * s * c ∈ longInvAt G Ω α := by
    have := conj_mem_longInvAt hs c⁻¹
    rwa [inv_inv, inv_smul_eq_iff.mpr hcα.symm] at this
  have h1 : (c⁻¹ * s * c) • C.β ∈ C.line := C.holtDelta'_subset_line hS hT ⟨_, hs', rfl⟩
  have h2 := hcm.smul_mem h1
  have e : c • (c⁻¹ * s * c) • C.β = s • (C.lpt ψ : Ω) := by
    rw [← hcβ, smul_smul, smul_smul]
    congr 1
    group
  rwa [e] at h2

theorem isJClosed_line (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) : IsJClosed G Ω C.line := by
  have hαa : (C.lpt (C.D.coord C.a C.i) : Ω) = α := by rw [C.lpt_coord_a, C.coe_a]
  have hmap : ∀ x ∈ C.line, ∀ s ∈ longInvAt G Ω x, ∀ ω ∈ C.line, s • ω ∈ C.line := by
    rintro _ ⟨ψ₀, rfl⟩ s hs ω hω
    obtain ⟨m, hm, hma⟩ := C.exists_mem_M_apply_eq' (C.D.coord C.a C.i) ψ₀
    obtain ⟨c, -, hcm⟩ := C.exists_lineActs_of_mem hm
    have hcα : c • α = C.lpt ψ₀ := by rw [hcm.smul_α, hma]
    have hs' : c⁻¹ * s * c ∈ longInvAt G Ω α := by
      have := conj_mem_longInvAt hs c⁻¹
      rwa [inv_inv, inv_smul_eq_iff.mpr hcα.symm] at this
    have h1 := hcm.smul_mem (C.smul_mem_line_of_mem_longInvAt hS hT hs' (hcm.inv.smul_mem hω))
    have e : c • (c⁻¹ * s * c) • c⁻¹ • ω = s • ω := by
      rw [smul_smul, smul_smul]
      congr 1
      group
    rwa [e] at h1
  intro x hx s hs
  refine Set.Subset.antisymm ?_ fun ω hω => ?_
  · rintro _ ⟨ω, hω, rfl⟩
    exact hmap x hx s hs ω hω
  · refine ⟨s • ω, hmap x hx s hs ω hω, ?_⟩
    show s • s • ω = ω
    rw [smul_smul, mul_self_eq_one_of_mem_longInv hs.1, one_smul]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem three_le_card_line : 3 ≤ Nat.card C.line := by
  have h5 := (C.isNaturalSE C.i).odd_card_and_five_le.2
  have e : Nat.card C.line = Nat.card (C.D.Ψc C.i) :=
    Nat.card_range_of_injective C.lpt_coe_injective
  omega

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem zpowers_le_fixingSubgroup_line :
    Subgroup.zpowers v ≤ fixingSubgroup G C.line := fun g hg =>
  (mem_fixingSubgroup_iff G).mpr fun _ hω => C.line_subset_fixSet hω g hg

theorem exists_lineActs_of_mem_longInvAt (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) {ψ₀ : C.D.Ψc C.i} {s : G} (hs : s ∈ longInvAt G Ω (C.lpt ψ₀ : Ω)) :
    ∃ y ∈ C.D.M C.i, y ∈ longInvAt (Equiv.Perm (C.D.Ψc C.i)) (C.D.Ψc C.i) ψ₀ ∧
      C.LineActs s y := by
  have hsL := C.isJClosed_line hS hT _ (C.lpt_mem_line ψ₀) s hs
  obtain ⟨c, hcJ, hcV, hcs⟩ := hS.frattini C.three_le_card_line C.isPGroup_zpowers
    C.zpowers_le_fixingSubgroup_line hs.1 (mem_stabilizer_iff.mpr hsL)
  have hπJ : centralizerImageElt (Ω := Ω) hcV ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff C.isPGroup_zpowers
      (three_le_card_fixSet_of_isTypeL hS.star C.isTypeL) _).mpr ⟨c, hcJ, hcV, fun _ => rfl⟩
  set πH : jHull (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    ⟨_, mem_jHull_of_mem_longInv hπJ⟩
  have hcα : c • α ∈ C.line := by
    rw [hcs α C.α_mem_line]
    exact hsL ▸ Set.smul_mem_smul_set C.α_mem_line
  obtain ⟨ψ', hψ'⟩ := hcα
  simp only at hψ'
  have hfix : ∀ j, j ≠ C.i → C.D.ρ j πH (C.D.coord C.a j) = C.D.coord C.a j := fun j hj => by
    rw [← C.D.coord_smul]
    have e : ((πH : typeLSection G Ω v) • C.a) = C.lpt ψ' := Subtype.ext (by
      rw [hψ']
      show c • (C.a : Ω) = c • α
      rw [C.coe_a])
    rw [e, coord_lpt_of_ne _ _ hj]
  have hact : C.LineActs s (C.D.ρ C.i πH) := fun ψ => by
    rw [← hcs _ (C.lpt_mem_line ψ), ← C.smul_lpt hfix ψ]
    rfl
  refine ⟨_, C.D.rho_mem_M_of_isNaturalSE (C.isNaturalSE C.i) πH,
    ⟨C.D.rho_mem_longInv hπJ C.i, ?_⟩, hact⟩
  refine C.lpt_injective (Subtype.ext ?_)
  show (C.lpt ((C.D.ρ C.i πH) ψ₀) : Ω) = C.lpt ψ₀
  rw [← hact ψ₀]
  exact hs.2

theorem exists_lineActs_closure (hS : Sec4Setting G Ω)
    (hT : IsPretransitive (jOddCore (twoPointSection G Ω α C.β) (holtDelta G Ω α C.β))
      (holtDelta G Ω α C.β)) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVL : V ≤ fixingSubgroup G C.line) {m : Equiv.Perm (C.D.Ψc C.i)} (hm : m ∈ C.D.M C.i) :
    ∃ g ∈ Subgroup.closure {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (V : Set G) ∧
      c • C.line = C.line}, C.LineActs g m := by
  set T : Set G := {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (V : Set G) ∧
      c • C.line = C.line}
  have hgen : ∀ y ∈ {y | y ∈ C.D.M C.i ∧ y ∈ longInv (Equiv.Perm (C.D.Ψc C.i)) (C.D.Ψc C.i)},
      ∃ g ∈ Subgroup.closure T, C.LineActs g y := by
    rintro y ⟨hyM, hyJ⟩
    obtain ⟨ψ₀, hψ₀, -⟩ := hyJ.2
    obtain ⟨s, hs, -, hsy⟩ := C.exists_lineActs_longInvAt hS hyM ⟨hyJ, hψ₀⟩
    have hsL := C.isJClosed_line hS hT _ (C.lpt_mem_line ψ₀) s hs
    obtain ⟨c, hcJ, hcV, hcs⟩ := hS.frattini C.three_le_card_line hV hVL hs.1
      (mem_stabilizer_iff.mpr hsL)
    have hcy : C.LineActs c y := fun ψ => by rw [hcs _ (C.lpt_mem_line ψ), hsy]
    exact ⟨c, Subgroup.subset_closure ⟨hcJ, hcV, hcy.smul_line⟩, hcy⟩
  have key := (C.isNaturalSE C.i).le_closure_longInv hm
  clear hm
  induction key using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => exact ⟨1, Subgroup.one_mem _, C.lineActs_one⟩
  | mul y y' _ _ hy hy' =>
    obtain ⟨g, hg, hgy⟩ := hy
    obtain ⟨g', hg', hgy'⟩ := hy'
    exact ⟨g * g', Subgroup.mul_mem _ hg hg', hgy.mul hgy'⟩
  | inv y _ hy =>
    obtain ⟨g, hg, hgy⟩ := hy
    exact ⟨g⁻¹, Subgroup.inv_mem _ hg, hgy.inv⟩

end Transitive

end P49Config

end CFSG.Holt.H78
