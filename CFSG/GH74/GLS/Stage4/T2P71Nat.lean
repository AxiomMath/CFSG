module

public import CFSG.GH74.GLS.Stage4.T6Sec

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2

theorem nat_rep' {H : Type} [Group H] {p m : ℕ} (hp : p.Prime) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ m) (e : H ≃* SL2 F) :
    ∃ (_ : Module (ZMod p) (Fin 2 → F)) (_ : Module.Finite (ZMod p) (Fin 2 → F))
      (ρ' : Representation (ZMod p) H (Fin 2 → F)),
      (∀ h v, ρ' h v = (e h : Matrix (Fin 2) (Fin 2) F).mulVec v) ∧
      Function.Injective ρ' ∧ Module.finrank (ZMod p) (Fin 2 → F) = 2 * m := by
  have hpF : (p : F) = 0 := t6_cast_p hF
  have hp0 : ∀ v : Fin 2 → F, p • v = 0 := fun v => by
    ext i
    simp [hpF]
  have hmod : Module (ZMod p) (Fin 2 → F) := AddCommGroup.zmodModule hp0
  let f : H → Module.End (ZMod p) (Fin 2 → F) := fun h =>
    AddMonoidHom.toZModLinearMap p
      (Matrix.mulVecLin (e h : Matrix (Fin 2) (Fin 2) F)).toAddMonoidHom
  have hf : ∀ h v, f h v = (e h : Matrix (Fin 2) (Fin 2) F).mulVec v := fun h v => rfl
  have f1 : f 1 = 1 := by
    ext v : 1
    rw [hf]
    simp
  have f2 : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    ext v : 1
    rw [Module.End.mul_apply, hf, hf, hf, map_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec]
  let ρ' : Representation (ZMod p) H (Fin 2 → F) := MonoidHom.mk ⟨f, f1⟩ f2
  have hρ' : ∀ h v, ρ' h v = (e h : Matrix (Fin 2) (Fin 2) F).mulVec v := fun h v => rfl
  refine ⟨hmod, inferInstance, ρ', hρ', ?_, ?_⟩
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← hρ', ← hρ', hab]
  · have : Fact p.Prime := ⟨hp⟩
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Fin 2 → F)
    rw [Nat.card_zmod, Nat.card_fun, hF, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
      ← pow_mul] at h
    have h' := Nat.pow_right_injective hp.two_le h
    omega

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem exists_natCoord (h11b : IVK_11_1b_nat) (h : T6Ctx N u p) {m : ℕ} (hm : N.q₁ = p ^ m)
    (hcard : N.X₂.relIndex (R₂ N p) = p ^ (2 * m)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL2 F →* G) (c : G → (Fin 2 → F)),
      Nat.card F = p ^ m ∧ Function.Injective φ ∧ φ.range = N.K₁ ∧ φ (negOne F) = N.z ∧
      N.X₁ = (uSub F).map φ ∧ N.X₁' = (lSub F).map φ ∧ N.w₁ = φ (sl2W F) ∧
      N.H ⊓ N.K₁ = (tSub F).map φ ∧
      (∀ a ∈ R₂ N p, ∀ a' ∈ R₂ N p, c (a * a') = c a + c a') ∧
      (∀ a ∈ R₂ N p, c a = 0 ↔ a ∈ N.X₂) ∧
      (∀ v : Fin 2 → F, ∃ a ∈ R₂ N p, c a = v) ∧
      ∀ (g : SL2 F), ∀ a ∈ R₂ N p, c (φ g * a * (φ g)⁻¹) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (c a) := by
  classical
  have hp := h.prime
  have hp2 := h.p_ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, iF, fF, φ, hcardF, hinj, hrange, hz, hX, hX', hw, hHK⟩ := h.coord.coord₁
  have hF : Nat.card F = p ^ m := hcardF.trans hm
  have hzK : N.z ∈ N.K₁ := h.sec5.loc.z_mem_K₁
  have hmemφ : ∀ g : SL2 F, φ g ∈ N.K₁ := fun g => hrange ▸ ⟨g, rfl⟩
  let e : ↥N.K₁ ≃* SL2 F :=
    (MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm
  have heφ : ∀ g : SL2 F, e ⟨φ g, hmemφ g⟩ = g := by
    intro g
    show (MonoidHom.ofInjective hinj).symm (MulEquiv.subgroupCongr hrange.symm ⟨φ g, hmemφ g⟩) = g
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rfl
  have hez : e ⟨N.z, hzK⟩ = negOne F := by
    have := heφ (negOne F)
    rw [← this]
    congr 1
    apply Subtype.ext
    exact hz.symm
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card F = 1 := by simpa using hF
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨hKR, hKX⟩ := K₁_sec_X₂R₂ h
  have hXR := X₂_le_R₂ h
  have hcomm := (R₂_inv_comm h).2
  have hinv := (R₂_inv_comm h).1
  have hexp := R₂_exp h
  obtain ⟨V, _, _, _, ρ, π, hcard', hπ0, hπadd, hρπ⟩ :=
    t6_sec_rep (p := p) hKR hKX (fun a ha a' ha' => hcomm a ha a' ha') hexp
  have hne : N.X₂ ≠ R₂ N p := by
    intro heq
    have h1 : N.X₂.relIndex (R₂ N p) = 1 := by
      rw [heq]
      exact Subgroup.relIndex_self _
    rw [hcard] at h1
    have h2 : 1 < p ^ (2 * m) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hinjρ := t6_sec_faithful hp hp2 hodd e hzK hez hXR hKR hinv hne ρ π hπ0 hπadd hρπ
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Module.Finite (ZMod p) V := inferInstance
  have hfr : Module.finrank (ZMod p) V = 2 * m := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod, hcard', hcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  obtain ⟨_, _, ρ', hρ'e, hinj', hfr'⟩ := nat_rep' hp hF e
  have hSL : HasSL2Model ↥(⊤ : Subgroup ↥N.K₁) (fun r => r = p ^ m) :=
    ⟨F, inferInstance, inferInstance, hF,
      ⟨Subgroup.topEquiv.trans (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))⟩⟩
  obtain ⟨-, -, huniq⟩ := h11b p m hp hp2 ↥N.K₁ ⊤ hSL V ρ hinjρ hfr
  obtain ⟨φ'⟩ := huniq (Fin 2 → F) ρ' hinj' hfr'
  obtain ⟨ψ, hψ⟩ := t6_iso_equivariant ρ ρ' φ'
  let c : G → (Fin 2 → F) := fun a => if ha : a ∈ R₂ N p then ψ (π ⟨a, ha⟩) else 0
  have hc : ∀ a (ha : a ∈ R₂ N p), c a = ψ (π ⟨a, ha⟩) := fun a ha => by simp [c, ha]
  refine ⟨F, iF, fF, φ, c, hF, hinj, hrange, hz, hX, hX', hw, hHK, ?_, ?_, ?_, ?_⟩
  · intro a ha a' ha'
    rw [hc a ha, hc a' ha', hc (a * a') ((R₂ N p).mul_mem ha ha')]
    have := hπadd ⟨a, ha⟩ ⟨a', ha'⟩
    rw [show (⟨a * a', (R₂ N p).mul_mem ha ha'⟩ : ↥(R₂ N p)) = ⟨a, ha⟩ * ⟨a', ha'⟩ from rfl, this,
      map_add]
  · intro a ha
    rw [hc a ha, map_eq_zero_iff ψ ψ.injective, hπ0]
  ·
    intro v
    let A := R₂ N p
    let j : (↥A ⧸ N.X₂.subgroupOf A) → V := Quotient.lift (fun a : ↥A => π a) (by
      intro a b hab
      have h1 : ((a⁻¹ * b : ↥A) : G) ∈ N.X₂ := by
        have : a⁻¹ * b ∈ N.X₂.subgroupOf A := (QuotientGroup.leftRel_apply).1 hab
        exact this
      have h2 := hπadd a (a⁻¹ * b)
      rw [mul_inv_cancel_left] at h2
      have h3 : π (a⁻¹ * b) = 0 := (hπ0 _).2 h1
      rw [h2, h3, add_zero])
    have hjinj : Function.Injective j := by
      intro x y hxy
      induction x using QuotientGroup.induction_on with | H a => ?_
      induction y using QuotientGroup.induction_on with | H b => ?_
      have hxy' : π a = π b := hxy
      apply QuotientGroup.eq.2
      have h2 := hπadd (a⁻¹) b
      have h4 : π (a⁻¹) + π a = 0 := by
        rw [← hπadd, inv_mul_cancel]
        have h0 := hπadd (1 : ↥A) 1
        rw [mul_one] at h0
        exact left_eq_add.1 h0
      have h5 : π (a⁻¹ * b) = π a⁻¹ + π b := h2
      have : π (a⁻¹ * b) = 0 := by
        rw [h5, ← hxy']
        exact h4
      exact (hπ0 _).1 this
    have hcardeq : Nat.card (↥A ⧸ N.X₂.subgroupOf A) = Nat.card V := by
      rw [hcard', ← Subgroup.index_eq_card]
      rfl
    have hsurj : Function.Surjective j :=
      (Function.Injective.bijective_of_nat_card_le hjinj (le_of_eq hcardeq.symm)).2
    obtain ⟨x, hx⟩ := hsurj (ψ.symm v)
    induction x using QuotientGroup.induction_on with | H a => ?_
    refine ⟨a, a.2, ?_⟩
    rw [hc a a.2]
    have : π a = ψ.symm v := hx
    rw [this]
    simp
  · intro g a ha
    have hk : φ g ∈ N.K₁ := hmemφ g
    have hconj : φ g * a * (φ g)⁻¹ ∈ R₂ N p := R₂_norm N p (K₁_le_M₂ h hk) ha
    rw [hc _ hconj, hc a ha]
    have e1 : π ⟨φ g * a * (φ g)⁻¹, hconj⟩ = ρ ⟨φ g, hk⟩ (π ⟨a, ha⟩) :=
      (hρπ ⟨φ g, hk⟩ ⟨a, ha⟩).symm
    rw [e1, hψ, hρ'e, heφ]

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
