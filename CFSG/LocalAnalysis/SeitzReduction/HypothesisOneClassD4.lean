module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassD4Torus
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneOddDerivation

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint RootOps

universe u

theorem d4_conj_identity {G : Type*} [Group G]
    {xa xb xd xac xbc xcd xabc xacd xbcd xabcd xθ : G}
    (h1 : xbcd * xa * xbcd⁻¹ = xabcd * xa) (h2 : Commute xbcd xb) (h3 : Commute xbcd xd)
    (h4 : Commute xbcd xθ) (h5 : Commute xac xabcd) (h6 : Commute xac xa)
    (h7 : xac * xb * xac⁻¹ = xabc * xb) (h8 : xac * xd * xac⁻¹ = xacd * xd) (h9 : Commute xac xθ)
    (h10 : Commute xbc xabcd) (h11 : xbc * xa * xbc⁻¹ = xabc * xa) (h12 : Commute xbc xabc)
    (h13 : Commute xbc xb) (h14 : xbc * xacd * xbc⁻¹ = xθ * xacd)
    (h15 : xbc * xd * xbc⁻¹ = xbcd * xd) (h16 : Commute xbc xθ) (h17 : Commute xcd xabcd)
    (h18 : xcd * xa * xcd⁻¹ = xacd * xa) (h19 : xcd * xb * xcd⁻¹ = xbcd * xb)
    (h20 : Commute xcd xacd) (h21 : Commute xcd xbcd) (h22 : Commute xcd xd)
    (h23 : Commute xa xabc) (h24 : Commute xa xacd) (h25 : Commute xθ xacd)
    (h26 : Commute xθ xbcd) (h27 : Commute xθ xd) (h28 : xb * xacd * xb⁻¹ = xabcd * xacd)
    (h29 : Commute xabcd xa) (h30 : Commute xabcd xacd) (h31 : Commute xabcd xbcd)
    (h32 : Commute xacd xbcd) (i1 : xabc * xabc = 1) (i2 : xθ * xθ = 1) (i3 : xabcd * xabcd = 1)
    (i4 : xacd * xacd = 1) (i5 : xbcd * xbcd = 1) :
    (xcd * xbc * xac * xbcd) * (xa * xb * xd * xθ) * (xcd * xbc * xac * xbcd)⁻¹ =
      xa * xb * xd := by
  have sq : ∀ {x : G}, x * x = 1 → ∀ w, x * (x * w) = w := fun hx w => by
    rw [← mul_assoc, hx, one_mul]
  have e1 : xbcd * (xa * xb * xd * xθ) * xbcd⁻¹ = xabcd * xa * xb * xd * xθ := by
    rw [← MulAut.conj_apply]
    simp only [map_mul, MulAut.conj_apply, h1, h2.mul_inv_cancel, h3.mul_inv_cancel,
      h4.mul_inv_cancel]
  have e2 : xac * (xabcd * xa * xb * xd * xθ) * xac⁻¹ =
      xabcd * xa * (xabc * xb) * (xacd * xd) * xθ := by
    rw [← MulAut.conj_apply]
    simp only [map_mul, MulAut.conj_apply, h5.mul_inv_cancel, h6.mul_inv_cancel, h7, h8,
      h9.mul_inv_cancel]
  have e3 : xbc * (xabcd * xa * (xabc * xb) * (xacd * xd) * xθ) * xbc⁻¹ =
      xabcd * xa * xb * xacd * xbcd * xd := by
    rw [← MulAut.conj_apply]
    simp only [map_mul, MulAut.conj_apply, h10.mul_inv_cancel, h11, h12.mul_inv_cancel,
      h13.mul_inv_cancel, h14, h15, h16.mul_inv_cancel]
    simp only [mul_assoc]
    rw [← h23.left_comm, sq i1, h25.left_comm, h26.left_comm, h27.left_comm, i2, mul_one]
  have e4 : xcd * (xabcd * xa * xb * xacd * xbcd * xd) * xcd⁻¹ = xa * xb * xd := by
    rw [← MulAut.conj_apply]
    simp only [map_mul, MulAut.conj_apply, h17.mul_inv_cancel, h18, h19, h20.mul_inv_cancel,
      h21.mul_inv_cancel, h22.mul_inv_cancel]
    have j : ∀ w, xb * (xacd * w) = xabcd * (xacd * (xb * w)) := fun w => by
      rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← h28]
      group
    simp only [mul_assoc]
    rw [← h24.left_comm, j, ← h31.left_comm, ← h30.left_comm, ← h29.left_comm, sq i3,
      ← h32.left_comm, sq i4, h2.left_comm, sq i5]
  calc (xcd * xbc * xac * xbcd) * (xa * xb * xd * xθ) * (xcd * xbc * xac * xbcd)⁻¹ =
        xcd * (xbc * (xac * (xbcd * (xa * xb * xd * xθ) * xbcd⁻¹) * xac⁻¹) * xbc⁻¹) *
          xcd⁻¹ := by group
    _ = xa * xb * xd := by rw [e1, e2, e3, e4]

variable {τ : Tag}

theorem classD4_noG2 (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : NoG2 τ := fun i =>
  Or.inl (by rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer])

theorem classD4_iform_self
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]
  rcases hτ with rfl | rfl | rfl | rfl <;> simp [Tag.symmetrizer]

theorem classD4_isRoot_add
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : iform γ δ = -1) :
    IsRoot τ (γ + δ) ∧ γ ≠ δ ∧ γ ≠ -δ := by
  have hne : γ ≠ δ := fun e => by
    rw [e, classD4_iform_self hτ hδ] at h
    omega
  have hne' : γ ≠ -δ := fun e => by
    rw [e, ← neg_one_smul ℤ δ, iform_smul_left, classD4_iform_self hτ hδ] at h
    omega
  exact ⟨isRoot_add_of_iform_neg hγ hδ hne' (by omega), hne, hne'⟩

theorem classD4_not_isRoot_add
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : 0 ≤ iform γ δ) :
    ¬IsRoot τ (γ + δ) ∧ γ ≠ -δ := by
  refine ⟨fun hr => ?_, fun e => ?_⟩
  · have h' := classD4_iform_self hτ hr
    rw [iform_add_left, iform_add_right, iform_add_right, classD4_iform_self hτ hγ,
      classD4_iform_self hτ hδ, iform_comm δ γ] at h'
    omega
  · rw [e, ← neg_one_smul ℤ δ, iform_smul_left, classD4_iform_self hτ hδ] at h
    omega

theorem classD4_pinnedX_mul_self
    {R : Type u} [CommRing R] (h2 : (2 : R) = 0) (γ : Fin τ.rank → ℤ) :
    pinnedX τ R γ 1 * pinnedX τ R γ 1 = 1 := by
  rw [← pinnedX_add, one_add_one_eq_two, h2, pinnedX_zero]

@[expose] def IsD4Pattern (τ : Tag) (a b c d : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ a ∧ IsRoot τ b ∧ IsRoot τ c ∧ IsRoot τ d ∧ iform a c = -1 ∧ iform b c = -1 ∧
    iform d c = -1 ∧ iform a b = 0 ∧ iform a d = 0 ∧ iform b d = 0

@[expose] def isD4PatternB (τ : Tag) (a b c d : Fin τ.rank → ℤ) : Bool :=
  isRootB τ a && isRootB τ b && isRootB τ c && isRootB τ d && decide (iform a c = -1) &&
    decide (iform b c = -1) && decide (iform d c = -1) && decide (iform a b = 0) &&
    decide (iform a d = 0) && decide (iform b d = 0)

theorem isD4Pattern_of_isD4PatternB
    {a b c d : Fin τ.rank → ℤ} (h : isD4PatternB τ a b c d = true) : IsD4Pattern τ a b c d := by
  simp only [isD4PatternB, Bool.and_eq_true, decide_eq_true_eq, isRootB_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨ha, hb, hc, hd, h1, h2, h3, h4, h5, h6⟩

theorem IsD4Pattern.smul
    {a b c d : Fin τ.rank → ℤ} (h : IsD4Pattern τ a b c d) (w : WeylGroup τ) :
    IsD4Pattern τ (w • a) (w • b) (w • c) (w • d) := by
  obtain ⟨ha, hb, hc, hd, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨IsRoot.smul ha w, IsRoot.smul hb w, IsRoot.smul hc w, IsRoot.smul hd w,
    by rw [iform_smul]; exact h1, by rw [iform_smul]; exact h2, by rw [iform_smul]; exact h3,
    by rw [iform_smul]; exact h4, by rw [iform_smul]; exact h5, by rw [iform_smul]; exact h6⟩

theorem isD4Pattern_D4 :
    IsD4Pattern .D4 (![1, 0, 0, 0] : Fin 4 → ℤ) ![0, 1, 0, 0] ![0, 0, 1, 0] ![0, 0, 0, 1] :=
  isD4Pattern_of_isD4PatternB (by decide +kernel)

theorem isD4Pattern_E6 :
    IsD4Pattern .E6 (![0, 1, 0, 0, 0, 0] : Fin 6 → ℤ) ![0, 0, 1, 0, 0, 0] ![0, 0, 0, 1, 0, 0]
      ![0, 0, 0, 0, 1, 0] :=
  isD4Pattern_of_isD4PatternB (by decide +kernel)

theorem isD4Pattern_E7 :
    IsD4Pattern .E7 (![0, 1, 0, 0, 0, 0, 0] : Fin 7 → ℤ) ![0, 0, 1, 0, 0, 0, 0]
      ![0, 0, 0, 1, 0, 0, 0] ![0, 0, 0, 0, 1, 0, 0] :=
  isD4Pattern_of_isD4PatternB (by decide +kernel)

theorem isD4Pattern_E8 :
    IsD4Pattern .E8 (![0, 1, 0, 0, 0, 0, 0, 0] : Fin 8 → ℤ) ![0, 0, 1, 0, 0, 0, 0, 0]
      ![0, 0, 0, 1, 0, 0, 0, 0] ![0, 0, 0, 0, 1, 0, 0, 0] :=
  isD4Pattern_of_isD4PatternB (by decide +kernel)

theorem isD4Pattern_E6_cascade :
    IsD4Pattern .E6 (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ) ![0, 0, 1, 1, 1, 0] ![0, 1, 0, 0, 0, 0]
      ![0, 0, 0, 1, 0, 0] :=
  isD4Pattern_of_isD4PatternB (by decide +kernel)

theorem IsD4Pattern.isRoot_add
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c d : Fin τ.rank → ℤ}
    (hp : IsD4Pattern τ a b c d) :
    IsRoot τ (a + c) ∧ IsRoot τ (b + c) ∧ IsRoot τ (c + d) ∧ IsRoot τ (a + b + c) ∧
      IsRoot τ (a + c + d) ∧ IsRoot τ (b + c + d) ∧ IsRoot τ (a + b + c + d) ∧
      IsRoot τ (a + b + 2 • c + d) := by
  obtain ⟨ra, rb, rc, rd, hac, hbc, hdc, hab, had, hbd⟩ := hp
  have hcc := classD4_iform_self hτ rc
  have hcb : iform c b = -1 := by rw [iform_comm]; exact hbc
  have hcd : iform c d = -1 := by rw [iform_comm]; exact hdc
  have rac := (classD4_isRoot_add hτ ra rc hac).1
  have rbc := (classD4_isRoot_add hτ rb rc hbc).1
  have rcd := (classD4_isRoot_add hτ rc rd hcd).1
  have rabc : IsRoot τ (a + b + c) := by
    have := (classD4_isRoot_add hτ rac rb (by rw [iform_add_left, hab, hcb]; norm_num)).1
    rwa [show a + c + b = a + b + c by abel] at this
  have racd : IsRoot τ (a + c + d) :=
    (classD4_isRoot_add hτ rac rd (by rw [iform_add_left, had, hcd]; norm_num)).1
  have rbcd : IsRoot τ (b + c + d) :=
    (classD4_isRoot_add hτ rbc rd (by rw [iform_add_left, hbd, hcd]; norm_num)).1
  have rabcd : IsRoot τ (a + b + c + d) := (classD4_isRoot_add hτ rabc rd (by
    rw [iform_add_left, iform_add_left, had, hbd, hcd]; norm_num)).1
  refine ⟨rac, rbc, rcd, rabc, racd, rbcd, rabcd, ?_⟩
  have := (classD4_isRoot_add hτ rabcd rc (by
    rw [iform_add_left, iform_add_left, iform_add_left, hac, hbc, hcc, hdc]; norm_num)).1
  rwa [show a + b + c + d + c = a + b + 2 • c + d by abel] at this

theorem IsD4Pattern.iform_highest
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c d : Fin τ.rank → ℤ}
    (hp : IsD4Pattern τ a b c d) :
    iform a (a + b + 2 • c + d) = 0 ∧ iform b (a + b + 2 • c + d) = 0 ∧
      iform d (a + b + 2 • c + d) = 0 := by
  obtain ⟨ra, rb, -, rd, hac, hbc, hdc, hab, had, hbd⟩ := hp
  have hba : iform b a = 0 := by rw [iform_comm]; exact hab
  have hda : iform d a = 0 := by rw [iform_comm]; exact had
  have hdb : iform d b = 0 := by rw [iform_comm]; exact hbd
  simp only [iform_add_right, two_nsmul, classD4_iform_self hτ ra, classD4_iform_self hτ rb,
    classD4_iform_self hτ rd, hab, hac, had, hba, hbc, hbd, hda, hdb, hdc]
  norm_num

section Sound


theorem classD4_commute_pinnedX (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type u}
    [CommRing R] {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
    (h : 0 ≤ iform γ δ) (c e : R) : Commute (pinnedX τ R γ c) (pinnedX τ R δ e) := by
  obtain ⟨hn, hne'⟩ := classD4_not_isRoot_add hτ hγ hδ h
  exact commute_pinnedX_of_oddDeriv hγ hδ hne' hn c e

theorem classD4_conj_pinnedX (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type u}
    [CommRing R] (h2 : (2 : R) = 0) {γ δ ε : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : iform γ δ = -1) (hε : γ + δ = ε) :
    pinnedX τ R γ 1 * pinnedX τ R δ 1 * (pinnedX τ R γ 1)⁻¹ =
      pinnedX τ R ε 1 * pinnedX τ R δ 1 := by
  obtain ⟨hr, hne, hne'⟩ := classD4_isRoot_add hτ hγ hδ h
  have hc := commutatorElement_pinnedX_of_oddDerivLaced h2 (oddDerivLacedCheck_of_simplyLaced hτ)
    hγ hδ hne hne' hr (1 : R) 1
  rw [commutatorElement_def, mul_one, hε] at hc
  rw [← hc]
  group

theorem classD4_conj_eq (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type u} [CommRing R]
    (h2 : (2 : R) = 0) {a b c d : Fin τ.rank → ℤ} (hp : IsD4Pattern τ a b c d) :
    (pinnedX τ R (c + d) 1 * pinnedX τ R (b + c) 1 * pinnedX τ R (a + c) 1 *
          pinnedX τ R (b + c + d) 1) *
        (pinnedX τ R a 1 * pinnedX τ R b 1 * pinnedX τ R d 1 *
          pinnedX τ R (a + b + 2 • c + d) 1) *
        (pinnedX τ R (c + d) 1 * pinnedX τ R (b + c) 1 * pinnedX τ R (a + c) 1 *
          pinnedX τ R (b + c + d) 1)⁻¹ =
      pinnedX τ R a 1 * pinnedX τ R b 1 * pinnedX τ R d 1 := by
  obtain ⟨ra, rb, rc, rd, hac, hbc, hdc, hab, had, hbd⟩ := hp
  have haa := classD4_iform_self hτ ra
  have hbb := classD4_iform_self hτ rb
  have hcc := classD4_iform_self hτ rc
  have hdd := classD4_iform_self hτ rd
  have hca : iform c a = -1 := by rw [iform_comm]; exact hac
  have hcb : iform c b = -1 := by rw [iform_comm]; exact hbc
  have hcd : iform c d = -1 := by rw [iform_comm]; exact hdc
  have hba : iform b a = 0 := by rw [iform_comm]; exact hab
  have hda : iform d a = 0 := by rw [iform_comm]; exact had
  have hdb : iform d b = 0 := by rw [iform_comm]; exact hbd
  have F : iform (a + c) b = -1 ∧ iform (a + c) d = -1 ∧ iform (b + c) d = -1 ∧
      iform (b + c + d) a = -1 ∧ 0 ≤ iform (b + c + d) b ∧ 0 ≤ iform (b + c + d) d ∧
      0 ≤ iform (b + c + d) (a + b + 2 • c + d) ∧ 0 ≤ iform (a + c) (a + b + c + d) ∧
      0 ≤ iform (a + c) a ∧ 0 ≤ iform (a + c) (a + b + 2 • c + d) ∧
      0 ≤ iform (b + c) (a + b + c + d) ∧ iform (b + c) a = -1 ∧
      0 ≤ iform (b + c) (a + b + c) ∧ 0 ≤ iform (b + c) b ∧ iform (b + c) (a + c + d) = -1 ∧
      0 ≤ iform (b + c) (a + b + 2 • c + d) ∧ 0 ≤ iform (c + d) (a + b + c + d) ∧
      iform (c + d) a = -1 ∧ iform (c + d) b = -1 ∧ 0 ≤ iform (c + d) (a + c + d) ∧
      0 ≤ iform (c + d) (b + c + d) ∧ 0 ≤ iform (c + d) d ∧ 0 ≤ iform a (a + b + c) ∧
      0 ≤ iform a (a + c + d) ∧ 0 ≤ iform (a + b + 2 • c + d) (a + c + d) ∧
      0 ≤ iform (a + b + 2 • c + d) (b + c + d) ∧ 0 ≤ iform (a + b + 2 • c + d) d ∧
      iform b (a + c + d) = -1 ∧ 0 ≤ iform (a + b + c + d) a ∧
      0 ≤ iform (a + b + c + d) (a + c + d) ∧ 0 ≤ iform (a + b + c + d) (b + c + d) ∧
      0 ≤ iform (a + c + d) (b + c + d) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [iform_add_left, iform_add_right, two_nsmul, haa, hab, hac, had, hba,
      hbb, hbc, hbd, hca, hcb, hcc, hcd, hda, hdb, hdc, hdd]
    all_goals norm_num
  obtain ⟨g1, g2, g3, f1, f2, f3, f4, f5, f6, f9, f10, f11, f12, f13, f14, f16, f17,
    f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32⟩ := F
  obtain ⟨rac, rbc, rcd, rabc, racd, rbcd, rabcd, rθ⟩ :=
    IsD4Pattern.isRoot_add hτ ⟨ra, rb, rc, rd, hac, hbc, hdc, hab, had, hbd⟩
  have cj := fun {γ δ ε : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
      (h : iform γ δ = -1) (hε : γ + δ = ε) => classD4_conj_pinnedX (R := R) hτ h2 hγ hδ h hε
  have cm := fun {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hδ : IsRoot τ δ)
      (h : 0 ≤ iform γ δ) => classD4_commute_pinnedX (R := R) hτ hγ hδ h 1 1
  have sq := classD4_pinnedX_mul_self (τ := τ) h2
  exact d4_conj_identity (cj rbcd ra f1 (by abel)) (cm rbcd rb f2) (cm rbcd rd f3)
    (cm rbcd rθ f4) (cm rac rabcd f5) (cm rac ra f6) (cj rac rb g1 (by abel))
    (cj rac rd g2 (by abel)) (cm rac rθ f9) (cm rbc rabcd f10) (cj rbc ra f11 (by abel))
    (cm rbc rabc f12) (cm rbc rb f13) (cj rbc racd f14 (by abel)) (cj rbc rd g3 (by abel))
    (cm rbc rθ f16) (cm rcd rabcd f17) (cj rcd ra f18 (by abel)) (cj rcd rb f19 (by abel))
    (cm rcd racd f20) (cm rcd rbcd f21) (cm rcd rd f22) (cm ra rabc f23) (cm ra racd f24)
    (cm rθ racd f25) (cm rθ rbcd f26) (cm rθ rd f27) (cj rb racd f28 (by abel))
    (cm rabcd ra f29) (cm rabcd racd f30) (cm rabcd rbcd f31) (cm racd rbcd f32)
    (sq _) (sq _) (sq _) (sq _) (sq _)

theorem classD4_frame_prod_perm (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type u}
    [CommRing R] {F F' : List (Fin τ.rank → ℤ)} (hF : ∀ σ ∈ F, IsRoot τ σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (hperm : F.Perm F')
    (e : (Fin τ.rank → ℤ) → R) :
    (F.map fun σ => pinnedX τ R σ (e σ)).prod = (F'.map fun σ => pinnedX τ R σ (e σ)).prod :=
  (hperm.map _).prod_eq' (List.pairwise_map.2 (horth.imp_of_mem fun hσ hσ' h =>
    classD4_commute_pinnedX hτ (hF _ hσ) (hF _ hσ') h.ge _ _))

theorem classD4_conj_frame (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {R : Type u}
    [CommRing R] (h2 : (2 : R) = 0) {a b c d θ : Fin τ.rank → ℤ} (hp : IsD4Pattern τ a b c d)
    (hθ : a + b + 2 • c + d = θ) {P : List (Fin τ.rank → ℤ)}
    (hP : ∀ ρ ∈ P, IsRoot τ ρ ∧ iform ρ a = 0 ∧ iform ρ b = 0 ∧ iform ρ d = 0 ∧ iform ρ θ = 0)
    (e : (Fin τ.rank → ℤ) → R) :
    (pinnedX τ R (c + d) 1 * pinnedX τ R (b + c) 1 * pinnedX τ R (a + c) 1 *
          pinnedX τ R (b + c + d) 1) *
        (pinnedX τ R a 1 * pinnedX τ R b 1 * pinnedX τ R d 1 * pinnedX τ R θ 1 *
          (P.map fun ρ => pinnedX τ R ρ (e ρ)).prod) *
        (pinnedX τ R (c + d) 1 * pinnedX τ R (b + c) 1 * pinnedX τ R (a + c) 1 *
          pinnedX τ R (b + c + d) 1)⁻¹ =
      pinnedX τ R a 1 * pinnedX τ R b 1 * pinnedX τ R d 1 *
        (P.map fun ρ => pinnedX τ R ρ (e ρ)).prod := by
  subst hθ
  obtain ⟨rac, rbc, rcd, -, -, rbcd, -, -⟩ := IsD4Pattern.isRoot_add hτ hp
  have hcomm : Commute (pinnedX τ R (c + d) 1 * pinnedX τ R (b + c) 1 * pinnedX τ R (a + c) 1 *
      pinnedX τ R (b + c + d) 1) (P.map fun ρ => pinnedX τ R ρ (e ρ)).prod := by
    refine Commute.list_prod_right _ _ fun x hx => ?_
    obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
    obtain ⟨rρ, ha, hb, hd, hθ⟩ := hP ρ hρ
    have hc : iform ρ c = 0 := by
      rw [iform_add_right, iform_add_right, iform_add_right, two_nsmul, iform_add_right, ha, hb,
        hd] at hθ
      omega
    have ha' : iform a ρ = 0 := by rw [iform_comm]; exact ha
    have hb' : iform b ρ = 0 := by rw [iform_comm]; exact hb
    have hc' : iform c ρ = 0 := by rw [iform_comm]; exact hc
    have hd' : iform d ρ = 0 := by rw [iform_comm]; exact hd
    have k : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → iform γ ρ = 0 →
        Commute (pinnedX τ R γ 1) (pinnedX τ R ρ (e ρ)) := fun hγ h0 =>
      classD4_commute_pinnedX hτ hγ rρ h0.ge 1 (e ρ)
    exact (((k rcd (by rw [iform_add_left, hc', hd', add_zero])).mul_left
      (k rbc (by rw [iform_add_left, hb', hc', add_zero]))).mul_left
        (k rac (by rw [iform_add_left, ha', hc', add_zero]))).mul_left
          (k rbcd (by rw [iform_add_left, iform_add_left, hb', hc', hd', add_zero, add_zero]))
  rw [show ∀ g t z : (Module.End R (RootModule τ R))ˣ, g * (t * z) * g⁻¹ =
      (g * t * g⁻¹) * (g * z * g⁻¹) from fun g t z => by group, classD4_conj_eq hτ h2 hp,
    hcomm.mul_inv_cancel]

variable {K : Type} [Field K]

theorem exists_conj_frame_prod_of_isD4Pattern [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c d θ : Fin τ.rank → ℤ}
    (hp : IsD4Pattern τ a b c d) (hθ : a + b + 2 • c + d = θ) {P : List (Fin τ.rank → ℤ)}
    (hPr : ∀ ρ ∈ P, IsRoot τ ρ)
    (horth : (a :: b :: d :: θ :: P).Pairwise fun σ σ' => iform σ σ' = 0)
    (e : (Fin τ.rank → ℤ) → K) (he : ∀ σ ∈ a :: b :: d :: θ :: P, e σ ≠ 0) :
    ∃ g ∈ adjointGroup τ K,
      g * ((a :: b :: d :: θ :: P).map fun σ => pinnedX τ K σ (e σ)).prod * g⁻¹ =
        ((a :: b :: d :: P).map fun σ => pinnedX τ K σ 1).prod := by
  subst hθ
  have h2 : (2 : K) = 0 := by rw [← Nat.cast_two, CharP.cast_eq_zero]
  obtain ⟨ra, rb, -, rd, -⟩ := id hp
  have rθ := (IsD4Pattern.isRoot_add hτ hp).2.2.2.2.2.2.2
  have hF : ∀ σ ∈ a :: b :: d :: (a + b + 2 • c + d) :: P, IsRoot τ σ := by
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨ra, rb, rd, rθ, hPr⟩
  obtain ⟨h, hhC, -, -, hh⟩ := exists_torus_conj_frame_prod (classD4_noG2 hτ) hF horth e he
  have hP : ∀ ρ ∈ P, IsRoot τ ρ ∧ iform ρ a = 0 ∧ iform ρ b = 0 ∧ iform ρ d = 0 ∧
      iform ρ (a + b + 2 • c + d) = 0 := by
    simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at horth
    obtain ⟨⟨-, -, -, hPa⟩, ⟨-, -, hPb⟩, ⟨-, hPd⟩, hPθ, -⟩ := horth
    intro ρ hρ
    refine ⟨hPr ρ hρ, ?_, ?_, ?_, ?_⟩ <;> rw [iform_comm]
    exacts [hPa ρ hρ, hPb ρ hρ, hPd ρ hρ, hPθ ρ hρ]
  have key := classD4_conj_frame hτ h2 hp rfl hP fun _ => (1 : K)
  have hg : pinnedX τ K (c + d) 1 * pinnedX τ K (b + c) 1 * pinnedX τ K (a + c) 1 *
      pinnedX τ K (b + c + d) 1 ∈ adjointGroup τ K :=
    mul_mem (mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _)
  refine ⟨_ * h, mul_mem hg hhC, ?_⟩
  rw [show ∀ g h' L : ModGL τ K, g * h' * L * (g * h')⁻¹ = g * (h' * L * h'⁻¹) * g⁻¹ from
    fun g h' L => by group, hh]
  simp only [List.map_cons, List.prod_cons] at key ⊢
  simpa only [mul_assoc] using key

theorem exists_conj_frame_prod_of_perm [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {a b c d θ : Fin τ.rank → ℤ}
    (hp : IsD4Pattern τ a b c d) (hθ : a + b + 2 • c + d = θ) {F P : List (Fin τ.rank → ℤ)}
    (hFP : F.Perm (a :: b :: d :: θ :: P)) (hF : ∀ σ ∈ F, IsRoot τ σ)
    (horth : F.Pairwise fun σ σ' => iform σ σ' = 0) (e : (Fin τ.rank → ℤ) → K)
    (he : ∀ σ ∈ F, e σ ≠ 0) :
    ∃ g ∈ adjointGroup τ K, g * (F.map fun σ => pinnedX τ K σ (e σ)).prod * g⁻¹ =
      ((a :: b :: d :: P).map fun σ => pinnedX τ K σ 1).prod := by
  have horth' := hFP.pairwise horth fun h => by rw [iform_comm]; exact h
  rw [classD4_frame_prod_perm hτ hF horth hFP e]
  exact exists_conj_frame_prod_of_isD4Pattern hτ hp hθ
    (fun ρ hρ => hF ρ (hFP.mem_iff.2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hρ)))))) horth' e
    fun σ hσ => he σ (hFP.mem_iff.2 hσ)

theorem exists_conj_cascade_prod_E6 [Finite K] [CharP K 2] (e : (Fin Tag.E6.rank → ℤ) → K)
    (he : ∀ σ ∈ ([![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0],
      ![1, 2, 2, 3, 2, 1]] : List (Fin 6 → ℤ)), e σ ≠ 0) :
    ∃ g ∈ adjointGroup .E6 K,
      g * (([![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0],
          ![1, 2, 2, 3, 2, 1]] : List (Fin 6 → ℤ)).map fun σ => pinnedX .E6 K σ (e σ)).prod *
        g⁻¹ =
      (([![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0]] : List (Fin 6 → ℤ)).map
        fun σ => pinnedX .E6 K σ 1).prod :=
  exists_conj_frame_prod_of_isD4Pattern (Or.inr (Or.inl rfl)) isD4Pattern_E6_cascade
    (by funext i; fin_cases i <;> rfl) (fun _ h => by cases h) (by decide +kernel) e he

theorem exists_conj_cascade_prod_E7 [Finite K] [CharP K 2] (e : (Fin Tag.E7.rank → ℤ) → K)
    (he : ∀ σ ∈ ([![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
      ![0, 1, 1, 2, 1, 0, 0], ![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1],
      ![0, 0, 0, 0, 0, 0, 1]] : List (Fin 7 → ℤ)), e σ ≠ 0) :
    ∃ g ∈ adjointGroup .E7 K,
      g * (([![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
          ![0, 1, 1, 2, 1, 0, 0], ![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1],
          ![0, 0, 0, 0, 0, 0, 1]] : List (Fin 7 → ℤ)).map fun σ => pinnedX .E7 K σ (e σ)).prod *
        g⁻¹ =
      (([![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
          ![2, 2, 3, 4, 3, 2, 1], ![0, 1, 1, 2, 2, 2, 1], ![0, 0, 0, 0, 0, 0, 1]] :
            List (Fin 7 → ℤ)).map fun σ => pinnedX .E7 K σ 1).prod :=
  exists_conj_frame_prod_of_isD4Pattern (Or.inr (Or.inr (Or.inl rfl))) isD4Pattern_E7
    (by funext i; fin_cases i <;> rfl)
    (fun ρ hρ => isRootB_iff.1 (List.all_eq_true.1 (by decide +kernel) ρ hρ))
    (by decide +kernel) e he

theorem exists_conj_cascade_prod_E8 [Finite K] [CharP K 2] (e : (Fin Tag.E8.rank → ℤ) → K)
    (he : ∀ σ ∈ ([![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 1, 1, 2, 1, 0, 0, 0], ![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0],
      ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0]] : List (Fin 8 → ℤ)), e σ ≠ 0) :
    ∃ g ∈ adjointGroup .E8 K,
      g * (([![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
          ![0, 1, 1, 2, 1, 0, 0, 0], ![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0],
          ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 0, 0, 0, 0, 0, 1, 0]] : List (Fin 8 → ℤ)).map
            fun σ => pinnedX .E8 K σ (e σ)).prod * g⁻¹ =
      (([![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
          ![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1, 0],
          ![0, 0, 0, 0, 0, 0, 1, 0]] : List (Fin 8 → ℤ)).map fun σ => pinnedX .E8 K σ 1).prod :=
  exists_conj_frame_prod_of_isD4Pattern (Or.inr (Or.inr (Or.inr rfl))) isD4Pattern_E8
    (by funext i; fin_cases i <;> rfl)
    (fun ρ hρ => isRootB_iff.1 (List.all_eq_true.1 (by decide +kernel) ρ hρ))
    (by decide +kernel) e he

end Sound

end CFSG.SeitzReduction
