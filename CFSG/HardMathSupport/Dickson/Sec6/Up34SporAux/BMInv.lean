module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Classes
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvGroup
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMCenter
import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_conj_eq_gLBConj_inv (g : G) (J : Subgroup G) :
    J.map (MulAut.conj g).toMonoidHom = GLBConj g⁻¹ J := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨g⁻¹ * y * g, by simpa using h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem gLBConj_centralizer_of_inverts {s α : G} (hα : α * α = 1)
    (hinv : α * s * α⁻¹ = s⁻¹) :
    GLBConj α (Subgroup.centralizer ({s} : Set G)) = Subgroup.centralizer ({s} : Set G) := by
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  have hcs : (MulAut.conj α) s = s⁻¹ := by rw [MulAut.conj_apply]; exact hinv
  have hcc : ∀ y : G, (MulAut.conj α) ((MulAut.conj α) y) = y := by
    intro y
    simp only [MulAut.conj_apply, hαinv]
    calc α * (α * y * α) * α = (α * α) * y * (α * α) := by simp only [mul_assoc]
      _ = y := by rw [hα]; simp
  have key : ∀ y : G, s * y = y * s → s * (MulAut.conj α) y = (MulAut.conj α) y * s := by
    intro y hy
    have h2 := congrArg (MulAut.conj α) hy
    rw [map_mul, map_mul, hcs] at h2
    exact (Commute.inv_left_iff.1 (show Commute s⁻¹ ((MulAut.conj α) y) from h2))
  ext y
  have e : α * y * α⁻¹ = (MulAut.conj α) y := (MulAut.conj_apply α y).symm
  rw [mem_gLBConj, e, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have := key _ h
    rwa [hcc] at this
  · exact key y

theorem glaPComponent_conj_inverter {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J) :
    GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) (J.map (MulAut.conj α).toMonoidHom) := by
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ α
  rw [gLBConj_centralizer_of_inverts hα hinv] at h
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα
  rw [map_conj_eq_gLBConj_inv, hαinv]
  exact h

theorem noL3Comp_of_inverted {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hbig : ∀ k : ℕ, 6720 ^ k ≤ Nat.card G → k.factorial < Nat.card ↥H)
    (hnum : ∀ (r : ℕ) (ε : Bool) (e : ℕ), (e = 1 ∨ e = 3) → L3Cond r ε →
      L3Ord r ε ∣ Nat.card G * e → ¬ Nat.card ↥H ∣ L3Ord r ε ^ 2) :
    NoL3Comp (Subgroup.centralizer ({s} : Set G)) := by
  intro J hJ p hL
  set C := Subgroup.centralizer ({s} : Set G) with hCdef
  have hcore := glaPPrimeCore_eq_bot_of_glaPComponent hO hJ
  have e : barOf 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  have hZ : 6720 * Nat.card ↥(Subgroup.center ↥J) ≤ Nat.card ↥J :=
    six_seven_two_zero_mul_center_le_of_isL3Kind (isL3Kind_of_mulEquiv e hL)
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hZtop : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcon y x
    have hcard : Nat.card ↥(Subgroup.center ↥J) = Nat.card ↥J := by
      rw [hZtop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have hpos : 0 < Nat.card ↥J := Nat.card_pos
    omega
  have hHC : ∀ g ∈ H, g ∈ C := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hHs g hg
  have hconjComp : ∀ g ∈ H, GLAPComponent 3 C (J.map (MulAut.conj g).toMonoidHom) := by
    intro g hg
    rw [map_conj_eq_gLBConj_inv]
    exact glaPComponent_gLBConj_of_mem hJ (C.inv_mem (hHC g hg))
  have hcomm_of_ne : ∀ {A B : Subgroup G}, GLAPComponent 3 C A → GLAPComponent 3 C B → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
    intro A B hA hB hne a ha b hb
    have hc := commutator_le_gLAPPrimeCore_of_ne (by norm_num) hA hB hne
    rw [hO] at hc
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup G) := hc (Subgroup.commutator_mem_commutator ha hb)
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 h1)
  have hHJ : ∀ h ∈ H, ∀ j ∈ J, h * j * h⁻¹ ∈ J :=
    simple_normalizes_of_commuting_conj hH 6720
      (fun g₁ hg₁ g₂ hg₂ hne => hcomm_of_ne (hconjComp g₁ hg₁) (hconjComp g₂ hg₂) hne) hZ hbig
  have hcommα : J.map (MulAut.conj α).toMonoidHom = J ∨
      ∀ a ∈ J, ∀ b ∈ J.map (MulAut.conj α).toMonoidHom, a * b = b * a := by
    by_cases heq : J.map (MulAut.conj α).toMonoidHom = J
    · exact Or.inl heq
    · exact Or.inr (hcomm_of_ne hJ (glaPComponent_conj_inverter hα hinv hJ) (Ne.symm heq))
  have hJs : ∀ j ∈ J, s * j = j * s := fun j hj =>
    Subgroup.mem_centralizer_iff.1 (hJ.1 hj) s (Set.mem_singleton s)
  have hdvd : Nat.card ↥H ∣ Nat.card ↥J ^ 2 :=
    lemmaInv_core hα hinv hH hHα hHn hCQ hJs hHJ hcommα hnab
  obtain ⟨r, ε, f, hf, hc, hcard⟩ := isL3Kind_card_forms hL
  have hbar := card_barOf_of_glaPComponent hO hJ
  rw [hbar] at hcard
  have hJG : Nat.card ↥J ∣ Nat.card G := Subgroup.card_subgroup_dvd_card J
  have hL3 : L3Ord r ε ∣ Nat.card G * f := by
    rw [← hcard]
    exact Nat.mul_dvd_mul_right hJG f
  apply hnum r ε f hf hc hL3
  rw [← hcard]
  exact hdvd.trans (pow_dvd_pow_of_dvd (Dvd.intro f rfl) 2)

end CFSG.HardMathSupport.Dickson.Sec6.BM
