module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.CGT.PushingUpLit.BHS.Replacement
public import CFSG.CGT.PushingUpLit.BHS.GlaubOne
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUp.ResidualTwo
public import CFSG.CGT.PushingUpLit.BHS.LLemmaBasic
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS.Glauberman

variable {V : Type} [CommGroup V] {Γ : Type} [Group Γ]

structure ThreeFiveHyp (ρ : Γ →* MulAut V) (T M A : Subgroup Γ) : Prop where
  hV : ∀ v : V, v ^ 2 = 1
  faithful : Function.Injective ρ
  minpar : MinPar ⊤ T M
  le_T : A ≤ T
  elemAb : IsElemAbelian2 (A.map ρ)
  card_le : Nat.card V ≤ Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ))
  lt_wt : ∀ B : Subgroup (MulAut V), B ≤ A.map ρ → B ≠ ⊥ → B ≠ A.map ρ →
    Nat.card B * Nat.card (fixV B) < Nat.card (A.map ρ) * Nat.card (fixV (A.map ρ))
  nontriv : ∃ g : Γ, ∃ z ∈ fixV (T.map ρ), ρ g z ≠ z
  gen : ∀ x : Γ, x ∉ M → A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤

theorem isQuadratic_of_weights [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    (hel : IsElemAbelian2 A) (hne : A ≠ ⊥) (hcard : Nat.card V ≤ Nat.card A * Nat.card (fixV A))
    (hlt : ∀ B : Subgroup (MulAut V), B ≤ A → B ≠ ⊥ → B ≠ A →
      Nat.card B * Nat.card (fixV B) < Nat.card A * Nat.card (fixV A)) : IsQuadratic A := by
  have hmax : ∀ B ≤ A, wt B ≤ wt A := by
    intro B hB
    by_cases hB0 : B = ⊥
    · subst hB0
      show Nat.card (⊥ : Subgroup (MulAut V)) * Nat.card (fixV (⊥ : Subgroup (MulAut V))) ≤ _
      rw [B1.card_bot_mul_card_fixV]
      exact hcard
    · by_cases hBA : B = A
      · subst hBA
        exact le_rfl
      · exact (hlt B hB hB0 hBA).le
  have hAV : IsAV A := ⟨hel, hmax⟩
  obtain ⟨hw, -, hcomm0⟩ := replacement hel.1 hmax
  obtain ⟨-, -, hne'⟩ := timmesfeld_replacement hV hAV ⊤
  rw [commOn_top] at hne'
  have hcomm : commV A ≠ ⊥ := fun h => hne (commV_eq_bot_iff.1 h)
  have hA0 : commV (cenIn A (commV A)) ≠ ⊥ := hne' hcomm
  have hbot : cenIn A (commV A) ≠ ⊥ := fun h => hA0 (by rw [h]; exact commV_eq_bot_iff.2 rfl)
  have hAA : cenIn A (commV A) = A := by
    by_contra hneq
    have := hlt _ (cenIn_le A _) hbot hneq
    exact absurd hw (Nat.ne_of_lt this)
  intro u hu a ha
  have : a ∈ cenIn A (commV A) := by rw [hAA]; exact ha
  exact this.2 u hu

@[expose] def wMod (ρ : Γ →* MulAut V) (T : Subgroup Γ) : Subgroup V :=
  Subgroup.closure {w | ∃ g : Γ, ∃ z ∈ fixV (T.map ρ), w = ρ g z}

theorem apply_mem_wMod (ρ : Γ →* MulAut V) (T : Subgroup Γ) (g : Γ) {z : V}
    (hz : z ∈ fixV (T.map ρ)) : ρ g z ∈ wMod ρ T :=
  Subgroup.subset_closure ⟨g, z, hz, rfl⟩

theorem wMod_inv (ρ : Γ →* MulAut V) (T : Subgroup Γ) (g : Γ) {w : V} (hw : w ∈ wMod ρ T) :
    ρ g w ∈ wMod ρ T := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨g', z, hz, rfl⟩ := hw
    rw [← MulAut.mul_apply, ← map_mul]
    exact apply_mem_wMod ρ T _ hz
  | one => simp
  | mul y z _ _ ihy ihz =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ih =>
    rw [map_inv]
    exact Subgroup.inv_mem _ ih

theorem fixV_le_wMod (ρ : Γ →* MulAut V) (T : Subgroup Γ) : fixV (T.map ρ) ≤ wMod ρ T := by
  intro z hz
  have := apply_mem_wMod ρ T 1 hz
  simpa using this

theorem fixV_range_le (ρ : Γ →* MulAut V) (T : Subgroup Γ) :
    fixV ρ.range ≤ fixV (T.map ρ) := fun v hv x hx => by
  obtain ⟨t, -, rfl⟩ := hx
  exact hv _ (MonoidHom.mem_range.2 ⟨t, rfl⟩)

theorem map_map_conj (ρ : Γ →* MulAut V) (A : Subgroup Γ) (x : Γ) :
    (A.map (MulAut.conj x).toMonoidHom).map ρ =
      (A.map ρ).map (MulAut.conj (ρ x)).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨ρ a, ⟨a, ha, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨x * a * x⁻¹, ⟨a, ha, rfl⟩, by simp⟩

theorem isQuadratic_map_conj {A : Subgroup (MulAut V)} (hA : IsQuadratic A) (g : MulAut V) :
    IsQuadratic (A.map (MulAut.conj g).toMonoidHom) := by
  show commV _ ≤ fixV _
  rw [B19.commV_map_conj, fixV_map_conj]
  exact Subgroup.map_mono hA

namespace ThreeFiveHyp

variable {ρ : Γ →* MulAut V} {T M A : Subgroup Γ} (h : ThreeFiveHyp ρ T M A)

include h

theorem exists_not_mem : ∃ x : Γ, x ∉ M := by
  obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt h.minpar.lt_P
  exact ⟨x, hx⟩

theorem A_ne_bot : A ≠ ⊥ := by
  intro hA
  obtain ⟨x, hx⟩ := h.exists_not_mem
  have h1 := h.gen x hx
  rw [hA, Subgroup.map_bot, bot_sup_eq] at h1
  have hx1 : x ∈ (⊥ : Subgroup Γ) := by rw [h1]; exact Subgroup.mem_top x
  rw [Subgroup.mem_bot] at hx1
  exact hx (hx1 ▸ M.one_mem)

theorem quadratic [Finite V] : IsQuadratic (A.map ρ) := by
  refine isQuadratic_of_weights h.hV h.elemAb ?_ h.card_le h.lt_wt
  intro h0
  apply h.A_ne_bot
  rw [eq_bot_iff]
  intro a ha
  have : ρ a ∈ A.map ρ := Subgroup.mem_map_of_mem ρ ha
  rw [h0, Subgroup.mem_bot] at this
  exact (Subgroup.mem_bot).2 (h.faithful (by rw [this, map_one]))

end ThreeFiveHyp

end CFSG.CGT.PushingUpLit.BHS
