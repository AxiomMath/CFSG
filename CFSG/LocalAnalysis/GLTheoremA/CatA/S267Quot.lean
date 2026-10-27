module

public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma52
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Centralizer

variable {A Ω : Type*} [Group A] [Group Ω]

theorem map_inf_centralizer {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {M E : Subgroup A} (hE : IsPGroup p E) (hEM : E ≤ Subgroup.normalizer (M : Set A)) :
    (M ⊓ Subgroup.centralizer (E : Set A)).map π =
      M.map π ⊓ Subgroup.centralizer ((E.map π : Subgroup Ω) : Set Ω) := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxM, hxC⟩, rfl⟩
    refine ⟨⟨x, hxM, rfl⟩, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    show π e * π x = π x * π e
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.1 hxC e he)]
  · rintro y ⟨⟨m, hmM, rfl⟩, hyC⟩
    set V : Subgroup A := π.ker ⊓ M with hV
    have hVp : ¬ p ∣ Nat.card V := fun h =>
      hN (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hEV : E ≤ Subgroup.normalizer (V : Set A) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · rintro ⟨hv1, hv2⟩
        exact ⟨(MonoidHom.normal_ker π).conj_mem v hv1 e, (Subgroup.mem_normalizer_iff.1 (hEM he) v).1 hv2⟩
      · rintro ⟨hv1, hv2⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (hEM he) v).2 hv2⟩
        have := (MonoidHom.normal_ker π).conj_mem _ hv1 e⁻¹
        simpa [mul_assoc] using this
    have hmV : m ∈ Subgroup.normalizer (V : Set A) := by
      rw [Subgroup.mem_normalizer_iff]
      intro v
      constructor
      · rintro ⟨hv1, hv2⟩
        exact ⟨(MonoidHom.normal_ker π).conj_mem v hv1 m, M.mul_mem (M.mul_mem hmM hv2) (M.inv_mem hmM)⟩
      · rintro ⟨hv1, hv2⟩
        refine ⟨?_, ?_⟩
        · have := (MonoidHom.normal_ker π).conj_mem _ hv1 m⁻¹
          simpa [mul_assoc] using this
        · have := M.mul_mem (M.mul_mem (M.inv_mem hmM) hv2) hmM
          simpa [mul_assoc] using this
    have hx : ∀ u ∈ E, u * m * u⁻¹ * m⁻¹ ∈ V := by
      intro u hu
      refine ⟨?_, ?_⟩
      · have h1 : π u * π m = π m * π u := Subgroup.mem_centralizer_iff.1 hyC (π u) ⟨u, hu, rfl⟩
        have h2 : π (u * m * u⁻¹ * m⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]; group
        exact h2
      · exact M.mul_mem ((Subgroup.mem_normalizer_iff.1 (hEM hu) m).1 hmM) (M.inv_mem hmM)
    obtain ⟨v, hv, hfix⟩ := exists_fixed_in_coset' hE hVp hEV hmV hx
    refine ⟨m * v, ⟨M.mul_mem hmM hv.2, ?_⟩, ?_⟩
    · refine Subgroup.mem_centralizer_iff.2 fun e he => ?_
      have := hfix e he
      calc e * (m * v) = e * (m * v) * e⁻¹ * e := by group
        _ = m * v * e := by rw [this]
    · rw [map_mul, MonoidHom.mem_ker.1 hv.1, mul_one]

end Centralizer


section Components

variable {A Ω : Type} [Group A] [Finite A] [Group Ω]

omit [Finite A] in
theorem coprime_inf_ker {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    (Y : Subgroup A) : Nat.Coprime p (Nat.card ↥(Y ⊓ π.ker)) :=
  (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
    hN (hd.trans (Subgroup.card_dvd_of_le inf_le_right))

theorem glaPComponent_map_inf_centralizer {p : ℕ} (hp : p.Prime) (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {M E : Subgroup A} (hE : IsPGroup p E)
    (hEM : E ≤ Subgroup.normalizer (M : Set A)) {J : Subgroup A}
    (hJ : GLAPComponent p (M ⊓ Subgroup.centralizer (E : Set A)) J) :
    GLAPComponent p (M.map π ⊓ Subgroup.centralizer ((E.map π : Subgroup Ω) : Set Ω)) (J.map π) := by
  have h := glaPComponent_map hp π (coprime_inf_ker hp π hN _) hJ
  rwa [map_inf_centralizer hp π hN hE hEM] at h

theorem exists_glaPComponent_lift {p : ℕ} (hp : p.Prime) (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {M E : Subgroup A} (hE : IsPGroup p E)
    (hEM : E ≤ Subgroup.normalizer (M : Set A)) {J' : Subgroup Ω}
    (hJ' : GLAPComponent p (M.map π ⊓ Subgroup.centralizer ((E.map π : Subgroup Ω) : Set Ω)) J') :
    ∃ J : Subgroup A, GLAPComponent p (M ⊓ Subgroup.centralizer (E : Set A)) J ∧ J.map π = J' := by
  rw [← map_inf_centralizer hp π hN hE hEM] at hJ'
  exact exists_glaPComponent_map_eq hp π (coprime_inf_ker hp π hN _) hJ'

theorem glaPLayer_eq_of_map {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    {Y J : Subgroup A} (hJ : GLAPComponent p Y J)
    (hJ' : J.map π = GLAPLayer p (Y.map π)) : GLAPLayer p Y = J := by
  unfold GLAPLayer
  have hset : {L : Subgroup A | GLAPComponent p Y L} = {J} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      have h1 := glaPComponent_map hp π (coprime_inf_ker hp π hN Y) hL
      have h2 : L.map π ≤ GLAPLayer p (Y.map π) := le_sSup h1
      have hJm := glaPComponent_map hp π (coprime_inf_ker hp π hN Y) hJ
      have h3 : L.map π = J.map π := by
        refine CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_eq_of_le hp h1 hJm ?_
        rw [hJ']; exact h2
      exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq hp π (coprime_inf_ker hp π hN Y) hL hJ h3
    · rintro rfl; exact hJ
  rw [hset, sSup_singleton]

end Components

section Core

variable {A Ω : Type} [Group A] [Finite A] [Group Ω]

theorem mem_glaPPrimeCoreOf_iff {p : ℕ} {H : Subgroup A} {g : A} :
    g ∈ GLAPPrimeCoreOf p H ↔ ∃ h ∈ GLAPPrimeCore p ↥H, (h : A) = g := by
  unfold GLAPPrimeCoreOf
  simp [Subgroup.mem_map]

theorem map_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    (Y : Subgroup A) :
    (GLAPPrimeCoreOf p Y).map π = GLAPPrimeCoreOf p (Y.map π) := by
  have h := glaPPrimeCore_map_subgroupMap hp π Y (coprime_inf_ker hp π hN Y)
  unfold GLAPPrimeCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

theorem inf_ker_le_glaPPrimeCoreOf {p : ℕ} (hp : p.Prime) (π : A →* Ω) (hN : ¬ p ∣ Nat.card π.ker)
    (Y : Subgroup A) : Y ⊓ π.ker ≤ GLAPPrimeCoreOf p Y := by
  have hker : (π.subgroupMap Y).ker ≤ GLAPPrimeCore p ↥Y :=
    le_sSup ⟨MonoidHom.normal_ker _, coprime_card_ker_subgroupMap π Y (coprime_inf_ker hp π hN Y)⟩
  intro x hx
  rw [mem_glaPPrimeCoreOf_iff]
  refine ⟨⟨x, hx.1⟩, hker ?_, rfl⟩
  rw [MonoidHom.mem_ker]
  exact Subtype.ext (MonoidHom.mem_ker.1 hx.2)

theorem mem_glaPPrimeCoreOf_iff_map {p : ℕ} (hp : p.Prime) (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {Y : Subgroup A} {x : A} (hx : x ∈ Y) :
    x ∈ GLAPPrimeCoreOf p Y ↔ π x ∈ GLAPPrimeCoreOf p (Y.map π) := by
  rw [← map_glaPPrimeCoreOf hp π hN Y]
  constructor
  · intro h; exact ⟨x, h, rfl⟩
  · rintro ⟨o, ho, hox⟩
    have h1 : o⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hox, inv_mul_cancel]
    have hoY : o ∈ Y := Subgroup.map_subtype_le _ ho
    have h2 : o⁻¹ * x ∈ GLAPPrimeCoreOf p Y :=
      inf_ker_le_glaPPrimeCoreOf hp π hN Y ⟨Y.mul_mem (Y.inv_mem hoY) hx, h1⟩
    have := (GLAPPrimeCoreOf p Y).mul_mem ho h2
    simpa using this

theorem mem_centModSubgroup_map_iff {p : ℕ} (hp : p.Prime) (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {J : Subgroup A} {b : A} (hb : b ∈ Subgroup.normalizer (J : Set A)) :
    b ∈ centModSubgroup p J ↔ π b ∈ centModSubgroup p (J.map π) := by
  have hJ' : π b ∈ Subgroup.normalizer ((J.map π : Subgroup Ω) : Set Ω) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨b * l * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb l).1 hl, by simp⟩
    · rintro ⟨l, hl, hly⟩
      have hl2 : b⁻¹ * l * b ∈ J := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) l).1 hl
        simpa using this
      refine ⟨b⁻¹ * l * b, hl2, ?_⟩
      simp only [map_mul, map_inv]
      rw [hly]
      group
  constructor
  · rintro ⟨-, h⟩
    refine ⟨hJ', ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    have := h l hl
    rw [← map_glaPPrimeCoreOf hp π hN J]
    refine ⟨_, this, ?_⟩
    exact map_commutatorElement π l b
  · rintro ⟨-, h⟩
    refine ⟨hb, fun l hl => ?_⟩
    have hlb : ⁅l, b⁆ ∈ J := by
      have h1 := (Subgroup.mem_normalizer_iff.1 hb l).1 hl
      have h2 : b * l * b⁻¹ * l⁻¹ ∈ J := J.mul_mem h1 (J.inv_mem hl)
      have : ⁅l, b⁆ = (b * l * b⁻¹ * l⁻¹)⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
      rw [this]
      exact J.inv_mem h2
    rw [mem_glaPPrimeCoreOf_iff_map hp π hN hlb]
    have := h (π l) ⟨l, hl, rfl⟩
    rw [map_commutatorElement π l b]
    exact this

end Core


theorem map_gLBConj {G G' : Type*} [Group G] [Group G'] (π : G →* G') (g : G) (H : Subgroup G) :
    (GLBConj g H).map π = GLBConj (π g) (H.map π) := by
  unfold GLBConj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

section Layer

variable {A Ω : Type} [Group A] [Finite A] [Group Ω]

theorem glaPLayer_ne_bot_iff {G : Type} [Group G] [Finite G] (p : ℕ) (Y : Subgroup G) :
    GLAPLayer p Y ≠ ⊥ ↔ ∃ J : Subgroup G, GLAPComponent p Y J := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    apply h
    unfold GLAPLayer
    have : {L : Subgroup G | GLAPComponent p Y L} = ∅ := by
      ext L; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]; exact hne L
    rw [this, sSup_empty]
  · rintro ⟨J, hJ⟩ h
    have hle : J ≤ GLAPLayer p Y := le_sSup hJ
    rw [h] at hle
    exact CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_ne_bot hJ (le_bot_iff.1 hle)

theorem glaPLayer_map_ne_bot_iff {p : ℕ} (hp : p.Prime) [Finite Ω] (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) (Y : Subgroup A) :
    GLAPLayer p (Y.map π) ≠ ⊥ ↔ GLAPLayer p Y ≠ ⊥ := by
  rw [glaPLayer_ne_bot_iff, glaPLayer_ne_bot_iff]
  constructor
  · rintro ⟨J', hJ'⟩
    obtain ⟨J, hJ, -⟩ := exists_glaPComponent_map_eq hp π (coprime_inf_ker hp π hN Y) hJ'
    exact ⟨J, hJ⟩
  · rintro ⟨J, hJ⟩
    exact ⟨_, glaPComponent_map hp π (coprime_inf_ker hp π hN Y) hJ⟩

theorem exists_glaPComponent_lift_invariant {p : ℕ} (hp : p.Prime) [Finite Ω] (π : A →* Ω)
    (hN : ¬ p ∣ Nat.card π.ker) {M B₁ : Subgroup A} (hB : IsPGroup p B₁) (hBM : B₁ ≤ Subgroup.normalizer (M : Set A))
    (hBc : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x) {D' : Subgroup Ω} (hD' : D' ≤ B₁.map π)
    {J' : Subgroup Ω}
    (hJ' : GLAPComponent p (M.map π ⊓ Subgroup.centralizer (D' : Set Ω)) J')
    (hBJ : B₁.map π ≤ Subgroup.normalizer (J' : Set Ω)) :
    ∃ J : Subgroup A, GLAPComponent p (M ⊓ Subgroup.centralizer ((B₁ ⊓ D'.comap π : Subgroup A) : Set A)) J ∧
      J.map π = J' ∧ B₁ ≤ Subgroup.normalizer (J : Set A) := by
  set D : Subgroup A := B₁ ⊓ D'.comap π with hD
  have hDB : D ≤ B₁ := inf_le_left
  have hDmap : D.map π = D' := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := hD' hy
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
  have hDp : IsPGroup p D := hB.to_le hDB
  have hDM : D ≤ Subgroup.normalizer (M : Set A) := hDB.trans hBM
  have hJ'' : GLAPComponent p (M.map π ⊓ Subgroup.centralizer ((D.map π : Subgroup Ω) : Set Ω)) J' := by
    rw [hDmap]; exact hJ'
  obtain ⟨J, hJ, hJmap⟩ := exists_glaPComponent_lift hp π hN hDp hDM hJ''
  refine ⟨J, hJ, hJmap, fun b hb => ?_⟩
  have hbC : b ∈ Subgroup.centralizer (D : Set A) :=
    Subgroup.mem_centralizer_iff.2 fun d hd => hBc d (hDB hd) b hb
  have hbX : b ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (D : Set A) : Subgroup A) : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.1 (hBM hb) x)
      (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hbC) x)
  have hbX' : b⁻¹ ∈ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (D : Set A) : Subgroup A) : Set A) :=
    Subgroup.inv_mem _ hbX
  have hJb := glaPComponent_gLBConj hJ b⁻¹
  rw [mem_normalizer_iff_gLBConj_eq.1 hbX'] at hJb
  have hπb : π b ∈ Subgroup.normalizer (J' : Set Ω) := hBJ ⟨b, hb, rfl⟩
  have himg : (GLBConj b⁻¹ J).map π = J.map π := by
    rw [map_gLBConj, map_inv, hJmap]
    exact mem_normalizer_iff_gLBConj_eq.1 (Subgroup.inv_mem _ hπb)
  have heq := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq hp π (coprime_inf_ker hp π hN _) hJb hJ himg
  rw [mem_normalizer_iff_gLBConj_eq]
  have := congrArg (GLBConj b) heq
  rw [gLBConj_gLBConj_inv] at this
  exact this.symm


end Layer

end CFSG.LocalAnalysis.GLTheoremA.S267

end
