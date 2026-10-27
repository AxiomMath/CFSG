module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Reduction
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Tools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Balance CFSG.ClassicalInvolution.Balance.LocalBalance

open scoped commutatorElement

section Quotient

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ}

omit [Finite Y] in
theorem conjSub_eq_of_commute {s : Y} {L : Subgroup Y} (h : ∀ x ∈ L, s * x = x * s) :
    conjSub s L = L := by
  have hs : s ∈ Subgroup.centralizer (L : Set Y) :=
    Subgroup.mem_centralizer_iff.2 fun x hx => (h x hx).symm
  exact conjSub_eq_of_mem_normalizer (Subgroup.centralizer_le_normalizer (L : Set Y) hs)

theorem component_trichotomy (hH1 : H1Stmt.{0}) (hp : p.Prime) (hO : GLAPPrimeCore p Y = ⊥)
    {F : Subgroup Y} (hFel : IsElemAbelian p F) {f₀ : Y} (hf₀F : f₀ ∈ F) (hf₀1 : f₀ ≠ 1)
    {W : Subgroup Y}
    (hW : ∀ f ∈ F, f ≠ 1 → W ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y)))
    {L : Subgroup Y} (hL : IsComponent L) :
    (∀ s ∈ W, conjSub s L = L) ∧
      ((∃ s ∈ W, ∃ x ∈ L, s * x ≠ x * s) →
        (∀ f ∈ F, conjSub f L = L) ∧ ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f) := by
  have hLp := p_dvd_card_center_quot hp hO hL
  have hFp : ∀ f ∈ F, f ^ p = 1 := hFel.2
  by_cases hcen : ∃ f ∈ F, f ≠ 1 ∧ ∀ x ∈ L, f * x = x * f
  · obtain ⟨f, hfF, hf1, hfL⟩ := hcen
    have hLC : L ≤ Subgroup.centralizer ({f} : Set Y) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hfL x hx).symm
    have hnc : ¬ Nat.Coprime p (Nat.card L) := by
      intro hcop
      have h2 : p ∣ Nat.card L := hLp.trans (Subgroup.card_quotient_dvd_card _)
      exact hp.one_lt.ne' (hcop.eq_one_of_dvd h2)
    have key : ∀ s ∈ W, ∀ x ∈ L, s * x = x * s := fun s hs =>
      commute_of_mem_gLAPPrimeCoreOf_of_isComponent hp hLC
        (CFSG.LocalCores.component_overgroup hL hLC) hnc (hW f hfF hf1 hs)
    exact ⟨fun s hs => conjSub_eq_of_commute (key s hs), fun ⟨s, hs, x, hx, hne⟩ =>
      absurd (key s hs x hx) hne⟩
  · by_cases hmov : ∃ f ∈ F, conjSub f L ≠ L
    · obtain ⟨f, hfF, hfne⟩ := hmov
      have hf1 : f ≠ 1 := fun h => hfne (by rw [h, conjSub_one])
      have key : ∀ s ∈ W, ∀ x ∈ L, s * x = x * s := fun s hs =>
        commute_of_moved_p hp hL hLp (hFp f hfF) hfne (hW f hfF hf1 hs)
      exact ⟨fun s hs => conjSub_eq_of_commute (key s hs), fun ⟨s, hs, x, hx, hne⟩ =>
        absurd (key s hs x hx) hne⟩
    · push Not at hcen hmov
      refine ⟨fun s hs => conjSub_eq_of_mem_gLAPPrimeCoreOf hH1 hp hL hLp (hFp f₀ hf₀F)
        (hmov f₀ hf₀F) (hW f₀ hf₀F hf₀1 hs), fun _ => ⟨hmov, ?_⟩⟩
      intro f hf hf1 h
      obtain ⟨x, hx, hxne⟩ := hcen f hf hf1
      exact hxne (h x hx)

end Quotient

section Ambient

variable {G : Type} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem commutator_mem_core_iff {X : Subgroup G} {x s : G} (hx : x ∈ X) (hs : s ∈ X) :
    x * s * x⁻¹ * s⁻¹ ∈ GLAPPrimeCoreOf p X ↔
      (QuotientGroup.mk ⟨x, hx⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) * QuotientGroup.mk ⟨s, hs⟩ =
        QuotientGroup.mk ⟨s, hs⟩ * QuotientGroup.mk ⟨x, hx⟩ := by
  have hc : x * s * x⁻¹ * s⁻¹ ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hx hs) (X.inv_mem hx))
    (X.inv_mem hs)
  have h1 : x * s * x⁻¹ * s⁻¹ ∈ GLAPPrimeCoreOf p X ↔
      (⟨x * s * x⁻¹ * s⁻¹, hc⟩ : ↥X) ∈ GLAPPrimeCore p ↥X :=
    Subgroup.mem_map_iff_mem X.subtype_injective (x := ⟨x * s * x⁻¹ * s⁻¹, hc⟩)
  rw [h1, ← QuotientGroup.eq_one_iff]
  have h2 : (QuotientGroup.mk (⟨x * s * x⁻¹ * s⁻¹, hc⟩ : ↥X) : ↥X ⧸ GLAPPrimeCore p ↥X) =
      ⁅(QuotientGroup.mk ⟨x, hx⟩ : ↥X ⧸ GLAPPrimeCore p ↥X), QuotientGroup.mk ⟨s, hs⟩⁆ := by
    rw [commutatorElement_def]
    rfl
  rw [h2]
  exact commutatorElement_eq_one_iff_mul_comm

structure InDelta (p : ℕ) (X D S : Subgroup G) : Prop where
  D_le : D ≤ X
  elem : IsElemAbelian p D
  ne_bot : D ≠ ⊥
  S_le : S ≤ X
  le_core : ∀ e ∈ D, e ≠ 1 →
    S ≤ GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer ({e} : Set G))

theorem InDelta.of_le_gLADelta (hp : p.Prime) {X D S : Subgroup G} (hDX : D ≤ X)
    (hD : IsElemAbelian p D) (hD1 : D ≠ ⊥) (hSX : S ≤ X) (hSΔ : S ≤ GLADelta p D) :
    InDelta p X D S := by
  refine ⟨hDX, hD, hD1, hSX, fun e he he1 y hy => ?_⟩
  have hye : y ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set G)) := by
    have := hSΔ hy
    simp only [GLADelta, Subgroup.mem_iInf] at this
    exact this e he he1
  have hyCe : y ∈ Subgroup.centralizer ({e} : Set G) := Subgroup.map_subtype_le _ hye
  exact inf_glaPPrimeCoreOf_le (H := X ⊓ Subgroup.centralizer ({e} : Set G))
    (A := Subgroup.centralizer ({e} : Set G)) hp inf_le_right
    (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hSX hy, hyCe⟩, hye⟩)

variable {X D S : Subgroup G}

omit [Finite G] in
theorem InDelta.exists_ne_one (h : InDelta p X D S) : ∃ e ∈ D, e ≠ 1 := by
  by_contra hcon
  push Not at hcon
  exact h.ne_bot ((Subgroup.eq_bot_iff_forall D).2 hcon)

theorem InDelta.barX_le_core (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S) :
    ∀ f ∈ barX p X D, f ≠ 1 →
      barX p X S ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set (↥X ⧸ GLAPPrimeCore p ↥X))) := by
  rintro _ ⟨e', he', rfl⟩ hf1
  have heD : (e' : G) ∈ D := (Subgroup.mem_subgroupOf).1 he'
  have hne : e' ≠ 1 := fun h => hf1 (by rw [h, map_one])
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_centralizer_core hH1 hp h.D_le h.elem heD hne
    (h.le_core e' heD (fun h => hne (Subtype.ext h)) ((Subgroup.mem_subgroupOf).1 hx))

theorem InDelta.exists_barX_ne_one (hp : p.Prime) (h : InDelta p X D S) :
    ∃ f ∈ barX p X D, f ≠ 1 := by
  obtain ⟨e, he, he1⟩ := h.exists_ne_one
  exact ⟨_, ⟨⟨e, h.D_le he⟩, (Subgroup.mem_subgroupOf).2 he, rfl⟩,
    mk_ne_one hp h.D_le h.elem (e := ⟨e, h.D_le he⟩) he (fun h => he1 (congrArg Subtype.val h))⟩

omit [Finite G] in
theorem InDelta.barX_isComponent {L : Subgroup G} (hL : GLAPComponent p X L) :
    IsComponent (barX p X L) := (isComponent_iff_open _).2 hL.2.2.1

theorem InDelta.main (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S) {L : Subgroup G}
    (hL : GLAPComponent p X L) :
    S ≤ Subgroup.normalizer (L : Set G) ∧
      (¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf p X →
        D ≤ Subgroup.normalizer (L : Set G) ∧ kerB p D L = ⊥) := by
  classical
  have hO : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  obtain ⟨f₀, hf₀F, hf₀1⟩ := h.exists_barX_ne_one hp
  obtain ⟨hN, hCn⟩ := component_trichotomy hH1 hp hO (elemAbelian_image hp h.D_le h.elem) hf₀F
    hf₀1 (h.barX_le_core hH1 hp) (InDelta.barX_isComponent hL)
  have hnorm : ∀ {e : G} (he : e ∈ X), (QuotientGroup.mk ⟨e, he⟩ : ↥X ⧸ GLAPPrimeCore p ↥X) ∈
      Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) → e ∈ Subgroup.normalizer (L : Set G) :=
    fun he hy => mem_normalizer_of_barX_normalizer hL he hy
  refine ⟨fun s hs => hnorm (h.S_le hs) (mem_normalizer_of_conjSub_eq
    (hN _ ⟨⟨s, h.S_le hs⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩)), fun hn => ?_⟩
  have hnc : ∃ s ∈ barX p X S, ∃ x ∈ barX p X L, s * x ≠ x * s := by
    by_contra hcon
    push Not at hcon
    refine hn (Subgroup.commutator_le.2 fun x hx s hs => ?_)
    have hxX : x ∈ X := hL.1 hx
    have hsX : s ∈ X := h.S_le hs
    rw [commutatorElement_def, commutator_mem_core_iff hxX hsX]
    exact (hcon _ ⟨⟨s, hsX⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩ _
      ⟨⟨x, hxX⟩, (Subgroup.mem_subgroupOf).2 hx, rfl⟩).symm
  obtain ⟨hFn, hFf⟩ := hCn hnc
  refine ⟨fun e he => hnorm (h.D_le he) (mem_normalizer_of_conjSub_eq
    (hFn _ ⟨⟨e, h.D_le he⟩, (Subgroup.mem_subgroupOf).2 he, rfl⟩)), ?_⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun e he => ?_
  by_contra hne
  have heX : e ∈ X := h.D_le he.1
  refine hFf _ ⟨⟨e, heX⟩, (Subgroup.mem_subgroupOf).2 he.1, rfl⟩
    (mk_ne_one hp h.D_le h.elem (e := ⟨e, heX⟩) he.1 (fun h1 => hne (congrArg Subtype.val h1))) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hxL : (x : G) ∈ L := (Subgroup.mem_subgroupOf).1 hx
  obtain ⟨-, -, hcq⟩ := he.2
  have hcX := glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcq x hxL)
  exact ((commutator_mem_core_iff x.2 heX).1 hcX).symm

theorem InDelta.commutator_oPrimePOf_le (hH1 : H1Stmt.{0}) (hp : p.Prime) (h : InDelta p X D S) :
    ⁅oPrimePOf p X, S⁆ ≤ GLAPPrimeCoreOf p X := by
  obtain ⟨f₀, hf₀F, hf₀1⟩ := h.exists_barX_ne_one hp
  have hpe : f₀ ^ p = 1 := (elemAbelian_image hp h.D_le h.elem).2 f₀ hf₀F
  have hc := CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCoreOf_centralizer_le_centralizer_pCore
    hp (isPGroup_zpowers_of_pow_eq_one hp hpe)
  refine Subgroup.commutator_le.2 fun x hx s hs => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have hsX := h.S_le hs
  have hsc := hc (h.barX_le_core hH1 hp f₀ hf₀F hf₀1
    ⟨⟨s, hsX⟩, (Subgroup.mem_subgroupOf).2 hs, rfl⟩)
  rw [commutatorElement_def]
  exact (commutator_mem_core_iff y.2 hsX).2 (Subgroup.mem_centralizer_iff.1 hsc _ hy)

end Ambient

end CFSG.HardMathSupport.Solomon.Coordinator
