module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerGNDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542ThreeMultiplier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OddCentreAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OddCentreAlt

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.RankThree.PerfectCover

theorem transport_hel_hg {S A : Type} [Group S] [Group A] (e : S ≃* A)
    (hA : ∀ Pb : Subgroup A, Nat.card Pb = 9 → IsElemAbelian 3 Pb ∧
      ∃ g ∈ Subgroup.normalizer (Pb : Set A), ∀ x ∈ Pb, x ≠ 1 →
        g * x * g⁻¹ ∉ Subgroup.zpowers x) :
    ∀ Pb : Subgroup S, Nat.card Pb = 9 → IsElemAbelian 3 Pb ∧
      ∃ g ∈ Subgroup.normalizer (Pb : Set S), ∀ x ∈ Pb, x ≠ 1 →
        g * x * g⁻¹ ∉ Subgroup.zpowers x := by
  intro Pb h9
  set Qb : Subgroup A := Pb.map e.toMonoidHom with hQb
  have hQ9 : Nat.card Qb = 9 := by
    rw [hQb, Subgroup.card_map_of_injective e.injective]; exact h9
  obtain ⟨hel, g', hg'N, hg'⟩ := hA Qb hQ9
  have hmemQ : ∀ x : S, x ∈ Pb → e x ∈ Qb := fun x hx => ⟨x, hx, rfl⟩
  have hmemQ' : ∀ x : S, e x ∈ Qb → x ∈ Pb := by
    rintro x ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    rwa [← this]
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, e.symm g', ?_, ?_⟩
  · have := hel.1.is_comm.comm (⟨e a, hmemQ a a.2⟩ : Qb) ⟨e b, hmemQ b b.2⟩
    apply Subtype.ext
    apply e.injective
    simpa using congrArg Subtype.val this
  · have := hel.2 (e x) (hmemQ x hx)
    apply e.injective
    simpa using this
  · refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
    have key := Subgroup.mem_normalizer_iff.mp hg'N (e h)
    have he : e (e.symm g' * h * (e.symm g')⁻¹) = g' * e h * g'⁻¹ := by simp
    constructor
    · intro hh
      apply hmemQ'
      rw [he]; exact key.mp (hmemQ h hh)
    · intro hh
      have := hmemQ _ hh
      rw [he] at this
      exact hmemQ' h (key.mpr this)
  · intro x hx hx1 hmem
    apply hg' (e x) (hmemQ x hx) (fun h => hx1 (e.injective (by simpa using h)))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg e hk
    simpa using this

theorem card_center_dvd_cases
    {R : Type} [Group R] [Finite R] [Group.IsPerfect R]
    (hty : IsRankTwoLayerType (R ⧸ Subgroup.center R) ∨
      Nonempty ((R ⧸ Subgroup.center R) ≃* alternatingGroup (Fin 7))) :
    (Nonempty ((R ⧸ Subgroup.center R) ≃* alternatingGroup (Fin 6)) ∧
        Nat.card (Subgroup.center R) ∣ 6) ∨
      (Nonempty ((R ⧸ Subgroup.center R) ≃* alternatingGroup (Fin 7)) ∧
        Nat.card (Subgroup.center R) ∣ 6) ∨ Nat.card (Subgroup.center R) ∣ 2 := by
  have hdvd : Nat.card (Subgroup.center R) ∣ Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) := by
    have := card_ker_dvd_hopfMultiplier (QuotientGroup.mk' (Subgroup.center R))
      (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    rwa [QuotientGroup.ker_mk'] at this
  have viaEquiv : ∀ (B : Type) [Group B] (e : (R ⧸ Subgroup.center R) ≃* B) (m : ℕ),
      Nat.card (hopfMultiplier B) = m → Nat.card (Subgroup.center R) ∣ m := by
    intro B _ e m hm
    let p : R →* B := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center R))
    have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hker : p.ker = Subgroup.center R := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff e e.injective, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    haveI : Finite B := Finite.of_surjective p hp
    have hd := card_ker_dvd_hopfMultiplier p hp hker.le
    rw [hker, hm] at hd
    exact hd
  rcases hty with (h | h | h) | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨⟨e⟩, viaEquiv _ e 6 (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six).2⟩
  ·
    obtain ⟨e₁⟩ := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.nonempty_gl32_of_statedClassicalModel h
    obtain ⟨e₂⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) ≃* (R ⧸ Subgroup.center R) :=
      e₂.symm.trans (e₁.symm.trans (MulEquiv.refl _))
    obtain ⟨-, ⟨g⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv
      (k := ZMod 7) (by rw [ZMod.card]; norm_num) (by rw [ZMod.card]; norm_num) e
    have hcard : Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) = 2 := by
      rw [← Nat.card_congr (hopfMultiplierEquivGriess (R ⧸ Subgroup.center R)).toEquiv,
        Nat.card_congr g.toEquiv]
      simp [Nat.card_eq_fintype_card, ZMod.card]
    rw [hcard] at hdvd
    exact Or.inr (Or.inr hdvd)
  · obtain ⟨-, ⟨g⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psu_odd_row
      (X := R ⧸ Subgroup.center R) (n := 3) (p := 3) (f := 1) h (by decide)
    have hcard : Nat.card (hopfMultiplier (R ⧸ Subgroup.center R)) = 1 := by
      rw [← Nat.card_congr (hopfMultiplierEquivGriess (R ⧸ Subgroup.center R)).toEquiv,
        Nat.card_congr g.toEquiv]
      have h1 : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 3 1 = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 3 1 = (1, 1) := by
        simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
      rw [h1, h2]
      simp
    rw [hcard] at hdvd
    exact Or.inr (Or.inr ((Nat.dvd_one.mp hdvd) ▸ one_dvd _))
  · obtain ⟨e⟩ := h
    exact Or.inr (Or.inl ⟨⟨e⟩, viaEquiv _ e 6
      (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2⟩)


theorem kFactOddCentreE9 :
    KFactOddCentreE9 := by
  intro Y _ _ hq hodd hty
  haveI : Group.IsPerfect Y := Group.isPerfect_def.mpr hq.1
  have hbot : Nat.card (Subgroup.center Y) = 1 → Subgroup.center Y = ⊥ := fun h =>
    Subgroup.card_eq_one.mp h
  have hsix : Nat.card (Subgroup.center Y) ∣ 6 →
      Nat.card (Subgroup.center Y) = 1 ∨ Nat.card (Subgroup.center Y) = 3 := fun hd => by
    have hle : Nat.card (Subgroup.center Y) ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have key : ∀ n ≤ 6, n ∣ 6 → ¬ 2 ∣ n → n = 1 ∨ n = 3 := by decide
    exact key _ hle hd hodd
  have hmain : ∀ (A : Type) [Group A], ∀ (e : (Y ⧸ Subgroup.center Y) ≃* A),
      (Nat.card A).factorization 3 = 2 →
      (∀ Pb : Subgroup A, Nat.card Pb = 9 → IsElemAbelian 3 Pb ∧
        ∃ g ∈ Subgroup.normalizer (Pb : Set A), ∀ x ∈ Pb, x ≠ 1 →
          g * x * g⁻¹ ∉ Subgroup.zpowers x) →
      Nat.card (Subgroup.center Y) = 3 →
      (∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E = 9 → Subgroup.center Y ≤ E) ∧
        ∀ y : Y, orderOf y ≠ 9 := by
    intro A _ e hfac hA hZ3
    have hS : (Nat.card (Y ⧸ Subgroup.center Y)).factorization 3 = 2 := by
      rw [Nat.card_congr e.toEquiv]; exact hfac
    have hT := transport_hel_hg e hA
    exact ⟨fun E hE hE9 => center_le_of_elemAbelian hZ3 hS hE hE9,
      fun y => no_order_nine hZ3 hS (fun Pb _ h9 => (hT Pb h9).1) (fun Pb _ h9 => (hT Pb h9).2) y⟩
  rcases card_center_dvd_cases hty with ⟨⟨e⟩, hd⟩ | ⟨⟨e⟩, hd⟩ | hd
  · rcases hsix hd with h | h
    · exact Or.inl (hbot h)
    · exact Or.inr ⟨h, hmain _ e Alt6.fact3 (fun Pb h9 => Alt6.hel_hg_A Pb h9) h⟩
  · rcases hsix hd with h | h
    · exact Or.inl (hbot h)
    · exact Or.inr ⟨h, hmain _ e Alt7.fact3 (fun Pb h9 => Alt7.hel_hg_A Pb h9) h⟩
  · have hle : Nat.card (Subgroup.center Y) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have key : ∀ n ≤ 2, n ∣ 2 → ¬ 2 ∣ n → n = 1 := by decide
    exact Or.inl (hbot (key _ hle hd hodd))

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
