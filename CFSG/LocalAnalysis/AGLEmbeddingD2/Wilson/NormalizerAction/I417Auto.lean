module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CoverFacts
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormalizerQuotient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.Asc83Table CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec21 Subgroup

theorem mem_normalizer_of_map {Y Q : Type*} [Group Y] [Group Q] (π : Y →* Q) {K : Subgroup Y}
    (hker : π.ker ≤ K) {y : Y} (hy : π y ∈ Subgroup.normalizer ((K.map π : Subgroup Q) : Set Q)) :
    y ∈ Subgroup.normalizer (K : Set Y) := by
  have hmem : ∀ h : Y, h ∈ K ↔ π h ∈ K.map π := by
    intro h
    constructor
    · exact fun hh => Subgroup.mem_map_of_mem π hh
    · rintro ⟨x, hx, hxh⟩
      have : x⁻¹ * h ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxh, inv_mul_cancel]
      have h2 := hker this
      have := mul_mem hx h2
      simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hmem h, hmem (y * h * y⁻¹), map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.1 hy (π h)

theorem isTransvectionOn_of_central_comm {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    (hZF : Subgroup.center X ≤ F) (hZ3 : Nat.card (Subgroup.center X) = 3) {y : X}
    (hy : y ∈ Subgroup.normalizer (F : Set X))
    (hcomm : ∀ x ∈ F, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center X)
    (hne : F.normalizerMonoidHom ⟨y, hy⟩ ≠ 1) :
    IsTransvectionOn (F.normalizerMonoidHom ⟨y, hy⟩) := by
  set σ := F.normalizerMonoidHom ⟨y, hy⟩ with hσ
  have hσapp : ∀ a : F, ((σ a : F) : X) = y * a * y⁻¹ := fun a => rfl
  set Zs : Subgroup ↥F := (Subgroup.center X).subgroupOf F with hZs
  have hcard_Zs : Nat.card Zs = 3 := by
    rw [hZs, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZF).toEquiv, hZ3]
  have hgen : ∀ a : F, a⁻¹ * σ a ∈ Zs := by
    intro a
    have hc := hcomm a a.2
    rw [hZs, Subgroup.mem_subgroupOf]
    have h1 : ((a⁻¹ * σ a : F) : X) = (a : X)⁻¹ * (y * a * y⁻¹) := rfl
    rw [h1]
    have h2 : y * (a : X) * y⁻¹ = (y * a * y⁻¹ * (a : X)⁻¹) * a := by group
    rw [h2]
    have h3 := Subgroup.mem_center_iff.1 hc (a : X)⁻¹
    have : (a : X)⁻¹ * (y * a * y⁻¹ * (a : X)⁻¹ * a) = y * a * y⁻¹ * (a : X)⁻¹ := by
      calc (a : X)⁻¹ * (y * a * y⁻¹ * (a : X)⁻¹ * a)
          = ((a : X)⁻¹ * (y * a * y⁻¹ * (a : X)⁻¹)) * a := by group
        _ = ((y * a * y⁻¹ * (a : X)⁻¹) * (a : X)⁻¹) * a := by rw [h3]
        _ = y * a * y⁻¹ * (a : X)⁻¹ := by group
    rw [this]
    exact hc
  have hle : commOf σ ≤ Zs := by
    rw [commOf, Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact hgen a
  have hnbot : commOf σ ≠ ⊥ := by
    intro hbot
    apply hne
    ext a
    have h1 : a⁻¹ * σ a ∈ commOf σ := Subgroup.subset_closure ⟨a, rfl⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h1
    rw [MulAut.one_apply]
    exact congrArg Subtype.val h1.symm
  refine ⟨?_, ?_⟩
  · have hdvd : Nat.card (commOf σ) ∣ 3 := hcard_Zs ▸ Subgroup.card_dvd_of_le hle
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd ((Subgroup.card_eq_one).1 h) hnbot
    · exact h
  · intro w hw
    have hwZ := hle hw
    rw [hZs, Subgroup.mem_subgroupOf] at hwZ
    rw [mem_fixedSubgroupOf]
    apply Subtype.ext
    rw [hσapp]
    have := Subgroup.mem_center_iff.1 hwZ y
    calc y * (w : X) * y⁻¹ = (w : X) * y * y⁻¹ := by rw [this]
      _ = w := by group

theorem autIn_equiv_automizer {G : Type*} [Group G] (L : Subgroup G) {Q : Type*} [Group Q]
    (π : ↥L →* Q) (hπ : Function.Surjective π) (K : Subgroup ↥L) (hker : π.ker ≤ K)
    (hcent : ∀ y ∈ Subgroup.normalizer (K : Set ↥L),
      π y ∈ Subgroup.centralizer ((K.map π : Subgroup Q) : Set Q) → ∀ x ∈ K, y * x = x * y) :
    Nonempty (↥(autIn L (K.map L.subtype)) ≃* Automizer (K.map π)) := by
  set A : Subgroup G := K.map L.subtype with hA
  set N : Subgroup ↥L := Subgroup.normalizer (K : Set ↥L) with hN
  have hKA : ∀ k : ↥L, k ∈ K ↔ (k : G) ∈ A := fun k => by
    rw [hA, Subgroup.mem_map]
    constructor
    · exact fun h => ⟨k, h, rfl⟩
    · rintro ⟨k', hk', hkk⟩
      have : k' = k := Subtype.ext hkk
      exact this ▸ hk'
  have hNA : ∀ y ∈ N, (y : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hh
      exact (hKA (y * k * y⁻¹)).1 ((Subgroup.mem_normalizer_iff.1 hy k).1 hk)
    · intro hh
      obtain ⟨k, hk, hkh⟩ := Subgroup.mem_map.1 hh
      have hy' := Subgroup.mem_normalizer_iff.1 (inv_mem hy) k
      rw [inv_inv] at hy'
      have hmem : y⁻¹ * k * y ∈ K := hy'.1 hk
      have : h = ((y⁻¹ * k * y : ↥L) : G) := by
        have h1 : (k : G) = (y : G) * h * (y : G)⁻¹ := hkh
        calc h = (y : G)⁻¹ * ((y : G) * h * (y : G)⁻¹) * (y : G) := by group
          _ = _ := by rw [← h1]; rfl
      rw [this]
      exact (hKA _).1 hmem
  let ιN : N →* Subgroup.normalizer (A : Set G) :=
    { toFun := fun y => ⟨((y : ↥L) : G), hNA y y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  set Θ : N →* MulAut ↥A := A.normalizerMonoidHom.comp ιN with hΘ
  have hΘapp : ∀ (y : N) (a : ↥A), (((Θ y) a : ↥A) : G) = ((y : ↥L) : G) * a * ((y : ↥L) : G)⁻¹ :=
    fun _ _ => rfl
  have hrange : Θ.range = autIn L A := by
    ext σ
    rw [mem_autIn_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨((y : ↥L) : G), hNA y y.2, y.1.2, rfl⟩
    · rintro ⟨h, hNh, hL, rfl⟩
      have hyN : (⟨h, hL⟩ : ↥L) ∈ N := by
        rw [hN, Subgroup.mem_normalizer_iff]
        intro k
        rw [hKA k, hKA]
        exact Subgroup.mem_normalizer_iff.1 hNh (k : G)
      exact ⟨⟨⟨h, hL⟩, hyN⟩, rfl⟩
  have hΘker : ∀ y : N, y ∈ Θ.ker ↔ ∀ x ∈ K, (y : ↥L) * x = x * (y : ↥L) := by
    intro y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x hx
      have h1 := hΘapp y ⟨(x : G), (hKA x).1 hx⟩
      rw [h, MulAut.one_apply] at h1
      have h2 : (x : G) = (y : G) * x * (y : G)⁻¹ := h1
      apply Subtype.ext
      calc ((y : ↥L) * x : G) = ((y : G) * x * (y : G)⁻¹) * y := by group
        _ = x * y := by rw [← h2]
    · intro h
      ext a
      obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.1 a.2
      rw [hΘapp, MulAut.one_apply, ← hka]
      have h3 : ((y : ↥L) : G) * (k : G) = (k : G) * ((y : ↥L) : G) :=
        congrArg Subtype.val (h k hk)
      show ((y : ↥L) : G) * (k : G) * ((y : ↥L) : G)⁻¹ = (k : G)
      rw [h3]
      exact mul_inv_cancel_right _ _
  have hmapN : ∀ y : N, π (y : ↥L) ∈ Subgroup.normalizer ((K.map π : Subgroup Q) : Set Q) :=
    fun y => Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π y.2)
  let Ψ0 : N →* Subgroup.normalizer ((K.map π : Subgroup Q) : Set Q) :=
    { toFun := fun y => ⟨π (y : ↥L), hmapN y⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun x y => Subtype.ext (map_mul π _ _) }
  let Ψ : N →* Automizer (K.map π) := (QuotientGroup.mk' _).comp Ψ0
  have hΨsurj : Function.Surjective Ψ := by
    refine (QuotientGroup.mk'_surjective _).comp ?_
    rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := hπ q
    exact ⟨⟨y, mem_normalizer_of_map π hker hq⟩, rfl⟩
  have hΨker : ∀ y : N, y ∈ Ψ.ker ↔ ∀ x ∈ K, (y : ↥L) * x = x * (y : ↥L) := by
    intro y
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk (Ψ0 y) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact hcent y y.2 h
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have := h x hx
      show π x * π y = π y * π x
      rw [← map_mul, ← map_mul, ← this]
  have hkereq : Θ.ker = Ψ.ker := by
    ext y
    rw [hΘker, hΨker]
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans <|
    (QuotientGroup.quotientKerEquivRange Θ).symm.trans <|
    (QuotientGroup.quotientMulEquivOfEq hkereq).trans
      (QuotientGroup.quotientKerEquivOfSurjective Ψ hΨsurj)⟩

theorem cent_of_frame {X : Type*} [Group X] [Finite X] {k : Fin 6 → X} (h : J3Pkg k)
    (hZ : Nat.card (Subgroup.center X) = 3) {F : Subgroup X} (hF : F = F0 k)
    (hN : ∀ y ∈ Subgroup.normalizer (F : Set X), y ∈ Subgroup.closure (Set.range k))
    (hZF : Subgroup.center X ≤ F) {y : X} (hy : y ∈ Subgroup.normalizer (F : Set X))
    (hcomm : ∀ x ∈ F, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center X) :
    ∀ x ∈ F, y * x = x * y := by
  subst hF
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hxy⟩ := hcon
  have hne : (F0 k).normalizerMonoidHom ⟨y, hy⟩ ≠ 1 := by
    intro h1
    apply hxy
    have h2 := congrArg (fun σ : MulAut (F0 k) => ((σ ⟨x, hx⟩ : F0 k) : X)) h1
    have h3 : y * x * y⁻¹ = x := h2
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [h3]
  exact h.not_transvection y (hN y hy) hy
    (isTransvectionOn_of_central_comm hZF hZ hy hcomm hne)

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
