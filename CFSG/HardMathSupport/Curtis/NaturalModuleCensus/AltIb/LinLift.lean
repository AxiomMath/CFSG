module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Core

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)
open CFSG.LocalAnalysis.ComponentInitial LinearFlag

section EvenCentre

open TauCeti

theorem card_projectiveSL_three_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) : Nat.card (projectiveSL 3 K) = 20160 := by
  have hZ : Nat.card (scalars 3 K) = 3 := by
    have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
    rw [scalars_eq_center, Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (⟨0, by norm_num⟩ : Fin 3)).toEquiv]
    have htop : rootsOfUnity (Fintype.card (Fin 3)) K = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rw [mem_rootsOfUnity, Fintype.card_fin, ← hu]
      exact pow_card_eq_one'
    rw [htop, Subgroup.card_top, hu]
  rw [card_projectiveSL, card_SL_eq (by norm_num), hZ, hK]
  decide

theorem exists_mulEquiv_projectiveSL_valid {X : Type} [Group X] (h : IsLieOf IdxA X) :
    ∃ n f : ℕ, 2 ≤ n ∧ 1 ≤ f ∧ (n = 2 → 3 ≤ f) ∧ ((n = 3 ∨ n = 4) → 2 ≤ f) ∧
      Nonempty (X ≃* projectiveSL n (GaloisField 2 f)) := by
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h
  cases d with
  | A r q =>
    change q.p = 2 at hd
    obtain ⟨hr, hdup⟩ := (TauCeti.LieTypeIndex.valid_iff _).1 hv
    have hr' := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hr
    have hdup' := (TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).not.1 hdup
    have hcard : q.card = 2 ^ q.exponent := by
      rw [TauCeti.PrimePower.card_def, hd]
    obtain ⟨p, k, hp, hk⟩ := q
    change p = 2 at hd
    subst hd
    have : Fact (Nat.Prime 2) := ⟨hp⟩
    have hc : 2 ^ k = TauCeti.PrimePower.card ⟨2, k, hp, hk⟩ := hcard.symm
    simp only at hdup' hr'
    refine ⟨r + 1, k, by omega, hk, ?_, ?_, ⟨(e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL
      r ⟨2, k, hp, hk⟩ hv)).trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL _ _)⟩⟩
    · intro h2
      have hr1 : r = 1 := by omega
      subst hr1
      have h4 := hr'.2 rfl
      rw [← hc] at h4 hdup'
      by_contra hk3
      have hk2 : k ≤ 2 := by omega
      interval_cases k <;> simp at h4 hdup'
    · intro h34
      rw [← hc] at hdup'
      by_contra hk2
      have hk1 : k = 1 := by omega
      subst hk1
      rcases h34 with h3 | h3
      · exact hdup' (Or.inr (Or.inl ⟨by omega, by norm_num⟩))
      · exact hdup' (Or.inr (Or.inr ⟨by omega, by norm_num⟩))
  | _ => exact hd.elim

theorem card_dvd_of_even_centre_linear (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] (hX : IsLieOf IdxA (A ⧸ Subgroup.center A))
    (heven : ¬ Odd (Nat.card (Subgroup.center A))) :
    Nat.card A ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 := by
  obtain ⟨n, f, hn, hf, h2, h34, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_valid hX
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h22 : ¬ (n = 2 ∧ Nat.card (GaloisField 2 f) = 2) := by
    rintro ⟨h, hc⟩
    have := h2 h
    rw [hK] at hc
    have h8 : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hm := ToralCensus.lieModel_of_projectiveSL_evenChar hf hK hn h22 (MulEquiv.refl _)
  have hdvd := ToralCensus.card_center_dvd_multiplierOrders hGA e hm
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL n 2 f =
      (Nat.gcd n (2 ^ f - 1), 1) := rfl
  rw [hgen, mul_one] at hdvd
  have h2Z : 2 ∣ Nat.card (Subgroup.center A) :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 heven)
  have hcop : Nat.Coprime 2 (Nat.gcd n (2 ^ f - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right _ _)
      (Nat.coprime_two_left.2 (ToralCensus.odd_two_pow_pred hf))
  have h2x := hcop.dvd_of_dvd_mul_left (h2Z.trans hdvd)
  have hnf : n = 3 ∧ f = 2 := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders at h2x
    split at h2x
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (exfalso
         first
          | exact absurd (h2 rfl) (by norm_num)
          | exact absurd (h34 (Or.inl rfl)) (by norm_num)
          | exact absurd (h34 (Or.inr rfl)) (by norm_num)
          | omega
          | contradiction)
  obtain ⟨rfl, rfl⟩ := hnf
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by rw [hK]; norm_num
  have hP : Nat.card (A ⧸ Subgroup.center A) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_projectiveSL_three_of_card_four hK4
  have hZ48 : Nat.card (Subgroup.center A) ∣ 48 := by
    have : (Nat.gcd 3 (2 ^ 2 - 1), 1).1 *
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 2).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 2).2) = 48 := by decide
    exact this ▸ hdvd
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center A), hP]
  have : 20160 * 48 = 2 ^ 10 * 3 ^ 3 * 5 * 7 := by norm_num
  rw [← this]
  exact Nat.mul_dvd_mul_left _ hZ48

theorem not_sq_dvd_card_of_even_centre_linear (hGA : CFSG.Open.GriessAllModelsStatement)
    {A : Type} [Group A] [Finite A] [Group.IsPerfect A]
    (hX : IsLieOf IdxA (A ⧸ Subgroup.center A))
    (heven : ¬ Odd (Nat.card (Subgroup.center A))) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ p ^ 2 ∣ Nat.card A := fun h => by
  have h' := h.trans (card_dvd_of_even_centre_linear hGA hX heven)
  have hd : p ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 := (dvd_pow_self p two_ne_zero).trans h'
  have key : p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h7
    · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h5
      · rcases (Nat.Prime.dvd_mul hp).1 h2 with h4 | h33
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h4)
          omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h33)
          omega
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7)
  rcases key with rfl | rfl <;> norm_num at h'

theorem even_centre_l34 (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hX : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L))
    (heven : ¬ Odd (Nat.card (Subgroup.center ↥L))) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Subgroup Y} (hEL : E ≤ L) (hcard : Nat.card E = p ^ 2) : False := by
  have : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hq.1
  exact not_sq_dvd_card_of_even_centre_linear hGA hX heven hp hp5
    (hcard ▸ Subgroup.card_dvd_of_le hEL)

section Cover

theorem exists_cover_or_sq_free
    (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hCP : CompParabE L J) (hA : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L)) :
    (¬ Odd (Nat.card (Subgroup.center ↥L)) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ E : Subgroup Y, E ≤ L → Nat.card E ≠ p ^ 2) ∨
    (Odd (Nat.card (Subgroup.center ↥L)) ∧
      ∃ (n f : ℕ) (σ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
        (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ),
        3 ≤ n ∧ 1 ≤ f ∧ Function.Surjective σ ∧
        σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
        (∀ g, e (QuotientGroup.mk (σ g)) = proj n (GaloisField 2 f) g) ∧
        (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ I.Nonempty ∧ (∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) ∧
        (J.subgroupOf L).comap σ = flagStabilizer n (GaloisField 2 f) I) := by
  by_cases hodd : Odd (Nat.card (Subgroup.center ↥L))
  · exact Or.inr ⟨hodd, ToralCensus.exists_cover_comap_eq_flagStabilizer hGA
      ⟨hCP.comp, hCP.type, hodd, hCP.parab, hCP.ne_top, hCP.ne_borel⟩ hA⟩
  · refine Or.inl ⟨hodd, fun p hp hp5 E hEL hEc => ?_⟩
    exact even_centre_l34 hGA hCP.comp.2.2 hA hodd hp hp5 hEL hEc

end Cover

section Lift

open scoped commutatorElement

variable {G M : Type*} [Group G] [Group M]

theorem commutator_commutator_eq_one_of_central_aux {a b y : G}
    (ha : ⁅a, y⁆ ∈ Subgroup.center G) (hb : ⁅b, y⁆ ∈ Subgroup.center G) : ⁅⁅a, b⁆, y⁆ = 1 := by
  set α := ⁅a, y⁆ with hα
  set β := ⁅b, y⁆ with hβ
  have conj1 : ∀ (g z : G), z ∈ Subgroup.center G → g * z * g⁻¹ = z := fun g z hz => by
    rw [Subgroup.mem_center_iff.1 hz g, mul_assoc, mul_inv_cancel, mul_one]
  have conj2 : ∀ (g z : G), z ∈ Subgroup.center G → g⁻¹ * z * g = z := fun g z hz => by
    simpa using conj1 g⁻¹ z hz
  have e1 : a * y * a⁻¹ = α * y := by rw [hα, commutatorElement_def]; group
  have e2 : b * y * b⁻¹ = β * y := by rw [hβ, commutatorElement_def]; group
  have e1' : a⁻¹ * y * a = α⁻¹ * y := by
    have h1 : a⁻¹ * (α * y) * a = α * (a⁻¹ * y * a) := by
      calc a⁻¹ * (α * y) * a = (a⁻¹ * α * a) * (a⁻¹ * y * a) := by group
        _ = α * (a⁻¹ * y * a) := by rw [conj2 a α ha]
    have h2 : a⁻¹ * (α * y) * a = y := by rw [← e1]; group
    rw [h2] at h1
    calc a⁻¹ * y * a = α⁻¹ * (α * (a⁻¹ * y * a)) := by group
      _ = α⁻¹ * y := by rw [← h1]
  have e2' : b⁻¹ * y * b = β⁻¹ * y := by
    have h1 : b⁻¹ * (β * y) * b = β * (b⁻¹ * y * b) := by
      calc b⁻¹ * (β * y) * b = (b⁻¹ * β * b) * (b⁻¹ * y * b) := by group
        _ = β * (b⁻¹ * y * b) := by rw [conj2 b β hb]
    have h2 : b⁻¹ * (β * y) * b = y := by rw [← e2]; group
    rw [h2] at h1
    calc b⁻¹ * y * b = β⁻¹ * (β * (b⁻¹ * y * b)) := by group
      _ = β⁻¹ * y := by rw [← h1]
  have hα' : α⁻¹ ∈ Subgroup.center G := inv_mem ha
  have hβ' : β⁻¹ ∈ Subgroup.center G := inv_mem hb
  have key : ⁅a, b⁆ * y * ⁅a, b⁆⁻¹ = y := by
    have s1 : a⁻¹ * (β⁻¹ * y) * a = β⁻¹ * (α⁻¹ * y) := by
      calc a⁻¹ * (β⁻¹ * y) * a = (a⁻¹ * β⁻¹ * a) * (a⁻¹ * y * a) := by group
        _ = β⁻¹ * (α⁻¹ * y) := by rw [conj2 a _ hβ', e1']
    have s2 : b * (β⁻¹ * (α⁻¹ * y)) * b⁻¹ = β⁻¹ * (α⁻¹ * (β * y)) := by
      calc b * (β⁻¹ * (α⁻¹ * y)) * b⁻¹ = (b * β⁻¹ * b⁻¹) * ((b * α⁻¹ * b⁻¹) * (b * y * b⁻¹)) := by
            group
        _ = β⁻¹ * (α⁻¹ * (β * y)) := by rw [conj1 b _ hβ', conj1 b _ hα', e2]
    have s3 : a * (β⁻¹ * (α⁻¹ * (β * y))) * a⁻¹ = β⁻¹ * (α⁻¹ * (β * (α * y))) := by
      calc a * (β⁻¹ * (α⁻¹ * (β * y))) * a⁻¹
          = (a * β⁻¹ * a⁻¹) * ((a * α⁻¹ * a⁻¹) * ((a * β * a⁻¹) * (a * y * a⁻¹))) := by group
        _ = β⁻¹ * (α⁻¹ * (β * (α * y))) := by
          rw [conj1 a _ hβ', conj1 a _ hα', conj1 a β hb, e1]
    have s4 : β⁻¹ * (α⁻¹ * (β * (α * y))) = y := by
      have hαβ : α * β = β * α := Subgroup.mem_center_iff.1 hb α
      calc β⁻¹ * (α⁻¹ * (β * (α * y))) = β⁻¹ * α⁻¹ * (β * α) * y := by group
        _ = β⁻¹ * α⁻¹ * (α * β) * y := by rw [hαβ]
        _ = y := by group
    calc ⁅a, b⁆ * y * ⁅a, b⁆⁻¹
        = a * (b * (a⁻¹ * (b⁻¹ * y * b) * a) * b⁻¹) * a⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = a * (b * (a⁻¹ * (β⁻¹ * y) * a) * b⁻¹) * a⁻¹ := by rw [e2']
      _ = y := by rw [s1, s2, s3, s4]
  rw [commutatorElement_def, key]
  group

theorem commute_of_perfect_of_map_commute {σ : G →* M} (hker : σ.ker ≤ Subgroup.center G)
    {W : Subgroup G} (hW : ⁅W, W⁆ = W) {y : G} (h : ∀ w ∈ W, σ w * σ y = σ y * σ w) :
    ∀ w ∈ W, w * y = y * w := by
  intro w hw
  have hcen : ∀ g ∈ W, ⁅g, y⁆ ∈ Subgroup.center G := by
    intro g hg
    refine hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h g hg
  have hle : ⁅W, W⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have := commutator_commutator_eq_one_of_central_aux (hcen g₁ hg₁) (hcen g₂ hg₂)
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  rw [hW] at hle
  exact (Subgroup.mem_centralizer_iff.1 (hle hw) y (Set.mem_singleton y)).symm

theorem exists_perfect_lift {σ : G →* M} (hker : σ.ker ≤ Subgroup.center G) {V : Subgroup M}
    (hV : ⁅V, V⁆ = V) (hVr : V ≤ σ.range) {x : M} (hVx : V ≤ Subgroup.centralizer ({x} : Set M))
    {xh : G} (hxh : σ xh = x) :
    ∃ W : Subgroup G, ⁅W, W⁆ = W ∧ W.map σ = V ∧ W ≤ V.comap σ ∧
      W ≤ Subgroup.centralizer ({xh} : Set G) := by
  obtain ⟨W, hW, hWV, hWm⟩ := ParabPrime.exists_perfect_map_eq σ hker hV hVr
  refine ⟨W, hW, hWm, hWV, fun w hw => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  refine (commute_of_perfect_of_map_commute hker hW (y := xh) (fun w' hw' => ?_) w hw).symm
  have h1 : σ w' ∈ V := hWm ▸ Subgroup.mem_map_of_mem σ hw'
  have := Subgroup.mem_centralizer_iff.1 (hVx h1) x (Set.mem_singleton x)
  rw [hxh]
  exact this.symm

theorem exists_pSubgroup_lift [Finite G] {σ : G →* M} {p : ℕ} (hp : p.Prime) {W : Subgroup G}
    {E : Subgroup M} (hE : IsPGroup p E) (hEW : E ≤ W.map σ) :
    ∃ Eh : Subgroup G, Eh ≤ W ∧ IsPGroup p Eh ∧ Eh.map σ = E := by
  have : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := W ⊓ E.comap σ with hH
  let ψ : ↥H →* ↥E := (σ.comp H.subtype).codRestrict E fun h => h.2.2
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨w, hw, hwe⟩ := hEW e.2
    exact ⟨⟨w, hw, by show σ w ∈ E; rw [hwe]; exact e.2⟩, Subtype.ext hwe⟩
  obtain ⟨P⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hP : IsPGroup p ↥(⊤ : Subgroup ↥E) := fun x => by
    obtain ⟨k, hk⟩ := hE x.1
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have htop : (P.map ψ : Subgroup ↥E) = ⊤ :=
    (Sylow.coe_mapSurjective hψ P ▸ (P.mapSurjective hψ).is_maximal' hP le_top).symm
  refine ⟨P.map H.subtype, fun g hg => ?_, ?_, ?_⟩
  · obtain ⟨h, -, rfl⟩ := hg
    exact h.2.1
  · exact (P.isPGroup'.map H.subtype)
  · apply le_antisymm
    · rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact h.2.2
    · intro e he
      have : (⟨e, he⟩ : ↥E) ∈ P.map ψ := by rw [htop]; trivial
      obtain ⟨h, hh, hhe⟩ := this
      exact ⟨h.1, ⟨h, hh, rfl⟩, congrArg Subtype.val hhe⟩

theorem lift_core [Finite G] {σ : G →* M} (hker : σ.ker ≤ Subgroup.center G) {p : ℕ}
    (hp : p.Prime) {V E : Subgroup M} (hV : ⁅V, V⁆ = V) (hVr : V ≤ σ.range) {x : M}
    (hVx : V ≤ Subgroup.centralizer ({x} : Set M)) {xh : G} (hxh : σ xh = x) (hE : IsPGroup p E)
    (hEV : E ≤ V) :
    ∃ W Eh : Subgroup G, ⁅W, W⁆ = W ∧ W.map σ = V ∧ W ≤ V.comap σ ∧
      W ≤ Subgroup.centralizer ({xh} : Set G) ∧ Eh ≤ W ∧ IsPGroup p Eh ∧ Eh.map σ = E := by
  obtain ⟨W, hW, hWV, hWc, hWx⟩ := exists_perfect_lift hker hV hVr hVx hxh
  obtain ⟨Eh, hEW, hEp, hEm⟩ := exists_pSubgroup_lift hp hE (hWV ▸ hEV)
  exact ⟨W, Eh, hW, hWV, hWc, hWx, hEW, hEp, hEm⟩

theorem inf_ker_eq_bot_of_pGroup [Finite G] {σ : G →* M} {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card σ.ker) {Eh : Subgroup G} (hEp : IsPGroup p Eh) :
    Eh ⊓ σ.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  rintro g ⟨hgE, hgk⟩
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hEp) ⟨g, hgE⟩
  have hk' : orderOf g = p ^ k := by simpa [Subgroup.orderOf_mk] using hk
  have hdvd : orderOf g ∣ Nat.card σ.ker := by
    have := orderOf_dvd_natCard (⟨g, hgk⟩ : ↥σ.ker)
    simpa [Subgroup.orderOf_mk] using this
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simpa using hk'
  · exact absurd ((dvd_pow_self p hkpos.ne').trans (hk' ▸ hdvd)) hpk

theorem lift_core_elemAbelian [Finite G] {σ : G →* M} {p : ℕ} (hp : p.Prime)
    (hpk : ¬ p ∣ Nat.card σ.ker) {Eh : Subgroup G} (hEp : IsPGroup p Eh)
    (hEl : IsElemAbelian p (Eh.map σ)) : IsElemAbelian p Eh ∧ Nat.card Eh = Nat.card (Eh.map σ) := by
  have hinf := inf_ker_eq_bot_of_pGroup hp hpk hEp
  have hinj : Function.Injective (σ.subgroupMap Eh) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_bot]
    have h1 : σ (a : G) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.1 ha)
      simpa using this
    have : (a : G) ∈ Eh ⊓ σ.ker := ⟨a.2, h1⟩
    rw [hinf] at this
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  have hbij : Function.Bijective (σ.subgroupMap Eh) :=
    ⟨hinj, MonoidHom.subgroupMap_surjective σ Eh⟩
  let φ := MulEquiv.ofBijective (σ.subgroupMap Eh) hbij
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, (Nat.card_congr φ.toEquiv)⟩
  · apply φ.injective
    have := hEl.1.is_comm.comm ⟨σ a, a, a.2, rfl⟩ ⟨σ b, b, b.2, rfl⟩
    refine Subtype.ext ?_
    have h2 := congrArg Subtype.val this
    simpa [φ] using h2
  · have h := hEl.2 (σ x) ⟨x, hx, rfl⟩
    rw [← map_pow] at h
    have : x ^ p ∈ Eh ⊓ σ.ker := ⟨Eh.pow_mem hx p, h⟩
    rw [hinf] at this
    exact Subgroup.mem_bot.1 this

theorem center_eq_map_center {σ : G →* M} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center G) (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤) :
    Subgroup.center M = (Subgroup.center G).map σ := by
  apply le_antisymm
  · intro m hm
    obtain ⟨g, rfl⟩ := hσs m
    refine ⟨g, ?_, rfl⟩
    have hcen : ∀ h : G, ⁅h, g⁆ ∈ Subgroup.center G := by
      intro h
      refine hker ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_center_iff.1 hm (σ h)
    have hG' : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have := commutator_commutator_eq_one_of_central_aux (hcen a) (hcen b)
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    show g ∈ Subgroup.center G
    rw [Subgroup.mem_center_iff]
    intro h
    have hh : σ h ∈ (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).map σ := by
      rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective σ hσs, hM]
      trivial
    obtain ⟨c, hc, hcσ⟩ := hh
    have hk : c⁻¹ * h ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcσ, inv_mul_cancel]
    have h1 : h = c * (c⁻¹ * h) := by group
    have hgc : c * g = g * c := by
      have := Subgroup.mem_centralizer_iff.1 (hG' hc) g (Set.mem_singleton g)
      exact this.symm
    have hgk : (c⁻¹ * h) * g = g * (c⁻¹ * h) := (Subgroup.mem_center_iff.1 (hker hk) g).symm
    calc h * g = c * ((c⁻¹ * h) * g) := by rw [h1]; group
      _ = c * (g * (c⁻¹ * h)) := by rw [hgk]
      _ = (c * g) * (c⁻¹ * h) := by group
      _ = g * h := by rw [hgc]; group
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨g, rfl⟩ := hσs m
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz g]

theorem pow_mem_center_of_lift {σ : G →* M} (hker : σ.ker ≤ Subgroup.center G) {xh : G}
    {m : ℕ} (hxm : σ xh ^ m = 1) : xh ^ m ∈ Subgroup.center G :=
  hker (by rw [MonoidHom.mem_ker, map_pow, hxm])

theorem exists_lift_pow_eq_one_cover [Finite G] {σ : G →* M} (hker : σ.ker ≤ Subgroup.center G)
    {p : ℕ} (hp : p.Prime) (hpk : ¬ p ∣ Nat.card σ.ker) {x : M} (hx : x ^ p = 1)
    (hxr : x ∈ σ.range) : ∃ xh : G, σ xh = x ∧ xh ^ p = 1 := by
  obtain ⟨x0, rfl⟩ := hxr
  set c : G := x0 ^ p with hc
  have hck : c ∈ σ.ker := by rw [MonoidHom.mem_ker, hc, map_pow, hx]
  have hord : orderOf c ∣ Nat.card σ.ker := by
    have := orderOf_dvd_natCard (⟨c, hck⟩ : ↥σ.ker)
    simpa [Subgroup.orderOf_mk] using this
  have hcop : Nat.Coprime p (orderOf c) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hpk (h.trans hord)
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (orderOf c : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  set d : G := c ^ a with hd
  have hdk : d ∈ σ.ker := σ.ker.zpow_mem hck a
  have hdp : d ^ p = c := by
    have h2 : a * (p : ℤ) + (orderOf c : ℤ) * b = 1 := by rw [← hab]; ring
    calc d ^ p = c ^ (a * (p : ℤ)) := by rw [hd, ← zpow_natCast, ← zpow_mul]
      _ = c ^ (a * (p : ℤ) + (orderOf c : ℤ) * b) := by
          rw [zpow_add, zpow_mul c (orderOf c : ℤ) b, zpow_natCast, pow_orderOf_eq_one, one_zpow,
            mul_one]
      _ = c := by rw [h2, zpow_one]
  refine ⟨x0 * d⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hdk, inv_one, mul_one]
  · have hcomm : Commute x0 d⁻¹ := Subgroup.mem_center_iff.1 (hker (σ.ker.inv_mem hdk)) x0
    rw [hcomm.mul_pow, inv_pow, hdp, hc, mul_inv_cancel]

end Lift

section Core

variable {Y : Type} [Group Y]

theorem inf_centralizer_eq_map_center (L : Subgroup Y) :
    L ⊓ Subgroup.centralizer (L : Set Y) = (Subgroup.center ↥L).map L.subtype := by
  ext y
  constructor
  · rintro ⟨hyL, hy⟩
    refine ⟨⟨y, hyL⟩, ?_, rfl⟩
    show (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hy g g.2)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)

theorem exists_perfect_core_mul {L : Subgroup Y} {x : Y} (hx : x ∈ L) {W : Subgroup Y}
    (hW : ⁅W, W⁆ = W) (hWL : W ≤ L ⊔ Subgroup.centralizer (L : Set Y))
    (hWx : W ≤ Subgroup.centralizer ({x} : Set Y)) {E : Subgroup Y} (hEW : E ≤ W ⊓ L) :
    ∃ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧
      E ≤ V ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) := by
  set A : Subgroup Y := L ⊓ (W ⊔ Subgroup.centralizer (L : Set Y)) with hA
  have hCx : Subgroup.centralizer (L : Set Y) ≤ Subgroup.centralizer ({x} : Set Y) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hc y hx
  have hAx : A ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) :=
    fun a ha => ⟨ha.1, (sup_le hWx hCx) ha.2⟩
  have hcomm : ∀ j ∈ A, ∀ c ∈ Subgroup.centralizer (L : Set Y), j * c = c * j := fun j hj c hc =>
    Subgroup.mem_centralizer_iff.mp hc j hj.1
  have hWA : W ≤ A ⊔ Subgroup.centralizer (L : Set Y) := by
    intro w hw
    have h1 : w ∈ (L ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) := hWL hw
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (ToralCensus.le_normalizer_centralizer L)] at h1
    obtain ⟨l, hl, c, hc, rfl⟩ := h1
    have hlA : l ∈ A := by
      refine ⟨hl, ?_⟩
      have := Subgroup.mul_mem _
        (Subgroup.mem_sup_left hw : l * c ∈ W ⊔ Subgroup.centralizer (L : Set Y))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hc :
          c ∈ W ⊔ Subgroup.centralizer (L : Set Y)))
      simpa using this
    exact Subgroup.mul_mem_sup hlA hc
  have hWV : W ≤ perfectJoin A ⊔ Subgroup.centralizer (L : Set Y) :=
    ToralCensus.perfect_le_perfectJoin_sup hcomm hW hWA
  have hVL : perfectJoin A ≤ L := (perfectJoin_le A).trans (fun a ha => ha.1)
  refine ⟨perfectJoin A, (perfectJoin_le A).trans hAx, perfectJoin_perfect A, ?_⟩
  intro e he
  have heW : e ∈ W := (hEW he).1
  have heL : e ∈ L := (hEW he).2
  have h1 : e ∈ (perfectJoin A ⊔ Subgroup.centralizer (L : Set Y) : Subgroup Y) := hWV heW
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (hVL.trans (ToralCensus.le_normalizer_centralizer L))] at h1
  obtain ⟨v, hv, c, hc, rfl⟩ := h1
  have hcL : c ∈ L := by
    have := L.mul_mem (L.inv_mem (hVL hv)) heL
    simpa using this
  exact Subgroup.mul_mem_sup hv (show c ∈ L ⊓ Subgroup.centralizer (L : Set Y) from ⟨hcL, hc⟩)

theorem exists_perfect_core_mul_of_comp (hSch : KFactCatalogSchreier) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {x : Y}
    (hx : x ∈ L) {W : Subgroup Y} [Finite Y] (hW : ⁅W, W⁆ = W)
    (hWN : W ≤ Subgroup.normalizer (L : Set Y)) (hWx : W ≤ Subgroup.centralizer ({x} : Set Y))
    {E : Subgroup Y} (hEW : E ≤ W ⊓ L) :
    ∃ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧
      E ≤ V ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) :=
  exists_perfect_core_mul hx hW (ToralCensus.perfect_le_sup_centralizer_of_comp hSch hL htype hW hWN)
    hWx hEW

end Core

theorem isCyclic_center_SL (n : ℕ) (K : Type*) [Field K] :
    IsCyclic (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) := by
  have : NeZero (max (Fintype.card (Fin n)) 1) := ⟨by omega⟩
  exact isCyclic_of_surjective
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)).symm
    (MulEquiv.surjective _)

theorem isCyclic_center_of_cover {n : ℕ} {K : Type*} [Field K] {M : Type*} [Group M]
    {σ : Matrix.SpecialLinearGroup (Fin n) K →* M} (hσs : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊤) : IsCyclic (Subgroup.center M) := by
  have := isCyclic_center_SL n K
  rw [center_eq_map_center hσs hker hM]
  exact isCyclic_of_surjective (σ.subgroupMap (Subgroup.center _))
    (MonoidHom.subgroupMap_surjective σ _)

section LiftCover

variable {G : Type*} [Group G] {Y : Type} [Group Y] {L : Subgroup Y} {ρ : G →* ↥L}

theorem lift_core_cover [Finite G] (hρs : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center G) {p : ℕ} (hp : p.Prime) {J V E : Subgroup Y}
    (hVJ : V ≤ J) (hVL : V ≤ L) (hV : ⁅V, V⁆ = V) {x : Y}
    (hVx : V ≤ Subgroup.centralizer ({x} : Set Y)) {xh : G} (hxh : ((ρ xh : ↥L) : Y) = x)
    (hE : IsPGroup p E) (hEV : E ≤ V) :
    ∃ W Eh : Subgroup G, ⁅W, W⁆ = W ∧ W.map (L.subtype.comp ρ) = V ∧
      W ≤ (J.subgroupOf L).comap ρ ∧ W ≤ Subgroup.centralizer ({xh} : Set G) ∧ Eh ≤ W ∧
      IsPGroup p Eh ∧ Eh.map (L.subtype.comp ρ) = E := by
  have hVr : V ≤ (L.subtype.comp ρ).range := fun v hv => by
    obtain ⟨g, hg⟩ := hρs ⟨v, hVL hv⟩
    exact ⟨g, by rw [MonoidHom.comp_apply, hg]; rfl⟩
  obtain ⟨W, Eh, hW, hWV, -, hWx, hEW, hEp, hEm⟩ :=
    lift_core (σ := L.subtype.comp ρ) (ToralCensus.ker_subtype_comp_le hker) hp hV hVr hVx
      (xh := xh) (by simpa using hxh) hE hEV
  refine ⟨W, Eh, hW, hWV, fun w hw => ?_, hWx, hEW, hEp, hEm⟩
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  exact hVJ (hWV ▸ Subgroup.mem_map_of_mem _ hw)

end LiftCover

section Setup


theorem altIbA_setup (hSch : KFactCatalogSchreier) (hGA : CFSG.Open.GriessAllModelsStatement)
    {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y} (hL : IsComponentOf L ⊤)
    (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L))
    (hX : IsLieOf IdxA (↥L ⧸ Subgroup.center ↥L)) (hpar : IsParabolicTwo L J) (hJL : J ≠ L)
    (hnB : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {x : Y} (hxL : x ∈ L)
    (hfix : ∀ l ∈ L, x * l * x⁻¹ = l → l ∈ J) {W : Subgroup Y} (hW : ⁅W, W⁆ = W)
    (hWN : W ≤ Subgroup.normalizer (L : Set Y)) (hWx : W ≤ Subgroup.centralizer ({x} : Set Y))
    {E : Subgroup Y} (hEW : E ≤ W ⊓ L) (hE : IsPGroup p E) (hEc : Nat.card E = p ^ 2) :
    Odd (Nat.card (Subgroup.center ↥L)) ∧
    (∃ (n f : ℕ) (σ : Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f) →* ↥L)
        (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n (GaloisField 2 f)) (I : Set ℕ),
        3 ≤ n ∧ 1 ≤ f ∧ Function.Surjective σ ∧
        σ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 f)) ∧
        (∀ g, e (QuotientGroup.mk (σ g)) = proj n (GaloisField 2 f) g) ∧
        (∀ i ∈ I, 1 ≤ i ∧ i < n) ∧ I.Nonempty ∧ (∃ i, 1 ≤ i ∧ i < n ∧ i ∉ I) ∧
        (J.subgroupOf L).comap σ = flagStabilizer n (GaloisField 2 f) I) ∧
    ∃ V : Subgroup Y, V ≤ J ⊓ Subgroup.centralizer ({x} : Set Y) ∧ ⁅V, V⁆ = V ∧
      E ≤ V ⊔ (L ⊓ Subgroup.centralizer (L : Set Y)) ∧
      (¬ p ∣ Nat.card (Subgroup.center ↥L) → E ≤ V) := by
  have hCP : CompParabE L J := ⟨hL, htype, hpar, hJL, hnB⟩
  have hEL : E ≤ L := hEW.trans inf_le_right
  rcases exists_cover_or_sq_free hGA hCP hX with ⟨-, hno⟩ | ⟨hodd, hcover⟩
  · exact absurd hEc (hno p hp hp5 E hEL)
  · refine ⟨hodd, hcover, ?_⟩
    have hVJ : ∀ V : Subgroup Y, V ≤ L ⊓ Subgroup.centralizer ({x} : Set Y) →
        V ≤ J ⊓ Subgroup.centralizer ({x} : Set Y) := fun V hV v hv =>
      ⟨hfix v (hV hv).1 (by
        have := Subgroup.mem_centralizer_iff.1 (hV hv).2 x (Set.mem_singleton x)
        rw [this, mul_inv_cancel_right]), (hV hv).2⟩
    by_cases hpZ : p ∣ Nat.card (Subgroup.center ↥L)
    · obtain ⟨V, hVle, hV, hEV⟩ :=
        exists_perfect_core_mul_of_comp hSch hL htype hxL hW hWN hWx hEW
      exact ⟨V, hVJ V hVle, hV, hEV, fun h => absurd hpZ h⟩
    · obtain ⟨V, hVle, hV, hEV⟩ :=
        exists_perfect_core_of_comp hSch hp hL htype hpZ hxL hW hWN hWx hEW hE
      exact ⟨V, hVJ V hVle, hV, hEV.trans le_sup_left, fun _ => hEV⟩

end Setup

end EvenCentre

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb
