module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Statements
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_conjSub_iff {g y : G} {X : Subgroup G} : y ∈ conjSub g X ↔ g⁻¹ * y * g ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simpa [conjSub, MulAut.conj_apply] using this.symm ▸ hx
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply]; group⟩

theorem conj_mem_conjSub {g x : G} {X : Subgroup G} (hx : x ∈ X) : g * x * g⁻¹ ∈ conjSub g X :=
  mem_conjSub_iff.mpr (by simpa [mul_assoc] using hx)

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext y
  simp [mem_conjSub_iff]

theorem conjSub_conjSub (g h : G) (X : Subgroup G) :
    conjSub g (conjSub h X) = conjSub (g * h) X := by
  ext y
  simp only [mem_conjSub_iff]
  rw [show h⁻¹ * (g⁻¹ * y * g) * h = (g * h)⁻¹ * y * (g * h) by group]

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [conjSub_conjSub, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (X : Subgroup G) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [conjSub_conjSub, mul_inv_cancel, conjSub_one]

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  Subgroup.map_mono h

theorem conjSub_le_conjSub_iff {g : G} {X Y : Subgroup G} : conjSub g X ≤ conjSub g Y ↔ X ≤ Y :=
  ⟨fun h => by simpa [conjSub_inv_conjSub] using conjSub_mono (g := g⁻¹) h, conjSub_mono⟩

theorem conjSub_le_iff {g : G} {X Y : Subgroup G} : conjSub g X ≤ Y ↔ X ≤ conjSub g⁻¹ Y := by
  rw [← conjSub_le_conjSub_iff (g := g⁻¹), conjSub_inv_conjSub]

theorem conjSub_injective (g : G) : Function.Injective (conjSub g) := fun X Y h => by
  rw [← conjSub_inv_conjSub g X, h, conjSub_inv_conjSub]

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj g).injective

theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup X Y _

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext y
  simp [mem_conjSub_iff]

theorem conjSub_eq_bot_iff {g : G} {X : Subgroup G} : conjSub g X = ⊥ ↔ X = ⊥ := by
  constructor
  · intro h
    exact conjSub_injective g (h.trans (conjSub_bot g).symm)
  · rintro rfl
    exact conjSub_bot g

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem isPGroup_conjSub {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) (g : G) :
    IsPGroup p (conjSub g X) :=
  hX.map _

theorem conjSub_eq_self_iff {g : G} {X : Subgroup G} :
    conjSub g X = X ↔ g ∈ Subgroup.normalizer (X : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact conj_mem_conjSub hy
    · intro hy
      rw [← h, mem_conjSub_iff] at hy
      simpa [mul_assoc] using hy
  · intro h
    ext y
    rw [mem_conjSub_iff, h (g⁻¹ * y * g)]
    simp [mul_assoc]

theorem conjSub_eq_self_of_mem {g : G} {X : Subgroup G} (hg : g ∈ X) : conjSub g X = X :=
  conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hg)

theorem normalizer_conjSub (g : G) (X : Subgroup G) :
    Subgroup.normalizer (conjSub g X : Set G) = conjSub g (Subgroup.normalizer (X : Set G)) := by
  ext y
  rw [← conjSub_eq_self_iff, mem_conjSub_iff, ← conjSub_eq_self_iff, conjSub_conjSub]
  constructor
  · intro h
    rw [show g⁻¹ * y * g = g⁻¹ * (y * g) by group, ← conjSub_conjSub, h, conjSub_inv_conjSub]
  · intro h
    rw [show y * g = g * (g⁻¹ * y * g) by group, ← conjSub_conjSub, h]

theorem le_normalizer_conjSub {g : G} {C X : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) (hC : C ≤ Subgroup.normalizer (X : Set G)) :
    C ≤ Subgroup.normalizer (conjSub g X : Set G) := by
  rw [normalizer_conjSub, ← conjSub_eq_self_iff.mpr hg]
  exact conjSub_mono hC

theorem conjSub_centralizer_singleton (g t : G) :
    conjSub g (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc y * (g * t * g⁻¹) = g * (g⁻¹ * y * g * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = g * t * g⁻¹ * y := by group
  · intro h
    calc g⁻¹ * y * g * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹ * y) * g := by rw [h]
      _ = t * (g⁻¹ * y * g) := by group

theorem conjSub_pCoreIn (p : ℕ) (g : G) (H : Subgroup G) :
    conjSub g (pCoreIn p H) = pCoreIn p (conjSub g H) := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj g).injective
  set e : H ≃* conjSub g H := H.equivMapOfInjective f hf
  have hcomm : (conjSub g H).subtype.comp e.toMonoidHom = f.comp H.subtype := by
    ext h
    rfl
  rw [pCoreIn, pCoreIn, ← CFSG.pCore_map_iso p e, Subgroup.map_map, hcomm, conjSub,
    Subgroup.map_map]

theorem mem_normalizer_of_conj_mem [Finite G] {g : G} {X : Subgroup G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  rw [← conjSub_eq_self_iff]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSub])
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

theorem isSylowOf_conjSub [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (h : IsSylowOf p P K) (g : G) : IsSylowOf p (conjSub g P) (conjSub g K) :=
  isSylowOf_of_card (conjSub_mono h.le) (by rw [card_conjSub, card_conjSub, h.card_eq])

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreIn p H) :=
  CFSG.pCore_isPGroup.map H.subtype

theorem le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreIn p H : Set G) :=
  CFSG.ABGTheoremB.le_normalizer_map_subtype H (CFSG.pCore p H)

theorem mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  Subgroup.inf_normalizer_le_normalizer_sup A B ⟨hA, hB⟩

theorem le_normalizer_sup {C A B : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun _ hc => mem_normalizer_sup (hA hc) (hB hc)

theorem mul_comm_of_le_normalizer {C X : Subgroup G}
    (h : C ≤ Subgroup.normalizer (X : Set G)) : (X : Set G) * C = C * X :=
  (Subgroup.set_mul_normalizer_comm (C : Set G) X h).symm

theorem exists_le_mem_maximals [Finite G] {𝓢 : Set (Subgroup G)} {X : Subgroup G}
    (hX : X ∈ 𝓢) : ∃ Y ∈ maximals 𝓢, X ≤ Y := by
  obtain ⟨Y, hXY, hY⟩ := (Set.toFinite 𝓢).exists_le_maximal hX
  exact ⟨Y, ⟨hY.1, fun R hR hYR => le_antisymm (hY.2 hR hYR) hYR⟩, hXY⟩

theorem conjSub_mem_maximals {𝓢 : Set (Subgroup G)} {g : G}
    (h₁ : ∀ U ∈ 𝓢, conjSub g U ∈ 𝓢) (h₂ : ∀ U ∈ 𝓢, conjSub g⁻¹ U ∈ 𝓢) {U : Subgroup G}
    (hU : U ∈ maximals 𝓢) : conjSub g U ∈ maximals 𝓢 := by
  refine ⟨h₁ U hU.1, fun R hR hUR => ?_⟩
  have h := hU.2 (conjSub g⁻¹ R) (h₂ R hR) (by rwa [← conjSub_le_iff])
  rw [← h, conjSub_conjSub_inv]

theorem conjSub_mem_signalizersPerm {H X Y U : Subgroup G} {p : ℕ} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G))
    (hU : U ∈ signalizersPerm H X Y p) : conjSub g U ∈ signalizersPerm (conjSub g H) X Y p := by
  obtain ⟨⟨hUH, hUp, hXU, hUX⟩, hperm⟩ := hU
  refine ⟨⟨conjSub_mono hUH, isPGroup_conjSub hUp g, le_normalizer_conjSub hX hXU, ?_⟩, ?_⟩
  · rw [← conjSub_eq_self_iff.mpr hX, ← conjSub_inf, hUX, conjSub_bot]
  · have hY' : ∀ y : G, y ∈ Y ↔ g⁻¹ * y * g ∈ Y := by
      intro y
      rw [← mem_conjSub_iff, conjSub_eq_self_iff.mpr hY]
    have key : ∀ {A B : Subgroup G}, (A : Set G) * B = B * A →
        conjSub g B = B → (conjSub g A : Set G) * conjSub g B ⊆ conjSub g B * conjSub g A := by
      intro A B hAB _ z hz
      obtain ⟨u, hu, c, hc, rfl⟩ := hz
      rw [SetLike.mem_coe, mem_conjSub_iff] at hu hc
      have hmem : (g⁻¹ * u * g) * (g⁻¹ * c * g) ∈ (A : Set G) * B := ⟨_, hu, _, hc, rfl⟩
      rw [hAB] at hmem
      obtain ⟨c', hc', u', hu', he⟩ := hmem
      have he : c' * u' = (g⁻¹ * u * g) * (g⁻¹ * c * g) := he
      refine ⟨g * c' * g⁻¹, conj_mem_conjSub hc', g * u' * g⁻¹, conj_mem_conjSub hu', ?_⟩
      calc g * c' * g⁻¹ * (g * u' * g⁻¹) = g * (c' * u') * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * (g⁻¹ * c * g)) * g⁻¹ := by rw [he]
        _ = u * c := by group
    have hYg : conjSub g Y = Y := conjSub_eq_self_iff.mpr hY
    have h₁ := key hperm hYg
    rw [hYg] at h₁
    refine Set.Subset.antisymm h₁ ?_
    intro z hz
    obtain ⟨c, hc, u, hu, rfl⟩ := hz
    rw [SetLike.mem_coe, mem_conjSub_iff] at hu
    have hmem : (g⁻¹ * c * g) * (g⁻¹ * u * g) ∈ (Y : Set G) * U :=
      ⟨_, (hY' c).mp hc, _, hu, rfl⟩
    rw [← hperm] at hmem
    obtain ⟨u', hu', c', hc', he⟩ := hmem
    have he : u' * c' = (g⁻¹ * c * g) * (g⁻¹ * u * g) := he
    refine ⟨g * u' * g⁻¹, conj_mem_conjSub hu', g * c' * g⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← hYg]
      exact conj_mem_conjSub hc'
    · calc g * u' * g⁻¹ * (g * c' * g⁻¹) = g * (u' * c') * g⁻¹ := by group
        _ = g * ((g⁻¹ * c * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [he]
        _ = c * u := by group

theorem conjSub_mem_maximals_signalizersPerm {X Y U : Subgroup G} {p : ℕ} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G))
    (hU : U ∈ maximals (signalizersPerm ⊤ X Y p)) :
    conjSub g U ∈ maximals (signalizersPerm ⊤ X Y p) := by
  refine conjSub_mem_maximals (fun V hV => ?_) (fun V hV => ?_) hU
  · simpa [conjSub_top] using conjSub_mem_signalizersPerm hX hY hV
  · simpa [conjSub_top] using
      conjSub_mem_signalizersPerm (Subgroup.inv_mem _ hX) (Subgroup.inv_mem _ hY) hV

section Setting

variable {σ : Setting G}

theorem xs_mem_T (i : Fin 3) : σ.xs i ∈ σ.T := by
  match i with
  | 0 => exact σ.x_mem_T
  | 1 => exact σ.x₂_mem_T
  | 2 => exact σ.T.mul_mem σ.x_mem_T σ.x₂_mem_T

theorem C_le_Ns (i : Fin 3) : σ.C ≤ σ.Ns i := fun _ hc =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hc) _ (xs_mem_T i)).symm

theorem C_le_normalizer_Ps (r : ℕ) (i : Fin 3) :
    σ.C ≤ Subgroup.normalizer (σ.Ps r i : Set G) :=
  (C_le_Ns i).trans (le_normalizer_pCoreIn r _)

theorem isPGroup_T [Finite G] (hσ : σ.IsValid) : IsPGroup 2 σ.T :=
  σ.S.isPGroup'.to_le (σ.T_le_S hσ)

theorem inf_T_eq_bot [Finite G] (hσ : σ.IsValid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup G} (hX : IsPGroup p X) : X ⊓ σ.T = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne p 2 hp2 X σ.T hX (isPGroup_T hσ))

end Setting

section Data

variable [Finite G] {σ : Setting G} {r : ℕ}

theorem a_mem_normalizer_T (Δ : Data σ r) : Δ.a ∈ Subgroup.normalizer (σ.T : Set G) := by
  apply mem_normalizer_of_conj_mem
  have key : Subgroup.closure ({σ.x, σ.x₂} : Set G) ≤
      σ.T.comap (MulAut.conj Δ.a).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · have h := Δ.a_cycle 0
      change Δ.a * σ.x * Δ.a⁻¹ ∈ σ.T
      rw [show Δ.a * σ.x * Δ.a⁻¹ = σ.xs 1 from h]
      exact xs_mem_T 1
    · have h := Δ.a_cycle 1
      change Δ.a * σ.x₂ * Δ.a⁻¹ ∈ σ.T
      rw [show Δ.a * σ.x₂ * Δ.a⁻¹ = σ.xs 2 from h]
      exact xs_mem_T 2
  intro t ht
  exact key ht

theorem a_mem_normalizer_C (Δ : Data σ r) : Δ.a ∈ Subgroup.normalizer (σ.C : Set G) :=
  Δ.a_mem

theorem C_le_normalizer_R (Δ : Data σ r) (i : Fin 3) :
    σ.C ≤ Subgroup.normalizer (R Δ i : Set G) :=
  le_normalizer_sup (Δ.Q_C i).1 (C_le_normalizer_Ps r i)

theorem C_le_normalizer_Rs (Δ : Data σ r) (i : Fin 3) :
    σ.C ≤ Subgroup.normalizer (Rs Δ i : Set G) :=
  le_normalizer_sup (Δ.Q_C i).2 (C_le_normalizer_Ps r i)

theorem conjSub_R (Δ : Data σ r) (i : Fin 3) : conjSub Δ.a (R Δ i) = R Δ (i + 1) := by
  rw [R, R, conjSub_sup, (Δ.Q_conj i).1, Δ.P_conj i]

theorem conjSub_Rs (Δ : Data σ r) (i : Fin 3) : conjSub Δ.a (Rs Δ i) = Rs Δ (i + 1) := by
  rw [Rs, Rs, conjSub_sup, (Δ.Q_conj i).2, Δ.P_conj i]

theorem R_mem_maximals (Δ : Data σ r) (i : Fin 3) :
    R Δ i ∈ maximals (signalizers (σ.Ns i) σ.C r) := by
  rw [Δ.lemma71 i]
  split_ifs with h
  · exact Or.inl (sup_comm _ _)
  · rw [R, (Δ.Q_trivial h i).1, bot_sup_eq]
    rfl

theorem Rs_mem_maximals (Δ : Data σ r) (i : Fin 3) :
    Rs Δ i ∈ maximals (signalizers (σ.Ns i) σ.C r) := by
  rw [Δ.lemma71 i]
  split_ifs with h
  · exact Or.inr (sup_comm _ _)
  · rw [Rs, (Δ.Q_trivial h i).2, bot_sup_eq]
    rfl

end Data

end CFSG.ABGTheoremB.TotallyInverted.Sec11
