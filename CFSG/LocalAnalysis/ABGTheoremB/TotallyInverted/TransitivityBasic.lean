module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Walter.Transitivity.Coprime
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Statements

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec10

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_conjSub {g x : G} {X : Subgroup G} : x ∈ conjSub g X ↔ g⁻¹ * x * g ∈ X := by
  rw [conjSub, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conjSub {g x : G} {X : Subgroup G} (hx : x ∈ X) :
    g * x * g⁻¹ ∈ conjSub g X := by
  rw [mem_conjSub]
  simpa [mul_assoc] using hx

theorem conjSub_mul (g h : G) (X : Subgroup G) :
    conjSub (g * h) X = conjSub g (conjSub h X) := by
  ext x
  simp only [mem_conjSub, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem conjSub_one (X : Subgroup G) : conjSub 1 X = X := by
  ext x
  simp [mem_conjSub]

theorem conjSub_inv_conjSub (g : G) (X : Subgroup G) : conjSub g⁻¹ (conjSub g X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : G) (X : Subgroup G) : conjSub g (conjSub g⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_le_conjSub_iff {g : G} {X Y : Subgroup G} :
    conjSub g X ≤ conjSub g Y ↔ X ≤ Y := by
  constructor
  · intro h x hx
    have := h (conj_mem_conjSub (g := g) hx)
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  · intro h x hx
    rw [mem_conjSub] at hx ⊢
    exact h hx

theorem conjSub_mono {g : G} {X Y : Subgroup G} (h : X ≤ Y) : conjSub g X ≤ conjSub g Y :=
  conjSub_le_conjSub_iff.mpr h

theorem conjSub_injective (g : G) : Function.Injective (conjSub g : Subgroup G → Subgroup G) :=
  fun _ _ h => le_antisymm (conjSub_le_conjSub_iff.mp h.le) (conjSub_le_conjSub_iff.mp h.ge)

theorem conjSub_eq_self {g : G} {X : Subgroup G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    conjSub g X = X := by
  ext x
  rw [mem_conjSub]
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
  rw [inv_inv] at h
  exact h.symm

theorem le_normalizer_iff_conjSub {X : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (X : Set G) ↔ conjSub g X = X := by
  refine ⟨conjSub_eq_self, fun h => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact conj_mem_conjSub hx
  · intro hx
    rw [← h, mem_conjSub] at hx
    simpa [mul_assoc] using hx

theorem card_conjSub (g : G) (X : Subgroup G) : Nat.card (conjSub g X) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_sup (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊔ Y) = conjSub g X ⊔ conjSub g Y :=
  Subgroup.map_sup X Y _

theorem conjSub_inf (g : G) (X Y : Subgroup G) :
    conjSub g (X ⊓ Y) = conjSub g X ⊓ conjSub g Y :=
  Subgroup.map_inf_eq X Y _ (MulAut.conj g).injective

theorem conjSub_bot (g : G) : conjSub g (⊥ : Subgroup G) = ⊥ :=
  Subgroup.map_bot _

theorem conjSub_top (g : G) : conjSub g (⊤ : Subgroup G) = ⊤ := by
  ext x
  simp [mem_conjSub]

theorem conjSub_eq_bot_iff {g : G} {X : Subgroup G} : conjSub g X = ⊥ ↔ X = ⊥ :=
  ⟨fun h => conjSub_injective g (h.trans (conjSub_bot g).symm), fun h => h ▸ conjSub_bot g⟩

theorem isPGroup_conjSub {p : ℕ} {X : Subgroup G} (hX : IsPGroup p X) (g : G) :
    IsPGroup p (conjSub g X) :=
  hX.map _

theorem conjSub_centralizer_singleton (g y : G) :
    conjSub g (Subgroup.centralizer ({y} : Set G)) =
      Subgroup.centralizer ({g * y * g⁻¹} : Set G) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * y * g⁻¹ * x := by group
  · intro h
    calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * x) * g := by rw [h]
      _ = y * (g⁻¹ * x * g) := by group

theorem conjSub_normalizer (g : G) (X : Subgroup G) :
    conjSub g (Subgroup.normalizer (X : Set G)) =
      Subgroup.normalizer ((conjSub g X : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjSub, le_normalizer_iff_conjSub, le_normalizer_iff_conjSub]
  constructor
  · intro h
    calc conjSub x (conjSub g X) = conjSub g (conjSub (g⁻¹ * x * g) X) := by
          rw [← conjSub_mul, ← conjSub_mul]; congr 1; group
      _ = conjSub g X := by rw [h]
  · intro h
    calc conjSub (g⁻¹ * x * g) X = conjSub g⁻¹ (conjSub x (conjSub g X)) := by
          rw [← conjSub_mul, ← conjSub_mul]
      _ = X := by rw [h, conjSub_inv_conjSub]

theorem conjSub_centralizer (g : G) (X : Subgroup G) :
    conjSub g (Subgroup.centralizer (X : Set G)) =
      Subgroup.centralizer ((conjSub g X : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [SetLike.mem_coe, mem_conjSub] at hy
    have := h _ hy
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group
  · intro h y hy
    have := h (g * y * g⁻¹) (conj_mem_conjSub hy)
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * y := by group

noncomputable def conjSubEquiv (g : G) (X : Subgroup G) : X ≃* conjSub g X :=
  X.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

theorem subtype_comp_conjSubEquiv (g : G) (X : Subgroup G) :
    (conjSub g X).subtype.comp (conjSubEquiv g X).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp X.subtype := by
  ext x
  rfl

theorem pCoreIn_conjSub (p : ℕ) (g : G) (X : Subgroup G) :
    pCoreIn p (conjSub g X) = conjSub g (pCoreIn p X) := by
  rw [pCoreIn, ← CFSG.pCore_map_iso p (conjSubEquiv g X), Subgroup.map_map,
    subtype_comp_conjSubEquiv, ← Subgroup.map_map]
  rfl

theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (CFSG.oddCore X).map e.toMonoidHom = CFSG.oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.oddCore_normal X).map _ e.surjective,
      by rw [Subgroup.card_map_of_injective e.injective]; exact odd_card_oddCore X⟩
  · have hle : (CFSG.oddCore Y).map e.symm.toMonoidHom ≤ CFSG.oddCore X :=
      le_sSup ⟨(CFSG.oddCore_normal Y).map _ e.symm.surjective,
        by rw [Subgroup.card_map_of_injective e.symm.injective]; exact odd_card_oddCore Y⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

theorem oddCoreIn_conjSub [Finite G] (g : G) (X : Subgroup G) :
    oddCoreIn (conjSub g X) = conjSub g (oddCoreIn X) := by
  rw [oddCoreIn, ← oddCore_map_mulEquiv (conjSubEquiv g X), Subgroup.map_map,
    subtype_comp_conjSubEquiv, ← Subgroup.map_map]
  rfl

theorem mem_zpowers_of_orderOf_eq_two {x z : G} (hx : orderOf x = 2)
    (hz : z ∈ Subgroup.zpowers x) : z = 1 ∨ z = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_zero]
  · right; rw [show ((2 : ℕ) : ℤ) = 2 by norm_num, h, zpow_one]

theorem ne_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  norm_num at hx

theorem mul_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx, pow_orderOf_eq_one]

theorem inv_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_of_orderOf_eq_two hx)

theorem mem_of_sq_mem_of_odd {u : G} {A : Subgroup G} (hu : Odd (orderOf u)) (h : u ^ 2 ∈ A) :
    u ∈ A := by
  obtain ⟨m, hm⟩ := hu
  have : u = (u ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf u + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact A.pow_mem h _

theorem odd_orderOf_of_mem {K : Subgroup G} (hK : Odd (Nat.card K)) {u : G} (hu : u ∈ K) :
    Odd (orderOf u) :=
  hK.of_dvd_nat (Subgroup.orderOf_dvd_natCard K hu)

theorem eq_one_of_eq_inv_of_odd {K : Subgroup G} (hK : Odd (Nat.card K)) {u : G} (hu : u ∈ K)
    (h : u = u⁻¹) : u = 1 := by
  have h2 : u ^ 2 ∈ (⊥ : Subgroup G) := by
    rw [Subgroup.mem_bot, pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel u
  simpa using mem_of_sq_mem_of_odd (odd_orderOf_of_mem hK hu) h2

theorem odd_card_of_isPGroup {p : ℕ} [Fact p.Prime] (hp : Odd p) {K : Subgroup G} [Finite K]
    (hK : IsPGroup p K) : Odd (Nat.card K) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK
  rw [hk]
  exact hp.pow

section Setting

variable {σ : Setting G}

theorem x₃_eq : σ.x₃ = σ.x * σ.x₂ := rfl

theorem x₃_mem_T : σ.x₃ ∈ σ.T := σ.T.mul_mem σ.x_mem_T σ.x₂_mem_T

theorem xs_mem_T (i : Fin 3) : σ.xs i ∈ σ.T := by
  fin_cases i
  · exact σ.x_mem_T
  · exact σ.x₂_mem_T
  · exact x₃_mem_T

theorem mem_C_iff_commute_xs {c : G} : c ∈ σ.C ↔ ∀ i : Fin 3, c * σ.xs i = σ.xs i * c := by
  constructor
  · intro hc i
    exact ((Subgroup.mem_centralizer_iff.mp hc) _ (xs_mem_T i)).symm
  · intro h
    rw [Setting.C, Setting.T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with rfl | rfl
    · exact (h 0).symm
    · exact (h 1).symm

theorem commute_of_mem_C {c : G} (hc : c ∈ σ.C) (i : Fin 3) : c * σ.xs i = σ.xs i * c :=
  mem_C_iff_commute_xs.mp hc i

theorem C_le_Ns (i : Fin 3) : σ.C ≤ σ.Ns i := fun _ hc =>
  Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_C hc i)

theorem Ns_le_normalizer_Ps (r : ℕ) (i : Fin 3) :
    σ.Ns i ≤ Subgroup.normalizer ((σ.Ps r i : Subgroup G) : Set G) :=
  le_normalizer_map_subtype _ _

theorem C_le_normalizer_Ps (r : ℕ) (i : Fin 3) :
    σ.C ≤ Subgroup.normalizer ((σ.Ps r i : Subgroup G) : Set G) :=
  (C_le_Ns i).trans (Ns_le_normalizer_Ps r i)

theorem conjSub_Ps (r : ℕ) {g : G} {i j : Fin 3} (h : g * σ.xs j * g⁻¹ = σ.xs i) :
    conjSub g (σ.Ps r j) = σ.Ps r i := by
  rw [Setting.Ps, Setting.Ps, ← pCoreIn_conjSub, Setting.Ns, Setting.Ns,
    conjSub_centralizer_singleton, h]

theorem conjSub_Ps_of_mem_C (r : ℕ) {c : G} (hc : c ∈ σ.C) (i : Fin 3) :
    conjSub c (σ.Ps r i) = σ.Ps r i :=
  conjSub_eq_self (C_le_normalizer_Ps r i hc)

theorem normalizer_T_le_M {g : G} (hg : g ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G)) :
    g ∈ σ.M := by
  rw [Setting.M, le_normalizer_iff_conjSub, Setting.C, conjSub_centralizer,
    conjSub_eq_self hg]

theorem conjSub_C_of_mem_M {g : G} (hg : g ∈ σ.M) : conjSub g σ.C = σ.C :=
  conjSub_eq_self hg

variable [Finite G]

theorem x_ne_one (hσ : σ.IsValid) : σ.x ≠ 1 := ne_one_of_orderOf_eq_two hσ.x_order

theorem x₂_ne_one (hσ : σ.IsValid) : σ.x₂ ≠ 1 := ne_one_of_orderOf_eq_two hσ.x₂_order

theorem T_isKleinFour (hσ : σ.IsValid) : IsKleinFour σ.T := by
  refine CFSG.Wreathed.isKleinFour_closure_pair hσ.x_order hσ.x₂_order hσ.commute ?_
  rw [Subgroup.disjoint_def]
  intro z h₁ h₂
  rcases mem_zpowers_of_orderOf_eq_two hσ.x_order h₁ with h | h
  · exact h
  rcases mem_zpowers_of_orderOf_eq_two hσ.x₂_order h₂ with h' | h'
  · exact h'
  exact absurd (h.symm.trans h') hσ.x_ne_x₂

theorem mem_T_iff (hσ : σ.IsValid) {t : G} :
    t ∈ σ.T ↔ t = 1 ∨ t = σ.x ∨ t = σ.x₂ ∨ t = σ.x₃ := by
  have := T_isKleinFour hσ
  constructor
  · intro ht
    exact kleinFour_mem_cases σ.x_mem_T σ.x₂_mem_T ht (x_ne_one hσ) (x₂_ne_one hσ) hσ.x_ne_x₂
  · rintro (rfl | rfl | rfl | rfl)
    · exact σ.T.one_mem
    · exact σ.x_mem_T
    · exact σ.x₂_mem_T
    · exact x₃_mem_T

theorem exists_xs_of_mem_T (hσ : σ.IsValid) {t : G} (ht : t ∈ σ.T) (ht1 : t ≠ 1) :
    ∃ i : Fin 3, t = σ.xs i := by
  rcases (mem_T_iff hσ).mp ht with h | h | h | h
  · exact absurd h ht1
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

end Setting

section Signalizers

theorem mem_signalizersPerm_iff {H X Y U : Subgroup G} {p : ℕ} :
    U ∈ signalizersPerm H X Y p ↔ U ≤ H ∧ IsPGroup p U ∧ X ≤ Subgroup.normalizer (U : Set G) ∧
      U ⊓ X = ⊥ ∧ (U : Set G) * (Y : Set G) = (Y : Set G) * (U : Set G) := by
  simp only [signalizersPerm, signalizers, Set.mem_ofPred_eq, and_assoc]

theorem exists_mem_maximals_ge [Finite G] {𝓢 : Set (Subgroup G)} {A : Subgroup G} (hA : A ∈ 𝓢) :
    ∃ B ∈ maximals 𝓢, A ≤ B := by
  obtain ⟨B, hAB, hB⟩ := (Set.toFinite 𝓢).exists_le_maximal hA
  exact ⟨B, ⟨hB.1, fun R' hR' hBR' => le_antisymm (hB.2 hR' hBR') hBR'⟩, hAB⟩

theorem signalizersPerm_mono {H H' X Y : Subgroup G} {p : ℕ} (hHH' : H ≤ H') {U : Subgroup G}
    (hU : U ∈ signalizersPerm H X Y p) : U ∈ signalizersPerm H' X Y p := by
  rw [mem_signalizersPerm_iff] at hU ⊢
  exact ⟨hU.1.trans hHH', hU.2⟩

theorem mem_maximals_of_le {H X Y U : Subgroup G} {p : ℕ}
    (hU : U ∈ maximals (signalizersPerm ⊤ X Y p)) (hUH : U ≤ H) :
    U ∈ maximals (signalizersPerm H X Y p) := by
  refine ⟨?_, fun R' hR' hUR' => hU.2 R' (signalizersPerm_mono le_top hR') hUR'⟩
  have := hU.1
  rw [mem_signalizersPerm_iff] at this ⊢
  exact ⟨hUH, this.2⟩

theorem coe_conjSub (g : G) (X : Subgroup G) :
    ((conjSub g X : Subgroup G) : Set G) = (MulAut.conj g) '' (X : Set G) := by
  rw [conjSub, Subgroup.coe_map]
  rfl

theorem conjSub_mem_signalizersPerm {H X Y U : Subgroup G} {p : ℕ} {g : G}
    (hX : conjSub g X = X) (hY : conjSub g Y = Y) (hU : U ∈ signalizersPerm H X Y p) :
    conjSub g U ∈ signalizersPerm (conjSub g H) X Y p := by
  rw [mem_signalizersPerm_iff] at hU ⊢
  obtain ⟨hUH, hp, hXU, hUX, hperm⟩ := hU
  refine ⟨conjSub_mono hUH, isPGroup_conjSub hp g, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hX, mem_conjSub] at hx
    rw [le_normalizer_iff_conjSub, ← conjSub_mul, show x * g = g * (g⁻¹ * x * g) by group,
      conjSub_mul, conjSub_eq_self (hXU hx)]
  · rw [← hX, ← conjSub_inf, hUX, conjSub_bot]
  · rw [← hY, coe_conjSub, coe_conjSub, ← Set.image_mul, hperm, Set.image_mul]

theorem conjSub_mem_maximals {H X Y U : Subgroup G} {p : ℕ} {g : G}
    (hX : conjSub g X = X) (hY : conjSub g Y = Y) (hU : U ∈ maximals (signalizersPerm H X Y p)) :
    conjSub g U ∈ maximals (signalizersPerm (conjSub g H) X Y p) := by
  have hX' : conjSub g⁻¹ X = X := by rw [← hX, conjSub_inv_conjSub, hX]
  have hY' : conjSub g⁻¹ Y = Y := by rw [← hY, conjSub_inv_conjSub, hY]
  refine ⟨conjSub_mem_signalizersPerm hX hY hU.1, fun R' hR' hle => ?_⟩
  have h1 := conjSub_mem_signalizersPerm hX' hY' hR'
  rw [conjSub_inv_conjSub] at h1
  have h2 : U ≤ conjSub g⁻¹ R' := by
    rw [← conjSub_inv_conjSub g U]
    exact conjSub_mono hle
  have h3 := hU.2 _ h1 h2
  rw [← h3, conjSub_conjSub_inv]

end Signalizers

section Cores

theorem le_pCoreIn {p : ℕ} {K A : Subgroup G} (hAK : A ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (A : Set G)) (hA : IsPGroup p A) : A ≤ pCoreIn p K := by
  have hnormal : (A.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hnorm
  have hp : IsPGroup p (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hle : A.subgroupOf K ≤ CFSG.pCore p K := le_sSup ⟨hnormal, hp⟩
  intro a ha
  exact ⟨⟨a, hAK ha⟩, hle ha, rfl⟩

theorem isPGroup_pCoreIn (p : ℕ) (K : Subgroup G) : IsPGroup p (pCoreIn p K) :=
  CFSG.pCore_isPGroup.map _

theorem le_normalizer_pCoreIn (p : ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((pCoreIn p K : Subgroup G) : Set G) :=
  le_normalizer_map_subtype K _

variable [Finite G]

theorem le_oddCoreIn_of_hasNormalPComplement {K Z : Subgroup G}
    (hK : CFSG.HasNormalPComplement 2 K) (hZK : Z ≤ K) (hZ : Odd (Nat.card Z)) :
    Z ≤ oddCoreIn K := by
  obtain ⟨N, hN, hcop, hq⟩ := hK
  set Z' : Subgroup K := Z.subgroupOf K
  have hZ' : Odd (Nat.card Z') := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv]
  have hmap : Z'.map (QuotientGroup.mk' N) = ⊥ := by
    have h2 : IsPGroup 2 (Z'.map (QuotientGroup.mk' N)) := hq.to_subgroup _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    have hodd : Odd (Nat.card (Z'.map (QuotientGroup.mk' N))) :=
      hZ'.of_dvd_nat (Subgroup.card_map_dvd _ _)
    rw [hk] at hodd
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.mp hk
    · exact absurd hodd (by rw [pow_succ]; simp)
  have hZN : Z' ≤ N := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hmap
    exact hmap
  have hNO : N ≤ CFSG.oddCore K := le_sSup ⟨hN, Nat.coprime_two_left.mp hcop⟩
  intro z hz
  exact ⟨⟨z, hZK hz⟩, hNO (hZN hz), rfl⟩

omit [Finite G] in
theorem card_sup_mul_card_inf {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAB
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A B hAB).toEquiv
  change B.relIndex A = B.relIndex (A ⊔ B) at he
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr le_sup_right] at h1
  rw [← h1, ← he, ← h2, inf_comm]
  ring

omit [Finite G] in
theorem card_sup_dvd {A B : Subgroup G} (hAB : A ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ∣ Nat.card A * Nat.card B :=
  Dvd.intro _ (card_sup_mul_card_inf hAB)

theorem exists_conjSub_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {A K X Y : Subgroup G}
    (hA : Nat.card A = 4) (hK : Odd (Nat.card K)) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hX : IsSylowOf p X K) (hY : IsSylowOf p Y K) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ c ∈ K ⊓ Subgroup.centralizer (A : Set G), conjSub c X = Y := by
  have hsolv : Group.IsSolvable K := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hK
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    rw [hA, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr hK).pow_left 2
  set π : Set Nat.Primes := {(⟨p, Fact.out⟩ : Nat.Primes)} with hπ
  have hpi : ∀ {Z : Subgroup G}, IsPGroup p Z → CFSG.IsPiSubgroup π Z := by
    intro Z hZ q hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [hk] at hq
    have := (Nat.prime_dvd_prime_iff_eq q.2 Fact.out).mp (q.2.dvd_of_dvd_pow hq)
    rw [hπ]
    exact Set.mem_singleton_iff.mpr (Subtype.ext this)
  obtain ⟨S, hSK, hSπ, -, hXS, c, hc, hYS⟩ :=
    CFSG.Walter.Transitivity.exists_conjBy_of_coprime_action hAK hsolv hcop hX.le hY.le
      (hpi hX.isPGroup) (hpi hY.isPGroup) hAX hAY
  have hSp : IsPGroup p S := by
    rw [IsPGroup.iff_card]
    refine ⟨(Nat.card S).primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
      Nat.card_pos.ne' fun {d} hd hdS => ?_⟩
    have h := hSπ ⟨d, hd⟩ hdS
    rw [hπ] at h
    exact congrArg Subtype.val (Set.mem_singleton_iff.mp h)
  have hSX : S = X := hX.eq_of_le hXS hSK hSp
  rw [hSX] at hYS
  refine ⟨c, hc, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge hYS
  change Nat.card (conjSub c X) ≤ Nat.card Y
  rw [card_conjSub, hX.card_eq, hY.card_eq]

end Cores

section TDecomposition

variable {σ : Setting G}

theorem mem_comp {K : Subgroup G} {i : Fin 3} {u : G} :
    u ∈ comp σ K i ↔ u ∈ K ∧ σ.xs i * u = u * σ.xs i ∧
      σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹ := Iff.rfl

theorem mem_of_mem_comp {K A : Subgroup G} (hK : Odd (Nat.card K))
    (hA : ∀ k ∈ K, ∀ t ∈ σ.T, k * t * k⁻¹ * t⁻¹ ∈ A) {i : Fin 3} {u : G}
    (hu : u ∈ comp σ K i) : u ∈ A := by
  obtain ⟨huK, -, h2⟩ := hu
  have h := hA u huK _ (xs_mem_T (i + 1))
  have e : u * σ.xs (i + 1) * u⁻¹ * (σ.xs (i + 1))⁻¹ = u ^ 2 := by
    calc u * σ.xs (i + 1) * u⁻¹ * (σ.xs (i + 1))⁻¹ =
          u * (σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹)⁻¹ := by group
      _ = u ^ 2 := by rw [h2, inv_inv, pow_two]
  rw [e] at h
  exact mem_of_sq_mem_of_odd (odd_orderOf_of_mem hK huK) h

variable [Finite G]

theorem subset_mul_comp (hσ : σ.IsValid) {K : Subgroup G} (hK : Odd (Nat.card K))
    (hTK : σ.T ≤ Subgroup.normalizer (K : Set G)) :
    (K : Set G) ⊆ ((K ⊓ σ.C : Subgroup G) : Set G) * comp σ K 0 * comp σ K 1 * comp σ K 2 := by
  have := T_isKleinFour hσ
  have hdec := (four_group_T_decomposition hK hTK σ.x_mem_T σ.x₂_mem_T (x_ne_one hσ)
    (x₂_ne_one hσ) hσ.x_ne_x₂).2
  have h0 : fourInverted K σ.x σ.x₂ = comp σ K 0 := by
    ext u
    simp only [fourInverted, Set.mem_ofPred_eq, mem_comp]
    have e : σ.xs 0 = σ.x := rfl
    have e' : σ.xs (0 + 1) = σ.x₂ := rfl
    rw [e, e', mul_inv_eq_iff_eq_mul]
  have h1 : fourInverted K σ.x₂ σ.x = comp σ K 1 := by
    ext u
    simp only [fourInverted, Set.mem_ofPred_eq, mem_comp]
    have e : σ.xs 1 = σ.x₂ := rfl
    have e' : σ.xs (1 + 1) = σ.x * σ.x₂ := rfl
    rw [e, e', mul_inv_eq_iff_eq_mul]
    constructor
    · rintro ⟨hu, h2, h3⟩
      refine ⟨hu, h2, ?_⟩
      calc σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ = σ.x * (σ.x₂ * u) * σ.x₂⁻¹ * σ.x⁻¹ := by group
        _ = σ.x * u * σ.x⁻¹ := by rw [h2]; group
        _ = u⁻¹ := h3
    · rintro ⟨hu, h2, h3⟩
      refine ⟨hu, h2, ?_⟩
      calc σ.x * u * σ.x⁻¹ = σ.x * (u * σ.x₂) * σ.x₂⁻¹ * σ.x⁻¹ := by group
        _ = σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ := by rw [← h2]; group
        _ = u⁻¹ := h3
  have h2 : fourInverted K (σ.x * σ.x₂) σ.x = comp σ K 2 := by
    ext u
    simp only [fourInverted, Set.mem_ofPred_eq, mem_comp]
    have e : σ.xs 2 = σ.x * σ.x₂ := rfl
    have e' : σ.xs (2 + 1) = σ.x := rfl
    rw [e, e', mul_inv_eq_iff_eq_mul]
  rw [h0, h1, h2] at hdec
  rw [Setting.C]
  exact hdec.subset

theorem subset_inf_C_mul (hσ : σ.IsValid) {K A : Subgroup G} (hK : Odd (Nat.card K))
    (hTK : σ.T ≤ Subgroup.normalizer (K : Set G)) (hcomp : ∀ i, comp σ K i ⊆ A) :
    (K : Set G) ⊆ ((K ⊓ σ.C : Subgroup G) : Set G) * (A : Set G) := by
  intro k hk
  obtain ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, d, hd, rfl⟩ := subset_mul_comp hσ hK hTK hk
  exact ⟨a, ha, b * c * d, A.mul_mem (A.mul_mem (hcomp 0 hb) (hcomp 1 hc)) (hcomp 2 hd),
    by group⟩

theorem le_sup_of_comp_le (hσ : σ.IsValid) {K A : Subgroup G} (hK : Odd (Nat.card K))
    (hTK : σ.T ≤ Subgroup.normalizer (K : Set G)) (hcomp : ∀ i, comp σ K i ⊆ A) :
    K ≤ (K ⊓ σ.C) ⊔ A := by
  intro k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := subset_inf_C_mul hσ hK hTK hcomp hk
  exact Subgroup.mul_mem_sup ha hb

theorem le_of_comp_le_of_inf_C (hσ : σ.IsValid) {K A : Subgroup G} (hK : Odd (Nat.card K))
    (hTK : σ.T ≤ Subgroup.normalizer (K : Set G)) (hKC : K ⊓ σ.C = ⊥)
    (hcomp : ∀ i, comp σ K i ⊆ A) : K ≤ A := by
  intro k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := subset_inf_C_mul hσ hK hTK hcomp hk
  rw [hKC, SetLike.mem_coe, Subgroup.mem_bot] at ha
  dsimp only
  rw [ha, one_mul]
  exact hb

theorem subset_comp_zero (hσ : σ.IsValid) {K : Subgroup G} (hK : Odd (Nat.card K))
    (hTK : σ.T ≤ Subgroup.normalizer (K : Set G)) (hKN : K ≤ σ.N) (hKC : K ⊓ σ.C = ⊥) :
    (K : Set G) ⊆ comp σ K 0 := by
  intro k hk
  obtain ⟨_, ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩, d, hd, rfl⟩ := subset_mul_comp hσ hK hTK hk
  rw [hKC, SetLike.mem_coe, Subgroup.mem_bot] at ha
  have hxc : ∀ {u : G}, u ∈ K → σ.x * u = u * σ.x := fun hu =>
    ((σ.mem_N_iff _).mp (hKN hu)).symm
  have hc1 : c = 1 := by
    obtain ⟨hcK, hc2, hc3⟩ := hc
    apply eq_one_of_eq_inv_of_odd hK hcK
    have e : σ.xs (1 + 1) = σ.x * σ.x₂ := rfl
    have e1 : σ.xs 1 = σ.x₂ := rfl
    rw [e] at hc3
    rw [e1] at hc2
    rw [← hc3]
    calc c = σ.x * c * σ.x⁻¹ := by rw [hxc hcK]; group
      _ = σ.x * (σ.x₂ * c * σ.x₂⁻¹) * σ.x⁻¹ := by rw [hc2]; group
      _ = σ.x * σ.x₂ * c * (σ.x * σ.x₂)⁻¹ := by group
  have hd1 : d = 1 := by
    obtain ⟨hdK, -, hd3⟩ := hd
    apply eq_one_of_eq_inv_of_odd hK hdK
    have e : σ.xs (2 + 1) = σ.x := rfl
    rw [e] at hd3
    rw [← hd3, hxc hdK]
    group
  dsimp only
  rw [ha, hc1, hd1, one_mul, mul_one, mul_one]
  exact hb

theorem x_conj_of_mem_comp {K : Subgroup G} (hσ : σ.IsValid) {j : Fin 3} (hj : j ≠ 0) {u : G}
    (hu : u ∈ comp σ K j) : σ.x * u * σ.x⁻¹ = u⁻¹ := by
  obtain ⟨-, h2, h3⟩ := hu
  fin_cases j
  · exact absurd rfl hj
  · have e1 : σ.xs 1 = σ.x₂ := rfl
    have e : σ.xs ((1 : Fin 3) + 1) = σ.x * σ.x₂ := rfl
    simp only [Fin.mk_one, Fin.isValue] at h2 h3
    rw [e1] at h2
    rw [e] at h3
    rw [← h3]
    have hx2 := mul_self_of_orderOf_eq_two hσ.x₂_order
    calc σ.x * u * σ.x⁻¹ = σ.x * (σ.x₂ * u * σ.x₂⁻¹) * σ.x⁻¹ := by
          rw [h2]; group
      _ = σ.x * σ.x₂ * u * (σ.x * σ.x₂)⁻¹ := by group
  · have e : σ.xs ((2 : Fin 3) + 1) = σ.x := rfl
    simp only [Fin.reduceFinMk, Fin.isValue] at h3
    rw [e] at h3
    exact h3

end TDecomposition

end CFSG.ABGTheoremB.TotallyInverted.Sec10
