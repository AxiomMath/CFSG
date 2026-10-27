module

public import CFSG.LocalAnalysis.EvenBN.G2.Data
public import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Centr
public import CFSG.Quasithin.Background.SmithB45G2Out

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification
open scoped commutatorElement

theorem exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr (h x hx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ, Set.ncard_pair zero_ne_one] at h1
  omega

theorem units_eq_one_of_sq_eq_one {K : Type} [Field K] [CharP K 2] {t : Kˣ} (h : t ^ 2 = 1) :
    t = 1 := by
  have h' : (t : K) * t = 1 := by
    rw [← Units.val_mul, ← sq, h, Units.val_one]
  exact Units.ext (UnbalancedCatalog.eq_one_of_mul_self_eq_one_two h')

theorem exists_units_sq_eq {K : Type} [Field K] [CharP K 2] [Finite K] (t : Kˣ) :
    ∃ s : Kˣ, s ^ 2 = t := by
  set s₀ := (frobeniusEquiv K 2).symm (t : K) with hs₀
  have hsq : s₀ ^ 2 = t := by
    have := frobenius_apply_frobeniusEquiv_symm K 2 (t : K)
    rwa [frobenius_def, ← hs₀] at this
  have hs₀0 : s₀ ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hsq
    exact t.ne_zero hsq.symm
  exact ⟨Units.mk0 s₀ hs₀0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hsq])⟩

theorem card_le_cube_of_injective {G K : Type*} [Group G] [Finite K] {A : Subgroup G}
    (φ : A → K × K × K) (hφ : Function.Injective φ) : Nat.card A ≤ Nat.card K ^ 3 := by
  calc Nat.card A ≤ Nat.card (K × K × K) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card K ^ 3 := by rw [Nat.card_prod, Nat.card_prod]; ring

theorem add_mem_zero_delta {K : Type} [Field K] [CharP K 2] {Δ s s' : K} (hs : s = 0 ∨ s = Δ)
    (hs' : s' = 0 ∨ s' = Δ) : s + s' = 0 ∨ s + s' = Δ := by
  rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
  · exact Or.inl (add_zero 0)
  · exact Or.inr (zero_add _)
  · exact Or.inr (add_zero _)
  · exact Or.inl (CharTwo.add_self_eq_zero _)

theorem eq_of_mem_zero_delta {K : Type} [Field K] [CharP K 2] {Δ ω s s' t t' : K}
    (hΔ : Δ ≠ 0) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (hs : s = 0 ∨ s = Δ) (hs' : s' = 0 ∨ s' = Δ)
    (ht : t = 0 ∨ t = Δ) (ht' : t' = 0 ∨ t' = Δ) (h : t + ω * s = t' + ω * s') :
    s = s' ∧ t = t' := by
  have hτ : t + t' = ω * (s + s') := by linear_combination (norm := char2_ring) h
  rcases add_mem_zero_delta hs hs' with hσ | hσ
  · rw [hσ, mul_zero] at hτ
    exact ⟨CharTwo.add_eq_zero.1 hσ, CharTwo.add_eq_zero.1 hτ⟩
  · exfalso
    rw [hσ] at hτ
    rcases add_mem_zero_delta ht ht' with h0 | h0
    · exact mul_ne_zero hω0 hΔ (hτ ▸ h0)
    · have : (ω - 1) * Δ = 0 := by linear_combination hτ.symm.trans h0
      exact hω1 (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hΔ))

theorem commutator_sup_le_of_comm {G : Type*} [Group G] {N A : Subgroup G}
    (hAN : A ≤ normalizer (N : Set G)) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ⁅N ⊔ A, N ⊔ A⁆ ≤ N := by
  rw [commutator_le]
  intro x hx y hy
  obtain ⟨n₁, hn₁, a₁, ha₁, rfl⟩ := Common.exists_mul_of_le_normalizer hAN x hx
  obtain ⟨n₂, hn₂, a₂, ha₂, rfl⟩ := Common.exists_mul_of_le_normalizer hAN y hy
  have e : ⁅n₁ * a₁, n₂ * a₂⁆ = n₁ * (a₁ * n₂ * a₁⁻¹) * (a₁ * a₂ * a₁⁻¹ * a₂⁻¹) *
      (a₂ * n₁⁻¹ * a₂⁻¹) * n₂⁻¹ := by
    rw [commutatorElement_def]
    group
  have h1 : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ = 1 := by
    rw [hA a₁ ha₁ a₂ ha₂]
    group
  rw [e, h1, mul_one]
  refine mul_mem (mul_mem (mul_mem hn₁ ((mem_normalizer_iff.1 (hAN ha₁) n₂).1 hn₂))
    ((mem_normalizer_iff.1 (hAN ha₂) _).1 (inv_mem hn₁))) (inv_mem hn₂)

theorem mem_normalizer_sup {G : Type*} [Group G] {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ normalizer (H₁ : Set G)) (h₂ : g ∈ normalizer (H₂ : Set G)) :
    g ∈ normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  have key : ∀ {k : G}, k ∈ normalizer (H₁ : Set G) → k ∈ normalizer (H₂ : Set G) →
      (H₁ ⊔ H₂).map (MulAut.conj k).toMonoidHom ≤ H₁ ⊔ H₂ := fun {k} hk₁ hk₂ => by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hk₁ x).1 hx
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hk₂ x).1 hx
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key h₁ h₂ ⟨x, hx, rfl⟩
  · intro hx
    have := key (inv_mem h₁) (inv_mem h₂) ⟨_, hx, rfl⟩
    simpa [mul_assoc] using this

theorem le_normalizer_commutator {G : Type*} [Group G] (H : Subgroup G) :
    H ≤ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_conj_mem fun h hh x hx => ?_
  have : ⁅H, H⁆.map (MulAut.conj h).toMonoidHom ≤ ⁅H, H⁆ := by
    rw [map_commutator]
    have hle : H.map (MulAut.conj h).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hh hy) (inv_mem hh)
    exact commutator_mono hle hle
  exact this ⟨x, hx, rfl⟩

@[expose] noncomputable def rankThompson {G : Type*} [Group G] [Finite G] (P : Subgroup G) :
    Subgroup G :=
  ⨆ (A : Subgroup G) (_ : A ≤ P ∧ IsMulCommutative A ∧
    CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 P), A

theorem isElemAbelian_of_isElementaryAbelian {G : Type*} [Group G] {E : Subgroup G}
    (h : CFSG.IsElementaryAbelian 2 E) : CFSG.Open.IsElemAbelian 2 E :=
  CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr h

theorem isElemAbelian_map_conj {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) (g : G) :
    CFSG.Open.IsElemAbelian 2 (E.map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (E.map (MulAut.conj g).toMonoidHom) = Nat.card E :=
  ⟨SectionRank.isElemAbelian_map hE _,
    card_map_of_injective (MulAut.conj g).injective⟩

theorem exists_ne_ne {K : Type} [Field K] [Finite K] (hK : 3 ≤ Nat.card K) (a b : K) :
    ∃ s : K, s ≠ a ∧ s ≠ b := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ {a, b} := fun x _ => by
    by_cases hx : x = a
    · exact Or.inl hx
    · exact Or.inr (h x hx)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_univ] at h1
  have h2 := Set.ncard_insert_le a ({b} : Set K)
  rw [Set.ncard_singleton] at h2
  omega

theorem commutatorElement_mem_of_mem_normalizer {G : Type*} [Group G] {E : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (E : Set G)) (hx : x ∈ E) : ⁅g, x⁆ ∈ E := by
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.1 hg x).1 hx) (inv_mem hx)

theorem mem_map_conj_iff {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem isElementaryAbelian_map_conj {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.IsElementaryAbelian 2 E) (g : G) :
    CFSG.IsElementaryAbelian 2 (E.map (MulAut.conj g).toMonoidHom) := by
  refine isElementaryAbelian_of_forall (fun x hx y hy => ?_) fun x hx => ?_
  · obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩))
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, ← sq, CFSG.elemPow_eq_one_of_isElementaryAbelian a ha, map_one]

theorem le_or_le_of_subset_union {G : Type*} [Group G] {E A B : Subgroup G}
    (h : ∀ x ∈ E, x ∈ A ∨ x ∈ B) : E ≤ A ∨ E ≤ B := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨x, hxE, hxA⟩, ⟨y, hyE, hyB⟩⟩ := And.intro (Set.not_subset.1 hne.1)
    (Set.not_subset.1 hne.2)
  have hxB : x ∈ B := (h x hxE).resolve_left hxA
  have hyA : y ∈ A := (h y hyE).resolve_right hyB
  rcases h (x * y) (mul_mem hxE hyE) with hxy | hxy
  · exact hxA (by simpa using mul_mem hxy (inv_mem hyA))
  · exact hyB (by simpa using mul_mem (inv_mem hxB) hxy)

@[expose] def ElemModulo {G : Type*} [Group G] (N E : Subgroup G) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, x * x ∈ N ∧ ⁅x, y⁆ ∈ N

namespace Model


variable {K : Type} [Field K] [CharP K 2]

theorem coords_of_commutator_eq_one {A B C D E F a b c d e f : K}
    (h : ⁅g2N A B C D E F, g2N a b c d e f⁆ = 1) :
    A * b + B * a = 0 ∧ A ^ 2 * b + B * a ^ 2 = 0 ∧
      A ^ 3 * b + A ^ 2 * B * a + A ^ 2 * a * b + A ^ 2 * c + A * B * a ^ 2 + A * a ^ 2 * b +
        A * d + B * a ^ 3 + C * a ^ 2 + D * a = 0 ∧
      A ^ 2 * a * b ^ 2 + A ^ 2 * b * c + A * B ^ 2 * a ^ 2 + A * B * a ^ 2 * b + A * b * d +
        A * c ^ 2 + B ^ 2 * a ^ 3 + B * C * a ^ 2 + B * D * a + B * e + C ^ 2 * a + C * d +
        D * c + E * b = 0 := by
  rw [g2N_commutator_coords, ← g2N_zero] at h
  obtain ⟨-, -, h3, h4, h5, h6⟩ := g2N_injective h
  exact ⟨h3, h4, h5, h6⟩

theorem coords_of_commutator_mem_U {A B C D E F a b c d e f : K}
    (h : ⁅g2N A B C D E F, g2N a b c d e f⁆ ∈ U K) :
    A * b + B * a = 0 ∧ A ^ 2 * b + B * a ^ 2 = 0 ∧
      A ^ 3 * b + A ^ 2 * B * a + A ^ 2 * a * b + A ^ 2 * c + A * B * a ^ 2 + A * a ^ 2 * b +
        A * d + B * a ^ 3 + C * a ^ 2 + D * a = 0 := by
  rw [g2N_commutator_coords, g2N_mem_U_iff] at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem coords_of_commutator_mem_Y {A B C D E F a b c d e f : K}
    (h : ⁅g2N A B C D E F, g2N a b c d e f⁆ ∈ Y K) :
    A * b + B * a = 0 ∧ A ^ 2 * b + B * a ^ 2 = 0 := by
  rw [g2N_commutator_coords, g2N_mem_Y_iff] at h
  exact ⟨h.2.2.1, h.2.2.2⟩

theorem S_inf_centralizer_S : S K ⊓ centralizer (S K : Set (ModGL .G2 K)) = U K := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
    have key : ∀ a b c d e f : K, ⁅g2N A B C D E F, g2N a b c d e f⁆ = 1 := fun a b c d e f =>
      commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 hc _ (mem_S.2 ⟨a, b, c, d, e, f, rfl⟩)).symm
    obtain ⟨hB, -, -, hC⟩ := coords_of_commutator_eq_one (key 1 0 0 0 0 0)
    obtain ⟨hA, -, -, hE⟩ := coords_of_commutator_eq_one (key 0 1 0 0 0 0)
    obtain ⟨-, -, -, hD⟩ := coords_of_commutator_eq_one (key 0 0 1 0 0 0)
    simp at hB hA
    subst hA hB
    simp at hC hE hD
    subst hC hD hE
    exact g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro x hx
    refine ⟨U_le_S hx, mem_centralizer_iff.2 fun y hy => ?_⟩
    obtain ⟨f, hf⟩ := mem_rootSubgroup.1 hx
    rw [← hf]
    exact (commute_pinnedX_c_of_mem_posUnipotent f hy).eq.symm

theorem U_le_D : U K ≤ Model.D K := fun _ hx => F_le_D (X_le_F (Y_le_X (U_le_Y hx)))

theorem Y_le_M : Y K ≤ M K := fun _ hx => F_le_M (X_le_F (Y_le_X hx))

theorem Y_le_D : Y K ≤ Model.D K := fun _ hx => F_le_D (X_le_F (Y_le_X hx))

theorem commute_of_mem_U {x y : ModGL .G2 K} (hx : x ∈ U K) (hy : y ∈ S K) : y * x = x * y := by
  obtain ⟨f, rfl⟩ := mem_rootSubgroup.1 hx
  exact (commute_pinnedX_c_of_mem_posUnipotent f hy).eq.symm

theorem D_inf_centralizer_D :
    Model.D K ⊓ centralizer (Model.D K : Set (ModGL .G2 K)) = U K := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hx
    have key : ∀ b c d e f : K, ⁅g2N 0 B C D E F, g2N 0 b c d e f⁆ = 1 := fun b c d e f =>
      commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 hc _ (g2N_mem_D_iff.2 rfl)).symm
    obtain ⟨-, -, -, hE⟩ := coords_of_commutator_eq_one (key 1 0 0 0 0)
    obtain ⟨-, -, -, hD⟩ := coords_of_commutator_eq_one (key 0 1 0 0 0)
    obtain ⟨-, -, -, hC⟩ := coords_of_commutator_eq_one (key 0 0 1 0 0)
    obtain ⟨-, -, -, hB⟩ := coords_of_commutator_eq_one (key 0 0 0 1 0)
    simp at hB hC hD hE
    subst hB hC hD hE
    exact g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro x hx
    exact ⟨U_le_D hx, mem_centralizer_iff.2 fun y hy => commute_of_mem_U hx (D_le_S hy)⟩

theorem closure_sq_D : closure {z | ∃ g ∈ Model.D K, z = g ^ 2} = U K := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hg
    rw [SetLike.mem_coe, sq, g2N_mul_self, g2N_mem_U_iff]
    simp
  · intro x hx
    obtain ⟨f, rfl⟩ := mem_U.1 hx
    refine subset_closure ⟨g2N 0 1 0 0 f 0, g2N_mem_D_iff.2 rfl, ?_⟩
    rw [sq, g2N_mul_self]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_b_3ab (f : K) :
    ⁅g2N (0 : K) 1 0 0 0 0, g2N 0 0 0 0 f 0⁆ = g2N 0 0 0 0 0 f := by
  rw [g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_a_2ab (e : K) :
    ⁅g2N e (0 : K) 0 0 0 0, g2N 0 0 0 1 0 0⁆ = g2N 0 0 0 0 e 0 := by
  rw [g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_ab_2ab (f : K) :
    ⁅g2N (0 : K) 0 1 0 0 0, g2N 0 0 0 f 0 0⁆ = g2N 0 0 0 0 0 f := by
  rw [g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_D : ⁅Model.D K, Model.D K⁆ = U K := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hx
    obtain ⟨b, c, d, e, f, rfl⟩ := mem_D.1 hy
    rw [g2N_commutator_coords, g2N_mem_U_iff]
    simp
  · intro x hx
    obtain ⟨f, rfl⟩ := mem_U.1 hx
    rw [← commutator_b_3ab]
    exact commutator_mem_commutator (g2N_mem_D_iff.2 rfl) (g2N_mem_D_iff.2 rfl)

omit
  [CharP K 2] in
theorem U_le_of_forall {T : Subgroup (ModGL .G2 K)} (h : ∀ f : K, g2N 0 0 0 0 0 f ∈ T) :
    U K ≤ T := by
  intro x hx
  obtain ⟨f, rfl⟩ := mem_U.1 hx
  exact h f

theorem Y_le_of_forall {T : Subgroup (ModGL .G2 K)} (he : ∀ e : K, g2N 0 0 0 0 e 0 ∈ T)
    (hf : ∀ f : K, g2N 0 0 0 0 0 f ∈ T) : Y K ≤ T := by
  rintro _ ⟨e, f, rfl⟩
  have h : g2N (0 : K) 0 0 0 e f = g2N 0 0 0 0 e 0 * g2N 0 0 0 0 0 f := by
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (he e) (hf f)

theorem F_le_of_forall {T : Subgroup (ModGL .G2 K)} {ω : K} (hω1 : ω ≠ 1)
    (hY : Y K ≤ T) (h1 : ∀ t : K, ∃ e f : K, g2N 0 0 t t e f ∈ T)
    (h2 : ∀ t : K, ∃ e f : K, g2N 0 0 t (ω * t) e f ∈ T) : Model.F K ≤ T := by
  have strip : ∀ c d : K, (∃ e f : K, g2N 0 0 c d e f ∈ T) → g2N 0 0 c d 0 0 ∈ T := by
    rintro c d ⟨e, f, hT⟩
    have hy : g2N (0 : K) 0 0 0 e f ∈ T := hY ⟨e, f, rfl⟩
    have h : g2N (0 : K) 0 c d 0 0 = g2N 0 0 c d e f * g2N 0 0 0 0 e f := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
    rw [h]
    exact mul_mem hT hy
  have hω : ω + 1 ≠ 0 := fun h => hω1 ((CharTwo.add_eq_zero).1 h)
  have hv : ∀ s : K, g2N 0 0 0 s 0 0 ∈ T := by
    intro s
    have hts : s / (ω + 1) + ω * (s / (ω + 1)) = s := by
      field_simp
      ring
    have hprod : g2N 0 0 (s / (ω + 1)) (s / (ω + 1)) 0 0 *
        g2N 0 0 (s / (ω + 1)) (ω * (s / (ω + 1))) 0 0 =
          g2N 0 0 0 s 0 (s / (ω + 1) * (s / (ω + 1))) := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N (by ring) (by ring) (by char2_ring) (by linear_combination hts)
        (by ring) (by ring)
    have hm := mul_mem (strip _ _ (h1 (s / (ω + 1)))) (strip _ _ (h2 (s / (ω + 1))))
    rw [hprod] at hm
    exact strip _ _ ⟨0, _, hm⟩
  have hu : ∀ c : K, g2N 0 0 c 0 0 0 ∈ T := by
    intro c
    have hprod : g2N 0 0 c c 0 0 * g2N 0 0 0 c 0 0 = g2N 0 0 c 0 0 0 := by
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
    rw [← hprod]
    exact mul_mem (strip _ _ (h1 c)) (hv c)
  rintro _ ⟨c, d, e, f, rfl⟩
  have h : g2N (0 : K) 0 c d e f = g2N 0 0 c 0 0 0 * g2N 0 0 0 d 0 0 * g2N 0 0 0 0 e f := by
    rw [g2N_mul_coords, g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mul_mem (hu c) (hv d)) (hY ⟨e, f, rfl⟩)

theorem M_inf_centralizer_M : M K ⊓ centralizer (M K : Set (ModGL .G2 K)) = Y K := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hx
    have key : ∀ a c d e f : K, ⁅g2N A 0 C D E F, g2N a 0 c d e f⁆ = 1 := fun a c d e f =>
      commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 hc _ (g2N_mem_M_iff.2 rfl)).symm
    obtain ⟨-, -, h1e, h1f⟩ := coords_of_commutator_eq_one (key 1 0 0 0 0)
    obtain ⟨-, -, h2e, -⟩ := coords_of_commutator_eq_one (key 0 1 0 0 0)
    simp at h1f h2e
    subst h1f h2e
    simp at h1e
    subst h1e
    exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩
  · intro x hx
    refine ⟨Y_le_M hx, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact (mem_centralizer_iff.1
      (AS81.G2.g2ShortParabolicRadical_le_centralizer hy) x hx).symm

theorem closure_sq_M : closure {z | ∃ g ∈ M K, z = g ^ 2} = Y K := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hg
    rw [SetLike.mem_coe, sq, g2N_mul_self, g2N_mem_Y_iff]
    simp
  · refine Y_le_of_forall (fun e => subset_closure ⟨g2N 1 0 0 e 0 0, g2N_mem_M_iff.2 rfl, ?_⟩)
      fun f => subset_closure ⟨g2N 0 0 1 f 0 0, g2N_mem_M_iff.2 rfl, ?_⟩
    all_goals
      rw [sq, g2N_mul_self]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_M : ⁅M K, M K⁆ = Y K := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hx
    obtain ⟨a, c, d, e, f, rfl⟩ := mem_M.1 hy
    rw [g2N_commutator_coords, g2N_mem_Y_iff]
    simp
  · refine Y_le_of_forall (fun e => ?_) fun f => ?_
    · rw [← commutator_a_2ab]
      exact commutator_mem_commutator (g2N_mem_M_iff.2 rfl) (g2N_mem_M_iff.2 rfl)
    · rw [← commutator_ab_2ab]
      exact commutator_mem_commutator (g2N_mem_M_iff.2 rfl) (g2N_mem_M_iff.2 rfl)

theorem mem_center_S_iff {x : S K} : x ∈ center (S K) ↔ (x : ModGL .G2 K) ∈ U K := by
  rw [← S_inf_centralizer_S]
  constructor
  · intro hx
    exact ⟨x.2, mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (mem_center_iff.1 hx ⟨y, hy⟩)⟩
  · rintro ⟨-, hc⟩
    exact mem_center_iff.2 fun y => Subtype.ext (mem_centralizer_iff.1 hc y y.2)

theorem mem_upperCentralSeries_two_iff [Finite K] (hK : 4 ≤ Nat.card K) {x : S K} :
    x ∈ Subgroup.upperCentralSeries (S K) 2 ↔ (x : ModGL .G2 K) ∈ Y K := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  simp only [Subgroup.upperCentralSeries_one, mem_center_S_iff, commutatorElement_def,
    coe_mul, coe_inv]
  obtain ⟨x, hx⟩ := x
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  constructor
  · intro h
    have key : ∀ a b c d e f : K, ⁅g2N A B C D E F, g2N a b c d e f⁆ ∈ U K :=
      fun a b c d e f => by
        rw [commutatorElement_def]
        exact h ⟨_, mem_S.2 ⟨a, b, c, d, e, f, rfl⟩⟩
    obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    obtain ⟨hB, -, h1⟩ := coords_of_commutator_mem_U (key 1 0 0 0 0 0)
    obtain ⟨hA, -, -⟩ := coords_of_commutator_mem_U (key 0 1 0 0 0 0)
    simp at hA hB
    subst hA hB
    obtain ⟨-, -, h2⟩ := coords_of_commutator_mem_U (key ω 0 0 0 0 0)
    simp at h1 h2
    have hD : C = D := CharTwo.add_eq_zero.1 h1
    subst hD
    have hω : ω + 1 ≠ 0 := fun h => hω1 ((CharTwo.add_eq_zero).1 h)
    have hC : C * (ω * (ω + 1)) = 0 := by linear_combination h2
    rcases mul_eq_zero.1 hC with hC | hC
    · subst hC
      exact g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩
    · exact absurd hC (mul_ne_zero hω0 hω)
  · intro h ⟨y, hy⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := g2N_mem_Y_iff.1 h
    obtain ⟨a, b, c, d, e, f, rfl⟩ := mem_S.1 hy
    have := g2N_commutator_coords (0 : K) 0 0 0 E F a b c d e f
    rw [commutatorElement_def] at this
    rw [this, g2N_mem_U_iff]
    simp

theorem map_upperCentralSeries_two [Finite K] (hK : 4 ≤ Nat.card K) :
    (Subgroup.upperCentralSeries (S K) 2).map (S K).subtype = Y K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_upperCentralSeries_two_iff hK).1 hy
  · intro hx
    exact ⟨⟨x, Y_le_S hx⟩, (mem_upperCentralSeries_two_iff hK).2 hx, rfl⟩

theorem mem_upperCentralSeries_three_iff [Finite K] (hK : 4 ≤ Nat.card K) {x : S K} :
    x ∈ Subgroup.upperCentralSeries (S K) 3 ↔ (x : ModGL .G2 K) ∈ Model.F K := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, Subgroup.mem_upperCentralSeries_succ_iff]
  simp only [mem_upperCentralSeries_two_iff hK, commutatorElement_def, coe_mul, coe_inv]
  obtain ⟨x, hx⟩ := x
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  constructor
  · intro h
    have key : ∀ a b c d e f : K, ⁅g2N A B C D E F, g2N a b c d e f⁆ ∈ Y K :=
      fun a b c d e f => by
        rw [commutatorElement_def]
        exact h ⟨_, mem_S.2 ⟨a, b, c, d, e, f, rfl⟩⟩
    obtain ⟨hB, -⟩ := coords_of_commutator_mem_Y (key 1 0 0 0 0 0)
    obtain ⟨hA, -⟩ := coords_of_commutator_mem_Y (key 0 1 0 0 0 0)
    simp at hA hB
    subst hA hB
    exact g2N_mem_F_iff.2 ⟨rfl, rfl⟩
  · intro h ⟨y, hy⟩
    obtain ⟨rfl, rfl⟩ := g2N_mem_F_iff.1 h
    obtain ⟨a, b, c, d, e, f, rfl⟩ := mem_S.1 hy
    have := g2N_commutator_coords (0 : K) 0 C D E F a b c d e f
    rw [commutatorElement_def] at this
    rw [this, g2N_mem_Y_iff]
    simp

theorem map_upperCentralSeries_three [Finite K] (hK : 4 ≤ Nat.card K) :
    (Subgroup.upperCentralSeries (S K) 3).map (S K).subtype = Model.F K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_upperCentralSeries_three_iff hK).1 hy
  · intro hx
    exact ⟨⟨x, F_le_S hx⟩, (mem_upperCentralSeries_three_iff hK).2 hx, rfl⟩

theorem commutator_S [Finite K] (hK : 4 ≤ Nat.card K) : ⁅S K, S K⁆ = Model.F K := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
    obtain ⟨a, b, c, d, e, f, rfl⟩ := mem_S.1 hy
    rw [g2N_commutator_coords, g2N_mem_F_iff]
    exact ⟨rfl, rfl⟩
  · obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    have hY : Y K ≤ ⁅S K, S K⁆ := by
      rw [← commutator_M]
      exact commutator_mono M_le_S M_le_S
    have hmem : ∀ A B : K, ⁅g2N (0 : K) B 0 0 0 0, g2N A 0 0 0 0 0⁆ ∈ ⁅S K, S K⁆ := fun A B =>
      commutator_mem_commutator (mem_S.2 ⟨_, _, _, _, _, _, rfl⟩)
        (mem_S.2 ⟨_, _, _, _, _, _, rfl⟩)
    refine F_le_of_forall hω1 hY (fun t => ⟨t, t ^ 2, ?_⟩) fun t => ⟨t * ω ^ 2, ω * t ^ 2, ?_⟩
    · have h := hmem 1 t
      rw [g2N_commutator_coords] at h
      convert h using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · have h := hmem ω (t / ω)
      rw [g2N_commutator_coords] at h
      convert h using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | ring1 | (field_simp; ring1)

theorem closure_sq_S [Finite K] (hK : 4 ≤ Nat.card K) :
    closure {z | ∃ g ∈ S K, z = g ^ 2} = Model.F K := by
  apply le_antisymm
  · rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hg
    rw [SetLike.mem_coe, sq, g2N_mul_self, g2N_mem_F_iff]
    exact ⟨rfl, rfl⟩
  · obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    have hY : Y K ≤ closure {z | ∃ g ∈ S K, z = g ^ 2} := by
      rw [← closure_sq_M]
      exact closure_mono fun z ⟨g, hg, hz⟩ => ⟨g, M_le_S hg, hz⟩
    have hmem : ∀ A B : K, g2N A B 0 0 0 0 * g2N A B 0 0 0 0 ∈
        closure {z | ∃ g ∈ S K, z = g ^ 2} := fun A B =>
      subset_closure ⟨_, mem_S.2 ⟨A, B, 0, 0, 0, 0, rfl⟩, (sq _).symm⟩
    refine F_le_of_forall hω1 hY (fun t => ⟨t, 0, ?_⟩) fun t => ⟨t * ω ^ 2, 0, ?_⟩
    · have h := hmem 1 t
      rw [g2N_mul_self] at h
      convert h using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · have h := hmem ω (t / ω)
      rw [g2N_mul_self] at h
      convert h using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | ring1 | (field_simp; ring1) | field_simp

theorem commutator_F : ⁅Model.F K, Model.F K⁆ = U K := by
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    obtain ⟨C, D, E, F, rfl⟩ := mem_F.1 hx
    obtain ⟨c, d, e, f, rfl⟩ := mem_F.1 hy
    rw [g2N_commutator_coords, g2N_mem_U_iff]
    simp
  · intro x hx
    obtain ⟨f, rfl⟩ := mem_U.1 hx
    rw [← commutator_ab_2ab]
    exact commutator_mem_commutator (g2N_mem_F_iff.2 ⟨rfl, rfl⟩) (g2N_mem_F_iff.2 ⟨rfl, rfl⟩)

theorem commutator_commutator_S [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅⁅S K, S K⁆, ⁅S K, S K⁆⁆ = U K := by
  rw [commutator_S hK, commutator_F]

theorem twoElementaryProduct_F : Common.TwoElementaryProduct (Model.F K) (W K) (X K) where
  le_left := W_le_F
  le_right := X_le_F
  exists_mul := by
    rintro _ ⟨c, d, e, f, rfl⟩
    refine ⟨g2N 0 0 0 d e (f + c * d), g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩, g2N 0 0 c 0 0 0,
      g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩, ?_⟩
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
  isElementaryAbelian_left := W_isElementaryAbelian
  isElementaryAbelian_right := X_isElementaryAbelian
  exists_mul_ne := by
    refine ⟨g2N 0 0 1 0 0 0, g2N_mem_F_iff.2 ⟨rfl, rfl⟩, g2N 0 0 0 1 0 0,
      g2N_mem_F_iff.2 ⟨rfl, rfl⟩, fun h => ?_⟩
    rw [g2N_mul_coords, g2N_mul_coords] at h
    have := (g2N_injective h).2.2.2.2.2
    simp at this
  inf_centralizer_left := by
    intro w hw hwX
    obtain ⟨D, E, F, rfl⟩ := mem_W.1 hw
    have hD : D ≠ 0 := fun hD => hwX (g2N_mem_X_iff.2 ⟨rfl, rfl, hD⟩)
    apply le_antisymm
    · rintro x ⟨hx, hc⟩
      obtain ⟨c, d, e, f, rfl⟩ := mem_F.1 hx
      have h := commutatorElement_eq_one_iff_mul_comm.2 (mem_centralizer_singleton_iff.1 hc)
      obtain ⟨-, -, -, h4⟩ := coords_of_commutator_eq_one h
      simp only [zero_mul, mul_zero, zero_add, add_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow] at h4
      rcases mul_eq_zero.1 h4 with h | h
      · subst h
        exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩
      · exact absurd h hD
    · intro x hx
      refine ⟨W_le_F hx, mem_centralizer_singleton_iff.2 ?_⟩
      exact (commute_of_mem_g2ShortRadical hx hw).eq

theorem maximal_elementaryAbelian_F_iff (E : Subgroup (ModGL .G2 K)) :
    Maximal (fun E' : Subgroup (ModGL .G2 K) => E' ≤ Model.F K ∧ CFSG.IsElementaryAbelian 2 E')
      E ↔ E = W K ∨ E = X K :=
  twoElementaryProduct_F.maximal_iff E

theorem F_inf_centralizer_F :
    Model.F K ⊓ centralizer (Model.F K : Set (ModGL .G2 K)) = Y K := by
  rw [twoElementaryProduct_F.inf_centralizer_self, inf_comm, X_inf_W]

theorem mem_D_or_M_of_mul_self_mem {N : Subgroup (ModGL .G2 K)} (hN : N ≤ W K ∨ N ≤ X K)
    {x : ModGL .G2 K} (hx : x ∈ S K) (hsq : x * x ∈ N) : x ∈ Model.D K ∨ x ∈ M K := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  rw [g2N_mul_self] at hsq
  rcases hN with hN | hN
  · obtain ⟨-, -, h⟩ := g2N_mem_W_iff.1 (hN hsq)
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (g2N_mem_D_iff.2 h)
    · exact Or.inr (g2N_mem_M_iff.2 h)
  · obtain ⟨-, -, h⟩ := g2N_mem_X_iff.1 (hN hsq)
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (g2N_mem_D_iff.2 (pow_eq_zero_iff two_ne_zero |>.1 h))
    · exact Or.inr (g2N_mem_M_iff.2 h)

theorem elemModulo_M {N : Subgroup (ModGL .G2 K)} (hN : Y K ≤ N) : ElemModulo N (M K) := by
  intro x hx y hy
  obtain ⟨A, C, D, E, F, rfl⟩ := mem_M.1 hx
  obtain ⟨a, c, d, e, f, rfl⟩ := mem_M.1 hy
  refine ⟨hN ?_, hN ?_⟩
  · rw [g2N_mul_self, g2N_mem_Y_iff]
    simp
  · rw [g2N_commutator_coords, g2N_mem_Y_iff]
    simp

theorem elemModulo_D {N : Subgroup (ModGL .G2 K)} (hN : Y K ≤ N) :
    ElemModulo N (Model.D K) := by
  intro x hx y hy
  obtain ⟨B, C, D, E, F, rfl⟩ := mem_D.1 hx
  obtain ⟨b, c, d, e, f, rfl⟩ := mem_D.1 hy
  refine ⟨hN ?_, hN ?_⟩
  · rw [g2N_mul_self, g2N_mem_Y_iff]
    simp
  · rw [g2N_commutator_coords, g2N_mem_Y_iff]
    simp

theorem not_M_le_D : ¬ M K ≤ Model.D K ∧ ¬ Model.D K ≤ M K := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := g2N_mem_D_iff.1 (h ((g2N_mem_M_iff (A := (1 : K)) (C := 0) (D := 0) (E := 0)
      (F := 0)).2 rfl))
    exact one_ne_zero this
  · have := g2N_mem_M_iff.1 (h ((g2N_mem_D_iff (B := (1 : K)) (C := 0) (D := 0) (E := 0)
      (F := 0)).2 rfl))
    exact one_ne_zero this

theorem maximal_elemModulo_iff {N : Subgroup (ModGL .G2 K)} (hYN : Y K ≤ N)
    (hN : N ≤ W K ∨ N ≤ X K) (E : Subgroup (ModGL .G2 K)) :
    Maximal (fun E' : Subgroup (ModGL .G2 K) => N ≤ E' ∧ E' ≤ S K ∧ ElemModulo N E') E ↔
      E = M K ∨ E = Model.D K := by
  have hNF : N ≤ Model.F K := hN.elim (fun h => h.trans W_le_F) fun h => h.trans X_le_F
  have key : ∀ E' : Subgroup (ModGL .G2 K), E' ≤ S K → ElemModulo N E' →
      E' ≤ M K ∨ E' ≤ Model.D K := fun E' hE'S hE' =>
    (le_or_le_of_subset_union fun x hx =>
      (mem_D_or_M_of_mul_self_mem hN (hE'S hx) (hE' x hx x hx).1).symm)
  have hM : N ≤ M K ∧ M K ≤ S K ∧ ElemModulo N (M K) :=
    ⟨hNF.trans F_le_M, M_le_S, elemModulo_M hYN⟩
  have hD : N ≤ Model.D K ∧ Model.D K ≤ S K ∧ ElemModulo N (Model.D K) :=
    ⟨hNF.trans F_le_D, D_le_S, elemModulo_D hYN⟩
  constructor
  · rintro ⟨⟨-, hES, hE⟩, hmax⟩
    rcases key E hES hE with h | h
    · exact Or.inl (le_antisymm h (hmax hM h))
    · exact Or.inr (le_antisymm h (hmax hD h))
  · rintro (rfl | rfl)
    · refine ⟨hM, fun E' hE' hME' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h | h
      · exact h
      · exact absurd (hME'.trans h) not_M_le_D.1
    · refine ⟨hD, fun E' hE' hDE' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h | h
      · exact absurd (hDE'.trans h) not_M_le_D.2
      · exact h

theorem maximal_elemModulo_Y_iff (E : Subgroup (ModGL .G2 K)) :
    Maximal (fun E' : Subgroup (ModGL .G2 K) => Y K ≤ E' ∧ E' ≤ S K ∧ ElemModulo (Y K) E') E ↔
      E = M K ∨ E = Model.D K :=
  maximal_elemModulo_iff le_rfl (Or.inl Y_le_W) E

theorem maximal_elemModulo_W_iff (E : Subgroup (ModGL .G2 K)) :
    Maximal (fun E' : Subgroup (ModGL .G2 K) => W K ≤ E' ∧ E' ≤ S K ∧ ElemModulo (W K) E') E ↔
      E = M K ∨ E = Model.D K :=
  maximal_elemModulo_iff Y_le_W (Or.inl le_rfl) E

theorem maximal_elemModulo_X_iff (E : Subgroup (ModGL .G2 K)) :
    Maximal (fun E' : Subgroup (ModGL .G2 K) => X K ≤ E' ∧ E' ≤ S K ∧ ElemModulo (X K) E') E ↔
      E = M K ∨ E = Model.D K :=
  maximal_elemModulo_iff Y_le_X (Or.inr le_rfl) E

omit
  [CharP K 2] in
theorem exists_torus_conj_g2N {h : ModGL .G2 K} (hh : h ∈ torusGroup .G2 K) :
    ∃ c₁ c₂ c₃ c₄ c₅ c₆ : Kˣ, ∀ A B C D E F : K, h * g2N A B C D E F * h⁻¹ =
      g2N (c₁ * A) (c₂ * B) (c₃ * C) (c₄ * D) (c₅ * E) (c₆ * F) := by
  obtain ⟨c₁, h₁⟩ := exists_torus_scale hh isRoot_g2r
  obtain ⟨c₂, h₂⟩ := exists_torus_scale hh isRoot_g2a
  obtain ⟨c₃, h₃⟩ := exists_torus_scale hh isRoot_g2u
  obtain ⟨c₄, h₄⟩ := exists_torus_scale hh isRoot_g2v
  obtain ⟨c₅, h₅⟩ := exists_torus_scale hh isRoot_g2b
  obtain ⟨c₆, h₆⟩ := exists_torus_scale hh isRoot_g2c
  refine ⟨c₁, c₂, c₃, c₄, c₅, c₆, fun A B C D E F => ?_⟩
  have e : ∀ x y : ModGL .G2 K, h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) :=
    fun x y => by group
  simp only [g2N, e, h₁, h₂, h₃, h₄, h₅, h₆]

omit [CharP K 2] in
theorem borelGroup_le_normalizer {H : Subgroup (ModGL .G2 K)}
    (hS : S K ≤ normalizer (H : Set (ModGL .G2 K)))
    (hH : ∀ (c₁ c₂ c₃ c₄ c₅ c₆ : Kˣ) (A B C D E F : K), g2N A B C D E F ∈ H →
      g2N (c₁ * A) (c₂ * B) (c₃ * C) (c₄ * D) (c₅ * E) (c₆ * F) ∈ H)
    (hHS : H ≤ S K) : borelGroup .G2 K ≤ normalizer (H : Set (ModGL .G2 K)) := by
  refine sup_le (le_normalizer_of_conj_mem fun h hh x hx => ?_) hS
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 (hHS hx)
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, hc⟩ := exists_torus_conj_g2N hh
  rw [hc]
  exact hH c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F hx

theorem borelGroup_le_normalizer_U : borelGroup .G2 K ≤ normalizer (U K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_U (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := g2N_mem_U_iff.1 h
    exact g2N_mem_U_iff.2 ⟨mul_zero _, mul_zero _, mul_zero _, mul_zero _, mul_zero _⟩) U_le_S

theorem borelGroup_le_normalizer_X : borelGroup .G2 K ≤ normalizer (X K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_X (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_X_iff.1 h
    exact g2N_mem_X_iff.2 ⟨mul_zero _, mul_zero _, mul_zero _⟩) X_le_S

theorem borelGroup_le_normalizer_W : borelGroup .G2 K ≤ normalizer (W K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_W (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain ⟨rfl, rfl, rfl⟩ := g2N_mem_W_iff.1 h
    exact g2N_mem_W_iff.2 ⟨mul_zero _, mul_zero _, mul_zero _⟩) W_le_S

theorem borelGroup_le_normalizer_F :
    borelGroup .G2 K ≤ normalizer (Model.F K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_F (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain ⟨rfl, rfl⟩ := g2N_mem_F_iff.1 h
    exact g2N_mem_F_iff.2 ⟨mul_zero _, mul_zero _⟩) F_le_S

theorem borelGroup_le_normalizer_D :
    borelGroup .G2 K ≤ normalizer (Model.D K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_D (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain rfl := g2N_mem_D_iff.1 h
    exact g2N_mem_D_iff.2 (mul_zero _)) D_le_S

theorem borelGroup_le_normalizer_M : borelGroup .G2 K ≤ normalizer (M K : Set (ModGL .G2 K)) :=
  borelGroup_le_normalizer S_le_normalizer_M (fun c₁ c₂ c₃ c₄ c₅ c₆ A B C D E F h => by
    obtain rfl := g2N_mem_M_iff.1 h
    exact g2N_mem_M_iff.2 (mul_zero _)) M_le_S

theorem exists_bruhat_of_mem_normalizer {H : Subgroup (ModGL .G2 K)}
    (hB : borelGroup .G2 K ≤ normalizer (H : Set (ModGL .G2 K))) {g : ModGL .G2 K}
    (hg : g ∈ adjointGroup .G2 K) (hgN : g ∈ normalizer (H : Set (ModGL .G2 K))) :
    ∃ w : WeylGroup .G2, ∃ b₁ ∈ borelGroup .G2 K, ∃ b₂ ∈ borelGroup .G2 K,
      g = b₁ * canonicalRep (coxeterSystem .G2) K w * b₂ ∧
      ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ H → pinnedX .G2 K (w • γ) 1 ∈ H := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := exists_bruhat hg
  refine ⟨w, b₁, hb₁, b₂, hb₂, rfl, fun γ hγ hX => ?_⟩
  have hnN : canonicalRep (coxeterSystem .G2) K w ∈ normalizer (H : Set (ModGL .G2 K)) := by
    have e : canonicalRep (coxeterSystem .G2) K w =
        b₁⁻¹ * (b₁ * canonicalRep (coxeterSystem .G2) K w * b₂) * b₂⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hB hb₁)) hgN) (inv_mem (hB hb₂))
  rw [← canonicalRep_conj w hγ 1]
  exact (mem_normalizer_iff.mp hnN _).mp hX

omit
  [CharP K 2] in
theorem pos_of_pinnedX_mem_S {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ)
    (h : pinnedX .G2 K δ 1 ∈ S K) :
    δ = g2r ∨ δ = g2a ∨ δ = g2u ∨ δ = g2v ∨ δ = g2b ∨ δ = g2c := by
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  have hneg : ∀ {γ : Fin Tag.G2.rank → ℤ}, (γ = g2r ∨ γ = g2a ∨ γ = g2u ∨ γ = g2v ∨
      γ = g2b ∨ γ = g2c) → pinnedX .G2 K (-γ) 1 ∈ S K → False := fun hγ hγS =>
    h10 (pinnedX_injective .G2 K _ ((eq_one_of_mem_borel_of_mem_neg
      (posUnipotent_le_borelGroup hγS) (pinnedX_neg_mem_negUnipotent hγ 1)).trans
        (pinnedX_zero .G2 K _).symm))
  rcases g2_root_cases hδ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact (hneg (Or.inl rfl) h).elim
  · exact (hneg (Or.inr (Or.inl rfl)) h).elim
  · exact (hneg (Or.inr (Or.inr (Or.inl rfl))) h).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) h).elim
  · exact (hneg (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) h).elim

theorem roots_X {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) (h : pinnedX .G2 K δ 1 ∈ X K) :
    δ = g2u ∨ δ = g2b ∨ δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (X_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N] at h
    exact absurd (g2N_mem_X_iff.1 h).1 one_ne_zero
  · rw [pinnedX_a_eq_g2N] at h
    exact absurd (g2N_mem_X_iff.1 h).2.1 one_ne_zero
  · exact Or.inl rfl
  · rw [pinnedX_v_eq_g2N] at h
    exact absurd (g2N_mem_X_iff.1 h).2.2 one_ne_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem roots_F {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ)
    (h : pinnedX .G2 K δ 1 ∈ Model.F K) : δ = g2u ∨ δ = g2v ∨ δ = g2b ∨ δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (F_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N] at h
    exact absurd (g2N_mem_F_iff.1 h).1 one_ne_zero
  · rw [pinnedX_a_eq_g2N] at h
    exact absurd (g2N_mem_F_iff.1 h).2 one_ne_zero
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem roots_D {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ)
    (h : pinnedX .G2 K δ 1 ∈ Model.D K) : δ = g2a ∨ δ = g2u ∨ δ = g2v ∨ δ = g2b ∨ δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (D_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N] at h
    exact absurd (g2N_mem_D_iff.1 h) one_ne_zero
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem roots_M {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) (h : pinnedX .G2 K δ 1 ∈ M K) :
    δ = g2r ∨ δ = g2u ∨ δ = g2v ∨ δ = g2b ∨ δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (M_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · rw [pinnedX_a_eq_g2N] at h
    exact absurd (g2N_mem_M_iff.1 h) one_ne_zero
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem roots_W {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) (h : pinnedX .G2 K δ 1 ∈ W K) :
    δ = g2v ∨ δ = g2b ∨ δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (W_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N] at h
    exact absurd (g2N_mem_W_iff.1 h).1 one_ne_zero
  · rw [pinnedX_a_eq_g2N] at h
    exact absurd (g2N_mem_W_iff.1 h).2.1 one_ne_zero
  · rw [pinnedX_u_eq_g2N] at h
    exact absurd (g2N_mem_W_iff.1 h).2.2 one_ne_zero
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem roots_U {δ : Fin Tag.G2.rank → ℤ} (hδ : IsRoot .G2 δ) (h : pinnedX .G2 K δ 1 ∈ U K) :
    δ = g2c := by
  rcases pos_of_pinnedX_mem_S hδ (U_le_S h) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [pinnedX_r_eq_g2N] at h
    exact absurd (g2N_mem_U_iff.1 h).1 one_ne_zero
  · rw [pinnedX_a_eq_g2N] at h
    exact absurd (g2N_mem_U_iff.1 h).2.1 one_ne_zero
  · rw [pinnedX_u_eq_g2N] at h
    exact absurd (g2N_mem_U_iff.1 h).2.2.1 one_ne_zero
  · rw [pinnedX_v_eq_g2N] at h
    exact absurd (g2N_mem_U_iff.1 h).2.2.2.1 one_ne_zero
  · rw [pinnedX_b_eq_g2N] at h
    exact absurd (g2N_mem_U_iff.1 h).2.2.2.2 one_ne_zero
  · rfl

end Model

section Weyl


theorem weyl_eq_one_of_X {w : WeylGroup .G2}
    (hu : w • g2u = g2u ∨ w • g2u = g2b ∨ w • g2u = g2c)
    (hb : w • g2b = g2u ∨ w • g2b = g2b ∨ w • g2b = g2c)
    (hc : w • g2c = g2u ∨ w • g2c = g2b ∨ w • g2c = g2c) : w = 1 := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2u, ha, hr] at hu <;> rw [smul_g2b, ha, hr] at hb <;> rw [smul_g2c, ha, hr] at hc
  · exact eq_one_of_smul ha hr
  all_goals exfalso; revert hu hb hc; decide

theorem weyl_eq_one_of_F {w : WeylGroup .G2}
    (h1 : w • g2u = g2u ∨ w • g2u = g2v ∨ w • g2u = g2b ∨ w • g2u = g2c)
    (h2 : w • g2v = g2u ∨ w • g2v = g2v ∨ w • g2v = g2b ∨ w • g2v = g2c)
    (h3 : w • g2b = g2u ∨ w • g2b = g2v ∨ w • g2b = g2b ∨ w • g2b = g2c) : w = 1 := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2u, ha, hr] at h1 <;> rw [smul_g2v, ha, hr] at h2 <;> rw [smul_g2b, ha, hr] at h3
  · exact eq_one_of_smul ha hr
  all_goals exfalso; revert h1 h2 h3; decide

theorem weyl_of_c {w : WeylGroup .G2} (h : w • g2c = g2c) : w = 1 ∨ w = simple .G2 g2ir := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2c, ha, hr] at h
  · exact Or.inl (eq_one_of_smul ha hr)
  · exfalso; revert h; decide
  · exact Or.inr (eq_simple_r_of_smul ha hr)
  all_goals exfalso; revert h; decide

theorem weyl_of_D {w : WeylGroup .G2}
    (h1 : w • g2a = g2a ∨ w • g2a = g2u ∨ w • g2a = g2v ∨ w • g2a = g2b ∨ w • g2a = g2c)
    (h2 : w • g2u = g2a ∨ w • g2u = g2u ∨ w • g2u = g2v ∨ w • g2u = g2b ∨ w • g2u = g2c)
    (h3 : w • g2v = g2a ∨ w • g2v = g2u ∨ w • g2v = g2v ∨ w • g2v = g2b ∨ w • g2v = g2c) :
    w = 1 ∨ w = simple .G2 g2ir := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [ha] at h1 <;> rw [smul_g2u, ha, hr] at h2 <;> rw [smul_g2v, ha, hr] at h3
  · exact Or.inl (eq_one_of_smul ha hr)
  · exfalso; revert h1 h2 h3; decide
  · exact Or.inr (eq_simple_r_of_smul ha hr)
  all_goals exfalso; revert h1 h2 h3; decide

theorem weyl_of_W {w : WeylGroup .G2} (h1 : w • g2v = g2v ∨ w • g2v = g2b ∨ w • g2v = g2c) :
    w = 1 ∨ w = simple .G2 g2ia := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [smul_g2v, ha, hr] at h1
  · exact Or.inl (eq_one_of_smul ha hr)
  · exact Or.inr (eq_simple_a_of_smul ha hr)
  all_goals exfalso; revert h1; decide

theorem weyl_of_M {w : WeylGroup .G2}
    (h1 : w • g2r = g2r ∨ w • g2r = g2u ∨ w • g2r = g2v ∨ w • g2r = g2b ∨ w • g2r = g2c)
    (h2 : w • g2u = g2r ∨ w • g2u = g2u ∨ w • g2u = g2v ∨ w • g2u = g2b ∨ w • g2u = g2c)
    (h3 : w • g2b = g2r ∨ w • g2b = g2u ∨ w • g2b = g2v ∨ w • g2b = g2b ∨ w • g2b = g2c) :
    w = 1 ∨ w = simple .G2 g2ia := by
  rcases g2_weyl_cases w with ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ |
    ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ | ⟨ha, hr⟩ <;>
    rw [hr] at h1 <;> rw [smul_g2u, ha, hr] at h2 <;> rw [smul_g2b, ha, hr] at h3
  · exact Or.inl (eq_one_of_smul ha hr)
  · exact Or.inr (eq_simple_a_of_smul ha hr)
  all_goals exfalso; revert h1 h2 h3; decide

end Weyl

namespace Model


variable {K : Type} [Field K] [CharP K 2]

theorem pinnedX_mem_F : pinnedX .G2 K g2u 1 ∈ Model.F K ∧ pinnedX .G2 K g2v 1 ∈ Model.F K ∧
    pinnedX .G2 K g2b 1 ∈ Model.F K ∧ pinnedX .G2 K g2c 1 ∈ Model.F K := by
  rw [pinnedX_u_eq_g2N, pinnedX_v_eq_g2N, pinnedX_b_eq_g2N, pinnedX_c_eq_g2N]
  exact ⟨g2N_mem_F_iff.2 ⟨rfl, rfl⟩, g2N_mem_F_iff.2 ⟨rfl, rfl⟩, g2N_mem_F_iff.2 ⟨rfl, rfl⟩,
    g2N_mem_F_iff.2 ⟨rfl, rfl⟩⟩

theorem adjointGroup_inf_normalizer_X :
    adjointGroup .G2 K ⊓ normalizer (X K : Set (ModGL .G2 K)) = borelGroup .G2 K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_X hg hgN
    have hX : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ X K →
        (w • γ = g2u ∨ w • γ = g2b ∨ w • γ = g2c) :=
      fun γ hγ h => roots_X (IsRoot.smul hγ w) (hw γ hγ h)
    have hu : pinnedX .G2 K g2u 1 ∈ X K := by
      rw [pinnedX_u_eq_g2N]; exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
    have hb : pinnedX .G2 K g2b 1 ∈ X K := by
      rw [pinnedX_b_eq_g2N]; exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
    have hc : pinnedX .G2 K g2c 1 ∈ X K := by
      rw [pinnedX_c_eq_g2N]; exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
    obtain rfl := weyl_eq_one_of_X (hX _ isRoot_g2u hu) (hX _ isRoot_g2b hb) (hX _ isRoot_g2c hc)
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · exact le_inf AS81.G2.borelGroup_le_adjointGroup₀ borelGroup_le_normalizer_X

theorem adjointGroup_inf_normalizer_F :
    adjointGroup .G2 K ⊓ normalizer (Model.F K : Set (ModGL .G2 K)) = borelGroup .G2 K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_F hg hgN
    have hF : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ Model.F K →
        (w • γ = g2u ∨ w • γ = g2v ∨ w • γ = g2b ∨ w • γ = g2c) :=
      fun γ hγ h => roots_F (IsRoot.smul hγ w) (hw γ hγ h)
    obtain ⟨hu, hv, hb, -⟩ := pinnedX_mem_F (K := K)
    obtain rfl := weyl_eq_one_of_F (hF _ isRoot_g2u hu) (hF _ isRoot_g2v hv) (hF _ isRoot_g2b hb)
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb₁ hb₂
  · exact le_inf AS81.G2.borelGroup_le_adjointGroup₀ borelGroup_le_normalizer_F

omit [CharP K 2] in
theorem adjointGroup_inf_normalizer_S :
    adjointGroup .G2 K ⊓ normalizer (S K : Set (ModGL .G2 K)) = borelGroup .G2 K ∧
      borelGroup .G2 K = J K ⊔ S K :=
  ⟨(borel_self_normalizers .G2 K).1, rfl⟩

theorem borelGroup_le_D_sup : borelGroup .G2 K ≤ Model.D K ⊔ leviA K ⊔ J K := by
  refine sup_le le_sup_right fun u hu => ?_
  obtain ⟨s, q, hq, rfl⟩ := exists_pinnedX_r_mul_of_mem_posUnipotent hu
  refine mul_mem (mem_sup_left (mem_sup_right ?_)) (mem_sup_left (mem_sup_left hq))
  rw [← xUnit_g2ir]
  exact xUnit_mem_g2RankOne g2ir s

theorem borelGroup_le_M_sup : borelGroup .G2 K ≤ M K ⊔ leviB K ⊔ J K := by
  refine sup_le le_sup_right fun u hu => ?_
  obtain ⟨q, hq, s, rfl⟩ := exists_mul_pinnedX_a_of_mem_posUnipotent hu
  refine mul_mem (mem_sup_left (mem_sup_left hq)) (mem_sup_left (mem_sup_right ?_))
  rw [← xUnit_g2ia]
  exact xUnit_mem_g2RankOne g2ia s

theorem mem_D_sup_of_bruhat {w : WeylGroup .G2} (hw : w = 1 ∨ w = simple .G2 g2ir)
    {b₁ b₂ : ModGL .G2 K} (hb₁ : b₁ ∈ borelGroup .G2 K) (hb₂ : b₂ ∈ borelGroup .G2 K) :
    b₁ * canonicalRep (coxeterSystem .G2) K w * b₂ ∈ Model.D K ⊔ leviA K ⊔ J K := by
  refine mul_mem (mul_mem (borelGroup_le_D_sup hb₁) ?_) (borelGroup_le_D_sup hb₂)
  rcases hw with rfl | rfl
  · rw [canonicalRep_one]
    exact one_mem _
  · rw [canonicalRep_simple]
    exact mem_sup_left (mem_sup_right (weylElt_mem_g2RankOne g2ir 1))

theorem mem_M_sup_of_bruhat {w : WeylGroup .G2} (hw : w = 1 ∨ w = simple .G2 g2ia)
    {b₁ b₂ : ModGL .G2 K} (hb₁ : b₁ ∈ borelGroup .G2 K) (hb₂ : b₂ ∈ borelGroup .G2 K) :
    b₁ * canonicalRep (coxeterSystem .G2) K w * b₂ ∈ M K ⊔ leviB K ⊔ J K := by
  refine mul_mem (mul_mem (borelGroup_le_M_sup hb₁) ?_) (borelGroup_le_M_sup hb₂)
  rcases hw with rfl | rfl
  · rw [canonicalRep_one]
    exact one_mem _
  · rw [canonicalRep_simple]
    exact mem_sup_left (mem_sup_right (weylElt_mem_g2RankOne g2ia 1))

omit
  [CharP K 2] in
theorem J_le_of_borel {H : Subgroup (ModGL .G2 K)}
    (h : borelGroup .G2 K ≤ normalizer (H : Set (ModGL .G2 K))) :
    J K ≤ adjointGroup .G2 K ⊓ normalizer (H : Set (ModGL .G2 K)) :=
  le_inf (J_le_adjointGroup K) (le_sup_left.trans h)

theorem adjointGroup_inf_normalizer_U :
    adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) = Model.D K ⊔ leviA K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_U hg hgN
    have hc : pinnedX .G2 K g2c 1 ∈ U K := mem_rootSubgroup.2 ⟨1, rfl⟩
    exact mem_D_sup_of_bruhat (weyl_of_c (roots_U (IsRoot.smul isRoot_g2c w)
      (hw _ isRoot_g2c hc))) hb₁ hb₂
  · refine sup_le (sup_le (le_inf D_le_adjointGroup
      (D_le_S.trans (borelGroup_le_normalizer_U.trans' le_sup_right)))
      (le_inf (leviA_le_adjointGroup K) ?_)) (J_le_of_borel borelGroup_le_normalizer_U)
    refine fun l hl => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact (commute_of_mem_g2RankOne_r hl y).eq.symm

theorem adjointGroup_inf_normalizer_D :
    adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)) =
      Model.D K ⊔ leviA K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_D hg hgN
    have hD : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ Model.D K →
        (w • γ = g2a ∨ w • γ = g2u ∨ w • γ = g2v ∨ w • γ = g2b ∨ w • γ = g2c) :=
      fun γ hγ h => roots_D (IsRoot.smul hγ w) (hw γ hγ h)
    obtain ⟨hu, hv, -, -⟩ := pinnedX_mem_F (K := K)
    have ha : pinnedX .G2 K g2a 1 ∈ Model.D K := by
      rw [pinnedX_a_eq_g2N]; exact g2N_mem_D_iff.2 rfl
    exact mem_D_sup_of_bruhat (weyl_of_D (hD _ isRoot_g2a ha) (hD _ isRoot_g2u (F_le_D hu))
      (hD _ isRoot_g2v (F_le_D hv))) hb₁ hb₂
  · refine sup_le (sup_le (le_inf D_le_adjointGroup (D_le_S.trans
      (borelGroup_le_normalizer_D.trans' le_sup_right)))
      (le_inf (leviA_le_adjointGroup K) g2RankOne_r_le_normalizer))
      (J_le_of_borel borelGroup_le_normalizer_D)

theorem leviB_le_normalizer_M : leviB K ≤ normalizer (M K : Set (ModGL .G2 K)) :=
  le_normalizer_of_conj_mem fun _ hl _ hq => conj_mem_g2ShortParabolicRadical hl hq

theorem adjointGroup_inf_normalizer_Y :
    adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)) = M K ⊔ leviB K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer AS81.G2.borelGroup_le_normalizer_g2BCGroup hg hgN
    have hY : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ Y K → (w • γ = g2b ∨ w • γ = g2c) :=
      fun γ hγ h => AS81.G2.eq_b_or_c_of_pinnedX_mem (IsRoot.smul hγ w) (hw γ hγ h)
    exact mem_M_sup_of_bruhat (AS81.G2.weyl_eq_of_bc
      (hY _ isRoot_g2b (AS81.G2.pinnedX_b_mem_g2BCGroup 1))
      (hY _ isRoot_g2c (AS81.G2.pinnedX_c_mem_g2BCGroup 1))) hb₁ hb₂
  · refine sup_le (sup_le (le_inf M_le_adjointGroup (M_le_S.trans
      (AS81.G2.borelGroup_le_normalizer_g2BCGroup.trans' le_sup_right)))
      (le_inf (leviB_le_adjointGroup K) AS81.G2.g2RankOne_a_le_normalizer))
      (J_le_of_borel AS81.G2.borelGroup_le_normalizer_g2BCGroup)

theorem adjointGroup_inf_normalizer_W :
    adjointGroup .G2 K ⊓ normalizer (W K : Set (ModGL .G2 K)) = M K ⊔ leviB K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_W hg hgN
    have hv : pinnedX .G2 K g2v 1 ∈ W K := pinnedX_v_mem_g2ShortRadical 1
    exact mem_M_sup_of_bruhat (weyl_of_W (roots_W (IsRoot.smul isRoot_g2v w)
      (hw _ isRoot_g2v hv))) hb₁ hb₂
  · refine sup_le (sup_le (le_inf M_le_adjointGroup (M_le_S.trans
      (borelGroup_le_normalizer_W.trans' le_sup_right)))
      (le_inf (leviB_le_adjointGroup K) g2RankOne_a_le_normalizer))
      (J_le_of_borel borelGroup_le_normalizer_W)

theorem adjointGroup_inf_normalizer_M :
    adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K)) = M K ⊔ leviB K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl, hw⟩ :=
      exists_bruhat_of_mem_normalizer borelGroup_le_normalizer_M hg hgN
    have hM : ∀ γ, IsRoot .G2 γ → pinnedX .G2 K γ 1 ∈ M K →
        (w • γ = g2r ∨ w • γ = g2u ∨ w • γ = g2v ∨ w • γ = g2b ∨ w • γ = g2c) :=
      fun γ hγ h => roots_M (IsRoot.smul hγ w) (hw γ hγ h)
    obtain ⟨hu, -, hb, -⟩ := pinnedX_mem_F (K := K)
    have hr : pinnedX .G2 K g2r 1 ∈ M K := by
      rw [pinnedX_r_eq_g2N]; exact g2N_mem_M_iff.2 rfl
    exact mem_M_sup_of_bruhat (weyl_of_M (hM _ isRoot_g2r hr) (hM _ isRoot_g2u (F_le_M hu))
      (hM _ isRoot_g2b (F_le_M hb))) hb₁ hb₂
  · refine sup_le (sup_le (le_inf M_le_adjointGroup (M_le_S.trans
      (borelGroup_le_normalizer_M.trans' le_sup_right)))
      (le_inf (leviB_le_adjointGroup K) leviB_le_normalizer_M))
      (J_le_of_borel borelGroup_le_normalizer_M)

theorem adjointGroup_inf_normalizer_v [Finite K] :
    adjointGroup .G2 K ⊓ normalizer (rootSubgroup .G2 K g2v : Set (ModGL .G2 K)) =
      W K ⊔ leviB K ⊔ J K := by
  apply le_antisymm
  · rintro g ⟨hg, hgN⟩
    have h1 : g * pinnedX .G2 K g2v 1 * g⁻¹ ∈ rootSubgroup .G2 K g2v :=
      (mem_normalizer_iff.1 hgN _).1 (mem_rootSubgroup.2 ⟨1, rfl⟩)
    obtain ⟨μ, hμ⟩ := mem_rootSubgroup.1 h1
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [pinnedX_zero] at hμ
      have : pinnedX .G2 K g2v 1 = 1 := by
        have h2 := congrArg (fun x => g⁻¹ * x * g) hμ
        simpa [mul_assoc] using h2.symm
      exact one_ne_zero (pinnedX_injective .G2 K _ (this.trans (pinnedX_zero .G2 K _).symm))
    set d := torusElt .G2 K g2ir (Units.mk0 μ hμ0) with hd
    have hdv : d * pinnedX .G2 K g2v 1 * d⁻¹ = pinnedX .G2 K g2v μ := by
      rw [hd, torus_r_v, Units.val_mk0, mul_one]
    have hc : d⁻¹ * g ∈ adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K g2v 1} := by
      refine mem_inf.2 ⟨mul_mem (inv_mem (torusElt_mem_adjointGroup _ _)) hg,
        mem_centralizer_singleton_iff.2 ?_⟩
      have e : d⁻¹ * g * pinnedX .G2 K g2v 1 = d⁻¹ * (g * pinnedX .G2 K g2v 1 * g⁻¹) * g := by
        group
      rw [e, ← hμ, ← hdv]
      group
    rw [(even_G2_highest_short_root_centralizer K).2.2.2.1] at hc
    have hdJ : d ∈ J K := torusElt_mem_torusGroup g2ir _
    have e : g = d * (d⁻¹ * g) := by group
    rw [e]
    exact mul_mem (mem_sup_right hdJ) (mem_sup_left hc)
  · refine sup_le (sup_le (le_inf W_le_adjointGroup ?_) (le_inf (leviB_le_adjointGroup K) ?_))
      (le_inf (J_le_adjointGroup K) ?_)
    · refine fun w hw => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
      obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
      exact (commute_of_mem_g2ShortRadical (pinnedX_v_mem_g2ShortRadical y) hw).eq
    · refine fun l hl => centralizer_le_normalizer _ (mem_centralizer_iff.2 fun x hx => ?_)
      obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
      exact (commute_of_mem_g2RankOne_a hl y).eq.symm
    · refine le_normalizer_of_conj_mem fun h hh x hx => ?_
      obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
      obtain ⟨c, hc⟩ := exists_torus_scale hh isRoot_g2v
      rw [hc]
      exact mem_rootSubgroup.2 ⟨_, rfl⟩

end Model

namespace Model


variable {K : Type} [Field K] [CharP K 2]

omit
  [CharP K 2] in
theorem torus_conj_of {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (t₁ t₂ : Kˣ) {m₁ m₂ : ℤ}
    (h₁ : ∑ j, Tag.G2.cartan g2ia j * α j = m₁) (h₂ : ∑ j, Tag.G2.cartan g2ir j * α j = m₂)
    (x : K) : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * pinnedX .G2 K α x *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹ =
      pinnedX .G2 K α (((t₁ ^ m₁ * t₂ ^ m₂ : Kˣ) : K) * x) := by
  rw [torus_conj hα, h₁, h₂]

omit
  [CharP K 2] in
theorem eq_one_of_pinnedX_eq {α : Fin Tag.G2.rank → ℤ} {c : Kˣ}
    (h : pinnedX .G2 K α ((c : K) * 1) = pinnedX .G2 K α 1) : c = 1 := by
  have := pinnedX_injective .G2 K α h
  rw [mul_one] at this
  exact Units.ext this

omit
  [CharP K 2] in
theorem mem_torusFix_of {s : Fin Tag.G2.rank → ℤ} (hs : IsRoot .G2 s) (t₁ t₂ : Kˣ) {m₁ m₂ : ℤ}
    (h₁ : ∑ j, Tag.G2.cartan g2ia j * s j = m₁) (h₂ : ∑ j, Tag.G2.cartan g2ir j * s j = m₂)
    (h : t₁ ^ m₁ * t₂ ^ m₂ = 1) :
    torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ ∈ torusFix K s := by
  refine ⟨mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _),
    mem_centralizer_iff.2 fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
  have := torus_conj_of hs t₁ t₂ h₁ h₂ y
  rw [h, Units.val_one, one_mul] at this
  calc pinnedX .G2 K s y * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) =
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * pinnedX .G2 K s y *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹) *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) := by rw [this]
    _ = (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * pinnedX .G2 K s y := by group

theorem J_le_leviA_sup_J₃ [Finite K] : J K ≤ leviA K ⊔ J₃ K := by
  intro h hh
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  obtain ⟨s, hs⟩ := exists_units_sq_eq t₁
  have h3 : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir s ∈ J₃ K :=
    mem_torusFix_of (m₁ := -1) (m₂ := 2) isRoot_g2r t₁ s (by decide) (by decide) (by
      rw [zpow_neg_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hs,
        inv_mul_cancel])
  have e : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ =
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir s) *
        ((torusElt .G2 K g2ir s)⁻¹ * torusElt .G2 K g2ir t₂) := by group
  rw [e]
  exact mul_mem (mem_sup_right h3) (mem_sup_left (mul_mem (inv_mem
    (torusElt_mem_g2RankOne g2ir s)) (torusElt_mem_g2RankOne g2ir t₂)))

theorem J_le_leviB_sup_J₄ [Finite K] : J K ≤ leviB K ⊔ J₄ K := by
  intro h hh
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
  obtain ⟨s, hs⟩ := exists_units_sq_eq (t₂ ^ 3)
  have h4 : torusElt .G2 K g2ia s * torusElt .G2 K g2ir t₂ ∈ J₄ K :=
    mem_torusFix_of (m₁ := 2) (m₂ := -3) isRoot_g2a s t₂ (by decide) (by decide) (by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hs,
        show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, mul_inv_cancel])
  have e : torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ =
      (torusElt .G2 K g2ia t₁ * (torusElt .G2 K g2ia s)⁻¹) *
        (torusElt .G2 K g2ia s * torusElt .G2 K g2ir t₂) := by group
  rw [e]
  exact mul_mem (mem_sup_left (mul_mem (torusElt_mem_g2RankOne g2ia t₁) (inv_mem
    (torusElt_mem_g2RankOne g2ia s)))) (mem_sup_right h4)

omit
  [CharP K 2] in
theorem commute_of_torus_char {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (t₁ t₂ : Kˣ)
    {m₁ m₂ : ℤ} (h₁ : ∑ j, Tag.G2.cartan g2ia j * α j = m₁)
    (h₂ : ∑ j, Tag.G2.cartan g2ir j * α j = m₂) (h : t₁ ^ m₁ * t₂ ^ m₂ = 1) (x : K) :
    pinnedX .G2 K α x * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) =
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * pinnedX .G2 K α x := by
  have := torus_conj_of hα t₁ t₂ h₁ h₂ x
  rw [h, Units.val_one, one_mul] at this
  calc pinnedX .G2 K α x * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) =
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂ * pinnedX .G2 K α x *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂)⁻¹) *
        (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) := by rw [this]
    _ = (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * pinnedX .G2 K α x := by group

omit
  [CharP K 2] in
theorem torus_char_eq_one {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (t₁ t₂ : Kˣ)
    {m₁ m₂ : ℤ} (h₁ : ∑ j, Tag.G2.cartan g2ia j * α j = m₁)
    (h₂ : ∑ j, Tag.G2.cartan g2ir j * α j = m₂)
    (h : pinnedX .G2 K α 1 * (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) =
      (torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂) * pinnedX .G2 K α 1) :
    t₁ ^ m₁ * t₂ ^ m₂ = 1 := by
  have := torus_conj_of hα t₁ t₂ h₁ h₂ 1
  rw [← h, mul_inv_cancel_right] at this
  exact eq_one_of_pinnedX_eq this.symm

omit
  [CharP K 2] in
theorem J₃_le_centralizer_leviA : J₃ K ≤ centralizer (leviA K : Set (ModGL .G2 K)) := by
  rintro h ⟨hhJ, hhc⟩
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hhJ
  have hχ : t₁ ^ (-1 : ℤ) * t₂ ^ (2 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2r t₁ t₂ (by decide) (by decide)
      (mem_centralizer_iff.1 hhc _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hχ' : t₁ ^ (1 : ℤ) * t₂ ^ (-2 : ℤ) = 1 := by
    have h2 := congrArg (·⁻¹) hχ
    simp only [mul_inv, ← zpow_neg, neg_neg, inv_one] at h2
    exact h2
  have key : leviA K ≤ centralizer {torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂} := by
    rw [leviA, g2RankOne_r_eq, closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact mem_centralizer_singleton_iff.2
        (commute_of_torus_char isRoot_g2r t₁ t₂ (by decide) (by decide) hχ x)
    · exact mem_centralizer_singleton_iff.2
        (commute_of_torus_char isRoot_g2nr t₁ t₂ (by decide) (by decide) hχ' x)
  exact mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (key hl)

omit
  [CharP K 2] in
theorem J₄_le_centralizer_leviB : J₄ K ≤ centralizer (leviB K : Set (ModGL .G2 K)) := by
  rintro h ⟨hhJ, hhc⟩
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hhJ
  have hχ : t₁ ^ (2 : ℤ) * t₂ ^ (-3 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2a t₁ t₂ (by decide) (by decide)
      (mem_centralizer_iff.1 hhc _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hχ' : t₁ ^ (-2 : ℤ) * t₂ ^ (3 : ℤ) = 1 := by
    have h2 := congrArg (·⁻¹) hχ
    simp only [mul_inv, ← zpow_neg, neg_neg, inv_one] at h2
    exact h2
  have key : leviB K ≤ centralizer {torusElt .G2 K g2ia t₁ * torusElt .G2 K g2ir t₂} := by
    rw [leviB, g2RankOne_a_eq, closure_le]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact mem_centralizer_singleton_iff.2
        (commute_of_torus_char isRoot_g2a t₁ t₂ (by decide) (by decide) hχ x)
    · exact mem_centralizer_singleton_iff.2
        (commute_of_torus_char isRoot_g2na t₁ t₂ (by decide) (by decide) hχ' x)
  exact mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (key hl)

theorem leviA_inf_J₃ : leviA K ⊓ J₃ K = ⊥ := by
  refine eq_bot_iff.2 fun h ⟨hhL, hhJ, hhc⟩ => ?_
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hhJ
  have hχr : t₁ ^ (-1 : ℤ) * t₂ ^ (2 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2r t₁ t₂ (by decide) (by decide)
      (mem_centralizer_iff.1 hhc _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hχc : t₁ ^ (1 : ℤ) * t₂ ^ (0 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2c t₁ t₂ (by decide) (by decide)
      (commute_of_mem_g2RankOne_r hhL 1).eq.symm
  rw [zpow_zero, mul_one, zpow_one] at hχc
  subst hχc
  rw [one_zpow, one_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hχr
  rw [units_eq_one_of_sq_eq_one hχr, torusElt_one, torusElt_one, mul_one]
  exact one_mem _

theorem leviB_inf_J₄ : leviB K ⊓ J₄ K = ⊥ := by
  refine eq_bot_iff.2 fun h ⟨hhL, hhJ, hhc⟩ => ?_
  obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hhJ
  have hχa : t₁ ^ (2 : ℤ) * t₂ ^ (-3 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2a t₁ t₂ (by decide) (by decide)
      (mem_centralizer_iff.1 hhc _ (mem_rootSubgroup.2 ⟨1, rfl⟩))
  have hχv : t₁ ^ (0 : ℤ) * t₂ ^ (1 : ℤ) = 1 :=
    torus_char_eq_one isRoot_g2v t₁ t₂ (by decide) (by decide)
      (commute_of_mem_g2RankOne_a hhL 1).eq.symm
  rw [zpow_zero, one_mul, zpow_one] at hχv
  subst hχv
  rw [one_zpow, mul_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hχa
  rw [units_eq_one_of_sq_eq_one hχa, torusElt_one, torusElt_one, mul_one]
  exact one_mem _

theorem D_sup_leviA_sup_J [Finite K] :
    Model.D K ⊔ leviA K ⊔ J K = Model.D K ⊔ (leviA K ⊔ J₃ K) := by
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (J_le_leviA_sup_J₃.trans le_sup_right)
  · exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_right.trans le_sup_left) (inf_le_left.trans le_sup_right))

theorem sup_leviB_sup_J [Finite K] (H : Subgroup (ModGL .G2 K)) :
    H ⊔ leviB K ⊔ J K = H ⊔ (leviB K ⊔ J₄ K) := by
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (J_le_leviB_sup_J₄.trans le_sup_right)
  · exact sup_le (le_sup_left.trans le_sup_left)
      (sup_le (le_sup_right.trans le_sup_left) (inf_le_left.trans le_sup_right))

theorem yamada_3_13_2 [Finite K] :
    adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) =
        Model.D K ⊔ (leviA K ⊔ J₃ K) ∧
      adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)) =
        Model.D K ⊔ (leviA K ⊔ J₃ K) ∧
      J₃ K ≤ centralizer (leviA K : Set (ModGL .G2 K)) ∧ leviA K ⊓ J₃ K = ⊥ :=
  ⟨adjointGroup_inf_normalizer_U.trans D_sup_leviA_sup_J,
    adjointGroup_inf_normalizer_D.trans D_sup_leviA_sup_J, J₃_le_centralizer_leviA,
    leviA_inf_J₃⟩

theorem yamada_3_13_3 [Finite K] :
    adjointGroup .G2 K ⊓ normalizer (Y K : Set (ModGL .G2 K)) = M K ⊔ (leviB K ⊔ J₄ K) ∧
      adjointGroup .G2 K ⊓ normalizer (W K : Set (ModGL .G2 K)) = M K ⊔ (leviB K ⊔ J₄ K) ∧
      adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K)) = M K ⊔ (leviB K ⊔ J₄ K) ∧
      J₄ K ≤ centralizer (leviB K : Set (ModGL .G2 K)) ∧ leviB K ⊓ J₄ K = ⊥ :=
  ⟨adjointGroup_inf_normalizer_Y.trans (sup_leviB_sup_J _),
    adjointGroup_inf_normalizer_W.trans (sup_leviB_sup_J _),
    adjointGroup_inf_normalizer_M.trans (sup_leviB_sup_J _), J₄_le_centralizer_leviB,
    leviB_inf_J₄⟩

theorem yamada_3_13_1 :
    adjointGroup .G2 K ⊓ normalizer (X K : Set (ModGL .G2 K)) = J K ⊔ S K ∧
      adjointGroup .G2 K ⊓ normalizer (Model.F K : Set (ModGL .G2 K)) = J K ⊔ S K ∧
      adjointGroup .G2 K ⊓ normalizer (S K : Set (ModGL .G2 K)) = J K ⊔ S K :=
  ⟨adjointGroup_inf_normalizer_X, adjointGroup_inf_normalizer_F,
    (adjointGroup_inf_normalizer_S (K := K)).1⟩

theorem yamada_3_15 [Finite K] :
    adjointGroup .G2 K ⊓ normalizer (rootSubgroup .G2 K g2v : Set (ModGL .G2 K)) =
      W K ⊔ (leviB K ⊔ J₄ K) :=
  adjointGroup_inf_normalizer_v.trans (sup_leviB_sup_J _)

theorem J_le_normalizer_D_sup_leviA :
    J K ≤ normalizer ((Model.D K ⊔ leviA K : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
  intro h hh
  refine mem_normalizer_sup (borelGroup_le_normalizer_D (mem_sup_left hh))
    (le_normalizer_of_conj_mem (fun h hh l hl => torus_conj_mem_g2RankOne_r hh hl) hh)

theorem J_le_normalizer_M_sup_leviB :
    J K ≤ normalizer ((M K ⊔ leviB K : Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) := by
  intro h hh
  refine mem_normalizer_sup (borelGroup_le_normalizer_M (mem_sup_left hh))
    (le_normalizer_of_conj_mem (fun h hh l hl => torus_conj_mem_g2RankOne_a hh hl) hh)

omit
  [CharP K 2] in
theorem J_comm {x y : ModGL .G2 K} (hx : x ∈ J K) (hy : y ∈ J K) : x * y = y * x :=
  mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hx) (torusGroup_le_diagonalGroup hy)

theorem yamada_3_13_4_D [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)),
        adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K))⁆ =
        Model.D K ⊔ leviA K ∧
      ⁅Model.D K ⊔ leviA K, Model.D K ⊔ leviA K⁆ = Model.D K ⊔ leviA K := by
  have hC := (even_G2_highest_long_root_centralizer K).2.2.2.1
  have hperf : ⁅Model.D K ⊔ leviA K, Model.D K ⊔ leviA K⁆ = Model.D K ⊔ leviA K := by
    have := (g2Centr184 K hK).1
    simp only [g2LongCent, g2Centralizer] at this
    rwa [hC] at this
  refine ⟨le_antisymm ?_ ?_, hperf⟩
  · rw [adjointGroup_inf_normalizer_D]
    exact commutator_sup_le_of_comm J_le_normalizer_D_sup_leviA fun a ha b hb => J_comm ha hb
  · rw [adjointGroup_inf_normalizer_D]
    calc Model.D K ⊔ leviA K = ⁅Model.D K ⊔ leviA K, Model.D K ⊔ leviA K⁆ := hperf.symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_left

theorem commutator_b_a (t : K) :
    ⁅g2N (0 : K) t 0 0 0 0, g2N 1 0 0 0 0 0⁆ = g2N 0 0 t t t (t ^ 2) := by
  rw [g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem commutator_M_sup_leviB [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅M K ⊔ leviB K, M K ⊔ leviB K⁆ = M K ⊔ leviB K := by
  set T := ⁅M K ⊔ leviB K, M K ⊔ leviB K⁆ with hT
  apply le_antisymm
  · rw [commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · have hB : leviB K ≤ T :=
      calc leviB K = ⁅leviB K, leviB K⁆ := (g2RankOne_commutator hK).symm
        _ ≤ T := commutator_mono le_sup_right le_sup_right
    have hY : Y K ≤ T := by
      rw [← commutator_M]
      exact commutator_mono le_sup_left le_sup_left
    have hxa : ∀ B : K, g2N (0 : K) B 0 0 0 0 ∈ M K ⊔ leviB K := fun B => by
      refine mem_sup_right ?_
      rw [← pinnedX_a_eq_g2N, ← xUnit_g2ia]
      exact xUnit_mem_g2RankOne g2ia B
    have hxr : ∀ A : K, g2N A (0 : K) 0 0 0 0 ∈ M K ⊔ leviB K := fun A =>
      mem_sup_left (g2N_mem_M_iff.2 rfl)
    obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    have hF : Model.F K ≤ T := by
      refine F_le_of_forall hω1 hY (fun t => ⟨t, t ^ 2, ?_⟩) fun t => ⟨t * ω ^ 2, ω * t ^ 2, ?_⟩
      · rw [← commutator_b_a]
        exact commutator_mem_commutator (hxa t) (hxr 1)
      · have h := commutator_mem_commutator (hxa (t / ω)) (hxr ω)
        rw [g2N_commutator_coords] at h
        convert h using 1
        refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
        all_goals first | ring1 | (field_simp; ring1)
    have hwb : weylElt .G2 K g2ia 1 ∈ M K ⊔ leviB K := mem_sup_right (weylElt_mem_g2RankOne _ 1)
    have hr : rootSubgroup .G2 K g2r ≤ T := by
      intro x hx
      obtain ⟨t, rfl⟩ := mem_rootSubgroup.1 hx
      have h1 : g2N (0 : K) 0 t t t (t ^ 2) ∈ T := by
        rw [← commutator_b_a]
        exact commutator_mem_commutator (hxa t) (hxr 1)
      have h2 := (mem_normalizer_iff.1 (le_normalizer_commutator _ hwb) _).1 h1
      rw [weylElt_a_conj_g2N] at h2
      have h3 : g2N (0 : K) 0 0 t (t ^ 2) t ∈ T := hF (g2N_mem_F_iff.2 ⟨rfl, rfl⟩)
      have e : pinnedX .G2 K g2r t = g2N t 0 0 t (0 * t ^ 2 + t ^ 2) (0 ^ 2 * t + t) *
          g2N 0 0 0 t (t ^ 2) t := by
        rw [pinnedX_r_eq_g2N, g2N_mul_coords]
        refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
      rw [e]
      exact mul_mem h2 h3
    refine sup_le ?_ hB
    rw [← rootSubgroup_r_sup_F]
    exact sup_le hr hF

theorem yamada_3_13_4_M [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K)),
        adjointGroup .G2 K ⊓ normalizer (M K : Set (ModGL .G2 K))⁆ = M K ⊔ leviB K ∧
      ⁅M K ⊔ leviB K, M K ⊔ leviB K⁆ = M K ⊔ leviB K := by
  have hperf := commutator_M_sup_leviB hK
  refine ⟨le_antisymm ?_ ?_, hperf⟩
  · rw [adjointGroup_inf_normalizer_M]
    exact commutator_sup_le_of_comm J_le_normalizer_M_sup_leviB fun a ha b hb => J_comm ha hb
  · rw [adjointGroup_inf_normalizer_M]
    calc M K ⊔ leviB K = ⁅M K ⊔ leviB K, M K ⊔ leviB K⁆ := hperf.symm
      _ ≤ _ := commutator_mono le_sup_left le_sup_left

theorem adjointGroup_inf_centralizer_W [Finite K] :
    adjointGroup .G2 K ⊓ centralizer (W K : Set (ModGL .G2 K)) = W K := by
  apply le_antisymm
  · rintro g ⟨hg, hgc⟩
    have hv : g ∈ ((adjointGroup .G2 K ⊓ centralizer {pinnedX .G2 K g2v 1} :
        Subgroup (ModGL .G2 K)) : Set (ModGL .G2 K)) :=
      ⟨hg, mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 hgc _ (pinnedX_v_mem_g2ShortRadical 1)).symm⟩
    rw [(even_G2_highest_short_root_centralizer K).2.2.2.2.1] at hv
    obtain ⟨w, hw, l, hl, rfl⟩ := Set.mem_mul.1 hv
    have hlc : l ∈ centralizer (g2BCGroup K : Set (ModGL .G2 K)) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := mem_centralizer_iff.1 hgc y (Y_le_W hy)
      have h2 := (commute_of_mem_g2ShortRadical (Y_le_W hy) hw).eq
      calc y * l = w⁻¹ * (y * (w * l)) := by rw [← mul_assoc y w, h2]; group
        _ = w⁻¹ * (w * l * y) := by rw [h1]
        _ = l * y := by group
    rw [AS81.G2.eq_one_of_mem_g2RankOne_of_centralizes hl hlc, mul_one]
    exact hw
  · intro x hx
    exact ⟨W_le_adjointGroup hx, mem_centralizer_iff.2 fun y hy =>
      (commute_of_mem_g2ShortRadical hy hx).eq⟩

theorem commute_of_mem_X {x y : ModGL .G2 K} (hx : x ∈ X K) (hy : y ∈ X K) : x * y = y * x := by
  obtain ⟨c, e, f, rfl⟩ := mem_X.1 hx
  obtain ⟨c', e', f', rfl⟩ := mem_X.1 hy
  rw [g2N_mul_coords, g2N_mul_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem adjointGroup_inf_centralizer_X :
    adjointGroup .G2 K ⊓ centralizer (X K : Set (ModGL .G2 K)) = X K := by
  apply le_antisymm
  · rintro g ⟨hg, hgc⟩
    have hgB : g ∈ borelGroup .G2 K := by
      rw [← adjointGroup_inf_normalizer_X]
      exact ⟨hg, centralizer_le_normalizer _ hgc⟩
    obtain ⟨h, hh, u, hu, rfl⟩ := exists_torus_mul_of_mem_borel hgB
    obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hu
    obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆, hc⟩ := exists_torus_conj_g2N hh
    have key : ∀ x ∈ X K, h * (g2N A B C D E F * x * (g2N A B C D E F)⁻¹) * h⁻¹ = x :=
      fun x hx => by
        have := mem_centralizer_iff.1 hgc x hx
        calc h * (g2N A B C D E F * x * (g2N A B C D E F)⁻¹) * h⁻¹ =
            (h * g2N A B C D E F) * x * (h * g2N A B C D E F)⁻¹ := by group
          _ = x := by rw [← this]; group
    have hu1 := key _ (g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩ : g2N 0 0 (1 : K) 0 0 0 ∈ X K)
    have hb1 := key _ (g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩ : g2N 0 0 0 0 (1 : K) 0 ∈ X K)
    rw [g2N_conj_coords, hc] at hu1 hb1
    obtain ⟨-, -, -, -, hu5, hu6⟩ := g2N_injective hu1
    obtain ⟨-, -, -, -, -, hb6⟩ := g2N_injective hb1
    have hB : B = 0 := by simpa using hb6
    have hA : A = 0 := by simpa using hu5
    subst hA hB
    have hD : D = 0 := by simpa using hu6
    subst hD
    have huX : g2N (0 : K) 0 C 0 E F ∈ X K := g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
    have hhc : ∀ x ∈ X K, x * h = h * x := fun x hx => by
      have h1 := mem_centralizer_iff.1 hgc x hx
      have h2 := commute_of_mem_X hx huX
      calc x * h = x * (h * g2N 0 0 C 0 E F) * (g2N 0 0 C 0 E F)⁻¹ := by group
        _ = h * g2N 0 0 C 0 E F * x * (g2N 0 0 C 0 E F)⁻¹ := by rw [h1]
        _ = h * (x * g2N 0 0 C 0 E F) * (g2N 0 0 C 0 E F)⁻¹ := by rw [mul_assoc h, ← h2]
        _ = h * x := by group
    obtain ⟨t₁, t₂, rfl⟩ := exists_eq_torusElt_mul hh
    have hχc : t₁ ^ (1 : ℤ) * t₂ ^ (0 : ℤ) = 1 :=
      torus_char_eq_one isRoot_g2c t₁ t₂ (by decide) (by decide)
        (hhc _ (by rw [pinnedX_c_eq_g2N]; exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩))
    have hχu : t₁ ^ (1 : ℤ) * t₂ ^ (-1 : ℤ) = 1 :=
      torus_char_eq_one isRoot_g2u t₁ t₂ (by decide) (by decide)
        (hhc _ (by rw [pinnedX_u_eq_g2N]; exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩))
    rw [zpow_zero, mul_one, zpow_one] at hχc
    subst hχc
    rw [one_zpow, one_mul, zpow_neg_one, inv_eq_one] at hχu
    subst hχu
    rw [torusElt_one, torusElt_one, mul_one, one_mul]
    exact huX
  · intro x hx
    exact ⟨X_le_adjointGroup hx, mem_centralizer_iff.2 fun y hy => commute_of_mem_X hy hx⟩

end Model

namespace Model


variable {K : Type} [Field K] [CharP K 2]

theorem mem_map_wa_W {B C F : K} :
    g2N 0 B C 0 0 F ∈ (W K).map (MulAut.conj (wa K)).toMonoidHom := by
  refine ⟨g2N 0 0 0 C B F, g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wa]
  rw [weylElt_r_conj_g2N]
  refine g2N_eq_g2N rfl rfl rfl rfl rfl ?_
  ring

theorem mem_map_wb_X {A E F : K} :
    g2N A 0 0 0 E F ∈ (X K).map (MulAut.conj (wb K)).toMonoidHom := by
  refine ⟨g2N 0 0 A 0 F E, g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wb]
  rw [weylElt_a_conj_g2N]
  refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;> ring

theorem map_wa_W_le_S : (W K).map (MulAut.conj (wa K)).toMonoidHom ≤ S K := by
  rintro _ ⟨_, ⟨D, E, F, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wa]
  rw [weylElt_r_conj_g2N]
  exact mem_S.2 ⟨_, _, _, _, _, _, rfl⟩

theorem map_wb_X_le_S : (X K).map (MulAut.conj (wb K)).toMonoidHom ≤ S K := by
  rintro _ ⟨_, ⟨C, E, F, rfl⟩, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, wb]
  rw [weylElt_a_conj_g2N]
  exact mem_S.2 ⟨_, _, _, _, _, _, rfl⟩

theorem S_le_sup_conj : S K ≤ W K ⊔ (W K).map (MulAut.conj (wa K)).toMonoidHom ⊔
    (X K).map (MulAut.conj (wb K)).toMonoidHom := by
  intro g hg
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hg
  have h : g2N A B C D E F = g2N A 0 0 0 0 0 * g2N 0 B C 0 0 0 * g2N 0 0 0 D E F := by
    rw [g2N_mul_coords, g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  rw [h]
  exact mul_mem (mul_mem (mem_sup_right mem_map_wb_X) (mem_sup_left (mem_sup_right mem_map_wa_W)))
    (mem_sup_left (mem_sup_left (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)))

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Rank

variable [CharP K 2] [Finite K]

include d in
theorem card_le_cube {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) {E : Subgroup G}
    (hEL : E ≤ L) (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ Nat.card K ^ 3 := by
  set Γ := E.comap d.emb with hΓ
  have hmap : Γ.map d.emb = E := map_comap_eq_self (by rw [d.range_emb]; exact hEL)
  have hc : Nat.card Γ = Nat.card E := by rw [← hmap, card_map_of_injective d.emb_injective]
  rw [← hc]
  have := hE.1
  refine Quasithin.B45G2.card_le_cube_adjointGroup hK hn (fun g hg => ?_) fun g hg h hh => ?_
  · apply d.emb_injective
    rw [map_mul, map_one, ← sq]
    exact hE.2 _ hg
  · apply d.emb_injective
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (mul_comm' (⟨d.emb g, hg⟩ : E) ⟨d.emb h, hh⟩)

include d in
theorem pRank_eq_of_le [Finite G] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {H E : Subgroup G} (hEH : E ≤ H) (hHL : H ≤ L) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : Nat.card E = Nat.card K ^ 3) : CFSG.Open.pRank 2 H = 3 * n := by
  apply le_antisymm
  · refine SectionRank.pRank_le one_lt_two fun E' hE'H hE' => ?_
    calc Nat.card E' ≤ Nat.card K ^ 3 := d.card_le_cube hK hn (hE'H.trans hHL) hE'
      _ = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  · refine SectionRank.le_pRank one_lt_two hEH hE ?_
    rw [hcard, hK, ← pow_mul, mul_comm]

theorem pRank_S [Finite G] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    CFSG.Open.pRank 2 d.S = 3 * n ∧ CFSG.Open.pRank 2 L = 3 * n := by
  have hW := isElemAbelian_of_isElementaryAbelian d.isElementaryAbelian.2.2.2
  have hWS : d.W ≤ d.S := d.image_mono Model.W_le_S
  exact ⟨d.pRank_eq_of_le hK hn hWS (d.image_le _) hW d.cards.2.2.2.1,
    d.pRank_eq_of_le hK hn (hWS.trans (d.image_le _)) le_rfl hW d.cards.2.2.2.1⟩

omit
  [CharP K 2] [Finite K] in
theorem emb_wa_wb : d.emb ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩ = d.wa ∧
    d.emb ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩ = d.wb := ⟨rfl, rfl⟩

omit [Finite K] in
theorem image_conj : d.image ((Model.W K).map (MulAut.conj (Model.wa K)).toMonoidHom) =
      d.W.map (MulAut.conj d.wa).toMonoidHom ∧
    d.image ((Model.X K).map (MulAut.conj (Model.wb K)).toMonoidHom) =
      d.X.map (MulAut.conj d.wb).toMonoidHom :=
  ⟨d.image_map_conj ⟨Model.wa K, Model.wa_mem_adjointGroup K⟩ _,
    d.image_map_conj ⟨Model.wb K, Model.wb_mem_adjointGroup K⟩ _⟩

theorem rankThompson_S [Finite G] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) :
    rankThompson d.S = d.S := by
  have hS := (d.pRank_S hK hn).1
  have hW := isElemAbelian_of_isElementaryAbelian d.isElementaryAbelian.2.2.2
  have hX := isElemAbelian_of_isElementaryAbelian d.isElementaryAbelian.2.2.1
  have hcW := d.cards.2.2.2.1
  have hcX := d.cards.2.2.1
  have hWS : d.W ≤ d.S := d.image_mono Model.W_le_S
  have hW'S : d.W.map (MulAut.conj d.wa).toMonoidHom ≤ d.S := by
    rw [← d.image_conj.1]
    exact d.image_mono Model.map_wa_W_le_S
  have hX'S : d.X.map (MulAut.conj d.wb).toMonoidHom ≤ d.S := by
    rw [← d.image_conj.2]
    exact d.image_mono Model.map_wb_X_le_S
  have hSL : d.S ≤ L := d.image_le _
  have key : ∀ A : Subgroup G, A ≤ d.S → CFSG.Open.IsElemAbelian 2 A →
      Nat.card A = Nat.card K ^ 3 → A ≤ rankThompson d.S := fun A hAS hA hcA => by
    refine le_iSup₂_of_le A ⟨hAS, hA.1, ?_⟩ le_rfl
    rw [hS, d.pRank_eq_of_le hK hn le_rfl (hAS.trans hSL) hA hcA]
  apply le_antisymm
  · exact iSup₂_le fun A hA => hA.1
  · have hle : d.S ≤ d.W ⊔ d.W.map (MulAut.conj d.wa).toMonoidHom ⊔
        d.X.map (MulAut.conj d.wb).toMonoidHom := by
      have h := d.image_mono Model.S_le_sup_conj
      rwa [d.image_sup (sup_le Model.W_le_adjointGroup
          (Model.map_wa_W_le_S.trans (Model.S_le_adjointGroup K)))
          (Model.map_wb_X_le_S.trans (Model.S_le_adjointGroup K)),
        d.image_sup Model.W_le_adjointGroup
          (Model.map_wa_W_le_S.trans (Model.S_le_adjointGroup K)), d.image_conj.1,
        d.image_conj.2] at h
    refine hle.trans (sup_le (sup_le (key _ hWS hW hcW) ?_) ?_)
    · obtain ⟨h1, h2⟩ := isElemAbelian_map_conj hW d.wa
      exact key _ hW'S h1 (h2.trans hcW)
    · obtain ⟨h1, h2⟩ := isElemAbelian_map_conj hX d.wb
      exact key _ hX'S h1 (h2.trans hcX)

end Rank

end G2Data

namespace Model


variable {K : Type} [Field K] [CharP K 2]

theorem wb_conj_M (A C D E F : K) :
    weylElt .G2 K g2ia 1 * g2N A 0 C D E F * weylElt .G2 K g2ia 1 =
      g2N C 0 A D (A * C ^ 2 + F) (A ^ 2 * C + E) := by
  have := weylElt_a_conj_g2N A C D E F
  rwa [UnbalancedCatalog.weylElt_inv] at this

theorem conj_na_eq (s : K) (x : ModGL .G2 K) :
    pinnedX .G2 K g2na s * x * (pinnedX .G2 K g2na s)⁻¹ =
      weylElt .G2 K g2ia 1 * (pinnedX .G2 K g2a s * (weylElt .G2 K g2ia 1 * x *
        weylElt .G2 K g2ia 1) * pinnedX .G2 K g2a s) * weylElt .G2 K g2ia 1 := by
  rw [pinnedX_na_eq]
  simp only [mul_inv_rev, UnbalancedCatalog.weylElt_inv, pinnedX_inv_eq]
  group

theorem conj_na_M (s A C D E F : K) : ∃ D' E' F' : K,
    pinnedX .G2 K g2na s * g2N A 0 C D E F * (pinnedX .G2 K g2na s)⁻¹ =
      g2N (A + s * C) 0 C D' E' F' := by
  rw [conj_na_eq, wb_conj_M, conj_a, wb_conj_M]
  exact ⟨_, _, _, g2N_eq_g2N (by ring) rfl rfl rfl rfl rfl⟩

theorem conj_na_Y (s e f : K) :
    pinnedX .G2 K g2na s * g2N 0 0 0 0 e f * (pinnedX .G2 K g2na s)⁻¹ =
      g2N 0 0 0 0 (e + s * f) f := by
  rw [conj_na_eq, wb_conj_M, conj_a, wb_conj_M]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem conj_a_Y (s e f : K) :
    pinnedX .G2 K g2a s * g2N 0 0 0 0 e f * (pinnedX .G2 K g2a s)⁻¹ =
      g2N 0 0 0 0 e (f + s * e) := by
  rw [pinnedX_inv_eq, conj_a]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem conj_a_M (s A C D E F : K) : ∃ D' E' F' : K,
    pinnedX .G2 K g2a s * g2N A 0 C D E F * (pinnedX .G2 K g2a s)⁻¹ =
      g2N A 0 (C + s * A) D' E' F' := by
  rw [pinnedX_inv_eq, conj_a]
  exact ⟨_, _, _, g2N_eq_g2N rfl rfl (by ring) rfl rfl rfl⟩

theorem uSL_inv (s : K) : (uSL s)⁻¹ = uSL s := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, CharTwo.neg_eq]

theorem vSL_inv (s : K) : (vSL s)⁻¹ = vSL s := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_vSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, CharTwo.neg_eq]

theorem SL2_induction_uv {p : SL2 K → Prop} (h1 : p 1)
    (hu : ∀ s g, p g → p (uSL s * g)) (hv : ∀ s g, p g → p (vSL s * g)) (g : SL2 K) : p g := by
  have hg : g ∈ closure (Set.range (uSL (K := K)) ∪ Set.range vSL) := by
    rw [show closure (Set.range (uSL (K := K)) ∪ Set.range vSL) = ⊤ from
      LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    trivial
  induction hg using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left x hx y _ ih =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · exact hu s y ih
    · exact hv s y ih
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [uSL_inv]
      exact hu s y ih
    · rw [vSL_inv]
      exact hv s y ih

theorem conj_Y_of_uv {ρ : SL2 K →* ModGL .G2 K} (hu : ∀ s, ρ (uSL s) = pinnedX .G2 K g2a s)
    (hv : ∀ s, ρ (vSL s) = pinnedX .G2 K g2na s) (g : SL2 K) (v : Fin 2 → K) :
    ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ g)⁻¹ =
      g2N 0 0 0 0 ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 1)
        ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 0) := by
  revert v
  induction g using SL2_induction_uv with
  | h1 => intro v; simp
  | hu s g ih =>
    intro v
    rw [map_mul, show ρ (uSL s) * ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ (uSL s) * ρ g)⁻¹ =
      ρ (uSL s) * (ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ g)⁻¹) * (ρ (uSL s))⁻¹ by group, ih, hu,
      conj_a_Y, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;>
      simp [coe_uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | hv s g ih =>
    intro v
    rw [map_mul, show ρ (vSL s) * ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ (vSL s) * ρ g)⁻¹ =
      ρ (vSL s) * (ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ g)⁻¹) * (ρ (vSL s))⁻¹ by group, ih, hv,
      conj_na_Y, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    refine g2N_eq_g2N rfl rfl rfl rfl ?_ ?_ <;>
      simp [coe_vSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem conj_M_of_uv {ρ : SL2 K →* ModGL .G2 K} (hu : ∀ s, ρ (uSL s) = pinnedX .G2 K g2a s)
    (hv : ∀ s, ρ (vSL s) = pinnedX .G2 K g2na s) (g : SL2 K) (v : Fin 2 → K) (D E F : K) :
    ∃ D' E' F' : K, ρ g * g2N (v 1) 0 (v 0) D E F * (ρ g)⁻¹ =
      g2N ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 1) 0
        ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 0) D' E' F' := by
  revert v D E F
  induction g using SL2_induction_uv with
  | h1 => intro v D E F; exact ⟨D, E, F, by simp⟩
  | hu s g ih =>
    intro v D E F
    obtain ⟨D₁, E₁, F₁, h₁⟩ := ih v D E F
    obtain ⟨D₂, E₂, F₂, h₂⟩ := conj_a_M s _ _ D₁ E₁ F₁
    refine ⟨D₂, E₂, F₂, ?_⟩
    rw [map_mul, show ρ (uSL s) * ρ g * g2N (v 1) 0 (v 0) D E F * (ρ (uSL s) * ρ g)⁻¹ =
      ρ (uSL s) * (ρ g * g2N (v 1) 0 (v 0) D E F * (ρ g)⁻¹) * (ρ (uSL s))⁻¹ by group, h₁, hu,
      h₂, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    refine g2N_eq_g2N ?_ rfl ?_ rfl rfl rfl <;>
      simp [coe_uSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  | hv s g ih =>
    intro v D E F
    obtain ⟨D₁, E₁, F₁, h₁⟩ := ih v D E F
    obtain ⟨D₂, E₂, F₂, h₂⟩ := conj_na_M s _ _ D₁ E₁ F₁
    refine ⟨D₂, E₂, F₂, ?_⟩
    rw [map_mul, show ρ (vSL s) * ρ g * g2N (v 1) 0 (v 0) D E F * (ρ (vSL s) * ρ g)⁻¹ =
      ρ (vSL s) * (ρ g * g2N (v 1) 0 (v 0) D E F * (ρ g)⁻¹) * (ρ (vSL s))⁻¹ by group, h₁, hv,
      h₂, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
    refine g2N_eq_g2N ?_ rfl ?_ rfl rfl rfl <;>
      simp [coe_vSL, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem natural_Y [Finite K] :
    ∃ ρ : SL2 K →* ModGL .G2 K, ρ.range = leviB K ∧ Function.Injective ρ ∧
      (∀ s, ρ (uSL s) = pinnedX .G2 K g2a s) ∧ (∀ s, ρ (vSL s) = pinnedX .G2 K g2na s) ∧
      ∀ (g : SL2 K) (v : Fin 2 → K), ρ g * g2N 0 0 0 0 (v 1) (v 0) * (ρ g)⁻¹ =
        g2N 0 0 0 0 ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 1)
          ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 0) := by
  obtain ⟨ρ, hu, hv, hrange, hinj⟩ := (even_G2_highest_short_root_centralizer K).2.2.2.2.2.2.2.1
  exact ⟨ρ, hrange, hinj, hu, hv, conj_Y_of_uv hu hv⟩

theorem natural_M_mod_W [Finite K] :
    ∃ ρ : SL2 K →* ModGL .G2 K, ρ.range = leviB K ∧ Function.Injective ρ ∧
      (∀ s, ρ (uSL s) = pinnedX .G2 K g2a s) ∧ (∀ s, ρ (vSL s) = pinnedX .G2 K g2na s) ∧
      ∀ (g : SL2 K) (v : Fin 2 → K) (D E F : K), ∃ D' E' F' : K,
        ρ g * g2N (v 1) 0 (v 0) D E F * (ρ g)⁻¹ =
          g2N ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 1) 0
            ((Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v) 0) D' E' F' := by
  obtain ⟨ρ, hu, hv, hrange, hinj⟩ := (even_G2_highest_short_root_centralizer K).2.2.2.2.2.2.2.1
  exact ⟨ρ, hrange, hinj, hu, hv, conj_M_of_uv hu hv⟩

theorem g2N_inv_mul_mem_W (A C D E F D' E' F' : K) :
    (g2N A 0 C D E F)⁻¹ * g2N A 0 C D' E' F' ∈ W K := by
  rw [g2N_inv_coords, g2N_mul_coords, g2N_mem_W_iff]
  refine ⟨?_, ?_, ?_⟩ <;> char2_ring

theorem g2N_mul_M (A C D E F a c d e f : K) : ∃ D' E' F' : K,
    g2N A 0 C D E F * g2N a 0 c d e f = g2N (A + a) 0 (C + c) D' E' F' := by
  rw [g2N_mul_coords]
  exact ⟨_, _, _, g2N_eq_g2N rfl (by ring) (by ring) rfl rfl rfl⟩

omit
  [CharP K 2] in
theorem pinnedX_mem_leviB (s : K) :
    pinnedX .G2 K g2a s ∈ leviB K ∧ pinnedX .G2 K g2na s ∈ leviB K := by
  rw [leviB, g2RankOne_a_eq]
  exact ⟨subset_closure (Or.inl ⟨s, rfl⟩), subset_closure (Or.inr ⟨s, rfl⟩)⟩

theorem Y_irreducible {E : Subgroup (ModGL .G2 K)} (hEY : E ≤ Y K)
    (hN : leviB K ≤ normalizer (E : Set (ModGL .G2 K))) : E = ⊥ ∨ E = Y K := by
  by_cases hE : E = ⊥
  · exact Or.inl hE
  right
  apply le_antisymm hEY
  obtain ⟨⟨y, hyE⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
  obtain ⟨e, f, rfl⟩ := hEY hyE
  have hyne : e ≠ 0 ∨ f ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hy1 (Subtype.ext g2N_zero)
  have hstep : ∀ {e f : K}, g2N 0 0 0 0 e f ∈ E → ∀ s : K,
      g2N 0 0 0 0 0 (s * e) ∈ E ∧ g2N 0 0 0 0 (s * f) 0 ∈ E := fun {e f} h s => by
    have h1 := (mem_normalizer_iff.1 (hN (pinnedX_mem_leviB s).1) _).1 h
    have h2 := (mem_normalizer_iff.1 (hN (pinnedX_mem_leviB s).2) _).1 h
    rw [conj_a_Y] at h1
    rw [conj_na_Y] at h2
    refine ⟨?_, ?_⟩
    · convert mul_mem h1 (inv_mem h) using 1
      rw [g2N_inv_coords, g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
    · convert mul_mem h2 (inv_mem h) using 1
      rw [g2N_inv_coords, g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
  have hc : (∀ z : K, g2N 0 0 0 0 0 z ∈ E) → Y K ≤ E := fun hc => by
    refine Y_le_of_forall (fun z => ?_) hc
    have := (hstep (hc 1) z).2
    rwa [mul_one] at this
  rcases hyne with he | hf
  · exact hc fun z => by
      have := (hstep hyE (z / e)).1
      rwa [div_mul_cancel₀ z he] at this
  · have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ E := fun z => by
      have := (hstep hyE (z / f)).2
      rwa [div_mul_cancel₀ z hf] at this
    exact hc fun z => by
      have := (hstep (hb 1) z).1
      rwa [mul_one] at this

theorem mem_of_mod_W {E : Subgroup (ModGL .G2 K)} (hWE : W K ≤ E) :
    (∀ {x : ModGL .G2 K} {c : K}, x ∈ E → (∃ d e f : K, x = g2N 0 0 c d e f) →
      g2N 0 0 c 0 0 0 ∈ E) ∧
    ∀ {x : ModGL .G2 K} {a : K}, x ∈ E → (∃ d e f : K, x = g2N a 0 0 d e f) →
      g2N a 0 0 0 0 0 ∈ E := by
  refine ⟨fun {x c} hx ⟨d, e, f, hxe⟩ => ?_, fun {x a} hx ⟨d, e, f, hxe⟩ => ?_⟩
  · subst hxe
    convert mul_mem hx (hWE (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩ :
      g2N (0 : K) 0 0 d e f ∈ W K)) using 1
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
  · subst hxe
    convert mul_mem hx (hWE (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩ :
      g2N (0 : K) 0 0 d e f ∈ W K)) using 1
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring

theorem M_mod_W_irreducible {E : Subgroup (ModGL .G2 K)} (hWE : W K ≤ E) (hEM : E ≤ M K)
    (hN : leviB K ≤ normalizer (E : Set (ModGL .G2 K))) : E = W K ∨ E = M K := by
  by_cases hE : E ≤ W K
  · exact Or.inl (le_antisymm hE hWE)
  right
  apply le_antisymm hEM
  obtain ⟨x, hxE, hxW⟩ := Set.not_subset.1 hE
  obtain ⟨A, C, D, E', F, rfl⟩ := mem_M.1 (hEM hxE)
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hxW (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)
  obtain ⟨hmodu, hmodr⟩ := mem_of_mod_W hWE
  have hstep : ∀ {a c d e f : K}, g2N a 0 c d e f ∈ E → ∀ s : K,
      g2N 0 0 (s * a) 0 0 0 ∈ E ∧ g2N (s * c) 0 0 0 0 0 ∈ E := fun {a c d e f} h s => by
    obtain ⟨D₁, E₁, F₁, h₁⟩ := conj_a_M s a c d e f
    obtain ⟨D₂, E₂, F₂, h₂⟩ := conj_na_M s a c d e f
    have m₁ := (mem_normalizer_iff.1 (hN (pinnedX_mem_leviB s).1) _).1 h
    have m₂ := (mem_normalizer_iff.1 (hN (pinnedX_mem_leviB s).2) _).1 h
    rw [h₁] at m₁
    rw [h₂] at m₂
    have p₁ := mul_mem m₁ (inv_mem h)
    have p₂ := mul_mem m₂ (inv_mem h)
    rw [g2N_inv_coords, g2N_mul_coords] at p₁ p₂
    exact ⟨hmodu p₁ ⟨_, _, _, g2N_eq_g2N (by char2_ring) (by char2_ring) (by char2_ring) rfl rfl
      rfl⟩, hmodr p₂ ⟨_, _, _, g2N_eq_g2N (by char2_ring) (by char2_ring) (by char2_ring) rfl
      rfl rfl⟩⟩
  have hu : (∀ z : K, g2N 0 0 z 0 0 0 ∈ E) → (∀ z : K, g2N z 0 0 0 0 0 ∈ E) → M K ≤ E :=
    fun hu hr => by
      rw [← rootSubgroup_r_sup_F, ← X_sup_W, ← rootSubgroup_u_sup_Y]
      refine sup_le (fun g hg => ?_) (sup_le (sup_le (fun g hg => ?_) (Y_le_W.trans hWE)) hWE)
      · obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
        rw [pinnedX_r_eq_g2N]
        exact hr z
      · obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
        rw [pinnedX_u_eq_g2N]
        exact hu z
  rcases hAC with hA | hC
  · have hu' : ∀ z : K, g2N 0 0 z 0 0 0 ∈ E := fun z => by
      have := (hstep hxE (z / A)).1
      rwa [div_mul_cancel₀ z hA] at this
    refine hu hu' fun z => ?_
    have := (hstep (hu' 1) z).2
    rwa [mul_one] at this
  · have hr' : ∀ z : K, g2N z 0 0 0 0 0 ∈ E := fun z => by
      have := (hstep hxE (z / C)).2
      rwa [div_mul_cancel₀ z hC] at this
    refine hu (fun z => ?_) hr'
    have := (hstep (hr' 1) z).1
    rwa [mul_one] at this

omit
  [CharP K 2] in
theorem pinnedX_r_mem_leviA (s : K) : pinnedX .G2 K g2r s ∈ leviA K := by
  rw [leviA, g2RankOne_r_eq]
  exact subset_closure (Or.inl ⟨s, rfl⟩)

theorem commutator_r_D (s B C D E F : K) :
    ⁅pinnedX .G2 K g2r s, g2N 0 B C D E F⁆ =
      g2N 0 0 (s * B) (s ^ 2 * B) (s ^ 3 * B + s ^ 2 * C + s * D)
        (s ^ 2 * B * C + s * B * D + s * C ^ 2) := by
  rw [pinnedX_r_eq_g2N, g2N_commutator_coords]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

theorem D_mod_U_of_steps [Finite K] (hK : 4 ≤ Nat.card K) {E : Subgroup (ModGL .G2 K)}
    (hUE : U K ≤ E) (hED : E ≤ Model.D K)
    (hNr : ∀ s : K, pinnedX .G2 K g2r s ∈ normalizer (E : Set (ModGL .G2 K)))
    (hNw : weylElt .G2 K g2ir 1 ∈ normalizer (E : Set (ModGL .G2 K)))
    (hYstep : ∀ e f : K, e ≠ 0 → g2N 0 0 0 0 e f ∈ E → Y K ≤ E) :
    E = U K ∨ E = Model.D K := by
  by_cases hE : E ≤ U K
  · exact Or.inl (le_antisymm hE hUE)
  right
  apply le_antisymm hED
  obtain ⟨x, hxE, hxU⟩ := Set.not_subset.1 hE
  obtain ⟨B, C, D, E', F, rfl⟩ := mem_D.1 (hED hxE)
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  have hω : ω + 1 ≠ 0 := fun h => hω1 ((CharTwo.add_eq_zero).1 h)
  have hcomm : ∀ (s : K) {y : ModGL .G2 K}, y ∈ E → ⁅pinnedX .G2 K g2r s, y⁆ ∈ E :=
    fun s _ hy => commutatorElement_mem_of_mem_normalizer (hNr s) hy
  have h1 : ∃ e f : K, e ≠ 0 ∧ g2N 0 0 0 0 e f ∈ E := by
    by_cases hB : B = 0
    · subst hB
      by_cases hCD : C = 0 ∧ D = 0
      · obtain ⟨rfl, rfl⟩ := hCD
        refine ⟨E', F, fun h => hxU (g2N_mem_U_iff.2 ⟨rfl, rfl, rfl, rfl, h⟩), hxE⟩
      · have hs : ∃ s : K, s ≠ 0 ∧ s ^ 2 * C + s * D ≠ 0 := by
          by_cases hC : C = 0
          · subst hC
            have hD : D ≠ 0 := fun hD => hCD ⟨rfl, hD⟩
            exact ⟨1, one_ne_zero, by simpa using hD⟩
          · obtain ⟨s, hs0, hs1⟩ := exists_ne_ne (by omega) 0 (D / C)
            refine ⟨s, hs0, fun h => hs1 ?_⟩
            have h' : s * (s * C + D) = 0 := by linear_combination h
            have h'' : s * C + D = 0 := (mul_eq_zero.1 h').resolve_left hs0
            field_simp
            exact CharTwo.add_eq_zero.1 h''
        obtain ⟨s, -, hs⟩ := hs
        have := hcomm s hxE
        rw [commutator_r_D] at this
        refine ⟨_, s * C ^ 2, hs, ?_⟩
        convert this using 1
        refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · have h₁ := hcomm 1 hxE
      rw [commutator_r_D] at h₁
      have h₂ := hcomm ω h₁
      rw [pinnedX_r_eq_g2N, g2N_commutator_coords] at h₂
      refine ⟨ω ^ 2 * B + ω * B, ω * B ^ 2, ?_, ?_⟩
      · have : ω ^ 2 * B + ω * B = ω * (ω + 1) * B := by ring
        rw [this]
        exact mul_ne_zero (mul_ne_zero hω0 hω) hB
      · convert h₂ using 1
        refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  obtain ⟨e, f, he, hyE⟩ := h1
  have hY : Y K ≤ E := hYstep e f he hyE
  have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ E := fun z => hY (g2N_mem_Y_iff.2 ⟨rfl, rfl, rfl, rfl⟩)
  have ha : ∀ z : K, g2N 0 z 0 0 0 0 ∈ E := by
    intro z
    have := (mem_normalizer_iff.1 hNw _).1 (hb z)
    rw [← pinnedX_b_eq_g2N, weylElt_conj g2ir isRoot_g2b, reflect_r_b, pinnedX_a_eq_g2N] at this
    exact this
  have hF : Model.F K ≤ E := by
    refine F_le_of_forall hω1 hY (fun t => ⟨t, 0, ?_⟩) fun t => ⟨ω ^ 2 * t, 0, ?_⟩
    · have := hcomm 1 (ha t)
      rw [commutator_r_D] at this
      convert this using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    · have := hcomm ω (ha (t / ω))
      rw [commutator_r_D] at this
      convert this using 1
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
      all_goals first | ring1 | (field_simp; ring1) | field_simp
  rw [← rootSubgroup_a_sup_F]
  refine sup_le (fun g hg => ?_) hF
  obtain ⟨z, rfl⟩ := mem_rootSubgroup.1 hg
  rw [pinnedX_a_eq_g2N]
  exact ha z

theorem D_mod_U_irreducible [Finite K] (hK : 4 ≤ Nat.card K) {E : Subgroup (ModGL .G2 K)}
    (hUE : U K ≤ E) (hED : E ≤ Model.D K)
    (hN : adjointGroup .G2 K ⊓ normalizer (U K : Set (ModGL .G2 K)) ≤
      normalizer (E : Set (ModGL .G2 K))) : E = U K ∨ E = Model.D K := by
  rw [adjointGroup_inf_normalizer_U] at hN
  have hNJ : ∀ h ∈ J K, h ∈ normalizer (E : Set (ModGL .G2 K)) := fun h hh => hN (mem_sup_right hh)
  refine D_mod_U_of_steps hK hUE hED (fun s => hN (mem_sup_left (mem_sup_right
    (pinnedX_r_mem_leviA s)))) (hN (mem_sup_left (mem_sup_right
      (weylElt_mem_g2RankOne g2ir 1)))) fun e f he hyE => ?_
  have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ E := by
    intro z
    by_cases hz : z = 0
    · rw [hz, g2N_zero]
      exact one_mem _
    set t : Kˣ := Units.mk0 (e / z) (div_ne_zero he hz) with ht
    have hdJ : torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1 ∈ J K :=
      mul_mem (torusElt_mem_torusGroup _ _) (torusElt_mem_torusGroup _ _)
    have hm := (mem_normalizer_iff.1 (hNJ _ hdJ) _).1 hyE
    have hy : g2N (0 : K) 0 0 0 e f = pinnedX .G2 K g2b e * pinnedX .G2 K g2c f := by
      rw [pinnedX_b_eq_g2N, pinnedX_c_eq_g2N, g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
    have e1 : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1 * (a * b) *
        (torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1)⁻¹ =
        (torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1 * a *
          (torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1)⁻¹) *
        (torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1 * b *
          (torusElt .G2 K g2ia t * torusElt .G2 K g2ir 1)⁻¹) := fun a b => by group
    rw [hy, e1, torus_conj_of (m₁ := -1) (m₂ := 3) isRoot_g2b t 1 (by decide) (by decide),
      torus_conj_of (m₁ := 1) (m₂ := 0) isRoot_g2c t 1 (by decide) (by decide)] at hm
    have hc : pinnedX .G2 K g2c (((t ^ (1 : ℤ) * (1 : Kˣ) ^ (0 : ℤ) : Kˣ) : K) * f) ∈ E :=
      hUE (mem_rootSubgroup.2 ⟨_, rfl⟩)
    have := mul_mem hm (inv_mem hc)
    rw [mul_inv_cancel_right] at this
    convert this using 1
    rw [pinnedX_b_eq_g2N]
    congr 1
    rw [ht]
    simp only [one_zpow, mul_one, zpow_neg_one, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
  exact Y_le_of_forall hb fun f => hUE (mem_U.2 ⟨f, rfl⟩)

omit
  [CharP K 2] in
theorem torus_r_conj_F (t : Kˣ) (c d e f : K) :
    torusElt .G2 K g2ir t * g2N 0 0 c d e f * (torusElt .G2 K g2ir t)⁻¹ =
      g2N 0 0 (((t⁻¹ : Kˣ) : K) * c) ((t : K) * d) (((t ^ 3 : Kˣ) : K) * e) f := by
  have hF : ∀ c d e f : K, g2N (0 : K) 0 c d e f =
      pinnedX .G2 K g2u c * pinnedX .G2 K g2v d * pinnedX .G2 K g2b e * pinnedX .G2 K g2c f :=
    fun c d e f => by simp only [g2N, pinnedX_zero, one_mul]
  have e1 : ∀ a b : ModGL .G2 K, torusElt .G2 K g2ir t * (a * b) * (torusElt .G2 K g2ir t)⁻¹ =
      (torusElt .G2 K g2ir t * a * (torusElt .G2 K g2ir t)⁻¹) *
        (torusElt .G2 K g2ir t * b * (torusElt .G2 K g2ir t)⁻¹) := fun a b => by group
  have hd : torusElt .G2 K g2ir t = torusElt .G2 K g2ia 1 * torusElt .G2 K g2ir t := by
    rw [torusElt_one, one_mul]
  rw [hF c d e f, hF, e1, e1, e1, hd,
    torus_conj_of (m₁ := 1) (m₂ := -1) isRoot_g2u 1 t (by decide) (by decide),
    torus_conj_of (m₁ := 0) (m₂ := 1) isRoot_g2v 1 t (by decide) (by decide),
    torus_conj_of (m₁ := -1) (m₂ := 3) isRoot_g2b 1 t (by decide) (by decide),
    torus_conj_of (m₁ := 1) (m₂ := 0) isRoot_g2c 1 t (by decide) (by decide)]
  simp

omit
  [CharP K 2] in
theorem exists_units_pow_three_ne_one [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ t : Kˣ, t ^ 3 ≠ 1 := by
  by_contra h
  push Not at h
  have hle : Nat.card Kˣ ≤ 3 := by
    have hsub : ∀ t : Kˣ, t ∈ rootsOfUnity 3 K := fun t => by
      rw [mem_rootsOfUnity]
      exact h t
    calc Nat.card Kˣ = Nat.card (rootsOfUnity 3 K) :=
          (Nat.card_congr ((Equiv.subtypeUnivEquiv hsub).symm))
      _ ≤ 3 := card_rootsOfUnity K 3
  rw [Nat.card_units] at hle
  omega

theorem D_mod_U_irreducible_centralizer [Finite K] (hK : 8 ≤ Nat.card K)
    {E : Subgroup (ModGL .G2 K)} (hUE : U K ≤ E) (hED : E ≤ Model.D K)
    (hN : adjointGroup .G2 K ⊓ centralizer (U K : Set (ModGL .G2 K)) ≤
      normalizer (E : Set (ModGL .G2 K))) : E = U K ∨ E = Model.D K := by
  have hL : leviA K ≤ normalizer (E : Set (ModGL .G2 K)) := by
    refine le_trans (le_inf (leviA_le_adjointGroup K) fun l hl => ?_) hN
    refine mem_centralizer_iff.2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := mem_rootSubgroup.1 hx
    exact (commute_of_mem_g2RankOne_r hl y).eq.symm
  have hNr : ∀ s : K, pinnedX .G2 K g2r s ∈ normalizer (E : Set (ModGL .G2 K)) := fun s =>
    hL (pinnedX_r_mem_leviA s)
  have hNw : weylElt .G2 K g2ir 1 ∈ normalizer (E : Set (ModGL .G2 K)) :=
    hL (weylElt_mem_g2RankOne g2ir 1)
  refine D_mod_U_of_steps (by omega) hUE hED hNr hNw fun e f he hyE => ?_
  have hcomm : ∀ (s : K) {y : ModGL .G2 K}, y ∈ E → ⁅pinnedX .G2 K g2r s, y⁆ ∈ E :=
    fun s _ hy => commutatorElement_mem_of_mem_normalizer (hNr s) hy
  have h1 : g2N (0 : K) e 0 0 0 f ∈ E := by
    have := (mem_normalizer_iff.1 hNw _).1 hyE
    rwa [weylElt_r_conj_g2N, show (0 : K) * 0 + e * 0 + f = f by ring] at this
  obtain ⟨t, ht⟩ := exists_units_pow_three_ne_one hK
  have htt : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by rw [← Units.val_mul, inv_mul_cancel,
    Units.val_one]
  have ht3 : ((t ^ 3 : Kˣ) : K) = (t : K) ^ 3 := Units.val_pow_eq_pow_val t 3
  have hz1 : g2N (0 : K) 0 e e e 0 ∈ E := by
    have := hcomm 1 h1
    rw [commutator_r_D] at this
    convert this using 1
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring
  have hzt : g2N (0 : K) 0 e ((t : K) ^ 3 * e) ((t : K) ^ 6 * e) 0 ∈ E := by
    have h2 := hcomm (t : K) h1
    rw [commutator_r_D] at h2
    have h3 := (mem_normalizer_iff.1 (hL (torusElt_mem_g2RankOne g2ir t)) _).1 h2
    rw [torus_r_conj_F] at h3
    convert h3 using 1
    refine g2N_eq_g2N rfl rfl ?_ ?_ ?_ ?_
    · rw [← mul_assoc, htt, one_mul]
    · ring
    · rw [ht3]
      ring
    · ring
  have hw : g2N (0 : K) 0 0 (e + (t : K) ^ 3 * e) (e + (t : K) ^ 6 * e) (e * e) ∈ E := by
    convert mul_mem hz1 hzt using 1
    rw [g2N_mul_coords]
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> char2_ring
  set d₀ := e + (t : K) ^ 3 * e with hd₀
  have hd₀0 : d₀ ≠ 0 := by
    rw [hd₀, show e + (t : K) ^ 3 * e = e * (1 + (t : K) ^ 3) by ring]
    refine mul_ne_zero he fun h0 => ht (Units.ext ?_)
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (CharTwo.add_eq_zero.1 h0).symm
  have hb : ∀ z : K, g2N 0 0 0 0 z 0 ∈ E := by
    intro z
    have := hcomm (z / d₀) hw
    rw [commutator_r_D] at this
    convert this using 1
    refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_
    all_goals first | ring1 | (field_simp; ring1)
  exact Y_le_of_forall hb fun f => hUE (mem_U.2 ⟨f, rfl⟩)

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Transport

theorem image_closure_sq {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K) :
    d.image (closure {z | ∃ g ∈ H, z = g ^ 2}) = closure {z | ∃ g ∈ d.image H, z = g ^ 2} := by
  have hT : closure {z | ∃ g ∈ H, z = g ^ 2} ≤ adjointGroup .G2 K := by
    rw [closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact pow_mem (hH hg) 2
  apply le_antisymm
  · have hL : closure {z | ∃ g ∈ d.image H, z = g ^ 2} ≤ L := by
      rw [closure_le]
      rintro _ ⟨g, hg, rfl⟩
      exact pow_mem (d.image_le _ hg) 2
    rw [← d.image_preimage hL]
    refine d.image_mono ((closure_le _).2 ?_)
    rintro _ ⟨g, hg, rfl⟩
    refine (d.mem_preimage (g := ⟨g, hH hg⟩ ^ 2)).2 ?_
    rw [map_pow]
    exact subset_closure ⟨_, d.emb_mem_image hg, rfl⟩
  · rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hx
    rw [← map_pow]
    exact d.emb_mem_image (subset_closure ⟨_, hg, rfl⟩)

@[expose] noncomputable def imageEquiv {H : Subgroup (ModGL .G2 K)}
    (hH : H ≤ adjointGroup .G2 K) : H ≃* d.image H :=
  (subgroupOfEquivOfLe hH).symm.trans
    ((H.subgroupOf (adjointGroup .G2 K)).equivMapOfInjective d.emb d.emb_injective)

theorem coe_imageEquiv {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K) (x : H) :
    ((d.imageEquiv hH x : d.image H) : G) = d.emb ⟨x, hH x.2⟩ := rfl

theorem map_upperCentralSeries {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    (n : ℕ) : (Subgroup.upperCentralSeries (d.image H) n).map (d.image H).subtype =
      d.image ((Subgroup.upperCentralSeries H n).map H.subtype) := by
  have hc := Subgroup.comap_upperCentralSeries (d.imageEquiv hH) n
  ext z
  simp only [mem_map, d.mem_image, Subgroup.coe_subtype]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨h, rfl⟩ := (d.imageEquiv hH).surjective w
    have hh : h ∈ Subgroup.upperCentralSeries H n := by
      rw [← hc]
      exact hw
    exact ⟨⟨h, hH h.2⟩, ⟨h, hh, rfl⟩, (d.coe_imageEquiv hH h).symm⟩
  · rintro ⟨g, ⟨h, hh, hhg⟩, rfl⟩
    refine ⟨d.imageEquiv hH h, ?_, ?_⟩
    · rw [← hc] at hh
      exact hh
    · rw [d.coe_imageEquiv]
      congr 1
      exact Subtype.ext hhg

theorem maximal_iff_image {P : Subgroup (ModGL .G2 K) → Prop} {PG : Subgroup G → Prop}
    (hPG : ∀ E, PG E → E ≤ L) (hP : ∀ E', P E' → E' ≤ adjointGroup .G2 K)
    (htr : ∀ E', E' ≤ adjointGroup .G2 K → (PG (d.image E') ↔ P E')) (E : Subgroup G) :
    Maximal PG E ↔ ∃ E', Maximal P E' ∧ d.image E' = E := by
  constructor
  · rintro ⟨hE, hmax⟩
    have hEL := hPG E hE
    refine ⟨d.preimage E, ⟨(htr _ (d.preimage_le E)).1 (by rwa [d.image_preimage hEL]),
      fun F' hF' hEF' => ?_⟩, d.image_preimage hEL⟩
    have hF'A := hP F' hF'
    have h1 : E ≤ d.image F' := by
      rw [← d.image_preimage hEL]
      exact d.image_mono hEF'
    have h2 := hmax ((htr F' hF'A).2 hF') h1
    rw [← d.image_preimage hEL] at h2
    exact (d.image_le_image_iff hF'A).1 h2
  · rintro ⟨E', ⟨hE', hmax⟩, rfl⟩
    have hE'A := hP E' hE'
    refine ⟨(htr E' hE'A).2 hE', fun F hF hEF => ?_⟩
    have hFL := hPG F hF
    rw [← d.image_preimage hFL] at hF hEF ⊢
    have h1 := hmax ((htr _ (d.preimage_le F)).1 hF) ((d.image_le_image_iff hE'A).1 hEF)
    exact d.image_mono h1

theorem elemModulo_image_iff {N E' : Subgroup (ModGL .G2 K)} (hE : E' ≤ adjointGroup .G2 K) :
    ElemModulo (d.image N) (d.image E') ↔ ElemModulo N E' := by
  constructor
  · intro h x hx y hy
    obtain ⟨h1, h2⟩ := h _ (d.emb_mem_image (g := ⟨x, hE hx⟩) hx) _
      (d.emb_mem_image (g := ⟨y, hE hy⟩) hy)
    rw [← map_mul, d.emb_mem_image_iff] at h1
    rw [← map_commutatorElement, d.emb_mem_image_iff] at h2
    exact ⟨h1, h2⟩
  · intro h X hX Y hY
    obtain ⟨g, hg, rfl⟩ := d.mem_image.1 hX
    obtain ⟨k, hk, rfl⟩ := d.mem_image.1 hY
    obtain ⟨h1, h2⟩ := h _ hg _ hk
    refine ⟨?_, ?_⟩
    · rw [← map_mul]
      exact d.emb_mem_image h1
    · rw [← map_commutatorElement]
      exact d.emb_mem_image h2

theorem image_bot : d.image (⊥ : Subgroup (ModGL .G2 K)) = ⊥ := by
  rw [image, bot_subgroupOf, Subgroup.map_bot]

theorem mem_normalizer_preimage {E : Subgroup G} {g : adjointGroup .G2 K}
    (hg : d.emb g ∈ normalizer (E : Set G)) :
    (g : ModGL .G2 K) ∈ normalizer (d.preimage E : Set (ModGL .G2 K)) := by
  rw [mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ adjointGroup .G2 K
  · have e : (g : ModGL .G2 K) * y * (g : ModGL .G2 K)⁻¹ =
        ((g * ⟨y, hy⟩ * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) := rfl
    rw [show y = ((⟨y, hy⟩ : adjointGroup .G2 K) : ModGL .G2 K) from rfl, e, d.mem_preimage,
      d.mem_preimage, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hg _)
  · have h1 : y ∉ d.preimage E := fun h => hy (d.preimage_le E h)
    have h2 : (g : ModGL .G2 K) * y * (g : ModGL .G2 K)⁻¹ ∉ d.preimage E := fun h => by
      have := mul_mem (mul_mem (inv_mem g.2) (d.preimage_le E h)) g.2
      rw [show (g : ModGL .G2 K)⁻¹ * ((g : ModGL .G2 K) * y * (g : ModGL .G2 K)⁻¹) *
        (g : ModGL .G2 K) = y by group] at this
      exact hy this
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

theorem le_normalizer_preimage {E : Subgroup G} {H : Subgroup (ModGL .G2 K)}
    (hH : H ≤ adjointGroup .G2 K) (h : d.image H ≤ normalizer (E : Set G)) :
    H ≤ normalizer (d.preimage E : Set (ModGL .G2 K)) := fun x hx =>
  d.mem_normalizer_preimage (g := ⟨x, hH hx⟩) (h (d.emb_mem_image hx))

end Transport

section Yamada312

variable [CharP K 2]

theorem yamada_3_12_centers :
    d.S ⊓ centralizer (d.S : Set G) = d.U ∧ d.D ⊓ centralizer (d.D : Set G) = d.U ∧
      d.M ⊓ centralizer (d.M : Set G) = d.Y ∧ d.F ⊓ centralizer (d.F : Set G) = d.Y := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [G2Data.S, G2Data.U, ← d.image_inf_centralizer _ (Model.S_le_adjointGroup K),
      Model.S_inf_centralizer_S]
  · rw [G2Data.D, G2Data.U, ← d.image_inf_centralizer _ Model.D_le_adjointGroup,
      Model.D_inf_centralizer_D]
  · rw [G2Data.M, G2Data.Y, ← d.image_inf_centralizer _ Model.M_le_adjointGroup,
      Model.M_inf_centralizer_M]
  · rw [G2Data.F, G2Data.Y, ← d.image_inf_centralizer _ Model.F_le_adjointGroup,
      Model.F_inf_centralizer_F]

theorem yamada_3_12_commutators [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅d.D, d.D⁆ = d.U ∧ ⁅d.M, d.M⁆ = d.Y ∧ ⁅d.S, d.S⁆ = d.F ∧
      ⁅⁅d.S, d.S⁆, ⁅d.S, d.S⁆⁆ = d.U := by
  have hS : ⁅d.S, d.S⁆ = d.F := by
    rw [G2Data.S, G2Data.F, ← d.image_commutator (Model.S_le_adjointGroup K)
      (Model.S_le_adjointGroup K), Model.commutator_S hK]
  refine ⟨?_, ?_, hS, ?_⟩
  · rw [G2Data.D, G2Data.U, ← d.image_commutator Model.D_le_adjointGroup
      Model.D_le_adjointGroup, Model.commutator_D]
  · rw [G2Data.M, G2Data.Y, ← d.image_commutator Model.M_le_adjointGroup
      Model.M_le_adjointGroup, Model.commutator_M]
  · rw [hS, G2Data.F, G2Data.U, ← d.image_commutator Model.F_le_adjointGroup
      Model.F_le_adjointGroup, Model.commutator_F]

theorem yamada_3_12_mho [Finite K] (hK : 4 ≤ Nat.card K) :
    closure {z | ∃ g ∈ d.D, z = g ^ 2} = d.U ∧ closure {z | ∃ g ∈ d.M, z = g ^ 2} = d.Y ∧
      closure {z | ∃ g ∈ d.S, z = g ^ 2} = d.F := by
  refine ⟨?_, ?_, ?_⟩
  · rw [G2Data.D, G2Data.U, ← d.image_closure_sq Model.D_le_adjointGroup, Model.closure_sq_D]
  · rw [G2Data.M, G2Data.Y, ← d.image_closure_sq Model.M_le_adjointGroup, Model.closure_sq_M]
  · rw [G2Data.S, G2Data.F, ← d.image_closure_sq (Model.S_le_adjointGroup K),
      Model.closure_sq_S hK]

theorem yamada_3_12_upperCentralSeries [Finite K] (hK : 4 ≤ Nat.card K) :
    (Subgroup.upperCentralSeries d.S 1).map d.S.subtype = d.U ∧
      (Subgroup.upperCentralSeries d.S 2).map d.S.subtype = d.Y ∧
      (Subgroup.upperCentralSeries d.S 3).map d.S.subtype = d.F := by
  have hS := Model.S_le_adjointGroup K
  refine ⟨?_, ?_, ?_⟩
  · rw [G2Data.S, d.map_upperCentralSeries hS, G2Data.U, Subgroup.upperCentralSeries_one]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Model.mem_center_S_iff.1 hy
    · intro hx
      exact ⟨⟨x, Model.U_le_S hx⟩, Model.mem_center_S_iff.2 hx, rfl⟩
  · rw [G2Data.S, d.map_upperCentralSeries hS, G2Data.Y, Model.map_upperCentralSeries_two hK]
  · rw [G2Data.S, d.map_upperCentralSeries hS, G2Data.F, Model.map_upperCentralSeries_three hK]

end Yamada312

end G2Data

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Yamada313

variable [CharP K 2]

theorem yamada_3_12_2_F (E : Subgroup G) :
    Maximal (fun E' : Subgroup G => E' ≤ d.F ∧ CFSG.IsElementaryAbelian 2 E') E ↔
      E = d.W ∨ E = d.X := by
  rw [d.maximal_iff_image (P := fun E' => E' ≤ Model.F K ∧ CFSG.IsElementaryAbelian 2 E')
    (fun E hE => hE.1.trans (d.image_le _)) (fun E' hE' => hE'.1.trans Model.F_le_adjointGroup)
    (fun E' hE' => by rw [G2Data.F, d.image_le_image_iff hE', d.isElementaryAbelian_image_iff hE'])]
  constructor
  · rintro ⟨E', hE', rfl⟩
    rcases (Model.maximal_elementaryAbelian_F_iff E').1 hE' with rfl | rfl
    exacts [Or.inl rfl, Or.inr rfl]
  · rintro (rfl | rfl)
    exacts [⟨_, (Model.maximal_elementaryAbelian_F_iff _).2 (Or.inl rfl), rfl⟩,
      ⟨_, (Model.maximal_elementaryAbelian_F_iff _).2 (Or.inr rfl), rfl⟩]

theorem yamada_3_12_2_quotients (E : Subgroup G) :
    (Maximal (fun E' : Subgroup G => d.Y ≤ E' ∧ E' ≤ d.S ∧ ElemModulo d.Y E') E ↔
        E = d.M ∨ E = d.D) ∧
      (Maximal (fun E' : Subgroup G => d.W ≤ E' ∧ E' ≤ d.S ∧ ElemModulo d.W E') E ↔
        E = d.M ∨ E = d.D) ∧
      (Maximal (fun E' : Subgroup G => d.X ≤ E' ∧ E' ≤ d.S ∧ ElemModulo d.X E') E ↔
        E = d.M ∨ E = d.D) := by
  have key : ∀ N : Subgroup (ModGL .G2 K), N ≤ adjointGroup .G2 K →
      (∀ E' : Subgroup (ModGL .G2 K), Maximal (fun E'' => N ≤ E'' ∧ E'' ≤ Model.S K ∧
        ElemModulo N E'') E' ↔ E' = Model.M K ∨ E' = Model.D K) →
      (Maximal (fun E' : Subgroup G => d.image N ≤ E' ∧ E' ≤ d.S ∧
        ElemModulo (d.image N) E') E ↔ E = d.M ∨ E = d.D) := fun N hN hmod => by
    rw [d.maximal_iff_image (P := fun E'' => N ≤ E'' ∧ E'' ≤ Model.S K ∧ ElemModulo N E'')
      (fun E hE => hE.2.1.trans (d.image_le _))
      (fun E' hE' => hE'.2.1.trans (Model.S_le_adjointGroup K))
      (fun E' hE' => by rw [G2Data.S, d.image_le_image_iff hN, d.image_le_image_iff hE',
        d.elemModulo_image_iff hE'])]
    constructor
    · rintro ⟨E', hE', rfl⟩
      rcases (hmod E').1 hE' with rfl | rfl
      exacts [Or.inl rfl, Or.inr rfl]
    · rintro (rfl | rfl)
      exacts [⟨_, (hmod _).2 (Or.inl rfl), rfl⟩, ⟨_, (hmod _).2 (Or.inr rfl), rfl⟩]
  exact ⟨key _ Model.Y_le_adjointGroup Model.maximal_elemModulo_Y_iff,
    key _ Model.W_le_adjointGroup Model.maximal_elemModulo_W_iff,
    key _ Model.X_le_adjointGroup Model.maximal_elemModulo_X_iff⟩

theorem yamada_3_13_1_G :
    L ⊓ normalizer (d.X : Set G) = d.J ⊔ d.S ∧ L ⊓ normalizer (d.F : Set G) = d.J ⊔ d.S ∧
      L ⊓ normalizer (d.S : Set G) = d.J ⊔ d.S := by
  obtain ⟨h1, h2, h3⟩ := Model.yamada_3_13_1 (K := K)
  have hJS : d.image (Model.J K ⊔ Model.S K) = d.J ⊔ d.S :=
    d.image_sup (Model.J_le_adjointGroup K) (Model.S_le_adjointGroup K)
  refine ⟨(d.image_inf_normalizer Model.X_le_adjointGroup).symm.trans (by rw [h1, hJS]),
    (d.image_inf_normalizer Model.F_le_adjointGroup).symm.trans (by rw [h2, hJS]),
    (d.image_inf_normalizer (Model.S_le_adjointGroup K)).symm.trans (by rw [h3, hJS])⟩

omit
  [CharP K 2] in
theorem image_sup_sup {H A B : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    (hA : A ≤ adjointGroup .G2 K) (hB : B ≤ adjointGroup .G2 K) :
    d.image (H ⊔ (A ⊔ B)) = d.image H ⊔ (d.image A ⊔ d.image B) := by
  rw [d.image_sup hH (sup_le hA hB), d.image_sup hA hB]

theorem yamada_3_13_2_G [Finite K] :
    L ⊓ normalizer (d.U : Set G) = d.D ⊔ (d.leviA ⊔ d.J₃) ∧
      L ⊓ normalizer (d.D : Set G) = d.D ⊔ (d.leviA ⊔ d.J₃) ∧
      d.J₃ ≤ centralizer (d.leviA : Set G) ∧ d.leviA ⊓ d.J₃ = ⊥ := by
  obtain ⟨h1, h2, h3, h4⟩ := Model.yamada_3_13_2 (K := K)
  have hJ3 := Model.torusFix_le_adjointGroup K g2r
  have hsup := d.image_sup_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K) hJ3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [G2Data.U, ← d.image_inf_normalizer (Model.U_le_adjointGroup K), h1, hsup]
    rfl
  · rw [G2Data.D, ← d.image_inf_normalizer Model.D_le_adjointGroup, h2, hsup]
    rfl
  · intro x hx
    have hx' : x ∈ d.image (Model.J₃ K ⊓ centralizer (Model.leviA K : Set (ModGL .G2 K))) := by
      rwa [inf_eq_left.2 h3]
    rw [d.image_inf_centralizer _ (Model.leviA_le_adjointGroup K)] at hx'
    exact hx'.2
  · rw [G2Data.leviA, G2Data.J₃, ← d.image_inf, h4, d.image_bot]

theorem yamada_3_13_3_G [Finite K] :
    L ⊓ normalizer (d.Y : Set G) = d.M ⊔ (d.leviB ⊔ d.J₄) ∧
      L ⊓ normalizer (d.W : Set G) = d.M ⊔ (d.leviB ⊔ d.J₄) ∧
      L ⊓ normalizer (d.M : Set G) = d.M ⊔ (d.leviB ⊔ d.J₄) ∧
      d.J₄ ≤ centralizer (d.leviB : Set G) ∧ d.leviB ⊓ d.J₄ = ⊥ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Model.yamada_3_13_3 (K := K)
  have hJ4 := Model.torusFix_le_adjointGroup K g2a
  have hsup := d.image_sup_sup Model.M_le_adjointGroup (Model.leviB_le_adjointGroup K) hJ4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [G2Data.Y, ← d.image_inf_normalizer Model.Y_le_adjointGroup, h1, hsup]
    rfl
  · rw [G2Data.W, ← d.image_inf_normalizer Model.W_le_adjointGroup, h2, hsup]
    rfl
  · rw [G2Data.M, ← d.image_inf_normalizer Model.M_le_adjointGroup, h3, hsup]
    rfl
  · intro x hx
    have hx' : x ∈ d.image (Model.J₄ K ⊓ centralizer (Model.leviB K : Set (ModGL .G2 K))) := by
      rwa [inf_eq_left.2 h4]
    rw [d.image_inf_centralizer _ (Model.leviB_le_adjointGroup K)] at hx'
    exact hx'.2
  · rw [G2Data.leviB, G2Data.J₄, ← d.image_inf, h5, d.image_bot]

theorem yamada_3_15_G [Finite K] :
    L ⊓ normalizer (d.rootGroup g2v : Set G) = d.W ⊔ (d.leviB ⊔ d.J₄) := by
  rw [G2Data.rootGroup, ← d.image_inf_normalizer (rootSubgroup_le_adjointGroup _),
    Model.yamada_3_15, d.image_sup_sup Model.W_le_adjointGroup (Model.leviB_le_adjointGroup K)
      (Model.torusFix_le_adjointGroup K g2a)]
  rfl

theorem yamada_3_13_4_G [Finite K] (hK : 4 ≤ Nat.card K) :
    ⁅L ⊓ normalizer (d.D : Set G), L ⊓ normalizer (d.D : Set G)⁆ = d.D ⊔ d.leviA ∧
      ⁅d.D ⊔ d.leviA, d.D ⊔ d.leviA⁆ = d.D ⊔ d.leviA ∧
      ⁅L ⊓ normalizer (d.M : Set G), L ⊓ normalizer (d.M : Set G)⁆ = d.M ⊔ d.leviB ∧
      ⁅d.M ⊔ d.leviB, d.M ⊔ d.leviB⁆ = d.M ⊔ d.leviB := by
  obtain ⟨h1, h2⟩ := Model.yamada_3_13_4_D hK
  obtain ⟨h3, h4⟩ := Model.yamada_3_13_4_M hK
  have hND : L ⊓ normalizer (d.D : Set G) =
      d.image (adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K))) :=
    (d.image_inf_normalizer Model.D_le_adjointGroup).symm
  have hNM : L ⊓ normalizer (d.M : Set G) =
      d.image (adjointGroup .G2 K ⊓ normalizer (Model.M K : Set (ModGL .G2 K))) :=
    (d.image_inf_normalizer Model.M_le_adjointGroup).symm
  have hDA := d.image_sup Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)
  have hMB := d.image_sup Model.M_le_adjointGroup (Model.leviB_le_adjointGroup K)
  have hNDA : adjointGroup .G2 K ⊓ normalizer (Model.D K : Set (ModGL .G2 K)) ≤
      adjointGroup .G2 K := inf_le_left
  have hNMA : adjointGroup .G2 K ⊓ normalizer (Model.M K : Set (ModGL .G2 K)) ≤
      adjointGroup .G2 K := inf_le_left
  have hDAA := sup_le Model.D_le_adjointGroup (Model.leviA_le_adjointGroup K)
  have hMBA := sup_le Model.M_le_adjointGroup (Model.leviB_le_adjointGroup K)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hND, ← d.image_commutator hNDA hNDA, h1, hDA]
    rfl
  · have := congrArg d.image h2
    rwa [d.image_commutator hDAA hDAA, hDA] at this
  · rw [hNM, ← d.image_commutator hNMA hNMA, h3, hMB]
    rfl
  · have := congrArg d.image h4
    rwa [d.image_commutator hMBA hMBA, hMB] at this

theorem yamada_3_17_2_G [Finite K] :
    L ⊓ centralizer (d.X : Set G) = d.X ∧ L ⊓ centralizer (d.W : Set G) = d.W := by
  have hX := d.image_inf_centralizer (adjointGroup .G2 K) Model.X_le_adjointGroup
  have hW := d.image_inf_centralizer (adjointGroup .G2 K) Model.W_le_adjointGroup
  rw [d.image_adjointGroup, Model.adjointGroup_inf_centralizer_X] at hX
  rw [d.image_adjointGroup, Model.adjointGroup_inf_centralizer_W] at hW
  exact ⟨hX.symm, hW.symm⟩

end Yamada313

end G2Data

namespace Model


variable {K : Type} [Field K] [CharP K 2]

theorem wa_conj_D (B C D E F : K) :
    weylElt .G2 K g2ir 1 * g2N 0 B C D E F * weylElt .G2 K g2ir 1 =
      g2N 0 E D C B (D * C + E * B + F) := by
  have := weylElt_r_conj_g2N B C D E F
  rwa [UnbalancedCatalog.weylElt_inv] at this

theorem coords_of_sq_M {A C D E F : K} (h : g2N A 0 C D E F * g2N A 0 C D E F = 1) :
    A * (A * C + D) = 0 ∧ C * (A * C + D) = 0 := by
  rw [g2N_mul_self, ← g2N_zero] at h
  obtain ⟨-, -, -, -, h5, h6⟩ := g2N_injective h
  exact ⟨by linear_combination h5, by linear_combination h6⟩

theorem coords_of_commute_M {A C D E F a c d e f : K}
    (h : g2N A 0 C D E F * g2N a 0 c d e f = g2N a 0 c d e f * g2N A 0 C D E F) :
    A ^ 2 * c + A * d + C * a ^ 2 + D * a = 0 ∧ A * c ^ 2 + C ^ 2 * a + C * d + D * c = 0 := by
  obtain ⟨-, -, h5, h6⟩ := coords_of_commutator_eq_one (commutatorElement_eq_one_iff_mul_comm.2 h)
  exact ⟨by linear_combination h5, by linear_combination h6⟩

theorem elementary_le_M {E : Subgroup (ModGL .G2 K)} (hEM : E ≤ M K)
    (hE : CFSG.IsElementaryAbelian 2 E) : E ≤ W K ∨ E ≤ X K ∨ ∃ l : K, E ≤
      (X K).map (MulAut.conj (pinnedX .G2 K g2a l * weylElt .G2 K g2ia 1)).toMonoidHom := by
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  by_cases hW : E ≤ W K
  · exact Or.inl hW
  obtain ⟨y₀, hy₀E, hy₀W⟩ := Set.not_subset.1 hW
  obtain ⟨a₀, c₀, d₀, e₀, f₀, rfl⟩ := mem_M.1 (hEM hy₀E)
  have hac : a₀ ≠ 0 ∨ c₀ ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hy₀W (g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩)
  have hd₀ : d₀ = a₀ * c₀ := by
    obtain ⟨h1, h2⟩ := coords_of_sq_M (hsq _ hy₀E)
    have : a₀ * c₀ + d₀ = 0 := by
      rcases hac with ha | hc
      · exact (mul_eq_zero.1 h1).resolve_left ha
      · exact (mul_eq_zero.1 h2).resolve_left hc
    exact (CharTwo.add_eq_zero.1 this).symm
  subst hd₀
  have key : ∀ {A C D E' F : K}, g2N A 0 C D E' F ∈ E → A * c₀ = C * a₀ ∧ D = A * C := by
    intro A C D E' F hx
    obtain ⟨h1, h2⟩ := coords_of_sq_M (hsq _ hx)
    obtain ⟨h3, h4⟩ := coords_of_commute_M (hcomm _ hx _ hy₀E)
    by_cases hAC : A = 0 ∧ C = 0
    · obtain ⟨rfl, rfl⟩ := hAC
      have h3' : D * a₀ = 0 := by linear_combination h3
      have h4' : D * c₀ = 0 := by linear_combination h4
      have hD : D = 0 := by
        rcases hac with ha | hc
        · exact (mul_eq_zero.1 h3').resolve_right ha
        · exact (mul_eq_zero.1 h4').resolve_right hc
      exact ⟨by ring, by rw [hD]; ring⟩
    · have hD : D = A * C := by
        have : A * C + D = 0 := by
          by_cases hA : A = 0
          · exact (mul_eq_zero.1 h2).resolve_left fun hC => hAC ⟨hA, hC⟩
          · exact (mul_eq_zero.1 h1).resolve_left hA
        exact (CharTwo.add_eq_zero.1 this).symm
      subst hD
      have e3 : (A + a₀) * (A * c₀ + a₀ * C) = 0 := by linear_combination h3
      have e4 : (C + c₀) * (A * c₀ + a₀ * C) = 0 := by linear_combination h4
      refine ⟨?_, rfl⟩
      by_contra hne
      have hne' : A * c₀ + a₀ * C ≠ 0 := fun h0 => hne (by
        have := CharTwo.add_eq_zero.1 h0
        rw [this]; ring)
      have hA : A = a₀ := CharTwo.add_eq_zero.1 ((mul_eq_zero.1 e3).resolve_right hne')
      have hC : C = c₀ := CharTwo.add_eq_zero.1 ((mul_eq_zero.1 e4).resolve_right hne')
      apply hne'
      rw [hA, hC]
      exact CharTwo.add_self_eq_zero _
  right
  by_cases ha₀ : a₀ = 0
  · subst ha₀
    have hc₀ : c₀ ≠ 0 := hac.resolve_left (fun h => h rfl)
    left
    intro x hx
    obtain ⟨A, C, D, E', F, rfl⟩ := mem_M.1 (hEM hx)
    obtain ⟨h1, h2⟩ := key hx
    have hA : A = 0 := by
      have : A * c₀ = 0 := by rw [h1]; ring
      exact (mul_eq_zero.1 this).resolve_right hc₀
    subst hA
    rw [h2, zero_mul]
    exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
  · right
    refine ⟨c₀ / a₀, fun x hx => ?_⟩
    obtain ⟨A, C, D, E', F, rfl⟩ := mem_M.1 (hEM hx)
    obtain ⟨h1, h2⟩ := key hx
    have hC : C = c₀ / a₀ * A := by
      field_simp
      linear_combination h1.symm
    subst hC h2
    rw [mem_map_conj_iff, mul_inv_rev, UnbalancedCatalog.weylElt_inv, pinnedX_inv_eq,
      show weylElt .G2 K g2ia 1 * pinnedX .G2 K g2a (c₀ / a₀) *
        g2N A 0 (c₀ / a₀ * A) (A * (c₀ / a₀ * A)) E' F *
        (pinnedX .G2 K g2a (c₀ / a₀) * weylElt .G2 K g2ia 1) =
        weylElt .G2 K g2ia 1 * (pinnedX .G2 K g2a (c₀ / a₀) *
          g2N A 0 (c₀ / a₀ * A) (A * (c₀ / a₀ * A)) E' F * pinnedX .G2 K g2a (c₀ / a₀)) *
          weylElt .G2 K g2ia 1 by group, conj_a]
    rw [show g2N A 0 (c₀ / a₀ * A + A * (c₀ / a₀)) (A * (c₀ / a₀ * A) + A ^ 2 * (c₀ / a₀))
        (E' + A ^ 3 * (c₀ / a₀)) (F + A ^ 3 * 0 * (c₀ / a₀) + A ^ 2 * (c₀ / a₀ * A) * (c₀ / a₀) +
          E' * (c₀ / a₀)) =
        g2N A 0 0 0 (E' + A ^ 3 * (c₀ / a₀))
          (F + A ^ 3 * 0 * (c₀ / a₀) + A ^ 2 * (c₀ / a₀ * A) * (c₀ / a₀) + E' * (c₀ / a₀)) from
      g2N_eq_g2N rfl rfl (by char2_ring) (by char2_ring) rfl rfl, wb_conj_M]
    exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩

theorem coords_of_sq_D {B C D E F : K} (h : g2N 0 B C D E F * g2N 0 B C D E F = 1) :
    B * E = C * D := by
  rw [g2N_mul_self, ← g2N_zero] at h
  obtain ⟨-, -, -, -, -, h6⟩ := g2N_injective h
  exact CharTwo.add_eq_zero.1 (by linear_combination h6)

theorem coords_of_commute_D {B C D E F b c d e f : K}
    (h : g2N 0 B C D E F * g2N 0 b c d e f = g2N 0 b c d e f * g2N 0 B C D E F) :
    B * e + C * d + D * c + E * b = 0 := by
  obtain ⟨-, -, -, h6⟩ := coords_of_commutator_eq_one (commutatorElement_eq_one_iff_mul_comm.2 h)
  linear_combination h6

theorem elementary_le_D [Finite K] {E : Subgroup (ModGL .G2 K)} (hED : E ≤ Model.D K)
    (hE : CFSG.IsElementaryAbelian 2 E) : E ≤ M K ∨
      (∃ γ : K, E ≤ (X K).map (MulAut.conj (pinnedX .G2 K g2r γ *
        weylElt .G2 K g2ir 1)).toMonoidHom) ∨
      ∃ s : K, E ≤ (W K).map (MulAut.conj (pinnedX .G2 K g2r s *
        weylElt .G2 K g2ir 1)).toMonoidHom := by
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  by_cases hM : E ≤ M K
  · exact Or.inl hM
  right
  obtain ⟨x₀, hx₀E, hx₀M⟩ := Set.not_subset.1 hM
  obtain ⟨B₀, C₀, D₀, E₀, F₀, rfl⟩ := mem_D.1 (hED hx₀E)
  have hB₀ : B₀ ≠ 0 := fun h => hx₀M (g2N_mem_M_iff.2 h)
  have h₀ := coords_of_sq_D (hsq _ hx₀E)
  set γ := C₀ / B₀ with hγ
  set δ := D₀ / B₀ with hδ
  have key : ∀ {B C D E' F : K}, g2N 0 B C D E' F ∈ E →
      (C = γ * B ∧ E' = γ * D) ∨ (D = δ * B ∧ E' = δ * C) := by
    intro B C D E' F hx
    have h1 := coords_of_sq_D (hsq _ hx)
    have h2 := coords_of_commute_D (hcomm _ hx _ hx₀E)
    have hE' : E' = B * γ * δ + C * δ + D * γ := by
      rw [hγ, hδ]
      field_simp
      linear_combination (norm := char2_ring) (-B₀) * h2 + B * h₀
    have hfac : (B * γ + C) * (B * δ + D) = 0 := by
      rw [hE'] at h1
      linear_combination (norm := char2_ring) h1
    rcases mul_eq_zero.1 hfac with h | h
    · have hC : C = γ * B := by rw [← CharTwo.add_eq_zero.1 h]; ring
      refine Or.inl ⟨hC, ?_⟩
      rw [hE', hC]
      char2_ring
    · have hD : D = δ * B := by rw [← CharTwo.add_eq_zero.1 h]; ring
      refine Or.inr ⟨hD, ?_⟩
      rw [hE', hD]
      char2_ring
  have hall : (∀ {B C D E' F : K}, g2N 0 B C D E' F ∈ E → C = γ * B ∧ E' = γ * D) ∨
      (∀ {B C D E' F : K}, g2N 0 B C D E' F ∈ E → D = δ * B ∧ E' = δ * C) := by
    by_contra h
    rw [not_or] at h
    obtain ⟨hR', hC'⟩ := h
    simp only [not_forall] at hR' hC'
    obtain ⟨B₁, C₁, D₁, E₁, F₁, hx₁, hR⟩ := hR'
    obtain ⟨B₂, C₂, D₂, E₂, F₂, hx₂, hC⟩ := hC'
    have hC₁ := (key hx₁).resolve_left hR
    have hR₂ := (key hx₂).resolve_right hC
    have hx₁₂ := mul_mem hx₁ hx₂
    rw [g2N_zero_mul_g2N_zero] at hx₁₂
    rcases key hx₁₂ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply hR
      constructor
      · linear_combination h1 - hR₂.1
      · linear_combination h2 - hR₂.2
    · apply hC
      constructor
      · linear_combination h1 - hC₁.1
      · linear_combination h2 - hC₁.2
  rcases hall with hR | hC
  · left
    refine ⟨γ, fun x hx => ?_⟩
    obtain ⟨B, C, D, E', F, rfl⟩ := mem_D.1 (hED hx)
    obtain ⟨rfl, rfl⟩ := hR hx
    rw [mem_map_conj_iff, mul_inv_rev, UnbalancedCatalog.weylElt_inv, pinnedX_inv_eq,
      show weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r γ * g2N 0 B (γ * B) D (γ * D) F *
        (pinnedX .G2 K g2r γ * weylElt .G2 K g2ir 1) =
        weylElt .G2 K g2ir 1 * (pinnedX .G2 K g2r γ * g2N 0 B (γ * B) D (γ * D) F *
          pinnedX .G2 K g2r γ) * weylElt .G2 K g2ir 1 by group, conj_r]
    rw [show g2N 0 B (γ * B + B * γ) (D + B * γ ^ 2) (γ * D + B * γ ^ 3 + γ * B * γ ^ 2 + D * γ)
        (F + B ^ 2 * γ ^ 3 + B * (γ * B) * γ ^ 2 + (γ * B) ^ 2 * γ) =
        g2N 0 B 0 (D + B * γ ^ 2) 0
          (F + B ^ 2 * γ ^ 3 + B * (γ * B) * γ ^ 2 + (γ * B) ^ 2 * γ) from
      g2N_eq_g2N rfl rfl (by char2_ring) rfl (by char2_ring) rfl, wa_conj_D]
    exact g2N_mem_X_iff.2 ⟨rfl, rfl, rfl⟩
  · right
    obtain ⟨s, hs⟩ : ∃ s : K, s ^ 2 = δ := ⟨(frobeniusEquiv K 2).symm δ, by
      have := frobenius_apply_frobeniusEquiv_symm K 2 δ
      rwa [frobenius_def] at this⟩
    refine ⟨s, fun x hx => ?_⟩
    obtain ⟨B, C, D, E', F, rfl⟩ := mem_D.1 (hED hx)
    obtain ⟨rfl, rfl⟩ := hC hx
    rw [mem_map_conj_iff, mul_inv_rev, UnbalancedCatalog.weylElt_inv, pinnedX_inv_eq,
      show weylElt .G2 K g2ir 1 * pinnedX .G2 K g2r s * g2N 0 B C (δ * B) (δ * C) F *
        (pinnedX .G2 K g2r s * weylElt .G2 K g2ir 1) =
        weylElt .G2 K g2ir 1 * (pinnedX .G2 K g2r s * g2N 0 B C (δ * B) (δ * C) F *
          pinnedX .G2 K g2r s) * weylElt .G2 K g2ir 1 by group, conj_r, ← hs]
    rw [show g2N 0 B (C + B * s) (s ^ 2 * B + B * s ^ 2)
        (s ^ 2 * C + B * s ^ 3 + C * s ^ 2 + s ^ 2 * B * s)
        (F + B ^ 2 * s ^ 3 + B * C * s ^ 2 + C ^ 2 * s) =
        g2N 0 B (C + B * s) 0 0 (F + B ^ 2 * s ^ 3 + B * C * s ^ 2 + C ^ 2 * s) from
      g2N_eq_g2N rfl rfl rfl (by char2_ring) (by char2_ring) rfl, wa_conj_D]
    exact g2N_mem_W_iff.2 ⟨rfl, rfl, rfl⟩

theorem elementary_le_S_conj [Finite K] {E : Subgroup (ModGL .G2 K)} (hES : E ≤ S K)
    (hE : CFSG.IsElementaryAbelian 2 E) :
    ∃ g ∈ adjointGroup .G2 K, E ≤ (X K).map (MulAut.conj g).toMonoidHom ∨
      E ≤ (W K).map (MulAut.conj g).toMonoidHom := by
  have h1 : ∀ H : Subgroup (ModGL .G2 K), E ≤ H →
      E ≤ H.map (MulAut.conj (1 : ModGL .G2 K)).toMonoidHom := fun H h x hx =>
    mem_map_conj_iff.2 (by simpa using h hx)
  have hDM : E ≤ Model.D K ∨ E ≤ M K := le_or_le_of_subset_union fun x hx =>
    mem_D_or_M_of_mul_self_mem (N := Y K) (Or.inl Y_le_W) (hES hx) (by
      rw [← sq, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]
      exact one_mem _)
  have hmem : ∀ (γ : Fin Tag.G2.rank → ℤ) (i : Fin Tag.G2.rank) (l : K),
      pinnedX .G2 K γ l * weylElt .G2 K i 1 ∈ adjointGroup .G2 K := fun γ i l =>
    mul_mem (pinnedX_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _)
  have caseM : E ≤ M K → ∃ g ∈ adjointGroup .G2 K, E ≤ (X K).map (MulAut.conj g).toMonoidHom ∨
      E ≤ (W K).map (MulAut.conj g).toMonoidHom := fun hEM => by
    rcases elementary_le_M hEM hE with h | h | ⟨l, h⟩
    · exact ⟨1, one_mem _, Or.inr (h1 _ h)⟩
    · exact ⟨1, one_mem _, Or.inl (h1 _ h)⟩
    · exact ⟨_, hmem _ _ l, Or.inl h⟩
  rcases hDM with hED | hEM
  · rcases elementary_le_D hED hE with h | ⟨γ, h⟩ | ⟨s, h⟩
    · exact caseM h
    · exact ⟨_, hmem _ _ γ, Or.inl h⟩
    · exact ⟨_, hmem _ _ s, Or.inr h⟩
  · exact caseM hEM

theorem elementary_le_conj [Finite K] {E : Subgroup (ModGL .G2 K)}
    (hEL : E ≤ adjointGroup .G2 K) (hE : CFSG.IsElementaryAbelian 2 E) :
    ∃ g ∈ adjointGroup .G2 K, E ≤ (X K).map (MulAut.conj g).toMonoidHom ∨
      E ≤ (W K).map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2
    (posUnipotent_le_adjointGroup (τ := .G2) (K := K)) card_posUnipotent
  set S₀ : Sylow 2 (adjointGroup .G2 K) := hUp.toSylow hUi with hS₀
  have hE' : IsPGroup 2 (E.subgroupOf (adjointGroup .G2 K)) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ (mem_subgroupOf.1 x.2)
  obtain ⟨P, hP⟩ := hE'.exists_le_sylow
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) S₀ P
  set E₁ := E.map (MulAut.conj ((h : ModGL .G2 K)⁻¹)).toMonoidHom with hE₁
  have hE₁S : E₁ ≤ S K := by
    rintro _ ⟨x, hx, rfl⟩
    have hxA : x ∈ adjointGroup .G2 K := hEL hx
    have hmem := hP (show (⟨x, hxA⟩ : adjointGroup .G2 K) ∈ E.subgroupOf (adjointGroup .G2 K)
      from hx)
    rw [Sylow.coe_subgroup_smul] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : h * y * h⁻¹ = ⟨x, hxA⟩ := by simpa using hyx
    have hyS : ((h⁻¹ * ⟨x, hxA⟩ * h : adjointGroup .G2 K) : ModGL .G2 K) ∈ S K := by
      rw [← hyx', show h⁻¹ * (h * y * h⁻¹) * h = y by group]
      have := hy
      rw [hS₀, IsPGroup.toSylow_coe] at this
      exact mem_subgroupOf.1 this
    simpa [MulAut.conj_apply] using hyS
  obtain ⟨g, hg, hX | hW⟩ := elementary_le_S_conj hE₁S (isElementaryAbelian_map_conj hE _)
  · refine ⟨h * g, mul_mem h.2 hg, Or.inl fun x hx => ?_⟩
    have := hX ⟨x, hx, rfl⟩
    rw [mem_map_conj_iff] at this ⊢
    simpa [mul_assoc] using this
  · refine ⟨h * g, mul_mem h.2 hg, Or.inr fun x hx => ?_⟩
    have := hW ⟨x, hx, rfl⟩
    rw [mem_map_conj_iff] at this ⊢
    simpa [mul_assoc] using this

theorem pow_eight_eq_one_of_mem_S {x : ModGL .G2 K} (hx : x ∈ S K) : x ^ 8 = 1 := by
  obtain ⟨A, B, C, D, E, F, rfl⟩ := mem_S.1 hx
  rw [show (8 : ℕ) = 2 * 2 * 2 from rfl, pow_mul, pow_mul, sq (g2N A B C D E F), g2N_mul_self,
    sq (g2N _ _ _ _ _ _), g2N_mul_self, sq (g2N _ _ _ _ _ _), g2N_mul_self, ← g2N_zero]
  refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> ring

omit
  [CharP K 2] in
theorem commutator_borelGroup_le :
    ⁅borelGroup .G2 K, borelGroup .G2 K⁆ ≤ S K := by
  have hB : borelGroup .G2 K = S K ⊔ J K := sup_comm _ _
  rw [hB]
  exact commutator_sup_le_of_comm
    (le_normalizer_of_conj_mem fun h hh u hu => torus_conj_mem_posUnipotent hh hu)
    fun a ha b hb => J_comm ha hb

theorem yamada_3_17_1 [Finite K] (hK : 4 ≤ Nat.card K) :
    Maximal (fun E : Subgroup (ModGL .G2 K) => E ≤ adjointGroup .G2 K ∧
        CFSG.IsElementaryAbelian 2 E) (X K) ∧
      Maximal (fun E : Subgroup (ModGL .G2 K) => E ≤ adjointGroup .G2 K ∧
        CFSG.IsElementaryAbelian 2 E) (W K) ∧
      (∀ g ∈ adjointGroup .G2 K, (X K).map (MulAut.conj g).toMonoidHom ≠ W K) ∧
      ∀ E : Subgroup (ModGL .G2 K), Maximal (fun E : Subgroup (ModGL .G2 K) =>
          E ≤ adjointGroup .G2 K ∧ CFSG.IsElementaryAbelian 2 E) E →
        ∃ g ∈ adjointGroup .G2 K, E = (X K).map (MulAut.conj g).toMonoidHom ∨
          E = (W K).map (MulAut.conj g).toMonoidHom := by
  have hmax : ∀ H : Subgroup (ModGL .G2 K), H ≤ adjointGroup .G2 K →
      CFSG.IsElementaryAbelian 2 H → adjointGroup .G2 K ⊓ centralizer (H : Set (ModGL .G2 K)) = H →
      Maximal (fun E : Subgroup (ModGL .G2 K) => E ≤ adjointGroup .G2 K ∧
        CFSG.IsElementaryAbelian 2 E) H := fun H hHA hH hC => by
    refine ⟨⟨hHA, hH⟩, fun E ⟨hEA, hE⟩ hHE x hx => ?_⟩
    rw [← hC]
    refine ⟨hEA hx, mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (mul_comm' (⟨y, hHE hy⟩ : E) ⟨x, hx⟩)
  refine ⟨hmax _ X_le_adjointGroup X_isElementaryAbelian adjointGroup_inf_centralizer_X,
    hmax _ W_le_adjointGroup W_isElementaryAbelian adjointGroup_inf_centralizer_W, ?_, ?_⟩
  ·
    intro g hg hXW
    obtain ⟨hperf, -, hnt⟩ := g2RankOne_isPerfect_isSimpleGroup (K := K) hK
    have hconj : ∀ l ∈ leviB K, g⁻¹ * l * g ∈ borelGroup .G2 K := by
      intro l hl
      rw [← adjointGroup_inf_normalizer_X]
      refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hg) (leviB_le_adjointGroup K hl)) hg, ?_⟩
      have hlN := g2RankOne_a_le_normalizer hl
      rw [mem_normalizer_iff] at hlN ⊢
      intro y
      have e1 : ∀ z, z ∈ X K ↔ g * z * g⁻¹ ∈ W K := fun z => by
        rw [← hXW, mem_map_conj_iff]
        simp [mul_assoc]
      rw [e1, e1, show g * (g⁻¹ * l * g * y * (g⁻¹ * l * g)⁻¹) * g⁻¹ =
        l * (g * y * g⁻¹) * l⁻¹ by group]
      exact hlN _
    have hS : ∀ l ∈ leviB K, g⁻¹ * l * g ∈ S K := by
      intro l hl
      replace hl : l ∈ ⁅leviB K, leviB K⁆ := by
        rw [show ⁅leviB K, leviB K⁆ = leviB K from g2RankOne_commutator hK]
        exact hl
      have hmap : (⁅leviB K, leviB K⁆).map (MulAut.conj g⁻¹).toMonoidHom ≤
          ⁅borelGroup .G2 K, borelGroup .G2 K⁆ := by
        rw [map_commutator]
        have hle : (leviB K).map (MulAut.conj g⁻¹).toMonoidHom ≤ borelGroup .G2 K := by
          rintro _ ⟨l', hl', rfl⟩
          simpa using hconj l' hl'
        exact commutator_mono hle hle
      have := commutator_borelGroup_le (hmap ⟨l, hl, rfl⟩)
      simpa using this
    have hp : IsPGroup 2 (leviB K) := by
      intro l
      refine ⟨3, Subtype.ext ?_⟩
      have h8 := pow_eight_eq_one_of_mem_S (hS l l.2)
      rw [show g⁻¹ * (l : ModGL .G2 K) * g = (MulAut.conj g⁻¹) (l : ModGL .G2 K) by simp,
        ← map_pow, map_eq_one_iff _ (MulAut.conj g⁻¹).injective] at h8
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h8
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact AS81.G2.not_isPGroup_of_isPerfect hperf hp
  ·
    intro E ⟨⟨hEA, hE⟩, hEmax⟩
    obtain ⟨g, hg, hX | hW⟩ := elementary_le_conj hEA hE
    · have hP : (X K).map (MulAut.conj g).toMonoidHom ≤ adjointGroup .G2 K ∧
          CFSG.IsElementaryAbelian 2 ((X K).map (MulAut.conj g).toMonoidHom) := by
        refine ⟨?_, isElementaryAbelian_map_conj X_isElementaryAbelian g⟩
        rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hg (X_le_adjointGroup hx)) (inv_mem hg)
      exact ⟨g, hg, Or.inl (le_antisymm hX (hEmax hP hX))⟩
    · have hP : (W K).map (MulAut.conj g).toMonoidHom ≤ adjointGroup .G2 K ∧
          CFSG.IsElementaryAbelian 2 ((W K).map (MulAut.conj g).toMonoidHom) := by
        refine ⟨?_, isElementaryAbelian_map_conj W_isElementaryAbelian g⟩
        rintro _ ⟨x, hx, rfl⟩
        exact mul_mem (mul_mem hg (W_le_adjointGroup hx)) (inv_mem hg)
      exact ⟨g, hg, Or.inr (le_antisymm hW (hEmax hP hW))⟩

theorem card_le_of_commute_D [Finite K] {A : Subgroup (ModGL .G2 K)} (hAD : A ≤ Model.D K)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ Nat.card K ^ 3 := by
  have hc : ∀ x : A, ∃ v : K × K × K × K × K,
      (x : ModGL .G2 K) = g2N 0 v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2 := fun x => by
    obtain ⟨B, C, D, E, F, h⟩ := mem_D.1 (hAD x.2)
    exact ⟨(B, C, D, E, F), h⟩
  choose v hv using hc
  have hinj : ∀ x y : A, v x = v y → x = y := fun x y h => Subtype.ext (by rw [hv, hv, h])
  have hrel : ∀ x y : A, (v x).1 * (v y).2.2.2.1 + (v x).2.1 * (v y).2.2.1 +
      (v x).2.2.1 * (v y).2.1 + (v x).2.2.2.1 * (v y).1 = 0 := fun x y => by
    have := hA _ x.2 _ y.2
    rw [hv x, hv y] at this
    exact coords_of_commute_D this
  by_cases h1 : ∀ x : A, (v x).1 = 0 ∧ (v x).2.1 = 0
  · refine card_le_cube_of_injective (fun x => ((v x).2.2.1, (v x).2.2.2.1, (v x).2.2.2.2))
      fun x y h => hinj x y ?_
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1x, h2x⟩ := h1 x
    obtain ⟨h1y, h2y⟩ := h1 y
    exact Prod.ext (h1x.trans h1y.symm) (Prod.ext (h2x.trans h2y.symm) (Prod.ext h.1
      (Prod.ext h.2.1 h.2.2)))
  push Not at h1
  obtain ⟨x₀, hx₀⟩ := h1
  by_cases h2 : ∀ x : A, (v x).1 * (v x₀).2.1 = (v x).2.1 * (v x₀).1
  · by_cases hB₀ : (v x₀).1 = 0
    · have hC₀ : (v x₀).2.1 ≠ 0 := hx₀ hB₀
      have hB : ∀ x : A, (v x).1 = 0 := fun x => by
        have := h2 x
        rw [hB₀, mul_zero] at this
        exact (mul_eq_zero.1 this).resolve_right hC₀
      refine card_le_cube_of_injective (fun x => ((v x).2.1, (v x).2.2.2.1, (v x).2.2.2.2))
        fun x y h => hinj x y ?_
      simp only [Prod.mk.injEq] at h
      have ex := hrel x₀ x
      have ey := hrel x₀ y
      rw [hB₀, hB x] at ex
      rw [hB₀, hB y] at ey
      have hD : (v x).2.2.1 = (v y).2.2.1 := by
        have : (v x₀).2.1 * ((v x).2.2.1 + (v y).2.2.1) = 0 := by
          linear_combination (norm := char2_ring) ex + ey + (v x₀).2.2.1 * h.1
        exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hC₀)
      exact Prod.ext ((hB x).trans (hB y).symm) (Prod.ext h.1 (Prod.ext hD (Prod.ext h.2.1
        h.2.2)))
    · refine card_le_cube_of_injective (fun x => ((v x).1, (v x).2.2.1, (v x).2.2.2.2))
        fun x y h => hinj x y ?_
      simp only [Prod.mk.injEq] at h
      have hC : (v x).2.1 = (v y).2.1 := by
        have hx := h2 x
        have hy := h2 y
        have : (v x₀).1 * ((v x).2.1 + (v y).2.1) = 0 := by
          linear_combination (norm := char2_ring) hy - hx + (v x₀).2.1 * h.1
        exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hB₀)
      have hE : (v x).2.2.2.1 = (v y).2.2.2.1 := by
        have ex := hrel x₀ x
        have ey := hrel x₀ y
        have : (v x₀).1 * ((v x).2.2.2.1 + (v y).2.2.2.1) = 0 := by
          linear_combination (norm := char2_ring) ex + ey + (v x₀).2.1 * h.2.1 +
            (v x₀).2.2.1 * hC + (v x₀).2.2.2.1 * h.1
        exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hB₀)
      exact Prod.ext h.1 (Prod.ext hC (Prod.ext h.2.1 (Prod.ext hE h.2.2)))
  · push Not at h2
    obtain ⟨x₁, hx₁⟩ := h2
    have hdet : (v x₁).1 * (v x₀).2.1 + (v x₁).2.1 * (v x₀).1 ≠ 0 := fun h0 =>
      hx₁ (CharTwo.add_eq_zero.1 h0)
    refine card_le_cube_of_injective (fun x => ((v x).1, (v x).2.1, (v x).2.2.2.2))
      fun x y h => hinj x y ?_
    simp only [Prod.mk.injEq] at h
    have e0x := hrel x₀ x
    have e0y := hrel x₀ y
    have e1x := hrel x₁ x
    have e1y := hrel x₁ y
    have l0 : (v x₀).2.1 * ((v x).2.2.1 + (v y).2.2.1) +
        (v x₀).1 * ((v x).2.2.2.1 + (v y).2.2.2.1) = 0 := by
      linear_combination (norm := char2_ring) e0x + e0y + (v x₀).2.2.1 * h.2.1 +
        (v x₀).2.2.2.1 * h.1
    have l1 : (v x₁).2.1 * ((v x).2.2.1 + (v y).2.2.1) +
        (v x₁).1 * ((v x).2.2.2.1 + (v y).2.2.2.1) = 0 := by
      linear_combination (norm := char2_ring) e1x + e1y + (v x₁).2.2.1 * h.2.1 +
        (v x₁).2.2.2.1 * h.1
    have hD : (v x).2.2.1 = (v y).2.2.1 := by
      have : ((v x₁).1 * (v x₀).2.1 + (v x₁).2.1 * (v x₀).1) *
          ((v x).2.2.1 + (v y).2.2.1) = 0 := by
        linear_combination (norm := char2_ring) (v x₁).1 * l0 + (v x₀).1 * l1
      exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hdet)
    have hE : (v x).2.2.2.1 = (v y).2.2.2.1 := by
      have : ((v x₁).1 * (v x₀).2.1 + (v x₁).2.1 * (v x₀).1) *
          ((v x).2.2.2.1 + (v y).2.2.2.1) = 0 := by
        linear_combination (norm := char2_ring) (v x₁).2.1 * l0 + (v x₀).2.1 * l1
      exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hdet)
    exact Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext hD (Prod.ext hE h.2.2)))

theorem card_le_of_commute_M [Finite K] (hK : 4 ≤ Nat.card K) {A : Subgroup (ModGL .G2 K)}
    (hAM : A ≤ Model.M K) (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ Nat.card K ^ 3 := by
  choose a c d e f hv using fun x : A => mem_M.1 (hAM x.2)
  have hinj : ∀ x y : A, a x = a y → c x = c y → d x = d y → e x = e y → f x = f y → x = y :=
    fun x y h1 h2 h3 h4 h5 => Subtype.ext (by rw [hv, hv, h1, h2, h3, h4, h5])
  have hrel : ∀ x y : A, a x ^ 2 * c y + a x * d y + c x * a y ^ 2 + d x * a y = 0 ∧
      a x * c y ^ 2 + c x ^ 2 * a y + c x * d y + d x * c y = 0 := fun x y => by
    have := hA _ x.2 _ y.2
    rw [hv x, hv y] at this
    exact coords_of_commute_M this
  have hkey : ∀ x y : A, (a x * c y + c x * a y) *
      (d y + a y * c y + (a x * c y + c x * a y)) = 0 := fun x y => by
    obtain ⟨h1, h2⟩ := hrel x y
    linear_combination (norm := char2_ring) c y * h1 + a y * h2
  by_cases h0 : ∀ x : A, a x = 0 ∧ c x = 0
  · refine card_le_cube_of_injective (fun x => (d x, e x, f x)) fun x y h => ?_
    simp only [Prod.mk.injEq] at h
    exact hinj x y ((h0 x).1.trans (h0 y).1.symm) ((h0 x).2.trans (h0 y).2.symm) h.1 h.2.1
      h.2.2
  push Not at h0
  obtain ⟨x₀, hx₀⟩ := h0
  have hdz : ∀ z : A, a z = 0 → c z = 0 → d z = 0 := fun z hza hzc => by
    obtain ⟨h1, h2⟩ := hrel z x₀
    rw [hza, hzc] at h1 h2
    have h1' : d z * a x₀ = 0 := by linear_combination h1
    have h2' : d z * c x₀ = 0 := by linear_combination h2
    by_cases ha₀ : a x₀ = 0
    · exact (mul_eq_zero.1 h2').resolve_right (hx₀ ha₀)
    · exact (mul_eq_zero.1 h1').resolve_right ha₀
  have hd : ∀ x y : A, a x = a y → c x = c y → d x = d y := fun x y hxa hxc => by
    by_cases hxz : a x = 0 ∧ c x = 0
    · rw [hdz x hxz.1 hxz.2, hdz y (hxa ▸ hxz.1) (hxc ▸ hxz.2)]
    · obtain ⟨h1, h2⟩ := hrel x y
      rw [← hxa, ← hxc] at h1 h2
      have h1' : a x * (d x + d y) = 0 := by linear_combination (norm := char2_ring) h1
      have h2' : c x * (d x + d y) = 0 := by linear_combination (norm := char2_ring) h2
      rcases not_and_or.1 hxz with hax | hcx
      · exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 h1').resolve_left hax)
      · exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 h2').resolve_left hcx)
  by_cases hpar : ∀ x : A, a x * c x₀ = c x * a x₀
  · by_cases ha₀ : a x₀ = 0
    · have hax : ∀ x : A, a x = 0 := fun x => by
        have := hpar x
        rw [ha₀, mul_zero] at this
        exact (mul_eq_zero.1 this).resolve_right (hx₀ ha₀)
      refine card_le_cube_of_injective (fun x => (c x, e x, f x)) fun x y h => ?_
      simp only [Prod.mk.injEq] at h
      have h1 := (hax x).trans (hax y).symm
      exact hinj x y h1 h.1 (hd x y h1 h.1) h.2.1 h.2.2
    · refine card_le_cube_of_injective (fun x => (a x, e x, f x)) fun x y h => ?_
      simp only [Prod.mk.injEq] at h
      have h2 : c x = c y := by
        have : a x₀ * (c x + c y) = 0 := by
          linear_combination (norm := char2_ring) hpar x + hpar y + c x₀ * h.1
        exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left ha₀)
      exact hinj x y h.1 h2 (hd x y h.1 h2) h.2.1 h.2.2
  push Not at hpar
  obtain ⟨x₁, hx₁⟩ := hpar
  have hΔ : a x₀ * c x₁ + c x₀ * a x₁ ≠ 0 := fun h =>
    hx₁ (by linear_combination (norm := char2_ring) h)
  have hδ₀ : d x₀ + a x₀ * c x₀ = a x₀ * c x₁ + c x₀ * a x₁ := by
    have hne : a x₁ * c x₀ + c x₁ * a x₀ ≠ 0 := fun h => hΔ (by linear_combination h)
    have := (mul_eq_zero.1 (hkey x₁ x₀)).resolve_left hne
    linear_combination (norm := char2_ring) this
  have hδ₁ : d x₁ + a x₁ * c x₁ = a x₀ * c x₁ + c x₀ * a x₁ := by
    have := (mul_eq_zero.1 (hkey x₀ x₁)).resolve_left hΔ
    linear_combination (norm := char2_ring) this
  have hs : ∀ x : A, a x * c x₀ + c x * a x₀ = 0 ∨
      a x * c x₀ + c x * a x₀ = a x₀ * c x₁ + c x₀ * a x₁ := fun x => by
    rcases mul_eq_zero.1 (hkey x x₀) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination (norm := char2_ring) h + hδ₀)
  have ht : ∀ x : A, a x * c x₁ + c x * a x₁ = 0 ∨
      a x * c x₁ + c x * a x₁ = a x₀ * c x₁ + c x₀ * a x₁ := fun x => by
    rcases mul_eq_zero.1 (hkey x x₁) with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination (norm := char2_ring) h + hδ₁)
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
  refine card_le_cube_of_injective
    (fun x => (a x * c x₁ + c x * a x₁ + ω * (a x * c x₀ + c x * a x₀), e x, f x))
    fun x y h => ?_
  simp only [Prod.mk.injEq] at h
  obtain ⟨hst, htt⟩ := eq_of_mem_zero_delta hΔ hω0 hω1 (hs x) (hs y) (ht x) (ht y) h.1
  have hax : a x = a y := by
    have : (a x₀ * c x₁ + c x₀ * a x₁) * (a x + a y) = 0 := by
      linear_combination (norm := char2_ring) a x₁ * hst + a x₀ * htt
    exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hΔ)
  have hcx : c x = c y := by
    have : (a x₀ * c x₁ + c x₀ * a x₁) * (c x + c y) = 0 := by
      linear_combination (norm := char2_ring) c x₁ * hst + c x₀ * htt
    exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hΔ)
  exact hinj x y hax hcx (hd x y hax hcx) h.2.1 h.2.2

theorem yamada_3_17_4 [Finite K] (hK : 4 ≤ Nat.card K) {A : Subgroup (ModGL .G2 K)}
    (hA : A ≤ Model.D K ∨ A ≤ Model.M K) (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ Nat.card K ^ 3 :=
  hA.elim (fun h => card_le_of_commute_D h hcomm) fun h => card_le_of_commute_M hK h hcomm

end Model

namespace G2Data

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] (d : G2Data L K)

section Yamada316

variable [CharP K 2]

theorem yamada_3_16_1_G [Finite K] (hK : 4 ≤ Nat.card K) {E : Subgroup G} (hUE : d.U ≤ E)
    (hED : E ≤ d.D) :
    (L ⊓ normalizer (d.U : Set G) ≤ normalizer (E : Set G) → E = d.U ∨ E = d.D) ∧
      (8 ≤ Nat.card K → L ⊓ centralizer (d.U : Set G) ≤ normalizer (E : Set G) →
        E = d.U ∨ E = d.D) := by
  have hEL : E ≤ L := hED.trans (d.image_le _)
  have hU : Model.U K ≤ d.preimage E := by
    rw [← d.image_le_image_iff (Model.U_le_adjointGroup K), d.image_preimage hEL]
    exact hUE
  have hD : d.preimage E ≤ Model.D K := by
    rw [← d.image_le_image_iff (d.preimage_le E), d.image_preimage hEL]
    exact hED
  have fin : ∀ {E' : Subgroup (ModGL .G2 K)}, d.preimage E = E' → E = d.image E' := fun h => by
    rw [← h, d.image_preimage hEL]
  refine ⟨fun hN => ?_, fun h8 hN => ?_⟩
  · have hN' : adjointGroup .G2 K ⊓ normalizer (Model.U K : Set (ModGL .G2 K)) ≤
        normalizer (d.preimage E : Set (ModGL .G2 K)) := d.le_normalizer_preimage inf_le_left (by
      rw [d.image_inf_normalizer (Model.U_le_adjointGroup K)]
      exact hN)
    rcases Model.D_mod_U_irreducible hK hU hD hN' with h | h
    · exact Or.inl (fin h)
    · exact Or.inr (fin h)
  · have hN' : adjointGroup .G2 K ⊓ centralizer (Model.U K : Set (ModGL .G2 K)) ≤
        normalizer (d.preimage E : Set (ModGL .G2 K)) := d.le_normalizer_preimage inf_le_left (by
      rw [d.image_inf_centralizer _ (Model.U_le_adjointGroup K), d.image_adjointGroup]
      exact hN)
    rcases Model.D_mod_U_irreducible_centralizer h8 hU hD hN' with h | h
    · exact Or.inl (fin h)
    · exact Or.inr (fin h)

theorem yamada_3_16_2_G {E : Subgroup G} (hN : d.leviB ≤ normalizer (E : Set G)) :
    (E ≤ d.Y → E = ⊥ ∨ E = d.Y) ∧ (d.W ≤ E → E ≤ d.M → E = d.W ∨ E = d.M) := by
  have hN' : Model.leviB K ≤ normalizer (d.preimage E : Set (ModGL .G2 K)) :=
    d.le_normalizer_preimage (Model.leviB_le_adjointGroup K) hN
  refine ⟨fun hEY => ?_, fun hWE hEM => ?_⟩
  · have hEL : E ≤ L := hEY.trans (d.image_le _)
    have hY : d.preimage E ≤ Model.Y K := by
      rw [← d.image_le_image_iff (d.preimage_le E), d.image_preimage hEL]
      exact hEY
    rcases Model.Y_irreducible hY hN' with h | h
    · left
      rw [← d.image_preimage hEL, h, d.image_bot]
    · right
      rw [← d.image_preimage hEL, h]
      rfl
  · have hEL : E ≤ L := hEM.trans (d.image_le _)
    have hW : Model.W K ≤ d.preimage E := by
      rw [← d.image_le_image_iff Model.W_le_adjointGroup, d.image_preimage hEL]
      exact hWE
    have hM : d.preimage E ≤ Model.M K := by
      rw [← d.image_le_image_iff (d.preimage_le E), d.image_preimage hEL]
      exact hEM
    rcases Model.M_mod_W_irreducible hW hM hN' with h | h
    · left
      rw [← d.image_preimage hEL, h]
      rfl
    · right
      rw [← d.image_preimage hEL, h]
      rfl

theorem yamada_3_16_2_natural_G [Finite K] :
    ∃ ρ : SL2 K →* G, ρ.range = d.leviB ∧ Function.Injective ρ ∧
      (∃ φ : (Fin 2 → K) → G, Function.Injective φ ∧ Set.range φ = d.Y ∧
        (∀ v w, φ (v + w) = φ v * φ w) ∧ ∀ (g : SL2 K) (v : Fin 2 → K),
          ρ g * φ v * (ρ g)⁻¹ = φ (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v)) ∧
      ∃ ψ : (Fin 2 → K) → G, (∀ v, ψ v ∈ d.M) ∧ (∀ v, ψ v ∈ d.W → v = 0) ∧
        (∀ x ∈ d.M, ∃ v, (ψ v)⁻¹ * x ∈ d.W) ∧ (∀ v w, (ψ v * ψ w)⁻¹ * ψ (v + w) ∈ d.W) ∧
        ∀ (g : SL2 K) (v : Fin 2 → K),
          (ψ (Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) K) v))⁻¹ * (ρ g * ψ v * (ρ g)⁻¹) ∈ d.W := by
  obtain ⟨ρ, hrange, hinj, hu, hv, -⟩ := Model.natural_Y (K := K)
  have hρA : ∀ g, ρ g ∈ adjointGroup .G2 K := fun g =>
    Model.leviB_le_adjointGroup K (hrange ▸ ⟨g, rfl⟩)
  let ρ' : SL2 K →* adjointGroup .G2 K := ρ.codRestrict _ hρA
  have hYA : ∀ v : Fin 2 → K, g2N 0 0 0 0 (v 1) (v 0) ∈ adjointGroup .G2 K := fun v =>
    Model.Y_le_adjointGroup ⟨_, _, rfl⟩
  have hMA : ∀ v : Fin 2 → K, g2N (v 1) 0 (v 0) 0 0 0 ∈ adjointGroup .G2 K := fun v =>
    Model.M_le_adjointGroup ⟨_, _, _, _, _, rfl⟩
  have hconj : ∀ (g : SL2 K) (m : adjointGroup .G2 K),
      d.emb (ρ' g) * d.emb m * (d.emb (ρ' g))⁻¹ = d.emb (ρ' g * m * (ρ' g)⁻¹) := fun g m => by
    rw [map_mul, map_mul, map_inv]
  have hρ' : ∀ g, (ρ' g : ModGL .G2 K) = ρ g := fun g => rfl
  have hfin : ∀ v : Fin 2 → K, v = ![v 0, v 1] := fun v => by
    ext i
    fin_cases i <;> rfl
  refine ⟨d.emb.comp ρ', ?_, fun g k h => hinj (congrArg Subtype.val (d.emb_injective h)), ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact d.emb_mem_image (g := ρ' g) (hrange ▸ ⟨g, rfl⟩)
    · intro hx
      obtain ⟨m, hm, rfl⟩ := d.mem_image.1 hx
      rw [← hrange] at hm
      obtain ⟨g, hg⟩ := hm
      exact ⟨g, congrArg d.emb (Subtype.ext hg)⟩
  · refine ⟨fun v => d.emb ⟨_, hYA v⟩, fun v w h => ?_, ?_, fun v w => ?_, fun g v => ?_⟩
    · have h₀ := d.emb_injective h
      obtain ⟨-, -, -, -, h1, h0⟩ := g2N_injective (Subtype.mk.inj h₀)
      rw [hfin v, hfin w, h0, h1]
    · ext x
      constructor
      · rintro ⟨v, rfl⟩
        exact d.emb_mem_image (g := ⟨_, hYA v⟩) ⟨_, _, rfl⟩
      · intro hx
        obtain ⟨m, hm, rfl⟩ := d.mem_image.1 hx
        obtain ⟨E, F, hEF⟩ := hm
        refine ⟨![F, E], congrArg d.emb (Subtype.ext ?_)⟩
        rw [hEF]
        rfl
    · show d.emb ⟨_, hYA (v + w)⟩ = d.emb ⟨_, hYA v⟩ * d.emb ⟨_, hYA w⟩
      rw [← map_mul]
      refine congrArg d.emb (Subtype.ext ?_)
      show g2N 0 0 0 0 ((v + w) 1) ((v + w) 0) =
        g2N 0 0 0 0 (v 1) (v 0) * g2N 0 0 0 0 (w 1) (w 0)
      rw [g2N_mul_coords]
      refine g2N_eq_g2N ?_ ?_ ?_ ?_ ?_ ?_ <;> (try simp only [Pi.add_apply]) <;> ring
    · show d.emb (ρ' g) * d.emb ⟨_, hYA v⟩ * (d.emb (ρ' g))⁻¹ = d.emb ⟨_, hYA _⟩
      rw [hconj]
      refine congrArg d.emb (Subtype.ext ?_)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ']
      exact Model.conj_Y_of_uv hu hv g v
  · refine ⟨fun v => d.emb ⟨_, hMA v⟩, fun v => d.emb_mem_image (g := ⟨_, hMA v⟩)
      ⟨_, _, _, _, _, rfl⟩, fun v hvW => ?_, fun x hx => ?_, fun v w => ?_, fun g v => ?_⟩
    · have h' : g2N (v 1) 0 (v 0) 0 0 0 ∈ Model.W K :=
        (d.emb_mem_image_iff (g := ⟨_, hMA v⟩)).1 hvW
      obtain ⟨h1, -, h0⟩ := Model.g2N_mem_W_iff.1 h'
      rw [hfin v, h0, h1]
      ext i
      fin_cases i <;> rfl
    · obtain ⟨m, hm, rfl⟩ := d.mem_image.1 hx
      obtain ⟨A, C, D, E, F, hm⟩ := hm
      refine ⟨![C, A], ?_⟩
      show (d.emb ⟨_, hMA ![C, A]⟩)⁻¹ * d.emb m ∈ d.W
      rw [← map_inv, ← map_mul]
      refine d.emb_mem_image ?_
      show (g2N A 0 C 0 0 0)⁻¹ * (m : ModGL .G2 K) ∈ Model.W K
      rw [hm]
      exact Model.g2N_inv_mul_mem_W _ _ _ _ _ _ _ _
    · show (d.emb ⟨_, hMA v⟩ * d.emb ⟨_, hMA w⟩)⁻¹ * d.emb ⟨_, hMA (v + w)⟩ ∈ d.W
      rw [← map_mul, ← map_inv, ← map_mul]
      refine d.emb_mem_image ?_
      show (g2N (v 1) 0 (v 0) 0 0 0 * g2N (w 1) 0 (w 0) 0 0 0)⁻¹ *
        g2N ((v + w) 1) 0 ((v + w) 0) 0 0 0 ∈ Model.W K
      obtain ⟨D', E', F', h⟩ := Model.g2N_mul_M (v 1) (v 0) 0 0 0 (w 1) (w 0) 0 0 0
      rw [h]
      exact Model.g2N_inv_mul_mem_W _ _ _ _ _ _ _ _
    · show (d.emb ⟨_, hMA _⟩)⁻¹ * (d.emb (ρ' g) * d.emb ⟨_, hMA v⟩ * (d.emb (ρ' g))⁻¹) ∈ d.W
      rw [hconj, ← map_inv, ← map_mul]
      refine d.emb_mem_image ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hρ']
      obtain ⟨D', E', F', h⟩ := Model.conj_M_of_uv hu hv g v 0 0 0
      rw [h]
      exact Model.g2N_inv_mul_mem_W _ _ _ _ _ _ _ _

end Yamada316

section Yamada317

variable [CharP K 2]

omit
  [CharP K 2] in
theorem conj_le_adjointGroup {H : Subgroup (ModGL .G2 K)} (hH : H ≤ adjointGroup .G2 K)
    {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K) :
    H.map (MulAut.conj g).toMonoidHom ≤ adjointGroup .G2 K := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hg (hH hx)) (inv_mem hg)

theorem yamada_3_17_1_G [Finite K] (hK : 4 ≤ Nat.card K) :
    Maximal (fun E : Subgroup G => E ≤ L ∧ CFSG.IsElementaryAbelian 2 E) d.X ∧
      Maximal (fun E : Subgroup G => E ≤ L ∧ CFSG.IsElementaryAbelian 2 E) d.W ∧
      (∀ g ∈ L, d.X.map (MulAut.conj g).toMonoidHom ≠ d.W) ∧
      ∀ E : Subgroup G, Maximal (fun E : Subgroup G => E ≤ L ∧ CFSG.IsElementaryAbelian 2 E) E →
        ∃ g ∈ L, E = d.X.map (MulAut.conj g).toMonoidHom ∨
          E = d.W.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hX, hW, hXW, hall⟩ := Model.yamada_3_17_1 hK
  have htr := d.maximal_iff_image (P := fun E' : Subgroup (ModGL .G2 K) =>
      E' ≤ adjointGroup .G2 K ∧ CFSG.IsElementaryAbelian 2 E')
    (PG := fun E : Subgroup G => E ≤ L ∧ CFSG.IsElementaryAbelian 2 E) (fun E hE => hE.1)
    (fun E' hE' => hE'.1) (fun E' hE' => by
      rw [d.isElementaryAbelian_image_iff hE']
      exact ⟨fun h => ⟨hE', h.2⟩, fun h => ⟨d.image_le _, h.2⟩⟩)
  refine ⟨(htr _).2 ⟨_, hX, rfl⟩, (htr _).2 ⟨_, hW, rfl⟩, ?_, fun E hE => ?_⟩
  · intro g hgL h
    obtain ⟨g', rfl⟩ := d.exists_emb_eq hgL
    rw [G2Data.X, G2Data.W, ← d.image_map_conj, d.image_inj (conj_le_adjointGroup
      Model.X_le_adjointGroup g'.2) Model.W_le_adjointGroup] at h
    exact hXW _ g'.2 h
  · obtain ⟨E', hE', rfl⟩ := (htr E).1 hE
    obtain ⟨g, hg, h | h⟩ := hall E' hE'
    · refine ⟨d.emb ⟨g, hg⟩, d.emb_mem _, Or.inl ?_⟩
      rw [h]
      exact d.image_map_conj ⟨g, hg⟩ (Model.X K)
    · refine ⟨d.emb ⟨g, hg⟩, d.emb_mem _, Or.inr ?_⟩
      rw [h]
      exact d.image_map_conj ⟨g, hg⟩ (Model.W K)

theorem yamada_3_17_4_G [Finite K] (hK : 4 ≤ Nat.card K) {E : Subgroup G}
    (hE : E ≤ d.D ∨ E ≤ d.M) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ Nat.card K ^ 3 := by
  have hEL : E ≤ L := hE.elim (fun h => h.trans (d.image_le _)) fun h => h.trans (d.image_le _)
  have hcomm' : ∀ x ∈ d.preimage E, ∀ y ∈ d.preimage E, x * y = y * x := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨k, hk, rfl⟩
    have := hcomm _ hg _ hk
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (d.emb_injective this)
  have hle : ∀ {H : Subgroup (ModGL .G2 K)}, E ≤ d.image H → d.preimage E ≤ H := fun h => by
    rw [← d.image_le_image_iff (d.preimage_le E), d.image_preimage hEL]
    exact h
  rw [← d.image_preimage hEL, d.card_image (d.preimage_le E)]
  exact Model.yamada_3_17_4 hK (hE.imp (fun h => hle (H := Model.D K) h)
    (fun h => hle (H := Model.M K) h)) hcomm'

end Yamada317

end G2Data

end CFSG.LocalAnalysis.EvenBN.G2
