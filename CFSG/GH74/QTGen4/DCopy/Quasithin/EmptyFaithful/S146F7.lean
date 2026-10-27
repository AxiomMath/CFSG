module

public import CFSG.Quasithin.EmptyFaithful.S146F7
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Vocabulary

variable {G : Type} [Group G]

@[expose] def Stage14613Lab_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        (Case13One T M H p H₁ ∨ Case13Two T M H p H₁) ∨
          (Case13One T M H p H₂ ∨ Case13Two T M H p H₂)

end Vocabulary

section Steps

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.false_of_conj_Z_F4 (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616_F4)
    (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) {z g : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hconj : g * z * g⁻¹ = u) : False :=
  (h4 G T M S H hred.isHTM u (h.isInvU_of_fixed_F4 S h5 h16 hred hmax hMod hF hu huZ huT)).2.2 g z hz hz1
    hconj

theorem IsDec12.false_of_conj_gen_F4 (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616_F4)
    (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {w g z y : G} (hw : w ∈ uHi T M H H₁)
    (hwZ : w ∉ quasithinOmegaOneCenter T) (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hwg : g * z * g⁻¹ = w) (hy : y ∈ H₀)
    (hyT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (y * w * y⁻¹)) : False := by
  have hH : IsHTM T M H := hred.isHTM
  have hy' : y ∈ H := h.le hy
  have hu'1 : y * w * y⁻¹ ∈ uHi T M H H₁ :=
    (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_uHi₁ S hred hy) w).mp hw
  have hu'Z : y * w * y⁻¹ ∉ quasithinOmegaOneCenter T := by
    intro hu'Z
    apply hwZ
    have hcomm : y⁻¹ * (y * w * y⁻¹) = (y * w * y⁻¹) * y⁻¹ :=
      S146T.comm_Z (Subgroup.inv_mem _ (S.le_mcOf hH hy')) hu'Z
    have e : w = y⁻¹ * (y * w * y⁻¹) * y := by group
    rw [e, hcomm]
    simpa [mul_assoc] using hu'Z
  refine h.false_of_conj_Z_F4 S h5 h16 h4 hred hmax hMod hF hu'1 hu'Z hyT hz hz1 (g := y * g) ?_
  rw [← hwg]
  group

theorem IsDec12.not_case13Two_F4 (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616_F4)
    (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    (hγ : ∀ V' : Subgroup G, IsElemAbelian 2 V' → V' ≤ H₁ → ¬ V' ≤ pCoreOf 2 H →
      ∀ w ∈ V', w ∈ uHi T M H H₁ →
        ∃ y ∈ H₀, T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (y * w * y⁻¹))
    (hc : Case13Two T M H p H₁) : False := by
  obtain ⟨-, -, γ, γ', g, hsetup, hD, hUγ, hA, -⟩ := hc
  have hH : IsHTM T M H := hred.isHTM
  have hF81 : HypF81 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) H :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).1
  have hUab : IsElemAbelian 2 (F8.Uγ (VZ T M) H (g : G)) :=
    isElemAbelian_conjSub' (F8.isElemAbelian_conjClosure hF81) (g : G)
  have hUQ : ¬ F8.Uγ (VZ T M) H (g : G) ≤ pCoreOf 2 H := by
    intro hle
    apply hD.2
    intro x hx
    exact mem_centralizerMod.mpr ⟨hx, Subgroup.centralizer_le_normalizer _
      (le_centralizer_quasithinOmegaOneCenter T (S.pCoreOf_le_T hH (hle hx))),
      fun u hu => S.comm_mem_Z hH hu (hle hx)⟩
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  have hwA : (g : G) * z * (g : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G) :=
    mem_conjSub.mpr (by simpa [mul_assoc] using hz)
  have hwU : (g : G) * z * (g : G)⁻¹ ∈ F8.Uγ (VZ T M) H (g : G) :=
    mem_conjSub.mpr (by simpa [mul_assoc] using Z_le_conjClosure_VZ T M H hz)
  obtain ⟨y, hy, hyT⟩ := hγ _ hUab hUγ hUQ _ hwU (hA hwA)
  exact h.false_of_conj_gen_F4 S h5 h16 h4 hred hmax hMod hF (hA hwA)
    (S.conj_not_mem_Z hH hsetup hz hz1) hz hz1 rfl hy hyT

theorem IsDec12.not_A₁_le_uHi_F4 (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616_F4)
    (h4 : Stage1463Four) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    (hOrb : ∀ w ∈ uHi T M H H₁, w ∉ quasithinOmegaOneCenter T →
      ∃ y ∈ H₁, T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T (y * w * y⁻¹))
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hsetup : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) :
    ¬ F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ uHi T M H H₁ := by
  intro hA
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  have hwA : (g : G) * z * (g : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G) :=
    mem_conjSub.mpr (by simpa [mul_assoc] using hz)
  have hwZ := S.conj_not_mem_Z hH hsetup hz hz1
  obtain ⟨y, hy, hyT⟩ := hOrb _ (hA hwA) hwZ
  exact h.false_of_conj_gen_F4 S h5 h16 h4 hred hmax hMod hF (hA hwA) hwZ hz hz1 rfl
    (h.le₁ hy) hyT

end Steps

end CFSG.Quasithin
