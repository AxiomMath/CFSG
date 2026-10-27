module

public import CFSG.LieType.Ree.ReeBorelCoreCenter
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.LieType.Ree.LargeReeB2FixedCoordinates
public import CFSG.LieType.Chevalley.GraphFixedCenterTrivial

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace ReeTag

variable {K : Type} [Field K]

theorem conj_largeReeP
    {g : (Module.End K (RootModule Tag.F4 K))ˣ} (c : Fin 4 → K)
    (hg : ∀ i x, g * largeReeX K i x * g⁻¹ = largeReeX K i (c i * x)) (A B C D : K) :
    g * largeReeP K A B C D * g⁻¹ = largeReeP K (c 0 * A) (c 1 * B) (c 2 * C) (c 3 * D) := by
  simp only [largeReeP]
  rw [show g * (largeReeX K 0 A * largeReeX K 1 B * largeReeX K 2 C * largeReeX K 3 D) * g⁻¹ =
      (g * largeReeX K 0 A * g⁻¹) * (g * largeReeX K 1 B * g⁻¹) * (g * largeReeX K 2 C * g⁻¹) *
        (g * largeReeX K 3 D * g⁻¹) by group, hg, hg, hg, hg]

theorem largeReeRoot_zero_one :
    (largeReeRoot 0 : Fin F4.tag.rank → ℤ) = Pi.single (⟨2, by decide⟩ : Fin F4.tag.rank) 1 ∧
      (largeReeRoot 1 : Fin F4.tag.rank → ℤ) = Pi.single (⟨1, by decide⟩ : Fin F4.tag.rank) 1 := by
  constructor <;>
  · funext ⟨i, hi⟩
    change i < 4 at hi
    interval_cases i <;> rfl

theorem large_Ree_fixed_group_center_trivial
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.center (F4.reeGamma K a) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH : (z : ModGL F4.tag K) ∈ F4.reeFixedTorus K a :=
    mem_reeFixedTorus_of_mem_normalCore (center_le_normalCore_reeFixedBorel hz)
  have hzT : (z : ModGL F4.tag K) ∈ torusGroup F4.tag K := (Subgroup.mem_inf.1 hzH).1
  obtain ⟨l, hl⟩ := exists_torus_characters hzT
  have hsingle : ∀ i : Fin F4.tag.rank,
      (∏ j, l j ^ (Pi.single i 1 : Fin F4.tag.rank → ℤ) j : Kˣ) = l i := fun i => by
    rw [Finset.prod_eq_single i (fun j _ hji => by rw [Pi.single_eq_of_ne hji, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  have hcomm : ∀ g ∈ F4.reeGamma K a, (z : ModGL F4.tag K) * g * (z : ModGL F4.tag K)⁻¹ = g :=
    fun g hg => by
      have h := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
      have h' : g * (z : ModGL F4.tag K) = (z : ModGL F4.tag K) * g := congrArg Subtype.val h
      rw [← h', mul_inv_cancel_right]
  have hconjX : ∀ (i : Fin F4.tag.rank) (c : K),
      (z : ModGL F4.tag K) * xUnit F4.tag K i c * (z : ModGL F4.tag K)⁻¹ =
        xUnit F4.tag K i ((l i : K) * c) := fun i c => by
    rw [← pinnedX_single, (hl _ (isRoot_single _ i)).2, hsingle, pinnedX_single]
  have hx1 : xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 ((1 : K) ^ 2 ^ a) ∈
      F4.reeGamma K a := by
    have h : xUnit F4.tag K largeReeI1 1 * xUnit F4.tag K largeReeI4 ((1 : K) ^ 2 ^ a) ∈
        (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ : Set (ModGL F4.tag K)) := by
      rw [coe_reeFixedOrbitUnipotent_zero hK]
      exact ⟨1, rfl⟩
    exact (Subgroup.mem_inf.1 h).2
  have h1 := hcomm _ hx1
  rw [show (z : ModGL F4.tag K) * (xUnit F4.tag K largeReeI1 1 *
      xUnit F4.tag K largeReeI4 ((1 : K) ^ 2 ^ a)) * (z : ModGL F4.tag K)⁻¹ =
      ((z : ModGL F4.tag K) * xUnit F4.tag K largeReeI1 1 * (z : ModGL F4.tag K)⁻¹) *
        ((z : ModGL F4.tag K) * xUnit F4.tag K largeReeI4 ((1 : K) ^ 2 ^ a) *
          (z : ModGL F4.tag K)⁻¹) by group, hconjX, hconjX] at h1
  obtain ⟨e0, e3⟩ := largeRee_x_inj h1
  simp only [one_pow, mul_one] at e0 e3
  set c : Fin 4 → K := fun i =>
    ((∏ j, l j ^ (largeReeRoot i : Fin F4.tag.rank → ℤ) j : Kˣ) : K) with hc
  let g : (Module.End K (RootModule Tag.F4 K))ˣ := (z : ModGL F4.tag K)
  have hgR : ∀ i x, g * largeReeX K i x * g⁻¹ = largeReeX K i (c i * x) := fun i x =>
    (hl _ (largeReeRoot_pos i).1).2 x
  have hu : largeReeCoord a K 1 0 ∈ F4.reeGamma K a :=
    (Subgroup.mem_inf.1 ((bijOn_largeReeCoord hK).1 (Set.mem_univ ((1 : K), (0 : K))))).2
  have h2 : largeReeP K (c 0 * 1) (c 1 * largeReeSigma a 1) (c 2 * 0)
      (c 3 * (largeReeSigma a 0 + 1 ^ 2 * largeReeSigma a 1)) =
        largeReeP K 1 (largeReeSigma a 1) 0 (largeReeSigma a 0 + 1 ^ 2 * largeReeSigma a 1) :=
    (conj_largeReeP c hgR _ _ _ _).symm.trans (hcomm _ hu)
  obtain ⟨e2, e1, -, -⟩ := largeReeP_injective h2
  have hσ1 : largeReeSigma a (1 : K) = 1 := one_pow _
  rw [hσ1, mul_one] at e1
  rw [mul_one] at e2
  obtain ⟨hr0, hr1⟩ := largeReeRoot_zero_one
  have e2' : l ⟨2, by decide⟩ = 1 := by
    have h : (∏ j, l j ^ (largeReeRoot 0 : Fin F4.tag.rank → ℤ) j : Kˣ) = l ⟨2, by decide⟩ := by
      rw [hr0]
      exact hsingle _
    exact Units.ext (h ▸ e2)
  have e1' : l ⟨1, by decide⟩ = 1 := by
    have h : (∏ j, l j ^ (largeReeRoot 1 : Fin F4.tag.rank → ℤ) j : Kˣ) = l ⟨1, by decide⟩ := by
      rw [hr1]
      exact hsingle _
    exact Units.ext (h ▸ e1)
  have hl1 : ∀ i, l i = 1 := by
    rintro ⟨i, hi⟩
    change i < 4 at hi
    interval_cases i
    · exact Units.ext e0
    · exact e1'
    · exact e2'
    · exact Units.ext e3
  have hchar : ∀ α : Fin F4.tag.rank → ℤ, (∏ j, l j ^ α j : Kˣ) = 1 := fun α => by
    simp [hl1]
  refine Subtype.ext (Units.ext (end_ext_of_hVec_rootVec (fun j => ?_) fun α hα => ?_))
  · rw [Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    exact ((triangular_borel_structure.{0, 0} F4.tag K).2.1 _ hzT).1 j
  · rw [Subgroup.coe_one, Units.val_one, Module.End.one_apply, (hl α hα).1, hchar, Units.val_one,
      one_smul]

end ReeTag

end CFSG.LieType.Ree
