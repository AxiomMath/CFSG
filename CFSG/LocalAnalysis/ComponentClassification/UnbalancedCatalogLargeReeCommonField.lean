module

public import CFSG.LieType.Ree.LargeReeFixedGroupSchreier
public import CFSG.LieType.Ree.LargeReeCenterTrivial

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Ree.ReeTag
open scoped MatrixGroups

namespace LargeReeCatalog

section Elements

variable {K : Type} [Field K]

@[expose] def largeReeA1X (a : ℕ) (c : K) : ModGL F4.tag K :=
  xUnit F4.tag K largeReeI1 c * xUnit F4.tag K largeReeI4 (c ^ 2 ^ a)

@[expose] def largeReeA1H (a : ℕ) (t : Kˣ) : ModGL F4.tag K :=
  torusElt F4.tag K largeReeI1 t * torusElt F4.tag K largeReeI4 (t ^ 2 ^ a)

theorem largeReeA1X_injective {a : ℕ} {c d : K} (h : largeReeA1X a c = largeReeA1X a d) :
    c = d :=
  (largeRee_x_inj h).1

end Elements

variable (K : Type) [Field K] [Finite K] [CharP K F4.prime] (a : ℕ) in
abbrev largeReeOppAut :
    Subgroup (MulAut (F4.reeGamma K a)) :=
  pairAutSubgroup ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a))
    ((F4.reeFixedNegUnipotent K a).subgroupOf (F4.reeGamma K a))

theorem coe_apply_congr {G : Type*} [Group G] {Γ : Subgroup G} (α : MulAut Γ) {g g' : G}
    (h : g = g') (hg : g ∈ Γ) (hg' : g' ∈ Γ) :
    ((α ⟨g, hg⟩ : Γ) : G) = ((α ⟨g', hg'⟩ : Γ) : G) := by
  subst h
  rfl

section Membership

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem largeReeA1X_mem_U1 (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    largeReeA1X a c ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ := by
  rw [← SetLike.mem_coe, coe_reeFixedOrbitUnipotent_zero hK]
  exact ⟨c, rfl⟩

theorem exists_largeReeA1X_eq (hK : Nat.card K = 2 ^ (2 * a + 1)) {g : ModGL F4.tag K}
    (hg : g ∈ F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩) : ∃ c, largeReeA1X a c = g := by
  rw [← SetLike.mem_coe, coe_reeFixedOrbitUnipotent_zero hK] at hg
  exact hg

theorem largeReeA1X_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (c : K) :
    largeReeA1X a c ∈ F4.reeGamma K a :=
  (Subgroup.mem_inf.1 (largeReeA1X_mem_U1 hK c)).2

omit [Finite K] in
theorem largeReeA1Hom_HSL_eq (t : Kˣ) : largeReeA1Hom K a (HSL t) = largeReeA1H a t := by
  rw [largeReeA1Hom_HSL, largeReeA1H]
  congr 2

theorem largeReeA1Hom_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL2 K) :
    largeReeA1Hom K a g ∈ F4.reeLocalBlock K a ⟨0, by decide⟩ := by
  change _ ∈ largeReeA1M K a
  rw [← largeReeA1Hom_range hK]
  exact ⟨g, rfl⟩

theorem largeReeA1H_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ) :
    largeReeA1H a t ∈ F4.reeGamma K a := by
  rw [← largeReeA1Hom_HSL_eq]
  exact reeLocalBlock_le_reeGamma _ (largeReeA1Hom_mem hK _)

theorem largeReeCoord_mem_reeGamma (hK : Nat.card K = 2 ^ (2 * a + 1)) (s v : K) :
    largeReeCoord a K s v ∈ F4.reeGamma K a :=
  (Subgroup.mem_inf.1 (largeReeCoord_mem hK s v)).2

theorem U1_le_reeGamma : F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩ ≤ F4.reeGamma K a :=
  (reeFixedOrbitUnipotent_le_reeLocalBlock _).trans (reeLocalBlock_le_reeGamma _)

theorem U2_le_reeGamma : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≤ F4.reeGamma K a :=
  (reeFixedOrbitUnipotent_le_reeLocalBlock _).trans (reeLocalBlock_le_reeGamma _)

end Membership

section Torus

variable {K : Type} [Field K] {a : ℕ}

theorem largeReeA1H_conj_largeReeX (t : Kˣ) (i : Fin 4) (x : K) :
    (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a)) *
        largeReeX K i x *
        (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a))⁻¹ =
      largeReeX K i (((t ^ (∑ j, Tag.F4.cartan ⟨0, by decide⟩ j * largeReeRoot i j) : Kˣ) : K) *
        ((((t ^ 2 ^ a) ^ (∑ j, Tag.F4.cartan ⟨3, by decide⟩ j * largeReeRoot i j) : Kˣ) : K) *
          x)) := by
  rw [show ∀ A B X : (Module.End K (RootModule Tag.F4 K))ˣ,
      A * B * X * (A * B)⁻¹ = A * (B * X * B⁻¹) * A⁻¹ from fun A B X => by group]
  rw [largeReeX, root_torus_conjugation _ (largeReeRoot_pos i).1,
    root_torus_conjugation _ (largeReeRoot_pos i).1]
  rfl

variable [Finite K]

theorem largeReeA1H_conj_largeReeCoord (hK : Nat.card K = 2 ^ (2 * a + 1)) (t : Kˣ) (s v : K) :
    (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a)) *
        largeReeCoord a K s v *
        (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a))⁻¹ =
      largeReeCoord a K (((t : K) ^ 2 ^ a)⁻¹ * s) (((t : K) * (t : K) ^ 2 ^ a)⁻¹ * v) := by
  obtain ⟨ρ, σ, hρ, hσ, hρσ, -, -, -⟩ := large_Ree_field_powers a K hK
  have hσρ : ∀ c, σ (ρ c) = c := fun c => congrArg (fun e : K ≃+* K => e c) hρσ
  have hσsq : ∀ c, σ c = ρ c ^ 2 := fun c => by rw [hσ, hρ, ← pow_mul, mul_comm]
  have hs : ∀ c, largeReeSigma a c = σ c := fun c => (hσ c).symm
  have hr : ∀ c : K, c ^ 2 ^ a = ρ c := fun c => (hρ c).symm
  have ht : (t : K) ≠ 0 := t.ne_zero
  have hρt : ρ t ≠ 0 := (map_ne_zero ρ).2 ht
  let m : Fin 4 → K := fun i =>
    ((t ^ (∑ j, Tag.F4.cartan ⟨0, by decide⟩ j * largeReeRoot i j) : Kˣ) : K) *
      (((t ^ 2 ^ a) ^ (∑ j, Tag.F4.cartan ⟨3, by decide⟩ j * largeReeRoot i j) : Kˣ) : K)
  have hc : ∀ i x,
      (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a)) *
        largeReeX K i x *
        (torusElt Tag.F4 K ⟨0, by decide⟩ t * torusElt Tag.F4 K ⟨3, by decide⟩ (t ^ 2 ^ a))⁻¹ =
      largeReeX K i (m i * x) := fun i x => by
    rw [largeReeA1H_conj_largeReeX, mul_assoc]
  have s0 : ∀ i : Fin 4, (∑ j, Tag.F4.cartan ⟨0, by decide⟩ j * largeReeRoot i j) =
      ![0, -1, -1, -1] i := by decide
  have s3 : ∀ i : Fin 4, (∑ j, Tag.F4.cartan ⟨3, by decide⟩ j * largeReeRoot i j) =
      ![-1, 0, -1, -2] i := by decide
  have m0 : m 0 = (ρ t)⁻¹ := by
    simp only [m, s0, s3]
    simp [hr]
  have m1 : m 1 = (t : K)⁻¹ := by
    simp only [m, s0, s3]
    simp
  have m2 : m 2 = (t : K)⁻¹ * (ρ t)⁻¹ := by
    simp only [m, s0, s3]
    simp [hr]
  have m3 : m 3 = (t : K)⁻¹ * ((ρ t) ^ 2)⁻¹ := by
    simp only [m, s0, s3]
    simp [hr]
  have key := conj_largeReeP m hc s (largeReeSigma a s) v
    (largeReeSigma a v + s ^ 2 * largeReeSigma a s)
  refine key.trans ?_
  simp only [largeReeCoord, hs, hr, m0, m1, m2, m3, map_mul, map_inv₀, hσρ]
  rw [hσsq t]
  congr 1 <;> field_simp

end Torus

section A1

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

@[expose] def largeReeA1Rep (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    SL2 K →* F4.reeLocalBlock K a ⟨0, by decide⟩ :=
  (largeReeA1Hom K a).codRestrict _ (largeReeA1Hom_mem hK)

theorem coe_largeReeA1Rep (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL2 K) :
    (largeReeA1Rep hK g : ModGL F4.tag K) = largeReeA1Hom K a g :=
  rfl

theorem largeReeA1Rep_surjective (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Function.Surjective (largeReeA1Rep hK) := by
  rintro ⟨x, hx⟩
  have hx' : x ∈ largeReeA1M K a := hx
  rw [← largeReeA1Hom_range hK] at hx'
  obtain ⟨g, rfl⟩ := hx'
  exact ⟨g, rfl⟩

theorem largeReeA1Rep_ker (hK : Nat.card K = 2 ^ (2 * a + 1)) (g : SL(2, K))
    (hg : largeReeA1Rep hK g = 1) : ∃ l : Kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) K) = (l : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h1 : g = 1 := eq_one_of_largeReeA1Hom_eq_one a (congrArg Subtype.val hg)
  exact ⟨1, one_pow 2, by rw [h1]; simp⟩

theorem sl2RootX_largeReeA1Rep (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sl2RootX (largeReeA1Rep hK) = (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩).subgroupOf
      (F4.reeLocalBlock K a ⟨0, by decide⟩) := by
  ext ⟨x, hx⟩
  rw [mem_sl2RootX, Subgroup.mem_subgroupOf, ← SetLike.mem_coe,
    coe_reeFixedOrbitUnipotent_zero hK]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_uSL a c).symm.trans (congrArg Subtype.val hc)⟩,
    fun ⟨c, hc⟩ => ⟨c, Subtype.ext ((largeReeA1Hom_uSL a c).trans hc)⟩⟩

theorem sl2RootY_largeReeA1Rep (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    sl2RootY (largeReeA1Rep hK) = (F4.reeFixedOrbitNegUnipotent K a ⟨0, by decide⟩).subgroupOf
      (F4.reeLocalBlock K a ⟨0, by decide⟩) := by
  ext ⟨x, hx⟩
  rw [mem_sl2RootY, Subgroup.mem_subgroupOf]
  change _ ↔ x ∈ largeReeA1Y K a
  rw [← SetLike.mem_coe, coe_largeReeA1Y hK]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, (largeReeA1Hom_vSL a c).symm.trans (congrArg Subtype.val hc)⟩,
    fun ⟨c, hc⟩ => ⟨c, Subtype.ext ((largeReeA1Hom_vSL a c).trans hc)⟩⟩

theorem exists_largeReeA1_params (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : MulAut (F4.reeGamma K a)} (hα : α ∈ largeReeOppAut K a) :
    ∃ (b : Kˣ) (β : K ≃+* K),
      (∀ c, ((α ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
        largeReeA1X a (b * β c)) ∧
      ∀ t, ((α ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
        largeReeA1H a (Units.map β.toMonoidHom t) := by
  obtain ⟨-, ⟨φ, -, hφ, -⟩, -⟩ := large_Ree_fixed_group_Schreier a ha K hK
  have hmem : ((φ ⟨α, hα⟩).1 : MulAut (F4.reeLocalBlock K a ⟨0, by decide⟩)) ∈
      pairAutSubgroup (sl2RootX (largeReeA1Rep hK)) (sl2RootY (largeReeA1Rep hK)) := by
    rw [sl2RootX_largeReeA1Rep, sl2RootY_largeReeA1Rep]
    exact (φ ⟨α, hα⟩).1.2
  obtain ⟨⟨b, β⟩, ⟨hu, -, hd⟩, -⟩ := (central_SL2_root_pair_semilinear_parameters
    (largeReeA1Rep hK) (largeReeA1Rep_surjective hK) (largeReeA1Rep_ker hK)).1 _ hmem
  refine ⟨b, β, fun c => ?_, fun t => ?_⟩
  · calc ((α ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ : F4.reeGamma K a) : ModGL F4.tag K)
        = ((α ⟨(largeReeA1Rep hK (sl2Upper K c) : ModGL F4.tag K),
            reeLocalBlock_le_reeGamma _ (largeReeA1Rep hK (sl2Upper K c)).2⟩ :
              F4.reeGamma K a) : ModGL F4.tag K) :=
          coe_apply_congr α (largeReeA1Hom_uSL a c).symm _ _
      _ = (((φ ⟨α, hα⟩).1 : MulAut (F4.reeLocalBlock K a ⟨0, by decide⟩))
            (largeReeA1Rep hK (sl2Upper K c)) : ModGL F4.tag K) :=
          (hφ ⟨α, hα⟩ (largeReeA1Rep hK (sl2Upper K c))).symm
      _ = (largeReeA1Rep hK (sl2Upper K (b * β c)) : ModGL F4.tag K) :=
          congrArg Subtype.val (hu c)
      _ = largeReeA1X a (b * β c) := largeReeA1Hom_uSL a _
  · calc ((α ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) : ModGL F4.tag K)
        = ((α ⟨(largeReeA1Rep hK (sl2Diag K t) : ModGL F4.tag K),
            reeLocalBlock_le_reeGamma _ (largeReeA1Rep hK (sl2Diag K t)).2⟩ :
              F4.reeGamma K a) : ModGL F4.tag K) :=
          coe_apply_congr α (largeReeA1Hom_HSL_eq t).symm _ _
      _ = (((φ ⟨α, hα⟩).1 : MulAut (F4.reeLocalBlock K a ⟨0, by decide⟩))
            (largeReeA1Rep hK (sl2Diag K t)) : ModGL F4.tag K) :=
          (hφ ⟨α, hα⟩ (largeReeA1Rep hK (sl2Diag K t))).symm
      _ = (largeReeA1Rep hK (sl2Diag K (Units.map β.toMonoidHom t)) : ModGL F4.tag K) :=
          congrArg Subtype.val (hd t)
      _ = largeReeA1H a (Units.map β.toMonoidHom t) := largeReeA1Hom_HSL_eq _

end A1

section B2

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem largeReeOppAut_le_U2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    largeReeOppAut K a ≤ pairAutSubgroup
      ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a))
      ((F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩).subgroupOf (F4.reeGamma K a)) :=
  fun α hα =>
    ⟨((large_Ree_fixed_group_Schreier a ha K hK).1 α hα ⟨1, by decide⟩).1,
      ((large_Ree_fixed_group_Schreier a ha K hK).1 α hα ⟨1, by decide⟩).1⟩

@[expose] def largeReeRestrictU2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    largeReeOppAut K a →* MulAut (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) :=
  (MulAut.congr (Subgroup.subgroupOfEquivOfLe U2_le_reeGamma)).toMonoidHom.comp
    ((pairAutRestrict _ _).comp (Subgroup.inclusion (largeReeOppAut_le_U2 ha hK)))

theorem coe_largeReeRestrictU2 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : largeReeOppAut K a) (g : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) :
    ((largeReeRestrictU2 ha hK α g : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) :
      ModGL F4.tag K) = (((α : MulAut (F4.reeGamma K a)) ⟨g, U2_le_reeGamma g.2⟩ :
        F4.reeGamma K a) : ModGL F4.tag K) :=
  rfl

theorem exists_largeReeCoord_apply [Module (ZMod 2) K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K}
    {e : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≃* SuzukiA K σ}
    (he : ∀ (t v : K) (h : largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩),
      e ⟨_, h⟩ = ⟨t, v + t * σ t⟩)
    (α : largeReeOppAut K a) (s v : K) :
    ∃ w, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeCoord a K s v,
        largeReeCoord_mem_reeGamma hK s v⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
      largeReeCoord a K ((MulAut.congr e (largeReeRestrictU2 ha hK α) ⟨s, v + s * σ s⟩).fst) w := by
  obtain ⟨s', w, hsw⟩ := exists_largeReeCoord_eq hK
    (largeReeRestrictU2 ha hK α ⟨_, largeReeCoord_mem hK s v⟩).2
  refine ⟨w, ?_⟩
  have h3 : largeReeRestrictU2 ha hK α ⟨_, largeReeCoord_mem hK s v⟩ =
      ⟨largeReeCoord a K s' w, largeReeCoord_mem hK s' w⟩ := Subtype.ext hsw.symm
  have h2 : MulAut.congr e (largeReeRestrictU2 ha hK α) ⟨s, v + s * σ s⟩ =
      ⟨s', w + s' * σ s'⟩ := by
    rw [← he s v (largeReeCoord_mem hK s v), MulAut.congr_apply, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h3, he]
  rw [h2]
  exact (coe_largeReeRestrictU2 ha hK α _).symm.trans (congrArg Subtype.val h3)

theorem exists_largeReeB2_params (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : largeReeOppAut K a) :
    ∃ (b : Kˣ) (β : K ≃+* K), ∀ s v, ∃ w,
      (((α : MulAut (F4.reeGamma K a)) ⟨largeReeCoord a K s v,
        largeReeCoord_mem_reeGamma hK s v⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeCoord a K (b * β s) w := by
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  let _ : Module (ZMod 2) K := Module.compHom K (ZMod.castHom (dvd_refl 2) K)
  obtain ⟨-, σ, -, hσ, -, -, -, h4⟩ := large_Ree_field_powers a K hK
  have hσ' : ∀ c, σ c = largeReeSigma a c := fun c => by rw [hσ, largeReeSigma]
  obtain ⟨e, he⟩ := exists_mulEquiv_suzukiA hK σ hσ'
  obtain ⟨hquot, hrange, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK σ (h4 ha)
  obtain ⟨b, β, hbβ⟩ : ∃ (b : Kˣ) (β : K ≃+* K), ∀ x,
      (suzukiQuotAction (MulAut.congr e (largeReeRestrictU2 ha hK α)) : K →ₗ[ZMod 2] K) x =
        b * β x := by
    have h : suzukiQuotAction (MulAut.congr e (largeReeRestrictU2 ha hK α)) ∈
        Set.range (suzukiQuotAction (K := K) (φ := σ)) := ⟨_, rfl⟩
    rw [hrange] at h
    exact h
  refine ⟨b, β, fun s v => ?_⟩
  obtain ⟨w, hw⟩ := exists_largeReeCoord_apply ha hK he α s v
  refine ⟨w, hw.trans ?_⟩
  rw [← hquot, hbβ]

theorem suzukiQuotAction_largeRee [Module (ZMod 2) K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {σ : K ≃+* K}
    {e : F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩ ≃* SuzukiA K σ}
    (he : ∀ (t v : K) (h : largeReeCoord a K t v ∈ F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩),
      e ⟨_, h⟩ = ⟨t, v + t * σ t⟩)
    (α : largeReeOppAut K a) {b : Kˣ} {β : K ≃+* K}
    (hb : ∀ s v, ∃ w, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeCoord a K s v,
        largeReeCoord_mem_reeGamma hK s v⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeCoord a K (b * β s) w) (x : K) :
    (suzukiQuotAction (MulAut.congr e (largeReeRestrictU2 ha hK α)) : K →ₗ[ZMod 2] K) x =
      b * β x := by
  obtain ⟨w, hw⟩ := exists_largeReeCoord_apply ha hK he α x (x * σ x)
  obtain ⟨w', hw'⟩ := hb x (x * σ x)
  have h := (largeReeCoord_injective (hw.symm.trans hw')).1
  rw [← h]
  exact suzukiQuotFun_fst _ ⟨x, x * σ x + x * σ x⟩

end B2

section Trivial

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem eq_one_of_forall_fix (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : largeReeOppAut K a)
    (h1 : ∀ c, (((α : MulAut (F4.reeGamma K a)) ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ :
      F4.reeGamma K a) : ModGL F4.tag K) = largeReeA1X a c)
    (h2 : ∀ g, largeReeRestrictU2 ha hK α g = g) : α = 1 := by
  have : Fact F4.prime.Prime := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨φ, hφinj, hφ1, hφ2⟩, -⟩ := large_Ree_fixed_group_Schreier a ha K hK
  have e1 : (φ α).1 = 1 := by
    apply injective_pairAutRestrict_reeLocalBlock (t := F4) (K := K) (a := a) ⟨0, by decide⟩
    rw [map_one]
    refine MulEquiv.ext fun u => Subtype.ext (Subtype.ext ?_)
    change (((φ α).1 : MulAut (F4.reeLocalBlock K a ⟨0, by decide⟩))
        (u : F4.reeLocalBlock K a ⟨0, by decide⟩) : ModGL F4.tag K) =
      ((u : F4.reeLocalBlock K a ⟨0, by decide⟩) : ModGL F4.tag K)
    rw [hφ1]
    obtain ⟨c, hc⟩ := exists_largeReeA1X_eq hK (Subgroup.mem_subgroupOf.1 u.2)
    exact (coe_apply_congr _ hc.symm _ _).trans ((h1 c).trans hc)
  have e2 : (φ α).2 = 1 := by
    apply injective_pairAutRestrict_reeLocalBlock (t := F4) (K := K) (a := a) ⟨1, by decide⟩
    rw [map_one]
    refine MulEquiv.ext fun u => Subtype.ext (Subtype.ext ?_)
    change (((φ α).2 : MulAut (F4.reeLocalBlock K a ⟨1, by decide⟩))
        (u : F4.reeLocalBlock K a ⟨1, by decide⟩) : ModGL F4.tag K) =
      ((u : F4.reeLocalBlock K a ⟨1, by decide⟩) : ModGL F4.tag K)
    rw [hφ2]
    exact congrArg Subtype.val (h2 ⟨_, Subgroup.mem_subgroupOf.1 u.2⟩)
  exact hφinj ((Prod.ext e1 e2).trans (map_one φ).symm)

end Trivial

section Params

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem ringEquiv_eq_of_largeRee_params (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : MulAut (F4.reeGamma K a)} {b : Kˣ} {β₁ β₂ : K ≃+* K}
    (hh : ∀ t, ((α ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) :
      ModGL F4.tag K) = largeReeA1H a (Units.map β₁.toMonoidHom t))
    (hu : ∀ s v, ∃ w, ((α ⟨largeReeCoord a K s v, largeReeCoord_mem_reeGamma hK s v⟩ :
      F4.reeGamma K a) : ModGL F4.tag K) = largeReeCoord a K (b * β₂ s) w) : β₁ = β₂ := by
  obtain ⟨ρ, -, hρ, -, -, -, -, -⟩ := large_Ree_field_powers a K hK
  refine RingEquiv.ext fun c => ?_
  by_cases hc : c = 0
  · rw [hc, map_zero, map_zero]
  let t : Kˣ := Units.mk0 c hc
  have hconj : (⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) *
      ⟨largeReeCoord a K 1 0, largeReeCoord_mem_reeGamma hK 1 0⟩ *
      (⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a)⁻¹ =
        ⟨largeReeCoord a K (((t : K) ^ 2 ^ a)⁻¹ * 1) (((t : K) * (t : K) ^ 2 ^ a)⁻¹ * 0),
          largeReeCoord_mem_reeGamma hK _ _⟩ :=
    Subtype.ext (largeReeA1H_conj_largeReeCoord hK t 1 0)
  have h1 := congrArg (fun g => ((α g : F4.reeGamma K a) : ModGL F4.tag K)) hconj
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  obtain ⟨w, hw⟩ := hu 1 0
  obtain ⟨w', hw'⟩ := hu (((t : K) ^ 2 ^ a)⁻¹ * 1) (((t : K) * (t : K) ^ 2 ^ a)⁻¹ * 0)
  rw [hh, hw, hw'] at h1
  have h2 := (largeReeCoord_injective
    ((largeReeA1H_conj_largeReeCoord hK (Units.map β₁.toMonoidHom t) _ w).symm.trans h1)).1
  simp only [Units.coe_map, map_one, mul_one, map_inv₀, map_pow, t,
    Units.val_mk0] at h2
  have h3 : β₁ c ^ 2 ^ a = β₂ c ^ 2 ^ a := by
    rw [mul_comm] at h2
    exact inv_injective (mul_left_cancel₀ b.ne_zero h2)
  rw [← hρ, ← hρ] at h3
  exact ρ.injective h3

variable (a) in
@[expose] def IsLargeReeParam (hK : Nat.card K = 2 ^ (2 * a + 1)) (α : MulAut (F4.reeGamma K a))
    (p : Kˣ × Kˣ × (K ≃+* K)) : Prop :=
  (∀ c, ((α ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
    largeReeA1X a (p.1 * p.2.2 c)) ∧
  (∀ t, ((α ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
    largeReeA1H a (Units.map p.2.2.toMonoidHom t)) ∧
  ∀ s v, ∃ w, ((α ⟨largeReeCoord a K s v, largeReeCoord_mem_reeGamma hK s v⟩ :
    F4.reeGamma K a) : ModGL F4.tag K) = largeReeCoord a K (p.2.1 * p.2.2 s) w

theorem IsLargeReeParam.unique {hK : Nat.card K = 2 ^ (2 * a + 1)}
    {α : MulAut (F4.reeGamma K a)} {p q : Kˣ × Kˣ × (K ≃+* K)}
    (hp : IsLargeReeParam a hK α p) (hq : IsLargeReeParam a hK α q) : p = q := by
  have e1 : ∀ c, (p.1 : K) * p.2.2 c = q.1 * q.2.2 c := fun c =>
    largeReeA1X_injective ((hp.1 c).symm.trans (hq.1 c))
  have h1 : p.1 = q.1 := Units.ext (by simpa using e1 1)
  have h3 : p.2.2 = q.2.2 := RingEquiv.ext fun c => by
    have := e1 c
    rw [h1] at this
    exact mul_left_cancel₀ q.1.ne_zero this
  obtain ⟨w, hw⟩ := hp.2.2 1 0
  obtain ⟨w', hw'⟩ := hq.2.2 1 0
  have h2 : p.2.1 = q.2.1 := Units.ext (by
    simpa using (largeReeCoord_injective (hw.symm.trans hw')).1)
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem IsLargeReeParam.mul {hK : Nat.card K = 2 ^ (2 * a + 1)}
    {α γ : MulAut (F4.reeGamma K a)} {p q : Kˣ × Kˣ × (K ≃+* K)}
    (hp : IsLargeReeParam a hK α p) (hq : IsLargeReeParam a hK γ q) :
    IsLargeReeParam a hK (α * γ) (p.1 * Units.map p.2.2.toMonoidHom q.1,
      p.2.1 * Units.map p.2.2.toMonoidHom q.2.1, p.2.2 * q.2.2) := by
  refine ⟨fun c => ?_, fun t => ?_, fun s v => ?_⟩
  · have e : γ ⟨largeReeA1X a c, largeReeA1X_mem hK c⟩ =
        ⟨largeReeA1X a (q.1 * q.2.2 c), largeReeA1X_mem hK _⟩ := Subtype.ext (hq.1 c)
    rw [MulAut.mul_apply, e, hp.1]
    congr 1
    simp only [Units.val_mul, Units.coe_map, map_mul, mul_assoc]
    rfl
  · have e : γ ⟨largeReeA1H a t, largeReeA1H_mem hK t⟩ =
        ⟨largeReeA1H a (Units.map q.2.2.toMonoidHom t), largeReeA1H_mem hK _⟩ :=
      Subtype.ext (hq.2.1 t)
    rw [MulAut.mul_apply, e, hp.2.1]
    rfl
  · obtain ⟨w, hw⟩ := hq.2.2 s v
    have e : γ ⟨largeReeCoord a K s v, largeReeCoord_mem_reeGamma hK s v⟩ =
        ⟨largeReeCoord a K (q.2.1 * q.2.2 s) w, largeReeCoord_mem_reeGamma hK _ _⟩ :=
      Subtype.ext hw
    obtain ⟨w', hw'⟩ := hp.2.2 (q.2.1 * q.2.2 s) w
    refine ⟨w', ?_⟩
    rw [MulAut.mul_apply, e, hw']
    congr 1
    simp only [Units.val_mul, Units.coe_map, map_mul, mul_assoc]
    rfl

theorem isLargeReeParam_one (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsLargeReeParam a hK 1 (1, 1, 1) := by
  refine ⟨fun c => ?_, fun t => ?_, fun s v => ⟨v, ?_⟩⟩
  · simp only [MulAut.one_apply, Units.val_one, one_mul]
    rfl
  · rfl
  · simp only [MulAut.one_apply, Units.val_one, one_mul]
    rfl

theorem exists_isLargeReeParam (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : largeReeOppAut K a) : ∃ p, IsLargeReeParam a hK α p := by
  obtain ⟨b₁, β₁, hx, hh⟩ := exists_largeReeA1_params ha hK α.2
  obtain ⟨b₂, β₂, hu⟩ := exists_largeReeB2_params ha hK α
  have hβ : β₁ = β₂ := ringEquiv_eq_of_largeRee_params hK hh hu
  subst hβ
  exact ⟨(b₁, b₂, β₁), hx, hh, hu⟩

end Params

end LargeReeCatalog

open LargeReeCatalog

theorem large_Ree_opposite_Sylow_stabilizer_common_field_parameter (a : ℕ) (ha : 1 ≤ a)
    (K : Type) [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (∀ α ∈ largeReeOppAut K a, ∀ j : Fin F4.fixedOrbitCount,
      ((F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)).map α.toMonoidHom =
        (F4.reeFixedOrbitUnipotent K a j).subgroupOf (F4.reeGamma K a)) ∧
    (∀ c : K, largeReeA1X a c ∈ F4.reeGamma K a) ∧
    (∀ t : Kˣ, largeReeA1H a t ∈ F4.reeGamma K a) ∧
    (∀ s v : K, largeReeCoord a K s v ∈ F4.reeGamma K a) ∧
    (∀ α ∈ largeReeOppAut K a, ∃! p : Kˣ × Kˣ × (K ≃+* K),
      (∀ (c : K) (hc : largeReeA1X a c ∈ F4.reeGamma K a),
        ((α ⟨_, hc⟩ : F4.reeGamma K a) : ModGL F4.tag K) = largeReeA1X a (p.1 * p.2.2 c)) ∧
      (∀ (t : Kˣ) (ht : largeReeA1H a t ∈ F4.reeGamma K a),
        ((α ⟨_, ht⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeA1H a (Units.map p.2.2.toMonoidHom t)) ∧
      ∀ (s v : K) (hsv : largeReeCoord a K s v ∈ F4.reeGamma K a), ∃ w : K,
        ((α ⟨_, hsv⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeCoord a K (p.2.1 * p.2.2 s) w) ∧
    ∃ δ : largeReeOppAut K a →* RingAut K,
      (∀ (α : largeReeOppAut K a) (b : Kˣ) (β : K ≃+* K),
        (∀ (c : K) (hc : largeReeA1X a c ∈ F4.reeGamma K a),
          (((α : MulAut (F4.reeGamma K a)) ⟨_, hc⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
            largeReeA1X a (b * β c)) → δ α = β) ∧
      IsCyclic δ.range ∧
      Nat.card δ.ker ∣ 2 ^ ((2 * a + 1) ^ 2) * (2 ^ (2 * a + 1) - 1) ^ 2 := by
  classical
  choose P hP using exists_isLargeReeParam ha hK
  have hPmul : ∀ α γ : largeReeOppAut K a, P (α * γ) =
      ((P α).1 * Units.map (P α).2.2.toMonoidHom (P γ).1,
        (P α).2.1 * Units.map (P α).2.2.toMonoidHom (P γ).2.1, (P α).2.2 * (P γ).2.2) :=
    fun α γ => (hP (α * γ)).unique ((hP α).mul (hP γ))
  have hP1 : P 1 = (1, 1, 1) := (hP 1).unique (isLargeReeParam_one hK)
  let δ : largeReeOppAut K a →* RingAut K :=
    { toFun := fun α => (P α).2.2
      map_one' := by simp only [hP1]
      map_mul' := fun α γ => by simp only [hPmul] }
  have hδchar : ∀ (α : largeReeOppAut K a) (b : Kˣ) (β : K ≃+* K),
      (∀ (c : K) (hc : largeReeA1X a c ∈ F4.reeGamma K a),
        (((α : MulAut (F4.reeGamma K a)) ⟨_, hc⟩ : F4.reeGamma K a) : ModGL F4.tag K) =
          largeReeA1X a (b * β c)) → δ α = β := by
    intro α b β hb
    have e1 : ∀ c, ((P α).1 : K) * (P α).2.2 c = b * β c := fun c =>
      largeReeA1X_injective (((hP α).1 c).symm.trans (hb c _))
    have h1 : (P α).1 = b := Units.ext (by simpa using e1 1)
    exact RingEquiv.ext fun c => by
      have := e1 c
      rw [h1] at this
      exact mul_left_cancel₀ b.ne_zero this
  have : IsCyclic (RingAut K) := ringAut_isCyclic
  have hkerδ : ∀ α : δ.ker, (P α).2.2 = 1 := fun α => α.2
  let ε : δ.ker →* Kˣ × Kˣ :=
    { toFun := fun α => ((P α).1, (P α).2.1)
      map_one' := by
        change ((P 1).1, (P 1).2.1) = 1
        rw [hP1]
        rfl
      map_mul' := fun α γ => by
        change ((P ((α : largeReeOppAut K a) * γ)).1, (P ((α : largeReeOppAut K a) * γ)).2.1) =
          ((P α).1, (P α).2.1) * ((P γ).1, (P γ).2.1)
        rw [hPmul, hkerδ α]
        rfl }
  have hε : ∀ α : ε.ker, (P α).1 = 1 ∧ (P α).2.1 = 1 := fun α => Prod.ext_iff.1 α.2
  have : CharP K 2 := inferInstanceAs (CharP K F4.prime)
  let _ : Module (ZMod 2) K := Module.compHom K (ZMod.castHom (dvd_refl 2) K)
  obtain ⟨-, σ, -, hσ, -, -, -, h4⟩ := large_Ree_field_powers a K hK
  have hσ' : ∀ c, σ c = largeReeSigma a c := fun c => by rw [hσ, largeReeSigma]
  obtain ⟨e, he⟩ := exists_mulEquiv_suzukiA hK σ hσ'
  obtain ⟨-, -, -, -, -, hcard, -⟩ :=
    suzuki_two_A_automorphism_solvable (K := K) (by omega : 1 ≤ 2 * a + 1) hK σ (h4 ha)
  let f : ε.ker →* MulAut (SuzukiA K σ) := (MulAut.congr e).toMonoidHom.comp
    ((largeReeRestrictU2 ha hK).comp (δ.ker.subtype.comp ε.ker.subtype))
  have hf : ∀ α, f α ∈ (suzukiQuotAction (K := K) (φ := σ)).ker := fun α => by
    rw [MonoidHom.mem_ker]
    refine Units.ext (LinearMap.ext fun x => ?_)
    have key := suzukiQuotAction_largeRee ha hK he ((α : δ.ker) : largeReeOppAut K a)
      (hP ((α : δ.ker) : largeReeOppAut K a)).2.2 x
    rw [(hε α).2, hkerδ α, Units.val_one, one_mul] at key
    exact key
  let θ : ε.ker →* (suzukiQuotAction (K := K) (φ := σ)).ker := f.codRestrict _ hf
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro α hα
    have hf1 : f α = 1 := congrArg Subtype.val hα
    have hr : largeReeRestrictU2 ha hK ((α : δ.ker) : largeReeOppAut K a) = 1 :=
      (MulAut.congr e).injective (hf1.trans (map_one _).symm)
    have h1 := eq_one_of_forall_fix ha hK ((α : δ.ker) : largeReeOppAut K a)
      (fun c => by rw [(hP _).1 c, (hε α).1, hkerδ α, Units.val_one, one_mul]; rfl)
      (fun g => by rw [hr]; rfl)
    exact Subtype.ext (Subtype.ext h1)
  have hcardker : Nat.card ε.ker ∣ 2 ^ ((2 * a + 1) ^ 2) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_injective θ hθ
  have hcardrange : Nat.card ε.range ∣ (2 ^ (2 * a + 1) - 1) ^ 2 := by
    have h := Subgroup.card_subgroup_dvd_card ε.range
    rwa [Nat.card_prod, Nat.card_units, hK, ← sq] at h
  have hsplit : Nat.card δ.ker = Nat.card ε.range * Nat.card ε.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ε.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ε).toEquiv]
  refine ⟨fun α hα j => ((large_Ree_fixed_group_Schreier a ha K hK).1 α hα j).1,
    largeReeA1X_mem hK, largeReeA1H_mem hK, largeReeCoord_mem_reeGamma hK,
    fun α hα => ⟨P ⟨α, hα⟩, ⟨fun c _ => (hP ⟨α, hα⟩).1 c, fun t _ => (hP ⟨α, hα⟩).2.1 t,
      fun s v _ => (hP ⟨α, hα⟩).2.2 s v⟩, fun q hq => ((hP ⟨α, hα⟩).unique
        ⟨fun c => hq.1 c _, fun t => hq.2.1 t _, fun s v => hq.2.2 s v _⟩).symm⟩,
    δ, hδchar, inferInstance, ?_⟩
  rw [hsplit, mul_comm]
  exact Nat.mul_dvd_mul hcardker hcardrange

end CFSG.ComponentClassification.UnbalancedCatalog
