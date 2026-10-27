module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightCOne
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixAlternatingEightLeviFix

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits Degree64
open LinearMap (BilinForm)
open scoped Pointwise

abbrev jSym (c x x' : ZMod 2) : binarySymMatrices 3 :=
  ⟨jMat c x x', mem_binarySymMatrices.2 (jMat_transpose c x x')⟩

theorem jSym_add (c x x' c₀ y y' : ZMod 2) :
    jSym c x x' + jSym c₀ y y' = jSym (c + c₀) (x + y) (x' + y') := by
  apply Subtype.ext
  change jMat c x x' + jMat c₀ y y' = jMat (c + c₀) (x + y) (x' + y')
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jMat]

theorem jSym_injective {c x x' c₀ y y' : ZMod 2} (h : jSym c x x' = jSym c₀ y y') :
    c = c₀ ∧ x = y ∧ x' = y' :=
  jMat_injective c x x' c₀ y y' (congrArg Subtype.val h)

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
  (halt : AltOrbit z φ e)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))
local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒟" => CFSG.Assembly.pCoreOf 2 𝒩
local notation "θ₂" => RadicalLabels.radLabel φ he hzC hz hinf
local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒟₁" => ptD₁ hzC hsup hinf hz hb hnd hV φ he halt
local notation "𝐛₁" => ptB₁ hzC hz hb φ he

omit [FiniteDimensional (ZMod 2) V] in
include he in
theorem pointVec_mem_pairOrth (x x' : ZMod 2) : pointVec e x x' 0 0 ∈ 𝔼 := by
  rw [← pointSpan_eq_pairOrth he]
  exact pointVec_mem x x' 0 0

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem tauHom_jSym (c x x' : ZMod 2) :
    tauHom φ he (Multiplicative.ofAdd (jSym c x x')) =
      ((φ.symm (pointElt hb (mem_pairOrth_left (pointVec_mem_pairOrth he x x')) c) : L) : G) := by
  refine (RadicalLabels.eq_tauHom_of_toMatrix φ he (φ.symm _).2 _ ?_).symm
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hw : pointVec e x x' 0 0 ∈ pointSpan e := pointVec_mem x x' 0 0
  change LinearMap.toMatrix e e (pointMap b (e (Sum.inl 0)) (pointVec e x x' 0 0) c) = _
  rw [toMatrix_pointMap he hw]
  obtain ⟨h1, h2, h3, h4⟩ := pointVec_coords (e := e) x x' 0 0
  rw [h1, h2, h3, h4, t0Mat_zero, Matrix.transpose_one]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem tauHom_jSym_mem_ptA (c x x' : ZMod 2) :
    tauHom φ he (Multiplicative.ofAdd (jSym c x x')) ∈ 𝒜₁ := by
  rw [tauHom_jSym hb φ he]
  refine mem_pullSub.2 ⟨(φ.symm _).2, ?_⟩
  rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
  exact pointElt_mem_pointRadical hb (pointVec_mem_pairOrth he x x') c

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem tauHom_mem_radA (B : binarySymMatrices 3) :
    tauHom φ he (Multiplicative.ofAdd B) ∈ 𝒜 :=
  (mem_pullSub_iff φ he).2 ⟨_, rfl⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptB₁_eq_tauHom : 𝐛₁ = tauHom φ he (Multiplicative.ofAdd (jSym 1 0 0)) := by
  rw [ptB₁, ptHom_pt, ← tauHom_symE₁₁ he hb φ]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem mem_J_iff {g : G} :
    g ∈ 𝒜₁ ⊓ 𝒜 ↔ ∃ c x x' : ZMod 2, tauHom φ he (Multiplicative.ofAdd (jSym c x x')) = g := by
  constructor
  · rintro ⟨hgA, hgW⟩
    obtain ⟨hgL, hgP⟩ := mem_pullSub.1 hgA
    obtain ⟨w, hw, c, hwc⟩ := (mem_pointRadical hb).1 hgP
    obtain ⟨hgL', hgW'⟩ := mem_pullSub.1 hgW
    have hfix : ∀ j : Fin 3, b (e (Sum.inl j)) w = 0 := by
      intro j
      have h := hgW' (e (Sum.inl j)) (Submodule.subset_span ⟨j, rfl⟩)
      rw [hwc] at h
      change pointMap b (e (Sum.inl 0)) w c (e (Sum.inl j)) = e (Sum.inl j) at h
      rw [pointMap_apply, bilin_ee he 0 j, zero_smul, add_zero, add_eq_left] at h
      have hu : e (Sum.inl 0) ≠ 0 := e.ne_zero _
      rcases BinarySymplecticTransvection.zmod_two_cases (b (e (Sum.inl j)) w) with h0 | h1
      · exact h0
      · rw [h1, one_smul] at h
        exact absurd h hu
    have hy₂ : e.repr w (Sum.inr 1) = 0 := by rw [← bilin_inl he]; exact hfix 1
    have hy₃ : e.repr w (Sum.inr 2) = 0 := by rw [← bilin_inl he]; exact hfix 2
    have hwv : pointVec e (e.repr w (Sum.inl 1)) (e.repr w (Sum.inl 2)) 0 0 = w := by
      apply e.repr.injective
      ext i
      have hw' : w ∈ pointSpan e := by rwa [pointSpan_eq_pairOrth he]
      obtain ⟨h0, h0'⟩ := mem_pointSpan.1 hw'
      rw [repr_pointVec]
      rcases i with i | i <;> fin_cases i <;> simp [h0, h0', hy₂, hy₃]
    refine ⟨c, e.repr w (Sum.inl 1), e.repr w (Sum.inl 2), ?_⟩
    rw [tauHom_jSym hb φ he]
    have h1 : (⟨g, hgL⟩ : L) = φ.symm (pointElt hb (mem_pairOrth_left hw) c) := by
      rw [← hwc, MulEquiv.symm_apply_apply]
    rw [show g = ((⟨g, hgL⟩ : L) : G) from rfl, h1]
    congr 2
    exact pointElt_ext hb _ _ (by rw [hwv])
  · rintro ⟨c, x, x', rfl⟩
    exact ⟨tauHom_jSym_mem_ptA hb φ he c x x', tauHom_mem_radA φ he _⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem tauHom_jSym_injective : Function.Injective fun p : ZMod 2 × ZMod 2 × ZMod 2 =>
    tauHom φ he (Multiplicative.ofAdd (jSym p.1 p.2.1 p.2.2)) := by
  rintro ⟨c, x, x'⟩ ⟨c₀, y, y'⟩ h
  obtain ⟨rfl, rfl, rfl⟩ :=
    jSym_injective (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
  rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hb he in
theorem card_J : Nat.card (𝒜₁ ⊓ 𝒜 : Subgroup G) = 8 := by
  have hset : ((𝒜₁ ⊓ 𝒜 : Subgroup G) : Set G) = Set.range fun p : ZMod 2 × ZMod 2 × ZMod 2 =>
      tauHom φ he (Multiplicative.ofAdd (jSym p.1 p.2.1 p.2.2)) := by
    ext g
    rw [SetLike.mem_coe, mem_J_iff hb φ he]
    exact ⟨fun ⟨c, x, x', h⟩ => ⟨(c, x, x'), h⟩, fun ⟨p, h⟩ => ⟨p.1, p.2.1, p.2.2, h⟩⟩
  rw [show Nat.card (𝒜₁ ⊓ 𝒜 : Subgroup G) = Nat.card ((𝒜₁ ⊓ 𝒜 : Subgroup G) : Set G) from rfl,
    hset, Nat.card_range_of_injective (tauHom_jSym_injective φ he), Nat.card_prod, Nat.card_prod,
    Nat.card_zmod]

theorem jSym_mem_altSym (x x' : ZMod 2) : jSym 0 x x' ∈ BinarySymThreeOrbit.altSym := by
  rw [BinarySymThreeOrbit.mem_altSym_iff]
  funext i
  fin_cases i <;> rfl

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem mem_J₀_iff {g : G} :
    g ∈ 𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym ↔
      ∃ x x' : ZMod 2, tauHom φ he (Multiplicative.ofAdd (jSym 0 x x')) = g := by
  constructor
  · rintro ⟨hgA, hgI⟩
    obtain ⟨B, hB, rfl⟩ := (BinarySymThreeOrbit.mem_layerSub θ₂).1 hgI
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one] at hgA ⊢
    obtain ⟨c, x, x', h⟩ := (mem_J_iff hb φ he).1 ⟨hgA, tauHom_mem_radA φ he B⟩
    have h1 := Multiplicative.ofAdd.injective (tauHom_injective φ he h)
    have hc : c = 0 := by
      have h2 := congrFun (BinarySymThreeOrbit.mem_altSym_iff.1 hB) 0
      rw [← h1] at h2
      exact h2
    subst hc
    exact ⟨x, x', h⟩
  · rintro ⟨x, x', rfl⟩
    refine ⟨tauHom_jSym_mem_ptA hb φ he 0 x x', (BinarySymThreeOrbit.mem_layerSub θ₂).2
      ⟨_, jSym_mem_altSym x x', ?_⟩⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem card_J₀ :
    Nat.card (𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym : Subgroup G) =
      4 := by
  have hinj : Function.Injective fun p : ZMod 2 × ZMod 2 =>
      tauHom φ he (Multiplicative.ofAdd (jSym 0 p.1 p.2)) := by
    rintro ⟨x, x'⟩ ⟨y, y'⟩ h
    obtain ⟨-, rfl, rfl⟩ :=
      jSym_injective (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
    rfl
  have hset : ((𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym :
      Subgroup G) : Set G) = Set.range fun p : ZMod 2 × ZMod 2 =>
        tauHom φ he (Multiplicative.ofAdd (jSym 0 p.1 p.2)) := by
    ext g
    rw [SetLike.mem_coe, mem_J₀_iff hzC hinf hz hb φ he]
    exact ⟨fun ⟨x, x', h⟩ => ⟨(x, x'), h⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h⟩⟩
  rw [show Nat.card (𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym :
      Subgroup G) = Nat.card ((𝒜₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym :
        Subgroup G) : Set G) from rfl, hset, Nat.card_range_of_injective hinj, Nat.card_prod,
    Nat.card_zmod]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
include hinf he in
theorem orderOf_ptB₁ : orderOf 𝐛₁ = 2 := by
  have hsq : 𝐛₁ ^ 2 = 1 := by
    rw [ptB₁_eq, sq, ← pt₁_add, add_self_eq_zero_zmod_two, pt₁_zero]
  have hne : 𝐛₁ ≠ 1 := by
    rw [ptB₁_eq, ← pt₁_zero hzC hz hb φ he]
    intro h
    have h1 := congrArg (fun x : (𝔼 × ZMod 2) × ZMod 2 => x.1.2)
      (pt₁_injective hzC hinf hz hb φ he h)
    exact one_ne_zero h1
  exact orderOf_eq_prime hsq hne

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem ptI_inf_radI :
    zpowers 𝐛₁ ⊓ BinarySymThreeOrbit.layerSub θ₂ BinarySymThreeOrbit.altSym = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  rcases eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ hzC hinf hz hb φ he) hx1 with h | h
  · exact h ▸ one_mem _
  · exfalso
    obtain ⟨B, hB, hBx⟩ := (BinarySymThreeOrbit.mem_layerSub θ₂).1 hx2
    rw [h, ptB₁_eq_tauHom hzC hz hb φ he, coe_radLabel_symm_apply, RadicalLabels.zPow_zero,
      mul_one] at hBx
    have h1 := Multiplicative.ofAdd.injective (tauHom_injective φ he hBx)
    have h2 := congrFun (BinarySymThreeOrbit.mem_altSym_iff.1 hB) 0
    rw [← h1] at h2
    exact one_ne_zero h2

omit [FiniteDimensional (ZMod 2) V] in
include hzC hnd he in
theorem radA_le_stab :
    𝒜 ≤ 𝒩₁ ⊓ centralizer ({z} : Set G) := by
  obtain ⟨hAL, -, -, -, hAN, -⟩ := ptA_facts he hb hnd φ
  intro a ha
  have haL : a ∈ L := pullSub_le φ _ ha
  have hza : a * z = z * a := RadicalLabels.mul_comm_z hzC haL
  refine mem_inf.2 ⟨mem_normalizer_of_map_le ?_, mem_centralizer_singleton_iff.2 hza⟩
  have hav : a ∈ pullSub φ (vecStabilizer b (e (Sum.inl 0))) := by
    obtain ⟨haL', haW⟩ := mem_pullSub.1 ha
    exact mem_pullSub.2 ⟨haL', mem_vecStabilizer.2
      (haW _ (Submodule.subset_span ⟨0, rfl⟩))⟩
  rw [← hAN] at hav
  have haN := (mem_inf.1 hav).1
  rw [Subgroup.map_le_iff_le_comap]
  intro x hx
  rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  obtain ⟨y, hy, t, ht, rfl⟩ := (mem_sup_of_le_centralizer
    (FusionOrbits.zpowers_le_centralizer_pullSub φ hzC _)).1 hx
  have htz : a * t * a⁻¹ = t := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ht
    rw [mul_inv_eq_iff_eq_mul, (Commute.zpow_right hza k).eq]
  rw [show a * (y * t) * a⁻¹ = (a * y * a⁻¹) * (a * t * a⁻¹) by group, htz]
  exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 haN y).1 hy)) (mem_sup_right ht)

theorem radA_inf_ptD₁ : 𝒜 ⊓ 𝒟₁ = 𝒜₁ ⊓ 𝒜 := by
  obtain ⟨-, -, -, hBL⟩ := ptSub_facts he hb hnd φ hzC hinf hz
  apply le_antisymm
  · rintro a ⟨ha, haD⟩
    have hac := (mem_inf.1 (radA_le_stab hzC hb hnd φ he ha)).2
    have haB : a ∈ ptSub φ z hb e := by
      rw [← ptD₁_inf_centralizer hzC hsup hinf hz hb hnd hV φ he halt]
      exact ⟨haD, hac⟩
    refine ⟨?_, ha⟩
    rw [← hBL]
    exact ⟨haB, pullSub_le φ _ ha⟩
  · rintro a ⟨haA₁, ha⟩
    exact ⟨ha, ptSub_le_ptD₁ hzC hsup hinf hz hb hnd hV φ he halt (mem_sup_left haA₁)⟩

include hzC hsup hinf hz hnd hV he halt in
theorem mem_ptN_iff_of_mem_D₂ {d : G} (hd : d ∈ 𝒟) :
    d ∈ 𝒩₁ ↔ z⁻¹ * d⁻¹ * z * d ∈ 𝒜₁ := by
  classical
  obtain ⟨ν, hν1, -, hν3, -, -, -, -⟩ :=
    translation_group_structure hzC hsup hinf hz hb hnd hV φ he halt
  set ν' : G → binarySymMatrices 3 := fun g => if h : g ∈ 𝒟 then
    ((Multiplicative.toAdd (ν ⟨g, h⟩) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3)
    else 0 with hν'def
  have hν' : ∀ (g : G) (h : g ∈ 𝒟), ν' g =
      ((Multiplicative.toAdd (ν ⟨g, h⟩) : ↥BinarySymThreeOrbit.altSym) : binarySymMatrices 3) :=
    fun g h => by simp only [hν'def, h, ↓reduceDIte]
  have hcomm : ∀ g (h : g ∈ 𝒟), z⁻¹ * g⁻¹ * z * g = tauHom φ he (Multiplicative.ofAdd (ν' g)) := by
    intro g h
    have h1 := hν1 ⟨g, h⟩
    rw [coe_radLabel_symm_apply, RadicalLabels.zPow_zero, mul_one, ← hν' g h] at h1
    exact h1
  constructor
  · intro hdN
    obtain ⟨-, -, -, hBL⟩ := ptSub_facts he hb hnd φ hzC hinf hz
    have h1 : d⁻¹ * z * d ∈ ptSub φ z hb e := by
      have h2 := (mem_normalizer_iff.1 (inv_mem hdN) z).1 (mem_sup_right (mem_zpowers z))
      rwa [inv_inv] at h2
    have h3 : z⁻¹ * d⁻¹ * z * d ∈ ptSub φ z hb e := by
      have h4 := mul_mem (inv_mem (mem_sup_right (mem_zpowers z) : z ∈ ptSub φ z hb e)) h1
      simpa only [mul_assoc] using h4
    rw [← hBL]
    refine ⟨h3, ?_⟩
    rw [hcomm d hd]
    exact tauHom_mem φ he _
  · intro hdA
    have hDN : 𝒟 ≤ 𝒩 := map_subtype_le _
    have hDn : ∀ n ∈ 𝒩, ∀ d ∈ 𝒟, n * d * n⁻¹ ∈ 𝒟 := by
      intro n hn d hd
      obtain ⟨d', hd', rfl⟩ := hd
      exact ⟨⟨n, hn⟩ * d' * ⟨n, hn⟩⁻¹,
        (CFSG.Assembly.Dichotomy.CentralizerContainment.pCore_normal_assembly 2 𝒩).conj_mem d'
          hd' ⟨n, hn⟩, rfl⟩
    have hνz : ∀ d ∈ 𝒟, d⁻¹ * z * d =
        RadicalLabels.radHom φ he hzC hz (Multiplicative.ofAdd (ν' d, 1)) := by
      intro d hd
      have h := hcomm d hd
      rw [RadicalLabels.radHom_apply, RadicalLabels.zPow_one,
        RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _), ← h]
      group
    have hνeq : ∀ d ∈ 𝒟, ∀ d' ∈ 𝒟, ν' d = ν' d' ↔ d⁻¹ * d' ∈ ℛ := by
      intro d hd d' hd'
      rw [hν' d hd, hν' d' hd']
      have hmem : d⁻¹ * d' ∈ ℛ ↔ (⟨d, hd⟩ : 𝒟)⁻¹ * ⟨d', hd'⟩ ∈ ν.ker := by
        rw [hν3, mem_subgroupOf]
        rfl
      rw [hmem, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
      constructor
      · intro h
        exact Multiplicative.toAdd.injective (Subtype.ext h)
      · intro h
        rw [h]
    have hdA' : tauHom φ he (Multiplicative.ofAdd (ν' d)) ∈ 𝒜₁ := by
      rw [← hcomm d hd]
      exact hdA
    exact mem_normalizer_ptSub_of_mem he hb hnd φ hzC hinf hz hDN hDn hνz hνeq hd hdA'

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.AlternatingEight
