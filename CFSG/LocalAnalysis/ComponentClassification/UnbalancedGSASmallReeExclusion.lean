module

public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.Walter.Ree.Model

namespace SmallReeExclusion

variable {H : Type*} [Group H]

theorem eq_one_or_eq_of_mem_zpowers {x y : H} (hx : x * x = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hx, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hx, one_zpow, one_mul, zpow_one]

theorem triple_isElementaryAbelian_card [Finite H] {t x y : H} (ht : orderOf t = 2)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (htx : t * x = x * t) (hty : t * y = y * t)
    (hxy : x * y = y * x) (hyx : y ∉ Subgroup.zpowers x)
    (hinf : Subgroup.zpowers t ⊓ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) = ⊥) :
    IsElementaryAbelian 2
        (Subgroup.zpowers t ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup H) ∧
      Nat.card (Subgroup.zpowers t ⊔ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) : Subgroup H) =
        2 ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hVcard⟩ := RankOneCenter.pair_isElementaryAbelian_card hx hy hxy hyx
  have : IsElementaryAbelian 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup H) := hV
  have : IsElementaryAbelian 2 (Subgroup.zpowers t) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have hcent : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer (Subgroup.zpowers t : Set H) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_) <;>
      refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_ <;>
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    · exact (Commute.zpow_left htx k).eq
    · exact (Commute.zpow_left hty k).eq
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hcent, ?_⟩
  have hc : ∀ g ∈ Subgroup.zpowers t, ∀ h ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y :
      Subgroup H), g * h = h * g := fun g hg h hh =>
    Subgroup.mem_centralizer_iff.mp (hcent hh) g hg
  have h := RankOneCenter.card_sup_mul_card_inf_of_commute _ _ hc
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, ht, hVcard] at h
  rw [h]
  norm_num

end SmallReeExclusion

open SmallReeExclusion ReeTag

theorem dihedral_sylow_small_ree_model_exclusion {T : Type} [Group T] {p f : ℕ}
    (hT : ReeTitsModel T .twistedG2 p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨hfin, -, hp, -, hiso⟩ := small_Ree_model_Schreier T p f hT
  subst hp
  obtain ⟨-, a, hfa, hmodel⟩ := hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hiso a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 3 ^ (2 * a + 1) := hfa ▸ hK
  have : Finite T := hfin
  have : Finite (ModGL G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
  obtain ⟨ψ, hψC, -, -, -, hψ1, -, ⟨hsup, hdisj, hcent⟩, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK' w₀ hw₀
  set t := smallReeH a K (-1) with htdef
  have : CharP K 3 := ‹CharP K G2.prime›
  have hkchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    decide
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hkchar
  obtain ⟨u, v, huv⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hkchar (-1)
  obtain ⟨x, y, hxm, hym, hx2, hy2, hxy⟩ :=
    LocalAnalysis.ComponentInitial.sl2_exists_anticommuting_pair huv
  have hent : ∀ (g g' : SL2 K) (i j : Fin 2), g = g' →
      (g : Matrix (Fin 2) (Fin 2) K) i j = (g' : Matrix (Fin 2) (Fin 2) K) i j :=
    fun g g' i j h => by rw [h]
  have hx1 : ψ x ≠ 1 := by
    rw [Ne, hψ1]
    rintro (h | h)
    · have := hent _ _ 0 0 h
      simp [hxm] at this
    · have := hent _ _ 0 0 h
      simp [hxm] at this
  have hy1 : ψ y ≠ 1 := by
    rw [Ne, hψ1]
    rintro (h | h)
    · have h0 := hent _ _ 0 0 h
      have h1 := hent _ _ 1 1 h
      simp [hym] at h0 h1
      apply h2
      linear_combination -h0 - h1
    · have h0 := hent _ _ 0 0 h
      have h1 := hent _ _ 1 1 h
      simp [hym] at h0 h1
      apply h2
      linear_combination h0 - h1
  have hxy1 : ψ x ≠ ψ y := by
    intro h
    have h' : ψ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [hψ1, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, one_mul] at h'
    rcases h' with h' | h'
    · have h0 := hent _ _ 0 1 h'
      have h1 := hent _ _ 1 0 h'
      simp [hxm, hym] at h0 h1
      apply h2
      linear_combination h0 - h1
    · have h0 := hent _ _ 0 1 h'
      have h1 := hent _ _ 1 0 h'
      simp [hxm, hym] at h0 h1
      apply h2
      linear_combination h0 + h1
  have hψsq : ∀ g : SL2 K, g ^ 2 = -1 → ψ g * ψ g = 1 := fun g hg => by
    rw [← map_mul, ← sq, hg]
    exact (hψ1 _).2 (Or.inr rfl)
  have hψxy : ψ x * ψ y = ψ y * ψ x := by
    rw [← map_mul, hxy, map_mul, (hψ1 (-1)).2 (Or.inr rfl), one_mul, map_mul]
  have htC : t ∈ smallReeInvCentralizer a K := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have htcomm : ∀ g : SL2 K, t * ψ g = ψ g * t := fun g =>
    (Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_zpowers t)) (ψ g) ⟨g, rfl⟩).symm
  set Γ := G2.reeGamma K a
  let tΓ : Γ := ⟨t, (Subgroup.mem_inf.mp htC).1⟩
  let xΓ : Γ := ⟨ψ x, (Subgroup.mem_inf.mp (hψC x)).1⟩
  let yΓ : Γ := ⟨ψ y, (Subgroup.mem_inf.mp (hψC y)).1⟩
  have hord : ∀ g : Γ, g * g = 1 → g ≠ 1 → orderOf g = 2 := fun g hg hg1 =>
    orderOf_eq_prime (by rw [sq, hg]) hg1
  have ht1 : t ≠ 1 := by
    rw [htdef, ← smallReeH_one (a := a) (K := K), Ne, smallReeH_injective.eq_iff, Units.ext_iff,
      Units.val_neg, Units.val_one]
    intro h
    apply h2
    linear_combination -h
  have hto : orderOf tΓ = 2 := hord _ (Subtype.ext smallReeH_neg_one_mul_self)
    (fun h => ht1 (congrArg Subtype.val h))
  have hxo : orderOf xΓ = 2 := hord _ (Subtype.ext (hψsq x hx2))
    (fun h => hx1 (congrArg Subtype.val h))
  have hyo : orderOf yΓ = 2 := hord _ (Subtype.ext (hψsq y hy2))
    (fun h => hy1 (congrArg Subtype.val h))
  have hyx : yΓ ∉ Subgroup.zpowers xΓ := by
    intro hmem
    rcases eq_one_or_eq_of_mem_zpowers (Subtype.ext (hψsq x hx2)) hmem with h | h
    · exact hy1 (congrArg Subtype.val h)
    · exact hxy1 (congrArg Subtype.val h).symm
  have hinf : Subgroup.zpowers tΓ ⊓ (Subgroup.zpowers xΓ ⊔ Subgroup.zpowers yΓ) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have h1 : (g : ModGL G2.tag K) ∈ Subgroup.zpowers t := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg.1
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← hk, Subgroup.coe_zpow]⟩
    have hle : Subgroup.zpowers xΓ ⊔ Subgroup.zpowers yΓ ≤ ψ.range.comap Γ.subtype :=
      sup_le (Subgroup.zpowers_le.mpr ⟨x, rfl⟩) (Subgroup.zpowers_le.mpr ⟨y, rfl⟩)
    have h2 : (g : ModGL G2.tag K) ∈ ψ.range := hle hg.2
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.disjoint_def.mp hdisj h1 h2))
  obtain ⟨hEl, hcard⟩ := triple_isElementaryAbelian_card hto hxo hyo
    (Subtype.ext (htcomm x)) (Subtype.ext (htcomm y)) (Subtype.ext hψxy) hyx hinf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hEl
  have hEl' := IsElementaryAbelian.map (p := 2)
    (A := Subgroup.zpowers tΓ ⊔ (Subgroup.zpowers xΓ ⊔ Subgroup.zpowers yΓ)) E.symm.toMonoidHom
  have hcard' : Nat.card ((Subgroup.zpowers tΓ ⊔ (Subgroup.zpowers xΓ ⊔
      Subgroup.zpowers yΓ)).map E.symm.toMonoidHom) = 2 ^ 3 := by
    rw [Subgroup.card_map_of_injective E.symm.injective, hcard]
  have hle := RankOneCenter.le_pRank_of_subgroup hEl' hcard'
  have hrank :=
    (SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩).1
  omega

end CFSG.ComponentClassification.UnbalancedGS
