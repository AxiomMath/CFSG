module

public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KS219.Tools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaCentralQuot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2
open scoped commutatorElement

instance isSimpleGroup_alt6 : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)

theorem exists_mul_ne_alt6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg (fun σ : alternatingGroup (Fin 6) => (σ : Equiv.Perm (Fin 6)) 0) h
  revert this
  decide

theorem commutator_alt6 :
    ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ = alternatingGroup (Fin 6) := by
  have htop : _root_.commutator (alternatingGroup (Fin 6)) = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup (alternatingGroup (Fin 6))) ⊤).eq_bot_or_eq_top with
      h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_mul_ne_alt6
      have hc : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))), ⊤⁆ :=
        commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  have := congrArg (Subgroup.map (alternatingGroup (Fin 6)).subtype) htop
  rwa [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at this

theorem x_mem_C : xJ ∈ centralizer ({zJ} : Set GJ) := by
  rw [mem_centralizer_singleton_iff, z_eq]
  exact z_comm_x.eq.symm

theorem y_mem_C : yJ ∈ centralizer ({zJ} : Set GJ) := by
  rw [mem_centralizer_singleton_iff, z_eq]
  exact z_comm_y.eq.symm

theorem center_C_eq : center (centralizer ({zJ} : Set GJ)) = act6.ker := by
  apply le_antisymm
  · intro c hc
    rw [MonoidHom.mem_ker]
    have hmem : act6 c ∈ alternatingGroup (Fin 6) := by
      rw [← range_act6]
      exact ⟨c, rfl⟩
    have hcen :
        (⟨act6 c, hmem⟩ : alternatingGroup (Fin 6)) ∈ center (alternatingGroup (Fin 6)) := by
      rw [mem_center_iff]
      intro σ
      obtain ⟨d, hd⟩ : (σ : Equiv.Perm (Fin 6)) ∈ act6.range := by
        rw [range_act6]
        exact σ.2
      apply Subtype.ext
      change (σ : Equiv.Perm (Fin 6)) * act6 c = act6 c * σ
      rw [← hd, ← map_mul, ← map_mul, mem_center_iff.mp hc d]
    rw [center_eq_bot_of_isSimpleGroup exists_mul_ne_alt6, mem_bot] at hcen
    exact congrArg Subtype.val hcen
  · rw [ker_act6]
    intro c hc
    rw [mem_subgroupOf] at hc
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hc
    rw [mem_center_iff]
    intro d
    apply Subtype.ext
    have hd : Commute (d : GJ) zJ := mem_centralizer_singleton_iff.mp d.2
    change (d : GJ) * c = c * d
    rw [← hn]
    exact (hd.zpow_right n).eq

theorem card_center_C : Nat.card (center (centralizer ({zJ} : Set GJ))) = 3 := by
  rw [center_C_eq, card_ker_act6]

theorem commutator_C : _root_.commutator (centralizer ({zJ} : Set GJ)) = ⊤ := by
  set C := centralizer ({zJ} : Set GJ) with hC
  have hz : (⟨zJ, z_mem_C⟩ : C) ∈ _root_.commutator C := by
    have : (⟨zJ, z_mem_C⟩ : C) = ⁅(⟨xJ, x_mem_C⟩ : C), ⟨yJ, y_mem_C⟩⁆ := Subtype.ext z_eq
    rw [this]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  have hker : act6.ker ≤ _root_.commutator C := by
    rw [ker_act6]
    intro c hc
    rw [mem_subgroupOf] at hc
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hc
    have : c = (⟨zJ, z_mem_C⟩ : C) ^ n := by
      apply Subtype.ext
      rw [← hn]
      rfl
    rw [this]
    exact zpow_mem hz n
  have hmap : (_root_.commutator C).map act6 = alternatingGroup (Fin 6) := by
    rw [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_act6, commutator_alt6]
  rw [eq_top_iff]
  intro c _
  have hc : act6 c ∈ (_root_.commutator C).map act6 := by
    rw [hmap, ← range_act6]
    exact ⟨c, rfl⟩
  obtain ⟨d, hd, hdc⟩ := mem_map.mp hc
  have hk : d⁻¹ * c ∈ act6.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdc, inv_mul_cancel]
  have := mul_mem hd (hker hk)
  rwa [mul_inv_cancel_left] at this

noncomputable def quotCenterEquiv :
    centralizer ({zJ} : Set GJ) ⧸ center (centralizer ({zJ} : Set GJ)) ≃*
      alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq center_C_eq).trans
    ((QuotientGroup.quotientKerEquivRange act6).trans (MulEquiv.subgroupCongr range_act6))

theorem isQuasisimple_C : CFSG.IsQuasisimple (centralizer ({zJ} : Set GJ)) := by
  refine ⟨⟨commutator_C⟩, quotCenterEquiv.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_mul_ne_alt6
  refine ⟨quotCenterEquiv.symm a, quotCenterEquiv.symm b, fun h => hab ?_⟩
  have := congrArg quotCenterEquiv h
  simpa using this

theorem isTripleCover_C :
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover (centralizer ({zJ} : Set GJ))
      (alternatingGroup (Fin 6)) :=
  ⟨card_center_C, ⟨quotCenterEquiv⟩⟩

theorem factorization_card_GJ : (Nat.card GJ).factorization 3 = 3 := by
  rw [card_GJ]
  exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
    (show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num) (by norm_num)

theorem centralizer_zpow_eq {n : ℤ} (hn : zJ ^ n ≠ 1) :
    centralizer ({zJ ^ n} : Set GJ) = centralizer ({zJ} : Set GJ) := by
  have h3 : zJ ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact z_cube
  have hmod : zJ ^ n = zJ ^ (n % 3) := zpow_eq_zpow_emod n h3
  have hr : n % 3 = 1 ∨ n % 3 = 2 := by
    have h0 := Int.emod_nonneg n (by norm_num : (3 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 3)
    have : n % 3 ≠ 0 := fun h => hn (by rw [hmod, h, zpow_zero])
    omega
  apply le_antisymm
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    have hc' : Commute c (zJ ^ n) := hc
    rcases hr with h | h
    · rw [hmod, h, zpow_one] at hc'
      exact hc'.eq
    · rw [hmod, h] at hc'
      have := hc'.zpow_right 2
      rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, h3, mul_one,
        zpow_one] at this
      exact this.eq
  · intro c hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    exact ((show Commute c zJ from hc).zpow_right n).eq

theorem ks219J2 : CFSG.RankThree.PartTwo.Sec21.KS219J2 := by
  intro X _ _ ⟨e⟩ x hx1 hx
  let e' : X ≃* GJ := e.trans CFSG.ComponentClassification.J2Cover.nativeEquivP
  set P₀ : Subgroup X := P3.map e'.symm.toMonoidHom with hP₀def
  have hP₀ : Nat.card P₀ = 3 ^ (Nat.card X).factorization 3 := by
    rw [hP₀def, card_map_of_injective e'.symm.injective, card_P3, Nat.card_congr e'.toEquiv,
      factorization_card_GJ]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_center_of_isCentral218 hP₀ hx
  have hZ : P₀ ⊓ centralizer (P₀ : Set X) = (zpowers zJ).map e'.symm.toMonoidHom := by
    rw [hP₀def, ← CFSG.RankThree.PartTwo.Sec4.Sporadic.map_inf_centralizer e'.symm P3,
      inf_centralizer_P3, ← z_eq]
  rw [hZ] at hg
  obtain ⟨w, hw, hwx⟩ := mem_map.mp hg
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
  have hwx' : e'.symm (zJ ^ n) = g⁻¹ * x * g := hwx
  have hxw : x = g * e'.symm (zJ ^ n) * g⁻¹ := by rw [hwx']; group
  have hzn : zJ ^ n ≠ 1 := by
    intro h
    apply hx1
    rw [hxw, h, map_one, mul_one, mul_inv_cancel]
  have hmapC : (centralizer ({e'.symm (zJ ^ n)} : Set X)).map e'.toMonoidHom =
      centralizer ({zJ} : Set GJ) := by
    rw [Proving.centralizer_map_mulEquiv_wilson, MulEquiv.apply_symm_apply,
      centralizer_zpow_eq hzn]
  let φ : centralizer ({x} : Set X) ≃* centralizer ({zJ} : Set GJ) :=
    (MulEquiv.subgroupCongr (congrArg (fun y : X => centralizer ({y} : Set X)) hxw)).trans
      ((centralizerConjEquiv g _).trans
        ((e'.subgroupMap _).trans (MulEquiv.subgroupCongr hmapC)))
  have hq : CFSG.IsQuasisimple (centralizer ({x} : Set X)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm isQuasisimple_C
  rw [Proving.inSubgroup_layer_eq_self hq]
  exact ⟨mem_centralizer_singleton_iff.mpr rfl, isTripleCover_of_mulEquiv φ isTripleCover_C⟩

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KS219
