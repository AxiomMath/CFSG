module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCTwoLocalA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.style.longLine false


theorem exists_centralizer_of_card_81 {E : Subgroup GM} (hE : E ≤ P0G) (hz : zG ∈ E)
    (hcard : Nat.card E = 81) :
    ∃ a ∈ P0G, a ∉ zpowers zG ∧ ∀ w ∈ E, w * a = a * w := by
  let E' : Subgroup P0G := E.subgroupOf P0G
  let U₀ : Subgroup (Multiplicative (Fin 4 → ZMod 3)) := E'.map relG.coordHom
  let U : Submodule (ZMod 3) (Fin 4 → ZMod 3) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ U₀}
      add_mem' := fun {a b} ha hb => by
        have := U₀.mul_mem ha hb
        exact this
      zero_mem' := U₀.one_mem
      smul_mem' := fun c v hv => by
        have h1 : c • v = c.val • v := by
          conv_lhs => rw [← ZMod.natCast_zmod_val c]
          exact Nat.cast_smul_eq_nsmul (ZMod 3) c.val v
        show Multiplicative.ofAdd (c • v) ∈ U₀
        rw [h1, ofAdd_nsmul]
        exact U₀.pow_mem hv _ }
  have hmemU : ∀ w : P0G, (w : GM) ∈ E → relG.coord w ∈ U := fun w hw =>
    ⟨w, hw, rfl⟩
  have hlt : U < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hall : ∀ p : P0G, (p : GM) ∈ E := by
      intro p
      have hp : Multiplicative.ofAdd (relG.coord p) ∈ U₀ := by
        have : relG.coord p ∈ U := by rw [htop]; trivial
        exact this
      obtain ⟨e, he, hep⟩ := hp
      have hker : p * e⁻¹ ∈ relG.coordHom.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have h1 : relG.coordHom e = Multiplicative.ofAdd (relG.coord p) := hep
        rw [h1]
        show Multiplicative.ofAdd (relG.coord p) * (Multiplicative.ofAdd (relG.coord p))⁻¹ = 1
        exact mul_inv_cancel _
      rw [relG.coordHom_ker, mem_subgroupOf] at hker
      have hpe : (p : GM) = (p * e⁻¹ : P0G) * (e : GM) := by
        simp
      rw [hpe]
      exact mul_mem ((zpowers_le).2 hz hker) he
    have hcard' : Nat.card E = 243 := by
      have : E = P0G := le_antisymm hE (fun p hp => hall ⟨p, hp⟩)
      rw [this]
      exact relG.card_threeQ_type
    omega
  obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U hlt
  set c : Fin 4 → ZMod 3 := fun i => f (fun j => if i = j then 1 else 0) with hc
  have hfc : ∀ e, f e = ∑ i, c i * e i := fun e => by
    rw [LinearMap.pi_apply_eq_sum_univ f e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hc0 : c ≠ 0 := by
    intro h0
    apply hf0
    apply LinearMap.ext
    intro e
    rw [LinearMap.zero_apply, hfc e]
    simp [h0]
  obtain ⟨u, hu⟩ := Finite.surjective_of_injective relG.threeForm_injective c
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hu]
    funext j
    simp [ThreeQRel.threeForm]
  have ha : threeNF zG xG 0 u ∈ P0G := ThreeQRel.nf_mem 0 u
  refine ⟨threeNF zG xG 0 u, ha, ?_, fun w hw => ?_⟩
  · intro h
    have := (relG.coord_eq_zero_iff ⟨_, ha⟩).2 h
    rw [relG.coord_nf] at this
    exact hu0 this
  · have hwP := hE hw
    have h1 := (relG.commute_iff ⟨threeNF zG xG 0 u, ha⟩ ⟨w, hwP⟩).2 (by
      have hw' : relG.coord ⟨w, hwP⟩ ∈ U := hmemU _ hw
      have h2 : f (relG.coord ⟨w, hwP⟩) = 0 := hfU hw'
      rw [hfc] at h2
      rw [relG.coord_nf]
      rw [← h2, ThreeQRel.threePair]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show ThreeQRel.threeForm omegaZ u j = c j from congrFun hu j])
    exact (congrArg Subtype.val h1).symm

theorem conj_inv_mem {n : GM} (hn : ∀ h ∈ P0G, n⁻¹ * h * n ∈ P0G) :
    ∀ h ∈ P0G, n * h * n⁻¹ ∈ P0G := by
  have hle : P0G.map (MulAut.conj n⁻¹).toMonoidHom ≤ P0G := by
    rintro _ ⟨k, hk, rfl⟩
    have := hn k hk
    simpa [MulAut.conj_apply] using this
  have heq : P0G.map (MulAut.conj n⁻¹).toMonoidHom = P0G :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective])
  intro h hh
  rw [← heq] at hh
  obtain ⟨k, hk, hkh⟩ := hh
  have : n * h * n⁻¹ = k := by
    rw [← hkh]
    simp
    group
  rw [this]
  exact hk

theorem exists_conj_x0_normalizing {g : GM} (hg : g ∈ P0G) (hgz : g ∉ zpowers zG) :
    ∃ (n : GM) (c : ℕ), (∀ h ∈ P0G, n⁻¹ * h * n ∈ P0G) ∧ n⁻¹ * g * n = xG 0 * zG ^ c := by
  set v := relG.coord ⟨g, hg⟩ with hv
  have hv0 : v ≠ 0 := fun h0 => hgz ((relG.coord_eq_zero_iff _).1 h0)
  refine ⟨wordN (vw v), (relG.nfEquiv.symm ⟨_, conjW_mem _ (vw_lt v) hg⟩).1.val,
    fun h hh => conjW_mem _ (vw_lt v) hh, ?_⟩
  have hc := coord_conjW (vw v) (vw_lt v) hg
  rw [← hv, vecWord_spec v hv0] at hc
  have hnf := relG.eq_nf ⟨_, conjW_mem _ (vw_lt v) hg⟩
  rw [hc] at hnf
  refine hnf.trans ?_
  simp [threeNF, val_one_three]

theorem conj_zG_pow (n : GM) (k : ℕ) : n * zG ^ k * n⁻¹ = zG ^ k := by
  have h : n * zG ^ k = zG ^ k * n := ((Commute.pow_left (zG_central n) k).eq).symm
  rw [h]
  group

theorem exists_g_centralizer {a : GM} (ha : a ∈ P0G) (haz : a ∉ zpowers zG) :
    ∃ g : GM, (∀ h ∈ P0G, g⁻¹ * h * g ∈ P0G) ∧
      ∀ w : GM, w * a = a * w → (g⁻¹ * w * g) * xG 1 = xG 1 * (g⁻¹ * w * g) := by
  obtain ⟨na, ca, hna, hca⟩ := exists_conj_x0_normalizing ha haz
  obtain ⟨n1, c1, hn1, hc1⟩ := exists_conj_x0_normalizing (ThreeQRel.v_mem 1 :
    xG 1 ∈ P0G) (xG_not_mem_zpowers_z 1)
  refine ⟨na * n1⁻¹, fun h hh => ?_, fun w hw => ?_⟩
  · have e : (na * n1⁻¹)⁻¹ * h * (na * n1⁻¹) = n1 * (na⁻¹ * h * na) * n1⁻¹ := by group
    rw [e]
    exact conj_inv_mem hn1 _ (hna h hh)
  · have Ea : a = na * xG 0 * na⁻¹ * zG ^ ca := by
      calc a = na * (na⁻¹ * a * na) * na⁻¹ := by group
        _ = na * (xG 0 * zG ^ ca) * na⁻¹ := by rw [hca]
        _ = na * xG 0 * na⁻¹ * (na * zG ^ ca * na⁻¹) := by group
        _ = na * xG 0 * na⁻¹ * zG ^ ca := by rw [conj_zG_pow]
    have Eg : (na * n1⁻¹) * xG 1 * (na * n1⁻¹)⁻¹ = na * xG 0 * na⁻¹ * zG ^ c1 := by
      calc (na * n1⁻¹) * xG 1 * (na * n1⁻¹)⁻¹ = na * (n1⁻¹ * xG 1 * n1) * na⁻¹ := by group
        _ = na * (xG 0 * zG ^ c1) * na⁻¹ := by rw [hc1]
        _ = na * xG 0 * na⁻¹ * (na * zG ^ c1 * na⁻¹) := by group
        _ = na * xG 0 * na⁻¹ * zG ^ c1 := by rw [conj_zG_pow]
    have hcent : centralizer ({a} : Set GM) = centralizer ({(na * n1⁻¹) * xG 1 * (na * n1⁻¹)⁻¹} : Set GM) := by
      rw [Ea, Eg, centralizer_mul_zpow, centralizer_mul_zpow]
    have hw' : w ∈ centralizer ({(na * n1⁻¹) * xG 1 * (na * n1⁻¹)⁻¹} : Set GM) := by
      rw [← hcent]
      exact mem_centralizer_singleton_iff.2 hw
    rw [← map_conj_centralizer] at hw'
    obtain ⟨w0, hw0, hw0w⟩ := hw'
    have : w0 = (na * n1⁻¹)⁻¹ * w * (na * n1⁻¹) := by
      rw [← hw0w]
      simp [MulAut.conj_apply]
      group
    rw [← this]
    exact mem_centralizer_singleton_iff.1 hw0

end CFSG.HardMathSupport.Solomon.Coordinator
