module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitIsoTransport
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.SignalizerFunctorTheorem.Solvable.SmallPrimes

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open scoped commutatorElement

@[expose] def footeTheta {G : Type} [Group G] (V : Subgroup G) (a : G) : Subgroup G :=
  ⁅oddCoreOfCentralizer a, V⁆ ⊔ (oddCoreOfCentralizer a ⊓ oddCoreIn (centralizer (V : Set G)))

variable {G : Type} [Group G] [Finite G]

theorem le_of_isKleinFour_inf_centralizer_le {F O X : Subgroup G} (hF : IsKleinFour F)
    (hFO : F ≤ normalizer (O : Set G)) (hO : Odd (Nat.card O))
    (h : ∀ w ∈ F, w ≠ 1 → O ⊓ centralizer ({w} : Set G) ≤ X) : O ≤ X := by
  have : CFSG.IsElementaryAbelian 2 F :=
    { toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two hF.exponent_two⟩⟩
      exponent_dvd_p := by rw [hF.exponent_two] }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction F O :=
    MulDistribMulAction.compHom O (O.normalizerMonoidHom.comp (Subgroup.inclusion hFO))
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := F) (H := O)
    (by rw [hF.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h))
  intro x hx
  have hle : ⨆ (a : F) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) O ≤
      X.comap O.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hconj : (a : G) * y * (a : G)⁻¹ = y :=
      (O.normalizerMonoidHom_apply_apply_coe _ y).symm.trans (congrArg Subtype.val hy)
    refine h a a.property (fun h => ha (Subtype.ext h))
      ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hconj]
      _ = a * y := by group
  exact hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : O))

theorem le_of_forall_hyperplane_inf_centralizer_le {E Y X : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (hE1 : E ≠ ⊥) (hEY : E ≤ normalizer (Y : Set G))
    (hY : Odd (Nat.card Y))
    (h : ∀ B : Subgroup G, B ≤ E → Nat.card B * 2 = Nat.card E →
      Y ⊓ centralizer (B : Set G) ≤ X) : Y ≤ X := by
  have : CFSG.IsElementaryAbelian 2 E :=
    { toIsMulCommutative := hEc
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun e =>
        Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp e e.2) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial E := (nontrivial_iff_ne_bot E).mpr hE1
  let : MulDistribMulAction E Y :=
    MulDistribMulAction.compHom Y (Y.normalizerMonoidHom.comp (Subgroup.inclusion hEY))
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := E) (H := Y)
    (fun h => (Nat.not_even_iff_odd.mpr hY) (even_iff_two_dvd.mpr h))
  intro x hx
  have hle : ⨆ (B : Subgroup E) (_ : B.index = 2), CFSG.fixedPointSubgroup B Y ≤
      X.comap Y.subtype := by
    refine iSup₂_le fun B hB => ?_
    intro y hy
    refine h (B.map E.subtype) (map_subtype_le B) ?_ ⟨y.property, ?_⟩
    · rw [Subgroup.card_map_of_injective E.subtype_injective, ← hB, B.card_mul_index]
    · show (y : G) ∈ centralizer ((B.map E.subtype : Subgroup G) : Set G)
      rw [mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hb' : (⟨b, hb⟩ : B) • y = y := hy ⟨b, hb⟩
      have hconj : ((b : E) : G) * y * ((b : E) : G)⁻¹ = y :=
        (Y.normalizerMonoidHom_apply_apply_coe _ y).symm.trans (congrArg Subtype.val hb')
      show ((b : E) : G) * y = y * ((b : E) : G)
      calc ((b : E) : G) * y = ((b : E) : G) * y * ((b : E) : G)⁻¹ * ((b : E) : G) := by group
        _ = y * ((b : E) : G) := by rw [hconj]
  exact hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : Y))

omit [Finite G] in
theorem map_conj_eq_self_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) :
    H.map (MulAut.conj x).toMonoidHom = H := by
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  exact ⟨fun h => by simpa [mul_assoc] using H.mul_mem (H.mul_mem hx h) (H.inv_mem hx),
    fun h => H.mul_mem (H.mul_mem (H.inv_mem hx) h) hx⟩

omit [Finite G] in
theorem map_conj_eq_self_of_mem_centralizer {V : Subgroup G} {x : G}
    (hx : x ∈ centralizer (V : Set G)) : V.map (MulAut.conj x).toMonoidHom = V := by
  have h1 : ∀ v ∈ V, x⁻¹ * v * x = v := fun v hv => by
    have := (mem_centralizer_iff.mp hx) v hv
    rw [mul_assoc, this]
    group
  ext y
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  refine ⟨fun h => ?_, fun h => by rw [h1 y h]; exact h⟩
  have h2 := h1 _ h
  have h3 : y = x⁻¹ * y * x := by
    calc y = x * (x⁻¹ * y * x) * x⁻¹ := by group
      _ = x * (x⁻¹ * (x⁻¹ * y * x) * x) * x⁻¹ := by rw [h2]
      _ = x⁻¹ * y * x := by group
  rw [h3]
  exact h

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact mem_map_of_mem _ hy
  · intro hy
    rw [← h, mem_map_equiv, MulAut.conj_symm_apply] at hy
    simpa [mul_assoc] using hy

omit [Finite G] in
theorem footeTheta_le {V : Subgroup G} {a : G} (hV : V ≤ centralizer ({a} : Set G)) :
    footeTheta V a ≤ oddCoreOfCentralizer a :=
  sup_le (commutator_le_self_of_le_normalizer fun _ hv =>
    mem_normalizer_oddCoreOfCentralizer (hV hv)) inf_le_left

theorem odd_card_footeTheta {V : Subgroup G} {a : G} (hV : V ≤ centralizer ({a} : Set G)) :
    Odd (Nat.card (footeTheta V a)) :=
  Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le (footeTheta_le hV))

omit [Finite G] in
theorem footeTheta_le_centralizer {V : Subgroup G} {a : G} (hV : V ≤ centralizer ({a} : Set G)) :
    footeTheta V a ≤ centralizer ({a} : Set G) :=
  (footeTheta_le hV).trans (map_subtype_le _)

omit [Finite G] in
theorem map_conj_footeTheta {V : Subgroup G} {a x : G} (hxa : x * a = a * x)
    (hxV : x ∈ centralizer (V : Set G)) :
    (footeTheta V a).map (MulAut.conj x).toMonoidHom = footeTheta V a := by
  have ha : (MulAut.conj x) a = a := by
    rw [MulAut.conj_apply, hxa, mul_assoc, mul_inv_cancel, mul_one]
  have h1 : (oddCoreOfCentralizer a).map (MulAut.conj x).toMonoidHom = oddCoreOfCentralizer a := by
    rw [map_oddCoreOfCentralizer_mulEquiv, ha]
  have hC : (centralizer (V : Set G)).map (MulAut.conj x).toMonoidHom = centralizer (V : Set G) :=
    map_conj_eq_self_of_mem hxV
  have h3 : (oddCoreIn (centralizer (V : Set G))).map (MulAut.conj x).toMonoidHom =
      oddCoreIn (centralizer (V : Set G)) := by
    unfold oddCoreIn
    rw [GSLit.map_map_pPrimeCore (MulAut.conj x) (centralizer (V : Set G)), hC]
  unfold footeTheta
  rw [Subgroup.map_sup, Subgroup.map_commutator, map_inf_eq _ _ _ (MulAut.conj x).injective, h1,
    map_conj_eq_self_of_mem_centralizer hxV, h3]

omit [Finite G] in
theorem footeTheta_le_iSup {E V : Subgroup G} {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) :
    footeTheta V b ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a :=
  le_iSup₂_of_le (f := fun a (_ : a ∈ E) => ⨆ (_ : a ≠ 1), footeTheta V a) b hb
    (le_iSup (fun _ : b ≠ 1 => footeTheta V b) hb1)

theorem footeTheta_completion {E V : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : 2 ^ 3 ∣ Nat.card E)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b) :
    Odd (Nat.card ↥(⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a)) ∧
      ∀ a ∈ E, a ≠ 1 →
        (⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a) ⊓ centralizer ({a} : Set G) =
          footeTheta V a := by
  have hVa : ∀ a ∈ E, V ≤ centralizer ({a} : Set G) := fun a ha v hv =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hVE a ha)) v hv)
  have hcomm : ∀ x ∈ E, ∀ a ∈ E, x * a = a * x := fun x hx a ha =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨x, hx⟩ ⟨a, ha⟩)
  have hθ : CFSG.Open.IsSolvableSignalizerFunctor 2 E (footeTheta V) :=
    { le_centralizer := fun a ha _ => footeTheta_le_centralizer (hVa a ha)
      coprime := fun a ha _ => Nat.coprime_two_left.mpr (odd_card_footeTheta (hVa a ha))
      invariant := fun a ha _ x hx => map_conj_footeTheta (hcomm x hx a ha) (hVE x hx)
      balance := hbal
      solvable := fun a ha _ => CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_footeTheta (hVa a ha)) }
  obtain ⟨hcop, -, hcent⟩ := CFSG.SignalizerFunctorTheorem.Solvable.glauberman_of_le_three G 2
    Nat.prime_two (by norm_num) E hEc hexp h8 (footeTheta V) hθ
  exact ⟨Nat.coprime_two_left.mp hcop, fun a ha ha1 => (hcent a ha ha1).symm⟩

omit [Finite G] in
theorem le_normalizer_footeTheta_completion {E V : Subgroup G} (hEc : IsMulCommutative E)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G)) :
    E ≤ normalizer ((⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a : Subgroup G) : Set G) := by
  intro x hx
  apply mem_normalizer_of_map_conj_eq
  simp only [Subgroup.map_iSup]
  refine iSup_congr fun a => iSup_congr fun ha => iSup_congr fun _ =>
    map_conj_footeTheta ?_ (hVE x hx)
  exact congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨x, hx⟩ ⟨a, ha⟩)

theorem footeTheta_completion_eq_iSup {E V F : Subgroup G} (hEc : IsMulCommutative E)
    (hexp : ∀ e ∈ E, e ^ 2 = 1) (h8 : 2 ^ 3 ∣ Nat.card E)
    (hVE : ∀ e ∈ E, e ∈ centralizer (V : Set G))
    (hbal : ∀ a ∈ E, a ≠ 1 → ∀ b ∈ E, b ≠ 1 →
      footeTheta V a ⊓ centralizer ({b} : Set G) ≤ footeTheta V b)
    (hF : IsKleinFour F) (hFE : F ≤ E) :
    (⨆ a ∈ E, ⨆ (_ : a ≠ 1), footeTheta V a) = ⨆ w ∈ F, ⨆ (_ : w ≠ 1), footeTheta V w := by
  obtain ⟨hodd, hcent⟩ := footeTheta_completion hEc hexp h8 hVE hbal
  apply le_antisymm
  · refine le_of_isKleinFour_inf_centralizer_le hF
      (hFE.trans (le_normalizer_footeTheta_completion hEc hVE)) hodd fun w hw hw1 => ?_
    rw [hcent w (hFE hw) hw1]
    exact le_iSup₂_of_le w hw (le_iSup_of_le hw1 le_rfl)
  · exact iSup₂_le fun w hw => iSup_le fun hw1 =>
      le_iSup₂_of_le w (hFE hw) (le_iSup_of_le hw1 le_rfl)

end CFSG.ComponentClassification.FooteLit
