module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionShape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_center_map_of_mem_centralizer {D : Subgroup G} {c : G} (hcD : c ∈ D)
    (hc : c ∈ centralizer (D : Set G)) : c ∈ (center D).map D.subtype :=
  ⟨⟨c, hcD⟩, mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hc g g.2), rfl⟩

omit [Finite G] in
private theorem mul_mul_inv_mul_inv_aux {g h x : G}
    (hgb : g * (h * x * h⁻¹ * x⁻¹) = (h * x * h⁻¹ * x⁻¹) * g)
    (hab : (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) = (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹)) :
    g * h * x * (g * h)⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) :=
  calc g * h * x * (g * h)⁻¹ * x⁻¹
      = g * (h * x * h⁻¹ * x⁻¹) * x * g⁻¹ * x⁻¹ := by group
    _ = (h * x * h⁻¹ * x⁻¹) * g * x * g⁻¹ * x⁻¹ := by rw [hgb]
    _ = (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    _ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) := hab.symm

private theorem card_le_mul_card_of_commutator_mem {D Z C : Subgroup G} {x : G}
    (hZD : Z ≤ D) (hZc : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d)
    (hcomm : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ Z) (hC : ∀ g ∈ D, g * x = x * g → g ∈ C) :
    Nat.card D ≤ Nat.card C * Nat.card Z := by
  let φ : D →* Z :=
    { toFun := fun g => ⟨(g : G) * x * (g : G)⁻¹ * x⁻¹, hcomm g g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        have hb := hcomm h h.2
        change (g : G) * h * x * ((g : G) * h)⁻¹ * x⁻¹ =
          ((g : G) * x * (g : G)⁻¹ * x⁻¹) * ((h : G) * x * (h : G)⁻¹ * x⁻¹)
        exact mul_mul_inv_mul_inv_aux (hZc _ hb g g.2) (hZc _ (hcomm g g.2) _ (hZD hb)).symm) }
  have hker : φ.ker.map D.subtype ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    refine hC g g.2 ?_
    have h1 : (g : G) * x * (g : G)⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  calc Nat.card D = Nat.card φ.ker * Nat.card φ.range := (card_ker_mul_card_range φ).symm
    _ ≤ Nat.card C * Nat.card Z := by
      refine Nat.mul_le_mul ?_ (card_le_card_group _)
      calc Nat.card φ.ker = Nat.card (φ.ker.map D.subtype) :=
            (card_map_of_injective D.subtype_injective).symm
        _ ≤ Nat.card C := card_le_of_le hker

theorem ExtremalObstruction.card_eq_of_not_isMulCommutative {p : ℕ} {P : Sylow p G}
    {M D : Subgroup G} (hext : ExtremalObstruction p P M D) (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ¬ IsMulCommutative D) : Nat.card D = p ^ 3 := by
  classical
  have hfact : Fact p.Prime := ⟨hp⟩
  obtain ⟨hpow, hcomm⟩ := hext.pow_eq_one_and_commutator_mem hp hp2
  set Z : Subgroup G := (center D).map D.subtype with hZ
  have hZD : Z ≤ D := map_subtype_le _
  have hZc : Nat.card Z = p := hext.card_center_eq hp hp2 hD
  have hZcomm : ∀ z ∈ Z, ∀ d ∈ D, d * z = z * d := fun z hz d hd =>
    mul_comm_of_mem_center_map hz hd
  have hZe : CFSG.IsElementaryAbelian p Z :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Z).2
      ⟨⟨⟨fun a b => Subtype.ext (hZcomm b b.2 a (hZD a.2))⟩⟩, fun z hz => hpow z (hZD hz)⟩
  obtain ⟨x, hxD, hxZ⟩ : ∃ x ∈ D, x ∉ Z := by
    by_contra h
    push Not at h
    exact hD ⟨⟨fun a b => Subtype.ext (hZcomm _ (h b b.2) a a.2)⟩⟩
  have hxp : x ^ p = 1 := hpow x hxD
  have hZx : ∀ z ∈ Z, z * x = x * z := fun z hz => (hZcomm z hz x hxD).symm
  set E : Subgroup G := Z ⊔ zpowers x with hE
  have hEc : Nat.card E = p ^ 2 := by
    rw [hE, card_sup_zpowers hp Z hxp hxZ hZx, hZc, pow_two]
  have hED : E ≤ D := sup_le hZD (zpowers_le.mpr hxD)
  have hxe : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hEe : CFSG.IsElementaryAbelian p E :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer
      (zpowers_le.mpr (mem_centralizer_iff.mpr hZx))
  have hCE : ∀ y ∈ D, y * x = x * y → y ∈ E := by
    intro y hyD hyx
    by_contra hyE
    have hyp : y ^ p = 1 := hpow y hyD
    have hEy : E ≤ centralizer ({y} : Set G) := by
      refine sup_le (fun z hz => ?_) (zpowers_le.mpr ?_)
      · exact mem_centralizer_singleton_iff.mpr (hZcomm z hz y hyD).symm
      · exact mem_centralizer_singleton_iff.mpr hyx.symm
    have hEy' : ∀ e ∈ E, e * y = y * e := fun e he =>
      mem_centralizer_singleton_iff.mp (hEy he)
    have hye : CFSG.IsElementaryAbelian p (zpowers y) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hyp
    have hcard : Nat.card ↥(E ⊔ zpowers y) = p ^ 3 := by
      rw [card_sup_zpowers hp E hyp hyE hEy', hEc, ← pow_succ]
    have hF : CFSG.IsElementaryAbelian p ↥(E ⊔ zpowers y) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer
        (zpowers_le.mpr (mem_centralizer_iff.mpr fun e he => hEy' e he))
    have h3 : 3 ≤ CFSG.Open.pRank p D := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hp.one_lt _)
        ⟨E ⊔ zpowers y, sup_le hED (zpowers_le.mpr hyD),
          (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hF, hcard⟩
    have h2 := hext.rank_eq
    omega
  have hcomm' : ∀ g ∈ D, g * x * g⁻¹ * x⁻¹ ∈ Z := fun g hg =>
    mem_center_map_of_mem_centralizer
      (mul_mem (mul_mem (mul_mem hg hxD) (inv_mem hg)) (inv_mem hxD)) (hcomm g hg x hxD)
  have hle : Nat.card D ≤ p ^ 3 := by
    have h := card_le_mul_card_of_commutator_mem hZD hZcomm hcomm' hCE
    rw [hEc, hZc] at h
    calc Nat.card D ≤ p ^ 2 * p := h
      _ = p ^ 3 := by ring
  have hDp : IsPGroup p D := P.isPGroup'.to_le hext.obstruction.2.1
  obtain ⟨k, hk⟩ := hDp.exists_card_eq
  have hEltD : E < D := lt_of_le_of_ne hED fun h => hD (h ▸ hEe.toIsMulCommutative)
  have hlt : p ^ 2 < p ^ k := by
    rw [← hEc, ← hk]
    exact card_lt_of_lt hEltD
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right hp.one_lt).1 (by rw [← hk]; exact hle)
  have hk2 : 2 < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  rw [hk, show k = 3 by omega]

end CFSG.LocalAnalysis.RankThreeTheoremC
