module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SZGammaThree
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanSignalizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldSignalizer
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvSylow

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

structure SuzSylowData (P : Subgroup G) (t : G) : Prop where
  elem : ∀ D : Subgroup G, IsSylowTwoIn D P →
    IsElemTwo (zGammaThree D) ∧ 16 ≤ Nat.card (zGammaThree D)
  big : ∀ D : Subgroup G, IsSylowTwoIn D P → 32 ≤ Nat.card ↥(zGammaThree D ⊔ zpowers t)
  gen : ∀ D : Subgroup G, IsSylowTwoIn D P → ∃ Q : Subgroup G, Q ≤ D ∧ IsElemTwo Q ∧
    8 ≤ Nat.card Q ∧ P ≤ D ⊔ (P ⊓ centralizer (Q : Set G)) ⊔ oddIn P

theorem wGroup_zGammaThree_basic (hB : GWTwoBalanced G) {P D : Subgroup G} (hDP : D ≤ P)
    (hPU : P ≤ normalizer (oddIn P : Set G)) (hUo : Odd (Nat.card (oddIn P)))
    (hA : IsElemTwo (zGammaThree D)) (h16 : 16 ≤ Nat.card (zGammaThree D)) :
    Odd (Nat.card (wGroup (zGammaThree D))) ∧
      oddIn P ≤ normalizer (wGroup (zGammaThree D) : Set G) ∧
      D ≤ normalizer (wGroup (zGammaThree D) : Set G) :=
  ⟨odd_card_wGroup hB hA h16,
    le_normalizer_wGroup_of_odd hB hA h16 (((zGammaThree_le D).trans hDP).trans hPU) hUo,
    fun _ hd => GrS4.mem_normalizer_wGroup (mem_normalizer_zGammaThree (le_normalizer hd))⟩

theorem wGroup_eq_wGroup_zGammaThree_of_le (hB : GWTwoBalanced G) {t : G} (ht : orderOf t = 2)
    {D : Subgroup G} (hD : IsPGroup 2 D) (hDt : D ≤ centralizer ({t} : Set G))
    (hA : IsElemTwo (zGammaThree D)) (hA8 : 8 ≤ Nat.card (zGammaThree D))
    (h32 : 32 ≤ Nat.card ↥(zGammaThree D ⊔ zpowers t)) {Q : Subgroup G} (hQD : Q ≤ D)
    (hQ3 : IsAbelianTwoOfRank 3 Q) :
    wGroup Q = wGroup (zGammaThree D) := by
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  refine wGroup_eq_wGroup_zGammaThree hB ht hD hDt (HSFLit.L34Inv.isPGroup_zpowers_of_mul_self htt)
    (mem_zpowers t) (zpowers_le.mpr htC) (zpowers_le.mpr ?_) hA hA8 h32 (hQD.trans le_sup_left)
    hQ3
  exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun d hd =>
    mem_centralizer_singleton_iff.mp (hDt hd))

theorem le_normalizer_wGroup_zGammaThree (hB : GWTwoBalanced G) {t : G} (ht : orderOf t = 2)
    {P : Subgroup G} (hPt : P ≤ centralizer ({t} : Set G))
    (hPU : P ≤ normalizer (oddIn P : Set G)) (hUo : Odd (Nat.card (oddIn P)))
    (hdata : SuzSylowData P t) {D : Subgroup G} (hD : IsSylowTwoIn D P) :
    P ≤ normalizer (wGroup (zGammaThree D) : Set G) := by
  obtain ⟨hA, h16⟩ := hdata.elem D hD
  obtain ⟨-, hUW, hDW⟩ := wGroup_zGammaThree_basic hB hD.1 hPU hUo hA h16
  obtain ⟨Q, hQD, hQ, hQ8, hPgen⟩ := hdata.gen D hD
  have hWQ : wGroup Q = wGroup (zGammaThree D) :=
    wGroup_eq_wGroup_zGammaThree_of_le hB ht hD.isPGroup (hD.1.trans hPt) hA (by omega)
      (hdata.big D hD) hQD (hQ.isAbelianTwoOfRank hQ8)
  have hCW : P ⊓ centralizer (Q : Set G) ≤ normalizer (wGroup (zGammaThree D) : Set G) :=
    fun _ hx => hWQ ▸ GrS4.mem_normalizer_wGroup (centralizer_le_normalizer _ hx.2)
  exact hPgen.trans (sup_le (sup_le hDW hCW) hUW)

theorem exists_wGroup_glue_of_sylowData (hB : GWTwoBalanced G) {t : G} (ht : orderOf t = 2)
    {P : Subgroup G} (hPt : P ≤ centralizer ({t} : Set G))
    (hCN : centralizer ({t} : Set G) ≤ normalizer (P : Set G))
    (hPU : P ≤ normalizer (oddIn P : Set G)) (hUo : Odd (Nat.card (oddIn P)))
    (hdata : SuzSylowData P t) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧ normalizer (P : Set G) ≤ normalizer (W : Set G) ∧
      (∀ E : Subgroup G, E ≤ centralizer ({t} : Set G) → Open.IsElemAbelian 2 E →
        8 ≤ Nat.card E → wGroup E = W) ∧
      ∀ D : Subgroup G, IsSylowTwoIn D P → wGroup (zGammaThree D) = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₀, hD₀, -, -⟩ := HSFLit.L34Inv.exists_isSylowTwoIn_normalized
    (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G)) bot_le
  obtain ⟨hA₀, h16₀⟩ := hdata.elem D₀ hD₀
  have hPN := le_normalizer_wGroup_zGammaThree hB ht hPt hPU hUo hdata hD₀
  have hconj : ∀ D : Subgroup G, IsSylowTwoIn D P →
      wGroup (zGammaThree D) = wGroup (zGammaThree D₀) := by
    intro D hD
    obtain ⟨d, hdP, hd⟩ := hD₀.exists_conj_le hD.1 hD.isPGroup
    have hDD : D₀.map (MulAut.conj d⁻¹).toMonoidHom = D := by
      refine hD.eq_of_le (fun q hq => ⟨d * q * d⁻¹, hd q hq, ?_⟩) ?_ (hD₀.isPGroup.map _)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      · rintro _ ⟨x, hx, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact P.mul_mem (P.mul_mem (P.inv_mem hdP) (hD₀.1 hx)) hdP
    rw [← hDD, zGammaThree_map_conj, wGroup_map_conj]
    exact mem_normalizer_iff_map_conj_eq.mp (hPN (P.inv_mem hdP))
  refine ⟨wGroup (zGammaThree D₀), odd_card_wGroup hB hA₀ h16₀, ?_, ?_, hconj⟩
  ·
    intro g hg
    have hgP : D₀.map (MulAut.conj g).toMonoidHom ≤ P := by
      rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_iff.mp hg r).mp (hD₀.1 hr)
    obtain ⟨d, hdP, hd⟩ := hD₀.exists_conj_le hgP (hD₀.isPGroup.map _)
    have hdg : D₀.map (MulAut.conj (d * g)).toMonoidHom = D₀ := by
      refine eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
      rintro _ ⟨r, hr, rfl⟩
      have := hd _ ⟨r, hr, rfl⟩
      convert this using 1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
      group
    have := mul_mem (inv_mem (hPN hdP)) (GrS4.mem_normalizer_wGroup
      (mem_normalizer_zGammaThree (mem_normalizer_iff_map_conj_eq.mpr hdg)))
    simpa using this
  ·
    intro E hEt hEab hE8
    have hE : IsElemTwo E := by
      refine ⟨fun a ha b hb => congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩),
        fun a ha => ?_⟩
      rw [← pow_two]
      exact hEab.2 a ha
    have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    have htC : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
    have hX : IsElemTwo (E ⊔ zpowers t) := hE.sup (isElemTwo_zpowers htt) fun x hx y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (mem_centralizer_singleton_iff.mp (hEt hx)) k).eq
    have hXt : E ⊔ zpowers t ≤ centralizer ({t} : Set G) := sup_le hEt (zpowers_le.mpr htC)
    obtain ⟨D, hD, hXD, -⟩ :=
      HSFLit.L34Inv.exists_isSylowTwoIn_normalized hX.isPGroup (hXt.trans hCN)
    obtain ⟨hA, h16⟩ := hdata.elem D hD
    rw [← hconj D hD]
    exact wGroup_eq_wGroup_zGammaThree hB ht hD.isPGroup (hD.1.trans hPt) hX.isPGroup
      (mem_sup_right (mem_zpowers t)) hXt hXD hA (by omega) (hdata.big D hD)
      (le_sup_left.trans le_sup_right) (hE.isAbelianTwoOfRank hE8)

end CFSG.ComponentClassification.GrSLit.L34Sec5S
