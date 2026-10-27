module

public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Basic
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PerfectCover.HopfCover
import CFSG.LocalAnalysis.SectionRank.QTK.A134List0
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.SectionRank.QTK.Witness3
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.Open.StatedCenterThree
import CFSG.Quasithin.Background.A3FactsClassical
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.Assembly.InCatalog
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBA134Defs
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

public section

namespace CFSG.SectionRank.QTK.CentreFact.LayerPair

open Subgroup CFSG.SectionRank.QTK CFSG.SectionRank.QTK.CoverB CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.Quasithin.A3Facts CFSG.SectionRank.ClassicalEven
open CFSG.Assembly.RankThreeEven (localRank)

private theorem not_dvd_three_of_ne' {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) : ¬ r ∣ 3 := fun h =>
  hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)

theorem exists_prime_witness_psu_three_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (hf3 : f ≠ 3) (hm : StatedClassicalModel S .PSU 3 2 f) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup S) ∧
      1 ≤ localRank r S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_add_one hf hf3
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h0 : 0 < 2 ^ f := by positivity
    omega
  refine ⟨r, hr, hr2, hr3, ?_, ?_⟩
  · rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e]
    have := Fact.mk hr
    have hq : 2 ^ f ≠ 0 := by positivity
    have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
      rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
    obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) r
      (by rw [hcard]; exact hrd.mul_right _)
    have hζq : ζ ^ (2 ^ f + 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hrd)
    exact two_le_pRank_torus_shared hr3 hζ (i₀ := 0) (i₁ := 1) (i₂ := 2) (by decide) (by decide)
      (by decide)
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
      (torusDiag_mem_SU hq (prod_torusVec ζ _ _) (by rw [torusVec_pow, hζq, torusVec_one]))
  · rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr]
    exact CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus hU (k := 0) hr hrd
      (by norm_num) (Or.inr (not_dvd_three_of_ne' hr hr3))

theorem false_of_components_of_witness {H : Type} [Group H] [Finite H]
    (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hrZ : ¬ r ∣ Nat.card (center ↥L₁))
    (h2 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥L₁ ⧸ center ↥L₁)))
    (h1 : 1 ≤ localRank r (↥L₁ ⧸ center ↥L₁)) : False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R, hR, hR2, hk⟩ := exists_twoLocal_eq_localRank hr.one_lt h1
  obtain ⟨E, hEN, hE, hEc⟩ :=
    CFSG.SectionRank.exists_pRank hr.one_lt (normalizer (R : Set (↥L₁ ⧸ center ↥L₁)))
  have hpos : 1 ≤ CFSG.Open.pRank r (normalizer (R : Set (↥L₁ ⧸ center ↥L₁))) := by omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) r (by
    rw [hEc]; exact dvd_pow_self r (by omega))
  obtain ⟨F, -, hF, hFc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
  refine false_of_components he hc φ hr hr2 hR hR2 (x := (x : ↥L₁ ⧸ center ↥L₁))
    (hEN x.2) (by rw [← Subgroup.orderOf_coe] at hx; exact hx) (Or.inr hrZ) fun _ => ⟨F, hF, hFc⟩

theorem false_of_components_psu_three_even {H : Type} [Group H] [Finite H]
    (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) {f : ℕ} (hf : 2 ≤ f) (hf3 : f ≠ 3)
    (hm : StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 3 2 f)
    (hZ3 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center ↥L₁) → r = 3) : False := by
  obtain ⟨r, hr, hr2, hr3, h2, h1⟩ := exists_prime_witness_psu_three_even hf hf3 hm
  exact false_of_components_of_witness he hc φ hr hr2 (fun h => hr3 (hZ3 r hr hr2 h)) h2 h1

section Torus

variable {H : Type} [Group H] [Finite H]

theorem false_of_extra_element (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) {t : H} (htL : t ∈ L₁) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) {F₂ : Subgroup H} (hF₂ : CFSG.Open.IsElemAbelian 3 F₂)
    (hF₂c : Nat.card F₂ = 3 ^ 2) (hF₂L : F₂ ≤ L₂) {y : H} (hy3 : y ^ 3 = 1) (hyL : y ∉ L₂)
    (hyt : Commute y t) (hyF : ∀ g ∈ F₂, Commute y g) : False := by
  have hR : zpowers t ≠ ⊥ := fun h => ht1 (Subgroup.mem_bot.mp (h ▸ mem_zpowers t))
  have hR2 : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_sq ht2
  have hRL : zpowers t ≤ L₁ := zpowers_le.2 htL
  have hF₂N : F₂ ≤ normalizer ((zpowers t : Subgroup H) : Set H) :=
    hF₂L.trans (le_normalizer_of_commuting hc hRL)
  obtain ⟨F, hF, hFc, hFN⟩ := exists_elemAbelian_sup Nat.prime_three hF₂ hF₂c hy3 hyF
    (fun h => hyL (hF₂L h)) (K := normalizer ((zpowers t : Subgroup H) : Set H))
    (mem_normalizer_zpowers hyt) hF₂N
  have := le_two_of_evenRank_le_two he hR hR2 Nat.prime_three (by norm_num) hF hFN hFc
  omega

theorem false_of_pair_torus_data (he : CFSG.Open.evenRank H ≤ 2) {L₁ L₂ : Subgroup H}
    (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂) (hZ : Nat.card (center ↥L₁) = 3)
    {x t e : ↥L₁} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (hxt : Commute x t) (hxe : Commute x e)
    (he3 : e ^ 3 = 1) (hx3c : x ^ 3 ∈ center ↥L₁) (hx3 : x ^ 3 ≠ 1)
    (hexω : e ∉ zpowers (x ^ 3)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : ∀ z ∈ center ↥L₁, z ^ 3 = 1 := fun z hz => by
    have h := pow_card_eq_one' (G := ↥(center ↥L₁)) (x := ⟨z, hz⟩)
    rw [hZ] at h
    simpa using congrArg Subtype.val h
  have hω3 : (x ^ 3) ^ 3 = 1 := hcube _ hx3c
  have hωord : orderOf (x ^ 3) = 3 := orderOf_eq_prime hω3 hx3
  have hZgen : center ↥L₁ = zpowers (x ^ 3) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hx3c) ?_
    rw [Nat.card_zpowers, hωord, hZ]
  obtain ⟨F₀, hF₀, hF₀c, hF₀K⟩ := exists_elemAbelian_sup Nat.prime_three (k := 1)
    (isElemAbelian_zpowers_of_pow hω3) (by rw [Nat.card_zpowers, hωord, pow_one]) he3
    (fun g hg => by
      have hgz : g ∈ center ↥L₁ := by rw [hZgen]; exact hg
      exact Subgroup.mem_center_iff.mp hgz e)
    hexω (K := centralizer ({x} : Set ↥L₁))
    (Subgroup.mem_centralizer_singleton_iff.2 hxe.eq.symm)
    (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
      ((Commute.refl x).pow_left 3).eq))
  set f : ↥L₁ →* H := L₂.subtype.comp φ.toMonoidHom with hf
  have hfinj : Function.Injective f := L₂.subtype_injective.comp φ.injective
  have hfL : ∀ g : ↥L₁, f g ∈ L₂ := fun g => (φ g).2
  set F₂ : Subgroup H := F₀.map f with hF₂def
  have hF₂ : CFSG.Open.IsElemAbelian 3 F₂ := CFSG.SectionRank.isElemAbelian_map hF₀ f
  have hF₂c : Nat.card F₂ = 3 ^ 2 := by
    rw [hF₂def, card_map_of_injective hfinj, hF₀c]
  have hF₂L : F₂ ≤ L₂ := by
    rintro _ ⟨g, -, rfl⟩
    exact hfL g
  have hF₂x : ∀ g ∈ F₂, Commute g (f x) := by
    rintro _ ⟨g, hg, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hF₀K hg)
    show f g * f x = f x * f g
    rw [← map_mul, ← map_mul, h]
  have ht2H : (t : H) ^ 2 = 1 := by rw [← SubgroupClass.coe_pow, ht2]; rfl
  have ht1H : (t : H) ≠ 1 := fun h => ht1 (Subtype.ext (by simpa using h))
  have hω3H : (((x ^ 3 : ↥L₁)) : H) ^ 3 = 1 := by rw [← SubgroupClass.coe_pow, hω3]; rfl
  by_cases hωL : (((x ^ 3 : ↥L₁)) : H) ∈ L₂
  ·
    have hωc : (⟨(((x ^ 3 : ↥L₁)) : H), hωL⟩ : ↥L₂) ∈ center ↥L₂ :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc _ (x ^ 3 : ↥L₁).2 g g.2).eq.symm
    have hζ : φ.symm ⟨(((x ^ 3 : ↥L₁)) : H), hωL⟩ ∈ center ↥L₁ :=
      Subgroup.mem_center_iff.2 fun g => by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hωc (φ g)
    rw [hZgen] at hζ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hζ
    have hk' : (f x) ^ (3 * k) = (((x ^ 3 : ↥L₁)) : H) := by
      have h1 := congrArg (fun z : ↥L₁ => f z) hk
      simp only [map_zpow, map_pow, f, MonoidHom.comp_apply, MulEquiv.apply_symm_apply] at h1
      have h2 : L₂.subtype (φ.toMonoidHom (φ.symm ⟨(((x ^ 3 : ↥L₁)) : H), hωL⟩)) =
          (((x ^ 3 : ↥L₁)) : H) := by simp
      rw [h2] at h1
      rw [zpow_mul, zpow_ofNat]
      exact h1
    set y : H := (x : H) * (f x) ^ (-k) with hy
    have hxx₂ : Commute (x : H) (f x) := hc _ x.2 _ (hfL x)
    have hy3 : y ^ 3 = 1 := by
      rw [hy, (hxx₂.zpow_right (-k)).mul_pow]
      have h3 : ((f x) ^ (-k)) ^ 3 = ((f x) ^ (3 * k))⁻¹ := by
        rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
        congr 1
        push_cast
        ring
      rw [h3, hk', ← SubgroupClass.coe_pow]
      exact mul_inv_cancel _
    have hyL : y ∉ L₂ := by
      intro hy2
      have hxL₂ : (x : H) ∈ L₂ := by
        have h4 : (x : H) = y * (f x) ^ k := by
          rw [hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
        rw [h4]
        exact L₂.mul_mem hy2 (L₂.zpow_mem (hfL x) k)
      exact hx3 (hcube x (mem_center_of_mem_commuting hc hxL₂))
    have hyt : Commute y (t : H) :=
      Commute.mul_left (congrArg Subtype.val hxt.eq)
        ((hc _ t.2 _ (hfL x)).symm.zpow_left (-k))
    have hyF : ∀ g ∈ F₂, Commute y g := fun g hg =>
      Commute.mul_left (hc _ x.2 g (hF₂L hg)) ((hF₂x g hg).symm.zpow_left (-k))
    exact false_of_extra_element he hc t.2 ht2H ht1H hF₂ hF₂c hF₂L hy3 hyL hyt hyF
  · refine false_of_extra_element he hc t.2 ht2H ht1H hF₂ hF₂c hF₂L hω3H hωL ?_ ?_
    · exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx3c t)).symm
    · intro g hg
      exact hc _ (x ^ 3 : ↥L₁).2 g (hF₂L hg)

end Torus

section SU38

open CFSG.RankThree.PartTwo.Census Matrix

theorem exists_torus_data_su_three_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) :
    ∃ x t e : StatedSU 3 (2 ^ 3) K, t ^ 2 = 1 ∧ t ≠ 1 ∧ Commute x t ∧ Commute x e ∧ e ^ 3 = 1 ∧
      x ^ 3 ∈ Subgroup.center (StatedSU 3 (2 ^ 3) K) ∧ x ^ 3 ≠ 1 ∧ e ∉ zpowers (x ^ 3) := by
  have hU : UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  have hcard : Nat.card Kˣ = 63 := by
    rw [Nat.card_units, hK]
    norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [hcard] at hg
  set ζ : Kˣ := g ^ 7 with hζdef
  have hζ : orderOf ζ = 9 := by
    rw [hζdef, orderOf_pow_of_dvd (by norm_num) (by rw [hg]; norm_num), hg]
  have hζ9 : ζ ^ 9 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hζ3 : ζ ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at this
    omega
  have hq : (2 ^ 3 : ℕ) ≠ 0 := by norm_num
  set d : Fin 3 → Kˣ := ![ζ, ζ, ζ⁻¹ ^ 2] with hd
  have hprod : ∏ i, d i = 1 := by
    rw [Fin.prod_univ_three]
    simp only [hd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← pow_two, ← mul_pow, mul_inv_cancel, one_pow]
  have hd9 : d ^ (2 ^ 3 + 1) = 1 := by
    funext i
    fin_cases i <;> simp [hd, Pi.pow_apply]
    · exact hζ9
    · exact hζ9
    · rw [← pow_mul, show 2 * 9 = 9 * 2 from rfl, pow_mul, hζ9, one_pow]
  set d' : Fin 3 → Kˣ := ![1, ζ ^ 3, (ζ ^ 3)⁻¹] with hd'
  have hprod' : ∏ i, d' i = 1 := by
    rw [Fin.prod_univ_three]
    simp [hd']
  have hζ27 : (ζ ^ 3) ^ 9 = 1 := by
    rw [← pow_mul, show 3 * 9 = 9 * 3 from rfl, pow_mul, hζ9, one_pow]
  have hd9' : d' ^ (2 ^ 3 + 1) = 1 := by
    funext i
    fin_cases i <;> simp [hd', Pi.pow_apply, inv_pow]
    · exact hζ27
    · exact hζ27
  have hd3' : d' ^ 3 = 1 := by
    funext i
    fin_cases i <;> simp [hd', Pi.pow_apply, inv_pow]
    · rw [← pow_mul, show 3 * 3 = 9 from rfl, hζ9]
    · rw [← pow_mul, show 3 * 3 = 9 from rfl, hζ9]
  set x : StatedSU 3 (2 ^ 3) K := ⟨torusDiag d, torusDiag_mem_SU hq hprod hd9⟩
  set e : StatedSU 3 (2 ^ 3) K := ⟨torusDiag d', torusDiag_mem_SU hq hprod' hd9'⟩
  set t : StatedSU 3 (2 ^ 3) K := ⟨swapGL (K := K) (by norm_num), swapGL_mem_statedSU hU _⟩
  have hd01 : ∀ i j : Fin 3, i.val < 2 → j.val < 2 → ((d i : Kˣ) : K) = ((d j : Kˣ) : K) := by
    intro i j hi hj
    fin_cases i <;> fin_cases j <;> simp_all
  have hxt : x * t = t * x := Subtype.ext (Units.ext (by
    change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * (1 + swapBlock 3 K) =
      (1 + swapBlock 3 K) * (torusDiag d : Matrix (Fin 3) (Fin 3) K)
    rw [coe_torusDiag]
    exact diagonal_mul_swap hd01))
  have ht2 : t ^ 2 = 1 := Subtype.ext (Units.ext (by
    rw [pow_two]
    change (1 + swapBlock 3 K) * (1 + swapBlock 3 K) = 1
    exact one_add_mul_one_add (swapBlock_mul_self (by norm_num))))
  have hinv : ((ζ ^ 2) ^ 3)⁻¹ = ζ ^ 3 := by
    rw [← pow_mul]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hζ9)
  have hd3 : d ^ 3 = fun _ => ζ ^ 3 := by
    funext i
    fin_cases i <;> simp [hd, Pi.pow_apply, hinv]
  set T := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ 3) K)
  have hx3 : x ^ 3 ∈ T := by
    rw [Subgroup.mem_subgroupOf]
    refine ⟨ζ ^ 3, Units.ext ?_⟩
    rw [Matrix.GeneralLinearGroup.coe_scalar]
    change Matrix.scalar (Fin 3) ((ζ ^ 3 : Kˣ) : K) =
      ((torusDiag d ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← map_pow, hd3, coe_torusDiag]
    rfl
  have hscal : ∀ y : StatedSU 3 (2 ^ 3) K, y ∈ T →
      ∃ c : K, ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c :=
    fun y hy => by
      obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hy
      exact ⟨c, by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]⟩
  have htT : t ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal t h
    change 1 + swapBlock 3 K = _ at hc
    have h01 := congrFun (congrFun hc 0) 1
    simp [swapBlock, Matrix.scalar_apply] at h01
  have heT : e ∉ T := fun h => by
    obtain ⟨c, hc⟩ := hscal e h
    change (torusDiag d' : Matrix (Fin 3) (Fin 3) K) = _ at hc
    rw [coe_torusDiag] at hc
    have h0 := congrFun (congrFun hc 0) 0
    have h1 := congrFun (congrFun hc 1) 1
    simp only [diagonal_apply_eq, Matrix.scalar_apply] at h0 h1
    apply hζ3
    apply Units.ext
    simpa [hd'] using h1.trans h0.symm
  refine ⟨x, t, e, ht2, fun h => htT (h ▸ T.one_mem), hxt, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subtype.ext (Units.ext (by
      change (torusDiag d : Matrix (Fin 3) (Fin 3) K) * torusDiag d' =
        (torusDiag d' : Matrix (Fin 3) (Fin 3) K) * torusDiag d
      rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_comm]))
  · refine Subtype.ext (Units.ext ?_)
    change ((torusDiag d' ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
    rw [← map_pow, hd3', map_one]
    rfl
  · exact CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (2 ^ 3) hx3
  · intro h
    have h1 := congrArg (fun y : StatedSU 3 (2 ^ 3) K => (y : GL (Fin 3) K)) h
    change torusDiag d ^ 3 = 1 at h1
    rw [← map_pow, ← map_one (torusDiag (K := K) (ι := Fin 3))] at h1
    have h2 := congrFun (torusDiag_injective h1) 0
    rw [hd3] at h2
    exact hζ3 h2
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    apply heT
    rw [← hm]
    exact T.zpow_mem hx3 m

end SU38

section Covers

open CFSG.RankThree.PerfectCover

theorem exists_mulEquiv_of_central_covers {S E₁ E₂ : Type} [Group S] [Finite S]
    [Group.IsPerfect S] [Group E₁] [Finite E₁] [Group.IsPerfect E₁] [Group E₂] [Finite E₂]
    [Group.IsPerfect E₂] (hM : Nat.card (hopfMultiplier S) ∣ 3) (p₁ : E₁ →* S)
    (hp₁ : Function.Surjective p₁) (hc₁ : p₁.ker ≤ center E₁) (h₁ : Nat.card p₁.ker = 3)
    (p₂ : E₂ →* S) (hp₂ : Function.Surjective p₂) (hc₂ : p₂.ker ≤ center E₂)
    (h₂ : Nat.card p₂.ker = 3) : Nonempty (E₁ ≃* E₂) := by
  have key : ∀ {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (p : E →* S),
      Function.Surjective p → p.ker ≤ center E → Nat.card p.ker = 3 →
      Nonempty (HopfCover S ≃* E) := by
    intro E _ _ _ p hp hc hcard
    obtain ⟨-, h, hh, -, hsurj, hmap, -⟩ :=
      perfect_central_kernel_quotient_of_hopf_multiplier p hp hc
    refine ⟨MulEquiv.ofBijective h ⟨?_, hsurj⟩⟩
    have hMc : Nat.card (hopfMultiplier S) = 3 := by
      refine Nat.dvd_antisymm hM ?_
      have := Subgroup.card_map_dvd (H := hopfMultiplier S) h
      rwa [hmap, hcard] at this
    rw [injective_iff_map_eq_one]
    intro u hu
    have huM : u ∈ hopfMultiplier S := by
      change hopfCoverMap S u = 1
      rw [← hh, MonoidHom.comp_apply, hu, map_one]
    set f : ↥(hopfMultiplier S) →* E := h.comp (hopfMultiplier S).subtype with hf
    have hrange : f.range = p.ker := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
    have hker : f.ker = ⊥ := by
      have h1 : Nat.card ↥(hopfMultiplier S) = Nat.card (↥(hopfMultiplier S) ⧸ f.ker) *
          Nat.card f.ker := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hcard,
        hMc] at h1
      have : Nat.card f.ker = 1 := by omega
      exact Subgroup.eq_bot_of_card_eq _ this
    have : (⟨u, huM⟩ : ↥(hopfMultiplier S)) ∈ f.ker := hu
    rw [hker, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨e₁⟩ := key p₁ hp₁ hc₁ h₁
  obtain ⟨e₂⟩ := key p₂ hp₂ hc₂ h₂
  exact ⟨e₁.symm.trans e₂⟩

theorem card_center_dvd_card_hopfMultiplier_quotient {Q : Type} [Group Q] [Group.IsPerfect Q] :
    Nat.card (center Q) ∣ Nat.card (hopfMultiplier (Q ⧸ center Q)) := by
  have hker : (QuotientGroup.mk' (center Q)).ker = center Q := QuotientGroup.ker_mk' _
  have hmap := map_hopfMultiplier_hopfLift (QuotientGroup.mk' (center Q))
    (QuotientGroup.mk'_surjective _) hker.le
  have h := Subgroup.card_map_dvd (H := hopfMultiplier (Q ⧸ center Q))
    (hopfLift (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _) hker.le)
  rw [hmap, hker] at h
  exact h

end Covers

section Core

open CFSG.RankThree.PerfectCover CFSG.LieType.Universal.Unitary
  CFSG.Open.StatedCenterThree

variable {H : Type} [Group H] [Finite H]

theorem false_of_components_psu_three_eight_of_multiplier (he : CFSG.Open.evenRank H ≤ 2)
    {L₁ L₂ : Subgroup H} (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, Commute a b) (φ : ↥L₁ ≃* ↥L₂)
    (hq : CFSG.IsQuasisimple ↥L₁) (hm : StatedClassicalModel (↥L₁ ⧸ center ↥L₁) .PSU 3 2 3)
    (hM : Nat.card (hopfMultiplier (↥L₁ ⧸ center ↥L₁)) ∣ 3) (h3 : 3 ∣ Nat.card (center ↥L₁)) :
    False := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥L₁ := hq.1
  have hperfS : Group.IsPerfect (↥L₁ ⧸ center ↥L₁) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hZ : Nat.card (center ↥L₁) = 3 :=
    Nat.dvd_antisymm ((card_center_dvd_card_hopfMultiplier_quotient).trans hM) h3
  obtain ⟨hqSU, hcenSU⟩ :=
    isQuasisimple_statedSU_of_card (n := 3) hK (by norm_num) (by norm_num)
  have hSUperf : Group.IsPerfect (StatedSU 3 (2 ^ 3) K) := hqSU.1
  set T := (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ 3) K) with hT
  set p₂ : StatedSU 3 (2 ^ 3) K →* ↥L₁ ⧸ center ↥L₁ :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' T) with hp₂def
  have hp₂ : Function.Surjective p₂ := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₂ : p₂.ker = T := by
    ext y
    rw [MonoidHom.mem_ker, hp₂def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hc₂ : p₂.ker ≤ center (StatedSU 3 (2 ^ 3) K) := hker₂.le.trans hcenSU.symm.le
  have h₂ : Nat.card p₂.ker = 3 := by
    rw [hker₂, ← hcenSU]
    exact card_center_statedSU_three hK (by norm_num)
  obtain ⟨ψ⟩ := exists_mulEquiv_of_central_covers hM (QuotientGroup.mk' (center ↥L₁))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    (by rw [QuotientGroup.ker_mk']; exact hZ) p₂ hp₂ hc₂ h₂
  obtain ⟨x, t, e', ht2, ht1, hxt, hxe, he3, hx3c, hx3, hexω⟩ :=
    exists_torus_data_su_three_eight hK
  refine false_of_pair_torus_data he hc φ hZ (x := ψ.symm x) (t := ψ.symm t) (e := ψ.symm e')
    ?_ ?_ (hxt.map ψ.symm) (hxe.map ψ.symm) ?_ ?_ ?_ ?_
  · rw [← map_pow, ht2, map_one]
  · exact fun h => ht1 (ψ.symm.injective (by rw [h, map_one]))
  · rw [← map_pow, he3, map_one]
  · rw [← map_pow]
    exact Subgroup.mem_center_iff.2 fun g => ψ.injective (by
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.1 hx3c (ψ g))
  · exact fun h => hx3 (ψ.symm.injective (by rw [map_pow, h, map_one]))
  · intro h
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
    refine hexω (Subgroup.mem_zpowers_iff.mpr ⟨m, ψ.symm.injective ?_⟩)
    rw [map_zpow, map_pow]
    exact hm

end Core

end CFSG.SectionRank.QTK.CentreFact.LayerPair
