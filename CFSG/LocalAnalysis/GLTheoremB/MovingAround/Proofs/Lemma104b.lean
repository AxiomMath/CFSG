module

public import CFSG.LocalAnalysis.GLTheoremB.NormalPlane
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13Small

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Iii

variable {G : Type} [Group G] [Finite G]

private theorem rank_ge_of_card {p : ℕ} [Fact p.Prime] {E : Subgroup G} (hE : IsElemAbelian p E)
    {k : ℕ} (hk : p ^ k ≤ Nat.card E) : k ≤ CFSG.Open.pRank p E := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Nat.card E = p ^ r :=
    exists_card_eq_pow (fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩)
  rw [hr] at hk
  have hkr : k ≤ r := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hk
  exact hkr.trans (CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt le_rfl hE hr)

private theorem exists_isSCp_top_above {p : ℕ} {Y : Subgroup G} (hY : IsElemAbelian p Y) :
    ∃ H : Subgroup G, IsSCp p ⊤ H ∧ Y ≤ H := by
  obtain ⟨H, hYH, hHmax⟩ :=
    (Set.toFinite {X : Subgroup G | IsElemAbelian p X}).exists_le_maximal
      (show Y ∈ {X : Subgroup G | IsElemAbelian p X} from hY)
  refine ⟨H, ⟨le_top, hHmax.1, fun E _ hE hHE => le_antisymm (hHmax.2 hE hHE) hHE⟩, hYH⟩

private theorem inD_of_meet {p : ℕ} (hp : p.Prime) {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {F F' : Subgroup G} (hF : inD p M F) (hF' : IsSCp p ⊤ F')
    (hk : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p (F ⊓ F')) : inD p M F' := by
  have hp1 : 1 < p := hp.one_lt
  have h2k : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hEA.1.2.2
  have hF'le : F' ≤ M := by
    have hcent : F' ≤ Subgroup.centralizer ((F ⊓ F' : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hd' : d ∈ F' := (Subgroup.mem_inf.1 hd).2
      exact (elemAbelian_comm hF'.2.1 hx hd').symm
    have hnorm : F' ≤ Subgroup.normalizer ((F ⊓ F' : Subgroup G) : Set G) :=
      hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hrank2 : 2 ≤ CFSG.Open.pRank p (F ⊓ F') := by omega
    have hGL : Subgroup.normalizer ((F ⊓ F' : Subgroup G) : Set G) ≤ GLBCore p 2 F :=
      le_sSup ⟨F ⊓ F', inf_le_left, hrank2, rfl⟩
    exact hnorm.trans (hGL.trans hF.2.clause_d)
  have hF'sc : IsSCp p M F' := ⟨hF'le, hF'.2.1, fun E' _ hE' hF'E' => hF'.2.2 E' le_top hE' hF'E'⟩
  have hF'rank : 3 ≤ CFSG.Open.pRank p F' := by
    have := CFSG.SectionRank.pRank_mono hp1 (inf_le_right : F ⊓ F' ≤ F')
    omega
  by_cases hu : IsUniquenessTwoLocal p F' M
  · exact ⟨⟨hF'sc, hF'rank⟩, hu⟩
  · exfalso
    have hdd : inDDp p M F F' :=
      ⟨hF, ⟨⟨hF'sc, hF'rank⟩, hu⟩, by omega⟩
    have hle := hEA.2 F F' hdd
    unfold ddKey at hle
    have hle' : CFSG.Open.pRank p (F ⊓ F') ≤ CFSG.Open.pRank p (E ⊓ A) := by
      rcases Prod.Lex.toLex_le_toLex.mp hle with h1 | h1
      · exact h1.le
      · exact h1.1.le
    omega

private theorem good_of_commute {p : ℕ} (hp : p.Prime) {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {Y Z : Subgroup G} (hY : IsElemAbelian p Y) (hZ : IsElemAbelian p Z)
    (hYZ : Y ≤ Subgroup.centralizer (Z : Set G))
    (hYr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p Y)
    (hZgood : ∀ H : Subgroup G, IsSCp p ⊤ H → Z ≤ H → inD p M H) :
    ∀ H : Subgroup G, IsSCp p ⊤ H → Y ≤ H → inD p M H := by
  intro H hH hYH
  obtain ⟨H', hH'sc, hYZH'⟩ := exists_isSCp_top_above (isElemAbelian_sup_of_commute hY hZ hYZ)
  have hH'D : inD p M H' := hZgood H' hH'sc (le_sup_right.trans hYZH')
  refine inD_of_meet hp hEA hH'D hH ?_
  have hYle : Y ≤ H' ⊓ H := le_inf (le_sup_left.trans hYZH') hYH
  exact hYr.trans (CFSG.SectionRank.pRank_mono hp.one_lt hYle)

end Iii

theorem lemma104_iii_holds : Lemma104_iiiStatement := by
  intro G _ _ m p B M h E A hEA Es E0 hEs hE0 hconn
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hEsab, hEscard, -, hE0ab, hE0card, hchain⟩ := hconn
  have hE0r : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p E0 :=
    rank_ge_of_card hE0ab hE0card
  have hEsr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p Es :=
    rank_ge_of_card hEsab hEscard
  have hgood0 : ∀ H : Subgroup G, IsSCp p ⊤ H → E0 ≤ H → inD p M H := by
    intro H hH hE0H
    refine inD_of_meet hp hEA hE0 hH ?_
    rw [inf_eq_left.2 hE0H]
    exact hE0r
  rcases hchain with hcomm | ⟨U, V, hU, hV, hEsU, hrefl, hVE0⟩
  ·
    exact good_of_commute hp hEA hEsab hE0ab hcomm hEsr (fun H hH hE0H => hgood0 H hH hE0H)
      Es hEs le_rfl
  ·
    have hVab : IsElemAbelian p V := hV.2.1
    have hVr : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p V :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hV.2.1 hV.2.2
    have hgoodV : ∀ H : Subgroup G, IsSCp p ⊤ H → V ≤ H → inD p M H :=
      good_of_commute hp hEA hVab hE0ab hVE0 hVr (fun H hH hE0H => hgood0 H hH hE0H)
    have hgoodU : ∀ a : Subgroup G,
        Relation.ReflTransGen (IsKConnStep p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤) a V →
        ∀ H : Subgroup G, IsSCp p ⊤ H → a ≤ H → inD p M H := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact hgoodV
      | @head x y hac _ ih =>
        have har : CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p x :=
          CFSG.SectionRank.le_pRank hp.one_lt le_rfl hac.1.2.1 hac.1.2.2
        exact good_of_commute hp hEA hac.1.2.1 hac.2.1.2.1 hac.2.2 har ih
    exact good_of_commute hp hEA hEsab hU.2.1 hEsU hEsr (fun H hH hUH => hgoodU U hrefl H hH hUH)
      Es hEs le_rfl

section Chains

variable {G : Type} [Group G] [Finite G]

private theorem good_of_rtg {p : ℕ} (hp : p.Prime) {M E A : Subgroup G} (hEA : IsDDpStar p M E A)
    {r : Subgroup G → Subgroup G → Prop}
    (hr : ∀ a c : Subgroup G, r a c → IsElemAbelian p a ∧ IsElemAbelian p c ∧
      a ≤ Subgroup.centralizer (c : Set G) ∧
      CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p a ∧
      CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p c)
    {V : Subgroup G} (hV : ∀ H : Subgroup G, IsSCp p ⊤ H → V ≤ H → inD p M H) :
    ∀ a : Subgroup G, Relation.ReflTransGen r a V →
      ∀ H : Subgroup G, IsSCp p ⊤ H → a ≤ H → inD p M H := by
  intro a ha
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl => exact hV
  | @head x y hxy _ ih =>
    obtain ⟨h1, h2, h3, h4, -⟩ := hr x y hxy
    exact good_of_commute hp hEA h1 h2 h3 h4 ih

private theorem card_gLBConj (y : G) (H : Subgroup G) : Nat.card (GLBConj y H) = Nat.card H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective

private theorem gLBConj_fix_of_mem {M : Subgroup G} {y : G} (hy : y ∈ M) : GLBConj y M = M :=
  gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)

private theorem gLBConj_le_of_mem {M H : Subgroup G} {y : G} (hy : y ∈ M) (hH : H ≤ M) :
    GLBConj y H ≤ M := by
  calc GLBConj y H ≤ GLBConj y M := gLBConj_mono y hH
    _ = M := gLBConj_fix_of_mem hy

private theorem isSCp_gLBConj_of_mem' {p : ℕ} {M A : Subgroup G} {y : G} (hy : y ∈ M)
    (hA : IsSCp p M A) : IsSCp p M (GLBConj y A) := by
  refine ⟨gLBConj_le_of_mem hy hA.1, CFSG.SectionRank.isElemAbelian_map hA.2.1 _, ?_⟩
  intro E hEM hE hAE
  have hE' : GLBConj y⁻¹ E ≤ M := gLBConj_le_of_mem (M.inv_mem hy) hEM
  have hA' : A ≤ GLBConj y⁻¹ E := by
    have h := gLBConj_mono y⁻¹ hAE
    rwa [gLBConj_inv_gLBConj] at h
  have heq : GLBConj y⁻¹ E = A :=
    hA.2.2 _ hE' (CFSG.SectionRank.isElemAbelian_map hE _) hA'
  calc E = GLBConj y (GLBConj y⁻¹ E) := (gLBConj_gLBConj_inv y E).symm
    _ = GLBConj y A := by rw [heq]

private theorem inD_gLBConj_of_mem {p : ℕ} (hp : 1 < p) {M B : Subgroup G} {y : G} (hy : y ∈ M)
    (hconj : IsUniquenessTwoLocal_conjStatement) (hB : inD p M B) :
    inD p M (GLBConj y B) := by
  refine ⟨⟨isSCp_gLBConj_of_mem' hy hB.1.1, ?_⟩, hconj hB.2 hy⟩
  exact hB.1.2.trans
    (CFSG.SectionRank.pRank_le_map hp (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective B)

end Chains

section Plane

variable {G : Type} [Group G] [Finite G]

private theorem exists_centralizing_of_plane {p : ℕ} [Fact p.Prime] {B U : Subgroup G}
    (hBp : IsPGroup p ↥B) (hBe : IsElemAbelian p B) {m : ℕ} (hBcard : Nat.card B = p ^ m)
    (hm : 4 ≤ m) (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (hUe : IsElemAbelian p U)
    (hUc : Nat.card U = p ^ 2) :
    ∃ W : Subgroup G, W ≤ B ∧ IsElemAbelian p W ∧ Nat.card W = p ^ 3 ∧
      ∀ w ∈ W, ∀ u ∈ U, w * u = u * w := by
  have hp : p.Prime := Fact.out
  letI act : MulAction ↥B ↥U :=
    { smul := fun b u => ⟨(b : G) * (u : G) * (b : G)⁻¹, hUB b b.2 u u.2⟩
      one_smul := fun u => Subtype.ext (by
        show ((1 : ↥B) : G) * (u : G) * ((1 : ↥B) : G)⁻¹ = (u : G)
        simp)
      mul_smul := fun a b u => Subtype.ext (by
        show ((a * b : ↥B) : G) * (u : G) * ((a * b : ↥B) : G)⁻¹ =
          (a : G) * ((b : G) * (u : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp only [Subgroup.coe_mul]
        group) }
  have hfix_dvd : p ∣ Nat.card (MulAction.fixedPoints ↥B ↥U) := by
    have h1 : Nat.card ↥U ≡ Nat.card (MulAction.fixedPoints ↥B ↥U) [MOD p] :=
      hBp.card_modEq_card_fixedPoints ↥U
    rw [hUc] at h1
    exact Nat.modEq_zero_iff_dvd.1
      (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 (dvd_pow_self p two_ne_zero)))
  obtain ⟨u0, hu0fix, hu0ne⟩ : ∃ u0 : ↥U, u0 ∈ MulAction.fixedPoints ↥B ↥U ∧ u0 ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : MulAction.fixedPoints ↥B ↥U ⊆ {1} := fun x hx => hcon x hx
    have h1mem : (1 : ↥U) ∈ MulAction.fixedPoints ↥B ↥U := by
      rw [MulAction.mem_fixedPoints]
      intro b
      exact Subtype.ext (show (b : G) * ((1 : ↥U) : G) * (b : G)⁻¹ = ((1 : ↥U) : G) by simp)
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥B ↥U) :=
      Nat.card_pos_iff.2 ⟨⟨⟨1, h1mem⟩⟩, Set.toFinite _⟩
    have hle : Nat.card (MulAction.fixedPoints ↥B ↥U) ≤ 1 := by
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_singleton] at this
      rwa [Nat.card_coe_set_eq]
    have := Nat.le_of_dvd hpos hfix_dvd
    have := hp.two_le
    omega
  have hu0B : ∀ b ∈ B, b * (u0 : G) * b⁻¹ = (u0 : G) := by
    intro b hb
    have h1 := MulAction.mem_fixedPoints.1 hu0fix ⟨b, hb⟩
    have h2 : (b : G) * (u0 : G) * (b : G)⁻¹ = (u0 : G) := congrArg Subtype.val h1
    exact h2
  have hu0ord : orderOf (u0 : G) = p :=
    orderOf_eq_prime (hUe.2 _ u0.2) (fun h => hu0ne (Subtype.ext h))
  obtain ⟨u1, hu1U, hu1n⟩ : ∃ u1 ∈ U, u1 ∉ Subgroup.zpowers (u0 : G) := by
    by_contra hcon
    push_neg at hcon
    have h1 := Subgroup.card_le_of_le
      (show U ≤ Subgroup.zpowers (u0 : G) from fun u hu => hcon u hu)
    rw [hUc, Nat.card_zpowers, hu0ord] at h1
    have := hp.two_le
    nlinarith
  have hu1ne : u1 ≠ 1 := fun h => hu1n (h ▸ Subgroup.one_mem _)
  set u1' : ↥U := ⟨u1, hu1U⟩ with hu1'
  have horb_ne : MulAction.orbit ↥B u1' ≠ Set.univ := by
    intro huniv
    have h1 : (1 : ↥U) ∈ MulAction.orbit ↥B u1' := by
      rw [huniv]; exact Set.mem_univ _
    obtain ⟨b, hb⟩ := h1
    apply hu1ne
    have h2 : (b : G) * u1 * (b : G)⁻¹ = 1 := congrArg Subtype.val hb
    calc u1 = (b : G)⁻¹ * ((b : G) * u1 * (b : G)⁻¹) * (b : G) := by group
      _ = 1 := by rw [h2]; group
  have horb_lt : (MulAction.orbit ↥B u1').ncard < Nat.card ↥U := Set.ncard_lt_card horb_ne
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card (MulAction.orbit ↥B u1') = p ^ n := hBp.card_orbit u1'
  have hn1 : n ≤ 1 := by
    rw [← Nat.card_coe_set_eq, hn, hUc] at horb_lt
    have : n < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).1 horb_lt
    omega
  have hidx : (MulAction.stabilizer ↥B u1').index = Nat.card (MulAction.orbit ↥B u1') := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  have hcard_stab : Nat.card (MulAction.stabilizer ↥B u1') * p ^ n = p ^ m := by
    rw [← hn, ← hidx, Subgroup.card_mul_index, hBcard]
  have hS3 : p ^ 3 ≤ Nat.card (MulAction.stabilizer ↥B u1') := by
    have h1 : p ^ m ≤ Nat.card (MulAction.stabilizer ↥B u1') * p := by
      rw [← hcard_stab]
      have hpn : p ^ n ≤ p := by simpa using Nat.pow_le_pow_right hp.pos hn1
      exact Nat.mul_le_mul_left _ hpn
    have h2 : p ^ 4 ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
    have h3 : p ^ 3 * p ≤ Nat.card (MulAction.stabilizer ↥B u1') * p := by
      have : p ^ 3 * p = p ^ 4 := by ring
      omega
    exact Nat.le_of_mul_le_mul_right h3 hp.pos
  set Wb : Subgroup G := (MulAction.stabilizer ↥B u1').map B.subtype with hWb
  have hWb_le : Wb ≤ B := Subgroup.map_subtype_le _
  have hWb_e : IsElemAbelian p Wb := isElemAbelian_mono hBe hWb_le
  have hWb_card : Nat.card Wb = Nat.card (MulAction.stabilizer ↥B u1') :=
    Subgroup.card_map_of_injective B.subtype_injective
  have hWb_dvd : p ^ 3 ∣ Nat.card Wb := by
    rw [hWb_card]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
      (⟨p ^ n, hcard_stab.symm⟩ : Nat.card (MulAction.stabilizer ↥B u1') ∣ p ^ m)
    have hj3 : 3 ≤ j := by
      have : p ^ 3 ≤ p ^ j := by rw [← hj]; exact hS3
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 this
    rw [hj]
    exact pow_dvd_pow p hj3
  obtain ⟨W, hWWb, hWe, hWc⟩ := exists_le_isElemAbelian_card hWb_e hWb_dvd
  have hUgen : ∀ u ∈ U, u ∈ Subgroup.closure ({(u0 : G), u1} : Set G) := by
    set V : Subgroup G := Subgroup.closure ({(u0 : G), u1} : Set G) with hV
    have hVU : V ≤ U := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact u0.2
      · exact hu1U
    have hz : Subgroup.zpowers (u0 : G) ≤ V :=
      Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
    have hu1V : u1 ∈ V := Subgroup.subset_closure (by simp)
    have hdvd : Nat.card V ∣ p ^ 2 := by
      rw [← hUc]; exact Subgroup.card_dvd_of_le hVU
    obtain ⟨j, hj2, hVj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hpV : p ∣ Nat.card V := by
      have := Subgroup.card_dvd_of_le hz
      rwa [Nat.card_zpowers, hu0ord] at this
    intro u hu
    interval_cases j
    · rw [pow_zero] at hVj
      rw [hVj] at hpV
      have := hp.two_le
      have := Nat.le_of_dvd one_pos hpV
      omega
    · exfalso
      rw [pow_one] at hVj
      have heq : Subgroup.zpowers (u0 : G) = V :=
        Subgroup.eq_of_le_of_card_ge hz (by rw [hVj, Nat.card_zpowers, hu0ord])
      exact hu1n (heq ▸ hu1V)
    · have heq : V = U := Subgroup.eq_of_le_of_card_ge hVU (by rw [hUc, hVj])
      rw [heq]
      exact hu
  refine ⟨W, hWWb.trans hWb_le, hWe, hWc, ?_⟩
  intro w hw u hu
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 (hWWb hw)
  have hb' := MulAction.mem_stabilizer_iff.1 hb
  have hbu1 : (b : G) * u1 * (b : G)⁻¹ = u1 := congrArg Subtype.val hb'
  have hc1 : (b : G) * u1 = u1 * (b : G) := by
    have := hbu1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hc0 : (b : G) * (u0 : G) = (u0 : G) * (b : G) := by
    have := hu0B (b : G) b.2
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcent : Subgroup.closure ({(u0 : G), u1} : Set G) ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with rfl | rfl
    · exact hc0.symm
    · exact hc1.symm
  have := Subgroup.mem_centralizer_singleton_iff.1 (hcent (hUgen u hu))
  exact this.symm

end Plane

section Sylow

variable {G : Type} [Group G] [Finite G]

private theorem exists_sylow_map_eq {p : ℕ} {Y X : Subgroup G} (hX : IsSylowIn p Y X) :
    ∃ S : Sylow p ↥Y, (S : Subgroup ↥Y).map Y.subtype = X := by
  have hXY : IsPGroup p ↥(X.subgroupOf Y) :=
    hX.2.1.comap_of_injective Y.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hXY
  refine ⟨S, ?_⟩
  have hmap : IsPGroup p ↥((S : Subgroup ↥Y).map Y.subtype) := S.isPGroup'.map Y.subtype
  have hle : X ≤ (S : Subgroup ↥Y).map Y.subtype := fun x hx =>
    ⟨⟨x, hX.1 hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  exact hX.2.2 _ (Subgroup.map_subtype_le _) hmap hle

private theorem isPGroup_gLBConj' {p : ℕ} {H : Subgroup G} (hH : IsPGroup p ↥H) (g : G) :
    IsPGroup p ↥(GLBConj g H) :=
  hH.map (MulAut.conj g⁻¹).toMonoidHom

private theorem isSylowIn_gLBConj' {p : ℕ} {P : Subgroup G} (hP : IsSylowIn p ⊤ P) (g : G) :
    IsSylowIn p ⊤ (GLBConj g P) := by
  refine ⟨le_top, isPGroup_gLBConj' hP.2.1 g, fun R' _ hR'p hR'le => ?_⟩
  have h1 : P ≤ GLBConj g⁻¹ R' := by
    have h := gLBConj_mono g⁻¹ hR'le
    rwa [gLBConj_inv_gLBConj] at h
  have h2 : GLBConj g⁻¹ R' = P := hP.2.2 _ le_top (isPGroup_gLBConj' hR'p g⁻¹) h1
  rw [← h2, gLBConj_gLBConj_inv]

private theorem isSylowIn_top_of_sylow_in {p : ℕ} [Fact p.Prime] {M P R : Subgroup G}
    (hPsyl : IsSylowIn p ⊤ P) (hPM : P ≤ M) (hR : IsSylowIn p M R) : IsSylowIn p ⊤ R := by
  have hPM' : IsSylowIn p M P :=
    ⟨hPM, hPsyl.2.1, fun R' _ hR'p hPR' => hPsyl.2.2 R' le_top hR'p hPR'⟩
  obtain ⟨SP, hSP⟩ := exists_sylow_map_eq hPM'
  obtain ⟨SR, hSR⟩ := exists_sylow_map_eq hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M SP SR
  have hRP : R = GLBConj (g : G)⁻¹ P := by
    ext x
    constructor
    · intro hx
      have hxM : x ∈ M := hR.1 hx
      have hkR : (⟨x, hxM⟩ : ↥M) ∈ (SR : Subgroup ↥M) := by
        rw [← hSR] at hx
        obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.1 hx
        have hk' : k = ⟨x, hxM⟩ := Subtype.ext hkx
        rw [← hk']
        exact hk
      rw [← hg, Sylow.coe_subgroup_smul] at hkR
      obtain ⟨s, hs, hsx⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hkR
      have hsP : (s : G) ∈ P := by
        rw [← hSP]
        exact Subgroup.mem_map.2 ⟨s, hs, rfl⟩
      have hxs : x = (g : G) * (s : G) * (g : G)⁻¹ := by
        have := congrArg Subtype.val hsx
        simpa [MulAut.conj_apply] using this.symm
      rw [mem_gLBConj, inv_inv, hxs]
      have : (g : G)⁻¹ * ((g : G) * (s : G) * (g : G)⁻¹) * (g : G) = (s : G) := by group
      rw [this]
      exact hsP
    · intro hx
      rw [mem_gLBConj, inv_inv] at hx
      have hxM : x ∈ M := by
        have h1 : x = (g : G) * ((g : G)⁻¹ * x * (g : G)) * (g : G)⁻¹ := by group
        rw [h1]
        exact M.mul_mem (M.mul_mem g.2 (hPM hx)) (M.inv_mem g.2)
      have hyP : (g : G)⁻¹ * x * (g : G) ∈ P := hx
      rw [← hSP] at hyP
      obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.1 hyP
      have hsR : MulAut.conj g • s ∈ (SR : Subgroup ↥M) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
      rw [← hSR]
      refine Subgroup.mem_map.2 ⟨MulAut.conj g • s, hsR, ?_⟩
      have hsy' : (s : G) = (g : G)⁻¹ * x * (g : G) := hsy
      show (g : G) * (s : G) * (g : G)⁻¹ = x
      rw [hsy']
      group
  rw [hRP]
  exact isSylowIn_gLBConj' hPsyl _

end Sylow

section Iv

variable {G : Type} [Group G] [Finite G]

theorem lemma104_iv_of (h102 : Lemma102Statement) (h31 : Input31_6)
    (hconj : IsUniquenessTwoLocal_conjStatement) : Lemma104_ivStatement := by
  intro G _ _ m p B M h E A hEA hk R hR
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hp2 : p ≠ 2 := hS.ne_two
  have hm4 : 4 ≤ m := hS.four_le
  have hB : IsBOneMax p B := h.bOne
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hBsc : IsSCp p ⊤ B := lemma23_proved G m p hS B hB
  have hBe : IsElemAbelian p B := hBsc.2.1
  have hBcard : Nat.card B = p ^ m := hS.card_eq hB
  have hBp : IsPGroup p ↥B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hBD : inD p M B := by
    refine ⟨⟨⟨hBM, hBe, fun E' _ hE' hBE' => hBsc.2.2 E' le_top hE' hBE'⟩, ?_⟩, h.uniq⟩
    have : m ≤ CFSG.Open.pRank p B := CFSG.SectionRank.le_pRank hp1 le_rfl hBe hBcard
    omega
  have hMtwo : CFSG.Open.IsTwoLocal M := h.pre.1.1
  have hMrank : ∀ X : Subgroup G, X ≤ M → CFSG.Open.pRank p X ≤ m := by
    intro X hXM
    have hbdd : BddAbove {k : ℕ | ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank p H = k} :=
      ⟨CFSG.Open.pRank p ⊤, by
        rintro k ⟨H, -, rfl⟩
        exact CFSG.SectionRank.pRank_mono hp1 le_top⟩
    have htlr : CFSG.Open.twoLocalPrimeRank p G = m := hS.rank_eq
    calc CFSG.Open.pRank p X ≤ CFSG.Open.pRank p M := CFSG.SectionRank.pRank_mono hp1 hXM
      _ ≤ CFSG.Open.twoLocalPrimeRank p G :=
          le_csSup hbdd ⟨M, hMtwo, rfl⟩
      _ = m := htlr
  obtain ⟨P, hPsyl, hBP⟩ : ∃ P : Subgroup G, IsSylowIn p ⊤ P ∧ B ≤ P := by
    obtain ⟨P, hBP, hPmax⟩ :=
      (Set.toFinite {X : Subgroup G | X ≤ ⊤ ∧ IsPGroup p ↥X}).exists_le_maximal
        (show B ∈ {X : Subgroup G | X ≤ ⊤ ∧ IsPGroup p ↥X} from ⟨le_top, hBp⟩)
    exact ⟨P, ⟨hPmax.1.1, hPmax.1.2, fun R' hR'G hR'p hPR' =>
      le_antisymm (hPmax.2 ⟨hR'G, hR'p⟩ hPR') hPR'⟩, hBP⟩
  have hPp : IsPGroup p ↥P := hPsyl.2.1
  have hPnc : ¬ IsCyclic ↥P := by
    intro hcyc
    have hBc : IsCyclic ↥(B.subgroupOf P) := inferInstance
    have hBc' : IsCyclic ↥B := by
      have e := Subgroup.subgroupOfEquivOfLe hBP
      exact isCyclic_of_surjective e.toMonoidHom e.surjective
    exact not_isCyclic_of_isElemAbelian hBe
      (by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega)) hBc'
  obtain ⟨U', hU'n, hU'e, hU'c⟩ := exists_normal_plane hp2 hPp hPnc
  set U : Subgroup G := U'.map P.subtype with hU
  have hUe : IsElemAbelian p U := CFSG.SectionRank.isElemAbelian_map hU'e P.subtype
  have hUc : Nat.card U = p ^ 2 := by
    rw [hU, Subgroup.card_map_of_injective P.subtype_injective]
    exact hU'c
  have hUP : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U := by
    intro x hx u hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hu
    have := hU'n.conj_mem a ha ⟨x, hx⟩
    exact Subgroup.mem_map.2 ⟨_, this, by simp⟩
  have hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U := fun b hb u hu => hUP b (hBP hb) u hu
  obtain ⟨W, hWB, hWe, hWc, hWcomm⟩ := exists_centralizing_of_plane hBp hBe hBcard hm4 hUB hUe hUc
  have hUW : U ≤ Subgroup.centralizer (W : Set G) := fun u hu =>
    Subgroup.mem_centralizer_iff.2 (fun w hw => hWcomm w hw u hu)
  have hUWe : IsElemAbelian p (U ⊔ W) := isElemAbelian_sup_of_commute hUe hWe hUW
  obtain ⟨Es, hEs, hUWEs⟩ := exists_isSCp_top_above hUWe
  have hWEs : W ≤ Es := le_sup_right.trans hUWEs
  have hUEs : U ≤ Es := le_sup_left.trans hUWEs
  have hconn : IsKConnectedIn p (CFSG.Open.pRank p (E ⊓ A) + 1) ⊤ Es B := by
    rw [hk]
    refine ⟨le_top, hEs.2.1, ?_, le_top, hBe, ?_,
      Or.inr ⟨W, W, ⟨le_top, hWe, hWc⟩, ⟨le_top, hWe, hWc⟩, ?_, Relation.ReflTransGen.refl, ?_⟩⟩
    · rw [show 2 + 1 = 3 from rfl, ← hWc]
      exact Subgroup.card_le_of_le hWEs
    · rw [show 2 + 1 = 3 from rfl, hBcard]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact elemAbelian_comm hEs.2.1 (hWEs hw) hx
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact elemAbelian_comm hBe hb (hWB hw)
  have hEsD : inD p M Es := lemma104_iii_holds h hEA hEs hBD hconn
  have hUrank : 2 ≤ CFSG.Open.pRank p U := CFSG.SectionRank.le_pRank hp1 le_rfl hUe hUc
  have hUM : Subgroup.normalizer (U : Set G) ≤ M := by
    have h2 : Subgroup.normalizer (U : Set G) ≤ GLBCore p 2 Es :=
      le_sSup ⟨U, hUEs, hUrank, rfl⟩
    exact h2.trans hEsD.2.clause_d
  have hPN : P ≤ Subgroup.normalizer (U : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hUP x hx u
    · intro hu
      have := hUP x⁻¹ (P.inv_mem hx) _ hu
      simpa [mul_assoc] using this
  have hPM : P ≤ M := hPN.trans hUM
  have hRG : IsSylowIn p ⊤ R := isSylowIn_top_of_sylow_in hPsyl hPM hR
  have hRM : R ≤ M := hR.1
  have hRp : IsPGroup p ↥R := hR.2.1
  have hE5claim : ∀ E5 : Subgroup G, IsEkIn p 5 R E5 → inD0 p M E5 := by
    intro E5 hE5
    have hE5M : E5 ≤ M := hE5.1.trans hRM
    have hE5r : 5 ≤ CFSG.Open.pRank p E5 :=
      CFSG.SectionRank.le_pRank hp1 le_rfl hE5.2.1 hE5.2.2
    have hm5 : 5 ≤ m := le_trans hE5r (hMrank E5 hE5M)
    obtain ⟨y, hyM, hyp⟩ := exists_conj_pGroup_aux hRM hRp hBM hBp
    have hByR : GLBConj y B ≤ R := by
      have hle : R ⊔ GLBConj y B = R :=
        hR.2.2 (R ⊔ GLBConj y B) (sup_le hRM (gLBConj_le_of_mem hyM hBM)) hyp le_sup_left
      exact le_sup_right.trans hle.le
    have hByD : inD p M (GLBConj y B) := inD_gLBConj_of_mem hp1 hyM hconj hBD
    have hByE : IsElemAbelian p (GLBConj y B) := CFSG.SectionRank.isElemAbelian_map hBe _
    have hByc : Nat.card (GLBConj y B) = p ^ m := by
      rw [card_gLBConj, hBcard]
    obtain ⟨B2, hB2le, hB2e, hB2c⟩ :=
      exists_le_isElemAbelian_card hByE (n := 5) (by rw [hByc]; exact pow_dvd_pow p hm5)
    have hB2R : IsEkIn p 5 R B2 := ⟨hB2le.trans hByR, hB2e, hB2c⟩
    have hGoodB2 : ∀ H : Subgroup G, IsSCp p ⊤ H → B2 ≤ H → inD p M H := by
      intro H hH hB2H
      refine inD_of_meet hp hEA hByD hH ?_
      have h1 : CFSG.Open.pRank p B2 ≤ CFSG.Open.pRank p (GLBConj y B ⊓ H) :=
        CFSG.SectionRank.pRank_mono hp1 (le_inf hB2le hB2H)
      have h2 : 5 ≤ CFSG.Open.pRank p B2 := CFSG.SectionRank.le_pRank hp1 le_rfl hB2e hB2c
      rw [hk]
      omega
    have hconn3 := (h31 G p hp hp2 R hRp).1 E5 B2 hE5 hB2R
    obtain ⟨-, -, -, -, -, -, hchain⟩ := hconn3
    have hgoodE5 : ∀ H : Subgroup G, IsSCp p ⊤ H → E5 ≤ H → inD p M H := by
      rcases hchain with hc | ⟨U3, V3, hU3, hV3, hE5U3, hrtg, hV3B2⟩
      · exact good_of_commute hp hEA hE5.2.1 hB2e hc (by rw [hk]; omega) hGoodB2
      · have hr : ∀ a c : Subgroup G, IsKConnStep p 3 R a c → IsElemAbelian p a ∧
            IsElemAbelian p c ∧ a ≤ Subgroup.centralizer (c : Set G) ∧
            CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p a ∧
            CFSG.Open.pRank p (E ⊓ A) + 1 ≤ CFSG.Open.pRank p c := by
          intro a c hac
          have ha3 : 3 ≤ CFSG.Open.pRank p a :=
            CFSG.SectionRank.le_pRank hp1 le_rfl hac.1.2.1 hac.1.2.2
          have hc3 : 3 ≤ CFSG.Open.pRank p c :=
            CFSG.SectionRank.le_pRank hp1 le_rfl hac.2.1.2.1 hac.2.1.2.2
          refine ⟨hac.1.2.1, hac.2.1.2.1, hac.2.2, ?_, ?_⟩ <;> (rw [hk]; omega)
        have hV3r : 3 ≤ CFSG.Open.pRank p V3 :=
          CFSG.SectionRank.le_pRank hp1 le_rfl hV3.2.1 hV3.2.2
        have hgoodV3 : ∀ H : Subgroup G, IsSCp p ⊤ H → V3 ≤ H → inD p M H := by
          refine good_of_commute hp hEA hV3.2.1 hB2e hV3B2 ?_ hGoodB2
          rw [hk]
          exact hV3r
        have hgoodU3 := good_of_rtg hp hEA hr hgoodV3 U3 hrtg
        exact good_of_commute hp hEA hE5.2.1 hU3.2.1 hE5U3 (by rw [hk]; omega) hgoodU3
    obtain ⟨H, hHsc, hE5H⟩ := exists_isSCp_top_above hE5.2.1
    exact ⟨hE5M, hE5.2.1, H, hgoodE5 H hHsc hE5H, hE5H⟩
  refine ⟨hE5claim, ?_, hRG⟩
  unfold GLBCore
  apply sSup_le
  rintro N ⟨Q, hQR, hQr, rfl⟩
  have hQM : Q ≤ M := hQR.trans hRM
  have hQp : IsPGroup p ↥Q := IsPGroup.to_le hRp hQR
  obtain ⟨E0', hE0'Q, hE0'e, hE0'c⟩ := CFSG.SectionRank.exists_pRank hp1 Q
  obtain ⟨E5', hE5'E0, hE5'e, hE5'c⟩ :=
    exists_le_isElemAbelian_card hE0'e (n := 5) (by rw [hE0'c]; exact pow_dvd_pow p hQr)
  exact h102 h hQM hQp (by norm_num : 2 ≤ 5) ⟨E5', hE5'E0.trans hE0'Q, hE5'e, hE5'c⟩
    (fun E hE => hE5claim E ⟨hE.1.trans hQR, hE.2.1, hE.2.2⟩)

end Iv

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
