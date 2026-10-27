module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.Translation
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.ElationGroup
public import CFSG.Geometry.GeneralizedQuadrangles.Whorls

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin
open CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V]
  [FaithfulSMul H V] [GraphAction H Γ]
variable [Fintype V] [DecidableRel Γ.Adj]

theorem natCard_symmetryGroup_eq_s (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L) {p L : V} (hp : c p = 0)
    (hpL : Γ.Adj p L) :
    Nat.card (symmetryGroup H Γ L) = s := by
  classical
  have hcL : c L = 1 := by
    have hne := c.valid hpL
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c L) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  obtain ⟨x, hLx, hxp, -⟩ := exists_adj_ne_two hT L p p
  exact card_symmetryGroup_eq_s hP hT hM c hdeg (hreg L hcL) hcL hLx hpL.symm hxp

theorem conj_mem_symmetryGroup_of_fix (hP : IsGeneralizedPolygon Γ 4) {M : V} {h : H}
    {θ : H} (hfix : h • M = M) (hθ : θ ∈ symmetryGroup H Γ M) :
    h * θ * h⁻¹ ∈ symmetryGroup H Γ M := by
  have hset : h • perpSet Γ M = perpSet Γ M := by
    rw [smul_perpSet hP.connected h M, hfix]
  have hmem := Set.conj_mem_fixingSubgroup (M := H) (g := h) (t := perpSet Γ M)
    (s := perpSet Γ M) hset hθ
  simpa [MulAut.conj_apply] using hmem

theorem translationGroup_le_normalizer_translationGroupMinus
    (hP : IsGeneralizedPolygon Γ 4) (p L₀ : V) :
    translationGroup H Γ p ≤
      Subgroup.normalizer (translationGroupMinus H Γ p L₀ : Set H) := by
  refine Subgroup.le_normalizer_closure_iff.mpr ?_
  intro h hh g hg
  obtain ⟨M, hpM, hML, hgM⟩ := hg
  have hfixM : h • M = M :=
    (mem_fixingSubgroup_iff H).mp (translationGroup_le_whorlGroup hP p hh) M hpM
  exact Subgroup.subset_closure ⟨M, hpM, hML, conj_mem_symmetryGroup_of_fix hP hfixM hgM⟩



theorem exists_fixed_third_of_prime_order {M x y : V} {θ : H} {q s : ℕ}
    (hxM : Γ.Adj M x) (hyM : Γ.Adj M y) (hxy : x ≠ y) (hMfix : θ • M = M)
    (hθx : θ • x = x) (hθy : θ • y = y) (hq : orderOf θ = q) (hqprime : q.Prime)
    (hcardM : Fintype.card ↥(Γ.neighborSet M) = s + 1) (hqs : q ∣ s) :
    ∃ z, Γ.Adj M z ∧ z ≠ x ∧ z ≠ y ∧ θ • z = z := by
  classical
  let σ : Equiv.Perm ↥(Γ.neighborSet M) :=
    { toFun := fun z => ⟨θ • (z : V), by
        have h := (GraphAction.adj_smul θ M (z : V)).mpr z.2
        rwa [hMfix] at h⟩
      invFun := fun z => ⟨θ⁻¹ • (z : V), by
        have hMinv : θ⁻¹ • M = M := by
          have h := congrArg (fun X => θ⁻¹ • X) hMfix
          rw [smul_smul, inv_mul_cancel, one_smul] at h
          exact h.symm
        have h := (GraphAction.adj_smul θ⁻¹ M (z : V)).mpr z.2
        rwa [hMinv] at h⟩
      left_inv := fun z => by ext; simp
      right_inv := fun z => by ext; simp }
  have hθq : θ ^ q = 1 := by
    simpa [hq] using pow_orderOf_eq_one θ
  have hσpow : ∀ n : ℕ, ∀ z : ↥(Γ.neighborSet M),
      ((σ ^ n) z : V) = (θ ^ n) • (z : V) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
        intro z
        rw [pow_succ']
        change θ • (((σ ^ n) z : V)) = (θ ^ (n + 1)) • (z : V)
        rw [ih z, ← mul_smul, ← pow_succ']
  have hσq : σ ^ q = 1 := by
    ext z
    rw [hσpow q z, hθq, one_smul]
    rfl
  have hxmem : (⟨x, hxM⟩ : ↥(Γ.neighborSet M)) ∈ Function.fixedPoints σ := by
    simp only [Function.mem_fixedPoints]
    apply Subtype.ext
    change θ • x = x
    exact hθx
  have hymem : (⟨y, hyM⟩ : ↥(Γ.neighborSet M)) ∈ Function.fixedPoints σ := by
    simp only [Function.mem_fixedPoints]
    apply Subtype.ext
    change θ • y = y
    exact hθy
  have hxyne : (⟨x, hxM⟩ : ↥(Γ.neighborSet M)) ≠ ⟨y, hyM⟩ := by
    intro h
    exact hxy (Subtype.ext_iff.mp h)
  let f : Fin 2 → Function.fixedPoints σ := fun i =>
    if i = 0 then ⟨⟨x, hxM⟩, hxmem⟩ else ⟨⟨y, hyM⟩, hymem⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, hxyne]
  have hfix2 : 2 ≤ Fintype.card (Function.fixedPoints σ) := by
    simpa using Fintype.card_le_of_injective f hfinj
  haveI : Fact q.Prime := ⟨hqprime⟩
  have hmod : Fintype.card (Function.fixedPoints σ) ≡ s + 1 [MOD q] := by
    have h := σ.card_compl_support_modEq (p := q) (n := 1) (by simpa using hσq)
    have hcompl : σ.supportᶜ.card = Fintype.card (Function.fixedPoints σ) := by
      have hset : σ.supportᶜ = (Function.fixedPoints σ).toFinset := by
        ext z
        simp only [Finset.mem_compl, Finset.mem_univ, true_and, Function.mem_fixedPoints,
          Function.IsFixedPt, Equiv.Perm.mem_support, Set.mem_toFinset, not_not]
      rw [hset, ← Set.ncard_eq_toFinset_card']
      exact (Set.fintypeCard_eq_ncard _).symm
    rw [hcompl, hcardM] at h
    exact h
  have hmod1 : Fintype.card (Function.fixedPoints σ) ≡ 1 [MOD q] := by
    have hs1 : s + 1 ≡ 1 [MOD q] :=
      ((Nat.modEq_iff_dvd' (by omega : 1 ≤ s + 1)).mpr (by simpa using hqs)).symm
    exact hmod.trans hs1
  have hne2 : Fintype.card (Function.fixedPoints σ) ≠ 2 := by
    intro h2
    have : (2 : ℕ) ≡ 1 [MOD q] := by rwa [h2] at hmod1
    have h12 : (1 : ℕ) ≡ 2 [MOD q] := this.symm
    have hq1 : q ∣ 1 := by
      have h := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp h12
      simpa using h
    exact hqprime.not_dvd_one hq1
  have hfix3 : 3 ≤ Fintype.card (Function.fixedPoints σ) := by omega
  let F : Finset ↥(Γ.neighborSet M) := (Function.fixedPoints σ).toFinset
  have hFcard : F.card = Fintype.card (Function.fixedPoints σ) := by
    rw [show F = (Function.fixedPoints σ).toFinset from rfl,
      ← Set.ncard_eq_toFinset_card']
    exact (Set.fintypeCard_eq_ncard _).symm
  have hxF : (⟨x, hxM⟩ : ↥(Γ.neighborSet M)) ∈ F := by
    rw [show F = (Function.fixedPoints σ).toFinset from rfl]
    simpa using hxmem
  have hyF : (⟨y, hyM⟩ : ↥(Γ.neighborSet M)) ∈ F := by
    rw [show F = (Function.fixedPoints σ).toFinset from rfl]
    simpa using hymem
  have hpos : 0 < ((F.erase ⟨x, hxM⟩).erase ⟨y, hyM⟩).card := by
    have h1 := Finset.pred_card_le_card_erase (s := F) (a := ⟨x, hxM⟩)
    have h2 := Finset.pred_card_le_card_erase
      (s := F.erase ⟨x, hxM⟩) (a := ⟨y, hyM⟩)
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  have hzy : z ≠ ⟨y, hyM⟩ := (Finset.mem_erase.mp hz).1
  have hzx : z ≠ ⟨x, hxM⟩ := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
  have hzF : z ∈ F := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
  have hzfix : σ z = z := by
    have h := hzF
    rw [show F = (Function.fixedPoints σ).toFinset from rfl] at h
    simpa [Function.mem_fixedPoints, Function.IsFixedPt] using h
  refine ⟨(z : V), z.2, ?_, ?_, ?_⟩
  · intro h
    exact hzx (Subtype.ext h)
  · intro h
    exact hzy (Subtype.ext h)
  · simpa [σ] using congrArg Subtype.val hzfix


theorem translationGroup_eq_translationGroupMinus
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L₀ : V} (hp : c p = 0) (hpL₀ : Γ.Adj p L₀) (h3 : 3 ≤ t) :
    translationGroup H Γ p = translationGroupMinus H Γ p L₀ := by
  classical
  haveI : Fintype H :=
    Fintype.ofInjective (MulAction.toPerm (α := H) (β := V))
      (MulAction.toPerm_injective (α := H) (β := V))
  let G : Subgroup H := translationGroup H Γ p
  let G₀ : Subgroup H := translationGroupMinus H Γ p L₀
  let S : Subgroup H := symmetryGroup H Γ L₀
  have hsup : G = S ⊔ G₀ := by
    simpa [G, G₀, S] using translationGroup_eq_sup p L₀ hpL₀
  have hSG : S ≤ G := by rw [hsup]; exact le_sup_left
  have hG₀G : G₀ ≤ G := by rw [hsup]; exact le_sup_right
  have hcL₀ : c L₀ = 1 := by
    have hne := c.valid hpL₀
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c L₀) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hcardS : Nat.card S = s := by
    simpa [S] using natCard_symmetryGroup_eq_s hP hT hM hdeg hreg hp hpL₀
  have hnormH : G ≤ Subgroup.normalizer (G₀ : Set H) := by
    simpa [G, G₀] using translationGroup_le_normalizer_translationGroupMinus hP p L₀
  haveI : (G₀.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hG₀G).mpr hnormH
  have hcomm : S ≤ Subgroup.centralizer (G₀ : Set H) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (commute_of_mem_symmetryGroup_of_mem_translationGroupMinus hP hT hpL₀ hg hh).symm
  have hSmul : ((S ⊔ G₀ : Subgroup H) : Set H) = (S : Set H) * (G₀ : Set H) :=
    Subgroup.coe_mul_of_left_le_normalizer_right S G₀
      (hcomm.trans (Subgroup.centralizer_le_normalizer (G₀ : Set H)))
  let Q := G ⧸ G₀.subgroupOf G
  have hcardQ : (G₀.subgroupOf G).index = Nat.card Q := Subgroup.index_eq_card (G₀.subgroupOf G)
  have hdvdS : (G₀.subgroupOf G).index ∣ s := by
    have hφsurj : Function.Surjective
        ((QuotientGroup.mk' (G₀.subgroupOf G)).comp (S.subgroupOf G).subtype) := by
      intro q
      obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (G₀.subgroupOf G) q
      have hgmem : (g : H) ∈ (S : Set H) * (G₀ : Set H) := by
        rw [← hSmul, ← hsup]
        exact g.2
      obtain ⟨a, haS, b, hbG₀, hab⟩ := Set.mem_mul.mp hgmem
      have haG : a ∈ G := hSG haS
      have hbG : b ∈ G := hG₀G hbG₀
      refine ⟨⟨⟨a, haG⟩, haS⟩, ?_⟩
      rw [← hg]
      have hgprod : g = ⟨a, haG⟩ * ⟨b, hbG⟩ := Subtype.ext (by simpa using hab.symm)
      have hb' : (⟨b, hbG⟩ : G) ∈ G₀.subgroupOf G := hbG₀
      rw [hgprod, map_mul]
      simp [hb']
    have hdvd := Subgroup.card_dvd_of_surjective
      (f := (QuotientGroup.mk' (G₀.subgroupOf G)).comp (S.subgroupOf G).subtype) hφsurj
    have hcardS' : Nat.card (S.subgroupOf G) = s := by
      calc
        Nat.card (S.subgroupOf G) = Nat.card S :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv
        _ = s := hcardS
    have hdvd' : Nat.card Q ∣ s := by
      rw [← hcardS']
      exact hdvd
    rwa [← hcardQ] at hdvd'
  by_contra hne
  have htop : G₀.subgroupOf G ≠ ⊤ := by
    intro htop
    apply hne
    exact (le_antisymm hG₀G (Subgroup.subgroupOf_eq_top.mp htop)).symm
  haveI : Finite (G ⧸ G₀.subgroupOf G) := Quotient.finite _
  have hlt : 1 < (G₀.subgroupOf G).index := Subgroup.one_lt_index_of_ne_top htop
  obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd (by omega : (G₀.subgroupOf G).index ≠ 1)
  have hqs : q ∣ s := dvd_trans hqdiv hdvdS
  obtain ⟨y, hyp, -⟩ := hP.exists_dist_eq hT hpL₀ 4 (by norm_num) (by norm_num)
  have hdist : Γ.dist y L₀ = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hyp hpL₀
  let x : V := proj hP hdist
  have hxL₀ : Γ.Adj L₀ x := proj_adj hP hdist
  have hxy : Γ.dist y x = 2 := proj_dist hP hdist
  have hxyp : x ≠ y := by
    intro h
    rw [h] at hxy
    simp at hxy
  let Gy : Subgroup G := MulAction.stabilizer G y
  have hGyLE : Gy ≤ Subgroup.normalizer (G₀.subgroupOf G : Set G) :=
    Subgroup.le_normalizer_of_normal
  have hGyMul : ((Gy ⊔ G₀.subgroupOf G : Subgroup G) : Set G) =
      (Gy : Set G) * (G₀.subgroupOf G : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Gy (G₀.subgroupOf G) hGyLE
  have htransY : Gy ⊔ G₀.subgroupOf G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hgp : (g : H) • p = p :=
      whorlGroup_fix_self hP hT (translationGroup_le_whorlGroup hP p g.2)
    have hgy : Γ.dist p ((g : H) • y) = 4 := by
      rw [← hgp, GPath.dist_smul hP.connected (g : H) p y]
      exact hyp
    obtain ⟨s, hsG₀, hsy⟩ :=
      exists_smul_mem_translationGroupMinus_of_dist_eq_four hP hT hM hdeg hreg hp hpL₀ h3
        hyp hgy
    let sG : G := ⟨s, hG₀G hsG₀⟩
    let tG : G := sG⁻¹ * g
    have htGy : tG ∈ Gy := by
      rw [MulAction.mem_stabilizer_iff]
      show ((sG⁻¹ * g : G) : H) • y = y
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_smul, ← hsy]
      exact inv_smul_smul s y
    have hg_eq : sG * tG = g := by
      dsimp [tG]
      rw [mul_inv_cancel_left]
    have hmem : g ∈ (G₀.subgroupOf G : Set G) * (Gy : Set G) := by
      refine ⟨sG, hsG₀, tG, htGy, hg_eq⟩
    have hcommul : (Gy : Set G) * (G₀.subgroupOf G : Set G) =
        (G₀.subgroupOf G : Set G) * (Gy : Set G) :=
      Subgroup.set_mul_normal_comm (Gy : Set G) (G₀.subgroupOf G)
    have : g ∈ (↑(Gy ⊔ G₀.subgroupOf G) : Set G) := by
      rw [hGyMul, hcommul]
      exact hmem
    simpa using this
  have hφYsurj : Function.Surjective
      ((QuotientGroup.mk' (G₀.subgroupOf G)).comp Gy.subtype) := by
    intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (G₀.subgroupOf G) q
    have hgmem : g ∈ (Gy : Set G) * (G₀.subgroupOf G : Set G) := by
      rw [← hGyMul, htransY]
      exact Subgroup.mem_top g
    obtain ⟨a, haGy, b, hbG₀, hab⟩ := Set.mem_mul.mp hgmem
    refine ⟨⟨a, haGy⟩, ?_⟩
    rw [← hg]
    have hgprod : g = a * b := hab.symm
    rw [hgprod, map_mul]
    simpa using hbG₀
  have hdvdY : Nat.card Q ∣ Nat.card Gy := by
    have h := Subgroup.card_dvd_of_surjective
      (f := (QuotientGroup.mk' (G₀.subgroupOf G)).comp Gy.subtype) hφYsurj
    rwa [← hcardQ] at h
  have hqY : q ∣ Nat.card Gy := dvd_trans hqdiv hdvdY
  haveI : Fintype Gy := Fintype.ofFinite Gy
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨θ, hθorder⟩ := exists_prime_orderOf_dvd_card' (G := Gy) q hqY
  have hθG : (θ : H) ∈ G := θ.1.2
  have hθwhorl : (θ : H) ∈ whorlGroup H Γ p :=
    translationGroup_le_whorlGroup hP p hθG
  have hθy : (θ : H) • y = y :=
    (MulAction.mem_stabilizer_iff.mp θ.2)
  have hqH : orderOf (θ : H) = q := by
    have h1 : orderOf (θ : G) = q := by
      rw [Subgroup.orderOf_coe]
      exact hθorder
    have h2 : orderOf ((θ : G) : H) = orderOf ((θ : G)) := Subgroup.orderOf_coe _
    rw [show (θ : H) = ((θ : G) : H) from rfl, h2, h1]
  have hL0fix : (θ : H) • L₀ = L₀ :=
    (mem_fixingSubgroup_iff H).mp hθwhorl L₀ hpL₀
  have hθx : (θ : H) • x = x := by
    have hproj : (θ : H) • x = proj hP hdist := by
      refine eq_proj hP hdist ?_ ?_
      · have h := (GraphAction.adj_smul (θ : H) L₀ x).mpr hxL₀
        rwa [hL0fix] at h
      · rw [← hθy, GPath.dist_smul hP.connected (θ : H) y x]
        exact hxy
    simpa [x] using hproj
  let M : V := commonNeighbor hP hxy
  have hyM : Γ.Adj y M := commonNeighbor_adj_left hP hxy
  have hxM : Γ.Adj M x := (commonNeighbor_adj_right hP hxy).symm
  have hMfix : (θ : H) • M = M :=
    line_fixed_of_fix_of_fix hP hθy hθx hyM hxM hxyp
  have hcx : c x = 0 := by
    have hd : Γ.dist x p = 2 := by
      rw [SimpleGraph.dist_comm]
      exact dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm (by
        intro h
        rw [h] at hxy
        have h2 : Γ.dist p y = 2 := by rw [SimpleGraph.dist_comm]; exact hxy
        omega))
    have hcp : c x = c p := (hP.eq_iff_even_dist c x p).2 (by rw [hd]; norm_num)
    rw [hcp]
    exact hp
  have hcM : c M = 1 := by
    have hne := c.valid hxM
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c M) with h | h
    · exact absurd (h.trans hcx.symm) hne
    · exact h
  have hcardM : Fintype.card ↥(Γ.neighborSet M) = s + 1 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, SimpleGraph.ncard_neighborSet,
      hdeg M, if_neg (by rw [hcM]; decide)]
  obtain ⟨z, hzM, hzx, hzy, hθz⟩ :=
    exists_fixed_third_of_prime_order hxM hyM.symm hxyp hMfix hθx hθy hqH hqprime hcardM hqs
  have hxp : Γ.dist x p = 2 := by
    rw [SimpleGraph.dist_comm]
    exact dist_eq_two_of_adj_of_adj_of_ne hP hpL₀ hxL₀ (Ne.symm (by
      intro h
      rw [h] at hxy
      have h2 : Γ.dist p y = 2 := by rw [SimpleGraph.dist_comm]; exact hxy
      omega))
  have hMxL₀ : commonNeighbor hP hxp = L₀ :=
    (eq_commonNeighbor hP hxp hxL₀.symm hpL₀).symm
  have hxz : Γ.dist x z = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hxM.symm hzM (Ne.symm hzx)
  have hMz : commonNeighbor hP hxz = M :=
    (eq_commonNeighbor hP hxz hxM.symm hzM.symm).symm
  have hML₀ : M ≠ L₀ := by
    intro h
    rw [h] at hyM
    have h3 := dist_eq_three_of_adj_of_dist_eq_four hP hyp hpL₀
    have h1 : Γ.dist y L₀ = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hyM
    omega
  have hzp : Γ.dist p z = 4 :=
    dist_eq_four_of_dist_eq_two_of_ne_commonNeighbor hP hxp hxz
      (by rw [hMxL₀, hMz]; exact Ne.symm hML₀)
  have hθone : (θ : H) = 1 :=
    eq_one_of_mem_whorlGroup_of_fix hP hT c hdeg hst hp hθwhorl hyp hyM hzM hzy hzp hθy hθz
  have horder1 : orderOf (θ : H) = 1 := by
    rw [hθone]
    exact orderOf_one
  have hq1 : q = 1 := by omega
  exact hqprime.ne_one hq1


theorem symmetryGroup_comm_of_adj (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p L : V} (hp : c p = 0) (hpL : Γ.Adj p L) (h3 : 3 ≤ t) :
    ∀ g h : H, g ∈ symmetryGroup H Γ L → h ∈ symmetryGroup H Γ L → Commute g h := by
  have hEq : translationGroup H Γ p = translationGroupMinus H Γ p L :=
    translationGroup_eq_translationGroupMinus hP hT hM hdeg hst hreg hp hpL h3
  have hSle : symmetryGroup H Γ L ≤ translationGroupMinus H Γ p L := by
    rw [← hEq]
    exact symmetryGroup_le_translationGroup hpL
  have hG0C : translationGroupMinus H Γ p L ≤
      Subgroup.centralizer (symmetryGroup H Γ L : Set H) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact commute_of_mem_symmetryGroup_of_mem_translationGroupMinus hP hT hpL hh hg
  intro g h hg hh
  exact (Subgroup.mem_centralizer_iff.mp (hG0C (hSle hg)) h hh).symm

theorem translationGroup_comm (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (hM : MoufangCondition H Γ 4) {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p : V} (hp : c p = 0) (h3 : 3 ≤ t) :
    ∀ g h : H, g ∈ translationGroup H Γ p → h ∈ translationGroup H Γ p → Commute g h := by
  have hgen : ∀ {L : V}, Γ.Adj p L →
      symmetryGroup H Γ L ≤ Subgroup.centralizer (translationGroup H Γ p : Set H) := by
    intro L hpL s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    refine Subgroup.closure_induction (p := fun x _ => Commute x s) ?_ ?_ ?_ ?_ ht
    · rintro x ⟨M, hpM, hx⟩
      by_cases hLM : L = M
      · subst hLM
        exact symmetryGroup_comm_of_adj hP hT hM hdeg hst hreg hp hpL h3 x s hx hs
      · exact commute_of_mem_symmetryGroup_of_adj hP hT hpM hpL (Ne.symm hLM) hx hs
    · exact Commute.one_left s
    · intro x y _ _ hx hy
      exact Commute.mul_left hx hy
    · intro x _ hx
      exact hx.inv_left
  intro a b ha hb
  refine Subgroup.closure_induction (p := fun x _ => Commute x b) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨L, hpL, hx⟩
    exact (Subgroup.mem_centralizer_iff.mp (hgen hpL hx) b hb).symm
  · exact Commute.one_left b
  · intro x y _ _ hx hy
    exact Commute.mul_left hx hy
  · intro x _ hx
    exact hx.inv_left


theorem translationGroup_fix_of_mem_stabilizer_line
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p A B : V} (hp : c p = 0) (h3 : 3 ≤ t)
    (hpA : Γ.Adj p A) (hpB : Γ.Adj p B) (hAB : A ≠ B)
    {z : V} (hzA : Γ.Adj A z) (hzp : z ≠ p)
    {g : H} (hg : g ∈ translationGroup H Γ p) (hgz : g • z = z) :
    ∀ w, Γ.Adj A w → g • w = w := by
  classical
  have hcB : c B = 1 := by
    have hne := c.valid hpB
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c B) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hgp : g • p = p :=
    whorlGroup_fix_self hP hT (translationGroup_le_whorlGroup hP p hg)
  intro w hwA
  by_cases hwp : w = p
  · rw [hwp]
    exact hgp
  · obtain ⟨h, hhS, hhz⟩ :=
      exists_smul_eq_of_mem_symmetryGroup_of_adj hP hT hM (hreg B hcB) hpB.symm hpA.symm
        (Ne.symm hAB) hzA hwA hzp hwp
    have hhG : h ∈ translationGroup H Γ p := symmetryGroup_le_translationGroup hpB hhS
    have hcomm : Commute g h := translationGroup_comm hP hT hM hdeg hst hreg hp h3 g h hg hhG
    calc
      g • w = g • (h • z) := by rw [hhz]
      _ = (g * h) • z := (mul_smul g h z).symm
      _ = (h * g) • z := by rw [hcomm.eq]
      _ = h • (g • z) := mul_smul h g z
      _ = h • z := by rw [hgz]
      _ = w := hhz

theorem index_stabilizer_translationGroup_line
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p A B : V} (hp : c p = 0) (h3 : 3 ≤ t)
    (hpA : Γ.Adj p A) (hpB : Γ.Adj p B) (hAB : A ≠ B)
    {z : V} (hzA : Γ.Adj A z) (hzp : z ≠ p) :
    (MulAction.stabilizer (translationGroup H Γ p) z).index = s := by
  classical
  have hcA : c A = 1 := by
    have hne := c.valid hpA
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c A) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hcB : c B = 1 := by
    have hne := c.valid hpB
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c B) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have horbit : MulAction.orbit (translationGroup H Γ p) z =
      Γ.neighborSet A \ {p} := by
    ext w
    constructor
    · rintro ⟨g, hgz⟩
      have hgH : (g : H) ∈ translationGroup H Γ p := g.2
      have hgz' : (g : H) • z = w := hgz
      have hgp : (g : H) • p = p :=
        whorlGroup_fix_self hP hT (translationGroup_le_whorlGroup hP p hgH)
      have hAfix : (g : H) • A = A :=
        (mem_fixingSubgroup_iff H).mp (translationGroup_le_whorlGroup hP p hgH) A hpA
      refine ⟨?_, ?_⟩
      · have h := (GraphAction.adj_smul (g : H) A z).mpr hzA
        rwa [hAfix, hgz'] at h
      · intro hwp
        have hdist : Γ.dist z p = 0 := by
          rw [← GPath.dist_smul hP.connected (g : H) z p, hgz', hgp, hwp,
            SimpleGraph.dist_self]
        have hzp' : z = p := (hP.connected.dist_eq_zero_iff).mp hdist
        exact hzp hzp'
    · rintro ⟨hwA, hwp⟩
      obtain ⟨g, hgS, hgz⟩ :=
        exists_smul_eq_of_mem_symmetryGroup_of_adj hP hT hM (hreg B hcB) hpB.symm hpA.symm
          (Ne.symm hAB) hzA hwA hzp hwp
      exact ⟨⟨g, symmetryGroup_le_translationGroup hpB hgS⟩, by simpa using hgz⟩
  rw [MulAction.index_stabilizer, horbit]
  have hp_mem : p ∈ Γ.neighborSet A := hpA.symm
  have hcard : (Γ.neighborSet A).ncard = s + 1 := by
    rw [SimpleGraph.ncard_neighborSet, hdeg A, if_neg (by rw [hcA]; decide)]
  rw [Set.ncard_sdiff_singleton_of_mem hp_mem, hcard]
  omega


theorem ncard_opposite_eq (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) {p : V}
    (hp : c p = 0) :
    {y : V | Γ.dist p y = 4}.ncard = s ^ 2 * t := by
  rw [Set.ncard_eq_toFinset_card]
  have h := card_opposite hP hT c hdeg hp
  convert h using 2
  ext y
  simp

theorem s_sq_mul_t_le_natCard_translationGroup
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p : V} (hp : c p = 0) (h3 : 3 ≤ t) :
    s ^ 2 * t ≤ Nat.card (translationGroup H Γ p) := by
  classical
  haveI : Fintype H :=
    Fintype.ofInjective (MulAction.toPerm (α := H) (β := V))
      (MulAction.toPerm_injective (α := H) (β := V))
  obtain ⟨L₀, hpL₀, -, -⟩ := exists_adj_ne_two hT p p p
  obtain ⟨y, hyp, -⟩ := hP.exists_dist_eq hT hpL₀ 4 (by norm_num) (by norm_num)
  let f : ↥(translationGroup H Γ p) → {z : V // Γ.dist p z = 4} := fun g =>
    ⟨(g : H) • y, by
      have hgp : (g : H) • p = p :=
        whorlGroup_fix_self hP hT (translationGroup_le_whorlGroup hP p g.2)
      calc
        Γ.dist p ((g : H) • y) = Γ.dist ((g : H) • p) ((g : H) • y) := by rw [hgp]
        _ = Γ.dist p y := GPath.dist_smul hP.connected (g : H) p y
        _ = 4 := hyp⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hgG₀, hgz⟩ :=
      exists_smul_mem_translationGroupMinus_of_dist_eq_four hP hT hM hdeg hreg hp hpL₀ h3
        hyp hz
    refine ⟨⟨g, translationGroupMinus_le_translationGroup p L₀ hgG₀⟩, ?_⟩
    exact Subtype.ext hgz
  have h := Nat.card_le_card_of_surjective f hsurj
  have hX : Nat.card {z : V // Γ.dist p z = 4} = s ^ 2 * t := by
    change Nat.card ↥{z : V | Γ.dist p z = 4} = s ^ 2 * t
    rw [Nat.card_coe_set_eq]
    exact ncard_opposite_eq hP hT hdeg hp
  rwa [hX] at h



theorem rootGroup_le_translationGroup_of_adj
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (hM : MoufangCondition H Γ 4)
    {c : Γ.Coloring (Fin 2)} {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L)
    {p A B : V} (hp : c p = 0) (h3 : 3 ≤ t)
    (hpA : Γ.Adj p A) (hpB : Γ.Adj p B) (hAB : A ≠ B) :
    rootGroup H Γ A p B ≤ translationGroup H Γ p := by
  classical
  haveI : Fintype H :=
    Fintype.ofInjective (MulAction.toPerm (α := H) (β := V))
      (MulAction.toPerm_injective (α := H) (β := V))
  let G : Subgroup H := translationGroup H Γ p
  have hcA : c A = 1 := by
    have hne := c.valid hpA
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c A) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hcB : c B = 1 := by
    have hne := c.valid hpB
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c B) with h | h
    · exact absurd (hp.trans h.symm) hne
    · exact h
  have hs_pos : 0 < s := by
    have h := hT A
    rw [hdeg A, if_neg (by rw [hcA]; decide)] at h
    omega
  obtain ⟨zA, hzA, hzAp, -⟩ := exists_adj_ne_two hT A p p
  obtain ⟨zB, hzB, hzBp, -⟩ := exists_adj_ne_two hT B p p
  let A0 : Subgroup ↥G := MulAction.stabilizer G zA
  let B0 : Subgroup ↥G := MulAction.stabilizer G zB
  have hAidx : A0.index = s := by
    simpa [A0, G] using index_stabilizer_translationGroup_line hP hT hM hdeg hst hreg hp h3
      hpA hpB hAB hzA hzAp
  have hBidx : B0.index = s := by
    simpa [B0, G] using index_stabilizer_translationGroup_line hP hT hM hdeg hst hreg hp h3
      hpB hpA (Ne.symm hAB) hzB hzBp
  have hcardG : s ^ 2 * t ≤ Nat.card ↥G := by
    simpa [G] using s_sq_mul_t_le_natCard_translationGroup hP hT hM hdeg hst hreg hp h3
  have hcardA0 : s * Nat.card A0 = Nat.card ↥G := by
    have h := Subgroup.index_mul_card (H := A0)
    rwa [hAidx] at h
  have hA0ge : s * t ≤ Nat.card A0 := by
    have hle : s * (s * t) ≤ s * Nat.card A0 := by
      rw [hcardA0]
      calc
        s * (s * t) = s ^ 2 * t := by ring
        _ ≤ Nat.card ↥G := hcardG
    exact Nat.le_of_mul_le_mul_left hle hs_pos
  haveI : B0.Normal := ⟨by
    intro n hn g
    have hcomm : Commute (g : H) (n : H) :=
      translationGroup_comm hP hT hM hdeg hst hreg hp h3 (g : H) (n : H) g.2 n.2
    have heq : (g * n * g⁻¹ : ↥G) = n := by
      apply Subtype.ext
      change ((g : H) * (n : H) * (g : H)⁻¹) = (n : H)
      rw [hcomm.eq]
      group
    rwa [heq]⟩
  let f : A0 →* ↥G ⧸ B0 := (QuotientGroup.mk' B0).comp A0.subtype
  have hker : f.ker = B0.subgroupOf A0 := by
    ext x
    constructor
    · intro hx
      have hxB : (x : ↥G) ∈ B0 :=
        (QuotientGroup.eq_one_iff (x : ↥G)).mp (by simpa [f] using hx)
      change (x : ↥G) ∈ B0
      exact hxB
    · intro hx
      have hxB : (x : ↥G) ∈ B0 := hx
      exact MonoidHom.mem_ker.mpr (by
        have : f x = QuotientGroup.mk' B0 (x : ↥G) := rfl
        rw [this]
        exact (QuotientGroup.eq_one_iff (x : ↥G)).mpr hxB)
  have hcardKer : Nat.card f.ker = Nat.card ↥(A0 ⊓ B0) := by
    rw [hker]
    rw [show B0.subgroupOf A0 = (A0 ⊓ B0).subgroupOf A0 from by
      rw [inf_comm, Subgroup.inf_subgroupOf_right]]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show A0 ⊓ B0 ≤ A0 from inf_le_left)).toEquiv
  have hrangeLe : Nat.card f.range ≤ s := by
    have h := Subgroup.card_le_card_group (H := f.range)
    rw [← Subgroup.index_eq_card] at h
    rwa [hBidx] at h
  have hkerGe : t ≤ Nat.card f.ker := by
    have hcard := Subgroup.card_ker_mul_card_range f
    have hle : t * s ≤ Nat.card f.ker * s := by
      calc
        t * s = s * t := by ring
        _ ≤ Nat.card A0 := hA0ge
        _ = Nat.card f.ker * Nat.card f.range := hcard.symm
        _ ≤ Nat.card f.ker * s := Nat.mul_le_mul_left _ hrangeLe
    exact Nat.le_of_mul_le_mul_right hle hs_pos
  have hinfGe : t ≤ Nat.card ↥(A0 ⊓ B0) := by
    rw [← hcardKer]
    exact hkerGe
  have hleU : (A0 ⊓ B0).map G.subtype ≤ rootGroup H Γ A p B := by
    rintro x ⟨y, hy, rfl⟩
    rw [mem_rootGroup]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fixingSubgroup_iff]
      intro w hwA
      have hyA : (y : H) • zA = zA :=
        (MulAction.mem_stabilizer_iff.mp hy.1)
      exact translationGroup_fix_of_mem_stabilizer_line hP hT hM hdeg hst hreg hp h3 hpA hpB
        hAB hzA hzAp y.2 (by simpa using hyA) w hwA
    · rw [mem_fixingSubgroup_iff]
      exact (mem_fixingSubgroup_iff H).mp
        (translationGroup_le_whorlGroup hP p y.2)
    · rw [mem_fixingSubgroup_iff]
      intro w hwB
      have hyB : (y : H) • zB = zB :=
        (MulAction.mem_stabilizer_iff.mp hy.2)
      exact translationGroup_fix_of_mem_stabilizer_line hP hT hM hdeg hst hreg hp h3 hpB hpA
        (Ne.symm hAB) hzB hzBp y.2 (by simpa using hyB) w hwB
  have hzBcolor : c zB = 0 := by
    have hne := c.valid hzB
    have hfin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
    rcases hfin (c zB) with h | h
    · exact h
    · exact absurd (h.trans hcB.symm) (Ne.symm hne)
  have hcardU : Nat.card (rootGroup H Γ A p B) = t := by
    let q : GPath Γ 4 :=
      { toFun := fun i => if i = 0 then zA else if i = 1 then A else if i = 2 then p
          else if i = 3 then B else zB
        adj := fun i hi => by
          rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
          · simpa using hzA.symm
          · simpa using hpA.symm
          · simpa using hpB
          · simpa using hzB
        tail := fun i hi => by
          have h0 : i ≠ 0 := by omega
          have h1 : i ≠ 1 := by omega
          have h2 : i ≠ 2 := by omega
          have h3' : i ≠ 3 := by omega
          simp [h0, h1, h2, h3', hzAp, hAB, hzBp] }
    have hq : q.NoBack := by
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · simpa [q] using hzAp
      · simpa [q] using hAB
      · simpa [q] using (Ne.symm hzBp)
    have h := card_rootGroup hP hT hM q hq
    have hq1 : q 1 = A := by simp [q]
    have hq2 : q 2 = p := by simp [q]
    have hq3 : q 3 = B := by simp [q]
    have hq4 : q 4 = zB := by simp [q]
    rw [hq1, hq2, hq3, hq4, hdeg zB, if_pos hzBcolor] at h
    omega
  have hmapCard : Nat.card ((A0 ⊓ B0).map G.subtype) = Nat.card ↥(A0 ⊓ B0) :=
    Subgroup.card_map_of_injective (f := G.subtype) (Subtype.coe_injective)
  have heq : (A0 ⊓ B0).map G.subtype = rootGroup H Γ A p B :=
    Subgroup.eq_of_le_of_card_ge hleU (by
      rw [hmapCard, hcardU]
      exact hinfGe)
  rw [← heq]
  rintro x ⟨y, -, rfl⟩
  exact y.2


theorem commute_of_mem_rootGroup_of_isRegular (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) (hreg : ∀ L, c L = 1 → IsRegularVertex Γ L) (p : GPath Γ 4)
    (hp : p.NoBack) {g h : H} (hg : g ∈ rootGroup H Γ (p 1) (p 2) (p 3))
    (hh : h ∈ rootGroup H Γ (p 1) (p 2) (p 3)) : g * h = h * g := by
  classical
  have h01 : ∀ {a b : V}, Γ.Adj a b → c a = 0 → c b = 1 := by
    intro a b hab ha
    have hne := c.valid hab
    have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hfin (c b) with hb | hb
    · exact absurd (ha.trans hb.symm) hne
    · exact hb
  have h10 : ∀ {a b : V}, Γ.Adj a b → c b = 1 → c a = 0 := by
    intro a b hab hb
    have hne := c.valid hab
    have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
    rcases hfin (c a) with ha | ha
    · exact ha
    · exact absurd (ha.trans hb.symm) hne
  by_cases h3 : 3 ≤ t
  · have hcol2 : c (p 2) = 0 ∨ c (p 2) = 1 := by
      have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
      exact hfin (c (p 2))
    rcases hcol2 with hc2 | hc2
    ·
      have hle := rootGroup_le_translationGroup_of_adj hP hT hM hdeg hst hreg hc2 h3
        (p.adj 1 (by omega)).symm (p.adj 2 (by omega)) (hp 1 (by omega))
      exact translationGroup_comm hP hT hM hdeg hst hreg hc2 h3 g h (hle hg) (hle hh)
    ·
      have hc1 : c (p 1) = 0 := h10 (p.adj 1 (by omega)) hc2
      have heq : rootGroup H Γ (p 1) (p 2) (p 3) = symmetryGroup H Γ (p 2) :=
        rootGroup_eq_symmetryGroup hP hT (hreg (p 2) hc2) (p.adj 1 (by omega)).symm
          (p.adj 2 (by omega)) (hp 1 (by omega))
      have hgS : g ∈ symmetryGroup H Γ (p 2) := by rwa [← heq]
      have hhS : h ∈ symmetryGroup H Γ (p 2) := by rwa [← heq]
      have hle : symmetryGroup H Γ (p 2) ≤ translationGroup H Γ (p 1) :=
        symmetryGroup_le_translationGroup (p.adj 1 (by omega))
      exact translationGroup_comm hP hT hM hdeg hst hreg hc1 h3 g h (hle hgS) (hle hhS)
  ·
    have ht2 : 2 ≤ t := by
      by_cases hc2 : c (p 2) = 0
      · have h := hT (p 2)
        rw [hdeg (p 2), if_pos hc2] at h
        omega
      · have hc2' : c (p 2) = 1 := by
          have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
          rcases hfin (c (p 2)) with h | h
          · exact absurd h hc2
          · exact h
        have hc1 : c (p 1) = 0 := h10 (p.adj 1 (by omega)) hc2'
        have h := hT (p 1)
        rw [hdeg (p 1), if_pos hc1] at h
        omega
    have hs2 : 2 ≤ s := by
      by_cases hc2 : c (p 2) = 0
      · have hc1 : c (p 1) = 1 := h01 (p.adj 1 (by omega)).symm hc2
        have h := hT (p 1)
        rw [hdeg (p 1), if_neg (by rw [hc1]; decide)] at h
        omega
      · have hc2' : c (p 2) = 1 := by
          have hfin : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
          rcases hfin (c (p 2)) with h | h
          · exact absurd h hc2
          · exact h
        have h := hT (p 2)
        rw [hdeg (p 2), if_neg (by rw [hc2']; decide)] at h
        omega
    have ht_le : t ≤ 2 := by omega
    have hs_eq : s = 2 := by omega
    have ht_eq : t = 2 := by omega
    have hp4color : c (p 4) = c (p 2) := by
      have hd : Γ.dist (p 2) (p 4) = 2 :=
        dist_eq_two_of_adj_of_adj_of_ne hP (p.adj 2 (by omega)) (p.adj 3 (by omega))
          (hp 2 (by omega))
      exact ((hP.eq_iff_even_dist c (p 2) (p 4)).2 (by rw [hd]; norm_num)).symm
    have hUcard : Nat.card ↥(rootGroup H Γ (p 1) (p 2) (p 3)) = 2 := by
      have h := card_rootGroup hP hT hM p hp
      have hdeg4 : Γ.degree (p 4) = 3 := by
        rw [hdeg (p 4)]
        by_cases hc2 : c (p 2) = 0
        · rw [if_pos (by rw [hp4color]; exact hc2), ht_eq]
        · rw [if_neg (by rw [hp4color]; exact hc2), hs_eq]
      omega
    let U := rootGroup H Γ (p 1) (p 2) (p 3)
    have hU2 : Nat.card ↥U = 2 := by simpa [U] using hUcard
    obtain ⟨y, hyne, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : ↥U)).mp hU2
    have hone_or : ∀ a : ↥U, a = 1 ∨ a = y := by
      intro a
      by_cases ha : a = 1
      · exact Or.inl ha
      · exact Or.inr (hyuniq a ha)
    rcases hone_or ⟨g, by simpa [U] using hg⟩ with hg1 | hgy
    · have hg1H : g = 1 := congrArg Subtype.val hg1
      rw [hg1H, one_mul, mul_one]
    · rcases hone_or ⟨h, by simpa [U] using hh⟩ with hh1 | hhy
      · have hh1H : h = 1 := congrArg Subtype.val hh1
        rw [hh1H, mul_one, one_mul]
      · have hgyH : g = (y : H) := congrArg Subtype.val hgy
        have hhyH : h = (y : H) := congrArg Subtype.val hhy
        rw [hgyH, hhyH]

end CFSG.Geometry.GeneralizedQuadrangles
