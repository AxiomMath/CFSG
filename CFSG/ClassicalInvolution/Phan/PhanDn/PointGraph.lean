module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Perp
public import CFSG.ClassicalInvolution.Phan.Geometry.Collinear
import all CFSG.ClassicalInvolution.Phan.PhanDn.Perp
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace
import all CFSG.ClassicalInvolution.Phan.Geometry.Collinear

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

private theorem isFlipflopSub_of_point {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : IsFlipflopSub σ p := by
  change IsFlipflopSub σ p ∧ Module.finrank K p = 1 at hp
  exact hp.1

private theorem finrank_of_point {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : Module.finrank K p = 1 := by
  change IsFlipflopSub σ p ∧ Module.finrank K p = 1 at hp
  exact hp.2

@[expose] noncomputable def toA (n : ℕ) (K : Type) [Field K] :
    (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin (n + n) → K) :=
  LinearEquiv.funCongrLeft K K finSumFinEquiv.symm

theorem herm_toA (u v : Fin n ⊕ Fin n → K) :
    herm σ (toA n K u) (toA n K v) = flipHerm σ v u := by
  rw [herm, flipHerm_apply]
  rw [show (∑ i : Fin (n + n), σ (toA n K u i) * toA n K v i) =
      ∑ j : Fin n ⊕ Fin n, σ (u j) * v j from ?_]
  · rw [Fintype.sum_sum_type, Finset.sum_add_distrib]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring
  · rw [← Equiv.sum_comp finSumFinEquiv.symm (fun j : Fin n ⊕ Fin n => σ (u j) * v j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [toA, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private theorem map_round_one (W : Submodule K (Fin (n + n) → K)) :
    (W.map (toA n K).symm.toLinearMap).map (toA n K).toLinearMap = W := by
  rw [← Submodule.map_comp]
  rw [show ((toA n K).toLinearMap).comp ((toA n K).symm).toLinearMap =
    LinearMap.id from LinearMap.ext fun v => (toA n K).apply_symm_apply v]
  rw [Submodule.map_id]

private theorem map_round_two (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (W.map (toA n K).toLinearMap).map (toA n K).symm.toLinearMap = W := by
  rw [← Submodule.map_comp]
  rw [show ((toA n K).symm.toLinearMap).comp ((toA n K).toLinearMap) =
    LinearMap.id from LinearMap.ext fun v => (toA n K).symm_apply_apply v]
  rw [Submodule.map_id]

theorem nondeg_map_toA_iff (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} :
    Nondeg σ (U.map (toA n K).toLinearMap) ↔
      ∀ u ∈ U, (∀ v ∈ U, flipHerm σ u v = 0) → u = 0 := by
  constructor
  · intro hnd u hu hper
    have hmem : toA n K u ∈ U.map (toA n K).toLinearMap :=
      Submodule.mem_map_of_mem hu
    have h0 := hnd (toA n K u) hmem fun t ht => by
      obtain ⟨v, hv, rfl⟩ := ht
      simp only [LinearEquiv.coe_coe]
      have h1 : flipHerm σ u v = 0 := hper v hv
      rw [herm_toA, (flipHerm_eq_zero_iff hσ).mp h1]
    exact (toA n K).injective (by simpa using h0)
  · intro h s hs hper
    obtain ⟨u, hu, rfl⟩ := hs
    have hu0 : u = 0 := h u hu fun v hv => by
      have h := hper (toA n K v) (Submodule.mem_map_of_mem hv)
      simp only [LinearEquiv.coe_coe] at h
      rw [herm_toA] at h
      exact (flipHerm_eq_zero_iff hσ).mpr h
    rw [hu0, map_zero]

theorem isFlipflopSub_iff_nondeg (hσ : ∀ x, σ (σ x) = x)
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : QSing U) :
    IsFlipflopSub σ U ↔ Nondeg σ (U.map (toA n K).toLinearMap) := by
  rw [nondeg_map_toA_iff hσ]
  constructor
  · exact fun h => h.nondeg
  · intro h
    refine ⟨?_, h⟩
    intro u hu
    have h1 : (quadPlusForm n K).Q u = 0 :=
      ((qSing_iff_isTotallySingular U).mp hU) u hu
    rwa [quadPlusForm_Q] at h1

@[expose] def IsFlipLine (σ : K ≃+* K) (L : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  IsFlipflopSub σ L ∧ Module.finrank K L = 2

@[expose] def FlipColl (σ : K ≃+* K) (p p' : Submodule K (Fin n ⊕ Fin n → K)) : Prop :=
  p ≠ p' ∧ IsFlipflopSub σ (p ⊔ p')

abbrev FlipPt (σ : K ≃+* K) (n : ℕ) : Type _ :=
  {p : Submodule K (Fin n ⊕ Fin n → K) // IsFlipflopPt σ p}

@[expose] def flipGraph (σ : K ≃+* K) (n : ℕ) : SimpleGraph (FlipPt σ n) where
  Adj p p' := FlipColl σ p.1 p'.1
  symm := ⟨fun p p' h => ⟨h.1.symm, by rw [sup_comm]; exact h.2⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

@[expose] def ptsOn (σ : K ≃+* K) (L : Submodule K (Fin n ⊕ Fin n → K)) :
    Set (Submodule K (Fin n ⊕ Fin n → K)) :=
  {x | IsFlipflopPt σ x ∧ x ≤ L}

theorem IsFlipflopPt.exists_eq_span {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) :
    ∃ v, p = K ∙ v ∧ quadPlus n K v = 0 ∧ flipHerm σ v v ≠ 0 := by
  have hne : p ≠ ⊥ := by
    rintro rfl
    have h1 := finrank_of_point hp
    rw [finrank_bot] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : K ∙ v ≤ p := (Submodule.span_singleton_le_iff_mem _ _).mpr hv
  have hfin : Module.finrank K (K ∙ v) = 1 := finrank_span_singleton hv0
  have hpv : p = K ∙ v :=
    (Submodule.eq_of_le_of_finrank_eq hspan (by rw [finrank_of_point hp, hfin])).symm
  have h := (isFlipflopSub_span_singleton_iff (σ := σ) hv0).mp (hpv ▸ isFlipflopSub_of_point hp)
  exact ⟨v, hpv, h.1, h.2⟩

theorem IsFlipflopSub.finrank_le {U : Submodule K (Fin n ⊕ Fin n → K)}
    (hU : IsFlipflopSub σ U) : Module.finrank K U ≤ n := by
  have h := ((qSing_iff_isTotallySingular U).mp hU.total).two_mul_finrank_le
  rw [finrank_flipSpace] at h
  omega

theorem IsFlipflopSub.sup_of_orth (hσ : ∀ x, σ (σ x) = x)
    {A B : Submodule K (Fin n ⊕ Fin n → K)} (hA : IsFlipflopSub σ A)
    (hB : IsFlipflopSub σ B) (hf : A ≤ qPerp n K B) (hh : A ≤ flipOrth σ B) :
    IsFlipflopSub σ (A ⊔ B) ∧ Disjoint A B := by
  have hBA : ∀ b ∈ B, ∀ a ∈ A, flipHerm σ b a = 0 :=
    fun b hb a ha => (mem_flipOrth.mp (hh ha)) b hb
  have hAB : ∀ a ∈ A, ∀ b ∈ B, flipHerm σ a b = 0 :=
    fun a ha b hb => (flipHerm_eq_zero_iff hσ).mp (hBA b hb a ha)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (qSing_iff_isTotallySingular (A ⊔ B)).mpr
      ((qSing_iff_isTotallySingular A).mp (show QSing A from hA.total) |>.sup
        ((qSing_iff_isTotallySingular B).mp (show QSing B from hB.total)) hf)
  · intro s hs hper
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
    have ha0 : a = 0 := by
      refine hA.nondeg a ha fun t ht => ?_
      have h := hper t (Submodule.mem_sup_left ht)
      rw [flipHerm_add_left, hBA b hb t ht] at h
      simpa using h
    have hb0 : b = 0 := by
      refine hB.nondeg b hb fun t ht => ?_
      have h := hper t (Submodule.mem_sup_right ht)
      rw [flipHerm_add_left, hAB a ha t ht] at h
      simpa using h
    rw [ha0, hb0, add_zero]
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxA, hxB⟩ := Submodule.mem_inf.mp hx
    exact hB.nondeg x hxB fun t ht => hAB x hxA t ht

theorem flipColl_of_orth (hσ : ∀ x, σ (σ x) = x)
    {p p' : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p)
    (hp' : IsFlipflopPt σ p') (hf : p ≤ qPerp n K p') (hh : p ≤ flipOrth σ p') :
    FlipColl σ p p' := by
  obtain ⟨hsup, hdisj⟩ := IsFlipflopSub.sup_of_orth hσ (isFlipflopSub_of_point hp)
    (isFlipflopSub_of_point hp') hf hh
  refine ⟨?_, hsup⟩
  intro hEq
  subst hEq
  rw [disjoint_iff, inf_idem] at hdisj
  have h1 := finrank_of_point hp
  rw [hdisj, finrank_bot] at h1
  omega

theorem FlipColl.le_qPerp {p p' : Submodule K (Fin n ⊕ Fin n → K)}
    (h : FlipColl σ p p') : p ≤ qPerp n K p' := by
  intro x hx
  rw [mem_qPerp]
  intro y hy
  have hx' : x ∈ p ⊔ p' := Submodule.mem_sup_left hx
  have hy' : y ∈ p ⊔ p' := Submodule.mem_sup_right hy
  have hx0 := h.2.total x hx'
  have hy0 := h.2.total y hy'
  have hxy := h.2.total (x + y) (Submodule.add_mem_sup hx hy)
  rw [QuadraticMap.map_add (quadPlus n K) x y, hx0, hy0] at hxy
  rw [polar_comm]
  simpa using hxy

theorem FlipColl.isFlipLine {p p' : Submodule K (Fin n ⊕ Fin n → K)}
    (h : FlipColl σ p p') (hp : IsFlipflopPt σ p) (hp' : IsFlipflopPt σ p') :
    IsFlipLine σ (p ⊔ p') := by
  refine ⟨h.2, ?_⟩
  have hinf : p ⊓ p' = ⊥ := by
    by_contra hne
    have h0 : Module.finrank K ↥(p ⊓ p') ≠ 0 := fun h0 =>
      hne (Submodule.finrank_eq_zero.mp h0)
    have h1 : Module.finrank K ↥(p ⊓ p') ≤ 1 :=
      finrank_of_point hp ▸ Submodule.finrank_mono inf_le_left
    have h2 : Module.finrank K ↥(p ⊓ p') = 1 := by omega
    have e1 : p ⊓ p' = p :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, finrank_of_point hp])
    have e2 : p ⊓ p' = p' :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h2, finrank_of_point hp'])
    exact h.1 (e1.symm.trans e2)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq p p'
  rw [hinf, finrank_bot, add_zero, finrank_of_point hp, finrank_of_point hp'] at hdim
  omega

theorem flipColl_iff_isCollinear (hσ : ∀ x, σ (σ x) = x)
    {p p' : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p)
    (hp' : IsFlipflopPt σ p') (hf : p ≤ qPerp n K p') :
    FlipColl σ p p' ↔
      IsCollinear σ (p.map (toA n K).toLinearMap) (p'.map (toA n K).toLinearMap) := by
  have hinj := Submodule.map_injective_of_injective (toA n K).injective
  have hsing : QSing (p ⊔ p') := by
    refine (qSing_iff_isTotallySingular (p ⊔ p')).mpr ?_
    exact (qSing_iff_isTotallySingular p).mp
      (show QSing p from (isFlipflopSub_of_point hp).total) |>.sup
      ((qSing_iff_isTotallySingular p').mp
        (show QSing p' from (isFlipflopSub_of_point hp').total)) hf
  constructor
  · intro h
    refine ⟨fun hEq => h.1 (hinj hEq), ?_⟩
    rw [← Submodule.map_sup]
    exact (isFlipflopSub_iff_nondeg hσ hsing).mp h.2
  · intro h
    refine ⟨fun hEq => h.1 (by rw [hEq]), ?_⟩
    refine (isFlipflopSub_iff_nondeg hσ hsing).mpr ?_
    rw [Submodule.map_sup]
    exact h.2

theorem flipColl_of_le_line {L x y : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L)
    (hx : x ∈ ptsOn σ L) (hy : y ∈ ptsOn σ L) (hxy : x ≠ y) : FlipColl σ x y := by
  obtain ⟨hxpt, hxL⟩ := hx
  obtain ⟨hypt, hyL⟩ := hy
  have hsup : x ⊔ y = L := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hxL hyL) ?_
    have hinf : x ⊓ y = ⊥ := by
      by_contra hne
      have h0 : Module.finrank K ↥(x ⊓ y) ≠ 0 := fun h0 =>
        hne (Submodule.finrank_eq_zero.mp h0)
      have h1 : Module.finrank K ↥(x ⊓ y) ≤ 1 :=
        finrank_of_point hxpt ▸ Submodule.finrank_mono inf_le_left
      have h2 : Module.finrank K ↥(x ⊓ y) = 1 := by omega
      have e1 : x ⊓ y = x :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, finrank_of_point hxpt])
      have e2 : x ⊓ y = y :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h2, finrank_of_point hypt])
      exact hxy (e1.symm.trans e2)
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq x y
    rw [hinf, finrank_bot, add_zero, finrank_of_point hxpt, finrank_of_point hypt] at hdim
    rw [hL.2]
    omega
  refine ⟨hxy, ?_⟩
  rw [hsup]
  exact hL.1

private theorem mem_nsPts_map_of_mem_ptsOn (hσ : ∀ x, σ (σ x) = x)
    {L : Submodule K (Fin n ⊕ Fin n → K)}
    {x : Submodule K (Fin n ⊕ Fin n → K)} (hx : x ∈ ptsOn σ L) :
    x.map (toA n K).toLinearMap ∈ nsPts σ (L.map (toA n K).toLinearMap) := by
  obtain ⟨hxpt, hxL⟩ := hx
  refine ⟨Submodule.map_mono hxL, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, finrank_of_point hxpt]
  · exact (isFlipflopSub_iff_nondeg hσ
      (isFlipflopSub_of_point hxpt).total).mp (isFlipflopSub_of_point hxpt)

private theorem exists_ptsOn_map_eq_of_mem_nsPts (hσ : ∀ x, σ (σ x) = x)
    {L : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L)
    {y : Submodule K (Fin (n + n) → K)}
    (hy : y ∈ nsPts σ (L.map (toA n K).toLinearMap)) :
    ∃ x ∈ ptsOn σ L, x.map (toA n K).toLinearMap = y := by
  set x : Submodule K (Fin n ⊕ Fin n → K) := y.map (toA n K).symm.toLinearMap with hxdef
  have hxe : x.map (toA n K).toLinearMap = y := by
    rw [hxdef]
    exact map_round_one (n := n) (K := K) y
  have hxL : x ≤ L := by
    rw [hxdef]
    have h := Submodule.map_mono (f := (toA n K).symm.toLinearMap) hy.1
    rw [map_round_two (n := n) (K := K) L] at h
    exact h
  have hxfin : Module.finrank K x = 1 := by
    rw [hxdef, LinearEquiv.finrank_map_eq, hy.2.1]
  have hxnd : ∀ u ∈ x, (∀ v ∈ x, flipHerm σ u v = 0) → u = 0 :=
    (nondeg_map_toA_iff hσ (U := x)).mp (hxe.symm ▸ hy.2.2)
  have hxpt : IsFlipflopPt σ x := by
    change IsFlipflopSub σ x ∧ Module.finrank K x = 1
    exact ⟨⟨fun u hu => hL.1.total u (hxL hu), hxnd⟩, hxfin⟩
  exact ⟨x, ⟨hxpt, hxL⟩, hxe⟩

private theorem flipColl_of_isCollinear_map (hσ : IsUnitaryInvolution σ)
    {L p x : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L)
    (hp : IsFlipflopPt σ p) (hpL : p ≤ qPerp n K L) (hx : x ∈ ptsOn σ L)
    (hcol : IsCollinear σ (p.map (toA n K).toLinearMap) (x.map (toA n K).toLinearMap)) :
    FlipColl σ p x := by
  have hsing : QSing (p ⊔ x) := by
    refine (qSing_iff_isTotallySingular (p ⊔ x)).mpr ?_
    exact (qSing_iff_isTotallySingular p).mp
      (show QSing p from (isFlipflopSub_of_point hp).total) |>.sup
      ((qSing_iff_isTotallySingular x).mp (show QSing x from fun u hu => hL.1.total u (hx.2 hu)))
      (le_trans hpL (qPerp_antitone hx.2))
  refine ⟨?_, ?_⟩
  · intro hpx
    exact hcol.1 (by rw [hpx])
  · refine (isFlipflopSub_iff_nondeg hσ.invol hsing).mpr ?_
    rw [Submodule.map_sup]
    exact hcol.2

theorem isFlipflopPt_stdE (hn : 1 ≤ n) :
    IsFlipflopPt σ (K ∙ stdE (K := K) (⟨0, by omega⟩ : Fin n)) := by
  refine (isFlipflopPt_span_singleton_iff (σ := σ) ?_).mpr
    ⟨quadPlus_stdE _, ?_⟩
  · intro h
    have h1 := congrFun h (Sum.inl (⟨0, by omega⟩ : Fin n))
    rw [stdE_inl] at h1
    simp at h1
  · rw [flipHerm_stdE_stdE, if_pos rfl]
    exact one_ne_zero

theorem ncard_ptsOn (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {L : Submodule K (Fin n ⊕ Fin n → K)}
    (hL : IsFlipLine σ L) : (ptsOn σ L).ncard = q ^ 2 - q := by
  have hset : ((fun x : Submodule K (Fin n ⊕ Fin n → K) =>
        x.map (toA n K).toLinearMap) '' ptsOn σ L) =
      nsPts σ (L.map (toA n K).toLinearMap) := by
    ext y
    exact ⟨fun hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact mem_nsPts_map_of_mem_ptsOn hσ.invol hx,
      fun hy => by
        obtain ⟨x, hx, hxy⟩ := exists_ptsOn_map_eq_of_mem_nsPts hσ.invol hL hy
        exact ⟨x, hx, hxy⟩⟩
  have hLfin : Module.finrank K (L.map (toA n K).toLinearMap) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hL.2]
  have hLnd : Nondeg σ (L.map (toA n K).toLinearMap) :=
    (isFlipflopSub_iff_nondeg hσ.invol hL.1.total).mp hL.1
  have hcard : (ptsOn σ L).ncard =
      (nsPts σ (L.map (toA n K).toLinearMap)).ncard := by
    rw [← hset]
    exact (Set.ncard_image_of_injective (ptsOn σ L)
      (Submodule.map_injective_of_injective (toA n K).injective)).symm
  rw [hcard, ncard_nsPts_of_nondeg_plane hσ hK hLfin hLnd]

theorem le_ncard_flipColl (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {L p : Submodule K (Fin n ⊕ Fin n → K)}
    (hL : IsFlipLine σ L) (hp : IsFlipflopPt σ p) (hpL : p ≤ qPerp n K L) :
    q ^ 2 - 2 * q - 1 ≤ {x | x ∈ ptsOn σ L ∧ FlipColl σ p x}.ncard := by
  have hset : ((fun x : Submodule K (Fin n ⊕ Fin n → K) =>
        x.map (toA n K).toLinearMap) '' {x | x ∈ ptsOn σ L ∧ FlipColl σ p x}) =
      {y | y ∈ nsPts σ (L.map (toA n K).toLinearMap) ∧
        IsCollinear σ (p.map (toA n K).toLinearMap) y} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hcoll⟩, rfl⟩
      refine ⟨mem_nsPts_map_of_mem_ptsOn hσ.invol hx, ?_⟩
      refine ⟨fun hEq => hcoll.1 (Submodule.map_injective_of_injective
        (toA n K).injective hEq), ?_⟩
      rw [← Submodule.map_sup]
      exact (isFlipflopSub_iff_nondeg hσ.invol hcoll.2.total).mp hcoll.2
    · rintro ⟨hy, hcol⟩
      obtain ⟨x, hx, hxy⟩ := exists_ptsOn_map_eq_of_mem_nsPts hσ.invol hL hy
      exact ⟨x, ⟨hx, flipColl_of_isCollinear_map hσ hL hp hpL hx (hxy.symm ▸ hcol)⟩, hxy⟩
  have hLfin : Module.finrank K (L.map (toA n K).toLinearMap) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hL.2]
  have hLnd : Nondeg σ (L.map (toA n K).toLinearMap) :=
    (isFlipflopSub_iff_nondeg hσ.invol hL.1.total).mp hL.1
  have hp' : p.map (toA n K).toLinearMap ∈
      nsPts σ (⊤ : Submodule K (Fin (n + n) → K)) :=
    ⟨le_top, by rw [LinearEquiv.finrank_map_eq, finrank_of_point hp],
      (isFlipflopSub_iff_nondeg hσ.invol (isFlipflopSub_of_point hp).total).mp
        (isFlipflopSub_of_point hp)⟩
  have hcard : {x | x ∈ ptsOn σ L ∧ FlipColl σ p x}.ncard =
      {y | y ∈ nsPts σ (L.map (toA n K).toLinearMap) ∧
        IsCollinear σ (p.map (toA n K).toLinearMap) y}.ncard := by
    rw [← hset]
    exact (Set.ncard_image_of_injective {x | x ∈ ptsOn σ L ∧ FlipColl σ p x}
      (Submodule.map_injective_of_injective (toA n K).injective)).symm
  rw [hcard]
  exact le_ncard_collinear hσ hK hLfin hLnd hp'

theorem exists_flipColl_ne (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {L p : Submodule K (Fin n ⊕ Fin n → K)}
    (hL : IsFlipLine σ L) (hp : IsFlipflopPt σ p) (hpL : p ≤ qPerp n K L)
    (y z : Submodule K (Fin n ⊕ Fin n → K)) :
    ∃ x ∈ ptsOn σ L, x ≠ y ∧ x ≠ z ∧ FlipColl σ p x := by
  have h3 : 3 ≤ q ^ 2 - 2 * q - 1 := by
    have hlt : 2 * q < q ^ 2 := by nlinarith
    have h2q : 2 * q ≤ q ^ 2 := le_of_lt hlt
    have h1 : 1 ≤ q ^ 2 - 2 * q := by omega
    have hcast : ((q ^ 2 - 2 * q - 1 : ℕ) : ℤ) = (q : ℤ) ^ 2 - 2 * q - 1 := by
      rw [Nat.cast_sub h1, Nat.cast_sub h2q]
      push_cast
      ring
    have h3' : (3 : ℤ) ≤ (q : ℤ) ^ 2 - 2 * q - 1 := by
      have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    rw [← hcast] at h3'
    exact_mod_cast h3'
  have hlow := le_ncard_flipColl hσ hK hL hp hpL
  have hgt : 3 ≤ {x | x ∈ ptsOn σ L ∧ FlipColl σ p x}.ncard := le_trans h3 hlow
  obtain ⟨x, hxS, hxy, hxz⟩ : ∃ x ∈ {x | x ∈ ptsOn σ L ∧ FlipColl σ p x},
      x ≠ y ∧ x ≠ z := by
    by_contra hcon
    have hsub : {x | x ∈ ptsOn σ L ∧ FlipColl σ p x} ⊆
        ({y, z} : Set (Submodule K (Fin n ⊕ Fin n → K))) := by
      intro x hx
      by_cases hxy : x = y
      · simp [hxy]
      · have hxz : x = z := by
          by_contra hxz
          exact hcon ⟨x, hx, hxy, hxz⟩
        simp [hxz]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair : ({y, z} : Set (Submodule K (Fin n ⊕ Fin n → K))).ncard ≤ 2 := by
      have h := Set.ncard_insert_le y ({z} : Set (Submodule K (Fin n ⊕ Fin n → K)))
      rw [Set.ncard_singleton] at h
      simpa using h
    omega
  exact ⟨x, hxS.1, hxy, hxz, hxS.2⟩

theorem exists_flipColl₂ (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) {L p₁ p₂ : Submodule K (Fin n ⊕ Fin n → K)}
    (hL : IsFlipLine σ L) (hp₁ : IsFlipflopPt σ p₁) (hp₂ : IsFlipflopPt σ p₂)
    (h₁ : p₁ ≤ qPerp n K L) (h₂ : p₂ ≤ qPerp n K L) :
    ∃ x ∈ ptsOn σ L, FlipColl σ p₁ x ∧ FlipColl σ p₂ x := by
  classical
  have hp₁' : p₁.map (toA n K).toLinearMap ∈
      nsPts σ (⊤ : Submodule K (Fin (n + n) → K)) :=
    ⟨le_top, by rw [LinearEquiv.finrank_map_eq, finrank_of_point hp₁],
      (isFlipflopSub_iff_nondeg hσ.invol (isFlipflopSub_of_point hp₁).total).mp
        (isFlipflopSub_of_point hp₁)⟩
  have hp₂' : p₂.map (toA n K).toLinearMap ∈
      nsPts σ (⊤ : Submodule K (Fin (n + n) → K)) :=
    ⟨le_top, by rw [LinearEquiv.finrank_map_eq, finrank_of_point hp₂],
      (isFlipflopSub_iff_nondeg hσ.invol (isFlipflopSub_of_point hp₂).total).mp
        (isFlipflopSub_of_point hp₂)⟩
  have hLfin : Module.finrank K (L.map (toA n K).toLinearMap) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hL.2]
  have hLnd : Nondeg σ (L.map (toA n K).toLinearMap) :=
    (isFlipflopSub_iff_nondeg hσ.invol hL.1.total).mp hL.1
  have hX : ∀ x ∈ ({p₁.map (toA n K).toLinearMap, p₂.map (toA n K).toLinearMap} :
      Finset (Submodule K (Fin (n + n) → K))),
      x ∈ nsPts σ (⊤ : Submodule K (Fin (n + n) → K)) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hp₁'
    · rw [Finset.mem_singleton.mp hx]
      exact hp₂'
  have hcard : ({p₁.map (toA n K).toLinearMap, p₂.map (toA n K).toLinearMap} :
      Finset (Submodule K (Fin (n + n) → K))).card * (q + 1) < q ^ 2 - q := by
    have hF : ({p₁.map (toA n K).toLinearMap, p₂.map (toA n K).toLinearMap} :
        Finset (Submodule K (Fin (n + n) → K))).card ≤ 2 := by
      have h := Finset.card_insert_le (p₁.map (toA n K).toLinearMap)
        ({p₂.map (toA n K).toLinearMap} : Finset (Submodule K (Fin (n + n) → K)))
      rw [Finset.card_singleton] at h
      simpa using h
    have hmul : ({p₁.map (toA n K).toLinearMap, p₂.map (toA n K).toLinearMap} :
        Finset (Submodule K (Fin (n + n) → K))).card * (q + 1) ≤ 2 * (q + 1) := by
      simpa [mul_comm] using mul_le_mul_right hF (q + 1)
    refine lt_of_le_of_lt hmul ?_
    have hq1 : 1 ≤ q := by omega
    have hle : q ≤ q ^ 2 := by
      have h := le_mul_of_one_le_right (Nat.zero_le q) hq1
      simpa [pow_two] using h
    have hcast : ((q ^ 2 - q : ℕ) : ℤ) = (q : ℤ) ^ 2 - q := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have h3' : (2 * (q + 1) : ℤ) < (q : ℤ) ^ 2 - q := by
      have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    rw [← hcast] at h3'
    exact_mod_cast h3'
  obtain ⟨y, hy, hcol⟩ := exists_collinear_all hσ hK hLfin hLnd
    ({p₁.map (toA n K).toLinearMap, p₂.map (toA n K).toLinearMap} :
      Finset (Submodule K (Fin (n + n) → K))) hX hcard
  obtain ⟨x, hx, hxy⟩ := exists_ptsOn_map_eq_of_mem_nsPts hσ.invol hL hy
  refine ⟨x, hx, ?_, ?_⟩
  · exact flipColl_of_isCollinear_map hσ hL hp₁ h₁ hx
      (hxy.symm ▸ hcol (p₁.map (toA n K).toLinearMap) (Finset.mem_insert_self _ _))
  · exact flipColl_of_isCollinear_map hσ hL hp₂ h₂ hx
      (hxy.symm ▸ hcol (p₂.map (toA n K).toLinearMap)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

end CFSG.ClassicalInvolution.PhanDn
