module

public import CFSG.GF2Type.SmithTypeE.LMod.AutNorm
public import Certificates.Certificate38609

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open Subgroup

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

theorem partners_reach :
    K.Reach 1953 1953 (fun v => v == 31 || !isPartner v)
      (fun g u v => tvImg g 0 == 0 && tvImg g u == v && (!isPartner v || isPartner u)) :=
  Certificates.certificate38609.1

@[expose] def FourStep (s t : ℕ × ℕ × ℕ) : Prop :=
  ∃ g < 1953, tvImg g 0 = 0 ∧ tvImg g 31 = 31 ∧ t = fourStep g s

theorem four_orbit : ∃ L : List (ℕ × ℕ × ℕ), L.length = 20160 ∧
    L.Nodup ∧ ∀ t ∈ L, Relation.ReflTransGen FourStep fourBase t :=
  Certificates.certificate38609.2

@[expose] def fin1953 (k : ℕ) : Fin 1953 := ⟨k % 1953, Nat.mod_lt _ (by norm_num)⟩

theorem fin1953_val {k : ℕ} (hk : k < 1953) : (fin1953 k).val = k := Nat.mod_eq_of_lt hk

@[expose] def p31 : Fin 1953 := fin1953 31

section Pairs


@[expose] def commSet (kt ku : Fin 1953) : Set (Fin 1953) :=
  {k | Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)}

theorem commute_tvP_iff (k a : Fin 1953) :
    Commute (tvP k) (tvP a) ↔ tvImg k.val a.val = a.val := by
  have h1 : tvP k * tvP a * (tvP k)⁻¹ = tvP (tvP k a) := mul_tvP_mul_inv (tvP_mem k) a
  have h2 : Commute (tvP k) (tvP a) ↔ tvP k * tvP a * (tvP k)⁻¹ = tvP a := by
    rw [commute_iff_eq, mul_inv_eq_iff_eq_mul]
  rw [h2, h1, tvP_injective.eq_iff, Fin.ext_iff, tvP_apply]

theorem tvP_conj_fin {g a : ℕ} (hg : g < 1953) (ha : a < 1953) :
    tvP (fin1953 g) * tvP (fin1953 a) * (tvP (fin1953 g))⁻¹ = tvP (fin1953 (tvImg g a)) := by
  have hlt : tvImg g a < 1953 := tvImg_lt hg ha
  have h1 : tvP (fin1953 g) (fin1953 a) = fin1953 (tvImg g a) := by
    apply Fin.ext
    rw [tvP_apply, fin1953_val hlt, fin1953_val hg, fin1953_val ha]
  rw [mul_tvP_mul_inv (tvP_mem (fin1953 g)) (fin1953 a), h1]

@[expose] def stabGrp : Subgroup (Equiv.Perm (Fin 1953)) :=
  closure (tvP '' {g : Fin 1953 | tvImg g.val 0 = 0})

theorem stabGrp_le_T6 : stabGrp ≤ T6 := by
  unfold stabGrp
  rw [Subgroup.closure_le]
  rintro _ ⟨g, _, rfl⟩
  exact tvP_mem g

theorem mem_stabGrp_apply_zero {h : Equiv.Perm (Fin 1953)} (hh : h ∈ stabGrp) : h 0 = 0 := by
  unfold stabGrp at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' : tvImg g.val 0 = 0 := hg
    apply Fin.ext
    rw [tvP_apply]
    exact hg'
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => exact Equiv.Perm.inv_eq_iff_eq.2 hx.symm

theorem braid_of_orderOf_three {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : orderOf (a * b) = 3) : a * b * a = b * a * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h3 : (a * b) ^ 3 = 1 := by
    have h' := pow_orderOf_eq_one (a * b)
    rwa [h] at h'
  have h3' : a * b * (a * b) * (a * b) = 1 := (pow_three' (a * b)).symm.trans h3
  have h5 : a * b * a * (b * a * b) = 1 := by
    have e : a * b * a * (b * a * b) = a * b * (a * b) * (a * b) := by
      simp only [mul_assoc]
    exact e.trans h3'
  have h6 : b * a * b = (a * b * a)⁻¹ := eq_inv_of_mul_eq_one_right h5
  have h7 : (a * b * a)⁻¹ = a * b * a := by
    rw [mul_inv_rev, mul_inv_rev, ha', hb', mul_assoc]
  exact (h6.trans h7).symm

theorem isPartner_of_orderOf_three {u : Fin 1953} (h : orderOf (tvP 0 * tvP u) = 3) :
    isPartner u.val = true := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [tvP_mul_self, orderOf_one] at h
    omega
  have hu : u.val ≠ 0 := fun hv => hu0 (Fin.ext hv)
  have hb := braid_of_orderOf_three (tvP_mul_self 0) (tvP_mul_self u) h
  have e1 : tvP 0 * tvP u * tvP 0 = tvP (tvP 0 u) := by
    have := mul_tvP_mul_inv (tvP_mem 0) u
    rwa [tvP_inv 0] at this
  have e2 : tvP u * tvP 0 * tvP u = tvP (tvP u 0) := by
    have := mul_tvP_mul_inv (tvP_mem u) 0
    rwa [tvP_inv u] at this
  have h3 : tvP (tvP 0 u) = tvP (tvP u 0) := e1.symm.trans (hb.trans e2)
  have hv : ((tvP 0 u : Fin 1953) : ℕ) = ((tvP u 0 : Fin 1953) : ℕ) :=
    congrArg Fin.val (tvP_injective h3)
  rw [tvP_apply, tvP_apply] at hv
  have h0 : ((0 : Fin 1953) : ℕ) = 0 := rfl
  rw [h0] at hv
  rw [isPartner, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact ⟨hu, hv⟩

section Cert


theorem exists_stab_partner {u : Fin 1953} (hu : isPartner u.val = true) :
    ∃ h ∈ stabGrp, h p31 = u := by
  have key := partners_reach
    (fun v => ∀ hv : v < 1953, isPartner v = true → ∃ h ∈ stabGrp, h p31 = ⟨v, hv⟩) ?_ ?_
    u.val u.isLt
  · exact key u.isLt hu
  · intro v _ hr
    intro hv' hpv
    simp only [Bool.or_eq_true, beq_iff_eq] at hr
    rcases hr with hr | hr
    · subst hr
      refine ⟨1, stabGrp.one_mem, ?_⟩
      rw [Equiv.Perm.one_apply]
      refine Fin.ext ?_
      exact fin1953_val (by norm_num)
    · simp [hpv] at hr
  · intro g hg a ha b _ he ihA
    intro hb' hpb
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨⟨hk0, he1⟩, he2⟩ := he
    have hpa : isPartner a = true := by simpa [hpb] using he2
    obtain ⟨s, hs, hsa⟩ := ihA ha hpa
    refine ⟨tvP ⟨g, hg⟩ * s,
      stabGrp.mul_mem (Subgroup.subset_closure ⟨⟨g, hg⟩, hk0, rfl⟩) hs, ?_⟩
    rw [Equiv.Perm.mul_apply, hsa]
    refine Fin.ext ?_
    rw [tvP_apply]
    exact he1


theorem exists_pair_map {kt ku : Fin 1953} (h : orderOf (tvP kt * tvP ku) = 3) :
    ∃ y ∈ T6, y kt = 0 ∧ y ku = p31 := by
  obtain ⟨g, hg, hgk⟩ := exists_mem_T6_apply_eq kt 0
  have hconj : g * (tvP kt * tvP ku) * g⁻¹ = tvP 0 * tvP (g ku) := by
    rw [show g * (tvP kt * tvP ku) * g⁻¹ = (g * tvP kt * g⁻¹) * (g * tvP ku * g⁻¹) by group,
      mul_tvP_mul_inv hg, mul_tvP_mul_inv hg, hgk]
  have hord : orderOf (tvP 0 * tvP (g ku)) = 3 := by
    have hc := MulEquiv.orderOf_eq (MulAut.conj g) (tvP kt * tvP ku)
    rw [MulAut.conj_apply] at hc
    rw [← hconj, hc]
    exact h
  obtain ⟨s, hs, hsu⟩ := exists_stab_partner (isPartner_of_orderOf_three hord)
  refine ⟨s⁻¹ * g, T6.mul_mem (T6.inv_mem (stabGrp_le_T6 hs)) hg, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, hgk, Equiv.Perm.inv_eq_iff_eq]
    exact (mem_stabGrp_apply_zero hs).symm
  · rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact hsu.symm

end Cert

end Pairs

section Four


theorem conj_step_fin {g a : ℕ} (hg : g < 1953) (ha : a < 1953) (h x : Equiv.Perm (Fin 1953))
    (hx : h * x * h⁻¹ = tvP (fin1953 a)) :
    tvP (fin1953 g) * h * x * (tvP (fin1953 g) * h)⁻¹ = tvP (fin1953 (tvImg g a)) := by
  rw [← tvP_conj_fin hg ha, ← hx]
  simp only [mul_inv_rev, mul_assoc]

theorem four_exists_conj {t : ℕ × ℕ × ℕ} (ht : Relation.ReflTransGen FourStep fourBase t) :
    (t.1 < 1953 ∧ t.2.1 < 1953 ∧ t.2.2 < 1953) ∧ ∃ h ∈ closure (tvP '' commSet 0 p31),
      h * tvP (fin1953 1352) * h⁻¹ = tvP (fin1953 t.1) ∧
      h * tvP (fin1953 968) * h⁻¹ = tvP (fin1953 t.2.1) ∧
      h * tvP (fin1953 1480) * h⁻¹ = tvP (fin1953 t.2.2) := by
  induction ht with
  | refl =>
    refine ⟨⟨by decide, by decide, by decide⟩, 1, Subgroup.one_mem _, ?_, ?_, ?_⟩ <;>
      simp only [fourBase, one_mul, inv_one, mul_one]
  | tail _ hst ih =>
    obtain ⟨g, hg, hg0, hg31, rfl⟩ := hst
    obtain ⟨⟨hb1, hb2, hb3⟩, k, hk, e1, e2, e3⟩ := ih
    have hcomm : fin1953 g ∈ commSet 0 p31 := by
      have hp31 : p31.val = 31 := fin1953_val (k := 31) (by norm_num)
      simp only [commSet, Set.mem_setOf_eq]
      refine ⟨(commute_tvP_iff _ _).2 ?_, (commute_tvP_iff _ _).2 ?_⟩
      · rw [fin1953_val hg]
        exact hg0
      · rw [fin1953_val hg, hp31]
        exact hg31
    have hmem : tvP (fin1953 g) ∈ closure (tvP '' commSet 0 p31) :=
      Subgroup.subset_closure (Set.mem_image_of_mem tvP hcomm)
    exact ⟨⟨tvImg_lt hg hb1, tvImg_lt hg hb2, tvImg_lt hg hb3⟩, tvP (fin1953 g) * k,
      Subgroup.mul_mem _ hmem hk, conj_step_fin hg hb1 k _ e1, conj_step_fin hg hb2 k _ e2,
      conj_step_fin hg hb3 k _ e3⟩


theorem four_card_ge : 20160 ≤ Nat.card (closure (tvP '' commSet 0 p31)) := by
  obtain ⟨L, hlen, hnd, hL⟩ := four_orbit
  have hn : ∀ n : Fin 20160, (n : ℕ) < L.length := fun n => by
    have := n.2
    omega
  have hP := fun n : Fin 20160 => four_exists_conj (hL _ (List.getElem_mem (hn n)))
  choose f hfS hf1 hf2 hf3 using fun n => (hP n).2
  let F : Fin 20160 → closure (tvP '' commSet 0 p31) := fun n => ⟨f n, hfS n⟩
  have hF : Function.Injective F := by
    intro a b hab
    have hfab : f a = f b := congrArg Subtype.val hab
    have c1 : tvP (fin1953 (L[(a : ℕ)]'(hn a)).1) = tvP (fin1953 (L[(b : ℕ)]'(hn b)).1) := by
      rw [← hf1 a, ← hf1 b, hfab]
    have c2 : tvP (fin1953 (L[(a : ℕ)]'(hn a)).2.1) = tvP (fin1953 (L[(b : ℕ)]'(hn b)).2.1) := by
      rw [← hf2 a, ← hf2 b, hfab]
    have c3 : tvP (fin1953 (L[(a : ℕ)]'(hn a)).2.2) = tvP (fin1953 (L[(b : ℕ)]'(hn b)).2.2) := by
      rw [← hf3 a, ← hf3 b, hfab]
    have e1 := congrArg Fin.val (tvP_injective c1)
    have e2 := congrArg Fin.val (tvP_injective c2)
    have e3 := congrArg Fin.val (tvP_injective c3)
    rw [fin1953_val (hP a).1.1, fin1953_val (hP b).1.1] at e1
    rw [fin1953_val (hP a).1.2.1, fin1953_val (hP b).1.2.1] at e2
    rw [fin1953_val (hP a).1.2.2, fin1953_val (hP b).1.2.2] at e3
    have hDeq : L[(a : ℕ)]'(hn a) = L[(b : ℕ)]'(hn b) := Prod.ext e1 (Prod.ext e2 e3)
    exact Fin.ext ((hnd.getElem_inj (hi := hn a) (hj := hn b)).1 hDeq)
  have h := Nat.card_le_card_of_injective F hF
  rw [Nat.card_fin] at h
  exact h

end Four

section Main


theorem card_closure_commSet_ge {kt ku : Fin 1953} (h : orderOf (tvP kt * tvP ku) = 3) :
    20160 ≤ Nat.card (closure (tvP '' {k : Fin 1953 |
      Commute (tvP k) (tvP kt) ∧ Commute (tvP k) (tvP ku)})) := by
  obtain ⟨y, hyT, hykt, hyku⟩ := exists_pair_map h
  have hy : IsTvAut y⁻¹ := (isTvAut_of_mem hyT).inv
  have hyk : ∀ k : Fin 1953, (MulAut.conj y⁻¹) (tvP k) = tvP (y⁻¹ k) := fun k => by
    rw [MulAut.conj_apply]
    exact hy k
  have hkt : y⁻¹ 0 = kt := Equiv.Perm.inv_eq_iff_eq.2 hykt.symm
  have hku : y⁻¹ p31 = ku := Equiv.Perm.inv_eq_iff_eq.2 hyku.symm
  have hle : (closure (tvP '' commSet 0 p31)).map (MulAut.conj y⁻¹).toMonoidHom ≤
      closure (tvP '' commSet kt ku) := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨y⁻¹ k, ⟨?_, ?_⟩, (hyk k).symm⟩
    · have := hk.1.map (MulAut.conj y⁻¹)
      rwa [hyk, hyk, hkt] at this
    · have := hk.2.map (MulAut.conj y⁻¹)
      rwa [hyk, hyk, hku] at this
  calc 20160 ≤ Nat.card (closure (tvP '' commSet 0 p31)) := four_card_ge
    _ = Nat.card ((closure (tvP '' commSet 0 p31)).map (MulAut.conj y⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective).symm
    _ ≤ Nat.card (closure (tvP '' commSet kt ku)) := Subgroup.card_le_of_le hle

end Main

end CFSG.GF2Type.SmithTypeE.LMod
