module

public import CFSG.CGT.PushingUpLit.BHS.FourSymA
public import CFSG.GH74.GLS.Basic
import CFSG.Timmesfeld.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Trv

public section

namespace CFSG.GroupTheory

open CFSG.CGT.PushingUpLit.BHS (IsTransv)

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem transv_rel_of_odd (hW : ∀ w : W, w ^ 2 = 1) {e f : MulAut W} {ue uf : W}
    (he : IsTransv e ue) (hf : IsTransv f uf) (hef : e ≠ f) (hodd : Odd (orderOf (e * f))) :
    e * f ≠ f * e ∧ e uf = uf * ue ∧ f ue = ue * uf ∧ ue ≠ uf := by
  have hnc : e * f ≠ f * e := by
    intro hc
    have h2 : (e * f) ^ 2 = 1 := by
      calc (e * f) ^ 2 = e * (f * e) * f := by rw [pow_two]; simp only [mul_assoc]
        _ = e * (e * f) * f := by rw [hc]
        _ = 1 := by rw [← mul_assoc, he.sq, one_mul, hf.sq]
    obtain ⟨k, hk⟩ := hodd
    have hle := Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one h2)
    have h1 : orderOf (e * f) = 1 := by omega
    apply hef
    rw [eq_inv_of_mul_eq_one_right (orderOf_eq_one_iff.1 h1), inv_eq_of_mul_eq_one_right he.sq]
  obtain ⟨g, hg, hgf⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul he.sq hf.sq hodd
  have hg' : g ∈ Subgroup.zpowers e ⊔ Subgroup.zpowers f := by
    refine (Subgroup.closure_le _).2 ?_ hg
    rintro x (rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact ⟨hnc, he.rel_of_conj hW hf hnc hg' hgf.symm⟩

omit [Finite W] in
private theorem transv_fourth (hW : ∀ w : W, w ^ 2 = 1) {e f g h : MulAut W} {ue uf ug : W}
    (hue : IsTransv e ue) (huf : IsTransv f uf) (hug : IsTransv g ug)
    (hh : IsTransv h (ue * uf)) (hge : g ≠ e) (hgf : g ≠ f) (hgh : g ≠ h)
    (h1 : Odd (orderOf (g * e))) (h2 : Odd (orderOf (g * f))) (h3 : Odd (orderOf (g * h))) :
    False := by
  have e1 := (transv_rel_of_odd hW hug hue hge h1).2.1
  have e2 := (transv_rel_of_odd hW hug huf hgf h2).2.1
  have e3 := (transv_rel_of_odd hW hug hh hgh h3).2.1
  have hug2 : ug * ug = 1 := by rw [← pow_two]; exact hW ug
  have key : ue * uf * ug = ue * uf * 1 := by
    rw [mul_one, ← e3, map_mul, e1, e2, mul_mul_mul_comm, hug2, mul_one]
  exact hug.ne (mul_left_cancel key)

omit [Finite W] in
private theorem conj_mul_conj_mem {a : MulAut W} (ha2 : a * a = 1) {R : Subgroup (MulAut W)}
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W))) {r s : MulAut W} (hr : r ∈ R)
    (hs : s ∈ R) : r * a * r⁻¹ * (s * a * s⁻¹) ∈ R := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have h1 : a * (r⁻¹ * s) * a⁻¹ ∈ R :=
    (Subgroup.mem_normalizer_iff.1 haR _).1 (R.mul_mem (R.inv_mem hr) hs)
  have : r * a * r⁻¹ * (s * a * s⁻¹) = r * (a * (r⁻¹ * s) * a⁻¹) * s⁻¹ := by
    rw [hai]; group
  rw [this]
  exact R.mul_mem (R.mul_mem hr h1) (R.inv_mem hs)

omit [Finite W] in
private theorem mul_mul_mem_conj {a : MulAut W} (ha2 : a * a = 1) {R : Subgroup (MulAut W)}
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W))) {e f : MulAut W}
    (he : e ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}) (hf : f ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x})
    (hf2 : f * f = 1) : f * e * f ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x} := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf2
  have hefR : e * f ∈ R := by
    obtain ⟨r, hr, rfl⟩ := he
    obtain ⟨s, hs, rfl⟩ := hf
    exact conj_mul_conj_mem ha2 haR hr hs
  obtain ⟨r, hr, hre⟩ := he
  refine ⟨(e * f)⁻¹ * r, R.mul_mem (R.inv_mem hefR) hr, ?_⟩
  calc (e * f)⁻¹ * r * a * ((e * f)⁻¹ * r)⁻¹ = (e * f)⁻¹ * (r * a * r⁻¹) * (e * f) := by
        group
    _ = f * e * f := by rw [hre, mul_inv_rev, hfi]; group

omit [Finite W] in
private theorem conj_eq_triple (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} {u : W}
    (ha : IsTransv a u) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W))) {e f : MulAut W}
    (he : e ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}) (hf : f ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x})
    (hef : e ≠ f) :
    {x | ∃ r ∈ R, r * a * r⁻¹ = x} = {e, f, f * e * f} ∧ f * e * f ≠ e ∧ f * e * f ≠ f := by
  have hodd : ∀ x ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}, ∀ y ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x},
      Odd (orderOf (x * y)) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
    exact Odd.of_dvd_nat hR (R.orderOf_dvd_natCard (conj_mul_conj_mem ha.sq haR hr hs))
  have htr : ∀ x ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}, ∃ v, IsTransv x v := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r u, ha.conj r⟩
  obtain ⟨ue, hue⟩ := htr e he
  obtain ⟨uf, huf⟩ := htr f hf
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right huf.sq
  obtain ⟨hnc, -, hf_ue, -⟩ := transv_rel_of_odd hW hue huf hef (hodd e he f hf)
  have hhE := mul_mul_mem_conj ha.sq haR he hf huf.sq
  have hhtr : IsTransv (f * e * f) (ue * uf) := by
    have := hue.conj f
    rwa [hfi, hf_ue] at this
  have hhe : f * e * f ≠ e := by
    intro h
    apply hnc
    calc e * f = f * (f * e * f) := by rw [← mul_assoc, ← mul_assoc, huf.sq, one_mul]
      _ = f * e := by rw [h]
  have hhf : f * e * f ≠ f := by
    intro h
    have h1 : f * e = 1 := mul_right_cancel (h.trans (one_mul f).symm)
    exact hef (by rw [eq_inv_of_mul_eq_one_right h1, hfi])
  refine ⟨Set.Subset.antisymm ?_ ?_, hhe, hhf⟩
  · intro g hg
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
    push Not at hcon
    obtain ⟨hge, hgf, hgh⟩ := hcon
    obtain ⟨ug, hug⟩ := htr g hg
    exact transv_fourth hW hue huf hug hhtr hge hgf hgh (hodd g hg e he) (hodd g hg f hf)
      (hodd g hg _ hhE)
  · rintro x (rfl | rfl | rfl)
    · exact he
    · exact hf
    · exact hhE

omit [Finite W] in
private theorem ncard_conj_eq_three_of_ne (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} {u : W}
    (ha : IsTransv a u) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W))) {f : MulAut W}
    (hf : f ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}) (hfa : f ≠ a) :
    {x | ∃ r ∈ R, r * a * r⁻¹ = x}.ncard = 3 := by
  have haE : a ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x} := ⟨1, R.one_mem, by group⟩
  obtain ⟨hE, hhe, hhf⟩ := conj_eq_triple hW ha hR haR haE hf hfa.symm
  exact Set.ncard_eq_three.2 ⟨a, f, f * a * f, hfa.symm, hhe.symm, hhf.symm, hE⟩

omit [Finite W] in
theorem ncard_conj_le_three (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} {u : W}
    (ha : IsTransv a u) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W))) :
    {x | ∃ r ∈ R, r * a * r⁻¹ = x}.ncard ≤ 3 := by
  by_cases h : ∃ f ∈ {x | ∃ r ∈ R, r * a * r⁻¹ = x}, f ≠ a
  · obtain ⟨f, hf, hfa⟩ := h
    exact (ncard_conj_eq_three_of_ne hW ha hR haR hf hfa).le
  · push Not at h
    have hsub : {x | ∃ r ∈ R, r * a * r⁻¹ = x} ⊆ {a} := h
    calc {x | ∃ r ∈ R, r * a * r⁻¹ = x}.ncard ≤ ({a} : Set (MulAut W)).ncard :=
          Set.ncard_le_ncard hsub (Set.finite_singleton a)
      _ ≤ 3 := by rw [Set.ncard_singleton]; omega

omit [Finite W] in
theorem ncard_conj_eq_three (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W} {u : W}
    (ha : IsTransv a u) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W)))
    (hnc : a ∉ Subgroup.centralizer (R : Set (MulAut W))) :
    {x | ∃ r ∈ R, r * a * r⁻¹ = x}.ncard = 3 := by
  obtain ⟨r, hr, hra⟩ : ∃ r ∈ R, r * a ≠ a * r := by
    by_contra hcon
    push Not at hcon
    exact hnc (Subgroup.mem_centralizer_iff.2 hcon)
  refine ncard_conj_eq_three_of_ne hW ha hR haR ⟨r, hr, rfl⟩ fun h => hra ?_
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

private theorem odd_card_zpowers_sup {G : Type*} [Group G] {R : Subgroup G} {c : G}
    (hR : Odd (Nat.card R)) (hc : Odd (orderOf c))
    (hcR : c ∈ Subgroup.normalizer (R : Set G)) : Odd (Nat.card ↥(Subgroup.zpowers c ⊔ R)) := by
  have hLE : Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.2 hcR
  have := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
  have hidx : R.relIndex (Subgroup.zpowers c ⊔ R) = R.relIndex (Subgroup.zpowers c) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers c) R hLE).toEquiv.symm
  have hcard := Subgroup.relIndex_mul_card R (Subgroup.zpowers c ⊔ R)
  rw [inf_of_le_left le_sup_right, hidx] at hcard
  rw [← hcard]
  refine Nat.odd_mul.2 ⟨Odd.of_dvd_nat hc ?_, hR⟩
  rw [← Nat.card_zpowers]
  exact Subgroup.relIndex_dvd_card R (Subgroup.zpowers c)

theorem mul_mem_of_orderOf_mul_eq_three (hW : ∀ w : W, w ^ 2 = 1) {a b : MulAut W} {u : W}
    (ha : IsTransv a u) (hb : b * b = 1) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W)))
    (hbR : b ∈ Subgroup.normalizer (R : Set (MulAut W)))
    (hnc : a ∉ Subgroup.centralizer (R : Set (MulAut W))) (h3 : orderOf (a * b) = 3) :
    a * b ∈ R := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.sq
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have ha' : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha.sq, one_mul]
  have hb' : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  obtain ⟨c, hc⟩ : ∃ c, c = a * b := ⟨_, rfl⟩
  rw [← hc] at h3 ⊢
  have hcR : c ∈ Subgroup.normalizer (R : Set (MulAut W)) := hc ▸ Subgroup.mul_mem _ haR hbR
  have hcinv : c⁻¹ = b * a := by rw [hc, mul_inv_rev, hai, hbi]
  have hac : a * c * a⁻¹ = c⁻¹ := by rw [hcinv, hc, hai, ← mul_assoc, ha.sq, one_mul]
  have hcab : c * a * c⁻¹ = b := by
    have hc3 : c * (c * c) = 1 := by rw [← pow_three, ← h3, pow_orderOf_eq_one]
    rw [inv_eq_of_mul_eq_one_right hc3, hc]
    simp only [mul_assoc, ha', hb']
  have hR' := odd_card_zpowers_sup hR (h3 ▸ (by decide : Odd 3)) hcR
  have haR' : a ∈ Subgroup.normalizer ((Subgroup.zpowers c ⊔ R : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
    refine Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.2 ⟨?_, haR⟩)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change Subgroup.zpowers (a * c * a⁻¹) = _
    rw [hac, Subgroup.zpowers_inv]
  have hsub : {x | ∃ r ∈ R, r * a * r⁻¹ = x} ⊆
      {x | ∃ r ∈ Subgroup.zpowers c ⊔ R, r * a * r⁻¹ = x} := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, Subgroup.mem_sup_right hr, rfl⟩
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by rw [ncard_conj_eq_three hW ha hR haR hnc]; exact ncard_conj_le_three hW ha hR' haR')
    (Set.toFinite _)
  have hbE : b ∈ {x | ∃ r ∈ Subgroup.zpowers c ⊔ R, r * a * r⁻¹ = x} :=
    ⟨c, Subgroup.mem_sup_left (Subgroup.mem_zpowers c), hcab⟩
  rw [← heq] at hbE
  obtain ⟨r, hr, rfl⟩ := hbE
  rw [hc, show a * (r * a * r⁻¹) = a * r * a⁻¹ * r⁻¹ by rw [hai]; group]
  exact R.mul_mem ((Subgroup.mem_normalizer_iff.1 haR r).1 hr) (R.inv_mem hr)

private theorem two_or_mem (hW : ∀ w : W, w ^ 2 = 1) {a b : MulAut W} {u v : W}
    (ha : IsTransv a u) (hb : IsTransv b v) {R : Subgroup (MulAut W)} (hR : Odd (Nat.card R))
    (haR : a ∈ Subgroup.normalizer (R : Set (MulAut W)))
    (hbR : b ∈ Subgroup.normalizer (R : Set (MulAut W)))
    (hnc : a ∉ Subgroup.centralizer (R : Set (MulAut W))) :
    (∃ k : ℕ, (a * b) ^ 2 ^ k = 1) ∨ a * b ∈ R := by
  by_cases huv : u = v
  · subst huv
    have hcomm : a * b = b * a := (ha.comm_iff hW hb).2 ⟨ha.apply_centre hW, hb.apply_centre hW⟩
    refine Or.inl ⟨1, ?_⟩
    calc (a * b) ^ 2 ^ 1 = a * (b * a) * b := by rw [pow_one, pow_two]; simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hcomm]
      _ = 1 := by rw [← mul_assoc, ha.sq, one_mul, hb.sq]
  · have hE : ∀ x : W, x * x = 1 := fun x => by rw [← pow_two]; exact hW x
    rcases CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c1_G47_two_transv hE ha.ne hb.ne huv
        ha.step hb.step ha.ne_one hb.ne_one with h | h | h
    · exact Or.inl ⟨1, by rw [pow_one, ← h, pow_orderOf_eq_one]⟩
    · exact Or.inr (mul_mem_of_orderOf_mul_eq_three hW ha hb.sq hR haR hbR hnc h)
    · exact Or.inl ⟨2, by rw [show 2 ^ 2 = 4 from rfl, ← h, pow_orderOf_eq_one]⟩

theorem mem_inSubgroup_pPrimePCore_of_isTransv (hW : ∀ w : W, w ^ 2 = 1)
    {Y R : Subgroup (MulAut W)} {a : MulAut W} {u : W} (ha : IsTransv a u) (haY : a ∈ Y)
    (hRY : R ≤ Y) (hRn : (R.subgroupOf Y).Normal) (hR : Odd (Nat.card R))
    (hnc : a ∉ Subgroup.centralizer (R : Set (MulAut W))) :
    a ∈ CFSG.inSubgroup (CFSG.GH74.GLS.pPrimePCore 2) Y := by
  have : Finite (MulAut W) := MulEquiv.finite_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ g ∈ Y, g ∈ Subgroup.normalizer (R : Set (MulAut W)) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    exact Subgroup.mem_subgroupOf.1
      (hRn.conj_mem ⟨n, hRY hn⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, hg⟩)
  have hRle : R.subgroupOf Y ≤ CFSG.pPrimeCore 2 ↥Y := by
    refine le_sSup ⟨hRn, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv]
    exact Nat.coprime_two_left.2 hR
  have hA2 : (⟨a, haY⟩ : ↥Y) * ⟨a, haY⟩ = 1 := Subtype.ext ha.sq
  refine ⟨⟨a, haY⟩, ?_, rfl⟩
  rw [CFSG.GH74.GLS.pPrimePCore, SetLike.mem_coe, Subgroup.mem_comap,
    CFSG.BaerSuzuki.baer_suzuki_iff]
  intro gbar
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 2 ↥Y) gbar
  rw [← map_inv, ← map_mul, ← map_mul]
  have hB2 : (g * ⟨a, haY⟩ * g⁻¹ : ↥Y) * (g * ⟨a, haY⟩ * g⁻¹) = 1 := by
    rw [show g * ⟨a, haY⟩ * g⁻¹ * (g * ⟨a, haY⟩ * g⁻¹) = g * (⟨a, haY⟩ * ⟨a, haY⟩) * g⁻¹ by
      group, hA2, mul_one, mul_inv_cancel]
  rcases two_or_mem hW ha (ha.conj (g : MulAut W)) hR (hnorm a haY)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnorm g g.2) (hnorm a haY))
        (Subgroup.inv_mem _ (hnorm g g.2))) hnc with ⟨k, hk⟩ | hmem
  · rw [← Set.image_pair, ← MonoidHom.map_closure]
    exact (CFSG.Timmesfeld.isPGroup_two_closure_pair hA2 hB2 (k := k) (Subtype.ext hk)).map _
  · have hq : QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥Y) ⟨a, haY⟩ =
        QuotientGroup.mk' (CFSG.pPrimeCore 2 ↥Y) (g * ⟨a, haY⟩ * g⁻¹) := by
      refine QuotientGroup.eq.2 (hRle (Subgroup.mem_subgroupOf.2 ?_))
      rw [inv_eq_of_mul_eq_one_right hA2]
      exact hmem
    rw [← hq]
    refine CFSG.Timmesfeld.isPGroup_two_closure_pair (k := 0) ?_ ?_ ?_ <;>
      rw [← map_mul, hA2, map_one]
    rw [pow_zero, pow_one]

end CFSG.GroupTheory
