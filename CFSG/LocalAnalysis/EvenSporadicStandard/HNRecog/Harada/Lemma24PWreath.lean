module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24E
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24WreathA8

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA CFSG.GH74.Uniqueness.SU.SU5

variable {G : Type} [Group G] {ι : Elem2 6 →* G} {a : G}

private theorem v6_add_self (v : V6) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem zmod_two_eq (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

private theorem coordElt_injective_of (h : Setting24 ι a) :
    Function.Injective (coordElt ι) := by
  intro u v huv
  have huv' : ι (Multiplicative.ofAdd u) = ι (Multiplicative.ofAdd v) := by
    simpa only [coordElt] using huv
  exact Multiplicative.ofAdd.injective (h.inj huv')

private theorem coordElt_commute (v w : V6) : Commute (coordElt ι v) (coordElt ι w) := by
  rw [commute_iff_eq, ← coordElt_add, ← coordElt_add, add_comm]

private theorem coordElt_smul (c : ZMod 2) (w : V6) :
    coordElt ι (c • w) = (coordElt ι w) ^ c.val := by
  rcases zmod_two_eq c with h | h
  · rw [h, zero_smul, coordElt_zero, show (0 : ZMod 2).val = 0 from ZMod.val_zero, pow_zero]
  · rw [h, one_smul, show (1 : ZMod 2).val = 1 from ZMod.val_one 2, pow_one]

private theorem coordElt_mem_E24 (h : Setting24 ι a) {v : V6} (hv : v ∈ Fix3) :
    coordElt ι v ∈ E24 ι a :=
  (mem_E24_iff h).mpr ⟨v, hv, rfl⟩

private theorem coordElt_mem_P24 (h : Setting24 ι a) {v : V6} (hv : v ∈ Fix3) :
    coordElt ι v ∈ P24 ι a :=
  E24_le_P24 (coordElt_mem_E24 h hv)

private theorem exists_involution_lift (h : Setting24 ι a) {x : G} (hxP : x ∈ P24 ι a)
    {g : Equiv.Perm V6} (hxind : Induces ι x g) (hg_sq : g * g = 1)
    (hsplit : ∀ s ∈ Fix3, g s = s → ∃ y ∈ Fix3, y + g y = s) :
    ∃ u ∈ P24 ι a, Induces ι u g ∧ u * u = 1 := by
  have hx2ind : Induces ι (x * x) (g * g) := hxind.mul hxind
  rw [hg_sq] at hx2ind
  obtain ⟨s, hs⟩ := Induces.exists_eq_coordElt h.centralizer_le hx2ind
  have hx2P : x * x ∈ P24 ι a := mul_mem hxP hxP
  have hx2range : x * x ∈ ι.range := by
    rw [hs]
    exact ⟨Multiplicative.ofAdd s, rfl⟩
  have hE : x * x ∈ E24 ι a := by
    rw [← P24_inf_range]
    exact ⟨hx2P, hx2range⟩
  obtain ⟨v, hvfix, hv_eq⟩ := (mem_E24_iff h).mp hE
  have hsv : s = v := coordElt_injective_of h (hs.symm.trans hv_eq)
  have hsfix : s ∈ Fix3 := hsv ▸ hvfix
  have hgs : g s = s := by
    have hcomm : x * coordElt ι s = coordElt ι s * x := by
      rw [← hs]; group
    have hxconj : x * coordElt ι s * x⁻¹ = coordElt ι s := by
      rw [hcomm]; group
    have h1 := hxind s
    rw [hxconj] at h1
    exact (coordElt_injective_of h h1).symm
  obtain ⟨y, hyfix, hysum⟩ := hsplit s hsfix hgs
  refine ⟨coordElt ι y * x, ?_, ?_, ?_⟩
  · exact mul_mem (coordElt_mem_P24 h hyfix) hxP
  · have hh := (induces_coordElt (ι := ι) y).mul hxind
    simpa using hh
  · have hmul := hxind y
    calc coordElt ι y * x * (coordElt ι y * x)
        = coordElt ι y * (x * coordElt ι y * x⁻¹) * (x * x) := by group
      _ = coordElt ι y * coordElt ι (g y) * coordElt ι s := by rw [hmul, hs]
      _ = coordElt ι (y + g y + s) := by rw [← coordElt_add, ← coordElt_add]
      _ = 1 := by rw [hysum, v6_add_self, coordElt_zero]

private theorem coordElt_mem_closure (h : Setting24 ι a) {e u w : G}
    (he : e = coordElt ι tv) (huind : Induces ι u uV) (hwind : Induces ι w wV) :
    ∀ v ∈ Fix3, coordElt ι v ∈ Subgroup.closure ({e, u, w} : Set G) := by
  intro v hv
  obtain ⟨c0, c1, c2, c3, hveq⟩ := Fix3_free v hv
  have heK : e ∈ Subgroup.closure ({e, u, w} : Set G) := Subgroup.subset_closure (by simp)
  have huK : u ∈ Subgroup.closure ({e, u, w} : Set G) := Subgroup.subset_closure (by simp)
  have hwK : w ∈ Subgroup.closure ({e, u, w} : Set G) := Subgroup.subset_closure (by simp)
  have h1 : coordElt ι (uV tv) = u * e * u⁻¹ := by rw [← huind tv, he]
  have h2 : coordElt ι (wV tv) = w * e * w⁻¹ := by rw [← hwind tv, he]
  have h3 : coordElt ι ((uV * wV) tv) = (u * w) * e * (u * w)⁻¹ := by
    rw [← (huind.mul hwind) tv, he]
  have hmem1 : coordElt ι (uV tv) ∈ Subgroup.closure ({e, u, w} : Set G) := by
    rw [h1]; exact mul_mem (mul_mem huK heK) (inv_mem huK)
  have hmem2 : coordElt ι (wV tv) ∈ Subgroup.closure ({e, u, w} : Set G) := by
    rw [h2]; exact mul_mem (mul_mem hwK heK) (inv_mem hwK)
  have hmem3 : coordElt ι ((uV * wV) tv) ∈ Subgroup.closure ({e, u, w} : Set G) := by
    rw [h3]; exact mul_mem (mul_mem (mul_mem huK hwK) heK) (inv_mem (mul_mem huK hwK))
  rw [hveq, coordElt_add, coordElt_add, coordElt_add,
    coordElt_smul, coordElt_smul, coordElt_smul, coordElt_smul]
  exact mul_mem (mul_mem (mul_mem
    (pow_mem (by rw [← he]; exact heK) _) (pow_mem hmem1 _))
    (pow_mem hmem2 _)) (pow_mem hmem3 _)

private theorem P24_le_closure (h : Setting24 ι a) {e u w : G}
    (he : e = coordElt ι tv) (huind : Induces ι u uV) (hwind : Induces ι w wV)
    (huP : u ∈ P24 ι a) (hwP : w ∈ P24 ι a)
    (hcoord : ∀ v ∈ Fix3, coordElt ι v ∈ Subgroup.closure ({e, u, w} : Set G)) :
    P24 ι a ≤ Subgroup.closure ({e, u, w} : Set G) := by
  intro x hxP
  have hxindSub : x ∈ indSub ι Vg := by
    have hx := hxP
    change x ∈ indSub ι Vg ⊓ centralizer ({a} : Set G) at hx
    exact hx.1
  obtain ⟨g, hgVg, hxind⟩ := mem_indSub.mp hxindSub
  have hex : ∃ m, m ∈ Subgroup.closure ({e, u, w} : Set G) ∧ m ∈ P24 ι a ∧ Induces ι m g := by
    rcases mem_Vg_iff.mp hgVg with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, one_mem _, induces_one⟩
    · exact ⟨u, Subgroup.subset_closure (by simp), huP, huind⟩
    · exact ⟨w, Subgroup.subset_closure (by simp), hwP, hwind⟩
    · exact ⟨u * w,
        mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)),
        mul_mem huP hwP, huind.mul hwind⟩
  obtain ⟨m, hmK, hmP, hmind⟩ := hex
  have hxmind : Induces ι (x * m⁻¹) 1 := by
    have hh := hxind.mul hmind.inv
    rwa [mul_inv_cancel] at hh
  obtain ⟨v, hv⟩ := Induces.exists_eq_coordElt h.centralizer_le hxmind
  have hxmP : x * m⁻¹ ∈ P24 ι a := mul_mem hxP (inv_mem hmP)
  have hxmrange : x * m⁻¹ ∈ ι.range := by
    rw [hv]
    exact ⟨Multiplicative.ofAdd v, rfl⟩
  have hE : x * m⁻¹ ∈ E24 ι a := by
    rw [← P24_inf_range]
    exact ⟨hxmP, hxmrange⟩
  obtain ⟨v', hv'fix, hv'eq⟩ := (mem_E24_iff h).mp hE
  have hvv : v = v' := coordElt_injective_of h (hv.symm.trans hv'eq)
  have hvfix : v ∈ Fix3 := hvv ▸ hv'fix
  have hvK : coordElt ι v ∈ Subgroup.closure ({e, u, w} : Set G) := hcoord v hvfix
  have hxeq : x = (x * m⁻¹) * m := by group
  rw [hxeq, hv]
  exact mul_mem hvK hmK

private theorem conj_comm_of_induces {e x y : G} (he : e = coordElt ι tv)
    {γ δ : Equiv.Perm V6} (hx : Induces ι x γ) (hy : Induces ι y δ) :
    Commute (x * e * x⁻¹) (y * e * y⁻¹) := by
  rw [he, hx tv, hy tv]
  exact coordElt_commute (γ tv) (δ tv)

theorem isA8Type_P24 (h : Setting24 ι a) : IsA8Type ↥(P24 ι a) := by
  set e : G := coordElt ι tv with he
  have heP : e ∈ P24 ι a := coordElt_mem_P24 h tv_mem_Fix3
  have he_sq : e * e = 1 := by
    rw [he, ← coordElt_add, v6_add_self, coordElt_zero]
  obtain ⟨u0, hu0P, hu0ind⟩ := exists_lift_P24 h (mem_Vg_iff.mpr (Or.inr (Or.inl rfl)))
  obtain ⟨u1, hu1P, hu1ind, hu1_sq⟩ :=
    exists_involution_lift h hu0P hu0ind uV_wV_facts.1 Fix3_split_u
  obtain ⟨w0, hw0P, hw0ind⟩ :=
    exists_lift_P24 h (mem_Vg_iff.mpr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨w1, hw1P, hw1ind, hw1_sq⟩ :=
    exists_involution_lift h hw0P hw0ind uV_wV_facts.2.1 Fix3_split_w
  have hu1inv : u1⁻¹ = u1 := inv_eq_of_mul_eq_one_left hu1_sq
  have hw1inv : w1⁻¹ = w1 := inv_eq_of_mul_eq_one_left hw1_sq
  let κ : G := u1 * w1 * u1 * w1
  have huw_sq : (uV * wV) * (uV * wV) = 1 := by
    have hc : wV * uV = uV * wV := (uV_wV_facts.2.2.1).symm
    calc (uV * wV) * (uV * wV)
        = uV * (wV * uV) * wV := by group
      _ = uV * (uV * wV) * wV := by rw [hc]
      _ = (uV * uV) * (wV * wV) := by group
      _ = 1 := by rw [uV_wV_facts.1, uV_wV_facts.2.1, one_mul]
  have hκind : Induces ι κ 1 := by
    have h' : Induces ι ((u1 * w1) * (u1 * w1)) 1 := by
      have hh := (hu1ind.mul hw1ind).mul (hu1ind.mul hw1ind)
      rwa [huw_sq] at hh
    change Induces ι (u1 * w1 * u1 * w1) 1
    simpa only [mul_assoc] using h'
  obtain ⟨r, hr⟩ := Induces.exists_eq_coordElt h.centralizer_le hκind
  have hκP : κ ∈ P24 ι a := by
    change u1 * w1 * u1 * w1 ∈ P24 ι a
    exact mul_mem (mul_mem (mul_mem hu1P hw1P) hu1P) hw1P
  have hκrange : κ ∈ ι.range := by
    rw [hr]; exact ⟨Multiplicative.ofAdd r, rfl⟩
  have hEκ : κ ∈ E24 ι a := by
    rw [← P24_inf_range]
    exact ⟨hκP, hκrange⟩
  obtain ⟨r', hr'fix, hr'eq⟩ := (mem_E24_iff h).mp hEκ
  have hrr : r = r' := coordElt_injective_of h (hr.symm.trans hr'eq)
  have hrfix : r ∈ Fix3 := hrr ▸ hr'fix
  have hκsq : κ * κ = 1 := by
    have hcr : coordElt ι r * coordElt ι r = 1 := by
      rw [← coordElt_add, v6_add_self, coordElt_zero]
    simpa only [hr] using hcr
  have huk : u1 * κ * u1⁻¹ = κ := by
    change u1 * (u1 * w1 * u1 * w1) * u1⁻¹ = u1 * w1 * u1 * w1
    calc u1 * (u1 * w1 * u1 * w1) * u1⁻¹
        = (u1 * u1) * (w1 * u1 * w1 * u1⁻¹) := by group
      _ = w1 * u1 * w1 * u1 := by rw [hu1_sq, one_mul, hu1inv]
      _ = (u1 * w1 * u1 * w1)⁻¹ := by
            simp only [mul_inv_rev, inv_inv, hu1inv, hw1inv]
            group
      _ = u1 * w1 * u1 * w1 := inv_eq_of_mul_eq_one_left hκsq
  have hwk : w1 * κ * w1⁻¹ = κ := by
    change w1 * (u1 * w1 * u1 * w1) * w1⁻¹ = u1 * w1 * u1 * w1
    calc w1 * (u1 * w1 * u1 * w1) * w1⁻¹
        = (w1 * u1 * w1 * u1) * (w1 * w1⁻¹) := by group
      _ = w1 * u1 * w1 * u1 := by rw [mul_inv_cancel, mul_one]
      _ = (u1 * w1 * u1 * w1)⁻¹ := by
            simp only [mul_inv_rev, inv_inv, hu1inv, hw1inv]
            group
      _ = u1 * w1 * u1 * w1 := inv_eq_of_mul_eq_one_left hκsq
  have huVr : uV r = r := by
    have h1 := hu1ind r
    rw [← hr, huk] at h1
    exact (coordElt_injective_of h (hr.symm.trans h1)).symm
  have hwVr : wV r = r := by
    have h1 := hw1ind r
    rw [← hr, hwk] at h1
    exact (coordElt_injective_of h (hr.symm.trans h1)).symm
  obtain ⟨y, hyfix, huVy, hysum⟩ := Fix3_split_uw r hrfix huVr hwVr
  let u : G := coordElt ι y * u1
  have huP : u ∈ P24 ι a := by
    change coordElt ι y * u1 ∈ P24 ι a
    exact mul_mem (coordElt_mem_P24 h hyfix) hu1P
  have huind : Induces ι u uV := by
    change Induces ι (coordElt ι y * u1) uV
    have hh := (induces_coordElt (ι := ι) y).mul hu1ind
    simpa using hh
  have hcy_sq : coordElt ι y * coordElt ι y = 1 := by
    rw [← coordElt_add, v6_add_self, coordElt_zero]
  have hu_sq : u * u = 1 := by
    change (coordElt ι y * u1) * (coordElt ι y * u1) = 1
    have hmul := hu1ind y
    calc (coordElt ι y * u1) * (coordElt ι y * u1)
        = coordElt ι y * (u1 * coordElt ι y * u1⁻¹) * (u1 * u1) := by group
      _ = coordElt ι y * coordElt ι (uV y) * 1 := by rw [hmul, hu1_sq]
      _ = coordElt ι (y + uV y) := by rw [← coordElt_add, mul_one]
      _ = coordElt ι 0 := by rw [huVy, v6_add_self]
      _ = 1 := coordElt_zero ι
  have hcyinv : (coordElt ι y)⁻¹ = coordElt ι y := inv_eq_of_mul_eq_one_left hcy_sq
  have huw_comm : u * w1 = w1 * u := by
    change (coordElt ι y * u1) * w1 = w1 * (coordElt ι y * u1)
    have h1 : (coordElt ι y * u1) * w1 * (coordElt ι y * u1)⁻¹ * w1⁻¹ = 1 := by
      have hwcy : w1 * coordElt ι y * w1 = coordElt ι (wV y) := by
        simpa only [hw1inv] using hw1ind y
      calc (coordElt ι y * u1) * w1 * (coordElt ι y * u1)⁻¹ * w1⁻¹
          = coordElt ι y * (u1 * w1 * u1) * coordElt ι y * w1 := by
              rw [mul_inv_rev, hu1inv, hw1inv, hcyinv]
              group
        _ = coordElt ι y * (κ * w1) * coordElt ι y * w1 := by
              rw [show u1 * w1 * u1 = κ * w1 from by
                change u1 * w1 * u1 = (u1 * w1 * u1 * w1) * w1
                rw [show (u1 * w1 * u1 * w1) * w1 = (u1 * w1 * u1) * (w1 * w1) from
                  by group, hw1_sq, mul_one]]
        _ = coordElt ι y * κ * (w1 * coordElt ι y * w1) := by group
        _ = coordElt ι y * κ * coordElt ι (wV y) := by rw [hwcy]
        _ = coordElt ι (y + r + wV y) := by rw [hr, ← coordElt_add, ← coordElt_add]
        _ = 1 := by
              rw [show y + r + wV y = 0 from by
                    rw [show y + r + wV y = r + (y + wV y) from by abel,
                      hysum, v6_add_self],
                  coordElt_zero]
    calc (coordElt ι y * u1) * w1
        = (coordElt ι y * u1) * w1 * (coordElt ι y * u1)⁻¹ * w1⁻¹ *
            (w1 * (coordElt ι y * u1)) := by group
      _ = 1 * (w1 * (coordElt ι y * u1)) := by rw [h1]
      _ = w1 * (coordElt ι y * u1) := by rw [one_mul]
  have hcoord : ∀ v ∈ Fix3, coordElt ι v ∈ Subgroup.closure ({e, u, w1} : Set G) :=
    coordElt_mem_closure h he huind hw1ind
  have hPK : P24 ι a ≤ Subgroup.closure ({e, u, w1} : Set G) :=
    P24_le_closure h he huind hw1ind huP hw1P hcoord
  have hgen : Subgroup.closure ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} : Set ↥(P24 ι a)) = ⊤ := by
    let f : ↥(P24 ι a) →* G := (P24 ι a).subtype
    have himg : f '' ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} : Set ↥(P24 ι a)) =
        ({e, u, w1} : Set G) := by
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      rfl
    have hmap : (Subgroup.closure ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} :
        Set ↥(P24 ι a))).map f = Subgroup.closure ({e, u, w1} : Set G) := by
      rw [MonoidHom.map_closure, himg]
    have hker : f.ker ≤ Subgroup.closure ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} :
        Set ↥(P24 ι a)) := by
      rw [f.ker_eq_bot Subtype.coe_injective]
      exact bot_le
    calc Subgroup.closure ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} : Set ↥(P24 ι a))
        = Subgroup.comap f
            ((Subgroup.closure ({⟨e, heP⟩, ⟨u, huP⟩, ⟨w1, hw1P⟩} :
              Set ↥(P24 ι a))).map f) :=
            (Subgroup.comap_map_eq_self hker).symm
      _ = Subgroup.comap f (Subgroup.closure ({e, u, w1} : Set G)) := by rw [hmap]
      _ = ⊤ := by
            rw [eq_top_iff]
            intro x _
            exact hPK x.2
  refine isA8Type_of_wreathData (P := ↥(P24 ι a))
    ⟨card_P24 h, hgen, Subtype.ext he_sq, Subtype.ext hu_sq,
      Subtype.ext hw1_sq, Subtype.ext huw_comm, ?_⟩
  · intro g hg h' hh
    have h_ind_of : ∀ z ∈ ({1, ⟨u, huP⟩, ⟨w1, hw1P⟩,
        ⟨u, huP⟩ * ⟨w1, hw1P⟩} : Set ↥(P24 ι a)),
        ∃ γ : Equiv.Perm V6, Induces ι (z : G) γ := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨1, induces_one⟩
      · exact ⟨uV, by simpa using huind⟩
      · exact ⟨wV, by simpa using hw1ind⟩
      · exact ⟨uV * wV, by simpa using huind.mul hw1ind⟩
    obtain ⟨γ, hgind⟩ := h_ind_of g hg
    obtain ⟨δ, hhind⟩ := h_ind_of h' hh
    have hcomm : ((g : G) * e * (g : G)⁻¹) * ((h' : G) * e * (h' : G)⁻¹) =
        ((h' : G) * e * (h' : G)⁻¹) * ((g : G) * e * (g : G)⁻¹) :=
      conj_comm_of_induces (G := G) he hgind hhind
    rw [commute_iff_eq]
    exact Subtype.ext hcomm

end CFSG.EvenSporadicStandard.HNRecog.Harada
