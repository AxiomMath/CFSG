module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35LMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35YL

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_YL (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem add_self_add_YL (v u : V) : v + (v + u) = u := by
  rw [← add_assoc, add_self_YL, zero_add]

theorem zmod2_cases_YL : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem apply_eq_of_fix_of_pow_three_YL [FiniteDimensional (ZMod 2) V] {g : V ≃ₗ[ZMod 2] V}
    (h3 : g ^ 3 = 1) {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2)
    (hgU : ∀ v ∈ U, g v ∈ U) {u : V} (huU : u ∈ U) (hu0 : u ≠ 0) (hgu : g u = u) :
    ∀ v ∈ U, g v = v := by
  intro v hvU
  by_cases hv0 : v = 0
  · rw [hv0, map_zero]
  by_cases hvu : v = u
  · rw [hvu, hgu]
  have hli : LinearIndependent (ZMod 2) ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod2_cases_YL s with rfl | rfl <;> rcases zmod2_cases_YL t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst hv0
    · simp at hst
      exact absurd hst hu0
    · simp only [one_smul] at hst
      have huv : u = v := by
        have h := congrArg (· + v) hst
        simpa only [add_assoc, add_self_YL, add_zero, zero_add] using h
      exact absurd huv.symm hvu
  have hspan : Submodule.span (ZMod 2) {u, v} = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact huU
      · exact hvU
    · rw [hU2]
      have hr : Set.range ![u, v] = {u, v} := by
        ext x
        simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      have := finrank_span_eq_card hli
      rw [hr] at this
      simpa using this
  have hgv : g v ∈ Submodule.span (ZMod 2) {u, v} := hspan ▸ hgU v hvU
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hgv
  have hg3 : g (g (g v)) = v := by
    have h := LinearEquiv.congr_fun h3 v
    rwa [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
  rcases zmod2_cases_YL a with rfl | rfl <;> rcases zmod2_cases_YL b with rfl | rfl
  · simp only [zero_smul, add_zero] at hab
    exact absurd (g.injective (hab.symm.trans (map_zero g).symm)) hv0
  · simpa using hab.symm
  · simp only [one_smul, zero_smul, add_zero] at hab
    exact absurd (g.injective (hab.symm.trans hgu.symm)) hvu
  · simp only [one_smul] at hab
    have h2 : g (g v) = v := by
      rw [← hab, map_add, hgu, ← hab, ← add_assoc, add_self_YL, zero_add]
    rw [h2, ← hab] at hg3
    exact absurd (by simpa using congrArg (· - v) hg3) hu0

theorem map_mem_commSpace_of_commute_YL {g α : V ≃ₗ[ZMod 2] V} (h : g * α = α * g) {x : V}
    (hx : x ∈ commSpace α) : g x ∈ commSpace α := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hx
  refine mem_commSpace.mpr ⟨g w, ?_⟩
  have e := LinearEquiv.congr_fun h w
  simp only [LinearEquiv.mul_apply] at e
  rw [map_sub, e]

variable {q : QuadraticForm (ZMod 2) V}

theorem polar_map_YL {y : V ≃ₗ[ZMod 2] V} (hy : ∀ v, q (y v) = q v) (a b : V) :
    polar q (y a) (y b) = polar q a b := by
  simp only [polar, ← map_add, hy]

theorem exists_fix_of_orderOf_eq_four_YL [FiniteDimensional (ZMod 2) V]
    (hq : q.polarBilin.Nondegenerate) {α β y : V ≃ₗ[ZMod 2] V} (hα : IsTypeA q α 2)
    (hβ : IsTypeA q β 2) (h4 : orderOf (α * β) = 4) (hy : ∀ v, q (y v) = q v)
    (hyα : y * α = α * y) (hyβ : y * β = β * y) :
    ∃ a ∈ commSpace α, a ≠ 0 ∧ y a = a := by
  obtain ⟨-, hA, a', ha', b', hb', hab'⟩ := (orderOf_mul_eq_four_iff_of_isTypeA hq hα hβ).mp h4
  set A := commSpace α ⊓ LinearMap.BilinForm.orthogonal q.polarBilin (commSpace β) with hAdef
  have hyinv : y⁻¹ * β = β * y⁻¹ := (Commute.inv_left (show Commute y β from hyβ)).eq
  have hyA : ∀ x ∈ A, y x ∈ A := by
    intro x hx
    obtain ⟨hxα, hxβ⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨map_mem_commSpace_of_commute_YL hyα hxα, ?_⟩
    rw [OrthoF2.mem_orthogonal_iff_polar] at hxβ ⊢
    intro w hw
    have hw' : y⁻¹ w ∈ commSpace β := map_mem_commSpace_of_commute_YL hyinv hw
    have e : y (y⁻¹ w) = w := y.apply_symm_apply w
    rw [← e, polar_map_YL hy]
    exact hxβ _ hw'
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  refine ⟨a, (Submodule.mem_inf.mp haA).1, ha0, ?_⟩
  by_contra hya
  have hyaA := hyA a haA
  have hya0 : y a ≠ 0 := fun h => ha0 (y.injective (h.trans (map_zero y).symm))
  have hli : LinearIndependent (ZMod 2) ![a, y a] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases zmod2_cases_YL s with rfl | rfl <;> rcases zmod2_cases_YL t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst
      exact absurd hst ha0
    · simp at hst
      exact absurd hst ha0
    · simp only [one_smul] at hst
      have h' : a = y a := by
        have h := congrArg (· + y a) hst
        simpa only [add_assoc, add_self_YL, add_zero, zero_add] using h
      exact absurd h'.symm hya
  have hle : Submodule.span (ZMod 2) {a, y a} ≤ A := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact haA
    · exact hyaA
  have hspan : Submodule.span (ZMod 2) {a, y a} = commSpace α := by
    refine Submodule.eq_of_le_of_finrank_eq (hle.trans inf_le_left) ?_
    rw [hα.2.2.2.1]
    have hr : Set.range ![a, y a] = {a, y a} := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    have := finrank_span_eq_card hli
    rw [hr] at this
    simpa using this
  have ha'A : a' ∈ A := hle (hspan ▸ ha')
  have h0 := (OrthoF2.mem_orthogonal_iff_polar.mp (Submodule.mem_inf.mp ha'A).2) b' hb'
  exact hab' h0

theorem inv_apply_mem_commSpace_conj_YL {g d : V ≃ₗ[ZMod 2] V} {x : V}
    (hx : x ∈ commSpace (g * d * g⁻¹)) : g⁻¹ x ∈ commSpace d := by
  obtain ⟨u, rfl⟩ := mem_commSpace.mp hx
  refine mem_commSpace.mpr ⟨g⁻¹ u, ?_⟩
  simp only [LinearEquiv.mul_apply, map_sub]
  rw [show g⁻¹ (g (d (g⁻¹ u))) = d (g⁻¹ u) from g.symm_apply_apply _]

section Image

variable {H : Type} [Group H] {D : Set H}

theorem closure_image_eq_top_YL :
    closure (QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D)) = ⊤ := by
  have hc : closure (Subtype.val ⁻¹' D : Set (closure D)) = ⊤ := by simp
  rw [← MonoidHom.map_closure, hc, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']

theorem subsingleton_of_mem_center_YL (hconj : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ closure D, g * a * g⁻¹ = b)
    {d : closure D} (hd : (d : H) ∈ D) (hc : d ∈ center (closure D)) :
    Subsingleton (closure D ⧸ center (closure D)) := by
  have hall : ∀ e ∈ D, e = (d : H) := by
    intro e he
    obtain ⟨g, hg, hge⟩ := hconj _ hd e he
    have hcomm' : g * (d : H) = d * g := congrArg Subtype.val (mem_center_iff.mp hc ⟨g, hg⟩)
    rw [← hge, hcomm', mul_assoc, mul_inv_cancel, mul_one]
  have hle : closure D ≤ zpowers (d : H) := by
    rw [closure_le]
    intro e he
    rw [hall e he]
    exact mem_zpowers _
  have htop : center (closure D) = ⊤ := by
    refine eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun b => Subtype.ext ?_
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hle b.2)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hle a.2)
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self (d : H) i j).eq
  rw [htop]
  exact QuotientGroup.subsingleton_quotient_top

theorem mk_ne_one_YL (hconj : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ closure D, g * a * g⁻¹ = b)
    [Nontrivial (closure D ⧸ center (closure D))] {d : closure D} (hd : (d : H) ∈ D) :
    QuotientGroup.mk' (center (closure D)) d ≠ 1 := by
  intro h
  have hc : d ∈ center (closure D) := (QuotientGroup.eq_one_iff d).mp h
  exact not_subsingleton _ (subsingleton_of_mem_center_YL hconj hd hc)

theorem nonempty_of_nontrivial_YL [Nontrivial (closure D ⧸ center (closure D))] :
    D.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  subst h
  have hbot : ∀ a : closure (∅ : Set H), a = 1 := by
    intro a
    have ha : (a : H) ∈ (⊥ : Subgroup H) :=
      (closure_le (⊥ : Subgroup H)).mpr (Set.empty_subset _) a.2
    exact Subtype.ext ((mem_bot).mp ha)
  have htop : center (closure (∅ : Set H)) = ⊤ :=
    eq_top_iff.mpr fun a _ => mem_center_iff.mpr fun b => by rw [hbot a, hbot b]
  apply not_subsingleton (closure (∅ : Set H) ⧸ center (closure (∅ : Set H)))
  rw [htop]
  exact QuotientGroup.subsingleton_quotient_top

theorem orderOf_mul_coe_YL {L : Subgroup H} (d e : L) :
    orderOf (d * e) = orderOf ((d : H) * e) := by
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]

theorem conj_mem_image_YL (hinv : ∀ l ∈ closure D, ∀ d ∈ D, l * d * l⁻¹ ∈ D)
    {x c : closure D ⧸ center (closure D)}
    (hx : x ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D)) :
    c * x * c⁻¹ ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D) := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (center (closure D)) c
  refine ⟨l * d * l⁻¹, hinv _ l.2 _ hd, ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem mem_image_iff_isConj_YL (hconj : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ closure D, g * a * g⁻¹ = b)
    (hinv : ∀ l ∈ closure D, ∀ d ∈ D, l * d * l⁻¹ ∈ D) {d : closure D} (hd : (d : H) ∈ D)
    (x : closure D ⧸ center (closure D)) :
    x ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D) ↔
      IsConj (QuotientGroup.mk' (center (closure D)) d) x := by
  constructor
  · rintro ⟨e, he, rfl⟩
    obtain ⟨g, hg, hge⟩ := hconj d hd e he
    have hgT : (⟨g, hg⟩ : closure D) * d * (⟨g, hg⟩ : closure D)⁻¹ = e := Subtype.ext hge
    refine isConj_iff.mpr ⟨QuotientGroup.mk' (center (closure D)) ⟨g, hg⟩, ?_⟩
    rw [← hgT, map_mul, map_mul, map_inv]
  · intro hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hx
    exact conj_mem_image_YL hinv ⟨d, hd, rfl⟩

theorem orderOf_mul_image_le_YL [Finite H] (hord : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    {x y : closure D ⧸ center (closure D)}
    (hx : x ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D))
    (hy : y ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D)) :
    orderOf (x * y) ≤ 4 := by
  obtain ⟨d, hd, rfl⟩ := hx
  obtain ⟨e, he, rfl⟩ := hy
  rw [← map_mul]
  have h1 := orderOf_map_dvd (QuotientGroup.mk' (center (closure D))) (d * e)
  rw [orderOf_mul_coe_YL] at h1
  exact (Nat.le_of_dvd (orderOf_pos _) h1).trans (hord _ hd _ he)

theorem orderOf_eq_four_of_mk_YL [Finite H] (hord : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    {d e : closure D}
    (hd : (d : H) ∈ D) (he : (e : H) ∈ D)
    (h4 : orderOf (QuotientGroup.mk' (center (closure D)) d *
      QuotientGroup.mk' (center (closure D)) e) = 4) :
    orderOf ((d : H) * e) = 4 := by
  rw [← map_mul] at h4
  have h1 := orderOf_map_dvd (QuotientGroup.mk' (center (closure D))) (d * e)
  rw [h4, orderOf_mul_coe_YL] at h1
  exact le_antisymm (hord _ hd _ he) (Nat.le_of_dvd (orderOf_pos _) h1)

theorem mul_self_of_mem_image_YL (hinvol : ∀ d ∈ D, d * d = 1)
    {x : closure D ⧸ center (closure D)}
    (hx : x ∈ QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D)) : x * x = 1 := by
  obtain ⟨d, hd, rfl⟩ := hx
  rw [← map_mul]
  have : d * d = 1 := Subtype.ext (hinvol _ hd)
  rw [this, map_one]

theorem isTransClass34_image_YL [Finite H]
    (hconj : ∀ a ∈ D, ∀ b ∈ D, ∃ g ∈ closure D, g * a * g⁻¹ = b)
    (hinv : ∀ l ∈ closure D, ∀ d ∈ D, l * d * l⁻¹ ∈ D) (hinvol : ∀ d ∈ D, d * d = 1)
    (hord : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 4)
    (hsq : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    [Nontrivial (closure D ⧸ center (closure D))] :
    DW.IsTransClass34 (QuotientGroup.mk' (center (closure D)) '' (Subtype.val ⁻¹' D)) := by
  obtain ⟨t₀, ht₀⟩ := nonempty_of_nontrivial_YL (D := D)
  have hT : t₀ ∈ closure D := subset_closure ht₀
  refine ⟨closure_image_eq_top_YL, ⟨QuotientGroup.mk' (center (closure D)) ⟨t₀, hT⟩,
    ⟨⟨t₀, hT⟩, ht₀, rfl⟩, mem_image_iff_isConj_YL hconj hinv (d := ⟨t₀, hT⟩) ht₀⟩, ?_,
    fun x hx y hy => orderOf_mul_image_le_YL hord hx hy, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact ⟨mk_ne_one_YL hconj hd, mul_self_of_mem_image_YL hinvol ⟨d, hd, rfl⟩⟩
  · rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ h4
    have h4' := orderOf_eq_four_of_mk_YL hord hd he h4
    refine ⟨(d * e) ^ 2, ?_, by rw [map_pow, map_mul]⟩
    simpa using hsq _ hd _ he h4'

theorem nontrivial_of_inspNondeg_YL {X : Type} [Group X] {E : Set X} (h : InspNondeg X E) :
    Nontrivial X := by
  obtain ⟨d, -, e, -, h4⟩ := h
  refine nontrivial_of_ne (d * e) 1 fun h1 => ?_
  rw [h1, orderOf_one] at h4
  exact absurd h4 (by norm_num)

@[expose] noncomputable def quotEquiv_YL (L : Subgroup H) (hc : center L = ⊥) :
    L ⧸ center L ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot

@[simp] theorem quotEquiv_YL_mk (L : Subgroup H) (hc : center L = ⊥) (l : L) :
    quotEquiv_YL L hc (QuotientGroup.mk' (center L) l) = l := rfl

@[expose] noncomputable def quotEmb_YL (L : Subgroup H) (hc : center L = ⊥) : L ⧸ center L →* H :=
  L.subtype.comp (quotEquiv_YL L hc)

theorem quotEmb_YL_injective (L : Subgroup H) (hc : center L = ⊥) :
    Function.Injective (quotEmb_YL L hc) :=
  L.subtype_injective.comp (MulEquiv.injective _)

@[simp] theorem quotEmb_YL_mk (L : Subgroup H) (hc : center L = ⊥) (l : L) :
    quotEmb_YL L hc (QuotientGroup.mk' (center L) l) = l := rfl

end Image

end AS35YL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

open AS35YL

theorem isTypeA_of_mem_DbarAsc_YL (hS : S.SixHyp) {d : S.O} (hd : d ∈ S.DbarAsc) :
    IsTypeA S.q (d : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact (S.fiveOne_two hS.sixFour hS.weak ht htM).1

theorem DbarAsc_subset_Mbar_YL : S.DbarAsc ⊆ S.Mbar := by
  rintro _ ⟨t, -, htM, rfl⟩
  exact ⟨⟨t, htM⟩, rfl⟩

theorem LbarAsc_le_Mbar_YL : S.LbarAsc ≤ S.Mbar :=
  (closure_le _).mpr DbarAsc_subset_Mbar_YL

theorem mul_self_of_mem_DbarAsc_YL {d : S.O} (hd : d ∈ S.DbarAsc) : d * d = 1 := by
  obtain ⟨t, ht, htM, rfl⟩ := hd
  exact S.ρ_mul_self_eq_one htM (S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1))

theorem conj_mem_DbarAsc_YL {l d : S.O} (hl : l ∈ S.LbarAsc) (hd : d ∈ S.DbarAsc) :
    l * d * l⁻¹ ∈ S.DbarAsc :=
  S.conj_mem_DbarAsc_L (LbarAsc_le_Mbar_YL hl) hd

theorem mem_Dbar12_of_mem_DbarAsc_YL (hS : S.SixHyp) {d : S.O} (hd : d ∈ S.DbarAsc) :
    d ∈ S.Dbar12 :=
  ⟨DbarAsc_subset_Mbar_YL hd, isTypeA_of_mem_DbarAsc_YL hS hd⟩

theorem orderOf_mul_le_four_YL (hS : S.SixHyp) {d e : S.O} (hd : d ∈ S.DbarAsc)
    (he : e ∈ S.DbarAsc) : orderOf (d * e) ≤ 4 :=
  Dbar12_rootInvolution.1 d (mem_Dbar12_of_mem_DbarAsc_YL hS hd) e
    (mem_Dbar12_of_mem_DbarAsc_YL hS he)

theorem sq_mem_DbarAsc_YL (hS : S.SixHyp) {d e : S.O} (hd : d ∈ S.DbarAsc)
    (he : e ∈ S.DbarAsc) (h4 : orderOf (d * e) = 4) : (d * e) ^ 2 ∈ S.DbarAsc := by
  have hdD := mem_Dbar12_of_mem_DbarAsc_YL hS hd
  have heD := mem_Dbar12_of_mem_DbarAsc_YL hS he
  have hde : d * e ≠ e * d := by
    intro h
    have hdd : d * d = 1 := mul_self_of_mem_DbarAsc_YL hd
    have hee : e * e = 1 := mul_self_of_mem_DbarAsc_YL he
    have h2 : (d * e) ^ 2 = 1 := by
      calc (d * e) ^ 2 = d * (e * d) * e := by rw [pow_two]; group
        _ = d * (d * e) * e := by rw [h]
        _ = (d * d) * (e * e) := by group
        _ = 1 := by rw [hdd, hee, one_mul]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hec : e ∈ S.comp12 d := Relation.ReflTransGen.single ⟨hdD, heD, hde⟩
  have hsq := sq_mem_comp12 hdD hec h4
  obtain ⟨x, hx, hxe⟩ := S14.rootInvolutionComponentsInput S.Qt S.q S.q_nondegenerate S.Mbar
    S.s12_noNormalTwo_Mbar S.Dbar12 rfl d hdD _ hsq
  have hxM : x ∈ S.Mbar :=
    (closure_le _).mpr (fun y hy => (mem_Dbar12_of_mem_comp12 hdD hy).1) hx
  rw [hxe]
  exact S.conj_mem_DbarAsc_L hxM hd

@[expose] def LbarIrred_YL (S : Setting G) : Prop :=
  ∀ W : Submodule (ZMod 2) S.Qt,
    (∀ l ∈ S.LbarAsc, ∀ w ∈ W, ((l : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W) → W = ⊥ ∨ W = ⊤

theorem mk_mem_EhatAsc_YL {d : S.LbarAsc} (hd : (d : S.O) ∈ S.DbarAsc) :
    QuotientGroup.mk' (center S.LbarAsc) d ∈ S.EhatAsc := ⟨d, hd, rfl⟩

theorem DbarAsc_nonempty_YL [h : Nontrivial (S.LbarAsc ⧸ center S.LbarAsc)] :
    S.DbarAsc.Nonempty :=
  @nonempty_of_nontrivial_YL _ _ S.DbarAsc h

theorem isTransClass34_EhatAsc_YL (hS : S.SixHyp) (hst : S.Asc512Standing)
    [Nontrivial (S.LbarAsc ⧸ center S.LbarAsc)] : DW.IsTransClass34 S.EhatAsc :=
  isTransClass34_image_YL hst.conj (fun _ hl _ hd => conj_mem_DbarAsc_YL hl hd)
    (fun _ hd => mul_self_of_mem_DbarAsc_YL hd)
    (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he)
    (fun _ hd _ he h4 => sq_mem_DbarAsc_YL hS hd he h4)

theorem orderOf_mul_EhatAsc_le_YL (hS : S.SixHyp) {x y : S.LbarAsc ⧸ center S.LbarAsc}
    (hx : x ∈ S.EhatAsc) (hy : y ∈ S.EhatAsc) : orderOf (x * y) ≤ 4 :=
  orderOf_mul_image_le_YL (fun _ hd _ he => orderOf_mul_le_four_YL hS hd he) hx hy

theorem conj_mem_EhatAsc_YL {x c : S.LbarAsc ⧸ center S.LbarAsc} (hx : x ∈ S.EhatAsc) :
    c * x * c⁻¹ ∈ S.EhatAsc :=
  conj_mem_image_YL (fun _ hl _ hd => conj_mem_DbarAsc_YL hl hd) hx

end Setting

namespace S14

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def Asc512FieldFam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧ ∃ (τ : StatedLieTag) (n f : ℕ),
    2 ≤ f ∧ ((τ = .PSL ∧ 3 ≤ n) ∨ (τ = .PSp ∧ 3 ≤ n) ∨
      ((τ = .POmegaPlus ∨ τ = .POmegaMinus) ∧ 4 ≤ n) ∨
      (n = 0 ∧ τ ∈ ({.G2, .trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag))) ∧
    LieModel X τ n 2 f

@[expose] def Asc512PSLFam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧ ∃ m, 3 ≤ m ∧ LieModel X .PSL m 2 1

@[expose] def Asc512PSpFam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧ ∃ m, 3 ≤ m ∧ LieModel X .PSp m 2 1

@[expose] def Asc512POmegaFam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧ ∃ m, 4 ≤ m ∧
    (LieModel X .POmegaPlus m 2 1 ∨ LieModel X .POmegaMinus m 2 1)

@[expose] def Asc512ExcFam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧
    ∃ τ ∈ ({.trialityD4, .F4, .E6, .twistedE6, .E7, .E8} : Finset StatedLieTag), LieModel X τ 0 2 1

@[expose] def Asc512U33Fam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (D : Set X) => InspNondeg X D ∧ LieModel X .PSU 3 3 1

@[expose] def Asc512Alt6Fam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (_ : Set X) => Nonempty (X ≃* alternatingGroup (Fin 6))

@[expose] def Asc512J2Fam : ∀ (X : Type) [Group X], Set X → Prop :=
  fun (X : Type) [Group X] (_ : Set X) => NativeSporadic.IsSporadic X .J2

end S14

end CFSG.LargeExtraspecial
