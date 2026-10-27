module

public import CFSG.CharacterTheory.SteinbergBSExceptionalCharacterTools
public import CFSG.CharacterTheory.DirectProductCharacters
public import CFSG.GH74.QTGen4.Recog.G23.HK2
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

open scoped Classical

variable {G : Type} [Group G]

theorem suzI_orderOf_conj (c x : G) : orderOf (c * x * c⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x
  simpa [MulAut.conj_apply] using h

theorem suzI_orderOf_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact suzI_orderOf_conj c a

theorem suzI_classFn_eq {f : G → ℂ} (hf : CFSG.BlocksIsClassFunction f) {a b : G}
    (h : IsConj a b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  exact (hf a c).symm

theorem suzI_one_not_mem_specialD (z : G) (H : Subgroup G) : (1 : G) ∉ specialD z H := by
  rintro ⟨-, h | ⟨k, hk, ho, -⟩⟩
  · exact h.2 rfl
  · rw [orderOf_one] at ho
    omega

theorem suzI_eq_of_mem_specialD_of_sq {z x : G} {H : Subgroup G} (hx : x ∈ specialD z H)
    (hsq : x ^ 2 = 1) : x = z := by
  obtain ⟨-, h | ⟨k, hk, ho, hkz⟩⟩ := hx
  · exfalso
    have hg : x ^ Nat.gcd 2 3 = 1 := pow_gcd_eq_one.mpr ⟨hsq, h.1⟩
    rw [show Nat.gcd 2 3 = 1 by norm_num, pow_one] at hg
    exact h.2 hg
  · have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [ho] at hdvd
    have hk1 : k = 1 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    subst hk1
    simpa using hkz

theorem suzI_mem_specialD_of_root {z x : G} {H : Subgroup G} (hxH : x ∈ H)
    (ho : orderOf x = 4) (hsq : x ^ 2 = z) : x ∈ specialD z H := by
  simp only [specialD, Set.mem_setOf_eq]
  exact ⟨hxH, Or.inr ⟨2, by norm_num, by omega, hsq⟩⟩

theorem suzI_mem_specialD_self {z : G} {H : Subgroup G} (hzH : z ∈ H) (ho : orderOf z = 2) :
    z ∈ specialD z H := by
  simp only [specialD, Set.mem_setOf_eq]
  exact ⟨hzH, Or.inr ⟨1, by norm_num, by omega, pow_one z⟩⟩

theorem suzI_order4_conj {z : G} {H : Subgroup G} [Finite G]
    (hOC : ∀ u : G, orderOf u = 2 → IsConj z u) (hC : ∀ g : G, g ∈ H ↔ g * z = z * g)
    {y : G} (hy4 : orderOf y = 4) :
    ∃ y' : G, y' ∈ H ∧ y' ∈ specialD z H ∧ orderOf y' = 4 ∧ IsConj y y' := by
  have hy2 : orderOf (y ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hy4]; norm_num), hy4]
  obtain ⟨c, hc⟩ := isConj_iff.mp (hOC (y ^ 2) hy2)
  obtain ⟨y', hy'⟩ : ∃ y' : G, y' = c⁻¹ * y * c := ⟨_, rfl⟩
  have hy'sq : y' ^ 2 = z := by
    rw [hy']
    calc (c⁻¹ * y * c) ^ 2 = c⁻¹ * y ^ 2 * c := by rw [sq, sq]; group
      _ = c⁻¹ * (c * z * c⁻¹) * c := by rw [hc]
      _ = z := by group
  have hy'4 : orderOf y' = 4 := by
    have h := suzI_orderOf_conj c⁻¹ y
    rw [inv_inv] at h
    rw [hy', h, hy4]
  have hy'H : y' ∈ H := by
    rw [hC y', ← hy'sq, sq]
    group
  refine ⟨y', hy'H, suzI_mem_specialD_of_root hy'H hy'4 hy'sq, hy'4, ?_⟩
  rw [hy']
  exact isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩

theorem suzI_zOf_facts [Finite G] {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}
    (hH : G23One H H₁ H₂) (hL : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e) (hO : OneClass e) :
    zOf e ∈ H₁ ⊓ H₂ ∧ zOf e ≠ 1 ∧ orderOf (zOf e) = 2 ∧ zOf e ∈ H ∧
      ∀ g : G, g ∈ H ↔ g * zOf e = zOf e * g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he0 : e 0 ∈ H₁ := by
    rw [← hL.gen₁]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he1 : e 1 ∈ H₁ := by
    rw [← hL.gen₁]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have he2 : e 2 ∈ H₂ := by
    rw [← hL.gen₂]; exact Subgroup.subset_closure (Set.mem_insert _ _)
  have he3 : e 3 ∈ H₂ := by
    rw [← hL.gen₂]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hA : e 0 * e 1 * e 0 * e 1 = e 2 * e 3 * e 2 * e 3 := by
    have hr : FreeGroup.lift e (FreeGroup.mk ([(0, true), (1, true), (0, true), (1, true),
        (3, false), (2, false), (3, false), (2, false)] : List (Fin 6 × Bool))) = 1 :=
      hL.rels _ (by simp [g23WordsH])
    have hr' : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
      simpa [FreeGroup.lift_mk, mul_assoc] using hr
    calc e 0 * e 1 * e 0 * e 1
        = (e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) *
            (e 2 * e 3 * e 2 * e 3) := by group
      _ = e 2 * e 3 * e 2 * e 3 := by rw [hr', one_mul]
  have hzA : zOf e ∈ H₁ := by
    unfold zOf; exact H₁.pow_mem (H₁.mul_mem he0 he1) 2
  have hzB : zOf e ∈ H₂ := by
    have h : zOf e = (e 2 * e 3) ^ 2 := by
      unfold zOf; simp only [sq, mul_assoc] at hA ⊢; exact hA
    rw [h]; exact H₂.pow_mem (H₂.mul_mem he2 he3) 2
  have hzInf : zOf e ∈ H₁ ⊓ H₂ := Subgroup.mem_inf.mpr ⟨hzA, hzB⟩
  have hz1 : zOf e ≠ 1 := by
    intro h1
    have hHdvd : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
    rw [hF.card_H] at hHdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (dvd_trans (by norm_num) hHdvd)
    have hxc : IsConj (zOf e) x := hO x hx
    rw [h1] at hxc
    have hx1 : x = 1 := isConj_one_right.mp hxc
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  have hsq : zOf e ^ 2 = 1 := CFSG.GH74.QTGen4.Recog.G23.G23One.sq_inf hH hzInf
  have hord : orderOf (zOf e) = 2 := orderOf_eq_prime hsq hz1
  have hzH : zOf e ∈ H := hH.le_one hzA
  have hunique : ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = zOf e := by
    obtain ⟨w, -, -, huniq⟩ := CFSG.GH74.QTGen4.Recog.G23.G23One.exists_unique_inf hH
    intro y hy
    rcases huniq y hy with h | h
    · exact Or.inl h
    · rcases huniq (zOf e) hzInf with h' | h'
      · exact absurd h' hz1
      · exact Or.inr (h.trans h'.symm)
  refine ⟨hzInf, hz1, hord, hzH, fun g => ?_⟩
  rw [hH.eq_centralizer, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg
    exact (hg (zOf e) hzInf).symm
  · intro hg y hy
    rcases hunique y hy with rfl | rfl
    · simp
    · exact hg.symm

theorem suzI_card_pairs {H : Subgroup G} [Fintype G] {z σ : G}
    (hz2 : orderOf z = 2) (hOC : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hSinv : ∀ x ∈ specialD z H, ∀ u : G, u * u = 1 → u * x * u⁻¹ = x⁻¹ → u ∈ H)
    (hC : ∀ g : G, g ∈ H ↔ g * z = z * g) (hσ : σ ∈ specialD z H) :
    (Finset.univ.filter fun u : H => orderOf u = 2 ∧
        (if σ = z then (u : G) ≠ z else (u : G) * σ * (u : G)⁻¹ = σ⁻¹)).card =
      (((Finset.univ.filter fun g : G => IsConj g z) ×ˢ
          (Finset.univ.filter fun g : G => IsConj g z)).filter fun q => q.1 * q.2 = σ).card := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2, sq] at this
    exact this
  refine Finset.card_bij (fun u _ => ((u : G), (u : G)⁻¹ * σ)) ?_ ?_ ?_
  ·
    intro u hu
    obtain ⟨-, hu2, hcond⟩ := Finset.mem_filter.mp hu
    have ha2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
    have haa : (u : G) * (u : G) = 1 := by
      have := pow_orderOf_eq_one (u : G)
      rw [ha2, sq] at this
      exact this
    have hainv : (u : G)⁻¹ = (u : G) := inv_eq_of_mul_eq_one_right haa
    have hinvσ : (u : G) * σ * (u : G)⁻¹ = σ⁻¹ := by
      by_cases hσz : σ = z
      · have huz : (u : G) * z = z * (u : G) := (hC (u : G)).mp u.2
        rw [hσz, huz, mul_assoc, mul_inv_cancel, mul_one, inv_eq_of_mul_eq_one_right hzz]
      · rw [if_neg hσz] at hcond
        exact hcond
    have hvv : ((u : G)⁻¹ * σ) * ((u : G)⁻¹ * σ) = 1 := by
      have e1 : ((u : G)⁻¹ * σ) * ((u : G)⁻¹ * σ) = ((u : G) * σ * (u : G)⁻¹) * σ := by
        rw [hainv]; simp only [mul_assoc]
      rw [e1, hinvσ, inv_mul_cancel]
    have hv1 : (u : G)⁻¹ * σ ≠ 1 := by
      intro h
      have hua : (u : G) = σ := inv_mul_eq_one.mp h
      have hσsq : σ ^ 2 = 1 := by rw [sq, ← hua, haa]
      have hσz' : σ = z := suzI_eq_of_mem_specialD_of_sq hσ hσsq
      by_cases hσz : σ = z
      · rw [if_pos hσz] at hcond
        exact hcond (hua.trans hσz')
      · exact hσz hσz'
    have hv2 : orderOf ((u : G)⁻¹ * σ) = 2 := orderOf_eq_prime (by rw [sq]; exact hvv) hv1
    have hIsC_v : IsConj ((u : G)⁻¹ * σ) z := isConj_comm.mp (hOC _ hv2)
    have hIsC_u : IsConj (u : G) z := isConj_comm.mp (hOC _ ha2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIsC_u⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hIsC_v⟩⟩, mul_inv_cancel_left _ _⟩
  ·
    intro u₁ _ u₂ _ h
    exact Subtype.ext (congrArg Prod.fst h)
  ·
    intro p hp
    obtain ⟨hpmem, hprod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpmem
    have hpa : IsConj p.1 z := (Finset.mem_filter.mp hp1).2
    have hpb : IsConj p.2 z := (Finset.mem_filter.mp hp2).2
    have ha2 : orderOf p.1 = 2 := (suzI_orderOf_of_isConj hpa).symm.trans hz2
    have hb2 : orderOf p.2 = 2 := (suzI_orderOf_of_isConj hpb).symm.trans hz2
    have haa : p.1 * p.1 = 1 := by
      have := pow_orderOf_eq_one p.1
      rw [ha2, sq] at this
      exact this
    have hbb : p.2 * p.2 = 1 := by
      have := pow_orderOf_eq_one p.2
      rw [hb2, sq] at this
      exact this
    have hprod' : p.1 * p.2 = σ := hprod
    have ha' : p.1⁻¹ = p.1 := inv_eq_of_mul_eq_one_right haa
    have hb' : p.2⁻¹ = p.2 := inv_eq_of_mul_eq_one_right hbb
    have hpinv : p.1 * σ * p.1⁻¹ = σ⁻¹ := by
      rw [← hprod', mul_inv_rev, hb', ha']
      calc p.1 * (p.1 * p.2) * p.1 = (p.1 * p.1) * p.2 * p.1 := by group
        _ = p.2 * p.1 := by rw [haa, one_mul]
    have hpH : p.1 ∈ H := hSinv σ hσ p.1 haa hpinv
    refine ⟨⟨p.1, hpH⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← Subgroup.orderOf_coe]; exact ha2
      · by_cases hσz : σ = z
        · rw [if_pos hσz]
          intro hpz
          have hpz' : p.1 = z := hpz
          have h2' : p.1 * p.2 = p.1 := by rw [hprod', hσz, hpz']
          have hp2one : p.2 = 1 := mul_eq_left.mp h2'
          rw [hp2one, orderOf_one] at hb2
          exact absurd hb2 (by norm_num)
        · rw [if_neg hσz]
          exact hpinv
    · refine Prod.ext rfl ?_
      show p.1⁻¹ * σ = p.2
      rw [← hprod', inv_mul_cancel_left]

theorem suzI_sum_subgroup_int [Fintype G] (H : Subgroup G) {θ : G → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr G) :
    ∃ m : ℤ, ∑ y : H, θ y = (Nat.card H : ℂ) * m := by
  have h1 : (1 : H → ℂ) ∈ CFSG.BlocksVChar H :=
    AddSubgroup.subset_closure (CFSG.DirectProduct.one_mem_blocksIrr H)
  have h2 := CFSG.inducedFunction_mem_blocksVChar H h1
  have h3 : θ ∈ CFSG.BlocksVChar G := AddSubgroup.subset_closure hθ
  obtain ⟨n, hn⟩ := CFSG.blocksInnerProduct_virtual_integer h2 h3
  rw [CFSG.blocksInnerProduct_inducedFunction_left H 1 θ
    (CFSG.SmallDefect.isClassFunction_of_mem hθ)] at hn
  refine ⟨n, ?_⟩
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold CFSG.BlocksInnerProduct at hn
  simp only [Pi.one_apply, one_mul] at hn
  have h4 : ∑ x : H, starRingEnd ℂ (θ x) = (Nat.card H : ℂ) * n := by
    rw [← hn, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have h5 := congrArg (starRingEnd ℂ) h4
  simpa only [map_sum, map_mul, Complex.conj_natCast, map_intCast, Complex.conj_conj] using h5

theorem suzI_bip_add [Fintype G] (f g θ : G → ℂ) :
    CFSG.BlocksInnerProduct (f + g) θ = CFSG.BlocksInnerProduct f θ + CFSG.BlocksInnerProduct g θ := by
  unfold CFSG.BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.add_apply]
  ring

theorem suzI_bip_smul [Fintype G] (c : ℂ) (f θ : G → ℂ) :
    CFSG.BlocksInnerProduct (c • f) θ = c * CFSG.BlocksInnerProduct f θ := by
  unfold CFSG.BlocksInnerProduct
  have key : ∑ x : G, (c • f) x * starRingEnd ℂ (θ x) = c * ∑ x : G, f x * starRingEnd ℂ (θ x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [key]
  ring

theorem suzI_sum_H_split {H : Subgroup G} [Fintype G] {z : G}
    (hcard : Nat.card H = 576)
    (cD : (Finset.univ.filter fun y : H => (y : G) ∈ specialD z H).card = 413)
    (cI : (Finset.univ.filter fun y : H => orderOf y = 2 ∧ (y : G) ≠ z).card = 90)
    (cF : (Finset.univ.filter fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD z H).card = 72)
    (f : H → ℂ) :
    ∑ y : H, f y = f 1 +
      ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD z H), f y +
      ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ z), f y +
      ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD z H), f y := by
  set DH := Finset.univ.filter (fun y : H => (y : G) ∈ specialD z H) with hDH
  set IH := Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ z) with hIH
  set FH := Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD z H) with hFH
  have hD1 : Disjoint ({1} : Finset H) DH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    rw [hDH, Finset.mem_filter] at hb
    subst ha
    exact suzI_one_not_mem_specialD z H (by simpa using hb.2)
  have hI1 : Disjoint ({1} : Finset H) IH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    rw [hIH, Finset.mem_filter] at hb
    subst ha
    obtain ⟨-, h2, -⟩ := hb
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hF1 : Disjoint ({1} : Finset H) FH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_singleton] at ha
    rw [hFH, Finset.mem_filter] at hb
    subst ha
    obtain ⟨-, h2, -⟩ := hb
    rw [orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hDI : Disjoint DH IH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hDH, Finset.mem_filter] at ha
    rw [hIH, Finset.mem_filter] at hb
    have hsq : (a : G) ^ 2 = 1 := by
      have h1 : a ^ 2 = 1 := by
        have := pow_orderOf_eq_one a
        rwa [hb.2.1] at this
      have h2 := congrArg (fun x : H => (x : G)) h1
      simpa using h2
    exact hb.2.2 (suzI_eq_of_mem_specialD_of_sq ha.2 hsq)
  have hDF : Disjoint DH FH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hDH, Finset.mem_filter] at ha
    rw [hFH, Finset.mem_filter] at hb
    exact hb.2.2 ha.2
  have hIF : Disjoint IH FH := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [hIH, Finset.mem_filter] at ha
    rw [hFH, Finset.mem_filter] at hb
    rw [ha.2.1] at hb
    exact absurd hb.2.1 (by norm_num)
  have hcard' : Fintype.card H = 576 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hAD : Disjoint ({1} : Finset H) DH := hD1
  have hA_I : Disjoint ({1} ∪ DH : Finset H) IH := Finset.disjoint_union_left.mpr ⟨hI1, hDI⟩
  have hAI_F : Disjoint ({1} ∪ DH ∪ IH : Finset H) FH :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hF1, hDF⟩, hIF⟩
  have hunion : ({1} ∪ DH ∪ IH ∪ FH : Finset H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hAI_F, Finset.card_union_of_disjoint hA_I,
      Finset.card_union_of_disjoint hAD, Finset.card_singleton, cD, cI, cF, hcard']
  rw [← hunion, Finset.sum_union hAI_F, Finset.sum_union hA_I, Finset.sum_union hAD,
    Finset.sum_singleton]

theorem suzI_card_conj_mul_centralizer [Finite G] (t : G) :
    Nat.card {s : G // IsConj t s} * Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Nat.card G := by
  classical
  have := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) t
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have e : Nat.card {s : G // IsConj t s} = Nat.card (MulAction.orbit (ConjAct G) t) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun s => by
      rw [ConjAct.mem_orbit_conjAct, isConj_comm])
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := MulAction.stabilizer (ConjAct G) t),
    Nat.card_eq_fintype_card (α := G), ← ConjAct.card]
  exact h

theorem suzI_card_isConj_mul [Fintype G] (z : G) :
    (Finset.univ.filter fun g : G => IsConj g z).card *
      Nat.card (Subgroup.centralizer ({z} : Set G)) = Nat.card G := by
  have hfilt : (Finset.univ.filter fun g : G => IsConj g z) =
      Finset.univ.filter fun s : G => IsConj z s := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isConj_comm]
  have hcard : (Finset.univ.filter fun s : G => IsConj z s).card =
      Nat.card {s : G // IsConj z s} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hfilt, hcard]
  exact suzI_card_conj_mul_centralizer z

theorem suzI_sum_irr_ite [DecidableEq (G → ℂ)] (S : Finset (G → ℂ)) (F : (G → ℂ) → ℂ) {a : G → ℂ}
    (ha : a ∈ S) :
    ∑ θ ∈ S, F θ * (if a = θ then 1 else 0) = F a := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, if_pos ha]

theorem leafSuzukiIntegers : LeafSuzukiIntegers := by
  intro G _ _ T H H₁ H₂ M e χ X₁ X₂ ε₁ ε₂ h hF hO hD hχ hc
  obtain ⟨hzInf, hz1, hz2, hzH, hC⟩ := suzI_zOf_facts h.ctx.one h.lets hF hO
  have hOC : ∀ u : G, orderOf u = 2 → IsConj (zOf e) u := hO
  have hSinv : ∀ x ∈ specialD (zOf e) H, ∀ u : G, u * u = 1 → u * x * u⁻¹ = x⁻¹ → u ∈ H :=
    hD.invert
  have hDz : zOf e ∈ specialD (zOf e) H := suzI_mem_specialD_self hzH hz2
  have hcardH : Nat.card H = 576 := hF.card_H
  obtain ⟨n₁, hn₁pos, hX₁1, hn₁dvd, -⟩ :=
    CFSG.OddOrderBasics.irreducible_character_degree_divides_order X₁ hc.irr₁
  obtain ⟨n₂, hn₂pos, hX₂1, hn₂dvd, -⟩ :=
    CFSG.OddOrderBasics.irreducible_character_degree_divides_order X₂ hc.irr₂
  have hn₁c : (n₁ : ℂ) ≠ 0 := by exact_mod_cast hn₁pos.ne'
  have hn₂c : (n₂ : ℂ) ≠ 0 := by exact_mod_cast hn₂pos.ne'
  have hε₁sq : (ε₁ : ℂ) ^ 2 = 1 := by rcases hc.ε₁_pm with rfl | rfl <;> norm_num
  have hε₂sq : (ε₂ : ℂ) ^ 2 = 1 := by rcases hc.ε₂_pm with rfl | rfl <;> norm_num
  have hε₁sqZ : ε₁ ^ 2 = 1 := by rcases hc.ε₁_pm with rfl | rfl <;> norm_num
  have hε₂sqZ : ε₂ ^ 2 = 1 := by rcases hc.ε₂_pm with rfl | rfl <;> norm_num
  have hX₁z : X₁ (zOf e) = ε₁ * (-8) := by
    have h1 := hc.val₁ ⟨zOf e, hzH⟩ hDz
    rw [hχ.chi20_z ⟨zOf e, hzH⟩ rfl] at h1
    exact h1
  have hX₂z : X₂ (zOf e) = -(ε₂ : ℂ) * 9 := by
    have h1 := hc.val₂ ⟨zOf e, hzH⟩ hDz
    rw [hχ.chi9_z ⟨zOf e, hzH⟩ rfl] at h1
    exact h1
  have hcl₂ : CFSG.BlocksIsClassFunction X₂ := CFSG.SmallDefect.isClassFunction_of_mem hc.irr₂
  have hDsum : ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H), X₂ y
      = 171 * (ε₂ : ℂ) := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H), X₂ y
        = ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
          (-(ε₂ : ℂ) * χ 8 y) :=
      Finset.sum_congr rfl fun y hy => hc.val₂ y (Finset.mem_filter.mp hy).2
    rw [h1, ← Finset.mul_sum, hχ.sum_chi9]
    ring
  have hIsum : ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ zOf e), X₂ y
      = -810 * (ε₂ : ℂ) := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ zOf e), X₂ y
        = ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 2 ∧ (y : G) ≠ zOf e),
          (-(ε₂ : ℂ) * 9) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨-, hy2, -⟩ := Finset.mem_filter.mp hy
      have hy2' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hy2
      exact (suzI_classFn_eq hcl₂ (hOC _ hy2')).symm.trans hX₂z
    rw [h1, Finset.sum_const, hχ.count_invol, nsmul_eq_mul]
    push_cast
    ring
  have hFsum : ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD (zOf e) H),
      X₂ y = 216 * (ε₂ : ℂ) := by
    have h1 : ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD (zOf e) H),
        X₂ y = ∑ y ∈ Finset.univ.filter (fun y : H => orderOf y = 4 ∧ (y : G) ∉ specialD (zOf e) H),
          (3 * (ε₂ : ℂ)) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      obtain ⟨-, hy4, hyD⟩ := Finset.mem_filter.mp hy
      have hy4' : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe]; exact hy4
      obtain ⟨y', hy'H, hy'D, hy'4, hconj⟩ := suzI_order4_conj hOC hC hy4'
      have hy'4H : orderOf (⟨y', hy'H⟩ : H) = 4 := by rw [← Subgroup.orderOf_coe]; exact hy'4
      have hval := hc.val₂ ⟨y', hy'H⟩ hy'D
      rw [hχ.chi9_order4 ⟨y', hy'H⟩ hy'D hy'4H] at hval
      have hval' : X₂ y' = -(ε₂ : ℂ) * (-3) := hval
      rw [suzI_classFn_eq hcl₂ hconj, hval']
      ring
    rw [h1, Finset.sum_const, hχ.count_order4, nsmul_eq_mul]
    push_cast
    ring
  have hsplit := suzI_sum_H_split (f := fun y : H => X₂ y) hcardH hχ.count_D hχ.count_invol
    hχ.count_order4
  have hS2 : ∑ y : H, X₂ y = (n₂ : ℂ) - 423 * (ε₂ : ℂ) := by
    rw [hsplit, hDsum, hIsum, hFsum]
    simp only [Subgroup.coe_one, hX₂1]
    ring
  obtain ⟨m, hm⟩ := suzI_sum_subgroup_int H hc.irr₂
  rw [hS2, hcardH] at hm
  have hn2Z : (n₂ : ℤ) = 576 * m + 423 * ε₂ := by
    have h1 : ((n₂ : ℤ) : ℂ) = ((576 * m + 423 * ε₂ : ℤ) : ℂ) := by
      push_cast
      linear_combination hm
    exact_mod_cast h1
  have hind0 : CFSG.TwoRankLowerBound.Helpers.inducedFunction H (psiFun H χ 0) 1 = 0 := by
    apply CFSG.CharacterTheory.SteinbergBS.inducedFunction_suzuki_vanish (A := specialD (zOf e) H)
    · intro y hy
      exact hχ.vanish 0 y hy
    · intro a ha hconj
      exact suzI_one_not_mem_specialD (zOf e) H (isConj_one_right.mp hconj ▸ ha)
  have hind1 : (1 : ℂ) + ε₁ * n₁ + ε₂ * n₂ = 0 := by
    have h1 := congrFun hc.ind 1
    rw [hind0] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hX₁1, hX₂1] at h1
    linear_combination -h1
  have hint1 : (1 : ℤ) + ε₁ * n₁ + ε₂ * n₂ = 0 := by
    have h1 : (((1 : ℤ) + ε₁ * n₁ + ε₂ * n₂ : ℤ) : ℂ) = 0 := by
      push_cast
      exact hind1
    exact_mod_cast h1
  obtain ⟨S, hS⟩ : ∃ S : Finset (G → ℂ),
      S = (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite G).toFinset := ⟨_, rfl⟩
  have hmemS : ∀ θ : G → ℂ, θ ∈ S ↔ θ ∈ CFSG.BlocksIrr G := fun θ => by
    rw [hS]; exact (CFSG.BlockSectionOrthogonality.Helpers.irreducibles_finite G).mem_toFinset
  obtain ⟨cC, hcCdef⟩ : ∃ c : ℕ, c = (Finset.univ.filter fun g : G => IsConj g (zOf e)).card :=
    ⟨_, rfl⟩
  have hcCard : cC * 576 = Nat.card G := by
    have h1 := suzI_card_isConj_mul (zOf e)
    have hcent : Subgroup.centralizer ({zOf e} : Set G) = H := by
      ext g
      exact (Subgroup.mem_centralizer_singleton_iff).trans (hC g).symm
    rw [hcent, hcardH, ← hcCdef] at h1
    exact h1
  have hcC : (cC : ℂ) * 576 = (Nat.card G : ℂ) := by exact_mod_cast hcCard
  have hNc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcC0 : (cC : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcC
    exact hNc hcC.symm
  have hpt : ∀ y : H, (y : G) ∈ specialD (zOf e) H →
      ((Finset.univ.filter (fun u : H => orderOf u = 2 ∧
          (if (y : G) = zOf e then (u : G) ≠ zOf e else (u : G) * (y : G) * (u : G)⁻¹ = (y : G)⁻¹))).card : ℂ) =
        (cC : ℂ) * cC / (Nat.card G : ℂ) *
          ∑ θ ∈ S, θ (zOf e) * θ (zOf e) * starRingEnd ℂ (θ (y : G)) / θ 1 := by
    intro y hy
    have h1 := suzI_card_pairs hz2 hOC hSinv hC hy
    have h2 := (CFSG.CharacterTheory.SteinbergBS.class_multiplication_count (zOf e) (zOf e)
      (y : G)).1
    rw [h1, h2, ← hcCdef, ← hS]
  have hT : ∀ θ ∈ CFSG.BlocksIrr G,
      ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
        psiFun H χ 0 y * starRingEnd ℂ (θ y) =
      576 * ((if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
        (ε₁ : ℂ) * (if X₁ = θ then 1 else 0) + (ε₂ : ℂ) * (if X₂ = θ then 1 else 0)) := by
    intro θ hθ
    have hθcl : CFSG.BlocksIsClassFunction θ := CFSG.SmallDefect.isClassFunction_of_mem hθ
    have hsub : ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
        psiFun H χ 0 y * starRingEnd ℂ (θ y) =
        ∑ y : H, psiFun H χ 0 y * starRingEnd ℂ (θ y) := by
      apply Finset.sum_filter_of_ne
      intro y _ hy
      by_contra hnot
      exact hy (by rw [hχ.vanish 0 y hnot, zero_mul])
    have hsumBIP : ∑ y : H, psiFun H χ 0 y * starRingEnd ℂ (θ y) =
        (Nat.card H : ℂ) * CFSG.BlocksInnerProduct (psiFun H χ 0) (fun y : H => θ y) := by
      unfold CFSG.BlocksInnerProduct
      rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'), one_mul]
    have hfrob := CFSG.blocksInnerProduct_inducedFunction_left H (psiFun H χ 0) θ hθcl
    rw [hc.ind] at hfrob
    have hone : CFSG.BlocksInnerProduct (fun _ : G => (1 : ℂ)) θ =
        if (fun _ : G => (1 : ℂ)) = θ then 1 else 0 :=
      CFSG.DirectProduct.blocksInnerProduct_of_mem (CFSG.DirectProduct.one_mem_blocksIrr G) hθ
    have hb1 : CFSG.BlocksInnerProduct X₁ θ = if X₁ = θ then 1 else 0 :=
      CFSG.DirectProduct.blocksInnerProduct_of_mem hc.irr₁ hθ
    have hb2 : CFSG.BlocksInnerProduct X₂ θ = if X₂ = θ then 1 else 0 :=
      CFSG.DirectProduct.blocksInnerProduct_of_mem hc.irr₂ hθ
    rw [suzI_bip_add, suzI_bip_add, suzI_bip_smul, suzI_bip_smul, hone, hb1, hb2] at hfrob
    rw [hsub, hsumBIP, hcardH, ← hfrob]
    push_cast
    ring
  have hF1 : (fun _ : G => (1 : ℂ)) (zOf e) * (fun _ : G => (1 : ℂ)) (zOf e) /
      (fun _ : G => (1 : ℂ)) 1 = 1 := by simp
  have hFX1 : X₁ (zOf e) * X₁ (zOf e) / X₁ 1 = 64 / (n₁ : ℂ) := by
    rw [hX₁z, hX₁1]
    linear_combination (64 / (n₁ : ℂ)) * hε₁sq
  have hFX2 : X₂ (zOf e) * X₂ (zOf e) / X₂ 1 = 81 / (n₂ : ℂ) := by
    rw [hX₂z, hX₂1]
    linear_combination (81 / (n₂ : ℂ)) * hε₂sq
  have hone_mem : (fun _ : G => (1 : ℂ)) ∈ S := (hmemS _).mpr (CFSG.DirectProduct.one_mem_blocksIrr G)
  have hX₁mem : X₁ ∈ S := (hmemS _).mpr hc.irr₁
  have hX₂mem : X₂ ∈ S := (hmemS _).mpr hc.irr₂
  have hsumθ : ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) *
      ((if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
        (ε₁ : ℂ) * (if X₁ = θ then 1 else 0) + (ε₂ : ℂ) * (if X₂ = θ then 1 else 0)) =
      1 + (ε₁ : ℂ) * (64 / (n₁ : ℂ)) + (ε₂ : ℂ) * (81 / (n₂ : ℂ)) := by
    have e0 : ∀ θ : G → ℂ, (θ (zOf e) * θ (zOf e) / θ 1) *
        ((if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
          (ε₁ : ℂ) * (if X₁ = θ then 1 else 0) + (ε₂ : ℂ) * (if X₂ = θ then 1 else 0)) =
        (θ (zOf e) * θ (zOf e) / θ 1) * (if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
        (ε₁ : ℂ) * ((θ (zOf e) * θ (zOf e) / θ 1) * (if X₁ = θ then 1 else 0)) +
        (ε₂ : ℂ) * ((θ (zOf e) * θ (zOf e) / θ 1) * (if X₂ = θ then 1 else 0)) :=
      fun θ => by ring
    rw [Finset.sum_congr rfl fun θ _ => e0 θ, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have i0 : ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) * (if (fun _ : G => (1 : ℂ)) = θ then 1 else 0)
        = (fun _ : G => (1 : ℂ)) (zOf e) * (fun _ : G => (1 : ℂ)) (zOf e) /
          (fun _ : G => (1 : ℂ)) 1 :=
      suzI_sum_irr_ite S (fun θ : G → ℂ => θ (zOf e) * θ (zOf e) / θ 1) hone_mem
    have i1 : ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) * (if X₁ = θ then 1 else 0)
        = X₁ (zOf e) * X₁ (zOf e) / X₁ 1 :=
      suzI_sum_irr_ite S (fun θ : G → ℂ => θ (zOf e) * θ (zOf e) / θ 1) hX₁mem
    have i2 : ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) * (if X₂ = θ then 1 else 0)
        = X₂ (zOf e) * X₂ (zOf e) / X₂ 1 :=
      suzI_sum_irr_ite S (fun θ : G → ℂ => θ (zOf e) * θ (zOf e) / θ 1) hX₂mem
    rw [i0, i1, i2, hF1, hFX1, hFX2]
  have hK : (cC : ℂ) * cC / (Nat.card G : ℂ) * 576 = cC := by
    rw [div_mul_eq_mul_div, div_eq_iff hNc]
    linear_combination (cC : ℂ) * hcC
  have hN : (7200 : ℂ) = (cC : ℂ) * (1 + (ε₁ : ℂ) * (64 / (n₁ : ℂ)) + (ε₂ : ℂ) * (81 / (n₂ : ℂ))) := by
    calc (7200 : ℂ)
        = ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
            psiFun H χ 0 y * (((Finset.univ.filter (fun u : H => orderOf u = 2 ∧
              (if (y : G) = zOf e then (u : G) ≠ zOf e else (u : G) * (y : G) * (u : G)⁻¹ = (y : G)⁻¹))).card : ℕ) : ℂ) :=
          hχ.sum_N.symm
      _ = ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
            psiFun H χ 0 y * ((cC : ℂ) * cC / (Nat.card G : ℂ) *
              ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) * starRingEnd ℂ (θ (y : G))) := by
          refine Finset.sum_congr rfl fun y hy => ?_
          rw [hpt y (Finset.mem_filter.mp hy).2]
          congr 2
          exact Finset.sum_congr rfl fun θ _ => by ring
      _ = ∑ θ ∈ S, (cC : ℂ) * cC / (Nat.card G : ℂ) * (θ (zOf e) * θ (zOf e) / θ 1) *
            ∑ y ∈ Finset.univ.filter (fun y : H => (y : G) ∈ specialD (zOf e) H),
              psiFun H χ 0 y * starRingEnd ℂ (θ y) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ θ ∈ S, (cC : ℂ) * cC / (Nat.card G : ℂ) * (θ (zOf e) * θ (zOf e) / θ 1) *
            (576 * ((if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
              (ε₁ : ℂ) * (if X₁ = θ then 1 else 0) + (ε₂ : ℂ) * (if X₂ = θ then 1 else 0))) := by
          refine Finset.sum_congr rfl fun θ hθ => ?_
          rw [hT θ ((hmemS θ).mp hθ)]
      _ = (cC : ℂ) * cC / (Nat.card G : ℂ) * 576 * ∑ θ ∈ S, (θ (zOf e) * θ (zOf e) / θ 1) *
            ((if (fun _ : G => (1 : ℂ)) = θ then 1 else 0) +
              (ε₁ : ℂ) * (if X₁ = θ then 1 else 0) + (ε₂ : ℂ) * (if X₂ = θ then 1 else 0)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun θ _ => by ring
      _ = (cC : ℂ) * (1 + (ε₁ : ℂ) * (64 / (n₁ : ℂ)) + (ε₂ : ℂ) * (81 / (n₂ : ℂ))) := by
          rw [hK, hsumθ]
  have hkey : (Nat.card G : ℂ) * (n₁ * n₂ + 64 * ε₁ * n₂ + 81 * ε₂ * n₁) =
      576 * 7200 * (n₁ * n₂) := by
    rw [← hcC, hN]
    field_simp
  have hZ : ((Nat.card G : ℕ) : ℤ) * ((ε₁ * n₁) * (ε₂ * n₂) + 64 * (ε₂ * n₂) + 81 * (ε₁ * n₁)) =
      576 * 7200 * ((ε₁ * n₁) * (ε₂ * n₂)) := by
    have h1 : ((((Nat.card G : ℕ) : ℤ) * ((ε₁ * n₁) * (ε₂ * n₂) + 64 * (ε₂ * n₂) + 81 * (ε₁ * n₁)) :
        ℤ) : ℂ) = (((576 * 7200 * ((ε₁ * n₁) * (ε₂ * n₂)) : ℤ)) : ℂ) := by
      push_cast
      linear_combination (ε₁ * ε₂ : ℂ) * hkey - (64 * (Nat.card G : ℂ) * ε₂ * n₂) * hε₁sq -
        (81 * (Nat.card G : ℂ) * ε₁ * n₁) * hε₂sq
    exact_mod_cast h1
  refine ⟨ε₁ * n₁, ε₂ * n₂, ?_⟩
  unfold StepAArith
  refine ⟨hint1, ?_, ?_, ?_, hZ⟩
  · have hx2 : ε₂ * (n₂ : ℤ) = 423 + 576 * (ε₂ * m) := by
      linear_combination ε₂ * hn2Z + 423 * hε₂sqZ
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-1 - ε₂ * m, by rw [hx2]; ring⟩
  · have h1 : (ε₁ * (n₁ : ℤ)).natAbs = n₁ := by
      rcases hc.ε₁_pm with rfl | rfl <;> simp
    rw [h1]
    exact hn₁dvd
  · have h1 : (ε₂ * (n₂ : ℤ)).natAbs = n₂ := by
      rcases hc.ε₂_pm with rfl | rfl <;> simp
    rw [h1]
    exact hn₂dvd

end CFSG.GH74.QTGen4.Recog.G23.P7
