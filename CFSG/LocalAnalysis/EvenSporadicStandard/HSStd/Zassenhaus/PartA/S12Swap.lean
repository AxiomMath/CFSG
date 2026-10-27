module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Conj

variable {G : Type*} [Group G]

theorem conjSub_conjSub {t : G} (ht : t * t = 1) (K : Subgroup G) : conjSub t (conjSub t K) = K := by
  have := map_conj_map_conj K t t
  rw [ht, map_conj_one] at this
  exact this

theorem mem_conjSub {t : G} {K : Subgroup G} {g : G} :
    g ∈ conjSub t K ↔ ∃ k ∈ K, t * k * t⁻¹ = g := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem conj_mem_conjSub {t : G} {K : Subgroup G} {k : G} (hk : k ∈ K) :
    t * k * t⁻¹ ∈ conjSub t K := mem_conjSub.2 ⟨k, hk, rfl⟩

theorem conj_conj_of_sq {t : G} (ht : t * t = 1) (g : G) : t * (t * g * t⁻¹) * t⁻¹ = g := by
  have h : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [h]
  calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
    _ = g := by rw [ht]; group

theorem conjSub_mono {t : G} {K K' : Subgroup G} (h : K ≤ K') : conjSub t K ≤ conjSub t K' :=
  Subgroup.map_mono h

theorem card_conjSub (t : G) (K : Subgroup G) : Nat.card (conjSub t K) = Nat.card K :=
  (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj t) K).toEquiv).symm

theorem map_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2

theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : GorensteinWalter.IsQuasisimple A) : GorensteinWalter.IsQuasisimple B := by
  have hNontriv : Nontrivial B := by
    let : Nontrivial A := hA.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect B := by
    let : Group.IsPerfect A := (Group.isPerfect_def).2 hA.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hSimple : IsSimpleGroup (B ⧸ center B) := by
    have he : (center A).map e.toMonoidHom = center B := map_center_eq_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (center A) (center B) e he)).mp hA.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

theorem isComponentOf_conjSub {E H : Subgroup G} {t : G} (ht : t ∈ H)
    (h : GorensteinWalter.IsComponentOf E H) :
    GorensteinWalter.IsComponentOf (conjSub t E) H := by
  obtain ⟨hEH, hsn, hq⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    exact H.mul_mem (H.mul_mem ht (hEH he)) (H.inv_mem ht)
  · have h1 := hsn.map (f := (MulAut.conj (⟨t, ht⟩ : ↥H)).toMonoidHom)
      (MulEquiv.surjective _)
    convert h1 using 1
    ext ⟨g, hg⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, hEH he⟩, he, rfl⟩
    · rintro ⟨⟨e, heH⟩, he, hge⟩
      exact ⟨e, he, congrArg Subtype.val hge⟩
  · exact isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap (MulAut.conj t) E) hq

theorem conj_mul_conj (t a b : G) : (t * a * t⁻¹) * (t * b * t⁻¹) = t * (a * b) * t⁻¹ := by
  group

theorem s12_conj_comm_iff (t a b : G) :
    (t * a * t⁻¹) * (t * b * t⁻¹) = (t * b * t⁻¹) * (t * a * t⁻¹) ↔ a * b = b * a := by
  rw [conj_mul_conj, conj_mul_conj]
  constructor
  · intro h
    have h2 := congrArg (fun m => t⁻¹ * m * t) h
    simpa [mul_assoc] using h2
  · intro h
    rw [h]

theorem conj_mem_zpowers_of_comm {t u g : G} (h : u * t = t * u) (hg : g ∈ zpowers u) :
    t * g * t⁻¹ ∈ zpowers u := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  have : Commute t (u ^ n) := (Commute.zpow_right (h.symm : Commute t u) n)
  rw [this.mul_inv_cancel]
  exact zpow_mem (mem_zpowers u) n

theorem orderOf_conj_eq (t a : G) : orderOf (t * a * t⁻¹) = orderOf a :=
  MulEquiv.orderOf_eq (MulAut.conj t) a

end Conj


section Swap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

@[expose] def PA11.swapL8 (hb : PAB G L t E W z) (a : PA11 L t E z) : PA8 L t E z :=
  { toPA7 := a.toPA10.toPA9.toPA8.toPA7,
    L₁ := conjSub t a.L₁,
    L₁_comp := isComponentOf_conjSub (PA8.pairData hb a.toPA10.toPA9.toPA8).t_mem a.L₁_comp,
    L₁_ne := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [conjSub_conjSub htt]
      exact fun h => a.L₁_ne h.symm,
    L₁_comm := by
      have htt : t * t = 1 := hb.t_mul_t
      intro g hg h hh
      obtain ⟨g₀, hg₀, rfl⟩ := mem_conjSub.1 hg
      obtain ⟨h₀, hh₀, rfl⟩ := mem_conjSub.1 hh
      rw [conj_conj_of_sq htt]
      exact (a.L₁_comm h₀ hh₀ g₀ hg₀).symm,
    E_eq := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [conjSub_conjSub htt, sup_comm]
      exact a.E_eq,
    L₁_A6 := by
      obtain ⟨e⟩ := a.L₁_A6
      let e₁ : ↥a.L₁ ≃* ↥(conjSub t a.L₁) := MulEquiv.subgroupMap (MulAut.conj t) a.L₁
      have he : (center ↥a.L₁).map e₁.toMonoidHom = center ↥(conjSub t a.L₁) :=
        map_center_eq_of_mulEquiv e₁
      exact ⟨(QuotientGroup.congr (center ↥a.L₁) (center ↥(conjSub t a.L₁)) e₁ he).symm.trans e⟩,
    Z_le := by
      have hcomm : a.ub * t = t * a.ub :=
        PA5.comm_t_ub hb a.toPA10.toPA9.toPA8.toPA7.toPA6.toPA5
      rintro g ⟨z, hz, rfl⟩
      let e₁ : ↥a.L₁ ≃* ↥(conjSub t a.L₁) := MulEquiv.subgroupMap (MulAut.conj t) a.L₁
      have hz0 : e₁.symm z ∈ center ↥a.L₁ := ((Subgroup.centerCongr e₁).symm ⟨z, hz⟩).2
      have h1 := a.Z_le (Subgroup.mem_map.2 ⟨e₁.symm z, hz0, rfl⟩)
      have h2 : ((z : ↥(conjSub t a.L₁)) : G) = t * ((e₁.symm z : ↥a.L₁) : G) * t⁻¹ := by
        have := congrArg Subtype.val (e₁.apply_symm_apply z).symm
        exact this
      show ((z : ↥(conjSub t a.L₁)) : G) ∈ zpowers a.ub
      rw [h2]
      exact conj_mem_zpowers_of_comm hcomm h1,
    perm := by
      have htt : t * t = 1 := hb.t_mul_t
      have pd : PairData (Cen a.ub) a.L₁ t := PA8.pairData hb a.toPA10.toPA9.toPA8
      intro p hp
      rw [map_conj_map_conj]
      rcases pd.perm (p * t) (mul_mem hp pd.t_mem) with h | h
      · right
        rw [conjSub_conjSub htt]
        exact h
      · left
        exact h,
    J_le := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [conjSub_conjSub htt, sup_comm]
      exact a.J_le,
    CPE_eq := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [conjSub_conjSub htt, sup_comm]
      exact a.CPE_eq,
    u₁_CPE := by
      have htt : t * t = 1 := hb.t_mul_t
      intro hd
      rw [conjSub_conjSub htt]
      exact ⟨(a.u₁_CPE hd).2, (a.u₁_CPE hd).1⟩ }

@[expose] def PA11.swapL9 (hb : PAB G L t E W z) (a : PA11 L t E z) : PA9 L t E z :=
  { toPA8 := PA11.swapL8 hb a, ub_eq := by exact a.ub_eq }

@[expose] def PA11.swapL10 (hb : PAB G L t E W z) (a : PA11 L t E z) : PA10 L t E z :=
  { toPA9 := PA11.swapL9 hb a, d8_case := by exact a.d8_case }

theorem PA11.swapL10_y (hb : PAB G L t E W z) (a : PA11 L t E z) :
    (PA11.swapL10 hb a).y = a.y := rfl

@[expose] def PA11.swapL (hb : PAB G L t E W z) (a : PA11 L t E z) : PA11 L t E z :=
  { toPA10 := PA11.swapL10 hb a,
    x := t * a.x * t⁻¹,
    x_mem := conj_mem_conjSub a.x_mem,
    x_ord := by rw [orderOf_conj_eq]; exact a.x_ord,
    x_y := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [PA11.swapL10_y, conj_conj_of_sq htt, a.x_y]
      exact (a.L₁_comm a.x a.x_mem a.x a.x_mem).eq,
    x_O := by
      rw [PA11.swapL10_y, a.O_eq]
      exact mem_sup_right (mem_zpowers _),
    O_eq := by
      have htt : t * t = 1 := hb.t_mul_t
      rw [PA11.swapL10_y, conj_conj_of_sq htt, a.O_eq, sup_comm],
    card_Cy := a.card_Cy,
    X := conjSub t a.X,
    X_le := by
      rintro _ ⟨b, hb, rfl⟩
      have hb' := Subgroup.mem_inf.1 (a.X_le hb)
      refine Subgroup.mem_inf.2 ⟨conj_mem_conjSub hb'.1, ?_⟩
      exact mem_Cen.2 ((s12_conj_comm_iff t b a.x).2 (mem_Cen.1 hb'.2)),
    X_card := by rw [card_conjSub]; exact a.X_card,
    X_three := by
      intro g hg hord
      obtain ⟨hgL, hgc⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨k, hk, rfl⟩ := mem_conjSub.1 hgL
      refine mem_conjSub.2 ⟨k, a.X_three k (Subgroup.mem_inf.2 ⟨hk,
        mem_Cen.2 ((s12_conj_comm_iff t k a.x).1 (mem_Cen.1 hgc))⟩)
        (by rwa [orderOf_conj_eq] at hord), rfl⟩ }

@[expose] noncomputable def PA11.phi (a : PA11 L t E z) : ↥(Cen a.y) →* Wr2 (Equiv.Perm (Fin 5)) :=
  a.ι.comp (oMk (Cen a.y))

omit [Finite G] in
theorem PA11.phi_apply (a : PA11 L t E z) (g : ↥(Cen a.y)) : a.phi g = a.ι (oMk (Cen a.y) g) := rfl

omit [Finite G] in
theorem PA11.phi_conj (a : PA11 L t E z) {g : G} (hg : g ∈ Cen a.y)
    (hg' : t * g * t⁻¹ ∈ Cen a.y) :
    a.phi ⟨t * g * t⁻¹, hg'⟩ = tau * a.phi ⟨g, hg⟩ * tau := by
  have h1 : (⟨t * g * t⁻¹, hg'⟩ : ↥(Cen a.y)) = ⟨t, a.t_cy⟩ * ⟨g, hg⟩ * ⟨t, a.t_cy⟩⁻¹ := rfl
  have h2 := a.ι_t
  rw [h1, map_mul, map_mul, map_inv, a.phi_apply ⟨t, a.t_cy⟩, h2, tau_inv]

omit [Finite G] in
theorem PA11.ub_mul_ub (a : PA11 L t E z) : a.ub * a.ub = 1 := by
  have := pow_orderOf_eq_one a.ub
  rw [a.ub_ord, pow_two] at this
  exact this

@[expose] def PA11.FirstType (a : PA11 L t E z) : Prop :=
  ∃ σ : Equiv.Perm (Fin 5), σ.IsSwap ∧ ∃ hc : a.u₁ ∈ Cen a.y,
    a.ι (oMk (Cen a.y) ⟨a.u₁, hc⟩) = base σ 1

noncomputable def PA11.swapU (hb : PAB G L t E W z) (a : PA11 L t E z) : PA11 L t E z :=
  { a with
    u₁ := t * a.u₁ * t⁻¹,
    d8_props := by
      intro hd
      obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := a.d8_props hd
      have htt : t * t = 1 := hb.t_mul_t
      have hub2 := PA11.ub_mul_ub a
      have hubJ : a.ub ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro h hh
        have hAbar : h ∈ a.Abar := derivedIn_le _ hh
        have := mem_Cen.1 ((Subgroup.mem_inf.1 (a.Abar_le hAbar)).2)
        rw [a.ub_eq]
        exact this
      have hmem : t * a.u₁ * t⁻¹ ∈ Cen a.y := by
        obtain ⟨σ, hσ, hc, -⟩ := o7
        exact mul_mem (mul_mem a.t_cy hc) (inv_mem a.t_cy)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [orderOf_conj_eq]; exact o1
      · rw [o4]
        exact mul_mem (mem_Cen.2 rfl) o2
      · rw [o4]
        exact mul_mem hubJ o3
      · rw [conj_conj_of_sq htt, o4, ← mul_assoc, hub2, one_mul]
      · rw [o4, o5]
        apply le_antisymm
        · refine sup_le le_sup_left (zpowers_le.2 ?_)
          have := mul_mem (mem_sup_left (mem_zpowers a.ub) :
            a.ub ∈ zpowers a.ub ⊔ zpowers (a.ub * a.u₁))
            (mem_sup_right (mem_zpowers (a.ub * a.u₁)) :
            a.ub * a.u₁ ∈ zpowers a.ub ⊔ zpowers (a.ub * a.u₁))
          rwa [← mul_assoc, hub2, one_mul] at this
        · refine sup_le le_sup_left (zpowers_le.2 ?_)
          exact mul_mem (mem_sup_left (mem_zpowers a.ub)) (mem_sup_right (mem_zpowers a.u₁))
      · rw [o4]
        intro h
        apply o6
        have := mul_mem (mem_zpowers a.ub) h
        rwa [← mul_assoc, hub2, one_mul] at this
      · obtain ⟨σ, hσ, hc, hι⟩ := o7
        refine ⟨σ, hσ, hmem, ?_⟩
        have h1 := a.phi_conj hc hmem
        rw [PA11.phi_apply, PA11.phi_apply] at h1
        rcases hι with h | h
        · right
          rw [h1, h, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
        · left
          rw [h1, h, tau_mul_base, mul_assoc, tau_mul_tau, mul_one],
    u₁_CPE := by
      intro hd
      obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := a.d8_props hd
      have hubc : a.ub ∈ centralizer (a.L₁ : Set G) := by
        rw [mem_centralizer_iff]
        intro h hh
        exact mem_Cen.1 (a.L₁_comp.1 hh)
      have hubct : a.ub ∈ centralizer ((conjSub t a.L₁ : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro h hh
        obtain ⟨l, hl, rfl⟩ := mem_conjSub.1 hh
        have hut : Commute a.ub t := (PA5.comm_t_ub hb a.toPA10.toPA9.toPA8.toPA7.toPA6.toPA5)
        have hul : Commute a.ub l := (mem_Cen.1 (a.L₁_comp.1 hl)).symm
        exact ((hut.mul_right hul).mul_right hut.inv_right).symm.eq
      rw [o4]
      exact ⟨mul_mem hubc (a.u₁_CPE hd).1, mul_mem hubct (a.u₁_CPE hd).2⟩ }

theorem PA11.firstType_or (hb : PAB G L t E W z) (a : PA11 L t E z) :
    a.FirstType ∨ (a.swapU hb).FirstType := by
  obtain ⟨-, -, -, -, -, -, σ, hσ, hc, hι⟩ := a.d8_props a.d8_case
  rcases hι with h | h
  · exact Or.inl ⟨σ, hσ, hc, h⟩
  · right
    have hmem : t * a.u₁ * t⁻¹ ∈ Cen a.y := mul_mem (mul_mem a.t_cy hc) (inv_mem a.t_cy)
    refine ⟨σ, hσ, hmem, ?_⟩
    have h1 := a.phi_conj hc hmem
    rw [PA11.phi_apply, PA11.phi_apply] at h1
    show a.ι (oMk (Cen a.y) ⟨t * a.u₁ * t⁻¹, hmem⟩) = base σ 1
    rw [h1, h, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]

end Swap

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
