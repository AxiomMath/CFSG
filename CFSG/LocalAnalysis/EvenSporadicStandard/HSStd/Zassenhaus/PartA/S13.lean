module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S13Aut

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section General

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem isConj_t_mul_of_pab (hb : PAB G L t E W z) {w : G} (hwL : w ∈ L) (hw2 : orderOf w = 2)
    (hcw : Nat.card ↥(L ⊓ centralizer ({w} : Set G)) = 2880) (htw : IsConj t (t * w)) :
    ∀ ℓ ∈ L, ℓ * ℓ = 1 → IsConj t (t * ℓ) := by
  intro ℓ hℓ hℓ2
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  by_cases h1 : ℓ = 1
  · subst h1
    rw [mul_one]
  have hord : orderOf ℓ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) h1
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 hb.t_cent l hl
  have key : ∀ m ∈ L, ∀ ℓ' : G, m * ℓ * m⁻¹ = ℓ' → IsConj (t * ℓ) (t * ℓ') := by
    intro m hm ℓ' h
    refine isConj_iff.2 ⟨m, ?_⟩
    rw [← h]
    calc m * (t * ℓ) * m⁻¹ = (m * t) * ℓ * m⁻¹ := by simp only [mul_assoc]
      _ = t * m * ℓ * m⁻¹ := by rw [hct m hm]
      _ = t * (m * ℓ * m⁻¹) := by simp only [mul_assoc]
  have hzL : z ∈ L := hb.E_le hb.z_mem
  have hz1 : z ≠ 1 := by
    intro hz
    have h3 : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 7680 := hb.z_class
    rw [hz] at h3
    have : (centralizer ({(1 : G)} : Set G)) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [mem_centralizer_singleton_iff]
      simp
    rw [this, inf_top_eq, card_eq_of_isSporadic_hs hL] at h3
    omega
  have hz2 : orderOf z = 2 := by
    have hzz : z ^ 2 = 1 := hb.E_ab.2 z hb.z_mem
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hzz hz1
  rcases card_inf_centralizer_of_involution hL hℓ hord with h | h
  · obtain ⟨g, hg, hgz⟩ := exists_conj_in_L hL hℓ hzL hord hz2 (h.trans (hb.z_class : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 7680).symm)
    have hzt : IsConj t (t * z) := by
      obtain ⟨m, -, hm⟩ := hb.E_fuse z hb.z_mem
      exact isConj_iff.2 ⟨m, hm⟩
    exact hzt.trans (key g hg z hgz).symm
  · obtain ⟨g, hg, hgu⟩ := exists_conj_in_L hL hℓ hwL hord hw2 (h.trans hcw.symm)
    exact htw.trans (key g hg w hgu).symm

theorem ncard_conjCommSet_le_gen (hb : PAB G L t E W z) {w : G} (hw2 : orderOf w = 2)
    (hnc : ¬ IsConj t w) (hcl : ∀ ℓ ∈ L, ℓ * ℓ = 1 → IsConj t (t * ℓ)) :
    (conjCommSet w t).ncard ≤ 21175 := by
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have ht : t * t = 1 := hb.t_mul_t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 hb.t_cent a ha
  have hsub : conjCommSet w t ⊆ {g : G | g ∈ L ∧ orderOf g = 2} := by
    rintro g ⟨hug, hgt⟩
    have hord : orderOf g = 2 := (orderOf_eq_of_isConj' hug).symm.trans hw2
    have hg2 : g * g = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hord
    have hgC : g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hgt.eq
    rw [hb.inner] at hgC
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc hgC with hgL | hgL
    · exact ⟨hgL, hord⟩
    · exfalso
      have hgt' : g * t = t * g := hgt
      have hℓ2 : (t⁻¹ * g) * (t⁻¹ * g) = 1 := by
        rw [hti]
        calc t * g * (t * g) = t * (g * t) * g := by simp only [mul_assoc]
          _ = t * (t * g) * g := by rw [hgt']
          _ = (t * t) * (g * g) := by simp only [mul_assoc]
          _ = 1 := by rw [ht, hg2, one_mul]
      have h1 := hcl _ hgL hℓ2
      rw [hti, ← mul_assoc, ht, one_mul] at h1
      exact hnc (h1.trans hug.symm)
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
    (ncard_involutions_hs_le_of_le L hL).le

theorem ncard_conj_in_P_mul_lt_gen (hb : PAB G L t E W z) {w : G} (hw2 : orderOf w = 2)
    (hnc : ¬ IsConj t w) (hcl : ∀ ℓ ∈ L, ℓ * ℓ = 1 → IsConj t (t * ℓ)) :
    {g : G | IsConj t g ∧ g ∈ centralizer ({w} : Set G)}.ncard * 3840 <
      Nat.card ↥(centralizer ({w} : Set G)) := by
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have hset : {g : G | IsConj t g ∧ g ∈ centralizer ({w} : Set G)} = conjCommSet t w := by
    ext g
    refine and_congr_right fun _ => ?_
    change g ∈ centralizer ({w} : Set G) ↔ g * w = w * g
    exact mem_centralizer_singleton_iff
  have h := ncard_conjCommSet_mul_card_centralizer t w
  rw [card_centralizer_t hL hb.t_cent hb.t_ord hb.inner] at h
  have h2 := ncard_conjCommSet_le_gen hb hw2 hnc hcl
  have hP : 0 < Nat.card ↥(centralizer ({w} : Set G)) := Nat.card_pos
  have h3 : (conjCommSet w t).ncard * Nat.card ↥(centralizer ({w} : Set G)) ≤
      21175 * Nat.card ↥(centralizer ({w} : Set G)) := Nat.mul_le_mul_right _ h2
  have h4 : (conjCommSet t w).ncard * 88704000 ≤ 21175 * Nat.card ↥(centralizer ({w} : Set G)) := by
    rw [h]; exact h3
  rw [hset]
  omega

theorem card_centralizer_t_in_cen_le (hb : PAB G L t E W z) {w : G}
    (hcw : Nat.card ↥(L ⊓ centralizer ({w} : Set G)) = 2880) (htP : t ∈ centralizer ({w} : Set G)) :
    Nat.card (centralizer ({(⟨t, htP⟩ : ↥(centralizer ({w} : Set G)))} :
      Set ↥(centralizer ({w} : Set G)))) ≤ 5760 := by
  have ht : t * t = 1 := hb.t_mul_t
  have hc : ∀ a ∈ L, a * t = t * a := fun a ha => mem_centralizer_iff.1 hb.t_cent a ha
  rw [card_centralizer_subtype (centralizer ({w} : Set G)) htP]
  have hle := card_le_two_mul_card_inf (D := centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G))
    (L := L) (t := t)
    (fun x hx => by
      have := hx.2
      rw [hb.inner] at this
      exact mem_or_inv_mul_mem_of_mem_sup_zpowers ht hc this)
  have hsub : centralizer ({w} : Set G) ⊓ centralizer ({t} : Set G) ⊓ L ≤
      L ⊓ centralizer ({w} : Set G) := fun x hx => ⟨hx.2, hx.1.1⟩
  have h2 := Subgroup.card_le_of_le hsub
  rw [hcw] at h2
  omega

end General

section Diag

variable {G : Type} [Group G] [Finite G] {P K : Subgroup G} {t : G}

omit [Finite G] in
theorem commute_of_rho_eq_one (pd : PairData P K t) {J : Subgroup G} (hJ : J ≤ K ⊔ conjSub t K)
    (w : ↥P) (hw : pd.rho w = 1) : ∀ j ∈ J, (w : G) * j = j * (w : G) := by
  obtain ⟨h1, h2⟩ := (pd.rho_eq_one_iff w).1 hw
  have hK : K ≤ centralizer ({(w : G)} : Set G) := fun k hk =>
    mem_centralizer_singleton_iff.2 (h1 k hk).eq.symm
  have hKt : conjSub t K ≤ centralizer ({(w : G)} : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    exact mem_centralizer_singleton_iff.2 (show t * k * t⁻¹ * (w : G) = (w : G) * (t * k * t⁻¹) from
      (h2 k hk).eq.symm)
  intro j hj
  exact (mem_centralizer_singleton_iff.1 ((sup_le hK hKt) (hJ hj))).symm

theorem rho_diag_cover (pd : PairData P K t) (Ab J : Subgroup G)
    (hAbP : Ab ≤ P) (hAbt : ∀ x ∈ Ab, x * t = t * x) (hJAb : J ≤ Ab)
    (hJH : J ≤ K ⊔ conjSub t K)
    (hCJ : ∀ x ∈ Ab, (∀ j ∈ J, x * j = j * x) → x = 1)
    (hAb : Nat.card Ab = 1440) (hA : Nat.card (MulAut ↥K) ≤ 1440) :
    Nat.card (MulAut ↥K) = 1440 ∧ (∀ d : MulAut ↥K, base d d ∈ pd.rho.range) ∧
      ∀ a : MulAut ↥K, a * a = 1 → a ≠ 1 → ∃ (x : G) (hx : x ∈ Ab), x * x = 1 ∧
        (pd.rho ⟨x, hAbP hx⟩ = base a a ∨ pd.rho ⟨x, hAbP hx⟩ = base a a * tau) := by
  let φ : ↥Ab →* Wr2 (MulAut ↥K) := pd.rho.comp (Subgroup.inclusion hAbP)
  have hφ : ∀ x : ↥Ab, φ x = pd.rho ⟨x, hAbP x.2⟩ := fun x => rfl
  have htau : (tau : Wr2 (MulAut ↥K)) ≠ 1 := by
    intro h
    have := base_ne_base_mul_tau (1 : MulAut ↥K) 1 1 1
    rw [base_one, one_mul] at this
    exact this h.symm
  have hone : ∀ x : ↥Ab, φ x = 1 → x = 1 := by
    intro x hx
    have := commute_of_rho_eq_one pd hJH ⟨x, hAbP x.2⟩ hx
    have h1 : (x : G) = 1 := hCJ x x.2 (fun j hj => this j hj)
    exact Subtype.ext h1
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    exact hone
  have htauR : ∀ x : ↥Ab, φ x ≠ tau := by
    intro x hx
    let w : ↥P := ⟨(x : G) * t, mul_mem (hAbP x.2) pd.t_mem⟩
    have hw : pd.rho w = 1 := by
      have : w = ⟨x, hAbP x.2⟩ * ⟨t, pd.t_mem⟩ := rfl
      rw [this, map_mul, pd.rho_t, ← hφ, hx, tau_mul_tau]
    have hc := commute_of_rho_eq_one pd hJH w hw
    have hx1 : (x : G) = 1 := by
      refine hCJ x x.2 (fun j hj => ?_)
      have e := hc j hj
      have hjt := hAbt j (hJAb hj)
      show (x : G) * j = j * x
      apply mul_right_cancel (b := t)
      calc (x : G) * j * t = x * (j * t) := mul_assoc _ _ _
        _ = x * (t * j) := by rw [hjt]
        _ = x * t * j := (mul_assoc _ _ _).symm
        _ = j * (x * t) := e
        _ = j * x * t := (mul_assoc _ _ _).symm
    have : x = 1 := Subtype.ext hx1
    rw [this, map_one] at hx
    exact htau hx.symm
  have hRcard : Nat.card φ.range = 1440 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, hAb]
  have hRc : φ.range ≤ centralizer ({tau} : Set (Wr2 (MulAut ↥K))) := by
    rintro _ ⟨x, rfl⟩
    rw [mem_centralizer_singleton_iff, ← pd.rho_t, hφ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAbt x x.2)
  have hτ : (tau : Wr2 (MulAut ↥K)) ∉ φ.range := by
    rintro ⟨x, hx⟩
    exact htauR x hx
  obtain ⟨hAeq, hcov⟩ := diag_cover hA φ.range hRcard hRc hτ
  have htR : (tau : Wr2 (MulAut ↥K)) ∈ pd.rho.range := ⟨⟨t, pd.t_mem⟩, pd.rho_t⟩
  have hRle : φ.range ≤ pd.rho.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  refine ⟨hAeq, fun d => ?_, fun a ha ha1 => ?_⟩
  · rcases hcov d with h | h
    · exact hRle h
    · have := pd.rho.range.mul_mem (hRle h) htR
      rwa [mul_assoc, tau_mul_tau, mul_one] at this
  · have hsq1 : base a a * base a a = 1 := by
      rw [base_mul_base, ha, base_one]
    have hsq2 : (base a a * tau) * (base a a * tau) = 1 := by
      rw [base_mul_tau_sq, ha, base_one]
    rcases hcov a with h | h
    · obtain ⟨x, hx⟩ := h
      refine ⟨x, x.2, ?_, Or.inl hx⟩
      have : φ (x * x) = φ 1 := by rw [map_mul, hx, hsq1, map_one]
      exact congrArg Subtype.val (hφinj this)
    · obtain ⟨x, hx⟩ := h
      refine ⟨x, x.2, ?_, Or.inr hx⟩
      have : φ (x * x) = φ 1 := by rw [map_mul, hx, hsq2, map_one]
      exact congrArg Subtype.val (hφinj this)

end Diag

section Main

set_option linter.unusedSectionVars false

@[expose] def StepS13Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (t : G) (E W : Subgroup G) (z : G)
    (hb : PAB G L t E W z) (a : PA10 L t E z),
    Nonempty (MulAut ↥a.L₁ ≃* MulAut (alternatingGroup (Fin 6))) ∧
      (PA8.pairData hb a.toPA9.toPA8).rho.range = ⊤

theorem s13_full : StepS13Full := by
  intro G _ _ L t E W z hb a
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have pd := PA8.pairData hb a.toPA9.toPA8
  have hub : a.ub = a.u := a.ub_eq
  have hub2 : orderOf a.ub = 2 := a.ub_ord
  have hubL : a.ub ∈ L := hub ▸ (a.K₀_le a.u_mem).1
  have hcub : Nat.card ↥(L ⊓ centralizer ({a.ub} : Set G)) = 2880 := by
    rw [hub]; exact a.card_Lu
  have hcomm : a.ub * t = t * a.ub := PA5.comm_t_ub hb a.toPA9.toPA8.toPA7.toPA6.toPA5
  have htub : IsConj t (t * a.ub) := by
    obtain ⟨hu1, hu1c, -, htu1, -⟩ := a.d8_props a.d8_case
    have hu1sq : a.u₁ * a.u₁ = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hu1
    have hcc : a.u₁ * a.ub = a.ub * a.u₁ := mem_Cen.1 hu1c
    have e1 : t * a.u₁ = a.ub * a.u₁ * t := mul_inv_eq_iff_eq_mul.1 htu1
    refine isConj_iff.2 ⟨a.u₁, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu1sq]
    calc a.u₁ * t * a.u₁ = a.u₁ * (t * a.u₁) := by rw [mul_assoc]
      _ = a.u₁ * (a.ub * a.u₁ * t) := by rw [e1]
      _ = (a.u₁ * a.ub) * a.u₁ * t := by simp only [mul_assoc]
      _ = (a.ub * a.u₁) * a.u₁ * t := by rw [hcc]
      _ = a.ub * (a.u₁ * a.u₁) * t := by simp only [mul_assoc]
      _ = a.ub * t := by rw [hu1sq, mul_one]
      _ = t * a.ub := hcomm
  have hcl := isConj_t_mul_of_pab hb hubL hub2 hcub htub
  have hUB := ncard_conj_in_P_mul_lt_gen hb hub2 a.ub_nconj hcl
  have hCt := card_centralizer_t_in_cen_le hb hcub pd.t_mem
  have hker : Nat.card pd.rho.ker ≤ 4 := by
    rw [pd.ker_rho]
    have hF : Nat.card a.F₀ = 4 := a.F₀_card a.d8_case
    rw [← Subgroup.card_map_of_injective (Cen a.ub).subtype_injective,
      Subgroup.subgroupOf_map_subtype, ← hF]
    refine Subgroup.card_le_of_le ?_
    rw [← a.CPE_eq]
    rintro g ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h3, mem_centralizer_iff.2 fun h hh => ?_⟩
    have hle : a.L₁ ⊔ conjSub t a.L₁ ≤ Cen g :=
      sup_le (fun k hk => mem_Cen.2 (mem_centralizer_iff.1 h1 k hk))
        (fun k hk => mem_Cen.2 (mem_centralizer_iff.1 h2 k hk))
    exact mem_Cen.1 (hle hh)
  have hAbP : a.Abar ≤ Cen a.ub := fun x hx => by
    have := (a.Abar_le hx).2
    rw [hub]
    exact this
  have hAbt : ∀ x ∈ a.Abar, x * t = t * x := fun x hx =>
    mem_centralizer_iff.1 hb.t_cent x (a.Abar_le hx).1
  have hCJ : ∀ x ∈ a.Abar, (∀ j ∈ (derivedIn a.Abar : Subgroup G), x * j = j * x) → x = 1 := by
    intro x hx h
    have hxC : x ∈ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
      mem_centralizer_iff.2 fun j hj => (h j hj).symm
    have hxm : x ∈ L ⊓ centralizer ((derivedIn a.Abar : Subgroup G) : Set G) :=
      ⟨(a.Abar_le hx).1, hxC⟩
    rw [a.C_L_J] at hxm
    exact (Subgroup.disjoint_def.1 a.Abar_disj) hxm hx
  have hAb : Nat.card a.Abar = 1440 := by
    rw [Nat.card_congr a.eAbar.toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6
  have hperf : commutator ↥a.L₁ = ⊤ := a.L₁_comp.2.2.2.1
  obtain ⟨e⟩ := a.L₁_A6
  have hA : Nat.card (MulAut ↥a.L₁) ≤ 1440 := by
    refine (card_mulAut_le_of_perfect hperf e).trans ?_
    rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6]
  obtain ⟨hA1440, hdiag, hx⟩ := rho_diag_cover pd a.Abar (derivedIn a.Abar) hAbP hAbt
    (derivedIn_le a.Abar) a.J_le hCJ hAb hA
  let Φ : MulAut ↥a.L₁ ≃* MulAut (alternatingGroup (Fin 6)) := autEquiv hperf e (by
    rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6, hA1440])
  have hCA : ∀ b : MulAut ↥a.L₁, b * b = 1 → b ≠ 1 →
      Nat.card (centralizer ({b} : Set (MulAut ↥a.L₁))) ≤ 48 := by
    intro b hb2 hb1
    refine card_centralizer_le_of_equiv Φ 48 b (card_centralizer_le_of_involution (Φ b) ?_ ?_)
    · rw [← map_mul, hb2, map_one]
    · intro h
      exact hb1 (Φ.injective (h.trans (map_one Φ).symm))
  have hgen := closure_involutions_of_equiv Φ closure_involutions_eq_top
  refine ⟨⟨Φ⟩, range_eq_top_of_conj_count pd.t_mem pd.rho pd.rho_t hker hA1440 hCA hgen hdiag hCt
    ?_ hUB⟩
  intro b hb2 hb1
  obtain ⟨x, hxA, hxx, hρ⟩ := hx b hb2 hb1
  exact ⟨⟨x, hAbP hxA⟩, hcl x (a.Abar_le hxA).1 hxx, hρ⟩

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
