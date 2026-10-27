module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Pgl

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem isConj_t_mul_of_card_7680 (hb : PAB G L t E W z) {ℓ : G} (hℓ : ℓ ∈ L)
    (hord : orderOf ℓ = 2) (h : Nat.card ↥(L ⊓ centralizer ({ℓ} : Set G)) = 7680) :
    IsConj t (t * ℓ) := by
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 hb.t_cent l hl
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
  obtain ⟨g, hg, hgz⟩ := exists_conj_in_L hL hℓ hzL hord hz2
    (h.trans (hb.z_class : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 7680).symm)
  have hzt : IsConj t (t * z) := by
    obtain ⟨m, -, hm⟩ := hb.E_fuse z hb.z_mem
    exact isConj_iff.2 ⟨m, hm⟩
  have key : IsConj (t * ℓ) (t * z) := by
    refine isConj_iff.2 ⟨g, ?_⟩
    rw [← hgz]
    calc g * (t * ℓ) * g⁻¹ = (g * t) * ℓ * g⁻¹ := by simp only [mul_assoc]
      _ = t * g * ℓ * g⁻¹ := by rw [hct g hg]
      _ = t * (g * ℓ * g⁻¹) := by simp only [mul_assoc]
  exact hzt.trans key.symm

theorem PA8.isConj_t_u_d8 (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u)
    (hd8 : a.dcase = DCase.d8) : IsConj t a.u := by
  obtain ⟨hu1, hu1c, -, htu1, -⟩ := a.d8_props hd8
  have hu1sq : a.u₁ * a.u₁ = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hu1
  have hcc : a.u₁ * a.ub = a.ub * a.u₁ := mem_Cen.1 hu1c
  have hcomm : a.ub * t = t * a.ub := PA5.comm_t_ub hb a.toPA7.toPA6.toPA5
  have e1 : t * a.u₁ = a.ub * a.u₁ * t := mul_inv_eq_iff_eq_mul.1 htu1
  have h : IsConj t (t * a.ub) := by
    refine isConj_iff.2 ⟨a.u₁, ?_⟩
    rw [inv_eq_of_mul_eq_one_right hu1sq]
    calc a.u₁ * t * a.u₁ = a.u₁ * (t * a.u₁) := by rw [mul_assoc]
      _ = a.u₁ * (a.ub * a.u₁ * t) := by rw [e1]
      _ = (a.u₁ * a.ub) * a.u₁ * t := by simp only [mul_assoc]
      _ = (a.ub * a.u₁) * a.u₁ * t := by rw [hcc]
      _ = a.ub * (a.u₁ * a.u₁) * t := by simp only [mul_assoc]
      _ = a.ub * t := by rw [hu1sq, mul_one]
      _ = t * a.ub := hcomm
  have : t * a.ub = a.u := by rw [hub, ← mul_assoc, hb.t_mul_t, one_mul]
  rwa [this] at h

theorem PA8.card_ker_rho_le (hb : PAB G L t E W z) (a : PA8 L t E z) {k : ℕ}
    (hk : Nat.card a.F₀ ≤ k) : Nat.card (PA8.pairData hb a).rho.ker ≤ k := by
  have pd := PA8.pairData hb a
  refine le_trans ?_ hk
  rw [pd.ker_rho]
  rw [← Subgroup.card_map_of_injective (Cen a.ub).subtype_injective,
    Subgroup.subgroupOf_map_subtype]
  refine Subgroup.card_le_of_le ?_
  rw [← a.CPE_eq]
  rintro g ⟨⟨h1, h2⟩, h3⟩
  refine ⟨h3, mem_centralizer_iff.2 fun h hh => ?_⟩
  have hle : a.L₁ ⊔ conjSub t a.L₁ ≤ Cen g :=
    sup_le (fun k hk => mem_Cen.2 (mem_centralizer_iff.1 h1 k hk))
      (fun k hk => mem_Cen.2 (mem_centralizer_iff.1 h2 k hk))
  exact mem_Cen.1 (hle hh)

theorem twisted_d8_false (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u)
    (hd8 : a.dcase = DCase.d8) : False := by
  have pd := PA8.pairData hb a
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have huL : a.u ∈ L := (a.K₀_le a.u_mem).1
  obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub
  have hordu : orderOf a.u = 2 := orderOf_eq_two_of_sq hu2 hu1
  have htu : IsConj t a.u := PA8.isConj_t_u_d8 hb a hub hd8
  have htP : t ∈ Cen a.ub := pd.t_mem
  obtain ⟨ℓ, hℓP, hℓL, hℓ2, hℓc, γ, hργ, hγ⟩ := exists_pgl_class hb a hub
  have hac : IsConj ((⟨t, htP⟩ : ↥(Cen a.ub)) : G) ℓ := htu.trans hℓc
  have hCt : Nat.card (centralizer ({(⟨t, htP⟩ : ↥(Cen a.ub))} : Set ↥(Cen a.ub))) ≤ 5760 := by
    rw [card_centralizer_subtype (Cen a.ub) htP]
    refine le_trans (Subgroup.card_le_of_le ?_)
      (card_cen_t_inf_cen_u_le hb.t_cent hb.t_ord hb.inner a.card_Lu)
    intro g hg
    have hg1 : g * a.ub = a.ub * g := mem_Cen.1 hg.1
    have ht2 : g * t = t * g := mem_Cen.1 hg.2
    refine ⟨hg.2, mem_Cen.2 ?_⟩
    rw [hub] at hg1
    apply mul_left_cancel (a := t)
    calc t * (g * a.u) = (t * g) * a.u := by rw [mul_assoc]
      _ = (g * t) * a.u := by rw [ht2]
      _ = g * (t * a.u) := by rw [mul_assoc]
      _ = (t * a.u) * g := hg1
      _ = t * (a.u * g) := by rw [mul_assoc]
  have hker : Nat.card pd.rho.ker ≤ 4 :=
    PA8.card_ker_rho_le hb a (by rw [a.F₀_card hd8])
  obtain ⟨c₁, c₂, hc, hc1, hc2⟩ := two_class_count pd.rho ⟨t, htP⟩ ⟨ℓ, hℓP⟩ pd.rho_t hργ hac hCt
    hker hγ
  have hUB := ncard_conj_in_cen_mul_le t a.ub (n := 21175)
    (by
      refine ncard_conjCommSet_le_of_twist hL hb.t_cent hb.t_ord hb.inner a.ub_ord
        a.ub_nconj ?_ ?_
      · intro ℓ hℓ hord h
        exact isConj_t_mul_of_card_7680 hb hℓ hord h
      · intro ℓ hℓ hord h
        obtain ⟨g, hg, hgℓ⟩ := exists_conj_in_L hL huL hℓ hordu hord (a.card_Lu.trans h.symm)
        exact htu.trans (isConj_iff.2 ⟨g, hgℓ⟩))
  rw [card_centralizer_t hL hb.t_cent hb.t_ord hb.inner] at hUB
  have hPpos : 0 < Nat.card ↥(Cen a.ub) := Nat.card_pos
  have e1 : (4 * (2 * 40 ^ 2) : ℕ) = 12800 := by norm_num
  rw [e1] at hc2
  change {g : G | IsConj t g ∧ g ∈ Cen a.ub}.ncard * 88704000 ≤ 21175 * Nat.card ↥(Cen a.ub)
    at hUB
  change c₁ + c₂ ≤ {g : G | IsConj t g ∧ g ∈ Cen a.ub}.ncard at hc
  change Nat.card ↥(Cen a.ub) ≤ c₁ * 5760 at hc1
  change Nat.card ↥(Cen a.ub) ≤ c₂ * 12800 at hc2
  omega

theorem twisted_e4_false (hb : PAB G L t E W z) (a : PA8 L t E z) (hub : a.ub = t * a.u)
    (he4 : a.dcase = DCase.e4) (hCu : Nat.card ↥(Cen a.u) = 88704000)
    (hInv : {g : G | g ∈ Cen a.u ∧ orderOf g = 2}.ncard ≤ 42351) : False := by
  have pd := PA8.pairData hb a
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  have huL : a.u ∈ L := (a.K₀_le a.u_mem).1
  obtain ⟨hu2, hu1⟩ := PA8.u_sq_twisted hb a hub
  have hut : a.u * t = t * a.u := mem_centralizer_iff.1 hb.t_cent a.u huL
  have huP : a.u ∈ Cen a.ub := u_mem_Cen_ub hb a hub
  obtain ⟨ℓ, hℓP, hℓL, hℓ2, hℓc, γ, hργ, hγ⟩ := exists_pgl_class hb a hub
  have hCu' : Nat.card (centralizer ({(⟨a.u, huP⟩ : ↥(Cen a.ub))} : Set ↥(Cen a.ub))) ≤ 5760 := by
    rw [card_centralizer_subtype (Cen a.ub) huP]
    refine le_trans (Subgroup.card_le_of_le ?_)
      (card_cen_t_inf_cen_u_le hb.t_cent hb.t_ord hb.inner a.card_Lu)
    intro g hg
    have hg1 : g * a.ub = a.ub * g := mem_Cen.1 hg.1
    have hg2 : g * a.u = a.u * g := mem_Cen.1 hg.2
    refine ⟨mem_Cen.2 ?_, hg.2⟩
    rw [hub] at hg1
    apply mul_right_cancel (b := a.u)
    calc g * t * a.u = g * (t * a.u) := by rw [mul_assoc]
      _ = (t * a.u) * g := hg1
      _ = t * (a.u * g) := by rw [mul_assoc]
      _ = t * (g * a.u) := by rw [hg2]
      _ = t * g * a.u := by rw [mul_assoc]
  have hker : Nat.card pd.rho.ker ≤ 2 := by
    refine PA8.card_ker_rho_le hb a ?_
    rw [(a.F₀_e4 he4).1, Nat.card_zpowers, a.ub_ord]
  obtain ⟨c₁, c₂, hc, hc1, hc2⟩ := two_class_count pd.rho ⟨a.u, huP⟩ ⟨ℓ, hℓP⟩
    (rho_u_eq_tau hb a hub) hργ hℓc hCu' hker hγ
  have hS1 : (conjCommSet a.ub a.u).ncard ≤ 26951 := by
    have htU : t ∈ Cen a.u := mem_Cen.2 hut.symm
    set U : Subgroup G := Cen a.u with hU
    let cls : Set G := subgroupConjClass U ⟨t, htU⟩
    have hcls : cls.ncard * 5760 ≥ 88704000 := by
      have h1 := ncard_subgroupConjClass_mul_card_centralizer U ⟨t, htU⟩
      have h2 : Nat.card (centralizer ({(⟨t, htU⟩ : ↥U)} : Set ↥U)) ≤ 5760 := by
        rw [card_centralizer_subtype U htU]
        refine le_trans (Subgroup.card_le_of_le ?_)
          (card_cen_t_inf_cen_u_le hb.t_cent hb.t_ord hb.inner a.card_Lu)
        intro g hg
        exact ⟨hg.2, hg.1⟩
      have h3 : cls.ncard * Nat.card (centralizer ({(⟨t, htU⟩ : ↥U)} : Set ↥U)) = Nat.card U := h1
      rw [hCu] at h3
      calc 88704000 = cls.ncard * Nat.card (centralizer ({(⟨t, htU⟩ : ↥U)} : Set ↥U)) := h3.symm
        _ ≤ cls.ncard * 5760 := Nat.mul_le_mul_left _ h2
    have hdisj : Disjoint (conjCommSet a.ub a.u) cls := by
      rw [Set.disjoint_left]
      rintro g ⟨hg1, -⟩ ⟨x, hx, rfl⟩
      exact a.ub_nconj ((MonoidHom.map_isConj U.subtype hx).trans hg1.symm)
    have hsub : conjCommSet a.ub a.u ∪ cls ⊆ {g : G | g ∈ Cen a.u ∧ orderOf g = 2} := by
      rintro g (⟨hg1, hgu⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨mem_Cen.2 hgu.eq, (orderOf_eq_of_isConj' hg1).symm.trans a.ub_ord⟩
      · exact ⟨x.2, (orderOf_eq_of_isConj' (MonoidHom.map_isConj U.subtype hx)).symm.trans
          hb.t_ord⟩
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hInv
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)] at hle
    omega
  have hUB := ncard_conj_in_cen_mul_le a.u a.ub (n := 26951) hS1
  rw [hCu] at hUB
  have hPpos : 0 < Nat.card ↥(Cen a.ub) := Nat.card_pos
  have e1 : (2 * (2 * 40 ^ 2) : ℕ) = 6400 := by norm_num
  rw [e1] at hc2
  change {g : G | IsConj a.u g ∧ g ∈ Cen a.ub}.ncard * 88704000 ≤ 26951 * Nat.card ↥(Cen a.ub)
    at hUB
  change c₁ + c₂ ≤ {g : G | IsConj a.u g ∧ g ∈ Cen a.ub}.ncard at hc
  change Nat.card ↥(Cen a.ub) ≤ c₁ * 5760 at hc1
  change Nat.card ↥(Cen a.ub) ≤ c₂ * 6400 at hc2
  omega

end

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
