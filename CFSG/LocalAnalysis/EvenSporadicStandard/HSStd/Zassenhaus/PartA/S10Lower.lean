module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S13Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Count
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Upper

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rho_comm_t {P K : Subgroup G} {t : G} (pd : PairData P K t) (p : ↥P)
    (htp : Commute (p : G) t) :
    ∃ γ : MulAut ↥K, pd.rho p = base γ γ ∨ pd.rho p = base γ γ * tau := by
  by_cases hn : (p : G) ∈ normalizer (K : Set G)
  · exact ⟨_, Or.inl (pd.rho_of_commute_t_of_normalizes p hn htp)⟩
  · have hsw := pd.map_conj_eq_of_not_mem_normalizer p.2 hn
    obtain ⟨a, h, -⟩ := pd.rho_of_commute_t_of_swaps p hsw htp
    exact ⟨a, Or.inr h⟩

theorem card_cent_le_48 {K : Type} [Group K] [Finite K] (hK : commutator K = ⊤)
    (e : K ⧸ center K ≃* alternatingGroup (Fin 6)) (γ : MulAut K) (h2 : γ * γ = 1) (h1 : γ ≠ 1) :
    Nat.card (centralizer ({γ} : Set (MulAut K))) ≤ 48 := by
  let Φ : MulAut K →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (autQuot K)
  have hΦ : Function.Injective Φ := (MulAut.congr e).injective.comp (autQuot_injective hK)
  have hΦ2 : Φ γ * Φ γ = 1 := by rw [← map_mul, h2, map_one]
  have hΦ1 : Φ γ ≠ 1 := fun h => h1 (hΦ (h.trans (map_one Φ).symm))
  refine le_trans ?_ (card_centralizer_le_of_involution (Φ γ) hΦ2 hΦ1)
  refine Nat.card_le_card_of_injective
    (fun x => (⟨Φ x, ?_⟩ : centralizer ({Φ γ} : Set (MulAut (alternatingGroup (Fin 6)))))) ?_
  · have hx : (x : MulAut K) * γ = γ * x := mem_centralizer_singleton_iff.1 x.2
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hx]
  · intro x y hxy
    exact Subtype.ext (hΦ (congrArg Subtype.val hxy))

end Generic

section Main

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem lower_contra (hb : PAB G L t E W z) (a : PA9 L t E z) (he4 : a.dcase = DCase.e4)
    (hH : Nat.card ↥(Cen (t * a.u)) = 88704000)
    (hup : {g : G | IsConj a.u g ∧ g ∈ Cen (t * a.u)}.ncard ≤ 26951) : False := by
  have hub : a.ub = a.u := a.ub_eq
  have S : FusionSetup G L a.Abar t a.u := PA0.fusionSetup hb a.toPA0
  have hu2 : a.u * a.u = 1 := PA0.u_mul_u hb a.toPA0
  have htu : t * a.u = a.u * t := PA0.t_mul_u hb a.toPA0
  have ht2 : t * t = 1 := hb.t_mul_t
  have hpd : PairData (Cen a.u) a.L₁ t := by
    have := PA8.pairData hb a.toPA8
    rw [hub] at this
    exact this
  have h5760 : Nat.card ↥(centralizer ((Vsub t a.u : Subgroup G) : Set G)) = 5760 :=
    PA0.card_cent_V hb a.toPA0
  obtain ⟨hFe, hnct⟩ := a.F₀_e4 he4
  rw [hub] at hFe hnct
  have hCPE : Cen a.u ⊓ centralizer ((a.L₁ ⊔ conjSub t a.L₁ : Subgroup G) : Set G) = a.F₀ := by
    have := a.CPE_eq
    rw [hub] at this
    exact this
  have htP : t ∈ Cen a.u := mem_Cen.2 htu
  let zP : ↥(Cen a.u) := ⟨a.u, mem_Cen.2 rfl⟩
  have hzc : ∀ p : ↥(Cen a.u), p * zP = zP * p := fun p => Subtype.ext (mem_Cen.1 p.2)
  have hz2 : zP * zP = 1 := Subtype.ext hu2
  have hz1 : zP ≠ 1 := fun h => S.u_ne (congrArg Subtype.val h)
  have hrho_one : ∀ p : ↥(Cen a.u), hpd.rho p = 1 ↔ (p : G) = 1 ∨ (p : G) = a.u := by
    intro p
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := (hpd.rho_eq_one_iff p).1 h
      have hle : a.L₁ ⊔ conjSub t a.L₁ ≤ centralizer ({(p : G)} : Set G) := by
        refine sup_le (fun k hk => mem_centralizer_singleton_iff.2 (h1 k hk).eq.symm) ?_
        rintro _ ⟨k, hk, rfl⟩
        exact mem_centralizer_singleton_iff.2 (h2 k hk).eq.symm
      have hpc : (p : G) ∈ centralizer ((a.L₁ ⊔ conjSub t a.L₁ : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro g hg
        exact (mem_centralizer_singleton_iff.1 (hle hg))
      have hpF : (p : G) ∈ a.F₀ := by
        rw [← hCPE]
        exact ⟨p.2, hpc⟩
      rw [hFe] at hpF
      exact s3l_mem_zpowers_two hu2 hpF
    · intro h
      rw [hpd.rho_eq_one_iff]
      rcases h with h | h
      · rw [h]
        exact ⟨fun k _ => Commute.one_left _, fun k _ => Commute.one_left _⟩
      · have hu : a.u ∈ a.F₀ := by
          rw [hFe]
          exact mem_zpowers _
        rw [← hCPE] at hu
        have hc := hu.2
        rw [h]
        refine ⟨fun k hk => ?_, fun k hk => ?_⟩
        · exact (mem_centralizer_iff.1 hc k (mem_sup_left hk)).symm
        · exact (mem_centralizer_iff.1 hc _ (mem_sup_right (Subgroup.mem_map_of_mem _ hk))).symm
  have hρz : hpd.rho zP = 1 := (hrho_one zP).2 (Or.inr rfl)
  have hker : ∀ p : ↥(Cen a.u), hpd.rho p = 1 → p = 1 ∨ p = zP := by
    intro p hp
    rcases (hrho_one p).1 hp with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  let tPP : ↥(Cen a.u) := ⟨t, htP⟩
  have hρt : hpd.rho tPP = tau := hpd.rho_t
  let aP : ↥(Cen a.u) := tPP * zP
  have hρa : hpd.rho aP = tau := by
    change hpd.rho (tPP * zP) = tau
    rw [map_mul, hρt, hρz, mul_one]
  obtain ⟨α, hα2, hαout, hαfix⟩ := exists_pgl_involution
  let ℓ' : ↥a.Abar := a.eAbar.symm α
  have hℓ'2 : ℓ' * ℓ' = 1 := by
    rw [← map_mul, hα2, map_one]
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hαout ⟨1, map_one _⟩
  have hℓ'1 : ℓ' ≠ 1 := by
    intro h
    apply hα1
    have := congrArg a.eAbar h
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have hℓA : (ℓ' : G) ∈ a.Abar := ℓ'.2
  have hℓ2 : (ℓ' : G) * ℓ' = 1 := congrArg Subtype.val hℓ'2
  have hℓ1 : (ℓ' : G) ≠ 1 := fun h => hℓ'1 (Subtype.ext h)
  have hℓe : a.eAbar ⟨(ℓ' : G), hℓA⟩ = α := by
    show a.eAbar ℓ' = α
    exact MulEquiv.apply_symm_apply _ _
  obtain ⟨hc1, hc2⟩ := a.tab_PGL (ℓ' : G) hℓA hℓ2 hℓ1 (by rw [hℓe]; exact hαout)
    (by intro x hx; rw [hℓe]; exact hαfix x hx)
  have hℓL : (ℓ' : G) ∈ L := (a.Abar_le hℓA).1
  have hℓu : (ℓ' : G) * a.u = a.u * ℓ' := S.A_u _ hℓA
  have hℓt : (ℓ' : G) * t = t * ℓ' := S.t_comm _ hℓL
  have hℓP : (ℓ' : G) ∈ Cen a.u := mem_Cen.2 hℓu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hℓo : orderOf (ℓ' : G) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hℓ2) hℓ1
  have huo : orderOf a.u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) S.u_ne
  have huℓ2 : a.u * ℓ' * (a.u * ℓ') = 1 := by
    calc a.u * ℓ' * (a.u * ℓ') = a.u * (ℓ' * a.u) * ℓ' := by simp only [mul_assoc]
      _ = a.u * (a.u * ℓ') * ℓ' := by rw [hℓu]
      _ = (a.u * a.u) * (ℓ' * ℓ') := by simp only [mul_assoc]
      _ = 1 := by rw [hu2, hℓ2, one_mul]
  have huℓ1 : a.u * (ℓ' : G) ≠ 1 := by
    intro h
    have h1 : (ℓ' : G) = a.u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [inv_eq_of_mul_eq_one_right hu2] at h1
    have h2 := Subgroup.disjoint_def.1 S.disj (mem_zpowers a.u) (h1 ▸ hℓA)
    exact S.u_ne h2
  have huℓo : orderOf (a.u * ℓ') = 2 := orderOf_eq_prime (by rw [pow_two]; exact huℓ2) huℓ1
  have huL : a.u ∈ L := PA0.u_mem_L a.toPA0
  have hL : IsSporadic ↥L .HS := hb.setting.2.1
  obtain ⟨g₁, hg₁L, hg₁⟩ := exists_conj_in_L hL hℓL huL hℓo huo (hc1.trans a.card_Lu.symm)
  obtain ⟨g₂, hg₂L, hg₂⟩ := exists_conj_in_L hL (mul_mem huL hℓL) huL huℓo huo
    (hc2.trans a.card_Lu.symm)
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 hb.t_cent l hl
  have hac : IsConj (t * a.u) (t * ℓ') := by
    refine isConj_iff.2 ⟨g₁⁻¹, ?_⟩
    have e : g₁⁻¹ * a.u * g₁ = ℓ' := by
      calc g₁⁻¹ * a.u * g₁ = g₁⁻¹ * (g₁ * ℓ' * g₁⁻¹) * g₁ := by rw [hg₁]
        _ = ℓ' := by group
    calc g₁⁻¹ * (t * a.u) * g₁⁻¹⁻¹ = (g₁⁻¹ * t) * (a.u * g₁) := by group
      _ = (t * g₁⁻¹) * (a.u * g₁) := by rw [hct _ (inv_mem hg₁L)]
      _ = t * (g₁⁻¹ * a.u * g₁) := by group
      _ = t * ℓ' := by rw [e]
  have hacz : IsConj (t * a.u) (t * ℓ' * a.u) := by
    refine isConj_iff.2 ⟨g₂⁻¹, ?_⟩
    have e : g₂⁻¹ * a.u * g₂ = a.u * ℓ' := by
      calc g₂⁻¹ * a.u * g₂ = g₂⁻¹ * (g₂ * (a.u * ℓ') * g₂⁻¹) * g₂ := by rw [hg₂]
        _ = a.u * ℓ' := by group
    calc g₂⁻¹ * (t * a.u) * g₂⁻¹⁻¹ = (g₂⁻¹ * t) * (a.u * g₂) := by group
      _ = (t * g₂⁻¹) * (a.u * g₂) := by rw [hct _ (inv_mem hg₂L)]
      _ = t * (g₂⁻¹ * a.u * g₂) := by group
      _ = t * (a.u * ℓ') := by rw [e]
      _ = t * (ℓ' * a.u) := by rw [hℓu]
      _ = t * ℓ' * a.u := (mul_assoc _ _ _).symm
  have hcP : t * (ℓ' : G) ∈ Cen a.u := mem_Cen.2 (by
    calc t * ℓ' * a.u = t * (ℓ' * a.u) := mul_assoc _ _ _
      _ = t * (a.u * ℓ') := by rw [hℓu]
      _ = (t * a.u) * ℓ' := (mul_assoc _ _ _).symm
      _ = (a.u * t) * ℓ' := by rw [htu]
      _ = a.u * (t * ℓ') := mul_assoc _ _ _)
  let ℓP : ↥(Cen a.u) := ⟨ℓ', hℓP⟩
  let cP : ↥(Cen a.u) := tPP * ℓP
  have hρc : hpd.rho cP = tau * hpd.rho ℓP := by
    change hpd.rho (tPP * ℓP) = _
    rw [map_mul, hρt]
  have hρc1 : hpd.rho cP ≠ 1 := by
    intro h
    rcases hker cP h with h1 | h1
    · apply S.t_nmem
      have h2 : t * (ℓ' : G) = 1 := congrArg Subtype.val h1
      have h3 : t = (ℓ' : G)⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [h3]
      exact inv_mem (S.A_le hℓA)
    · apply S.t_nmem
      have h2 : t * (ℓ' : G) = a.u := congrArg Subtype.val h1
      have h3 : t = a.u * (ℓ' : G)⁻¹ := by
        calc t = t * (ℓ' : G) * (ℓ' : G)⁻¹ := by group
          _ = a.u * (ℓ' : G)⁻¹ := by rw [h2]
      rw [h3]
      exact mul_mem S.u_mem (inv_mem (S.A_le hℓA))
  have hℓρ2 : hpd.rho ℓP * hpd.rho ℓP = 1 := by
    rw [← map_mul]
    have : ℓP * ℓP = 1 := Subtype.ext hℓ2
    rw [this, map_one]
  obtain ⟨γ, hγ⟩ := rho_comm_t hpd ℓP hℓt
  have hform : (∃ γ : MulAut ↥a.L₁, hpd.rho cP = base γ γ ∧ γ ≠ 1 ∧ γ * γ = 1) ∨
      ∃ γ : MulAut ↥a.L₁, hpd.rho cP = base γ γ * tau ∧ γ * γ = 1 := by
    rcases hγ with h | h
    · have hγ2 : γ * γ = 1 := by
        rw [h, base_mul_base] at hℓρ2
        exact (base_injective.1 (hℓρ2.trans base_one.symm)).1
      right
      exact ⟨γ, by rw [hρc, h, tau_mul_base], hγ2⟩
    · have hγ2 : γ * γ = 1 := by
        rw [h, base_mul_tau_sq] at hℓρ2
        exact (base_injective.1 (hℓρ2.trans base_one.symm)).1
      left
      have hc : hpd.rho cP = base γ γ := by
        rw [hρc, h, ← mul_assoc, tau_mul_base, mul_assoc, tau_mul_tau, mul_one]
      refine ⟨γ, hc, ?_, hγ2⟩
      intro h1
      apply hρc1
      rw [hc, h1, base_one]
  have hw : ∀ p : ↥(Cen a.u), hpd.rho p * tau * (hpd.rho p)⁻¹ ≠ hpd.rho cP := by
    intro p hp
    let q : ↥(Cen a.u) := p * tPP * p⁻¹
    have hq : hpd.rho q = hpd.rho cP := by
      change hpd.rho (p * tPP * p⁻¹) = _
      rw [map_mul, map_mul, map_inv, hρt]
      exact hp
    have h1 : hpd.rho (q⁻¹ * cP) = 1 := by rw [map_mul, map_inv, hq, inv_mul_cancel]
    apply hnct
    have hqt : IsConj t (q : G) := isConj_iff.2 ⟨(p : G), rfl⟩
    rcases hker _ h1 with h2 | h2
    · have hqc : q = cP := inv_mul_eq_one.1 h2
      have : IsConj (t * a.u) (q : G) := by rw [hqc]; exact hac
      exact hqt.trans this.symm
    · have hqc : q = cP * zP := by
        have := congrArg (fun x => q * x) h2
        simp only [mul_inv_cancel_left] at this
        have h3 : cP = q * zP := this
        calc q = q * zP * zP := by rw [mul_assoc, hz2, mul_one]
          _ = cP * zP := by rw [← h3]
      have : IsConj (t * a.u) (q : G) := by rw [hqc]; exact hacz
      exact hqt.trans this.symm
  have hperf : commutator ↥a.L₁ = ⊤ := a.L₁_comp.2.2.2.1
  obtain ⟨eL⟩ := a.L₁_A6
  have hA : Nat.card (MulAut ↥a.L₁) ≤ 1440 :=
    (card_mulAut_le_of_perfect hperf eL).trans
      (by rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6])
  have hm : Nat.card (centralizer ({hpd.rho cP} : Set (Wr2 (MulAut ↥a.L₁)))) ≤ 4608 := by
    rcases hform with ⟨γ, hc, hγ1, hγ2⟩ | ⟨γ, hc, hγ2⟩
    · rw [hc, card_centralizer_base_self]
      have := card_cent_le_48 hperf eL γ hγ2 hγ1
      calc 2 * Nat.card (centralizer ({γ} : Set (MulAut ↥a.L₁))) ^ 2 ≤ 2 * 48 ^ 2 :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left this 2)
        _ = 4608 := by norm_num
    · rw [hc, card_centralizer_base_mul_tau, hγ2]
      have htop : centralizer ({(1 : MulAut ↥a.L₁)} : Set (MulAut ↥a.L₁)) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        rw [mem_centralizer_singleton_iff]
        simp
      rw [htop, Subgroup.card_top]
      omega
  have hm₁ : Nat.card (centralizer ({aP} : Set ↥(Cen a.u))) ≤ 5760 := by
    rw [← h5760]
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : G), mem_centralizer_Vsub.2 ⟨?_, ?_⟩⟩ :
        centralizer ((Vsub t a.u : Subgroup G) : Set G))) ?_
    · have h1 : (x.1 : G) * (t * a.u) = (t * a.u) * x.1 :=
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
      exact comm_t_of_comm_tu S h1 (mem_Cen.1 x.1.2)
    · exact mem_Cen.1 x.1.2
    · intro x y hxy
      have h : ((x.1 : ↥(Cen a.u)) : G) = ((y.1 : ↥(Cen a.u)) : G) :=
        congrArg (fun w : centralizer ((Vsub t a.u : Subgroup G) : Set G) => (w : G)) hxy
      exact Subtype.ext (Subtype.ext h)
  have hac' : IsConj ((aP : ↥(Cen a.u)) : G) ((cP : ↥(Cen a.u)) : G) := hac
  have hacz' : IsConj ((aP : ↥(Cen a.u)) : G) ((cP * zP : ↥(Cen a.u)) : G) := hacz
  obtain ⟨n₁, n₂, hn12, hP1, hP2⟩ := fibre_class_count hpd.rho aP cP zP hzc hz2 hz1 hker hρz hρa
    hac' hacz' hw hm hm₁
  have hconj : {g : G | IsConj (t * a.u) g ∧ g ∈ Cen a.u}.ncard * Nat.card ↥(Cen (t * a.u)) ≤
      26951 * Nat.card ↥(Cen a.u) :=
    ncard_conj_in_cen_mul_le (t * a.u) a.u (by rw [← set_conj_cen_eq]; exact hup)
  have hN : {g : G | IsConj ((aP : ↥(Cen a.u)) : G) g ∧ g ∈ (Cen a.u : Subgroup G)} =
      {g : G | IsConj (t * a.u) g ∧ g ∈ Cen a.u} := rfl
  rw [hN] at hn12
  rw [hH] at hconj
  have hPpos : 0 < Nat.card ↥(Cen a.u) := Nat.card_pos
  omega

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
