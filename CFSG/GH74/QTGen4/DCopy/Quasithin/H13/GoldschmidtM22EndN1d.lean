module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN1a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN1c
public import CFSG.Quasithin.H13.GoldschmidtM22EndAbs
public import CFSG.Quasithin.H13.GoldschmidtM22EndLin
public import CFSG.Quasithin.Vol2.Ch12Sec2H3

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

theorem endN1_F4 (hG : G64Out) (h622 : Stmt6_2_2_F4) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6211 : Stmt6_2_11_F4) (h : Hyp6Sec2 G T M L V)
    (hZS : ch6ZS T L V = V ⊓ UU T L V) :
    ∃ (n : ℕ) (ψ : ↥(HH T) →* Equiv.Perm (Fin n)), (n = 3 ∨ n = 6 ∨ n = 7) ∧
      Function.Surjective ψ ∧ (∀ x : ↥(HH T), ψ x = 1 ↔ (x : G) ∈ CHU T L V) ∧
      ∀ a : ↥(HH T), (a : G) ∈ V → (a : G) ∉ CHU T L V → (ψ a).IsSwap ∧
        ∀ c : ↥(HH T), ((c : G) ∈ Subgroup.normalizer (V : Set G) ↔ ψ c * ψ a = ψ a * ψ c) := by
  have hZ : Nat.card (quasithinOmegaOneCenter T) = 2 := (h622 G T M L V h).2.1
  haveI : Fact (IsElemAbelianMod (UU T L V) (quasithinOmegaOneCenter T)) :=
    ⟨isElemAbelianMod_UU_F4 h h6210 hZ⟩
  obtain ⟨z₀, hz₀, hz₀Z, hw⟩ := exists_z0 h hZ
  have hw1 : zt T L V z₀ hz₀ ≠ 1 := fun h1 => hz₀Z ((tmk_eq_one_iff _).mp h1)
  obtain ⟨v₀, hv₀V, hv₀C⟩ : ∃ v₀ ∈ V, v₀ ∉ CHU T L V := by
    by_contra hcon
    push Not at hcon
    exact not_V_le_CHU_F4 h h6210 fun v hv => hcon v hv
  set a : ↥(HH T) := ⟨v₀, V_le_HH h hZ hv₀V⟩ with ha
  have haV : (a : G) ∈ V := hv₀V
  have ha1 : rep T L V a ≠ 1 := fun h1 => hv₀C ((rep_eq_one_iff a).mp h1)
  have ha2 : rep T L V a * rep T L V a = 1 := by
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by
      simpa [pow_two] using h.toHyp611.isElemAbelian.2 (a : G) haV)
    rw [this, map_one]
  have hcomm := commV_rep_eq_F4 h h6210 hZS z₀ hz₀ hw a haV ha1
  have htr : Nat.card (commV (Subgroup.zpowers (rep T L V a))) = 2 := by
    rw [hcomm, Nat.card_zpowers]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hw1
    exact Sec.sq_eq_one _ _ _
  have hspan := span_rep h z₀ hz₀ hw
  rw [← hcomm] at hspan

  have hTH : T ≤ HH T := T_le_HH T
  have hTsyl : IsPGroup 2 (T.subgroupOf (HH T)) ∧ ¬ 2 ∣ (T.subgroupOf (HH T)).index := by
    refine ⟨h.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm, fun hd => h.sylow.2 ?_⟩
    have := Subgroup.relIndex_mul_index hTH
    exact hd.trans (Dvd.intro _ this)
  have haT : a ∈ T.subgroupOf (HH T) := h.toHyp611.le_T haV
  have hcent : ∀ t ∈ T.subgroupOf (HH T),
      rep T L V t * rep T L V a = rep T L V a * rep T L V t := fun t ht =>
    rep_comm_of_normalizer_F4 h h6211 a haV ha1 t (h.toHyp611.T_le_normalizer ht)
  obtain ⟨hXc, hXcomm, hcase⟩ := transvection_outcome_hom hG (Sec.sq_eq_one _ _)
    (rep T L V) (isQuotientOfSQTK_HH_F4 h hZ h6210) (rep_o2_F4 h h6210) ha2 ha1 htr hspan hTsyl haT
    hcent

  suffices hsuf : ∀ (n : ℕ), (n = 3 ∨ n = 6 ∨ n = 7) →
      ∀ e : (rep T L V).range ≃* Equiv.Perm (Fin n),
        (e ⟨rep T L V a, ⟨a, rfl⟩⟩).IsSwap →
      ∃ (n' : ℕ) (ψ : ↥(HH T) →* Equiv.Perm (Fin n')), (n' = 3 ∨ n' = 6 ∨ n' = 7) ∧
        Function.Surjective ψ ∧ (∀ x : ↥(HH T), ψ x = 1 ↔ (x : G) ∈ CHU T L V) ∧
        ∀ b : ↥(HH T), (b : G) ∈ V → (b : G) ∉ CHU T L V → (ψ b).IsSwap ∧
          ∀ c : ↥(HH T), ((c : G) ∈ Subgroup.normalizer (V : Set G) ↔
            ψ c * ψ b = ψ b * ψ c) by
    rcases hcase with ⟨n, hn2, hn5, hcard, ⟨e⟩⟩ | ⟨n, hn, θ, hsw⟩
    ·
      have hn2' : n = 2 := by
        by_contra hne
        have hn3 : 3 ≤ n := by omega
        have hform := rep_form_F4 h h6210 hZS z₀ hz₀ hw a haV
        obtain ⟨g, ⟨x, rfl⟩, hgw, hga⟩ := exists_mem_not_comm (Sec.sq_eq_one _ _) hn3 hcard
          ⟨e⟩ hw1 hform ha1
        have hxN := mem_normalizer_ZS_of_fix h hZ z₀ hz₀ hw x hgw
        have hxV : (x : G) ∈ Subgroup.normalizer (V : Set G) :=
          HH_inf_normalizer_ZS_le_F4 h h629 ⟨x.2, hxN⟩
        exact hga (rep_comm_of_normalizer_F4 h h6211 a haV ha1 x hxV)
      subst hn2'
      obtain ⟨e₃⟩ := GL4.nonempty_gl2_mulEquiv_perm3
      have hsw : ((e.trans e₃) ⟨rep T L V a, ⟨a, rfl⟩⟩).IsSwap := by
        refine isSwap_of_sq_fin3 _ ?_ ?_
        · intro h1
          have := (e.trans e₃).injective (h1.trans (map_one _).symm)
          exact ha1 (congrArg Subtype.val this)
        · rw [← map_mul]
          have : (⟨rep T L V a, ⟨a, rfl⟩⟩ : ↥(rep T L V).range) *
              ⟨rep T L V a, ⟨a, rfl⟩⟩ = 1 := Subtype.ext ha2
          rw [this, map_one]
      exact hsuf 3 (Or.inl rfl) (e.trans e₃) hsw
    · exact hsuf n (by omega) θ hsw
  intro n hn e hsw
  refine ⟨n, e.toMonoidHom.comp (rep T L V).rangeRestrict, hn, ?_, ?_, ?_⟩
  · exact e.surjective.comp (rep T L V).rangeRestrict_surjective
  · intro x
    have : (e.toMonoidHom.comp (rep T L V).rangeRestrict) x = 1 ↔ rep T L V x = 1 := by
      constructor
      · intro h1
        have h2 : e ((rep T L V).rangeRestrict x) = 1 := h1
        have := e.injective (h2.trans (map_one e).symm)
        exact congrArg Subtype.val this
      · intro h1
        have h2 : (rep T L V).rangeRestrict x = 1 := Subtype.ext h1
        show e ((rep T L V).rangeRestrict x) = 1
        rw [h2, map_one]
    rw [this, rep_eq_one_iff]
  · intro b hbV hbC
    have hb1 : rep T L V b ≠ 1 := fun h1 => hbC ((rep_eq_one_iff b).mp h1)
    have hab := rep_eq_of_mem_V_F4 h h6211 a b haV hbV ha1 hb1
    set ψ := e.toMonoidHom.comp (rep T L V).rangeRestrict with hψ
    have hb : ψ b = e ⟨rep T L V a, ⟨a, rfl⟩⟩ := by
      show e ((rep T L V).rangeRestrict b) = _
      congr 1
      exact Subtype.ext hab.symm
    have hψ : ∀ c : ↥(HH T), ψ c = e ((rep T L V).rangeRestrict c) := fun c => rfl
    refine ⟨hb ▸ hsw, fun c => ⟨fun hc => ?_, fun hc => ?_⟩⟩
    · have hcomm := rep_comm_of_normalizer_F4 h h6211 a haV ha1 c hc
      have h1 : (rep T L V).rangeRestrict c * (rep T L V).rangeRestrict b =
          (rep T L V).rangeRestrict b * (rep T L V).rangeRestrict c := by
        apply Subtype.ext
        show rep T L V c * rep T L V b = rep T L V b * rep T L V c
        rw [← hab]
        exact hcomm
      show e ((rep T L V).rangeRestrict c) * e ((rep T L V).rangeRestrict b) =
        e ((rep T L V).rangeRestrict b) * e ((rep T L V).rangeRestrict c)
      rw [← map_mul e, ← map_mul e, h1]
    · have hc' : e ((rep T L V).rangeRestrict c) * e ((rep T L V).rangeRestrict b) =
          e ((rep T L V).rangeRestrict b) * e ((rep T L V).rangeRestrict c) := hc
      rw [← map_mul e, ← map_mul e] at hc'
      have h1 := e.injective hc'
      have h2 : rep T L V c * rep T L V b = rep T L V b * rep T L V c := congrArg Subtype.val h1
      rw [← hab] at h2
      exact normalizer_V_of_rep_comm_F4 h hZ h6210 hZS z₀ hz₀ hz₀Z hw a haV ha1 h629 c h2

end CFSG.Quasithin.H13.GM22
