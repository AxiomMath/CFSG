module

public import CFSG.GH74.Uniqueness.Section172K

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem le_of_forall_sylow_le {Y C : Subgroup X} (hCY : C ≤ Y) (hodd : Odd (Nat.card Y))
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q Y ∧ Q ≤ C) :
    Y ≤ C := by
  have hdvd : Nat.card Y ∣ Nat.card C := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    by_cases h2 : p = 2
    · subst h2
      have hk : k = 0 := by
        by_contra hk
        have : 2 ∣ Nat.card Y := (dvd_pow_self 2 hk).trans hpk
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
      rw [hk, pow_zero]
      exact one_dvd _
    · obtain ⟨Q, hQ, hQC⟩ := h p hp h2
      have : Fact p.Prime := ⟨hp⟩
      have hcard := hQ.card_eq
      have hk : k ≤ (Nat.card Y).factorization p :=
        (hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hpk
      exact (pow_dvd_pow p hk).trans (hcard ▸ Subgroup.card_dvd_of_le hQC)
  exact (Subgroup.eq_of_le_of_card_ge hCY (Nat.le_of_dvd Nat.card_pos hdvd)).ge

theorem ZDSetup.odd_card_D0 (S : ZDSetup X Z M) (h166 : Cor166Stmt Z M) (c : Conf16 Z M)
    {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    Odd (Nat.card ↥(c.D ⊓ cenHull Z (c.t * c.u))) := by
  by_contra hev
  have hev' : 2 ∣ Nat.card ↥(c.D ⊓ cenHull Z (c.t * c.u)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 2 hev'
  have hy : (y' : X) ∈ c.D ⊓ cenHull Z (c.t * c.u) := y'.2
  have hy2 : orderOf (y' : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hy'
  obtain ⟨g, hg⟩ := isConj_iff.mp (S.isConj_u_tu h166 c hB)
  have h1 := Sec172.mem_cenHull_conj S.invariant g⁻¹ (Subgroup.mem_inf.mp hy).2
  rw [show g⁻¹ * (c.t * c.u) * g⁻¹⁻¹ = c.u by rw [← hg]; group] at h1
  have h2 : orderOf (g⁻¹ * (y' : X) * g⁻¹⁻¹) = 2 := orderOf_conj_eq hy2 g⁻¹
  have h3 := hB.invol _ h1 h2
  have h4 : (y' : X) ∈ Z := by
    have h5 := S.invariant.2 _ h3 g⁻¹
    have e : g⁻¹⁻¹ * (g⁻¹ * (y' : X) * g⁻¹⁻¹) * g⁻¹ = y' := by group
    rwa [e] at h5
  exact S.not_mem_Z_of_mem_dGrp c.htM (Subgroup.mem_inf.mp hy).1 h4

theorem ZDSetup.omegaFix_eq_pair (S : ZDSetup X Z M) (h167 : Lemma167Stmt Z M) (c : Conf16 Z M)
    {Y : Subgroup X} (hYD : Y ≤ c.D) (hYodd : Odd (Nat.card Y))
    (htY : c.t ∈ normalizer (Y : Set X)) (hY : ¬ ∀ y ∈ Y, y * c.t = c.t * y) :
    omegaFix M (Y : Set X) = {M, conjugate M c.t} := by
  have hβΩ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  have hMβ : M ≠ conjugate M c.t := by
    intro h
    apply c.htM
    have := conjugate_eq_iff_mem_normalizer.mp h.symm
    rwa [S.prodDisc.normalizer_eq_self] at this
  have hYM : Y ≤ M := hYD.trans inf_le_left
  have hYβ : Y ≤ conjugate M c.t := hYD.trans inf_le_right
  have hMΩ : M ∈ omegaFix M (Y : Set X) :=
    S.prodDisc.mem_omegaFix_iff.mpr ⟨self_mem_omega M, hYM⟩
  have hβΩ' : conjugate M c.t ∈ omegaFix M (Y : Set X) :=
    S.prodDisc.mem_omegaFix_iff.mpr ⟨hβΩ, hYβ⟩
  have hsub : ({M, conjugate M c.t} : Set (Subgroup X)) ⊆ omegaFix M (Y : Set X) := by
    intro γ hγ
    rcases hγ with rfl | rfl
    · exact hMΩ
    · exact hβΩ'
  refine Set.Subset.antisymm ?_ hsub
  intro γ hγ
  by_contra hγ'
  have hγM : γ ≠ M := fun h => hγ' (Or.inl h)
  have hγβ : γ ≠ conjugate M c.t := fun h => hγ' (Or.inr h)
  have h3 : 3 ≤ (omegaFix M (Y : Set X)).ncard := by
    have hsub3 : ({M, conjugate M c.t, γ} : Set (Subgroup X)) ⊆ omegaFix M (Y : Set X) := by
      intro δ hδ
      rcases hδ with rfl | rfl | rfl
      · exact hMΩ
      · exact hβΩ'
      · exact hγ
    have hcard : ({M, conjugate M c.t, γ} : Set (Subgroup X)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_pair hγβ.symm]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hMβ, hγM.symm⟩
    calc 3 = ({M, conjugate M c.t, γ} : Set (Subgroup X)).ncard := hcard.symm
      _ ≤ _ := Set.ncard_le_ncard hsub3 (Set.toFinite _)
  have hZst : IsZStarIn (Y ⊔ zpowers c.t) c.t :=
    S.prodDisc.isZStarIn_of_le_inf_conjugate S.invariant c.ht c.htM hYD htY
  have ht2' : orderOf c.t = 2 := S.invariant.1 c.t c.ht
  have hsyl : ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q Y ∧ Q ≤ Y ⊓ centralizer ({c.t} : Set X) := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have hbotN : c.t ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      simp only [Subgroup.mem_bot]
      exact (conj_eq_one_iff).symm
    obtain ⟨Q, hQ, -, htQ⟩ := exists_invariant_sylow (P := ⊥) hp hp2 ht2' htY hZst bot_le
      (IsPGroup.of_card (n := 0) (by simp)) hbotN
    have hQY : Q ≤ Y := by
      obtain ⟨S', rfl⟩ := hQ
      exact Subgroup.map_subtype_le _
    have hQp : IsPGroup p Q := IsPGroup.of_card hQ.card_eq
    have hΩQ : 3 ≤ (omegaFix M (Q : Set X)).ncard :=
      h3.trans (Set.ncard_le_ncard (omegaFix_anti (fun x hx => hQY hx)) (Set.toFinite _))
    have hc := h167 p hp hp2 Q hQp hΩQ
    have htz : c.t ∈ zHull Z (normalizer (Q : Set X)) := Subgroup.subset_closure ⟨c.ht, htQ⟩
    have htc := Subgroup.mem_centralizer_iff.mp (hc htz)
    refine ⟨Q, hQ, le_inf hQY ?_⟩
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mpr (htc q hq)
  have hYC := le_of_forall_sylow_le (inf_le_left : Y ⊓ centralizer ({c.t} : Set X) ≤ Y) hYodd hsyl
  apply hY
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hYC hy)).2

theorem ZDSetup.normalizer_pair_le (S : ZDSetup X Z M) (c : Conf16 Z M) {Y : Subgroup X}
    (hΩ : omegaFix M (Y : Set X) = {M, conjugate M c.t}) {g : X}
    (hg : g ∈ normalizer (Y : Set X)) : g ∈ c.D ∨ g * c.t⁻¹ ∈ c.D := by
  have ht2 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hβΩ : conjugate M c.t ∈ omega M := ⟨c.t, rfl⟩
  have hMβ : M ≠ conjugate M c.t := by
    intro h
    apply c.htM
    have := conjugate_eq_iff_mem_normalizer.mp h.symm
    rwa [S.prodDisc.normalizer_eq_self] at this
  have hM : conjugate M g ∈ ({M, conjugate M c.t} : Set (Subgroup X)) := by
    rw [← hΩ]
    exact conjugate_mem_omegaFix_of_mem_normalizer hg
      (by rw [hΩ]; exact Set.mem_insert _ _)
  have hβ : conjugate (conjugate M c.t) g ∈ ({M, conjugate M c.t} : Set (Subgroup X)) := by
    rw [← hΩ]
    exact conjugate_mem_omegaFix_of_mem_normalizer hg
      (by rw [hΩ]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rcases hM with hM | hM
  ·
    left
    have hgM : g ∈ M := (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp hM
    rcases hβ with hβ | hβ
    · exact absurd (conjugate_injective g (hM.trans hβ.symm)) hMβ
    · exact Subgroup.mem_inf.mpr ⟨hgM, (S.prodDisc.conjugate_eq_iff_mem hβΩ).mp hβ⟩
  ·
    right
    rcases hβ with hβ | hβ
    · have h1 : conjugate M (g * c.t⁻¹) = M := by
        rw [← conjugate_conjugate, hM, conjugate_conjugate, mul_inv_cancel, conjugate_one]
      have h2 : conjugate (conjugate M c.t) (g * c.t⁻¹) = conjugate M c.t := by
        rw [← conjugate_conjugate, hβ, hti]
      exact Subgroup.mem_inf.mpr ⟨(S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp h1,
        (S.prodDisc.conjugate_eq_iff_mem hβΩ).mp h2⟩
    · exact absurd (conjugate_injective g (hM.trans hβ.symm)) hMβ

omit [Finite X] in
theorem Sec172.eq_one_of_sq {a : X} (h : a * a = 1) (hodd : Odd (orderOf a)) : a = 1 := by
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
  · exact orderOf_eq_one_iff.mp h2
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem Sec172.t_mem_cenHull (c : Conf16 Z M) : c.t ∈ cenHull Z (c.t * c.u) := by
  refine Subgroup.subset_closure ⟨c.ht, ?_⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  calc c.t * (c.t * c.u) = c.t * (c.u * c.t) := by rw [c.t_mul_u_comm]
    _ = (c.t * c.u) * c.t := by group

theorem Sec172.t_mem_normalizer_cenHull (S : ZDSetup X Z M) (c : Conf16 Z M) :
    c.t ∈ normalizer ((cenHull Z (c.t * c.u) : Subgroup X) : Set X) := by
  have ht2 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hcomm : c.t * (c.t * c.u) * c.t⁻¹ = c.t * c.u := by
    calc c.t * (c.t * c.u) * c.t⁻¹ = c.t * (c.u * c.t) * c.t⁻¹ := by rw [c.t_mul_u_comm]
      _ = c.t * c.u := by group
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := Sec172.mem_cenHull_conj S.invariant c.t hy
    rwa [hcomm] at this
  · intro hy
    have := Sec172.mem_cenHull_conj S.invariant c.t⁻¹ hy
    have e1 : c.t⁻¹ * (c.t * y * c.t⁻¹) * c.t⁻¹⁻¹ = y := by group
    have e2 : c.t⁻¹ * (c.t * c.u) * c.t⁻¹⁻¹ = c.t * c.u := by
      rw [inv_inv, hti]
      calc c.t * (c.t * c.u) * c.t = c.t * (c.u * c.t) * c.t := by rw [c.t_mul_u_comm]
        _ = c.t * c.u * (c.t * c.t) := by group
        _ = c.t * c.u := by rw [ht2, mul_one]
    rwa [e1, e2] at this

theorem ZDSetup.exists_D0_not_comm
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M)
    (h161 : Lemma161Stmt Z M) (c : Conf16 Z M) (hzu : c.u * c.z = c.z * c.u) :
    ∃ a ∈ c.D ⊓ cenHull Z (c.t * c.u), a * c.t ≠ c.t * a := by
  obtain ⟨x, hxK, hxtu, hxt⟩ := S.exists_not_comm_of_tu h121 h161 c hzu
  have ht2 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨hKodd, htK, -⟩ := commutator_zpowers_kGrp M S.invariant c.ht
  set a : X := x⁻¹ * (c.t * x * c.t⁻¹) with ha
  have haK : a ∈ kGrp M c.t := (kGrp M c.t).mul_mem ((kGrp M c.t).inv_mem hxK)
    ((Subgroup.mem_normalizer_iff.mp htK x).mp hxK)
  have haD : a ∈ c.D := Sec172.kGrp_le_D S.invariant c.ht haK
  have hcomm_tw : c.t * (c.t * c.u) = (c.t * c.u) * c.t := by
    calc c.t * (c.t * c.u) = c.t * (c.u * c.t) := by rw [c.t_mul_u_comm]
      _ = (c.t * c.u) * c.t := by group
  have hxw' : x⁻¹ * (c.t * c.u) = (c.t * c.u) * x⁻¹ := by
    calc x⁻¹ * (c.t * c.u) = x⁻¹ * (c.t * c.u) * x * x⁻¹ := by group
      _ = x⁻¹ * (x * (c.t * c.u)) * x⁻¹ := by rw [hxtu]; group
      _ = (c.t * c.u) * x⁻¹ := by group
  have hxZ : x⁻¹ * c.t * x ∈ Z := S.invariant.2 c.t c.ht x
  have hxc : x⁻¹ * c.t * x ∈ centralizer ({c.t * c.u} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x⁻¹ * c.t * x * (c.t * c.u) = x⁻¹ * c.t * (x * (c.t * c.u)) := by group
      _ = x⁻¹ * c.t * ((c.t * c.u) * x) := by rw [hxtu]
      _ = x⁻¹ * (c.t * (c.t * c.u)) * x := by group
      _ = x⁻¹ * ((c.t * c.u) * c.t) * x := by rw [hcomm_tw]
      _ = (x⁻¹ * (c.t * c.u)) * c.t * x := by group
      _ = ((c.t * c.u) * x⁻¹) * c.t * x := by rw [hxw']
      _ = (c.t * c.u) * (x⁻¹ * c.t * x) := by group
  have h1 : x⁻¹ * c.t * x ∈ cenHull Z (c.t * c.u) := Subgroup.subset_closure ⟨hxZ, hxc⟩
  have h2 : c.t⁻¹ ∈ cenHull Z (c.t * c.u) := (cenHull Z (c.t * c.u)).inv_mem (Sec172.t_mem_cenHull c)
  have haC : a ∈ cenHull Z (c.t * c.u) := by
    have e : a = (x⁻¹ * c.t * x) * c.t⁻¹ := by rw [ha]; group
    rw [e]
    exact (cenHull Z (c.t * c.u)).mul_mem h1 h2
  refine ⟨a, Subgroup.mem_inf.mpr ⟨haD, haC⟩, ?_⟩
  intro hat
  have haodd : Odd (orderOf a) := Odd.of_dvd_nat hKodd (Subgroup.orderOf_dvd_natCard _ haK)
  have hta : c.t * a * c.t⁻¹ = a := by
    rw [← hat]
    group
  have hx' : c.t * x * c.t⁻¹ = x * a := by rw [ha]; group
  have hx2 : x = x * (a * a) := by
    calc x = c.t * (c.t * x * c.t⁻¹) * c.t⁻¹ := by
          calc x = 1 * x * 1 := by group
            _ = (c.t * c.t) * x * (c.t⁻¹ * c.t⁻¹) := by rw [ht2, hti, ht2]
            _ = _ := by group
      _ = c.t * (x * a) * c.t⁻¹ := by rw [hx']
      _ = (c.t * x * c.t⁻¹) * (c.t * a * c.t⁻¹) := by group
      _ = (x * a) * a := by rw [hx', hta]
      _ = x * (a * a) := by group
  have haa : a * a = 1 := by
    have := hx2
    calc a * a = x⁻¹ * (x * (a * a)) := by group
      _ = x⁻¹ * x := by rw [← hx2]
      _ = 1 := by group
  have ha1 : a = 1 := Sec172.eq_one_of_sq haa haodd
  apply hxt
  have : c.t * x * c.t⁻¹ = x := by rw [hx', ha1, mul_one]
  calc x * c.t = (c.t * x * c.t⁻¹) * c.t := by rw [this]
    _ = c.t * x := by group

theorem ZDSetup.lemma172_cdef
    (S : ZDSetup X Z M) (h121 : Thm121Stmt Z M) (h161 : Lemma161Stmt Z M)
    (h164 : Lemma164Stmt Z M) (h166 : Cor166Stmt Z M) (h167 : Lemma167Stmt Z M)
    (c : Conf16 Z M) {n i e : ℕ} (hB : BenderSub Z M (cenHull Z c.u) n i e) :
    ((c.D ⊓ centralizer ({c.t, c.u} : Set X)).relIndex
        (c.D ⊓ centralizer ({c.t * c.u} : Set X)) ≠ 1) ∧
    Odd (Nat.card ↥(c.D ⊓ cenHull Z (c.t * c.u))) ∧
    omegaFix M ((c.D ⊓ cenHull Z (c.t * c.u) : Subgroup X) : Set X) = {M, conjugate M c.t} ∧
    ∀ Y : Subgroup X, Y ≤ c.D ⊓ cenHull Z (c.t * c.u) → ⁅zpowers c.t, Y⁆ ≠ ⊥ →
      ⁅zpowers c.t, Y⁆ ≤ Y →
      omegaFix M (Y : Set X) = {M, conjugate M c.t} ∧
        normalizer (Y : Set X) ⊓ cenHull Z (c.t * c.u) ≤
          (c.D ⊓ cenHull Z (c.t * c.u)) ⊔ zpowers c.t := by
  have hzu := Sec172.u_mul_z_comm h164 c hB
  have ht2 := S.conf_t_sq c
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  have hodd := S.odd_card_D0 h166 c hB
  have htD : c.t ∈ normalizer (c.D : Set X) := mem_normalizer_inf_conjugate ht2
  have htD0 : c.t ∈ normalizer ((c.D ⊓ cenHull Z (c.t * c.u) : Subgroup X) : Set X) :=
    mem_normalizer_inf_of_mem_normalizer htD (Sec172.t_mem_normalizer_cenHull S c)
  obtain ⟨a, haD0, hat⟩ := S.exists_D0_not_comm h121 h161 c hzu
  have hnc : ¬ ∀ y ∈ c.D ⊓ cenHull Z (c.t * c.u), y * c.t = c.t * y := fun h => hat (h a haD0)
  have he := S.omegaFix_eq_pair h167 c inf_le_left hodd htD0 hnc
  refine ⟨?_, hodd, he, ?_⟩
  ·
    intro h
    have hle := Subgroup.relIndex_eq_one.mp h
    obtain ⟨x, hxK, hxtu, hxt⟩ := S.exists_not_comm_of_tu h121 h161 c hzu
    have hxD : x ∈ c.D := Sec172.kGrp_le_D S.invariant c.ht hxK
    have hx1 : x ∈ c.D ⊓ centralizer ({c.t * c.u} : Set X) :=
      Subgroup.mem_inf.mpr ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr hxtu⟩
    have hxc := (Subgroup.mem_inf.mp (hle hx1)).2
    exact hxt (Subgroup.mem_centralizer_iff.mp hxc c.t (by simp)).symm
  ·
    intro Y hY hYt hYY
    have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hY)
    have htY : c.t ∈ normalizer (Y : Set X) :=
      (Subgroup.zpowers_le.mp (Subgroup.le_normalizer_iff_commutator_le_right.mpr hYY))
    have hYnc : ¬ ∀ y ∈ Y, y * c.t = c.t * y := by
      intro h
      apply hYt
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
        Subgroup.mem_centralizer_iff]
      exact h
    have hΩ := S.omegaFix_eq_pair h167 c (hY.trans inf_le_left) hYodd htY hYnc
    refine ⟨hΩ, ?_⟩
    intro g hg
    obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.mp hg
    rcases S.normalizer_pair_le c hΩ hgN with hgD | hgD
    · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgD, hgC⟩)
    · have hgC' : g * c.t⁻¹ ∈ cenHull Z (c.t * c.u) :=
        (cenHull Z (c.t * c.u)).mul_mem hgC ((cenHull Z (c.t * c.u)).inv_mem
          (Sec172.t_mem_cenHull c))
      have hg' : g = (g * c.t⁻¹) * c.t := by group
      rw [hg']
      exact (c.D ⊓ cenHull Z (c.t * c.u) ⊔ zpowers c.t).mul_mem
        (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgD, hgC'⟩))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c.t))

end CFSG.GH74.Uniqueness
