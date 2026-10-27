module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21B03

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped Pointwise

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem eq_one_or_eq_of_mem_zpowers_of_sq {c : G} (hc2 : c * c = 1) {a : G}
    (ha : a ∈ Subgroup.zpowers c) : a = 1 ∨ a = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, zpow_two, hc2, one_zpow]
  · right
    rw [hm, zpow_add, zpow_mul, zpow_two, hc2, one_zpow, one_mul, zpow_one]

theorem exists_mem_oddCoreOf_centralizer_of_comm {Y : Subgroup G} {c : G} (hc2 : c * c = 1)
    (hcY : conjSub c Y = Y) (h : ∀ y ∈ Y, c * y * c⁻¹ * y⁻¹ ∈ oddCoreOf Y) {y : G} (hy : y ∈ Y) :
    ∃ n ∈ oddCoreOf Y, n⁻¹ * y ∈ Subgroup.centralizer ({c} : Set G) := by
  classical
  set O := oddCoreOf Y with hO
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hcO : ∀ o ∈ O, c * o * c⁻¹ ∈ O := by
    intro o ho
    have h1 : oddCoreOf (conjSub c Y) = conjSub c (oddCoreOf Y) := AscE184Sect.oddCoreOf_conjSub c Y
    rw [hcY] at h1
    have : c * o * c⁻¹ ∈ conjSub c (oddCoreOf Y) := conj_mem_conjSub ho
    rwa [← h1] at this
  by_cases hc1 : c = 1
  · refine ⟨1, O.one_mem, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hc1]
    simp
  have hcN : c ∈ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hcO x, fun hx => ?_⟩
    have h1 := hcO _ hx
    have e : c * (c * x * c⁻¹) * c⁻¹ = x := by
      rw [hcinv]
      calc c * (c * x * c) * c = (c * c) * x * (c * c) := by group
        _ = x := by rw [hc2]; group
    rwa [e] at h1
  set A : Subgroup G := Subgroup.zpowers c with hA
  have hAN : A ≤ Subgroup.normalizer (O : Set G) := Subgroup.zpowers_le.mpr hcN
  set P : Subgroup G := O ⊔ A with hP
  have hPset : ((O ⊔ A : Subgroup G) : Set G) = (O : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O A hAN
  have hPmem : ∀ x ∈ P, ∃ o ∈ O, x = o ∨ x = o * c := by
    intro x hx
    have hx' : x ∈ ((O ⊔ A : Subgroup G) : Set G) := hx
    rw [hPset] at hx'
    obtain ⟨o, ho, a, ha, hoa⟩ := hx'
    have hoa' : o * a = x := hoa
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hc2 ha with h1 | h1
    · exact ⟨o, ho, Or.inl (by rw [← hoa', h1, mul_one])⟩
    · exact ⟨o, ho, Or.inr (by rw [← hoa', h1])⟩
  have hodd : ∀ x ∈ O, IsPGroup 2 (Subgroup.zpowers x) → x = 1 := fun x hx hx2 =>
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard Y) hx hx2
  have hmax : ∀ t₀ : G, t₀ ∈ P → t₀ * t₀ = 1 → (∃ o ∈ O, t₀ = o * c) →
      IsSylow2In (Subgroup.zpowers t₀) P := by
    intro t₀ ht₀P ht₀2 ⟨o₁, ho₁, ht₀⟩
    refine ⟨Subgroup.zpowers_le.mpr ht₀P,
      Q3T8.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ht₀2, ?_⟩
    intro V' hV'P hV'2 hV'
    apply le_antisymm ?_ hV'
    intro v hv
    obtain ⟨o, ho, hvo | hvo⟩ := hPmem v (hV'P hv)
    · have h1 : v = 1 := by
        rw [hvo] at hv ⊢
        exact hodd o ho (hV'2.to_le (Subgroup.zpowers_le.mpr hv))
      rw [h1]
      exact Subgroup.one_mem _
    · have ht₀V' : t₀ ∈ V' := hV' (Subgroup.mem_zpowers t₀)
      have h3 : v * t₀⁻¹ ∈ V' := V'.mul_mem hv (V'.inv_mem ht₀V')
      have e : v * t₀⁻¹ = o * o₁⁻¹ := by rw [hvo, ht₀]; group
      have hoo : o * o₁⁻¹ ∈ O := O.mul_mem ho (O.inv_mem ho₁)
      rw [e] at h3
      have h4 : o * o₁⁻¹ = 1 := hodd _ hoo (hV'2.to_le (Subgroup.zpowers_le.mpr h3))
      have h5 : v = t₀ := by
        have h6 : v * t₀⁻¹ = 1 := by rw [e, h4]
        exact mul_inv_eq_one.mp h6
      rw [h5]
      exact Subgroup.mem_zpowers t₀
  have ho₀ : y * c * y⁻¹ * c⁻¹ ∈ O := by
    have h1 := h y hy
    have e : y * c * y⁻¹ * c⁻¹ = (c * y * c⁻¹ * y⁻¹)⁻¹ := by group
    rw [e]
    exact O.inv_mem h1
  set d : G := y * c * y⁻¹ with hd
  have hd2 : d * d = 1 := by
    calc d * d = y * (c * c) * y⁻¹ := by rw [hd]; group
      _ = 1 := by rw [hc2]; group
  have hdc : d = (y * c * y⁻¹ * c⁻¹) * c := by rw [hd]; group
  have hcP : c ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hdP : d ∈ P := by
    rw [hdc]
    exact P.mul_mem (Subgroup.mem_sup_left ho₀) hcP
  have hS1 : IsSylow2In (Subgroup.zpowers c) P := hmax c hcP hc2 ⟨1, O.one_mem, by rw [one_mul]⟩
  have hS2 : IsSylow2In (Subgroup.zpowers d) P := hmax d hdP hd2 ⟨_, ho₀, hdc⟩
  obtain ⟨x, hxP, hx⟩ := CFSG.ClassicalInvolution.Asc77.Thompson.exists_conj_of_isSylow2In hS1 hS2
  have hxc : x * c * x⁻¹ ∈ Subgroup.zpowers d := by
    rw [← hx]
    exact conj_mem_conjSub (Subgroup.mem_zpowers c)
  have hxc' : x * c * x⁻¹ = d := by
    rcases eq_one_or_eq_of_mem_zpowers_of_sq hd2 hxc with h1 | h1
    · exfalso
      apply hc1
      have h2 : c = x⁻¹ * (x * c * x⁻¹) * x := by group
      rw [h2, h1]
      group
    · exact h1
  have key : ∀ n ∈ O, n * c * n⁻¹ = d → ∃ n ∈ O, n⁻¹ * y ∈ Subgroup.centralizer ({c} : Set G) := by
    intro n hn hnd
    refine ⟨n, hn, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (n⁻¹ * y) * c = n⁻¹ * (y * c * y⁻¹) * y := by group
      _ = n⁻¹ * (n * c * n⁻¹) * y := by rw [hnd, hd]
      _ = c * (n⁻¹ * y) := by group
  obtain ⟨n, hn, hxn | hxn⟩ := hPmem x hxP
  · apply key n hn
    rw [← hxc', hxn]
  · apply key n hn
    rw [← hxc', hxn]
    group

end Coprime

section Layer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}


theorem Hyp21.c₀_facts' (h : Hyp21 Ω K K' z u J t W) {c₀ : G} (hc₀ : c₀ = z ∨ c₀ = t * z) :
    c₀ * c₀ = 1 ∧ c₀ * u = u * c₀ := by
  rcases hc₀ with rfl | rfl
  · exact ⟨h.std.hz.sq, h.u_comm_z.symm⟩
  · refine ⟨h.tz_sq, ?_⟩
    calc (t * z) * u = t * (z * u) := by group
      _ = t * (u * z) := by rw [h.u_comm_z.symm]
      _ = (t * u) * z := by group
      _ = (u * t) * z := by rw [h.htu]
      _ = u * (t * z) := by group

theorem Hyp21.exactLayer_u_le_normalizer_alpha_of_trivial (h : Hyp21 Ω K K' z u J t W)
    (hC3 : C21_3) {c₀ : G} (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ ExactLayer.exactLayer Ω u,
      c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u)) :
    ExactLayer.exactLayer Ω u ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  obtain ⟨hc₀2, hc₀u⟩ := h.c₀_facts' hc₀
  have hα : alphaOf (Subgroup.closure ({u, c₀} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    rcases hc₀ with rfl | rfl
    · rfl
    · exact h.alpha_u_tz hC3
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (ExactLayer.exactLayer Ω u) = ExactLayer.exactLayer Ω u :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hcC
  have hOY : oddCoreOf (ExactLayer.exactLayer Ω u) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) :=
    (oddCoreOf_exactLayer_le hΩ.conjInvariant u).trans
      (oddCoreOf_centralizer_le_normalizer_alphaOf h.std.hz.sq h.hu1 h.u_comm_z)
  intro y hy
  obtain ⟨n, hn, hnc⟩ := exists_mem_oddCoreOf_centralizer_of_comm hc₀2 hcY htriv hy
  have hnY : n ∈ ExactLayer.exactLayer Ω u := oddCoreOf_le_self _ hn
  have hnyY : n⁻¹ * y ∈ ExactLayer.exactLayer Ω u :=
    (ExactLayer.exactLayer Ω u).mul_mem ((ExactLayer.exactLayer Ω u).inv_mem hnY) hy
  have hnyC : n⁻¹ * y ∈ Subgroup.centralizer ({u} : Set G) :=
    ExactLayer.exactLayer_le_centralizer Ω u hnyY
  have hle : Subgroup.closure ({u, c₀} : Set G) ≤ Subgroup.centralizer ({n⁻¹ * y} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hnyC).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hnc).symm
  have hxA : n⁻¹ * y ∈ Subgroup.centralizer
      ((Subgroup.closure ({u, c₀} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  have hxN := T7B.centralizer_le_normalizer_alphaOf _ hxA
  rw [hα] at hxN
  have e : y = n * (n⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hOY hn) hxN

theorem Hyp21.exactLayer_u_le_centralizer_of_trivial (h : Hyp21 Ω K K' z u J t W)
    (hC3 : C21_3) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {c₀ : G}
    (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ ExactLayer.exactLayer Ω u,
      c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u)) :
    ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({c₀} : Set G) := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  obtain ⟨hc₀2, hc₀u⟩ := h.c₀_facts' hc₀
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (ExactLayer.exactLayer Ω u) = ExactLayer.exactLayer Ω u :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hcC
  intro y hy
  obtain ⟨n, hn, hnc⟩ := exists_mem_oddCoreOf_centralizer_of_comm hc₀2 hcY htriv hy
  have hnO : n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G)) :=
    oddCoreOf_exactLayer_le hΩ.conjInvariant u hn
  have hnC : n ∈ Subgroup.centralizer ({c₀} : Set G) := by
    rcases hc₀ with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.oddCore_centralizer_u_comm hα hnO)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (h.oddCore_centralizer_u_comm_tz hC3 hα hnO)
  have e : y = n * (n⁻¹ * y) := by group
  rw [e]
  exact (Subgroup.centralizer ({c₀} : Set G)).mul_mem hnC hnc

theorem Hyp21.exactLayer_u_le_sigmaGen_of_le_centralizer_z (h : Hyp21 Ω K K' z u J t W)
    (hY : ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({z} : Set G)) :
    ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hK : K ∈ Ω := h.std.stand.mem
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one h.hu2
  rw [ExactLayer.exactLayer_eq_iSup]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨M, hMt, rfl⟩ := hL
  obtain ⟨hMΩ, R, hR, hRu⟩ := (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mp hMt
  have hRK : R ≤ ExactLayer.exactCore u M := by
    rw [ExactLayer.exactCore_def]
    exact le_inf hR.1 hRu
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hR
  have hRz : R ≤ Subgroup.centralizer ({z} : Set G) :=
    hRK.trans ((ExactLayer.exactCore_le_exactLayer hMt).trans hY)
  have hMd : M ∈ dComp Ω K := by
    by_cases hMK : M = K
    · rw [hMK]
      exact Relation.ReflTransGen.refl
    · have h8 := hΩ.eight_le_of_mem_RSet hRset
      have hRN : R ≤ Subgroup.normalizer (K : Set G) :=
        hΩ.le_normalizer_of_le_centralizer hK hMΩ (Ne.symm hMK) h.std.hz hR.1 hR.2.1 (by omega)
          hRz
      exact T7A.mem_dComp_of_mem_omegaNbr ⟨hMΩ, hMK, R, hRset, hR.1, hRN⟩
  exact (ExactLayer.exactCore_le_left u M).trans (le_iSup₂_of_le M hMd le_rfl)

theorem Hyp21.exactLayer_u_le_sigmaGen_of_le_centralizer_tz (h : Hyp21 Ω K K' z u J t W)
    (hC3 : C21_3) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (heq : dComp Ω K = dstarComp Ω K)
    (hY : ExactLayer.exactLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G)) :
    ExactLayer.exactLayer Ω u ≤ sigmaGen Ω K := by
  have hΩ : Q3T7M.HM Ω := h.std.stand.modU
  have hMF : DStarConnectedTwinGen := dstarConnectedTwinGen_of
  have h3s : ∀ n, Q3T8.Generic.CITBelowU n → T3.Thm3SectBelow n :=
    fun _ hh => Q3T7E.thm3SectBelow3_of_ih hh
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one h.hu2
  have hcA' : IsPGroup 2 (Subgroup.zpowers (t * z)) :=
    ExactLayer.isPGroup_zpowers_of_sq_eq_one h.tz_sq
  rw [ExactLayer.exactLayer_eq_iSup]
  refine iSup₂_le fun L hL => ?_
  obtain ⟨M, hMt, rfl⟩ := hL
  obtain ⟨hMΩ, R, hR, hRu⟩ := (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mp hMt
  have hRK : R ≤ ExactLayer.exactCore u M := by
    rw [ExactLayer.exactCore_def]
    exact le_inf hR.1 hRu
  have hRtz : R ≤ Subgroup.centralizer ({t * z} : Set G) :=
    hRK.trans ((ExactLayer.exactCore_le_exactLayer hMt).trans hY)
  have hMtz : M ∈ ExactLayer.tqMembers Ω (t * z) :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA').mpr ⟨hMΩ, R, hR, hRtz⟩
  have hMd : M ∈ dComp Ω K := by
    rw [heq]
    exact tqMembers_subset_dstarComp_gen h hMF h3s hC3 hα M hMtz
  exact (ExactLayer.exactCore_le_left u M).trans (le_iSup₂_of_le M hMd le_rfl)

@[expose] def C21_14_ZT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 Ω K K' z u J t W →
      ¬ SectionConnected Ω u →
        (∀ y ∈ ExactLayer.exactLayer Ω u,
          z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u)) ∨
          (∀ y ∈ ExactLayer.exactLayer Ω u,
            (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω u))

theorem c21_14_Y_disc_of_zt (hC3 : C21_3) (hZT : C21_14_ZT) : C21_14_Y_disc := by
  intro G _ _ _ Ω K K' z u J t W h hdisc
  rcases hZT G Ω K K' z u J t W h hdisc with htriv | htriv
  · refine ⟨h.exactLayer_u_le_normalizer_alpha_of_trivial hC3 (c₀ := z) (Or.inl rfl) htriv,
      fun hα => Or.inl ?_⟩
    exact h.exactLayer_u_le_sigmaGen_of_le_centralizer_z
      (h.exactLayer_u_le_centralizer_of_trivial hC3 hα (c₀ := z) (Or.inl rfl) htriv)
  · refine ⟨h.exactLayer_u_le_normalizer_alpha_of_trivial hC3 (c₀ := t * z) (Or.inr rfl) htriv,
      fun hα => Or.inr ?_⟩
    exact h.exactLayer_u_le_centralizer_of_trivial hC3 hα (c₀ := t * z) (Or.inr rfl) htriv

theorem c21_14_alt_rest_of (hC3 : C21_3) (hY : C21_14_Y_disc) (hN : C21_NormCent) :
    C21_14_alt_rest := by
  intro G _ _ _ Ω K K' z u J t W h hα hnot
  have h3s : ∀ n, Q3T8.Generic.CITBelowU n → T3.Thm3SectBelow n :=
    fun _ hh => Q3T7E.thm3SectBelow3_of_ih hh
  by_cases hconn : SectionConnected Ω u
  · have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hnot ⟨heq, hconn⟩
    exact Or.inr (h.centralizer_u_le_centralizer_tz_of_conn hC3 hα hne
      (hN G Ω K K' z u J t W h hα (h.not_rLayer_le_sigmaGen hne)) hconn)
  · rcases (hY G Ω K K' z u J t W h hconn).2 hα with hSig | hD
    · exact Or.inl hSig
    · by_cases heq : dComp Ω K = dstarComp Ω K
      · exact Or.inl (h.exactLayer_u_le_sigmaGen_of_le_centralizer_tz hC3 hα heq hD)
      · exact Or.inr (h.centralizer_u_le_centralizer_tz_of_disc h3s heq
          (hN G Ω K K' z u J t W h hα (h.not_rLayer_le_sigmaGen heq)) hconn hD)

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
