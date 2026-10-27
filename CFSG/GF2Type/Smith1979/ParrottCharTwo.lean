module

public import CFSG.GF2Type.Smith1979.CharTwoSpec
public import CFSG.GF2Type.Smith1979.CharTwoLemmas
public import CFSG.GF2Type.Smith1979.CharTwoLift
public import CFSG.GF2Type.Smith1979.IdxFourHSyl
public import CFSG.GF2Type.Smith1979.W4O83Local
public import CFSG.LargeExtraspecial.S4Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_Qa_of_commute (S : Setting G) {g m x : G}
    (hm : m * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * m) (hx : x ∈ S.Qa g) : m * x * m⁻¹ ∈ S.Qa g :=
  (S.conjBy g).conj_mem_QG (mem_centralizer_singleton_iff.mpr hm) hx

theorem hasLbar_cl_conj_z (S : Setting G) (hw : S.width = 6) {g : G} (H : S4.Hyp4 S g)
    (C : S4.Cons311 S g) : HasLbar S (S.cl (g * S.z * g⁻¹)) := by
  have haQ := H.conj_mem
  have hne := H.conj_ne
  have ha1 : g * S.z * g⁻¹ ≠ 1 := S4.conj_z_ne_one S g
  refine ⟨S.Lbar g, fun s hs => ⟨S.Lbar_le_Mbar g hs, ?_⟩, fun s hs p hp => ?_, ?_, ?_⟩
  · have hmem : S.cl (g * S.z * g⁻¹) ∈ S4.fixSub S (S.Lbar g) := by
      rw [H.fixSub_eq]
      exact Submodule.mem_span_singleton_self _
    exact hmem s hs
  · obtain ⟨m, hma, rfl⟩ := exists_centralizer_lift S haQ ha1 hne hs
    obtain ⟨y, hyL, rfl⟩ := S.mem_Lbar_iff.mp hp
    refine S.mem_Lbar_iff.mpr ⟨m * y * m⁻¹, ⟨?_, (m * y * m⁻¹).2⟩, by
      rw [map_mul, map_mul, map_inv]⟩
    exact conj_mem_Qa_of_commute S hma hyL.1
  · haveI := S.isElementaryAbelian_Lbar haQ
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  · rw [C.card_Lbar, hw]

theorem false_of_charTwoFacts [IsSimpleGroup G] (hchar : IsCharTwoType G)
    (hTI : WeaklyClosedTITransitive.{0}) (S : Setting G) (hw : S.width = 6)
    (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S) {g : G} (H : S4.Hyp4 S g)
    (C : S4.Cons311 S g) (hF : CharTwoFacts S) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ : g * S.z * g⁻¹ ∈ S.QG := H.conj_mem
  have hne : g * S.z * g⁻¹ ≠ S.z := H.conj_ne
  have ha1 : g * S.z * g⁻¹ ≠ 1 := S4.conj_z_ne_one S g
  set a : G := g * S.z * g⁻¹ with ha
  set T : Setting G := S.conjBy g with hT
  have hTz : T.z = a := rfl
  have haQa : a ∈ S.Qa g := S.conj_z_mem_Qa g
  have ha0 : S.cl a ≠ 0 := S.cl_conj_z_ne_zero haQ hne
  have haq : S.q (S.cl a) = 0 := S.q_cl_conj_z haQ
  have hLa : HasLbar S (S.cl a) := hasLbar_cl_conj_z S hw H C
  set V : Subgroup G := S.QG ⊓ S.Qa g with hV
  have hU6 : finrank (ZMod 2) (S.clSub V) = 6 := by
    rw [hV, S4.finrank_clSub_QG_inf_Qa haQ hne C.card_QG_inf_Qa, hw]
  have haU : S.cl a ∈ S.clSub V := S.cl_mem_clSub ⟨haQ, haQa⟩ haQ
  have hUinv : ∀ s ∈ stab S (S.cl a), ∀ u ∈ S.clSub V,
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ S.clSub V := by
    intro s hs u hu
    obtain ⟨m, hma, rfl⟩ := exists_centralizer_lift S haQ ha1 hne hs
    obtain ⟨v, hvV, hvQ, rfl⟩ := S.mem_clSub_iff.mp hu
    rw [S.ρ_cl m hvQ]
    exact S.cl_mem_clSub ⟨S.conj_mem_QG m.2 hvQ, conj_mem_Qa_of_commute S hma hvV.2⟩
      (S.conj_mem_QG m.2 hvQ)
  obtain ⟨w, hwU, hw0, hwq, hwL⟩ := hF.sub6 _ ha0 haq hLa _ hU6 haU hUinv
  obtain ⟨j, hjV, hjQ, rfl⟩ := S.mem_clSub_iff.mp hwU
  have hjQa : j ∈ S.Qa g := hjV.2
  have hj2 : j ^ 2 = 1 := (S.q_cl_eq_zero_iff hjQ).mp hwq
  have hjj : j * j = 1 := by rw [← pow_two, hj2]
  have hj1 : j ≠ 1 := by
    rintro rfl
    exact hw0 S.cl_one
  have hjz : j ≠ S.z := by
    rintro rfl
    exact hw0 S.cl_z
  have hjord : orderOf j = 2 := orderOf_eq_prime hj2 hj1
  have hja : j ≠ a := by
    rintro rfl
    exact hwL hLa
  have hL5 : ∀ h : G, h * S.z * h⁻¹ ≠ j := by
    intro h hh
    refine no_conj_z_class_mem hTI hw hirr hnoAll (W := (ZMod 2) ∙ S.cl j) ?_
      (by rw [hh]; exact hjQ) (by rw [hh]; exact hjz)
      (by rw [hh]; exact Submodule.mem_span_singleton_self _)
    intro w' hw' hw'0 P hPs hPn hP2 hPc
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    have hc : c = 1 := by
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with h0 | h0
      · exact absurd (by rw [h0, zero_smul]) hw'0
      · exact h0
    rw [hc, one_smul] at hPs hPn
    exact hwL ⟨P, hPs, hPn, hP2, hPc⟩
  have hjTQ : j ∈ T.QG := hjQa
  have hjTz : j ≠ T.z := hja
  have hjT0 : T.cl j ≠ 0 := by
    intro h
    rcases (T.cl_eq_zero_iff hjTQ).mp h with h' | h'
    · exact hj1 h'
    · exact hjTz h'
  have hjTq : T.q (T.cl j) = 0 := (T.q_cl_eq_zero_iff hjTQ).mpr hj2
  have hTa : ∀ x ∈ T.QG, x * a = a * x := fun x hx => T.z_comm (T.QG_le_M hx)
  set N : Subgroup G := T.QG ⊓ centralizer ({j} : Set G) with hN
  have hNle : N ≤ centralizer ({j} : Set G) ⊓ centralizer ({a} : Set G) := fun x hx =>
    ⟨hx.2, mem_centralizer_singleton_iff.mpr (hTa x hx.1)⟩
  have hQa2 : IsPGroup 2 T.QG := by
    refine IsPGroup.of_card (n := 1 + 2 * T.width) ?_
    rw [T.card_QG_eq_card_Q, T.card_Q_eq]
  have hN2 : IsPGroup 2 N := hQa2.to_le inf_le_left
  have hjN : j ∈ N := ⟨hjTQ, mem_centralizer_singleton_iff.mpr rfl⟩
  have haN : a ∈ N := ⟨T.z_mem_QG, mem_centralizer_singleton_iff.mpr (hTa j hjTQ).symm⟩
  obtain ⟨Sy, hSy, -⟩ := S5.exists_isSylowTwoIn_ge
    (bot_le : (⊥ : Subgroup G) ≤ centralizer ({j} : Set G) ⊓ centralizer ({a} : Set G))
    IsPGroup.of_bot
  have hNSy : N ≤ Sy := le_of_normal_isSylowTwoIn hSy hNle hN2 fun h hh n hn => by
    have h1 : h ∈ centralizer ({j} : Set G) := (mem_inf.mp hh).1
    have h2 : n ∈ centralizer ({j} : Set G) := (mem_inf.mp hn).2
    exact ⟨T.conj_mem_QG (mem_inf.mp hh).2 (mem_inf.mp hn).1,
      (centralizer ({j} : Set G)).mul_mem ((centralizer ({j} : Set G)).mul_mem h1 h2)
        ((centralizer ({j} : Set G)).inv_mem h1)⟩
  have hfour : ∀ y : G, (∀ x ∈ N, y * x = x * y) →
      y = 1 ∨ y = a ∨ y = j ∨ y = j * a := by
    intro y hy
    have hyM : y ∈ T.M := mem_centralizer_singleton_iff.mpr (hy a haN)
    have hρ : T.ρ ⟨y, hyM⟩ = 1 := by
      refine eq_one_of_fix_perp T hjT0 hjTq fun v hv => ?_
      obtain ⟨x, hxQ, rfl⟩ := T.exists_cl v
      have hxj : x * j = j * x := (T.polar_cl_eq_zero_iff hxQ hjTQ).mp hv
      rw [T.ρ_cl ⟨y, hyM⟩ hxQ]
      congr 1
      have := hy x ⟨hxQ, mem_centralizer_singleton_iff.mpr hxj⟩
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [this]
        _ = x := by group
    have hyQ : y ∈ T.QG := (T.ρ_eq_one_iff ⟨y, hyM⟩).mp hρ
    have hperp : T.cl y ∈ LinearMap.BilinForm.orthogonal T.q.polarBilin
        (LinearMap.BilinForm.orthogonal T.q.polarBilin ((ZMod 2) ∙ T.cl j)) := by
      intro v hv
      show T.q.polarBilin v (T.cl y) = 0
      obtain ⟨x, hxQ, rfl⟩ := T.exists_cl v
      have hjx : T.q.polarBilin (T.cl j) (T.cl x) = 0 := hv _ (Submodule.mem_span_singleton_self _)
      rw [QuadraticMap.polarBilin_apply_apply] at hjx
      have hxj' : j * x = x * j := (T.polar_cl_eq_zero_iff hjTQ hxQ).mp hjx
      rw [QuadraticMap.polarBilin_apply_apply, T.polar_cl_eq_zero_iff hxQ hyQ]
      exact (hy x ⟨hxQ, mem_centralizer_singleton_iff.mpr hxj'.symm⟩).symm
    rw [LinearMap.BilinForm.orthogonal_orthogonal T.q_nondegenerate T.polarBilin_isRefl] at hperp
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hperp
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with h0 | h0
    · rw [h0, zero_smul] at hc
      rcases (T.cl_eq_zero_iff hyQ).mp hc.symm with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [h0, one_smul] at hc
      rcases (T.cl_eq_cl_iff hjTQ hyQ).mp hc with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨u, huQ, hu⟩ := T.exists_conj_eq_mul_z hjTQ hj1 hjTz
  have hcomm : a ∈ ⁅Sy, Sy⁆ := by
    obtain ⟨x₁, hx₁, x₂, hx₂, h12⟩ : ∃ x₁ ∈ N, ∃ x₂ ∈ N, x₁ * x₂ ≠ x₂ * x₁ := by
      by_contra hcon
      push Not at hcon
      set W := LinearMap.BilinForm.orthogonal T.q.polarBilin ((ZMod 2) ∙ T.cl j) with hW
      have hWW : W ≤ LinearMap.BilinForm.orthogonal T.q.polarBilin W := by
        intro v hv v' hv'
        show T.q.polarBilin v' v = 0
        obtain ⟨x, hxQ, rfl⟩ := T.exists_cl v
        obtain ⟨x', hx'Q, rfl⟩ := T.exists_cl v'
        have hj' : ∀ y ∈ T.QG, T.cl y ∈ W → y ∈ N := by
          intro y hyQ hyW
          have hjy : T.q.polarBilin (T.cl j) (T.cl y) = 0 :=
            hyW _ (Submodule.mem_span_singleton_self _)
          rw [QuadraticMap.polarBilin_apply_apply] at hjy
          exact ⟨hyQ, mem_centralizer_singleton_iff.mpr
            ((T.polar_cl_eq_zero_iff hjTQ hyQ).mp hjy).symm⟩
        rw [QuadraticMap.polarBilin_apply_apply, T.polar_cl_eq_zero_iff hx'Q hxQ]
        exact hcon x' (hj' x' hx'Q hv') x (hj' x hxQ hv)
      have h1 := LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate W
      have h2 := LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate ((ZMod 2) ∙ T.cl j)
      have h3 := Submodule.finrank_mono hWW
      have hdim : finrank (ZMod 2) T.Qt = 12 := by
        rw [T.finrank_Qt_eq_two_mul_width, S.width_conjBy, hw]
      rw [finrank_span_singleton hjT0, hdim, ← hW] at h2
      rw [hdim] at h1
      omega
    rcases T.commutator_eq_one_or_z (hx₁.1) (hx₂.1) with h | h
    · exfalso
      apply h12
      calc x₁ * x₂ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * (x₂ * x₁) := by group
        _ = x₂ * x₁ := by rw [h, one_mul]
    · rw [hTz] at h
      rw [← h]
      exact commutator_mem_commutator (hNSy hx₁) (hNSy hx₂)
  have hSyl : S5.IsSylowTwoIn Sy (centralizer ({j} : Set G)) := by
    refine isSylowTwoIn_centralizer_of_unique hSy ?_ ?_ hcomm
    · intro h hhC _
      rcases hfour (h * a * h⁻¹) (fun x hx => (mem_centralizer_iff.mp hhC x (hNSy hx)).symm)
        with h1 | h1 | h1 | h1
      · exfalso
        apply ha1
        calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
          _ = 1 := by rw [h1]; group
      · exact h1
      · exfalso
        apply hL5 (h * g)
        calc h * g * S.z * (h * g)⁻¹ = h * a * h⁻¹ := by rw [ha]; group
          _ = j := h1
      · exfalso
        apply hL5 (u⁻¹ * h * g)
        calc u⁻¹ * h * g * S.z * (u⁻¹ * h * g)⁻¹ = u⁻¹ * (h * a * h⁻¹) * u := by
              rw [ha]; group
          _ = u⁻¹ * (j * a) * u := by rw [h1]
          _ = j := by
              rw [← hTz, ← hu]
              group
    · rw [mem_centralizer_iff]
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hSy.le hx).2
  set P : Subgroup G := pCoreOf 2 (centralizer ({j} : Set G)) with hP
  have hP2 : IsPGroup 2 P := by
    rw [hP, pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hPn : ∀ c ∈ centralizer ({j} : Set G), ∀ r ∈ P, c * r * c⁻¹ ∈ P := by
    intro c hc r hr
    rw [hP, pCoreOf] at hr ⊢
    obtain ⟨r', hr', rfl⟩ := hr
    exact ⟨⟨c, hc⟩ * r' * ⟨c, hc⟩⁻¹, CFSG.pCore_normal.conj_mem r' hr' _, rfl⟩
  have hPle : P ≤ centralizer ({j} : Set G) := by
    rw [hP, pCoreOf]
    exact map_subtype_le _
  have hPSy : P ≤ Sy := le_of_normal_isSylowTwoIn hSyl hPle hP2 hPn
  have haC : a ∈ centralizer ({j} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hTa j hjTQ).symm
  have hcen : ∀ c ∈ centralizer ({j} : Set G), ∀ r ∈ P, (c * a * c⁻¹) * r = r * (c * a * c⁻¹) := by
    intro c hc r hr
    have hr' : c⁻¹ * r * c ∈ P := by
      have := hPn c⁻¹ (inv_mem hc) r hr
      simpa using this
    have hca : a * (c⁻¹ * r * c) = (c⁻¹ * r * c) * a :=
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (hSy.le (hPSy hr'))).2).symm
    calc c * a * c⁻¹ * r = c * (a * (c⁻¹ * r * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * r * c) * a) * c⁻¹ := by rw [hca]
      _ = r * (c * a * c⁻¹) := by group
  have hinP : ∀ c ∈ centralizer ({j} : Set G), c * a * c⁻¹ ∈ P := by
    intro c hc
    refine W4O83.centralizer_pCoreOf_le hchar hjord _ ?_ (hcen c hc)
    exact mul_mem (mul_mem hc haC) (inv_mem hc)
  set A : Set S.Qt := {v | ∃ s ∈ stab S (S.cl j), (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = v}
    with hA
  have hAlift : ∀ v ∈ A, ∃ m : S.M, (m : G) * j = j * (m : G) ∧
      v = S.cl ((m : G) * a * (m : G)⁻¹) := by
    rintro v ⟨s, hs, rfl⟩
    obtain ⟨m, hmj, rfl⟩ := exists_centralizer_lift S hjQ hj1 hjz hs
    exact ⟨m, hmj, S.ρ_cl m haQ⟩
  have h0 : (0 : S.Qt) ∉ A := by
    rintro ⟨s, -, hs⟩
    exact ha0 ((s : S.Qt ≃ₗ[ZMod 2] S.Qt).map_eq_zero_iff.mp hs)
  have hpol : ∀ x ∈ A, ∀ y ∈ A, polar S.q x y = 0 := by
    intro x hx y hy
    obtain ⟨m₁, hm₁, rfl⟩ := hAlift x hx
    obtain ⟨m₂, hm₂, rfl⟩ := hAlift y hy
    have hc₁ : (m₁ : G) ∈ centralizer ({j} : Set G) := mem_centralizer_singleton_iff.mpr hm₁
    have hc₂ : (m₂ : G) ∈ centralizer ({j} : Set G) := mem_centralizer_singleton_iff.mpr hm₂
    rw [S.polar_cl_eq_zero_iff (S.conj_mem_QG m₁.2 haQ) (S.conj_mem_QG m₂.2 haQ)]
    exact hcen _ hc₁ _ (hinP _ hc₂)
  have hle := ncard_le_of_pairwise_polar S h0 hpol
  have hge := hF.orbit _ hw0 hwq hwL _ ha0 haq hLa
    ((S.polar_cl_eq_zero_iff haQ hjQ).mpr (hTa j hjTQ).symm)
  rw [hw] at hle
  have hle' : A.ncard ≤ 63 := by simpa using hle
  have hge' : 64 ≤ A.ncard := hge
  omega

end CFSG.GF2Type.Smith1979.IdxFour
