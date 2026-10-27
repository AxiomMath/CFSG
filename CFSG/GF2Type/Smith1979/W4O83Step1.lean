module

public import CFSG.GF2Type.Smith1979.W4O83Conj
public import CFSG.Goldschmidt.Steps.AxB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
open CFSG.RankThree.Literature.FSmith (zmod2_cases)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

noncomputable abbrev perp (W : Submodule (ZMod 2) S.Qt) : Submodule (ZMod 2) S.Qt :=
  LinearMap.BilinForm.orthogonal S.q.polarBilin W

theorem mem_perp_iff {W : Submodule (ZMod 2) S.Qt} {m : S.Qt} :
    m ∈ perp W ↔ ∀ n ∈ W, polar S.q n m = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [LinearMap.BilinForm.IsOrtho, polarBilin_apply_apply]

theorem perp_perp (W : Submodule (ZMod 2) S.Qt) : perp (perp W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl W

theorem rho_apply_eq_th (C : Omega83Config S) {θ₀ : S.M} {i : Fin 4} (h : S.ρ θ₀ = C.theta i)
    (v : S.Qt) : (S.ρ θ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = C.th i v := by
  rw [h]
  rfl

theorem Omega83Config.step_one (C : Omega83Config S) {t' : G} (ht'Q : t' ∈ S.QG)
    (ht'2 : t' ^ 2 = 1) {k : Fin 4} (hk : C.th k (S.cl t') = S.cl t') {U' : Subgroup G}
    (hU2 : IsPGroup 2 U')
    (hnorm : ∀ h ∈ centralizer ({t'} : Set G), ∀ u ∈ U', h * u * h⁻¹ ∈ U')
    (hchar : ∀ y ∈ centralizer ({t'} : Set G), (∀ u ∈ U', y * u = u * y) → y ∈ U') :
    ∀ y ∈ S.QG, S.cl y ∈ C.plane k → y ∈ U' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ₁, hθρ, hθ3⟩ := C.exists_lift k
  have hθOb : S.ρ θ₁ ∈ Ob S := hθρ ▸ C.theta_mem_Ob k
  have hθt : (θ₁ : G) * t' = t' * θ₁ :=
    mul_comm_of_apply_eq θ₁.2 hθ3 ht'Q (by rw [rho_apply_eq_th C hθρ]; exact hk)
  have hθC : (θ₁ : G) ∈ centralizer ({t'} : Set G) := mem_centralizer_singleton_iff.mpr hθt
  have hnormU : ∀ h ∈ centralizer ({t'} : Set G), h ∈ normalizer (U' : Set G) := by
    intro h hh
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hnorm h hh u hu, fun hu => ?_⟩
    have := hnorm h⁻¹ (inv_mem hh) _ hu
    simpa [mul_assoc] using this
  set W : Submodule (ZMod 2) S.Qt := C.plane k ⊔ Submodule.span (ZMod 2) {S.cl t'} with hW
  set B : Subgroup G := S.clPre (perp W) with hB
  have hBQ : B ≤ S.QG := S.clPre_le_QG _
  have hB2 : IsPGroup 2 B := S.isPGroup_QG.to_le hBQ
  have hBmem : ∀ x, x ∈ B ↔ x ∈ S.QG ∧ ∀ n ∈ W, polar S.q n (S.cl x) = 0 := by
    intro x
    rw [hB, S.mem_clPre, mem_perp_iff]
  have hzB : S.z ∈ B := S.z_mem_clPre _
  have hBt : ∀ x ∈ B, x * t' = t' * x := by
    intro x hx
    obtain ⟨hxQ, hxW⟩ := (hBmem x).mp hx
    have h1 := hxW (S.cl t') (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    exact ((S.polar_cl_eq_zero_iff ht'Q hxQ).mp h1).symm
  have hBθ : ∀ x ∈ B, (θ₁ : G) * x = x * θ₁ := by
    intro x hx
    obtain ⟨hxQ, hxW⟩ := (hBmem x).mp hx
    have h1 : C.prL k (S.cl x) = 0 := C.prL_eq_zero_of_polar fun w hw => by
      rw [polar_comm]
      exact hxW w (Submodule.mem_sup_left hw)
    have h2 := (C.th_eq_iff k _).mpr h1
    exact mul_comm_of_apply_eq θ₁.2 hθ3 hxQ (by rw [rho_apply_eq_th C hθρ]; exact h2)
  have hdual : ∀ c ∈ S.QG, (∀ x ∈ B, c * x = x * c) → S.cl c ∈ W := by
    intro c hc hcomm
    have h1 : S.cl c ∈ perp (perp W) := by
      rw [mem_perp_iff]
      intro n hn
      obtain ⟨x, hxQ, rfl⟩ := S.exists_cl n
      have hxB : x ∈ B := (hBmem x).mpr ⟨hxQ, mem_perp_iff.mp hn⟩
      rw [S.polar_cl_eq_zero_iff hxQ hc]
      exact (hcomm x hxB).symm
    rwa [perp_perp] at h1
  set T : Subgroup G := U' ⊓ centralizer (B : Set G) with hT
  have hTM : ∀ x ∈ T, x ∈ S.M := fun x hx =>
    S.mem_M_iff.mpr ((mem_centralizer_iff.mp hx.2) S.z hzB).symm
  have hθU : ∀ u ∈ U', (θ₁ : G) * u * (θ₁ : G)⁻¹ ∈ U' := fun u hu => hnorm θ₁ hθC u hu
  have hTθ : ∀ x ∈ T, (θ₁ : G) * x * (θ₁ : G)⁻¹ ∈ T := by
    intro x hx
    refine ⟨hθU x hx.1, mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hbθ := hBθ b hb
    have hbx := (mem_centralizer_iff.mp hx.2) b hb
    have hconj : (θ₁ : G) * b * (θ₁ : G)⁻¹ = b := by
      rw [hbθ]
      group
    calc b * ((θ₁ : G) * x * (θ₁ : G)⁻¹)
        = ((θ₁ : G) * b * (θ₁ : G)⁻¹) * ((θ₁ : G) * x * (θ₁ : G)⁻¹) := by rw [hconj]
      _ = (θ₁ : G) * (b * x) * (θ₁ : G)⁻¹ := by group
      _ = (θ₁ : G) * (x * b) * (θ₁ : G)⁻¹ := by rw [hbx]
      _ = ((θ₁ : G) * x * (θ₁ : G)⁻¹) * ((θ₁ : G) * b * (θ₁ : G)⁻¹) := by group
      _ = ((θ₁ : G) * x * (θ₁ : G)⁻¹) * b := by rw [hconj]
  have hcomm_Q : ∀ x ∈ T, (θ₁ : G) * x * (θ₁ : G)⁻¹ * x⁻¹ ∈ S.QG := by
    intro x hx
    have hxM := hTM x hx
    have hcU : (θ₁ : G) * x * (θ₁ : G)⁻¹ * x⁻¹ ∈ U' := mul_mem (hθU x hx.1) (inv_mem hx.1)
    obtain ⟨n, hn⟩ := hU2 ⟨_, hcU⟩
    have hn' : ((θ₁ : G) * x * (θ₁ : G)⁻¹ * x⁻¹) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    exact commutator_mem_Q (x₀ := ⟨x, hxM⟩) hθOb hn'
  have hθodd : Odd (orderOf (θ₁ : G)) :=
    Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hθ3)
  by_cases hA : ∀ x ∈ T, (θ₁ : G) * x = x * θ₁
  ·
    exfalso
    have hcop : Nat.Coprime (Nat.card (zpowers (θ₁ : G))) 2 := by
      rw [Nat.card_zpowers]
      exact Nat.coprime_two_right.mpr hθodd
    have hRN : zpowers (θ₁ : G) ≤ normalizer (U' : Set G) := by
      intro r hr
      refine hnormU r ?_
      exact (zpowers_le.mpr hθC) hr
    have hBN : B ≤ normalizer (U' : Set G) := fun x hx =>
      hnormU x (mem_centralizer_singleton_iff.mpr (hBt x hx))
    have hRB : ⁅zpowers (θ₁ : G), B⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr ?_)
      exact mem_centralizer_iff.mpr fun b hb => (hBθ b hb).symm
    have hfix : U' ⊓ centralizer (B : Set G) ≤ centralizer (zpowers (θ₁ : G) : Set G) := by
      intro x hx
      rw [mem_centralizer_iff]
      rintro r ⟨m, rfl⟩
      exact ((Commute.zpow_left (hA x hx) m)).eq
    have hall := CFSG.Goldschmidt.N10 G (p := 2) U' (zpowers (θ₁ : G)) B hU2 hcop hB2 hRN hBN
      hRB hfix
    have hθU' : (θ₁ : G) ∈ U' := by
      refine hchar θ₁ hθC fun u hu => ?_
      exact (mem_centralizer_iff.mp (hall hu)) (θ₁ : G) (mem_zpowers _)
    obtain ⟨n, hn⟩ := hU2 ⟨(θ₁ : G), hθU'⟩
    have hθ1 : (θ₁ : G) = 1 :=
      eq_one_of_odd_orderOf hθodd (n := n) (by simpa using congrArg Subtype.val hn)
    have hρ1 : C.theta k = 1 := by
      rw [← hθρ, show θ₁ = 1 from Subtype.ext hθ1, map_one]
    have hbot : C.plane k ≠ ⊥ := by
      intro h
      have := C.finrank_plane k
      rw [h, finrank_bot] at this
      omega
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    apply hp0
    refine C.eq_zero_of_th_eq hp ?_
    change (C.theta k : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p
    rw [hρ1]
    rfl
  ·
    push Not at hA
    obtain ⟨x, hxT, hxne⟩ := hA
    set c : G := (θ₁ : G) * x * (θ₁ : G)⁻¹ * x⁻¹ with hc
    have hcT : c ∈ T := mul_mem (hTθ x hxT) (inv_mem hxT)
    have hcQ : c ∈ S.QG := hcomm_Q x hxT
    have hcW : S.cl c ∈ W :=
      hdual c hcQ fun b hb => ((mem_centralizer_iff.mp hcT.2) b hb).symm
    have hspan : S.cl c ∉ Submodule.span (ZMod 2) {S.cl t'} := by
      intro hs
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
      have hfixc : C.th k (S.cl c) = S.cl c := by
        rw [← ha, map_smul, hk]
      have hθc : (θ₁ : G) * c = c * θ₁ :=
        mul_comm_of_apply_eq θ₁.2 hθ3 hcQ (by rw [rho_apply_eq_th C hθρ]; exact hfixc)
      have hc2 : c ^ 2 = 1 := by
        have hq : S.q (S.cl c) = 0 := by
          rw [← ha]
          rcases zmod2_cases a with rfl | rfl
          · simp
          · rw [one_smul]
            exact (S.q_cl_eq_zero_iff ht'Q).mpr ht'2
        exact (S.q_cl_eq_zero_iff hcQ).mp hq
      have h1 : (θ₁ : G) * x * (θ₁ : G)⁻¹ = c * x := by
        rw [hc]
        group
      have hθcθ : (θ₁ : G) * c * (θ₁ : G)⁻¹ = c := by
        rw [hθc]
        group
      have h2 : (θ₁ : G) * ((θ₁ : G) * x * (θ₁ : G)⁻¹) * (θ₁ : G)⁻¹ = x := by
        rw [h1]
        calc (θ₁ : G) * (c * x) * (θ₁ : G)⁻¹
            = ((θ₁ : G) * c * (θ₁ : G)⁻¹) * ((θ₁ : G) * x * (θ₁ : G)⁻¹) := by group
          _ = c * (c * x) := by rw [hθcθ, h1]
          _ = x := by rw [← mul_assoc, ← pow_two, hc2, one_mul]
      have h3 : (θ₁ : G) ^ 2 * x = x * (θ₁ : G) ^ 2 := by
        calc (θ₁ : G) ^ 2 * x
            = ((θ₁ : G) * ((θ₁ : G) * x * (θ₁ : G)⁻¹) * (θ₁ : G)⁻¹) * (θ₁ : G) ^ 2 := by
              rw [pow_two]
              group
          _ = x * (θ₁ : G) ^ 2 := by rw [h2]
      have hxx : (θ₁ : G) = ((θ₁ : G) ^ 2) ^ 2 := by
        calc (θ₁ : G) = (θ₁ : G) * (θ₁ : G) ^ 3 := by rw [hθ3, mul_one]
          _ = ((θ₁ : G) ^ 2) ^ 2 := by group
      apply hxne
      have hcm : Commute ((θ₁ : G) ^ 2) x := h3
      rw [hxx]
      exact (hcm.pow_left 2).eq
    obtain ⟨p, hp, s, hs, hps⟩ := Submodule.mem_sup.mp hcW
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [zero_add] at hps
      exact hspan (hps ▸ hs)
    have hths : C.th k s = s := by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hs
      rw [← ha, map_smul, hk]
    have hinv : ∀ w ∈ S.clSub U', C.th k w ∈ S.clSub U' := by
      intro w hw
      obtain ⟨y, hyU, hyQ, rfl⟩ := S.mem_clSub_iff.mp hw
      have h1 := S.ρ_cl θ₁ hyQ
      rw [rho_apply_eq_th C hθρ] at h1
      rw [h1]
      exact S.cl_mem_clSub (hθU y hyU) (S.conj_mem_QG θ₁.2 hyQ)
    have hclc : S.cl c ∈ S.clSub U' := S.cl_mem_clSub hcT.1 hcQ
    have hp₂ : C.th k p + p ∈ S.clSub U' := by
      have h1 := add_mem (hinv _ hclc) hclc
      rw [← hps, map_add, hths] at h1
      have h2 : C.th k p + s + (p + s) = C.th k p + p := by
        calc C.th k p + s + (p + s) = C.th k p + p + (s + s) := by abel
          _ = C.th k p + p := by rw [CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2),
              add_zero]
      rwa [h2] at h1
    have hp₂mem : C.th k p + p ∈ C.plane k := add_mem (C.th_mem_plane hp) hp
    have hp₂0 : C.th k p + p ≠ 0 := by
      intro h
      apply hp0
      refine C.eq_zero_of_th_eq hp ?_
      rw [eq_neg_of_add_eq_zero_left h, CFSG.RankThree.OrthogonalInvolutions.neg_vec_eq (ZMod 2)]
    have hplane : ∀ w ∈ C.plane k, w ∈ S.clSub U' := by
      intro w hw
      rcases C.mem_orbit hp₂mem hp₂0 hw with h | h | h | h
      · rw [h]
        exact zero_mem _
      · rw [h]
        exact hp₂
      · rw [h]
        exact hinv _ hp₂
      · rw [h]
        exact hinv _ (hinv _ hp₂)
    obtain ⟨y, hyU, hyQ, hyc⟩ := S.mem_clSub_iff.mp hp₂
    have hy2 : y ^ 2 ≠ 1 := by
      rw [← S.q_cl_eq_one_iff hyQ, hyc]
      exact C.q_eq_one k _ hp₂mem hp₂0
    have hzU : S.z ∈ U' := by
      rw [← (S.sq_eq_one_or_z hyQ).resolve_left hy2]
      exact pow_mem hyU 2
    intro y₀ hy₀Q hy₀
    obtain ⟨y₁, hy₁U, hy₁Q, hy₁⟩ := S.mem_clSub_iff.mp (hplane _ hy₀)
    rcases (S.cl_eq_cl_iff hy₁Q hy₀Q).mp hy₁ with h | h
    · rw [h]
      exact hy₁U
    · rw [h]
      exact mul_mem hy₁U hzU

end CFSG.GF2Type.Smith1979.W4O83
