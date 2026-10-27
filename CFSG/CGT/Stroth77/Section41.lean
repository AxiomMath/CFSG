module

public import CFSG.CGT.Stroth77.Section41Lemmas

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.card_omegaIn_one_A (F : StrothFrame G) : Nat.card (omegaIn 1 F.A) = 8 :=
  card_omegaIn_one_eq_eight F.dA.e fun i => by fin_cases i <;> decide

theorem StrothFrame.uv_not_mem_centralizer_omegaIn_A (F : StrothFrame G) :
    F.dA.uv ∉ Subgroup.centralizer ((omegaIn 1 F.A : Subgroup G) : Set G) := by
  intro h
  have hc2 : (F.dA.c : G) * F.dA.c = 1 := by
    have h1 : F.dA.c * F.dA.c = 1 := by
      apply Additive.ofMul.injective
      apply F.dA.e.injective
      rw [ofMul_mul, map_add]
      simp only [StrothWeakTypeData.c, ofMul_toMul, AddEquiv.apply_symm_apply, ofMul_one,
        map_zero]
      decide
    simpa using congrArg Subtype.val h1
  have hcV : (F.dA.c : G) ∈ omegaIn 1 F.A := mem_omegaIn_one_of_mul_self F.dA.c.2 hc2
  have hcomm := (Subgroup.mem_centralizer_iff.mp h) _ hcV
  have h1 : conjBy F.dA.uv_mem F.dA.c = F.dA.c := by
    apply Subtype.ext
    simp only [conjBy]
    rw [mul_assoc, hcomm]
    group
  have h2 := F.dA.conj_apply F.dA.uv_mem F.dA.uv_conj Torus.c
  rw [show Additive.toMul (F.dA.e.symm Torus.c) = F.dA.c from rfl, h1] at h2
  have h3 : F.dA.e (Additive.ofMul F.dA.c) = Torus.c := by
    simp [StrothWeakTypeData.c]
  rw [h3] at h2
  exact (show (Type100.action 1).φuv Torus.c ≠ (Torus.c : Torus (Type100.k 1)) by decide) h2.symm

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem omegaIn_one_eq (h : F.IsD D dD) : omegaIn 1 D = omegaIn 1 F.A := by
  refine (Subgroup.eq_of_le_of_card_ge (omegaIn_one_mono (comm_of_torus F.dA.e) h.A_le) ?_).symm
  rw [F.card_omegaIn_one_A]
  exact card_omegaIn_one_le dD.e

theorem two_le_k_one_of_eq (h : F.IsD D dD) (hτ : τ.k 0 = τ.k 1) : 2 ≤ τ.k 1 := by
  by_contra hlt
  have hk : ∀ i, τ.k i = τ.k 1 := by
    have h21 : τ.k 2 = τ.k 1 := by cases τ <;> rfl
    intro i
    fin_cases i
    exacts [hτ, rfl, h21]
  have ha := pow_two_pow_eq_one_of_torus dD.e hk (h.A_le (F.dA.a).2)
  have ha2 : ((F.dA.a : F.A) : G) ^ 2 = 1 := by
    obtain h0 | h1 : τ.k 1 = 0 ∨ τ.k 1 = 1 := by omega
    · rw [h0, pow_zero, pow_one] at ha
      rw [ha, one_pow]
    · rwa [h1, pow_one] at ha
  have hA2 : F.dA.a ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  have h0 := congrArg (fun z => F.dA.e (Additive.ofMul z)) hA2
  simp only [ofMul_pow, map_nsmul, StrothWeakTypeData.a, ofMul_toMul, AddEquiv.apply_symm_apply,
    ofMul_one, map_zero] at h0
  exact (show (2 • Torus.a : Torus (Type100.k 1)) ≠ 0 by decide) h0

theorem uv_not_mem_centralizer_omegaIn (h : F.IsD D dD) :
    dD.uv ∉ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  rw [h.omegaIn_one_eq, h.uv_eq]
  exact F.uv_not_mem_centralizer_omegaIn_A

theorem eq_sup_closure (h : F.IsD D dD)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) :
    (F.S : Subgroup G) = (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ⊔
        Subgroup.closure {dD.uv, dD.t, dD.u} := by
  have hV8 : Nat.card (omegaIn 1 D) = 8 := by rw [h.omegaIn_one_eq]; exact F.card_omegaIn_one_A
  rw [inf_eq_left.mpr hSN]
  exact (card_map_eq_eight_and_eq_sup F.S.isPGroup'
    (isElemAbelian_omegaIn_one (comm_of_torus dD.e)) hV8
    (hSN.trans (normalizer_le_normalizer_omegaIn D)) (h.uv_eq ▸ F.uv_mem_S) (h.t_eq ▸ F.t_mem_S)
    (h.u_eq ▸ F.u_mem_S) dD.uv_comm_u dD.t_u h.uv_not_mem_centralizer_omegaIn).2

theorem stroth_4_1 (h : F.IsD D dD)
    (hSN : (F.S : Subgroup G) ≤ Subgroup.normalizer (D : Set G))
    (hR : τ.m = τ.n → (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (h227 : (∀ x : G, x ∈ omegaIn 1 D → orderOf x = 2 →
      ∀ y : G, y ∈ omegaIn 1 D → orderOf y = 2 → ∃ g : G, y = g * x * g⁻¹) → τ.m = τ.n)
    (hall : ∀ x ∈ omegaIn 1 F.A, ∀ y ∈ omegaIn 1 F.A, orderOf x = 2 → orderOf y = 2 →
      IsConj x y) :
    τ.k 0 = τ.k 1 ∧
      (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u} ∧
      ∃ φ : ↥(Subgroup.normalizer (D : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
        φ.ker = (Subgroup.centralizer (D : Set G)).subgroupOf
          (Subgroup.normalizer (D : Set G)) := by
  have hallD : ∀ x ∈ omegaIn 1 D, ∀ y ∈ omegaIn 1 D, orderOf x = 2 → orderOf y = 2 →
      IsConj x y := by
    rw [h.omegaIn_one_eq]
    exact hall
  have hmn : τ.m = τ.n := h227 fun x hx hx2 y hy hy2 => by
    obtain ⟨c, hc⟩ := isConj_iff.mp (hallD x hx y hy hx2 hy2)
    exact ⟨c, hc.symm⟩
  have hk : τ.k 0 = τ.k 1 := by
    have h0 := congrFun τ.k_eq 0
    have h1 := congrFun τ.k_eq 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    rw [h0, h1, hmn]
  obtain ⟨hS, φ, hφ, hker⟩ := exists_gl32_of_stroth41 hk (h.two_le_k_one_of_eq hk) dD.e dD.uv_mem
    dD.uv_conj dD.uv_comm_t dD.uv_comm_u dD.t_u F.S (h.uv_eq ▸ F.uv_mem_S)
    (h.t_eq ▸ F.t_mem_S) (h.u_eq ▸ F.u_mem_S) h.uv_not_mem_centralizer_omegaIn hSN (hR hmn) hallD
  rw [h.uv_eq, h.t_eq, h.u_eq] at hS
  exact ⟨hk, hS, φ, hφ, hker⟩

end StrothFrame.IsD

end CFSG.CGT.Stroth77
