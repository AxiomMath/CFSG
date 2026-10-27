module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_Final
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.BadCaseLocalCalc
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.BadCaseLocalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.BadCaseLocalSylow

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Local

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {D : A6Datum N}

theorem Notation25.xx_mem_S (N : Notation25 hs) : N.x * N.x ∈ N.S := by
  simpa [sq] using N.x_sq

theorem FinalCtx.f2_data {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    N.x * e * N.x⁻¹ ∈ CFSG.conjugate N.SK N.x ∧ (N.x * e * N.x⁻¹) * (N.x * e * N.x⁻¹) = 1 ∧
      D.Φ (N.x * e * N.x⁻¹) ≠ 1 ∧ D.Φ (N.x * e * N.x⁻¹) ≠ zb ∧ InE4 (D.Φ (N.x * e * N.x⁻¹)) := by
  have hx2S : N.x * N.x ∈ N.S := N.xx_mem_S
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have heH : e ∈ N.H := N.S_le_H (N.SK_le_S heSK)
  have hxxH : N.x * N.x ∈ N.H := N.S_le_H hx2S
  have hb : N.x * N.x * e * (N.x * N.x)⁻¹ ∈ N.SK :=
    Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_SK C.hKH) (N.x * N.x) hx2S e heSK
  have hbr : IsRefl (D.Φ (N.x * N.x * e * (N.x * N.x)⁻¹)) := by
    rw [D.Φ_conj hxxH heH]
    exact isRefl_conj hE.hrefl (D.S_mem _ hx2S)
  have h := C.refl_image hb hbr
  have eq : N.x⁻¹ * (N.x * N.x * e * (N.x * N.x)⁻¹) * N.x = N.x * e * N.x⁻¹ := by group
  rwa [eq] at h

theorem FinalCtx.tau_ne {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G)) :
    D.Φ (N.x⁻¹ * e * N.x) ≠ D.Φ (N.x * e * N.x⁻¹) := by
  intro hΦ
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  obtain ⟨hf₁mem, -, -, -, -⟩ := C.refl_image heSK hE.hrefl
  obtain ⟨hf₂mem, -, -, -, -⟩ := C.f2_data hE
  have hf₁S := C.SKx_le_S hf₁mem
  have hf₂S := C.SKx_le_S hf₂mem
  have hSC : (N.x⁻¹ * e * N.x)⁻¹ * (N.x * e * N.x⁻¹) ∈ N.SC :=
    D.inv_mul_mem_SC C.hK0 hf₁S hf₂S hΦ
  have hin : (N.x⁻¹ * e * N.x)⁻¹ * (N.x * e * N.x⁻¹) ∈ CFSG.conjugate N.SK N.x :=
    (CFSG.conjugate N.SK N.x).mul_mem ((CFSG.conjugate N.SK N.x).inv_mem hf₁mem) hf₂mem
  have hw := C.SKx_inf_SC heSK hE.hrefl _ hin hSC
  have hx2S : N.x * N.x ∈ N.S := N.xx_mem_S
  have hb : N.x * N.x * e * (N.x * N.x)⁻¹ ∈ E := by
    rcases hw with hw | hw
    · have h1 : N.x * e * N.x⁻¹ = N.x⁻¹ * e * N.x := by
        calc N.x * e * N.x⁻¹
            = (N.x⁻¹ * e * N.x) * ((N.x⁻¹ * e * N.x)⁻¹ * (N.x * e * N.x⁻¹)) := by group
          _ = N.x⁻¹ * e * N.x := by rw [hw, mul_one]
      have : N.x * N.x * e * (N.x * N.x)⁻¹ = e := by
        calc N.x * N.x * e * (N.x * N.x)⁻¹ = N.x * (N.x * e * N.x⁻¹) * N.x⁻¹ := by group
          _ = N.x * (N.x⁻¹ * e * N.x) * N.x⁻¹ := by rw [h1]
          _ = e := by group
      rw [this]
      exact hE.heE
    · have h1 : N.x * e * N.x⁻¹ = (N.x⁻¹ * e * N.x) * t := by
        calc N.x * e * N.x⁻¹
            = (N.x⁻¹ * e * N.x) * ((N.x⁻¹ * e * N.x)⁻¹ * (N.x * e * N.x⁻¹)) := by group
          _ = (N.x⁻¹ * e * N.x) * t := by rw [hw]
      have : N.x * N.x * e * (N.x * N.x)⁻¹ = e * zK := by
        calc N.x * N.x * e * (N.x * N.x)⁻¹ = N.x * (N.x * e * N.x⁻¹) * N.x⁻¹ := by group
          _ = N.x * ((N.x⁻¹ * e * N.x) * t) * N.x⁻¹ := by rw [h1]
          _ = e * (N.x * t * N.x⁻¹) := by group
          _ = e * zK := by rw [C.x_t]
      rw [this]
      exact E.mul_mem hE.heE hE.hzKE
  apply hbad
  apply mem_normalizer_of_conj_mem
  intro y hy
  rcases hE.hEel y hy with hy1 | hy1 | hy1 | hy1
  · rw [hy1]
    simp
  · rw [hy1]
    have hc := C.zK_comm hx2S
    have : N.x * N.x * zK * (N.x * N.x)⁻¹ = zK := by
      calc N.x * N.x * zK * (N.x * N.x)⁻¹ = zK * (N.x * N.x) * (N.x * N.x)⁻¹ := by rw [hc]
        _ = zK := by group
    rw [this]
    exact hE.hzKE
  · rw [hy1]
    exact hb
  · rw [hy1]
    have hc := C.zK_comm hx2S
    have e1 : N.x * N.x * (e * zK) * (N.x * N.x)⁻¹ =
        (N.x * N.x * e * (N.x * N.x)⁻¹) * (N.x * N.x * zK * (N.x * N.x)⁻¹) := by group
    have e2 : N.x * N.x * zK * (N.x * N.x)⁻¹ = zK := by
      calc N.x * N.x * zK * (N.x * N.x)⁻¹ = zK * (N.x * N.x) * (N.x * N.x)⁻¹ := by rw [hc]
        _ = zK := by group
    rw [e1, e2]
    exact E.mul_mem hb hE.hzKE

theorem FinalCtx.tau_mul {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G)) :
    D.Φ (N.x⁻¹ * e * N.x) * D.Φ (N.x * e * N.x⁻¹) = zb := by
  obtain ⟨-, -, h1ne, h1z, h1E⟩ := C.refl_image (hE.hEK hE.heE) hE.hrefl
  obtain ⟨-, -, h2ne, h2z, h2E⟩ := C.f2_data hE
  have hne := C.tau_ne hE hbad
  have hτ₁d : D.Φ (N.x⁻¹ * e * N.x) ∉ A6Models.psl29 := fun hmem => by
    rcases E4_inter_psl29 h1E hmem with h | h
    · exact h1ne h
    · exact h1z h
  have hsq : D.Φ (N.x⁻¹ * e * N.x) * D.Φ (N.x⁻¹ * e * N.x) = 1 :=
    P0_sq_of_centralizes_D h1E.1 h1E.2
  rcases E4_shape h1E hτ₁d h2E with h | h | h | h
  · exact absurd h h2ne
  · exact absurd h h2z
  · exact absurd h.symm hne
  · rw [h, ← mul_assoc, hsq, one_mul]


theorem FinalCtx.kappa {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    {u f : G} (huK : u ∈ N.K) (hf : f ∈ CFSG.conjugate N.SK N.x) (hfE4 : InE4 (D.Φ f))
    {ψ : P10} (huΦ : D.Φ u = ψ)
    (hc : D.Φ f * ψ * D.Φ f * ψ⁻¹ = 1 ∨ D.Φ f * ψ * D.Φ f * ψ⁻¹ = D.Φ e) :
    (f⁻¹ * u * f * u⁻¹ = 1 ∨ f⁻¹ * u * f * u⁻¹ = e) ∧
      (f⁻¹ * u * f * u⁻¹ = e ↔ D.Φ f * ψ * D.Φ f * ψ⁻¹ = D.Φ e) := by
  have hfS := C.SKx_le_S hf
  have hfH := N.S_le_H hfS
  have huH := N.K_le_H huK
  have heK : e ∈ N.K := (hE.hEK hE.heE).2
  have hκK : f⁻¹ * u * f * u⁻¹ ∈ N.K := by
    have h1 : f⁻¹ * u * f ∈ N.K := by
      have := Subgroup.le_normalizer_iff.mp (N.S_le_normalizer_K C.hKH) f⁻¹ (N.S.inv_mem hfS) u huK
      simpa using this
    exact N.K.mul_mem h1 (N.K.inv_mem huK)
  have hsq : D.Φ f * D.Φ f = 1 := P0_sq_of_centralizes_D hfE4.1 hfE4.2
  have hΦκ : D.Φ (f⁻¹ * u * f * u⁻¹) = D.Φ f * ψ * D.Φ f * ψ⁻¹ := by
    rw [D.mul _ (N.H.mul_mem (N.H.mul_mem (N.H.inv_mem hfH) huH) hfH) _ (N.H.inv_mem huH),
      D.mul _ (N.H.mul_mem (N.H.inv_mem hfH) huH) _ hfH, D.mul _ (N.H.inv_mem hfH) _ huH,
      D.Φ_inv hfH, D.Φ_inv huH, huΦ, inv_eq_of_mul_eq_one_right hsq]
  refine ⟨?_, ?_⟩
  · rcases hc with hc | hc
    · left
      apply D.inj_K C.hsimple hκK N.K.one_mem
      rw [hΦκ, hc, D.Φ_one]
    · right
      apply D.inj_K C.hsimple hκK heK
      rw [hΦκ, hc]
  · constructor
    · intro h
      rw [← hΦκ, h]
    · intro h
      apply D.inj_K C.hsimple hκK heK
      rw [hΦκ, h]

theorem FinalCtx.exists_u {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G)) :
    ∃ u ∈ N.K, u * zK * u⁻¹ = zK * e ∧ u * e * u⁻¹ = e ∧ u * t * u⁻¹ = t ∧
      ∃ κ₁ κ₂ : G, (κ₁ = 1 ∨ κ₁ = e) ∧ (κ₂ = 1 ∨ κ₂ = e) ∧
        u * (N.x⁻¹ * e * N.x) * u⁻¹ = (N.x⁻¹ * e * N.x) * κ₁ ∧
        u * (N.x * e * N.x⁻¹) * u⁻¹ = (N.x * e * N.x⁻¹) * κ₂ ∧ (κ₁ = e ↔ ¬ κ₂ = e) := by
  obtain ⟨ψ, hψ, h1, h2, h3, h4⟩ := exists_star hE.hrefl
  obtain ⟨u, huK, huΦ⟩ := D.K_surj ψ hψ
  have huH := N.K_le_H huK
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have heK : e ∈ N.K := heSK.2
  have hzKK : zK ∈ N.K := (C.hf.zK_mem_SK C.hK0).2
  have heH : e ∈ N.H := N.K_le_H heK
  have hzKH : zK ∈ N.H := N.K_le_H hzKK
  have hU1 : u * zK * u⁻¹ = zK * e := by
    apply D.inj_K C.hsimple (N.K.mul_mem (N.K.mul_mem huK hzKK) (N.K.inv_mem huK))
      (N.K.mul_mem hzKK heK)
    rw [D.Φ_conj huH hzKH, D.mul zK hzKH e heH, huΦ, C.hΦzK]
    exact h1
  have hU2 : u * e * u⁻¹ = e := by
    apply D.inj_K C.hsimple (N.K.mul_mem (N.K.mul_mem huK heK) (N.K.inv_mem huK)) heK
    rw [D.Φ_conj huH heH, huΦ]
    exact h2
  have hU3 : u * t * u⁻¹ = t := by
    have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer C.hf.t_mem) u (C.hK0 ▸ huK)
    rw [this]
    group
  obtain ⟨hf₁mem, -, h1ne, h1z, h1E⟩ := C.refl_image heSK hE.hrefl
  obtain ⟨hf₂mem, -, h2ne, h2z, h2E⟩ := C.f2_data hE
  have hk₁ := C.kappa hE huK hf₁mem h1E huΦ (h3 _ h1E)
  have hk₂ := C.kappa hE huK hf₂mem h2E huΦ (h3 _ h2E)
  have hmul := C.tau_mul hE hbad
  refine ⟨u, huK, hU1, hU2, hU3, (N.x⁻¹ * e * N.x)⁻¹ * u * (N.x⁻¹ * e * N.x) * u⁻¹,
    (N.x * e * N.x⁻¹)⁻¹ * u * (N.x * e * N.x⁻¹) * u⁻¹, hk₁.1, hk₂.1, ?_, ?_, ?_⟩
  · group
  · group
  · exact (hk₁.2.trans (h4 _ _ h1E h2E hmul)).trans (not_congr hk₂.2.symm)


omit [Finite G] in
theorem IsFourSubgroup.comm_of_mem {E : Subgroup G} (hE4 : IsFourSubgroup E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have : IsMulCommutative ↥E := hE4.1.1
  exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem FinalCtx.A_eq_closure {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e) :
    E ⊔ CFSG.conjugate E N.x = Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) := by
  have hzKA : zK ∈ Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have heA : e ∈ Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have htA : t ∈ Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hfA : N.x⁻¹ * e * N.x ∈ Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hsL : E ≤ E ⊔ CFSG.conjugate E N.x := le_sup_left
  have hsR : CFSG.conjugate E N.x ≤ E ⊔ CFSG.conjugate E N.x := le_sup_right
  apply le_antisymm
  · apply sup_le
    · intro y hy
      rcases hE.hEel y hy with h | h | h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact hzKA
      · rw [h]; exact heA
      · rw [h]; exact Subgroup.mul_mem _ heA hzKA
    · intro y hy
      have hy' : N.x * y * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hy
      have hyeq : y = N.x⁻¹ * (N.x * y * N.x⁻¹) * N.x := by group
      rcases hE.hEel _ hy' with h | h | h | h
      · rw [hyeq, h]
        simp only [mul_one, inv_mul_cancel]
        exact Subgroup.one_mem _
      · rw [hyeq, h, C.zK_x]; exact htA
      · rw [hyeq, h]; exact hfA
      · have : y = (N.x⁻¹ * e * N.x) * t := by
          rw [hyeq, h]
          calc N.x⁻¹ * (e * zK) * N.x = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * zK * N.x) := by group
            _ = (N.x⁻¹ * e * N.x) * t := by rw [C.zK_x]
        rw [this]
        exact Subgroup.mul_mem _ hfA htA
  · refine (Subgroup.closure_le _).2 ?_
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h
    · rw [h]; exact hsL hE.hzKE
    · rw [h]; exact hsL hE.heE
    · rw [h]; exact hsR (C.mem_conj_E hE).2
    · rw [h]; exact hsR (C.mem_conj_E hE).1

theorem FinalCtx.sq_SK (C : FinalCtx N t zK D) {d : G} (hd : d ∈ N.SK) :
    d * d = 1 ∨ d * d = zK := by
  have hdK : d ∈ N.K := hd.2
  have hdH : d ∈ N.H := N.K_le_H hdK
  have hzKK : zK ∈ N.K := (C.hf.zK_mem_SK C.hK0).2
  have h := sq_D (D.S_mem d (N.SK_le_S hd)) (D.K_mem d hdK)
  rw [← D.mul d hdH d hdH] at h
  rcases h with h | h
  · left
    exact D.inj_K C.hsimple (N.K.mul_mem hdK hdK) N.K.one_mem (by rw [h, D.Φ_one])
  · right
    exact D.inj_K C.hsimple (N.K.mul_mem hdK hdK) hzKK (by rw [h, C.hΦzK])

theorem FinalCtx.sq_R {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    (hE4 : IsFourSubgroup E)
    (hQ : N.S ⊓ Subgroup.normalizer (E : Set G) = N.SK ⊔ CFSG.conjugate N.SK N.x) :
    ∀ r ∈ N.S ⊓ Subgroup.normalizer (E : Set G), ∀ a ∈ E ⊔ CFSG.conjugate E N.x,
      r * r * a * (r * r)⁻¹ = a := by
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have heS : e ∈ N.S := N.SK_le_S heSK
  have hzKS : zK ∈ N.S := N.SK_le_S (C.hf.zK_mem_SK C.hK0)
  obtain ⟨hf₁mem, hf₁sq, -, -, -⟩ := C.refl_image heSK hE.hrefl
  have hf₁S := C.SKx_le_S hf₁mem
  have hzKe : zK * e = e * zK := hE4.comm_of_mem hE.hzKE hE.heE
  have hzKt : zK * t = t * zK := C.t_comm hzKS
  have het : e * t = t * e := C.t_comm heS
  have hzKf : zK * (N.x⁻¹ * e * N.x) = (N.x⁻¹ * e * N.x) * zK :=
    C.comm_SK_SKx zK (C.hf.zK_mem_SK C.hK0) _ hf₁mem
  have hef : e * (N.x⁻¹ * e * N.x) = (N.x⁻¹ * e * N.x) * e := C.comm_SK_SKx e heSK _ hf₁mem
  have htf : t * (N.x⁻¹ * e * N.x) = (N.x⁻¹ * e * N.x) * t := by
    calc t * (N.x⁻¹ * e * N.x) = N.x⁻¹ * (zK * e) * N.x := by
          conv_lhs => rw [← C.zK_x]
          group
      _ = N.x⁻¹ * (e * zK) * N.x := by rw [hzKe]
      _ = (N.x⁻¹ * e * N.x) * t := by
          conv_rhs => rw [← C.zK_x]
          group
  have hcentA : ∀ c ∈ ({zK, t} : Set G), ∀ a ∈ E ⊔ CFSG.conjugate E N.x, c * a = a * c := by
    intro c hc a ha
    rw [C.A_eq_closure hE] at ha
    have hle : Subgroup.closure ({zK, e, t, N.x⁻¹ * e * N.x} : Set G) ≤
        Subgroup.centralizer ({c} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hc
      rcases hc with hc | hc <;> rcases hy with hy | hy | hy | hy <;> rw [hc, hy] <;>
        first
        | rfl | exact hzKe.symm | exact hzKe | exact hzKt.symm | exact hzKt | exact het.symm
        | exact het | exact hzKf.symm | exact hzKf | exact hef.symm | exact hef | exact htf.symm
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
    exact this.symm
  intro r hr a ha
  have hr' : r ∈ N.SK ⊔ CFSG.conjugate N.SK N.x := hQ ▸ hr
  obtain ⟨d, hd, d', hd', hdd⟩ := exists_mul_of_mem_sup_of_commute C.comm_SK_SKx hr'
  have hrdd : r = d * d' := by first | exact hdd.symm | exact hdd
  have hcomm : d * d' = d' * d := C.comm_SK_SKx d hd d' hd'
  have hd'0 : N.x * d' * N.x⁻¹ ∈ N.SK := BenderBranch.mem_conjugate_iff.mp hd'
  have hsq1 : d * d = 1 ∨ d * d = zK := C.sq_SK hd
  have hsq2 : d' * d' = 1 ∨ d' * d' = t := by
    have hd'eq : d' * d' = N.x⁻¹ * ((N.x * d' * N.x⁻¹) * (N.x * d' * N.x⁻¹)) * N.x := by group
    rcases C.sq_SK hd'0 with h | h
    · left
      rw [hd'eq, h]
      group
    · right
      rw [hd'eq, h, C.zK_x]
  have hrr : r * r = (d * d) * (d' * d') := by
    rw [hrdd]
    calc d * d' * (d * d') = d * (d' * d) * d' := by group
      _ = d * (d * d') * d' := by rw [hcomm]
      _ = (d * d) * (d' * d') := by group
  have hc1 : ∀ a' ∈ E ⊔ CFSG.conjugate E N.x, (d * d) * a' = a' * (d * d) := by
    intro a' ha'
    rcases hsq1 with h | h
    · rw [h]; simp
    · rw [h]; exact hcentA zK (by simp) a' ha'
  have hc2 : ∀ a' ∈ E ⊔ CFSG.conjugate E N.x, (d' * d') * a' = a' * (d' * d') := by
    intro a' ha'
    rcases hsq2 with h | h
    · rw [h]; simp
    · rw [h]; exact hcentA t (by simp) a' ha'
  have hfull : (r * r) * a = a * (r * r) := by
    rw [hrr]
    calc d * d * (d' * d') * a = (d * d) * ((d' * d') * a) := by group
      _ = (d * d) * (a * (d' * d')) := by rw [hc2 a ha]
      _ = ((d * d) * a) * (d' * d') := by group
      _ = (a * (d * d)) * (d' * d') := by rw [hc1 a ha]
      _ = a * (d * d * (d' * d')) := by group
  calc r * r * a * (r * r)⁻¹ = (a * (r * r)) * (r * r)⁻¹ := by rw [hfull]
    _ = a := by group


theorem FinalCtx.false_of_bad {E : Subgroup G} {e : G} (C : FinalCtx N t zK D) (hE : FinalE C E e)
    (hE4 : IsFourSubgroup E) (hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G))
    (hres : IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G))
      (Subgroup.normalizer ((E ⊔ CFSG.conjugate E N.x : Subgroup G) : Set G)))
    (hQ : N.S ⊓ Subgroup.normalizer (E : Set G) = N.SK ⊔ CFSG.conjugate N.SK N.x) : False := by
  obtain ⟨u, huK, hU1, hU2, hU3, κ₁, κ₂, hκ₁, hκ₂, hu₁, hu₂, hpar⟩ := C.exists_u hE hbad
  have heSK : e ∈ N.SK := hE.hEK hE.heE
  have heK : e ∈ N.K := heSK.2
  have heH : e ∈ N.H := N.K_le_H heK
  obtain ⟨hf₁mem, hf₁sq, h1ne, -, -⟩ := C.refl_image heSK hE.hrefl
  have hA := C.A_eq_closure hE
  have he2 : e * e = 1 :=
    D.inj_K C.hsimple (N.K.mul_mem heK heK) N.K.one_mem
      (by rw [D.mul e heH e heH, hE.hrefl.2.2.2.2, D.Φ_one])
  have hene : e ≠ 1 := fun h1 => hE.hrefl.2.2.1 (by rw [h1, D.Φ_one])
  have hf1ne : N.x⁻¹ * e * N.x ≠ 1 := fun h1 => h1ne (by rw [h1, D.Φ_one])
  have hef : e * (N.x⁻¹ * e * N.x) = (N.x⁻¹ * e * N.x) * e := C.comm_SK_SKx e heSK _ hf₁mem
  have hV1 : (N.x⁻¹ * u * N.x) * zK * (N.x⁻¹ * u * N.x)⁻¹ = zK := by
    calc (N.x⁻¹ * u * N.x) * zK * (N.x⁻¹ * u * N.x)⁻¹
        = N.x⁻¹ * (u * (N.x * zK * N.x⁻¹) * u⁻¹) * N.x := by group
      _ = N.x⁻¹ * (u * t * u⁻¹) * N.x := by rw [C.x_zK]
      _ = N.x⁻¹ * t * N.x := by rw [hU3]
      _ = zK := C.hxt
  have hV2 : (N.x⁻¹ * u * N.x) * e * (N.x⁻¹ * u * N.x)⁻¹ = e * (N.x⁻¹ * κ₂ * N.x) := by
    calc (N.x⁻¹ * u * N.x) * e * (N.x⁻¹ * u * N.x)⁻¹
        = N.x⁻¹ * (u * (N.x * e * N.x⁻¹) * u⁻¹) * N.x := by group
      _ = N.x⁻¹ * ((N.x * e * N.x⁻¹) * κ₂) * N.x := by rw [hu₂]
      _ = e * (N.x⁻¹ * κ₂ * N.x) := by group
  have hV3 : (N.x⁻¹ * u * N.x) * t * (N.x⁻¹ * u * N.x)⁻¹ = t * (N.x⁻¹ * e * N.x) := by
    calc (N.x⁻¹ * u * N.x) * t * (N.x⁻¹ * u * N.x)⁻¹
        = N.x⁻¹ * (u * (N.x * t * N.x⁻¹) * u⁻¹) * N.x := by group
      _ = N.x⁻¹ * (u * zK * u⁻¹) * N.x := by rw [C.x_t]
      _ = N.x⁻¹ * (zK * e) * N.x := by rw [hU1]
      _ = t * (N.x⁻¹ * e * N.x) := by
          calc N.x⁻¹ * (zK * e) * N.x = (N.x⁻¹ * zK * N.x) * (N.x⁻¹ * e * N.x) := by group
            _ = t * (N.x⁻¹ * e * N.x) := by rw [C.zK_x]
  have hV4 : (N.x⁻¹ * u * N.x) * (N.x⁻¹ * e * N.x) * (N.x⁻¹ * u * N.x)⁻¹ = N.x⁻¹ * e * N.x := by
    calc (N.x⁻¹ * u * N.x) * (N.x⁻¹ * e * N.x) * (N.x⁻¹ * u * N.x)⁻¹
        = N.x⁻¹ * (u * e * u⁻¹) * N.x := by group
      _ = N.x⁻¹ * e * N.x := by rw [hU2]
  have hcases : (κ₁ = e ∧ κ₂ = 1) ∨ (κ₁ = 1 ∧ κ₂ = e) := by
    rcases hκ₁ with h1 | h1 <;> rcases hκ₂ with h2 | h2
    · exfalso
      have := hpar.mpr (by rw [h2]; exact fun h => hene h.symm)
      rw [h1] at this
      exact hene this.symm
    · right; exact ⟨h1, h2⟩
    · left; exact ⟨h1, h2⟩
    · exfalso
      exact (hpar.mp h1) h2
  have hf2 : (N.x⁻¹ * e * N.x) * (N.x⁻¹ * e * N.x) = 1 := hf₁sq
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hu₁' : u * (N.x⁻¹ * e * N.x) * u⁻¹ = (N.x⁻¹ * e * N.x) * e := by rw [hu₁, h1]
    have hV2' : (N.x⁻¹ * u * N.x) * e * (N.x⁻¹ * u * N.x)⁻¹ = e := by
      rw [hV2, h2]
      group
    obtain ⟨hgN, hg4, hnot⟩ := calc_P1 hA he2 hf2 hef hU1 hU2 hU3 hu₁' hV1 hV2' hV3 hV4 hene
    exact hnot (sq_centralizes_of_sylow le_rfl hres (C.sq_R hE hE4 hQ) hgN hg4)
  ·
    have hu₁' : u * (N.x⁻¹ * e * N.x) * u⁻¹ = N.x⁻¹ * e * N.x := by rw [hu₁, h1, mul_one]
    have hV2' : (N.x⁻¹ * u * N.x) * e * (N.x⁻¹ * u * N.x)⁻¹ = e * (N.x⁻¹ * e * N.x) := by
      rw [hV2, h2]
    obtain ⟨hgN, hg4, hnot⟩ := calc_P2 hA he2 hf2 hU1 hU2 hU3 hu₁' hV1 hV2' hV3 hV4 hf1ne
    exact hnot (sq_centralizes_of_sylow le_rfl hres (C.sq_R hE hE4 hQ) hgN hg4)

end Local

theorem Lv2527.badCase_false {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    {hs : UnconstrainedSetting G T M} {N : Notation25 hs} {t zK : G} (h : Lv2527 N t zK)
    {E : Subgroup G} (hEK : E ≤ N.SK) (hE4 : IsFourSubgroup E)
    (hxE : N.x ^ 2 ∉ Subgroup.normalizer (E : Set G)) : False := by
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  obtain ⟨D⟩ := exists_a6Datum N hKH h.facts258 h.concl2521
  have C : FinalCtx N t zK D := FinalCtx.of_lv h D
  obtain ⟨e, hE⟩ := C.exists_finalE hEK hE4
  have hbad : N.x * N.x ∉ Subgroup.normalizer (E : Set G) := fun hmem =>
    hxE (by rw [sq]; exact hmem)
  obtain ⟨E', C'⟩ := C.badCtx h hE hE4 hbad
  have hpair := h.isUStarPair hEK hE4
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hAS : E ⊔ CFSG.conjugate E N.x ≤ N.S := by
    refine sup_le (fun y hy => N.SK_le_S (hE.hEK hy)) (fun g hg => ?_)
    have h1 : N.x * g * N.x⁻¹ ∈ E := BenderBranch.mem_conjugate_iff.mp hg
    have h2 := N.x_conj_S' (N.SK_le_S (hE.hEK h1))
    simpa [mul_assoc] using h2
  have hA2 : IsPGroup 2 ↥(E ⊔ CFSG.conjugate E N.x) := hS2.to_le hAS
  have hc := ((h.concl2512 hKH).1 _ _ hpair inf_le_left).2
  have hres := hc (E ⊔ CFSG.conjugate E N.x) hA2 (C.z_mem_A hE) (C.A_le hE) (C.norm_H_le hE)
  exact C.false_of_bad hE hE4 hbad hres.2 C'.Q_eq_R

theorem lemma25FinalBadCaseExcluded : Lemma25FinalBadCaseExcluded := by
  intro G _ _ T M hs N t zK h _ E hEK hE4 hxE
  exact h.badCase_false hEK hE4 hxE

end CFSG.QuasithinUnique
