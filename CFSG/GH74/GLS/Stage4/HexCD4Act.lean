module

public import CFSG.GH74.GLS.Stage4.HexCD4Comm

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

structure ActData4 (D : HexData4 root F K) (A2 A4 : F → K → F) (g3 : F → K → G) : Prop where
  g3_mem : ∀ c s, g3 c s ∈ root 3
  eq : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s)

section Act4

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)

include R in
theorem exists_actData4 : ∃ (A2 A4 : F → K → F) (g3 : F → K → G), ActData4 D A2 A4 g3 := by
  classical
  have hn : ∀ c s, ⁅D.p6 c, D.p1 s⁆ * (D.p5 (D.θ c * s))⁻¹ ∈ Vsub root 2 4 := fun c s => by
    have h := root5_norm R (D.p5_mem (D.θ c * s)) (D.rel_short c s)
    have e : D.p5 (D.θ c * s) * ((D.p5 (D.θ c * s))⁻¹ * ⁅D.p6 c, D.p1 s⁆) *
        (D.p5 (D.θ c * s))⁻¹ = ⁅D.p6 c, D.p1 s⁆ * (D.p5 (D.θ c * s))⁻¹ := by group
    rwa [e] at h
  have h : ∀ c s, ∃ a ∈ root 2, ∃ u ∈ root 3, ∃ b ∈ root 4,
      ⁅D.p6 c, D.p1 s⁆ * (D.p5 (D.θ c * s))⁻¹ = a * u * b := fun c s => V24_decomp R (hn c s)
  choose a ha u hu b hb he using h
  have hA : ∀ c s, ∃ e, D.p2 e = a c s := fun c s => D.p2_surj _ (ha c s)
  have hB : ∀ c s, ∃ e, D.p4 e = b c s := fun c s => D.p4_surj _ (hb c s)
  choose A2 hA2 using hA
  choose A4 hA4 using hB
  refine ⟨A2, A4, u, ⟨hu, fun c s => ?_⟩⟩
  have := he c s
  rw [← hA2, ← hA4] at this
  unfold Nel4
  rw [← this]; group

variable {β : K → G → F} (hβ : PairData D β) {a2 a4 : K → K → F} {L : K → K → G}
  (hcd : CommData4 D a2 a4 L) {A2 A4 : F → K → F} {g3 : F → K → G} (had : ActData4 D A2 A4 g3)

include R hC hβ had in
theorem act_add_c4 (c c' : F) (s : K) :
    A2 (c + c') s = A2 c' s + A2 c s ∧ g3 (c + c') s = g3 c' s * g3 c s ∧
      A4 (c + c') s = A4 c' s + c * A2 c' s + A4 c s + β (D.θ c' * s) (g3 c s) := by
  have eq : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s) :=
    fun c s => had.eq c s
  have h1 : ⁅D.p6 (c + c'), D.p1 s⁆ =
      D.p6 c * ⁅D.p6 c', D.p1 s⁆ * (D.p6 c)⁻¹ * ⁅D.p6 c, D.p1 s⁆ := by
    rw [D.p6_add]; simp only [commutatorElement_def]; group
  rw [eq (c + c') s, eq c' s, eq c s] at h1
  have hc56 : D.p6 c * D.p5 (D.θ c' * s) * (D.p6 c)⁻¹ = D.p5 (D.θ c' * s) := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.c56 _ (D.p5_mem _) _ (D.p6_mem c)).symm
  have h1' : D.p6 c * (Nel4 D (A2 c' s) (g3 c' s) (A4 c' s) * D.p5 (D.θ c' * s)) * (D.p6 c)⁻¹ *
      (Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s)) =
      Nel4 D (A2 c' s + A2 c s) (g3 c' s * g3 c s)
        (A4 c' s + c * A2 c' s + (A4 c s + β (D.θ c' * s) (g3 c s))) *
        D.p5 (D.θ (c + c') * s) := by
    have hconj : D.p6 c * (Nel4 D (A2 c' s) (g3 c' s) (A4 c' s) * D.p5 (D.θ c' * s)) * (D.p6 c)⁻¹ =
        Nel4 D (A2 c' s) (g3 c' s) (A4 c' s + c * A2 c' s) * D.p5 (D.θ c' * s) := by
      calc _ = (D.p6 c * Nel4 D (A2 c' s) (g3 c' s) (A4 c' s) * (D.p6 c)⁻¹) *
            (D.p6 c * D.p5 (D.θ c' * s) * (D.p6 c)⁻¹) := by group
        _ = _ := by rw [conj_p6_Nel4 hC D c _ _ (had.g3_mem c' s), hc56]
    have hp5 : D.p5 (D.θ c' * s) * Nel4 D (A2 c s) (g3 c s) (A4 c s) =
        Nel4 D (A2 c s) (g3 c s) (A4 c s + β (D.θ c' * s) (g3 c s)) * D.p5 (D.θ c' * s) := by
      rw [← conj_p5_Nel4 hC D hβ (D.θ c' * s) _ _ (had.g3_mem c s)]; group
    calc _ = Nel4 D (A2 c' s) (g3 c' s) (A4 c' s + c * A2 c' s) *
          (D.p5 (D.θ c' * s) * Nel4 D (A2 c s) (g3 c s) (A4 c s)) * D.p5 (D.θ c * s) := by
          rw [hconj]; group
      _ = Nel4 D (A2 c' s) (g3 c' s) (A4 c' s + c * A2 c' s) *
          Nel4 D (A2 c s) (g3 c s) (A4 c s + β (D.θ c' * s) (g3 c s)) *
          (D.p5 (D.θ c' * s) * D.p5 (D.θ c * s)) := by rw [hp5]; group
      _ = _ := by
          rw [Nel4_mul hC D (had.g3_mem c' s) (had.g3_mem c s), ← D.p5_add]
          congr 2
          rw [map_add]; ring
  rw [h1'] at h1
  have h2 := mul_right_cancel h1
  have := Nel4_inj R D (had.g3_mem _ _) ((root 3).mul_mem (had.g3_mem _ _) (had.g3_mem _ _)) h2
  refine ⟨this.1, this.2.1, ?_⟩
  rw [this.2.2]; ring

include R hC hβ hcd had in
theorem act_add_s4 (c : F) (s s' : K) :
    A2 c (s + s') = A2 c s + (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')) ∧
      g3 c (s + s') = g3 c s * (g3 c s' * L s (D.θ c * s')) ∧
      A4 c (s + s') = A4 c s + (A4 c s' + a4 s (D.θ c * s') +
        β (D.θ c * s) (g3 c s' * L s (D.θ c * s'))) := by
  have eq : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s) :=
    fun c s => had.eq c s
  have eqc : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have h1 : ⁅D.p6 c, D.p1 (s + s')⁆ =
      ⁅D.p6 c, D.p1 s⁆ * (D.p1 s * ⁅D.p6 c, D.p1 s'⁆ * (D.p1 s)⁻¹) := by
    rw [D.p1_add]; simp only [commutatorElement_def]; group
  rw [eq c (s + s'), eq c s, eq c s'] at h1
  have hp5 : D.p1 s * D.p5 (D.θ c * s') * (D.p1 s)⁻¹ =
      Nel4 D (a2 s (D.θ c * s')) (L s (D.θ c * s')) (a4 s (D.θ c * s')) * D.p5 (D.θ c * s') := by
    rw [← eqc s (D.θ c * s')]; simp only [commutatorElement_def]; group
  have hconj : D.p1 s * (Nel4 D (A2 c s') (g3 c s') (A4 c s') * D.p5 (D.θ c * s')) * (D.p1 s)⁻¹ =
      Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')) (g3 c s' * L s (D.θ c * s'))
        (A4 c s' + a4 s (D.θ c * s')) * D.p5 (D.θ c * s') := by
    calc _ = (D.p1 s * Nel4 D (A2 c s') (g3 c s') (A4 c s') * (D.p1 s)⁻¹) *
          (D.p1 s * D.p5 (D.θ c * s') * (D.p1 s)⁻¹) := by group
      _ = _ := by
        rw [conj_p1_Nel4 hC D hβ s _ _ (had.g3_mem c s'), hp5, ← mul_assoc,
          Nel4_mul hC D (had.g3_mem c s') (hcd.L_mem s (D.θ c * s'))]
  have hY : (g3 c s' * L s (D.θ c * s')) ∈ root 3 :=
    (root 3).mul_mem (had.g3_mem c s') (hcd.L_mem s (D.θ c * s'))
  have hp5' : D.p5 (D.θ c * s) * Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s'))
      (g3 c s' * L s (D.θ c * s')) (A4 c s' + a4 s (D.θ c * s')) =
      Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')) (g3 c s' * L s (D.θ c * s'))
        (A4 c s' + a4 s (D.θ c * s') + β (D.θ c * s) (g3 c s' * L s (D.θ c * s'))) *
        D.p5 (D.θ c * s) := by
    rw [← conj_p5_Nel4 hC D hβ (D.θ c * s) _ _ hY]; group
  rw [hconj] at h1
  have h2 : Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s) *
      (Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')) (g3 c s' * L s (D.θ c * s'))
        (A4 c s' + a4 s (D.θ c * s')) * D.p5 (D.θ c * s')) =
      Nel4 D (A2 c s + (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')))
        (g3 c s * (g3 c s' * L s (D.θ c * s')))
        (A4 c s + (A4 c s' + a4 s (D.θ c * s') +
          β (D.θ c * s) (g3 c s' * L s (D.θ c * s')))) *
        D.p5 (D.θ c * (s + s')) := by
    calc _ = Nel4 D (A2 c s) (g3 c s) (A4 c s) *
          (D.p5 (D.θ c * s) * Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s'))
            (g3 c s' * L s (D.θ c * s')) (A4 c s' + a4 s (D.θ c * s'))) *
          D.p5 (D.θ c * s') := by group
      _ = Nel4 D (A2 c s) (g3 c s) (A4 c s) *
          Nel4 D (A2 c s' + β s (g3 c s') + a2 s (D.θ c * s')) (g3 c s' * L s (D.θ c * s'))
            (A4 c s' + a4 s (D.θ c * s') +
              β (D.θ c * s) (g3 c s' * L s (D.θ c * s'))) *
          (D.p5 (D.θ c * s) * D.p5 (D.θ c * s')) := by rw [hp5']; group
      _ = _ := by
        rw [Nel4_mul hC D (had.g3_mem c s) hY, ← D.p5_add, mul_add]
  rw [h2] at h1
  have h3 := mul_right_cancel h1
  have := Nel4_inj R D (had.g3_mem _ _)
    ((root 3).mul_mem (had.g3_mem _ _) hY) h3
  exact ⟨this.1, this.2.1, this.2.2⟩

include R hC hβ hcd had in
theorem act_comm4 (c : F) (s t : K) :
    c * a2 s t = β (D.θ c * s) (L s t) - β t (g3 c s) := by
  have eqc : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  set n := Nel4 D (A2 c s) (g3 c s) (A4 c s) with hn
  have hnmem : n ∈ Vsub root 2 4 := Nel4_mem D (had.g3_mem c s)
  have h : D.p6 c * ⁅D.p1 s, D.p5 t⁆ * (D.p6 c)⁻¹ =
      ⁅D.p6 c * D.p1 s * (D.p6 c)⁻¹, D.p6 c * D.p5 t * (D.p6 c)⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hp1 : D.p6 c * D.p1 s * (D.p6 c)⁻¹ = n * D.p5 (D.θ c * s) * D.p1 s := by
    have : D.p6 c * D.p1 s * (D.p6 c)⁻¹ = ⁅D.p6 c, D.p1 s⁆ * D.p1 s := by
      simp only [commutatorElement_def]; group
    rw [this, had.eq c s]
  have hp5 : D.p6 c * D.p5 t * (D.p6 c)⁻¹ = D.p5 t := by
    rw [mul_inv_eq_iff_eq_mul]; exact (hC.c56 _ (D.p5_mem t) _ (D.p6_mem c)).symm
  rw [hp1, hp5, eqc s t, conj_p6_Nel4 hC D c _ _ (hcd.L_mem s t)] at h
  have hxz : ⁅D.p5 (D.θ c * s), D.p5 t⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
    (hC.ab 5 (by norm_num) (by norm_num) _ (D.p5_mem _) _ (D.p5_mem _))
  have hI : ⁅n * D.p5 (D.θ c * s) * D.p1 s, D.p5 t⁆ =
      (n * D.p5 (D.θ c * s)) * ⁅D.p1 s, D.p5 t⁆ *
      (n * D.p5 (D.θ c * s))⁻¹ * (n * ⁅D.p5 (D.θ c * s), D.p5 t⁆ * n⁻¹ * ⁅n, D.p5 t⁆) := by
    simp only [commutatorElement_def]; group
  rw [hI, hxz, eqc s t, mul_one, mul_inv_cancel, one_mul] at h
  have hM : (n * D.p5 (D.θ c * s)) * Nel4 D (a2 s t) (L s t) (a4 s t) *
      (n * D.p5 (D.θ c * s))⁻¹ =
      Nel4 D (a2 s t) (L s t) (a4 s t + β (D.θ c * s) (L s t)) := by
    have hMmem : Nel4 D (a2 s t) (L s t) (a4 s t + β (D.θ c * s) (L s t)) ∈ Vsub root 2 4 :=
      Nel4_mem D (hcd.L_mem s t)
    have hc : n * Nel4 D (a2 s t) (L s t) (a4 s t + β (D.θ c * s) (L s t)) =
        Nel4 D (a2 s t) (L s t) (a4 s t + β (D.θ c * s) (L s t)) * n :=
      V24_comm R hC hnmem hMmem
    calc (n * D.p5 (D.θ c * s)) * Nel4 D (a2 s t) (L s t) (a4 s t) *
          (n * D.p5 (D.θ c * s))⁻¹
        = n * (D.p5 (D.θ c * s) * Nel4 D (a2 s t) (L s t) (a4 s t) *
            (D.p5 (D.θ c * s))⁻¹) * n⁻¹ := by
          group
      _ = n * Nel4 D (a2 s t) (L s t) (a4 s t + β (D.θ c * s) (L s t)) * n⁻¹ := by
          rw [conj_p5_Nel4 hC D hβ (D.θ c * s) _ _ (hcd.L_mem s t)]
      _ = _ := by rw [hc]; group
  rw [hM] at h
  have hν : ⁅n, D.p5 t⁆ * Nel4 D 0 1 (β t (g3 c s)) = 1 := by
    have hzn : D.p5 t * n * (D.p5 t)⁻¹ = n * Nel4 D 0 1 (β t (g3 c s)) := by
      rw [hn, conj_p5_Nel4 hC D hβ t _ _ (had.g3_mem c s),
        Nel4_mul hC D (had.g3_mem c s) (root 3).one_mem]
      simp
    have hcν : Commute n (Nel4 D 0 1 (β t (g3 c s))) :=
      V24_comm R hC hnmem (Nel4_mem D (root 3).one_mem)
    calc ⁅n, D.p5 t⁆ * Nel4 D 0 1 (β t (g3 c s))
        = n * (D.p5 t * n * (D.p5 t)⁻¹)⁻¹ * Nel4 D 0 1 (β t (g3 c s)) := by
          simp only [commutatorElement_def]; group
      _ = n * (n * Nel4 D 0 1 (β t (g3 c s)))⁻¹ * Nel4 D 0 1 (β t (g3 c s)) := by rw [hzn]
      _ = (n * (Nel4 D 0 1 (β t (g3 c s)))⁻¹ * n⁻¹) * Nel4 D 0 1 (β t (g3 c s)) := by group
      _ = 1 := by
          rw [mul_inv_eq_iff_eq_mul.2 (hcν.inv_right.eq), inv_mul_cancel]
  have h' := congrArg (fun x => x * Nel4 D 0 1 (β t (g3 c s))) h
  simp only [mul_assoc, hν, mul_one] at h'
  rw [Nel4_mul hC D (hcd.L_mem s t) (root 3).one_mem] at h'
  have := Nel4_inj R D ((root 3).mul_mem (hcd.L_mem s t) (root 3).one_mem) (hcd.L_mem s t) h'
  have h3 := this.2.2
  linear_combination h3

include R had in
theorem act_torus4 (τ : Fˣ) (c : F) (s : K) :
    A2 ((τ : F) ^ 2 * c) ((D.θ (τ : F))⁻¹ * s) = (τ : F)⁻¹ * A2 c s ∧
      g3 ((τ : F) ^ 2 * c) ((D.θ (τ : F))⁻¹ * s) = g3 c s ∧
      A4 ((τ : F) ^ 2 * c) ((D.θ (τ : F))⁻¹ * s) = (τ : F) * A4 c s := by
  have eq : ∀ c s, ⁅D.p6 c, D.p1 s⁆ = Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s) :=
    fun c s => had.eq c s
  have hconj : D.T τ * ⁅D.p6 c, D.p1 s⁆ * (D.T τ)⁻¹ =
      ⁅D.p6 ((τ : F) ^ 2 * c), D.p1 ((D.θ (τ : F))⁻¹ * s)⁆ := by
    have : D.T τ * ⁅D.p6 c, D.p1 s⁆ * (D.T τ)⁻¹ =
        ⁅D.T τ * D.p6 c * (D.T τ)⁻¹, D.T τ * D.p1 s * (D.T τ)⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [this, D.w6, D.w1]
  rw [eq c s] at hconj
  have hL : D.T τ * (Nel4 D (A2 c s) (g3 c s) (A4 c s) * D.p5 (D.θ c * s)) * (D.T τ)⁻¹ =
      Nel4 D ((τ : F)⁻¹ * A2 c s) (g3 c s) ((τ : F) * A4 c s) *
        D.p5 (D.θ (τ : F) * (D.θ c * s)) := by
    calc _ = (D.T τ * Nel4 D (A2 c s) (g3 c s) (A4 c s) * (D.T τ)⁻¹) *
          (D.T τ * D.p5 (D.θ c * s) * (D.T τ)⁻¹) := by group
      _ = _ := by rw [conj_T_Nel4 D τ (had.g3_mem c s), D.w5]
  rw [hL, eq] at hconj
  have h5 : D.p5 (D.θ (τ : F) * (D.θ c * s)) =
      D.p5 (D.θ ((τ : F) ^ 2 * c) * ((D.θ (τ : F))⁻¹ * s)) := by
    congr 1
    have hτ : D.θ (τ : F) ≠ 0 := (map_ne_zero D.θ).2 τ.ne_zero
    rw [map_mul, map_pow]
    field_simp
  rw [h5] at hconj
  have h6 := mul_right_cancel hconj
  have := Nel4_inj R D (had.g3_mem _ _) (had.g3_mem _ _) h6
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

end Act4

end CFSG.GH74.GLS.Stage4.Hex
