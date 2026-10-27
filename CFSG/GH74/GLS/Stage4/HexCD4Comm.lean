module

public import CFSG.GH74.GLS.Stage4.HexCD4Ncalc

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F K : Type} [Field F] [Field K]

structure CommData4 (D : HexData4 root F K) (a2 a4 : K → K → F) (L : K → K → G) : Prop where
  L_mem : ∀ s t, L s t ∈ root 3
  eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = D.p2 (a2 s t) * L s t * D.p4 (a4 s t)

section Comm4

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData4 root F K)

include R in
theorem comm15_mem4 (s t : K) : ⁅D.p1 s, D.p5 t⁆ ∈ Vsub root 2 4 := by
  have h := rgd2_octComm R 1 5 (by norm_num) (by norm_num) (by norm_num) _ (D.p1_mem s) _
    (D.p5_mem t)
  refine (iSup₂_le (fun k hk => ?_) : (⨆ k ∈ Set.Ioo (1 : ℤ) 5, root k) ≤ Vsub root 2 4) h
  have := Set.mem_Ioo.1 hk
  exact root_le_Vsub (by omega) (by omega)

include R in
theorem exists_commData4 : ∃ (a2 a4 : K → K → F) (L : K → K → G), CommData4 D a2 a4 L := by
  classical
  have h : ∀ s t, ∃ a ∈ root 2, ∃ u ∈ root 3, ∃ b ∈ root 4,
      ⁅D.p1 s, D.p5 t⁆ = a * u * b := fun s t => V24_decomp R (comm15_mem4 R D s t)
  choose a ha u hu b hb he using h
  have hA : ∀ s t, ∃ e, D.p2 e = a s t := fun s t => D.p2_surj _ (ha s t)
  have hB : ∀ s t, ∃ e, D.p4 e = b s t := fun s t => D.p4_surj _ (hb s t)
  choose a2 ha2 using hA
  choose a4 ha4 using hB
  refine ⟨a2, a4, u, ⟨hu, fun s t => ?_⟩⟩
  rw [ha2, ha4]
  exact he s t

variable {β : K → G → F} (hβ : PairData D β) {a2 a4 : K → K → F} {L : K → K → G}
  (hcd : CommData4 D a2 a4 L)

include R hC hβ hcd in
theorem comm15_add_s4 (s s' t : K) :
    a2 (s + s') t = a2 s' t + β s (L s' t) + a2 s t ∧ L (s + s') t = L s' t * L s t ∧
      a4 (s + s') t = a4 s' t + a4 s t := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have h1 : ⁅D.p1 (s + s'), D.p5 t⁆ =
      D.p1 s * ⁅D.p1 s', D.p5 t⁆ * (D.p1 s)⁻¹ * ⁅D.p1 s, D.p5 t⁆ := by
    rw [D.p1_add]; simp only [commutatorElement_def]; group
  rw [eq (s + s') t, eq s' t, eq s t] at h1
  have h1' : D.p1 s * Nel4 D (a2 s' t) (L s' t) (a4 s' t) * (D.p1 s)⁻¹ *
      Nel4 D (a2 s t) (L s t) (a4 s t) =
      Nel4 D (a2 s' t + β s (L s' t) + a2 s t) (L s' t * L s t) (a4 s' t + a4 s t) := by
    rw [conj_p1_Nel4 hC D hβ s _ _ (hcd.L_mem s' t),
      Nel4_mul hC D (hcd.L_mem s' t) (hcd.L_mem s t)]
  rw [h1'] at h1
  have := Nel4_inj R D (hcd.L_mem _ _) ((root 3).mul_mem (hcd.L_mem _ _) (hcd.L_mem _ _)) h1
  exact ⟨this.1, this.2.1, this.2.2⟩

include R hC hβ hcd in
theorem comm15_add_t4 (s t t' : K) :
    a2 s (t + t') = a2 s t + a2 s t' ∧ L s (t + t') = L s t * L s t' ∧
      a4 s (t + t') = a4 s t + (a4 s t' + β t (L s t')) := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have h1 : ⁅D.p1 s, D.p5 (t + t')⁆ =
      ⁅D.p1 s, D.p5 t⁆ * (D.p5 t * ⁅D.p1 s, D.p5 t'⁆ * (D.p5 t)⁻¹) := by
    rw [D.p5_add]; simp only [commutatorElement_def]; group
  rw [eq s (t + t'), eq s t, eq s t'] at h1
  have h1' : Nel4 D (a2 s t) (L s t) (a4 s t) *
      (D.p5 t * Nel4 D (a2 s t') (L s t') (a4 s t') * (D.p5 t)⁻¹) =
      Nel4 D (a2 s t + a2 s t') (L s t * L s t') (a4 s t + (a4 s t' + β t (L s t'))) := by
    rw [conj_p5_Nel4 hC D hβ t _ _ (hcd.L_mem s t'),
      Nel4_mul hC D (hcd.L_mem s t) (hcd.L_mem s t')]
  rw [h1'] at h1
  have := Nel4_inj R D (hcd.L_mem _ _) ((root 3).mul_mem (hcd.L_mem _ _) (hcd.L_mem _ _)) h1
  exact ⟨this.1, this.2.1, this.2.2⟩

include R hcd in
theorem comm15_torus4 (τ : Fˣ) (s t : K) :
    a2 ((D.θ (τ : F))⁻¹ * s) (D.θ (τ : F) * t) = (τ : F)⁻¹ * a2 s t ∧
      L ((D.θ (τ : F))⁻¹ * s) (D.θ (τ : F) * t) = L s t ∧
      a4 ((D.θ (τ : F))⁻¹ * s) (D.θ (τ : F) * t) = (τ : F) * a4 s t := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel4 D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have hconj : D.T τ * ⁅D.p1 s, D.p5 t⁆ * (D.T τ)⁻¹ =
      ⁅D.p1 ((D.θ (τ : F))⁻¹ * s), D.p5 (D.θ (τ : F) * t)⁆ := by
    have : D.T τ * ⁅D.p1 s, D.p5 t⁆ * (D.T τ)⁻¹ =
        ⁅D.T τ * D.p1 s * (D.T τ)⁻¹, D.T τ * D.p5 t * (D.T τ)⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [this, D.w1, D.w5]
  rw [eq s t, conj_T_Nel4 D τ (hcd.L_mem s t), eq] at hconj
  have := Nel4_inj R D (hcd.L_mem _ _) (hcd.L_mem _ _) hconj
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

end Comm4

end CFSG.GH74.GLS.Stage4.Hex
