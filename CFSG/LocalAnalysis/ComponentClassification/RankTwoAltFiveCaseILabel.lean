module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsA6
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveCaseISylow
public import CFSG.Sporadic.Recognition.JankoWongPSLNine

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup Equiv Equiv.Perm CFSG.Open CFSG.ABGLocalTools CFSG.GorensteinWalter
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoAlt CFSG.Quasithin.SteinbergCB

variable {G : Type} [Group G] [Finite G]

theorem exists_viaEmbedding_castLE_of_fix {m n : ℕ} (h : m ≤ n) {π : Perm (Fin n)}
    (hπ : ∀ i : Fin n, m ≤ (i : ℕ) → π i = i) :
    ∃ π' : Perm (Fin m), viaEmbeddingHom (Fin.castLEEmb h) π' = π := by
  have hlt : ∀ σ : Perm (Fin n), (∀ i : Fin n, m ≤ (i : ℕ) → σ i = i) →
      ∀ i : Fin n, (i : ℕ) < m → (σ i : ℕ) < m := by
    intro σ hσ i hi
    by_contra hge
    push Not at hge
    have := hσ (σ i) hge
    have hii : σ i = i := σ.injective this
    rw [hii] at hge
    omega
  have hπinv : ∀ i : Fin n, m ≤ (i : ℕ) → π⁻¹ i = i := fun i hi =>
    (Perm.inv_eq_iff_eq).mpr (hπ i hi).symm
  let f : Fin m → Fin m := fun j => ⟨π (Fin.castLEEmb h j), hlt π hπ _ (by simp)⟩
  let g : Fin m → Fin m := fun j => ⟨π⁻¹ (Fin.castLEEmb h j), hlt π⁻¹ hπinv _ (by simp)⟩
  have hemb : ∀ j : Fin m, Fin.castLEEmb h (f j) = π (Fin.castLEEmb h j) := fun j => Fin.ext (by
    simp [f])
  have hemb' : ∀ j : Fin m, Fin.castLEEmb h (g j) = π⁻¹ (Fin.castLEEmb h j) := fun j =>
    Fin.ext (by simp [g])
  let π' : Perm (Fin m) :=
    { toFun := f
      invFun := g
      left_inv := fun j => (Fin.castLEEmb h).injective (by rw [hemb', hemb]; simp)
      right_inv := fun j => (Fin.castLEEmb h).injective (by rw [hemb, hemb']; simp) }
  refine ⟨π', Equiv.ext fun i => ?_⟩
  by_cases hi : (i : ℕ) < m
  · have hi' : Fin.castLEEmb h ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← hi', viaEmbeddingHom_apply_image]
    exact hemb ⟨i, hi⟩
  · have hnot : i ∉ Set.range (Fin.castLEEmb h) := by
      rintro ⟨j, rfl⟩
      exact hi (by simp)
    rw [viaEmbeddingHom_apply_of_notMem _ _ hnot, hπ i (by omega)]

@[expose] noncomputable def ιP56 : Perm (Fin 5) →* Perm (Fin 6) :=
  viaEmbeddingHom (Fin.castLEEmb (by norm_num : 5 ≤ 6))

@[expose] noncomputable def ι56 : A5 →* alternatingGroup (Fin 6) :=
  (ιP56.comp A5.subtype).codRestrict (alternatingGroup (Fin 6)) fun σ => by
    rw [MonoidHom.comp_apply, mem_alternatingGroup, ιP56, sign_viaEmbeddingHom]
    exact σ.2

theorem coe_ι56 (σ : A5) : ((ι56 σ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
    ιP56 (σ : Perm (Fin 5)) := rfl

theorem ιP56_injective : Function.Injective ιP56 := viaEmbeddingHom_injective _

theorem ι56_injective : Function.Injective ι56 := fun _ _ h =>
  Subtype.ext (ιP56_injective (congrArg Subtype.val h :))

theorem mem_range_ι56 {x : alternatingGroup (Fin 6)} (hx : (x : Perm (Fin 6)) 5 = 5) :
    x ∈ ι56.range := by
  obtain ⟨π', hπ'⟩ := exists_viaEmbedding_castLE_of_fix (by norm_num : 5 ≤ 6)
    (π := (x : Perm (Fin 6))) (fun i hi => by
      have : i = 5 := Fin.ext (by have := i.isLt; omega)
      rw [this, hx])
  have hs : π' ∈ alternatingGroup (Fin 5) := by
    rw [mem_alternatingGroup, ← sign_viaEmbeddingHom (Fin.castLEEmb (by norm_num : 5 ≤ 6)), hπ']
    exact x.2
  exact ⟨⟨π', hs⟩, Subtype.ext (by rw [coe_ι56]; exact hπ')⟩

theorem ιP56_castSucc (π : Perm (Fin 5)) (i : Fin 5) : ιP56 π i.castSucc = (π i).castSucc :=
  viaEmbeddingHom_apply_image (Fin.castLEEmb (by norm_num : 5 ≤ 6)) π i

theorem ιP56_five (π : Perm (Fin 5)) : ιP56 π 5 = 5 := by
  refine viaEmbeddingHom_apply_of_notMem _ π fun ⟨j, hj⟩ => ?_
  have h1 := j.isLt
  have h2 := congrArg Fin.val hj
  simp at h2
  omega

theorem ιP56_eq_of {π : Perm (Fin 5)} {σ : Perm (Fin 6)} (h5 : σ 5 = 5)
    (h : ∀ i : Fin 5, σ i.castSucc = (π i).castSucc) : ιP56 π = σ := by
  refine Equiv.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => exact (ιP56_five π).trans h5.symm
  | cast i => rw [ιP56_castSucc, h]

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

@[expose] def c013 : A5 := ⟨swap 0 1 * swap 1 3, by decide⟩

theorem ι56_y0 : ι56 y0 = a6c012 := Subtype.ext (ιP56_eq_of (by decide) (by decide))

theorem ι56_c013 : ι56 c013 = a6c013 := Subtype.ext (ιP56_eq_of (by decide) (by decide))

theorem c013_norm : ∀ q ∈ (1 :: p0inv), c013 * q * c013⁻¹ ∈ (1 :: p0inv) := by decide

namespace CaseICoords

variable {A B R T : Subgroup G} (c : CaseICoords A B R T)

theorem psiB_mem_normalizer {a : A5} (ha : ∀ q ∈ (1 :: p0inv), a * q * a⁻¹ ∈ (1 :: p0inv)) :
    ((c.ψB a : B) : G) ∈ B ⊓ normalizer (R : Set G) := by
  refine ⟨(c.ψB a).2, RankTwoAlt.mem_normalizer_of_conj_le fun r hr => ?_⟩
  have hrB := c.pair.R_le hr
  rw [c.mem_R_iff hrB] at hr
  have hm : ((c.ψB a : B) : G) * r * ((c.ψB a : B) : G)⁻¹ ∈ B :=
    mul_mem (mul_mem (c.ψB a).2 hrB) (inv_mem (c.ψB a).2)
  rw [c.mem_R_iff hm]
  have h1 : c.ψB.symm ⟨((c.ψB a : B) : G) * r * ((c.ψB a : B) : G)⁻¹, hm⟩ =
      a * c.ψB.symm ⟨r, hrB⟩ * a⁻¹ := by
    apply c.ψB.injective
    rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  rw [h1, mem_P0]
  exact ha _ (mem_P0.mp hr)

theorem exists_label (hA6 : Nonempty (c.Hbar ≃* alternatingGroup (Fin 6))) :
    ∃ θ : c.Hbar ≃* alternatingGroup (Fin 6),
      ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ := by
  obtain ⟨θ0⟩ := hA6
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup c.Hbar := θ0.isSimpleGroup
  have hQcard : Nat.card c.Hbar = 360 := by rw [Nat.card_congr θ0.toEquiv, card_alt6]
  set Bb := (c.barOf c.B_le_H).range with hBb
  have hBb60 : Nat.card Bb = 60 := c.card_range_B
  have hBbi : Bb.index = 6 := by
    have h := Bb.card_mul_index
    rw [hBb60, hQcard] at h
    omega
  have hBbtop : Bb ≠ ⊤ := fun h => by
    rw [h, index_top] at hBbi
    omega
  have hcard : Nat.card (c.Hbar ⧸ Bb) = 6 := hBbi
  let e0 : c.Hbar ⧸ Bb ≃ Fin 6 := Finite.equivFinOfCardEq hcard
  let e : c.Hbar ⧸ Bb ≃ Fin 6 := e0.trans (swap (e0 (1 : c.Hbar)) 5)
  have he1 : e ((1 : c.Hbar) : c.Hbar ⧸ Bb) = 5 := by
    simp only [e, Equiv.trans_apply, swap_apply_left]
  let ψ : c.Hbar →* Perm (Fin 6) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom c.Hbar (c.Hbar ⧸ Bb))
  have hψapp : ∀ h : c.Hbar, ∀ i : Fin 6, ψ h i = e (h • e.symm i) := fun h i => rfl
  have hψ : Function.Injective ψ :=
    e.permCongrHom.injective.comp
      (CFSG.Sporadic.Recognition.JankoWong.PSLNineStep.injective_toPermHom_of_ne_top hBbtop)
  have hrange_card : Nat.card ψ.range = 360 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hQcard]
  have hindex : ψ.range.index = 2 := by
    have h := ψ.range.card_mul_index
    rw [hrange_card, Nat.card_perm, Nat.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have hrange : ψ.range = alternatingGroup (Fin 6) := eq_alternatingGroup_of_index_eq_two hindex
  set θ1 : c.Hbar ≃* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange) with hθ1
  have hθ1app : ∀ h, ((θ1 h : alternatingGroup (Fin 6)) : Perm (Fin 6)) = ψ h := fun h => rfl
  have hfix : ∀ h ∈ Bb, ψ h 5 = 5 := by
    intro h hh
    rw [hψapp, ← he1, Equiv.symm_apply_apply, MulAction.Quotient.smul_mk, smul_eq_mul,
      mul_one]
    congr 1
    rw [QuotientGroup.eq, mul_one]
    exact inv_mem hh
  set j : A5 →* alternatingGroup (Fin 6) :=
    θ1.toMonoidHom.comp ((c.barOf c.B_le_H).comp c.ψB.toMonoidHom) with hj
  have hjinj : Function.Injective j :=
    θ1.injective.comp ((c.barOf_injective c.B_le_H c.ψB.symm).comp c.ψB.injective)
  have hjrange : j.range = ι56.range := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨σ, rfl⟩
      exact mem_range_ι56 (hfix _ ⟨c.ψB σ, rfl⟩)
    · rw [← Nat.card_congr (MonoidHom.ofInjective ι56_injective).toEquiv,
        ← Nat.card_congr (MonoidHom.ofInjective hjinj).toEquiv]
  set ε : A5 ≃* A5 := (MonoidHom.ofInjective hjinj).trans ((MulEquiv.subgroupCongr hjrange).trans
    (MonoidHom.ofInjective ι56_injective).symm) with hεdef
  have hε : ∀ σ, ι56 (ε σ) = j σ := by
    intro σ
    have h1 := MonoidHom.ofInjective_apply ι56_injective (x := ε σ)
    rw [← h1, hεdef, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨τ, hτ⟩ := conjPerm_surjective (n := 5) (Or.inl rfl) ε
  have hετ : ∀ σ : A5, ((ε σ : A5) : Perm (Fin 5)) = τ * σ * τ⁻¹ := fun σ => by
    rw [← hτ, conjPerm_apply]
  refine ⟨θ1.trans (conjPerm 6 (ιP56 τ)⁻¹), fun σ => Subtype.ext ?_⟩
  rw [MulEquiv.trans_apply, conjPerm_apply, inv_inv, coe_ι56]
  have h1 : θ1 (c.barOf c.B_le_H (c.ψB σ)) = ι56 (ε σ) := (hε σ).symm
  rw [h1, coe_ι56, hετ, map_mul, map_mul, map_inv]
  group

theorem label_x {θ : c.Hbar ≃* alternatingGroup (Fin 6)}
    (hθ : ∀ σ : A5, θ (c.barOf c.B_le_H (c.ψB σ)) = ι56 σ) (h : c.Hbar) :
    θ (quotAut ⟨c.x, c.x_mem_normalizer⟩ h) = conjPerm 6 (swap 4 5) (θ h) := by
  set q := quotAut (K := c.H) ⟨c.x, c.x_mem_normalizer⟩ with hq
  have hfixY : ∀ a : A5, (∀ q ∈ (1 :: p0inv), a * q * a⁻¹ ∈ (1 :: p0inv)) →
      q (c.barOf c.B_le_H (c.ψB a)) = c.barOf c.B_le_H (c.ψB a) := by
    intro a ha
    have hK : ((c.ψB a : B) : G) ∈ centralizer (A : Set G) :=
      c.pair.inf_normalizer_le (c.psiB_mem_normalizer ha)
    rw [barOf_apply, hq, quotAut_mk]
    congr 1
    apply Subtype.ext
    show c.x * ((c.ψB a : B) : G) * c.x⁻¹ = ((c.ψB a : B) : G)
    rw [(mem_centralizer_iff.mp hK c.x c.x_mem), mul_inv_cancel_right]
  set β : MulAut (alternatingGroup (Fin 6)) := θ.symm.trans (q.trans θ) with hβ
  have hβapp : ∀ g, β g = θ (q (θ.symm g)) := fun g => rfl
  have hβ1 : β a6c012 = a6c012 := by
    rw [hβapp, ← ι56_y0, ← hθ, MulEquiv.symm_apply_apply, hfixY y0 y0_norm]
  have hβ2 : β a6c013 = a6c013 := by
    rw [hβapp, ← ι56_c013, ← hθ, MulEquiv.symm_apply_apply, hfixY c013 c013_norm]
  rcases eq_one_or_eq_conj45 hβ1 hβ2 with h1 | h1
  ·
    exfalso
    apply c.false_of_range_le
    rintro _ ⟨⟨_, ⟨b, hb, rfl⟩⟩, rfl⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    have h2 : q (c.barOf c.B_le_H ⟨b, hb⟩) = c.barOf c.B_le_H ⟨b, hb⟩ := by
      apply θ.injective
      have := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) =>
        φ (θ (c.barOf c.B_le_H ⟨b, hb⟩))) h1
      simpa [hβapp] using this
    rw [← h2, barOf_apply, hq, quotAut_mk]
    rfl
  · have := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) => φ (θ h)) h1
    simpa [hβapp] using this

end CaseICoords

end CFSG.ComponentClassification.RankTwoAltFive
