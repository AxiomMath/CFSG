module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD7Frame

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

theorem aff8_comm_k8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 1 →
    aff8 u b * k8 * (aff8 u b)⁻¹ * k8⁻¹ ≠ 1 := by decide

theorem aff8_comm_refl_even : ∀ u : (ZMod 8)ˣ, ∀ c e : ZMod 8, dbit8 e = 0 →
    aff8 u c * aff8 (-1) e = aff8 (-1) e * aff8 u c → dbit8 c = 0 := by decide

theorem R8_comm_refl_one : ∀ c e : ZMod 8, dbit8 e = 0 →
    aff8 1 (2 * c) * aff8 (-1) e = aff8 (-1) e * aff8 1 (2 * c) →
      aff8 1 (2 * c) = 1 ∨ aff8 1 (2 * c) = z8 := by decide

theorem R8_comm_refl_neg : ∀ c e : ZMod 8, dbit8 e = 0 →
    aff8 (-1) (2 * c) * aff8 (-1) e = aff8 (-1) e * aff8 (-1) (2 * c) →
      aff8 (-1) (2 * c) = aff8 (-1) e ∨ aff8 (-1) (2 * c) = z8 * aff8 (-1) e := by decide

theorem R8_comm_refl {u : (ZMod 8)ˣ} {c e : ZMod 8} (hu : u = 1 ∨ u = -1) (he : dbit8 e = 0)
    (h : aff8 u (2 * c) * aff8 (-1) e = aff8 (-1) e * aff8 u (2 * c)) :
    aff8 u (2 * c) = 1 ∨ aff8 u (2 * c) = z8 ∨ aff8 u (2 * c) = aff8 (-1) e ∨
      aff8 u (2 * c) = z8 * aff8 (-1) e := by
  rcases hu with rfl | rfl
  · rcases R8_comm_refl_one c e he h with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · rcases R8_comm_refl_neg c e he h with h1 | h1
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem B_eq : S.B = zpowers S.z ⊔ zpowers t ⊔ zpowers S.k := Sec7.closure_triple_eq _ _ _

theorem B_le_T : S.B ≤ A.T := by
  rw [B_eq]
  exact sup_le (sup_le (zpowers_le.mpr (z_mem_T S)) (zpowers_le.mpr A.t_mem_T))
    (zpowers_le.mpr C.k_mem)

theorem B_comm_R {b r : X} (hb : b ∈ S.B) (hr : r ∈ A.R) : b * r = r * b := by
  have hle : S.B ≤ centralizer ({r} : Set X) := by
    rw [B_eq]
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_) <;>
      rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S hr.1).symm
    · exact (A.commute_t hr.1).symm
    · exact L2KD.commute_k C hr
  exact mem_centralizer_singleton_iff.mp (hle hb)

theorem B_comm_k {b : X} (hb : b ∈ S.B) : b * S.k = S.k * b := by
  have hle : S.B ≤ centralizer ({S.k} : Set X) := by
    rw [B_eq]
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) <;>
      rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S C.k_mem).symm
    · exact (A.commute_t C.k_mem).symm
  exact mem_centralizer_singleton_iff.mp (hle hb)

theorem B_comm_B {b c : X} (hb : b ∈ S.B) (hc : c ∈ S.B) : b * c = c * b := by
  have hle : S.B ≤ centralizer ({c} : Set X) := by
    rw [B_eq]
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_) <;>
      rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S (B_le_T S hc)).symm
    · exact (A.commute_t (B_le_T S hc)).symm
    · exact (B_comm_k S hc).symm
  exact mem_centralizer_singleton_iff.mp (hle hb)

theorem elemAbelianTwo_B : ElemAbelianTwo S.B := by
  have hzt : ElemAbelianTwo (zpowers S.z ⊔ zpowers t : Subgroup X) :=
    Sec7.elemAbelianTwo_sup (elemAbelianTwo_z S) (L2K.t_sq (A := A))
      fun _ ha => comm_zpowers_z S A.t_mem_T ha
  rw [B_eq]
  refine Sec7.elemAbelianTwo_sup hzt C.k_sq fun a ha => ?_
  have hle : (zpowers S.z ⊔ zpowers t : Subgroup X) ≤ centralizer ({S.k} : Set X) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_) <;> rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S C.k_mem).symm
    · exact (A.commute_t C.k_mem).symm
  exact (mem_centralizer_singleton_iff.mp (hle ha)).symm

theorem sq_of_mem_B {b : X} (hb : b ∈ S.B) : b ^ 2 = 1 := (elemAbelianTwo_B S).sq_eq_one b hb

theorem mem_TE_iff {g : X} : g ∈ S.TE ↔ g ∈ A.T ∧ ∀ b ∈ S.B, b * g = g * b := by
  rw [KDBase.TE, mem_inf, mem_centralizer_iff]
  rfl

theorem mem_TE_of_comm_k {g : X} (hg : g ∈ A.T) (hk : g * S.k = S.k * g) : g ∈ S.TE := by
  refine (mem_TE_iff S).mpr ⟨hg, fun b hb => ?_⟩
  have hle : S.B ≤ centralizer ({g} : Set X) := by
    rw [B_eq]
    refine sup_le (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_) <;>
      rw [mem_centralizer_singleton_iff]
    · exact (z_comm_T S hg).symm
    · exact (A.commute_t hg).symm
    · exact hk.symm
  exact mem_centralizer_singleton_iff.mp (hle hb)

theorem exists_eq_of_mem_TE {g : X} (hg : g ∈ S.TE) :
    ∃ r ∈ A.R, ∃ a e : ℕ, a < 2 ∧ e < 2 ∧ g = r * t ^ a * S.k ^ e := by
  have hgT : g ∈ A.T := ((mem_TE_iff S).mp hg).1
  have hgk : S.k * g = g * S.k := ((mem_TE_iff S).mp hg).2 S.k (Frame.k_mem_B)
  obtain ⟨u, b, hub⟩ := L2KD.ψX_mem_H8 (A := A) hgT
  rcases L2KD.dbit8_eq b with hb | hb
  · obtain ⟨r, hr, a, e, ha, he, hg', -⟩ := L2KD.exists_eq_of_mem_T C hgT hub.symm hb
    exact ⟨r, hr, a, e, ha, he, hg'⟩
  · exfalso
    apply aff8_comm_k8 u b hb
    have hgk' : C.k * g = g * C.k := hgk
    have h1 : g * C.k * g⁻¹ * C.k⁻¹ = 1 := by rw [← hgk']; group
    have h2 := L2K.ψX_comm hgT C.k_mem
    rw [h1, L2K.ψX_one, ← hub, L2KD.ψX_k C] at h2
    exact h2.symm

theorem TE_eq : S.TE = A.R ⊔ S.B := by
  apply le_antisymm
  · intro g hg
    obtain ⟨r, hr, a, e, -, -, rfl⟩ := exists_eq_of_mem_TE S hg
    exact mul_mem (mul_mem (mem_sup_left hr) (pow_mem (mem_sup_right Frame.t_mem_B) a))
      (pow_mem (mem_sup_right Frame.k_mem_B) e)
  · refine sup_le (fun r hr => (mem_TE_iff S).mpr ⟨hr.1, fun b hb => B_comm_R S hb hr⟩)
      (fun b hb => (mem_TE_iff S).mpr ⟨B_le_T S hb, fun c hc => B_comm_B S hc hb⟩)

theorem R_le_TE : A.R ≤ S.TE := by rw [TE_eq]; exact le_sup_left

theorem B_le_TE : S.B ≤ S.TE := by rw [TE_eq]; exact le_sup_right

theorem TE_le_T : S.TE ≤ A.T := inf_le_left

theorem central_of_mem_B {b g : X} (hb : b ∈ S.B) (hg : g ∈ S.TE) : b * g = g * b :=
  ((mem_TE_iff S).mp hg).2 b hb

theorem commutator_TE {g h : X} (hg : g ∈ S.TE) (hh : h ∈ S.TE) :
    g * h * g⁻¹ * h⁻¹ = 1 ∨ g * h * g⁻¹ * h⁻¹ = S.z := by
  obtain ⟨r, hr, a, e, -, -, rfl⟩ := exists_eq_of_mem_TE S hg
  obtain ⟨r', hr', a', e', -, -, rfl⟩ := exists_eq_of_mem_TE S hh
  have hb : t ^ a * S.k ^ e ∈ S.B := mul_mem (pow_mem Frame.t_mem_B a) (pow_mem Frame.k_mem_B e)
  have hb' : t ^ a' * S.k ^ e' ∈ S.B :=
    mul_mem (pow_mem Frame.t_mem_B a') (pow_mem Frame.k_mem_B e')
  have hc : r * t ^ a * S.k ^ e * (r' * t ^ a' * S.k ^ e') * (r * t ^ a * S.k ^ e)⁻¹ *
      (r' * t ^ a' * S.k ^ e')⁻¹ = r * r' * r⁻¹ * r'⁻¹ := by
    have h1 : r * t ^ a * S.k ^ e = r * (t ^ a * S.k ^ e) := by group
    have h2 : r' * t ^ a' * S.k ^ e' = r' * (t ^ a' * S.k ^ e') := by group
    rw [h1, h2]
    set β := t ^ a * S.k ^ e
    set β' := t ^ a' * S.k ^ e'
    have e1 : β * r' = r' * β := B_comm_R S hb hr'
    have e2 : β' * r = r * β' := B_comm_R S hb' hr
    have e3 : β * β' = β' * β := B_comm_B S hb hb'
    calc r * β * (r' * β') * (r * β)⁻¹ * (r' * β')⁻¹ =
        r * (β * r') * β' * β⁻¹ * r⁻¹ * β'⁻¹ * r'⁻¹ := by group
      _ = r * r' * (β * β') * β⁻¹ * r⁻¹ * β'⁻¹ * r'⁻¹ := by rw [e1]; group
      _ = r * r' * (β' * β) * β⁻¹ * r⁻¹ * β'⁻¹ * r'⁻¹ := by rw [e3]
      _ = r * r' * (β' * r⁻¹) * β'⁻¹ * r'⁻¹ := by group
      _ = r * r' * r⁻¹ * r'⁻¹ := by
        rw [show β' * r⁻¹ = r⁻¹ * β' by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e2, mul_assoc, mul_inv_cancel, mul_one]]
        group
  rw [hc]
  have hm : r * r' * r⁻¹ * r'⁻¹ ∈ A.R :=
    mul_mem (mul_mem (mul_mem hr hr') (inv_mem hr)) (inv_mem hr')
  rcases L2K.comm_mem_R8 (L2K.ψX_mem_R8 hr) (L2K.ψX_mem_R8 hr') with h | h
  · left
    refine L2K.eq_one_of_ψX hm ?_
    rw [L2K.ψX_comm hr.1 hr'.1, h]
  · right
    refine L2K.eq_of_ψX_eq hm (z_mem_R S) ?_
    rw [L2K.ψX_comm hr.1 hr'.1, h, ψX_z S]

theorem mem_TE_of_comm_refl {r g : X} (h : IsRefl S r) (hg : g ∈ A.T) (hgr : g * r = r * g) :
    g ∈ S.TE := by
  obtain ⟨u, c, huc⟩ := L2KD.ψX_mem_H8 (A := A) hg
  obtain ⟨e, he, hψr⟩ := h.ψX
  have hc : aff8 u c * aff8 (-1) e = aff8 (-1) e * aff8 u c := by
    rw [huc, ← hψr, ← L2K.ψX_mul hg h.mem.1, ← L2K.ψX_mul h.mem.1 hg, hgr]
  obtain ⟨s, hs, a, e', -, -, rfl, -⟩ :=
    L2KD.exists_eq_of_mem_T C hg huc.symm (aff8_comm_refl_even u c e he hc)
  refine mul_mem (mul_mem (R_le_TE S hs) (pow_mem (B_le_TE S Frame.t_mem_B) a))
    (pow_mem (B_le_TE S Frame.k_mem_B) e')

theorem mem_E_of_comm {r g : X} (h : IsRefl S r) (hg : g ∈ S.TE) (hgr : g * r = r * g) :
    g ∈ S.E r := by
  obtain ⟨s, hs, a, e, -, -, rfl⟩ := exists_eq_of_mem_TE S hg
  have hb : t ^ a * S.k ^ e ∈ S.B := mul_mem (pow_mem Frame.t_mem_B a) (pow_mem Frame.k_mem_B e)
  have hbE : t ^ a * S.k ^ e ∈ S.E r :=
    mul_mem (pow_mem (Frame.t_mem_E r) a) (pow_mem (Frame.k_mem_E r) e)
  have hsr : s * r = r * s := by
    have e1 : (t ^ a * S.k ^ e) * r = r * (t ^ a * S.k ^ e) := B_comm_R S hb h.mem
    have e2 : s * (t ^ a * S.k ^ e) * r = r * s * (t ^ a * S.k ^ e) := by
      rw [show s * t ^ a * S.k ^ e * r = s * (t ^ a * S.k ^ e) * r by group] at hgr
      rw [hgr]; group
    rw [mul_assoc, e1, ← mul_assoc] at e2
    exact mul_right_cancel e2
  have hsE : s ∈ S.E r := by
    obtain ⟨u, c, hu, hψs⟩ := L2K.ψX_mem_R8 (A := A) hs
    obtain ⟨e', he', hψr⟩ := h.ψX
    have hc : aff8 u (2 * c) * aff8 (-1) e' = aff8 (-1) e' * aff8 u (2 * c) := by
      rw [hψs, ← hψr, ← L2K.ψX_mul hs.1 h.mem.1, ← L2K.ψX_mul h.mem.1 hs.1, hsr]
    rcases R8_comm_refl hu he' hc with h1 | h1 | h1 | h1 <;> rw [hψs] at h1
    · rw [L2K.eq_one_of_ψX hs h1]; exact one_mem _
    · rw [L2K.eq_of_ψX_eq hs (z_mem_R S) (h1.trans (ψX_z S).symm)]; exact Frame.z_mem_E r
    · rw [L2K.eq_of_ψX_eq hs h.mem (h1.trans hψr.symm)]; exact Frame.yi_mem_E r
    · rw [L2K.eq_of_ψX_eq hs (mul_mem (z_mem_R S) h.mem)
        (by rw [h1, L2K.ψX_mul (z_mem_T S) h.mem.1, ψX_z S, hψr])]
      exact mul_mem (Frame.z_mem_E r) (Frame.yi_mem_E r)
  rw [show s * t ^ a * S.k ^ e = s * (t ^ a * S.k ^ e) by group]
  exact mul_mem hsE hbE

theorem mem_T_of_mem_T₁ {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {g : X} (hg : g ∈ T₁)
    (hgt : g * t = t * g) : g ∈ A.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := A.T ⊔ zpowers g with hH
  have hHT₁ : H ≤ T₁ := sup_le h4.le (zpowers_le.mpr hg)
  have hHC : H ≤ centralizer ({t} : Set X) :=
    sup_le A.T_le_centralizer (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hgt))
  have hP : IsPGroup 2 H := h4.isPGroup.to_le hHT₁
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcard := L2K.card_T_eq_of_le (A := A) (le_sup_left : A.T ≤ H) hHC
  rw [hn, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at hcard
  have heq : A.T = H := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard, hn])
  rw [heq]
  exact mem_sup_right (mem_zpowers g)

theorem mem_TE_of_mem_T₁ {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {g : X} (hg : g ∈ T₁)
    (hgt : g * t = t * g) (hgk : g * S.k = S.k * g) : g ∈ S.TE :=
  mem_TE_of_comm_k S (mem_T_of_mem_T₁ S h4 hg hgt) hgk

theorem mem_E_of_mem_T₁ {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {r g : X} (h : IsRefl S r)
    (hg : g ∈ T₁) (hgt : g * t = t * g) (hgr : g * r = r * g) : g ∈ S.E r :=
  mem_E_of_comm S h (mem_TE_of_comm_refl S h (mem_T_of_mem_T₁ S h4 hg hgt) hgr) hgr

variable {S} in
@[expose] def frameOf {r ki : X} (h : IsRefl S r) (hk : ki = S.k ∨ ki = S.z * S.k) :
    Frame S where
  xF := S.x
  yF := r
  kF := ki
  xF_mem := S.x_mem
  yF_mem := h.mem
  xF_sq := rfl
  yF_sq := h.sq
  yF_inv := h.inv
  kF_eq := hk

end KD8ab

end CFSG.ComponentClassification.HSFLit
