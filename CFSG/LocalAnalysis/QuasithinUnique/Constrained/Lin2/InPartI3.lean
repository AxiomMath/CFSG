module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin MatrixGroups Matrix.SpecialLinearGroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem isElemAbelian_sup_of_commute {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian 2 (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

omit [Finite G] in
theorem commutatorElement_mul_central {p₁ p₂ c₁ c₂ : G} (h1 : c₁ * p₂ = p₂ * c₁)
    (h2 : c₁ * c₂ = c₂ * c₁) (h3 : c₂ * p₁ = p₁ * c₂) :
    ⁅p₁ * c₁, p₂ * c₂⁆ = ⁅p₁, p₂⁆ := by
  have e1' : c₁ * (p₂ * c₂) = (p₂ * c₂) * c₁ := by
    calc c₁ * (p₂ * c₂) = (c₁ * p₂) * c₂ := by group
      _ = (p₂ * c₁) * c₂ := by rw [h1]
      _ = p₂ * (c₁ * c₂) := by group
      _ = p₂ * (c₂ * c₁) := by rw [h2]
      _ = (p₂ * c₂) * c₁ := by group
  have e1 : c₁ * (p₂ * c₂) * c₁⁻¹ = p₂ * c₂ := by
    calc c₁ * (p₂ * c₂) * c₁⁻¹ = ((p₂ * c₂) * c₁) * c₁⁻¹ := by rw [e1']
      _ = p₂ * c₂ := by group
  have e2 : c₂ * p₁⁻¹ = p₁⁻¹ * c₂ := by
    calc c₂ * p₁⁻¹ = p₁⁻¹ * (p₁ * c₂) * p₁⁻¹ := by group
      _ = p₁⁻¹ * (c₂ * p₁) * p₁⁻¹ := by rw [h3]
      _ = p₁⁻¹ * c₂ := by group
  have e2' : c₂ * p₁⁻¹ * c₂⁻¹ = p₁⁻¹ := by
    calc c₂ * p₁⁻¹ * c₂⁻¹ = (p₁⁻¹ * c₂) * c₂⁻¹ := by rw [e2]
      _ = p₁⁻¹ := by group
  simp only [commutatorElement_def]
  calc p₁ * c₁ * (p₂ * c₂) * (p₁ * c₁)⁻¹ * (p₂ * c₂)⁻¹
      = p₁ * (c₁ * (p₂ * c₂) * c₁⁻¹) * p₁⁻¹ * (p₂ * c₂)⁻¹ := by group
    _ = p₁ * (p₂ * c₂) * p₁⁻¹ * (p₂ * c₂)⁻¹ := by rw [e1]
    _ = p₁ * p₂ * (c₂ * p₁⁻¹ * c₂⁻¹) * p₂⁻¹ := by group
    _ = p₁ * p₂ * p₁⁻¹ * p₂⁻¹ := by rw [e2']

theorem Lin2Data.commutator_R_le_P (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    ⁅thompsonJ S, thompsonJ S⁆ ≤ S ⊓ L := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨p₁, hp₁, c₁, hc₁, rfl⟩ := (dat.R_mem_iff h).1 hg₁
  obtain ⟨p₂, hp₂, c₂, hc₂, rfl⟩ := (dat.R_mem_iff h).1 hg₂
  have h1 : c₁ * p₂ = p₂ * c₁ := dat.D₀_comm hc₁ hp₂.2
  have h2 : c₁ * c₂ = c₂ * c₁ := IsElemAbelian.comm dat.D₀_elem hc₁ hc₂
  have h3 : c₂ * p₁ = p₁ * c₂ := dat.D₀_comm hc₂ hp₁.2
  rw [commutatorElement_mul_central h1 h2 h3, commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hp₁ hp₂)
    (Subgroup.inv_mem _ hp₁)) (Subgroup.inv_mem _ hp₂)

theorem slUpper_mulVec {F : Type} [Field F] (c : F) (v : Fin 2 → F) :
    (slUpper c : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + c * v 1, v 1] := by
  ext i
  fin_cases i <;> simp [slUpper_val, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Lin2Cfg.mem_commutator_of_central (h : Lin2Cfg G T M H S L n D)
    (dat : Lin2Data T M H S L n) (hZ : blockZ L = ⊥) {z : G} (hzU : z ∈ blockU L)
    (hzc : ∀ p ∈ S ⊓ L, z * p = p * z) : z ∈ ⁅S ⊓ L, S ⊓ L⁆ := by
  obtain ⟨F, _, _, ⟨A⟩⟩ := h.coord
  have hexP : ∀ c : F, ∃ q : L, (q : G) ∈ S ⊓ L ∧ A.α q = slUpper c := by
    intro c
    obtain ⟨q, hq⟩ := A.α_surj (slUpper c)
    exact ⟨q, (A.mem_P q).2 (hq ▸ slUpper_mem_slUni c), hq⟩
  have hβinj : Function.Injective A.β :=
    (MonoidHom.ker_eq_bot_iff A.β).1 (by rw [A.β_ker, hZ, Subgroup.bot_subgroupOf])
  set v : Fin 2 → F := Multiplicative.toAdd (A.β ⟨z, hzU⟩) with hv
  have hv1 : v 1 = 0 := by
    obtain ⟨q, hqP, hq⟩ := hexP 1
    have hcomm : (q : G) * z * (q : G)⁻¹ = z := by
      have := hzc q hqP
      rw [← this]
      exact mul_inv_cancel_right z (q : G)
    have h1 := A.toAdd_beta_conj q hzU
    have e : (⟨(q : G) * z * (q : G)⁻¹, mem_blockU_conj q.2 hzU⟩ : blockU L) = ⟨z, hzU⟩ :=
      Subtype.ext hcomm
    rw [e, hq, slUpper_mulVec] at h1
    have h2 := congrFun h1 0
    simp at h2
    exact h2
  obtain ⟨u', hu'⟩ := A.β_surj (Multiplicative.ofAdd ![0, 1])
  obtain ⟨q, hqP, hq⟩ := hexP (v 0)
  have hu'U : (u' : G) ∈ blockU L := u'.2
  have hu'P : (u' : G) ∈ S ⊓ L := dat.U_le_P h u'.2
  have hwU : (q : G) * u' * (q : G)⁻¹ * (u' : G)⁻¹ ∈ blockU L :=
    Subgroup.mul_mem _ (mem_blockU_conj q.2 hu'U) (Subgroup.inv_mem _ hu'U)
  have hzw : z = (q : G) * u' * (q : G)⁻¹ * (u' : G)⁻¹ := by
    have hb : Multiplicative.toAdd (A.β ⟨(q : G) * u' * (q : G)⁻¹, mem_blockU_conj q.2 hu'U⟩) =
        (A.α q : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (A.β u')) :=
      A.toAdd_beta_conj q hu'U
    have e : (⟨(q : G) * u' * (q : G)⁻¹ * (u' : G)⁻¹, hwU⟩ : blockU L) =
        ⟨(q : G) * u' * (q : G)⁻¹, mem_blockU_conj q.2 hu'U⟩ * u'⁻¹ := rfl
    have hcalc : Multiplicative.toAdd
        (A.β ⟨(q : G) * u' * (q : G)⁻¹ * (u' : G)⁻¹, hwU⟩) = v := by
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hb, hq, hu', toAdd_ofAdd, slUpper_mulVec]
      funext i
      fin_cases i
      · simp
      · simp [hv1]
    have hinj := hβinj (a₁ := ⟨z, hzU⟩) (a₂ := ⟨_, hwU⟩)
      (Multiplicative.toAdd.injective hcalc.symm)
    exact congrArg Subtype.val hinj
  rw [hzw]
  exact Subgroup.commutator_mem_commutator hqP hu'P

theorem Lin2Data.D₀_eq_bot_of_Z_bot (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D)
    (hZ : blockZ L = ⊥) : blockD S L = ⊥ := by
  by_contra hD₀
  have hcard := (dat.D₀_eq_bot_or_card h).resolve_left hD₀
  obtain ⟨x, hx, hxS⟩ := h.exists_mem_T_not_mem_S
  have hXP := dat.conjR_D₀_le_P h hx hxS
  have hxR := dat.x_normalizer_R h hx
  have hXcent : ∀ z ∈ conjR (blockD S L) x, ∀ r ∈ thompsonJ S, z * r = r * z := by
    intro z hz r hr
    have hz' : x * z * x⁻¹ ∈ blockD S L := mem_conjR.1 hz
    have hr' : x * r * x⁻¹ ∈ thompsonJ S := (Subgroup.mem_normalizer_iff.1 hxR r).1 hr
    have hc := dat.D₀_central h hz' hr'
    have h1 : x⁻¹ * ((x * z * x⁻¹) * (x * r * x⁻¹)) * x = z * r := by group
    have h2 : x⁻¹ * ((x * r * x⁻¹) * (x * z * x⁻¹)) * x = r * z := by group
    rw [← h1, ← h2, hc]
  have hXe : IsElemAbelian 2 (conjR (blockD S L) x) := (isElemAbelian_conjR_iff _ _).2 dat.D₀_elem
  have hQe : IsElemAbelian 2 (pCoreOf 2 H) := dat.Q_max.2.1
  have hQX : ∀ a ∈ pCoreOf 2 H, ∀ b ∈ conjR (blockD S L) x, a * b = b * a :=
    fun a ha b hb => (hXcent b hb a (dat.Q_le_R h ha)).symm
  have hE := isElemAbelian_sup_of_commute hQe hXe hQX
  have hES : pCoreOf 2 H ⊔ conjR (blockD S L) x ≤ S := sup_le h.Q_le_S (hXP.trans inf_le_left)
  have hcardle := dat.Q_max.2.2 _ hES hE
  have hXQ : conjR (blockD S L) x ≤ pCoreOf 2 H := by
    have hEQ : pCoreOf 2 H ⊔ conjR (blockD S L) x = pCoreOf 2 H :=
      (Subgroup.eq_of_le_of_card_ge le_sup_left hcardle).symm
    rw [← hEQ]
    exact le_sup_right
  have hUn : blockU L ≤ Subgroup.normalizer (blockD S L : Set G) :=
    le_normalizer_of_commute fun a ha b hb => dat.D₀_comm ha (blockU_le L hb)
  have hXU : conjR (blockD S L) x ≤ blockU L := by
    intro z hz
    have hzQ := hXQ hz
    rw [dat.Q_eq] at hzQ
    obtain ⟨c, hc, u, hu, rfl⟩ := (mem_sup_iff_of_le_normalizer hUn).1 hzQ
    have hcP : c ∈ S ⊓ L := by
      have h1 : c * u * u⁻¹ ∈ S ⊓ L :=
        Subgroup.mul_mem _ (hXP hz) (Subgroup.inv_mem _ (dat.U_le_P h hu))
      simpa using h1
    have hc1 : c ∈ (S ⊓ L) ⊓ blockD S L := ⟨hcP, hc⟩
    rw [dat.P_inf_D₀ h, hZ, Subgroup.mem_bot] at hc1
    rw [hc1, one_mul]
    exact hu
  have hXcomm : ∀ z ∈ conjR (blockD S L) x, z ∈ ⁅S ⊓ L, S ⊓ L⁆ := fun z hz =>
    h.mem_commutator_of_central dat hZ (hXU hz) fun p hp => hXcent z hz p (dat.P_le_R h hp)
  have hxN : x ∈ Subgroup.normalizer ((⁅thompsonJ S, thompsonJ S⁆ : Subgroup G) : Set G) := by
    rw [← conjR_eq_self_iff]
    have : conjR ⁅thompsonJ S, thompsonJ S⁆ x = ⁅conjR (thompsonJ S) x, conjR (thompsonJ S) x⁆ := by
      simp only [conjR_def]
      exact Subgroup.map_commutator _ _ _
    rw [this, conjR_eq_of_mem_normalizer hxR]
  have hD₀R : blockD S L ≤ ⁅thompsonJ S, thompsonJ S⁆ := by
    intro c hc
    have hz : x⁻¹ * c * x ∈ conjR (blockD S L) x := by
      rw [mem_conjR]
      have : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
      rw [this]
      exact hc
    have h1 : x⁻¹ * c * x ∈ ⁅thompsonJ S, thompsonJ S⁆ :=
      Subgroup.commutator_mono (dat.P_le_R h) (dat.P_le_R h) (hXcomm _ hz)
    have h2 := (Subgroup.mem_normalizer_iff.1 hxN (x⁻¹ * c * x)).1 h1
    have : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rwa [this] at h2
  have hD₀P : blockD S L ≤ S ⊓ L := hD₀R.trans (dat.commutator_R_le_P h)
  have hbot : blockD S L ≤ ⊥ := by
    rw [← hZ, ← dat.P_inf_D₀ h]
    exact le_inf hD₀P le_rfl
  exact hD₀ (le_bot_iff.1 hbot)

theorem Lin2Data.D₀_eq_Z (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    blockD S L = blockZ L := by
  by_cases hZ : blockZ L = ⊥
  · rw [hZ]
    exact dat.D₀_eq_bot_of_Z_bot h hZ
  · exact (dat.blockZ_eq_D₀ h hZ).1.symm

theorem Lin2Data.R_eq_P (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    thompsonJ S = S ⊓ L := by
  rw [dat.R_eq_sup h, dat.D₀_eq_Z h]
  exact sup_eq_left.2 ((blockZ_le_blockU L).trans (dat.U_le_P h))

theorem Lin2Data.R_le_L (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    thompsonJ S ≤ L := by
  rw [dat.R_eq_P h]
  exact inf_le_right

theorem Lin2Data.Q_eq_U (dat : Lin2Data T M H S L n) (h : Lin2Cfg G T M H S L n D) :
    pCoreOf 2 H = blockU L := by
  rw [dat.Q_eq, dat.D₀_eq_Z h]
  exact sup_eq_right.2 (blockZ_le_blockU L)

end CFSG.QuasithinUnique.Lin2
