module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAS4
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM5

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

section Generic

variable {X : Type} [Group X]

theorem fixMod_mul {ζ y g₁ g₂ : X} (hζ : ζ * ζ = 1) (hζ₁ : g₁ * ζ * g₁⁻¹ = ζ)
    (h₁ : g₁ * y * g₁⁻¹ = y ∨ g₁ * y * g₁⁻¹ = ζ * y)
    (h₂ : g₂ * y * g₂⁻¹ = y ∨ g₂ * y * g₂⁻¹ = ζ * y) :
    g₁ * g₂ * y * (g₁ * g₂)⁻¹ = y ∨ g₁ * g₂ * y * (g₁ * g₂)⁻¹ = ζ * y := by
  rw [show g₁ * g₂ * y * (g₁ * g₂)⁻¹ = g₁ * (g₂ * y * g₂⁻¹) * g₁⁻¹ by group]
  rcases h₂ with h | h <;> rw [h]
  · exact h₁
  · rw [show g₁ * (ζ * y) * g₁⁻¹ = (g₁ * ζ * g₁⁻¹) * (g₁ * y * g₁⁻¹) by group, hζ₁]
    rcases h₁ with h' | h' <;> rw [h']
    · exact Or.inr rfl
    · left; rw [← mul_assoc, hζ, one_mul]

theorem conj_of_comm {g y : X} (h : g * y = y * g) : g * y * g⁻¹ = y := by
  rw [h, mul_inv_cancel_right]

theorem comm_of_conj' {g y : X} (h : g * y * g⁻¹ = y) : g * y = y * g := by
  calc g * y = g * y * g⁻¹ * g := by group
    _ = y * g := by rw [h]

end Generic

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

theorem ι_ne (H : AD S T₁) {a b : MA} (h : a ≠ b) : H.ι a ≠ H.ι b :=
  fun h' => h (H.ι_injective h')

theorem ι_comm_z (H : AD S T₁) (a : MA) : H.ι a * H.ι MA.z = H.ι MA.z * H.ι a := by
  rw [← map_mul, ← map_mul, (zk_central MA.z (by simp [MA.ZList]) a).symm]

theorem ι_comm_k (H : AD S T₁) (a : MA) : H.ι a * H.ι MA.k = H.ι MA.k * H.ι a := by
  rw [← map_mul, ← map_mul, (zk_central MA.k (by simp [MA.ZList]) a).symm]

theorem ι_conj_w₁ (H : AD S T₁) (a : MA) : H.ι a * H.ι MA.w₁ * (H.ι a)⁻¹ = H.ι MA.w₁ ∨
    H.ι a * H.ι MA.w₁ * (H.ι a)⁻¹ = H.ι MA.z * H.ι MA.w₁ := by
  rcases conj_w₁_all a with h | h
  · left; simpa only [map_mul, map_inv] using congrArg H.ι h
  · right; simpa only [map_mul, map_inv] using congrArg H.ι h

theorem ι_z_sq (H : AD S T₁) : H.ι MA.z * H.ι MA.z = 1 := by
  rw [← map_mul, zkw_facts.1, map_one]

namespace TD

variable {H : AD S T₁} (T : H.TD)

theorem t_mem_T₂ : t ∈ T.T₂ := by
  have h := T.ι_mem_R₂ MA.t
  rw [H.ι_t] at h
  exact T.R₂_le_T₂ h

theorem T₂_cases {g : X} (hg : g ∈ T.T₂) : ∃ a : MA, ∃ i j : Bool,
    g = H.ι a * (if i then T.p else 1) * (if j then T.d else 1) := by
  have hR : ∀ r ∈ T.R₂, ∃ a : MA, ∃ i : Bool, r = H.ι a * (if i then T.p else 1) := by
    intro r hr
    rcases T.mem_R₂ hr with h | h
    · obtain ⟨a, ha⟩ := H.mem_range_of_mem_S₁ h
      exact ⟨a, false, by simp only [Bool.false_eq_true, ↓reduceIte, mul_one, ha]⟩
    · obtain ⟨a, ha⟩ := H.mem_range_of_mem_S₁ h
      exact ⟨a, true, by simp only [↓reduceIte, ha, inv_mul_cancel_right]⟩
  rcases T.mem_T₂ hg with h | h
  · obtain ⟨a, i, hr⟩ := hR g h
    exact ⟨a, i, false, by simp only [Bool.false_eq_true, ↓reduceIte, mul_one, ← hr]⟩
  · obtain ⟨a, i, hr⟩ := hR _ h
    exact ⟨a, i, true, by simp only [↓reduceIte, ← hr, inv_mul_cancel_right]⟩

theorem Tp_cases {g : X} (hg : g ∈ T.Tp) : ∃ a : MA, g = H.ι a ∨ g = H.ι a * T.d := by
  rcases Sec7.mem_or_of_mem_sup_zpowers T.d_mem_normalizer_Ct
    (by rw [pow_two]; exact T.d_sq_mem_Ct) hg with ⟨a, -, ha⟩ | ⟨a, -, ha⟩
  · exact ⟨a, Or.inl ha.symm⟩
  · exact ⟨a, Or.inr (by rw [ha, inv_mul_cancel_right])⟩

theorem p_conj_z : T.p * H.ι MA.z * T.p⁻¹ = H.ι MA.z := T.actsW.2.2.2.1

theorem p_conj_k : T.p * H.ι MA.k * T.p⁻¹ = H.ι MA.k := T.actsW.2.2.2.2.1

theorem p_conj_w₁ : T.p * H.ι MA.w₁ * T.p⁻¹ = H.ι MA.w₁ := T.actsW.2.2.2.2.2.1

theorem d_conj_z : T.d * H.ι MA.z * T.d⁻¹ = H.ι MA.z := by
  rw [← T.conj MA.z (by decide +kernel), dc_z]

theorem d_conj_k : T.d * H.ι MA.k * T.d⁻¹ = H.ι MA.z * H.ι MA.k := by
  rw [← T.conj MA.k (by decide +kernel), dc_k, map_mul]

theorem d_conj_w₁ (he : T.e = false) : T.d * H.ι MA.w₁ * T.d⁻¹ = H.ι MA.w₁ :=
  conj_of_comm (T.d_comm_w₁ he)

theorem T₂_le_C_z : T.T₂ ≤ centralizer ({H.ι MA.z} : Set X) := by
  have hc : ∀ g : X, g * H.ι MA.z * g⁻¹ = H.ι MA.z → g ∈ centralizer ({H.ι MA.z} : Set X) :=
    fun g h => mem_centralizer_singleton_iff.mpr (comm_of_conj' h)
  show (H.G.D₁.S₁ ⊔ zpowers T.p) ⊔ zpowers T.d ≤ _
  refine sup_le (sup_le ?_ (zpowers_le.mpr (hc _ T.p_conj_z))) (zpowers_le.mpr (hc _ T.d_conj_z))
  rw [← H.range_ι]
  rintro _ ⟨a, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (H.ι_comm_z a)

theorem conj_z {g : X} (hg : g ∈ T.T₂) : g * H.ι MA.z * g⁻¹ = H.ι MA.z :=
  conj_of_comm (mem_centralizer_singleton_iff.mp (T.T₂_le_C_z hg))

theorem R₂_le_C_k : T.R₂ ≤ centralizer ({H.ι MA.k} : Set X) := by
  show H.G.D₁.S₁ ⊔ zpowers T.p ≤ _
  refine sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
    (comm_of_conj' T.p_conj_k)))
  rw [← H.range_ι]
  rintro _ ⟨a, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (H.ι_comm_k a)

theorem fix_T₂ {y : X}
    (ha : ∀ a : MA, H.ι a * y * (H.ι a)⁻¹ = y ∨ H.ι a * y * (H.ι a)⁻¹ = H.ι MA.z * y)
    (hp : T.p * y * T.p⁻¹ = y ∨ T.p * y * T.p⁻¹ = H.ι MA.z * y)
    (hd : T.d * y * T.d⁻¹ = y ∨ T.d * y * T.d⁻¹ = H.ι MA.z * y) {g : X} (hg : g ∈ T.T₂) :
    g * y * g⁻¹ = y ∨ g * y * g⁻¹ = H.ι MA.z * y := by
  obtain ⟨a, i, j, rfl⟩ := T.T₂_cases hg
  have hP : (if i then T.p else 1) * y * (if i then T.p else 1)⁻¹ = y ∨
      (if i then T.p else 1) * y * (if i then T.p else 1)⁻¹ = H.ι MA.z * y := by
    cases i
    · left; simp only [Bool.false_eq_true, ↓reduceIte, one_mul, inv_one, mul_one]
    · simpa only [↓reduceIte] using hp
  have hD : (if j then T.d else 1) * y * (if j then T.d else 1)⁻¹ = y ∨
      (if j then T.d else 1) * y * (if j then T.d else 1)⁻¹ = H.ι MA.z * y := by
    cases j
    · left; simp only [Bool.false_eq_true, ↓reduceIte, one_mul, inv_one, mul_one]
    · simpa only [↓reduceIte] using hd
  have haT : H.ι a ∈ T.T₂ := T.R₂_le_T₂ (T.ι_mem_R₂ a)
  have hmem : H.ι a * (if i then T.p else 1) ∈ T.T₂ := by
    refine mul_mem haT ?_
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact one_mem _
    · simp only [↓reduceIte]; exact T.R₂_le_T₂ T.p_mem_R₂
  exact fixMod_mul H.ι_z_sq (T.conj_z hmem) (fixMod_mul H.ι_z_sq (T.conj_z haT) (ha a) hP) hD

theorem conj_w₁ (he : T.e = false) {g : X} (hg : g ∈ T.T₂) :
    g * H.ι MA.w₁ * g⁻¹ = H.ι MA.w₁ ∨ g * H.ι MA.w₁ * g⁻¹ = H.ι MA.z * H.ι MA.w₁ :=
  T.fix_T₂ H.ι_conj_w₁ (Or.inl T.p_conj_w₁) (Or.inl (T.d_conj_w₁ he)) hg

theorem conj_k {g : X} (hg : g ∈ T.T₂) :
    g * H.ι MA.k * g⁻¹ = H.ι MA.k ∨ g * H.ι MA.k * g⁻¹ = H.ι MA.z * H.ι MA.k :=
  T.fix_T₂ (fun a => Or.inl (conj_of_comm (H.ι_comm_k a))) (Or.inl T.p_conj_k)
    (Or.inr T.d_conj_k) hg

theorem not_w₂_fix {a : MA} {c : X} (hc : c = 1 ∨ c = H.ι MA.z)
    (h : H.ι MA.w₂ * (H.ι a * T.d) * (H.ι MA.w₂)⁻¹ = c * (H.ι a * T.d)) : False := by
  have e : H.ι MA.w₂ * (H.ι a * T.d) * (H.ι MA.w₂)⁻¹ = H.ι (MA.w₂ * a) * T.p⁻¹ * T.d := by
    rw [p, map_mul]; group
  rw [e] at h
  have hcS : c ∈ H.G.D₁.S₁ := by
    rcases hc with rfl | rfl
    · exact one_mem _
    · exact H.ι_mem_S₁ _
  have h1 : T.p⁻¹ = (H.ι (MA.w₂ * a))⁻¹ * c * H.ι a := by
    calc T.p⁻¹ = (H.ι (MA.w₂ * a))⁻¹ * (H.ι (MA.w₂ * a) * T.p⁻¹ * T.d) * T.d⁻¹ := by group
      _ = (H.ι (MA.w₂ * a))⁻¹ * (c * (H.ι a * T.d)) * T.d⁻¹ := by rw [h]
      _ = (H.ι (MA.w₂ * a))⁻¹ * c * H.ι a := by group
  apply T.p_not_mem_S₁
  have := inv_mem (mul_mem (mul_mem (inv_mem (H.ι_mem_S₁ (MA.w₂ * a))) hcS) (H.ι_mem_S₁ a))
  rwa [← h1, inv_inv] at this

theorem center_T₂ {g : X} (hg : g ∈ T.T₂) (hc : ∀ h ∈ T.T₂, g * h = h * g) :
    g = 1 ∨ g = H.ι MA.z := by
  obtain ⟨a, ha | ha⟩ := T.Tp_cases (T.mem_Tp_of_comm_t hg (hc t T.t_mem_T₂))
  · subst ha
    have hcen : ∀ b ∈ MA.gens, b * a = a * b := fun b _ => H.ι_injective (by
      rw [map_mul, map_mul]; exact (hc _ (T.R₂_le_T₂ (T.ι_mem_R₂ b))).symm)
    have haZ : a ∈ MA.ZList := by
      rcases MA.center_cases a hcen with rfl | rfl | rfl | rfl <;> simp [MA.ZList]
    have hd : dc T.e T.c₂ a = a := H.ι_injective (by
      rw [T.conj a (ZList_T1 a haZ), ← hc T.d T.d_mem_T₂, mul_inv_cancel_right])
    rcases dc_fix_zk T.e T.c₂ T.hc₂ a haZ hd with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · exfalso
    refine T.not_w₂_fix (a := a) (c := 1) (Or.inl rfl) ?_
    have := hc _ (T.R₂_le_T₂ (T.ι_mem_R₂ MA.w₂))
    rw [← ha, one_mul, ← this, mul_inv_cancel_right]

theorem Y_T₂ (he : T.e = false) {g : X} (hg : g ∈ T.T₂)
    (hY : ∀ h ∈ T.T₂, h * g * h⁻¹ = g ∨ h * g * h⁻¹ = H.ι MA.z * g) :
    g = 1 ∨ g = H.ι MA.z ∨ g = H.ι MA.k ∨ g = H.ι MA.z * H.ι MA.k ∨ g = H.ι MA.w₁ ∨
      g = H.ι MA.z * H.ι MA.w₁ ∨ g = H.ι MA.k * H.ι MA.w₁ ∨
      g = H.ι MA.z * H.ι MA.k * H.ι MA.w₁ := by
  obtain ⟨a, ha⟩ : ∃ a : MA, g = H.ι a ∨ g = H.ι a * T.d := by
    rcases hY t T.t_mem_T₂ with h | h
    · exact T.Tp_cases (T.mem_Tp_of_comm_t hg (comm_of_conj' h).symm)
    · have htw : t * H.ι MA.w₁ * t⁻¹ = H.ι MA.z * H.ι MA.w₁ := by
        simpa only [map_mul, map_inv, H.ι_t] using congrArg H.ι t_conj_w₁
      have e1 : t * (H.ι MA.w₁ * g) * t⁻¹ = H.ι MA.w₁ * g := by
        rw [show t * (H.ι MA.w₁ * g) * t⁻¹ = (t * H.ι MA.w₁ * t⁻¹) * (t * g * t⁻¹) by group,
          htw, h, show H.ι MA.z * H.ι MA.w₁ * (H.ι MA.z * g) =
            H.ι MA.w₁ * (H.ι MA.z * H.ι MA.z) * g by rw [← H.ι_comm_z MA.w₁]; group,
          H.ι_z_sq, mul_one]
      obtain ⟨a, ha⟩ := T.Tp_cases (T.mem_Tp_of_comm_t
        (mul_mem (T.R₂_le_T₂ (T.ι_mem_R₂ _)) hg) (comm_of_conj' e1).symm)
      refine ⟨MA.w₁⁻¹ * a, ?_⟩
      rcases ha with ha | ha
      · left; rw [map_mul, map_inv, ← ha]; group
      · right; rw [map_mul, map_inv, mul_assoc, ← ha]; group
  rcases ha with rfl | rfl
  swap
  · exfalso
    rcases hY _ (T.R₂_le_T₂ (T.ι_mem_R₂ MA.w₂)) with h | h
    · exact T.not_w₂_fix (Or.inl rfl) (by rw [h, one_mul])
    · exact T.not_w₂_fix (Or.inr rfl) h
  have hgen : ∀ b ∈ MA.gens, b * a * b⁻¹ = a ∨ b * a * b⁻¹ = MA.z * a := by
    intro b _
    rcases hY _ (T.R₂_le_T₂ (T.ι_mem_R₂ b)) with h | h
    · left; apply H.ι_injective; rw [map_mul, map_mul, map_inv, h]
    · right; apply H.ι_injective; rw [map_mul, map_mul, map_inv, h, map_mul]
  obtain ⟨haT, hfin⟩ := z2_conj T.c₂ T.hc₂ a hgen
  have hd : dc T.e T.c₂ a = a ∨ dc T.e T.c₂ a = MA.z * a := by
    rcases hY _ T.d_mem_T₂ with h | h
    · left; apply H.ι_injective; rw [T.conj a haT, h]
    · right; apply H.ι_injective; rw [T.conj a haT, h, map_mul]
  have hp : pAct T.e T.c₂ a = a ∨ pAct T.e T.c₂ a = MA.z * a := by
    rcases hY _ (T.R₂_le_T₂ T.p_mem_R₂) with h | h
    · left; apply H.ι_injective; rw [← T.p_conj_ι haT, h]
    · right; apply H.ι_injective; rw [← T.p_conj_ι haT, h, map_mul]
  rw [he] at hd hp
  have h8 := hfin hd hp
  simp only [Z2List, List.mem_cons, List.not_mem_nil, or_false] at h8
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_mul, map_one, true_or, or_true]

theorem fus_T₂ (he : T.e = false) {x : X} (hx : x ∈ T.T₂) (hc : ConjTo t x) :
    (∃ g ∈ T.T₂, x = g * t * g⁻¹) ∨ (x * H.ι MA.k * x⁻¹ = H.ι MA.z * H.ι MA.k ∧
      x * H.ι MA.w₁ * x⁻¹ = H.ι MA.z * H.ι MA.w₁) := by
  by_cases hxR : x ∈ T.R₂
  · obtain ⟨r, hr, hxr⟩ := T.exists_conj_R₂ hxR hc
    exact Or.inl ⟨r, T.R₂_le_T₂ hr, hxr⟩
  · right
    have hr : x * T.d⁻¹ ∈ T.R₂ := (T.mem_T₂ hx).resolve_left hxR
    refine ⟨?_, ?_⟩
    · have hk := conj_of_comm (mem_centralizer_singleton_iff.mp (T.R₂_le_C_k hr))
      have hz := T.conj_z (T.R₂_le_T₂ hr)
      calc x * H.ι MA.k * x⁻¹ = (x * T.d⁻¹) * (T.d * H.ι MA.k * T.d⁻¹) * (x * T.d⁻¹)⁻¹ := by
            group
        _ = (x * T.d⁻¹) * H.ι MA.z * (x * T.d⁻¹)⁻¹ *
            ((x * T.d⁻¹) * H.ι MA.k * (x * T.d⁻¹)⁻¹) := by rw [T.d_conj_k]; group
        _ = H.ι MA.z * H.ι MA.k := by rw [hz, hk]
    · rcases T.conj_w₁ he hx with h | h
      · exact absurd hc (T.not_conjTo_U₁ he hx (comm_of_conj' h))
      · exact h

theorem nonempty_spkg (he : T.e = false) : Nonempty (SPkg A) := by
  obtain ⟨hzz, hkk, hww, hkw, hz1, hk1, hkz, hw1, hwz, hwk, hwzk⟩ := zkw_facts
  have hne1 : ∀ {a : MA}, a ≠ 1 → H.ι a ≠ 1 := fun h h' =>
    h (H.ι_injective (h'.trans (map_one H.ι).symm))
  have hmem : ∀ a : MA, H.ι a ∈ T.T₂ := fun a => T.R₂_le_T₂ (T.ι_mem_R₂ a)
  exact ⟨{
    T₂ := T.T₂
    Tp := T.Tp
    z := H.ι MA.z
    k := H.ι MA.k
    w := H.ι MA.w₁
    isPGroup := T.isPGroup_T₂
    Tp_le := T.Tp_le_T₂
    Tp_le_C := T.Tp_le_centralizer
    card_T_le := T.card_T_le_Tp
    t_mem := T.t_mem_T₂
    z_mem := hmem _
    k_mem := hmem _
    w_mem := hmem _
    zz := by rw [← map_mul, hzz, map_one]
    kk := by rw [← map_mul, hkk, map_one]
    ww := by rw [← map_mul, hww, map_one]
    kw := by rw [← map_mul, ← map_mul, hkw]
    z_ne := hne1 hz1
    k_ne₁ := hne1 hk1
    k_ne_z := H.ι_ne hkz
    w_ne₁ := hne1 hw1
    w_ne_z := H.ι_ne hwz
    w_ne_k := H.ι_ne hwk
    w_ne_zk := by rw [← map_mul]; exact H.ι_ne hwzk
    z_central := fun g hg => mem_centralizer_singleton_iff.mp (T.T₂_le_C_z hg)
    center := fun g hg hc => T.center_T₂ hg hc
    conj_k := fun g hg => T.conj_k hg
    conj_w := fun g hg => T.conj_w₁ he hg
    Y := fun g hg hY => T.Y_T₂ he hg hY
    t_k := by simpa only [map_mul, map_inv, H.ι_t] using congrArg H.ι t_conj_k
    t_w := by simpa only [map_mul, map_inv, H.ι_t] using congrArg H.ι t_conj_w₁
    fus := fun x hx hc => T.fus_T₂ he hx hc
    noconj := fun x hx hxw => T.not_conjTo_U₁ he hx hxw }⟩

theorem false_of_e_false [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (he : T.e = false) :
    False := by
  obtain ⟨P⟩ := T.nonempty_spkg he
  exact P.false_of_simple hX A.orderOf_t

end TD

end AD

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
