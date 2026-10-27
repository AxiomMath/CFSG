module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7D

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer DihedralGroup

theorem conjTo_conj_iff {X : Type} [Group X] (t a g : X) :
    ConjTo t (g * a * g⁻¹) ↔ ConjTo t a := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨g⁻¹ * h, ?_⟩
    calc g⁻¹ * h * t * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * t * h⁻¹) * g := by group
      _ = a := by rw [hh]; group
  · rintro ⟨h, rfl⟩
    exact ⟨g * h, by group⟩

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

variable (Λ : A7Sigma S.t S.L S.data)

theorem elem_B : ElemAbelianTwo S.B :=
  ⟨fun _ ha _ hb => S.central_of_mem_B ha (S.B_le_T hb), fun _ ha => S.sq_of_mem_B ha⟩

theorem E_eq_B_sup (yi : X) : S.E yi = S.B ⊔ zpowers yi := by
  apply le_antisymm
  · rw [E, closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left (subset_closure (by simp))
    · exact mem_sup_left (subset_closure (by simp))
  · refine sup_le ?_ ?_
    · rw [B, closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> exact subset_closure (by simp)
    · rw [zpowers_le]
      exact subset_closure (by simp)

theorem card_E {yi : X} (hyi : yi ∈ S.data.R) (hyi2 : yi ^ 2 = 1) (hyiB : yi ∉ S.B) :
    Nat.card (S.E yi) = 16 := by
  rw [S.E_eq_B_sup]
  obtain ⟨-, -, h⟩ := S.elem_B.sup_zpowers hyi2 hyiB
    (fun a ha => (S.central_of_mem_B ha hyi.1).symm)
  rw [h, S.card_B]

theorem coords_xy : S.coords ⟨S.x * S.y, S.xy_mem.1⟩ = (sr 3, 1) := by
  have : (⟨S.x * S.y, S.xy_mem.1⟩ : S.data.T) = ⟨S.x, S.x_mem.1⟩ * ⟨S.y, S.y_mem.1⟩ := rfl
  rw [this, map_mul, S.coords_x, S.coords_y]
  rfl

theorem coords_prod {yi : X} (hyi : yi ∈ S.data.T) {s : DihedralGroup 4}
    (hs : S.coords ⟨yi, hyi⟩ = (s, 1)) (a b c d : ℕ)
    (hm : S.z ^ a * yi ^ b * S.t ^ c * S.k ^ d ∈ S.data.T) :
    S.coords ⟨S.z ^ a * yi ^ b * S.t ^ c * S.k ^ d, hm⟩ =
      ((r 2) ^ a * s ^ b, (r 1) ^ c * (sr 0) ^ d) := by
  have : (⟨S.z ^ a * yi ^ b * S.t ^ c * S.k ^ d, hm⟩ : S.data.T) =
      (⟨S.z, S.z_mem.1⟩ : S.data.T) ^ a * (⟨yi, hyi⟩ : S.data.T) ^ b *
        (⟨S.t, S.data.t_mem_T⟩ : S.data.T) ^ c * (⟨S.k, S.k_mem⟩ : S.data.T) ^ d := rfl
  rw [this, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, S.coords_z, hs,
    S.coords_t, S.coords_k]
  ext <;> simp

theorem y_not_mem_B : S.y ∉ S.B := by
  intro h
  have h1 := S.central_of_mem_B h S.x_mem.1
  have h2 := S.y_x_y
  rw [h1, mul_inv_cancel_right] at h2
  have h3 : S.x ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h2]; exact mul_inv_cancel _
  exact S.z_ne_one h3

theorem xy_not_mem_B : S.x * S.y ∉ S.B := by
  intro h
  have h1 := S.central_of_mem_B h S.y_mem.1
  have hyinv : S.y⁻¹ = S.y := by rw [inv_eq_iff_mul_eq_one, S.y_mul_y]
  have h2 : S.x = S.x⁻¹ := by
    calc S.x = S.x * S.y * S.y := by rw [mul_assoc, S.y_mul_y, mul_one]
      _ = S.y * (S.x * S.y) := h1
      _ = S.y * S.x * S.y⁻¹ := by rw [hyinv]; group
      _ = S.x⁻¹ := S.y_x_y
  have h3 : S.x ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h2]; exact mul_inv_cancel _
  exact S.z_ne_one h3

theorem mem_E_iff {yi : X} (hyi : yi ∈ S.data.R) (hyi2 : yi ^ 2 = 1) {s : DihedralGroup 4}
    (hs : S.coords ⟨yi, hyi.1⟩ = (s, 1)) {g : X} (hg : g ∈ S.data.T) :
    g ∈ S.E yi ↔ ∃ a b : Fin 2, (S.coords ⟨g, hg⟩).1 = (r 2) ^ (a : ℕ) * s ^ (b : ℕ) := by
  constructor
  · intro hgE
    obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E hyi hyi2 (S.z_comm_of_mem_T hyi.1) hgE
    exact ⟨a, b, by rw [S.coords_prod hyi.1 hs]⟩
  · rintro ⟨a, b, hab⟩
    obtain ⟨c, d, hcd⟩ : ∃ c d : Fin 2,
        (S.coords ⟨g, hg⟩).2 = (r 1) ^ (c : ℕ) * (sr 0) ^ (d : ℕ) := by
      generalize (S.coords ⟨g, hg⟩).2 = q
      revert q
      decide
    have hm : S.z ^ (a : ℕ) * yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ) ∈ S.data.T :=
      mul_mem (mul_mem (mul_mem (pow_mem S.z_mem.1 _) (pow_mem hyi.1 _)) (pow_mem S.data.t_mem_T _))
        (pow_mem S.k_mem _)
    have heq : (⟨g, hg⟩ : S.data.T) = ⟨_, hm⟩ := by
      apply S.coords.injective
      rw [S.coords_prod hyi.1 hs]
      ext
      · exact hab
      · exact hcd
    have hg' : g = S.z ^ (a : ℕ) * yi ^ (b : ℕ) * S.t ^ (c : ℕ) * S.k ^ (d : ℕ) :=
      congrArg Subtype.val heq
    rw [hg']
    exact mul_mem (mul_mem (mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)) (pow_mem (subset_closure (by simp)) _))
      (pow_mem (subset_closure (by simp)) _)

theorem eq_E_of_elem {E : Subgroup X} (hET : E ≤ S.data.T) (hE : ElemAbelianTwo E)
    (hcard : Nat.card E = 16) : E = S.E S.y ∨ E = S.E (S.x * S.y) := by
  have hy : ∀ g (hg : g ∈ S.data.T), (g ∈ S.E S.y ↔
      ∃ a b : Fin 2, (S.coords ⟨g, hg⟩).1 = (r 2) ^ (a : ℕ) * (sr 0) ^ (b : ℕ)) :=
    fun g hg => S.mem_E_iff S.y_mem S.y_sq S.coords_y hg
  have hxy : ∀ g (hg : g ∈ S.data.T), (g ∈ S.E (S.x * S.y) ↔
      ∃ a b : Fin 2, (S.coords ⟨g, hg⟩).1 = (r 2) ^ (a : ℕ) * (sr 3) ^ (b : ℕ)) :=
    fun g hg => S.mem_E_iff S.xy_mem S.xy_sq S.coords_xy hg
  have hsq : ∀ g (hg : g ∈ S.data.T), g ^ 2 = 1 → (S.coords ⟨g, hg⟩).1 ^ 2 = 1 := by
    intro g hg hg2
    have : (⟨g, hg⟩ : S.data.T) ^ 2 = 1 := Subtype.ext hg2
    have h := congrArg Prod.fst (congrArg S.coords this)
    rwa [map_pow, map_one, Prod.pow_fst] at h
  have hinv : ∀ g ∈ E, g ∈ S.E S.y ∨ g ∈ S.E (S.x * S.y) := by
    intro g hg
    have hgT := hET hg
    rw [hy g hgT, hxy g hgT]
    have h2 := hsq g hgT (hE.sq_eq_one g hg)
    generalize (S.coords ⟨g, hgT⟩).1 = p at h2 ⊢
    revert p
    decide
  by_cases hEy : ∀ g ∈ E, g ∈ S.E S.y
  · left
    exact Subgroup.eq_of_le_of_card_ge hEy
      (by rw [hcard, S.card_E S.y_mem S.y_sq S.y_not_mem_B])
  by_cases hExy : ∀ g ∈ E, g ∈ S.E (S.x * S.y)
  · right
    exact Subgroup.eq_of_le_of_card_ge hExy
      (by rw [hcard, S.card_E S.xy_mem S.xy_sq S.xy_not_mem_B])
  push Not at hEy hExy
  obtain ⟨a, ha, hay⟩ := hEy
  obtain ⟨b, hb, hbxy⟩ := hExy
  have haxy := (hinv a ha).resolve_left hay
  have hby := (hinv b hb).resolve_right hbxy
  have haT := hET ha
  have hbT := hET hb
  rw [hy a haT] at hay
  rw [hxy a haT] at haxy
  rw [hy b hbT] at hby
  rw [hxy b hbT] at hbxy
  have hab : (S.coords ⟨a, haT⟩).1 * (S.coords ⟨b, hbT⟩).1 =
      (S.coords ⟨b, hbT⟩).1 * (S.coords ⟨a, haT⟩).1 := by
    have : (⟨a, haT⟩ : S.data.T) * ⟨b, hbT⟩ = ⟨b, hbT⟩ * ⟨a, haT⟩ :=
      Subtype.ext (hE.comm a ha b hb)
    have h := congrArg Prod.fst (congrArg S.coords this)
    rwa [map_mul, map_mul, Prod.fst_mul, Prod.fst_mul] at h
  exfalso
  generalize (S.coords ⟨a, haT⟩).1 = p at hay haxy hab
  generalize (S.coords ⟨b, hbT⟩).1 = q at hby hbxy hab
  revert p q
  decide

theorem eq_k_or_tk_of_mem_E_xy {e : X} (he : e ∈ S.E (S.x * S.y))
    (h5 : numFixed (S.act Λ e) = 5) : e = S.k ∨ e = S.t * S.k := by
  obtain ⟨a, b, c, d, rfl⟩ := S.eq_of_mem_E S.xy_mem S.xy_sq (S.z_comm_of_mem_T S.xy_mem.1) he
  have hzC := S.data.T_le_centralizer S.z_mem.1
  have hxyC := S.data.T_le_centralizer S.xy_mem.1
  have hkC := S.data.T_le_centralizer S.k_mem
  rw [S.act_prod Λ hzC hxyC S.t_mem_centralizer hkC, S.act_z Λ, S.act_xy Λ, S.act_t Λ, one_pow,
    mul_one, S.act_k Λ] at h5
  have key : ∀ a b d : Fin 2, numFixed ((a0 ^ 2) ^ (a : ℕ) * (rho0 * (c0 * b0)) ^ (b : ℕ) *
      c0 ^ (d : ℕ)) = 5 → a = 0 ∧ b = 0 ∧ d = 1 := by decide
  obtain ⟨rfl, rfl, rfl⟩ := key a b d h5
  fin_cases c
  · left
    simp
  · right
    simp

theorem not_conj_E_y_E_xy_of_sigma (Λ : A7Sigma S.t S.L S.data) {g : X}
    (hg : g ∈ centralizer ({S.t} : Set X))
    (h : ∀ e ∈ S.E S.y, g * e * g⁻¹ ∈ S.E (S.x * S.y)) : False := by
  have hkC := S.data.T_le_centralizer S.k_mem
  have hyC := S.data.T_le_centralizer S.y_mem.1
  have hykC := mul_mem hyC hkC
  have hk5 : numFixed (S.act Λ (g * S.k * g⁻¹)) = 5 := by
    rw [S.act_conj Λ hg hkC, numFixed_conj, S.act_k Λ]
    decide
  have hyk5 : numFixed (S.act Λ (g * (S.y * S.k) * g⁻¹)) = 5 := by
    rw [S.act_conj Λ hg hykC, numFixed_conj, S.act_mul Λ hyC hkC, S.act_y Λ, S.act_k Λ]
    decide
  have h1 := S.eq_k_or_tk_of_mem_E_xy Λ (h _ (subset_closure (by simp))) hk5
  have h2 := S.eq_k_or_tk_of_mem_E_xy Λ
    (h _ (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))) hyk5
  have htk : S.t * S.k = S.k * S.t := (S.data.commute_t S.k_mem).symm
  have hk2 : S.k * S.k = 1 := by rw [← pow_two, S.k_sq]
  have ht2 : S.t * S.t = 1 := by rw [← pow_two, S.t_sq]
  have hgy : g * S.y * g⁻¹ = (g * (S.y * S.k) * g⁻¹) * (g * S.k * g⁻¹) := by
    calc g * S.y * g⁻¹ = g * (S.y * (S.k * S.k)) * g⁻¹ := by rw [hk2, mul_one]
      _ = _ := by group
  have hy1 : S.y ≠ 1 := fun h1 => S.y_not_mem_B (h1 ▸ one_mem _)
  have hyt : S.y ≠ S.t := fun h1 => S.data.t_not_mem_L (h1 ▸ S.y_mem.2)
  have hgt : g * S.t * g⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hg]
    group
  have hcases : g * S.y * g⁻¹ = 1 ∨ g * S.y * g⁻¹ = S.t := by
    rw [hgy]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2]
    · left; exact hk2
    · right
      calc S.t * S.k * S.k = S.t * (S.k * S.k) := by group
        _ = S.t := by rw [hk2, mul_one]
    · right
      calc S.k * (S.t * S.k) = S.k * (S.k * S.t) := by rw [htk]
        _ = S.t := by rw [← mul_assoc, hk2, one_mul]
    · left
      calc S.t * S.k * (S.t * S.k) = S.t * (S.k * S.t) * S.k := by group
        _ = S.t * (S.t * S.k) * S.k := by rw [htk]
        _ = 1 := by rw [← mul_assoc, ht2, one_mul, hk2]
  rcases hcases with h0 | h0
  · apply hy1
    calc S.y = g⁻¹ * (g * S.y * g⁻¹) * g := by group
      _ = 1 := by rw [h0]; group
  · apply hyt
    calc S.y = g⁻¹ * (g * S.y * g⁻¹) * g := by group
      _ = g⁻¹ * (g * S.t * g⁻¹) * g := by rw [h0, hgt]
      _ = S.t := by group


theorem not_conj_E_y_E_xy {g : X} (hg : g ∈ centralizer ({S.t} : Set X))
    (h : ∀ e ∈ S.E S.y, g * e * g⁻¹ ∈ S.E (S.x * S.y)) : False := by
  rcases S.facts with hF | hΛ
  · exact hF.not_conj hg h
  · obtain ⟨Λ⟩ := hΛ
    exact S.not_conj_E_y_E_xy_of_sigma Λ hg h
theorem conj_eq_of_mem_tk {g f : X} (hg : g ∈ centralizer ({S.t} : Set X))
    (hgk : g * S.k * g⁻¹ = S.k) (hf : f ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X)) :
    g * f * g⁻¹ = f := by
  have hgt : g * S.t * g⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hg]
    group
  rcases S.eq_of_mem_tk hf with rfl | rfl | rfl | rfl
  · group
  · exact hgt
  · exact hgk
  · calc g * (S.t * S.k) * g⁻¹ = (g * S.t * g⁻¹) * (g * S.k * g⁻¹) := by group
      _ = S.t * S.k := by rw [hgt, hgk]

theorem conjTo_xy_iff {f : X} (hf : f ∈ (zpowers S.t ⊔ zpowers S.k : Subgroup X)) :
    (ConjTo S.t (S.x * S.y * f) ↔ ConjTo S.t (S.z * f)) ∧
      (ConjTo S.t (S.z * (S.x * S.y) * f) ↔ ConjTo S.t (S.z * f)) := by
  obtain ⟨d, hdC, -, hdz, hdxy, hdk⟩ := S.exists_d_xy
  have hdf := S.conj_eq_of_mem_tk hdC hdk hf
  constructor
  · rw [← conjTo_conj_iff S.t (S.x * S.y * f) d⁻¹]
    have : d⁻¹ * (S.x * S.y * f) * d⁻¹⁻¹ = S.z * f := by
      have h1 : d⁻¹ * (S.x * S.y) * d = S.z := by rw [← hdz]; group
      have h2 : d⁻¹ * f * d = f := by
        calc d⁻¹ * f * d = d⁻¹ * (d * f * d⁻¹) * d := by rw [hdf]
          _ = f := by group
      calc d⁻¹ * (S.x * S.y * f) * d⁻¹⁻¹ = (d⁻¹ * (S.x * S.y) * d) * (d⁻¹ * f * d) := by group
        _ = S.z * f := by rw [h1, h2]
    rw [this]
  · rw [← conjTo_conj_iff S.t (S.z * (S.x * S.y) * f) d]
    have : d * (S.z * (S.x * S.y) * f) * d⁻¹ = S.z * f := by
      have hxy2 : S.x * S.y * (S.z * (S.x * S.y)) = S.z := by
        calc S.x * S.y * (S.z * (S.x * S.y)) = S.z * ((S.x * S.y) * (S.x * S.y)) := by
              rw [← mul_assoc, ← S.z_comm_of_mem_T S.xy_mem.1]; group
          _ = S.z := by rw [← pow_two, S.xy_sq, mul_one]
      calc d * (S.z * (S.x * S.y) * f) * d⁻¹
          = (d * S.z * d⁻¹) * (d * (S.x * S.y) * d⁻¹) * (d * f * d⁻¹) := by group
        _ = S.z * f := by rw [hdz, hdxy, hdf, hxy2]
    rw [this]

theorem conj_eq_of_mem_tzk {g f : X} (hg : g ∈ centralizer ({S.t} : Set X))
    (hgk : g * (S.z * S.k) * g⁻¹ = S.z * S.k)
    (hf : f = 1 ∨ f = S.t ∨ f = S.z * S.k ∨ f = S.t * (S.z * S.k)) : g * f * g⁻¹ = f := by
  have hgt : g * S.t * g⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hg]
    group
  rcases hf with rfl | rfl | rfl | rfl
  · group
  · exact hgt
  · exact hgk
  · calc g * (S.t * (S.z * S.k)) * g⁻¹ = (g * S.t * g⁻¹) * (g * (S.z * S.k) * g⁻¹) := by group
      _ = S.t * (S.z * S.k) := by rw [hgt, hgk]

theorem conjTo_y_iff {f : X} (hf : f = 1 ∨ f = S.t ∨ f = S.z * S.k ∨ f = S.t * (S.z * S.k)) :
    (ConjTo S.t (S.y * f) ↔ ConjTo S.t (S.z * f)) ∧
      (ConjTo S.t (S.z * S.y * f) ↔ ConjTo S.t (S.z * f)) := by
  obtain ⟨d, hdC, -, hdz, hdy, hdk⟩ := S.exists_d_y
  have hdf := S.conj_eq_of_mem_tzk hdC hdk hf
  have h2 : d⁻¹ * f * d = f := by
    calc d⁻¹ * f * d = d⁻¹ * (d * f * d⁻¹) * d := by rw [hdf]
      _ = f := by group
  constructor
  · rw [← conjTo_conj_iff S.t (S.y * f) d]
    have : d * (S.y * f) * d⁻¹ = S.z * f := by
      calc d * (S.y * f) * d⁻¹ = (d * S.y * d⁻¹) * (d * f * d⁻¹) := by group
        _ = S.z * f := by rw [hdy, hdf]
    rw [this]
  · rw [← conjTo_conj_iff S.t (S.z * S.y * f) d⁻¹]
    have : d⁻¹ * (S.z * S.y * f) * d⁻¹⁻¹ = S.z * f := by
      have h1 : d⁻¹ * (S.z * S.y) * d = S.z := by rw [← hdz]; group
      calc d⁻¹ * (S.z * S.y * f) * d⁻¹⁻¹ = (d⁻¹ * (S.z * S.y) * d) * (d⁻¹ * f * d) := by group
        _ = S.z * f := by rw [h1, h2]
    rw [this]

theorem exists_normalizer_conj_eq_t {yi : X} (hyi : yi = S.y ∨ yi = S.x * S.y)
    (hnot : ¬ SubConj (S.E S.y) (S.E (S.x * S.y))) {e : X} (he : e ∈ S.E yi)
    (hconj : ConjTo S.t e) : ∃ n ∈ normalizer (S.E yi : Set X), n * e * n⁻¹ = S.t := by
  have hyiR : yi ∈ S.data.R := by rcases hyi with rfl | rfl; exacts [S.y_mem, S.xy_mem]
  have hyi2 : yi ^ 2 = 1 := by rcases hyi with rfl | rfl; exacts [S.y_sq, S.xy_sq]
  have hyiB : yi ∉ S.B := by rcases hyi with rfl | rfl; exacts [S.y_not_mem_B, S.xy_not_mem_B]
  obtain ⟨h, rfl⟩ := hconj
  set P : Subgroup X := (S.E yi).map (MulAut.conj h⁻¹).toMonoidHom with hP
  have hPC : P ≤ centralizer ({S.t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hc := S.E_comm hyiR ha he
    calc h⁻¹ * a * h * S.t = h⁻¹ * (a * (h * S.t * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * S.t * h⁻¹) * a) * h := by rw [hc]
      _ = S.t * (h⁻¹ * a * h) := by group
  have hEp : IsPGroup 2 (S.E yi) := S.data.isPGroup_T.to_le (S.E_le_T hyiR)
  have hPp : IsPGroup 2 P := hEp.map _
  obtain ⟨m, hm, hmP⟩ := S.data.exists_conj_le_T hPp hPC
  set E' : Subgroup X := (S.E yi).map (MulAut.conj (m * h⁻¹)).toMonoidHom with hE'
  have hE'eq : E' = P.map (MulAut.conj m).toMonoidHom := by
    rw [hE', hP, Subgroup.map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  have hE'T : E' ≤ S.data.T := hE'eq ▸ hmP
  have hE'el : ElemAbelianTwo E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, S.E_comm hyiR ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, S.E_sq hyiR hyi2 ha, map_one]
  have hE'card : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective (MulAut.conj (m * h⁻¹)).injective, S.card_E hyiR hyi2 hyiB]
  have hmt : m * S.t * m⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hm]
    group
  have hconjt : (m * h⁻¹) * (h * S.t * h⁻¹) * (m * h⁻¹)⁻¹ = S.t := by
    calc (m * h⁻¹) * (h * S.t * h⁻¹) * (m * h⁻¹)⁻¹ = m * S.t * m⁻¹ := by group
      _ = S.t := hmt
  rcases S.eq_E_of_elem hE'T hE'el hE'card with h1 | h1 <;> rcases hyi with rfl | rfl
  · refine ⟨m * h⁻¹, ?_, hconjt⟩
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    have : (m * h⁻¹) * a * (m * h⁻¹)⁻¹ ∈ E' := ⟨a, ha, rfl⟩
    rwa [h1] at this
  · exact absurd ⟨(m * h⁻¹)⁻¹, by rw [← h1, hE', Subgroup.map_map]; ext a; simp [MulAut.conj_apply,
      mul_assoc]⟩ hnot
  · exact absurd ⟨m * h⁻¹, h1⟩ hnot
  · refine ⟨m * h⁻¹, ?_, hconjt⟩
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    have : (m * h⁻¹) * a * (m * h⁻¹)⁻¹ ∈ E' := ⟨a, ha, rfl⟩
    rwa [h1] at this

end A7Base

end CFSG.ComponentClassification.HSFLit
