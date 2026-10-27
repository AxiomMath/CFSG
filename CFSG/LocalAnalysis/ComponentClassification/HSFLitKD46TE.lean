module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46T
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDCong

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

theorem dbit8_one : dbit8 1 = 1 := by decide

theorem conj_dbit8 : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8) (u' : (ZMod 8)ˣ) (b' : ZMod 8),
    dbit8 b' = 0 →
    dbit8 (b + u * b' + u * u' * (-(u⁻¹ * b))) = 0 := by decide

theorem conj_even_pE : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8) (u' : (ZMod 8)ˣ) (b' : ZMod 8),
    dbit8 b = 0 →
    (pE 0 u' b' → pE 0 (u * u' * u⁻¹) (b + u * b' + u * u' * (-(u⁻¹ * b)))) ∧
    (pE 2 u' b' → pE 2 (u * u' * u⁻¹) (b + u * b' + u * u' * (-(u⁻¹ * b)))) := by decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem TE_eq : S.TE = pre A PTE := by
  ext g
  rw [mem_pre, KDBase.TE, mem_inf]
  constructor
  · rintro ⟨hgT, hgB⟩
    refine ⟨hgT, ?_⟩
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [← hub, mem_PTE]
    rcases dbit8_eq b with hb | hb
    · exact hb
    · exfalso
      have hk := mem_centralizer_iff.mp hgB S.k (mem_B_k S)
      have := congrArg (ψX A) hk
      rw [ψX_mul (k_mem_T S) hgT, ψX_mul hgT (k_mem_T S), ψ_k, ← hub] at this
      exact not_comm_k8 hb this.symm
  · rintro ⟨hgT, hgP⟩
    refine ⟨hgT, ?_⟩
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [← hub, mem_PTE] at hgP
    obtain ⟨r, hr, a, e, -, -, rfl, -⟩ := exists_eq_of_mem_T C hgT hub.symm hgP
    rw [KDBase.B, centralizer_closure, mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact z_comm S hgT
    · exact (comm_t hgT).symm
    · have hk : Commute S.k (r * t ^ a * C.k ^ e) :=
        ((Commute.mul_right (k_comm_R S hr) ((Commute.pow_right (k_comm_t S) a)))).mul_right
          (Commute.pow_right (Commute.refl _) e)
      exact hk

theorem mem_TE_iff {g : X} : g ∈ S.TE ↔ g ∈ A.T ∧ ψX A g ∈ PTE := by rw [TE_eq]; exact mem_pre

theorem TE_le_T : S.TE ≤ A.T := by rw [TE_eq]; exact pre_le_T _

theorem comm_B_TE {b g : X} (hb : b ∈ S.B) (hg : g ∈ S.TE) : b * g = g * b :=
  mem_centralizer_iff.mp (mem_inf.mp hg).2 b hb

theorem B_le_TE : S.B ≤ S.TE := fun _ hb =>
  mem_inf.mpr ⟨B_le_T S hb, mem_centralizer_iff.mpr fun _ hc => B_comm S hc hb⟩

theorem E_le_TE {yi : X} (hyi : yi ∈ A.R) : S.E yi ≤ S.TE := fun _ he =>
  mem_inf.mpr ⟨E_le_T S yi hyi he, mem_centralizer_iff.mpr fun _ hc =>
    E_comm S hyi (B_le_E S yi hc) he⟩

theorem TE_eq_L2KD : S.TE = L2KD.TE A := by
  ext g
  rw [mem_TE_iff, L2KD.mem_TE]
  constructor
  · rintro ⟨hgT, hgP⟩
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [← hub, mem_PTE] at hgP
    refine ⟨hgT, ?_⟩
    rw [dbitT_apply hgT hub.symm, hgP]
    rfl
  · rintro ⟨hgT, h1⟩
    obtain ⟨u, b, hub⟩ := ψX_mem_H8' hgT
    rw [dbitT_apply hgT hub.symm] at h1
    refine ⟨hgT, ?_⟩
    rw [← hub, mem_PTE]
    have := congrArg Multiplicative.toAdd h1
    simpa using this

theorem card_T_eq : Nat.card A.T = 2 * Nat.card S.TE := by
  rw [TE_eq_L2KD]
  exact card_T_eq_two_mul_card_TE C

theorem relIndex_TE : S.TE.relIndex A.T = 2 := by
  have h := relIndex_mul_card S.TE A.T
  rw [inf_of_le_left (TE_le_T S), card_T_eq S] at h
  have hpos : 0 < Nat.card S.TE := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h

theorem odd_of_not_mem_TE {g : X} (hg : g ∈ A.T) (hgE : g ∉ S.TE) :
    ∃ u b, ψX A g = aff8 u b ∧ dbit8 b = 1 := by
  obtain ⟨u, b, hub⟩ := ψX_mem_H8' hg
  refine ⟨u, b, hub.symm, ?_⟩
  rcases dbit8_eq b with hb | hb
  · exact absurd ((mem_TE_iff S).mpr ⟨hg, by rw [← hub]; exact mem_PTE.mpr hb⟩) hgE
  · exact hb

theorem d_not_mem_TE : S.d ∉ S.TE := by
  rw [mem_TE_iff, ψ_d]
  rintro ⟨-, h⟩
  rw [d8, mem_PTE, dbit8_one] at h
  exact one_ne_zero h

theorem conj_mem_TE {g h : X} (hg : g ∈ A.T) (hh : h ∈ S.TE) : g * h * g⁻¹ ∈ S.TE := by
  obtain ⟨hhT, hhP⟩ := (mem_TE_iff S).mp hh
  rw [mem_TE_iff]
  refine ⟨mul_mem (mul_mem hg hhT) (inv_mem hg), ?_⟩
  obtain ⟨u, b, hub⟩ := ψX_mem_H8' hg
  obtain ⟨u', b', hψ, hb'⟩ := hhP
  rw [ψX_conj hg hhT, ← hub, ← hψ, aff8_inv, aff8_mul, aff8_mul, mem_PTE]
  exact conj_dbit8 u b u' b' hb'

theorem conj_mem_B {g b : X} (hg : g ∈ A.T) (hb : b ∈ S.B) : g * b * g⁻¹ ∈ S.B := by
  obtain ⟨hbT, hbP⟩ := (mem_B_iff S).mp hb
  rw [mem_B_iff]
  refine ⟨mul_mem (mul_mem hg hbT) (inv_mem hg), ?_⟩
  obtain ⟨u, b', hub⟩ := ψX_mem_H8' hg
  rw [ψX_conj hg hbT, ← hub]
  exact conj_mem_PB hbP

theorem conj_pre_PE_of_mem_TE {g e : X} (hg : g ∈ S.TE) :
    (e ∈ pre A PE₀ → g * e * g⁻¹ ∈ pre A PE₀) ∧ (e ∈ pre A PE₂ → g * e * g⁻¹ ∈ pre A PE₂) := by
  obtain ⟨hgT, ⟨u, b, hub, hb⟩⟩ := (mem_TE_iff S).mp hg
  constructor
  · intro he
    obtain ⟨heT, ⟨u', b', hψ, h'⟩⟩ := mem_pre.mp he
    refine mem_pre.mpr ⟨mul_mem (mul_mem hgT heT) (inv_mem hgT), ?_⟩
    rw [ψX_conj hgT heT, ← hub, ← hψ, aff8_inv, aff8_mul, aff8_mul, mem_PE₀]
    exact (conj_even_pE u b u' b' hb).1 h'
  · intro he
    obtain ⟨heT, ⟨u', b', hψ, h'⟩⟩ := mem_pre.mp he
    refine mem_pre.mpr ⟨mul_mem (mul_mem hgT heT) (inv_mem hgT), ?_⟩
    rw [ψX_conj hgT heT, ← hub, ← hψ, aff8_inv, aff8_mul, aff8_mul, mem_PE₂]
    exact (conj_even_pE u b u' b' hb).2 h'

theorem conj_pre_PE_of_not_mem_TE {g e : X} (hg : g ∈ A.T) (hgE : g ∉ S.TE) :
    (e ∈ pre A PE₀ → g * e * g⁻¹ ∈ pre A PE₂) ∧ (e ∈ pre A PE₂ → g * e * g⁻¹ ∈ pre A PE₀) := by
  obtain ⟨u, b, hub, hb⟩ := odd_of_not_mem_TE S hg hgE
  constructor
  · intro he
    obtain ⟨heT, heP⟩ := mem_pre.mp he
    refine mem_pre.mpr ⟨mul_mem (mul_mem hg heT) (inv_mem hg), ?_⟩
    rw [ψX_conj hg heT, hub]
    exact (conj_mem_PE_of_odd hb).1 heP
  · intro he
    obtain ⟨heT, heP⟩ := mem_pre.mp he
    refine mem_pre.mpr ⟨mul_mem (mul_mem hg heT) (inv_mem hg), ?_⟩
    rw [ψX_conj hg heT, hub]
    exact (conj_mem_PE_of_odd hb).2 heP

theorem E_y_ne : S.E S.y ≠ S.E (S.x * S.y) := by
  intro h
  apply y_not_mem_B S
  rw [← E₁_inf_E₂ S, ← h, inf_idem]
  exact mem_E_yi S _

theorem conj_E_of_not_mem_TE {g e : X} (hg : g ∈ A.T) (hgE : g ∉ S.TE) :
    (e ∈ S.E S.y → g * e * g⁻¹ ∈ S.E (S.x * S.y)) ∧
      (e ∈ S.E (S.x * S.y) → g * e * g⁻¹ ∈ S.E S.y) := by
  have h := conj_pre_PE_of_not_mem_TE S (e := e) hg hgE
  rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact h
  · exact ⟨h.2, h.1⟩

theorem conj_E_of_mem_TE {g e : X} (hg : g ∈ S.TE) :
    (e ∈ S.E S.y → g * e * g⁻¹ ∈ S.E S.y) ∧
      (e ∈ S.E (S.x * S.y) → g * e * g⁻¹ ∈ S.E (S.x * S.y)) := by
  have h := conj_pre_PE_of_mem_TE S (e := e) hg
  rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact h
  · exact ⟨h.2, h.1⟩

theorem TE_le_normalizer_E₁ : S.TE ≤ normalizer (S.E S.y : Set X) := fun _ hg =>
  mem_normalizer_of_conj_mem fun _ he => (conj_E_of_mem_TE S hg).1 he

theorem TE_le_normalizer_E₂ : S.TE ≤ normalizer (S.E (S.x * S.y) : Set X) := fun _ hg =>
  mem_normalizer_of_conj_mem fun _ he => (conj_E_of_mem_TE S hg).2 he

theorem mem_TE_of_mem_normalizer_E₁ {g : X} (hg : g ∈ A.T)
    (hgN : g ∈ normalizer (S.E S.y : Set X)) : g ∈ S.TE := by
  by_contra hgE
  have h1 : g * S.y * g⁻¹ ∈ S.E S.y := (mem_normalizer_iff.mp hgN _).mp (mem_E_yi S _)
  have h2 : g * S.y * g⁻¹ ∈ S.E (S.x * S.y) := (conj_E_of_not_mem_TE S hg hgE).1 (mem_E_yi S _)
  have hB : g * S.y * g⁻¹ ∈ S.B := by rw [← E₁_inf_E₂ S]; exact mem_inf.mpr ⟨h1, h2⟩
  apply y_not_mem_B S
  have := conj_mem_B S (inv_mem hg) hB
  simpa [mul_assoc] using this

theorem mem_TE_of_mem_normalizer_E₂ {g : X} (hg : g ∈ A.T)
    (hgN : g ∈ normalizer (S.E (S.x * S.y) : Set X)) : g ∈ S.TE := by
  by_contra hgE
  have h1 : g * (S.x * S.y) * g⁻¹ ∈ S.E (S.x * S.y) :=
    (mem_normalizer_iff.mp hgN _).mp (mem_E_yi S _)
  have h2 : g * (S.x * S.y) * g⁻¹ ∈ S.E S.y := (conj_E_of_not_mem_TE S hg hgE).2 (mem_E_yi S _)
  have hB : g * (S.x * S.y) * g⁻¹ ∈ S.B := by rw [← E₁_inf_E₂ S]; exact mem_inf.mpr ⟨h2, h1⟩
  apply xy_not_mem_B S
  have := conj_mem_B S (inv_mem hg) hB
  simpa [mul_assoc] using this

theorem d_conj_z : S.d * S.z * S.d⁻¹ = S.z := by rw [← z_comm S (d_mem_T S), mul_inv_cancel_right]

theorem d_conj_t : S.d * t * S.d⁻¹ = t := by rw [comm_t (d_mem_T S), mul_inv_cancel_right]

theorem z_eq_gens (G : Gens A) : S.z = G.z :=
  eq_of_ψX_eq (z_mem S) G.z_mem (by rw [ψ_z, G.ψ_z])

theorem d_conj_k : ∃ c : ℕ, c < 2 ∧ S.d * S.k * S.d⁻¹ = S.z * t ^ c * S.k := by
  obtain ⟨G⟩ := nonempty_gens (A := A)
  obtain ⟨c, hc, h⟩ := L2KD.d_conj_k C G
  exact ⟨c, hc, by rw [z_eq_gens S G]; exact h⟩

@[expose] noncomputable def Zt : Subgroup X := ⊥ ⊔ zpowers S.z ⊔ zpowers t

theorem z_mem_Zt : S.z ∈ Zt S := mem_sup_left (mem_sup_right (mem_zpowers _))

theorem t_mem_Zt : t ∈ Zt S := mem_sup_right (mem_zpowers _)

theorem card_Zt : Nat.card (Zt S) = 4 := by
  obtain ⟨hV1, -, hV1c⟩ := ElemAbelianTwo.bot.sup_zpowers (z_sq S)
    (fun h => z_ne_one S (mem_bot.mp h)) (fun a ha => by rw [mem_bot.mp ha, one_mul, mul_one])
  have hV1R : (⊥ ⊔ zpowers S.z : Subgroup X) ≤ A.R := sup_le bot_le (zpowers_le.mpr (z_mem S))
  obtain ⟨-, -, hV2c⟩ := hV1.sup_zpowers (t_sq' (A := A))
    (fun h => A.config.not_mem (hV1R h).2) (fun a ha => (comm_t (hV1R ha).1).symm)
  rw [Zt, hV2c, hV1c, card_bot]

theorem mem_Zt_of_comm {f g : X} (hf : f ∈ A.T) (hfE : f ∉ S.TE) (hg : g ∈ S.TE)
    (hg2 : g ^ 2 = 1) (hfg : f * g = g * f) : g ∈ Zt S := by
  obtain ⟨u, b, hψf, hb⟩ := odd_of_not_mem_TE S hf hfE
  obtain ⟨hgT, hgP⟩ := (mem_TE_iff S).mp hg
  have hc := congrArg (ψX A) hfg
  rw [ψX_mul hf hgT, ψX_mul hgT hf, hψf] at hc
  have h2 : ψX A g ^ 2 = 1 := by rw [← ψX_pow hgT, hg2, ψX_one]
  rcases eq_of_comm_odd hb hgP h2 hc with h | h
  · rcases eq_or_eq_mul_t C hgT (one_mem _) (by rw [h, ψX_one]) with h1 | h1 <;> rw [h1]
    · exact one_mem _
    · rw [one_mul]
      exact t_mem_Zt S
  · rcases eq_or_eq_mul_t C hgT (z_mem_T S) (by rw [h, ψ_z]) with h1 | h1 <;> rw [h1]
    · exact z_mem_Zt S
    · exact mul_mem (z_mem_Zt S) (t_mem_Zt S)

theorem card_le_of_not_le_TE {F : Subgroup X} (hFT : F ≤ A.T) (hF : ElemAbelianTwo F)
    (hFE : ¬ F ≤ S.TE) : Nat.card F ≤ 8 ∧ (Nat.card F = 8 → t ∈ F) := by
  obtain ⟨f, hf, hfE⟩ := Set.not_subset.mp hFE
  have hle : F ⊓ S.TE ≤ Zt S := fun g hg =>
    mem_Zt_of_comm S (hFT hf) hfE (mem_inf.mp hg).2 (hF.sq_eq_one g (mem_inf.mp hg).1)
      (hF.comm f hf g (mem_inf.mp hg).1)
  have hidx : S.TE.relIndex F = 2 := by
    have h1 : S.TE.relIndex F ≤ 2 := by
      rw [← relIndex_TE S]
      exact relIndex_le_of_le_right hFT (by rw [relIndex_TE S]; norm_num)
    have h2 : S.TE.relIndex F ≠ 1 := fun h => hFE (relIndex_eq_one.mp h)
    have h3 : S.TE.relIndex F ≠ 0 := by
      intro h0
      have := relIndex_mul_card S.TE F
      rw [h0, zero_mul] at this
      exact Nat.card_pos.ne' this.symm
    omega
  have hcard : Nat.card F = 2 * Nat.card (F ⊓ S.TE : Subgroup X) := by
    have := relIndex_mul_card S.TE F
    rw [hidx, inf_comm] at this
    exact this.symm
  have hZ : Nat.card (F ⊓ S.TE : Subgroup X) ≤ 4 := by
    rw [← card_Zt S]
    exact card_le_of_le hle
  refine ⟨by omega, fun h8 => ?_⟩
  have h4 : Nat.card (F ⊓ S.TE : Subgroup X) = 4 := by omega
  have heq : F ⊓ S.TE = Zt S := eq_of_le_of_card_ge hle (by rw [h4, card_Zt])
  have : t ∈ F ⊓ S.TE := by rw [heq]; exact t_mem_Zt S
  exact (mem_inf.mp this).1

theorem le_E_of_elem {F : Subgroup X} (hFE : F ≤ S.TE) (hF : ElemAbelianTwo F) :
    F ≤ S.E S.y ∨ F ≤ S.E (S.x * S.y) := by
  have key : F ≤ pre A PE₀ ∨ F ≤ pre A PE₂ := by
    by_cases h : F ≤ pre A PE₀
    · exact Or.inl h
    · right
      obtain ⟨a, ha, haE⟩ := Set.not_subset.mp h
      intro b hb
      obtain ⟨haT, haP⟩ := (mem_TE_iff S).mp (hFE ha)
      obtain ⟨hbT, hbP⟩ := (mem_TE_iff S).mp (hFE hb)
      refine mem_pre.mpr ⟨hbT, mem_PE₂_of_comm haP hbP ?_ ?_ ?_ ?_⟩
      · rw [← ψX_pow haT, hF.sq_eq_one a ha, ψX_one]
      · rw [← ψX_pow hbT, hF.sq_eq_one b hb, ψX_one]
      · rw [← ψX_mul haT hbT, ← ψX_mul hbT haT, hF.comm a ha b hb]
      · exact fun h' => haE (mem_pre.mpr ⟨haT, h'⟩)
  rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
  · exact key
  · exact key.symm

theorem eq_E_of_card {F : Subgroup X} (hFT : F ≤ A.T) (hF : ElemAbelianTwo F)
    (h16 : Nat.card F = 16) : F = S.E S.y ∨ F = S.E (S.x * S.y) := by
  have hFE : F ≤ S.TE := by
    by_contra h
    have := (card_le_of_not_le_TE S hFT hF h).1
    omega
  rcases le_E_of_elem S hFE hF with h | h
  · exact Or.inl (eq_of_le_of_card_ge h (by rw [h16, card_E₁]))
  · exact Or.inr (eq_of_le_of_card_ge h (by rw [h16, card_E₂]))

omit [Finite X] in
theorem elem_map {E : Subgroup X} (hE : ElemAbelianTwo E) (g : X) :
    ElemAbelianTwo (E.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hE.comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hE.sq_eq_one a ha, map_one]

theorem mem_normalizer_TE_of_conj_le {g : X} (h : ∀ a ∈ S.TE, g * a * g⁻¹ ∈ A.T) :
    g ∈ normalizer (S.TE : Set X) := by
  set φ := (MulAut.conj g).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have hM : ∀ {yi : X}, yi ∈ A.R → yi ^ 2 = 1 → yi ∉ S.B →
      (S.E yi).map φ = S.E S.y ∨ (S.E yi).map φ = S.E (S.x * S.y) := by
    intro yi hyi hyi2 hyiB
    refine eq_E_of_card S ?_ (elem_map (elem_E S hyi hyi2) g) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact h a (E_le_TE S hyi ha)
    · rw [card_map_of_injective hinj, card_E S hyi hyi2 hyiB]
  have hne : (S.E S.y).map φ ≠ (S.E (S.x * S.y)).map φ := fun h' =>
    E_y_ne S (map_injective hinj h')
  have hB : S.B.map φ = S.B := by
    rw [← E₁_inf_E₂ S, map_inf _ _ _ hinj]
    rcases hM S.y_mem S.y_sq (y_not_mem_B S) with h1 | h1 <;>
      rcases hM (xy_mem S) (xy_sq S) (xy_not_mem_B S) with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, inf_comm]
    · exact absurd (h1.trans h2.symm) hne
  refine mem_normalizer_of_conj_mem fun a ha => ?_
  refine mem_inf.mpr ⟨h a ha, mem_centralizer_iff.mpr fun b hb => ?_⟩
  rw [← hB] at hb
  obtain ⟨b', hb', rfl⟩ := hb
  simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have := comm_B_TE S hb' ha
  calc g * b' * g⁻¹ * (g * a * g⁻¹) = g * (b' * a) * g⁻¹ := by group
    _ = g * (a * b') * g⁻¹ := by rw [this]
    _ = g * a * g⁻¹ * (g * b' * g⁻¹) := by group

end CFSG.ComponentClassification.HSFLit.KD46
