module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2Make
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Tz

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem not_mem_R_sup_K {c : X} (hc : c = S.k ∨ c = S.t * S.k) :
    c ∉ S.data.R ⊔ S.data.K := by
  have hle : S.data.R ⊔ S.data.K ≤ (R0.comap S.data.ψ).map S.data.T.subtype := by
    refine sup_le (fun r hr => ⟨⟨r, hr.1⟩, S.data.ψ_mem_R0 hr, rfl⟩) fun g hg => ?_
    have hgT : g ∈ S.data.T := (mem_inf.mp hg).1
    have h1 : S.data.ψ ⟨g, hgT⟩ = 1 := (S.data.mem_K_iff hgT).mp hg
    exact ⟨⟨g, hgT⟩, show S.data.ψ ⟨g, hgT⟩ ∈ R0 by rw [h1]; exact one_mem _, rfl⟩
  intro h
  obtain ⟨⟨g, hgT⟩, hgR0, hgc⟩ := hle h
  have hgc' : g = c := hgc
  have hψ : S.data.ψ ⟨g, hgT⟩ = c0 := by
    rcases hc with rfl | rfl
    · have : (⟨g, hgT⟩ : S.data.T) = ⟨S.k, S.k_mem⟩ := Subtype.ext hgc'
      rw [this, S.ψ_k]
    · have : (⟨g, hgT⟩ : S.data.T) = ⟨S.t * S.k, mul_mem S.data.t_mem_T S.k_mem⟩ :=
        Subtype.ext hgc'
      rw [this, S.ψ_tk]
  exact c0_not_mem_R0 (hψ ▸ hgR0)

@[expose] noncomputable def frameOf {c : X} (hc : c = S.k ∨ c = S.t * S.k) : S.Frame where
  xF := S.x⁻¹
  yF := S.x * S.y
  kF := c
  xF_mem := inv_mem S.x_mem
  yF_mem := S.xy_mem
  xF_sq := by
    have hz2 : S.z ^ 2 = 1 := S.sq_of_mem_B (subset_closure (by simp))
    rw [inv_pow, show S.x ^ 2 = S.z from rfl]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two, hz2])
  yF_sq := S.xy_sq
  yF_inv := by
    calc S.x * S.y * S.x⁻¹ * (S.x * S.y)⁻¹ = S.x * (S.y * S.x * S.y⁻¹)⁻¹ * S.x⁻¹ := by group
      _ = S.x⁻¹⁻¹ := by rw [S.y_x_y]; group
  kF_mem := by
    rcases hc with rfl | rfl
    · exact S.k_mem
    · exact mul_mem S.data.t_mem_T S.k_mem
  kF_sq := by
    rcases hc with rfl | rfl
    · exact S.k_sq
    · rw [(Commute.mul_pow (S.data.commute_t S.k_mem).symm 2), S.t_sq, S.k_sq, one_mul]
  kF_comm := by
    intro r hr
    rcases hc with rfl | rfl
    · exact S.k_comm hr
    · rw [mul_assoc, S.k_comm hr, ← mul_assoc, ← S.data.commute_t hr.1, mul_assoc]
  kF_not_mem := S.not_mem_R_sup_K hc
  kF_fixed := by
    intro n hn
    have hk := S.conj_k_eq_of_mem_normalizer hn
    rcases hc with rfl | rfl
    · exact hk
    · have ht : n * S.t * n⁻¹ = S.t := by
        rw [mem_centralizer_singleton_iff.mp hn.2]
        group
      calc n * (S.t * S.k) * n⁻¹ = (n * S.t * n⁻¹) * (n * S.k * n⁻¹) := by group
        _ = S.t * S.k := by rw [ht, hk]

theorem B_withK {c : X} (hc : c = S.k ∨ c = S.t * S.k) : (S.withK c hc).B = S.B := by
  rcases hc with rfl | rfl
  · rfl
  · change closure {S.z, S.t, S.t * S.k} = closure {S.z, S.t, S.k}
    have h1 : S.t ∈ closure ({S.z, S.t, S.k} : Set X) := subset_closure (by simp)
    have h2 : S.k ∈ closure ({S.z, S.t, S.k} : Set X) := subset_closure (by simp)
    have h3 : S.t ∈ closure ({S.z, S.t, S.t * S.k} : Set X) := subset_closure (by simp)
    have h4 : S.t * S.k ∈ closure ({S.z, S.t, S.t * S.k} : Set X) := subset_closure (by simp)
    refine le_antisymm (closure_le _ |>.mpr ?_) (closure_le _ |>.mpr ?_)
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact h1
      · exact mul_mem h1 h2
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact h3
      · have := mul_mem (inv_mem h3) h4
        rwa [inv_mul_cancel_left] at this

theorem E_withK {c : X} (hc : c = S.k ∨ c = S.t * S.k) (yi : X) :
    (S.withK c hc).E yi = S.E yi := by
  rcases hc with rfl | rfl
  · rfl
  · change closure {S.z, yi, S.t, S.t * S.k} = closure {S.z, yi, S.t, S.k}
    have h1 : S.t ∈ closure ({S.z, yi, S.t, S.k} : Set X) := subset_closure (by simp)
    have h2 : S.k ∈ closure ({S.z, yi, S.t, S.k} : Set X) := subset_closure (by simp)
    have h3 : S.t ∈ closure ({S.z, yi, S.t, S.t * S.k} : Set X) := subset_closure (by simp)
    have h4 : S.t * S.k ∈ closure ({S.z, yi, S.t, S.t * S.k} : Set X) := subset_closure (by simp)
    refine le_antisymm (closure_le _ |>.mpr ?_) (closure_le _ |>.mpr ?_)
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact h1
      · exact mul_mem h1 h2
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact h3
      · have := mul_mem (inv_mem h3) h4
        rwa [inv_mul_cancel_left] at this

theorem frameOf_E₁ {c : X} (hc : c = S.k ∨ c = S.t * S.k) :
    (S.frameOf hc).E₁ = S.E (S.x * S.y) := rfl

theorem frameOf_E₂ {c : X} (hc : c = S.k ∨ c = S.t * S.k) :
    (S.frameOf hc).E₂ = S.E S.y := by
  change S.E (S.x⁻¹ * (S.x * S.y)) = S.E S.y
  rw [inv_mul_cancel_left]

theorem exists_normalizer_E_xy
    (hB : ∀ b ∈ S.B, ConjTo S.t b →
      ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = b)
    {e : X} (he : e ∈ S.E (S.x * S.y)) (hce : ConjTo S.t e) :
    ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = e := by
  obtain ⟨a, b, c, d, rfl⟩ := S.eq_W (Or.inr rfl) he
  rcases Fin.exists_fin_two.mp ⟨b, rfl⟩ with rfl | rfl
  · exact hB _ (S.W_mem_B _ _ _ _) hce
  obtain ⟨n, hn, hnt⟩ := hB _ (S.W_mem_B _ _ _ _) ((S.conjTo_W_xy a c d).mp hce)
  obtain ⟨g, hgC, hgN, hgz, hgxy, hgk⟩ := S.exists_d_xy
  set f := S.t ^ (c : ℕ) * S.k ^ (d : ℕ) with hf
  have hgt : g * S.t * g⁻¹ = S.t := by
    rw [mem_centralizer_singleton_iff.mp hgC]
    group
  have hgf : g * f * g⁻¹ = f := by
    have : g * f * g⁻¹ = (g * S.t * g⁻¹) ^ (c : ℕ) * (g * S.k * g⁻¹) ^ (d : ℕ) := by
      rw [hf, ← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply,
        MulAut.conj_apply]
    rw [this, hgt, hgk]
  have h10 : S.W (S.x * S.y) 1 0 c d = S.z * f := by simp [W, hf, mul_assoc]
  have h01 : S.W (S.x * S.y) 0 1 c d = S.x * S.y * f := by simp [W, hf, mul_assoc]
  have h11 : S.W (S.x * S.y) 1 1 c d = S.z * (S.x * S.y) * f := by simp [W, hf, mul_assoc]
  have hg1 : g * (S.z * f) * g⁻¹ = S.x * S.y * f := by
    calc g * (S.z * f) * g⁻¹ = (g * S.z * g⁻¹) * (g * f * g⁻¹) := by group
      _ = S.x * S.y * f := by rw [hgz, hgf]
  have hg2 : g * (S.x * S.y * f) * g⁻¹ = S.z * (S.x * S.y) * f := by
    calc g * (S.x * S.y * f) * g⁻¹ = (g * (S.x * S.y) * g⁻¹) * (g * f * g⁻¹) := by group
      _ = S.z * (S.x * S.y) * f := by rw [hgxy, hgf]
  rw [h10] at hnt
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with rfl | rfl
  · refine ⟨g * n, mul_mem hgN hn, ?_⟩
    rw [h01, ← hg1, ← hnt]
    group
  · refine ⟨g * g * n, mul_mem (mul_mem hgN hgN) hn, ?_⟩
    rw [h11, ← hg2, ← hg1, ← hnt]
    group

theorem not_subConj_or_of_four {T₁ : Subgroup X} {c : X} (hT₁p : IsPGroup 2 T₁)
    (hTT₁ : S.data.T ≤ T₁) (hT₁N : T₁ ≤ normalizer (S.data.T : Set X))
    (hcard : Nat.card T₁ = 4 * Nat.card S.data.T)
    (hO : ∀ b ∈ S.B, ConjTo S.t b ↔ b = S.t ∨ b = S.t * S.z ∨ b = S.t * c ∨ b = S.t * S.z * c) :
    ¬ SubConj (S.E (S.x * S.y)) (S.E S.y) ∨
      ∃ g ∈ T₁, (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y := by
  by_cases hsw : ∃ g ∈ T₁, (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y
  · exact Or.inr hsw
  left
  push Not at hsw
  have htB : S.t ∈ S.B := subset_closure (by simp)
  have hel : ElemAbelianTwo (S.E (S.x * S.y)) :=
    ⟨fun a ha b hb => S.E_comm S.xy_mem ha hb, fun a ha => S.E_sq S.xy_mem S.xy_sq ha⟩
  have hT₁E : ∀ g ∈ T₁, g ∈ normalizer (S.E (S.x * S.y) : Set X) := by
    intro g hg
    have hgN := hT₁N hg
    have hmap : (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom ≤ S.data.T := by
      rintro _ ⟨e, he, rfl⟩
      exact (mem_normalizer_iff.mp hgN e).mp (S.E_le_T S.xy_mem he)
    have hel' : ElemAbelianTwo ((S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_mul, ← map_mul, hel.comm a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom]
        rw [← map_pow, hel.sq_eq_one a ha, map_one]
    have hc16 : Nat.card ((S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom) = 16 := by
      rw [card_map_of_injective (MulAut.conj g).injective,
        S.card_E S.xy_mem S.xy_sq S.xy_not_mem_B]
    rcases S.eq_E_of_elem hmap hel' hc16 with h | h
    · exact absurd h (hsw g hg)
    · refine mem_normalizer_of_conj_mem fun e he => ?_
      have : g * e * g⁻¹ ∈ (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom := ⟨e, he, rfl⟩
      rwa [h] at this
  set O₁ : Set X := {b | ∃ g ∈ T₁, g * S.t * g⁻¹ = b} with hO₁
  have hidx := relIndex_inf_centralizer_eq_ncard T₁ S.t
  have hT₁C : T₁ ⊓ centralizer ({S.t} : Set X) = S.data.T :=
    S.eq_T_of_le' (hT₁p.to_le inf_le_left) (le_inf hTT₁ S.data.T_le_centralizer) inf_le_right
  rw [hT₁C] at hidx
  have hrel : S.data.T.relIndex T₁ * Nat.card S.data.T = Nat.card T₁ := by
    have := relIndex_mul_card (H := S.data.T) (K := T₁)
    rwa [inf_of_le_left hTT₁] at this
  have hO₁4 : O₁.ncard = 4 := by
    rw [← hidx]
    have hpos : 0 < Nat.card S.data.T := Nat.card_pos
    rw [hcard] at hrel
    exact Nat.eq_of_mul_eq_mul_right hpos hrel
  have hO₁sub : O₁ ⊆ ({S.t, S.t * S.z, S.t * c, S.t * S.z * c} : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    have hb := S.conj_mem_B (hT₁N hg) htB
    rcases (hO _ hb).mp ⟨g, rfl⟩ with h | h | h | h <;> simp [h]
  have hO₁eq : O₁ = ({S.t, S.t * S.z, S.t * c, S.t * S.z * c} : Set X) := by
    refine Set.eq_of_subset_of_ncard_le hO₁sub ?_ (Set.toFinite _)
    rw [hO₁4]
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  have hB : ∀ b ∈ S.B, ConjTo S.t b →
      ∃ n ∈ normalizer (S.E (S.x * S.y) : Set X), n * S.t * n⁻¹ = b := by
    intro b hb hcb
    have hbO : b ∈ O₁ := by
      rw [hO₁eq]
      rcases (hO b hb).mp hcb with h | h | h | h <;> simp [h]
    obtain ⟨g, hg, hgb⟩ := hbO
    exact ⟨g, hT₁E g hg, hgb⟩
  rintro ⟨g, hg⟩
  have hgmem : ∀ e ∈ S.E S.y, g⁻¹ * e * g ∈ S.E (S.x * S.y) := by
    intro e he
    rw [← hg] at he
    obtain ⟨e', he', rfl⟩ := he
    simpa [MulAut.conj_apply, mul_assoc] using he'
  have htEy : S.t ∈ S.E S.y := subset_closure (by simp)
  obtain ⟨n, hn, hnt⟩ := S.exists_normalizer_E_xy hB (hgmem _ htEy) ⟨g⁻¹, by group⟩
  refine S.not_conj_E_y_E_xy (g := n⁻¹ * g⁻¹) ?_ fun e he => ?_
  · rw [mem_centralizer_singleton_iff]
    calc n⁻¹ * g⁻¹ * S.t = n⁻¹ * (g⁻¹ * S.t * g) * n * (n⁻¹ * g⁻¹) := by group
      _ = n⁻¹ * (n * S.t * n⁻¹) * n * (n⁻¹ * g⁻¹) := by rw [hnt]
      _ = S.t * (n⁻¹ * g⁻¹) := by group
  · have := (mem_normalizer_iff.mp (inv_mem hn) _).mp (hgmem e he)
    simpa [mul_assoc] using this

end A7Base

theorem fritzA7Section4 : FritzA7Section4 := by
  intro hH X _ _ _ hnab hnot S
  obtain ⟨T₁, hT₁p, hTT₁, hT₁N, hmax, c, hc, w, -, -, -, -, -, hcase⟩ := S.exists_T₁ hnot
  have hzt : S.z * S.t = S.t * S.z := S.z_comm_of_mem_T S.data.t_mem_T
  rcases hcase with ⟨hcard, hO⟩ | ⟨hcard, hO, hwt⟩
  · refine ⟨S.withK c hc, (S.withK c hc).frameOf (Or.inl rfl), T₁,
      ⟨hT₁p, hTT₁, hT₁N, hmax, hcard, fun b hb => ?_⟩, ⟨rfl, rfl, rfl⟩, ?_⟩
    · rw [S.B_withK hc] at hb
      exact hO b hb
    · rw [A7Base.frameOf_E₁, A7Base.frameOf_E₂, S.E_withK hc, S.E_withK hc]
      exact S.not_subConj_or_of_four hT₁p hTT₁ hT₁N hcard hO
  exfalso
  rcases hwt with h | h | h
  · exact S.false_of_tz (eq_one_of_isSimpleGroup hnab) fun b hb => by rw [hO b hb, h]
  · apply hnot
    obtain ⟨fc, hfc⟩ : ∃ fc : Fin 2, S.t * c = S.W S.y 0 0 (1 + fc) 1 := by
      rcases hc with rfl | rfl
      · exact ⟨0, by simp [A7Base.W]⟩
      · refine ⟨1, ?_⟩
        rw [← mul_assoc, ← pow_two, S.t_sq, one_mul]
        simp [A7Base.W]
    exact S.sectRank4_of_tc hH hT₁p hTT₁ hT₁N hcard fc fun b hb => by rw [hO b hb, h, hfc]
  · apply hnot
    obtain ⟨fc, hfc⟩ : ∃ fc : Fin 2, S.t * S.z * c = S.W (S.x * S.y) 1 0 (1 + fc) 1 := by
      rcases hc with rfl | rfl
      · exact ⟨0, by simp [A7Base.W, hzt]⟩
      · refine ⟨1, ?_⟩
        rw [← hzt, mul_assoc, ← mul_assoc S.t, ← pow_two, S.t_sq, one_mul]
        simp [A7Base.W]
    exact S.sectRank4_of_tzc hH hT₁p hTT₁ hT₁N hcard fc fun b hb => by rw [hO b hb, h, hfc]

end CFSG.ComponentClassification.HSFLit
