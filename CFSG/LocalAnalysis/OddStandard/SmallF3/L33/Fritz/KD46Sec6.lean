module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NMisc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NS1

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

namespace KD46

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem conj_E_cases {g : X} (hg : g ∈ normalizer (S.TE : Set X)) :
    ((S.E S.y).map (MulAut.conj g).toMonoidHom = S.E S.y ∧
      (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y)) ∨
    ((S.E S.y).map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y) ∧
      (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom = S.E S.y) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hM : ∀ {yi : X}, yi ∈ A.R → yi ^ 2 = 1 → yi ∉ S.B →
      (S.E yi).map (MulAut.conj g).toMonoidHom = S.E S.y ∨
        (S.E yi).map (MulAut.conj g).toMonoidHom = S.E (S.x * S.y) := by
    intro yi hyi hyi2 hyiB
    refine eq_E_of_card S ?_ (elem_map (elem_E S hyi hyi2) g) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact TE_le_T S ((mem_normalizer_iff.mp hg a).mp (E_le_TE S hyi ha))
    · rw [card_map_of_injective hinj, card_E S hyi hyi2 hyiB]
  have hne : (S.E S.y).map (MulAut.conj g).toMonoidHom ≠
      (S.E (S.x * S.y)).map (MulAut.conj g).toMonoidHom := fun h' =>
    E_y_ne S (map_injective hinj h')
  rcases hM S.y_mem S.y_sq (y_not_mem_B S) with h1 | h1 <;>
    rcases hM (xy_mem S) (xy_sq S) (xy_not_mem_B S) with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne

theorem mem_normalizer_iff_map {g : X} {E : Subgroup X} :
    g ∈ normalizer (E : Set X) ↔ E.map (MulAut.conj g).toMonoidHom = E := by
  constructor
  · intro hg
    apply le_antisymm
    · rintro _ ⟨e, he, rfl⟩
      exact (mem_normalizer_iff.mp hg e).mp he
    · intro e he
      refine ⟨g⁻¹ * e * g, ?_, by simp [mul_assoc]⟩
      have := (mem_normalizer_iff.mp (inv_mem hg) e).mp he
      simpa using this
  · intro h
    refine mem_normalizer_of_conj_mem fun e he => ?_
    rw [← h]
    exact ⟨e, he, rfl⟩

theorem mem_normalizer_E₁_iff {g : X} (hg : g ∈ normalizer (S.TE : Set X)) :
    g ∈ normalizer (S.E S.y : Set X) ↔ g ∈ normalizer (S.E (S.x * S.y) : Set X) := by
  rw [mem_normalizer_iff_map, mem_normalizer_iff_map]
  rcases conj_E_cases S hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · rw [h1, h2]
    exact ⟨fun h => absurd h (E_y_ne S).symm, fun h => absurd h (E_y_ne S)⟩

variable {S}

theorem relIndex_R {T₁ : Subgroup X} (h4 : S.Sec4 T₁) :
    (T₁ ⊓ normalizer (S.E S.y : Set X)).relIndex T₁ = 2 := by
  set R := T₁ ⊓ normalizer (S.E S.y : Set X) with hR
  have hdT₁ : S.d ∈ T₁ := h4.le (d_mem_T S)
  have hdN : S.d ∈ normalizer (S.TE : Set X) := h4.le_normalizer hdT₁
  have hdR : S.d ∉ normalizer (S.E S.y : Set X) := fun h =>
    d_not_mem_TE S (mem_TE_of_mem_normalizer_E₁ S (d_mem_T S) h)
  have hcases : ∀ {g : X}, g ∈ T₁ → (g ∈ normalizer (S.E S.y : Set X) ↔
      (S.E S.y).map (MulAut.conj g).toMonoidHom = S.E S.y) := fun _ => mem_normalizer_iff_map
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨S.d, hdT₁⟩, fun b => ?_⟩
  have hbN : (b : X) ∈ normalizer (S.TE : Set X) := h4.le_normalizer b.2
  have hbdN : (b : X) * S.d ∈ normalizer (S.TE : Set X) := mul_mem hbN hdN
  simp only [mem_subgroupOf, Subgroup.coe_mul, hR, mem_inf, b.2, mul_mem b.2 hdT₁, true_and]
  rw [hcases (mul_mem b.2 hdT₁), hcases b.2]
  have hmap : (S.E S.y).map (MulAut.conj ((b : X) * S.d)).toMonoidHom =
      ((S.E S.y).map (MulAut.conj S.d).toMonoidHom).map (MulAut.conj (b : X)).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [mul_assoc]
  rw [hmap]
  rcases conj_E_cases S hdN with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (mem_normalizer_iff_map.mpr h1) hdR
  rw [h1]
  rcases conj_E_cases S hbN with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ <;> rw [h1', h2'] <;>
    simp [Xor, (E_y_ne S).symm]

theorem hyp_of_sec4 {T₁ : Subgroup X} (h4 : S.Sec4 T₁) :
    Hyp S (T₁ ⊓ normalizer (S.E S.y : Set X)) := by
  set R := T₁ ⊓ normalizer (S.E S.y : Set X) with hR
  have hTE : S.TE ≤ R := le_inf ((TE_le_T S).trans h4.le) (TE_le_normalizer_E₁ S)
  have hcard : Nat.card R = 4 * Nat.card S.TE := by
    have h1 := relIndex_mul_card R T₁
    have hRT : R ⊓ T₁ = R := inf_of_le_left inf_le_left
    rw [relIndex_R h4, hRT, h4.card, card_T_eq S] at h1
    omega
  refine ⟨h4.isPGroup.to_le inf_le_left, hTE, inf_le_left.trans h4.le_normalizer, hcard,
    fun b hb => h4.fusion b hb, inf_le_right,
    fun g hg => (mem_normalizer_E₁_iff S (h4.le_normalizer (mem_inf.mp hg).1)).mp
      (mem_inf.mp hg).2, ?_⟩
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨hgT₁, hgN⟩, hgC⟩ := hg
    have hT : T₁ ⊓ centralizer ({t} : Set X) = A.T :=
      eq_T_of_le (h4.isPGroup.to_le inf_le_left) (le_inf h4.le A.T_le_centralizer) inf_le_right
    have hgT : g ∈ A.T := hT ▸ mem_inf.mpr ⟨hgT₁, hgC⟩
    exact mem_TE_of_mem_normalizer_E₁ S hgT hgN
  · exact le_inf hTE (TE_le_C S)

theorem T₁_eq_sup {T₁ : Subgroup X} (h4 : S.Sec4 T₁) :
    T₁ = A.T ⊔ (T₁ ⊓ normalizer (S.E S.y : Set X)) := by
  set R := T₁ ⊓ normalizer (S.E S.y : Set X) with hR
  set K := A.T ⊔ R with hK
  have hRK : R ≤ K := le_sup_right
  have hKT₁ : K ≤ T₁ := sup_le h4.le inf_le_left
  have hmul := relIndex_mul_relIndex R K T₁ hRK hKT₁
  rw [relIndex_R h4] at hmul
  have hne : R.relIndex K ≠ 1 := by
    intro h
    have := relIndex_eq_one.mp h (mem_sup_left (d_mem_T S) : S.d ∈ K)
    exact d_not_mem_TE S (mem_TE_of_mem_normalizer_E₁ S (d_mem_T S) (mem_inf.mp this).2)
  have h2 : K.relIndex T₁ = 1 := by
    rcases Nat.eq_zero_or_pos (R.relIndex K) with h0 | hpos
    · rw [h0, zero_mul] at hmul; omega
    · have : R.relIndex K * K.relIndex T₁ = 2 := hmul
      have hle : R.relIndex K ≤ 2 := Nat.le_of_dvd (by norm_num) ⟨_, this.symm⟩
      interval_cases h : R.relIndex K
      · omega
      · omega
  exact le_antisymm (relIndex_eq_one.mp h2) hKT₁

theorem inf_normalizer_le {T₁ : Subgroup X} (h4 : S.Sec4 T₁) (I : Inst S) :
    T₁ ⊓ normalizer (S.E I.yi : Set X) ≤ T₁ ⊓ normalizer (S.E S.y : Set X) := by
  intro g hg
  obtain ⟨hgT₁, hgN⟩ := mem_inf.mp hg
  refine mem_inf.mpr ⟨hgT₁, ?_⟩
  rcases I.yi_or with h | h <;> rw [h] at hgN
  · exact hgN
  · exact (mem_normalizer_E₁_iff S (h4.le_normalizer hgT₁)).mpr hgN

namespace Inst

variable {I : Inst S} {T₁ : Subgroup X} {H : Hyp S (T₁ ⊓ normalizer (S.E S.y : Set X))}

namespace Data6

variable (D : I.Data6 H)

theorem Q0_le : S.Q0 I.yi I.ki D.w₁ D.w₂ ≤ D.Q₁ :=
  sup_le (sup_le (I.E0_le_E.trans D.E_le_Q₁) (zpowers_le.mpr D.w₁_Q₁)) (zpowers_le.mpr D.w₂_Q₁)

theorem D₁₁_le : zpowers D.d ≤ normalizer (S.E I.yi : Set X) ⊓ normalizer (D.Q₁ : Set X) ⊓
    centralizer ({t} : Set X) :=
  zpowers_le.mpr (mem_inf.mpr ⟨mem_inf.mpr ⟨D.d_mat.mem, D.d_Q₁⟩, D.d_mem_C_t⟩)

theorem w₁_comm_t : D.w₁ * t * D.w₁⁻¹ * t⁻¹ ≠ 1 := by
  rw [D.w₁_mat.conj_t, M1C_two]
  intro h
  have h' : I.wV (1, 0, 1, D.ε) = I.wV (0, 0, 1, 0) := by
    calc I.wV (1, 0, 1, D.ε) = I.wV (1, 0, 1, D.ε) * t⁻¹ * t := by group
      _ = I.wV (0, 0, 1, 0) := by rw [h, one_mul]; exact I.wV_t
  have h1 : (1 : Fin 2) = 0 := congrArg Prod.fst (I.wV_injective h')
  exact absurd h1 (by decide)

theorem w₁_comm_C' : ∀ c ∈ D.Q₁ ⊓ centralizer (zpowers D.d : Set X), D.w₁ * c * D.w₁⁻¹ * c⁻¹ ∈
    (match actOf D.ε with
      | .one => closure {S.z}
      | .two => closure {S.z * I.ki}) := by
  intro c hc
  have h := D.w₁_comm_C c hc
  rcases Fin.exists_fin_two.mp ⟨D.ε, rfl⟩ with he | he
  · rw [he] at h ⊢
    simpa [actOf, wV] using h
  · rw [he] at h ⊢
    simpa [actOf, wV] using h

variable (Rl : D.Rel)

noncomputable def toSec6 (h4 : S.Sec4 T₁) : S.Sec6 T₁ I.yi I.ki I.ui where
  S₁ := D.S₁
  Q₁ := D.Q₁
  D₁₁ := zpowers D.d
  C₁ := D.C₁
  v := D.v
  w₁ := D.w₁
  w₂ := D.w₂
  u := D.u
  d₃ := D.d
  act := actOf D.ε
  q0 := q0Of D.ε Rl.s1 Rl.s4
  automizer := I.automizer H
  controls := controls I H
  card_conj := card_conj I H
  isPGroup_S₁ := D.isPGroup
  S₁_le := D.le
  S₁_maximal := D.maximal
  S₁_eq := D.S₁_eq Rl
  v_central := D.v_central
  d₃_mem := mem_inf.mpr ⟨D.d_mat.mem, D.d_mem_C_t⟩
  d₃_cube := D.d_cube_mem
  d₃_not_mem := D.d_not_mem
  u_inv_d₃ := by rw [D.u_inv_d, inv_mul_cancel]; exact one_mem _
  u_comm_w₁ := D.u_comm_w₁
  normalizer_inf_centralizer := D.normalizer_inf_centralizer
  act_holds := D.act_holds
  k_fixed := fun _ hn => I.k_fixed H hn
  T₁_eq := by
    calc T₁ = A.T ⊔ (T₁ ⊓ normalizer (S.E S.y : Set X)) := T₁_eq_sup h4
      _ = A.T ⊔ (S.TE ⊔ zpowers D.v ⊔ zpowers D.w₁) := by rw [← D.T₁_eq Rl]
      _ = A.T ⊔ zpowers D.v ⊔ zpowers D.w₁ := by
          rw [← sup_assoc, ← sup_assoc, sup_eq_left.mpr (TE_le_T S)]
  R₁_le := (inf_normalizer_le h4 I).trans D.T₁_le
  Q₁_eq := rfl
  Q0_le := D.Q0_le
  Q0_invariant := fun _ hn => D.Q0_invariant Rl hn
  q0_holds := D.q0_holds Rl
  isPGroup_D₁₁ := D.isPGroup_D₁₁
  D₁₁_le := D.D₁₁_le
  C_eq := D.C_eq
  w₁_comm_C := D.w₁_comm_C'
  w₁_comm_t := D.w₁_comm_t
  C₁_le := D.C₁_le
  C₁_sup := D.C₁_sup
  card_C₁ := D.card_C₁
  card_C := D.card_C
  C₁_comm := D.C₁_comm Rl
  u_eq := D.u_eq
  u_comm_C := D.u_comm_C
  u_inv_D₁₁ := D.u_inv_D₁₁
  S₁_commutator_mem := D.S₁_commutator_mem Rl
  Q₁_char := fun h _ hn => by
    rcases q0Of_cases D.ε Rl.s1 Rl.s4 with ⟨hq, -⟩ | ⟨hq, hε, h1, -⟩ | ⟨hq, hε, -, hs4⟩ |
        ⟨hq, hε, h1, -⟩ | ⟨hq, -⟩ <;> rw [hq] at h
    · simp at h
    · exact D.Q₁_char Rl hε (Or.inl h1) hn
    · exact D.Q₁_char Rl hε (Or.inr hs4) hn
    · exact D.Q₁_char Rl hε (Or.inl h1) hn
    · simp at h
  no_conj_of := fun h => by
    rcases q0Of_cases D.ε Rl.s1 Rl.s4 with ⟨hq, hε, -, hs4⟩ | ⟨hq, hε, -, hs4⟩ | ⟨hq, -⟩ |
        ⟨hq, -⟩ | ⟨hq, -⟩ <;> rw [hq] at h
    · exact D.no_conj_one Rl hε hs4
    · exact D.no_conj_one Rl hε hs4
    · simp at h
    · simp at h
    · simp at h

end Data6

theorem exists_sec6 (h4 : S.Sec4 T₁) (I : Inst S) : Nonempty (S.Sec6 T₁ I.yi I.ki I.ui) := by
  have H := hyp_of_sec4 h4
  obtain ⟨D⟩ := I.exists_data6 H
  obtain ⟨Rl⟩ := D.nonempty_rel
  exact ⟨D.toSec6 Rl h4⟩

end Inst

end KD46

theorem fritzKDSection6 : FritzKDSection6 := by
  intro _ X _ _ _ _ _ t L A C S T₁ h4
  exact ⟨KD46.Inst.exists_sec6 h4 (KD46.inst₁ S), KD46.Inst.exists_sec6 h4 (KD46.inst₂ S)⟩

end CFSG.OddStandard.SmallF3.L33.KD
