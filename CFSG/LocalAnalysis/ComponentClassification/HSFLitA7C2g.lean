module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2e

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Case2

variable (C : S.Case2)

theorem false_of_three {a b c : X} (ha : a ∈ S.E C.ys) (hb : b ∈ S.E C.ys) (hc : c ∈ S.E C.ys)
    (hca : ConjTo S.t a) (hcb : ConjTo S.t b) (hcc : ConjTo S.t c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : False := by
  rcases (C.omega_small a ha).mp hca with h1 | h1 <;>
    rcases (C.omega_small b hb).mp hcb with h2 | h2 <;>
      rcases (C.omega_small c hc).mp hcc with h3 | h3
  all_goals first
    | exact hab (h1.trans h2.symm)
    | exact hac (h1.trans h3.symm)
    | exact hbc (h2.trans h3.symm)

include C in
theorem two_E16 {u₀ : X} (hu₀ : ConjTo S.t u₀) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPu : P ≤ centralizer ({u₀} : Set X)) {F₁ F₂ : Subgroup X} (hF₁ : F₁ ≤ P) (hF₂ : F₂ ≤ P)
    (hel₁ : ElemAbelianTwo F₁) (hel₂ : ElemAbelianTwo F₂) (hc₁ : Nat.card F₁ = 16)
    (hc₂ : Nat.card F₂ = 16) (hne : F₁ ≠ F₂)
    (h₁ : ∃ a b c, a ∈ F₁ ∧ b ∈ F₁ ∧ c ∈ F₁ ∧ ConjTo S.t a ∧ ConjTo S.t b ∧ ConjTo S.t c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (h₂ : ∃ a b c, a ∈ F₂ ∧ b ∈ F₂ ∧ c ∈ F₂ ∧ ConjTo S.t a ∧ ConjTo S.t b ∧ ConjTo S.t c ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c) : False := by
  obtain ⟨g, hg⟩ := hu₀
  set P' : Subgroup X := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'C : P' ≤ centralizer ({S.t} : Set X) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hc := mem_centralizer_singleton_iff.mp (hPu hp)
    rw [← hg] at hc
    calc g⁻¹ * p * g * S.t = g⁻¹ * (p * (g * S.t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.t * g⁻¹) * p) * g := by rw [hc]
      _ = S.t * (g⁻¹ * p * g) := by group
  obtain ⟨m, -, hmP⟩ := S.data.exists_conj_le_T (hP.map _) hP'C
  set h : X := m * g⁻¹ with hh
  have hmap : ∀ K : Subgroup X, (K.map (MulAut.conj g⁻¹).toMonoidHom).map
      (MulAut.conj m).toMonoidHom = K.map (MulAut.conj h).toMonoidHom := by
    intro K
    rw [Subgroup.map_map]
    congr 1
    ext a
    simp [hh, MulAut.conj_apply, mul_assoc]
  have hPT : P.map (MulAut.conj h).toMonoidHom ≤ S.data.T := hmap P ▸ hmP
  have himg : ∀ F : Subgroup X, F ≤ P → ElemAbelianTwo F → Nat.card F = 16 →
      F.map (MulAut.conj h).toMonoidHom = S.E S.y ∨
        F.map (MulAut.conj h).toMonoidHom = S.E (S.x * S.y) := by
    intro F hFP hel hc
    refine S.eq_E_of_elem ((Subgroup.map_mono hFP).trans hPT) ⟨?_, ?_⟩ ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hel.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hel.sq_eq_one a ha, map_one]
    · rw [card_map_of_injective (MulAut.conj h).injective, hc]
  have hne' : F₁.map (MulAut.conj h).toMonoidHom ≠ F₂.map (MulAut.conj h).toMonoidHom :=
    fun heq => hne (Subgroup.map_injective (MulAut.conj h).injective heq)
  have hsmall : ∀ F : Subgroup X, F.map (MulAut.conj h).toMonoidHom = S.E C.ys →
      (∃ a b c, a ∈ F ∧ b ∈ F ∧ c ∈ F ∧ ConjTo S.t a ∧ ConjTo S.t b ∧ ConjTo S.t c ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c) → False := by
    intro F hF ⟨a, b, c, ha, hb, hc, hca, hcb, hcc, hab, hac, hbc⟩
    have hmem : ∀ v ∈ F, h * v * h⁻¹ ∈ S.E C.ys := fun v hv => hF ▸ ⟨v, hv, rfl⟩
    have hinj : ∀ v w : X, h * v * h⁻¹ = h * w * h⁻¹ → v = w := fun v w hvw => by
      simpa using hvw
    exact C.false_of_three (hmem a ha) (hmem b hb) (hmem c hc)
      ((conjTo_conj_iff S.t a h).mpr hca) ((conjTo_conj_iff S.t b h).mpr hcb)
      ((conjTo_conj_iff S.t c h).mpr hcc) (fun e => hab (hinj _ _ e))
      (fun e => hac (hinj _ _ e)) (fun e => hbc (hinj _ _ e))
  rcases C.hy with ⟨-, hs⟩ | ⟨-, hs⟩ <;>
    rcases himg F₁ hF₁ hel₁ hc₁ with e1 | e1 <;> rcases himg F₂ hF₂ hel₂ hc₂ with e2 | e2
  · exact hne' (e1.trans e2.symm)
  · exact hsmall F₂ (e2.trans (congrArg S.E hs.symm)) h₂
  · exact hsmall F₁ (e1.trans (congrArg S.E hs.symm)) h₁
  · exact hne' (e1.trans e2.symm)
  · exact hne' (e1.trans e2.symm)
  · exact hsmall F₁ (e1.trans (congrArg S.E hs.symm)) h₁
  · exact hsmall F₂ (e2.trans (congrArg S.E hs.symm)) h₂
  · exact hne' (e1.trans e2.symm)

section V

variable {V : Subgroup X} (hT₁V : C.T₁ ≤ V) (hVN : V ≤ normalizer (S.E C.yb : Set X))
  (hVc : Nat.card V = 4 * Nat.card S.data.T) (hVp : IsPGroup 2 V)
  (hVmax : ∀ Q : Subgroup X, IsPGroup 2 Q → V ≤ Q → Q ≤ normalizer (S.E C.yb : Set X) → Q = V)
  (hVE : ∀ v ∈ V, (∀ e ∈ S.E C.yb, v * e = e * v) → v ∈ S.E C.yb)

theorem card_le_of_π {H : Subgroup X} (hHV : H ≤ V) {A : Set (Perm (Fin 4))}
    (hA : ∀ h (hh : h ∈ H), C.π (C.ofV hVN (hHV hh)) ∈ A) {B' : Set X}
    (hB : ∀ h (hh : h ∈ H), C.π (C.ofV hVN (hHV hh)) = 1 → h ∈ B') :
    Nat.card H ≤ A.ncard * B'.ncard := by
  set N := normalizer (S.E C.yb : Set X) with hN
  have hHN : H ≤ N := hHV.trans hVN
  let ρ : ↥(H.subgroupOf N) →* Perm (Fin 4) := C.π.comp (H.subgroupOf N).subtype
  have h := Subgroup.card_ker_mul_card_range ρ
  have hcardH : Nat.card ↥(H.subgroupOf N) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHN).toEquiv
  rw [hcardH] at h
  have hrange : Nat.card ρ.range ≤ A.ncard := by
    have hsub : (ρ.range : Set (Perm (Fin 4))) ⊆ A := by
      rintro _ ⟨⟨⟨g, hgN⟩, hg⟩, rfl⟩
      exact hA g hg
    calc Nat.card ρ.range = (ρ.range : Set (Perm (Fin 4))).ncard := (Nat.card_coe_set_eq _).symm
      _ ≤ A.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hker : Nat.card ρ.ker ≤ B'.ncard := by
    let f : ρ.ker → B' := fun k => ⟨((k : ↥(H.subgroupOf N)) : N), hB _ k.1.2 k.2⟩
    have hf : Function.Injective f := by
      intro k₁ k₂ hk
      have h1 := Subtype.ext_iff.mp hk
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    calc Nat.card ρ.ker ≤ Nat.card B' := Nat.card_le_card_of_injective f hf
      _ = B'.ncard := Nat.card_coe_set_eq _
  calc Nat.card H = Nat.card ρ.ker * Nat.card ρ.range := h.symm
    _ ≤ B'.ncard * A.ncard := Nat.mul_le_mul hker hrange
    _ = A.ncard * B'.ncard := mul_comm _ _

end V

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
