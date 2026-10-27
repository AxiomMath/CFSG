module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBSylowA

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8.MB

theorem inE1_mul_t : ∀ e : MB, inE0 e = true → inE1 (e * t) = true := by decide +kernel

theorem E0L_nodup : E0L.Nodup := by decide +kernel

theorem E0L_length : E0L.length = 8 := rfl

theorem k_not_Z2L : k ∉ Z2L := by decide +kernel

theorem y_not_one : y ≠ 1 := by decide +kernel

theorem y_ne_z : y ≠ z := by decide +kernel

theorem E0L_rest : ∀ e ∈ E0L, e ∉ [1, z, y, z * y] → e ∈ [k, z * k, y * k, z * y * k] := by
  decide +kernel

theorem ZY_sub_Z2L : ∀ e ∈ [1, z, y, z * y], e ∈ Z2L := by decide +kernel

theorem H4elt_length {p : ℕ × ℕ} (hp : p ∈ goodIdx) (s : MB) (a b : Bool) :
    (H4elt p s a b).length = 7 := by
  cases b
  · simp [H4elt, compQ1, gensQ1_length]
  · simp [H4elt, compQ1, g0Q_length p hp]

end Sec8.MB

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable {B : BData S T₁}

theorem ActsQ1.eq_list {g : X} {f f' : List MB} (hf : B.ActsQ1 g f) (hf' : B.ActsQ1 g f')
    (hl : f.length = 7) (hl' : f'.length = 7) : f = f' := by
  rw [← MB.applyQ1_gens f hl, ← MB.applyQ1_gens f' hl']
  exact List.map_congr_left fun x hx =>
    hf.eq_of_actsAs hf' (ActsAs.refl _ _) x (MB.gensQ1_mem x hx)

theorem mem_normalizer_E₁ {g : X}
    (hE : ∀ e : MB, MB.inE0 e = true → ∃ e' : MB, MB.inE0 e' = true ∧ g * B.ι e * g⁻¹ = B.ι e')
    (ht : ∃ e : MB, MB.inE0 e = true ∧ g * t * g⁻¹ = B.ι e * t) :
    g ∈ normalizer (S.E S.y : Set X) := by
  refine mem_normalizer_of_conj_le fun x hx => ?_
  obtain ⟨x', hx', rfl⟩ := B.mem_E₁_iff.mp hx
  obtain ⟨bs, -, rfl⟩ := MB.E1h_span x' hx'
  have e1 : g * B.ι (Sec8.nfProd [MB.z, MB.y, MB.t, MB.k] bs) * g⁻¹ =
      Sec8.nfProd ([MB.z, MB.y, MB.t, MB.k].map fun a => g * B.ι a * g⁻¹) bs :=
    map_nfProd ((MulAut.conj g).toMonoidHom.comp B.ι) _ _
  rw [e1]
  refine nfProd_mem _ _ fun g' hg' => ?_
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hg'
  have hE0 : ∀ a : MB, MB.inE0 a = true → g * B.ι a * g⁻¹ ∈ S.E S.y := fun a ha => by
    obtain ⟨e', he', hee⟩ := hE a ha
    rw [hee]
    exact B.ι_mem_E₁ (MB.inE1_of_inE0 e' he')
  rcases hg' with rfl | rfl | rfl | rfl
  · exact hE0 MB.z (by decide +kernel)
  · exact hE0 MB.y (by decide +kernel)
  · obtain ⟨e, he, hee⟩ := ht
    rw [B.ι_t, hee, show B.ι e * t = B.ι (e * MB.t) by rw [map_mul, B.ι_t]]
    exact B.ι_mem_E₁ (MB.inE1_mul_t e he)
  · exact hE0 MB.k (by decide +kernel)

namespace T2Data

variable (D : B.T2Data)

theorem actsQ1_lift_mul {τ : MB × Bool × Bool} {e : MB} (he : MB.inE0 e = true) :
    B.ActsQ1 (D.lift τ * B.ι e) (MB.H4elt D.p τ.1 τ.2.1 τ.2.2) := fun y hy => by
  rw [show D.lift τ * B.ι e * B.ι y * (D.lift τ * B.ι e)⁻¹ =
    D.lift τ * (B.ι e * B.ι y * (B.ι e)⁻¹) * (D.lift τ)⁻¹ by group, ← map_inv, ← map_mul,
    ← map_mul, ← MB.E0_comm_Q1 y hy e ((MB.mem_E0L e).mp he), mul_inv_cancel_right]
  exact D.actsQ1_lift τ y hy

theorem card_ge_of_lifts (K : Subgroup X) (L : List ((MB × Bool × Bool) × List MB))
    (hL : ∀ e ∈ L, e ∈ MB.H4Zof D.p) (hnd : (L.map Prod.snd).Nodup)
    (hlift : ∀ e ∈ L, D.lift e.1 ∈ K) (hE : ∀ e ∈ MB.E0L, B.ι e ∈ K) :
    8 * L.length ≤ Nat.card K := by
  classical
  set s := L.toFinset ×ˢ MB.E0L.toFinset with hs
  have hcard : s.card = L.length * 8 := by
    rw [hs, Finset.card_product, List.toFinset_card_of_nodup (hnd.of_map _),
      List.toFinset_card_of_nodup MB.E0L_nodup, MB.E0L_length]
  have hmem : ∀ x : s, x.1.1 ∈ L ∧ x.1.2 ∈ MB.E0L := fun x => by
    have := Finset.mem_product.mp x.2
    exact ⟨List.mem_toFinset.mp this.1, List.mem_toFinset.mp this.2⟩
  let f : s → K := fun x =>
    ⟨D.lift x.1.1.1 * B.ι x.1.2, mul_mem (hlift _ (hmem x).1) (hE _ (hmem x).2)⟩
  have hf : Function.Injective f := by
    intro x₁ x₂ heq
    have heq' : D.lift x₁.1.1.1 * B.ι x₁.1.2 = D.lift x₂.1.1.1 * B.ι x₂.1.2 :=
      congrArg Subtype.val heq
    obtain ⟨h1L, h1E⟩ := hmem x₁
    obtain ⟨h2L, h2E⟩ := hmem x₂
    have s1 := MB.mem_H4Zof_spec D.hp (hL _ h1L)
    have s2 := MB.mem_H4Zof_spec D.hp (hL _ h2L)
    have a1 := D.actsQ1_lift_mul (τ := x₁.1.1.1) ((MB.mem_E0L _).mpr h1E)
    have a2 := D.actsQ1_lift_mul (τ := x₂.1.1.1) ((MB.mem_E0L _).mpr h2E)
    rw [heq'] at a1
    have hφ : x₁.1.1.2 = x₂.1.1.2 := by
      rw [s1.2, s2.2]
      exact a1.eq_list a2 (MB.H4elt_length D.hp _ _ _) (MB.H4elt_length D.hp _ _ _)
    have h12 : x₁.1.1 = x₂.1.1 := List.inj_on_of_nodup_map hnd h1L h2L hφ
    rw [h12, mul_right_inj] at heq'
    exact Subtype.ext (Prod.ext h12 (B.ι_injective heq'))
  calc 8 * L.length = s.card := by rw [hcard, mul_comm]
    _ = Nat.card s := (Nat.card_eq_finsetCard s).symm
    _ ≤ Nat.card K := Nat.card_le_card_of_injective f hf

theorem exists_E0_match {g : X} (hg : g ∈ normalizer (D.T2 : Set X)) :
    ∃ i : Fin 8, ∀ e : MB, MB.inE0 e = true →
      (D.lift (MB.E0tau i))⁻¹ * g * B.ι e * ((D.lift (MB.E0tau i))⁻¹ * g)⁻¹ = B.ι e := by
  have hgi : g⁻¹ ∈ normalizer (D.T2 : Set X) := inv_mem hg
  have hz : g * B.ι MB.z * g⁻¹ = B.ι MB.z := by rw [B.ι_z]; exact D.conj_z hg
  obtain ⟨y', hy'E, hy'⟩ := D.conj_E0 hg (e := MB.y) (by decide +kernel)
  obtain ⟨y'', hy''Z, hy''⟩ := D.conj_Z2 hg (x := MB.y) (by decide +kernel)
  have hyy : y' = y'' := B.ι_injective (by rw [← hy', hy''])
  subst hyy
  have hy'4 := MB.Z2L_E0 y' hy''Z hy'E
  have hy'1 : y' ≠ 1 := by
    rintro rfl
    rw [map_one] at hy'
    exact MB.y_not_one (B.ι_injective (by
      rw [map_one]
      calc B.ι MB.y = g⁻¹ * (g * B.ι MB.y * g⁻¹) * g := by group
        _ = 1 := by rw [hy']; group))
  have hy'z : y' ≠ MB.z := by
    rintro rfl
    rw [← hz] at hy'
    exact MB.y_ne_z (B.ι_injective (by
      calc B.ι MB.y = g⁻¹ * (g * B.ι MB.y * g⁻¹) * g := by group
        _ = g⁻¹ * (g * B.ι MB.z * g⁻¹) * g := by rw [hy']
        _ = B.ι MB.z := by group))
  have hy'2 : y' ∈ [MB.y, MB.z * MB.y] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy'4 ⊢
    rcases hy'4 with h | h | h | h
    · exact absurd h hy'1
    · exact absurd h hy'z
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨k', hk'E, hk'⟩ := D.conj_E0 hg (e := MB.k) (by decide +kernel)
  have hk'2 : k' ∈ [MB.k, MB.z * MB.k, MB.y * MB.k, MB.z * MB.y * MB.k] := by
    refine MB.E0L_rest k' ((MB.mem_E0L k').mp hk'E) fun hk4 => ?_
    obtain ⟨k'', hk'', hke⟩ := D.conj_Z2 hgi (MB.ZY_sub_Z2L k' hk4)
    apply MB.k_not_Z2L
    have : MB.k = k'' := B.ι_injective (by
      rw [← hke, ← hk']
      group)
    rw [this]
    exact hk''
  obtain ⟨i, hiy, hik⟩ := MB.E0_cover y' hy'2 k' hk'2
  refine ⟨i, ?_⟩
  set r := D.lift (MB.E0tau i) with hr
  have hrT : r ∈ D.T2 := D.lift_mem_T2 _
  have hact := D.actsQ1_lift (MB.E0tau i)
  obtain ⟨h1, h2⟩ := MB.E0tau_facts D.p D.hp i
  have hry : r * B.ι MB.y * r⁻¹ = B.ι y' := by
    rw [hact MB.y (by decide +kernel), h1, hiy]
  have hrk : r * B.ι MB.k * r⁻¹ = B.ι k' := by
    rw [hact MB.k (by decide +kernel), h2, hik]
  have hrz : r * B.ι MB.z * r⁻¹ = B.ι MB.z := by rw [B.ι_z]; exact D.conj_z_T2 hrT
  have hfix : ∀ a : MB, (g * B.ι a * g⁻¹ = r * B.ι a * r⁻¹) →
      r⁻¹ * g * B.ι a * (r⁻¹ * g)⁻¹ = B.ι a := fun a ha => by
    calc r⁻¹ * g * B.ι a * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * B.ι a * g⁻¹) * r := by group
      _ = B.ι a := by rw [ha]; group
  have hz' := hfix MB.z (by rw [hz, hrz])
  have hy3 := hfix MB.y (by rw [hy', hry])
  have hk3 := hfix MB.k (by rw [hk', hrk])
  have hmul : ∀ a b : MB, r⁻¹ * g * B.ι a * (r⁻¹ * g)⁻¹ = B.ι a →
      r⁻¹ * g * B.ι b * (r⁻¹ * g)⁻¹ = B.ι b →
      r⁻¹ * g * B.ι (a * b) * (r⁻¹ * g)⁻¹ = B.ι (a * b) := fun a b ha hb => by
    calc r⁻¹ * g * B.ι (a * b) * (r⁻¹ * g)⁻¹ =
        (r⁻¹ * g * B.ι a * (r⁻¹ * g)⁻¹) * (r⁻¹ * g * B.ι b * (r⁻¹ * g)⁻¹) := by
          rw [map_mul]; group
      _ = B.ι (a * b) := by rw [ha, hb, map_mul]
  intro e he
  rcases MB.E0L_gen e ((MB.mem_E0L e).mp he) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hz'
  · exact hy3
  · exact hmul _ _ hz' hy3
  · exact hk3
  · exact hmul _ _ hz' hk3
  · exact hmul _ _ hy3 hk3
  · exact hmul _ _ (hmul _ _ hz' hy3) hk3

end T2Data

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
