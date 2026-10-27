module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Cls

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open
open scoped MatrixGroups

theorem psi_spE {ψ : Sp8 ≃* Sp8} (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8} (hs : s ∈ spE) :
    ψ s ∈ spE := by
  rw [mem_spE_iff_cube] at hs ⊢
  exact ⟨(hψ s).1 hs.1, by rw [← map_pow, hs.2, map_one]⟩

theorem psi_symm_spE {ψ : Sp8 ≃* Sp8} (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {s : Sp8}
    (hs : s ∈ spE) : ψ.symm s ∈ spE := by
  rw [mem_spE_iff_cube] at hs ⊢
  refine ⟨?_, by rw [← map_pow, hs.2, map_one]⟩
  rw [hψ, MulEquiv.apply_symm_apply]
  exact hs.1

theorem psi_wrp_slD {ψ : Sp8 ≃* Sp8} (hψ : ∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) {n : Sp8}
    (hn : n ∈ wrp slD) : ψ n ∈ wrp slD := by
  rw [wrp_eq_normalizer] at hn ⊢
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro t
  have h1 := hn (ψ.symm t)
  have h2 : t ∈ spT0 ↔ ψ.symm t ∈ spT0 := by
    rw [hψ (ψ.symm t), MulEquiv.apply_symm_apply]
  have h3 : n * ψ.symm t * n⁻¹ ∈ spT0 ↔ ψ n * t * (ψ n)⁻¹ ∈ spT0 := by
    rw [hψ (n * ψ.symm t * n⁻¹), map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact h2.trans (h1.trans h3)

theorem nonsolv_classify {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    {e : K ≃* Sp8} {T : Subgroup Y} {y : Y} (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    (hsimple : IsSimpleGroup Sp8) {Y₀ : Subgroup Y}
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀) (hY₀ : Y₀ ≠ ⊤)
    (hns : ¬ Group.IsSolvable Y₀) :
    ∃ θ ψ : Sp8 ≃* Sp8, (∀ x, x ∈ spT0 ↔ θ x ∈ spT0) ∧ θ spZ1 = spZ12 ∧
      (∀ x, x ∈ spT0 ↔ ψ x ∈ spT0) ∧
      Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom := by
  obtain ⟨θ, hθT, hθz, hcl⟩ := classify_comap hcard hsimple hNE hY₀
  rcases hcl with h | h | h
  · exact absurd (S.solvable_of_comap_eq hC hcard h) hns
  · refine ⟨θ, MulEquiv.refl Sp8, hθT, hθz, fun x => Iff.rfl, ?_⟩
    rw [h]
    exact (Subgroup.map_id _).symm
  · exact ⟨θ, θ, hθT, hθz, hθT, h⟩

section NS

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {e : K ≃* Sp8}
  {T : Subgroup Y} {y : Y}

@[expose] def fpsi (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Sp8 →* Y := (emb e).comp ψ.toMonoidHom

omit [K.Normal] in
theorem fpsi_apply (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) (x : Sp8) : fpsi e ψ x = emb e (ψ x) := rfl

omit [K.Normal] in
theorem fpsi_injective (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) : Function.Injective (fpsi e ψ) :=
  (emb_injective e).comp ψ.injective

@[expose] noncomputable def omg (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) (g : Y) : Sp8 ≃* Sp8 :=
  ψ.trans ((adHom K e g).trans ψ.symm)

theorem fpsi_omg (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) (g : Y) (x : Sp8) :
    fpsi e ψ (omg e ψ g x) = g * fpsi e ψ x * g⁻¹ := by
  rw [fpsi_apply, fpsi_apply]
  show emb e (ψ (ψ.symm (adHom K e g (ψ x)))) = _
  rw [MulEquiv.apply_symm_apply, emb_adHom]

theorem conj_map_fpsi (e : K ≃* Sp8) (ψ : Sp8 ≃* Sp8) (g : Y) (A : Subgroup Sp8) :
    (A.map (fpsi e ψ)).map (MulAut.conj g).toMonoidHom =
      (A.map (omg e ψ g).toMonoidHom).map (fpsi e ψ) := by
  ext t
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨omg e ψ g a, ⟨a, ha, rfl⟩, by
      show fpsi e ψ (omg e ψ g a) = g * fpsi e ψ a * g⁻¹
      exact fpsi_omg e ψ g a⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨fpsi e ψ a, ⟨a, ha, rfl⟩, by
      show g * fpsi e ψ a * g⁻¹ = fpsi e ψ (omg e ψ g a)
      exact (fpsi_omg e ψ g a).symm⟩

theorem mem_normalizer_of_map_conj {H : Subgroup Y} {g : Y}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    rw [← h]
    exact ⟨t, ht, rfl⟩
  · intro ht
    rw [← h] at ht
    obtain ⟨t', ht', hc⟩ := ht
    have : t' = t := by
      have h' : g * t' * g⁻¹ = g * t * g⁻¹ := hc
      simpa using h'
    rwa [← this]

variable {ψ : Sp8 ≃* Sp8} {Y₀ : Subgroup Y}

theorem omg_wrp_top (hcl : Y₀.comap (emb e) = (wrp (⊤ : Subgroup Sl28)).map ψ.toMonoidHom)
    {g : Y} (hg : g ∈ Y₀) :
    (wrp (⊤ : Subgroup Sl28)).map (omg e ψ g).toMonoidHom = wrp (⊤ : Subgroup Sl28) := by
  have hle : (wrp (⊤ : Subgroup Sl28)).map (omg e ψ g).toMonoidHom ≤ wrp (⊤ : Subgroup Sl28) := by
    rintro _ ⟨m, hm, rfl⟩
    have h1 : fpsi e ψ m ∈ Y₀ := by
      have : ψ m ∈ Y₀.comap (emb e) := by rw [hcl]; exact ⟨m, hm, rfl⟩
      exact this
    have h2 : fpsi e ψ (omg e ψ g m) ∈ Y₀ := by
      rw [fpsi_omg]
      exact Y₀.mul_mem (Y₀.mul_mem hg h1) (Y₀.inv_mem hg)
    have h3 : ψ (omg e ψ g m) ∈ Y₀.comap (emb e) := h2
    rw [hcl] at h3
    obtain ⟨m', hm', hmm⟩ := h3
    have : m' = omg e ψ g m := ψ.injective hmm
    show omg e ψ g m ∈ wrp (⊤ : Subgroup Sl28)
    rw [← this]
    exact hm'
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (omg e ψ g).injective])

omit [K.Normal] in
theorem wrp_le_comap [Finite Y]
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀) :
    wrp slD ≤ Y₀.comap (emb e) := fun _ hn => hNE (emb_mem_normalizer_E hn)

theorem Sp48Setup.comap_ne_bot [Finite Y] (S : Sp48Setup e T y)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    (hNE : Subgroup.normalizer ((spE.map (emb e) : Subgroup Y) : Set Y) ≤ Y₀)
    {W : Subgroup Y} (hn : Y₀ ≤ Subgroup.normalizer (W : Set Y)) (hW : W ≠ ⊥) :
    W.comap (emb e) ≠ ⊥ := by
  intro h
  apply hW
  rw [eq_bot_iff]
  intro w hw
  have hHp := wrp_le_comap hNE
  have hcomm : ∀ s ∈ Y₀.comap (emb e), w * emb e s = emb e s * w := by
    intro s hs
    have h1 : emb e s * w * (emb e s)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.1 (hn hs) w).1 hw
    have h2 : (emb e s * w * (emb e s)⁻¹) * w⁻¹ ∈ W := W.mul_mem h1 (W.inv_mem hw)
    have h3 : (emb e s * w * (emb e s)⁻¹) * w⁻¹ ∈ K := by
      have : (emb e s * w * (emb e s)⁻¹) * w⁻¹ = emb e s * (w * (emb e s)⁻¹ * w⁻¹) := by group
      rw [this]
      exact K.mul_mem (emb_mem e s)
        (Subgroup.Normal.conj_mem (inferInstance : K.Normal) _ (K.inv_mem (emb_mem e s)) w)
    obtain ⟨k, hk⟩ := exists_emb e h3
    have hk1 : k ∈ W.comap (emb e) := by
      show emb e k ∈ W
      rw [hk]
      exact h2
    rw [h, Subgroup.mem_bot] at hk1
    rw [hk1, map_one] at hk
    have : emb e s * w * (emb e s)⁻¹ = w := by
      calc emb e s * w * (emb e s)⁻¹ = ((emb e s * w * (emb e s)⁻¹) * w⁻¹) * w := by group
        _ = w := by rw [← hk]; group
    calc w * emb e s = (emb e s * w * (emb e s)⁻¹) * emb e s := by rw [this]
      _ = emb e s * w := by group
  have hwT : w ∈ T := by
    refine S.cent_E_le hC fun z hz => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    exact hcomm s (hHp (spT0_le_wrp (spE_le_spT0 hs)))
  obtain ⟨k, hk, hwk⟩ := S.cent_T0 hwT fun s hs => hcomm s (hHp (spT0_le_wrp hs))
  have hk1 : k ∈ W.comap (emb e) := by
    show emb e k ∈ W
    rw [← hwk]
    exact hw
  rw [h, Subgroup.mem_bot] at hk1
  rw [hwk, hk1, map_one]
  exact Subgroup.one_mem _

end NS

end CFSG.AGLEmbedding.KFactProofs.Sp48
