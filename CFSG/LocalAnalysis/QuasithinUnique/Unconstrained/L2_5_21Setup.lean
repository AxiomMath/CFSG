module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Facts

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Reduction

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.hKH (h : Lv2520 N t zK) : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
  have h1 := N.H_le_normalizer_K0
  rw [h.concl2520] at h1
  exact h1

theorem Lv2520.mem_SC_of_commutes (h : Lv2520 N t zK) {c : G} (hc : c ∈ N.H)
    (hcK : ∀ f ∈ N.K, c * f = f * c) : c ∈ N.SC := by
  have hS : c ∈ N.S := N.mem_S_of_centralizes h.hKH h.facts254
    (fun x hx hcx => N.center_K_trivial h.facts258.simple hx hcx) hc hcK
  refine ⟨hS, ?_⟩
  rw [h.concl2520]
  exact Subgroup.mem_centralizer_iff.mpr fun f hf => (hcK f hf).symm

theorem Lv2520.SC_commutes (h : Lv2520 N t zK) {c : G} (hc : c ∈ N.SC) :
    ∀ f ∈ N.K, c * f = f * c := by
  intro f hf
  have h1 := hc.2
  rw [h.concl2520] at h1
  exact (Subgroup.mem_centralizer_iff.mp h1 f hf).symm

theorem Lv2520.K_inf_SC (h : Lv2520 N t zK) : N.K ⊓ N.SC = ⊥ := by
  have h1 := h.facts258.K0_inf_SC
  rw [h.concl2520] at h1
  exact h1

theorem concl2521_of_autA6 (h : Lv2520 N t zK) (e6 : ↥N.K ≃* alternatingGroup (Fin 6))
    (ψ₀ : ↥(autOn N.H N.K) ≃* ↥A6Models.autA6) : Concl2521 N := by
  have hKH := h.hKH
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hcard : Nat.card ↥N.K = 360 := by
    rw [Nat.card_congr e6.toEquiv]
    exact Unc25K1.card_alt_six
  let Φ : ↥N.H →* ↥A6Models.autA6 := ψ₀.toMonoidHom.comp (N.actHom hKH)
  have hsurj : Function.Surjective Φ := ψ₀.surjective.comp (N.actHom_surjective hKH)
  have hker : ∀ x : ↥N.H, Φ x = 1 ↔ ∀ k ∈ N.K, (x : G) * k = k * (x : G) := by
    intro x
    have hx : Φ x = ψ₀ (N.actHom hKH x) := rfl
    rw [hx, ← N.actHom_eq_one_iff hKH x]
    exact map_eq_one_iff _ ψ₀.injective
  obtain ⟨hmem, hsurjK⟩ := K_part N hKH hsimple hZ hcard Φ hsurj hker
  let φ₀ : ↥N.K →* ↥A6Models.psl29 :=
    { toFun := fun k => ⟨((Φ ⟨k, N.K_le_H k.2⟩ : ↥A6Models.autA6) : Equiv.Perm (Fin 10)),
        hmem ⟨k, N.K_le_H k.2⟩ k.2⟩
      map_one' := by
        apply Subtype.ext
        show ((Φ ⟨(1 : ↥N.K), N.K_le_H (1 : ↥N.K).2⟩ : ↥A6Models.autA6) : Equiv.Perm (Fin 10)) = 1
        have : (⟨((1 : ↥N.K) : G), N.K_le_H (1 : ↥N.K).2⟩ : ↥N.H) = 1 := rfl
        rw [this, map_one]; rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        show ((Φ ⟨((a * b : ↥N.K) : G), N.K_le_H (a * b).2⟩ : ↥A6Models.autA6) :
          Equiv.Perm (Fin 10)) = _
        have : (⟨((a * b : ↥N.K) : G), N.K_le_H (a * b).2⟩ : ↥N.H) =
            ⟨(a : G), N.K_le_H a.2⟩ * ⟨(b : G), N.K_le_H b.2⟩ := rfl
        rw [this, map_mul]; rfl }
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have h1 : Φ ⟨(k : G), N.K_le_H k.2⟩ = 1 := by
      apply Subtype.ext
      have h2 : ((φ₀ k : ↥A6Models.psl29) : Equiv.Perm (Fin 10)) = 1 := by rw [hk]; rfl
      exact h2
    rw [hker] at h1
    apply Subtype.ext
    exact hZ _ k.2 (fun y hy => h1 y hy)
  have hsurj' : Function.Surjective φ₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxK, hx⟩ := hsurjK y hy
    refine ⟨⟨(x : G), hxK⟩, ?_⟩
    apply Subtype.ext
    exact hx
  refine ⟨⟨e6⟩, MulEquiv.ofBijective φ₀ ⟨hinj, hsurj'⟩, ψ₀, ?_⟩
  intro k hk
  have : N.actHom hKH ⟨(k : G), N.K_le_H k.2⟩ =
      ⟨conjAct N.K ⟨(k : G), Subgroup.le_normalizer k.2⟩, hk⟩ := Subtype.ext rfl
  show ((ψ₀ ⟨conjAct N.K ⟨(k : G), Subgroup.le_normalizer k.2⟩, hk⟩ : ↥A6Models.autA6) :
    Equiv.Perm (Fin 10)) = ((Φ ⟨(k : G), N.K_le_H k.2⟩ : ↥A6Models.autA6) : Equiv.Perm (Fin 10))
  rw [← this]
  rfl

end Reduction

@[expose] def Lemma2521Out : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G), Lv2520 N t zK → OutFamily N.K N.H → False

theorem lemma2521_of_out (hout : Lemma2521Out) : Lemma2521 := by
  intro G _ _ T M hs N t zK h
  have h2516 := h.concl2516
  rcases h2516 with ⟨p, hp, h7, hmodel⟩ | ⟨hmodel, -⟩ | ⟨⟨e6⟩, hH | hH | hH⟩
  · exact (hout G T M hs N t zK h (Or.inl (Or.inl ⟨p, hp, h7, hmodel⟩))).elim
  · exact (hout G T M hs N t zK h (Or.inl (Or.inr hmodel))).elim
  · exact (hout G T M hs N t zK h (Or.inr ⟨⟨e6⟩, Or.inl hH⟩)).elim
  · exact (hout G T M hs N t zK h (Or.inr ⟨⟨e6⟩, Or.inr hH⟩)).elim
  · obtain ⟨ψ₀⟩ := hH
    exact concl2521_of_autA6 h e6 ψ₀

end CFSG.QuasithinUnique
