module

public import CFSG.LargeExtraspecial.O62WeakCheck
public import CFSG.LargeExtraspecial.O62Rank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.O62

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Code Check

@[expose] def WeakClosed {G : Type*} [Group G] (H E : Subgroup G) : Prop :=
  ∀ k ∈ H, (∀ e ∈ E, ∀ f ∈ E, k * e * k⁻¹ * f * (k * e * k⁻¹)⁻¹ ∈ E) →
    ∀ e ∈ E, k * e * k⁻¹ ∈ E

theorem weakClosed_of {G : Type*} [Group G] {H E : Subgroup G} (hinv : ∀ x ∈ E, x ^ 2 = 1)
    (hwc : ∀ h ∈ H, E.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (E : Set G) →
      E.map (MulAut.conj h).toMonoidHom = E) : WeakClosed H E := by
  intro k hk hn e he
  have hle : E.map (MulAut.conj k).toMonoidHom ≤ Subgroup.normalizer (E : Set G) := by
    rintro _ ⟨e', he', rfl⟩
    have hy : (MulAut.conj k).toMonoidHom e' = k * e' * k⁻¹ := rfl
    rw [hy, Subgroup.mem_normalizer_iff]
    intro f
    have hyy : (k * e' * k⁻¹) * (k * e' * k⁻¹) = 1 := by
      have := hinv e' he'
      rw [pow_two] at this
      calc (k * e' * k⁻¹) * (k * e' * k⁻¹) = k * (e' * e') * k⁻¹ := by group
        _ = 1 := by rw [this, mul_one, mul_inv_cancel]
    have hyinv : (k * e' * k⁻¹)⁻¹ = k * e' * k⁻¹ := inv_eq_of_mul_eq_one_right hyy
    constructor
    · exact hn e' he' f
    · intro hf
      have h := hn e' he' _ hf
      rw [hyinv] at h
      have e1 : k * e' * k⁻¹ * (k * e' * k⁻¹ * f * (k * e' * k⁻¹)) * (k * e' * k⁻¹) = f := by
        calc _ = (k * e' * k⁻¹ * (k * e' * k⁻¹)) * f * (k * e' * k⁻¹ * (k * e' * k⁻¹)) := by
              group
          _ = f := by rw [hyy, one_mul, mul_one]
      rwa [e1] at h
  have h := hwc k hk hle
  rw [← h]
  exact ⟨e, he, rfl⟩

theorem WeakClosed.map {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {H E : Subgroup G}
    (h : WeakClosed H E) : WeakClosed (H.map φ.toMonoidHom) (E.map φ.toMonoidHom) := by
  intro k hk hn e he
  rw [Subgroup.mem_map_equiv] at hk he ⊢
  have hn' : ∀ e ∈ E, ∀ f ∈ E, φ.symm k * e * (φ.symm k)⁻¹ * f *
      (φ.symm k * e * (φ.symm k)⁻¹)⁻¹ ∈ E := by
    intro e₁ he₁ f hf
    have h1 := hn (φ e₁) (by rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]; exact he₁)
      (φ f) (by rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]; exact hf)
    rw [Subgroup.mem_map_equiv] at h1
    simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h1
  have h1 := h _ hk hn' _ he
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h1

theorem eq_omegaGroup_or_eq_orthogonalGroup {minus : Bool} {H : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (h1 : Ω₀ minus ≤ H) (h2 : H ≤ O₀ minus) : H = Ω₀ minus ∨ H = O₀ minus := by
  have : Nontrivial V₀ := inferInstance
  have hrel := relIndex_omegaGroup (qModel minus) (qModel_nondegenerate minus)
  rw [← Subgroup.relIndex_mul_relIndex _ _ _ h1 h2] at hrel
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ hrel) with h | h
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h) h1
  · right
    rw [h] at hrel
    have h' : H.relIndex (O₀ minus) = 1 := by omega
    exact le_antisymm h2 (Subgroup.relIndex_eq_one.mp h')

theorem conj_mem_omega {minus : Bool} {g x : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ O₀ minus)
    (hx : x ∈ Ω₀ minus) : g * x * g⁻¹ ∈ Ω₀ minus := by
  have hL : ∀ v, qModel minus (g v) = qModel minus v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have h := (mem_omegaGroup_conjL (qModel_nondegenerate minus) (qModel_nondegenerate minus)
    hL (g := x)).mpr hx
  have e : conjL g x = g * x * g⁻¹ := LinearEquiv.ext fun v => rfl
  rwa [e] at h

theorem exists_coded_of_mem_left {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded gs cs) {g : V₀ ≃ₗ[ZMod 2] V₀} (hg : g ∈ gs) :
    ∃ c ∈ cs, Coded g c := by
  induction h with
  | nil => simp at hg
  | cons hab _ ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨c, hc, hgc⟩ := ih hg
      exact ⟨c, List.mem_cons_of_mem _ hc, hgc⟩

theorem exists_coded_of_mem_right {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded gs cs) {c : ℕ} (hc : c ∈ cs) : ∃ g ∈ gs, Coded g c := by
  induction h with
  | nil => simp at hc
  | cons hab _ ih =>
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨g, hg, hgc⟩ := ih hc
      exact ⟨g, List.mem_cons_of_mem _ hg, hgc⟩

theorem nodup_of_forall₂ {gs : List (V₀ ≃ₗ[ZMod 2] V₀)} {cs : List ℕ}
    (h : List.Forall₂ Coded gs cs) (hnd : cs.Nodup) : gs.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | cons hab hrest ih =>
    rw [List.nodup_cons] at hnd ⊢
    exact ⟨fun hmem => hnd.1 ((mem_iff_of_forall₂ hrest hab).mp hmem), ih hnd.2⟩

theorem forall_mem_of_nodup {G : Type*} [Group G] [Finite G] {E : Subgroup G} {l : List G}
    (hl : l.Nodup) (hsub : ∀ g ∈ l, g ∈ E) (hcard : Nat.card E ≤ l.length) :
    ∀ e ∈ E, e ∈ l := by
  classical
  intro e he
  by_contra hne
  have hsub' : (↑(insert e l.toFinset) : Set G) ⊆ (E : Set G) := by
    intro x hx
    rw [Finset.coe_insert, Set.mem_insert_iff, List.coe_toFinset] at hx
    rcases hx with rfl | hx
    · exact he
    · exact hsub x hx
  have h1 := Set.ncard_le_ncard hsub' (Set.toFinite _)
  rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simpa using hne),
    List.toFinset_card_of_nodup hl, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h1
  omega

theorem weaklyClosed_core
    {minus : Bool} {H E : Subgroup (V₀ ≃ₗ[ZMod 2] V₀)}
    (h1 : Ω₀ minus ≤ H) (h2 : H ≤ O₀ minus) (hEH : E ≤ H) (hET : E ≤ sylowT minus)
    (hE8 : Nat.card E = 8) (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hinv : ∀ x ∈ E, x ^ 2 = 1) (hwc : WeakClosed H E) : minus = false ∧ E ≤ Ω₀ minus := by
  have := finite_linearEquiv (V := V₀)
  obtain ⟨x, hx, hnx⟩ := exists_mem_not_mem_spanG (P := E) [] (by rw [hE8]; norm_num)
  obtain ⟨y, hy, hny⟩ := exists_mem_not_mem_spanG (P := E) [x] (by rw [hE8]; norm_num)
  obtain ⟨z, hz, hnz⟩ := exists_mem_not_mem_spanG (P := E) [y, x] (by rw [hE8]; norm_num)
  obtain ⟨a, ha, rfl⟩ := mem_sylowT.mp (hET hx)
  obtain ⟨b, hb, rfl⟩ := mem_sylowT.mp (hET hy)
  obtain ⟨c, hc, rfl⟩ := mem_sylowT.mp (hET hz)
  have hne : ∀ {g : V₀ ≃ₗ[ZMod 2] V₀} {xs : List (V₀ ≃ₗ[ZMod 2] V₀)}, g ∉ spanG xs → g ≠ 1 :=
    fun hn h => hn (h ▸ one_mem_spanG _)
  have ca := coded_wordProd a
  have cb := coded_wordProd b
  have cc := coded_wordProd c
  have kab := comm_of_coded ca cb (hab _ hx _ hy)
  have kac := comm_of_coded ca cc (hab _ hx _ hz)
  have kbc := comm_of_coded cb cc (hab _ hy _ hz)
  have F₁ : List.Forall₂ Coded [wordProd a] [wordC a] := .cons ca .nil
  have F₂ : List.Forall₂ Coded [wordProd b, wordProd a] [wordC b, wordC a] := .cons cb F₁
  have F₃ : List.Forall₂ Coded [wordProd c, wordProd b, wordProd a]
      [wordC c, wordC b, wordC a] := .cons cc F₂
  have nyx := not_mem_spanC_of_coded F₁ cb hny
  have nzyx := not_mem_spanC_of_coded F₂ cc hnz
  obtain ⟨hnd, hres⟩ := wcTriple_spec kab kac kbc nyx nzyx (wcTriple_eq_true ha hb hc
    (isInv_of_coded ca (hinv _ hx) (hne hnx)) (isInv_of_coded cb (hinv _ hy) (hne hny))
    (isInv_of_coded cc (hinv _ hz) (hne hnz)) kab nyx)
  have hFS := forall₂_spanG F₃
  have hndG := nodup_of_forall₂ hFS hnd
  have hSE : ∀ g ∈ spanG [wordProd c, wordProd b, wordProd a], g ∈ E := by
    refine spanG_subset fun g hg => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> assumption
  have hES : ∀ e ∈ E, e ∈ spanG [wordProd c, wordProd b, wordProd a] :=
    forall_mem_of_nodup hndG hSE (by rw [hE8, length_spanG]; rfl)
  have hlet := fun w (hw : w ∈ sylowWords minus) => (checkSylow_spec minus).1 w hw
  have hΩw : ∀ w ∈ sylowWords minus, w.length % 2 = 0 → wordProd w ∈ Ω₀ minus :=
    fun w hw hev => (wordProd_mem_omegaGroup_iff (hlet w hw)).mpr (Nat.even_iff.mpr hev)
  rcases hres with ⟨hm, hea, heb, hec⟩ | ⟨p, -, hplet, hpev, hok⟩
  · refine ⟨hm, fun e he => spanG_subset (E := Ω₀ minus) (fun g hg => ?_) e (hES e he)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact hΩw c hc hec
    · exact hΩw b hb heb
    · exact hΩw a ha hea
  · exfalso
    have hkH : wordProd p.2 ∈ H := by
      rcases eq_omegaGroup_or_eq_orthogonalGroup h1 h2 with hH | hH
      · have hΩ : ∀ w ∈ sylowWords minus, wordProd w ∈ E → w.length % 2 = 0 :=
          fun w hw hwE => by
            have hwH := hEH hwE
            rw [hH] at hwH
            exact Nat.even_iff.mp ((wordProd_mem_omegaGroup_iff (hlet w hw)).mp hwH)
        exact h1 ((wordProd_mem_omegaGroup_iff hplet).mpr
          (Nat.even_iff.mpr (hpev ⟨hΩ a ha hx, hΩ b hb hy, hΩ c hc hz⟩)))
      · rw [hH]
        exact wordProd_mem_orthogonalGroup hplet
    obtain ⟨hN, e₀, he₀, hout⟩ := certOK_spec hok
    have ck : Coded (wordProd p.2) (wordC p.2) := coded_wordProd p.2
    have cki : Coded (wordProd p.2)⁻¹ (wordC p.2.reverse) := by
      rw [wordProd_inv]
      exact coded_wordProd _
    have hconj : ∀ {g : V₀ ≃ₗ[ZMod 2] V₀} {d : ℕ}, Coded g d →
        Coded (wordProd p.2 * g * (wordProd p.2)⁻¹) (conjC p.2 d) :=
      fun hg => (ck.mul hg).mul cki
    have hyp : ∀ e ∈ E, ∀ f ∈ E, wordProd p.2 * e * (wordProd p.2)⁻¹ * f *
        (wordProd p.2 * e * (wordProd p.2)⁻¹)⁻¹ ∈ E := by
      intro e he f hf
      obtain ⟨d, hd, ced⟩ := exists_coded_of_mem_left hFS (hES e he)
      obtain ⟨d', hd', cfd⟩ := exists_coded_of_mem_left hFS (hES f hf)
      have cy := hconj ced
      have hel := (mem_iff_of_forall₂ hFS ((cy.mul cfd).mul cy)).mpr (hN d hd d' hd')
      have hyy : (wordProd p.2 * e * (wordProd p.2)⁻¹)⁻¹ = wordProd p.2 * e * (wordProd p.2)⁻¹ := by
        have h2e := hinv e he
        rw [pow_two] at h2e
        apply inv_eq_of_mul_eq_one_right
        calc wordProd p.2 * e * (wordProd p.2)⁻¹ * (wordProd p.2 * e * (wordProd p.2)⁻¹) =
              wordProd p.2 * (e * e) * (wordProd p.2)⁻¹ := by group
          _ = 1 := by rw [h2e, mul_one, mul_inv_cancel]
      rw [hyy]
      exact hSE _ hel
    obtain ⟨g₀, hg₀, cg₀⟩ := exists_coded_of_mem_right hFS he₀
    have hin := hwc _ hkH hyp g₀ (hSE g₀ hg₀)
    exact hout ((mem_iff_of_forall₂ hFS (hconj cg₀)).mp (hES _ hin))

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem weaklyClosed_E8
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hV : finrank (ZMod 2) V = 6) (hQ : Q.polarBilin.Nondegenerate)
    {H E : Subgroup (V ≃ₗ[ZMod 2] V)} (h1 : omegaGroup Q hQ ≤ H)
    (h2 : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hEH : E ≤ H) (hE8 : Nat.card E = 8)
    (hab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hinv : ∀ x ∈ E, x ^ 2 = 1)
    (hwc : ∀ h ∈ H, E.map (MulAut.conj h).toMonoidHom ≤ Subgroup.normalizer (E : Set _) →
      E.map (MulAut.conj h).toMonoidHom = E) :
    IsPlus Q ∧ E ≤ omegaGroup Q hQ := by
  have := finite_linearEquiv (V := V₀)
  obtain ⟨L, hL⟩ := exists_linearEquiv_model hV hQ
  obtain ⟨minus, hL'⟩ : ∃ minus, ∀ v, qModel minus (L v) = Q v := by
    rcases hL with hL | hL
    · exact ⟨false, fun v => by rw [qModel_false]; exact hL v⟩
    · exact ⟨true, fun v => by rw [qModel_true]; exact hL v⟩
  have hΩ := fun g => mem_omegaGroup_conjL hQ (qModel_nondegenerate minus) hL' (g := g)
  have hO := fun g => mem_orthogonalGroup_conjL hL' (g := g)
  set σ := conjL L with hσ
  set H₀ := H.map σ.toMonoidHom with hH₀
  set E₀ := E.map σ.toMonoidHom with hE₀
  have h1₀ : Ω₀ minus ≤ H₀ := by
    intro x hx
    refine (Subgroup.mem_map_equiv (f := σ)).mpr (h1 ?_)
    rw [← hΩ, MulEquiv.apply_symm_apply]
    exact hx
  have h2₀ : H₀ ≤ O₀ minus := by
    rintro _ ⟨h, hh, rfl⟩
    exact (hO h).mpr (h2 hh)
  have hE₀O : E₀ ≤ O₀ minus := le_trans (Subgroup.map_mono hEH) h2₀
  have hwc₀ : WeakClosed H₀ E₀ := (weakClosed_of hinv hwc).map σ
  have hP2 : IsPGroup 2 E₀ := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨e, he, hx⟩ := x.2
    rw [Subgroup.coe_pow, pow_one, Subgroup.coe_one, ← hx, ← map_pow, hinv e he, map_one]
  obtain ⟨k, hk, hkE⟩ := exists_conj_mem_sylowT hE₀O hP2
  set τ := MulAut.conj k⁻¹ with hτ
  have hτx : ∀ x, τ x = k⁻¹ * x * k := fun x => by
    rw [hτ, MulAut.conj_apply, inv_inv]
  set H₁ := H₀.map τ.toMonoidHom with hH₁
  set E₁ := E₀.map τ.toMonoidHom with hE₁
  have h1₁ : Ω₀ minus ≤ H₁ := by
    intro x hx
    refine ⟨k * x * k⁻¹, h1₀ (conj_mem_omega hk hx), ?_⟩
    change τ (k * x * k⁻¹) = x
    rw [hτx]
    group
  have h2₁ : H₁ ≤ O₀ minus := by
    rintro _ ⟨h, hh, rfl⟩
    change τ h ∈ O₀ minus
    rw [hτx]
    exact mul_mem (mul_mem (inv_mem hk) (h2₀ hh)) hk
  have hEH₁ : E₁ ≤ H₁ := Subgroup.map_mono (Subgroup.map_mono hEH)
  have hET₁ : E₁ ≤ sylowT minus := by
    rintro _ ⟨x, hx, rfl⟩
    change τ x ∈ sylowT minus
    rw [hτx]
    exact hkE x hx
  have hcard₁ : Nat.card E₁ = 8 := by
    rw [hE₁, Subgroup.card_map_of_injective τ.injective, hE₀,
      Subgroup.card_map_of_injective σ.injective, hE8]
  have hab₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hab x hx y hy]
  have hinv₁ : ∀ x ∈ E₁, x ^ 2 = 1 := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hinv x hx, map_one]
  obtain ⟨hm, hEΩ⟩ := weaklyClosed_core h1₁ h2₁ hEH₁ hET₁ hcard₁ hab₁ hinv₁ (hwc₀.map τ)
  subst hm
  refine ⟨isPlus_of_qPlus L fun v => by rw [← qModel_false]; exact hL' v, fun e he => ?_⟩
  rw [← hΩ]
  have h3 : τ (σ e) ∈ Ω₀ false := hEΩ ⟨σ e, ⟨e, he, rfl⟩, rfl⟩
  rw [hτx] at h3
  have h4 := conj_mem_omega hk h3
  rwa [show k * (k⁻¹ * σ e * k) * k⁻¹ = σ e by group] at h4

end CFSG.LargeExtraspecial.O62
