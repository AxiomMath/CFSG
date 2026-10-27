module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TK
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TF13

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

section Transport

variable {α : Type*} [Fintype α] [DecidableEq α] {T : Finset α} {k : ℕ}

private noncomputable def altOnFin (e : ↥T ≃ Fin k) :
    ↥(altOn T) ≃* alternatingGroup (Fin k) :=
  (altOnEquiv T).symm.trans (Equiv.altCongrHom e)

private theorem altOnFin_apply (e : ↥T ≃ Fin k) (u : ↥(altOn T)) (x : Fin k) :
    ((e.symm (((altOnFin e u : alternatingGroup (Fin k)) : Perm (Fin k)) x) : ↥T) : α) =
      (u : Perm α) (e.symm x) := by
  set v := (altOnEquiv T).symm u with hv
  have hvu : (u : Perm α) = Perm.ofSubtype (v : Perm ↥T) := by
    have h1 : altOnEquiv T v = u := by rw [hv, MulEquiv.apply_symm_apply]
    rw [← h1]
    rfl
  change ((e.symm (e.permCongr (v : Perm ↥T) x) : ↥T) : α) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hvu, Perm.ofSubtype_apply_coe]

private theorem permCongr_subtypePerm_apply_fin (e : ↥T ≃ Fin k) {g : Perm α}
    (hg : ∀ i, g i ∈ T ↔ i ∈ T) (x : Fin k) :
    ((e.symm (e.permCongr (g.subtypePerm hg) x) : ↥T) : α) = g (e.symm x) := by
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.subtypePerm_apply]

private theorem altOnFin_conj (e : ↥T ≃ Fin k) {g : Perm α} (hg : ∀ i, g i ∈ T ↔ i ∈ T)
    (u : ↥(altOn T)) (hu : g * (u : Perm α) * g⁻¹ ∈ altOn T) :
    ((altOnFin e ⟨_, hu⟩ : alternatingGroup (Fin k)) : Perm (Fin k)) =
      e.permCongr (g.subtypePerm hg) * (altOnFin e u : Perm (Fin k)) *
        (e.permCongr (g.subtypePerm hg))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  refine Equiv.Perm.ext fun x => e.symm.injective (Subtype.ext ?_)
  rw [Perm.mul_apply, Perm.mul_apply, altOnFin_apply, permCongr_subtypePerm_apply_fin,
    permCongr_subtypePerm_apply_fin, altOnFin_apply]
  simp only [Perm.coe_mul, Perm.coe_inv, Function.comp_apply, Equiv.symm_apply_apply]

end Transport

private theorem exists_equiv_fin_ten {N₁ N₂ L : Subgroup X} {n : ℕ}
    {φ₁ : ↥N₁ →* Perm (Fin 10)} {φ₂ : ↥N₂ →* Perm (Fin n)} {Δ : Finset (Fin n)}
    (hΔ : Δ.card = 10) (h₁ : IsRep φ₁ L (alternatingGroup (Fin 10)))
    (h₂ : IsRep φ₂ L (altOn Δ)) :
    ∃ τ : Fin 10 ≃ ↥Δ, (∀ m (hm : m ∈ L) (i : Fin 10),
        φ₂ ⟨m, h₂.1 hm⟩ (τ i) = (τ (φ₁ ⟨m, h₁.1 hm⟩ i) : Fin n)) ∧
      ∀ g (hg₁ : g ∈ N₁) (hg₂ : g ∈ N₂), g ∈ normalizer (L : Set X) →
        (∀ j, φ₂ ⟨g, hg₂⟩ j ∈ Δ ↔ j ∈ Δ) →
          ∀ i : Fin 10, φ₂ ⟨g, hg₂⟩ (τ i) = (τ (φ₁ ⟨g, hg₁⟩ i) : Fin n) := by
  obtain ⟨κ, hκ, hκg⟩ := h₁.exists_equiv h₂
  set eΔ : ↥Δ ≃ Fin 10 := Δ.equivFinOfCardEq hΔ
  obtain ⟨σ, hσ⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)).2 (κ.trans (altOnFin eΔ))
  have hinj := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 10 (by norm_num)
  have hA : ∀ v : alternatingGroup (Fin 10),
      ((altOnFin eΔ (κ v) : alternatingGroup (Fin 10)) : Perm (Fin 10)) = σ * v * σ⁻¹ := by
    intro v
    have h1 : MulAut.conjNormal σ v = altOnFin eΔ (κ v) := by
      rw [hσ]
      rfl
    rw [← h1, MulAut.conjNormal_apply]
  have hpt : ∀ v : alternatingGroup (Fin 10), ∀ i : Fin 10,
      (κ v : Perm (Fin n)) (eΔ.symm (σ i)) = (eΔ.symm (σ ((v : Perm (Fin 10)) i)) : Fin n) := by
    intro v i
    rw [← altOnFin_apply eΔ (κ v) (σ i), hA]
    simp only [Perm.mul_apply, Perm.coe_inv, Equiv.symm_apply_apply]
  refine ⟨σ.trans eΔ.symm, fun m hm i => ?_, fun g hg₁ hg₂ hgL hgΔ i => ?_⟩
  · have hmN : m ∈ N₁ := h₁.1 hm
    have hm₁ : φ₁ ⟨m, hmN⟩ ∈ alternatingGroup (Fin 10) := by
      rw [← h₁.2.1]
      exact ⟨⟨m, hmN⟩, hm, rfl⟩
    rw [← hκ m hm hm₁]
    exact hpt ⟨_, hm₁⟩ i
  ·
    have hN : ∀ u ∈ altOn Δ, φ₂ ⟨g, hg₂⟩ * u * (φ₂ ⟨g, hg₂⟩)⁻¹ ∈ altOn Δ := by
      intro u hu
      obtain ⟨huA, huS⟩ := mem_altOn.mp hu
      refine mem_altOn.mpr ⟨(alternatingGroup.normal (α := Fin n)).conj_mem u huA _, ?_⟩
      rw [Perm.support_conj]
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
      exact (hgΔ i).mpr (huS hi)
    have hσρ : σ * φ₁ ⟨g, hg₁⟩ = eΔ.permCongr ((φ₂ ⟨g, hg₂⟩).subtypePerm hgΔ) * σ := by
      apply hinj
      refine MulEquiv.ext fun v => Subtype.ext ?_
      have hv' : φ₁ ⟨g, hg₁⟩ * (v : Perm (Fin 10)) * (φ₁ ⟨g, hg₁⟩)⁻¹ ∈
          alternatingGroup (Fin 10) :=
        (alternatingGroup.normal (α := Fin 10)).conj_mem _ v.2 _
      have e1 : MulAut.conjNormal (φ₁ ⟨g, hg₁⟩) v = ⟨_, hv'⟩ :=
        Subtype.ext (MulAut.conjNormal_apply _ v)
      have e2 : κ ⟨_, hv'⟩ = ⟨φ₂ ⟨g, hg₂⟩ * (κ v : Perm (Fin n)) * (φ₂ ⟨g, hg₂⟩)⁻¹,
          hN _ (κ v).2⟩ :=
        Subtype.ext (hκg g hg₁ hg₂ hgL v v.2 hv')
      rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, e1, MulAut.conjNormal_apply,
        MulAut.conjNormal_apply, MulAut.conjNormal_apply, ← hA ⟨_, hv'⟩, e2,
        altOnFin_conj eΔ hgΔ (κ v) (hN _ (κ v).2), hA v]
    calc φ₂ ⟨g, hg₂⟩ ((σ.trans eΔ.symm) i) = φ₂ ⟨g, hg₂⟩ (eΔ.symm (σ i)) := rfl
      _ = (eΔ.symm (eΔ.permCongr ((φ₂ ⟨g, hg₂⟩).subtypePerm hgΔ) (σ i)) : Fin n) :=
        (permCongr_subtypePerm_apply_fin eΔ hgΔ (σ i)).symm
      _ = (eΔ.symm (σ (φ₁ ⟨g, hg₁⟩ i)) : Fin n) := by
        rw [← Perm.mul_apply _ σ, ← hσρ, Perm.mul_apply]
      _ = ((σ.trans eΔ.symm) (φ₁ ⟨g, hg₁⟩ i) : Fin n) := rfl

private theorem eq_ten_of_factorial_div_two {k : ℕ} (h : k.factorial / 2 = 1814400) : k = 10 := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hk | hk
  · have h1 := Nat.factorial_le (show k ≤ 9 by omega)
    have h9 : Nat.factorial 9 = 362880 := rfl
    omega
  · have h1 := Nat.factorial_le (show 11 ≤ k by omega)
    have h11 : Nat.factorial 11 = 39916800 := rfl
    omega

private theorem sup_oddCoreIn_eq_of_card {A Y : Subgroup X} (hAY : A ≤ Y)
    (hcard : Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) ≤ Nat.card (↥A ⧸ pPrimeCore 2 ↥A)) :
    A ⊔ oddCoreIn Y = Y := by
  set f : ↥A →* ↥Y ⧸ pPrimeCore 2 ↥Y := (QuotientGroup.mk' _).comp (inclusion hAY) with hf
  have hker : f.ker ≤ pPrimeCore 2 ↥A := by
    have h1 : f.ker = (pPrimeCore 2 ↥Y).comap (inclusion hAY) := by
      rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    refine UnbalancedGS.le_pPrimeCore_two_of_normal_odd inferInstance ?_
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
      (card_comap_dvd_of_injective _ _ (inclusion_injective hAY))
  have hsurj : Function.Surjective f := by
    have h1 : Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) ≤ Nat.card f.range :=
      calc Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) ≤ Nat.card (↥A ⧸ pPrimeCore 2 ↥A) := hcard
        _ ≤ Nat.card (↥A ⧸ f.ker) := index_antitone hker
        _ = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    exact MonoidHom.range_eq_top.mp (eq_top_of_le_card _ h1)
  refine le_antisymm (sup_le hAY (map_subtype_le _)) fun y hy => ?_
  obtain ⟨a, ha⟩ := hsurj (QuotientGroup.mk' _ ⟨y, hy⟩)
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at ha
  have h1 : (a : X)⁻¹ * y ∈ oddCoreIn Y := ⟨_, ha, rfl⟩
  have h2 : (a : X) * ((a : X)⁻¹ * y) ∈ A ⊔ oddCoreIn Y :=
    mul_mem (mem_sup_left a.2) (mem_sup_right h1)
  rwa [mul_inv_cancel_left] at h2

private theorem even_card_fixed {n : ℕ} (hn : Even n) {π : Perm (Fin n)} (hπ : π ^ 2 = 1) :
    Even (Finset.univ.filter fun i => π i = i).card := by
  have h1 : (Finset.univ.filter fun i => π i = i) = π.supportᶜ := by
    ext i
    simp [Perm.mem_support]
  rw [h1, Finset.card_compl, Fintype.card_fin]
  obtain ⟨k, hk⟩ := Perm.two_dvd_card_support hπ
  have h2 : π.support.card ≤ n := by
    have := Finset.card_le_univ π.support
    rwa [Fintype.card_fin] at this
  obtain ⟨r, hr⟩ := hn
  exact ⟨r - k, by omega⟩

namespace Ctx.CaseIIIp

variable {c : Ctx X} (e : c.CaseIIIp)

private theorem r0_fix_of_mem_fixR : ∀ i : Fin 10, i ∈ fixR → r0 i = i := by
  decide

private theorem mem_fixR_of_r0_fix : ∀ i : Fin 10, r0 i = i → i ∈ fixR := by
  decide

private theorem exists_Yb_of_rep {b : X} (hbB : b ∈ c.s.h.secB0 c.s.y) (hb : orderOf b = 2)
    {M : Subgroup X} (hMC : M ≤ centralizer ({b} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))))
    (hLM : Seven.Lay c.s.h c.s.y ≤ M) (hwM : e.w ∈ normalizer (M : Set X))
    (hBM : c.s.h.secB0 c.s.y ≤ normalizer (M : Set X)) {n : ℕ} (hn : Even n) (hn10 : 10 ≤ n)
    {ψ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hψ : IsRep ψ M (alternatingGroup (Fin n)))
    (hML : Nat.card (c.s.h.secB0 c.s.y) = 2 → M = Seven.Lay c.s.h c.s.y) :
    ∃ Y : Subgroup X, Y ≤ e.K ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))) ∧
      e.A8 ≤ Y ∧ ∃ s : ℕ, Even s ∧ 8 ≤ s ∧
        Nonempty (↥Y ⧸ pPrimeCore 2 ↥Y ≃* alternatingGroup (Fin s)) ∧
        (s = 8 → e.A8 ⊔ oddCoreIn Y = Y) ∧ (Nat.card (c.s.h.secB0 c.s.y) = 2 → s = 8) := by
  classical
  have hLB : Seven.Lay c.s.h c.s.y ≤ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    Seven.Lay_le_centralizer_secB0 _ _
  have hwL : e.w ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _ (mem_inf.mp e.d.z'_mem_S0).2
  have hBw : c.s.h.secB0 c.s.y ≤ centralizer ({e.w} : Set X) := e.secB0_le_centralizer_w
  set Δ : Finset (Fin n) := Finset.univ.filter fun i =>
    ∀ u (hu : u ∈ c.s.h.secB0 c.s.y), ψ ⟨u, hBM hu⟩ i = i with hΔdef
  have hΔ : ∀ i, (∀ u (hu : u ∈ c.s.h.secB0 c.s.y), ψ ⟨u, hBM hu⟩ i = i) ↔ i ∈ Δ := by
    intro i
    simp only [hΔdef, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨hΔ5, hLrep⟩ := isRep_of_pComponent hψ hBM hBM (c.s.h.isPGroup_secB0 c.s.y) hΔ
    (le_inf hLM hLB) (isPComponent_of_le_of_le (le_inf hLM hLB) inf_le_right c.s.L_pc)
  have h10 : Nat.factorial 10 / 2 = 1814400 := by decide
  have hΔ10 : Δ.card = 10 := by
    obtain ⟨e1⟩ := hLrep.nonempty_equiv
    obtain ⟨e2⟩ := c.nonempty_Lay_equiv
    have h1 : Nat.card (altOn Δ) = 1814400 := by
      rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin, h10]
    rw [card_altOn Δ (by omega)] at h1
    exact eq_ten_of_factorial_div_two h1
  have hwΔ : ∀ j, ψ ⟨e.w, hwM⟩ j ∈ Δ ↔ j ∈ Δ := by
    intro j
    rw [← hΔ, ← hΔ]
    have hcomm : ∀ u (hu : u ∈ c.s.h.secB0 c.s.y),
        ψ ⟨u, hBM hu⟩ * ψ ⟨e.w, hwM⟩ = ψ ⟨e.w, hwM⟩ * ψ ⟨u, hBM hu⟩ := by
      intro u hu
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (mem_centralizer_singleton_iff.mp (hBw hu)))
    constructor
    · intro h u hu
      apply (ψ ⟨e.w, hwM⟩).injective
      rw [← Perm.mul_apply, ← hcomm u hu, Perm.mul_apply, h u hu]
    · intro h u hu
      rw [← Perm.mul_apply, hcomm u hu, Perm.mul_apply, h u hu]
  obtain ⟨τ, hτL, hτg⟩ := exists_equiv_fin_ten hΔ10 c.isRep_Lay hLrep
  have hτw : ∀ i, ψ ⟨e.w, hwM⟩ (τ i) = (τ (r0 i) : Fin n) := by
    intro i
    rw [hτg e.w e.d.z'_mem_secSub hwM hwL hwΔ i, e.hw]
  set Δ' : Finset (Fin n) := Finset.univ.filter fun i => ψ ⟨e.w, hwM⟩ i = i with hΔ'def
  have hEN : zpowers e.w ≤ normalizer (M : Set X) := zpowers_le.mpr hwM
  have hΔ' : ∀ i, (∀ u (hu : u ∈ zpowers e.w), ψ ⟨u, hEN hu⟩ i = i) ↔ i ∈ Δ' := by
    intro i
    simp only [hΔ'def, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h => h e.w (mem_zpowers _), fun hi u hu => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    have h1 : ψ ⟨e.w ^ k, hEN hu⟩ = ψ ⟨e.w, hwM⟩ ^ k := by
      rw [← map_zpow]
      rfl
    rw [h1]
    exact zpow_apply_eq_self_of_apply_eq_self hi k
  set τ' : Fin 10 ↪ Fin n := τ.toEmbedding.trans (Function.Embedding.subtype _)
  have hcard8 : fixR.card = 8 := by decide
  have hfixR : fixR.map τ' ⊆ Δ' := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simp only [hΔ'def, Finset.mem_filter, Finset.mem_univ, true_and]
    change ψ ⟨e.w, hwM⟩ (τ i) = (τ i : Fin n)
    rw [hτw, r0_fix_of_mem_fixR i hi]
  have h8 : 8 ≤ Δ'.card := by
    have h1 := Finset.card_le_card hfixR
    rw [Finset.card_map] at h1
    omega
  have hE2 : IsPGroup 2 (zpowers e.w) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact e.d.z'_mul_self))
  obtain ⟨Y, hYC, hYpc, hYrep, hYmax, -, -⟩ :=
    exists_natural_component hψ hEN hEN hE2 hΔ' (by omega)
  rw [UnbalancedLayer.centralizer_zpowers_eq] at hYC hYpc hYmax
  have hA8C : e.A8 ≤ centralizer ({e.w} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) :=
    le_inf (e.A8_le.trans inf_le_right) (e.A8_le.trans (inf_le_left.trans hLB))
  have hA8L : e.A8 ≤ Seven.Lay c.s.h c.s.y := e.A8_le.trans inf_le_left
  have hA8Y : e.A8 ≤ Y := by
    refine hYmax e.A8 (le_inf (hA8L.trans hLM) (e.A8_le.trans inf_le_right))
      (isPerfect_of_isPComponent hA8C e.isPComponent_A8) ?_
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    have hxA8 : x ∈ e.A8 := hx
    have hxL := hA8L hxA8
    have hxΔ : ψ ⟨x, hxN⟩ ∈ altOn Δ := by
      rw [← hLrep.2.1]
      exact ⟨⟨x, hxN⟩, hxL, rfl⟩
    obtain ⟨hxA, hxS⟩ := mem_altOn.mp hxΔ
    have hxH : x ∈ c.s.h.secSub c.s.y := c.isRep_Lay.1 hxL
    have hφx : c.φ ⟨x, hxH⟩ ∈ altOn fixR := by
      rw [← e.isRep_A8.2.1]
      exact ⟨⟨x, hxH⟩, hxA8, rfl⟩
    refine mem_altOn.mpr ⟨hxA, fun j hj => ?_⟩
    simp only [hΔ'def, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hwj
    obtain ⟨i, hi⟩ := τ.surjective ⟨j, hxS hj⟩
    have hji : j = (τ i : Fin n) := congrArg Subtype.val hi.symm
    subst hji
    rw [hτw] at hwj
    have hiR : i ∉ fixR := fun h => hwj (by rw [r0_fix_of_mem_fixR i h])
    have hφi : c.φ ⟨x, c.isRep_Lay.1 hxL⟩ i = i := by
      by_contra h
      exact hiR ((mem_altOn.mp hφx).2 (Perm.mem_support.mpr h))
    apply Perm.mem_support.mp hj
    calc ψ ⟨x, hxN⟩ (τ i) = (τ (c.φ ⟨x, c.isRep_Lay.1 hxL⟩ i) : Fin n) := hτL x hxL i
      _ = (τ i : Fin n) := by rw [hφi]
  have hUV : M ⊓ centralizer ({e.w} : Set X) ≤
      centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X) :=
    le_inf inf_le_right (inf_le_left.trans hMC)
  have hUsub : ((M ⊓ centralizer ({e.w} : Set X)).subgroupOf
      (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))).IsSubnormal := by
    obtain ⟨-, -, hsub, -, -⟩ := hMpc
    have heq : (M ⊓ centralizer ({e.w} : Set X)).subgroupOf
        (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X)) =
        (M.subgroupOf (centralizer ({b} : Set X))).comap (inclusion (inf_le_right :
          centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X) ≤
            centralizer ({b} : Set X))) := by
      ext ⟨x, hx⟩
      simp only [mem_subgroupOf, mem_comap, mem_inf, coe_inclusion]
      exact ⟨fun h => h.1, fun h => ⟨h, (mem_inf.mp hx).1⟩⟩
    rw [heq]
    exact Subgroup.IsSubnormal.comap _ hsub
  have hYpc' : IsPComponent 2
      (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))) :=
    isPComponent_of_le_of_subnormal hYC hUV hUsub hYpc
  have hb2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  have hbN : zpowers b ≤ normalizer (centralizer ({e.w} : Set X) : Set X) :=
    zpowers_le.mpr (le_normalizer (hBw hbB))
  have hYlay : Y ≤ layerIn (centralizer ({e.w} : Set X)) := by
    apply le_layerIn_of_isPComponent_inf_centralizer hb2 hbN
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hYC.trans hUV
    · rw [UnbalancedLayer.centralizer_zpowers_eq]
      exact hYpc'
  have hA8ns : ¬ Group.IsSolvable e.A8 :=
    not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent hA8C e.isPComponent_A8)
  have hYK : Y ≤ e.K := le_of_le_layerIn_of_nonsolvable_quasisimple e.K_le e.isPComponent_K
    hYlay (isPerfect_of_isPComponent hYC hYpc) (isQuasisimple_of_isPComponent hYC hYpc) hA8Y
    e.A8_le_K hA8ns
  have hπ2 : ψ ⟨e.w, hwM⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have h1 : (⟨e.w, hwM⟩ : ↥(normalizer (M : Set X))) * ⟨e.w, hwM⟩ = 1 :=
      Subtype.ext e.d.z'_mul_self
    rw [h1, map_one]
  refine ⟨Y, le_inf hYK (hYC.trans (inf_le_left.trans hMC)), hYpc', hA8Y, Δ'.card,
    even_card_fixed hn hπ2, h8, ?_, fun hs => ?_, fun h2 => ?_⟩
  · obtain ⟨eY⟩ := hYrep.nonempty_equiv
    exact ⟨eY.trans ((altOnEquiv Δ').symm.trans (Equiv.altCongrHom Δ'.equivFin))⟩
  ·
    refine sup_oddCoreIn_eq_of_card hA8Y ?_
    obtain ⟨eY⟩ := hYrep.nonempty_equiv
    obtain ⟨eA⟩ := e.isRep_A8.nonempty_equiv
    rw [Nat.card_congr eY.toEquiv, Nat.card_congr eA.toEquiv, card_altOn Δ' (by omega),
      card_altOn fixR (by omega), hs, hcard8]
  ·
    have hML' := hML h2
    have himg : altOn Δ = alternatingGroup (Fin n) := by
      rw [← hLrep.2.1, ← hψ.2.1]
      exact congrArg (fun K : Subgroup X => (K.subgroupOf (normalizer (M : Set X))).map ψ)
        hML'.symm
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hn' : n = 10 := by
      have h1 : Nat.card (altOn Δ) = Nat.card (alternatingGroup (Fin n)) := by rw [himg]
      rw [card_altOn Δ (by omega), hΔ10, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h1
      exact eq_ten_of_factorial_div_two (h1.symm.trans h10)
    have hΔu : ∀ j, j ∈ Δ := by
      have h1 : Δ = Finset.univ :=
        Finset.eq_univ_of_card Δ (by rw [hΔ10, Fintype.card_fin, hn'])
      intro j
      rw [h1]
      exact Finset.mem_univ j
    have hsub : Δ' ⊆ fixR.map τ' := by
      intro j hj
      simp only [hΔ'def, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨i, hi⟩ := τ.surjective ⟨j, hΔu j⟩
      have hji : j = (τ i : Fin n) := congrArg Subtype.val hi.symm
      subst hji
      rw [hτw] at hj
      have hri : r0 i = i := τ.injective (Subtype.ext hj)
      exact Finset.mem_map.mpr ⟨i, mem_fixR_of_r0_fix i hri, rfl⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_map] at h1
    omega

theorem exists_Yb (hcore : EvenPump.EvenAltPumpInput) (hHN : EvenPump.HNPumpInput)
    (hHNfix : HNFixedComponents) {b : X} (hbB : b ∈ c.s.h.secB0 c.s.y) (hb : orderOf b = 2)
    (hbZ : ∀ u ∈ c.s.h.secB0 c.s.y, u * b = b * u) :
    ∃ Y : Subgroup X, Y ≤ e.K ⊓ centralizer ({b} : Set X) ∧
      IsPComponent 2 (Y.subgroupOf (centralizer ({e.w} : Set X) ⊓ centralizer ({b} : Set X))) ∧
      e.A8 ≤ Y ∧ ∃ s : ℕ, Even s ∧ 8 ≤ s ∧
        Nonempty (↥Y ⧸ pPrimeCore 2 ↥Y ≃* alternatingGroup (Fin s)) ∧
        (s = 8 → e.A8 ⊔ oddCoreIn Y = Y) ∧ (Nat.card (c.s.h.secB0 c.s.y) = 2 → s = 8) := by
  have hCb : centralizer ((zpowers b : Subgroup X) : Set X) = centralizer ({b} : Set X) :=
    UnbalancedLayer.centralizer_zpowers_eq b
  have hFn : c.propMCfg.B₀ ≤ normalizer ((zpowers b : Subgroup X) : Set X) := fun u hu =>
    centralizer_le_normalizer _ (by rw [hCb]; exact mem_centralizer_singleton_iff.mpr (hbZ u hu))
  obtain ⟨M, hMC, hMpc, hLM, huniq, hnorm, -⟩ :=
    c.propMCfg.exists_unique_component (zpowers_le.mpr hbB) hFn
  rw [hCb] at hMC hMpc huniq
  obtain ⟨n, hn, hn10, ⟨eM⟩⟩ :=
    c.propMCfg.component_alt hcore hHN hHNfix hbB hb hbZ hMC hMpc hLM
  obtain ⟨ψ, hψ, -⟩ := isRep_of_equiv (by omega : 5 ≤ n) (by omega : n ≠ 6) eM
  have hwL : e.w ∈ normalizer (Seven.Lay c.s.h c.s.y : Set X) :=
    Seven.secG0_le_normalizer_Lay _ _ (mem_inf.mp e.d.z'_mem_S0).2
  have hwb : e.w ∈ normalizer ((zpowers b : Subgroup X) : Set X) := by
    refine centralizer_le_normalizer _ ?_
    rw [hCb]
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (e.secB0_le_centralizer_w hbB)).symm
  have hwM : e.w ∈ normalizer (M : Set X) := hnorm (mem_inf.mpr ⟨hwL, hwb⟩)
  have hBM : c.s.h.secB0 c.s.y ≤ normalizer (M : Set X) := fun u hu =>
    hnorm (mem_inf.mpr ⟨Seven.secG0_le_normalizer_Lay _ _ (le_normalizer hu), hFn hu⟩)
  have hML : Nat.card (c.s.h.secB0 c.s.y) = 2 → M = Seven.Lay c.s.h c.s.y := by
    intro h2
    have hFB : zpowers b = c.s.h.secB0 c.s.y :=
      eq_of_le_of_card_ge (zpowers_le.mpr hbB) (by rw [h2, Nat.card_zpowers, hb])
    have hC : centralizer ({b} : Set X) = centralizer (c.s.h.secB0 c.s.y : Set X) := by
      rw [← hCb, hFB]
    refine (huniq (Seven.Lay c.s.h c.s.y) ?_ ?_ le_rfl).symm
    · rw [hC]
      exact Seven.Lay_le_centralizer_secB0 _ _
    · rw [hC]
      exact c.s.L_pc
  exact e.exists_Yb_of_rep hbB hb hMC hMpc hLM hwM hBM hn hn10 hψ hML

end Ctx.CaseIIIp

end CFSG.ComponentClassification.GSThmB.A10T
