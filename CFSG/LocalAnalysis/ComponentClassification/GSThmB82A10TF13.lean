module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TNat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10E1Aut

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10

variable {X : Type} [Group X] [Finite X]

theorem IsRep.exists_equiv {N₁ N₂ M : Subgroup X} {n₁ n₂ : ℕ} {φ₁ : ↥N₁ →* Perm (Fin n₁)}
    {φ₂ : ↥N₂ →* Perm (Fin n₂)} {A₁ : Subgroup (Perm (Fin n₁))} {A₂ : Subgroup (Perm (Fin n₂))}
    (h₁ : IsRep φ₁ M A₁) (h₂ : IsRep φ₂ M A₂) :
    ∃ κ : ↥A₁ ≃* ↥A₂, (∀ m (hm : m ∈ M) (hm₁ : φ₁ ⟨m, h₁.1 hm⟩ ∈ A₁),
        (κ ⟨_, hm₁⟩ : Perm (Fin n₂)) = φ₂ ⟨m, h₂.1 hm⟩) ∧
      ∀ g (hg₁ : g ∈ N₁) (hg₂ : g ∈ N₂), g ∈ normalizer (M : Set X) →
        ∀ u (hu : u ∈ A₁) (hu' : φ₁ ⟨g, hg₁⟩ * u * (φ₁ ⟨g, hg₁⟩)⁻¹ ∈ A₁),
          (κ ⟨_, hu'⟩ : Perm (Fin n₂)) =
            φ₂ ⟨g, hg₂⟩ * (κ ⟨u, hu⟩ : Perm (Fin n₂)) * (φ₂ ⟨g, hg₂⟩)⁻¹ := by
  have hMN₁ : M ≤ N₁ := h₁.1
  have hMN₂ : M ≤ N₂ := h₂.1
  have hmap₁ := h₁.2.1
  have hmap₂ := h₂.2.1
  let f₁ : ↥M →* ↥A₁ := (φ₁.comp (inclusion hMN₁)).codRestrict A₁ fun m => by
    rw [← hmap₁]
    exact ⟨inclusion hMN₁ m, m.2, rfl⟩
  let f₂ : ↥M →* ↥A₂ := (φ₂.comp (inclusion hMN₂)).codRestrict A₂ fun m => by
    rw [← hmap₂]
    exact ⟨inclusion hMN₂ m, m.2, rfl⟩
  have hf₁ : Function.Surjective f₁ := by
    rintro ⟨a, ha⟩
    rw [← hmap₁] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have hf₂ : Function.Surjective f₂ := by
    rintro ⟨a, ha⟩
    rw [← hmap₂] at ha
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : f₁.ker = f₂.ker := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj, ← Subtype.coe_inj,
      OneMemClass.coe_one, OneMemClass.coe_one]
    change φ₁ ⟨m, hMN₁ m.2⟩ = 1 ↔ φ₂ ⟨m, hMN₂ m.2⟩ = 1
    rw [h₁.2.2 m m.2, h₂.2.2 m m.2]
  let κ : ↥A₁ ≃* ↥A₂ := (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂))
  have hκ : ∀ m : ↥M, κ (f₁ m) = f₂ m := by
    intro m
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm (f₁ m) =
        (m : ↥M ⧸ f₁.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂
      (QuotientGroup.quotientMulEquivOfEq hk
        ((QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁).symm (f₁ m))) = f₂ m
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hconj : ∀ {n : ℕ} {N : Subgroup X} (φ : ↥N →* Perm (Fin n)) {g j : X} (hg : g ∈ N)
      (hj : j ∈ N) (hgj : g * j * g⁻¹ ∈ N),
      φ ⟨g * j * g⁻¹, hgj⟩ = φ ⟨g, hg⟩ * φ ⟨j, hj⟩ * (φ ⟨g, hg⟩)⁻¹ := by
    intro n N φ g j hg hj hgj
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine ⟨κ, fun m hm hm₁ => congrArg Subtype.val (hκ ⟨m, hm⟩), ?_⟩
  intro g hg₁ hg₂ hgM u hu hu'
  obtain ⟨⟨j, hj⟩, hju⟩ := hf₁ ⟨u, hu⟩
  obtain rfl : φ₁ ⟨j, h₁.1 hj⟩ = u := congrArg Subtype.val hju
  have hjM : g * j * g⁻¹ ∈ M := (mem_normalizer_iff.mp hgM j).mp hj
  have e1 : (⟨_, hu'⟩ : ↥A₁) = f₁ ⟨g * j * g⁻¹, hjM⟩ :=
    Subtype.ext (hconj φ₁ hg₁ (h₁.1 hj) (h₁.1 hjM)).symm
  rw [e1, hκ, show (⟨_, hu⟩ : ↥A₁) = f₁ ⟨j, hj⟩ from rfl, hκ]
  exact hconj φ₂ hg₂ (h₂.1 hj) (h₂.1 hjM)

section Six

private theorem odd_involution_six : ∀ π : Perm (Fin 6), π * π = 1 → sign π = -1 →
    (∀ k, π k ≠ k) ∨ ∃ r s : Fin 6, r ≠ s ∧ π = swap r s := by
  decide +kernel

private theorem even_two_fixed_six : ∀ y : Perm (Fin 6), sign y = 1 →
    (Finset.univ.filter fun k => y k = k).card = 2 → y * y = 1 := by
  decide +kernel

private theorem even_involution_fixed_six : ∀ z : Perm (Fin 6), sign z = 1 → z * z = 1 →
    ∃ r, z r = r := by
  decide +kernel

private theorem exists_fixed_moved_six
    (A : MulAut (alternatingGroup (Fin 6))) {π : Perm (Fin 6)} {i j : Fin 6} (hij : i ≠ j)
    (hA : A * MulAut.conjNormal (swap i j) = MulAut.conjNormal π * A)
    (y : alternatingGroup (Fin 6)) (hy : ∀ k, (y : Perm (Fin 6)) k = k ↔ (k = i ∨ k = j)) :
    ∃ r, (A y : Perm (Fin 6)) r = r ∧ π r ≠ r := by
  have hinj : Function.Injective
      (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))) :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  have hπ2 : π * π = 1 := by
    apply hinj
    have hπA : MulAut.conjNormal π = A * MulAut.conjNormal (swap i j) * A⁻¹ := by
      rw [hA, mul_inv_cancel_right]
    rw [map_mul, map_one, hπA]
    calc A * MulAut.conjNormal (swap i j) * A⁻¹ * (A * MulAut.conjNormal (swap i j) * A⁻¹) =
        A * MulAut.conjNormal (swap i j * swap i j) * A⁻¹ := by rw [map_mul]; group
      _ = 1 := by rw [swap_mul_self, map_one, mul_one, mul_inv_cancel]
  have hπs : sign π = -1 := by
    rcases Int.units_eq_one_or (sign π) with h | h
    · exfalso
      set π' : alternatingGroup (Fin 6) := ⟨π, mem_alternatingGroup.mpr h⟩
      have h2 : MulAut.conjNormal (swap i j) = A⁻¹ * MulAut.conj π' * A := by
        rw [← MulAut.conjNormal_val]
        change _ = A⁻¹ * MulAut.conjNormal π * A
        rw [mul_assoc, ← hA, inv_mul_cancel_left]
      have h1 : (MulAut.conjNormal (swap i j) : MulAut (alternatingGroup (Fin 6))) =
          MulAut.conjNormal ((A⁻¹ π' : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
        rw [MulAut.conjNormal_val, h2]
        refine MulEquiv.ext fun a => ?_
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
      have h4 := (A⁻¹ π').2
      rw [← hinj h1, mem_alternatingGroup, sign_swap hij] at h4
      exact absurd h4 (by decide)
    · exact h
  rcases odd_involution_six π hπ2 hπs with hfree | ⟨r, s, hrs, rfl⟩
  ·
    have hfix : (Finset.univ.filter fun k => (y : Perm (Fin 6)) k = k) = {i, j} := by
      ext k
      simp [hy k]
    have hy2 : (y : Perm (Fin 6)) * y = 1 :=
      even_two_fixed_six y (mem_alternatingGroup.mp y.2) (by rw [hfix, Finset.card_pair hij])
    have hAy : ((A y : alternatingGroup (Fin 6)) : Perm (Fin 6)) * (A y : Perm (Fin 6)) = 1 := by
      have : A y * A y = 1 := by
        rw [← map_mul, show y * y = 1 from Subtype.ext hy2, map_one]
      exact congrArg Subtype.val this
    obtain ⟨r, hr⟩ := even_involution_fixed_six _ (mem_alternatingGroup.mp (A y).2) hAy
    exact ⟨r, hr, hfree r⟩
  ·
    obtain ⟨σ, hσ⟩ := isConj_iff.mp (isConj_swap hij hrs)
    have hB : (MulAut.conjNormal σ)⁻¹ * A * MulAut.conjNormal (swap i j) =
        MulAut.conjNormal (swap i j) * ((MulAut.conjNormal σ)⁻¹ * A) := by
      rw [← hσ, map_mul, map_mul, map_inv] at hA
      calc (MulAut.conjNormal σ)⁻¹ * A * MulAut.conjNormal (swap i j)
          = (MulAut.conjNormal σ)⁻¹ * (A * MulAut.conjNormal (swap i j)) := by group
        _ = (MulAut.conjNormal σ)⁻¹ * (MulAut.conjNormal σ * MulAut.conjNormal (swap i j) *
            (MulAut.conjNormal σ)⁻¹ * A) := by rw [hA]
        _ = MulAut.conjNormal (swap i j) * ((MulAut.conjNormal σ)⁻¹ * A) := by group
    obtain ⟨ρ, hρ⟩ := A10E1.mem_range_conjNormal_of_commute_swap _ hij hB
    obtain ⟨g, hAg⟩ : ∃ g, A = MulAut.conjNormal g :=
      ⟨σ * ρ, by rw [map_mul, ← hρ, mul_inv_cancel_left]⟩
    have hg : swap (g i) (g j) = swap r s := by
      apply hinj
      rw [swap_apply_apply, map_mul, map_mul, map_inv, ← hAg, hA, mul_inv_cancel_right]
    refine ⟨g i, ?_, ?_⟩
    · rw [hAg, MulAut.conjNormal_apply]
      simp only [Perm.coe_mul, Perm.coe_inv, Function.comp_apply, Equiv.symm_apply_apply,
        (hy i).mpr (Or.inl rfl)]
    · rw [← hg, swap_apply_left]
      exact fun h => hij (g.injective h).symm

variable {α : Type*} [Fintype α] [DecidableEq α] {T : Finset α}

private noncomputable def altOnSix (e : ↥T ≃ Fin 6) : ↥(altOn T) ≃* alternatingGroup (Fin 6) :=
  (altOnEquiv T).symm.trans (Equiv.altCongrHom e)

private theorem altOnSix_apply (e : ↥T ≃ Fin 6) (u : ↥(altOn T)) (x : Fin 6) :
    ((e.symm (((altOnSix e u : alternatingGroup (Fin 6)) : Perm (Fin 6)) x) : ↥T) : α) =
      (u : Perm α) (e.symm x) := by
  set k := (altOnEquiv T).symm u with hk
  have hku : (u : Perm α) = Perm.ofSubtype (k : Perm ↥T) := by
    have h1 : altOnEquiv T k = u := by rw [hk, MulEquiv.apply_symm_apply]
    rw [← h1]
    rfl
  change ((e.symm (e.permCongr (k : Perm ↥T) x) : ↥T) : α) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hku, Perm.ofSubtype_apply_coe]

private theorem permCongr_subtypePerm_apply (e : ↥T ≃ Fin 6) {g : Perm α}
    (hg : ∀ i, g i ∈ T ↔ i ∈ T) (x : Fin 6) :
    ((e.symm (e.permCongr (g.subtypePerm hg) x) : ↥T) : α) = g (e.symm x) := by
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.subtypePerm_apply]

private theorem altOnSix_conj (e : ↥T ≃ Fin 6) {g : Perm α} (hg : ∀ i, g i ∈ T ↔ i ∈ T)
    (u : ↥(altOn T)) (hu : g * (u : Perm α) * g⁻¹ ∈ altOn T) :
    ((altOnSix e ⟨_, hu⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      e.permCongr (g.subtypePerm hg) * (altOnSix e u : Perm (Fin 6)) *
        (e.permCongr (g.subtypePerm hg))⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  refine Equiv.Perm.ext fun x => e.symm.injective (Subtype.ext ?_)
  rw [Perm.mul_apply, Perm.mul_apply, altOnSix_apply, permCongr_subtypePerm_apply,
    permCongr_subtypePerm_apply, altOnSix_apply]
  simp only [Perm.coe_mul, Perm.coe_inv, Function.comp_apply, Equiv.symm_apply_apply]

end Six

theorem exists_fixed_moved {α β : Type*} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] {T : Finset α} {T' : Finset β}
    (hT : T.card = 6) (hT' : T'.card = 6) (κ : ↥(altOn T) ≃* ↥(altOn T'))
    {π₁ : Perm α} {π₂ : Perm β} (hπ₁T : ∀ i, π₁ i ∈ T ↔ i ∈ T) (hπ₂T : ∀ i, π₂ i ∈ T' ↔ i ∈ T')
    {p q : α} (hpT : p ∈ T) (hqT : q ∈ T) (hpq : p ≠ q) (hπ₁p : π₁ p = q) (hπ₁q : π₁ q = p)
    (hπ₁ : ∀ i ∈ T, i ≠ p → i ≠ q → π₁ i = i) {x₁ : ↥(altOn T)}
    (hx₁ : ∀ i ∈ T, (x₁ : Perm α) i = i ↔ (i = p ∨ i = q))
    (hπ₁N : ∀ u ∈ altOn T, π₁ * u * π₁⁻¹ ∈ altOn T)
    (hπ₂N : ∀ u ∈ altOn T', π₂ * u * π₂⁻¹ ∈ altOn T')
    (hκ : ∀ u (hu : u ∈ altOn T), (κ ⟨π₁ * u * π₁⁻¹, hπ₁N u hu⟩ : Perm β) =
      π₂ * (κ ⟨u, hu⟩ : Perm β) * π₂⁻¹) :
    ∃ r ∈ T', (κ x₁ : Perm β) r = r ∧ π₂ r ≠ r := by
  obtain ⟨eT⟩ : Nonempty (↥T ≃ Fin 6) :=
    ⟨Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hT])⟩
  obtain ⟨eT'⟩ : Nonempty (↥T' ≃ Fin 6) :=
    ⟨Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hT'])⟩
  obtain ⟨A, hAψ⟩ : ∃ A : MulAut (alternatingGroup (Fin 6)),
      ∀ v, A (altOnSix eT v) = altOnSix eT' (κ v) :=
    ⟨(altOnSix eT).symm.trans (κ.trans (altOnSix eT')), fun v => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]⟩
  have hPQ : eT ⟨p, hpT⟩ ≠ eT ⟨q, hqT⟩ := fun h => hpq (congrArg Subtype.val (eT.injective h))
  have hτ : eT.permCongr (π₁.subtypePerm hπ₁T) = swap (eT ⟨p, hpT⟩) (eT ⟨q, hqT⟩) := by
    refine Equiv.Perm.ext fun x => ?_
    obtain ⟨t, rfl⟩ := eT.surjective x
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    by_cases htp : (t : α) = p
    · obtain rfl : t = ⟨p, hpT⟩ := Subtype.ext htp
      rw [swap_apply_left]
      exact congrArg eT (Subtype.ext hπ₁p)
    · by_cases htq : (t : α) = q
      · obtain rfl : t = ⟨q, hqT⟩ := Subtype.ext htq
        rw [swap_apply_right]
        exact congrArg eT (Subtype.ext hπ₁q)
      · rw [swap_apply_of_ne_of_ne (fun h => htp (congrArg Subtype.val (eT.injective h)))
          (fun h => htq (congrArg Subtype.val (eT.injective h)))]
        exact congrArg eT (Subtype.ext (hπ₁ t t.2 htp htq))
  have hA : A * MulAut.conjNormal (swap (eT ⟨p, hpT⟩) (eT ⟨q, hqT⟩)) =
      MulAut.conjNormal (eT'.permCongr (π₂.subtypePerm hπ₂T)) * A := by
    rw [← hτ]
    refine MulEquiv.ext fun a => ?_
    obtain ⟨u, rfl⟩ := (altOnSix eT).surjective a
    have h1 : MulAut.conjNormal (eT.permCongr (π₁.subtypePerm hπ₁T)) (altOnSix eT u) =
        altOnSix eT ⟨π₁ * u * π₁⁻¹, hπ₁N u u.2⟩ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply, altOnSix_conj eT hπ₁T u])
    have h2 : κ ⟨π₁ * u * π₁⁻¹, hπ₁N u u.2⟩ = ⟨π₂ * (κ u : Perm β) * π₂⁻¹, hπ₂N _ (κ u).2⟩ :=
      Subtype.ext (hκ u u.2)
    have h3 : MulAut.conjNormal (eT'.permCongr (π₂.subtypePerm hπ₂T)) (altOnSix eT' (κ u)) =
        altOnSix eT' ⟨π₂ * (κ u : Perm β) * π₂⁻¹, hπ₂N _ (κ u).2⟩ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply, altOnSix_conj eT' hπ₂T (κ u)])
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, hAψ, hAψ, h2, h3]
  have hy : ∀ k, ((altOnSix eT x₁ : alternatingGroup (Fin 6)) : Perm (Fin 6)) k = k ↔
      (k = eT ⟨p, hpT⟩ ∨ k = eT ⟨q, hqT⟩) := by
    intro k
    obtain ⟨t, rfl⟩ := eT.surjective k
    have h1 := altOnSix_apply eT x₁ (eT t)
    rw [Equiv.symm_apply_apply] at h1
    have h2 : ((altOnSix eT x₁ : alternatingGroup (Fin 6)) : Perm (Fin 6)) (eT t) = eT t ↔
        (x₁ : Perm α) t = t := by
      rw [← h1, Subtype.coe_inj, Equiv.symm_apply_eq]
    rw [h2, hx₁ t t.2]
    simp only [Equiv.apply_eq_iff_eq, Subtype.ext_iff]
  obtain ⟨r, hr1, hr2⟩ := exists_fixed_moved_six A hPQ hA (altOnSix eT x₁) hy
  refine ⟨eT'.symm r, (eT'.symm r).2, ?_, ?_⟩
  · have h1 := altOnSix_apply eT' (κ x₁) r
    rw [← hAψ x₁, hr1] at h1
    exact h1.symm
  · intro h
    apply hr2
    rw [Equiv.permCongr_apply, Equiv.apply_eq_iff_eq_symm_apply]
    exact Subtype.ext h

end CFSG.ComponentClassification.GSThmB.A10T
