module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Diagonal
public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.Assembly.OddCoreSpan

public section

namespace CFSG.ClassicalInvolution.Balance.LocalBalance

open CFSG CFSG.LocalCores CFSG.Open

section Conj

variable {X : Type*} [Group X]

@[expose] def conjSub (g : X) (L : Subgroup X) : Subgroup X := L.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {g : X} {L : Subgroup X} {y : X} : y ∈ conjSub g L ↔ g⁻¹ * y * g ∈ L := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have e : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e, this]
    exact hx
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    have e : (MulAut.conj g).toMonoidHom (g⁻¹ * y * g) = g * (g⁻¹ * y * g) * g⁻¹ := rfl
    rw [e]
    group

theorem conj_mem_conjSub {g : X} {L : Subgroup X} {x : X} (hx : x ∈ L) :
    g * x * g⁻¹ ∈ conjSub g L := by
  rw [mem_conjSub_iff]
  have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [this]
  exact hx

theorem conjSub_conjSub (g h : X) (L : Subgroup X) :
    conjSub g (conjSub h L) = conjSub (g * h) L := by
  ext y
  rw [mem_conjSub_iff, mem_conjSub_iff, mem_conjSub_iff]
  have : (g * h)⁻¹ * y * (g * h) = h⁻¹ * (g⁻¹ * y * g) * h := by group
  rw [this]

theorem conjSub_one (L : Subgroup X) : conjSub (1 : X) L = L := by
  ext y
  rw [mem_conjSub_iff]
  simp

theorem conjSub_pow_eq {g : X} {L : Subgroup X} (h : conjSub g L = L) (n : ℕ) :
    conjSub (g ^ n) L = L := by
  induction n with
  | zero => simpa using conjSub_one L
  | succ n ih => rw [pow_succ, ← conjSub_conjSub, h, ih]

end Conj

section Moved

variable {X : Type*} [Group X] [Finite X]

theorem not_two_dvd_orderOf_of_mem_oddCore {C : Subgroup X} {r : C}
    (hr : r ∈ componentClassificationOddCore C) : ¬ 2 ∣ orderOf (r : X) := by
  have hdvd := orderOf_dvd_natCard (⟨r, hr⟩ : componentClassificationOddCore C)
  have h1 : orderOf (r : X) = orderOf r := (Subgroup.orderOf_coe r)
  have h2 : orderOf (⟨r, hr⟩ : componentClassificationOddCore C) = orderOf r :=
    (Subgroup.orderOf_coe (⟨r, hr⟩ : componentClassificationOddCore C)).symm
  have hodd : Odd (orderOf (r : X)) := by
    rw [h1, ← h2]
    exact (ComponentClassification.OddCore.odd_card C).of_dvd_nat hdvd
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem commute_of_isComponent_centralizer {f d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) {K : Subgroup X}
    (hK : K ≤ Subgroup.centralizer ({f} : Set X))
    (hKc : IsComponent (K.subgroupOf (Subgroup.centralizer ({f} : Set X)))) :
    ∀ x ∈ K, d * x = x * d := by
  set C : Subgroup X := Subgroup.centralizer ({f} : Set X) with hC
  obtain ⟨r, hr, rfl⟩ := hd
  have hr' : r ∈ componentClassificationOddCore C := hr
  have hsolv : Group.IsSolvable (componentClassificationOddCore C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (ComponentClassification.OddCore.odd_card C)
  have hsub : (componentClassificationOddCore C).IsSubnormal :=
    (inferInstance : (componentClassificationOddCore C).Normal).isSubnormal
  have hcomm := (component_solvable_centralizer hsolv hsub).1 _ hKc
  intro x hx
  have hmem : (⟨x, hK hx⟩ : C) ∈ K.subgroupOf C := hx
  have := Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hmem) r hr'
  exact congrArg Subtype.val this

omit [Finite X] in
theorem exists_noncomm_of_isQuasisimple {L : Subgroup X} (hL : IsQuasisimple L) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨-, -, a, b, hab⟩ := hL
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, x.2, y, y.2, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext h)

theorem commute_of_isComponent_of_ne {K K' : Subgroup X} (hK : IsComponent K)
    (hK' : IsComponent K') (hne : K ≠ K') : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := fun _ hx y hy =>
  (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      ((distinct_components_commute hK hK').resolve_left hne) hx) y hy).symm

omit [Finite X] in
theorem commute_of_central_displacement {L : Subgroup X} (hL : IsQuasisimple L) {d : X}
    (hdn : ∀ h, d * h * d⁻¹ ∈ L ↔ h ∈ L)
    (hc : ∀ x ∈ L, ∀ w ∈ L, w * (x⁻¹ * (d * x * d⁻¹)) = (x⁻¹ * (d * x * d⁻¹)) * w) :
    ∀ x ∈ L, d * x = x * d := by
  have : Group.IsPerfect L := hL.1
  have hmem : d ∈ Subgroup.normalizer (L : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    exact fun h => (hdn h).symm
  let σ : L →* L :=
    (CFSG.LocalAnalysis.ComponentInitial.normalizerConjHom L ⟨d, hmem⟩).toMonoidHom
  have hσ : ∀ x : L, ((σ x : L) : X) = d * x * d⁻¹ := fun x =>
    CFSG.LocalAnalysis.ComponentInitial.coe_normalizerConjHom_apply L ⟨d, hmem⟩ x
  have hcen : ∀ x : L, x⁻¹ * σ x ∈ Subgroup.center L := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h2 := hc x x.2 g g.2
    change (g : X) * ((x : X)⁻¹ * ((σ x : L) : X)) = ((x : X)⁻¹ * ((σ x : L) : X)) * g
    rw [hσ]
    exact h2
  have hid := ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement σ hcen
  intro x hx
  have := congrArg (fun φ : L →* L => ((φ ⟨x, hx⟩ : L) : X)) hid
  simp only [hσ, MonoidHom.id_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem commute_of_moved {L : Subgroup X} (hL : IsComponent L) {f : X} (hf2 : f * f = 1)
    (hmoved : conjSub f L ≠ L) {d : X}
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) : ∀ x ∈ L, d * x = x * d := by
  obtain ⟨Δ, hΔC, hΔcomp, hΔmem⟩ := exists_diagonal_component hL hf2 hmoved
  have hdΔ : ∀ δ ∈ Δ, d * δ = δ * d := commute_of_isComponent_centralizer hd hΔC hΔcomp
  have hdf : d * f = f * d := by
    obtain ⟨r, _, rfl⟩ := hd
    exact Subgroup.mem_centralizer_singleton_iff.mp r.2
  have hdodd : ¬ 2 ∣ orderOf d := by
    obtain ⟨r, hr, rfl⟩ := hd
    exact not_two_dvd_orderOf_of_mem_oddCore hr
  have hL'c : IsComponent (conjSub f L) := isComponent_map_mulEquiv (MulAut.conj f) hL
  have hcomm : ∀ x ∈ L, ∀ y ∈ conjSub f L, x * y = y * x :=
    commute_of_isComponent_of_ne hL hL'c (fun h => hmoved h.symm)
  have hLdc : IsComponent (conjSub d L) := isComponent_map_mulEquiv (MulAut.conj d) hL
  have hrel : ∀ x ∈ L, (d * x * d⁻¹) * (d * (f * x * f⁻¹) * d⁻¹) = x * (f * x * f⁻¹) := by
    intro x hx
    have h := hdΔ _ (hΔmem x hx)
    calc (d * x * d⁻¹) * (d * (f * x * f⁻¹) * d⁻¹) = d * (x * (f * x * f⁻¹)) * d⁻¹ := by group
      _ = (x * (f * x * f⁻¹) * d) * d⁻¹ := by rw [h]
      _ = x * (f * x * f⁻¹) := by group
  have hconjf : ∀ x : X, d * (f * x * f⁻¹) * d⁻¹ = f * (d * x * d⁻¹) * f⁻¹ := by
    intro x
    have h1 : d * f = f * d := hdf
    calc d * (f * x * f⁻¹) * d⁻¹ = (d * f) * x * (d * f)⁻¹ := by group
      _ = (f * d) * x * (f * d)⁻¹ := by rw [h1]
      _ = f * (d * x * d⁻¹) * f⁻¹ := by group
  have hdisj : conjSub d L = L ∨ conjSub d L = conjSub f L := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hLd'c : IsComponent (conjSub f (conjSub d L)) :=
      isComponent_map_mulEquiv (MulAut.conj f) hLdc
    have hLd'ne : conjSub f (conjSub d L) ≠ L := by
      intro h
      apply h2
      calc conjSub d L = conjSub f (conjSub f (conjSub d L)) := by
            rw [conjSub_conjSub, hf2, conjSub_one]
        _ = conjSub f L := by rw [h]
    have hc1 : ∀ w ∈ L, ∀ z ∈ conjSub d L, w * z = z * w :=
      commute_of_isComponent_of_ne hL hLdc (fun h => h1 h.symm)
    have hc2 : ∀ w ∈ L, ∀ z ∈ conjSub f (conjSub d L), w * z = z * w :=
      commute_of_isComponent_of_ne hL hLd'c (fun h => hLd'ne h.symm)
    have hall : ∀ x ∈ L, ∀ w ∈ L, w * x = x * w := by
      intro x hx w hw
      have hx'' : f * x * f⁻¹ ∈ conjSub f L := conj_mem_conjSub hx
      have hu1 : d * x * d⁻¹ ∈ conjSub d L := conj_mem_conjSub hx
      have hu2 : d * (f * x * f⁻¹) * d⁻¹ ∈ conjSub f (conjSub d L) := by
        rw [hconjf]
        exact conj_mem_conjSub hu1
      have e1 := hrel x hx
      have e2 : w * ((d * x * d⁻¹) * (d * (f * x * f⁻¹) * d⁻¹)) =
          ((d * x * d⁻¹) * (d * (f * x * f⁻¹) * d⁻¹)) * w := by
        rw [← mul_assoc, hc1 w hw _ hu1, mul_assoc, hc2 w hw _ hu2, ← mul_assoc]
      rw [e1] at e2
      have e3 : w * x * (f * x * f⁻¹) = x * w * (f * x * f⁻¹) := by
        calc w * x * (f * x * f⁻¹) = w * (x * (f * x * f⁻¹)) := by group
          _ = (x * (f * x * f⁻¹)) * w := e2
          _ = x * ((f * x * f⁻¹) * w) := by group
          _ = x * (w * (f * x * f⁻¹)) := by rw [hcomm w hw _ hx'']
          _ = x * w * (f * x * f⁻¹) := by group
      exact mul_right_cancel e3
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isQuasisimple hL.1
    exact hab (hall a ha b hb).symm
  have hdL : conjSub d L = L := by
    rcases hdisj with h | h
    · exact h
    · exfalso
      have h1 : conjSub d (conjSub f L) = L := by
        calc conjSub d (conjSub f L) = conjSub (d * f) L := by rw [conjSub_conjSub]
          _ = conjSub (f * d) L := by rw [hdf]
          _ = conjSub f (conjSub d L) := by rw [conjSub_conjSub]
          _ = conjSub f (conjSub f L) := by rw [h]
          _ = L := by rw [conjSub_conjSub, hf2, conjSub_one]
      have h2 : conjSub (d * d) L = L := by rw [← conjSub_conjSub, h, h1]
      obtain ⟨j, hj⟩ : Odd (orderOf d) := Nat.not_even_iff_odd.mp fun he =>
        hdodd (even_iff_two_dvd.mp he)
      have hpow : (d * d) ^ (j + 1) = d := by
        rw [← sq, ← pow_mul, show 2 * (j + 1) = orderOf d + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      have h3 : conjSub d L = L := by
        have := conjSub_pow_eq h2 (j + 1)
        rwa [hpow] at this
      exact hmoved (h.symm.trans h3)
  have hdL' : conjSub d (conjSub f L) = conjSub f L := by
    rw [conjSub_conjSub, hdf, ← conjSub_conjSub, hdL]
  have hiff : ∀ h, d * h * d⁻¹ ∈ L ↔ h ∈ L := by
    intro h
    have := mem_conjSub_iff (g := d) (L := L) (y := d * h * d⁻¹)
    rw [hdL] at this
    have e : d⁻¹ * (d * h * d⁻¹) * d = h := by group
    rw [e] at this
    exact this
  refine commute_of_central_displacement hL.1 hiff ?_
  intro x hx w hw
  have hx'' : f * x * f⁻¹ ∈ conjSub f L := conj_mem_conjSub hx
  have hu1 : d * x * d⁻¹ ∈ L := (hiff x).mpr hx
  have hu2 : d * (f * x * f⁻¹) * d⁻¹ ∈ conjSub f L := by
    rw [← hdL'] 
    exact conj_mem_conjSub hx''
  have e1 := hrel x hx
  have ha : x⁻¹ * (d * x * d⁻¹) = (f * x * f⁻¹) * (d * (f * x * f⁻¹) * d⁻¹)⁻¹ := by
    calc x⁻¹ * (d * x * d⁻¹)
        = x⁻¹ * ((d * x * d⁻¹) * (d * (f * x * f⁻¹) * d⁻¹)) * (d * (f * x * f⁻¹) * d⁻¹)⁻¹ := by
          group
      _ = x⁻¹ * (x * (f * x * f⁻¹)) * (d * (f * x * f⁻¹) * d⁻¹)⁻¹ := by rw [e1]
      _ = (f * x * f⁻¹) * (d * (f * x * f⁻¹) * d⁻¹)⁻¹ := by group
  have haL' : x⁻¹ * (d * x * d⁻¹) ∈ conjSub f L := by
    rw [ha]
    exact (conjSub f L).mul_mem hx'' ((conjSub f L).inv_mem hu2)
  exact hcomm w hw _ haL'

end Moved

end CFSG.ClassicalInvolution.Balance.LocalBalance
