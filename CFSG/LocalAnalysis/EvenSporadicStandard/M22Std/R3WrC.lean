module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrE
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3WrConj
public import Certificates.Certificate25910

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M22Std.S6Check

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 6)), Fintype.card_perm, Fintype.card_fin]
    at h
  have h6 : Nat.factorial 6 = 720 := by decide
  omega

theorem card_subgroup_prod {G H : Type*} [Group G] [Group H] (A : Subgroup G) (B : Subgroup H) :
    Nat.card ↥(A.prod B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.subtypeProdEquivProd (p := (· ∈ A)) (q := (· ∈ B)))

variable {X : Type} [Group X] [Finite X] {zb : X} {f : X →* Wr} {E : Subgroup X}

namespace WrSit

theorem b_eq_of_commute {a b u : Equiv.Perm (Fin 6)}
    (h : (⟨a, b, false⟩ : Wr) * ⟨u, u⁻¹, true⟩ = ⟨u, u⁻¹, true⟩ * ⟨a, b, false⟩) :
    b = u⁻¹ * a * u := by
  have h1 := congrArg Wr.a h
  simp only [Wr.mul_ff, Wr.mul_tt] at h1
  calc b = u⁻¹ * (u * b) := by group
    _ = u⁻¹ * (a * u) := by rw [← h1]
    _ = u⁻¹ * a * u := by group

omit [Finite X] in
theorem b_eq_of_mem_centralizer {u : Equiv.Perm (Fin 6)}
    (hu : f zb = ⟨u, u⁻¹, true⟩) {g : X} (hg : g ∈ centralizer ({zb} : Set X))
    (hge : (f g).e = false) : (f g).b = u⁻¹ * (f g).a * u := by
  have hc : g * zb = zb * g := mem_centralizer_singleton_iff.1 hg
  have h1 : f g * f zb = f zb * f g := by rw [← map_mul, ← map_mul, hc]
  rw [hu] at h1
  rcases hfg : f g with ⟨a, b, e⟩
  rw [hfg] at hge h1
  simp only at hge
  subst hge
  exact b_eq_of_commute h1

theorem card_E (h : WrSit X zb f E) : Nat.card E = 129600 := by
  obtain ⟨e⟩ := h.E_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_alt6]


theorem zb_outer (h : WrSit X zb f E) : (f zb).e = true := by
  classical
  by_contra hne
  have he : (f zb).e = false := by simpa using hne
  have hsq : f zb * f zb = 1 := by rw [← map_mul, h.zb2, map_one]
  rcases hfz : f zb with ⟨u, v, e⟩
  rw [hfz] at he hsq
  simp only at he
  subst he
  have hu2 : u * u = 1 := congrArg Wr.a hsq
  have hv2 : v * v = 1 := congrArg Wr.b hsq
  have hcheck := of_decide_eq_true (Certificates.certificate25910)
  have huv : u ≠ 1 ∨ v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨rfl, rfl⟩ := hcon
    have hz1 : zb = 1 := h.inj (by rw [hfz, map_one]; rfl)
    have htop : centralizer ({zb} : Set X) = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun g => mem_centralizer_singleton_iff.2 (by rw [hz1]; simp)
    have hX : Nat.card X = 1440 := by
      rw [← h.C_card, htop, Subgroup.card_top]
    have h1 := Subgroup.card_le_card_group E
    have h2 := h.card_E
    omega
  have hdiv : cA6 u * cA6 v ∣ 1440 := by
    let K0 : Subgroup (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :=
      ((centralizer ({u} : Set (Equiv.Perm (Fin 6)))).comap
        (alternatingGroup (Fin 6)).subtype).prod
        ((centralizer ({v} : Set (Equiv.Perm (Fin 6)))).comap
          (alternatingGroup (Fin 6)).subtype)
    have hcA : ∀ w : Equiv.Perm (Fin 6),
        Nat.card ↥((centralizer ({w} : Set (Equiv.Perm (Fin 6)))).comap
          (alternatingGroup (Fin 6)).subtype) = cA6 w := fun w => by
      rw [Nat.card_eq_fintype_card, cA6]
      refine Fintype.card_congr (Equiv.subtypeEquivRight fun c => ?_)
      rw [Subgroup.mem_comap, mem_centralizer_singleton_iff]
      rfl
    have hK0 : Nat.card K0 = cA6 u * cA6 v := by
      rw [card_subgroup_prod, hcA, hcA]
    let ι : K0 →* X := E.subtype.comp
      ((MulEquiv.ofBijective h.theta h.theta_bijective).symm.toMonoidHom.comp K0.subtype)
    have hι : Function.Injective ι := by
      intro k k' hkk
      have h1 : ((MulEquiv.ofBijective h.theta h.theta_bijective).symm (k : _)) =
          (MulEquiv.ofBijective h.theta h.theta_bijective).symm (k' : _) := Subtype.ext hkk
      exact Subtype.ext ((MulEquiv.ofBijective h.theta h.theta_bijective).symm.injective h1)
    have hrange : ι.range ≤ centralizer ({zb} : Set X) := by
      rintro _ ⟨k, rfl⟩
      rw [mem_centralizer_singleton_iff]
      set g : E := (MulEquiv.ofBijective h.theta h.theta_bijective).symm (k : _) with hg
      have hθ : h.theta g = (k : _) :=
        (MulEquiv.ofBijective h.theta h.theta_bijective).apply_symm_apply _
      have h1 : (f g).a = ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).1 :=
        congrArg (fun p => (p.1 : Equiv.Perm (Fin 6))) hθ
      have h2 : (f g).b = ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).2 :=
        congrArg (fun p => (p.2 : Equiv.Perm (Fin 6))) hθ
      have hfg : f g = ⟨((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).1,
          ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).2, false⟩ := by
        have he := h.E_flag g.2
        rcases hf' : f g with ⟨a, b, e⟩
        rw [hf'] at h1 h2 he
        simp only at h1 h2 he
        subst he
        rw [h1, h2]
      have hkc1 : ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).1 * u = u *
          ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).1 :=
        mem_centralizer_singleton_iff.1 k.2.1
      have hkc2 : ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).2 * v = v *
          ((k : _) : alternatingGroup (Fin 6) × alternatingGroup (Fin 6)).2 :=
        mem_centralizer_singleton_iff.1 k.2.2
      apply h.inj
      rw [map_mul, map_mul, hfz]
      show f (g : X) * _ = _ * f (g : X)
      rw [show f (g : X) = f g from rfl, hfg]
      simp [hkc1, hkc2]
    have hd1 : Nat.card ι.range = Nat.card K0 :=
      (Nat.card_congr (MonoidHom.ofInjective hι).toEquiv).symm
    rw [← hK0, ← hd1, ← h.C_card]
    exact Subgroup.card_dvd_of_le hrange
  exact hcheck.2.apply hu2 hv2 huv hdiv

theorem exists_zb_form (h : WrSit X zb f E) : ∃ u, f zb = ⟨u, u⁻¹, true⟩ := by
  have hzo := h.zb_outer
  have hsq : f zb * f zb = 1 := by rw [← map_mul, h.zb2, map_one]
  rcases hfz : f zb with ⟨u, v, e⟩
  rw [hfz] at hzo hsq
  simp only at hzo
  subst hzo
  refine ⟨u, ?_⟩
  have := Wr.eq_inv_of_sq_eq_one (w := ⟨u, v, true⟩) rfl hsq
  simp only at this
  rw [this]

theorem exists_base_centralizer (h : WrSit X zb f E) :
    ∃ ν ∈ centralizer ({zb} : Set X), (f ν).e = false ∧ ν ∉ E := by
  classical
  obtain ⟨u, hu⟩ := h.exists_zb_form
  set C : Subgroup X := centralizer ({zb} : Set X) with hC
  have hzbC : zb ∈ C := mem_centralizer_singleton_iff.2 rfl
  set D1 : Subgroup X := E ⊓ C with hD1
  have hD1card : Nat.card D1 ≤ 360 := by
    rw [← card_alt6]
    refine Nat.card_le_card_of_injective
      (fun g : D1 => (⟨(f (g : X)).a, Equiv.Perm.mem_alternatingGroup.2
        (h.E_sign (Subgroup.mem_inf.1 g.2).1).1⟩ : alternatingGroup (Fin 6))) ?_
    intro g g' hgg
    have h1 : (f (g : X)).a = (f (g' : X)).a := congrArg Subtype.val hgg
    have hgE := (Subgroup.mem_inf.1 g.2)
    have hgE' := (Subgroup.mem_inf.1 g'.2)
    have h2 := b_eq_of_mem_centralizer hu hgE.2 (h.E_flag hgE.1)
    have h3 := b_eq_of_mem_centralizer hu hgE'.2 (h.E_flag hgE'.1)
    have h4 : f (g : X) = f (g' : X) := by
      rcases hfg : f (g : X) with ⟨a, b, e⟩
      rcases hfg' : f (g' : X) with ⟨a', b', e'⟩
      have e1 := h.E_flag hgE.1
      have e2 := h.E_flag hgE'.1
      rw [hfg] at h1 h2 e1
      rw [hfg'] at h1 h3 e2
      simp only at h1 h2 h3 e1 e2
      subst e1 e2 h1
      rw [h2, h3]
    exact Subtype.ext (h.inj h4)
  have hex : ∃ γ ∈ C, γ ∉ D1 ∧ γ * zb ∉ D1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (C : Set X) ⊆ (D1 : Set X) ∪ (fun g => g * zb) '' (D1 : Set X) := by
      intro γ hγ
      by_cases hγD : γ ∈ D1
      · exact Or.inl hγD
      · refine Or.inr ⟨γ * zb, hcon γ hγ hγD, ?_⟩
        show γ * zb * zb = γ
        rw [mul_assoc, h.zb2, mul_one]
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le (D1 : Set X) ((fun g => g * zb) '' (D1 : Set X))
    have h3 : ((fun g => g * zb) '' (D1 : Set X)).ncard = (D1 : Set X).ncard :=
      Set.ncard_image_of_injective _ (mul_left_injective zb)
    have h4 : (C : Set X).ncard = 1440 := by
      rw [← Nat.card_coe_set_eq]
      exact h.C_card
    have h5 : (D1 : Set X).ncard = Nat.card D1 := (Nat.card_coe_set_eq _).symm
    omega
  obtain ⟨γ, hγC, hγD, hγzD⟩ := hex
  by_cases he : (f γ).e = false
  · refine ⟨γ, hγC, he, fun hE => hγD (Subgroup.mem_inf.2 ⟨hE, hγC⟩)⟩
  · have het : (f γ).e = true := by simpa using he
    refine ⟨γ * zb, C.mul_mem hγC hzbC, ?_, fun hE =>
      hγzD (Subgroup.mem_inf.2 ⟨hE, C.mul_mem hγC hzbC⟩)⟩
    rw [map_mul, hu]
    rcases hfg : f γ with ⟨a, b, e⟩
    rw [hfg] at het
    simp only at het
    subst het
    rfl

theorem exists_oddodd (h : WrSit X zb f E) :
    ∃ g : X, ∃ n1 n2 : Equiv.Perm (Fin 6), f g = ⟨n1, n2, false⟩ ∧
      Equiv.Perm.sign n1 = -1 ∧ Equiv.Perm.sign n2 = -1 := by
  obtain ⟨u, hu⟩ := h.exists_zb_form
  obtain ⟨ν, hνC, hνe, hνE⟩ := h.exists_base_centralizer
  have hb := b_eq_of_mem_centralizer hu hνC hνe
  refine ⟨ν, (f ν).a, (f ν).b, ?_, ?_, ?_⟩
  · rcases hfν : f ν with ⟨a, b, e⟩
    rw [hfν] at hνe
    simp only at hνe
    subst hνe
    rfl
  · have hn : ¬ (Equiv.Perm.sign (f ν).a = 1 ∧ Equiv.Perm.sign (f ν).b = 1) := fun hh =>
      hνE ((h.mem_E_iff ν).2 ⟨hνe, hh.1, hh.2⟩)
    rw [hb] at hn
    simp only [map_mul, map_inv] at hn
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f ν).a) with h1 | h1
    · exfalso
      apply hn
      refine ⟨h1, ?_⟩
      rw [h1]
      rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]
    · exact h1
  · have hn : ¬ (Equiv.Perm.sign (f ν).a = 1 ∧ Equiv.Perm.sign (f ν).b = 1) := fun hh =>
      hνE ((h.mem_E_iff ν).2 ⟨hνe, hh.1, hh.2⟩)
    have ha : Equiv.Perm.sign (f ν).a = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (f ν).a) with h1 | h1
      · exfalso
        apply hn
        refine ⟨h1, ?_⟩
        rw [hb]
        simp only [map_mul, map_inv, h1]
        rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]
      · exact h1
    rw [hb]
    simp only [map_mul, map_inv, ha]
    rcases Int.units_eq_one_or (Equiv.Perm.sign u) with h2 | h2 <;> simp [h2]

theorem exists_matched (h : WrSit X zb f E) {c d : Equiv.Perm (Fin 6)}
    (hcd : Equiv.Perm.sign c = Equiv.Perm.sign d) : ∃ g : X, f g = ⟨c, d, false⟩ := by
  obtain ⟨gν, n1, n2, hν, hn1, hn2⟩ := h.exists_oddodd
  rcases Int.units_eq_one_or (Equiv.Perm.sign c) with hc | hc
  · obtain ⟨g, -, hg⟩ := h.E_surj hc (hcd ▸ hc)
    exact ⟨g, hg⟩
  · have hd : Equiv.Perm.sign d = -1 := hcd ▸ hc
    have h1 : Equiv.Perm.sign (n1⁻¹ * c) = 1 := by
      simp only [map_mul, map_inv, hn1, hc]
      decide
    have h2 : Equiv.Perm.sign (n2⁻¹ * d) = 1 := by
      simp only [map_mul, map_inv, hn2, hd]
      decide
    obtain ⟨g, -, hg⟩ := h.E_surj h1 h2
    refine ⟨gν * g, ?_⟩
    rw [map_mul, hν, hg]
    simp

end WrSit

end CFSG.EvenSporadicStandard.M22Std
