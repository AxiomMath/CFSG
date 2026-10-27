module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514L24

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5

variable {G : Type} [Group G] [Finite G]

theorem mem_of_central_of_isSylowOf {X P : Subgroup G} (hP : IsSylowOf 2 P X) {a : G}
    (haX : a ∈ X) (ha2 : a * a = 1) (hac : ∀ x ∈ X, a * x = x * a) : a ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hza : IsPGroup 2 (zpowers a) := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact ha2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hN : zpowers a ≤ normalizer (P : Set G) := by
    refine zpowers_le_of_mem (mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · rw [hac y (hP.le hy)]; group; exact hy
    · have h1 : a * y * a⁻¹ ∈ X := hP.le hy
      have h2 : y = a * y * a⁻¹ := by
        have h3 := hac (a * y * a⁻¹) h1
        have h4 : a * (a * y * a⁻¹) * a⁻¹ = y := by
          rw [show a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ by group, ha2]; group
        calc y = a * (a * y * a⁻¹) * a⁻¹ := h4.symm
          _ = (a * y * a⁻¹) * a * a⁻¹ := by rw [h3]
          _ = a * y * a⁻¹ := by group
      rw [h2]; exact hy
  have hsup : IsPGroup 2 ↥(zpowers a ⊔ P) := IsPGroup.to_sup_of_normal_right' hza hP.isPGroup hN
  have heq := hP.eq_of_le (le_sup_right : P ≤ zpowers a ⊔ P)
    (sup_le (zpowers_le_of_mem haX) hP.le) hsup
  rw [← heq]
  exact mem_sup_left (mem_zpowers a)

omit [Finite G] in
theorem isSylowOf_conjugate [Finite G] {P X : Subgroup G} (hP : IsSylowOf 2 P X) (g : G) :
    IsSylowOf 2 (conjugate P g) (conjugate X g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e₁⟩ := nonempty_conjugate_equiv P g
  obtain ⟨e₂⟩ := nonempty_conjugate_equiv X g
  refine isSylowOf_of_card (fun x hx => ?_) ?_
  · rw [mem_conjugate_iff] at hx ⊢; exact hP.le hx
  · rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv, hP.card_eq]

omit [Finite G] in
theorem conjugate_centralizer_inf {d a g : G} (hgd : g * d = d * g) :
    conjugate (centralizer ({d} : Set G) ⊓ centralizer ({a} : Set G)) g =
      centralizer ({d} : Set G) ⊓ centralizer ({g⁻¹ * a * g} : Set G) := by
  have hgd' : g⁻¹ * d * g = d := by rw [mul_assoc, ← hgd]; group
  ext x
  rw [mem_conjugate_iff, mem_inf, mem_inf, mem_centralizer_singleton_iff,
    mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc x * d = x * (g⁻¹ * d * g) := by rw [hgd']
        _ = g⁻¹ * ((g * x * g⁻¹) * d) * g := by group
        _ = g⁻¹ * (d * (g * x * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * d * g) * x := by group
        _ = d * x := by rw [hgd']
    · calc x * (g⁻¹ * a * g) = g⁻¹ * ((g * x * g⁻¹) * a) * g := by group
        _ = g⁻¹ * (a * (g * x * g⁻¹)) * g := by rw [h2]
        _ = g⁻¹ * a * g * x := by group
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · calc g * x * g⁻¹ * d = g * (x * (g⁻¹ * d * g)) * g⁻¹ := by group
        _ = g * (x * d) * g⁻¹ := by rw [hgd']
        _ = g * (d * x) * g⁻¹ := by rw [h1]
        _ = (g * d * g⁻¹) * (g * x * g⁻¹) := by group
        _ = d * (g * x * g⁻¹) := by rw [hgd]; group
    · calc g * x * g⁻¹ * a = g * (x * (g⁻¹ * a * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * a * g) * x) * g⁻¹ := by rw [h2]
        _ = a * (g * x * g⁻¹) := by group

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem mem_S_of_mem_T_of_commute_z {y : G} (hyT : y ∈ T) (hyz : y * z = z * y) : y ∈ S := by
  have h1 : s * y * s⁻¹ ∈ T := mul_mem (mul_mem H.sT hyT) (inv_mem H.sT)
  have h2 : s * y * s⁻¹ * t = t * (s * y * s⁻¹) := by
    rw [← H.conj_s_z]
    calc s * y * s⁻¹ * (s * z * s⁻¹) = s * (y * z) * s⁻¹ := by group
      _ = s * (z * y) * s⁻¹ := by rw [hyz]
      _ = s * z * s⁻¹ * (s * y * s⁻¹) := by group
  have h3 := H.centT _ h1 h2
  have h4 := conj_mem_of_mem_normalizer H.s_mem_normalizer h3
  rwa [show s⁻¹ * (s * y * s⁻¹) * s = y by group] at h4

theorem isSylowOf_T_H : IsSylowOf 2 T (centralizer ({z * t} : Set G)) :=
  H.sec5.sylT.of_le H.T_le_centralizer_d le_top

theorem exists_conj_strongly_closed {a : G} (haS : a ∈ S) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haRs : ∀ r ∈ conjugate (S ⊓ L) s, a * r = r * a)
    (htype : (a ∈ S ⊓ L ∧ a ≠ t) ∨ actG L ε a ∉ Lin) :
    ∃ g ∈ centralizer ({z * t} : Set G), g⁻¹ * z * g = z ∧ g⁻¹ * a * g ∈ S ∧
      ∃ P : Subgroup G, IsSylowOf 2 P
        (centralizer ({z * t} : Set G) ⊓ centralizer ({g⁻¹ * a * g} : Set G)) ∧
        ∀ x ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({g⁻¹ * a * g} : Set G),
          x⁻¹ * z * x ∈ P → x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G) with hX
  have haz : a * z = z * a := H.sec5.zS a haS
  have hat : a * t = t * a := H.sec5.tZ a haS
  have hRsX : conjugate (S ⊓ L) s ≤ X := fun r hr => mem_inf.mpr
    ⟨mem_centralizer_singleton_iff.mpr (H.commute_d_of_mem_S (H.Rs_le_S hr)),
      mem_centralizer_singleton_iff.mpr (haRs r hr).symm⟩
  obtain ⟨P₁, hP₁, hRsP₁⟩ := exists_isSylowOf_ge_of_le hRsX
    (H.sec5.R_sylow.isPGroup.map (MulAut.conj s⁻¹).toMonoidHom)
  obtain ⟨g₀, hg₀H, hg₀⟩ := exists_conj_le_of_isSylowOf H.isSylowOf_T_H
    (hP₁.le.trans inf_le_left) hP₁.isPGroup
  have hRsT : conjugate (conjugate (S ⊓ L) s) g₀ ≤ T := fun x hx => by
    have h1 := hg₀ _ (hRsP₁ (mem_conjugate_iff.mp hx))
    rwa [show g₀⁻¹ * (g₀ * x * g₀⁻¹) * g₀ = x by group] at h1
  have hz₀ := H.conj_z_eq_of_conjugate_Rs_le (H.conjugate_Rs_le_S hRsT)
  obtain ⟨g, hgH, hgT, hgz⟩ : ∃ g ∈ centralizer ({z * t} : Set G),
      (∀ p ∈ P₁, g⁻¹ * p * g ∈ T) ∧ g⁻¹ * z * g = z := by
    rcases hz₀ with h1 | h1
    · exact ⟨g₀, hg₀H, hg₀, h1⟩
    · refine ⟨g₀ * s, mul_mem hg₀H (H.T_le_centralizer_d H.sT), fun p hp => ?_, ?_⟩
      · rw [show (g₀ * s)⁻¹ * p * (g₀ * s) = s⁻¹ * (g₀⁻¹ * p * g₀) * s by group]
        exact mul_mem (mul_mem (inv_mem H.sT) (hg₀ p hp)) H.sT
      · rw [show (g₀ * s)⁻¹ * z * (g₀ * s) = s⁻¹ * (g₀⁻¹ * z * g₀) * s by group, h1,
          H.conj_s_inv_t]
  have hgd : g * (z * t) = z * t * g := mem_centralizer_singleton_iff.mp hgH
  have hgz' : g * z = z * g := by
    calc g * z = g * (g⁻¹ * z * g) := by rw [hgz]
      _ = z * g := by group
  have hgd' : g⁻¹ * (z * t) * g = z * t := by
    calc g⁻¹ * (z * t) * g = g⁻¹ * (g * (z * t)) := by rw [hgd]; group
      _ = z * t := by group
  have hgt : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = (g⁻¹ * z * g)⁻¹ * (g⁻¹ * (z * t) * g) := by group
      _ = t := by rw [hgz, hgd', ← mul_assoc, inv_mul_cancel, one_mul]
  have hgN : g ∈ normalizer (L : Set G) :=
    H.sec5.centralizer_le_normalizer (mem_centralizer_singleton_iff.mpr hgz')
  set a' := g⁻¹ * a * g with ha'
  have haP₁ : a ∈ P₁ := mem_of_central_of_isSylowOf hP₁
    (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (H.commute_d_of_mem_S haS),
      mem_centralizer_singleton_iff.mpr rfl⟩) ha2
    (fun x hx => (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2).symm)
  have ha'T : a' ∈ T := hgT a haP₁
  have ha'z : a' * z = z * a' := by
    calc a' * z = g⁻¹ * (a * (g * z * g⁻¹)) * g := by rw [ha']; group
      _ = g⁻¹ * (a * z) * g := by rw [show g * z * g⁻¹ = z by rw [hgz']; group]
      _ = g⁻¹ * (z * a) * g := by rw [haz]
      _ = (g⁻¹ * z * g) * (g⁻¹ * a * g) := by group
      _ = z * a' := by rw [hgz]
  have ha'S : a' ∈ S := H.mem_S_of_mem_T_of_commute_z ha'T ha'z
  have ha't : a' * t = t * a' := H.sec5.tZ a' ha'S
  have ha'2 : a' * a' = 1 := by
    rw [ha', show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, ha2]; group
  have htype' : (a' ∈ S ⊓ L ∧ a' ≠ t) ∨ actG L ε a' ∉ Lin := by
    rcases htype with ⟨haR, hat'⟩ | hlin
    · left
      refine ⟨mem_inf.mpr ⟨ha'S, ?_⟩, fun e => hat' ?_⟩
      · exact conj_mem_of_mem_normalizer hgN (mem_inf.mp haR).2
      · calc a = g * a' * g⁻¹ := by rw [ha']; group
          _ = g * t * g⁻¹ := by rw [e]
          _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [hgt]
          _ = t := by group
    · right
      intro hlin'
      apply hlin
      have hN := fun x (hx : x ∈ S) => H.sec5.S_le hx
      have h1 : actG L ε a' = (actG L ε g)⁻¹ * actG L ε a * actG L ε g := by
        rw [ha', actG_mul ε (mul_mem (inv_mem hgN) (hN a haS)) hgN,
          actG_mul ε (inv_mem hgN) (hN a haS), actG_inv ε hgN]
      have h2 : actG L ε a = actG L ε g * actG L ε a' * (actG L ε g)⁻¹ := by
        rw [h1]; group
      rw [h2]
      exact H.autData.normal.conj_mem _ hlin' _
  set X' := centralizer ({z * t} : Set G) ⊓ centralizer ({a'} : Set G) with hX'
  have hXX' : conjugate X g = X' := conjugate_centralizer_inf hgd
  have hP' : IsSylowOf 2 (conjugate P₁ g) X' := hXX' ▸ isSylowOf_conjugate hP₁ g
  have hP'T : conjugate P₁ g ≤ T := fun x hx => by
    have h1 := hgT _ (mem_conjugate_iff.mp hx)
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1
  have hzX' : z ∈ X' := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (H.commute_d_of_mem_S H.sec5.zS_mem), mem_centralizer_singleton_iff.mpr ha'z.symm⟩
  have htX' : t ∈ X' := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr
    (H.commute_d_of_mem_S H.sec5.tS), mem_centralizer_singleton_iff.mpr ha't.symm⟩
  have hcl : ∀ x ∈ X', x⁻¹ * z * x ∈ conjugate P₁ g → x⁻¹ * z * x = z ∨ x⁻¹ * z * x = t := by
    intro x hx hxP
    have hxH : x ∈ centralizer ({z * t} : Set G) := (mem_inf.mp hx).1
    have hxT : x⁻¹ * z * x ∈ T := hP'T hxP
    by_contra hne
    push Not at hne
    obtain ⟨hS, hlin, hinn⟩ := H.pgl_of_conj hxH hxT hne.1 hne.2
    have hca : a' * (x⁻¹ * z * x) = (x⁻¹ * z * x) * a' := by
      have h1 : x⁻¹ * z * x ∈ X' := mul_mem (mul_mem (inv_mem hx) hzX') hx
      exact (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2).symm
    rcases htype' with ⟨ha'R, ha't'⟩ | hlin'
    · rcases H.fix_R_of_conj hxH hxT hne.1 hne.2 a' ha'R hca with h1 | h1
      · exact ha1 (by
          calc a = g * a' * g⁻¹ := by rw [ha']; group
            _ = 1 := by rw [h1]; group)
      · exact ha't' h1
    · apply H.autData.not_commute _ _ hlin hinn
        (by rw [← actG_mul ε (H.sec5.S_le hS) (H.sec5.S_le hS), H.conj_z_mul_self x,
          actG_one]) hlin'
        (by rw [← actG_mul ε (H.sec5.S_le ha'S) (H.sec5.S_le ha'S), ha'2, actG_one])
      rw [← actG_mul ε (H.sec5.S_le hS) (H.sec5.S_le ha'S),
        ← actG_mul ε (H.sec5.S_le ha'S) (H.sec5.S_le hS), hca]
  exact ⟨g, hgH, hgz, ha'S, conjugate P₁ g, hP', hcl⟩

theorem isSolvable_CH {a : G} (haS : a ∈ S) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haRs : ∀ r ∈ conjugate (S ⊓ L) s, a * r = r * a)
    (htype : (a ∈ S ⊓ L ∧ a ≠ t) ∨ actG L ε a ∉ Lin) :
    Group.IsSolvable ↥(centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G)) := by
  obtain ⟨g, hgH, -, ha'S, P, hP, hcl⟩ := H.exists_conj_strongly_closed haS ha2 ha1 haRs htype
  have ha'z : g⁻¹ * a * g * z = z * (g⁻¹ * a * g) := H.sec5.zS _ ha'S
  have ha't : g⁻¹ * a * g * t = t * (g⁻¹ * a * g) := H.sec5.tZ _ ha'S
  have hzX' : z ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({g⁻¹ * a * g} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (H.commute_d_of_mem_S H.sec5.zS_mem),
      mem_centralizer_singleton_iff.mpr ha'z.symm⟩
  have htX' : t ∈ centralizer ({z * t} : Set G) ⊓ centralizer ({g⁻¹ * a * g} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (H.commute_d_of_mem_S H.sec5.tS),
      mem_centralizer_singleton_iff.mpr ha't.symm⟩
  have hsolv := isSolvable_of_isolated_pair H.mul_self_z H.mul_self_t H.z_ne_one H.t_ne_one
    H.isSolvable_CZ inf_le_left hzX' htX' hP hcl
  obtain ⟨e⟩ := nonempty_conjugate_equiv
    (centralizer ({z * t} : Set G) ⊓ centralizer ({a} : Set G)) g
  rw [conjugate_centralizer_inf (mem_centralizer_singleton_iff.mp hgH)] at e
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

end Hyp

end CFSG.ComponentClassification.Sol78.F514
