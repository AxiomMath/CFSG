module

public import CFSG.LargeExtraspecial.S2OrthLevi
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup reflect)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem exists_singular_mem_perp {F : Submodule (ZMod 2) V}
    (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) : ∃ p ∈ perp q F, p ≠ 0 ∧ q p = 0 := by
  obtain ⟨x, hx0, hx⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_ne_zero_map_eq_zero (Q := q.comp (perp q F).subtype)
      h3
  exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hx⟩

theorem exists_hyperbolic_partner (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {p : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) :
    ∃ p₁ ∈ perp q F, q p₁ = 0 ∧ polar q p p₁ = 1 := by
  obtain ⟨y, hyF, hyp⟩ := exists_mem_perp_polar_eq_one hq hF hpF hp0
  refine ⟨y + q y • p, Submodule.add_mem _ hyF (Submodule.smul_mem _ _ hpF), ?_, ?_⟩
  · rw [map_add_eq, map_smul_zmod2, hp, mul_zero, add_zero, polar_smul_right, hyp,
      smul_eq_mul, mul_one, zmod2_add_self]
  · rw [polar_add_right, polar_smul_right, polar_self_eq_zero, smul_zero, add_zero, polar_comm,
      hyp]

omit [FiniteDimensional (ZMod 2) V] in
theorem mem_span_pair_cases {c d w : V} (hw : w ∈ Submodule.span (ZMod 2) {c, d}) :
    w = 0 ∨ w = c ∨ w = d ∨ w = c + d := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
  rcases zmod2_eq_zero_or_eq_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one b with rfl | rfl <;> simp

theorem eq_one_of_commSpace_le_span (hq : q.polarBilin.Nondegenerate) {y : V ≃ₗ[ZMod 2] V}
    (hy : y ∈ omegaGroup q hq) {e : V} (he : commSpace y ≤ (ZMod 2) ∙ e) : y = 1 := by
  by_contra h1
  have h1' := one_le_finrank_commSpace h1
  have h2 : finrank (ZMod 2) (commSpace y) ≤ 1 :=
    (Submodule.finrank_mono he).trans (by simpa using finrank_span_le_card ({e} : Set V))
  have h3 := (mem_omegaGroup.mp hy).2
  rw [show finrank (ZMod 2) (commSpace y) = 1 by omega] at h3
  exact Nat.not_even_one h3

theorem mem_radGen_of_finrank_two (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (h2 : finrank (ZMod 2) (perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁})) = 2)
    {y : V ≃ₗ[ZMod 2] V} (hy : y ∈ omegaFix q hq (F ⊔ Submodule.span (ZMod 2) {p, p₁})) :
    y ∈ radGen q F := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hyO := mem_orthogonalGroup_of_mem_omegaFix hy
  have hyK : ∀ k ∈ K, y k = k := hy.2
  have hne : perp q K ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨c, hcK, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d, hdK, hdc⟩ := exists_mem_perp_polar_eq_one hq hK hcK hc0
  have hcd : polar q c d = 1 := by rw [polar_comm]; exact hdc
  have hli : LinearIndependent (ZMod 2) ![c, d] := linearIndependent_of_polar_eq_one hcd
  have hspan : Submodule.span (ZMod 2) {c, d} = perp q K := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, h2])
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hcK
    · exact hdK
  have hext : ∀ g h : V ≃ₗ[ZMod 2] V, (∀ k ∈ K, g k = h k) → g c = h c → g d = h d → g = h := by
    intro g h hk hgc hgd
    ext v
    have hv : v ∈ K ⊔ perp q K := by rw [sup_perp_eq_top hK]; exact Submodule.mem_top
    obtain ⟨k, hk', w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [← hspan] at hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [map_add, map_smul, hk k hk', hgc, hgd]
  have hpolK : ∀ k ∈ K, ∀ w ∈ perp q K, polar q k w = 0 := fun k hk w hw => (mem_perp.mp hw) k hk
  have hyc : y c ∈ Submodule.span (ZMod 2) {c, d} := hspan ▸ apply_mem_perp hyO hy.2 hcK
  have hyd : y d ∈ Submodule.span (ZMod 2) {c, d} := hspan ▸ apply_mem_perp hyO hy.2 hdK
  have hyc0 : y c ≠ 0 := fun h => hc0 (y.map_eq_zero_iff.mp h)
  have hd0 : d ≠ 0 := by rintro rfl; rw [polar_zero_right] at hcd; exact zero_ne_one hcd
  have hyd0 : y d ≠ 0 := fun h => hd0 (y.map_eq_zero_iff.mp h)
  have hycd : y c ≠ y d := fun h => by
    have := y.injective h
    rw [this, polar_self_eq_zero] at hcd
    exact zero_ne_one hcd
  have hqyc : q (y c) = q c := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hyO c
  have hqyd : q (y d) = q d := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hyO d
  have hqcd : q (c + d) = q c + q d + 1 := by rw [map_add_eq, hcd]
  have hcomm : ∀ e : V, (∀ a b : ZMod 2, y (a • c + b • d) - (a • c + b • d) ∈ (ZMod 2) ∙ e) →
      commSpace y ≤ (ZMod 2) ∙ e := by
    intro e he x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    have hv : v ∈ K ⊔ perp q K := by rw [sup_perp_eq_top hK]; exact Submodule.mem_top
    obtain ⟨k, hk', w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [← hspan] at hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hw
    have := he a b
    rwa [map_add, hyK k hk', add_sub_add_left_eq_sub]
  have hx : p + p₁ ∈ K := Submodule.mem_sup_right (Submodule.add_mem _
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)))
  have hxF : p + p₁ ∈ perp q F := Submodule.add_mem _ hpF hp₁F
  have hqx : q (p + p₁) = 1 := by rw [map_add_eq, hp, hp₁, hpp₁, zero_add, zero_add]
  have hrot : ∀ e e' : V, e ∈ perp q K → e' ∈ perp q K → q e = 1 → q e' = 1 →
      reflect q e * reflect q e' ∈ radGen q F := by
    intro e e' he he' hqe hqe'
    have h2 : (2 : ZMod 2) = 0 := by decide
    set x := p + p₁ with hxdef
    have hex : polar q e x = 0 := by rw [polar_comm]; exact hpolK x hx e he
    have he'x : polar q e' x = 0 := by rw [polar_comm]; exact hpolK x hx e' he'
    have heF : e ∈ perp q F := perp_sup_span_pair_le he
    have he'F : e' ∈ perp q F := perp_sup_span_pair_le he'
    have hu1 : q (e + x) = 0 := by rw [map_add_eq, hqe, hqx, hex]; decide
    have hu2 : q (x + e') = 0 := by rw [map_add_eq, hqe', hqx, polar_comm, he'x]; decide
    have h1 := CFSG.ClassicalGroups.Orthogonal.eichler_eq_reflect_mul_reflect h2 hu1
      (by rw [polar_add_left, polar_self_eq_zero, polar_comm, hex, add_zero]) hqe
    have h1' := CFSG.ClassicalGroups.Orthogonal.eichler_eq_reflect_mul_reflect h2 hu2
      (by rw [polar_add_left, polar_self_eq_zero, he'x, zero_add]) hqx
    rw [show e + (e + x) = x by rw [← add_assoc, vec_add_self, zero_add]] at h1
    rw [show x + (x + e') = e' by rw [← add_assoc, vec_add_self, zero_add]] at h1'
    have hsplit : reflect q e * reflect q e' =
        (reflect q e * reflect q x) * (reflect q x * reflect q e') := by
      rw [mul_assoc, ← mul_assoc (reflect q x), CFSG.ClassicalGroups.Orthogonal.reflect_mul_self,
        one_mul]
    have hx0 : ∀ z, z ∈ perp q K → z + x ≠ 0 := by
      intro z hz h
      have hzx : z = x := by rw [add_eq_zero_iff_eq_neg, vec_neg] at h; exact h
      have : polar q x p = 1 := by
        rw [hxdef, polar_add_left, polar_self_eq_zero, polar_comm, hpp₁, zero_add]
      rw [← hzx, polar_comm] at this
      rw [hpolK p (Submodule.mem_sup_right (Submodule.subset_span (by simp))) z hz] at this
      exact zero_ne_one this
    rw [hsplit, ← h1, ← h1']
    refine mul_mem (radFix_le_radGen (Submodule.add_mem _ heF hxF) (hx0 e he) hu1
      ((mem_radFix_iff hq (hx0 e he) hu1 (Submodule.add_mem _ heF hxF)).mpr
        ⟨e, heF, by rw [polar_add_left, polar_self_eq_zero, polar_comm, hex, add_zero], rfl⟩))
      (radFix_le_radGen (Submodule.add_mem _ hxF he'F) ?_ hu2
        ((mem_radFix_iff hq ?_ hu2 (Submodule.add_mem _ hxF he'F)).mpr
          ⟨x, hxF, by rw [polar_add_left, polar_self_eq_zero, he'x, zero_add], rfl⟩))
    · rw [add_comm]; exact hx0 e' he'
    · rw [add_comm]; exact hx0 e' he'
  have hrefl : ∀ e : V, e ∈ perp q K → q e = 1 → ∀ k ∈ K, reflect q e k = k := by
    intro e he hqe k hk
    rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqe, hpolK k hk e he,
      zero_smul, add_zero]
  have hcc : polar q c c = 0 := polar_self_eq_zero q c
  have hdd : polar q d d = 0 := polar_self_eq_zero q d
  have hdc' : polar q d c = 1 := hdc
  rcases mem_span_pair_cases hyc with h | h | h | h
  · exact absurd h hyc0
  ·
    rcases mem_span_pair_cases hyd with h' | h' | h' | h'
    · exact absurd h' hyd0
    · exact absurd (h.trans h'.symm) hycd
    ·
      have : y = 1 := hext y 1 (fun k hk => hyK k hk) h h'
      rw [this]
      exact one_mem _
    ·
      exfalso
      refine absurd (eq_one_of_commSpace_le_span hq hy.1 (hcomm c fun a b => ?_)) ?_
      · rw [map_add, map_smul, map_smul, h, h']
        exact Submodule.mem_span_singleton.mpr ⟨b, by module⟩
      · intro h1
        have hd' : y d = d := by rw [h1]; rfl
        rw [hd'] at h'
        exact hc0 (add_eq_right.mp h'.symm)
  ·
    rcases mem_span_pair_cases hyd with h' | h' | h' | h'
    · exact absurd h' hyd0
    ·
      exfalso
      refine absurd (eq_one_of_commSpace_le_span hq hy.1 (hcomm (c + d) fun a b => ?_)) ?_
      · rw [map_add, map_smul, map_smul, h, h']
        exact Submodule.mem_span_singleton.mpr ⟨a + b, by rw [vec_sub]; module⟩
      · intro h1
        have hc' : y c = c := by rw [h1]; rfl
        rw [hc'] at h
        rw [← h, polar_self_eq_zero] at hcd
        exact zero_ne_one hcd
    · exact absurd (h.trans h'.symm) hycd
    ·
      have e1 : q d = q c := by rw [← h, hqyc]
      have hqc : q c = 1 := by
        have e2 : q (c + d) = q d := by rw [← h', hqyd]
        rw [hqcd, e1, zmod2_add_self, zero_add] at e2
        exact e2.symm
      have hqd : q d = 1 := by rw [e1, hqc]
      have : y = reflect q c * reflect q d := by
        refine hext _ _ (fun k hk => ?_) ?_ ?_
        · rw [LinearEquiv.mul_apply, hrefl d hdK hqd k hk, hrefl c hcK hqc k hk, hyK k hk]
        · rw [h, LinearEquiv.mul_apply,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqd,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqc, hcd, one_smul,
            polar_add_left, hcc, hdc', zero_add, one_smul, add_comm c d, add_assoc, vec_add_self,
            add_zero]
        · rw [h', LinearEquiv.mul_apply,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqd,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqc, hdd, zero_smul,
            add_zero, hdc', one_smul, add_comm]
      rw [this]
      exact hrot c d hcK hdK hqc hqd
  ·
    rcases mem_span_pair_cases hyd with h' | h' | h' | h'
    · exact absurd h' hyd0
    ·
      have e1 : q c = q d := by rw [← h', hqyd]
      have hqc : q c = 1 := by
        have e2 : q (c + d) = q c := by rw [← h, hqyc]
        rw [hqcd, ← e1, zmod2_add_self, zero_add] at e2
        exact e2.symm
      have hqd : q d = 1 := by rw [← e1, hqc]
      have : y = reflect q d * reflect q c := by
        refine hext _ _ (fun k hk => ?_) ?_ ?_
        · rw [LinearEquiv.mul_apply, hrefl c hcK hqc k hk, hrefl d hdK hqd k hk, hyK k hk]
        · rw [h, LinearEquiv.mul_apply,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqc,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqd, hcc, zero_smul,
            add_zero, hcd, one_smul]
        · rw [h', LinearEquiv.mul_apply,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqc,
            CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_map_eq_one hqd, hdc', one_smul,
            polar_add_left, hdd, hcd, zero_add, one_smul, add_comm d c, add_assoc, vec_add_self,
            add_zero]
      rw [this]
      exact hrot d c hdK hcK hqd hqc
    ·
      exfalso
      refine absurd (eq_one_of_commSpace_le_span hq hy.1 (hcomm d fun a b => ?_)) ?_
      · rw [map_add, map_smul, map_smul, h, h']
        exact Submodule.mem_span_singleton.mpr ⟨a, by module⟩
      · intro h1
        have hc' : y c = c := by rw [h1]; rfl
        rw [hc'] at h
        exact hd0 (add_eq_left.mp h.symm)
    · exact absurd (h.trans h'.symm) hycd

theorem omegaFix_le_radGen (hq : q.polarBilin.Nondegenerate) :
    ∀ (m : ℕ) (F : Submodule (ZMod 2) V), 2 ≤ m → F ⊓ perp q F = ⊥ →
      finrank (ZMod 2) (perp q F) = 2 * m → omegaFix q hq F ≤ radGen q F := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F hm hF hdim g hg
  obtain ⟨p, hpF, hp0, hp⟩ := exists_singular_mem_perp (q := q) (F := F) (by omega)
  obtain ⟨p₁, hp₁F, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq hF hpF hp0 hp
  have hgO := mem_orthogonalGroup_of_mem_omegaFix hg
  have hgpF : g p ∈ perp q F := apply_mem_perp hgO hg.2 hpF
  have hgp0 : g p ≠ 0 := fun h => hp0 (g.map_eq_zero_iff.mp h)
  have hgp : q (g p) = 0 := by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO, hp]
  obtain ⟨e, he, hep⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hgpF hpF hgp0 hp0 hgp hp
  have heg : e * g ∈ omegaFix q hq F := mul_mem (radGen_le_omegaFix hq F he) hg
  obtain ⟨t, ht, hty⟩ := exists_mem_radFix_inv_mul_mem hq hpF hp₁F hp0 hp hp₁ hpp₁ heg
    (by rw [LinearEquiv.mul_apply, hep])
  have hK := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim := finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  have hy : t⁻¹ * (e * g) ∈ radGen q F := by
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · exact mem_radGen_of_finrank_two hq hF hpF hp₁F hp hp₁ hpp₁ (by omega) hty
    · exact radGen_sup_span_pair_le (ih (m - 1) (by omega) _ (by omega) hK (by omega) hty)
  have e1 : g = e⁻¹ * t * (t⁻¹ * (e * g)) := by group
  rw [e1]
  exact mul_mem (mul_mem (inv_mem he) (radFix_le_radGen hpF hp0 hp ht)) hy

theorem radFix_le_closure (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {p p₁ p' : V}
    (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp'F : p' ∈ perp q F) (hp0 : p ≠ 0)
    (hp₁0 : p₁ ≠ 0) (hp'0 : p' ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hp' : q p' = 0)
    (hpp₁ : polar q p p₁ = 1) :
    radFix q F p' ≤ Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁) := by
  set G₀ := Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁)
  have hconj : ∀ {a b : V} {t : V ≃ₗ[ZMod 2] V}, a ∈ perp q F → a ≠ 0 → q a = 0 →
      t ∈ G₀ → t ∈ pointRadical q b ⊓ fixGroup F → radFix q F a ≤ G₀ →
      radFix q F (t a) ≤ G₀ := by
    intro a b t haF ha0 ha htG ht hL s hs
    have h := (map_conj_radFix hq ha0 ha haF ht.1.1 ht.2 s).mp hs
    rw [show s = t * (t⁻¹ * s * t) * t⁻¹ by group]
    exact mul_mem (mul_mem htG (hL h)) (inv_mem htG)
  have key : ∀ {p'' : V}, p'' ∈ perp q F → p'' ≠ 0 → q p'' = 0 → polar q p p'' = 1 →
      radFix q F p'' ≤ G₀ := by
    intro p'' hp''F hp''0 hp'' hpp''
    obtain ⟨t, ht, htp⟩ := exists_mem_radFix_apply_eq hq hp0 hp hpF hp₁F hp''F hp₁ hp'' hpp₁
      hpp''
    rw [← htp]
    exact hconj hp₁F hp₁0 hp₁ (Subgroup.subset_closure (Or.inl ht)) ht
      (fun s hs => Subgroup.subset_closure (Or.inr hs))
  rcases zmod2_eq_zero_or_eq_one (polar q p p') with h0 | h1
  · obtain ⟨p'', hp''F, hp'', hp''p, hp''p'⟩ :=
      exists_common_nonorth hq hF h3 hpF hp'F hp0 hp'0 hp hp'
    have hp''0 : p'' ≠ 0 := by
      rintro rfl
      rw [polar_zero_left] at hp''p
      exact zero_ne_one hp''p
    have hL'' := key hp''F hp''0 hp'' (by rw [polar_comm]; exact hp''p)
    obtain ⟨t, ht, htp⟩ := exists_mem_radFix_apply_eq hq hp''0 hp'' hp''F hpF hp'F hp hp'
      hp''p hp''p'
    rw [← htp]
    exact hconj hpF hp0 hp (hL'' ht) ht (fun s hs => Subgroup.subset_closure (Or.inl hs))
  · exact key hp'F hp'0 hp' h1

theorem omegaFix_eq_closure_radFix (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m)
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) :
    omegaFix q hq F =
      Subgroup.closure ((radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ∪ radFix q F p₁) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  refine le_antisymm ((omegaFix_le_radGen hq m F hm hF hdim).trans ?_) ?_
  · rw [radGen, Subgroup.closure_le]
    rintro t ⟨p', hp'F, hp'0, hp', ht⟩
    exact radFix_le_closure hq hF (by omega) hpF hp₁F hp'F hp0 hp₁0 hp'0 hp hp₁ hp' hpp₁ ht
  · rw [Subgroup.closure_le]
    rintro t (ht | ht)
    · exact radFix_le_omegaFix hq hp0 hp ht
    · exact radFix_le_omegaFix hq hp₁0 hp₁ ht

theorem omegaFix_eq_closure_insert (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m)
    {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ radFix q F p₁)
    (hx1 : x ≠ 1) (hxa : ¬ IsTypeA q x 2) :
    omegaFix q hq F = Subgroup.closure (insert x (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hxO : x ∈ orthogonalGroup q := hx.1.1
  have hxpF : x p ∈ perp q F := apply_mem_perp hxO hx.2 hpF
  have hxp : q (x p) = 0 := by rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hxO, hp]
  have hpxp : polar q p (x p) = 1 := by
    rw [polar_comm]
    exact polar_apply_eq_one_of_not_isTypeA hq hp₁F hp₁0 hp₁ hpp₁ hx hx1 hxa
  refine le_antisymm ?_ ?_
  · rw [omegaFix_eq_closure_radFix hq hF hm hdim hpF hxpF hp0 hp hxp hpxp, Subgroup.closure_le]
    rintro s (hs | hs)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hs)
    · have h := (map_conj_radFix hq hp0 hp hpF hxO hx.2 s).mp hs
      have hxG : x ∈ Subgroup.closure (insert x (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      rw [show s = x * (x⁻¹ * s * x) * x⁻¹ by group]
      exact mul_mem (mul_mem hxG (Subgroup.subset_closure (Set.mem_insert_of_mem _ h)))
        (inv_mem hxG)
  · rw [Subgroup.closure_le]
    rintro t (rfl | ht)
    · exact radFix_le_omegaFix hq hp₁0 hp₁ hx
    · exact radFix_le_omegaFix hq hp0 hp ht

end S2

end CFSG.LargeExtraspecial
