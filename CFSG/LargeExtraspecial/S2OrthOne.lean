module

public import CFSG.LargeExtraspecial.S2OrthGen
public import CFSG.LargeExtraspecial.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mul eichler_zero_right
  eichler_mem_orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def OmegaInvariant (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))
    (F : Submodule (ZMod 2) V) (N : Submodule (ZMod 2) M) : Prop :=
  ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N, ρ g v ∈ N

@[expose] def RadDecomp (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)) (F : Submodule (ZMod 2) V)
    (N : Submodule (ZMod 2) M) (p p₁ : V) : Prop :=
  (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) ⊔
      (N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) = N ∧
    (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) ⊓
      (N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) = ⊥

theorem RadDecomp.symm {ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M)} {F : Submodule (ZMod 2) V}
    {N : Submodule (ZMod 2) M} {p p₁ : V} (h : RadDecomp ρ F N p p₁) : RadDecomp ρ F N p₁ p :=
  ⟨by rw [sup_comm]; exact h.1, by rw [inf_comm]; exact h.2⟩

variable [FiniteDimensional (ZMod 2) M] (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem map_eq_of_omegaInvariant {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) (g : omegaGroup q hq) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    N.map (ρ g : M →ₗ[ZMod 2] M) = N :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨v, hv, rfl⟩; exact hN g hg v hv)
    (LinearEquiv.finrank_map_eq (ρ g) N)

theorem map_inf_fixOf_radFix {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) (g : omegaGroup q hq) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F)
    {p : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) :
    (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))).map (ρ g : M →ₗ[ZMod 2] M) =
      N ⊓ fixOf ρ (radFix q F ((g : V ≃ₗ[ZMod 2] V) p) : Set (V ≃ₗ[ZMod 2] V)) := by
  have hgO : (g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp g.2).1
  rw [Submodule.map_inf _ (ρ g).injective, map_eq_of_omegaInvariant ρ hN g hg,
    map_fixOf_conj ρ g (fun x => map_conj_radFix hq hp0 hp hpF hgO hg x)]

theorem radDecomp_apply {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hD : RadDecomp ρ F N p p₁)
    (g : omegaGroup q hq) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    RadDecomp ρ F N ((g : V ≃ₗ[ZMod 2] V) p) ((g : V ≃ₗ[ZMod 2] V) p₁) := by
  have h1 := map_inf_fixOf_radFix ρ hN g hg hpF hp0 hp
  have h2 := map_inf_fixOf_radFix ρ hN g hg hp₁F hp₁0 hp₁
  constructor
  · rw [← h1, ← h2, ← Submodule.map_sup, hD.1, map_eq_of_omegaInvariant ρ hN g hg]
  · rw [← h1, ← h2, ← Submodule.map_inf _ (ρ g).injective, hD.2, Submodule.map_bot]

theorem radDecomp_of_pair {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ p' p₁' : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp'F : p' ∈ perp q F) (hp₁'F : p₁' ∈ perp q F) (hp0 : p ≠ 0) (hp'0 : p' ≠ 0)
    (hp : q p = 0) (hp₁ : q p₁ = 0) (hp' : q p' = 0) (hp₁' : q p₁' = 0)
    (hpp₁ : polar q p p₁ = 1) (hpp₁' : polar q p' p₁' = 1) (hD : RadDecomp ρ F N p p₁) :
    RadDecomp ρ F N p' p₁' := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  obtain ⟨g, hg, hgp, hgp₁⟩ := exists_mem_radGen_apply_eq_pair hq hF h3 hpF hp₁F hp'F hp₁'F
    hp0 hp'0 hp hp₁ hp' hp₁' hpp₁ hpp₁'
  have hgΩ := radGen_le_omegaFix hq F hg
  have := radDecomp_apply ρ hN hpF hp₁F hp0 hp₁0 hp hp₁ hD ⟨g, hgΩ.1⟩ hgΩ.2
  rwa [← hgp, ← hgp₁]

theorem finrank_eq_two_mul {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥)
    (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hD : RadDecomp ρ F N p p₁) :
    finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) =
        finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) ∧
      finrank (ZMod 2) N =
        2 * finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) := by
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF h3 hpF hp₁F hp0 hp₁0 hp hp₁
  have hgΩ := radGen_le_omegaFix hq F hg
  have h1 := map_inf_fixOf_radFix ρ hN ⟨g, hgΩ.1⟩ hgΩ.2 hpF hp0 hp
  have hdim : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) =
      finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) := by
    rw [← hgp]
    change _ = _ at h1
    rw [show (g : V ≃ₗ[ZMod 2] V) = ((⟨g, hgΩ.1⟩ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) from rfl,
      ← h1]
    exact LinearEquiv.finrank_map_eq _ _
  refine ⟨hdim, ?_⟩
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)))
    (N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)))
  rw [hD.1, hD.2, finrank_bot, add_zero] at h2
  omega

theorem timmesfeld_2_1_b0 {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hm : 2 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ F N p p₁) (x : omegaGroup q hq)
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q F p₁) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1)
    (hxa : ¬ IsTypeA q x 2) :
    N ⊓ fixSpace (ρ x) = N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) ∧
      N.map ((ρ x : M →ₗ[ZMod 2] M) - 1) =
        N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hgen : (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) ⊆
      Subgroup.closure (insert (x : V ≃ₗ[ZMod 2] V) (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) := by
    rw [← omegaFix_eq_closure_insert hq hF hm hdim hpF hp₁F hp0 hp hp₁ hpp₁ hx hx1 hxa]
    exact fun t ht => radFix_le_omegaFix hq hp₁0 hp₁ ht
  have hLX : (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ⊆ omegaGroup q hq :=
    fun t ht => (radFix_le_omegaFix hq hp0 hp ht).1
  have h1 := inf_fixSpace_eq_of_compl ρ hD.1 hD.2 hLX x hx hgen
  refine ⟨h1, ?_⟩
  obtain ⟨u, -, hp₁u, -, hxu⟩ := exists_eq_eichler_of_not_isTypeA hq hp₁F hp₁0 hp₁ hx hx1 hxa
  have hxx : ρ x * ρ x = 1 := by
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by
      change (x : V ≃ₗ[ZMod 2] V) * x = 1
      rw [hxu]
      exact eichler_mul_self hp₁u)
    rw [this, map_one]
  have hxF : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hx.2
  have hdims := finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD
  rw [← h1]
  refine map_sub_one_eq_inf_fixSpace hxx (fun v hv => hN x hxF v hv) ?_
  rw [h1, hdims.1, hdims.2]

omit [FiniteDimensional (ZMod 2) M] in
theorem omegaInvariant_inf_fixOf {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) :
    OmegaInvariant ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
      (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) := by
  intro g hgK v hv
  obtain ⟨hgF, hgp, -⟩ := mem_fixGroup_sup_span_pair.mp hgK
  have hgO : (g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp g.2).1
  have hmap := map_fixOf_conj ρ g (fun x => map_conj_radFix hq hp0 hp hpF hgO hgF x)
  rw [hgp] at hmap
  refine ⟨hN g hgF v hv.1, ?_⟩
  rw [← hmap]
  exact ⟨v, hv.2, rfl⟩

theorem timmesfeld_2_1_b2 {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ}
    (hm : 3 ≤ m) (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ F N p p₁) {p' p₁' : V}
    (hp'K : p' ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}))
    (hp₁'K : p₁' ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁})) (hp'0 : p' ≠ 0)
    (hp' : q p' = 0) (hp₁' : q p₁' = 0) (hpp₁' : polar q p' p₁' = 1) :
    OmegaInvariant ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
        (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) ∧
      RadDecomp ρ (F ⊔ Submodule.span (ZMod 2) {p, p₁})
        (N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) p' p₁' := by
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  set W := N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) with hWdef
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁'0 : p₁' ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁'
    exact zero_ne_one hpp₁'
  have hW : OmegaInvariant ρ K W := omegaInvariant_inf_fixOf ρ hN hpF hp0 hp
  refine ⟨hW, ?_⟩
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  have hp'F : p' ∈ perp q F := perp_sup_span_pair_le hp'K
  have hp₁'F : p₁' ∈ perp q F := perp_sup_span_pair_le hp₁'K
  have hp₁'p' : polar q p₁' p' = 1 := by rw [polar_comm, hpp₁']
  obtain ⟨c, hcKK, -, hcR, hc1, hca⟩ :=
    exists_mem_radFix_not_isTypeA hq hK (by omega) hp'K hp₁'K hp'0 hp' hpp₁'
  obtain ⟨c', hc'KK, -, hc'R, hc'1, hc'a⟩ :=
    exists_mem_radFix_not_isTypeA hq hK (by omega) hp₁'K hp'K hp₁'0 hp₁' hp₁'p'
  have hp'c : polar q p' c = 0 := (mem_perp_sup_span_pair.mp hcKK).2.1
  have hp₁'c' : polar q p₁' c' = 0 := (mem_perp_sup_span_pair.mp hc'KK).2.1
  set a : omegaGroup q hq := ⟨eichler q p' c, (radFix_le_omegaFix hq hp'0 hp' hcR).1⟩ with ha
  set b : omegaGroup q hq := ⟨eichler q p₁' c', (radFix_le_omegaFix hq hp₁'0 hp₁' hc'R).1⟩
    with hb
  have hD' := radDecomp_of_pair ρ hF (by omega) hN hpF hp₁F hp'F hp₁'F hp0 hp'0 hp hp₁ hp'
    hp₁' hpp₁ hpp₁' hD
  have hDa := (timmesfeld_2_1_b0 ρ hF (by omega) hdim hN hp₁'F hp'F hp₁'0 hp₁' hp' hp₁'p'
    hD'.symm a (radFix_anti le_sup_left p' hcR) hc1 hca).1
  have hDb := (timmesfeld_2_1_b0 ρ hF (by omega) hdim hN hp'F hp₁'F hp'0 hp' hp₁' hpp₁' hD'
    b (radFix_anti le_sup_left p₁' hc'R) hc'1 hc'a).1
  have haa : ρ a * ρ a = 1 := by
    rw [← map_mul, show a * a = 1 from Subtype.ext (eichler_mul_self hp'c), map_one]
  have hbb : ρ b * ρ b = 1 := by
    rw [← map_mul, show b * b = 1 from Subtype.ext (eichler_mul_self hp₁'c'), map_one]
  have haW : ∀ w ∈ W, ρ a w ∈ W := hW a hcR.2
  have hbW : ∀ w ∈ W, ρ b w ∈ W := hW b hc'R.2
  have hWN : W ≤ N := inf_le_left
  have hab : W ⊓ fixSpace (ρ a) ⊓ fixSpace (ρ b) = ⊥ := by
    rw [eq_bot_iff, ← hD'.2]
    rintro v ⟨⟨hvW, hva⟩, hvb⟩
    have h1 : v ∈ N ⊓ fixSpace (ρ a) := ⟨hWN hvW, hva⟩
    have h2 : v ∈ N ⊓ fixSpace (ρ b) := ⟨hWN hvW, hvb⟩
    rw [hDa] at h1
    rw [hDb] at h2
    exact ⟨h1, h2⟩
  have hsum := sup_inf_fixSpace_eq haa hbb haW hbW hab
  have hWa : W ⊓ fixSpace (ρ a) = W ⊓ fixOf ρ (radFix q K p' : Set (V ≃ₗ[ZMod 2] V)) := by
    refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩) (fun v hv => ⟨hv.1, mem_fixSpace.mpr (hv.2 a hcR)⟩)
    have h1 : v ∈ N ⊓ fixSpace (ρ a) := ⟨hWN hv.1, hv.2⟩
    rw [hDa] at h1
    exact fixOf_anti ρ (fun t ht => radFix_anti le_sup_left p' ht) h1.2
  have hWb : W ⊓ fixSpace (ρ b) = W ⊓ fixOf ρ (radFix q K p₁' : Set (V ≃ₗ[ZMod 2] V)) := by
    refine le_antisymm (fun v hv => ⟨hv.1, ?_⟩) (fun v hv => ⟨hv.1, mem_fixSpace.mpr (hv.2 b hc'R)⟩)
    have h1 : v ∈ N ⊓ fixSpace (ρ b) := ⟨hWN hv.1, hv.2⟩
    rw [hDb] at h1
    exact fixOf_anti ρ (fun t ht => radFix_anti le_sup_left p₁' ht) h1.2
  refine ⟨by rw [← hWa, ← hWb]; exact hsum, ?_⟩
  rw [← hWa, ← hWb, eq_bot_iff, ← hab]
  rintro v ⟨⟨hvW, hva⟩, -, hvb⟩
  exact ⟨⟨hvW, hva⟩, hvb⟩

theorem timmesfeld_2_1_b_dvd : ∀ (m : ℕ) {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {p p₁ : V}, F ⊓ perp q F = ⊥ → 1 ≤ m → finrank (ZMod 2) (perp q F) = 2 * m →
    OmegaInvariant ρ F N → p ∈ perp q F → p₁ ∈ perp q F → p ≠ 0 → q p = 0 → q p₁ = 0 →
    polar q p p₁ = 1 → RadDecomp ρ F N p p₁ → 2 ^ (m - 1) ∣ finrank (ZMod 2) N := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ hF hm hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · rw [show m - 1 = 0 by omega, pow_zero]
    exact one_dvd _
  have htwo := (finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD).2
  rcases Nat.lt_or_ge m 3 with h2' | h3
  · rw [show m - 1 = 1 by omega, pow_one, htwo]
    exact dvd_mul_right _ _
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  obtain ⟨p', hp'K, hp'0, hp'⟩ := exists_singular_mem_perp (q := q) (F := K) (by omega)
  obtain ⟨p₁', hp₁'K, hp₁', hpp₁'⟩ := exists_hyperbolic_partner hq hK hp'K hp'0 hp'
  obtain ⟨hW, hDW⟩ := timmesfeld_2_1_b2 ρ hF h3 hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hp'K hp₁'K
    hp'0 hp' hp₁' hpp₁'
  have := ih (m - 1) (by omega) hK (by omega) (by omega) hW hp'K hp₁'K hp'0 hp' hp₁' hpp₁' hDW
  rw [htwo, show m - 1 = (m - 1 - 1) + 1 by omega, pow_succ, mul_comm]
  exact mul_dvd_mul_left 2 this

theorem timmesfeld_2_1_b_dvd_omega {m : ℕ} (hm : 1 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    2 ^ (m - 1) ∣ finrank (ZMod 2) M := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hD : RadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  have h := timmesfeld_2_1_b_dvd ρ m hF hm (by rw [perp_bot, finrank_top]; exact hdim)
    (fun g _ v _ => Submodule.mem_top) (by rw [perp_bot]; exact Submodule.mem_top)
    (by rw [perp_bot]; exact Submodule.mem_top) hp0 hp hp₁ hpp₁ hD
  rwa [finrank_top] at h

end S2

end CFSG.LargeExtraspecial
