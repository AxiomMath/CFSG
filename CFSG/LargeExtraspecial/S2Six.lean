module

public import CFSG.LargeExtraspecial.S2OrthOne
public import CFSG.LargeExtraspecial.S2SpOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open LinearMap (BilinForm)

namespace S2

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

omit [FiniteDimensional (ZMod 2) M] in
theorem exists_smul_of_finrank_eq_one {W : Submodule (ZMod 2) M} (hW : finrank (ZMod 2) W = 1)
    {φ : M →ₗ[ZMod 2] M} (hφ : ∀ v ∈ W, φ v ∈ W) : ∃ c : ZMod 2, ∀ v ∈ W, φ v = c • v := by
  obtain ⟨w, hw0, hspan⟩ := finrank_eq_one_iff'.mp hW
  obtain ⟨c, hc⟩ := hspan ⟨φ w, hφ w w.2⟩
  refine ⟨c, fun v hv => ?_⟩
  obtain ⟨a, ha⟩ := hspan ⟨v, hv⟩
  have hv' : v = a • (w : M) := (congrArg Subtype.val ha).symm
  have hc' : φ w = c • (w : M) := (congrArg Subtype.val hc).symm
  rw [hv', map_smul, hc', smul_comm]

omit [FiniteDimensional (ZMod 2) M] in
theorem smul_eq_of_map {W W₁ : Submodule (ZMod 2) M} {T : M ≃ₗ[ZMod 2] M}
    (hT : W.map (T : M →ₗ[ZMod 2] M) = W₁) (hW : W ≠ ⊥) {φ : M →ₗ[ZMod 2] M}
    (hcomm : ∀ v ∈ W, φ (T v) = T (φ v)) {c c₁ : ZMod 2} (hc : ∀ v ∈ W, φ v = c • v)
    (hc₁ : ∀ v ∈ W₁, φ v = c₁ • v) : c = c₁ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hTw : T w ∈ W₁ := hT ▸ ⟨w, hw, rfl⟩
  have h : c • T w = c₁ • T w := by rw [← map_smul, ← hc w hw, ← hcomm w hw, hc₁ _ hTw]
  have hTw0 : T w ≠ 0 := fun h0 => hw0 (T.map_eq_zero_iff.mp h0)
  rcases zmod2_eq_zero_or_eq_one c with rfl | rfl <;>
    rcases zmod2_eq_zero_or_eq_one c₁ with rfl | rfl
  · rfl
  · rw [zero_smul, one_smul] at h
    exact absurd h.symm hTw0
  · rw [zero_smul, one_smul] at h
    exact absurd h hTw0
  · rfl

section Omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem timmesfeld_2_6_1_omega : ∀ (m : ℕ) {F : Submodule (ZMod 2) V}
    {N : Submodule (ZMod 2) M} {p p₁ : V}, F ⊓ perp q F = ⊥ → 2 ≤ m →
    finrank (ZMod 2) (perp q F) = 2 * m → OmegaInvariant ρ F N → p ∈ perp q F →
    p₁ ∈ perp q F → p ≠ 0 → q p = 0 → q p₁ = 0 → polar q p p₁ = 1 → RadDecomp ρ F N p p₁ →
    finrank (ZMod 2) N = 2 ^ (m - 1) → ∀ φ : M →ₗ[ZMod 2] M, (∀ v ∈ N, φ v ∈ N) →
    (∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N,
      φ (ρ g v) = ρ g (φ v)) → ∃ c : ZMod 2, ∀ v ∈ N, φ v = c • v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ hF hm hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hdimN φ hφN hcomm
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have htwo := finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD
  have hpres : ∀ a : V, a ∈ perp q F → a ≠ 0 → q a = 0 → ∀ v ∈ N ⊓
      fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V)), φ v ∈ N ⊓
        fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V)) := by
    intro a haF ha0 ha v hv
    refine ⟨hφN v hv.1, fun t ht => ?_⟩
    rw [← hcomm t ht.2 v hv.1, hv.2 t ht]
  have hscal : ∀ a a₁ : V, a ∈ perp q F → a₁ ∈ perp q F → a ≠ 0 → q a = 0 → q a₁ = 0 →
      polar q a a₁ = 1 → RadDecomp ρ F N a a₁ →
      finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V))) = 2 ^ (m - 2) →
      ∃ c : ZMod 2, ∀ v ∈ N ⊓ fixOf ρ (radFix q F a : Set (V ≃ₗ[ZMod 2] V)), φ v = c • v := by
    intro a a₁ haF ha₁F ha0 ha ha₁ haa₁ hDa hdimW
    rcases Nat.lt_or_ge m 3 with h2 | h3
    · exact exists_smul_of_finrank_eq_one (by rw [hdimW, show m - 2 = 0 by omega, pow_zero])
        (hpres a haF ha0 ha)
    set K := F ⊔ Submodule.span (ZMod 2) {a, a₁} with hKdef
    have hK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF haF ha₁F haa₁
    have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
      finrank_perp_sup_span_pair hq hF haF ha₁F haa₁
    obtain ⟨p', hp'K, hp'0, hp'⟩ := exists_singular_mem_perp (q := q) (F := K) (by omega)
    obtain ⟨p₁', hp₁'K, hp₁', hpp₁'⟩ := exists_hyperbolic_partner hq hK hp'K hp'0 hp'
    obtain ⟨hW, hDW⟩ := timmesfeld_2_1_b2 ρ hF h3 hdim hN haF ha₁F ha0 ha ha₁ haa₁ hDa hp'K
      hp₁'K hp'0 hp' hp₁' hpp₁'
    exact ih (m - 1) (by omega) hK (by omega) (by omega) hW hp'K hp₁'K hp'0 hp' hp₁' hpp₁' hDW
      (by rw [hdimW]; congr 1) φ (hpres a haF ha0 ha)
      (fun g hg v hv => hcomm g (fixGroup_anti le_sup_left hg) v hv.1)
  have hdimW : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) =
      2 ^ (m - 2) := by
    have : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [show m - 1 = (m - 2) + 1 by omega, pow_succ, mul_comm]
    omega
  obtain ⟨c, hc⟩ := hscal p p₁ hpF hp₁F hp0 hp hp₁ hpp₁ hD hdimW
  obtain ⟨c₁, hc₁⟩ := hscal p₁ p hp₁F hpF hp₁0 hp₁ hp hp₁p hD.symm (by rw [htwo.1, hdimW])
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hpF hp₁F hp0 hp₁0 hp hp₁
  have hgΩ := radGen_le_omegaFix hq F hg
  set g' : omegaGroup q hq := ⟨g, hgΩ.1⟩ with hg'
  have hmap := map_inf_fixOf_radFix ρ hN g' hgΩ.2 hpF hp0 hp
  have hgp' : (g' : V ≃ₗ[ZMod 2] V) p = p₁ := hgp
  rw [hgp'] at hmap
  have hWne : N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimW
    exact absurd hdimW.symm (pow_ne_zero _ (by norm_num))
  have hcc := smul_eq_of_map hmap hWne (fun v hv => hcomm g' hgΩ.2 v hv.1) hc hc₁
  refine ⟨c, fun v hv => ?_⟩
  rw [← hD.1] at hv
  obtain ⟨w, hw, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hc w hw, hc₁ w₁ hw₁, ← hcc, smul_add]

theorem timmesfeld_2_6_1_omegaGroup {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hdimM : finrank (ZMod 2) M = 2 ^ (m - 1)) {φ : M →ₗ[ZMod 2] M}
    (hcomm : ∀ (g : omegaGroup q hq) (v : M), φ (ρ g v) = ρ g (φ v)) :
    ∃ c : ZMod 2, φ = c • LinearMap.id := by
  have hD : RadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  obtain ⟨c, hc'⟩ := timmesfeld_2_6_1_omega ρ m (bot_inf_eq _) hm
    (by rw [perp_bot, finrank_top]; exact hdim) (fun g _ v _ => Submodule.mem_top)
    (by rw [perp_bot]; exact Submodule.mem_top) (by rw [perp_bot]; exact Submodule.mem_top) hp0
    hp hp₁ hpp₁ hD (by rw [finrank_top]; exact hdimM) φ (fun _ _ => Submodule.mem_top)
    (fun g _ v _ => hcomm g v)
  exact ⟨c, LinearMap.ext fun v => by rw [hc' v Submodule.mem_top]; rfl⟩

end Omega

section Sp

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

theorem timmesfeld_2_6_1_sp (hf : f.IsAlt) (hnd : f.Nondegenerate) : ∀ (m : ℕ)
    {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M} {p p₁ : V}, F ⊓ spPerp f F = ⊥ →
    1 ≤ m → finrank (ZMod 2) (spPerp f F) = 2 * m → SpInvariant ρ F N → p ∈ spPerp f F →
    p₁ ∈ spPerp f F → f p p₁ = 1 → SpRadDecomp ρ F N p p₁ → finrank (ZMod 2) N = 2 ^ m →
    ∀ φ : M →ₗ[ZMod 2] M, (∀ v ∈ N, φ v ∈ N) →
    (∀ g : TauCeti.BilinForm.isometryGroup f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N,
      φ (ρ g v) = ρ g (φ v)) → ∃ c : ZMod 2, ∀ v ∈ N, φ v = c • v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ hF hm hdim hN hpF hp₁F hpp₁ hD hdimN φ hφN hcomm
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  have htwo := sp_finrank_eq_two_mul ρ hf hnd hF hN hpF hp₁F hpp₁ hD
  have hpres : ∀ a : V, ∀ v ∈ N ⊓ fixOf ρ (spRadFix f F a : Set (V ≃ₗ[ZMod 2] V)),
      φ v ∈ N ⊓ fixOf ρ (spRadFix f F a : Set (V ≃ₗ[ZMod 2] V)) := by
    intro a v hv
    refine ⟨hφN v hv.1, fun t ht => ?_⟩
    rw [← hcomm t ht.2 v hv.1, hv.2 t ht]
  have hscal : ∀ a a₁ : V, a ∈ spPerp f F → a₁ ∈ spPerp f F → f a a₁ = 1 →
      SpRadDecomp ρ F N a a₁ →
      finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F a : Set (V ≃ₗ[ZMod 2] V))) = 2 ^ (m - 1) →
      ∃ c : ZMod 2, ∀ v ∈ N ⊓ fixOf ρ (spRadFix f F a : Set (V ≃ₗ[ZMod 2] V)),
        φ v = c • v := by
    intro a a₁ haF ha₁F haa₁ hDa hdimW
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · exact exists_smul_of_finrank_eq_one (by rw [hdimW, show m - 1 = 0 by omega, pow_zero])
        (hpres a)
    set K := F ⊔ Submodule.span (ZMod 2) {a, a₁} with hKdef
    have hK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF haF ha₁F haa₁
    have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
      finrank_spPerp_sup_span_pair hf hnd hF haF ha₁F haa₁
    have hne : spPerp f K ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hKdim
      omega
    obtain ⟨p', hp'K, hp'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨p₁', hp₁'K, hpp₁'⟩ := sp_exists_partner hf hnd hK hp'K hp'0
    obtain ⟨hW, hDW⟩ := sp_timmesfeld_2_1_b2 ρ hf hnd hF hdim hN haF ha₁F haa₁ hDa hp'K hp₁'K
      hpp₁'
    exact ih (m - 1) (by omega) hK (by omega) (by omega) hW hp'K hp₁'K hpp₁' hDW hdimW φ
      (hpres a) (fun g hg v hv => hcomm g (fixGroup_anti le_sup_left hg) v hv.1)
  have hdimW : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V))) =
      2 ^ (m - 1) := by
    have : 2 ^ m = 2 * 2 ^ (m - 1) := by
      rw [show m = (m - 1) + 1 by omega, pow_succ, mul_comm, Nat.add_sub_cancel]
    omega
  obtain ⟨c, hc⟩ := hscal p p₁ hpF hp₁F hpp₁ hD hdimW
  obtain ⟨c₁, hc₁⟩ := hscal p₁ p hp₁F hpF hp₁p hD.symm (by rw [htwo.1, hdimW])
  obtain ⟨g, hg, hgp⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp₁F hp0 hp₁0
  have hgS := spRadGen_le_spFix F hg
  set g' : TauCeti.BilinForm.isometryGroup f := ⟨g, hgS.1⟩ with hg'
  have hmap := map_inf_fixOf_spRadFix ρ hf hnd hN g' hgS.2 hpF hp0
  have hgp' : (g' : V ≃ₗ[ZMod 2] V) p = p₁ := hgp
  rw [hgp'] at hmap
  have hWne : N ⊓ fixOf ρ (spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdimW
    exact absurd hdimW.symm (pow_ne_zero _ (by norm_num))
  have hcc := smul_eq_of_map hmap hWne (fun v hv => hcomm g' hgS.2 v hv.1) hc hc₁
  refine ⟨c, fun v hv => ?_⟩
  rw [← hD.1] at hv
  obtain ⟨w, hw, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hc w hw, hc₁ w₁ hw₁, ← hcc, smul_add]

theorem timmesfeld_2_6_1_spGroup (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hc : IsCompl (fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hdimM : finrank (ZMod 2) M = 2 ^ m) {φ : M →ₗ[ZMod 2] M}
    (hcomm : ∀ (g : TauCeti.BilinForm.isometryGroup f) (v : M), φ (ρ g v) = ρ g (φ v)) :
    ∃ c : ZMod 2, φ = c • LinearMap.id := by
  have hD : SpRadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [SpRadDecomp, spRadFix_bot, spRadFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  obtain ⟨c, hc'⟩ := timmesfeld_2_6_1_sp ρ hf hnd m (bot_inf_eq _) hm
    (by rw [spPerp_bot, finrank_top]; exact hdim) (fun g _ v _ => Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    hpp₁ hD (by rw [finrank_top]; exact hdimM) φ (fun _ _ => Submodule.mem_top)
    (fun g _ v _ => hcomm g v)
  exact ⟨c, LinearMap.ext fun v => by rw [hc' v Submodule.mem_top]; rfl⟩

end Sp

end S2

end CFSG.LargeExtraspecial
