module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S2OrthMinus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

theorem finrank_map_add_finrank_inf_ker {K M M₂ : Type*} [Field K] [AddCommGroup M]
    [Module K M] [AddCommGroup M₂] [Module K M₂] [FiniteDimensional K M] (f : M →ₗ[K] M₂)
    (N : Submodule K M) :
    finrank K (N.map f) + finrank K (N ⊓ LinearMap.ker f : Submodule K M) = finrank K N := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.comp N.subtype)
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  have e : (LinearMap.ker f).comap N.subtype = (N ⊓ LinearMap.ker f).comap N.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  rw [e, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)] at h
  exact h

section Rad

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem radDecomp_mono {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) (perp q F) = 2 * m) {N : Submodule (ZMod 2) M}
    (hN : OmegaInvariant ρ F N) {p p₁ : V} (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F)
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ F N p p₁) {F' : Submodule (ZMod 2) V} (hFF' : F ≤ F')
    {N' : Submodule (ZMod 2) M} (hN'N : N' ≤ N) {x y : omegaGroup q hq}
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q F' p₁) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1)
    (hxa : ¬ IsTypeA q x 2) (hy : (y : V ≃ₗ[ZMod 2] V) ∈ radFix q F' p)
    (hy1 : (y : V ≃ₗ[ZMod 2] V) ≠ 1) (hya : ¬ IsTypeA q y 2)
    (hN'x : ∀ v ∈ N', ρ x v ∈ N') (hN'y : ∀ v ∈ N', ρ y v ∈ N') :
    RadDecomp ρ F' N' p p₁ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  set A := N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V)) with hA
  set B := N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V)) with hB
  obtain ⟨hxB, hxB'⟩ := timmesfeld_2_1_b0 ρ hF hm hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD x
    (radFix_anti hFF' p₁ hx) hx1 hxa
  obtain ⟨hyA, hyA'⟩ := timmesfeld_2_1_b0 ρ hF hm hdim hN hp₁F hpF hp₁0 hp₁ hp hpp₁' hD.symm y
    (radFix_anti hFF' p hy) hy1 hya
  have hfix : ∀ {r : V} {z : omegaGroup q hq}, (z : V ≃ₗ[ZMod 2] V) ∈ radFix q F' r →
      N ⊓ fixSpace (ρ z) = N ⊓ fixOf ρ (radFix q F r : Set (V ≃ₗ[ZMod 2] V)) →
      N' ⊓ fixOf ρ (radFix q F' r : Set (V ≃ₗ[ZMod 2] V)) =
        N' ⊓ (N ⊓ fixOf ρ (radFix q F r : Set (V ≃ₗ[ZMod 2] V))) := by
    intro r z hz hzN
    apply le_antisymm
    · rintro v ⟨hvN', hvfix⟩
      refine ⟨hvN', ?_⟩
      have hv : v ∈ N ⊓ fixSpace (ρ z) := ⟨hN'N hvN', mem_fixSpace.mpr (hvfix z hz)⟩
      rwa [hzN] at hv
    · rintro v ⟨hvN', -, hvfix⟩
      exact ⟨hvN', fixOf_anti ρ (radFix_anti hFF' r) hvfix⟩
  have hA' := hfix hy hyA
  have hB' := hfix hx hxB
  have hbound : ∀ {z : omegaGroup q hq} {X : Submodule (ZMod 2) M},
      (∀ v ∈ N', ρ z v ∈ N') → N ⊓ fixSpace (ρ z) = X → N.map ((ρ z : M →ₗ[ZMod 2] M) - 1) = X →
      finrank (ZMod 2) N' ≤ 2 * finrank (ZMod 2) (N' ⊓ X : Submodule (ZMod 2) M) := by
    intro z X hz hzX hzX'
    have h := finrank_map_add_finrank_inf_ker ((ρ z : M →ₗ[ZMod 2] M) - 1) N'
    have h1 : N' ⊓ LinearMap.ker ((ρ z : M →ₗ[ZMod 2] M) - 1) = N' ⊓ X := by
      rw [← hzX, ← inf_assoc, inf_eq_left.mpr hN'N]
    have h2 : N'.map ((ρ z : M →ₗ[ZMod 2] M) - 1) ≤ N' ⊓ X := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · change ρ z v - v ∈ N'
        exact N'.sub_mem (hz v hv) hv
      · rw [← hzX']
        exact ⟨v, hN'N hv, rfl⟩
    rw [h1] at h
    have h3 := Submodule.finrank_mono h2
    omega
  have hAb : finrank (ZMod 2) N' ≤ 2 * finrank (ZMod 2) (N' ⊓ A : Submodule (ZMod 2) M) :=
    hbound hN'y hyA hyA'
  have hBb : finrank (ZMod 2) N' ≤ 2 * finrank (ZMod 2) (N' ⊓ B : Submodule (ZMod 2) M) :=
    hbound hN'x hxB hxB'
  have hdisj : (N' ⊓ A) ⊓ (N' ⊓ B) = ⊥ := by
    rw [eq_bot_iff, ← hD.2]
    exact inf_le_inf inf_le_right inf_le_right
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (N' ⊓ A) (N' ⊓ B)
  rw [hdisj, finrank_bot, add_zero] at hsup
  have hle : (N' ⊓ A) ⊔ (N' ⊓ B) ≤ N' := sup_le inf_le_left inf_le_left
  have heq : (N' ⊓ A) ⊔ (N' ⊓ B) = N' :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨?_, ?_⟩
  · rw [hA', hB']
    exact heq
  · rw [hA', hB']
    exact hdisj

end Rad

section Witt

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem perp_sup (A B : Submodule (ZMod 2) V) : perp q (A ⊔ B) = perp q A ⊓ perp q B := by
  ext x
  simp only [Submodule.mem_inf, mem_perp]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Submodule.mem_sup_left hy),
      fun y hy => h y (Submodule.mem_sup_right hy)⟩
  · rintro ⟨hA, hB⟩ y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_left, hA a ha, hB b hb, add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem le_perp_of_singular {T : Submodule (ZMod 2) V} (hT : ∀ x ∈ T, q x = 0) :
    T ≤ perp q T := by
  intro x hx
  rw [mem_perp]
  intro y hy
  rw [polar, hT _ (T.add_mem hy hx), hT y hy, hT x hx, sub_zero, sub_zero]

theorem finrank_perp (hq : q.polarBilin.Nondegenerate) (A : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (perp q A) + finrank (ZMod 2) A = finrank (ZMod 2) V := by
  have := LinearMap.BilinForm.finrank_orthogonal hq A
  have h2 := Submodule.finrank_le A
  unfold perp
  omega

theorem perp_perp (hq : q.polarBilin.Nondegenerate) (A : Submodule (ZMod 2) V) :
    perp q (perp q A) = A :=
  LinearMap.BilinForm.orthogonal_orthogonal hq (isRefl_polarBilin q) A

theorem finrank_le_of_forall_singular_mem (hq : q.polarBilin.Nondegenerate)
    {T U : Submodule (ZMod 2) V} (hTmax : ∀ x ∈ perp q T, q x = 0 → x ∈ T)
    (hU : ∀ x ∈ U, q x = 0) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) T := by
  have hP : U ⊓ perp q T ≤ T := fun x hx => hTmax x hx.2 (hU x hx.1)
  have hP' : U ⊓ perp q T ≤ T ⊓ perp q U :=
    le_inf hP (inf_le_left.trans (le_perp_of_singular hU))
  have h1 : perp q (T ⊔ perp q U) = U ⊓ perp q T := by
    rw [perp_sup, perp_perp hq, inf_comm]
  have h2 := finrank_perp hq (T ⊔ perp q U)
  rw [h1] at h2
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq T (perp q U)
  have h4 := finrank_perp hq U
  have h5 := Submodule.finrank_mono hP'
  omega

theorem isMinusType_of_aniso (hq : q.polarBilin.Nondegenerate) {E : Submodule (ZMod 2) V}
    (hE : E ⊓ perp q E = ⊥) (hE2 : finrank (ZMod 2) E = 2)
    (hEa : ∀ x ∈ E, q x = 0 → x = 0) {m : ℕ} (hdim : finrank (ZMod 2) V = 2 * (m + 1))
    {U : Submodule (ZMod 2) V} (hU : ∀ x ∈ U, q x = 0) (hUm : m + 1 ≤ finrank (ZMod 2) U) :
    IsMinusType q E m := by
  intro T hTE hT
  by_contra hlt
  push Not at hlt
  have hTE' : T ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot _).mpr (hEa x hx.2 (hT x hx.1))
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T E
  rw [hTE', finrank_bot, add_zero, hE2] at h1
  have h2 := finrank_perp hq (T ⊔ E)
  rw [perp_sup] at h2
  have hTle : T ≤ perp q T ⊓ perp q E := le_inf (le_perp_of_singular hT) hTE
  have h3 := Submodule.finrank_mono hTle
  have hTeq : T = perp q T ⊓ perp q E :=
    Submodule.eq_of_le_of_finrank_le hTle (by omega)
  have hTmax : ∀ x ∈ perp q T, q x = 0 → x ∈ T := by
    intro x hx hqx
    obtain ⟨w, hwE, hxw⟩ := exists_mem_perp_sub_mem hE x
    have hET : E ≤ perp q T := by
      intro e he
      rw [mem_perp]
      intro y hy
      have := (mem_perp.mp (hTE hy)) e he
      rw [polar_comm]
      exact this
    have hwT : w ∈ T := by
      rw [hTeq]
      refine ⟨?_, hwE⟩
      have := (perp q T).sub_mem hx (hET hxw)
      rwa [sub_sub_cancel] at this
    have hq0 : q (x - w) = 0 := by
      have e1 : x = (x - w) + w := by abel
      have h0 : q ((x - w) + w) = q (x - w) + q w + polar q (x - w) w := by
        rw [polar]; abel
      rw [← e1, hqx, hT w hwT, add_zero, (mem_perp.mp (hTE hwT)) _ hxw, add_zero] at h0
      exact h0.symm
    have h00 := hEa _ hxw hq0
    rw [sub_eq_zero] at h00
    rw [h00]
    exact hwT
  have := finrank_le_of_forall_singular_mem hq hTmax hU
  omega

theorem exists_aniso_partner (hq : q.polarBilin.Nondegenerate) {d : V} (hd : q d = 1)
    (h4 : 4 ≤ finrank (ZMod 2) V) : ∃ e : V, q e = 1 ∧ polar q d e = 1 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact zero_ne_one hd
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  obtain ⟨y, -, hyd⟩ := exists_mem_perp_polar_eq_one hq hF (by rw [perp_bot]; exact
    Submodule.mem_top) hd0
  have hdy : polar q d y = 1 := by rw [polar_comm]; exact hyd
  rcases zmod2_eq_zero_or_eq_one (q y) with hy | hy
  · have hK := sup_span_pair_inf_perp_eq_bot hF (by rw [perp_bot]; exact Submodule.mem_top)
      (by rw [perp_bot]; exact Submodule.mem_top) hdy
    have hKdim := finrank_perp_sup_span_pair hq hF (by rw [perp_bot]; exact Submodule.mem_top)
      (by rw [perp_bot]; exact Submodule.mem_top) hdy
    rw [perp_bot, finrank_top] at hKdim
    have hne : perp q (⊥ ⊔ Submodule.span (ZMod 2) {d, y}) ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hKdim
      omega
    obtain ⟨c, hcK, hc⟩ := exists_mem_perp_map_eq_one hq hK hne
    obtain ⟨-, hdc, hyc⟩ := mem_perp_sup_span_pair.mp hcK
    refine ⟨y + c, ?_, ?_⟩
    · have h0 : q (y + c) = q y + q c + polar q y c := by rw [polar]; abel
      rw [h0, hy, hc, hyc]
      rfl
    · rw [polar_add_right, hdy, hdc, add_zero]
  · exact ⟨y, hy, hdy⟩

end Witt

end CFSG.LargeExtraspecial.S8
