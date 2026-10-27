module

public import CFSG.LieType.BorelTits.OrthogonalOdd
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.LieType.BorelTits

universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
variable {H : Type w} [Group H]

section Completion

variable {F : ReflForm K V} (ρ : H →* Module.End K V)

theorem le_flagStab_isoCompletion (hρ : IsIsometric F ρ) {X : ℕ → Submodule K V} (m : ℕ)
    {G : Subgroup H} (hG : ∀ h ∈ G, ∀ k, ∀ v ∈ X k, ρ h v ∈ X k) :
    G ≤ flagStab ρ (isoCompletion F X m) := by
  have key : ∀ h ∈ G, ∀ k, ∀ v ∈ isoCompletion F X m k, ρ h v ∈ isoCompletion F X m k := by
    intro h hh k v hv
    unfold isoCompletion at hv ⊢
    split_ifs at hv ⊢
    · exact hG h hh k v hv
    · exact hρ.apply_mem_perp_of_forall (fun w hw => hG _ (inv_mem hh) _ w hw) hv
    · exact Submodule.mem_top
  intro h hh k v hv
  exact ⟨key h hh k v hv, key h⁻¹ (inv_mem hh) k v hv⟩

theorem le_flagKernel_isoCompletion (hρ : IsIsometric F ρ) {X : ℕ → Submodule K V}
    (hX0 : X 0 = ⊥) {m : ℕ} {R : Subgroup H} (hstab : R ≤ flagStab ρ (isoCompletion F X m))
    (htriv : ∀ k < m, ∀ g ∈ R, ∀ v ∈ X (k + 1), ρ g v - v ∈ X k)
    (hmid : ∀ g ∈ R, ∀ v ∈ F.perp (X m), ρ g v - v ∈ X m) :
    R ≤ flagKernel ρ (isoCompletion F X m) := by
  intro g hg
  refine ⟨hstab hg, fun k v hv => ?_⟩
  rcases Nat.lt_or_ge k m with hk | hk
  · rw [isoCompletion_of_le (by omega)] at hv
    rw [isoCompletion_of_le hk.le]
    exact htriv k hk g hg v hv
  rcases Nat.eq_or_lt_of_le hk with hk | hk
  · rw [← hk] at hv ⊢
    have h1 : isoCompletion F X m (m + 1) = F.perp (X m) := by
      have := isoCompletion_perp (F := F) (X := X) (m := m) (le_refl m)
      rwa [show 2 * m + 1 - m = m + 1 by omega] at this
    rw [h1] at hv
    rw [isoCompletion_of_le le_rfl]
    exact hmid g hg v hv
  rcases Nat.lt_or_ge k (2 * m + 1) with hk2 | hk2
  ·
    have h1 : isoCompletion F X m (k + 1) = F.perp (X (2 * m - k)) := by
      have := isoCompletion_perp (F := F) (X := X) (m := m) (k := 2 * m - k) (by omega)
      rwa [show 2 * m + 1 - (2 * m - k) = k + 1 by omega] at this
    have h2 : isoCompletion F X m k = F.perp (X (2 * m - k + 1)) := by
      have := isoCompletion_perp (F := F) (X := X) (m := m) (k := 2 * m - k + 1) (by omega)
      rwa [show 2 * m + 1 - (2 * m - k + 1) = k by omega] at this
    rw [h1] at hv
    rw [h2]
    intro w hw
    have h3 := hρ g (ρ g⁻¹ w) v
    rw [rep_apply_inv_apply] at h3
    rw [F.β_sub_right, h3, ← F.β_sub_left]
    exact hv _ (htriv _ (by omega) g⁻¹ (inv_mem hg) w hw)
  · have htop : isoCompletion F X m k = ⊤ := by
      rcases Nat.eq_or_lt_of_le hk2 with hk2 | hk2
      · rw [← hk2]
        exact isoCompletion_top hX0 m
      · exact isoCompletion_of_lt hk2
    rw [htop]
    exact Submodule.mem_top

end Completion

theorem le_or_le_of_forall_mem_or_mem {P A B : Submodule K V} (h : ∀ v ∈ P, v ∈ A ∨ v ∈ B) :
    P ≤ A ∨ P ≤ B := by
  by_contra! hcon
  obtain ⟨x, hxP, hxA⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨y, hyP, hyB⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have hxB := (h x hxP).resolve_left hxA
  have hyA := (h y hyP).resolve_right hyB
  rcases h (x + y) (add_mem hxP hyP) with hA | hB
  · exact hxA (by simpa using sub_mem hA hyA)
  · exact hyB (by simpa using sub_mem hB hxB)

namespace QuadForm

variable (Φ : QuadForm K V)

theorem isIsometric_of_Q {ρ : H →* Module.End K V} (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) :
    IsIsometric Φ.polar ρ :=
  fun h u v => Φ.polar_map_of_Q (hQ h) u v

theorem Q_sub_self {g : V →ₗ[K] V} (hg : ∀ v, Φ.Q (g v) = Φ.Q v) (v : V) :
    Φ.Q (g v - v) = -Φ.polar.β (g v - v) v := by
  have h := Φ.Q_add (g v - v) v
  rw [sub_add_cancel, hg] at h
  linear_combination -h

theorem exists_Q_add_smul_eq_zero [Finite K] (h2 : (2 : K) = 0) {a v : V} (hQa : Φ.Q a ≠ 0)
    (hva : Φ.polar.β v a = 0) : ∃ c : K, Φ.Q (v + c • a) = 0 := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two
    (CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h2)) (-(Φ.Q v / Φ.Q a))
  refine ⟨c, ?_⟩
  rw [Φ.Q_add, Φ.Q_smul, Φ.polar.smul_right, hva, mul_zero, add_zero, sq, ← hc]
  field_simp
  ring

theorem sub_mem_or_sub_reflect_mem [FiniteDimensional K V] {g : V →ₗ[K] V}
    (hg : ∀ v, Φ.Q (g v) = Φ.Q v) {Z : Submodule K V} (hZ : Φ.IsTotallySingular Z)
    (hgZ : ∀ v ∈ Φ.polar.perp Z, g v ∈ Φ.polar.perp Z) {a : V} (ha : a ∈ Φ.polar.perp Z)
    (hQa : Φ.Q a ≠ 0) (hW : ∀ v ∈ Φ.polar.perp (Z ⊔ K ∙ a), g v - v ∈ Z) :
    (∀ v ∈ Φ.polar.perp Z, g v - v ∈ Z) ∨
      ∀ v ∈ Φ.polar.perp Z, g v - (v - (Φ.polar.β v a / Φ.Q a) • a) ∈ Z := by
  have key : ∀ v ∈ Φ.polar.perp Z, v ∈ Z.comap (g - LinearMap.id) ∨
      v ∈ Z.comap (g - (LinearMap.id - (Φ.Q a)⁻¹ • (Φ.polar.toDual a).smulRight a)) := by
    intro v hv
    simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, ReflForm.toDual_apply]
    have hmem : g v - v ∈ Z ⊔ K ∙ a := by
      rw [← Φ.polar.perp_perp (Z ⊔ K ∙ a)]
      intro u hu
      have h1 := Φ.polar_map_of_Q hg u v
      have h2 : Φ.polar.β (g u - u) (g v) = 0 := hgZ v hv _ (hW u hu)
      rw [Φ.polar.β_sub_left] at h2
      rw [Φ.polar.β_sub_right]
      linear_combination h1 - h2
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp ht
    have hsa : Φ.polar.β s a = 0 := ha s hs
    have hvs : Φ.polar.β v s = 0 := by rw [Φ.polar_symm]; exact hv s hs
    have hQ := hg v
    rw [show g v = v + (s + μ • a) by rw [hst]; abel, Φ.Q_add, Φ.Q_add, Φ.Q_smul, hZ s hs,
      Φ.polar.add_right, Φ.polar.smul_right, Φ.polar.smul_right, hsa, hvs] at hQ
    have hμ : μ * (μ * Φ.Q a + Φ.polar.β v a) = 0 := by linear_combination hQ
    rcases mul_eq_zero.mp hμ with h | h
    · left
      rw [← hst, h, zero_smul, add_zero]
      exact hs
    · right
      have hμ' : μ = -(Φ.polar.β v a / Φ.Q a) := by
        field_simp
        linear_combination h
      rw [Φ.polar_symm a v, smul_smul, show g v - (v - ((Φ.Q a)⁻¹ * Φ.polar.β v a) • a) =
        s + (μ + Φ.polar.β v a / Φ.Q a) • a by rw [add_smul, ← add_assoc, hst]; field_simp; module,
        hμ', neg_add_cancel, zero_smul, add_zero]
      exact hs
  rcases le_or_le_of_forall_mem_or_mem key with h | h
  · refine Or.inl fun v hv => ?_
    simpa using h hv
  · refine Or.inr fun v hv => ?_
    have := h hv
    simp only [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, ReflForm.toDual_apply, smul_smul] at this
    rwa [Φ.polar_symm a v, ← div_eq_inv_mul] at this

end QuadForm

section Singular

variable (Φ : QuadForm K V) (ρ : H →* Module.End K V)

@[expose] def NoQuotientReflection : Prop :=
  ∀ h : H, ∀ Z : Submodule K V, Φ.IsTotallySingular Z → ∀ a ∈ Φ.polar.perp Z, Φ.Q a ≠ 0 →
    ¬∀ v ∈ Φ.polar.perp Z, ρ h v - (v - (Φ.polar.β v a / Φ.Q a) • a) ∈ Z

@[expose] def singSeq (R : Subgroup H) (k : ℕ) : Submodule K V where
  carrier := {w | w ∈ isoSeq Φ.polar ρ R k ∧ Φ.Q w = 0}
  add_mem' := by
    rintro u w ⟨hu, hQu⟩ ⟨hw, hQw⟩
    refine ⟨add_mem hu hw, ?_⟩
    rw [Φ.Q_add, hQu, hQw, isoSeq_isTotallyIsotropic Φ.polar ρ R k hw u hu, add_zero, add_zero]
  zero_mem' := ⟨Submodule.zero_mem _, Φ.Q_zero⟩
  smul_mem' := by
    rintro c w ⟨hw, hQw⟩
    exact ⟨Submodule.smul_mem _ c hw, by rw [Φ.Q_smul, hQw, mul_zero]⟩

variable {Φ ρ} in
theorem mem_singSeq {R : Subgroup H} {k : ℕ} {w : V} :
    w ∈ singSeq Φ ρ R k ↔ w ∈ isoSeq Φ.polar ρ R k ∧ Φ.Q w = 0 :=
  Iff.rfl

theorem singSeq_zero (R : Subgroup H) : singSeq Φ ρ R 0 = ⊥ := by
  ext w
  rw [mem_singSeq, isoSeq_zero, Submodule.mem_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, h ▸ Φ.Q_zero⟩⟩

theorem singSeq_le_isoSeq (R : Subgroup H) (k : ℕ) :
    singSeq Φ ρ R k ≤ isoSeq Φ.polar ρ R k :=
  fun _ h => h.1

theorem singSeq_mono (R : Subgroup H) : Monotone (singSeq Φ ρ R) :=
  fun _ _ hij _ hw => ⟨isoSeq_mono Φ.polar ρ R hij hw.1, hw.2⟩

theorem isTotallySingular_singSeq (R : Subgroup H) (k : ℕ) :
    Φ.IsTotallySingular (singSeq Φ ρ R k) :=
  fun _ h => h.2

variable {Φ ρ}

theorem apply_mem_singSeq (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (R : Subgroup H) (k : ℕ) {h : H}
    (hh : h ∈ Subgroup.normalizer (R : Set H)) {v : V} (hv : v ∈ singSeq Φ ρ R k) :
    ρ h v ∈ singSeq Φ ρ R k :=
  ⟨apply_mem_isoSeq Φ.polar ρ (Φ.isIsometric_of_Q hQ) R k hh hv.1, by rw [hQ, hv.2]⟩

theorem singSeq_triv (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (R : Subgroup H) (k : ℕ) {g : H}
    (hg : g ∈ R) {v : V} (hv : v ∈ singSeq Φ ρ R (k + 1)) : ρ g v - v ∈ singSeq Φ ρ R k := by
  have h1 : ρ g v - v ∈ isoSeq Φ.polar ρ R k := isoSeq_triv Φ.polar ρ R k hg hv.1
  refine ⟨h1, ?_⟩
  rw [Φ.Q_sub_self (hQ g), isoSeq_isTotallyIsotropic Φ.polar ρ R (k + 1) hv.1 _
    (isoSeq_le_succ Φ.polar ρ R k h1), neg_zero]

theorem singSeq_middle_triv [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ) (R : Subgroup H)
    (hR : IsPGroup p R) {g : H} (hg : g ∈ R) {v : V}
    (hv : v ∈ Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V))) :
    ρ g v - v ∈ singSeq Φ ρ R (Module.finrank K V) := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hρ := Φ.isIsometric_of_Q hQ
  have hWiso := isoSeq_isTotallyIsotropic Φ.polar ρ R (Module.finrank K V)
  have hWperp : ∀ u ∈ Φ.polar.perp (isoSeq Φ.polar ρ R (Module.finrank K V)),
      ρ g u - u ∈ singSeq Φ ρ R (Module.finrank K V) := fun u hu => by
    have h1 := isoSeq_middle_triv Φ.polar ρ p hρ R hR hg hu
    exact ⟨h1, by rw [Φ.Q_sub_self (hQ g), hu _ h1, neg_zero]⟩
  by_cases hsing : ∀ w ∈ isoSeq Φ.polar ρ R (Module.finrank K V), Φ.Q w = 0
  · have hZW : singSeq Φ ρ R (Module.finrank K V) = isoSeq Φ.polar ρ R (Module.finrank K V) :=
      le_antisymm (singSeq_le_isoSeq Φ ρ R _) fun w hw => ⟨hw, hsing w hw⟩
    exact hWperp v (hZW ▸ hv)
  push Not at hsing
  obtain ⟨a, haW, hQa⟩ := hsing
  have h2 : (2 : K) = 0 := by
    have h := hWiso haW a haW
    rw [Φ.polar_self] at h
    exact (mul_eq_zero.mp h).resolve_right hQa
  have ha0 : a ≠ 0 := fun h => hQa (h ▸ Φ.Q_zero)
  have : Finite K := Finite.of_injective (fun c : K => c • a) (smul_left_injective K ha0)
  have hWle : isoSeq Φ.polar ρ R (Module.finrank K V) ≤
      singSeq Φ ρ R (Module.finrank K V) ⊔ K ∙ a := by
    intro w hw
    obtain ⟨c, hc⟩ := Φ.exists_Q_add_smul_eq_zero h2 hQa (hWiso haW w hw)
    have hmem : w + c • a ∈ singSeq Φ ρ R (Module.finrank K V) :=
      ⟨add_mem hw (Submodule.smul_mem _ c haW), hc⟩
    rw [show w = (w + c • a) - c • a by abel]
    exact sub_mem (Submodule.mem_sup_left hmem)
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)))
  have hgZ : ∀ u ∈ Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V)),
      ρ g u ∈ Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V)) := fun u hu =>
    hρ.apply_mem_perp_of_forall (fun z hz => apply_mem_singSeq hQ R _
      (Subgroup.le_normalizer (inv_mem hg)) hz) hu
  have ha : a ∈ Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V)) := fun z hz => hWiso haW z hz.1
  refine ((Φ.sub_mem_or_sub_reflect_mem (hQ g) (isTotallySingular_singSeq Φ ρ R _) hgZ ha hQa
    fun u hu => hWperp u (Φ.polar.perp_antitone hWle hu)).resolve_right
      (hstar g _ (isTotallySingular_singSeq Φ ρ R _) a ha hQa)) v hv

variable (Φ ρ)

@[expose] noncomputable def singFlag (R : Subgroup H) : ℕ → Submodule K V :=
  isoCompletion Φ.polar (singSeq Φ ρ R) (Module.finrank K V)

theorem singFlag_zero (R : Subgroup H) : singFlag Φ ρ R 0 = ⊥ :=
  isoCompletion_zero (singSeq_zero Φ ρ R) _

theorem singFlag_top (R : Subgroup H) :
    singFlag Φ ρ R (2 * Module.finrank K V + 1) = ⊤ :=
  isoCompletion_top (singSeq_zero Φ ρ R) _

theorem singFlag_finrank (R : Subgroup H) :
    singFlag Φ ρ R (Module.finrank K V) = singSeq Φ ρ R (Module.finrank K V) :=
  isoCompletion_of_le le_rfl

theorem singFlag_finrank_succ (R : Subgroup H) :
    singFlag Φ ρ R (Module.finrank K V + 1) =
      Φ.polar.perp (singSeq Φ ρ R (Module.finrank K V)) := by
  have := isoCompletion_perp (F := Φ.polar) (X := singSeq Φ ρ R) (le_refl (Module.finrank K V))
  rwa [show 2 * Module.finrank K V + 1 - Module.finrank K V = Module.finrank K V + 1 by omega]
    at this

variable {Φ ρ}

theorem normalizer_le_flagStab_singFlag (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (R : Subgroup H) :
    Subgroup.normalizer (R : Set H) ≤ flagStab ρ (singFlag Φ ρ R) :=
  le_flagStab_isoCompletion ρ (Φ.isIsometric_of_Q hQ) _ fun _ hh k _ hv =>
    apply_mem_singSeq hQ R k hh hv

theorem le_flagKernel_singFlag [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ) (R : Subgroup H)
    (hR : IsPGroup p R) : R ≤ flagKernel ρ (singFlag Φ ρ R) :=
  le_flagKernel_isoCompletion ρ (Φ.isIsometric_of_Q hQ) (singSeq_zero Φ ρ R)
    (Subgroup.le_normalizer.trans (normalizer_le_flagStab_singFlag hQ R))
    (fun k _ _ hg _ hv => singSeq_triv hQ R k hg hv)
    fun _ hg _ hv => singSeq_middle_triv p hQ hstar R hR hg hv

end Singular

section Middle

variable {Φ : QuadForm K V} {ρ : H →* Module.End K V}

theorem sub_mem_of_fixed_nonsingular [FiniteDimensional K V] (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v)
    (hstar : NoQuotientReflection Φ ρ) {Z : Submodule K V} (hZ : Φ.IsTotallySingular Z) {g : H}
    (hgZ : ∀ z ∈ Z, ρ g z ∈ Z) (hgZ' : ∀ z ∈ Z, ρ g⁻¹ z ∈ Z) {a : V}
    (ha : a ∈ Φ.polar.perp Z) (hQa : Φ.Q a ≠ 0) (hga : ρ g a - a ∈ Z)
    (hW : Φ.polar.perp (Z ⊔ K ∙ a) ≤ Z ⊔ K ∙ a) : ∀ v ∈ Φ.polar.perp Z, ρ g v - v ∈ Z := by
  refine (Φ.sub_mem_or_sub_reflect_mem (hQ g) hZ
    (fun v hv => (Φ.isIsometric_of_Q hQ).apply_mem_perp_of_forall hgZ' hv) ha hQa
    fun v hv => ?_).resolve_right (hstar g Z hZ a ha hQa)
  obtain ⟨z, hz, t, ht, rfl⟩ := Submodule.mem_sup.mp (hW hv)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rw [map_add, map_smul, show ρ g z + c • ρ g a - (z + c • a) = (ρ g z - z) + c • (ρ g a - a) by
    module]
  exact add_mem (sub_mem (hgZ z hz) hz) (Submodule.smul_mem _ c hga)

theorem triv_of_isTotallySingular_maximal [Finite V] (p : ℕ) [Fact p.Prime] [CharP K p]
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ) {Z : Submodule K V}
    (hZ : Φ.IsTotallySingular Z) (hmax : ∀ v ∈ Φ.polar.perp Z, Φ.Q v = 0 → v ∈ Z)
    (S : Subgroup H) (hS : IsPGroup p S) (hstab : ∀ g ∈ S, ∀ v ∈ Z, ρ g v ∈ Z) :
    ∀ g ∈ S, ∀ v ∈ Φ.polar.perp Z, ρ g v - v ∈ Z := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hρ := Φ.isIsometric_of_Q hQ
  have hZiso := hZ.isTotallyIsotropic
  have hperp : ∀ g ∈ S, ∀ v ∈ Φ.polar.perp Z, ρ g v ∈ Φ.polar.perp Z := fun g hg v hv =>
    hρ.apply_mem_perp_of_forall (fun w hw => hstab _ (inv_mem hg) w hw) hv
  by_cases h2 : (2 : K) = 0
  swap
  · exact triv_of_anisotropic Φ.polar ρ p hρ hZiso
      (fun v hv hvv => hmax v hv (Φ.Q_eq_zero_of_polar_self h2 hvv)) S hS hstab
  by_cases hZZ : Φ.polar.perp Z ≤ Z
  · exact fun g hg v hv => hZZ (sub_mem (hperp g hg v hv) hv)
  obtain ⟨a, ha, haZ, hafix⟩ := exists_mem_notMem_forall_sub_mem ρ p S hS
    (lt_of_le_of_ne hZiso fun h => hZZ h.ge) hstab hperp
  have hQa : Φ.Q a ≠ 0 := fun h => haZ (hmax a ha h)
  have ha0 : a ≠ 0 := fun h => hQa (h ▸ Φ.Q_zero)
  have : Finite K := Finite.of_injective (fun c : K => c • a) (smul_left_injective K ha0)
  have hW : Φ.polar.perp (Z ⊔ K ∙ a) ≤ Z ⊔ K ∙ a := by
    intro v hv
    rw [Φ.polar.perp_sup] at hv
    obtain ⟨c, hc⟩ := Φ.exists_Q_add_smul_eq_zero h2 hQa
      (by rw [Φ.polar_symm]; exact Φ.polar.mem_perp_span_singleton.mp hv.2)
    have hmem : v + c • a ∈ Z := hmax _ (add_mem hv.1 (Submodule.smul_mem _ c ha)) hc
    rw [show v = (v + c • a) - c • a by abel]
    exact sub_mem (Submodule.mem_sup_left hmem)
      (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self a)))
  exact fun g hg => sub_mem_of_fixed_nonsingular hQ hstar hZ (hstab g hg) (hstab _ (inv_mem hg))
    ha hQa (hafix g hg) hW

theorem sub_mem_of_singular_fixed [FiniteDimensional K V] (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v)
    {A : Submodule K V} (hA : Φ.IsTotallySingular A)
    (hd : 2 * (Module.finrank K A + 1) = Module.finrank K V) {S : Subgroup H}
    (hstab : ∀ g ∈ S, ∀ v ∈ A, ρ g v ∈ A) {v : V} (hv : v ∈ Φ.polar.perp A) (hvA : v ∉ A)
    (hQv : Φ.Q v = 0) (hvfix : ∀ g ∈ S, ρ g v - v ∈ A) :
    ∀ g ∈ S, ∀ w ∈ Φ.polar.perp A, ρ g w - w ∈ A := by
  have hρ := Φ.isIsometric_of_Q hQ
  have hA₁ : Φ.IsTotallySingular (A ⊔ K ∙ v) := hA.sup_span hv hQv
  have hA₁perp : Φ.polar.perp (A ⊔ K ∙ v) = A ⊔ K ∙ v :=
    Φ.polar.perp_eq_self_of_two_mul_finrank hA₁.isTotallyIsotropic
      (by rw [Submodule.finrank_sup_span_singleton hvA]; omega)
  have hA₁fix : ∀ g ∈ S, ∀ z ∈ A ⊔ K ∙ v, ρ g z - z ∈ A := by
    intro g hg z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    rw [map_add, map_smul, show ρ g a + c • ρ g v - (a + c • v) = (ρ g a - a) + c • (ρ g v - v) by
      module]
    exact add_mem (sub_mem (hstab g hg a ha) ha) (Submodule.smul_mem _ c (hvfix g hg))
  intro g hg w hw
  have hmem : ρ g w - w ∈ A ⊔ K ∙ v := by
    rw [← hA₁perp]
    intro z hz
    have h1 := hρ g (ρ g⁻¹ z) w
    rw [rep_apply_inv_apply] at h1
    rw [Φ.polar.β_sub_right, h1, ← Φ.polar.β_sub_left]
    exact hw _ (hA₁fix g⁻¹ (inv_mem hg) z hz)
  by_cases hvw : Φ.polar.β v w = 0
  · have hwA₁ : w ∈ A ⊔ K ∙ v := by
      rw [← hA₁perp, Φ.polar.perp_sup]
      exact ⟨hw, Φ.polar.mem_perp_span_singleton.mpr hvw⟩
    exact hA₁fix g hg w hwA₁
  ·
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have hnorm := hQ g w
    have hwa : Φ.polar.β w a = 0 := by rw [Φ.polar_symm]; exact hw a ha
    rw [show ρ g w = w + (a + c • v) by rw [hab]; abel, Φ.Q_add,
      hA₁ _ (add_mem (Submodule.mem_sup_left ha)
        (Submodule.mem_sup_right (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self v)))),
      Φ.polar.add_right, Φ.polar.smul_right, hwa, Φ.polar_symm w v] at hnorm
    have hc : c = 0 := by
      have : c * Φ.polar.β v w = 0 := by linear_combination hnorm
      exact (mul_eq_zero.mp this).resolve_right hvw
    rw [← hab, hc, zero_smul, add_zero]
    exact ha

theorem triv_of_two_mul_finrank_succ_of_noQuotientReflection [Finite V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ)
    {A : Submodule K V} (hA : Φ.IsTotallySingular A)
    (hd : 2 * (Module.finrank K A + 1) = Module.finrank K V) (S : Subgroup H) (hS : IsPGroup p S)
    (hstab : ∀ g ∈ S, ∀ v ∈ A, ρ g v ∈ A) :
    ∀ g ∈ S, ∀ v ∈ Φ.polar.perp A, ρ g v - v ∈ A := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hρ := Φ.isIsometric_of_Q hQ
  have hAiso := hA.isTotallyIsotropic
  by_cases h2 : (2 : K) = 0
  swap
  · exact triv_of_two_mul_finrank_succ Φ h2 p hρ hAiso hd S hS hstab
  have hlt : A < Φ.polar.perp A := lt_of_le_of_ne hAiso fun h => by
    have := Φ.polar.finrank_perp A
    rw [← h] at this
    omega
  obtain ⟨a, ha, haA, hafix⟩ := exists_mem_notMem_forall_sub_mem ρ p S hS hlt hstab
    fun g hg v hv => hρ.apply_mem_perp_of_forall (fun w hw => hstab _ (inv_mem hg) w hw) hv
  by_cases hQa : Φ.Q a = 0
  · exact sub_mem_of_singular_fixed hQ hA hd hstab ha haA hQa hafix
  have hW : Φ.polar.perp (A ⊔ K ∙ a) ≤ A ⊔ K ∙ a :=
    (Φ.polar.perp_eq_self_of_two_mul_finrank
      (hAiso.sup_span ha (by rw [Φ.polar_self, h2, zero_mul]))
      (by rw [Submodule.finrank_sup_span_singleton haA]; omega)).le
  exact fun g hg => sub_mem_of_fixed_nonsingular hQ hstar hA (hstab g hg) (hstab _ (inv_mem hg))
    ha hQa (hafix g hg) hW

theorem apply_mem_of_noQuotientReflection [FiniteDimensional K V]
    (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v) (hstar : NoQuotientReflection Φ ρ) {A L : Submodule K V}
    (hL : Φ.IsTotallySingular L) (hLd : 2 * Module.finrank K L = Module.finrank K V)
    (hAL : A ≤ L) (hrank : Module.finrank K L = Module.finrank K A + 1) {h : H}
    (hhA : ∀ v ∈ A, ρ h v ∈ A) (hhA' : ∀ v ∈ A, ρ h⁻¹ v ∈ A) : ∀ v ∈ L, ρ h v ∈ L := by
  have hρ := Φ.isIsometric_of_Q hQ
  have hLiso := hL.isTotallyIsotropic
  have hA : Φ.IsTotallySingular A := hL.mono hAL
  have hLperp : Φ.polar.perp L = L := Φ.polar.perp_eq_self_of_two_mul_finrank hLiso hLd
  have hLA : L ≤ Φ.polar.perp A := hLiso.trans (Φ.polar.perp_antitone hAL)
  have hgA : ∀ v ∈ Φ.polar.perp A, ρ h v ∈ Φ.polar.perp A := fun v hv =>
    hρ.apply_mem_perp_of_forall hhA' hv
  obtain ⟨e, heL, heA⟩ : ∃ e ∈ L, e ∉ A := IsConcreteLE.exists_of_lt
    (lt_of_le_of_ne hAL fun h => by rw [h] at hrank; omega)
  have hLe : L = A ⊔ K ∙ e := (Submodule.eq_of_le_of_finrank_eq
    (sup_le hAL ((Submodule.span_singleton_le_iff_mem _ _).mpr heL))
    (by rw [Submodule.finrank_sup_span_singleton heA, hrank])).symm
  by_contra! hcon
  obtain ⟨u, huL, hguL⟩ := hcon
  have hfA : ρ h u ∈ Φ.polar.perp A := hgA u (hLA huL)
  have hef : Φ.polar.β e (ρ h u) ≠ 0 := by
    intro hef
    apply hguL
    rw [← hLperp, hLe, Φ.polar.perp_sup]
    exact ⟨hfA, Φ.polar.mem_perp_span_singleton.mpr hef⟩
  obtain ⟨f, hfdef⟩ : ∃ f, f = (Φ.polar.β e (ρ h u))⁻¹ • ρ h u := ⟨_, rfl⟩
  have hef' : Φ.polar.β e f = 1 := by rw [hfdef, Φ.polar.smul_right, inv_mul_cancel₀ hef]
  have hfe : Φ.polar.β f e = 1 := by rw [Φ.polar_symm, hef']
  have hfA' : f ∈ Φ.polar.perp A := by
    rw [hfdef]
    exact Submodule.smul_mem _ _ hfA
  have hQf : Φ.Q f = 0 := by rw [hfdef, Φ.Q_smul, hQ, hL u huL, mul_zero]
  have hff : Φ.polar.β f f = 0 := by rw [Φ.polar_self, hQf, mul_zero]
  have hQe : Φ.Q e = 0 := hL e heL
  have hee : Φ.polar.β e e = 0 := by rw [Φ.polar_self, hQe, mul_zero]
  have hfL : f ∉ L := fun hf => one_ne_zero (hef'.symm.trans (hLiso hf e heL))
  have hfnA : f ∉ A := fun hf => hfL (hAL hf)
  have hM : Φ.IsTotallySingular (A ⊔ K ∙ f) := hA.sup_span hfA' hQf
  have hMperp : Φ.polar.perp (A ⊔ K ∙ f) = A ⊔ K ∙ f :=
    Φ.polar.perp_eq_self_of_two_mul_finrank hM.isTotallyIsotropic
      (by rw [Submodule.finrank_sup_span_singleton hfnA, ← hrank, hLd])
  have hgLM : ∀ v ∈ L, ρ h v ∈ A ⊔ K ∙ f := by
    intro v hv
    rw [← hMperp, Φ.polar.perp_sup]
    refine ⟨hgA v (hLA hv), Φ.polar.mem_perp_span_singleton.mpr ?_⟩
    rw [hfdef, Φ.polar_smul_left, hρ, hLiso hv u huL, mul_zero]
  obtain ⟨a₀, ha₀, t, ht, hge⟩ := Submodule.mem_sup.mp (hgLM e heL)
  obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hl : l ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hge
    have := hhA' _ (hge ▸ ha₀)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
    exact heA this
  have hAperp : Φ.polar.perp A ≤ L ⊔ K ∙ f := by
    refine (Submodule.eq_of_le_of_finrank_eq
      (sup_le hLA ((Submodule.span_singleton_le_iff_mem _ _).mpr hfA')) ?_).ge
    have := Φ.polar.finrank_perp A
    rw [Submodule.finrank_sup_span_singleton hfL]
    omega
  obtain ⟨l₁, hl₁, t₁, ht₁, hgf⟩ := Submodule.mem_sup.mp (hAperp (hgA f hfA'))
  obtain ⟨y, rfl⟩ := Submodule.mem_span_singleton.mp ht₁
  rw [hLe] at hl₁
  obtain ⟨a₁, ha₁, t₂, ht₂, rfl⟩ := Submodule.mem_sup.mp hl₁
  obtain ⟨x, rfl⟩ := Submodule.mem_span_singleton.mp ht₂
  have hQa₁ : Φ.Q a₁ = 0 := hA a₁ ha₁
  have ha₁e : Φ.polar.β a₁ e = 0 := hLA heL a₁ ha₁
  have ha₁f : Φ.polar.β a₁ f = 0 := hfA' a₁ ha₁
  have hfa₁ : Φ.polar.β f a₁ = 0 := by rw [Φ.polar_symm, ha₁f]
  have ha₀a₁ : Φ.polar.β a₀ a₁ = 0 := hA.isTotallyIsotropic ha₁ a₀ ha₀
  have ha₀e : Φ.polar.β a₀ e = 0 := hLA heL a₀ ha₀
  have ha₀f : Φ.polar.β a₀ f = 0 := hfA' a₀ ha₀
  have hxy : x * y = 0 := by
    have := hQ h f
    rw [← hgf, hQf] at this
    simp only [Φ.Q_add, Φ.Q_smul, Φ.polar.add_left, Φ.polar.smul_right, Φ.polar_smul_left, hQa₁,
      hQe, hQf, ha₁e, ha₁f, hef'] at this
    linear_combination this
  have hlx : l * x = 1 := by
    have := hρ h e f
    rw [← hge, ← hgf, hef'] at this
    simp only [Φ.polar.add_left, Φ.polar.add_right, Φ.polar.smul_right, Φ.polar_smul_left,
      ha₀a₁, ha₀e, ha₀f, hfa₁, hfe, hff] at this
    linear_combination this
  have hx : x = l⁻¹ := by
    field_simp
    linear_combination hlx
  have hy : y = 0 := (mul_eq_zero.mp hxy).resolve_left (by rw [hx]; exact inv_ne_zero hl)
  have hQa : Φ.Q (e - l • f) = -l := by
    rw [sub_eq_add_neg, ← neg_smul, Φ.Q_add, Φ.Q_smul, hQe, hQf, Φ.polar.smul_right, hef']
    ring
  have hQa0 : Φ.Q (e - l • f) ≠ 0 := by rw [hQa]; exact neg_ne_zero.mpr hl
  have haA : e - l • f ∈ Φ.polar.perp A := sub_mem (hLA heL) (Submodule.smul_mem _ l hfA')
  refine hstar h A hA _ haA hQa0 fun v hv => ?_
  rw [Φ.polar_symm v]
  change ρ h v - Φ.reflect (e - l • f) v ∈ A
  have hle : L ⊔ K ∙ f ≤ A.comap (ρ h - Φ.reflect (e - l • f)) := by
    rw [hLe]
    refine sup_le (sup_le (fun z hz => ?_) ?_) ?_
    · rw [Submodule.mem_comap, LinearMap.sub_apply,
        Φ.reflect_apply_of_polar_eq_zero (by rw [Φ.polar_symm]; exact haA z hz)]
      exact sub_mem (hhA z hz) hz
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, LinearMap.sub_apply, ← hge,
        Φ.reflect_apply, hQa, Φ.polar.β_sub_left, Φ.polar_smul_left, hee, hfe,
        show (0 - l * 1) / -l = 1 by rw [zero_sub, mul_one, neg_div_neg_eq, div_self hl],
        one_smul, sub_sub_cancel, add_sub_cancel_right]
      exact ha₀
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, LinearMap.sub_apply, ← hgf,
        Φ.reflect_apply, hQa, Φ.polar.β_sub_left, Φ.polar_smul_left, hef', hff, hx, hy,
        show (1 - l * 0) / -l = -l⁻¹ by rw [mul_zero, sub_zero, div_neg, one_div],
        show a₁ + l⁻¹ • e + (0 : K) • f - (f - (-l⁻¹) • (e - l • f)) = a₁ + (l⁻¹ * l - 1) • f by
          module, inv_mul_cancel₀ hl, sub_self, zero_smul, add_zero]
      exact ha₁
  exact hle (hAperp hv)

end Middle

section Eichler

variable {Φ : QuadForm K V} {ρ : H →* Module.End K V}

theorem exists_apply_notMem_of_isTotallySingular [FiniteDimensional K V]
    (hd : 3 ≤ Module.finrank K V)
    (heich : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 → ∃ h : H, ∀ v, ρ h v = Φ.eichler x y v)
    {W : Submodule K V} (hW : W ≠ ⊥) (hWs : Φ.IsTotallySingular W) :
    ∃ h : H, ∃ w ∈ W, ρ h w ∉ W := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨u, hu⟩ : ∃ u, Φ.polar.β w u = 1 := by
    by_contra! h
    apply hw0
    refine Φ.polar.nondeg w fun v => ?_
    by_contra hv
    apply h ((Φ.polar.β w v)⁻¹ • v)
    rw [Φ.polar.smul_right, inv_mul_cancel₀ hv]
  have hww : Φ.polar.β w w = 0 := hWs.isTotallyIsotropic hwW w hwW
  have hQw : Φ.Q w = 0 := hWs w hwW
  have huw : Φ.polar.β u w = 1 := by rw [Φ.polar_symm, hu]
  have hQf : Φ.Q (u + (-Φ.Q u) • w) = 0 := by
    rw [Φ.Q_add, Φ.Q_smul, hQw, Φ.polar.smul_right, huw]
    ring
  have hfw : Φ.polar.β (u + (-Φ.Q u) • w) w = 1 := by
    rw [Φ.polar.add_left, Φ.polar_smul_left, hww, huw]
    ring
  obtain ⟨y, hfy, hy⟩ := Φ.exists_polar_eq_zero_Q_ne_zero hd (u + (-Φ.Q u) • w)
  obtain ⟨h, hh⟩ := heich _ y hQf hfy
  refine ⟨h, w, hwW, fun hmem => hy ?_⟩
  have h0 : Φ.polar.β (ρ h w - w) w = 0 := hWs.isTotallyIsotropic hwW _ (sub_mem hmem hwW)
  have h3 : ρ h w - w = y - (Φ.Q y + Φ.polar.β y w) • (u + (-Φ.Q u) • w) := by
    rw [hh, Φ.eichler_apply, hfw, one_smul]
    module
  rw [h3, Φ.polar.β_sub_left, Φ.polar_smul_left, hfw] at h0
  linear_combination -h0

theorem mem_of_forall_mem_flagKernel_sub_mem [FiniteDimensional K V]
    (heich : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 → ∃ h : H, ∀ v, ρ h v = Φ.eichler x y v)
    {X : ℕ → Submodule K V} (hXmono : Monotone X) (hXs : ∀ k, Φ.IsTotallySingular (X k)) {m : ℕ}
    (hXrank : ∀ k ≤ m, Module.finrank K (X k) = k) {k : ℕ} (hk : k < m)
    (hne : Φ.polar.perp (X (k + 1)) ≠ X (k + 1)) {v : V} (hv : v ∈ Φ.polar.perp (X k))
    (hfix : ∀ g ∈ flagKernel ρ (isoCompletion Φ.polar X m), ρ g v - v ∈ X k) :
    v ∈ X (k + 1) := by
  have hXiso : ∀ k, Φ.polar.IsTotallyIsotropic (X k) := fun k => (hXs k).isTotallyIsotropic
  by_contra hvX
  have hlt : X k < X (k + 1) := by
    refine lt_of_le_of_ne (hXmono (Nat.le_succ k)) fun h => ?_
    have := hXrank (k + 1) (by omega)
    rw [← h, hXrank k (by omega)] at this
    omega
  obtain ⟨x, hx, hxk⟩ := IsConcreteLE.exists_of_lt hlt
  have hQx : Φ.Q x = 0 := hXs (k + 1) x hx
  have hXk1 : X (k + 1) = X k ⊔ K ∙ x := by
    refine (Submodule.eq_of_le_of_finrank_eq
      (sup_le (hXmono (Nat.le_succ k)) ((Submodule.span_singleton_le_iff_mem _ _).mpr hx))
      ?_).symm
    rw [Submodule.finrank_sup_span_singleton hxk, hXrank k (by omega), hXrank (k + 1) (by omega)]
  have hU : ∀ y ∈ Φ.polar.perp (X (k + 1)), ∃ h ∈ flagKernel ρ (isoCompletion Φ.polar X m),
      ∀ v, ρ h v = Φ.eichler x y v := by
    intro y hy
    obtain ⟨h, hh⟩ := heich x y hQx (hy x hx)
    refine ⟨h, mem_flagKernel_isoCompletion ρ hXmono hXiso hk hx hy
      (a := y - Φ.Q y • x) (sub_mem hy (Submodule.smul_mem _ _ (hXiso (k + 1) hx))) (-1)
      fun v => ?_, hh⟩
    rw [hh, Φ.eichler_apply, neg_one_mul, neg_smul, ← sub_eq_add_neg]
  by_cases hxv : Φ.polar.β x v = 0
  ·
    have hvperp : v ∈ Φ.polar.perp (X (k + 1)) := by
      rw [hXk1, Φ.polar.perp_sup]
      exact ⟨hv, Φ.polar.mem_perp_span_singleton.mpr hxv⟩
    obtain ⟨y, hy, hyv⟩ : ∃ y ∈ Φ.polar.perp (X (k + 1)), Φ.polar.β y v ≠ 0 := by
      by_contra! h
      apply hvX
      have hpp : v ∈ Φ.polar.perp (Φ.polar.perp (X (k + 1))) := fun y hy => h y hy
      rwa [Φ.polar.perp_perp] at hpp
    obtain ⟨h, hhU, hh⟩ := hU y hy
    have := hfix h hhU
    rw [hh, Φ.eichler_apply, hxv, zero_smul, add_zero, sub_sub_cancel_left, ← neg_smul,
      Submodule.smul_mem_iff _ (neg_ne_zero.mpr hyv)] at this
    exact hxk this
  ·
    obtain ⟨y, hy, hyX⟩ := IsConcreteLE.exists_of_lt
      (lt_of_le_of_ne (hXiso (k + 1)) (Ne.symm hne))
    obtain ⟨h, hhU, hh⟩ := hU y hy
    have hmem : Φ.polar.β x v • y ∈ X (k + 1) := by
      have h1 := hfix h hhU
      have h3 : Φ.polar.β x v • y = (ρ h v - v) + (Φ.polar.β x v * Φ.Q y +
          Φ.polar.β y v) • x := by
        rw [hh, Φ.eichler_apply]
        module
      rw [h3]
      exact add_mem (hXmono (Nat.le_succ k) h1) (Submodule.smul_mem _ _ hx)
    exact hyX ((Submodule.smul_mem_iff _ hxv).mp hmem)

end Eichler

variable (Φ : QuadForm K V) {ρ : H →* Module.End K V}

theorem holds_of_quadForm_singular [Finite H] [Finite V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (hd : 3 ≤ Module.finrank K V) (hQ : ∀ h v, Φ.Q (ρ h v) = Φ.Q v)
    (hinj : Function.Injective ρ)
    (heich : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 → ∃ h : H, ∀ v, ρ h v = Φ.eichler x y v)
    (hstar : NoQuotientReflection Φ ρ) : Holds H p := by
  have : FiniteDimensional K V := Module.Finite.of_finite
  have hρ := Φ.isIsometric_of_Q hQ
  refine holds_of_flags ρ p hinj (singFlag Φ ρ) (fun R _ _ => singFlag_zero Φ ρ R)
    (fun R _ _ => ⟨_, singFlag_top Φ ρ R⟩) (fun R _ _ => normalizer_le_flagStab_singFlag hQ R)
    (fun R _ hR => le_flagKernel_singFlag p hQ hstar R hR) (fun R hR hRp htop => ?_)
    (fun R _ _ => ?_)
  ·
    by_cases h0 : singSeq Φ ρ R (Module.finrank K V) = ⊥
    · refine hR ((Subgroup.eq_bot_iff_forall R).mpr fun g hg => hinj ?_)
      ext v
      have := (le_flagKernel_singFlag p hQ hstar R hRp hg).2 (Module.finrank K V) v
        (by rw [singFlag_finrank_succ, h0, Φ.polar.perp_bot]; trivial)
      rw [singFlag_finrank, h0, Submodule.mem_bot, sub_eq_zero] at this
      rw [this, map_one, Module.End.one_apply]
    · obtain ⟨h, w, hw, hhw⟩ := exists_apply_notMem_of_isTotallySingular hd heich h0
        (isTotallySingular_singSeq Φ ρ R _)
      apply hhw
      have := flagStab_apply_mem ρ (htop ▸ Subgroup.mem_top h) (k := Module.finrank K V)
        (v := w) (by rw [singFlag_finrank]; exact hw)
      rwa [singFlag_finrank] at this
  ·
    obtain ⟨X, m, hX0, hXmono, hXs, hXrank, hXstable, hrefine, hmax⟩ :=
      exists_chain_refining_of_maximal (P := Φ.IsTotallySingular) (fun hM h => hM.mono h)
        (singSeq Φ ρ R) (singSeq_zero Φ ρ R) (singSeq_mono Φ ρ R) (isTotallySingular_singSeq Φ ρ R)
    have hXiso : ∀ k, Φ.polar.IsTotallyIsotropic (X k) := fun k => (hXs k).isTotallyIsotropic
    have hmax' : ∀ v ∈ Φ.polar.perp (X m), Φ.Q v = 0 → v ∈ X m := fun v hv hQv =>
      hmax _ le_sup_left ((hXs m).sup_span hv hQv)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    have hU'p : IsPGroup p (flagKernel ρ (isoCompletion Φ.polar X m)) :=
      isPGroup_flagKernel ρ p hinj (isoCompletion_zero hX0 m) (isoCompletion_top hX0 m)
    suffices hS : ∃ S : Sylow p H, Subgroup.normalizer ((S : Subgroup H) : Set H) ≤ flagStab ρ X by
      obtain ⟨S, hS⟩ := hS
      refine ⟨S, le_flagStab_isoCompletion ρ hρ _ fun h hh j v hv => ?_⟩
      obtain ⟨k, hk⟩ := hrefine j
      rw [hk] at hv ⊢
      exact flagStab_apply_mem ρ (hS hh) hv
    by_cases hL : Φ.polar.perp (X m) = X m
    ·
      have hm : Module.finrank K (X m) = m := hXrank m le_rfl
      have hdm : 2 * m = Module.finrank K V := by
        have := Φ.polar.finrank_perp (X m)
        rw [hL, hm] at this
        omega
      refine exists_sylow_normalizer_le_flagStab_of_isotropicChain Φ.polar ρ p hρ X m (m - 1)
        (Nat.sub_le m 1) hX0 hXmono hXiso hXrank hXstable _ hU'p
        (fun k hk v hv hfix => mem_of_forall_mem_flagKernel_sub_mem heich hXmono hXs hXrank
          (by omega : k < m) (fun h => ?_) hv hfix) (fun S hS hSstab g hg v hv => ?_)
        (fun S hseq k hk1 hk2 => ?_)
      · have := Φ.polar.finrank_perp (X (k + 1))
        rw [h, hXrank (k + 1) (by omega)] at this
        omega
      · exact triv_of_two_mul_finrank_succ_of_noQuotientReflection p hQ hstar (hXs (m - 1))
          (by rw [hXrank (m - 1) (by omega)]; omega) S hS (fun g hg w hw => (hSstab hg 0 w hw).1)
          g hg v hv
      ·
        rw [show k = m by omega]
        have hA : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ v ∈ X (m - 1),
            ρ h v ∈ X (m - 1) := fun h hh v hv => by
          have := apply_mem_isoSeq Φ.polar ρ hρ S (m - 1) hh (v := v)
          rw [hseq, min_self] at this
          exact this hv
        have key : ∀ h ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ v ∈ X m,
            ρ h v ∈ X m := fun h hh =>
          apply_mem_of_noQuotientReflection hQ hstar (hXs m) (by rw [hm]; omega)
            (hXmono (Nat.sub_le m 1)) (by rw [hm, hXrank (m - 1) (by omega)]; omega) (hA h hh)
            (hA _ (inv_mem hh))
        intro h hh j v hv
        exact ⟨key h hh v hv, key h⁻¹ (inv_mem hh) v hv⟩
    ·
      refine exists_sylow_normalizer_le_flagStab_of_isotropicChain Φ.polar ρ p hρ X m m le_rfl
        hX0 hXmono hXiso hXrank hXstable _ hU'p
        (fun k hk v hv hfix => mem_of_forall_mem_flagKernel_sub_mem heich hXmono hXs hXrank hk
          (fun h => ?_) hv hfix)
        (fun S hS hSstab g hg v hv => ?_) (fun S _ k hk1 hk2 => absurd hk2 (by omega))
      · apply hL
        have h1 := Φ.polar.finrank_perp (X (k + 1))
        have h3 := Φ.polar.finrank_perp (X m)
        have h4 := Submodule.finrank_mono (hXiso m)
        rw [h, hXrank (k + 1) hk] at h1
        rw [hXrank m le_rfl] at h3 h4
        rw [show m = k + 1 by omega, h]
      · exact triv_of_isTotallySingular_maximal p hQ hstar (hXs m) hmax' S hS
          (fun g hg w hw => (hSstab hg 0 w hw).1) g hg v hv

end CFSG.LieType.BorelTits
