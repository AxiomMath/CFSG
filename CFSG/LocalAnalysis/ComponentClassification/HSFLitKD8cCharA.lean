module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cLift
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCharM

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

@[expose] def cen (H : Subgroup X) : Set X := {g | g ∈ H ∧ ∀ h ∈ H, g * h = h * g}

@[expose] def zz (H : Subgroup X) : Set X :=
  {g | g ∈ H ∧ g * g = 1 ∧ ∀ h ∈ H, g * h * g⁻¹ * h⁻¹ ∈ cen H}

omit [Finite X] in
theorem conj_cen {H : Subgroup X} {y : X} (hy : y ∈ normalizer (H : Set X)) {g : X}
    (hg : g ∈ cen H) : y * g * y⁻¹ ∈ cen H := by
  refine ⟨(mem_normalizer_iff.mp hy g).mp hg.1, fun h hh => ?_⟩
  have hh' : y⁻¹ * h * y ∈ H := by
    have := (mem_normalizer_iff.mp hy (y⁻¹ * h * y)).mpr (by simpa [mul_assoc] using hh)
    exact this
  have := hg.2 _ hh'
  calc y * g * y⁻¹ * h = y * (g * (y⁻¹ * h * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * h * y) * g) * y⁻¹ := by rw [this]
    _ = h * (y * g * y⁻¹) := by group

omit [Finite X] in
theorem conj_zz {H : Subgroup X} {y : X} (hy : y ∈ normalizer (H : Set X)) {g : X}
    (hg : g ∈ zz H) : y * g * y⁻¹ ∈ zz H := by
  refine ⟨(mem_normalizer_iff.mp hy g).mp hg.1, ?_, fun h hh => ?_⟩
  · rw [show y * g * y⁻¹ * (y * g * y⁻¹) = y * (g * g) * y⁻¹ by group, hg.2.1]
    group
  · have hh' : y⁻¹ * h * y ∈ H := by
      have := (mem_normalizer_iff.mp hy (y⁻¹ * h * y)).mpr (by simpa [mul_assoc] using hh)
      exact this
    have := conj_cen hy (hg.2.2 _ hh')
    convert this using 1
    group

theorem card_le_mul_of_cosets {A R : Subgroup X} {n : ℕ} (c : Fin n → X)
    (h : ∀ a ∈ A, ∃ i, (c i)⁻¹ * a ∈ R) : Nat.card A ≤ n * Nat.card (A ⊓ R : Subgroup X) := by
  classical
  choose f hf using fun a : A => h a.1 a.2
  have hne : Nonempty A := ⟨1⟩
  let base : Fin n → A := Function.invFun f
  have hbase : ∀ a : A, f (base (f a)) = f a := fun a => Function.invFun_eq ⟨a, rfl⟩
  have hmem : ∀ a : A, (base (f a) : X)⁻¹ * a ∈ (A ⊓ R : Subgroup X) := fun a => by
    have hA : (base (f a) : X)⁻¹ * (a : X) ∈ A := A.mul_mem (A.inv_mem (base (f a)).2) a.2
    refine Subgroup.mem_inf.mpr ⟨hA, ?_⟩
    have h1 := hf (base (f a))
    rw [hbase a] at h1
    have := mul_mem (inv_mem h1) (hf a)
    simpa [mul_assoc] using this
  let F : A → Fin n × (A ⊓ R : Subgroup X) := fun a => (f a, ⟨_, hmem a⟩)
  have hF : Function.Injective F := by
    intro a a' haa
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at haa
    obtain ⟨h1, h2⟩ := haa
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this

namespace Conf

variable (K : Conf S T₁)

theorem mem_Zx_iff (x : MC) : K.ι x ∈ K.Zx ↔ inZ x = true := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← K.ι_injective hyx]
    exact hy
  · exact fun hx => ⟨x, hx, rfl⟩

theorem Zx_eq : K.Zx = K.Ex 0 ⊓ K.Ex 3 := by
  refine eq_of_le_of_card_ge (le_inf (K.Zx_le_Ex 0) (K.Zx_le_Ex 3)) ?_
  rw [K.card_inf_Ex, K.card_Zx]
  decide

theorem comm_R1' {a b : X} (ha : a ∈ K.R1) (hb : b ∈ K.R1) : a * b * a⁻¹ * b⁻¹ ∈ K.Zx := by
  obtain ⟨a', ha', rfl⟩ := K.mem_R1.mp ha
  obtain ⟨b', hb', rfl⟩ := K.mem_R1.mp hb
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, K.mem_Zx_iff]
  exact comm_R1 ha' hb'

namespace T2

variable {K} (T : K.T2)

theorem R1_le_P : K.R1 ≤ T.P := K.R1_le_S1.trans T.S1_le

theorem y_mem : S.y ∈ T.P := by
  have h := K.ι_mem_S1 MC.y
  rw [K.ι_y] at h
  exact T.S1_le h

theorem k_mem : S.k ∈ T.P := by
  have h := K.ι_mem_S1 MC.k
  rw [K.ι_k] at h
  exact T.S1_le h

theorem pN_03 {g : X} (hg : g ∈ T.P) :
    (K.pN (T.le_NR hg) 0 = 0 ∧ K.pN (T.le_NR hg) 3 = 3) ∨
      (K.pN (T.le_NR hg) 0 = 3 ∧ K.pN (T.le_NR hg) 3 = 0) := by
  rcases K.pN_cases T.isPGroup (T.S1_le K.w₂_mem_S1) T.le_NR hg with h0 | ha | hsa
  · exact Or.inl ⟨h0, K.pN_S1_3 (T.mem_S1_of hg h0) _⟩
  · exact Or.inr ⟨ha 0, ha 3⟩
  · exact Or.inr ⟨hsa 0, hsa 3⟩

theorem conj_Zx {g : X} (hg : g ∈ T.P) {z : X} (hz : z ∈ K.Zx) : g * z * g⁻¹ ∈ K.Zx := by
  rw [K.Zx_eq] at hz ⊢
  have h0 := K.conj_mem_pN (T.le_NR hg) hz.1
  have h3 := K.conj_mem_pN (T.le_NR hg) hz.2
  rcases T.pN_03 hg with ⟨e0, e3⟩ | ⟨e0, e3⟩
  · rw [e0] at h0
    rw [e3] at h3
    exact ⟨h0, h3⟩
  · rw [e0] at h0
    rw [e3] at h3
    exact ⟨h3, h0⟩

theorem comm_coset_iff {b c a : X} (hb : b ∈ K.R1) (hc : c ∈ T.P) (hca : c⁻¹ * a ∈ K.R1) :
    b * a * b⁻¹ * a⁻¹ ∈ K.Zx ↔ b * c * b⁻¹ * c⁻¹ ∈ K.Zx := by
  have hcz := T.conj_Zx hc (K.comm_R1' hb hca)
  have key : b * a * b⁻¹ * a⁻¹ =
      b * c * b⁻¹ * c⁻¹ * (c * (b * (c⁻¹ * a) * b⁻¹ * (c⁻¹ * a)⁻¹) * c⁻¹) := by group
  rw [key]
  constructor
  · intro h
    have := mul_mem h (inv_mem hcz)
    simpa [mul_assoc] using this
  · exact fun h => mul_mem h hcz

theorem comm_y_not_mem {g : X} (hg : g ∈ T.P) (hgS : g ∉ K.D₁.S₁) :
    g * S.y * g⁻¹ * S.y⁻¹ ∉ K.Zx := by
  intro hz
  have hy0 : S.y ∈ K.Ex 0 := by rw [← K.ι_y]; exact K.ι_mem_Ex (by decide +kernel)
  have h3 : g * S.y * g⁻¹ ∈ K.Ex 3 := by
    have := K.conj_mem_pN (T.le_NR hg) hy0
    rcases T.pN_03 hg with ⟨e0, -⟩ | ⟨e0, -⟩
    · exact absurd (T.mem_S1_of hg e0) hgS
    · rwa [e0] at this
  have h0 : g * S.y * g⁻¹ ∈ K.Ex 0 := by
    have := mul_mem (K.Zx_le_Ex 0 hz) hy0
    simpa using this
  have hZ : g * S.y * g⁻¹ ∈ K.Zx := by rw [K.Zx_eq]; exact ⟨h0, h3⟩
  have := T.conj_Zx (inv_mem hg) hZ
  rw [show g⁻¹ * (g * S.y * g⁻¹) * g⁻¹⁻¹ = S.y by group, ← K.ι_y, K.mem_Zx_iff] at this
  exact absurd this (by rw [inZ_y]; decide)

theorem cen_sub {g : X} (hg : g ∈ cen T.P) : g = 1 ∨ g = S.k := by
  by_cases hgS : g ∈ K.D₁.S₁
  · rw [← K.range_ι] at hgS
    obtain ⟨a, rfl⟩ := hgS
    have hc : ∀ x ∈ MC.gens, a * x = x * a := fun x _ =>
      K.ι_injective (by rw [map_mul, map_mul]; exact hg.2 _ (T.S1_le (K.ι_mem_S1 x)))
    rcases center_MC a hc with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr K.ι_k
  · exfalso
    apply T.comm_y_not_mem hg.1 hgS
    rw [hg.2 _ T.y_mem]
    simp

namespace Lift

variable {T} (W : T.Lift)

include W in
theorem k_mem_cen : S.k ∈ cen T.P := by
  refine ⟨T.k_mem, fun h hh => ?_⟩
  rcases W.cases h hh with hS | hS
  · rw [← K.range_ι] at hS
    obtain ⟨a, rfl⟩ := hS
    rw [← K.ι_k, ← map_mul, ← map_mul, k_comm]
  · rw [← K.range_ι] at hS
    obtain ⟨a, ha⟩ := hS
    have hQk : W.Q * S.k = S.k * W.Q := by
      have := W.hQ MC.k
      rw [phiR_Zl W.j MC.k (by simp [Zl]), K.ι_k] at this
      calc W.Q * S.k = W.Q * S.k * W.Q⁻¹ * W.Q := by group
        _ = S.k * W.Q := by rw [this]
    have hh' : h = K.ι a * W.Q := by rw [ha]; group
    have hka : S.k * K.ι a = K.ι a * S.k := by rw [← K.ι_k, ← map_mul, ← map_mul, k_comm]
    calc S.k * h = S.k * K.ι a * W.Q := by rw [hh', mul_assoc]
      _ = K.ι a * S.k * W.Q := by rw [hka]
      _ = K.ι a * (W.Q * S.k) := by rw [mul_assoc, ← hQk]
      _ = h * S.k := by rw [hh', mul_assoc]

include W in
theorem mem_cen_of {g : X} (hg : g = 1 ∨ g = S.k) : g ∈ cen T.P := by
  rcases hg with rfl | rfl
  · exact ⟨one_mem _, fun h _ => by group⟩
  · exact W.k_mem_cen

include W in
theorem zz_eq : zz T.P = (K.Zx : Set X) := by
  ext g
  constructor
  · rintro ⟨hgP, hg2, hgc⟩
    by_cases hgS : g ∈ K.D₁.S₁
    · rw [← K.range_ι] at hgS
      obtain ⟨a, rfl⟩ := hgS
      refine (K.mem_Zx_iff a).mpr (zz_MC a (K.ι_injective (by rw [map_mul, hg2, map_one]))
        fun x _ => ?_)
      rcases T.cen_sub (hgc _ (T.S1_le (K.ι_mem_S1 x))) with h | h
      · left
        exact K.ι_injective (by simpa [map_mul, map_inv] using h)
      · right
        exact K.ι_injective (by simpa [map_mul, map_inv, K.ι_k] using h)
    · exfalso
      apply T.comm_y_not_mem hgP hgS
      rcases T.cen_sub (hgc _ T.y_mem) with h | h
      · rw [h]; exact one_mem _
      · rw [h, ← K.ι_k, K.mem_Zx_iff]; decide +kernel
  · intro hg
    obtain ⟨z, hz, rfl⟩ := hg
    have hzl := inZ_zl hz
    refine ⟨T.S1_le (K.ι_mem_S1 z), by rw [← map_mul, Zl_sq z hzl, map_one], fun h hh => ?_⟩
    refine W.mem_cen_of ?_
    rcases W.cases h hh with hS | hS
    · rw [← K.range_ι] at hS
      obtain ⟨a, rfl⟩ := hS
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← K.ι_k]
      rcases comm_Zl z hzl a with e | e
      · left; rw [e, map_one]
      · right; rw [e]
    · rw [← K.range_ι] at hS
      obtain ⟨a, ha⟩ := hS
      have hh' : h = K.ι a * W.Q := by rw [ha]; group
      have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (Zl_sq z hzl)
      have hQz : W.Q * (K.ι z)⁻¹ * W.Q⁻¹ = (K.ι z)⁻¹ := by
        rw [← map_inv, W.hQ, hzi, phiR_Zl W.j z hzl]
      have key : K.ι z * h * (K.ι z)⁻¹ * h⁻¹ = K.ι (z * a * z⁻¹ * a⁻¹) := by
        rw [hh', show K.ι z * (K.ι a * W.Q) * (K.ι z)⁻¹ * (K.ι a * W.Q)⁻¹ =
          K.ι z * K.ι a * (W.Q * (K.ι z)⁻¹ * W.Q⁻¹) * (K.ι a)⁻¹ by group, hQz]
        simp [map_mul, map_inv]
      rw [key, ← K.ι_k]
      rcases comm_Zl z hzl a with e | e
      · left; rw [e, map_one]
      · right; rw [e]

include W in
theorem conj_Zx' {y : X} (hy : y ∈ normalizer (T.P : Set X)) {z : X} (hz : z ∈ K.Zx) :
    y * z * y⁻¹ ∈ K.Zx := by
  have hz' : z ∈ zz T.P := by rw [W.zz_eq]; exact hz
  have := conj_zz hy hz'
  rwa [W.zz_eq] at this

end Lift

end T2

end Conf

end KD8c

end CFSG.ComponentClassification.HSFLit
