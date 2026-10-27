module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance

public section

namespace CFSG.QuasithinUnique.Lin2.Five

open CFSG.Open CFSG.Quasithin
open scoped Pointwise

section Generic

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_right_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {g : G} :
    g ∈ A ⊔ B ↔ ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B h]
  exact Set.mem_mul

theorem comm_inv_of_comm {s x : G} (hxs : x * s = s * x) : x⁻¹ * s = s * x⁻¹ := by
  calc x⁻¹ * s = x⁻¹ * (s * x) * x⁻¹ := by group
    _ = x⁻¹ * (x * s) * x⁻¹ := by rw [hxs]
    _ = s * x⁻¹ := by group

theorem Ks_le_centralizer {L : Subgroup G} {s x : G} (hxs : x * s = s * x) :
    L ⊓ Subgroup.centralizer ({s} : Set G) ⊔ conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x ≤
      Subgroup.centralizer ({s} : Set G) := by
  refine sup_le inf_le_right ?_
  have h : conjR (Subgroup.centralizer ({s} : Set G)) x = Subgroup.centralizer ({s} : Set G) :=
    conjR_eq_of_mem_normalizer
      (Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hxs))
  calc conjR (L ⊓ Subgroup.centralizer ({s} : Set G)) x
      ≤ conjR (Subgroup.centralizer ({s} : Set G)) x := conjR_mono inf_le_right x
    _ = Subgroup.centralizer ({s} : Set G) := h

theorem three_le_of_four_lt_two_pow {n : ℕ} (h4 : 4 < 2 ^ n) : 3 ≤ n := by
  by_contra h
  have h2 : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at h2
  omega

theorem sq_conj_eq_self {U : Subgroup G} (hU : IsElemAbelian 2 U) {s y : G} (hs2 : s * s = 1)
    (hsU : s ∈ Subgroup.normalizer (U : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hsy : s * y = y * s) (hyW : ∀ w ∈ U, s * w * s⁻¹ = w → y * w * y⁻¹ = w) :
    ∀ a ∈ U, y * (y * a * y⁻¹) * y⁻¹ = a := by
  intro a ha
  have hcomm : ∀ {p q : G}, p ∈ U → q ∈ U → p * q = q * p := fun hp hq =>
    IsElemAbelian.comm hU hp hq
  have hinv : ∀ {p : G}, p ∈ U → p⁻¹ = p := fun {p} hp =>
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hU.2 p hp)
  have hsmem : ∀ {p : G}, p ∈ U → s * p * s⁻¹ ∈ U := fun {p} hp =>
    (Subgroup.mem_normalizer_iff.mp hsU p).mp hp
  have hymem : ∀ {p : G}, p ∈ U → y * p * y⁻¹ ∈ U := fun {p} hp =>
    (Subgroup.mem_normalizer_iff.mp hyU p).mp hp
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hss : s⁻¹ * s⁻¹ = 1 := by rw [hs1]; exact hs2
  have hsy' : y⁻¹ * s⁻¹ = s⁻¹ * y⁻¹ := by rw [← mul_inv_rev, ← mul_inv_rev, hsy]
  obtain ⟨a', ha'⟩ : ∃ a', s * a * s⁻¹ = a' := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, y * a * y⁻¹ = b := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', y * a' * y⁻¹ = b' := ⟨_, rfl⟩
  have ha'U : a' ∈ U := ha' ▸ hsmem ha
  have hbU : b ∈ U := hb ▸ hymem ha
  have hsa' : s * a' * s⁻¹ = a := by
    rw [← ha']
    calc s * (s * a * s⁻¹) * s⁻¹ = (s * s) * a * (s⁻¹ * s⁻¹) := by group
      _ = a := by rw [hs2, hss]; group
  have hsc : s * (a * a') * s⁻¹ = a * a' := by
    calc s * (a * a') * s⁻¹ = (s * a * s⁻¹) * (s * a' * s⁻¹) := by group
      _ = a' * a := by rw [ha', hsa']
      _ = a * a' := hcomm ha'U ha
  have hyc : y * (a * a') * y⁻¹ = a * a' := hyW _ (U.mul_mem ha ha'U) hsc
  have hbb' : b * b' = a * a' := by
    calc b * b' = (y * a * y⁻¹) * (y * a' * y⁻¹) := by rw [hb, hb']
      _ = y * (a * a') * y⁻¹ := by group
      _ = a * a' := hyc
  have hsb : s * b * s⁻¹ = b' := by
    calc s * b * s⁻¹ = s * (y * a * y⁻¹) * s⁻¹ := by rw [hb]
      _ = (s * y) * a * (y⁻¹ * s⁻¹) := by group
      _ = (y * s) * a * (s⁻¹ * y⁻¹) := by rw [hsy, hsy']
      _ = y * (s * a * s⁻¹) * y⁻¹ := by group
      _ = b' := by rw [ha', hb']
  have hη : s * (a * b) * s⁻¹ = a * b := by
    have h1 : s * (a * b) * s⁻¹ = a' * b' := by
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = a' * b' := by rw [ha', hsb]
    have hb'U : b' ∈ U := hb' ▸ hymem ha'U
    have h2 : (a * b) * (a' * b') = 1 := by
      calc (a * b) * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hcomm hbU ha'U]
        _ = (a * a') * (b * b') := by group
        _ = (a * a') * (a * a') := by rw [hbb']
        _ = 1 := by simpa [pow_two] using hU.2 _ (U.mul_mem ha ha'U)
    have h3 : a' * b' = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h2
    rw [h1, h3]
    exact hinv (U.mul_mem ha hbU)
  have hyη : y * (a * b) * y⁻¹ = a * b := hyW _ (U.mul_mem ha hbU) hη
  have h4 : b * (y * b * y⁻¹) = a * b := by
    calc b * (y * b * y⁻¹) = (y * a * y⁻¹) * (y * b * y⁻¹) := by rw [hb]
      _ = y * (a * b) * y⁻¹ := by group
      _ = a * b := hyη
  have h5 : y * b * y⁻¹ = b⁻¹ * (a * b) := by
    rw [eq_inv_mul_iff_mul_eq]
    exact h4
  rw [hb, h5]
  calc b⁻¹ * (a * b) = b⁻¹ * (b * a) := by rw [hcomm ha hbU]
    _ = a := by group

theorem mem_or_inv_mul_mem_of_sq_mem [Finite G] {R S F : Subgroup G}
    (hSR : S ≤ Subgroup.normalizer (R : Set G)) (hFS : F ≤ S) (hcyc : IsCyclic F)
    (hRF : R ⊓ F = ⊥) (hRFS : R ⊔ F = S) {s y : G} (hs : s ∈ S) (hsR : s ∉ R) (hs2 : s ^ 2 = 1)
    (hy : y ∈ S) (hy2 : y ^ 2 ∈ R) : y ∈ R ∨ s⁻¹ * y ∈ R := by
  have hFN : F ≤ Subgroup.normalizer (R : Set G) := hFS.trans hSR
  have key : ∀ z ∈ S, z ^ 2 ∈ R → ∃ r ∈ R, ∃ f ∈ F, z = r * f ∧ f ^ 2 = 1 := by
    intro z hz hz2
    obtain ⟨r, hr, f, hf, rfl⟩ := (mem_sup_iff_of_right_le_normalizer hFN).mp (hRFS ▸ hz)
    have hfN : f ∈ Subgroup.normalizer (R : Set G) := hFN hf
    have hrf : f * r * f⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hfN r).mp hr
    refine ⟨r, hr, f, hf, rfl, ?_⟩
    have hmem : f ^ 2 ∈ R ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨?_, F.pow_mem hf 2⟩
      have e : f ^ 2 = (r * (f * r * f⁻¹))⁻¹ * (r * f) ^ 2 := by
        calc f ^ 2 = f * f := pow_two f
          _ = (r * (f * r * f⁻¹))⁻¹ * ((r * f) * (r * f)) := by group
          _ = (r * (f * r * f⁻¹))⁻¹ * (r * f) ^ 2 := by rw [pow_two]
      rw [e]
      exact R.mul_mem (R.inv_mem (R.mul_mem hr hrf)) hz2
    rw [hRF] at hmem
    simpa using hmem
  obtain ⟨r, hr, f, hf, hyrf, hf2⟩ := key y hy hy2
  obtain ⟨r', hr', f', hf', hsr'f', hf'2⟩ := key s hs (by rw [hs2]; exact R.one_mem)
  have hf'1 : f' ≠ 1 := by
    rintro rfl
    exact hsR (by rw [hsr'f', mul_one]; exact hr')
  by_cases hf1 : f = 1
  · left
    rw [hyrf, hf1, mul_one]
    exact hr
  · right
    have hff' : (⟨f, hf⟩ : F) = ⟨f', hf'⟩ := by
      have : IsCyclic ↥F := hcyc
      exact eq_of_sq_eq_one_of_isCyclic (Subtype.ext (by simpa [pow_two] using hf2))
        (Subtype.ext (by simpa [pow_two] using hf'2)) (fun h => hf1 (congrArg Subtype.val h))
        (fun h => hf'1 (congrArg Subtype.val h))
    have hf_eq : f = f' := congrArg Subtype.val hff'
    have hsy : s⁻¹ * y = f'⁻¹ * (r'⁻¹ * r) * f' := by
      rw [hyrf, hsr'f', hf_eq]
      group
    rw [hsy]
    have hf'N : f'⁻¹ ∈ Subgroup.normalizer (R : Set G) := (Subgroup.normalizer _).inv_mem (hFN hf')
    have := (Subgroup.mem_normalizer_iff.mp hf'N (r'⁻¹ * r)).mp
      (R.mul_mem (R.inv_mem hr') hr)
    simpa using this

end Generic

end CFSG.QuasithinUnique.Lin2.Five
