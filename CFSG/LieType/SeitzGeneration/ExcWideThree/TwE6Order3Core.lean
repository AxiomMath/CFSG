module

public import Certificates.Data.E6Order3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralWeyl

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

theorem len72 : e6Certificate.roots.length = 72 := by decide

theorem isRoot_root72 {k : ℕ} (hk : k < 72) : IsRoot Tag.E6 (e6Certificate.root k) :=
  RootCertificate.isRoot_root e6Certificate_check k (by rw [len72]; exact hk)

theorem root_inj {k k' : ℕ} (hk : k < 72) (hk' : k' < 72)
    (h : e6Certificate.root k = e6Certificate.root k') : k = k' := by
  have hn := e6Certificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at hn
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 (len72 ▸ hk))
    (List.mem_range.2 (len72 ▸ hk')) (congrArg List.ofFn h)

theorem exists_root72 {v : Fin Tag.E6.rank → ℤ} (hv : IsRoot Tag.E6 v) :
    ∃ k < 72, e6Certificate.root k = v := by
  obtain ⟨k, hk, hkv⟩ := RootCertificate.exists_root_eq e6Certificate_check hv
  exact ⟨k, len72 ▸ hk, hkv⟩

theorem root_basis (j : Fin Tag.E6.rank) :
    e6Certificate.root j = (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
  have hC := e6Certificate_check
  simp only [RootCertificate.check, Bool.and_eq_true] at hC
  obtain ⟨⟨hb, -⟩, -⟩ := hC
  simp only [RootCertificate.checkBasis, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at hb
  exact RootCertificate.eq_of_ofFn_beq (hb.2 j)

theorem parent_spec {b : ℕ} (hb6 : 6 ≤ b) (hb : b < 72) :
    e6Certificate.parent b < b ∧ ∃ h : e6Certificate.parentReflection b < Tag.E6.rank,
      e6Certificate.root b =
        reflect Tag.E6 ⟨_, h⟩ (e6Certificate.root (e6Certificate.parent b)) := by
  have hC := e6Certificate_check
  simp only [RootCertificate.check, Bool.and_eq_true] at hC
  obtain ⟨⟨-, hp⟩, -⟩ := hC
  simp only [RootCertificate.checkParents, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at hp
  rcases hp b (by rw [len72]; exact hb) with h | ⟨hlt, hrefl⟩
  · exact absurd h (by simp only [Tag.rank]; omega)
  · refine ⟨hlt, ?_⟩
    split at hrefl
    · rename_i h
      exact ⟨h, RootCertificate.eq_of_ofFn_beq hrefl⟩
    · exact absurd hrefl (by simp)

theorem iform_self_e6 {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  have h1 : Tag.E6.symmetrizer j j = 1 := by
    change (1 : Matrix (Fin 6) (Fin 6) ℤ) j j = 1
    exact Matrix.one_apply_eq j
  rw [hj, h1, mul_one]

theorem simple_inv (i : Fin Tag.E6.rank) : (simple Tag.E6 i)⁻¹ = simple Tag.E6 i :=
  inv_eq_of_mul_eq_one_right ((coxeterSystem Tag.E6).simple_mul_simple_self i)

theorem imgN_spec {k : ℕ} (hk : k < 72) (i : Fin Tag.E6.rank) :
    imgN k i < 72 ∧ e6Certificate.root (imgN k i) = simple Tag.E6 i • e6Certificate.root k := by
  have h := RootCertificate.image_spec e6Certificate_check (len72 ▸ hk) i
  refine ⟨len72 ▸ h.1, ?_⟩
  rw [simple_smul]
  exact h.2

theorem reflIdx_spec : ∀ (n b : ℕ), b < n → b < 72 → ∀ c, c < 72 →
    reflIdx n b c < 72 ∧
      e6Certificate.root (reflIdx n b c) =
        rootReflection (e6Certificate.root b) • e6Certificate.root c := by
  intro n
  induction n with
  | zero => intro b hb; omega
  | succ n ih =>
    intro b hbn hb72 c hc
    by_cases hb6 : b < 6
    · have h1 : reflIdx (n + 1) b c = imgN c b := by simp [reflIdx, hb6]
      rw [h1]
      obtain ⟨hlt, hroot⟩ := imgN_spec hc ⟨b, hb6⟩
      refine ⟨hlt, ?_⟩
      have h2 : rootReflection (e6Certificate.root b) = simple Tag.E6 ⟨b, hb6⟩ := by
        have h := rootReflection_eq_conj (w := (1 : WeylGroup Tag.E6)) (j := ⟨b, hb6⟩)
          (β := e6Certificate.root b) (by rw [one_smul, root_basis ⟨b, hb6⟩])
        rw [h]
        simp
      rw [h2]
      exact hroot
    · have hb6' : 6 ≤ b := by omega
      obtain ⟨hpb, hi, hroot_b⟩ := parent_spec hb6' hb72
      have h1 : reflIdx (n + 1) b c = imgN (reflIdx n (e6Certificate.parent b)
          (imgN c (e6Certificate.parentReflection b))) (e6Certificate.parentReflection b) := by
        simp [reflIdx, hb6]
      rw [h1]
      obtain ⟨hc'lt, hc'root⟩ := imgN_spec hc ⟨e6Certificate.parentReflection b, hi⟩
      obtain ⟨hrlt, hrroot⟩ := ih (e6Certificate.parent b) (by omega) (by omega) _ hc'lt
      obtain ⟨hlt, hroot⟩ := imgN_spec hrlt ⟨e6Certificate.parentReflection b, hi⟩
      refine ⟨hlt, ?_⟩
      rw [hroot, hrroot, hc'root]
      have hrb : e6Certificate.root b =
          simple Tag.E6 ⟨e6Certificate.parentReflection b, hi⟩ •
            e6Certificate.root (e6Certificate.parent b) := by
        rw [hroot_b, simple_smul]
      rw [hrb, rootReflection_smul_root _ (isRoot_root72 (by omega)), simple_inv, mul_smul,
        mul_smul]

theorem isA2Pair_of_add {a b c : ℕ} (ha : a < 72) (hb : b < 72) (hc : c < 72)
    (h : e6Certificate.root c = e6Certificate.root a + e6Certificate.root b) :
    IsA2Pair (e6Certificate.root a) (e6Certificate.root b) := by
  have hra := isRoot_root72 ha
  have hrb := isRoot_root72 hb
  have hrc : IsRoot Tag.E6 (e6Certificate.root a + e6Certificate.root b) := h ▸ isRoot_root72 hc
  have h2a := iform_self_e6 hra
  have h2b := iform_self_e6 hrb
  have h2c := iform_self_e6 hrc
  rw [iform_add_left, iform_add_right, iform_add_right, iform_comm (e6Certificate.root b),
    h2a, h2b] at h2c
  exact ⟨hra, hrb, hrc, by rw [h2a, h2b], by rw [h2a]; omega⟩

theorem norm_zero_of_single {w : WeylGroup Tag.E6}
    (h : ∀ j : Fin Tag.E6.rank, (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) + w • w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = 0)
    (v : Fin Tag.E6.rank → ℤ) : v + w • v + w • w • v = 0 := by
  have hv : v = ∑ j : Fin Tag.E6.rank, v j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have key : v + w • v + w • w • v = ∑ j : Fin Tag.E6.rank, v j •
      ((Pi.single j 1 : Fin Tag.E6.rank → ℤ) + w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
        w • w • (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) := by
    conv_lhs => rw [hv]
    simp only [Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_comm w]
  rw [key]
  exact Finset.sum_eq_zero fun j _ => by rw [h j, smul_zero]

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3
