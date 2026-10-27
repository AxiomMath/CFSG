module

public import CFSG.Fischer.Classification.PartII.O2Mono
public import CFSG.Fischer.Classification.PartII.Twins.Fourth

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin
open scoped commutatorElement

namespace O2G

theorem three_dvd_ncard_of_cube {α : Type*} {s : Set α} (hs : s.Finite) (σ : α → α)
    (hmaps : ∀ x ∈ s, σ x ∈ s) (h3 : ∀ x ∈ s, σ (σ (σ x)) = x) (hfree : ∀ x ∈ s, σ x ≠ x) :
    3 ∣ s.ncard := by
  obtain ⟨n, hn⟩ : ∃ n, s.ncard = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · rw [Set.ncard_empty]
      exact dvd_zero 3
    · have h1 := hmaps x hx
      have h2 := hmaps _ h1
      have n01 : σ x ≠ x := hfree x hx
      have n12 : σ (σ x) ≠ σ x := hfree _ h1
      have n02 : σ (σ x) ≠ x := fun e => n01 (by have h := h3 x hx; rw [e] at h; exact h)
      have hsub : ({x, σ x, σ (σ x)} : Set α) ⊆ s := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hx
        · exact h1
        · exact h2
      have hc3 : ({x, σ x, σ (σ x)} : Set α).ncard = 3 := by
        have hx' : x ∉ ({σ x, σ (σ x)} : Set α) := by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨n01.symm, n02.symm⟩
        rw [Set.ncard_insert_of_notMem hx', Set.ncard_pair n12.symm]
      have hle : 3 ≤ n := hn ▸ hc3 ▸ Set.ncard_le_ncard hsub hs
      have hcard : (s \ {x, σ x, σ (σ x)}).ncard = n - 3 := by
        rw [Set.ncard_sdiff hsub, hc3, hn]
      have hmaps' : ∀ y ∈ s \ {x, σ x, σ (σ x)}, σ y ∈ s \ {x, σ x, σ (σ x)} := by
        rintro y ⟨hys, hyn⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hyn
        refine ⟨hmaps y hys, fun hm => ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        have hy3 := h3 y hys
        rcases hm with e | e | e
        · exact hyn.2.2 (by rw [← hy3, e])
        · exact hyn.1 (by rw [← h3 y hys, e, h3 x hx])
        · exact hyn.2.1 (by rw [← h3 y hys, e, h3 x hx])
      have hrest := ih ((s \ {x, σ x, σ (σ x)}).ncard) (by omega) (s := s \ {x, σ x, σ (σ x)})
        (hs.subset Set.sdiff_subset) hmaps' (fun y hy => h3 y hy.1) (fun y hy => hfree y hy.1)
        rfl
      rw [hcard] at hrest
      obtain ⟨m, hm⟩ := hrest
      rw [hn]
      exact ⟨m + 1, by omega⟩

end O2G

namespace O2Mod

variable {X : Type} [Group X] {E : Set X}

theorem cube_eq_of_affine (hP : Pair X E) {d e z : X} (hd : d ∈ E) (he : e ∈ E) (hz : z ∈ E)
    (hde : d * e ≠ e * d) (hdz : d * z ≠ z * d) (hez : e * z ≠ z * e)
    (hzl : z * (d * e * d) ≠ d * e * d * z) :
    (z * d * z * (e * z * e) * (d * e * d)) ^ 3 = d := by
  have hR := Pair.cubeRel_of_affine hP hd he hz hde hdz hez hzl
  have hcom := Pair.commute_commutator_of_affine hP hd he hz hde hdz hez hzl
  obtain ⟨x, hx⟩ : ∃ x, x = d * e := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = d * z := ⟨_, rfl⟩
  rw [← hx, ← hy] at hR hcom
  have hdd : d * d = 1 := Pair.mul_self hP hd
  have he' : e = d * x := by rw [hx, ← mul_assoc, hdd, one_mul]
  have hz' : z = d * y := by rw [hy, ← mul_assoc, hdd, one_mul]
  have hdy : d * y * d = y⁻¹ := by rw [hy]; exact Pair.conj_mul_eq_inv hP hd hz
  have hxx : x * x = x⁻¹ := by rw [← sq]; exact sq_eq_inv_of_pow_three hR.cube_left
  have hyy : y⁻¹ * y⁻¹ = y := by
    rw [← mul_inv_rev, ← sq, sq_eq_inv_of_pow_three hR.cube_right, inv_inv]
  have key :
      z * d * z * (e * z * e) * (d * e * d) = d * y * y * d * x * (d * y * d) * x * x * d := by
    rw [he', hz']
    simp only [mul_assoc, mul_mul_self hP hd]
  have h1 : d * y * y * d = y⁻¹ * y⁻¹ := by
    rw [← hdy]
    simp only [mul_assoc, mul_mul_self hP hd]
  have hG : z * d * z * (e * z * e) * (d * e * d) = ⁅y, x⁆ * d := by
    rw [key, commutatorElement_def]
    calc d * y * y * d * x * (d * y * d) * x * x * d
        = d * y * y * d * x * (d * y * d) * (x * x) * d := by simp only [mul_assoc]
      _ = y * x * y⁻¹ * x⁻¹ * d := by rw [h1, hdy, hxx, hyy]
  have hc : Commute ⁅y, x⁆ d := by
    rw [← commutatorElement_inv]
    exact hcom.inv_right.symm
  have hc3 : ⁅y, x⁆ ^ 3 = 1 := by
    rw [← commutatorElement_inv, inv_pow, hR.commutator_pow_three, inv_one]
  rw [hG, hc.mul_pow, hc3, one_mul, pow_succ, sq, hdd, one_mul]

variable {H : Type} [Group H] {E μ : Set H}

namespace IsTwinSection

variable (hμ : IsTwinSection E μ) (hP : Pair H E)
include hμ hP

theorem mate_eq_conj {f g : H} (hf : f ∈ E) (hfμ : f ∉ μ) (hg : g ∈ E) (hfg : f * g ≠ g * f) :
    mate E μ f g = sec E μ f * sec E μ g * sec E μ f * f *
      (sec E μ f * sec E μ g * sec E μ f) := by
  rw [← hμ.sec_mul_mul hP hf hg hfg]
  set s := sec E μ (f * g * f)
  have hfgf : f * g * f ∈ E := Pair.mul_mul_mem hP hf hg
  have hs := hμ.sec_mem hfgf
  have hsE := hμ.subset hs
  have hts : IsTwin E (f * g * f) s := hμ.isTwin_sec hfgf
  have hf1 : f * (f * g * f) ≠ f * g * f * f := by
    rw [show f * (f * g * f) = g * f by
        rw [← mul_assoc, ← mul_assoc, Pair.mul_self hP hf, one_mul],
      show f * g * f * f = f * g by rw [mul_assoc, Pair.mul_self hP hf, mul_one]]
    exact fun e => hfg e.symm
  have hfs : s * f ≠ f * s := fun e => hf1 ((hts.2.2.2 f hf).2 e.symm)
  have hgt : IsTwin E g (s * f * s) := by
    have h' := isTwin_conj hP f hts
    rwa [Pair.inv_eq hP hf, Pair.mul_mul_mul_mul hP hf,
      Pair.mul_mul_eq hP hf hsE fun e => hfs e.symm] at h'
  rw [← hμ.mate_congr hP hf hfμ hg hfg hgt]
  exact hμ.mate_conj hP hs hf hfμ hfs

theorem three_dvd_ncard_of_affine {f g k : H} (hf : f ∈ E) (hg : g ∈ E) (hk : k ∈ E)
    (hfg : f * g ≠ g * f) (hgk : g * k ≠ k * g) (hfk : f * k ≠ k * f)
    (hc : k * (f * g * f) ≠ f * g * f * k) :
    3 ∣ (twinClass E f \ μ).ncard := by
  have := Pair.finite hP
  obtain ⟨d, hd⟩ : ∃ d, sec E μ f = d := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, sec E μ g = e := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, sec E μ k = z := ⟨_, rfl⟩
  have hdf : IsTwin E f d := hd ▸ hμ.isTwin_sec hf
  have heg : IsTwin E g e := he ▸ hμ.isTwin_sec hg
  have hzk : IsTwin E k z := hz ▸ hμ.isTwin_sec hk
  have hdE := hdf.2.1
  have heE := heg.2.1
  have hzE := hzk.2.1
  have hde : d * e ≠ e * d := by
    have h1 : g * d ≠ d * g := fun e' => hfg ((hdf.2.2.2 g hg).2 e').symm
    exact fun e' => h1 ((heg.2.2.2 d hdE).2 e').symm
  have hdz : d * z ≠ z * d := by
    have h1 : k * d ≠ d * k := fun e' => hfk ((hdf.2.2.2 k hk).2 e').symm
    exact fun e' => h1 ((hzk.2.2.2 d hdE).2 e').symm
  have hez : e * z ≠ z * e := by
    have h1 : k * e ≠ e * k := fun e' => hgk ((heg.2.2.2 k hk).2 e').symm
    exact fun e' => h1 ((hzk.2.2.2 e heE).2 e').symm
  have hzl : z * (d * e * d) ≠ d * e * d * z := by
    have hfgf : f * g * f ∈ E := Pair.mul_mul_mem hP hf hg
    have htw : IsTwin E (f * g * f) (d * e * d) := by
      rw [← hd, ← he, ← hμ.sec_mul_mul hP hf hg hfg]
      exact hμ.isTwin_sec hfgf
    have h1 : k * (d * e * d) ≠ d * e * d * k := fun e' => hc ((htw.2.2.2 k hk).2 e')
    exact fun e' => h1 (((hzk.2.2.2 _ htw.2.1).2 e'.symm).symm)
  have hG3 : (z * d * z * (e * z * e) * (d * e * d)) ^ 3 = d :=
    cube_eq_of_affine hP hdE heE hzE hde hdz hez hzl
  obtain ⟨G, hG⟩ : ∃ G, z * d * z * (e * z * e) * (d * e * d) = G := ⟨_, rfl⟩
  rw [hG] at hG3
  have hinv : G⁻¹ = d * e * d * (e * z * e) * (z * d * z) := by
    rw [← hG]
    simp only [mul_inv_rev, Pair.inv_eq hP hdE, Pair.inv_eq hP heE, Pair.inv_eq hP hzE,
      mul_assoc]
  have hstep : ∀ f' ∈ twinClass E f \ μ,
      mate E μ (mate E μ (mate E μ f' g) k) f ∈ twinClass E f \ μ ∧
        mate E μ (mate E μ (mate E μ f' g) k) f = G * f' * G⁻¹ := by
    rintro f' ⟨hff', hf'μ⟩
    have hf'E := hff'.2.1
    have hf'g : f' * g ≠ g * f' := not_commute_of_isTwin hff' hg hfg
    have h1 := hμ.mate_eq_conj hP hf'E hf'μ hg hf'g
    rw [← hμ.sec_eq_sec hff', hd, he] at h1
    have hf₁E := hμ.mate_mem hP hf'E hf'μ hg hf'g
    have hf₁μ := hμ.mate_notMem hP hf'E hf'μ hg hf'g
    have hgf₁ := hμ.isTwin_mate hP hf'E hf'μ hg hf'g
    have hf₁k := not_commute_of_isTwin hgf₁ hk hgk
    have h2 := hμ.mate_eq_conj hP hf₁E hf₁μ hk hf₁k
    rw [← hμ.sec_eq_sec hgf₁, he, hz] at h2
    have hf₂E := hμ.mate_mem hP hf₁E hf₁μ hk hf₁k
    have hf₂μ := hμ.mate_notMem hP hf₁E hf₁μ hk hf₁k
    have hkf₂ := hμ.isTwin_mate hP hf₁E hf₁μ hk hf₁k
    have hf₂f : _ * f ≠ f * _ := not_commute_of_isTwin hkf₂ hf fun e' => hfk e'.symm
    have h3 := hμ.mate_eq_conj hP hf₂E hf₂μ hf hf₂f
    rw [← hμ.sec_eq_sec hkf₂, hz, hd] at h3
    refine ⟨⟨hμ.isTwin_mate hP hf₂E hf₂μ hf hf₂f, hμ.mate_notMem hP hf₂E hf₂μ hf hf₂f⟩, ?_⟩
    rw [h3, h2, h1, hinv, ← hG]
    simp only [mul_assoc]
  refine O2G.three_dvd_ncard_of_cube (Set.toFinite _) (fun f' => G * f' * G⁻¹)
    (fun f' hf' => (hstep f' hf').2 ▸ (hstep f' hf').1) (fun f' hf' => ?_) (fun f' hf' => ?_)
  ·
    show G * (G * (G * f' * G⁻¹) * G⁻¹) * G⁻¹ = f'
    have hdf' : IsTwin E f' d := isTwin_trans (isTwin_symm hf'.1) hdf
    calc G * (G * (G * f' * G⁻¹) * G⁻¹) * G⁻¹ = G ^ 3 * f' * (G ^ 3)⁻¹ := by
          rw [pow_three]; group
      _ = f' := by
        rw [hG3, Pair.inv_eq hP hdE, ← hdf'.2.2.1, mul_assoc, Pair.mul_self hP hdE, mul_one]
  ·
    show G * f' * G⁻¹ ≠ f'
    rw [← (hstep f' hf').2]
    obtain ⟨hff', hf'μ⟩ := hf'
    have hf'E := hff'.2.1
    have hf'g : f' * g ≠ g * f' := not_commute_of_isTwin hff' hg hfg
    have hf'k : f' * k ≠ k * f' := not_commute_of_isTwin hff' hk hfk
    have hc' : k * (f' * g * f') ≠ f' * g * f' * k := by
      have htw := Pair.isTwin_mul_mul hP hff' hg hfg
      exact fun e' => hc ((htw.2.2.2 k hk).2 e')
    have hf₁E := hμ.mate_mem hP hf'E hf'μ hg hf'g
    have hf₁μ := hμ.mate_notMem hP hf'E hf'μ hg hf'g
    have hgf₁ := hμ.isTwin_mate hP hf'E hf'μ hg hf'g
    have hf₁k := not_commute_of_isTwin hgf₁ hk hgk
    have hf₂E := hμ.mate_mem hP hf₁E hf₁μ hk hf₁k
    have hf₂μ := hμ.mate_notMem hP hf₁E hf₁μ hk hf₁k
    have hkf₂ := hμ.isTwin_mate hP hf₁E hf₁μ hk hf₁k
    have hf₂f : _ * f ≠ f * _ := not_commute_of_isTwin hkf₂ hf fun e' => hfk e'.symm
    rw [← hμ.mate_congr hP hf₂E hf₂μ hf hf₂f hff']
    exact hμ.mate_mate_mate_ne_of_affine hP hf'E hf'μ hg hk hf'g hgk hf'k hc'

end IsTwinSection

end O2Mod

end CFSG.Fischer.Classification
