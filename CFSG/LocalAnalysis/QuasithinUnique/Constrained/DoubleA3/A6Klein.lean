module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6KleinCore

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

theorem code_inv (σ : P10) : code σ⁻¹ = cinvC (code σ) := by
  have hnd : (code σ).Nodup := by
    unfold code
    exact List.nodup_ofFn.mpr (fun a b h => σ.injective (Fin.ext h))
  apply List.ext_getElem?
  intro n
  rw [code_getElem?]
  unfold cinvC
  rw [code_length, List.getElem?_map]
  by_cases hn : n < 10
  · rw [List.getElem?_range hn]
    simp only [hn, ↓reduceDIte, Option.map_some]
    congr 1
    set j : Fin 10 := σ⁻¹ ⟨n, hn⟩ with hj
    have hjl : j.val < (code σ).length := by rw [code_length]; exact j.2
    have hget : (code σ)[j.val]'hjl = n := by
      have h1 : σ j = ⟨n, hn⟩ := by
        rw [hj]
        exact σ.apply_symm_apply ⟨n, hn⟩
      simp only [code, List.getElem_ofFn]
      simpa using congrArg Fin.val h1
    have := hnd.idxOf_getElem j.val hjl
    rw [hget] at this
    exact this.symm
  · simp only [hn, ↓reduceDIte]
    have h1 : (List.range 10)[n]? = none := List.getElem?_eq_none (by rw [List.length_range]; omega)
    rw [h1]
    rfl

theorem code_conjb (b w : P10) : code (b * w * b⁻¹) = conjb (code b) (code w) := by
  rw [code_mul, code_mul, code_inv]
  rfl

theorem code_inj_iff {x y : P10} : code x = code y ↔ x = y := code_injective.eq_iff

theorem code_cid_iff {x : P10} : code x = Core.cid ↔ x = 1 := by
  rw [← code_one, code_inj_iff]

theorem mem_tauList {x : P10} (hx : x ∈ A6Models.psl29)
    (hτ : x * A6Models.tFrob = A6Models.tFrob * x) : code x ∈ tauList := by
  unfold tauList Core.cpslList
  rw [List.mem_filter]
  refine ⟨(mem_psl29_iff x).1 hx, ?_⟩
  simp only [beq_iff_eq]
  rw [← tFrob_code, ← code_mul, ← code_mul, hτ]

theorem klein_stable_P10 {c z b y₁ y₂ y₃ : P10}
    (hcP : c ∈ A6Models.psl29) (hzP : z ∈ A6Models.psl29)
    (hbs : b ∈ s6)
    (hcτ : c * A6Models.tFrob = A6Models.tFrob * c) (hzτ : z * A6Models.tFrob = A6Models.tFrob * z)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcz : c * z * c⁻¹ ≠ z) (hcomm : (c * z * c⁻¹) * z = z * (c * z * c⁻¹))
    (hy₁P : y₁ ∈ A6Models.psl29) (hy₂P : y₂ ∈ A6Models.psl29) (hy₃P : y₃ ∈ A6Models.psl29)
    (hy₁ : b * z = y₁ * b) (hy₂ : b * (c * z * c⁻¹) = y₂ * b)
    (hy₃ : b * (c * (c * z * c⁻¹) * c⁻¹) = y₃ * b)
    (hτ₁ : y₁ * A6Models.tFrob = A6Models.tFrob * y₁)
    (hτ₂ : y₂ * A6Models.tFrob = A6Models.tFrob * y₂)
    (hτ₃ : y₃ * A6Models.tFrob = A6Models.tFrob * y₃) :
    (y₁ = z ∨ y₁ = c * z * c⁻¹ ∨ y₁ = c * (c * z * c⁻¹) * c⁻¹) ∧
    (y₂ = z ∨ y₂ = c * z * c⁻¹ ∨ y₂ = c * (c * z * c⁻¹) * c⁻¹) ∧
    (y₃ = z ∨ y₃ = c * z * c⁻¹ ∨ y₃ = c * (c * z * c⁻¹) * c⁻¹) := by
  have hci : c⁻¹ = c * c := by
    apply inv_eq_of_mul_eq_one_right
    calc c * (c * c) = c ^ 3 := (pow_three c).symm
      _ = 1 := hc3
  have hccc : c * c * c = 1 := by
    calc c * c * c = c ^ 3 := (pow_three' c).symm
      _ = 1 := hc3
  have hconj2 : code (c * z * c⁻¹) = conjC (code c) (code z) := by
    rw [hci]; simp only [conjC, code_mul]
  have hconj3 : code (c * (c * z * c⁻¹) * c⁻¹) = conjC (code c) (conjC (code c) (code z)) := by
    rw [← hconj2, hci]; simp only [conjC, code_mul]
  have hCt := mem_tauList hcP hcτ
  have hZt := mem_tauList hzP hzτ
  obtain ⟨hZV, hW2V, hW3V, hd12, hd23, hd13⟩ := V0l_conj (code c) hCt (code z) hZt
    ⟨by rw [← code_mul, ← code_mul, hccc, code_one], fun h => hc1 (code_cid_iff.1 h),
      by rw [← code_mul, hz2, code_one], fun h => hz1 (code_cid_iff.1 h),
      by rw [← hconj2]; exact fun h => hcz (code_inj_iff.1 h),
      by rw [← hconj2, ← code_mul, ← code_mul, hcomm]⟩
  have hcomm_of : ∀ w : P10, w * A6Models.tFrob = A6Models.tFrob * w →
      A6Models.tFrob * w * A6Models.tFrob⁻¹ = w := by
    intro w hw
    calc A6Models.tFrob * w * A6Models.tFrob⁻¹ = (w * A6Models.tFrob) * A6Models.tFrob⁻¹ := by
          rw [hw]
      _ = w := by group
  obtain ⟨b', hb'P, hb'⟩ : ∃ b' ∈ A6Models.psl29, ∀ w : P10,
      w * A6Models.tFrob = A6Models.tFrob * w → b' * w * b'⁻¹ = b * w * b⁻¹ := by
    rcases s6_cases hbs with h | h
    · exact ⟨b, h, fun w _ => rfl⟩
    · refine ⟨b * A6Models.tFrob, h, fun w hw => ?_⟩
      calc b * A6Models.tFrob * w * (b * A6Models.tFrob)⁻¹
          = b * (A6Models.tFrob * w * A6Models.tFrob⁻¹) * b⁻¹ := by group
        _ = b * w * b⁻¹ := by rw [hcomm_of w hw]
  have hcC : Commute c A6Models.tFrob := hcτ
  have hzC : Commute z A6Models.tFrob := hzτ
  have hw2τ : (c * z * c⁻¹) * A6Models.tFrob = A6Models.tFrob * (c * z * c⁻¹) :=
    ((hcC.mul_left hzC).mul_left hcC.inv_left : Commute (c * z * c⁻¹) A6Models.tFrob)
  have hw3τ : (c * (c * z * c⁻¹) * c⁻¹) * A6Models.tFrob =
      A6Models.tFrob * (c * (c * z * c⁻¹) * c⁻¹) :=
    ((hcC.mul_left (show Commute (c * z * c⁻¹) A6Models.tFrob from hw2τ)).mul_left
      hcC.inv_left : Commute (c * (c * z * c⁻¹) * c⁻¹) A6Models.tFrob)
  have hbconj : ∀ w y : P10, w * A6Models.tFrob = A6Models.tFrob * w → b * w = y * b →
      code y = conjb (code b') (code w) := by
    intro w y hw hwy
    rw [← code_conjb, hb' w hw]
    congr 1
    calc y = (y * b) * b⁻¹ := by group
      _ = b * w * b⁻¹ := by rw [← hwy]
  have hprem : ∀ w ∈ V0l, conjb (code b') w ∈ tauList := by
    intro w hw
    rcases V0l_three (code z) hZV _ hW2V _ hW3V hd12.symm hd23.symm hd13.symm w hw with
      h | h | h
    · rw [h, ← hbconj z y₁ hzτ hy₁]
      exact mem_tauList hy₁P hτ₁
    · rw [h, ← hconj2, ← hbconj _ y₂ hw2τ hy₂]
      exact mem_tauList hy₂P hτ₂
    · rw [h, ← hconj3, ← hbconj _ y₃ hw3τ hy₃]
      exact mem_tauList hy₃P hτ₃
  have hconcl := klein_conj_check (code b') ((mem_psl29_iff b').1 hb'P) hprem
  have hstep : ∀ (w y : P10), w * A6Models.tFrob = A6Models.tFrob * w → code w ∈ V0l →
      b * w = y * b → code y ∈ V0l := by
    intro w y hw hwV hwy
    rw [hbconj w y hw hwy]
    exact hconcl (code w) hwV
  have hfin : ∀ y : P10, code y ∈ V0l →
      (y = z ∨ y = c * z * c⁻¹ ∨ y = c * (c * z * c⁻¹) * c⁻¹) := by
    intro y hy
    rcases V0l_three (code z) hZV _ hW2V _ hW3V hd12.symm hd23.symm hd13.symm (code y) hy with
      h | h | h
    · exact Or.inl (code_inj_iff.1 h)
    · exact Or.inr (Or.inl (code_inj_iff.1 (h.trans hconj2.symm)))
    · exact Or.inr (Or.inr (code_inj_iff.1 (h.trans hconj3.symm)))
  refine ⟨hfin _ ?_, hfin _ ?_, hfin _ ?_⟩
  · exact hstep z y₁ hzτ hZV hy₁
  · exact hstep _ y₂ hw2τ (by rw [hconj2]; exact hW2V) hy₂
  · exact hstep _ y₃ hw3τ (by rw [hconj3]; exact hW3V) hy₃


theorem autA6_le_of_not_mem_s6 (H : Subgroup P10) (hpsl : A6Models.psl29 ≤ H)
    (hF : A6Models.tFrob ∈ H) {b : P10} (hbH : b ∈ H) (hbA : b ∈ A6Models.autA6) (hbs : b ∉ s6) :
    A6Models.autA6 ≤ H := by
  have hs6 : psl29_le_s6 = psl29_le_s6 := rfl
  have hF6 : A6Models.tFrob ∈ s6 := tFrob_mem_s6
  have hMul : A6Models.tMul ∈ H := by
    obtain ⟨r, hr, hbr⟩ := (mem_autA6_iff_exists b).1 hbA
    simp only [autRepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact absurd (psl29_le_s6 (by simpa using hbr)) hbs
    · have h1 : b * A6Models.tMul⁻¹ ∈ H := hpsl hbr
      have : A6Models.tMul = (b * A6Models.tMul⁻¹)⁻¹ * b := by group
      rw [this]
      exact H.mul_mem (H.inv_mem h1) hbH
    · apply absurd _ hbs
      have h1 : b * A6Models.tFrob⁻¹ ∈ s6 := psl29_le_s6 hbr
      have : b = (b * A6Models.tFrob⁻¹) * A6Models.tFrob := by group
      rw [this]
      exact s6.mul_mem h1 hF6
    · have h1 : b * (A6Models.tMul * A6Models.tFrob)⁻¹ ∈ H := hpsl hbr
      have h2 : A6Models.tMul * A6Models.tFrob ∈ H := by
        have : A6Models.tMul * A6Models.tFrob = (b * (A6Models.tMul * A6Models.tFrob)⁻¹)⁻¹ * b := by
          group
        rw [this]
        exact H.mul_mem (H.inv_mem h1) hbH
      have : A6Models.tMul = (A6Models.tMul * A6Models.tFrob) * A6Models.tFrob⁻¹ := by group
      rw [this]
      exact H.mul_mem h2 (H.inv_mem hF)
  intro x hx
  obtain ⟨r, hr, hxr⟩ := (mem_autA6_iff_exists x).1 hx
  have hrH : r ∈ H := by
    simp only [autRepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hMul
    · exact hF
    · exact H.mul_mem hMul hF
  have : x = (x * r⁻¹) * r := by group
  rw [this]
  exact H.mul_mem (hpsl hxr) hrH

theorem mulAut_eq_top_of_model {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29)
    (Hk : Subgroup (MulAut K)) (h1 : ∀ k₀ : K, MulAut.conj k₀ ∈ Hk)
    (h2 : ∃ γ ∈ Hk, ∀ k : K, ((φ (γ k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹)
    (h3 : ∃ γ ∈ Hk, ∃ b : P10, b ∈ A6Models.autA6 ∧ b ∉ s6 ∧ ∀ k : K,
      ((φ (γ k) : ↥A6Models.psl29) : P10) = b * ((φ k : ↥A6Models.psl29) : P10) * b⁻¹) :
    Hk = ⊤ := by
  let H : Subgroup P10 :=
    { carrier := {a | ∃ γ ∈ Hk, ∀ k : K, ((φ (γ k) : ↥A6Models.psl29) : P10) =
        a * ((φ k : ↥A6Models.psl29) : P10) * a⁻¹}
      mul_mem' := by
        rintro a₁ a₂ ⟨γ₁, hγ₁, h₁⟩ ⟨γ₂, hγ₂, h₂⟩
        refine ⟨γ₁ * γ₂, Hk.mul_mem hγ₁ hγ₂, fun k => ?_⟩
        show ((φ (γ₁ (γ₂ k)) : ↥A6Models.psl29) : P10) = _
        rw [h₁, h₂]
        group
      one_mem' := ⟨1, Hk.one_mem, fun k => by simp⟩
      inv_mem' := by
        rintro a ⟨γ, hγ, h⟩
        refine ⟨γ⁻¹, Hk.inv_mem hγ, fun k => ?_⟩
        have h' := h (γ⁻¹ k)
        have e : γ (γ⁻¹ k) = k := by
          show γ (γ.symm k) = k
          exact γ.apply_symm_apply k
        rw [e] at h'
        calc ((φ (γ⁻¹ k) : ↥A6Models.psl29) : P10)
            = a⁻¹ * (a * ((φ (γ⁻¹ k) : ↥A6Models.psl29) : P10) * a⁻¹) * a := by group
          _ = a⁻¹ * ((φ k : ↥A6Models.psl29) : P10) * a := by rw [← h'] }
  have hpsl : A6Models.psl29 ≤ H := by
    intro y hy
    refine ⟨MulAut.conj (φ.symm ⟨y, hy⟩), h1 _, fun k => ?_⟩
    show ((φ (φ.symm ⟨y, hy⟩ * k * (φ.symm ⟨y, hy⟩)⁻¹) : ↥A6Models.psl29) : P10) = _
    simp
  have hF : A6Models.tFrob ∈ H := h2
  obtain ⟨γ₃, hγ₃, b, hbA, hbs, hb⟩ := h3
  have hbH : b ∈ H := ⟨γ₃, hγ₃, hb⟩
  have hle := autA6_le_of_not_mem_s6 H hpsl hF hbH hbA hbs
  rw [eq_top_iff]
  intro α _
  obtain ⟨a, haA, ha⟩ := exists_aut_model φ α
  obtain ⟨γ, hγ, hγa⟩ := hle haA
  have : γ = α := by
    ext k
    apply φ.injective
    apply Subtype.ext
    rw [hγa k, ha k]
  rw [← this]
  exact hγ

end CFSG.QuasithinUnique.DoubleA3
