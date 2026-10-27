module

public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module

universe u

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def commonKernel (L : Submodule K (Module.End K V)) : Submodule K V :=
  ⨅ f : L, LinearMap.ker (f : Module.End K V)

@[simp] theorem mem_commonKernel {L : Submodule K (Module.End K V)} {v : V} :
    v ∈ commonKernel L ↔ ∀ f ∈ L, f v = 0 := by
  simp [commonKernel]

theorem commonKernel_le_ker {L : Submodule K (Module.End K V)} {f : Module.End K V}
    (hf : f ∈ L) : commonKernel L ≤ LinearMap.ker f := by
  intro v hv
  rw [mem_commonKernel] at hv
  exact hv f hf

@[expose] def imageSpan (L : Submodule K (Module.End K V)) : Submodule K V :=
  ⨆ f : L, LinearMap.range (f : Module.End K V)

theorem range_le_imageSpan {L : Submodule K (Module.End K V)} {f : Module.End K V}
    (hf : f ∈ L) : LinearMap.range f ≤ imageSpan L :=
  le_iSup (fun f : L => LinearMap.range (f : Module.End K V)) ⟨f, hf⟩

theorem imageSpan_eq_bot_of_eq_bot {L : Submodule K (Module.End K V)} (h : L = ⊥) :
    imageSpan L = ⊥ := by
  rw [imageSpan, iSup_eq_bot]
  intro f
  have hf : (f : Module.End K V) = 0 := by
    have hmem : (f : Module.End K V) ∈ (⊥ : Submodule K (Module.End K V)) := by
      rw [← h]
      exact f.2
    simpa using hmem
  rw [hf]
  simp

theorem inf_ker_ne_bot_of_isNilpotent {W : Submodule K V} {f : Module.End K V}
    (hW : W ≠ ⊥) (hinv : ∀ w ∈ W, f w ∈ W) (hnil : IsNilpotent f) :
    W ⊓ LinearMap.ker f ≠ ⊥ := by
  obtain ⟨N, hN⟩ := hnil
  intro hbot
  rw [Submodule.eq_bot_iff] at hbot
  have hkey : ∀ k : ℕ, W ⊓ LinearMap.ker (f ^ k) = ⊥ := by
    intro k
    induction k with
    | zero =>
      have h1 : LinearMap.ker (1 : Module.End K V) = ⊥ := by
        ext x
        simp
      rw [pow_zero, h1]
      simp
    | succ k ih =>
      rw [Submodule.eq_bot_iff] at ih ⊢
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
      have hrec : (f ^ k) (f x) = 0 := by
        have h := hx.2
        rw [pow_succ] at h
        simpa using h
      have h1 : f x = 0 := ih (f x) ⟨hinv x hx.1, hrec⟩
      exact hbot x ⟨hx.1, h1⟩
  have hle : W ≤ LinearMap.ker (f ^ N) := by
    intro x hx
    rw [LinearMap.mem_ker, hN]
    rfl
  have hWbot : W = ⊥ := by
    rw [← inf_eq_left.mpr hle, hkey N]
  exact hW hWbot

theorem exists_killed_invariant [Module.Finite K V] {ι : Type*} {f : ι → Module.End K V}
    (hcomm : ∀ i j, f i * f j = f j * f i) (hnil : ∀ i, IsNilpotent (f i))
    {I : Submodule K V} (hI : I ≠ ⊥) (hIinv : ∀ i, ∀ x ∈ I, f i x ∈ I) :
    ∃ Z : Submodule K V, Z ≤ I ∧ Z ≠ ⊥ ∧ ∀ i, ∀ z ∈ Z, f i z = 0 := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ W : Submodule K V, W ≤ I ∧ W ≠ ⊥ ∧ (∀ i, ∀ w ∈ W, f i w ∈ W) ∧ finrank K W = m
  have hP : ∃ m, P m := ⟨_, I, le_rfl, hI, hIinv, rfl⟩
  obtain ⟨W, hWI, hWne, hWinv, hWfin⟩ := Nat.find_spec hP
  have hmin : ∀ W' : Submodule K V, W' ≤ I → W' ≠ ⊥ →
      (∀ i, ∀ w ∈ W', f i w ∈ W') → finrank K W ≤ finrank K W' := by
    intro W' h1 h2 h3
    have := Nat.find_min' hP ⟨W', h1, h2, h3, rfl⟩
    omega
  refine ⟨W, hWI, hWne, fun i z hz => ?_⟩
  have hx0mem : ∀ x ∈ W ⊓ LinearMap.ker (f i), f i x = 0 := by
    intro x hx
    have hx' : x ∈ W ⊓ LinearMap.ker (f i) := hx
    rw [Submodule.mem_inf, LinearMap.mem_ker] at hx'
    exact hx'.2
  have hne : W ⊓ LinearMap.ker (f i) ≠ ⊥ :=
    inf_ker_ne_bot_of_isNilpotent hWne (hWinv i) (hnil i)
  have hinv : ∀ j, ∀ x ∈ W ⊓ LinearMap.ker (f i), f j x ∈ W ⊓ LinearMap.ker (f i) := by
    rintro j x hx
    refine ⟨hWinv j x hx.1, LinearMap.mem_ker.mpr ?_⟩
    calc f i (f j x) = (f i * f j) x := rfl
      _ = (f j * f i) x := by rw [hcomm i j]
      _ = f j (f i x) := rfl
      _ = 0 := by rw [hx0mem x hx, map_zero]
  have hle : W ⊓ LinearMap.ker (f i) ≤ W := inf_le_left
  have hfin : finrank K ↥(W ⊓ LinearMap.ker (f i)) = finrank K ↥W :=
    le_antisymm (Submodule.finrank_mono hle) (hmin _ (le_trans hle hWI) hne hinv)
  have heq : W ⊓ LinearMap.ker (f i) = W := Submodule.eq_of_le_of_finrank_eq hle hfin
  have hker : W ≤ LinearMap.ker (f i) := by
    have h : W ⊓ LinearMap.ker (f i) ≤ LinearMap.ker (f i) := inf_le_right
    rwa [heq] at h
  exact hker hz

theorem commonKernel_ne_bot [Module.Finite K V] (L : Submodule K (Module.End K V))
    (hcomm : ∀ f ∈ L, ∀ g ∈ L, f * g = g * f)
    (hnil : ∀ f ∈ L, IsNilpotent f) (hV : Nontrivial V) : commonKernel L ≠ ⊥ := by
  haveI := hV
  obtain ⟨Z, -, hZne, hZk⟩ := exists_killed_invariant
    (f := fun f : L => (f : Module.End K V))
    (fun f g => hcomm f.val f.2 g.val g.2) (fun f => hnil f.val f.2)
    (I := ⊤) (by simp) (by simp)
  intro hbot
  have hZle : Z ≤ commonKernel L := by
    intro z hz
    rw [mem_commonKernel]
    intro f hf
    exact hZk ⟨f, hf⟩ z hz
  rw [hbot] at hZle
  exact hZne (le_bot_iff.mp hZle)

theorem dualMap_pow (f : Module.End K V) (k : ℕ) :
    ((f ^ k).dualMap : Module.End K (Module.Dual K V)) = f.dualMap ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    ext mu v
    rfl
  | succ k ih =>
    have h1 : f ^ (k + 1) = (f ^ k).comp f := pow_succ f k
    have h2 : f.dualMap ^ (k + 1) = f.dualMap * f.dualMap ^ k := pow_succ' f.dualMap k
    rw [h1, h2, ← LinearMap.dualMap_comp_dualMap f (f ^ k), ← ih]
    rfl

theorem dualMap_ne_zero [Module.Finite K V] [Nontrivial V] {f : Module.End K V} (hf : f ≠ 0) :
    f.dualMap ≠ 0 := by
  intro h
  apply hf
  ext v
  have h1 : ∀ mu : Module.Dual K V, mu (f v) = 0 := by
    intro mu
    have h2 : f.dualMap mu = 0 := by rw [h]; rfl
    have h3 : f.dualMap mu v = 0 := by rw [h2]; rfl
    simpa [LinearMap.dualMap_apply] using h3
  exact (Module.forall_dual_apply_eq_zero_iff K (f v)).mp h1

theorem exists_dual_annihilating [Module.Finite K V] (L : Submodule K (Module.End K V))
    (hmul : ∀ f ∈ L, ∀ g ∈ L, f * g ∈ L)
    (hcomm : ∀ f ∈ L, ∀ g ∈ L, f * g = g * f)
    (hnil : ∀ f ∈ L, IsNilpotent f) (hL : L ≠ ⊥) :
    ∃ mu : Module.Dual K V, mu ≠ 0 ∧ imageSpan L ≤ LinearMap.ker mu ∧
      commonKernel L ≤ LinearMap.ker mu := by
  classical
  haveI : Module.Finite K (Module.Dual K V) := Module.dual_finite
  let A : L → Module.End K (Module.Dual K V) := fun f => (f : Module.End K V).dualMap
  have hAcomm : ∀ i j, A i * A j = A j * A i := by
    intro i j
    ext mu v
    simp only [Module.End.mul_apply, A, LinearMap.dualMap_apply]
    have h1 : (j : Module.End K V) ((i : Module.End K V) v) =
        (i : Module.End K V) ((j : Module.End K V) v) := by
      calc (j : Module.End K V) ((i : Module.End K V) v)
          = ((j : Module.End K V) * (i : Module.End K V)) v := rfl
        _ = ((i : Module.End K V) * (j : Module.End K V)) v := by
              rw [← hcomm i i.2 j j.2]
        _ = (i : Module.End K V) ((j : Module.End K V) v) := rfl
    rw [h1]
  have hAnil : ∀ i, IsNilpotent (A i) := by
    rintro ⟨f, hf⟩
    obtain ⟨N, hN⟩ := hnil f hf
    refine ⟨N, ?_⟩
    rw [show A ⟨f, hf⟩ = f.dualMap from rfl, ← dualMap_pow, hN]
    ext mu v
    simp
  let I : Submodule K (Module.Dual K V) := ⨆ f : L, LinearMap.range (A f)
  have hIne : I ≠ ⊥ := by
    obtain ⟨f, hfL, hfne⟩ := Submodule.ne_bot_iff L |>.mp hL
    haveI : Nontrivial V := by
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra h
        simp only [not_exists, ne_eq, not_not] at h
        exact hfne (by ext v; exact h v)
      refine ⟨v, 0, ?_⟩
      intro h
      exact hv (by rw [h, map_zero])
    have hfd : (f : Module.End K V).dualMap ≠ 0 := dualMap_ne_zero hfne
    have hrange : LinearMap.range ((f : Module.End K V).dualMap) ≠ ⊥ := by
      rwa [Ne, LinearMap.range_eq_bot]
    intro hbot
    have hle : LinearMap.range ((f : Module.End K V).dualMap) ≤ I :=
      le_iSup (fun g : L => LinearMap.range (A g)) ⟨f, hfL⟩
    rw [hbot] at hle
    exact hrange (le_bot_iff.mp hle)
  have hIinv : ∀ i, ∀ x ∈ I, A i x ∈ I := by
    intro i x hx
    have hle : I ≤ Submodule.comap (A i) I := by
      change (⨆ g : L, LinearMap.range (A g)) ≤ Submodule.comap (A i) I
      refine iSup_le fun g => ?_
      rintro y ⟨y', rfl⟩
      have hmem : A i (A g y') =
          (((g : Module.End K V) * (i : Module.End K V))).dualMap y' := by
        ext v
        simp only [A, LinearMap.dualMap_apply]
        rfl
      rw [Submodule.mem_comap, hmem]
      exact le_iSup (fun h : L => LinearMap.range (A h))
        ⟨(g : Module.End K V) * (i : Module.End K V), hmul g g.2 i i.2⟩ ⟨y', rfl⟩
    exact hle hx
  obtain ⟨Z, hZI, hZne, hZk⟩ := exists_killed_invariant (f := A) hAcomm hAnil hIne hIinv
  obtain ⟨mu, hmuZ, hmune⟩ := Submodule.ne_bot_iff Z |>.mp hZne
  refine ⟨mu, hmune, ?_, ?_⟩
  · refine iSup_le fun f => ?_
    rintro v ⟨w, rfl⟩
    have hkill : A f mu = 0 := hZk f mu hmuZ
    rw [LinearMap.mem_ker]
    have h3 : A f mu w = 0 := by rw [hkill]; rfl
    simpa [A, LinearMap.dualMap_apply] using h3
  · have hZle : mu ∈ Submodule.dualAnnihilator (commonKernel L) := by
      have hIle : I ≤ Submodule.dualAnnihilator (commonKernel L) := by
        change (⨆ f : L, LinearMap.range (A f)) ≤ Submodule.dualAnnihilator (commonKernel L)
        refine iSup_le fun f => ?_
        rintro y ⟨w, rfl⟩
        rw [Submodule.mem_dualAnnihilator]
        intro v hv
        rw [mem_commonKernel] at hv
        have h0 : (f : Module.End K V) v = 0 := hv (f : Module.End K V) f.2
        simp [A, LinearMap.dualMap_apply, h0]
      exact hIle (hZI hmuZ)
    intro v hv
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_dualAnnihilator mu).mp hZle v hv

@[expose] noncomputable def restrictEnd (U : Submodule K V) (f : Module.End K V)
    (hf : ∀ u ∈ U, f u ∈ U) : Module.End K U where
  toFun u := ⟨f u, hf u u.2⟩
  map_add' u v := by ext; simp
  map_smul' c u := by ext; simp

@[simp] theorem restrictEnd_apply (U : Submodule K V) (f : Module.End K V)
    (hf : ∀ u ∈ U, f u ∈ U) (u : U) : ((restrictEnd U f hf) u : V) = f u := rfl

section Restrict

variable (L : Submodule K (Module.End K V)) (U : Submodule K V) (hU : imageSpan L ≤ U)

@[expose] noncomputable def restrictMap : L →ₗ[K] Module.End K U where
  toFun f := restrictEnd U (f : Module.End K V) (fun u _ => hU (range_le_imageSpan f.2 ⟨u, rfl⟩))
  map_add' f g := by ext u; simp
  map_smul' c f := by ext u; simp

theorem restrictMap_apply (f : L) (u : U) :
    ((restrictMap L U hU f) u : V) = (f : Module.End K V) u := rfl

theorem restrictMap_pow_apply (f : L) (k : ℕ) (u : U) :
    (((restrictMap L U hU f) ^ k) u : V) = ((f : Module.End K V) ^ k) (u : V) := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rfl

theorem restrictMap_mul (hmul : ∀ f ∈ L, ∀ g ∈ L, f * g ∈ L) (f g : L) :
    restrictMap L U hU ⟨(f : Module.End K V) * g, hmul f f.2 g g.2⟩ =
      restrictMap L U hU f * restrictMap L U hU g := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  show (((restrictMap L U hU) ⟨(f : Module.End K V) * g, hmul f f.2 g g.2⟩) u : V) =
    (((restrictMap L U hU f) * (restrictMap L U hU g)) u : V)
  simp only [Module.End.mul_apply, restrictMap_apply]

end Restrict

variable {L : Submodule K (Module.End K V)} {U : Submodule K V} {hU : imageSpan L ≤ U}

theorem restrictMap_range_mul_mem (hmul : ∀ f ∈ L, ∀ g ∈ L, f * g ∈ L) :
    ∀ a ∈ LinearMap.range (restrictMap L U hU), ∀ b ∈ LinearMap.range (restrictMap L U hU),
      a * b ∈ LinearMap.range (restrictMap L U hU) := by
  rintro a ⟨f, rfl⟩ b ⟨g, rfl⟩
  exact ⟨⟨(f : Module.End K V) * g, hmul f f.2 g g.2⟩,
    restrictMap_mul L U hU hmul f g⟩

theorem restrictMap_range_comm (hmul : ∀ f ∈ L, ∀ g ∈ L, f * g ∈ L)
    (hcomm : ∀ f ∈ L, ∀ g ∈ L, f * g = g * f) :
    ∀ a ∈ LinearMap.range (restrictMap L U hU), ∀ b ∈ LinearMap.range (restrictMap L U hU),
      a * b = b * a := by
  rintro a ⟨f, rfl⟩ b ⟨g, rfl⟩
  rw [← restrictMap_mul L U hU hmul f g, ← restrictMap_mul L U hU hmul g f]
  congr 1
  exact Subtype.ext (hcomm f f.2 g g.2)

theorem restrictMap_range_isNilpotent (hnil : ∀ f ∈ L, IsNilpotent f) :
    ∀ a ∈ LinearMap.range (restrictMap L U hU), IsNilpotent a := by
  rintro a ⟨f, rfl⟩
  obtain ⟨N, hN⟩ := hnil f f.2
  refine ⟨N, ?_⟩
  ext u
  rw [restrictMap_pow_apply, hN]
  rfl

private theorem finrank_le_commonKernel_mul_aux (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module.Finite K V]
      (L : Submodule K (Module.End K V)),
      finrank K V = n →
      (∀ f ∈ L, ∀ g ∈ L, f * g ∈ L) →
      (∀ f ∈ L, ∀ g ∈ L, f * g = g * f) →
      (∀ f ∈ L, IsNilpotent f) →
      finrank K L ≤ finrank K (commonKernel L) *
        (finrank K V - finrank K (commonKernel L)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ L hVn hmul hcomm hnil
    rw [hVn]
    by_cases hspan : imageSpan L = ⊥
    · have hLbot : L = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro f hf
        ext v
        have hv : f v ∈ imageSpan L := range_le_imageSpan hf ⟨v, rfl⟩
        rw [hspan] at hv
        simpa using hv
      rw [hLbot]
      simp
    · have hLne : L ≠ ⊥ := fun h => hspan (imageSpan_eq_bot_of_eq_bot h)
      have hn1 : 0 < n := by
        have hVntriv : Nontrivial V := by
          obtain ⟨f, hfL, hfne⟩ := Submodule.ne_bot_iff L |>.mp hLne
          obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
            by_contra h
            simp only [not_exists, ne_eq, not_not] at h
            exact hfne (by ext v; exact h v)
          exact ⟨v, 0, fun h => hv (by rw [h, map_zero])⟩
        rw [← hVn]
        exact Module.finrank_pos_iff.mpr hVntriv
      obtain ⟨mu, hmune, h1, h2⟩ := exists_dual_annihilating L hmul hcomm hnil hLne
      set U : Submodule K V := LinearMap.ker mu with hUdef
      have hUtne : U ≠ ⊤ := by
        intro htop
        apply hmune
        ext v
        have hv : v ∈ U := by rw [htop]; trivial
        simpa [hUdef] using hv
      have hfinU : finrank K U = n - 1 := by
        have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := mu) hmune
        rw [hVn] at h
        have h' : finrank K U + 1 = n := by rw [hUdef]; exact h
        omega
      have hCU : commonKernel L ≤ U := by rw [hUdef]; exact h2
      have hLU : imageSpan L ≤ U := by rw [hUdef]; exact h1
      let LU : Submodule K (Module.End K U) := LinearMap.range (restrictMap L U hLU)
      let K0 : Submodule K L := LinearMap.ker (restrictMap L U hLU)
      have hmulU : ∀ a ∈ LU, ∀ b ∈ LU, a * b ∈ LU :=
        restrictMap_range_mul_mem (L := L) (U := U) (hU := hLU) hmul
      have hcommU : ∀ a ∈ LU, ∀ b ∈ LU, a * b = b * a :=
        restrictMap_range_comm (L := L) (U := U) (hU := hLU) hmul hcomm
      have hnilU : ∀ a ∈ LU, IsNilpotent a :=
        restrictMap_range_isNilpotent (L := L) (U := U) (hU := hLU) hnil
      have hrank : finrank K L = finrank K K0 + finrank K LU := by
        have h := LinearMap.finrank_range_add_finrank_ker (restrictMap L U hLU)
        rw [add_comm]
        exact h.symm
      have hmap : (commonKernel LU).map U.subtype = commonKernel L := by
        ext v
        constructor
        · rintro ⟨u, hu, rfl⟩
          rw [mem_commonKernel]
          intro f hf
          have hmem : restrictMap L U hLU ⟨f, hf⟩ ∈ LU := ⟨⟨f, hf⟩, rfl⟩
          have h1' : ((restrictMap L U hLU ⟨f, hf⟩) u : V) = 0 := by
            have h2 : (restrictMap L U hLU ⟨f, hf⟩) u = 0 := commonKernel_le_ker hmem hu
            rw [h2]
            rfl
          have h2' : f (U.subtype u) = ((restrictMap L U hLU ⟨f, hf⟩) u : V) := rfl
          rw [h2']
          exact h1'
        · intro hv
          rw [Submodule.mem_map]
          have hvU : v ∈ U := hCU hv
          refine ⟨⟨v, hvU⟩, ?_, rfl⟩
          rw [mem_commonKernel]
          rintro g ⟨f, rfl⟩
          have hv0 : (f : Module.End K V) v = 0 := by
            rw [mem_commonKernel] at hv
            exact hv f f.2
          apply Subtype.ext
          simpa [restrictMap_apply] using hv0
      have hd : finrank K (commonKernel LU) = finrank K (commonKernel L) := by
        rw [← hmap, Submodule.finrank_map_subtype_eq]
      have hIH := ih (finrank K U) (by rw [← hVn]; exact Submodule.finrank_lt hUtne)
        U LU rfl hmulU hcommU hnilU
      have hIH' : finrank K LU ≤
          finrank K (commonKernel L) * (finrank K U - finrank K (commonKernel L)) := by
        simpa only [hd] using hIH
      have hK0 : finrank K K0 ≤ finrank K (commonKernel L) := by
        obtain ⟨e, he⟩ : ∃ e : V, e ∉ U := by
          by_contra h
          simp only [not_exists, not_not] at h
          exact hUtne (Submodule.eq_top_iff'.mpr h)
        have he0 : e ≠ 0 := fun h => he (h ▸ Submodule.zero_mem U)
        have hspan1 : finrank K (Submodule.span K {e}) = 1 := finrank_span_singleton he0
        have hdisj : U ⊓ Submodule.span K {e} = ⊥ := by
          rw [Submodule.eq_bot_iff]
          rintro x ⟨hxU, hxspan⟩
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxspan
          rw [← hc] at hxU
          by_cases hc0 : c = 0
          · rw [← hc, hc0, zero_smul]
          · exfalso
            apply he
            have hmem : c⁻¹ • (c • e) ∈ U := U.smul_mem _ hxU
            rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at hmem
        have hsup : U ⊔ Submodule.span K {e} = ⊤ := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span K {e}) (K := K)
          rw [hdisj, hspan1, finrank_bot, hfinU] at h
          refine Submodule.eq_top_of_finrank_eq ?_
          rw [hVn]
          omega
        have hdecomp : ∀ v : V, ∃ u ∈ U, ∃ c : K, v = u + c • e := by
          intro v
          have hv : v ∈ U ⊔ Submodule.span K {e} := by rw [hsup]; trivial
          rw [Submodule.mem_sup] at hv
          obtain ⟨u, hu, w, hw, hvw⟩ := hv
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
          exact ⟨u, hu, c, by rw [← hvw, hc]⟩
        let psi : K0 →ₗ[K] V :=
          { toFun := fun x => x.1.1 e
            map_add' := fun x y => rfl
            map_smul' := fun c x => rfl }
        have hker_eval : ∀ x : K0, ∀ u ∈ U, x.1.1 u = 0 := by
          intro x u hu
          have hx0 : restrictMap L U hLU x.1 = 0 := x.2
          have h1' : ((restrictMap L U hLU x.1) ⟨u, hu⟩ : V) = 0 := by
            rw [hx0]
            rfl
          have h2' : ((restrictMap L U hLU x.1) ⟨u, hu⟩ : V) = x.1.1 u := rfl
          rw [← h2']
          exact h1'
        have hpsiC : ∀ x : K0, x.1.1 e ∈ commonKernel L := by
          intro x
          rw [mem_commonKernel]
          intro g hg
          have hge : g e ∈ U := hLU (range_le_imageSpan hg ⟨e, rfl⟩)
          calc g (x.1.1 e) = ((g : Module.End K V) * x.1.1) e := rfl
            _ = (x.1.1 * (g : Module.End K V)) e := by rw [hcomm g hg x.1.1 x.1.2]
            _ = x.1.1 (g e) := rfl
            _ = 0 := hker_eval x (g e) hge
        have hpsiinj : Function.Injective psi := by
          intro x y hxy
          have hval : x.1.1 e = y.1.1 e := hxy
          have hxy' : x.1.1 = y.1.1 := by
            ext v
            obtain ⟨u, hu, c, rfl⟩ := hdecomp v
            rw [map_add, map_smul, map_add, map_smul, hker_eval x u hu, hker_eval y u hu, hval]
          exact Subtype.ext (Subtype.ext hxy')
        calc finrank K K0 = finrank K (LinearMap.range psi) :=
              (LinearMap.finrank_range_of_inj hpsiinj).symm
          _ ≤ finrank K (commonKernel L) := Submodule.finrank_mono (by
              rintro _ ⟨x, rfl⟩
              exact hpsiC x)
      have hCne : commonKernel L ≠ ⊤ := by
        intro htop
        apply hLne
        rw [Submodule.eq_bot_iff]
        intro f hf
        ext v
        have hv : v ∈ commonKernel L := by rw [htop]; trivial
        rw [mem_commonKernel] at hv
        exact hv f hf
      have hdle : finrank K (commonKernel L) ≤ n - 1 := by
        have hlt := Submodule.finrank_lt hCne
        rw [hVn] at hlt
        omega
      calc finrank K L
          = finrank K K0 + finrank K LU := hrank
        _ ≤ finrank K (commonKernel L) +
              finrank K (commonKernel L) * (finrank K U - finrank K (commonKernel L)) :=
            Nat.add_le_add hK0 hIH'
        _ = finrank K (commonKernel L) * (n - finrank K (commonKernel L)) := by
            rw [hfinU]
            have hsub : n - finrank K (commonKernel L) =
                (n - 1 - finrank K (commonKernel L)) + 1 := by omega
            rw [hsub, Nat.mul_add, Nat.mul_one, add_comm]

theorem finrank_le_commonKernel_mul {V : Type u} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (L : Submodule K (Module.End K V))
    (hmul : ∀ f ∈ L, ∀ g ∈ L, f * g ∈ L)
    (hcomm : ∀ f ∈ L, ∀ g ∈ L, f * g = g * f)
    (hnil : ∀ f ∈ L, IsNilpotent f) :
    finrank K L ≤
      finrank K (commonKernel L) * (finrank K V - finrank K (commonKernel L)) :=
  finrank_le_commonKernel_mul_aux (K := K) (finrank K V) V L rfl hmul hcomm hnil

end CFSG.HardMathSupport.GuralnickMalle
