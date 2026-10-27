module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitInvPair
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.CommInvolutions

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix Module

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem trace_eq_of_sq_scalar (h2 : (2 : K) ≠ 0) (a : Matrix ι ι K) (l : K) (hl0 : l ≠ 0)
    (haa : ∀ x, a *ᵥ (a *ᵥ x) = (l ^ 2) • x) :
    Matrix.trace a = l * (2 * (finrank K (eig a l) : K) - (Fintype.card ι : K)) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix ι ι K, P = (2⁻¹ : K) • (1 + l⁻¹ • a) := ⟨_, rfl⟩
  have hPx : ∀ x, P *ᵥ x = (2⁻¹ : K) • (x + l⁻¹ • (a *ᵥ x)) := fun x => by
    rw [hPdef, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  have hP : LinearMap.IsProj (eig a l) (Matrix.toLin' P) := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [Matrix.toLin'_apply, hPx, mem_eig]
      simp only [Matrix.mulVec_smul, Matrix.mulVec_add, haa]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    · rw [Matrix.toLin'_apply, hPx, mem_eig.1 hx, smul_smul l⁻¹ l, inv_mul_cancel₀ hl0, one_smul,
        ← two_smul K x, smul_smul, inv_mul_cancel₀ h2, one_smul]
  have h1 := hP.trace
  rw [Matrix.trace_toLin'_eq, hPdef, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul, smul_eq_mul] at h1
  field_simp at h1
  linear_combination h1

theorem exists_eig_line (h2 : (2 : K) ≠ 0) (hcard : Fintype.card ι = 4) (a : Matrix ι ι K)
    (l : K) (hl0 : l ≠ 0) (haa : ∀ x, a *ᵥ (a *ᵥ x) = (l ^ 2) • x)
    (hns : ∀ c : K, ∃ x, a *ᵥ x ≠ c • x) (htr : Matrix.trace a ≠ 0) :
    ∃ s : K, finrank K (eig a s) = 1 ∧ (s = l ∨ s = -l) := by
  have hsum := eig_finrank a l hl0 haa h2 hcard
  obtain ⟨hb1, hb2⟩ := eig_ne_bot a l hl0 haa h2 hns
  have h1 : 1 ≤ finrank K (eig a l) := Submodule.one_le_finrank_iff.2 hb1
  have h1' : 1 ≤ finrank K (eig a (-l)) := Submodule.one_le_finrank_iff.2 hb2
  have hne2 : finrank K (eig a l) ≠ 2 := by
    intro h2'
    apply htr
    rw [trace_eq_of_sq_scalar h2 a l hl0 haa, h2', hcard]
    norm_num
  rcases (by omega : finrank K (eig a l) = 1 ∨ finrank K (eig a l) = 3) with h | h
  · exact ⟨l, h, Or.inl rfl⟩
  · exact ⟨-l, by omega, Or.inr rfl⟩

theorem card_le_of_traceless (h4 : (Fintype.card ι : K) ≠ 0) (H : Subgroup (GL ι K))
    (hA : ∀ g ∈ H, (∃ c : K, (g : Matrix ι ι K) = c • 1) ∨ Matrix.trace (g : Matrix ι ι K) = 0)
    (T : Finset (Matrix ι ι K)) (hT : ∀ t ∈ T, ∃ g ∈ H, (g : Matrix ι ι K) = t)
    (hTnp : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∀ c : K, t ≠ c • t') :
    T.card ≤ Fintype.card ι * Fintype.card ι := by
  classical
  have hli : LinearIndependent K (fun t : T => (t : Matrix ι ι K)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha t₀
    obtain ⟨g₀, hg₀, hg₀t⟩ := hT t₀ t₀.2
    have h1 : ∑ t : T, a t • ((t : Matrix ι ι K) * ((g₀⁻¹ : GL ι K) : Matrix ι ι K)) = 0 := by
      have := congrArg (fun M => M * ((g₀⁻¹ : GL ι K) : Matrix ι ι K)) ha
      simpa [Finset.sum_mul, Matrix.smul_mul] using this
    have h2' := congrArg Matrix.trace h1
    simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_zero, smul_eq_mul] at h2'
    have key : ∀ t : T, t ≠ t₀ →
        Matrix.trace ((t : Matrix ι ι K) * ((g₀⁻¹ : GL ι K) : Matrix ι ι K)) = 0 := by
      intro t ht
      obtain ⟨g, hg, hgt⟩ := hT t t.2
      have hmem : g * g₀⁻¹ ∈ H := H.mul_mem hg (H.inv_mem hg₀)
      rcases hA _ hmem with ⟨c, hc⟩ | hc
      · exfalso
        have e1 : (t : Matrix ι ι K) * ((g₀⁻¹ : GL ι K) : Matrix ι ι K) = c • 1 := by
          rw [← hgt, ← Units.val_mul]; exact hc
        have e2 : (t : Matrix ι ι K) = c • (t₀ : Matrix ι ι K) := by
          have := congrArg (fun M => M * (g₀ : Matrix ι ι K)) e1
          simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at this
          rw [this, ← hg₀t]
        exact hTnp t t.2 t₀ t₀.2 (fun h => ht (Subtype.ext h)) c e2
      · rw [← hgt, ← Units.val_mul]; exact hc
    rw [Finset.sum_eq_single t₀ (fun t _ ht => by rw [key t ht, mul_zero]) (by simp)] at h2'
    have e : (t₀ : Matrix ι ι K) * ((g₀⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← hg₀t, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [e, Matrix.trace_one] at h2'
    exact (mul_eq_zero.1 h2').resolve_right h4
  have := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix] at this
  simpa using this

theorem card_le_of_abelian (h2 : (2 : K) ≠ 0) (hcard : Fintype.card ι = 4)
    (H : Subgroup (GL ι K))
    (H1 : ∀ g ∈ H, ∃ l : K, (g : Matrix ι ι K) * g = (l ^ 2) • 1)
    (habel : ∀ g ∈ H, ∀ g' ∈ H, (g : Matrix ι ι K) * g' = g' * g)
    (T : Finset (Matrix ι ι K)) (hT : ∀ t ∈ T, ∃ g ∈ H, (g : Matrix ι ι K) = t)
    (hTnp : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∀ c : K, t ≠ c • t') : 2 * T.card ≤ 16 := by
  classical
  have hex : ∀ t : T, ∃ l : K, l ≠ 0 ∧ (t : Matrix ι ι K) * t = (l ^ 2) • 1 ∧
      ∃ g ∈ H, (g : Matrix ι ι K) = t := by
    intro t
    obtain ⟨g, hg, hgt⟩ := hT t t.2
    obtain ⟨l, hl⟩ := H1 g hg
    refine ⟨l, ?_, by rw [← hgt]; exact hl, g, hg, hgt⟩
    rintro rfl
    have h0 : (g : Matrix ι ι K) * g = 0 := by rw [hl]; simp
    have h1 : (1 : Matrix ι ι K) = 0 := by
      calc (1 : Matrix ι ι K) = ((g⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) * ((g * g : GL ι K) : Matrix ι ι K) := by
            rw [← Units.val_mul]; group; simp
        _ = 0 := by rw [Units.val_mul g g, h0, mul_zero]
    have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i⟩ := hne
    have := congrFun (congrFun h1 i) i
    simp at this
  choose lt hlt0 hlt hg using hex
  have hcomm : ∀ t t' : T, (t : Matrix ι ι K) * t' = t' * t := by
    intro t t'
    obtain ⟨g, hgH, hgt⟩ := hg t
    obtain ⟨g', hgH', hgt'⟩ := hg t'
    rw [← hgt, ← hgt']
    exact habel g hgH g' hgH'
  let sg : Bool → K := fun b => if b then 1 else -1
  have hsg2 : ∀ b, sg b * sg b = 1 := by intro b; cases b <;> simp [sg]
  have hsg0 : ∀ b, sg b ≠ 0 := by intro b; cases b <;> simp [sg]
  let M : T × Bool → Matrix ι ι K := fun p => (sg p.2 * (lt p.1)⁻¹) • (p.1 : Matrix ι ι K)
  let G : T × Bool → (ι → K) →ₗ[K] (ι → K) := fun p => Matrix.toLin' (M p)
  have hMM : ∀ p, M p * M p = 1 := by
    intro p
    simp only [M, Matrix.smul_mul, Matrix.mul_smul, hlt p.1, smul_smul]
    have hl := inv_mul_cancel₀ (hlt0 p.1)
    have : sg p.2 * (lt p.1)⁻¹ * (sg p.2 * (lt p.1)⁻¹ * lt p.1 ^ 2) = 1 := by
      calc _ = (sg p.2 * sg p.2) * (((lt p.1)⁻¹ * lt p.1) * ((lt p.1)⁻¹ * lt p.1)) := by ring
        _ = 1 := by rw [hsg2, hl]; norm_num
    rw [this, one_smul]
  have hMcomm : ∀ p q, M p * M q = M q * M p := by
    intro p q
    simp only [M, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hcomm p.1 q.1, mul_comm (sg p.2 * (lt p.1)⁻¹)]
  have hne0 : ∀ t : T, (t : Matrix ι ι K) ≠ 0 := by
    intro t h0
    have h1 := hlt t
    rw [h0, mul_zero] at h1
    have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i⟩ := hne
    have := congrFun (congrFun h1 i) i
    simp at this
    exact hlt0 t ((pow_eq_zero_iff (two_ne_zero)).1 this.symm)
  have hinj : Function.Injective G := by
    intro p q hpq
    have hMpq : M p = M q := Matrix.toLin'.injective hpq
    have hcp : sg p.2 * (lt p.1)⁻¹ ≠ 0 := mul_ne_zero (hsg0 _) (inv_ne_zero (hlt0 _))
    have hcq : sg q.2 * (lt q.1)⁻¹ ≠ 0 := mul_ne_zero (hsg0 _) (inv_ne_zero (hlt0 _))
    by_cases hpq1 : p.1 = q.1
    · obtain ⟨t, b⟩ := p
      obtain ⟨t', b'⟩ := q
      simp only at hpq1
      subst hpq1
      have h3 : (sg b * (lt t)⁻¹ - sg b' * (lt t)⁻¹) • (t : Matrix ι ι K) = 0 := by
        rw [sub_smul]; exact sub_eq_zero.2 hMpq
      have h4 : sg b * (lt t)⁻¹ - sg b' * (lt t)⁻¹ = 0 := by
        rcases smul_eq_zero.1 h3 with h | h
        · exact h
        · exact absurd h (hne0 t)
      have h5 : sg b = sg b' := by
        have : (sg b - sg b') * (lt t)⁻¹ = 0 := by linear_combination h4
        have := (mul_eq_zero.1 this).resolve_right (inv_ne_zero (hlt0 t))
        linear_combination this
      have : b = b' := by
        by_contra hne
        apply h2
        cases b <;> cases b' <;> first
          | exact absurd rfl hne
          | (simp only [sg, ite_true, ite_false, Bool.false_eq_true] at h5
             first | linear_combination h5 | linear_combination -h5)
      subst this
      rfl
    · exfalso
      have e : (p.1 : Matrix ι ι K) = ((sg p.2 * (lt p.1)⁻¹)⁻¹ * (sg q.2 * (lt q.1)⁻¹)) •
          (q.1 : Matrix ι ι K) := by
        have h6 : (sg p.2 * (lt p.1)⁻¹) • (p.1 : Matrix ι ι K) =
            (sg q.2 * (lt q.1)⁻¹) • (q.1 : Matrix ι ι K) := hMpq
        calc (p.1 : Matrix ι ι K) = (sg p.2 * (lt p.1)⁻¹)⁻¹ • ((sg p.2 * (lt p.1)⁻¹) •
              (p.1 : Matrix ι ι K)) := by rw [inv_smul_smul₀ hcp]
          _ = _ := by rw [h6, smul_smul]
      exact hTnp p.1 p.1.2 q.1 q.1.2 (fun h => hpq1 (Subtype.ext h)) _ e
  obtain ⟨F, hFdef⟩ : ∃ F : Finset ((ι → K) →ₗ[K] (ι → K)), F = Finset.univ.image G := ⟨_, rfl⟩
  have hF : F.card = 2 * T.card := by
    rw [hFdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_coe]
    ring
  have hinvF : ∀ f ∈ F, ∀ w ∈ (⊤ : Submodule K (ι → K)), f (f w) = w := by
    intro f hf w _
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 (hFdef ▸ hf)
    show (M p) *ᵥ ((M p) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hMM, Matrix.one_mulVec]
  have hcommF : ∀ f ∈ F, ∀ g ∈ F, ∀ v, f (g v) = g (f v) := by
    intro f hf g hg v
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 (hFdef ▸ hf)
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (hFdef ▸ hg)
    show (M p) *ᵥ ((M q) *ᵥ v) = (M q) *ᵥ ((M p) *ᵥ v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hMcomm]
  have hbound := card_le_of_commuting_involutions h2 (⊤ : Submodule K (ι → K)) F
    (fun _ _ _ _ => trivial) hinvF hcommF (fun f _ g _ hfg => LinearMap.ext fun w => hfg w trivial)
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, hcard, hF] at hbound
  simpa using hbound

theorem card_le_sixteen (h2 : (2 : K) ≠ 0) (h4 : (4 : K) ≠ 0) (hcard : Fintype.card ι = 4)
    (H : Subgroup (GL ι K))
    (H1 : ∀ g ∈ H, ∃ l : K, (g : Matrix ι ι K) * g = (l ^ 2) • 1)
    (H2 : ∀ g ∈ H, ∀ g' ∈ H, ∃ ε : K, (g : Matrix ι ι K) * g' = ε • ((g' : Matrix ι ι K) * g))
    (T : Finset (Matrix ι ι K)) (hT : ∀ t ∈ T, ∃ g ∈ H, (g : Matrix ι ι K) = t)
    (hTnp : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∀ c : K, t ≠ c • t') : T.card ≤ 16 := by
  classical
  have h4' : (Fintype.card ι : K) ≠ 0 := by rw [hcard]; exact_mod_cast h4
  by_cases hA : ∀ g ∈ H, (∃ c : K, (g : Matrix ι ι K) = c • 1) ∨ Matrix.trace (g : Matrix ι ι K) = 0
  · have := card_le_of_traceless h4' H hA T hT hTnp
    rw [hcard] at this
    omega
  · push Not at hA
    obtain ⟨a, haH, hns', htr⟩ := hA
    obtain ⟨l, hl⟩ := H1 a haH
    have hl0 : l ≠ 0 := by
      rintro rfl
      have h0 : (a : Matrix ι ι K) * a = 0 := by rw [hl]; simp
      have h1 : (1 : Matrix ι ι K) = 0 := by
        calc (1 : Matrix ι ι K) = ((a⁻¹ * a⁻¹ : GL ι K) : Matrix ι ι K) *
              ((a * a : GL ι K) : Matrix ι ι K) := by rw [← Units.val_mul]; group; simp
          _ = 0 := by rw [Units.val_mul a a, h0, mul_zero]
      have hne : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
      obtain ⟨i⟩ := hne
      have := congrFun (congrFun h1 i) i
      simp at this
    have haa : ∀ x, (a : Matrix ι ι K) *ᵥ ((a : Matrix ι ι K) *ᵥ x) = (l ^ 2) • x := by
      intro x
      rw [Matrix.mulVec_mulVec, hl, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hns : ∀ c : K, ∃ x, (a : Matrix ι ι K) *ᵥ x ≠ c • x := by
      intro c
      by_contra hc
      push Not at hc
      exact hns' c (Matrix.ext_iff_mulVec.2 fun x => by
        rw [hc x, Matrix.smul_mulVec, Matrix.one_mulVec])
    obtain ⟨s, hs1, -⟩ := exists_eig_line h2 hcard (a : Matrix ι ι K) l hl0 haa hns htr
    have hcommA : ∀ g ∈ H, (g : Matrix ι ι K) * (a : Matrix ι ι K) = (a : Matrix ι ι K) * g := by
      intro g hg
      obtain ⟨ε, hε⟩ := H2 g hg a haH
      have hε1 : ε = 1 := by
        have h1 : Matrix.trace ((g : Matrix ι ι K) * (a : Matrix ι ι K) *
            ((g⁻¹ : GL ι K) : Matrix ι ι K)) = Matrix.trace (a : Matrix ι ι K) := by
          rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, Matrix.one_mul]
        have h2' : (g : Matrix ι ι K) * (a : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) =
            ε • (a : Matrix ι ι K) := by
          rw [hε, Matrix.smul_mul, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
        rw [h2', Matrix.trace_smul, smul_eq_mul] at h1
        have : (ε - 1) * Matrix.trace (a : Matrix ι ι K) = 0 := by linear_combination h1
        have := (mul_eq_zero.1 this).resolve_right htr
        linear_combination this
      rw [hε, hε1, one_smul]
    have hne : eig (a : Matrix ι ι K) s ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hs1
      omega
    obtain ⟨v₀, hv₀L, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hLspan : ∀ x ∈ eig (a : Matrix ι ι K) s, ∃ c : K, c • v₀ = x := by
      intro x hx
      have hle : Submodule.span K {v₀} ≤ eig (a : Matrix ι ι K) s := by
        rw [Submodule.span_le]; simpa using hv₀L
      have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_singleton hv₀, hs1])
      rw [← heq] at hx
      exact Submodule.mem_span_singleton.1 hx
    have hscal : ∀ g ∈ H, ∃ c : K, c ≠ 0 ∧ (g : Matrix ι ι K) *ᵥ v₀ = c • v₀ := by
      intro g hg
      have hgL : (g : Matrix ι ι K) *ᵥ v₀ ∈ eig (a : Matrix ι ι K) s := by
        rw [mem_eig, Matrix.mulVec_mulVec, ← hcommA g hg, ← Matrix.mulVec_mulVec,
          mem_eig.1 hv₀L, Matrix.mulVec_smul]
      obtain ⟨c, hc⟩ := hLspan _ hgL
      refine ⟨c, ?_, hc.symm⟩
      rintro rfl
      rw [zero_smul] at hc
      apply hv₀
      have := congrArg (fun x => ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) hc.symm
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
    have habel : ∀ g ∈ H, ∀ g' ∈ H, (g : Matrix ι ι K) * g' = g' * g := by
      intro g hg g' hg'
      obtain ⟨ε, hε⟩ := H2 g hg g' hg'
      obtain ⟨c, hc0, hc⟩ := hscal g hg
      obtain ⟨c', hc0', hc'⟩ := hscal g' hg'
      have h1 := congrArg (fun M : Matrix ι ι K => M *ᵥ v₀) hε
      simp only [← Matrix.mulVec_mulVec, hc, hc', Matrix.smul_mulVec, Matrix.mulVec_smul,
        smul_smul] at h1
      have h3 : ((c' * c) - ε * (c * c')) • v₀ = 0 := by rw [sub_smul, h1, sub_self]
      have h4 : (c' * c) - ε * (c * c') = 0 := (smul_eq_zero.1 h3).resolve_right hv₀
      have h5 : (1 - ε) * (c * c') = 0 := by linear_combination h4
      have h6 : 1 - ε = 0 := (mul_eq_zero.1 h5).resolve_right (mul_ne_zero hc0 hc0')
      have h7 : ε = 1 := by linear_combination -h6
      rw [hε, h7, one_smul]
    have := card_le_of_abelian h2 hcard H H1 habel T hT hTnp
    omega

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
