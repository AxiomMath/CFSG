module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseBClifford

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

variable {K : Type} [Field K] {p : ℕ}

theorem exists_ne_zero_col {M : Matrix (Fin p) (Fin p) K} (hM : IsUnit M) (j : Fin p) :
    ∃ a, M a j ≠ 0 := by
  by_contra h
  push Not at h
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hM
  have h1 : M *ᵥ Pi.single j 1 = M *ᵥ 0 := by
    rw [Matrix.mulVec_single_one, Matrix.mulVec_zero]
    ext a
    exact h a
  have h2 := congrFun (hinj h1) j
  simp at h2

theorem exists_ne_zero_row {M : Matrix (Fin p) (Fin p) K} (hM : IsUnit M) (j : Fin p) :
    ∃ b, M j b ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_ne_zero_col ((Matrix.isUnit_transpose M).2 hM) j
  exact ⟨b, hb⟩

theorem eq_zero_of_comm_mod_scalar {ζ : K} (hζ0 : ζ ≠ 0) (hζ1 : ζ ≠ 1) (hζ2 : ζ ^ 2 ≠ 1)
    {M : Matrix (Fin p) (Fin p) K} (hM : IsUnit M)
    (h : ∀ j : Fin p, ∃ c : K, ∀ a b : Fin p,
      M a b * (if b = j then ζ else 1) = c * ((if a = j then ζ else 1) * M a b)) :
    ∀ a b : Fin p, a ≠ b → M a b = 0 := by
  have key : ∀ j : Fin p, ∀ c : K, (∀ a b : Fin p,
      M a b * (if b = j then ζ else 1) = c * ((if a = j then ζ else 1) * M a b)) →
      ∀ a, a ≠ j → M a j = 0 := by
    intro j c hc
    have f1 : ∀ a, a ≠ j → M a j * (ζ - c) = 0 := by
      intro a ha
      have := hc a j
      simp only [if_true, if_neg ha] at this
      linear_combination this
    have f2 : M j j * (ζ * (1 - c)) = 0 := by
      have := hc j j
      simp only [if_true] at this
      linear_combination this
    have f3 : ∀ a b, a ≠ j → b ≠ j → M a b * (1 - c) = 0 := by
      intro a b ha hb
      have := hc a b
      simp only [if_neg ha, if_neg hb] at this
      linear_combination this
    have f4 : ∀ b, b ≠ j → M j b * (1 - c * ζ) = 0 := by
      intro b hb
      have := hc j b
      simp only [if_true, if_neg hb] at this
      linear_combination this
    by_cases hc1 : c = 1
    · subst hc1
      intro a ha
      have := f1 a ha
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.1 h0) hζ1
    · exfalso
      have h1c : (1 - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hc1)
      have hMjj : M j j = 0 := by
        rcases mul_eq_zero.1 f2 with h0 | h0
        · exact h0
        · rcases mul_eq_zero.1 h0 with h1 | h1
          · exact absurd h1 hζ0
          · exact absurd h1 h1c
      by_cases hcz : c = ζ
      · obtain ⟨b, hb⟩ := exists_ne_zero_row hM j
        by_cases hbj : b = j
        · subst hbj
          exact hb hMjj
        · have h1 : (1 - c * ζ) ≠ 0 := by
            rw [hcz]
            intro h0
            exact hζ2 (by linear_combination -h0)
          rcases mul_eq_zero.1 (f4 b hbj) with h0 | h0
          · exact hb h0
          · exact h1 h0
      · obtain ⟨a, ha⟩ := exists_ne_zero_col hM j
        by_cases haj : a = j
        · subst haj
          exact ha hMjj
        · have h1 : (ζ - c) ≠ 0 := sub_ne_zero.2 (Ne.symm hcz)
          rcases mul_eq_zero.1 (f1 a haj) with h0 | h0
          · exact ha h0
          · exact h1 h0
  intro a b hab
  obtain ⟨c, hc⟩ := h b
  exact key b c hc a hab


section Centralizer

variable {G : Subgroup (GL (Fin p) K)} {ŷ B : GL (Fin p) K}

@[expose] def IsDiagGL (x : GL (Fin p) K) : Prop :=
  ∀ i j : Fin p, i ≠ j → (x : Matrix (Fin p) (Fin p) K) i j = 0

theorem isDiagGL_diagGL (d : Fin p → Kˣ) : IsDiagGL (diagGL p K d) := by
  intro i j hij
  rw [diagGL_val, Matrix.diagonal_apply_ne _ hij]

theorem IsDiagGL.comm {x y : GL (Fin p) K} (hx : IsDiagGL x) (hy : IsDiagGL y) :
    x * y = y * x := by
  have hd : ∀ z : GL (Fin p) K, IsDiagGL z →
      ∃ e : Fin p → K, (z : Matrix (Fin p) (Fin p) K) = Matrix.diagonal e := by
    intro z hz
    refine ⟨fun i => (z : Matrix (Fin p) (Fin p) K) i i, ?_⟩
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.diagonal_apply_ne _ h]
      exact hz i j h
  obtain ⟨ex, hex⟩ := hd x hx
  obtain ⟨ey, hey⟩ := hd y hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hex, hey, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem isDiagGL_of_mem_centralizer (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d) {g : GL (Fin p) K}
    (hg : g ∈ centralizer (G : Set (GL (Fin p) K))) : IsDiagGL (B⁻¹ * g * B) := by
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin p) K, X = B⁻¹ * g * B := ⟨_, rfl⟩
  rw [← hX]
  intro i j hij
  obtain ⟨t, ht, hne⟩ := hsep i j hij
  obtain ⟨d, hd⟩ := hdiag t ht
  have hcomm : (B⁻¹ * t * B) * X = X * (B⁻¹ * t * B) := by
    have := Subgroup.mem_centralizer_iff.1 hg t ht
    rw [hX]
    calc (B⁻¹ * t * B) * (B⁻¹ * g * B) = B⁻¹ * (t * g) * B := by group
      _ = B⁻¹ * (g * t) * B := by rw [this]
      _ = _ := by group
  rw [hd] at hcomm hne
  have h2 := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K) i j) hcomm
  simp only [Units.val_mul, diagGL_val, Matrix.diagonal_mul, Matrix.mul_diagonal] at h2
  simp only [diagGL_val, Matrix.diagonal_apply_eq] at hne
  have h3 : (X : Matrix (Fin p) (Fin p) K) i j * ((d j : K) - (d i : K)) = 0 := by
    linear_combination -h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact h4
  · exact absurd (sub_eq_zero.1 h4).symm hne

theorem mem_centralizer_iff (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d) {g : GL (Fin p) K} :
    g ∈ centralizer (G : Set (GL (Fin p) K)) ↔ IsDiagGL (B⁻¹ * g * B) := by
  refine ⟨isDiagGL_of_mem_centralizer hsep hdiag, fun hg => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  obtain ⟨d, hd⟩ := hdiag t ht
  have h1 : (B⁻¹ * t * B) * (B⁻¹ * g * B) = (B⁻¹ * g * B) * (B⁻¹ * t * B) := by
    rw [hd]
    exact (isDiagGL_diagGL d).comm hg
  calc t * g = B * ((B⁻¹ * t * B) * (B⁻¹ * g * B)) * B⁻¹ := by group
    _ = B * ((B⁻¹ * g * B) * (B⁻¹ * t * B)) * B⁻¹ := by rw [h1]
    _ = g * t := by group

theorem centralizer_commute (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d) {g h : GL (Fin p) K}
    (hg : g ∈ centralizer (G : Set (GL (Fin p) K)))
    (hh : h ∈ centralizer (G : Set (GL (Fin p) K))) : g * h = h * g := by
  have h1 := (mem_centralizer_iff hsep hdiag).1 hg
  have h2 := (mem_centralizer_iff hsep hdiag).1 hh
  have h3 := IsDiagGL.comm h1 h2
  calc g * h = B * ((B⁻¹ * g * B) * (B⁻¹ * h * B)) * B⁻¹ := by group
    _ = B * ((B⁻¹ * h * B) * (B⁻¹ * g * B)) * B⁻¹ := by rw [h3]
    _ = h * g := by group

theorem scalar_comm (c : Kˣ) (x : GL (Fin p) K) :
    GeneralLinearGroup.scalar (Fin p) c * x = x * GeneralLinearGroup.scalar (Fin p) c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r' => Commute.all _ _) _).eq

theorem mem_centralizer_of_comm_mod_scalar (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d)
    {𝔾 : Subgroup (GL (Fin p) K)} (hBG : B ∈ 𝔾) {ζ : Kˣ} (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ^ 2 ≠ 1) (hζG : ∀ j : Fin p, diagGL p K (Pi.mulSingle j ζ) ∈ 𝔾)
    {g : GL (Fin p) K}
    (h : ∀ d ∈ 𝔾, d ∈ centralizer (G : Set (GL (Fin p) K)) → d ^ p = 1 →
      ∃ c : Kˣ, g * d * g⁻¹ * d⁻¹ = GeneralLinearGroup.scalar (Fin p) c) :
    g ∈ centralizer (G : Set (GL (Fin p) K)) := by
  rw [mem_centralizer_iff hsep hdiag]
  obtain ⟨X, hX⟩ : ∃ X : GL (Fin p) K, X = B⁻¹ * g * B := ⟨_, rfl⟩
  rw [← hX]
  have hMu : IsUnit (X : Matrix (Fin p) (Fin p) K) := Units.isUnit _
  refine eq_zero_of_comm_mod_scalar (ζ := (ζ : K)) ζ.ne_zero ?_ ?_ hMu ?_
  · intro h1
    exact hζ1 (Units.ext h1)
  · intro h1
    exact hζ2 (Units.ext (by simpa using h1))
  · intro j
    set Dj : GL (Fin p) K := diagGL p K (Pi.mulSingle j ζ) with hDj
    set dj : GL (Fin p) K := B * Dj * B⁻¹ with hdj
    have hdjG : dj ∈ 𝔾 := mul_mem (mul_mem hBG (hζG j)) (inv_mem hBG)
    have hdjC : dj ∈ centralizer (G : Set (GL (Fin p) K)) := by
      rw [mem_centralizer_iff hsep hdiag]
      have : B⁻¹ * dj * B = Dj := by rw [hdj]; group
      rw [this]
      exact isDiagGL_diagGL _
    have hdjp : dj ^ p = 1 := by
      have h1 : Dj ^ p = 1 := by
        rw [hDj, ← map_pow, ← Pi.mulSingle_pow, hζp, Pi.mulSingle_one, map_one]
      calc dj ^ p = B * Dj ^ p * B⁻¹ := by rw [hdj, conj_pow]
        _ = 1 := by rw [h1]; group
    obtain ⟨c, hc⟩ := h dj hdjG hdjC hdjp
    refine ⟨(c : K), fun a b => ?_⟩
    obtain ⟨s, hs⟩ : ∃ s : GL (Fin p) K, s = GeneralLinearGroup.scalar (Fin p) c := ⟨_, rfl⟩
    rw [← hs] at hc
    have h1 : g * dj = s * (dj * g) := by
      calc g * dj = (g * dj * g⁻¹ * dj⁻¹) * (dj * g) := by group
        _ = _ := by rw [hc]
    have hsB : s * B⁻¹ = B⁻¹ * s := by rw [hs]; exact scalar_comm c B⁻¹
    have h2 : X * Dj = s * (Dj * X) := by
      calc X * Dj = B⁻¹ * (g * dj) * B := by rw [hX, hdj]; group
        _ = B⁻¹ * (s * (dj * g)) * B := by rw [h1]
        _ = (B⁻¹ * s) * (dj * g) * B := by group
        _ = (s * B⁻¹) * (dj * g) * B := by rw [hsB]
        _ = s * (B⁻¹ * (dj * g) * B) := by group
        _ = s * (Dj * X) := by rw [hX, hdj]; group
    have h3 := congrArg (fun x : GL (Fin p) K => (x : Matrix (Fin p) (Fin p) K) a b) h2
    simp only [Units.val_mul, hDj, diagGL_val, hs, GeneralLinearGroup.coe_scalar,
      Matrix.mul_diagonal, Matrix.scalar_apply, Matrix.diagonal_mul] at h3
    have e1 : ∀ k : Fin p, (((Pi.mulSingle j ζ : Fin p → Kˣ) k : Kˣ) : K) =
        if k = j then (ζ : K) else 1 := by
      intro k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [Pi.mulSingle_eq_of_ne hk, hk]
    simp only [e1] at h3
    exact h3

end Centralizer


section Normalizer

variable {G : Subgroup (GL (Fin p) K)} {ŷ B : GL (Fin p) K}

theorem map_monoQ_le_normalizer
    (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d)
    (hrot : ∃ δ : Fin p → Kˣ, B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) (Q : Subgroup Kˣ) :
    (monoQ (p := p) (K := K) Q).map (MulAut.conj B).toMonoidHom ≤
      normalizer (G : Set (GL (Fin p) K)) := by
  rw [monoQ, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨c, rfl⟩ := hm
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff hsep hdiag]
    have : B⁻¹ * ((MulAut.conj B).toMonoidHom (diagQ Q c)) * B = diagQ Q c := by
      show B⁻¹ * (B * diagQ Q c * B⁻¹) * B = diagQ Q c
      group
    rw [this]
    exact isDiagGL_diagGL _
  · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    obtain ⟨δ, hδ⟩ := hrot
    have hrot' : rotGL p K = (B⁻¹ * ŷ * B) * (diagGL p K δ)⁻¹ := by
      rw [hδ]
      group
    have e : (MulAut.conj B).toMonoidHom (rotGL p K) = ŷ * (B * (diagGL p K δ)⁻¹ * B⁻¹) := by
      show B * rotGL p K * B⁻¹ = _
      rw [hrot']
      group
    have hmemC : B * (diagGL p K δ)⁻¹ * B⁻¹ ∈ centralizer (G : Set (GL (Fin p) K)) := by
      rw [mem_centralizer_iff hsep hdiag]
      have : B⁻¹ * (B * (diagGL p K δ)⁻¹ * B⁻¹) * B = diagGL p K δ⁻¹ := by
        rw [map_inv]
        group
      rw [this]
      exact isDiagGL_diagGL _
    rw [e]
    exact mul_mem hyN (Subgroup.centralizer_le_normalizer _ hmemC)

theorem not_dvd_index_normalizer [Finite K] [Fact p.Prime] (hp2 : p ≠ 2)
    (hsep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
        ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j)
    (hdiag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d)
    (hrot : ∃ δ : Fin p → Kˣ, B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ)
    (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) (Q : Sylow p Kˣ)
    (hpK : p ∣ Nat.card K - 1) :
    ¬ p ∣ (normalizer (G : Set (GL (Fin p) K))).index := by
  intro hdvd
  have h1 := map_monoQ_le_normalizer hsep hdiag hrot hyN (Q : Subgroup Kˣ)
  have h2 := Subgroup.index_dvd_of_le h1
  have h3 : ((monoQ (p := p) (K := K) (Q : Subgroup Kˣ)).map
      (MulAut.conj B).toMonoidHom).index = (monoQ (p := p) (K := K) (Q : Subgroup Kˣ)).index :=
    Subgroup.index_map_of_bijective (MulAut.conj B).bijective _
  rw [h3] at h2
  exact not_dvd_index_monoQ hp2 Q hpK (hdvd.trans h2)

end Normalizer


structure DiagData (G : Subgroup (GL (Fin p) K)) (ŷ B : GL (Fin p) K) : Prop where
  rot : ∃ δ : Fin p → Kˣ, B⁻¹ * ŷ * B = rotGL p K * diagGL p K δ
  diag : ∀ g ∈ G, ∃ d : Fin p → Kˣ, B⁻¹ * g * B = diagGL p K d
  sep : ∀ i j : Fin p, i ≠ j → ∃ g ∈ G,
    ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) i i ≠
      ((B⁻¹ * g * B : GL (Fin p) K) : Matrix (Fin p) (Fin p) K) j j

theorem exists_diagData [Finite K] {G : Subgroup (GL (Fin p) K)} {ŷ : GL (Fin p) K}
    (hp : p.Prime) (hp2 : p ≠ 2) (hG2 : IsPGroup 2 G) (hGne : G ≠ ⊥)
    (hdet : ∀ g ∈ G, (g : Matrix (Fin p) (Fin p) K).det = 1) {ω : K}
    (hy : (ŷ : Matrix (Fin p) (Fin p) K) ^ p = Matrix.scalar (Fin p) ω)
    (hω : ∀ b : K, b ^ p ≠ ω) (hyN : ŷ ∈ normalizer (G : Set (GL (Fin p) K))) :
    ∃ B : GL (Fin p) K, DiagData G ŷ B := by
  obtain ⟨B, δ, hrot, -, hdiag, hsep⟩ := exists_diag_basis hp hp2 hG2 hGne hdet hy hω hyN
  exact ⟨B, ⟨δ, hrot⟩, hdiag, hsep⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
