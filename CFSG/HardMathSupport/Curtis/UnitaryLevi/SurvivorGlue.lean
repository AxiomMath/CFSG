module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorChain
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.SurvivorReindex
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.FixedSpacePerfect

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n q : ℕ}

@[expose] noncomputable def suToGL (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K →* LinearMap.GeneralLinearGroup K (Fin n → K) :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := K)).toMonoidHom.comp
    (StatedSU n q K).subtype

theorem suToGL_apply (y : StatedSU n q K) (v : Fin n → K) :
    ((suToGL n q K y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v = ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v := rfl

theorem suToGL_injective : Function.Injective (suToGL n q K) := fun _ _ hxy =>
  Subtype.ext (Matrix.GeneralLinearGroup.toLin.injective hxy)

theorem suToGL_isometry {f : ℕ} (h : UnitaryFieldData 2 f K) (y : StatedSU n (2 ^ f) K)
    (v w : Fin n → K) :
    stdHermForm h n (((suToGL n (2 ^ f) K y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) v)
      (((suToGL n (2 ^ f) K y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) w) = stdHermForm h n v w := by
  rw [suToGL_apply, suToGL_apply]
  exact ((mem_unitarySU_iff_isometry h).mp y.2).2 v w

structure SUChain (h : UnitaryFieldData 2 1 K) (n : ℕ) (Dt : Subgroup (StatedSU n (2 ^ 1) K))
    (S : Finset ℕ) (a : ℕ → ℕ) (W : ℕ → Submodule K (Fin n → K)) : Prop where
  enum : Enumeration S a
  ne : S.Nonempty
  mono : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → W i ≤ W j
  dim : ∀ i ∈ S, finrank K (W i) = i
  iso : ∀ i ∈ S, ∀ v ∈ W i, ∀ w ∈ W i, stdHermForm h n v w = 0
  stab : ∀ y ∈ Dt, ∀ i ∈ S, ∀ w ∈ W i, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W i
  perf : ⁅Dt, Dt⁆ = Dt

variable {h : UnitaryFieldData 2 1 K} {Dt : Subgroup (StatedSU n (2 ^ 1) K)} {S : Finset ℕ}
  {a : ℕ → ℕ} {W : ℕ → Submodule K (Fin n → K)}

namespace SUChain

noncomputable abbrev delta (Dt : Subgroup (StatedSU n (2 ^ 1) K)) :
    Subgroup (LinearMap.GeneralLinearGroup K (Fin n → K)) := Dt.map (suToGL n (2 ^ 1) K)

theorem perf_delta (hc : SUChain h n Dt S a W) : ⁅delta Dt, delta Dt⁆ = delta Dt := by
  rw [delta, ← Subgroup.map_commutator, hc.perf]

theorem delta_iso (d : LinearMap.GeneralLinearGroup K (Fin n → K)) (hd : d ∈ delta Dt)
    (v w : Fin n → K) :
    stdHermForm h n ((d : Module.End K (Fin n → K)) v) ((d : Module.End K (Fin n → K)) w) =
      stdHermForm h n v w := by
  obtain ⟨y, -, rfl⟩ := hd
  exact suToGL_isometry h y v w

theorem delta_stab (hc : SUChain h n Dt S a W) (d : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hd : d ∈ delta Dt) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ S.card) (v : Fin n → K)
    (hv : v ∈ reindexChain a S.card W j) : (d : Module.End K (Fin n → K)) v ∈
      reindexChain a S.card W j := by
  obtain ⟨y, hy, rfl⟩ := hd
  rw [reindexChain_of_le a W hj1 hj2] at hv ⊢
  exact hc.stab y hy _ (hc.enum.mem j hj1 hj2) v hv

theorem iso_reindex (hc : SUChain h n Dt S a W) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ S.card) :
    ∀ v ∈ reindexChain a S.card W j, ∀ w ∈ reindexChain a S.card W j, stdHermForm h n v w = 0 := by
  rw [reindexChain_of_le a W hj1 hj2]
  exact hc.iso _ (hc.enum.mem j hj1 hj2)

theorem delta_stab' (hc : SUChain h n Dt S a W) (d : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hd : d ∈ delta Dt) (j : ℕ) (hj : j ≤ S.card) (v : Fin n → K)
    (hv : v ∈ reindexChain a S.card W j) : (d : Module.End K (Fin n → K)) v ∈
      reindexChain a S.card W j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [reindexChain_zero, Submodule.mem_bot] at hv ⊢
    simp [hv]
  · exact hc.delta_stab d hd j hj0 hj v hv

theorem delta_trivial_on_line (hc : SUChain h n Dt S a W) {j : ℕ}
    (hj1 : 1 ≤ j) (hj2 : j ≤ S.card) (hline : a j = a (j - 1) + 1) :
    ∀ d ∈ delta Dt, ∀ v ∈ reindexChain a S.card W j,
      (d : Module.End K (Fin n → K)) v - v ∈ reindexChain a S.card W (j - 1) := by
  have h1 : finrank K (PieceQ (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j)) = 1 := by
    rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hj1 hj2]
    omega
  exact perfect_trivial_on_line_piece h1 (delta Dt) hc.perf_delta
    (fun d hd v hv => hc.delta_stab' d hd (j - 1) (by omega) v hv)
    (fun d hd v hv => hc.delta_stab' d hd j hj2 v hv)

theorem finrank_tail_eq (hc : SUChain h n Dt S a W) :
    finrank K (PieceQ (reindexChain a S.card W S.card)
      ((reindexChain a S.card W S.card).orthogonalBilin (stdHermForm h n))) = n - 2 * a S.card := by
  have := finrank_tail_reindexChain (K := K) (V := Fin n → K) (B := stdHermForm h n)
    (fun c => ⟨h.bar c, h.bar_bar c⟩) (stdHermForm_separatingLeft h n) hc.enum hc.ne hc.dim hc.iso
  rw [this, Module.finrank_fin_fun]

theorem delta_trivial_on_tail (hc : SUChain h n Dt S a W) (htail : n - 2 * a S.card ≤ 3) :
    ∀ d ∈ delta Dt, ∀ v ∈ (reindexChain a S.card W S.card).orthogonalBilin (stdHermForm h n),
      (d : Module.End K (Fin n → K)) v - v ∈ reindexChain a S.card W S.card := by
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have := h.charP
  exact isometry_perfect_trivial_on_tail' h (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n)
    (hc.iso_reindex S.card hs le_rfl) (by rw [hc.finrank_tail_eq]; exact htail) (delta Dt)
    (fun d hd => ⟨fun v w => delta_iso d hd v w, fun v hv => hc.delta_stab' d hd S.card le_rfl v hv⟩)
    hc.perf_delta

theorem eq_one_of_gaps_one [Finite K] (hc : SUChain h n Dt S a W)
    (hgap : ∀ k, 1 ≤ k → k ≤ S.card → a k = a (k - 1) + 1) (htail : n - 2 * a S.card ≤ 3) :
    ∀ y ∈ Dt, y = 1 := by
  have := h.charP
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have h2 : ∀ d ∈ delta Dt, ∃ k, d ^ 2 ^ k = 1 :=
    exists_pow_two_pow_eq_one_of_lines h (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n)
      hs (reindexChain_zero a S.card W) (fun j hj1 hj2 => hc.iso_reindex j hj1 hj2) (delta Dt)
      hc.perf_delta (fun d hd v w => delta_iso d hd v w)
      (fun d hd j hj1 hj2 v hv => hc.delta_stab d hd j hj1 hj2 v hv)
      (fun j hj1 hj2 => by
        rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hj1 hj2]
        have := hgap j hj1 hj2
        omega)
      (by rw [hc.finrank_tail_eq]; exact htail)
  have hp : IsPGroup 2 Dt := by
    intro y
    obtain ⟨k, hk⟩ := h2 (suToGL n (2 ^ 1) K y) ⟨y, y.2, rfl⟩
    refine ⟨k, Subtype.ext (suToGL_injective ?_)⟩
    rw [← map_pow] at hk
    simpa using hk
  have : Finite Dt := inferInstance
  have hnil : Group.IsNilpotent Dt := hp.isNilpotent
  have hperf : Group.IsPerfect Dt := Subgroup.isPerfect_iff.mpr hc.perf
  intro y hy
  by_contra hne
  have : Nontrivial Dt := ⟨⟨⟨y, hy⟩, 1, fun e => hne (congrArg Subtype.val e)⟩⟩
  exact Group.IsPerfect.not_isSolvable (G := Dt) inferInstance

theorem fixed_space_dim_of_plane_piece (hc : SUChain h n Dt S a W) {k₀ : ℕ} (hk1 : 1 ≤ k₀)
    (hk2 : k₀ ≤ S.card) (hplane : a k₀ = a (k₀ - 1) + 2)
    (hother : ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1)
    (htail : n - 2 * a S.card ≤ 3) {x : StatedSU n (2 ^ 1) K} (hx : x ∈ Dt)
    (hx3 : ((x : GL (Fin n) K)) ^ 3 = 1) :
    n - 4 ≤ finrank K (LinearMap.ker (Matrix.mulVecLin
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1))) := by
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have hx3' : (suToGL n (2 ^ 1) K x) ^ 3 = 1 := by
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, this, map_one]
  have key := fixed_space_dim_of_perfect h (stdHermForm_isSymm h n) (stdHermForm_separatingLeft h n)
    hs (reindexChain_zero a S.card W) (reindexChain_mono hc.enum hc.mono)
    (fun j hj1 hj2 => hc.iso_reindex j hj1 hj2) (delta Dt) hc.perf_delta
    (fun d hd v w => delta_iso d hd v w)
    (fun d hd j hj1 hj2 v hv => hc.delta_stab d hd j hj1 hj2 v hv)
    (x := suToGL n (2 ^ 1) K x) ⟨x, hx, rfl⟩ hx3' hk1 hk2
    (by rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hk1 hk2]; omega)
    (fun j hj1 hj2 hne => by
      rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hj1 hj2]
      have := hother j hj1 hj2 hne
      omega)
    (by rw [hc.finrank_tail_eq]; exact htail)
  rw [Module.finrank_fin_fun] at key
  have hker : LinearMap.ker (((suToGL n (2 ^ 1) K x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) - 1) = LinearMap.ker (Matrix.mulVecLin
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)) := by
    congr 1
    ext v i
    simp [suToGL_apply]
  rwa [hker] at key

theorem cube_scalar_eq_one (hc : SUChain h n Dt S a W) {k₀ : ℕ} 
    (hother : ∀ k, 1 ≤ k → k ≤ S.card → k ≠ k₀ → a k = a (k - 1) + 1)
    (htail : n - 2 * a S.card ≤ 3) (hbig : 2 ≤ S.card ∨ 0 < n - 2 * a S.card)
    {x : StatedSU n (2 ^ 1) K} (hx : x ∈ Dt) {c : K}
    (hcx : ∀ v, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)) = c • v) : c = 1 := by
  have hs : 1 ≤ S.card := Finset.card_pos.mpr hc.ne
  have hxΔ : suToGL n (2 ^ 1) K x ∈ delta Dt := ⟨x, hx, rfl⟩
  have hcx' : ∀ v, ((suToGL n (2 ^ 1) K x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))
      (((suToGL n (2 ^ 1) K x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K))
      (((suToGL n (2 ^ 1) K x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) v)) = c • v := hcx
  rcases hbig with h2 | h0
  ·
    obtain ⟨j, hj1, hj2, hjne⟩ : ∃ j, 1 ≤ j ∧ j ≤ S.card ∧ j ≠ k₀ := by
      by_cases hk : k₀ = 1
      · exact ⟨2, by omega, h2, by omega⟩
      · exact ⟨1, le_rfl, hs, by omega⟩
    have hline := hother j hj1 hj2 hjne
    have hp : 0 < finrank K (PieceQ (reindexChain a S.card W (j - 1)) (reindexChain a S.card W j)) := by
      rw [finrank_pieceQ_reindexChain hc.enum hc.mono hc.dim hj1 hj2]
      omega
    obtain ⟨v, hv, hvF⟩ := exists_mem_not_mem_of_finrank_pieceQ_pos hp
    exact scalar_cube_eq_one_of_trivial_piece
      (fun w hw => hc.delta_stab' _ hxΔ (j - 1) (by omega) w hw)
      (fun w hw => delta_trivial_on_line hc hj1 hj2 hline _ hxΔ w hw) hcx' hv hvF
  · have hp : 0 < finrank K (PieceQ (reindexChain a S.card W S.card)
        ((reindexChain a S.card W S.card).orthogonalBilin (stdHermForm h n))) := by
      rw [hc.finrank_tail_eq]
      exact h0
    obtain ⟨v, hv, hvF⟩ := exists_mem_not_mem_of_finrank_pieceQ_pos hp
    exact scalar_cube_eq_one_of_trivial_piece
      (fun w hw => hc.delta_stab' _ hxΔ S.card le_rfl w hw)
      (fun w hw => delta_trivial_on_tail hc htail _ hxΔ w hw) hcx' hv hvF

end SUChain

end CFSG.HardMathSupport.Curtis.UnitaryLevi
