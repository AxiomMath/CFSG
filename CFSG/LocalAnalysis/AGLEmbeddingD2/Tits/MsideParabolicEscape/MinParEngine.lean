module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.MinPar
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenYLevel

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open scoped Pointwise

variable {Y : Type} [Group Y]

structure MinParData (L S₀ : Subgroup Y) where
  ι : Type
  P : ι → Subgroup Y
  P_min : ∀ i, IsMinOverBorel L S₀ (P i)
  P_all : ∀ A, IsMinOverBorel L S₀ A → ∃ i, A = P i
  P_inj : Function.Injective P
  OV : ∀ X : Subgroup Y, S₀ ≤ X → X ≤ L → ¬ X ≤ Subgroup.normalizer (S₀ : Set Y) →
    ∃ i, pElementSubgroup 2 (P i) ≤ X
  sub : ∀ (J : Set ι) (k : ι), J.Nonempty → pElementSubgroup 2 (P k) ≤ ⨆ j ∈ J, P j → k ∈ J
  two : ∀ (J : Set ι) (a : Y), J.Nonempty → a ∈ ⨆ j ∈ J, P j → (∃ m : ℕ, orderOf a = 2 ^ m) →
    a ∈ ⨆ j ∈ J, pElementSubgroup 2 (P j)
  nonnorm : ∀ i, ¬ pElementSubgroup 2 (P i) ≤ Subgroup.normalizer (S₀ : Set Y)

theorem isMinOverBorel_conjSub {L S₀ A : Subgroup Y} {g : Y}
    (hgL : g ∈ Subgroup.normalizer (L : Set Y)) (hgS : g ∈ Subgroup.normalizer (S₀ : Set Y))
    (h : IsMinOverBorel L S₀ A) : IsMinOverBorel L S₀ (B6.conjSub g A) := by
  have hL : B6.conjSub g L = L := B6.conjSub_eq_self hgL
  have hS : B6.conjSub g S₀ = S₀ := B6.conjSub_eq_self hgS
  have hN : B6.conjSub g (Subgroup.normalizer (S₀ : Set Y)) = Subgroup.normalizer (S₀ : Set Y) := by
    have := Subgroup.map_equiv_normalizer_eq S₀ (MulAut.conj g)
    change (Subgroup.normalizer (S₀ : Set Y)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((S₀.map (MulAut.conj g).toMonoidHom : Subgroup Y) : Set Y) at this
    change (Subgroup.normalizer (S₀ : Set Y)).map (MulAut.conj g).toMonoidHom = _
    rw [this]
    change Subgroup.normalizer ((B6.conjSub g S₀ : Subgroup Y) : Set Y) = _
    rw [hS]
  have hB : B6.conjSub g (L ⊓ Subgroup.normalizer (S₀ : Set Y)) =
      L ⊓ Subgroup.normalizer (S₀ : Set Y) := by
    rw [OrderIso.map_inf, hL, hN]
  obtain ⟨hAL, hBA, hmin⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · calc B6.conjSub g A ≤ B6.conjSub g L := (B6.conjSub g).monotone hAL
      _ = L := hL
  · rw [← hB]
    exact (B6.conjSub g).lt_iff_lt.2 hBA
  · intro Q hBQ hQA
    have h1 : L ⊓ Subgroup.normalizer (S₀ : Set Y) ≤ (B6.conjSub g).symm Q := by
      rw [OrderIso.le_symm_apply, hB]; exact hBQ
    have h2 : (B6.conjSub g).symm Q ≤ A := by
      rw [OrderIso.symm_apply_le]; exact hQA
    rcases hmin _ h1 h2 with h3 | h3
    · left
      rw [← hB, ← h3, OrderIso.apply_symm_apply]
    · right
      rw [← h3, OrderIso.apply_symm_apply]


theorem conjSub_pElementSubgroup (g : Y) (A : Subgroup Y) :
    B6.conjSub g (pElementSubgroup 2 A) = pElementSubgroup 2 (B6.conjSub g A) :=
  (pElementSubgroup_map_equiv (MulAut.conj g) A).symm

theorem mem_normalizer_inf {R L : Subgroup Y} (hR : R ≤ Subgroup.normalizer (L : Set Y)) {r : Y}
    (hr : r ∈ R) : r ∈ Subgroup.normalizer ((R ⊓ L : Subgroup Y) : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 : x ∈ R ↔ r * x * r⁻¹ ∈ R :=
    ⟨fun hx => R.mul_mem (R.mul_mem hr hx) (R.inv_mem hr), fun hx => by
      have := R.mul_mem (R.mul_mem (R.inv_mem hr) hx) hr
      simpa [mul_assoc] using this⟩
  have h2 : x ∈ L ↔ r * x * r⁻¹ ∈ L := Subgroup.mem_normalizer_iff.1 (hR hr) x
  exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩

theorem exists_iSup_conjClosure {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hP : IsMinOverBorel L (R ⊓ L) P)
    (D : MinParData L (R ⊓ L)) :
    ∃ J : Set D.ι, J.Nonempty ∧ conjClosure P R = ⨆ k ∈ J, D.P k := by
  classical
  have hRS : ∀ r ∈ R, r ∈ Subgroup.normalizer ((R ⊓ L : Subgroup Y) : Set Y) := fun r hr =>
    mem_normalizer_inf hR hr
  obtain ⟨i₀, hi₀⟩ := D.P_all P hP
  have hconj : ∀ r ∈ R, ∀ j, ∃ k, B6.conjSub r (D.P j) = D.P k := fun r hr j =>
    D.P_all _ (isMinOverBorel_conjSub (hR hr) (hRS r hr) (D.P_min j))
  set J : Set D.ι := {k | ∃ r ∈ R, B6.conjSub r (D.P i₀) = D.P k} with hJ
  have hJne : J.Nonempty := ⟨i₀, 1, R.one_mem, B6.conjSub_one _⟩
  refine ⟨J, hJne, ?_⟩
  apply le_antisymm
  · refine conjClosure_le fun h hh z hz => ?_
    obtain ⟨k, hk⟩ := hconj h hh i₀
    have hkJ : k ∈ J := ⟨h, hh, hk⟩
    have hmem : h * z * h⁻¹ ∈ B6.conjSub h (D.P i₀) := by
      rw [B6.mem_conjSub]
      have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      rw [this, ← hi₀]; exact hz
    rw [hk] at hmem
    exact le_iSup₂_of_le (f := fun k (_ : k ∈ J) => D.P k) k hkJ le_rfl hmem
  · refine iSup₂_le fun k hk x hx => ?_
    obtain ⟨r, hr, hrk⟩ := hk
    rw [← hrk, B6.mem_conjSub] at hx
    have hz : r⁻¹ * x * r ∈ P := by rw [hi₀]; exact hx
    have := mem_conjClosure hr hz
    simpa [mul_assoc] using this

theorem minParabolic_of_minParData [Finite Y] {L R P : Subgroup Y}
    (hR : R ≤ Subgroup.normalizer (L : Set Y)) (hR2 : IsPGroup 2 R)
    (hS : IsSylowTwoOf (R ⊓ L) L) (hP : IsMinOverBorel L (R ⊓ L) P)
    (D : MinParData L (R ⊓ L)) :
    ∃ M : Subgroup Y, MinParabolic (pElementSubgroup 2 (conjClosure P R) ⊔ R) R M := by
  classical
  set S₀ := R ⊓ L with hS₀
  have hRS : ∀ r ∈ R, r ∈ Subgroup.normalizer (S₀ : Set Y) := fun r hr =>
    mem_normalizer_inf hR hr
  obtain ⟨i₀, hi₀⟩ := D.P_all P hP
  have hconj : ∀ r ∈ R, ∀ j, ∃ k, B6.conjSub r (D.P j) = D.P k := fun r hr j =>
    D.P_all _ (isMinOverBorel_conjSub (hR hr) (hRS r hr) (D.P_min j))
  set J : Set D.ι := {k | ∃ r ∈ R, B6.conjSub r (D.P i₀) = D.P k} with hJ
  have hJne : J.Nonempty := ⟨i₀, 1, R.one_mem, B6.conjSub_one _⟩
  have hQ : conjClosure P R = ⨆ k ∈ J, D.P k := by
    apply le_antisymm
    · refine conjClosure_le fun h hh z hz => ?_
      obtain ⟨k, hk⟩ := hconj h hh i₀
      have hkJ : k ∈ J := ⟨h, hh, hk⟩
      have hmem : h * z * h⁻¹ ∈ B6.conjSub h (D.P i₀) := by
        rw [B6.mem_conjSub]
        have : h⁻¹ * (h * z * h⁻¹) * h = z := by group
        rw [this, ← hi₀]; exact hz
      rw [hk] at hmem
      exact le_iSup₂_of_le (f := fun k (_ : k ∈ J) => D.P k) k hkJ le_rfl hmem
    · refine iSup₂_le fun k hk x hx => ?_
      obtain ⟨r, hr, hrk⟩ := hk
      rw [← hrk, B6.mem_conjSub] at hx
      have hz : r⁻¹ * x * r ∈ P := by rw [hi₀]; exact hx
      have := mem_conjClosure hr hz
      simpa [mul_assoc] using this
  set Q := conjClosure P R with hQdef
  set W := pElementSubgroup 2 Q with hW
  have hQL : Q ≤ L := by
    rw [hQ]; exact iSup₂_le fun k _ => (D.P_min k).1
  have hWL : W ≤ L := (pElementSubgroup_le Q).trans hQL
  have hRW : R ≤ Subgroup.normalizer (W : Set Y) :=
    (le_normalizer_conjClosure P R).trans
      (CFSG.AGLEmbeddingD2.GN.normalizer_le_normalizer_pElementSubgroup 2 Q)
  have hS₀B : S₀ ≤ L ⊓ Subgroup.normalizer (S₀ : Set Y) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hS₀P : S₀ ≤ D.P i₀ := by rw [← hi₀]; exact hS₀B.trans hP.2.1.le
  have hPQ : D.P i₀ ≤ Q := by rw [← hi₀]; exact le_conjClosure P R
  have hPW : pElementSubgroup 2 (D.P i₀) ≤ W :=
    Subgroup.closure_mono fun x hx => ⟨hPQ hx.1, hx.2⟩
  have hS₀W : S₀ ≤ W := by
    intro x hx
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hR2) ⟨x, hx.1⟩
    refine hPW (Subgroup.subset_closure ⟨hS₀P hx, k, ?_⟩)
    rw [← hk, ← Subgroup.orderOf_coe]
  have hSylW : IsSylowTwoOf S₀ W := B6.isSylowTwoOf_mono hS hS₀W hWL
  have hHset : (↑(W ⊔ R) : Set Y) = (W : Set Y) * (R : Set Y) :=
    Subgroup.coe_mul_of_right_le_normalizer_left W R hRW
  have hSylR : IsSylowTwoOf R (W ⊔ R) := by
    rw [A4.isSylowTwoOf_iff_maximal]
    refine ⟨le_sup_right, hR2, fun P' hP'H hP'2 hRP' => ?_⟩
    intro p hp
    have hpH : p ∈ (W : Set Y) * (R : Set Y) := by rw [← hHset]; exact hP'H hp
    obtain ⟨w, hw, r, hr, rfl⟩ := hpH
    have hwP' : w ∈ P' := by
      have := P'.mul_mem hp (P'.inv_mem (hRP' hr))
      simpa using this
    have hmax := (A4.isSylowTwoOf_iff_maximal.1 hSylW).2.2 (P' ⊓ W) inf_le_right
      (hP'2.to_le inf_le_left) (le_inf ((inf_le_left : S₀ ≤ R).trans hRP') hS₀W)
    exact R.mul_mem (hmax ⟨hwP', hw⟩).1 hr
  have hnormR : ¬ (W ⊔ R) ≤ Subgroup.normalizer (R : Set Y) := by
    intro h
    apply D.nonnorm i₀
    refine hPW.trans fun w hw => ?_
    have hwR : w ∈ Subgroup.normalizer (R : Set Y) := h ((le_sup_left : W ≤ W ⊔ R) hw)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : x ∈ R ↔ w * x * w⁻¹ ∈ R := Subgroup.mem_normalizer_iff.1 hwR x
    have h2 : x ∈ L ↔ w * x * w⁻¹ ∈ L :=
      ⟨fun hx => L.mul_mem (L.mul_mem (hWL hw) hx) (L.inv_mem (hWL hw)), fun hx => by
        have := L.mul_mem (L.mul_mem (L.inv_mem (hWL hw)) hx) (hWL hw)
        simpa [mul_assoc] using this⟩
    exact ⟨fun hx => ⟨h1.1 hx.1, h2.1 hx.2⟩, fun hx => ⟨h1.2 hx.1, h2.2 hx.2⟩⟩
  have key : ∀ X : Subgroup Y, R ≤ X → X ≤ W ⊔ R →
      ¬ X ≤ Subgroup.normalizer (S₀ : Set Y) → X = W ⊔ R := by
    intro X hRX hXH hXn
    have hS₀X : S₀ ≤ X := inf_le_left.trans hRX
    have hn : ¬ (X ⊓ W) ≤ Subgroup.normalizer (S₀ : Set Y) := by
      intro hle
      apply hXn
      intro x hx
      have hxH : x ∈ (W : Set Y) * (R : Set Y) := by rw [← hHset]; exact hXH hx
      obtain ⟨w, hw, r, hr, rfl⟩ := hxH
      have hwX : w ∈ X := by
        have := X.mul_mem hx (X.inv_mem (hRX hr))
        simpa using this
      exact (Subgroup.normalizer (S₀ : Set Y)).mul_mem (hle ⟨hwX, hw⟩) (hRS r hr)
    obtain ⟨k, hk⟩ := D.OV (X ⊓ W) (le_inf hS₀X hS₀W) (inf_le_right.trans hWL) hn
    have hkJ : k ∈ J := by
      refine D.sub J k hJne ?_
      rw [← hQ]
      exact (hk.trans inf_le_right).trans (pElementSubgroup_le Q)
    have hall : ∀ j ∈ J, pElementSubgroup 2 (D.P j) ≤ X ⊓ W := by
      intro j hj
      obtain ⟨r₁, hr₁, h₁⟩ := hkJ
      obtain ⟨r₂, hr₂, h₂⟩ := hj
      set g := r₂ * r₁⁻¹ with hg
      have hgR : g ∈ R := R.mul_mem hr₂ (R.inv_mem hr₁)
      have hjk : B6.conjSub g (D.P k) = D.P j := by
        rw [← h₁, ← h₂, ← B6.conjSub_mul, hg, mul_assoc, inv_mul_cancel, mul_one]
      have hpe : pElementSubgroup 2 (D.P j) = B6.conjSub g (pElementSubgroup 2 (D.P k)) := by
        rw [conjSub_pElementSubgroup, hjk]
      rw [hpe]
      intro x hx
      rw [B6.mem_conjSub] at hx
      have hy := hk hx
      have hxy : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      have hgX : g ∈ X := hRX hgR
      refine ⟨?_, ?_⟩
      · rw [hxy]; exact X.mul_mem (X.mul_mem hgX hy.1) (X.inv_mem hgX)
      · rw [hxy]
        exact (Subgroup.mem_normalizer_iff.1 (hRW hgR) _).1 hy.2
    have hWX : W ≤ X := by
      rw [hW, pElementSubgroup, Subgroup.closure_le]
      rintro x ⟨hxQ, hx2⟩
      have hx' := D.two J x hJne (by rw [← hQ]; exact hxQ) hx2
      exact (iSup₂_le fun j hj => (hall j hj).trans inf_le_left) hx'
    exact le_antisymm hXH (sup_le hWX hRX)
  have hHn : ¬ (W ⊔ R) ≤ Subgroup.normalizer (S₀ : Set Y) := fun h =>
    D.nonnorm i₀ (hPW.trans (le_sup_left.trans h))
  have hRM : R ≤ (W ⊔ R) ⊓ Subgroup.normalizer (S₀ : Set Y) := le_inf le_sup_right hRS
  have hmax : IsMaxSubgroupIn (W ⊔ R) ((W ⊔ R) ⊓ Subgroup.normalizer (S₀ : Set Y)) := by
    refine ⟨lt_of_le_of_ne inf_le_left fun h => hHn (h ▸ inf_le_right), fun K hMK hKH => ?_⟩
    refine key K (hRM.trans hMK.le) hKH fun hle => ?_
    exact absurd (le_inf hKH hle) (not_le_of_gt hMK)
  refine ⟨(W ⊔ R) ⊓ Subgroup.normalizer (S₀ : Set Y), hSylR, hnormR,
    isUniqueMaxOver_iff.2 ⟨hmax, hRM, fun N' hN' hRN' => ?_⟩⟩
  by_cases hle : N' ≤ Subgroup.normalizer (S₀ : Set Y)
  · have hNM : N' ≤ (W ⊔ R) ⊓ Subgroup.normalizer (S₀ : Set Y) := le_inf hN'.1.le hle
    by_contra hne
    exact hmax.1.ne (hN'.2 _ (lt_of_le_of_ne hNM hne) hmax.1.le)
  · exact absurd (key N' hRN' hN'.1.le hle) hN'.1.ne

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
