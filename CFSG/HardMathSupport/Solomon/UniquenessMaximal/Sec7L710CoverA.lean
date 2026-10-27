module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {H H' : Type} [Group H] [Group H'] {f : H →* H'} {T₁ : Subgroup H}

theorem eq_of_map_eq_of_mem (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) {x y : H} (hx : x ∈ T₁)
    (hy : y ∈ T₁) (h : f x = f y) : x = y := by
  have h1 : f (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  exact inv_mul_eq_one.mp (hinj _ (mul_mem (inv_mem hx) hy) h1)

theorem isElemAbelian_map_iff (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) {p : ℕ} {E : Subgroup H}
    (hE : E ≤ T₁) : IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  refine ⟨fun h => ?_, fun h => CFSG.SectionRank.isElemAbelian_map h f⟩
  have hc := h.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · have h1 := mul_comm' (⟨f a, Subgroup.mem_map_of_mem f a.2⟩ : ↥(E.map f))
      ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    have h2 : f ((a : H) * b) = f ((b : H) * a) := by
      rw [map_mul, map_mul]; exact congrArg Subtype.val h1
    exact Subtype.ext (eq_of_map_eq_of_mem hinj (mul_mem (hE a.2) (hE b.2))
      (mul_mem (hE b.2) (hE a.2)) h2)
  · have h1 := h.2 (f x) (Subgroup.mem_map_of_mem f hx)
    rw [← map_pow] at h1
    exact hinj _ (pow_mem (hE hx) p) h1

theorem card_map_of_le (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) {E : Subgroup H} (hE : E ≤ T₁) :
    Nat.card (E.map f) = Nat.card E := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : E => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : E.map f)) ⟨fun a b hab => ?_, ?_⟩)
  · exact Subtype.ext (eq_of_map_eq_of_mem hinj (hE a.2) (hE b.2) (congrArg Subtype.val hab))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem exists_le_map_eq {E' : Subgroup H'} (h : E' ≤ T₁.map f) :
    ∃ E : Subgroup H, E ≤ T₁ ∧ E.map f = E' := by
  refine ⟨E'.comap f ⊓ T₁, inf_le_right, ?_⟩
  ext y
  constructor
  · rintro ⟨x, ⟨hx1, _⟩, rfl⟩
    exact hx1
  · intro hy
    obtain ⟨x, hx, rfl⟩ := h hy
    exact ⟨x, ⟨hy, hx⟩, rfl⟩

variable [Finite H] [Finite H']

theorem pRank_map_eq (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (T₁.map f) = CFSG.Open.pRank p T₁ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨E', hE'T, hE', hcard⟩ := CFSG.SectionRank.exists_pRank hp (T₁.map f)
    obtain ⟨E, hET, rfl⟩ := exists_le_map_eq hE'T
    refine CFSG.SectionRank.le_pRank hp hET ((isElemAbelian_map_iff hinj hET).1 hE') ?_
    rw [← card_map_of_le hinj hET, hcard]
  · obtain ⟨E, hET, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp T₁
    exact CFSG.SectionRank.le_pRank hp (Subgroup.map_mono hET)
      (CFSG.SectionRank.isElemAbelian_map hE f) (k := CFSG.Open.pRank p T₁)
      (by rw [card_map_of_le hinj hET, hcard])

theorem jOf_map (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) : jOf (T₁.map f) = (jOf T₁).map f := by
  have hr := pRank_map_eq hinj (p := 2) Nat.one_lt_two
  unfold jOf
  simp only [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun E' hE' => ?_
    obtain ⟨E, hET, rfl⟩ := exists_le_map_eq hE'.1
    refine le_iSup₂_of_le E ⟨hET, (isElemAbelian_map_iff hinj hET).1 hE'.2.1, ?_⟩ le_rfl
    rw [← card_map_of_le hinj hET, hE'.2.2, hr]
  · refine iSup₂_le fun E hE => ?_
    refine le_iSup₂_of_le (E.map f) ⟨Subgroup.map_mono hE.1,
      CFSG.SectionRank.isElemAbelian_map hE.2.1 f, ?_⟩ le_rfl
    rw [card_map_of_le hinj hE.1, hE.2.2, hr]

theorem jOneOf_map (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) :
    jOneOf (T₁.map f) = (jOneOf T₁).map f := by
  have hr := pRank_map_eq hinj (p := 2) Nat.one_lt_two
  unfold jOneOf
  simp only [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun E' hE' => ?_
    obtain ⟨E, hET, rfl⟩ := exists_le_map_eq hE'.1
    refine le_iSup₂_of_le E ⟨hET, (isElemAbelian_map_iff hinj hET).1 hE'.2.1, ?_⟩ le_rfl
    have := hE'.2.2
    rwa [card_map_of_le hinj hET, hr] at this
  · refine iSup₂_le fun E hE => ?_
    refine le_iSup₂_of_le (E.map f) ⟨Subgroup.map_mono hE.1,
      CFSG.SectionRank.isElemAbelian_map hE.2.1 f, ?_⟩ le_rfl
    rw [card_map_of_le hinj hE.1, hr]
    exact hE.2.2

omit [Finite H] [Finite H'] in
theorem omegaOneZ_map (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) {X : Subgroup H} (hX : X ≤ T₁) :
    omegaOneZ (X.map f) = (omegaOneZ X).map f := by
  unfold omegaOneZ
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hyc, hy2⟩
    obtain ⟨hyX, hycomm⟩ := Sec7.mem_centerOf_iff'.1 hyc
    obtain ⟨x, hx, rfl⟩ := hyX
    refine ⟨x, ⟨Sec7.mem_centerOf_iff'.2 ⟨hx, fun z hz => ?_⟩, ?_⟩, rfl⟩
    · exact eq_of_map_eq_of_mem hinj (mul_mem (hX hx) (hX hz)) (mul_mem (hX hz) (hX hx))
        (by rw [map_mul, map_mul]; exact hycomm _ (Subgroup.mem_map_of_mem f hz))
    · exact hinj _ (pow_mem (hX hx) 2) (by rw [map_pow]; exact hy2)
  · rintro ⟨x, ⟨hxc, hx2⟩, rfl⟩
    obtain ⟨hxX, hxcomm⟩ := Sec7.mem_centerOf_iff'.1 hxc
    refine ⟨Sec7.mem_centerOf_iff'.2 ⟨Subgroup.mem_map_of_mem f hxX, ?_⟩, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hxcomm z hz]
    · rw [← map_pow, hx2, map_one]

theorem tripleOf_map (hinj : ∀ x ∈ T₁, f x = 1 → x = 1) (i : Fin 3) :
    tripleOf (T₁.map f) i = (tripleOf T₁ i).map f := by
  rcases Sec7.fin_three_cases i with rfl | rfl | rfl
  · exact jOf_map hinj
  · show omegaOneZ (jOneOf (T₁.map f)) = (omegaOneZ (jOneOf T₁)).map f
    rw [jOneOf_map hinj, omegaOneZ_map hinj (Sec7.jOneOf_le T₁)]
  · exact omegaOneZ_map hinj le_rfl

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
