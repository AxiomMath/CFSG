module

public import CFSG.CGT.PushingUpLit.BHS7.QuotAutOn

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

variable {V : Type} [CommGroup V] [Finite V] {K S : Subgroup (MulAut V)}

@[expose] def offQ (K S : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {B | B ≤ S ∧ IsOffStar (qImg K B)}

@[expose] def offQMin (K S : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {B | B ∈ offQ K S ∧ ∀ C ∈ offQ K S, C ≤ B → C = B}

theorem exists_offQMin_le {B : Subgroup (MulAut V)} (hB : B ∈ offQ K S) :
    ∃ C ∈ offQMin K S, C ≤ B := by
  obtain ⟨C, ⟨hCS, hCB⟩, hmin⟩ := (wellFounded_lt (α := Subgroup (MulAut V))).has_min
    {C : Subgroup (MulAut V) | C ∈ offQ K S ∧ C ≤ B} ⟨B, hB, le_rfl⟩
  refine ⟨C, ⟨hCS, fun D hD hDC => ?_⟩, hCB⟩
  by_contra hne
  exact hmin D ⟨hD, hDC.trans hCB⟩ (lt_of_le_of_ne hDC hne)

omit [Finite V] in
theorem qImg_conjSub {σ : MulAut V} (hσ : σ ∈ K) {B : Subgroup (MulAut V)} :
    qImg K (conjSub σ B) = conjSub (BHS5.quotHom K ⟨σ, hσ⟩) (qImg K B) := by
  ext y
  rw [mem_conjSub_iff, mem_qImg, mem_qImg]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨σ⁻¹ * (x : MulAut V) * σ, K.mul_mem (K.mul_mem (K.inv_mem hσ) x.2) hσ⟩, ?_, ?_⟩
    · rwa [mem_conjSub_iff] at hx
    · rw [← map_inv, ← map_mul, ← map_mul]
      rfl
  · rintro ⟨z, hz, hzy⟩
    refine ⟨⟨σ * (z : MulAut V) * σ⁻¹, K.mul_mem (K.mul_mem hσ z.2) (K.inv_mem hσ)⟩, ?_, ?_⟩
    · rw [mem_conjSub_iff]
      simpa [mul_assoc] using hz
    · have h1 : (⟨σ * (z : MulAut V) * σ⁻¹, K.mul_mem (K.mul_mem hσ z.2) (K.inv_mem hσ)⟩ : ↥K) =
          ⟨σ, hσ⟩ * z * (⟨σ, hσ⟩)⁻¹ := rfl
      rw [h1, map_mul, map_mul, map_inv, hzy]
      group

omit [Finite V] in
theorem conjSub_conjSub_inv' (g : MulAut V) (X : Subgroup (MulAut V)) :
    conjSub g (conjSub g⁻¹ X) = X := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

omit [Finite V] in
theorem conjSub_inv_conjSub' (g : MulAut V) (X : Subgroup (MulAut V)) :
    conjSub g⁻¹ (conjSub g X) = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

omit [Finite V] in
theorem conjSub_mem_offQ {σ : MulAut V} (hσ : σ ∈ K) {B : Subgroup (MulAut V)}
    (hB : B ∈ offQ K S) (hle : conjSub σ B ≤ S) : conjSub σ B ∈ offQ K S := by
  refine ⟨hle, ?_⟩
  rw [qImg_conjSub hσ]
  exact ⟨hB.2.1.conj _, by rw [wt_conjSub]; exact hB.2.2⟩

omit [Finite V] in
theorem conjSub_mem_offQMin {σ : MulAut V} (hσ : σ ∈ K) {B : Subgroup (MulAut V)}
    (hB : B ∈ offQMin K S) (hle : conjSub σ B ≤ S) : conjSub σ B ∈ offQMin K S := by
  refine ⟨conjSub_mem_offQ hσ hB.1 hle, fun C hC hCB => ?_⟩
  have hC' : conjSub σ⁻¹ C ≤ B := by
    have := conjSub_mono σ⁻¹ hCB
    rwa [conjSub_inv_conjSub'] at this
  have hC'S : conjSub σ⁻¹ C ≤ S := hC'.trans hB.1.1
  have hmem : conjSub σ⁻¹ C ∈ offQ K S := conjSub_mem_offQ (K.inv_mem hσ) hC hC'S
  have heq := hB.2 _ hmem hC'
  rw [← heq, conjSub_conjSub_inv']

omit [Finite V] in
theorem eq_of_le_qImg (hinj : Function.Injective (BHS5.quotHom K)) (hSK : S ≤ K)
    {B : Subgroup (MulAut V)} (hB : B ∈ offQMin K S) {C' : Subgroup (MulAut (V ⧸ fixOp K))}
    (hC'B : C' ≤ qImg K B) (hC' : IsOffStar C') : C' = qImg K B := by
  have hBK : B ≤ K := hB.1.1.trans hSK
  have hC'r : C' ≤ (⊤ : Subgroup ↥K).map (BHS5.quotHom K) := hC'B.trans qImg_le_range
  have hle : liftQ K C' ≤ B := by
    have := liftQ_mono hC'B
    rwa [qImg, liftQ_quotImg hinj hBK] at this
  have himg : qImg K (liftQ K C') = C' := quotImg_liftQ hC'r
  have hmem : liftQ K C' ∈ offQ K S := ⟨hle.trans hB.1.1, by rw [himg]; exact hC'⟩
  have heq := hB.2 _ hmem hle
  rw [← himg, heq]

omit [Finite V] in
theorem isElemAbelian2_of_mem_offQ (hinj : Function.Injective (BHS5.quotHom K)) (hSK : S ≤ K)
    {B : Subgroup (MulAut V)} (hB : B ∈ offQ K S) : IsElemAbelian2 B := by
  have h := hB.2.1.2.2.1
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have hxK : x ∈ K := hSK (hB.1 hx)
    have hyK : y ∈ K := hSK (hB.1 hy)
    have := h.1 (BHS5.quotHom K ⟨x, hxK⟩) (mem_qImg.2 ⟨⟨x, hxK⟩, hx, rfl⟩)
      (BHS5.quotHom K ⟨y, hyK⟩) (mem_qImg.2 ⟨⟨y, hyK⟩, hy, rfl⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (hinj this)
  · have hxK : x ∈ K := hSK (hB.1 hx)
    have := h.2 (BHS5.quotHom K ⟨x, hxK⟩) (mem_qImg.2 ⟨⟨x, hxK⟩, hx, rfl⟩)
    rw [← map_pow] at this
    have h2 : (⟨x, hxK⟩ : ↥K) ^ 2 = 1 := hinj (by rw [this, map_one])
    exact congrArg Subtype.val h2

omit [Finite V] in
theorem ne_bot_of_mem_offQ {B : Subgroup (MulAut V)} (hB : B ∈ offQ K S) : B ≠ ⊥ := by
  rintro rfl
  apply hB.2.1.2.1
  unfold qImg
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem exists_mem_offQ (hinj : Function.Injective (BHS5.quotHom K)) (hSK : S ≤ K)
    {A : Subgroup (MulAut V)} (hAS : A ≤ S) (hA : IsOffStar A) : ∃ B, B ∈ offQ K S := by
  obtain ⟨B, hBA, hB⟩ := exists_isOffStar_quot hinj (hAS.trans hSK) hA
  exact ⟨B, hBA.trans hAS, hB⟩

end CFSG.CGT.PushingUpLit.BHS7
