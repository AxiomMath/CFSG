module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Dec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf9Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Loc

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem mkQ_embed_mem_true (α : Finset (Fin n)) (hα : α.card = 4) {k : Wr 4} (hk : k ∈ kList) :
    mkQ n (embed (emb α hα) k) ∈ memBar α hα true := ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, rfl⟩

theorem mkQ_embed_mem_false (α : Finset (Fin n)) (hα : α.card = 4) {k : Wr 4}
    (hk : k ∈ kStarList) : mkQ n (embed (emb α hα) k) ∈ memBar α hα false :=
  ⟨embed (emb α hα) k, ⟨k, hk, rfl⟩, rfl⟩

theorem aeChar_of (hn8 : n ≠ 8) : TwinThinPf8.AEChar n := by
  intro α hα g hg
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (piSub n) g
  have hg' : mkQ n (a * zOf (emb α hα) * a⁻¹) = mkQ n (zOf (emb α hα)) := by
    have hg0 : mkQ n a * mkQ n (zOf (emb α hα)) * (mkQ n a)⁻¹ = mkQ n (zOf (emb α hα)) := hg
    simpa only [map_mul, map_inv] using hg0
  have hp := perm_range_of_conj hn8 (emb α hα) a hg'
  obtain ⟨b, c, hab, hc⟩ := exists_decomp (emb α hα) a hp
  have hy : a * yOf (emb α hα) * a⁻¹ = embed (emb α hα) (b * yQ * b⁻¹) :=
    conj_embed (emb α hα) hab hc yQ
  obtain ⟨k₁, hk₁, k₂, hk₂, j, hj⟩ : ∃ k₁ ∈ kList, ∃ k₂ ∈ kStarList, ∃ j : ℕ,
      b * yQ * b⁻¹ = k₁ * k₂ * yQ ^ j := by
    have := loc_conj_y b
    simp only [nyList, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at this
    obtain ⟨k₁, hk₁, k₂, hk₂, h | h | h⟩ := this
    · exact ⟨k₁, hk₁, k₂, hk₂, 0, by rw [h]; simp⟩
    · exact ⟨k₁, hk₁, k₂, hk₂, 1, by rw [h]; simp⟩
    · exact ⟨k₁, hk₁, k₂, hk₂, 2, by rw [h]; simp [pow_two, mul_assoc]⟩
  refine ⟨mkQ n (embed (emb α hα) k₁), mkQ_embed_mem_true α hα hk₁,
    mkQ n (embed (emb α hα) k₂), mkQ_embed_mem_false α hα hk₂, j, ?_⟩
  show mkQ n a * mkQ n (yOf (emb α hα)) * (mkQ n a)⁻¹ = _
  rw [← map_mul, ← map_inv, ← map_mul, hy, hj]
  show mkQ n (embed (emb α hα) (k₁ * k₂ * yQ ^ j)) = _
  simp only [map_mul, map_pow]
  rfl

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
