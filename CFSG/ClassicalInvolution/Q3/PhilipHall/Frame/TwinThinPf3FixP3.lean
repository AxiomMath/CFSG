module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3OkP3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf3Mem

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

theorem ha_mem_P3 : dataP3.a ∈ memAt α0 α0_card true :=
  mem_memAt_of_spec true f0 emb_α0 ⟨vec4 [0, 2], d₁⟩ (by decide +kernel) dataP3.a
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem hb_mem_P3 : dataP3.b ∈ memAt α0 α0_card true :=
  mem_memAt_of_spec true f0 emb_α0 ⟨vec4 [0, 3], d₂⟩ (by decide +kernel) dataP3.b
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem hc_mem_P3 : dataP3.c ∈ memAt α1 α1_card false :=
  mem_memAt_of_spec false f1 emb_α1 ⟨vec4 [0, 3], d₁⟩ (by decide +kernel) dataP3.c
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem hd_mem_P3 : dataP3.d ∈ memAt α1 α1_card false :=
  mem_memAt_of_spec false f1 emb_α1 ⟨vec4 [0, 1], d₂⟩ (by decide +kernel) dataP3.d
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem fixPair_P3 (σ : ↥e29Sub →* ↥e29Sub) (hσ : ∃ a : ℕ, ∀ r, σ^[3 ^ a] r = r)
    (h1 : ∀ x : ↥e29Sub, (x : AEQ 8) ∈ memBar α0 α0_card true → σ x = x)
    (h2 : ∀ x : ↥e29Sub, (x : AEQ 8) ∈ memBar α1 α1_card false → σ x = x) : ∀ r, σ r = r := by
  have hok := ok_P3
  refine fix_core hok σ hσ ?_ ?_ ?_ ?_
  · exact h1 _ ⟨dataP3.a, ha_mem_P3, rfl⟩
  · exact h1 _ ⟨dataP3.b, hb_mem_P3, rfl⟩
  · exact h2 _ ⟨dataP3.c, hc_mem_P3, rfl⟩
  · exact h2 _ ⟨dataP3.d, hd_mem_P3, rfl⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf.P3
