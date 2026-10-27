module

public import Certificates.Data.Kernel.SporSch.Co2M
public import CFSG.Certificates.Kernel.SporSch.MatRep
public import CFSG.Certificates.Kernel.Misc.PairCountSound

set_option exponentiation.threshold 600

public section

namespace CFSG.KS.Co2M

open CFSG.KC.Enum CFSG.RankThree.Native.F2 CFSG.KS.MatRep CFSG.KS.Raw

theorem M22_eq : M22 = 2 ^ 22 - 1 := rfl

theorem L22_eq : L22 = lanes 22 := by decide

theorem I22_eq : I22 = idM 22 := by decide

theorem vmK_eq (v M : ℕ) : vmK v M = vmul 22 v M := vmulK_eq M22_eq v M

theorem mmK_eq (A B : ℕ) : mmK A B = mmul 22 A B := mulK_eq (by norm_num) M22_eq L22_eq A B

theorem mask12 : CFSG.KS.mask 12 = 4095 := by decide

theorem bindK_sound {V : Array ℕ} {PV P M MI : ℕ} {a : Array ℕ} (G : Good 22 V)
    (hVs : V.size = 2300) (hV : ∀ i < 2300, V[i]! = VG PV i) (ha : a = unpack 2300 12 P)
    (h : bindK PV P M MI = true) : Rep 22 V a M MI := by
  unfold bindK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hs : a.size = V.size := by
    rw [ha, hVs]
    simp [unpack]
  have himg : ∀ i < V.size, a[i]! < V.size ∧ V[a[i]!]! = vmul 22 V[i]! M := by
    intro i hi
    rw [hVs] at hi ⊢
    have := allN_spec h1 i hi
    rw [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    have ea : a[i]! = pg 12 4095 P i := by
      rw [ha, CFSG.KC.Misc.PairCount.unpack_get hi, mask12]
    rw [ea, hV _ this.1, hV i hi, ← vmK_eq]
    exact this
  obtain ⟨hinv, hp⟩ := inv_of_images G.hd G.nodup G.lt hs himg
    (by rw [← mmK_eq, h2, I22_eq]) (by rw [← mmK_eq, h3, I22_eq])
  exact ⟨hp, hinv⟩

end CFSG.KS.Co2M

end
