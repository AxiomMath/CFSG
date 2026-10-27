module

public import CFSG.ClassicalInvolution.Asc77.AscS24Inv
public import CFSG.ClassicalInvolution.Asc77.AscS24Frame

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

theorem conj_u_of {G : Type} [Group G] {r u z b b' : G} (hu : u = b * b' ∨ u = z * (b * b'))
    (h1 : r * b * r⁻¹ = b * z) (h2 : r * b' * r⁻¹ = b') (h3 : r * z * r⁻¹ = z)
    (hzb' : z * b' = b' * z) : r * u * r⁻¹ = u * z := by
  rcases hu with rfl | rfl
  · calc r * (b * b') * r⁻¹ = (r * b * r⁻¹) * (r * b' * r⁻¹) := by group
      _ = b * (z * b') := by rw [h1, h2]; group
      _ = b * b' * z := by rw [hzb']; group
  · calc r * (z * (b * b')) * r⁻¹ = (r * z * r⁻¹) * (r * b * r⁻¹) * (r * b' * r⁻¹) := by group
      _ = z * (b * (z * b')) := by rw [h1, h2, h3]; group
      _ = z * (b * b') * z := by rw [hzb']; group

theorem conj_u_of' {G : Type} [Group G] {r u z b b' : G} (hu : u = b * b' ∨ u = z * (b * b'))
    (h1 : r * b * r⁻¹ = b) (h2 : r * b' * r⁻¹ = b' * z) (h3 : r * z * r⁻¹ = z) :
    r * u * r⁻¹ = u * z := by
  rcases hu with rfl | rfl
  · calc r * (b * b') * r⁻¹ = (r * b * r⁻¹) * (r * b' * r⁻¹) := by group
      _ = b * b' * z := by rw [h1, h2]; group
  · calc r * (z * (b * b')) * r⁻¹ = (r * z * r⁻¹) * (r * b * r⁻¹) * (r * b' * r⁻¹) := by group
      _ = z * (b * b') * z := by rw [h1, h2, h3]; group

structure Ctx (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u g : G) : Type where
  hs : Hyp23Setting p f Ω K K' z
  hd : Hyp24Data Ω K K' W S R R' z u
  hg : g⁻¹ * z * g = u
  D : T7X.Frame24 p f Ω W
  hK : D.F.ρ.K = K
  hK' : D.F.ρ'.K = K'
  hR : D.F.ρ.R = R
  hR' : D.F.ρ'.R = R'
  hz : D.F.z = z
  hJ : D.F.ρ₃.K = conjSub g⁻¹ K
  hj : D.F.j = u
  c : ℕ
  hc : 2 * c = D.m

namespace Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u g : G}

theorem exists_of_gt [IsSimpleGroup G] (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (hg : g⁻¹ * z * g = u) (h8 : 8 < Nat.card ↥R) :
    Nonempty (Ctx p f Ω K K' W S R R' z u g) := by
  obtain ⟨D, hK, hK', hR, hR', hz, hJ, hj⟩ := exists_frame24_conj hs hd hg
  have h8' : 8 < Nat.card ↥D.F.ρ.R := hR ▸ h8
  obtain ⟨c, hc⟩ := D.m_even h8'
  exact ⟨⟨hs, hd, hg, D, hK, hK', hR, hR', hz, hJ, hj, c, hc.symm⟩⟩

variable (C : Ctx p f Ω K K' W S R R' z u g)

include C

@[expose] def e0 : G := C.D.eEl C.c

@[expose] def B : Subgroup G := Subgroup.closure ({u * C.e0, u, z} : Set G)

theorem e0_mem : C.e0 ∈ W := C.D.eEl_mem C.c

theorem e0_sq (hZ : W ⊓ centerIn (Subgroup.normalizer (W : Set G)) = ⊥) : C.e0 * C.e0 = 1 :=
  C.D.eEl_sq C.hc hZ

theorem e0_ne_one : C.e0 ≠ 1 := C.D.eEl_ne_one C.hc

theorem z_mem_W : z ∈ W := C.hd.hzW

theorem u_mem_W : u ∈ W := C.hd.hu.2.1

theorem comm_W {a b : G} (ha : a ∈ W) (hb : b ∈ W) : a * b = b * a :=
  Thompson.commutes_of_mem_WSet C.D.c.hp C.D.c.hq C.D.c.hΩ C.D.c.hW a ha b hb

theorem u_cases :
    u = C.D.x₁ ^ C.D.m * C.D.x₂ ^ C.D.m ∨ u = z * (C.D.x₁ ^ C.D.m * C.D.x₂ ^ C.D.m) := by
  have hRsyl : IsSylow2In R K := by
    have h := C.D.F.ρ.hRK
    rwa [C.hR, C.hK] at h
  have hR'syl : IsSylow2In R' K' := by
    have h := C.D.F.ρ'.hRK
    rwa [C.hR', C.hK'] at h
  have hb : C.D.x₁ ^ C.D.m ∈ R := by
    have h := bEl_mem C.D
    rwa [C.hR] at h
  have hb' : C.D.x₂ ^ C.D.m ∈ R' := by
    have h := bEl'_mem C.D
    rwa [C.hR'] at h
  obtain ⟨huK, huW, hu2, hu1, huz⟩ := C.hd.hu
  exact T7E.involution_cases C.hs hRsyl hR'syl C.hd.hR.2.2 C.hd.hR'.2.2 hb hb'
    (orderOf_bEl C.D) (orderOf_bEl' C.D) huK (C.hd.hWS huW) hu2 hu1 huz
    (C.comm_W huW (W.pow_mem C.D.x₁_mem _)) (C.comm_W huW (W.pow_mem C.D.x₂_mem _))

theorem conj_r_u : C.D.F.ρ.r * u * C.D.F.ρ.r⁻¹ = u * z := by
  have h1 := conj_r_bEl C.D
  have h3 := conj_r_z C.D
  rw [C.hz] at h1 h3
  exact conj_u_of C.u_cases h1 (conj_r_bEl' C.D) h3
    (C.comm_W C.z_mem_W (W.pow_mem C.D.x₂_mem _))

theorem conj_t_u : C.D.F.ρ'.r * u * C.D.F.ρ'.r⁻¹ = u * z := by
  have h2 := conj_t_bEl' C.D
  have h3 := conj_t_z C.D
  rw [C.hz] at h2 h3
  exact conj_u_of' C.u_cases (conj_t_bEl C.D) h2 h3

theorem conj_s_z : C.D.F.ρ₃.r * z * C.D.F.ρ₃.r⁻¹ = u * z := by
  have h := S24.conj_s_z C.D
  rwa [C.hz, C.hj] at h

theorem conj_r_e0 : C.D.F.ρ.r * C.e0 * C.D.F.ρ.r⁻¹ = C.e0 := C.D.eEl_r C.c

theorem conj_s_e0 : C.D.F.ρ₃.r * C.e0 * C.D.F.ρ₃.r⁻¹ = C.e0 := C.D.eEl_s C.c

theorem conj_t_e0 : C.D.F.ρ'.r * C.e0 * C.D.F.ρ'.r⁻¹ = C.e0 * z := by
  have h := C.D.eEl_t_eq C.hc
  rwa [C.hz] at h

end Ctx

end CFSG.ClassicalInvolution.Asc77.S24
