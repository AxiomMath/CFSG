module

public import CFSG.ClassicalInvolution.Q3.Q3AM289A07
public import CFSG.ClassicalInvolution.Q3.Q3AM289Nbr
public import CFSG.ClassicalInvolution.Q3.Q3AMLYEdge
public import CFSG.ClassicalInvolution.Q3.Q3T8B14F
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22RowsFin

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace S3A

section Plain

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_sylow_centralizing (hΩ : HypOmegaMod Ω) {L K : Subgroup G} {s : G}
    (hLs : IsUniqueInvolution L s) (hKL : K ∈ omegaNbr Ω L) :
    ∃ P : Subgroup G, IsSylow2In P K ∧ ∀ r ∈ P, r * s = s * r := by
  obtain ⟨hKΩ, -, P, hP, hPK, hPN⟩ := hKL
  refine ⟨P, Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hKΩ hP hPK,
    fun r hr => ?_⟩
  have h1 : r * s * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hPN hr) s).mp hLs.mem
  have h2 : (r * s * r⁻¹) * (r * s * r⁻¹) = 1 := by
    calc (r * s * r⁻¹) * (r * s * r⁻¹) = r * (s * s) * r⁻¹ := by group
      _ = 1 := by rw [hLs.sq]; group
  rcases hLs.unique _ h1 h2 with h3 | h3
  · exact absurd (by simpa using h3) hLs.ne_one
  · calc r * s = (r * s * r⁻¹) * r := by group
      _ = s * r := by rw [h3]

theorem closure_eq_of_mem' {A B : Set G} (h₁ : ∀ a ∈ A, a ∈ Subgroup.closure B)
    (h₂ : ∀ b ∈ B, b ∈ Subgroup.closure A) : Subgroup.closure A = Subgroup.closure B :=
  le_antisymm ((Subgroup.closure_le _).mpr h₁) ((Subgroup.closure_le _).mpr h₂)

end Plain

end S3A

section Leaf


theorem s3VertexA_proved : Q3AM.S3VertexALeaf := by
  intro G _ _ _ Ω K J S R T W z t hset s hs hnbr2
  have hbad := hset.bad
  have hstd : Std8 Ω K J S R T W z t := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hK : K ∈ Ω := hstd.stand.mem
  have hJΩ : J ∈ Ω := hstd.hJ.1
  have hTW := Q3T7.twinSqAlphaAll3_proved
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hs2 := hs.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hB : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({z, t, s} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hs.comm_z hs.comm_t
  have hts : t ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have hzcl : z ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have htcl : t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hscl : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsymm : ∀ {M N : Subgroup G}, M ∈ Ω → N ∈ Ω → N ∈ omegaNbr Ω M → M ∈ omegaNbr Ω N :=
    fun hM hN h => Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hM hN h
  obtain ⟨L, hLK, hLs, hLstar, hLnot⟩ := hs.nbr
  have hLnbr : L ∉ omegaNbr Ω J := fun h => hLnot (Set.mem_insert_of_mem _ h)
  obtain ⟨J₂, hJ₂, hu₂⟩ := hnbr2
  refine ⟨?_, ?_, ?_⟩
  ·
    obtain ⟨R₀, hR₀, hR₀c⟩ := S3A.exists_sylow_centralizing hΩ hLs (hsymm hK hLK.1 hLK)
    have hz₁ : z ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
    have hs₁ : s ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
    have hzt₁ : z * t ∈ Subgroup.closure ({z, s, z * t} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht₁ : t ∈ Subgroup.closure ({z, s, z * t} : Set G) := by
      have := Subgroup.mul_mem _ hz₁ hzt₁
      rwa [← mul_assoc, hz2, one_mul] at this
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, s, z * t} : Set G) :=
      S3A.closure_eq_of_mem' (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₁, ht₁, hs₁]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, hscl, Subgroup.mul_mem _ hzcl htcl])
    exact S3A.hyp51At_vertex_s3 hTW hstd (fun L' h1 h2 => hset.noTri L' h1 h2) hs2 hs.comm_z
      hs.comm_t (Ne.symm hts) hR₀ hR₀c hLK.1 hLs hLstar hLnbr hB hBgen
  ·
    obtain ⟨S₁, R₁, T₁, W₁, hst₁⟩ :=
      exists_std8_of_omegaNbr hstd.stand hstd.noTwins hstd.hz hLK hLs
    have hnoL : Q3AM.NoTriangleAtEdge Ω K L := Q3AM.noTriangleAtEdge_nbr hbad hset.noTri hLK
    obtain ⟨R₀, hR₀, hR₀c⟩ := S3A.exists_sylow_centralizing hΩ hstd.ht (hsymm hK hJΩ hstd.hJ)
    have hJL : J ∈ omegaStarNbr Ω L := Q3T6.Mu.omegaStarNbr_symm hΩ hJΩ hLK.1 hLstar
    have hJnbr : J ∉ omegaNbr Ω L := fun h => hLnbr (hsymm hLK.1 hJΩ h)
    have hz₂ : z ∈ Subgroup.closure ({z, t, z * s} : Set G) := Subgroup.subset_closure (by simp)
    have ht₂ : t ∈ Subgroup.closure ({z, t, z * s} : Set G) := Subgroup.subset_closure (by simp)
    have hzs₂ : z * s ∈ Subgroup.closure ({z, t, z * s} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hs₂ : s ∈ Subgroup.closure ({z, t, z * s} : Set G) := by
      have := Subgroup.mul_mem _ hz₂ hzs₂
      rwa [← mul_assoc, hz2, one_mul] at this
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, t, z * s} : Set G) :=
      S3A.closure_eq_of_mem' (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₂, ht₂, hs₂]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, htcl, Subgroup.mul_mem _ hzcl hscl])
    exact S3A.hyp51At_vertex_s3 hTW hst₁ (fun L' h1 h2 => hnoL L' h1 h2) ht2 hzt hs.comm_t.symm
      hts hR₀ hR₀c hJΩ hstd.ht hJL hJnbr hB hBgen
  ·
    obtain ⟨S₂, R₂, T₂, W₂, hst₂⟩ :=
      exists_std8_of_omegaNbr hstd.stand hstd.noTwins hstd.hz hJ₂ hu₂
    have hno₂ : Q3AM.NoTriangleAtEdge Ω K J₂ := Q3AM.noTriangleAtEdge_nbr hbad hset.noTri hJ₂
    obtain ⟨L', hL'K, hL's, hL'star⟩ := s3_mem_omegaStarNbr_nbr2 hbad hs hJ₂ hu₂
    obtain ⟨R₀, hR₀, hR₀c⟩ := S3A.exists_sylow_centralizing hΩ hL's (hsymm hK hL'K.1 hL'K)
    have hu₂c : (t * s) * s = s * (t * s) := by
      calc (t * s) * s = t := by rw [mul_assoc, hs2, mul_one]
        _ = s * (t * s) := by
          calc t = (s * s) * t := by rw [hs2, one_mul]
            _ = s * (s * t) := by rw [mul_assoc]
            _ = s * (t * s) := by rw [← hs.comm_t]
    have hne₂ : s ≠ t * s := fun e => hstd.ht.ne_one (by
      have h : t * s = 1 * s := by rw [one_mul]; exact e.symm
      exact mul_right_cancel h)
    have hz₃ : z ∈ Subgroup.closure ({z, s, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hs₃ : s ∈ Subgroup.closure ({z, s, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hzts₃ : z * (t * s) ∈ Subgroup.closure ({z, s, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht₃ : t ∈ Subgroup.closure ({z, s, z * (t * s)} : Set G) := by
      have e : t = z * (z * (t * s)) * s := by
        calc t = (t * s) * s := by rw [mul_assoc, hs2, mul_one]
          _ = ((z * z) * (t * s)) * s := by rw [hz2, one_mul]
          _ = z * (z * (t * s)) * s := by simp only [mul_assoc]
      have h := Subgroup.mul_mem _ (Subgroup.mul_mem _ hz₃ hzts₃) hs₃
      rwa [← e] at h
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, s, z * (t * s)} : Set G) :=
      S3A.closure_eq_of_mem' (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₃, ht₃, hs₃]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, hscl, Subgroup.mul_mem _ hzcl (Subgroup.mul_mem _ htcl hscl)])
    have := S3A.hyp51At_vertex_s3 hTW hst₂ (fun L'' h1 h2 => hno₂ L'' h1 h2) hs2 hs.comm_z hu₂c
      hne₂ hR₀ hR₀c hL'K.1 hL's hL'star (hno₂ L' hL'K) hB hBgen
    rwa [← mul_assoc] at this

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
