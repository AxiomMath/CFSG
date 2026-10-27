module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5A02
public import CFSG.ClassicalInvolution.Q3.Q3T8B14F
public import CFSG.ClassicalInvolution.Q3.Q3T8B18B
public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AMLYEdge
public import CFSG.ClassicalInvolution.Q3.Q3T8B05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77.Thompson

section Leaf


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commute_R_tY [IsSimpleGroup G] {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 Ω K J S R T W z t) : ∀ r ∈ R, r * t = t * r := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have htT : t ∈ T := by
    have hTsyl : IsSylow2In T J :=
      Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hs.hJ.1 hs.hT.1 hs.hT.2.1
    have h8 : 8 ≤ Nat.card T := hΩ.eight_le_of_mem_RSet hs.hT.1
    exact T3.mem_of_isPGroup hs.ht hs.hT.2.1 hTsyl.2.1 (by omega)
  have hcomm : Commutes T R :=
    l6_7_proved G Ω hΩ S T hTΩ R hRΩ hTS hRS (Ne.symm (T8R.R_ne_T hs))
  exact fun r hr => (hcomm t htT r hr).symm

private theorem mem_of_eq' {H : Subgroup G} {a b : G} (e : a = b) (h : b ∈ H) : a ∈ H := by
  rw [e]
  exact h

private theorem closure_eq_of_mem {A B : Set G} (h₁ : ∀ a ∈ A, a ∈ Subgroup.closure B)
    (h₂ : ∀ b ∈ B, b ∈ Subgroup.closure A) : Subgroup.closure A = Subgroup.closure B :=
  le_antisymm ((Subgroup.closure_le _).mpr h₁) ((Subgroup.closure_le _).mpr h₂)

theorem layerShapeLeafY_proved :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Q3AM.E4SettingY Ω K J S R T W z t →
        Q3AM.LayerE4 Ω K z → ∀ s : G, E4Axis Ω K J R z t s →
          LayerShapeAt Ω K J (z * t) ∧
            (∀ J₁ ∈ omegaNbr Ω K, IsUniqueInvolution J₁ s → LayerShapeAt Ω K J₁ (z * s)) ∧
              (∀ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s) →
                LayerShapeAt Ω K J₂ (z * (t * s))) := by
  intro G _ _ _ Ω K J S R T W z t hset _ s _
  have hbad := hset.bad
  have hs := hbad.std
  have hE := hset.mu
  refine ⟨layerShapeAt_of_shape hs hE (fun hL hL' hu => hbad.eq_mul_of_nbr_nbr hL hL' hu),
    fun J₁ hJ₁ hu₁ => ?_, fun J₂ hJ₂ hu₂ => ?_⟩
  · obtain ⟨S₁, R₁, T₁, W₁, hst₁⟩ := c27_setupB hs.stand hs.noTwins hs.hz hJ₁ hu₁
    exact layerShapeAt_of_shape hst₁ (muIsoE4_of_mem_WSet hs hE hst₁.hW.1)
      (fun hL hL' hu => hbad.eq_mul_of_nbr_nbr_at hst₁ hL hL' hu)
  · obtain ⟨S₂, R₂, T₂, W₂, hst₂⟩ := c27_setupB hs.stand hs.noTwins hs.hz hJ₂ hu₂
    exact layerShapeAt_of_shape hst₂ (muIsoE4_of_mem_WSet hs hE hst₂.hW.1)
      (fun hL hL' hu => hbad.eq_mul_of_nbr_nbr_at hst₂ hL hL' hu)

theorem vertexALeafY_of_layerShape : Q3AM.VertexALeafY := by
  have hLS := CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.layerShapeLeafY_proved
  intro G _ _ _ Ω K J S R T W z t h hsec s hs
  obtain ⟨hLS1, hLS2, hLS3⟩ := hLS G Ω K J S R T W z t h hsec s hs
  have hstd : Std8 Ω K J S R T W z t := h.bad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hK : K ∈ Ω := hstd.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hs2 := hs.sq
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hNK : Q3AM.NoTriangleAtEdge Ω K J := h.noTri
  have hB : CFSG.Open.IsElemAbelian 2 (Subgroup.closure ({z, t, s} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 ht2 hs2 hzt hs.comm_z hs.comm_t
  have hRsyl : IsSylow2In R K :=
    Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hstd.hR.1 hstd.hR.2.1
  have hRt : ∀ r ∈ R, r * t = t * r := commute_R_tY hstd
  have hts : t ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  obtain ⟨J₁, hJ₁, hv₁⟩ := hs.nbr₁
  obtain ⟨J₂, hJ₂, hv₂⟩ := hs.nbr₂
  have hnorm : ∀ {M : Subgroup G} {u : G}, M ∈ Ω → IsUniqueInvolution M u → ∀ g : G,
      g * u = u * g → conjSub g M = M := fun hM hu g hg =>
    conjSub_eq_of_mem_normalizer (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM
      (hnt _ hM) hu (Subgroup.mem_centralizer_singleton_iff.mpr hg))
  have hzcl : z ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have htcl : t ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hscl : s ∈ Subgroup.closure ({z, t, s} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨?_, ?_, ?_⟩
  ·
    have hz₁ : z ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
    have hs₁ : s ∈ Subgroup.closure ({z, s, z * t} : Set G) := Subgroup.subset_closure (by simp)
    have hzt₁ : z * t ∈ Subgroup.closure ({z, s, z * t} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht₁ : t ∈ Subgroup.closure ({z, s, z * t} : Set G) := by
      have := Subgroup.mul_mem _ hz₁ hzt₁
      rwa [← mul_assoc, hz2, one_mul] at this
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, s, z * t} : Set G) :=
      closure_eq_of_mem (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₁, ht₁, hs₁]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, hscl, Subgroup.mul_mem _ hzcl htcl])
    exact hyp51At_vertexAY hstd hNK hs2 hs.comm_z hs.comm_t (Ne.symm hts) hRsyl hs.cent_R
      hs.norm_J hJ₁ hv₁ hLS1 hB hBgen
  ·
    obtain ⟨S₁, R₁, T₁, W₁, hs₁⟩ := exists_std8_of_omegaNbr hstd.stand hstd.noTwins hstd.hz hJ₁ hv₁
    have hz₂ : z ∈ Subgroup.closure ({z, t, z * s} : Set G) := Subgroup.subset_closure (by simp)
    have ht₂ : t ∈ Subgroup.closure ({z, t, z * s} : Set G) := Subgroup.subset_closure (by simp)
    have hzs₂ : z * s ∈ Subgroup.closure ({z, t, z * s} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hs₂ : s ∈ Subgroup.closure ({z, t, z * s} : Set G) := by
      have := Subgroup.mul_mem _ hz₂ hzs₂
      rwa [← mul_assoc, hz2, one_mul] at this
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, t, z * s} : Set G) :=
      closure_eq_of_mem (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₂, ht₂, hs₂]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, htcl, Subgroup.mul_mem _ hzcl hscl])
    have hNJ₁ : Q3AM.NoTriangleAtEdge Ω K J₁ := Q3AM.noTriangleAtEdge_nbr h.bad hNK hJ₁
    exact hyp51At_vertexAY hs₁ hNJ₁ ht2 hzt hs.comm_t.symm hts hRsyl hRt
      (hnorm hJ₁.1 hv₁ t hs.comm_t) hstd.hJ hstd.ht (hLS2 J₁ hJ₁ hv₁) hB hBgen
  ·
    obtain ⟨S₂, R₂, T₂, W₂, hs₂⟩ := exists_std8_of_omegaNbr hstd.stand hstd.noTwins hstd.hz hJ₂ hv₂
    have hz₃ : z ∈ Subgroup.closure ({z, t, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have ht₃ : t ∈ Subgroup.closure ({z, t, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hzts₃ : z * (t * s) ∈ Subgroup.closure ({z, t, z * (t * s)} : Set G) :=
      Subgroup.subset_closure (by simp)
    have hs₃ : s ∈ Subgroup.closure ({z, t, z * (t * s)} : Set G) := by
      have e : s = t * (z * (z * (t * s))) := by
        calc s = (t * t) * s := by rw [ht2, one_mul]
          _ = t * (t * s) := by rw [mul_assoc]
          _ = t * ((z * z) * (t * s)) := by rw [hz2, one_mul]
          _ = t * (z * (z * (t * s))) := by rw [mul_assoc]
      exact mem_of_eq' e (Subgroup.mul_mem _ ht₃ (Subgroup.mul_mem _ hz₃ hzts₃))
    have hBgen : Subgroup.closure ({z, t, s} : Set G) =
        Subgroup.closure ({z, t, z * (t * s)} : Set G) :=
      closure_eq_of_mem (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hz₃, ht₃, hs₃]) (fun a ha => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with h | h | h <;> rw [h]
        exacts [hzcl, htcl, Subgroup.mul_mem _ hzcl (Subgroup.mul_mem _ htcl hscl)])
    have hcomm : t * s * t = t * (t * s) := by
      calc t * s * t = t * (s * t) := by rw [mul_assoc]
        _ = t * (t * s) := by rw [hs.comm_t]
    have hne : t ≠ t * s := fun e => hs.ne_one (by
      have : t * s = t * 1 := by rw [mul_one]; exact e.symm
      exact mul_left_cancel this)
    have hnormJ₂ : conjSub t J₂ = J₂ := hnorm hJ₂.1 hv₂ t hcomm.symm
    have hNJ₂ : Q3AM.NoTriangleAtEdge Ω K J₂ := Q3AM.noTriangleAtEdge_nbr h.bad hNK hJ₂
    have := hyp51At_vertexAY hs₂ hNJ₂ ht2 hzt hcomm hne hRsyl hRt hnormJ₂ hstd.hJ hstd.ht
      (hLS3 J₂ hJ₂ hv₂) hB hBgen
    rwa [← mul_assoc] at this

theorem vertexALeafY_proved : Q3AM.VertexALeafY := vertexALeafY_of_layerShape

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
