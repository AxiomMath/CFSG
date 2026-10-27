module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.PhiMap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.UnitriangularCoord
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.VEndCentralizer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup Matrix CFSG.GroupTheory SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G}
  {S A B Aa D : Subgroup G} {z b : G}

private theorem mem_normalizer_A_of_mem_S (W : ThLocalIn L S A B z) {s : G} (hs : s ∈ S) :
    s ∈ normalizer (A : Set G) :=
  mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := s) fun a ha => by
    simpa using W.conj_mem_A_of_mem_S (S.inv_mem hs) ha)

private theorem mem_normalizer_D_of_mem_S (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {s : G} (hs : s ∈ S) :
    s ∈ normalizer (D : Set G) := by
  have h : s ∈ L ⊓ normalizer (D : Set G) := by
    have h' : s ∈ L ⊓ normalizer (A : Set G) := ⟨W.S_le hs, mem_normalizer_A_of_mem_S W hs⟩
    rwa [← H.inf_normalizer_D_eq W W2 hD] at h'
  exact h.2

private theorem mem_normalizer_omega1_of_mem_S (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {s : G} (hs : s ∈ S) :
    s ∈ normalizer (omega1 D hD.comm : Set G) :=
  normalizer_D_le_normalizer_omega1 hD (mem_normalizer_D_of_mem_S H W W2 hD hs)

private theorem conj_mul_inv_centralizes_A {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    {y s : G} (hy : y ∈ normalizer (A : Set G)) (hs : s ∈ normalizer (A : Set G))
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hys : IsRep A c y M) (hss : IsRep A c s M) :
    ∀ a ∈ A, (y * s⁻¹) * a * (y * s⁻¹)⁻¹ = a := by
  intro a ha
  have hsa : s⁻¹ * a * s ∈ A := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.1 ((normalizer (A : Set G)).inv_mem hs) a).1 ha
  calc (y * s⁻¹) * a * (y * s⁻¹)⁻¹ = y * (s⁻¹ * a * s) * y⁻¹ := by group
    _ = s * (s⁻¹ * a * s) * s⁻¹ :=
      IsRep.conj_mem hc hys (fun b hb => (mem_normalizer_iff.1 hy b).1 hb)
        (fun b hb => (mem_normalizer_iff.1 hs b).1 hb) hss hsa
    _ = a := by group

private theorem vConj_eq_of_conj_eq (hD : DHyp A Aa t D) {n m : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G))
    (hm : m ∈ normalizer (omega1 D hD.comm : Set G))
    (h : ∀ v ∈ omega1 D hD.comm, n * v * n⁻¹ = m * v * m⁻¹) :
    vConj hD n = vConj hD m := by
  apply AbelianSub.end_ext
  intro x
  rw [val_vConj_apply hD hn, val_vConj_apply hD hm]
  exact h x.val (AbelianSub.val_mem x)

private theorem vConj_ne_zero (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G}
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) : vConj hD n ≠ 0 := by
  intro h
  have h1 : vConj hD n * vConj hD n⁻¹ = 1 := vConj_mul_inv hD hn
  rw [h, zero_mul] at h1
  have h2 : (1 : AddMonoid.End (VSub hD)) = 0 := h1.symm
  have hzV : z ∈ omega1 D hD.comm := H.A_le_omega1 W W2 hD W.z_mem_A
  have hz0 : AbelianSub.mk z hzV ≠ (0 : VSub hD) := by
    intro hz
    have h' := congrArg AbelianSub.val hz
    rw [AbelianSub.val_mk, AbelianSub.val_zero] at h'
    exact W.z_ne_one h'
  have h3 := congrArg (fun f : AddMonoid.End (VSub hD) => f (AbelianSub.mk z hzV)) h2
  exact hz0 (by simpa using h3)

private theorem vConj_t_commute_of_mem_S (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {n : G} (hn : n ∈ S) :
    vConj hD t * vConj hD n = vConj hD n * vConj hD t := by
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) := H.t_mem_normalizer_omega1 W W2 hD
  have hnV : n ∈ normalizer (omega1 D hD.comm : Set G) :=
    mem_normalizer_omega1_of_mem_S H W W2 hD hn
  have hnt : n * t = t * n := (H.comm_of_mem_L (W.S_le hn)).symm
  calc vConj hD t * vConj hD n = vConj hD (t * n) := (vConj_mul hD htV hnV).symm
    _ = vConj hD (n * t) := by rw [hnt]
    _ = vConj hD n * vConj hD t := vConj_mul hD hnV htV

private theorem vConj_inv_mul_commute (hD : DHyp A Aa t D) {g : G}
    (hg : g ∈ normalizer (omega1 D hD.comm : Set G)) {w : AddMonoid.End (VSub hD)}
    (hgw : vConj hD g * w = w * vConj hD g) :
    vConj hD g⁻¹ * w = w * vConj hD g⁻¹ := by
  have hg' : g⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hg
  have h1 : vConj hD g⁻¹ * (vConj hD g * w) * vConj hD g⁻¹ =
      vConj hD g⁻¹ * (w * vConj hD g) * vConj hD g⁻¹ := by rw [hgw]
  have h2 : vConj hD g⁻¹ * (vConj hD g * w) * vConj hD g⁻¹ = w * vConj hD g⁻¹ := by
    calc vConj hD g⁻¹ * (vConj hD g * w) * vConj hD g⁻¹
        = (vConj hD g⁻¹ * vConj hD g) * w * vConj hD g⁻¹ := by noncomm_ring
      _ = w * vConj hD g⁻¹ := by rw [vConj_inv_mul hD hg, one_mul]
  have h3 : vConj hD g⁻¹ * (w * vConj hD g) * vConj hD g⁻¹ = vConj hD g⁻¹ * w := by
    calc vConj hD g⁻¹ * (w * vConj hD g) * vConj hD g⁻¹
        = vConj hD g⁻¹ * w * (vConj hD g * vConj hD g⁻¹) := by noncomm_ring
      _ = vConj hD g⁻¹ * w := by rw [vConj_mul_inv hD hg, mul_one]
  rw [h2, h3] at h1
  exact h1.symm

private theorem vConj_conj_t_mul_w (hD : DHyp A Aa t D) {g : G}
    (hg : g ∈ normalizer (omega1 D hD.comm : Set G))
    (ht : t ∈ normalizer (omega1 D hD.comm : Set G)) {w : AddMonoid.End (VSub hD)}
    (hgw : vConj hD g * w = w * vConj hD g)
    (hτw : vConj hD t * w = (w + 1) * vConj hD t) :
    vConj hD (g⁻¹ * t * g) * w = (w + 1) * vConj hD (g⁻¹ * t * g) := by
  have hg' : g⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hg
  have hgiw := vConj_inv_mul_commute hD hg hgw
  have hu : vConj hD (g⁻¹ * t * g) =
      vConj hD g⁻¹ * vConj hD t * vConj hD g := by
    rw [vConj_mul hD ((normalizer _).mul_mem hg' ht) hg, vConj_mul hD hg' ht]
  rw [hu]
  calc (vConj hD g⁻¹ * vConj hD t * vConj hD g) * w
      = vConj hD g⁻¹ * vConj hD t * (vConj hD g * w) := by noncomm_ring
    _ = vConj hD g⁻¹ * vConj hD t * (w * vConj hD g) := by rw [hgw]
    _ = vConj hD g⁻¹ * (vConj hD t * w) * vConj hD g := by noncomm_ring
    _ = vConj hD g⁻¹ * ((w + 1) * vConj hD t) * vConj hD g := by rw [hτw]
    _ = (vConj hD g⁻¹ * (w + 1)) * vConj hD t * vConj hD g := by noncomm_ring
    _ = (vConj hD g⁻¹ * w + vConj hD g⁻¹) * vConj hD t * vConj hD g := by
        rw [mul_add, mul_one]
    _ = (w * vConj hD g⁻¹ + vConj hD g⁻¹) * vConj hD t * vConj hD g := by rw [hgiw]
    _ = ((w + 1) * vConj hD g⁻¹) * vConj hD t * vConj hD g := by
        rw [show w * vConj hD g⁻¹ + vConj hD g⁻¹ =
          (w + 1) * vConj hD g⁻¹ by rw [add_mul, one_mul]]
    _ = (w + 1) * (vConj hD g⁻¹ * vConj hD t * vConj hD g) := by noncomm_ring

private theorem vConj_t_mul_w (hD : DHyp A Aa t D) {n : G}
    (ht : t ∈ normalizer (omega1 D hD.comm : Set G))
    (hn : n ∈ normalizer (omega1 D hD.comm : Set G)) {w : AddMonoid.End (VSub hD)}
    (hτw : vConj hD t * w = (w + 1) * vConj hD t)
    (hnw : vConj hD n * w = w * vConj hD n) :
    vConj hD (t * n) * w = (w + 1) * vConj hD (t * n) := by
  rw [vConj_mul hD ht hn]
  calc (vConj hD t * vConj hD n) * w = vConj hD t * (vConj hD n * w) := by
        rw [mul_assoc]
    _ = vConj hD t * (w * vConj hD n) := by rw [hnw]
    _ = (vConj hD t * w) * vConj hD n := by rw [mul_assoc]
    _ = ((w + 1) * vConj hD t) * vConj hD n := by rw [hτw]
    _ = (w + 1) * (vConj hD t * vConj hD n) := by rw [mul_assoc]

private theorem ut_eq_of_central (p q r x y z : ZMod 2)
    (h01 : !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1] * (1 + Matrix.single 0 1 1) =
      (1 + Matrix.single 0 1 1) * !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1])
    (h12 : !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1] * (1 + Matrix.single 1 2 1) =
      (1 + Matrix.single 1 2 1) * !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1])
    (h23 : !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1] * (1 + Matrix.single 2 3 1) =
      (1 + Matrix.single 2 3 1) * !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1])
    (hne : !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1] ≠ 1) :
    !![1,p,q,r; 0,1,x,y; 0,0,1,z; 0,0,0,1] = 1 + Matrix.single 0 3 1 := by
  decide +revert

private theorem eq_of_mem_UT (g : GL (Fin 4) (ZMod 2))
    (hg : g ∈ CFSG.Quasithin.FFC.UT 4) :
    (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      !![1, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1,
          (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2,
          (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3;
         0, 1, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2,
          (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3;
         0, 0, 1, (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3;
         0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Quasithin.FFC.mem_UT.1 hg, CFSG.Quasithin.FFC.UT_diag hg]

private theorem isRep_conj_comm {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c) {s₀ s : G}
    {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hs₀ : IsRep A c s₀ M) (hs : IsRep A c s N)
    (hcomm : ∀ a ∈ A, s₀ * (s * a * s⁻¹) * s₀⁻¹ = s * (s₀ * a * s₀⁻¹) * s⁻¹)
    (hN : ∀ a ∈ A, s * a * s⁻¹ ∈ A) (hM : ∀ a ∈ A, s₀ * a * s₀⁻¹ ∈ A) :
    M * N = N * M := by
  have hall : ∀ u : Fin 4 → ZMod 2, (M * N) *ᵥ u = (N * M) *ᵥ u := by
    intro u
    obtain ⟨a, ha, rfl⟩ := hc.onto u
    have h1 := congrArg c (hcomm a ha)
    rw [hs₀ _ (hN a ha), hs a ha, hs _ (hM a ha), hs₀ a ha] at h1
    simpa only [Matrix.mulVec_mulVec] using h1
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

private theorem not_centralizes_A_of_conj_t (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {Q : Subgroup G} (hQ : QHyp L A D t Q)
    {g : G} (hgQ : g ∈ normalizer (Q : Set G)) (hgM : g ∉ normalizer (D : Set G)) {s₀ : G}
    (hsecond : ∀ v ∈ omega1 D hD.comm,
      (g⁻¹ * t * g) * v * (g⁻¹ * t * g)⁻¹ = (t * s₀) * v * (t * s₀)⁻¹) :
    ∃ a ∈ A, s₀ * a * s₀⁻¹ ≠ a := by
  by_contra h
  push Not at h
  apply hgM
  have hgV : g ∈ normalizer (omega1 D hD.comm : Set G) :=
    QHyp.mem_normalizer_omega1 hD hQ hgQ
  have hta : ∀ a ∈ A, t * a * t⁻¹ = a := by
    intro a ha
    have h' := H.comm_of_mem_L (W.S_le ((W.mem_A_iff a).1 ha).1)
    calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [h']
      _ = a := by group
  have huA : ∀ a ∈ A, (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ = a := by
    intro a ha
    calc (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹
        = (t * s₀) * a * (t * s₀)⁻¹ := hsecond a (H.A_le_omega1 W W2 hD ha)
      _ = t * (s₀ * a * s₀⁻¹) * t⁻¹ := by group
      _ = t * a * t⁻¹ := by rw [h a ha]
      _ = a := hta a ha
  have hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro a ha
    have hmemV : g * a * g⁻¹ ∈ omega1 D hD.comm :=
      (mem_normalizer_iff.1 hgV a).1 (H.A_le_omega1 W W2 hD ha)
    have hmemC : g * a * g⁻¹ ∈ centralizer ({t} : Set G) := by
      refine mem_centralizer_singleton_iff.2 ?_
      have h2 : t * (g * a * g⁻¹) * t⁻¹ = g * a * g⁻¹ := by
        calc t * (g * a * g⁻¹) * t⁻¹
            = g * ((g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹) * g⁻¹ := by group
          _ = g * a * g⁻¹ := by rw [huA a ha]
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hmem : g * a * g⁻¹ ∈ omega1 D hD.comm ⊓ centralizer ({t} : Set G) :=
      ⟨hmemV, hmemC⟩
    rwa [H.omega1_inf_centralizer_t W W2 hD] at hmem
  exact QHyp.mem_normalizer_D_of_conj_mem_A H W W2 hD h4 hQ
    (fun q hq => (mem_normalizer_iff.1 hgQ q).1 hq) hgA

theorem ThCyc.exists_mem_S_conj_eq (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (hsurj : ∀ g ∈ CFSG.Quasithin.FFC.UT 4, ∃ s ∈ S,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {T : Subgroup G} (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (D : Set G))
    (hST : S ≤ T) {y : G} (hy : y ∈ T) :
    ∃ s ∈ S, (∀ v ∈ omega1 D hD.comm, y * v * y⁻¹ = s * v * s⁻¹) ∨
      (∀ v ∈ omega1 D hD.comm, y * v * y⁻¹ = (t * s) * v * (t * s)⁻¹) := by
  classical
  have hTA : T ≤ normalizer (A : Set G) :=
    hTM.trans (H.normalizer_D_le_normalizer_A W W2 hD h4)
  have hTN : ∀ q ∈ T, ∀ a ∈ A, q * a * q⁻¹ ∈ A :=
    fun q hq a ha => (mem_normalizer_iff.1 (hTA hq) a).1 ha
  obtain ⟨m, hm⟩ := hc.exists_matHom T hTN
  let ρ : T →* GL (Fin 4) (ZMod 2) := m.toHomUnits
  have hρrep : ∀ q : T, IsRep A c (q : G) (ρ q) := fun q => by
    change IsRep A c (q : G) (m q)
    exact hm q
  have hUTle : (CFSG.Quasithin.FFC.UT 4 : Subgroup (GL (Fin 4) (ZMod 2))) ≤ ρ.range := by
    intro g hg
    obtain ⟨s, hsS, hsr⟩ := hsurj g hg
    have hsT : s ∈ T := hST hsS
    have hmats : ((ρ ⟨s, hsT⟩ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
      hc.rep_unique (hρrep ⟨s, hsT⟩) hsr
    exact ⟨⟨s, hsT⟩, Units.ext hmats⟩
  have hρp : IsPGroup 2 ρ.range :=
    hT2.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hrange : ρ.range = CFSG.Quasithin.FFC.UT 4 := by
    have h := (CFSG.Quasithin.FFC.UTSylow 4).is_maximal' hρp hUTle
    rwa [CFSG.Quasithin.FFC.coe_UTSylow] at h
  have hyUT : ρ ⟨y, hy⟩ ∈ CFSG.Quasithin.FFC.UT 4 := by
    rw [← hrange]
    exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨s, hsS, hsr⟩ := hsurj (ρ ⟨y, hy⟩) hyUT
  have hyA : y ∈ normalizer (A : Set G) := hTA hy
  have hsA : s ∈ normalizer (A : Set G) := mem_normalizer_A_of_mem_S W hsS
  have hkA : ∀ a ∈ A, (y * s⁻¹) * a * (y * s⁻¹)⁻¹ = a :=
    conj_mul_inv_centralizes_A hc hyA hsA (hρrep ⟨y, hy⟩) hsr
  have hsD : s ∈ normalizer (D : Set G) := mem_normalizer_D_of_mem_S H W W2 hD hsS
  have hkD : y * s⁻¹ ∈ normalizer (D : Set G) :=
    (normalizer (D : Set G)).mul_mem (hTM hy) ((normalizer (D : Set G)).inv_mem hsD)
  have hsV : s ∈ normalizer (omega1 D hD.comm : Set G) :=
    mem_normalizer_omega1_of_mem_S H W W2 hD hsS
  refine ⟨s, hsS, ?_⟩
  rcases H.mem_M0_or_inv_t_mul_mem_M0 W W2 hD h4 hb hkD with hkM0 | hkM0
  · left
    obtain ⟨n, hn, hact⟩ := ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 hD hkM0
    have hnB : n ∈ B := (W.mem_B_iff n hn.1).2 fun a ha => by
      have hna : n * a * n⁻¹ = a := by
        rw [← hact a (H.A_le_omega1 W W2 hD ha), hkA a ha]
      exact mul_inv_eq_iff_eq_mul.mp hna
    have hkV : ∀ v ∈ omega1 D hD.comm, (y * s⁻¹) * v * (y * s⁻¹)⁻¹ = v := by
      intro v hv
      rw [hact v hv, H.comm_omega1_of_mem_B W W2 hD hb hnB hv]
    intro v hv
    have hsv : s * v * s⁻¹ ∈ omega1 D hD.comm := (mem_normalizer_iff.1 hsV v).1 hv
    calc y * v * y⁻¹ = (y * s⁻¹) * (s * v * s⁻¹) * (y * s⁻¹)⁻¹ := by group
      _ = s * v * s⁻¹ := hkV _ hsv
  · right
    obtain ⟨n, hn, hact⟩ := ThCyc.exists_mem_inf_normalizer_conj_eq_of_mem_M0 hD hkM0
    have hnB : n ∈ B := (W.mem_B_iff n hn.1).2 fun a ha => by
      have hta : t * a * t⁻¹ = a := by
        have h := H.comm_of_mem_L (W.S_le ((W.mem_A_iff a).1 ha).1)
        calc t * a * t⁻¹ = (a * t) * t⁻¹ := by rw [h]
          _ = a := by group
      have hna : n * a * n⁻¹ = a := by
        rw [← hact a (H.A_le_omega1 W W2 hD ha)]
        calc (t⁻¹ * (y * s⁻¹)) * a * (t⁻¹ * (y * s⁻¹))⁻¹
            = t⁻¹ * ((y * s⁻¹) * a * (y * s⁻¹)⁻¹) * t := by group
          _ = t⁻¹ * a * t := by rw [hkA a ha]
          _ = a := by
            have htinv : t⁻¹ = t :=
              inv_eq_of_mul_eq_one_right (by rw [← sq]; exact H.sq_t)
            simpa [htinv] using hta
      exact mul_inv_eq_iff_eq_mul.mp hna
    have hkV : ∀ v ∈ omega1 D hD.comm,
        (t⁻¹ * (y * s⁻¹)) * v * (t⁻¹ * (y * s⁻¹))⁻¹ = v := by
      intro v hv
      rw [hact v hv, H.comm_omega1_of_mem_B W W2 hD hb hnB hv]
    have hkV' : ∀ v ∈ omega1 D hD.comm, (y * s⁻¹) * v * (y * s⁻¹)⁻¹ = t * v * t⁻¹ := by
      intro v hv
      have h1 := hkV v hv
      have h2 : (t⁻¹ * (y * s⁻¹)) * v * (t⁻¹ * (y * s⁻¹))⁻¹
          = t⁻¹ * ((y * s⁻¹) * v * (y * s⁻¹)⁻¹) * t := by group
      rw [h2] at h1
      calc (y * s⁻¹) * v * (y * s⁻¹)⁻¹
          = t * (t⁻¹ * ((y * s⁻¹) * v * (y * s⁻¹)⁻¹) * t) * t⁻¹ := by group
        _ = t * v * t⁻¹ := by rw [h1]
    intro v hv
    have hsv : s * v * s⁻¹ ∈ omega1 D hD.comm := (mem_normalizer_iff.1 hsV v).1 hv
    calc y * v * y⁻¹ = (y * s⁻¹) * (s * v * s⁻¹) * (y * s⁻¹)⁻¹ := by group
      _ = t * (s * v * s⁻¹) * t⁻¹ := hkV' _ hsv
      _ = (t * s) * v * (t * s)⁻¹ := by group

theorem ThLocalIn.isRep_of_central (W : ThLocalIn L S A B z) {c : G → (Fin 4 → ZMod 2)}
    (hc : IsCoord A c)
    (hS : ∀ s ∈ S, ∃ g ∈ CFSG.Quasithin.FFC.UT 4,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    (hsurj : ∀ g ∈ CFSG.Quasithin.FFC.UT 4, ∃ s ∈ S,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {s₀ : G} (hs₀ : s₀ ∈ S)
    (hcomm : ∀ s ∈ S, ∀ a ∈ A, s₀ * (s * a * s⁻¹) * s₀⁻¹ = s * (s₀ * a * s₀⁻¹) * s⁻¹)
    (hne : ∃ a ∈ A, s₀ * a * s₀⁻¹ ≠ a) :
    IsRep A c s₀ (1 + Matrix.single 0 3 1) := by
  classical
  obtain ⟨g, hgUT, hrep⟩ := hS s₀ hs₀
  have hg_eq := eq_of_mem_UT g hgUT
  have hM : ∀ a ∈ A, s₀ * a * s₀⁻¹ ∈ A := fun a ha =>
    W.conj_mem_A_of_mem_S hs₀ ha
  obtain ⟨s01, hs01S, hrep01⟩ :=
    ThLocalIn.exists_mem_S_isRep_of_unitriangular (S := S) (A := A) (c := c) hsurj
      (i := 0) (j := 1) (by decide)
  obtain ⟨s12, hs12S, hrep12⟩ :=
    ThLocalIn.exists_mem_S_isRep_of_unitriangular (S := S) (A := A) (c := c) hsurj
      (i := 1) (j := 2) (by decide)
  obtain ⟨s23, hs23S, hrep23⟩ :=
    ThLocalIn.exists_mem_S_isRep_of_unitriangular (S := S) (A := A) (c := c) hsurj
      (i := 2) (j := 3) (by decide)
  have h01 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (1 + Matrix.single 0 1 1) =
      (1 + Matrix.single 0 1 1) * (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    isRep_conj_comm hc hrep hrep01 (fun a ha => hcomm s01 hs01S a ha)
      (fun a ha => W.conj_mem_A_of_mem_S hs01S ha) hM
  have h12 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (1 + Matrix.single 1 2 1) =
      (1 + Matrix.single 1 2 1) * (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    isRep_conj_comm hc hrep hrep12 (fun a ha => hcomm s12 hs12S a ha)
      (fun a ha => W.conj_mem_A_of_mem_S hs12S ha) hM
  have h23 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (1 + Matrix.single 2 3 1) =
      (1 + Matrix.single 2 3 1) * (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
    isRep_conj_comm hc hrep hrep23 (fun a ha => hcomm s23 hs23S a ha)
      (fun a ha => W.conj_mem_A_of_mem_S hs23S ha) hM
  have hne1 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) ≠ 1 := by
    intro h1
    obtain ⟨a, ha, hne_a⟩ := hne
    refine hne_a (hc.inj _ (W.conj_mem_A_of_mem_S hs₀ ha) _ ha ?_)
    rw [show c (s₀ * a * s₀⁻¹) = (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ c a from
      hrep a ha, h1, Matrix.one_mulVec]
  have hg_final : (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + Matrix.single 0 3 1 := by
    rw [hg_eq]
    refine ut_eq_of_central ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1)
      ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2)
      ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3)
      ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 2)
      ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3)
      ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3) ?_ ?_ ?_ ?_
    · rwa [hg_eq] at h01
    · rwa [hg_eq] at h12
    · rwa [hg_eq] at h23
    · rwa [hg_eq] at hne1
  rwa [hg_final] at hrep

theorem ThCyc.exists_conj_t_eq_t_mul (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹) {c : G → (Fin 4 → ZMod 2)} (hc : IsCoord A c)
    (hsurj : ∀ g ∈ CFSG.Quasithin.FFC.UT 4, ∃ s ∈ S,
      IsRep A c s (g : Matrix (Fin 4) (Fin 4) (ZMod 2)))
    {Q T : Subgroup G} (hQ : QHyp L A D t Q) (hT : THyp S D Q t T)
    {g : G} (hgT : g ∈ normalizer (T : Set G)) (hgQ : g ∈ normalizer (Q : Set G))
    (hgM : g ∉ normalizer (D : Set G)) {w : AddMonoid.End (VSub hD)}
    (hwH : ∀ n ∈ L ⊓ normalizer (A : Set G), vConj hD n * w = w * vConj hD n)
    (hτw : vConj hD t * w * vConj hD t = w + 1)
    (hgw : vConj hD g * w = w * vConj hD g) :
    ∃ s₀ ∈ S,
      (∀ v ∈ omega1 D hD.comm,
        (g⁻¹ * t * g) * v * (g⁻¹ * t * g)⁻¹ = (t * s₀) * v * (t * s₀)⁻¹) ∧
      (∀ s ∈ S, ∀ v ∈ omega1 D hD.comm,
        s₀ * (s * v * s⁻¹) * s₀⁻¹ = s * (s₀ * v * s₀⁻¹) * s⁻¹) ∧
      ∃ a ∈ A, s₀ * a * s₀⁻¹ ≠ a := by
  classical
  have hgV : g ∈ normalizer (omega1 D hD.comm : Set G) :=
    QHyp.mem_normalizer_omega1 hD hQ hgQ
  have htV : t ∈ normalizer (omega1 D hD.comm : Set G) :=
    H.t_mem_normalizer_omega1 W W2 hD
  have hττ : vConj hD t * vConj hD t = 1 := H.vConj_t_mul_self W W2 hD
  have hτw' : vConj hD t * w = (w + 1) * vConj hD t := by
    have h := congrArg (fun x => x * vConj hD t) hτw
    simpa [mul_assoc, hττ] using h
  have hgiV : g⁻¹ ∈ normalizer (omega1 D hD.comm : Set G) :=
    (normalizer (omega1 D hD.comm : Set G)).inv_mem hgV
  have hgiw := vConj_inv_mul_commute hD hgV hgw
  have huT : g⁻¹ * t * g ∈ T := by
    simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) t).1 hT.t_mem
  have huV : g⁻¹ * t * g ∈ normalizer (omega1 D hD.comm : Set G) :=
    normalizer_D_le_normalizer_omega1 hD (hT.le_normalizer huT)
  have hu_w : vConj hD (g⁻¹ * t * g) * w = (w + 1) * vConj hD (g⁻¹ * t * g) :=
    vConj_conj_t_mul_w hD hgV htV hgw hτw'
  obtain ⟨s₀, hs₀S, hu_like⟩ :=
    H.exists_mem_S_conj_eq W W2 hD h4 hb hc hsurj hT.pgroup hT.le_normalizer hT.S_le huT
  have hs₀A : s₀ ∈ normalizer (A : Set G) := mem_normalizer_A_of_mem_S W hs₀S
  have hs₀V : s₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
    mem_normalizer_omega1_of_mem_S H W W2 hD hs₀S
  have hs₀w : vConj hD s₀ * w = w * vConj hD s₀ :=
    hwH s₀ ⟨W.S_le hs₀S, hs₀A⟩
  have hsecond : ∀ v ∈ omega1 D hD.comm,
      (g⁻¹ * t * g) * v * (g⁻¹ * t * g)⁻¹ = (t * s₀) * v * (t * s₀)⁻¹ := by
    rcases hu_like with h | h
    · exfalso
      have hρu_eq : vConj hD (g⁻¹ * t * g) = vConj hD s₀ :=
        vConj_eq_of_conj_eq hD huV hs₀V h
      have h1 : vConj hD s₀ * w = (w + 1) * vConj hD s₀ := by
        rw [← hρu_eq]
        exact hu_w
      have h2 : (w + 1) * vConj hD s₀ = w * vConj hD s₀ + vConj hD s₀ := by
        rw [add_mul, one_mul]
      have h3 : w * vConj hD s₀ = w * vConj hD s₀ + vConj hD s₀ := by
        rw [← h2, ← h1, hs₀w]
      have h4 : w * vConj hD s₀ + 0 = w * vConj hD s₀ + vConj hD s₀ := by
        simpa using h3
      have hzero : vConj hD s₀ = 0 := (add_left_cancel h4).symm
      exact vConj_ne_zero H W W2 hD hs₀V hzero
    · exact h
  have hρu_eq : vConj hD (g⁻¹ * t * g) = vConj hD t * vConj hD s₀ := by
    rw [vConj_eq_of_conj_eq hD huV ((normalizer _).mul_mem htV hs₀V) hsecond,
      vConj_mul hD htV hs₀V]
  have hcommS : ∀ s ∈ S, ∀ v ∈ omega1 D hD.comm,
      s₀ * (s * v * s⁻¹) * s₀⁻¹ = s * (s₀ * v * s₀⁻¹) * s⁻¹ := by
    intro s hsS v hv
    letI : Fintype S := Fintype.ofFinite S
    let Ffun : AddMonoid.End (VSub hD) → AddMonoid.End (VSub hD) :=
      fun X => vConj hD g⁻¹ * X * vConj hD g
    let R : Finset (AddMonoid.End (VSub hD)) :=
      (Finset.univ : Finset S).image (fun s : S => vConj hD (s : G))
    have hF_maps : ∀ X ∈ R, Ffun X ∈ R := by
      intro X hX
      obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 hX
      have hs'S : (s' : G) ∈ S := s'.2
      have hgsT : g⁻¹ * (s' : G) * g ∈ T := by
        simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) (s' : G)).1
          (hT.S_le hs'S)
      have hgsV : g⁻¹ * (s' : G) * g ∈ normalizer (omega1 D hD.comm : Set G) :=
        normalizer_D_le_normalizer_omega1 hD (hT.le_normalizer hgsT)
      have hs'V : (s' : G) ∈ normalizer (omega1 D hD.comm : Set G) :=
        mem_normalizer_omega1_of_mem_S H W W2 hD hs'S
      have h2 : vConj hD (g⁻¹ * (s' : G) * g) =
          vConj hD g⁻¹ * vConj hD (s' : G) * vConj hD g := by
        rw [vConj_mul hD ((normalizer _).mul_mem hgiV hs'V) hgV, vConj_mul hD hgiV hs'V]
      obtain ⟨s'', hs''S, hlike | hlike⟩ :=
        H.exists_mem_S_conj_eq W W2 hD h4 hb hc hsurj hT.pgroup hT.le_normalizer
          hT.S_le hgsT
      · refine Finset.mem_image.2 ⟨⟨s'', hs''S⟩, Finset.mem_univ _, ?_⟩
        have hs''V : s'' ∈ normalizer (omega1 D hD.comm : Set G) :=
          mem_normalizer_omega1_of_mem_S H W W2 hD hs''S
        have h1 : vConj hD (g⁻¹ * (s' : G) * g) = vConj hD s'' :=
          vConj_eq_of_conj_eq hD hgsV hs''V hlike
        exact h1.symm.trans h2
      · exfalso
        have hs''V : s'' ∈ normalizer (omega1 D hD.comm : Set G) :=
          mem_normalizer_omega1_of_mem_S H W W2 hD hs''S
        have hts''V : t * s'' ∈ normalizer (omega1 D hD.comm : Set G) :=
          (normalizer _).mul_mem htV hs''V
        have h1 : vConj hD (g⁻¹ * (s' : G) * g) = vConj hD (t * s'') :=
          vConj_eq_of_conj_eq hD hgsV hts''V hlike
        have hcomm_gs : vConj hD (g⁻¹ * (s' : G) * g) * w =
            w * vConj hD (g⁻¹ * (s' : G) * g) := by
          rw [h2]
          calc (vConj hD g⁻¹ * vConj hD (s' : G) * vConj hD g) * w
              = vConj hD g⁻¹ * vConj hD (s' : G) * (vConj hD g * w) := by noncomm_ring
            _ = vConj hD g⁻¹ * vConj hD (s' : G) * (w * vConj hD g) := by rw [hgw]
            _ = vConj hD g⁻¹ * (vConj hD (s' : G) * w) * vConj hD g := by noncomm_ring
            _ = vConj hD g⁻¹ * (w * vConj hD (s' : G)) * vConj hD g := by
                rw [hwH (s' : G) ⟨W.S_le hs'S, mem_normalizer_A_of_mem_S W hs'S⟩]
            _ = (vConj hD g⁻¹ * w) * vConj hD (s' : G) * vConj hD g := by noncomm_ring
            _ = (w * vConj hD g⁻¹) * vConj hD (s' : G) * vConj hD g := by rw [hgiw]
            _ = w * (vConj hD g⁻¹ * vConj hD (s' : G) * vConj hD g) := by noncomm_ring
        have h3 : vConj hD (t * s'') * w = (w + 1) * vConj hD (t * s'') :=
          vConj_t_mul_w hD htV hs''V hτw'
            (hwH (s'' : G) ⟨W.S_le hs''S, mem_normalizer_A_of_mem_S W hs''S⟩)
        have h4 : (w + 1) * vConj hD (t * s'') = w * vConj hD (t * s'') := by
          rw [← h3, ← h1, hcomm_gs, h1]
        have h5 : w * vConj hD (t * s'') + vConj hD (t * s'') =
            w * vConj hD (t * s'') + 0 := by
          rw [add_zero]
          rw [show w * vConj hD (t * s'') + vConj hD (t * s'') =
            (w + 1) * vConj hD (t * s'') by rw [add_mul, one_mul]]
          exact h4
        exact vConj_ne_zero H W W2 hD hts''V (add_left_cancel h5)
    have hF_inj : Function.Injective Ffun := by
      intro X Y hXY
      have hX : vConj hD g * (vConj hD g⁻¹ * X * vConj hD g) * vConj hD g⁻¹ = X := by
        calc vConj hD g * (vConj hD g⁻¹ * X * vConj hD g) * vConj hD g⁻¹
            = (vConj hD g * vConj hD g⁻¹) * X * (vConj hD g * vConj hD g⁻¹) := by
              noncomm_ring
          _ = X := by rw [vConj_mul_inv hD hgV, one_mul, mul_one]
      have hY : vConj hD g * (vConj hD g⁻¹ * Y * vConj hD g) * vConj hD g⁻¹ = Y := by
        calc vConj hD g * (vConj hD g⁻¹ * Y * vConj hD g) * vConj hD g⁻¹
            = (vConj hD g * vConj hD g⁻¹) * Y * (vConj hD g * vConj hD g⁻¹) := by
              noncomm_ring
          _ = Y := by rw [vConj_mul_inv hD hgV, one_mul, mul_one]
      have h := congrArg (fun Z => vConj hD g * Z * vConj hD g⁻¹) hXY
      rwa [hX, hY] at h
    have hcard : (R.image Ffun).card = R.card := Finset.card_image_of_injective R hF_inj
    have hsub : R.image Ffun ⊆ R := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hX
      exact hF_maps Y hY
    have heq : R.image Ffun = R := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    have hmem : vConj hD s ∈ R :=
      Finset.mem_image.2 ⟨⟨s, hsS⟩, Finset.mem_univ _, rfl⟩
    have hmem' : vConj hD s ∈ R.image Ffun := by rw [heq]; exact hmem
    obtain ⟨X, hXR, hXeq⟩ := Finset.mem_image.1 hmem'
    obtain ⟨s', -, hs'eq⟩ := Finset.mem_image.1 hXR
    have hF_eq : Ffun (vConj hD (s' : G)) = vConj hD s := by
      rw [hs'eq]
      exact hXeq
    have hs'V : (s' : G) ∈ normalizer (omega1 D hD.comm : Set G) :=
      mem_normalizer_omega1_of_mem_S H W W2 hD s'.2
    have hgs'T : g⁻¹ * (s' : G) * g ∈ T := by
      simpa using (mem_normalizer_iff.1 ((normalizer (T : Set G)).inv_mem hgT) (s' : G)).1
        (hT.S_le s'.2)
    have hgs'V : g⁻¹ * (s' : G) * g ∈ normalizer (omega1 D hD.comm : Set G) :=
      normalizer_D_le_normalizer_omega1 hD (hT.le_normalizer hgs'T)
    have hF_eq' : vConj hD (g⁻¹ * (s' : G) * g) = vConj hD s := by
      have h2 : vConj hD (g⁻¹ * (s' : G) * g) =
          vConj hD g⁻¹ * vConj hD (s' : G) * vConj hD g := by
        rw [vConj_mul hD ((normalizer _).mul_mem hgiV hs'V) hgV, vConj_mul hD hgiV hs'V]
      rw [h2]
      exact hF_eq
    have hu_comm : vConj hD (g⁻¹ * t * g) * vConj hD (g⁻¹ * (s' : G) * g) =
        vConj hD (g⁻¹ * (s' : G) * g) * vConj hD (g⁻¹ * t * g) := by
      have hcomm_gg : (g⁻¹ * t * g) * (g⁻¹ * (s' : G) * g) =
          (g⁻¹ * (s' : G) * g) * (g⁻¹ * t * g) := by
        calc (g⁻¹ * t * g) * (g⁻¹ * (s' : G) * g) = g⁻¹ * (t * (s' : G)) * g := by group
          _ = g⁻¹ * ((s' : G) * t) * g := by rw [← H.comm_of_mem_L (W.S_le s'.2)]
          _ = (g⁻¹ * (s' : G) * g) * (g⁻¹ * t * g) := by group
      rw [← vConj_mul hD huV hgs'V, ← vConj_mul hD hgs'V huV, hcomm_gg]
    have h1 : vConj hD t * vConj hD s₀ * vConj hD s =
        vConj hD s * vConj hD t * vConj hD s₀ := by
      have h := hu_comm
      rw [hF_eq', hρu_eq] at h
      exact h
    have h2 : vConj hD t * vConj hD s = vConj hD s * vConj hD t :=
      vConj_t_commute_of_mem_S H W W2 hD hsS
    have h3 : vConj hD s₀ * vConj hD s = vConj hD s * vConj hD s₀ := by
      calc vConj hD s₀ * vConj hD s
          = (vConj hD t * vConj hD t) * (vConj hD s₀ * vConj hD s) := by
            rw [hττ, one_mul]
        _ = vConj hD t * (vConj hD t * vConj hD s₀ * vConj hD s) := by noncomm_ring
        _ = vConj hD t * (vConj hD s * vConj hD t * vConj hD s₀) := by rw [h1]
        _ = (vConj hD t * vConj hD s) * vConj hD t * vConj hD s₀ := by noncomm_ring
        _ = (vConj hD s * vConj hD t) * vConj hD t * vConj hD s₀ := by rw [h2]
        _ = vConj hD s * vConj hD s₀ := by
            rw [show (vConj hD s * vConj hD t) * vConj hD t * vConj hD s₀
                = vConj hD s * (vConj hD t * vConj hD t) * vConj hD s₀ from by
              noncomm_ring, hττ, mul_one]
    have h4 := congrArg (fun f : AddMonoid.End (VSub hD) =>
      (f (AbelianSub.mk v hv)).val) h3
    have hsV : s ∈ normalizer (omega1 D hD.comm : Set G) :=
      mem_normalizer_omega1_of_mem_S H W W2 hD hsS
    simpa only [AddMonoid.End.coe_mul, Function.comp_apply, val_vConj_apply hD hs₀V,
      val_vConj_apply hD hsV, AbelianSub.val_mk] using h4
  exact ⟨s₀, hs₀S, hsecond, hcommS,
    not_centralizes_A_of_conj_t H W W2 hD h4 hQ hgQ hgM hsecond⟩

end CFSG.EvenSporadicStandard.ThStd
