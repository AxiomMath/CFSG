module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow
public import CFSG.Quasithin.Background.E1Invariance

public noncomputable section

open Matrix QuadraticMap
open scoped commutatorElement
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.GH74.GLS.IVK.Proofs2
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open CFSG.GH74.GLS.IVK.Proofs2.Sp48.O2Plane
open CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open CFSG.ComponentClassification.CatalogueBOrthogonal

namespace CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

abbrev localKConj (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  tPositiveDerivedConj F ⊔ localS F W G

abbrev localCConj (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  localKConj F W G ⊓ Subgroup.centralizer (tPositiveDerivedConj F :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q))

abbrev swapConjHom (F : FrameData Q) :
    TauCeti.QuadraticMap.orthogonalGroup Q →* TauCeti.QuadraticMap.orthogonalGroup Q :=
  (MulAut.conj F.sO).toMonoidHom

private theorem swapConjHom_apply (F : FrameData Q)
    (x : TauCeti.QuadraticMap.orthogonalGroup Q) :
    swapConjHom F x = F.sO * x * F.sO⁻¹ := rfl

theorem swapConjHom_injective (F : FrameData Q) : Function.Injective (swapConjHom F) :=
  (MulAut.conj F.sO).injective

theorem sO_mem_G (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    F.sO ∈ G :=
  hLG (sO_mem_derived F)

theorem sO_mem_P (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) : F.sO ∈ P := by
  rw [hP]
  refine ⟨?_, sO_mem_G F G hLG⟩
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)

private theorem betaBaseO_map_conj_s (F : FrameData Q) (D : Subgroup (O2 K)) :
    (betaBaseO F D).map (swapConjHom F) = betaBaseO F D := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨y, hy, rfl⟩
    rw [betaBaseO] at hy ⊢
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    rw [show F.betaHom p = F.betaO p.1 p.2 from FrameData.betaHom_apply (F := F) p]
    change swapConjHom F (F.betaO p.1 p.2) ∈ betaBaseO F D
    have hconj : swapConjHom F (F.betaO p.1 p.2) = F.betaO p.2 p.1 := by
      rw [swapConjHom_apply]
      have hs : F.sO⁻¹ = F.sO := inv_eq_of_mul_eq_one_right F.sO_mul_self
      rw [hs]
      exact F.sO_betaO_conj' p.1 p.2
    rw [hconj]
    exact Subgroup.mem_map.mpr ⟨(p.2, p.1), ⟨hp.2, hp.1⟩, rfl⟩
  · rw [Subgroup.card_map_of_injective (swapConjHom_injective F)]

theorem localS_map_conj_s (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    (localS F W G).map (swapConjHom F) = localS F W G := by
  letI : G.Normal := Subgroup.Normal.of_commutator_le
    (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  have hG : Subgroup.map (swapConjHom F) G = G := by
    simpa using Subgroup.Normal.map_conj_eq G F.sO
  rw [localS, Subgroup.map_inf _ _ (swapConjHom F) (swapConjHom_injective F),
    betaBaseO_map_conj_s, hG]

theorem localKConj_eq_map (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    localKConj F W G =
      (localK F W G).map (swapConjHom F) := by
  rw [localKConj, localK, tPositiveDerivedConj, Subgroup.map_sup,
    localS_map_conj_s F W G hLG]

@[expose]
noncomputable def localKConjEquiv (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    localK F W G ≃* localKConj F W G :=
  (Subgroup.equivMapOfInjective (localK F W G) (swapConjHom F)
    (swapConjHom_injective F)).trans
  (MulEquiv.subgroupCongr (localKConj_eq_map F W G hLG).symm)

@[expose]
noncomputable def localPiConj (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    localKConj F W G →* CFSG.GorensteinWalter.PGL2 K :=
  (localPi F hodd W G).comp (localKConjEquiv F W G hLG).symm.toMonoidHom

theorem localPiConj_surjective (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    Function.Surjective (localPiConj F hodd W G hLG) :=
  (localPi_surjective F hodd h3 W G hLG hGSO).comp
    (localKConjEquiv F W G hLG).symm.surjective

theorem localKConjEquiv_apply_val (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (z : localK F W G) :
    ((localKConjEquiv F W G hLG z).val :
      TauCeti.QuadraticMap.orthogonalGroup Q) = swapConjHom F z.val := by
  rw [localKConjEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply]

theorem localKConjEquiv_symm_apply_val (F : FrameData Q)
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (y : localKConj F W G) :
    (((localKConjEquiv F W G hLG).symm y).val :
      TauCeti.QuadraticMap.orthogonalGroup Q) =
      F.sO⁻¹ * y.val * F.sO := by
  have h := localKConjEquiv_apply_val F W G hLG
    ((localKConjEquiv F W G hLG).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  have hz : F.sO⁻¹ * (y.val) * F.sO =
      (((localKConjEquiv F W G hLG).symm y).val :
        TauCeti.QuadraticMap.orthogonalGroup Q) := by
    rw [h, swapConjHom_apply]
    group
  exact hz.symm

private theorem mem_centralizer_localX_iff_mem_centralizer_conj (F : FrameData Q)
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (y : localKConj F W G) :
    (((localKConjEquiv F W G hLG).symm y).val :
      TauCeti.QuadraticMap.orthogonalGroup Q) ∈
        Subgroup.centralizer (localX F :
          Set (TauCeti.QuadraticMap.orthogonalGroup Q)) ↔
      y.val ∈ Subgroup.centralizer (tPositiveDerivedConj F :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x' hx'
    rw [tPositiveDerivedConj] at hx'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    have hz := h x hx
    have hconj : Commute (F.sO * (((localKConjEquiv F W G hLG).symm y).val) * F.sO⁻¹)
        (F.sO * x * F.sO⁻¹) := by
      simpa [MulAut.conj_apply] using (Commute.conj_iff F.sO).mpr (Commute.symm hz)
    have hzval := localKConjEquiv_symm_apply_val F W G hLG y
    have hyeq : F.sO * (((localKConjEquiv F W G hLG).symm y).val) * F.sO⁻¹ =
        y.val := by rw [hzval]; group
    rw [hyeq] at hconj
    exact Commute.symm hconj
  · intro h x hx
    have hx' : F.sO * x * F.sO⁻¹ ∈ tPositiveDerivedConj F := by
      rw [tPositiveDerivedConj]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hy'' : (F.sO * x * F.sO⁻¹) * y.val = y.val * (F.sO * x * F.sO⁻¹) :=
      h (F.sO * x * F.sO⁻¹) hx'
    have hzval := localKConjEquiv_symm_apply_val F W G hLG y
    rw [hzval]
    calc x * (F.sO⁻¹ * y.val * F.sO)
        = F.sO⁻¹ * ((F.sO * x * F.sO⁻¹) * y.val) * F.sO := by group
      _ = F.sO⁻¹ * (y.val * (F.sO * x * F.sO⁻¹)) * F.sO := by rw [hy'']
      _ = (F.sO⁻¹ * y.val * F.sO) * x := by group

theorem localPiConj_ker_eq (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    (localPiConj F hodd W G hLG).ker =
      (localCConj F W G).subgroupOf (localKConj F W G) := by
  ext y
  constructor
  · intro hy
    rw [Subgroup.mem_subgroupOf]
    refine ⟨y.property, ?_⟩
    have hker : (localKConjEquiv F W G hLG).symm y ∈ (localPi F hodd W G).ker := hy
    rw [localPi_ker_eq F hodd h3 W G] at hker
    have hmem := Subgroup.mem_subgroupOf.mp hker
    exact (mem_centralizer_localX_iff_mem_centralizer_conj F W G hLG y).mp hmem.2
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨_, hyC⟩ := hy
    show localPiConj F hodd W G hLG y = 1
    change localPi F hodd W G ((localKConjEquiv F W G hLG).symm y) = 1
    have hmem : (localKConjEquiv F W G hLG).symm y ∈ (localPi F hodd W G).ker := by
      rw [localPi_ker_eq F hodd h3 W G]
      exact Subgroup.mem_subgroupOf.mpr
        ⟨((localKConjEquiv F W G hLG).symm y).property,
          (mem_centralizer_localX_iff_mem_centralizer_conj F W G hLG y).mpr hyC⟩
    exact hmem

theorem localPiConj_ker_isPGroup (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    IsPGroup 2 (localPiConj F hodd W G hLG).ker := by
  intro y
  have hy : localPi F hodd W G ((localKConjEquiv F W G hLG).symm y) = 1 := y.property
  obtain ⟨k, hk⟩ := localPi_ker_isPGroup F hodd h3 W G hLG hGSO
    ⟨(localKConjEquiv F W G hLG).symm y, hy⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  have hkval : (((localKConjEquiv F W G hLG).symm y) ^ (2 ^ k) : localK F W G) = 1 :=
    congrArg Subtype.val hk
  have h1 : (localKConjEquiv F W G hLG
      ((localKConjEquiv F W G hLG).symm y.val)) ^ (2 ^ k) = 1 := by
    rw [← map_pow, hkval, map_one]
  simpa using h1

theorem localS_sylowIn_KConj (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    CFSG.Quasithin.IsSylowIn 2 (localS F W G) (localKConj F W G) := by
  have h := (CFSG.Quasithin.E1.isSylowIn_map_mulEquiv (e := MulAut.conj F.sO)
    (P := localS F W G) (H := localK F W G)).mpr
    (localS_sylowIn_K F hodd W G hLG hGSO)
  rw [show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj F.sO)) (localS F W G) =
        localS F W G from by
        simpa [swapConjHom] using localS_map_conj_s F W G hLG,
      show Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj F.sO)) (localK F W G) =
        localKConj F W G from by
        simpa [swapConjHom] using (localKConj_eq_map F W G hLG).symm] at h
  exact h

theorem localS_eq_P_inf_KConj (F : FrameData Q) (hodd : Odd (Nat.card K))
    (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) :
    localS F W G = P ⊓ localKConj F W G := by
  have hmap : (P ⊓ localK F W G).map (swapConjHom F) = P ⊓ localKConj F W G := by
    have hPmap : Subgroup.map (swapConjHom F) P = P := by
      simpa [swapConjHom] using
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (sO_mem_P F W G hLG P hP)))
    rw [Subgroup.map_inf _ _ (swapConjHom F) (swapConjHom_injective F),
      hPmap, localKConj_eq_map F W G hLG]
  rw [← hmap, ← localS_eq_P_inf_K F hodd W G hLG P hP]
  exact (localS_map_conj_s F W G hLG).symm

theorem betaBaseO_le_centralizer_zO (F : FrameData Q) (D : Subgroup (O2 K)) :
    betaBaseO F D ≤ Subgroup.centralizer ({F.zO} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  intro g hg
  rw [betaBaseO] at hg
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
  rw [show F.betaHom p = F.betaO p.1 p.2 from FrameData.betaHom_apply (F := F) p]
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact betaO_commute_zO F p.1 p.2

theorem P_map_conj_s (F : FrameData Q) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hP : P = wreathO F W.D ⊓ G) :
    P.map (swapConjHom F) = P := by
  letI : G.Normal := Subgroup.Normal.of_commutator_le
    (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  have hG : Subgroup.map (swapConjHom F) G = G := by
    simpa using Subgroup.Normal.map_conj_eq G F.sO
  have hTw : Subgroup.map (swapConjHom F) (wreathO F W.D) = wreathO F W.D := by
    have hs : F.sO ∈ wreathO F W.D :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    simpa [swapConjHom] using
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs))
  rw [hP, Subgroup.map_inf _ _ (swapConjHom F) (swapConjHom_injective F), hTw, hG]

theorem XConj_le_G (F : FrameData Q)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G) :
    tPositiveDerivedConj F ≤ G := by
  letI : G.Normal := Subgroup.Normal.of_commutator_le
    (G := TauCeti.QuadraticMap.orthogonalGroup Q) hLG
  rintro x ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using
    (inferInstance : G.Normal).conj_mem y (localX_le_G F G hLG hy) F.sO

theorem localS_common_centralizer_eq_bot (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K) (W : FiveDimensionalWreathData F)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) :
    localS F W G ⊓ Subgroup.centralizer (localX F :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) ⊓
      Subgroup.centralizer (tPositiveDerivedConj F :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hgS : g ∈ localS F W G := hg.1.1
  have hgX : g ∈ Subgroup.centralizer (localX F :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := hg.1.2
  have hgX' : g ∈ Subgroup.centralizer (tPositiveDerivedConj F :
    Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := hg.2
  have hgSO : g ∈ Q.specialOrthogonalWithin :=
    betaBaseO_le_SO F W.D hgS.1
  have hgt : Commute g F.tO :=
    Subgroup.mem_centralizer_singleton_iff.mp (localS_le_C0 F W G hgS)
  have hgz : Commute g F.zO :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (betaBaseO_le_centralizer_zO F W.D hgS.1)
  have hgXc : ∀ x ∈ localX F, Commute g x := by
    rw [Subgroup.mem_centralizer_iff] at hgX
    intro x hx
    exact (hgX x hx).symm
  have hgX'c : ∀ x ∈ tPositiveDerivedConj F, Commute g x := by
    rw [Subgroup.mem_centralizer_iff] at hgX'
    intro x hx
    exact (hgX' x hx).symm
  have hgone := tPositive_common_centralizer_eq_one F hodd h3 g hgSO hgt hgz hgXc hgX'c
  simpa using hgone

structure TPositiveLocalPackageConj (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin) where
  base : TPositiveLocalPackage F hodd h3 G hLG hGSO
  X_conj_le_G : tPositiveDerivedConj F ≤ G
  X_conj_le_KConj : tPositiveDerivedConj F ≤ localKConj F base.W G
  K_conj_eq_map : localKConj F base.W G =
    (localK F base.W G).map (swapConjHom F)
  S_map_conj_s : (localS F base.W G).map (swapConjHom F) = localS F base.W G
  P_map_conj_s : base.P.map (swapConjHom F) = base.P
  s_mem_P : F.sO ∈ base.P
  S_sylow_KConj : CFSG.Quasithin.IsSylowIn 2 (localS F base.W G)
    (localKConj F base.W G)
  S_eq_P_inf_KConj : localS F base.W G = base.P ⊓ localKConj F base.W G
  piConj_surjective : Function.Surjective (localPiConj F hodd base.W G hLG)
  piConj_ker_eq : (localPiConj F hodd base.W G hLG).ker =
    (localCConj F base.W G).subgroupOf (localKConj F base.W G)
  piConj_ker_isPGroup : IsPGroup 2 (localPiConj F hodd base.W G hLG).ker
  common_centralizer : localS F base.W G ⊓ Subgroup.centralizer (localX F :
      Set (TauCeti.QuadraticMap.orthogonalGroup Q)) ⊓
      Subgroup.centralizer (tPositiveDerivedConj F :
        Set (TauCeti.QuadraticMap.orthogonalGroup Q)) = ⊥

@[expose]
noncomputable def conjugatePackageOf (F : FrameData Q) (hodd : Odd (Nat.card K))
    (h3 : 3 < Nat.card K)
    (G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hLG : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G)
    (hGSO : G ≤ Q.specialOrthogonalWithin)
    (pkg : TPositiveLocalPackage F hodd h3 G hLG hGSO) :
    TPositiveLocalPackageConj F hodd h3 G hLG hGSO where
  base := pkg
  X_conj_le_G := XConj_le_G F G hLG
  X_conj_le_KConj := le_sup_left
  K_conj_eq_map := localKConj_eq_map F pkg.W G hLG
  S_map_conj_s := localS_map_conj_s F pkg.W G hLG
  P_map_conj_s := P_map_conj_s F pkg.W G hLG pkg.P pkg.hPw
  s_mem_P := sO_mem_P F pkg.W G hLG pkg.P pkg.hPw
  S_sylow_KConj := localS_sylowIn_KConj F hodd pkg.W G hLG hGSO
  S_eq_P_inf_KConj := localS_eq_P_inf_KConj F hodd pkg.W G hLG pkg.P pkg.hPw
  piConj_surjective := localPiConj_surjective F hodd h3 pkg.W G hLG hGSO
  piConj_ker_eq := localPiConj_ker_eq F hodd h3 pkg.W G hLG
  piConj_ker_isPGroup := localPiConj_ker_isPGroup F hodd h3 pkg.W G hLG hGSO
  common_centralizer := localS_common_centralizer_eq_bot F hodd h3 pkg.W G hLG hGSO

