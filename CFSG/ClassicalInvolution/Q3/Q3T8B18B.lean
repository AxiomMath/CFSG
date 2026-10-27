module

public import CFSG.ClassicalInvolution.Q3.Q3T8B18A
public import CFSG.ClassicalInvolution.Q3.Q3T8B14L
public import CFSG.ClassicalInvolution.Q3.Q3T8B13
public import CFSG.ClassicalInvolution.Q3.Q3T8AF02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.Thompson

section Shape

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem eq_partner_of_mem_omegaNbr_tq (hΩ : HypOmegaMod Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) {A B : Subgroup G} {a b : G}
    (ha : IsUniqueInvolution A a) (hb : IsUniqueInvolution B b) (hBA : B ∈ omegaNbr Ω A)
    (hno : ∀ L : Subgroup G, L ∈ omegaNbr Ω A → L ∈ omegaNbr Ω B → False)
    {M : Subgroup G} (hM : M ∈ Q3NL.tqMembers3 Ω (a * b)) (hMA : M ∈ omegaNbr Ω A) : M = B := by
  by_contra hMB
  obtain ⟨ℓ, hℓ⟩ := hΩ.exists_uniqueInvolution hM.1
  have haM : a ∈ trivialOnQuot M := (mem_tqMembers3_of_omegaNbr hΩ hnt ha hMA hℓ).2
  have hbM : b ∈ trivialOnQuot M := by
    have hb' : b = a * (a * b) := by rw [← mul_assoc, ha.sq, one_mul]
    rw [hb']
    exact Subgroup.mul_mem _ haM hM.2
  have hcomm : ⁅Subgroup.zpowers b, M⁆ ≤ oddCoreOf M :=
    Subgroup.commutator_le.mpr fun x hx y hy =>
      (mem_trivialOnQuot_iff.mp (Subgroup.zpowers_le.mpr hbM hx)).2 y hy
  obtain ⟨P, hP, hPc⟩ := AscE184Sect.exists_isSylow2In_centralizer
    (Q3KB.isPGroup_zpowers_of_sq hb.sq) hcomm
  have hPc' : P ≤ Subgroup.centralizer ({b} : Set G) := by
    rwa [centralizer_zpowers_eq_singleton'] at hPc
  have hPset : P ∈ RSet Ω := mem_RSet_of_isSylow2In hM.1 hP
  have hBM : B ∈ omegaNbr Ω M :=
    mem_omegaNbr_of_centralizes hΩ hM.1 hBA.1 (fun h => hMB h.symm) hb hPset hP.1
      (fun r hr => Subgroup.mem_centralizer_singleton_iff.mp (hPc' hr))
  exact hno M hMA (Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hM.1 hBA.1 hBM)

theorem layerShape3 (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    (h28 : ∀ {L : Subgroup G} {u : G}, L ∈ omegaNbr Ω K → L ∈ omegaNbr Ω J →
      IsUniqueInvolution L u → u = z * t)
    {B : Subgroup (Q3T7.layerQuot3 Ω (z * t))}
    (hB : B ∈ dstarComp (Q3T7.layerFam3 Ω (z * t)) (Layer.layerImg3 Ω (z * t) K)) :
    B = Layer.layerImg3 Ω (z * t) K ∨ B = Layer.layerImg3 Ω (z * t) J := by
  classical
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hXK : T8.XMem Ω (z * t) K := Layer.xMem_zt3 hs
  have hXJ : T8.XMem Ω (z * t) J := T8V.xMem_J hs
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := hXK.mem_tqMembers3 hΩ hx
  have hJt : J ∈ Q3NL.tqMembers3 Ω (z * t) := hXJ.mem_tqMembers3 hΩ hx
  have hs3 : Q3.Disc3.AscStand3 Ω K := hs.stand.toStand3
  have hL : Layer.LayerHyp Ω (z * t) := Layer.LayerHyp.of_stand3 hs3 hx ⟨K, hKt⟩
  have hn21 : K ∈ omegaNbr Ω J :=
    Q3CL.T3.omegaNbr_symm Disconnected.AschTight.Sec6Gen.l6_2Gen hΩ hs.stand.mem hs.hJ.1 hs.hJ
  have hKJ : ∀ {M : Subgroup G}, M ∈ Q3NL.tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω K → M = J :=
    fun hM hMK => eq_partner_of_mem_omegaNbr_tq hΩ hnt hs.hz hs.ht hs.hJ
      (fun L h1 h2 => no_common_nbr_E4 hs hE h28 h1 h2) hM hMK
  have hJK : ∀ {M : Subgroup G}, M ∈ Q3NL.tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω J → M = K :=
    fun {M} hM hMJ => by
      have hM' : M ∈ Q3NL.tqMembers3 Ω (t * z) := hzt ▸ hM
      exact eq_partner_of_mem_omegaNbr_tq hΩ hnt hs.ht hs.hz hn21
        (fun L h1 h2 => no_common_nbr_E4 hs hE h28 h2 h1) hM' hMJ
  have hcen : ∀ {n : G}, n ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) →
      n ∈ Subgroup.centralizer ({z * t} : Set G) := fun {n} hn =>
    (T8.cenZ_eq_centralizer (z * t)) ▸
      Layer.exactLayer3_le_cenZ Ω (z * t) (oddCoreOf_le_self _ hn)
  have step : ∀ {X : Subgroup G}, X ∈ Q3NL.tqMembers3 Ω (z * t) →
      (∀ {M : Subgroup G}, M ∈ Q3NL.tqMembers3 Ω (z * t) → M ∈ omegaNbr Ω X →
        Layer.layerImg3 Ω (z * t) M = Layer.layerImg3 Ω (z * t) K ∨
          Layer.layerImg3 Ω (z * t) M = Layer.layerImg3 Ω (z * t) J) →
      ∀ {B' : Subgroup (Q3T7.layerQuot3 Ω (z * t))},
        dstarAdj (Q3T7.layerFam3 Ω (z * t)) (Layer.layerImg3 Ω (z * t) X) B' →
          B' = Layer.layerImg3 Ω (z * t) K ∨ B' = Layer.layerImg3 Ω (z * t) J := by
    intro X hXt hnbr B' hadj
    obtain ⟨hBΦ, hadj'⟩ := hadj
    obtain ⟨M, hMt, hMB⟩ : ∃ M ∈ Q3NL.tqMembers3 Ω (z * t), Layer.layerImg3 Ω (z * t) M = B' := by
      obtain ⟨_, ⟨L₀, ⟨⟨M, hM, rfl⟩, -⟩, hLY, rfl⟩, hb⟩ := hBΦ
      exact ⟨M, hM, hb⟩
    have hM' : ∃ M' : Subgroup G, M' ∈ Q3NL.tqMembers3 Ω (z * t) ∧
        Layer.layerImg3 Ω (z * t) M' = B' ∧ M' ∈ omegaStarNbr Ω X := by
      rcases hadj' with h | h
      · rw [← hMB] at h
        obtain ⟨n, hn, hmn⟩ := Layer.exists_oddCore_conj_omegaStarNbr3 hL hXt hMt h
        have h1 := omegaStarNbr_conj hΩ.conjInvariant hmn n⁻¹
        rw [conjSub_inv_conjSub] at h1
        have hninv : n⁻¹ ∈ oddCoreOf (Q3NL.exactLayer3 Ω (z * t)) := (oddCoreOf _).inv_mem hn
        exact ⟨conjSub n⁻¹ M,
          Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant (hcen hninv) hMt,
          (Layer.layerImg3_conj_of_mem_oddCore hninv).trans hMB, h1⟩
      · rw [← hMB] at h
        obtain ⟨n, hn, hmn⟩ := Layer.exists_oddCore_conj_omegaStarNbr3 hL hMt hXt h
        exact ⟨conjSub n M,
          Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant (hcen hn) hMt,
          (Layer.layerImg3_conj_of_mem_oddCore hn).trans hMB,
          Q3T6.Mu.omegaStarNbr_symm hΩ (hΩ.conjInvariant n M hMt.1) hXt.1 hmn⟩
    obtain ⟨M', hM't, hM'B, hM'X⟩ := hM'
    rw [← hM'B]
    exact hnbr hM't (omegaStarNbr_imp_omegaNbr_E4 hs hE hXt.1 hM'X)
  have hmain : ∀ {B' : Subgroup (Q3T7.layerQuot3 Ω (z * t))},
      Relation.ReflTransGen (dstarAdj (Q3T7.layerFam3 Ω (z * t))) (Layer.layerImg3 Ω (z * t) K) B' →
        B' = Layer.layerImg3 Ω (z * t) K ∨ B' = Layer.layerImg3 Ω (z * t) J := by
    intro B' hB'
    induction hB' with
    | refl => exact Or.inl rfl
    | tail _ hadj ih =>
      rcases ih with h | h
      · rw [h] at hadj
        exact step hKt (fun hM hMK => Or.inr (by rw [hKJ hM hMK])) hadj
      · rw [h] at hadj
        exact step hJt (fun hM hMJ => Or.inl (by rw [hJK hM hMJ])) hadj
  exact hmain hB

theorem layerShapeAt_of_shape (hs : Std8 Ω K J S R T W z t) (hE : MuIsoE4 Ω W)
    (h28 : ∀ {L : Subgroup G} {u : G}, L ∈ omegaNbr Ω K → L ∈ omegaNbr Ω J →
      IsUniqueInvolution L u → u = z * t) : LayerShapeAt Ω K J (z * t) := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hx : z * t * (z * t) = 1 := Q3CL.T8.mul_self_zt hΩ hs.hz hs.hJ hs.ht
  have hKt : K ∈ Q3NL.tqMembers3 Ω (z * t) := (Layer.xMem_zt3 hs).mem_tqMembers3 hΩ hx
  by_cases hconn : T3.DStarConnected (Q3T7.layerFam3 Ω (z * t))
  · right
    intro M hM
    exact layerShape3 hs hE h28 (hconn _ (Layer.layerImg3_mem hKt) _ hM)
  · left
    exact hconn

end Shape

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
