module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7SCT3
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Alpha
public import CFSG.ClassicalInvolution.Asc77.AscT8V4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8.T21

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section Thin


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_std8A7 (hs : Hat2A7S.Std2A7 Ω K) (hnt : ∀ K' ∈ twinSet Ω K, K' = K) {z t : G}
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G), Hat2A7S.Std8A7 Ω K J S R T W z t := by
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨hJΩ, hJK, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3.Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    Thompson.le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { stand := hs
      noTwins := hnt
      hz := hz
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hs.mem hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

theorem le_layerRes_of_isPGroup (hΩ : HypOmegaGen Ω)
    (hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u) {x : G} (hx : x * x = 1)
    {M : Subgroup G} (hM : T8.XMem Ω x M) {A : Subgroup G} (hA : IsPGroup 2 ↥A) (hAM : A ≤ M)
    (hAx : A ≤ T8.cenZ x) : A ≤ T8.layerRes x M := by
  obtain ⟨P, hP, hAP⟩ := IsSylow2In.exists_ge hA (le_inf hAM hAx)
  have hCK : M ⊓ T8.cenZ x ≤ M := inf_le_left
  obtain ⟨Qs, hQs, -⟩ := IsSylow2In.exists_ge (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup G))
    (bot_le : (⊥ : Subgroup G) ≤ T8.layerRes x M)
  have hQK : IsSylow2In Qs M := Asc77.T8.XMem.isSylow2In_of_layerRes hΩ hcls hx hM hQs
  have hQC : IsSylow2In Qs (M ⊓ T8.cenZ x) :=
    T8.isSylow2In_of_le_of_le hQK (hQs.1.trans (T8.layerRes_le_inf x M)) hCK
  obtain ⟨c, hcC, hcQ⟩ := exists_conj_of_isSylow2In hQC hP
  have hcN : c ∈ Subgroup.normalizer (T8.layerRes x M : Set G) :=
    T8.mem_normalizer_layerRes (Subgroup.le_normalizer hcC.1) hcC.2
  have hPle : P ≤ T8.layerRes x M := by
    rw [← hcQ]
    calc conjSub c Qs ≤ conjSub c (T8.layerRes x M) := conjSub_mono hQs.1
      _ = T8.layerRes x M := mem_normalizer_iff_conjSub_eq.mp hcN
  exact hAP.trans hPle

theorem core26_of_thin [IsSimpleGroup G] (hs : Asc77.Std8 Ω K J S R T W z t)
    (th1 : ∀ J₁ ∈ omegaNbr Ω K, ∀ J₂ ∈ omegaNbr Ω K,
      ∃ q ∈ oddCoreOf (T8.layerJoin Ω z), J₂ = conjSub q J₁)
    (th2 : ∀ A ∈ omegaNbr Ω K, ∀ B ∈ omegaNbr Ω K, B ∉ omegaNbr Ω A) :
    Asc77.T8R.Core.Core26 Ω K J S R T z t := by
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hcls : ∀ L ∈ Ω, ∃ u : G, Hat2A7.IsClassical2A7 ⊤ L u := hs.stand.std.classical
  have hw : ∀ L ∈ Ω, A7Witness L := witness_of_pre hs.stand.std.toPre2A7
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hTΩ hTJ
  have h8R := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have h8T := Sec6Gen.eight_le_of_mem_RSet hΩ hTΩ
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hs.hz hRK hRsyl.2.1 (by omega)
  have htT : t ∈ T := mem_of_isUniqueInvolution_of_isPGroup hs.ht hTJ hTsyl.2.1 (by omega)
  have hztc : z * t = t * z := Q3.Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hQodd : Odd (Nat.card (oddCoreOf (T8.layerJoin Ω z))) := odd_natCard_oddCoreOf _
  have hzcen : z ∈ T8.cenZ z := T8.mem_cenZ_iff.mpr rfl
  have htcen : t ∈ T8.cenZ z := T8.mem_cenZ_iff.mpr hztc.symm
  have hzN : z ∈ Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
    Asc77.T8.mem_normalizer_oddCoreOf_layerJoin hΩ hzcen
  have htN : t ∈ Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
    Asc77.T8.mem_normalizer_oddCoreOf_layerJoin hΩ htcen
  have hqmem : ∀ q ∈ oddCoreOf (T8.layerJoin Ω z),
      q * (t * q⁻¹ * t⁻¹) ∈ oddCoreOf (T8.layerJoin Ω z) := fun q hq =>
    (oddCoreOf _).mul_mem hq
      ((Subgroup.mem_normalizer_iff.mp htN q⁻¹).mp ((oddCoreOf _).inv_mem hq))
  refine ⟨?_, ?_, ?_⟩
  ·
    intro P hP hPS
    by_contra hcon
    push Not at hcon
    obtain ⟨M, hM, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
    have hP8 := Sec6Gen.eight_le_of_mem_RSet hΩ hP
    have hMK : M ≠ K := by
      rintro rfl
      exact hcon.1 (Asc77.T8R.eq_of_isSylow2In_of_le_sylow hPM hRsyl hPS hRS)
    have hMJ : M ≠ J := by
      rintro rfl
      exact hcon.2 (Asc77.T8R.eq_of_isSylow2In_of_le_sylow hPM hTsyl hPS hTS)
    have hcR : Commutes P R := Asc77.l6_7_proved G Ω hΩ S P hP R hRΩ hPS hRS hcon.1
    have hcT : Commutes P T := Asc77.l6_7_proved G Ω hΩ S P hP T hTΩ hPS hTS hcon.2
    have hPcz : P ≤ Subgroup.centralizer ({z} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcR x hx z hzR)
    have hPct : P ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcT x hx t htT)
    have hPNK : P ≤ Subgroup.normalizer (K : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hM (Ne.symm hMK) hs.hz hPM.1 hPM.2.1
        (by omega) hPcz
    have hPNJ : P ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hJΩ hM (Ne.symm hMJ) hs.ht hPM.1 hPM.2.1
        (by omega) hPct
    exact th2 J hs.hJ M ⟨hM, hMK, P, hP, hPM.1, hPNK⟩ ⟨hM, hMJ, P, hP, hPM.1, hPNJ⟩
  ·
    intro n hn
    refine ⟨oddCoreOf (T8.layerJoin Ω z), hQodd, ?_⟩
    rcases hn with hn | hn
    · have hnz : n * z * n⁻¹ = z := hs.hz.conj_eq hn
      have hJn : conjSub n J ∈ omegaNbr Ω K := by
        have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
        rwa [hn] at this
      obtain ⟨q, hq, hqJ⟩ := th1 J hs.hJ (conjSub n J) hJn
      have hnt : n * t * n⁻¹ = q * t * q⁻¹ := by
        have h1 : IsUniqueInvolution (conjSub q J) (n * t * n⁻¹) := hqJ ▸ hs.ht.conj n
        exact ((hs.ht.conj q).eq h1).symm
      have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = z * (q * (t * q⁻¹ * t⁻¹)) * z⁻¹ := by
        calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
          _ = z * (q * t * q⁻¹) * (z * t)⁻¹ := by rw [hnz, hnt]
          _ = z * (q * (t * q⁻¹ * t⁻¹)) * z⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hzN _).mp (hqmem q hq)
    · have hnt : n * t * n⁻¹ = z := by
        have := hs.ht.conj n
        rw [hn] at this
        exact (hs.hz.eq this).symm
      have hKn : conjSub n K ∈ omegaNbr Ω K := by
        have h1 : K ∈ omegaNbr Ω (conjSub n K) := by
          have := omegaNbr_conj hΩ.conjInvariant hs.hJ n
          rwa [hn] at this
        exact nbr_symm hΩ (hΩ.conjInvariant n K hK) hK h1
      obtain ⟨q, hq, hqK⟩ := th1 J hs.hJ (conjSub n K) hKn
      have hnz : n * z * n⁻¹ = q * t * q⁻¹ := by
        have h1 : IsUniqueInvolution (conjSub q J) (n * z * n⁻¹) := hqK ▸ hs.hz.conj n
        exact ((hs.ht.conj q).eq h1).symm
      have hzt' : z * t⁻¹ * z⁻¹ = t⁻¹ := by
        have hc : Commute z t := hztc
        have h1 : z * t⁻¹ = t⁻¹ * z := hc.inv_right.eq
        calc z * t⁻¹ * z⁻¹ = t⁻¹ * z * z⁻¹ := by rw [h1]
          _ = t⁻¹ := by group
      have e : n * (z * t) * n⁻¹ * (z * t)⁻¹ = q * (t * q⁻¹ * t⁻¹) := by
        calc n * (z * t) * n⁻¹ * (z * t)⁻¹ = (n * z * n⁻¹) * (n * t * n⁻¹) * (z * t)⁻¹ := by group
          _ = (q * t * q⁻¹) * z * (t⁻¹ * z⁻¹) := by rw [hnz, hnt]; group
          _ = (q * t * q⁻¹) * (z * t⁻¹ * z⁻¹) := by group
          _ = q * (t * q⁻¹ * t⁻¹) := by rw [hzt']; group
      rw [e]
      exact hqmem q hq
  ·
    intro M hM h4 hMJ hMK
    obtain ⟨q, hq, hMq⟩ := th1 J hs.hJ M hMK
    have hKM : K ∈ omegaNbr Ω M := nbr_symm hΩ hK hM hMK
    obtain ⟨-, hzcomm⟩ := comm_mem_oddCore_of_mem_omegaNbr hΩ (hw M hM) hKM hs.hz
    have hzS : z ∈ (S : Subgroup G) := hRS hzR
    have hMc : ∀ x ∈ M ⊓ (S : Subgroup G), x ∈ T8.cenZ z := by
      intro x hx
      have hxS : x ∈ (S : Subgroup G) := hx.2
      have hcS : z * x * z⁻¹ * x⁻¹ ∈ (S : Subgroup G) :=
        S.mul_mem (S.mul_mem (S.mul_mem hzS hxS) (S.inv_mem hzS)) (S.inv_mem hxS)
      have h1 : z * x * z⁻¹ * x⁻¹ = 1 :=
        eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard M) (hzcomm x hx.1)
          (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hcS))
      have h2 : z * x = x * z := commutatorElement_eq_one_iff_mul_comm.mp h1
      exact T8.mem_cenZ_iff.mpr h2.symm
    have hMx : T8.XMem Ω z M := xMem_of_mem_omegaNbr hΩ hw hK hs.hz hMK
    have hA2 : IsPGroup 2 ↥(M ⊓ (S : Subgroup G)) := S.isPGroup'.to_inf_right
    have hAres : M ⊓ (S : Subgroup G) ≤ T8.layerRes z M :=
      le_layerRes_of_isPGroup hΩ hcls hs.hz.sq hMx hA2 inf_le_left fun x hx => hMc x hx
    have hqc : q ∈ T8.cenZ z := T8.layerJoin_le_cenZ z (oddCoreOf_le_self _ hq)
    have hresq : T8.layerRes z M = conjSub q (T8.layerRes z J) := by
      rw [hMq]
      exact (T8.layerRes_conj J hqc).symm
    have hJx : T8.XMem Ω z J := xMem_of_mem_omegaNbr hΩ hw hK hs.hz hs.hJ
    have hTz : T ≤ T8.cenZ z := fun y hy =>
      T8.mem_cenZ_iff.mpr (((Asc77.l6_7_proved G Ω hΩ S R hRΩ T hTΩ hRS hTS
        (Asc77.T8R.R_ne_T hs)) z hzR y hy).symm)
    have hTres : IsSylow2In T (T8.layerRes z J) :=
      Asc77.T8.XMem.isSylow2In_layerRes_of_le hΩ hcls hs.hz.sq hJx hTsyl hTz
    have hJzN : T8.layerRes z J ≤ Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
      fun y hy => Asc77.T8.mem_normalizer_oddCoreOf_layerJoin hΩ (T8.layerRes_le_cenZ z J hy)
    have hYQ : oddCoreOf (T8.layerJoin Ω z) ≤
        T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z) := le_sup_right
    have hYN : T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z) ≤
        Subgroup.normalizer (oddCoreOf (T8.layerJoin Ω z) : Set G) :=
      sup_le hJzN Subgroup.le_normalizer
    have hQY : oddCoreOf (T8.layerJoin Ω z) ≤
        oddCoreOf (T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z)) :=
      T8V.le_oddCoreOf_of_normal_odd' hYQ hYN hQodd
    have hYeq : T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z) =
        T8.layerRes z J ⊔ oddCoreOf (T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z)) :=
      le_antisymm (sup_le_sup_left hQY _)
        (sup_le le_sup_left (oddCoreOf_le_self _))
    have hTY : IsSylow2In T (T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z)) :=
      T8R.isSylow2In_of_eq_sup_oddCoreOf le_sup_left hYeq hTres
    have hSY : (S : Subgroup G) ⊓ (T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z)) = T :=
      hTY.eq_of_le S.isPGroup'.to_inf_left inf_le_right (le_inf hTS hTY.1)
    have hMY : T8.layerRes z M ≤ T8.layerRes z J ⊔ oddCoreOf (T8.layerJoin Ω z) := by
      rw [hresq]
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
      have hjq : q * j * q⁻¹ = (q * j * q⁻¹ * j⁻¹) * j := by group
      have hqmem' : q * j * q⁻¹ * j⁻¹ ∈ oddCoreOf (T8.layerJoin Ω z) := by
        have h1 : j * q⁻¹ * j⁻¹ ∈ oddCoreOf (T8.layerJoin Ω z) :=
          (Subgroup.mem_normalizer_iff.mp (hJzN hj) q⁻¹).mp ((oddCoreOf _).inv_mem hq)
        have : q * (j * q⁻¹ * j⁻¹) ∈ oddCoreOf (T8.layerJoin Ω z) :=
          (oddCoreOf _).mul_mem hq h1
        simpa [mul_assoc] using this
      show (MulAut.conj q).toMonoidHom j ∈ _
      have : (MulAut.conj q).toMonoidHom j = q * j * q⁻¹ := rfl
      rw [this, hjq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hqmem') (Subgroup.mem_sup_left hj)
    have hMST : M ⊓ (S : Subgroup G) ≤ T := by
      intro y hy
      rw [← hSY]
      exact ⟨hy.2, hMY (hAres hy)⟩
    exact hMJ (Sec6Gen.eq_of_le_of_le hΩ hM hJΩ hA2 h4 inf_le_left (hMST.trans hTJ))

end Thin

end CFSG.ClassicalInvolution.Hat2A7S8.T21
