module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BadAuxB
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4BypassCore2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnCoord
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnStab
public import CFSG.RankThree.PartOne.KE.FiniteFieldAlgClosure

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4Minus_bad_case {p f : ℕ} [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L p]
    {g₀ : ModGL TwistTag.D4.tag L} (hg₀ : D4MinusFrame p f L g₀)
    {V Z : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))}
    (h2 : N2Cfg (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) 3 V Z)
    (h3 : N3Full (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) V Z)
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hv : d4MinusPsi σ L g₀ v ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L p f)))
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1) (hvV : MulAut.conj v ∈ V)
    (hnM : d4MinusPsi σ L g₀ n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnT : d4MinusPsi σ L g₀ n ∉ torusGroup TwistTag.D4.tag L)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (heV : MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ ∈ V)
    (hev : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) : False := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  have hg₀' := hg₀
  obtain ⟨hg₀C, hg₀P, hg₀F⟩ := hg₀'
  have hcen : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  have hVe : IsElementaryAbelian 3 V := h2.2.2.1
  have he3 : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ heV
  have hq2 : 2 < p ^ f := by
    by_contra hle
    have h2' : p ^ f = 2 := by omega
    have hdvd : p ∣ 2 := h2' ▸ dvd_pow_self p (by omega)
    exact hp2 (le_antisymm (Nat.le_of_dvd (by norm_num) hdvd) hp.two_le)
  obtain ⟨A, hA3, hA1, hψv⟩ := d4Minus_fixed_line hp hp2 hp3 hf hq K hK σ hσ L hg₀ v n δ hv hv1
    hv3 hnM hnT hδ he3 hev
  have hv_ord : orderOf v = 3 := orderOf_eq_prime hv3 hv1
  have hb : rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) =
      g₀⁻¹ * triEmb K σ L (1 * v * 1⁻¹) * g₀ := by
    rw [← hψv, d4MinusPsi_apply, one_mul, inv_one, mul_one]
  have hh : rootDiagUnit TwistTag.D4.tag (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) := by
    rw [← hψv]
    exact hv
  have hsurv := d4Minus_rootCharKernel hA3 hA1
  have hstab := d4_stab_three_A2 hA3 hA1
  obtain ⟨k, hkF, hkAlg, hkcl, hkcard⟩ := exists_finite_field_isAlgClosure p f hf K L
  have hzM : trialityOpposition L ∈ monomialSubgroup TwistTag.D4.tag L :=
    trialityOpposition_mem_monomialSubgroup
  have hzW : ∀ x : Fin TwistTag.D4.tag.rank → ℤ,
      weylQuotientHom TwistTag.D4.tag L ⟨trialityOpposition L, hzM⟩ • x = -x :=
    weylQuotientHom_trialityOpposition_smul
  obtain ⟨P, hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent, U, hUP, hUp, hUcard⟩ :=
    d4Q_a2_family (L := L) (k := k) hf hkcard hq2 Fr hFr (trialityOpposition L) hzM hzW
  have hperf : ∀ P' : Subgroup (ModGL TwistTag.D4.tag L), Finite P' →
      P' ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P', twistHom TwistTag.D4 L Fr x = x) →
      ⁅P', P'⁆ = P' → P' ≤ (triEmb K σ L).range := by
    intro P' _ hPC hPF _
    rw [triEmb_range hp hf hK hσ Fr hFr]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  have hPerX := d4Q_perx_a2 (triEmb K σ L) triEmb_injective triEmb_mem_adjointGroup Fr
    (triEmb_fixed Fr hcomm) hzM hzW hg₀C hg₀F hperf hv_ord 1 hb hh hsurv hstab
    ⟨Unit, fun _ => P, fun _ => hPfin, fun _ => hPq, fun _ => hPQ, fun _ => hPR,
      fun _ => hPadj, fun _ y hy hyR u hu => hPnorm y hy hyR u hu,
      fun y hy hyR hcomm' => hPcent y hy hyR (fun u hu => hcomm' () u hu)⟩
  have hab : ∀ N₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      N₀ ≤ fixSub (MulAut.conj v) →
      (∀ f' ∈ fixSub (MulAut.conj v), ∀ x ∈ N₀, f' * x * f'⁻¹ ∈ N₀) →
      (∀ x ∈ N₀, ∀ y ∈ N₀, x * y = y * x) →
      (∀ c ∈ N₀, (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) c = c) →
        N₀ ≤ Subgroup.zpowers v := by
    intro N₀ hN₀F hN₀n hN₀ab hN₀e c₀ hc₀
    have hcent : ∀ y ∈ fixSub (MulAut.conj v),
        y ∈ Subgroup.centralizer ({v} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
      intro y hy
      rw [mem_fixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at hy
      exact Subgroup.mem_centralizer_singleton_iff.2 hy.symm
    set D := Subgroup.centralizer ({v} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      with hD
    let V₀ : Subgroup D := N₀.subgroupOf D
    have hV₀n : V₀.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have hgF : (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
          fixSub (MulAut.conj v) := by
        rw [mem_fixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
        exact (Subgroup.mem_centralizer_singleton_iff.1 g.2).symm
      exact hN₀n _ hgF _ hx
    have hV₀s : Group.IsSolvable V₀ := by
      refine Group.isSolvable_of_comm fun a b => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact hN₀ab _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2)
    have hc₀D : c₀ ∈ D := hcent c₀ (hN₀F hc₀)
    have hmem : (⟨c₀, hc₀D⟩ : D) ∈ V₀ := Subgroup.mem_subgroupOf.2 hc₀
    obtain ⟨-, a, hψa, hker⟩ := hPerX V₀ hV₀n hV₀s ⟨c₀, hc₀D⟩ hmem
    have hψc : d4MinusPsi σ L g₀ c₀ = rootDiagUnit TwistTag.D4.tag a := by
      rw [← hψa, d4QPsi_apply, d4MinusPsi_apply, one_mul, inv_one, mul_one]
    have hmem1 : (![0, 0, 1, 0] : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4LongA2 := Or.inl rfl
    have hmem2 : (![1, 1, 1, 1] : Fin TwistTag.D4.tag.rank → ℤ) ∈ d4LongA2 :=
      Or.inr (Or.inl rfl)
    have h1 := hker _ hmem1
    have h2' := hker _ hmem2
    have e1 := rootChar_d4_apply (K := L) a ![0, 0, 1, 0]
    have e2 := rootChar_d4_apply (K := L) a ![1, 1, 1, 1]
    rw [e1] at h1
    rw [e2] at h2'
    have ha2 : a (2 : Fin 4) = 1 := by simpa using h1
    have has : a (0 : Fin 4) * a (1 : Fin 4) * a (3 : Fin 4) = 1 := by
      have h3' : a (0 : Fin 4) * a (1 : Fin 4) * a (2 : Fin 4) * a (3 : Fin 4) = 1 := by
        simpa using h2'
      rw [ha2, mul_one] at h3'
      exact h3'
    exact d4Minus_coord_mem_zpowers hp hf K hK σ hσ L hg₀ v n c₀ δ hA3 hA1 hψv hnM hδ he3 a hψc
      ha2 has (hN₀e c₀ hc₀)
  set ψ := d4MinusPsi σ L g₀ with hψdef
  have hinj : Function.Injective ψ := d4MinusPsi_injective g₀
  have hrange := d4MinusPsi_mem_range_iff hp hf hK hσ Fr hFr hg₀C hg₀F
  have hUrange : U ≤ ψ.range := fun x hx =>
    (hrange x).2 ⟨hPadj (hUP hx), hPR (hUP hx)⟩
  let U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := U.comap ψ
  have hU₀card : Nat.card U₀ = (p ^ f) ^ 3 := by
    have h1 : U₀.map ψ = U := Subgroup.map_comap_eq_self hUrange
    rw [← hUcard, ← h1, Subgroup.card_map_of_injective hinj]
  have hU₀p : IsPGroup p U₀ := by
    have : Fact p.Prime := ⟨hp⟩
    exact IsPGroup.of_card (n := 3 * f) (by rw [hU₀card, ← pow_mul, mul_comm])
  have hS : ∀ α ∈ d4LongA2, IsRoot TwistTag.D4.tag α := fun _ hα => d4LongA2_isRoot hα
  have hcentb := (rootDiagUnit_mem_centralizer_rootSpan_iff
    (![A, A, 1, A] : Fin TwistTag.D4.tag.rank → Lˣ) hS).2
    (fun α hα => ((hsurv α).2 hα).2)
  have hU₀F : U₀ ≤ fixSub (MulAut.conj v) := by
    intro y hy
    have hyU : ψ y ∈ U := hy
    have hyQ : ψ y ∈ rootSpan TwistTag.D4.tag L d4LongA2 := hPQ (hUP hyU)
    have hcomm' := Subgroup.mem_centralizer_iff.1 hcentb (ψ y) hyQ
    rw [← hψv] at hcomm'
    have hyv : y * v = v * y := by
      apply hinj
      rw [map_mul, map_mul]
      exact hcomm'
    rw [mem_fixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
    exact hyv.symm
  have hker := d4_hker_of_abelian hp hp2 hf K hK σ hσ hv3 _ hab U₀ hU₀F hU₀p hU₀card.ge
  exact false_of_inner_abelian_core hcen h2 h3 hv1 hvV heV hab hker

end CFSG.GH74.GLS.Stage2.Bender.Thm1
