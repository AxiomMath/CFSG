module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf2Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

namespace ExitE4

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem eq_top_of_subnormal (hgen : omegaGen Φ = ⊤)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {K : Subgroup X} (hK : K ∈ Φ)
    {H T : Subgroup X} (hHT : IsSubnormal H T) (hT : T = ⊤) (hKH : K ≤ H) : H = ⊤ := by
  revert hT hKH
  induction hHT with
  | refl => intro hT _; exact hT
  | @step H' M' T' hle hn _ ih =>
    intro hT hKH
    have hM : M' = ⊤ := ih hT (hKH.trans hle)
    have hHn : H'.Normal := ⟨fun x hx g => by
      refine (Subgroup.normal_subgroupOf_iff hle).mp hn x g hx ?_
      rw [hM]
      exact Subgroup.mem_top g⟩
    rw [eq_top_iff, ← hgen]
    unfold omegaGen
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, rfl⟩ := htrans K hK L hL
    intro y hy
    rw [mem_conjSub_iff] at hy
    have := hHn.conj_mem _ (hKH hy) g
    simpa [mul_assoc] using this

omit [Finite X] in
theorem twinE4_of_top (h : TwinE4 ↥(⊤ : Subgroup X)) :
    ∃ (Q : Type) (_ : Group Q) (f : X →* Q), Function.Surjective f ∧ IsPGroup 2 ↥f.ker ∧
      (CFSG.Blueprint.LieModel Q .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel Q .POmegaPlus 4 2 1) := by
  obtain ⟨Q, hQ, f, hs, hk, hM⟩ := h
  refine ⟨Q, hQ, f.comp Subgroup.topEquiv.symm.toMonoidHom, ?_, ?_, hM⟩
  · intro q
    obtain ⟨y, hy⟩ := hs q
    refine ⟨Subgroup.topEquiv y, ?_⟩
    show f (Subgroup.topEquiv.symm (Subgroup.topEquiv y)) = q
    rw [MulEquiv.symm_apply_apply]
    exact hy
  · intro g
    obtain ⟨k, hk'⟩ := hk ⟨Subgroup.topEquiv.symm (g : X), g.2⟩
    refine ⟨k, ?_⟩
    have h1 := congrArg (fun y : ↥f.ker => ((y : ↥(⊤ : Subgroup X)) : X)) hk'
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h1

theorem exists_noncomm (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {J : Subgroup X}
    (hJ : J ∈ Φ) : ∃ a ∈ J, ∃ b ∈ J, a * b ≠ b * a := by
  obtain ⟨-, P, hP, hnc⟩ := hΩ.omega1 J hJ
  have hPJ : J = P := hP.2.2 J le_rfl (h2 J hJ) hP.1
  subst hPJ
  by_contra hall
  push Not at hall
  exact hnc ⟨⟨fun a b => Subtype.ext (hall a a.2 b b.2)⟩⟩

theorem inf_eq_bot (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hΩ : HypOmegaGen Φ) {N : Subgroup X}
    (hN : ∀ J ∈ Φ, ∀ u : X, IsUniqueInvolution J u → u ∉ N) {J : Subgroup X} (hJ : J ∈ Φ) :
    J ⊓ N = ⊥ := by
  by_contra hne
  obtain ⟨u, hu⟩ := (hΩ.omega1 J hJ).1
  exact hN J hJ u hu (Twin1711.mem_of_inf_ne_bot (h2 J hJ) hu hne)

theorem center_of_meet (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) (hgen : omegaGen Φ = ⊤)
    {N : Subgroup X} [N.Normal] (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Φ, J ⊓ N = ⊥) :
    N ≤ Subgroup.center X := by
  have hJc : ∀ J ∈ Φ, J ≤ Subgroup.centralizer (N : Set X) := by
    intro J hJ
    have hc := comm613Gen_normal hΩ (Q3.TC.mem_RSet_of_isPGroup hJ (h2 J hJ)) inferInstance
      (hmeet J hJ)
    rw [oddCoreOf_eq_bot_of_isPGroup hN2, le_bot_iff] at hc
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hX : (⊤ : Subgroup X) ≤ Subgroup.centralizer (N : Set X) := by
    rw [← hgen]
    unfold omegaGen
    exact iSup₂_le hJc
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro y
  exact (Subgroup.mem_centralizer_iff.mp (hX (Subgroup.mem_top y)) n hn).symm

theorem twin_clause_central (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {K : Subgroup X}
    (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z)
    (hnab : ∃ a ∈ K, ∃ b ∈ K, a * b ≠ b * a) {s q : X} (hq : z⁻¹ * (s * z * s⁻¹) = q)
    (hqc : ∀ y : X, y * q = q * y) :
    conjSub s K = K ∨ Commutes K (conjSub s K) := by
  by_cases he : conjSub s K = K
  · exact Or.inl he
  right
  have hΩ' : conjSub s K ∈ Φ := hΩ.conjInvariant s K hK
  have hne : K ≠ conjSub s K := fun e => he e.symm
  have hR' : IsUniqueInvolution (conjSub s K) (s * z * s⁻¹) := hz.conj s
  have hw' : s * z * s⁻¹ = z * q := by rw [← hq]; group
  have hJw : ∀ v ∈ conjSub s K, v * z = z * v := by
    intro v hv
    have h1 := TwinE4Perf.commute_of_inv hR' hv
    rw [hw'] at h1
    have h2 := hqc v
    have h3 : v * z * q = z * v * q := by
      calc v * z * q = v * (z * q) := by group
        _ = (z * q) * v := h1
        _ = z * (q * v) := by group
        _ = z * (v * q) := by rw [← h2]
        _ = z * v * q := by group
    exact mul_right_cancel h3
  have hJw' : ∀ v ∈ K, v * (s * z * s⁻¹) = (s * z * s⁻¹) * v := by
    intro v hv
    rw [hw']
    have h1 := TwinE4Perf.commute_of_inv hz hv
    have h2 := hqc v
    calc v * (z * q) = (v * z) * q := by group
      _ = (z * v) * q := by rw [h1]
      _ = z * (v * q) := by group
      _ = z * (q * v) := by rw [h2]
      _ = (z * q) * v := by group
  have hnab' : ∃ a ∈ conjSub s K, ∃ b ∈ conjSub s K, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    refine ⟨s * a * s⁻¹, conj_mem_conjSub ha, s * b * s⁻¹, conj_mem_conjSub hb, fun hh => hab ?_⟩
    have : s * (a * b) * s⁻¹ = s * (b * a) * s⁻¹ := by
      calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
        _ = (s * b * s⁻¹) * (s * a * s⁻¹) := hh
        _ = s * (b * a) * s⁻¹ := by group
    have h5 := congrArg (fun y => s⁻¹ * y * s) this
    simpa [mul_assoc] using h5
  have n1 := TwinE4Perf.le_normalizer_of_inv_commute hΩ h2 hK hΩ' hne hz hJw hnab'
  have n2 := TwinE4Perf.le_normalizer_of_inv_commute hΩ h2 hΩ' hK hne.symm hR' hJw' hnab
  exact commutes_of_mutual_normalizer hΩ h2 hK hΩ' hne n2 n1

theorem eq_of_map (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {N : Subgroup X} [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hmeet : ∀ J ∈ Φ, J ⊓ N = ⊥) {K J : Subgroup X} (hK : K ∈ Φ)
    (hJ : J ∈ Φ) (hmap : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) :
    K = J := by
  by_contra hne
  obtain ⟨uK, huK⟩ := (hΩ.omega1 K hK).1
  obtain ⟨uJ, huJ⟩ := (hΩ.omega1 J hJ).1
  have huJN : uJ ∉ N := fun h => huJ.ne_one (by
    have : uJ ∈ J ⊓ N := ⟨huJ.mem, h⟩
    rw [hmeet J hJ, Subgroup.mem_bot] at this
    exact this)
  have hmem : QuotientGroup.mk' N uJ ∈ K.map (QuotientGroup.mk' N) := by
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ huJ.mem
  obtain ⟨k, hk, hke⟩ := hmem
  have hkk : k * k = 1 := by
    have h0 : QuotientGroup.mk' N (k * k) = 1 := by
      rw [map_mul, hke, ← map_mul, huJ.sq, map_one]
    have h1 : k * k ∈ K ⊓ N := ⟨K.mul_mem hk hk, (QuotientGroup.eq_one_iff _).mp h0⟩
    rw [hmeet K hK, Subgroup.mem_bot] at h1
    exact h1
  have hk1 : k ≠ 1 := by
    intro h
    apply huJN
    refine (QuotientGroup.eq_one_iff _).mp ?_
    exact hke.symm.trans (by rw [h, map_one])
  have hkK : k = uK := (huK.unique k hk hkk).resolve_left hk1
  have hq : uK⁻¹ * uJ ∈ N := by
    have h0 := hke
    rw [hkK, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h0
    exact h0
  have hqc : ∀ y : X, y * (uK⁻¹ * uJ) = (uK⁻¹ * uJ) * y := Subgroup.mem_center_iff.mp (hNc hq)
  have hqe : uJ = uK * (uK⁻¹ * uJ) := (mul_inv_cancel_left uK uJ).symm
  have hJz : ∀ v ∈ J, v * uK = uK * v := by
    intro v hv
    have h1 := TwinE4Perf.commute_of_inv huJ hv
    rw [hqe] at h1
    have h3 : v * uK * (uK⁻¹ * uJ) = uK * v * (uK⁻¹ * uJ) := by
      calc v * uK * (uK⁻¹ * uJ) = v * (uK * (uK⁻¹ * uJ)) := by group
        _ = (uK * (uK⁻¹ * uJ)) * v := h1
        _ = uK * ((uK⁻¹ * uJ) * v) := by group
        _ = uK * (v * (uK⁻¹ * uJ)) := by rw [← hqc v]
        _ = uK * v * (uK⁻¹ * uJ) := by group
    exact mul_right_cancel h3
  have hKz : ∀ v ∈ K, v * uJ = uJ * v := by
    intro v hv
    have h1 := TwinE4Perf.commute_of_inv huK hv
    rw [hqe]
    calc v * (uK * (uK⁻¹ * uJ)) = (v * uK) * (uK⁻¹ * uJ) := by group
      _ = (uK * v) * (uK⁻¹ * uJ) := by rw [h1]
      _ = uK * (v * (uK⁻¹ * uJ)) := by group
      _ = uK * ((uK⁻¹ * uJ) * v) := by rw [hqc v]
      _ = (uK * (uK⁻¹ * uJ)) * v := by group
  have hnabK := exists_noncomm hΩ h2 hK
  have hnabJ := exists_noncomm hΩ h2 hJ
  have n1 := TwinE4Perf.le_normalizer_of_inv_commute hΩ h2 hK hJ hne huK hJz hnabJ
  have n2 := TwinE4Perf.le_normalizer_of_inv_commute hΩ h2 hJ hK (Ne.symm hne) huJ hKz hnabK
  have hcomm : Commutes K J := commutes_of_mutual_normalizer hΩ h2 hK hJ hne n2 n1
  obtain ⟨a, ha, b, hb, hab⟩ := hnabK
  obtain ⟨j, hj, hje⟩ : ∃ j ∈ J, QuotientGroup.mk' N j = QuotientGroup.mk' N a := by
    have : QuotientGroup.mk' N a ∈ J.map (QuotientGroup.mk' N) := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ ha
    exact this
  have hn : a⁻¹ * j ∈ N := by
    have h0 := hje.symm
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h0
    exact h0
  have hnc : ∀ y : X, y * (a⁻¹ * j) = (a⁻¹ * j) * y := Subgroup.mem_center_iff.mp (hNc hn)
  have hjb : b * j = j * b := hcomm b hb j hj
  have hje' : j = a * (a⁻¹ * j) := (mul_inv_cancel_left a j).symm
  apply hab
  have h3 : b * a * (a⁻¹ * j) = a * b * (a⁻¹ * j) := by
    calc b * a * (a⁻¹ * j) = b * (a * (a⁻¹ * j)) := by group
      _ = b * j := by rw [← hje']
      _ = j * b := hjb
      _ = (a * (a⁻¹ * j)) * b := by rw [← hje']
      _ = a * ((a⁻¹ * j) * b) := by group
      _ = a * (b * (a⁻¹ * j)) := by rw [← hnc b]
      _ = a * b * (a⁻¹ * j) := by group
  exact (mul_right_cancel h3).symm

theorem centQuotGen (hΩ : HypOmegaGen Φ) (h2 : ∀ J ∈ Φ, IsPGroup 2 J) {N : Subgroup X} [N.Normal]
    (hNc : N ≤ Subgroup.center X) (hmeet : ∀ J ∈ Φ, J ⊓ N = ⊥) : CentQuotGen Φ N where
  hyp := hΩ
  hyp' := CentQ.quotient_hypOmegaGen hΩ N hNc fun K hK => by
    rw [inf_comm, hmeet K hK, Subgroup.card_bot]
    exact odd_one
  meet := hmeet
  eq_of_map := fun K hK J hJ h => eq_of_map hΩ h2 hNc hmeet hK hJ h
  normalizer_of_map := by
    intro K hK u hu
    have hKu : conjSub u K ∈ Φ := hΩ.conjInvariant u K hK
    rw [mem_normalizer_iff_conjSub_eq]
    refine eq_of_map hΩ h2 hNc hmeet hKu hK ?_
    rw [AscQuot.map_conjSub]
    exact mem_normalizer_iff_conjSub_eq.mp hu

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
