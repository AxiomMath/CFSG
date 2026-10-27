module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3A
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3F
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoS1C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic Matrix
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
  CFSG.ClassicalInvolution.Q3.TA3.Q5U3
open CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

namespace U3

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {K : Type} [Field K]
  (h : UnitaryFieldData p f K)

omit [Finite G] in
theorem sl_facts (h5 : 5 ≤ p ^ f) {N : Subgroup G} [N.Normal] {w : G}
    {π : ↥(GU2Stated (p ^ f) K) →* G}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({w} : Set G)) (hk : CubeKer π)
    (hπ1 : π ⟨-1, neg_one_mem_GU2 h⟩ = w) :
    (slPart (GU2Stated (p ^ f) K)).map π ≤ Subgroup.centralizer ({w} : Set G) ∧
      (∀ c ∈ Subgroup.centralizer ({w} : Set G), ∀ j ∈ (slPart (GU2Stated (p ^ f) K)).map π,
        c * j * c⁻¹ ∈ (slPart (GU2Stated (p ^ f) K)).map π) ∧
      IsQuasisimple ↥((slPart (GU2Stated (p ^ f) K)).map π) ∧
      w ∈ (slPart (GU2Stated (p ^ f) K)).map π := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  set J₀ := (slPart (GU2Stated (p ^ f) K)).map π with hJ₀
  have hJr : J₀ ≤ π.range := Subgroup.map_le_range π _
  have hJNC : J₀ ≤ N ⊓ Subgroup.centralizer ({w} : Set G) := hrange ▸ hJr
  obtain ⟨eJ⟩ := nonempty_slPart_equiv h
  have hF₀ := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  have h4 : 4 ≤ Nat.card (LieType.Steinberg.fixedSubfield K p f) := by rw [hF₀]; omega
  have hJr' : J₀ = (π.comp (slPart (GU2Stated (p ^ f) K)).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eJ' : ↥J₀ ≃* SL(2, LieType.Steinberg.fixedSubfield K p f) :=
    (MulEquiv.subgroupCongr hJr').trans
      ((MonoidHom.ofInjective (injective_slPart hk)).symm.trans eJ)
  have hq : IsQuasisimple ↥J₀ := LocalCores.isQuasisimple_of_mulEquiv eJ'.symm
    ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      (Balance.StrongBalance.Linear.isQuasisimple_SL_of_two_le le_rfl h4))
  have : Group.IsPerfect ↥J₀ := isPerfect_of_equiv_sl2 h4 eJ'
  refine ⟨hJNC.trans inf_le_right, fun c hc j hj => ?_, hq, ?_⟩
  · have hle : J₀.map (MulAut.conj c).toMonoidHom ≤ π.range := by
      rw [hrange]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp (hJNC hx)
      exact Subgroup.mem_inf.mpr ⟨(inferInstance : N.Normal).conj_mem _ hxN c,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hxC) (Subgroup.inv_mem _ hc)⟩
    have hM : J₀.map (MulAut.conj c).toMonoidHom ≤ J₀ :=
      calc J₀.map (MulAut.conj c).toMonoidHom
          = ⁅J₀.map (MulAut.conj c).toMonoidHom, J₀.map (MulAut.conj c).toMonoidHom⁆ := by
            rw [← Subgroup.map_commutator, Subgroup.commutator_eq_self]
        _ ≤ ⁅π.range, π.range⁆ := Subgroup.commutator_mono hle hle
        _ ≤ J₀ := commutator_range_le π
    exact hM ⟨j, hj, rfl⟩
  · rw [← hπ1]
    refine ⟨⟨-1, neg_one_mem_GU2 h⟩, mem_slPart.mpr ?_, rfl⟩
    ext
    simp [Matrix.det_neg]

theorem exists_scalar_four (h5 : 5 ≤ p ^ f) {N : Subgroup G} [N.Normal]
    (hOut : ∀ P : Subgroup (G ⧸ N), IsPGroup 2 P → IsCyclic P) {w : G}
    {π : ↥(GU2Stated (p ^ f) K) →* G}
    (hrange : π.range = N ⊓ Subgroup.centralizer ({w} : Set G)) (hk : CubeKer π)
    (hπ1 : π ⟨-1, neg_one_mem_GU2 h⟩ = w) {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {M : Subgroup G} (hM : M ∈ Δ)
    (hMw : IsUniqueInvolution M w) :
    ∃ A : ↥(GU2Stated (p ^ f) K),
      (∃ c : Kˣ, (A : GL (Fin 2) K) = GeneralLinearGroup.scalar (Fin 2) c) ∧ π A ∈ M ∧
        orderOf (π A) = 4 := by
  obtain ⟨hJC, hJn, hJq, hwJ⟩ := sl_facts h h5 hrange hk hπ1
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := M) (IsPGroup.of_bot (p := 2)) bot_le
  obtain ⟨eP⟩ := hΔ.quat M hM P hP
  obtain ⟨s, hsP, hsN, hs4⟩ := exists_four_of_quat hOut eP
  have hsM : s ∈ M := hP.1 hsP
  have hsC : s ∈ Subgroup.centralizer ({w} : Set G) :=
    le_centralizer_of_isUniqueInvolution hMw hsM
  obtain ⟨A, hA⟩ : s ∈ π.range := hrange ▸ Subgroup.mem_inf.mpr ⟨hsN, hsC⟩
  have hcomm := commute_of_component hΔ hM hMw hJC (isComponent_of_normal hJC hJn hJq) hwJ s hsM
  obtain ⟨c, hc⟩ := exists_scalar_of_commute hk (slCentScalar_GU2 h) fun B hB => by
    rw [hA]
    exact hcomm _ ⟨B, hB, rfl⟩
  exact ⟨A, ⟨c, hc⟩, hA ▸ hsM, hA ▸ hs4⟩

include h in
theorem eq_of_inv (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) {N : Subgroup G} [N.Normal]
    (hOut : ∀ P : Subgroup (G ⧸ N), IsPGroup 2 P → IsCyclic P)
    (e : ↥N ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 (p ^ f) K))
    {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ) {w : G} (hwN : w ∈ N) {M M' : Subgroup G}
    (hM : M ∈ Δ) (hM' : M' ∈ Δ) (hMw : IsUniqueInvolution M w)
    (hM'w : IsUniqueInvolution M' w) : M = M' := by
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hMw.sq) hMw.ne_one
  obtain ⟨-, π, hrange, hk, hπ1, -⟩ := MF163.U3.exists_frame_formula h hp2 e hwN hw2
  obtain ⟨A, ⟨c, hc⟩, hAM, hA4⟩ := exists_scalar_four h h5 hOut hrange hk hπ1 hΔ hM hMw
  obtain ⟨A', ⟨c', hc'⟩, hA'M, hA'4⟩ := exists_scalar_four h h5 hOut hrange hk hπ1 hΔ hM' hM'w
  have hsq : ∀ {L : Subgroup G} {x : G}, IsUniqueInvolution L w → x ∈ L → orderOf x = 4 →
      x * x = w := by
    intro L x hL hx hx4
    have hx2 : x * x * (x * x) = 1 := by
      rw [← sq, ← sq, ← pow_mul, show 2 * 2 = orderOf x by rw [hx4], pow_orderOf_eq_one]
    rcases hL.unique _ (L.mul_mem hx hx) hx2 with h0 | h0
    · exfalso
      have := orderOf_dvd_of_pow_eq_one (show x ^ 2 = 1 by rw [sq]; exact h0)
      rw [hx4] at this
      norm_num at this
    · exact h0
  set a := π A with ha
  set a' := π A' with ha'
  have hw : a * a = w := hsq hMw hAM hA4
  have hw' : a' * a' = w := hsq hM'w hA'M hA'4
  have hcomm : a⁻¹ * a' = a' * a⁻¹ := by
    have h1 : a * a' = a' * a := by
      rw [ha, ha', ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc, scalar_mul_comm]
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_assoc, mul_inv_cancel, mul_one]
  have hBs : ((A' * A⁻¹ : ↥(GU2Stated (p ^ f) K)) : GL (Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2) (c' * c⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hc, hc', map_mul, map_inv]
  have hBB : π (A' * A⁻¹) * π (A' * A⁻¹) = 1 := by
    rw [map_mul, map_inv, ← ha, ← ha',
      show a' * a⁻¹ * (a' * a⁻¹) = a' * (a⁻¹ * a') * a⁻¹ by group, hcomm,
      show a' * (a' * a⁻¹) * a⁻¹ = a' * a' * (a * a)⁻¹ by group, hw, hw', mul_inv_cancel]
  have haM' : a ∈ M' := by
    rcases eq_or_of_scalar_sq hk (N1 := ⟨-1, neg_one_mem_GU2 h⟩) rfl hBs hBB with h1 | h1
    · rw [map_mul, map_inv, ← ha, ← ha', mul_inv_eq_one] at h1
      exact h1 ▸ hA'M
    · rw [map_mul, map_inv, ← ha, ← ha', hπ1, mul_inv_eq_iff_eq_mul] at h1
      have h2 : a = w * a' := by
        rw [h1, ← mul_assoc, hMw.sq, one_mul]
      exact h2 ▸ M'.mul_mem hM'w.mem hA'M
  exact eq_of_orderOf_eq_four hΔ.hyp hM hM' hAM haM' hA4

end U3

theorem socleTransitive_u3Ge5 : SocleTransitive IsU3Ge5 := by
  intro G _ _ N _ _ _ hC hP Δ hΔ hN J hJ L hL
  obtain ⟨p, f, hp, hp2, h5, hLie⟩ := hP
  obtain ⟨-, hf, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hO : Nobq.OutTwoCyclic ↥N := outTwoCyclic_PSU (n := 3)
    ⟨⟨h.prime, h.one_le, le_rfl, fun he => by
      have := congrArg Prod.snd he
      simp only at this
      omega⟩, K, inferInstance, inferInstance, h.card_eq_sq, ⟨e⟩⟩
    ((by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _))
  have hOut := Nobq.isCyclic_of_outTwoCyclic N hC hO
  obtain ⟨⟨t, ht⟩, -⟩ := hΔ.hyp.omega1 J hJ
  have htN := hN J hJ t ht
  have ho : ∀ {K' : Subgroup G} {z : G}, IsUniqueInvolution K' z → orderOf z = 2 := fun hz =>
    orderOf_eq_prime (by rw [sq]; exact hz.sq) hz.ne_one
  refine transitive_of_eq_at hΔ.hyp (t := t) (fun K' hK' z hz => ?_)
    (fun K' hK' K'' hK'' h1 h2 => U3.eq_of_inv h hp2 h5 hOut e hΔ htN hK' hK'' h1 h2) J hJ L hL
  obtain ⟨n, -, hn⟩ := U3.exists_conj_of_psu hp2 hLie (hN K' hK' z hz) htN (ho hz) (ho ht)
  exact ⟨n, hn⟩

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
