module

public import CFSG.ClassicalInvolution.Asc77.AscT7L4
public import CFSG.ClassicalInvolution.Asc77.AscT7L6B
public import CFSG.ClassicalInvolution.Asc77.AscT7L8
public import CFSG.ClassicalInvolution.Asc77.AscT7K10

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace T7L

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z u e g : G}

section GammaB

theorem inf_centralizer_le_gamma2 (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) {s : G}
    (hsB : s ∈ Subgroup.closure ({u * e, u, z} : Set G)) (hs1 : s ≠ 1) (hsu : s ≠ u)
    {Y : Subgroup G} (hY : Y ≤ Subgroup.centralizer ({u} : Set G)) :
    Y ⊓ Subgroup.centralizer ({s} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
  have hB := T7K.B_isElemAbelian hs hd
  have hcomm := T7A.commutes_closure (T7K.comm_gen hs hd)
  obtain ⟨-, huB, -⟩ := T7K.generators_mem_B z u e
  have hs2 : s * s = 1 := by
    have := hB.2 s hsB
    rwa [pow_two] at this
  have hus : u * s = s * u := hcomm u huB s hsB
  have hA := T7A.isElemAbelian2_closure_pair hd.hu2 hs2 hd.hu1 hs1 (Ne.symm hsu) hus
  have hAB : Subgroup.closure ({u, s} : Set G) ≤ Subgroup.closure ({u * e, u, z} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact huB
    · exact hsB
  rintro y ⟨hyY, hys⟩
  have hyu : u * y = y * u := (Subgroup.mem_centralizer_singleton_iff.mp (hY hyY)).symm
  have hys' : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.mp hys).symm
  exact T7K.le_gamma2 hAB hA ⟨hY hyY, T7B.mem_centralizer_closure_pair hyu hys'⟩

theorem oddCore_layer_le_gamma2 (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) :
    oddCoreOf (exactLayer Ω u) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
  have hB := T7K.B_isElemAbelian hs hd
  have hB8 := T7K.B_natCard hs hd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hBu : Subgroup.closure ({u * e, u, z} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_gen hs hd x hx u (by simp))
  have hBN : ∀ b ∈ Subgroup.closure ({u * e, u, z} : Set G),
      b ∈ Subgroup.normalizer (oddCoreOf (exactLayer Ω u) : Set G) := fun b hb =>
    mem_normalizer_oddCoreOf (mem_normalizer_iff_conjSub_eq.mpr
      (conjSub_exactLayer hΩ.conjInvariant (hBu hb)))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two (Subgroup.closure ({u * e, u, z} : Set G)) (oddCoreOf (exactLayer Ω u)) hB
    (by rw [hB8]; norm_num) hBN (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  have hNH : oddCoreOf (exactLayer Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    (oddCoreIn_le _).trans (exactLayer_le_centralizer Ω u)
  conv_lhs => rw [← hgen]
  refine iSup₂_le fun E hE => ?_
  have hE2 : IsElemAbelian2 E 2 :=
    ⟨hE.2, fun x hx => by rw [← pow_two]; exact hB.2 x (hE.1 hx)⟩
  exact (inf_le_inf_right _ hNH).trans (T7K.le_gamma2 hE.1 hE2)

theorem B_ne (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    (u * e ≠ 1 ∧ u * e ≠ u) ∧ (z ≠ 1 ∧ z ≠ u) ∧ (u * z ≠ 1 ∧ u * z ≠ u) ∧
      (u * e * z ≠ 1 ∧ u * e * z ≠ u) ∧ (u * e * (u * z) ≠ 1 ∧ u * e * (u * z) ≠ u) := by
  have hee : e ∉ K ⊔ K' := T7K.e_not_mem_sup hs hd
  have huS : u ∈ K ⊔ K' := hd.hu
  have hzS : z ∈ K ⊔ K' := Subgroup.mem_sup_left hs.hz.mem
  have hue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hd.hu2
  have hez : u * e * (u * z) = e * z := by
    calc u * e * (u * z) = (e * u) * (u * z) := by rw [hue]
      _ = e * (u * u) * z := by group
      _ = e * z := by rw [hd.hu2]; group
  have a1 : u * e ≠ 1 := by
    intro h
    apply hee
    rw [eq_inv_of_mul_eq_one_right h]
    exact (K ⊔ K').inv_mem huS
  have a2 : u * e ≠ u := by
    intro h
    exact hd.he1 (mul_left_cancel (h.trans (mul_one u).symm))
  have a3 : u * z ≠ 1 := by
    intro h
    apply hd.huz
    have := eq_inv_of_mul_eq_one_right h
    rw [this, hu1]
  have a4 : u * z ≠ u := by
    intro h
    exact hs.hz.ne_one (mul_left_cancel (h.trans (mul_one u).symm))
  have a5 : u * e * z ≠ 1 := by
    intro h
    apply hee
    have h1 : e * z = u⁻¹ := by
      calc e * z = u⁻¹ * (u * e * z) := by group
        _ = u⁻¹ := by rw [h, mul_one]
    have : e = u⁻¹ * z⁻¹ := by
      calc e = (e * z) * z⁻¹ := by group
        _ = u⁻¹ * z⁻¹ := by rw [h1]
    rw [this]
    exact (K ⊔ K').mul_mem ((K ⊔ K').inv_mem huS) ((K ⊔ K').inv_mem hzS)
  have a6 : u * e * z ≠ u := by
    intro h
    apply hee
    have h1 : e * z = 1 := by
      have : u * (e * z) = u * 1 := by rw [← mul_assoc, h, mul_one]
      exact mul_left_cancel this
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (K ⊔ K').inv_mem hzS
  have a7 : u * e * (u * z) ≠ 1 := by
    intro h
    apply hee
    rw [hez] at h
    rw [eq_inv_of_mul_eq_one_left h]
    exact (K ⊔ K').inv_mem hzS
  have a8 : u * e * (u * z) ≠ u := by
    intro h
    apply hee
    rw [hez] at h
    have : e = u * z⁻¹ := by
      calc e = (e * z) * z⁻¹ := by group
        _ = u * z⁻¹ := by rw [h]
    rw [this]
    exact (K ⊔ K').mul_mem huS ((K ⊔ K').inv_mem hzS)
  exact ⟨⟨a1, a2⟩, ⟨hs.hz.ne_one, fun h => hd.huz h.symm⟩, ⟨a3, a4⟩, ⟨a5, a6⟩, ⟨a7, a8⟩⟩

end GammaB

end T7L

variable {p f : ℕ} [Fact p.Prime]

theorem c23_GammaU_of_facts (htcf : TwinCentralFact p) (hgen : E4TwinGen p) :
    C23_GammaU p f := by
  intro G _ _ _ Ω K K' W z u e g hs hd
  classical
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hBelow : CITBelowU p f (Nat.card G) := hst.below f hq
  obtain ⟨a₂, b₂, v', ha₂Y, hb₂Y, hv'Y, htY, hv'z, hS, hlt, T, hconj⟩ :=
    T7L.layer_u_frame hs hd
  obtain ⟨hsplit, hCI⟩ := T7L.twinSection_gen_conj htcf hgen hp hq hBelow hlt hS T
  have hBel := T7K.B_isElemAbelian hs hd
  obtain ⟨hzB, huB, heB⟩ := T7K.generators_mem_B z u e
  have htB : u * e ∈ Subgroup.closure ({u * e, u, z} : Set G) :=
    Subgroup.mul_mem _ huB heB
  have hv'B : v' ∈ Subgroup.closure ({u * e, u, z} : Set G) := by
    rcases hv'z with h | h
    · rw [h]
      exact hzB
    · rw [h]
      exact Subgroup.mul_mem _ huB hzB
  have htv'B : u * e * v' ∈ Subgroup.closure ({u * e, u, z} : Set G) := Subgroup.mul_mem _ htB hv'B
  have sq : ∀ x ∈ Subgroup.closure ({u * e, u, z} : Set G), x * x = 1 := fun x hx => by
    have := hBel.2 x hx
    rwa [pow_two] at this
  obtain ⟨⟨ht1, htu⟩, ⟨hz1, hzu⟩, ⟨huz1, huzu⟩, ⟨htz1, htzu⟩, ⟨htuz1, htuzu⟩⟩ :=
    T7L.B_ne hs hd
  have hv'1 : v' ≠ 1 ∧ v' ≠ u := by
    rcases hv'z with h | h <;> rw [h]
    · exact ⟨hz1, hzu⟩
    · exact ⟨huz1, huzu⟩
  have htv'1 : u * e * v' ≠ 1 ∧ u * e * v' ≠ u := by
    rcases hv'z with h | h <;> rw [h]
    · exact ⟨htz1, htzu⟩
    · exact ⟨htuz1, htuzu⟩
  have hYH : exactLayer Ω u ≤ Subgroup.centralizer ({u} : Set G) := exactLayer_le_centralizer Ω u
  have hYΓ : exactLayer Ω u ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) := by
    rw [← T7H.toBar_mul htY hv'Y] at hsplit
    have hgenY := T7L.layer_le_of_quot_gen htY hv'Y ((exactLayer Ω u).mul_mem htY hv'Y)
      (sq _ htB) (sq _ hv'B) (sq _ htv'B) ht1 hv'1.1 htv'1.1 hsplit
    exact hgenY.trans (sup_le (sup_le (sup_le (T7L.oddCore_layer_le_gamma2 hs hd)
      (T7L.inf_centralizer_le_gamma2 hs hd htB ht1 htu hYH))
      (T7L.inf_centralizer_le_gamma2 hs hd hv'B hv'1.1 hv'1.2 hYH))
      (T7L.inf_centralizer_le_gamma2 hs hd htv'B htv'1.1 htv'1.2 hYH))
  have hHt : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({u * e} : Set G) ≤
      gamma2 (Subgroup.closure ({u * e, u, z} : Set G)) (Subgroup.centralizer ({u} : Set G)) :=
    T7L.inf_centralizer_le_gamma2 hs hd htB ht1 htu le_rfl
  intro h hh
  obtain ⟨B₀, hB₀, hmem, huniq⟩ := hconj h hh
  obtain ⟨yb, hyb⟩ := hCI B₀ hB₀ _ huniq
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective yb
  have hcongr := T7L.mem_oddCore_of_mk_conj htY hmem y hyb
  obtain ⟨y', hy', c, hc, rfl⟩ := T7L.eq_mul_of_conj_mod hYH (oddCoreIn_le _)
    (oddCoreOf_odd_natCard _) (fun y hy => normalizer_oddCoreIn _ hy) htY (sq _ htB) ht1 hh y.2
    hcongr
  exact Subgroup.mul_mem _ (hYΓ hy') (hHt hc)

end CFSG.ClassicalInvolution.Asc77
