module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3TB
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Cl
public import CFSG.ClassicalInvolution.Q3.ONanTA3SmallU33
public import CFSG.ClassicalInvolution.Q3.TL4MF163L2
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3Ck
public import CFSG.GH74.KGroups.Generic6
public import Certificates.Certificate55111

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic QuaternionGroup
open scoped commutatorElement

namespace E3S3T

theorem q8_hom_ext {G : Type*} [Group G] {f₁ f₂ : QuaternionGroup 2 →* G}
    (h1 : f₁ (a 1) = f₂ (a 1)) (h2 : f₁ (xa 0) = f₂ (xa 0)) : f₁ = f₂ := by
  have ha : ∀ i : ZMod (2 * 2), f₁ (a i) = f₂ (a i) := by
    intro i
    rw [show (a i : QuaternionGroup 2) = (a 1) ^ i.val by rw [a_one_pow, ZMod.natCast_zmod_val],
      map_pow, map_pow, h1]
  refine MonoidHom.ext fun q => ?_
  cases q with
  | a i => exact ha i
  | xa i =>
    rw [show (xa i : QuaternionGroup 2) = xa 0 * a i by rw [xa_mul_a, zero_add], map_mul,
      map_mul, h2, ha]

theorem q8_conj_cases : ∀ qx qy : QuaternionGroup 2, qx * qx = a 2 → (qx * (a 1)⁻¹) ^ 2 = 1 →
    qy * qy = a 2 → (qy * (xa 0)⁻¹) ^ 2 = 1 →
      ∃ s : QuaternionGroup 2, s * a 1 * s⁻¹ = qx ∧ s * xa 0 * s⁻¹ = qy := by
  decide

theorem q8_sq_cases : ∀ s : QuaternionGroup 2, s * s = 1 ∨ s * s = a 2 := by
  decide

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {z : Y}

theorem twSwap_of_pair (hD : TightDatum R S z)
    (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) (hO : oddCoreImg R = ⊥)
    (hP : ∀ c ∈ Subgroup.centralizer ({z} : Set Y), c * c = 1 → (∀ r ∈ R, c * r = r * c) →
      c = 1 ∨ c = z)
    {g : Y} (hg : g ∈ Subgroup.centralizer ({z} : Set Y)) (hg4 : g ^ 4 = 1) (hg1 : g * g ≠ 1)
    (hgz : g * g ≠ z) : TwSwap R z := by
  by_contra hno
  have hsq : ∀ r ∈ R, ⁅g, r⁆ ^ 2 = 1 := fun r hr => by
    by_contra h
    exact hno ⟨g, hg, r, hr, by rw [hO, Subgroup.mem_bot]; exact h⟩
  obtain ⟨-, hR2, -⟩ := TA3.datum_shape_of_odd hD hq8 hO
  obtain ⟨eS⟩ := hq8
  set φ : QuaternionGroup 2 →* Y :=
    R.subtype.comp ((S : Subgroup R).subtype.comp eS.symm.toMonoidHom) with hφdef
  have hφi : Function.Injective φ :=
    R.subtype_injective.comp (Subtype.val_injective.comp eS.symm.injective)
  have hφR : ∀ q, φ q ∈ R := fun q => ((eS.symm q : (S : Subgroup R)) : R).2
  have hS : (⊤ : Subgroup R) = (S : Subgroup R) :=
    S.is_maximal' (hR2.of_equiv Subgroup.topEquiv.symm) le_top
  have hSR : ∀ r ∈ R, ∃ q, φ q = r := fun r hr => by
    have hrS : (⟨r, hr⟩ : R) ∈ (S : Subgroup R) := hS ▸ Subgroup.mem_top _
    refine ⟨eS ⟨⟨r, hr⟩, hrS⟩, ?_⟩
    simp [hφdef]
  have hφz : φ (a 2) = z := by
    refine hD.eq_of_orderOf_eq_two (hφR _) ?_
    rw [orderOf_injective φ hφi]
    exact orderOf_eq_prime (by decide) (by decide)
  have hz2 : z * z = 1 := by rw [← hφz, ← map_mul, show a 2 * a 2 = (1 : QuaternionGroup 2) by
    decide, map_one]
  have hgz' : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hgR : ∀ q, g * φ q * g⁻¹ ∈ R := fun q =>
    (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hg) _).mp (hφR q)
  have hcond : ∀ q₀ : QuaternionGroup 2, q₀ * q₀ = a 2 → ∀ qx, φ qx = g * φ q₀ * g⁻¹ →
      qx * qx = a 2 ∧ (qx * q₀⁻¹) ^ 2 = 1 := by
    intro q₀ hq₀ qx hqx
    refine ⟨hφi ?_, hφi ?_⟩
    · rw [map_mul, hqx, hφz]
      calc g * φ q₀ * g⁻¹ * (g * φ q₀ * g⁻¹) = g * φ (q₀ * q₀) * g⁻¹ := by rw [map_mul]; group
        _ = z := by rw [hq₀, hφz, hgz', mul_inv_cancel_right]
    · have h1 := hsq _ (hφR q₀)
      rw [map_pow, map_mul, map_inv, hqx, map_one]
      rw [commutatorElement_def] at h1
      exact h1
  obtain ⟨qx, hqx⟩ := hSR _ (hgR (a 1))
  obtain ⟨qy, hqy⟩ := hSR _ (hgR (xa 0))
  obtain ⟨hx2, hx3⟩ := hcond (a 1) (by decide) qx hqx
  obtain ⟨hy2, hy3⟩ := hcond (xa 0) (by decide) qy hqy
  obtain ⟨s, hs1, hs2⟩ := q8_conj_cases qx qy hx2 hx3 hy2 hy3
  have hact : ∀ q, g * φ q * g⁻¹ = φ s * φ q * (φ s)⁻¹ := by
    have h1 := q8_hom_ext (f₁ := (MulAut.conj g).toMonoidHom.comp φ)
      (f₂ := (MulAut.conj (φ s)).toMonoidHom.comp φ)
      (by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← hqx, ← hs1, map_mul, map_mul, map_inv])
      (by simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          rw [← hqy, ← hs2, map_mul, map_mul, map_inv])
    intro q
    have h2 := DFunLike.congr_fun h1 q
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2
  have hhR : ∀ r ∈ R, (φ s)⁻¹ * g * r = r * ((φ s)⁻¹ * g) := by
    intro r hr
    obtain ⟨q, rfl⟩ := hSR r hr
    calc (φ s)⁻¹ * g * φ q = (φ s)⁻¹ * (g * φ q * g⁻¹) * g := by group
      _ = (φ s)⁻¹ * (φ s * φ q * (φ s)⁻¹) * g := by rw [hact q]
      _ = φ q * ((φ s)⁻¹ * g) := by group
  have hhC : (φ s)⁻¹ * g ∈ Subgroup.centralizer ({z} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hD.cent (hφR s))) hg
  have hh2 : (φ s)⁻¹ * g * ((φ s)⁻¹ * g) = φ (s⁻¹ * s⁻¹) * (g * g) := by
    have h1 := hact s⁻¹
    rw [map_inv] at h1
    calc (φ s)⁻¹ * g * ((φ s)⁻¹ * g) = (φ s)⁻¹ * (g * (φ s)⁻¹ * g⁻¹) * (g * g) := by group
      _ = (φ s)⁻¹ * (φ s * (φ s)⁻¹ * (φ s)⁻¹) * (g * g) := by rw [h1]
      _ = φ (s⁻¹ * s⁻¹) * (g * g) := by rw [map_mul, map_inv]; group
  have hcR : ∀ r ∈ R, (φ s)⁻¹ * g * ((φ s)⁻¹ * g) * r =
      r * ((φ s)⁻¹ * g * ((φ s)⁻¹ * g)) := by
    intro r hr
    calc (φ s)⁻¹ * g * ((φ s)⁻¹ * g) * r = (φ s)⁻¹ * g * ((φ s)⁻¹ * g * r) := by group
      _ = (φ s)⁻¹ * g * (r * ((φ s)⁻¹ * g)) := by rw [hhR r hr]
      _ = ((φ s)⁻¹ * g * r) * ((φ s)⁻¹ * g) := by group
      _ = (r * ((φ s)⁻¹ * g)) * ((φ s)⁻¹ * g) := by rw [hhR r hr]
      _ = r * ((φ s)⁻¹ * g * ((φ s)⁻¹ * g)) := by group
  have hg4' : g * g * (g * g) = 1 := by
    rw [← hg4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rcases q8_sq_cases s⁻¹ with hs | hs
  · rw [hs, map_one, one_mul] at hh2
    rcases hP _ (Subgroup.mul_mem _ hhC hhC) (by rw [hh2]; exact hg4') hcR with h0 | h0
    · exact hg1 (hh2 ▸ h0)
    · exact hgz (hh2 ▸ h0)
  · rw [hs, hφz] at hh2
    have hzgg : (g * g) * z = z * (g * g) := by
      rw [mul_assoc, hgz', ← mul_assoc, hgz', mul_assoc]
    have hc2 : z * (g * g) * (z * (g * g)) = 1 := by
      calc z * (g * g) * (z * (g * g)) = z * ((g * g) * z) * (g * g) := by group
        _ = z * (z * (g * g)) * (g * g) := by rw [hzgg]
        _ = z * z * (g * g * (g * g)) := by group
        _ = 1 := by rw [hz2, hg4', one_mul]
    rcases hP _ (Subgroup.mul_mem _ hhC hhC) (by rw [hh2]; exact hc2) hcR with h0 | h0
    · apply hgz
      rw [hh2] at h0
      calc g * g = z * (z * (g * g)) := by rw [← mul_assoc, hz2, one_mul]
        _ = z := by rw [h0, mul_one]
    · apply hg1
      rw [hh2] at h0
      calc g * g = z * (z * (g * g)) := by rw [← mul_assoc, hz2, one_mul]
        _ = 1 := by rw [h0, hz2]

end E3S3T

namespace MF163.U3

open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups
  CFSG.GH74.KGroups.U33

theorem outer_pair_u3_three {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    {z : X} (hD : TightDatum R S z) (hq8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    (hgen : TightSelfGen R) (h3 : ¬ TightActs3 R z) {N : Subgroup X} [N.Normal]
    [IsSimpleGroup N] (hC : Subgroup.centralizer (N : Set X) = ⊥)
    (hL : CFSG.Blueprint.LieModel ↥N .PSU 3 3 1) :
    oddCoreImg R = ⊥ ∧ (∃ u ∈ R, u ^ 4 = 1 ∧ u ∉ N) ∧
      ∀ c ∈ Subgroup.centralizer ({z} : Set X), c * c = 1 → (∀ r ∈ R, c * r = r * c) →
        c = 1 ∨ c = z := by
  classical
  obtain ⟨e⟩ := U33.equiv_of_lieModel hL
  obtain ⟨M, hMP, hMA⟩ := U33.autModel e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, QP_closure, u33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  set ψ := M.actHom N with hψ
  have hψi : Function.Injective ψ := M.actHom_injective N hC
  have hψN : ∀ n (hn : n ∈ N), ψ n = (M.e ⟨n, hn⟩ : Equiv.Perm (Fin 28)) := by
    intro n hn
    show (M.Φ (MulAut.conjNormal n) : Equiv.Perm (Fin 28)) = _
    rw [show (MulAut.conjNormal n : MulAut N) = MulAut.conj ⟨n, hn⟩ from
      MulAut.conjNormal_val (h := ⟨n, hn⟩)]
    exact autModel_Φ_conj_eq M hPA ⟨n, hn⟩
  have hle1 : QP.originalSubgroup ≤ ψ.range := by
    intro m hm
    rw [← hMP] at hm
    refine ⟨((M.e.symm ⟨m, hm⟩ : N) : X), ?_⟩
    rw [hψN _ (M.e.symm ⟨m, hm⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
  have hle2 : ψ.range ≤ QA.originalSubgroup := by
    rintro _ ⟨x, rfl⟩
    rw [← hMA]
    exact M.actHom_mem N x
  have hP : Nat.card QP.originalSubgroup = 6048 := by rw [card_group QP QP_ok, QP_valid.2]
  have hA : Nat.card QA.originalSubgroup = 12096 := by rw [card_group QA QA_ok, QA_valid.2]
  obtain ⟨k, hk⟩ : 6048 ∣ Nat.card ψ.range := hP ▸ Subgroup.card_dvd_of_le hle1
  have h2 : Nat.card ψ.range ∣ 12096 := hA ▸ Subgroup.card_dvd_of_le hle2
  have hk2 : k ∣ 2 := by
    rw [hk] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 6048) (by simpa using h2)
  have hLN : ∀ y, ψ y ∈ elemsT QP ↔ y ∈ N := by
    intro y
    rw [mem_elemsT QP QP_ok]
    constructor
    · intro hy
      rw [← hMP] at hy
      have h1 : ψ ((M.e.symm ⟨ψ y, hy⟩ : N) : X) = ψ y := by
        rw [hψN _ (M.e.symm ⟨ψ y, hy⟩).2, Subtype.coe_eta, MulEquiv.apply_symm_apply]
      rw [← hψi h1]
      exact (M.e.symm ⟨ψ y, hy⟩).2
    · intro hy
      rw [hψN y hy, ← hMP]
      exact (M.e ⟨y, hy⟩).2
  rcases (Nat.dvd_prime Nat.prime_two).1 hk2 with rfl | rfl
  ·
    exfalso
    have hR : ψ.range = QP.originalSubgroup :=
      (Subgroup.eq_of_le_of_card_ge hle1 (by rw [hk, hP])).symm
    have hLP : ∀ m, m ∈ elemsT QP ↔ ∃ y, ψ y = m := fun m => by
      rw [mem_elemsT QP QP_ok, ← hR]
      rfl
    obtain ⟨x, k', hx, hxk, hxr, -⟩ := good_of_goodCheck (ι := ψ) hψi hLP u33_check_9743 hD hq8
    exact h3 ⟨x, k', hx, hxk, hxr⟩
  have hR : ψ.range = QA.originalSubgroup :=
    Subgroup.eq_of_le_of_card_ge hle2 (by rw [hk, hA])
  have hLA : ∀ m, m ∈ elemsT QA ↔ ∃ y, ψ y = m := fun m => by
    rw [mem_elemsT QA QA_ok, ← hR]
    rfl
  have hNtop : N ≠ ⊤ := by
    intro hN
    have hle : ψ.range ≤ QP.originalSubgroup := by
      rintro _ ⟨y, rfl⟩
      rw [← mem_elemsT QP QP_ok, hLN, hN]
      trivial
    have := Subgroup.card_le_of_le hle
    rw [hR, hA, hP] at this
    omega
  have hck := u33_check_9744
  have hcov := (Bool.and_eq_true_iff.1 hck).1
  have h55 : Certificates.TL4MF163U3Inv.centInvCheck (elemsT QP) (elemsT QA)
      (pickReps (elemsT QA)) = true := Certificates.certificate55111
  obtain ⟨r, hr, g, hg⟩ := cover_of_coverB hψi hLA hcov hD.order
  have hVP := verdictPred_of_check hψi hLA (by norm_num : 100 < 243) hLN hck hr
  have hNO : NoOddNormalAt3 z := noOddNormalAt3_of_conj g (hg ▸ hVP.1)
  have hO : oddCoreImg R = ⊥ := oddCoreImg_eq_bot_3 hNO hD.cent hD.le_normalizer
  obtain ⟨-, hR2, u, v, hu, hv, huu, hvv, hvu, hlist⟩ := datum_shape_of_odd hD hq8 hO
  have hnorm : ∀ c ∈ Subgroup.centralizer ({z} : Set X),
      c * u * c⁻¹ ∈ q8List z u v ∧ c * v * c⁻¹ ∈ q8List z u v := fun c hc =>
    ⟨hlist _ ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hc) u).mp hu),
      hlist _ ((Subgroup.mem_normalizer_iff.mp (hD.le_normalizer hc) v).mp hv)⟩
  have hNuv : ¬ (u ∈ N ∧ v ∈ N) := fun huv =>
    not_selfGen_of_le inferInstance hNtop (fun x hx => mem_of_mem_q8List huv.1 huv.2 huu
      (hlist x hx)) hgen
  have h3uv : ∀ x ∈ Subgroup.centralizer ({z} : Set X), x ^ 3 = 1 →
      x * u = u * x ∧ x * v = v * x := by
    intro x hx hx3
    by_contra hne
    apply h3
    have hx3' : x ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hx3
    rw [not_and_or] at hne
    rcases hne with hne | hne
    · refine ⟨x, 1, hx, hx3', u, hu, fun hm => hne ?_⟩
      rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · refine ⟨x, 1, hx, hx3', v, hv, fun hm => hne ?_⟩
      rw [hO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
  have hz2 : z * z = 1 := by rw [← pow_two, ← hD.order, pow_orderOf_eq_one]
  have hu4 : ∀ w : X, w * w = z → w ^ 4 = 1 := fun w hw => by
    rw [show w ^ 4 = (w * w) * (w * w) by simp only [pow_succ, pow_zero, one_mul, mul_assoc],
      hw, hz2]
  refine ⟨hO, ?_, fun c hcC hc2 hcR => eq_of_pair_of_check hψi hLA inferInstance hLN hcov h55
    hD.order huu hvv hvu hnorm hNuv h3uv (Subgroup.mem_centralizer_singleton_iff.mp hcC) hc2
    (hcR u hu) (hcR v hv)⟩
  by_cases huN : u ∈ N
  · exact ⟨v, hv, hu4 v hvv, fun hvN => hNuv ⟨huN, hvN⟩⟩
  · exact ⟨u, hu, hu4 u huu, huN⟩

end MF163.U3

namespace E3S3T

open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.Proofs2 CFSG.RankThree.CentralCover
  CFSG.Assembly.LowTwoRank

theorem exists_elem_u3_three {X : Type} [Group X] {N : Subgroup X} {K : Type} [Field K]
    (h : UnitaryFieldData 3 1 K)
    (e : ↥N ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) K)) {z : X}
    (hzN : z ∈ N) (hz : orderOf z = 2) :
    ∃ g ∈ Subgroup.centralizer ({z} : Set X), g ^ 4 = 1 ∧ g * g ≠ 1 ∧ g * g ≠ z := by
  obtain ⟨π, hrange, hk, hπ1⟩ := Q5U3.exists_frame h (by norm_num) e hzN hz
  have : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := h.charP
  have hcard : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, h.card]; norm_num
  obtain ⟨l, hl⟩ : IsSquare (-1 : K) :=
    FiniteField.isSquare_neg_one_iff.mpr (by rw [hcard]; norm_num)
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  have hll : l * l = -1 := hl.symm
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hll
    exact one_ne_zero (neg_eq_zero.mp hll.symm)
  have hbar : h.bar l * l = 1 := by
    rw [UnitaryFieldData.bar_apply, pow_one]
    linear_combination (l * l - 1) * hll
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  let D : GL (Fin 2) K := ⟨!![l, 0; 0, 1], !![l⁻¹, 0; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hl0]⟩
  have hDm : D ∈ GU2Stated (3 ^ 1) K := by
    rw [Lemma41aU3.mem_GU2Stated_iff h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two, hbar]
  set A : ↥(GU2Stated (3 ^ 1) K) := ⟨D, hDm⟩ with hA
  set N1 : ↥(GU2Stated (3 ^ 1) K) := ⟨-1, Q5U3.neg_one_mem_GU2 h⟩ with hN1
  have hAA : ((A * A : ↥(GU2Stated (3 ^ 1) K)) : GL (Fin 2) K) =
      (⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩ :
          GL (Fin 2) K) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, D, Matrix.mul_apply, Fin.sum_univ_two, hll]
  refine ⟨π A, ?_, ?_, ?_, ?_⟩
  · have h1 : π A ∈ π.range := ⟨A, rfl⟩
    rw [hrange] at h1
    exact h1.2
  · have h1 : A * A * (A * A) = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, hAA]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [show π A ^ 4 = π (A * A * (A * A)) by
      simp only [map_mul, pow_succ, pow_zero, one_mul, mul_assoc], h1, map_one]
  · intro h1
    rw [← map_mul] at h1
    obtain ⟨ω, -, hω⟩ := hk _ h1
    have e00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have e11 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp only [hAA, Matrix.GeneralLinearGroup.coe_scalar] at e00 e11
    simp at e00 e11
    exact h2 (by linear_combination e11 - e00)
  · intro h1
    rw [← map_mul] at h1
    have h1' : π (A * A * N1) = 1 := by rw [map_mul, h1, hN1, hπ1, hz2]
    obtain ⟨ω, -, hω⟩ := hk _ h1'
    have e00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hω
    have e11 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hω
    simp only [Subgroup.coe_mul, Units.val_mul, hAA, hN1,
      Matrix.GeneralLinearGroup.coe_scalar] at e00 e11
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
    exact h2 (by linear_combination e00 - e11)

end E3S3T

theorem twKindU33_proved : TwKindU33 := by
  intro X _ _ R S z hm hs h3 hi6 hl
  have hD := hm.datum
  have hNn : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hQs : IsSimpleGroup (FStarQuot X) := by
    rcases hl with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact (ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1 h).2
    · simp [Blueprint.chevalleyExceptionalTags] at ht
    · simp [Blueprint.reeTitsTags] at ht
    · cases ht
  have hnab : ∃ a b : ↥(genFittingFStar X), a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have hZ : Subgroup.center ↥(genFittingFStar X) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    obtain ⟨a, b, hab⟩ := hQs.toNontrivial.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.mpr (hZ ▸ Subgroup.mem_top _))
  have hC := Nobq.centralizer_genFittingFStar_eq_bot hnab
  obtain ⟨eF⟩ := MFMuZ2.nonempty_fstar_equiv (MFMuZ2.center_fstar_eq_bot hnab)
  have hLN : Blueprint.LieModel ↥(genFittingFStar X) .PSU 3 3 1 :=
    MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inr rfl) hl
  obtain ⟨hO, ⟨u, -, hu4, huN⟩, hP⟩ :=
    MF163.U3.outer_pair_u3_three hD hm.cls.1 hm.cls.2.1 h3 hC hLN
  refine ⟨E3S3T.two_dvd_index_of_not_mem hu4 huN, ?_⟩
  obtain ⟨ιq, -, -, hιqz⟩ := MF163.exists_quat_of_member hm
  obtain ⟨q, hq2, hqN⟩ := E3S3T.exists_q8_mem_of_index_dvd_six hi6 ιq
  have hqq : q * q = QuaternionGroup.a 2 := by
    have hQ : ∀ q : QuaternionGroup 2, q ^ 2 ≠ 1 → q * q = QuaternionGroup.a 2 := by decide
    exact hQ q hq2
  have hzN : z ∈ genFittingFStar X := by
    rw [← hιqz, ← hqq, map_mul]
    exact Subgroup.mul_mem _ hqN hqN
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLN
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, by rw [hK]; norm_num⟩
  obtain ⟨g, hg, hg4, hg1, hgz⟩ := E3S3T.exists_elem_u3_three h e hzN hD.order
  exact E3S3T.twSwap_of_pair hD hm.cls.1 hO hP hg hg4 hg1 hgz

end CFSG.ClassicalInvolution.Q3.TL4
