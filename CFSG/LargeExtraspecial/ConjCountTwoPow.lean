module

public import CFSG.LargeExtraspecial.S6Eight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.LargeExtraspecial.S4

theorem dvd_natCard_of_forall_dvd_ncard_orbit {H α : Type*} [Group H] [MulAction H α]
    [Finite α] {n : ℕ} (h : ∀ x : α, n ∣ (MulAction.orbit H x).ncard) : n ∣ Nat.card α := by
  classical
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient H α)
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits' H α), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  induction ω using Quotient.inductionOn with
  | h x =>
    rw [Nat.card_coe_set_eq]
    change n ∣ (MulAction.orbitRel.Quotient.orbit (Quotient.mk'' x)).ncard
    rw [MulAction.orbitRel.Quotient.orbit_mk (G := H) x]
    exact h x

theorem pow_two_dvd_of_dvd_two_pow_of_le {n k m : ℕ} (hn : n ∣ 2 ^ m) (h : 2 ^ k ≤ n) :
    2 ^ k ∣ n := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hn
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by norm_num)).1 h)

namespace Setting

variable {G : Type*} [Group G] (S : Setting G)

def qIncl : S.Q →* G := S.M.subtype.comp S.Q.subtype

theorem mem_M_qIncl (q : S.Q) : qIncl S q ∈ S.M := (q : S.M).2

theorem qIncl_mem_QG (q : S.Q) : qIncl S q ∈ S.QG := S.coe_mem_QG q

theorem qIncl_injective : Function.Injective (qIncl S) :=
  S.M.subtype_injective.comp S.Q.subtype_injective

def conjOutside : Set G := {x | IsConj S.z x ∧ x ∉ S.QG}

theorem conj_mem_conjOutside (q : S.Q) {x : G} (hx : x ∈ conjOutside S) :
    qIncl S q * x * (qIncl S q)⁻¹ ∈ conjOutside S := by
  refine ⟨hx.1.trans (isConj_iff.2 ⟨qIncl S q, rfl⟩), fun h => hx.2 ?_⟩
  have := S.conj_mem_QG (S.M.inv_mem (mem_M_qIncl S q)) h
  simpa [mul_assoc] using this

instance instMulActionConjOutside : MulAction S.Q (conjOutside S) where
  smul q x := ⟨qIncl S q * x * (qIncl S q)⁻¹, conj_mem_conjOutside S q x.2⟩
  one_smul x := Subtype.ext (by
    change qIncl S 1 * (x : G) * (qIncl S 1)⁻¹ = x
    simp)
  mul_smul q r x := Subtype.ext (by
    change qIncl S (q * r) * (x : G) * (qIncl S (q * r))⁻¹ =
      qIncl S q * (qIncl S r * (x : G) * (qIncl S r)⁻¹) * (qIncl S q)⁻¹
    simp [mul_assoc])

theorem mem_stabilizer_conjOutside (x : conjOutside S) (q : S.Q) :
    q ∈ MulAction.stabilizer S.Q x ↔ qIncl S q * x * (qIncl S q)⁻¹ = x := by
  rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  rfl

variable [Finite G]

theorem two_pow_width_succ_dvd_index_of_not_mem_M (x : conjOutside S)
    (hx : (x : G) ∉ S.M) :
    2 ^ (S.width + 1) ∣ (MulAction.stabilizer S.Q x).index := by
  classical
  set K := MulAction.stabilizer S.Q x with hK
  set D := K.map (qIncl S) with hD
  have hKQ : D ≤ S.QG := by
    rintro _ ⟨k, -, rfl⟩
    exact qIncl_mem_QG S k
  have hzK : S.zQ ∉ K := by
    intro h
    rw [mem_stabilizer_conjOutside] at h
    exact hx (S.mem_M_iff.2 (mul_inv_eq_iff_eq_mul.1 h).symm)
  have hzD : S.z ∉ D := by
    rintro ⟨k, hk, hkz⟩
    refine hzK ?_
    have hk' : k = S.zQ := qIncl_injective S (by rw [hkz]; rfl)
    rw [← hk']
    exact hk
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have haQ := hKQ ha
    have hbQ := hKQ hb
    rcases S.commutator_eq_one_or_z haQ hbQ with h | h
    · calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h, one_mul]
    · exact absurd (h ▸ D.mul_mem (D.mul_mem (D.mul_mem ha hb) (D.inv_mem ha)) (D.inv_mem hb))
        hzD
  have htot : S.clSub D ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub D) := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    obtain ⟨a, haD, haQ, rfl⟩ := S.mem_clSub_iff.mp hv
    obtain ⟨b, hbD, hbQ, rfl⟩ := S.mem_clSub_iff.mp hu
    rw [QuadraticMap.polarBilin_apply_apply, S.polar_cl_eq_zero_iff hbQ haQ]
    exact (hDab a haD b hbD).symm
  have hdim : finrank (ZMod 2) (S.clSub D) ≤ S.width := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (S.clSub D)
    have h2 := Submodule.finrank_mono htot
    rw [S.finrank_Qt_eq_two_mul_width] at h1
    omega
  have hinj : Function.Injective
      (fun d : D => (⟨S.cl (d : G), S.cl_mem_clSub d.2 (hKQ d.2)⟩ : S.clSub D)) := by
    intro a b hab
    have hcl : S.cl (a : G) = S.cl (b : G) :=
      congrArg (fun w : S.clSub D => (w : S.Qt)) hab
    have haQ := hKQ a.2
    have hbQ := hKQ b.2
    rcases (S.cl_eq_cl_iff haQ hbQ).mp hcl with h | h
    · exact Subtype.ext h.symm
    · exact absurd (show S.z ∈ D from by
        rw [show S.z = (a : G)⁻¹ * (b : G) from by rw [h]; group]
        exact D.mul_mem (D.inv_mem a.2) b.2) hzD
  have hcardD : Nat.card D ≤ 2 ^ S.width := by
    calc Nat.card D ≤ Nat.card (S.clSub D) := Nat.card_le_card_of_injective _ hinj
      _ = 2 ^ finrank (ZMod 2) (S.clSub D) := S.card_submodule _
      _ ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) hdim
  have hcardK : Nat.card K = Nat.card D := by
    rw [hD, Subgroup.card_map_of_injective (qIncl_injective S)]
  have hcardQ : Nat.card S.Q = 2 ^ (S.width + 1) * 2 ^ S.width := by
    rw [S.card_Q_eq, show 1 + 2 * S.width = (S.width + 1) + S.width by ring, pow_add]
  have hle : 2 ^ (S.width + 1) ≤ K.index := by
    have h := Subgroup.card_mul_index K
    have hmain : 2 ^ (S.width + 1) * Nat.card K ≤ Nat.card S.Q := by
      calc 2 ^ (S.width + 1) * Nat.card K = 2 ^ (S.width + 1) * Nat.card D := by
            rw [hcardK]
        _ ≤ 2 ^ (S.width + 1) * 2 ^ S.width := Nat.mul_le_mul_left _ hcardD
        _ = Nat.card S.Q := hcardQ.symm
    have hthis : 2 ^ (S.width + 1) * Nat.card K ≤ K.index * Nat.card K := by
      calc 2 ^ (S.width + 1) * Nat.card K ≤ Nat.card S.Q := hmain
        _ = Nat.card K * K.index := h.symm
        _ = K.index * Nat.card K := by rw [mul_comm]
    exact Nat.le_of_mul_le_mul_right hthis Nat.card_pos
  exact pow_two_dvd_of_dvd_two_pow_of_le (S.card_Q_eq ▸ K.index_dvd_card) hle

theorem pow_dvd_index_of_mem_M (x : conjOutside S) (hxM : (x : G) ∈ S.M) {k : ℕ}
    (h2 : k ≤ finrank (ZMod 2)
      (CFSG.RankThree.OrthogonalInvolutions.commSpace
        ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    2 ^ k ∣ (MulAction.stabilizer S.Q x).index := by
  classical
  set σ : S.Qt ≃ₗ[ZMod 2] S.Qt := ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hσ
  set K := MulAction.stabilizer S.Q x with hKdef
  set W := CFSG.RankThree.OrthogonalInvolutions.fixSpace σ with hW
  have hmem : ∀ k : K, qIncl S k ∈ S.clPre W := by
    intro k
    refine ⟨qIncl_mem_QG S k, ?_⟩
    rw [hW, CFSG.RankThree.OrthogonalInvolutions.mem_fixSpace, hσ,
      S.ρ_cl ⟨x, hxM⟩ (qIncl_mem_QG S k)]
    have hk := (mem_stabilizer_conjOutside S x k).1 k.2
    have hc : (x : G) * qIncl S k * (x : G)⁻¹ = qIncl S k := by
      rw [← mul_inv_eq_iff_eq_mul.1 hk, mul_inv_cancel_right]
    exact congrArg S.cl hc
  have hinj : Function.Injective (fun k : K => (⟨qIncl S k, hmem k⟩ : S.clPre W)) := by
    intro k l hkl
    have h : qIncl S k = qIncl S l := congrArg (fun w : S.clPre W => (w : G)) hkl
    exact Subtype.ext (qIncl_injective S h)
  have hle : Nat.card K ≤ Nat.card (S.clPre W) := Nat.card_le_card_of_injective _ hinj
  have hd : finrank (ZMod 2) (CFSG.RankThree.OrthogonalInvolutions.commSpace σ) +
      finrank (ZMod 2) W = finrank (ZMod 2) S.Qt :=
    CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace σ
  have hcardQ : Nat.card S.Q = 2 * 2 ^ finrank (ZMod 2) S.Qt := by
    rw [← S.card_QG_eq_card_Q, S.card_QG_eq, S.card_Qt]
  have hcardW : Nat.card (S.clPre W) = 2 * 2 ^ finrank (ZMod 2) W := by
    rw [S.card_clPre, S.card_submodule]
  have hcardK : Nat.card K ≤ 2 * 2 ^ finrank (ZMod 2) W := hcardW ▸ hle
  have hmain : 2 ^ k * Nat.card K ≤ Nat.card S.Q := by
    calc 2 ^ k * Nat.card K ≤ 2 ^ k * (2 * 2 ^ finrank (ZMod 2) W) :=
          Nat.mul_le_mul_left _ hcardK
      _ = 2 ^ (k + 1) * 2 ^ finrank (ZMod 2) W := by rw [pow_succ]; ring
      _ ≤ 2 ^ (finrank (ZMod 2) (CFSG.RankThree.OrthogonalInvolutions.commSpace σ) + 1) *
            2 ^ finrank (ZMod 2) W :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ (1 + finrank (ZMod 2) S.Qt) := by
          rw [← pow_add]
          congr 1
          omega
      _ = Nat.card S.Q := by rw [hcardQ, pow_add, pow_one]
  have hle' : 2 ^ k ≤ K.index := by
    have h := Subgroup.card_mul_index K
    have hthis : 2 ^ k * Nat.card K ≤ K.index * Nat.card K := by
      calc 2 ^ k * Nat.card K ≤ Nat.card S.Q := hmain
        _ = Nat.card K * K.index := h.symm
        _ = K.index * Nat.card K := by rw [mul_comm]
    exact Nat.le_of_mul_le_mul_right hthis Nat.card_pos
  exact pow_two_dvd_of_dvd_two_pow_of_le (S.card_Q_eq ▸ K.index_dvd_card) hle'

end Setting

variable {G : Type*} [Group G] [Finite G]

theorem card_conj_mod_two_pow (S : Setting G) {k : ℕ} (hk : k ≤ S.width + 1)
    (hdim : ∀ y : G, IsConj S.z y → (hyM : y ∈ S.M) → y ∉ S.QG →
      k ≤ finrank (ZMod 2)
        (CFSG.RankThree.OrthogonalInvolutions.commSpace
          ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))) :
    Nat.card {x : G | IsConj S.z x} % 2 ^ k =
      Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} % 2 ^ k := by
  have hdvd : 2 ^ k ∣ Nat.card (Setting.conjOutside S) := by
    refine dvd_natCard_of_forall_dvd_ncard_orbit (H := S.Q) fun x => ?_
    rw [← MulAction.index_stabilizer S.Q x]
    by_cases hxM : (x : G) ∈ S.M
    · exact Setting.pow_dvd_index_of_mem_M S x hxM (hdim x x.2.1 hxM x.2.2)
    · exact dvd_trans (pow_dvd_pow 2 hk)
        (Setting.two_pow_width_succ_dvd_index_of_not_mem_M S x hxM)
  have hsplit : Nat.card {x : G | IsConj S.z x} =
      Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} + Nat.card (Setting.conjOutside S) := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
    exact (Set.ncard_inter_add_ncard_diff_eq_ncard {x : G | IsConj S.z x}
      (S.QG : Set G)).symm
  obtain ⟨t, ht⟩ := hdvd
  rw [hsplit, ht]
  exact Nat.add_mul_mod_self_left _ _ _

variable {S : Setting G} {g : G}

theorem card_conj_inter_QG_eq (H : Hyp4 S g) (hF : S6.FusionCtl S g) :
    Nat.card {x : G | IsConj S.z x ∧ x ∈ S.QG} =
      1 + 2 * Nat.card (MulAction.orbit S.Mbar (S.cl (g * S.z * g⁻¹))) := by
  classical
  set a : G := g * S.z * g⁻¹ with ha
  set A : Set G := {x | ∃ m : S.M, x = (m : G) * a * (m : G)⁻¹} with hA
  set O : Set S.Qt := MulAction.orbit S.Mbar (S.cl a) with hO
  haveI : Fintype O := Fintype.ofFinite O
  have haQ : a ∈ S.QG := by rw [ha]; exact H.conj_mem
  have hane : a ≠ S.z := by rw [ha]; exact H.conj_ne
  have hclane : S.cl a ≠ 0 := S.cl_conj_z_ne_zero haQ hane
  have h0O : (0 : S.Qt) ∉ O := by
    intro h0
    rw [hO] at h0
    obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp h0
    have hm' : ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = 0 := hm
    exact hclane ((LinearEquiv.map_eq_zero_iff _).mp hm')
  have hset : {x : G | IsConj S.z x ∧ x ∈ S.QG} = insert S.z A := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_insert_iff, hA, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hc, hxQ⟩
      by_cases hxz : x = S.z
      · exact Or.inl hxz
      · right
        obtain ⟨k, hk⟩ := isConj_iff.mp hc
        obtain ⟨m, hm, hmx⟩ := hF k (hk ▸ hxQ) (hk ▸ hxz)
        rw [ha]
        exact ⟨⟨m, hm⟩, (hmx.trans hk).symm⟩
    · rintro (rfl | ⟨m, rfl⟩)
      · exact ⟨IsConj.refl _, S.z_mem_QG⟩
      · refine ⟨isConj_iff.2 ⟨(m : G) * g, ?_⟩, S.conj_mem_QG m.2 haQ⟩
        rw [ha]
        exact S4.mul_conj_z S (m : G) g
  have hzA : S.z ∉ A := by
    rw [hA]
    rintro ⟨m, hm⟩
    have h1 : (m : G)⁻¹ * S.z * (m : G) = a := by rw [hm]; group
    have h2 : (m : G)⁻¹ * S.z * (m : G) = S.z := by
      rw [S.z_comm (S.M.inv_mem m.2), mul_assoc, inv_mul_cancel, mul_one]
    exact hane (h1 ▸ h2)
  have hAO : A = {x : G | x ∈ S.QG ∧ S.cl x ∈ O} := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨S.conj_mem_QG m.2 haQ, ?_⟩
      rw [hO]
      refine MulAction.mem_orbit_iff.mpr
        ⟨⟨S.ρ m, MonoidHom.mem_range.mpr ⟨m, rfl⟩⟩, ?_⟩
      change ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) =
        S.cl ((m : G) * a * (m : G)⁻¹)
      rw [ha, S4.ρ_cl_conj_z S m H.conj_mem]
      congr 1
      exact S4.mul_conj_z S (m : G) g
    · rintro ⟨hxQ, hxO⟩
      rw [hO] at hxO
      obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp hxO
      obtain ⟨μ, hμ⟩ := MonoidHom.mem_range.mp (show (y : S.O) ∈ S.ρ.range from y.2)
      have hy' : ((S.ρ μ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl a) = S.cl x := by
        rw [hμ]
        exact hy
      rw [S4.ρ_cl_conj_z S μ haQ] at hy'
      have hcls : S.cl x = S.cl ((μ : G) * a * (μ : G)⁻¹) := by
        rw [← hy', ha]
        exact congrArg S.cl (S4.mul_conj_z S (μ : G) g)
      have hμQ : (μ : G) * a * (μ : G)⁻¹ ∈ S.QG := S.conj_mem_QG μ.2 haQ
      rcases (S.cl_eq_cl_iff hxQ hμQ).mp hcls with h | h
      · exact ⟨μ, h.symm⟩
      · have hx_eq : x = ((μ : G) * a * (μ : G)⁻¹) * S.z := by
          rw [h, mul_assoc, S.z_mul_z, mul_one]
        obtain ⟨q, hq, hqa⟩ := S.exists_conj_eq_mul_z haQ (S4.conj_z_ne_one S g) hane
        have hqM : q ∈ S.M := S.QG_le_M hq
        have hzμ : S.z * (μ : G)⁻¹ = (μ : G)⁻¹ * S.z :=
          (S.z_comm (S.M.inv_mem μ.2)).symm
        have hcalc : (((μ : G) * q) * a * ((μ : G) * q)⁻¹) =
            ((μ : G) * a * (μ : G)⁻¹) * S.z := by
          calc ((μ : G) * q) * a * ((μ : G) * q)⁻¹
              = (μ : G) * (q * a * q⁻¹) * (μ : G)⁻¹ := by group
            _ = (μ : G) * (a * S.z) * (μ : G)⁻¹ := by rw [hqa]
            _ = (μ : G) * a * (S.z * (μ : G)⁻¹) := by group
            _ = (μ : G) * a * ((μ : G)⁻¹ * S.z) := by rw [hzμ]
            _ = ((μ : G) * a * (μ : G)⁻¹) * S.z := by group
        refine ⟨μ * ⟨q, hqM⟩, ?_⟩
        change x = ((μ : G) * q) * a * ((μ : G) * q)⁻¹
        rw [hx_eq]
        exact hcalc.symm
  have hB : A = S.cl ⁻¹' O := by
    rw [hAO]
    ext x
    constructor
    · rintro ⟨-, hx⟩; exact hx
    · intro hx
      refine ⟨?_, hx⟩
      by_contra hxQ
      have hx0 : S.cl x = 0 := by
        simp only [Setting.cl, dif_neg hxQ]
      exact h0O (hx0 ▸ hx)
  have hfiber : ∀ b ∈ O.toFinset, Nat.card {x : G // S.cl x = b} = 2 := by
    intro b hb
    have hbO : b ∈ O := by simpa using hb
    obtain ⟨x₀, hx₀Q, hx₀⟩ := S.exists_cl b
    have hclz : S.cl (x₀ * S.z) = b := by rw [S.cl_mul_z hx₀Q, hx₀]
    have hx₀z : (⟨x₀ * S.z, hclz⟩ : {x : G // S.cl x = b}) ≠ ⟨x₀, hx₀⟩ := by
      intro h
      have h1 : x₀ * S.z = x₀ * 1 := by
        simpa using congrArg (fun w : {x : G // S.cl x = b} => w.1) h
      exact S.z_ne_one (mul_left_cancel h1)
    refine (Nat.card_eq_two_iff' (⟨x₀, hx₀⟩ : {x : G // S.cl x = b})).mpr
      ⟨⟨x₀ * S.z, hclz⟩, hx₀z, ?_⟩
    rintro y hyne
    have hyQ : y.1 ∈ S.QG := by
      by_contra hyq
      have hb0 : b = 0 := by
        rw [← y.2]
        simp only [Setting.cl, dif_neg hyq]
      exact h0O (hb0 ▸ hbO)
    have hcl : S.cl x₀ = S.cl y.1 := by rw [hx₀, y.2]
    rcases (S.cl_eq_cl_iff hx₀Q hyQ).mp hcl with h | h
    · exact absurd (Subtype.ext h) hyne
    · exact Subtype.ext h
  have hpre : (S.cl ⁻¹' O).ncard =
      ∑ b ∈ O.toFinset, Nat.card {x : G // S.cl x = b} := by
    have h := Finset.card_preimage_eq_sum_card_image_eq (f := S.cl) (s := O.toFinset)
      (fun b _ => Set.toFinite _)
    rw [Set.coe_toFinset O] at h
    rwa [Nat.card_coe_set_eq] at h
  have hsum : ∑ b ∈ O.toFinset, Nat.card {x : G // S.cl x = b} = 2 * O.ncard := by
    calc ∑ b ∈ O.toFinset, Nat.card {x : G // S.cl x = b}
        = ∑ _b ∈ O.toFinset, 2 := Finset.sum_congr rfl hfiber
      _ = O.toFinset.card * 2 := by rw [Finset.sum_const, nsmul_eq_mul]; simp
      _ = 2 * O.ncard := by
          have hsc : O.toFinset.card = O.ncard := by
            rw [Set.toFinset_card, ← Nat.card_coe_set_eq O, Nat.card_eq_fintype_card]
          rw [hsc]
          ring
  have hcardA : A.ncard = 2 * O.ncard := by rw [hB, hpre, hsum]
  rw [Nat.card_coe_set_eq]
  rw [hset, Set.ncard_insert_of_notMem hzA, hcardA]
  rw [Nat.card_coe_set_eq O]
  ring

end CFSG.LargeExtraspecial
