module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.InvolutionConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSNotConj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSCentral
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4StrongFinal

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped Matrix commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem J4Matrix_pow_twenty : J4Matrix ^ 20 = -1 := by decide +kernel

theorem exists_fixed_vector_of_sq_eq_one (M : Matrix (Fin 2) (Fin 2) (ZMod 11)) (hM : M * M = 1)
    (hne : M ≠ -1) : ∃ w : Fin 2 → ZMod 11, w ≠ 0 ∧ M *ᵥ w = w := by
  have hne' : M + 1 ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_left h)
  have : ∃ v : Fin 2 → ZMod 11, (M + 1) *ᵥ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hne'
    ext i j
    have := congrFun (hcon (Pi.single j 1)) i
    simpa using this
  obtain ⟨v, hv⟩ := this
  refine ⟨(M + 1) *ᵥ v, hv, ?_⟩
  rw [Matrix.mulVec_mulVec, mul_add, hM, mul_one, add_comm]

theorem two_dvd_card_centralizer {G : Type*} [Group G] [Finite G] (u t : G) (htu : t * u = u * t)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : 2 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
  have hmem : t ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 htu
  have hord : orderOf (⟨t, hmem⟩ : Subgroup.centralizer ({u} : Set G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  rw [← hord]
  exact orderOf_dvd_natCard _


theorem exists_centralized_noncentral {t : J} (htN : t ∈ Subgroup.normalizer (Q11 : Set J))
    (ht2 : t * t = 1) (w : Fin 2 → ZMod 11) (hw : w ≠ 0)
    (hMw : heisData.actMat ⟨t, htN⟩ *ᵥ w = w) :
    ∃ u ∈ Q11, u ∉ Subgroup.zpowers qz ∧ t * u * t⁻¹ = u := by
  obtain ⟨q, hq⟩ := heisData.surj (Multiplicative.ofAdd w)
  have hπ : heisData.π (Q11.normalizerMonoidHom ⟨t, htN⟩ q) = heisData.π q := by
    apply Multiplicative.toAdd.injective
    rw [heisData.π_conj, hq]
    exact hMw
  have hker : (Q11.normalizerMonoidHom ⟨t, htN⟩ q) * q⁻¹ ∈ heisData.π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, mul_inv_cancel]
  rw [heisData.ker_eq, center_Q11_eq] at hker
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hker
  have hk' : qz ^ k = t * q * t⁻¹ * (q : J)⁻¹ := by
    have := congrArg Subtype.val hk
    simpa [normalizerMonoidHom_coe] using this
  have hqc : (q : J) * qz = qz * q := qz_commute_of_mem q.2
  have htk : t * q * t⁻¹ = q * qz ^ k := by
    have h1 : t * q * t⁻¹ = qz ^ k * q := by
      rw [hk']; group
    rw [h1]
    exact @comm_zpow_of_comm J (Subgroup.toGroup J) qz q hqc.symm k
  have hconj : t * qz * t⁻¹ ∈ Subgroup.zpowers qz :=
    (conj_mem_zpowers_iff htN).2 (Subgroup.mem_zpowers qz)
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 hconj
  obtain ⟨c, hc⟩ := exists_fixed_lift t q qz orderOf_qz ht2 e k he.symm htk
  refine ⟨q * qz ^ c, Q11.mul_mem q.2 (Subgroup.zpow_mem _ qz_mem c), ?_, hc⟩
  intro hu
  have hq1 : (q : J) ∈ Subgroup.zpowers qz := by
    have h2 := Subgroup.mul_mem _ hu (Subgroup.zpow_mem _ (Subgroup.mem_zpowers qz) (-c))
    rwa [show q * qz ^ c * qz ^ (-c) = (q : J) by group] at h2
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hq1
  have hq2 : q ∈ heisData.π.ker := by
    rw [heisData.ker_eq, center_Q11_eq]
    refine ⟨m, Subtype.ext ?_⟩
    simpa using hm
  rw [MonoidHom.mem_ker, hq] at hq2
  exact hw (Multiplicative.ofAdd.injective hq2)


theorem card_centralizer_noncentral_le {u : J} (hu : u ∈ Q11) (hnu : u ∉ Subgroup.zpowers qz) :
    121 ∣ Nat.card (Subgroup.centralizer ({u} : Set J)) ∧
      Nat.card (Subgroup.centralizer ({u} : Set J)) ≤ 242 := by
  constructor
  · have h := @card_centralizer_of_noncentral J (Subgroup.toGroup J) _ Q11 qz u orderOf_qz
      Q11_commutator_mem_zpowers (fun q hq => qz_commute_of_mem hq) Q11_mem_zpowers_of_central hu hnu
    have h2 : Nat.card ↥(Subgroup.centralizer ({u} : Set J) ⊓ Q11) ∣
        Nat.card (Subgroup.centralizer ({u} : Set J)) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h, card_Q11] at h2
    simpa using h2
  · obtain ⟨n, hn, rfl⟩ := exists_conj_of_mem_Q11 card_centralizer_qx_le u hu hnu
    exact (card_centralizer_conj_le n qx).trans card_centralizer_qx_le

theorem card_centralizer_noncentral_eq {u t : J} (hu : u ∈ Q11) (hnu : u ∉ Subgroup.zpowers qz)
    (htu : t * u = u * t) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card (Subgroup.centralizer ({u} : Set J)) = 2 * 121 := by
  obtain ⟨h1, h2⟩ := card_centralizer_noncentral_le hu hnu
  have hev : 2 ∣ Nat.card (Subgroup.centralizer ({u} : Set J)) :=
    @two_dvd_card_centralizer J (Subgroup.toGroup J) _ u t htu ht2 ht1
  obtain ⟨m, hm⟩ := h1
  obtain ⟨r, hr⟩ := hev
  have hpos : 0 < Nat.card (Subgroup.centralizer ({u} : Set J)) := Nat.card_pos
  rw [hm] at hr h2 hpos ⊢
  omega


theorem fusion_j {t : J} (htN : t ∈ Subgroup.normalizer (Q11 : Set J))
    (hconj : IsConj (nrm₂ ^ 20) t) :
    ∃ m ∈ Subgroup.normalizer (Q11 : Set J), m * nrm₂ ^ 20 * m⁻¹ = t := by
  obtain ⟨hj2, hs2, a, b, ha, hb, hab, hsu⟩ := js_central_facts
  set j : J := nrm₂ ^ 20 with hjdef
  set s : J := (nrm₁ ^ 2 * nrm₂ ^ 5) ^ 11 with hsdef
  have hjN : j ∈ Subgroup.normalizer (Q11 : Set J) :=
    (Subgroup.normalizer (Q11 : Set J)).pow_mem nrm₂_mem_normalizer 20
  have hjact : heisData.actMat ⟨j, hjN⟩ = -1 := by
    have h1 : (⟨j, hjN⟩ : Subgroup.normalizer (Q11 : Set J)) =
        (⟨nrm₂, nrm₂_mem_normalizer⟩ : Subgroup.normalizer (Q11 : Set J)) ^ 20 := rfl
    rw [h1, heisData.actMat_pow, actMat_nrm₂, J4Matrix_pow_twenty]
  have hj1 : j ≠ 1 := by
    intro h
    have h1 : heisData.actMat ⟨j, hjN⟩ = 1 := by
      have : (⟨j, hjN⟩ : Subgroup.normalizer (Q11 : Set J)) = 1 := Subtype.ext h
      rw [this, heisData.actMat_one]
    rw [hjact] at h1
    have := congrFun (congrFun h1 0) 0
    revert this
    decide
  have hfj : fixDim j = 62 := fixDim_nrm₂_pow_twenty
  have hfs : fixDim s = 56 := fixDim_s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, fixDim_one] at hfs
    omega
  have hu₀Q : qx ^ a * qy ^ b ∈ Q11 :=
    Q11.mul_mem (Q11.pow_mem qx_mem a) (Q11.pow_mem qy_mem b)
  have hu₀z : qx ^ a * qy ^ b ∉ Subgroup.zpowers qz := by
    intro h
    have hker : (⟨qx ^ a * qy ^ b, hu₀Q⟩ : Q11) ∈ heisData.π.ker := by
      rw [heisData.ker_eq, center_Q11_eq]
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
      exact ⟨m, Subtype.ext (by simpa using hm)⟩
    rw [MonoidHom.mem_ker] at hker
    have hπ : heisData.π ⟨qx ^ a * qy ^ b, hu₀Q⟩ =
        heisData.π ⟨qx, qx_mem⟩ ^ a * heisData.π ⟨qy, qy_mem⟩ ^ b := by
      have : (⟨qx ^ a * qy ^ b, hu₀Q⟩ : Q11) = ⟨qx, qx_mem⟩ ^ a * ⟨qy, qy_mem⟩ ^ b := rfl
      rw [this, map_mul, map_pow, map_pow]
    rw [hπ, ← heisData_x, ← heisData_y, heisData.π_x, heisData.π_y] at hker
    have h2 := congrArg Multiplicative.toAdd hker
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one] at h2
    have h3 := congrFun h2 0
    have h4 := congrFun h2 1
    simp at h3 h4
    have ha0 : a = 0 := Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff a 11).1 h3) ha
    have hb0 : b = 0 := Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff b 11).1 h4) hb
    rcases hab with h | h
    · exact h ha0
    · exact h hb0
  obtain ⟨d, hd⟩ := isConj_iff.1 hconj
  have ht2 : t * t = 1 := by
    rw [← hd]
    calc d * j * d⁻¹ * (d * j * d⁻¹) = d * (j * j) * d⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have ht1 : t ≠ 1 := by
    intro h
    apply hj1
    have : j = d⁻¹ * t * d := by rw [← hd]; group
    rw [this, h]; group
  have hM : heisData.actMat ⟨t, htN⟩ * heisData.actMat ⟨t, htN⟩ = 1 := by
    rw [← heisData.actMat_mul]
    have : (⟨t, htN⟩ : Subgroup.normalizer (Q11 : Set J)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
    rw [this, heisData.actMat_one]
  by_cases hMn : heisData.actMat ⟨t, htN⟩ = -1
  ·
    have htjQ : t * j ∈ Q11 := by
      have hprod : (⟨t * j, Subgroup.mul_mem _ htN hjN⟩ : Subgroup.normalizer (Q11 : Set J)) =
          ⟨t, htN⟩ * ⟨j, hjN⟩ := rfl
      refine actMat_eq_one_mem ⟨t * j, Subgroup.mul_mem _ htN hjN⟩ ?_
      rw [hprod, heisData.actMat_mul, hMn, hjact, neg_mul_neg, one_mul]
    have hodd : Odd (orderOf (t * j)) := by
      have h1 : orderOf (⟨t * j, htjQ⟩ : Q11) ∣ Nat.card Q11 := orderOf_dvd_natCard _
      rw [card_Q11] at h1
      have h2 : orderOf (t * j) = orderOf (⟨t * j, htjQ⟩ : Q11) := Subgroup.orderOf_coe (⟨t * j, htjQ⟩ : Q11)
      rw [h2]
      exact Odd.of_dvd_nat (by decide) h1
    obtain ⟨k, hk⟩ := @conj_of_inv_odd J (Subgroup.toGroup J) j t hj2 ht2 hodd
    exact ⟨(t * j) ^ k, Subgroup.le_normalizer (Q11.pow_mem htjQ k), hk⟩
  · exfalso
    obtain ⟨w, hw0, hw⟩ := exists_fixed_vector_of_sq_eq_one _ hM hMn
    obtain ⟨u, huQ, hnu, htu⟩ := exists_centralized_noncentral htN ht2 w hw0 hw
    have htu' : t * u = u * t := by
      have : t * u * t⁻¹ = u := htu
      calc t * u = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [this]
    have hCu := card_centralizer_noncentral_eq huQ hnu htu' ht2 ht1
    obtain ⟨n₁, hn₁, hu1⟩ := exists_conj_of_mem_Q11 card_centralizer_qx_le u huQ hnu
    obtain ⟨n₀, hn₀, hu0⟩ := exists_conj_of_mem_Q11 card_centralizer_qx_le (qx ^ a * qy ^ b) hu₀Q hu₀z
    set n : J := n₁ * n₀⁻¹ with hn
    have hun : u = n * (qx ^ a * qy ^ b) * n⁻¹ := by
      have e1 : qx = n₀⁻¹ * (qx ^ a * qy ^ b) * n₀ := by rw [hu0]; group
      rw [hn, mul_assoc n₁ n₀⁻¹ _, mul_inv_rev, inv_inv]
      calc u = n₁ * qx * n₁⁻¹ := hu1
        _ = n₁ * (n₀⁻¹ * (qx ^ a * qy ^ b) * n₀) * n₁⁻¹ := by rw [← e1]
        _ = _ := by group
    set s' : J := n * s * n⁻¹ with hs'
    have hs'u : s' * u = u * s' := by
      rw [hs', hun]
      calc n * s * n⁻¹ * (n * (qx ^ a * qy ^ b) * n⁻¹)
          = n * (s * (qx ^ a * qy ^ b)) * n⁻¹ := by group
        _ = n * ((qx ^ a * qy ^ b) * s) * n⁻¹ := by rw [hsu]
        _ = _ := by group
    have hs'2 : s' * s' = 1 := by
      rw [hs']
      calc n * s * n⁻¹ * (n * s * n⁻¹) = n * (s * s) * n⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hs'1 : s' ≠ 1 := by
      intro h
      apply hs1
      have : s = n⁻¹ * s' * n := by rw [hs']; group
      rw [this, h]; group
    obtain ⟨c, hcu, hc'⟩ := @exists_conj_in_centralizer J (Subgroup.toGroup J) _ u s' t 121
      (by decide) hCu hs'u hs'2 hs'1 htu' ht2 ht1
    have hft : fixDim t = 56 := by
      have : t = ((c : J) * n) * s * ((c : J) * n)⁻¹ := by rw [← hc', hs']; group
      rw [this, fixDim_conj, hfs]
    have hft' : fixDim t = 62 := by rw [← hd, fixDim_conj, hfj]
    omega

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
