module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33I
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33G

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem inf_pPrimeCore_le [Finite X] {J K : Subgroup X} (hKJ : K ≤ J) :
    K ⊓ (pPrimeCore 2 ↥J).map J.subtype ≤ (pPrimeCore 2 ↥K).map K.subtype := by
  refine le_pPrimeCore_map inf_le_left ?_ ?_
  · intro g hg
    exact inf_mem_normalizer' (le_normalizer hg) (le_normalizer_pPrimeCore (le_normalizer
      (hKJ hg)))
  · have h5 : Nat.card ↥(K ⊓ (pPrimeCore 2 ↥J).map J.subtype) ∣
        Nat.card ↥((pPrimeCore 2 ↥J).map J.subtype) := card_dvd_of_le inf_le_right
    rw [card_map_of_injective J.subtype_injective] at h5
    exact Nat.Coprime.coprime_dvd_right h5 pPrimeCore_coprime_card

theorem mem_coreActionKernel_of_le [Finite X] {J K : Subgroup X} (hKJ : K ≤ J) {u : X}
    (hu : u ∈ UnbalancedLayer.coreActionKernel J) (huK : u ∈ normalizer (K : Set X)) :
    u ∈ UnbalancedLayer.coreActionKernel K := by
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨huK, fun x hx => ?_⟩
  have h1 := (UnbalancedLayer.mem_coreActionKernel.mp hu).2 x (hKJ hx)
  have h3 : u⁻¹ * x * u ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem huK) x).mp hx
    simpa using this
  have h2 : x⁻¹ * u⁻¹ * x * u ∈ K := by
    have h4 := mul_mem (inv_mem hx) h3
    simpa [mul_assoc] using h4
  exact inf_pPrimeCore_le hKJ ⟨h2, h1⟩

theorem mem_coreActionKernel_of_commute [Finite X] {J K : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) (hKJ : K ≤ J) {g : X} (hg : g ∈ J)
    (hgK : g ∈ normalizer (K : Set X))
    (hc : ∀ (x : X) (hx : x ∈ J), x ∈ K → coreImage θ hg * coreImage θ hx =
      coreImage θ hx * coreImage θ hg) :
    g ∈ UnbalancedLayer.coreActionKernel K := by
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨hgK, fun x hx => ?_⟩
  have hxJ := hKJ hx
  have h3 : g⁻¹ * x * g ∈ K := by
    have := (mem_normalizer_iff.mp (inv_mem hgK) x).mp hx
    simpa using this
  have h2 : x⁻¹ * g⁻¹ * x * g ∈ K := by
    have h4 := mul_mem (inv_mem hx) h3
    simpa [mul_assoc] using h4
  have hJ : x⁻¹ * g⁻¹ * x * g ∈ (pPrimeCore 2 ↥J).map J.subtype := by
    set z : ↥J := (⟨x, hxJ⟩ : ↥J)⁻¹ * (⟨g, hg⟩ : ↥J)⁻¹ * ⟨x, hxJ⟩ * ⟨g, hg⟩ with hzdef
    set p := θ ((⟨x, hxJ⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) with hpdef
    set q := θ ((⟨g, hg⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) with hqdef
    have hpq : q * p = p * q := Subtype.ext (hc x hxJ hx)
    have hz : θ (z : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [hzdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← hpdef, ← hqdef]
      calc p⁻¹ * q⁻¹ * p * q = p⁻¹ * q⁻¹ * (p * q) := by group
        _ = p⁻¹ * q⁻¹ * (q * p) := by rw [hpq]
        _ = 1 := by group
    rw [map_eq_one_iff _ θ.injective, QuotientGroup.eq_one_iff] at hz
    exact ⟨z, hz, rfl⟩
  exact inf_pPrimeCore_le hKJ ⟨h2, hJ⟩

theorem exists_pump_data (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {n : ℕ}
    (hmax : ∀ (t' : X) (K' : Subgroup X) (n' : ℕ), SolAltLit.IsAltTwoComponent t' K' n' →
      Odd n' → n' ≤ n)
    {c t : X} (hc : orderOf c = 2) (ht : orderOf t = 2) (htc : t ∈ centralizer ({c} : Set X))
    {Jc : Subgroup X} (hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    {k : ℕ} (hk : 9 ≤ k) (hkodd : Odd k)
    (eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin k)) :
    ∃ (M : Subgroup X) (r : ℕ), M ≤ centralizer ({c} : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) ∧
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧ Odd r ∧ k ≤ r ∧ r ≤ n ∧
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)) ∧
      (r = k ∨ (M.map (MulAut.conj t).toMonoidHom = M ∧
        IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hCne : centralizer ({c} : Set X) ≠ ⊤ := centralizer_ne_top_of_ne_one hnab hc1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({c} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top hKP hCne
  have hTY : Jc ≤ centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X) := by
    rw [inf_comm]
    exact hJcC
  have hTpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJcpc
  obtain ⟨M, hMY, hMpc, hJcM, hJcMpc, htype⟩ :=
    pump_type_in hPump hK htc ht hTY hTpc hkodd (by omega) eJc
  have hexact : ∀ r : ℕ, Odd r → 9 ≤ r →
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin r)) →
      Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)) ∧ r ≤ n := by
    rintro r hr hr9 ⟨eM⟩
    have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
    have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = centralizer ({c} : Set X) :=
      centralizer_zpowers_eq' c
    have hMC' : M ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by rw [hCc']; exact hMY
    have hMpc' : IsPComponent 2 (M.subgroupOf (centralizer ((zpowers c : Subgroup X) :
        Set X))) := by rw [hCc']; exact hMpc
    have hZ := hN1 X hnab hKP hunb hnU (zpowers c) r M hT (isPGroup_zpowers_of_mul_self hc2) hr
      hr9 hMC' hMpc' ⟨eM⟩
    have eM' : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).symm.trans eM
    exact ⟨⟨eM'⟩, hmax c M r ⟨hc, hMY, hMpc, ⟨eM'⟩⟩ hr⟩
  rcases htype with ⟨hfix, ⟨m', hm', hkm', heM⟩ | ⟨h7, -⟩⟩ | ⟨-, heM⟩
  · obtain ⟨hθ, hmn⟩ := hexact m' hm' (by omega) heM
    rw [hfix, sup_idem] at hJcMpc
    refine ⟨M, m', hMY, hMpc, hJcM, hm', hkm', hmn, hθ, Or.inr ⟨hfix, hJcMpc⟩⟩
  · omega
  · obtain ⟨hθ, hkn⟩ := hexact k hkodd hk heM
    exact ⟨M, k, hMY, hMpc, hJcM, hkodd, le_rfl, hkn, hθ, Or.inl rfl⟩

theorem map_conj_map_conj_of_mul_self {t : X} (htt : t * t = 1) (M : Subgroup X) :
    (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = M := by
  rw [Subgroup.map_map]
  have h1 : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id X := by
    ext z
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [htinv]
    calc t * (t * z * t) * t = (t * t) * z * (t * t) := by group
      _ = z := by rw [htt]; group
  rw [h1, Subgroup.map_id]

theorem pump_data_conj [Finite X] {c t : X} (htt : t * t = 1)
    (htc : t ∈ centralizer ({c} : Set X)) {M Jc : Subgroup X}
    (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))))
    (hJcM : Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) {r k : ℕ}
    (hθ : Nonempty (↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r)))
    (hcase : r = k ∨ (M.map (MulAut.conj t).toMonoidHom = M ∧
      IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))))) :
    M.map (MulAut.conj t).toMonoidHom ≤ centralizer ({c} : Set X) ∧
      IsPComponent 2 ((M.map (MulAut.conj t).toMonoidHom).subgroupOf
        (centralizer ({c} : Set X))) ∧
      Jc ≤ M.map (MulAut.conj t).toMonoidHom ⊔
        (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom ∧
      Nonempty (↥(M.map (MulAut.conj t).toMonoidHom) ⧸
        pPrimeCore 2 ↥(M.map (MulAut.conj t).toMonoidHom) ≃* alternatingGroup (Fin r)) ∧
      (r = k ∨ ((M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom =
          M.map (MulAut.conj t).toMonoidHom ∧
        IsPComponent 2 (Jc.subgroupOf (M.map (MulAut.conj t).toMonoidHom ⊓
          centralizer ({t} : Set X))))) := by
  obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htc
  have hMtt := map_conj_map_conj_of_mul_self htt M
  obtain ⟨θM⟩ := hθ
  let φ : ↥M ≃* ↥(M.map (MulAut.conj t).toMonoidHom) :=
    M.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  refine ⟨hMtC, hMtpc, by rw [hMtt, sup_comm]; exact hJcM,
    ⟨(Sol78.coreQuotCongr φ).symm.trans θM⟩, ?_⟩
  rcases hcase with h | ⟨hfix, hpc⟩
  · exact Or.inl h
  · refine Or.inr ⟨by rw [hfix, hfix], ?_⟩
    rw [hfix]
    exact hpc

end CFSG.ComponentClassification.SolMax
