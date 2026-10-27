module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQKFSetting
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Field

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sz32Local Subgroup

namespace InnerQ.FieldInvert

variable {K : Type} [Group K] [Finite K] {T : Subgroup K}

private theorem sq_mod_twentyFive : ∀ r < 25, r * r % 25 = 1 → r = 1 ∨ r = 24 := by decide

private theorem exists_inverter (hT : Sz32Data K T) :
    ∃ n : K, n ^ 2 = 1 ∧ ∀ a ∈ T, n * a * n⁻¹ = a⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (T : Set K)) 2
    (by rw [hT.card_normalizer]; norm_num)
  have hnK : orderOf (n : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hn
  have hn2 : (n : K) ^ 2 = 1 := hnK ▸ pow_orderOf_eq_one _
  have := hT.isCyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := T)
  have hgo : orderOf (g : K) = 25 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hT.card_eq]
  have hg1 : (g : K) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hgo
    omega
  have hngT : (n : K) * g * (n : K)⁻¹ ∈ T := (mem_normalizer_iff.mp n.2 g).mp g.2
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (y := (⟨_, hngT⟩ : T))).mpr (hg _)
  have hk' : (n : K) * g * (n : K)⁻¹ = (g : K) ^ k := by
    have h := congrArg Subtype.val hk
    simpa using h.symm
  have hkk : (g : K) ^ (k * k) = (g : K) ^ 1 := by
    have hnn : (n : K) * n = 1 := by rw [← pow_two, hn2]
    have h1 : (n : K) * ((n : K) * g * (n : K)⁻¹) * (n : K)⁻¹ = g := by
      calc (n : K) * ((n : K) * g * (n : K)⁻¹) * (n : K)⁻¹
          = ((n : K) * n) * g * ((n : K) * n)⁻¹ := by group
        _ = g := by rw [hnn, one_mul, inv_one, mul_one]
    rw [hk', ← conj_pow, hk', ← pow_mul] at h1
    rw [h1, pow_one]
  rw [pow_eq_pow_iff_modEq, hgo] at hkk
  have hr := sq_mod_twentyFive (k % 25) (Nat.mod_lt _ (by norm_num))
    (by rw [← Nat.mul_mod]; exact hkk)
  have hgk : (g : K) ^ k = (g : K) ^ (k % 25) := by
    rw [← hgo, pow_mod_orderOf]
  rcases hr with h | h
  · exfalso
    rw [h, pow_one] at hgk
    have hnT : (n : K) ∈ T := hT.centralizer_le g g.2 hg1 n (by
      calc (n : K) * g = (n : K) * g * (n : K)⁻¹ * n := by group
        _ = g * n := by rw [hk', hgk])
    have := Subgroup.orderOf_dvd_natCard T hnT
    rw [hnK, hT.card_eq] at this
    omega
  · refine ⟨n, hn2, fun a ha => ?_⟩
    have hinv : (n : K) * g * (n : K)⁻¹ = (g : K)⁻¹ := by
      rw [hk', hgk, h, eq_inv_iff_mul_eq_one, ← pow_succ, show 24 + 1 = orderOf (g : K) by
        rw [hgo]]
      exact pow_orderOf_eq_one _
    obtain ⟨j, hj⟩ := hg ⟨a, ha⟩
    have haj : a = (g : K) ^ j := by
      have h := congrArg Subtype.val hj
      simpa using h.symm
    rw [haj, ← conj_zpow, hinv, inv_zpow]

private theorem exists_fixed_inverter (hT : Sz32Data K T)
    (haut : ∀ f : MulAut K, (∀ x ∈ T, f x = x) → ∃ c ∈ T, f = MulAut.conj c)
    {φ : MulAut K} (hφ5 : φ ^ 5 = 1) (hout : ¬ ∃ y : K, φ = MulAut.conj y)
    {t : K} (htT : t ∈ T) (ht : orderOf t = 5) (hφt : φ t = t) :
    ∃ s : K, s ^ 2 = 1 ∧ φ s = s ∧ s * t * s⁻¹ = t⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm := hT.commute
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have hφT : ∀ a ∈ T, φ a ∈ T := fun a ha => hT.centralizer_le t htT ht1 (φ a) (by
    have h := congrArg φ (hcomm a ha t htT)
    rwa [map_mul, map_mul, hφt] at h)
  obtain ⟨n, hn2, hninv⟩ := exists_inverter hT
  have hnn : n⁻¹ = n := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hn2]
  set b := n⁻¹ * φ n with hbdef
  have hbT : b ∈ T := hT.centralizer_le t htT ht1 b (by
    have h1 : φ n * t * (φ n)⁻¹ = t⁻¹ := by
      rw [← hφt, ← map_inv, ← map_mul, ← map_mul, hφt, hninv t htT, map_inv, hφt]
    have h2 : n⁻¹ * t⁻¹ * n = t := by
      rw [← hninv t htT]
      group
    calc b * t = (n⁻¹ * (φ n * t * (φ n)⁻¹) * n) * b := by rw [hbdef]; group
      _ = t * b := by rw [h1, h2])
  have hφn : φ n = n * b := by rw [hbdef]; group
  letI : CommGroup T :=
    { (inferInstance : Group T) with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  have hTcyc : IsCyclic T := hT.isCyclic
  set fT : T →* T :=
    { toFun := fun a => ⟨φ (a : K), hφT a a.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a a' => Subtype.ext (map_mul φ (a : K) (a' : K)) } with hfT
  have hfT_val : ∀ a : T, ((fT a : T) : K) = φ (a : K) := fun a => rfl
  set θ : T →* T := MonoidHom.id T / fT with hθ
  have hθ_apply : ∀ a : T, θ a = a / fT a := fun a => rfl
  have hmem_ker : ∀ a : T, a ∈ θ.ker ↔ fT a = a := fun a => by
    rw [MonoidHom.mem_ker, hθ_apply, div_eq_one, eq_comm]
  have htker : (⟨t, htT⟩ : T) ∈ θ.ker := (hmem_ker _).mpr (Subtype.ext hφt)
  have hker_ne : θ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨c, -, hc⟩ := haut φ fun x hx =>
      congrArg Subtype.val ((hmem_ker ⟨x, hx⟩).mp (htop ▸ mem_top _))
    exact hout ⟨c, hc⟩
  have hTcard : Nat.card T = 25 := hT.card_eq
  have hker5 : Nat.card θ.ker = 5 := by
    have hdvd : Nat.card θ.ker ∣ 5 ^ 2 := by
      rw [show (5 : ℕ) ^ 2 = Nat.card T by rw [hTcard]; norm_num]
      exact card_subgroup_dvd_card _
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdvd
    interval_cases i
    · exfalso
      rw [pow_zero, Subgroup.card_eq_one] at hik
      have := htker
      rw [hik, mem_bot] at this
      exact ht1 (congrArg Subtype.val this)
    · simpa using hik
    · exact absurd (Subgroup.eq_top_of_card_eq _ (by rw [hik, hTcard]; norm_num)) hker_ne
  have hrange5 : Nat.card θ.range = 5 := by
    have h := Subgroup.card_ker_mul_card_range θ
    rw [hker5, hTcard] at h
    omega
  have hrk : θ.range = θ.ker := (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [hrange5, hker5])
  set bT : T := ⟨b, hbT⟩
  set cT : T := (θ bT)⁻¹
  have hcker : cT ∈ θ.ker := hrk ▸ inv_mem (MonoidHom.mem_range.mpr ⟨bT, rfl⟩)
  have hfc : fT cT = cT := (hmem_ker cT).mp hcker
  have hfb : fT bT = bT * cT := by
    rw [show cT = (θ bT)⁻¹ from rfl, hθ_apply, inv_div, mul_div_cancel]
  have hc5 : cT ^ 5 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard θ.ker hcker
    rw [hker5] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  set ψ : T → T := fun a => bT * fT a with hψ
  have hψ_apply : ∀ x, ψ x = bT * fT x := fun x => rfl
  have hφψ : ∀ (k : ℕ) (a : T), (φ ^ k) (n * a) = n * (ψ^[k] a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply', map_mul, hφn, hψ_apply,
        Subgroup.coe_mul, hfT_val, mul_assoc]
  have hstep : ∀ i j : ℕ, ψ (bT ^ i * cT ^ j) = bT ^ (i + 1) * cT ^ (i + j) := by
    intro i j
    rw [hψ_apply]
    simp only [map_mul, map_pow, hfb, hfc, mul_pow, pow_add, pow_succ]
    simp only [mul_comm, mul_left_comm, mul_assoc]
  have h5 : ψ^[5] (bT ^ 0 * cT ^ 0) = bT ^ 5 * cT ^ 10 := by
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, hstep]
  have hb5 : bT ^ 5 = 1 := by
    have h := hφψ 5 (bT ^ 0 * cT ^ 0)
    rw [h5, hφ5, MulAut.one_apply] at h
    have h' : bT ^ 5 * cT ^ 10 = 1 := by
      have h'' : bT ^ 5 * cT ^ 10 = bT ^ 0 * cT ^ 0 := Subtype.ext (mul_left_cancel h).symm
      simpa using h''
    rwa [show cT ^ 10 = (cT ^ 5) ^ 2 by rw [← pow_mul], hc5, one_pow, mul_one] at h'
  have hbker : bT ∈ θ.ker := by
    by_cases hb1 : bT = 1
    · rw [hb1]
      exact one_mem _
    · have hob : orderOf bT = 5 := orderOf_eq_prime hb5 hb1
      have hz : zpowers bT = θ.ker :=
        (IsCyclic.subgroup_eq_iff_card_eq).mpr (by rw [Nat.card_zpowers, hob, hker5])
      exact hz ▸ mem_zpowers bT
  obtain ⟨a, ha⟩ := (hrk ▸ hbker : bT ∈ θ.range)
  have hba : bT * fT a = a := by
    rw [← ha, hθ_apply]
    simp only [MonoidHom.id_apply, div_mul_cancel]
  refine ⟨n * a, ?_, ?_, ?_⟩
  · rw [pow_two, show n * a * (n * a) = (n * a * n⁻¹) * a by rw [hnn]; group, hninv a a.2,
      inv_mul_cancel]
  · have h := hφψ 1 a
    rw [pow_one] at h
    rw [h, Function.iterate_one, hψ_apply]
    exact congrArg (n * ·) (congrArg Subtype.val hba)
  · rw [show n * a * t * (n * a)⁻¹ = n * (a * t * (a : K)⁻¹) * n⁻¹ by group,
      show (a : K) * t * (a : K)⁻¹ = t by rw [hcomm a a.2 t htT]; group, hninv t htT]

end InnerQ.FieldInvert

open InnerQ.FieldInvert in
theorem kFactCaseTwoFieldInvert :
    KFactCaseTwoFieldInvert := by
  intro K _ _ hK φ hφ5 hout t ht hφt
  obtain ⟨⟨x, hv⟩, hd, he⟩ := hK
  rcases hd with ⟨h53, -⟩ | ⟨-, hs⟩
  · omega
  obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := hs
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, he⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hOut : (CFSG.ComponentClassification.OuterAutomorphisms.inner K).index ∣ 5 :=
    CFSG.RankThree.PartOne.K159F.card_outer_dvd_five hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    CFSG.AGLEmbedding.KFactProofs.Sz32.F32.ringEquiv F hF'
  let ε : K ≃* CFSG.Blueprint.suzukiGroup 2 CFSG.AGLEmbedding.KFactProofs.Sz32.F32 :=
    eF.trans (modelEquiv σ)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨T, hT⟩ := (IsPGroup.of_card (n := 1) (p := 5) (G := zpowers t)
    (by rw [Nat.card_zpowers, ht, pow_one])).exists_le_sylow
  have hdata : Sz32Data K (T : Subgroup K) :=
    ⟨hSz.card, by
      rw [Sylow.card_eq_multiplicity, hSz.card,
        CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
      norm_num, hSz.cyclic T, centralizer_le_of_equiv ε T⟩
  exact exists_fixed_inverter hdata (fun f hf => hdata.aut hSz hsimple hOut hf) hφ5 hout
    (hT (mem_zpowers t)) ht hφt

end CFSG.LocalAnalysis.RankThreeTheoremC
