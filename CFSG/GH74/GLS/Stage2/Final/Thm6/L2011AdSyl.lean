module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdMain

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Final.Thm6
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_ge' {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 ↥P) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ P ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hS hx, rfl⟩

theorem exists_sylow_central_of_zP {J : Subgroup G} {z : G} (hzJ : z ∈ J) (hz2 : orderOf z = 2)
    (hZ : ∀ P : Subgroup G, IsSylowOf 2 P (centralizer ({z} : Set G) ⊓ J) → ∀ w ∈ P,
      (∀ p ∈ P, w * p = p * w) → orderOf w = 2 → w = z) :
    ∃ T : Subgroup G, IsSylowOf 2 T J ∧ z ∈ T ∧ ∀ s ∈ T, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set CJ : Subgroup G := centralizer ({z} : Set G) ⊓ J with hCJ
  have hzCJ : z ∈ CJ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hzJ⟩
  have hzp : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hz2)
  have hzle : zpowers z ≤ CJ := (Subgroup.zpowers_le).mpr hzCJ
  obtain ⟨P, hP, hzP⟩ := exists_isSylowOf_ge' hzle hzp
  have hPCJ : P ≤ CJ := hP.le
  have hPJ : P ≤ J := hPCJ.trans inf_le_right
  obtain ⟨T, hT, hPT⟩ := exists_isSylowOf_ge' hPJ hP.isPGroup
  have hzT : z ∈ T := hPT (hzP (Subgroup.mem_zpowers z))
  have hTp : IsPGroup 2 ↥T := hT.isPGroup
  have hnt : Nontrivial ↥T := ⟨⟨⟨z, hzT⟩, 1, fun h => by
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at hz2
    omega⟩⟩
  have hcn : Nontrivial ↥(center ↥T) := hTp.center_nontrivial
  obtain ⟨u₀, hu₀⟩ := exists_ne (1 : ↥(center ↥T))
  have hcp : IsPGroup 2 ↥(center ↥T) := hTp.of_injective (center ↥T).subtype (center ↥T).subtype_injective
  obtain ⟨u, hu2⟩ : ∃ u : ↥(center ↥T), orderOf u = 2 := by
    obtain ⟨n, hn⟩ := hcp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1 : Nat.card ↥(center ↥T) = 1 := by simpa using hn
      have := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hu₀ (Subsingleton.elim u₀ 1)
    have h2 : 2 ∣ Nat.card ↥(center ↥T) := by
      rw [hn]; exact dvd_pow_self 2 hn0
    exact exists_prime_orderOf_dvd_card' 2 h2
  set ũ : G := ((u : ↥T) : G) with hũ
  have hũT : ũ ∈ T := (u : ↥T).2
  have hũ2 : orderOf ũ = 2 := by
    rw [hũ, Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hu2
  have hcentT : ∀ s ∈ T, s * ũ = ũ * s := by
    intro s hs
    have := Subgroup.mem_center_iff.mp u.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hũCJ : ũ ∈ CJ := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hcentT z hzT).symm, hT.le hũT⟩
  have hPle : P ⊔ zpowers ũ ≤ T := sup_le hPT ((Subgroup.zpowers_le).mpr hũT)
  have hPle' : P ⊔ zpowers ũ ≤ CJ := sup_le hPCJ ((Subgroup.zpowers_le).mpr hũCJ)
  have hp2 : IsPGroup 2 ↥(P ⊔ zpowers ũ) := by
    exact hTp.of_injective (Subgroup.inclusion hPle) (Subgroup.inclusion_injective hPle)
  have hEq := hP.eq_of_le le_sup_left hPle' hp2
  have hũP : ũ ∈ P := by
    rw [← hEq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ũ)
  have hũz : ũ = z := hZ P hP ũ hũP (fun p hp => (hcentT p (hPT hp)).symm) hũ2
  refine ⟨T, hT, hzT, fun s hs => ?_⟩
  rw [← hũz]
  exact hcentT s hs

theorem claimG_to_zP {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}
    (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) (hpair : PairG z K₁ K₂ q) {J : Subgroup G}
    (hEJ : K₁ ⊔ K₂ ≤ J)
    (hG : ∀ w ∈ S, orderOf w = 2 → (∀ r ∈ S ⊓ (K₁ ⊔ K₂), w * r = r * w) → w = z) :
    ∀ P : Subgroup G, IsSylowOf 2 P (centralizer ({z} : Set G) ⊓ J) → ∀ w ∈ P,
      (∀ p ∈ P, w * p = p * w) → orderOf w = 2 → w = z := by
  intro P hP w hwP hwc hw2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({z} : Set G) with hCdef
  set E : Subgroup G := K₁ ⊔ K₂ with hE
  have hEC : E ≤ C := sup_le hpair.le₁ hpair.le₂
  have hCnorm : C ≤ normalizer (E : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hpair.norm c hc a ha
    · intro ha
      have h1 := hpair.norm c⁻¹ (C.inv_mem hc) _ ha
      have e : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
      rwa [e] at h1
  have hPC : P ≤ C := hP.le.trans inf_le_left
  obtain ⟨P', hP', hPP'⟩ := exists_isSylowOf_ge' hPC hP.isPGroup
  obtain ⟨c, hcC, hc⟩ := hS.exists_mem_conj hP'
  have hPE : IsSylowOf 2 (P ⊓ E) E :=
    hP.inf_of_le_normalizer (le_inf hEC hEJ) (inf_le_left.trans hCnorm)
  have hEq : P' ⊓ E = P ⊓ E :=
    hPE.eq_of_le (inf_le_inf_right E hPP') inf_le_right (hP'.isPGroup.to_inf_left)
  have hw'S : c⁻¹ * w * c ∈ S := (hc w).1 (hPP' hwP)
  have hw'2 : orderOf (c⁻¹ * w * c) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) w
    rw [MulAut.conj_apply, show c⁻¹ * w * c⁻¹⁻¹ = c⁻¹ * w * c by simp] at this
    rw [this]
    exact hw2
  have hw'c : ∀ r ∈ S ⊓ E, (c⁻¹ * w * c) * r = r * (c⁻¹ * w * c) := by
    intro r hr
    have hr' : c * r * c⁻¹ ∈ P' ⊓ E :=
      ⟨(hc _).2 (by rw [show c⁻¹ * (c * r * c⁻¹) * c = r by group]; exact hr.1),
        hpair.norm c hcC r hr.2⟩
    have hr'' : c * r * c⁻¹ ∈ P ⊓ E := hEq ▸ hr'
    have h1 := hwc _ hr''.1
    calc c⁻¹ * w * c * r = c⁻¹ * (w * (c * r * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * r * c⁻¹) * w) * c := by rw [h1]
      _ = r * (c⁻¹ * w * c) := by group
  have hwz := hG _ hw'S hw'2 hw'c
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  calc w = c * (c⁻¹ * w * c) * c⁻¹ := by group
    _ = c * z * c⁻¹ := by rw [hwz]
    _ = z := by rw [hcz]; group

theorem exists_sylow_barIn {J T : Subgroup G} (hT : IsSylowOf 2 T J) :
    ∃ T' : Sylow 2 (HBar J), (T' : Subgroup (HBar J)) = barIn J T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylowOf_iff).1 hT
  have h1 : IsPGroup 2 ↥(T.subgroupOf J) := h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  have hP : IsPGroup 2 ↥(barIn J T) := h1.map (mkH J)
  have hdvd1 : (barIn J T).index ∣ (T.subgroupOf J).index :=
    Subgroup.index_map_dvd (T.subgroupOf J) (QuotientGroup.mk'_surjective _)
  exact ⟨hP.toSylow (fun hd => h.2.2 (hd.trans hdvd1)), IsPGroup.toSylow_coe _ _⟩

@[expose] def ClaimG : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)) (K₁ K₂ : Subgroup G),
      Stage1Pair G z S q L₁ L₂ → (RC S z).relIndex S ≤ 4 → CompData z K₁ K₂ L₁ L₂ →
        ∀ w ∈ S, orderOf w = 2 → (∀ r ∈ S ⊓ (K₁ ⊔ K₂), w * r = r * w) → w = z

theorem relIndex_RC_le_four {z : G} {k : Kind} {S : Subgroup G} (hC : Ctx2011 G z k S) : (RC S z).relIndex S ≤ 4 := by
  rcases hC.2 with ⟨ε, q, -, L₁, L₂, h⟩ | ⟨q, -, L₁, L₂, h⟩
  · exact h.index_le
  · exact h.index.le.trans (by norm_num)

theorem central20_of_claimG (hG : ClaimG) : Central20 := by
  intro G _ _ z k S hC g hg h
  obtain ⟨q, L₁, L₂, K₁, K₂, hP, hK⟩ := exists_data hC
  have hz2 := orderOf_z_of_ctx hC
  have hpair : PairG z K₁ K₂ q := PairG.of_data hz2 hP hK
  have hEJ : K₁ ⊔ K₂ ≤ J0 z g := hK.layer ▸ h.layer_le
  obtain ⟨T, hT, hzT, hTc⟩ := exists_sylow_central_of_zP h.z_mem hz2
    (claimG_to_zP hC.1.ctx.ctx17.ctx.sylow hpair hEJ
      (hG G z k S hC.1.ctx.ctx17.ctx q L₁ L₂ K₁ K₂ hP (relIndex_RC_le_four hC) hK))
  obtain ⟨T', hT'⟩ := exists_sylow_barIn hT
  refine ⟨orderOf_mkH_of_orderOf h.z_mem hz2, T', ?_, ?_⟩
  · rw [hT']
    exact ⟨⟨z, h.z_mem⟩, Subgroup.mem_subgroupOf.mpr hzT, rfl⟩
  · intro s hs
    rw [hT'] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    rw [← map_mul, ← map_mul]
    exact congrArg (mkH (J0 z g)) (Subtype.ext (hTc _ (Subgroup.mem_subgroupOf.mp hs')))

theorem adapter20_9_of_claimG (hG : ClaimG) : Adapter20_9 :=
  adapter20_9_of_central (central20_of_claimG hG)

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
