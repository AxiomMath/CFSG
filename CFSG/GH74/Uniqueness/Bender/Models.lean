module

public import CFSG.GH74.Uniqueness.Bender.Core
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K]

theorem rootCenter_eq_map_center (P : Subgroup K) : rootCenter P = (center P).map P.subtype := by
  ext x
  rw [mem_rootCenter_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hxP, hc⟩
    refine ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, fun p hp => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨p, hp⟩
    exact congrArg Subtype.val this

theorem rootCenter_data {q k : ℕ} (hF : CFSG.Open.fusionBenderBorel K q k) (Q : Sylow 2 K) :
    Nat.card (rootCenter (Q : Subgroup K)) = q ∧
      ∀ z ∈ rootCenter (Q : Subgroup K), z * z = 1 := by
  obtain ⟨-, -, hsq, hcard, -⟩ := hF Q
  refine ⟨?_, ?_⟩
  · rw [rootCenter_eq_map_center, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hcard
  · intro z hz
    rw [rootCenter_eq_map_center] at hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have := hsq y hy
    change (y : K) * y = 1
    rw [← Subgroup.coe_mul, ← sq, this]
    rfl

open CFSG.ShultStronglyClosedTI.LinearModel CFSG.ShultStronglyClosedTI.SuzukiModel
  CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups

section Linear

theorem exists_benderCore_psl2 [Finite K] {n : ℕ} (e : K ≃* PSL2BinaryMatrixGroup n)
    (hn : 2 ≤ n) (Q : Sylow 2 K) : ∃ t, BenderCore (2 ^ n) 1 1 (Q : Subgroup K) t := by
  obtain ⟨T, β, hP, -⟩ := linearPointAction_cosets_of_mulEquiv_psl2 e hn Q
  have hq : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hN := hP.normalizer_eq_stabilizer hq
  have hF : CFSG.Open.fusionBenderBorel K (2 ^ n) 1 := by
    have : Finite (PSL2BinaryMatrixGroup n) := Finite.of_equiv K e.toEquiv
    exact (CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv e.symm
  obtain ⟨hcc, hcsq⟩ := rootCenter_data hF Q
  have h2 := hP.isMultiplyPretransitive
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨w, hw1, hw2⟩ := h2 hP.ne hP.ne.symm
  obtain ⟨hword, hwinv⟩ := hP.swap w hw1 hw2
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hword, sq] at this
    exact this
  have hwi : w⁻¹ = w := inv_eq_of_mul_self hww
  have hconj : conjugate (MulAction.stabilizer K
      (QuotientGroup.mk 1 : K ⧸ normalizer ((Q : Subgroup K) : Set K))) w =
      MulAction.stabilizer K β := by
    unfold conjugate
    rw [hwi, ← hw1, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hcart : cartan (Q : Subgroup K) w = T := by
    unfold cartan borel
    rw [hN, hconj, hP.stabilizer_inf_stabilizer]
  have hbor : borel (Q : Subgroup K) = MulAction.stabilizer K
      (QuotientGroup.mk 1 : K ⧸ normalizer ((Q : Subgroup K) : Set K)) := hN
  refine ⟨w, ?_⟩
  exact
    { sq_eq_one := hww
      not_mem := by
        intro hmem
        rw [hbor] at hmem
        exact hP.ne ((MulAction.mem_stabilizer_iff.mp hmem).symm.trans hw1)
      strong := by rw [hbor]; exact hP.stronglyEmbedded
      index_eq := by
        have h1 : (borel (Q : Subgroup K)).index =
            Nat.card (K ⧸ normalizer ((Q : Subgroup K) : Set K)) := rfl
        rw [h1, hP.card_eq, pow_one]
      card_eq := by rw [pow_one]; exact hP.card_U
      sup_eq := by rw [hcart, hP.sup_eq_stabilizer, hbor]
      inf_eq := by rw [hcart]; exact hP.inf_eq_bot
      isCyclic := by rw [hcart]; exact hP.isCyclic
      card_cartan := by rw [hcart, hP.card_T, mul_one]
      ncard_inv := by
        have hset : {x : K | x ∈ cartan (Q : Subgroup K) w ∧ w * x * w = x⁻¹} = (T : Set K) := by
          ext x
          rw [hcart]
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            have := hwinv x hx
            rwa [hwi] at this
        rw [hset, ← Nat.card_coe_set_eq]
        exact hP.card_T
      card_center := hcc
      center_sq := hcsq
      center_of_involution := by
        intro g hg hord
        rw [hbor] at hg
        have := (hP.orderOf_eq_two_iff g hg).mp hord
        refine mem_rootCenter_iff.mpr ⟨this.1, fun p hp => ?_⟩
        exact congrArg Subtype.val
          (hP.isElemAbelian.1.is_comm.comm (⟨p, hp⟩ : (Q : Subgroup K)) ⟨g, this.1⟩) }

end Linear

section Suzuki

theorem szModel_eq_open_sz (a : ℕ) : SzModel a = CFSG.Open.Sz a :=
  CFSG.Models.benderSzModel_eq_sz a

theorem exists_benderCore_suzuki
    [Finite K] {a : ℕ} (ha : 1 ≤ a) (e : K ≃* SzModel a)
    (Q : Sylow 2 K) : ∃ t, BenderCore (2 ^ (2 * a + 1)) 2 1 (Q : Subgroup K) t := by
  let e' : K ≃* CFSG.Open.Sz a := e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a))
  obtain ⟨T, β, hP, -⟩ := suzukiPointAction_cosets_of_mulEquiv_sz a e' Q
  have hq : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
  have hN := hP.normalizer_eq_stabilizer hq
  have hF : CFSG.Open.fusionBenderBorel K (2 ^ (2 * a + 1)) 2 := by
    have : Finite (CFSG.Open.Sz a) := Finite.of_equiv K e'.toEquiv
    exact (CFSG.Open.bender_suzuki_borel_full a ha).map_mulEquiv e'.symm
  obtain ⟨hcc, hcsq⟩ := rootCenter_data hF Q
  have h2 := hP.isMultiplyPretransitive
  rw [MulAction.is_two_pretransitive_iff] at h2
  obtain ⟨w, hw1, hw2⟩ := h2 hP.ne hP.ne.symm
  obtain ⟨hword, hwinv⟩ := hP.swap w hw1 hw2
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hword, sq] at this
    exact this
  have hwi : w⁻¹ = w := inv_eq_of_mul_self hww
  have hconj : conjugate (MulAction.stabilizer K
      (QuotientGroup.mk 1 : K ⧸ normalizer ((Q : Subgroup K) : Set K))) w =
      MulAction.stabilizer K β := by
    unfold conjugate
    rw [hwi, ← hw1, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hcart : cartan (Q : Subgroup K) w = T := by
    unfold cartan borel
    rw [hN, hconj, hP.stabilizer_inf_stabilizer]
  have hbor : borel (Q : Subgroup K) = MulAction.stabilizer K
      (QuotientGroup.mk 1 : K ⧸ normalizer ((Q : Subgroup K) : Set K)) := hN
  refine ⟨w, ?_⟩
  exact
    { sq_eq_one := hww
      not_mem := by
        intro hmem
        rw [hbor] at hmem
        exact hP.ne ((MulAction.mem_stabilizer_iff.mp hmem).symm.trans hw1)
      strong := by rw [hbor]; exact hP.stronglyEmbedded
      index_eq := by
        have h1 : (borel (Q : Subgroup K)).index =
            Nat.card (K ⧸ normalizer ((Q : Subgroup K) : Set K)) := rfl
        rw [h1, hP.card_eq]
      card_eq := hP.card_U
      sup_eq := by rw [hcart, hP.sup_eq_stabilizer, hbor]
      inf_eq := by rw [hcart]; exact hP.inf_eq_bot
      isCyclic := by rw [hcart]; exact hP.isCyclic
      card_cartan := by rw [hcart, hP.card_T, mul_one]
      ncard_inv := by
        have hset : {x : K | x ∈ cartan (Q : Subgroup K) w ∧ w * x * w = x⁻¹} = (T : Set K) := by
          ext x
          rw [hcart]
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            have := hwinv x hx
            rwa [hwi] at this
        rw [hset, ← Nat.card_coe_set_eq]
        exact hP.card_T
      card_center := hcc
      center_sq := hcsq
      center_of_involution := by
        intro g hg hord
        rw [hbor] at hg
        obtain ⟨hgU, hgc⟩ := hP.involution_mem_center g hg hord
        exact mem_rootCenter_iff.mpr ⟨hgU, fun p hp => hgc p hp⟩ }

end Suzuki

section Unitary

theorem benderCore_of_pointData {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
    {q i e : ℕ} {α β : Ω} {U T : Subgroup G} {w : G}
    (htrans : MulAction.IsPretransitive G Ω)
    (hcardΩ : Nat.card Ω = q ^ i + 1)
    (hsup : U ⊔ T = MulAction.stabilizer G α)
    (hnorm : MulAction.stabilizer G α ≤ normalizer (U : Set G)) (hinf : U ⊓ T = ⊥)
    (hT : MulAction.stabilizer G α ⊓ MulAction.stabilizer G β = T) (hcyc : IsCyclic T)
    (hTcard : Nat.card T = (q - 1) * e) (hUcard : Nat.card U = q ^ i) (hq : 1 < q ^ i)
    (hreg : ∀ x y : Ω, x ≠ α → y ≠ α → ∃! u : U, (u : G) • x = y)
    (hSE : CFSG.Open.fusionStronglyEmbedded (MulAction.stabilizer G α))
    (hw : w * w = 1) (hw1 : w • α = β)
    (hinv : {x : G | x ∈ T ∧ w * x * w = x⁻¹}.ncard = q - 1)
    (hcen : Nat.card (rootCenter U) = q ∧ ∀ z ∈ rootCenter U, z * z = 1)
    (hinvol : ∀ g ∈ MulAction.stabilizer G α, orderOf g = 2 →
      g ∈ U ∧ ∀ u ∈ U, u * g = g * u) :
    BenderCore q i e U w := by
  have hUle : U ≤ MulAction.stabilizer G α := hsup ▸ le_sup_left
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    omega
  have hN : normalizer (U : Set G) = MulAction.stabilizer G α :=
    CFSG.BenderSuzuki.normalizer_eq_stabilizer_of_regular_compl U α hUle hUne hreg hnorm
  have hwi : w⁻¹ = w := inv_eq_of_mul_self hw
  have hbor : borel U = MulAction.stabilizer G α := hN
  have hconj : conjugate (MulAction.stabilizer G α) w = MulAction.stabilizer G β := by
    unfold conjugate
    rw [hwi, ← hw1, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  have hcart : cartan U w = T := by
    unfold cartan
    rw [hbor, hconj, hT]
  have hne : α ≠ β := by
    intro hab
    subst hab
    have : T = MulAction.stabilizer G α := by rw [← hT, inf_idem]
    have hUT : U ≤ T := this ▸ hUle
    have : U = ⊥ := by rw [← hinf]; exact (inf_eq_left.mpr hUT).symm
    exact hUne this
  exact
    { sq_eq_one := hw
      not_mem := by
        intro hmem
        rw [hbor] at hmem
        exact hne ((MulAction.mem_stabilizer_iff.mp hmem).symm.trans hw1)
      strong := by rw [hbor]; exact hSE
      index_eq := by
        have h1 : (MulAction.stabilizer G α).index = (MulAction.orbit G α).ncard :=
          MulAction.index_stabilizer G α
        have h2 : MulAction.orbit G α = Set.univ := MulAction.orbit_eq_univ G α
        rw [hbor, h1, h2, Set.ncard_univ, hcardΩ]
      card_eq := hUcard
      sup_eq := by rw [hcart, hsup, hbor]
      inf_eq := by rw [hcart]; exact hinf
      isCyclic := by rw [hcart]; exact hcyc
      card_cartan := by rw [hcart]; exact hTcard
      ncard_inv := by rw [hcart]; exact hinv
      card_center := hcen.1
      center_sq := hcen.2
      center_of_involution := by
        intro g hg hord
        rw [hbor] at hg
        obtain ⟨hgU, hgc⟩ := hinvol g hg hord
        exact mem_rootCenter_iff.mpr ⟨hgU, fun p hp => hgc p hp⟩ }

end Unitary

section UnitaryModel

open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
  CFSG.ShultStronglyClosedTI.UnitaryModel

theorem benderCore_of_permData {G Ω : Type*} [Group G] [Finite G] (rho : G →* Equiv.Perm Ω)
    {q i e : ℕ} {α β : Ω} {U T B B₂ : Subgroup G} {w : G}
    (htwo : ∀ b c d e : Ω, b ≠ c → d ≠ e → ∃ g : G, rho g b = d ∧ rho g c = e)
    (hcardΩ : Nat.card Ω = q ^ i + 1)
    (hstabα : (MulAction.stabilizer (Equiv.Perm Ω) α).comap rho = B)
    (hstabβ : (MulAction.stabilizer (Equiv.Perm Ω) β).comap rho = B₂)
    (hnormal : (U.subgroupOf B).Normal) (hUT : U ⊓ T = ⊥) (hUTsup : U ⊔ T = B)
    (hTeq : T = B ⊓ B₂) (hTcyc : IsCyclic T) (hTcard : Nat.card T = (q - 1) * e)
    (hUcard : Nat.card U = q ^ i) (hq : 1 < q ^ i)
    (hreg : ∀ b c : Ω, b ≠ α → c ≠ α → ∃! u : U, rho (u : G) b = c)
    (hSE : CFSG.Open.fusionStronglyEmbedded B) (hw : w * w = 1) (hw1 : rho w α = β)
    (hinv : {x : G | x ∈ T ∧ w * x * w = x⁻¹}.ncard = q - 1)
    (hcen : Nat.card (rootCenter U) = q ∧ ∀ z ∈ rootCenter U, z * z = 1)
    (hinvol : ∀ g ∈ B, orderOf g = 2 → g ∈ U ∧ ∀ u ∈ U, u * g = g * u) :
    BenderCore q i e U w := by
  let _ : MulAction G Ω := MulAction.compHom Ω rho
  have hstab : ∀ a : Ω, MulAction.stabilizer G a =
      (MulAction.stabilizer (Equiv.Perm Ω) a).comap rho := fun a => by
    ext g
    rfl
  have h2 : MulAction.IsMultiplyPretransitive G Ω 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro b c d e hbc hde
    exact htwo b c d e hbc hde
  have htrans : MulAction.IsPretransitive G Ω := MulAction.isPretransitive_of_is_two_pretransitive
  have hBα : MulAction.stabilizer G α = B := by rw [hstab, hstabα]
  have hBβ : MulAction.stabilizer G β = B₂ := by rw [hstab, hstabβ]
  have hUB : U ≤ B := hUTsup ▸ le_sup_left
  exact benderCore_of_pointData (α := α) (β := β) htrans hcardΩ (by rw [hBα]; exact hUTsup)
    (by rw [hBα]; exact (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).mp hnormal) hUT
    (by rw [hBα, hBβ]; exact hTeq.symm) hTcyc hTcard hUcard hq hreg (by rw [hBα]; exact hSE) hw
    hw1 hinv hcen (by rw [hBα]; exact hinvol)

theorem exists_benderCore_psu3_concrete {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card E = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (w : ProjectiveSpecialUnitaryMatrixGroup J),
      BenderCore (2 ^ f) 3 ((2 ^ f + 1) / Nat.gcd 3 (2 ^ f + 1))
        (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) w := by
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective
      (fun x : ProjectiveSpecialUnitaryMatrixGroup J => (x : Matrix.ProjGenLinGroup (Fin 3) E))
      Subtype.coe_injective
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hF := CFSG.Open.bender_projectiveSpecialUnitary_borel J f hf hcard hfixed hJ
  have h := unitary_three_point_structure J f hf hcard hfixed hJ
  obtain ⟨-, -, -, -, -, rho, -, -, hΩ, htwo, hstabα, hstabβ, hnormal, hUT, hUTsup, hTeq, hTcyc,
    hTcard, ⟨S, hS⟩, hUcard, hreg, hSE, -, -, hinvol, ⟨w, hword, hw1, hw2⟩, hswap⟩ := h
  refine ⟨S, w, ?_⟩
  have hww : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hword, sq] at this
    exact this
  have hwi : w⁻¹ = w := inv_eq_of_mul_self hww
  obtain ⟨-, C, hC, -, hCcard⟩ := hswap w hw1 hw2
  rw [hwi] at hC
  have hq : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  rw [hS]
  refine benderCore_of_permData rho htwo hΩ hstabα hstabβ hnormal hUT hUTsup hTeq hTcyc ?_
    hUcard hq hreg hSE hww hw1 ?_ ?_ hinvol
  · rw [hTcard]
    have hfactor : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2 ^ f) 1
    rw [hfactor, Nat.mul_div_assoc _ (Nat.gcd_dvd_right 3 (2 ^ f + 1))]
  · rw [← hC, ← Nat.card_coe_set_eq]
    exact hCcard
  · have := rootCenter_data hF S
    rw [hS] at this
    exact this

end UnitaryModel

section Assembly

inductive BenderType (K : Type*) [Group K] : ℕ → ℕ → ℕ → Prop
  | linear (n : ℕ) (hn : 2 ≤ n) (e : K ≃* PSL2Model n) : BenderType K n 1 1
  | suzuki (a : ℕ) (ha : 1 ≤ a) (e : K ≃* SzModel a) : BenderType K (2 * a + 1) 2 1
  | unitary (n : ℕ) (hn : 2 ≤ n) (e : K ≃* PSU3Model n) :
      BenderType K n 3 ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1))

theorem isBenderGroup_iff_exists_benderType :
    IsBenderGroup K ↔ ∃ n i e, BenderType K n i e := by
  constructor
  · rintro (⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩)
    · exact ⟨n, 1, 1, .linear n hn e⟩
    · exact ⟨2 * a + 1, 2, 1, .suzuki a ha e⟩
    · exact ⟨n, 3, _, .unitary n hn e⟩
  · rintro ⟨n, i, e, h⟩
    cases h with
    | linear n hn e => exact .isPSL2 n hn e
    | suzuki a ha e => exact .isSuzuki a ha e
    | unitary n hn e => exact .isPSU3 n hn e

theorem BenderType.cases' {K : Type*} [Group K] {n i e : ℕ} (h : BenderType K n i e) :
    (i = 1 ∧ e = 1 ∧ 2 ≤ n) ∨ (i = 2 ∧ e = 1 ∧ ∃ a, 1 ≤ a ∧ n = 2 * a + 1) ∨
      (i = 3 ∧ e = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) ∧ 2 ≤ n) := by
  cases h with
  | linear n hn e => exact Or.inl ⟨rfl, rfl, hn⟩
  | suzuki a ha e => exact Or.inr (Or.inl ⟨rfl, rfl, a, ha, rfl⟩)
  | unitary n hn e => exact Or.inr (Or.inr ⟨rfl, rfl, hn⟩)

theorem exists_psu3_concrete {n : ℕ} (hn : 2 ≤ n) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
      J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧ Nat.card E = (2 ^ n) ^ 2 ∧
      Nat.card {x : E // J.conj x = x} = 2 ^ n ∧
      Nonempty (PSU3Model n ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  let J := binaryQuadraticHermitian n (by omega)
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  obtain ⟨e⟩ := projectiveSpecialUnitary_equiv_PSU3Model J n hn hJ hEcard hfixed
  exact ⟨_, inferInstance, inferInstance, J, hJ, hEcard, hfixed, ⟨e.symm⟩⟩

theorem BenderType.exists_benderCore
    [Finite K] {n i e : ℕ} (h : BenderType K n i e)
    (Q : Sylow 2 K) : ∃ t, BenderCore (2 ^ n) i e (Q : Subgroup K) t := by
  cases h with
  | linear n hn e => exact exists_benderCore_psl2 e hn Q
  | suzuki a ha e => exact exists_benderCore_suzuki ha e Q
  | unitary n hn e =>
    obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
    obtain ⟨S, w, hcore⟩ := exists_benderCore_psu3_concrete J n hn hcard hfixed hJ
    let φ : K ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e'
    let S' : Sylow 2 K := S.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    have hS' : (S' : Subgroup K) = (S : Subgroup _).map φ.symm.toMonoidHom :=
      Sylow.coe_mapSurjective φ.symm.surjective S
    have := hcore.map φ.symm
    rw [← hS'] at this
    exact this.exists_of_sylow Q

theorem BenderType.benderCore
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K)
    {t : K} (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) :
    BenderCore (2 ^ n) i e (Q : Subgroup K) t := by
  obtain ⟨t₀, h₀⟩ := h.exists_benderCore Q
  exact h₀.of_involution ht htQ

end Assembly

section Consequences

theorem BenderType.isSimpleBenderGroup [Finite K] {n i e : ℕ} (h : BenderType K n i e) :
    IsSimpleBenderGroup K := by
  cases h with
  | linear n hn e => exact IsSimpleBenderGroup.isPSL2 ⟨n, hn, ⟨e⟩⟩
  | suzuki a ha e =>
    exact IsSimpleBenderGroup.isSuzuki
      ⟨a, ha, ⟨e.trans (MulEquiv.subgroupCongr (szModel_eq_suzukiMatrixGroup a))⟩⟩
  | unitary n hn e =>
    obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
    exact IsSimpleBenderGroup.isPSU3 ⟨n, hn, E, hE, hF, J, hJ, hcard, hfixed, ⟨e.trans e'⟩⟩

theorem BenderType.isSimple [Finite K] {n i e : ℕ} (h : BenderType K n i e) : IsSimpleGroup K :=
  h.isSimpleBenderGroup.isSimple

theorem BenderType.card_eq
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) :
    Nat.card K = ((2 ^ n) ^ i + 1) * ((2 ^ n) ^ i * ((2 ^ n - 1) * e)) := by
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  exact hc.card_group

theorem BenderType.pRank_eq
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K) :
    CFSG.Open.pRank 2 (Q : Subgroup K) = n := by
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hZ : CFSG.Open.IsElemAbelian 2 (rootCenter (Q : Subgroup K)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hx' := mem_rootCenter_iff.mp x.2
      have hy' := mem_rootCenter_iff.mp y.2
      exact (hx'.2 y hy'.1).symm
    · rw [sq]
      exact hc.center_sq x hx
  apply IsGreatest.csSup_eq
  refine ⟨⟨rootCenter (Q : Subgroup K), rootCenter_le _, hZ, hc.card_center⟩, ?_⟩
  rintro k ⟨E, hEQ, hE, hEcard⟩
  have hEZ : E ≤ rootCenter (Q : Subgroup K) :=
    hc.elemAbelian_le_rootCenter hEQ fun x hx => by
      have := hE.2 x hx
      rwa [sq] at this
  have hdvd : 2 ^ k ∣ 2 ^ n := by
    rw [← hEcard, ← hc.card_center]
    exact Subgroup.card_dvd_of_le hEZ
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd

theorem BenderType.twoRank_eq
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) :
    CFSG.Open.twoRank K = n := by
  have hQ := h.pRank_eq (default : Sylow 2 K)
  apply IsGreatest.csSup_eq
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  have hZ : CFSG.Open.IsElemAbelian 2 (rootCenter ((default : Sylow 2 K) : Subgroup K)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      have hx' := mem_rootCenter_iff.mp x.2
      have hy' := mem_rootCenter_iff.mp y.2
      exact (hx'.2 y hy'.1).symm
    · rw [sq]
      exact hc.center_sq x hx
  refine ⟨⟨rootCenter ((default : Sylow 2 K) : Subgroup K), le_top, hZ, hc.card_center⟩, ?_⟩
  rintro k ⟨E, -, hE, hEcard⟩
  have hEp : IsPGroup 2 E := IsPGroup.of_card hEcard
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨t', hc'⟩ := h.exists_benderCore Q
  have hEZ : E ≤ rootCenter (Q : Subgroup K) :=
    hc'.elemAbelian_le_rootCenter hEQ fun x hx => by
      have := hE.2 x hx
      rwa [sq] at this
  have hdvd : 2 ^ k ∣ 2 ^ n := by
    rw [← hEcard, ← hc'.card_center]
    exact Subgroup.card_dvd_of_le hEZ
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd

end Consequences

section Unique

theorem BenderType.of_mulEquiv {K K' : Type*} [Group K] [Group K'] {n i e : ℕ}
    (h : BenderType K n i e) (φ : K ≃* K') : BenderType K' n i e := by
  cases h with
  | linear n hn e => exact .linear n hn (φ.symm.trans e)
  | suzuki a ha e => exact .suzuki a ha (φ.symm.trans e)
  | unitary n hn e => exact .unitary n hn (φ.symm.trans e)

theorem BenderType.two_le {K : Type*} [Group K] {n i e : ℕ} (h : BenderType K n i e) :
    1 ≤ i ∧ 2 ≤ n := by
  rcases h.cases' with ⟨hi, -, hn⟩ | ⟨hi, -, a, ha, hn⟩ | ⟨hi, -, hn⟩
  · omega
  · omega
  · omega

theorem BenderType.unique
    [Finite K] {n i e n' i' e' : ℕ} (h : BenderType K n i e)
    (h' : BenderType K n' i' e') : n = n' ∧ i = i' ∧ e = e' := by
  obtain ⟨t, hc⟩ := h.exists_benderCore (default : Sylow 2 K)
  obtain ⟨t', hc'⟩ := h'.exists_benderCore (default : Sylow 2 K)
  have hn : n = n' :=
    Nat.pow_right_injective (le_refl 2) (hc.card_center.symm.trans hc'.card_center)
  subst hn
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
  have hi : i = i' :=
    Nat.pow_right_injective hq2 (hc.card_eq.symm.trans hc'.card_eq)
  subst hi
  refine ⟨rfl, rfl, ?_⟩
  have hcard := h.card_eq.symm.trans h'.card_eq
  have hpos1 : 0 < (2 ^ n) ^ i + 1 := Nat.succ_pos _
  have hpos2 : 0 < (2 ^ n) ^ i := by positivity
  have hpos3 : 0 < 2 ^ n - 1 := by omega
  have h1 := Nat.eq_of_mul_eq_mul_left hpos1 hcard
  have h2 := Nat.eq_of_mul_eq_mul_left hpos2 h1
  exact Nat.eq_of_mul_eq_mul_left hpos3 h2

end Unique

end CFSG.GH74.Uniqueness.Bender
