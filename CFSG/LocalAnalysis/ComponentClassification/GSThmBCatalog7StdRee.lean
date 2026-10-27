module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdArith
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCent
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup

theorem eight_dvd_ordL2sq {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hQ : (2 * k + 1) ^ 2 = 8 * j + 1 := by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    rw [this, hj]
    ring
  rw [hQ]
  have h1 : (8 * j + 1) ^ 2 - 1 = 16 * (j * (4 * j + 1)) := by
    have : (8 * j + 1) ^ 2 = 16 * (j * (4 * j + 1)) + 1 := by ring
    omega
  rw [h1]
  apply Nat.dvd_div_of_mul_dvd
  exact ⟨(8 * j + 1) * (j * (4 * j + 1)), by ring⟩

theorem exists_ne_comm_of_sylow_psl2 {F : Type} [Field F] [Finite F] {q : ℕ} (hq : Odd q)
    (hF : Nat.card F = q ^ 2) (P : Sylow 2 (GorensteinWalter.PSL2 F)) :
    ∃ u ∈ (P : Subgroup (GorensteinWalter.PSL2 F)),
      ∃ v ∈ (P : Subgroup (GorensteinWalter.PSL2 F)), u * v ≠ v * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpp : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    AutL2Facts.isOddPrimePower_of_odd_card F (hF ▸ hq.pow)
  obtain ⟨m, hm1, ⟨eD⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hpp P
  have h8 : 2 ^ 3 ∣ Nat.card (GorensteinWalter.PSL2 F) := by
    rw [GorensteinWalter.psl2_card_formula F hpp, hF]
    exact eight_dvd_ordL2sq hq
  have hP8 := P.pow_dvd_card_of_pow_dvd_card h8
  rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hP8
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm : m = 1 := by omega
    subst hm
    norm_num at hP8
  have hne : (-1 : ZMod (2 ^ m)) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
      have : (2 : ZMod (2 ^ m)) = 1 - (-1) := by ring
      push_cast
      rw [this, h, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  refine ⟨eD.symm (DihedralGroup.r 1), (eD.symm (DihedralGroup.r 1)).2,
    eD.symm (DihedralGroup.sr 0), (eD.symm (DihedralGroup.sr 0)).2, ?_⟩
  intro h
  have h' : eD.symm (DihedralGroup.r 1 * DihedralGroup.sr 0) =
      eD.symm (DihedralGroup.sr 0 * DihedralGroup.r 1) := by
    rw [map_mul, map_mul]
    exact Subtype.ext h
  have h'' := eD.symm.injective h'
  rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq, zero_sub,
    zero_add] at h''
  exact hne h''

theorem isMulCommutative_of_reeTitsModel
    {G : Type} [Group G] {p f : ℕ} (h : Blueprint.ReeTitsModel G .twistedG2 p f)
    (P : Sylow 2 G) : IsMulCommutative (P : Subgroup G) := by
  obtain ⟨hfin, -, hp, ⟨a, -, rfl⟩, hiso⟩ := LieType.Ree.small_Ree_model_Schreier G p f h
  subst hp
  obtain ⟨-, a', ha', K, _, _, hK, hmod⟩ := h
  have haa : a' = a := by omega
  rw [haa] at hmod
  have := Fintype.ofFinite K
  have : CharP K LieType.Ree.ReeTag.G2.prime := charP_of_card_eq_prime_pow (f := 2 * a + 1) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨e⟩ := hiso a K rfl hK hmod
  have : Finite G := hfin
  have : Finite (LieType.Ree.ReeTag.G2.reeGamma K a) := Finite.of_equiv G e.toEquiv
  obtain ⟨w₀, hw₀, -⟩ := LieType.Chevalley.weyl_longest_element LieType.Ree.ReeTag.G2.tag
  have hab := Walter.Ree.Model.hasAbelianSylowTwo_reeGamma hK hw₀
    (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change IsMulCommutative ((P : Subgroup G).map e.toMonoidHom) at hab
  refine ⟨⟨fun x y => ?_⟩⟩
  have h1 := hab.is_comm.comm ⟨e x, x, x.2, rfl⟩ ⟨e y, y, y.2, rfl⟩
  apply Subtype.ext
  apply e.injective
  have h2 := congrArg Subtype.val h1
  simpa only [Subgroup.coe_mul, map_mul] using h2

variable {H : Type} [Group H] [Finite H]

theorem rowRee :
    RowRee := by
  intro H _ _ c m _ hm
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Blueprint.ReeTitsModel ↥(generalizedFitting H) .twistedG2 3 (2 * m + 1) := by
    rcases hm with ⟨hcl, -⟩ | ⟨-, hce, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩
    · exact absurd hcl (by decide)
    · exact absurd hce (by decide)
    · exact h
    · exact absurd ht (by decide)
  have habel : ∀ S : Subgroup ↥(generalizedFitting H), IsPGroup 2 S →
      ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro S hS x hx y hy
    obtain ⟨S', hSS'⟩ := hS.exists_le_sylow
    have hc := (isMulCommutative_of_reeTitsModel hR S').is_comm.comm ⟨x, hSS' hx⟩ ⟨y, hSS' hy⟩
    exact congrArg Subtype.val hc
  obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data c.type_K
  have hF' : Nat.card F = (c.p ^ c.f) ^ 2 := by rw [hF, ← pow_mul, mul_comm]
  set φ : ↥c.K →* GorensteinWalter.PSL2 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥c.K)) with hφ
  have hφs : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥c.K) := inferInstance
  obtain ⟨u, hu, v, hv, huv⟩ := exists_ne_comm_of_sylow_psl2 c.odd_q hF' (P.mapSurjective hφs)
  rw [Sylow.coe_mapSurjective] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  apply huv
  rw [← map_mul, ← map_mul]
  congr 1
  set S : Subgroup ↥(generalizedFitting H) :=
    ((P : Subgroup ↥c.K).map c.K.subtype).subgroupOf (generalizedFitting H) with hS
  have hS2 : IsPGroup 2 S :=
    (P.2.map c.K.subtype).comap_of_injective _ (generalizedFitting H).subtype_injective
  have hxS : (⟨(x : H), c.K_le_G x.2⟩ : ↥(generalizedFitting H)) ∈ S := ⟨x, hx, rfl⟩
  have hyS : (⟨(y : H), c.K_le_G y.2⟩ : ↥(generalizedFitting H)) ∈ S := ⟨y, hy, rfl⟩
  have h1 := habel S hS2 _ hxS _ hyS
  have h2 : (x : H) * y = y * x := congrArg Subtype.val h1
  exact Subtype.ext h2

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
