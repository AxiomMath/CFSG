module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.LocalAnalysis.ABGTheoremB.IV2
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

universe u

section Schur

variable {X : Type*} [Group X]

private theorem commutatorElement_mul_mul_of_mem_center {a b z w : X}
    (hz : z ∈ Subgroup.center X) (hw : w ∈ Subgroup.center X) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [Subgroup.mem_center_iff] at hz hw
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (b * w * z) * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hz (b * w)]; group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [hw a⁻¹]; group
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutator_inf_ker_eq_bot_of_central_pGroup_sl2 [Finite X] {F : Type} [Field F]
    [Finite F] {p f r : ℕ} [Fact p.Prime] [Fact r.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h9 : p ^ f ≠ 9) (h4 : 4 ≤ p ^ f) (hr2 : r ≠ 2)
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hcen : φ.ker ≤ Subgroup.center X) (hpg : IsPGroup r φ.ker) :
    commutator X ⊓ φ.ker = ⊥ := by
  have hperfSL : commutator (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F
      (hF ▸ h4)).commutator_eq_top
  have hEmap : (commutator X).map φ = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hφ, ← commutator_def, hperfSL]
  have hdecomp : ∀ x : X, ∃ e ∈ commutator X, e⁻¹ * x ∈ φ.ker := by
    intro x
    have hx : φ x ∈ (commutator X).map φ := hEmap ▸ Subgroup.mem_top _
    obtain ⟨e, he, hex⟩ := hx
    refine ⟨e, he, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hex, inv_mul_cancel]
  have hperf : ⁅commutator X, commutator X⁆ = commutator X := by
    refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
    conv_lhs => rw [commutator_def]
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨e₁, he₁, hk₁⟩ := hdecomp a
    obtain ⟨e₂, he₂, hk₂⟩ := hdecomp b
    have ha : a = e₁ * (e₁⁻¹ * a) := by group
    have hb : b = e₂ * (e₂⁻¹ * b) := by group
    rw [ha, hb, commutatorElement_mul_mul_of_mem_center (hcen hk₁) (hcen hk₂)]
    exact Subgroup.commutator_mem_commutator he₁ he₂
  have : Group.IsPerfect (commutator X) := Subgroup.isPerfect_iff.mpr hperf
  set E := commutator X
  let π : E →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp
      (φ.comp E.subtype)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hs : s ∈ E.map φ := hEmap ▸ Subgroup.mem_top s
    obtain ⟨e, he, rfl⟩ := hs
    exact ⟨⟨e, he⟩, rfl⟩
  set A : Subgroup X := (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).comap φ
  have hAker : ⁅A, (⊤ : Subgroup X)⁆ ≤ φ.ker := by
    rw [Subgroup.commutator_le]
    intro a ha x _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp ha) (φ x)).symm
  have h1 : ⁅⁅A, (⊤ : Subgroup X)⁆, (⊤ : Subgroup X)⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      ((hAker.trans hcen).trans (Subgroup.center_le_centralizer _))
  have h2 : ⁅⁅(⊤ : Subgroup X), A⁆, (⊤ : Subgroup X)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (⊤ : Subgroup X) A]; exact h1
  have h3 : ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, A⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  have hker : π.ker ≤ Subgroup.center E := by
    intro e he
    have heA : (e : X) ∈ A := by
      have : π e = 1 := he
      exact (QuotientGroup.eq_one_iff (φ e)).mp this
    rw [Subgroup.mem_center_iff]
    intro e'
    have hc : ⁅(e' : X), (e : X)⁆ ∈ ⁅⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆, A⁆ := by
      refine Subgroup.commutator_mem_commutator ?_ heA
      rw [← commutator_def]
      exact e'.2
    rw [h3, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact Subtype.ext hc
  have hsyl : ∀ Cr : Sylow r π.ker, (Cr : Subgroup π.ker) = ⊥ := by
    intro Cr
    by_cases hrp : r = p
    · subst hrp
      exact CFSG.SectionRank.OddCover.psl_two_sylow_kernel_eq_bot hp2 hF h9 π hπ hker Cr
    · obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow r (Matrix.ProjectiveSpecialLinearGroup
        (Fin 2) F)))
      exact CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hker Cr R
        (CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic (Fact.out) hp2 hF hr2 hrp R)
  set W : Subgroup E := φ.ker.subgroupOf E
  have hWker : W ≤ π.ker := by
    intro w hw
    change QuotientGroup.mk' _ (φ w) = 1
    rw [show φ w = 1 from hw, map_one]
  have hW' : IsPGroup r (W.subgroupOf π.ker) := (hpg.comap_subtype).comap_subtype
  obtain ⟨Q, hQ⟩ := hW'.exists_le_sylow
  rw [hsyl Q, le_bot_iff] at hQ
  rw [eq_bot_iff]
  intro x hx
  have hxW : (⟨x, hx.1⟩ : E) ∈ W := hx.2
  have hmem : (⟨⟨x, hx.1⟩, hWker hxW⟩ : π.ker) ∈ W.subgroupOf π.ker := hxW
  rw [hQ, Subgroup.mem_bot] at hmem
  rw [Subgroup.mem_bot]
  exact congrArg (fun y : π.ker => ((y : E) : X)) hmem

private theorem exists_normal_complement_of_central_sylow [Finite X] {r : ℕ} [hr : Fact r.Prime]
    {Y Z : Subgroup X} [Y.Normal] (hZ : IsSylowOf r Z Y) (hZc : Z ≤ Subgroup.center X) :
    ∃ K : Subgroup X, K.Normal ∧ K ≤ Y ∧ ¬ r ∣ Nat.card K ∧ Y ≤ K ⊔ Z := by
  have hZY : Z ≤ Y := hZ.le
  set Z' : Subgroup Y := Z.subgroupOf Y
  have hZ'n : Z'.Normal := by
    constructor
    intro z hz y
    have hz' : (z : X) ∈ Z := hz
    have hc : (y : X) * z * (y : X)⁻¹ = z := by
      rw [(Subgroup.mem_center_iff.mp (hZc hz')) (y : X)]
      group
    change ((y * z * y⁻¹ : Y) : X) ∈ Z
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc]
    exact hz'
  have hZ'card : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZY).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hZ.isPGroup
  have hidx : ¬ r ∣ Z'.index := ((isSylowOf_iff (p := r)).mp hZ).2.2
  have hcop : Nat.Coprime (Nat.card Z') Z'.index := by
    rw [hZ'card, ha]
    exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr.out).mpr hidx)
  obtain ⟨K', hK'⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hK'card : Nat.card K' = Z'.index := hK'.index_eq_card.symm
  have hdec : ∀ y : Y, ∃ k ∈ K', ∃ z ∈ Z', k * z = y := by
    intro y
    obtain ⟨⟨k, z⟩, hkz, -⟩ := Subgroup.IsComplement.existsUnique hK' y
    exact ⟨k, k.2, z, z.2, hkz⟩
  have hpow : ∀ y : Y, y ^ Nat.card K' = 1 → y ∈ K' := by
    intro y hy
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec y
    have hzc : Commute k z := by
      have hz' : ((z : Y) : X) ∈ Z := hz
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (Subgroup.mem_center_iff.mp (hZc hz')) (k : X)
    have hkm : k ^ Nat.card K' = 1 := by
      have : (⟨k, hk⟩ : K') ^ Nat.card K' = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    rw [hzc.mul_pow, hkm, one_mul] at hy
    have hzo : orderOf z ∣ Nat.card K' := orderOf_dvd_of_pow_eq_one hy
    have hzo' : orderOf z ∣ r ^ a := by
      have h1 : orderOf (⟨z, hz⟩ : Z') ∣ Nat.card Z' := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hZ'card, ha] at h1
      exact h1
    have hcop' : Nat.Coprime (r ^ a) (Nat.card K') := by
      rw [hK'card]
      exact Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hr.out).mpr hidx)
    have hz1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop' hzo' hzo
    rw [orderOf_eq_one_iff] at hz1
    rw [hz1, mul_one]
    exact hk
  refine ⟨K'.map Y.subtype, ⟨fun k hk g => ?_⟩, Subgroup.map_subtype_le _, ?_, ?_⟩
  · obtain ⟨k', hk', rfl⟩ := hk
    have hmem : g * (k' : X) * g⁻¹ ∈ Y := (inferInstance : Y.Normal).conj_mem _ k'.2 g
    have hk'm : k' ^ Nat.card K' = 1 := by
      have : (⟨k', hk'⟩ : K') ^ Nat.card K' = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    refine ⟨⟨_, hmem⟩, hpow _ ?_, rfl⟩
    refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow]
    change (g * (k' : X) * g⁻¹) ^ Nat.card K' = 1
    rw [conj_pow, ← SubgroupClass.coe_pow, hk'm]
    simp
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hK'card]
    exact hidx
  · intro y hy
    obtain ⟨k, hk, z, hz, hkz⟩ := hdec ⟨y, hy⟩
    have : y = (k : X) * (z : X) := by rw [← Subgroup.coe_mul, hkz]
    rw [this]
    exact Subgroup.mul_mem_sup ⟨k, hk, rfl⟩ hz

private theorem not_dvd_card_commutator_inf_ker_sl2 [Finite X] {F : Type} [Field F] [Finite F]
    {p f r : ℕ} [Fact p.Prime] [Fact r.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (h9 : p ^ f ≠ 9) (h4 : 4 ≤ p ^ f) (hr2 : r ≠ 2)
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    {Z : Subgroup X} (hZ : IsSylowOf r Z φ.ker) (hZc : Z ≤ Subgroup.center X) :
    ¬ r ∣ Nat.card (commutator X ⊓ φ.ker : Subgroup X) := by
  obtain ⟨K, hKn, hKY, hKr, hYKZ⟩ := exists_normal_complement_of_central_sylow hZ hZc
  let φ' : X ⧸ K →* Matrix.SpecialLinearGroup (Fin 2) F := QuotientGroup.lift K φ hKY
  have hφ' : Function.Surjective φ' := by
    intro s
    obtain ⟨x, rfl⟩ := hφ s
    exact ⟨(x : X ⧸ K), rfl⟩
  have hker' : φ'.ker ≤ Z.map (QuotientGroup.mk' K) := by
    rw [QuotientGroup.ker_lift]
    calc φ.ker.map (QuotientGroup.mk' K) ≤ (K ⊔ Z).map (QuotientGroup.mk' K) :=
          Subgroup.map_mono hYKZ
      _ = Z.map (QuotientGroup.mk' K) := by
          rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hcen' : φ'.ker ≤ Subgroup.center (X ⧸ K) :=
    hker'.trans ((Subgroup.map_mono hZc).trans
      (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective K)))
  have hpg' : IsPGroup r φ'.ker := (hZ.isPGroup.map _).to_le hker'
  have hbot := commutator_inf_ker_eq_bot_of_central_pGroup_sl2 hp2 hF h9 h4 hr2 φ' hφ' hcen'
    hpg'
  have hle : commutator X ⊓ φ.ker ≤ K := by
    intro x hx
    have h1 : (x : X ⧸ K) ∈ commutator (X ⧸ K) := by
      have : (commutator X).map (QuotientGroup.mk' K) ≤ commutator (X ⧸ K) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator]
        exact Subgroup.commutator_mono le_top le_top
      exact this ⟨x, hx.1, rfl⟩
    have h2 : (x : X ⧸ K) ∈ φ'.ker := hx.2
    have h3 : (x : X ⧸ K) ∈ commutator (X ⧸ K) ⊓ φ'.ker := ⟨h1, h2⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h3
    exact h3
  exact fun h => hKr (h.trans (Subgroup.card_dvd_of_le hle))

end Schur

section General

variable {G : Type u} [Group G]

private theorem normalizer_le_normalizer_centralizer' [Finite G] (T : Subgroup G) :
    Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun c hc => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro t ht
  have ht' : g⁻¹ * t * g ∈ T := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
    simpa using h
  have h := hc _ ht'
  calc t * (g * c * g⁻¹) = g * ((g⁻¹ * t * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * t := by group

private theorem mem_normalizer_commutator {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_commutator, hH, hK]

private theorem isSylowOf_map_conj' [Finite G] {r : ℕ} [Fact r.Prime] {P C : Subgroup G}
    (hP : IsSylowOf r P C) {g : G} (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    IsSylowOf r (P.map (MulAut.conj g).toMonoidHom) C := by
  refine isSylowOf_of_card ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg y).mp (hP.le hy)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP.card_eq]

private theorem exists_conj_eq_of_isSylowOf' [Finite G] {r : ℕ} [Fact r.Prime] {P Q C : Subgroup G}
    (hP : IsSylowOf r P C) (hQ : IsSylowOf r Q C) :
    ∃ c ∈ C, Q.map (MulAut.conj c).toMonoidHom = P := by
  obtain ⟨P₁, rfl⟩ := hP
  obtain ⟨Q₁, rfl⟩ := hQ
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₁ P₁
  refine ⟨c, c.2, ?_⟩
  have hsmul : ((c • Q₁ : Sylow r C) : Subgroup C) =
      (Q₁ : Subgroup C).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [← hc, hsmul, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem mem_normalizer_subgroupOf_iff' {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.normalizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.mem_subgroupOf]

private theorem mem_centralizer_subgroupOf_iff' {T H : Subgroup G} (hTH : T ≤ H) {g : H} :
    g ∈ Subgroup.centralizer (T.subgroupOf H : Set H) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTH ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem exists_of_three_dvd_automizerIndex' {K : Type*} [Group K] [Finite K]
    {T : Subgroup K} (h : 3 ∣ automizerIndex T) :
    ∃ g ∈ Subgroup.normalizer (T : Set K), g ^ 3 ∈ Subgroup.centralizer (T : Set K) ∧
      g ∉ Subgroup.centralizer (T : Set K) := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' T)
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, g.2, ?_, ?_⟩
  · have : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  · intro hg
    have : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [this, orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem three_dvd_automizerIndex_of' {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    {g : K} (hg : g ∈ Subgroup.normalizer (T : Set K))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set K))
    (h1 : g ∉ Subgroup.centralizer (T : Set K)) : 3 ∣ automizerIndex T := by
  set Nt := Subgroup.normalizer (T : Set K)
  set Ct := Subgroup.centralizer (T : Set K)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' T)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 3 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using h3
    · rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact h1
  have := orderOf_dvd_natCard ((⟨g, hg⟩ : Nt) : Nt ⧸ Ct.subgroupOf Nt)
  rw [hord, ← Subgroup.index_eq_card] at this
  exact this

private theorem exists_of_three_dvd_automizerIndex_subgroupOf' [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf H)) :
    ∃ g ∈ H, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex' h
  refine ⟨g, g.2, (mem_normalizer_subgroupOf_iff' hTH).mp hgN, ?_, ?_⟩
  · simpa using (mem_centralizer_subgroupOf_iff' hTH).mp hg3
  · exact fun h' => hg1 ((mem_centralizer_subgroupOf_iff' hTH).mpr h')

private theorem three_dvd_automizerIndex_subgroupOf_of' [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) {g : G} (hgH : g ∈ H) (hg : g ∈ Subgroup.normalizer (T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (T : Set G)) (h1 : g ∉ Subgroup.centralizer (T : Set G)) :
    3 ∣ automizerIndex (T.subgroupOf H) :=
  three_dvd_automizerIndex_of' (g := ⟨g, hgH⟩) ((mem_normalizer_subgroupOf_iff' hTH).mpr hg)
    ((mem_centralizer_subgroupOf_iff' hTH).mpr (by simpa using h3))
    (fun h' => h1 ((mem_centralizer_subgroupOf_iff' hTH).mp h'))

private theorem three_dvd_automizerIndex_mono [Finite G] {T K H : Subgroup G} (hTK : T ≤ K)
    (hKH : K ≤ H) (h : 3 ∣ automizerIndex (T.subgroupOf K)) :
    3 ∣ automizerIndex (T.subgroupOf H) := by
  obtain ⟨g, hgK, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex_subgroupOf' hTK h
  exact three_dvd_automizerIndex_subgroupOf_of' (hTK.trans hKH) (hKH hgK) hgN hg3 hg1

private theorem mul_pow_three_mem {M : Subgroup G} {c g : G} (hc : c ∈ M)
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (h3 : g ^ 3 ∈ M) : (c * g) ^ 3 ∈ M := by
  have h1 : g * c * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hg c).mp hc
  have h2 : g * (g * c * g⁻¹) * g⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hg _).mp h1
  have heq : (c * g) ^ 3 = c * (g * c * g⁻¹) * (g * (g * c * g⁻¹) * g⁻¹) * g ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]; group
  rw [heq]
  exact M.mul_mem (M.mul_mem (M.mul_mem hc h1) h2) h3

private theorem centerOf_ne_bot_of_isPGroup [Finite G] {r : ℕ} [Fact r.Prime] {H : Subgroup G}
    (hH : IsPGroup r H) (hne : H ≠ ⊥) : centerOf H ≠ ⊥ := by
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH.bot_lt_center.ne'
  intro hbot
  have hmem : ((z : H) : G) ∈ centerOf H := by
    refine ⟨(z : H).2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    have := (Subgroup.mem_center_iff.mp z.2) ⟨h, hh⟩
    exact congrArg Subtype.val this
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 (Subtype.ext (Subtype.ext hmem))

private theorem exists_centralizer_mul_inv_mem [Finite G] {r : ℕ} [Fact r.Prime]
    {A M : Subgroup G} (hA : IsPGroup r A) (hAM : A ≤ Subgroup.normalizer (M : Set G))
    (hM : ¬ r ∣ Nat.card M) {b : G} (hb : ∀ a ∈ A, a * b * a⁻¹ * b⁻¹ ∈ M) :
    ∃ c ∈ Subgroup.centralizer (A : Set G), c * b⁻¹ ∈ M := by
  let α : A →* MulAut G := MulAut.conj.comp A.subtype
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed r hA α M
    hM b).1 (by
      intro a x hx
      change (a : G) * x * (a : G)⁻¹ * b⁻¹ ∈ M
      have h1 : (a : G) * (x * b⁻¹) * (a : G)⁻¹ ∈ M :=
        (Subgroup.mem_normalizer_iff.mp (hAM a.2) _).mp hx
      have heq : (a : G) * x * (a : G)⁻¹ * b⁻¹ =
          ((a : G) * (x * b⁻¹) * (a : G)⁻¹) * ((a : G) * b * (a : G)⁻¹ * b⁻¹) := by group
      rw [heq]
      exact M.mul_mem h1 (hb a a.2))
  refine ⟨c, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, hc⟩
  have h := hfix ⟨a, ha⟩
  change a * c * a⁻¹ = c at h
  calc a * c = a * c * a⁻¹ * a := by group
    _ = c * a := by rw [h]

private theorem map_commutator_eq_top_sl2 {X : Type*} [Group X] {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F) (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hφ : Function.Surjective φ) : (commutator X).map φ = ⊤ := by
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hφ, ← commutator_def,
    (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4).commutator_eq_top]

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem L_le_N' (hσ : σ.IsValid) : σ.L ≤ σ.N :=
  sup_le hσ.L₀_le_N (σ.S_le_N hσ)

private theorem le_L₀_of_le_L (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {U : Subgroup G} (hU : IsPGroup r U) (hUL : U ≤ σ.L) : U ≤ σ.L₀ := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : σ.L ≤ Subgroup.normalizer (σ.L₀ : Set G) :=
    (L_le_N' σ hσ).trans hσ.N_le_normalizer_L₀
  have hU' : U ≤ Subgroup.normalizer (σ.L₀ : Set G) := hUL.trans hLN
  have hS' : (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.L₀ : Set G) := le_sup_right.trans hLN
  have h1 := relIndex_sup_right_of_le_normalizer hU'
  have h2 := relIndex_sup_right_of_le_normalizer hS'
  have hdvd : σ.L₀.relIndex (U ⊔ σ.L₀) ∣ σ.L₀.relIndex ((σ.S : Subgroup G) ⊔ σ.L₀) := by
    have hle2 : U ⊔ σ.L₀ ≤ (σ.S : Subgroup G) ⊔ σ.L₀ := by
      refine sup_le ?_ le_sup_right
      rw [sup_comm]
      exact hUL
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle2)
  rw [h1, h2] at hdvd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp σ.S.isPGroup'
  have hU1 : σ.L₀.relIndex U ∣ r ^ a := ha ▸ Subgroup.relIndex_dvd_card _ _
  have hS1 : σ.L₀.relIndex (σ.S : Subgroup G) ∣ 2 ^ b := hb ▸ Subgroup.relIndex_dvd_card _ _
  have hcop : Nat.Coprime (r ^ a) (2 ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hU1 (hdvd.trans hS1))

private theorem inf_L₀_ne_bot (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hdvd : r ∣ Nat.card (σ.C ⊓ σ.L : Subgroup G)) {P : Subgroup G} (hP : IsSylowOf r P σ.C) :
    P ⊓ σ.L₀ ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe, hx]
  have hU : IsPGroup r (Subgroup.zpowers (x : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hUCL : Subgroup.zpowers (x : G) ≤ σ.C ⊓ σ.L := Subgroup.zpowers_le.mpr x.2
  have hUL₀ : Subgroup.zpowers (x : G) ≤ σ.L₀ :=
    le_L₀_of_le_L σ hσ hr hr2 hU (hUCL.trans inf_le_right)
  obtain ⟨Q, hQ⟩ := (hU.comap_subtype (K := σ.C)).exists_le_sylow
  have hP' : IsSylowOf r ((Q : Subgroup σ.C).map σ.C.subtype) σ.C := ⟨Q, rfl⟩
  have hxQ : (x : G) ∈ (Q : Subgroup σ.C).map σ.C.subtype := by
    have hxC : (x : G) ∈ σ.C := (hUCL (Subgroup.mem_zpowers _)).1
    refine ⟨⟨x, hxC⟩, hQ ?_, rfl⟩
    change (x : G) ∈ Subgroup.zpowers (x : G)
    exact Subgroup.mem_zpowers _
  obtain ⟨c, hcC, hc⟩ := exists_conj_eq_of_isSylowOf' hP hP'
  intro hbot
  have hmem : c * (x : G) * c⁻¹ ∈ P ⊓ σ.L₀ := by
    refine ⟨?_, ?_⟩
    · rw [← hc]
      exact ⟨x, hxQ, rfl⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        (hσ.N_le_normalizer_L₀ (σ.C_le_N hcC)) _).mp (hUL₀ (Subgroup.mem_zpowers _))
  rw [hbot, Subgroup.mem_bot] at hmem
  have hx1 : (x : G) = 1 := by
    have : c * (x : G) * c⁻¹ = c * 1 * c⁻¹ := by rw [hmem]; group
    exact mul_left_cancel (mul_right_cancel this)
  rw [hx1, orderOf_one] at hxo
  exact hr.one_lt.ne hxo

private theorem inf_ON_le_of_isSylowOf {r : ℕ} (hr : r.Prime) {P R : Subgroup G}
    (hP : IsPGroup r P) (hR : IsSylowOf r R σ.ON) (hRP : P ≤ Subgroup.normalizer (R : Set G)) :
    P ⊓ σ.ON ≤ R := by
  have : Fact r.Prime := ⟨hr⟩
  have h1 : IsPGroup r ((P ⊓ σ.ON ⊔ R : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' (hP.to_le inf_le_left) hR.isPGroup (inf_le_left.trans hRP)
  exact le_sup_left.trans (hR.eq_of_le le_sup_right (sup_le inf_le_right hR.le) h1).le

private theorem le_centerOf_of_isSylowOf {r : ℕ} (hr : r.Prime) {R U : Subgroup G}
    (hR : IsSylowOf r R σ.ON) (hU : IsPGroup r U) (hUON : U ≤ σ.ON)
    (hUR : U ≤ Subgroup.centralizer (R : Set G)) : U ≤ centerOf R := by
  have : Fact r.Prime := ⟨hr⟩
  have h1 : IsPGroup r ((U ⊔ R : Subgroup G)) := IsPGroup.to_sup_of_normal_right' hU hR.isPGroup
    (hUR.trans (Subgroup.centralizer_le_normalizer _))
  have h2 := hR.eq_of_le le_sup_right (sup_le hUON hR.le) h1
  exact le_inf (le_sup_left.trans h2.le) hUR

private theorem isSylowOf_centerOf {r : ℕ} (hr : r.Prime) {R : Subgroup G}
    (hR : IsSylowOf r R σ.ON) :
    IsSylowOf r (centerOf R) (σ.ON ⊓ Subgroup.centralizer (R : Set G)) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨Q, hQ⟩ := exists_isSylowOf r (σ.ON ⊓ Subgroup.centralizer (R : Set G))
  have hQZ : Q ≤ centerOf R :=
    le_centerOf_of_isSylowOf σ hr hR hQ.isPGroup (hQ.le.trans inf_le_left)
      (hQ.le.trans inf_le_right)
  have hZ : centerOf R ≤ σ.ON ⊓ Subgroup.centralizer (R : Set G) :=
    le_inf (inf_le_left.trans hR.le) inf_le_right
  rw [hQ.eq_of_le hQZ hZ (hR.isPGroup.to_le inf_le_left)]
  exact hQ

private theorem three_dvd_automizerIndex_normalizer (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) {P : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hTP : σ.T ≤ Subgroup.normalizer (P : Set G)) :
    3 ∣ automizerIndex (σ.T.subgroupOf (Subgroup.normalizer (P : Set G))) := by
  have : Fact r.Prime := ⟨hr⟩
  have h6 : 3 ∣ automizerIndex σ.T := by rw [hII.automizer_T]; norm_num
  obtain ⟨g, hgN, hg3, hg1⟩ := exists_of_three_dvd_automizerIndex' h6
  have hgC : g ∈ Subgroup.normalizer (σ.C : Set G) := normalizer_le_normalizer_centralizer' σ.T hgN
  obtain ⟨c, hcC, hc⟩ := exists_conj_eq_of_isSylowOf' hP (isSylowOf_map_conj' hP hgC)
  have hcT : c ∈ Subgroup.centralizer (σ.T : Set G) := hcC
  refine three_dvd_automizerIndex_subgroupOf_of' hTP (g := c * g) ?_
    (Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ hcT) hgN)
    (mul_pow_three_mem hcT (normalizer_le_normalizer_centralizer' σ.T hgN) hg3) ?_
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hc]
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  · intro hcg
    apply hg1
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hcT) hcg
    rwa [inv_mul_cancel_left] at this

private theorem exists_sl2_section_centralizer (hσ : σ.IsValid) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P R : Subgroup G} (hPC : P ≤ σ.C) (hPr : IsPGroup r P)
    (hR : IsSylowOf r R σ.ON) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (hcov : (σ.L₀ : Set G) ⊆
      ((σ.N ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) * (σ.ON : Set G))
    (h9 : σ.q ≠ 9) {Λ : Subgroup G}
    (hΛ : ∀ l : G, l ∈ Λ ↔ l ∈ σ.L₀ ∧ ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ σ.ON)
    {F₀ : Type} [Field F₀] [Finite F₀] (φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀)
    (hφ : Function.Surjective φ) (hφker : φ.ker = σ.ON.subgroupOf Λ) :
    ∃ X : Subgroup G, X ≤ Subgroup.centralizer (P : Set G) ∧
      ∃ φ' : X →* Matrix.SpecialLinearGroup (Fin 2) F₀, Function.Surjective φ' ∧
        φ'.ker = (σ.ON ⊓ X).subgroupOf X := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  obtain ⟨F, _, _, hFq, ψ, hψ, hψker⟩ := hσ.L₀_quotient
  have hq4 : 4 ≤ σ.p ^ σ.f := by have := hσ.five_lt_q; rw [Setting.q] at this; omega
  have hF : Nat.card F = σ.p ^ σ.f := hFq
  set X₀ : Subgroup G := σ.L₀ ⊓ Subgroup.centralizer (R : Set G) with hX₀
  have hX₀L₀ : X₀ ≤ σ.L₀ := inf_le_left
  let ψ₀ : X₀ →* Matrix.SpecialLinearGroup (Fin 2) F := ψ.comp (Subgroup.inclusion hX₀L₀)
  have hψ₀ker : ψ₀.ker = σ.ON.subgroupOf X₀ := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hψ₀ : Function.Surjective ψ₀ := by
    intro s
    obtain ⟨l, rfl⟩ := hψ s
    obtain ⟨a, ha, b, hb, hab⟩ := hcov l.2
    have hbL₀ : b ∈ σ.L₀ := hσ.ON_le_L₀ hb
    have haL₀ : a ∈ σ.L₀ := by
      have : a = (l : G) * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact σ.L₀.mul_mem l.2 (σ.L₀.inv_mem hbL₀)
    refine ⟨⟨a, haL₀, ha.2⟩, ?_⟩
    have hb1 : ψ ⟨b, hbL₀⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hψker]
      exact hb
    have hl : l = ⟨a, haL₀⟩ * ⟨b, hbL₀⟩ := Subtype.ext hab.symm
    change ψ ⟨a, haL₀⟩ = ψ l
    rw [hl, map_mul, hb1, mul_one]
  have hZsyl : IsSylowOf r ((centerOf R).subgroupOf X₀) ψ₀.ker := by
    rw [hψ₀ker, ← isSylowOf_map_subtype_iff X₀, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype]
    have h1 : centerOf R ⊓ X₀ = centerOf R :=
      inf_eq_left.mpr (le_inf ((inf_le_left.trans hR.le).trans hσ.ON_le_L₀) inf_le_right)
    have h2 : σ.ON ⊓ X₀ = σ.ON ⊓ Subgroup.centralizer (R : Set G) := by
      rw [hX₀, ← inf_assoc, inf_eq_left.mpr hσ.ON_le_L₀]
    rw [h1, h2]
    exact isSylowOf_centerOf σ hr hR
  have hZc : (centerOf R).subgroupOf X₀ ≤ Subgroup.center X₀ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    have hzR : (z : G) ∈ R := hz.1
    have hxR := Subgroup.mem_centralizer_iff.mp x.2.2 (z : G) hzR
    exact Subtype.ext hxR.symm
  have h9' : σ.p ^ σ.f ≠ 9 := h9
  have hschur := not_dvd_card_commutator_inf_ker_sl2 hσ.p_ne_two hF h9' hq4 hr2 ψ₀ hψ₀ hZsyl
    hZc
  set J₀ : Subgroup G := ⁅X₀, X₀⁆ with hJ₀
  have hJ₀X₀ : J₀ ≤ X₀ := by
    rw [hJ₀, ← Subgroup.map_subtype_commutator]
    exact Subgroup.map_subtype_le _
  have hJ₀card : ¬ r ∣ Nat.card (J₀ ⊓ σ.ON : Subgroup G) := by
    have hmap : (commutator X₀ ⊓ ψ₀.ker).map X₀.subtype = J₀ ⊓ σ.ON := by
      have hJ₀X₀' : ⁅X₀, X₀⁆ ⊓ X₀ = ⁅X₀, X₀⁆ := inf_eq_left.mpr hJ₀X₀
      rw [Subgroup.map_inf _ _ _ X₀.subtype_injective, Subgroup.map_subtype_commutator,
        hψ₀ker, Subgroup.subgroupOf_map_subtype, ← inf_assoc, inf_right_comm, hJ₀X₀']
    rw [← hmap, Subgroup.card_map_of_injective X₀.subtype_injective]
    exact hschur
  have hJcov : (σ.L₀ : Set G) ⊆ (J₀ : Set G) * (σ.ON : Set G) := by
    intro l hl
    have htop := map_commutator_eq_top_sl2 (hF ▸ hq4) ψ₀ hψ₀
    have hmem : ψ ⟨l, hl⟩ ∈ (commutator X₀).map ψ₀ := htop ▸ Subgroup.mem_top _
    obtain ⟨j, hj, hjl⟩ := hmem
    have hjJ : (j : G) ∈ J₀ := by
      rw [hJ₀, ← Subgroup.map_subtype_commutator]
      exact ⟨j, hj, rfl⟩
    have hjL₀ : (j : G) ∈ σ.L₀ := hX₀L₀ j.2
    have hn : (j : G)⁻¹ * l ∈ σ.ON := by
      have h1 : (⟨(j : G)⁻¹ * l, σ.L₀.mul_mem (σ.L₀.inv_mem hjL₀) hl⟩ : σ.L₀) ∈ ψ.ker := by
        have heq : (⟨(j : G)⁻¹ * l, σ.L₀.mul_mem (σ.L₀.inv_mem hjL₀) hl⟩ : σ.L₀) =
            (Subgroup.inclusion hX₀L₀ j)⁻¹ * ⟨l, hl⟩ := rfl
        rw [MonoidHom.mem_ker, heq, map_mul, map_inv]
        change (ψ₀ j)⁻¹ * ψ ⟨l, hl⟩ = 1
        rw [hjl, inv_mul_cancel]
      rw [hψker] at h1
      exact h1
    exact ⟨j, hjJ, (j : G)⁻¹ * l, hn, by group⟩
  have hPJ : P ≤ Subgroup.normalizer (J₀ : Set G) := by
    intro g hg
    have hgL₀ : g ∈ Subgroup.normalizer (σ.L₀ : Set G) :=
      hσ.N_le_normalizer_L₀ (σ.C_le_N (hPC hg))
    have hgCR : g ∈ Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) :=
      normalizer_le_normalizer_centralizer' R (hRP hg)
    have hgX₀ : g ∈ Subgroup.normalizer (X₀ : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hgL₀, hgCR⟩
    exact mem_normalizer_commutator hgX₀ hgX₀
  have hPN : P ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (hPC.trans σ.C_le_N).trans σ.N_le_normalizer_ON
  have hPJON : P ≤ Subgroup.normalizer ((J₀ ⊓ σ.ON : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hPJ hg, hPN hg⟩
  have hONΛ : σ.ON ≤ Λ := by
    intro n hn
    refine (hΛ n).mpr ⟨hσ.ON_le_L₀ hn, fun g hg => σ.ON.mul_mem ?_ (σ.ON.inv_mem hn)⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPN hg) n).mp hn
  set X : Subgroup G := J₀ ⊓ Subgroup.centralizer (P : Set G)
  have hXΛ : X ≤ Λ := by
    intro x hx
    refine (hΛ x).mpr ⟨hX₀L₀ (hJ₀X₀ hx.1), fun g hg => ?_⟩
    have hc : g * x = x * g := Subgroup.mem_centralizer_iff.mp hx.2 g hg
    have : g * x * g⁻¹ * x⁻¹ = 1 := by rw [hc]; group
    rw [this]
    exact σ.ON.one_mem
  refine ⟨X, inf_le_right, φ.comp (Subgroup.inclusion hXΛ), ?_, ?_⟩
  · intro s
    obtain ⟨l, rfl⟩ := hφ s
    have hlL₀ : (l : G) ∈ σ.L₀ := ((hΛ l).mp l.2).1
    obtain ⟨j, hj, n, hn, hjn⟩ := hJcov hlL₀
    have hjΛ : j ∈ Λ := by
      have : j = (l : G) * n⁻¹ := by rw [← hjn]; group
      rw [this]
      exact Λ.mul_mem l.2 (Λ.inv_mem (hONΛ hn))
    have hcond : ∀ a ∈ P, a * j * a⁻¹ * j⁻¹ ∈ J₀ ⊓ σ.ON := by
      intro a ha
      refine ⟨J₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPJ ha) j).mp hj) (J₀.inv_mem hj),
        ((hΛ j).mp hjΛ).2 a ha⟩
    obtain ⟨c, hcP, hcj⟩ := exists_centralizer_mul_inv_mem hPr hPJON hJ₀card hcond
    have hcJ : c ∈ J₀ := by
      have : c = (c * j⁻¹) * j := by group
      rw [this]
      exact J₀.mul_mem hcj.1 hj
    have hcX : c ∈ X := ⟨hcJ, hcP⟩
    refine ⟨⟨c, hcX⟩, ?_⟩
    have hcjΛ : c * j⁻¹ ∈ Λ := hONΛ hcj.2
    have hnΛ : n⁻¹ ∈ Λ := Λ.inv_mem (hONΛ hn)
    have heq : (Subgroup.inclusion hXΛ ⟨c, hcX⟩ : Λ) = ⟨c * j⁻¹, hcjΛ⟩ * l * ⟨n⁻¹, hnΛ⟩ := by
      refine Subtype.ext ?_
      change c = c * j⁻¹ * (l : G) * n⁻¹
      rw [← hjn]
      group
    have h1 : φ ⟨c * j⁻¹, hcjΛ⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hφker]
      exact hcj.2
    have h2 : φ ⟨n⁻¹, hnΛ⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hφker]
      exact σ.ON.inv_mem hn
    change φ (Subgroup.inclusion hXΛ ⟨c, hcX⟩) = φ l
    rw [heq, map_mul, map_mul, h1, h2, one_mul, mul_one]
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩

private theorem ne_nine_and_odd_of_eq_pow (hσ : σ.IsValid) {q₀ m : ℕ} (hq₀ : 2 ≤ q₀)
    (hm1 : 1 < m) (hmodd : Odd m) (hq : σ.q = q₀ ^ m) : σ.q ≠ 9 ∧ Odd q₀ := by
  have hpodd : Odd σ.p := hσ.p_prime.eq_two_or_odd'.resolve_left hσ.p_ne_two
  have hqodd : Odd σ.q := hpodd.pow
  have hq₀odd : Odd q₀ := by
    rw [hq] at hqodd
    exact (Nat.odd_pow_iff (by omega)).mp hqodd
  refine ⟨fun h9 => ?_, hq₀odd⟩
  have hm3 : 3 ≤ m := by obtain ⟨k, rfl⟩ := hmodd; omega
  have hq₀3 : 3 ≤ q₀ := by obtain ⟨k, rfl⟩ := hq₀odd; omega
  have h27 : 3 ^ 3 ≤ q₀ ^ m :=
    (Nat.pow_le_pow_right (by norm_num) hm3).trans (Nat.pow_le_pow_left hq₀3 m)
  rw [← hq, h9] at h27
  norm_num at h27

theorem center_le_L₀_of_not_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (hnc : ¬ σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (_hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h_II42v : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G, IsSylowOf r P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → centerOf P ≤ σ.L ∨ P ⊓ σ.L ≤ σ.ON)
    (h_II42vi : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ P : Subgroup G, IsSylowOf r P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) → ¬ centerOf P ≤ σ.L₀ → P ⊓ σ.L ≤ σ.ON →
        ∃ Λ : Subgroup G, (∀ l : G, l ∈ Λ ↔ l ∈ σ.L₀ ∧ ∀ g ∈ P, g * l * g⁻¹ * l⁻¹ ∈ σ.ON) ∧
          ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (m : ℕ), 1 < m ∧ Odd m ∧
            σ.q = Nat.card F₀ ^ m ∧ ∃ φ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F₀,
              Function.Surjective φ ∧ φ.ker = σ.ON.subgroupOf Λ)
    (h_II55 : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
      ∀ X : Subgroup G, X ≤ H → ∀ (F : Type) [Field F] [Finite F], Odd (Nat.card F) →
        ∀ φ : X →* Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective φ →
          ¬ Odd (Nat.card φ.ker)) :
    centerOf P ≤ σ.L₀ := by
  have hrp : r.Prime := hr.prime
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hrp hr.dvd_ON
  by_contra hZ
  have hPL : P ⊓ σ.L ≤ σ.ON := (h_II42v r hrp hr.dvd_ON P hP hPD).resolve_left fun h =>
    hZ (le_L₀_of_le_L σ hσ hrp hr2 (hP.isPGroup.to_le inf_le_left) h)
  have hPON : P ⊓ σ.ON ≠ ⊥ := by
    intro hbot
    apply inf_L₀_ne_bot σ hσ hrp hr2 hr.dvd_CL hP
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ P ⊓ σ.ON := ⟨hx.1, hPL ⟨hx.1, (le_sup_left : σ.L₀ ≤ σ.L) hx.2⟩⟩
    rwa [hbot] at hx'
  have hcov := (σ.not_constrained_iff_covers hσ hII hrp hr.dvd_ON hR).mp hnc
  have hPONR : P ⊓ σ.ON ≤ R := inf_ON_le_of_isSylowOf σ hrp hP.isPGroup hR hRP
  set A := centerOf (P ⊓ σ.ON)
  have hAP : A ≤ P := inf_le_left.trans inf_le_left
  have hAR : A ≤ R := inf_le_left.trans hPONR
  have hA : A ≠ ⊥ := centerOf_ne_bot_of_isPGroup (hP.isPGroup.to_le inf_le_left) hPON
  have hAA : A ≤ Subgroup.centralizer (A : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.mp ha.2 b hb.1
  have hCPH₁ : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le hAP
  have hTCP : σ.T ≤ Subgroup.centralizer (P : Set G) := Subgroup.le_centralizer_iff.mp hP.le
  have hOH₁ : oddCoreIn (Subgroup.centralizer (A : Set G)) ≠ ⊥ := by
    have hodd : Odd (Nat.card A) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.isPGroup.to_le hAP)
      rw [hk]
      exact (hrp.eq_two_or_odd'.resolve_left hr2).pow
    have hle := le_oddCoreIn hAA (Subgroup.centralizer_le_normalizer _) hodd
    intro hbot
    rw [hbot, le_bot_iff] at hle
    exact hA hle
  have hcovH₁ : (σ.L₀ : Set G) ⊆
      (Subgroup.centralizer (A : Set G) : Set G) * (σ.ON : Set G) :=
    hcov.trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr
      (inf_le_right.trans (Subgroup.centralizer_le hAR))))
  have hH₁ : IsQGroup (Subgroup.centralizer (A : Set G)) :=
    (hII.cover_qgroup _ (hTCP.trans hCPH₁) hOH₁ hcovH₁).1.1
  have hTNP : σ.T ≤ Subgroup.normalizer (P : Set G) := (σ.T_le_D hσ).trans hPD
  have h3 := three_dvd_automizerIndex_normalizer σ hII hrp hP hTNP
  rcases hII.qd_or_d_of_three _ hTNP (Or.inl hPD) h3 with hQD | hDg
  ·
    obtain ⟨T₁, hT₁, hK₁, h3'⟩ := hII.normal_contains_three _ hPD (Or.inl hQD)
      (Subgroup.centralizer (P : Set G)) (Subgroup.centralizer_le_normalizer _)
      (normalizer_le_normalizer_centralizer' P) hTCP
    exact hII.qgroup_no_three _ hH₁ T₁ (hT₁.trans hCPH₁) hK₁
      (three_dvd_automizerIndex_mono hT₁ hCPH₁ h3')
  ·
    obtain ⟨Λ, hΛ, F₀, _, _, m, hm1, hmodd, hqm, φ, hφ, hφker⟩ :=
      h_II42vi r hrp hr.dvd_ON P hP hPD hZ hPL
    obtain ⟨h9, hF₀odd⟩ := ne_nine_and_odd_of_eq_pow σ hσ Finite.one_lt_card hm1 hmodd hqm
    obtain ⟨X, hXP, φ', hφ', hφ'ker⟩ := exists_sl2_section_centralizer σ hσ hrp hr2 hP.le
      hP.isPGroup hR hRP hcov h9 hΛ φ hφ hφker
    refine h_II55 _ hPD hDg X (hXP.trans (Subgroup.centralizer_le_normalizer _)) F₀ hF₀odd φ'
      hφ' ?_
    rw [hφ'ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

end Setting

end CFSG.ABGTheoremB
