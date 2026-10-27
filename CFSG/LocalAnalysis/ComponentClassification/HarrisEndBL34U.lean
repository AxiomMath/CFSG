module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Wit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34E4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Q8

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.LLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* PSL3Four.S}

theorem eq_of_mem_layer_pCore (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    {y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)}
    (hyE : y ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (hyQ : y ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
    y = 1 ∨ y = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyZ : (⟨y, hyE⟩ : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∈
      center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [mem_center_iff]
    intro e
    rw [← hs.centralizer_layer_eq hL.h412] at hyQ
    exact Subtype.ext (mem_centralizer_iff.mp hyQ e e.2)
  obtain ⟨b, hb, hbeq⟩ := hL.h412.lemma46c.2.2 hZ
  have hbeq' : (b : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := hbeq
  have hb2 : b ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hbeq', hs.betaBar_sq]; rfl)
  have hb1 : b ≠ 1 := fun h => hs.betaBar_ne_one (by rw [← hbeq', h]; rfl)
  have hzb : zpowers b = center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hb) ?_
    rw [h2, Nat.card_zpowers, orderOf_eq_prime hb2 hb1]
  rw [← hzb] at hyZ
  rcases EndB.eq_one_or_eq_of_mem_zpowers_sq hb2 hyZ with h | h
  · left
    exact congrArg Subtype.val h
  · right
    rw [← hbeq']
    exact congrArg Subtype.val h

theorem unitary_layer_facts
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {d : Equiv.Perm (Fin 42)} (hd : d ∈ PSL3Four.R)
    (hgd : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = d * PSL3Four.r₄ * d⁻¹)
    {U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hU : IsSylowOf 2 U (centralizer {g})) (hgU : g ∈ U)
    (hβU : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ U) :
    Nat.card ↥(U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) = 8 ∧
      (∀ u ∈ U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        ∀ v ∈ U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), u * v = v * u) ∧
      (∀ u ∈ U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), u ^ 4 = 1) ∧
      ∀ B : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
        B ≤ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {g} →
        IsPGroup 2 B → Nat.card B ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := inferInstance
  have hCN : centralizer {g} ≤ normalizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {g} : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    intro x hx
    refine mem_normalizer_iff.mpr fun a => ⟨fun ha => mem_inf.mpr
      ⟨hn.conj_mem a (mem_inf.mp ha).1 x, mul_mem (mul_mem hx (mem_inf.mp ha).2) (inv_mem hx)⟩,
        fun ha => ?_⟩
    have h1 : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {g} := mem_inf.mpr ⟨hn.conj_mem _ (mem_inf.mp ha).1 x⁻¹,
          mul_mem (mul_mem (inv_mem hx) (mem_inf.mp ha).2) (inv_mem (inv_mem hx))⟩
    rwa [show x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a by group] at h1
  have hA := hU.inf_of_le_normalizer inf_le_right hCN
  have hAeq : U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {g}) =
      U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    ext u
    simp only [mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hU.le h.1⟩⟩
  rw [hAeq] at hA
  obtain ⟨Ŝ, hŜ, hUŜ⟩ := exists_isSylowOf_ge hU.isPGroup (le_top : U ≤ ⊤)
  have hPE := hŜ.inf_of_le_normalizer (le_top :
    layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤ ⊤) (fun x _ => by
      rw [mem_normalizer_iff]
      intro e
      refine ⟨fun he => hn.conj_mem e he x, fun he => ?_⟩
      have := hn.conj_mem _ he x⁻¹
      rwa [show x⁻¹ * (x * e * x⁻¹) * x⁻¹⁻¹ = e by group] at this)
  obtain ⟨Q₀, hQ₀⟩ := hPE.exists_sylow_eq_subgroupOf
  have hgŜ : g ∈ Ŝ := hUŜ hgU
  have hgN : g ∈ normalizer ((Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :
      Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :
        Set (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact mem_inf.mpr ⟨mul_mem (mul_mem hgŜ (mem_inf.mp hk).1) (inv_mem hgŜ),
        hn.conj_mem _ (mem_inf.mp hk).2 g⟩
    · intro hk
      have hk' : k = g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ := by group
      rw [hk']
      exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hgŜ) (mem_inf.mp hk).1)
        (inv_mem (inv_mem hgŜ)), hn.conj_mem _ (mem_inf.mp hk).2 _⟩
  obtain ⟨-, h8, -, -, h5, -, -, -⟩ := hUC (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) g
    (Subgroup.isPerfect_iff.mp hL.isPerfect) hL.isL34Type (hL.isL34Unitary hg2 hd hgd)
    ⟨inf_le_right, Q₀, hQ₀⟩ hgN
  have hZP : GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≤
      Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    rw [zStarIn_eq]
    rintro _ ⟨c, hc, rfl⟩
    have hcQ := hL.center_le_pCore ⟨c, hc, rfl⟩
    rcases hL.eq_of_mem_layer_pCore hZ h2 c.2 hcQ with h | h
    · rw [Subgroup.coe_subtype, h]
      exact one_mem _
    · rw [Subgroup.coe_subtype, h]
      exact mem_inf.mpr ⟨hUŜ hβU, h ▸ c.2⟩
  have hZcard : Nat.card ↥((Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2 := by
    rw [inf_of_le_right hZP, zStarIn_eq, Subgroup.card_map_of_injective (subtype_injective _), h2]
  have hne : (Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      GrSLit.zStarIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZcard
    omega
  obtain ⟨hab, hexp⟩ := h5 hne (isCyclic_of_prime_card hZcard)
  have hle : U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      (Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓ centralizer {g} :=
    fun u hu => mem_inf.mpr ⟨mem_inf.mpr ⟨hUŜ (mem_inf.mp hu).1, (mem_inf.mp hu).2⟩,
      hU.le (mem_inf.mp hu).1⟩
  have hP8 : IsPGroup 2 ↥((Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      centralizer {g}) := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have hge : Nat.card ↥((Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓
      centralizer {g}) ≤ Nat.card ↥(U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
    rw [hA.card_eq]
    exact card_le_twoPart hP8 (fun u hu =>
      mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hu).1).2, (mem_inf.mp hu).2⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hle hge
  refine ⟨by rw [heq, h8], fun u hu v hv => hab u (heq ▸ hu) v (heq ▸ hv), fun u hu => ?_,
    fun B hB hB2 => ?_⟩
  · have := Monoid.pow_exponent_eq_one (⟨u, heq ▸ hu⟩ :
      ↥((Ŝ ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⊓ centralizer {g}))
    rw [hexp] at this
    simpa using congrArg Subtype.val this
  · calc Nat.card B ≤ twoPart (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
          centralizer {g}) := card_le_twoPart hB2 hB
      _ = Nat.card ↥(U ⊓ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := hA.card_eq.symm
      _ = 8 := by rw [heq, h8]

theorem unitary_rho_facts (hL : LLayer hs π)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} {d : Equiv.Perm (Fin 42)}
    (hd : d ∈ PSL3Four.R)
    (hgd : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = d * PSL3Four.r₄ * d⁻¹)
    {U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))} (hUg : U ≤ centralizer {g})
    (hU2 : IsPGroup 2 U) :
    (∀ u ∈ U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      ∀ v ∈ U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      hL.rho u ^ 2 = 1 → hL.rho v ^ 2 = 1 → hL.rho u = 1 ∨ hL.rho v = 1 ∨ hL.rho u = hL.rho v) ∧
      ∀ y ∈ U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))), hL.rho y ^ 2 ≠ 1 →
      ∀ u ∈ U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
        pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))),
      hL.rho u * hL.rho y = hL.rho y * hL.rho u → ∃ k : ℕ, hL.rho u = hL.rho y ^ k := by
  set B := U ⊓ (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊔
    pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) with hB
  set Θ := (B.map hL.rho).map PSL3Four.R.subtype with hΘdef
  have hΘ : Θ ≤ centralizer {d * PSL3Four.r₄ * d⁻¹} ⊓ PSL3Four.S := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      (hL.rho_mem_S_iff u).mpr (mem_inf.mp hu).2⟩
    rw [← hgd]
    have h1 : u * g = g * u := mem_centralizer_singleton_iff.mp (hUg (mem_inf.mp hu).1)
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, h1]
  have hΘ2 : IsPGroup 2 Θ := ((hU2.to_le inf_le_left).map _).map _
  obtain ⟨φ, hφ⟩ := EndB.exists_embed_quaternion hd hΘ hΘ2
  obtain ⟨-, h1, hc⟩ := EndB.facts_of_embed_quaternion φ hφ
  have hmem : ∀ u ∈ B, ((hL.rho u : PSL3Four.R) : Equiv.Perm (Fin 42)) ∈ Θ :=
    fun u hu => ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have hsq : ∀ u : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j), hL.rho u ^ 2 = 1 →
      ((hL.rho u : PSL3Four.R) : Equiv.Perm (Fin 42)) ^ 2 = 1 := fun u h => by
    simpa using congrArg Subtype.val h
  refine ⟨fun u hu v hv hu2 hv2 => ?_, fun y hy hy2 u hu huy => ?_⟩
  · rcases h1 _ (hmem u hu) _ (hmem v hv) (hsq u hu2) (hsq v hv2) with h | h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Or.inl (Subtype.ext (by simpa using h)))
    · exact Or.inr (Or.inr (Subtype.ext h))
  · have hy2' : ((hL.rho y : PSL3Four.R) : Equiv.Perm (Fin 42)) ^ 2 ≠ 1 :=
      fun h => hy2 (Subtype.ext (by simpa using h))
    obtain ⟨k, hk⟩ := hc _ (hmem y hy) hy2' _ (hmem u hu)
      (by simpa using congrArg Subtype.val huy)
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem witnesses_of_unitary
    (hUC : GrSLit.L34UnitaryCentralizerFact) (hL : LLayer hs π)
    (hZ : center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ≠ ⊥)
    (h2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) = 2)
    {g : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hg2 : g ^ 2 = 1)
    {d : Equiv.Perm (Fin 42)} (hd : d ∈ PSL3Four.R)
    (hgd : ((hL.rho g : PSL3Four.R) : Equiv.Perm (Fin 42)) = d * PSL3Four.r₄ * d⁻¹)
    {U : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hU : IsSylowOf 2 U (centralizer {g})) (hgU : g ∈ U) (htU : hs.setup.tBar i j ∈ U)
    (hβU : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈ U)
    {zb : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)} (hzU : zb ∈ U)
    (hzE : zb ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) (hz2 : zb ^ 2 = 1)
    (hzQ : zb ∉ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
    (h64 : 64 ≤ Nat.card U) :
    (∀ r ∈ U, r * zb * r⁻¹ = zb) ∧
      ((∃ a ∈ U, ∃ c ∈ U, a ^ 2 ≠ 1 ∧ c ^ 2 ≠ 1 ∧ a * c ≠ c * a) ∨
        ∃ a ∈ U, ∃ y ∈ U, ∃ k : ℕ, a ^ 2 ≠ 1 ∧ (a ^ 2) ^ 2 = 1 ∧ y ^ 2 ≠ 1 ∧ y ^ k ≠ 1 ∧
          (y ^ k) ^ 2 = 1 ∧ y ^ k ≠ a ^ 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h8, hab, h4, hmax⟩ := hL.unitary_layer_facts hUC hZ h2 hg2 hd hgd hU hgU hβU
  obtain ⟨hθ1, hθc⟩ := hL.unitary_rho_facts hd hgd hU.le hU.isPGroup
  have hEQc : ∀ e ∈ layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)), e * q = q * e := by
    intro e he q hq
    rw [← hs.centralizer_layer_eq hL.h412] at hq
    exact mem_centralizer_iff.mp hq e he
  have hβE : betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∈
      layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
    obtain ⟨b, -, hb⟩ := hL.h412.lemma46c.2.2 hZ
    rw [← hb]
    exact b.2
  have hCt : ∀ q ∈ pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      q * hs.setup.tBar i j = hs.setup.tBar i j * q →
        q = 1 ∨ q = betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
    intro q hq hqt
    have hqB : q ∈ zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hL.h412.pCore_inf_centralizer]
      exact mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqt⟩
    exact EndB.eq_one_or_eq_of_mem_zpowers_sq hs.betaBar_sq hqB
  have h16 := hL.card_le_four_mul hU.isPGroup
  exact EndB.unitary_witnesses inferInstance pCore_normal hL.rho hL.rho_eq_one_iff
    pCore_isPGroup hEQc hβE hs.betaBar_mem_pCore
    (fun y => mem_center_iff.mp (betaBar_mem_center _) y) hs.betaBar_ne_one hs.betaBar_sq
    (fun y hyE hyQ => hL.eq_of_mem_layer_pCore hZ h2 hyE hyQ) hU.le hU.isPGroup hβU htU
    hs.tBar_sq hCt hzU hzE hz2 hzQ h8 hab h4 hmax hθ1 hθc (by omega)

end EndB.LLayer

end CFSG.ComponentClassification.HarrisLit
