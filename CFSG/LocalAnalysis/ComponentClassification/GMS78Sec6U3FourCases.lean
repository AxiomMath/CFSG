module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6U3FourLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveTau
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveEpsLines
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6U3FourLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

section Transfer

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_map_conj_le' {H : Subgroup X} {x : X}
    (h : H.map (MulAut.conj x).toMonoidHom ≤ H) : x ∈ normalizer (H : Set X) :=
  mem_normalizer_iff_map_conj_eq.mpr
    (eq_of_le_of_card_ge h (by rw [card_map_of_injective (MulAut.conj x).injective]))

theorem map_subtype_le_normalizer {H : Subgroup X} {Q W : Subgroup H}
    (hQN : Q ≤ normalizer (W : Set H)) :
    Q.map H.subtype ≤ normalizer ((W.map H.subtype : Subgroup X) : Set X) := by
  rintro _ ⟨q, hq, rfl⟩
  refine mem_normalizer_of_map_conj_le' ?_
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨q * w * q⁻¹, (mem_normalizer_iff.mp (hQN hq) w).mp hw, rfl⟩

omit [Finite X] in
theorem le_centralizer_of_map_subtype {H : Subgroup X} {Q W : Subgroup H}
    (h : Q.map H.subtype ≤ centralizer ((W.map H.subtype : Subgroup X) : Set X)) :
    Q ≤ centralizer (W : Set H) := by
  intro q hq
  rw [mem_centralizer_iff]
  intro w hw
  exact Subtype.ext ((mem_centralizer_iff.mp (h ⟨q, hq, rfl⟩)) _ ⟨w, hw, rfl⟩)

end Transfer

theorem perm5_odd_inv_eq_conj : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → Equiv.Perm.sign σ ≠ 1 →
    ∃ c : Equiv.Perm (Fin 5), Equiv.Perm.sign c = 1 ∧ σ = c * Equiv.swap 0 1 * c⁻¹ := by
  decide +kernel

theorem swap01_conj_P0 : ∀ p ∈ (1 :: RankTwoAltFive.p0inv), ∃ p' ∈ (1 :: RankTwoAltFive.p0inv),
    Equiv.swap (0 : Fin 5) 1 * (p : Equiv.Perm (Fin 5)) * Equiv.swap 0 1 =
      (p' : Equiv.Perm (Fin 5)) := by
  decide +kernel

theorem swap01_conj_k2 : Equiv.swap (0 : Fin 5) 1 * (RankTwoAltFive.k2 : Equiv.Perm (Fin 5)) *
    Equiv.swap 0 1 ≠ (RankTwoAltFive.k2 : Equiv.Perm (Fin 5)) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

omit [Finite G] in
theorem gmsV_le_centralizer_K {K : Subgroup G} (hKL : K ≤ L)
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    gmsV L T ≤ centralizer (K : Set G) :=
  sup_le (gmsA_le_centralizer_K hKH) (T₀_le_centralizer_K hKL)

omit [Finite G] in
theorem oddQuotImageC_gmsV {K : Subgroup G} (hKL : K ≤ L)
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    oddQuotImageC K (gmsV L T) =
      oddQuotImageC K (gmsA L T) ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) := by
  rw [oddQuotImageC, oddQuotImageC, oddQuotImageC, gmsV,
    subgroupOf_sup (gmsA_le_centralizer_K hKH) (T₀_le_centralizer_K hKL), Subgroup.map_sup]

theorem mem_centralizer_of_mem_normalizer_gmsV_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {y : G} (hy : IsPGroup 2 (zpowers y)) (hyN : y ∈ normalizer (gmsV L T : Set G))
    (hyK : y ∈ centralizer (K : Set G)) : y ∈ centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have h1 := rightConjugate_T₁_eq h3 hF le_rfl e hKL hKo hKH hyN
  have hyT : y ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    have := (rightConjugate_eq_self_iff _ _).mp h1
    simpa using inv_mem this
  exact mem_centralizer_of_isPGroup_four h3 e hKL hKo hKH hy hyT hyK

omit [Finite G] in
theorem isPGroup_of_sq_eq_one' {H : Subgroup G} (h : ∀ x ∈ H, x ^ 2 = 1) : IsPGroup 2 H :=
  fun x => ⟨1, Subtype.ext (by simpa using h x x.2)⟩

theorem mem_normalizer_gmsV_of_mem_normalizer_subgroupOf {K : Subgroup G} (hKL : K ≤ L)
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {y : centralizer (K : Set G)}
    (hy : y ∈ normalizer (((gmsV L T).subgroupOf (centralizer (K : Set G)) :
      Subgroup (centralizer (K : Set G))) : Set (centralizer (K : Set G)))) :
    (y : G) ∈ normalizer (gmsV L T : Set G) := by
  have hVG₁ := gmsV_le_centralizer_K hKL hKH
  refine mem_normalizer_of_map_conj_le' ?_
  rintro _ ⟨v, hv, rfl⟩
  have hv' : (⟨v, hVG₁ hv⟩ : centralizer (K : Set G)) ∈ (gmsV L T).subgroupOf _ := hv
  exact (mem_normalizer_iff.mp hy _).mp hv'

theorem le_centralizer_gmsA_of_le_normalizer_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {Q : Subgroup (u3G₁Bar K)} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (oddQuotImageC K (gmsV L T) : Set (u3G₁Bar K))) :
    Q ≤ centralizer (oddQuotImageC K (gmsA L T) : Set (u3G₁Bar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := centralizer (K : Set G) with hG₁
  set π := QuotientGroup.mk' (standardComponentOddCore ↥G₁) with hπ
  set V' : Subgroup G₁ := (gmsV L T).subgroupOf G₁ with hV'
  have hVel := ((h3.facts_of_psu3 hF le_rfl e).vFacts h3 hF).2.1
  have hV2 : IsPGroup 2 V' := (isPGroup_of_sq_eq_one' hVel.2).comap_subtype
  have hS2 : IsPGroup 2 (Q ⊔ V'.map π : Subgroup (u3G₁Bar K)) :=
    IsPGroup.to_sup_of_normal_right' hQ (hV2.map π) hQN
  obtain ⟨S, -, hS, hSmap, hSN⟩ :=
    exists_isPGroup_le_normalizer hV2 hS2 le_sup_right (sup_le hQN le_normalizer)
  have hyA : ∀ y ∈ S, ∀ a : G₁, (a : G) ∈ gmsA L T → y * a = a * y := by
    intro y hy a ha
    have hyN := mem_normalizer_gmsV_of_mem_normalizer_subgroupOf hKL hKH (hSN hy)
    have hy2 : IsPGroup 2 (zpowers (y : G)) := by
      have h1 : IsPGroup 2 (zpowers y) := hS.to_le (zpowers_le.mpr hy)
      have h2 := h1.map G₁.subtype
      rwa [MonoidHom.map_zpowers] at h2
    have hyC := mem_centralizer_of_mem_normalizer_gmsV_four h3 hF e hKL hKo hKH hy2 hyN y.2
    exact Subtype.ext ((mem_centralizer_iff.mp hyC) (a : G) (mem_inf.mp ha).1).symm
  intro q hq
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have hqS : q ∈ S.map π := hSmap ▸ mem_sup_left hq
  obtain ⟨y, hy, rfl⟩ := hqS
  rw [← map_mul, ← map_mul, hyA y hy a ha]

theorem le_centralizer_gmsA_of_le_normalizer_normalizer_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {P S : Subgroup (u3G₁Bar K)} (hVP : oddQuotImageC K (gmsV L T) ≤ P) (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (oddQuotImageC K (gmsV L T) : Set (u3G₁Bar K))) (hPS : P ≤ S)
    (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (P : Set (u3G₁Bar K))) :
    S ≤ centralizer (oddQuotImageC K (gmsA L T) : Set (u3G₁Bar K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G₁ := centralizer (K : Set G) with hG₁
  set π := QuotientGroup.mk' (standardComponentOddCore ↥G₁) with hπ
  set V' : Subgroup G₁ := (gmsV L T).subgroupOf G₁ with hV'
  have hVG₁ : gmsV L T ≤ G₁ := gmsV_le_centralizer_K hKL hKH
  have hVel := ((h3.facts_of_psu3 hF le_rfl e).vFacts h3 hF).2.1
  have hV2 : IsPGroup 2 V' := (isPGroup_of_sq_eq_one' hVel.2).comap_subtype
  obtain ⟨Ph, hVPh, hPh, hPhmap, hPhN⟩ := exists_isPGroup_le_normalizer hV2 hP hVP hPN
  obtain ⟨Sh, hPSh, hSh, hShmap, hShN⟩ := exists_isPGroup_le_normalizer hPh hS
    (hPhmap ▸ hPS) (hPhmap ▸ hSN)
  set W := Ph.map G₁.subtype with hW
  have hVW : gmsV L T ≤ W := by
    intro v hv
    exact ⟨⟨v, hVG₁ hv⟩, hVPh hv, rfl⟩
  have h2el : ∀ {X : Subgroup G₁}, IsPGroup 2 X → ∀ y ∈ X, IsPGroup 2 (zpowers (y : G)) := by
    intro X hX y hy
    have h1 : IsPGroup 2 (zpowers y) := hX.to_le (zpowers_le.mpr hy)
    have h2 := h1.map G₁.subtype
    rwa [MonoidHom.map_zpowers] at h2
  have hWT : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_centralizer_of_mem_normalizer_gmsV_four h3 hF e hKL hKo hKH (h2el hPh p hp)
      (mem_normalizer_gmsV_of_mem_normalizer_subgroupOf hKL hKH (hPhN hp)) p.2
  have hyA : ∀ y ∈ Sh, ∀ a : G₁, (a : G) ∈ gmsA L T → y * a = a * y := by
    intro y hy a ha
    have hyW : (y : G) ∈ normalizer (W : Set G) := by
      refine mem_normalizer_of_map_conj_le' ?_
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨y * p * y⁻¹, (mem_normalizer_iff.mp (hShN hy) p).mp hp, rfl⟩
    have hyK : (y : G) ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ y.2
    have hyT := mem_normalizer_T₁_of_mem_normalizer h3 hF le_rfl e hKL hKo hKH hVW hWT hyW hyK
    have hyC := mem_centralizer_of_isPGroup_four h3 e hKL hKo hKH (h2el hSh y hy) hyT y.2
    exact Subtype.ext ((mem_centralizer_iff.mp hyC) (a : G) (mem_inf.mp ha).1).symm
  intro q hq
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨y, hy, rfl⟩ : q ∈ Sh.map π := hShmap ▸ hq
  rw [← map_mul, ← map_mul, hyA y hy a ha]

omit [Finite G] in
theorem oddQuotImageC_T₀_le_centralizer {K : Subgroup G} :
    oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ u3X₀CentralizerC L K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hyL : (y : G) ∈ L := (inf_le_left : L ⊓ centralizer (K : Set G) ≤ L)
    ((commutator_le.mpr fun a ha b hb => ?_) (mem_subgroupOf.mp hy))
  · exact (mem_centralizer_iff.mp (mem_inf.mp (mem_subgroupOf.mp hx)).2 (y : G) hyL)
  · exact mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (mem_inf.mp ha).1 (mem_inf.mp hb).1)
      (inv_mem (mem_inf.mp ha).1)) (inv_mem (mem_inf.mp hb).1),
      mul_mem (mul_mem (mul_mem (mem_inf.mp ha).2 (mem_inf.mp hb).2)
      (inv_mem (mem_inf.mp ha).2)) (inv_mem (mem_inf.mp hb).2)⟩

theorem exists_conj_eq_gmsA_four (h3 : Sec3 G L T) (e : rankTwoQuot L ≃* PSU3 2 2)
    {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {V₀ : Subgroup (u3G₁Bar K)} (hV₀ : IsSylowOf 2 V₀ (oddQuotImageC K (u3X₀ L K))) :
    ∃ c : MulAut (u3G₁Bar K), V₀.map c.toMonoidHom = oddQuotImageC K (gmsA L T) ∧
      (V₀ ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G))).map c.toMonoidHom =
        oddQuotImageC K (gmsV L T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := isSylowOf_oddQuotImageC_four h3 e hKL hKo hKH
  obtain ⟨w, hwX, hw⟩ := hsyl.exists_mem_conj hV₀
  have hcV₀ : V₀.map (MulAut.conj w⁻¹).toMonoidHom = oddQuotImageC K (gmsA L T) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hw x).mp hx
      simpa [MulAut.conj_apply] using this
    · intro hy
      refine ⟨w * y * w⁻¹, (hw _).mpr (by simpa [mul_assoc] using hy), ?_⟩
      simp [mul_assoc]
  have hcT₀ : (oddQuotImageC K (T ⊓ centralizer (L : Set G))).map (MulAut.conj w⁻¹).toMonoidHom =
      oddQuotImageC K (T ⊓ centralizer (L : Set G)) := by
    have hfix : ∀ t ∈ oddQuotImageC K (T ⊓ centralizer (L : Set G)), w⁻¹ * t * w = t := by
      intro t ht
      have hc := (mem_centralizer_iff.mp (oddQuotImageC_T₀_le_centralizer ht)) w hwX
      calc w⁻¹ * t * w = w⁻¹ * (w * t) := by rw [hc]; group
        _ = t := by group
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : (MulAut.conj w⁻¹).toMonoidHom x = x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact hfix x hx
      rw [h1]
      exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hfix y hy
  refine ⟨MulAut.conj w⁻¹, hcV₀, ?_⟩
  rw [Subgroup.map_sup, hcV₀, hcT₀, oddQuotImageC_gmsV hKL hKH]

theorem le_centralizer_of_le_normalizer_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {V₀ : Subgroup (u3G₁Bar K)} (hV₀ : IsSylowOf 2 V₀ (oddQuotImageC K (u3X₀ L K)))
    {Q : Subgroup (u3G₁Bar K)} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer ((V₀ ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) :
      Subgroup (u3G₁Bar K)) : Set (u3G₁Bar K))) :
    Q ≤ centralizer (V₀ : Set (u3G₁Bar K)) := by
  obtain ⟨c, hcV₀, hcV⟩ := exists_conj_eq_gmsA_four h3 e hKL hKo hKH hV₀
  have h1 : Q.map c.toMonoidHom ≤ normalizer (oddQuotImageC K (gmsV L T) : Set (u3G₁Bar K)) := by
    rw [← hcV, ← map_equiv_normalizer_eq]
    exact Subgroup.map_mono hQN
  have h2 := le_centralizer_gmsA_of_le_normalizer_four h3 hF e hKL hKo hKH (hQ.map _) h1
  rw [← hcV₀, centralizer_map_mulEquiv] at h2
  exact (map_le_map_iff_of_injective c.injective).mp h2

theorem le_centralizer_of_le_normalizer_normalizer_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {V₀ : Subgroup (u3G₁Bar K)} (hV₀ : IsSylowOf 2 V₀ (oddQuotImageC K (u3X₀ L K)))
    {P S : Subgroup (u3G₁Bar K)}
    (hVP : V₀ ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ P) (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer ((V₀ ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) :
      Subgroup (u3G₁Bar K)) : Set (u3G₁Bar K)))
    (hPS : P ≤ S) (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (P : Set (u3G₁Bar K))) :
    S ≤ centralizer (V₀ : Set (u3G₁Bar K)) := by
  obtain ⟨c, hcV₀, hcV⟩ := exists_conj_eq_gmsA_four h3 e hKL hKo hKH hV₀
  have hVP' : oddQuotImageC K (gmsV L T) ≤ P.map c.toMonoidHom := hcV ▸ Subgroup.map_mono hVP
  have hPN' : P.map c.toMonoidHom ≤
      normalizer (oddQuotImageC K (gmsV L T) : Set (u3G₁Bar K)) := by
    rw [← hcV, ← map_equiv_normalizer_eq]
    exact Subgroup.map_mono hPN
  have hSN' : S.map c.toMonoidHom ≤ normalizer ((P.map c.toMonoidHom : Subgroup _) :
      Set (u3G₁Bar K)) := by
    rw [← map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSN
  have h2 := le_centralizer_gmsA_of_le_normalizer_normalizer_four h3 hF e hKL hKo hKH hVP'
    (hP.map _) hPN' (Subgroup.map_mono hPS) (hS.map _) hSN'
  rw [← hcV₀, centralizer_map_mulEquiv] at h2
  exact (map_le_map_iff_of_injective c.injective).mp h2

theorem le_centralizer_subgroupOf_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {H : Subgroup (u3G₁Bar K)} (hXH : oddQuotImageC K (u3X₀ L K) ≤ H)
    (hTH : oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ H) {W₀ : Subgroup H}
    (hW₀ : IsSylowOf 2 W₀ ((oddQuotImageC K (u3X₀ L K)).subgroupOf H))
    {Q : Subgroup H} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H ⊔ W₀ :
      Subgroup H) : Set H)) :
    Q ≤ centralizer (W₀ : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW₀' : IsSylowOf 2 (W₀.map H.subtype) (oddQuotImageC K (u3X₀ L K)) := by
    have h1 := (isSylowOf_map_subtype_iff H).mpr hW₀
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hXH] at h1
  have hmap : ((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H ⊔ W₀).map H.subtype =
      W₀.map H.subtype ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hTH, sup_comm]
  have hQN' := map_subtype_le_normalizer hQN
  rw [hmap] at hQN'
  exact le_centralizer_of_map_subtype
    (le_centralizer_of_le_normalizer_four h3 hF e hKL hKo hKH hW₀' (hQ.map _) hQN')

theorem le_centralizer_subgroupOf_normalizer_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {H : Subgroup (u3G₁Bar K)} (hXH : oddQuotImageC K (u3X₀ L K) ≤ H)
    (hTH : oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ H) {W₀ : Subgroup H}
    (hW₀ : IsSylowOf 2 W₀ ((oddQuotImageC K (u3X₀ L K)).subgroupOf H)) {P S : Subgroup H}
    (hVP : (oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H ⊔ W₀ ≤ P)
    (hP : IsPGroup 2 P)
    (hPN : P ≤ normalizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H ⊔ W₀ :
      Subgroup H) : Set H))
    (hPS : P ≤ S) (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (P : Set H)) :
    S ≤ centralizer (W₀ : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW₀' : IsSylowOf 2 (W₀.map H.subtype) (oddQuotImageC K (u3X₀ L K)) := by
    have h1 := (isSylowOf_map_subtype_iff H).mpr hW₀
    rwa [subgroupOf_map_subtype, inf_eq_left.mpr hXH] at h1
  have hmap : ((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H ⊔ W₀).map H.subtype =
      W₀.map H.subtype ⊔ oddQuotImageC K (T ⊓ centralizer (L : Set G)) := by
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr hTH, sup_comm]
  have hVP' := Subgroup.map_mono (f := H.subtype) hVP
  rw [hmap] at hVP'
  have hPN' := map_subtype_le_normalizer hPN
  rw [hmap] at hPN'
  exact le_centralizer_of_map_subtype
    (le_centralizer_of_le_normalizer_normalizer_four h3 hF e hKL hKo hKH hW₀' hVP' (hP.map _)
      hPN' (Subgroup.map_mono hPS) (hS.map _) (map_subtype_le_normalizer hSN))

theorem false_of_setting310_IIa_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    (hGold : Asc76X.GoldschmidtTheoremA) {H : Subgroup (u3G₁Bar K)}
    (hXH : oddQuotImageC K (u3X₀ L K) ≤ H) (hTH : oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ H)
    {g : H} {T' V₀ : Subgroup H}
    (hset : RankTwoAltFive.Setting310 ((oddQuotImageC K (u3X₀ L K)).subgroupOf H)
      ((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H) g T' V₀)
    (hIIa : ¬ centralizer (((oddQuotImageC K (u3X₀ L K)).subgroupOf H : Subgroup H) : Set H) ⊓
      normalizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H : Subgroup H) :
        Set H) ≤
      centralizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H : Subgroup H) :
        Set H)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (oddQuotImageC K (u3X₀ L K)).subgroupOf H with hAdef
  set R := (oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H with hRdef
  obtain ⟨y, hy, hyC⟩ := IsConcreteLE.not_le_iff_exists.mp hIIa
  obtain ⟨hyK, hyN⟩ := mem_inf.mp hy
  have hX := RankTwoAltFive.rankTwoX_eq_top_of_IIa hset.sylowR hset.elemR hset.cardR
    hset.sup_top hyK hyN hyC
  have hA31 : AS76b.Hyp31 A := by
    obtain ⟨eA⟩ := hset.equiv
    have hZ : center ↥A = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : eA x ∈ center RankTwoAltFive.A5 := mem_center_iff.mpr fun y => by
        obtain ⟨y', rfl⟩ := eA.surjective y
        rw [← map_mul, ← map_mul, mem_center_iff.mp hx y']
      rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
      exact mem_bot.mpr (eA.injective (h1.trans (map_one eA).symm))
    exact ⟨hset.hyp.standard, RankTwoClassical.hypIIAlt5 ↥A hset.hyp.standard.1.1
      ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eA)⟩,
      hset.oddCore, by have := hset.hyp.rank; omega, hset.hyp.not_normal⟩
  obtain ⟨hXF, hXs⟩ := AS76b.asc08Lemma34 H A hA31
  have hGs : IsSimpleGroup H := by
    have h1 : IsSimpleGroup ↥(⊤ : Subgroup H) := by
      rw [← hX]
      show IsSimpleGroup ↥(normalClosure (A : Set H))
      rw [hXF]
      exact hXs
    exact MulEquiv.isSimpleGroup Subgroup.topEquiv.symm
  obtain ⟨P, hP, hVP, hPC, hP64⟩ := hset.exists_sylow_transv
  obtain ⟨V', hV'P, hV'e, hV'16, hinf, hsup, hV'inv, -⟩ :=
    hset.exists_Vprime hP hPC hIIa hP64 hVP
  have hW₀ : IsSylowOf 2 V₀ A := hset.loc.sylowV₀
  have hPN : P ≤ normalizer ((R ⊔ T' : Subgroup H) : Set H) := fun p hp => (hP.le hp).1
  have hRV : R ⊔ V₀ = R ⊔ T' := hset.sup_R_V₀
  have hPN' : P ≤ normalizer ((R ⊔ V₀ : Subgroup H) : Set H) := by rw [hRV]; exact hPN
  have hε : RankTwoAltFive.EpsOne (R ⊔ T') P := by
    obtain ⟨Q, hQ, hPQ⟩ := AS76b.exists_isSylowOf_le hPN hP.isPGroup
    have hQN : Q ≤ normalizer ((R ⊔ V₀ : Subgroup H) : Set H) := by rw [hRV]; exact hQ.le
    have hQC : Q ≤ centralizer (V₀ : Set H) :=
      le_centralizer_subgroupOf_four h3 hF e hKL hKo hKH hXH hTH hW₀ hQ.isPGroup hQN
    have hQtr : Q ≤ RankTwoAltFive.transvGroup (R ⊔ T') V₀ := by
      intro n hn
      obtain ⟨p, hp, hnp⟩ := hset.exists_mul_mem_normalizer_R hP hPC hP64 (hQ.le hn)
      have hnpQ : n * p ∈ Q := mul_mem hn (hPQ hp)
      have hnpC : n * p ∈ centralizer ((R ⊔ T' : Subgroup H) : Set H) :=
        hset.mem_centralizer_of_mem_centralizer_V₀ (hQ.le hnpQ) hnp
          (hQ.isPGroup.to_le (zpowers_le.mpr hnpQ)) (hQC hnpQ)
      have e1 : n = (n * p) * p⁻¹ := by group
      rw [e1]
      exact mul_mem (hset.centralizer_le_transvGroup hnpC) (inv_mem (hP.le hp))
    have hQP : Q = P := hP.eq_of_le hPQ hQtr hQ.isPGroup
    exact hQP ▸ hQ
  obtain ⟨S, hPS⟩ := hP.isPGroup.exists_le_sylow
  obtain ⟨hSN, -⟩ := hset.sylow_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16
    hinf hsup hV'inv S hPS
  have hτ : ∀ s ∈ (S : Subgroup H), ∀ w ∈ V₀, s * w = w * s := by
    have h1 := le_centralizer_subgroupOf_normalizer_four h3 hF e hKL hKo hKH hXH hTH hW₀
      (hRV ▸ hVP) hP.isPGroup hPN' hPS S.isPGroup' hSN
    intro s hs w hw
    exact ((mem_centralizer_iff.mp (h1 hs)) w hw).symm
  exact hset.false_of_tauType hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf hsup
    hV'inv S hPS hτ

theorem false_of_setting310_IIb_four
    (h3 : Sec3 G L T) (hF : Foundation)
    (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    (hIIb : RankTwoAltFive.Asc310IIb) {H : Subgroup (u3G₁Bar K)}
    (hXH : oddQuotImageC K (u3X₀ L K) ≤ H) (hTH : oddQuotImageC K (T ⊓ centralizer (L : Set G)) ≤ H)
    {g : H} {T' V₀ : Subgroup H}
    (hset : RankTwoAltFive.Setting310 ((oddQuotImageC K (u3X₀ L K)).subgroupOf H)
      ((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H) g T' V₀)
    (hb : centralizer (((oddQuotImageC K (u3X₀ L K)).subgroupOf H : Subgroup H) : Set H) ⊓
      normalizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H : Subgroup H) :
        Set H) ≤
      centralizer (((oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H : Subgroup H) :
        Set H)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := (oddQuotImageC K (u3X₀ L K)).subgroupOf H with hAdef
  set R := (oddQuotImageC K (T ⊓ centralizer (L : Set G))).subgroupOf H with hRdef
  obtain ⟨-, t, ht2, htA, htR, htout⟩ := hIIb H A R g T' V₀ hset hb
  obtain ⟨eA⟩ := hset.equiv
  set σ := RankTwoAltFive.autPerm eA ⟨t, htA⟩ with hσdef
  have hσ2 : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have h1 : (⟨t, htA⟩ : normalizer (A : Set H)) * ⟨t, htA⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq]; exact ht2)
    rw [h1, map_one]
  have hσodd : Equiv.Perm.sign σ ≠ 1 := by
    intro hsign
    apply htout
    set b : ↥A := eA.symm ⟨σ, (Equiv.Perm.mem_alternatingGroup).mpr hsign⟩ with hbdef
    have hbN : (b : H) ∈ normalizer (A : Set H) := le_normalizer b.2
    have hb1 : RankTwoAltFive.autPerm eA ⟨(b : H), hbN⟩ = σ := by
      rw [RankTwoAltFive.autPerm_of_mem eA b.2]
      have : eA ⟨(b : H), b.2⟩ = ⟨σ, (Equiv.Perm.mem_alternatingGroup).mpr hsign⟩ := by
        rw [hbdef]
        exact eA.apply_symm_apply _
      rw [this]
    have h1 : RankTwoAltFive.autPerm eA (⟨t, htA⟩ * (⟨(b : H), hbN⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv, hb1, ← hσdef, mul_inv_cancel]
    have h2 := (RankTwoAltFive.autPerm_eq_one_iff eA _).mp h1
    refine ⟨(b : H), b.2, fun y hy => ?_⟩
    have hy' : (b : H) * y * (b : H)⁻¹ ∈ A :=
      mul_mem (mul_mem b.2 hy) (inv_mem b.2)
    have hc := (mem_centralizer_iff.mp h2) _ hy'
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    calc t * y * t⁻¹ = (b : H) * y * (b : H)⁻¹ * (t * (b : H)⁻¹) * (b : H) * t⁻¹ := by
          rw [hc]; group
      _ = (b : H) * y * (b : H)⁻¹ := by group
  obtain ⟨c, hc, hσc⟩ := perm5_odd_inv_eq_conj σ hσ2 hσodd
  set c' : RankTwoAltFive.A5 := ⟨c, (Equiv.Perm.mem_alternatingGroup).mpr hc⟩ with hc'def
  set W₀ : Subgroup H :=
    ((RankTwoAltFive.P0.map (MulAut.conj c').toMonoidHom).map eA.symm.toMonoidHom).map
      A.subtype with hW₀def
  have hW₀mem : ∀ w : H, w ∈ W₀ ↔ ∃ p ∈ RankTwoAltFive.P0,
      ((eA.symm (c' * p * c'⁻¹) : ↥A) : H) = w := by
    intro w
    simp only [hW₀def, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨_, ⟨_, ⟨p, hp, rfl⟩, rfl⟩, rfl⟩
  have hW₀A : W₀ ≤ A := by
    intro w hw
    obtain ⟨p, -, rfl⟩ := (hW₀mem w).mp hw
    exact (eA.symm _).2
  have hconj : ∀ p p' : RankTwoAltFive.A5, Equiv.swap (0 : Fin 5) 1 * (p : Equiv.Perm (Fin 5)) *
      Equiv.swap 0 1 = (p' : Equiv.Perm (Fin 5)) →
      t * ((eA.symm (c' * p * c'⁻¹) : ↥A) : H) * t⁻¹ = ((eA.symm (c' * p' * c'⁻¹) : ↥A) : H) := by
    intro p p' hpp'
    set a := eA.symm (c' * p * c'⁻¹) with hadef
    have hspec := RankTwoAltFive.autPerm_spec eA ⟨t, htA⟩ (a : H) a.2
    have hea : eA ⟨(a : H), a.2⟩ = c' * p * c'⁻¹ := by rw [hadef]; exact eA.apply_symm_apply _
    rw [hea, ← hσdef, hσc] at hspec
    have h2 : eA ⟨t * a * t⁻¹, (mem_normalizer_iff.mp htA _).mp a.2⟩ = c' * p' * c'⁻¹ := by
      apply Subtype.ext
      rw [hspec]
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, hc'def]
      calc c * Equiv.swap 0 1 * c⁻¹ * (c * (p : Equiv.Perm (Fin 5)) * c⁻¹) *
            (c * Equiv.swap 0 1 * c⁻¹)⁻¹
          = c * (Equiv.swap 0 1 * (p : Equiv.Perm (Fin 5)) * (Equiv.swap (0 : Fin 5) 1)⁻¹) *
            c⁻¹ := by group
        _ = c * (p' : Equiv.Perm (Fin 5)) * c⁻¹ := by rw [Equiv.swap_inv, hpp']
    have h3 : (⟨t * a * t⁻¹, (mem_normalizer_iff.mp htA _).mp a.2⟩ : ↥A) =
        eA.symm (c' * p' * c'⁻¹) := by
      rw [← h2, eA.symm_apply_apply]
    exact congrArg Subtype.val h3
  have hP0 : ∀ p ∈ RankTwoAltFive.P0, ∃ p' ∈ RankTwoAltFive.P0,
      Equiv.swap (0 : Fin 5) 1 * (p : Equiv.Perm (Fin 5)) * Equiv.swap 0 1 =
        (p' : Equiv.Perm (Fin 5)) := by
    intro p hp
    obtain ⟨p', hp', h⟩ := swap01_conj_P0 p (RankTwoAltFive.mem_P0.mp hp)
    exact ⟨p', RankTwoAltFive.mem_P0.mpr hp', h⟩
  have htW₀ : t ∈ normalizer (W₀ : Set H) := by
    refine mem_normalizer_of_map_conj_le' ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨p, hp, rfl⟩ := (hW₀mem w).mp hw
    obtain ⟨p', hp', hpp'⟩ := hP0 p hp
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj p p' hpp']
    exact (hW₀mem _).mpr ⟨p', hp', rfl⟩
  have hk2 : RankTwoAltFive.k2 ∈ RankTwoAltFive.P0 := RankTwoAltFive.mem_P0.mpr (by decide)
  have htC : ¬ t ∈ centralizer (W₀ : Set H) := by
    intro htC
    obtain ⟨p', -, hpp'⟩ := hP0 _ hk2
    have hw : ((eA.symm (c' * RankTwoAltFive.k2 * c'⁻¹) : ↥A) : H) ∈ W₀ :=
      (hW₀mem _).mpr ⟨_, hk2, rfl⟩
    have h1 := (mem_centralizer_iff.mp htC) _ hw
    have h2 : t * ((eA.symm (c' * RankTwoAltFive.k2 * c'⁻¹) : ↥A) : H) * t⁻¹ =
        ((eA.symm (c' * RankTwoAltFive.k2 * c'⁻¹) : ↥A) : H) := by
      rw [← h1]; group
    rw [hconj _ p' hpp'] at h2
    have h3 := eA.symm.injective (Subtype.ext h2)
    have h4 : p' = RankTwoAltFive.k2 := by
      have := congrArg (fun x => c'⁻¹ * x * c') h3
      simpa [mul_assoc] using this
    exact swap01_conj_k2 (hpp'.trans (congrArg Subtype.val h4))
  have hW₀c : Nat.card W₀ = 4 := by
    rw [hW₀def, card_map_of_injective A.subtype_injective,
      card_map_of_injective eA.symm.injective,
      card_map_of_injective (MulAut.conj c').injective, RankTwoAltFive.card_P0]
  have hAc : Nat.card A = 60 := by
    rw [Nat.card_congr eA.toEquiv, RankTwoAltFive.card_A5]
  have hW₀syl : IsSylowOf 2 W₀ A := by
    refine isSylowOf_of_card hW₀A ?_
    rw [hW₀c, hAc, show (60 : ℕ) = Nat.card RankTwoAltFive.A5 from
      RankTwoAltFive.card_A5.symm, RankTwoAltFive.fact_A5]
    rfl
  have hR2 : IsPGroup 2 R := hset.sylowR.isPGroup
  have hRW : R ≤ normalizer (W₀ : Set H) := fun r hr =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hW₀A (hset.sylowR.le hr))
  have hRW2 : IsPGroup 2 (R ⊔ W₀ : Subgroup H) :=
    IsPGroup.to_sup_of_normal_right' hR2 (hW₀syl.isPGroup) hRW
  have htRW : t ∈ normalizer ((R ⊔ W₀ : Subgroup H) : Set H) := by
    refine mem_normalizer_of_map_conj_le' ?_
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨r, hr, rfl⟩
      exact (mem_normalizer_iff.mp htR r).mp hr
    · rintro _ ⟨w, hw, rfl⟩
      exact (mem_normalizer_iff.mp htW₀ w).mp hw
  have ht2' : IsPGroup 2 (zpowers t) := isPGroup_zpowers_of_sq_eq_one ht2
  have hQ2 : IsPGroup 2 (zpowers t ⊔ (R ⊔ W₀) : Subgroup H) :=
    IsPGroup.to_sup_of_normal_right' ht2' hRW2 (zpowers_le.mpr htRW)
  have hQN : zpowers t ⊔ (R ⊔ W₀) ≤ normalizer ((R ⊔ W₀ : Subgroup H) : Set H) :=
    sup_le (zpowers_le.mpr htRW) le_normalizer
  have hQC := le_centralizer_subgroupOf_four h3 hF e hKL hKo hKH hXH hTH hW₀syl hQ2 hQN
  exact htC (hQC (mem_sup_left (mem_zpowers t)))

end Sec3

end CFSG.ComponentClassification.GMS78
