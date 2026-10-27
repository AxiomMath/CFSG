module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldStrong
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldPSL3
public import CFSG.GH74.KGroups.L3EpsLin
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open scoped commutatorElement Pointwise

@[expose] def L34FieldHost : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (P W : Subgroup G), L34FieldNormalSetting G t P →
    Odd (Nat.card W) → W ≠ ⊥ → normalizer (P : Set G) ≤ normalizer (W : Set G) →
    ∃ (Y : Subgroup G) (k : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (φ : ↥Y →* (Fin k → projectiveSL 3 F)),
      Y ≤ normalizer (W : Set G) ∧ (Y.subgroupOf (normalizer (W : Set G))).Normal ∧
      oddIn (normalizer (W : Set G)) ≤ Y ∧ Function.Surjective φ ∧
      φ.ker = (oddIn (normalizer (W : Set G))).subgroupOf Y ∧ 1 ≤ k ∧ 16 ≤ Nat.card F ∧
      (k = 1 → Nat.card F = 16 → ∀ y ∈ Y, t * y * t⁻¹ * y⁻¹ ∈ oddIn (normalizer (W : Set G)))

theorem l34FieldNormalUTSection_of_host (h : L34FieldHost) : L34FieldNormalUTSection := by
  intro G _ _ t P W hset hWodd hW1 hPW hWE
  obtain ⟨Y, k, F, _, _, _, φ, hYM, hYn, hOY, hφs, hφk, hk1, hF16, hbd⟩ :=
    h G t P W hset hWodd hW1 hPW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (W : Set G) with hM
  set O := oddIn M with hO
  have hGW : GWTwoBalanced G :=
    gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hset.1.2.2.2.2.2.1
  have ht2 : t * t = 1 := by rw [← pow_two, ← hset.2.1, pow_orderOf_eq_one]
  have htM : t ∈ M := by
    have hCP : centralizer ({t} : Set G) ≤ normalizer (P : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hset.2.2.1).mp hset.2.2.2.2.1
    exact hPW (hCP (mem_centralizer_singleton_iff.mpr rfl))
  obtain ⟨S, hSyl, htS⟩ : ∃ S : Subgroup G, IsSylowTwoIn S M ∧ t ∈ S := by
    have hz : IsPGroup 2 ↥(zpowers (⟨t, htM⟩ : ↥M)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hset.2.1, pow_one]
    obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
    refine ⟨(Q : Subgroup ↥M).map M.subtype, ⟨map_subtype_le _, Q, ?_⟩,
      ⟨⟨t, htM⟩, hQ (mem_zpowers _), rfl⟩⟩
    exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm
  have hS2 : IsPGroup 2 S := hSyl.isPGroup
  have hOodd : Nat.Coprime 2 (Nat.card O) := by
    rw [hO, oddIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  have hSO : ∀ x ∈ S, x ∈ O → x = 1 := by
    intro x hxS hxO
    obtain ⟨n, hn⟩ := hS2 ⟨x, hxS⟩
    have h1 : orderOf x ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hn
    have h2 : orderOf x ∣ Nat.card O := O.orderOf_dvd_natCard hxO
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left n hOodd) h1 h2)
  have hYN : M ≤ normalizer (Y : Set G) := (normal_subgroupOf_iff_le_normalizer hYM).mp hYn
  obtain ⟨R, hR⟩ :=
    UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hSyl.1 hSyl.2 hYM hYN
  have hRY : (R : Subgroup ↥Y).map Y.subtype = S ⊓ Y := by
    rw [hR, subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hinj : ∀ y : ↥Y, (y : G) ∈ S → φ y = 1 → y = 1 := by
    intro y hyS hy
    have hk : y ∈ φ.ker := hy
    rw [hφk, mem_subgroupOf] at hk
    exact Subtype.ext (hSO _ hyS hk)
  have hmemR : ∀ x (hx : x ∈ S ⊓ Y), (⟨x, (mem_inf.mp hx).2⟩ : ↥Y) ∈ (R : Subgroup ↥Y) := by
    intro x hx
    rw [hR, mem_subgroupOf]
    exact hx
  have hRS : ∀ r ∈ (R : Subgroup ↥Y), (r : G) ∈ S := by
    intro r hr
    rw [hR, mem_subgroupOf] at hr
    exact (mem_inf.mp hr).1
  set V : Sylow 2 (Fin k → projectiveSL 3 F) := R.mapSurjective hφs with hV
  have hVcoe : (V : Subgroup (Fin k → projectiveSL 3 F)) = (R : Subgroup ↥Y).map φ :=
    Sylow.coe_mapSurjective hφs R
  have hV2 : IsPGroup 2 ↥(V : Subgroup (Fin k → projectiveSL 3 F)) := V.isPGroup'
  have hφR : ∀ r ∈ (R : Subgroup ↥Y), φ r ∈ (V : Subgroup (Fin k → projectiveSL 3 F)) := by
    intro r hr
    rw [hVcoe]
    exact ⟨r, hr, rfl⟩
  have hcl3 : ∀ a ∈ S ⊓ Y, ∀ b ∈ S ⊓ Y, ∀ c ∈ S ⊓ Y, ⁅⁅a, b⁆, c⁆ = 1 := by
    intro a ha b hb c hc
    set a' : ↥Y := ⟨a, (mem_inf.mp ha).2⟩ with ha'
    set b' : ↥Y := ⟨b, (mem_inf.mp hb).2⟩ with hb'
    set c' : ↥Y := ⟨c, (mem_inf.mp hc).2⟩ with hc'
    have hφ := commutator_commutator_eq_one_of_isPGroup_pi hV2 _ (hφR a' (hmemR a ha)) _
      (hφR b' (hmemR b hb)) _ (hφR c' (hmemR c hc))
    rw [← map_commutatorElement, ← map_commutatorElement] at hφ
    have hmem : ((⁅⁅a', b'⁆, c'⁆ : ↥Y) : G) ∈ S := by
      have hSa := (mem_inf.mp ha).1
      have hSb := (mem_inf.mp hb).1
      have hSc := (mem_inf.mp hc).1
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, ha', hb', hc']
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hSa hSb) (inv_mem hSa))
        (inv_mem hSb)) hSc) (inv_mem (mul_mem (mul_mem (mul_mem hSa hSb) (inv_mem hSa))
        (inv_mem hSb)))) (inv_mem hSc)
    have h1 := congrArg Subtype.val (hinj _ hmem hφ)
    simpa [commutatorElement_def, ha', hb', hc'] using h1
  have hexp : ∀ x ∈ S ⊓ Y, x ^ 4 = 1 := by
    intro x hx
    have hφ := pow_four_eq_one_of_isPGroup_pi hV2 _ (hφR _ (hmemR x hx))
    rw [← map_pow] at hφ
    have hmem : (((⟨x, (mem_inf.mp hx).2⟩ : ↥Y) ^ 4 : ↥Y) : G) ∈ S := by
      rw [Subgroup.coe_pow]
      exact pow_mem (mem_inf.mp hx).1 4
    have h1 := congrArg Subtype.val (hinj _ hmem hφ)
    simpa using h1
  have hcl : ⁅⁅S ⊓ Y, S ⊓ Y⁆, S ⊓ Y⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp (hcl3 a ha b hb c hc)).symm
  set D := ⁅S ⊓ Y, S ⊓ Y⁆ with hD
  have hDS₀ : D ≤ S ⊓ Y := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hDS : D ≤ S := hDS₀.trans inf_le_left
  have hDc : D ≤ centralizer ((S ⊓ Y : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl
  have hDR : D = ⁅(R : Subgroup ↥Y), (R : Subgroup ↥Y)⁆.map Y.subtype := by
    rw [hD, ← hRY, Subgroup.map_commutator]
  have hS₀n : S ≤ normalizer ((S ⊓ Y : Subgroup G) : Set G) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro x
    have hsY := hYN (hSyl.1 hs)
    rw [mem_normalizer_iff] at hsY
    constructor
    · intro hx
      exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hx).1) (inv_mem hs),
        (hsY x).mp (mem_inf.mp hx).2⟩
    · intro hx
      have h1 : x = s⁻¹ * (s * x * s⁻¹) * s := by group
      exact mem_inf.mpr ⟨h1 ▸ mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hx).1) hs,
        (hsY x).mpr (mem_inf.mp hx).2⟩
  have hDn : S ≤ normalizer (D : Set G) := by
    intro s hs
    rw [mem_normalizer_iff_map_conj_eq, hD, Subgroup.map_commutator,
      (mem_normalizer_iff_map_conj_eq.mp (hS₀n hs))]
  have hDelem : IsElemTwo D := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp (hDc hx) y (hDS₀ hy)).symm
    · rw [hDR] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      have hVr : φ r ∈ ⁅(V : Subgroup (Fin k → projectiveSL 3 F)),
          (V : Subgroup (Fin k → projectiveSL 3 F))⁆ := by
        rw [hVcoe, ← Subgroup.map_commutator]
        exact ⟨r, hr, rfl⟩
      have h2 := (isElemTwo_commutator_sylow_pi V).1.2 _ hVr
      rw [← map_mul] at h2
      have hrR : r ∈ (R : Subgroup ↥Y) := by
        have := Subgroup.commutator_le.mpr (fun a ha b hb => by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hr
        exact this
      have hrr : ((r * r : ↥Y) : G) ∈ S := by
        rw [Subgroup.coe_mul]
        exact mul_mem (hRS r hrR) (hRS r hrR)
      have := congrArg Subtype.val (hinj _ hrr h2)
      simpa using this
  have hDcard : Nat.card F ^ k ≤ Nat.card D := by
    rw [← (isElemTwo_commutator_sylow_pi V).2, hVcoe, ← Subgroup.map_commutator, hDR,
      Subgroup.card_map_of_injective Y.subtype_injective]
    exact Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective _)
  have hD16 : 16 ≤ Nat.card D :=
    hF16.trans ((Nat.le_self_pow (by omega) _).trans hDcard)
  have hDE : Open.IsElemAbelian 2 D := hDelem.isElemAbelian
  have hD8 : 8 ≤ Nat.card D := by omega
  by_cases hb : k = 1 ∧ Nat.card F = 16
  ·
    obtain ⟨hk, hF⟩ := hb
    have hbd' := hbd hk hF
    have htc : ∀ x ∈ S ⊓ Y, t * x = x * t := by
      intro x hx
      have h1 := hbd' x (mem_inf.mp hx).2
      have h2 : t * x * t⁻¹ * x⁻¹ ∈ S :=
        mul_mem (mul_mem (mul_mem htS (mem_inf.mp hx).1) (inv_mem htS)) (inv_mem (mem_inf.mp hx).1)
      have h3 := hSO _ h2 h1
      calc t * x = t * x * t⁻¹ * x⁻¹ * (x * t) := by group
        _ = x * t := by rw [h3, one_mul]
    have hDt : D ≤ centralizer ({t} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (htc x (hDS₀ hx)).symm
    have hWD : wGroup D = W := hWE D hDt hDE hD8
    have conj_mem_oddIn : ∀ {g d : G}, g ∈ M → d ∈ O → g * d * g⁻¹ ∈ O := by
      intro g d hg hd
      obtain ⟨d', hd', rfl⟩ := hd
      have hn : (pPrimeCore 2 ↥M).Normal := inferInstance
      exact ⟨⟨g, hg⟩ * d' * ⟨g, hg⟩⁻¹, hn.conj_mem d' hd' ⟨g, hg⟩, by simp⟩
    let K₀ : Subgroup G :=
      { carrier := {m | m ∈ M ∧ ∀ y ∈ Y, m * y * m⁻¹ * y⁻¹ ∈ O}
        one_mem' := ⟨one_mem _, fun y _ => by simp⟩
        mul_mem' := by
          rintro m₁ m₂ ⟨hm₁, h₁⟩ ⟨hm₂, h₂⟩
          refine ⟨mul_mem hm₁ hm₂, fun y hy => ?_⟩
          have e : m₁ * m₂ * y * (m₁ * m₂)⁻¹ * y⁻¹ =
              (m₁ * (m₂ * y * m₂⁻¹ * y⁻¹) * m₁⁻¹) * (m₁ * y * m₁⁻¹ * y⁻¹) := by group
          rw [e]
          exact mul_mem (conj_mem_oddIn hm₁ (h₂ y hy)) (h₁ y hy)
        inv_mem' := by
          rintro m ⟨hm, h⟩
          refine ⟨inv_mem hm, fun y hy => ?_⟩
          have hy' : m⁻¹ * y * m ∈ Y := by
            have := (mem_normalizer_iff.mp (hYN (inv_mem hm)) y).mp hy
            simpa using this
          have h1 := inv_mem (h _ hy')
          have e : (m * (m⁻¹ * y * m) * m⁻¹ * (m⁻¹ * y * m)⁻¹)⁻¹ = m⁻¹ * y * m⁻¹⁻¹ * y⁻¹ := by
            group
          rwa [e] at h1 }
    have htK : t ∈ K₀ := ⟨htM, hbd'⟩
    have hK₀n : S ≤ normalizer (K₀ : Set G) := by
      intro s hs
      have hsM := hSyl.1 hs
      rw [mem_normalizer_iff]
      intro m
      constructor
      · rintro ⟨hm, h⟩
        refine ⟨mul_mem (mul_mem hsM hm) (inv_mem hsM), fun y hy => ?_⟩
        have hy' : s⁻¹ * y * s ∈ Y := by
          have := (mem_normalizer_iff.mp (hYN (inv_mem hsM)) y).mp hy
          simpa using this
        have e : s * m * s⁻¹ * y * (s * m * s⁻¹)⁻¹ * y⁻¹ =
            s * (m * (s⁻¹ * y * s) * m⁻¹ * (s⁻¹ * y * s)⁻¹) * s⁻¹ := by group
        rw [e]
        exact conj_mem_oddIn hsM (h _ hy')
      · rintro ⟨hm, h⟩
        have hm' : m ∈ M := by
          have := mul_mem (mul_mem (inv_mem hsM) hm) hsM
          simpa [mul_assoc] using this
        refine ⟨hm', fun y hy => ?_⟩
        have hy' : s * y * s⁻¹ ∈ Y := (mem_normalizer_iff.mp (hYN hsM) y).mp hy
        have e : m * y * m⁻¹ * y⁻¹ =
            s⁻¹ * (s * m * s⁻¹ * (s * y * s⁻¹) * (s * m * s⁻¹)⁻¹ * (s * y * s⁻¹)⁻¹) * s := by group
        rw [e]
        have := conj_mem_oddIn (inv_mem hsM) (h _ hy')
        simpa using this
    set T₁ := S ⊓ K₀ with hT₁
    have hT₁ne : T₁ ≠ ⊥ := by
      intro hbot
      have : t ∈ (⊥ : Subgroup G) := hbot ▸ mem_inf.mpr ⟨htS, htK⟩
      have ht1 : t = 1 := (mem_bot.mp this)
      have hto : orderOf t = 2 := hset.2.1
      rw [ht1, orderOf_one] at hto
      exact absurd hto (by norm_num)
    obtain ⟨v, hvT, hvZ, hv2, hv1⟩ :
        ∃ v ∈ T₁, v ∈ centralizer (S : Set G) ∧ v * v = 1 ∧ v ≠ 1 := by
      have hT₁S : T₁ ≤ S := inf_le_left
      have hT₁n : (T₁.subgroupOf S).Normal := by
        rw [normal_subgroupOf_iff_le_normalizer hT₁S]
        intro s hs
        rw [mem_normalizer_iff]
        intro x
        have h1 := mem_normalizer_iff.mp (Subgroup.le_normalizer hs) x
        have h2 := mem_normalizer_iff.mp (hK₀n hs) x
        rw [hT₁, mem_inf, mem_inf]
        exact and_congr h1 h2
      have := hS2.isNilpotent
      have hNne : T₁.subgroupOf S ≠ ⊥ := by
        intro h0
        apply hT₁ne
        rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hT₁S hx⟩ : ↥S) ∈ T₁.subgroupOf S := hx
        rw [h0, mem_bot] at hx'
        exact mem_bot.mpr (congrArg Subtype.val hx')
      have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hNne
      set Z' := T₁.subgroupOf S ⊓ center ↥S with hZ'
      have hZ2 : IsPGroup 2 ↥Z' := hS2.to_subgroup Z'
      have : Nontrivial ↥Z' := (Subgroup.nontrivial_iff_ne_bot Z').mpr hZ
      obtain ⟨n, hn0, hn⟩ := hZ2.nontrivial_iff_card.mp this
      obtain ⟨v', hv'⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z') 2
        (hn ▸ dvd_pow_self 2 (by omega))
      have hv'T : ((v' : ↥S) : G) ∈ T₁ := mem_subgroupOf.mp (mem_inf.mp v'.2).1
      have hv'Z : (v' : ↥S) ∈ center ↥S := (mem_inf.mp v'.2).2
      refine ⟨((v' : ↥S) : G), hv'T, ?_, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro s hs
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv'Z ⟨s, hs⟩)
      · have h := pow_orderOf_eq_one v'
        rw [hv', pow_two] at h
        exact congrArg (fun z : ↥Z' => ((z : ↥S) : G)) h
      · intro h1
        have : v' = 1 := Subtype.ext (Subtype.ext h1)
        rw [this, orderOf_one] at hv'
        exact absurd hv' (by norm_num)
    have hvS : v ∈ S := (mem_inf.mp hvT).1
    have hvK : v ∈ K₀ := (mem_inf.mp hvT).2
    have hcen : center (Fin k → projectiveSL 3 F) = ⊥ := by
      rw [Subgroup.center_pi]
      simp only [CFSG.GH74.KGroups.L3Eps.center_projectiveSL_three_eq_bot]
      exact Subgroup.pi_bot
    have hvY : v ∉ Y := by
      intro hvY
      apply hv1
      have hc : φ ⟨v, hvY⟩ ∈ center (Fin k → projectiveSL 3 F) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨y, rfl⟩ := hφs z
        have hk : (⟨v, hvY⟩ : ↥Y) * y * (⟨v, hvY⟩ : ↥Y)⁻¹ * y⁻¹ ∈ φ.ker := by
          rw [hφk, mem_subgroupOf]
          exact hvK.2 y y.2
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hk
        have := congrArg (· * (φ y * φ ⟨v, hvY⟩)) hk
        simp only [one_mul] at this
        rw [← this]
        group
      rw [hcen, mem_bot] at hc
      exact congrArg Subtype.val (hinj _ hvS hc)
    set B := D ⊔ zpowers v with hB
    have hvC : zpowers v ≤ centralizer (S : Set G) := zpowers_le.mpr hvZ
    have hBelem : IsElemTwo B :=
      hDelem.sup (isElemTwo_zpowers hv2) fun x hx y hy =>
        (Subgroup.mem_centralizer_iff.mp (hvC hy) x (hDS hx))
    have hBS : B ≤ S := sup_le hDS (zpowers_le.mpr hvS)
    have hBn : S ≤ normalizer (B : Set G) := by
      intro s hs
      rw [mem_normalizer_iff_map_conj_eq, hB, Subgroup.map_sup,
        mem_normalizer_iff_map_conj_eq.mp (hDn hs), MonoidHom.map_zpowers]
      congr 2
      show s * v * s⁻¹ = v
      rw [Subgroup.mem_centralizer_iff.mp hvZ s hs, mul_inv_cancel_right]
    have hDB : D ≤ B := le_sup_left
    have hvB : v ∈ B := (le_sup_right : zpowers v ≤ B) (mem_zpowers v)
    have hvD : v ∉ D := fun hvD => hvY (mem_inf.mp (hDS₀ hvD)).2
    have hB32 : 32 ≤ Nat.card B := by
      obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hDB
      have hm1 : m ≠ 1 := by
        rintro rfl
        rw [mul_one] at hm
        exact hvD ((Subgroup.eq_of_le_of_card_ge hDB hm.le) ▸ hvB)
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hm
        exact Nat.card_pos.ne' hm
      rw [hm]
      calc 32 = 16 * 2 := by norm_num
        _ ≤ Nat.card D * m := Nat.mul_le_mul hD16 (by omega)
    have hBc : B ≤ centralizer ((S ⊓ Y : Subgroup G) : Set G) :=
      sup_le hDc (hvC.trans (Subgroup.centralizer_le inf_le_left))
    have hWB : wGroup B = W := by
      rw [← hWD]
      exact wGroup_eq_of_commute hGW (hBelem.isAbelianTwoOfRank (by omega))
        (hDelem.isAbelianTwoOfRank hD8) fun x hx y hy => hBelem.1 x hx y (hDB hy)
    exact ⟨S, Y, hSyl, hYM, hYn, hcl, hexp, ⟨D, hDS₀, hDE, hD16⟩,
      ⟨B, hBS, hBn, hBelem.isElemAbelian, hB32, hWB⟩,
      ⟨B, hBS, hBn, hBelem.isElemAbelian, hB32,
        fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hBc hy) x hx)⟩⟩
  ·
    have hD32 : 32 ≤ Nat.card D := by
      refine le_trans ?_ hDcard
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card F = 2 ^ n := by
        have := Fintype.ofFinite F
        obtain ⟨n, -, hn⟩ := FiniteField.card F 2
        exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
      by_cases hk2 : 2 ≤ k
      · calc 32 ≤ 16 ^ 2 := by norm_num
          _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hF16 2
          _ ≤ Nat.card F ^ k := Nat.pow_le_pow_right (by omega) hk2
      · have hk : k = 1 := by omega
        have hF' : Nat.card F ≠ 16 := fun h => hb ⟨hk, h⟩
        rw [hk, pow_one, hn]
        rw [hn] at hF16 hF'
        have h4 : 4 ≤ n := by
          by_contra hlt
          have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have h5 : n ≠ 4 := fun h => hF' (by rw [h]; norm_num)
        calc 32 = 2 ^ 5 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htD : t ∈ normalizer (D : Set G) := hDn htS
    have hsq := card_le_card_inf_centralizer_sq hDelem htD ht2
    have hE'8 : 8 ≤ Nat.card ↥(D ⊓ centralizer ({t} : Set G)) :=
      (le_card_of_le_card_sq (hDelem.isPGroup.to_le inf_le_left)).2 (hD32.trans hsq)
    have hE' : IsElemTwo (D ⊓ centralizer ({t} : Set G)) := hDelem.mono inf_le_left
    have hWE' := hWE _ inf_le_right hE'.isElemAbelian hE'8
    have hWD : wGroup D = W := by
      rw [← hWE']
      exact wGroup_eq_of_commute hGW (hDelem.isAbelianTwoOfRank hD8) (hE'.isAbelianTwoOfRank hE'8)
        fun x hx y hy => hDelem.1 x hx y (mem_inf.mp hy).1
    exact ⟨S, Y, hSyl, hYM, hYn, hcl, hexp, ⟨D, hDS₀, hDE, hD16⟩,
      ⟨D, hDS, hDn, hDE, hD32, hWD⟩,
      ⟨D, hDS, hDn, hDE, hD32, fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hDc hy) x hx)⟩⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
