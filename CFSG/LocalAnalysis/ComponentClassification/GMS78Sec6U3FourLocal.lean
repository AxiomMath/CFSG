module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalLocal

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec3

variable {L T : Subgroup G}

omit [Finite G] in
theorem inf_le_normalizer_gmsA :
    T ⊓ L ≤ normalizer ((gmsA L T : Subgroup G) : Set G) := fun t ht =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun _ ha =>
    ((mem_centralizer_iff.mp (mem_inf.mp ha).2) t ht).symm)

omit [Finite G] in
theorem commutator_mem_of_sq_mem_of_mem_normalizer {N : Subgroup G} {x y : G}
    (hyN : y ∈ normalizer (N : Set G)) (hx2 : x ^ 2 ∈ N) (hy2 : y ^ 2 ∈ N)
    (hxy2 : (x * y) ^ 2 ∈ N) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
    rw [sq, sq, sq]
    group
  rw [e]
  refine mul_mem (mul_mem hxy2 ?_) (inv_mem hy2)
  have := (mem_normalizer_iff.mp (inv_mem hyN) _).mp (inv_mem hx2)
  simpa using this

theorem commutator_inf_eq_gmsA (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) : ⁅T ⊓ L, T ⊓ L⁆ = gmsA L T := by
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  obtain ⟨-, hA₁c, -, -, hsq, hcomm⟩ := sylow_of_psu3 hZ hf e h3.isSylowOf_T₁
  have hle : ⁅T ⊓ L, T ⊓ L⁆ ≤ gmsA L T := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact commutator_mem_of_sq_mem_of_mem_normalizer (inf_le_normalizer_gmsA hb) (hsq a ha)
      (hsq b hb) (hsq _ (mul_mem ha hb))
  refine eq_of_le_of_card_ge hle ?_
  have h1 : Nat.card (⁅T ⊓ L, T ⊓ L⁆ : Subgroup G) =
      Nat.card (_root_.commutator ↥(T ⊓ L)) := by
    rw [← Subgroup.map_subtype_commutator]
    exact card_map_of_injective (T ⊓ L).subtype_injective
  rw [h1, hcomm]
  exact hA₁c.le

theorem commutator_inf_K_eq (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) :
    ⁅T ⊓ L, K⁆ = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hCT, -⟩ := u3K_facts h3 hf e hKL hKo hKH
  have hKN : K ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := fun k hk =>
    (mem_inf.mp (mem_inf.mp ((hKH ▸ (le_sup_right : K ≤ (T ⊓ L) ⊔ K)) hk)).1).2
  have hT2 : IsPGroup 2 (T ⊓ L : Subgroup G) := h3.isSylowOf_T₁.isPGroup
  have hdec := le_commutator_sup_inf_centralizer_of_odd hKN hT2 hKo
  have hCle : ⁅T ⊓ L, K⁆ ≤ T ⊓ L := by
    rw [commutator_le]
    intro t ht k hk
    rw [commutatorElement_def]
    have h1 : k * t⁻¹ * k⁻¹ ∈ T ⊓ L := (mem_normalizer_iff.mp (hKN hk) _).mp (inv_mem ht)
    have e1 : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
    rw [e1]
    exact mul_mem ht h1
  set C := ⁅T ⊓ L, K⁆ with hCdef
  have hTCA : T ⊓ L ≤ C ⊔ gmsA L T := hdec.trans (sup_le_sup_left hCT _)
  have hCN : C ≤ normalizer ((gmsA L T : Subgroup G) : Set G) :=
    hCle.trans inf_le_normalizer_gmsA
  have hdecomp : ∀ a ∈ T ⊓ L, ∃ c ∈ C, ∃ z ∈ gmsA L T, c * z = a := fun a ha =>
    CFSG.Goldschmidt.G37.mem_sup_of_le_normalizer hCN (hTCA ha)
  have hcomm : ⁅T ⊓ L, T ⊓ L⁆ ≤ C := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨c₁, hc₁, z₁, hz₁, rfl⟩ := hdecomp a ha
    obtain ⟨c₂, hc₂, z₂, hz₂, rfl⟩ := hdecomp b hb
    have hc₁T := hCle hc₁
    have hc₂T := hCle hc₂
    have hz₁c : ∀ t ∈ T ⊓ L, t * z₁ = z₁ * t := fun t ht =>
      (mem_centralizer_iff.mp (mem_inf.mp hz₁).2) t ht
    have hz₂c : ∀ t ∈ T ⊓ L, t * z₂ = z₂ * t := fun t ht =>
      (mem_centralizer_iff.mp (mem_inf.mp hz₂).2) t ht
    have e1 : ⁅c₁ * z₁, c₂ * z₂⁆ = ⁅c₁, c₂⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      have hz₁2 : z₁ * c₂ = c₂ * z₁ := (hz₁c c₂ hc₂T).symm
      have hz₁3 : z₁ * z₂ = z₂ * z₁ := (hz₁c z₂ (mem_inf.mp hz₂).1).symm
      have hz₂1 : z₂ * c₁⁻¹ = c₁⁻¹ * z₂ := (hz₂c _ (inv_mem hc₁T)).symm
      calc c₁ * z₁ * (c₂ * z₂) * (c₁ * z₁)⁻¹ * (c₂ * z₂)⁻¹
          = c₁ * (z₁ * c₂) * z₂ * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * c₂ * (z₁ * z₂) * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by rw [hz₁2]; group
        _ = c₁ * c₂ * (z₂ * z₁) * z₁⁻¹ * c₁⁻¹ * z₂⁻¹ * c₂⁻¹ := by rw [hz₁3]
        _ = c₁ * c₂ * (z₂ * c₁⁻¹) * z₂⁻¹ * c₂⁻¹ := by group
        _ = c₁ * c₂ * (c₁⁻¹ * z₂) * z₂⁻¹ * c₂⁻¹ := by rw [hz₂1]
        _ = c₁ * c₂ * c₁⁻¹ * c₂⁻¹ := by group
    rw [e1, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hc₁ hc₂) (inv_mem hc₁)) (inv_mem hc₂)
  have hAC : gmsA L T ≤ C := (commutator_inf_eq_gmsA h3 hf e) ▸ hcomm
  exact le_antisymm hCle (hTCA.trans (sup_le le_rfl hAC))

theorem pow_mem_centralizer_of_mem_K (h3 : Sec3 G L T) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G)) {k : G} (hk : k ∈ K) :
    k ^ (2 ^ f + 1) ∈ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 hf e
  have hP : IsSylowOf 2 (T ⊓ L) L := h3.isSylowOf_T₁
  set P : Subgroup G := T ⊓ L with hPdef
  obtain ⟨R, hR⟩ := exists_sylow_range hP
  obtain ⟨Kf, _, _, _, J, hJ, hcard, hfixed, φ, S, hS, hRS⟩ := exists_mulEquiv_root hf e R
  set ρ : L →* ProjectiveSpecialUnitaryMatrixGroup J :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hρdef
  have hker : ρ.ker = center L := by
    ext x
    rw [MonoidHom.mem_ker, hρdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set P' : Subgroup L := P.subgroupOf L
  have hP' : IsPGroup 2 P' := hP.isPGroup.comap_subtype
  have hroot : P'.map ρ = unitaryCoverRoot J hJ := by
    rw [← hS, ← hRS, hρdef, ← map_map, ← hR]
    congr 1
    ext y
    rw [MonoidHom.mem_range, mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, hP.le x.2⟩, x.2, rfl⟩
  have hRp : IsPGroup 2 (unitaryCoverRoot J hJ) := hS ▸ S.isPGroup'
  have hPZ : P' ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) hP'.to_inf_left hZ
      inf_le_right
  have hinjP : ∀ p ∈ P', ρ p = 1 → p = 1 := fun p hp h1 => by
    have : p ∈ P' ⊓ center L := mem_inf.mpr ⟨hp, hker ▸ MonoidHom.mem_ker.mpr h1⟩
    rwa [hPZ, mem_bot] at this
  have hkH : k ∈ L ⊓ normalizer (P : Set G) ⊓ centralizer ((gmsA L T : Subgroup G) : Set G) := by
    rw [← hKH]
    exact mem_sup_right hk
  obtain ⟨hkLN, hkC⟩ := mem_inf.mp hkH
  obtain ⟨hkL, hkN⟩ := mem_inf.mp hkLN
  set k' : L := ⟨k, hkL⟩ with hk'def
  have hkR : ρ k' ∈ normalizer ((unitaryCoverRoot J hJ : Subgroup _) : Set _) := by
    rw [← hroot, mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨k' * p * k'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (mem_normalizer_iff.mp hkN (p : G)).mp hp
    · rintro ⟨p, hp, hpe⟩
      refine ⟨k'⁻¹ * p * k', ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp (inv_mem hkN) (p : G)).mp hp
        have e1 : ((k'⁻¹ * p * k' : L) : G) = k⁻¹ * p * k⁻¹⁻¹ := by
          simp [hk'def]
        show ((k'⁻¹ * p * k' : L) : G) ∈ P
        rw [e1]
        exact h1
      · rw [map_mul, map_mul, map_inv, hpe]
        group
  have hkZ : ρ k' ∈ centralizer ((sylowCenter (unitaryCoverRoot J hJ) : Subgroup _) :
      Set _) := by
    rw [mem_centralizer_iff]
    intro z hz
    obtain ⟨hzR, hzc⟩ := mem_sylowCenter.mp hz
    rw [← hroot] at hzR hzc
    obtain ⟨p, hp, rfl⟩ := hzR
    have hpA : (p : G) ∈ gmsA L T := by
      refine mem_inf.mpr ⟨hp, mem_centralizer_iff.mpr fun q hq => ?_⟩
      have hq' : (⟨q, hP.le hq⟩ : L) ∈ P' := hq
      have hc := hzc (ρ ⟨q, hP.le hq⟩) ⟨_, hq', rfl⟩
      have h1 : (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ = 1 := by
        apply hinjP
        · exact mul_mem (mul_mem (mul_mem hq' hp) (inv_mem hq')) (inv_mem hp)
        · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
          group
      have h2 : (⟨q, hP.le hq⟩ : L) * p = p * (⟨q, hP.le hq⟩ : L) := by
        calc (⟨q, hP.le hq⟩ : L) * p =
              (⟨q, hP.le hq⟩ : L) * p * (⟨q, hP.le hq⟩ : L)⁻¹ * p⁻¹ *
                (p * (⟨q, hP.le hq⟩ : L)) := by group
          _ = p * (⟨q, hP.le hq⟩ : L) := by rw [h1, one_mul]
      exact congrArg Subtype.val h2
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp hkC) (p : G) hpA)
  obtain ⟨r, hr, a, ha, hra⟩ :=
    u3_exists_eq_mul_of_mem_normalizer J hJ hf hcard hfixed hkR hkZ
  have hA₀dvd : Nat.card (u3TorusK J hJ) ∣ 2 ^ f + 1 := by
    have hq : 2 < 2 ^ f := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right two_pos hf)
    have h1 := card_torusL_mul_card hJ (le_rfl : scalarCenter J ≤ scalarCenter J)
    rw [card_normOne (J := J) Nat.prime_two hq hcard hfixed] at h1
    have h2 : Nat.card (u3TorusK J hJ) = Nat.card (torusL J (scalarCenter J) hJ) :=
      Subgroup.card_map_of_injective (u3CoverEquiv J hJ).injective
    rw [h2]
    exact ⟨_, h1.symm⟩
  have ha5 : a ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := hA₀dvd
    have h1 : (⟨a, ha⟩ : u3TorusK J hJ) ^ (2 ^ f + 1) = 1 := by
      rw [hm, pow_mul, pow_card_eq_one', one_pow]
    simpa using congrArg Subtype.val h1
  have haN := u3_torusK_le_normalizer J hJ ha
  have hpow : ∀ n : ℕ, (r * a) ^ n * (a ^ n)⁻¹ ∈ unitaryCoverRoot J hJ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : (r * a) ^ (n + 1) * (a ^ (n + 1))⁻¹ =
          ((r * a) ^ n * (a ^ n)⁻¹) * (a ^ n * r * (a ^ n)⁻¹) := by
        rw [pow_succ, pow_succ]
        group
      rw [e1]
      exact mul_mem ih ((mem_normalizer_iff.mp (pow_mem haN n) r).mp hr)
  have hyR : ρ k' ^ (2 ^ f + 1) ∈ unitaryCoverRoot J hJ := by
    have h1 := hpow (2 ^ f + 1)
    rwa [ha5, inv_one, mul_one, ← hra] at h1
  have hodd : Odd (orderOf (ρ k' ^ (2 ^ f + 1))) := by
    have h1 : orderOf (ρ k' ^ (2 ^ f + 1)) ∣ Nat.card K := by
      refine (orderOf_pow_dvd _).trans ((orderOf_map_dvd ρ k').trans ?_)
      rw [← Subgroup.orderOf_coe k', hk'def]
      show orderOf k ∣ Nat.card K
      rw [← Subgroup.orderOf_mk k hk]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hKo h1
  have hy1 : ρ k' ^ (2 ^ f + 1) = 1 := by
    obtain ⟨m, hm⟩ := hRp ⟨_, hyR⟩
    have h1 : orderOf (ρ k' ^ (2 ^ f + 1)) ∣ 2 ^ m :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
    have h3 : orderOf (ρ k' ^ (2 ^ f + 1)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)) h1
    exact orderOf_eq_one_iff.mp h3
  have hz : k' ^ (2 ^ f + 1) ∈ center L := by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hy1
  rw [mem_centralizer_iff]
  intro l hl
  have h1 := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨l, hl⟩)
  simpa [hk'def] using h1

theorem eq_or_eq_of_four (h3 : Sec3 G L T) (e : rankTwoQuot L ≃* PSU3 2 2) {K : Subgroup G}
    (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {U : Subgroup G} (hAU : gmsA L T ≤ U) (hUT : U ≤ T ⊓ L)
    (hKU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) : U = gmsA L T ∨ U = T ⊓ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 le_rfl e
  obtain ⟨hTc, hAc, -⟩ := sylow_of_psu3 hZ le_rfl e h3.isSylowOf_T₁
  obtain ⟨-, -, -, hCT, -⟩ := u3K_facts h3 le_rfl e hKL hKo hKH
  have hKA : K ≤ centralizer ((gmsA L T : Subgroup G) : Set G) := fun k hk =>
    (mem_inf.mp ((hKH ▸ (le_sup_right : K ≤ (T ⊓ L) ⊔ K)) hk)).2
  let act : K → Equiv.Perm U := fun k =>
    { toFun := fun u => ⟨k * u * k⁻¹, hKU k k.2 u u.2⟩
      invFun := fun u => ⟨(k : G)⁻¹ * u * k, by simpa using hKU _ (inv_mem k.2) u u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  let ψ : K →* Equiv.Perm U :=
    { toFun := act
      map_one' := Equiv.ext fun u => Subtype.ext (by simp [act])
      map_mul' := fun k₁ k₂ => Equiv.ext fun u => Subtype.ext (by simp [act, mul_assoc]) }
  have hψ : ∀ (k : K) (u : U), ((ψ k u : U) : G) = k * u * k⁻¹ := fun _ _ => rfl
  have hQ : IsPGroup 5 ψ.range := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    show ψ k ^ 5 = 1
    rw [← map_pow]
    ext u
    have hk5 : ((k : G) ^ (2 ^ 2 + 1)) ∈ centralizer (L : Set G) :=
      pow_mem_centralizer_of_mem_K h3 le_rfl e hKo hKH k.2
    have hc := (mem_centralizer_iff.mp hk5) (u : G) ((hUT.trans inf_le_right) u.2)
    norm_num at hc
    rw [Equiv.Perm.coe_one, id_eq, hψ, InvMemClass.coe_inv, SubgroupClass.coe_pow]
    calc (k : G) ^ 5 * (u : G) * ((k : G) ^ 5)⁻¹
        = ((u : G) * (k : G) ^ 5) * ((k : G) ^ 5)⁻¹ := by rw [hc]
      _ = (u : G) := by group
  have hfixset : MulAction.fixedPoints ψ.range U = {u : U | (u : G) ∈ gmsA L T} := by
    ext u
    simp only [MulAction.mem_fixedPoints, Set.mem_ofPred_eq]
    constructor
    · intro hu
      apply hCT
      refine mem_inf.mpr ⟨hUT u.2, mem_centralizer_iff.mpr fun k hk => ?_⟩
      have h1 := congrArg Subtype.val (hu ⟨ψ ⟨k, hk⟩, ⟨k, hk⟩, rfl⟩)
      have h2 : k * u * k⁻¹ = u := h1
      calc k * u = k * u * k⁻¹ * k := by group
        _ = u * k := by rw [h2]
    · intro hu q
      obtain ⟨_, k, rfl⟩ := q
      apply Subtype.ext
      show (k : G) * u * (k : G)⁻¹ = u
      rw [← (mem_centralizer_iff.mp (hKA k.2)) (u : G) hu]
      group
  have hfix : Nat.card (MulAction.fixedPoints ψ.range U) = 4 := by
    rw [hfixset]
    have h1 : Nat.card {u : U | (u : G) ∈ gmsA L T} = Nat.card ((gmsA L T).subgroupOf U) := rfl
    rw [h1, Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv]
    simpa using hAc
  have hcount := hQ.card_modEq_card_fixedPoints U
  rw [hfix] at hcount
  obtain ⟨j, hj⟩ := (h3.isSylowOf_T₁.isPGroup.to_le hUT).exists_card_eq
  have hj6 : j ≤ 6 := by
    have h1 := Subgroup.card_dvd_of_le hUT
    rw [hj, hTc] at h1
    have h2 : 2 ^ j ∣ 2 ^ 6 := by
      rw [show (2 : ℕ) ^ 6 = (2 ^ 2) ^ 3 by norm_num]
      exact h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h2
  have hj2 : 2 ≤ j := by
    have h1 := Subgroup.card_dvd_of_le hAU
    rw [hj] at h1
    have h2 : Nat.card (gmsA L T) = 2 ^ 2 := by simpa using hAc
    rw [h2] at h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h1
  rw [hj] at hcount
  interval_cases j
  · left
    refine (eq_of_le_of_card_ge hAU ?_).symm
    rw [hj]
    simpa using hAc.ge
  · exact absurd hcount (by decide)
  · exact absurd hcount (by decide)
  · exact absurd hcount (by decide)
  · right
    refine eq_of_le_of_card_ge hUT ?_
    rw [hj, hTc]
    norm_num

theorem mem_centralizer_of_isPGroup_four (h3 : Sec3 G L T) (e : rankTwoQuot L ≃* PSU3 2 2)
    {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {x : G} (hx : IsPGroup 2 (zpowers x)) (hxN : x ∈ normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hxK : x ∈ centralizer (K : Set G)) : x ∈ centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Odd (Nat.card (center L)) := odd_card_center_of_psu3 h3.hyp.standard.1.1 le_rfl e
  obtain ⟨hTc, hAc, -⟩ := sylow_of_psu3 hZ le_rfl e h3.isSylowOf_T₁
  have hKA : K ≤ centralizer ((gmsA L T : Subgroup G) : Set G) := fun k hk =>
    (mem_inf.mp ((hKH ▸ (le_sup_right : K ≤ (T ⊓ L) ⊔ K)) hk)).2
  have hKN : K ≤ normalizer ((T ⊓ L : Subgroup G) : Set G) := fun k hk =>
    (mem_inf.mp (mem_inf.mp ((hKH ▸ (le_sup_right : K ≤ (T ⊓ L) ⊔ K)) hk)).1).2
  set T₁ := T ⊓ L with hT₁def
  set A₁ := gmsA L T with hA₁def
  have hAT : A₁ ≤ T₁ := inf_le_left
  have hAc' : ∀ a ∈ A₁, ∀ t ∈ T₁, t * a = a * t := fun a ha t ht =>
    (mem_centralizer_iff.mp (mem_inf.mp ha).2) t ht
  have hxA : ∀ a ∈ A₁, x * a * x⁻¹ ∈ A₁ := by
    intro a ha
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hxN a).mp (hAT ha),
      mem_centralizer_iff.mpr fun t ht => ?_⟩
    have ht' : x⁻¹ * t * x ∈ T₁ := by
      simpa using (mem_normalizer_iff.mp (inv_mem hxN) t).mp ht
    have hc := hAc' a ha _ ht'
    calc t * (x * a * x⁻¹) = x * ((x⁻¹ * t * x) * a) * x⁻¹ := by group
      _ = x * (a * (x⁻¹ * t * x)) * x⁻¹ := by rw [hc]
      _ = x * a * x⁻¹ * t := by group
  let U : Subgroup G :=
    { carrier := {t | t ∈ T₁ ∧ t⁻¹ * (x * t * x⁻¹) ∈ A₁}
      mul_mem' := by
        rintro t s ⟨ht, hta⟩ ⟨hs, hsa⟩
        refine ⟨mul_mem ht hs, ?_⟩
        have e1 : (t * s)⁻¹ * (x * (t * s) * x⁻¹) =
            s⁻¹ * (t⁻¹ * (x * t * x⁻¹)) * s * (s⁻¹ * (x * s * x⁻¹)) := by group
        have e2 : s⁻¹ * (t⁻¹ * (x * t * x⁻¹)) * s = t⁻¹ * (x * t * x⁻¹) := by
          rw [mul_assoc, ← hAc' _ hta s hs]
          group
        rw [e1, e2]
        exact mul_mem hta hsa
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro t ⟨ht, hta⟩
        refine ⟨inv_mem ht, ?_⟩
        have e1 : t⁻¹⁻¹ * (x * t⁻¹ * x⁻¹) = t * (t⁻¹ * (x * t * x⁻¹))⁻¹ * t⁻¹ := by group
        rw [e1, hAc' _ (inv_mem hta) t ht]
        simpa using inv_mem hta }
  have hmemU : ∀ t, t ∈ U ↔ t ∈ T₁ ∧ t⁻¹ * (x * t * x⁻¹) ∈ A₁ := fun _ => Iff.rfl
  have hAU : A₁ ≤ U := fun a ha => ⟨hAT ha, mul_mem (inv_mem ha) (hxA a ha)⟩
  have hUT : U ≤ T₁ := fun t ht => ht.1
  have hKU : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    rintro k hk u ⟨hu, hua⟩
    refine ⟨(mem_normalizer_iff.mp (hKN hk) u).mp hu, ?_⟩
    have hxk : x * k = k * x := (mem_centralizer_iff.mp hxK k hk).symm
    have hxk1 : x * k * x⁻¹ = k := by rw [hxk]; group
    have e1 : (k * u * k⁻¹)⁻¹ * (x * (k * u * k⁻¹) * x⁻¹) =
        k * (u⁻¹ * (x * u * x⁻¹)) * k⁻¹ := by
      have h2 : x * (k * u * k⁻¹) * x⁻¹ =
          (x * k * x⁻¹) * (x * u * x⁻¹) * (x * k * x⁻¹)⁻¹ := by group
      rw [h2, hxk1]
      group
    rw [e1, ← (mem_centralizer_iff.mp (hKA hk)) _ hua]
    simpa [mul_assoc] using hua
  have hT₁2 : IsPGroup 2 T₁ := h3.isSylowOf_T₁.isPGroup
  have hUA : ∃ t ∈ U, t ∉ A₁ := by
    set E := zpowers x ⊔ T₁ with hEdef
    have hE2 : IsPGroup 2 E := IsPGroup.to_sup_of_normal_right' hx hT₁2 (zpowers_le.mpr hxN)
    have hT₁E : T₁ ≤ E := le_sup_right
    have hxE : x ∈ E := mem_sup_left (mem_zpowers x)
    have hAE : A₁ ≤ E := hAT.trans hT₁E
    have hxAN : x ∈ normalizer (A₁ : Set G) := by
      have hle : A₁.map (MulAut.conj x).toMonoidHom ≤ A₁ := by
        rintro _ ⟨a, ha, rfl⟩
        exact hxA a ha
      exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hle
        (by rw [card_map_of_injective (MulAut.conj x).injective]))
    have hEA : E ≤ normalizer (A₁ : Set G) := sup_le (zpowers_le.mpr hxAN) inf_le_normalizer_gmsA
    set N := A₁.subgroupOf E with hN
    have : N.Normal := (normal_subgroupOf_iff_le_normalizer hAE).mpr hEA
    have hQ : IsPGroup 2 (E ⧸ N) := hE2.to_quotient N
    have : Group.IsNilpotent (E ⧸ N) := hQ.isNilpotent
    have hTn : (T₁.subgroupOf E).Normal :=
      (normal_subgroupOf_iff_le_normalizer hT₁E).mpr (sup_le (zpowers_le.mpr hxN) le_normalizer)
    set H := (T₁.subgroupOf E).map (QuotientGroup.mk' N) with hH
    have : H.Normal := hTn.map _ (QuotientGroup.mk'_surjective N)
    obtain ⟨t₀, ht₀, ht₀A⟩ : ∃ t₀ ∈ T₁, t₀ ∉ A₁ := by
      by_contra hcon
      push Not at hcon
      have h1 := Subgroup.card_le_of_le (show T₁ ≤ A₁ from hcon)
      have hA4 : Nat.card A₁ = 2 ^ 2 := hAc
      rw [hTc, hA4] at h1
      norm_num at h1
    have hH1 : H ≠ ⊥ := by
      intro hb
      have hmem : QuotientGroup.mk' N ⟨t₀, hT₁E ht₀⟩ ∈ H :=
        mem_map_of_mem _ (mem_subgroupOf.mpr ht₀)
      rw [hb, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at hmem
      exact ht₀A hmem
    obtain ⟨⟨z, hz⟩, hz1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hH1)
    obtain ⟨hzH, hzc⟩ := mem_inf.mp hz
    obtain ⟨⟨t, htE⟩, htT, rfl⟩ := mem_map.mp hzH
    have htT' : t ∈ T₁ := mem_subgroupOf.mp htT
    refine ⟨t, ⟨htT', ?_⟩, fun htA => hz1 ?_⟩
    · have hc := mem_center_iff.mp hzc (QuotientGroup.mk' N ⟨x, hxE⟩)
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq, mem_subgroupOf] at hc
      have hc' : t⁻¹ * x⁻¹ * t * x ∈ A₁ := by simpa [mul_assoc] using hc
      have h1 := hxA _ hc'
      have e1 : t⁻¹ * (x * t * x⁻¹) = (x * (t⁻¹ * x⁻¹ * t * x) * x⁻¹)⁻¹ := by group
      rw [e1]
      exact inv_mem h1
    · exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr htA))
  have hUeq : U = T₁ := by
    rcases eq_or_eq_of_four h3 e hKL hKo hKH hAU hUT hKU with h | h
    · obtain ⟨t, htU, htA⟩ := hUA
      rw [h] at htU
      exact absurd htU htA
    · exact h
  have hcomm : ⁅T₁, K⁆ ≤ centralizer ({x} : Set G) := by
    rw [commutator_le]
    intro t ht k hk
    rw [mem_centralizer_singleton_iff, commutatorElement_def]
    have hta : t⁻¹ * (x * t * x⁻¹) ∈ A₁ := ((hmemU t).mp (hUeq ▸ ht)).2
    set a := t⁻¹ * (x * t * x⁻¹) with hadef
    have hxt : x * t * x⁻¹ = t * a := by rw [hadef]; group
    have hak : a * k = k * a := (mem_centralizer_iff.mp (hKA hk)) a hta
    have hxk : x * k = k * x := (mem_centralizer_iff.mp hxK k hk).symm
    have hxk1 : x * k * x⁻¹ = k := by rw [hxk]; group
    have hconj : x * (t * k * t⁻¹ * k⁻¹) * x⁻¹ = t * k * t⁻¹ * k⁻¹ := by
      have h1 : x * (t * k * t⁻¹ * k⁻¹) * x⁻¹ =
          (x * t * x⁻¹) * (x * k * x⁻¹) * (x * t * x⁻¹)⁻¹ * (x * k * x⁻¹)⁻¹ := by group
      rw [h1, hxt, hxk1]
      calc t * a * k * (t * a)⁻¹ * k⁻¹ = t * (a * k) * a⁻¹ * t⁻¹ * k⁻¹ := by group
        _ = t * (k * a) * a⁻¹ * t⁻¹ * k⁻¹ := by rw [hak]
        _ = t * k * t⁻¹ * k⁻¹ := by group
    calc t * k * t⁻¹ * k⁻¹ * x = x * (t * k * t⁻¹ * k⁻¹) * x⁻¹ * x := by rw [hconj]
      _ = x * (t * k * t⁻¹ * k⁻¹) := by group
  rw [commutator_inf_K_eq h3 le_rfl e hKL hKo hKH] at hcomm
  rw [mem_centralizer_iff]
  intro t ht
  exact mem_centralizer_singleton_iff.mp (hcomm ht)

theorem mem_normalizer_T₁_of_mem_normalizer
    (h3 : Sec3 G L T) (hF : Foundation) {f : ℕ} (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSU3 2 f) {K : Subgroup G} (hKL : K ≤ L) (hKo : Odd (Nat.card K))
    (hKH : (T ⊓ L) ⊔ K = L ⊓ normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓
      centralizer ((gmsA L T : Subgroup G) : Set G))
    {W : Subgroup G} (hVW : gmsV L T ≤ W) (hWT : W ≤ centralizer ((T ⊓ L : Subgroup G) : Set G))
    {y : G} (hyW : y ∈ normalizer (W : Set G)) (hyK : y ∈ normalizer (K : Set G)) :
    y ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := T ⊓ L with hT₁def
  have hCV : centralizer (W : Set G) ≤ centralizer (gmsV L T : Set G) :=
    Subgroup.centralizer_le hVW
  have hCN : centralizer (W : Set G) ≤ normalizer (L : Set G) :=
    hCV.trans (h3.centralizer_gmsV_le_normalizer hF)
  have hCT : centralizer (W : Set G) ≤ normalizer (T₁ : Set G) :=
    hCV.trans (h3.centralizer_gmsV_le_normalizer_T₁ hF hf e)
  have hCA : centralizer (W : Set G) ≤ centralizer ((gmsA L T : Subgroup G) : Set G) :=
    Subgroup.centralizer_le ((le_sup_left : gmsA L T ≤ gmsV L T).trans hVW)
  set H := ⁅centralizer (W : Set G), K⁆ with hHdef
  have hHle : H ≤ T₁ ⊔ K := by
    rw [commutator_le]
    intro c hc k hk
    have hkH : k ∈ L ⊓ normalizer (T₁ : Set G) ⊓ centralizer ((gmsA L T : Subgroup G) : Set G) := by
      rw [← hKH]
      exact mem_sup_right hk
    obtain ⟨hkLN, hkC⟩ := mem_inf.mp hkH
    obtain ⟨hkL, hkN⟩ := mem_inf.mp hkLN
    have hck : c * k * c⁻¹ ∈ T₁ ⊔ K := by
      rw [hKH]
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCN hc) k).mp hkL, ?_⟩, ?_⟩
      · exact mul_mem (mul_mem (hCT hc) hkN) (inv_mem (hCT hc))
      · refine mem_centralizer_iff.mpr fun a ha => ?_
        have hca : c * a = a * c := ((mem_centralizer_iff.mp (hCA hc)) a ha).symm
        have hka : a * k = k * a := (mem_centralizer_iff.mp hkC) a ha
        calc a * (c * k * c⁻¹) = (a * c) * k * c⁻¹ := by group
          _ = c * (a * k) * c⁻¹ := by rw [← hca]; group
          _ = c * (k * a) * c⁻¹ := by rw [hka]
          _ = c * k * c⁻¹ * (c * a * c⁻¹) := by group
          _ = c * k * c⁻¹ * a := by rw [hca]; group
    rw [commutatorElement_def]
    exact mul_mem hck (inv_mem (mem_sup_right hk))
  have hT₁C : T₁ ≤ centralizer (W : Set G) := (Subgroup.le_centralizer_iff).mp hWT
  have hT₁H : T₁ ≤ H :=
    (commutator_inf_K_eq h3 hf e hKL hKo hKH).symm.le.trans (Subgroup.commutator_mono hT₁C le_rfl)
  have hyC : y ∈ normalizer (centralizer (W : Set G) : Set G) := by
    rw [mem_normalizer_iff]
    intro c
    simp only [mem_centralizer_iff]
    constructor
    · intro hc w hw
      have hw' : y⁻¹ * w * y ∈ W := by simpa using (mem_normalizer_iff.mp (inv_mem hyW) w).mp hw
      have h1 := hc _ hw'
      calc w * (y * c * y⁻¹) = y * ((y⁻¹ * w * y) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * w * y)) * y⁻¹ := by rw [h1]
        _ = y * c * y⁻¹ * w := by group
    · intro hc w hw
      have hw' : y * w * y⁻¹ ∈ W := (mem_normalizer_iff.mp hyW w).mp hw
      have h1 := hc _ hw'
      calc w * c = y⁻¹ * ((y * w * y⁻¹) * (y * c * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * c * y⁻¹) * (y * w * y⁻¹)) * y := by rw [h1]
        _ = c * w := by group
  have hyC' : (centralizer (W : Set G)).map (MulAut.conj y).toMonoidHom = centralizer (W : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp hyC
  have hyK' : K.map (MulAut.conj y).toMonoidHom = K := mem_normalizer_iff_map_conj_eq.mp hyK
  have hyH : H.map (MulAut.conj y).toMonoidHom = H := by
    rw [hHdef, Subgroup.map_commutator, hyC', hyK']
  have hT₁syl : IsSylowOf 2 T₁ (T₁ ⊔ K) := by
    refine h3.isSylowOf_T₁.of_le le_sup_left ?_
    rw [hKH]
    exact inf_le_left.trans inf_le_left
  have hTKN : T₁ ⊔ K ≤ normalizer (T₁ : Set G) := by
    rw [hKH]
    exact inf_le_left.trans inf_le_right
  have hmap : T₁.map (MulAut.conj y).toMonoidHom ≤ T₁ := by
    have hle : T₁.map (MulAut.conj y).toMonoidHom ≤ T₁ ⊔ K := by
      calc T₁.map (MulAut.conj y).toMonoidHom ≤ H.map (MulAut.conj y).toMonoidHom :=
            Subgroup.map_mono hT₁H
        _ = H := hyH
        _ ≤ T₁ ⊔ K := hHle
    have hp : IsPGroup 2 (T₁.map (MulAut.conj y).toMonoidHom) := hT₁syl.isPGroup.map _
    have hp' : IsPGroup 2 (T₁.map (MulAut.conj y).toMonoidHom ⊔ T₁ : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hp hT₁syl.isPGroup (hle.trans hTKN)
    have heq := hT₁syl.eq_of_le le_sup_right (sup_le hle le_sup_left) hp'
    exact le_sup_left.trans heq.le
  have hcard : Nat.card (T₁.map (MulAut.conj y).toMonoidHom) = Nat.card T₁ :=
    card_map_of_injective (MulAut.conj y).injective
  exact mem_normalizer_iff_map_conj_eq.mpr (eq_of_le_of_card_ge hmap hcard.ge)

end Sec3

end CFSG.ComponentClassification.GMS78
