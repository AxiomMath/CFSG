module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (g y : G) :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    refine ⟨g⁻¹ * y * g, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem coe_smul_sylow_eq_map {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (g : G)
    (P : Sylow p G) :
    ((g • P : Sylow p G) : Subgroup G) = (P : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map_conj_iff]
  rw [MulAut.smul_def]
  simp [MulAut.conj_inv_apply]

theorem isPGroup_pCoreOf (p : ℕ) {G : Type*} [Group G] (P : Subgroup G) :
    IsPGroup p ↥(CFSG.Open.pCoreOf p P) :=
  (CFSG.pCore_isPGroup (p := p) (G := ↥P)).map P.subtype

theorem pCoreOf_le_self (p : ℕ) {G : Type*} [Group G] (P : Subgroup G) :
    CFSG.Open.pCoreOf p P ≤ P := by
  rintro _ ⟨t, -, rfl⟩
  exact t.2

theorem conj_mem_pCoreOf (p : ℕ) {G : Type*} [Group G] (P : Subgroup G) :
    ∀ x ∈ P, ∀ y ∈ CFSG.Open.pCoreOf p P, x * y * x⁻¹ ∈ CFSG.Open.pCoreOf p P := by
  rintro x hx _ ⟨t, ht, rfl⟩
  refine ⟨⟨x, hx⟩ * t * ⟨x, hx⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pCore_normal (p := p) (G := ↥P)).conj_mem t ht ⟨x, hx⟩

theorem card_sup_mul_card_inf_of_normal {X : Type*} [Group X] (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc _ hAN, hc _ hB] at h
  exact h

theorem exists_conj_mem_of_not_dvd_relIndex {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] {H P : Subgroup G} (hHP : H ≤ P) (hidx : ¬ p ∣ H.relIndex P) {z : G}
    (hz : z ∈ P) (hzp : z ^ p = 1) : ∃ x ∈ P, x * z * x⁻¹ ∈ H := by
  classical
  set H' : Subgroup P := H.subgroupOf P with hH'
  have hidx' : ¬ p ∣ H'.index := hidx
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p H'))
  have hcQ : Nat.card Q = p ^ (Nat.card H').factorization p := Q.card_eq_multiplicity
  have hmul : H'.index * Nat.card H' = Nat.card P := Subgroup.index_mul_card H'
  have hfac : (Nat.card P).factorization p = (Nat.card H').factorization p := by
    rw [← hmul, Nat.factorization_mul (Subgroup.index_ne_zero_of_finite) Nat.card_pos.ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hidx']
  set S0 : Subgroup P := (Q : Subgroup H').map H'.subtype with hS0
  have hcS0 : Nat.card S0 = p ^ (Nat.card P).factorization p := by
    rw [hS0, Subgroup.card_map_of_injective H'.subtype_injective, hcQ, hfac]
  let S : Sylow p P := Sylow.ofCard S0 hcS0
  have hSS : (S : Subgroup P) = S0 := rfl
  have hap : (⟨z, hz⟩ : P) ^ p = 1 := Subtype.ext hzp
  have hcyc : IsPGroup p (Subgroup.zpowers (⟨z, hz⟩ : P)) := by
    have hord : orderOf (⟨z, hz⟩ : P) ∣ p := orderOf_dvd_of_pow_eq_one hap
    rcases (Nat.dvd_prime hp.out).1 hord with h1 | h1
    · refine IsPGroup.of_card (n := 0) ?_
      rw [Nat.card_zpowers, h1]; simp
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, h1]; simp
  obtain ⟨S₂, hS₂⟩ := hcyc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S S₂
  have haS₂ : (⟨z, hz⟩ : P) ∈ (S₂ : Subgroup P) := hS₂ (Subgroup.mem_zpowers _)
  rw [← hg] at haS₂
  have hmem : g⁻¹ * (⟨z, hz⟩ : P) * g ∈ (S : Subgroup P) := by
    have h := haS₂
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h
    have e : (MulAut.conj g)⁻¹ • (⟨z, hz⟩ : P) = g⁻¹ * ⟨z, hz⟩ * g := by
      rw [MulAut.smul_def]
      simp [MulAut.conj_inv_apply]
    rwa [e] at h
  rw [hSS, hS0, Subgroup.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  refine ⟨((g⁻¹ : P) : G), (g⁻¹).2, ?_⟩
  have hyH : (((y : H') : P) : G) ∈ H := Subgroup.mem_subgroupOf.1 y.2
  have hyeq : (((y : H') : P) : G) = ((g⁻¹ : P) : G) * z * (((g⁻¹ : P) : G))⁻¹ := by
    have := congrArg (fun w : P => (w : G)) hy
    simpa using this
  rw [← hyeq]
  exact hyH

theorem le_sylow_of_normal_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (S : Sylow p X) {P R : Subgroup X} (hSP : (S : Subgroup X) ≤ P) (hRP : R ≤ P)
    (hR : IsPGroup p R) (hRn : ∀ x ∈ P, ∀ y ∈ R, x * y * x⁻¹ ∈ R) : R ≤ S := by
  have hnorm : (R.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hRn (g : X) g.2 (n : X) hn
    simpa using this⟩
  have hp : IsPGroup p (R.subgroupOf P) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  have h := hp.le_sylow_of_normal (S.subtype hSP)
  intro r hr
  exact h (show (⟨r, hRP hr⟩ : P) ∈ R.subgroupOf P from hr)

theorem two_part_centralizer_le {X : Type*} [Group X] [Finite X] (U H : Subgroup X)
    (Fam : Set (Subgroup X)) (N : ℕ) (hN : 1 ≤ N) (hU : ∃ S : Sylow 2 X, (S : Subgroup X) = U)
    (hP : ∀ P ∈ Fam, U ≤ P ∧ H ≤ P ∧ ¬ 3 ∣ H.relIndex P)
    (hBT : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
      ∃ g : X, ∃ P ∈ Fam, ∃ R : Subgroup X, R ≤ P ∧ IsPGroup 2 R ∧
        (∀ x ∈ P, ∀ y ∈ R, x * y * x⁻¹ ∈ R) ∧ T.map (MulAut.conj g).toMonoidHom ≤ R ∧
        (Subgroup.normalizer (T : Set X)).map (MulAut.conj g).toMonoidHom ≤ P)
    (hH : ∀ h ∈ H, h ^ 3 = 1 → h ≠ 1 → Nat.card ↥(U ⊓ Subgroup.centralizer {h}) ≤ N) :
    ∀ z : X, z ^ 3 = 1 → z ≠ 1 →
      2 ^ (Nat.card (Subgroup.centralizer ({z} : Set X))).factorization 2 ≤ N := by
  intro z hz3 hz1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, rfl⟩ := hU
  set C := Subgroup.centralizer ({z} : Set X) with hC
  obtain ⟨T0⟩ := (inferInstance : Nonempty (Sylow 2 C))
  set T : Subgroup X := (T0 : Subgroup C).map C.subtype with hT
  have hTcard : Nat.card T = 2 ^ (Nat.card C).factorization 2 := by
    rw [hT, Subgroup.card_map_of_injective C.subtype_injective]
    exact T0.card_eq_multiplicity
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := (Nat.card C).factorization 2) hTcard
  rw [← hTcard]
  by_cases hT1 : T = ⊥
  · rw [hT1]
    simpa using hN
  obtain ⟨g, P, hPF, R, hRP, hR2, hRn, hTR, hNP⟩ := hBT T hT1 hT2
  obtain ⟨hUP, hHP, hidx⟩ := hP P hPF
  have hcomm : ∀ t ∈ T, t * z = z * t := fun t ht => by
    exact (Subgroup.mem_centralizer_singleton_iff (g := z) (k := t)).1 (hTC ht)
  have hzc : z ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact hcomm t ht
  have hzN : z ∈ Subgroup.normalizer (T : Set X) := Subgroup.centralizer_le_normalizer _ hzc
  have hz'P : g * z * g⁻¹ ∈ P := hNP ⟨z, hzN, by simp [MulAut.conj_apply]⟩
  have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
    have := congrArg (fun w => g * w * g⁻¹) hz3
    simpa [conj_pow] using this
  obtain ⟨x, hxP, hxH⟩ := exists_conj_mem_of_not_dvd_relIndex hHP hidx hz'P hz'3
  set k : X := x * g with hk
  have hkz : x * (g * z * g⁻¹) * x⁻¹ = k * z * k⁻¹ := by simp [hk, mul_assoc]
  rw [hkz] at hxH
  have hh3 : (k * z * k⁻¹) ^ 3 = 1 := by
    have := congrArg (fun w => k * w * k⁻¹) hz3
    simpa [conj_pow] using this
  have hh1 : k * z * k⁻¹ ≠ 1 := fun h => hz1 (by
    have : k * z * k⁻¹ = k * 1 * k⁻¹ := by simpa using h
    simpa using this)
  have hle : T.map (MulAut.conj k).toMonoidHom ≤
      (S : Subgroup X) ⊓ Subgroup.centralizer {k * z * k⁻¹} := by
    rintro _ ⟨t, ht, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : g * t * g⁻¹ ∈ R := hTR ⟨t, ht, by simp [MulAut.conj_apply]⟩
      have h2 := hRn x hxP _ h1
      have h3 : x * (g * t * g⁻¹) * x⁻¹ = (MulAut.conj k).toMonoidHom t := by
        simp [hk, MulAut.conj_apply, mul_assoc]
      rw [h3] at h2
      exact le_sylow_of_normal_isPGroup S hUP hRP hR2 hRn h2
    · rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := hcomm t ht
      calc k * t * k⁻¹ * (k * z * k⁻¹) = k * (t * z) * k⁻¹ := by group
        _ = k * (z * t) * k⁻¹ := by rw [this]
        _ = k * z * k⁻¹ * (k * t * k⁻¹) := by group
  calc Nat.card T = Nat.card (T.map (MulAut.conj k).toMonoidHom) :=
        (Subgroup.card_map_of_injective (MulAut.conj k).injective).symm
    _ ≤ Nat.card ↥((S : Subgroup X) ⊓ Subgroup.centralizer {k * z * k⁻¹}) :=
        Subgroup.card_le_of_le hle
    _ ≤ N := hH _ hxH hh3 hh1

theorem two_part_centralizer_le_of_injective {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (ψ : X →* Y) (hψ : Function.Injective ψ) (z : X) :
    2 ^ (Nat.card (Subgroup.centralizer ({z} : Set X))).factorization 2 ≤
      2 ^ (Nat.card (Subgroup.centralizer ({ψ z} : Set Y))).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite X := Finite.of_injective ψ hψ
  set C := Subgroup.centralizer ({z} : Set X) with hC
  obtain ⟨T0⟩ := (inferInstance : Nonempty (Sylow 2 C))
  set T : Subgroup X := (T0 : Subgroup C).map C.subtype with hT
  have hTcard : Nat.card T = 2 ^ (Nat.card C).factorization 2 := by
    rw [hT, Subgroup.card_map_of_injective C.subtype_injective]
    exact T0.card_eq_multiplicity
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hle : T.map ψ ≤ Subgroup.centralizer ({ψ z} : Set Y) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      (Subgroup.mem_centralizer_singleton_iff).1 (hTC ht)]
  have hdvd : Nat.card (T.map ψ) ∣ Nat.card (Subgroup.centralizer ({ψ z} : Set Y)) :=
    Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hψ, hTcard] at hdvd
  have hpos : Nat.card (Subgroup.centralizer ({ψ z} : Set Y)) ≠ 0 := Nat.card_pos.ne'
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 hdvd
  exact Nat.pow_le_pow_right (by norm_num) this

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
