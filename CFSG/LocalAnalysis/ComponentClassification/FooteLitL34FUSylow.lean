module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUField
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitL34FUSixteen

public section

namespace CFSG.ComponentClassification.TBLit.L34FU

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.Sol76
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem isSylowOf_of_isSylowTwoIn {S H : Subgroup X} (hS : IsSylowTwoIn S H) :
    ABGLocalTools.IsSylowOf 2 S H := by
  obtain ⟨hSH, Q, hQ⟩ := hS
  refine ⟨Q, ?_⟩
  rw [hQ, subgroupOf_map_subtype, inf_eq_left.mpr hSH]

theorem isSylowTwoIn_inf {S H K : Subgroup X} (hS : IsSylowTwoIn S H) (hKH : K ≤ H)
    (hHK : H ≤ normalizer (K : Set X)) : IsSylowTwoIn (S ⊓ K) K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := ((isSylowOf_of_isSylowTwoIn hS).inf_of_le_normalizer hKH hHK
    ).exists_sylow_eq_subgroupOf
  exact ⟨inf_le_right, Q, hQ⟩

theorem isSylowTwoIn_of_card {P K K' : Subgroup X} (hP : IsSylowTwoIn P K) (hPK' : P ≤ K')
    (hc : Nat.card K' = Nat.card K) : IsSylowTwoIn P K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPK, Q, hQ⟩ := hP
  have hcQ : Nat.card (Q : Subgroup ↥K) = 2 ^ (Nat.card ↥K).factorization 2 :=
    Sylow.card_eq_multiplicity Q
  have hcP : Nat.card ↥(P.subgroupOf K') = 2 ^ (Nat.card ↥K').factorization 2 := by
    rw [hc, ← hcQ, hQ, Nat.card_congr (subgroupOfEquivOfLe hPK').toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv]
  exact ⟨hPK', Sylow.ofCard _ hcP, rfl⟩

omit [Finite X] in
theorem exists_orderOf_eq_two_pow {P : Subgroup X} (hP : IsPGroup 2 P) {g : X} (hg : g ∈ P) :
    ∃ k : ℕ, orderOf g = 2 ^ k := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  have h1 : orderOf g ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact ⟨m, hm⟩

theorem conj_mem_of_coreActionKernel (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hbK : b ∈ K) {S : Subgroup X} (hS : IsSylowTwoIn S (centralizer ({b} : Set X))) {t : X}
    (hc : t⁻¹ * b * t ∈ coreActionKernel K)
    (hcS : ∀ s ∈ S, s * (t⁻¹ * b * t) = t⁻¹ * b * t * s) : t⁻¹ * b * t ∈ K := by
  set c := t⁻¹ * b * t with hcdef
  have hc2 : orderOf c = 2 := by rw [hcdef, orderOf_conj, hb]
  have hcp : IsPGroup 2 (zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  have hNK := centralizer_le_normalizer h13 hnab hKP hb hK hKmax hKl
  have hPK : IsSylowTwoIn (S ⊓ K) K := isSylowTwoIn_inf hS hK.1 hNK
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  have hle : S ⊓ K ≤ conjugate K t := by
    intro p hp
    obtain ⟨hpS, hpK⟩ := mem_inf.mp hp
    obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow hS2 hpS
    exact twoLayerIn_le_conjugate h13 hnab hKP hb hK hKmax hKl t hc
      (mem_twoLayerIn_of_pow hK hcp hc hpK (hcS p hpS) hk)
  have hPKt : IsSylowTwoIn (S ⊓ K) (conjugate K t) :=
    isSylowTwoIn_of_card hPK hle (card_map_of_injective (MulAut.conj t⁻¹).injective)
  have hcKt : c ∈ conjugate K t := ⟨b, hbK, by simp [hcdef]⟩
  have hccen : ∀ k ∈ conjugate K t, k * c = c * k := by
    rintro _ ⟨k, hk, rfl⟩
    have hkb := mem_centralizer_singleton_iff.mp (hK.1 hk)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hcdef]
    calc t⁻¹ * k * t * (t⁻¹ * b * t) = t⁻¹ * (k * b) * t := by group
      _ = t⁻¹ * (b * k) * t := by rw [hkb]
      _ = t⁻¹ * b * t * (t⁻¹ * k * t) := by group
  exact (mem_inf.mp (mem_of_isSylowTwoIn_of_central hPKt hcKt hccen hc2)).2

theorem conj_eq_of_normalizer (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hbK : b ∈ K) (h16 : Nat.card (zStarIn K) = 16 * Nat.card (oddIn K)) {v : X}
    (hv : HarrisLit.EndB.IsL34Field K v) {S : Subgroup X}
    (hS : IsSylowTwoIn S (centralizer ({b} : Set X))) (hvS : v ∈ S) {r : X} (hrS : r ∈ S)
    (hr8 : r ^ 8 = b) {t : X} (ht : t ∈ normalizer (S : Set X)) : t⁻¹ * b * t = b := by
  have hKperf : ⁅K, K⁆ = K := UnbalancedCorr.commutator_eq_of_isPComponent hK.1 hK.2
  have hNK := centralizer_le_normalizer h13 hnab hKP hb hK hKmax hKl
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hSb : ∀ s ∈ S, s * b = b * s := fun s hs => mem_centralizer_singleton_iff.mp (hS.1 hs)
  have htS : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => (mem_normalizer_iff.mp ht s).mp hs
  have htS' : ∀ s ∈ S, t⁻¹ * s * t ∈ S := fun s hs => by
    have := (mem_normalizer_iff.mp (inv_mem ht) s).mp hs
    rwa [inv_inv] at this
  set c := t⁻¹ * b * t with hcdef
  have hc2 : orderOf c = 2 := by rw [hcdef, orderOf_conj, hb]
  have hcS : ∀ s ∈ S, s * c = c * s := by
    intro s hs
    have h1 := hSb _ (htS s hs)
    calc s * c = t⁻¹ * ((t * s * t⁻¹) * b) * t := by rw [hcdef]; group
      _ = t⁻¹ * (b * (t * s * t⁻¹)) * t := by rw [h1]
      _ = c * s := by rw [hcdef]; group
  have hc : c ∈ coreActionKernel K :=
    mem_coreActionKernel_of_pow_eight hKperf hKl hbb hr8 (hNK (hS.1 (htS' r hrS)))
  have hcK : c ∈ K := conj_mem_of_coreActionKernel h13 hnab hKP hb hK hKmax hKl hbK hS hc hcS
  have hcZ : c ∈ zStarIn K := by
    rw [zStarIn, GSThmB.map_fusionZStar_eq]
    exact mem_inf.mpr ⟨hcK, hc⟩
  have hbcen : ∀ k ∈ K, k * b = b * k := fun k hk => mem_centralizer_singleton_iff.mp (hK.1 hk)
  have hbZ : b ∈ zStarIn K := by
    rw [zStarIn, GSThmB.map_fusionZStar_eq]
    refine mem_inf.mpr ⟨hbK, mem_coreActionKernel.mpr ⟨le_normalizer hbK, fun j hj => ?_⟩⟩
    have e : j⁻¹ * b⁻¹ * j * b = 1 := by
      rw [show j⁻¹ * b⁻¹ * j * b = j⁻¹ * (b⁻¹ * (j * b)) by group, hbcen j hj,
        inv_mul_cancel_left, inv_mul_cancel]
    rw [e]
    exact one_mem _
  have hvN : v ∈ normalizer (K : Set X) := hv.1
  obtain ⟨P, hP, hvP⟩ := exists_sylowTwoIn_normalized (T := zpowers v)
    (isPGroup_sup_zpowers hv.2.1 hv.2.1 rfl |>.to_le (le_sup_left)) (zpowers_le.mpr hvN)
  obtain ⟨q, l, hQS, -, -, -, hzz, hinj⟩ :=
    exists_field_frame16 hKperf hKl hvN hv h16 hP (hvP (mem_zpowers v))
  exact eq_of_mem_zStarIn hQS hzz hinj hcZ hbZ hc2 hb (hcS v hvS).symm (hSb v hvS).symm
    (hcS b (mem_of_isSylowTwoIn_of_central hS (mem_centralizer_singleton_iff.mpr rfl)
      (fun k hk => mem_centralizer_singleton_iff.mp hk) hb)).symm

theorem exists_sylow_eq (h13 : Sol76T13.SolomonThm13Simple) [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X) {b : X}
    (hb : orderOf b = 2) {K : Subgroup X} (hK : IsTwoComponentIn K (centralizer ({b} : Set X)))
    (hKmax : IsSolomonMaximal K) (hKl : GrSLit.IsL34Type (↥K ⧸ Open.fusionZStar ↥K))
    (hbK : b ∈ K) (h16 : Nat.card (zStarIn K) = 16 * Nat.card (oddIn K)) {v : X}
    (hv : HarrisLit.EndB.IsL34Field K v) {S : Subgroup X}
    (hS : IsSylowTwoIn S (centralizer ({b} : Set X))) (hvS : v ∈ S) {r : X} (hrS : r ∈ S)
    (hr8 : r ^ 8 = b) : ∃ T : Sylow 2 X, (T : Subgroup X) = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := isPGroup_of_isSylowTwoIn hS
  obtain ⟨T, hST⟩ := hS2.exists_le_sylow
  refine ⟨T, ?_⟩
  by_contra hne
  have hlt : S.subgroupOf (T : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm (fun x hx => ?_) hST)
    have : (⟨x, hx⟩ : ↥(T : Subgroup X)) ∈ S.subgroupOf (T : Subgroup X) := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hnil : Group.IsNilpotent ↥(T : Subgroup X) := T.isPGroup'.isNilpotent
  obtain ⟨t', ht'N, ht'S⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  set t : X := (t' : X) with htdef
  have htT : t ∈ (T : Subgroup X) := t'.2
  have ht : t ∈ normalizer (S : Set X) := by
    rw [mem_normalizer_iff]
    intro h
    have hiff := mem_normalizer_iff.mp ht'N
    constructor
    · intro hh
      have := (hiff ⟨h, hST hh⟩).mp (mem_subgroupOf.mpr hh)
      exact mem_subgroupOf.mp this
    · intro hh
      have hhT : h ∈ (T : Subgroup X) := by
        have e : h = t⁻¹ * (t * h * t⁻¹) * t := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem htT) (hST hh)) htT
      have := (hiff ⟨h, hhT⟩).mpr (mem_subgroupOf.mpr hh)
      exact mem_subgroupOf.mp this
  have htS : t ∉ S := fun h => ht'S (mem_subgroupOf.mpr h)
  have hbt := conj_eq_of_normalizer h13 hnab hKP hb hK hKmax hKl hbK h16 hv hS hvS hrS hr8 ht
  have htb : t ∈ centralizer ({b} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc t * b = t * (t⁻¹ * b * t) := by rw [hbt]
      _ = b * t := by group
  obtain ⟨hSC, Q, hQ⟩ := hS
  have hQ' : IsPGroup 2 ↥((S ⊔ zpowers t).subgroupOf (centralizer ({b} : Set X))) := by
    have h1 : IsPGroup 2 ↥(S ⊔ zpowers t) :=
      T.isPGroup'.to_le (sup_le hST (zpowers_le.mpr htT))
    exact h1.comap_subtype (K := centralizer ({b} : Set X))
  have hle : (Q : Subgroup ↥(centralizer ({b} : Set X))) ≤
      (S ⊔ zpowers t).subgroupOf (centralizer ({b} : Set X)) := by
    rw [hQ]
    exact fun x hx => mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  have heq := Q.is_maximal' hQ' hle
  apply htS
  have hmem : (⟨t, htb⟩ : ↥(centralizer ({b} : Set X))) ∈
      (S ⊔ zpowers t).subgroupOf (centralizer ({b} : Set X)) :=
    mem_subgroupOf.mpr (mem_sup_right (mem_zpowers t))
  rw [heq, hQ] at hmem
  exact mem_subgroupOf.mp hmem

end CFSG.ComponentClassification.TBLit.L34FU
