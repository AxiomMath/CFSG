module

public import CFSG.LocalAnalysis.ABGTheoremB.ClaimR23
import CFSG.GroupTheory.ABGDGroups.LinearCentralizers
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.ABGTheoremB.V5Tools
import CFSG.LocalAnalysis.ABGTheoremB.IV2

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open CFSG.GorensteinWalter (PGammaL2 PGL2 pGammaL2PSLRange pGammaL2PGLRange
  mem_pGammaL2PSLRange_iff)
open CFSG.ABGDGroups (IsLinearDecomposition linearCore)

section General

variable {H : Type*} [Group H]

private theorem lif_mem_normalizer_of_conj_mem [Finite H] {J : Subgroup H} {g : H}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem lif_mem_normalizer_of_mem_centralizer [Finite H] {J : Subgroup H} {g : H}
    (hg : g ∈ Subgroup.centralizer (J : Set H)) : g ∈ Subgroup.normalizer (J : Set H) := by
  apply lif_mem_normalizer_of_conj_mem
  intro y hy
  rw [← (Subgroup.mem_centralizer_iff.mp hg) y hy, mul_inv_cancel_right]
  exact hy

private theorem lif_normalizer_le_normalizer_map [Finite H] {Y : Subgroup H} (A : Subgroup Y)
    [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set H) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup H) : Set H) := by
  intro g hg
  apply lif_mem_normalizer_of_conj_mem
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
  have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
    rw [hfix]
    exact ha
  refine ⟨_, hmem, ?_⟩
  change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : H) = g * a * g⁻¹
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem lif_normal_of_commutator_le {K : Subgroup H} (hK : commutator H ≤ K) :
    K.Normal := by
  refine ⟨fun k hk g => ?_⟩
  have hc : g * k * g⁻¹ * k⁻¹ ∈ K := hK (Subgroup.commutator_mem_commutator
    (Subgroup.mem_top g) (Subgroup.mem_top k))
  have h := K.mul_mem hc hk
  rwa [inv_mul_cancel_right] at h

private theorem lif_isSylowOf_map [Finite H] {p : ℕ} [Fact p.Prime] {N : Subgroup H} [N.Normal]
    {A B : Subgroup H} (h : IsSylowOf p A B) :
    IsSylowOf p (A.map (QuotientGroup.mk' N)) (B.map (QuotientGroup.mk' N)) := by
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hAB, hA, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hAB, hA.map _, fun hdvd' => hdvd ?_⟩
  rw [← Subgroup.relIndex_comap, QuotientGroup.comap_map_mk'] at hdvd'
  exact hdvd'.trans (Subgroup.relIndex_dvd_of_le_left _ le_sup_right)

private theorem lif_commute_of_dihedral {Y : Subgroup H} {m : ℕ} (e : Y ≃* DihedralGroup m)
    {p : ℕ} (hp : Odd p) {a b : H} (ha : a ∈ Y) (hb : b ∈ Y) {i j : ℕ} (hai : a ^ p ^ i = 1)
    (hbj : b ^ p ^ j = 1) : a * b = b * a := by
  have hrot : ∀ c : H, ∀ hc : c ∈ Y, ∀ k : ℕ, c ^ p ^ k = 1 →
      ∃ t, e ⟨c, hc⟩ = DihedralGroup.r t := by
    intro c hc k hck
    rcases h : e ⟨c, hc⟩ with t | t
    · exact ⟨t, rfl⟩
    · exfalso
      have h1 : (⟨c, hc⟩ : Y) ^ p ^ k = 1 := Subtype.ext (by simpa using hck)
      have h2 : (e ⟨c, hc⟩) ^ p ^ k = 1 := by rw [← map_pow, h1, map_one]
      rw [h] at h2
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [DihedralGroup.orderOf_sr] at h3
      exact (Nat.not_even_iff_odd.mpr hp.pow) (even_iff_two_dvd.mpr h3)
  obtain ⟨s, hs⟩ := hrot a ha i hai
  obtain ⟨t, ht⟩ := hrot b hb j hbj
  have h : e (⟨a, ha⟩ * ⟨b, hb⟩) = e (⟨b, hb⟩ * ⟨a, ha⟩) := by
    rw [map_mul, map_mul, hs, ht, DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  exact congrArg Subtype.val (e.injective h)

private def lif_pPart {p : ℕ} (Y : Subgroup H)
    (hY : ∀ a ∈ Y, ∀ b ∈ Y, ∀ i j : ℕ, a ^ p ^ i = 1 → b ^ p ^ j = 1 → a * b = b * a) :
    Subgroup H where
  carrier := {y | y ∈ Y ∧ ∃ k : ℕ, y ^ p ^ k = 1}
  mul_mem' := by
    rintro a b ⟨ha, i, hai⟩ ⟨hb, j, hbj⟩
    refine ⟨Y.mul_mem ha hb, i + j, ?_⟩
    have hab : Commute a b := hY a ha b hb i j hai hbj
    rw [hab.mul_pow, pow_add, pow_mul, hai, one_pow, one_mul, mul_comm, pow_mul, hbj, one_pow]
  one_mem' := ⟨Y.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, i, hai⟩
    exact ⟨Y.inv_mem ha, i, by rw [inv_pow, hai, inv_one]⟩

end General

section Linear

variable {H : Type} [Group H] [Finite H] {F : Type} [Field F] [Finite F]
  {ι : H →* PGammaL2 F} {L E : Subgroup H} {S : Sylow 2 H}

omit [Finite F] in
private theorem lif_nonempty_comap_inl_mulEquiv {A : Subgroup (PGammaL2 F)}
    (hA : A ≤ pGammaL2PGLRange F) :
    Nonempty (A.comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F) ≃* A) :=
  ⟨((A.comap SemidirectProduct.inl).equivMapOfInjective _ SemidirectProduct.inl_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hA))⟩

private theorem lif_isCyclic_of_le_linearCore (hd : IsLinearDecomposition ι L E S)
    {T : Subgroup H} (hT : IsKleinFour T) {K : Subgroup H}
    (hKT : T ≤ Subgroup.normalizer (K : Set H)) (hK : Odd (Nat.card K))
    (hKL₀ : K ≤ linearCore ι) : IsCyclic K := by
  have hF := hd.isOddPrimePower_card
  have hTL : T ≤ L := by
    obtain ⟨P, hTP⟩ := (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hT).exists_le_sylow
    exact hTP.trans (hd.sylow_le P)
  have hKL₀' : K.map ι ≤ pGammaL2PSLRange F := Subgroup.map_le_iff_le_comap.mpr hKL₀
  have hTPGL : T.map ι ≤ pGammaL2PGLRange F := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · rw [ht1, map_one]
      exact Subgroup.one_mem _
    have h2 : orderOf t = 2 := by
      have h := Monoid.pow_exponent_eq_one (⟨t, ht⟩ : T)
      rw [hT.exponent_two] at h
      exact orderOf_eq_prime (by simpa using congrArg Subtype.val h) ht1
    exact hd.isStandardLayer.mem_pGLRange_of_orderOf_eq_two hF ⟨t, hTL ht, rfl⟩
      (by rw [orderOf_injective ι hd.injective, h2])
  set K₁ := (K.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  set T₁ := (T.map ι).comap (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hKPGL : K.map ι ≤ pGammaL2PGLRange F :=
    hKL₀'.trans CFSG.ABGDGroups.pGammaL2PSLRange_le_pGLRange
  obtain ⟨eK⟩ := lif_nonempty_comap_inl_mulEquiv hKPGL
  obtain ⟨eT⟩ := lif_nonempty_comap_inl_mulEquiv hTPGL
  let eK' : K ≃* K.map ι := K.equivMapOfInjective ι hd.injective
  let eT' : T ≃* T.map ι := T.equivMapOfInjective ι hd.injective
  have hK₁J : K₁ ≤ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    intro x hx
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).mp (hKL₀' hx)
    exact ⟨y, SemidirectProduct.inl_injective hy⟩
  have hK₁ : Odd (Nat.card K₁) := by
    rwa [Nat.card_congr eK.toEquiv, ← Nat.card_congr eK'.toEquiv]
  have hT₁ : IsKleinFour T₁ := by
    refine ⟨?_, ?_⟩
    · rw [Nat.card_congr eT.toEquiv, ← Nat.card_congr eT'.toEquiv]
      exact hT.card_four
    · rw [Monoid.exponent_eq_of_mulEquiv eT, ← Monoid.exponent_eq_of_mulEquiv eT']
      exact hT.exponent_two
  have hT₁K : T₁ ≤ Subgroup.normalizer (K₁ : Set (PGL2 F)) := by
    intro t ht
    apply Subgroup.mem_normalizer_fintype
    intro k hk
    have hN := Subgroup.le_normalizer_map ι
      (Subgroup.map_mono hKT (show SemidirectProduct.inl t ∈ T.map ι from ht))
    change SemidirectProduct.inl (t * k * t⁻¹) ∈ K.map ι
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hN _).mp hk
  have hcyc :=
    CFSG.ABGDGroups.pgl2_isCyclic_of_odd_of_kleinFour_le_normalizer hF hK₁J hK₁ hT₁ hT₁K
  exact (eK'.trans eK.symm).isCyclic.mpr hcyc

private theorem lif_le_centralizer (hd : IsLinearDecomposition ι L E S) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {D T : Subgroup H} (hT : IsKleinFour T) (hTD : T ≤ D) {x x₂ d : H}
    (hxD : x ∈ D) (hx2 : x * x = 1) (hx₂D : x₂ ∈ D) (hdD : d ∈ D) (hdx : d * x₂ * d⁻¹ = x * x₂)
    {U : Subgroup H} (hU : IsPGroup p U) (hDU : D ≤ Subgroup.normalizer (U : Set H)) :
    U ≤ Subgroup.centralizer ({x} : Set H) := by
  classical
  have hL₀n : (linearCore ι).Normal := hd.linearCore_normal
  have hDX : D ≤ Subgroup.normalizer ((U ⊓ linearCore ι : Subgroup H) : Set H) := by
    intro g hg
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hDU hg, ?_⟩
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hX₀p : IsPGroup p (U ⊓ linearCore ι : Subgroup H) := hU.to_le inf_le_left
  have hcyc : IsCyclic (U ⊓ linearCore ι : Subgroup H) :=
    lif_isCyclic_of_le_linearCore hd hT (hTD.trans hDX) (odd_card_of_isPGroup hp2 hX₀p)
      inf_le_right
  have hx₂N := hDX hx₂D
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic
    (Subgroup.normalizerMonoidHom (U ⊓ linearCore ι) ⟨x₂, hx₂N⟩).toMonoidHom
  have hpow : ∀ y ∈ (U ⊓ linearCore ι : Subgroup H), x₂ * y * x₂⁻¹ = y ^ m := by
    intro y hy
    have h : (((Subgroup.normalizerMonoidHom (U ⊓ linearCore ι) ⟨x₂, hx₂N⟩) ⟨y, hy⟩ :
        ↥(U ⊓ linearCore ι)) : H) = ((⟨y, hy⟩ ^ m : ↥(U ⊓ linearCore ι)) : H) :=
      congrArg Subtype.val (hm ⟨y, hy⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    simpa using h
  have hdN := hDX hdD
  have hcent : ∀ w ∈ (U ⊓ linearCore ι : Subgroup H), x * w * x⁻¹ = w := by
    intro w hw
    obtain ⟨y, hy, hwy⟩ : ∃ y ∈ (U ⊓ linearCore ι : Subgroup H), w = x₂ * y * x₂⁻¹ :=
      ⟨x₂⁻¹ * w * x₂⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx₂N) w).mp hw,
        by group⟩
    obtain ⟨z, hz, hyz⟩ : ∃ z ∈ (U ⊓ linearCore ι : Subgroup H), y = d * z * d⁻¹ :=
      ⟨d⁻¹ * y * d⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdN) y).mp hy,
        by group⟩
    calc x * w * x⁻¹ = (x * x₂) * y * (x * x₂)⁻¹ := by rw [hwy]; group
      _ = d * (x₂ * z * x₂⁻¹) * d⁻¹ := by rw [← hdx, hyz]; group
      _ = d * z ^ m * d⁻¹ := by rw [hpow z hz]
      _ = (d * z * d⁻¹) ^ m := conj_zpow.symm
      _ = y ^ m := by rw [← hyz]
      _ = w := by rw [← hpow y hy, ← hwy]
  intro u hu
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxN := hDU hxD
  have hcU : u * x * u⁻¹ * x⁻¹ ∈ U := by
    have h1 : x * u⁻¹ * x⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hxN _).mp (U.inv_mem hu)
    have h2 := U.mul_mem hu h1
    rwa [show u * (x * u⁻¹ * x⁻¹) = u * x * u⁻¹ * x⁻¹ by group] at h2
  have hcL : u * x * u⁻¹ * x⁻¹ ∈ linearCore ι := hd.commutator_le_linearCore
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top u) (Subgroup.mem_top x))
  set c := u * x * u⁻¹ * x⁻¹ with hcdef
  have hcx : x * c * x⁻¹ = c := hcent c ⟨hcU, hcL⟩
  have e1 : u * x * u⁻¹ = c * x := by rw [hcdef]; group
  have e3 : c * x = x * c := by
    calc c * x = (x * c * x⁻¹) * x := by rw [hcx]
      _ = x * c := by group
  have hc2 : c * c = 1 := by
    calc c * c = c * c * (x * x) := by rw [hx2, mul_one]
      _ = c * (c * x) * x := by group
      _ = c * (x * c) * x := by rw [e3]
      _ = (c * x) * (c * x) := by group
      _ = (u * x * u⁻¹) * (u * x * u⁻¹) := by rw [e1]
      _ = u * (x * x) * u⁻¹ := by group
      _ = 1 := by rw [hx2, mul_one, mul_inv_cancel]
  have hc1 : c = 1 := by
    obtain ⟨k, hk⟩ := hU ⟨c, hcU⟩
    have hk' : c ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, hj⟩ : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    rwa [hj, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hk'
  calc u * x = (u * x * u⁻¹) * u := by group
    _ = x * u := by rw [e1, hc1, one_mul]

omit [Finite H] in
private theorem lif_exists_mul_eq (hd : IsLinearDecomposition ι L E S) {u : H} {n : ℕ}
    (hn : Odd n) (hu : u ^ n = 1) :
    ∃ l ∈ linearCore ι, ∃ e ∈ E, l * e = u ∧ e ^ n = 1 := by
  have hF := hd.isOddPrimePower_card
  have hL := hd.normal
  have hL₀n : (linearCore ι).Normal := hd.linearCore_normal
  have hcomm : ∀ a b : H, (QuotientGroup.mk' (linearCore ι) a) *
      (QuotientGroup.mk' (linearCore ι) b) =
      (QuotientGroup.mk' (linearCore ι) b) * (QuotientGroup.mk' (linearCore ι) a) := by
    intro a b
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h := hd.commutator_le_linearCore
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹))
    rw [commutatorElement_def] at h
    rwa [show (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ by group]
  have huLE : u ∈ L ⊔ E := by
    rw [hd.sup_eq_top]
    exact Subgroup.mem_top u
  obtain ⟨l, hl, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp huLE
  set π₀ := QuotientGroup.mk' (linearCore ι) with hπ₀
  have hl2 : π₀ l * π₀ l = 1 := by
    have hsq : ι l ^ 2 ∈ pGammaL2PSLRange F :=
      CFSG.ABGDGroups.sq_mem_pGammaL2PSLRange hF (hd.isStandardLayer.right_sq ⟨l, hl, rfl⟩)
    rw [← map_mul, hπ₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change ι (l * l) ∈ pGammaL2PSLRange F
    rwa [map_mul, ← sq]
  have hun : (π₀ l * π₀ e) ^ n = 1 := by rw [← map_mul, ← map_pow, hu, map_one]
  have hle : π₀ l * π₀ e ^ n = 1 := by
    obtain ⟨k, rfl⟩ := hn
    rw [(show Commute (π₀ l) (π₀ e) from hcomm l e).mul_pow, pow_succ, pow_mul, sq, hl2,
      one_pow, one_mul] at hun
    exact hun
  have hl₀ : l * e ^ n ∈ linearCore ι := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ₀, map_mul, map_pow]
    exact hle
  refine ⟨l * e ^ n, hl₀, (e ^ n)⁻¹ * e, E.mul_mem (E.inv_mem (E.pow_mem he n)) he,
    by group, ?_⟩
  have hmem : ((e ^ n)⁻¹ * e) ^ n ∈ linearCore ι := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ₀, map_pow, map_mul, map_inv,
      map_pow, inv_eq_of_mul_eq_one_left hle, hun]
  have hmemE : ((e ^ n)⁻¹ * e) ^ n ∈ E := E.pow_mem (E.mul_mem (E.inv_mem (E.pow_mem he n)) he) n
  have hbot : ((e ^ n)⁻¹ * e) ^ n ∈ L ⊓ E := ⟨hd.linearCore_le hmem, hmemE⟩
  rwa [hd.inf_eq_bot, Subgroup.mem_bot] at hbot

private theorem lif_dihedral (hd : IsLinearDecomposition ι L E S) {x : H} (hx : orderOf x = 2) :
    ∃ m : ℕ, (2 * m = Nat.card F + 1 ∨ 2 * m + 1 = Nat.card F) ∧
      Nonempty (↥(linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)) ≃* DihedralGroup m) := by
  have hF := hd.isOddPrimePower_card
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, f, -, hpodd, -, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · have hε : (Nat.card F : ℤ) ≡ 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-j, by rw [hk, hj]; push_cast; ring⟩
    by_cases hxL : x ∈ linearCore ι
    · obtain ⟨m, hm, he⟩ := hd.centralizer_dihedral_of_mem_linearCore hε (Or.inl rfl) hx hxL
      exact ⟨m, Or.inr (by omega), he⟩
    · obtain ⟨m, hm, he⟩ :=
        hd.centralizer_dihedral_of_not_mem_linearCore hε (Or.inl rfl) hx hxL
      exact ⟨m, Or.inl (by omega), he⟩
  · have hε : (Nat.card F : ℤ) ≡ -1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-j - 1, by rw [hk, hj]; push_cast; ring⟩
    by_cases hxL : x ∈ linearCore ι
    · obtain ⟨m, hm, he⟩ := hd.centralizer_dihedral_of_mem_linearCore hε (Or.inr rfl) hx hxL
      exact ⟨m, Or.inl (by omega), he⟩
    · obtain ⟨m, hm, he⟩ :=
        hd.centralizer_dihedral_of_not_mem_linearCore hε (Or.inr rfl) hx hxL
      exact ⟨m, Or.inr (by omega), he⟩

omit [Finite H] in
private theorem lif_eq_bot_of_card_three (hd : IsLinearDecomposition ι L E S)
    (h3 : Nat.card F = 3) : E = ⊥ := by
  have hAut : Nat.card (F ≃+* F) = 1 :=
    CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card F (p := 3) Nat.prime_three
      (by rw [h3, pow_one])
  have : Subsingleton (F ≃+* F) := (Nat.card_eq_one_iff_unique.mp hAut).1
  rw [eq_bot_iff]
  intro e he
  obtain ⟨σ', hσ'⟩ := hd.map_le_fieldRange ⟨e, he, rfl⟩
  rw [Subsingleton.elim σ' 1, map_one] at hσ'
  exact Subgroup.mem_bot.mpr (hd.injective (hσ'.symm.trans (map_one ι).symm))

private theorem lif_mem_of_isSylowOf (hd : IsLinearDecomposition ι L E S) {p : ℕ} [Fact p.Prime]
    {T : Subgroup H} (hT : IsKleinFour T) (hTS : T ≤ S) {P : Subgroup H}
    (hP : IsSylowOf p P (Subgroup.centralizer (T : Set H))) {e : H} (he : e ∈ E) {k : ℕ}
    (hek : e ^ p ^ k = 1) : e ∈ P := by
  have hC : Subgroup.centralizer (T : Set H) = T ⊔ E := (hd.centralizer_kleinFour hT hTS).1
  have hET : E ≤ Subgroup.centralizer (T : Set H) :=
    hd.le_centralizer.trans (Subgroup.centralizer_le hTS)
  have hEE : E ≤ Subgroup.centralizer (E : Set H) := by
    have := hd.isCyclic
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val ((IsCyclic.isMulCommutative (α := E)).is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  have hTE : E ≤ Subgroup.centralizer ((T ⊔ E : Subgroup H) : Set H) :=
    Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp hET) hEE)
  have hzp : IsPGroup p (Subgroup.zpowers e) := by
    rintro ⟨g, hg⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    change (e ^ i) ^ p ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hek, one_zpow]
  have hzN : Subgroup.zpowers e ≤ Subgroup.normalizer (P : Set H) := by
    rw [Subgroup.zpowers_le]
    exact lif_mem_normalizer_of_mem_centralizer
      (Subgroup.centralizer_le (hP.le.trans hC.le) (hTE he))
  have hR : IsPGroup p (Subgroup.zpowers e ⊔ P : Subgroup H) :=
    IsPGroup.to_sup_of_normal_right' hzp hP.isPGroup hzN
  have hRC : (Subgroup.zpowers e ⊔ P : Subgroup H) ≤ Subgroup.centralizer (T : Set H) :=
    sup_le (by rw [Subgroup.zpowers_le]; exact hET he) hP.le
  rw [← hP.eq_of_le le_sup_right hRC hR]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers e)

private theorem lif_main (hd : IsLinearDecomposition ι L E S) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {D T : Subgroup H} (hDS : D ≤ S) (hT : IsKleinFour T) (hTD : T ≤ D)
    {x x₂ d : H} (hxD : x ∈ D) (hxo : orderOf x = 2)
    (hxc : D ≤ Subgroup.centralizer ({x} : Set H)) (hx₂D : x₂ ∈ D) (hdD : d ∈ D)
    (hdx : d * x₂ * d⁻¹ = x * x₂) {U P : Subgroup H} (hU : IsPGroup p U)
    (hDU : D ≤ Subgroup.normalizer (U : Set H)) (hPU : P ≤ U)
    (hP : IsSylowOf p P (Subgroup.centralizer (T : Set H)))
    (hmax : ∀ Q : Subgroup H, IsPGroup p Q → D ≤ Subgroup.normalizer (Q : Set H) → U ≤ Q →
      Q = U) :
    U = ⊥ ∨ (3 < Nat.card F ∧ ∃ PE ≤ E,
      U = pCoreIn p ((linearCore ι ⊔ D) ⊓ Subgroup.centralizer ({x} : Set H)) ⊔ PE) := by
  classical
  have hpp : p.Prime := Fact.out
  have hx2 : x * x = 1 := by rw [← sq, ← hxo, pow_orderOf_eq_one]
  have hL₀n : (linearCore ι).Normal := hd.linearCore_normal
  have hUx : U ≤ Subgroup.centralizer ({x} : Set H) :=
    lif_le_centralizer hd hp2 hT hTD hxD hx2 hx₂D hdD hdx hU hDU
  have hEx : E ≤ Subgroup.centralizer ({x} : Set H) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hd.le_centralizer he)) x (hDS hxD)).symm
  have hdec : ∀ u ∈ U, ∃ k : ℕ, ∃ l ∈ linearCore ι ⊓ Subgroup.centralizer ({x} : Set H),
      ∃ e ∈ E, l * e = u ∧ e ^ p ^ k = 1 ∧ u ^ p ^ k = 1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hU ⟨u, hu⟩
    have hk' : u ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨l, hl, e, he, hle, hek⟩ := lif_exists_mul_eq hd (hpp.odd_of_ne_two hp2).pow hk'
    refine ⟨k, l, ⟨hl, ?_⟩, e, he, hle, hek, hk'⟩
    rw [show l = u * e⁻¹ by rw [← hle]; group]
    exact Subgroup.mul_mem _ (hUx hu) (Subgroup.inv_mem _ (hEx he))
  obtain ⟨m, hm, ⟨eY⟩⟩ := lif_dihedral hd hxo
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨r, f, -, hrodd, -, hq⟩ := hd.isOddPrimePower_card
    rw [hq]
    exact hrodd.pow
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  by_cases h3 : Nat.card F = 3
  ·
    left
    have hE : E = ⊥ := lif_eq_bot_of_card_three hd h3
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨k, l, hl, e, he, hle, -, huk⟩ := hdec u hu
    rw [hE, Subgroup.mem_bot] at he
    rw [he, mul_one] at hle
    subst hle
    have hcard : Nat.card (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) ∣
        2 ^ 2 := by
      rw [Nat.card_congr eY.toEquiv, DihedralGroup.nat_card]
      have hm2 : m = 1 ∨ m = 2 := by omega
      rcases hm2 with rfl | rfl <;> norm_num
    have ho1 : orderOf (⟨l, hl⟩ : (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H) :
        Subgroup H)) ∣ 2 ^ 2 := (orderOf_dvd_natCard _).trans hcard
    have ho2 : orderOf (⟨l, hl⟩ : (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H) :
        Subgroup H)) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using huk))
    have hcop : Nat.Coprime (2 ^ 2) (p ^ k) :=
      ((Nat.coprime_two_left.mpr (hpp.odd_of_ne_two hp2)).pow_left 2).pow_right k
    have ho : orderOf (⟨l, hl⟩ : (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H) :
        Subgroup H)) = 1 :=
      Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hcop ▸ Nat.dvd_gcd ho1 ho2)
    rw [orderOf_eq_one_iff] at ho
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val ho)
  ·
    right
    have h3' : 3 < Nat.card F := by
      obtain ⟨j, hj⟩ := hFodd
      omega
    refine ⟨h3', P ⊓ E, inf_le_right, ?_⟩
    have hcommY : ∀ a ∈ linearCore ι ⊓ Subgroup.centralizer ({x} : Set H),
        ∀ b ∈ linearCore ι ⊓ Subgroup.centralizer ({x} : Set H), ∀ i j : ℕ,
          a ^ p ^ i = 1 → b ^ p ^ j = 1 → a * b = b * a :=
      fun a ha b hb i j hai hbj =>
        lif_commute_of_dihedral eY (hpp.odd_of_ne_two hp2) ha hb hai hbj
    set Q₀ := lif_pPart (p := p) (linearCore ι ⊓ Subgroup.centralizer ({x} : Set H)) hcommY
      with hQ₀def
    set Y := (linearCore ι ⊔ D) ⊓ Subgroup.centralizer ({x} : Set H) with hYdef
    have hQ₀p : IsPGroup p Q₀ := by
      rintro ⟨y, -, k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hQ₀Y : Q₀ ≤ Y := fun y hy => ⟨Subgroup.mem_sup_left hy.1.1, hy.1.2⟩
    have hYN : Y ≤ Subgroup.normalizer (Q₀ : Set H) := by
      intro g hg
      apply lif_mem_normalizer_of_conj_mem
      rintro y ⟨⟨hyL, hyx⟩, k, hk⟩
      refine ⟨⟨hL₀n.conj_mem y hyL g, ?_⟩, k, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg.2 hyx) (Subgroup.inv_mem _ hg.2)
      · rw [conj_pow, hk, mul_one, mul_inv_cancel]
    have hQ₀O : Q₀ ≤ pCoreIn p Y := V56.le_pCoreIn hQ₀Y hYN hQ₀p
    have hLDn : (linearCore ι ⊔ D).Normal :=
      lif_normal_of_commutator_le (hd.commutator_le_linearCore.trans le_sup_left)
    have hCN : Subgroup.centralizer ({x} : Set H) ≤ Subgroup.normalizer (Y : Set H) := by
      intro g hg
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, Subgroup.le_normalizer hg⟩
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top g
    have hYO : Subgroup.normalizer (Y : Set H) ≤ Subgroup.normalizer (pCoreIn p Y : Set H) :=
      lif_normalizer_le_normalizer_map (CFSG.pCore p Y)
    have hPEN : P ⊓ E ≤ Subgroup.normalizer (pCoreIn p Y : Set H) :=
      inf_le_right.trans (hEx.trans (hCN.trans hYO))
    have hQp : IsPGroup p (pCoreIn p Y ⊔ P ⊓ E : Subgroup H) :=
      IsPGroup.to_sup_of_normal_left' (V56.isPGroup_pCoreIn p Y) hP.isPGroup.to_inf_left hPEN
    have hDQ : D ≤ Subgroup.normalizer ((pCoreIn p Y ⊔ P ⊓ E : Subgroup H) : Set H) := by
      intro g hg
      refine Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hYO (hCN (hxc hg)), ?_⟩
      apply lif_mem_normalizer_of_mem_centralizer
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact ((Subgroup.mem_centralizer_iff.mp (hd.le_centralizer hh.2)) g (hDS hg)).symm
    have hUQ : U ≤ pCoreIn p Y ⊔ P ⊓ E := by
      intro u hu
      obtain ⟨k, l, hl, e, he, hle, hek, -⟩ := hdec u hu
      have heP : e ∈ P := lif_mem_of_isSylowOf hd hT (hTD.trans hDS) hP he hek
      have hlU : l ∈ U := by
        rw [show l = u * e⁻¹ by rw [← hle]; group]
        exact U.mul_mem hu (U.inv_mem (hPU heP))
      obtain ⟨j, hj⟩ := hU ⟨l, hlU⟩
      have hlQ₀ : l ∈ Q₀ := ⟨hl, j, by simpa using congrArg Subtype.val hj⟩
      rw [← hle]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hQ₀O hlQ₀))
        (Subgroup.mem_sup_right ⟨heP, he⟩)
    exact (hmax _ hQp hDQ hUQ).symm

end Linear

namespace Setting

variable {G : Type} [Group G] [Finite G] (σ : Setting G)

private theorem lif_exists_conj (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∃ d ∈ σ.D, d * σ.x₂ * d⁻¹ = σ.x * σ.x₂ := by
  by_contra hne
  push Not at hne
  have hx₂D : σ.x₂ ∈ σ.D := σ.T_le_D hσ σ.x₂_mem_T
  have hcent : ∀ d ∈ σ.D, d * σ.x₂ = σ.x₂ * d := by
    intro d hd
    have hdT : d * σ.x₂ * d⁻¹ ∈ σ.T :=
      (Subgroup.mem_normalizer_iff.mp hd.2 σ.x₂).mp σ.x₂_mem_T
    have hxd : d * σ.x = σ.x * d :=
      (Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) d hd.1
    rcases σ.mem_T_cases hσ hdT with h | h | h | h
    · exfalso
      have h1 : σ.x₂ = 1 := conj_eq_one_iff.mp h
      have ho := hσ.x₂_order
      rw [h1, orderOf_one] at ho
      exact absurd ho (by norm_num)
    · exfalso
      apply hσ.x_ne_x₂
      rw [show σ.x₂ = d⁻¹ * σ.x * d by rw [← h]; group, mul_assoc, ← hxd, ← mul_assoc,
        inv_mul_cancel, one_mul]
    · calc d * σ.x₂ = d * σ.x₂ * d⁻¹ * d := by group
        _ = σ.x₂ * d := by rw [h]
    · exact absurd h (hne d hd)
  have hx₂Z : σ.x₂ ∈ centerOf σ.D :=
    ⟨hx₂D, Subgroup.mem_centralizer_iff.mpr fun d hd => hcent d hd⟩
  rw [← hII.center_S_eq_center_D] at hx₂Z
  exact hσ.x_ne_x₂ (hσ.center_involution _ hx₂Z hσ.x₂_order).symm

theorem linearImageForm_of_maximal (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {P K U : Subgroup G} (hP : IsSylowOf σ.p P σ.C) (hK : K ∈ σ.familyMstar σ.p)
    (hU : U ∈ maximals (signalizers K σ.D σ.p)) (hPU : P ≤ U) :
    σ.LinearImageForm σ.p K U := by
  classical
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxK S hDS F _ _ ι L E hd
  set π := QuotientGroup.mk' (CFSG.oddCore K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hDK : σ.D ≤ K := hK.2.1
  have hUK : U ≤ K := hU.1.1
  have hTK : σ.T ≤ K := (σ.T_le_D hσ).trans hDK
  have hPK : P ≤ K := hPU.trans hUK
  have hTK4 : IsKleinFour (σ.T.subgroupOf K) := hK.2.2.1.2.1
  have hTO : σ.T.subgroupOf K ⊓ π.ker = ⊥ := by
    rw [hπdef, QuotientGroup.ker_mk']
    apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
    rw [hTK4.card_four, show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_two_left.mpr (odd_card_oddCore K)).pow_left 2
  have hTbar : IsKleinFour ((σ.T.subgroupOf K).map π) :=
    CFSG.ABGDGroups.isKleinFour_map_of_inf_ker_eq_bot π hTK4 hTO
  have hTD : (σ.T.subgroupOf K).map π ≤ (σ.D.subgroupOf K).map π :=
    Subgroup.map_mono fun y hy => σ.T_le_D hσ hy
  set xK : K := ⟨σ.x, hxK⟩ with hxKdef
  have hxD : π xK ∈ (σ.D.subgroupOf K).map π :=
    Subgroup.mem_map_of_mem π (show (xK : G) ∈ σ.D from σ.T_le_D hσ σ.x_mem_T)
  have hxo : orderOf (π xK) = 2 := by
    apply orderOf_eq_prime
    · have h2 : xK ^ 2 = 1 := Subtype.ext (by
        change σ.x ^ 2 = 1
        rw [← hσ.x_order, pow_orderOf_eq_one])
      rw [← map_pow, h2, map_one]
    · intro h1
      have hxker : xK ∈ σ.T.subgroupOf K ⊓ π.ker := ⟨σ.x_mem_T, MonoidHom.mem_ker.mpr h1⟩
      rw [hTO, Subgroup.mem_bot] at hxker
      have ho := hσ.x_order
      rw [show σ.x = 1 from congrArg Subtype.val hxker, orderOf_one] at ho
      exact absurd ho (by norm_num)
  have hxc : (σ.D.subgroupOf K).map π ≤ Subgroup.centralizer ({π xK} : Set _) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hσ.x_mem_center.2) (d : G) hd.1)
  set x₂K : K := ⟨σ.x₂, hTK σ.x₂_mem_T⟩ with hx₂Kdef
  have hx₂D : π x₂K ∈ (σ.D.subgroupOf K).map π :=
    Subgroup.mem_map_of_mem π (show (x₂K : G) ∈ σ.D from σ.T_le_D hσ σ.x₂_mem_T)
  obtain ⟨d, hdD, hdx⟩ := σ.lif_exists_conj hσ hII
  set dK : K := ⟨d, hDK hdD⟩ with hdKdef
  have hdD' : π dK ∈ (σ.D.subgroupOf K).map π :=
    Subgroup.mem_map_of_mem π (show (dK : G) ∈ σ.D from hdD)
  have hdbar : π dK * π x₂K * (π dK)⁻¹ = π xK * π x₂K := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hdx
  have hUp : IsPGroup σ.p ((U.subgroupOf K).map π) := (hU.1.2.1.comap_subtype).map π
  have hDUK : σ.D.subgroupOf K ≤ Subgroup.normalizer ((U.subgroupOf K : Subgroup K) : Set K) :=
    (Subgroup.comap_mono hU.1.2.2.1).trans (Subgroup.le_normalizer_comap _)
  have hDU : (σ.D.subgroupOf K).map π ≤
      Subgroup.normalizer (((U.subgroupOf K).map π : Subgroup _) : Set _) :=
    (Subgroup.map_mono hDUK).trans (Subgroup.le_normalizer_map π)
  have hPU' : (P.subgroupOf K).map π ≤ (U.subgroupOf K).map π :=
    Subgroup.map_mono (Subgroup.comap_mono hPU)
  have hCbar : (Subgroup.centralizer ((σ.T.subgroupOf K : Subgroup K) : Set K)).map π =
      Subgroup.centralizer (((σ.T.subgroupOf K).map π : Subgroup _) : Set _) :=
    CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 2 (CFSG.oddCore K)
      (odd_card_oddCore K).not_two_dvd_nat _ (CFSG.ABGDGroups.isPGroup_two_of_isKleinFour hTK4)
  have hCK : (Subgroup.centralizer ((σ.T.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      σ.C ⊓ K := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨?_, k.2⟩
      change (k : G) ∈ Subgroup.centralizer (σ.T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk ⟨t, hTK ht⟩ ht)
    · rintro ⟨hgC, hgK⟩
      have hgC' : g ∈ Subgroup.centralizer (σ.T : Set G) := hgC
      refine ⟨⟨g, hgK⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
      intro t ht
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC' t ht)
  have hPK' : IsSylowOf σ.p (P.subgroupOf K)
      (Subgroup.centralizer ((σ.T.subgroupOf K : Subgroup K) : Set K)) := by
    rw [← isSylowOf_map_subtype_iff K, hCK, Subgroup.map_subgroupOf_eq_of_le hPK]
    exact hP.of_le (le_inf hP.le hPK) inf_le_left
  have hPbar : IsSylowOf σ.p ((P.subgroupOf K).map π)
      (Subgroup.centralizer (((σ.T.subgroupOf K).map π : Subgroup _) : Set _)) := by
    rw [← hCbar, hπdef]
    exact lif_isSylowOf_map hPK'
  have hmaxK : IsMaximalPSignalizer (σ.D.subgroupOf K) σ.p (U.subgroupOf K) :=
    (isMaximalPSignalizer_subgroupOf_iff hDK hUK).mpr
      ⟨⟨hU.1.2.1, hU.1.2.2.1, hU.1.2.2.2⟩, fun R' hR'K hp' hn' hb' hRR' =>
        hU.2 R' ⟨hR'K, hp', hn', hb'⟩ hRR'⟩
  have hD2 : IsPGroup 2 (σ.D.subgroupOf K) :=
    (σ.S.isPGroup'.to_le σ.D_le_S).comap_subtype
  have hmax : ∀ Q : Subgroup (K ⧸ CFSG.oddCore K), IsPGroup σ.p Q →
      (σ.D.subgroupOf K).map π ≤ Subgroup.normalizer (Q : Set _) →
      (U.subgroupOf K).map π ≤ Q → Q = (U.subgroupOf K).map π := by
    intro Q hQ hDQ hUQ
    have hYodd : Odd (Nat.card (Q.comap π)) := by
      rw [hπdef, card_comap_mk']
      exact (odd_card_oddCore K).mul (odd_card_of_isPGroup hσ.p_ne_two hQ)
    have hDY : σ.D.subgroupOf K ≤ Subgroup.normalizer ((Q.comap π : Subgroup K) : Set K) :=
      (Subgroup.map_le_iff_le_comap.mp hDQ).trans (Subgroup.le_normalizer_comap π)
    have hUY : U.subgroupOf K ≤ Q.comap π := Subgroup.map_le_iff_le_comap.mp hUQ
    have hsyl := hmaxK.isSylowOf_of_odd hσ.p_ne_two hD2 hUY hYodd hDY
    have hsyl' := lif_isSylowOf_map (N := CFSG.oddCore K) hsyl
    rw [← hπdef, Subgroup.map_comap_eq_self_of_surjective hπ] at hsyl'
    exact hsyl'.eq_of_le hUQ le_rfl hQ
  exact lif_main hd hσ.p_ne_two hDS hTbar hTD hxD hxo hxc hx₂D hdD' hdbar hUp hDU hPU' hPbar
    hmax

theorem linearImageForm_of (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∀ J : Subgroup G, σ.IsV21Layer J → σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J,
      ∀ P : Subgroup G, IsSylowOf σ.p P σ.C → σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∀ K ∈ σ.familyMstar σ.p, W ≤ K →
      ∀ U ∈ maximals (signalizersPerm K σ.D W σ.p), U ∈ maximals (signalizers K σ.D σ.p) →
      P ≤ U → pPrimeCoreIn σ.p (U ⊔ W) = ⊥ → σ.LinearImageForm σ.p K U := by
  intro J _ _ W _ P hP _ K hK _ U _ hU hPU _
  exact σ.linearImageForm_of_maximal hσ hII hP hK hU hPU

end Setting

end CFSG.ABGTheoremB
