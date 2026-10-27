module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CoreNoCyclicIndexTwo
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSymplecticSmallCritical

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.SectionRank.Ccomm (ThompsonCritical)

namespace SteinbergBK

variable {G : Type*} [Group G]

theorem eq_of_orderOf_eq_two_of_isCyclic_subgroup {X : Subgroup G} [Finite X] (hX : IsCyclic X)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : x = y :=
  congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic (X := X) (u := ⟨x, hx⟩) (v := ⟨y, hy⟩)
    (by rw [Subgroup.orderOf_mk]; exact hx2) (by rw [Subgroup.orderOf_mk]; exact hy2))

theorem exists_orderOf_eq_two_of_ne_bot [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X)
    (hne : X ≠ ⊥) : ∃ x ∈ X, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq X (by rw [hn, pow_zero]))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem card_mulAut_mul_two_of_isCyclic {X : Type*} [Group X] [Finite X] [IsCyclic X] {k : ℕ}
    (hk : 1 ≤ k) (hX : Nat.card X = 2 ^ k) : Nat.card (MulAut X) * 2 = 2 ^ k := by
  rw [IsCyclic.card_mulAut, hX, Nat.totient_prime_pow Nat.prime_two (by omega)]
  rw [show (2 : ℕ) - 1 = 1 from rfl, mul_one, ← pow_succ]
  congr 1
  omega

theorem involution_mem_centralizer_of_le_normalizer [Finite G] {X Y : Subgroup G}
    (hXc : IsCyclic X) (hYc : IsCyclic Y) {k : ℕ} (hk : 1 ≤ k) (hXk : Nat.card X = 2 ^ k)
    (hYk : Nat.card Y = 2 ^ k) (hYN : Y ≤ normalizer (X : Set G)) {y : G} (hy : y ∈ Y)
    (hy2 : orderOf y = 2) : y ∈ centralizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : Y →* MulAut X := X.normalizerMonoidHom.comp (inclusion hYN)
  have hψ : ∀ (a : Y) (x : X), ((ψ a x : X) : G) = (a : G) * x * (a : G)⁻¹ := fun a x =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hAut := card_mulAut_mul_two_of_isCyclic hk hXk
  have hrange : Nat.card ψ.range * 2 ≤ 2 ^ k :=
    (Nat.mul_le_mul_right 2 (Nat.le_of_dvd Nat.card_pos (card_subgroup_dvd_card _))).trans
      hAut.le
  have hker : 2 ≤ Nat.card ψ.ker := by
    have h1 := card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hYk] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card ψ.ker ≤ 1 := by omega
    have h3 : 2 ^ k ≤ Nat.card ψ.range := by
      calc 2 ^ k = Nat.card ψ.range * Nat.card ψ.ker := h1
        _ ≤ Nat.card ψ.range * 1 := Nat.mul_le_mul_left _ h2
        _ = Nat.card ψ.range := mul_one _
    have : 0 < Nat.card ψ.range := Nat.card_pos
    omega
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card hYk
  have hkerY : IsPGroup 2 ψ.ker := hY2.to_subgroup _
  have hkerne : ψ.ker ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hker
    omega
  obtain ⟨a, ha, ha2⟩ := exists_orderOf_eq_two_of_ne_bot hkerY hkerne
  have haY : (a : G) = y := eq_of_orderOf_eq_two_of_isCyclic_subgroup hYc a.2 hy
    (by rw [Subgroup.orderOf_coe]; exact ha2) hy2
  rw [← haY, mem_centralizer_iff]
  intro x hx
  have h1 := congrArg (fun σ : MulAut X => ((σ ⟨x, hx⟩ : X) : G)) (MonoidHom.mem_ker.mp ha)
  simp only [hψ, MulAut.one_apply] at h1
  calc x * (a : G) = (a : G) * x * (a : G)⁻¹ * a := by rw [h1]
    _ = a * x := by group

theorem nonempty_prod_mulEquiv_sup {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hHK : H ⊓ K = ⊥) :
    Nonempty (H × K ≃* (H ⊔ K : Subgroup G)) := by
  have hc : ∀ (h : H) (k : K), Commute (H.subtype h) (K.subtype k) := fun h k =>
    hcomm h h.2 k k.2
  let f : H × K →* G := H.subtype.noncommCoprod K.subtype hc
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨h, k⟩ hhk
    have h1 : (h : G) * k = 1 := hhk
    have hk : (k : G) = (h : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hmem : (h : G) ∈ H ⊓ K := ⟨h.2, by rw [← inv_inv (h : G), ← hk]; exact K.inv_mem k.2⟩
    rw [hHK, mem_bot] at hmem
    have hk1 : (k : G) = 1 := by rw [hk, hmem, inv_one]
    rw [mem_bot]
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hk1)
  have hrange : f.range = H ⊔ K :=
    (MonoidHom.noncommCoprod_range H.subtype K.subtype hc).trans
      (by rw [range_subtype, range_subtype])
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange)⟩

theorem normalizer_le_normalizer_map_of_characteristic {Q : Subgroup G} {Z₀ : Subgroup Q}
    (hZ₀ : Z₀.Characteristic) :
    normalizer (Q : Set G) ≤ normalizer ((Z₀.map Q.subtype : Subgroup G) : Set G) := by
  intro g hg
  let σ : MulAut Q := Q.normalizerMonoidHom ⟨g, hg⟩
  have hσ : ∀ x : Q, ((σ x : Q) : G) = g * x * g⁻¹ := fun x =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hfix : ∀ x : Q, σ x ∈ Z₀ ↔ x ∈ Z₀ := fun x => by
    conv_rhs => rw [← hZ₀.fixed σ]
    rfl
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    exact ⟨σ x₀, (hfix x₀).mpr hx₀, hσ x₀⟩
  · rintro ⟨y₀, hy₀, hy⟩
    have hxQ : x ∈ Q := by
      have h1 : g * x * g⁻¹ ∈ Q := by rw [← hy]; exact y₀.2
      exact ((mem_normalizer_iff.mp hg) x).mpr h1
    refine ⟨⟨x, hxQ⟩, (hfix _).mp ?_, rfl⟩
    have h2 : σ ⟨x, hxQ⟩ = y₀ := Subtype.ext (by rw [hσ]; exact hy.symm)
    rw [h2]
    exact hy₀

theorem coe_mem_centralizer_map_iff {Q : Subgroup G} {Z₀ : Subgroup Q} (q : Q) :
    (q : G) ∈ centralizer ((Z₀.map Q.subtype : Subgroup G) : Set G) ↔
      q ∈ centralizer (Z₀ : Set Q) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    exact Subtype.ext (h x ⟨x, hx, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (h x hx)

end SteinbergBK

open SteinbergBK

theorem gf2_critical_center_and_exponent_four_reduction
    {G : Type*} [Group G] [Finite G]
    (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G}
    (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B)
    (hBM : B ≤ M) {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G}
    (hzQ : z ∈ (center Q).map Q.subtype) (hz : orderOf z = 2) {r : ℕ}
    (hr : r = GLATwoLocalRank 3 G) :
    (∃ D : Subgroup Q, ThompsonCritical D) ∧
    ∀ D : Subgroup Q, ThompsonCritical D → ∀ Z₀ : Subgroup Q, Z₀ = (center D).map D.subtype →
    ∀ Z : Subgroup G, Z = Z₀.map Q.subtype →
      (∃ E R : Subgroup Q, E ⊔ Z₀ = D ∧ R = centralizer (E : Set Q) ∧ E ⊔ R = ⊤ ∧
        ⁅E, R⁆ = ⊥ ∧ R ⊓ centralizer (Z₀ : Set Q) = Z₀ ∧ E.Normal ∧ R.Normal ∧
        ((E = ⊥ ∧ R = ⊤ ∧ D = Z₀ ∧ 2 < Z₀.relIndex R) ∨
          (IsExtraspecialPGroup 2 E ∧ (E ⊓ R).map Q.subtype = zpowers z ∧
            (E ⊓ Z₀).map Q.subtype = zpowers z ∧
            ((center E).map E.subtype).map Q.subtype = zpowers z)) ∧
        (∃ φ : Q →* MulAut Z₀,
          (∀ (q : Q) (x : Z₀), ((φ q x : Z₀) : Q) = q * x * q⁻¹) ∧ φ.ker = D) ∧
        ∃ ψ : R →* MulAut Z₀,
          (∀ (t : R) (x : Z₀), ((ψ t x : Z₀) : Q) = t * x * t⁻¹) ∧ ψ.ker = Z₀.subgroupOf R) ∧
      Z₀ ≠ ⊥ ∧ IsCyclic Z₀ ∧ Z₀.Characteristic ∧ z ∈ Z ∧ (∀ y ∈ Z, orderOf y = 2 → y = z) ∧
      centralizer (Z₀ : Set Q) = D ∧ normalizer (Z : Set G) = M ∧ M = centralizer {z} ∧
      centralizer (Z : Set G) = M ⊓ centralizer (Z : Set G) ∧
      (∃ k : ℕ, (M ⊓ centralizer (Z : Set G)).relIndex M = 2 ^ k) ∧
      (∀ K : Subgroup G, K ≤ M → Odd (Nat.card K) → K ≤ centralizer (Z : Set G)) ∧
      B ≤ centralizer (Z : Set G) ∧
      (∀ g : G, (conjugate Z g = Z ∨ Z ⊓ conjugate Z g = ⊥) ∧
        (conjugate Z g ≤ M ↔ ⁅Z, conjugate Z g⁆ = ⊥) ∧
        (⁅Z, conjugate Z g⁆ = ⊥ ↔ g⁻¹ * z * g ∈ M ⊓ centralizer (Z : Set G)) ∧
        (g⁻¹ * z * g ∈ Q → (conjugate Z g ≤ M ↔ g⁻¹ * z * g ∈ D.map Q.subtype)) ∧
        (g⁻¹ * z * g ∈ D.map Q.subtype → g⁻¹ * z * g ≠ z →
          Z ⊔ conjugate Z g ≤ M ∧ ⁅Z, conjugate Z g⁆ = ⊥ ∧ Z ⊓ conjugate Z g = ⊥ ∧
          IsCyclic (conjugate Z g) ∧ Nat.card (conjugate Z g) = Nat.card Z ∧
          Nonempty (Z × conjugate Z g ≃* (Z ⊔ conjugate Z g : Subgroup G)))) ∧
      (¬ IsExtraspecialPGroup 2 Q →
        Xor
          ((∀ x : Q, x ^ 4 = 1) ∧ D = ⊤ ∧ Z₀ = center Q ∧ Nat.card Z₀ = 4 ∧
            ∃ w : ℕ, 1 ≤ w ∧
              (∃ E : Subgroup Q, IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
                E ⊔ Z₀ = ⊤ ∧ ⁅E, Z₀⁆ = ⊥ ∧ (E ⊓ Z₀).map Q.subtype = zpowers z ∧
                ((center E).map E.subtype).map Q.subtype = zpowers z) ∧
              (commutator Q).map Q.subtype = zpowers z ∧
              (frattini Q).map Q.subtype = zpowers z ∧ Nat.card Q = 2 ^ (2 * w + 2) ∧
              CFSG.IsElementaryAbelian 2 (Q ⧸ center Q) ∧
              Nat.card (Q ⧸ center Q) = 2 ^ (2 * w) ∧
              CFSG.IsElementaryAbelian 2 (Q ⧸ frattini Q) ∧
              Nat.card (Q ⧸ frattini Q) = 2 ^ (2 * w + 1) ∧ r ≤ w)
          (8 ≤ Nat.card Z₀ ∧ ∃ x : Q, 8 ≤ orderOf x)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsym₀ := hsym
  obtain ⟨⟨z₁, -, -, huniq₁, hMC₁, hMNQ, -, -⟩, -, hQne, hBcard, -, -, ⟨d, hd, hdr⟩, -, -⟩ :=
    gf2_witness_centralizer_and_rank hchar hM hsym hB hBM hQ hr
  have hMC : M = centralizer {z} := by rw [hMC₁, huniq₁ z hzQ hz]
  have hQeq : pCoreOf 2 M = Q := by
    rw [hQ]
    unfold CFSG.Open.pCoreOf
    rfl
  rw [hQeq] at hsym
  obtain ⟨hQ2, hsymp⟩ := hsym
  have : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQne
  have hQM : Q ≤ M := by
    rw [hQ]
    exact map_subtype_le _
  obtain ⟨hex, hcp⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.symplectic_critical_subgroup_central_product hQ2 hsymp
  refine ⟨hex.elim fun D h => ⟨D, h.2⟩, fun D hD Z₀ hZ₀ Z hZ => ?_⟩
  obtain ⟨hZ0, hcyc, hZchar, z₀, hz₀Z, hz₀, huniq₀, -, huniqc, hcZ, E, R, hEZ, hR, hER,
    hERc, hRZ, hEn, hRn, hcases, hφ, hψ⟩ := hcp D hD
  subst hZ₀ hZ
  set Z₀ := (center D).map D.subtype with hZ₀def
  set Z := Z₀.map Q.subtype with hZdef
  have hzz₀ : (z₀ : G) = z := by
    obtain ⟨zq, hzqc, hzq⟩ := hzQ
    have hzq' : (zq : G) = z := hzq
    have hzq2 : orderOf zq = 2 := by rw [← Subgroup.orderOf_coe, hzq']; exact hz
    rw [← huniqc zq hzqc hzq2, hzq']
  subst hzz₀
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZM : Z ≤ M := hZQ.trans hQM
  have hzZ : (z₀ : G) ∈ Z := mem_map_of_mem Q.subtype hz₀Z
  have huniqZ : ∀ y ∈ Z, orderOf y = 2 → y = z₀ := by
    rintro _ ⟨y, hy, rfl⟩ hy2
    change orderOf (y : G) = 2 at hy2
    change (y : G) = z₀
    rw [huniq₀ y hy (by rwa [Subgroup.orderOf_coe] at hy2)]
  have eZ : Z₀ ≃* Z := Z₀.equivMapOfInjective Q.subtype Q.subtype_injective
  have hZcyc : IsCyclic Z := isCyclic_of_surjective eZ.toMonoidHom eZ.surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hQ2.to_subgroup Z₀)
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      exact absurd (Subgroup.eq_bot_of_card_eq Z₀ hk) hZ0
    · exact h
  have hZk : Nat.card Z = 2 ^ k := (Nat.card_congr eZ.toEquiv).symm.trans hk
  have hMNZ : M ≤ normalizer (Z : Set G) :=
    hMNQ.le.trans (normalizer_le_normalizer_map_of_characteristic hZchar)
  have hconj_ord : ∀ g x : G, orderOf (g * x * g⁻¹) = orderOf x := fun g x => by
    simpa only [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) x
  have hNZM : normalizer (Z : Set G) ≤ M := by
    intro g hg
    rw [hMC, mem_centralizer_singleton_iff]
    have h1 : g * (z₀ : G) * g⁻¹ ∈ Z := (mem_normalizer_iff.mp hg z₀).mp hzZ
    have h2 := huniqZ _ h1 (by rw [hconj_ord]; exact hz)
    calc g * (z₀ : G) = g * z₀ * g⁻¹ * g := by group
      _ = z₀ * g := by rw [h2]
  have hNZ : normalizer (Z : Set G) = M := le_antisymm hNZM hMNZ
  have hCM : centralizer (Z : Set G) ≤ M := (centralizer_le_normalizer _).trans hNZM
  let θ : M →* MulAut Z := Z.normalizerMonoidHom.comp (inclusion hMNZ)
  have hθ : ∀ (m : M) (x : Z), ((θ m x : Z) : G) = m * x * (m : G)⁻¹ := fun _ _ =>
    normalizerMonoidHom_apply_apply_coe _ _ _
  have hθker : ∀ m : M, θ m = 1 ↔ (m : G) ∈ centralizer (Z : Set G) := by
    intro m
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun σ : MulAut Z => ((σ ⟨x, hx⟩ : Z) : G)) h
      simp only [hθ, MulAut.one_apply] at h1
      calc x * (m : G) = m * x * (m : G)⁻¹ * m := by rw [h1]
        _ = m * x := by group
    · intro h
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hθ, MulAut.one_apply, ← mem_centralizer_iff.mp h x x.2, mul_inv_cancel_right]
  have hAut : Nat.card (MulAut Z) = 2 ^ (k - 1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [card_mulAut_mul_two_of_isCyclic hk1 hZk, ← pow_succ]
    congr 1
    omega
  have hidx : ∃ j : ℕ, (M ⊓ centralizer (Z : Set G)).relIndex M = 2 ^ j := by
    have hker : θ.ker = (M ⊓ centralizer (Z : Set G)).subgroupOf M := by
      ext m
      rw [MonoidHom.mem_ker, hθker, mem_subgroupOf, mem_inf]
      exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
    have h1 : (M ⊓ centralizer (Z : Set G)).relIndex M = Nat.card θ.range := by
      rw [relIndex, ← hker, index_ker]
    have h2 : Nat.card θ.range ∣ 2 ^ (k - 1) := hAut ▸ card_subgroup_dvd_card θ.range
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact ⟨j, h1.trans hj⟩
  have hodd : ∀ K : Subgroup G, K ≤ M → Odd (Nat.card K) → K ≤ centralizer (Z : Set G) := by
    intro K hKM hK x hx
    have h1 : orderOf (θ ⟨x, hKM hx⟩) ∣ Nat.card K := by
      refine (orderOf_map_dvd θ _).trans ?_
      rw [Subgroup.orderOf_mk]
      have := orderOf_dvd_natCard (⟨x, hx⟩ : K)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (θ ⟨x, hKM hx⟩) ∣ 2 ^ (k - 1) := hAut ▸ orderOf_dvd_natCard _
    have hcop : Nat.Coprime (Nat.card K) (2 ^ (k - 1)) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hK)
    have h4 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, hθker] at h4
    exact h4
  refine ⟨?_, hZ0, hcyc, hZchar, hzZ, huniqZ, hcZ, hNZ, hMC,
    (inf_eq_right.mpr hCM).symm, hidx, hodd,
    hodd B hBM (by rw [hBcard]; exact Odd.pow ⟨1, rfl⟩), fun g => ?_, ?_⟩
  ·
    refine ⟨E, R, hEZ, hR, hER, hERc, hRZ, hEn, hRn, ?_, hφ, hψ⟩
    rcases hcases with ⟨-, rfl, rfl⟩ | ⟨w, -, -, -, -, hEx, -, -, hER', hEZ', hEc, -⟩
    · refine Or.inl ⟨rfl, rfl, by rw [← hEZ, bot_sup_eq], ?_⟩
      rw [relIndex_top_right]
      have h1 := gf2_core_has_no_cyclic_index_two_subgroup hchar he hM hsym₀ hB hBM hQ Z hZQ hZcyc
      have h2 : Z.subgroupOf Q = Z₀ := comap_map_eq_self_of_injective Q.subtype_injective Z₀
      rw [relIndex, h2] at h1
      exact h1
    · refine Or.inr ⟨hEx, ?_, ?_, ?_⟩
      · rw [hER', MonoidHom.map_zpowers, coe_subtype]
      · rw [hEZ', MonoidHom.map_zpowers, coe_subtype]
      · rw [hEc, MonoidHom.map_zpowers, coe_subtype]
  ·
    set Y := conjugate Z g with hYdef
    have hYmem : ∀ y, y ∈ Y ↔ g * y * g⁻¹ ∈ Z := fun y => mem_conjugate_iff_conj_mem
    have hzgY : g⁻¹ * (z₀ : G) * g ∈ Y := inv_mul_mul_mem_conjugate hzZ
    have hzg2 : orderOf (g⁻¹ * (z₀ : G) * g) = 2 := by
      have h1 := hconj_ord g⁻¹ z₀
      rw [inv_inv] at h1
      rw [h1]
      exact hz
    have eY : Z ≃* Y :=
      Z.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    have hYcyc : IsCyclic Y := isCyclic_of_surjective eY.toMonoidHom eY.surjective
    have hYk : Nat.card Y = 2 ^ k := (Nat.card_congr eY.toEquiv).symm.trans hZk
    have huniqY : ∀ y ∈ Y, orderOf y = 2 → y = g⁻¹ * z₀ * g := by
      intro y hy hy2
      have h1 := huniqZ _ ((hYmem y).mp hy) (by rw [hconj_ord]; exact hy2)
      rw [← h1]
      group
    have hCY : ∀ h : G, h * (g⁻¹ * z₀ * g) = (g⁻¹ * z₀ * g) * h →
        h ∈ normalizer (Y : Set G) := by
      intro h hh
      have h1 : g * h * g⁻¹ ∈ M := by
        rw [hMC, mem_centralizer_singleton_iff]
        calc g * h * g⁻¹ * z₀ = g * (h * (g⁻¹ * z₀ * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * z₀ * g) * h) * g⁻¹ := by rw [hh]
          _ = z₀ * (g * h * g⁻¹) := by group
      have h2 := mem_normalizer_iff.mp (hMNZ h1)
      rw [mem_normalizer_iff]
      intro y
      rw [hYmem, hYmem, h2 (g * y * g⁻¹)]
      have h3 : g * h * g⁻¹ * (g * y * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ := by
        group
      rw [h3]
    have hTI : Y = Z ∨ Z ⊓ Y = ⊥ := by
      by_cases hb : Z ⊓ Y = ⊥
      · exact Or.inr hb
      left
      obtain ⟨y, hy, hy2⟩ := exists_orderOf_eq_two_of_ne_bot ((hQ2.to_le hZQ).to_le inf_le_left) hb
      have h1 : y = z₀ := huniqZ y hy.1 hy2
      have h2 : y = g⁻¹ * z₀ * g := huniqY y hy.2 hy2
      have hgM : g ∈ M := by
        rw [hMC, mem_centralizer_singleton_iff]
        have h3 : (z₀ : G) = g⁻¹ * z₀ * g := h1 ▸ h2
        calc g * (z₀ : G) = g * (g⁻¹ * z₀ * g) := by rw [← h3]
          _ = z₀ * g := by group
      exact mem_normalizer_iff_conjugate_eq.mp (hMNZ hgM)
    have hcommYZ : Y ≤ normalizer (Z : Set G) → Z ≤ normalizer (Y : Set G) → ⁅Z, Y⁆ = ⊥ := by
      intro hYN hZN
      rcases hTI with hYZ | hb
      · rw [hYZ, commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val
          ((IsCyclic.isMulCommutative (α := Z)).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
      · rw [eq_bot_iff, ← hb, commutator_le]
        intro x hx y hy
        refine mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : y * x⁻¹ * y⁻¹ ∈ Z := (mem_normalizer_iff.mp (hYN hy) x⁻¹).mp (inv_mem hx)
          rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
          exact mul_mem hx h1
        · have h1 : x * y * x⁻¹ ∈ Y := (mem_normalizer_iff.mp (hZN hx) y).mp hy
          rw [commutatorElement_def]
          exact mul_mem h1 (inv_mem hy)
    have hi : Y ≤ M → ⁅Z, Y⁆ = ⊥ := by
      intro hYM
      have h1 : g⁻¹ * (z₀ : G) * g ∈ centralizer (Z : Set G) :=
        involution_mem_centralizer_of_le_normalizer hZcyc hYcyc hk1 hZk hYk (hYM.trans hMNZ)
          hzgY hzg2
      exact hcommYZ (hYM.trans hMNZ) fun x hx => hCY x (mem_centralizer_iff.mp h1 x hx)
    have hii : ⁅Z, Y⁆ = ⊥ → g⁻¹ * (z₀ : G) * g ∈ M ⊓ centralizer (Z : Set G) := by
      intro h
      have h1 : g⁻¹ * (z₀ : G) * g ∈ centralizer (Z : Set G) := by
        rw [mem_centralizer_iff]
        intro x hx
        exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h hx) _ hzgY).symm
      exact ⟨hCM h1, h1⟩
    have hiii : g⁻¹ * (z₀ : G) * g ∈ M ⊓ centralizer (Z : Set G) → Y ≤ M := by
      rintro ⟨-, h1⟩
      have hZN : Z ≤ normalizer (Y : Set G) := fun x hx =>
        hCY x (mem_centralizer_iff.mp h1 x hx)
      have h2 : (z₀ : G) ∈ centralizer (Y : Set G) :=
        involution_mem_centralizer_of_le_normalizer hYcyc hZcyc hk1 hYk hZk hZN hzZ hz
      intro y hy
      rw [hMC, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp h2 y hy
    have hiv : g⁻¹ * (z₀ : G) * g ∈ Q → (Y ≤ M ↔ g⁻¹ * (z₀ : G) * g ∈ D.map Q.subtype) := by
      intro hq
      have h1 := coe_mem_centralizer_map_iff (Z₀ := Z₀) ⟨_, hq⟩
      rw [hcZ] at h1
      refine ⟨fun h => ?_, fun h => hiii ?_⟩
      · obtain ⟨-, h2⟩ := hii (hi h)
        exact ⟨⟨_, hq⟩, h1.mp h2, rfl⟩
      · obtain ⟨q, hqD, hqe⟩ := h
        obtain rfl : q = ⟨_, hq⟩ := Subtype.ext hqe
        exact ⟨hQM hq, h1.mpr hqD⟩
    have hv : g⁻¹ * (z₀ : G) * g ∈ D.map Q.subtype → g⁻¹ * (z₀ : G) * g ≠ z₀ →
        Z ⊔ Y ≤ M ∧ ⁅Z, Y⁆ = ⊥ ∧ Z ⊓ Y = ⊥ ∧ IsCyclic Y ∧ Nat.card Y = Nat.card Z ∧
          Nonempty (Z × Y ≃* (Z ⊔ Y : Subgroup G)) := by
      intro hD' hne
      have hq : g⁻¹ * (z₀ : G) * g ∈ Q := map_subtype_le D hD'
      have hYM : Y ≤ M := (hiv hq).mpr hD'
      have hc := hi hYM
      have hb : Z ⊓ Y = ⊥ := by
        rcases hTI with hYZ | hb
        · exact absurd (huniqZ _ (hYZ ▸ hzgY) hzg2) hne
        · exact hb
      refine ⟨sup_le hZM hYM, hc, hb, hYcyc, hYk.trans hZk.symm,
        nonempty_prod_mulEquiv_sup (fun x hx y hy => ?_) hb⟩
      exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc hx) y hy).symm
    exact ⟨hTI, ⟨hi, fun h => hiii (hii h)⟩, ⟨hii, fun h => hi (hiii h)⟩, hiv, hv⟩
  ·
    intro hnex
    obtain ⟨hsmall, hiff⟩ := symplectic_small_critical_center_structure hQ2 hsymp hD
    by_cases hk2 : k ≤ 2
    · have h4 : Nat.card Z₀ ≤ 4 := by
        rw [hk]
        calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
          _ = 4 := by norm_num
      obtain ⟨z', hz'Z, hz', -, halt, -, -, -, hcons, hexp⟩ := hsmall h4
      have hz'z : z' = z₀ := huniq₀ z' hz'Z hz'
      rw [hz'z] at halt hcons
      rcases halt with ⟨hQcyc, -⟩ | hQex | ⟨w, hw⟩
      · exfalso
        have h1 :=
          gf2_core_has_no_cyclic_index_two_subgroup hchar he hM hsym₀ hB hBM hQ Q le_rfl hQcyc
        rw [relIndex_self] at h1
        omega
      · exact absurd hQex hnex
      · obtain ⟨hcom, hfr, hel, hQZ, hQcard, -⟩ := hcons w hw
        obtain ⟨hDtop, hZc, hZ4, hw1, E', hE'x, hE'card, hE'Z, hE'c, hE'Zi, hE'cen⟩ := hw
        rw [← hZ₀def] at hZc hE'Z hE'c hE'Zi
        have hZ₀4 : Nat.card Z₀ = 4 := by rw [hZc]; exact hZ4
        have hΦcard : Nat.card (frattini Q) = 2 := by rw [hfr, Nat.card_zpowers, hz₀]
        have hQΦ : Nat.card (Q ⧸ frattini Q) = 2 ^ (2 * w + 1) := by
          have h1 := card_eq_card_quotient_mul_card_subgroup (frattini Q)
          rw [hQcard, hΦcard, show 2 ^ (2 * w + 2) = 2 ^ (2 * w + 1) * 2 by ring] at h1
          exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
        have hdw : d = 2 * w + 1 := by
          rw [hQΦ] at hd
          exact (Nat.pow_right_injective (le_refl 2) hd).symm
        have : Fact (IsPGroup 2 Q) := ⟨hQ2⟩
        refine Or.inl ⟨⟨hexp, hDtop, hZc, hZ₀4, w, hw1,
          ⟨E', hE'x, hE'card, hE'Z, hE'c, ?_, ?_⟩, ?_, ?_, hQcard, hel, hQZ,
          isElementaryAbelian_quotient_frattini, hQΦ, by omega⟩, fun h => by omega⟩
        · rw [hE'Zi, MonoidHom.map_zpowers, coe_subtype]
        · rw [hE'cen, MonoidHom.map_zpowers, coe_subtype]
        · rw [hcom, MonoidHom.map_zpowers, coe_subtype]
        · rw [hfr, MonoidHom.map_zpowers, coe_subtype]
    · have h8 : 8 ≤ Nat.card Z₀ := by
        rw [hk]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      refine Or.inr ⟨⟨h8, hiff.mpr h8⟩, fun hA => ?_⟩
      obtain ⟨-, -, -, h4, -⟩ := hA
      omega

end CFSG.LocalAnalysis.GorensteinLyons
