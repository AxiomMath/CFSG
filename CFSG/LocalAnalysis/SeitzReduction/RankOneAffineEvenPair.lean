module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneAffineEvenPairTranslations

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV CFSG.LocalAnalysis.SteinbergBX
  CFSG.LocalAnalysis.SteinbergBX.GMSAffine

theorem card_eq_mul_of_forall_eq_mul {G : Type*} [Group G] {K A H : Subgroup G} (hAK : A ≤ K)
    (hHK : H ≤ K) (hdec : ∀ x ∈ K, ∃ a ∈ A, ∃ b ∈ H, x = a * b) (hinf : A ⊓ H = ⊥) :
    Nat.card K = Nat.card A * Nat.card H := by
  rw [← Nat.card_prod]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : A × H => (⟨(p.1 : G) * p.2, mul_mem (hAK p.1.2) (hHK p.2.2)⟩ : K)) ⟨?_, ?_⟩)
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ hab
    have h1 : x * y = x' * y' := congrArg Subtype.val hab
    have h2 : x'⁻¹ * x = y' * y⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * y) * y⁻¹ := by group
        _ = x'⁻¹ * (x' * y') * y⁻¹ := by rw [h1]
        _ = y' * y⁻¹ := by group
    have h3 : x'⁻¹ * x ∈ A ⊓ H := by
      refine mem_inf.2 ⟨mul_mem (inv_mem hx') hx, ?_⟩
      rw [h2]
      exact mul_mem hy' (inv_mem hy)
    rw [hinf, mem_bot] at h3
    have hxx : x = x' := by
      calc x = x' * (x'⁻¹ * x) := by group
        _ = x' := by rw [h3, mul_one]
    have hyy : y = y' := by
      have h4 : y' * y⁻¹ = 1 := by
        rw [← h2]
        exact h3
      calc y = (y' * y⁻¹)⁻¹ * y' := by group
        _ = y' := by rw [h4, inv_one, one_mul]
    subst hxx hyy
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem comap_ker_quotient_of_le_range {L M : Type*} [Group L] [Group M] (π : L →* M)
    (K : Subgroup L) [K.Normal] (hK : π.ker = K) (A : Subgroup M) (hAN : A ≤ π.range) :
    K ≤ A.comap π ∧ Nonempty (↥(A.comap π) ⧸ K.subgroupOf (A.comap π) ≃* A) := by
  subst hK
  refine ⟨fun l hl => ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hl
    rw [mem_comap, hl]
    exact one_mem A
  · set φ : A.comap π →* A :=
      (π.comp (A.comap π).subtype).codRestrict A (fun x => x.2) with hφ
    have hφsurj : Function.Surjective φ := by
      rintro ⟨e, he⟩
      obtain ⟨l, hl⟩ := hAN he
      exact ⟨⟨l, by rw [mem_comap, hl]; exact he⟩, Subtype.ext hl⟩
    have hφker : φ.ker = π.ker.subgroupOf (A.comap π) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h1 => congrArg Subtype.val h1, fun h1 => Subtype.ext h1⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)⟩

theorem comap_normal_of_le_range {L M : Type*} [Group L] [Group M] (π : L →* M)
    (K : Subgroup L) [K.Normal] (hK : π.ker = K) (A : Subgroup M) (hAN : A ≤ π.range)
    (hAn : (A.subgroupOf π.range).Normal) :
    (A.comap π).Normal ∧ K ≤ A.comap π ∧
      Nonempty (↥(A.comap π) ⧸ K.subgroupOf (A.comap π) ≃* A) := by
  refine ⟨⟨fun l hl g => ?_⟩, comap_ker_quotient_of_le_range π K hK A hAN⟩
  rw [mem_comap] at hl ⊢
  have h1 := hAn.conj_mem ⟨_, hAN hl⟩ (mem_subgroupOf.2 hl) ⟨_, ⟨g, rfl⟩⟩
  rw [mem_subgroupOf] at h1
  rw [map_mul, map_mul, map_inv]
  exact h1

section GMS

variable {D : Type} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_even_pair_involutionGeometry [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hd : Even (Nat.card (gmsPairStabilizer U R β)))
    {τ : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)} (hτ : τ ∈ gmsPairStabilizer U R β)
    (hτ2 : orderOf τ = 2) :
    InvolutionGeometry (gmsRootConjugateAction (U ⊔ R) R).range τ ⟨R, gms_R_mem⟩ β
        (2 ^ (n / 2)) ∧
      ∀ w ∈ (gmsRootConjugateAction (U ⊔ R) R).range, w ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ →
        w * τ = τ * w → orderOf w = 2 → w = τ := by
  obtain ⟨-, hΔcard, -, -, h2tr, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  obtain ⟨-, -, -, -, -, hn4, -, hsq, hs4, -, hτex, -, -, -, -, -, -, -, hτall⟩ :=
    gms_normal_root_even_pair_involution_affine_plane h h3 β hβ hd
  have hβR : β ≠ ⟨R, gms_R_mem⟩ := fun h1 => hβ (congrArg Subtype.val h1)
  have hτH : τ ∈ gmsPermStabilizer U R := (mem_inf.1 hτ).1
  obtain ⟨hτN, hτR⟩ := GMSDichotomy.mem_gmsPermStabilizer.1 hτH
  have hτβ : τ β = β := MulAction.mem_stabilizer_iff.1 (mem_inf.1 hτ).2
  have hBuniq : ∀ b ∈ (gmsRootConjugateAction (U ⊔ R) R).range, b ⟨R, gms_R_mem⟩ =
      ⟨R, gms_R_mem⟩ → b β = β → orderOf b = 2 → b = τ := by
    intro b hb hbR hbβ hb2
    exact hτex.unique ⟨mem_inf.2 ⟨GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hb, hbR⟩,
      MulAction.mem_stabilizer_iff.2 hbβ⟩, hb2⟩ ⟨hτ, hτ2⟩
  have hG : InvolutionGeometry (gmsRootConjugateAction (U ⊔ R) R).range τ ⟨R, gms_R_mem⟩ β
      (2 ^ (n / 2)) :=
    { two_trans := fun x y x' y' hxy hxy' => h2tr x y x' y' hxy hxy'
      ne := hβR.symm
      mem := hτN
      fix_left := hτR
      fix_right := hτβ
      orderOf_eq := hτ2
      unique := hBuniq
      card_fix := (hτall τ hτ hτ2).1
      card := by rw [Nat.card_coe_set_eq, hΔcard, hsq]
      two_le := by omega
      even := Nat.even_pow.2 ⟨even_two, by omega⟩ }
  have hTH := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have hTN : gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range :=
    fun t ht => (GMSDichotomy.mem_gmsPermStabilizer.1 (hTH ht)).1
  have hTR : ∀ t ∈ gmsSingerPermImage X U R, t ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ :=
    fun t ht => (GMSDichotomy.mem_gmsPermStabilizer.1 (hTH ht)).2
  have hTtrans : ∀ x y, x ≠ ⟨R, gms_R_mem⟩ → y ≠ ⟨R, gms_R_mem⟩ →
      ∃ t ∈ gmsSingerPermImage X U R, t x = y := fun x y hx hy => by
    obtain ⟨t, ht, -⟩ := gms_singer_regular h h3 x y hx hy
    exact ⟨t, t.2, ht⟩
  have hTfree : ∀ t ∈ gmsSingerPermImage X U R, ∀ x, x ≠ ⟨R, gms_R_mem⟩ → t x = x → t = 1 := by
    intro t ht x hx htx
    obtain ⟨t₀, -, huniq⟩ := gms_singer_regular h h3 x x hx hx
    exact congrArg Subtype.val ((huniq ⟨t, ht⟩ htx).trans (huniq 1 rfl).symm)
  have hTn : ∀ t ∈ gmsSingerPermImage X U R, ∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      g ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ → g * t * g⁻¹ ∈ gmsSingerPermImage X U R := by
    intro t ht g hg hgR
    have h1 := (GMSDichotomy.gmsSingerPermImage_normal h (X := X)).conj_mem ⟨t, hTH ht⟩
      (mem_subgroupOf.2 ht) ⟨g, GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hg, hgR⟩⟩
    rw [mem_subgroupOf] at h1
    exact h1
  have hTodd : Odd (Nat.card (gmsSingerPermImage X U R)) := by
    rw [(GMSDichotomy.isCyclic_gmsSingerPermImage h h3).2]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  exact ⟨hG, hG.eq_tau_of_singer hTN hTR hTn hTtrans hTfree hTodd⟩

theorem gms_normal_root_even_pair_completion [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (β : gmsRootConjugates (U ⊔ R) R) (hβ : (β : Subgroup D) ≠ R)
    (hd : Even (Nat.card (gmsPairStabilizer U R β))) :
    4 ≤ n ∧ Even n ∧ 2 ^ n = (2 ^ (n / 2)) ^ 2 ∧ 4 ≤ 2 ^ (n / 2) ∧
    (gmsRootConjugates (U ⊔ R) R).ncard = 2 ^ n ∧
    Nat.card (gmsPermStabilizer U R) = (2 ^ n - 1) * Nat.card (gmsPairStabilizer U R β) ∧
    Nat.card (gmsRootConjugateAction (U ⊔ R) R).range =
      2 ^ n * (2 ^ n - 1) * Nat.card (gmsPairStabilizer U R β) ∧
    ∃ E : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)),
      E ≤ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (E.subgroupOf (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃! a : E,
        (a : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) Q = Z) ∧
      (∀ σ, σ ∈ E ↔ σ = 1 ∨ σ ∈ regInvolutions (gmsRootConjugateAction (U ⊔ R) R).range) ∧
      (∀ τ ∈ gmsPairStabilizer U R β, orderOf τ = 2 → ∀ σ, σ ∈ E ↔
        σ ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧
          (∀ ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
              (Function.fixedPoints ⇑τ), ⇑σ '' ℓ = ℓ ∨ Disjoint (⇑σ '' ℓ) ℓ) ∧
          (σ = 1 ∨ ∀ Q : gmsRootConjugates (U ⊔ R) R, σ Q ≠ Q)) ∧
      IsElementaryAbelian 2 E ∧ Nat.card E = 2 ^ n ∧
      E ⊓ gmsPermStabilizer U R = ⊥ ∧
      E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range ∧
      E ⊔ gmsSingerPermImage X U R ⊔ gmsPairStabilizer U R β =
        (gmsRootConjugateAction (U ⊔ R) R).range ∧
      E ⊓ gmsSingerPermImage X U R = ⊥ ∧
      ((E ⊔ gmsSingerPermImage X U R).subgroupOf
        (gmsRootConjugateAction (U ⊔ R) R).range).Normal ∧
      Nat.card (E ⊔ gmsSingerPermImage X U R : Subgroup _) = 2 ^ n * (2 ^ n - 1) ∧
      E ⊔ gmsSingerPermImage X U R ≠ (gmsRootConjugateAction (U ⊔ R) R).range ∧
      (∀ Q Z : gmsRootConjugates (U ⊔ R) R, ∃ f ∈ E ⊔ gmsSingerPermImage X U R, f Q = Z) ∧
      (∀ f ∈ E ⊔ gmsSingerPermImage X U R, f ≠ 1 → ∀ Q Z : gmsRootConjugates (U ⊔ R) R,
        f Q = Q → f Z = Z → Q = Z) ∧
      (E.comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤ E.comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥(E.comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf (E.comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        E) ∧
      ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)).Normal ∧
      gmsRootKernel (U ⊔ R) R ≤
        (E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      Nonempty (↥((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf
            ((E ⊔ gmsSingerPermImage X U R).comap (gmsRootConjugateAction (U ⊔ R) R)) ≃*
        ↥(E ⊔ gmsSingerPermImage X U R)) := by
  classical
  obtain ⟨-, hΔcard, -, -, -, -⟩ := gms_normal_root_partition_and_two_transitivity h h3
  obtain ⟨-, hdecH, hsupH, hinfH, -, hn4, hneven, hsq, hs4, -, hτex, -, hπker, -, -, -, -, -,
    -⟩ := gms_normal_root_even_pair_involution_affine_plane h h3 β hβ hd
  obtain ⟨τ, ⟨hτ, hτ2⟩, hτuniq⟩ := hτex
  obtain ⟨hG, hCH⟩ := gms_even_pair_involutionGeometry h h3 β hβ hd hτ hτ2
  obtain ⟨E, hEN, hEn, hEchar, hEreg, hreg, -, hEfree, hEdec⟩ :=
    EvenPairPlane.exists_regular_normal_translations hG hCH
  obtain ⟨hEel, hEcard, -, hFn, hFcard, hFtrans, hFfrob⟩ :=
    GMSDichotomy.affine_branch h h3 E hEN hEn hreg
  have hTH := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have hTcard := (GMSDichotomy.isCyclic_gmsSingerPermImage h h3).2
  have hHN : gmsPermStabilizer U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range := inf_le_left
  have hEH : E ⊓ gmsPermStabilizer U R = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    obtain ⟨hgE, hgH⟩ := mem_inf.1 hg
    exact hEfree g hgE (GMSDichotomy.mem_gmsPermStabilizer.1 hgH).2
  have hdecN : ∀ x ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      ∃ a ∈ E, ∃ b ∈ gmsPermStabilizer U R, x = a * b := by
    intro x hx
    obtain ⟨a, ha, b, hb, hbR, rfl⟩ := hEdec x hx
    exact ⟨a, ha, b, GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hb, hbR⟩, rfl⟩
  have hEHN : E ⊔ gmsPermStabilizer U R = (gmsRootConjugateAction (U ⊔ R) R).range := by
    refine le_antisymm (sup_le hEN hHN) fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdecN x hx
    exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
  have hHcard : Nat.card (gmsPermStabilizer U R) =
      (2 ^ n - 1) * Nat.card (gmsPairStabilizer U R β) := by
    rw [card_eq_mul_of_forall_eq_mul (H := gmsPairStabilizer U R β) hTH inf_le_left hdecH hinfH,
      hTcard]
  have hNcard : Nat.card (gmsRootConjugateAction (U ⊔ R) R).range =
      2 ^ n * (2 ^ n - 1) * Nat.card (gmsPairStabilizer U R β) := by
    rw [card_eq_mul_of_forall_eq_mul hEN hHN hdecN hEH, hEcard, hHcard, mul_assoc]
  have hET : E ⊓ gmsSingerPermImage X U R = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_left E hTH) hEH.le)
  have hFne : E ⊔ gmsSingerPermImage X U R ≠ (gmsRootConjugateAction (U ⊔ R) R).range := by
    intro hF
    have h1 := hNcard
    rw [← hF, hFcard] at h1
    have h16 : 16 ≤ 2 ^ n :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    have hpos : 0 < 2 ^ n * (2 ^ n - 1) := Nat.mul_pos (by omega) (by omega)
    have hd1 : Nat.card (gmsPairStabilizer U R β) = 1 := by
      have h2 := Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (mul_one _).symm)
      exact h2
    rw [hd1] at hd
    exact Nat.not_even_one hd
  obtain ⟨hEcn, hEck, hEcq⟩ := comap_normal_of_le_range (gmsRootConjugateAction (U ⊔ R) R)
    (gmsRootKernel (U ⊔ R) R) hπker E hEN hEn
  obtain ⟨hFcn, hFck, hFcq⟩ := comap_normal_of_le_range (gmsRootConjugateAction (U ⊔ R) R)
    (gmsRootKernel (U ⊔ R) R) hπker (E ⊔ gmsSingerPermImage X U R) (sup_le hEN (hTH.trans hHN))
    hFn
  refine ⟨hn4, hneven, hsq, hs4, hΔcard, hHcard, hNcard, E, hEN, hEn, hreg, hEreg,
    fun τ' hτ' hτ'2 => ?_, hEel, hEcard, hEH, hEHN, ?_, hET, hFn, hFcard, hFne, hFtrans,
    hFfrob, hEcn, hEck, hEcq, hFcn, hFck, hFcq⟩
  · rw [hτuniq τ' ⟨hτ', hτ'2⟩]
    exact hEchar
  · rw [sup_assoc, hsupH, hEHN]

end GMS

end CFSG.SeitzReduction.RankOne
