module

public import CFSG.StronglyEmbedded.BenderBorelRegularRoot
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearTorus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3

public section

namespace CFSG.Open

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Matrix LinearAlgebra.Projectivization MatrixGroups

noncomputable section

theorem bender_pgl2_borel_full (n : ℕ) (hn : 2 ≤ n) :
    fusionBenderBorel (Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField n))
      (2 ^ n) 1 := by
  let K := BinaryGaloisField n
  let q := 2 ^ n
  let Omega := ℙ K (Fin 2 → K)
  let G := Matrix.ProjGenLinGroup (Fin 2) K
  classical
  let : Fintype K := Fintype.ofFinite K
  let : Finite G :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hn0 : n ≠ 0 := by omega
  have hKcard : Nat.card K = q := by
    simpa [K, q, BinaryGaloisField] using
      GaloisField.card 2 n hn0
  rcases External.huppert_blackburn_XI_example_1_3_a K with
    ⟨hOmegaCard, rho, iota, hrho, _hiota, hiota_apply, hrho_apply,
      _hiota_normal, _hiota_index, hsharp, hlarge,
      _hsmall_two, _hsmall_three⟩
  obtain ⟨rhoPSL, _hrhoPSL, hrhoPSL_apply, htwoPSL⟩ :=
    External.huppert_II_6_11_projective_action
      (K := K) 2 (by omega)
  have hcompat
      (x : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :
      rho (iota x) = rhoPSL x := by
    rcases QuotientGroup.mk'_surjective
        (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) K)) x with
      ⟨A, rfl⟩
    apply Equiv.ext
    intro z
    rw [hiota_apply]
    rw [hrho_apply _ _ _ rfl, hrhoPSL_apply]
  let : MulAction G Omega := MulAction.compHom Omega rho
  let : FaithfulSMul G Omega :=
    faithfulSMul_iff.mpr (by
      intro g hg
      apply hrho
      apply Equiv.ext
      intro z
      have hgz := hg z
      change rho g z = z at hgz
      calc
        rho g z = z := hgz
        _ = rho 1 z := by rw [map_one]; rfl)
  have htwo : MulAction.IsMultiplyPretransitive G Omega 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    rcases htwoPSL a b c d hab hcd with ⟨x, hxa, hxb⟩
    refine ⟨iota x, ?_, ?_⟩
    · change rho (iota x) a = c
      rw [hcompat]
      exact hxa
    · change rho (iota x) b = d
      rw [hcompat]
      exact hxb
  have hat_most_two :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
          ¬ (g • a = a ∧ g • b = b ∧ g • c = c) := by
    intro g hg a b c hab hac hbc hfix
    have hu := hsharp a b c a b c hab hac hbc hab hac hbc
    apply hg
    change rho g a = a ∧ rho g b = b ∧ rho g c = c at hfix
    have hone_fix :
        rho (1 : G) a = a ∧
          rho (1 : G) b = b ∧ rho (1 : G) c = c := by
      rw [map_one]
      exact ⟨rfl, rfl, rfl⟩
    exact hu.unique hfix hone_fix
  have hq_ge_four : 4 ≤ q := by
    simpa [q] using
      (Nat.pow_le_pow_right (n := 2) (by omega) hn)
  have hKgt : 3 < Nat.card K := by omega
  rcases hlarge hKgt with
    ⟨_hsimple, _hnoncommutative, hno_regular⟩
  let : Fintype Omega := Fintype.ofFinite Omega
  have hdegree : Fintype.card Omega = q + 1 := by
    rw [← Nat.card_eq_fintype_card, hOmegaCard, hKcard]
  have hdegree_gt_one : 1 < Fintype.card Omega := by
    rw [hdegree]
    omega
  obtain ⟨pinf, b, hpinf_b⟩ :=
    Fintype.one_lt_card_iff.mp hdegree_gt_one
  have hno_regular' :
      ¬ ∃ R : Subgroup G,
        R.Normal ∧ R ≠ ⊥ ∧
          ∀ x y : Omega, ∃! r : R, (r : G) • x = y := by
    intro h
    apply hno_regular
    rcases h with ⟨R, hRnormal, hRne, hRregular⟩
    refine ⟨R, hRnormal, hRne, ?_⟩
    intro x y
    rcases hRregular x y with ⟨r, hr, hr_unique⟩
    refine ⟨r, ?_, ?_⟩
    · change rho (r : G) x = y
      exact hr
    · intro s hs
      apply hr_unique s
      change rho (s : G) x = y at hs
      exact hs
  obtain ⟨F, hFrob⟩ :=
    External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
      htwo hat_most_two hno_regular' pinf b hpinf_b
  let D := MulAction.stabilizer (MulAction.stabilizer G pinf)
    (⟨b, hpinf_b.symm⟩ : SubMulAction.ofStabilizer G pinf)
  have hFrob' : IsFrobeniusGroupWithKernelComplement F D := hFrob
  have hFcard : Nat.card F = q :=
    External.huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      q hdegree htwo pinf b hpinf_b F hFrob
  let H := MulAction.stabilizer G pinf
  let R : Subgroup G := F.map H.subtype
  let T : Subgroup G := D.map H.subtype
  let X := SubMulAction.ofStabilizer G pinf
  let : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_multi : MulAction.IsMultiplyPretransitive H X 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := pinf)).mp htwo
  let : MulAction.IsPretransitive H X :=
    (MulAction.is_one_pretransitive_iff (G := H) (α := X)).mp hstab_multi
  have hFregular : ∀ x y : X, ∃! f : F, (f : H) • x = y :=
    External.huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement'
        (inferInstance : MulAction.IsPretransitive H X)
  have hRregular : IsRegularOn R
      {omega : Omega | omega ≠ pinf} :=
    regularOn_compl_of_stabilizer_subgroup pinf F hFregular
  have hRcard : Nat.card R = q := by
    calc
      Nat.card R = Nat.card F :=
        Subgroup.card_map_of_injective H.subtype_injective
      _ = q := hFcard
  have hRp : IsPGroup 2 R :=
    IsPGroup.of_card (by simpa [q] using hRcard)
  have hnormalizer :
      Subgroup.normalizer (R : Set G) = MulAction.stabilizer G pinf := by
    have hRle : R ≤ MulAction.stabilizer G pinf := by
      change R ≤ H
      apply Subgroup.map_le_iff_le_comap.mpr
      intro f hf
      exact f.property
    have hRne : R ≠ ⊥ := by
      intro hRbot
      change F.map H.subtype = (⊥ : Subgroup G) at hRbot
      have hFbot : F = ⊥ := by
        exact (Subgroup.map_eq_bot_iff_of_injective F
          H.subtype_injective).mp hRbot
      have hFcard_one : Nat.card F = 1 := by
        rw [hFbot, Subgroup.card_bot]
      have : q = 1 := hFcard.symm.trans hFcard_one
      omega
    have hHle : H ≤ Subgroup.normalizer (R : Set G) := by
      have hmap := Subgroup.le_normalizer_map (H := F) H.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hFrob.normal] at hmap
      change H ≤ Subgroup.normalizer (F.map H.subtype : Set G)
      have htop : (⊤ : Subgroup H).map H.subtype = H := by
        ext g
        constructor
        · rintro ⟨h, _, rfl⟩
          exact h.property
        · intro hg
          exact ⟨⟨g, hg⟩, trivial, rfl⟩
      rw [htop] at hmap
      exact hmap
    exact normalizer_eq_stabilizer_of_regular_compl R pinf hRle hRne
      hRregular hHle
  have hsharp_smul :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
        ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c' := hsharp
  obtain ⟨p, f, hp, hf, hqpow, hFelem⟩ :=
    External.huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
      q hdegree htwo hsharp_smul pinf b hpinf_b F hFrob
  have hp_two : p = 2 := by
    apply Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two
    change p ∣ q
    rw [hqpow]
    exact dvd_pow_self p (by omega)
  have hFelem_two : IsElementaryAbelian 2 F := hp_two ▸ hFelem
  let : IsElementaryAbelian 2 F := hFelem_two
  let eR : F ≃* R := F.equivMapOfInjective H.subtype H.subtype_injective
  have hRpow : ∀ r : R, r ^ 2 = 1 := by
    intro r
    apply eR.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := F)) (eR.symm r)
  let : IsMulCommutative R := by
    let : CommGroup F := IsMulCommutative.instCommGroup
    refine ⟨⟨fun r s => eR.symm.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact mul_comm _ _
  have hRcenterPow : ∀ z ∈ Subgroup.center R, z ^ 2 = 1 := by
    intro z _
    exact hRpow z
  have hRcenterCard : Nat.card (Subgroup.center R) = q := by
    rw [Subgroup.center_eq_top, Subgroup.card_top, hRcard]
  have hRle : R ≤ H := Subgroup.map_subtype_le F
  have hTle : T ≤ H := Subgroup.map_subtype_le D
  have hRTinf : R ⊓ T = ⊥ := by
    change F.map H.subtype ⊓ D.map H.subtype = ⊥
    rw [← Subgroup.map_inf _ _ _ H.subtype_injective,
      hFrob'.isComplement'.disjoint.eq_bot, Subgroup.map_bot]
  have hRTsup : R ⊔ T = H := by
    change F.map H.subtype ⊔ D.map H.subtype = H
    rw [← Subgroup.map_sup, hFrob'.isComplement'.sup_eq_top]
    rw [Subgroup.map_top, H.range_subtype]
  have hDambient : T = MulAction.stabilizer G pinf ⊓
      MulAction.stabilizer G b := by
    ext g
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨d.property, MulAction.mem_stabilizer_iff.mpr
        (congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hd))⟩
    · intro hg
      have hgH : g ∈ H := hg.1
      refine ⟨⟨g, hgH⟩, ?_, rfl⟩
      change (⟨g, hgH⟩ : H) ∈ MulAction.stabilizer H
        (⟨b, hpinf_b.symm⟩ : X)
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      exact MulAction.mem_stabilizer_iff.mp hg.2
  have hTcyclic : IsCyclic T := by
    rw [hDambient]
    exact pgl_twoPointStabilizer_isCyclic hrho_apply htwo pinf b hpinf_b
  obtain ⟨_z, _hz, eD, _hconj⟩ :=
    External.huppert_blackburn_XI_twoPointStabilizer_exists_conjEquiv
      htwo hsharp_smul pinf b hpinf_b F hFrob
  have hDcard : Nat.card D = q - 1 := by
    calc
      Nat.card D = Nat.card {x : F // x ≠ 1} := Nat.card_congr eD
      _ = Nat.card F - 1 := by
        let : Fintype F := Fintype.ofFinite F
        let : Fintype {x : F // x ≠ 1} := Fintype.ofFinite _
        simp only [Nat.card_eq_fintype_card]
        rw [Fintype.card_subtype_compl (fun x : F => x = 1)]
        simp
      _ = q - 1 := by rw [hFcard]
  have hTcard : Nat.card T = q - 1 :=
    (Subgroup.card_map_of_injective H.subtype_injective).trans hDcard
  have hq_even : Even q := by
    dsimp only [q]
    exact Nat.even_pow.mpr ⟨even_two, hn0⟩
  have hTodd : Odd (Nat.card T) := by
    rw [hTcard]
    exact Nat.Even.sub_odd (by positivity : 0 < q) hq_even odd_one
  have hmove : ∃ g : G, g • pinf ≠ pinf := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G pinf b
    exact ⟨g, hg ▸ hpinf_b.symm⟩
  exact fusionBenderBorel_of_regular_root pinf R T q 1 hRle hTle
    (by rw [hnormalizer]) hRTinf hRTsup hTcyclic hTodd hRp
    (hRcard ▸ hq_even) hmove hRregular hRcenterPow hRcenterCard
    (by simpa using hRcard)

theorem bender_psl2_borel_full (n : ℕ) (hn : 2 ≤ n) :
    fusionBenderBorel PSL(2, GaloisField 2 n) (2 ^ n) 1 := by
  obtain ⟨e⟩ := psl_charTwo_equiv_pgl n (by omega)
  let : Finite (Matrix.ProjGenLinGroup (Fin 2) (BinaryGaloisField n)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (PSL2BinaryMatrixGroup n) := Finite.of_injective e e.injective
  exact (bender_pgl2_borel_full n hn).map_mulEquiv e.symm

end

end CFSG.Open
