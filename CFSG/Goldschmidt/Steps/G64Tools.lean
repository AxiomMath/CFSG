module

public import CFSG.Goldschmidt.Steps.G64Basic
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.Goldschmidt.Steps.G62Basic
import CFSG.Goldschmidt.Steps.Balance
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.QCoreConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GeneralizedFittingSubgroupConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.Adapters.Involutions
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Walter.Bender1970.S3.CoreExchangeRank

public section

namespace CFSG.Goldschmidt.G64

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_eq_card_mul_index {A B : Subgroup G} (hBA : B ≤ A) :
    Nat.card A = Nat.card B * (B.subgroupOf A).index := by
  rw [← (B.subgroupOf A).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv]

theorem le_iSup_hyperplane {A D : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D)) :
    D ≤ ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : (B.subgroupOf A).index = 2),
      D ⊓ Subgroup.centralizer (B : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAcomm := hA.1
  have : IsElementaryAbelian 2 A :=
    { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (hA.2 x x.2) }
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  let _ : MulDistribMulAction A D := Subgroup.conjMulDistribMulActionOfLeNormalizer A D hAD
  have hp : ¬ 2 ∣ Nat.card D := fun h => (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := D) hp
  set X := ⨆ (B : Subgroup G) (_ : B ≤ A) (_ : (B.subgroupOf A).index = 2),
    D ⊓ Subgroup.centralizer (B : Set G) with hXdef
  have hle : ⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B D ≤
      X.comap D.subtype := by
    refine iSup₂_le fun B hB => ?_
    intro y hy
    set R : Subgroup G := B.map A.subtype with hR
    have hRA : R ≤ A := Subgroup.map_subtype_le B
    have hRB : R.subgroupOf A = B :=
      Subgroup.comap_map_eq_self_of_injective A.subtype_injective B
    have hRi : (R.subgroupOf A).index = 2 := by rw [hRB]; exact hB
    have hmem : (y : G) ∈ D ⊓ Subgroup.centralizer (R : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have hby := congrArg Subtype.val (hy ⟨b, hb⟩)
      change (b : G) * (y : G) * (b : G)⁻¹ = (y : G) at hby
      show (b : G) * (y : G) = (y : G) * (b : G)
      calc (b : G) * (y : G) = (b : G) * (y : G) * (b : G)⁻¹ * (b : G) := by group
        _ = (y : G) * (b : G) := by rw [hby]
    have hRX : D ⊓ Subgroup.centralizer (R : Set G) ≤ X :=
      le_iSup₂_of_le R hRA (le_iSup_of_le hRi le_rfl)
    exact Subgroup.mem_comap.mpr (hRX hmem)
  rw [hgen, top_le_iff] at hle
  intro x hx
  have hxX : (⟨x, hx⟩ : D) ∈ X.comap D.subtype := hle ▸ Subgroup.mem_top _
  exact hxX

theorem exists_hyperplane_inf_ne_bot {A D : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hA1 : A ≠ ⊥) (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDodd : Odd (Nat.card D))
    (hD1 : D ≠ ⊥) :
    ∃ B : Subgroup G, B ≤ A ∧ (B.subgroupOf A).index = 2 ∧
      D ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  exact hD1 (le_bot_iff.mp ((le_iSup_hyperplane hA hA1 hAD hDodd).trans
    (iSup₂_le fun B hB => iSup_le fun hi => (hcon B hB hi).le)))

theorem le_of_card_le_of_isCyclic {Z X Y : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ : IsCyclic Z) (hZp : IsPGroup p Z) (hXZ : X ≤ Z) (hYZ : Y ≤ Z)
    (hcard : Nat.card X ≤ Nat.card Y) : X ≤ Y := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ := (hZp.to_le hXZ).exists_card_eq
  obtain ⟨j, hj⟩ := (hZp.to_le hYZ).exists_card_eq
  have hij : i ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hi ▸ hj ▸ hcard)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) p (n := i)
    (by rw [hj]; exact pow_dvd_pow p hij)
  have hKY : K.map Y.subtype ≤ Y := Subgroup.map_subtype_le K
  have hKcard : Nat.card (K.map Y.subtype) = Nat.card X := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hK, hi]
  rw [← G53.eq_of_le_isCyclic_of_card_eq hZ (hKY.trans hYZ) hXZ hKcard]
  exact hKY

theorem exists_noncyclic_centralizer {A D : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : CFSG.Open.IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hAD : A ≤ Subgroup.normalizer (D : Set G)) (hDp : IsPGroup p D) (hD : ¬ IsCyclic D) :
    ∃ B : Subgroup G, B ≤ A ∧ Nat.card A ≤ 4 * Nat.card B ∧
      ¬ IsCyclic (D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  classical
  by_contra hcon
  push Not at hcon
  have hDodd : Odd (Nat.card D) := G62.odd_card_of_isPGroup hp hp2 hDp
  set 𝓗 : Set (Subgroup G) := {B | B ≤ A ∧ (B.subgroupOf A).index = 2} with h𝓗def
  have hcyc1 : ∀ B ∈ 𝓗, IsCyclic (D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :=
    fun B hB => hcon B hB.1 (by rw [card_eq_card_mul_index hB.1, hB.2]; omega)
  have hcyc2 : ∀ B₁ ∈ 𝓗, ∀ B₂ ∈ 𝓗,
      IsCyclic (D ⊓ Subgroup.centralizer ((B₁ ⊓ B₂ : Subgroup G) : Set G) : Subgroup G) := by
    intro B₁ hB₁ B₂ hB₂
    refine hcon (B₁ ⊓ B₂) (inf_le_left.trans hB₁.1) ?_
    have heq : (B₁ ⊓ B₂).subgroupOf A = B₁.subgroupOf A ⊓ B₂.subgroupOf A := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    have hidx : ((B₁ ⊓ B₂).subgroupOf A).index ≤ 4 := by
      rw [heq]
      exact Subgroup.index_inf_le.trans (by rw [hB₁.2, hB₂.2])
    rw [card_eq_card_mul_index (inf_le_left.trans hB₁.1)]
    rw [mul_comm]
    exact Nat.mul_le_mul_right _ hidx
  have hgen := le_iSup_hyperplane hA hA1 hAD hDodd
  by_cases h𝓗 : 𝓗.Nonempty
  · obtain ⟨B₀, hB₀, hmax⟩ := Set.exists_max_image 𝓗
      (fun B => Nat.card (D ⊓ Subgroup.centralizer (B : Set G) : Subgroup G))
      (Set.toFinite 𝓗) h𝓗
    have hle : ∀ B ∈ 𝓗, D ⊓ Subgroup.centralizer (B : Set G) ≤
        D ⊓ Subgroup.centralizer (B₀ : Set G) := fun B hB =>
      le_of_card_le_of_isCyclic hp (hcyc2 B hB B₀ hB₀) (hDp.to_le inf_le_left)
        (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)))
        (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right)))
        (hmax B hB)
    exact hD (G63.isCyclic_of_le (hcyc1 B₀ hB₀)
      (hgen.trans (iSup₂_le fun B hBA => iSup_le fun hi => hle B ⟨hBA, hi⟩)))
  · have hD1 : D = ⊥ := le_bot_iff.mp (hgen.trans
      (iSup₂_le fun B hBA => iSup_le fun hi => absurd ⟨B, hBA, hi⟩ h𝓗))
    exact hD (hD1 ▸ inferInstance)

end CFSG.Goldschmidt.G64

namespace CFSG.Goldschmidt.G64

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_card_eight {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (h8 : Nat.card A = 8)
    (hirr : ∀ V : Subgroup G, V ≤ A →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = ⊥ ∨ V = A)
    {b c : G} (hb : b ∈ A) (hb1 : b ≠ 1) (hc : c ∈ A) (hc1 : c ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n⁻¹ * b * n = c := by
  classical
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have hAcomm : IsMulCommutative A := hA.1
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  have : N.Normalizes A := ⟨le_rfl⟩
  have : Fintype A := Fintype.ofFinite A
  have : Fintype N := Fintype.ofFinite N
  have hsq : ∀ y : A, y * y = 1 := fun y => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact hA.2 y y.2
  have hsmul : ∀ (m : N) (y : A), ((m • y : A) : G) = (m : G) * y * (m : G)⁻¹ := fun m y =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe N A m y
  set orb : A → Finset A := fun x => Finset.univ.image (fun n : N => n • x) with horb
  have hmem_orb : ∀ x : A, x ∈ orb x := fun x =>
    Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ _⟩
  have hstab : ∀ (x : A) (m : N), ∀ y ∈ orb x, m • y ∈ orb x := by
    intro x m y hy
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨m * n, Finset.mem_univ _, mul_smul _ _ _⟩
  have hne1 : ∀ x : A, x ≠ 1 → ∀ y ∈ orb x, y ≠ 1 := by
    intro x hx y hy h1
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hy
    exact hx (MulAction.injective n (h1.trans (smul_one n).symm))
  have hprod : ∀ x : A, ∏ y ∈ orb x, y = 1 := by
    intro x
    set π := ∏ y ∈ orb x, y with hπ
    have hfix : ∀ m : N, m • π = π := by
      intro m
      have hinj : Function.Injective (fun y : A => m • y) := MulAction.injective m
      have himage : (orb x).image (fun y => m • y) = orb x :=
        Finset.eq_of_subset_of_card_le (fun z hz => by
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
          exact hstab x m y hy) (by rw [Finset.card_image_of_injective _ hinj])
      calc m • π = ∏ y ∈ orb x, m • y := map_prod (MulDistribMulAction.toMonoidHom A m) _ _
        _ = ∏ y ∈ (orb x).image (fun y => m • y), y :=
          (Finset.prod_image (f := fun y => y) fun _ _ _ _ h => hinj h).symm
        _ = π := by rw [himage]
    set Z := Subgroup.zpowers (π : G) with hZ
    have hZA : Z ≤ A := Subgroup.zpowers_le.mpr π.2
    have hNZ : N ≤ Subgroup.normalizer (Z : Set G) := by
      intro m hm
      have hm' : (m : G) * π * (m : G)⁻¹ = π := by
        have := congrArg Subtype.val (hfix ⟨m, hm⟩)
        rwa [hsmul] at this
      refine mem_normalizer_of_map_conj_le ?_
      rw [hZ, MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.mpr ?_
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hm']
      exact Subgroup.mem_zpowers _
    rcases hirr Z hZA hNZ with h | h
    · exact Subtype.ext (Subgroup.zpowers_eq_bot.mp h)
    · exfalso
      have hcard : Nat.card Z ≤ 2 := by
        rw [hZ, Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one two_pos (hA.2 π π.2)
      rw [h, h8] at hcard
      omega
  have hfour : ∀ x : A, x ≠ 1 → 4 ≤ (orb x).card := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hpos : 0 < (orb x).card := Finset.card_pos.mpr ⟨x, hmem_orb x⟩
    interval_cases h : (orb x).card
    · obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
      have := hprod x
      rw [hu, Finset.prod_singleton] at this
      exact hne1 x hx u (hu ▸ Finset.mem_singleton_self u) this
    · obtain ⟨u, v, huv, huvO⟩ := Finset.card_eq_two.mp h
      have := hprod x
      rw [huvO, Finset.prod_pair huv] at this
      apply huv
      calc u = u * (u * v) := by rw [this, mul_one]
        _ = v := by rw [← mul_assoc, hsq, one_mul]
    · obtain ⟨u, v, w, huv, huw, hvw, hO⟩ := Finset.card_eq_three.mp h
      have hπ := hprod x
      rw [hO, Finset.prod_insert (by simp [huv, huw]), Finset.prod_pair hvw] at hπ
      have hw : w = u * v := by
        have h1 : u * v * w = 1 := by rw [mul_assoc]; exact hπ
        rw [eq_inv_of_mul_eq_one_right h1]
        exact inv_eq_of_mul_eq_one_right (hsq (u * v))
      set V := Subgroup.zpowers (u : G) ⊔ Subgroup.zpowers (v : G) with hV
      have hOV : ∀ y ∈ orb x, (y : G) ∈ V := by
        intro y hy
        rw [hO] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · exact (le_sup_left : Subgroup.zpowers (y : G) ≤ V) (Subgroup.mem_zpowers _)
        · exact (le_sup_right : Subgroup.zpowers (y : G) ≤ V) (Subgroup.mem_zpowers _)
        · rw [hw, Subgroup.coe_mul]
          exact V.mul_mem ((le_sup_left : Subgroup.zpowers (u : G) ≤ V) (Subgroup.mem_zpowers _))
            ((le_sup_right : Subgroup.zpowers (v : G) ≤ V) (Subgroup.mem_zpowers _))
      have huO : u ∈ orb x := by rw [hO]; simp
      have hvO : v ∈ orb x := by rw [hO]; simp
      have hVA : V ≤ A := sup_le (Subgroup.zpowers_le.mpr u.2) (Subgroup.zpowers_le.mpr v.2)
      have hNV : N ≤ Subgroup.normalizer (V : Set G) := by
        intro m hm
        refine mem_normalizer_of_map_conj_le ?_
        rw [hV, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hsmul ⟨m, hm⟩ u]
          exact hOV _ (hstab x ⟨m, hm⟩ u huO)
        · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hsmul ⟨m, hm⟩ v]
          exact hOV _ (hstab x ⟨m, hm⟩ v hvO)
      have hu1 : (u : G) ≠ 1 := fun h1 => hne1 x hx u huO (Subtype.ext h1)
      have hv1 : (v : G) ≠ 1 := fun h1 => hne1 x hx v hvO (Subtype.ext h1)
      rcases hirr V hVA hNV with h' | h'
      · exact hu1 (Subgroup.mem_bot.mp (h' ▸ (le_sup_left : Subgroup.zpowers (u : G) ≤ V)
          (Subgroup.mem_zpowers _)))
      · have hu2 : orderOf (u : G) = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime (hA.2 u u.2) hu1
        have hv2 : orderOf (v : G) = 2 := by
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          exact orderOf_eq_prime (hA.2 v v.2) hv1
        have hdisj : Disjoint (Subgroup.zpowers (u : G)) (Subgroup.zpowers (v : G)) := by
          rw [Subgroup.disjoint_def]
          intro g hgu hgv
          rcases eq_one_or_eq_of_mem_zpowers hu2 hgu with h1 | h1
          · exact h1
          · rcases eq_one_or_eq_of_mem_zpowers hv2 hgv with h2 | h2
            · exact h2
            · exact absurd (Subtype.ext (h1.symm.trans h2)) huv
        have hcomm : Subgroup.zpowers (u : G) ≤
            Subgroup.normalizer (Subgroup.zpowers (v : G) : Set G) := by
          refine Subgroup.zpowers_le.mpr ((Subgroup.centralizer_le_normalizer _) ?_)
          rw [centralizer_zpowers_eq', Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (mul_comm u v)
        have hcardV : Nat.card V = 4 := by
          rw [hV, sup_comm, card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hcomm hdisj.symm,
            Nat.card_zpowers, Nat.card_zpowers, hu2, hv2]
        rw [h', h8] at hcardV
        omega
  set b' : A := ⟨b, hb⟩ with hb'
  set c' : A := ⟨c, hc⟩ with hc'
  have hb'1 : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hc'1 : c' ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hsub : ∀ x : A, x ≠ 1 → orb x ⊆ Finset.univ.erase 1 := fun x hx y hy =>
    Finset.mem_erase.mpr ⟨hne1 x hx y hy, Finset.mem_univ _⟩
  have hcard7 : (Finset.univ.erase (1 : A)).card = 7 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, h8]
  have hnd : ¬ Disjoint (orb b') (orb c') := by
    intro hdisj
    have h1 := Finset.card_union_of_disjoint hdisj
    have h2 := Finset.card_le_card (Finset.union_subset (hsub b' hb'1) (hsub c' hc'1))
    have := hfour b' hb'1
    have := hfour c' hc'1
    omega
  obtain ⟨y, hyb, hyc⟩ := Finset.not_disjoint_iff.mp hnd
  obtain ⟨n₁, -, hn₁⟩ := Finset.mem_image.mp hyb
  obtain ⟨n₂, -, hn₂⟩ := Finset.mem_image.mp hyc
  have hcb : c' = (n₂⁻¹ * n₁) • b' := by
    rw [mul_smul, hn₁, ← hn₂, inv_smul_smul]
  refine ⟨((n₂⁻¹ * n₁ : N) : G)⁻¹, N.inv_mem (n₂⁻¹ * n₁).2, ?_⟩
  have h := congrArg Subtype.val hcb
  rw [hsmul] at h
  rw [inv_inv]
  exact h.symm

end CFSG.Goldschmidt.G64

namespace CFSG.Goldschmidt.G64

open CFSG.GorensteinWalter hiding oddCoreOf
open CFSG.Walter

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_oddCoreOf {H : Subgroup G} {a : G} (haH : a ∈ H) (ha2 : a * a = 1)
    (hF : CFSG.fittingSubgroupOf (oddCoreOf H) ≤ Subgroup.centralizer ({a} : Set G)) :
    oddCoreOf H ≤ Subgroup.centralizer ({a} : Set G) := by
  set O := oddCoreOf H with hOdef
  set F := CFSG.fittingSubgroupOf O with hFdef
  have hOodd : Odd (Nat.card O) := Balance.odd_card_oddCoreOf H
  have hOsolv : Group.IsSolvable O := CFSG.FeitThompson.isSolvable_of_odd_natCard O hOodd
  have haO : a ∈ Subgroup.normalizer (O : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => Balance.conj_mem_oddCoreOf haH hy, fun hy => ?_⟩
    have := Balance.conj_mem_oddCoreOf (H.inv_mem haH) hy
    simpa [mul_assoc] using this
  have hFn : IsNormalIn F O := fittingSubgroupOf_isNormalIn O
  have haF : Subgroup.zpowers a ≤ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro f hf
    exact Subgroup.mem_centralizer_singleton_iff.mp (hF hf)
  have h1 : ⁅Subgroup.zpowers a, F⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr haF
  have h2 : ⁅⁅F, O⁆, Subgroup.zpowers a⁆ = ⊥ := by
    have hFO : ⁅F, O⁆ ≤ F := by
      rw [Subgroup.commutator_le]
      intro f hf o ho
      have hof : o * f⁻¹ * o⁻¹ ∈ F := hFn.2 o ho _ (F.inv_mem hf)
      rw [commutatorElement_def, mul_assoc, mul_assoc]
      exact F.mul_mem hf (by simpa [mul_assoc] using hof)
    refine le_bot_iff.mp ((Subgroup.commutator_mono hFO le_rfl).trans ?_)
    rw [Subgroup.commutator_comm, h1]
  have h3 : ⁅⁅O, Subgroup.zpowers a⁆, F⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (by rw [h1, Subgroup.commutator_bot_left]) h2
  have h4 : ⁅O, Subgroup.zpowers a⁆ ≤ F := by
    refine (le_inf (commutator_zpowers_le_of_mem_normalizer haO)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)).trans ?_
    exact fact_1_2_centralizer_fitting_le_fitting O hOsolv
  have h5 : ⁅⁅O, Subgroup.zpowers a⁆, Subgroup.zpowers a⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono h4 le_rfl).trans ?_)
    rw [Subgroup.commutator_comm, h1]
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers a)) (Nat.card O) := by
    rw [Nat.card_zpowers]
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
    refine Nat.Coprime.coprime_dvd_left hdvd ?_
    exact Nat.coprime_two_left.mpr hOodd
  have h6 := commutator_le_commutator_commutator O (Subgroup.zpowers a)
    (Subgroup.zpowers_le.mpr haO) hcop
  have h7 : ⁅O, Subgroup.zpowers a⁆ = ⊥ := le_bot_iff.mp (h5 ▸ h6)
  have h8 : O ≤ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h7
  rwa [centralizer_zpowers_eq'] at h8

variable {S : Sylow 2 G} {A : Subgroup G}

theorem eq_centralizer (hG : GoldSetting G S A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {H : Subgroup G} (hH : H ≠ ⊤) (hAH : A ≤ H)
    (hCH : Subgroup.centralizer ({a} : Set G) ≤ H) (haF : a ∈ generalizedFittingSubgroupOf H)
    (hAF : ∀ b ∈ A, b ∈ generalizedFittingSubgroupOf H → b = 1 ∨ b = a) :
    H = Subgroup.centralizer ({a} : Set G) := by
  obtain ⟨-, -, T, hTSyl, hAT, hcl, -⟩ := G62.isSStarIn_of_le hG hH hAH
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hG.elem.2 a ha
  have haord : orderOf a = 2 := orderOf_eq_prime (hG.elem.2 a ha) ha1
  have haH : a ∈ H := hAH ha
  have haT : a ∈ T := hAT ha
  have hFn := generalizedFittingSubgroupOf_isNormalIn H
  have hconj : ∀ h ∈ H, h⁻¹ * a * h ∈ T → h⁻¹ * a * h = a := by
    intro h hh hT
    have hA' : h⁻¹ * a * h ∈ A := hcl a ha h hh hT
    have hF' : h⁻¹ * a * h ∈ generalizedFittingSubgroupOf H := by
      have := hFn.2 h⁻¹ (H.inv_mem hh) a haF
      simpa using this
    rcases hAF _ hA' hF' with h1 | h1
    · exfalso
      apply ha1
      calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · exact h1
  have haZ : ∀ t ∈ T, t * a = a * t := by
    intro t ht
    have h1 := hconj t (hTSyl.1 ht) (T.mul_mem (T.mul_mem (T.inv_mem ht) haT) ht)
    calc t * a = t * (t⁻¹ * a * t) := by rw [h1]
      _ = a * t := by group
  have hTH : T ≤ H := hTSyl.1
  set T' : Sylow 2 H :=
    { toSubgroup := T.subgroupOf H
      isPGroup' := hTSyl.2.1.comap_of_injective H.subtype H.subtype_injective
      is_maximal' := fun {Q} hQ hTQ => by
        have hQ' : IsPGroup 2 (Q.map H.subtype) := hQ.map H.subtype
        have hTQ' : T ≤ Q.map H.subtype := fun t ht =>
          ⟨⟨t, hTH ht⟩, hTQ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
        have heq := hTSyl.2.2 (Q.map H.subtype) (Subgroup.map_subtype_le Q) hQ' hTQ'
        rw [← heq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
          H.subtype_injective] } with hT'
  have haT' : (⟨a, haH⟩ : H) ∈ (T' : Subgroup H) := Subgroup.mem_subgroupOf.mpr haT
  set z : (T' : Subgroup H) := ⟨⟨a, haH⟩, haT'⟩ with hz
  have hzZ : z ∈ Subgroup.center (T' : Subgroup H) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact haZ _ (Subgroup.mem_subgroupOf.mp g.2)
  have hz2 : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact haord
  have hwc : ∀ g : H, g⁻¹ * (z : H) * g ∈ (T' : Subgroup H) → g⁻¹ * (z : H) * g = z := by
    intro g hg
    apply Subtype.ext
    exact hconj g g.2 (Subgroup.mem_subgroupOf.mp hg)
  obtain ⟨hfact, -⟩ := CFSG.Adapters.glauberman_zStar T' z hzZ hz2 hwc
  have hcq : ∀ q : ℕ, q.Prime → q ≠ 2 → a ∈ Subgroup.centralizer (qCoreOf H q : Set G) :=
    fun q hq hq2 => mem_centralizer_qCoreOf_of_mem_fstar haF ha2 hq hq2
  have hOn : IsNormalIn (oddCoreOf H) H :=
    ⟨Subgroup.map_subtype_le _, fun _ hh _ hy => Balance.conj_mem_oddCoreOf hh hy⟩
  have hFOn : IsNormalIn (CFSG.fittingSubgroupOf (oddCoreOf H)) H := by
    refine G63.isNormalIn_of_le_normalizer ((fittingSubgroupOf_isNormalIn _).1.trans hOn.1)
      fun h hh => G53.mem_normalizer_fittingSubgroupOf (le_normalizer_of_isNormalIn hOn hh)
  have hFOodd : Odd (Nat.card (CFSG.fittingSubgroupOf (oddCoreOf H))) :=
    Odd.of_dvd_nat (Balance.odd_card_oddCoreOf H)
      (Subgroup.card_dvd_of_le (fittingSubgroupOf_isNormalIn _).1)
  have hO : oddCoreOf H ≤ Subgroup.centralizer ({a} : Set G) :=
    le_centralizer_oddCoreOf haH ha2 (le_centralizer_of_forall hcq hFOn
      (CFSG.fittingSubgroupOf_isNilpotent _) hFOodd)
  refine le_antisymm (fun h hh => ?_) hCH
  obtain ⟨c, hc, k, hk, hck⟩ := hfact ⟨h, hh⟩
  have hc' : (c : G) * a = a * c := by
    have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    exact this
  have hk' : (k : G) ∈ oddCoreOf H := ⟨k, hk, rfl⟩
  have hk'' : (k : G) * a = a * k := Subgroup.mem_centralizer_singleton_iff.mp (hO hk')
  have hh' : h = (c : G) * k := congrArg Subtype.val hck
  rw [Subgroup.mem_centralizer_singleton_iff, hh']
  calc (c : G) * k * a = c * (k * a) := by group
    _ = c * (a * k) := by rw [hk'']
    _ = (c * a) * k := by group
    _ = a * (c * k) := by rw [hc']; group

theorem fstarZero_conjBy (H : Subgroup G) (g : G) :
    fstarZero (H.conjBy g) = (fstarZero H).conjBy g := by
  have hinj := (MulAut.conj g).injective
  have hC : ∀ X : Subgroup G, Subgroup.centralizer ((X.conjBy g : Subgroup G) : Set G) =
      (Subgroup.centralizer (X : Set G)).conjBy g := by
    intro X
    show _ = Subgroup.map _ _
    rw [map_centralizer_mulEquiv]
    rfl
  have hF : CFSG.fittingSubgroupOf (H.conjBy g) =
      (CFSG.fittingSubgroupOf H).map (MulAut.conj g).toMonoidHom :=
    fittingSubgroupOf_conjugateSubgroup H g
  have hFs : GorensteinWalter.generalizedFittingSubgroupOf (H.conjBy g) =
      (GorensteinWalter.generalizedFittingSubgroupOf H).map (MulAut.conj g).toMonoidHom :=
    generalizedFittingSubgroupOf_conjugateSubgroup H g
  unfold fstarZero
  rw [hF, hFs]
  show _ = Subgroup.map _ _
  rw [Subgroup.map_sup, Subgroup.map_inf_eq _ _ _ hinj, Subgroup.map_commutator]
  congr 2
  rw [← Subgroup.map_commutator]
  exact hC _

theorem qCoreOf_fstarZero_conjBy (H : Subgroup G) (g : G) (p : ℕ) :
    qCoreOf (fstarZero (H.conjBy g)) p = (qCoreOf (fstarZero H) p).conjBy g := by
  rw [fstarZero_conjBy]
  exact qCoreOf_conjugateSubgroup _ g p

end CFSG.Goldschmidt.G64
