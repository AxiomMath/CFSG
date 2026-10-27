module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Act
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.C1GNBlockLemmas

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped MatrixGroups

namespace L238

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_twoElement_not_mem_blockQ {L : Subgroup G}
    (hL : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) :
    ∃ x ∈ L, x ∉ blockQ L ∧ ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have key : ∀ {Y : Type} [Group Y] (α : ↥L →* Y), α.ker = CFSG.pCore 2 ↥L →
      ∀ y : Y, y ≠ 1 → y * y = 1 → ∀ l : ↥L, α l = y →
      (l : G) ∈ L ∧ (l : G) ∉ blockQ L ∧ ∃ k : ℕ, (l : G) ^ 2 ^ k = 1 := by
    intro Y _ α hαk y hy1 hyy l hl
    refine ⟨l.2, fun hQ => hy1 ?_, ?_⟩
    · have : l ∈ α.ker := by rw [hαk]; exact (C56.mem_blockQ_iff l).mp hQ
      rw [← hl]
      exact this
    · have hmem : l * l ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, hl, hyy]
      rw [hαk] at hmem
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)) ⟨l * l, hmem⟩
      refine ⟨k + 1, ?_⟩
      have hk' : (l * l) ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have : (l : G) ^ 2 ^ (k + 1) = ((l * l) ^ 2 ^ k : ↥L) := by
        rw [← pow_two, ← pow_mul, pow_succ, mul_comm]
        rfl
      rw [this, hk']
      rfl
  rcases hL with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
    have : CharP F 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega) hq
    have h11 : (1 : F) + 1 = 0 := by
      have := CharTwo.two_eq_zero (R := F)
      rw [one_add_one_eq_two]
      exact this
    have hy1 : Lin2.slUpper (1 : F) ≠ 1 := by
      intro h
      have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
      simp [Lin2.slUpper_val] at this
    have hyy : Lin2.slUpper (1 : F) * Lin2.slUpper 1 = 1 := by
      rw [← Lin2.slUpper_add, h11, Lin2.slUpper_zero]
    obtain ⟨l, hl⟩ := hαs (Lin2.slUpper (1 : F))
    obtain ⟨h1, h2, h3⟩ := key α hαk _ hy1 hyy l hl
    exact ⟨l, h1, h2, h3⟩
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    let t : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
    have hy1 : t ≠ 1 := by decide
    have hyy : t * t = 1 := by decide
    obtain ⟨l, hl⟩ := hαs t
    obtain ⟨h1, h2, h3⟩ := key α hαk t hy1 hyy l hl
    exact ⟨l, h1, h2, h3⟩

omit [Finite G] in
theorem mem_blockQ_of_twoElement_alt3 {L : Subgroup G} (h3 : IsAltType L 3) {x : G} (hx : x ∈ L)
    (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ blockQ L := by
  obtain ⟨α, -, hαk, -⟩ := h3
  obtain ⟨k, hk⟩ := hx2
  let y : ↥L := ⟨x, hx⟩
  have hy : y ^ 2 ^ k = 1 := Subtype.ext hk
  have hcube : ∀ g : alternatingGroup (Fin 3), g ^ 3 = 1 := by decide
  have hα : α y ^ 2 ^ k = 1 := by rw [← map_pow, hy, map_one]
  have hdvd1 : orderOf (α y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hα
  have hdvd2 : orderOf (α y) ∣ 3 := orderOf_dvd_of_pow_eq_one (hcube _)
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left _ (by norm_num)
  have h1 : orderOf (α y) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hy1 : α y = 1 := orderOf_eq_one_iff.mp h1
  have : y ∈ α.ker := hy1
  rw [hαk] at this
  exact (C56.mem_blockQ_iff y).mpr this

omit [Finite G] in
theorem exists_sl2_model {L : Subgroup G}
    (h : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧ 0 < m ∧
      ∃ α : ↥L →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L := by
  rcases h with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨F, hF, hFin, hcard, α, hαs, hαk, -⟩ := hlin
    exact ⟨F, hF, hFin, n, hcard, by omega, α, hαs, hαk⟩
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    let K := GaloisField 2 2
    have hK : Nat.card K = 4 := by
      have := GaloisField.card 2 2 two_ne_zero
      rw [this]
      norm_num
    obtain ⟨e⟩ := Setup.Family.specialLinear_two_equiv_alternating_five K hK
    let _ : Fintype K := Fintype.ofFinite K
    refine ⟨K, inferInstance, inferInstance, 2, ?_, by norm_num,
      e.symm.toMonoidHom.comp α, e.symm.surjective.comp hαs, ?_⟩
    · rw [← Nat.card_eq_fintype_card, hK]
      norm_num
    · rw [MonoidHom.ker_comp_of_injective α e.symm.toMonoidHom e.symm.injective, hαk]

omit [Finite G] in
theorem dickson_block {L S₁ A : Subgroup G} (hS₁ : IsSylowTwoOf S₁ L) (hSA : S₁ ≤ A)
    (hAL : A ≤ L)
    (hmod : ∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧ 0 < m ∧
      ∃ α : ↥L →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L) :
    A = L ∨ A ≤ Subgroup.normalizer (S₁ : Set G) := by
  classical
  obtain ⟨F, hF, hFin, m, hcard, hm, α, hαs, hαk⟩ := hmod
  have hS₁L : S₁ ≤ L := hS₁.le
  let S₁' : Subgroup ↥L := S₁.subgroupOf L
  let A' : Subgroup ↥L := A.subgroupOf L
  have hker : α.ker ≤ S₁' := by
    intro l hl
    rw [hαk] at hl
    have : (l : G) ∈ blockQ L := (C56.mem_blockQ_iff l).mpr hl
    exact hS₁.pCoreOf_le this
  have hS₁'A' : S₁' ≤ A' := fun l hl => hSA hl
  have hS₁'2 : IsPGroup 2 S₁' := by
    have e : ↥S₁' ≃* ↥S₁ := Subgroup.subgroupOfEquivOfLe hS₁L
    exact hS₁.isPGroup.of_equiv e.symm
  let P : Subgroup SL(2, F) := S₁'.map α
  have hcomap : P.comap α = S₁' := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hker
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, hS₁'2.map α, ?_⟩
    show ¬ 2 ∣ P.relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_comap_of_surjective P hαs, hcomap]
    exact hS₁.2.2
  have hPK : P ≤ A'.map α := Subgroup.map_mono hS₁'A'
  rcases Lin2.dicksonLite hcard hm hPsyl hPK with hK | hK
  · left
    have h1 : A' ⊔ α.ker = ⊤ := by
      have := congrArg (Subgroup.comap α) hK
      rwa [Subgroup.comap_map_eq, Subgroup.comap_top] at this
    have hA' : A' = ⊤ := by
      rw [← h1]
      exact (sup_eq_left.mpr (hker.trans hS₁'A')).symm
    have : L ≤ A := (Subgroup.subgroupOf_eq_top).mp hA'
    exact le_antisymm hAL this
  · right
    intro a ha
    have haL : a ∈ L := hAL ha
    let a' : ↥L := ⟨a, haL⟩
    have ha' : a' ∈ A' := ha
    have hN := hK ⟨a', ha', rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyL : y ∈ L := hS₁L hy
      let y' : ↥L := ⟨y, hyL⟩
      have hy' : y' ∈ S₁' := hy
      have h1 : α y' ∈ P := ⟨_, hy', rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp hN (α y')).mp h1
      have h3 : a' * y' * a'⁻¹ ∈ S₁' := by
        rw [← hcomap]
        show α (a' * y' * a'⁻¹) ∈ P
        rw [map_mul, map_mul, map_inv]
        exact h2
      exact h3
    · intro hy
      have hyL : y ∈ L := by
        have h1 : a⁻¹ * (a * y * a⁻¹) * a ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem haL) (hS₁L hy)) haL
        simpa [mul_assoc] using h1
      let y' : ↥L := ⟨y, hyL⟩
      have hy' : a' * y' * a'⁻¹ ∈ S₁' := hy
      have h1 : α (a' * y' * a'⁻¹) ∈ P := ⟨_, hy', rfl⟩
      rw [map_mul, map_mul, map_inv] at h1
      have h2 := (Subgroup.mem_normalizer_iff.mp hN (α y')).mpr h1
      have h3 : y' ∈ S₁' := by
        rw [← hcomap]
        exact h2
      exact h3

theorem eq_of_le_isChi0Block
    {X S L Lh : Subgroup G} (hS : IsSylowTwoOf S X)
    (hLh : IsChi0Block X Lh)
    (hLtype : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) (hLLh : L ≤ Lh)
    (hnorm : S ⊓ Lh ≤ Subgroup.normalizer (L : Set G)) : L = Lh := by
  classical
  obtain ⟨x, hxL, hxQ, k, hxk⟩ := exists_twoElement_not_mem_blockQ hLtype
  have hS₁ : IsSylowTwoOf (S ⊓ Lh) Lh :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hLh.1.2.1 hLh.1.2.2
  set S₁ := S ⊓ Lh with hS₁def
  have hS₁Lh : S₁ ≤ Lh := inf_le_right
  have hA : L ⊔ S₁ ≤ Lh := sup_le hLLh hS₁Lh
  have hLQ : blockQ Lh ⊓ L ≤ blockQ L := by
    refine le_pCoreOf_of_normalizes inf_le_right ?_ ((C1.blockQ_isPGroup Lh).to_le inf_le_left)
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨C1.le_normalizer_blockQ Lh (hLLh hl), Subgroup.le_normalizer hl⟩
  have hmain : (∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧
      0 < m ∧ ∃ α : ↥Lh →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥Lh) →
      L = Lh := by
    intro hmod
    rcases dickson_block hS₁ le_sup_right hA hmod with hAeq | hAN
    ·
      have hLn : Lh ≤ Subgroup.normalizer (L : Set G) := by
        rw [← hAeq]
        exact sup_le Subgroup.le_normalizer hnorm
      have hnormal : (L.subgroupOf Lh).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLLh).mpr hLn
      have hpow : ∀ g : ↥Lh, ∃ j : ℕ, (g : G) ^ 2 ^ j ∈ L := by
        intro g
        have hgA : (g : G) ∈ L ⊔ S₁ := by
          rw [hAeq]
          exact g.2
        exact C1.exists_pow_mem_of_mem_sup hS₁.isPGroup hnorm hgA
      have h2 : IsPGroup 2 (↥Lh ⧸ L.subgroupOf Lh) := fun q =>
        QuotientGroup.induction_on q fun g => by
          obtain ⟨j, hj⟩ := hpow g
          refine ⟨j, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
          exact hj
      have htop := hLh.1.1.1 (L.subgroupOf Lh) h2
      exact le_antisymm hLLh ((Subgroup.subgroupOf_eq_top).mp htop)
    ·
      exfalso
      have hS₁A : IsSylowTwoOf S₁ (L ⊔ S₁) := C1GN.isSylowTwoOf_of_le hS₁ le_sup_right hA
      have hxA : x ∈ L ⊔ S₁ := Subgroup.mem_sup_left hxL
      have hz : IsPGroup 2 (Subgroup.zpowers x) := by
        have hcard : Nat.card (Subgroup.zpowers x) = orderOf x := Nat.card_zpowers x
        have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
        exact IsPGroup.of_card (by rw [hcard, hj])
      obtain ⟨y, hy, hzy⟩ := F7.isSylowTwoOf_exists_conj_le hS₁A
        ((Subgroup.zpowers_le).mpr hxA) hz
      have hyS : conjSub y S₁ = S₁ := B6.conjSub_eq_self (hAN hy)
      have hxS : x ∈ S₁ := by
        have := hzy (Subgroup.mem_zpowers x)
        rwa [hyS] at this
      have hxQ' : x ∈ blockQ L := by
        refine le_pCoreOf_of_normalizes (inf_le_left : L ⊓ S₁ ≤ L) ?_
          (hS₁.isPGroup.to_le (inf_le_right : L ⊓ S₁ ≤ S₁)) ⟨hxL, hxS⟩
        intro l hl
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hl, hAN (Subgroup.mem_sup_left hl)⟩
      exact hxQ hxQ'
  rcases hLh.2 with hlin | h3 | h5
  · exact hmain (exists_sl2_model (Or.inl hlin))
  · exfalso
    exact hxQ (hLQ ⟨mem_blockQ_of_twoElement_alt3 h3 (hLLh hxL) ⟨k, hxk⟩, hxL⟩)
  · exact hmain (exists_sl2_model (Or.inr h5))

end L238

end CFSG.QuasithinUnique
