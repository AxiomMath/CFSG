module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClQuot
public import CFSG.Blueprint.Catalog
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup

@[expose] def BarConfig (P : Type) [Group P] (p' f' p f : ℕ) : Prop :=
  ∃ (E : Subgroup (MulAut P)) (L : Subgroup P) (t : P) (J J₀ : Subgroup P),
    IsPGroup 2 E ∧ L ≤ fixedBy E ∧ IsPComponent 2 (L.subgroupOf (fixedBy E)) ∧
    L ≠ ⊤ ∧ Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f' ∧
    t ∈ L ∧ t * t = 1 ∧ t ≠ 1 ∧
    J ≤ centralizer {t} ∧ IsPComponent 2 (J.subgroupOf (centralizer {t})) ∧
    Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f ∧
    J₀ ≤ L ∧ J₀ ≤ J ∧ J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J

theorem center_eq_bot_of_simple_perfect' {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    have hc : commutator X = ⊥ := by
      rw [eq_bot_iff, commutator_def, commutator_le]
      intro a _ b _
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (h ▸ mem_top b) a)
    have htop := Group.IsPerfect.commutator_eq_top (G := X)
    rw [hc] at htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    apply hab
    have ha : a ∈ (⊥ : Subgroup X) := htop ▸ mem_top a
    have hb : b ∈ (⊥ : Subgroup X) := htop ▸ mem_top b
    rw [mem_bot] at ha hb
    rw [ha, hb]

theorem center_eq_bot_of_lieModel {X : Type} [Group X] [Group.IsPerfect X]
    {t : Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ} (ht : t = .PSL ∨ t = .PSp)
    (h : Blueprint.LieModel X t n p f) : center X = ⊥ := by
  have hcl : Assembly.LowTwoRank.StatedClassicalModel X t n p f := by
    rcases h with ⟨-, h⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · exact h
    all_goals rcases ht with rfl | rfl <;> exact absurd htag (by decide)
  rcases ht with rfl | rfl
  · have := (LieType.Simplicity.fam_PSL_simplicity X n p f hcl).2
    exact center_eq_bot_of_simple_perfect'
  · have := ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X n p f hcl
    exact center_eq_bot_of_simple_perfect'

variable {M : Type} [Group M] [Finite M]

theorem inf_center_eq_bot (hZ : IsPGroup 2 (center M)) {L : Subgroup M}
    (hc : center (↥L ⧸ pPrimeCore 2 ↥L) = ⊥) : L ⊓ center M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxZ⟩
  set y : L := ⟨x, hxL⟩ with hy
  have hyO : y ∈ pPrimeCore 2 L := by
    have hc' : (QuotientGroup.mk' (pPrimeCore 2 L) y) ∈ center (L ⧸ pPrimeCore 2 L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (mem_center_iff.1 hxZ g)
    rw [hc, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hc'
    exact hc'
  obtain ⟨k, hk⟩ := hZ ⟨x, hxZ⟩
  have hx2 : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [SubgroupClass.coe_pow] at this
  have hk' : y ^ 2 ^ k = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hx2)
  have hdvd : orderOf (⟨y, hyO⟩ : pPrimeCore 2 L) ∣ Nat.card (pPrimeCore 2 L) :=
    orderOf_dvd_natCard _
  have hcop := pPrimeCore_coprime_card (p := 2) (G := L)
  have hpow : orderOf (⟨y, hyO⟩ : pPrimeCore 2 L) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hpow
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf (⟨y, hyO⟩ : pPrimeCore 2 L) := by
      rw [hi]
      exact dvd_pow_self 2 hne
    exact absurd (Nat.dvd_gcd (dvd_refl 2) (h2.trans hdvd)) (by rw [hcop]; norm_num)
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  rw [mem_bot]
  exact congrArg (fun z : pPrimeCore 2 L => ((z : L) : M)) hi

@[expose] noncomputable def equivMapMk {L : Subgroup M} (hL : L ⊓ center M = ⊥) :
    L ≃* L.map (QuotientGroup.mk' (center M)) :=
  (MonoidHom.ofInjective (f := (QuotientGroup.mk' (center M)).comp L.subtype) (by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    have : (y : M) ∈ L ⊓ center M := ⟨y.2, hy⟩
    rw [hL, mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

omit [Finite M] in
theorem equivMapMk_apply {L : Subgroup M} (hL : L ⊓ center M = ⊥) (y : L) :
    ((equivMapMk hL y : L.map (QuotientGroup.mk' (center M))) : M ⧸ center M) =
      ((y : M) : M ⧸ center M) := rfl

end CFSG.ComponentClassification.GSThmB.QPUCl
