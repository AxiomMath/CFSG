module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorLineRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbedding

open Subgroup

theorem map_normalizerMonoidHom_eq {Y : Type*} [Group Y] {A : Subgroup Y} {t : Y}
    (htA : t ∈ normalizer (A : Set Y)) {F F' : Subgroup A}
    (h : (F.map A.subtype).map (MulAut.conj t).toMonoidHom = F'.map A.subtype) :
    F.map (A.normalizerMonoidHom ⟨t, htA⟩).toMonoidHom = F' := by
  apply map_injective A.subtype_injective
  rw [← h, map_map, map_map]
  congr 1

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open Subgroup CFSG.Open
open scoped commutatorElement

theorem four_le_pRank_of_lineTransitive {Y : Type} [Group Y] [Finite Y] {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hs5 : s ≠ 5) {Sg A : Subgroup Y} (hSg : IsPGroup s Sg)
    (hA : IsElemAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hAS : A ≤ Subgroup.normalizer (Sg : Set Y)) (Γ : Set Y)
    (hΓS : Γ ⊆ Subgroup.normalizer (Sg : Set Y)) (hΓA : Γ ⊆ Subgroup.normalizer (A : Set Y))
    (htrans : ∀ F F' : Subgroup Y, F ≤ A → F' ≤ A → Nat.card F = 5 → Nat.card F' = 5 →
      ∃ g ∈ Γ, F.map (MulAut.conj g).toMonoidHom = F')
    (hnt : ¬ A ≤ Subgroup.centralizer (Sg : Set Y)) : 4 ≤ Open.pRank s Sg := by
  have := Fact.mk hs
  have h5 : Nat.Prime 5 := by norm_num
  have := Fact.mk h5
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnt fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexp, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let _ : CommGroup A := @IsMulCommutative.instCommGroup _ _ hA.1
  let ψ : A →* MulAut D := φ.comp (Subgroup.inclusion hAS)
  have hcompat : ∀ (t : Y) (htS : t ∈ Subgroup.normalizer (Sg : Set Y))
      (htA : t ∈ Subgroup.normalizer (A : Set Y)) (a : A),
      φ ⟨t, htS⟩ * ψ a = ψ (A.normalizerMonoidHom ⟨t, htA⟩ a) * φ ⟨t, htS⟩ := fun t htS htA a => by
    change φ ⟨t, htS⟩ * φ (Subgroup.inclusion hAS a) =
      φ (Subgroup.inclusion hAS (A.normalizerMonoidHom ⟨t, htA⟩ a)) * φ ⟨t, htS⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change t * (a : Y) = t * a * t⁻¹ * t
    rw [inv_mul_cancel_right]
  have hA' : ∀ a : A, a ^ 5 = 1 := fun a => Subtype.ext (hA.2 a a.2)
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexp d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  have hψ : ∃ a : A, ψ a ≠ 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hxA, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnt
    apply hx
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨x, hAS hxA⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) (hall ⟨x, hxA⟩)
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ 5 = 1 := by
      have hn : (⟨x, hAS hxA⟩ : Subgroup.normalizer (Sg : Set Y)) ^ 5 = 1 :=
        Subtype.ext (hA.2 x hxA)
      change (Sg.normalizerMonoidHom ⟨x, hAS hxA⟩) ^ 5 = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h1 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs h5).mpr hs5)),
        pow_one] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = y := congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  set Γ' : Set (MulAut A × MulAut D) := {g | ∃ (t : Y) (htS : t ∈ Subgroup.normalizer
    (Sg : Set Y)) (htA : t ∈ Subgroup.normalizer (A : Set Y)), t ∈ Γ ∧
      g = (A.normalizerMonoidHom ⟨t, htA⟩, φ ⟨t, htS⟩)} with hΓ'
  have hΓ'c : ∀ g ∈ Γ', ∀ a, g.2 * ψ a = ψ (g.1 a) * g.2 := by
    rintro g ⟨t, htS, htA, -, rfl⟩ a
    exact hcompat t htS htA a
  have hcardA : ∀ F : Subgroup A, F.index = 5 → Nat.card (F.map A.subtype) = 5 := by
    intro F hF
    have h := F.card_mul_index
    rw [hF, hAcard] at h
    rw [card_map_of_injective A.subtype_injective]
    omega
  have htrans' : ∀ F F' : Subgroup A, F.index = 5 → F'.index = 5 →
      ∃ g ∈ Γ', F.map g.1.toMonoidHom = F' := by
    intro F F' hF hF'
    obtain ⟨t, ht, htF⟩ := htrans _ _ (map_subtype_le F) (map_subtype_le F') (hcardA F hF)
      (hcardA F' hF')
    exact ⟨_, ⟨t, hΓS ht, hΓA ht, ht, rfl⟩, map_normalizerMonoidHom_eq (hΓA ht) htF⟩
  obtain ⟨E, hEcomm, hEcard⟩ := exists_isMulCommutative_of_lineTransitive hs5 hA' hAcard hD hc
    ψ hψ Γ' hΓ'c htrans'
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨m, hm⟩ := hEp.exists_card_eq
  rw [hm] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hm (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end CFSG.AGLEmbedding
