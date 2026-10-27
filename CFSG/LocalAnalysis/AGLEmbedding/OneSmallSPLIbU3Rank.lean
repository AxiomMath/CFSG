module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLIbU3Core
import CFSG.LocalAnalysis.AGLEmbeddingD2.OddCoreHeis

public section

namespace CFSG.AGLEmbedding

open CFSG
open scoped commutatorElement

theorem stmtFaithfulExtraspecialRank : StmtFaithfulExtraspecialRank := by
  intro Y _ _ s p hs hs2 hp hp5 hsp Sg X hSg hXS hXcard hXexp hnc
  have := Fact.mk hs
  have := Fact.mk hp
  have hSnt : Nontrivial Sg := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    rintro rfl
    refine hnc fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  obtain ⟨D, hDchar, -, hcl, hexpD, hfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hSg
  let φ : Subgroup.normalizer (Sg : Set Y) →* MulAut D :=
    (MulAut.characteristic D).comp Sg.normalizerMonoidHom
  let φX : X →* MulAut D := φ.comp (Subgroup.inclusion hXS)
  have hmapc : (commutator X).map X.subtype = ⁅X, X⁆ := by
    rw [map_commutator_eq, Subgroup.range_subtype]
  have hXnc : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    push Not at h
    apply hnc
    have hbot : ⁅X, X⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (h ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hbot]
    exact bot_le
  obtain ⟨hcomm, hZcard, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure (S := X) hXcard hXnc
  have hZc : Nat.card (commutator X) = p := by rw [hcomm]; exact hZcard
  have hφ : ∃ z ∈ commutator X, φX z ≠ 1 := by
    obtain ⟨x, hxXX, hx⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
    rw [← hmapc] at hxXX
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hxXX
    refine ⟨z, hz, fun h1 => hx ?_⟩
    let θ : MulAut Sg := Sg.normalizerMonoidHom ⟨(z : Y), hXS z.2⟩
    have hθfix : θ ∈ fixingSubgroup (MulAut Sg) (D : Set Sg) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      exact congrArg (fun f : MulAut D => ((f ⟨y, hy⟩ : D) : Sg)) h1
    obtain ⟨k, hk⟩ := hfix ⟨θ, hθfix⟩
    have hθk : θ ^ s ^ k = 1 := congrArg Subtype.val hk
    have hθp : θ ^ p = 1 := by
      have hn : (⟨(z : Y), hXS z.2⟩ : Subgroup.normalizer (Sg : Set Y)) ^ p = 1 :=
        Subtype.ext (hXexp z z.2)
      change (Sg.normalizerMonoidHom ⟨(z : Y), hXS z.2⟩) ^ p = 1
      rw [← map_pow, hn, map_one]
    have hθ : θ = 1 := by
      have h2 := pow_gcd_eq_one.mpr ⟨hθk, hθp⟩
      rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k ((Nat.coprime_primes hs hp).mpr hsp)),
        pow_one] at h2
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h3 : (z : Y) * y * (z : Y)⁻¹ = y :=
      congrArg (fun f : MulAut Sg => ((f ⟨y, hy⟩ : Sg) : Y)) hθ
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3.symm
  have hD : ∀ d : D, d ^ s = 1 := fun d => Subtype.ext (by simpa using hexpD d d.2)
  have hc : commutator D ≤ Subgroup.center D := by
    rw [_root_.commutator_def]
    refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
    refine Subgroup.mem_center_iff.mpr fun z => ?_
    have hmem : ⁅(x : Sg), (y : Sg)⁆ ∈ ⁅D, (⊤ : Subgroup Sg)⁆ :=
      Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top _)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcl hmem).2 (z : Sg) z.2)
  obtain ⟨E, hEcomm, hEcard⟩ :=
    CFSG.AGLEmbeddingD2.exists_isMulCommutative_pow_four_le_card_of_derived (R := X) hp5 hsp
      hZc rfl (fun r => Subtype.ext (hXexp r r.2)) hD hc φX hφ
  have hEp : IsPGroup s E := fun e => ⟨1, by rw [pow_one]; exact Subtype.ext (hD e)⟩
  obtain ⟨n, hn⟩ := hEp.exists_card_eq
  rw [hn] at hEcard
  refine ((Nat.pow_le_pow_iff_right hs.one_lt).mp hEcard).trans
    (CFSG.SectionRank.le_pRank_of_injective (A := E) hs.one_lt (fun a b => mul_comm' a b)
      (fun e => Subtype.ext (hD e)) hn (Sg.subtype.comp (D.subtype.comp E.subtype))
      (Sg.subtype_injective.comp (D.subtype_injective.comp E.subtype_injective)) ?_)
  rintro _ ⟨e, rfl⟩
  exact ((e : D) : Sg).2

end CFSG.AGLEmbedding
