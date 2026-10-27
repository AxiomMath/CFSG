module

public import CFSG.ClassicalInvolution.Q3.Q3T8B00

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight

section Alpha

variable {H : Type} [Group H]

theorem alphaCore_eq_bot_of_alphaOf_eq_bot {F : Subgroup H} (h : alphaOf F = ⊥) :
    Balance.Bootstrap.alphaCore F = ⊥ := by
  obtain ⟨h1, h2⟩ := (alphaOf_eq_bot_iff F).mp h
  have hU : Balance.Bootstrap.uCore F ≤ Subgroup.centralizer (F : Set H) := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h1 f hf hf1)
  have hc : ⁅Balance.Bootstrap.uCore F, F⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hU
  have hd : Balance.deltaCore F = ⊥ := h2
  refine le_bot_iff.mp (Balance.Bootstrap.alphaCore_le_of_normalized ?_ ?_)
  · rw [hc, hd]
    simp
  · intro u hu x hx
    have hx1 : x = 1 := by simpa using hx
    simp [hx1]

end Alpha

section Stand

variable {G : Type} [Group G] [Finite G]

theorem bridge_hypOmegaModU [IsSimpleGroup G] (hF : TwoElementsNormalizeU (.sl2 3 1))
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) :
    HypOmegaModU (.sl2 3 1) (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) := by
  have hm := hz.satU_member
  have hi := isIntrinsicU_satU (.sl2 3 1) K z
  exact hypOmegaModU_conjClass (MemberType.cert_sl2 3 1) hm hi
    (omega5At_of_twoElementsNormalize hm (hF G hnab _ z hm hi))

theorem aEmpty_of_noTwins {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) : ∀ M ∈ Ω, AEmpty Ω M := by
  intro M hM J hJs hJn zK zJ hzK hzJ
  by_contra hno
  have hA : InA Ω M J := ⟨hJs, hJn, zK, zJ, hzK, hzJ, hno⟩
  obtain ⟨-, -, -, -, Kstar, -, -, -, -, -, -, -, -, -, -, -, -, -, hne, htwin, -⟩ :=
    Sec6Gen.l6_4ThreeGen G Ω hΩ M hM J hJs.1 hA zK zJ hzK hzJ _ _ rfl rfl
  have hmem : Kstar ∈ twinSet Ω M := by
    rw [htwin]
    exact Or.inr rfl
  exact hne (hnt M hM Kstar hmem)

theorem bridge_ascStand3 [IsSimpleGroup G] (hF : TwoElementsNormalizeU (.sl2 3 1))
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n) (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (hz : IsClassicalMemberU (.sl2 3 1) K z)
    (hbelow : CITBelowT (.sl2 3 1) (Nat.card G))
    (hnt : ∀ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z),
      K' = satU (.sl2 3 1) K z) :
    Q3.Disc3.AscStand3 (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z) := by
  have hmod := bridge_hypOmegaModU hF hnab hz
  have hK := hz.satU_member
  have htrans : ∀ J ∈ CoreAssembly.conjClass (satU (.sl2 3 1) K z),
      ∃ g : G, conjSub g (satU (.sl2 3 1) K z) = J := fun J hJ => by
    obtain ⟨g, rfl⟩ := hJ
    exact ⟨g, rfl⟩
  exact
    { hyp := hmod
      below := hbelow
      ih := hih _ hbelow
      aEmpty := aEmpty_of_noTwins (hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hmod)
        (fun _ hM => Asc77.T8.noTwins_of_mem hmod.conjInvariant htrans hnt hM)
      mem := CoreAssembly.mem_conjClass_self _
      trans := htrans
      gen := gen_conjClass _ hK.mem hK.ne_one }

theorem _root_.CFSG.ClassicalInvolution.Q3.Disc3.AscStand3.rebase {Ω : Set (Subgroup G)}
    {K : Subgroup G} (h : Q3.Disc3.AscStand3 Ω K) {M : Subgroup G} (hM : M ∈ Ω) :
    Q3.Disc3.AscStand3 Ω M where
  hyp := h.hyp
  below := h.below
  ih := h.ih
  aEmpty := h.aEmpty
  mem := hM
  trans := fun J hJ => by
    obtain ⟨a, ha⟩ := h.trans J hJ
    obtain ⟨b, hb⟩ := h.trans M hM
    refine ⟨a * b⁻¹, ?_⟩
    rw [conjSub_mul, ← hb, conjSub_inv_conjSub, ha]
  gen := h.gen

theorem badStd8_of_edge [IsSimpleGroup G] {Ω : Set (Subgroup G)} {M N : Subgroup G} {a t : G}
    (hs : Q3T8.Asc77.AscStand Ω M) (hnt : ∀ K' ∈ twinSet Ω M, K' = M) (hconn : DConnected Ω)
    (ha : IsUniqueInvolution M a) (hN : N ∈ omegaNbr Ω M) (ht : IsUniqueInvolution N t)
    (hbad : alphaOf (Subgroup.closure ({t, a} : Set G)) ≠ ⊥) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G), Q3T8.Asc77.BadStd8 Ω M N S R T W a t := by
  obtain ⟨S, R, T, W, hstd⟩ := Q3T8.Asc77.c27_setupB hs hnt ha hN ht
  exact ⟨S, R, T, W, ⟨hstd, hconn, hbad⟩⟩

end Stand

end CFSG.ClassicalInvolution.Q3.Q3AM
