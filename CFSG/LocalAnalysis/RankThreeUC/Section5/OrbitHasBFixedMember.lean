module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitBStable
public import CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitHasBFixedMember

open CFSG.LocalAnalysis.RankThreeUC.Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_member {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) {D : Subgroup G} (hD : D ∈ Delta p P ρ) :
    ∃ s ∈ twoCoreCommutator T B, ∀ b ∈ B,
      b ∈ Subgroup.normalizer ((D.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  classical
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  letI : MulAction G (Delta p P ρ) :=
    MulAction.compHom _ (DeltaConjugationAction.act (p := p) hP ρ)
  have hsmul : ∀ (g : G) (i : Delta p P ρ), ((g • i : Delta p P ρ) : Subgroup G) =
      i.1.map (MulAut.conj g).toMonoidHom := fun g i => rfl
  have hstable := OrbitBStable.stable hc hD
  set S : Subgroup G := twoCoreCommutator T B with hSdef
  have hS2 : IsPGroup 2 S := by
    have hK : IsPGroup 2 (CFSG.Open.pCoreOf 2 (B ⊔ T)) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2).map (B ⊔ T).subtype
    exact hK.to_le (SstarQuotientFaithful.Xs_le_pCoreOf T B le_sup_left)
  have hBnorm : B ≤ Subgroup.normalizer (S : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_left.mpr
    exact (CoprimeStarSubgroupStructure.Xs_generated hc.oddPrimeClassTwoAction).le
  let i : Delta p P ρ := ⟨D, hD⟩
  have hB : ∀ b ∈ B, ∀ s ∈ S, ∃ t ∈ S, b • (s • i) = t • i := by
    intro b hb s hs
    obtain ⟨t, ht, h⟩ := hstable b hb s hs
    exact ⟨t, ht, Subtype.ext (by rw [hsmul, hsmul, hsmul]; exact h)⟩
  set H : Subgroup G := B ⊔ S with hH
  let O : Set (Delta p P ρ) := {x | ∃ s ∈ S, x = s • i}
  have hOB : ∀ b ∈ B, b • O = O := by
    intro b hb
    have hsub : b • O ⊆ O := by
      rintro _ ⟨x, ⟨s, hs, rfl⟩, rfl⟩
      obtain ⟨t, ht, e⟩ := hB b hb s hs
      exact ⟨t, ht, e⟩
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Set.image_smul, Set.ncard_image_of_injective _ (MulAction.injective b)]
  have hOS : ∀ s ∈ S, s • O = O := by
    intro s hs
    ext x
    constructor
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨s * t, S.mul_mem hs ht, by rw [mul_smul]⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(s⁻¹ * t) • i, ⟨s⁻¹ * t, S.mul_mem (S.inv_mem hs) ht, rfl⟩, ?_⟩
      show s • ((s⁻¹ * t) • i) = _
      rw [← mul_smul]; simp
  have hHle : H ≤ MulAction.stabilizer G O := by
    refine sup_le (fun b hb => ?_) (fun s hs => ?_)
    · exact hOB b hb
    · exact hOS s hs
  have hHS : ∀ h ∈ H, ∀ s ∈ S, ∃ t ∈ S, h • (s • i) = t • i := by
    intro h hh s hs
    have : h • (s • i) ∈ h • O := Set.smul_mem_smul_set ⟨s, hs, rfl⟩
    have h2 : h • O = O := hHle hh
    rw [h2] at this
    obtain ⟨t, ht, e⟩ := this
    exact ⟨t, ht, e⟩
  have hX : ∀ h ∈ H, ∃ s ∈ S, h • i = s • i := by
    intro h hh
    obtain ⟨t, ht, e⟩ := hHS h hh 1 S.one_mem
    exact ⟨t, ht, by simpa using e⟩
  let X : SubMulAction H (Delta p P ρ) :=
    { carrier := O
      smul_mem' := by
        intro h x hx
        have h2 : (h : G) • O = O := hHle h.2
        rw [← h2]
        exact Set.smul_mem_smul_set hx }
  haveI : Nonempty X := ⟨⟨i, 1, S.one_mem, by simp⟩⟩
  haveI hN : (S.subgroupOf H).Normal := by
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hBnorm
    exact this
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS2.comap_subtype
  have hB' : Odd (Nat.card (B.subgroupOf H)) := by
    have : Nat.card (B.subgroupOf H) = Nat.card B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [this]; exact hc.oddPrimeClassTwoAction.setting.oddOrder
  have hSB : S.subgroupOf H ⊔ B.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left, Subgroup.map_top, Subgroup.range_subtype,
      sup_comm]
  have htrans : ∀ x y : X, ∃ s : S.subgroupOf H, (s.val : H) • x = y := by
    have key : ∀ x : X, ∃ s ∈ S, x.1 = s • i := fun x => x.2
    intro x y
    obtain ⟨s1, hs1, hx⟩ := key x
    obtain ⟨s2, hs2, hy⟩ := key y
    refine ⟨⟨⟨s2 * s1⁻¹, le_sup_right (b := S) |> fun h => h (S.mul_mem hs2 (S.inv_mem hs1))⟩,
      S.mul_mem hs2 (S.inv_mem hs1)⟩, ?_⟩
    apply Subtype.ext
    show (s2 * s1⁻¹) • x.1 = y.1
    rw [hx, hy, ← mul_smul]; simp
  obtain ⟨x, hx⟩ := CFSG.GroupTheory.CoprimeActionSupport.OddComplementFixedPoints.exists_fixed (S.subgroupOf H) (B.subgroupOf H) hS' hB' hSB X htrans
  obtain ⟨s, hs, hxs⟩ : ∃ s ∈ S, x.1 = s • i := x.2
  refine ⟨s, hs, fun b hb => ?_⟩
  have hbx := hx ⟨⟨b, le_sup_left (b := S) hb⟩, hb⟩
  have h1 : (b • x.1 : Delta p P ρ) = x.1 := congrArg Subtype.val hbx
  rw [hxs] at h1
  have h2 := congrArg Subtype.val h1
  rw [hsmul, hsmul] at h2
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact h2

end CFSG.LocalAnalysis.RankThreeUC.Section5.OrbitHasBFixedMember
