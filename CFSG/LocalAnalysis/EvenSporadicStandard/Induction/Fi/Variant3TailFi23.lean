module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3CoexistClose
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.RowB
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Even
public import CFSG.Sporadic.Fi23.StarKernel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Fi23 CFSG.Blueprint.Fischer

theorem eq_or_eq_top_of_isCoatom_map {G Y : Type} [Group G] [Group Y] (ψ : G ≃* Y)
    {A : Subgroup G} {B : Subgroup Y} (hB : IsCoatom B) (hAB : A.map ψ.toMonoidHom = B)
    {M : Subgroup G} (hAM : A ≤ M) : M = A ∨ M = ⊤ := by
  have hle : A.map ψ.toMonoidHom ≤ M.map ψ.toMonoidHom := Subgroup.map_mono hAM
  rw [hAB] at hle
  rcases hB.le_iff.1 hle with h | h
  · right
    rw [eq_top_iff]
    intro g _
    have hg : ψ g ∈ M.map ψ.toMonoidHom := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hg
    exact (ψ.injective hmg) ▸ hm
  · exact Or.inl (Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (h.trans hAB.symm))

section CertificatesStar


theorem star_nonempty {s : J} (hs : s ∈ D23) : ∃ x, x ∈ LocalClass D23 s := by
  by_contra hne
  have hsub : Subgroup.centralizer ({s} : Set J) ≤ Subgroup.zpowers s := by
    intro g hg
    have hgs := Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases eq_of_centralizes_star hs hgs (fun x hx => absurd ⟨x, hx⟩ hne) with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers s
  obtain ⟨c, hc⟩ := isConj_iff.1 hs
  have hss : s ^ 2 = 1 := by
    rw [← hc, pow_two]
    calc c * d * c⁻¹ * (c * d * c⁻¹) = c * (d * d) * c⁻¹ := by group
      _ = 1 := by rw [d_sq]; group
  have hord : orderOf s ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hss)
  have h1 := Subgroup.card_le_of_le hsub
  rw [Nat.card_zpowers, card_centralizer_of_mem hs] at h1
  omega

end CertificatesStar

section CertificatesCover


theorem fi23_cover_facts {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    K = L ⊓ Subgroup.centralizer ({u} : Set H) ∧
      (∀ M : Subgroup H, K ≤ M → M ≤ L → M = K ∨ M = L) ∧
      ∃ l ∈ L, l * u * l⁻¹ ∈ K ∧ l * u * l⁻¹ ≠ u := by
  obtain ⟨e⟩ := hL
  obtain ⟨ψ⟩ : Nonempty (↥L ≃* J) := ⟨e.trans fi23EquivJ⟩
  have hT := fi23Transposition_of_fiLoc ⟨e⟩ hQ
  obtain ⟨huL, hu2, hKL, hKu, -, hcard⟩ := hQ
  have hX : K ≤ L ⊓ Subgroup.centralizer ({u} : Set H) := fun k hk =>
    ⟨hKL hk, Subgroup.mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hKcard : 129123503308800 ≤ Nat.card ↥K := by
    have h1 : Nat.card (↥K ⧸ CFSG.oddCore ↥K) ≤ Nat.card ↥K :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    omega
  have hKeq : K = L ⊓ Subgroup.centralizer ({u} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hX (by rw [hT.2.2]; exact hKcard)
  have hs2 : orderOf (ψ ⟨u, huL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hu2]
  have hcardJ : Nat.card ↥(Subgroup.centralizer ({ψ ⟨u, huL⟩} : Set J)) = 129123503308800 := by
    rw [← @fi23_card_inf_centralizer_eq H J _ (inferInstance) L ψ u huL]
    exact hT.2.2
  have hsD : ψ ⟨u, huL⟩ ∈ D23 := fi23J_isConj_d_of_card hs2 hcardJ
  have hKL' : K.subgroupOf L = Subgroup.centralizer ({(⟨u, huL⟩ : ↥L)} : Set ↥L) := by
    ext x
    rw [hKeq, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  refine ⟨hKeq, ?_, ?_⟩
  · intro M hKM hML
    have hA := @Hyp.map_centralizer_singleton ↥L J _ (inferInstance) ψ (⟨u, huL⟩ : ↥L)
    rw [← hKL'] at hA
    have hco := isCoatom_centralizer_of_mem hsD
    rcases @eq_or_eq_top_of_isCoatom_map ↥L J _ (inferInstance) ψ (K.subgroupOf L) _ hco hA
      (M.subgroupOf L) (fun x hx => hKM hx) with h | h
    · left
      have := congrArg (Subgroup.map L.subtype) h
      rwa [Subgroup.map_subgroupOf_eq_of_le hML, Subgroup.map_subgroupOf_eq_of_le hKL] at this
    · right
      exact le_antisymm hML (Subgroup.subgroupOf_eq_top.1 h)
  · obtain ⟨x, hxD, hxne, hxc⟩ := star_nonempty hsD
    obtain ⟨c, hc⟩ := isConj_iff.1 (IsConj.trans (isConj_comm.1 hsD) hxD)
    have hyx : ψ.symm x = ψ.symm c * (⟨u, huL⟩ : ↥L) * (ψ.symm c)⁻¹ := by
      rw [← hc, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    have hy : ((ψ.symm c : ↥L) : H) * u * ((ψ.symm c : ↥L) : H)⁻¹ = ((ψ.symm x : ↥L) : H) := by
      rw [hyx]; rfl
    refine ⟨((ψ.symm c : ↥L) : H), (ψ.symm c).2, ?_, ?_⟩
    · rw [hy, hKeq]
      refine ⟨(ψ.symm x).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 : ψ.symm x * (⟨u, huL⟩ : ↥L) = (⟨u, huL⟩ : ↥L) * ψ.symm x := by
        have h2 := congrArg ψ.symm hxc
        rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
      exact congrArg Subtype.val h1
    · rw [hy]
      intro h
      apply hxne
      have h3 : ψ.symm x = ⟨u, huL⟩ := Subtype.ext h
      exact ψ.symm_apply_eq.1 h3

end CertificatesCover

section CertificatesCenter


theorem fi23_center_facts {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (hL : IsSporadic ↥L .Fi23) (hQ : fiLoc (2 * 64561751654400) H L K u) :
    ∀ l ∈ L, (∀ k ∈ K, l * k = k * l) → l = 1 ∨ l = u := by
  obtain ⟨f⟩ := fi23_pair_equiv hL hQ
  have hKeq := (fi23_cover_facts hL hQ).1
  obtain ⟨huL, hu2, hKL, hKu, -, -⟩ := hQ
  have hcenter : Nat.card (center ↥K) = 2 := by
    rw [card_center_congr f]
    exact fi23D_card_center
  have huK : u ∈ K := by
    rw [hKeq]
    exact ⟨huL, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hord : orderOf (⟨u, huK⟩ : ↥K) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hle : Subgroup.zpowers (⟨u, huK⟩ : ↥K) ≤ center ↥K := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hKu k k.2)
  have hZ : Subgroup.zpowers (⟨u, huK⟩ : ↥K) = center ↥K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hord, hcenter])
  intro l hl hcomm
  have hlC : l ∈ Subgroup.centralizer ({u} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm u huK)
  have hlK : l ∈ K := by
    rw [hKeq]
    exact ⟨hl, hlC⟩
  have hlZ : (⟨l, hlK⟩ : ↥K) ∈ Subgroup.zpowers (⟨u, huK⟩ : ↥K) := by
    rw [hZ, Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hcomm k k.2).symm
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hlZ
  have hln : l = u ^ n := by
    have := congrArg Subtype.val hn
    simpa using this.symm
  rw [hln]
  exact Solomon78.zpow_eq_one_or_self_of_orderOf_eq_two hu2 n

end CertificatesCenter

end CFSG.EvenSporadicStandard.Induction.Fi.V3
