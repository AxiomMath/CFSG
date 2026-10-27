module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6M10

public section

namespace CFSG.QuasithinUnique

namespace Unc25G2

theorem sharp4_m11 : Sharp4 ↥CFSG.Blueprint.NativeSporadic.M11 where
  card_eq := CFSG.Semidihedral.GL2Recognition.card_nativeM11
  fix_eq_one g _ _ _ _ hab hac had hbc hbd hcd ha hb hc hd :=
    m11_fix_eq_one g hab hac had hbc hbd hcd ha hb hc hd
  trans x y := m11_trans x y

section Transport

theorem core_of_equiv
    {H : Type*} [Group H] (e : H ≃* ↥CFSG.Blueprint.NativeSporadic.M11)
    {B₁ Q₁ : Subgroup H} [IsSimpleGroup ↥B₁] (hB : Nat.card ↥B₁ = 360)
    (hQ : Nat.card ↥Q₁ = 16) (hQN : Q₁ ≤ Subgroup.normalizer (B₁ : Set H)) :
    Subgroup.normalizer (B₁ : Set H) = B₁ ⊔ Q₁ ∧ Subgroup.centralizer (B₁ : Set H) = ⊥ ∧
      Nonempty (↥(Subgroup.normalizer (B₁ : Set H)) ≃* ↥A6Models.m10) := by
  have hB' : Nat.card ↥(B₁.map e.toMonoidHom) = 360 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hB
  have hQ' : Nat.card ↥(Q₁.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hQ
  have hs : IsSimpleGroup ↥(B₁.map e.toMonoidHom) := (e.subgroupMap B₁).symm.isSimpleGroup
  have hNmap : (Subgroup.normalizer (B₁ : Set H)).map e.toMonoidHom =
      Subgroup.normalizer ((B₁.map e.toMonoidHom : Subgroup _) : Set _) :=
    Subgroup.map_equiv_normalizer_eq B₁ e
  have hQN' : Q₁.map e.toMonoidHom ≤
      Subgroup.normalizer ((B₁.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [← hNmap]
    exact Subgroup.map_mono hQN
  obtain ⟨x, hxN, hxS, hxC⟩ := sharp4_m11.a6_core hB' hQ' hQN'
  refine ⟨?_, ?_, ?_⟩
  · apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [hNmap, hxS, Subgroup.map_sup]
  · rw [eq_bot_iff]
    intro c hc
    rw [Subgroup.mem_bot]
    have hec : e c ∈ Subgroup.centralizer ((B₁.map e.toMonoidHom : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hc b hb
      have h2 := congrArg e h1
      rw [map_mul, map_mul] at h2
      exact h2
    rw [hxC, Subgroup.mem_bot] at hec
    exact e.injective (by rw [hec, map_one])
  · obtain ⟨f⟩ := nonempty_stabilizer_equiv_m10 x
    exact ⟨(e.subgroupMap (Subgroup.normalizer (B₁ : Set H))).trans
      ((MulEquiv.subgroupCongr (hNmap.trans hxN)).trans f)⟩

variable {G : Type*} [Group G]

theorem subgroupOf_normalizer {L B : Subgroup G} (hBL : B ≤ L) :
    (L ⊓ Subgroup.normalizer (B : Set G)).subgroupOf L =
      Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext ⟨l, hl⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, hn⟩ ⟨h, hh⟩
    have h1 := Subgroup.mem_normalizer_iff.mp hn h
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv] using h1
  · intro hn
    refine ⟨hl, Subgroup.mem_normalizer_iff.mpr fun g => ?_⟩
    constructor
    · intro hg
      have h1 := (hn ⟨g, hBL hg⟩).mp (by simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf] using hg)
      simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_inv] using h1
    · intro hg
      have hgL : g ∈ L := by
        have h2 : l⁻¹ * (l * g * l⁻¹) * l ∈ L :=
          L.mul_mem (L.mul_mem (L.inv_mem hl) (hBL hg)) hl
        have h3 : l⁻¹ * (l * g * l⁻¹) * l = g := by group
        rwa [h3] at h2
      have h1 := (hn ⟨g, hgL⟩).mpr (by simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf,
        Subgroup.coe_mul, Subgroup.coe_inv] using hg)
      simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf] using h1

theorem subgroupOf_centralizer {L B : Subgroup G} (hBL : B ≤ L) :
    (L ⊓ Subgroup.centralizer (B : Set G)).subgroupOf L =
      Subgroup.centralizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext ⟨l, hl⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hc⟩ ⟨h, hh⟩ hhB
    have h1 := Subgroup.mem_centralizer_iff.mp hc h hhB
    exact Subtype.ext h1
  · intro hc
    refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 := hc ⟨g, hBL hg⟩ (by simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf] using hg)
    exact congrArg Subtype.val h1

theorem card_eq_sixteen_of_sylow {L Q : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hL : Nat.card ↥L = 7920) : Nat.card ↥Q = 16 := by
  obtain ⟨hQL, hp, hodd⟩ := hQ
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hL]; norm_num)
  have : Finite ↥Q := Finite.of_injective (Subgroup.inclusion hQL)
    (Subgroup.inclusion_injective hQL)
  have h1 := Subgroup.card_mul_index (Q.subgroupOf L)
  have hc : Nat.card ↥(Q.subgroupOf L) = Nat.card ↥Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
  rw [hc, hL] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  rw [hn] at h1 ⊢
  have hn12 : n ≤ 12 := by
    by_contra hcon
    have h13 : 2 ^ 13 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ n ≤ 7920 := by
      have := Nat.le_of_dvd (by norm_num) (Dvd.intro _ h1)
      exact this
    omega
  interval_cases n <;> omega

end Transport

end Unc25G2

theorem m11A6Normalizer : M11A6Normalizer := by
  intro G _ _ L B Q ⟨e⟩ ⟨eB⟩ hBL hQ hQN
  have hQL : Q ≤ L := hQ.1
  have hcardL : Nat.card ↥L = 7920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Semidihedral.GL2Recognition.card_nativeM11
  have hQc : Nat.card ↥Q = 16 := Unc25G2.card_eq_sixteen_of_sylow hQ hcardL
  let eB₁ : ↥(B.subgroupOf L) ≃* alternatingGroup (Fin 6) :=
    (Subgroup.subgroupOfEquivOfLe hBL).trans eB
  have hA6 : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup ↥(B.subgroupOf L) :=
    eB₁.isSimpleGroup (H := alternatingGroup (Fin 6))
  have hB₁c : Nat.card ↥(B.subgroupOf L) = 360 :=
    (Nat.card_congr eB₁.toEquiv).trans Unc25G2.card_alternatingGroup_six
  have hQ₁c : Nat.card ↥(Q.subgroupOf L) = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv).trans hQc
  have hN := Unc25G2.subgroupOf_normalizer hBL
  have hC := Unc25G2.subgroupOf_centralizer hBL
  have hQN₁ : Q.subgroupOf L ≤ Subgroup.normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro q hq
    rw [← hN]
    exact ⟨q.2, hQN hq⟩
  obtain ⟨h1, h2, ⟨h3⟩⟩ := Unc25G2.core_of_equiv e hB₁c hQ₁c hQN₁
  refine ⟨?_, ?_, ?_⟩
  · have hmap : (L ⊓ Subgroup.normalizer (B : Set G)) =
        ((B.subgroupOf L) ⊔ (Q.subgroupOf L)).map L.subtype := by
      rw [← h1, ← hN, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rw [hmap, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hBL,
      Subgroup.map_subgroupOf_eq_of_le hQL]
  · have hmap : (L ⊓ Subgroup.centralizer (B : Set G)) =
        (⊥ : Subgroup ↥L).map L.subtype := by
      rw [← h2, ← hC, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
    rw [hmap, Subgroup.map_bot]
  · refine ⟨((Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ Subgroup.normalizer (B : Set G) ≤ L)).symm.trans
      ((MulEquiv.subgroupCongr hN).trans h3))⟩

end CFSG.QuasithinUnique
