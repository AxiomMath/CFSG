module

public import CFSG.CGT.PushingUpLit.T2KHall.Weak
public import CFSG.CGT.PushingUpLit.T2K.FourFourB
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Assembly CFSG.CGT.PushingUpLit.BHS
open CFSG.EvenSporadicStandard.Finkelstein77 (Asc76Lemma25)

namespace T2Hyp

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {s : G}
variable (h : T2Hyp G L M n) (hE1 : FooteNonsolvableSimple) (hs : orderOf s = 4)
  (hX : Subgroup.centralizer (L : Set G) = Subgroup.zpowers s)
include h hE1 hs hX

theorem z4_not_weaklyClosed_of_weak (hE9 : HallWeaklyClosedFourWeak)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hwc : ∀ g : G, (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤ T →
      (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer (L : Set G)) : False := by
  have hXT := h.z4_le_sylow hE1 hs hX hT
  have hXcard : Nat.card ↥(Subgroup.centralizer (L : Set G)) = 4 := by
    rw [hX]
    simp only [Nat.card_zpowers]
    exact hs
  have hXeven : Even (Nat.card ↥(Subgroup.centralizer (L : Set G))) := by
    rw [hXcard]
    exact ⟨2, rfl⟩
  have hNX := h.normalizer_centralizer_eq hE1 hXeven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := hT.isPGroup.exists_le_sylow
  have hTQeq : T = (Q : Subgroup G) := by
    by_contra hne
    have hlt : T.subgroupOf (Q : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
      intro hQT
      exact hne (le_antisymm hTQ hQT)
    have hnil : Group.IsNilpotent ↥(Q : Subgroup G) := Q.isPGroup'.isNilpotent
    obtain ⟨⟨n, hnQ⟩, hnN, hnT⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥(Q : Subgroup G)) _ hlt)
    have hnT' : n ∉ T := fun hn => hnT hn
    have hnormT : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
      intro t ht
      exact (Subgroup.mem_normalizer_iff.1 hnN ⟨t, hTQ ht⟩).1 ht
    have hXn : (Subgroup.centralizer (L : Set G)).map (MulAut.conj n).toMonoidHom ≤ T := by
      rintro _ ⟨x, hx, rfl⟩
      exact hnormT x (hXT hx)
    have hnX := hwc n hXn
    have hnM : n ∈ M := by
      rw [← hNX, Subgroup.mem_normalizer_iff]
      intro y
      have h1 := mem_map_conj_iff n (Subgroup.centralizer (L : Set G)) (n * y * n⁻¹)
      rw [hnX] at h1
      have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
      rw [e] at h1
      exact h1.symm
    have hP'Q : T ⊔ Subgroup.zpowers n ≤ (Q : Subgroup G) :=
      sup_le hTQ ((Subgroup.zpowers_le).2 hnQ)
    have hP'M : T ⊔ Subgroup.zpowers n ≤ M :=
      sup_le hT.le ((Subgroup.zpowers_le).2 hnM)
    have heq := hT.eq_of_le le_sup_left hP'M (Q.isPGroup'.to_le hP'Q)
    exact hnT' (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hTG : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := by
    refine (CFSG.ABGLocalTools.isSylowOf_iff).2 ⟨le_top, hT.isPGroup, ?_⟩
    rw [Subgroup.relIndex_top_right, hTQeq]
    exact Q.not_dvd_index
  have hXT' : Subgroup.zpowers s ≤ T := by
    rw [← hX]
    exact hXT
  have hwc' : ∀ g : G, (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom ≤ T →
      (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers s := by
    rw [← hX]
    exact hwc
  have hVT : blockU L ≤ T := NatBlock.blockU_le_sylow h.le (h.normal hE1) hT
  have h16 : 16 ≤ Nat.card ↥(blockU L) := by
    rw [h.natBlock.card_blockU]
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    have hZ : 1 ≤ Nat.card ↥(blockZ L) := Nat.card_pos
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      _ = (2 ^ n) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (2 ^ n) ^ 2 * Nat.card ↥(blockZ L) := Nat.mul_le_mul_left _ hZ
  have hsq : ∀ x : ↥T, x ∈ (blockU L).subgroupOf T → x ^ 2 = 1 := fun x hx =>
    Subtype.ext (h.natBlock.sq_eq_one_of_mem_blockU hx)
  rcases hE9 G h.kproper h.simple T s hTG hs ⟨hXT', hwc'⟩ with ⟨m, hm, ⟨ε⟩⟩ | ⟨k, hk, ⟨ε⟩⟩
  · let W : Subgroup (DihedralGroup (2 ^ m)) := ((blockU L).subgroupOf T).map ε.toMonoidHom
    have hW : ∀ w ∈ W, w ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hsq x hx, map_one]
    have hcard := CFSG.QuasithinUnique.dihedral_card_le_four hm W hW
    have hcardW : Nat.card W = Nat.card ↥(blockU L) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ ε.injective).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv
    omega
  · let W : Subgroup (SemidihedralGroup k) := ((blockU L).subgroupOf T).map ε.toMonoidHom
    have hW : ∀ w ∈ W, w ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hsq x hx, map_one]
    have hcard := CFSG.ABGDGroups.semidihedral_card_le_four hk W hW
    have hcardW : Nat.card W = Nat.card ↥(blockU L) := by
      rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ ε.injective).toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv
    omega

theorem z4_not_weaklyClosed_of_lemma25 (h25 : Asc76Lemma25)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hwc : ∀ g : G, (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ≤ T →
      (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer (L : Set G)) : False :=
  h.z4_not_weaklyClosed_of_weak hE1 hs hX (hallWeaklyClosedFour_of_lemma25 h25) hT hwc

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
