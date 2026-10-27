module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactU33

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.LinearGroups.UnitaryThreeOverNine

theorem three_dvd_card_of_layerType {Y : Type} [Group Y] [Finite Y] (h : IsRankTwoLayerType Y) :
    3 ∣ Nat.card Y := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Fintype.card_perm]
    decide
  · obtain ⟨e⟩ := nonempty_equiv_gl32_of_model h
    rw [Nat.card_congr e.toEquiv, SylowL32.card_gl]
    norm_num
  · obtain ⟨F, hF, hF9, ⟨e⟩⟩ := exists_equiv_statedSU_of_model h
    rw [Nat.card_congr e.toEquiv, CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9]
    norm_num

theorem conj_mem_of_normal_subgroupOf {G : Type} [Group G] {M Y : Subgroup G} (hYM : Y ≤ M)
    (hn : (Y.subgroupOf M).Normal) {m : G} (hm : m ∈ M) {y : G} (hy : y ∈ Y) : m * y * m⁻¹ ∈ Y :=
  (Subgroup.mem_normalizer_iff.mp
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mp hn) hm) y).mp hy

theorem inf_le_core_of_psolvable {G : Type} [Group G] [Finite G] {M L C : Subgroup G}
    (hlay : IsRankTwoLayer M L) (hCM : C ≤ M) (hCn : (C.subgroupOf M).Normal)
    (h3 : CFSG.HallHigman.IsPSolvable 3 ↥C) :
    L ⊓ C ≤ GLBPrimeCore 3 M ∧
      ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ * l⁻¹ ∈ GLBPrimeCore 3 M := by
  obtain ⟨hLM, hDL, hLn, hS, hnc, hty⟩ := hlay
  set D : Subgroup G := GLBPrimeCore 3 M with hD
  haveI : (L.subgroupOf M).Normal := hLn
  haveI : (C.subgroupOf M).Normal := hCn
  set π := QuotientGroup.mk' (D.subgroupOf M) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set S := starImg M L with hSdef
  have hconjL : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := fun m hm l hl =>
    conj_mem_of_normal_subgroupOf hLM hLn hm hl
  have hconjC : ∀ m ∈ M, ∀ c ∈ C, m * c * m⁻¹ ∈ C := fun m hm c hc =>
    conj_mem_of_normal_subgroupOf hCM hCn hm hc
  have key : L ⊓ C ≤ D := by
    intro x hx
    have hxM : x ∈ M := hLM hx.1
    set N : Subgroup M := L.subgroupOf M ⊓ C.subgroupOf M with hN
    haveI : N.Normal := inferInstance
    set R : Subgroup (M ⧸ D.subgroupOf M) := N.map π with hR
    have hRS : R ≤ S := Subgroup.map_mono inf_le_left
    have hRn : (R.subgroupOf S).Normal := (Subgroup.Normal.map inferInstance π hπs).subgroupOf S
    have hxN : (⟨x, hxM⟩ : M) ∈ N := ⟨hx.1, hx.2⟩
    have := hS
    have := hRn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf S) with hbot | htop
    · have h1 : (⟨π ⟨x, hxM⟩, hRS (Subgroup.mem_map_of_mem π hxN)⟩ : S) ∈ R.subgroupOf S :=
        Subgroup.mem_map_of_mem π hxN
      rw [hbot, Subgroup.mem_bot] at h1
      have h2 : π ⟨x, hxM⟩ = 1 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff (N := D.subgroupOf M) (⟨x, hxM⟩ : M)).mp h2
    · exfalso
      set H : Subgroup C := (L ⊓ C).subgroupOf C with hH
      haveI hHn : H.Normal := by
        refine ⟨fun h hh c => ?_⟩
        have hh' : (h : G) ∈ L ⊓ C := hh
        refine ⟨hconjL c (hCM c.2) h hh'.1, C.mul_mem (C.mul_mem c.2 hh'.2) (C.inv_mem c.2)⟩
      let ι : ↥C →* ↥M := Subgroup.inclusion hCM
      have hφmem : ∀ y : ↥H, π (ι y.1) ∈ S := by
        intro y
        have hy : (y.1 : G) ∈ L ⊓ C := y.2
        exact ⟨ι y.1, hy.1, rfl⟩
      let φ : ↥H →* ↥S := ((π.comp ι).comp H.subtype).codRestrict S hφmem
      have hφ : Function.Surjective φ := by
        rintro ⟨s, hs⟩
        have hsR : s ∈ R := by
          have : (⟨s, hs⟩ : S) ∈ R.subgroupOf S := by rw [htop]; trivial
          exact this
        obtain ⟨y, hyN, hys⟩ := hsR
        have hyC : (y : G) ∈ C := hyN.2
        refine ⟨⟨⟨y, hyC⟩, ⟨hyN.1, hyC⟩⟩, Subtype.ext ?_⟩
        exact hys
      have hsimple : IsSimpleGroup (↥H ⧸ φ.ker) :=
        MulEquiv.isSimpleGroup (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
      have hidx : φ.ker.index = Nat.card S := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
      rcases h3 H (Subgroup.Normal.isSubnormal hHn) φ.ker hsimple with h | h
      · rw [hidx] at h
        have hc3 : Nat.card S = 3 := h
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsCyclic ↥S := isCyclic_of_prime_card hc3
        exact hnc ⟨⟨fun a b => (mul_comm a b)⟩⟩
      · rw [hidx] at h
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp h (three_dvd_card_of_layerType hty)
  refine ⟨key, fun c hc l hl => key ⟨?_, ?_⟩⟩
  · have := L.mul_mem (hconjL c (hCM hc) l hl) (L.inv_mem hl)
    exact this
  · have h1 := hconjC l (hLM hl) c⁻¹ (C.inv_mem hc)
    have := C.mul_mem hc h1
    simpa [mul_assoc] using this

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
