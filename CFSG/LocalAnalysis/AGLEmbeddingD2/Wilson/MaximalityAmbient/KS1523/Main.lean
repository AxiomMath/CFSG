module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.SCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.OuterE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.CoprimeS
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.J2
public import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofZDefs
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover Subgroup
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec14

theorem exists_iso_E0
    {H : Type} [Group H]
    {L E : Subgroup H} (hL : Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) (hEL : E ≤ L)
    (hE9 : Nat.card E = 9) :
    ∃ ε : ↥L ≃* GJ, (E.subgroupOf L).map ε.toMonoidHom = E0 := by
  obtain ⟨e⟩ := hL
  let ε₀ : ↥L ≃* GJ := e.trans nativeEquivP
  have hcard : Nat.card ((E.subgroupOf L).map ε₀.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, hE9]
  have hE0 : Nat.card E0 = 9 := by rw [card_E0]; norm_num
  have hGJ : Nonempty (GJ ≃* CFSG.Blueprint.NativeSporadic.J2) := ⟨nativeEquivP.symm⟩
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.j2_exists_conjugate_of_card_nine
    CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15 hGJ hcard hE0
  refine ⟨ε₀.trans (MulAut.conj g⁻¹), ?_⟩
  have e1 : (ε₀.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp ε₀.toMonoidHom := rfl
  rw [e1, ← Subgroup.map_map]
  exact hg.symm


theorem eq_one_of_commute_E
    {H : Type} [Group H]
    {L E S : Subgroup H} (ε : ↥L ≃* GJ) (hε : (E.subgroupOf L).map ε.toMonoidHom = E0)
    (hS2 : IsPGroup 2 S) (hSN : S ≤ normalizer (L : Set H))
    (hSC : S ⊓ centralizer (L : Set H) = ⊥) {s : H} (hs : s ∈ S)
    (hcomm : ∀ e ∈ E, s * e = e * s) : s = 1 := by
  have hsN : s ∈ normalizer (L : Set H) := hSN hs
  let a : normalizer (L : Set H) := ⟨s, hsN⟩
  let α : MulAut GJ := MulAut.congr ε (L.normalizerMonoidHom a)
  obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
  have hα : α ^ (2 ^ n) = 1 := by
    have h1 : a ^ (2 ^ n) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hn)
    show (MulAut.congr ε (L.normalizerMonoidHom a)) ^ (2 ^ n) = 1
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hfix : ∀ g ∈ E0, α g = g := by
    intro g hg
    rw [← hε] at hg
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.1 hg
    show MulAut.congr ε (L.normalizerMonoidHom a) (ε ℓ) = ε ℓ
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    show s * (ℓ : H) * s⁻¹ = ℓ
    have := hcomm ℓ (Subgroup.mem_subgroupOf.1 hℓ)
    rw [this]; group
  have h1 := eq_one_of_fixes_E0 α n hα hfix
  have h2 : L.normalizerMonoidHom a = 1 := by
    have : MulAut.congr ε (L.normalizerMonoidHom a) = MulAut.congr ε 1 := by
      rw [map_one]; exact h1
    exact (MulAut.congr ε).injective this
  have hsC : s ∈ centralizer (L : Set H) := by
    rw [mem_centralizer_iff]
    intro l hl
    have := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : H)) h2
    simp only [MulAut.one_apply] at this
    change s * l * s⁻¹ = l at this
    calc l * s = (s * l * s⁻¹) * s := by rw [this]
      _ = s * l := by group
  have : s ∈ S ⊓ centralizer (L : Set H) := ⟨hs, hsC⟩
  rw [hSC] at this
  exact Subgroup.mem_bot.1 this


theorem le_of_trivial_centralizer_E
    {H : Type} [Group H] [Finite H]
    {L E S : Subgroup H} (ε : ↥L ≃* GJ) (hε : (E.subgroupOf L).map ε.toMonoidHom = E0)
    (hEL : E ≤ L) (hE9 : Nat.card E = 9) (hS2 : IsPGroup 2 S)
    (hSN : S ≤ normalizer (L : Set H)) (hSC : S ⊓ centralizer (L : Set H) = ⊥)
    (hES : E ≤ normalizer (S : Set H)) : S ≤ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have h1 := le_sup_inf_centralizer_commutator S E hS2 hE3 hES
  have h2 : S ⊓ centralizer (E : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact Subgroup.mem_bot.2 (eq_one_of_commute_E ε hε hS2 hSN hSC hs.1
      (fun e he => (mem_centralizer_iff.1 hs.2 e he).symm))
  have h3 : ⁅S, E⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro s hs e he
    rw [commutatorElement_def]
    exact L.mul_mem ((mem_normalizer_iff.1 (hSN hs) e).1 (hEL he)) (L.inv_mem (hEL he))
  rw [h2, bot_sup_eq] at h1
  exact h1.trans h3

theorem centralizer_eq_of_three_central
    {z' : GJ} (hz'E : z' ∈ E0)
    (hz'1 : z' ≠ 1) (h27 : 27 ∣ Nat.card (centralizer ({z'} : Set GJ))) :
    centralizer ({z'} : Set GJ) = centralizer ({zJ} : Set GJ) := by
  have hz1 : zJ ≠ 1 := by rw [z_eq]; exact z_ne_one
  have hy3 : z' ^ 3 = 1 := cube_of_mem_P3 (E0_le_P3 hz'E)
  rcases E0_elt_pow hz'E hz'1 with ⟨n, hn⟩ | ⟨k, n, hn⟩
  · exact KF148Sig.centralizer_eq_of_pow hn hy3 hz1
  · exfalso
    have hle := KF148Sig.centralizer_le_of_pow hn
    have hd := h27.trans (Subgroup.card_dvd_of_le hle)
    rw [KF148Sig.card_centralizer_aJ k] at hd
    omega


theorem ks1523HJTwo_holds :
    KS1523HJTwo := by
  intro H _ _ L E S z hL hEL hE9 hzE hz1 hz3 hS2 hSN hSC hES
  obtain ⟨ε, hε⟩ := exists_iso_E0 hL hEL hE9
  have hSL : S ≤ L := le_of_trivial_centralizer_E ε hε hEL hE9 hS2 hSN hSC hES
  set S₀ : Subgroup ↥L := S.subgroupOf L with hS₀
  set S' : Subgroup GJ := S₀.map ε.toMonoidHom with hS'
  have hS'2 : IsPGroup 2 S' := by
    obtain ⟨m, hm⟩ := hS2.exists_card_eq
    refine IsPGroup.of_card (n := m) ?_
    rw [hS', Subgroup.card_map_of_injective ε.injective, hS₀,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv, hm]
  have hS'N : E0 ≤ normalizer (S' : Set GJ) := by
    rw [← hε, hS', ← Subgroup.map_equiv_normalizer_eq S₀ ε]
    rintro _ ⟨b, hb, hbe⟩
    refine ⟨b, ?_, hbe⟩
    have hbE : (b : H) ∈ E := Subgroup.mem_subgroupOf.1 hb
    show b ∈ (normalizer ((S₀ : Subgroup ↥L) : Set ↥L) : Subgroup ↥L)
    rw [mem_normalizer_iff]
    intro x
    have := mem_normalizer_iff.1 (hES hbE) (x : H)
    rw [hS₀, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact this
  obtain ⟨hzL, P', hzP', hP'C⟩ := hz3
  set zL : ↥L := ⟨z, hzL⟩ with hzLdef
  have hzE' : zL ∈ E.subgroupOf L := Subgroup.mem_subgroupOf.2 hzE
  have hz'E : ε zL ∈ E0 := by
    rw [← hε]
    exact Subgroup.mem_map.2 ⟨zL, hzE', rfl⟩
  have hz'1 : ε zL ≠ 1 := fun h => hz1 (by
    have := ε.injective (h.trans (map_one ε).symm)
    exact congrArg Subtype.val this)
  have h27 : 27 ∣ Nat.card (centralizer ({ε zL} : Set GJ)) := by
    have hcardL : Nat.card ↥L = 604800 :=
      CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hL
    have hP'card : Nat.card (P' : Subgroup ↥L) = 27 := by
      rw [Sylow.card_eq_multiplicity, hcardL]
      have : (604800 : ℕ).factorization 3 = 3 := by
        rw [Nat.factorization_def _ Nat.prime_three]
        decide +kernel
      rw [this]; norm_num
    have := Subgroup.card_dvd_of_le hP'C
    rw [hP'card, ← KF148Sig.card_centralizer_singleton_mulEquiv ε zL] at this
    exact this
  have hCeq := centralizer_eq_of_three_central hz'E hz'1 h27
  intro g hg
  rw [mem_centralizer_iff]
  intro h hh
  have hgL : g ∈ L := hSL hg.1
  have hhL : h ∈ L := hSL hh
  set gL : ↥L := ⟨g, hgL⟩
  set hL' : ↥L := ⟨h, hhL⟩
  have hgS : ε gL ∈ S' := Subgroup.mem_map.2 ⟨gL, Subgroup.mem_subgroupOf.2 hg.1, rfl⟩
  have hhS : ε hL' ∈ S' := Subgroup.mem_map.2 ⟨hL', Subgroup.mem_subgroupOf.2 hh, rfl⟩
  have hgC : ε gL ∈ centralizer ({zJ} : Set GJ) := by
    rw [← hCeq, mem_centralizer_singleton_iff]
    have hgz := mem_centralizer_singleton_iff.1 hg.2
    have : gL * zL = zL * gL := Subtype.ext hgz
    rw [← map_mul, ← map_mul, this]
  have hcent := inf_centralizer_z_le_centralizer hS'2 hS'N ⟨hgS, hgC⟩
  have := mem_centralizer_iff.1 hcent (ε hL') hhS
  have h2 : hL' * gL = gL * hL' := ε.injective (by rw [map_mul, map_mul]; exact this)
  exact congrArg Subtype.val h2

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
