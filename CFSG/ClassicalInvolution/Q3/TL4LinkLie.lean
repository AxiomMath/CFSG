module

public import CFSG.ClassicalInvolution.Q3.TL4LinkLieDefs
public import CFSG.ClassicalInvolution.Q3.TL4LinkExit
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Nbr
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinIdentLie
public import CFSG.ClassicalInvolution.Uniform.U4Quot

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)

section Sylow

theorem isSylow2In_of_typeR_le {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) {K L : Subgroup X} (hK : K ∈ Φ) (hKL : K ≤ L) {z : X}
    (hL : IsClassicalMember3 L z) (h24 : Nat.card ↥L = 24) : IsSylow2In K L := by
  obtain ⟨P, hP⟩ := Sec7.exists_isSylow2In K
  obtain ⟨e⟩ := hΦ.quat K hK P hP
  have hP8 : Nat.card ↥P = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hK24 : Nat.card ↥K ∣ 24 := h24 ▸ Subgroup.card_dvd_of_le hKL
  have h8K : 8 ∣ Nat.card ↥K := hP8 ▸ Subgroup.card_dvd_of_le hP.1
  have hK8 : Nat.card ↥K = 8 := by
    obtain ⟨k, hk⟩ := h8K
    have hk3 : k ∣ 3 := by
      have : 8 * k ∣ 8 * 3 := by rw [← hk]; exact hK24
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp this
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with rfl | rfl
    · simpa using hk
    · exfalso
      have hKL' : K = L := Subgroup.eq_of_le_of_card_ge hKL (by rw [h24, hk])
      obtain ⟨e'⟩ := hL.nonempty_equiv
      have h2 := hΦ.twoGroup K hK
      rw [hKL'] at h2
      obtain ⟨m, hm⟩ := h2.exists_card_eq
      rw [Nat.card_congr e'.toEquiv, S1916.sl23_card] at hm
      have h3 : 3 ∣ 2 ^ m := hm ▸ (by norm_num : 3 ∣ 24)
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  have h2K : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by rw [hK8]; norm_num)
  refine ⟨hKL, h2K, fun V hVL hV2 hKV => ?_⟩
  obtain ⟨m, hm⟩ := hV2.exists_card_eq
  have hV24 : 2 ^ m ∣ 24 := hm ▸ h24 ▸ Subgroup.card_dvd_of_le hVL
  have hm3 : m ≤ 3 := by
    by_contra hgt
    have : 2 ^ 4 ∣ 24 := (Nat.pow_dvd_pow 2 (not_le.mp hgt)).trans hV24
    omega
  have hcard : Nat.card ↥V ≤ Nat.card ↥K := by
    rw [hm, hK8]
    calc 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
      _ = 8 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hKV hcard).symm

end Sylow

section Sl23

theorem lieKindSl23One_proved :
    ∀ (X : Type) [Group X] [Finite X] (Φ : Set (Subgroup X)), LieLinkSection Φ →
      SecIdQ8Shape CompData.sl23 Φ → ∀ L ∈ Φ, ∀ L' ∈ Φ, L = L' := by
  intro X _ _ Φ _ hsh L hL L' hL'
  obtain ⟨ψ, hψ, hker, hfund⟩ := hsh
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) := inferInstance
  have hle : ∀ V : Subgroup X, IsPGroup 2 V →
      V ≤ (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))).map ψ := by
    intro V hV x hx
    obtain ⟨k, hk⟩ := hV ⟨x, hx⟩
    have hx2 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨s, rfl⟩ := hψ x
    have hs : s ^ 2 ^ k ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :=
      hker (by rw [MonoidHom.mem_ker, map_pow, hx2])
    have h4 : s ^ 4 = 1 := by
      rcases Uniform.U4.sl23_center_cases _ fun y => (Subgroup.mem_center_iff.mp hs y).symm with
        h | h
      · exact S1916.sl23_pow_four_of_two_pow h
      · refine S1916.sl23_pow_four_of_two_pow (k := k + 1) ?_
        rw [pow_succ, pow_mul, h]
        decide
    exact ⟨s, S1916.mem_sylow_sl23 P h4, rfl⟩
  have hP2 : IsPGroup 2
      ((P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))).map ψ) := P.isPGroup'.map ψ
  have key : ∀ M ∈ Φ, M = (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))).map ψ := by
    intro M hM
    obtain ⟨F, hF, hMF⟩ := hfund M hM
    obtain rfl := Set.mem_singleton_iff.mp hF
    exact (hMF.2.2 _ (Subgroup.map_mono le_top) hP2 (hle M hMF.2.1)).symm
  rw [key L hL, key L' hL']

end Sl23

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem lieLinkSection_of (hL : TightLargeHypR 3 n Y R S t) (htr : LinkTrans R t) :
    LieLinkSection (linkFam R t) :=
  ⟨(typeRFam_coreLinkFam hL).restrict _, oddCore_linkGrp_eq_bot hL, omegaGen_linkRestrict, htr⟩

theorem exists_q8Shape_of_lie (hL : TightLargeHypR 3 n Y R S t)
    {R' : Subgroup ↥(linkGrp R t)} {t' : ↥(linkGrp R t)}
    (heq : CoreAssembly.conjClass (tightCore R') = linkFam R t) (hlie : SecIdLie3 R' t') :
    ∃ c : CompData, c.Valid ∧ SecIdQ8Shape c (linkFam R t) := by
  obtain ⟨L, hKL, hcl, -, hsys⟩ := hlie
  obtain ⟨ι, _, ⟨D⟩⟩ := lieSystem3_of_lieSystemMod3_corefree (oddCore_linkGrp_eq_bot hL) hsys
  have hnc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
    by_contra hcon
    refine hcl.false_of_commutative fun a b => Subtype.ext ?_
    by_contra hab
    exact hcon ⟨a, a.2, b, b.2, fun h => hab h⟩
  have hone := D.subsingleton_of_conjClass hnc
  obtain ⟨i₀, -⟩ := D.fundamental L (CoreAssembly.mem_conjClass_self L)
  have hsurj : Function.Surjective (D.hom i₀) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← D.generate]
    exact iSup_le fun i => by rw [hone i i₀]
  refine ⟨D.kind i₀, D.valid i₀, D.hom i₀, hsurj, D.ker_le_center i₀, ?_⟩
  intro K hK
  have hK' := hK
  rw [← heq] at hK'
  obtain ⟨g, rfl⟩ := hK'
  obtain ⟨i, F, hF, hFeq⟩ := D.fundamental (conjSub g L) ⟨g, rfl⟩
  obtain rfl := hone i i₀
  refine ⟨F, hF, ?_⟩
  rw [← hFeq]
  exact isSylow2In_of_typeR_le ((typeRFam_coreLinkFam hL).restrict _) hK (conjSub_mono hKL)
    (hcl.conj g) (D.card_eq _ ⟨g, rfl⟩)

theorem tightLinkLieR_of (hS : TightLinkStarEdgeR 3 n) (h2 : LieKindTwoNbrs)
    (hE : LieKindE4Edge) (hC : LieKindE4Cover) (hZ : LieKindZ2NoStar) :
    TightLinkLieR 3 n := by
  have h1 := lieKindSl23One_proved
  intro Y _ _ R S t hL hc hT hα htr hnc R' S' t' _ _ heq _ hlie
  have hsec := lieLinkSection_of hL htr
  obtain ⟨c, hcv, hsh⟩ := exists_q8Shape_of_lie hL heq hlie
  have hz2 : ∀ c : CompData, (c = CompData.model .PSL 3 ∨ c = CompData.m11) →
      SecIdQ8Shape c (linkFam R t) → False := by
    intro c hc' hsh'
    have hst := hZ _ _ c hc' hsec hsh'
    have hed : Disconnected.DEdgeless (linkFam R t) := by
      intro K hK J hJ hadj
      rcases hadj with h | h
      · have h' := Q3T6.Mu.omegaNbr_subset_omegaStarNbr hsec.1.hyp K h
        rw [hst K hK] at h'
        exact h'
      · have h' := Q3T6.Mu.omegaNbr_subset_omegaStarNbr hsec.1.hyp J h
        rw [hst J hJ] at h'
        exact h'
    obtain ⟨L, hLm, hne⟩ := hS Y R S t hL hc hT hα htr hnc hed
    rw [hst L hLm] at hne
    exact Set.not_nonempty_empty hne
  have he4 : ∀ c : CompData, (c = CompData.model .PSp 2 ∨ c = CompData.model .PSL 4) →
      SecIdQ8Shape c (linkFam R t) → LinkE4 R t := by
    intro c hc' hsh'
    obtain ⟨ψ, hψ, hker, hfund⟩ := hsh'
    refine ⟨htr, hE _ _ c hc' hsec ⟨ψ, hψ, hker, hfund⟩, ?_⟩
    rcases hc' with rfl | rfl
    · exact Or.inl ⟨ψ, hψ, hker, hC _ _ (Or.inl rfl) ψ hψ hker⟩
    · exact Or.inr ⟨ψ, hψ, hker, hC _ _ (Or.inr rfl) ψ hψ hker⟩
  rcases hcv with ⟨tg, m, hft, hadm, rfl⟩ | rfl | rfl
  · by_cases hnm : LieKindNamed tg m
    · rcases hnm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hz2 _ (Or.inl rfl) hsh).elim
      · exact Or.inl ⟨htr, hnc, Or.inl (Or.inl hsh)⟩
      · exact Or.inr (he4 _ (Or.inl rfl) hsh)
      · exact Or.inr (he4 _ (Or.inr rfl) hsh)
      · exact Or.inl ⟨htr, hnc, Or.inr (Or.inl (Or.inl hsh))⟩
      · exact Or.inl ⟨htr, hnc, Or.inr (Or.inl (Or.inr (Or.inl hsh)))⟩
      · exact Or.inl ⟨htr, hnc, Or.inr (Or.inl (Or.inr (Or.inr hsh)))⟩
      · exact Or.inl ⟨htr, hnc, Or.inl (Or.inr (Or.inl hsh))⟩
      · exact Or.inl ⟨htr, hnc, Or.inl (Or.inr (Or.inr hsh))⟩
    · obtain ⟨L, hLm, M, hM, M', hM', hne⟩ := h2 _ _ tg m hft hadm hnm hsec hsh
      exact (hne (LinkE2.subsingleton_omegaNbr_link hL hT htr L hLm M hM M' hM')).elim
  · refine (hnc fun K hK J hJ => ?_).elim
    obtain rfl := h1 _ _ hsec hsh K hK J hJ
    exact Relation.ReflTransGen.refl
  · exact (hz2 _ (Or.inr rfl) hsh).elim

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
