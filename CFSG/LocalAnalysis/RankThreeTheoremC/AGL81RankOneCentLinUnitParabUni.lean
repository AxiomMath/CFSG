module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniMap
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedASetup
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab

open CFSG.AGLEmbedding CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Cover


theorem exists_hypCover_three {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥L)))
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq : q.p = 2)
    (hd : d.1 = .twistedA 2 q)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (K : Type) (_ : Field K) (f : ℕ) (h : UnitaryFieldData 2 f K) (ρ : hypSU h 1 1 →* ↥L),
      Function.Surjective ρ ∧ ∀ g, ρ g ∈ Subgroup.center ↥L ↔ g ∈ hypScalars h 1 1 := by
  obtain ⟨d, hv⟩ := d
  change d = .twistedA 2 q at hd
  subst hd
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hq] at hc
  obtain ⟨⟨-, hf, hn3, hnq⟩, K, hK, hKfin, hcard, ⟨e'⟩⟩ := hc
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * q.exponent)
    (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  have hn : 2 + 1 = 2 * 1 + 1 := rfl
  rw [hn] at e' hn3 hnq
  obtain ⟨ρ₀, hρ₀, -, hρ₀e⟩ := kFactCoverUnitary Y L hL hodd _ _ K hcard hn3 hnq e'
  have h := ToralCensus.unitaryFieldData_of_card_eq_sq hcard hf
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 1) (ε := 1)
  refine ⟨K, hK, q.exponent, h, ρ₀.comp (hypTransport h hR).toMonoidHom,
    hρ₀.comp (hypTransport h hR).surjective, fun g => ?_⟩
  rw [← QuotientGroup.eq_one_iff, ← ker_hypProj, MonoidHom.mem_ker,
    ← (hypPSUEquivStatedProj h hR (by omega)).map_eq_one_iff, hypPSUEquivStatedProj_hypProj,
    ← hρ₀e, e'.map_eq_one_iff]
  rfl

end Cover

section Levi

open Matrix LeviBlock

variable {K : Type} [Field K]

theorem gl_mul_comm_of_subsingleton {ι : Type} [Fintype ι] [DecidableEq ι] [Subsingleton ι]
    (a b : GL ι K) : a * b = b * a := by
  ext i j
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_subsingleton _ i]
  rw [Subsingleton.elim j i]
  exact mul_comm _ _

theorem subsingleton_hypIndex_zero {ε : ℕ} (hε : ε ≤ 1) : Subsingleton (HypIndex 0 ε) := by
  refine ⟨fun a b => ?_⟩
  rcases a with ⟨i, hi⟩ | ⟨k, hk⟩ | ⟨i, hi⟩
  · omega
  · rcases b with ⟨i, hi⟩ | ⟨k', hk'⟩ | ⟨i, hi⟩
    · omega
    · exact congrArg (fun x => (.inr (.inl x) : HypIndex 0 ε)) (Fin.ext (by omega))
    · omega
  · omega

theorem uniBlockGroup_comm {t s ε : ℕ} {I : Finset ℕ} (hI : IsTopCut I t) (hts : t + s = 1)
    (hε : ε ≤ 1) (j : Option ↥I) (a b : uniBlockGroup K s ε I j) : a * b = b * a := by
  have ht1 : 1 ≤ t := (hI.le t hI.mem).1
  rcases j with _ | c
  · obtain rfl : s = 0 := by omega
    haveI := subsingleton_hypIndex_zero hε
    exact gl_mul_comm_of_subsingleton (K := K) a b
  · have hle : c.1 - predCut I c.1 ≤ 1 := by
      have := (hI.le c.1 c.2).2
      omega
    haveI : Subsingleton (Fin (c.1 - predCut I c.1)) := Fin.subsingleton_iff_le_one.mpr hle
    exact gl_mul_comm_of_subsingleton (K := K) a b

end Levi

theorem solvNormalCentral_of_hypCover {G : Type} [Group G] [Finite G] {L J : Subgroup G}
    {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ} (hr : r = 1) (hε : ε ≤ 1)
    (ρ : hypSU h r ε →* ↥L) (hρ : Function.Surjective ρ)
    (hZ : ∀ g, ρ g ∈ Subgroup.center ↥L ↔ g ∈ hypScalars h r ε)
    (hJ : IsParabolicTwo L J) (hne : J ≠ L) : SolvNormalCentral (↥J ⧸ CFSG.pCore 2 ↥J) := by
  have : Finite K := h.finite
  obtain ⟨T, hT⟩ := ToralCensus.exists_sylow_normalizer_le_comap_of_surjective hρ hJ
  obtain ⟨g, I₀, hI₀, hJ'⟩ :=
    ToralCensus.exists_eq_stab_hypFlag_of_normalizer_le h (by omega) hε T _ hT
  have hne' := ToralCensus.comap_ne_top_of_ne hρ hJ.1 hne
  have hfin : I₀.Finite := (Set.finite_Icc 1 r).subset hI₀
  obtain ⟨I, rfl⟩ : ∃ I : Finset ℕ, (↑I : Set ℕ) = I₀ := ⟨hfin.toFinset, hfin.coe_toFinset⟩
  have hIne : I.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hne' (eq_top_iff.mpr fun y _ => (hJ' y).mpr fun i hi => absurd hi (by simp))
  obtain ⟨t, htI, htmax⟩ : ∃ t ∈ I, ∀ i ∈ I, i ≤ t :=
    ⟨I.max' hIne, I.max'_mem hIne, fun i hi => I.le_max' i hi⟩
  have htr : t ≤ r := (hI₀ (Finset.mem_coe.mpr htI)).2
  obtain ⟨s, rfl⟩ : ∃ s, r = t + s := ⟨r - t, by omega⟩
  have hI : LeviBlock.IsTopCut I t :=
    ⟨htI, fun i hi => ⟨(hI₀ (Finset.mem_coe.mpr hi)).1, htmax i hi⟩⟩
  have hts : t + s = 1 := hr
  set J' : Subgroup (hypSU h (t + s) ε) := (J.subgroupOf L).comap ρ with hJ'def
  have hρJ : ∀ y : hypSU h (t + s) ε, y ∈ J' → (ρ y : G) ∈ J := fun y hy =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hy)
  let φ : ↥J' →* ↥J :=
    { toFun := fun y => ⟨(ρ y.1 : G), hρJ y.1 y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hφ : Function.Surjective φ := by
    intro j
    obtain ⟨y, hy⟩ := hρ ⟨j.1, hJ.1 j.2⟩
    have hyJ : y ∈ J' := by
      rw [hJ'def, Subgroup.mem_comap, hy, Subgroup.mem_subgroupOf]
      exact j.2
    exact ⟨⟨y, hyJ⟩, Subtype.ext (congrArg (Subtype.val : ↥L → G) hy)⟩
  have hφk : Group.IsSolvable ↥φ.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have hc : ∀ x : ↥φ.ker, (x.1.1 : hypSU h (t + s) ε) ∈ Subgroup.center _ := by
      intro x
      have h2 : φ x.1 = 1 := MonoidHom.mem_ker.mp x.2
      have h1 : ρ x.1.1 = 1 := Subtype.ext (congrArg (Subtype.val : ↥J → G) h2)
      exact normOneScalars_le_center h _ _ ((hZ _).mp (by rw [h1]; exact Subgroup.one_mem _))
    exact Subtype.ext (Subtype.ext ((Subgroup.mem_center_iff.mp (hc a) b.1.1).symm))
  set β0 := LeviBlock.uniLeviHom (s := s) h hε hI
  set e' := LeviBlock.stabMulEquiv g hJ'
  let β : ↥J' →* ↥β0.range := β0.rangeRestrict.comp e'.toMonoidHom
  have hβ : Function.Surjective β :=
    (MonoidHom.rangeRestrict_surjective β0).comp e'.surjective
  have hβk : IsPGroup 2 ↥β.ker := by
    have hker : β.ker = β0.ker.comap e'.toMonoidHom := by
      rw [← MonoidHom.ker_rangeRestrict β0, MonoidHom.comap_ker]
    rw [hker]
    exact (LeviBlock.isPGroup_ker_uniLeviHom h hε hI).comap_of_injective e'.toMonoidHom
      e'.injective
  have hΛ : SolvNormalCentral ↥β0.range := by
    refine solvNormalCentral_of_commutative fun a b => Subtype.ext (funext fun j => ?_)
    exact uniBlockGroup_comm hI hts hε j _ _
  exact solvNormalCentral_quotPCore φ hφ hφk β hβ hβk hΛ

theorem solvNormalCentral_parabolic_unitary
    {G : Type} [Group G] [Finite G] {L J : Subgroup G} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hodd : Odd (Nat.card ↥(Subgroup.center ↥L)))
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hq : q.p = 2)
    (hd : d.1 = .twistedA 2 q)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hJ : IsParabolicTwo L J) (hne : J ≠ L) :
    SolvNormalCentral (↥J ⧸ CFSG.pCore 2 ↥J) := by
  obtain ⟨K, _, f, h, ρ, hρ, hZ⟩ := exists_hypCover_three hL hodd d q hq hd e
  exact solvNormalCentral_of_hypCover h rfl le_rfl ρ hρ hZ hJ hne

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
