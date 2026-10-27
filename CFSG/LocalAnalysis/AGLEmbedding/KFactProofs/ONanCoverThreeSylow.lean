module

public import CFSG.LocalAnalysis.AGLEmbedding.SporadicAlphaData
import CFSG.LocalAnalysis.AGLEmbedding.CoverAbelianSylow
import CFSG.LocalAnalysis.AGLEmbedding.CoverRankLift
import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools
public import CFSG.LocalAnalysis.AGLEmbedding.KFacts

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open scoped commutatorElement

open CFSG.AGLEmbedding
open CFSG.SectionRank.OddCover (commutatorElement_mul_left_of_mem_center)

theorem card_zpowers_sup_center_le {G : Type*} [Group G] [Finite G] {x : G} (hx : x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center G) = 3) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) ≤ 9 := by
  let φ : Subgroup.zpowers x × Subgroup.center G →
      (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) :=
    fun p => ⟨(p.1 : G) * (p.2 : G),
      Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨m, hm⟩
    have hm' : m ∈ (↑(Subgroup.zpowers x ⊔ Subgroup.center G) : Set G) := hm
    rw [Subgroup.mul_normal] at hm'
    obtain ⟨u, hu, z, hz, rfl⟩ := hm'
    exact ⟨(⟨u, hu⟩, ⟨z, hz⟩), rfl⟩
  have h1 := Nat.card_le_card_of_surjective φ hφ
  rw [Nat.card_prod, hZ, Nat.card_zpowers] at h1
  have h2 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)
  calc _ ≤ orderOf x * 3 := h1
    _ ≤ 3 * 3 := Nat.mul_le_mul_right 3 h2
    _ = 9 := by norm_num

theorem exists_elemAbelian_of_class_two {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hZT : Subgroup.center G ≤ T) (hZ : Nat.card (Subgroup.center G) = 3)
    (hc : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Subgroup.center G) (hexp : ∀ t ∈ T, t ^ 3 = 1)
    (hT : 3 ^ 4 ≤ Nat.card T) :
    ∃ E : Subgroup G, E ≤ T ∧ Open.IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E := by
  classical
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTp : IsPGroup 3 T := fun t => ⟨1, Subtype.ext (by simpa using hexp t t.2)⟩
  obtain ⟨x, hxT, hxZ⟩ : ∃ x ∈ T, x ∉ Subgroup.center G := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show T ≤ Subgroup.center G from h)
    rw [hZ] at this
    omega
  let f : T →* Subgroup.center G :=
    { toFun := fun w => ⟨⁅(w : G), x⁆, hc w w.2 x hxT⟩
      map_one' := Subtype.ext (commutatorElement_one_left x)
      map_mul' := fun a b => Subtype.ext
        (commutatorElement_mul_left_of_mem_center (hc b b.2 x hxT)) }
  have hfk : ∀ w : f.ker, ((w : T) : G) * x = x * ((w : T) : G) := by
    intro w
    have h0 : ⁅((w : T) : G), x⁆ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp w.2)
    exact commutatorElement_eq_one_iff_mul_comm.mp h0
  have hker27 : 27 ≤ Nat.card f.ker := by
    have h1 := Subgroup.card_mul_index f.ker
    have h2 : f.ker.index ≤ 3 := by
      rw [Subgroup.index_ker]
      exact (Subgroup.card_le_card_group f.range).trans hZ.le
    by_contra hlt
    push Not at hlt
    have : Nat.card T ≤ 26 * 3 := by
      rw [← h1]; exact Nat.mul_le_mul (by omega) h2
    omega
  have hM9 := card_zpowers_sup_center_le (hexp x hxT) hZ
  obtain ⟨y', hy'⟩ : ∃ y' : f.ker,
      ((y' : T) : G) ∉ (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) := by
    by_contra h
    push Not at h
    have : Nat.card f.ker ≤ Nat.card (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) :=
      Nat.card_le_card_of_injective (fun y => ⟨((y : T) : G), h y⟩) (by
        intro a b hab
        have h' : ((a : T) : G) = ((b : T) : G) :=
          congrArg (fun w : (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) => (w : G)) hab
        exact Subtype.ext (Subtype.ext h'))
    omega
  have hyT : ((y' : T) : G) ∈ T := (y' : T).2
  set y : G := ((y' : T) : G) with hydef
  have hxy : x * y = y * x := (hfk y').symm
  have hcommK0 : ∀ a ∈ ({x, y} : Set G) ∪ (Subgroup.center G : Set G),
      ∀ b ∈ ({x, y} : Set G) ∪ (Subgroup.center G : Set G), a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe] at ha hb
    rcases ha with (rfl | rfl) | ha <;> rcases hb with (rfl | rfl) | hb
    · rfl
    · exact hxy
    · exact Subgroup.mem_center_iff.mp hb _
    · exact hxy.symm
    · rfl
    · exact Subgroup.mem_center_iff.mp hb _
    · exact (Subgroup.mem_center_iff.mp ha _).symm
    · exact (Subgroup.mem_center_iff.mp ha _).symm
    · exact Subgroup.mem_center_iff.mp hb _
  have hcomm : IsMulCommutative
      (Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G))) :=
    Subgroup.isMulCommutative_closure fun a ha b hb _ => hcommK0 a ha b hb
  have hxK : x ∈ Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) :=
    Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have hyK : y ∈ Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) :=
    Subgroup.subset_closure (Or.inl (Or.inr rfl))
  have hZK : Subgroup.center G ≤
      Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) :=
    fun z hz => Subgroup.subset_closure (Or.inr hz)
  have hET : Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) ≤ T := by
    rw [Subgroup.closure_le]
    rintro a (ha | ha)
    · rcases ha with rfl | rfl
      · exact hxT
      · exact hyT
    · exact hZT ha
  refine ⟨Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)), hET,
    ⟨hcomm, fun g hg => hexp g (hET hg)⟩, ?_⟩
  have hlt : ∀ {H K : Subgroup G}, H ≤ K → H ≠ K → Nat.card H < Nat.card K :=
    fun hle hne => lt_of_le_of_ne (Subgroup.card_le_of_le hle)
      (fun heq => hne (Subgroup.eq_of_le_of_card_ge hle heq.ge))
  have hMT : (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) ≤ T :=
    sup_le (Subgroup.zpowers_le.mpr hxT) hZT
  have hMK : (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) ≤
      Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) :=
    sup_le (Subgroup.zpowers_le.mpr hxK) hZK
  have hZM : Nat.card (Subgroup.center G) <
      Nat.card (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) :=
    hlt le_sup_right fun h => hxZ (h ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hME : Nat.card (Subgroup.zpowers x ⊔ Subgroup.center G : Subgroup G) <
      Nat.card (Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G))) :=
    hlt hMK fun h => hy' (by
      have : y ∈ Subgroup.closure (({x, y} : Set G) ∪ (Subgroup.center G : Set G)) := hyK
      rwa [← h] at this)
  obtain ⟨j, hj⟩ := (hTp.to_le hMT).exists_card_eq
  obtain ⟨k, hk⟩ := (hTp.to_le hET).exists_card_eq
  rw [hj, hZ] at hZM
  rw [hj, hk] at hME
  have hj2 : 2 ≤ j := by
    by_contra h
    have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    omega
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk3

theorem three_le_pRank_cover_of_abelianSylowDatum {K X : Type} [Group K] [Finite K] [Group X]
    [Group.IsPerfect K] (π : K →* X) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center K) (hZ3 : Nat.card (Subgroup.center K) = 3)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZc : IsCyclic (Subgroup.center K))
    (hD : AbelianSylowDatum X 3) (h3 : 3 ^ 3 ∣ Nat.card X) :
    3 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Finite X := Finite.of_surjective π hπ
  have hZ : Subgroup.center K ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ3
    omega
  obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hexp := (coverAbelianSylowLemma K X π hπ hker ‹_› 3 hp (by norm_num) hZ hZp hZc hD T).1
  obtain ⟨D, hn, hF, hN, hidx⟩ := hD
  obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (D.card_span hp)).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q (T.mapSurjective hπ)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  set D' := D.map (MulAut.conj g).toMonoidHom hinj with hD'
  have hspan : D'.span ≤ (T : Subgroup K).map π := by
    have h2 := congrArg (fun S : Sylow 3 X => (S : Subgroup X)) hg
    simp only [Sylow.coe_mapSurjective] at h2
    rw [hD', ModuleSpec.map_span, ← h2, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.map_mono hQ
  have hle : D'.span.comap π ≤ (T : Subgroup K) := by
    calc D'.span.comap π ≤ ((T : Subgroup K).map π).comap π := Subgroup.comap_mono hspan
      _ = (T : Subgroup K) ⊔ π.ker := Subgroup.comap_map_eq _ _
      _ = (T : Subgroup K) := by rw [hker, sup_eq_left]; exact IsPGroup.le_sylow_of_normal hZp T
  have hidx' : ¬ 3 ∣ (D'.span.comap π).index := by
    rwa [Subgroup.index_comap_of_surjective _ hπ, hD', ModuleSpec.map_span,
      Subgroup.index_map_of_bijective (MulAut.conj g).bijective]
  have heq : D'.span.comap π = (T : Subgroup K) :=
    (((T.isPGroup'.to_le hle).toSylow hidx').3 T.isPGroup' hle).symm
  have hcard : Nat.card (T : Subgroup K) = Nat.card (Subgroup.center K) * 3 ^ D'.n := by
    rw [← heq]; exact D'.card_comap π hp hπ hker
  have hc : ∀ x ∈ (T : Subgroup K), ∀ y ∈ (T : Subgroup K), ⁅x, y⁆ ∈ Subgroup.center K := by
    rw [← heq]; exact fun x hx y hy => D'.commutator_mem_center π hker hx hy
  have hn3 : 3 ≤ D'.n := by
    have h1 := Subgroup.card_mul_index D.span
    rw [D.card_span hp] at h1
    rw [← h1] at h3
    have hcop : Nat.Coprime (3 ^ 3) D.span.index :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).2 hidx)
    have h4 : 3 ^ 3 ∣ 3 ^ D.n := hcop.dvd_of_dvd_mul_right h3
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h4
  have hZT : Subgroup.center K ≤ (T : Subgroup K) := IsPGroup.le_sylow_of_normal hZp T
  obtain ⟨E, hET, hE, hEc⟩ := exists_elemAbelian_of_class_two hZT hZ3 hc hexp (by
    rw [hcard, hZ3, pow_succ' 3 3]
    exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by norm_num) hn3))
  exact le_pRank_of_pow_le_card hp (le_top) hE hEc

end CFSG.AGLEmbedding.KFactProofs.CoverThree
