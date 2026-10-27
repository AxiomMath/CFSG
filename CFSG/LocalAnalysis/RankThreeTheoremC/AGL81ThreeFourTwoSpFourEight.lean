module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48CenFact
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Fac
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import TauCeti.Algebra.Group.Coprime
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.AGLEmbedding.KFactProofs.Sp48 CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

section Generic

variable {X Y : Type*} [Group X] [Group Y]

private theorem commutator_le_of_relIndex_eq_two_sp48 {S T : Subgroup X}
    (h : S.relIndex T = 2) : ⁅T, T⁆ ≤ S := by
  have h2 : (S.subgroupOf T).index = 2 := h
  haveI : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (T ⧸ S.subgroupOf T) :=
    isCyclic_of_prime_card (p := 2) (by rw [← Subgroup.index_eq_card, h2])
  have h1 := Abelianization.commutator_subset_ker (QuotientGroup.mk' (S.subgroupOf T))
  rw [QuotientGroup.ker_mk'] at h1
  rw [← Subgroup.map_subtype_commutator]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (h1 hx)

private theorem pullback_sp48 {ι : X →* Y} (hι : Function.Injective ι)
    {K Y₀ J : Subgroup Y} (hrange : ι.range = K) (hJ : J ≤ K ⊓ Y₀) (hne : J ≠ ⊥)
    (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J (K ⊓ Y₀))
    (hQ : ∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      CFSG.Open.IsQuasisimple Q) :
    Nonempty (J.comap ι ≃* J) ∧ J.comap ι ≠ ⊥ ∧ ⁅J.comap ι, J.comap ι⁆ = J.comap ι ∧
      IsSubnormal (J.comap ι) (Y₀.comap ι) ∧
      ∃ (Q : Type) (_ : Group Q) (f : J.comap ι →* Q), Function.Surjective f ∧
        IsPGroup 2 f.ker ∧ CFSG.Open.IsQuasisimple Q := by
  have hJK : J ≤ ι.range := hrange ▸ hJ.trans inf_le_left
  have hmap : (J.comap ι).map ι = J := Subgroup.map_comap_eq_self hJK
  let θ : J.comap ι ≃* J :=
    (Subgroup.equivMapOfInjective (J.comap ι) ι hι).trans (MulEquiv.subgroupCongr hmap)
  have hKι : K.comap ι = ⊤ := by
    rw [← hrange, MonoidHom.comap_range_self]
  refine ⟨⟨θ⟩, ?_, ?_, ?_, ?_⟩
  · intro hbot
    apply hne
    rw [← hmap, hbot, Subgroup.map_bot]
  · apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hmap, hJp]
  · have h := hJs.comap ι
    rwa [Subgroup.comap_inf, hKι, top_inf_eq] at h
  · obtain ⟨Q, _, f, hf, hfk, hQ⟩ := hQ
    refine ⟨Q, inferInstance, f.comp θ.toMonoidHom, hf.comp θ.surjective, ?_, hQ⟩
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hfk ⟨θ x, hx⟩
    refine ⟨k, Subtype.ext (θ.injective ?_)⟩
    have h1 : (θ x) ^ 2 ^ k = 1 := by
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hk
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one] using h1

end Generic

private theorem fr_pow_apply_of_mem_spE (j : ℕ) {s : Sp8} (hs : s ∈ spE) : (fr ^ j) s = s := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    exact (fr_eq_self_iff_mem_spE (spE_le_spT0 hs)).2 hs

private theorem pow_eight_mem_spT0 {g : Sp8} (hg : g ∈ wrp slD) : g ^ 8 ∈ spT0 := by
  haveI : (spT0.subgroupOf (wrp slD)).Normal := ⟨fun n hn x =>
    Subgroup.mem_subgroupOf.2 (wrp_normalizes_spT0 x.2 (Subgroup.mem_subgroupOf.1 hn))⟩
  have hidx : (spT0.subgroupOf (wrp slD)).index = 8 := by
    have h := Subgroup.card_mul_index (spT0.subgroupOf (wrp slD))
    have hc : Nat.card (spT0.subgroupOf (wrp slD)) = Nat.card spT0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe spT0_le_wrp).toEquiv
    rw [hc, card_spT0, card_wrp_slD] at h
    omega
  have h := Subgroup.pow_index_mem (spT0.subgroupOf (wrp slD)) ⟨g, hg⟩
  rw [hidx] at h
  simpa only [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] using h

private theorem fixes_spE_of_pow_eq_one {α : MulAut Sp8} {n : ℕ} (hα : α ^ (3 ^ n) = 1)
    (hT : ∀ t ∈ spT0, α t ∈ spT0) {s : Sp8} (hs : s ∈ spE) : α s = s := by
  obtain ⟨g, σ, hgσ⟩ := exists_conj_fieldSp hα
  obtain ⟨j, hj⟩ : ∃ j : ℕ,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp 2 GF8 σ = fr ^ j := by
    rcases ringAut_gf8 σ with rfl | rfl | rfl
    · exact ⟨0, by rw [map_one, pow_zero]⟩
    · exact ⟨1, by rw [pow_one]; rfl⟩
    · exact ⟨2, by rw [map_pow]; rfl⟩
  have hαx : ∀ x, α x = g * (fr ^ j) x * g⁻¹ := fun x => by
    rw [hgσ, hj]
    rfl
  have hfr3 : (fr ^ j) ^ 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, fr_pow_three, one_pow]
  have hgN : g ∈ wrp slD := by
    rw [wrp_eq_normalizer]
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    have ht' : ((fr ^ j) ^ 2) t ∈ spT0 := by
      rw [← pow_mul]
      exact fr_pow_mem_spT0 _ ht
    have h1 := hT _ ht'
    rw [hαx] at h1
    have h2 : (fr ^ j) (((fr ^ j) ^ 2) t) = t := by
      rw [← MulAut.mul_apply, ← pow_succ', hfr3]
      rfl
    rwa [h2] at h1
  have hgE : ∀ k : ℕ, ∀ s ∈ spE, g ^ k * s * (g ^ k)⁻¹ ∈ spE := fun k s hs =>
    wrp_normalizes_spE (Subgroup.pow_mem _ hgN k) hs
  have hiter : ∀ k : ℕ, (α ^ k) s = g ^ k * s * (g ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, hαx, fr_pow_apply_of_mem_spE j (hgE k s hs)]
      group
  set C := Subgroup.centralizer ({s} : Set Sp8) with hC
  have hmemC : ∀ {x : Sp8}, x * s * x⁻¹ = s → x ∈ C := fun {x} hx => by
    rw [hC, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc s * x = x * s * x⁻¹ * x := by rw [hx]
      _ = x * s := by group
  have hc3 : g ^ (3 ^ n) ∈ C := hmemC (by rw [← hiter, hα]; rfl)
  have hc8 : g ^ 8 ∈ C := hmemC (by
    rw [comm_spT0 _ (pow_eight_mem_spT0 hgN) s (spE_le_spT0 hs)]
    group)
  obtain ⟨u, v, huv⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := Sp8)
    (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 3 8))
  have hgC : g ∈ C := by
    rw [← huv g]
    exact mul_mem (zpow_mem hc3 u) (zpow_mem hc8 v)
  rw [hC, Subgroup.mem_centralizer_iff] at hgC
  rw [hαx, fr_pow_apply_of_mem_spE j hs, ← hgC s rfl]
  group

private theorem exists_surj_of_isSubnormal_wrp_top {J : Subgroup Sp8}
    (hJs : IsSubnormal J (wrp (⊤ : Subgroup Sl28))) (hne : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) :
    ∃ g : J →* Sl28, Function.Surjective g := by
  haveI := sl28_isSimpleGroup
  set V : Subgroup Sp8 := blkHom.range with hV
  have hVW : V ≤ wrp (⊤ : Subgroup Sl28) := blkRange_le_wrp
  have hcardV : Nat.card V = 504 * 504 := by
    rw [hV, MonoidHom.range_eq_map, Subgroup.card_map_of_injective blkHom_injective,
      Subgroup.card_top, Nat.card_prod, card_sl28]
  have hrel : V.relIndex (wrp (⊤ : Subgroup Sl28)) = 2 := by
    have h := Subgroup.card_mul_index (V.subgroupOf (wrp (⊤ : Subgroup Sl28)))
    have hc : Nat.card (V.subgroupOf (wrp (⊤ : Subgroup Sl28))) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [hc, hcardV, card_wrp_top] at h
    rw [Subgroup.relIndex]
    omega
  have hJW : J ≤ wrp (⊤ : Subgroup Sl28) := hJs.le
  have hJV : J ≤ V := by
    rw [← hJp]
    exact (Subgroup.commutator_mono hJW hJW).trans (commutator_le_of_relIndex_eq_two_sp48 hrel)
  have hsub := hJs.inf V
  rw [inf_eq_left.2 hJV, inf_eq_right.2 hVW] at hsub
  set J₀ : Subgroup (Sl28 × Sl28) := J.comap blkHom with hJ₀
  have hmap : J₀.map blkHom = J := Subgroup.map_comap_eq_self hJV
  let θ : J₀ ≃* J :=
    (Subgroup.equivMapOfInjective J₀ blkHom blkHom_injective).trans (MulEquiv.subgroupCongr hmap)
  have hJ₀s : IsSubnormal J₀ ⊤ := by
    have h := hsub.comap blkHom
    rwa [hV, MonoidHom.comap_range_self] at h
  have hJ₀ne : J₀ ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hmap, hbot, Subgroup.map_bot]
  have hproj : ∀ (π : Sl28 × Sl28 →* Sl28), Function.Surjective π →
      J₀.map π = ⊥ ∨ J₀.map π = ⊤ := fun π hπ => by
    have h := hJ₀s.map π
    rw [Subgroup.map_top_of_surjective π hπ] at h
    exact h.eq_bot_or_top
  have hsurj : ∀ (π : Sl28 × Sl28 →* Sl28), J₀.map π = ⊤ →
      ∃ g : J →* Sl28, Function.Surjective g := fun π hπ => by
    have hs' : Function.Surjective (π.comp J₀.subtype) := by
      intro y
      have hy : y ∈ J₀.map π := hπ ▸ Subgroup.mem_top y
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    exact ⟨(π.comp J₀.subtype).comp θ.symm.toMonoidHom, hs'.comp θ.symm.surjective⟩
  rcases hproj (MonoidHom.fst Sl28 Sl28) Prod.fst_surjective with h1 | h1
  · rcases hproj (MonoidHom.snd Sl28 Sl28) Prod.snd_surjective with h2 | h2
    · exfalso
      apply hJ₀ne
      rw [eq_bot_iff]
      intro x hx
      have hx1 : x.1 = 1 := by
        have : x.1 ∈ J₀.map (MonoidHom.fst Sl28 Sl28) := ⟨x, hx, rfl⟩
        rwa [h1, Subgroup.mem_bot] at this
      have hx2 : x.2 = 1 := by
        have : x.2 ∈ J₀.map (MonoidHom.snd Sl28 Sl28) := ⟨x, hx, rfl⟩
        rwa [h2, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Prod.ext hx1 hx2
    · exact hsurj _ h2
  · exact hsurj _ h1

private theorem exists_surj_sl28_of_sp48 (hcard : Nat.card Sp8 = 3 ^ 4 * 13045760)
    (hsimple : IsSimpleGroup Sp8) {Y : Type} [Group Y] [Finite Y] {K Y₀ E : Subgroup Y}
    [K.Normal] (R : Sylow 3 Y) (e : K ≃* Sp8) (hER : E ≤ R) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2)
    (hcore : (if 3 ≤ pRank 3 (R : Subgroup Y) then GLBWeakCore 3 (R : Subgroup Y)
      else GLBCore 3 1 E) ≤ Y₀) (hKY : ¬ K ≤ Y₀) {J : Subgroup Y} (hJ : J ≤ K ⊓ Y₀)
    (hne : J ≠ ⊥) (hJp : ⁅J, J⁆ = J) (hJs : IsSubnormal J (K ⊓ Y₀))
    (hQ : ∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      CFSG.Open.IsQuasisimple Q) :
    ∃ g : J →* Sl28, Function.Surjective g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT0p : IsPGroup 3 spT0 := IsPGroup.of_card (n := 4) (by rw [card_spT0]; norm_num)
  have hT0i : ¬ 3 ∣ spT0.index := by
    have h := Subgroup.card_mul_index spT0
    rw [card_spT0, hcard] at h
    omega
  set T0S : Sylow 3 Sp8 := hT0p.toSylow hT0i with hT0S
  have hcoeT0S : (T0S : Subgroup Sp8) = spT0 := IsPGroup.toSylow_coe _ _
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq Sp8 (Sylow.mapSurjective hs T) T0S
  set ε : K ≃* Sp8 := e.trans (MulAut.conj m) with hε
  have hεT : (T : Subgroup K).map ε.toMonoidHom = spT0 := by
    have h1 := congrArg (fun P : Sylow 3 Sp8 => (P : Subgroup Sp8)) hm
    simp only [Sylow.coe_subgroup_smul, hcoeT0S, Sylow.coe_mapSurjective] at h1
    rw [← h1]
    change Subgroup.map ε.toMonoidHom (T : Subgroup K) =
      Subgroup.map (MulAut.conj m).toMonoidHom (Subgroup.map e.toMonoidHom (T : Subgroup K))
    rw [Subgroup.map_map]
    rfl
  have hιdef : emb ε = K.subtype.comp ε.symm.toMonoidHom := rfl
  have hι : Function.Injective (emb ε) := emb_injective ε
  have hrange : (emb ε).range = K := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact emb_mem ε x
    · intro hy
      exact exists_emb ε hy
  have hιT : spT0.map (emb ε) = (R : Subgroup Y) ⊓ K := by
    have h1 : ((T : Subgroup K).map ε.toMonoidHom).map ε.symm.toMonoidHom = T := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (T : Subgroup K)
      ext x
      simp
    rw [← hT, ← hεT, hιdef, ← Subgroup.map_map, h1]
  set A : Subgroup Y := spE.map (emb ε) with hA
  have hAR : A ≤ R :=
    (Subgroup.map_mono spE_le_spT0).trans (hιT.le.trans inf_le_left)
  have hRA : ∀ r ∈ (R : Subgroup Y), ∀ a ∈ A, r * a = a * r := by
    intro r hr a ha
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
    have hrn : r ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hα : (adHom K ε r) ^ (3 ^ n) = 1 := by rw [← map_pow, hrn, map_one]
    have hTα : ∀ t ∈ spT0, adHom K ε r t ∈ spT0 := by
      intro t ht
      have h1 : emb ε t ∈ (R : Subgroup Y) ⊓ K := hιT ▸ Subgroup.mem_map_of_mem _ ht
      have h2 : emb ε (adHom K ε r t) ∈ spT0.map (emb ε) := by
        rw [emb_adHom, hιT]
        exact ⟨R.toSubgroup.mul_mem (R.toSubgroup.mul_mem hr h1.1) (R.toSubgroup.inv_mem hr),
          ‹K.Normal›.conj_mem _ h1.2 r⟩
      obtain ⟨t', ht', heq⟩ := h2
      rwa [← hι heq]
    have h := fixes_spE_of_pow_eq_one hα hTα hs
    have h' : r * emb ε s * r⁻¹ = emb ε s := by rw [← emb_adHom, h]
    calc r * emb ε s = r * emb ε s * r⁻¹ * r := by group
      _ = emb ε s * r := by rw [h']
  have hEel : IsElemAbelian 3 spE := by
    refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ((mem_spE_iff_cube x).1 hx).2⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (comm_spT0 a (spE_le_spT0 ha) b (spE_le_spT0 hb))
  have hAel : IsElemAbelian 3 A := hEel.map (emb ε)
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [hA, Subgroup.card_map_of_injective hι, card_spE]
    norm_num
  have hNA : normalizer (A : Set Y) ≤ Y₀ := by
    by_cases h3 : 3 ≤ pRank 3 (R : Subgroup Y)
    · rw [if_pos h3] at hcore
      refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 hAR
        (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hAel hAc) ?_).trans hcore
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      refine h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three ?_)
      intro r hr
      refine Subgroup.mem_sup_right ⟨hr, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
      exact (hRA r hr a ha).symm
    · rw [if_neg h3] at hcore
      have hR2 : CFSG.Open.pRank 3 (R : Subgroup Y) ≤ 2 := by
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
        omega
      have hAE : A ≤ E := fun a ha =>
        CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two
          Nat.prime_three hR2 hER hE hEc (hAR ha) (hAel.2 a ha) fun r hr => hRA r hr a ha
      have hAE' : A = E := Subgroup.eq_of_le_of_card_ge hAE (by rw [hEc, hAc])
      rw [hAE']
      refine (le_sSup ⟨E, le_rfl, ?_, rfl⟩ : normalizer (E : Set Y) ≤ GLBCore 3 1 E).trans hcore
      exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hE (k := 2) hEc |>.trans' (by norm_num)
  have hY₀ : Y₀ ≠ ⊤ := fun h => hKY (h ▸ le_top)
  obtain ⟨θ, -, -, hcl⟩ := classify_comap hcard hsimple hNA hY₀
  obtain ⟨⟨θJ⟩, hne', hJp', hJs', Q, _, f, hf, hfk, hQ'⟩ :=
    pullback_sp48 hι hrange hJ hne hJp hJs hQ
  rcases hcl with hN | hM | hM
  ·
    exfalso
    rw [hN] at hJs'
    have hCN : Group.IsSolvable (centralizer (spT0 : Set Sp8) ⊓ wrp slD : Subgroup Sp8) :=
      TenThirteen.isSolvable_centralizer_inf_of_le Nat.prime_three hT0p fun h hh =>
        centralizer_spE_le fun z hz =>
          (Subgroup.mem_centralizer_iff.1 hh.1 z (spE_le_spT0 hz)).symm
    exact hne' (TenThirteen.eq_bot_of_isSubnormal_of_quasisimple_quotient Nat.prime_three
      Nat.prime_two (by norm_num) hJs' hJp' f hf hfk hQ' spT0_le_wrp wrp_le_normalizer hT0p hCN)
  ·
    rw [hM] at hJs'
    obtain ⟨g, hg⟩ := exists_surj_of_isSubnormal_wrp_top hJs' hne' hJp'
    exact ⟨g.comp θJ.symm.toMonoidHom, hg.comp θJ.symm.surjective⟩
  ·
    rw [hM] at hJs'
    set J' : Subgroup Sp8 := (J.comap (emb ε)).map θ.symm.toMonoidHom with hJ'
    have hθM : ((wrp (⊤ : Subgroup Sl28)).map θ.toMonoidHom).map θ.symm.toMonoidHom =
        wrp (⊤ : Subgroup Sl28) := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id (wrp (⊤ : Subgroup Sl28))
      ext x
      simp
    have hJ's : IsSubnormal J' (wrp (⊤ : Subgroup Sl28)) := by
      have h := hJs'.map θ.symm.toMonoidHom
      rwa [hθM] at h
    let θ' : J.comap (emb ε) ≃* J' :=
      Subgroup.equivMapOfInjective (J.comap (emb ε)) θ.symm.toMonoidHom θ.symm.injective
    have hJ'ne : J' ≠ ⊥ := by
      intro hbot
      apply hne'
      rw [eq_bot_iff]
      intro x hx
      have : θ.symm x ∈ J' := Subgroup.mem_map_of_mem _ hx
      rw [hbot, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact θ.symm.injective (this.trans (map_one _).symm)
    have hJ'p : ⁅J', J'⁆ = J' := by
      rw [hJ', ← Subgroup.map_commutator, hJp']
    obtain ⟨g, hg⟩ := exists_surj_of_isSubnormal_wrp_top hJ's hJ'ne hJ'p
    exact ⟨(g.comp θ'.toMonoidHom).comp θJ.symm.toMonoidHom,
      (hg.comp θ'.surjective).comp θJ.symm.surjective⟩

theorem threeFourTwoAt_sp48 : ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex),
    q.p = 2 → q.exponent = 3 → d.1 = .B 2 q →
    ThreeFourTwoAt 3 (TauCeti.CFSGIndex.lie d).Group := by
  intro q d hqp hqe hd
  have hd' : IsSpFourEightIndex d := ⟨q, hqp, hqe, hd⟩
  obtain ⟨⟨eX⟩, hcardX⟩ := exists_equiv_sp8 hd' (MulEquiv.refl (CatGroup d))
  have hcard : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardX]
    exact Nat.card_congr eX.symm.toEquiv
  have hsimple : IsSimpleGroup Sp8 := isSimple_sp8_of_index hd' (MulEquiv.refl _) eX
  obtain ⟨x, hv⟩ := d
  change x = _ at hd
  subst hd
  have hXs : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group := eX.isSimpleGroup
  have hXnab : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := sl28_nonabelian
    refine ⟨eX.symm (blkHom (a, 1)), eX.symm (blkHom (b, 1)), fun h => hab ?_⟩
    have h1 := congrArg eX h
    simp only [map_mul, MulEquiv.apply_symm_apply, ← map_mul] at h1
    have h2 := blkHom_injective h1
    simpa using congrArg Prod.fst h2
  have hXout : Group.IsSolvable (Outer (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group) :=
    CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv (MulEquiv.refl _))
  refine threeFourTwoAt_of_forall hXs hXnab hXout ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ hER hE hEc hcore _ hKY J hJ hne hJp hJs hQ
  haveI := hKn
  obtain ⟨e⟩ := hKX
  obtain ⟨g, hg⟩ :=
    exists_surj_sl28_of_sp48 hcard hsimple R (e.trans eX) hER hE hEc hcore hKY hJ hne hJp hJs hQ
  obtain rfl : q = ⟨2, 3, Nat.prime_two, by norm_num⟩ := TauCeti.PrimePower.ext hqp hqe
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let dJ : TauCeti.ValidLieTypeIndex := ⟨.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩,
    valid_A_one_eight⟩
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := dJ)
    ⟨_, rfl, rfl, rfl⟩
  let φ : Sl28 ≃* (TauCeti.CFSGIndex.lie dJ).Group := sl28Equiv.trans eP.symm
  refine ⟨.lie ⟨.B 2 _, hv⟩, .lie dJ, ?_, ⟨e⟩, φ.toMonoidHom.comp g, φ.surjective.comp hg⟩
  exact Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, rfl, ⟨.B 2 _, hv⟩, dJ, rfl, rfl, rfl, rfl⟩))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
