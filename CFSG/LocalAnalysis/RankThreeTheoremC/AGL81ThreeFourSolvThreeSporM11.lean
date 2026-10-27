module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsInner
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.M11Three
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Orbits
import CFSG.ClassicalInvolution.Q3.M11Kernel
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionDatum
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers


private theorem map_conj_eq_of_mem_normalizer {Y : Type*} [Group Y] {J : Subgroup Y} {n : Y}
    (hn : n ∈ normalizer (J : Set Y)) : J.map (MulAut.conj n).toMonoidHom = J := by
  ext x
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (mem_normalizer_iff.mp hn j).mp hj
  · intro hx
    refine ⟨n⁻¹ * x * n, (mem_normalizer_iff.mp hn _).mpr (by simpa [mul_assoc] using hx), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_mul {Y : Type*} [Group Y] (J : Subgroup Y) (a b : Y) :
    J.map (MulAut.conj (a * b)).toMonoidHom =
      (J.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem threeFourSolvThreeNoneAt_m11 :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.sporadic .M11).Group := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ _ hrkC hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    _ hdir
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  obtain ⟨hout, hsyl⟩ := CFSG.AGLEmbeddingD2.kFactM11Three ↥K hKX
  have hinnerAll : ∀ α : MulAut ↥K, ∃ g : ↥K, MulAut.conj g = α := by
    intro α
    have htop : CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K = ⊤ :=
      Subgroup.index_eq_one.mp hout
    exact (htop ▸ Subgroup.mem_top α : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥K)
  have hinner : ∀ α : MulAut ↥K, α ^ 3 = 1 → ∃ g : ↥K, α = MulAut.conj g := fun α _ => by
    obtain ⟨g, hg⟩ := hinnerAll α
    exact ⟨g, hg.symm⟩
  obtain ⟨eK⟩ := hKX
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  have hcardK : Nat.card ↥K = 7920 := by
    rw [Nat.card_congr (eK.trans eC.symm).toEquiv, CFSG.Sporadic.Mathieu.card_M11]
  have hK27 : ¬ 27 ∣ Nat.card ↥K := by rw [hcardK]; norm_num
  have hKcomm : ∀ Q : Subgroup Y, Q ≤ K → (∀ x ∈ Q, x ^ 3 = 1) →
      ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun Q hQ h3 => commute_of_le_of_not_dvd hQ hK27 h3
  rcases SolvNone.le_centralizer_or_le_of_inner σ hZ (fun y _ h => exists_mul_of_pow_three hinner h)
      (fun Q hQ _ => hKcomm Q hQ) hrkC hC hO2 hker hσY hσs hb with
    h | ⟨hJK, y₀, hy₀K, hy₀3, hJy₀⟩
  · exact h
  by_contra hJC
  have hKC := CFSG.QuasithinUnique.RankOneRecog.inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hdecY : ∀ y : Y, ∃ k : ↥K, (k : Y)⁻¹ * y ∈ C := by
    intro y
    obtain ⟨k, hk⟩ := hinnerAll (MulAut.conjNormal y)
    refine ⟨k, mem_centralizer_iff.mpr fun m hm => ?_⟩
    have h1 := congrArg (fun a : MulAut ↥K => ((a ⟨m, hm⟩ : ↥K) : Y)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc m * ((k : Y)⁻¹ * y) = (k : Y)⁻¹ * ((k : Y) * m * (k : Y)⁻¹) * y := by group
      _ = (k : Y)⁻¹ * (y * m * y⁻¹) * y := by rw [h1]
      _ = (k : Y)⁻¹ * y * m := by group
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTcard, -, hTmax⟩ := hsyl T
  set TY : Subgroup Y := (T : Subgroup ↥K).map K.subtype with hTY
  have hTYR : TY ≤ R := by rw [hT]; exact inf_le_left
  have hTYK : TY ≤ K := by rw [hT]; exact inf_le_right
  have hTYcard : Nat.card TY = 9 := by
    rw [hTY, Subgroup.card_map_of_injective K.subtype_injective, hTcard]
    norm_num
  have hNR : normalizer ((R : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  have hRCK : (((R : Subgroup Y) ⊔ C) ⊓ K).comap K.subtype = (T : Subgroup ↥K) := by
    have hp : IsPGroup 3 ((((R : Subgroup Y) ⊔ C) ⊓ K).comap K.subtype) := by
      rintro ⟨z, hz⟩
      rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_inf] at hz
      obtain ⟨hzRC, hzK⟩ := hz
      rw [← SetLike.mem_coe, Subgroup.mul_normal (R : Subgroup Y) C] at hzRC
      obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.mp hzRC
      obtain ⟨m, hm⟩ := (R.isPGroup' ⟨r, hr⟩)
      have hm' : r ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have hzc : (z : Y) * c⁻¹ = c⁻¹ * z :=
        mem_centralizer_iff.mp (C.inv_mem hc) (z : Y) hzK
      have hr' : r = (z : Y) * c⁻¹ := by rw [← hrc]; group
      have h1 : (z : Y) ^ 3 ^ m * (c⁻¹) ^ 3 ^ m = 1 := by
        rw [← (Commute.mul_pow hzc _), ← hr', hm']
      have h2 : (z : Y) ^ 3 ^ m ∈ K ⊓ C := by
        refine ⟨K.pow_mem hzK _, ?_⟩
        rw [eq_inv_of_mul_eq_one_left h1]
        exact C.inv_mem (C.pow_mem (C.inv_mem hc) _)
      rw [hKC, Subgroup.mem_bot] at h2
      have h3 : z ^ 3 ^ m = 1 := Subtype.ext (by simpa using h2)
      refine ⟨m, ?_⟩
      rw [Subtype.ext_iff, SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact h3
    have hle : (T : Subgroup ↥K) ≤ (((R : Subgroup Y) ⊔ C) ⊓ K).comap K.subtype := by
      intro t ht
      refine Subgroup.mem_comap.mpr ⟨mem_sup_left (hTYR ⟨t, ht, rfl⟩), t.2⟩
    exact T.is_maximal' hp hle
  have hRTC : ∀ r ∈ (R : Subgroup Y), ∃ t ∈ (T : Subgroup ↥K), ((t : Y))⁻¹ * r ∈ C := by
    intro r hr
    obtain ⟨k, hk⟩ := hdecY r
    refine ⟨k, ?_, hk⟩
    rw [← hRCK, Subgroup.mem_comap, Subgroup.coe_subtype]
    refine ⟨?_, k.2⟩
    have : (k : Y) = r * ((k : Y)⁻¹ * r)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_left hr) (mem_sup_right (C.inv_mem hk))
  have hNK : ∀ k : ↥K, k ∈ normalizer ((T : Subgroup ↥K) : Set ↥K) → (k : Y) ∈ Y₀ := by
    intro k hk
    refine hNR (Subgroup.mem_normalizer_fintype fun r hr => ?_)
    obtain ⟨t, ht, htr⟩ := hRTC r hr
    have hkt : k * t * k⁻¹ ∈ (T : Subgroup ↥K) := (mem_normalizer_iff.mp hk t).mp ht
    have hc : (k : Y) * ((t : Y)⁻¹ * r) * (k : Y)⁻¹ = (t : Y)⁻¹ * r := by
      have := mem_centralizer_iff.mp htr (k : Y) k.2
      rw [this, mul_inv_cancel_right]
    have he : (k : Y) * r * (k : Y)⁻¹ = ((k * t * k⁻¹ : ↥K) : Y) * ((t : Y)⁻¹ * r) := by
      calc (k : Y) * r * (k : Y)⁻¹ = (k : Y) * t * (k : Y)⁻¹ *
            ((k : Y) * ((t : Y)⁻¹ * r) * (k : Y)⁻¹) := by group
        _ = ((k * t * k⁻¹ : ↥K) : Y) * ((t : Y)⁻¹ * r) := by
          rw [hc]
          simp
    rw [he]
    refine Subgroup.mul_mem _ (hTYR ⟨_, hkt, rfl⟩) ?_
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTYR ⟨t, ht, rfl⟩)) hr
  have hKsimple : IsSimpleGroup ↥K := by
    haveI := CFSG.ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    exact (eK.trans eC.symm).isSimpleGroup
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥K = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
    have h1 : Nat.card (⊤ : Subgroup ↥K) = Nat.card (⊥ : Subgroup ↥K) := by rw [← htop, hZ]
    rw [Subgroup.card_top, Subgroup.card_bot, hcardK] at h1
    norm_num at h1
  have hKcomp : IsComponentOf K ⊤ := by
    haveI := hKsimple
    haveI : Group.IsPerfect ↥K := ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K hnab⟩
    exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩
  have hY₀K : Y₀.comap K.subtype = normalizer ((T : Subgroup ↥K) : Set ↥K) := by
    rcases hTmax (Y₀.comap K.subtype) (fun k hk => hNK k hk) with h | h
    · exact h
    · exfalso
      refine hcomp K hKcomp le_rfl fun y hy => ?_
      have : (⟨y, hy⟩ : ↥K) ∈ Y₀.comap K.subtype := h ▸ Subgroup.mem_top _
      exact this
  have hJsub : IsSubnormal J Y₀ := isSubnormal_oUpperTwo_map σ hσs
  have hJ3 : ∀ x ∈ J, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp (hJy₀ hx)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy₀3, one_zpow]
  have hJp : IsPGroup 3 J := fun x => ⟨1, Subtype.ext (by simpa using hJ3 x x.2)⟩
  set J' : Subgroup ↥K := J.comap K.subtype with hJ'
  have hJ'map : J'.map K.subtype = J :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hJK)
  have hJ'T : J' ≤ (T : Subgroup ↥K) := by
    have h1 := CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal
      (hJsub.comap K.subtype) (hJp.comap_of_injective K.subtype K.subtype_injective)
    rw [hY₀K] at h1
    have hp := (pCoreOf_isPGroup 3 (normalizer ((T : Subgroup ↥K) : Set ↥K))).to_sup_of_normal_left'
      T.isPGroup' (le_normalizer.trans (localGroup_le_normalizer_pCoreOf 3 _))
    exact h1.trans (le_sup_left.trans (T.is_maximal' hp le_sup_right).le)
  have hJT : J ≤ TY := by
    rw [← hJ'map]
    exact Subgroup.map_mono hJ'T
  have hJne : J ≠ ⊥ := fun h => hJC (by rw [h]; exact bot_le)
  have hJcard : Nat.card J = 3 := by
    have h1 : Nat.card J ∣ orderOf y₀ := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hJy₀
    have h3 : Nat.card J ∣ 3 := h1.trans (orderOf_dvd_of_pow_eq_one hy₀3)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq J h) hJne
    · exact h
  have hO2J : CFSG.pCore 2 ↥J = ⊥ := by
    have h2 : IsPGroup 2 (CFSG.pCore 2 ↥J) := CFSG.pCore_isPGroup
    have h3 : IsPGroup 3 (⊤ : Subgroup ↥J) := (hJp.of_equiv Subgroup.topEquiv.symm)
    rw [eq_bot_iff]
    intro x hx
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) _ _ h2 h3).le_bot ⟨hx, Subgroup.mem_top _⟩
  have hcardJq : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) = 3 := by
    rw [hO2J, Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hJcard]
  have hconjT : ∀ y ∈ Y₀, ∀ x ∈ J, y * x * y⁻¹ ∈ TY := by
    intro y hy x hx
    obtain ⟨k, hk⟩ := hdecY y
    have hkY : (k : Y) ∈ Y₀ := by
      have : (k : Y) = y * ((k : Y)⁻¹ * y)⁻¹ := by group
      rw [this]
      exact Y₀.mul_mem hy (Y₀.inv_mem (hC hk))
    have hkN : k ∈ normalizer ((T : Subgroup ↥K) : Set ↥K) := by
      rw [← hY₀K]
      exact hkY
    obtain ⟨xK, hxK, rfl⟩ := hJT hx
    have hc : ((k : Y)⁻¹ * y) * xK * ((k : Y)⁻¹ * y)⁻¹ = xK := by
      have := mem_centralizer_iff.mp hk (xK : Y) xK.2
      rw [← this, mul_inv_cancel_right]
    have he : y * xK * y⁻¹ = ((k * xK * k⁻¹ : ↥K) : Y) := by
      calc y * xK * y⁻¹ = (k : Y) * (((k : Y)⁻¹ * y) * xK * ((k : Y)⁻¹ * y)⁻¹) * (k : Y)⁻¹ := by
            group
        _ = ((k * xK * k⁻¹ : ↥K) : Y) := by rw [hc]; simp
    change y * (xK : Y) * y⁻¹ ∈ TY
    rw [he]
    exact ⟨_, (mem_normalizer_iff.mp hkN xK).mp hxK, rfl⟩
  have hD'T : (⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) ≤ TY := iSup₂_le fun y hy => by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hconjT y hy x hx
  have hh : ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 2 := by
    have hd := hdir
    unfold SolvThreeDirectCond at hd
    rw [hcardJq] at hd
    have h9 : 3 ^ ((normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀).index ≤ 3 ^ 2 := by
      rw [← hd]
      calc _ ≤ Nat.card ↥(⨆ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom) :=
            Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
        _ ≤ Nat.card TY := Subgroup.card_le_of_le hD'T
        _ = 3 ^ 2 := by rw [hTYcard]; norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9
  set M := (normalizer (J : Set Y) ⊓ Y₀).subgroupOf Y₀ with hM
  obtain ⟨g, hg⟩ : ∃ g : Y, ∀ y ∈ Y₀, J.map (MulAut.conj y).toMonoidHom = J ∨
      J.map (MulAut.conj y).toMonoidHom = J.map (MulAut.conj g).toMonoidHom := by
    have hidx : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (show M.index = 1 ∨ M.index = 2 by omega) with h1 | h2
    · refine ⟨1, fun y hy => Or.inl ?_⟩
      have hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M := (Subgroup.index_eq_one.mp h1) ▸ Subgroup.mem_top _
      exact map_conj_eq_of_mem_normalizer (Subgroup.mem_subgroupOf.mp hyM).1
    · obtain ⟨g, hgM⟩ : ∃ g : ↥Y₀, g ∉ M := by
        by_contra h
        push Not at h
        have : M = ⊤ := eq_top_iff.mpr fun x _ => h x
        rw [this, Subgroup.index_top] at h2
        omega
      refine ⟨g, fun y hy => ?_⟩
      by_cases hyM : (⟨y, hy⟩ : ↥Y₀) ∈ M
      · exact Or.inl (map_conj_eq_of_mem_normalizer (Subgroup.mem_subgroupOf.mp hyM).1)
      · right
        have hgyM : g⁻¹ * ⟨y, hy⟩ ∈ M := by
          rw [Subgroup.mul_mem_iff_of_index_two h2, Subgroup.inv_mem_iff]
          exact iff_of_false hgM hyM
        have hN' : (g : Y)⁻¹ * y ∈ normalizer (J : Set Y) := by
          simpa using (Subgroup.mem_subgroupOf.mp hgyM).1
        calc J.map (MulAut.conj y).toMonoidHom
            = J.map (MulAut.conj ((g : Y) * ((g : Y)⁻¹ * y))).toMonoidHom := by
              rw [mul_inv_cancel_left]
          _ = (J.map (MulAut.conj ((g : Y)⁻¹ * y)).toMonoidHom).map
                (MulAut.conj (g : Y)).toMonoidHom := map_conj_mul J _ _
          _ = J.map (MulAut.conj (g : Y)).toMonoidHom := by
              rw [map_conj_eq_of_mem_normalizer hN']
  obtain ⟨j, hjJ, hj1⟩ : ∃ j ∈ J, j ≠ 1 := by
    by_contra h
    push Not at h
    exact hJne (eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx))
  obtain ⟨jK, hjK, rfl⟩ := hJT hjJ
  have hjK1 : jK ≠ 1 := fun h => hj1 (by rw [h]; rfl)
  have htrans := CFSG.AGLEmbedding.KFactProofs.SmallIdent.orbitTrans_m11 ⟨eK⟩ T
  have hcover : (TY : Set Y) ⊆ (J : Set Y) ∪ (J.map (MulAut.conj g).toMonoidHom : Set Y) := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases ht1 : t = 1
    · left
      rw [ht1]
      exact J.one_mem
    obtain ⟨n, hnN, hnt⟩ := htrans jK hjK hjK1 t ht ht1
    have htmem : (t : Y) ∈ J.map (MulAut.conj (n : Y)).toMonoidHom :=
      ⟨jK, hjJ, by rw [← hnt]; simp [MulAut.conj_apply]⟩
    rcases hg n (hNK n hnN) with h | h
    · left
      rw [h] at htmem
      exact htmem
    · right
      rw [h] at htmem
      exact htmem
  have h1 := Set.ncard_le_ncard hcover (Set.toFinite _)
  have h2 := Set.ncard_union_le (J : Set Y) (J.map (MulAut.conj g).toMonoidHom : Set Y)
  have h3 : (TY : Set Y).ncard = 9 := by rw [← Nat.card_coe_set_eq]; exact hTYcard
  have h4 : (J : Set Y).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hJcard
  have h5 : (J.map (MulAut.conj g).toMonoidHom : Set Y).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (J.map (MulAut.conj g).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hJcard]
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
