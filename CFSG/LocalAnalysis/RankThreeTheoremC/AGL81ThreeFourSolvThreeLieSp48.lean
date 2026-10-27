module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSp48
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsB
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48NSLoc
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin Subgroup
open CFSG.AGLEmbedding.KFactProofs.Sp48
open SolvNone

private theorem exists_cube_of_mem_spE_solvSp {s : Sp8} (hs : s ∈ spE) :
    ∃ x ∈ spT0, x ^ 3 = s := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_spE_iff s).1 hs
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hb
  have key : ∀ k : ℤ, (slA ^ k) ^ 3 = slZ ^ k := fun k => by
    rw [slZ, ← zpow_natCast (slA ^ k) 3, ← zpow_natCast slA 3, ← zpow_mul, ← zpow_mul, mul_comm]
  refine ⟨blkHom (slA ^ i, slA ^ j), ?_, ?_⟩
  · exact ⟨(slA ^ i, slA ^ j), ⟨zpow_mem (mem_zpowers slA) i, zpow_mem (mem_zpowers slA) j⟩, rfl⟩
  · rw [← map_pow, Prod.pow_mk, blkHom_apply, key, key]

theorem threeFourSolvThreeNoneAt_sp48 (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex)
    (hq2 : q.p = 2) (hq3 : q.exponent = 3) (hd : d.1 = .B 2 q) :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group := by
  have hdK : IsSpFourEightIndex d := ⟨q, hq2, hq3, hd⟩
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ _ _ hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    hcond _
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  by_contra hJC
  obtain ⟨eK⟩ := hKX
  obtain ⟨⟨eSp⟩, hcardK⟩ := exists_equiv_sp8 hdK eK
  have hcardS : Nat.card Sp8 = 3 ^ 4 * 13045760 := by
    rw [← hcardK]
    exact Nat.card_congr eSp.symm.toEquiv
  haveI hsimple : IsSimpleGroup Sp8 := isSimple_sp8_of_index hdK eK eSp
  haveI hKs : IsSimpleGroup ↥K := eSp.isSimpleGroup
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥K = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
    have h1 : Nat.card (⊤ : Subgroup ↥K) = Nat.card (⊥ : Subgroup ↥K) := by rw [← htop, hZ]
    rw [Subgroup.card_top, Subgroup.card_bot, hcardK] at h1
    norm_num at h1
  have hKY : ¬ K ≤ Y₀ := by
    haveI : Group.IsPerfect ↥K :=
      ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top ↥K hnab⟩
    exact hcomp K ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      CFSG.ComponentClassification.Quasisimple.simple_of_perfect ↥K⟩ le_rfl
  have hKC : K ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have h1 : (⟨g, hg.1⟩ : ↥K) ∈ center ↥K := Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (mem_centralizer_iff.mp hg.2 k k.2)
    rw [hZ, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨A₀, hA₀K, hA₀, hA₀c, -⟩ := Sp48Cfg.exists_spE (K := K) eSp
  have hSeitz : ∀ A : Subgroup Y, A ≤ K → IsElemAbelian 3 A → Nat.card A = 9 →
      (∀ a ∈ A, a ≠ 1 → ∀ k ∈ K, k * a = a * k → k ∈ Y₀) → False :=
    fun A hAK hA hAc hZ' => hKY (Sp48Cfg.le_of_centralizers eSp hAK hA hAc hZ')
  have hC3 : Nat.Coprime 3 (Nat.card C) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    obtain ⟨c', hc'⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hc : (c' : Y) ∈ C := c'.2
    have hc3 : orderOf (c' : Y) = 3 := by rw [orderOf_coe]; exact hc'
    set c : Y := (c' : Y) with hcdef
    have hcK : c ∉ K := fun h => by
      have h1 : c ∈ K ⊓ C := ⟨h, hc⟩
      rw [hKC, Subgroup.mem_bot] at h1
      rw [h1, orderOf_one] at hc3
      norm_num at hc3
    have hcomm : ∀ a ∈ A₀, ∀ b ∈ zpowers c, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
      exact (mem_centralizer_iff.1 (zpow_mem hc m)) a (hA₀K ha)
    obtain ⟨hzc, hzcard⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three hc3
    have hinf : A₀ ⊓ zpowers c = ⊥ := by
      rw [inf_comm]
      exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hc3 fun h => hcK (hA₀K h)
    obtain ⟨hB₀, hB₀c⟩ := Sp48Cfg.elemAbelian_sup hA₀ hzc hcomm hinf
    have hB₀p : IsPGroup 3 (A₀ ⊔ zpowers c : Subgroup Y) := fun x =>
      ⟨1, Subtype.ext (by simpa using hB₀.2 x x.2)⟩
    obtain ⟨Q', hQ'⟩ := hB₀p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y Q' R
    have hgT : ((A₀ ⊔ zpowers c : Subgroup Y)).map (MulAut.conj g).toMonoidHom ≤
        (R : Subgroup Y) := by
      have h1 : ((g • Q' : Sylow 3 Y) : Subgroup Y) =
          (Q' : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
      rw [hg] at h1
      rw [h1]
      exact map_mono hQ'
    set B : Subgroup Y := (A₀ ⊔ zpowers c).map (MulAut.conj g).toMonoidHom with hBdef
    set A : Subgroup Y := A₀.map (MulAut.conj g).toMonoidHom with hAdef
    set z : Y := g * c * g⁻¹ with hz
    have hBel : IsElemAbelian 3 B := IsElemAbelian.map hB₀ _
    have hBc : Nat.card B = 3 ^ 3 := by
      rw [hBdef, card_map_of_injective (MulAut.conj g).injective, hB₀c, hA₀c, hzcard]
      norm_num
    have hAB : A ≤ B := map_mono le_sup_left
    have hzB : z ∈ B := ⟨c, mem_sup_right (mem_zpowers c), rfl⟩
    have hAK : A ≤ K := by
      rintro _ ⟨a, ha, rfl⟩
      exact hKn.conj_mem a (hA₀K ha) g
    have hzC : z ∈ C := (inferInstance : C.Normal).conj_mem c hc g
    have hzK : z ∉ K := by
      intro h
      apply hcK
      have := hKn.conj_mem z h g⁻¹
      rwa [hz, show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this
    have hz3 : orderOf z = 3 := by
      rw [hz, show g * c * g⁻¹ = MulAut.conj g c from rfl, MulEquiv.orderOf_eq, hc3]
    have hA : IsElemAbelian 3 A := IsElemAbelian.map hA₀ _
    have hAc : Nat.card A = 9 := by
      rw [hAdef, card_map_of_injective (MulAut.conj g).injective, hA₀c]
    have h3T : 3 ≤ Open.pRank 3 (R : Subgroup Y) :=
      Sp48Cfg.le_pRank' (by norm_num) hgT hBel hBc
    have h3T' : 3 ≤ CFSG.pRank 3 (R : Subgroup Y) := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact h3T
    have hcoreW : GLBWeakCore 3 (R : Subgroup Y) ≤ Y₀ := by
      have h := hcore
      rw [if_pos h3T'] at h
      exact h
    refine hSeitz A hAK hA hAc fun a ha ha1 k hk hka => ?_
    have ha3 : orderOf a = 3 := orderOf_eq_prime (hA.2 a ha) ha1
    set W : Subgroup Y := zpowers a ⊔ zpowers z with hWdef
    have haz : ∀ x ∈ zpowers a, ∀ y ∈ zpowers z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
      exact (mem_centralizer_iff.1 (zpow_mem hzC n)) _ (zpow_mem (hAK ha) m)
    have hWinf : zpowers a ⊓ zpowers z = ⊥ := by
      rw [inf_comm]
      exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hz3 fun h =>
        hzK ((zpowers_le.2 (hAK ha)) h)
    obtain ⟨hWel, hWc⟩ := Sp48Cfg.elemAbelian_sup
      (Sp48Cfg.elemAbelian_zpowers Nat.prime_three ha3).1
      (Sp48Cfg.elemAbelian_zpowers Nat.prime_three hz3).1 haz hWinf
    have hWB : W ≤ B := sup_le (zpowers_le.2 (hAB ha)) (zpowers_le.2 hzB)
    have hW2 : 2 ≤ Open.pRank 3 W := Sp48Cfg.le_pRank' (by norm_num) le_rfl hWel (by
      rw [hWc, Nat.card_zpowers, Nat.card_zpowers, ha3, hz3]; norm_num)
    have hW3 : 3 ≤ Open.pRank 3 (W ⊔ ((R : Subgroup Y) ⊓ centralizer (W : Set Y))) := by
      refine Sp48Cfg.le_pRank' (by norm_num) ?_ hBel hBc
      intro b hb
      refine mem_sup_right ⟨hgT hb, mem_centralizer_iff.2 fun x hx => ?_⟩
      exact congrArg Subtype.val (hBel.1.1.comm ⟨x, hWB hx⟩ ⟨b, hb⟩)
    have hNW := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3
      (hWB.trans hgT) hW2 hW3
    refine hcoreW (hNW (centralizer_le_normalizer _ ?_))
    rw [mem_centralizer_iff]
    intro x hx
    have hk' : x ∈ centralizer ({k} : Set Y) := by
      have hle : W ≤ centralizer ({k} : Set Y) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 hka.symm
        · exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hzC) k hk).symm
      exact hle hx
    exact mem_centralizer_singleton_iff.1 hk'
  set θ : Y →* MulAut ↥K := MulAut.conjNormal with hθ
  haveI : Finite (MulAut ↥K) := MulEquiv.finite_left
  set π : Y →* θ.range := θ.rangeRestrict with hπdef
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective θ
  have hπker : π.ker = C := ker_rangeRestrict_conjNormal K
  have hker' : Nat.Coprime 3 (Nat.card π.ker) := by rw [hπker]; exact hC3
  set K' : Subgroup θ.range := K.map π with hK'def
  haveI hK'n : K'.Normal := Subgroup.Normal.map hKn π hπ
  obtain ⟨fK⟩ := nonempty_mulEquiv_map_rangeRestrict_conjNormal hZ
  set eSp' : ↥K' ≃* Sp8 := fK.trans eSp with heSp'
  have hC' : centralizer (K' : Set θ.range) = ⊥ :=
    centralizer_map_rangeRestrict_conjNormal_eq_bot hZ
  set R' : Sylow 3 θ.range := R.mapSurjective hπ with hR'def
  have hR'eq : (R' : Subgroup θ.range) = (R : Subgroup Y).map π := Sylow.coe_mapSurjective _ _
  have hcore' := map_threeFourCore_le hπ hker' R hER hcore
  rw [← hR'eq] at hcore'
  have hK'Y : ¬ K' ≤ Y₀.map π := by
    intro h
    apply hKY
    intro k hk
    obtain ⟨y, hy, hyk⟩ := h ⟨k, hk, rfl⟩
    have h2 : y⁻¹ * k ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyk, inv_mul_cancel]
    rw [hπker] at h2
    have h3 := Y₀.mul_mem hy (hC h2)
    rwa [mul_inv_cancel_left] at h3
  have hne : Y₀.map π ≠ ⊤ := fun h => hK'Y (h ▸ le_top)
  have hE'R : E.map π ≤ (R' : Subgroup θ.range) := by rw [hR'eq]; exact Subgroup.map_mono hER
  have hE' : IsElemAbelian 3 (E.map π) := hE.map π
  have hE'c : Nat.card (E.map π) = 9 := by
    have hinj : Function.Injective (π.comp E.subtype) := by
      refine (injective_iff_map_eq_one _).mpr fun x hx => Subtype.ext ?_
      exact eq_one_of_isPGroup_of_coprime hker' hE.isPGroup _ x.2 hx
    have h1 : E.map π = (π.comp E.subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hEc]
    norm_num
  obtain ⟨A₁, hA₁K, hA₁, hA₁c, hA₁s⟩ := Sp48Cfg.exists_spE (K := K') eSp'
  have h3R' : 3 ≤ CFSG.pRank 3 (R' : Subgroup θ.range) := by
    by_contra hlt
    have hcore1 := hcore'
    rw [if_neg hlt] at hcore1
    have hlt' : ¬ 3 ≤ Open.pRank 3 (R' : Subgroup θ.range) := by
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hlt
    have hEK : E.map π ≤ K' := by
      intro e he
      by_contra heK
      have he3 : e ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hE'.2 e he
      obtain ⟨φ, hφ, hφ3, hφK⟩ := exists_frob (eK := eSp') hC' heK he3
      have hφc : ∀ a ∈ A₁, ∀ b ∈ zpowers φ, a * b = b * a := by
        intro a ha b hb
        obtain ⟨s, hs, rfl⟩ := hA₁s a ha
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
        have h1 : φ * ((eSp'.symm s : ↥K') : θ.range) * φ⁻¹ = ((eSp'.symm s : ↥K') : θ.range) := by
          rw [← coe_symm_adHom, hφ, (fr_eq_self_iff_mem_spE (spE_le_spT0 hs)).2 hs]
        have h2 : Commute φ ((eSp'.symm s : ↥K') : θ.range) := by
          rw [commute_iff_eq]
          calc φ * ((eSp'.symm s : ↥K') : θ.range) =
              φ * ((eSp'.symm s : ↥K') : θ.range) * φ⁻¹ * φ := by group
            _ = ((eSp'.symm s : ↥K') : θ.range) * φ := by rw [h1]
        exact ((h2.zpow_left m).eq).symm
      have hφ1 : φ ≠ 1 := fun h => hφK (h ▸ one_mem _)
      have hφo : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
      obtain ⟨hzφ, hzφc⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three hφo
      have hinf : A₁ ⊓ zpowers φ = ⊥ := by
        rw [inf_comm]
        exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hφo fun h => hφK (hA₁K h)
      obtain ⟨hB, hBc⟩ := Sp48Cfg.elemAbelian_sup hA₁ hzφ hφc hinf
      have h3top : 3 ≤ Open.pRank 3 (⊤ : Subgroup θ.range) :=
        Sp48Cfg.le_pRank' (by norm_num) le_top hB (by rw [hBc, hA₁c, hzφc]; norm_num)
      rw [← (CFSG.SectionRank.pRank_sylow R').1] at h3top
      exact hlt' h3top
    apply hK'Y
    refine Sp48Cfg.le_of_centralizers eSp' hEK hE' hE'c fun e he he1 k hk hke => hcore1 ?_
    have he3 : orderOf e = 3 := orderOf_eq_prime (hE'.2 e he) he1
    obtain ⟨hze, hzec⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three he3
    have hN : normalizer (zpowers e : Set θ.range) ≤ GLBCore 3 1 (E.map π) :=
      le_sSup ⟨zpowers e, zpowers_le.2 he,
        Sp48Cfg.le_pRank' (by norm_num) le_rfl hze (by rw [hzec, pow_one]), rfl⟩
    refine hN (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute e k from hke.symm) m).eq)
  have h3R'o : 3 ≤ Open.pRank 3 (R' : Subgroup θ.range) := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3R'
  have hcoreW : GLBWeakCore 3 (R' : Subgroup θ.range) ≤ Y₀.map π := by
    have h := hcore'
    rw [if_pos h3R'] at h
    exact h
  have hJ'ne : J.map π ≠ ⊥ := by
    intro h
    apply hJC
    intro x hx
    have h1 : π x ∈ J.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot, ← MonoidHom.mem_ker, hπker] at h1
    exact h1
  have hcube : ∀ x ∈ J, x ^ 3 ∈ C := cube_mem_of_pCoreOf_le σ hσs hO2 hb
  have hJ'3 : ∀ y ∈ J.map π, y ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, ← MonoidHom.mem_ker, hπker]
    exact hcube x hx
  have hJ'p : IsPGroup 3 (J.map π) := fun y => ⟨1, Subtype.ext (by simpa using hJ'3 y y.2)⟩
  have hJ'sub : IsSubnormal (J.map π) (Y₀.map π) := (isSubnormal_oUpperTwo_map σ hσs).map π
  have hJ'O : J.map π ≤ pCoreOf 3 (Y₀.map π) :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hJ'sub hJ'p
  by_cases hsolv : Group.IsSolvable ↥(Y₀.map π)
  swap
  ·
    obtain ⟨A₂, V₀, hI⟩ := kFactSp48NonsolvLocal θ.range K' d hdK hK'n ⟨fK.trans eK⟩ hC' R'
      (Y₀.map π) h3R'o hcoreW hne hsolv
    have hWY : pCoreOf 3 (Y₀.map π) ≤ Y₀.map π := Subgroup.map_subtype_le _
    have hWn : Y₀.map π ≤ normalizer (pCoreOf 3 (Y₀.map π) : Set θ.range) :=
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 3 _
    rcases hI.minimal _ hWY hWn with h | h
    · exact hJ'ne (le_bot_iff.mp (h ▸ hJ'O))
    · haveI : Group.IsNilpotent ↥(pCoreOf 3 (Y₀.map π)) :=
        (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 3 _).isNilpotent
      have hV : V₀ = ⊥ := CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le h inferInstance
        hI.V_perfect
      have hTK := hI.TK_le_V
      rw [hV, le_bot_iff] at hTK
      have hc := hI.card_TK
      rw [hTK, Subgroup.card_bot] at hc
      norm_num at hc
  obtain ⟨e', y, S⟩ := exists_setup K' eSp' hC' hcardS R' h3R'o
  have hNE := S.normalizer_E_le h3R'o hcoreW
  have hR'Y₀ : (R' : Subgroup θ.range) ≤ Y₀.map π := S.T_le_Y₀ hNE
  obtain ⟨θ', hθT, -, hcl⟩ := classify_comap (e := e') hcardS hsimple hNE hne
  have hcl' : (Y₀.map π).comap (emb e') = wrp slD := by
    rcases hcl with h | h | h
    · exact h
    · exfalso
      have h2 : (Y₀.map π).comap (emb e') =
          (wrp (⊤ : Subgroup Sl28)).map (MulEquiv.refl Sp8).toMonoidHom := by
        rw [h]
        ext x
        simp
      have hV := Vzero_le_Y₀ h2
      have hTK := S.TK_le_Vzero (ψ := MulEquiv.refl Sp8) (fun x => Iff.rfl)
      have hVb := CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le hV hsolv
        (Vzero_perfect (e := e') (ψ := MulEquiv.refl Sp8))
      rw [hVb, le_bot_iff] at hTK
      have hc := S.card_inf_K
      rw [hTK, Subgroup.card_bot] at hc
      norm_num at hc
    · exfalso
      have hV := Vzero_le_Y₀ h
      have hTK := S.TK_le_Vzero hθT
      have hVb := CFSG.AGLEmbedding.eq_bot_of_commutator_eq_self_of_le hV hsolv
        (Vzero_perfect (e := e') (ψ := θ'))
      rw [hVb, le_bot_iff] at hTK
      have hc := S.card_inf_K
      rw [hTK, Subgroup.card_bot] at hc
      norm_num at hc
  have hKN : ∀ x ∈ Y₀.map π, x ∈ K' →
      x ∈ normalizer ((R' : Subgroup θ.range) : Set θ.range) := by
    intro x hxY hxK
    obtain ⟨n, rfl⟩ := exists_emb e' hxK
    have hn : n ∈ wrp slD := by rw [← hcl']; exact hxY
    exact S.emb_mem_normalizer_T hn
  have hidx6 : K'.index ≤ 6 := index_le_six (eK := e') hC'
  set P : Sylow 3 (θ.range ⧸ K') := R'.mapSurjective (QuotientGroup.mk'_surjective K') with hP
  have hPeq : (P : Subgroup (θ.range ⧸ K')) =
      (R' : Subgroup θ.range).map (QuotientGroup.mk' K') := Sylow.coe_mapSurjective _ _
  have hPn : (P : Subgroup (θ.range ⧸ K')).Normal := by
    have hy1 : QuotientGroup.mk' K' y ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact S.not_mem
    have hyP : QuotientGroup.mk' K' y ∈ (P : Subgroup (θ.range ⧸ K')) := by
      rw [hPeq]
      exact Subgroup.mem_map_of_mem _ S.y_mem
    have hne' : (P : Subgroup (θ.range ⧸ K')) ≠ ⊥ := fun h => hy1 (by
      rw [h, Subgroup.mem_bot] at hyP
      exact hyP)
    have h3 : 3 ≤ Nat.card (P : Subgroup (θ.range ⧸ K')) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rw [hk]
      rcases k with _ | k
      · exfalso
        rw [pow_zero] at hk
        exact hne' (Subgroup.eq_bot_of_card_eq _ hk)
      · calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hmul := (P : Subgroup (θ.range ⧸ K')).card_mul_index
    have hcardQ : Nat.card (θ.range ⧸ K') = K'.index := rfl
    have hidx0 : (P : Subgroup (θ.range ⧸ K')).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidxP : (P : Subgroup (θ.range ⧸ K')).index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have h4 := Nat.mul_le_mul h3 hlt
      omega
    rcases (show (P : Subgroup (θ.range ⧸ K')).index = 1 ∨
        (P : Subgroup (θ.range ⧸ K')).index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have h3el : ∀ x ∈ Y₀.map π, (∃ k : ℕ, x ^ 3 ^ k = 1) → x ∈ (R' : Subgroup θ.range) := by
    rintro x hx ⟨k, hk⟩
    have hx' : QuotientGroup.mk' K' x ∈ (P : Subgroup (θ.range ⧸ K')) := by
      refine mem_of_mem_normalizer_of_pow_eq_one P ?_ (by rw [← map_pow, hk, map_one])
      rw [normalizer_eq_top_iff.mpr hPn]
      exact mem_top _
    rw [hPeq] at hx'
    obtain ⟨r, hr, hrx⟩ := hx'
    have hrx' : r⁻¹ * x ∈ K' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hrx
      exact QuotientGroup.eq.mp hrx
    have hrxY : r⁻¹ * x ∈ Y₀.map π := (Y₀.map π).mul_mem ((Y₀.map π).inv_mem (hR'Y₀ hr)) hx
    have hxN : x ∈ normalizer ((R' : Subgroup θ.range) : Set θ.range) := by
      have he : x = r * (r⁻¹ * x) := by group
      rw [he]
      exact (normalizer _).mul_mem (le_normalizer hr) (hKN _ hrxY hrx')
    exact mem_of_mem_normalizer_of_pow_eq_one R' hxN hk
  have hY₀N : Y₀.map π ≤ normalizer ((R' : Subgroup θ.range) : Set θ.range) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    obtain ⟨m, hm⟩ := R'.isPGroup' ⟨r, hr⟩
    have hm' : r ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
    refine h3el _ ((Y₀.map π).mul_mem ((Y₀.map π).mul_mem hg (hR'Y₀ hr)) ((Y₀.map π).inv_mem hg))
      ⟨m, ?_⟩
    rw [conj_pow, hm', mul_one, mul_inv_cancel]
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  have hkerσ : (π.comp σ).ker ≤ CFSG.pCore 2 I₀ := by
    rw [← MonoidHom.comap_ker, hπker]
    exact comap_le_pCore_two_of_coprime σ hb hC3 hker
  have hN3 : ∀ y' ∈ Y₀, (∃ k : ℕ, y' ^ 3 ^ k = 1) → π y' ∈ (R' : Subgroup θ.range) := by
    rintro y' hy' ⟨k, hk⟩
    exact h3el (π y') ⟨y', hy', rfl⟩ ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨f⟩ := symThree_of_autCond σ hσY hY₀N R'.isPGroup' hN3 hkerσ hcond
  set σ' : I₀ →* θ.range := π.comp σ with hσ'
  have hD'eq : σ'.range = σ.range.map π := MonoidHom.range_comp π σ
  have hD's : IsSubnormal σ'.range (Y₀.map π) := by rw [hD'eq]; exact hσs.map π
  have hD'Y₀ : σ'.range ≤ Y₀.map π := by rw [hD'eq]; exact Subgroup.map_mono hσY
  have hσ'O2 : (CFSG.pCore 2 I₀).map σ' ≤ zpowers 1 := by
    rintro _ ⟨i, hi, rfl⟩
    have h1 : σ i ∈ π.ker := by rw [hπker]; exact hσC ⟨i, hi, rfl⟩
    rw [MonoidHom.mem_ker] at h1
    change π (σ i) ∈ zpowers 1
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨y₀, hy₀J, hy₀1⟩ : ∃ y₀ ∈ J.map π, y₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hJ'ne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx))
  have hy₀3 : y₀ ^ 3 = 1 := hJ'3 y₀ hy₀J
  have hy₀o : Odd (orderOf y₀) := Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy₀3)
  have hy₀D : y₀ ∈ σ'.range := by
    obtain ⟨x, hx, rfl⟩ := hy₀J
    obtain ⟨i, -, rfl⟩ := hx
    exact MonoidHom.mem_range.mpr ⟨i, rfl⟩
  have hW : ∀ v ∈ σ'.range, (∃ k : ℕ, v ^ 3 ^ k = 1) → v ∈ zpowers y₀ := by
    rintro v hv ⟨k, hk⟩
    have hσ'C : (CFSG.pCore 2 I₀).map σ' ≤ zpowers y₀ :=
      hσ'O2.trans (zpowers_le.mpr (Subgroup.one_mem _))
    exact mem_of_odd_of_symThree σ' f hσ'C hy₀D hy₀o (mem_zpowers y₀) hy₀1 hv
      (Odd.of_dvd_nat (Odd.pow (by decide)) (orderOf_dvd_of_pow_eq_one hk))
  have hcardW : Nat.card (zpowers y₀) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy₀3)
  obtain ⟨t, htD, ht2, ht1⟩ : ∃ t ∈ σ'.range, t ^ 2 = 1 ∧ t ≠ 1 := by
    have h2 : ∃ i : I₀, (∃ k : ℕ, i ^ 2 ^ k = 1) ∧ σ' i ≠ 1 := by
      by_contra h
      push Not at h
      apply hy₀1
      have hle : σ'.range ≤ ⊥ := by
        rw [MonoidHom.range_eq_map σ', ← closure_twoElements_eq_top hb, MonoidHom.map_closure,
          Subgroup.closure_le]
        rintro _ ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_bot]
        exact h i hi
      exact Subgroup.mem_bot.mp (hle hy₀D)
    obtain ⟨i, ⟨k, hk⟩, hi1⟩ := h2
    have hx : (σ' i) ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hi1 hj
    refine ⟨(σ' i) ^ 2 ^ (j - 1), σ'.range.pow_mem (MonoidHom.mem_range.mpr ⟨i, rfl⟩) _, ?_, ?_⟩
    · rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0), ← hj,
        pow_orderOf_eq_one]
    · refine pow_ne_one_of_lt_orderOf (by positivity) ?_
      rw [hj]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have htN : t ∈ normalizer ((R' : Subgroup θ.range) : Set θ.range) := hY₀N (hD'Y₀ htD)
  have hidx : (centralizer ({t} : Set θ.range)).relIndex (R' : Subgroup θ.range) ≤ 3 := by
    have h1 := relIndex_centralizer_le_of_isSubnormal hD's hR'Y₀ R'.isPGroup' htD ht2 htN hW
    rw [inf_comm, Subgroup.inf_relIndex_right] at h1
    exact h1.trans hcardW
  have hidx0 : (centralizer ({t} : Set θ.range)).relIndex (R' : Subgroup θ.range) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  set T₀ : Subgroup θ.range := spT0.map (emb e') with hT₀
  have hT₀R : T₀ ≤ (R' : Subgroup θ.range) := by
    rintro _ ⟨k, hk, rfl⟩
    exact S.emb_mem_T hk
  have hT₀c : Nat.card T₀ = 3 ^ 4 := by
    rw [hT₀, Subgroup.card_map_of_injective (emb_injective e'), card_spT0]
    norm_num
  have hM : (centralizer ({t} : Set θ.range)).relIndex T₀ ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hT₀R hidx0).trans hidx
  have hcube3 : ∀ x ∈ T₀, x ^ 3 ∈ centralizer ({t} : Set θ.range) := by
    intro x hx
    set M : Subgroup ↥T₀ := (centralizer ({t} : Set θ.range)).subgroupOf T₀ with hMdef
    have hMi : M.index ≤ 3 := hM
    haveI hMn : M.Normal := ⟨fun n hn g => by
      have hc : (g : θ.range) * n = n * g := by
        obtain ⟨a, ha, hga⟩ := g.2
        obtain ⟨b, hb, hnb⟩ := n.2
        rw [← hga, ← hnb, ← map_mul, ← map_mul, comm_spT0 a ha b hb]
      have he : g * n * g⁻¹ = n := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hc, mul_inv_cancel_right])
      rw [he]
      exact hn⟩
    have hMdvd : M.index ∣ 3 ^ 4 := by rw [← hT₀c]; exact Subgroup.index_dvd_card M
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hMdvd
    have hpow := M.pow_index_mem ⟨x, hx⟩
    rw [hj] at hpow hMi
    have hj1 : j ≤ 1 := by
      by_contra h
      push Not at h
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases j
    · have h1 := Subgroup.mem_subgroupOf.mp hpow
      simp only [pow_zero, pow_one] at h1
      exact (centralizer _).pow_mem h1 3
    · have h1 := Subgroup.mem_subgroupOf.mp hpow
      simpa using h1
  have hE3 : ∀ z ∈ spE.map (emb e'), t * z = z * t := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨x, hx, hxs⟩ := exists_cube_of_mem_spE_solvSp hs
    have h1 := hcube3 (emb e' x) ⟨x, hx, rfl⟩
    rw [← map_pow, hxs] at h1
    exact (mem_centralizer_singleton_iff.mp h1).symm
  have htR := S.cent_E_le hC' hE3
  obtain ⟨n, hn⟩ := R'.isPGroup' ⟨t, htR⟩
  have hn' : t ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact ht1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one ht2)
    (orderOf_dvd_of_pow_eq_one hn')))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
