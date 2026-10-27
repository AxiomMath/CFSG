module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsB
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsSU
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsAut
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeToolsGen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeAltSix
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesJ3
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.Sporadic.J3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 (centralizer_eq_sylow_j3)
open SolvNone


theorem threeFourSolvThreeNoneAt_j3 :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.sporadic .J3).Group := by
  intro Y _ _ K Y₀ E R I₀ _ _ σ hKn hKX hZ hrk _ hC hcomp hER hE hEc hcore hO2 hker hσY hσs hb
    hcond _
  classical
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (K : Set Y) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  set J := (CFSG.ComponentClassification.AS76b.oUpperTwo (⊤ : Subgroup I₀)).map σ with hJdef
  by_contra hJC
  have hOR := kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨e⟩ := hKX
  obtain ⟨β⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI hKs : IsSimpleGroup ↥K :=
    MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) (e.trans β.symm)
  have hcardK : Nat.card ↥K = 50232960 := by
    rw [Nat.card_congr (e.trans β.symm).toEquiv]
    exact CFSG.Sporadic.J3.card_J3
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
  obtain ⟨hOut2, hrK⟩ := hOR ↥K ⟨e⟩
  obtain ⟨A₀, -, hA₀, hA₀c⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (⊤ : Subgroup ↥K)
  rw [hrK] at hA₀c
  set A : Subgroup Y := A₀.map K.subtype with hAdef
  have hAK : A ≤ K := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hA : IsElemAbelian 3 A := hA₀.map K.subtype
  have hAc : Nat.card A = 3 ^ 3 := by
    rw [hAdef, Subgroup.card_map_of_injective K.subtype_injective, hA₀c]
  have hC3 : Nat.Coprime 3 (Nat.card C) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hc3' : c ^ 3 = 1 := hc ▸ pow_orderOf_eq_one c
    have hc3 : (c : Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hc3'
    have h1 := eq_one_of_mem_centralizer_of_elemAbelian_card hrk hAK hA hAc hKC c.2 hc3
    have h2 : c = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at hc
    norm_num at hc
  set θ : Y →* MulAut ↥K := MulAut.conjNormal with hθ
  haveI : Finite (MulAut ↥K) := MulEquiv.finite_left
  set π : Y →* θ.range := θ.rangeRestrict with hπdef
  have hπ : Function.Surjective π := MonoidHom.rangeRestrict_surjective θ
  have hπker : π.ker = C := ker_rangeRestrict_conjNormal K
  have hker' : Nat.Coprime 3 (Nat.card π.ker) := by rw [hπker]; exact hC3
  set K' : Subgroup θ.range := K.map π with hK'def
  haveI hK'n : K'.Normal := Subgroup.Normal.map hKn π hπ
  have hK'X : Nonempty (↥K' ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) := by
    obtain ⟨f⟩ := nonempty_mulEquiv_map_rangeRestrict_conjNormal hZ
    exact ⟨f.trans e⟩
  have hC' : centralizer (K' : Set θ.range) = ⊥ :=
    centralizer_map_rangeRestrict_conjNormal_eq_bot hZ
  have hπK : Function.Injective (π.comp K.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun k hk => ?_
    have h1 : (k : Y) ∈ K ⊓ C := ⟨k.2, by rw [← hπker]; exact hk⟩
    rw [hKC, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  set R' : Sylow 3 θ.range := R.mapSurjective hπ with hR'def
  have hR'eq : (R' : Subgroup θ.range) = (R : Subgroup Y).map π := Sylow.coe_mapSurjective _ _
  have hNR : normalizer ((R : Subgroup Y) : Set Y) ≤ Y₀ :=
    (normalizer_sylow_le_threeFourCore Nat.prime_three R hER hE hEc).trans hcore
  have hNR' : normalizer ((R' : Subgroup θ.range) : Set θ.range) ≤ Y₀.map π := by
    rw [hR'eq, ← map_normalizer_eq_of_coprime hπ hker' R.isPGroup']
    exact Subgroup.map_mono hNR
  have hne : Y₀.map π ≠ ⊤ := by
    intro htop
    apply hKY
    intro k hk
    have h1 : π k ∈ Y₀.map π := htop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyk⟩ := h1
    have h2 : y⁻¹ * k ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyk, inv_mul_cancel]
    rw [hπker] at h2
    have h3 := Y₀.mul_mem hy (hC h2)
    rwa [mul_inv_cancel_left] at h3
  have hIS := j3InSitu_of kFactJ3Sylow kFactJ3OuterInvolution hOR hK'n hK'X hC' R' hNR' hne
  have hR'Y₀ : (R' : Subgroup θ.range) ≤ Y₀.map π :=
    Subgroup.le_normalizer.trans hNR'
  haveI : Finite (MulAut ↥K') := MulEquiv.finite_left
  have hOut3 : ¬ 3 ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K') :=
    fun hd => by
      have h1 := Nat.le_of_dvd Nat.card_pos hd
      have h2 := (hOR ↥K' hK'X).1
      omega
  have hR'K' : (R' : Subgroup θ.range) ≤ K' := by
    intro x hx
    obtain ⟨n, hn⟩ := R'.isPGroup' ⟨x, hx⟩
    have hx' : x ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h1 := mem_sup_centralizer_of_pow Nat.prime_three hOut3 hx'
    rwa [hC', sup_bot_eq] at h1
  have hσC : (CFSG.pCore 2 I₀).map σ ≤ C := (map_pCore_two_le_pCoreOf σ hσs).trans hO2
  have hkerσ : (π.comp σ).ker ≤ CFSG.pCore 2 I₀ := by
    rw [← MonoidHom.comap_ker, hπker]
    exact comap_le_pCore_two_of_coprime σ hb hC3 hker
  have hN3 : ∀ y ∈ Y₀, (∃ k : ℕ, y ^ 3 ^ k = 1) → π y ∈ (R' : Subgroup θ.range) := by
    rintro y hy ⟨k, hk⟩
    exact mem_of_mem_normalizer_of_pow_eq_one R' (hIS.le_normalizer ⟨y, hy, rfl⟩)
      (by rw [← map_pow, hk, map_one])
  obtain ⟨f⟩ := symThree_of_autCond σ hσY hIS.le_normalizer R'.isPGroup' hN3 hkerσ hcond
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
    apply hJC
    intro x hx
    have h1 : π x = 1 := h _ ⟨x, hx, rfl⟩
    rw [← MonoidHom.mem_ker, hπker] at h1
    exact h1
  have hcube : ∀ x ∈ J, x ^ 3 ∈ C := cube_mem_of_pCoreOf_le σ hσs hO2 hb
  have hy₀3 : y₀ ^ 3 = 1 := by
    obtain ⟨x, hx, rfl⟩ := hy₀J
    rw [← map_pow, ← MonoidHom.mem_ker, hπker]
    exact hcube x hx
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
  have htN : t ∈ normalizer ((R' : Subgroup θ.range) : Set θ.range) :=
    hIS.le_normalizer (hD'Y₀ htD)
  have hidx : (centralizer ({t} : Set θ.range)).relIndex (R' : Subgroup θ.range) ≤ 3 := by
    have h1 := relIndex_centralizer_le_of_isSubnormal hD's hR'Y₀ R'.isPGroup' htD ht2 htN hW
    rw [inf_comm, Subgroup.inf_relIndex_right] at h1
    exact h1.trans hcardW
  have hidx0 : (centralizer ({t} : Set θ.range)).relIndex (R' : Subgroup θ.range) ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  have hcardC : ∀ L : Subgroup θ.range, L ≤ R' →
      Nat.card L ≤ 3 * Nat.card (centralizer ({t} : Set θ.range) ⊓ L : Subgroup θ.range) := by
    intro L hL
    have h1 := Subgroup.relIndex_le_of_le_right hL hidx0
    have h2 := (centralizer ({t} : Set θ.range)).relIndex_mul_card L
    calc Nat.card L = _ := h2.symm
      _ ≤ 3 * Nat.card (centralizer ({t} : Set θ.range) ⊓ L : Subgroup θ.range) :=
          Nat.mul_le_mul_right _ (h1.trans hidx)
  by_cases htK : t ∈ K'
  ·
    set T'' : Sylow 3 ↥K' := R'.subtype hR'K' with hT''
    have hF := kFactJ3Sylow ↥K' hK'X T''
    have hZmap : (centerOf (T'' : Subgroup ↥K')).map K'.subtype =
        centerOf (R' : Subgroup θ.range) := by
      rw [hT'', Sylow.coe_subtype, map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hR'K']
    have hZc : Nat.card (centerOf (R' : Subgroup θ.range)) = 9 := by
      rw [← hZmap, Subgroup.card_map_of_injective K'.subtype_injective]
      exact hF.center_elem.2
    have hZR : centerOf (R' : Subgroup θ.range) ≤ R' := inf_le_left
    have h3 := hcardC _ hZR
    rw [hZc] at h3
    obtain ⟨b, ⟨hbC, hbZ⟩, hb1⟩ : ∃ b ∈ centralizer ({t} : Set θ.range) ⊓
        centerOf (R' : Subgroup θ.range), b ≠ 1 := by
      by_contra h
      push Not at h
      have h4 : centralizer ({t} : Set θ.range) ⊓ centerOf (R' : Subgroup θ.range) = ⊥ :=
        eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (h x hx)
      rw [h4, Subgroup.card_bot] at h3
      omega
    have hbZ' : b ∈ (R' : Subgroup θ.range) ⊓ centralizer ((R' : Subgroup θ.range) : Set θ.range) :=
      hbZ
    set b'' : ↥K' := ⟨b, hR'K' hbZ'.1⟩ with hb''
    have hb''Z : b'' ∈ centerOf (T'' : Subgroup ↥K') := by
      have h1 : b ∈ (centerOf (T'' : Subgroup ↥K')).map K'.subtype := hZmap ▸ hbZ
      obtain ⟨c, hc, hcb⟩ := h1
      have hcb' : c = b'' := Subtype.ext hcb
      rw [← hcb']
      exact hc
    have hb3 : b'' ^ 3 = 1 := hF.center_elem.1.2 b'' hb''Z
    have hb''1 : b'' ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
    have hbord : orderOf b'' = 3 := orderOf_eq_prime hb3 hb''1
    have hTb : (T'' : Subgroup ↥K') ≤ centralizer {b''} := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hxR : (x : θ.range) ∈ (R' : Subgroup θ.range) := by
        rw [hT'', Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hx
        exact hx
      exact mem_centralizer_iff.mp hbZ'.2 _ hxR
    have hcent := centralizer_eq_sylow_j3 hK'X T'' hbord hTb
    have ht' : (⟨t, htK⟩ : ↥K') ∈ centralizer {b''} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp hbC).symm
    rw [hcent, hT'', Sylow.coe_subtype, Subgroup.mem_subgroupOf] at ht'
    obtain ⟨n, hn⟩ := R'.isPGroup' ⟨t, ht'⟩
    have hn' : t ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    apply ht1
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one ht2)
      (orderOf_dvd_of_pow_eq_one hn'))
  ·
    set α : MulAut ↥K' := MulAut.conjNormal t with hα
    have hα2 : α ^ 2 = 1 := by rw [hα, ← map_pow, ht2, map_one]
    have hαout : α ∉ (MulAut.conj : ↥K' →* MulAut ↥K').range := by
      rintro ⟨k, hk⟩
      have h1 := inv_mul_mem_centralizer_of_conjNormal_eq hk.symm
      rw [hC', Subgroup.mem_bot, inv_mul_eq_one] at h1
      exact htK (h1 ▸ k.2)
    set A' : Subgroup θ.range := A.map π with hA'def
    have hA'K : A' ≤ K' := Subgroup.map_mono hAK
    have hA' : IsElemAbelian 3 A' := hA.map π
    have hA'c : Nat.card A' = 3 ^ 3 := by
      rw [hA'def, hAdef, Subgroup.map_map, Subgroup.card_map_of_injective hπK, hA₀c]
    obtain ⟨P, hP⟩ := hA'.isPGroup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq θ.range P R'
    set A'' : Subgroup θ.range := A'.map (MulAut.conj g).toMonoidHom with hA''def
    have hA''R : A'' ≤ R' := by
      have h1 : ((g • P : Sylow 3 θ.range) : Subgroup θ.range) =
          (P : Subgroup θ.range).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul]
        rfl
      rw [← hg, h1]
      exact Subgroup.map_mono hP
    have hA''K : A'' ≤ K' := by
      rintro _ ⟨a, ha, rfl⟩
      exact hK'n.conj_mem a (hA'K ha) g
    have hA''e : IsElemAbelian 3 A'' := hA'.map _
    have hA''c : Nat.card A'' = 3 ^ 3 := by
      rw [hA''def, Subgroup.card_map_of_injective (MulAut.conj g).injective, hA'c]
    have h9 : 3 ^ 2 ∣ Nat.card (centralizer ({t} : Set θ.range) ⊓ A'' : Subgroup θ.range) := by
      have h1 := hcardC A'' hA''R
      rw [hA''c] at h1
      have h2 : Nat.card (centralizer ({t} : Set θ.range) ⊓ A'' : Subgroup θ.range) ∣ 3 ^ 3 := by
        rw [← hA''c]
        exact Subgroup.card_dvd_of_le inf_le_right
      obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
      rw [hj'] at h1 ⊢
      apply pow_dvd_pow
      by_contra hlt
      push Not at hlt
      interval_cases j <;> norm_num at h1
    obtain ⟨E₉, hE₉c, -, hE₉le⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three
      (H := ⊥) (by rw [Subgroup.card_bot]; exact one_dvd _) h9 bot_le
    have hE₉ : IsElemAbelian 3 E₉ := hA''e.mono (hE₉le.trans inf_le_right)
    have hE₉K : E₉ ≤ K' := (hE₉le.trans inf_le_right).trans hA''K
    have hE₉Kc : Nat.card (E₉.subgroupOf K') = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₉K).toEquiv, hE₉c]
      norm_num
    obtain ⟨x, hx, hxα⟩ := kFactJ3OuterInvolution ↥K' hK'X α hα2 hαout (E₉.subgroupOf K')
      (hE₉.subgroupOf K') hE₉Kc
    apply hxα
    apply Subtype.ext
    have hxC : (x : θ.range) ∈ centralizer ({t} : Set θ.range) :=
      (hE₉le (Subgroup.mem_subgroupOf.mp hx)).1
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC
    rw [hα, MulAut.conjNormal_apply, ← hxC, mul_inv_cancel_right]

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
