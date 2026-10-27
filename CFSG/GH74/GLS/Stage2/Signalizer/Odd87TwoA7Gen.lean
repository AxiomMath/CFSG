module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7BDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Alt7
public import CFSG.GH74.GLS.AssemblyComponents
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87TwoA7Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.ComponentClassification Subgroup CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem le_of_open_isSubnormal' {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : A ≤ B :=
  h.le

theorem subgroupOf_isSubnormal_of_open' {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem isQuasisimple_of_open' {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hc, hs⟩ := h
  have hperf : Group.IsPerfect Q := ⟨hc⟩
  refine ⟨hperf, hs, ?_⟩
  by_contra hne
  push Not at hne
  have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := hne
  have hbot : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact (hcomm b a)
  have htop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (Subgroup.center Q))) hc
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
    rw [_root_.commutator_def]
    exact h2
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hs.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  have hx' : x ∈ commutator (Q ⧸ Subgroup.center Q) := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [hbot, Subgroup.mem_bot] at hx'
  exact hx hx'

theorem centerQuotient_equiv_of_central_ker {S Q : Type} [Group S] [Group Q]
    (hS : IsQuasisimple S) (ρ : S →* Q) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center S) :
    Nonempty (S ⧸ center S ≃* Q ⧸ center Q) := by
  have hle : center S ≤ (center Q).comap ρ := fun c hc => by
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨s, rfl⟩ := hρ q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc s]
  let φ : S ⧸ center S →* Q ⧸ center Q := QuotientGroup.map (center S) (center Q) ρ hle
  have hsimple : IsSimpleGroup (S ⧸ center S) := hS.2.1
  have hcen : Subgroup.center (S ⧸ center S) = ⊥ := by
    rcases (inferInstance : (Subgroup.center (S ⧸ center S)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hS
      apply hab
      have ha : a ∈ Subgroup.center (S ⧸ center S) := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MonoidHom.mem_ker] at hx
    have h1 : ρ s ∈ center Q := (QuotientGroup.eq_one_iff _).mp hx
    have h2 : (QuotientGroup.mk s : S ⧸ center S) ∈ Subgroup.center (S ⧸ center S) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hker
      have hc := Subgroup.mem_center_iff.mp h1 (ρ t)
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      rw [hc]
      exact inv_mul_cancel _
    rw [hcen] at h2
    exact h2
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨s, rfl⟩ := hρ q
    exact ⟨QuotientGroup.mk s, rfl⟩
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem injective_of_odd_ker {Q T : Type*} [Group Q] [Group T] (hQ : CFSG.IsQuasisimple Q)
    (hc : Nat.card (center Q) = 2) (f : Q →* T) (hodd : Odd (Nat.card f.ker)) :
    Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (f.normal_ker) with h | h
  · exfalso
    have h2 : 2 ∣ Nat.card Q := hc ▸ Subgroup.card_subgroup_dvd_card (center Q)
    rw [h, Subgroup.card_top] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · have hdvd : Nat.card f.ker ∣ 2 := hc ▸ Subgroup.card_dvd_of_le h
    have h1 : Nat.card f.ker = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.card_eq_one.mp h1

theorem oddCore_le_ker {X : Type} [Group X] [Finite X] {C J : Subgroup X} (hJC : J ≤ C)
    (hJ'sub : (J.subgroupOf C).IsSubnormal) :
    CFSG.Open.classicalInvolutionOddCore ↥J ≤
      ((QuotientGroup.mk' (pPrimeCore 2 ↥C)).comp (Subgroup.inclusion hJC)).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine sSup_le fun N ⟨hNn, hNodd⟩ x hx => ?_
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  have hle : N.map (Subgroup.inclusion hJC) ≤ J.subgroupOf C := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hnorm : ((N.map (Subgroup.inclusion hJC)).subgroupOf (J.subgroupOf C)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    rintro _ k ⟨n, hn, rfl⟩ hk
    have hk' : k ∈ (Subgroup.inclusion hJC).range := by
      rwa [Subgroup.inclusion_range]
    obtain ⟨j, rfl⟩ := hk'
    exact ⟨j * n * j⁻¹, hNn.conj_mem n hn j, by simp⟩
  have hsub : (N.map (Subgroup.inclusion hJC)).IsSubnormal :=
    Subgroup.IsSubnormal.trans hle hnorm.isSubnormal hJ'sub
  have hcop : Nat.Coprime 2 (Nat.card (N.map (Subgroup.inclusion hJC))) := by
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJC)]
    exact Nat.coprime_two_left.mpr hNodd
  exact CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 2 hsub hcop ⟨x, hx, rfl⟩

theorem noTwoA7ClassicalAt_of_data {X : Type} [Group X] [Finite X] {p : ℕ}
    (hO : LieOrderFormulasInput) (hp2 : p ≠ 2) {z : X} (hB : BTwo X z)
    (hC : ∀ S : Subgroup ↥(FixedCommutingProduct.fixedSubgroup (MulAut.conj z)),
      IsComponent S → OddLieCentralQuotient p ↥S) : NoTwoA7ClassicalAt z := by
  intro hz J hzJ hJsub hW hns
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQq, hQc, ⟨eA⟩⟩ := hW
  set C : Subgroup X := Subgroup.centralizer {z} with hCdef
  have hJC : J ≤ C := le_of_open_isSubnormal' hJsub
  have hJ'sub : (J.subgroupOf C).IsSubnormal := subgroupOf_isSubnormal_of_open' hJsub
  set O : Subgroup ↥C := pPrimeCore 2 ↥C with hOdef
  set π : ↥C →* ↥C ⧸ O := QuotientGroup.mk' O with hπ
  set OJ : Subgroup ↥J := CFSG.Open.classicalInvolutionOddCore ↥J with hOJ
  set ρ₀ : ↥J →* ↥C ⧸ O := π.comp (Subgroup.inclusion hJC) with hρ₀
  have hle : OJ ≤ ρ₀.ker := oddCore_le_ker hJC hJ'sub
  set ρQ : ↥J ⧸ OJ →* ↥C ⧸ O := QuotientGroup.lift OJ ρ₀ hle with hρQ
  have hQqs : CFSG.IsQuasisimple (↥J ⧸ OJ) := isQuasisimple_of_open' hQq
  have hker_odd : Odd (Nat.card ρQ.ker) := by
    have hodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have h1 : Nat.card ρ₀.ker ∣ Nat.card O := by
      have : ρ₀.ker = O.comap (Subgroup.inclusion hJC) := by
        ext x
        simp [hρ₀, hπ, QuotientGroup.eq_one_iff]
      rw [this]
      exact Subgroup.card_comap_dvd_of_injective O (Subgroup.inclusion hJC)
        (Subgroup.inclusion_injective hJC)
    have h2 : ρQ.ker ≤ ρ₀.ker.map (QuotientGroup.mk' OJ) := by
      intro x hx
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨j, by simpa [hρQ] using hx, rfl⟩
    have h3 : Nat.card ρQ.ker ∣ Nat.card (ρ₀.ker.map (QuotientGroup.mk' OJ)) :=
      Subgroup.card_dvd_of_le h2
    have h4 := Subgroup.card_map_dvd (H := ρ₀.ker) (QuotientGroup.mk' OJ)
    exact Odd.of_dvd_nat (hodd.of_dvd_nat h1) (h3.trans h4)
  have hinj : Function.Injective ρQ := injective_of_odd_ker hQqs hQc ρQ hker_odd
  set Jb : Subgroup (↥C ⧸ O) := ρQ.range with hJb
  have hJbeq : Jb = (J.subgroupOf C).map π := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨Subgroup.inclusion hJC j, j.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨QuotientGroup.mk ⟨c, hc⟩, rfl⟩
  have eQ : (↥J ⧸ OJ) ≃* ↥Jb := MonoidHom.ofInjective hinj
  have hJbq : CFSG.IsQuasisimple ↥Jb := CFSG.LocalCores.isQuasisimple_of_mulEquiv eQ hQqs
  have hJbsub : Jb.IsSubnormal := by
    rw [hJbeq]
    exact hJ'sub.map (QuotientGroup.mk'_surjective O)
  have hJbcomp : IsComponent Jb := ⟨hJbq, hJbsub⟩
  obtain ⟨hS, hSmap, -, -⟩ := (canonical_prime_component_lift (X := ↥C) 2).1 Jb hJbcomp
  set S : Subgroup ↥C := canonicalPrimeLift 2 Jb with hSdef
  set e : ↥C ≃* ↥(FixedCommutingProduct.fixedSubgroup (MulAut.conj z)) :=
    MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizer_gen z).symm with he
  have hS' : IsPComponent 2 (S.map e.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hS
  have eS : ↥S ≃* ↥(S.map e.toMonoidHom) := S.equivMapOfInjective e.toMonoidHom e.injective
  have hSq : IsQuasisimple ↥S :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eS.symm (hB _ hS')
  obtain ⟨K', -, hSsub, -, -⟩ := hS
  have hScomp : IsComponent S := ⟨hSq, hSsub⟩
  have hScomp' : IsComponent (S.map e.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e hScomp
  have hCS : OddLieCentralQuotient p ↥S := oddLieCentralQuotient_of_mulEquiv eS (hC _ hScomp')
  have hmem : ∀ x : ↥S, π (x : ↥C) ∈ Jb := fun x => by
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem _ x.2
  set σ : ↥S →* ↥Jb := (π.comp S.subtype).codRestrict Jb hmem with hσ
  set σ' : ↥S →* (↥J ⧸ OJ) := eQ.symm.toMonoidHom.comp σ with hσ'
  have hσs : Function.Surjective σ' := by
    intro q
    obtain ⟨x, hx, hxq⟩ := (show ((eQ q : ↥Jb) : ↥C ⧸ O) ∈ S.map π by rw [hSmap]; exact (eQ q).2)
    refine ⟨⟨x, hx⟩, ?_⟩
    have : σ ⟨x, hx⟩ = eQ q := Subtype.ext hxq
    simp [hσ', this]
  have hker : σ'.ker ≤ center ↥S := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSq σ'.normal_ker with h | h
    · exfalso
      have hone : ∀ q : ↥J ⧸ OJ, q = 1 := fun q => by
        obtain ⟨x, rfl⟩ := hσs q
        have hx : x ∈ σ'.ker := by
          rw [h]
          exact Subgroup.mem_top x
        exact MonoidHom.mem_ker.mp hx
      have hcard : Nat.card (center (↥J ⧸ OJ)) = 1 := by
        have : Subsingleton (center (↥J ⧸ OJ)) :=
          ⟨fun a b => Subtype.ext ((hone a).trans (hone b).symm)⟩
        exact Nat.card_of_subsingleton (⟨1, Subgroup.one_mem _⟩ : center (↥J ⧸ OJ))
      exact absurd (hcard.symm.trans hQc) (by norm_num)
    · exact h
  obtain ⟨eC⟩ := centerQuotient_equiv_of_central_ker hSq σ' hσs hker
  exact not_oddLieCentralQuotient_alt7 hO hp2 hCS (eC.trans eA)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
