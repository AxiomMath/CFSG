module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisEngine
public import CFSG.Quasithin.H13.A7SectionRank
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLevi
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTypes
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceAltSeven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement

@[expose] def KFactCompParabFieldIndex : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P → L.Normal →
    (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) → 3 ∣ Nat.card (perfectJoin P) →
    Open.pRank 3 (perfectJoin P) ≤ 1 → ∀ a : Y, IsPGroup 3 (Subgroup.zpowers a) →
    a ∈ Subgroup.normalizer (P : Set Y) →
    (¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) →
    ∃ N : Subgroup Y, N.Normal ∧ N.index = 3

namespace BlockFieldIndex

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_bot_of_perfect_le {J U : Subgroup Y} (hJ : Group.IsSolvable J) (hUJ : U ≤ J)
    (hU : ⁅U, U⁆ = U) : U = ⊥ := by
  set U' : Subgroup J := U.subgroupOf J
  have hmap : U'.map J.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUJ
  have hU' : ⁅U', U'⁆ = U' := by
    apply Subgroup.map_injective J.subtype_injective
    rw [Subgroup.map_commutator, hmap, hU]
  have hbot : U' = ⊥ := by
    by_contra hne
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hU'
  rw [← hmap, hbot, Subgroup.map_bot]

theorem perfectJoin_eq_bot_of_isSolvable {J : Subgroup Y} (hJ : Group.IsSolvable J) :
    perfectJoin J = ⊥ :=
  eq_bot_of_perfect_le hJ (perfectJoin_le J) (perfectJoin_perfect J)

theorem not_three_dvd_of_isSolvable {J : Subgroup Y} (hJ : Group.IsSolvable J) :
    ¬ 3 ∣ Nat.card (perfectJoin J) := by
  rw [perfectJoin_eq_bot_of_isSolvable hJ, Subgroup.card_bot]
  norm_num

theorem isSolvable_of_pCore_quotient {J : Subgroup Y} {Q : Type*} [Group Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) (hQ : Group.IsSolvable Q) : Group.IsSolvable J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable (↥J ⧸ CFSG.pCore 2 ↥J) :=
    solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Group.IsNilpotent (CFSG.pCore 2 ↥J) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  exact solvable_of_ker_le_range (CFSG.pCore 2 ↥J).subtype
    (QuotientGroup.mk' (CFSG.pCore 2 ↥J)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_card_dvd_seventyTwo' {J : Subgroup Y} (h : Nat.card J ∣ 72) :
    Group.IsSolvable J :=
  ToralReduce.isSolvable_of_card_dvd_seventyTwo h

theorem isSolvable_perm_of_le_four {n : ℕ} (hn : n ≤ 4) : Group.IsSolvable (Equiv.Perm (Fin n)) :=
  ToralReduce.isSolvable_of_card_dvd_seventyTwo (by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    interval_cases n <;> decide)

theorem exists_perfect_map_eq {A B : Type*} [Group A] [Finite A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (Q : Subgroup B) (hQ : ⁅Q, Q⁆ = Q) :
    ∃ N : Subgroup A, N ≤ Q.comap f ∧ N.map f = Q ∧ ⁅N, N⁆ = N := by
  classical
  have hne : ∃ n, ∃ N : Subgroup A, N ≤ Q.comap f ∧ N.map f = Q ∧ Nat.card N = n :=
    ⟨_, Q.comap f, le_rfl, Subgroup.map_comap_eq_self_of_surjective hf Q, rfl⟩
  obtain ⟨N, hNle, hNmap, hNcard⟩ := Nat.find_spec hne
  refine ⟨N, hNle, hNmap, ?_⟩
  have h1 : ⁅N, N⁆ ≤ N := by
    simpa only [sup_idem] using Subgroup.commutator_le_sup N N
  have hmin : Nat.find hne ≤ Nat.card ↥⁅N, N⁆ :=
    Nat.find_min' hne ⟨⁅N, N⁆, h1.trans hNle, by rw [Subgroup.map_commutator, hNmap, hQ], rfl⟩
  rw [← hNcard] at hmin
  exact Subgroup.eq_of_le_of_card_ge h1 hmin

@[expose] noncomputable def quotPi {J : Subgroup Y} {Q : Type*} [Group Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) : ↥J →* Q :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥J))

theorem quotPi_surjective {J : Subgroup Y} {Q : Type*} [Group Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) : Function.Surjective (quotPi e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem mem_pCore_of_quotPi_eq_one {J : Subgroup Y} {Q : Type*} [Group Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) {x : ↥J} (hx : quotPi e x = 1) :
    x ∈ CFSG.pCore 2 ↥J := by
  have h : QuotientGroup.mk' (CFSG.pCore 2 ↥J) x = 1 := by
    apply e.injective
    rw [map_one]
    exact hx
  exact (QuotientGroup.eq_one_iff x).1 h

theorem le_pRank_perfectJoin {J : Subgroup Y} {Q : Type*} [Group Q] [Finite Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) {Q₀ : Subgroup Q} (hQ₀ : ⁅Q₀, Q₀⁆ = Q₀)
    {E : Subgroup Q} (hEQ : E ≤ Q₀) (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) : k ≤ Open.pRank 3 (perfectJoin J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNle, hNmap, hNperf⟩ :=
    exists_perfect_map_eq (quotPi e) (quotPi_surjective e) Q₀ hQ₀
  set ρ : ↥N →* ↥Q₀ := ((quotPi e).comp N.subtype).codRestrict Q₀ fun x => hNle x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    rw [← hNmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.Coprime 3 (Nat.card ρ.ker) := by
    let ϕ : ρ.ker →* CFSG.pCore 2 ↥J :=
      (N.subtype.comp ρ.ker.subtype).codRestrict _ fun x => by
        apply mem_pCore_of_quotPi_eq_one e
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        exact this
    have hϕ : Function.Injective ϕ := fun x y hxy => by
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 ((CFSG.pCore_isPGroup (p := 2)).of_injective ϕ hϕ)
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have h1 := CFSG.AGLEmbeddingD2.HeisEngine.pRank_le_pRank_comap_of_coprime hρ hker
    (⊤ : Subgroup ↥Q₀)
  rw [Subgroup.comap_top] at h1
  have h0 : k ≤ Open.pRank 3 (⊤ : Subgroup ↥Q₀) := by
    refine CFSG.SectionRank.le_pRank (by norm_num) (le_top : E.subgroupOf Q₀ ≤ ⊤)
      ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ ?_
    · have := hE.1.1.comm ⟨((a : Q₀) : Q), Subgroup.mem_subgroupOf.1 a.2⟩
        ⟨((b : Q₀) : Q), Subgroup.mem_subgroupOf.1 b.2⟩
      have h := congrArg Subtype.val this
      apply Subtype.ext
      apply Subtype.ext
      show ((a : Q₀) : Q) * ((b : Q₀) : Q) = ((b : Q₀) : Q) * ((a : Q₀) : Q)
      exact h
    · apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact hE.2 _ (Subgroup.mem_subgroupOf.1 hx)
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv, hk]
  have h2 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) (J.subtype.comp N.subtype)
    (J.subtype_injective.comp N.subtype_injective) ⊤
  have h3 : (⊤ : Subgroup ↥N).map (J.subtype.comp N.subtype) ≤ perfectJoin J := by
    rw [← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
    refine le_perfectJoin ?_ ?_
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rw [← Subgroup.map_commutator, hNperf]
  exact h0.trans (h1.trans (h2.trans (CFSG.SectionRank.pRank_mono (by norm_num) h3)))

theorem commutator_alternatingGroup_self {n : ℕ} (hn : 5 ≤ n) :
    ⁅alternatingGroup (Fin n), alternatingGroup (Fin n)⁆ = alternatingGroup (Fin n) := by
  have h := commutator_alternatingGroup_eq_top (α := Fin n)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  have h' := congrArg (Subgroup.map (alternatingGroup (Fin n)).subtype) h
  rwa [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h'

theorem center_alternatingGroup_five : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 5)))
    with h | h
  · exact h
  · exfalso
    have hc : commutator (alternatingGroup (Fin 5)) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      have hy : y ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [h]; exact Subgroup.mem_top y
      exact (Subgroup.mem_center_iff.1 hy x).symm
    rw [commutator_alternatingGroup_eq_top (α := Fin 5) (by simp)] at hc
    exact top_ne_bot hc

theorem card_outer_alternatingGroup_five :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 5))) =
      2 := by
  have hA : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
    rw [card_mulAut_alternatingGroup_eq (by norm_num) (by norm_num)]
    rfl
  have hinj : Function.Injective
      (MulAut.conj : alternatingGroup (Fin 5) →* MulAut (alternatingGroup (Fin 5))) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 5)) => φ y)
        (MonoidHom.mem_ker.1 hx)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * x = x * y * x⁻¹ * x := by rw [h1]
        _ = x * y := by group
    rw [center_alternatingGroup_five] at hxc
    exact hxc
  have hI : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (alternatingGroup (Fin 5))) = 60 := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_eq_fintype_card]
    have h := two_mul_card_alternatingGroup (α := Fin 5)
    rw [Fintype.card_perm, Fintype.card_fin] at h
    simp only [Nat.factorial] at h
    omega
  have h := (CFSG.ComponentClassification.OuterAutomorphisms.inner
    (alternatingGroup (Fin 5))).card_mul_index
  rw [hI, hA] at h
  rw [CFSG.ComponentClassification.OuterAutomorphisms.Outer, ← Subgroup.index]
  omega

theorem mem_inner_alternatingGroup_five_of_pow {β : MulAut (alternatingGroup (Fin 5))} {k : ℕ}
    (hβ : β ^ 3 ^ k = 1) :
    β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 5)) := by
  set x : CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 5)) :=
    QuotientGroup.mk β
  have h1 : orderOf x ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one])
  have h2 : orderOf x ∣ 2 := card_outer_alternatingGroup_five ▸ orderOf_dvd_natCard x
  have hc : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left k (by norm_num)
  have h3 : orderOf x = 1 := Nat.dvd_one.1 ((Nat.Coprime.gcd_eq_one hc) ▸ Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff β).1 h3

theorem exists_inner_of_sym_five {J : Subgroup Y}
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin 5)) {a : Y}
    (ha3 : IsPGroup 3 (Subgroup.zpowers a)) (haN : a ∈ Subgroup.normalizer (J : Set Y)) :
    ∃ v ∈ perfectJoin J, ∀ w ∈ perfectJoin J, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := perfectJoin J with hVdef
  have hVJ : V ≤ J := perfectJoin_le J
  set π := quotPi e with hπdef
  set ι : ↥V →* ↥J := Subgroup.inclusion hVJ with hιdef
  have hsign : ∀ x : ↥V, π (ι x) ∈ alternatingGroup (Fin 5) := by
    have hVp : ⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆ = ⊤ := by
      apply Subgroup.map_injective V.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact perfectJoin_perfect J
    set f : ↥V →* ℤˣ := Equiv.Perm.sign.comp (π.comp ι) with hfdef
    have hH : (⊤ : Subgroup ↥V).map f = ⊥ := by
      have hc : ⁅(⊤ : Subgroup ↥V).map f, (⊤ : Subgroup ↥V).map f⁆ =
          (⊤ : Subgroup ↥V).map f := by
        rw [← Subgroup.map_commutator, hVp]
      rw [← hc, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact mul_comm y x
    intro x
    rw [Equiv.Perm.mem_alternatingGroup]
    have hx : f x ∈ (⊤ : Subgroup ↥V).map f := ⟨x, Subgroup.mem_top x, rfl⟩
    rw [hH, Subgroup.mem_bot] at hx
    exact hx
  set ρ : ↥V →* alternatingGroup (Fin 5) := (π.comp ι).codRestrict _ hsign with hρdef
  have hρ : Function.Surjective ρ := by
    obtain ⟨N, -, hNmap, hNperf⟩ := exists_perfect_map_eq π (quotPi_surjective e)
      (alternatingGroup (Fin 5)) (commutator_alternatingGroup_self (by norm_num))
    have hNV : N.map J.subtype ≤ V := le_perfectJoin (by rintro _ ⟨x, -, rfl⟩; exact x.2)
      (by rw [← Subgroup.map_commutator, hNperf])
    intro g
    have hg : (g : Equiv.Perm (Fin 5)) ∈ N.map π := by rw [hNmap]; exact g.2
    obtain ⟨x, hx, hxg⟩ := hg
    refine ⟨⟨x, hNV ⟨x, hx, rfl⟩⟩, Subtype.ext ?_⟩
    have hιx : ι ⟨(x : Y), hNV ⟨x, hx, rfl⟩⟩ = x := Subtype.ext rfl
    change π (ι ⟨(x : Y), hNV ⟨x, hx, rfl⟩⟩) = g
    rw [hιx, hxg]
  have hK2 : IsPGroup 2 ρ.ker := by
    let ϕ : ρ.ker →* CFSG.pCore 2 ↥J :=
      (ι.comp ρ.ker.subtype).codRestrict _ fun x => mem_pCore_of_quotPi_eq_one e (by
        have hx := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        exact hx)
    refine (CFSG.pCore_isPGroup (p := 2)).of_injective ϕ fun x y hxy => ?_
    have hxy' := congrArg (fun z : CFSG.pCore 2 ↥J => ((z : ↥J) : Y)) hxy
    exact Subtype.ext (Subtype.ext hxy')
  have hKle : ρ.ker ≤ CFSG.pCore 2 ↥V :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup (MonoidHom.normal_ker ρ) hK2
  have haV : a ∈ Subgroup.normalizer (V : Set Y) := ParabAutIrr.mem_normalizer_perfectJoin haN
  set σ : MulAut ↥V := V.normalizerMonoidHom ⟨a, haV⟩ with hσdef
  set τ : MulAut ↥J := J.normalizerMonoidHom ⟨a, haN⟩ with hτdef
  have hισ : ∀ x : ↥V, ι (σ x) = τ (ι x) := fun x => Subtype.ext rfl
  have hτp : ∀ x : ↥J, x ∈ CFSG.pCore 2 ↥J → τ x ∈ CFSG.pCore 2 ↥J := by
    intro x hx
    have hch := CFSG.BaerSuzuki.Helpers.pCore_characteristic (G := ↥J) 2
    exact (Subgroup.characteristic_iff_map_le.1 hch τ) ⟨x, hx, rfl⟩
  have hπp : ∀ x : ↥J, x ∈ CFSG.pCore 2 ↥J → π x = 1 := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥J) x = 1 := (QuotientGroup.eq_one_iff x).2 hx
    change e (QuotientGroup.mk' _ x) = 1
    rw [h1, map_one]
  have hσker : ∀ x : ↥V, ρ x = 1 → ρ (σ x) = 1 := by
    intro x hx
    apply Subtype.ext
    change π (ι (σ x)) = 1
    rw [hισ]
    exact hπp _ (hτp _ (mem_pCore_of_quotPi_eq_one e (congrArg Subtype.val hx)))
  have hKσ : ρ.ker.map (σ : ↥V →* ↥V) = ρ.ker := by
    have hle : ρ.ker.map (σ : ↥V →* ↥V) ≤ ρ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hσker x hx
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (f := (σ : ↥V →* ↥V)) σ.injective])
  set iso := QuotientGroup.quotientKerEquivOfSurjective ρ hρ with hisodef
  set β : MulAut (alternatingGroup (Fin 5)) :=
    (iso.symm.trans (QuotientGroup.congr ρ.ker ρ.ker σ hKσ)).trans iso with hβdef
  have hβ : ∀ x : ↥V, β (ρ x) = ρ (σ x) := by
    intro x
    have h1 : iso.symm (ρ x) = (QuotientGroup.mk x : ↥V ⧸ ρ.ker) := by
      apply iso.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change iso (QuotientGroup.congr ρ.ker ρ.ker σ hKσ (iso.symm (ρ x))) = ρ (σ x)
    rw [h1, QuotientGroup.congr_mk]
    rfl
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hσk : σ ^ 3 ^ k = 1 := by
    have h1 : (⟨a, haV⟩ : Subgroup.normalizer (V : Set Y)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hak)
    rw [hσdef, ← map_pow, h1, map_one]
  have hβn : ∀ n : ℕ, ∀ x : ↥V, (β ^ n) (ρ x) = ρ ((σ ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, MulAut.mul_apply, hβ, ih, MulAut.mul_apply]
  have hβk : β ^ 3 ^ k = 1 := by
    refine MulEquiv.ext fun g => ?_
    obtain ⟨x, rfl⟩ := hρ g
    rw [hβn, hσk]
    rfl
  obtain ⟨g, hg⟩ := mem_inner_alternatingGroup_five_of_pow hβk
  obtain ⟨v₀, hv₀⟩ := hρ g
  refine ⟨((v₀⁻¹ : ↥V) : Y), (v₀⁻¹).2, fun w hw => ?_⟩
  set w' : ↥V := ⟨w, hw⟩ with hw'
  set c : ↥V := σ (v₀⁻¹ * w' * v₀) * w'⁻¹ with hcdef
  have hc : ρ c = 1 := by
    have h1 : ρ c = β (ρ (v₀⁻¹ * w' * v₀)) * (ρ w')⁻¹ := by
      rw [hcdef, map_mul, ← hβ, map_inv]
    rw [h1, ← hg, MulAut.conj_apply, map_mul, map_mul, map_inv, hv₀]
    group
  have hcY : (c : Y) = ⁅a * ((v₀⁻¹ : ↥V) : Y), w⁆ := by
    rw [hcdef, commutatorElement_def]
    change a * ((v₀⁻¹ * w' * v₀ : ↥V) : Y) * a⁻¹ * ((w'⁻¹ : ↥V) : Y) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw']
    group
  rw [← hcY]
  exact ⟨c, hKle hc, rfl⟩

theorem false_of_isSolvable {J : Subgroup Y} (hJ : Group.IsSolvable J)
    (h3 : 3 ∣ Nat.card (perfectJoin J)) : False :=
  not_three_dvd_of_isSolvable hJ h3

theorem false_of_rank {J : Subgroup Y} {Q : Type*} [Group Q] [Finite Q]
    (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Q) {Q₀ : Subgroup Q} (hQ₀ : ⁅Q₀, Q₀⁆ = Q₀)
    {E : Subgroup Q} (hEQ : E ≤ Q₀) (hE : IsElemAbelian 3 E) {k : ℕ}
    (hk : Nat.card E = 3 ^ k) (hk2 : 2 ≤ k) (hrk : Open.pRank 3 (perfectJoin J) ≤ 1) : False := by
  have := le_pRank_perfectJoin e hQ₀ hEQ hE hk
  omega

theorem exists_elem_alternatingGroup (n : ℕ) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), E ≤ alternatingGroup (Fin n) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ (n / 3) := by
  have h := (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 n 3
    Nat.prime_three (by norm_num)
  obtain ⟨E₀, -, hE₀, hcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup (alternatingGroup (Fin n)))
  refine ⟨E₀.map (alternatingGroup (Fin n)).subtype, ?_, CFSG.SectionRank.isElemAbelian_map hE₀ _,
    ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective (alternatingGroup (Fin n)).subtype_injective, hcard, h]

theorem false_of_sym {J : Subgroup Y} {n : ℕ} (e : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin n))
    (h3 : 3 ∣ Nat.card (perfectJoin J)) (hrk : Open.pRank 3 (perfectJoin J) ≤ 1) {a : Y}
    (ha3 : IsPGroup 3 (Subgroup.zpowers a)) (haN : a ∈ Subgroup.normalizer (J : Set Y))
    (hout : ¬ ∃ v ∈ perfectJoin J, ∀ w ∈ perfectJoin J,
      ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin J)) : False := by
  rcases Nat.lt_or_ge n 5 with hn | hn
  · exact false_of_isSolvable (isSolvable_of_pCore_quotient e
      (isSolvable_perm_of_le_four (by omega))) h3
  rcases Nat.lt_or_ge n 6 with hn6 | hn6
  · obtain rfl : n = 5 := by omega
    exact hout (exists_inner_of_sym_five e ha3 haN)
  obtain ⟨E, hEA, hE, hcard⟩ := exists_elem_alternatingGroup n
  exact false_of_rank e (commutator_alternatingGroup_self (by omega)) hEA hE hcard
    (by omega) hrk

end BlockFieldIndex

open BlockFieldIndex

variable {G : Type} [Group G] [Finite G]

theorem kFactBlockFieldIndex_of (hC : KFactCompParabFieldIndex) :
    KFactBlockFieldIndex := by
  intro G _ _ M S L hyps hQS hLn hrank h3 hrk a ha3 haN hout
  obtain ⟨hK, hA, hL, h93, hX, hS⟩ := id hyps
  have hJL : blockPL M S L ≤ barM M L := fun x ⟨y, hy, hyx⟩ =>
    ⟨y, (Subgroup.mem_inf.1 hy).2, hyx⟩
  rcases h93 with h1 | h2 | h3' | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hX
  · exact hC _ _ _ (compParab_of_blockHyps hyps h2)
      (hLn.map _ (QuotientGroup.mk'_surjective _)) hrank h3 hrk a ha3 haN hout
  · exfalso
    rcases citedBlockTransvectionPL_of_type
        CFSG.HardMathSupport.Curtis.UnitaryLevi.citedBlockTransvectionPLType_holds
        G M S L hK hA hL hX hS h3' with ⟨k, d, hk, hd, ⟨e⟩⟩ | ⟨n, -, ⟨e⟩⟩
    · have : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv _ e.toEquiv
      obtain ⟨E, hE, hcard⟩ := ToralReduce.hasE9_sp hk hd
      have hperf := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds k d hk hd
      have hperf' : ⁅(⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group),
          (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group)⁆ =
          (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) := by
        rw [← commutator_def]
        exact hperf
      exact false_of_rank e (Q₀ := (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group)) hperf' le_top
        hE hcard le_rfl hrk
    · exact false_of_sym e h3 hrk ha3 haN hout
  · exfalso
    obtain ⟨-, -, -, -, ⟨e⟩⟩ := h4
    set Z := Subgroup.center ↥(barM M L)
    set I : Subgroup (↥(barM M L) ⧸ Z) :=
      ((blockPL M S L).subgroupOf (barM M L)).map (QuotientGroup.mk' Z)
    set φ : ↥(blockPL M S L) →* ↥(barM M L) ⧸ Z :=
      (QuotientGroup.mk' Z).comp (Subgroup.inclusion hJL)
    have hrange : φ.range ≤ I := by
      rintro _ ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hJL x, x.2, rfl⟩
    haveI : Group.IsSolvable (Equiv.Perm (Fin 4)) := isSolvable_perm_of_le_four le_rfl
    haveI : Group.IsSolvable I := solvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI : Group.IsSolvable φ.range :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hrange)
    have hcen : ∀ x : φ.ker, Subgroup.inclusion hJL (x : ↥(blockPL M S L)) ∈ Z := fun x =>
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 x.2)
    haveI : Group.IsSolvable φ.ker := by
      apply isSolvable_of_comm
      intro x y
      have h := Subgroup.mem_center_iff.1 (hcen x) (Subgroup.inclusion hJL (y : ↥(blockPL M S L)))
      have h' := congrArg Subtype.val h
      apply Subtype.ext
      apply Subtype.ext
      exact h'.symm
    exact false_of_isSolvable (solvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])) h3
  · exfalso
    exact false_of_isSolvable (isSolvable_of_card_dvd_seventyTwo'
      (citedBlockAltSevenPL_holds G M S L hK hA hL hX hS h5)) h3
  · exfalso
    obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    exact false_of_sym e h3 hrk ha3 haN hout
  · exfalso
    obtain ⟨-, n, -, ⟨e⟩⟩ := h7
    exact false_of_sym e h3 hrk ha3 haN hout
  · exfalso
    obtain ⟨-, N, r, hN, h2r, h0, h2, h4', -, φ, -⟩ := h8
    set m := N - 2 * r with hm
    have hm6 : 6 ≤ m := by
      obtain ⟨t, ht⟩ := hN
      omega
    obtain ⟨E, hEA, hE, hcard⟩ := exists_elem_alternatingGroup m
    set ι₂ := MonoidHom.inr (Equiv.Perm (Fin r)) (Equiv.Perm (Fin m))
    have hperf : ⁅(alternatingGroup (Fin m)).map ι₂, (alternatingGroup (Fin m)).map ι₂⁆ =
        (alternatingGroup (Fin m)).map ι₂ := by
      rw [← Subgroup.map_commutator, commutator_alternatingGroup_self (by omega)]
    exact false_of_rank φ hperf (Subgroup.map_mono hEA)
      (CFSG.SectionRank.isElemAbelian_map hE ι₂)
      (by rw [Subgroup.card_map_of_injective (f := ι₂) fun x y h => congrArg Prod.snd h, hcard])
      (by omega) hrk

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
