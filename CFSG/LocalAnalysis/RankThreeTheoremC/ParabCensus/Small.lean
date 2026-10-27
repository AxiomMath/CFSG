module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.OddW
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusAltEight
public import CFSG.LocalAnalysis.AGLEmbedding.SymThreeCentralExt
public import CFSG.HardMathSupport.Curtis.Proving.FixThreeSmallFour

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup TenThreeThree

theorem exists_surjective_perm_fin_three_of_sylow {H : Type} [Group H] [Finite H]
    (hcard : Nat.card (Sylow 2 H) = 3)
    (hnorm : ∀ T : Sylow 2 H, normalizer (T : Set H) = (T : Subgroup H)) :
    ∃ φ : H →* Equiv.Perm (Fin 3), Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧
      ∀ N : Subgroup H, N.Normal → IsPGroup 2 ↥N → N ≤ φ.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ψ : H →* Equiv.Perm (Sylow 2 H) := MulAction.toPermHom H (Sylow 2 H)
  let e3 : Sylow 2 H ≃ Fin 3 := Finite.equivFinOfCardEq hcard
  let φ : H →* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e3).toMonoidHom.comp ψ
  have hidx : ∀ T : Sylow 2 H, T.index = 3 := fun T => by
    rw [← hnorm T, ← Sylow.card_eq_index_normalizer T, hcard]
  have hmem : ∀ g : H, g ∈ φ.ker ↔ ∀ T : Sylow 2 H, g ∈ (T : Subgroup H) := by
    intro g
    have hψ : ψ g = 1 ↔ ∀ T : Sylow 2 H, g ∈ (T : Subgroup H) := by
      constructor
      · intro hg T
        have h3 : (ψ g) T = (1 : Equiv.Perm (Sylow 2 H)) T := congrArg (fun p => p T) hg
        rw [Equiv.Perm.one_apply] at h3
        have h2 : g • T = T := h3
        rwa [Sylow.smul_eq_iff_mem_normalizer, hnorm T] at h2
      · intro hg
        refine Equiv.Perm.ext fun T => ?_
        have h1 : g • T = T :=
          Sylow.smul_eq_iff_mem_normalizer.mpr (by rw [hnorm T]; exact hg T)
        calc (ψ g) T = g • T := MulAction.toPerm_apply g T
          _ = T := h1
          _ = (1 : Equiv.Perm (Sylow 2 H)) T := (Equiv.Perm.one_apply T).symm
    rw [MonoidHom.mem_ker, show φ g = (Equiv.permCongrHom e3) (ψ g) from rfl,
      ← map_one (Equiv.permCongrHom e3), (Equiv.permCongrHom e3).injective.eq_iff]
    exact hψ
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hle : φ.ker ≤ (T₀ : Subgroup H) := fun g hg => (hmem g).mp hg T₀
  refine ⟨φ, ?_, (T₀.isPGroup').to_le hle, ?_⟩
  ·
    have hHcard : Nat.card H = 3 * Nat.card (T₀ : Subgroup H) := by
      have h := Subgroup.card_mul_index (T₀ : Subgroup H)
      rw [hidx T₀] at h
      omega
    have hrange : Nat.card ↥φ.range = φ.ker.index := by
      rw [Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
    have hkey : Nat.card ↥φ.range = 3 * k := by
      have h1 : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card H := by
        rw [← Subgroup.card_mul_index φ.ker, hrange]
      rw [hHcard, hk] at h1
      have h2 : Nat.card ↥φ.ker * Nat.card ↥φ.range = Nat.card ↥φ.ker * (3 * k) := by
        rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h2
    have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have hk2 : k ∣ 2 := by
      have hdvd : Nat.card ↥φ.range ∣ 6 := by
        have h := Subgroup.card_subgroup_dvd_card φ.range
        rwa [h6] at h
      have h : 3 * k ∣ 6 := hkey ▸ hdvd
      rw [show (6 : ℕ) = 3 * 2 from rfl] at h
      exact (Nat.mul_dvd_mul_iff_left (by norm_num)).mp h
    have htop : φ.range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [hkey, h6]
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two k hk2 with hk1 | hk1
      · exfalso
        have hcard' : Nat.card ↥(T₀ : Subgroup H) = Nat.card ↥φ.ker := by
          rw [hk, hk1, mul_one]
        have hTeq : φ.ker = (T₀ : Subgroup H) :=
          Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard')
        have hTn : (T₀ : Subgroup H).Normal := hTeq ▸ MonoidHom.normal_ker φ
        have htop' : (T₀ : Subgroup H) = ⊤ := by
          have h2 : normalizer (T₀ : Set H) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hTn
          rwa [hnorm T₀] at h2
        have hidx1 : (T₀ : Subgroup H).index = 1 := by rw [htop', Subgroup.index_top]
        have h3 : (T₀ : Subgroup H).index = 3 := hidx T₀
        omega
      · omega
    exact MonoidHom.range_eq_top.mp htop
  ·
    intro N hNn hN2 g hg
    haveI := hNn
    exact (hmem g).mpr fun T => IsPGroup.le_sylow_of_normal hN2 T hg

theorem isPGroup_quotient_subgroupOf_comap {G N : Type} [Group G] [Group N] {p : ℕ} {π : G →* N}
    (hπ : Function.Surjective π) {Z : Subgroup G} [Z.Normal] (hZ : Z = π.ker) {K : Subgroup N}
    (hK : IsPGroup p ↥K) : IsPGroup p (↥(K.comap π) ⧸ Z.subgroupOf (K.comap π)) := by
  have hker : Z.subgroupOf (K.comap π) = (π.domRestrict (K.comap π)).ker := by
    rw [MonoidHom.ker_domRestrict, hZ]
  have hrange : (π.domRestrict (K.comap π)).range = K := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      obtain ⟨x, rfl⟩ := hπ y
      exact ⟨⟨x, hy⟩, rfl⟩
  refine hK.of_equiv ((QuotientGroup.quotientMulEquivOfEq hker).trans
    ((QuotientGroup.quotientKerEquivRange (π.domRestrict (K.comap π))).trans
      (MulEquiv.subgroupCongr hrange))).symm

theorem exists_symThree_quotient_of_not_normal_sylow {J : Type} [Group J] [Finite J]
    {Z : Subgroup J} [Z.Normal] (hZ : Z ≤ center J) (hZo : Odd (Nat.card Z))
    (h96 : Nat.card (J ⧸ Z) ∣ 96) {T₀ : Sylow 2 (J ⧸ Z)} (hT₀ : ¬ T₀.Normal) :
    ∃ f : J ⧸ CFSG.pCore 2 J →* Equiv.Perm (Fin 3),
      Function.Surjective f ∧ f.ker ≤ Z.map (QuotientGroup.mk' (CFSG.pCore 2 J)) ∧
      Odd (Nat.card f.ker) ∧ ∀ k ∈ f.ker, ∀ y, k * y = y * k := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : J →* J ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hidx3 : ∀ T : Sylow 2 (J ⧸ Z), T.index ∣ 3 := by
    intro T
    have hdvd : T.index ∣ 96 := (Subgroup.index_dvd_card _).trans h96
    rw [show (96 : ℕ) = 2 ^ 5 * 3 from by norm_num] at hdvd
    have hcop : Nat.Coprime T.index (2 ^ 5) :=
      Nat.Coprime.pow_right 5
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr T.not_dvd_index).symm
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hcard : Nat.card (Sylow 2 (J ⧸ Z)) = 3 := by
    have hdvd : Nat.card (Sylow 2 (J ⧸ Z)) ∣ 3 :=
      (Sylow.card_dvd_index T₀).trans (hidx3 T₀)
    have hne : Nat.card (Sylow 2 (J ⧸ Z)) ≠ 1 := by
      intro h1
      have h2 : (Subgroup.normalizer (T₀ : Set (J ⧸ Z))).index = 1 := by
        rw [← Sylow.card_eq_index_normalizer T₀, h1]
      exact hT₀ (Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h2))
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h | h
    · exact absurd h hne
    · exact h
  have hidxT : ∀ T : Sylow 2 (J ⧸ Z), T.index = 3 := by
    intro T
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three T.index (hidx3 T) with h | h
    · exfalso
      have h1 : Nat.card (Sylow 2 (J ⧸ Z)) ∣ 1 := h ▸ Sylow.card_dvd_index T
      rw [Nat.dvd_one] at h1
      omega
    · exact h
  have hnorm : ∀ T : Sylow 2 (J ⧸ Z),
      Subgroup.normalizer (T : Set (J ⧸ Z)) = (T : Subgroup (J ⧸ Z)) := by
    intro T
    have h1 : (Subgroup.normalizer (T : Set (J ⧸ Z))).index = 3 := by
      rw [← Sylow.card_eq_index_normalizer T, hcard]
    have h2 : T.relIndex (Subgroup.normalizer (T : Set (J ⧸ Z))) = 1 := by
      have h3 : T.relIndex (Subgroup.normalizer (T : Set (J ⧸ Z))) *
          (Subgroup.normalizer (T : Set (J ⧸ Z))).index = T.index :=
        Subgroup.relIndex_mul_index Subgroup.le_normalizer
      rw [h1, hidxT T] at h3
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) Subgroup.le_normalizer
  obtain ⟨φ, hφs, hφ2, hφN⟩ := exists_surjective_perm_fin_three_of_sylow hcard hnorm
  have hpc_le : CFSG.pCore 2 J ≤ (φ.comp π).ker := by
    have hle : (CFSG.pCore 2 J).map π ≤ φ.ker := by
      haveI : ((CFSG.pCore 2 J).map π).Normal :=
        (CFSG.pCore_normal (p := 2) (G := J)).map π hπs
      exact hφN _ inferInstance ((CFSG.pCore_isPGroup (p := 2) (G := J)).map π)
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hle (Subgroup.mem_map_of_mem π hx)
  let f : J ⧸ CFSG.pCore 2 J →* Equiv.Perm (Fin 3) :=
    QuotientGroup.lift (CFSG.pCore 2 J) (φ.comp π) hpc_le
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨j, hj⟩ := hφs.comp hπs y
    exact ⟨QuotientGroup.mk j, by
      rw [show f (QuotientGroup.mk j) = (φ.comp π) j from
        QuotientGroup.lift_mk _ _ j]
      exact hj⟩
  have hMle : (φ.ker).comap π ≤ Z ⊔ CFSG.pCore 2 J := by
    have hMn : ((φ.ker).comap π).Normal := (MonoidHom.normal_ker φ).comap π
    have hZM : Z ≤ (φ.ker).comap π := by
      intro z hz
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, show π z = 1 from by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz, map_one]
    exact le_sup_pCore_two_of_central_odd_quotient_two hMn hZM hZ hZo
      (isPGroup_quotient_subgroupOf_comap hπs hπker.symm hφ2)
  have hfker : f.ker ≤ Z.map (QuotientGroup.mk' (CFSG.pCore 2 J)) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) y
    rw [MonoidHom.mem_ker] at hy
    have hx1 : (φ.comp π) x = 1 := by
      rw [← QuotientGroup.lift_mk (CFSG.pCore 2 J) hpc_le x]
      exact hy
    have hxsup : x ∈ Z ⊔ CFSG.pCore 2 J :=
      hMle (by rw [Subgroup.mem_comap, MonoidHom.mem_ker]; exact hx1)
    have hqbot : (CFSG.pCore 2 J).map (QuotientGroup.mk' (CFSG.pCore 2 J)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hxq : QuotientGroup.mk' (CFSG.pCore 2 J) x ∈
        (Z ⊔ CFSG.pCore 2 J).map (QuotientGroup.mk' (CFSG.pCore 2 J)) :=
      Subgroup.mem_map_of_mem _ hxsup
    rw [Subgroup.map_sup, hqbot, sup_bot_eq] at hxq
    exact hxq
  have hfodd : Odd (Nat.card f.ker) :=
    Odd.of_dvd_nat hZo ((Subgroup.card_dvd_of_le hfker).trans (Subgroup.card_map_dvd Z _))
  refine ⟨f, hfs, hfker, hfodd, ?_⟩
  intro k hk y
  have hcen : Z.map (QuotientGroup.mk' (CFSG.pCore 2 J)) ≤
      center (J ⧸ CFSG.pCore 2 J) := by
    rintro - ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz) x]
  exact (Subgroup.mem_center_iff.mp (hcen (hfker hk)) y).symm

theorem not_two_dvd_index_wSup_of_card_dvd {J : Type} [Group J] [Finite J] {Z : Subgroup J}
    [Z.Normal] (hZ : Z ≤ center J) (hZo : Odd (Nat.card Z)) (h96 : Nat.card (J ⧸ Z) ∣ 96) :
    ¬ 2 ∣ (wSup (J ⧸ CFSG.pCore 2 J)).index := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : J →* J ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hidx3 : ∀ T : Sylow 2 (J ⧸ Z), T.index ∣ 3 := by
    intro T
    have hdvd : T.index ∣ 96 := (Subgroup.index_dvd_card _).trans h96
    rw [show (96 : ℕ) = 2 ^ 5 * 3 from by norm_num] at hdvd
    have hcop : Nat.Coprime T.index (2 ^ 5) :=
      Nat.Coprime.pow_right 5
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr T.not_dvd_index).symm
    exact hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 (J ⧸ Z)) := inferInstance
  by_cases hT₀ : T₀.Normal
  ·
    set M : Subgroup J := (T₀ : Subgroup (J ⧸ Z)).comap π with hM
    have hMn : M.Normal := hT₀.comap π
    have hZM : Z ≤ M := by
      intro z hz
      rw [hM, Subgroup.mem_comap, show π z = 1 from by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz]
      exact (T₀ : Subgroup (J ⧸ Z)).one_mem
    have hquot : IsPGroup 2 (↥M ⧸ Z.subgroupOf M) :=
      isPGroup_quotient_subgroupOf_comap hπs hπker.symm T₀.isPGroup'
    have hMD : M ≤ Z ⊔ CFSG.pCore 2 J :=
      le_sup_pCore_two_of_central_odd_quotient_two hMn hZM hZ hZo hquot
    have hpcM : CFSG.pCore 2 J ≤ M := by
      haveI hn : ((CFSG.pCore 2 J).map π).Normal :=
        (CFSG.pCore_normal (p := 2) (G := J)).map π hπs
      have hle : (CFSG.pCore 2 J).map π ≤ (T₀ : Subgroup (J ⧸ Z)) :=
        IsPGroup.le_sylow_of_normal
          ((CFSG.pCore_isPGroup (p := 2) (G := J)).map π) T₀
      intro x hx
      rw [hM, Subgroup.mem_comap]
      exact hle (Subgroup.mem_map_of_mem π hx)
    have hMi : M.index = (T₀ : Subgroup (J ⧸ Z)).index := by
      rw [hM]
      exact Subgroup.index_comap_of_surjective (T₀ : Subgroup (J ⧸ Z)) hπs
    have hrel : (CFSG.pCore 2 J).relIndex M ∣ Nat.card Z := by
      have h1 : (CFSG.pCore 2 J).relIndex M ∣
          (CFSG.pCore 2 J).relIndex (Z ⊔ CFSG.pCore 2 J) :=
        ⟨M.relIndex (Z ⊔ CFSG.pCore 2 J),
          (Subgroup.relIndex_mul_relIndex (CFSG.pCore 2 J) M (Z ⊔ CFSG.pCore 2 J) hpcM hMD).symm⟩
      refine h1.trans ?_
      rw [Subgroup.relIndex_sup_right]
      exact Subgroup.index_dvd_card (Subgroup.subgroupOf (CFSG.pCore 2 J) Z)
    have hodd : Odd (Nat.card (J ⧸ CFSG.pCore 2 J)) := by
      have heq : Nat.card (J ⧸ CFSG.pCore 2 J) =
          (CFSG.pCore 2 J).relIndex M * M.index :=
        ((Subgroup.index_eq_card _).symm).trans (Subgroup.relIndex_mul_index hpcM).symm
      rw [heq]
      exact Odd.mul (Odd.of_dvd_nat hZo hrel)
        (Odd.of_dvd_nat ⟨1, by norm_num⟩ (hMi ▸ hidx3 T₀))
    exact not_two_dvd_index_wSup_of_odd hodd.not_two_dvd_nat
  ·
    obtain ⟨f, hfs, hfker, hfodd, hfc⟩ :=
      exists_symThree_quotient_of_not_normal_sylow hZ hZo h96 hT₀
    obtain ⟨T, hTn, ⟨eT⟩, hTi⟩ := SymThreeCentralExt.exists_normal_symThree f hfs hfc hfodd
    intro h2
    have hsub : IsSubnormal T ⊤ := IsSubnormal.step le_top (hTn.subgroupOf ⊤) (IsSubnormal.refl ⊤)
    have hle : T ≤ wSup (J ⧸ CFSG.pCore 2 J) :=
      le_wSup_of_subnormal_of_symThree hsub (Or.inl ⟨eT⟩)
    exact hTi (h2.trans (Subgroup.index_dvd_of_le hle))


theorem not_two_dvd_index_wSup_small {X : Type} [Group X] [Finite X] {L J : Subgroup X}
    (hCP : CompParab L J) (h : IsSmallTwoOrG2 (↥L ⧸ center ↥L)) :
    ¬ 2 ∣ (wSup (↥J ⧸ CFSG.pCore 2 ↥J)).index := by
  classical
  rcases (CFSG.HardMathSupport.Curtis.Proving.isSmallTwoOrG2_iff _).mp h with h4 | hA8
  ·
    have hord : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥L ⧸ center ↥L) :=
      CFSG.HardMathSupport.Curtis.Proving.ordBound_isSmallFourTwo h4
    obtain ⟨hJL, T, hT, hTN⟩ := hCP.parab
    have hTJ : T ≤ J := fun x hx => hTN ⟨hT.1 hx, Subgroup.le_normalizer hx⟩
    have hLperf : commutator ↥L = ⊤ := hCP.comp.2.2.1
    set πL : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπL
    have hπLs : Function.Surjective πL := QuotientGroup.mk'_surjective _
    set Jb : Subgroup ↥L := J.subgroupOf L with hJb
    have hJbne : Jb.map πL ≠ ⊤ := by
      intro htop
      apply hCP.ne_top
      have hJbtop : Jb = ⊤ := by
        refine CFSG.HardMathSupport.Curtis.Proving.top_of_mul_central_of_perfect
          (Subgroup.center ↥L) Jb le_rfl hLperf ?_
        intro g
        have hg : πL g ∈ Jb.map πL := htop ▸ Subgroup.mem_top _
        obtain ⟨h', hh', he⟩ := Subgroup.mem_map.1 hg
        exact ⟨h', hh', h'⁻¹ * g, QuotientGroup.eq.1 he, (mul_inv_cancel_left h' g).symm⟩
      rw [hJb, Subgroup.subgroupOf_eq_top] at hJbtop
      exact le_antisymm hJL hJbtop
    have hT₀ : CFSG.QuasithinUnique.IsSylowTwoOf ((T.subgroupOf L).map πL) ⊤ :=
      CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
        (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hT) πL hπLs
    have hT₀J : (T.subgroupOf L).map πL ≤ Jb.map πL :=
      Subgroup.map_mono (fun x hx => hTJ hx)
    have h96 : Nat.card (Jb.map πL) ∣ 96 := hord _ _ hT₀ hT₀J hJbne
    have hZc : (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≤ center ↥J := by
      intro x hx
      rw [Subgroup.mem_comap] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      refine Subgroup.inclusion_injective hJL ?_
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hx (Subgroup.inclusion hJL y)
    have hZo : Odd (Nat.card ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) := by
      refine Odd.of_dvd_nat hCP.odd ?_
      have hcard : Nat.card ↥(Subgroup.map (Subgroup.inclusion hJL)
          ((Subgroup.center ↥L).comap (Subgroup.inclusion hJL))) =
          Nat.card ↥((Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) :=
        Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJL)
      rw [← hcard]
      exact Subgroup.card_dvd_of_le (by rintro - ⟨z, hz, rfl⟩; exact hz)
    have h96' : Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL)) ∣ 96 := by
      set g : ↥J →* ↥L ⧸ center ↥L := πL.comp (Subgroup.inclusion hJL) with hg
      have hgker : g.ker = (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) := by
        ext x
        rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, Subgroup.mem_comap, hπL,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have hgrange : g.range = Jb.map πL := by
        rw [hg, MonoidHom.range_comp, Subgroup.inclusion_range]
      have e : ↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL) ≃* ↥(Jb.map πL) :=
        (QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
          ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hgrange))
      rw [show Nat.card (↥J ⧸ (Subgroup.center ↥L).comap (Subgroup.inclusion hJL))
          = Nat.card ↥(Jb.map πL) from Nat.card_congr e.toEquiv]
      exact h96
    exact not_two_dvd_index_wSup_of_card_dvd hZc hZo h96'
  ·
    obtain ⟨eA⟩ := hA8
    obtain ⟨e8⟩ := CFSG.AGLEmbedding.ToralCensus.nonempty_alt_eight_mulEquiv_projectiveSL
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.AGLEmbedding.ToralCensus.center_eq_bot_of_mulEquiv_alt_eight hCP.comp.2.2 hCP.odd eA
    obtain ⟨ρ, hρ⟩ :=
      CFSG.AGLEmbedding.ToralCensus.exists_compat_of_center_eq_bot hZ (eA.trans e8)
    obtain ⟨hρs, -⟩ := CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat
      hCP.comp.2.2.1 (eA.trans e8) ρ hρ
    obtain ⟨σ, e', I, hσs, hσ, -, hcomap, -, -⟩ :=
      CFSG.AGLEmbedding.exists_comap_eq_flagStabilizer hCP.odd (n := 4) (by norm_num)
        (eA.trans e8) hρs hρ hCP.parab
    obtain ⟨-, hσk⟩ := CFSG.AGLEmbedding.ToralCensus.surjective_and_ker_le_of_compat
      hCP.comp.2.2.1 e' σ hσ
    exact HasLeviCensus.not_two_dvd_index_wSup
      (hasLeviCensus_of_comap_eq_flagStabilizer hCP.parab.1 (by norm_num) σ hσs hσk hcomap)

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
