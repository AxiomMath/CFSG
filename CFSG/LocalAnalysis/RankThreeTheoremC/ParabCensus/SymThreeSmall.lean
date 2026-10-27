module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymThreeNormal
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Small

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem normal_of_symThree_of_card_dvd {J : Type} [Group J] [Finite J] {Z : Subgroup J}
    [Z.Normal] (hZ : Z ≤ center J) (hZo : Odd (Nat.card Z)) (h96 : Nat.card (J ⧸ Z) ∣ 96)
    {U : Subgroup (J ⧸ CFSG.pCore 2 J)} (hU : TwelveNotLe.Sym.IsSymThree U) : U.Normal := by
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
    have hsix : 6 ∣ Nat.card (J ⧸ CFSG.pCore 2 J) := by
      simpa [TwelveNotLe.Sym.card_symThree hU] using Subgroup.card_subgroup_dvd_card U
    exact absurd ((show 2 ∣ 6 by norm_num).trans hsix) hodd.not_two_dvd_nat
  ·
    obtain ⟨f, hfs, hfker, hfodd, hfc⟩ :=
      exists_symThree_quotient_of_not_normal_sylow hZ hZo h96 hT₀
    have hcen : Z.map (QuotientGroup.mk' (CFSG.pCore 2 J)) ≤
        center (J ⧸ CFSG.pCore 2 J) := by
      rintro - ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZ hz) x]
    have hUK : U ⊓ f.ker = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      obtain ⟨hkU, hkK⟩ := hk
      have hcentU : (⟨k, hkU⟩ : ↥U) ∈ Subgroup.center ↥U := by
        rw [Subgroup.mem_center_iff]
        intro u
        exact Subtype.ext (hfc k hkK (u : J ⧸ CFSG.pCore 2 J)).symm
      obtain ⟨e⟩ := hU
      have hx1 : e ⟨k, hkU⟩ = 1 := by
        apply (show ∀ y : Equiv.Perm (Fin 3),
          y ∈ Subgroup.center (Equiv.Perm (Fin 3)) → y = 1 by decide)
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨u, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcentU u]
      have hk1 : (⟨k, hkU⟩ : ↥U) = 1 := e.injective (by rw [hx1, map_one])
      exact congrArg Subtype.val hk1
    let gU : ↥U →* Equiv.Perm (Fin 3) := f.comp U.subtype
    have hgUinj : Function.Injective gU := by
      intro x y hxy
      have hz : ((x : J ⧸ CFSG.pCore 2 J)⁻¹ * (y : J ⧸ CFSG.pCore 2 J)) ∈ U ⊓ f.ker := by
        refine ⟨U.mul_mem (U.inv_mem x.2) y.2, ?_⟩
        change ((x : J ⧸ CFSG.pCore 2 J)⁻¹ * (y : J ⧸ CFSG.pCore 2 J)) ∈ f.ker
        have hxyf : f (x : J ⧸ CFSG.pCore 2 J) = f (y : J ⧸ CFSG.pCore 2 J) := hxy
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxyf, inv_mul_cancel]
      rw [hUK] at hz
      have hz1 : (x : J ⧸ CFSG.pCore 2 J)⁻¹ * (y : J ⧸ CFSG.pCore 2 J) = 1 := by
        simpa using hz
      have hxy' : (y : J ⧸ CFSG.pCore 2 J) = (x : J ⧸ CFSG.pCore 2 J) := by
        have h := congrArg (fun t => (x : J ⧸ CFSG.pCore 2 J) * t) hz1
        simpa [mul_assoc] using h
      exact Subtype.ext hxy'.symm
    have hgUs : Function.Surjective gU := by
      obtain ⟨e⟩ := hU
      exact Function.Injective.surjective_of_finite e.toEquiv hgUinj
    refine Subgroup.Normal.mk ?_
    intro n hn g
    obtain ⟨u, hu⟩ := hgUs (f g)
    have hkg : (u : J ⧸ CFSG.pCore 2 J)⁻¹ * g ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [show f (u : J ⧸ CFSG.pCore 2 J) = f g from hu, inv_mul_cancel]
    set k := (u : J ⧸ CFSG.pCore 2 J)⁻¹ * g with hkdef
    have hg_eq : g = (u : J ⧸ CFSG.pCore 2 J) * k := by rw [hkdef]; group
    have hkcomm : k * n * k⁻¹ = n := by
      rw [hfc k hkg n, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : g * n * g⁻¹ = (u : J ⧸ CFSG.pCore 2 J) * n *
        (u : J ⧸ CFSG.pCore 2 J)⁻¹ := by
      calc g * n * g⁻¹ = (u : J ⧸ CFSG.pCore 2 J) * (k * n * k⁻¹) *
            (u : J ⧸ CFSG.pCore 2 J)⁻¹ := by rw [hg_eq]; group
        _ = (u : J ⧸ CFSG.pCore 2 J) * n * (u : J ⧸ CFSG.pCore 2 J)⁻¹ := by rw [hkcomm]
    rw [hconj]
    exact U.mul_mem (U.mul_mem u.2 hn) (U.inv_mem u.2)


theorem normal_of_subnormal_symThree_small {X : Type} [Group X] [Finite X] {L J : Subgroup X}
    (hCP : CompParab L J) (h : IsSmallTwoOrG2 (↥L ⧸ center ↥L))
    {U : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hUs : IsSubnormal U ⊤)
    (hU : TwelveNotLe.Sym.IsSymThree U) : U.Normal := by
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
    exact normal_of_symThree_of_card_dvd hZc hZo h96' hU
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
    exact HasLeviCensus.normal_of_subnormal_symThree
      (hasLeviCensus_of_comap_eq_flagStabilizer hCP.parab.1 (by norm_num) σ hσs hσk hcomap)
      hUs hU

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
