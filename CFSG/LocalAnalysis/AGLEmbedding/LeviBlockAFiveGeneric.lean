module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.LargeExtraspecial.S5Comp
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.AGLEmbedding

open CFSG.Open Subgroup

namespace LeviFive

private theorem commutator_alt5 : commutator (alternatingGroup (Fin 5)) = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with
    h | h
  · exfalso
    have hc : IsMulCommutative (alternatingGroup (Fin 5)) := ⟨⟨fun a b => by
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [← commutator_def, h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this⟩⟩
    have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 5)).mp hc
    simp at this
  · exact h

private theorem not_isSolvable_alt5 : ¬ Group.IsSolvable (alternatingGroup (Fin 5)) := by
  intro hs
  haveI : Group.IsPerfect (alternatingGroup (Fin 5)) := ⟨commutator_alt5⟩
  haveI : Nontrivial (alternatingGroup (Fin 5)) := IsSimpleGroup.toNontrivial
  exact Group.IsPerfect.not_isSolvable _ hs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)]

private theorem card_quot_center_eq_sixty {S : Type*} [Group S] (hq : Open.IsQuasisimple S)
    (h : S →* alternatingGroup (Fin 5)) (hh : Function.Surjective h) :
    Nat.card (S ⧸ Subgroup.center S) = 60 := by
  have hne : h.ker ≠ ⊤ := by
    intro htop
    haveI : Nontrivial (alternatingGroup (Fin 5)) := IsSimpleGroup.toNontrivial
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨y, rfl⟩ := hh a
    exact ha ((MonoidHom.mem_ker).mp (htop ▸ Subgroup.mem_top y))
  have hle := CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hq
    (MonoidHom.normal_ker h) hne
  have hge : Subgroup.center S ≤ h.ker := by
    intro z hz
    have hzc : h z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := hh a
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot] at hzc
    exact hzc
  have hker : h.ker = Subgroup.center S := le_antisymm hle hge
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective h hh)).toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]
  rfl

theorem exists_block_of_subnormal (S : ∀ j, Subgroup (G j)) {X B : Subgroup (∀ j, G j)}
    (hpi : Subgroup.pi Set.univ S ≤ X) (hcomm : ⁅X, X⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j)) (hBs : IsSubnormal B X)
    (g : ↥B →* alternatingGroup (Fin 5)) (hg : Function.Surjective g) :
    ∃ j, Open.IsQuasisimple (S j) ∧ Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 ∧
      S j ≤ B.map (Pi.evalMonoidHom G j) := by
  classical
  set p : ∀ j, ↥B →* G j := fun j => (Pi.evalMonoidHom G j).comp B.subtype with hp
  have hstep : ∃ j, (p j).ker ≤ g.ker := by
    by_contra hall
    push Not at hall
    have htop : ∀ j, (p j).ker.map g = ⊤ := by
      intro j
      haveI : ((p j).ker.map g).Normal := (MonoidHom.normal_ker _).map g hg
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((p j).ker.map g) with h | h
      · exact absurd ((Subgroup.map_eq_bot_iff _).mp h) (hall j)
      · exact h
    have hnorm : ∀ s : Finset ι, (⨅ j ∈ s, (p j).ker).Normal := by
      intro s
      refine ⟨fun n hn x => ?_⟩
      simp only [Subgroup.mem_iInf] at hn ⊢
      intro j hj
      exact (MonoidHom.normal_ker (p j)).conj_mem n (hn j hj) x
    have hfin : ∀ s : Finset ι, (⨅ j ∈ s, (p j).ker).map g = ⊤ := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [show (⨅ j ∈ (∅ : Finset ι), (p j).ker) = ⊤ by simp, ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top.mpr hg
      | insert a s ha ih =>
        rw [Finset.iInf_insert]
        haveI := hnorm s
        rw [eq_top_iff]
        calc (⊤ : Subgroup (alternatingGroup (Fin 5))) = commutator (alternatingGroup (Fin 5)) :=
              commutator_alt5.symm
          _ = ⁅(p a).ker.map g, (⨅ j ∈ s, (p j).ker).map g⁆ := by
              rw [htop a, ih, _root_.commutator_def]
          _ = ((⁅(p a).ker, ⨅ j ∈ s, (p j).ker⁆).map g) := (Subgroup.map_commutator _ _ _).symm
          _ ≤ ((p a).ker ⊓ ⨅ j ∈ s, (p j).ker).map g :=
              Subgroup.map_mono (Subgroup.commutator_le_inf _ _)
    have hbot : (⨅ j ∈ (Finset.univ : Finset ι), (p j).ker) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_iInf] at hx
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      funext j
      have := (Subgroup.mem_iInf.mp (hx j)) (Finset.mem_univ j)
      exact this
    have h1 := hfin Finset.univ
    rw [hbot, Subgroup.map_bot] at h1
    haveI : Nontrivial (alternatingGroup (Fin 5)) := IsSimpleGroup.toNontrivial
    exact bot_ne_top h1
  obtain ⟨j, hj⟩ := hstep
  set R := (p j).range with hR
  have hRB : R = B.map (Pi.evalMonoidHom G j) := by
    rw [hR, hp, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker' : (p j).rangeRestrict.ker ≤ g.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hj
  set g' : ↥R →* alternatingGroup (Fin 5) :=
    (MonoidHom.liftOfSurjective (p j).rangeRestrict (p j).rangeRestrict_surjective) ⟨g, hker'⟩
    with hg'
  have hg's : Function.Surjective g' := by
    intro a
    obtain ⟨y, rfl⟩ := hg a
    exact ⟨(p j).rangeRestrict y, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩
  have hcomm' : (commutator ↥R).map g' = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hg's, ← _root_.commutator_def, commutator_alt5]
  set D := (commutator ↥R).map R.subtype with hD
  have hRX : R ≤ X.map (Pi.evalMonoidHom G j) := by
    rw [hRB]
    exact Subgroup.map_mono hBs.le
  have hDS : D ≤ S j := by
    intro d hd
    obtain ⟨d', hd', rfl⟩ := hd
    have h1 : (R.subtype d') ∈ ⁅R, R⁆ := by
      rw [← Subgroup.map_subtype_commutator]
      exact ⟨d', hd', rfl⟩
    have h2 : ⁅R, R⁆ ≤ ⁅X, X⁆.map (Pi.evalMonoidHom G j) := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hRX hRX
    obtain ⟨x, hx, hxd⟩ := h2 h1
    have := ((Subgroup.mem_pi Set.univ).mp (hcomm hx)) j (Set.mem_univ j)
    rw [← hxd]
    exact this
  have hSX : S j ≤ X.map (Pi.evalMonoidHom G j) := by
    intro s hs
    refine ⟨Pi.mulSingle j s, hpi ?_, by simp⟩
    rw [Subgroup.mem_pi Set.univ]
    intro k _
    by_cases hk : k = j
    · subst hk
      simpa using hs
    · simp [Pi.mulSingle_eq_of_ne hk]
  have hRs : IsSubnormal R (X.map (Pi.evalMonoidHom G j)) := by
    rw [hRB]
    exact hBs.map _
  have hDs : IsSubnormal D (X.map (Pi.evalMonoidHom G j)) := by
    refine IsSubnormal.step (by rintro _ ⟨d, -, rfl⟩; exact d.2) ?_ hRs
    have hsub : D.subgroupOf R = commutator ↥R := by
      rw [hD, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
    rw [hsub]
    infer_instance
  have hDSs : IsSubnormal D (S j) := by
    have := hDs.inf_of_le hSX
    rwa [inf_eq_left.mpr hDS] at this
  set eD := (commutator ↥R).equivMapOfInjective R.subtype R.subtype_injective with heD
  rcases hS j with hq | hsol
  swap
  · exfalso
    have h1 : Group.IsSolvable ↥D :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hDS) (Subgroup.inclusion_injective _)
    have h2 : Group.IsSolvable ↥(commutator ↥R) :=
      solvable_of_solvable_injective (f := eD.toMonoidHom) eD.injective
    have h3 : Group.IsSolvable ↥((commutator ↥R).map g') :=
      solvable_of_surjective (g'.subgroupMap_surjective _)
    rw [hcomm'] at h3
    exact not_isSolvable_alt5 (solvable_of_surjective (f := (⊤ : Subgroup _).subtype)
      (fun a => ⟨⟨a, Subgroup.mem_top a⟩, rfl⟩))
  refine ⟨j, hq, ?_⟩
  rcases CFSG.Fischer.Classification.Recognition.IsSubnormal.eq_or_le_center hDSs hq with
    hDeq | hDc
  swap
  · exfalso
    have hcommD : ∀ a b : ↥(commutator ↥R), a * b = b * a := by
      intro a b
      apply eD.injective
      apply Subtype.ext
      have ha := hDc (eD a).2
      have hb := hDc (eD b).2
      obtain ⟨a', ha'c, ha'⟩ := ha
      obtain ⟨b', -, hb'⟩ := hb
      have := Subgroup.mem_center_iff.mp ha'c b'
      simp only [map_mul, Subgroup.coe_mul]
      rw [← ha', ← hb']
      simpa using (congrArg Subtype.val this).symm
    have hA : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := by
      intro a b
      have ha : a ∈ (commutator ↥R).map g' := by rw [hcomm']; exact Subgroup.mem_top a
      have hb : b ∈ (commutator ↥R).map g' := by rw [hcomm']; exact Subgroup.mem_top b
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      rw [← map_mul, ← map_mul]
      exact congrArg g' (congrArg Subtype.val (hcommD ⟨a', ha'⟩ ⟨b', hb'⟩))
    have h1 : commutator (alternatingGroup (Fin 5)) = ⊥ := by
      rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hA a b
    rw [commutator_alt5] at h1
    haveI : Nontrivial (alternatingGroup (Fin 5)) := IsSimpleGroup.toNontrivial
    exact top_ne_bot h1
  refine ⟨?_, ?_⟩
  · have eS : ↥(S j) ≃* ↥(commutator ↥R) := (MulEquiv.subgroupCongr hDeq.symm).trans eD.symm
    refine card_quot_center_eq_sixty hq ((g'.comp (commutator ↥R).subtype).comp eS.toMonoidHom)
      ?_
    intro a
    have ha : a ∈ (commutator ↥R).map g' := by rw [hcomm']; exact Subgroup.mem_top a
    obtain ⟨c, hc, rfl⟩ := ha
    refine ⟨eS.symm ⟨c, hc⟩, ?_⟩
    simp
  · rw [← hRB, ← hDeq]
    rintro _ ⟨d, -, rfl⟩
    exact d.2

theorem exists_quotient_of_cover {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] [Finite K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) :
    ∃ φ : ↥((P.subgroupOf L).comap ρ) →* ↥P ⧸ CFSG.pCore 2 ↥P, Function.Surjective φ ∧
      Group.IsSolvable ↥φ.ker ∧ ∀ q : ↥((P.subgroupOf L).comap ρ),
        φ q = QuotientGroup.mk ⟨((ρ q : ↥L) : Y), Subgroup.mem_subgroupOf.mp q.2⟩ := by
  classical
  have hθmem : ∀ q : ↥((P.subgroupOf L).comap ρ),
      ((L.subtype.comp ρ).comp ((P.subgroupOf L).comap ρ).subtype) q ∈ P := fun q =>
    Subgroup.mem_subgroupOf.mp q.2
  set θ : ↥((P.subgroupOf L).comap ρ) →* ↥P :=
    ((L.subtype.comp ρ).comp ((P.subgroupOf L).comap ρ).subtype).codRestrict P hθmem with hθ
  have hθs : Function.Surjective θ := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hρ ⟨y, hPL hy⟩
    have hkQ : k ∈ (P.subgroupOf L).comap ρ := by
      rw [Subgroup.mem_comap, hk, Subgroup.mem_subgroupOf]
      exact hy
    refine ⟨⟨k, hkQ⟩, Subtype.ext ?_⟩
    simp [hθ, hk]
  set φ := (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp θ with hφ
  refine ⟨φ, (QuotientGroup.mk'_surjective _).comp hθs, ?_, fun q => rfl⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ x : ↥φ.ker, (θ.comp φ.ker.subtype) x ∈ CFSG.pCore 2 ↥P := fun x => by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥P)) (θ (x : ↥((P.subgroupOf L).comap ρ))) = 1 :=
      x.2
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  set g₀ : ↥φ.ker →* ↥(CFSG.pCore 2 ↥P) := (θ.comp φ.ker.subtype).codRestrict _ hmem
    with hg₀
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥P) := by
    haveI := (CFSG.pCore_isPGroup (G := ↥P) (p := 2)).isNilpotent
    infer_instance
  have hcen : ∀ c : ↥g₀.ker,
      (((c : ↥φ.ker) : ↥((P.subgroupOf L).comap ρ)) : K) ∈ Subgroup.center K := by
    intro c
    apply hker
    rw [MonoidHom.mem_ker]
    have h1 : g₀ c = 1 := c.2
    have h2 := congrArg (fun z : ↥(CFSG.pCore 2 ↥P) => ((z : ↥P) : Y)) h1
    simp only [hg₀, hθ, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
      Subgroup.coe_subtype, OneMemClass.coe_one] at h2
    exact Subtype.ext h2
  haveI : Group.IsSolvable ↥g₀.ker := by
    apply isSolvable_of_comm
    intro a b
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp (hcen b) _
  exact solvable_of_ker_le_range g₀.ker.subtype g₀ (fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem exists_block_of_comap {Q X : Type*} [Group Q] [Finite Q] [Group X]
    (S : ∀ j, Subgroup (G j)) (β : Q →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hpi : Subgroup.pi Set.univ S ≤ β.range) (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j)) (φ : Q →* X)
    (hφ : Function.Surjective φ) {C : Subgroup X} (hC : IsSubnormal C ⊤)
    (f : ↥C →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) :
    ∃ j, Open.IsQuasisimple (S j) ∧ Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 ∧
      S j ≤ ((C.comap φ).map β).map (Pi.evalMonoidHom G j) := by
  have hBs : IsSubnormal ((C.comap φ).map β) β.range := by
    have h1 : IsSubnormal (C.comap φ) ⊤ := by
      have := hC.comap φ
      rwa [Subgroup.comap_top] at this
    have h2 := h1.map β
    rwa [← MonoidHom.range_eq_map] at h2
  have hf₁ : Function.Surjective (f.comp (φ.subgroupComap C)) :=
    hf.comp (φ.subgroupComap_surjective C hφ)
  have hk2 : IsPGroup 2 (β.subgroupMap (C.comap φ)).ker := by
    intro x
    have hx : β (x : ↥(C.comap φ)) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp x.2)
    obtain ⟨n, hn⟩ := hβ ⟨_, (MonoidHom.mem_ker).mpr hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨g, hg⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen.exists_surjective_alt5_of_ker _ hf₁
    (β.subgroupMap (C.comap φ)) (β.subgroupMap_surjective _) hk2
  exact exists_block_of_subnormal S hpi hcomm hS hBs g hg

end LeviFive

open LeviFive in
theorem leviBlocksOfFiveComponents_holds : LeviBlocksOfFiveComponents := by
  intro Y _ _ L P hPL K _ _ ρ hρ hker ι _ _ G _ _ S β hβ hpi hcomm hS
  classical
  obtain ⟨φ, hφs, hsolv, -⟩ := exists_quotient_of_cover hPL ρ hρ hker
  have key : ∀ C : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P), IsFiveComponent P C →
      ∃ j, Open.IsQuasisimple (S j) ∧ Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 ∧
        S j ≤ ((C.comap φ).map β).map (Pi.evalMonoidHom G j) := by
    rintro C ⟨hC, f, hf⟩
    exact exists_block_of_comap S β hβ hpi hcomm hS φ hφs hC.2.1 f hf
  refine ⟨fun C hC => ?_, fun C₁ C₂ hne h₁ h₂ => ?_⟩
  · obtain ⟨j, hq, hc, -⟩ := key C hC
    exact ⟨j, hq, hc⟩
  · obtain ⟨j₁, hq₁, hc₁, hle₁⟩ := key C₁ h₁
    obtain ⟨j₂, hq₂, hc₂, hle₂⟩ := key C₂ h₂
    refine ⟨j₁, j₂, ?_, hq₁, hq₂, hc₁, hc₂⟩
    intro hjj
    subst hjj
    have hcomm12 : ⁅C₁, C₂⁆ = ⊥ :=
      CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne h₁.1 h₂.1 hne
    have hle : ⁅C₁.comap φ, C₂.comap φ⁆ ≤ φ.ker := by
      rw [← Subgroup.map_eq_bot_iff, Subgroup.map_commutator,
        Subgroup.map_comap_eq_self_of_surjective hφs, Subgroup.map_comap_eq_self_of_surjective hφs]
      exact hcomm12
    have hSperf : ⁅S j₁, S j₁⁆ = S j₁ := by
      rw [← Subgroup.map_subtype_commutator, hq₁.1, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hSle : S j₁ ≤ (φ.ker.map β).map (Pi.evalMonoidHom G j₁) := by
      rw [← hSperf]
      calc ⁅S j₁, S j₁⁆ ≤ ⁅((C₁.comap φ).map β).map (Pi.evalMonoidHom G j₁),
            ((C₂.comap φ).map β).map (Pi.evalMonoidHom G j₁)⁆ := Subgroup.commutator_mono hle₁ hle₂
        _ = ((⁅C₁.comap φ, C₂.comap φ⁆).map β).map (Pi.evalMonoidHom G j₁) := by
            rw [Subgroup.map_commutator, Subgroup.map_commutator]
        _ ≤ (φ.ker.map β).map (Pi.evalMonoidHom G j₁) := Subgroup.map_mono (Subgroup.map_mono hle)
    have hT : Group.IsSolvable ↥((φ.ker.map β).map (Pi.evalMonoidHom G j₁)) := by
      haveI : Group.IsSolvable ↥(φ.ker.map β) := solvable_of_surjective (β.subgroupMap_surjective _)
      exact solvable_of_surjective ((Pi.evalMonoidHom G j₁).subgroupMap_surjective _)
    have hSs : Group.IsSolvable ↥(S j₁) :=
      solvable_of_solvable_injective (f := Subgroup.inclusion hSle) (Subgroup.inclusion_injective _)
    haveI : Group.IsPerfect ↥(S j₁) := ⟨hq₁.1⟩
    haveI : Nontrivial (↥(S j₁) ⧸ Subgroup.center ↥(S j₁)) := hq₁.2.toNontrivial
    haveI : Nontrivial ↥(S j₁) :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(S j₁))).nontrivial
    exact Group.IsPerfect.not_isSolvable _ hSs

end CFSG.AGLEmbedding
