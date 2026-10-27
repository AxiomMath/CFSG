module

public import CFSG.ClassicalInvolution.Asc77.AscS22A
import CFSG.ClassicalInvolution.Asc77.AscMuTabResidual3
import CFSG.ClassicalInvolution.Asc77.AscIHSectKD
public import CFSG.ClassicalInvolution.Asc77.AscIHSectI
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraph

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.ModelFacts.Orth15

section E4

variable {p : ℕ} [Fact p.Prime]

theorem noV_of_e4 (t : StatedLieTag) (k e : ℕ) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible t k p e)
    (hE4 : (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4 ∧ p ^ e % 4 = 3) ∨
      (t = .PSU ∧ k = 4 ∧ p ^ e % 4 = 1))
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H)
    (R R' : Subgroup (modelUniv t k p e Fact.out).K) (x x' : (modelUniv t k p e Fact.out).K)
    (hpair : TwinPairOn t (modelUniv t k p e Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  rcases hE4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
  · exact noV_psp2 hp2 hq hadm ψ R R' x x' hpair v hvR hvR' hvv
  · exact noV_psl4_three hp2 h hadm ψ R R' x x' hpair v hvR hvR' hvv
  · exact noV_psu4_one hp2 hq h hadm ψ R R' x x' hpair v hvR hvR' hvv

end E4


section Main

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem twin_section_dichotomy (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ} (hBelow : CITBelowU p f n)
    (hlt : Nat.card X < n) (hS : GenSection p f Φ) {A A' : Subgroup X} {z : X}
    (hA : A ∈ Φ) (hA' : A' ∈ Φ) (hne : A ≠ A')
    (hzA : IsUniqueInvolution A z) (hzA' : IsUniqueInvolution A' z)
    (hstar : ∀ B ∈ Φ, ∀ J ∈ Φ, J ∈ omegaStarNbr Φ B →
      ∃ w, IsUniqueInvolution B w ∧ IsUniqueInvolution J w)
    {H : Type} [Group H] [Finite H] (ι : X →* H) (hι : Function.Injective ι) (a : H)
    (ha : ∀ x : X, a * ι x * a⁻¹ ∈ ι.range ∧ a⁻¹ * ι x * a ∈ ι.range)
    (haA : ∀ x ∈ A, ∃ n ∈ oddCoreOf A, a * ι x * a⁻¹ = ι (n * x))
    (haA' : ∀ x ∈ A', ∃ n ∈ oddCoreOf A', a * ι x * a⁻¹ = ι (n * x))
    (ha2 : a * a = ι z) : ∀ B ∈ Φ, IsUniqueInvolution B z := by
  classical
  have hΦ : HypOmegaMod p f Φ := hS.hyp
  by_cases hconn : DConnected Φ
  · have hpath : ∀ N, Relation.ReflTransGen
        (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) A N → N ∈ Φ ∧ IsUniqueInvolution N z := by
      intro N hN
      induction hN with
      | refl => exact ⟨hA, hzA⟩
      | tail hpre hstep ih =>
        rename_i M N'
        obtain ⟨hN'Φ, hadj⟩ := hstep
        obtain ⟨hMΦ, hzM⟩ := ih
        refine ⟨hN'Φ, ?_⟩
        rcases hadj with h | h
        · obtain ⟨w, hw1, hw2⟩ :=
            hstar M hMΦ N' hN'Φ (T3.omegaNbr_subset_omegaStarNbr hp hΦ M h)
          have := hzM.eq hw1
          subst this
          exact hw2
        · obtain ⟨w, hw1, hw2⟩ :=
            hstar N' hN'Φ M hMΦ (T3.omegaNbr_subset_omegaStarNbr hp hΦ N' h)
          have := hzM.eq hw2
          subst this
          exact hw1
    intro B hB
    exact (hpath B (hconn A hA B hB)).2
  · exfalso
    have hNE : ¬ DEdgeless Φ := by
      intro h
      rcases mem_kPerp_of_twin hΦ hA hA' hzA hzA' with h' | h'
      · exact hne h'
      · exact h _ hA' _ hA (Or.inl h')
    obtain ⟨d, ε, hd5, hd8, t', n', hortag, D, hcard, i, htag, hrank⟩ :=
      thm8SectBelow'_of_citBelow G2D4Models.ih8G2D4_unconditional hBelow hp hq X hlt Φ hS
        ⟨_, hA⟩ hNE hconn
    have hsix : (D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
        (D.tag i = .PSU ∧ D.rank i = 4) ∨ (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
        (D.tag i = .POmegaPlus ∧ D.rank i = 4) ∨ (D.tag i = .POmegaMinus ∧ D.rank i = 4) := by
      rw [htag, hrank]
      rcases hortag with ⟨-, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨-, -, ht, hn⟩ | ⟨hd7, hodd, ht, hn⟩ |
        ⟨hd8', hev, -, ht, hn⟩ | ⟨hd8', hev, -, ht, hn⟩
      · exact Or.inl ⟨ht, hn⟩
      · exact Or.inr (Or.inl ⟨ht, hn⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨ht, hn⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, by omega⟩))))
    have htrans : TransSection p f Φ := by
      rcases transSection_or_dConnected hp hq (thm4Below_of_citBelow hBelow) hlt hS with h | h
      · exact absurd h hconn
      · exact h
    have htop : (⊤ : Subgroup X) ∉ Φ := top_notMem_of_transitive htrans.trans hA hA' hne.symm
    have hL : HasLieType p f Φ (D.tag i) (D.rank i) := ⟨D, hcard, i, rfl, rfl⟩
    have hsh : MuTab.MuSmallShapes p f :=
      MuTab.muSmallShapes_of_g2d4 ih8D4Star (MuTab.muResidualG2D4_proved p f)
    have hshape := MuTab.kindShape_of_shapes hsh hp hq htrans ⟨A, hA⟩ htop hL
    have hdcd : ∀ K ∈ Φ, dComp Φ K = dstarComp Φ K := by
      intro K hK
      refine Set.Subset.antisymm (Thompson.dComp_subset_dstarComp hp hΦ K) ?_
      intro J hJ
      have hJ' : Relation.ReflTransGen (dstarAdj Φ) K J := hJ
      have key : ∀ N, Relation.ReflTransGen (dstarAdj Φ) K N → N ∈ Φ ∧
          Relation.ReflTransGen (fun M N : Subgroup X => N ∈ Φ ∧ dAdj Φ M N) K N := by
        intro N hN
        induction hN with
        | refl => exact ⟨hK, Relation.ReflTransGen.refl⟩
        | tail hpre hstep ih =>
          rename_i M N'
          obtain ⟨hN'Φ, hadj⟩ := hstep
          obtain ⟨hMΦ, hMc⟩ := ih
          refine ⟨hN'Φ, ?_⟩
          rcases hadj with h | h
          · obtain ⟨w, hw1, hw2⟩ := hstar M hMΦ N' hN'Φ h
            rcases mem_kPerp_of_twin hΦ hN'Φ hMΦ hw2 hw1 with h' | h'
            · rw [h']
              exact hMc
            · exact hMc.tail ⟨hN'Φ, Or.inl h'⟩
          · obtain ⟨w, hw1, hw2⟩ := hstar N' hN'Φ M hMΦ h
            rcases mem_kPerp_of_twin hΦ hMΦ hN'Φ hw2 hw1 with h' | h'
            · rw [← h']
              exact hMc
            · exact hMc.tail ⟨hN'Φ, Or.inr h'⟩
      exact (key J hJ').2
    have hbad : ¬ ∃ K ∈ Φ, dComp Φ K ≠ dstarComp Φ K := fun ⟨K, hK, h⟩ => h (hdcd K hK)
    have hvac : ((D.tag i = .PSp ∧ D.rank i = 2) ∨
        (D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ f % 4 = 3) ∨
        (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ f % 4 = 1)) → False := by
      intro hE4
      have hG2 : D.tag i ≠ .G2 := by
        rcases hE4 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
      have hD4 : D.tag i ≠ .trialityD4 := by
        rcases hE4 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
      have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => hD4 h.1
      have hΦex : HypOmega p f Φ := hΦ.toExact (OmegaLie.exactMembers hp hq hΦ D)
      have hsurj : Function.Surjective (D.hom i) := D.hom_surjective_of_gen hcard hS.gen i
      obtain ⟨j, R, hRf, hAR⟩ := D.fundamental A hA
      obtain ⟨j', R', hR'f, hAR'⟩ := D.fundamental A' hA'
      have hsub : Subsingleton (Fin D.card) := by
        rw [hcard]
        infer_instance
      obtain rfl : i = j := Subsingleton.elim _ _
      obtain rfl : i = j' := Subsingleton.elim _ _
      have hKΦ : R.map (D.hom i) ∈ Φ := by rw [← hAR]; exact hA
      have hK'Φ : R'.map (D.hom i) ∈ Φ := by rw [← hAR']; exact hA'
      have hzK : IsUniqueInvolution (R.map (D.hom i)) z := by rw [← hAR]; exact hzA
      have hzK' : IsUniqueInvolution (R'.map (D.hom i)) z := by rw [← hAR']; exact hzA'
      have hneR : R.map (D.hom i) ≠ R'.map (D.hom i) := by rw [← hAR, ← hAR']; exact hne
      obtain ⟨-, hRR', hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩ :=
        twinShape_of_twin hp hq hΦex D i hG2 hD4 hRf hR'f hKΦ hK'Φ hzK hzK' hneR
      let ψ' : (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K →* H :=
        ι.comp (D.hom i)
      have hpair : TwinPairOn (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out)
          ψ' R R' x x' :=
        { ker := by
            intro y hy
            apply D.ker_le_center i
            rw [MonoidHom.mem_ker] at hy ⊢
            refine hι ?_
            rw [map_one]
            exact hy
          mem := hRf
          mem' := hR'f
          ne := hRR'
          comm := hcomm
          hx := hx
          hx2 := hx2
          hx1 := hx1
          hx' := hx'
          hx'2 := hx'2
          hx'1 := hx'1
          same := by simp only [ψ', MonoidHom.comp_apply, hψx, hψx'] }
      have hrange : ψ'.range = ι.range := by
        ext y
        simp only [ψ', MonoidHom.mem_range, MonoidHom.comp_apply]
        constructor
        · rintro ⟨s, rfl⟩
          exact ⟨_, rfl⟩
        · rintro ⟨x, rfl⟩
          obtain ⟨s, rfl⟩ := hsurj x
          exact ⟨s, rfl⟩
      have hn : a ∈ Subgroup.normalizer (ψ'.range : Set H) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [hrange]
        constructor
        · rintro ⟨x, rfl⟩
          exact (ha x).1
        · intro hy
          obtain ⟨x, hx⟩ := hy
          obtain ⟨y', hy'⟩ := (ha x).2
          have : y = a⁻¹ * ι x * a := by
            rw [hx]
            group
          rw [this]
          exact (ha x).2
      let v : ↥(inducedAutOn ψ'.range) := toInducedAutOn ψ'.range ⟨a, hn⟩
      have hexc : ∀ {B : Subgroup X}, B ∈ Φ →
          (∀ x ∈ B, ∃ n ∈ oddCoreOf B, a * ι x * a⁻¹ = ι (n * x)) →
          ∀ x ∈ B, a * ι x = ι x * a := by
        intro B hB hh x hx
        obtain ⟨n, hn, hnx⟩ := hh x hx
        rw [oddCoreOf_eq_bot_of_exact hΦex.exact hB, Subgroup.mem_bot] at hn
        rw [hn, one_mul] at hnx
        calc a * ι x = (a * ι x * a⁻¹) * a := by group
          _ = ι x * a := by rw [hnx]
      have hψ'A : ∀ r ∈ R, ψ' r ∈ ι '' (A : Set X) := by
        intro r hr
        refine ⟨D.hom i r, ?_, rfl⟩
        rw [hAR]
        exact Subgroup.mem_map_of_mem _ hr
      have hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ' r = FrameVertex.innerHom ψ' r * v := by
        intro r hr
        obtain ⟨s, hs, hsr⟩ := hψ'A r hr
        rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * ψ' r = ψ' r * a
        rw [← hsr]
        exact hexc hA haA s hs
      have hψ'A' : ∀ r ∈ R', ψ' r ∈ ι '' (A' : Set X) := by
        intro r hr
        refine ⟨D.hom i r, ?_, rfl⟩
        rw [hAR']
        exact Subgroup.mem_map_of_mem _ hr
      have hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ' r = FrameVertex.innerHom ψ' r * v := by
        intro r hr
        obtain ⟨s, hs, hsr⟩ := hψ'A' r hr
        rw [FrameVertex.innerHom_apply, ← map_mul, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * ψ' r = ψ' r * a
        rw [← hsr]
        exact hexc hA' haA' s hs
      have hvv : v * v = FrameVertex.innerHom ψ' x := by
        rw [FrameVertex.innerHom_apply, ← map_mul]
        congr 1
        refine Subtype.ext ?_
        show a * a = ψ' x
        simp only [ψ', MonoidHom.comp_apply, hψx]
        exact ha2
      have hq' : 5 ≤ p ^ D.exp i := by rw [hexp]; exact hq
      have hE4' : (D.tag i = .PSp ∧ D.rank i = 2) ∨
          (D.tag i = .PSL ∧ D.rank i = 4 ∧ p ^ D.exp i % 4 = 3) ∨
          (D.tag i = .PSU ∧ D.rank i = 4 ∧ p ^ D.exp i % 4 = 1) := by
        rw [hexp]
        exact hE4
      exact noV_of_e4 (D.tag i) (D.rank i) (D.exp i) hp hq' (D.admissible i) hE4' ψ' R R' x x'
        hpair v hvR hvR' hvv
    rcases hsix with ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩ | ⟨ht, hk⟩
    · exact hvac (Or.inl ⟨ht, hk⟩)
    · by_cases hπ : piSign p f = true
      · have h4 : MuTab.KindShape Φ .s4 := by
          have := hshape
          rw [ht, hk, hπ] at this
          simpa [MuTab.muKind] using this
        exact hbad h4.2.2
      · have hπf : piSign p f = false := by simpa using hπ
        exact hvac (Or.inr (Or.inl ⟨ht, hk, MuTab.pow_mod_four_of_piSign_false hp hπf⟩))
    · by_cases hπ : piSign p f = true
      · exact hvac (Or.inr (Or.inr ⟨ht, hk, MuTab.piSign_true_iff.mp hπ⟩))
      · have hπf : piSign p f = false := by simpa using hπ
        have h4 : MuTab.KindShape Φ .s4 := by
          have := hshape
          rw [ht, hk, hπf] at this
          simpa [MuTab.muKind] using this
        exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .s4 := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .wyl := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2
    · have h4 : MuTab.KindShape Φ .s4 := by
        have := hshape
        rw [ht, hk] at this
        simpa [MuTab.muKind] using this
      exact hbad h4.2.2

end Main

end S22

end CFSG.ClassicalInvolution.Asc77
