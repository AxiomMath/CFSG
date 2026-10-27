module

public import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
public import CFSG.GH74.QTGen4.Recog.G23.Words
public import Certificates.Certificate320001
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
meta import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
meta import CFSG.GH74.QTGen4.Recog.G23.Words

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.RankThree.PartTwo.Census.Carrier.G2Three CFSG.GH74.QTGen4.Recog.G23

section CodeChecks

theorem inv_code : ∀ i, mul14 (eCode i) (eInvCode i) = one14 := Certificates.certificate320001.1

theorem rels_code : ∀ r ∈ g23Words, evalCode r = one14 := Certificates.certificate320001.2

end CodeChecks

open CFSG.Blueprint CFSG.Blueprint.Chevalley

abbrev Ghat : Type := ↥(adjointGroup .G2 (ZMod 3))

section WordTransfer

theorem nonempty_mulEquiv_native_of_letters {Y : Type*} [Group Y] [Finite Y]
    (hsimp : IsSimpleGroup Ghat) (hcard : Nat.card Ghat = 7371 * 576)
    (u : Fin 6 → Ghat) (hu : SatisfiesG23Words u) (hugen : Subgroup.closure (Set.range u) = ⊤)
    (g : Fin 6 → Y) (hg : SatisfiesG23Words g) (hne : ∃ i, g i ≠ 1) :
    Nonempty (↥(Subgroup.closure (Set.range g)) ≃* Ghat) := by
  classical
  have hfinG : Finite Ghat := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set f : Fin 6 → Y × Ghat := fun i => (g i, u i) with hf
  set D : Subgroup (Y × Ghat) := Subgroup.closure (Set.range f) with hD
  have hrelD : SatisfiesG23Words f := by
    intro r hr
    have h1 : (MonoidHom.fst Y Ghat) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift g (FreeGroup.mk r) := by
      have : (MonoidHom.fst Y Ghat).comp (FreeGroup.lift f) = FreeGroup.lift g := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    have h2 : (MonoidHom.snd Y Ghat) (FreeGroup.lift f (FreeGroup.mk r)) =
        FreeGroup.lift u (FreeGroup.mk r) := by
      have : (MonoidHom.snd Y Ghat).comp (FreeGroup.lift f) = FreeGroup.lift u := by
        ext i; simp [hf]
      exact congrArg (fun φ => φ (FreeGroup.mk r)) this
    refine Prod.ext ?_ ?_
    · simpa [hg r hr] using h1
    · simpa [hu r hr] using h2
  have hcardD : Nat.card D ≤ 7371 * 576 := card_closure_le f hrelD
  have hmap₁ : D.map (MonoidHom.fst Y Ghat) = Subgroup.closure (Set.range g) := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hmap₂ : D.map (MonoidHom.snd Y Ghat) = ⊤ := by
    rw [hD, MonoidHom.map_closure, ← Set.range_comp]
    simpa [hf, Function.comp_def] using hugen
  let p₂ : D →* Ghat := (MonoidHom.snd Y Ghat).comp D.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro x
    have : x ∈ D.map (MonoidHom.snd Y Ghat) := by rw [hmap₂]; trivial
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, rfl⟩
  have hle : Nat.card D ≤ Nat.card Ghat := by rw [hcard]; exact hcardD
  have hbij₂ : Function.Bijective p₂ := hp₂.bijective_of_nat_card_le hle
  let ψ : D ≃* Ghat := MulEquiv.ofBijective p₂ hbij₂
  have hDsimp : IsSimpleGroup D := MulEquiv.isSimpleGroup ψ
  have hmem : ∀ d : D, (d : Y × Ghat).1 ∈ Subgroup.closure (Set.range g) := by
    intro d
    rw [← hmap₁]
    exact Subgroup.mem_map.mpr ⟨d, d.2, rfl⟩
  let q : D →* ↥(Subgroup.closure (Set.range g)) :=
    ((MonoidHom.fst Y Ghat).comp D.subtype).codRestrict _ hmem
  have hq : Function.Surjective q := by
    intro y
    have : (y : Y) ∈ D.map (MonoidHom.fst Y Ghat) := by rw [hmap₁]; exact y.2
    obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨d, hd⟩, Subtype.ext hdy⟩
  have hqinj : Function.Injective q := by
    have := q.normal_ker
    rcases hDsimp.eq_bot_or_eq_top_of_normal q.ker with hker | hker
    · exact (MonoidHom.ker_eq_bot_iff q).mp hker
    · exfalso
      obtain ⟨i, hi⟩ := hne
      have hfi : f i ∈ D := Subgroup.subset_closure ⟨i, rfl⟩
      have : (⟨f i, hfi⟩ : D) ∈ q.ker := by rw [hker]; trivial
      rw [MonoidHom.mem_ker] at this
      exact hi (congrArg Subtype.val this)
  exact ⟨(MulEquiv.ofBijective q ⟨hqinj, hq⟩).symm.trans ψ⟩

end WordTransfer

section Cert

theorem lieModel_of_mulEquiv_native {Y : Type} [Group Y] (e : Y ≃* Ghat) :
    LieModel Y .G2 0 3 1 := by
  have hc : AdjointQuotient .G2 (ZMod 3) ≃* Ghat :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := ZMod 3))).trans
      QuotientGroup.quotientBot
  refine Or.inr (Or.inl ⟨rfl, by simp [chevalleyExceptionalTags], ?_, ?_⟩)
  · exact ⟨Nat.prime_three, le_refl _, by norm_num, by norm_num⟩
  · exact ⟨ZMod 3, inferInstance, inferInstance, by simp, ⟨e.trans hc.symm⟩⟩

end Cert

end CFSG.GH74.QTGen4.Recog.G23
