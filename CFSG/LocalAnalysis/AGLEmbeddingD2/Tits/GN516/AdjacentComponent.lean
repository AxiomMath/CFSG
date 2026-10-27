module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.BaumComponent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.AdjacentImage
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.JoinTwoSubgroups
import CFSG.Quasithin.Background.C126NatDMin
import CFSG.Quasithin.EmptyFaithful.R3c21B
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFamData
import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin.B2F CFSG.Quasithin.E2
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem exists_hom_of_component {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    (hresJ : twoResidual H ≤ thompsonJ H)
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T)) :
    ∃ (ρ : ↥C →* MulAut (IntMod (VZ T H) hV)) (L : Subgroup (MulAut (IntMod (VZ T H) hV))),
      ⁅L, L⁆ = L ∧ L ≠ ⊥ ∧ L ≤ ρ.range ∧
        ∀ e : ↥C, (e : X ⧸ gnC T) ∈ twoResidual C → ρ e ∈ ⨆ L' ∈ I, L' := by
  set π := QuotientGroup.mk' (gnC T) with hπ
  have hHN : H ≤ Subgroup.normalizer (VZ T H : Set X) := le_normalizer_conjClosure _ H
  set S : Subgroup (MulAut (IntMod (VZ T H) hV)) := ⨆ L ∈ I, L with hSdef
  have hSJ : autI hV (thompsonJ H) = S := hFam.2.1
  have hperf : ∀ L ∈ I, ⁅L, L⁆ = L := fun L hL => by
    obtain ⟨n, hn, h⟩ := hn2 L hL
    exact Subgroup.isPerfect_iff.1 (R3c21.isPerfect_of_isL2Natural h hn)
  have hsimp : ∀ L ∈ I, ∀ N : Subgroup (MulAut (IntMod (VZ T H) hV)),
      L ≤ Subgroup.normalizer (N : Set (MulAut (IntMod (VZ T H) hV))) → L ⊓ N = ⊥ ∨ L ≤ N :=
    fun L hL N hLN => by
      obtain ⟨n, hn, h⟩ := hn2 L hL
      exact inf_eq_bot_or_le_of_isL2Natural h hn N hLN
  have hne0 : ∀ L ∈ I, L ≠ ⊥ := fun L hL => by
    obtain ⟨n, hn, h⟩ := hn2 L hL
    exact ne_bot_of_isL2Natural h hn
  have hLS : ∀ L ∈ I, L ≤ S := fun L hL => le_iSup₂ (f := fun L (_ : L ∈ I) => L) L hL
  have hSH : S ≤ autI hV H := hSJ ▸ autI_mono hV (C1GN.thompsonJ_le H)
  have hSres : S ≤ autI hV (twoResidual H) := iSup₂_le fun L hL =>
    (C126.Nat.le_twoResidual_of_perfect ((hLS L hL).trans hSH) (hperf L hL)).trans
      (R3c21.twoResidual_autI_le_autI_twoResidual hV)
  have hSn : autI hV H ≤ Subgroup.normalizer (S : Set (MulAut (IntMod (VZ T H) hV))) := by
    rw [← hSJ]
    exact autI_le_normalizer_autI' hV
      (Subgroup.le_normalizer.trans (GammaExtra.normalizer_le_normalizer_thompsonJ H))
  have hSab : ¬ S ≤ Subgroup.centralizer (S : Set (MulAut (IntMod (VZ T H) hV))) := by
    intro h
    obtain ⟨L₀, hL₀⟩ := hFam.1
    apply hne0 L₀ hL₀
    have h1 : ⁅L₀, L₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2
      ((hLS L₀ hL₀).trans (h.trans (Subgroup.centralizer_le (hLS L₀ hL₀))))
    rw [← hperf L₀ hL₀, h1]
  set K : Subgroup X := H ⊓ C.comap π with hKdef
  set Q : Subgroup (MulAut (IntMod (VZ T H) hV)) := autI hV K with hQdef
  have hON : twoResidual H ≤ Subgroup.normalizer (K : Set X) := by
    intro g hg
    have hgH : g ∈ H := twoResidual_le H hg
    have hgC : π g ∈ Subgroup.normalizer (C : Set (X ⧸ gnC T)) := hCN ⟨g, hg, rfl⟩
    have hgC' : g ∈ Subgroup.normalizer ((C.comap π : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff] at hgC ⊢
      intro x
      simp only [Subgroup.mem_comap, map_mul, map_inv]
      exact hgC (π x)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hgH, hgC'⟩
  have hSQ : S ≤ Subgroup.normalizer (Q : Set (MulAut (IntMod (VZ T H) hV))) :=
    hSres.trans (autI_le_normalizer_autI' hV hON)
  have hQS : Q ≤ Subgroup.normalizer (S : Set (MulAut (IntMod (VZ T H) hV))) :=
    (autI_mono hV inf_le_left).trans hSn
  have hne : ⁅S, Q⁆ ≠ ⊥ := commutator_ne_bot_of_le_conjClosure hTH hV hSn hSres hSab hCH hgen
  obtain ⟨L, hL, hLQ⟩ := exists_mem_le_of_commutator_ne_bot hFam.2.2.1 hperf hsimp hSQ hQS hne
  have hKN : K ≤ Subgroup.normalizer (VZ T H : Set X) := inf_le_left.trans hHN
  let π' : ↥K →* ↥C := (π.comp K.subtype).codRestrict C (fun k => k.2.2)
  have hπ' : Function.Surjective π' := by
    intro c
    obtain ⟨h, hh, hhc⟩ := hCH c.2
    exact ⟨⟨h, hh, Subgroup.mem_comap.2 (hhc ▸ c.2)⟩, Subtype.ext hhc⟩
  let ρ₁ : ↥K →* MulAut (IntMod (VZ T H) hV) := convHom hV K hKN
  have hker : π'.ker ≤ ρ₁.ker := by
    intro k hk
    have hk1 : π (k : X) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hk)
    have hkC : (k : X) ∈ gnC T := (QuotientGroup.eq_one_iff _).1 hk1
    exact (MonoidHom.mem_ker).2 ((convI_eq_one_iff hV _).2 (gnC_le_centralizer_vZ T H hkC))
  let ρ : ↥C →* MulAut (IntMod (VZ T H) hV) := MonoidHom.liftOfSurjective π' hπ' ⟨ρ₁, hker⟩
  have hρ : ∀ k : ↥K, ρ (π' k) = ρ₁ k := fun k => by simp [ρ]
  have hrange : L ≤ ρ.range := by
    intro φ hφ
    obtain ⟨g, hgK, rfl⟩ := (mem_autI hV).1 (hLQ hφ)
    exact ⟨π' ⟨g, hgK⟩, (hρ ⟨g, hgK⟩).trans rfl⟩
  have hKC : K.map π = C := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact hk.2
    · intro c hc
      obtain ⟨h, hh, hhc⟩ := hCH hc
      exact ⟨h, ⟨hh, Subgroup.mem_comap.2 (hhc ▸ hc)⟩, hhc⟩
  have hS : ∀ e : ↥C, (e : X ⧸ gnC T) ∈ twoResidual C → ρ e ∈ S := by
    intro e he
    have he' : (e : X ⧸ gnC T) ∈ (twoResidual K).map π := by
      rw [E1.map_twoResidual, hKC]; exact he
    obtain ⟨k, hk, hke⟩ := he'
    have hkK : k ∈ K := twoResidual_le K hk
    have hkH : k ∈ twoResidual H := E1.twoResidual_mono (inf_le_left : K ≤ H) hk
    have hpre : π' ⟨k, hkK⟩ = e := Subtype.ext hke
    have h1 : ρ e = convI hV ⟨k, hKN hkK⟩ := by
      rw [← hpre, hρ]; rfl
    rw [h1, ← hSJ]
    exact autI_mono hV hresJ (convI_mem_autI hV hkH (hKN hkK))
  exact ⟨ρ, L, hperf L hL, hne0 L hL, hrange, hS⟩

theorem false_of_quasisimple_mod_component {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    (hresJ : twoResidual H ≤ thompsonJ H)
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T))
    (N : Subgroup ↥(twoResidual C)) [N.Normal] (hN : IsPGroup 2 N)
    (hperf : commutator (↥(twoResidual C) ⧸ N) = ⊤)
    (hsimple : IsSimpleGroup ((↥(twoResidual C) ⧸ N) ⧸ Subgroup.center (↥(twoResidual C) ⧸ N)))
    (hodd : ∀ z ∈ Subgroup.center (↥(twoResidual C) ⧸ N), Odd (orderOf z))
    (P : Subgroup (↥(twoResidual C) ⧸ N)) (hP : IsPGroup 2 P)
    (hnon : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : False := by
  obtain ⟨ρ, L, hLp, hLne, hLr, hS⟩ := exists_hom_of_component hTH hV hFam hn2 hresJ hCH hCN hgen
  exact false_of_quasisimple_mod_image C N hN hperf hsimple hodd P hP hnon ρ _ hS
    (fun Q hQS hQ2 => comm_of_isPGroup_le_iSup_of_fam hFam
      (fun L hL => (hn2 L hL).imp fun _ h => h.2) hQ2 hQS) hLp hLne hLr

theorem false_of_solvable_component {H : Subgroup X} (hTH : T ≤ H)
    (hV : IsElemAbelian 2 (VZ T H)) {I : Finset (Subgroup (MulAut (IntMod (VZ T H) hV)))}
    (hFam : E23FamGen H T (VZ T H) hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n)
    (hresJ : twoResidual H ≤ thompsonJ H)
    {C : Subgroup (X ⧸ gnC T)} (hCH : C ≤ gnImg T H)
    (hCN : gnImg T (twoResidual H) ≤ Subgroup.normalizer (C : Set (X ⧸ gnC T)))
    (hgen : gnImg T (twoResidual H) ≤ conjClosure C (gnImg T T))
    (hsolv : Group.IsSolvable ↥C) : False := by
  obtain ⟨ρ, L, hLp, hLne, hLr, -⟩ := exists_hom_of_component hTH hV hFam hn2 hresJ hCH hCN hgen
  have hr : Group.IsSolvable ↥ρ.range :=
    solvable_of_surjective (MonoidHom.rangeRestrict_surjective ρ)
  have hL : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLr)
      (Subgroup.inclusion_injective hLr)
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 hLp
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).2 hLne
  exact Group.IsPerfect.not_isSolvable ↥L hL

end CFSG.AGLEmbeddingD2.Tits.GN516
