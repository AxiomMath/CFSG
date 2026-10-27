module

public import CFSG.GH74.GLS.Stage2.Local.P27.S45E
import CFSG.GH74.GLS.Stage2.Local.Prop28Good
import CFSG.GH74.GLS.Stage2.Local.P34S5Frat
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAssembly
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.GH74.GLS.Stage2.Local.P34S5Clo
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

variable {G : Type} [Group G]

abbrev OX (t : G) : Subgroup ↥(centralizer ({t} : Set G)) := pPrimeCore 2 ↥(centralizer ({t} : Set G))

abbrev KX (t : G) : Subgroup ↥(centralizer ({t} : Set G)) := (Jx t).subgroupOf (centralizer ({t} : Set G))

theorem KX_normal [Finite G] (t : G) : (KX t).Normal := by
  refine ⟨fun k hk n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  exact P34.Jx_normalized t n n.2 k hk

theorem OX_odd [Finite G] (t : G) : Odd (Nat.card (OX t)) :=
  Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(centralizer ({t} : Set G))))

theorem OX_subgroupOf_eq [Finite G] (t : G) : (OX t).subgroupOf (KX t) = pPrimeCore 2 ↥(KX t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKn := KX_normal t
  apply le_antisymm
  ·
    refine le_sSup ⟨Subgroup.Normal.subgroupOf inferInstance _, ?_⟩
    have h1 : Nat.card ↥(((OX t).subgroupOf (KX t)).map (KX t).subtype) ∣ Nat.card ↥(OX t) :=
      Subgroup.card_dvd_of_le (by rintro _ ⟨k, hk, rfl⟩; exact hk)
    rw [Subgroup.card_map_of_injective (KX t).subtype_injective] at h1
    exact Nat.Coprime.of_dvd_right h1 (Nat.coprime_two_left.2 (OX_odd t))
  ·
    set N' : Subgroup ↥(centralizer ({t} : Set G)) := (pPrimeCore 2 ↥(KX t)).map (KX t).subtype with hN'
    have hN'n : N'.Normal := by
      refine ⟨fun n hn x => ?_⟩
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
      have h1 := pPrimeCore_map_iso 2 (MulAut.conjNormal (H := KX t) x)
      have hm' : (MulAut.conjNormal (H := KX t) x) m ∈ pPrimeCore 2 ↥(KX t) := by
        rw [← h1]; exact Subgroup.mem_map_of_mem _ hm
      refine Subgroup.mem_map.2 ⟨_, hm', ?_⟩
      simp [MulAut.conjNormal_apply]
    have hN'c : Nat.Coprime 2 (Nat.card N') := by
      rw [hN', Subgroup.card_map_of_injective (KX t).subtype_injective]
      exact pPrimeCore_coprime_card
    have hle : N' ≤ OX t := le_sSup ⟨hN'n, hN'c⟩
    intro m hm
    rw [Subgroup.mem_subgroupOf]
    exact hle (Subgroup.mem_map_of_mem _ hm)

theorem KXb_equiv [Finite G] (t : G) :
    Nonempty (↥((KX t).map (QuotientGroup.mk' (OX t))) ≃* (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t))) := by
  set π : ↥(centralizer ({t} : Set G)) →* ↥(centralizer ({t} : Set G)) ⧸ OX t := QuotientGroup.mk' (OX t)
  let f : ↥(KX t) →* ↥(centralizer ({t} : Set G)) ⧸ OX t := π.comp (KX t).subtype
  have hker : f.ker = (OX t).subgroupOf (KX t) := by
    ext k
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hrange : f.range = (KX t).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e₁ : (↥(KX t) ⧸ f.ker) ≃* ↥f.range := QuotientGroup.quotientKerEquivRange f
  let e₁' : ↥((KX t).map π) ≃* (↥(KX t) ⧸ (OX t).subgroupOf (KX t)) :=
    (MulEquiv.subgroupCongr hrange.symm).trans
      (e₁.symm.trans (QuotientGroup.quotientMulEquivOfEq hker))
  let e₂ : (↥(KX t) ⧸ (OX t).subgroupOf (KX t)) ≃* (↥(KX t) ⧸ pPrimeCore 2 ↥(KX t)) :=
    QuotientGroup.quotientMulEquivOfEq (OX_subgroupOf_eq t)
  have hle : KX t ≤ KX t := le_rfl
  let ι : ↥(KX t) ≃* ↥(Jx t) :=
    Subgroup.subgroupOfEquivOfLe (P34.Jx_le_centralizer t : Jx t ≤ centralizer ({t} : Set G))
  let e₃ : (↥(KX t) ⧸ pPrimeCore 2 ↥(KX t)) ≃* (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t)) :=
    QuotientGroup.congr (pPrimeCore 2 ↥(KX t)) (pPrimeCore 2 ↥(Jx t)) ι (pPrimeCore_map_iso 2 ι)
  exact ⟨e₁'.trans (e₂.trans e₃)⟩

theorem isSolvable_of_hasNormal2Compl [Finite G] {Y : Subgroup G} (h : HasNormal2Compl Y) :
    Group.IsSolvable ↥Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNY, hNn, hNodd, a, ha⟩ := h
  have h1 : Group.IsSolvable ↥(N.subgroupOf Y) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv]
    exact hNodd
  have hp : IsPGroup 2 (↥Y ⧸ N.subgroupOf Y) := by
    rw [IsPGroup.iff_card]
    exact ⟨a, by rw [← Subgroup.index, ha]⟩
  have h2 : Group.IsSolvable (↥Y ⧸ N.subgroupOf Y) := by
    have := hp.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf Y).subtype (QuotientGroup.mk' (N.subgroupOf Y))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

abbrev Ctil (t : G) : Subgroup ↥(centralizer ({t} : Set G)) :=
  (Subgroup.centralizer (((KX t).map (QuotientGroup.mk' (OX t)) : Subgroup _) : Set _)).comap
    (QuotientGroup.mk' (OX t))

theorem Ctil_le [Finite G] (t : G) :
    Ctil t ≤ (CxK t (Jx t)).subgroupOf (centralizer ({t} : Set G)) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hx' : ∀ k ∈ KX t, QuotientGroup.mk' (OX t) x * QuotientGroup.mk' (OX t) k =
      QuotientGroup.mk' (OX t) k * QuotientGroup.mk' (OX t) x := fun k hk =>
    ((Subgroup.mem_centralizer_iff.1 hx) _ (Subgroup.mem_map_of_mem _ hk)).symm
  have hxJ : (x : G) ∈ normalizer ((Jx t : Subgroup G) : Set G) :=
    CFSG.GH74.GLS.Stage2.Local.P27.S45.mem_normalizer_Jx x.2
  refine ⟨x.2, hxJ, TwoThin.mem_normalizer_pPrimeCoreOf hxJ, fun k hk => ?_⟩
  have hkc : k ∈ centralizer ({t} : Set G) := P34.Jx_le_centralizer t hk
  set kX : ↥(centralizer ({t} : Set G)) := ⟨k, hkc⟩ with hkX
  have hkK : kX ∈ KX t := Subgroup.mem_subgroupOf.2 hk
  have hKn := KX_normal t
  have hcK : ⁅kX, x⁆ ∈ KX t := by
    have : ⁅kX, x⁆ = kX * (x * kX⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact (KX t).mul_mem hkK (hKn.conj_mem _ ((KX t).inv_mem hkK) x)
  have hcO : ⁅kX, x⁆ ∈ OX t := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 := hx' kX hkK
    have h2 : ⁅QuotientGroup.mk' (OX t) kX, QuotientGroup.mk' (OX t) x⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    rw [← h2]
    exact map_commutatorElement (QuotientGroup.mk' (OX t)) kX x
  have hc0 : (⟨⁅kX, x⁆, hcK⟩ : ↥(KX t)) ∈ pPrimeCore 2 ↥(KX t) := by
    rw [← OX_subgroupOf_eq t]
    exact Subgroup.mem_subgroupOf.2 hcO
  let ι : ↥(KX t) ≃* ↥(Jx t) :=
    Subgroup.subgroupOfEquivOfLe (P34.Jx_le_centralizer t : Jx t ≤ centralizer ({t} : Set G))
  have hc1 : ι ⟨⁅kX, x⁆, hcK⟩ ∈ pPrimeCore 2 ↥(Jx t) := by
    rw [← pPrimeCore_map_iso 2 ι]
    exact Subgroup.mem_map_of_mem _ hc0
  refine Subgroup.mem_map.2 ⟨_, hc1, ?_⟩
  simp [ι, hkX, commutatorElement_def]

theorem Ctil_solvable [Finite G] (t : G) (he : HasNormal2Compl (CxK t (Jx t))) :
    Group.IsSolvable ↥(Ctil t) := by
  have hC₁ : Group.IsSolvable ↥(CxK t (Jx t)) := isSolvable_of_hasNormal2Compl he
  have hle : CxK t (Jx t) ≤ centralizer ({t} : Set G) := CFSG.GH74.GLS.Stage2.Local.P27.S45.CxK_Jx_le t
  have h1 : Group.IsSolvable ↥((CxK t (Jx t)).subgroupOf (centralizer ({t} : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).injective
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (Ctil_le t))

theorem le_OX_of_le_Ctil [Finite G] {t : G} (he : HasNormal2Compl (CxK t (Jx t)))
    {Q : Subgroup ↥(centralizer ({t} : Set G))} (hQ : Q ≤ Ctil t) (hQodd : Odd (Nat.card Q)) :
    Q ≤ OX t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N₀, hN₀C, hN₀n, hN₀odd, a, ha⟩ := he
  have hC₁X : CxK t (Jx t) ≤ centralizer ({t} : Set G) := CFSG.GH74.GLS.Stage2.Local.P27.S45.CxK_Jx_le t
  set C₁X : Subgroup ↥(centralizer ({t} : Set G)) := (CxK t (Jx t)).subgroupOf (centralizer ({t} : Set G)) with hC₁Xdef
  set N₀X : Subgroup ↥(centralizer ({t} : Set G)) := N₀.subgroupOf (centralizer ({t} : Set G)) with hN₀Xdef
  have hN₀XC : N₀X ≤ C₁X := fun n hn => hN₀C hn
  have hnorm : ∀ c ∈ CxK t (Jx t), ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀ := by
    intro c hc n hn
    have := hN₀n.conj_mem (⟨n, hN₀C hn⟩ : ↥(CxK t (Jx t))) (Subgroup.mem_subgroupOf.2 hn) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hN₀Xn : (N₀X.subgroupOf C₁X).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' : ((n : ↥C₁X) : ↥(centralizer ({t} : Set G))).1 ∈ N₀ := hn
    exact hnorm _ c.2 _ hn'
  have hC₁Xn : C₁X.Normal := by
    refine ⟨fun c hc x => ?_⟩
    have hc' : ((c : ↥(centralizer ({t} : Set G))) : G) ∈ CxK t (Jx t) := hc
    exact CFSG.GH74.GLS.Stage2.Local.P27.S45.CxK_Jx_conj_mem x.2 hc'
  have hsub : N₀X.IsSubnormal :=
    Subgroup.IsSubnormal.step N₀X C₁X hN₀XC
      (Subgroup.IsSubnormal.step C₁X ⊤ le_top Subgroup.IsSubnormal.top
        (Subgroup.Normal.subgroupOf hC₁Xn _)) hN₀Xn
  have hcop : Nat.Coprime 2 (Nat.card N₀X) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hN₀C.trans hC₁X)).toEquiv]
    exact Nat.coprime_two_left.2 hN₀odd
  have hN₀O : N₀X ≤ OX t := le_pPrimeCore_of_subnormal 2 hsub hcop
  intro q hq
  apply hN₀O
  have hqC : q ∈ C₁X := Ctil_le t (hQ hq)
  have hord : orderOf (⟨q, hqC⟩ : ↥C₁X) ∣ Nat.card ↥Q := by
    have h1 : orderOf q ∣ Nat.card ↥Q := by
      have := orderOf_dvd_natCard (⟨q, hq⟩ : ↥Q)
      rwa [Subgroup.orderOf_mk] at this
    rwa [Subgroup.orderOf_mk]
  set M₀ : Subgroup ↥C₁X := N₀X.subgroupOf C₁X with hM₀
  have hcardq : Nat.card (↥C₁X ⧸ M₀) = 2 ^ a := by
    have h1 : M₀.index = (N₀.subgroupOf (CxK t (Jx t))).index := by
      have := Subgroup.relIndex_subgroupOf (H := N₀) hC₁X
      exact this
    rw [← Subgroup.index, h1, ha]
  have hn : (QuotientGroup.mk ⟨q, hqC⟩ : ↥C₁X ⧸ M₀) = 1 := by
    set g : ↥C₁X ⧸ M₀ := QuotientGroup.mk ⟨q, hqC⟩
    have h1 : orderOf g ∣ Nat.card (↥C₁X ⧸ M₀) := orderOf_dvd_natCard g
    have h2 : orderOf g ∣ orderOf (⟨q, hqC⟩ : ↥C₁X) := orderOf_map_dvd (QuotientGroup.mk' M₀) _
    have h3 : orderOf g ∣ Nat.card ↥Q := h2.trans hord
    rw [hcardq] at h1
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hodd : Odd (orderOf g) := Odd.of_dvd_nat hQodd h3
    have hk0 : k = 0 := by
      by_contra hne
      have : Even (orderOf g) := by
        rw [hk']; exact (Nat.even_pow.2 ⟨even_two, hne⟩)
      exact (Nat.not_even_iff_odd.2 hodd) this
    rw [hk0, pow_zero] at hk'
    exact orderOf_eq_one_iff.1 hk'
  have := (QuotientGroup.eq_one_iff _).1 hn
  exact this

theorem outer_solvable_of_isL2 {X : Type} [Group X] {r : ℕ} (hr3 : 3 < r)
    (h : IVK.IsL2 X (fun s => s = r)) : Group.IsSolvable (Outer X) := by
  obtain ⟨p, f, -, -, -, hLie⟩ := Prop28.lieModel_of_isL2 hr3 h
  rcases hLie with ⟨-, hm⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
  · exact CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable hm
  all_goals exact absurd hn (by norm_num)

theorem KXb_simple_outer [Finite G] {t : G} {q : ℕ} (hq : 3 < q)
    (hc : CFSG.GH74.GLS.Stage2.Local.P27.FullCL4 t q) :
    IsSimpleGroup ↥((KX t).map (QuotientGroup.mk' (OX t))) ∧
      Group.IsSolvable (Outer ↥((KX t).map (QuotientGroup.mk' (OX t)))) := by
  obtain ⟨e⟩ := KXb_equiv t
  have hq2 : 3 < q ^ 2 := by nlinarith
  rcases hc with hL2 | ⟨hq5, hA7⟩
  · have hs : IsSimpleGroup (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t)) := Prop28.isSimpleGroup_of_isL2 hq2 hL2
    have ho := outer_solvable_of_isL2 hq2 hL2
    exact ⟨(e.isSimpleGroup_congr).2 hs, solvable_of_equiv e.symm⟩
  · have hs : IsSimpleGroup (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t)) := Prop28.isSimpleGroup_of_A7 (by
      obtain ⟨f⟩ := hA7
      subst hq5
      exact ⟨f⟩)
    have ho : Group.IsSolvable (Outer (↥(Jx t) ⧸ pPrimeCore 2 ↥(Jx t))) := by
      obtain ⟨f⟩ := hA7
      exact CFSG.ComponentClassification.CatalogueSchreierAlternating.outer_solvable_of_equiv_outside_six
        (n := 7) (Or.inr le_rfl) f
    exact ⟨(e.isSimpleGroup_congr).2 hs, solvable_of_equiv e.symm⟩

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
