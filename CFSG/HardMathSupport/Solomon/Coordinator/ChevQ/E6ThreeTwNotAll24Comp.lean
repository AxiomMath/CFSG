module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LieType.Seitz

namespace KSNotAll24

section Restrict

variable {X : Type} [Group X]

@[expose] def resAut (J : Subgroup X) (g : MulAut X) (hg : J.map g.toMonoidHom = J) :
    MulAut J :=
  (MulEquiv.subgroupMap g J).trans (MulEquiv.subgroupCongr hg)

@[expose] def resHom (J : Subgroup X) (E : Subgroup (MulAut X))
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) : ↥E →* MulAut J where
  toFun g := resAut J g.1 (hJE g.1 g.2)
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

end Restrict

section Gen

variable {J : Type} [Group J] [Finite J]

theorem closure_fixed_eq_top (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hJ : commutator J = ⊤) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (d : TauCeti.ValidLieTypeIndex)
    (e : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hdp : 3 ≠ d.1.characteristic) (hex : ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (D : Subgroup (MulAut J)) (hD : CFSG.Open.IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2) :
    Subgroup.closure {x : J | ∃ δ ∈ D, δ ≠ 1 ∧ δ x = x} = ⊤ := by
  classical
  have hinj := quotCenterHom_injective hJ
  have hD' : CFSG.Open.IsElemAbelian 3 (D.map (quotCenterHom J)) :=
    CFSG.SectionRank.isElemAbelian_map hD (quotCenterHom J)
  have hDc' : Nat.card (D.map (quotCenterHom J)) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hDc
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) d e hdp hex hD' hDc'
  set H : Subgroup J := Subgroup.closure {x : J | ∃ δ ∈ D, δ ≠ 1 ∧ δ x = x} with hH
  have hle : Subgroup.closure {s : J ⧸ Subgroup.center J |
      ∃ f ∈ D.map (quotCenterHom J), f ≠ 1 ∧ f s = s} ≤ H.map (QuotientGroup.mk' _) := by
    rw [Subgroup.closure_le]
    rintro s ⟨_, ⟨δ, hδ, rfl⟩, hδ1, hδs⟩
    induction s using QuotientGroup.induction_on with | H x => ?_
    have hδ1' : δ ≠ 1 := fun h => hδ1 (by rw [h, map_one])
    rw [quotCenterHom_mk] at hδs
    have hx : (δ x)⁻¹ * x ∈ Subgroup.center J := QuotientGroup.eq.1 hδs
    obtain ⟨w, hw, hxw⟩ := exists_fixed_mul_center δ (hD.2 δ hδ) hZ x hx
    refine ⟨x * w, Subgroup.subset_closure ⟨δ, hδ, hδ1', hxw⟩, ?_⟩
    show (QuotientGroup.mk (x * w) : J ⧸ Subgroup.center J) = QuotientGroup.mk x
    exact (QuotientGroup.eq.2 (by simpa using inv_mem hw))
  rw [hgen] at hle
  refine eq_top_of_mul_center hJ ?_
  intro y
  obtain ⟨h, hh, hhy⟩ := hle (Subgroup.mem_top (QuotientGroup.mk y))
  refine ⟨h, hh, h⁻¹ * y, ?_, by group⟩
  exact QuotientGroup.eq.1 hhy

end Gen

section Main

variable {X : Type} [Group X]

theorem isElemAbelian_range {p : ℕ} {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian p E)
    {M : Type*} [Group M] (ρ : ↥E →* M) : CFSG.Open.IsElemAbelian p ρ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨g, hg⟩ := a.2
    obtain ⟨h, hh⟩ := b.2
    apply Subtype.ext
    show (a : M) * b = b * a
    rw [← hg, ← hh, ← map_mul, ← map_mul]
    congr 1
    exact hE.1.is_comm.comm g h
  · obtain ⟨g, rfl⟩ := hx
    rw [← map_pow]
    have : g ^ p = 1 := Subtype.ext (hE.2 g.1 g.2)
    rw [this, map_one]

theorem fixedPoints_le_hyperGamma {E F : Subgroup (MulAut X)} (hFE : F ≤ E)
    (hrel : F.relIndex E = 3) : fixedPoints F ≤ seitzHyperGamma 3 E :=
  le_iSup₂_of_le (f := fun (F : Subgroup (MulAut X)) (_ : F ≤ E ∧ F.relIndex E = 3) =>
    fixedPoints F) F ⟨hFE, hrel⟩ le_rfl

end Main

end KSNotAll24

open KSNotAll24 in
theorem component_le_hyperGamma_of_plane (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    {X : Type} [Group X] [Finite X]
    (E : Subgroup (MulAut X)) (hE : CFSG.Open.IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3)
    (f : MulAut X) (hf : f ∈ E) (hf1 : f ≠ 1)
    (J : Subgroup X) (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)))
    (hJ3 : ¬ 3 ∣ Nat.card (Subgroup.center J))
    (d : TauCeti.ValidLieTypeIndex)
    (e : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hdp : 3 ≠ d.1.characteristic) (hex : ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (hJE : ∀ g ∈ E, J.map g.toMonoidHom = J) :
    J ≤ seitzHyperGamma 3 E := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJfix : ∀ g ∈ Subgroup.zpowers f, ∀ y ∈ J, g y = y := fun g hg y hy => hJ.1 hy g hg
  have hperf : commutator J = ⊤ := hJ.2.2.1
  set ρ : ↥E →* MulAut J := resHom J E hJE with hρ
  have hρker : ∀ g : ↥E, g ∈ ρ.ker → ∀ y ∈ J, g.1 y = y := by
    intro g hg y hy
    have h : ρ g = 1 := MonoidHom.mem_ker.1 hg
    exact congrArg (fun φ : MulAut J => ((φ ⟨y, hy⟩ : J) : X)) h
  have hfker : (⟨f, hf⟩ : ↥E) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    ext y
    exact hJfix f (Subgroup.mem_zpowers f) y y.2
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = 3 ^ 3 := by
    rw [Subgroup.card_ker_mul_card_range, hEc]
  by_cases hD9 : Nat.card ρ.range = 3 ^ 2
  ·
    have hgen := closure_fixed_eq_top hS hperf hJ3 d e hdp hex ρ.range
      (isElemAbelian_range hE ρ) hD9
    have hsub : {x : J | ∃ δ ∈ ρ.range, δ ≠ 1 ∧ δ x = x} ⊆
        ((seitzHyperGamma 3 E).subgroupOf J : Set J) := by
      rintro x ⟨_, ⟨g, rfl⟩, hg1, hgx⟩
      have hgf : g.1 ∉ Subgroup.zpowers f := by
        intro hmem
        apply hg1
        ext y
        exact hJfix g.1 hmem y y.2
      have hf3 : f ^ 3 = 1 := hE.2 f hf
      have hg3 : g.1 ^ 3 = 1 := hE.2 g.1 g.2
      have hcomm : Commute f g.1 := congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ g)
      have hFc := card_zpowers_sup_zpowers hcomm hf1 hf3 hg3 hgf
      have hFE : Subgroup.zpowers f ⊔ Subgroup.zpowers g.1 ≤ E :=
        sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 g.2)
      have hxf : f x.1 = x.1 := hJfix f (Subgroup.mem_zpowers f) x x.2
      have hxg : g.1 x.1 = x.1 := congrArg Subtype.val hgx
      have hxfix : x.1 ∈ fixedPoints (Subgroup.zpowers f ⊔ Subgroup.zpowers g.1) := by
        have hle : Subgroup.zpowers f ⊔ Subgroup.zpowers g.1 ≤
            MulAction.stabilizer (MulAut X) x.1 :=
          sup_le (Subgroup.zpowers_le.2 hxf) (Subgroup.zpowers_le.2 hxg)
        intro φ hφ
        exact hle hφ
      exact fixedPoints_le_hyperGamma hFE (relIndex_eq_three hFE hEc hFc) hxfix
    intro y hy
    have h1 : (⟨y, hy⟩ : J) ∈ (⊤ : Subgroup J) := Subgroup.mem_top _
    rw [← hgen] at h1
    exact ((Subgroup.closure_le _).2 hsub) h1
  ·
    have hker1 : Nat.card ρ.ker ≠ 1 := by
      intro h1
      have h2 := Subgroup.card_eq_one.1 h1
      rw [h2] at hfker
      exact hf1 (congrArg Subtype.val (Subgroup.mem_bot.1 hfker))
    have hkerdvd : 3 ^ 2 ∣ Nat.card ρ.ker := by
      have hDdvd : Nat.card ρ.range ∣ 3 ^ 3 := Dvd.intro_left _ hcard
      obtain ⟨i, hi, hDi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hDdvd
      rw [hDi] at hcard
      interval_cases i
      · norm_num at hcard ⊢
        omega
      · norm_num at hcard ⊢
        omega
      · exact absurd hDi hD9
      · norm_num at hcard
        exact absurd hcard hker1
    obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ρ.ker) 3 hkerdvd
    set F : Subgroup (MulAut X) := (K₀.map ρ.ker.subtype).map E.subtype with hF
    have hFc : Nat.card F = 3 ^ 2 := by
      rw [hF, Subgroup.card_map_of_injective E.subtype_injective,
        Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK₀]
    have hFE : F ≤ E := Subgroup.map_subtype_le _
    have hFfix : J ≤ fixedPoints F := by
      intro y hy φ hφ
      rw [hF, Subgroup.mem_map] at hφ
      obtain ⟨a, ha, rfl⟩ := hφ
      rw [Subgroup.mem_map] at ha
      obtain ⟨b, -, rfl⟩ := ha
      exact hρker _ b.2 y hy
    exact hFfix.trans (fixedPoints_le_hyperGamma hFE (relIndex_eq_three hFE hEc hFc))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
