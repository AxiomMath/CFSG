module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

section SolvableStrip

variable {H S : Type} [Group H] [Group S]

theorem le_ker_of_solvable_normal [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S) (N : Subgroup H) [N.Normal]
    (hN : Group.IsSolvable ↥N) (f : H →* S) (hf : Function.Surjective f) : N ≤ f.ker := by
  have hnorm : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hsolv : Group.IsSolvable ↥(N.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap N) (f.subgroupMap_surjective N)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with hb | ht
  · intro n hn
    have : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
    rw [hb, Subgroup.mem_bot] at this
    exact this
  · exfalso
    apply hns
    have : Group.IsSolvable ↥(⊤ : Subgroup S) := by rw [← ht]; exact hsolv
    exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.topEquiv (G := S)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := S)).symm.injective

theorem surjective_restrict_of_solvable_quotient [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S)
    (N : Subgroup H) [N.Normal] (hq : Group.IsSolvable (H ⧸ N)) (f : H →* S)
    (hf : Function.Surjective f) : Function.Surjective (f.comp N.subtype) := by
  have hnorm : (N.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with hb | ht
  · exfalso
    apply hns
    have hle : N ≤ f.ker := by
      intro n hn
      have : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
      rw [hb, Subgroup.mem_bot] at this
      exact this
    let g : H ⧸ N →* S := QuotientGroup.lift N f hle
    have hg : Function.Surjective g := by
      intro s
      obtain ⟨h, rfl⟩ := hf s
      exact ⟨QuotientGroup.mk h, rfl⟩
    exact Group.isSolvable_of_surjective hg
  · intro s
    have : s ∈ N.map f := by rw [ht]; exact Subgroup.mem_top s
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨n, hn⟩, rfl⟩

end SolvableStrip

section Section

variable {G : Type} [Group G]

theorem section_lemma [Finite G] {M E : Subgroup G} {t : G}
    (hEn : ∀ m ∈ M, ∀ e ∈ E, m * e * m⁻¹ ∈ E) (htE : t ∈ E)
    (hZ : ∀ z ∈ E, (∀ e ∈ E, z * e = e * z) → z = 1)
    (hB : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer (E : Set G)))
    (hOut : Group.IsSolvable (Outer ↥E))
    {D : Subgroup G} (hD : D ≤ M ⊓ Subgroup.centralizer ({t} : Set G))
    {S : Type} [Group S] [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S)
    (f : ↥D →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup G, W ≤ E ⊓ Subgroup.centralizer ({t} : Set G) ∧ ∃ g : ↥W →* S, Function.Surjective g := by
  classical
  have hMN : ∀ m ∈ M, m ∈ Subgroup.normalizer (E : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro e
    refine ⟨fun he => hEn m hm e he, fun h => ?_⟩
    have := hEn m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this
  have hDN : D ≤ Subgroup.normalizer (E : Set G) := fun d hd => hMN d (hD hd).1
  let Φ : ↥D →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hDN)
  have hΦ : ∀ (d : ↥D) (e : ↥E), ((Φ d e : ↥E) : G) = (d : G) * (e : G) * (d : G)⁻¹ := fun d e => rfl
  have hker : (Φ.ker).map D.subtype ≤ M ⊓ Subgroup.centralizer (E : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hD d.2)).1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro e he
    have h1 := congrArg (fun a : MulAut ↥E => ((a ⟨e, he⟩ : ↥E) : G)) (MonoidHom.mem_ker.1 hd)
    simp only [hΦ, MulAut.one_apply] at h1
    have : (d : G) * e * (d : G)⁻¹ = e := h1
    show e * (d : G) = (d : G) * e
    calc e * (d : G) = ((d : G) * e * (d : G)⁻¹) * (d : G) := by rw [this]
      _ = (d : G) * e := by group
  have hNsolv : Group.IsSolvable ↥Φ.ker := by
    have : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer (E : Set G)) := hB
    have h1 : Group.IsSolvable ↥((Φ.ker).map D.subtype) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Φ.ker D.subtype D.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective Φ.ker D.subtype D.subtype_injective).injective
  have hkerf : Φ.ker ≤ f.ker := le_ker_of_solvable_normal hns Φ.ker hNsolv f hf
  let ψ : ↥D →* Outer ↥E := (QuotientGroup.mk' (inner ↥E)).comp Φ
  have hq : Group.IsSolvable (↥D ⧸ ψ.ker) := by
    have : Group.IsSolvable (Outer ↥E) := hOut
    exact Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective ψ)
  have hf₀ : Function.Surjective (f.comp ψ.ker.subtype) :=
    surjective_restrict_of_solvable_quotient hns ψ.ker hq f hf
  have hconj_inj : Function.Injective (MulAut.conj : ↥E →* MulAut ↥E) := by
    intro a b hab
    have h1 : ∀ x : ↥E, a * x * a⁻¹ = b * x * b⁻¹ := fun x => by
      have := congrArg (fun φ : MulAut ↥E => φ x) hab
      simpa using this
    have hc : (a⁻¹ * b : ↥E) ∈ Subgroup.center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h2 : (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹ = x := by
        calc (a⁻¹ * b) * x * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * x * b⁻¹) * a := by group
          _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [h1 x]
          _ = x := by group
      calc x * (a⁻¹ * b) = ((a⁻¹ * b) * x * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [h2]
        _ = (a⁻¹ * b) * x := by group
    have hz := hZ ((a⁻¹ * b : ↥E) : G) (a⁻¹ * b).2 (fun e he => by
      have := Subgroup.mem_center_iff.1 hc ⟨e, he⟩
      exact congrArg Subtype.val this.symm)
    have : a⁻¹ * b = 1 := Subtype.ext hz
    exact inv_mul_eq_one.1 this
  let ce : ↥E ≃* ↥(inner ↥E) := MonoidHom.ofInjective hconj_inj
  have hinner : ∀ d : ↥ψ.ker, Φ d ∈ inner ↥E := by
    intro d
    have := d.2
    rw [MonoidHom.mem_ker] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  let ρ1 : ↥ψ.ker →* ↥(inner ↥E) := (Φ.comp ψ.ker.subtype).codRestrict (inner ↥E) hinner
  let ρ : ↥ψ.ker →* ↥E := ce.symm.toMonoidHom.comp ρ1
  have hρ : ∀ d : ↥ψ.ker, (MulAut.conj (ρ d) : MulAut ↥E) = Φ d := by
    intro d
    have h1 : ce (ρ d) = ρ1 d := by
      show ce (ce.symm (ρ1 d)) = ρ1 d
      exact ce.apply_symm_apply _
    have h2 := congrArg (fun a : ↥(inner ↥E) => (a : MulAut ↥E)) h1
    exact h2
  have hρker : ρ.ker ≤ (f.comp ψ.ker.subtype).ker := by
    intro d hd
    have h1 : ρ d = 1 := hd
    have h2 : Φ d = 1 := by rw [← hρ d, h1, map_one]
    have h3 : (d : ↥D) ∈ Φ.ker := h2
    exact hkerf h3
  let g : ↥ρ.range →* S :=
    (QuotientGroup.lift ρ.ker (f.comp ψ.ker.subtype) hρker).comp
      (QuotientGroup.quotientKerEquivRange ρ).symm.toMonoidHom
  have hg : Function.Surjective g := by
    intro s
    obtain ⟨d, hd⟩ := hf₀ s
    refine ⟨⟨ρ d, d, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ d, d, rfl⟩ = QuotientGroup.mk d := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.lift ρ.ker (f.comp ψ.ker.subtype) hρker)
      ((QuotientGroup.quotientKerEquivRange ρ).symm ⟨ρ d, d, rfl⟩) = s
    rw [h1]
    exact hd
  refine ⟨ρ.range.map E.subtype, ?_, ?_⟩
  · rintro _ ⟨x, ⟨d, hdx⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := hρ d
    rw [hdx] at h1
    have h2 := congrArg (fun a : MulAut ↥E => ((a ⟨h, htE⟩ : ↥E) : G)) h1
    simp only [MulAut.conj_apply, hΦ] at h2
    have hdc : (d : G) * h = h * (d : G) :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hD (d : ↥D).2)).2)
    have h3 : (d : G) * h * (d : G)⁻¹ = h := by
      calc (d : G) * h * (d : G)⁻¹ = (h * (d : G)) * (d : G)⁻¹ := by rw [hdc]
        _ = h := by group
    have h4 : (x : G) * h * (x : G)⁻¹ = h := by
      have : ((x * ⟨h, htE⟩ * x⁻¹ : ↥E) : G) = h := h2.trans h3
      exact this
    show h * (x : G) = (x : G) * h
    calc h * (x : G) = ((x : G) * h * (x : G)⁻¹) * (x : G) := by rw [h4]
      _ = (x : G) * h := by group
  · let eW : ↥ρ.range ≃* ↥(ρ.range.map E.subtype) :=
      Subgroup.equivMapOfInjective ρ.range E.subtype E.subtype_injective
    exact ⟨g.comp eW.symm.toMonoidHom, hg.comp eW.symm.surjective⟩

end Section

section Perfect

theorem isPerfect_of_simple_nonsolvable {S : Type} [Group S] [IsSimpleGroup S]
    (hns : ¬ Group.IsSolvable S) : Group.IsPerfect S := by
  have hn : (commutator S).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with hb | ht
  · exfalso
    apply hns
    exact ⟨⟨1, by rw [derivedSeries_one]; exact hb⟩⟩
  · exact ⟨ht⟩

variable {W S : Type} [Group W] [Finite W] [Group S]

theorem exists_perfect_surjective [Group.IsPerfect S] (g : W →* S) (hg : Function.Surjective g) :
    ∃ W₀ : Subgroup W, ⁅W₀, W₀⁆ = W₀ ∧ Function.Surjective (g.comp W₀.subtype) := by
  classical
  obtain ⟨m, hm⟩ := (Set.toFinite (Set.range (derivedSeries W))).exists_minimal
    ⟨derivedSeries W 0, ⟨0, rfl⟩⟩
  obtain ⟨n, rfl⟩ := hm.prop
  have hnext : derivedSeries W (n + 1) = derivedSeries W n :=
    hm.eq_of_le ⟨n + 1, rfl⟩ (derivedSeries_antitone W (Nat.le_succ n))
  refine ⟨derivedSeries W n, ?_, ?_⟩
  · rw [← derivedSeries_succ, hnext]
  · have himage := derivedSeries_le_map_derivedSeries hg n
    rw [Group.IsPerfect.derivedSeries_eq_top] at himage
    intro s
    have : s ∈ (derivedSeries W n).map g := himage (Subgroup.mem_top s)
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 this
    exact ⟨⟨w, hw⟩, rfl⟩

end Perfect

section HSec

variable {G : Type} [Group G]

theorem hsec_of_perfect [Finite G] {t : G} {M E I : Subgroup G}
    (hEn : ∀ m ∈ M, ∀ e ∈ E, m * e * m⁻¹ ∈ E) (htE : t ∈ E)
    (hZ : ∀ z ∈ E, (∀ e ∈ E, z * e = e * z) → z = 1)
    (hB : Group.IsSolvable ↥(M ⊓ Subgroup.centralizer (E : Set G)))
    (hOut : Group.IsSolvable (Outer ↥E))
    {S : Type} [Group S] [IsSimpleGroup S] (hns : ¬ Group.IsSolvable S)
    (hI : ∀ N : Subgroup G, N ≤ E ⊓ Subgroup.centralizer ({t} : Set G) → ⁅N, N⁆ = N → N ≤ I)
    (hcard : ¬ Nat.card S ∣ Nat.card ↥I) :
    ∀ D : Subgroup ↥(Subgroup.centralizer ({t} : Set G)),
      D ≤ (M ⊓ Subgroup.centralizer ({t} : Set G)).subgroupOf (Subgroup.centralizer ({t} : Set G)) →
      ∀ f : ↥D →* S, ¬ Function.Surjective f := by
  intro D hD f hf
  have hD'le : D.map (Subgroup.centralizer ({t} : Set G)).subtype ≤ M ⊓ Subgroup.centralizer ({t} : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hD hd
  let e : ↥D ≃* ↥(D.map (Subgroup.centralizer ({t} : Set G)).subtype) :=
    Subgroup.equivMapOfInjective D (Subgroup.centralizer ({t} : Set G)).subtype
      (Subgroup.centralizer ({t} : Set G)).subtype_injective
  let f' : ↥(D.map (Subgroup.centralizer ({t} : Set G)).subtype) →* S := f.comp e.symm.toMonoidHom
  have hf' : Function.Surjective f' := hf.comp e.symm.surjective
  obtain ⟨W, hW, g, hg⟩ := section_lemma hEn htE hZ hB hOut hD'le hns f' hf'
  have : Group.IsPerfect S := isPerfect_of_simple_nonsolvable hns
  obtain ⟨W₀, hW₀, hgW₀⟩ := exists_perfect_surjective g hg
  have hW₀G : W₀.map W.subtype ≤ I := by
    apply hI _ (le_trans (Subgroup.map_subtype_le W₀) hW)
    rw [← Subgroup.map_commutator, hW₀]
  have h1 : Nat.card S ∣ Nat.card ↥W₀ := Subgroup.card_dvd_of_surjective (f := g.comp W₀.subtype) hgW₀
  have h2 : Nat.card ↥(W₀.map W.subtype) = Nat.card ↥W₀ :=
    Subgroup.card_map_of_injective W.subtype_injective
  exact hcard (h1.trans (h2 ▸ Subgroup.card_dvd_of_le hW₀G))

end HSec

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
