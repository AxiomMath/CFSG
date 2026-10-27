module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NChain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NStep

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

variable {A S : Type} [Group A] [Group S]

@[expose] def TypesA (ρ : A →* MulAut S) (H : Subgroup S) : Prop :=
  ∀ K : Subgroup S, IsComponentOf K (I142N.fixA ρ ⊓ H) → I142N.CPlus (↥K ⧸ Subgroup.center ↥K)

section Central

variable {G H : Type} [Group G] [Group H]

theorem nonempty_quot_center_equiv (π : G →* H)
    (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G) {K : Subgroup G} (hKp : ⁅K, K⁆ = K) :
    Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (↥(K.map π) ⧸ Subgroup.center ↥(K.map π))) := by
  classical
  let f : ↥K →* ↥(K.map π) :=
    { toFun := fun k => ⟨π (k : G), Subgroup.mem_map_of_mem π k.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : G) (b : G)) }
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : ∀ k : ↥K, f k = 1 → k ∈ Subgroup.center ↥K := by
    intro k hk1
    have hπ : π (k : G) = 1 := congrArg Subtype.val hk1
    have hc := hk (k : G) hπ
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    exact Subtype.ext (hc (y : G))
  have hZmap : Subgroup.center ↥K ≤ (Subgroup.center ↥(K.map π)).comap f := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro l
    obtain ⟨k, rfl⟩ := hfsurj l
    show f k * f z = f z * f k
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
  have hZpre : ∀ k : ↥K, f k ∈ Subgroup.center ↥(K.map π) → k ∈ Subgroup.center ↥K := by
    intro x hx
    have hcent : ∀ y : ↥K, ⁅x, y⁆ ∈ Subgroup.center ↥K := by
      intro y
      apply hfker
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hx (f y)).symm
    let χ : ↥K →* ↥(Subgroup.center ↥K) :=
      { toFun := fun y => ⟨⁅x, y⁆, hcent y⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          have hconj : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
            have hc := Subgroup.mem_center_iff.1 (hcent b) a
            calc a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ * a * a⁻¹ := by rw [hc]
              _ = ⁅x, b⁆ := by group
          show ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆
          calc ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
                rw [commutatorElement_def]; group
            _ = ⁅x, a⁆ * ⁅x, b⁆ := by rw [hconj]) }
    have hperf : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ :=
      I142N.commutator_top_of_comm_self_eq hKp
    have hχker : ⁅(⊤ : Subgroup ↥K), ⊤⁆ ≤ χ.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hcent a) ⁅x, b⁆).symm
    have htop : (⊤ : Subgroup ↥K) ≤ χ.ker := by rw [← hperf]; exact hχker
    rw [Subgroup.mem_center_iff]
    intro w
    have hw : w ∈ χ.ker := htop (Subgroup.mem_top w)
    rw [MonoidHom.mem_ker] at hw
    have h3 : ⁅x, w⁆ = 1 := congrArg Subtype.val hw
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  refine ⟨MulEquiv.ofBijective
    (QuotientGroup.map (Subgroup.center ↥K) (Subgroup.center ↥(K.map π)) f hZmap) ⟨?_, ?_⟩⟩
  · intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) b
    rw [QuotientGroup.map_mk', QuotientGroup.map_mk'] at hab
    have h2 : (↑(f x * (f y)⁻¹) : ↥(K.map π) ⧸ Subgroup.center ↥(K.map π)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hab]
      group
    have h3 : f x * (f y)⁻¹ ∈ Subgroup.center ↥(K.map π) := (QuotientGroup.eq_one_iff _).1 h2
    have h4 : x * y⁻¹ ∈ Subgroup.center ↥K := by
      apply hZpre
      rw [map_mul, map_inv]
      exact h3
    have h5 : (↑(x * y⁻¹) : ↥K ⧸ Subgroup.center ↥K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h4
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h5
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact mul_inv_eq_one.1 h5
  · intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥(K.map π)) y
    obtain ⟨k, rfl⟩ := hfsurj l
    exact ⟨QuotientGroup.mk' (Subgroup.center ↥K) k, by
      rw [QuotientGroup.map_mk', QuotientGroup.mk'_apply]⟩

theorem cplus_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) (h : I142N.CPlus H) :
    I142N.CPlus G := by
  obtain ⟨hs, hnc, hcl⟩ := h
  refine ⟨e.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun hc => hab (e.symm.injective (by simpa using hc))⟩
  · rcases hcl with hc | ht
    · rcases hc with hc | hc
      · obtain ⟨i, hi, ⟨f⟩⟩ := hc
        exact Or.inl (Or.inl ⟨i, hi, ⟨e.trans f⟩⟩)
      · obtain ⟨i, hi, ⟨f⟩⟩ := hc
        exact Or.inl (Or.inr ⟨i, hi, ⟨e.trans f⟩⟩)
    · obtain ⟨i, hi, ⟨f⟩⟩ := ht
      exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem cplus_iff_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    I142N.CPlus G ↔ I142N.CPlus H :=
  ⟨fun h => cplus_of_mulEquiv e.symm h, cplus_of_mulEquiv e⟩

theorem isChevSimple_of_cplus {G : Type} [Group G] (h : I142N.CPlus G) : IsChevSimple 2 G := by
  rcases h.2.2 with hc | ht
  · exact hc
  · obtain ⟨i, hi, ⟨e⟩⟩ := ht
    cases i with
    | lie d =>
      change d.1 = TauCeti.LieTypeIndex.tits at hi
      have hchar : d.1.characteristic = 2 := by
        rw [hi]
        exact TauCeti.LieTypeIndex.characteristic_tits
      exact Or.inl ⟨.lie d, hchar, ⟨e⟩⟩
    | alternating n hn => exact absurd hi (by simp [onLie])
    | sporadic s => exact absurd hi (by simp [onLie])
    | cyclic q hq => exact absurd hi (by simp [onLie])

theorem cplus_iff_of_perfect_map (π : G →* H)
    (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G) {K : Subgroup G} (hKp : ⁅K, K⁆ = K) :
    I142N.CPlus (↥K ⧸ Subgroup.center ↥K) ↔
      I142N.CPlus (↥(K.map π) ⧸ Subgroup.center ↥(K.map π)) :=
  let ⟨e⟩ := nonempty_quot_center_equiv π hk hKp
  cplus_iff_of_mulEquiv e

theorem cplus_quot_center_iff_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    I142N.CPlus (G ⧸ Subgroup.center G) ↔ I142N.CPlus (H ⧸ Subgroup.center H) :=
  cplus_iff_of_mulEquiv (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
    (Subgroup.map_center_eq e))

end Central

section Component

variable {G H : Type} [Group G] [Group H]

theorem isComponentOf_fixA_map (π : G →* H) (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {ρ : A →* MulAut G} {σ : A →* MulAut H}
    (hc : ∀ (a : A) (x : G), π (ρ a x) = σ a (π x))
    {K : Subgroup G} (hK : IsComponentOf K (I142N.fixA ρ)) :
    IsComponentOf (K.map π) (I142N.fixA σ ⊓ π.range) := by
  have hfix : (I142N.fixA ρ).map π ≤ I142N.fixA σ ⊓ π.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_range.2 ⟨x, rfl⟩⟩
    rw [I142N.mem_fixA]
    intro a
    rw [← hc, I142N.mem_fixA.1 hx a]
  exact I142N.isComponentOf_trans (I142N.isComponentOf_map π hk hK)
    (I142N.isSubnormal_of_commutator_le hfix (I142N.commutator_fixA_le_map hk hc))

theorem exists_isComponentOf_fixA_lift (π : G →* H)
    (hk : ∀ g : G, π g = 1 → g ∈ Subgroup.center G)
    {ρ : A →* MulAut G} {σ : A →* MulAut H}
    (hc : ∀ (a : A) (x : G), π (ρ a x) = σ a (π x))
    {Kb : Subgroup H} (hKb : IsComponentOf Kb (I142N.fixA σ ⊓ π.range)) :
    ∃ K : Subgroup G, IsComponentOf K (I142N.fixA ρ) ∧ K.map π = Kb := by
  have hfix : (I142N.fixA ρ).map π ≤ I142N.fixA σ ⊓ π.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_range.2 ⟨x, rfl⟩⟩
    rw [I142N.mem_fixA]
    intro a
    rw [← hc, I142N.mem_fixA.1 hx a]
  have hperf : ⁅Kb, Kb⁆ = Kb := I142N.comm_self_eq_of_commutator_top hKb.2.2.1
  have hle : Kb ≤ (I142N.fixA ρ).map π := by
    have h1 : ⁅Kb, Kb⁆ ≤ ⁅I142N.fixA σ ⊓ π.range, I142N.fixA σ ⊓ π.range⁆ :=
      Subgroup.commutator_mono hKb.1 hKb.1
    rw [hperf] at h1
    exact h1.trans (I142N.commutator_fixA_le_map hk hc)
  exact I142N.exists_component_lift π hk (I142N.isComponentOf_of_le hKb hle hfix)

end Component

section Restrict

variable {G : Type} [Group G]

private theorem isComponentOf_comap_subtype {H : Subgroup G} {X : Subgroup ↥H} {K : Subgroup G}
    (hK : IsComponentOf K (X.map H.subtype)) : IsComponentOf (K.comap H.subtype) X := by
  have hKH : K ≤ H := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 (hK.1 hy)
    exact x.2
  have hle : K.comap H.subtype ≤ X := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hK.1 hx)
    rw [H.subtype_injective hyx] at hy
    exact hy
  have hsub : IsSubnormal (K.comap H.subtype) X := by
    have hXeq : X ⊓ (X.map H.subtype).comap H.subtype = X :=
      inf_eq_left.2 fun x hx => Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem H.subtype hx)
    have h := I142N.isSubnormal_inf_comap H.subtype hK.2.1 X
    rw [hXeq, inf_eq_right.2 hle] at h
    exact h
  refine ⟨hle, hsub, ?_⟩
  have hmap : (K.comap H.subtype).map H.subtype = K :=
    Subgroup.map_comap_eq_self (f := H.subtype) (by rwa [Subgroup.range_subtype])
  exact I142N.isQuasisimple_of_mulEquiv' (e := (Subgroup.equivMapOfInjective (K.comap H.subtype)
    H.subtype H.subtype_injective).trans (MulEquiv.subgroupCongr hmap)) hK.2.2

private theorem cplus_of_comap_subtype {H : Subgroup G} {K : Subgroup G} (hKH : K ≤ H)
    (h : I142N.CPlus (↥(K.comap H.subtype) ⧸ Subgroup.center ↥(K.comap H.subtype))) :
    I142N.CPlus (↥K ⧸ Subgroup.center ↥K) := by
  have hmap : (K.comap H.subtype).map H.subtype = K :=
    Subgroup.map_comap_eq_self (f := H.subtype) (by rwa [Subgroup.range_subtype])
  exact (cplus_quot_center_iff_of_mulEquiv (G := ↥(K.comap H.subtype)) (H := ↥K)
    ((Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap))).1 h

end Restrict

section TypesTransfer

theorem typesA_of_component (ρ : A →* MulAut S) (K₀ : Subgroup S)
    (hinv : ∀ a, K₀.map (ρ a).toMonoidHom = K₀)
    (hT : ∀ Kb : Subgroup (↥K₀ ⧸ Subgroup.center ↥K₀),
      IsComponentOf Kb (I142N.fixA (I142N.quotAct ρ K₀ hinv)) →
        I142N.CPlus (↥Kb ⧸ Subgroup.center ↥Kb)) :
    TypesA ρ K₀ := by
  intro K hK
  have hKle : K ≤ K₀ := fun x hx => (Subgroup.mem_inf.1 (hK.1 hx)).2
  have hK' : IsComponentOf (K.comap K₀.subtype)
      (I142N.fixA (I142N.restrictAct ρ K₀ hinv)) := by
    have h := hK
    rw [← I142N.map_fixA_restrict ρ K₀ hinv] at h
    exact isComponentOf_comap_subtype h
  have hquot : IsComponentOf ((K.comap K₀.subtype).map
      (QuotientGroup.mk' (Subgroup.center ↥K₀)))
      (I142N.fixA (I142N.quotAct ρ K₀ hinv) ⊓
        (QuotientGroup.mk' (Subgroup.center ↥K₀)).range) :=
    isComponentOf_fixA_map (QuotientGroup.mk' (Subgroup.center ↥K₀))
      (fun g hg => (QuotientGroup.eq_one_iff g).1 hg)
      (fun a x => I142N.quotAct_mk ρ K₀ hinv a x) hK'
  rw [MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective _), inf_top_eq] at hquot
  have hCP1 := hT _ hquot
  have hCP2 : I142N.CPlus (↥(K.comap K₀.subtype) ⧸ Subgroup.center ↥(K.comap K₀.subtype)) :=
    (cplus_iff_of_perfect_map (QuotientGroup.mk' (Subgroup.center ↥K₀))
      (fun g hg => (QuotientGroup.eq_one_iff g).1 hg)
      (I142N.comm_self_eq_of_commutator_top hK'.2.2.1)).2 hCP1
  exact cplus_of_comap_subtype hKle hCP2

end TypesTransfer

section Product

variable [Finite S]

theorem typesA_iSup_coord {ι : Type} [Fintype ι] [DecidableEq ι] (ρ : A →* MulAut S)
    (H : ι → Subgroup S) (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (hinv : ∀ a i, (H i).map (ρ a).toMonoidHom = H i) (hfac : ∀ i, TypesA ρ (H i)) :
    TypesA ρ (⨆ i, H i) := by
  intro K hK
  have hm := I142N.hmap_one ρ H hinv
  have hrange : (I142N.piProd H hcomm).range = ⨆ i, H i := I142N.piProd_range H hcomm
  rw [← hrange] at hK
  have hk : ∀ g : ∀ i, ↥(H i), I142N.piProd H hcomm g = 1 → g ∈ Subgroup.center (∀ i, ↥(H i)) :=
    fun g => I142N.piProd_ker_central H hcomm
  have hc : ∀ (a : A) (x : ∀ i, ↥(H i)),
      I142N.piProd H hcomm (I142N.coordHom ρ H 1 hm a x) = ρ a (I142N.piProd H hcomm x) :=
    fun a x => I142N.piProd_coordHom ρ H hcomm 1 hm a x
  have hNj_le : ∀ j, I142N.fixA ρ ⊓ H j ≤
      I142N.fixA ρ ⊓ (I142N.piProd H hcomm).range := by
    intro j
    refine le_inf inf_le_left ?_
    rw [hrange]
    exact inf_le_right.trans (le_iSup H j)
  have hcommY : ⁅I142N.fixA ρ ⊓ (I142N.piProd H hcomm).range,
      I142N.fixA ρ ⊓ (I142N.piProd H hcomm).range⁆ ≤
      ⨆ j, (I142N.fixA ρ ⊓ H j) := by
    refine (I142N.commutator_fixA_le_map hk hc).trans ?_
    rintro _ ⟨w, hw, rfl⟩
    have hfixw : ∀ i, ((w i : ↥(H i)) : S) ∈ I142N.fixA ρ := by
      intro i
      rw [I142N.mem_fixA]
      intro a
      have h1 : I142N.coordFun ρ H 1 hm a w = w := I142N.mem_fixA.1 hw a
      have h2 := congrArg (fun g : (∀ j, ↥(H j)) => ((g i : ↥(H i)) : S)) h1
      rw [I142N.coordFun_apply, I142N.one_symm_apply] at h2
      exact h2
    rw [I142N.piProd, MonoidHom.noncommPiCoprod_apply]
    apply Subgroup.noncommProd_mem
    intro i _
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_inf.2 ⟨hfixw i, (w i).2⟩)
  have hfixconj : ∀ {y n : S}, y ∈ I142N.fixA ρ → n ∈ I142N.fixA ρ →
      y * n * y⁻¹ ∈ I142N.fixA ρ := by
    intro y n hy hn
    rw [I142N.mem_fixA] at hy hn ⊢
    intro a
    rw [map_mul, map_mul, map_inv, hy a, hn a]
  have hfixinv : ∀ {y : S}, y ∈ I142N.fixA ρ → y⁻¹ ∈ I142N.fixA ρ := by
    intro y hy
    rw [I142N.mem_fixA] at hy ⊢
    intro a
    rw [map_inv, hy a]
  have hHnorm : ∀ j, (⨆ i, H i) ≤ Subgroup.normalizer ((H j : Subgroup S) : Set S) := by
    intro j
    refine iSup_le fun i => ?_
    rcases eq_or_ne i j with rfl | hij
    · exact Subgroup.le_normalizer
    · have hle : H i ≤ Subgroup.centralizer ((H j : Subgroup S) : Set S) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hcomm i j hij x hx z hz).eq.symm
      exact hle.trans (Subgroup.centralizer_le_normalizer _)
  have hnorm : ∀ j, I142N.fixA ρ ⊓ (I142N.piProd H hcomm).range ≤
      Subgroup.normalizer ((I142N.fixA ρ ⊓ H j : Subgroup S) : Set S) := by
    intro j y hy
    obtain ⟨hyfix, hyX⟩ := Subgroup.mem_inf.1 hy
    have hyX' : y ∈ ⨆ i, H i := by rw [← hrange]; exact hyX
    have hyN : y ∈ Subgroup.normalizer ((H j : Subgroup S) : Set S) := hHnorm j hyX'
    have hyinvN : y⁻¹ ∈ Subgroup.normalizer ((H j : Subgroup S) : Set S) :=
      hHnorm j ((⨆ i, H i).inv_mem hyX')
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact Subgroup.mem_inf.2 ⟨hfixconj hyfix (Subgroup.mem_inf.1 hn).1,
        (Subgroup.mem_normalizer_iff.1 hyN n).1 (Subgroup.mem_inf.1 hn).2⟩
    · intro hn
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h := hfixconj (y := y⁻¹) (hfixinv hyfix) (Subgroup.mem_inf.1 hn).1
        convert h using 1
        group
      · have h := (Subgroup.mem_normalizer_iff.1 hyinvN (y * n * y⁻¹)).1
          (Subgroup.mem_inf.1 hn).2
        convert h using 1
        group
  by_cases hex : ∃ j, K ≤ I142N.fixA ρ ⊓ H j
  · obtain ⟨j, hj⟩ := hex
    exact hfac j K (I142N.isComponentOf_of_le hK hj (hNj_le j))
  · exfalso
    have hdisj : ∀ j, ⁅K, I142N.fixA ρ ⊓ H j⁆ = ⊥ := by
      intro j
      rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot (I142N.gw_isComponentOf_of_open hK)
        (hNj_le j) (hnorm j) with h | h
      · exact absurd h (fun hj => hex ⟨j, hj⟩)
      · exact h
    have hcent : (⨆ j, I142N.fixA ρ ⊓ H j) ≤ Subgroup.centralizer (K : Set S) := by
      refine iSup_le fun j => ?_
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [Subgroup.commutator_comm]; exact hdisj j)
    have hbotcomm : ⁅K, ⨆ j, (I142N.fixA ρ ⊓ H j)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro k hk'
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact (Subgroup.mem_centralizer_iff.1 (hcent hm) k hk').symm
    have hKleJ : K ≤ ⨆ j, (I142N.fixA ρ ⊓ H j) := by
      calc K = ⁅K, K⁆ := (I142N.comm_self_eq_of_commutator_top hK.2.2.1).symm
        _ ≤ _ := (Subgroup.commutator_mono hK.1 hK.1).trans hcommY
    have hbot : K = ⊥ := by
      have h1 : ⁅K, K⁆ ≤ ⁅K, ⨆ j, (I142N.fixA ρ ⊓ H j)⁆ := Subgroup.commutator_mono le_rfl hKleJ
      rw [hbotcomm, le_bot_iff] at h1
      refine eq_bot_iff.2 ?_
      rw [← I142N.comm_self_eq_of_commutator_top hK.2.2.1]
      exact le_of_eq h1
    exact absurd hbot ((Subgroup.nontrivial_iff_ne_bot K).1
      (I142N.nontrivial_of_isQuasisimple hK.2.2))

private theorem coordFun_fixA_coord {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) :
    ∀ g ∈ I142N.fixA (I142N.coordHom ρ H σ hmap), ∀ (a : A) (k : ι),
      ((g k : ↥(H k)) : S) = ρ a ((g ((σ a).symm k) : ↥(H ((σ a).symm k))) : S) := by
  intro g hg a k
  have h1 : I142N.coordFun ρ H σ hmap a g = g := I142N.mem_fixA.1 hg a
  have h2 := congrArg (fun f : (∀ j, ↥(H j)) => ((f k : ↥(H k)) : S)) h1
  rw [I142N.coordFun_apply] at h2
  exact h2.symm

theorem coordPr_injOn_fixA {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (i₀ : ι)
    (htrans : ∀ j, ∃ a, (σ a) i₀ = j) :
    ∀ g ∈ I142N.fixA (I142N.coordHom ρ H σ hmap), I142N.coordPr H i₀ g = 1 → g = 1 := by
  intro g hg hg1
  funext j
  apply Subtype.ext
  obtain ⟨c, hc⟩ := htrans j
  have h1 := coordFun_fixA_coord ρ H σ hmap g hg c j
  have hsymm : (σ c).symm j = i₀ := by rw [← hc, Equiv.symm_apply_apply]
  rw [hsymm] at h1
  have h2 : ((g i₀ : ↥(H i₀)) : S) = 1 := hg1
  show ((g j : ↥(H j)) : S) = 1
  rw [h1, h2, map_one]

theorem map_coordPr_fixA {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S) (σ : A →* Equiv.Perm ι)
    (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i)) (i₀ : ι)
    (htrans : ∀ j, ∃ a, (σ a) i₀ = j) :
    (I142N.fixA (I142N.coordHom ρ H σ hmap)).map (I142N.coordPr H i₀) =
      I142N.fixA (ρ.comp (I142N.stabSub σ i₀).subtype) ⊓ H i₀ := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, (g i₀).2⟩
    rw [I142N.mem_fixA]
    intro a
    have hs : (σ (a : A)).symm i₀ = i₀ := (Equiv.symm_apply_eq (σ (a : A))).2 (a.2).symm
    have h1 := coordFun_fixA_coord ρ H σ hmap g hg (a : A) i₀
    rw [hs] at h1
    show ρ (a : A) ((g i₀ : ↥(H i₀)) : S) = ((g i₀ : ↥(H i₀)) : S)
    exact h1.symm
  · intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.1 hy
    have hfixE : ∀ a : A, (σ a) i₀ = i₀ → ρ a (y : S) = y := fun a ha =>
      I142N.mem_fixA.1 hy1 ⟨a, ha⟩
    choose c hc using htrans
    let g : ∀ k, ↥(H k) := fun k => ⟨ρ (c k) (y : S), by
      have h := I142N.mem_coordTarget ρ H σ hmap (c k) i₀ ⟨y, hy2⟩
      rwa [hc k] at h⟩
    have hgW : g ∈ I142N.fixA (I142N.coordHom ρ H σ hmap) := by
      rw [I142N.mem_fixA]
      intro a
      funext k
      apply Subtype.ext
      show ((I142N.coordFun ρ H σ hmap a g k : ↥(H k)) : S) = ((g k : ↥(H k)) : S)
      rw [I142N.coordFun_apply]
      set m := (σ a).symm k with hm
      have hd : (σ ((c k)⁻¹ * (a * c m))) i₀ = i₀ := by
        rw [map_mul, Equiv.Perm.mul_apply, map_inv, map_mul, Equiv.Perm.mul_apply, hc m,
          Equiv.apply_symm_apply]
        exact Equiv.Perm.inv_eq_iff_eq.2 (hc k).symm
      show ρ a (ρ (c m) (y : S)) = ρ (c k) (y : S)
      calc ρ a (ρ (c m) (y : S)) = ρ (a * c m) (y : S) := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (c k * ((c k)⁻¹ * (a * c m))) (y : S) := by rw [mul_inv_cancel_left]
        _ = ρ (c k) (ρ ((c k)⁻¹ * (a * c m)) (y : S)) := by rw [map_mul, MulAut.mul_apply]
        _ = ρ (c k) (y : S) := by rw [hfixE _ hd]
    refine Subgroup.mem_map.2 ⟨g, hgW, ?_⟩
    show ((g i₀ : ↥(H i₀)) : S) = y
    show ρ (c i₀) (y : S) = y
    exact hfixE _ (hc i₀)

theorem typesA_iSup_transitive {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ : A →* MulAut S) (H : ι → Subgroup S)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, Commute x y)
    (σ : A →* Equiv.Perm ι) (hmap : ∀ a i, (H i).map (ρ a).toMonoidHom = H ((σ a) i))
    (i₀ : ι) (htrans : ∀ j, ∃ a, (σ a) i₀ = j)
    (htypes : TypesA (ρ.comp (I142N.stabSub σ i₀).subtype) (H i₀)) :
    TypesA ρ (⨆ i, H i) := by
  intro K hK
  set W : Subgroup (∀ i, ↥(H i)) := I142N.fixA (I142N.coordHom ρ H σ hmap) with hW
  have hk : ∀ g : ∀ i, ↥(H i),
      I142N.piProd H hcomm g = 1 → g ∈ Subgroup.center (∀ i, ↥(H i)) :=
    fun g => I142N.piProd_ker_central H hcomm
  have hpull : ∀ (a : A) (x : ∀ j, ↥(H j)),
      I142N.piProd H hcomm (I142N.coordHom ρ H σ hmap a x) = ρ a (I142N.piProd H hcomm x) :=
    fun a x => I142N.piProd_coordHom ρ H hcomm σ hmap a x
  have hrange : (I142N.piProd H hcomm).range = ⨆ i, H i := I142N.piProd_range H hcomm
  rw [← hrange] at hK
  obtain ⟨Ku, hKu, hKuK⟩ := exists_isComponentOf_fixA_lift (I142N.piProd H hcomm) hk hpull hK
  have hinj : Function.Injective ((I142N.coordPr H i₀).comp W.subtype) := by
    intro x y hxy
    have hmem : ((x : ∀ i, ↥(H i)) * (y : ∀ i, ↥(H i))⁻¹) ∈ W :=
      W.mul_mem x.2 (W.inv_mem y.2)
    have h1 : I142N.coordPr H i₀ ((x : ∀ i, ↥(H i)) * (y : ∀ i, ↥(H i))⁻¹) = 1 := by
      rw [map_mul, map_inv,
        show I142N.coordPr H i₀ (x : ∀ i, ↥(H i)) =
          I142N.coordPr H i₀ (y : ∀ i, ↥(H i)) from hxy, mul_inv_cancel]
    have h2 := coordPr_injOn_fixA ρ H σ hmap i₀ htrans _ hmem h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hker : ∀ g : ↥W, ((I142N.coordPr H i₀).comp W.subtype) g = 1 →
      g ∈ Subgroup.center ↥W := by
    intro g hg
    have h1 : g = 1 := hinj (by rw [hg, map_one])
    rw [h1]
    exact Subgroup.one_mem _
  have hKuinj : IsComponentOf (Ku.comap W.subtype) ⊤ := by
    apply isComponentOf_comap_subtype
    rw [I142N.map_subtype_top]
    exact hKu
  have hV : (⊤ : Subgroup ↥W).map ((I142N.coordPr H i₀).comp W.subtype) =
      I142N.fixA (ρ.comp (I142N.stabSub σ i₀).subtype) ⊓ H i₀ := by
    rw [← Subgroup.map_map, I142N.map_subtype_top]
    exact map_coordPr_fixA ρ H σ hmap i₀ htrans
  have hKuV : (Ku.comap W.subtype).map ((I142N.coordPr H i₀).comp W.subtype) =
      Ku.map (I142N.coordPr H i₀) := by
    rw [← Subgroup.map_map]
    congr 1
    exact Subgroup.map_comap_eq_self (f := W.subtype)
      (by rw [Subgroup.range_subtype]; exact hKu.1)
  have hKuΦ : IsComponentOf (Ku.map (I142N.coordPr H i₀))
      (I142N.fixA (ρ.comp (I142N.stabSub σ i₀).subtype) ⊓ H i₀) := by
    have h1 := I142N.isComponentOf_map ((I142N.coordPr H i₀).comp W.subtype) hker hKuinj
    rwa [hKuV, hV] at h1
  have hCP2 : I142N.CPlus (↥(Ku.comap W.subtype) ⧸ Subgroup.center ↥(Ku.comap W.subtype)) :=
    (cplus_quot_center_iff_of_mulEquiv
      ((Subgroup.equivMapOfInjective (Ku.comap W.subtype)
        ((I142N.coordPr H i₀).comp W.subtype) hinj).trans
        (MulEquiv.subgroupCongr hKuV))).2 (htypes _ hKuΦ)
  have hCP3 : I142N.CPlus (↥Ku ⧸ Subgroup.center ↥Ku) := by
    have hmap2 : (Ku.comap W.subtype).map W.subtype = Ku :=
      Subgroup.map_comap_eq_self (f := W.subtype)
        (by rw [Subgroup.range_subtype]; exact hKu.1)
    exact (cplus_quot_center_iff_of_mulEquiv
      ((Subgroup.equivMapOfInjective (Ku.comap W.subtype) W.subtype
        W.subtype_injective).trans (MulEquiv.subgroupCongr hmap2))).1 hCP2
  rw [← hKuK]
  exact (cplus_iff_of_perfect_map (I142N.piProd H hcomm) hk
    (I142N.comm_self_eq_of_commutator_top hKu.2.2.1)).1 hCP3

end Product

end CFSG.LocalAnalysis.GLTheoremA.I142T

end