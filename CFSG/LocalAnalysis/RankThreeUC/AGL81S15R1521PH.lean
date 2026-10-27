module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
  KFactsPair
open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem false_of_centralProd_gn_aux1 (T : Subgroup X) :
    ∃ ρ : (X ⧸ gnC T) →* MulAut ↥(gnV T), Function.Injective ρ ∧
      ∀ (x : X) (v : ↥(gnV T)), ((ρ (QuotientGroup.mk x) v : ↥(gnV T)) : X) = x * v * x⁻¹ := by
  haveI : (gnV T).Normal := Subgroup.normalClosure_normal
  have hker : gnC T ≤ (MulAut.conjNormal : X →* MulAut ↥(gnV T)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext v
    have h := Subgroup.mem_centralizer_iff.1 hx (v : X) v.2
    rw [MulAut.conjNormal_apply]
    show x * (v : X) * x⁻¹ = (v : X)
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm
  refine ⟨QuotientGroup.lift (gnC T) MulAut.conjNormal hker, ?_, fun x v => rfl⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx : x ∈ gnC T := by
    rw [gnC, Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := congrArg (fun f : MulAut ↥(gnV T) => ((f ⟨h, hh⟩ : ↥(gnV T)) : X)) hq
    simp only [QuotientGroup.lift_mk, MulAut.conjNormal_apply] at h1
    show h * x = x * h
    have h2 : x * h * x⁻¹ = h := h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  exact (QuotientGroup.eq_one_iff x).2 hx

theorem false_of_centralProd_gn_aux2 {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : IsAltSixCoverThree G) : IsAltSixCoverThree H := by
  obtain ⟨hq, hc, ⟨f⟩⟩ := h
  refine ⟨CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hq, ?_, ⟨?_⟩⟩
  · have h1 : Nat.card ↥((Subgroup.center G).map (e : G →* H)) = Nat.card ↥(Subgroup.center G) :=
      Subgroup.card_map_of_injective e.injective
    rw [Subgroup.map_center_eq e] at h1
    rw [h1, hc]
  · exact (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
      (Subgroup.map_center_eq e)).symm.trans f

theorem false_of_centralProd_gn_aux3 {S : Type} [Group S] [Finite S] (h : IsAltSixCoverThree S) :
    Nat.card S = 1080 := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S),
    Nat.card_congr e.toEquiv, card_alternatingGroup_six, hZ]

theorem false_of_centralProd_gn_aux4 {Y : Type} [Group Y] {Js : Subgroup Y} {K K' : Subgroup ↥Js}
    (hsup : K ⊔ K' = ⊤) (hc : K ≤ Subgroup.centralizer (K' : Set ↥Js)) : K.Normal := by
  have hconj : ∀ y ∈ K', ∀ a ∈ K, y * a * y⁻¹ = a := by
    intro y hy a ha
    rw [Subgroup.mem_centralizer_iff.1 (hc ha) y hy, mul_assoc, mul_inv_cancel, mul_one]
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
  refine sup_le (Subgroup.le_normalizer) ?_
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hconj y hy x hx]
    exact hx
  · intro hx
    have h3 := hconj y⁻¹ (K'.inv_mem hy) _ hx
    simp only [inv_inv] at h3
    have h4 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [h4] at h3
    rw [h3]
    exact hx

theorem false_of_centralProd_gn_aux5 {Y : Type} [Group Y] [Finite Y] {Ls Js : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤) (hle : Ls ≤ Js) (h3 : IsAltSixCoverThree ↥Ls)
    {K₁ K₂ : Subgroup ↥Js} (h1 : IsAltSixCoverThree ↥K₁) (h2 : IsAltSixCoverThree ↥K₂)
    (hsup : K₁ ⊔ K₂ = ⊤) (hc : K₁ ≤ Subgroup.centralizer (K₂ : Set ↥Js)) :
    K₁.map Js.subtype = Ls ∨ K₂.map Js.subtype = Ls := by
  obtain ⟨-, hsub, hqs⟩ := hLs
  have hc' : K₂ ≤ Subgroup.centralizer (K₁ : Set ↥Js) := fun y hy =>
    Subgroup.mem_centralizer_iff.2 fun h hh =>
      (Subgroup.mem_centralizer_iff.1 (hc hh) y hy).symm
  have hn1 : K₁.Normal := false_of_centralProd_gn_aux4 hsup hc
  have hn2 : K₂.Normal := false_of_centralProd_gn_aux4 (by rw [sup_comm]; exact hsup) hc'
  have hJ : CFSG.Open.IsSubnormal Ls Js := by
    have h := hsub.inf_of_le (le_top : Js ≤ ⊤)
    rwa [inf_eq_left.2 hle] at h
  have hK : CFSG.Open.IsSubnormal (Ls.subgroupOf Js) ⊤ :=
    CFSG.Open.IsSubnormal.of_mathlib hJ.subgroupOf
  have hqs' : CFSG.Open.IsQuasisimple ↥(Ls.subgroupOf Js) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hqs
  have hcomp : IsComponentOf (Ls.subgroupOf Js) ⊤ := ⟨le_top, hK, hqs'⟩
  have hmap : (Ls.subgroupOf Js).map Js.subtype = Ls := Subgroup.map_subgroupOf_eq_of_le hle
  have hLsc : Nat.card ↥Ls = 1080 := false_of_centralProd_gn_aux3 h3
  have hcard : Nat.card ↥(Ls.subgroupOf Js) = 1080 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hLsc
  have hcase : ∀ K : Subgroup ↥Js, IsAltSixCoverThree ↥K → Ls.subgroupOf Js ≤ K →
      K.map Js.subtype = Ls := by
    intro K hK3 hleK
    have hEq : Ls.subgroupOf Js = K :=
      Subgroup.eq_of_le_of_card_ge hleK (by rw [hcard, false_of_centralProd_gn_aux3 hK3])
    rw [← hEq]
    exact hmap
  rcases kComp_holds.2 ↥Js (Ls.subgroupOf Js) K₁ hn1 hcomp with hl1 | hcm1
  · exact Or.inl (hcase K₁ h1 hl1)
  rcases kComp_holds.2 ↥Js (Ls.subgroupOf Js) K₂ hn2 hcomp with hl2 | hcm2
  · exact Or.inr (hcase K₂ h2 hl2)
  exfalso
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcm1 hcm2
  have hcent : ∀ a ∈ Ls.subgroupOf Js, ∀ g : ↥Js, g * a = a * g := by
    intro a ha g
    have hK1 : K₁ ≤ Subgroup.centralizer ({a} : Set ↥Js) := fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (Subgroup.mem_centralizer_iff.1 (hcm1 ha) b hb).symm
    have hK2 : K₂ ≤ Subgroup.centralizer ({a} : Set ↥Js) := fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact (Subgroup.mem_centralizer_iff.1 (hcm2 ha) b hb).symm
    have hg : g ∈ Subgroup.centralizer ({a} : Set ↥Js) := by
      have : (⊤ : Subgroup ↥Js) ≤ Subgroup.centralizer ({a} : Set ↥Js) := by
        rw [← hsup]
        exact sup_le hK1 hK2
      exact this (Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_iff.1 hg a rfl).symm
  have hcenter : Subgroup.center ↥Ls = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro u
    rw [Subgroup.mem_center_iff]
    intro v
    apply Subtype.ext
    have hu : (⟨(u : Y), hle u.2⟩ : ↥Js) ∈ Ls.subgroupOf Js := by
      rw [Subgroup.mem_subgroupOf]
      exact u.2
    have := hcent _ hu ⟨(v : Y), hle v.2⟩
    simpa using congrArg Subtype.val this
  have h33 := h3.2.1
  rw [hcenter, Subgroup.card_top, hLsc] at h33
  omega

open scoped commutatorElement in
theorem false_of_centralProd_gn_aux6 (k534 : K534) (kA6Z3 : KA6Z3) {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hsh : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls) (h3 : IsAltSixCoverThree ↥Ls)
    {Js : Subgroup (X ⧸ gnC T)} {K K' : Subgroup ↥Js} (hK : IsAltSixCoverThree ↥K)
    (hK' : IsAltSixCoverThree ↥K') (hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hne : K ⊓ K' ≠ ⊥) (hKL : K.map Js.subtype = Ls) : False := by
  obtain ⟨ρ, hρinj, hρapp⟩ := false_of_centralProd_gn_aux1 T
  have hσ : Function.Injective (ρ.comp Js.subtype) := hρinj.comp Js.subtype_injective
  have hcard := k534 X T hX Ls hLs hsh h3
  have hVc := gnV_comm_exp_two hX
  refine kA6Z3 ↥(gnV T) (fun a b => Subtype.ext (hVc.1 a a.2 b b.2))
    (fun v => Subtype.ext (by simpa using hVc.2 v v.2))
    (K.map (ρ.comp Js.subtype)) (K'.map (ρ.comp Js.subtype))
    (false_of_centralProd_gn_aux2 (Subgroup.equivMapOfInjective K _ hσ) hK)
    (false_of_centralProd_gn_aux2 (Subgroup.equivMapOfInjective K' _ hσ) hK') ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rw [← Subgroup.map_inf _ _ _ hσ, Ne, Subgroup.map_eq_bot_iff_of_injective _ hσ]
    exact hne
  · have hle : (commOn ↥(gnV T) (K.map (ρ.comp Js.subtype) ⊓ K'.map (ρ.comp Js.subtype))).map
        (gnV T).subtype ≤ ⁅gnV T, Ls.comap (toStar T)⁆ := by
      rw [commOn, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨g, hg, v, rfl⟩, rfl⟩
      obtain ⟨k, hk, rfl⟩ := hg.1
      have hkL : (k : X ⧸ gnC T) ∈ Ls := hKL ▸ ⟨k, hk, rfl⟩
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (k : X ⧸ gnC T)
      have hxL : x ∈ Ls.comap (toStar T) := by
        have hts : toStar T x = (k : X ⧸ gnC T) := hx
        show toStar T x ∈ Ls
        rw [hts]
        exact hkL
      have hv2 : (((ρ.comp Js.subtype) k) v : X) = x * v * x⁻¹ := by
        have := hρapp x v
        rw [hx] at this
        exact this
      have heq : (gnV T).subtype (v⁻¹ * (ρ.comp Js.subtype) k v) = ⁅((v⁻¹ : ↥(gnV T)) : X), x⁆ := by
        rw [Subgroup.subtype_apply, Subgroup.coe_mul, hv2, commutatorElement_def]
        simp only [Subgroup.coe_inv, inv_inv]
        group
      show (gnV T).subtype (v⁻¹ * (ρ.comp Js.subtype) k v) ∈ ⁅gnV T, Ls.comap (toStar T)⁆
      rw [heq]
      exact Subgroup.commutator_mem_commutator (v⁻¹).2 hxL
    calc Nat.card ↥(commOn ↥(gnV T) (K.map (ρ.comp Js.subtype) ⊓ K'.map (ρ.comp Js.subtype)))
        = Nat.card ↥((commOn ↥(gnV T) (K.map (ρ.comp Js.subtype) ⊓
            K'.map (ρ.comp Js.subtype))).map (gnV T).subtype) :=
          (Subgroup.card_map_of_injective (gnV T).subtype_injective).symm
      _ ≤ Nat.card ↥⁅gnV T, Ls.comap (toStar T)⁆ := Subgroup.card_le_of_le hle
      _ = 2 ^ 6 := hcard

theorem false_of_centralProd_gn (k534 : K534) (kA6Z3 : KA6Z3) {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hsh : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls) (h3 : IsAltSixCoverThree ↥Ls)
    {Js : Subgroup (X ⧸ gnC T)} (hle : Ls ≤ Js) (hcp : IsCentralProdA6Z3 ↥Js) : False := by
  obtain ⟨K₁, K₂, h1, h2, hsup, hc, hi1, -⟩ := hcp
  have hne : K₁ ⊓ K₂ ≠ ⊥ := by
    rw [hi1, CFSG.centerIn_eq_map_center]
    intro h'
    rw [Subgroup.map_eq_bot_iff_of_injective _ K₁.subtype_injective] at h'
    have h33 := h1.2.1
    rw [h', Subgroup.card_bot] at h33
    omega
  have hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 (hc ha) b hb).symm
  rcases false_of_centralProd_gn_aux5 hLs hle h3 h1 h2 hsup hc with hL | hL
  · exact false_of_centralProd_gn_aux6 k534 kA6Z3 hX hLs hsh h3 h1 h2 hcomm hne hL
  · exact false_of_centralProd_gn_aux6 k534 kA6Z3 hX hLs hsh h3 h2 h1
      (fun a ha b hb => (hcomm b hb a ha).symm) (by rwa [inf_comm]) hL

end CFSG.LocalAnalysis.RankThreeUC.S15
