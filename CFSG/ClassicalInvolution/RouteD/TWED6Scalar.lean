module

public import CFSG.ClassicalInvolution.RouteD.TWED6Rec
public import CFSG.ClassicalInvolution.RouteD.TWEB6Scalar
public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.D6

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank
  CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (plus_hspan)
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)

set_option linter.unusedSectionVars false

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

def planePart (P : HypPair Q) (x : V) : V :=
  polar Q x P.f • P.e + polar Q x P.e • P.f

theorem planePart_mem (P : HypPair Q) (x : V) : planePart P x ∈ hypPlane P :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (e_mem_hypPlane _))
    (Submodule.smul_mem _ _ (f_mem_hypPlane _))

theorem polar_sub_planePart_self (P : HypPair Q) (x : V) :
    polar Q (x - planePart P x) P.e = 0 ∧ polar Q (x - planePart P x) P.f = 0 := by
  unfold planePart
  refine ⟨?_, ?_⟩
  · rw [polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ee,
      HypPair.polar_fe]
    ring
  · rw [polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, P.polar_ef,
      HypPair.polar_ff]
    ring

theorem polar_sub_planePart_orth {P P' : HypPair Q} (h : P.Orth P') (x : V) :
    polar Q (x - planePart P x) P'.e = polar Q x P'.e ∧
      polar Q (x - planePart P x) P'.f = polar Q x P'.f := by
  unfold planePart
  refine ⟨?_, ?_⟩
  · rw [polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h.ee, h.fe]
    ring
  · rw [polar_sub_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, h.ef, h.ff]
    ring

theorem mem_plane_of_orth {pr : ℕ → HypPair Q} {n : ℕ}
    (horth : ∀ a b, a < n → b < n → a ≠ b → (pr a).Orth (pr b))
    (hspan : ∀ y, (∀ a < n, polar Q y (pr a).e = 0 ∧ polar Q y (pr a).f = 0) → y = 0)
    {i : ℕ} (hi : i < n) {x : V}
    (hx : ∀ a < n, a ≠ i → polar Q x (pr a).e = 0 ∧ polar Q x (pr a).f = 0) :
    x ∈ hypPlane (pr i) := by
  have h0 : x - planePart (pr i) x = 0 := by
    refine hspan _ fun a ha => ?_
    by_cases hai : a = i
    · subst hai
      exact polar_sub_planePart_self _ x
    · have := polar_sub_planePart_orth (horth i a hi ha (Ne.symm hai)) x
      rw [this.1, this.2]
      exact hx a ha hai
  rw [sub_eq_zero.mp h0]
  exact planePart_mem _ x

theorem mem_two_planes_of_orth {pr : ℕ → HypPair Q} {n : ℕ}
    (horth : ∀ a b, a < n → b < n → a ≠ b → (pr a).Orth (pr b))
    (hspan : ∀ y, (∀ a < n, polar Q y (pr a).e = 0 ∧ polar Q y (pr a).f = 0) → y = 0)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) {x : V}
    (hx : ∀ a < n, a ≠ i → a ≠ j → polar Q x (pr a).e = 0 ∧ polar Q x (pr a).f = 0) :
    x ∈ hypPlane (pr i) ⊔ hypPlane (pr j) := by
  have hx₁ : x - planePart (pr i) x ∈ hypPlane (pr j) := by
    refine mem_plane_of_orth horth hspan hj fun a ha haj => ?_
    by_cases hai : a = i
    · subst hai
      exact polar_sub_planePart_self _ x
    · have := polar_sub_planePart_orth (horth i a hi ha (Ne.symm hai)) x
      rw [this.1, this.2]
      exact hx a ha hai haj
  have : x = planePart (pr i) x + (x - planePart (pr i) x) := by abel
  rw [this]
  exact Submodule.add_mem_sup (planePart_mem _ x) hx₁

theorem g_eq_id_on_perp {pr : ℕ → HypPair Q} {n : ℕ}
    (horth : ∀ a b, a < n → b < n → a ≠ b → (pr a).Orth (pr b))
    (hspan : ∀ y, (∀ a < n, polar Q y (pr a).e = 0 ∧ polar Q y (pr a).f = 0) → y = 0)
    (hn : 0 < n) {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg2 : g * g = 1)
    (hfix : ∀ a, 1 ≤ a → a < n → g (pr a).e = (pr a).e ∧ g (pr a).f = (pr a).f) :
    ∀ y, polar Q (pr 0).e y = 0 → polar Q (pr 0).f y = 0 → g y = y := by
  intro y hye hyf
  have hgg : ∀ v, g (g v) = v := fun v => by
    have h := congrArg (fun h : V ≃ₗ[K] V => h v) hg2
    exact h
  have hpol : ∀ a b, polar Q (g a) (g b) = polar Q a b := fun a b => polar_map_of_mem hgO a b
  have hyplane : ∀ w ∈ hypPlane (pr 0), polar Q y w = 0 := by
    intro w hw
    obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff _).mp hw
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, polar_comm Q y, polar_comm Q y,
      hye, hyf]
    ring
  have hgu : ∀ u ∈ hypPlane (pr 0), g u ∈ hypPlane (pr 0) := by
    intro u hu
    refine mem_plane_of_orth horth hspan hn fun a ha ha0 => ?_
    obtain ⟨hae, haf⟩ := hfix a (by omega) ha
    have ho := horth 0 a hn ha (Ne.symm ha0)
    refine ⟨?_, ?_⟩
    · have e1 : polar Q (g u) (pr a).e = polar Q (g u) (g (pr a).e) := by rw [hae]
      rw [e1, hpol]
      exact polar_hypPlane_of_orth ho u hu _ (e_mem_hypPlane _)
    · have e1 : polar Q (g u) (pr a).f = polar Q (g u) (g (pr a).f) := by rw [haf]
      rw [e1, hpol]
      exact polar_hypPlane_of_orth ho u hu _ (f_mem_hypPlane _)
  have hd : g y - y = 0 := by
    refine hspan _ fun a ha => ?_
    by_cases ha0 : a = 0
    · subst ha0
      have key : ∀ u ∈ hypPlane (pr 0), polar Q (g y - y) u = 0 := by
        intro u hu
        rw [polar_sub_left]
        have e1 : polar Q (g y) u = polar Q y (g u) := by
          have h := hpol y (g u)
          rw [hgg] at h
          exact h
        rw [e1, hyplane _ (hgu u hu), hyplane u hu, sub_zero]
      exact ⟨key _ (e_mem_hypPlane _), key _ (f_mem_hypPlane _)⟩
    · obtain ⟨hae, haf⟩ := hfix a (Nat.pos_of_ne_zero ha0) ha
      refine ⟨?_, ?_⟩
      · rw [polar_sub_left]
        have h := hpol y (pr a).e
        rw [hae] at h
        rw [h, sub_self]
      · rw [polar_sub_left]
        have h := hpol y (pr a).f
        rw [haf] at h
        rw [h, sub_self]
  exact sub_eq_zero.mp hd

theorem commutes_of_commutes_two (hodd : Odd (Nat.card K)) {pr : ℕ → HypPair Q}
    (horth : ∀ a b, a < 6 → b < 6 → a ≠ b → (pr a).Orth (pr b))
    (hspan : ∀ y, (∀ a < 6, polar Q y (pr a).e = 0 ∧ polar Q y (pr a).f = 0) → y = 0)
    {L₀ L₂ LM S : Subgroup (V ≃ₗ[K] V)} {i₀ i₂ iM iS : V ≃ₗ[K] V} (h₀ : IsFundamental Q L₀ i₀)
    (h₂ : IsFundamental Q L₂ i₂) (hM : IsFundamental Q LM iM) (hS : IsFundamental Q S iS)
    (n₀ : negSpace i₀ = hypPlane (pr 0) ⊔ hypPlane (pr 1))
    (n₂ : negSpace i₂ = hypPlane (pr 2) ⊔ hypPlane (pr 3))
    (nM : negSpace iM = hypPlane (pr 4) ⊔ hypPlane (pr 5))
    (hne : S ≠ L₂) (c₀ : Commutes S L₀) (cM : Commutes S LM) : Commutes S L₂ := by
  by_contra n
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hcomm_of : ∀ {L' : Subgroup (V ≃ₗ[K] V)} {i' : V ≃ₗ[K] V}, IsFundamental Q L' i' →
      (∀ x ∈ negSpace iS, ∀ y ∈ negSpace i', polar Q x y = 0) → Commutes S L' := by
    intro L' i' hL' h
    by_contra hc
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_polar_ne_of_not_commutes h2 hS hL' hc
    exact hxy (h x hx y hy)
  have hpl : ∀ a b, a < 6 → b < 6 → a ≠ b → ∀ x ∈ hypPlane (pr a), ∀ y ∈ hypPlane (pr b),
      polar Q x y = 0 := fun a b ha hb hab => polar_hypPlane_of_orth (horth a b ha hb hab)
  have o20 : ∀ x ∈ negSpace i₀, ∀ y ∈ negSpace i₂, polar Q x y = 0 := by
    rw [n₀, n₂]
    exact polar_eq_zero_of_sup (hpl 0 2 (by omega) (by omega) (by omega))
      (hpl 0 3 (by omega) (by omega) (by omega)) (hpl 1 2 (by omega) (by omega) (by omega))
      (hpl 1 3 (by omega) (by omega) (by omega))
  have oM2 : ∀ x ∈ negSpace iM, ∀ y ∈ negSpace i₂, polar Q x y = 0 := by
    rw [nM, n₂]
    exact polar_eq_zero_of_sup (hpl 4 2 (by omega) (by omega) (by omega))
      (hpl 4 3 (by omega) (by omega) (by omega)) (hpl 5 2 (by omega) (by omega) (by omega))
      (hpl 5 3 (by omega) (by omega) (by omega))
  have oS0 : ∀ x ∈ negSpace iS, ∀ y ∈ negSpace i₀, polar Q x y = 0 := by
    rcases orth_or_twin hodd hS h₀ c₀ with h | ht
    · exact h
    · exfalso
      refine n (hcomm_of h₂ fun x hx y hy => ?_)
      exact o20 x (ht ▸ hx) y hy
  have oSM : ∀ x ∈ negSpace iS, ∀ y ∈ negSpace iM, polar Q x y = 0 := by
    rcases orth_or_twin hodd hS hM cM with h | ht
    · exact h
    · exfalso
      refine n (hcomm_of h₂ fun x hx y hy => ?_)
      exact oM2 x (ht ▸ hx) y hy
  have hle : negSpace iS ≤ negSpace i₂ := by
    intro x hx
    rw [n₂]
    refine mem_two_planes_of_orth horth hspan (i := 2) (j := 3) (by omega) (by omega) (by omega)
      fun a ha h2' h3' => ?_
    have e0 : ∀ k, k < 2 → polar Q x (pr k).e = 0 ∧ polar Q x (pr k).f = 0 := fun k hk => by
      have hk' : hypPlane (pr k) ≤ negSpace i₀ := by
        rw [n₀]
        interval_cases k
        · exact le_sup_left
        · exact le_sup_right
      exact ⟨oS0 x hx _ (hk' (e_mem_hypPlane _)), oS0 x hx _ (hk' (f_mem_hypPlane _))⟩
    have eM : ∀ k, 4 ≤ k → k < 6 → polar Q x (pr k).e = 0 ∧ polar Q x (pr k).f = 0 :=
      fun k hk hk6 => by
      have hk' : hypPlane (pr k) ≤ negSpace iM := by
        rw [nM]
        interval_cases k
        · exact le_sup_left
        · exact le_sup_right
      exact ⟨oSM x hx _ (hk' (e_mem_hypPlane _)), oSM x hx _ (hk' (f_mem_hypPlane _))⟩
    by_cases hlt : a < 2
    · exact e0 a hlt
    · exact eM a (by omega) ha
  have heq : negSpace iS = negSpace i₂ :=
    Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_negSpace hodd hS, finrank_negSpace hodd h₂])
  exact negSpace_ne_of_not_commutes hodd hS h₂ hne n heq

end Model

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}


local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes.adj_def]; done)
    | (simp [DNodes.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem scalar_plus_six (c : TCtx p f .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember p f β t) (htz : t * z * t⁻¹ = z)
    {M : Subgroup G} (hMz : M ∈ centralizingMembers Ω {z}) (nd : DNodes p f 6 Ω M)
    (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {Rz : ℕ → Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K}
    {RzM RN : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K}
    {x : spinGroup (quadPlus 6 (GaloisField p f))} {tM : Bool}
    {α : spinGroup (quadPlus 6 (GaloisField p f)) ≃* spinGroup (quadPlus 6 (GaloisField p f))}
    {g₀ : (Fin 6 ⊕ Fin 6 → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin 6 ⊕ Fin 6 → GaloisField p f)}
    (hRz : ∀ a (h : a < 6), 2 ≤ a →
      Rz a ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
        locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ)
    (hRzM : RzM ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
      locImg Ω z M = RzM.map c.d.ψ)
    {N : Subgroup G} (hNz : N ∈ centralizingMembers Ω {z})
    (hRN : RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D ∧
      locImg Ω z N = RN.map c.d.ψ)
    (hxR : ∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) a
      (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom))
    (hxM : RzM = ((rootSL2 (plusFrame 6 (GaloisField p f) (by norm_num)) 4 5 (by omega) (by omega)
      (by omega) true tM).map (MulAut.conj x).toMonoidHom))
    (hαθ : ∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y))
    (hg₀O : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)))
    (hg₀2 : g₀ * g₀ = 1)
    (hconj : ∀ y v, spinAction (quadPlus 6 (GaloisField p f)) (α y) (g₀ v) =
      g₀ (spinAction (quadPlus 6 (GaloisField p f)) y v))
    (hfixv : ∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
      g₀ (spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s)) =
      spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec a s))
    (hNc : ∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a))
    (hN4 : ¬ Commutes N (nd.J ⟨4, by omega⟩)) (hN5 : ¬ Commutes N (nd.J ⟨5, by omega⟩)) :
    ∀ y, polar (quadPlus 6 (GaloisField p f)) (spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec ⟨0, by omega⟩ true)) y = 0 →
      polar (quadPlus 6 (GaloisField p f)) (spinAction (quadPlus 6 (GaloisField p f)) x
        ((plusFrame 6 (GaloisField p f) (by norm_num)).vec ⟨0, by omega⟩ false)) y = 0 →
      g₀ y = y := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f c.hp2
  have hodd : Odd (Nat.card (GaloisField p f)) := c.hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have cq := centralQuot_plus (m := 6) c.hp2 (by norm_num : 4 ≤ 6) (by norm_num : 3 ≤ 6) c.hq
  have hQ : (polarBilin (quadPlus 6 (GaloisField p f))).Nondegenerate :=
    nondegenerate_polarBilin_quadPlus 6 (GaloisField p f)
  set F₀ := plusFrame 6 (GaloisField p f) (by norm_num) with hF₀
  have hg : spinAction (quadPlus 6 (GaloisField p f)) x ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField p f)) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  let pr : ℕ → HypPair (quadPlus 6 (GaloisField p f)) := fun k =>
    if h : k < 6 then imgPair F₀ ⟨k, h⟩ hg else imgPair F₀ ⟨0, by omega⟩ hg
  have hprk : ∀ k (hk : k < 6), pr k = imgPair F₀ ⟨k, hk⟩ hg := fun k hk => by simp [pr, hk]
  have horth : ∀ a b, a < 6 → b < 6 → a ≠ b → (pr a).Orth (pr b) := fun a b ha hb hab => by
    rw [hprk a ha, hprk b hb]
    exact imgPair_orth F₀ hg (fun h => hab (congrArg Fin.val h))
  have hsp : ∀ y, (∀ a < 6, polar (quadPlus 6 (GaloisField p f)) y (pr a).e = 0 ∧
      polar (quadPlus 6 (GaloisField p f)) y (pr a).f = 0) → y = 0 := by
    intro y hy
    have h0 : spinAction (quadPlus 6 (GaloisField p f)) x⁻¹ y = 0 := by
      refine plus_hspan (F := GaloisField p f) (by norm_num) _ fun a r => ?_
      have h := hy a.val a.isLt
      have e1 : polar (quadPlus 6 (GaloisField p f)) y (imgPair F₀ a hg).e =
          polar (quadPlus 6 (GaloisField p f)) y (spinAction _ x (F₀.vec a true)) := rfl
      have hinv : y = spinAction (quadPlus 6 (GaloisField p f)) x
          (spinAction (quadPlus 6 (GaloisField p f)) x⁻¹ y) := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have key : ∀ r', polar (quadPlus 6 (GaloisField p f))
          (spinAction (quadPlus 6 (GaloisField p f)) x⁻¹ y) (F₀.vec a r') =
          polar (quadPlus 6 (GaloisField p f)) y (spinAction (quadPlus 6 (GaloisField p f)) x
            (F₀.vec a r')) := by
        intro r'
        conv_rhs => rw [hinv]
        exact (polar_map_of_mem hg _ _).symm
      rw [key]
      rw [hprk a.val a.isLt] at h
      cases r
      · exact h.2
      · exact h.1
    have := (spinAction (quadPlus 6 (GaloisField p f)) x⁻¹).injective
      (h0.trans (map_zero _).symm)
    exact this
  have hLf : ∀ a (h : a ≤ 2), ∃ i, IsFundamental (quadPlus 6 (GaloisField p f))
      ((Rz (a + 2)).map (spinAction (quadPlus 6 (GaloisField p f)))) i ∧
      negSpace i = hypPlane (pr a) ⊔ hypPlane (pr (a + 1)) := by
    intro a h
    obtain ⟨i, hi⟩ := cq.map_mem _ (hRz (a + 2) (by omega) (by omega)).1
    refine ⟨i, hi, ?_⟩
    rw [hprk a (by omega), hprk (a + 1) (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : a < 6) (by omega : a + 1 < 6) (by omega) true false
      x hg hi (by rw [hxR a h])
  obtain ⟨i₀, h₀, n₀⟩ := hLf 0 (by norm_num)
  obtain ⟨i₂, h₂', n₂⟩ := hLf 2 (by norm_num)
  obtain ⟨iM, hM', nM⟩ : ∃ iM, IsFundamental (quadPlus 6 (GaloisField p f))
      (RzM.map (spinAction (quadPlus 6 (GaloisField p f)))) iM ∧
      negSpace iM = hypPlane (pr 4) ⊔ hypPlane (pr 5) := by
    obtain ⟨i, hi⟩ := cq.map_mem _ hRzM.1
    refine ⟨i, hi, ?_⟩
    rw [hprk 4 (by omega), hprk 5 (by omega)]
    exact negSpace_rootSL2 hodd F₀ (by omega : 4 < 6) (by omega : 5 < 6) (by omega) true tM x hg hi
      (by rw [hxM])
  obtain ⟨iN, hN'⟩ := cq.map_mem _ hRN.1
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hn45 : Commutes (nd.J ⟨4, by omega⟩) (nd.J ⟨5, by omega⟩) :=
    nd.commutes_of_not_adj (fin_ne_of_val_ne (by d6_idx)) (by d6_idx)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => hN5 (h ▸ hn45)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hcentM : M ≤ Subgroup.centralizer ({t} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm
  have hcentN : N ≤ Subgroup.centralizer ({t} : Set G) := fun n hn => by
    have := hNc ⟨1, by omega⟩ (by norm_num)
    rw [h1] at this
    exact Subgroup.mem_centralizer_singleton_iff.mpr (this n hn t ht.mem)
  have hfixL : ∀ {L : Subgroup G} {R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K},
      L ∈ centralizingMembers Ω {z} → locImg Ω z L = R.map c.d.ψ →
      L ≤ Subgroup.centralizer ({t} : Set G) →
      ∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r :=
    fun hL hLR hLt r hr => (locAut_fixed_iff hΩ c.hP1 htz hL).mp hLt _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  have hcommg : ∀ {R : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K},
      R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField p f) (by norm_num)) →
      (∀ r ∈ R, locAut hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r) →
      ∀ l ∈ R.map (spinAction (quadPlus 6 (GaloisField p f))), g₀ * l = l * g₀ :=
    fun hR hfix => commute_of_fixed c.d.ψ c.d.ker_le (locAut hΩ.conjInvariant htz) α hαθ
      (cq.perf _ hR) hfix hconj
  have fM := hcommg hRzM.1 (hfixL hMz hRzM.2 hcentM)
  have fN := hcommg hRN.1 (hfixL hNz hRN.2 hcentN)
  obtain ⟨εM, hεM, hsM⟩ := sign_of_commute h2 hM' hg₀O hg₀2 fM
  obtain ⟨εN, hεN, hsN⟩ := sign_of_commute h2 hN' hg₀O hg₀2 fN
  have hfix2 : ∀ w ∈ negSpace i₂, g₀ w = w := by
    intro w hw
    rw [n₂] at hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    have hpl : ∀ (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3), ∀ u ∈ hypPlane (pr k), g₀ u = u := by
      intro k hk hk3 u hu
      obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff _).mp hu
      have hk6 : k < 6 := by omega
      have h := hfixv ⟨k, hk6⟩ hk hk3
      rw [map_add, map_smul, map_smul]
      have e1 : g₀ (pr k).e = (pr k).e := by
        rw [hprk k hk6]
        exact h true
      have e2 : g₀ (pr k).f = (pr k).f := by
        rw [hprk k hk6]
        exact h false
      rw [e1, e2]
    rw [map_add, hpl 2 (by omega) (by omega) u hu, hpl 3 (by omega) (by omega) v hv]
  have hRf' : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Rz a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField p f) (by norm_num)) := fun a ha ha2 => (hRz a ha ha2).1
  have hc₀ : Commutes (RN.map (spinAction (quadPlus 6 (GaloisField p f))))
      ((Rz (0 + 2)).map (spinAction (quadPlus 6 (GaloisField p f)))) :=
    (cq.commutes_iff hRN.1).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega)) hRN.1
      hRN.2 (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
  have hnc4 : ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField p f))))
      ((Rz (2 + 2)).map (spinAction (quadPlus 6 (GaloisField p f)))) := fun h =>
    hN4 ((c.commutes_iff_fund hNz (hmemz 4 (by omega) (by omega)) hRN.1 hRN.2
      (hRz 4 (by omega) (by omega)).2).mpr ((cq.commutes_iff hRN.1).mp h))
  have hne42 : RN.map (spinAction (quadPlus 6 (GaloisField p f))) ≠
      (Rz (2 + 2)).map (spinAction (quadPlus 6 (GaloisField p f))) := fun e =>
    hN4ne (c.eq_of_locImg_eq hNz (hmemz 4 (by omega) (by omega)) (by
      rw [hRN.2, (hRz 4 (by omega) (by omega)).2,
        cq.map_inj hRN.1 (hRf' 4 (by omega) (by omega)) e]))
  obtain ⟨u, hu, w, hw, hpuw⟩ := exists_polar_ne_of_not_commutes h2 hN' h₂' hnc4
  have hεN1 : εN = 1 := by
    have := sign_mul_eq_one hg₀O (hsN u hu) (show g₀ w = (1 : GaloisField p f) • w by
      rw [one_smul]; exact hfix2 w hw) hpuw
    rwa [mul_one] at this
  have hnM : ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField p f))))
      (RzM.map (spinAction (quadPlus 6 (GaloisField p f)))) := fun h =>
    hnc4 (commutes_of_commutes_two hodd horth hsp h₀ h₂' hM' hN' n₀ n₂ nM hne42 hc₀ h)
  obtain ⟨u', hu', w', hw', hpuw'⟩ := exists_polar_ne_of_not_commutes h2 hN' hM' hnM
  have hεM1 : εM = 1 := by
    have := sign_mul_eq_one hg₀O (hsN u' hu') (hsM w' hw') hpuw'
    rwa [hεN1, one_mul] at this
  have hfixall : ∀ a, 1 ≤ a → a < 6 →
      g₀ (pr a).e = (pr a).e ∧ g₀ (pr a).f = (pr a).f := by
    intro a ha1 ha6
    by_cases ha3 : a ≤ 3
    · have h := hfixv ⟨a, ha6⟩ ha1 ha3
      rw [hprk a ha6]
      exact ⟨h true, h false⟩
    · have hle : hypPlane (pr a) ≤ negSpace iM := by
        rw [nM]
        have : a = 4 ∨ a = 5 := by omega
        rcases this with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      refine ⟨?_, ?_⟩
      · rw [hsM _ (hle (e_mem_hypPlane _)), hεM1, one_smul]
      · rw [hsM _ (hle (f_mem_hypPlane _)), hεM1, one_smul]
  intro y hy1 hy2
  have key := g_eq_id_on_perp horth hsp (by norm_num) hg₀O hg₀2 hfixall y
  rw [hprk 0 (by omega)] at key
  exact key hy1 hy2

end Group

end CFSG.ClassicalInvolution.RouteD.TWE.D6
