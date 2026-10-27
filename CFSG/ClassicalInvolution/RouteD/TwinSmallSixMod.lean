module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallWitt
public import CFSG.ClassicalInvolution.RouteD.TwinSmallTwin
public import CFSG.ClassicalInvolution.ModelFacts.E8D8AdjPair
public import CFSG.ClassicalInvolution.RouteD.GapsFrSpin
public import CFSG.ClassicalInvolution.RouteD.GapsFrModel
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

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.ModelFacts.E8D8
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Img

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

@[expose] def imgPairSix (F₀ : HypFrame Q m) (j : Fin m) (s : Bool) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : HypPair Q :=
  ⟨g (F₀.vec j s), g (F₀.vec j (!s)), by rw [map_of_mem hg]; exact F₀.map_vec j s,
    by rw [map_of_mem hg]; exact F₀.map_vec j (!s),
    by rw [polar_map_of_mem hg]; exact F₀.polar_vec_not j s⟩

theorem orth_imgPairSix (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (imgPairSix F₀ i s hg).Orth (imgPairSix F₀ j t hg) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [imgPairSix]; rw [polar_map_of_mem hg]; exact F₀.polar_vec_of_ne hij _ _)

end Img

section Vec

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

omit [FiniteDimensional K V] in
theorem spinAction_vec_mem_negSpace (hodd : Odd (Nat.card K)) (F₀ : HypFrame Q m) {a b : ℕ}
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q)
    {i : V ≃ₗ[K] V}
    (hi : IsFundamental Q (((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map
      (spinAction Q)) i) {k : ℕ} (hkm : k < m) (hk : k = a ∨ k = b) (u : Bool) :
    spinAction Q x (F₀.vec ⟨k, hkm⟩ u) ∈ negSpace i := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hX : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have horth := orth_imgPairSix F₀ hij s t hX
  have heq := La_range_eq_of_pairs F₀ ha hb hab s t x horth ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  have hi' : IsFundamental Q (mkFrame (imgPairSix F₀ ⟨a, ha⟩ s hX) (imgPairSix F₀ ⟨b, hb⟩ t hX)
      horth).La.range i := by
    rw [heq]
    exact hi
  have hii : (mkFrame (imgPairSix F₀ ⟨a, ha⟩ s hX) (imgPairSix F₀ ⟨b, hb⟩ t hX) horth).La (-1) =
      i := IsFundamental.involution_unique hodd (IsFundamental.of_frame _) hi'
  rw [← hii, negSpace_La_neg_one h2]
  rcases hk with rfl | rfl
  · cases s <;> cases u
    · exact Frame.e₁_mem_span _
    · exact Frame.f₁_mem_span _
    · exact Frame.f₁_mem_span _
    · exact Frame.e₁_mem_span _
  · cases t <;> cases u
    · exact Frame.e₂_mem_span _
    · exact Frame.f₂_mem_span _
    · exact Frame.f₂_mem_span _
    · exact Frame.e₂_mem_span _

end Vec

section TwoPairs

variable {p f : ℕ} [Fact p.Prime]

theorem false_of_two_linear_pairs_six (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (R : Fin 2 → Fin 2 → Subgroup (SpinM p f 6))
    (hR : ∀ i j, R i j ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr p f)))
    (hadj : ∀ i, ModelAdj (Subgroup.center (SpinM p f 6)) (R i 0) (R i 1))
    (hlin : ∀ i, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R i 0) (R i 1))
    (hcomm : ∀ i i', i ≠ i' → ∀ j j', Commutes (R i j) (R i' j')) : False := by
  classical
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      simp at hq
    · exact h
  have cq := Exotic.centralQuot_minus hp2 hq ⟨Fact.out, hf1, (by norm_num : 4 ≤ 6)⟩
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Vm 6 (GaloisField p f)) := by
    rw [finrank_minus p f 6 (by omega)]
    omega
  choose ι hι using fun i j => cq.map_mem (R i j) (hR i j)
  have hadjV : ∀ i, ModelAdj (scalars (GaloisField p f) (Vm 6 (GaloisField p f)))
      ((R i 0).map (spinAction (QM p f 6))) ((R i 1).map (spinAction (QM p f 6))) := fun i =>
    cq.modelAdj (hR i 0) (hR i 1) (hadj i)
  have hdata := fun i => adj_data hodd hdim (hι i 0) (hι i 1) (hadjV i)
  have hsing : ∀ i, HasSingularVector (QM p f 6) (negSpace (ι i 0) ⊓ negSpace (ι i 1)) := by
    intro i
    obtain ⟨W, hW⟩ := hlin i
    exact hasSingularVector_of_linearPair hp2 (by omega) (hι i 0) (hι i 1) (hdata i).1
      (hdata i).2.1 (hdata i).2.2 ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
  have hpd : ∀ i, PairDecomposition (QM p f 6) (ι i 0) (ι i 1) := fun i =>
    (lemma_6_10 hodd (hι i 0) (hι i 1) (hdata i).1 (hdata i).2.1 (hdata i).2.2).1
  have hU : ∀ i (k : Fin 3), HasSingularVector (QM p f 6) (planeOf (ι i 0) (ι i 1) k) := by
    intro i k
    fin_cases k
    · exact (hpd i).type₁₂.mpr (hsing i)
    · exact hsing i
    · exact (hpd i).type₂₃.mp (hsing i)
  have hhyp : ∀ i (k : Fin 3), ∃ P : HypPair (QM p f 6),
      P.e ∈ planeOf (ι i 0) (ι i 1) k ∧ P.f ∈ planeOf (ι i 0) (ι i 1) k := by
    intro i k
    obtain ⟨P, he, hf, -⟩ := exists_hypPair_of_hasSingularVector (planeOf_nondeg (hpd i) k)
      (planeOf_finrank (hpd i) k) (hU i k)
    exact ⟨P, he, hf⟩
  choose P hPe hPf using hhyp
  have horth : ∀ i i', i ≠ i' → ∀ j j', ∀ x ∈ negSpace (ι i j), ∀ y ∈ negSpace (ι i' j'),
      polar (QM p f 6) x y = 0 := by
    intro i i' hii' j j' x hx y hy
    have h := polar_negSpace_eq_zero_of_commutes_adj hodd (hι i 0) (hι i 1) (hι i' j')
      (hdata i).1 (hadjV i).1 (hadjV i).2.1
      ((cq.commutes_iff (hR i' j')).mpr (hcomm i' i (Ne.symm hii') j' 0))
      ((cq.commutes_iff (hR i' j')).mpr (hcomm i' i (Ne.symm hii') j' 1))
    fin_cases j
    · exact h.1 x hx y hy
    · exact h.2 x hx y hy
  have hPorth : ∀ a b : Fin 2 × Fin 3, a ≠ b → (P a.1 a.2).Orth (P b.1 b.2) := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ hne
    by_cases hii : i = i'
    · subst hii
      have hkk : k ≠ k' := fun h => hne (by rw [h])
      exact hypPair_orth_of_mem (planeOf_orth (hpd i) k k' hkk) (hPe i k) (hPf i k) (hPe i k')
        (hPf i k')
    · exact hypPair_orth_of_mem (S := negSpace (ι i (planeSide k)))
        (T := negSpace (ι i' (planeSide k'))) (horth i i' hii _ _)
        (planeOf_le_negSpace (ι i) k (hPe i k)) (planeOf_le_negSpace (ι i) k (hPf i k))
        (planeOf_le_negSpace (ι i') k' (hPe i' k')) (planeOf_le_negSpace (ι i') k' (hPf i' k'))
  let e : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv
  refine false_of_pairs_minus (minusCoeffs_irr p f) hodd (n := 6) (by norm_num)
    (fun a => P (e.symm a).1 (e.symm a).2) fun a b hab => hPorth _ _ fun h => hab (by
      have := congrArg e h
      simpa using this)

end TwoPairs

section Pair

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {KY : Type} [Group KY] {𝓕 : Set (Subgroup KY)}
  {π : KY →* (V ≃ₗ[F] V)}

omit [Finite F] [FiniteDimensional F V] in
theorem sign_on_negSpace (h2 : (2 : F) ≠ 0) {L : Subgroup (V ≃ₗ[F] V)} {i : V ≃ₗ[F] V}
    (hL : IsFundamental Q L i) {g : V ≃ₗ[F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hcomm : ∀ l ∈ L, g * l = l * g) : ∃ s : F, ∀ v ∈ negSpace i, g v = s • v := by
  rcases negSpace_le_eigenspace_of_commute h2 hL hgO hg2 hcomm with h | h
  · refine ⟨1, fun v hv => ?_⟩
    have := Module.End.mem_eigenspace_iff.mp (h hv)
    simpa using this
  · refine ⟨-1, fun v hv => ?_⟩
    have := Module.End.mem_eigenspace_iff.mp (h hv)
    simpa using this

theorem hpair_data (hodd : Odd (Nat.card F)) (hdim : 9 ≤ Module.finrank F V)
    (cq : CentralQuot π 𝓕 (fundSet Q) (scalars F V)) {R R' R₁ : Subgroup KY} (hR : R ∈ 𝓕)
    (hR' : R' ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕) (hadj : ModelAdj (Subgroup.center KY) R R')
    (hc : Commutes R R₁) (hc' : Commutes R' R₁) {i₁ : V ≃ₗ[F] V}
    (hi₁ : IsFundamental Q (R₁.map π) i₁) {g : V ≃ₗ[F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hgR : ∀ y ∈ R, g * π y = π y * g) (hgR' : ∀ y ∈ R', g * π y = π y * g) :
    ∃ (T : Submodule F V) (s : F), 6 ≤ Module.finrank F T ∧ (∀ v ∈ T, g v = s • v) ∧
      ∀ v ∈ T, ∀ w ∈ negSpace i₁, polar Q v w = 0 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨i, hi⟩ := cq.map_mem R hR
  obtain ⟨i', hi'⟩ := cq.map_mem R' hR'
  have hadjV := cq.modelAdj hR hR' hadj
  obtain ⟨cm, hN, hC⟩ := adj_data hodd hdim hi hi' hadjV
  have hfin : Module.finrank F ↥(negSpace i ⊓ negSpace i') = 2 :=
    finrank_inf_negSpace hodd hi hi' cm hN hC
  have h4 : Module.finrank F ↥(negSpace i) = 4 := finrank_negSpace hodd hi
  have h4' : Module.finrank F ↥(negSpace i') = 4 := finrank_negSpace hodd hi'
  obtain ⟨s, hs⟩ := sign_on_negSpace h2 hi hgO hg2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact hgR y hy)
  obtain ⟨s', hs'⟩ := sign_on_negSpace h2 hi' hgO hg2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact hgR' y hy)
  have hss : s = s' := by
    have hpos : 0 < Module.finrank F ↥(negSpace i ⊓ negSpace i') := by omega
    have hne : negSpace i ⊓ negSpace i' ≠ ⊥ := fun h =>
      (Nat.pos_iff_ne_zero.mp hpos) (Submodule.finrank_eq_zero.mpr h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 : (s - s') • v = 0 := by
      rw [sub_smul, ← hs v hv.1, ← hs' v hv.2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hv0)
  refine ⟨negSpace i ⊔ negSpace i', s, ?_, ?_, ?_⟩
  · have := Submodule.finrank_sup_add_finrank_inf_eq (negSpace i) (negSpace i')
    omega
  · intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hs a ha, hs' b hb, ← hss, smul_add]
  · intro v hv w hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    have horth := polar_negSpace_eq_zero_of_commutes_adj hodd hi hi' hi₁ cm hadjV.1 hadjV.2.1
      ((cq.commutes_iff hR₁).mpr (commutes_symm hc)) ((cq.commutes_iff hR₁).mpr (commutes_symm hc'))
    rw [polar_add_left, horth.1 a ha w hw, horth.2 b hb w hw, add_zero]

end Pair

end CFSG.ClassicalInvolution.RouteD.TwinSmall
