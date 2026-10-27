module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165LayerPullback

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalGroups.UnitaryFlag
open scoped Matrix MatrixGroups Pointwise

private theorem exists_qTorus_and_qElement {G M : Type*} [Group G] [Group M] {J J₁ : Subgroup G}
    {P₀ P₁ : Subgroup M} (eJ : ↥J ≃* ↥P₀) (eJ₁ : ↥J₁ ≃* ↥P₁)
    {q : ℕ} (hq : q.Prime) {T₀ : Subgroup M} (hT₀ : T₀ ≤ P₀)
    (hT₀el : IsElemAbelian q T₀) (hT₀card : Nat.card T₀ = q ^ 2)
    {T₁ : Subgroup M} (hT₁ : T₁ ≤ P₁) (hT₁el : IsElemAbelian q T₁) (hT₁card : Nat.card T₁ = q ^ 2)
    (hZ : Nat.card (Subgroup.center ↥P₁) ∣ 3) :
    (∃ F₀ : Subgroup G, F₀ ≤ J ∧ IsElemAbelian q F₀ ∧ Nat.card F₀ = q ^ 2) ∧
      ∃ (s₀ : G) (hs₀ : s₀ ∈ J₁), orderOf s₀ = q ∧
        (⟨s₀, hs₀⟩ : ↥J₁) ∉ Subgroup.center ↥J₁ := by
  have hZJ₁ : Nat.card (Subgroup.center ↥J₁) ∣ 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr eJ₁).toEquiv]
    exact hZ
  obtain ⟨F₀, hF₀le, hF₀el, hF₀card⟩ :=
    exists_elemAbelian_le_of_mulEquiv eJ hT₀ hT₀el hT₀card
  obtain ⟨T₁', hT₁'le, hT₁'el, hT₁'card⟩ :=
    exists_elemAbelian_le_of_mulEquiv eJ₁ hT₁ hT₁el hT₁card
  obtain ⟨s₀, hs₀, hsq, hsZ⟩ := exists_noncentral_of_elemAbelian hT₁'le hq hT₁'el hT₁'card hZJ₁
  exact ⟨⟨F₀, hF₀le, hF₀el, hF₀card⟩, s₀, hs₀, hsq, hsZ⟩

theorem exists_twE6Six_layers {k : Type} [Field k] [Finite k] [CharP k 2] {n p q : ℕ}
    (hk : Nat.card k = (2 ^ n) ^ 2) (hn : 2 ≤ n) {σ : k ≃+* k} (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : rk2Ord p n = 6) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqd : q ∣ 2 ^ n + 1) {A : Subgroup ↥(twistedE6RootGroup k σ)}
    (hAe : IsElemAbelian p A) (hAcard : Nat.card A = p ^ 3) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ 1 ∧ y ∉ Subgroup.zpowers x ∧
      ∃ J J₁ : Subgroup ↥(twistedE6RootGroup k σ),
        J ≤ Subgroup.centralizer ({x} : Set ↥(twistedE6RootGroup k σ)) ∧
        (J.subgroupOf (Subgroup.centralizer ({x} : Set ↥(twistedE6RootGroup k σ)))).Normal ∧
        CFSG.Open.IsQuasisimple ↥J ∧ p ∣ Nat.card J ∧
        J ≤ Subgroup.centralizer ({y} : Set ↥(twistedE6RootGroup k σ)) ∧
        J₁ ≤ Subgroup.centralizer ({x} : Set ↥(twistedE6RootGroup k σ)) ∧
        CFSG.Open.IsQuasisimple ↥J₁ ∧ (∀ a ∈ J, ∀ b ∈ J₁, Commute a b) ∧
        Nonempty (↥J ≃* ↥(unitarySU 2 n k 3)) ∧
        Nonempty (↥J₁ ≃* ↥(unitarySU 2 n k 3)) ∧
        (∃ F₀ : Subgroup ↥(twistedE6RootGroup k σ), F₀ ≤ J ∧ IsElemAbelian q F₀ ∧
          Nat.card F₀ = q ^ 2) ∧
        ∃ (s₀ : ↥(twistedE6RootGroup k σ)) (hs₀ : s₀ ∈ J₁), orderOf s₀ = q ∧
          (⟨s₀, hs₀⟩ : ↥J₁) ∉ Subgroup.center ↥J₁ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (ModGL Tag.E6 k) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup k σ) := Subtype.finite
  have hpqn : p ∣ (2 ^ n) ^ 2 - 2 ^ n + 1 := dvd_two_pow_sq_sub_of_rk2Ord_six hp hp2 hrk
  have hp7 : 7 ≤ p := seven_le_of_rk2Ord_six hp hp2 hrk
  have hp5 : 5 < p := by omega
  have hp3 : 3 < p := by omega
  have hq3 : 3 ≤ 2 ^ n := by
    have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    norm_num at h
    omega
  have hf : 1 ≤ n := by omega
  have hpq : (p : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) ^ 2 - ((2 ^ n : ℕ) : ℤ) + 1 := by
    have hle : 2 ^ n ≤ (2 ^ n) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h1 : (((2 ^ n) ^ 2 - 2 ^ n + 1 : ℕ) : ℤ) =
        ((2 ^ n : ℕ) : ℤ) ^ 2 - ((2 ^ n : ℕ) : ℤ) + 1 := by
      push_cast [hle]; ring
    rw [← h1]
    exact Int.natCast_dvd_natCast.2 hpqn
  let L := AlgebraicClosure k
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap k L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have hq0 : ((2 ^ n : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame k hf hk σ hσ hp hp3 hpq L
  obtain ⟨c, hc⟩ := hconj A (IsPGroup.of_card hAcard)
  have hT : ∀ a ∈ A, psiT g0 c a ∈
      twistedTorusOf (tw6N L) (twistE6 L (iterateFrobenius L 2 n)) := fun a ha => hc a ha
  obtain ⟨-, ⟨ζ, hζ⟩, hr⟩ := tw6_prime_setup (L := L) hq0 hp hpq
  have hFr : ∀ c : L, iterateFrobenius L 2 n c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  obtain ⟨x, hxA, y, hyA, hx1, hyx, -, -, -, hsuby, hψx, hψy⟩ :=
    exists_twE6Six_selection (ℓ := 2) (f := n) hf hk hσ hp5 hpq (L := L)
      (Fr := iterateFrobenius L 2 n) hFr hζ hAe hAcard hT
  have hW : ((tw6SixFrameWeyl • ·) '' torusRootKernel (psiT g0 c x)) =
      parabolicRoots Tag.E6 CFSG.RankThree.E6.supportA2A2 := by
    rw [hψx, tw6SixZetaPow_torusRootKernel hζ]
    exact tw6SixFrameWeyl_supportA2A2 hp5 hr
  have hxo : orderOf x = p := orderOf_eq_prime (hAe.2 x hxA) hx1
  haveI : Module.Finite (fixSubfield σ) k := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (fixSubfield σ) k := Algebra.IsAlgebraic.of_finite _ k
  haveI : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) k L
  haveI : Finite (fixSubfield σ) := inferInstance
  have hK' : Nat.card (fixSubfield σ) = 2 ^ n :=
    card_fixSubfield_twisted Nat.prime_two hf hk σ hσ
  obtain ⟨KL, hKL⟩ := tw6SixFrame_kernelLayer (K := fixSubfield σ) (Ω := L)
    (Fr := iterateFrobenius L 2 n) hf hK' hq3 hFr (hT x hxA) hW
  obtain ⟨ψ, hψinj, hψ, hψHQ, hψR, hPψ⟩ :=
    tw6_exists_psi_of_kernelLayer (ℓ := 2) (f := n) (σ := σ) hσ hp hp5 hg0C hg0 hperf hxo
      (hT x hxA) KL
  have hPψ' : ∀ i, tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl i ≤
      ψ.range := fun i => by rw [← hKL i]; exact hPψ i
  have hnorm' : ∀ i, ∀ d : ↥(Subgroup.centralizer ({x} : Set ↥(twistedE6RootGroup k σ))),
      ∀ u ∈ tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl i,
        ψ d * u * (ψ d)⁻¹ ∈
          tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl i := by
    intro i d u hu
    rw [← hKL i] at hu ⊢
    exact KL.norm i (ψ d) (hψHQ d) (hψR d) u hu
  obtain ⟨-, -, hqL0, hqL1, hpL0, -, hP01⟩ :=
    tw6SixLayer_data (K := fixSubfield σ) (L := L) (Fr := iterateFrobenius L 2 n)
      hf hK' hq3 hFr hpqn (hT x hxA) hW
  let C : Subgroup ↥(twistedE6RootGroup k σ) :=
    Subgroup.centralizer ({x} : Set ↥(twistedE6RootGroup k σ))
  let J : Subgroup ↥(twistedE6RootGroup k σ) :=
    ((tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl 0).comap ψ).map C.subtype
  let J₁ : Subgroup ↥(twistedE6RootGroup k σ) :=
    ((tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl 1).comap ψ).map C.subtype
  obtain ⟨hJleC, hJn, hJq, hJcard⟩ :=
    quasisimple_normal_map_comap_of_layer (C := C) ψ hψinj (hPψ' 0) hqL0 (hnorm' 0)
  obtain ⟨hJ₁leC, -, hJ₁q, -⟩ :=
    quasisimple_normal_map_comap_of_layer (C := C) ψ hψinj (hPψ' 1) hqL1 (hnorm' 1)
  have hcomm : ∀ a ∈ J, ∀ b ∈ J₁, Commute a b := map_comap_commute hψinj hP01
  have hyT : psiT g0 c y ∈ torusGroup Tag.E6 L := (mem_twistedTorusOf.1 (hT y hyA)).1
  have hP0y : tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n) tw6SixFrameWeyl 0 ≤
      Subgroup.centralizer ({psiT g0 c y} : Set (ModGL Tag.E6 L)) := by
    rw [tw6SixLayer]
    refine inf_le_left.trans ?_
    rw [tw6SixLayerRoots_zero]
    exact (CFSG.LieType.Chevalley.rootSpan_mono hsuby).trans
      (rootSpan_torusRootKernel_le_centralizer hyT)
  have hJy : J ≤ Subgroup.centralizer ({y} : Set ↥(twistedE6RootGroup k σ)) := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 ha
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hP0y (Subgroup.mem_comap.1 hd))
    rw [hψ d] at h1
    exact Subgroup.mem_centralizer_singleton_iff.2 (commute_of_psiT_commute h1)
  have hU : UnitaryFieldData 2 n k :=
    ⟨Nat.prime_two, by omega, by rw [hk, ← pow_mul, mul_comm]⟩
  obtain ⟨⟨eP0⟩, -⟩ := tw6SixLayer_unitary (K' := fixSubfield σ) hn hK' hU hFr
    (hT x hxA) hW 0
  obtain ⟨⟨eP1⟩, hZ1⟩ := tw6SixLayer_unitary (K' := fixSubfield σ) hn hK' hU hFr
    (hT x hxA) hW 1
  have eJP : ↥J ≃* ↥(tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n)
      tw6SixFrameWeyl 0) := comapMapMulEquiv hψinj (hPψ' 0)
  have eJP₁ : ↥J₁ ≃* ↥(tw6SixLayer (L := L) (Fr := iterateFrobenius L 2 n)
      tw6SixFrameWeyl 1) := comapMapMulEquiv hψinj (hPψ' 1)
  have eJ : ↥J ≃* ↥(unitarySU 2 n k 3) := eJP.trans eP0
  have eJ₁ : ↥J₁ ≃* ↥(unitarySU 2 n k 3) := eJP₁.trans eP1
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (q : L) := ⟨by
    intro h
    have h2 : 2 ∣ q := (CharP.cast_eq_zero_iff L 2 q).1 h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 h2).symm⟩
  haveI : HasEnoughRootsOfUnity L q := IsSepClosed.hasEnoughRootsOfUnity L q
  obtain ⟨ζq, hζq⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
  obtain ⟨hst0, hst1⟩ := tw6SixLayerRoots_smul
    (tw6_torusRootKernel_smul_stable (Fr := iterateFrobenius L 2 n) hFr (hT x hxA)) hW
  obtain ⟨T₀, hT₀le, hT₀el, hT₀card⟩ := tw6SixLayer_torus (K := fixSubfield σ) (q := q)
    (Fr := iterateFrobenius L 2 n) hn hK' hFr hqd hst0 hst1 hζq 0
  obtain ⟨T₁, hT₁le, hT₁el, hT₁card⟩ := tw6SixLayer_torus (K := fixSubfield σ) (q := q)
    (Fr := iterateFrobenius L 2 n) hn hK' hFr hqd hst0 hst1 hζq 1
  obtain ⟨⟨F₀, hF₀le, hF₀el, hF₀card⟩, s₀, hs₀, hs₀q, hs₀Z⟩ :=
    exists_qTorus_and_qElement eJP eJP₁ hq hT₀le hT₀el hT₀card hT₁le hT₁el hT₁card hZ1
  have hpJ : p ∣ Nat.card J := by
    rw [hJcard]
    exact hpL0
  exact ⟨x, hxA, y, hyA, hx1, hyx, J, J₁, hJleC, hJn, hJq, hpJ, hJy, hJ₁leC, hJ₁q, hcomm,
    ⟨eJ⟩, ⟨eJ₁⟩, ⟨F₀, hF₀le, hF₀el, hF₀card⟩, s₀, hs₀, hs₀q, hs₀Z⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
