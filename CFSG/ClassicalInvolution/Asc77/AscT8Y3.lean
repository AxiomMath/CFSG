module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y2
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenWire
import CFSG.ClassicalInvolution.Asc77.AscT8RepEng
public import CFSG.ClassicalInvolution.Asc77.AscT8MinProof

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8

section Rep

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ctxOf (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) : Ctx p f Ω W :=
  ⟨hP.1, hP.2.1, hP.2.2.1, hW, thompsonKey G Ω hP W hW, hP.2.2.2⟩

@[expose] noncomputable def mkRep (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K) : Rep Ω W :=
  have h := exists_not_mem_of_mem_D hP.1 hP.2.1 hP.2.2.1 hW hR
  ⟨K, R, h.choose, hK, hR, hRK, h.choose_spec.1, h.choose_spec.2⟩

@[expose] noncomputable def repElt (ρ : Rep Ω W) : ↥(muGroup Ω W) :=
  ⟨ρ.img, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D ρ.hR ρ.hr))⟩

omit [Finite G] in
theorem repElt_mem (ρ : Rep Ω W) : repElt ρ ∈ muDelta Ω W :=
  ⟨ρ.R, ρ.hR, ρ.r, ρ.hr, ρ.hrW, rfl⟩

omit [Finite G] in
theorem exists_rep_of_mem_muDelta {d : ↥(muGroup Ω W)} (hd : d ∈ muDelta Ω W) :
    ∃ ρ : Rep Ω W, d = repElt ρ := by
  obtain ⟨R, hR, r, hr, hrW, hd⟩ := hd
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, Subtype.ext hd⟩

theorem repElt_eq_iff (c : Ctx p f Ω W) (ρ σ : Rep Ω W) : repElt ρ = repElt σ ↔ ρ.K = σ.K :=
  ⟨fun h => c.K_eq_of_img_eq ρ σ (congrArg Subtype.val h),
    fun h => Subtype.ext (c.img_eq_of_K_eq ρ σ h)⟩

theorem repElt_commute_iff (c : Ctx p f Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    repElt ρ * repElt σ = repElt σ * repElt ρ ↔ σ.K ∈ omegaNbr Ω ρ.K :=
  ⟨fun h => c.omega_of_comm ρ σ hne (congrArg Subtype.val h),
    fun h => Subtype.ext (c.comm_of_omega ρ σ h)⟩

theorem repElt_omegaStar (c : Ctx p f Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    σ.K ∈ omegaStarNbr Ω ρ.K :=
  (mem_omegaStarNbr_of_inf_W c.hp c.hq c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK).1

theorem rep_le_centralizer (c : Ctx p f Ω W) (ρ σ : Rep Ω W)
    (hσ : σ.K = ρ.K ∨ σ.K ∈ omegaNbr Ω ρ.K) {v : G} (hv : IsUniqueInvolution σ.K v) :
    ρ.R ≤ Subgroup.centralizer ({v} : Set G) := by
  exact T8V.rep_le_centralizerE (T8V.RepHooks.ofCtx c) ρ σ hσ hv

end Rep

section Std

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem partIHyp_of_std8 (hs : Std8 p f Ω K J S R T W z t) : PartIHyp p f Ω :=
  ⟨hs.stand.odd, hs.stand.five, hs.stand.hyp, hs.stand.aEmpty⟩

theorem mem_DSet_of_le_sylow (hs : Std8 p f Ω K J S R T W z t) {X : Subgroup G}
    (hX : X ∈ RSet Ω) (hXS : X ≤ (S : Subgroup G)) : X ∈ DSet Ω W :=
  ⟨hX, fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hs.hW.2.2 x (hXS hx))⟩

@[expose] noncomputable def stdRepK (hs : Std8 p f Ω K J S R T W z t) : Rep Ω W :=
  mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.stand.mem (mem_DSet_of_le_sylow hs hs.hR.1 hs.hR.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.odd hs.stand.hyp hs.stand.mem hs.hR.1 hs.hR.2.1)

@[expose] noncomputable def stdRepJ (hs : Std8 p f Ω K J S R T W z t) : Rep Ω W :=
  mkRep (partIHyp_of_std8 hs) hs.hW.1 hs.hJ.1 (mem_DSet_of_le_sylow hs hs.hT.1 hs.hT.2.2)
    (T3.isSylow2In_of_mem_RSet_of_le hs.stand.odd hs.stand.hyp hs.hJ.1 hs.hT.1 hs.hT.2.1)

theorem stdRepK_K (hs : Std8 p f Ω K J S R T W z t) : (stdRepK hs).K = K := rfl

theorem stdRepJ_K (hs : Std8 p f Ω K J S R T W z t) : (stdRepJ hs).K = J := rfl

end Std

section Klein

variable {Q : Type} [Group Q]

theorem nonempty_mulEquiv_klein {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hcl : Subgroup.closure ({a, b} : Set Q) = ⊤) :
    Nonempty (Q ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  have hall : ∀ x : Q, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := fun x =>
    mem_closure_pair_involutions ha hb hab (hcl ▸ Subgroup.mem_top x)
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [inv_eq_of_mul_eq_one_right hb] at this
    exact this)
  have hab_a : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab_b : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hcard : Nat.card Q = 4 := by
    have : (Set.univ : Set Q) = {1, a, b, a * b} := by
      ext x
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
      exact hall x
    rw [← Set.ncard_univ, this]
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm ha1, Ne.symm hb1, Ne.symm hab1]),
      Set.ncard_insert_of_notMem (by simp [hne, Ne.symm hab_a]), Set.ncard_pair (Ne.symm hab_b)]
  have : Nontrivial Q := ⟨⟨a, 1, ha1⟩⟩
  have hexp : Monoid.exponent Q = 2 := by
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    rcases hall g with hg' | hg' | hg' | hg' <;> rw [hg', pow_two]
    · exact absurd hg' hg
    · exact ha
    · exact hb
    · calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
  have : IsKleinFour Q := ⟨hcard, hexp⟩
  exact IsKleinFour.nonempty_mulEquiv

end Klein

section Dichotomy

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_third_of_abelian (hs : Std8 p f Ω K J S R T W z t) (hE4 : ¬ MuIsoE4 Ω W)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ τ : Rep Ω W, τ.K ≠ K ∧ τ.K ≠ J := by
  have hP := partIHyp_of_std8 hs
  have hc := ctxOf hP hs.hW.1
  by_contra hcon
  push Not at hcon
  set a := repElt (stdRepK hs) with ha
  set b := repElt (stdRepJ hs) with hb
  have hall : ∀ d ∈ muDelta Ω W, d = a ∨ d = b := by
    intro d hd
    obtain ⟨τ, rfl⟩ := exists_rep_of_mem_muDelta hd
    by_cases h1 : τ.K = K
    · left
      exact (repElt_eq_iff hc τ (stdRepK hs)).mpr h1
    · right
      exact (repElt_eq_iff hc τ (stdRepJ hs)).mpr (hcon τ h1)
  have haΔ : a ∈ muDelta Ω W := repElt_mem _
  have hbΔ : b ∈ muDelta Ω W := repElt_mem _
  have hne : a ≠ b := fun h =>
    hs.hJ.2.1 ((repElt_eq_iff hc (stdRepK hs) (stdRepJ hs)).mp h).symm
  apply hE4
  refine nonempty_mulEquiv_klein (muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hs.hW.1 haΔ)
    (muDelta_mul_self hP.1 hP.2.1 hP.2.2.1 hs.hW.1 hbΔ)
    (Subtype.ext (hab _ a.2 _ b.2)) (muDelta_ne_one hs.hW.1 haΔ) (muDelta_ne_one hs.hW.1 hbΔ) hne
    ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Ω W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rcases hall d hd with h | h
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [h]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

omit [Finite G] in
theorem exists_noncomm_of_not_abelian
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ d ∈ muDelta Ω W, ∃ e ∈ muDelta Ω W, d * e ≠ e * d := by
  by_contra hcon
  push Not at hcon
  apply hab
  have h1 : ∀ y : ↥(muGroup Ω W), ∀ d ∈ muDelta Ω W, d * y = y * d := by
    intro y d hd
    have : (⊤ : Subgroup ↥(muGroup Ω W)) ≤ Subgroup.centralizer ({d} : Set ↥(muGroup Ω W)) := by
      rw [← closure_muDelta_eq_top Ω W, Subgroup.closure_le]
      intro e he
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hcon e he d hd
    have hy := this (Subgroup.mem_top y)
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy.symm
  have h2 : ∀ x y : ↥(muGroup Ω W), x * y = y * x := by
    intro x y
    have : (⊤ : Subgroup ↥(muGroup Ω W)) ≤ Subgroup.centralizer ({y} : Set ↥(muGroup Ω W)) := by
      rw [← closure_muDelta_eq_top Ω W, Subgroup.closure_le]
      intro d hd
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact h1 y d hd
    have hx := this (Subgroup.mem_top x)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    exact hx
  intro x hx y hy
  exact congrArg Subtype.val (h2 ⟨x, hx⟩ ⟨y, hy⟩)

end Dichotomy

section LayerTri

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem layerImg_ne_of_involutions (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {x : G}
    (hx : x * x = 1) {K J : Subgroup G} (hK : XMem Ω x K) (hJ : XMem Ω x J) {zK zJ : G}
    (hzK : IsUniqueInvolution K zK) (hzJ : IsUniqueInvolution J zJ) (hcomm : zK * zJ = zJ * zK)
    (hne : zK ≠ zJ) : layerImg Ω x K ≠ layerImg Ω x J := by
  intro h
  obtain ⟨n, hn, hnK⟩ := exists_oddCore_conj_of_layerImg_eq hp hq hΩ hx hK hJ h
  have hzn : IsUniqueInvolution J (n * zK * n⁻¹) := hnK ▸ hzK.conj n
  have hzJn : zJ = n * zK * n⁻¹ := hzJ.eq hzn
  obtain ⟨R₀, hR₀, hR₀x⟩ := hK.2.2
  have hR₀L : IsSylow2In R₀ (layerRes x K) :=
    hK.isSylow2In_layerRes_of_le hp hq hΩ hx hR₀ (fun r hr => mem_cenZ_iff.mpr (hR₀x r hr))
  have h8 := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK.1 hR₀)
  have hzR₀ : zK ∈ R₀ := T3.mem_of_isPGroup hzK hR₀.1 hR₀.2.1 (by omega)
  have hzY : zK ∈ layerJoin Ω x := le_layerJoin ⟨K, hK, rfl⟩ (hR₀L.1 hzR₀)
  have hnorm := mem_normalizer_oddCoreOf hzY
  have hzi : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
  have hprod : zK * zJ ∈ oddCoreOf (layerJoin Ω x) := by
    have h1 : zK * n * zK⁻¹ ∈ oddCoreOf (layerJoin Ω x) :=
      (Subgroup.mem_normalizer_iff.mp hnorm n).mp hn
    have h2 := (oddCoreOf (layerJoin Ω x)).mul_mem h1 ((oddCoreOf (layerJoin Ω x)).inv_mem hn)
    have e : zK * zJ = zK * n * zK⁻¹ * n⁻¹ := by rw [hzJn, hzi]; group
    rw [e]
    exact h2
  have hsq : (zK * zJ) * (zK * zJ) = 1 := by
    calc zK * zJ * (zK * zJ) = zK * (zJ * zK) * zJ := by group
      _ = zK * (zK * zJ) * zJ := by rw [hcomm]
      _ = (zK * zK) * (zJ * zJ) := by group
      _ = 1 := by rw [hzK.sq, hzJ.sq, one_mul]
  have h1 : zK * zJ ≠ 1 := mul_ne_one_of_ne hzK.sq hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (zK * zJ) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) h1
  have hodd := odd_natCard_oddCoreOf (layerJoin Ω x)
  have hdvd : orderOf (⟨zK * zJ, hprod⟩ : oddCoreOf (layerJoin Ω x)) ∣
      Nat.card (oddCoreOf (layerJoin Ω x)) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)

theorem dstarConnected_layerFamQ_of_reps (hD4 : Ih8D4Star p f) {W : Subgroup G}
    (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω) (hn : CITBelowU p f (Nat.card G))
    (hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M) (ρ : Fin 3 → Rep Ω W) (zz : Fin 3 → G)
    (hzz : ∀ i, IsUniqueInvolution (ρ i).K (zz i)) (hne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K)
    (hnbr : ∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K)
    (hnc : ¬ ({zz 0 * zz 1} : Set G) ⊆ Subgroup.center G) :
    T3.DStarConnected (layerFamQ Ω (zz 0 * zz 1)) := by
  have c := ctxOf hP hW
  have hp := hP.1
  have hq := hP.2.1
  have hΩ := hP.2.2.1
  have hzW : ∀ i, zz i ∈ W := fun i =>
    (uniqueInvolution_mem_W hp hq hΩ hW (ρ i).hK (ρ i).hR (ρ i).hRK (hzz i)).2
  have hzzc : ∀ i j, zz i * zz j = zz j * zz i := fun i j => c.comm_W _ (hzW i) _ (hzW j)
  have haa : zz 0 * zz 1 * (zz 0 * zz 1) = 1 := by
    calc zz 0 * zz 1 * (zz 0 * zz 1) = zz 0 * (zz 1 * zz 0) * zz 1 := by group
      _ = zz 0 * (zz 0 * zz 1) * zz 1 := by rw [hzzc 1 0]
      _ = (zz 0 * zz 0) * (zz 1 * zz 1) := by group
      _ = 1 := by rw [(hzz 0).sq, (hzz 1).sq, one_mul]
  have haW : zz 0 * zz 1 ∈ W := W.mul_mem (hzW 0) (hzW 1)
  have hrel : ∀ i j, (ρ j).K = (ρ i).K ∨ (ρ j).K ∈ omegaNbr Ω (ρ i).K := by
    intro i j
    by_cases h : i = j
    · subst h
      exact Or.inl rfl
    · exact Or.inr (hnbr i j h)
  have hRc : ∀ i j, (ρ i).R ≤ Subgroup.centralizer ({zz j} : Set G) := fun i j =>
    rep_le_centralizer c (ρ i) (ρ j) (hrel i j) (hzz j)
  have hRa : ∀ i, (ρ i).R ≤ cenZ (zz 0 * zz 1) := by
    intro i r hr
    rw [mem_cenZ_iff]
    have h0 := Subgroup.mem_centralizer_singleton_iff.mp (hRc i 0 hr)
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hRc i 1 hr)
    calc r * (zz 0 * zz 1) = (r * zz 0) * zz 1 := by group
      _ = (zz 0 * r) * zz 1 := by rw [h0]
      _ = zz 0 * (r * zz 1) := by group
      _ = zz 0 * (zz 1 * r) := by rw [h1]
      _ = (zz 0 * zz 1) * r := by group
  have hX : ∀ i, XMem Ω (zz 0 * zz 1) (ρ i).K := by
    intro i
    refine ⟨(ρ i).hK, ?_, (ρ i).R, (ρ i).hRK, fun r hr => mem_cenZ_iff.mp (hRa i hr)⟩
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (ρ i).hK (hnt _ (ρ i).hK) (hzz i)
      (Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W _ haW (zz i) (hzW i)))
  have hzne : ∀ i j, i ≠ j → zz i ≠ zz j := by
    intro i j hij h
    have hj : IsUniqueInvolution (ρ j).K (zz i) := by rw [h]; exact hzz j
    exact hne i j hij (hnt _ (ρ i).hK _ ⟨(ρ j).hK, zz i, hzz i, hj⟩).symm
  have himg : ∀ i j, i ≠ j →
      layerImg Ω (zz 0 * zz 1) (ρ i).K ≠ layerImg Ω (zz 0 * zz 1) (ρ j).K := fun i j hij =>
    layerImg_ne_of_involutions hp hq hΩ haa (hX i) (hX j) (hzz i) (hzz j) (hzzc i j)
      (hzne i j hij)
  have hadj : ∀ i j, i ≠ j → layerImg Ω (zz 0 * zz 1) (ρ j).K ∈
      omegaNbr (layerFamQ Ω (zz 0 * zz 1)) (layerImg Ω (zz 0 * zz 1) (ρ i).K) := by
    intro i j hij
    refine layerImg_omegaNbr hp hq hΩ haa (hX i) (hX j) (ρ j).hRK (hRa j) ?_ (himg i j hij)
    exact hΩ.le_normalizer_of_le_centralizer hp hq (ρ i).hK (ρ j).hK (hne i j hij) (hzz i)
      (ρ j).hRK.1 (ρ j).hRK.2.1
      (by have := hΩ.eight_le_of_mem_RSet hp (ρ j).hR.1; omega) (hRc j i)
  have hlt := card_layerQuot_lt (Ω := Ω) hnc
  exact dstarConnected_of_triangle hn hlt hp hq hD4 (hypOmegaMod_layerQuot hp hq hΩ haa)
    (CFSG.ComponentClassification.OddCore.quotient_corefree _) (omegaGen_layerFamQ Ω _)
    (noTwins_layerQuot hp hq hΩ hnt haa) (fun i => layerImg Ω (zz 0 * zz 1) (ρ i).K)
    (fun i => layerImg_mem (hX i))
    (fun i j h => by
      by_contra hij
      exact himg i j hij h) hadj

end LayerTri

end T8

end CFSG.ClassicalInvolution.Asc77
