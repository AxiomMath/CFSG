module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Planes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

theorem ncard_sdiff_eq_mul_of_partition {α ι : Type*} [Finite α] {S E : Set α} {𝒱 : Set ι}
    (h𝒱 : 𝒱.Finite) {D : ι → Set α} {d : ℕ} (hcover : S \ E = ⋃ i ∈ 𝒱, D i \ E)
    (hdisj : 𝒱.PairwiseDisjoint fun i => D i \ E) (hcard : ∀ i ∈ 𝒱, (D i \ E).ncard = d) :
    (S \ E).ncard = 𝒱.ncard * d := by
  classical
  have : Fintype α := Fintype.ofFinite α
  set T := h𝒱.toFinset with hT
  set t : ι → Finset α := fun i => (D i \ E).toFinset with ht
  have hU : S \ E = ((T.biUnion t : Finset α) : Set α) := by
    rw [hcover]
    ext a
    simp [T, t]
  rw [hU, Set.ncard_coe_finset, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl fun i hi => (show (t i).card = d by
        rw [ht, ← Set.ncard_eq_toFinset_card']
        exact hcard i (h𝒱.mem_toFinset.mp hi)),
      Finset.sum_const, smul_eq_mul, Set.ncard_eq_toFinset_card 𝒱 h𝒱]
  · rw [hT, h𝒱.coe_toFinset]
    intro i hi j hj hij
    have := hdisj hi hj hij
    simp only [Function.onFun, t] at this ⊢
    rwa [Set.disjoint_toFinset]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem card_le_of_mem_inf_frame (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hD64 : 64 ≤ Nat.card D) {u : G} (huR : u ∈ R)
    (huD : u ∈ D) (hu1 : u ≠ 1) : Nat.card D ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  set K := centralizer (A : Set G) with hK
  have hRA : R ≤ K := hR.le
  have hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hD2 := isPGroup_two_of_isElemAbelian hD
  have hDNK : D ≤ normalizer (K : Set G) := fun d hd =>
    RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hRA huR) hu1
      (hF.elemR.2 u huR) (hDc d hd u huD)
  have hDN : D ≤ normalizer (A : Set G) := hNK ▸ hDNK
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
  have hle := le_sup_centralizer_of_sixteen_le hE16 hF.quasisimple.1 e₀ hR hDN hD
    (by rw [hF.cardR]; omega)
  obtain ⟨X, hX, hDX⟩ := AschbacherTheorem3.exists_isSylowOf_le hD2 (le_sup_left : D ≤ D ⊔ K)
  have hR' : IsSylowOf 2 (X ⊓ K) K :=
    hX.inf_of_le_normalizer le_sup_right (sup_le hDNK le_normalizer)
  have hDR' : D ≤ normalizer ((X ⊓ K : Subgroup G) : Set G) := fun d hd =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer (hDX hd), hDNK hd⟩
  have hDAR' := le_sup_of_le_sup_normalizer hR' hD2 hDR' hle
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hR' hR
  set R' := X ⊓ K with hR'def
  have hR'e : IsElemAbelian 2 R' := hc ▸ AS76b.isElemAbelian_rightConjugate hF.elemR c
  have hR'4 : Nat.card R' = 4 := by rw [← hc, rightConjugate_card, hF.cardR]
  have hDC : D ≤ centralizer (R' : Set G) := hDAR'.trans (sup_le
    (le_centralizer_iff.mp hR'.le)
    fun r hr => mem_centralizer_iff.mpr fun s hs =>
      congrArg Subtype.val (hR'e.1.is_comm.comm ⟨s, hs⟩ ⟨r, hr⟩))
  have hDR'e := isElemAbelian_sup_of_le_centralizer hD hR'e hDC
  have hcard := card_le_of_isElemAbelian_le_sup_sylow_frame h11 hF hL hodd hR' hR'4 hDR'e
    (sup_le hDAR' le_sup_right)
  exact (card_le_of_le le_sup_left).trans hcard

theorem card_le_of_mem_rightConjugate (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {D : Subgroup G} (hD : IsElemAbelian 2 D) (hD64 : 64 ≤ Nat.card D) {k u : G}
    (hu : u ∈ rightConjugate R k) (huD : u ∈ D) (hu1 : u ≠ 1) : Nat.card D ≤ 64 := by
  have h := card_le_of_mem_inf_frame h11 hE16 hF hL hodd
    (AS76b.isElemAbelian_rightConjugate hD k⁻¹) (by rw [rightConjugate_card]; exact hD64)
    ((mem_rightConjugate_iff R k u).mp hu) ?_ (fun h => hu1 ?_)
  · rwa [rightConjugate_card] at h
  · rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using huD
  · have := congrArg (fun z => k⁻¹ * z * k) h
    simpa [mul_assoc] using this

theorem rightConjugate_le_of_mem_inf (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    {W : Subgroup G} (hW : IsElemAbelian 2 W) (hW64 : Nat.card W = 64) (hWP : W ≤ sec2P E)
    {k u : G} (hkP : rightConjugate R k ≤ sec2P E) (hu : u ∈ rightConjugate R k) (huW : u ∈ W)
    (hu1 : u ≠ 1) : rightConjugate R k ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hu' : k * u * k⁻¹ ∈ R := (mem_rightConjugate_iff R k u).mp hu
  have huD : k * u * k⁻¹ ∈ rightConjugate W k⁻¹ := by
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using huW
  have hu1' : k * u * k⁻¹ ≠ 1 := fun h => hu1 (by
    have := congrArg (fun z => k⁻¹ * z * k) h
    simpa [mul_assoc] using this)
  obtain ⟨c, hcK, hRc, -⟩ := exists_rightConjugate_le_of_mem_inf_frame h11 hE16 hF hL hodd
    (AS76b.isElemAbelian_rightConjugate hW k⁻¹) (by rw [rightConjugate_card, hW64]) hu' huD hu1'
  set P₀ := rightConjugate (sec2P E) k⁻¹ with hP₀
  have hRP₀ : R ≤ P₀ := by
    intro r hr
    rw [hP₀, mem_rightConjugate_iff, inv_inv]
    apply hkP
    rw [mem_rightConjugate_iff]
    simpa [mul_assoc] using hr
  have hRcP₀ : rightConjugate R c ≤ P₀ :=
    hRc.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hWP k⁻¹)
  have hRcK : rightConjugate R c ≤ centralizer (A : Set G) :=
    AschbacherTheorem3.rightConjugate_le_of_mem hR.le hcK
  have hP₀2 : IsPGroup 2 P₀ := (Sec2.isPGroup_sec2P E).map _
  have heq : P₀ ⊓ centralizer (A : Set G) = R :=
    hR.eq_of_le (le_inf hRP₀ hR.le) inf_le_right (hP₀2.to_le inf_le_left)
  have hRcR : rightConjugate R c = R := by
    have hle : rightConjugate R c ≤ R := (le_inf hRcP₀ hRcK).trans heq.le
    exact eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  have hRD : R ≤ rightConjugate W k⁻¹ := hRcR ▸ hRc
  intro y hy
  have h1 : k * y * k⁻¹ ∈ rightConjugate W k⁻¹ := hRD ((mem_rightConjugate_iff R k y).mp hy)
  rw [mem_rightConjugate_iff] at h1
  simpa [mul_assoc] using h1

theorem le_sec2P_of_frame (hF : Frame G A A R g E F) : E ≤ sec2P E :=
  Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl

theorem sec2F0_le_sec2P (hF : Frame G A A R g E F) (x : G) : sec2F0 A E x ≤ sec2P E :=
  sup_le (inf_le_left.trans (le_sec2P_of_frame hF)) inf_le_right

theorem mem_normalizer_of_mem_inf_normalizer (hF : Frame G A A R g E F) {n : G}
    (hn : n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G)) :
    n ∈ normalizer (E : Set G) ∧ n ∈ normalizer (R : Set G) := by
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hnR : n ∈ normalizer (R : Set G) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) n hn.1).symm)
  refine ⟨?_, hnR⟩
  have hEeq := eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le
  rw [← rightConjugate_eq_self_iff] at hnR ⊢
  have hnH := (rightConjugate_eq_self_iff _ n).mpr hn.2
  rw [hEeq, rightConjugate_sup', hnH, hnR]

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem rightConjugate_inf_inf_eq_bot {k : G} (hkP : rightConjugate R k ≤ sec2P E) :
    rightConjugate R k ⊓ (E ⊓ A) = ⊥ := by
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  rw [eq_bot_iff]
  intro u hu
  rw [mem_bot]
  by_contra hu1
  have hle := rightConjugate_le_of_mem_inf h11 hE16 hF hL hodd hF.elemE hF.cardE
    (le_sec2P_of_frame hF) hkP hu.1 hu.2.1 hu1
  have hpt : rightConjugate R k ∈ pointsIn R E := ⟨hle, k, rfl⟩
  have hmem : u ∈ rightConjugate R k ⊓ (E ⊓ A) := hu
  rw [hD.inf_H _ hpt, mem_bot] at hmem
  exact hu1 hmem

theorem card_inf_sup_rightConjugate {k : G} (hkP : rightConjugate R k ≤ sec2P E) :
    Nat.card ((E ⊓ A) ⊔ rightConjugate R k : Subgroup G) = 64 := by
  have hN : rightConjugate R k ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    hkP.trans ((sec2P_le_centralizer_inf h11 hE16 hF hL hodd).trans
      (centralizer_le_normalizer _))
  rw [AschbacherTheorem3.card_sup_of_le_normalizer hN
    (by rw [inf_comm]; exact rightConjugate_inf_inf_eq_bot h11 hE16 hF hL hodd hkP),
    card_inf_left hF hodd, rightConjugate_card, hF.cardR]

theorem inf_le_of_mem_planes_of_le {V : Subgroup G} (hV : V ∈ planes E F)
    (hVP : V ≤ sec2P E) : E ⊓ A ≤ V := by
  obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  obtain ⟨h, hVh⟩ := hV
  have hRV : rightConjugate R h ≤ V := by
    rcases hVh with rfl | rfl
    · exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.R_le_E h
    · exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.R_le_F h
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hu : h⁻¹ * r * h ∈ rightConjugate R h := AschbacherTheorem3.conj_mem_rightConjugate hr h
  have hu1 : h⁻¹ * r * h ≠ 1 := fun h1 => hr1 (by
    have := congrArg (fun z => h * z * h⁻¹) h1
    simpa [mul_assoc] using this)
  have hEAe : IsElemAbelian 2 (E ⊓ A) := AS76b.IsElemAbelian.mono hF.elemE inf_le_left
  have hVC : V ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    hVP.trans (sec2P_le_centralizer_inf h11 hE16 hF hL hodd)
  have hDe := isElemAbelian_sup_of_le_centralizer hVe hEAe hVC
  have hcard := card_le_of_mem_rightConjugate h11 hE16 hF hL hodd hDe
    (hV64 ▸ card_le_of_le le_sup_left) hu (mem_sup_left (hRV hu)) hu1
  have heq : V = V ⊔ (E ⊓ A) := eq_of_le_of_card_ge le_sup_left (by rw [hV64]; exact hcard)
  exact le_sup_right.trans heq.ge

theorem mem_centralizerMod_iff_of_frame {c : G} :
    c ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) ↔
      c ∈ sec2P E ∧ rightConjugate R c ≤ E ⊓ F := by
  constructor
  · intro hc
    obtain ⟨hcP, -, hcomm⟩ := mem_centralizerMod.mp hc
    refine ⟨hcP, fun y hy => ?_⟩
    have hr : c * y * c⁻¹ ∈ R := (mem_rightConjugate_iff R c y).mp hy
    have h1 := hcomm _ (mem_sup_left hr)
    have hy' : y = (c * y * c⁻¹) * ((c * y * c⁻¹)⁻¹ * c⁻¹ * (c * y * c⁻¹) * c) := by group
    rw [← hF.sup_sec2Z, hy']
    exact mul_mem (mem_sup_left hr) (mem_sup_right h1)
  · rintro ⟨hcP, hcR⟩
    exact mem_centralizerMod_of_rightConjugate_le h11 hE16 hF hL hodd hcP hcR

theorem exists_conj_mem_centralizerMod {p : G} (hp : p ∈ sec2P E) :
    ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      n⁻¹ * p * n ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  by_cases hpE : p ∈ E
  · refine ⟨1, ⟨A.one_mem, Subgroup.one_mem _⟩, ?_⟩
    simpa using le_centralizerMod hF hpE
  have hQ : rightConjugate R p ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (Sec2.sec2P_le E hp)
  have hQR : rightConjugate R p ≠ R := fun h =>
    hpE (hPR.le ⟨hp, (rightConjugate_eq_self_iff R p).mp h⟩)
  obtain ⟨-, -, -, htr, -⟩ := step15_points h11 hE16 hF hL hodd
  obtain ⟨n, hn, hnQ⟩ := htr _ hQ hQR
  obtain ⟨hnE, hnR⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
  refine ⟨n, hn, (mem_centralizerMod_iff_of_frame h11 hE16 hF hL hodd).mpr ⟨?_, ?_⟩⟩
  · have hnP := Sec2.normalizer_le_normalizer_sec2P E (inv_mem hnE)
    have := (mem_normalizer_iff.mp hnP p).mp hp
    simpa using this
  · have hRn : rightConjugate R n⁻¹ = R :=
      (rightConjugate_eq_self_iff R n⁻¹).mpr (inv_mem hnR)
    rw [← rightConjugate_mul, ← rightConjugate_mul, hRn, hnQ, rightConjugate_mul,
      inv_mul_cancel, rightConjugate_one]
    exact hF.inf_eq ▸ le_sup_right

theorem mem_rightConjugate_centralizerMod_iff {m : G} (hmE : m ∈ normalizer (E : Set G))
    (hmR : m ∈ normalizer (R : Set G)) {p : G} :
    p ∈ rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m ↔
      p ∈ sec2P E ∧ rightConjugate R p ≤ rightConjugate (E ⊓ F) m := by
  have hmP := Sec2.normalizer_le_normalizer_sec2P E hmE
  rw [mem_rightConjugate_iff, mem_centralizerMod_iff_of_frame h11 hE16 hF hL hodd]
  have hRm : rightConjugate R m = R := (rightConjugate_eq_self_iff R m).mpr hmR
  have hR' : rightConjugate R (m * p * m⁻¹) = rightConjugate (rightConjugate R p) m⁻¹ := by
    rw [← rightConjugate_mul, ← rightConjugate_mul, hRm]
  rw [hR']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem hmP) _).mp h1
      simpa [mul_assoc] using this
    · have := AschbacherTheorem3.rightConjugate_le_rightConjugate h2 m
      rwa [rightConjugate_rightConjugate_inv] at this
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_normalizer_iff.mp hmP p).mp h1, ?_⟩
    have := AschbacherTheorem3.rightConjugate_le_rightConjugate h2 m⁻¹
    rwa [rightConjugate_inv_rightConjugate] at this

theorem rightConjugate_centralizerMod_eq {m m' : G} (hmE : m ∈ normalizer (E : Set G))
    (hmR : m ∈ normalizer (R : Set G)) (hm'E : m' ∈ normalizer (E : Set G))
    (hm'R : m' ∈ normalizer (R : Set G)) {t : G}
    (ht : t ∈ rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m)
    (ht' : t ∈ rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m')
    (htE : t ∉ E) :
    rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m =
      rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m' := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  obtain ⟨htP, htL⟩ := (mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd hmE hmR).mp ht
  obtain ⟨-, htL'⟩ :=
    (mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd hm'E hm'R).mp ht'
  have hQ : rightConjugate R t ∈ pointsIn R E :=
    rightConjugate_mem_pointsIn hD.self_mem (Sec2.sec2P_le E htP)
  have hQR : rightConjugate R t ≠ R := fun h =>
    htE (hPR.le ⟨htP, (rightConjugate_eq_self_iff R t).mp h⟩)
  have hcard := card_sup_of_mem_pointsIn hKte hF.sylowR hD.comm hD.self_mem hQ (Ne.symm hQR)
  rw [hF.cardR] at hcard
  have hRL : ∀ {m₀ : G}, m₀ ∈ normalizer (R : Set G) → R ≤ rightConjugate (E ⊓ F) m₀ := by
    intro m₀ hm₀
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate
      (hF.inf_eq ▸ le_sup_left : R ≤ E ⊓ F) m₀
    rwa [(rightConjugate_eq_self_iff R m₀).mpr hm₀] at h
  have hL16 : ∀ m₀ : G, Nat.card (rightConjugate (E ⊓ F) m₀) = 16 := fun m₀ => by
    rw [rightConjugate_card, hF.card_inf]
  have hLm : R ⊔ rightConjugate R t = rightConjugate (E ⊓ F) m :=
    eq_of_le_of_card_ge (sup_le (hRL hmR) htL) (by rw [hL16, hcard])
  have hLm' : R ⊔ rightConjugate R t = rightConjugate (E ⊓ F) m' :=
    eq_of_le_of_card_ge (sup_le (hRL hm'R) htL') (by rw [hL16, hcard])
  ext p
  rw [mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd hmE hmR,
    mem_rightConjugate_centralizerMod_iff h11 hE16 hF hL hodd hm'E hm'R, ← hLm, ← hLm']

section Plane

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include hx hxS

theorem centralizerMod_eq_sup_sec2F0 :
    centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) = E ⊔ sec2F0 A E x := by
  rw [← sec2S_inf_sec2P h11 hE16 hF hL hodd, inf_comm,
    sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS]

theorem le_or_le_of_le_rightConjugate {m : G} (hmE : m ∈ normalizer (E : Set G))
    {U : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hU : U ≤ rightConjugate (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) m) :
    U ≤ E ∨ U ≤ rightConjugate (sec2F0 A E x) m := by
  have hU' : rightConjugate U m⁻¹ ≤ sec2P E ⊓ sec2S A R E F := by
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hU m⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
      ← sec2S_inf_sec2P h11 hE16 hF hL hodd, inf_comm] at h
    exact h
  have hEm : rightConjugate E m = E := (rightConjugate_eq_self_iff E m).mpr hmE
  rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS hU'
    (AS76b.isElemAbelian_rightConjugate hUe m⁻¹) with h | h
  · left
    have h' := AschbacherTheorem3.rightConjugate_le_rightConjugate h m
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one, hEm] at h'
  · right
    have h' := AschbacherTheorem3.rightConjugate_le_rightConjugate h m
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h'

theorem eq_or_exists_of_mem_planes {V : Subgroup G} (hV : V ∈ planes E F) (hVP : V ≤ sec2P E) :
    V = E ∨ ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      V = rightConjugate (sec2F0 A E x) n := by
  obtain ⟨-, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV
  obtain ⟨hD, -⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hVpl := hV
  obtain ⟨h, hVh⟩ := hV
  have hRV : rightConjugate R h ≤ V := by
    rcases hVh with rfl | rfl
    · exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.R_le_E h
    · exact AschbacherTheorem3.rightConjugate_le_rightConjugate hF.R_le_F h
  obtain ⟨r, hr, hr1⟩ := hD.exists_ne_one
  have hb : h⁻¹ * r * h ∈ rightConjugate R h := AschbacherTheorem3.conj_mem_rightConjugate hr h
  have hb1 : h⁻¹ * r * h ≠ 1 := fun h1 => hr1 (by
    have := congrArg (fun z => h * z * h⁻¹) h1
    simpa [mul_assoc] using this)
  obtain ⟨n, hn, hbn⟩ := exists_conj_mem_centralizerMod h11 hE16 hF hL hodd (hVP (hRV hb))
  obtain ⟨hnE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
  have hnP := Sec2.normalizer_le_normalizer_sec2P E hnE
  have hPn : rightConjugate (sec2P E) n = sec2P E := (rightConjugate_eq_self_iff _ n).mpr hnP
  have hV'P : rightConjugate V n ≤ sec2P E :=
    hPn ▸ AschbacherTheorem3.rightConjugate_le_rightConjugate hVP n
  have hB'V' : rightConjugate R (h * n) ≤ rightConjugate V n := by
    rw [← rightConjugate_mul]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hRV n
  have hB'P := hB'V'.trans hV'P
  have hu : n⁻¹ * (h⁻¹ * r * h) * n ∈ rightConjugate R (h * n) := by
    rw [← rightConjugate_mul]
    exact AschbacherTheorem3.conj_mem_rightConjugate hb n
  have hu1 : n⁻¹ * (h⁻¹ * r * h) * n ≠ 1 := fun h1 => hb1 (by
    have := congrArg (fun z => n * z * n⁻¹) h1
    simpa [mul_assoc] using this)
  have hUe : IsElemAbelian 2 (rightConjugate R (h * n) ⊓ (sec2P E ⊓ sec2S A R E F)) :=
    AS76b.IsElemAbelian.mono (AS76b.isElemAbelian_rightConjugate hF.elemR _) inf_le_left
  have huU : n⁻¹ * (h⁻¹ * r * h) * n ∈
      rightConjugate R (h * n) ⊓ (sec2P E ⊓ sec2S A R E F) := by
    refine ⟨hu, ?_⟩
    rw [inf_comm, sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact hbn
  have hV'pl : rightConjugate V n ∈ planes E F := rightConjugate_mem_planes hVpl n
  have hV'64 : Nat.card (rightConjugate V n) = 64 := by rw [rightConjugate_card, hV64]
  have hEAV' := inf_le_of_mem_planes_of_le h11 hE16 hF hL hodd hV'pl hV'P
  have hcard := card_inf_sup_rightConjugate h11 hE16 hF hL hodd hB'P
  have key : ∀ W : Subgroup G, IsElemAbelian 2 W → Nat.card W = 64 → W ≤ sec2P E →
      E ⊓ A ≤ W → n⁻¹ * (h⁻¹ * r * h) * n ∈ W → rightConjugate V n = W := by
    intro W hWe hW64 hWP hEAW huW
    have hB'W := rightConjugate_le_of_mem_inf h11 hE16 hF hL hodd hWe hW64 hWP hB'P hu huW hu1
    have h1 : (E ⊓ A) ⊔ rightConjugate R (h * n) = rightConjugate V n :=
      eq_of_le_of_card_ge (sup_le hEAV' hB'V') (by rw [hcard, hV'64])
    have h2 : (E ⊓ A) ⊔ rightConjugate R (h * n) = W :=
      eq_of_le_of_card_ge (sup_le hEAW hB'W) (by rw [hcard, hW64])
    rw [← h1, h2]
  have hVeq : V = rightConjugate (rightConjugate V n) n⁻¹ :=
    (rightConjugate_inv_rightConjugate V n).symm
  rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS inf_le_right hUe with hUE | hUF
  · left
    rw [hVeq, key E hF.elemE hF.cardE (le_sec2P_of_frame hF) inf_le_left (hUE huU)]
    exact (rightConjugate_eq_self_iff E n⁻¹).mpr (inv_mem hnE)
  · right
    refine ⟨n⁻¹, inv_mem hn, ?_⟩
    rw [hVeq, key (sec2F0 A E x) (isElemAbelian_sec2F0 (x := x) h11 hE16 hF hL hodd)
      (card_sec2F0 h11 hE16 hF hL hodd hx hxS) (sec2F0_le_sec2P hF x) le_sup_left (hUF huU)]

theorem rightConjugate_sec2F0_ne {n : G} (hnE : n ∈ normalizer (E : Set G)) :
    rightConjugate (sec2F0 A E x) n ≠ E := by
  intro h
  have h' : sec2F0 A E x = E := by
    have := congrArg (fun V => rightConjugate V n⁻¹) h
    simp only [rightConjugate_inv_rightConjugate] at this
    rw [this]
    exact (rightConjugate_eq_self_iff E n⁻¹).mpr (inv_mem hnE)
  have h16 := card_inf_left hF hodd
  rw [← sec2F0_inf_eq h11 hE16 hF hL hodd hx hxS, h', inf_idem, hF.cardE] at h16
  omega

variable (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include h4

theorem rightConjugate_sec2F0_mem {n : G} (hnE : n ∈ normalizer (E : Set G)) :
    rightConjugate (sec2F0 A E x) n ∈ planes E F ∧ rightConjugate (sec2F0 A E x) n ≤ sec2P E ∧
      rightConjugate (sec2F0 A E x) n ≠ E := by
  have hnP := Sec2.normalizer_le_normalizer_sec2P E hnE
  refine ⟨rightConjugate_mem_planes (sec2F0_mem_planes h11 hE16 hF hL hodd hx hxS h4) n, ?_,
    rightConjugate_sec2F0_ne h11 hE16 hF hL hodd hx hxS hnE⟩
  rw [← (rightConjugate_eq_self_iff _ n).mpr hnP]
  exact AschbacherTheorem3.rightConjugate_le_rightConjugate (sec2F0_le_sec2P hF x) n

theorem planes_sec2P_eq :
    {V | V ∈ planes E F ∧ V ≤ sec2P E} = insert E
      (conjSet (sec2F0 A E x) (normalizer (E : Set G) ⊓ normalizer (sec2P E : Set G))) := by
  ext V
  constructor
  · rintro ⟨hV, hVP⟩
    rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hV hVP with rfl | ⟨n, hn, rfl⟩
    · exact Set.mem_insert _ _
    · obtain ⟨hnE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
      exact Set.mem_insert_of_mem _
        ⟨n, ⟨hnE, Sec2.normalizer_le_normalizer_sec2P E hnE⟩, rfl⟩
  · rintro (rfl | ⟨n, hn, rfl⟩)
    · exact ⟨⟨1, Or.inl (rightConjugate_one V).symm⟩, le_sec2P_of_frame hF⟩
    · obtain ⟨h1, h2, -⟩ := rightConjugate_sec2F0_mem h11 hE16 hF hL hodd hx hxS h4 hn.1
      exact ⟨h1, h2⟩

end Plane

theorem card_sec2P_of_frame : Nat.card (sec2P E) = 1024 := by
  obtain ⟨hEP, hEP16, -⟩ := isElemQuot_sec2P h11 hE16 hF hL hodd
  have h := Subgroup.relIndex_mul_card E (sec2P E)
  rw [inf_eq_left.mpr hEP, hEP16, hF.cardE] at h
  omega

theorem card_centralizerMod_of_frame :
    Nat.card (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) = 256 := by
  obtain ⟨hEC, hEC4, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have h := Subgroup.relIndex_mul_card E (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
  rw [inf_eq_left.mpr hEC, hEC4, hF.cardE] at h
  omega

section Count

variable {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)
  (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))

include hx hxS h4

theorem ncard_planes_ne :
    {V | V ∈ planes E F ∧ V ≤ sec2P E ∧ V ≠ E}.ncard = 5 := by
  set 𝒱 := {V | V ∈ planes E F ∧ V ≤ sec2P E ∧ V ≠ E} with h𝒱
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) with hCdef
  have hCeq := centralizerMod_eq_sup_sec2F0 h11 hE16 hF hL hodd hx hxS
  have hCcard := card_centralizerMod_of_frame h11 hE16 hF hL hodd
  have hPcard := card_sec2P_of_frame h11 hE16 hF hL hodd
  have hEP := le_sec2P_of_frame hF
  have hncard : ∀ H : Subgroup G, (H : Set G).ncard = Nat.card H := fun H =>
    (Nat.card_coe_set_eq (H : Set G)).symm
  have hform : ∀ V ∈ 𝒱, ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
      V = rightConjugate (sec2F0 A E x) n ∧ V ⊔ E = rightConjugate C n := by
    rintro V ⟨hV, hVP, hVE⟩
    rcases eq_or_exists_of_mem_planes h11 hE16 hF hL hodd hx hxS hV hVP with h | ⟨n, hn, rfl⟩
    · exact absurd h hVE
    · refine ⟨n, hn, rfl, ?_⟩
      obtain ⟨hnE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
      rw [hCdef, hCeq, rightConjugate_sup', (rightConjugate_eq_self_iff E n).mpr hnE, sup_comm]
  have hVEP : ∀ V ∈ 𝒱, V ⊔ E ≤ sec2P E := fun V hV => sup_le hV.2.1 hEP
  have hcover : (sec2P E : Set G) \ (E : Set G) =
      ⋃ V ∈ 𝒱, ((V ⊔ E : Subgroup G) : Set G) \ (E : Set G) := by
    ext p
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · rintro ⟨hp, hpE⟩
      obtain ⟨n, hn, hnp⟩ := exists_conj_mem_centralizerMod h11 hE16 hF hL hodd hp
      obtain ⟨hnE, -⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
      obtain ⟨h1, h2, h3⟩ :=
        rightConjugate_sec2F0_mem h11 hE16 hF hL hodd hx hxS h4 (inv_mem hnE)
      refine ⟨rightConjugate (sec2F0 A E x) n⁻¹, ⟨h1, h2, h3⟩, ?_, hpE⟩
      have hmem : p ∈ rightConjugate C n⁻¹ := by
        rw [mem_rightConjugate_iff, inv_inv]
        exact hnp
      rw [hCdef, hCeq, rightConjugate_sup',
        (rightConjugate_eq_self_iff E n⁻¹).mpr (inv_mem hnE), sup_comm] at hmem
      exact hmem
    · rintro ⟨V, hV, hpV, hpE⟩
      exact ⟨hVEP V hV hpV, hpE⟩
  have hdisj : 𝒱.PairwiseDisjoint fun V => ((V ⊔ E : Subgroup G) : Set G) \ (E : Set G) := by
    intro V hV W hW hVW
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    rintro p ⟨hpV, hpE⟩ ⟨hpW, -⟩
    obtain ⟨n, hn, hVn, hVC⟩ := hform V hV
    obtain ⟨n', hn', hWn, hWC⟩ := hform W hW
    obtain ⟨hnE, hnR⟩ := mem_normalizer_of_mem_inf_normalizer hF hn
    obtain ⟨hn'E, hn'R⟩ := mem_normalizer_of_mem_inf_normalizer hF hn'
    have hpV' : p ∈ rightConjugate C n := hVC ▸ hpV
    have hpW' : p ∈ rightConjugate C n' := hWC ▸ hpW
    have hCC := rightConjugate_centralizerMod_eq h11 hE16 hF hL hodd hnE hnR hn'E hn'R hpV' hpW'
      hpE
    obtain ⟨hVe, hV64⟩ := isElemAbelian_and_card_of_mem_planes hF hV.1
    obtain ⟨-, hW64⟩ := isElemAbelian_and_card_of_mem_planes hF hW.1
    have hVle : V ≤ rightConjugate C n' := by
      rw [← hCC, ← hVC]
      exact le_sup_left
    rcases le_or_le_of_le_rightConjugate h11 hE16 hF hL hodd hx hxS hn'E hVe hVle with h | h
    · exact hV.2.2 (eq_of_le_of_card_ge h (by rw [hV64, hF.cardE]))
    · rw [← hWn] at h
      exact hVW (eq_of_le_of_card_ge h (by rw [hV64, hW64]))
  have hcard : ∀ V ∈ 𝒱, (((V ⊔ E : Subgroup G) : Set G) \ (E : Set G)).ncard = 192 := by
    intro V hV
    obtain ⟨n, -, -, hVC⟩ := hform V hV
    rw [Set.ncard_sdiff (fun e he => (le_sup_right : E ≤ V ⊔ E) he), hncard, hncard, hVC,
      rightConjugate_card, hCcard, hF.cardE]
  have hPE : ((sec2P E : Set G) \ (E : Set G)).ncard = 960 := by
    rw [Set.ncard_sdiff (fun e he => hEP he), hncard, hncard, hPcard, hF.cardE]
  have h := ncard_sdiff_eq_mul_of_partition (Set.toFinite 𝒱) hcover hdisj hcard
  rw [hPE] at h
  omega

theorem ncard_planes_sec2P : Nat.card {V | V ∈ planes E F ∧ V ≤ sec2P E} = 6 := by
  have h : {V | V ∈ planes E F ∧ V ≤ sec2P E} =
      insert E {V | V ∈ planes E F ∧ V ≤ sec2P E ∧ V ≠ E} := by
    ext V
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hVE : V = E
      · exact Or.inl hVE
      · exact Or.inr ⟨h1, h2, hVE⟩
    · rintro (rfl | ⟨h1, h2, -⟩)
      · exact ⟨⟨1, Or.inl (rightConjugate_one _).symm⟩, le_sec2P_of_frame hF⟩
      · exact ⟨h1, h2⟩
  rw [Nat.card_coe_set_eq, h, Set.ncard_insert_of_notMem (fun h => h.2.2 rfl),
    ncard_planes_ne h11 hE16 hF hL hodd hx hxS h4]

end Count

end Frame

end CFSG.ComponentClassification.AS81
