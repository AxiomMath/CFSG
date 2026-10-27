module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630FiveN
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineA
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630NineB

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankF smallRankR smallRankIsQ8D8 smallRankCenter
  smallRankS)

@[expose] def PConstrainedFivePart : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M : Subgroup G) (P : Sylow 5 G) (z : G) (hz : z ∈ M),
    (P : Subgroup G) ≤ M → z ∈ (P : Subgroup G) →
      (∀ g ∈ (P : Subgroup G), g * z = z * g) →
        CFSG.ABGLocalTools.IsPConstrained 5 ↥M → (⟨z, hz⟩ : ↥M) ∈ CFSG.Op_p'p 5 ↥M

theorem op_five_facts {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    (∀ m ∈ M, ∀ r ∈ (CFSG.Op_p'p 5 ↥M).map M.subtype,
        m * r * m⁻¹ ∈ (CFSG.Op_p'p 5 ↥M).map M.subtype) ∧
    (∀ m ∈ M, ∀ t ∈ (CFSG.pPrimeCore 5 ↥M).map M.subtype,
        m * t * m⁻¹ ∈ (CFSG.pPrimeCore 5 ↥M).map M.subtype) ∧
    Nat.Coprime 5 (Nat.card ((CFSG.pPrimeCore 5 ↥M).map M.subtype)) ∧
    (∀ r ∈ (CFSG.Op_p'p 5 ↥M).map M.subtype,
        ∃ n : ℕ, r ^ (5 ^ n) ∈ (CFSG.pPrimeCore 5 ↥M).map M.subtype) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hOpn : (CFSG.Op_p'p 5 ↥M).Normal := inferInstance
  have hTn : (CFSG.pPrimeCore 5 ↥M).Normal := CFSG.pPrimeCore_normal
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm r hr
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : ↥M) * r' * (⟨m, hm⟩ : ↥M)⁻¹,
      hOpn.conj_mem _ hr' _, rfl⟩
  · intro m hm t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    refine Subgroup.mem_map.mpr ⟨(⟨m, hm⟩ : ↥M) * t' * (⟨m, hm⟩ : ↥M)⁻¹,
      hTn.conj_mem _ ht' _, rfl⟩
  · have hinj : Function.Injective M.subtype := M.subtype_injective
    rw [Subgroup.card_map_of_injective hinj]
    exact CFSG.pPrimeCore_coprime_card
  · intro r hr
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
    have hmem : (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥M) r') ∈
        CFSG.pCore 5 (↥M ⧸ CFSG.pPrimeCore 5 ↥M) := hr'
    have hpg : IsPGroup 5 (CFSG.pCore 5 (↥M ⧸ CFSG.pPrimeCore 5 ↥M)) :=
      CFSG.pCore_isPGroup
    obtain ⟨n, hn⟩ := hpg ⟨_, hmem⟩
    refine ⟨n, Subgroup.mem_map.mpr ⟨r' ^ (5 ^ n), ?_, rfl⟩⟩
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥M) (r' ^ (5 ^ n)) = 1 := by
      rw [map_pow]
      have h2 := congrArg Subtype.val hn
      simpa using h2
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem scalar_commute {E : Type} [Group E] (g : MulAut E) {k : ℕ} (hk : ∀ e : E, g e = e ^ k)
    (h : MulAut E) : g * h = h * g := by
  ext e
  show g (h e) = h (g e)
  rw [hk (h e), hk e, map_pow]

theorem stepNineFPF_of (hI : KFactI2026) (hL613 : L613f3) (hS6 : SigmaSixSectionFact)
    (hPC : PConstrainedFivePart) : StepNineFPF := by
  intro G _ _ p P M x z T₀ f hL
  have hp5 : p = 5 := by
    have h1 := hL.situation.p_ge
    have h2 := hL.lemma628.1
    omega
  subst hp5
  intro g hgN hgp hgC a ha ha1 hfix
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hf5 : Nat.Prime 5 := by norm_num
  have hf : f.Prime := hL.prime
  have hf2 : f ≠ 2 := hL.ne_two
  haveI : Fact f.Prime := ⟨hf⟩
  have hFe : IsElemAbelian f (smallRankF 5 f x) := hL.lemma629.2.2.2.1
  have hFc : Nat.card (smallRankF 5 f x) = f ^ 4 := hL.lemma629.2.2.2.2.1
  have hloc : rankThreeLocalRank f G ≤ 3 := hL.lemma629.2.2.1
  have hRM : smallRankR x z T₀ ≤ pCoreOf 2 M := hL.lemma629.2.1
  have hinvR := hL.lemma629.2.2.2.2.2
  have hQ8 : smallRankIsQ8D8 (smallRankR x z T₀) := hL.lemma628.2.2.1 rfl
  have hFM : smallRankF 5 f x ⊓ M = ⊥ := smallRankF_inf_eq_bot hf hf2 hL.lemma628.2.2.2
  have hFne : smallRankF 5 f x ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFc
    have h4 : 2 ≤ f ^ 4 := le_trans hf.two_le (Nat.le_self_pow (by norm_num) f)
    rw [← hFc] at h4
    norm_num at h4
  have hC_z : centralizer ({z} : Set G) ≤ M := centralizer_singleton_le hL.situation hL.central
  have hzN : z ∈ normalizer ((smallRankF 5 f x : Subgroup G) : Set G) :=
    central_mem_normalizer_smallRankF hf5 hf hL.point.mem hL.central.centralizes
  have hodd : Odd (Nat.card (centralizer ((smallRankF 5 f x : Subgroup G) : Set G))) :=
    odd_card_centralizer_of_rank hf hFe hFc hloc
  haveI : Finite (MulAut (smallRankF 5 f x)) :=
    Finite.of_injective (fun e : MulAut (smallRankF 5 f x) => e.toEquiv)
      (fun a b h => MulEquiv.ext fun y =>
        congrArg (fun e : smallRankF 5 f x ≃ smallRankF 5 f x => e y) h)
  have hzM : z ∈ M := hC_z (mem_centralizer_singleton_iff.mpr rfl)
  have hzP : z ∈ (P : Subgroup G) := hL.central.mem
  have hz5 : z ^ 5 = 1 := hL.central.pow_eq_one
  have hz1 : z ≠ 1 := hL.central.ne_one
  have hx : x ∈ (P : Subgroup G) := hL.point.mem
  have hx5 : orderOf x = 5 := hL.point.order
  set F : Subgroup G := smallRankF 5 f x with hFdef
  set R : Subgroup G := smallRankR x z T₀ with hRdef
  set S : Subgroup G := smallRankS x T₀ with hSdef
  set N : Subgroup G := normalizer (F : Set G) with hNdef
  set C : Subgroup G := centralizer (F : Set G) with hCdef
  set ψ : N →* MulAut F := Subgroup.normalizerMonoidHom F with hψdef
  have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hψapp : ∀ (g : N) (a : F), ((ψ g a : F) : G) = (g : G) * (a : G) * (g : G)⁻¹ :=
    fun g a => rfl
  have hker : ∀ g : N, ψ g = 1 ↔ (g : G) ∈ C := by
    intro g
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro a ha
      have h1 : (g : G) * a * (g : G)⁻¹ = a := by
        have := hψapp g ⟨a, ha⟩
        rw [h, MulAut.one_apply] at this
        exact this.symm
      calc (a : G) * (g : G) = ((g : G) * (a : G) * (g : G)⁻¹) * (g : G) := by rw [h1]
        _ = (g : G) * (a : G) := by group
    · intro hg
      ext a
      rw [hψapp, MulAut.one_apply]
      have hc : (a : G) * g = g * a := (mem_centralizer_iff.mp hg) a a.2
      calc (g : G) * (a : G) * (g : G)⁻¹ = ((a : G) * (g : G)) * (g : G)⁻¹ := by rw [← hc]
        _ = (a : G) := by group
  obtain ⟨hPX, hPcard, hSX, hSO, hSP, hSQ8⟩ :=
    stepApplyI2026_holds G 5 P M x z T₀ f hL hzN
  have hcomm : ∀ a b : F, a * b = b * a := fun a b => hFe.1.is_comm.comm a b
  have hexp : ∀ e : F, e ^ f = 1 := fun e => by
    apply Subtype.ext
    simpa using hFe.2 e e.2
  obtain ⟨hscal, hinv⟩ := hI f F hf hf2 hcomm hexp hFc _ _ _ hPX hPcard hSX hSO hSP hSQ8
  set Γ : Subgroup (MulAut F) := ψ.range with hΓdef
  have hOX : rankThreePrimeCore 2 Γ ≤ Γ := rankThreePrimeCore_le_self 2 Γ
  have hQX : pCoreOf 2 Γ ≤ Γ := pCoreOf_le_self 2 Γ
  have hOn : ((rankThreePrimeCore 2 Γ).subgroupOf Γ).Normal :=
    rankThreePrimeCore_subgroupOf_normal Nat.prime_two Γ
  have hQn : ((pCoreOf 2 Γ).subgroupOf Γ).Normal := pCoreOf_subgroupOf_normal 2 Γ
  have hK0n : (((rankThreePrimeCore 2 Γ) ⊔ pCoreOf 2 Γ).subgroupOf Γ).Normal :=
    sup_subgroupOf_normal Γ _ _ hOX hQX hOn hQn
  set K0 : Subgroup Γ := ((rankThreePrimeCore 2 Γ) ⊔ pCoreOf 2 Γ).subgroupOf Γ with hK0def
  haveI hK0 : K0.Normal := hK0n
  set Φ : N →* Γ ⧸ K0 := (QuotientGroup.mk' K0).comp ψ.rangeRestrict with hΦdef
  have hΦsurj : Function.Surjective Φ :=
    (QuotientGroup.mk'_surjective K0).comp ψ.rangeRestrict_surjective
  have hΦapp : ∀ n : N, Φ n = (QuotientGroup.mk' K0) (ψ.rangeRestrict n) := fun n => rfl
  have hsyl0 : ∀ D : Subgroup G, D ≤ C → IsPGroup 5 D → Nat.card D ≤ 5 := by
    have hB : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankPlane 5 (P : Subgroup G) x z :=
      CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.plane_of_central hL.situation hL.point hL.central
    have hxF : ∀ Q : Subgroup G, IsPGroup 5 Q → x ∉ (frattini ↥Q).map Q.subtype :=
      fun Q hQ => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.x_not_mem_frattini
        hL.situation hL.point hQ
    have hxC : x ∈ C := mem_centralizer_iff.mpr
      (fun a ha => mem_centralizer_singleton_iff.mp (smallRankF_le_centralizer (p := 5) hf ha))
    have hzNC : z ∈ normalizer (C : Set G) := normalizer_centralizer_of_mem hzN
    have hzC : z ∉ C := by
      intro hzC
      obtain ⟨a', ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
      have ha'G : (a' : G) ≠ 1 := fun h => ha' (Subtype.ext h)
      exact ha'G (eq_one_of_mem_smallRankF_comm hC_z hFM a'.2 (mem_centralizer_iff.mp hzC a' a'.2))
    intro D hD hDp
    exact card_le_five_of_centralizer hB C
      (mem_centralizer_iff.mpr (fun a ha => mem_centralizer_singleton_iff.mp
        (smallRankF_le_centralizer (p := 5) hf ha))) hzNC hzC hz5 hz1 hxF hD hDp
  have hzS : zpowers z ≤ normalizer ((S : Subgroup G) : Set G) :=
    zpowers_le_normalizer_smallRankS hL.sylowTwo hL.central hx
  have hR_le_S : R ≤ S := smallRankR_le_smallRankS hzS
  have hR_le_Cx : R ≤ centralizer ({x} : Set G) := hR_le_S.trans inf_le_right
  have hR_le_N : R ≤ N := fun r hr => mem_normalizer_smallRankF hf5 hf (hR_le_Cx hr)
  have hzR : z ∈ normalizer (R : Set G) := zpowers_le_normalizer_smallRankR (mem_zpowers z)
  have hRp : IsPGroup 2 R := (pCoreOf_isPGroup 2 M).to_le hRM
  have hRC : R ⊓ C = ⊥ :=
    inf_centralizer_eq_bot_of_inverts hf hf2 (fun e he => hFe.2 e he) hFne hRp hR_le_N hinvR
  obtain ⟨c, hcR, hc1, hc2, hcc⟩ := exists_central_involution_of_Q8D8 hQ8
  have hcZ : c ∈ smallRankCenter R := by
    rw [smallRankCenter, Subgroup.mem_inf]
    exact ⟨hcR, mem_centralizer_iff.mpr fun r hr => (hcc r hr).symm⟩
  have hcinv : ∀ a ∈ F, c * a * c⁻¹ = a⁻¹ := hinvR c hcZ hc1
  have hcC : c ∉ C := by
    intro hc
    have hmem : c ∈ R ⊓ C := ⟨hcR, hc⟩
    rw [hRC, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  have hzc : z * c * z⁻¹ = c := conj_fixes_central_involution hzR hcR hc1 hc2 hcc hinvR hRC
  have hzc' : z * c = c * z := by
    calc z * c = z * c * z⁻¹ * z := by group
      _ = c * z := by rw [hzc]
  have hxc : x * c = c * x := (mem_centralizer_singleton_iff.mp (hR_le_Cx hcR)).symm
  have hcM : c ∈ M := pCoreOf_le_self 2 M (hRM hcR)
  have hC_c : centralizer ({c} : Set G) ≤ M :=
    centralizer_singleton_le_of_involution hL.prop614 hc2 hc1 hcM hxc hzc'
  have hxC : x ∈ C := mem_centralizer_iff.mpr
    (fun a ha => mem_centralizer_singleton_iff.mp (smallRankF_le_centralizer (p := 5) hf ha))
  have hcov := covering_of_involution (F := F) (x := x) (c := c) hodd hc2 hc1
    (hR_le_N hcR) hcC hcinv hxC hxc hx5 hsyl0
  have hPhiC : ∀ (d : G) (hdN : d ∈ N), d ∈ C → Φ ⟨d, hdN⟩ = 1 := by
    intro d hdN hdC
    have h2 : ψ.rangeRestrict ⟨d, hdN⟩ = 1 := Subtype.ext ((hker ⟨d, hdN⟩).mpr hdC)
    rw [hΦapp, h2, map_one]
  have hcovN : ∀ n : N, ∃ e : N, ψ n = ψ e ∧ (e : G) ∈ centralizer ({c} : Set G) ∧
      (e : G) ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    intro n
    obtain ⟨d, hd, e, heN, hnde, hec, henorm⟩ := hcov n n.2
    refine ⟨⟨e, heN⟩, ?_, mem_centralizer_singleton_iff.mpr hec, henorm⟩
    have hdN : d ∈ N := hC_le_N hd
    have h1 : ψ ⟨d, hdN⟩ = 1 := (hker ⟨d, hdN⟩).mpr hd
    have h2 : ψ n = ψ ⟨d, hdN⟩ * ψ ⟨e, heN⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      simpa using hnde
    rw [h2, h1, one_mul]
  set X1 : Subgroup G := M ⊓ centralizer ({x} : Set G) with hX1def
  have hX1N : X1 ≤ N := fun y hy => mem_normalizer_smallRankF hf5 hf hy.2
  set L : Subgroup (Γ ⧸ K0) := (X1.subgroupOf N).map Φ with hLdef
  have hLn : L.Normal := by
    refine ⟨fun ℓ hℓ q => ?_⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hℓ
    obtain ⟨n, rfl⟩ := hΦsurj q
    obtain ⟨e, hψe, hec, henorm⟩ := hcovN n
    have hΦne : Φ n = Φ e := by
      have hrr : ψ.rangeRestrict n = ψ.rangeRestrict e := Subtype.ext hψe
      rw [hΦapp, hΦapp, hrr]
    rw [hΦne]
    have ht' : (t : G) ∈ X1 := Subgroup.mem_subgroupOf.mp ht
    have heM : (e : G) ∈ M := hC_c hec
    refine Subgroup.mem_map.mpr ⟨e * t * e⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨M.mul_mem (M.mul_mem heM ht'.1) (M.inv_mem heM),
      conj_mem_centralizer_of_normalizer_zpowers hx5 henorm ht'.2⟩
  have hLpow : ∀ q : Γ ⧸ K0, q ^ 4 ∈ L := by
    intro q
    obtain ⟨n, rfl⟩ := hΦsurj q
    obtain ⟨e, hψe, hec, henorm⟩ := hcovN n
    have hΦne : Φ n = Φ e := by
      have hrr : ψ.rangeRestrict n = ψ.rangeRestrict e := Subtype.ext hψe
      rw [hΦapp, hΦapp, hrr]
    rw [hΦne, ← map_pow]
    refine Subgroup.mem_map.mpr ⟨e ^ 4, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact Subgroup.mem_inf.mpr ⟨M.pow_mem (hC_c hec) 4, pow_four_mem_centralizer hx5 henorm⟩
  haveI hLn' : L.Normal := hLn
  have hψg1 : ψ ⟨g, hgN⟩ ≠ 1 := fun h => hgC ((hker ⟨g, hgN⟩).mp h)
  have hψg3 : ψ ⟨g, hgN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact (hker _).mpr (by simpa using hgp)
  have hΦg3 : Φ ⟨g, hgN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h1 : (⟨g, hgN⟩ : N) ^ 3 = ⟨g ^ 3, N.pow_mem hgN 3⟩ := Subtype.ext (by simp)
    rw [h1]
    exact hPhiC _ _ hgp
  have hΦz5 : Φ ⟨z, hzN⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have h1 : (⟨z, hzN⟩ : N) ^ 5 = 1 := Subtype.ext (by simpa using hz5)
    rw [h1, map_one]
  have hOodd : ¬ 2 ∣ Nat.card (rankThreePrimeCore 2 Γ) := by
    have h2c := coprime_rankThreePrimeCore' Nat.prime_two Γ
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h2c
    exact h2c
  have hΦz : Φ ⟨z, hzN⟩ ≠ 1 := by
    intro h1
    have hψz5 : orderOf (ψ ⟨z, hzN⟩) = 5 := by
      have h := hPcard
      rw [Nat.card_zpowers] at h
      exact h
    have hz_mem : ψ ⟨z, hzN⟩ ∈ rankThreePrimeCore 2 Γ ⊔ pCoreOf 2 Γ := by
      have h2 : ψ.rangeRestrict ⟨z, hzN⟩ ∈ K0 :=
        (QuotientGroup.eq_one_iff _).mp (by rw [hΦapp] at h1; exact h1)
      exact Subgroup.mem_subgroupOf.mp h2
    have hodd5 : Odd (orderOf (ψ ⟨z, hzN⟩)) := by
      rw [hψz5]
      decide
    have hwX : ψ ⟨z, hzN⟩ ∈ Γ := MonoidHom.mem_range.mpr ⟨⟨z, hzN⟩, rfl⟩
    have hO : ψ ⟨z, hzN⟩ ∈ rankThreePrimeCore 2 Γ :=
      mem_of_odd_of_mem_sup Γ _ _ hOX hQX hOn hQn hOodd (pCoreOf_isPGroup 2 Γ) hwX hz_mem hodd5
    obtain ⟨k, hk⟩ := hscal _ hO
    have hbot : ⁅(((R.subgroupOf N).map ψ) : Subgroup (MulAut F)),
        zpowers (ψ ⟨z, hzN⟩)⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine Subgroup.commutator_le.mpr ?_
      intro h1' hh1 h2' hh2
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hh2
      have hc : Commute (ψ ⟨z, hzN⟩) h1' := scalar_commute _ hk h1'
      have hc' : Commute h1' ((ψ ⟨z, hzN⟩) ^ j) := hc.symm.zpow_right j
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc'.eq
    have hS'bot : (R.subgroupOf N).map ψ = ⊥ := by
      have h := hSP
      rw [hbot] at h
      exact h.symm
    obtain ⟨A, B, ⟨eA⟩, -, -, hsup, -⟩ := hSQ8
    have hA : Nat.card A = 8 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hAle : A ≤ (R.subgroupOf N).map ψ := by
      rw [← hsup]
      exact le_sup_left
    rw [hS'bot] at hAle
    have hAbot : A = ⊥ := eq_bot_iff.mpr hAle
    rw [hAbot, Subgroup.card_bot] at hA
    norm_num at hA
  by_cases hgK : Φ ⟨g, hgN⟩ = 1
  ·
    have hwX : ψ ⟨g, hgN⟩ ∈ Γ := MonoidHom.mem_range.mpr ⟨⟨g, hgN⟩, rfl⟩
    have hK : ψ.rangeRestrict ⟨g, hgN⟩ ∈ K0 :=
      (QuotientGroup.eq_one_iff _).mp (by rw [hΦapp] at hgK; exact hgK)
    have hgmem : ψ ⟨g, hgN⟩ ∈ rankThreePrimeCore 2 Γ ⊔ pCoreOf 2 Γ :=
      Subgroup.mem_subgroupOf.mp hK
    have hodd3 : Odd (orderOf (ψ ⟨g, hgN⟩)) := by
      rw [orderOf_eq_prime hψg3 hψg1]
      decide
    have hO3 : ψ ⟨g, hgN⟩ ∈ rankThreePrimeCore 2 Γ :=
      mem_of_odd_of_mem_sup Γ _ _ hOX hQX hOn hQn hOodd (pCoreOf_isPGroup 2 Γ) hwX hgmem hodd3
    obtain ⟨k, hk⟩ := hscal _ hO3
    have haF : (⟨a, ha⟩ : F) ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
    have hfixF : ψ ⟨g, hgN⟩ ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext hfix
    exact hψg1 (scalar_eq_one hf hexp _ hk haF hfixF)
  ·
    have hord3 : orderOf (Φ ⟨g, hgN⟩) = 3 := orderOf_eq_prime hΦg3 hgK
    have hord5 : orderOf (Φ ⟨z, hzN⟩) = 5 := orderOf_eq_prime hΦz5 hΦz
    have h15 : 15 ∣ Nat.card (Γ ⧸ K0) := by
      have h3 : 3 ∣ Nat.card (Γ ⧸ K0) := by
        have := orderOf_dvd_natCard (Φ ⟨g, hgN⟩)
        rwa [hord3] at this
      have h5 : 5 ∣ Nat.card (Γ ⧸ K0) := by
        have := orderOf_dvd_natCard (Φ ⟨z, hzN⟩)
        rwa [hord5] at this
      have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 5) h3 h5
      norm_num at this
      exact this
    obtain ⟨S6, hS6n, hS6idx, hS6simple, h2S, h15S, hnab⟩ := hS6 (Γ ⧸ K0) (hinv hK0n) h15
    haveI := hS6n
    haveI := hS6simple
    have h3S6 : 3 ∣ Nat.card S6 := (by norm_num : (3 : ℕ) ∣ 15).trans h15S
    have h5S6 : 5 ∣ Nat.card S6 := (by norm_num : (5 : ℕ) ∣ 15).trans h15S
    have hSL : S6 ≤ L := simple_le_of_pow_four_mem h3S6 hLpow
    obtain ⟨H6, K6, hH6X1, hsec6, hrel6⟩ :=
      sectionOfPowerCover N Φ hΦsurj X1 hX1N S6 hnab h3S6 hLn hLpow
    have hzX : z ∈ X1 := ⟨hzM, mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hL.central.centralizes) x hx).symm⟩
    have hPleM : (P : Subgroup G) ≤ M := by
      intro g' hg'
      apply hC_z
      exact mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hL.central.centralizes) g' hg')
    have hNPC : ¬ CFSG.ABGLocalTools.IsPConstrained 5 ↥M := by
      intro hPCc
      have hzOp := hPC G M P z hzM hPleM hzP
        (fun g' hg' => (mem_centralizer_iff.mp hL.central.centralizes) g' hg') hPCc
      obtain ⟨hRn, hTn, hTcard, hRT⟩ := op_five_facts M
      have hzR : z ∈ (CFSG.Op_p'p 5 ↥M).map M.subtype :=
        Subgroup.mem_map.mpr ⟨⟨z, hzM⟩, hzOp, rfl⟩
      exact false_of_mem_fivePart N hX1N Φ hΦsurj S6 hnab h2S h5S6 hS6idx hSL hzX hΦz hz5
        ((CFSG.Op_p'p 5 ↥M).map M.subtype) ((CFSG.pPrimeCore 5 ↥M).map M.subtype) hRn hTn
        (Subgroup.map_subtype_le _) hTcard hRT hzR
    have hGLB : GLBStronglyEmbedded 3 M :=
      hL613 G 5 P M x z hL.situation hL.point hL.central hNPC H6 K6 hH6X1 hsec6
        (by rw [hrel6]; exact h5S6) (by rw [hrel6]; exact h3S6)
    obtain ⟨e, hψe, hec, -⟩ := hcovN ⟨g, hgN⟩
    have he3 : 3 ∣ orderOf (e : G) := by
      have h1 : orderOf (ψ e) ∣ orderOf e := orderOf_map_dvd ψ e
      have h2 : orderOf e = orderOf (e : G) := (Subgroup.orderOf_coe e).symm
      have h3 : orderOf (ψ e) = 3 := by
        rw [← hψe]
        exact orderOf_eq_prime hψg3 hψg1
      rw [h3, h2] at h1
      exact h1
    have heM : (e : G) ∈ M := hC_c hec
    have hCe : centralizer ({(e : G)} : Set G) ≤ M := centralizer_le_of_three_dvd hGLB heM he3
    have hae : (e : G) * a * (e : G)⁻¹ = a := by
      rw [← hψapp e ⟨a, ha⟩, ← hψe, hψapp]
      exact hfix
    have hea : (e : G) * a = a * (e : G) := by
      calc (e : G) * a = ((e : G) * a * (e : G)⁻¹) * (e : G) := by group
        _ = a * (e : G) := by rw [hae]
    have hcentA : a ∈ centralizer ({(e : G)} : Set G) := mem_centralizer_singleton_iff.mpr hea.symm
    have haM : a ∈ M := hCe hcentA
    have haF : a ∈ F ⊓ M := ⟨ha, haM⟩
    rw [hFM, Subgroup.mem_bot] at haF
    exact ha1 haF

theorem s62L630Iii_of_kfacts_full (hI : KFactI2026) (hGAP : KFactAutQ8D8Five) (hL613 : L613f3)
    (hS6 : SigmaSixSectionFact) (hPC : PConstrainedFivePart) : S62L630Iii :=
  s62L630Iii_of_kfacts hI (stepFiveFPF_of hGAP) (stepNineFPF_of hI hL613 hS6 hPC)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
