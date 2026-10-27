module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Steps
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
import CFSG.LocalAnalysis.RankThreeUC.GN15LayerCoprime
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PCoreQuotient
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

section Defs

variable {X : Type} [Group X] {T : Subgroup X}

@[expose] noncomputable def gnKThree (T : Subgroup X) : Subgroup X :=
  (Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) ⊔
    CFSG.pPrimeCore 3 (X ⧸ gnC T) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T))).comap (toStar T)

@[expose] noncomputable def gnPThree (T : Subgroup X) : Subgroup X :=
  (CFSG.pCore 3 (X ⧸ gnC T)).comap (toStar T)

private theorem normal_rankThreeLayer_top' {G : Type} [Group G] :
    (rankThreeLayer (⊤ : Subgroup G)).Normal := by
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.le_normalizer_rankThreeLayer (⊤ : Subgroup G)
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)

instance gnKThree_normal : (gnKThree T).Normal := by
  haveI : (rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T))).Normal := normal_rankThreeLayer_top'
  unfold gnKThree
  exact Subgroup.Normal.comap (Subgroup.normal_centralizer) _

instance gnPThree_normal : (gnPThree T).Normal := by
  unfold gnPThree
  exact Subgroup.Normal.comap inferInstance _

theorem gnKThree_le_gnHPre : gnKThree T ≤ gnHPre T :=
  Subgroup.comap_mono (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 le_sup_left))

theorem gnC_le_gnKThree : gnC T ≤ gnKThree T := fun c hc => by
  show toStar T c ∈ Subgroup.centralizer _
  rw [show toStar T c = 1 from (QuotientGroup.eq_one_iff _).2 hc]
  exact Subgroup.one_mem _

end Defs

section FIT

variable {G : Type} [Group G] [Finite G]

private theorem layer_eq_rankThreeLayer_top' (G : Type) [Group G] :
    CFSG.layer G = rankThreeLayer (⊤ : Subgroup G) := by
  rw [CFSG.layer.eq_sSup]
  unfold rankThreeLayer
  congr 1
  ext L
  exact CFSG.isComponent_iff_open L

private theorem pCore_le_pPrimeCore_three {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3) :
    CFSG.pCore q G ≤ CFSG.pPrimeCore 3 G := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore q G)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := q) (G := G))
    rw [hn]
    exact ((Nat.coprime_primes Nat.prime_three hq).2 (Ne.symm hq3)).pow_right n
  exact le_sSup ⟨CFSG.pCore_normal, hcop⟩

private theorem pCore_three_commute_pPrimeCore {a b : G} (ha : a ∈ CFSG.pCore 3 G)
    (hb : b ∈ CFSG.pPrimeCore 3 G) : a * b = b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzO : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pPrimeCore 3 G :=
    mul_mem (CFSG.pPrimeCore_normal.conj_mem b hb a) (inv_mem hb)
  have hzF : a * b * a⁻¹ * b⁻¹ ∈ CFSG.pCore 3 G := by
    have : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
    rw [this]
    exact mul_mem ha (CFSG.pCore_normal.conj_mem a⁻¹ (inv_mem ha) b)
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 3) (G := G)) ⟨_, hzF⟩
  have hz1 : (a * b * a⁻¹ * b⁻¹) ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hord1 : orderOf (a * b * a⁻¹ * b⁻¹) ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hz1
  have hord2 : orderOf (a * b * a⁻¹ * b⁻¹) ∣ Nat.card (CFSG.pPrimeCore 3 G) := by
    simpa using Subgroup.orderOf_dvd_natCard _ hzO
  have hcop : Nat.Coprime (3 ^ n) (Nat.card (CFSG.pPrimeCore 3 G)) :=
    CFSG.pPrimeCore_coprime_card.pow_left n
  have h1 : orderOf (a * b * a⁻¹ * b⁻¹) = 1 :=
    (Nat.Coprime.coprime_dvd_left hord1 hcop).eq_one_of_dvd hord2
  have hz : a * b * a⁻¹ * b⁻¹ = 1 := orderOf_eq_one_iff.mp h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [hz, one_mul]

private theorem mul_comm_of_mem_sup {A B : Subgroup G} {z : G} (hA : ∀ a ∈ A, a * z = z * a)
    (hB : ∀ b ∈ B, b * z = z * b) : ∀ g ∈ A ⊔ B, g * z = z * g := fun g hg => by
  have h : A ⊔ B ≤ Subgroup.centralizer ({z} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB b hb))
  exact Subgroup.mem_centralizer_singleton_iff.1 (h hg)

private theorem generalizedFitting_le_three :
    CFSG.generalizedFitting G ≤
      rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G ⊔ CFSG.pCore 3 G := by
  rw [CFSG.generalizedFitting.eq_sup, layer_eq_rankThreeLayer_top']
  refine sup_le ?_ (le_sup_of_le_left le_sup_left)
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun q => ?_
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases h3 : q.1.1 = 3
  · rw [h3]
    exact le_sup_right
  · exact (pCore_le_pPrimeCore_three hq h3).trans (le_sup_of_le_left le_sup_right)

private theorem centralizer_le_three :
    Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G ⊔
        CFSG.pCore 3 G : Subgroup G) : Set G) ≤
      rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G ⊔ CFSG.pCore 3 G :=
  (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 generalizedFitting_le_three)).trans
    ((CFSG.centralizer_generalizedFitting_le G).trans generalizedFitting_le_three)

private theorem commute_of_centralizer_three {z z' : G}
    (hz : z ∈ Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G ⊔
      CFSG.pCore 3 G : Subgroup G) : Set G))
    (hz' : z' ∈ Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G ⊔
      CFSG.pCore 3 G : Subgroup G) : Set G)) : z * z' = z' * z :=
  Subgroup.mem_centralizer_iff.1 hz' z (centralizer_le_three hz)

private theorem mem_centralizer_of_mem_pCore_three {p : G} (hp : p ∈ CFSG.pCore 3 G) :
    p ∈ Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup G) ⊔ CFSG.pPrimeCore 3 G :
      Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : CFSG.fittingSubgroup G ≤
      Subgroup.centralizer ((CFSG.layer G : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute
  refine Subgroup.mem_centralizer_iff.2 ?_
  exact mul_comm_of_mem_sup (fun e he => by
      rw [← layer_eq_rankThreeLayer_top'] at he
      exact Subgroup.mem_centralizer_iff.1 (hcomm (CFSG.pCore_le_fitting G 3 hp)) e he)
    (fun w hw => (pCore_three_commute_pPrimeCore hp hw).symm)

end FIT

section K3

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem gnPThree_le_gnKThree : gnPThree T ≤ gnKThree T := fun p hp =>
  mem_centralizer_of_mem_pCore_three hp

theorem commute_toStar_of_mem_gnKThree {x y : X} (hx : x ∈ gnKThree T) (hy : y ∈ gnKThree T)
    (hxP : ∀ p ∈ CFSG.pCore 3 (X ⧸ gnC T), p * toStar T x = toStar T x * p)
    (hyP : ∀ p ∈ CFSG.pCore 3 (X ⧸ gnC T), p * toStar T y = toStar T y * p) :
    toStar T x * toStar T y = toStar T y * toStar T x := by
  have key : ∀ z : X ⧸ gnC T, z ∈ Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) ⊔
      CFSG.pPrimeCore 3 (X ⧸ gnC T) : Subgroup (X ⧸ gnC T)) : Set (X ⧸ gnC T)) →
      (∀ p ∈ CFSG.pCore 3 (X ⧸ gnC T), p * z = z * p) →
      z ∈ Subgroup.centralizer ((rankThreeLayer (⊤ : Subgroup (X ⧸ gnC T)) ⊔
        CFSG.pPrimeCore 3 (X ⧸ gnC T) ⊔ CFSG.pCore 3 (X ⧸ gnC T) : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) := fun z hz hzP =>
    Subgroup.mem_centralizer_iff.2 (mul_comm_of_mem_sup (Subgroup.mem_centralizer_iff.1 hz) hzP)
  exact commute_of_centralizer_three (key _ hx hxP) (key _ hy hyP)

end K3

section Faith

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem inf_centralizer_conjClosure_le (hX : GNSetting X T) {K : Subgroup X} (hK : K.Normal)
    (hKH : K ≤ gnHPre T) :
    K ⊓ Subgroup.centralizer
      ((conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Subgroup X) : Set X) ≤ gnC T := by
  classical
  set W : Subgroup X := conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) with hW
  set Y : Subgroup X := K ⊓ Subgroup.centralizer (W : Set X) with hY
  have hV := isElemAbelian_gnV T hX
  have hMN : K ⊔ T ≤ Subgroup.normalizer (W : Set X) := le_normalizer_conjClosure _ _
  have hnormY : K ⊔ T ≤ Subgroup.normalizer (Y : Set X) := by
    intro g hg
    have h1 : g ∈ Subgroup.normalizer (K : Set X) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hK]; exact Subgroup.mem_top g
    have h2 := CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup W (hMN hg)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hYsub : Y.IsSubnormal := by
    refine Subgroup.IsSubnormal.step Y K inf_le_left hK.isSubnormal ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact le_sup_left.trans hnormY
  set Yb : Subgroup (X ⧸ gnC T) := Y.map (toStar T) with hYb
  have hYbsub : Yb.IsSubnormal := hYsub.map (QuotientGroup.mk'_surjective (gnC T))
  by_contra hcon
  have hYbne : Yb ≠ ⊥ := by
    intro hbot
    apply hcon
    intro y hy
    have : toStar T y ∈ Yb := Subgroup.mem_map_of_mem _ hy
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff _).1 this
  have hC : Yb ≤ Subgroup.centralizer
      ((CFSG.layer (X ⧸ gnC T) : Subgroup (X ⧸ gnC T)) : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [layer_eq_rankThreeLayer_top']
    exact hKH hy.1
  have hO2 : pCoreOf 2 Yb = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal (A3.subnormal_top_iff.mpr hYbsub),
      B6.pCoreOf_top, CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.pCore_two_gnQuot hX,
      inf_bot_eq]
  obtain ⟨p, hp, hp2, hne⟩ := exists_odd_pCoreOf_ne_bot hYbne hYbsub hC hO2
  haveI : Fact p.Prime := ⟨hp⟩
  set Qb : Subgroup (X ⧸ gnC T) := pCoreOf p Yb with hQb
  have hQp : IsPGroup p Qb := CFSG.LieType.BorelTits.pCoreOf_isPGroup p Yb
  have hQY : Qb ≤ Yb := CFSG.LieType.BorelTits.pCoreOf_le p Yb
  have hTQ : ∀ t ∈ T, ∀ q ∈ Qb, toStar T t * q * (toStar T t)⁻¹ ∈ Qb := by
    intro t ht q hq
    have h1 : toStar T t ∈ Subgroup.normalizer (Yb : Set (X ⧸ gnC T)) :=
      Subgroup.le_normalizer_map (toStar T) ⟨t, hnormY (Subgroup.mem_sup_right ht), rfl⟩
    have h2 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p Yb h1
    exact (Subgroup.mem_normalizer_iff.1 h2 q).1 hq
  set ι := gnIota hV with hι
  have hP : Odd (Nat.card (Qb.map ι)) := by
    rw [Subgroup.card_map_of_injective (gnIota_injective hV)]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hT2 : IsPGroup 2 ((T.map (toStar T)).map ι) :=
    (hX.sylow.2.1.map (toStar T)).map ι
  have hn : ∀ t ∈ (T.map (toStar T)).map ι, ∀ x ∈ Qb.map ι, t * x * t⁻¹ ∈ Qb.map ι := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨_, hTQ t ht q hq, by simp⟩
  have hfix : ∀ w : IntMod (gnV T) hV, (∀ t ∈ (T.map (toStar T)).map ι, t w = w) →
      ∀ x ∈ Qb.map ι, x w = w := by
    intro w hw x hx
    obtain ⟨q, hq, rfl⟩ := hx
    obtain ⟨y, hy, hqy⟩ := hQY hq
    have hwT : ∀ t ∈ T, t * w.val * t⁻¹ = w.val := by
      intro t ht
      have h1 := congrArg IntMod.val (hw (ι (toStar T t)) ⟨_, ⟨t, ht, rfl⟩, rfl⟩)
      have h2 : ι (toStar T t) = gnConj hV t := rfl
      rw [h2, gnConj_apply_val] at h1
      exact h1
    have hwZ : w.val ∈ quasithinOmegaOneCenter T := by
      refine Subgroup.subset_closure ⟨⟨gnV_le T hX w.val_mem, ?_⟩, ?_⟩
      · refine Subgroup.mem_centralizer_iff.2 fun t ht => ?_
        have := hwT t ht
        calc t * w.val = (t * w.val * t⁻¹) * t := by group
          _ = w.val * t := by rw [this]
      · simpa [pow_two] using congrArg IntMod.val (IntMod.sq_eq_one w)
    have hwW : w.val ∈ W := le_conjClosure _ _ hwZ
    refine IntMod.val_injective ?_
    have h2 : ι q = gnConj hV y := by rw [← hqy]; rfl
    rw [h2, gnConj_apply_val]
    have h := Subgroup.mem_centralizer_iff.1 hy.2 w.val hwW
    rw [← h, mul_inv_cancel_right]
  have htriv := eq_one_of_odd_normalized_fixed (fun w => IntMod.sq_eq_one w) hP hT2 hn hfix
  apply hne
  rw [eq_bot_iff]
  intro q hq
  have h1 : ι q = 1 := by
    ext w
    exact htriv (ι q) ⟨q, hq, rfl⟩ w
  exact (Subgroup.mem_bot).2 ((injective_iff_map_eq_one ι).1 (gnIota_injective hV) q h1)

end Faith

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
