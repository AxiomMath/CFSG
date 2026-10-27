module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenOtherCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreeSolv
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

@[expose] def TenThreeThree.KFactParabolicIrredCentralNA : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P B N : Subgroup A) (p : ℕ), p.Prime → p ≠ 2 →
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P →
    (∃ x ∈ P, ∃ y ∈ P, x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 P) →
    IsPGroup p ↥B → ¬ IsCyclic ↥B → B ≤ Subgroup.normalizer (Y : Set A) →
    B ≤ Subgroup.normalizer (P : Set A) →
    (∀ b ∈ B, ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) →
    N ≤ Subgroup.normalizer (Y : Set A) → N ≤ Subgroup.normalizer (P : Set A) →
    N ≤ Subgroup.normalizer (B : Set A) →
    (∀ V : Subgroup A, V ≤ B → ¬ V ≤ (frattini ↥B).map B.subtype →
      N ≤ Subgroup.normalizer (V : Set A) → V = B) →
    (∀ b ∈ B, ∀ y ∈ Y, b * y = y * b) ∨ 4 ≤ Open.pRank p Y

variable {G : Type} [Group G] [Finite G]

variable (G) in
@[expose] def AGL81TenThreeThreeCasesCfg : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    (L.subgroupOf M).Normal → ∀ b ∈ H ⊓ M, Odd (orderOf b) →
      (∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L)) →
      (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
        (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
          IsParabolicTwo (barM M L) (barM M (H ⊓ L)))

private theorem not_isCyclic_of_two_le_pRank {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {A : Subgroup X} (hA : 2 ≤ Open.pRank p A) : ¬ IsCyclic ↥A := by
  intro hcyc
  obtain ⟨E, hEA, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hA
  haveI : IsCyclic (E.subgroupOf A) := inferInstance
  haveI : IsCyclic ↥E :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hEA).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hEA).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥E)
  have h1 : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : g ^ p = 1 := Subtype.ext (hE.2 (g : X) g.2)
  have h3 : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one h2)
  rw [h1, hEc] at h3
  nlinarith [hp.two_le]

theorem commutator_le_pCoreOf_of_forall {M L A : Subgroup G} (hLM : L ≤ M) (hAM : A ≤ M)
    (hMn : M ≤ Subgroup.normalizer (L : Set G))
    (hc : ∀ b ∈ A, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : ⁅A, L⁆ ≤ pCoreOf 2 L := by
  rw [Subgroup.commutator_le]
  intro a ha l hl
  rw [commutatorElement_def]
  refine inf_pCoreOf_le hLM ⟨?_, hc a ha l hl⟩
  have hal : a * l * a⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hMn (hAM ha)) l).mp hl
  exact L.mul_mem hal (L.inv_mem hl)

theorem barHom_injective_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M A : Subgroup G}
    (hAM : A ≤ M) (hA : IsPGroup p A) : Function.Injective (barHom M A hAM) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : (x : G) ∈ pCoreOf 2 M := mem_ker_barHom.mp hx
  obtain ⟨k, hk⟩ := hA x
  obtain ⟨j, hj⟩ := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M ⟨(x : G), hmem⟩
  have h1 : orderOf (x : G) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (x : G) ∣ 2 ^ j :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hj)
  have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h3 : orderOf (x : G) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact Subtype.ext (orderOf_eq_one_iff.mp h3)

theorem pRank_barM_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Subgroup G}
    (Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Open.pRank p Y ≤ Open.pRank p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)).exists_card_eq
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  calc Open.pRank p Y ≤ Open.pRank p (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        CFSG.SectionRank.pRank_mono hp.one_lt le_top
    _ = Open.pRank p (⊤ : Subgroup ↥M) := CFSG.SectionRank.pRank_quotient_eq _ hN
    _ = Open.pRank p M := (CFSG.SectionRank.pRank_eq_pRank_top_subgroup M).symm

theorem irred_transfer_barM {M H A : Subgroup G} (hAM : A ≤ M)
    (hNA : H ⊓ Subgroup.normalizer (A : Set G) ≤ M) (e : ↥A ≃* ↥(barM M A))
    (he : ∀ a : ↥A, ((e a : ↥(barM M A)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(a : G), hAM a.2⟩)
    (hirr : ∀ V : Subgroup G, V ≤ A → ¬ V ≤ (frattini ↥A).map A.subtype →
      H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = A)
    (V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) (hVB : V ≤ barM M A)
    (hV : ¬ V ≤ (frattini ↥(barM M A)).map (barM M A).subtype)
    (hVn : barM M (H ⊓ Subgroup.normalizer (A : Set G)) ≤ Subgroup.normalizer (V : Set _)) :
    V = barM M A := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hπ
  let V' : Subgroup G := ((V.comap π).map M.subtype) ⊓ A
  have hmemV' : ∀ (a : G) (ha : a ∈ A), a ∈ V' ↔ π ⟨a, hAM ha⟩ ∈ V := by
    intro a ha
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, -⟩
      exact hy
    · intro h
      exact ⟨⟨⟨a, hAM ha⟩, h, rfl⟩, ha⟩
  have hV'A : V' ≤ A := inf_le_right
  have hV'1 : ¬ V' ≤ (frattini ↥A).map A.subtype := by
    intro hle
    apply hV
    intro v hv
    obtain ⟨y, hy, rfl⟩ := hVB hv
    have hyA : (y : G) ∈ A := hy
    have hyV' : (y : G) ∈ V' := (hmemV' _ hyA).mpr hv
    obtain ⟨s, hsΦ, hsy⟩ := hle hyV'
    refine ⟨e s, (OtherCfg.mem_frattini_iff_of_equiv e s).mpr hsΦ, ?_⟩
    show ((e s : ↥(barM M A)) : ↥M ⧸ CFSG.pCore 2 ↥M) = π y
    rw [he]
    congr 1
    exact Subtype.ext hsy
  have hV'n : H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V' : Set G) := by
    intro g hg
    have hgM : g ∈ M := hNA hg
    have hgb : π ⟨g, hgM⟩ ∈ Subgroup.normalizer (V : Set _) :=
      hVn ⟨⟨g, hgM⟩, hg, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    by_cases hxA : x ∈ A
    · have hgxA : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg.2 x).mp hxA
      rw [hmemV' x hxA, hmemV' _ hgxA]
      have hc : π ⟨g * x * g⁻¹, hAM hgxA⟩ =
          π ⟨g, hgM⟩ * π ⟨x, hAM hxA⟩ * (π ⟨g, hgM⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [hc]
      exact Subgroup.mem_normalizer_iff.mp hgb _
    · have hgxA : ¬ g * x * g⁻¹ ∈ A := fun h => hxA ((Subgroup.mem_normalizer_iff.mp hg.2 x).mpr h)
      exact ⟨fun h => absurd (hV'A h) hxA, fun h => absurd (hV'A h) hgxA⟩
  have hVA := hirr V' hV'A hV'1 hV'n
  refine le_antisymm hVB fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := hv
  have hyA : (y : G) ∈ A := hy
  have : (y : G) ∈ V' := hVA ▸ hyA
  exact (hmemV' _ hyA).mp this

theorem pRank_le_three_of_escape {p : ℕ} {P : Sylow p G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hS : Setting G)
    (hd : AGL81CfgData p P M H Q K) : Open.pRank p M ≤ 3 := by
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have h := pRank_inf_le_three_of_setting hS hesc.prime hesc.ne_two hesc.maxTwoLocal_M.1 M
  rwa [inf_idem] at h

theorem quot_comm_of_comm_mem {I : Subgroup G}
    (h : ∀ u ∈ I, ∀ v ∈ I, u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 I) (a b : ↥I ⧸ CFSG.pCore 2 ↥I) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with | _ x => ?_
  induction b using QuotientGroup.induction_on with | _ y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  obtain ⟨z, hz, hzc⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mp
    (h ((y⁻¹ : ↥I) : G) (y⁻¹).2 ((x⁻¹ : ↥I) : G) (x⁻¹).2)
  have hz' : (x * y)⁻¹ * (y * x) = z := by
    apply Subtype.ext
    rw [hzc]
    simp [mul_assoc]
  rw [hz']
  exact hz

theorem exists_comm_not_mem_pCoreOf_of_cZero {X I : Subgroup G} (hI : I ∈ cZero X) :
    ∃ u ∈ I, ∃ v ∈ I, u * v * u⁻¹ * v⁻¹ ∉ pCoreOf 2 I := by
  by_contra hcon
  push Not at hcon
  have hc := quot_comm_of_comm_mem hcon
  rcases hI.shape with h | ⟨-, hb⟩
  · haveI := h.component.2.2.2
    have hcen : Subgroup.center ↥(barM I I) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hc b.1 a.1)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(barM I I) ⧸ Subgroup.center ↥(barM I I))
    induction a using QuotientGroup.induction_on with | _ x => ?_
    induction b using QuotientGroup.induction_on with | _ y => ?_
    apply hab
    rw [QuotientGroup.eq, hcen]
    exact Subgroup.mem_top _
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 (IsSymThreeOrSUThreeTwo.three_dvd_card hb)
    have hcl := IsSymThreeOrSUThreeTwo.closure_two kFactSUThreeTwoShape_holds hb
    have key : ∀ x ∈ Subgroup.closure {x : ↥I ⧸ CFSG.pCore 2 ↥I | ∃ k : ℕ, x ^ (2 ^ k) = 1},
        ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hx
      | one => exact ⟨0, by simp⟩
      | mul x y _ _ hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨b, hb'⟩ := hy
        refine ⟨a + b, ?_⟩
        rw [(show Commute x y from hc x y).mul_pow, pow_add, pow_mul, ha, mul_comm (2 ^ a), pow_mul, hb']
        simp
      | inv x _ hx =>
        obtain ⟨a, ha⟩ := hx
        exact ⟨a, by rw [inv_pow, ha, inv_one]⟩
    obtain ⟨k, hk⟩ := key q (hcl ▸ Subgroup.mem_top q)
    have h3 : 3 ∣ 2 ^ k := hq ▸ orderOf_dvd_of_pow_eq_one hk
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
    omega

theorem comm_mem_pCoreOf_of_bar {M X I : Subgroup G} (hXM : X ≤ M) (hIX : I ≤ X) {u v : G}
    (hu : u ∈ I) (hv : v ∈ I)
    (h : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hXM (hIX hu)⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hXM (hIX hv)⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hXM (hIX hu)⟩)⁻¹ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hXM (hIX hv)⟩)⁻¹ ∈ pCoreOf 2 (barM M X)) :
    u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 I := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIM : I ≤ M := hIX.trans hXM
  let ρ : ↥I →* ↥M ⧸ CFSG.pCore 2 ↥M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hIM)
  let K : Subgroup G := ((pCoreOf 2 (barM M X)).comap ρ).map I.subtype
  have hmemK : ∀ (g : G) (hg : g ∈ I), g ∈ K ↔ ρ ⟨g, hg⟩ ∈ pCoreOf 2 (barM M X) := by
    intro g hg
    constructor
    · intro h'
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp h'
      exact hy
    · intro h'
      exact Subgroup.mem_map.mpr ⟨⟨g, hg⟩, h', rfl⟩
  have hKI : K ≤ I := Subgroup.map_subtype_le _
  have hρX : ∀ (g : G) (hg : g ∈ I), ρ ⟨g, hg⟩ ∈ barM M X :=
    fun g hg => ⟨⟨g, hIM hg⟩, hIX hg, rfl⟩
  have hker : IsPGroup 2 ρ.ker := by
    intro x
    have hm : (⟨(x.1 : G), hIM x.1.2⟩ : ↥M) ∈ CFSG.pCore 2 ↥M :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥M) ⟨(x.1 : G), hIM x.1.2⟩).mp x.2
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M) ⟨_, hm⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥(CFSG.pCore 2 ↥M) => ((z : ↥M) : G)) hk
    simpa using this
  have hKp : IsPGroup 2 K :=
    ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (barM M X)).comap_of_ker_isPGroup ρ
      hker).map I.subtype
  have hIK : I ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    by_cases hk : k ∈ I
    · have hgk : g * k * g⁻¹ ∈ I := I.mul_mem (I.mul_mem hg hk) (I.inv_mem hg)
      rw [hmemK k hk, hmemK _ hgk]
      have e : ρ ⟨g * k * g⁻¹, hgk⟩ = ρ ⟨g, hg⟩ * ρ ⟨k, hk⟩ * (ρ ⟨g, hg⟩)⁻¹ := by
        have : (⟨g * k * g⁻¹, hgk⟩ : ↥I) = ⟨g, hg⟩ * ⟨k, hk⟩ * (⟨g, hg⟩ : ↥I)⁻¹ := rfl
        rw [this]
        simp only [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (barM M X) (hρX g hg)) _
    · have hgk : ¬ g * k * g⁻¹ ∈ I := by
        intro h'
        apply hk
        have e : k = g⁻¹ * (g * k * g⁻¹) * g := by group
        rw [e]
        exact I.mul_mem (I.mul_mem (I.inv_mem hg) h') hg
      exact ⟨fun h' => absurd (hKI h') hk, fun h' => absurd (hKI h') hgk⟩
  have hc : u * v * u⁻¹ * v⁻¹ ∈ I :=
    I.mul_mem (I.mul_mem (I.mul_mem hu hv) (I.inv_mem hu)) (I.inv_mem hv)
  have huvK : u * v * u⁻¹ * v⁻¹ ∈ K := by
    rw [hmemK _ hc]
    have e : ρ ⟨u * v * u⁻¹ * v⁻¹, hc⟩ =
        ρ ⟨u, hu⟩ * ρ ⟨v, hv⟩ * (ρ ⟨u, hu⟩)⁻¹ * (ρ ⟨v, hv⟩)⁻¹ := by
      have : (⟨u * v * u⁻¹ * v⁻¹, hc⟩ : ↥I) =
          ⟨u, hu⟩ * ⟨v, hv⟩ * (⟨u, hu⟩ : ↥I)⁻¹ * (⟨v, hv⟩ : ↥I)⁻¹ := rfl
      rw [this]
      simp only [map_mul, map_inv]
    rw [e]
    exact h
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKI hIK hKp huvK

theorem commutator_le_of_cases_na (hK : KFactParabolicIrredCentralNA) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {M H L A : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hLn : (L.subgroupOf M).Normal) (hM3 : Open.pRank p M ≤ 3) (hAHM : A ≤ H ⊓ M)
    (hA : IsPGroup p A) (hAnc : ¬ IsCyclic ↥A)
    (hI : (cZero (H ⊓ L)).Nonempty)
    (hAJ : ∀ b ∈ A, ∀ x ∈ jZero H L, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 (jZero H L))
    (hNA : H ⊓ Subgroup.normalizer (A : Set G) ≤ M)
    (hirr : ∀ V : Subgroup G, V ≤ A → ¬ V ≤ (frattini ↥A).map A.subtype →
      H ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) → V = A)
    (hcases : ∀ b ∈ A, (∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        IsParabolicTwo (barM M L) (barM M (H ⊓ L)))) :
    ⁅A, L⁆ ≤ pCoreOf 2 L := by
  have hLM : L ≤ M := hL.le
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
  have hAM : A ≤ M := fun a ha => (hAHM ha).2
  by_cases hall : ∀ b ∈ A, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M
  · exact commutator_le_pCoreOf_of_forall hLM hAM hMn hall
  obtain ⟨b₀, hb₀, hb₀'⟩ : ∃ b ∈ A, ¬ ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M :=
    Classical.by_contradiction fun h => hall fun b hb => Classical.by_contradiction fun h' =>
      h ⟨b, hb, h'⟩
  obtain ⟨hcl, hpar⟩ := (hcases b₀ hb₀).resolve_left hb₀'
  have hact := fun b (hb : b ∈ A) =>
    bar_action hLM hLn (hAHM hb) (odd_orderOf_of_isPGroup hp hp2 hA hb) (hAJ b hb)
  have hinj := barHom_injective_of_isPGroup hp hp2 hAM hA
  let e : ↥A ≃* ↥(barM M A) := MulEquiv.ofBijective (barHom M A hAM) ⟨hinj, barHom_surjective M A hAM⟩
  have he : ∀ a : ↥A, ((e a : ↥(barM M A)) : ↥M ⧸ CFSG.pCore 2 ↥M) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(a : G), hAM a.2⟩ := fun a => rfl
  have hBp : IsPGroup p ↥(barM M A) := hA.of_surjective _ (barHom_surjective M A hAM)
  have hBnc : ¬ IsCyclic ↥(barM M A) := fun h =>
    hAnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hnab : ∃ x ∈ barM M (H ⊓ L), ∃ y ∈ barM M (H ⊓ L),
      x * y * x⁻¹ * y⁻¹ ∉ pCoreOf 2 (barM M (H ⊓ L)) := by
    obtain ⟨I₀, hI₀⟩ := hI
    obtain ⟨u, hu, v, hv, huv⟩ := exists_comm_not_mem_pCoreOf_of_cZero hI₀
    have hIX : I₀ ≤ H ⊓ L := hI₀.le
    have hXM : H ⊓ L ≤ M := inf_le_right.trans hLM
    exact ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨u, hXM (hIX hu)⟩, ⟨⟨u, hXM (hIX hu)⟩, hIX hu, rfl⟩,
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨v, hXM (hIX hv)⟩, ⟨⟨v, hXM (hIX hv)⟩, hIX hv, rfl⟩,
      fun h => huv (comm_mem_pCoreOf_of_bar hXM hIX hu hv h)⟩
  have hnormInf : ∀ g : G, g ∈ H → g ∈ Subgroup.normalizer (L : Set G) →
      g ∈ Subgroup.normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    intro g hgH hgL
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp
      (Subgroup.le_normalizer hgH : g ∈ Subgroup.normalizer (H : Set G)) x
    have h2 := Subgroup.mem_normalizer_iff.mp hgL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hkey := hK (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) (barM M (H ⊓ L)) (barM M A)
    (barM M (H ⊓ Subgroup.normalizer (A : Set G))) p hp hp2 hL.component.2.2
    (pCoreOf_barM_eq_bot hL.toIsTwoPrimeComponent) hcl hpar hnab hBp hBnc
    (by
      rintro _ ⟨⟨a, haM⟩, ha, rfl⟩
      exact (hact a ha).2.1)
    (by
      rintro _ ⟨⟨a, haM⟩, ha, rfl⟩
      exact (hact a ha).2.2.1)
    (by
      rintro _ ⟨⟨a, haM⟩, ha, rfl⟩ w hw hwW
      exact (hact a ha).2.2.2 w hw hwW)
    (by
      rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
      exact TenThreeThree.mem_normalizer_barM hgM (hMn hgM))
    (by
      rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
      exact TenThreeThree.mem_normalizer_barM hgM (hnormInf g hg.1 (hMn hgM)))
    (by
      rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
      exact TenThreeThree.mem_normalizer_barM hgM hg.2)
    (fun V hVB hV hVn => irred_transfer_barM hAM hNA e he hirr V hVB hV hVn)
  rcases hkey with hc | h4
  · refine commutator_le_pCoreOf_of_forall hLM hAM hMn fun b hb => ?_
    exact commutator_mem_pCoreOf_of_centralizes hLM (hAM hb) fun y hy =>
      hc _ ⟨⟨b, hAM hb⟩, hb, rfl⟩ y hy
  · exact absurd (h4.trans ((pRank_barM_le hp hp2 _).trans hM3)) (by norm_num)

theorem agl81ElevenElevenParabolicGen_of_na (hC : AGL81TenThreeThreeCasesCfg G)
    (hK : KFactParabolicIrredCentralNA) (h10C : AGL81TenOneCZero G)
    (h91 : AGL81TenNineOneCfg G) : AGL81ElevenElevenParabolicGen G := by
  intro hS p P M H Q K hd hlist hrk hnc L hL hLn hAJ hNA hirr hodd
  obtain ⟨H₁, R₁, hesc⟩ := hd.escape
  have hp : p.Prime := hesc.prime
  have hp2 : p ≠ 2 := hesc.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  set A := d1LiftX p H Q K with hAdef
  have hAQ : A ≤ Q := d1LiftX_le p H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hA3 : IsPGroup p A := hd.base.2.1.to_le hAQ
  have hZ : ∀ k : K, (∀ k' : K, k * k' = k' * k) → k = 1 := by
    intro k hk
    by_contra hk1
    have hcen : Subgroup.center ↥K = ⊤ := by
      haveI := hlist.1
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exfalso
        apply hk1
        have : k ∈ Subgroup.center ↥K := Subgroup.mem_center_iff.mpr fun g => (hk g).symm
        rw [h] at this
        exact Subgroup.mem_bot.mp this
      · exact h
    letI : CommGroup ↥K :=
      { (inferInstance : Group ↥K) with
        mul_comm := fun a b => by
          have := Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top a) b
          exact this.symm }
    haveI := hlist.1
    have hprime := IsSimpleGroup.prime_card (α := ↥K)
    obtain ⟨E, hEK, hE, hEc⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp hrk
    have hdvd : p ^ 2 ∣ Nat.card K := hEc ▸ Subgroup.card_dvd_of_le hEK
    have h1 : p ∣ Nat.card K := (dvd_pow_self p two_ne_zero).trans hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime p h1) with h | h
    · exact hp.ne_one h
    · rw [← h] at hdvd
      have := Nat.le_of_dvd hp.pos hdvd
      nlinarith [hp.two_le]
  obtain ⟨-, S, hSA, ⟨e⟩⟩ := OtherCfg.d1LiftX_facts_gen hd hZ
  have hA2 : 2 ≤ Open.pRank p A := (OtherCfg.pRank_eq_of_sylow_equiv S e).symm ▸ hrk
  exact commutator_le_of_cases_na hK hp hp2 hL hLn (pRank_le_three_of_escape hS hd)
    (le_inf hAH hAM) hA3 (not_isCyclic_of_two_le_pRank hp hA2)
    (h10C hS p P M H Q K hd L hL (h91 hS p P M H Q K hd L hL)) hAJ hNA hirr
    fun b hb => hC hS p P M H Q K hd L hL hLn b ⟨hAH hb, hAM hb⟩
      (odd_orderOf_of_isPGroup hp hp2 hA3 hb) (hAJ b hb)

theorem agl81ElevenElevenParabolic_of_na (hC : AGL81TenThreeThreeCasesCfg G)
    (hK : KFactParabolicIrredCentralNA) (h10C : AGL81TenOneCZero G)
    (h91 : AGL81TenNineOneCfg G) : AGL81ElevenElevenParabolic G := by
  intro hS P M H Q K hd hA6 hnc L hL hLn hJX hAJ hNA hirr hodd
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set A := d1LiftX 3 H Q K with hAdef
  obtain ⟨-, hAe, hAc⟩ := d1LiftX_facts_cfg hd hA6
  have hAc' : Nat.card A = 3 ^ 2 := by rw [hAc]; norm_num
  have hAQ : A ≤ Q := d1LiftX_le 3 H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hA3 : IsPGroup 3 A := hd.base.2.1.to_le hAQ
  have hA2 : 2 ≤ Open.pRank 3 A := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hAe hAc'
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  exact commutator_le_of_cases_na hK hp hp2 hL hLn (pRank_le_three_of_escape hS hd)
    (le_inf hAH hAM) hA3 (not_isCyclic_of_two_le_pRank hp hA2)
    (h10C hS 3 P M H Q K hd L hL (h91 hS 3 P M H Q K hd L hL)) hAJ hNA
    (fun V hVA hV hVn => hirr V hVA (fun h => hV (by rw [h]; exact bot_le)) hVn)
    fun b hb => hC hS 3 P M H Q K hd L hL hLn b ⟨hAH hb, hAM hb⟩
      (odd_orderOf_of_isPGroup hp hp2 hA3 hb) (hAJ b hb)

end CFSG.LocalAnalysis.RankThreeTheoremC
