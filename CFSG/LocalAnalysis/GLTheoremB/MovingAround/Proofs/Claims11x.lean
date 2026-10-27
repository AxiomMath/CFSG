module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1114
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1110
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1113b
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims11x

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Sub118

variable {G : Type} [Group G] [Finite G]

@[expose] def Input23_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K A B : Subgroup G),
    GLAPComponent p X K → A ≤ X → A ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian p A →
    ∀ n : ℕ, p < n → ¬ p ∣ n → IsAltType n (barOf p K) →
    p ^ (n / p) * Nat.card ↥(A ⊓ centBar p ⊤ K) ≤ Nat.card A →
    B ≤ A → CFSG.Open.pRank p B = 2 →
      barX p X K ≤ barX p X (⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Lemma123.Ke' p K e)

theorem le_centBar_of_ne {X L J : Subgroup G} (hL : GLAPComponent 3 X L)
    (hJ : GLAPComponent 3 X J) (hne : J ≠ L) : J ≤ centBar 3 X L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hL
  have hJs := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    Nat.prime_three).1 hJ
  have hne' : J.subgroupOf X ≠ L.subgroupOf X := by
    intro h
    apply hne
    have := Subgroup.subgroupOf_inj.1 h
    rwa [inf_of_le_left hJ.1, inf_of_le_left hL.1] at this
  obtain ⟨-, hn2, hcomm, -⟩ :=
    (CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 3
      Nat.prime_three _ _ hJs.2 hLs.2).2 hne'
  intro j hj
  have hjX : j ∈ X := hJ.1 hj
  have hjs : (⟨j, hjX⟩ : ↥X) ∈ J.subgroupOf X := Subgroup.mem_subgroupOf.2 hj
  have hjN : j ∈ Subgroup.normalizer (L : Set G) :=
    Inputs1114.mem_normalizer_of_subgroupOf hL.1 (n := ⟨j, hjX⟩) (hn2 hjs)
  refine Inputs1114.mem_centBar_iff_forall.2 ⟨hjX, hjN, fun l hl => ?_⟩
  have hls : (⟨l, hL.1 hl⟩ : ↥X) ∈ L.subgroupOf X := Subgroup.mem_subgroupOf.2 hl
  have h1 := hcomm (Subgroup.commutator_mem_commutator hjs hls)
  obtain ⟨z, hz, hzc⟩ := (Subgroup.mem_inf.1 h1).2
  let e : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  have hez : e z ∈ GLAPPrimeCore 3 ↥L := by
    have := glaPPrimeCore_map_iso 3 e
    rw [← this]
    exact ⟨z, hz, rfl⟩
  refine ⟨e z, hez, ?_⟩
  have : ((e z : ↥L) : G) = ((z : ↥X) : G) := rfl
  show ((e z : ↥L) : G) = j * l * j⁻¹ * l⁻¹
  rw [this]
  have h2 := congrArg (fun w : ↥X => (w : G)) hzc
  simpa [commutatorElement_def] using h2

theorem le_normalizer_of_rank {X K Q : Subgroup G} (hK : GLAPComponent 3 X K) (hQK : Q ≤ K)
    (hQ : IsElemAbelian 3 Q) (hQc : 3 < Nat.card Q)
    (hrk : ∀ U : Subgroup G, U ≤ centBar 3 X K → IsElemAbelian 3 U → Nat.card U ≤ 3) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hX : GLBConj g X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg)
  have hK' : GLAPComponent 3 X (GLBConj g K) := by
    have := glaPComponent_gLBConj hK g
    rwa [hX] at this
  rw [mem_normalizer_iff_gLBConj_eq]
  by_contra hne
  have hle := le_centBar_of_ne hK hK' hne
  have h1 := hrk (GLBConj g Q) ((gLBConj_mono g hQK).trans hle)
    (Lemma118T.isElemAbelian_gLBConj' hQ g)
  rw [Lemma1112b.card_glbConj] at h1
  omega

theorem rank_bound {n : ℕ} {K Q₁ Q₂ : Subgroup G} {a : G}
    (hn : IsAltType n (barOf 3 K)) (hn10 : 10 ≤ n)
    (hT : Lemma118T.TransportData 3 n K a Q₁ Q₂) (ha1 : a ≠ 1)
    (hq4 : CFSG.Open.pRank 3 (Q₁ ⊔ Q₂) = 4) :
    n / 3 = 3 ∧ ∀ U : Subgroup G, U ≤ centBar 3 (Cg a) K → IsElemAbelian 3 U → Nat.card U ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : Q₂ ⊓ K = ⊥ :=
    Lemma118T.inf_eq_bot_of_elemAb_le_centBar hn (by omega) hT.Q₂C hT.Q₂ab
  have hdisj : Q₁ ⊓ Q₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz2 : z ∈ Q₂ ⊓ K := Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hz).2, hT.Q₁K (Subgroup.mem_inf.1 hz).1⟩
    rw [h2] at hz2
    exact hz2
  have hcard := CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hT.comm hdisj
  obtain ⟨k₁, hk₁⟩ := exists_card_eq_pow (Lemma118T.isPGroup_of_isElemAbelian hT.Q₁ab)
  obtain ⟨k₂, hk₂⟩ := exists_card_eq_pow (Lemma118T.isPGroup_of_isElemAbelian hT.Q₂ab)
  have hr₁ : CFSG.Open.pRank 3 Q₁ = k₁ := Lemma118T.pRank_eq_of_isElemAbelian_card hT.Q₁ab hk₁
  have hr₂ : CFSG.Open.pRank 3 Q₂ = k₂ := Lemma118T.pRank_eq_of_isElemAbelian_card hT.Q₂ab hk₂
  have hQab : IsElemAbelian 3 (Q₁ ⊔ Q₂) := by
    refine isElemAbelian_sup_of_commute hT.Q₁ab hT.Q₂ab ?_
    exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hT.comm x hx y hy).symm
  have hr : CFSG.Open.pRank 3 (Q₁ ⊔ Q₂) = k₁ + k₂ :=
    Lemma118T.pRank_eq_of_isElemAbelian_card hQab (by rw [hcard, hk₁, hk₂, pow_add])
  have hk₁n : k₁ = n / 3 := by rw [← hr₁]; exact hT.Q₁rk
  have hk₂1 : 1 ≤ k₂ := by
    by_contra h0
    have hk0 : k₂ = 0 := by omega
    rw [hk0, pow_zero] at hk₂
    have hbot : Q₂ = ⊥ := (Subgroup.eq_bot_iff_card _).2 hk₂
    have : a ∈ Q₂ := hT.aQ₂
    rw [hbot] at this
    exact ha1 (Subgroup.mem_bot.1 this)
  have hn3 : 3 ≤ n / 3 := by omega
  refine ⟨by omega, fun U hUC hU => ?_⟩
  have hUr := hT.Q₂max U hUC hU
  obtain ⟨k, hk⟩ := exists_card_eq_pow (Lemma118T.isPGroup_of_isElemAbelian hU)
  have hUr' : CFSG.Open.pRank 3 U = k := Lemma118T.pRank_eq_of_isElemAbelian_card hU hk
  have hk1 : k ≤ 1 := by omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    _ = 3 := by norm_num

theorem inf_centBar_top_le {A K : Subgroup G} {a : G} (hA : A ≤ Cg a) :
    A ⊓ centBar 3 ⊤ K ≤ centBar 3 (Cg a) K := by
  intro x hx
  obtain ⟨hxA, hxc⟩ := Subgroup.mem_inf.1 hx
  unfold centBar at hxc ⊢
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxc).1, hA hxA⟩

theorem isAltType_quot_center {K : Subgroup G} {n : ℕ} (hn : IsAltType n (barOf 3 K)) (hn4 : 4 ≤ n) :
    IsAltType n (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) := by
  have hZ : Subgroup.center (barOf 3 K) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    exact Subgroup.mem_bot.2 (Lemma118T.eq_one_of_central_barOf K hn hn4 w
      (fun v => Subgroup.mem_center_iff.1 hw v))
  obtain ⟨e⟩ := hn
  exact ⟨(l119_center_bot_quot hZ).trans e⟩

theorem faithful_A0 {E A K : Subgroup G} {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) (haE : a ∉ E ⊓ A)
    (hAel : IsElemAbelian 3 A) (hKa : ∀ k ∈ K, a * k = k * a)
    (hAC : Nat.card ↥(A ⊓ centBar 3 ⊤ K) ≤ 3) :
    ∀ x ∈ E ⊓ A, x ∈ centBar 3 ⊤ K → x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx hxc
  by_contra hx1
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have hx3 : x ^ 3 = 1 := hAel.2 x hx.2
  have haN : a ∈ Subgroup.normalizer (K : Set G) := Lemma1112b.mem_normalizer_of_central hKa
  have hac : a ∈ centBar 3 ⊤ K := Lemma1112b.mem_centBar_top_of_central haN hKa
  have hza : Subgroup.zpowers a ≤ A ⊓ centBar 3 ⊤ K :=
    Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨ha, hac⟩)
  have hcard_a : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have heq : Subgroup.zpowers a = A ⊓ centBar 3 ⊤ K :=
    Subgroup.eq_of_le_of_card_ge hza (by rw [hcard_a]; exact hAC)
  have hxa : x ∈ Subgroup.zpowers a := by rw [heq]; exact Subgroup.mem_inf.2 ⟨hx.2, hxc⟩
  have hzx : Subgroup.zpowers x ≤ Subgroup.zpowers a := Subgroup.zpowers_le.2 hxa
  have hcard_x : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hxeq : Subgroup.zpowers x = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge hzx (by rw [hcard_a, hcard_x])
  have haX : a ∈ Subgroup.zpowers x := by rw [hxeq]; exact Subgroup.mem_zpowers a
  exact haE ((Subgroup.zpowers_le.2 hx) haX)

end Sub118

section Q2

variable {G : Type} [Group G] [Finite G]

theorem isSylowIn_top_subgroupOf {Y P : Subgroup G} (hP : IsSylowIn 3 Y P) :
    IsSylowIn 3 (⊤ : Subgroup ↥Y) (P.subgroupOf Y) := by
  refine ⟨le_top, hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm, ?_⟩
  intro R' _ hR'3 hPR'
  have hmap : R'.map Y.subtype = P := by
    refine hP.2.2 (R'.map Y.subtype) ?_ (hR'3.map Y.subtype) ?_
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · intro p hp
      exact ⟨⟨p, hP.1 hp⟩, hPR' (by simpa [Subgroup.mem_subgroupOf] using hp), rfl⟩
  rw [← hmap]
  exact (Subgroup.comap_map_eq_self_of_injective Y.subtype_injective R').symm

theorem exists_conj_le_of_isSylowIn {Y P R : Subgroup G} (hP : IsSylowIn 3 Y P) (hRY : R ≤ Y)
    (hR : IsPGroup 3 R) : ∃ y ∈ Y, ∀ r ∈ R, y⁻¹ * r * y ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP' := isSylowIn_top_subgroupOf hP
  obtain ⟨g, hg⟩ := Lemma1112b.exists_glbConj_le_of_isSylowIn hP'
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm : IsPGroup 3 (R.subgroupOf Y))
  refine ⟨(g : G), g.2, fun r hr => ?_⟩
  have hmem : (⟨r, hRY hr⟩ : ↥Y) ∈ R.subgroupOf Y := by simpa [Subgroup.mem_subgroupOf] using hr
  have h1 : (g⁻¹ * ⟨r, hRY hr⟩ * g : ↥Y) ∈ GLBConj g (R.subgroupOf Y) :=
    Lemma1112b.mem_glbConj.2 ⟨_, hmem, rfl⟩
  have h2 := hg h1
  simpa [Subgroup.mem_subgroupOf] using h2

theorem mem_A0_of_central (h1112 : Lemma1112Statement) (h104ii : Lemma104_iiStatement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    {R : Subgroup G} (hR : IsSylowIn 3 M R) (hAR : A ≤ R)
    {z : G} (hzc : ∀ g ∈ R, g * z = z * g) (hz3 : z ^ 3 = 1) : z ∈ E ⊓ A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsc := h104ii h.toCex117Base.toSec11.toSec10Fails h.pair
  have hzA : z ∈ A := l1110_mem_of_isSCp hsc.2 hAR hzc hz3
  by_contra hzA0
  have hz1 : z ≠ 1 := fun h1 => hzA0 (h1 ▸ (E ⊓ A).one_mem)
  obtain ⟨⟨-, hCa⟩, -, hconj⟩ := h1112 h
  have hIE : IsEkIn 3 1 A (Subgroup.zpowers z) :=
    ⟨Subgroup.zpowers_le.2 hzA, CFSG.Open.isElemAbelian_zpowers hz3, by
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]; norm_num⟩
  obtain ⟨g, hg⟩ := (hconj _ hIE).1 fun hle => hzA0 (Subgroup.zpowers_le.1 hle)
  have hCz : Cg z = GLBConj g (Cg a) := by
    rw [Lemma1114.glbConj_centralizer_singleton]
    exact (Lemma1114.centralizer_singleton_eq_of_zpowers_eq
      ((Lemma1114.glbConj_zpowers g a).symm.trans hg)).symm
  have hrCz : CFSG.Open.pRank 3 (Cg z) = 3 := by
    rw [hCz, Lemma118T.pRank_gLBConj' (by norm_num)]
    exact hCa
  have hRCz : R ≤ Cg z := fun r hr => Subgroup.mem_centralizer_singleton_iff.2 (hzc r hr)
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal h.standing h.bOne h.pre
  obtain ⟨hBab, hBcard, -⟩ := h.bOne.1
  have hBr : CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G :=
    Lemma118T.pRank_eq_of_isElemAbelian_card hBab hBcard
  obtain ⟨y, -, hy⟩ := exists_conj_le_of_isSylowIn hR hBM
    (Lemma118T.isPGroup_of_isElemAbelian hBab)
  have hBy : GLBConj y B ≤ R := by
    intro x hx
    have hx' := (mem_gLBConj).1 hx
    have := hy _ hx'
    simpa [mul_assoc] using this
  have h4 : 4 ≤ CFSG.Open.pRank 3 R := by
    have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hBy
    rw [Lemma118T.pRank_gLBConj' (by norm_num), hBr, h.standing.rank_eq] at h1
    have := h.standing.four_le
    omega
  have h5 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hRCz
  omega

theorem exists_A0_mem_layer (h1112 : Lemma1112Statement) (h104ii : Lemma104_iiStatement)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    (hL : GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥) :
    ∃ (z : G) (hz : z ∈ M), z ∈ E ⊓ A ∧ z ≠ 1 ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨z, hz⟩ : ↥M) ∈
        GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  set Lq := GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) with hLq
  have hO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3
  have hLn : Lq.Normal := Lemma1113b.layer_top_normal hO
  have h3L : 3 ∣ Nat.card Lq := by
    by_contra h3
    apply hL
    have hcop : Nat.Coprime 3 (Nat.card Lq) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have hle : Lq ≤ GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) :=
      le_sSup (s := {N : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
        ⟨hLn, hcop⟩
    rw [hO] at hle
    exact le_bot_iff.1 hle
  set Lh : Subgroup ↥M := Lq.comap π with hLh
  have hLhn : Lh.Normal := hLn.comap π
  have hmap : Lh.map π = Lq := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Lq
  have h3Lh : 3 ∣ Nat.card Lh := by
    have := Subgroup.card_map_dvd Lh π
    rw [hmap] at this
    exact h3L.trans this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3Lh
  set x₀ : G := ((x : ↥M) : G) with hx₀
  have hx₀M : x₀ ∈ M := (x : ↥M).2
  have hx₀3 : orderOf x₀ = 3 := by
    rw [hx₀, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  obtain ⟨R, hR, hAR⟩ := Lemma1112b.exists_isSylowIn_ge hAM (Lemma118T.isPGroup_of_isElemAbelian hAel)
  have hx₀p : IsPGroup 3 (Subgroup.zpowers x₀) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hx₀3]
    exact ⟨1, by norm_num⟩
  obtain ⟨y, hyM, hy⟩ := exists_conj_le_of_isSylowIn hR (Subgroup.zpowers_le.2 hx₀M) hx₀p
  set x₁ : G := y⁻¹ * x₀ * y with hx₁
  have hx₁R : x₁ ∈ R := hy x₀ (Subgroup.mem_zpowers x₀)
  have hx₁M : x₁ ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hyM) hx₀M) hyM
  have hx₁Lh : (⟨x₁, hx₁M⟩ : ↥M) ∈ Lh := by
    have : (⟨x₁, hx₁M⟩ : ↥M) = (⟨y, hyM⟩ : ↥M)⁻¹ * (x : ↥M) * ((⟨y, hyM⟩ : ↥M)⁻¹)⁻¹ := by
      apply Subtype.ext
      simp [hx₁, hx₀]
    rw [this]
    exact hLhn.conj_mem _ x.2 _
  have hx₁1 : x₁ ≠ 1 := by
    intro h1
    have : x₀ = 1 := by
      have e : x₀ = y * x₁ * y⁻¹ := by rw [hx₁]; group
      rw [e, h1]; group
    rw [this, orderOf_one] at hx₀3
    norm_num at hx₀3
  set LhG : Subgroup G := Lh.map M.subtype with hLhG
  have hRM : R ≤ M := hR.1
  have hNn : (LhG.subgroupOf R).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨(g : G), hRM g.2⟩ * w * (⟨(g : G), hRM g.2⟩ : ↥M)⁻¹,
      hLhn.conj_mem w hw _, ?_⟩
    simp [← hwn]
  have hN1 : LhG.subgroupOf R ≠ ⊥ := by
    intro hbot
    have hmem : (⟨x₁, hx₁R⟩ : ↥R) ∈ LhG.subgroupOf R :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨⟨x₁, hx₁M⟩, hx₁Lh, rfl⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx₁1 (congrArg Subtype.val hmem)
  have hR3 : IsPGroup 3 ↥R := hR.2.1
  haveI : Group.IsNilpotent ↥R := hR3.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN1
  set W : Subgroup ↥R := LhG.subgroupOf R ⊓ Subgroup.center ↥R with hW
  have hW3 : IsPGroup 3 ↥W := hR3.to_subgroup W
  have hWnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hZ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hW3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.2 hWnt).ne' hk
  have h3W : 3 ∣ Nat.card ↥W := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 3 h3W
  set z : G := (((w : ↥R) : G)) with hz
  have hzR : z ∈ R := (w : ↥R).2
  have hzM : z ∈ M := hRM hzR
  have hz3 : orderOf z = 3 := by rw [hz, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hzc : ∀ g ∈ R, g * z = z * g := by
    intro g hg
    have := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 w.2).2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hzA0 := mem_A0_of_central h1112 h104ii h hR hAR hzc (by rw [← hz3]; exact pow_orderOf_eq_one z)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz3
    norm_num at hz3
  refine ⟨z, hzM, hzA0, hz1, ?_⟩
  have hzL : z ∈ LhG := Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 w.2).1
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 hzL
  have : (⟨z, hzM⟩ : ↥M) = u := Subtype.ext hu'.symm
  rw [this]
  exact hu

theorem tilde_mem_layer (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement)
    {m p : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m p B M E A a K)
    (hp : p = 3) (e : G) (he : e ∈ M) (heEA : e ∈ E ⊓ A) (he1 : e ≠ 1)
    (hL : GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨e, he⟩ : ↥M) ∈
      GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
  subst hp
  have hO : GLAPPrimeCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ :=
    CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3
  have hLn := Lemma1113b.layer_top_normal hO
  obtain ⟨z, hzM, hzA0, hz1, hzL⟩ := exists_A0_mem_layer h1112 h104ii h hL
  have hIL : IsLThreeFour (barOf 3 K) := (h1111 h).2.2
  obtain ⟨n, -, hnN, hne⟩ :=
    Inputs1114.lemma1114FusionInput_of_inputs h119 h1112 h rfl hIL z hzA0 hz1 e heEA he1
  have hnM : n ∈ M := l1110_normalizer_A0_le h.pair.1.1 (h119 h).1 hnN
  have heq : (⟨e, he⟩ : ↥M) = (⟨n, hnM⟩ : ↥M)⁻¹ * ⟨z, hzM⟩ * ((⟨n, hnM⟩ : ↥M)⁻¹)⁻¹ := by
    apply Subtype.ext
    simp [← hne]
  rw [heq, map_mul, map_mul]
  have := hLn.conj_mem _ hzL (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨n, hnM⟩ : ↥M))⁻¹
  simpa [map_inv] using this

end Q2

section Q3

theorem eq_one_of_centralizes_layer {Y : Type} [Group Y] [Finite Y]
    (hO : GLAPPrimeCore 3 Y = ⊥) (hO3 : CFSG.pCore 3 Y = ⊥) (g : Y)
    (hg : ∀ l ∈ GLAPLayer 3 (⊤ : Subgroup Y), g * l = l * g) : g = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO' : CFSG.pPrimeCore 3 Y = ⊥ := hO
  have hlay : GLAPLayer 3 (⊤ : Subgroup Y) = CFSG.layer Y := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.l28b_glaPLayer_top_eq_layer Nat.prime_three hO,
      CFSG.layer_eq_componentClassification]
  have hF : CFSG.generalizedFitting Y = CFSG.layer Y := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.Fitting_eq_pcore Y 3 hO', hO3, bot_sup_eq]
  have hgC : g ∈ Subgroup.centralizer (CFSG.generalizedFitting Y : Set Y) := by
    rw [hF, Subgroup.mem_centralizer_iff]
    intro l hl
    rw [← hlay] at hl
    exact (hg l hl).symm
  have hgL : g ∈ CFSG.layer Y := hF ▸ CFSG.centralizer_generalizedFitting_le Y hgC
  have hz : g ∈ (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype := by
    refine ⟨⟨g, hgL⟩, Subgroup.mem_center_iff.2 fun l => Subtype.ext ?_, rfl⟩
    have hl : (l : Y) ∈ GLAPLayer 3 (⊤ : Subgroup Y) := by rw [hlay]; exact l.2
    exact (hg l hl).symm
  have := CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 3 hO' hz
  rw [hO3] at this
  exact Subgroup.mem_bot.1 this

end Q3

@[expose] def Lemma1113O3Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → p = 3 →
    GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥ →
      CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥

@[expose] def Lemma1113SimpleClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → p = 3 →
    GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥ →
    CFSG.pCore 3 (↥M ⧸ GLAPPrimeCore 3 ↥M) = ⊥ →
      CFSG.Open.IsQuasisimple ↥(GLAPLayer 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)))

theorem nonsolvQuasisimpleClaim_of_inputs (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h104ii : Lemma104_iiStatement) (hO3 : Lemma1113O3Claim)
    (hS : Lemma1113SimpleClaim) : Lemma1113b.NonsolvQuasisimpleClaim := by
  intro G _ _ m p B M E A a K h hp e he heEA he1 hL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO3' := hO3 G m p B M E A a K h hp hL
  refine ⟨hS G m p B M E A a K h hp hL hO3',
    tilde_mem_layer h1111 h1112 h119 h104ii h hp e he heEA he1 hL, ?_⟩
  intro g hg
  exact eq_one_of_centralizes_layer (CFSG.GH74.pPrimeCore_quotient_pPrimeCore_eq_bot ↥M 3) hO3' g hg

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem eq_one_of_mem_coprime {N T : Subgroup Y} (hN : Nat.Coprime 3 (Nat.card N))
    (hT : IsPGroup 3 ↥T) {w : Y} (hwN : w ∈ N) (hwT : w ∈ T) : w = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hT) ⟨w, hwT⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf w ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨w, hwN⟩ : ↥N)
    rwa [Subgroup.orderOf_mk] at this
  rw [hk] at hdvd
  have h1 : 3 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hN) hdvd
  rw [← hk] at h1
  exact orderOf_eq_one_iff.1 h1

theorem exists_lift_of_coprime (N : Subgroup Y) [N.Normal] (hN : Nat.Coprime 3 (Nat.card N))
    {H : Subgroup Y} {T' : Subgroup (Y ⧸ N)} (hTH : T' ≤ H.map (QuotientGroup.mk' N))
    (hT3 : IsPGroup 3 ↥T') {S : Subgroup Y} (hSH : S ≤ H) (hS3 : IsPGroup 3 ↥S)
    (hST : S.map (QuotientGroup.mk' N) ≤ T') :
    ∃ T : Subgroup Y, S ≤ T ∧ T ≤ H ∧ IsPGroup 3 ↥T ∧ T.map (QuotientGroup.mk' N) = T' ∧
      ∀ x ∈ T, ∀ y ∈ T, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  set P : Subgroup Y := H ⊓ T'.comap π with hP
  have hSP : S ≤ P := le_inf hSH (fun s hs => hST ⟨s, hs, rfl⟩)
  obtain ⟨T, hT, hST'⟩ := Lemma1112b.exists_isSylowIn_ge hSP hS3
  have hTP : T ≤ P := hT.1
  have hT3' : IsPGroup 3 ↥T := hT.2.1
  have hinj : ∀ x ∈ T, ∀ y ∈ T, π x = π y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ N := (QuotientGroup.eq).1 hxy
    have h1 := eq_one_of_mem_coprime hN hT3' hmem (T.mul_mem (T.inv_mem hx) hy)
    rw [inv_mul_eq_one] at h1
    exact h1
  have hPmap : P.map π = T' := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro t ht
      obtain ⟨h, hh, rfl⟩ := hTH ht
      exact ⟨h, ⟨hh, ht⟩, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hT3
  have hdvd : 3 ^ k ∣ Nat.card P := by
    rw [← hk, ← hPmap]
    exact Subgroup.card_map_dvd P π
  obtain ⟨C, hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 3 hdvd
  have hCP : C.map P.subtype ≤ P := Subgroup.map_subtype_le C
  have hCcard : Nat.card (C.map P.subtype) = 3 ^ k := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hC]
  have hC3 : IsPGroup 3 ↥(C.map P.subtype) := IsPGroup.of_card hCcard
  have hle := Lemma1112b.card_le_of_isSylowIn hT hCP hC3
  rw [hCcard] at hle
  let f : ↥T →* Y ⧸ N := π.comp T.subtype
  have hf : Function.Injective f := fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy)
  have hfr : f.range = T.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardTm : Nat.card (T.map π) = Nat.card T := by
    rw [← hfr]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hTm : T.map π ≤ T' := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hTP hx).2
  refine ⟨T, hST', hTP.trans inf_le_left, hT3', ?_, hinj⟩
  exact Subgroup.eq_of_le_of_card_ge hTm (by rw [hcardTm, hk]; exact hle)

end Lift

section Chev

open CFSG.HardMathSupport.Solomon.Coordinator (IsChevOfChar)

@[expose] def Input29_5 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), L.Normal → CFSG.Open.IsQuasisimple ↥L →
    CFSG.Open.IsKGroup ↥L → (∀ g : X, (∀ l ∈ L, g * l = l * g) → g = 1) →
    ¬ IsChevOfChar 3 (↥L ⧸ Subgroup.center ↥L) →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ x : X, orderOf x = 3 →
    (∀ S : Subgroup X, S ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4) →
    CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set X)) = 3 →
    CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set X)) →
      x ∉ L ∧ CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 4 ∧
      (∀ Q : Subgroup X, IsSylowIn 3 (L ⊓ Subgroup.centralizer ({x} : Set X)) Q →
        (∀ q ∈ Q, q ^ 3 = 1) ∧ ∃ q₁ ∈ Q, ∃ q₂ ∈ Q, q₁ * q₂ ≠ q₂ * q₁) ∧
      (∀ D : Subgroup X, D ≤ L ⊓ Subgroup.centralizer ({x} : Set X) → IsElemAbelian 3 D →
        Nat.card D = 9 → ∃ E : Subgroup X, D ≤ E ∧ E ≤ L ∧ IsElemAbelian 3 E ∧
          Nat.card E = 81 ∧ IsPGroup 3 ↥(E ⊔ Subgroup.zpowers x))

@[expose] def Lemma1113SolvClaim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → p = 3 → CFSG.HallHigman.IsPSolvable 3 ↥(M ⊓ Cg a)

@[expose] def Lemma1113C4Claim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G) (K : Subgroup G),
    Cex117 G m p B M E A a K → p = 3 → ∀ S : Subgroup G, S ≤ Cg a → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_injOn {Y Z : Type} [Group Y] [Group Z] (f : Y →* Z) {T : Subgroup Y}
    (hinj : ∀ x ∈ T, ∀ y ∈ T, f x = f y → x = y) (hT : IsElemAbelian 3 (T.map f)) :
    IsElemAbelian 3 T ∧ Nat.card T = Nat.card (T.map f) := by
  have hc : ∀ x ∈ T, ∀ y ∈ T, f x * f y = f y * f x := fun x hx y hy =>
    congrArg Subtype.val (hT.1.is_comm.comm ⟨f x, x, hx, rfl⟩ ⟨f y, y, hy, rfl⟩)
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have h1 : f ((x : Y) * y) = f ((y : Y) * x) := by
      rw [map_mul, map_mul]
      exact hc _ x.2 _ y.2
    exact hinj _ (T.mul_mem x.2 y.2) _ (T.mul_mem y.2 x.2) h1
  · refine hinj _ (T.pow_mem hx 3) _ T.one_mem ?_
    rw [map_pow, map_one]
    exact hT.2 _ ⟨x, hx, rfl⟩
  · let g : ↥T →* Z := f.comp T.subtype
    have hg : Function.Injective g := fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy)
    have hgr : g.range = T.map f := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hgr]
    exact Nat.card_congr (MonoidHom.ofInjective hg).toEquiv

theorem four_le_pRank_tilde {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h : Cex117 G m 3 B M E A a K) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal h.standing h.bOne h.pre
  obtain ⟨hBab, hBcard, -⟩ := h.bOne.1
  have hBr : CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G :=
    Lemma118T.pRank_eq_of_isElemAbelian_card hBab hBcard
  have h1 := l119_pRank_image_ge Nat.prime_three hBM hBab
  have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num)
    (le_top : (B.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)) ≤ ⊤)
  rw [hBr, h.standing.rank_eq] at h1
  have := h.standing.four_le
  omega

theorem pRank_le_tilde {M F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 3 F) :
    CFSG.Open.pRank 3 F ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
  (l119_pRank_image_ge Nat.prime_three hFM hF).trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

theorem exists_lift_centralizer {M : Subgroup G} {a : G} (haM : a ∈ M) (ha3 : a ^ 3 = 1)
    {S : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)}
    (hS : S ≤ Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M)} :
      Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) (hS3 : IsPGroup 3 ↥S) :
    ∃ T : Subgroup ↥M, T ≤ Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M) ∧ IsPGroup 3 ↥T ∧
      T.map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)) = S ∧
      ∀ x ∈ T, ∀ y ∈ T, QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) x =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) y → x = y := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3' : (⟨a, haM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hord : ∃ k : ℕ, orderOf (⟨a, haM⟩ : ↥M) = 3 ^ k := by
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha3')
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hcent := CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map 3 hord
  have hN : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥M)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨T, -, hTH, hT3, hTm, hinj⟩ := exists_lift_of_coprime (GLAPPrimeCore 3 ↥M) hN
    (H := Subgroup.centralizer ({(⟨a, haM⟩ : ↥M)} : Set ↥M)) (hS.trans (le_of_eq hcent)) hS3
    (S := ⊥) bot_le (IsPGroup.of_bot) (by rw [Subgroup.map_bot]; exact bot_le)
  exact ⟨T, hTH, hT3, hTm, hinj⟩

theorem tilde_centralizer_facts (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (hSolv : Lemma1113SolvClaim) (hC4 : Lemma1113C4Claim)
    {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G} (h : Cex117 G m 3 B M E A a K)
    (haM : a ∈ M) :
    (∀ S : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M),
        S ≤ Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M)} :
          Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) → IsPGroup 3 ↥S → Nat.card S ≤ 3 ^ 4) ∧
      CFSG.Open.pRank 3 (Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M)} :
          Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) = 3 ∧
      CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer
        ({QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) (⟨a, haM⟩ : ↥M)} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore 3 ↥M) with hπ
  set a' : ↥M := ⟨a, haM⟩ with ha'
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have ha : a ∈ A := h.ha.1
  have ha3 : a ^ 3 = 1 := hAel.2 a ha
  have ha3' : a' ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hord : ∃ k : ℕ, orderOf a' = 3 ^ k := by
    obtain h1 | h3 := (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ha3')
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h3, pow_one]⟩
  have hcent : Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) =
      (Subgroup.centralizer ({a'} : Set ↥M)).map π :=
    CFSG.GH74.centralizer_singleton_pPrimeCore_quotient_eq_map 3 hord
  have hTG : ∀ T : Subgroup ↥M, T ≤ Subgroup.centralizer ({a'} : Set ↥M) → T.map M.subtype ≤ Cg a := by
    intro T hT
    rintro _ ⟨x, hx, rfl⟩
    have h1 : x * a' = a' * x := Subgroup.mem_centralizer_singleton_iff.1 (hT hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val h1)
  have hCa : CFSG.Open.pRank 3 (Cg a) = 3 := ((h1112 h).1).2
  refine ⟨?_, ?_, ?_⟩
  · intro S hS hS3
    obtain ⟨T, hTC, hT3, hTm, hinj⟩ := exists_lift_centralizer haM ha3 hS hS3
    have hcardT : Nat.card T = Nat.card S := by
      let g : ↥T →* (↥M ⧸ GLAPPrimeCore 3 ↥M) := π.comp T.subtype
      have hg : Function.Injective g := fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy)
      have hgr : g.range = S := by rw [MonoidHom.range_comp, Subgroup.range_subtype, hTm]
      rw [← hgr]
      exact Nat.card_congr (MonoidHom.ofInjective hg).toEquiv
    have h1 := hC4 G m 3 B M E A a K h rfl (T.map M.subtype) (hTG T hTC) (hT3.map M.subtype)
    rw [Subgroup.card_map_of_injective M.subtype_injective, hcardT] at h1
    exact h1
  · refine le_antisymm ?_ ?_
    · obtain ⟨E', hE'C, hE'el, hE'card⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
        (Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)))
      obtain ⟨T, hTC, -, hTm, hinj⟩ := exists_lift_centralizer haM ha3 hE'C
        (Lemma118T.isPGroup_of_isElemAbelian hE'el)
      rw [← hTm] at hE'el hE'card
      obtain ⟨hTel, hTcard⟩ := isElemAbelian_of_injOn π hinj hE'el
      have hTGel : IsElemAbelian 3 (T.map M.subtype) := CFSG.SectionRank.isElemAbelian_map hTel _
      have hcard : Nat.card (T.map M.subtype) = 3 ^ CFSG.Open.pRank 3
          (Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) := by
        rw [Subgroup.card_map_of_injective M.subtype_injective, hTcard, hE'card]
      have := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (hTG T hTC) hTGel hcard
      omega
    · have hA3 : CFSG.Open.pRank 3 A = 3 := (h1111 h).2.1
      have h1 : CFSG.Open.pRank 3 A ≤ CFSG.Open.pRank 3 ((A.subgroupOf M).map π) :=
        l119_pRank_image_ge Nat.prime_three hAM hAel
      have hle : (A.subgroupOf M).map π ≤ Subgroup.centralizer ({π a'} : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
        rintro _ ⟨x, hx, rfl⟩
        have hxa : (x : G) * a = a * (x : G) :=
          congrArg Subtype.val (hAel.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩ ⟨a, ha⟩)
        have hxa' : x * a' = a' * x := Subtype.ext hxa
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hxa']
      have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hle
      omega
  · have hS := hSolv G m 3 B M E A a K h rfl
    have heq : (M ⊓ Cg a).subgroupOf M = Subgroup.centralizer ({a'} : Set ↥M) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hx).2)
      · intro hx
        exact Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hx)⟩
    have hS' : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({a'} : Set ↥M)) := by
      rw [← heq]
      exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe inf_le_left).symm hS
    rw [hcent]
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_map π hS'

theorem ddKey_le_of {p : ℕ} {E A E' A' : Subgroup G}
    (h1 : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p (E' ⊓ A'))
    (h2 : min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) ≤
      min (CFSG.Open.pRank p E') (CFSG.Open.pRank p A'))
    (h3 : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p E') (h4 : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p A')
    (h5 : IsPGroup p ↥(E' ⊔ A')) : ddKey p E A ≤ ddKey p E' A' := by
  classical
  unfold ddKey
  have h6 : (if IsPGroup p ↥(E ⊔ A) then 1 else 0) ≤ (if IsPGroup p ↥(E' ⊔ A') then 1 else 0) := by
    rw [if_pos h5]
    split_ifs <;> norm_num
  exact Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h1, Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h2,
    Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h3, Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h4, h6⟩)⟩)⟩)⟩)

theorem plane_of_commute {Y : Type} [Group Y] [Finite Y] {w z : Y} (hw3 : w ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hwz : w * z = z * w) (hwnz : w ∉ Subgroup.zpowers z) :
    IsElemAbelian 3 (Subgroup.zpowers w ⊔ Subgroup.zpowers z) ∧
      Nat.card ↥(Subgroup.zpowers w ⊔ Subgroup.zpowers z) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw1 : w ≠ 1 := fun h1 => hwnz (h1 ▸ Subgroup.one_mem _)
  have hc : ∀ x ∈ Subgroup.zpowers w, ∀ y ∈ Subgroup.zpowers z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (show Commute w z from hwz) i j)).eq
  have hcz : Subgroup.zpowers w ≤ Subgroup.centralizer (Subgroup.zpowers z : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm
  have hel := isElemAbelian_sup_of_commute (CFSG.Open.isElemAbelian_zpowers hw3)
    (CFSG.Open.isElemAbelian_zpowers hz3) hcz
  have hcz3 : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1]
  have hcw3 : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hw3 hw1]
  have hdisj : Subgroup.zpowers w ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    obtain ⟨huw, huz⟩ := Subgroup.mem_inf.1 hu
    by_contra hu1
    have hu1' : u ≠ 1 := fun h1 => hu1 (by rw [h1]; exact Subgroup.one_mem _)
    have hu3 : u ^ 3 = 1 := (CFSG.Open.isElemAbelian_zpowers hw3).2 u huw
    have hcu : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, orderOf_eq_prime hu3 hu1']
    have h1 : Subgroup.zpowers u = Subgroup.zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huw) (by rw [hcu, hcw3])
    have h2 : Subgroup.zpowers u = Subgroup.zpowers z :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huz) (by rw [hcu, hcz3])
    exact hwnz (by rw [← h2, h1]; exact Subgroup.mem_zpowers w)
  refine ⟨hel, ?_⟩
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.card_sup_eq_mul_of_commute hc hdisj, hcw3, hcz3]

theorem comm_of_card_dvd {Y : Type} [Group Y] [Finite Y] (hP : IsPGroup 3 Y)
    (hdvd : Nat.card Y ∣ 20160) : ∀ x y : Y, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h27 : 3 ^ 3 ∣ 20160 := (pow_dvd_pow 3 (by omega)).trans (hk ▸ hdvd)
    norm_num at h27
  interval_cases k
  · intro x y
    have : Subsingleton Y := by
      rw [pow_zero] at hk
      exact (Nat.card_eq_one_iff_unique.1 hk).1
    exact Subsingleton.elim _ _
  · haveI : IsCyclic Y := isCyclic_of_prime_card (p := 3) (by rw [hk, pow_one])
    intro x y
    exact IsCyclic.commGroup.mul_comm x y
  · exact IsPGroup.commutative_of_card_eq_prime_sq hk

@[expose] def InputAutL34Order27 : Prop :=
  ∀ (X : Type) [Group X], IsLThreeFour X → ∀ P : Subgroup (MulAut X), IsPGroup 3 ↥P → Nat.card P ≤ 27

theorem lemma1113C4Claim_of_inputs (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (hI : InputAutL34Order27) : Lemma1113C4Claim := by
  intro G _ _ m p B M E A a K h hp S hSC hS3
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := Inputs1114.cfg_of h1111 h119 h1112 h
  have hSN : S ≤ Subgroup.normalizer (K : Set G) := hSC.trans hcfg.cg_le_normalizer
  let f : ↥S →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hSN)
  have hcard : Nat.card S = Nat.card f.ker * Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hr : Nat.card f.range ≤ 27 :=
    hI _ (h1111 h).2.2 _ (hS3.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hk : Nat.card f.ker ≤ 3 := by
    have hsyl := ((h1112 h).1).1
    have hle : f.ker.map S.subtype ≤ centBar 3 (Cg a) K := by
      rintro _ ⟨x, hx, rfl⟩
      unfold centBar
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(x : G), hSN x.2⟩, MonoidHom.mem_ker.1 hx, rfl⟩,
        hSC x.2⟩
    have h1 := Lemma1112b.card_le_of_isSylowIn hsyl hle ((hS3.to_subgroup f.ker).map S.subtype)
    rw [Subgroup.card_map_of_injective S.subtype_injective] at h1
    have ha3 : a ^ 3 = 1 := h.pair.1.2.1.1.1.2.1.2 a h.ha.1
    have h3 : Nat.card (Subgroup.zpowers a) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime ha3 h.ha.2]
    omega
  rw [hcard]
  calc Nat.card f.ker * Nat.card f.range ≤ 3 * 27 := Nat.mul_le_mul hk hr
    _ = 3 ^ 4 := by norm_num

end Chev

section Solv

open CFSG.HallHigman (IsPSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
  (isPSolvable_of_le isPSolvable_map isPSolvable_of_normal)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal (isPSolvable_of_mulEquiv)

theorem isPSolvable_of_isPGroup_three' {X : Type} [Group X] [Finite X] (h : IsPGroup 3 X) :
    IsPSolvable 3 X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro H _ T _ hs
  left
  have hQ : IsPGroup 3 (↥H ⧸ T) := ((h.to_subgroup H).to_quotient T)
  haveI := hs
  have hcen : Subgroup.center (↥H ⧸ T) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥H ⧸ T)) with hb | ht
    · exact absurd hb ((Subgroup.nontrivial_iff_ne_bot _).mp hQ.center_nontrivial)
    · exact ht
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a := fun a b =>
    (Subgroup.mem_center_iff.mp (hcen ▸ Subgroup.mem_top b) a)
  haveI : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hprime : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  rw [Subgroup.index_eq_card, hk]
  rw [hk] at hprime
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero] at hprime
    exact absurd hprime Nat.not_prime_one
  · rcases hprime.eq_one_or_self_of_dvd 3 (dvd_pow_self 3 hkpos.ne') with h1 | h1
    · omega
    · exact h1.symm

theorem isPSolvable_of_coprime_three' {X : Type} [Group X] [Finite X]
    (h : Nat.Coprime 3 (Nat.card X)) : IsPSolvable 3 X := by
  intro H _ T _ _
  right
  exact Nat.Coprime.coprime_dvd_right ((T.index_dvd_card).trans (Subgroup.card_subgroup_dvd_card H)) h

theorem isPSolvable_of_isSolvable' {X : Type*} [Group X] (hX : Group.IsSolvable X) :
    IsPSolvable 3 X := by
  intro H _ T _ hs
  have := hX
  have := hs
  have hcomm : ∀ a b : ↥H ⧸ T, a * b = b * a :=
    (IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance
  have : IsMulCommutative (↥H ⧸ T) := ⟨⟨hcomm⟩⟩
  have hq : (Nat.card (↥H ⧸ T)).Prime := Group.is_simple_iff_prime_card.mp hs
  change Nat.card (↥H ⧸ T) = 3 ∨ Nat.Coprime 3 (Nat.card (↥H ⧸ T))
  by_cases h : Nat.card (↥H ⧸ T) = 3
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes Nat.prime_three hq).mpr (Ne.symm h))

theorem isPSolvable_of_inf_inner {X : Type} [Group X] (hX : IsLThreeFour X) {H : Subgroup (MulAut X)}
    (hH : IsPSolvable 3 ↥(H ⊓ innerAut X)) : IsPSolvable 3 ↥H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXc : Nat.card X = 20160 := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hX
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hXc]; norm_num)
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  haveI : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  haveI := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.linear_higher_schreier
    (K := k) (n := 3) le_rfl).2
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv φ.symm
  let f : ↥H →* CFSG.ComponentClassification.OuterAutomorphisms.Outer X :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X)).comp H.subtype
  have hker : IsPSolvable 3 ↥f.ker := by
    have hle : f.ker.map H.subtype ≤ H ⊓ innerAut X := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have : QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner X) (x : MulAut X) = 1 :=
        MonoidHom.mem_ker.1 hx
      have h2 : (x : MulAut X) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X :=
        (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner X) _).1 this
      exact h2
    have h1 : IsPSolvable 3 ↥(f.ker.map H.subtype) := isPSolvable_of_le hH hle
    exact isPSolvable_of_mulEquiv (f.ker.equivMapOfInjective H.subtype H.subtype_injective).symm h1
  have hran : IsPSolvable 3 ↥f.range := isPSolvable_of_isSolvable' inferInstance
  exact isPSolvable_of_normal f.ker hker
    (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange f).symm hran)

@[expose] def InputL34SylowNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S : Subgroup G), IsLThreeFour (barOf 3 K) → S ≤ K →
    IsPGroup 3 ↥S → Nat.card S = 9 →
    (∀ H : Subgroup G, GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer (S : Set G) ⊓ K) ≤ H → H ≤ K →
      H = K ∨ H = GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer (S : Set G) ⊓ K)) ∧
    IsPSolvable 3 ↥(Subgroup.normalizer (S : Set G) ⊓ K)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_core {K : Subgroup G} : K ≤ Subgroup.normalizer ((GLAPPrimeCoreOf 3 K : Subgroup G) : Set G) := by
  intro y hy
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hy
  rw [Subgroup.mem_normalizer_iff]
  intro o
  constructor
  · exact fun ho => Inputs1114.conj_mem_core hyN ho
  · intro ho
    have := Inputs1114.conj_mem_core (Subgroup.inv_mem _ hyN) ho
    simpa [mul_assoc] using this

theorem barAut_core_eq_one {K : Subgroup G} {o : G} (ho : o ∈ GLAPPrimeCoreOf 3 K)
    (hoN : o ∈ Subgroup.normalizer (K : Set G)) : barAut 3 K ⟨o, hoN⟩ = 1 := by
  obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.1 ho
  have e : (⟨K.subtype o', hoN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨(o' : G), Subgroup.le_normalizer o'.2⟩ := rfl
  rw [e, l119_barAut_eq_conj (p := 3) o']
  have : (QuotientGroup.mk o' : ↥K ⧸ GLAPPrimeCore 3 ↥K) = 1 := (QuotientGroup.eq_one_iff o').2 ho'
  rw [this, map_one]

theorem lemma1113SolvClaim_of_inputs (h1111 : Lemma1111Statement) (h1112 : Lemma1112Statement)
    (h119 : Lemma119Statement) (h111 : Prop111Statement) (hI : InputL34SylowNormalizer) :
    Lemma1113SolvClaim := by
  intro G _ _ m p B M E A a K h hp
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := Inputs1114.cfg_of h1111 h119 h1112 h
  have hSec : Sec11 G m 3 B M E A := h.toCex117Base.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hK : GLAPComponent 3 (Cg a) K := h.hK
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have haM : a ∈ M := hAM ha
  have hCN : Cg a ≤ Subgroup.normalizer (K : Set G) := hcfg.cg_le_normalizer
  have hOM : GLAPPrimeCoreOf 3 (Cg a) ≤ M := h111 hSec ha ha1
  have hsyl : IsSylowIn 3 (centBar 3 (Cg a) K) (Subgroup.zpowers a) := ((h1112 h).1).1
  set C₀ := centBar 3 (Cg a) K with hC₀
  have hC₀C : C₀ ≤ Cg a := inf_le_right
  set P₀ : Subgroup ↥C₀ := (Subgroup.zpowers a).subgroupOf C₀ with hP₀
  have hP₀s := isSylowIn_top_subgroupOf hsyl
  let P : Sylow 3 ↥C₀ :=
    { toSubgroup := P₀, isPGroup' := hP₀s.2.1, is_maximal' := fun {Q} hQ hle => hP₀s.2.2 Q le_top hQ hle }
  have hcentral : ∀ x ∈ P₀, ∀ g : ↥C₀, g * x = x * g := by
    intro x hx g
    apply Subtype.ext
    have hxa : (x : G) ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.1 hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hxa
    have hga : (g : G) * a = a * g := Subgroup.mem_centralizer_singleton_iff.1 (hC₀C g.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi]
    exact ((show Commute (g : G) a from hga).zpow_right i).eq
  have hNC : Subgroup.normalizer ((P : Subgroup ↥C₀) : Set ↥C₀) ≤
      Subgroup.centralizer ((P : Subgroup ↥C₀) : Set ↥C₀) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hcentral x hx g).symm
  obtain ⟨K₀, hK₀n, hK₀3, hK₀idx, -, -, -, hsup, -, -, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hNC
  have hK₀c : Nat.Coprime 3 (Nat.card K₀) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hK₀3
  have hC₀n : (C₀.subgroupOf (Cg a)).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hcfg.centBar_conj g.2 hn
  have hC₀sub : IsSubnormal C₀ (Cg a) := IsSubnormal.step hC₀C hC₀n (IsSubnormal.refl _)
  have hO₀ : GLAPPrimeCoreOf 3 C₀ ≤ M := (glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hC₀sub).trans hOM
  have hK₀O : K₀.map C₀.subtype ≤ GLAPPrimeCoreOf 3 C₀ := by
    apply Subgroup.map_mono
    exact le_sSup (s := {N : Subgroup ↥C₀ | N.Normal ∧ Nat.Coprime 3 (Nat.card N)}) ⟨hK₀n, hK₀c⟩
  have hC₀M : C₀ ≤ M := by
    intro c hc
    have hmem : (⟨c, hc⟩ : ↥C₀) ∈ K₀ ⊔ (P : Subgroup ↥C₀) := by rw [hsup]; exact Subgroup.mem_top _
    have h1 : c ∈ (K₀ ⊔ (P : Subgroup ↥C₀)).map C₀.subtype := ⟨⟨c, hc⟩, hmem, rfl⟩
    rw [Subgroup.map_sup] at h1
    refine (sup_le (hK₀O.trans hO₀) ?_) h1
    rintro _ ⟨x, hx, rfl⟩
    have : (x : G) ∈ Subgroup.zpowers a := Subgroup.mem_subgroupOf.1 hx
    exact (Subgroup.zpowers_le.2 haM) this
  have hC₀s : IsPSolvable 3 ↥C₀ := by
    haveI := hK₀n
    have hq3 : IsPGroup 3 (↥C₀ ⧸ K₀) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
      refine IsPGroup.of_card (n := k) ?_
      rw [← Subgroup.index, hK₀idx, hk]
    exact isPSolvable_of_normal K₀ (isPSolvable_of_coprime_three' hK₀c) (isPSolvable_of_isPGroup_three' hq3)
  have hA0el : IsElemAbelian 3 (E ⊓ A) := isElemAbelian_mono hcfg.hAel inf_le_right
  have hA0p : IsPGroup 3 ↥(E ⊓ A) := Lemma118T.isPGroup_of_isElemAbelian hA0el
  have hNA0 : Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    l1110_normalizer_A0_le h.pair.1.1 (h119 h).1
  have hOK : GLAPPrimeCoreOf 3 K ≤ M :=
    (glaPPrimeCoreOf_le_of_isSubnormal (by norm_num) hK.2.1).trans hOM
  have hOKK : GLAPPrimeCoreOf 3 K ≤ K := Subgroup.map_subtype_le _
  obtain ⟨hmax, hsolvN⟩ := hI G K (E ⊓ A) hcfg.hL hcfg.hA0K hA0p hcfg.hA0card
  have hMK : M ⊓ K = GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ⊓ K) := by
    rcases hmax (M ⊓ K) (le_inf (sup_le hOK (inf_le_left.trans hNA0)) (sup_le hOKK inf_le_right))
      inf_le_right with h1 | h1
    · exact absurd (by rw [← h1]; exact inf_le_left) h.notM
    · exact h1
  set X : Subgroup G := M ⊓ Cg a with hX
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans hCN
  let f : ↥X →* MulAut (barOf 3 K) := (barAut 3 K).comp (Subgroup.inclusion hXN)
  have hker : IsPSolvable 3 ↥f.ker := by
    have hle : f.ker.map X.subtype ≤ C₀ := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hC₀]
      unfold centBar
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(x : G), hXN x.2⟩, MonoidHom.mem_ker.1 hx, rfl⟩,
        (inf_le_right : X ≤ Cg a) x.2⟩
    exact isPSolvable_of_mulEquiv (f.ker.equivMapOfInjective X.subtype X.subtype_injective).symm
      (isPSolvable_of_le hC₀s hle)
  set NK : Subgroup G := Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ⊓ K with hNK
  have hNKN : NK ≤ Subgroup.normalizer (K : Set G) := inf_le_right.trans (fun k hk => Subgroup.le_normalizer hk)
  set Y₀ : Subgroup (MulAut (barOf 3 K)) := (NK.subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut 3 K)
    with hY₀
  have hY₀s : IsPSolvable 3 ↥Y₀ :=
    isPSolvable_map (barAut 3 K)
      (isPSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNKN).symm hsolvN)
  have hrange_inn : f.range ⊓ innerAut (barOf 3 K) ≤ Y₀ := by
    rintro φ ⟨⟨x, rfl⟩, hφ⟩
    obtain ⟨q, hq⟩ := hφ
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have hkN : (k : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer k.2
    have hbk : barAut 3 K ⟨k, hkN⟩ = MulAut.conj (QuotientGroup.mk k : ↥K ⧸ GLAPPrimeCore 3 ↥K) :=
      l119_barAut_eq_conj (p := 3) k
    have hfx : f x = barAut 3 K ⟨(x : G), hXN x.2⟩ := rfl
    have h1 : barAut 3 K (⟨k, hkN⟩⁻¹ * ⟨(x : G), hXN x.2⟩) = 1 := by
      rw [map_mul, map_inv, hbk, ← hfx]
      change (MulAut.conj (QuotientGroup.mk k : ↥K ⧸ GLAPPrimeCore 3 ↥K))⁻¹ * f x = 1
      rw [← hq, inv_mul_cancel]
    have hkxC : (k : G)⁻¹ * x ∈ Cg a :=
      (Cg a).mul_mem ((Cg a).inv_mem (hK.1 k.2)) ((inf_le_right : X ≤ Cg a) x.2)
    have hkx : (k : G)⁻¹ * x ∈ C₀ := by
      rw [hC₀]
      unfold centBar
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨_, MonoidHom.mem_ker.2 h1, rfl⟩, hkxC⟩
    have hkM : (k : G) ∈ M := by
      have := M.mul_mem ((inf_le_left : X ≤ M) x.2) (M.inv_mem (hC₀M hkx))
      simpa using this
    have hkMK : (k : G) ∈ NK ⊔ GLAPPrimeCoreOf 3 K := by
      rw [sup_comm, hNK, ← hMK]
      exact ⟨hkM, k.2⟩
    obtain ⟨n, hn, o, ho, hno⟩ :=
      Inputs1114.exists_mul_of_mem_sup (inf_le_right.trans le_normalizer_core) hkMK
    refine ⟨⟨n, hNKN hn⟩, Subgroup.mem_subgroupOf.2 hn, ?_⟩
    have hoN : o ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer (hOKK ho)
    have hk_eq : (⟨k, hkN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨n, hNKN hn⟩ * ⟨o, hoN⟩ :=
      Subtype.ext hno.symm
    rw [← hq, ← hbk, hk_eq, map_mul, barAut_core_eq_one ho hoN, mul_one]
  have hran : IsPSolvable 3 ↥f.range :=
    isPSolvable_of_inf_inner hcfg.hL (isPSolvable_of_le hY₀s hrange_inn)
  exact isPSolvable_of_normal f.ker hker
    (isPSolvable_of_mulEquiv (QuotientGroup.quotientKerEquivRange f).symm hran)

end Solv

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims11x
