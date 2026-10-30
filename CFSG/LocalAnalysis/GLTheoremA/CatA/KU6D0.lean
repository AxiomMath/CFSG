module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6L2
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6T9
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.GLTheoremA.I142N (GLALayer_eq_sSup le_GLALayer GLALayer_le_of GLALayer_le)
open scoped commutatorElement

namespace KU6D0

variable {G : Type} [Group G]

theorem not_dvd_card_O [Finite G] (J : Subgroup G) : ¬ 3 ∣ Nat.card (GLAPPrimeCoreOf 3 J) :=
  not_dvd_card_glaPPrimeCoreOf Nat.prime_three J

theorem O_conj_mem [Finite G] (J : Subgroup G) {g x : G} (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hx : x ∈ GLAPPrimeCoreOf 3 J) : g * x * g⁻¹ ∈ GLAPPrimeCoreOf 3 J :=
  (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf 3 J hg) x).1 hx

theorem O_le (J : Subgroup G) : GLAPPrimeCoreOf 3 J ≤ J := by
  unfold GLAPPrimeCoreOf
  exact Subgroup.map_subtype_le _

theorem exists_cover [Finite G] {J D : Subgroup G} (hD : D ≤ Subgroup.normalizer (J : Set G))
    (hDe : IsElemAbelian 3 D) (hcomm : ∀ d ∈ D, ∀ j ∈ J, ⁅j, d⁆ ∈ GLAPPrimeCoreOf 3 J)
    {j : G} (hj : j ∈ J) :
    ∃ c ∈ J ⊓ Subgroup.centralizer (D : Set G), c⁻¹ * j ∈ GLAPPrimeCoreOf 3 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Nn : Subgroup ↥(Subgroup.normalizer (J : Set G)) :=
    (GLAPPrimeCoreOf 3 J).subgroupOf (Subgroup.normalizer (J : Set G))
  have hOn : ∀ g ∈ Subgroup.normalizer (J : Set G), ∀ x ∈ GLAPPrimeCoreOf 3 J,
      g * x * g⁻¹ ∈ GLAPPrimeCoreOf 3 J := fun g hg x hx => O_conj_mem J hg hx
  haveI : Nn.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hOn g g.2 _ hn⟩
  have hOle : GLAPPrimeCoreOf 3 J ≤ Subgroup.normalizer (J : Set G) :=
    (O_le J).trans Subgroup.le_normalizer
  have hNcard : ¬ 3 ∣ Nat.card Nn := by
    have e : Nat.card Nn = Nat.card ↥(GLAPPrimeCoreOf 3 J) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv
    rw [e]
    exact not_dvd_card_O J
  let Dg : Subgroup ↥(Subgroup.normalizer (J : Set G)) := D.subgroupOf (Subgroup.normalizer (J : Set G))
  have hDg : IsPGroup 3 ↥Dg := by
    intro g
    refine ⟨1, ?_⟩
    have hg : ((g : ↥(Subgroup.normalizer (J : Set G))) : G) ∈ D := g.2
    have h3 : ((g : ↥(Subgroup.normalizer (J : Set G))) : G) ^ 3 = 1 := hDe.2 _ hg
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    simpa using h3
  have hcent := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3) (N := Nn) hNcard hDg
  let γ : ↥(Subgroup.normalizer (J : Set G)) := ⟨j, Subgroup.le_normalizer hj⟩
  have hγ : QuotientGroup.mk' Nn γ ∈ Subgroup.centralizer
      ((Dg.map (QuotientGroup.mk' Nn) : Subgroup (↥(Subgroup.normalizer (J : Set G)) ⧸ Nn)) :
        Set (↥(Subgroup.normalizer (J : Set G)) ⧸ Nn)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨d', hd', rfl⟩ := Subgroup.mem_map.1 hy
    have hd'D : ((d' : ↥(Subgroup.normalizer (J : Set G))) : G) ∈ D := hd'
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq.2
    rw [Subgroup.mem_subgroupOf]
    have hc := hcomm ((d' : ↥(Subgroup.normalizer (J : Set G))) : G)⁻¹ (D.inv_mem hd'D)
      j⁻¹ (J.inv_mem hj)
    simpa [γ, commutatorElement_def, mul_assoc] using hc
  rw [hcent] at hγ
  obtain ⟨c, hc, hceq⟩ := Subgroup.mem_map.1 hγ
  have hcO : (c : ↥(Subgroup.normalizer (J : Set G)))⁻¹ * γ ∈ Nn := QuotientGroup.eq.1 hceq
  rw [Subgroup.mem_subgroupOf] at hcO
  have hcj : ((c : ↥(Subgroup.normalizer (J : Set G))) : G)⁻¹ * j ∈ GLAPPrimeCoreOf 3 J := by
    simpa [γ] using hcO
  have hcJ : ((c : ↥(Subgroup.normalizer (J : Set G))) : G) ∈ J := by
    have h1 : j * (((c : ↥(Subgroup.normalizer (J : Set G))) : G)⁻¹ * j)⁻¹ ∈ J :=
      J.mul_mem hj (J.inv_mem ((O_le J) hcj))
    simpa using h1
  refine ⟨((c : ↥(Subgroup.normalizer (J : Set G))) : G), ⟨hcJ, ?_⟩, hcj⟩
  refine Subgroup.mem_centralizer_iff.2 fun d hd => ?_
  have hdN : d ∈ Subgroup.normalizer (J : Set G) := hD hd
  have hdg : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (J : Set G))) ∈ Dg := by
    show d ∈ D
    exact hd
  have := Subgroup.mem_centralizer_iff.1 hc _ hdg
  have h2 := congrArg Subtype.val this
  simpa using h2


theorem ker_le_center [Finite G] {J K : Subgroup G} (hKJ : K ≤ J) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (h3K : 3 ∣ Nat.card ↥K) {n : ↥K} (hn : chevQuotHom 3 J (Subgroup.inclusion hKJ n) = 1) :
    n ∈ Subgroup.center ↥K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let M : Subgroup ↥K := (GLAPPrimeCoreOf 3 J).subgroupOf K
  haveI hMn : M.Normal := ⟨fun m hm g => by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have hgJ : (g : G) ∈ J := hKJ g.2
    simpa using O_conj_mem J (Subgroup.le_normalizer hgJ) hm⟩
  have hMt : M ≠ ⊤ := by
    intro h
    have hKO : K ≤ GLAPPrimeCoreOf 3 J := by
      intro x hx
      have hxM : (⟨x, hx⟩ : ↥K) ∈ M := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 hxM
    have h1 : Nat.card ↥K ∣ Nat.card ↥(GLAPPrimeCoreOf 3 J) := Subgroup.card_dvd_of_le hKO
    exact not_dvd_card_O J (dvd_trans h3K h1)
  have hMc : M ≤ Subgroup.center ↥K := le_center_of_normal_of_isQuasisimple hKq hMn hMt
  have hcomm : ∀ k : ↥K, ⁅n, k⁆ ∈ Subgroup.center ↥K := by
    intro k
    apply hMc
    rw [Subgroup.mem_subgroupOf]
    have hz : pQuotHom 3 J (Subgroup.inclusion hKJ n) ∈ Subgroup.center (PQuot 3 J) :=
      (QuotientGroup.eq_one_iff _).1 hn
    have hc : pQuotHom 3 J (Subgroup.inclusion hKJ ⁅n, k⁆) = 1 := by
      rw [map_commutatorElement (Subgroup.inclusion hKJ) n k, map_commutatorElement (pQuotHom 3 J),
        commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 hz _).symm
    have hmem : (Subgroup.inclusion hKJ ⁅n, k⁆ : ↥J) ∈ GLAPPrimeCore 3 ↥J := by
      have h0 : (Subgroup.inclusion hKJ ⁅n, k⁆ : ↥J) ∈ (pQuotHom 3 J).ker := hc
      rwa [ker_pQuotHom] at h0
    exact (chev_mem_glaPPrimeCoreOf_iff (hKJ ⁅n, k⁆.2)).2 hmem
  have hmul : ∀ a b : ↥K, ⁅n, a * b⁆ = ⁅n, a⁆ * ⁅n, b⁆ := by
    intro a b
    rw [commutatorElement_mul_right]
    congr 1
    rw [Subgroup.mem_center_iff.1 (hcomm b) a, mul_assoc, mul_inv_cancel, mul_one]
  let f : ↥K →* ↥(Subgroup.center ↥K) :=
    { toFun := fun k => ⟨⁅n, k⁆, hcomm k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ⁅n, a * b⁆ = ⁅n, a⁆ * ⁅n, b⁆
        exact hmul a b) }
  have hker : (⊤ : Subgroup ↥K) ≤ f.ker := by
    have h1 : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) ≤ f.ker := by
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement f a b, commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (Subgroup.mem_center_iff.1 (f b).2 (f a))
    rw [show (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ from hKq.1] at h1
    exact h1
  have hcn : ∀ k : ↥K, ⁅n, k⁆ = 1 := by
    intro k
    have := congrArg Subtype.val (MonoidHom.mem_ker.1 (hker (Subgroup.mem_top k)))
    exact this
  refine Subgroup.mem_center_iff.2 fun k => ?_
  exact (commutatorElement_eq_one_iff_mul_comm.1 (hcn k)).symm


theorem exists_nontrivial [Finite G] (hb : CatDistinct.OrderBridge) {X J D K : Subgroup G}
    (hX : GLAPComponent 3 X J) (hJ6 : catalogIs (PSimple 3 J) S9.isU6two)
    (hD : D ≤ Subgroup.normalizer (J : Set G)) (hDe : IsElemAbelian 3 D)
    (hK : K = GLALayer (J ⊓ Subgroup.centralizer (D : Set G)))
    (hKL2 : catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isL2eight) :
    ∃ d : G, ∃ hd : d ∈ D, chevAut 3 J ⟨d, hD hd⟩ ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hall
  push Not at hall
  set H : Subgroup G := J ⊓ Subgroup.centralizer (D : Set G) with hHdef
  have hKH : K ≤ H := by rw [hK]; exact GLALayer_le _
  have hKJ : K ≤ J := hKH.trans inf_le_left
  have hcm : ∀ d ∈ D, ∀ j ∈ J, ⁅j, d⁆ ∈ GLAPPrimeCoreOf 3 J := by
    intro d hd j hj
    have hc := (chevAut_eq_one_iff Nat.prime_three hX (hD hd)).1 (hall d hd)
    exact (mem_centModSubgroup.1 (centMod_iff.1 hc)).2 j hj
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hX
  have hKperf : Group.IsPerfect ↥K := by rw [hK]; exact glaLayer_perfect _
  obtain ⟨hKs, hK504⟩ := catL2eight_simple_card hKL2
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hKperf.1, hKs⟩
  have h3K : 3 ∣ Nat.card ↥K := by
    have hidx : Subgroup.index (Subgroup.center ↥K) = 504 := hK504
    rw [← Subgroup.card_mul_index (Subgroup.center ↥K), hidx]
    exact Dvd.dvd.mul_left (by norm_num) _
  have h504K : 504 ∣ Nat.card ↥K := by
    have hidx : Subgroup.index (Subgroup.center ↥K) = 504 := hK504
    rw [← Subgroup.card_mul_index (Subgroup.center ↥K), hidx]
    exact Dvd.dvd.mul_left (dvd_refl _) _
  have hHQ : ∀ q : PQuot 3 J, ∃ h : ↥J, (h : G) ∈ H ∧ pQuotHom 3 J h = q := by
    intro q
    obtain ⟨j', rfl⟩ := pQuotHom_surjective 3 J q
    obtain ⟨c, hcH, hco⟩ := exists_cover hD hDe hcm j'.2
    have hcJ : c ∈ J := (Subgroup.mem_inf.1 hcH).1
    exact ⟨⟨c, hcJ⟩, hcH, (pQuot_mk_eq_mk_iff _ _).2 hco⟩
  have hconj : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    have key := glaLayer_conj_le (J ⊓ Subgroup.centralizer (D : Set G)) hh
    rw [← hK] at key
    have := key (Subgroup.mem_map_of_mem _ hk)
    simpa using this
  let fK : ↥K →* PQuot 3 J := (pQuotHom 3 J).comp (Subgroup.inclusion hKJ)
  have hfK : ∀ k : ↥K, fK k = pQuotHom 3 J (Subgroup.inclusion hKJ k) := fun k => rfl
  have hKbar : fK.range.Normal := ⟨fun x hx g => by
    obtain ⟨k, rfl⟩ := hx
    obtain ⟨h, hhH, hh⟩ := hHQ g
    refine MonoidHom.mem_range.2 ⟨⟨(h : G) * k * (h : G)⁻¹, hconj _ hhH _ k.2⟩, ?_⟩
    have e : Subgroup.inclusion hKJ ⟨(h : G) * k * (h : G)⁻¹, hconj _ hhH _ k.2⟩ =
        h * Subgroup.inclusion hKJ k * h⁻¹ := Subtype.ext (by simp)
    rw [hfK, e, map_mul, map_mul, map_inv, hh]
    rfl⟩
  by_cases hT : fK.range = ⊤
  ·
    let φ : ↥K →* PSimple 3 J := (chevQuotHom 3 J).comp (Subgroup.inclusion hKJ)
    have hφs : Function.Surjective φ := by
      intro s
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 J)) s
      have hq : q ∈ fK.range := by rw [hT]; exact Subgroup.mem_top _
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hq
      exact ⟨k, by simp only [φ, MonoidHom.comp_apply, chevQuotHom, MonoidHom.coe_comp,
        Function.comp_apply, QuotientGroup.mk'_apply]; rw [← hk, hfK]⟩
    have hker : φ.ker = Subgroup.center ↥K := by
      apply le_antisymm
      · intro n hn
        exact ker_le_center hKJ hKq h3K (MonoidHom.mem_ker.1 hn)
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hzc : fK z ∈ Subgroup.center (PQuot 3 J) := by
          rw [Subgroup.mem_center_iff]
          intro q
          have hq : q ∈ fK.range := by rw [hT]; exact Subgroup.mem_top _
          obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hq
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz k]
        show QuotientGroup.mk' (Subgroup.center (PQuot 3 J)) (fK z) = 1
        exact (QuotientGroup.eq_one_iff _).2 hzc
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφs
    have hcard : Nat.card (PSimple 3 J) = 504 := by
      rw [← Nat.card_congr e.toEquiv]
      rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv]
      exact hK504
    have hcardS := CatDistinct.card_isU6two hb hJ6
    omega
  ·
    have hcen : fK.range ≤ Subgroup.center (PQuot 3 J) := le_center_of_normal_of_isQuasisimple hQ hKbar hT
    have htop : (⊤ : Subgroup ↥K) ≤ fK.ker := by
      have h1 : (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) ≤ fK.ker := by
        refine Subgroup.commutator_le.2 fun a _ b _ => ?_
        rw [MonoidHom.mem_ker, map_commutatorElement fK a b, commutatorElement_eq_one_iff_mul_comm]
        have ha := hcen (MonoidHom.mem_range.2 ⟨a, rfl⟩)
        exact (Subgroup.mem_center_iff.1 ha (fK b)).symm
      rw [show (⁅(⊤ : Subgroup ↥K), ⊤⁆ : Subgroup ↥K) = ⊤ from hKq.1] at h1
      exact h1
    have hKO : K ≤ GLAPPrimeCoreOf 3 J := by
      intro x hx
      have hk : fK ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.1 (htop (Subgroup.mem_top _))
      rw [hfK] at hk
      have hmem : (Subgroup.inclusion hKJ ⟨x, hx⟩ : ↥J) ∈ GLAPPrimeCore 3 ↥J := by
        have h0 : (Subgroup.inclusion hKJ ⟨x, hx⟩ : ↥J) ∈ (pQuotHom 3 J).ker := hk
        rwa [ker_pQuotHom] at h0
      exact (chev_mem_glaPPrimeCoreOf_iff (hKJ hx)).2 hmem
    have h1 : Nat.card ↥K ∣ Nat.card ↥(GLAPPrimeCoreOf 3 J) := Subgroup.card_dvd_of_le hKO
    exact not_dvd_card_O J (dvd_trans (dvd_trans (by norm_num) h504K) h1)


theorem u6d0_of_facts (hF : KU6CentL2eightFact) (hb : CatDistinct.OrderBridge) (G : Type) [Group G]
    [Finite G] : U6D0RankAt G := by
  intro J D₀ K hJX hJ6 hD0N hD0 hD0card hInn hK hKL2 A hAN hAC hA
  obtain ⟨X, hX⟩ := hJX
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d₀, hd₀, hα1⟩ := exists_nontrivial hb hX hJ6 hD0N hD0 hK hKL2
  have hKH : K ≤ J ⊓ Subgroup.centralizer (D₀ : Set G) := by rw [hK]; exact GLALayer_le _
  have hKJ : K ≤ J := hKH.trans inf_le_left
  have hKC : ∀ k ∈ K, ∀ d ∈ D₀, d * k = k * d := fun k hk d hd =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hKH hk)).2 d hd
  have hKperf : Group.IsPerfect ↥K := by rw [hK]; exact glaLayer_perfect _
  obtain ⟨hKs, hK504⟩ := catL2eight_simple_card hKL2
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hKperf.1, hKs⟩
  have h3K : 3 ∣ Nat.card ↥K := by
    have hidx : Subgroup.index (Subgroup.center ↥K) = 504 := hK504
    rw [← Subgroup.card_mul_index (Subgroup.center ↥K), hidx]
    exact Dvd.dvd.mul_left (by norm_num) _
  let ρ : ↥K →* PSimple 3 J := (chevQuotHom 3 J).comp (Subgroup.inclusion hKJ)
  have hρker : ∀ x ∈ ρ.ker, x ∈ Subgroup.center ↥K := fun x hx =>
    ker_le_center hKJ hKq h3K (MonoidHom.mem_ker.1 hx)
  have hd₀3 : d₀ ^ 3 = 1 := hD0.2 d₀ hd₀
  let α : MulAut (PSimple 3 J) := chevAut 3 J ⟨d₀, hD0N hd₀⟩
  have hα3 : α ^ 3 = 1 := chevAut_pow_eq_one 3 J (hD0N hd₀) hd₀3
  have hNfix : ρ.range ≤ fixSubgroup α := by
    rintro _ ⟨k, rfl⟩
    rw [mem_fixSubgroup]
    show chevAut 3 J ⟨d₀, hD0N hd₀⟩ (chevQuotHom 3 J (Subgroup.inclusion hKJ k)) =
      chevQuotHom 3 J (Subgroup.inclusion hKJ k)
    rw [chevAut_chevQuotHom]
    congr 1
    apply Subtype.ext
    rw [chev_coe_normalizerMonoidHom]
    show d₀ * (k : G) * d₀⁻¹ = (k : G)
    rw [hKC k k.2 d₀ hd₀]
    group
  let e1 := QuotientGroup.quotientKerEquivRange ρ
  let e2 : ↥K ⧸ ρ.ker →* ↥K ⧸ Subgroup.center ↥K :=
    QuotientGroup.map ρ.ker (Subgroup.center ↥K) (MonoidHom.id ↥K) (fun x hx => hρker x hx)
  let f : ↥ρ.range →* ↥K ⧸ Subgroup.center ↥K := e2.comp e1.symm.toMonoidHom
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥K) y
    refine ⟨⟨ρ k, MonoidHom.mem_range.2 ⟨k, rfl⟩⟩, ?_⟩
    have hk : e1.symm ⟨ρ k, MonoidHom.mem_range.2 ⟨k, rfl⟩⟩ = QuotientGroup.mk' ρ.ker k :=
      e1.symm_apply_eq.2 rfl
    show e2 (e1.symm ⟨ρ k, MonoidHom.mem_range.2 ⟨k, rfl⟩⟩) = _
    rw [hk]
    rfl
  have hcatM : catalogIs (↥ρ.range ⧸ f.ker) S10.isL2eight :=
    KU6T9.catalogIs_of_mulEquiv hKL2 (QuotientGroup.quotientKerEquivOfSurjective f hf)
  let AN : ↥A →* MulAut (PSimple 3 J) := (chevAut 3 J).comp (Subgroup.inclusion hAN)
  have hcommA : ∀ a b : ↥A, a * b = b * a := fun a b =>
    Subtype.ext (congrArg Subtype.val (hA.1.is_comm.comm a b))
  have hE_el : IsElemAbelian 3 AN.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut (PSimple 3 J)) * (y : MulAut (PSimple 3 J)) =
        (y : MulAut (PSimple 3 J)) * (x : MulAut (PSimple 3 J))
      rw [← ha, ← hb, ← map_mul, ← map_mul, hcommA a b]
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
      have h3 : a ^ 3 = 1 := Subtype.ext (hA.2 _ a.2)
      show AN a ^ 3 = 1
      rw [← map_pow, h3, map_one]
  have hE_c : AN.range ≤ Subgroup.centralizer ({α} : Set (MulAut (PSimple 3 J))) := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show α * AN a = AN a * α
    have hda : d₀ * (a : G) = (a : G) * d₀ := Subgroup.mem_centralizer_iff.1 (hAC a.2) d₀ hd₀
    show chevAut 3 J ⟨d₀, hD0N hd₀⟩ * chevAut 3 J (Subgroup.inclusion hAN a) =
      chevAut 3 J (Subgroup.inclusion hAN a) * chevAut 3 J ⟨d₀, hD0N hd₀⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hda
  have hE27 : Nat.card AN.range ≤ 3 ^ 3 :=
    hF (PSimple 3 J) hJ6 α hα3 hα1 ρ.range hNfix f.ker hcatM AN.range hE_el hE_c
  have he : AN.ker = (A ⊓ centModSubgroup 3 J).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h' : chevAut 3 J ⟨(x : G), hAN x.2⟩ = 1 := h
      exact ⟨x.2, centMod_iff.1 ((chevAut_eq_one_iff Nat.prime_three hX (hAN x.2)).1 h')⟩
    · rintro ⟨-, h⟩
      exact (chevAut_eq_one_iff Nat.prime_three hX (hAN x.2)).2 (centMod_iff.2 h)
  have hkerc : Nat.card AN.ker = Nat.card ↥(A ⊓ centModSubgroup 3 J) := by
    rw [he]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hsplit := Subgroup.card_ker_mul_card_range AN
  calc Nat.card A = Nat.card AN.ker * Nat.card AN.range := hsplit.symm
    _ ≤ Nat.card AN.ker * 3 ^ 3 := Nat.mul_le_mul_left _ hE27
    _ = 3 ^ 3 * Nat.card ↥(A ⊓ centModSubgroup 3 J) := by rw [hkerc, mul_comm]

end KU6D0

end CFSG.LocalAnalysis.GLTheoremA
