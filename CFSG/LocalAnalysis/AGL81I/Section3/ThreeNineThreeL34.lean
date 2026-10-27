module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineOrders
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineExclude
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineThreeFamilies
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Main
public import Certificates.Certificate2022
public import Certificates.Certificate465003
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DSylow
import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutD1Aut
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.StandardType.L34OvergroupSeven
import CFSG.LocalAnalysis.StandardType.SolvableOrSimpleDerivedSylow

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix c25GammaCl mem_c25Fix)
open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL scalars scalars_eq_center
  descendAut proj_surjective)
open CFSG.LocalAnalysis.GLTheoremB (IsLThreeFour IsSLThreeFour)

theorem exists_conj_eq_of_mulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) {m : ℕ}
    (hH : ∀ β : MulAut H, β ^ m = 1 → ∃ g, MulAut.conj g = β) {α : MulAut G}
    (hα : α ^ m = 1) : ∃ g, MulAut.conj g = α := by
  obtain ⟨g, hg⟩ := hH (MulAut.congr φ α) (by rw [← map_pow, hα, map_one])
  refine ⟨φ.symm g, (MulAut.congr φ).injective ?_⟩
  rw [← hg]
  ext x
  simp [MulAut.congr_apply]

theorem exists_conj_eq_projectiveSL {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {m : ℕ} (hm : Odd m) (hm3 : Nat.Coprime m 3) (β : MulAut (projectiveSL 3 k))
    (hβ : β ^ m = 1) : ∃ g, MulAut.conj g = β := by
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.Stage2.Signalizer.L46E.mem_Iaut_of_coprime_three hk
    (CFSG.GH74.GLS.Stage2.Signalizer.L46E.mem_linearAutGroup_of_odd_pow
      (CFSG.GH74.GLS.Stage2.Signalizer.L46E.ringAut_sq_of_card_four hk) hm hβ) hm3 hβ
  exact ⟨g, hg⟩

theorem exists_conj_eq_SL {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4) {m : ℕ}
    (hm : Odd m) (hm3 : Nat.Coprime m 3) (β : MulAut (Matrix.SpecialLinearGroup (Fin 3) k))
    (hβ : β ^ m = 1) : ∃ g, MulAut.conj g = β := by
  obtain ⟨p, hp⟩ := exists_conj_eq_projectiveSL hk hm hm3 (descendAut 3 k β)
    (by rw [← map_pow, hβ, map_one])
  obtain ⟨g, rfl⟩ := proj_surjective 3 k p
  exact ⟨g, CFSG.Quasithin.G11.P4SL34.descendAut_injective k
    (by rw [CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.descend_conj, hp])⟩

theorem card_eq_of_mulEquiv_SL {G k : Type} [Group G] [Field k] [Finite k]
    (hk : Nat.card k = 4) (e : G ≃* Matrix.SpecialLinearGroup (Fin 3) k) :
    Nat.card G = 60480 := by
  rw [Nat.card_congr e.toEquiv, (scalars 3 k).card_eq_card_quotient_mul_card_subgroup,
    CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk,
    CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hk]

theorem not_seven_dvd_card_of_mulEquiv_SL
    {G k : Type} [Group G] [Finite G] [Field k] [Finite k]
    (hk : Nat.card k = 4) (e : G ≃* Matrix.SpecialLinearGroup (Fin 3) k) {Y : Subgroup G}
    (hY : Y ≠ ⊤) (h3 : ¬ 3 ∣ Y.index) (hZ : Subgroup.center G ≤ Y) : ¬ 7 ∣ Nat.card Y := by
  let φ : G ⧸ Subgroup.center G ≃* projectiveSL 3 k :=
    QuotientGroup.congr _ _ e (by rw [scalars_eq_center]; exact Subgroup.map_center_eq e)
  have hLie : LieModel (G ⧸ Subgroup.center G) .PSL 3 2 2 :=
    Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, k,
      inferInstance, inferInstance, hk.trans (by norm_num),
      ⟨φ.trans ((QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 k)).trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 k))⟩⟩
  set Ybar := Y.map (QuotientGroup.mk' (Subgroup.center G))
  have hcomap : Ybar.comap (QuotientGroup.mk' (Subgroup.center G)) = Y :=
    Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hZ)
  have hidx : Y.index = Ybar.index := by
    rw [← Subgroup.index_comap_of_surjective Ybar (QuotientGroup.mk'_surjective _), hcomap]
  have hYbar_ne : Ybar ≠ ⊤ := fun htop => hY (by rw [← hcomap, htop, Subgroup.comap_top])
  have h7bar := CFSG.StandardType.L34Overgroup.not_seven_dvd_card_of_lieModel hLie hYbar_ne
    (by rwa [← hidx])
  intro h7
  apply h7bar
  have hcardQ : Nat.card (G ⧸ Subgroup.center G) = 20160 := by
    rw [Nat.card_congr φ.toEquiv, CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk]
  have h1 := Y.card_mul_index
  have h2 := Ybar.card_mul_index
  rw [card_eq_of_mulEquiv_SL hk e] at h1
  rw [hcardQ, ← hidx] at h2
  have hpos : 0 < Y.index := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h1
  have hY3 : Nat.card Y = 3 * Nat.card Ybar :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_assoc, h2, h1]; norm_num)
  rw [hY3] at h7
  exact ((Nat.Prime.dvd_mul (by norm_num)).mp h7).resolve_left (by norm_num)

theorem commute_of_conjNormal_apply_eq {X : Type} [Group X] {K : Subgroup X} [K.Normal] {e : X}
    {y : ↥K} (hy : MulAut.conjNormal e y = y) : e * (y : X) = y * e := by
  have h1 : e * (y : X) * e⁻¹ = y := by simpa using congrArg Subtype.val hy
  calc e * (y : X) = e * y * e⁻¹ * e := by group
    _ = y * e := by rw [h1]

namespace ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem card_map_conjNormal [K.Normal] (h : ThreeNineHyp K E D X₁ p d) :
    Nat.card (E.map (MulAut.conjNormal : X →* MulAut ↥K)) = p ^ 2 := by
  have hinj : Function.Injective ((MulAut.conjNormal : X →* MulAut ↥K).domRestrict E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (h.E_faithful x.2 fun c hc =>
      commute_of_conjNormal_apply_eq (y := ⟨c, hc⟩) (by
        simpa using congrArg (fun φ : MulAut ↥K => φ ⟨c, hc⟩) hx))
  rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    h.card_E]

theorem c25GammaCl_le [K.Normal] (h : ThreeNineHyp K E D X₁ p d)
    (h9 : Nat.card (E.map (MulAut.conjNormal : X →* MulAut ↥K)) = 9) :
    c25GammaCl (E.map (MulAut.conjNormal : X →* MulAut ↥K)) ≤ X₁.subgroupOf K := by
  have hfixS : ∀ S : Subgroup (MulAut ↥K), S ≤ E.map (MulAut.conjNormal : X →* MulAut ↥K) →
      S ≠ ⊥ → c25Fix S ≤ X₁.subgroupOf K := by
    intro S hSA hS1 y hy
    obtain ⟨α, hαS, hα1⟩ := (Subgroup.bot_or_exists_ne_one S).resolve_left hS1
    obtain ⟨e, heE, rfl⟩ := hSA hαS
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hα1 (map_one _)
    exact h.mem_of_commute_E heE he1 (Subgroup.mem_sup_left y.2)
      (commute_of_conjNormal_apply_eq (mem_c25Fix.1 hy _ hαS))
  refine iSup₂_le fun S hS => ?_
  have hS1 : S ≠ ⊥ := by
    rintro rfl
    have := hS.2
    rw [Subgroup.card_bot, h9] at this
    omega
  exact sup_le ((CFSG.HardMathSupport.Solomon.UniquenessMaximal.glaPPrimeCoreOf_le _).trans
      (hfixS S hS.1 hS1))
    ((show GLAPLayer 3 (c25Fix S) ≤ c25Fix S from sSup_le fun _ hL => hL.1).trans
      (hfixS S hS.1 hS1))

theorem le_sup_centralizer (h : ThreeNineHyp K E D X₁ 3 d)
    (hgen : ∀ A : Subgroup (MulAut ↥K), IsElemAbelian 3 A → Nat.card A = 9 →
      ¬ A ≤ innerAut ↥K → ⊤ ≤ c25GammaCl A) :
    E ≤ K ⊔ Subgroup.centralizer (K : Set X) := by
  have : K.Normal := h.normal
  have h9 : Nat.card (E.map (MulAut.conjNormal : X →* MulAut ↥K)) = 9 := h.card_map_conjNormal
  have hinn : E.map (MulAut.conjNormal : X →* MulAut ↥K) ≤ innerAut ↥K := by
    by_contra hni
    apply h.not_K_le
    intro c hc
    exact h.c25GammaCl_le h9 (hgen _
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.isElemAbelian_map_hom _ h.elem)
      h9 hni (Subgroup.mem_top ⟨c, hc⟩))
  intro e he
  obtain ⟨k, hk⟩ := hinn ⟨e, he, rfl⟩
  have hkC : (k : X)⁻¹ * e ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have h1 : (k : X) * c * (k : X)⁻¹ = e * c * e⁻¹ := by
      simpa using congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hc⟩ : ↥K) : X)) hk
    calc c * ((k : X)⁻¹ * e) = (k : X)⁻¹ * ((k : X) * c * (k : X)⁻¹) * e := by group
      _ = (k : X)⁻¹ * (e * c * e⁻¹) * e := by rw [h1]
      _ = (k : X)⁻¹ * e * c := by group
  have hsplit : e = (k : X) * ((k : X)⁻¹ * e) := by group
  rw [hsplit]
  exact Subgroup.mul_mem_sup k.2 hkC

theorem index_facts_of_le_sup (h : ThreeNineHyp K E D X₁ p d)
    (hEKC : E ≤ K ⊔ Subgroup.centralizer (K : Set X)) :
    (X₁.subgroupOf K).index ≡ 1 [MOD p] ∧
      p ^ (Nat.card ↥K).factorization p ∣ Nat.card (X₁.subgroupOf K) ∧
      Subgroup.center ↥K ≤ X₁.subgroupOf K := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : K.Normal := h.normal
  obtain ⟨Q₀, hQ₀⟩ := ((CFSG.Open.IsElemAbelian.isPGroup h.elem).comap_subtype :
    IsPGroup p (E.subgroupOf (K ⊔ Subgroup.centralizer (K : Set X)))).exists_le_sylow
  let Q : Subgroup X :=
    (Q₀ : Subgroup ↥(K ⊔ Subgroup.centralizer (K : Set X))).map (Subgroup.subtype _)
  have hQsyl : IsSylowOf p Q (K ⊔ Subgroup.centralizer (K : Set X)) := ⟨Q₀, rfl⟩
  have hEQ : E ≤ Q := fun e he =>
    Subgroup.mem_map.mpr ⟨⟨e, hEKC he⟩, hQ₀ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  have hSK : IsSylowOf p (Q ⊓ K) K :=
    hQsyl.inf_of_le_normalizer le_sup_left Subgroup.le_normalizer_of_normal
  have hSC : IsSylowOf p (Q ⊓ Subgroup.centralizer (K : Set X))
      (Subgroup.centralizer (K : Set X)) :=
    hQsyl.inf_of_le_normalizer le_sup_right Subgroup.le_normalizer_of_normal
  have hQeq : Q = (Q ⊓ K) ⊔ (Q ⊓ Subgroup.centralizer (K : Set X)) := by
    obtain ⟨-, hcard⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_sup_sylow
      (M₁ := K) (M₂ := Subgroup.centralizer (K : Set X)) Subgroup.le_normalizer_of_normal
      Subgroup.le_normalizer_of_normal inf_le_right inf_le_right hSK.isPGroup hSC.isPGroup
      hSK.card_eq hSC.card_eq
      fun s hs t ht => Subgroup.mem_centralizer_iff.mp ht.2 s hs.2
    exact (Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
      (le_of_eq (by rw [hcard, hQsyl.card_eq]))).symm
  have hNle : Subgroup.normalizer (Q ⊓ K : Set X) ⊓ K ≤ X₁ :=
    (le_inf (normalizer_inf_le_normalizer_of_eq_sup hQeq)
      (inf_le_right.trans le_sup_left)).trans (h.normQ Q hQsyl.isPGroup hEQ)
  let P : Sylow p ↥K := Sylow.ofCard ((Q ⊓ K).subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hSK.card_eq])
  have hNP : Subgroup.normalizer ((P : Subgroup ↥K) : Set ↥K) ≤ X₁.subgroupOf K := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer (((Q ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq inf_le_right] at hn'
    exact hNle ⟨hn', n.2⟩
  refine ⟨index_modEq_one_of_normalizer_le P hNP, ?_,
    (Subgroup.center_le_normalizer _).trans hNP⟩
  rw [← Sylow.card_eq_multiplicity P]
  exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer.trans hNP)

theorem index_facts_of_D_le (h : ThreeNineHyp K E D X₁ p d) (hDK : D ≤ K) :
    (X₁.subgroupOf K).index ≡ 1 [MOD d] ∧ d ∣ Nat.card (X₁.subgroupOf K) ∧
      d ∣ Nat.card ↥K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hDsylK : IsSylowOf d (D ⊓ K) K :=
    h.sylow.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  rw [inf_eq_left.mpr hDK] at hDsylK
  let SD : Sylow d ↥K := Sylow.ofCard (D.subgroupOf K) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, hDsylK.card_eq])
  have hND : Subgroup.normalizer ((SD : Subgroup ↥K) : Set ↥K) ≤ X₁.subgroupOf K := by
    intro n hn
    have hn' : n ∈ Subgroup.normalizer ((D.subgroupOf K : Subgroup ↥K) : Set ↥K) := hn
    rw [← Subgroup.subgroupOf_normalizer_eq hDK] at hn'
    exact h.normalizer_inf_le_of_le_D le_rfl h.D_ne_bot ⟨hn', le_sup_left (a := K) n.2⟩
  have hdD : d ∣ Nat.card (D.subgroupOf K) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
    exact h.isPGroup_D.card_eq_or_dvd.resolve_left fun h1 =>
      h.D_ne_bot (Subgroup.card_eq_one.mp h1)
  exact ⟨index_modEq_one_of_normalizer_le SD hND,
    hdD.trans (Subgroup.card_dvd_of_le (Subgroup.le_normalizer.trans hND)),
    hdD.trans (Subgroup.card_subgroup_dvd_card _)⟩

theorem D_le_K_of_conj (h : ThreeNineHyp K E D X₁ p d)
    (hinn : ∀ x ∈ D, ∃ k ∈ K, ∀ c ∈ K, x * c * x⁻¹ = k * c * k⁻¹) : D ≤ K := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have : K.Normal := h.normal
  have hcardC : ¬ d ∣ Nat.card (Subgroup.centralizer (K : Set X)) := by
    intro hdvd
    have hc := (h.sylow.inf_of_le_normalizer le_top (by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        (inferInstance : (Subgroup.centralizer (K : Set X)).Normal)]) :
        IsSylowOf d (D ⊓ Subgroup.centralizer (K : Set X)) _).card_eq
    rw [h.D_faithful, Subgroup.card_bot] at hc
    have hpos : 0 < (Nat.card (Subgroup.centralizer (K : Set X))).factorization d :=
      Nat.Prime.factorization_pos_of_dvd h.d_prime Nat.card_pos.ne' hdvd
    have := Nat.one_lt_pow hpos.ne' h.d_prime.one_lt
    omega
  intro x hxD
  obtain ⟨k, hkK, hk⟩ := hinn x hxD
  have hyC : k⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    calc c * (k⁻¹ * x) = k⁻¹ * (k * c * k⁻¹) * x := by group
      _ = k⁻¹ * (x * c * x⁻¹) * x := by rw [hk c hc]
      _ = k⁻¹ * x * c := by group
  obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
  have hxa : x ^ d ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hyc : (k⁻¹ * x) ^ Nat.card (Subgroup.centralizer (K : Set X)) = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (x := (⟨k⁻¹ * x, hyC⟩ :
      Subgroup.centralizer (K : Set X))))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using this
  have hxk : (x : X ⧸ K) = ((k⁻¹ * x : X) : X ⧸ K) := by
    rw [QuotientGroup.eq, show x⁻¹ * (k⁻¹ * x) = x⁻¹ * k⁻¹ * x⁻¹⁻¹ by group]
    exact h.normal.conj_mem _ (K.inv_mem hkK) _
  have hcop : Nat.Coprime (d ^ a) (Nat.card (Subgroup.centralizer (K : Set X))) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd h.d_prime).2 hcardC)
  have := pow_gcd_eq_one.mpr ⟨(by rw [← QuotientGroup.mk_pow, hxa, QuotientGroup.mk_one] :
    (x : X ⧸ K) ^ d ^ a = 1), (by rw [hxk, ← QuotientGroup.mk_pow, hyc, QuotientGroup.mk_one] :
    (x : X ⧸ K) ^ Nat.card (Subgroup.centralizer (K : Set X)) = 1)⟩
  rwa [hcop.gcd_eq_one, pow_one, QuotientGroup.eq_one_iff] at this

theorem D_le_K_of_aut (h : ThreeNineHyp K E D X₁ 3 d)
    (hinn : ∀ m : ℕ, Odd m → Nat.Coprime m 3 → ∀ α : MulAut ↥K, α ^ m = 1 →
      ∃ g, MulAut.conj g = α) : D ≤ K := by
  have : K.Normal := h.normal
  have : Fact d.Prime := ⟨h.d_prime⟩
  refine h.D_le_K_of_conj fun x hxD => ?_
  obtain ⟨a, ha⟩ := h.isPGroup_D ⟨x, hxD⟩
  have hxa : x ^ d ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := hinn (d ^ a) (h.d_prime.eq_two_or_odd'.resolve_left h.d_ne_two).pow
    (Nat.Coprime.pow_left a ((Nat.coprime_primes h.d_prime Nat.prime_three).2 h.d_ne))
    (MulAut.conjNormal x) (by rw [← map_pow, hxa, map_one])
  refine ⟨b, b.2, fun c hc => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨c, hc⟩ : ↥K) : X)) hb
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1.symm

theorem false_of_L34_orders (h : ThreeNineHyp K E D X₁ 3 d)
    (hEKC : E ≤ K ⊔ Subgroup.centralizer (K : Set X)) (hDK : D ≤ K)
    (hK : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 60480)
    (h7 : ∀ Y : Subgroup ↥K, Y ≠ ⊤ → ¬ 3 ∣ Y.index → Subgroup.center ↥K ≤ Y →
      ¬ 7 ∣ Nat.card Y) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hm3, h3Y, hZY⟩ := h.index_facts_of_le_sup hEKC
  obtain ⟨hmd, hdY, hdK⟩ := h.index_facts_of_D_le hDK
  have hYtop : X₁.subgroupOf K ≠ ⊤ := fun htop => h.not_K_le fun x hx =>
    (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥K) : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K)
  have h7Y := h7 _ hYtop (fun h3 => by unfold Nat.ModEq at hm3; omega) hZY
  have hd5 : d = 5 := by
    have hdK' : d ∣ 2 ^ 6 * 3 ^ 3 * 5 * 7 :=
      hdK.trans (by rcases hK with hK | hK <;> rw [hK] <;> norm_num)
    rcases (Nat.Prime.dvd_mul h.d_prime).mp hdK' with h1 | h1
    · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
      · rcases (Nat.Prime.dvd_mul h.d_prime).mp h1 with h1 | h1
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_two).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne_two
        · exact absurd ((Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_three).mp
            (h.d_prime.dvd_of_dvd_pow h1)) h.d_ne
      · exact (Nat.prime_dvd_prime_iff_eq h.d_prime Nat.prime_five).mp h1
    · rw [(Nat.prime_dvd_prime_iff_eq h.d_prime (by norm_num)).mp h1] at hdY
      exact absurd hdY h7Y
  subst hd5
  have h7idx : 7 ∣ (X₁.subgroupOf K).index := by
    have h7K : 7 ∣ Nat.card ↥K := by rcases hK with hK | hK <;> rw [hK] <;> norm_num
    rw [← (X₁.subgroupOf K).card_mul_index] at h7K
    exact ((Nat.Prime.dvd_mul (by norm_num)).mp h7K).resolve_left h7Y
  have hidx : (X₁.subgroupOf K).index ∣ 448 := by
    rcases hK with hK | hK
    · rw [hK, ← (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 2)
        (k := 2240) (N := 20160) (by norm_num) (by norm_num))] at h3Y
      have := index_dvd_div_of_dvd_card (Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (by norm_num : Nat.Coprime (3 ^ 2) 5) h3Y hdY)
      rw [hK] at this
      norm_num at this
      exact this
    · rw [hK, ← (CFSG.StandardType.SylowOvergroup.card_eq_pow_factorization (p := 3) (a := 3)
        (k := 2240) (N := 60480) (by norm_num) (by norm_num))] at h3Y
      have := index_dvd_div_of_dvd_card (Nat.Coprime.mul_dvd_of_dvd_of_dvd
        (by norm_num : Nat.Coprime (3 ^ 3) 5) h3Y hdY)
      rw [hK] at this
      norm_num at this
      exact this
  have key : ∀ m ∈ Nat.divisors 448, 7 ∣ m → m ≡ 1 [MOD 3] → m ≡ 1 [MOD 5] → False := by
    decide +kernel
  exact key _ (Nat.mem_divisors.mpr ⟨hidx, by norm_num⟩) h7idx hm3 hmd

end ThreeNineHyp

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {d : ℕ}

theorem false_of_threeNineHyp_L34
    (h : ThreeNineHyp K E D X₁ 3 d)
    (hK : StatedClassicalModel ↥K .PSL 3 2 2) : False := by
  have hL : IsLThreeFour ↥K := by
    obtain ⟨-, F, hF, hFin, hcard, he⟩ := hK
    exact ⟨F, hF, hFin, hcard.trans (by norm_num), he⟩
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hL
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  exact h.false_of_L34_orders
    (h.le_sup_centralizer
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.l34_holds ↥K hL))
    (h.D_le_K_of_aut fun m hm hm3 α hα =>
      exists_conj_eq_of_mulEquiv φ (exists_conj_eq_projectiveSL hk hm hm3) hα)
    (Or.inl (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four hK))
    fun Y hY h3 _ => CFSG.StandardType.L34Overgroup.not_seven_dvd_card_of_lieModel
      (Or.inl ⟨by decide, hK⟩) hY h3

theorem false_of_threeNineHyp_SL34
    {F : Type} [Field F] [Finite F]
    (h : ThreeNineHyp K E D X₁ 3 d) (hF : Nat.card F = 4)
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 3) F) : False := by
  have hSL : IsSLThreeFour ↥K :=
    ⟨F, inferInstance, inferInstance, hF,
      ⟨e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)⟩⟩
  exact h.false_of_L34_orders
    (h.le_sup_centralizer
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320.sl34_holds ↥K hSL))
    (h.D_le_K_of_aut fun m hm hm3 α hα =>
      exists_conj_eq_of_mulEquiv e (exists_conj_eq_SL hF hm hm3) hα)
    (Or.inr (card_eq_of_mulEquiv_SL hF e))
    fun Y hY h3 hZ => not_seven_dvd_card_of_mulEquiv_SL hF e hY h3 hZ

theorem threeNineThreeL34_holds :
    ThreeNineThreeL34 := by
  intro X _ _ K E D X₁ d h hK
  rcases hK with hK | ⟨F, _, _, hF, ⟨e⟩⟩
  · exact false_of_threeNineHyp_L34 h hK
  · exact false_of_threeNineHyp_SL34 h hF e

end CFSG.LocalAnalysis.AGL81I.Section3
