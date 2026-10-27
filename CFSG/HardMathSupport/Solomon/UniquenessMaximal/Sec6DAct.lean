module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barOf_centreless (iL3 : InputL3U3Facts) {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (ht : IsLThreeEps (barOf 3 K)) {g : G} (hg : g ∈ K)
    (hc : ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K) : g ∈ GLAPPrimeCoreOf 3 K := by
  have hq : CFSG.Open.IsQuasisimple (barOf 3 K) :=
    (Lemma512Ns.isQuasisimple_barX_iff Nat.prime_three hK.2.1).1 hK.2.2.1.2.2
  have hbot := center_eq_bot_of_quasisimple_simple hq ((iL3 (barOf 3 K) ht).1 hq.1)
  set m : barOf 3 K := QuotientGroup.mk ⟨g, hg⟩ with hm
  have hcen : ∀ w : barOf 3 K, w * m = m * w := by
    intro w
    induction w using QuotientGroup.induction_on with | H k => ?_
    have h1 := (mem_coreOf_iff (p := 3) (X := K) (k * ⟨g, hg⟩ * k⁻¹ * ⟨g, hg⟩⁻¹)).1
      (by simpa using hc k.1 k.2)
    have h2 : (QuotientGroup.mk (k * ⟨g, hg⟩ * k⁻¹ * ⟨g, hg⟩⁻¹) : barOf 3 K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h1
    rw [hm]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1
      (show ⁅(QuotientGroup.mk k : barOf 3 K), (QuotientGroup.mk ⟨g, hg⟩ : barOf 3 K)⁆ = 1 from h2)
  have hmem : m ∈ Subgroup.center (barOf 3 K) := Subgroup.mem_center_iff.2 hcen
  rw [hbot, Subgroup.mem_bot] at hmem
  have : (⟨g, hg⟩ : ↥K) ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 hmem
  exact (mem_coreOf_iff (p := 3) (X := K) ⟨g, hg⟩).2 this

theorem barAut_eq_conj {p : ℕ} {K : Subgroup G} {f : G} (hf : f ∈ K)
    (hfN : f ∈ Subgroup.normalizer (K : Set G)) :
    barAut p K ⟨f, hfN⟩ = MulAut.conj (QuotientGroup.mk ⟨f, hf⟩ : barOf p K) := by
  ext z
  induction z using QuotientGroup.induction_on with | H y => ?_
  rw [barAut_mk]
  simp only [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
  rfl

theorem barAut_eq_one_of_cover {K J : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) {a : G} (haN : a ∈ Subgroup.normalizer (K : Set G))
    (haJ : ∀ j ∈ J, a * j = j * a) : barAut 3 K ⟨a, haN⟩ = 1 := by
  set φ : ↥K →* barOf 3 K := (barAut 3 K ⟨a, haN⟩).toMonoidHom.comp
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) with hφ
  set T : Subgroup ↥K := MonoidHom.eqLocus φ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) with hT
  have hJT : J.subgroupOf K ≤ T := by
    intro j hj
    have hj' : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    show φ j = QuotientGroup.mk' _ j
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    show a * (j : G) * a⁻¹ = j
    rw [haJ _ hj']; group
  have hOT : GLAPPrimeCore 3 ↥K ≤ T := by
    intro o ho
    show φ o = QuotientGroup.mk' _ o
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) o = 1 := (QuotientGroup.eq_one_iff _).2 ho
    simp only [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    rw [h1, map_one]
  have hTtop : T = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : (k : G) ∈ J ⊔ GLAPPrimeCoreOf 3 K := hcov k.2
    have hsup : (J.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K).map K.subtype = J ⊔ GLAPPrimeCoreOf 3 K := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK]
      rfl
    have : k ∈ J.subgroupOf K ⊔ GLAPPrimeCore 3 ↥K := by
      rw [← Subgroup.mem_map_iff_mem K.subtype_injective, hsup]; exact hk
    exact (sup_le hJT hOT) this
  ext z
  induction z using QuotientGroup.induction_on with | H y => ?_
  have hy : y ∈ T := by rw [hTtop]; exact Subgroup.mem_top y
  have h1 : φ y = QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) y := hy
  simpa [hφ] using h1

theorem mem_A_aux (iL3 : InputL3U3Facts) {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {X K : Subgroup G} (hK : GLAPComponent 3 X K)
    (ht : IsLThreeEps (barOf 3 K)) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hFK : B ⊓ L ≤ K) (hfield : ∀ a' ∈ A, InducesFieldAut 3 K a') {g : G} (hgB : g ∈ B)
    (hg : ∀ k ∈ K, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 K) : g ∈ A := by
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcentF : A ≤ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (ea_comm hx.Bel (hx.AB ha) hf.1).symm
  have hgAF : g ∈ A ⊔ (B ⊓ L) := by rw [hx.BAF]; exact hgB
  obtain ⟨a', ha', f, hf, rfl⟩ := exists_mul_of_mem_sup hcentF hgAF
  have hfK : f ∈ K := hFK hf
  have hfN : f ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hfK
  have ha'N : a' ∈ Subgroup.normalizer (K : Set G) := hBK (hx.AB ha')
  have hgN : a' * f ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ ha'N hfN
  have htriv : barAut 3 K ⟨a' * f, hgN⟩ = 1 :=
    (Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 ⟨a' * f, hgN⟩).1
      ⟨hgN, normalizer_core 3 hgN, hg⟩
  have hmul : barAut 3 K ⟨a' * f, hgN⟩ = barAut 3 K ⟨a', ha'N⟩ * barAut 3 K ⟨f, hfN⟩ := by
    rw [← map_mul]; rfl
  have hinv : barAut 3 K ⟨a', ha'N⟩ = (barAut 3 K ⟨f, hfN⟩)⁻¹ :=
    eq_inv_of_mul_eq_one_left (hmul ▸ htriv)
  have hinner : barAut 3 K ⟨a', ha'N⟩ ∈ innerAut (barOf 3 K) := by
    rw [hinv]
    refine (innerAut (barOf 3 K)).inv_mem ?_
    rw [barAut_eq_conj hfK hfN]
    exact ⟨_, rfl⟩
  obtain ⟨hN', hfa⟩ := hfield a' ha'
  have hα1 : barAut 3 K ⟨a', ha'N⟩ = 1 :=
    (iL3 (barOf 3 K) ht).2.2.1 _ hinner hfa
  have hfeq : barAut 3 K ⟨f, hfN⟩ = 1 := by
    rw [hα1] at hinv
    exact inv_eq_one.1 hinv.symm
  have hf_cq := (Lemma513Ns.mem_centralizerQuot_iff_barAut' 3 ⟨f, hfN⟩).2 hfeq
  have hfO := barOf_centreless iL3 hK ht hfK hf_cq.2.2
  have hFp : IsPGroup 3 ↥(B ⊓ L) := (isPGroup_of_isElemAbelian hx.Bel).to_inf_left
  have hf1 : f ∈ (B ⊓ L) ⊓ GLAPPrimeCoreOf 3 K := ⟨hf, hfO⟩
  rw [pgroup_inf_core_eq_bot K hFp, Subgroup.mem_bot] at hf1
  rw [hf1, mul_one]
  exact ha'

theorem mem_A_of_centralizes (iL3 : InputL3U3Facts) (iK : InputKType) (h514 : Lemma514)
    (h515 : Lemma515) {m : ℕ} {B : Subgroup G} {b : G} {L A : Subgroup G}
    (e : Env m B b L A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {g : G} (hgB : g ∈ B)
    (hg : ∀ k ∈ kOf L A a, k * g * k⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 (kOf L A a)) : g ∈ A := by
  refine mem_A_aux iL3 e.X (Ka_comp iL3 e.X ha ha1) (Ka_type iK e ha ha1) (Ka_B h515 e ha ha1)
    (F_le_Ka e.X a) ?_ hgB hg
  intro a' ha'
  have ha'N : a' ∈ Subgroup.normalizer (kOf L A a : Set G) := Ka_B h515 e ha ha1 (e.X.AB ha')
  by_cases hab : a ∈ Subgroup.zpowers b
  · have hC := centralizer_eq_of_mem_zpowers (e.X.Bel.2 b e.X.b_mem) e.X.b_ne hab ha1
    have hKL := kOf_eq_L iL3 e.X hC
    rw [hKL]
    exact e.X.field a' ha'
  · have hcov := (h514 G m e.S e.C B e.B1 b L A e.w a ha ha1).2 hab
    refine ⟨ha'N, Or.inl ?_⟩
    refine barAut_eq_one_of_cover (jOf_le_kOf' L A a) hcov ha'N fun j hj => ?_
    have hjC : j ∈ Subgroup.centralizer (A : Set G) := (jOf_le' L A hj).2
    exact Subgroup.mem_centralizer_iff.1 hjC a' ha'

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
