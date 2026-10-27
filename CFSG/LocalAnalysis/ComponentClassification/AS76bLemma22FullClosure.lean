module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullClosureBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma38Core
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Thm5

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma22Full

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22
open scoped commutatorElement

section Bars

variable {G : Type*} [Group G]

noncomputable def componentBars (L A : Subgroup G) :
    Fin 2 → Subgroup (↥(L ⊔ A) ⧸ aschbacherThm5OddCore ↥(L ⊔ A)) :=
  ![(L.subgroupOf (L ⊔ A)).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥(L ⊔ A))),
    (A.subgroupOf (L ⊔ A)).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥(L ⊔ A)))]

theorem preimage_map_subgroupOf {D M : Subgroup G} (hMD : M ≤ D) :
    aschbacherThm5Preimage D
      ((M.subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥D))) =
      M ⊔ aschbacherThm5Core D := by
  unfold aschbacherThm5Preimage aschbacherThm5Core
  rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup, subgroupOf_map_subtype,
    inf_eq_left.mpr hMD]

theorem preimage_componentBars_zero (L A : Subgroup G) :
    aschbacherThm5Preimage (L ⊔ A) (componentBars L A 0) = L ⊔ aschbacherThm5Core (L ⊔ A) :=
  preimage_map_subgroupOf le_sup_left

theorem preimage_componentBars_one (L A : Subgroup G) :
    aschbacherThm5Preimage (L ⊔ A) (componentBars L A 1) = A ⊔ aschbacherThm5Core (L ⊔ A) :=
  preimage_map_subgroupOf le_sup_right

theorem mem_centralizer_of_centralizes {D M : Subgroup G} (hM : ⁅M, M⁆ = M) (hMD : M ≤ D)
    (hcomm : ∀ o ∈ aschbacherThm5Core D, ∀ x ∈ D, Commute o x) {t : G}
    (ht : aschbacherThm5Centralizes (aschbacherThm5Core D) (M ⊔ aschbacherThm5Core D) t) :
    t ∈ centralizer (M : Set G) := by
  have hc : ∀ m ∈ M, ∃ c ∈ aschbacherThm5Core D, t⁻¹ * m * t = m * c⁻¹ := fun m hm =>
    ⟨t⁻¹ * m⁻¹ * t * m, ht m (mem_sup_left hm), by group⟩
  have hkey : M ≤ centralizer ({t} : Set G) := by
    rw [← hM, commutator_le]
    intro m₁ h₁ m₂ h₂
    obtain ⟨c₁, hc₁, he₁⟩ := hc m₁ h₁
    obtain ⟨c₂, hc₂, he₂⟩ := hc m₂ h₂
    rw [mem_centralizer_singleton_iff]
    have hconj : t⁻¹ * ⁅m₁, m₂⁆ * t = ⁅t⁻¹ * m₁ * t, t⁻¹ * m₂ * t⁆ := by
      simp only [commutatorElement_def]
      group
    have h : t⁻¹ * ⁅m₁, m₂⁆ * t = ⁅m₁, m₂⁆ := by
      rw [hconj, he₁, he₂]
      exact commutatorElement_mul_mul (hcomm _ (inv_mem hc₁) m₂ (hMD h₂))
        (hcomm _ (inv_mem hc₁) _ (inv_mem (core_le D hc₂))) (hcomm _ (inv_mem hc₂) m₁ (hMD h₁))
    calc ⁅m₁, m₂⁆ * t = t * (t⁻¹ * ⁅m₁, m₂⁆ * t) := by group
      _ = t * ⁅m₁, m₂⁆ := by rw [h]
  rw [mem_centralizer_iff]
  intro m hm
  exact mem_centralizer_singleton_iff.mp (hkey hm)

theorem le_of_forall_mem_mul {D M X : Subgroup G} (hM : ⁅M, M⁆ = M) (hMD : M ≤ D)
    (hcomm : ∀ o ∈ aschbacherThm5Core D, ∀ x ∈ D, Commute o x)
    (h : ∀ m ∈ M, ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D, m = x * o) : M ≤ X := by
  rw [← hM, commutator_le]
  intro m₁ h₁ m₂ h₂
  obtain ⟨x₁, hx₁, o₁, ho₁, rfl⟩ := h m₁ h₁
  obtain ⟨x₂, hx₂, o₂, ho₂, rfl⟩ := h m₂ h₂
  have hx₁D : x₁ ∈ D := by simpa using mul_mem (hMD h₁) (inv_mem (core_le D ho₁))
  have hx₂D : x₂ ∈ D := by simpa using mul_mem (hMD h₂) (inv_mem (core_le D ho₂))
  rw [commutatorElement_mul_mul (hcomm o₁ ho₁ x₂ hx₂D) (hcomm o₁ ho₁ o₂ (core_le D ho₂))
    (hcomm o₂ ho₂ x₁ hx₁D), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₁)) (inv_mem hx₂)

theorem isQuasisimple_map_subgroupOf [Finite G] {D M : Subgroup G}
    (hM : CFSG.Open.IsQuasisimple ↥M) (hMD : M ≤ D) :
    CFSG.Open.IsQuasisimple
      ↥((M.subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥D))) := by
  set f := (QuotientGroup.mk' (aschbacherThm5OddCore ↥D)).comp (M.subgroupOf D).subtype with hf
  have hrange : f.range = (M.subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥D)) :=
    by rw [hf, MonoidHom.range_comp, range_subtype]
  have hker : f.ker ≠ ⊤ := by
    intro htop
    have hle : M ≤ aschbacherThm5Core D := by
      intro m hm
      have hm' : (⟨⟨m, hMD hm⟩, hm⟩ : ↥(M.subgroupOf D)) ∈ f.ker := htop ▸ mem_top _
      rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hm'
      exact ⟨⟨m, hMD hm⟩, hm', rfl⟩
    exact (Nat.not_even_iff_odd.mpr ((odd_card_core D).of_dvd_nat (card_dvd_of_le hle)))
      (even_card_of_isQuasisimple hM)
  have h := Quasisimple.range_quasisimple_of_ker_ne_top
    ((Lemma37.isQuasisimple_subgroupOf_iff hMD).mpr hM) f hker
  rwa [hrange] at h

theorem aschbacherThm5IsSemisimple_of_isQuasisimple {Q : Type*} [Group Q] {X : Subgroup Q}
    (hX : CFSG.Open.IsQuasisimple ↥X) : aschbacherThm5IsSemisimple X :=
  ⟨1, fun _ => X, Nat.one_pos, fun _ => ⟨le_rfl, hX⟩,
    fun l m hlm => absurd (Subsingleton.elim l m) hlm, iSup_const⟩

theorem even_card_of_mem_of_pow_eq_one {X : Subgroup G} {t : G} (htX : t ∈ X) (ht1 : t ≠ 1)
    {k : ℕ} (htk : t ^ 2 ^ k = 1) : Even (Nat.card X) := by
  have hdvd : orderOf t ∣ Nat.card X := by
    rw [← Subgroup.orderOf_mk t htX]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one htk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact ht1 (orderOf_eq_one_iff.mp (by simpa using hj))
  exact even_iff_two_dvd.mpr ((dvd_pow_self 2 hj0).trans (hj ▸ hdvd))

end Bars

variable {G : Type} [Group G] [Finite G]

namespace ClosureSetting

variable {K R L : Subgroup G} {g : G} (hS : ClosureSetting K R L g)
include hS

theorem mem_normalizer_sup_of_conj_mem {x z t w : G}
    (hx : x ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G))
    (hz : z ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G)) (ht1 : t ≠ 1) {k : ℕ}
    (htk : t ^ 2 ^ k = 1) (htx : t ∈ centralizer (conj L x : Set G))
    (htz : w⁻¹ * t * w ∈ centralizer (conj L z : Set G)) :
    w ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G) := by
  set H := centralizer (L : Set G) with hH
  rw [centralizer_conj, mem_conj_iff] at htx htz
  set v := x⁻¹ * w * z with hv
  have h3 : v⁻¹ * (x⁻¹ * t * x) * v = z⁻¹ * (w⁻¹ * t * w) * z := by
    rw [hv]
    group
  have hvN : v⁻¹ ∈ normalizer (H : Set G) := by
    by_contra hvN
    have hodd := hS.tightlyEmbedded_centralizer.2 v⁻¹ hvN
    have hmem : x⁻¹ * t * x ∈ H ⊓ rightConjugate H v⁻¹ := by
      refine mem_inf.mpr ⟨htx, ?_⟩
      rw [mem_rightConjugate_iff, inv_inv, h3]
      exact htz
    have ht1' : x⁻¹ * t * x ≠ 1 := by
      intro h
      apply ht1
      have h' : x * (x⁻¹ * t * x) * x⁻¹ = 1 := by rw [h]; group
      simpa [mul_assoc] using h'
    have htk' : (x⁻¹ * t * x) ^ 2 ^ k = 1 := by
      rw [show x⁻¹ * t * x = x⁻¹ * t * x⁻¹⁻¹ by rw [inv_inv], conj_pow, htk, mul_one,
        mul_inv_cancel]
    exact (Nat.not_even_iff_odd.mpr hodd) (even_card_of_mem_of_pow_eq_one hmem ht1' htk')
  have hvL : v ∈ normalizer (L : Set G) := by
    rw [← hS.normalizer_centralizer]
    simpa using inv_mem hvN
  have hw : w = x * v * z⁻¹ := by
    rw [hv]
    group
  rw [hw]
  exact mul_mem (mul_mem hx (hS.normalizer_le_normalizer_sup hvL)) (inv_mem hz)

theorem componentBars_ne : componentBars L (conj L g) 0 ≠ componentBars L (conj L g) 1 := by
  intro h
  have hpre := congrArg (aschbacherThm5Preimage (L ⊔ conj L g)) h
  rw [preimage_componentBars_zero, preimage_componentBars_one] at hpre
  have hLA : L ≤ conj L g := by
    refine le_of_forall_mem_mul (commutator_self_eq hS.quasisimple) le_sup_left
      (fun o ho x hx => hS.commute_of_mem_core ho hx) fun l hl => ?_
    have hl' : l ∈ conj L g ⊔ aschbacherThm5Core (L ⊔ conj L g) := hpre ▸ mem_sup_left hl
    obtain ⟨a, ha, o, ho, hao⟩ := exists_mul_of_mem_sup_of_le_normalizer
      (hS.core_le_centralizer_conj.trans (centralizer_le_normalizer _)) hl'
    exact ⟨a, ha, o, ho, hao⟩
  have hLeq : L = conj L g := eq_of_le_of_card_ge hLA (by rw [card_conj])
  exact not_le_centralizer_self hS.quasisimple (hLeq.le.trans hS.conj_le)

theorem hyp61 :
    AschbacherTheorem5.Hyp61 G (L ⊔ conj L g) 2 (componentBars L (conj L g)) := by
  have hcomm : ∀ o ∈ aschbacherThm5Core (L ⊔ conj L g), ∀ x ∈ L ⊔ conj L g, Commute o x :=
    fun o ho x hx => hS.commute_of_mem_core ho hx
  have hpre : ∀ i : Fin 2, ∃ x ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G),
      aschbacherThm5Preimage (L ⊔ conj L g) (componentBars L (conj L g) i) =
        conj L x ⊔ aschbacherThm5Core (L ⊔ conj L g) := by
    intro i
    fin_cases i
    · exact ⟨1, one_mem _, by rw [conj_one]; exact preimage_componentBars_zero _ _⟩
    · exact ⟨g, hS.mem_normalizer_sup, preimage_componentBars_one _ _⟩
  have hD : ∀ x ∈ normalizer ((L ⊔ conj L g : Subgroup G) : Set G), conj L x ≤ L ⊔ conj L g :=
    fun x hx => (map_mono le_sup_left).trans (conj_eq_self_iff.mpr hx).le
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hS.componentBars_ne
    · exact absurd hij.symm hS.componentBars_ne
    · rfl
  ·
    intro i
    apply aschbacherThm5IsSemisimple_of_isQuasisimple
    fin_cases i
    · exact isQuasisimple_map_subgroupOf hS.quasisimple le_sup_left
    · exact isQuasisimple_map_subgroupOf (isQuasisimple_conj hS.quasisimple g) le_sup_right
  ·
    have hc : ∀ x ∈ componentBars L (conj L g) 0, ∀ y ∈ componentBars L (conj L g) 1,
        x * y = y * x := by
      rintro _ ⟨l, hl, rfl⟩ _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [coe_mul]
      exact (mem_centralizer_iff.mp (hS.conj_le ha) l hl)
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hc
    · exact fun x hx y hy => (hc y hy x hx).symm
    · exact absurd rfl hij
  ·
    apply top_unique
    have h01 : componentBars L (conj L g) 0 ⊔ componentBars L (conj L g) 1 ≤
        ⨆ i, componentBars L (conj L g) i := sup_le (le_iSup _ 0) (le_iSup _ 1)
    refine le_trans ?_ h01
    have : componentBars L (conj L g) 0 ⊔ componentBars L (conj L g) 1 =
        (L.subgroupOf (L ⊔ conj L g) ⊔ (conj L g).subgroupOf (L ⊔ conj L g)).map
          (QuotientGroup.mk' (aschbacherThm5OddCore ↥(L ⊔ conj L g))) := by
      rw [Subgroup.map_sup]
      rfl
    rw [this, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  ·
    intro h hh i
    obtain ⟨x, hx, hxe⟩ := hpre i
    have hmap : (conj L x ⊔ aschbacherThm5Core (L ⊔ conj L g)).map
        (MulAut.conj h).toMonoidHom =
        conj L (h * x) ⊔ aschbacherThm5Core (L ⊔ conj L g) := by
      rw [Subgroup.map_sup]
      change conj (conj L x) h ⊔ conj (aschbacherThm5Core (L ⊔ conj L g)) h = _
      rw [conj_conj, conj_eq_self_iff.mpr (normalizer_le_normalizer_core _ hh)]
    rw [hxe, hmap]
    rcases hS.conj_eq_or_eq (mul_mem hh hx) with h1 | h1
    · exact ⟨0, by rw [h1, preimage_componentBars_zero]⟩
    · exact ⟨1, by rw [h1, preimage_componentBars_one]⟩
  ·
    intro i j t w ht2 htZ hti htj
    obtain ⟨k, hk⟩ := ht2
    have ht1 : t ≠ 1 := fun h => htZ (h ▸ one_mem _)
    obtain ⟨x, hx, hxe⟩ := hpre i
    obtain ⟨z, hz, hze⟩ := hpre j
    rw [hxe] at hti
    rw [hze] at htj
    exact hS.mem_normalizer_sup_of_conj_mem hx hz ht1 hk
      (mem_centralizer_of_centralizes (commutator_self_eq (isQuasisimple_conj hS.quasisimple x))
        (hD x hx) hcomm hti)
      (mem_centralizer_of_centralizes (commutator_self_eq (isQuasisimple_conj hS.quasisimple z))
        (hD z hz) hcomm htj)
  ·
    intro i w X hX hXi
    obtain ⟨x, hx, hxe⟩ := hpre i
    rw [hxe] at hXi
    have hle : conj L x ≤ X :=
      le_of_forall_mem_mul (commutator_self_eq (isQuasisimple_conj hS.quasisimple x)) (hD x hx)
        hcomm fun m hm => hXi m (mem_sup_left hm)
    have hwx : conj L (w * x) ≤ normalizer ((L ⊔ conj L g : Subgroup G) : Set G) := by
      rw [← conj_conj]
      calc conj (conj L x) w ≤ conj X w := map_mono hle
        _ ≤ conj ((normalizer ((L ⊔ conj L g : Subgroup G) : Set G)).map
              (MulAut.conj w⁻¹).toMonoidHom) w := map_mono hX
        _ = normalizer ((L ⊔ conj L g : Subgroup G) : Set G) := by
          change conj (conj _ w⁻¹) w = _
          rw [conj_conj, mul_inv_cancel, conj_one]
    have h := mul_mem (hS.mem_normalizer_sup_of_conj_le hwx) (inv_mem hx)
    simpa using h

theorem normal_sup (h5 : Asc75T4.Theorem5Statement)
    (hV : ∃ V : Subgroup G, V ≤ L ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) :
    (L ⊔ conj L g).Normal := by
  by_contra hN
  have hN' : normalizer ((L ⊔ conj L g : Subgroup G) : Set G) ≠ ⊤ :=
    fun h => hN (normalizer_eq_top_iff.mp h)
  rcases h5 G (L ⊔ conj L g) 2 (componentBars L (conj L g)) hS.hyp61 hN' with h | ⟨-, h⟩
  · exact absurd h (by norm_num)
  · obtain ⟨-, hrank, -⟩ := h 0 1 (by decide)
    rw [preimage_componentBars_zero] at hrank
    obtain ⟨V, hVL, hVe, hV4⟩ := hV
    have h2 : 2 ≤ CFSG.Open.pRank 2 (L ⊔ aschbacherThm5Core (L ⊔ conj L g)) :=
      CFSG.SectionRank.le_pRank (k := 2) one_lt_two (hVL.trans le_sup_left) hVe
        (by rw [hV4]; norm_num)
    omega

theorem normalClosure_eq_sup (h5 : Asc75T4.Theorem5Statement)
    (hV : ∃ V : Subgroup G, V ≤ L ∧ IsElemAbelian 2 V ∧ Nat.card V = 4) :
    normalClosure (L : Set G) = L ⊔ conj L g := by
  have := hS.normal_sup h5 hV
  apply le_antisymm
  · exact normalClosure_le_normal (le_sup_left : L ≤ L ⊔ conj L g)
  · exact sup_le le_normalClosure (conj_le_of_normal (normalClosure_normal) le_normalClosure g)

end ClosureSetting

end Lemma22Full

end CFSG.ComponentClassification.AS76b
