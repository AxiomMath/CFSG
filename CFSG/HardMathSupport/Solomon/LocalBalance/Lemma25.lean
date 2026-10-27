module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements2
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma24
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Family
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma25Ns

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

abbrev Cen {G : Type*} [Group G] (b : G) : Subgroup G := Subgroup.centralizer ({b} : Set G)

@[expose] def IsLThreeEps (Y : Type*) [Group Y] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K % 3 = 1 ∧
      Nonempty (Y ≃* StatedProj (StatedSL 3 K))) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (q : ℕ), Nat.card K = q ^ 2 ∧ q % 3 = 2 ∧
      Nonempty (Y ≃* StatedProj (StatedSU 3 q K)))

@[expose] def IsAltType (Y : Type*) [Group Y] : Prop :=
  ∃ n : ℕ, Nonempty (Y ≃* ↥(alternatingGroup (Fin n)))

@[expose] def Input11_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ∀ b ∈ B, b ∉ Subgroup.normalizer (L : Set G) →
        Nonempty ((↥(GLAPLayer p (bClosure B L ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
            GLAPPrimeCore p ↥(GLAPLayer p (bClosure B L ⊓ Subgroup.centralizer ({b} : Set G)))) ≃*
          (barOf p L ⧸ Subgroup.center (barOf p L)))

@[expose] def Input19_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → ∀ D : Subgroup G,
      IsElemAbelian p D → Nat.card D = p ^ k →
      ∀ b ∈ Subgroup.centralizer (D : Set G), b ≠ 1 → b ^ p = 1 →
        (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (L : Set G)) ∧
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          ¬ ⁅L, GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤
              GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
            D ≤ Subgroup.normalizer (L : Set G) ∧ ¬ IsCompLocallyBalanced p k D L

@[expose] def Input19_6_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ (X J D : Subgroup G), X ≠ ⊤ → GLAPComponent 3 X J →
      D ≤ Subgroup.normalizer (J : Set G) → IsElemAbelian 3 D →
      ¬ IsCompLocallyBalanced 3 2 D J →
        IsLThreeEps (↥J ⧸ oPrimeP 3 ↥J) ∨ IsAltType (↥J ⧸ oPrimeP 3 ↥J)

@[expose] def Input14_3_L3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ (X Js J : Subgroup G) (b : G), X ≠ ⊤ → GLAPComponent 3 X Js →
      (IsLThreeEps (↥Js ⧸ oPrimeP 3 ↥Js) ∨ IsAltType (↥Js ⧸ oPrimeP 3 ↥Js)) →
      b ∈ X → b ∈ Subgroup.normalizer (Js : Set G) → b ^ 3 = 1 →
      GLAPComponent 3 (Js ⊓ Subgroup.centralizer ({b} : Set G)) J →
      (IsSLThreeExc (barOf 3 J) ∨ IsSUThreeExc (barOf 3 J)) →
      oPrimePOf 3 J ≤ oPrimePOf 3 Js


section PureGroup

variable {G : Type*} [Group G]

open scoped commutatorElement in
theorem pg1_conj_of_mem {T : Subgroup G} {y : G} (hy : y ∈ Subgroup.normalizer (T : Set G))
    {t : G} (ht : t ∈ T) : y * t * y⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.1 hy t).1 ht

open scoped commutatorElement in
theorem pg1_le_normalizer (T K : Subgroup G) (h : ∀ g ∈ K, ∀ t ∈ T, g * t * g⁻¹ ∈ T) :
    K ≤ Subgroup.normalizer (T : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => h g hg t ht, fun ht => ?_⟩
  have := h g⁻¹ (K.inv_mem hg) _ ht
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  rwa [e] at this

open scoped commutatorElement in
theorem pg1_conj_comm (c : G) (M B : Subgroup G) (hM : ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hB : ∀ b ∈ B, c * b * c⁻¹ ∈ B) : ∀ t ∈ ⁅M, B⁆, c * t * c⁻¹ ∈ ⁅M, B⁆ := by
  have : ⁅M, B⁆ ≤ Subgroup.comap (MulAut.conj c).toMonoidHom ⁅M, B⁆ := by
    rw [Subgroup.commutator_le]
    intro m hm b hb
    have e : (MulAut.conj c).toMonoidHom ⁅m, b⁆ = ⁅c * m * c⁻¹, c * b * c⁻¹⁆ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        commutatorElement_def]; group
    rw [Subgroup.mem_comap, e]
    exact Subgroup.commutator_mem_commutator (hM m hm) (hB b hb)
  intro t ht
  simpa using this ht

open scoped commutatorElement in
theorem pg1_self_conj (Y B : Subgroup G) : ∀ y ∈ Y, ∀ t ∈ ⁅Y, B⁆, y * t * y⁻¹ ∈ ⁅Y, B⁆ := by
  intro y hy
  have : ⁅Y, B⁆ ≤ Subgroup.comap (MulAut.conj y).toMonoidHom ⁅Y, B⁆ := by
    rw [Subgroup.commutator_le]
    intro m hm b hb
    have e : (MulAut.conj y).toMonoidHom ⁅m, b⁆ = ⁅y * m, b⁆ * ⁅y, b⁆⁻¹ := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
        commutatorElement_def]; group
    rw [Subgroup.mem_comap, e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (Y.mul_mem hy hm) hb)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy hb))
  intro t ht
  simpa using this ht

open scoped commutatorElement in
theorem pg1_sup_conj (c : G) (A1 A2 : Subgroup G) (h1 : ∀ t ∈ A1, c * t * c⁻¹ ∈ A1 ⊔ A2)
    (h2 : ∀ t ∈ A2, c * t * c⁻¹ ∈ A1 ⊔ A2) : ∀ t ∈ A1 ⊔ A2, c * t * c⁻¹ ∈ A1 ⊔ A2 := by
  have : A1 ⊔ A2 ≤ Subgroup.comap (MulAut.conj c).toMonoidHom (A1 ⊔ A2) :=
    sup_le (fun t ht => by simpa using h1 t ht) (fun t ht => by simpa using h2 t ht)
  intro t ht
  simpa using this ht

open scoped commutatorElement in
theorem pg1_comm_sup_le (T B P Q : Subgroup G) (hP : P ≤ Subgroup.normalizer (T : Set G))
    (hQ : Q ≤ Subgroup.normalizer (T : Set G)) (hP2 : ∀ p ∈ P, ∀ β ∈ B, ⁅p, β⁆ ∈ T)
    (hQ2 : ∀ q ∈ Q, ∀ β ∈ B, ⁅q, β⁆ ∈ T) : ⁅P ⊔ Q, B⁆ ≤ T := by
  let S : Subgroup G :=
    { carrier := {y | y ∈ Subgroup.normalizer (T : Set G) ∧ ∀ β ∈ B, ⁅y, β⁆ ∈ T}
      one_mem' := ⟨Subgroup.one_mem _, fun β _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h1, h1'⟩ ⟨h2, h2'⟩
        refine ⟨Subgroup.mul_mem _ h1 h2, fun β hβ => ?_⟩
        have e : ⁅y₁ * y₂, β⁆ = (y₁ * ⁅y₂, β⁆ * y₁⁻¹) * ⁅y₁, β⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact T.mul_mem (pg1_conj_of_mem h1 (h2' β hβ)) (h1' β hβ)
      inv_mem' := by
        rintro y ⟨h1, h1'⟩
        refine ⟨Subgroup.inv_mem _ h1, fun β hβ => ?_⟩
        have e : ⁅y⁻¹, β⁆ = y⁻¹ * ⁅y, β⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact pg1_conj_of_mem (Subgroup.inv_mem _ h1) (T.inv_mem (h1' β hβ)) }
  have hS : P ⊔ Q ≤ S := sup_le (fun p hp => ⟨hP hp, hP2 p hp⟩) (fun q hq => ⟨hQ hq, hQ2 q hq⟩)
  rw [Subgroup.commutator_le]
  intro y hy β hβ
  exact (hS hy).2 β hβ

open scoped commutatorElement in
theorem pg1_comm_eq_one_of_centralizer {c b : G} (h : c ∈ Subgroup.centralizer ({b} : Set G)) :
    ⁅c, b⁆ = 1 := by
  have := Subgroup.mem_centralizer_iff.1 h b (by simp)
  simp only [commutatorElement_def]
  rw [← this]; group

open scoped commutatorElement in
theorem pg1_cen_le {B : Subgroup G} {c : G} (h : c ∈ Subgroup.centralizer (B : Set G))
    {b : G} (hb : b ∈ B) : c * b * c⁻¹ = b := by
  have := Subgroup.mem_centralizer_iff.1 h b hb
  rw [mul_inv_eq_iff_eq_mul, this]

open scoped commutatorElement in
theorem pg1_comm_mul (n β : G) : ⁅n, β⁆ = n * (β * n⁻¹ * β⁻¹) := by
  simp only [commutatorElement_def]; group

open scoped commutatorElement in
theorem pg1_conj_mul (n t : G) : n * t * n⁻¹ = (n * (t * n⁻¹ * t⁻¹)) * t := by group

theorem commutator_commutator_eq [Finite G] {p : ℕ} [Fact p.Prime] {Y B : Subgroup G}
    (hB : IsPGroup p B) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hY : Nat.Coprime p (Nat.card Y)) : ⁅⁅Y, B⁆, B⁆ = ⁅Y, B⁆ := by
  have hBM : B ≤ Subgroup.normalizer ((⁅Y, B⁆ : Subgroup G) : Set G) := by
    refine pg1_le_normalizer ⁅Y, B⁆ B (fun g hg t ht => ?_)
    exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_mem_commutator hBY hg ht
  apply le_antisymm
  · exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer hBM
  · have hY' := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
      hB hBY hY
    refine (Subgroup.commutator_mono hY' le_rfl).trans
      (pg1_comm_sup_le ⁅⁅Y, B⁆, B⁆ B _ ⁅Y, B⁆ ?_ ?_ ?_ ?_)
    · refine pg1_le_normalizer _ _ (fun c hc t ht => ?_)
      refine pg1_conj_comm c _ B (fun m hm => pg1_self_conj Y B c hc.1 m hm) (fun b hb => ?_) t ht
      rw [pg1_cen_le hc.2 hb]; exact hb
    · exact pg1_le_normalizer _ _ (fun m hm t ht => pg1_self_conj _ B m hm t ht)
    · intro c hc β hβ
      rw [pg1_comm_eq_one_of_centralizer
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hβ) hc.2)]
      exact Subgroup.one_mem _
    · intro m hm β hβ
      exact Subgroup.commutator_mem_commutator hm hβ

theorem eq_sup_commutator_of_mem [Finite G] {p : ℕ} [Fact p.Prime] {X B : Subgroup G} {x : G}
    (hB : IsPGroup p B) (hBc : IsMulCommutative B) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X)) (hxB : x ∈ B) (hXB : ⁅X, B⁆ = X) :
    X = ⁅X ⊓ Cen x, B⁆ ⊔ ⁅X, Subgroup.zpowers x⁆ := by
  have hZB : Subgroup.zpowers x ≤ B := (Subgroup.zpowers_le).2 hxB
  have hZp : IsPGroup p (Subgroup.zpowers x) := hB.to_le hZB
  have hZX : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set G) := hZB.trans hBX
  have hmain := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
    hZp hZX hX
  have hC : X ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ X ⊓ Cen x :=
    inf_le_inf_left _ (Subgroup.centralizer_le (by
      intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact Subgroup.mem_zpowers y))
  have hXle : X ≤ (X ⊓ Cen x) ⊔ ⁅X, Subgroup.zpowers x⁆ := hmain.trans (sup_le_sup_right hC _)
  have hNX : ∀ g ∈ X, ∀ t ∈ ⁅X, Subgroup.zpowers x⁆, g * t * g⁻¹ ∈ ⁅X, Subgroup.zpowers x⁆ :=
    pg1_self_conj X _
  have hNB : ∀ β ∈ B, ∀ t ∈ ⁅X, Subgroup.zpowers x⁆, β * t * β⁻¹ ∈ ⁅X, Subgroup.zpowers x⁆ := by
    intro β hβ
    refine pg1_conj_comm β X _ (fun m hm => (Subgroup.mem_normalizer_iff.1 (hBX hβ) m).1 hm)
      (fun z hz => ?_)
    have hc : β * z = z * β :=
      congrArg Subtype.val (hBc.is_comm.comm (⟨β, hβ⟩ : B) ⟨z, hZB hz⟩)
    rw [hc, mul_inv_cancel_right]; exact hz
  have hNle : ⁅X, Subgroup.zpowers x⁆ ≤ X := (Subgroup.commutator_mono le_rfl hZB).trans hXB.le
  have hCle : ⁅X ⊓ Cen x, B⁆ ≤ X := (Subgroup.commutator_mono inf_le_left le_rfl).trans hXB.le
  apply le_antisymm
  · calc X = ⁅X, B⁆ := hXB.symm
      _ ≤ ⁅(X ⊓ Cen x) ⊔ ⁅X, Subgroup.zpowers x⁆, B⁆ := Subgroup.commutator_mono hXle le_rfl
      _ ≤ ⁅X ⊓ Cen x, B⁆ ⊔ ⁅X, Subgroup.zpowers x⁆ := by
        refine pg1_comm_sup_le _ B _ _ ?_ ?_ ?_ ?_
        · refine pg1_le_normalizer _ _ (fun c hc t ht => ?_)
          refine pg1_sup_conj c _ _ (fun t ht => ?_) (fun t ht => ?_) t ht
          · exact Subgroup.mem_sup_left (pg1_self_conj _ B c hc t ht)
          · exact Subgroup.mem_sup_right (hNX c hc.1 t ht)
        · refine pg1_le_normalizer _ _ (fun n hn t ht => ?_)
          refine pg1_sup_conj n _ _ (fun t ht => ?_) (fun t ht => ?_) t ht
          · rw [pg1_conj_mul]
            exact Subgroup.mul_mem _
              (Subgroup.mem_sup_right (Subgroup.mul_mem _ hn (hNX t (hCle ht) _ (Subgroup.inv_mem _ hn))))
              (Subgroup.mem_sup_left ht)
          · exact Subgroup.mem_sup_right (hNX n (hNle hn) t ht)
        · intro c hc β hβ
          exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hc hβ)
        · intro n hn β hβ
          rw [pg1_comm_mul]
          exact Subgroup.mem_sup_right (Subgroup.mul_mem _ hn (hNB β hβ _ (Subgroup.inv_mem _ hn)))
  · exact sup_le hCle hNle

theorem me_exists_mul_of_mem_sup {L R : Subgroup G} (hn : R ≤ Subgroup.normalizer (L : Set G))
    {g : G} (hg : g ∈ L ⊔ R) : ∃ l ∈ L, ∃ r ∈ R, g = l * r := by
  let S : Subgroup G :=
    { carrier := {g | ∃ l ∈ L, ∃ r ∈ R, g = l * r}
      one_mem' := ⟨1, L.one_mem, 1, R.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, r₁, hr₁, rfl⟩ ⟨l₂, hl₂, r₂, hr₂, rfl⟩
        refine ⟨l₁ * (r₁ * l₂ * r₁⁻¹), L.mul_mem hl₁ ?_, r₁ * r₂, R.mul_mem hr₁ hr₂, by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hn hr₁) l₂).1 hl₂
      inv_mem' := by
        rintro _ ⟨l, hl, r, hr, rfl⟩
        refine ⟨r⁻¹ * l⁻¹ * r, ?_, r⁻¹, R.inv_mem hr, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hn (R.inv_mem hr)) l⁻¹).1 (L.inv_mem hl)
        simpa [mul_assoc] using this }
  have hLS : L ≤ S := fun l hl => ⟨l, hl, 1, R.one_mem, by simp⟩
  have hRS : R ≤ S := fun r hr => ⟨1, L.one_mem, r, hr, by simp⟩
  exact (sup_le hLS hRS) hg

theorem mem_of_mem_sup_of_pGroup [Finite G] {L R : Subgroup G}
    (hn : R ≤ Subgroup.normalizer (L : Set G)) (hR : ¬ 3 ∣ Nat.card R) {g : G}
    (hg : g ∈ L ⊔ R) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) : g ∈ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨l, hl, r, hr, rfl⟩ := me_exists_mul_of_mem_sup hn hg
  have hLN : L ≤ L ⊔ R := le_sup_left
  have hRN : R ≤ L ⊔ R := le_sup_right
  have hnorm : (L.subgroupOf (L ⊔ R)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).2
      (sup_le Subgroup.le_normalizer hn)
  let π := QuotientGroup.mk' (L.subgroupOf (L ⊔ R))
  have hlN : l ∈ L ⊔ R := hLN hl
  have hrN : r ∈ L ⊔ R := hRN hr
  have hπl : π ⟨l, hlN⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (Subgroup.mem_subgroupOf).2 hl
  have hgN : l * r ∈ L ⊔ R := (L ⊔ R).mul_mem hlN hrN
  have hπg : π ⟨l * r, hgN⟩ = π ⟨r, hrN⟩ := by
    have : (⟨l * r, hgN⟩ : ↥(L ⊔ R)) = ⟨l, hlN⟩ * ⟨r, hrN⟩ := rfl
    rw [this, map_mul, hπl, one_mul]
  obtain ⟨a, ha⟩ := hg3.exists_card_eq
  rw [Nat.card_zpowers] at ha
  have h1 : π ⟨l * r, hgN⟩ ^ (3 ^ a) = 1 := by
    rw [← map_pow]
    have : (⟨l * r, hgN⟩ : ↥(L ⊔ R)) ^ (3 ^ a) = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← ha]; exact pow_orderOf_eq_one _
    rw [this, map_one]
  have h2 : orderOf (π ⟨r, hrN⟩) ∣ 3 ^ a := by rw [← hπg]; exact orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (π ⟨r, hrN⟩) ∣ Nat.card R := by
    have h4 : orderOf (π ⟨r, hrN⟩) ∣ orderOf (⟨r, hrN⟩ : ↥(L ⊔ R)) := orderOf_map_dvd _ _
    have h5 : orderOf (⟨r, hrN⟩ : ↥(L ⊔ R)) = orderOf r := by
      rw [← Subgroup.orderOf_coe]
    have h6 : orderOf r ∣ Nat.card R := by
      have := orderOf_dvd_natCard (⟨r, hr⟩ : R)
      rwa [← Subgroup.orderOf_coe] at this
    exact h4.trans (h5 ▸ h6)
  have hcop : Nat.Coprime (orderOf (π ⟨r, hrN⟩)) 3 := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hR (h.trans h3))
  have h7 : orderOf (π ⟨r, hrN⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a hcop) h2
  have h8 : π ⟨r, hrN⟩ = 1 := orderOf_eq_one_iff.1 h7
  have h9 : π ⟨l * r, hgN⟩ = 1 := hπg.trans h8
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h9
  exact (Subgroup.mem_subgroupOf).1 h9

theorem relIndex_centralizer_le_three [Finite G] {B T : Subgroup G} {x : G}
    (hB : IsPGroup 3 B) (hT : Nat.card T ≤ 9) (hx : x ∈ T) (hx1 : x ≠ 1)
    (hBT : ∀ β ∈ B, β * x * β⁻¹ ∈ T) : (Cen x).relIndex B ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup B := (Cen x).subgroupOf B with hH
  let f : B ⧸ H → T := Quotient.lift (fun β : B => (⟨β.1 * x * β.1⁻¹, hBT β.1 β.2⟩ : T))
    (by
      intro a b hab
      have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
      have h1 : (a⁻¹ * b : B).1 ∈ Cen x := hab'
      have h2 : (a.1⁻¹ * b.1) * x = x * (a.1⁻¹ * b.1) := by
        simpa [Subgroup.mem_centralizer_iff, eq_comm] using h1
      simp only [Subtype.mk.injEq]
      calc a.1 * x * a.1⁻¹ = a.1 * (x * (a.1⁻¹ * b.1)) * b.1⁻¹ := by group
        _ = a.1 * ((a.1⁻¹ * b.1) * x) * b.1⁻¹ := by rw [h2]
        _ = b.1 * x * b.1⁻¹ := by group)
  have hf : Function.Injective f := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | _ a =>
    induction r using Quotient.inductionOn with
    | _ b =>
    have hh : a.1 * x * a.1⁻¹ = b.1 * x * b.1⁻¹ := by
      have := hqr
      simp only [f, Quotient.lift_mk, Subtype.mk.injEq] at this
      exact this
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    show (a⁻¹ * b : B).1 ∈ Cen x
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (a.1⁻¹ * b.1) * x = x * (a.1⁻¹ * b.1)
    calc (a.1⁻¹ * b.1) * x = a.1⁻¹ * (b.1 * x * b.1⁻¹) * a.1 * (a.1⁻¹ * b.1) := by group
      _ = x * (a.1⁻¹ * b.1) := by rw [← hh]; group
  have hne : ∀ q, f q ≠ (1 : T) := by
    intro q; induction q using Quotient.inductionOn with
    | _ a =>
    intro h
    have h' : a.1 * x * a.1⁻¹ = 1 := congrArg Subtype.val h
    exact hx1 (by simpa using h')
  let g : Option (B ⧸ H) → T := fun o => o.elim 1 f
  have hg : Function.Injective g := by
    intro o p hop
    cases o with
    | none =>
      cases p with
      | none => rfl
      | some q => exact absurd hop.symm (hne q)
    | some q =>
      cases p with
      | none => exact absurd hop (hne q)
      | some r => exact congrArg some (hf hop)
  have hcard : Nat.card (B ⧸ H) + 1 ≤ 9 := by
    have := Nat.card_le_card_of_injective g hg
    rw [Nat.card_congr (Equiv.optionEquivSumPUnit.{0, _} _), Nat.card_sum] at this
    simp at this
    omega
  have hidx : (Cen x).relIndex B = Nat.card (B ⧸ H) := by
    rw [Subgroup.relIndex, Subgroup.index]
  rw [hidx]
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hdvd : Nat.card (B ⧸ H) ∣ 3 ^ n := by
    rw [← hn]
    have := Subgroup.index_dvd_card H
    simpa [Subgroup.index] using this
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  rw [hjeq]
  by_contra hcon
  have : 2 ≤ j := by
    by_contra h2
    push Not at h2
    interval_cases j <;> simp at hcon
  have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) this
  omega

theorem exists_conj_pGroup [Finite G] {B Z : Subgroup G} (hB : IsPGroup 3 B)
    (hBZ : B ≤ Subgroup.normalizer (Z : Set G)) {x : G} (hx : x ∈ Z)
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) :
    ∃ n ∈ Z, IsPGroup 3 ↥(B ⊔ Subgroup.zpowers (n * x * n⁻¹)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprod : ∀ g ∈ Z ⊔ B, ∃ z ∈ Z, ∃ b ∈ B, g = z * b := by
    let K : Subgroup G :=
      { carrier := {g | ∃ z ∈ Z, ∃ b ∈ B, g = z * b}
        one_mem' := ⟨1, Z.one_mem, 1, B.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨z1, hz1, b1, hb1, rfl⟩ ⟨z2, hz2, b2, hb2, rfl⟩
          refine ⟨z1 * (b1 * z2 * b1⁻¹), Z.mul_mem hz1 ?_, b1 * b2, B.mul_mem hb1 hb2, by group⟩
          exact (Subgroup.mem_normalizer_iff.1 (hBZ hb1) z2).1 hz2
        inv_mem' := by
          rintro _ ⟨z, hz, b, hb, rfl⟩
          refine ⟨b⁻¹ * z⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
          have h := (Subgroup.mem_normalizer_iff.1 (hBZ (B.inv_mem hb)) z⁻¹).1 (Z.inv_mem hz)
          simpa using h }
    have : Z ⊔ B ≤ K := sup_le (fun z hz => ⟨z, hz, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, Z.one_mem, b, hb, by simp⟩)
    exact fun g hg => this hg
  set H : Subgroup G := Z ⊔ B with hH
  have hZH : Z ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hBp : IsPGroup 3 (B.subgroupOf H) := hB.comap_subtype
  obtain ⟨P, hBP⟩ := hBp.exists_le_sylow
  have hxp : IsPGroup 3 ((Subgroup.zpowers x).subgroupOf H) := hx3.comap_subtype
  obtain ⟨Q, hxQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P Q
  obtain ⟨z, hz, b, hb, hgzb⟩ := hprod g.1 g.2
  refine ⟨z⁻¹, Z.inv_mem hz, ?_⟩
  have hxH : x ∈ H := hZH hx
  have hxQ' : (⟨x, hxH⟩ : H) ∈ (Q : Subgroup H) :=
    hxQ (by show x ∈ Subgroup.zpowers x; exact Subgroup.mem_zpowers x)
  rw [← hg] at hxQ'
  have hgP : g⁻¹ * ⟨x, hxH⟩ * g ∈ (P : Subgroup H) := by
    have h1 : (⟨x, hxH⟩ : H) ∈ ((g • P : Sylow 3 H) : Subgroup H) := hxQ'
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have : t = g⁻¹ * ⟨x, hxH⟩ * g := by
      rw [← hts]; simp [MulAut.smul_def, mul_assoc]
    exact this ▸ ht
  set P' : Subgroup G := (P : Subgroup H).map H.subtype with hP'
  have hBP' : B ≤ P' := by
    intro c hc
    exact ⟨⟨c, hBH hc⟩, hBP (show (⟨c, hBH hc⟩ : H) ∈ B.subgroupOf H from hc), rfl⟩
  have hbP' : b ∈ P' := hBP' hb
  have hgx : g.1⁻¹ * x * g.1 ∈ P' := ⟨_, hgP, rfl⟩
  have hn : z⁻¹ * x * z⁻¹⁻¹ ∈ P' := by
    have h := P'.mul_mem (P'.mul_mem hbP' hgx) (P'.inv_mem hbP')
    have e : z⁻¹ * x * z⁻¹⁻¹ = b * (g.1⁻¹ * x * g.1) * b⁻¹ := by
      rw [hgzb]; group
    rw [e]; exact h
  have hP'p : IsPGroup 3 P' := (P.2).map _
  refine IsPGroup.to_le hP'p (sup_le hBP' ?_)
  rw [Subgroup.zpowers_le]; exact hn

theorem conj_eq_of_card_three {Z : Subgroup G} (hZ : Nat.card Z = 3) {d : G} (hd : d ^ 3 = 1)
    (hdZ : d ∈ Subgroup.normalizer (Z : Set G)) : ∀ z ∈ Z, d * z * d⁻¹ = z := by
  have hp : Fact (Nat.Prime (Nat.card Z)) := ⟨hZ ▸ Nat.prime_three⟩
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨⟨z0, hz0Z⟩, hgen⟩ := hcyc.exists_generator
  have hord : orderOf z0 = 3 := by
    have : orderOf (⟨z0, hz0Z⟩ : Z) = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hZ]
    simpa using this
  have hZeq : ∀ z ∈ Z, ∃ m : ℤ, z0 ^ m = z := by
    intro z hz
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨z, hz⟩)
    exact ⟨m, congrArg Subtype.val hm⟩
  obtain ⟨k, hk⟩ := hZeq (d * z0 * d⁻¹) ((Subgroup.mem_normalizer_iff.1 hdZ z0).1 hz0Z)
  have hpow : ∀ (j : ℕ), d ^ j * z0 * (d ^ j)⁻¹ = z0 ^ (k ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : d ^ (j + 1) * z0 * (d ^ (j + 1))⁻¹ = d ^ j * (d * z0 * d⁻¹) * (d ^ j)⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [this, ← hk]
      have h2 : d ^ j * z0 ^ k * (d ^ j)⁻¹ = (d ^ j * z0 * (d ^ j)⁻¹) ^ k := by
        rw [← conj_zpow]
      rw [h2, ih, ← zpow_mul, pow_succ, mul_comm]
  have h3 := hpow 3
  rw [hd] at h3
  have h3' : z0 ^ (k ^ 3) = z0 ^ (1 : ℤ) := by
    rw [zpow_one, ← h3]; simp
  rw [zpow_eq_zpow_iff_modEq, hord] at h3'
  have hk1 : k ≡ 1 [ZMOD 3] := by
    have h5 : ((k : ZMod 3)) ^ 3 = 1 := by
      have := (ZMod.intCast_eq_intCast_iff _ _ 3).2 h3'
      simpa using this
    have h6 : ∀ a : ZMod 3, a ^ 3 = 1 → a = 1 := by decide
    have := h6 _ h5
    exact (ZMod.intCast_eq_intCast_iff k 1 3).1 (by simpa using this)
  have hk' : z0 ^ k = z0 ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, hord]; exact hk1
  rw [zpow_one] at hk'
  have hdz0 : d * z0 * d⁻¹ = z0 := by rw [← hk, hk']
  intro z hz
  obtain ⟨m, rfl⟩ := hZeq z hz
  rw [← conj_zpow, hdz0]

theorem exists_elemAbelian_ge [Finite G] {B : Subgroup G} (hB : IsElemAbelian 3 B) {x : G}
    (hx3 : x ^ 3 = 1) (hidx : (Cen x).relIndex B ≤ 3) :
    ∃ B' : Subgroup G, IsElemAbelian 3 B' ∧ B' ≤ Cen x ∧
      CFSG.Open.pRank 3 B ≤ CFSG.Open.pRank 3 B' ∧ B ⊓ Cen x ≤ B' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 (B ⊓ Cen x) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => hB.2 y hy.1⟩
    have := hB.1.is_comm.comm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
    simpa using congrArg Subtype.val this
  have hcomm : ∀ a ∈ B ⊓ Cen x, a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 ha.2
  have hB'el := isElemAbelian_sup_zpowers hAel hx3 hcomm
  have hxC : x ∈ Cen x := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hle : (B ⊓ Cen x) ⊔ Subgroup.zpowers x ≤ Cen x :=
    sup_le inf_le_right (Subgroup.zpowers_le.2 hxC)
  refine ⟨_, hB'el, hle, ?_, le_sup_left⟩
  have hpg : ∀ E : Subgroup G, IsElemAbelian 3 E → ∃ k, Nat.card E = 3 ^ k := by
    intro E hE
    have : IsPGroup 3 E := fun g => ⟨1, by
      apply Subtype.ext; simpa using hE.2 g.1 g.2⟩
    exact this.exists_card_eq
  obtain ⟨a, ha⟩ := hpg B hB
  obtain ⟨b, hb⟩ := hpg _ hB'el
  rw [pRank_eq_of_card Nat.prime_three hB ha, pRank_eq_of_card Nat.prime_three hB'el hb]
  have hcard : Nat.card B ≤ Nat.card ↥((B ⊓ Cen x) ⊔ Subgroup.zpowers x) := by
    by_cases hxB : x ∈ B
    · have hBle : B ≤ B ⊓ Cen x := by
        intro c hc
        refine ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have := hB.1.is_comm.comm ⟨c, hc⟩ ⟨x, hxB⟩
        simpa using congrArg Subtype.val this
      exact Subgroup.card_le_of_le (hBle.trans le_sup_left)
    · have hxn : x ∉ B ⊓ Cen x := fun h => hxB h.1
      rw [card_sup_zpowers_of_pow_three_eq_one hx3 hxn hcomm]
      have h1 := Subgroup.relIndex_mul_card (H := Cen x) (K := B)
      rw [inf_comm] at h1
      nlinarith [h1, hidx, Nat.card_pos (α := ↥(B ⊓ Cen x))]
  rw [ha, hb] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

theorem eq_one_of_mem_core_of_pGroup [Finite G] {X : Subgroup G} {g : G}
    (hg : g ∈ GLAPPrimeCoreOf 3 X) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) : g = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg3.exists_card_eq
  have hdvd : Nat.card (Subgroup.zpowers g) ∣ Nat.card (GLAPPrimeCoreOf 3 X) :=
    Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).2 hg)
  by_contra hne
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, pow_zero, Nat.card_zpowers] at hk
    exact hne (orderOf_eq_one_iff.1 hk)
  exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three X ((dvd_pow_self 3 hk0).trans (hk ▸ hdvd))

theorem Cen_conj (n x : G) : Cen (n * x * n⁻¹) = GLBConj n⁻¹ (Cen x) := by
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simp only [inv_inv]
    have := congrArg (fun t => n⁻¹ * t * n) h
    simpa [mul_assoc] using this
  · intro h
    simp only [inv_inv] at h
    have := congrArg (fun t => n * t * n⁻¹) h
    simpa [mul_assoc] using this

end PureGroup

section CenHelpers

open Matrix

variable {K : Type} [Field K]

theorem cen_card_center_statedSL_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (Subgroup.center ↥(StatedSL 3 K)) = 3 :=
  CFSG.Open.StatedCenterThree.card_center_statedSL_three h3

theorem cen_card_center_statedSU_three [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (h3 : 3 ∣ q + 1) :
    Nat.card (Subgroup.center ↥(StatedSU 3 q K)) = 3 :=
  CFSG.Open.StatedCenterThree.card_center_statedSU_three hK h3

end CenHelpers

theorem card_center_exc {Y : Type*} [Group Y] (h : IsSLThreeExc Y ∨ IsSUThreeExc Y) :
    Nat.card (Subgroup.center Y) = 3 := by
  rcases h with ⟨K, _, _, hK, ⟨e⟩⟩ | ⟨K, _, _, q, hK, hq, ⟨e⟩⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact cen_card_center_statedSL_three (by omega)
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact cen_card_center_statedSU_three hK (by omega)


section ConjLemmas

variable {G : Type*} [Group G]

theorem bClosure_eq_of_isBConjugate {B L L' : Subgroup G} (hB : IsMulCommutative B)
    (h : IsBConjugate B L L') : bClosure B L' = bClosure B L := by
  obtain ⟨g₀, hg₀, rfl⟩ := h
  unfold bClosure
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) (g₀ * g) (B.mul_mem hg₀ hg)
  · refine iSup₂_le fun g hg => ?_
    have : GLBConj g L = GLBConj (g₀⁻¹ * g) (GLBConj g₀ L) := by
      rw [gLBConj_gLBConj]; simp
    rw [this]
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b (GLBConj g₀ L)) (g₀⁻¹ * g)
      (B.mul_mem (B.inv_mem hg₀) hg)

theorem conj_gLBConj_commutator (g : G) (A B : Subgroup G) :
    GLBConj g ⁅A, B⁆ = ⁅GLBConj g A, GLBConj g B⁆ := by
  unfold GLBConj
  exact Subgroup.map_commutator _ _ _

theorem conj_gLBConj_inf (g : G) (A B : Subgroup G) :
    GLBConj g (A ⊓ B) = GLBConj g A ⊓ GLBConj g B := by
  unfold GLBConj
  exact Subgroup.map_inf _ _ (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem setup_conj [Finite G] {B D : Subgroup G} {b : G} {L L' : Subgroup G}
    (hs : Lemma24Setup 3 B D b L) (h : IsBConjugate B L L') : Lemma24Setup 3 B D b L' := by
  obtain ⟨g₀, hg₀, rfl⟩ := h
  have hB : IsElemAbelian 3 B := hs.isBOneMax.1.1
  have hDB : D ≤ B := hs.isEk.1
  have hcom : g₀ * b = b * g₀ := elemAbelian_comm hB hg₀ hs.mem
  have hCb : GLBConj g₀ (Subgroup.centralizer ({b} : Set G)) =
      Subgroup.centralizer ({b} : Set G) := gLBConj_centralizer_singleton_of_commute hcom
  have hΔ : GLBConj g₀ (GLADelta 3 D) = GLADelta 3 D :=
    mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_gLADelta hB hDB hg₀)
  have hBB : GLBConj g₀ B = B := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg₀)
  have hX : GLBConj g₀ (delta2At 3 B D b) = delta2At 3 B D b := by
    unfold delta2At
    rw [conj_gLBConj_commutator, conj_gLBConj_inf, hΔ, hCb, hBB]
  have hO : GLBConj g₀ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) =
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
    rw [← glaPPrimeCoreOf_gLBConj, hCb]
  refine ⟨hs.isBOneMax, hs.isEk, hs.mem, hs.ne_one, hs.not_le, ?_, ?_⟩
  · have := glaPComponent_gLBConj g₀ hs.isComp
    rwa [hCb] at this
  · intro hle
    apply hs.not_centralizes
    have h1 : GLBConj g₀ ⁅L, delta2At 3 B D b⁆ ≤
        GLBConj g₀ (GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) := by
      rw [hO]
      rw [conj_gLBConj_commutator, hX]
      exact hle
    have h2 := gLBConj_mono g₀⁻¹ h1
    rwa [gLBConj_inv_gLBConj, gLBConj_inv_gLBConj] at h2

theorem oPrimePOf_gLBConj [Finite G] (p : ℕ) (g : G) (X : Subgroup G) :
    oPrimePOf p (GLBConj g X) = GLBConj g (oPrimePOf p X) := by
  have hmap : oPrimeP p ↥(GLBConj g X) = (oPrimeP p ↥X).map (conjEquiv g X).toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := (conjEquiv g X).surjective y
    have hq := QuotientGroup.congr_mk (GLAPPrimeCore p ↥X) (GLAPPrimeCore p ↥(GLBConj g X))
      (conjEquiv g X) (glaPPrimeCore_map_iso p (conjEquiv g X)) x
    have hc : (CFSG.pCore p (↥(GLBConj g X) ⧸ GLAPPrimeCore p ↥(GLBConj g X))) =
        (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)).map (conjQuotEquiv p g X).toMonoidHom :=
      (CFSG.pCore_map_iso p (conjQuotEquiv p g X)).symm
    constructor
    · intro hy
      refine ⟨x, ?_, rfl⟩
      have hy' : QuotientGroup.mk' (GLAPPrimeCore p ↥(GLBConj g X)) (conjEquiv g X x) ∈
          CFSG.pCore p (↥(GLBConj g X) ⧸ GLAPPrimeCore p ↥(GLBConj g X)) := hy
      rw [hc] at hy'
      have : QuotientGroup.mk' (GLAPPrimeCore p ↥(GLBConj g X)) (conjEquiv g X x) =
          conjQuotEquiv p g X (QuotientGroup.mk' (GLAPPrimeCore p ↥X) x) := by
        exact hq.symm
      rw [this] at hy'
      obtain ⟨z, hz, hz'⟩ := hy'
      have := (conjQuotEquiv p g X).injective hz'
      subst this
      exact hz
    · rintro ⟨x', hx', hx'e⟩
      have hx : x' = x := (conjEquiv g X).injective hx'e
      subst hx
      have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) x' ∈
          CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := hx'
      show QuotientGroup.mk' (GLAPPrimeCore p ↥(GLBConj g X)) (conjEquiv g X x') ∈
          CFSG.pCore p (↥(GLBConj g X) ⧸ GLAPPrimeCore p ↥(GLBConj g X))
      rw [hc]
      refine ⟨_, h1, ?_⟩
      exact hq.symm
  have hf : (GLBConj g X).subtype.comp (conjEquiv g X).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp X.subtype := by
    ext t
    simp
  unfold oPrimePOf
  rw [hmap, Subgroup.map_map, hf, ← Subgroup.map_map]
  rfl

theorem conj_le_oPrimePOf_of_pow_mem [Finite G] {p : ℕ} (hp : p.Prime) {H S N₀ : Subgroup G}
    (hSH : S ≤ H) (hS : (S.subgroupOf H).Normal) (hNH : N₀ ≤ H) (hN : (N₀.subgroupOf H).Normal)
    (hcop : Nat.Coprime p (Nat.card N₀)) (hpow : ∀ s ∈ S, ∃ n : ℕ, s ^ (p ^ n) ∈ N₀) :
    S ≤ oPrimePOf p H := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop' : Nat.Coprime p (Nat.card (N₀.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact hcop
  have hN0 : N₀.subgroupOf H ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hN, hcop'⟩
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥H) with hπ
  set Sb : Subgroup (↥H ⧸ GLAPPrimeCore p ↥H) := (S.subgroupOf H).map π with hSb
  have hSbn : Sb.Normal := hS.map π (QuotientGroup.mk'_surjective _)
  have hSbp : IsPGroup p Sb := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    obtain ⟨n, hn⟩ := hpow (s : G) (Subgroup.mem_subgroupOf.1 hs)
    have h1 : π s ^ (p ^ n) = 1 := by
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).2
      apply hN0
      exact Subgroup.mem_subgroupOf.2 (by simpa using hn)
    have h2 : orderOf (⟨π s, ⟨s, hs, rfl⟩⟩ : Sb) ∣ p ^ n := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h2
    exact ⟨k, hk⟩
  have hle : Sb ≤ CFSG.pCore p (↥H ⧸ GLAPPrimeCore p ↥H) :=
    le_sSup ⟨hSbn, hSbp⟩
  intro s hs
  refine ⟨⟨s, hSH hs⟩, ?_, rfl⟩
  exact hle ⟨⟨s, hSH hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩

theorem conj_pow_mem_of_mem_oPrimePOf [Finite G] {p : ℕ} (hp : p.Prime) {X : Subgroup G} {s : G}
    (hs : s ∈ oPrimePOf p X) : ∃ n : ℕ, s ^ (p ^ n) ∈ GLAPPrimeCoreOf p X := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht, rfl⟩ := hs
  have hpg : IsPGroup p (CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hpg ⟨_, ht⟩
  refine ⟨k, t ^ (p ^ k), ?_, rfl⟩
  have h1 : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥X) t) = p ^ k := by
    have := Subgroup.orderOf_coe (⟨_, ht⟩ : CFSG.pCore p (↥X ⧸ GLAPPrimeCore p ↥X))
    rw [hk] at this
    exact this
  have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) t ^ (p ^ k) = 1 := by
    rw [← h1]; exact pow_orderOf_eq_one _
  rw [← map_pow] at h2
  exact (QuotientGroup.eq_one_iff _).1 h2

theorem conj_oPrimePOf_le_of_normal [Finite G] {p : ℕ} (hp : p.Prime) {L M : Subgroup G}
    (hLM : L ≤ M) (hn : (L.subgroupOf M).Normal) : oPrimePOf p L ≤ oPrimePOf p M := by
  have hML : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hn
  have hSL : oPrimePOf p L ≤ L := Subgroup.map_subtype_le _
  have hS : ((oPrimePOf p L).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hSL.trans hLM)]
    intro m hm
    rw [mem_normalizer_iff_gLBConj_eq, ← oPrimePOf_gLBConj,
      mem_normalizer_iff_gLBConj_eq.1 (hML hm)]
  have hNM : GLAPPrimeCoreOf p M ≤ M := Subgroup.map_subtype_le _
  have hN : ((GLAPPrimeCoreOf p M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNM]
    intro m hm
    rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj,
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hm)]
  refine conj_le_oPrimePOf_of_pow_mem hp (hSL.trans hLM) hS hNM hN
    ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp M)) ?_
  intro s hs
  obtain ⟨n, hn'⟩ := conj_pow_mem_of_mem_oPrimePOf hp hs
  exact ⟨n, glaPPrimeCoreOf_le_of_normal hp hLM hn hn'⟩

theorem oPrimePOf_le_of_isSubnormal [Finite G] {p : ℕ} (hp : p.Prime) {L X : Subgroup G}
    (h : IsSubnormal L X) : oPrimePOf p L ≤ oPrimePOf p X := by
  induction h with
  | refl => exact le_rfl
  | step hHM hn _ ih => exact (conj_oPrimePOf_le_of_normal hp hHM hn).trans ih

theorem glaPLayer_gLBConj [Finite G] (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  have hle : ∀ (g : G) (X : Subgroup G),
      GLBConj g (GLAPLayer p X) ≤ GLAPLayer p (GLBConj g X) := by
    intro g X
    refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun L hL => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_gLBConj g hL)
  refine le_antisymm ?_ (hle g X)
  have h1 := hle g⁻¹ (GLBConj g X)
  rw [gLBConj_inv_gLBConj] at h1
  have h2 := gLBConj_mono g h1
  rwa [gLBConj_gLBConj_inv] at h2

theorem glaPComponent_of_isSubnormal [Finite G] {p : ℕ} (hp : p.Prime) {Y H J : Subgroup G}
    (hH : IsSubnormal H Y) (hJ : GLAPComponent p H J) : GLAPComponent p Y J := by
  obtain ⟨hJN, hsn, hcomp, hmin⟩ := hJ
  have hHY : H ≤ Y := by
    clear hmin hcomp hsn hJN
    induction hH with
    | refl => exact le_rfl
    | step hHM _ _ ih => exact hHM.trans ih
  have hsnH : IsSubnormal J Y := isSubnormal_trans' hsn hH
  have hJH : J ≤ Y := hJN.trans hHY
  refine ⟨hJH, hsnH, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := Y) p hsnH
    rwa [barX_self] at this
  · have e : ↥(barX p H J) ≃* ↥(barX p Y J) :=
      (quotEquivBarX hp hJN hsn).symm.trans (quotEquivBarX hp hJH hsnH)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hJ'N : IsSubnormal J' H := isSubnormal_of_le_of_le hJ'sn (hJ'J.trans hJN) hHY
    have hcore : J ⊓ GLAPPrimeCoreOf p Y ≤ GLAPPrimeCoreOf p H := by
      rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hH]
      exact inf_le_inf_right _ hJN
    refine hmin J' hlt hJ'N ?_
    show barX p H J' = barX p H J
    refine le_antisymm (barX_mono p hJ'J) ?_
    refine barX_le_of_forall (hJ'J.trans hJN) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := Y) (le_of_eq heq.symm) hk (hJH hk)
    exact ⟨j, hj, hcore ⟨J.mul_mem (J.inv_mem (hJ'J hj)) hk, hjk⟩⟩

theorem isExc_of_equiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsSLThreeExc Y ∨ IsSUThreeExc Y) : IsSLThreeExc Y' ∨ IsSUThreeExc Y' := by
  rcases h with ⟨K, _, _, hK, ⟨f⟩⟩ | ⟨K, _, _, q, hK, hq, ⟨f⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, hK, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨K, inferInstance, inferInstance, q, hK, hq, ⟨e.symm.trans f⟩⟩

end ConjLemmas

section Config

variable {G : Type*} [Group G]

@[expose] def Jof (x : G) (L : Subgroup G) : Subgroup G :=
  GLAPLayer 3 (L ⊓ Cen x)

@[expose] def Jstar (x : G) (L : Subgroup G) : Subgroup G :=
  ⨆ g ∈ GLAPLayer 3 (Cen x), GLBConj g (Jof x L)

structure Config (b x : G) (L : Subgroup G) : Prop where
  comp : GLAPComponent 3 (Cen b) L
  hx : x ∈ Cen b
  ord : orderOf x = 3
  cen : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Cen b)

variable [Finite G]

omit [Finite G] in
theorem cf1_comm {b x : G} {L : Subgroup G} (h : Config b x L) {l : G} (hl : l ∈ L) :
    l⁻¹ * x⁻¹ * l * x ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  apply h.cen
  have := Subgroup.commutator_mem_commutator (H₁ := L) (H₂ := Subgroup.zpowers x)
    (L.inv_mem hl) (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  simpa [commutatorElement_def, mul_assoc] using this

omit [Finite G] in
theorem cf1_nontrivial {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) : Nontrivial Q := by
  have := hQ.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem cf1_eq_top {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) : K = ⊤ := by
  obtain ⟨-, hsn, hKq⟩ := hK
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hsn' : IsSubnormal (K.map π) ⊤ := by
    have := isSubnormal_map' π hsn
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at this
  have hcases : K.map π = ⊤ ∨ K.map π = ⊥ := by
    by_cases hne : K.map π = ⊤
    · exact Or.inl hne
    · right
      obtain ⟨M, hKM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hsn' hne
      have hMn' : M.Normal := by
        have := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hMn
        rwa [top_le_iff, Subgroup.normalizer_eq_top_iff] at this
      rcases hMn'.eq_bot_or_eq_top with h | h
      · exact le_bot_iff.1 (h ▸ hKM)
      · exact absurd h hMne
  rcases hcases with htop | hbot
  ·
    have hc : ∀ a : Q, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.center Q := by
      intro a
      have : π a ∈ K.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hka⟩ := this
      exact ⟨k, hk, (QuotientGroup.eq).1 hka⟩
    have hcomm : commutator Q ≤ K := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      obtain ⟨k1, hk1, hz1⟩ := hc a
      obtain ⟨k2, hk2, hz2⟩ := hc b
      set z1 := k1⁻¹ * a with hz1d
      set z2 := k2⁻¹ * b with hz2d
      have ha : a = k1 * z1 := by simp [hz1d]
      have hb : b = k2 * z2 := by simp [hz2d]
      have c1 := Subgroup.mem_center_iff.1 hz1
      have c2 := Subgroup.mem_center_iff.1 hz2
      have e : a * b * a⁻¹ * b⁻¹ = k1 * k2 * k1⁻¹ * k2⁻¹ := by
        rw [ha, hb]
        have e1 : z1 * k2 = k2 * z1 := (c1 k2).symm
        have e2 : z1 * z2 = z2 * z1 := (c1 z2).symm
        have e3 : z2 * k1⁻¹ = k1⁻¹ * z2 := (c2 k1⁻¹).symm
        calc k1 * z1 * (k2 * z2) * (k1 * z1)⁻¹ * (k2 * z2)⁻¹
            = k1 * (z1 * k2) * z2 * z1⁻¹ * k1⁻¹ * z2⁻¹ * k2⁻¹ := by group
          _ = k1 * (k2 * z1) * z2 * z1⁻¹ * k1⁻¹ * z2⁻¹ * k2⁻¹ := by rw [e1]
          _ = k1 * k2 * (z1 * z2 * z1⁻¹) * k1⁻¹ * z2⁻¹ * k2⁻¹ := by group
          _ = k1 * k2 * z2 * k1⁻¹ * z2⁻¹ * k2⁻¹ := by
              rw [e2]; group
          _ = k1 * k2 * (z2 * k1⁻¹) * z2⁻¹ * k2⁻¹ := by group
          _ = k1 * k2 * (k1⁻¹ * z2) * z2⁻¹ * k2⁻¹ := by rw [e3]
          _ = k1 * k2 * k1⁻¹ * k2⁻¹ := by group
      rw [commutatorElement_def, e]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk1 hk2) (K.inv_mem hk1)) (K.inv_mem hk2)
    rw [eq_top_iff, ← hQ.1]
    exact hcomm
  · exfalso
    have := hKq.2
    have : Nontrivial (↥K ⧸ Subgroup.center ↥K) := inferInstance
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥K ⧸ Subgroup.center ↥K)
    induction q using QuotientGroup.induction_on with
    | H k =>
      apply hq
      refine (QuotientGroup.eq_one_iff k).2 (Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_)
      have h1 : π k.1 ∈ K.map π := ⟨k.1, k.2, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact (Subgroup.mem_center_iff.1 h1) g.1

theorem Config.mem_normalizer {b x : G} {L : Subgroup G} (h : Config b x L) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  have hn : x ∈ Subgroup.normalizer ((Cen b : Subgroup G) : Set G) := Subgroup.le_normalizer h.hx
  have h1 : GLAPComponent 3 (Cen b) (GLBConj x L) := by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj h.comp x
    rwa [gLBConj_eq_of_mem_normalizer hn] at this
  have hbar : barX 3 (Cen b) L = barX 3 (Cen b) (GLBConj x L) := by
    refine le_antisymm ?_ ?_
    · refine barX_le_of_forall h1.1 (fun k hk => ?_)
      refine ⟨x⁻¹ * k * x, mem_gLBConj.2 (by simpa [mul_assoc] using hk), ?_⟩
      have := Subgroup.inv_mem _ (cf1_comm h hk)
      convert this using 1
      group
    · refine barX_le_of_forall h.comp.1 (fun k hk => ?_)
      have hk' : x * k * x⁻¹ ∈ L := mem_gLBConj.1 hk
      refine ⟨x * k * x⁻¹, hk', ?_⟩
      have := cf1_comm h hk'
      convert this using 1
      group
  have := glaPComponent_unique h.comp h1 hbar
  exact mem_normalizer_iff_gLBConj_eq.2 this.symm

theorem cf1_cover_aux {b x : G} {L : Subgroup G} (h : Config b x L) :
    ∀ l ∈ L, ∃ v ∈ GLAPPrimeCoreOf 3 L, l * v ∈ Cen x := by
  intro l hl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxn := h.mem_normalizer
  have hd : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord]; simp)
  have hVp := not_dvd_card_glaPPrimeCoreOf Nat.prime_three L
  have hdV : x ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq, ← glaPPrimeCoreOf_gLBConj, gLBConj_eq_of_mem_normalizer hxn]
  have hxV : l ∈ Subgroup.normalizer ((GLAPPrimeCoreOf 3 L : Subgroup G) : Set G) :=
    le_normalizer_glaPPrimeCoreOf 3 L hl
  have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three h.comp.2.1
  have hx : x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    rw [← hinf]
    refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.1 hxn l).1 hl) (L.inv_mem hl), ?_⟩
    have hm : x * l⁻¹ * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hxn l⁻¹).1 (L.inv_mem hl)
    have := cf1_comm h hm
    have e : x * l * x⁻¹ * l⁻¹ = (x * l⁻¹ * x⁻¹)⁻¹ * x⁻¹ * (x * l⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact this
  exact exists_mul_mem_centralizer hd hVp hdV hxV hx

theorem cf1_psi_surj {b x : G} {L : Subgroup G} (h : Config b x L) :
    Function.Surjective ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L))) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H l =>
    obtain ⟨v, hv, hlv⟩ := cf1_cover_aux h l.1 l.2
    obtain ⟨v', hv', hv'v⟩ := hv
    have hmem : (l : G) * v ∈ L ⊓ Cen x :=
      ⟨L.mul_mem l.2 (hv'v ▸ v'.2), hlv⟩
    refine ⟨⟨l * v, hmem⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have : Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L) ⟨l * v, hmem⟩ = l * v' :=
      Subtype.ext (by simp [← hv'v])
    rw [this]
    simpa using (GLAPPrimeCore 3 ↥L).inv_mem hv'

theorem cf1_psi_ker {b x : G} {L : Subgroup G} (h : Config b x L) :
    ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L))).ker =
      GLAPPrimeCore 3 ↥(L ⊓ Cen x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L)) with hψ
  have hsurj : Function.Surjective ψ := cf1_psi_surj h
  have hker : ∀ k : ↥(L ⊓ Cen x), k ∈ ψ.ker ↔
      Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L) k ∈ GLAPPrimeCore 3 ↥L := by
    intro k
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  refine le_antisymm ?_ ?_
  · have hcop : Nat.Coprime 3 (Nat.card ψ.ker) := by
      have h1 : Nat.card ψ.ker =
          Nat.card (ψ.ker.map (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L))) :=
        (Subgroup.card_map_of_injective (Subgroup.inclusion_injective _)).symm
      have h2 : ψ.ker.map (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L)) ≤
          GLAPPrimeCore 3 ↥L := by
        rintro _ ⟨k, hk, rfl⟩
        exact (hker k).1 hk
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h2) CFSG.pPrimeCore_coprime_card
    exact le_sSup ⟨MonoidHom.normal_ker ψ, hcop⟩
  · intro n hn
    have hnS : ((GLAPPrimeCore 3 ↥(L ⊓ Cen x)).map ψ).Normal :=
      (GLAPPrimeCore.normal 3 _).map ψ hsurj
    have hcS : Nat.Coprime 3 (Nat.card ((GLAPPrimeCore 3 ↥(L ⊓ Cen x)).map ψ)) :=
      by
      have h1 := Subgroup.card_map_dvd (GLAPPrimeCore 3 ↥(L ⊓ Cen x)) ψ
      have h2 : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥(L ⊓ Cen x))) :=
        CFSG.pPrimeCore_coprime_card
      exact Nat.Coprime.coprime_dvd_right h1 h2
    have hS : (GLAPPrimeCore 3 ↥(L ⊓ Cen x)).map ψ ≤ GLAPPrimeCore 3 (↥L ⧸ GLAPPrimeCore 3 ↥L) :=
      le_sSup (s := {N : Subgroup (↥L ⧸ GLAPPrimeCore 3 ↥L) | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
        ⟨hnS, hcS⟩
    rw [glaPPrimeCore_quotient_eq_bot Nat.prime_three] at hS
    have := hS ⟨n, hn, rfl⟩
    exact this

theorem cf1_O_le {b x : G} {L : Subgroup G} (h : Config b x L) :
    GLAPPrimeCoreOf 3 (L ⊓ Cen x) ≤ GLAPPrimeCoreOf 3 L := by
  rintro _ ⟨n, hn, rfl⟩
  have h2 : Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L) n ∈ GLAPPrimeCore 3 ↥L := by
    have hn' : n ∈ ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
      (Subgroup.inclusion (inf_le_left : L ⊓ Cen x ≤ L))).ker := by
      rw [cf1_psi_ker h]; exact hn
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      at hn'
    exact hn'
  exact ⟨_, h2, rfl⟩

theorem cf1_quasi {b x : G} {L : Subgroup G} (h : Config b x L) :
    CFSG.Open.IsQuasisimple (↥(L ⊓ Cen x) ⧸ GLAPPrimeCore 3 ↥(L ⊓ Cen x)) := by
  have hker := cf1_psi_ker h
  have e : (↥(L ⊓ Cen x) ⧸ GLAPPrimeCore 3 ↥(L ⊓ Cen x)) ≃* (↥L ⧸ GLAPPrimeCore 3 ↥L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (cf1_psi_surj h))
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm
    (isQuasisimple_quotient_of_glaPComponent h.comp)

theorem cf1_J {b x : G} {L : Subgroup G} (h : Config b x L) :
    ∃ J₀ : Subgroup G, GLAPComponent 3 (L ⊓ Cen x) J₀ ∧ barX 3 (L ⊓ Cen x) J₀ = ⊤ ∧
      Jof x L = J₀ := by
  have Hq := cf1_quasi h
  have htop : IsComponentOf (⊤ : Subgroup (↥(L ⊓ Cen x) ⧸ GLAPPrimeCore 3 ↥(L ⊓ Cen x))) ⊤ :=
    ⟨le_top, IsSubnormal.refl _,
      CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
        Subgroup.topEquiv.symm Hq⟩
  obtain ⟨J₀, hJ₀, hbar⟩ := exists_glaPComponent_barX_eq (p := 3) (L ⊓ Cen x) htop
  have hall : ∀ J' : Subgroup G, GLAPComponent 3 (L ⊓ Cen x) J' → barX 3 (L ⊓ Cen x) J' = ⊤ :=
    fun J' hJ' => cf1_eq_top Hq hJ'.2.2.1
  refine ⟨J₀, hJ₀, hbar, ?_⟩
  unfold Jof GLAPLayer
  have : {J' : Subgroup G | GLAPComponent 3 (L ⊓ Cen x) J'} = {J₀} := by
    ext J'
    refine ⟨fun hJ' => ?_, fun e => ?_⟩
    · exact glaPComponent_unique hJ' hJ₀ (by rw [hall J' hJ', hbar])
    · rw [Set.mem_singleton_iff.1 e]; exact hJ₀
  rw [this, sSup_singleton]

theorem Config.cover {b x : G} {L : Subgroup G} (h : Config b x L) :
    L ≤ Jof x L ⊔ GLAPPrimeCoreOf 3 L := by
  obtain ⟨J₀, -, hbar, hJ⟩ := cf1_J h
  rw [hJ]
  intro l hl
  obtain ⟨v, hv, hlv⟩ := cf1_cover_aux h l hl
  have hvL : v ∈ L := Subgroup.map_subtype_le _ hv
  have hmem : l * v ∈ L ⊓ Cen x := ⟨L.mul_mem hl hvL, hlv⟩
  have hle : barX 3 (L ⊓ Cen x) (L ⊓ Cen x) ≤ barX 3 (L ⊓ Cen x) J₀ := by
    rw [barX_self, hbar]
  obtain ⟨j, hj, hjk⟩ := exists_of_barX_le hle hmem hmem
  have hr : j⁻¹ * (l * v) ∈ GLAPPrimeCoreOf 3 L := cf1_O_le h hjk
  have e : l = j * ((j⁻¹ * (l * v)) * v⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hj
    ((GLAPPrimeCoreOf 3 L).mul_mem hr ((GLAPPrimeCoreOf 3 L).inv_mem hv))

theorem Config.jcomp_inf {b x : G} {L : Subgroup G} (h : Config b x L) :
    GLAPComponent 3 (L ⊓ Cen x) (Jof x L) := by
  obtain ⟨J₀, hJ₀, -, hJ⟩ := cf1_J h
  rw [hJ]
  exact hJ₀

theorem Config.jcomp {b x : G} {L : Subgroup G} (h : Config b x L) :
    GLAPComponent 3 (Cen x ⊓ Cen b) (Jof x L) := by
  have h1 := isSubnormal_inf h.comp.2.1 (Cen x)
  rw [inf_comm (Cen b) (Cen x)] at h1
  exact glaPComponent_of_isSubnormal Nat.prime_three h1 h.jcomp_inf

theorem cf2_inf_le {p : ℕ} (hp : p.Prime) {H A : Subgroup G} (hHA : H ≤ A) :
    H ⊓ GLAPPrimeCoreOf p A ≤ GLAPPrimeCoreOf p H := by
  set O := GLAPPrimeCoreOf p A with hO
  set N0 : Subgroup ↥H := O.subgroupOf H with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥H) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf p A (hHA h'.2)) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map H.subtype = H ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O H]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ H ≤ H)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map H.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp A (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore p ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

theorem cf2_exists_mul {J R : Subgroup G} (hJR : J ≤ Subgroup.normalizer (R : Set G)) {g : G}
    (hg : g ∈ J ⊔ R) : ∃ j ∈ J, ∃ r ∈ R, j * r = g := by
  have hy' : g ∈ ((J ⊔ R : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J R hJR] at hy'
  exact Set.mem_mul.mp hy'

theorem cf2_mem_core_iff {p : ℕ} {L : Subgroup G} (x : ↥L) :
    x ∈ GLAPPrimeCore p ↥L ↔ (x : G) ∈ GLAPPrimeCoreOf p L := by
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

@[expose] noncomputable def cf2_hom (p : ℕ) {J L : Subgroup G} (hJL : J ≤ L) : ↥J →* barOf p L :=
  (QuotientGroup.mk' (GLAPPrimeCore p ↥L)).comp (Subgroup.inclusion hJL)

theorem cf2_hom_apply (p : ℕ) {J L : Subgroup G} (hJL : J ≤ L) (j : ↥J) :
    cf2_hom p hJL j = QuotientGroup.mk (⟨(j : G), hJL j.2⟩ : ↥L) := rfl

theorem cf2_hom_surjective (p : ℕ) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) : Function.Surjective (cf2_hom p hJL) := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have hJR : J ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) :=
    hJL.trans (le_normalizer_glaPPrimeCoreOf p L)
  obtain ⟨j, hj, r, hr, hjr⟩ := cf2_exists_mul hJR (hcov l.2)
  refine ⟨⟨j, hj⟩, ?_⟩
  rw [cf2_hom_apply, QuotientGroup.eq]
  have h1 : (⟨j, hJL hj⟩ : ↥L)⁻¹ * l = ⟨r, (by
      have : r = j⁻¹ * l := by rw [← hjr]; simp
      rw [this]; exact L.mul_mem (L.inv_mem (hJL hj)) l.2)⟩ := by
    apply Subtype.ext; simp [← hjr]
  rw [h1, cf2_mem_core_iff]
  exact hr

theorem cf2_mem_ker_iff (p : ℕ) {J L : Subgroup G} (hJL : J ≤ L) (j : ↥J) :
    j ∈ (cf2_hom p hJL).ker ↔ (j : G) ∈ GLAPPrimeCoreOf p L := by
  rw [MonoidHom.mem_ker, cf2_hom_apply, QuotientGroup.eq_one_iff, cf2_mem_core_iff]

theorem cf2_ker_eq {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) :
    (cf2_hom p hJL).ker = GLAPPrimeCore p ↥J := by
  have hsurj := cf2_hom_surjective p hJL hcov
  have hcop : Nat.Coprime p (Nat.card (cf2_hom p hJL).ker) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    refine not_dvd_card_glaPPrimeCoreOf hp L (hd.trans ?_)
    rw [← Subgroup.card_map_of_injective J.subtype_injective]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨j, hj, rfl⟩
    exact (cf2_mem_ker_iff p hJL j).1 hj
  refine le_antisymm (le_sSup ⟨MonoidHom.normal_ker _, hcop⟩) ?_
  have h1 := glaPPrimeCore_map_of_surjective hp (cf2_hom p hJL) hsurj hcop
  rw [glaPPrimeCore_quotient_eq_bot hp] at h1
  intro j hj
  have : cf2_hom p hJL j ∈ (⊥ : Subgroup (barOf p L)) := h1 ▸ Subgroup.mem_map_of_mem _ hj
  exact this

theorem cf2_coreOf_eq {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) :
    GLAPPrimeCoreOf p J = J ⊓ GLAPPrimeCoreOf p L := by
  refine le_antisymm ?_ (cf2_inf_le hp hJL)
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j.2, ?_⟩
  show (j : G) ∈ GLAPPrimeCoreOf p L
  rw [← cf2_mem_ker_iff p hJL j, cf2_ker_eq hp hJL hcov]
  exact hj

theorem Config.barOf_equiv {b x : G} {L : Subgroup G} (h : Config b x L) :
    Nonempty (barOf 3 (Jof x L) ≃* barOf 3 L) := by
  have hJL : Jof x L ≤ L := h.jcomp_inf.1.trans inf_le_left
  have hcov := h.cover
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (cf2_ker_eq Nat.prime_three hJL hcov).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (cf2_hom_surjective 3 hJL hcov))⟩

theorem cf2_H_decomp {b x : G} {L : Subgroup G} (h : Config b x L) {y : G}
    (hy : y ∈ L ⊓ Cen x) : ∃ j ∈ Jof x L, j⁻¹ * y ∈ GLAPPrimeCoreOf 3 (L ⊓ Cen x) := by
  have hJH : Jof x L ≤ L ⊓ Cen x := h.jcomp_inf.1
  have hHL : L ⊓ Cen x ≤ L := inf_le_left
  have hcov : L ≤ (L ⊓ Cen x) ⊔ GLAPPrimeCoreOf 3 L :=
    h.cover.trans (sup_le_sup_right hJH _)
  have hcore := cf2_coreOf_eq Nat.prime_three hHL hcov
  have hJR : Jof x L ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
    (hJH.trans hHL).trans (le_normalizer_glaPPrimeCoreOf 3 L)
  obtain ⟨j, hj, r, hr, hjr⟩ := cf2_exists_mul hJR (h.cover hy.1)
  refine ⟨j, hj, ?_⟩
  have hr' : r = j⁻¹ * y := by rw [← hjr]; simp
  rw [← hr', hcore]
  refine ⟨?_, hr⟩
  rw [hr']
  exact (L ⊓ Cen x).mul_mem ((L ⊓ Cen x).inv_mem (hJH hj)) hy

theorem cf2_normalizer_J {b x : G} {L : Subgroup G} (h : Config b x L) :
    L ⊓ Cen x ≤ Subgroup.normalizer (Jof x L : Set G) := by
  have hJH : Jof x L ≤ L ⊓ Cen x := h.jcomp_inf.1
  have htop : barX 3 (L ⊓ Cen x) (Jof x L) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← barX_self 3 (L ⊓ Cen x)]
    refine barX_le_of_forall hJH fun k hk => ?_
    exact cf2_H_decomp h hk
  have hmem : ∀ g ∈ L ⊓ Cen x, g ∈ preimBarX 3 (L ⊓ Cen x) (Jof x L) := by
    intro g hg
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ _ ∈ (barX 3 (L ⊓ Cen x) (Jof x L))
    rw [htop]; trivial
  have hn := glaPComponent_normal_preimBarX h.jcomp_inf
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 3 hJH)).1 hn
  exact fun g hg => hle (hmem g hg)

theorem Config.three_mem_J {b x : G} {L : Subgroup G} (h : Config b x L) {y : G}
    (hyL : y ∈ L) (hyx : y ∈ Cen x) (hy3 : IsPGroup 3 (Subgroup.zpowers y)) :
    y ∈ Jof x L := by
  have hy : y ∈ L ⊓ Cen x := ⟨hyL, hyx⟩
  obtain ⟨j, hj, hr⟩ := cf2_H_decomp h hy
  have hJH : Jof x L ≤ L ⊓ Cen x := h.jcomp_inf.1
  have hOH : GLAPPrimeCoreOf 3 (L ⊓ Cen x) ≤ L ⊓ Cen x := Subgroup.map_subtype_le _
  have hysup : y ∈ Jof x L ⊔ GLAPPrimeCoreOf 3 (L ⊓ Cen x) := by
    have : y = j * (j⁻¹ * y) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hj hr
  exact mem_of_mem_sup_of_pGroup ((hOH.trans (cf2_normalizer_J h)))
    (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _) hysup hy3

@[expose] noncomputable def cf2_equiv {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) : barOf p J ≃* barOf p L :=
  (QuotientGroup.quotientMulEquivOfEq (cf2_ker_eq hp hJL hcov).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (cf2_hom_surjective p hJL hcov))

theorem cf2_equiv_mk {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) (j : ↥J) :
    cf2_equiv hp hJL hcov (QuotientGroup.mk j) = QuotientGroup.mk (⟨(j : G), hJL j.2⟩ : ↥L) :=
  rfl

theorem cf2_mem_oPrimeP {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L)
    (hcov : L ≤ J ⊔ GLAPPrimeCoreOf p L) {y : G} (hyJ : y ∈ J) (hyL : y ∈ oPrimePOf p L) :
    y ∈ oPrimePOf p J := by
  obtain ⟨y', hy', hyy'⟩ := hyL
  refine ⟨⟨y, hyJ⟩, ?_, rfl⟩
  set e := cf2_equiv hp hJL hcov with he
  have h1 : QuotientGroup.mk (⟨y, hJL hyJ⟩ : ↥L) ∈ CFSG.pCore p (barOf p L) := by
    have : y' = ⟨y, hJL hyJ⟩ := Subtype.ext hyy'
    exact this ▸ hy'
  rw [← CFSG.pCore_map_iso p e, Subgroup.mem_map_equiv] at h1
  have h3 : e.symm (QuotientGroup.mk (⟨y, hJL hyJ⟩ : ↥L)) = QuotientGroup.mk (⟨y, hyJ⟩ : ↥J) :=
    e.symm_apply_eq.2 rfl
  rw [h3] at h1
  exact h1

theorem Config.mem_oPrimeP_J {b x : G} {L : Subgroup G} (h : Config b x L) {y : G}
    (hyL : y ∈ L) (hyx : y ∈ Cen x) (hy3 : IsPGroup 3 (Subgroup.zpowers y))
    (hyz : y ∈ oPrimePOf 3 L) : y ∈ oPrimePOf 3 (Jof x L) :=
  cf2_mem_oPrimeP Nat.prime_three (h.jcomp_inf.1.trans inf_le_left) h.cover
    (h.three_mem_J hyL hyx hy3) hyz

theorem cf2_normalizes_core {p : ℕ} {L : Subgroup G} {z : G}
    (hz : z ∈ Subgroup.normalizer (L : Set G)) :
    z ∈ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq] at hz ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hz]

theorem cf2_normalizer_Jof {x : G} {L : Subgroup G} {z : G}
    (hzL : z ∈ Subgroup.normalizer (L : Set G)) (hzx : z ∈ Cen x) :
    z ∈ Subgroup.normalizer (Jof x L : Set G) := by
  have hH : GLBConj z (L ⊓ Cen x) = L ⊓ Cen x := by
    ext y
    rw [mem_gLBConj]
    have h1 := (Subgroup.mem_normalizer_iff.1 hzL y)
    have h2 := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hzx) y)
    simp only [Subgroup.mem_inf]
    rw [← h1, ← h2]
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold Jof
  rw [← glaPLayer_gLBConj, hH]

theorem cf2_le_Jstar {x : G} {L : Subgroup G} : Jof x L ≤ Jstar x L := by
  have h1 : (1 : G) ∈ GLAPLayer 3 (Cen x) := one_mem _
  unfold Jstar
  have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cen x)) => GLBConj g (Jof x L)) 1 h1
  simpa [gLBConj_one] using this

theorem Config.transfer {b x : G} {L : Subgroup G} (h : Config b x L) {Z : Subgroup G}
    (hZ : Z ≤ Subgroup.normalizer (L : Set G) ⊓ Cen x)
    (hJ : ⁅Jstar x L, Z⁆ ≤ GLAPPrimeCoreOf 3 (Cen x)) :
    ⁅L, Z⁆ ≤ GLAPPrimeCoreOf 3 (Cen b) := by
  have hJH : Jof x L ≤ L ⊓ Cen x := h.jcomp_inf.1
  have hJL : Jof x L ≤ L := hJH.trans inf_le_left
  have hJx : Jof x L ≤ Cen x := hJH.trans inf_le_right
  have hcov := h.cover
  have hcore := cf2_coreOf_eq Nat.prime_three hJL hcov
  have hjz : ∀ j ∈ Jof x L, ∀ z ∈ Z, j * z * j⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    intro j hj z hz
    have hzJ := cf2_normalizer_Jof (hZ hz).1 (hZ hz).2
    have h1 : j * z * j⁻¹ * z⁻¹ ∈ Jof x L := by
      have : j * z * j⁻¹ * z⁻¹ = j * (z * j⁻¹ * z⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hj
        ((Subgroup.mem_normalizer_iff.1 hzJ j⁻¹).1 (Subgroup.inv_mem _ hj))
    have h2 : j * z * j⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen x) :=
      hJ (Subgroup.commutator_mem_commutator (cf2_le_Jstar hj) hz)
    have h3 : j * z * j⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Jof x L) :=
      cf2_inf_le Nat.prime_three hJx ⟨h1, h2⟩
    rw [hcore] at h3
    exact h3.2
  have hLZ : ∀ l ∈ L, ∀ z ∈ Z, l * z * l⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    intro l hl z hz
    have hJR : Jof x L ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 L : Set G) :=
      hJL.trans (le_normalizer_glaPPrimeCoreOf 3 L)
    obtain ⟨j, hj, r, hr, rfl⟩ := cf2_exists_mul hJR (hcov hl)
    have hzR := cf2_normalizes_core (p := 3) (hZ hz).1
    have hjL : j ∈ L := hJL hj
    have t1 : z * r⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      (Subgroup.mem_normalizer_iff.1 hzR r⁻¹).1 (Subgroup.inv_mem _ hr)
    have t2 : r * (z * r⁻¹ * z⁻¹) ∈ GLAPPrimeCoreOf 3 L := Subgroup.mul_mem _ hr t1
    have t3 : j * (r * (z * r⁻¹ * z⁻¹)) * j⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 L hjL) _).1 t2
    have : j * r * z * (j * r)⁻¹ * z⁻¹ =
        (j * (r * (z * r⁻¹ * z⁻¹)) * j⁻¹) * (j * z * j⁻¹ * z⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ t3 (hjz j hj z hz)
  refine (Subgroup.commutator_le.2 fun l hl z hz => hLZ l hl z hz).trans ?_
  exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
    h.comp.2.1

end Config


section Claim

variable {G : Type} [Group G] [Finite G]

theorem exists_family (h18 : Input18_3_4) {m : ℕ} (hS : GLStanding G m 3) {b x : G}
    {L : Subgroup G} (h : Config b x L) (hb3 : b ^ 3 = 1) :
    ∃ 𝒞 : Set (Subgroup G), (∀ L' ∈ 𝒞, GLAPComponent 3 (Cen x) L') ∧
      (⨆ L' ∈ 𝒞, L') = Jstar x L ∧
      (∀ L' ∈ 𝒞, ∀ e ∈ Subgroup.zpowers b, GLBConj e L' ∈ 𝒞) ∧
      ∀ L' ∈ 𝒞, ∀ L'' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers b, GLBConj e L' = L'' := by
  have hs := hS.simple
  have hx1 : x ≠ 1 := by
    rintro rfl
    have := h.ord
    rw [orderOf_one] at this
    omega
  have hne : Cen x ≠ ⊤ := centralizer_ne_top_of_simple hS.nonabelian hx1
  have hbx : b ∈ Cen x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 h.hx).symm
  have hE : Subgroup.zpowers b ≤ Cen x := by
    rw [Subgroup.zpowers_le]; exact hbx
  have hEl : IsElemAbelian 3 (Subgroup.zpowers b) := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 c.2
      apply Subtype.ext
      show (a : G) * c = c * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [hb3]
  have hcen : Cen x ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Cen x ⊓ Cen b := by
    congr 1
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hy b (Subgroup.mem_zpowers b)
    · intro hy g hg
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      have hc : b * y = y * b := hy b rfl
      exact ((Commute.zpow_left (show Commute b y from hc) i)).eq
  have hJ : GLAPComponent 3 (Cen x ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G))
      (Jof x L) := by
    rw [hcen]; exact h.jcomp
  exact h18 G (Cen x) (isKGroup_of_isKProper hS.kProper hne) 3 Nat.prime_three
    (Subgroup.zpowers b) hE hEl (Jof x L) hJ

theorem fixed_of_mem_iSup {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, GLAPComponent 3 X L) {b : G} (hbX : b ∈ X) (hb : b ∈ ⨆ L ∈ 𝒞, L) :
    ∀ L ∈ 𝒞, b ∈ Subgroup.normalizer (L : Set G) := by
  intro L hL
  have hle : (⨆ L' ∈ 𝒞, L') ≤ Subgroup.normalizer (L : Set G) := by
    refine iSup₂_le fun L' hL' => ?_
    by_cases hne : L = L'
    · subst hne; exact Subgroup.le_normalizer
    · exact fun g hg => mem_normalizer_of_ne Nat.prime_three (h𝒞 L hL) (h𝒞 L' hL') hne hg
  exact hle hb

theorem comp_of_fixed {X : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, GLAPComponent 3 X L) {b : G}
    (htr : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers b, GLBConj e L = L')
    (hfix : ∀ L ∈ 𝒞, b ∈ Subgroup.normalizer (L : Set G)) (hne : (⨆ L ∈ 𝒞, L) ≠ ⊥) :
    GLAPComponent 3 X (⨆ L ∈ 𝒞, L) ∧ b ∈ Subgroup.normalizer ((⨆ L ∈ 𝒞, L : Subgroup G) : Set G) := by
  obtain ⟨L₀, hL₀⟩ : 𝒞.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    apply hne
    rw [hemp]
    simp
  have hsup : (⨆ L ∈ 𝒞, L) = L₀ := by
    apply le_antisymm
    · refine iSup₂_le fun L hL => ?_
      obtain ⟨e, he, rfl⟩ := htr L₀ hL₀ L hL
      have : e ∈ Subgroup.normalizer (L₀ : Set G) :=
        (Subgroup.zpowers_le.2 (hfix L₀ hL₀)) he
      rw [mem_normalizer_iff_gLBConj_eq.1 this]
    · exact le_iSup₂ (f := fun L' (_ : L' ∈ 𝒞) => L') L₀ hL₀
  rw [hsup]
  exact ⟨h𝒞 L₀ hL₀, hfix L₀ hL₀⟩

theorem Config.Jof_ne_bot {b x : G} {L : Subgroup G} (h : Config b x L) : Jof x L ≠ ⊥ := by
  obtain ⟨J₀, -, hbar, hJ⟩ := cf1_J h
  rw [hJ]
  rintro rfl
  have hnt := cf1_nontrivial (cf1_quasi h)
  have : barX 3 (L ⊓ Cen x) (⊥ : Subgroup G) = ⊥ := by
    unfold barX
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [this] at hbar
  exact (bot_ne_top (α := Subgroup _)) hbar

omit [Finite G] in
theorem Config.Jof_le_Jstar {b x : G} {L : Subgroup G} : Jof x L ≤ Jstar x L := by
  unfold Jstar
  refine le_iSup₂_of_le 1 (Subgroup.one_mem _) ?_
  rw [gLBConj_one]

theorem claim_eq_top_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q] {K : Subgroup Q}
    (hsn : IsSubnormal K ⊤) (hK : Nontrivial K) : K = ⊤ := by
  by_contra hne
  obtain ⟨M, hKM, -, hMne, hMn, -⟩ := isSubnormal_exists_normal hsn hne
  have hMn' : M.Normal := by
    have := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hMn
    rwa [top_le_iff, Subgroup.normalizer_eq_top_iff] at this
  rcases hMn'.eq_bot_or_eq_top with h | h
  · obtain ⟨k, hk⟩ := exists_ne (1 : K)
    have := hKM k.2
    rw [h, Subgroup.mem_bot] at this
    exact hk (Subtype.ext this)
  · exact hMne h

theorem claim_no_simple_exc {Y Y' : Type*} [Group Y] [Group Y'] [IsSimpleGroup Y] (e : Y ≃* Y')
    (hq : CFSG.Open.IsQuasisimple Y') (hexc : IsSLThreeExc Y' ∨ IsSUThreeExc Y') : False := by
  have hQY : CFSG.Open.IsQuasisimple Y :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq
  have hc3 : Nat.card (Subgroup.center Y) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_exc hexc
  have hnormal : (Subgroup.center Y).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h0 | h0
  · rw [h0] at hc3
    simp at hc3
  · have hcomm : ∀ a b : Y, a * b = b * a := fun a b =>
      Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a
    have hle : commutator Y ≤ ⊥ := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_def]
      have := hcomm a b
      rw [this]
      group
    rw [hQY.1] at hle
    have hsub : Subsingleton (Subgroup.center Y) :=
      ⟨fun a b => Subtype.ext (by
        have h1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_top (a : Y)))
        have h2 := Subgroup.mem_bot.1 (hle (Subgroup.mem_top (b : Y)))
        rw [h1, h2])⟩
    rw [Nat.card_of_subsingleton (1 : Subgroup.center Y)] at hc3
    omega

theorem fixed_of_B' (h112 : Input11_2_2) {m : ℕ} (hS : GLStanding G m 3) {b x : G}
    {L : Subgroup G} (h : Config b x L) {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L' ∈ 𝒞, GLAPComponent 3 (Cen x) L') (hsup : (⨆ L' ∈ 𝒞, L') = Jstar x L)
    (hcl : ∀ L' ∈ 𝒞, ∀ e ∈ Subgroup.zpowers b, GLBConj e L' ∈ 𝒞)
    (htr : ∀ L' ∈ 𝒞, ∀ L'' ∈ 𝒞, ∃ e ∈ Subgroup.zpowers b, GLBConj e L' = L'')
    {B' : Subgroup G} (hB' : IsElemAbelian 3 B') (hB'x : B' ≤ Cen x)
    (hrk : GLATwoLocalRank 3 ↥(Cen x) ≤ CFSG.Open.pRank 3 B') (hbB' : b ∈ B')
    (hexc : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) :
    ∀ C₀ ∈ 𝒞, b ∈ Subgroup.normalizer (C₀ : Set G) := by
  intro C₀ hC₀
  by_contra hbn
  have hC₀c := h𝒞 C₀ hC₀
  obtain ⟨e⟩ := h112 G m 3 hS (Cen x) B' C₀ hB' hB'x hrk hC₀c b hbB' hbn
  set K₁ := GLAPLayer 3 (bClosure B' C₀ ⊓ Cen b) with hK₁
  have hzp : Subgroup.zpowers b ≤ B' := Subgroup.zpowers_le.2 hbB'
  have hBcl : ∀ L' ∈ 𝒞, L' ≤ bClosure B' C₀ := by
    intro L' hL'
    obtain ⟨e, he, rfl⟩ := htr C₀ hC₀ L' hL'
    exact le_iSup₂ (f := fun (g : G) (_ : g ∈ B') => GLBConj g C₀) e (hzp he)
  have hJ_le_cl : Jof x L ≤ bClosure B' C₀ := by
    have : Jof x L ≤ Jstar x L := cf2_le_Jstar
    rw [← hsup] at this
    exact this.trans (iSup₂_le hBcl)
  have hcl_cen : bClosure B' C₀ ≤ Cen x := by
    refine iSup₂_le fun g hg => ?_
    have hgx : g ∈ Cen x := hB'x hg
    have := gLBConj_mono g hC₀c.1
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hgx)] at this
  have hJL : Jof x L ≤ L := h.jcomp_inf.1.trans inf_le_left
  have hJb : Jof x L ≤ Cen b := hJL.trans h.comp.1
  have hJA : Jof x L ≤ bClosure B' C₀ ⊓ Cen b := le_inf hJ_le_cl hJb
  have hAle : bClosure B' C₀ ⊓ Cen b ≤ Cen x ⊓ Cen b := inf_le_inf_right _ hcl_cen
  have hJcompA : GLAPComponent 3 (bClosure B' C₀ ⊓ Cen b) (Jof x L) :=
    glaPComponent_of_le Nat.prime_three h.jcomp hJA hAle
  have hJK₁ : Jof x L ≤ K₁ := le_sSup hJcompA
  have hK₁A : K₁ ≤ bClosure B' C₀ ⊓ Cen b := sSup_le fun L' hL' => hL'.1
  have hJcompK : GLAPComponent 3 K₁ (Jof x L) :=
    glaPComponent_of_le Nat.prime_three hJcompA hJK₁ hK₁A
  have hqs : IsSimpleGroup (barOf 3 C₀ ⧸ Subgroup.center (barOf 3 C₀)) :=
    (isQuasisimple_quotient_of_glaPComponent hC₀c).2
  haveI hsimp : IsSimpleGroup (↥K₁ ⧸ GLAPPrimeCore 3 ↥K₁) := e.isSimpleGroup
  obtain ⟨-, hsn, hq⟩ := hJcompK.2.2.1
  have hbarTop : barX 3 K₁ (Jof x L) = ⊤ :=
    claim_eq_top_of_simple hsn (cf1_nontrivial hq)
  let e2 : barOf 3 (Jof x L) ≃* ↥(barX 3 K₁ (Jof x L)) :=
    quotEquivBarX Nat.prime_three hJK₁ hJcompK.2.1
  let e3 : ↥(barX 3 K₁ (Jof x L)) ≃* (↥K₁ ⧸ GLAPPrimeCore 3 ↥K₁) :=
    (MulEquiv.subgroupCongr hbarTop).trans Subgroup.topEquiv
  haveI : IsSimpleGroup (barOf 3 (Jof x L)) := (e2.trans e3).isSimpleGroup
  exact claim_no_simple_exc h.barOf_equiv.some
    (isQuasisimple_quotient_of_glaPComponent h.comp) hexc

theorem claim_ii (h18 : Input18_3_4) (h112 : Input11_2_2) {m : ℕ} (hS : GLStanding G m 3)
    {b x : G} {L : Subgroup G} (h : Config b x L) (hb3 : b ^ 3 = 1)
    (hexc : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L))
    (hcase : b ∈ Jof x L ∨ ∃ B' : Subgroup G, IsElemAbelian 3 B' ∧ B' ≤ Cen x ∧
      GLATwoLocalRank 3 ↥(Cen x) ≤ CFSG.Open.pRank 3 B' ∧ b ∈ B') :
    GLAPComponent 3 (Cen x) (Jstar x L) ∧ b ∈ Subgroup.normalizer (Jstar x L : Set G) := by
  obtain ⟨𝒞, h𝒞, hsup, hcl, htr⟩ := exists_family h18 hS h hb3
  have hbx : b ∈ Cen x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 h.hx).symm
  have hfix : ∀ C ∈ 𝒞, b ∈ Subgroup.normalizer (C : Set G) := by
    rcases hcase with hbJ | ⟨B', hB', hB'x, hrk, hbB'⟩
    · exact fixed_of_mem_iSup h𝒞 hbx (hsup ▸ (Config.Jof_le_Jstar (b := b)) hbJ)
    · exact fixed_of_B' h112 hS h h𝒞 hsup hcl htr hB' hB'x hrk hbB' hexc
  have hne : (⨆ L' ∈ 𝒞, L') ≠ ⊥ := by
    rw [hsup]
    exact fun h0 => h.Jof_ne_bot (le_bot_iff.1 (h0 ▸ (Config.Jof_le_Jstar (b := b))))
  have := comp_of_fixed h𝒞 htr hfix hne
  rw [hsup] at this
  exact this

end Claim


section PartI

variable {G : Type*} [Group G] [Finite G]

theorem parti_B_le_cen {B : Subgroup G} (hB : IsElemAbelian 3 B) {b : G} (hb : b ∈ B) :
    B ≤ Cen b := fun _ hb' =>
  Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hb' hb)

theorem parti_cq_conj {L R : Subgroup G} {w y : G} (hwL : w ∈ Subgroup.normalizer (L : Set G))
    (hwR : w ∈ Subgroup.normalizer (R : Set G)) (hy : y ∈ centralizerQuot L R) :
    w * y * w⁻¹ ∈ centralizerQuot L R := by
  obtain ⟨hyL, hyR, hy'⟩ := hy
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwL hyL) (Subgroup.inv_mem _ hwL)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwR hyR) (Subgroup.inv_mem _ hwR)
  · have hl' : w⁻¹ * l * w ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hwL) l).1 hl
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hwR _).1 (hy' _ hl')
    have e : l * (w * y * w⁻¹) * l⁻¹ * (w * y * w⁻¹)⁻¹ =
        w * ((w⁻¹ * l * w) * y * (w⁻¹ * l * w)⁻¹ * y⁻¹) * w⁻¹ := by group
    rw [e]
    exact h1

theorem parti_x_mem_cq {b x : G} {L : Subgroup G} (h : Config b x L) :
    x ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  have hxn := h.mem_normalizer
  have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three h.comp.2.1
  refine ⟨hxn, cf2_normalizes_core hxn, fun l hl => ?_⟩
  rw [← hinf]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 hxn l⁻¹).1 (L.inv_mem hl)
    have e : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [e]; exact L.mul_mem hl this
  · apply h.cen
    have := Subgroup.commutator_mem_commutator (H₁ := L) (H₂ := Subgroup.zpowers x)
      hl (Subgroup.mem_zpowers x)
    simpa [commutatorElement_def] using this

theorem parti_le_cq {b x : G} {L : Subgroup G} (h : Config b x L) {Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (L : Set G)) (hYR : ⁅L, Y⁆ ≤ GLAPPrimeCoreOf 3 (Cen b)) :
    Y ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  have hinf := glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three h.comp.2.1
  intro y hy
  refine ⟨hY hy, cf2_normalizes_core (hY hy), fun l hl => ?_⟩
  rw [← hinf]
  refine ⟨?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.1 (hY hy) l⁻¹).1 (L.inv_mem hl)
    have e : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
    rw [e]; exact L.mul_mem hl this
  · exact hYR (Subgroup.commutator_mem_commutator hl hy)

theorem parti_N_le_cq {b x : G} {L : Subgroup G} (h : Config b x L) {X : Subgroup G}
    (hXn : X ≤ Subgroup.normalizer (L : Set G)) :
    ⁅X, Subgroup.zpowers x⁆ ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
  rw [Subgroup.commutator_le]
  intro w hw y hy
  have hyS : y ∈ centralizerQuot L (GLAPPrimeCoreOf 3 L) :=
    Subgroup.zpowers_le.2 (parti_x_mem_cq h) hy
  have := parti_cq_conj (hXn hw) (cf2_normalizes_core (hXn hw)) hyS
  rw [commutatorElement_def]
  have e : w * y * w⁻¹ * y⁻¹ = (w * y * w⁻¹) * y⁻¹ := rfl
  exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hyS)

theorem parti_comm_le_of_cq {b x : G} {L : Subgroup G} (h : Config b x L) {X : Subgroup G}
    (hX : X ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L)) :
    ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 (Cen b) := by
  refine ((Subgroup.commutator_le).2 fun l hl w hw => (hX hw).2.2 l hl).trans ?_
  exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three
    h.comp.2.1

theorem not_centralizes_i {B D : Subgroup G} {b x : G} {L : Subgroup G}
    (hB : IsBOneMax 3 B) (hD : IsEkIn 3 2 B D) (hb : b ∈ B) (hxB : x ∈ B)
    (h : Config b x L) (hXn : delta2At 3 B D b ≤ Subgroup.normalizer (L : Set G))
    (hX : ¬ ⁅L, delta2At 3 B D b⁆ ≤ GLAPPrimeCoreOf 3 (Cen b)) :
    ¬ ⁅Jstar x L, delta2At 3 B D x⁆ ≤ GLAPPrimeCoreOf 3 (Cen x) := by
  intro hJY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hBp : IsPGroup 3 B := fun g => ⟨1, by
    apply Subtype.ext; simpa using hBel.2 g.1 g.2⟩
  have hDne : D ≠ ⊥ := by
    intro h0
    have h1 := hD.2.2
    rw [h0, Subgroup.card_bot] at h1
    have h2 : 1 < 3 ^ 2 := by norm_num
    omega
  have hDcop := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta
    (G := G) Nat.prime_three hDne
  have hBbc : B ≤ Cen b := parti_B_le_cen hBel hb
  have hBxc : B ≤ Cen x := parti_B_le_cen hBel hxB
  have hBΔ : B ≤ Subgroup.normalizer (GLADelta 3 D : Set G) :=
    le_normalizer_gLADelta hBel hD.1
  set W : Subgroup G := GLADelta 3 D ⊓ Cen b with hW
  have hWΔ : W ≤ GLADelta 3 D := inf_le_left
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := by
    refine pg1_le_normalizer W B (fun g hg t ht => ⟨pg1_conj_of_mem (hBΔ hg) ht.1, ?_⟩)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBbc hg) ht.2) (Subgroup.inv_mem _ (hBbc hg))
  have hWcop : Nat.Coprime 3 (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hWΔ) hDcop
  have hXdef : delta2At 3 B D b = ⁅W, B⁆ := rfl
  have hXle : delta2At 3 B D b ≤ GLADelta 3 D := delta2At_le_gLADelta hBel hD.1 b
  have hXcop : Nat.Coprime 3 (Nat.card (delta2At 3 B D b)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXle) hDcop
  have hBX : B ≤ Subgroup.normalizer ((delta2At 3 B D b : Subgroup G) : Set G) := by
    refine pg1_le_normalizer _ B (fun g hg t ht => ?_)
    rw [hXdef] at ht ⊢
    refine pg1_conj_comm g W B (fun m hm => pg1_conj_of_mem (hBW hg) hm) (fun b' hb' => ?_) t ht
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hb') (Subgroup.inv_mem _ hg)
  have hXB : ⁅delta2At 3 B D b, B⁆ = delta2At 3 B D b := by
    rw [hXdef]; exact commutator_commutator_eq hBp hBW hWcop
  have hdec := eq_sup_commutator_of_mem hBp hBel.1 hBX hXcop hxB hXB
  set X := delta2At 3 B D b with hXset
  set Y : Subgroup G := ⁅X ⊓ Cen x, B⁆ with hYset
  have hYX : Y ≤ X := hdec ▸ le_sup_left
  have hYY : Y ≤ delta2At 3 B D x :=
    Subgroup.commutator_mono (inf_le_inf_right _ hXle) le_rfl
  have hYc : Y ≤ Cen x := by
    rw [hYset, Subgroup.commutator_le]
    intro c hc β hβ
    rw [commutatorElement_def]
    have hβ' := hBxc hβ
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc.2 hβ') (Subgroup.inv_mem _ hc.2))
      (Subgroup.inv_mem _ hβ')
  have hYn : Y ≤ Subgroup.normalizer (L : Set G) := hYX.trans hXn
  have hT := h.transfer (Z := Y) (le_inf hYn hYc)
    ((Subgroup.commutator_mono le_rfl hYY).trans hJY)
  have hYcq := parti_le_cq h hYn hT
  have hNcq := parti_N_le_cq h hXn
  have hXcq : X ≤ centralizerQuot L (GLAPPrimeCoreOf 3 L) := by
    rw [hdec]; exact sup_le hYcq hNcq
  exact hX (parti_comm_le_of_cq h hXcq)

theorem not_le_of_not_centralizes {J Y : Subgroup G} {x : G} (hJ : J ≤ Cen x)
    (h : ¬ ⁅J, Y⁆ ≤ GLAPPrimeCoreOf 3 (Cen x)) : ¬ Y ≤ GLAPPrimeCoreOf 3 (Cen x) := by
  intro hY
  apply h
  rw [Subgroup.commutator_le]
  intro j hj y hy
  have := mem_gLAPPrimeCoreOf_conj (p := 3) (H := Cen x) (hY hy) (hJ hj)
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (hY hy))

end PartI

section Bar

variable {G : Type*} [Group G] [Finite G]

@[expose] def CentMod (b : G) (K : Subgroup G) (x : G) : Prop :=
  x ∈ Cen b ∧ (∃ k ∈ K ⊓ Cen b, k⁻¹ * x ∈ GLAPPrimeCoreOf 3 (Cen b)) ∧
    ∀ k ∈ K ⊓ Cen b, x * k * x⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b)

@[expose] def bar1_bar (b : G) {y : G} (hy : y ∈ Cen b) : CBar 3 b :=
  QuotientGroup.mk (⟨y, hy⟩ : ↥(Cen b))

omit [Finite G] in
theorem bar1_mem_core_iff {b y : G} (hy : y ∈ Cen b) :
    y ∈ GLAPPrimeCoreOf 3 (Cen b) ↔ bar1_bar b hy = 1 := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact (QuotientGroup.eq_one_iff c).2 hc
  · intro h
    exact ⟨⟨y, hy⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩

omit [Finite G] in
theorem bar1_mul (b : G) {y z : G} (hy : y ∈ Cen b) (hz : z ∈ Cen b) :
    bar1_bar b hy * bar1_bar b hz = bar1_bar b (mul_mem hy hz) := rfl

omit [Finite G] in
theorem bar1_inv (b : G) {y : G} (hy : y ∈ Cen b) :
    (bar1_bar b hy)⁻¹ = bar1_bar b (inv_mem hy) := rfl

omit [Finite G] in
theorem bar1_eq_iff {b y z : G} (hy : y ∈ Cen b) (hz : z ∈ Cen b) :
    bar1_bar b hy = bar1_bar b hz ↔ y⁻¹ * z ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  unfold bar1_bar
  rw [QuotientGroup.eq]
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨c, hc, hcz⟩
    have : c = (⟨y, hy⟩ : ↥(Cen b))⁻¹ * ⟨z, hz⟩ := Subtype.ext hcz
    rwa [← this]

omit [Finite G] in
theorem bar1_mem_barImageAt_iff {b : G} {Y : Subgroup G} {w : CBar 3 b} :
    w ∈ barImageAt 3 b Y ↔ ∃ (y : G) (hy : y ∈ Cen b), y ∈ Y ∧ bar1_bar b hy = w := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, c.2, (Subgroup.mem_subgroupOf).1 hc, rfl⟩
  · rintro ⟨y, hy, hyY, rfl⟩
    exact ⟨⟨y, hy⟩, (Subgroup.mem_subgroupOf).2 hyY, rfl⟩

omit [Finite G] in
theorem bar1_mem_center_iff {b : G} {K : Subgroup G} {z : CBar 3 b} :
    z ∈ barCenterAt 3 b K ↔
      z ∈ barImageAt 3 b K ∧ ∀ w ∈ barImageAt 3 b K, w * z = z * w := by
  unfold barCenterAt
  constructor
  · rintro ⟨⟨c, hc⟩, hcz, rfl⟩
    refine ⟨hc, fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.1 hcz ⟨w, hw⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (h w w.2), rfl⟩

omit [Finite G] in
theorem bar1_comm_iff {b g k : G} (hg : g ∈ Cen b) (hk : k ∈ Cen b) :
    bar1_bar b hk * bar1_bar b hg = bar1_bar b hg * bar1_bar b hk ↔
      g * k * g⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  have hmem : g * k * g⁻¹ * k⁻¹ ∈ Cen b :=
    mul_mem (mul_mem (mul_mem hg hk) (inv_mem hg)) (inv_mem hk)
  rw [bar1_mem_core_iff hmem]
  have e : bar1_bar b hmem = bar1_bar b hg * bar1_bar b hk * (bar1_bar b hg)⁻¹ *
      (bar1_bar b hk)⁻¹ := rfl
  rw [e, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h; rw [h]
  · intro h; rw [h]

omit [Finite G] in
theorem bar1_mem_barCenterAt_iff {b : G} {K : Subgroup G} {g : G} (hg : g ∈ Cen b) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) ⟨g, hg⟩ ∈ barCenterAt 3 b K ↔ CentMod b K g := by
  change bar1_bar b hg ∈ barCenterAt 3 b K ↔ _
  rw [bar1_mem_center_iff]
  constructor
  · rintro ⟨hz, hc⟩
    obtain ⟨k, hk, hkK, hkg⟩ := bar1_mem_barImageAt_iff.1 hz
    refine ⟨hg, ⟨k, ⟨hkK, hk⟩, (bar1_eq_iff hk hg).1 hkg⟩, fun k' hk' => ?_⟩
    exact (bar1_comm_iff hg hk'.2).1 (hc _ (bar1_mem_barImageAt_iff.2 ⟨k', hk'.2, hk'.1, rfl⟩))
  · rintro ⟨-, ⟨k, hk, hkR⟩, hc⟩
    refine ⟨bar1_mem_barImageAt_iff.2 ⟨k, hk.2, hk.1, (bar1_eq_iff hk.2 hg).2 hkR⟩, fun w hw => ?_⟩
    obtain ⟨y, hy, hyK, rfl⟩ := bar1_mem_barImageAt_iff.1 hw
    exact (bar1_comm_iff hg hy).2 (hc y ⟨hyK, hy⟩)

theorem mem_barCenterAt_iff {b : G} {K : Subgroup G} {g : G} (hg : g ∈ Cen b) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) ⟨g, hg⟩ ∈ barCenterAt 3 b K ↔ CentMod b K g :=
  bar1_mem_barCenterAt_iff hg

theorem centMod_of_barImage_le {b : G} {P K : Subgroup G}
    (h : barImageAt 3 b P ≤ barCenterAt 3 b K) {g : G} (hg : g ∈ P) (hgb : g ∈ Cen b) :
    CentMod b K g :=
  (mem_barCenterAt_iff hgb).1 (h (bar1_mem_barImageAt_iff.2 ⟨g, hgb, hg, rfl⟩))

theorem card_barCenterAt {b : G} {K : Subgroup G} :
    Nat.card (barCenterAt 3 b K) = Nat.card (Subgroup.center ↥(barImageAt 3 b K)) :=
  Subgroup.card_map_of_injective (barImageAt 3 b K).subtype_injective

theorem bClosure_normalized {B L : Subgroup G} (hB : IsMulCommutative B) :
    B ≤ Subgroup.normalizer (bClosure B L : Set G) := by
  have key : ∀ γ ∈ B, GLBConj γ (bClosure B L) ≤ bClosure B L := by
    intro γ hγ
    have h1 : GLBConj γ (bClosure B L) = ⨆ g ∈ B, GLBConj γ (GLBConj g L) := by
      unfold bClosure GLBConj
      simp only [Subgroup.map_iSup]
    rw [h1]
    refine iSup₂_le fun g hg => ?_
    rw [gLBConj_gLBConj]
    exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) (g * γ) (B.mul_mem hg hγ)
  intro β hβ
  rw [mem_normalizer_iff_gLBConj_eq]
  refine le_antisymm (key β hβ) ?_
  have h2 := gLBConj_mono β (key β⁻¹ (B.inv_mem hβ))
  rwa [gLBConj_gLBConj_inv] at h2

theorem bar1_core_eq {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cen b) L) :
    GLAPPrimeCoreOf 3 L = L ⊓ GLAPPrimeCoreOf 3 (Cen b) := by
  apply le_antisymm
  · exact le_inf (Subgroup.map_subtype_le _)
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hL.2.1)
  · have := gLAPPrimeCoreOf_inf_le (G := G) Nat.prime_three (Cen b) L
    rw [inf_eq_right.2 hL.1] at this
    rw [inf_comm]
    exact this

theorem bar1_mem_coreL_iff {b : G} {L : Subgroup G} (hL : GLAPComponent 3 (Cen b) L) (y : ↥L) :
    y ∈ GLAPPrimeCore 3 ↥L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  have h1 : y ∈ GLAPPrimeCore 3 ↥L ↔ (y : G) ∈ GLAPPrimeCoreOf 3 L :=
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨y', hy', e⟩ => (Subtype.ext e : y' = y) ▸ hy'⟩
  rw [h1, bar1_core_eq hL]
  exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩

theorem bar1_coprime_orderOf {b n : G} (hn : n ∈ GLAPPrimeCoreOf 3 (Cen b)) :
    Nat.Coprime 3 (orderOf n) := by
  have hc := coprime_card_gLAPPrimeCore_aux 3 ↥(Cen b)
  have hcard : Nat.card (GLAPPrimeCoreOf 3 (Cen b)) = Nat.card (GLAPPrimeCore 3 ↥(Cen b)) :=
    Subgroup.card_map_of_injective (Cen b).subtype_injective
  rw [← hcard] at hc
  exact hc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hn)

theorem bar1_mem_zpowers_of_mul_eq {x j n : G} (hx3 : orderOf x = 3) (hjn : j * n = x)
    (hc : j * n = n * j) (hn : Nat.Coprime 3 (orderOf n)) : x ∈ Subgroup.zpowers j := by
  set m := orderOf n with hm
  have hcomm : Commute j n := hc
  have hxm : x ^ m = j ^ m := by
    rw [← hjn, hcomm.mul_pow, hm, pow_orderOf_eq_one, mul_one]
  have hm3 : ¬ 3 ∣ m := fun h => by
    have := Nat.Coprime.eq_one_of_dvd hn h
    omega
  have hmm : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hx : x ^ (m * m) = x := by
    rw [← pow_mod_orderOf, hx3, hmm, pow_one]
  have hxj : x = j ^ (m * m) := by
    calc x = x ^ (m * m) := hx.symm
      _ = (x ^ m) ^ m := pow_mul x m m
      _ = (j ^ m) ^ m := by rw [hxm]
      _ = j ^ (m * m) := (pow_mul j m m).symm
  rw [hxj]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers j) _

theorem bar1_exists_central {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Cen b) L) (hZ : Subgroup.center (barOf 3 L) ≠ ⊥) :
    ∃ (ℓ : G) (hℓ : ℓ ∈ Cen b), ℓ ∈ L ∧ bar1_bar b hℓ ≠ 1 ∧
      bar1_bar b hℓ ∈ barCenterAt 3 b (bClosure B L) := by
  classical
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective u
  have hℓL : (z : G) ∈ L := z.2
  have hℓ : (z : G) ∈ Cen b := hL.1 hℓL
  have hcommL : ∀ y ∈ L, y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) := by
    intro y hy
    have h1 : (⟨y, hy⟩ * z * ⟨y, hy⟩⁻¹ * z⁻¹ : ↥L) ∈ GLAPPrimeCore 3 ↥L := by
      rw [← QuotientGroup.eq_one_iff]
      have hc := Subgroup.mem_center_iff.1 hu (QuotientGroup.mk ⟨y, hy⟩)
      show (QuotientGroup.mk ⟨y, hy⟩ : barOf 3 L) * QuotientGroup.mk z *
        (QuotientGroup.mk ⟨y, hy⟩)⁻¹ * (QuotientGroup.mk z)⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hc
    exact (bar1_mem_coreL_iff hL _).1 h1
  have hnR : (z : G) ∉ GLAPPrimeCoreOf 3 (Cen b) := by
    intro h
    apply hu1
    refine Subtype.ext ?_
    exact (QuotientGroup.eq_one_iff z).2 ((bar1_mem_coreL_iff hL z).2 h)
  have hBC : ∀ g ∈ B, g * b = b * g := fun g hg => by
    have := hB.1.is_comm.comm (⟨g, hg⟩ : B) ⟨b, hbB⟩
    exact congrArg Subtype.val this
  have hcomp : ∀ g ∈ B, GLAPComponent 3 (Cen b) (GLBConj g L) := fun g hg => by
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
    rwa [gLBConj_centralizer_singleton_of_commute (hBC g hg)] at this
  have hcommg : ∀ g ∈ B, ∀ (y : G) (hy : y ∈ Cen b), y ∈ GLBConj g L →
      bar1_bar b hy * bar1_bar b hℓ = bar1_bar b hℓ * bar1_bar b hy := by
    intro g hg y hy hyg
    by_cases hne : GLBConj g L = L
    · rw [hne] at hyg
      exact ((bar1_comm_iff hy hℓ).2 (hcommL y hyg)).symm
    · have hcm := commutator_le_gLAPPrimeCore_of_ne (by norm_num : Nat.Prime 3)
        (hcomp g hg) hL hne
      have hmem : y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) := by
        have := Subgroup.commutator_mem_commutator hyg hℓL
        rw [commutatorElement_def] at this
        exact hcm this
      exact ((bar1_comm_iff hy hℓ).2 hmem).symm
  let T : Subgroup ↥(Cen b) :=
    (Subgroup.centralizer ({bar1_bar b hℓ} : Set (CBar 3 b))).comap
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)))
  let S : Subgroup G := T.map (Cen b).subtype
  have hKS : bClosure B L ≤ S := by
    refine iSup₂_le fun g hg y hy => ?_
    have hyC : y ∈ Cen b := (hcomp g hg).1 hy
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨y, hyC⟩ ∈ Subgroup.centralizer ({bar1_bar b hℓ} : Set (CBar 3 b))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommg g hg y hyC hy
  have hLK : L ≤ bClosure B L := by
    have h1 : GLBConj 1 L ≤ bClosure B L :=
      le_iSup₂ (f := fun (g : G) (_ : g ∈ B) => GLBConj g L) 1 B.one_mem
    rwa [gLBConj_one] at h1
  have hcent : CentMod b (bClosure B L) (z : G) := by
    refine ⟨hℓ, ⟨z, ⟨hLK hℓL, hℓ⟩, by simp [one_mem]⟩, fun k hk => ?_⟩
    obtain ⟨c, hc, hck⟩ := hKS hk.1
    have hck' : c = ⟨k, hk.2⟩ := Subtype.ext hck
    subst hck'
    have hcc : QuotientGroup.mk' _ (⟨k, hk.2⟩ : ↥(Cen b)) ∈
        Subgroup.centralizer ({bar1_bar b hℓ} : Set (CBar 3 b)) := hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hcc
    exact (bar1_comm_iff hℓ hk.2).1 hcc
  exact ⟨z, hℓ, hℓL, fun h => hnR ((bar1_mem_core_iff hℓ).2 h),
    (bar1_mem_barCenterAt_iff hℓ).2 hcent⟩

theorem mem_of_barCenter_eq {B : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hb1 : b ≠ 1) {L : Subgroup G} (hL : GLAPComponent 3 (Cen b) L)
    (hZ : Subgroup.center (barOf 3 L) ≠ ⊥)
    (h : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)) : b ∈ L := by
  classical
  obtain ⟨ℓ, hℓ, hℓL, hℓ1, hℓZ⟩ := bar1_exists_central hB hbB hL hZ
  rw [← h] at hℓZ
  obtain ⟨y, hy, hyz, hyℓ⟩ := bar1_mem_barImageAt_iff.1 hℓZ
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hbC : b ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply hℓ1
    rw [← hyℓ]
    rfl
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
  have hord : orderOf b = 3 := by
    have hd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exfalso
      rw [orderOf_eq_one_iff] at h
      apply hy1
      rw [h]; simp
    · exact h
  have hi : b ^ (i % 3) = b ^ i := by
    have := zpow_mod_orderOf b i
    rw [hord] at this
    simpa using this
  have hcases : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  have key : ∃ (g : G) (hg : g ∈ Cen b), g ∈ L ∧ bar1_bar b hbC = bar1_bar b hg := by
    rcases hcases with h | h | h
    · exfalso
      apply hy1
      rw [← hi]
      have : i % 3 = 0 := h
      simp [this]
    · refine ⟨ℓ, hℓ, hℓL, ?_⟩
      rw [hyℓ.symm]
      congr 1
      rw [← hi]
      have : i % 3 = 1 := h
      simp [this]
    · refine ⟨ℓ * ℓ, mul_mem hℓ hℓ, mul_mem hℓL hℓL, ?_⟩
      rw [← bar1_mul b hℓ hℓ, ← hyℓ, bar1_mul]
      have hyy : b ^ i = b ^ 2 := by
        rw [← hi]
        have : i % 3 = 2 := h
        simp [this]
      have hbb : b = b ^ 2 * b ^ 2 := by
        calc b = b ^ 3 * b := by rw [hb3]; simp
          _ = b ^ 2 * b ^ 2 := by group
      congr 1
      rw [hyy]
      exact hbb
  obtain ⟨g, hg, hgL, hbg⟩ := key
  have hn : g⁻¹ * b ∈ GLAPPrimeCoreOf 3 (Cen b) :=
    (bar1_eq_iff hg hbC).1 hbg.symm
  have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hcomm : g * (g⁻¹ * b) = (g⁻¹ * b) * g := by
    calc g * (g⁻¹ * b) = b := by group
      _ = (g⁻¹ * b) * g := by rw [mul_assoc, ← hgb]; group
  have hmem := bar1_mem_zpowers_of_mul_eq hord (by group : g * (g⁻¹ * b) = b) hcomm
    (bar1_coprime_orderOf hn)
  exact (Subgroup.zpowers_le.2 hgL) hmem

theorem CentMod.congr {b x x' : G} {K : Subgroup G} (h : CentMod b K x) (hx' : x' ∈ Cen b)
    (hxx : x'⁻¹ * x ∈ GLAPPrimeCoreOf 3 (Cen b)) : CentMod b K x' := by
  have e : bar1_bar b hx' = bar1_bar b h.1 := (bar1_eq_iff hx' h.1).2 hxx
  rw [← mem_barCenterAt_iff hx']
  change bar1_bar b hx' ∈ _
  rw [e]
  exact (mem_barCenterAt_iff h.1).2 h

@[expose] def centModSub (b : G) (K : Subgroup G) : Subgroup G where
  carrier := {g | CentMod b K g}
  mul_mem' := by
    intro x y hx hy
    have hx' : x ∈ Cen b := hx.1
    have hy' : y ∈ Cen b := hy.1
    have h1 := (bar1_mem_barCenterAt_iff hx').2 hx
    have h2 := (bar1_mem_barCenterAt_iff hy').2 hy
    exact (bar1_mem_barCenterAt_iff (mul_mem hx' hy')).1
      (by rw [show (⟨x * y, mul_mem hx' hy'⟩ : ↥(Cen b)) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from rfl, map_mul]
          exact mul_mem h1 h2)
  one_mem' := by
    refine (bar1_mem_barCenterAt_iff (one_mem (Cen b))).1 ?_
    rw [show (⟨1, one_mem (Cen b)⟩ : ↥(Cen b)) = 1 from rfl, map_one]
    exact one_mem _
  inv_mem' := by
    intro x hx
    have hx' : x ∈ Cen b := hx.1
    have h1 := (bar1_mem_barCenterAt_iff hx').2 hx
    exact (bar1_mem_barCenterAt_iff (inv_mem hx')).1
      (by rw [show (⟨x⁻¹, inv_mem hx'⟩ : ↥(Cen b)) = ⟨x, hx'⟩⁻¹ from rfl, map_inv]
          exact inv_mem h1)

omit [Finite G] in
theorem mem_centModSub {b : G} {K : Subgroup G} {g : G} : g ∈ centModSub b K ↔ CentMod b K g :=
  Iff.rfl

theorem Config.of_centMod {b x : G} {L K : Subgroup G} (hL : GLAPComponent 3 (Cen b) L)
    (hLK : L ≤ K) (hx : CentMod b K x) (hord : orderOf x = 3) : Config b x L := by
  have hLC : L ≤ Cen b := hL.1
  refine ⟨hL, hx.1, hord, Subgroup.commutator_le.2 fun l hl y hy => ?_⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hlC : l ∈ Cen b := hLC hl
  have hxn : x ^ n ∈ Cen b := zpow_mem hx.1 n
  have hc : bar1_bar b hx.1 * bar1_bar b hlC = bar1_bar b hlC * bar1_bar b hx.1 :=
    (bar1_comm_iff hlC hx.1).2 (by
      have := hx.2.2 l ⟨hLK hl, hlC⟩
      have h2 := inv_mem this
      simpa [mul_assoc] using h2)
  have hpow : bar1_bar b hxn = bar1_bar b hx.1 ^ n := by
    have := map_zpow (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b))) (⟨x, hx.1⟩ : ↥(Cen b)) n
    exact this
  have := (bar1_comm_iff hlC hxn).1 (by
    rw [hpow]
    exact (Commute.zpow_left hc n).eq)
  rw [commutatorElement_def]
  exact this


theorem bar2_normalizes {B : Subgroup G} {b : G} {L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hbB : b ∈ B) {β z : G} (hβ : β ∈ B) (hz : z ∈ centModSub b (bClosure B L)) :
    β * z * β⁻¹ ∈ centModSub b (bClosure B L) := by
  have hβC : β ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_comm hB hβ hbB)
  have hNK := bClosure_normalized (L := L) hB.1 hβ
  have hNK' := bClosure_normalized (L := L) hB.1 (B.inv_mem hβ)
  have hβC' : β⁻¹ ∈ Cen b := inv_mem hβC
  obtain ⟨hzC, ⟨k, hk, hkR⟩, hc⟩ := hz
  refine ⟨mul_mem (mul_mem hβC hzC) hβC', ⟨β * k * β⁻¹, ⟨?_, ?_⟩, ?_⟩, fun k' hk' => ?_⟩
  · exact pg1_conj_of_mem hNK hk.1
  · exact mul_mem (mul_mem hβC hk.2) hβC'
  · have := mem_gLAPPrimeCoreOf_conj hkR hβC
    convert this using 1
    group
  · have hk'' : β⁻¹ * k' * β⁻¹⁻¹ ∈ bClosure B L ⊓ Cen b :=
      ⟨pg1_conj_of_mem hNK' hk'.1, mul_mem (mul_mem hβC' hk'.2) ((Cen b).inv_mem hβC')⟩
    have := mem_gLAPPrimeCoreOf_conj (hc _ hk'') hβC
    convert this using 1
    group

theorem exists_good_conj {B : Subgroup G} {b x : G} {L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hbB : b ∈ B) (hx3 : x ^ 3 = 1) (hxK : CentMod b (bClosure B L) x) :
    ∃ n : G, n ∈ Cen b ∧ CentMod b (bClosure B L) n ∧
      IsPGroup 3 ↥(B ⊔ Subgroup.zpowers (n * x * n⁻¹)) ∧
      (n * x * n⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  have hxZ : x ∈ centModSub b (bClosure B L) := hxK
  have hBZ : B ≤ Subgroup.normalizer (centModSub b (bClosure B L) : Set G) :=
    pg1_le_normalizer _ _ fun g hg t ht => bar2_normalizes hB hbB hg ht
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨1, Subtype.ext ?_⟩
    have : (g : G) ^ 3 = 1 := by
      rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    simpa using this
  obtain ⟨n, hn, hnP⟩ := exists_conj_pGroup hBp hBZ hxZ hxp
  refine ⟨n, hn.1, hn, hnP, ?_⟩
  obtain ⟨-, ⟨k, hk, hkR⟩, -⟩ := hxK
  have hnC : n ∈ Cen b := hn.1
  have h1 := mem_gLAPPrimeCoreOf_conj (inv_mem hkR) hnC
  have h2 := hn.2.2 k⁻¹ ((bClosure B L ⊓ Cen b).inv_mem hk)
  have key : (n * x * n⁻¹)⁻¹ * x =
      (n * (k⁻¹ * x)⁻¹ * n⁻¹) * (n * k⁻¹ * n⁻¹ * k⁻¹⁻¹) * (k⁻¹ * x) := by group
  rw [key]
  exact mul_mem (mul_mem h1 h2) hkR

theorem relIndex_le_three_a {B : Subgroup G} {b x : G} {L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hbB : b ∈ B) (hx : x ∈ Cen b) (hx1 : x ≠ 1) (hP : IsPGroup 3 ↥(B ⊔ Subgroup.zpowers x))
    (hxK : CentMod b (bClosure B L) x)
    (hcard : Nat.card (Subgroup.center ↥(barImageAt 3 b (bClosure B L))) ≤ 9) :
    (Cen x).relIndex B ≤ 3 := by
  have hBp : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  set P := B ⊔ Subgroup.zpowers x with hPdef
  set T := P ⊓ centModSub b (bClosure B L) with hT
  have hxP : x ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hTC : ∀ t ∈ T, t ∈ Cen b := fun t ht => ht.2.1
  have hTcard : Nat.card T ≤ 9 := by
    let f : T → barCenterAt 3 b (bClosure B L) := fun t =>
      ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) ⟨t.1, hTC t.1 t.2⟩,
        (mem_barCenterAt_iff (hTC t.1 t.2)).2 t.2.2⟩
    have hf : Function.Injective f := by
      intro t1 t2 h12
      have h12' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) ⟨t1.1, hTC t1.1 t1.2⟩ =
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) ⟨t2.1, hTC t2.1 t2.2⟩ :=
        congrArg Subtype.val h12
      have h3 : t1.1⁻¹ * t2.1 ∈ GLAPPrimeCoreOf 3 (Cen b) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h12'
        exact ⟨_, h12', rfl⟩
      have hP3 : IsPGroup 3 (Subgroup.zpowers (t1.1⁻¹ * t2.1)) := by
        intro g
        have hgP : (g : G) ∈ P := by
          have : t1.1⁻¹ * t2.1 ∈ P := mul_mem (P.inv_mem t1.2.1) t2.2.1
          exact (Subgroup.zpowers_le.2 this) g.2
        obtain ⟨m, hm⟩ := hP ⟨g, hgP⟩
        exact ⟨m, Subtype.ext (by simpa using congrArg Subtype.val hm)⟩
      have := eq_one_of_mem_core_of_pGroup h3 hP3
      exact Subtype.ext (inv_mul_eq_one.1 this)
    calc Nat.card T ≤ Nat.card (barCenterAt 3 b (bClosure B L)) :=
          Nat.card_le_card_of_injective f hf
      _ ≤ 9 := by rw [card_barCenterAt]; exact hcard
  refine relIndex_centralizer_le_three hBp hTcard ⟨hxP, hxK⟩ hx1 fun β hβ => ?_
  exact ⟨mul_mem (mul_mem (Subgroup.mem_sup_left hβ) hxP) (P.inv_mem (Subgroup.mem_sup_left hβ)),
    bar2_normalizes hB hbB hβ hxK⟩

theorem bar3_B_le_Cen {B : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B) :
    B ≤ Cen b := fun g hg => by
  have := hB.1.is_comm.comm (⟨g, hg⟩ : B) ⟨b, hbB⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)

theorem bar3_conj_comp {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Cen b) L) {L' : Subgroup G} (h : IsBConjugate B L L') :
    GLAPComponent 3 (Cen b) L' := by
  obtain ⟨g, hg, rfl⟩ := h
  have hBC : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.1 (bar3_B_le_Cen hB hbB hg)
  have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g
  rwa [gLBConj_centralizer_singleton_of_commute hBC] at this

theorem bar3_commFam {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Cen b) L) :
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CommFam
      (fun i : {L' : Subgroup G // IsBConjugate B L L'} => barImageAt 3 b i.1) := by
  intro i j hij x y hx hy
  obtain ⟨u, hu, huL, rfl⟩ := bar1_mem_barImageAt_iff.1 hx
  obtain ⟨v, hv, hvL, rfl⟩ := bar1_mem_barImageAt_iff.1 hy
  have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hcm := commutator_le_gLAPPrimeCore_of_ne (by norm_num : Nat.Prime 3)
    (bar3_conj_comp hB hbB hL i.2) (bar3_conj_comp hB hbB hL j.2) hne
  have hmem : u * v * u⁻¹ * v⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) := by
    have := Subgroup.commutator_mem_commutator huL hvL
    rw [commutatorElement_def] at this
    exact hcm this
  exact ((bar1_comm_iff hu hv).2 hmem).symm

theorem bar3_barImage_mono {b : G} {Y Y' : Subgroup G} (h : Y ≤ Y') :
    barImageAt 3 b Y ≤ barImageAt 3 b Y' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem bar3_barImage_eq {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Cen b) L) :
    barImageAt 3 b (bClosure B L) =
      ⨆ i : {L' : Subgroup G // IsBConjugate B L L'}, barImageAt 3 b i.1 := by
  apply le_antisymm
  · set J : Subgroup (CBar 3 b) :=
      ⨆ i : {L' : Subgroup G // IsBConjugate B L L'}, barImageAt 3 b i.1 with hJ
    let T : Subgroup ↥(Cen b) := J.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)))
    have hKS : bClosure B L ≤ T.map (Cen b).subtype := by
      refine iSup₂_le fun g hg y hy => ?_
      have hyC : y ∈ Cen b := (bar3_conj_comp hB hbB hL ⟨g, hg, rfl⟩).1 hy
      refine ⟨⟨y, hyC⟩, ?_, rfl⟩
      show QuotientGroup.mk' _ ⟨y, hyC⟩ ∈ J
      have : bar1_bar b hyC ∈ barImageAt 3 b (GLBConj g L) :=
        bar1_mem_barImageAt_iff.2 ⟨y, hyC, hy, rfl⟩
      exact le_iSup (fun i : {L' : Subgroup G // IsBConjugate B L L'} => barImageAt 3 b i.1)
        ⟨GLBConj g L, g, hg, rfl⟩ this
    intro w hw
    obtain ⟨y, hy, hyK, rfl⟩ := bar1_mem_barImageAt_iff.1 hw
    obtain ⟨c, hc, hcy⟩ := hKS hyK
    have hcy' : c = ⟨y, hy⟩ := Subtype.ext hcy
    subst hcy'
    exact hc
  · refine iSup_le fun i => bar3_barImage_mono ?_
    obtain ⟨g, hg, e⟩ := i.2
    rw [e]
    exact le_iSup₂ (f := fun (g : G) (_ : g ∈ B) => GLBConj g L) g hg

theorem bar3_barCenter_eq {B L : Subgroup G} {b : G} (hB : IsElemAbelian 3 B) (hbB : b ∈ B)
    (hL : GLAPComponent 3 (Cen b) L) :
    barCenterAt 3 b (bClosure B L) =
      ⨆ i : {L' : Subgroup G // IsBConjugate B L L'}, barCenterAt 3 b i.1 := by
  classical
  haveI : Fintype {L' : Subgroup G // IsBConjugate B L L'} := Fintype.ofFinite _
  have h1 : ∀ K : Subgroup G, barCenterAt 3 b K =
      CFSG.HardMathSupport.Timmesfeld.ComponentBalance.centreIn (barImageAt 3 b K) := fun K =>
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.map_subtype_center _
  rw [h1, bar3_barImage_eq hB hbB hL,
    (bar3_commFam hB hbB hL).centreIn_iSup_eq_iSup]
  exact iSup_congr fun i => (h1 i.1).symm

theorem bar3_norm_center {b g : G} {L' : Subgroup G} (hL' : L' ≤ Cen b) (hg : g ∈ Cen b)
    (hgN : g ∈ Subgroup.normalizer (L' : Set G)) {w : CBar 3 b} (hw : w ∈ barCenterAt 3 b L') :
    bar1_bar b hg * w * (bar1_bar b hg)⁻¹ ∈ barCenterAt 3 b L' := by
  rw [bar1_mem_center_iff] at hw ⊢
  obtain ⟨hwI, hc⟩ := hw
  obtain ⟨y, hy, hyL, rfl⟩ := bar1_mem_barImageAt_iff.1 hwI
  have hgyg : g * y * g⁻¹ ∈ Cen b := mul_mem (mul_mem hg hy) (inv_mem hg)
  have e : bar1_bar b hg * bar1_bar b hy * (bar1_bar b hg)⁻¹ = bar1_bar b hgyg := rfl
  rw [e]
  have hyL' : g * y * g⁻¹ ∈ L' := (Subgroup.mem_normalizer_iff.1 hgN y).1 hyL
  refine ⟨bar1_mem_barImageAt_iff.2 ⟨_, hgyg, hyL', rfl⟩, fun v hv => ?_⟩
  obtain ⟨u, hu, huL, rfl⟩ := bar1_mem_barImageAt_iff.1 hv
  have hguq : g⁻¹ * u * g ∈ Cen b := mul_mem (mul_mem (inv_mem hg) hu) hg
  have hguL : g⁻¹ * u * g ∈ L' := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgN) u).1 huL
    simpa using this
  have h := hc _ (bar1_mem_barImageAt_iff.2 ⟨_, hguq, hguL, rfl⟩)
  have e2 : bar1_bar b hguq =
      (bar1_bar b hg)⁻¹ * bar1_bar b hu * bar1_bar b hg := rfl
  rw [e2] at h
  set a := bar1_bar b hg
  set c := bar1_bar b hu
  set y' := bar1_bar b hy
  calc c * (a * y' * a⁻¹) = a * ((a⁻¹ * c * a) * y') * a⁻¹ := by group
    _ = a * (y' * (a⁻¹ * c * a)) * a⁻¹ := by rw [h]
    _ = (a * y' * a⁻¹) * c := by group

theorem bar3_card_barCenter_three {b : G} {L' : Subgroup G} (hL' : GLAPComponent 3 (Cen b) L')
    (hZ : Nat.card (Subgroup.center (barOf 3 L')) = 3) :
    Nat.card (barCenterAt 3 b L') = 3 := by
  rw [card_barCenterAt]
  exact (Nat.card_congr
    (Subgroup.centerCongr (quotEquivBarX Nat.prime_three hL'.1 hL'.2.1)).toEquiv).symm.trans hZ

theorem D_cen_barCenter {B D : Subgroup G} {b : G} {L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hbB : b ∈ B) (hDB : D ≤ B) (hL : GLAPComponent 3 (Cen b) L)
    (hDL : ∀ L', IsBConjugate B L L' → D ≤ Subgroup.normalizer (L' : Set G))
    (hZ : ∀ L', IsBConjugate B L L' → Nat.card (Subgroup.center (barOf 3 L')) = 3) {d z : G} (hd : d ∈ D)
    (hz : CentMod b (bClosure B L) z) : d * z * d⁻¹ * z⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) := by
  have hdB : d ∈ B := hDB hd
  have hdC : d ∈ Cen b := bar3_B_le_Cen hB hbB hdB
  have hd3 : d ^ 3 = 1 := hB.2 d hdB
  have hdbar3 : bar1_bar b hdC ^ 3 = 1 := by
    have h1 : (⟨d, hdC⟩ : ↥(Cen b)) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    have := map_pow (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b))) (⟨d, hdC⟩ : ↥(Cen b)) 3
    rw [h1, map_one] at this
    exact this.symm
  have hzc : bar1_bar b hz.1 ∈ barCenterAt 3 b (bClosure B L) :=
    (mem_barCenterAt_iff hz.1).2 hz
  have hle : barCenterAt 3 b (bClosure B L) ≤
      Subgroup.centralizer ({bar1_bar b hdC} : Set (CBar 3 b)) := by
    rw [bar3_barCenter_eq hB hbB hL]
    refine iSup_le fun i => ?_
    have hcomp := bar3_conj_comp hB hbB hL i.2
    have hZi := bar3_card_barCenter_three hcomp (hZ i.1 i.2)
    have hdN := hDL i.1 i.2
    have hdn : bar1_bar b hdC ∈ Subgroup.normalizer (barCenterAt 3 b i.1 : Set (CBar 3 b)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact fun hw => bar3_norm_center hcomp.1 hdC (hdN hd) hw
      · intro hw
        have := bar3_norm_center hcomp.1 (inv_mem hdC) (inv_mem (hdN hd)) hw
        rw [show bar1_bar b (inv_mem hdC) = (bar1_bar b hdC)⁻¹ from rfl, inv_inv] at this
        simpa [mul_assoc] using this
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := conj_eq_of_card_three hZi hdbar3 hdn w hw
    calc w * bar1_bar b hdC = (bar1_bar b hdC * w * (bar1_bar b hdC)⁻¹) * bar1_bar b hdC := by rw [this]
      _ = bar1_bar b hdC * w := by group
  have hcw := hle hzc
  rw [Subgroup.mem_centralizer_singleton_iff] at hcw
  exact (bar1_comm_iff hdC hz.1).1 hcw

theorem bar3_core_le_normalizer {b : G} {L' : Subgroup G} (hL' : GLAPComponent 3 (Cen b) L') :
    GLAPPrimeCoreOf 3 (Cen b) ≤ Subgroup.normalizer (L' : Set G) := by
  have hn := glaPComponent_normal_preimBarX hL'
  have hN : preimBarX 3 (Cen b) L' ≤ Subgroup.normalizer (L' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX 3 hL'.1)).1 hn
  refine le_trans ?_ hN
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨c, ?_, rfl⟩
  have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) c = 1 := (QuotientGroup.eq_one_iff c).2 hc
  show QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen b)) c ∈ barX 3 (Cen b) L'
  rw [h1]
  exact one_mem _

theorem bar3_inj {b : G} {P : Subgroup G} (hP3 : IsPGroup 3 P) {y y' : G} (hy : y ∈ Cen b)
    (hy' : y' ∈ Cen b) (hyP : y ∈ P) (hyP' : y' ∈ P) (h : bar1_bar b hy = bar1_bar b hy') :
    y = y' := by
  have h1 : y⁻¹ * y' ∈ GLAPPrimeCoreOf 3 (Cen b) := (bar1_eq_iff hy hy').1 h
  have h2 : y⁻¹ * y' ∈ P := mul_mem (inv_mem hyP) hyP'
  have h3 : IsPGroup 3 (Subgroup.zpowers (y⁻¹ * y')) :=
    IsPGroup.to_le hP3 (Subgroup.zpowers_le.2 h2)
  have := eq_one_of_mem_core_of_pGroup h1 h3
  exact inv_mul_eq_one.1 this

theorem endgame_a {B : Subgroup G} {b : G} {L : Subgroup G} (hB : IsElemAbelian 3 B)
    (hbB : b ∈ B) (hL : GLAPComponent 3 (Cen b) L) {P : Subgroup G} (hPb : P ≤ Cen b)
    (hP3 : IsPGroup 3 P) (hPK : ∀ g ∈ P, CentMod b (bClosure B L) g)
    (hP9 : 9 ≤ Nat.card P) (hcard : Nat.card (Subgroup.center ↥(barImageAt 3 b (bClosure B L))) ≤ 9) :
    P ≤ ⨆ (L' : Subgroup G) (_ : IsBConjugate B L L'), P ⊓ oPrimePOf 3 L' := by
  set K := bClosure B L with hK
  set S : Subgroup G := ⨆ (L' : Subgroup G) (_ : IsBConjugate B L L'), P ⊓ oPrimePOf 3 L' with hS
  have hSP : S ≤ P := iSup₂_le fun _ _ => inf_le_left
  have hPle : barImageAt 3 b P ≤ barCenterAt 3 b K := by
    intro w hw
    obtain ⟨y, hy, hyP, rfl⟩ := bar1_mem_barImageAt_iff.1 hw
    exact (mem_barCenterAt_iff hy).2 (hPK y hyP)
  have hcardP : Nat.card (barCenterAt 3 b K) ≤ Nat.card (barImageAt 3 b P) := by
    rw [card_barCenterAt]
    refine hcard.trans (hP9.trans ?_)
    refine Nat.card_le_card_of_injective
      (fun x : P => (⟨bar1_bar b (hPb x.2), bar1_mem_barImageAt_iff.2 ⟨x, hPb x.2, x.2, rfl⟩⟩ :
        barImageAt 3 b P)) ?_
    intro x x' hxx
    have := congrArg Subtype.val hxx
    exact Subtype.ext (bar3_inj hP3 (hPb x.2) (hPb x'.2) x.2 x'.2 this)
  have hPeq : barImageAt 3 b P = barCenterAt 3 b K := Subgroup.eq_of_le_of_card_ge hPle hcardP
  have hZi : ∀ i : {L' : Subgroup G // IsBConjugate B L L'},
      barCenterAt 3 b i.1 ≤ barImageAt 3 b S := by
    intro i w hw
    have hcomp := bar3_conj_comp hB hbB hL i.2
    have hwK : w ∈ barCenterAt 3 b K := by
      rw [bar3_barCenter_eq hB hbB hL]
      exact le_iSup (fun i : {L' : Subgroup G // IsBConjugate B L L'} => barCenterAt 3 b i.1) i hw
    rw [← hPeq] at hwK
    obtain ⟨y, hy, hyP, rfl⟩ := bar1_mem_barImageAt_iff.1 hwK
    rw [bar1_mem_center_iff] at hw
    obtain ⟨hwI, hc⟩ := hw
    obtain ⟨ℓ, hℓ, hℓL, hℓy⟩ := bar1_mem_barImageAt_iff.1 hwI
    have hnR : ℓ⁻¹ * y ∈ GLAPPrimeCoreOf 3 (Cen b) := (bar1_eq_iff hℓ hy).1 hℓy
    have hysup : y ∈ i.1 ⊔ GLAPPrimeCoreOf 3 (Cen b) := by
      have : y = ℓ * (ℓ⁻¹ * y) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hℓL) (Subgroup.mem_sup_right hnR)
    have hyL : y ∈ i.1 :=
      mem_of_mem_sup_of_pGroup (bar3_core_le_normalizer hcomp)
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three (Cen b)) hysup
        (IsPGroup.to_le hP3 (Subgroup.zpowers_le.2 hyP))
    have hyO : y ∈ oPrimePOf 3 i.1 := by
      refine mem_oPrimePOf_of_forall_commutator_mem Nat.prime_three hyL fun l hl => ?_
      have hlC : l ∈ Cen b := hcomp.1 hl
      have h1 : y * l * y⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) :=
        (bar1_comm_iff hy hlC).1 (hc _ (bar1_mem_barImageAt_iff.2 ⟨l, hlC, hl, rfl⟩))
      have h2 : y * l * y⁻¹ * l⁻¹ ∈ i.1 :=
        mul_mem (mul_mem (mul_mem hyL hl) (inv_mem hyL)) (inv_mem hl)
      rw [bar1_core_eq hcomp]
      exact ⟨h2, h1⟩
    have hyS : y ∈ S :=
      (le_iSup₂ (f := fun (L' : Subgroup G) (_ : IsBConjugate B L L') => P ⊓ oPrimePOf 3 L')
        i.1 i.2) ⟨hyP, hyO⟩
    exact bar1_mem_barImageAt_iff.2 ⟨y, hy, hyS, rfl⟩
  intro g hgP
  have hgC : g ∈ Cen b := hPb hgP
  have hgbar : bar1_bar b hgC ∈ barImageAt 3 b S := by
    have h1 : bar1_bar b hgC ∈ barImageAt 3 b P := bar1_mem_barImageAt_iff.2 ⟨g, hgC, hgP, rfl⟩
    rw [hPeq, bar3_barCenter_eq hB hbB hL] at h1
    exact (iSup_le hZi) h1
  obtain ⟨s, hs, hsS, hsg⟩ := bar1_mem_barImageAt_iff.1 hgbar
  have := bar3_inj hP3 hs hgC (hSP hsS) hgP hsg
  rw [← this]
  exact hsS

end Bar


section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem core_conj_mem_cq {L U : Subgroup G} {g q : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hq : q ∈ centralizerQuot L U) : g * q * g⁻¹ ∈ centralizerQuot L U := by
  obtain ⟨hqL, hqU, hq⟩ := hq
  refine ⟨?_, ?_, fun l hl => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL hqL) (Subgroup.inv_mem _ hgL)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgU hqU) (Subgroup.inv_mem _ hgU)
  · have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgL) l).1 hl
      simpa using this
    have h1 := (Subgroup.mem_normalizer_iff.1 hgU _).1 (hq _ hl')
    have e : l * (g * q * g⁻¹) * l⁻¹ * (g * q * g⁻¹)⁻¹ =
        g * ((g⁻¹ * l * g) * q * (g⁻¹ * l * g)⁻¹ * q⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem core_comm_le_cq {L U W : Subgroup G} {x : G}
    (hW : W ≤ Subgroup.normalizer (L : Set G)) (hWU : W ≤ Subgroup.normalizer (U : Set G))
    (hx : x ∈ centralizerQuot L U) : ⁅W, Subgroup.zpowers x⁆ ≤ centralizerQuot L U := by
  rw [Subgroup.commutator_le]
  intro w hw y hy
  have hy' : y ∈ centralizerQuot L U := (Subgroup.zpowers_le.2 hx) hy
  have h1 := core_conj_mem_cq (hW hw) (hWU hw) hy'
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy')

omit [Finite G] in
theorem core_mem_normalizer_inf {A C : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro y
  have := hA y
  have := hC y
  simp only [Subgroup.mem_inf] at *
  tauto

theorem core_normalizes_delta {p : ℕ} {D : Subgroup G} {x : G}
    (hx : ∀ d ∈ D, x ∈ Cen d) : x ∈ Subgroup.normalizer (GLADelta p D : Set G) := by
  have hconj : ∀ w ∈ GLADelta p D, x * w * x⁻¹ ∈ GLADelta p D := by
    intro w hw
    simp only [GLADelta, Subgroup.mem_iInf] at hw ⊢
    intro d hd hd1
    exact mem_gLAPPrimeCoreOf_conj (hw d hd hd1) (hx d hd)
  exact Subgroup.mem_normalizer_fintype fun n hn => hconj n hn

theorem core_zpowers_cen {W : Subgroup G} {x : G} :
    W ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = W ⊓ Cen x := by
  have : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) = Cen x := by
    ext y
    constructor
    · intro hy
      exact Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hy x (Subgroup.mem_zpowers x)).symm
    · intro hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      have hc : Commute y x := (Subgroup.mem_centralizer_singleton_iff.1 hy)
      exact (Commute.zpow_left hc.symm k).eq
  rw [this]

theorem core_ii (h191 : Input19_1_2) (h196 : Input19_6_9) (h143 : Input14_3_L3) {m : ℕ}
    (hS : GLStanding G m 3) {B D : Subgroup G} {b x : G} {L : Subgroup G}
    (hB : IsBOneMax 3 B) (hD : IsEkIn 3 2 B D) (hb : b ∈ B) (hb1 : b ≠ 1) (h : Config b x L)
    (hX : ¬ ⁅L, delta2At 3 B D b⁆ ≤ GLAPPrimeCoreOf 3 (Cen b))
    (hexc : IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L))
    (hDx : D ≤ Cen x) (hcomp : GLAPComponent 3 (Cen x) (Jstar x L))
    (hbN : b ∈ Subgroup.normalizer (Jstar x L : Set G)) :
    oPrimePOf 3 (Jof x L) ≤ oPrimePOf 3 (Cen x) := by
  haveI := hS.simple
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hDB : D ≤ B := hD.1
  have hDel : IsElemAbelian 3 D := hD.2.1
  have hDcard : Nat.card D = 3 ^ 2 := hD.2.2
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hx3 : x ^ 3 = 1 := by rw [← h.ord]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h1
    have := h.ord
    rw [h1, orderOf_one] at this
    omega
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hDcard
    have : 1 < 3 ^ 2 := by norm_num
    omega
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (elemAbelian_comm hBel hb (hDB hd)).symm
  have hxD : x ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hDx hd))
  have hxCb : x ∈ Cen b := h.hx
  have hbCx : b ∈ Cen x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hxCb).symm
  set R : Subgroup G := GLAPPrimeCoreOf 3 (Cen b) with hR
  set W : Subgroup G := GLADelta 3 D ⊓ Cen b with hWdef
  set RL : Subgroup G := GLAPPrimeCoreOf 3 L with hRL
  have h191b := h191 G hS.nonabelian hS.kProper 3 Nat.prime_three 2 (by norm_num) D hDel hDcard
    b hbD hb1 hb3
  have hW : W ≤ Subgroup.normalizer (L : Set G) := h191b.1 L h.comp
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := fun e he =>
    core_mem_normalizer_inf (le_normalizer_gLADelta hBel hDB he)
      (Subgroup.le_normalizer (le_centralizer_of_mem hBel hb he))
  have hXW : delta2At 3 B D b ≤ W :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.commutator_le_of_normalizer hBW
  have hXW' : ¬ ⁅L, W⁆ ≤ R := fun hh => hX ((Subgroup.commutator_mono le_rfl hXW).trans hh)
  have hxW : x ∈ Subgroup.normalizer (W : Set G) :=
    core_mem_normalizer_inf
      (core_normalizes_delta fun d hd => Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hxD d hd).symm))
      (Subgroup.le_normalizer hxCb)
  have hzx : Subgroup.zpowers x ≤ Subgroup.normalizer (W : Set G) := Subgroup.zpowers_le.2 hxW
  have hWcop : Nat.Coprime 3 (Nat.card W) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_left : W ≤ GLADelta 3 D))
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLADelta Nat.prime_three
        hDne)
  have hPx : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.ord]; norm_num)
  have hdec := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
    hPx hzx hWcop
  rw [core_zpowers_cen] at hdec
  have hRLR : RL ≤ R :=
    CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three h.comp.2.1
  have hRLmem : ∀ g ∈ Subgroup.normalizer (L : Set G), ∀ l ∈ L, l * g * l⁻¹ * g⁻¹ ∈ R →
      l * g * l⁻¹ * g⁻¹ ∈ RL := by
    intro g hg l hl hR'
    have h2 : l * g * l⁻¹ * g⁻¹ ∈ L := by
      have : l * g * l⁻¹ * g⁻¹ = l * (g * l⁻¹ * g⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hl ((Subgroup.mem_normalizer_iff.1 hg l⁻¹).1 (Subgroup.inv_mem _ hl))
    have := glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three h.comp.2.1
    have h3 : l * g * l⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
      rw [← this]
      exact ⟨h2, hR'⟩
    exact h3
  have hxcq : x ∈ centralizerQuot L RL :=
    ⟨h.mem_normalizer, cf2_normalizes_core h.mem_normalizer, fun l hl =>
      hRLmem x h.mem_normalizer l hl
        (h.cen (Subgroup.commutator_mem_commutator hl (Subgroup.mem_zpowers x)))⟩
  have hWU : W ≤ Subgroup.normalizer (RL : Set G) := fun w hw => cf2_normalizes_core (hW hw)
  have hcomm := core_comm_le_cq hW hWU hxcq
  have hZnot : ¬ ⁅Jstar x L, W ⊓ Cen x⁆ ≤ GLAPPrimeCoreOf 3 (Cen x) := by
    intro hJ
    have hZn : W ⊓ Cen x ≤ Subgroup.normalizer (L : Set G) ⊓ Cen x := inf_le_inf_right _ hW
    have ht := h.transfer hZn hJ
    have hZq : W ⊓ Cen x ≤ centralizerQuot L RL := fun z hz =>
      ⟨hW hz.1, cf2_normalizes_core (hW hz.1), fun l hl =>
        hRLmem z (hW hz.1) l hl (ht (Subgroup.commutator_mem_commutator hl hz))⟩
    have hWq : W ≤ centralizerQuot L RL := hdec.trans (sup_le hZq hcomm)
    apply hXW'
    rw [Subgroup.commutator_le]
    intro l hl w hw
    exact hRLR ((hWq hw).2.2 l hl)
  have hnot2 : ¬ ⁅Jstar x L, GLADelta 3 D ⊓ Cen x⁆ ≤ GLAPPrimeCoreOf 3 (Cen x) := fun hh =>
    hZnot ((Subgroup.commutator_mono le_rfl (inf_le_inf_right _ inf_le_left)).trans hh)
  have h191x := h191 G hS.nonabelian hS.kProper 3 Nat.prime_three 2 (by norm_num) D hDel hDcard
    x hxD hx1 hx3
  have h7 := h191x.2 _ hcomp hnot2
  have hCxne : Cen x ≠ ⊤ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.centralizer_ne_top_of_simple hS.nonabelian hx1
  have h8 := h196 G hS.nonabelian hS.kProper (Cen x) _ D hCxne hcomp h7.1 hDel h7.2
  have hJb : Jof x L ≤ Cen b := h.jcomp.1.trans inf_le_right
  have hJ' : GLAPComponent 3 (Jstar x L ⊓ Cen b) (Jof x L) :=
    glaPComponent_of_le Nat.prime_three h.jcomp (le_inf cf2_le_Jstar hJb)
      (inf_le_inf_right _ hcomp.1)
  have hexc' : IsSLThreeExc (barOf 3 (Jof x L)) ∨ IsSUThreeExc (barOf 3 (Jof x L)) := by
    obtain ⟨e⟩ := h.barOf_equiv
    exact isExc_of_equiv e.symm hexc
  have h9 := h143 G hS.nonabelian hS.kProper (Cen x) (Jstar x L) (Jof x L) b hCxne hcomp h8
    hbCx hbN hb3 hJ' hexc'
  exact h9.trans (oPrimePOf_le_of_isSubnormal Nat.prime_three hcomp.2.1)

end Core

section PartII

variable {G : Type} [Group G] [Finite G]

theorem part_b (h18 : Input18_3_4) (h112 : Input11_2_2) (h191 : Input19_1_2)
    (h196 : Input19_6_9) (h143 : Input14_3_L3) {m : ℕ} (hS : GLStanding G m 3)
    {B D : Subgroup G} {b : G} {L Li : Subgroup G} (hs : Lemma24Setup 3 B D b L)
    (hLi : IsBConjugate B L Li)
    (hconc : ∀ L', Lemma24Setup 3 B D b L' → Lemma24Conclusion B D b L')
    {x : G} (hx : x ∈ Cen b) (hord : orderOf x = 3)
    (hc : ⁅Li, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Cen b)) (hDx : D ≤ Cen x)
    (hbeq : barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)) :
    b ∈ oPrimePOf 3 (Cen x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB1 := hs.isBOneMax
  have hBel : IsElemAbelian 3 B := hB1.1.1
  have hsi := setup_conj hs hLi
  have hconcLi := hconc Li hsi
  have cfg : Config b x Li := ⟨hsi.isComp, hx, hord, hc⟩
  have hb3 : b ^ 3 = 1 := hBel.2 b hs.mem
  have hexc := hconcLi.2.1
  have hZ : Subgroup.center (barOf 3 Li) ≠ ⊥ := by
    intro h0
    have := card_center_exc hexc
    rw [h0, Subgroup.card_bot] at this
    omega
  have hbLi : b ∈ Li :=
    mem_of_barCenter_eq hBel hs.mem hs.ne_one hsi.isComp hZ
      (by rw [bClosure_eq_of_isBConjugate hBel.1 hLi]; exact hbeq)
  have hbx : b ∈ Cen x :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
  have hpb : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, orderOf_eq_prime hb3 hs.ne_one]; simp⟩
  have hbJ : b ∈ Jof x Li := cfg.three_mem_J hbLi hbx hpb
  obtain ⟨hcomp, hbN⟩ := claim_ii h18 h112 hS cfg hb3 hexc (Or.inl hbJ)
  have hcore := core_ii h191 h196 h143 hS hB1 hs.isEk hs.mem hs.ne_one cfg hsi.not_centralizes
    hexc hDx hcomp hbN
  refine hcore ?_
  refine mem_oPrimePOf_of_forall_comm Nat.prime_three hbJ (fun y hy => ?_)
  have hyL : y ∈ Li := (cfg.jcomp_inf.1 hy).1
  have hyC : y ∈ Cen b := hsi.isComp.1 hyL
  exact (Subgroup.mem_centralizer_singleton_iff.1 hyC).symm


theorem part_a (h18 : Input18_3_4) (h112 : Input11_2_2) (h191 : Input19_1_2)
    (h196 : Input19_6_9) (h143 : Input14_3_L3) {m : ℕ} (hS : GLStanding G m 3)
    {B D : Subgroup G} {b : G} {L : Subgroup G} (hs : Lemma24Setup 3 B D b L)
    (hconc : ∀ L', Lemma24Setup 3 B D b L' → Lemma24Conclusion B D b L')
    {x : G} (hx : x ∈ Cen b) (hord : orderOf x = 3)
    (ha : barImageAt 3 b (Subgroup.closure {x, b}) ≤ barCenterAt 3 b (bClosure B L)) :
    b ∈ oPrimePOf 3 (Cen x) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB1 := hs.isBOneMax
  have hBel : IsElemAbelian 3 B := hB1.1.1
  have hbB := hs.mem
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hx3 : x ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one x
  have hbb : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hxK : CentMod b (bClosure B L) x :=
    centMod_of_barImage_le ha (Subgroup.subset_closure (by simp)) hx
  have hbK : CentMod b (bClosure B L) b :=
    centMod_of_barImage_le ha (Subgroup.subset_closure (by simp)) hbb
  obtain ⟨n, hn, hnK, hP3, hxx⟩ := exists_good_conj hBel hbB hx3 hxK
  have hx'b : n * x * n⁻¹ ∈ Cen b := (Cen b).mul_mem ((Cen b).mul_mem hn hx) ((Cen b).inv_mem hn)
  have hx'ord : orderOf (n * x * n⁻¹) = 3 := by
    rw [← hord]
    exact orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective x
  have hxK' : CentMod b (bClosure B L) (n * x * n⁻¹) := hxK.congr hx'b hxx
  generalize hx'def : n * x * n⁻¹ = x' at hx'b hx'ord hxK' hP3 hxx
  have hx'1 : x' ≠ 1 := by
    intro h; rw [h, orderOf_one] at hx'ord; omega
  have hx'3 : x' ^ 3 = 1 := by rw [← hx'ord]; exact pow_orderOf_eq_one x'
  have hcardZ : Nat.card (Subgroup.center ↥(barImageAt 3 b (bClosure B L))) ≤ 9 :=
    (hconc L hs).2.2.2.1.2
  have hidx : (Cen x').relIndex B ≤ 3 :=
    relIndex_le_three_a hBel hbB hx'b hx'1 hP3 hxK' hcardZ
  obtain ⟨B', hB'el, hB'x, hB'rk, hbB'⟩ := exists_elemAbelian_ge hBel hx'3 hidx
  have hbx' : b ∈ Cen x' :=
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1 hx'b).symm
  have hbB'' : b ∈ B' := hbB' ⟨hbB, hbx'⟩
  have hrank : GLATwoLocalRank 3 ↥(Cen x') ≤ CFSG.Open.pRank 3 B' :=
    (glaTwoLocalRank_subgroup_le Nat.prime_three (Cen x')).trans
      (hS.rank_eq.le.trans ((hS.le_pRank' hB1).trans hB'rk))
  have hDx' : D ≤ Cen x' := by
    intro d hd
    have hdB : d ∈ B := hs.isEk.1 hd
    have h1 : d * x' * d⁻¹ * x'⁻¹ ∈ GLAPPrimeCoreOf 3 (Cen b) :=
      D_cen_barCenter hBel hbB hs.isEk.1 hs.isComp
        (fun L' hL' => (hconc L' (setup_conj hs hL')).2.2.1.1)
        (fun L' hL' => card_center_exc (hconc L' (setup_conj hs hL')).2.1) hd hxK'
    have hdP : d ∈ B ⊔ Subgroup.zpowers x' := Subgroup.mem_sup_left hdB
    have hx'P : x' ∈ B ⊔ Subgroup.zpowers x' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
    have hgP : d * x' * d⁻¹ * x'⁻¹ ∈ B ⊔ Subgroup.zpowers x' :=
      mul_mem (mul_mem (mul_mem hdP hx'P) (inv_mem hdP)) (inv_mem hx'P)
    have hg1 : d * x' * d⁻¹ * x'⁻¹ = 1 :=
      eq_one_of_mem_core_of_pGroup h1 (hP3.to_le ((Subgroup.zpowers_le).2 hgP))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : d * x' = x' * d := by
      have h2 : d * x' * d⁻¹ = x' := by
        have := congrArg (· * x') hg1
        simpa [mul_assoc] using this
      calc d * x' = (d * x' * d⁻¹) * d := by group
        _ = x' * d := by rw [h2]
    exact this
  set P' : Subgroup G := Subgroup.zpowers x' ⊔ Subgroup.zpowers b with hP'def
  have hbP' : b ∈ P' := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
  have hP'le : P' ≤ B ⊔ Subgroup.zpowers x' := by
    refine sup_le ?_ ?_
    · exact le_sup_right
    · exact (Subgroup.zpowers_le).2 (Subgroup.mem_sup_left hbB)
  have hP'3 : IsPGroup 3 P' := hP3.to_le hP'le
  have hP'x : P' ≤ Cen x' := by
    refine sup_le ?_ ?_
    · refine (Subgroup.zpowers_le).2 ?_
      exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    · exact (Subgroup.zpowers_le).2 hbx'
  have hP'b : P' ≤ Cen b := by
    refine sup_le ?_ ?_
    · exact (Subgroup.zpowers_le).2 hx'b
    · exact (Subgroup.zpowers_le).2 hbb
  have hP'K : P' ≤ centModSub b (bClosure B L) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.zpowers_le).2 hxK'
    · exact (Subgroup.zpowers_le).2 hbK
  have hconj : ∀ L', IsBConjugate B L L' → P' ⊓ oPrimePOf 3 L' ≤ oPrimePOf 3 (Cen x') := by
    intro L' hL' y hy
    have hs' := setup_conj hs hL'
    have hc' := hconc L' hs'
    have hLK : L' ≤ bClosure B L := by
      obtain ⟨g, hg, rfl⟩ := hL'
      exact le_iSup₂ (f := fun (b : G) (_ : b ∈ B) => GLBConj b L) g hg
    have cfg' : Config b x' L' := Config.of_centMod hs'.isComp hLK hxK' hx'ord
    have hexc' := hc'.2.1
    obtain ⟨hcomp', hbN'⟩ := claim_ii h18 h112 hS cfg' hb3 hexc'
      (Or.inr ⟨B', hB'el, hB'x, hrank, hbB''⟩)
    have hcore' := core_ii h191 h196 h143 hS hB1 hs.isEk hbB hs.ne_one cfg' hs'.not_centralizes
      hexc' hDx' hcomp' hbN'
    have hyL' : y ∈ L' := Subgroup.map_subtype_le _ hy.2
    have hyx : y ∈ Cen x' := hP'x hy.1
    have hy3 : IsPGroup 3 (Subgroup.zpowers y) := hP'3.to_le ((Subgroup.zpowers_le).2 hy.1)
    exact hcore' (cfg'.mem_oPrimeP_J hyL' hyx hy3 hy.2)
  have hbQ : b ∈ oPrimePOf 3 (Cen x') := by
    by_cases hbz : b ∈ Subgroup.zpowers x'
    · have hx'Q : x' ∈ oPrimePOf 3 (Cen x') :=
        mem_oPrimePOf_of_forall_comm Nat.prime_three (Subgroup.mem_centralizer_singleton_iff.2 rfl)
          (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 hy).symm)
      exact ((Subgroup.zpowers_le).2 hx'Q) hbz
    · have hP9 : 9 ≤ Nat.card P' := by
        have h1 := card_sup_zpowers_of_pow_three_eq_one (H := Subgroup.zpowers x') hb3 hbz
          (fun h hh => by
            obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
            exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 hx'b).symm.symm k)).eq)
        rw [Nat.card_zpowers, hx'ord] at h1
        calc 9 = 3 * 3 := by norm_num
          _ ≤ Nat.card P' := h1.symm.le
      have hend := endgame_a hBel hbB hs.isComp hP'b hP'3 (fun g hg => hP'K hg) hP9 hcardZ
      have hle : P' ≤ oPrimePOf 3 (Cen x') :=
        hend.trans (iSup₂_le fun L' hL' => hconj L' hL')
      exact hle hbP'
  have hcen : Cen x' = GLBConj n⁻¹ (Cen x) := by rw [← hx'def]; exact Cen_conj n x
  rw [hcen, oPrimePOf_gLBConj, mem_gLBConj] at hbQ
  have hnb : n⁻¹ * b * n⁻¹⁻¹ = b := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hn
    simp only [inv_inv]
    calc n⁻¹ * b * n = n⁻¹ * (b * n) := by group
      _ = n⁻¹ * (n * b) := by rw [this]
      _ = b := by group
  rwa [hnb] at hbQ

end PartII


end Lemma25Ns

open Lemma25Ns CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem lemma25_of_inputs (h24 : Lemma24) (h18 : Input18_3_4) (h112 : Input11_2_2)
    (h191 : Input19_1_2) (h196 : Input19_6_9) (h143 : Input14_3_L3) : Lemma25Strong := by
  intro G _ _ m hS B D b L hs Li hLi x hx hord hc
  show (x ∈ B → Lemma24Setup 3 B D x (Jstar x Li) ∧ Lemma24Conclusion B D x (Jstar x Li)) ∧
    ((barImageAt 3 b (Subgroup.closure {x, b}) ≤ barCenterAt 3 b (bClosure B L) ∨
        (D ≤ Subgroup.centralizer ({x} : Set G) ∧
          barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L))) →
      b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB1 : IsBOneMax 3 B := hs.isBOneMax
  have hBel : IsElemAbelian 3 B := hB1.1.1
  have hD := hs.isEk
  have hb := hs.mem
  have hb1 := hs.ne_one
  have hnwb : ¬ IsWeaklyBalancedWrt 3 2 B := fun hw => hs.not_le (hw D hD b hb hb1)
  have hsi : Lemma24Setup 3 B D b Li := setup_conj hs hLi
  have h24' := h24 G m 3 hS B hB1 hnwb D hD b hb hb1 hs.not_le
  have hconc : ∀ L', Lemma24Setup 3 B D b L' → Lemma24Conclusion B D b L' := h24'.2.2
  have hconcLi := hconc Li hsi
  have cfg : Config b x Li := ⟨hsi.isComp, hx, hord, hc⟩
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hx1 : x ≠ 1 := fun h => by simp [h] at hord
  have hexc : IsSLThreeExc (barOf 3 Li) ∨ IsSUThreeExc (barOf 3 Li) := hconcLi.2.1
  refine ⟨fun hxB => ?_, fun hyp => ?_⟩
  ·
    have hBx : B ≤ Cen x := parti_B_le_cen hBel hxB
    have hrk : GLATwoLocalRank 3 ↥(Cen x) ≤ CFSG.Open.pRank 3 B :=
      (glaTwoLocalRank_subgroup_le Nat.prime_three (Cen x)).trans
        (hS.rank_eq.le.trans (hS.le_pRank' hB1))
    obtain ⟨hcomp, -⟩ := claim_ii h18 h112 hS cfg hb3 hexc (Or.inr ⟨B, hBel, hBx, hrk, hb⟩)
    have hnc := not_centralizes_i hB1 hD hb hxB cfg hconcLi.2.2.1.2.1 hsi.not_centralizes
    have hnl := not_le_of_not_centralizes hcomp.1 hnc
    have hsetup : Lemma24Setup 3 B D x (Jstar x Li) := ⟨hB1, hD, hxB, hx1, hnl, hcomp, hnc⟩
    exact ⟨hsetup, (h24 G m 3 hS B hB1 hnwb D hD x hxB hx1 hnl).2.2 _ hsetup⟩
  · rcases hyp with ha | ⟨hDx, hbeq⟩
    · exact part_a h18 h112 h191 h196 h143 hS hs hconc hx hord ha
    · exact part_b h18 h112 h191 h196 h143 hS hs hLi hconc hx hord hc hDx hbeq

open Lemma25Ns CFSG.HardMathSupport.Solomon.UniquenessMaximal in
theorem lemma25_of_inputs_weak (h24 : Lemma24) (h18 : Input18_3_4) (h112 : Input11_2_2)
    (h191 : Input19_1_2) (h196 : Input19_6_9) (h143 : Input14_3_L3) : Lemma25 :=
  lemma25_of_strong (lemma25_of_inputs h24 h18 h112 h191 h196 h143)

end CFSG.HardMathSupport.Solomon.LocalBalance
