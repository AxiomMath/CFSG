module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQ44

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]


private theorem elemModulo_map_conj {N E : Subgroup G} {g : G} (hgN : g ∈ normalizer (N : Set G))
    (hE : ElemModulo N E) : ElemModulo N (E.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  obtain ⟨h1, h2⟩ := hE x hx y hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨?_, ?_⟩
  · rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgN _).1 h1
  · rw [commutatorElement_def] at h2 ⊢
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
      g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgN _).1 h2

theorem maximal_map_conj {N Q : Subgroup G} {g : G}
    (hgN : g ∈ normalizer (N : Set G)) (hgQ : g ∈ normalizer (Q : Set G)) {E : Subgroup G}
    (hE : Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') E) :
    Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E')
      (E.map (MulAut.conj g).toMonoidHom) := by
  have key : ∀ {g : G}, g ∈ normalizer (N : Set G) → g ∈ normalizer (Q : Set G) →
      ∀ {E' : Subgroup G}, (N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') →
        (N ≤ E'.map (MulAut.conj g).toMonoidHom ∧ E'.map (MulAut.conj g).toMonoidHom ≤ Q ∧
          ElemModulo N (E'.map (MulAut.conj g).toMonoidHom)) := by
    intro g hgN hgQ E' ⟨h1, h2, h3⟩
    refine ⟨fun n hn => ?_, ?_, elemModulo_map_conj hgN h3⟩
    · refine ⟨g⁻¹ * n * g, h1 ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      have := (mem_normalizer_iff.1 (inv_mem hgN) n).1 hn
      simpa using this
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hgQ x).1 (h2 hx)
  refine ⟨key hgN hgQ hE.1, fun y hy hEy => ?_⟩
  have hy' := key (inv_mem hgN) (inv_mem hgQ) hy
  have hEy' : E ≤ y.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g * x * g⁻¹, hEy ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle := hE.2 hy' hEy'
  intro z hz
  refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have : g⁻¹ * z * g ∈ y.map (MulAut.conj g⁻¹).toMonoidHom :=
    ⟨z, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  exact hle this

theorem maximal_elemModulo_iff_sup_zpowers {N A C : Subgroup G} {t : G}
    (hNA : N ≤ A) (hCA : C ≤ A) (ht2 : t * t = 1) (htA : t ∉ A)
    (htA' : t ∈ normalizer (A : Set G)) (htN : t ∈ normalizer (N : Set G))
    (hA : ElemModulo N A) (hC : ∀ a ∈ A, a ∈ C ↔ t * a * t * a⁻¹ ∈ N) (hne : ∃ a ∈ A, a ∉ C)
    (X : Subgroup G) :
    Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ A ⊔ zpowers t ∧ ElemModulo N E') X ↔
      X = A ∨ X = C ⊔ zpowers t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htt : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, ht2, one_mul]
  have key : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a ha n hn => by
    have h2 := (hA a ha n (hNA hn)).2
    rw [commutatorElement_def] at h2
    have := mul_mem h2 hn
    rwa [show a * n * a⁻¹ * n⁻¹ * n = a * n * a⁻¹ by group] at this
  have hAN : A ≤ normalizer (N : Set G) := fun a ha => by
    rw [mem_normalizer_iff]
    intro n
    refine ⟨key a ha n, fun hn => ?_⟩
    have := key a⁻¹ (inv_mem ha) _ hn
    rwa [show a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n by group] at this
  have htN' : ∀ n ∈ N, t * n * t ∈ N := fun n hn => by
    have := (mem_normalizer_iff.1 htN n).1 hn
    rwa [htinv] at this
  have htA'' : ∀ a ∈ A, t * a * t ∈ A := fun a ha => by
    have := (mem_normalizer_iff.1 htA' a).1 ha
    rwa [htinv] at this
  have hCN : N ≤ C := fun n hn => (hC n (hNA hn)).2 (mul_mem (htN' n hn) (inv_mem hn))
  have htCc : ∀ c ∈ C, t * c * t ∈ C := fun c hc => by
    have hcA : c ∈ A := hCA hc
    have hn : t * c * t * c⁻¹ ∈ N := (hC c hcA).1 hc
    refine (hC _ (htA'' c hcA)).2 ?_
    have e : t * (t * c * t) * t * (t * c * t)⁻¹ = (t * c * t * c⁻¹)⁻¹ := by
      simp only [mul_inv_rev, htinv, inv_inv, mul_assoc, htt]
    rw [e]
    exact inv_mem hn
  have htC : t ∈ normalizer (C : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · have := htCc h hh
      rwa [htinv]
    · have := htCc _ hh
      rwa [htinv, show t * (t * h * t) * t = (t * t) * h * (t * t) by group, ht2,
        one_mul, mul_one] at this
  have hPA : N ≤ A ∧ A ≤ A ⊔ zpowers t ∧ ElemModulo N A := ⟨hNA, le_sup_left, hA⟩
  have hPC : N ≤ C ⊔ zpowers t ∧ C ⊔ zpowers t ≤ A ⊔ zpowers t ∧
      ElemModulo N (C ⊔ zpowers t) := by
    refine ⟨hCN.trans le_sup_left, sup_le_sup_right hCA _, ?_⟩
    refine elemModulo_of_mul_self_mem (sup_le (hCA.trans hAN) ((zpowers_le).2 htN)) fun x hx => ?_
    rcases (mem_sup_zpowers_iff_of ht2 htC).1 hx with h1 | ⟨c, hc, rfl⟩
    · exact (hA x (hCA h1) x (hCA h1)).1
    · have hcA := hCA hc
      have hn : t * c * t * c⁻¹ ∈ N := (hC c hcA).1 hc
      rw [show c * t * (c * t) = (c * (t * c * t * c⁻¹) * c⁻¹) * (c * c) by group]
      exact mul_mem (key c hcA _ hn) (hA c hcA c hcA).1
  have hdich : ∀ E' : Subgroup G, N ≤ E' → E' ≤ A ⊔ zpowers t → ElemModulo N E' →
      E' ≤ A ∨ E' ≤ C ⊔ zpowers t := by
    intro E' hNE' hE'A hE'
    by_cases hle : E' ≤ A
    · exact Or.inl hle
    right
    obtain ⟨x₀, hx₀E, hx₀A⟩ := Set.not_subset.1 hle
    obtain ⟨a₀, ha₀, rfl⟩ : ∃ a₀ ∈ A, x₀ = a₀ * t := by
      rcases (mem_sup_zpowers_iff_of ht2 htA').1 (hE'A hx₀E) with h1 | h1
      · exact absurd h1 hx₀A
      · exact h1
    have ha₀C : a₀ ∈ C := by
      refine (hC a₀ ha₀).2 ?_
      have hz : a₀ * t * a₀ * t ∈ N := by
        have := (hE' _ hx₀E _ hx₀E).1
        rwa [show a₀ * t * (a₀ * t) = a₀ * t * a₀ * t by group] at this
      have e : t * a₀ * t * a₀⁻¹ = (a₀⁻¹ * (a₀ * t * a₀ * t) * a₀⁻¹⁻¹) * (a₀⁻¹ * a₀⁻¹) := by
        have : t * a₀ * t = a₀⁻¹ * (a₀ * t * a₀ * t) := by group
        rw [this]
        group
      rw [e]
      exact mul_mem (key a₀⁻¹ (inv_mem ha₀) _ hz) (hA a₀⁻¹ (inv_mem ha₀) a₀⁻¹ (inv_mem ha₀)).1
    have hyA : ∀ y ∈ E', y ∈ A → y ∈ C := fun y hyE hyA => by
      refine (hC y hyA).2 ?_
      have h1 := (hE' _ hx₀E y hyE).2
      rw [commutatorElement_def] at h1
      have h2 := (hA a₀ ha₀ _ (htA'' y hyA)).2
      rw [commutatorElement_def] at h2
      have e1 : a₀ * t * y * (a₀ * t)⁻¹ * y⁻¹ = a₀ * (t * y * t) * a₀⁻¹ * y⁻¹ := by
        simp only [mul_inv_rev, htinv]
        group
      have e : t * y * t * y⁻¹ = (a₀ * (t * y * t) * a₀⁻¹ * (t * y * t)⁻¹)⁻¹ *
          (a₀ * t * y * (a₀ * t)⁻¹ * y⁻¹) := by
        rw [e1]
        group
      rw [e]
      exact mul_mem (inv_mem h2) h1
    intro y hy
    rcases (mem_sup_zpowers_iff_of ht2 htA').1 (hE'A hy) with h1 | ⟨a, ha, rfl⟩
    · exact mem_sup_left (hyA y hy h1)
    · have hmem : a * t * (a₀ * t)⁻¹ ∈ E' := mul_mem hy (inv_mem hx₀E)
      have e2 : a * t * (a₀ * t)⁻¹ = a * a₀⁻¹ := by
        simp only [mul_inv_rev, htinv, mul_assoc, htt]
      have hmemA : a * t * (a₀ * t)⁻¹ ∈ A := by
        rw [e2]
        exact mul_mem ha (inv_mem ha₀)
      have h3 := hyA _ hmem hmemA
      rw [e2] at h3
      have haC : a ∈ C := by
        have := mul_mem h3 ha₀C
        rwa [inv_mul_cancel_right] at this
      exact mul_mem (mem_sup_left haC) (mem_sup_right (mem_zpowers t))
  constructor
  · rintro ⟨hP, hmax⟩
    rcases hdich X hP.1 hP.2.1 hP.2.2 with hXA | hXC
    · exact Or.inl (le_antisymm hXA (hmax hPA hXA))
    · exact Or.inr (le_antisymm hXC (hmax hPC hXC))
  · rintro (rfl | rfl)
    · refine ⟨hPA, fun Y hY hAY => ?_⟩
      rcases hdich Y hY.1 hY.2.1 hY.2.2 with h' | h'
      · exact h'
      · exfalso
        obtain ⟨a, ha, haC⟩ := hne
        rcases (mem_sup_zpowers_iff_of ht2 htC).1 (h' (hAY ha)) with h1 | ⟨c, hc, e⟩
        · exact haC h1
        · refine htA ?_
          have := mul_mem (inv_mem (hCA hc)) ha
          rwa [e, inv_mul_cancel_left] at this
    · refine ⟨hPC, fun Y hY hCY => ?_⟩
      rcases hdich Y hY.1 hY.2.1 hY.2.2 with h' | h'
      · exact absurd (h' (hCY (mem_sup_right (mem_zpowers t)))) htA
      · exact h'


private theorem elemModulo_sup_of_le_normalizer {A B N : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hN : A ⊔ B ≤ normalizer (N : Set G)) (hA : ElemModulo N A) (hB : ElemModulo N B)
    (hc : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) : ElemModulo N (A ⊔ B) := by
  refine elemModulo_of_mul_self_mem hN fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer' hAB x hx
  have hbN : b ∈ normalizer (N : Set G) := hN (mem_sup_right hb)
  have e : a * b * (a * b) = ⁅a, b⁆ * (b * (a * a) * b⁻¹) * (b * b) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem (mul_mem (hc a ha b hb) ((mem_normalizer_iff.1 hbN _).1 (hA a ha a ha).1))
    (hB b hb b hb).1

private theorem mul_self_eq_one_of_elementaryAbelian {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A)
    {a : G} (ha : a ∈ A) : a * a = 1 := by
  have := hA
  rw [← sq]
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha

private theorem mul_comm_of_elementaryAbelian {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := by
  have := hA
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)

private theorem elemModulo_of_elementaryAbelian {N A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 A) :
    ElemModulo N A := fun x hx y hy => by
  refine ⟨?_, ?_⟩
  · rw [mul_self_eq_one_of_elementaryAbelian hA hx]
    exact one_mem _
  · rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = 1 by
      rw [mul_comm_of_elementaryAbelian hA hx hy]; group]
    exact one_mem _

private theorem commutator_mem_of_coprime_fixed {S V N₀ J' : Subgroup G}
    (hSV : S ≤ normalizer (V : Set G)) (hSN : S ≤ normalizer (N₀ : Set G))
    (hVN : V ≤ normalizer (N₀ : Set G))
    (hJS : J' ≤ normalizer (S : Set G)) (hJV : J' ≤ normalizer (V : Set G))
    (hJN : J' ≤ normalizer (N₀ : Set G))
    (hcop : ∀ {T : Subgroup G}, T ≤ S → S ≤ normalizer (T : Set G) →
      J' ≤ normalizer (T : Set G) → ∀ {m : G}, m ∈ S → (∀ j ∈ J', m⁻¹ * (j * m * j⁻¹) ∈ T) →
        ∃ c ∈ S ⊓ centralizer (J' : Set G), ∃ n ∈ T, m = c * n)
    (hjV : ∀ v ∈ V, ∀ j ∈ J', v⁻¹ * (j * v * j⁻¹) ∈ N₀)
    (hC : ∀ c ∈ S ⊓ centralizer (J' : Set G), ∀ v ∈ V, c * v * c⁻¹ * v⁻¹ ∈ N₀) :
    ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ ∈ N₀ := by
  set T : Subgroup G := S ⊓ centralizerModulo N₀ V with hT
  have hTS : T ≤ S := inf_le_left
  have hconj : ∀ g : G, g ∈ normalizer (S : Set G) → g ∈ normalizer (V : Set G) →
      g ∈ normalizer (N₀ : Set G) → ∀ m ∈ T, g * m * g⁻¹ ∈ T := by
    intro g hgS hgV hgN m hm
    obtain ⟨hmS, hmC⟩ := Subgroup.mem_inf.1 hm
    obtain ⟨hmN, hmV⟩ := mem_centralizerModulo_iff.1 hmC
    refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hgS m).1 hmS,
      mem_centralizerModulo_iff.2 ⟨mul_mem (mul_mem hgN hmN) (inv_mem hgN), fun x hx => ?_⟩⟩
    have hx' : g⁻¹ * x * g ∈ V := by
      have := (mem_normalizer_iff.1 (inv_mem hgV) x).1 hx
      rwa [inv_inv] at this
    have h1 := (mem_normalizer_iff.1 hgN _).1 (hmV (g⁻¹ * x * g) hx')
    rwa [show g * (m * (g⁻¹ * x * g) * m⁻¹ * (g⁻¹ * x * g)⁻¹) * g⁻¹ =
      g * m * g⁻¹ * x * (g * m * g⁻¹)⁻¹ * x⁻¹ by group] at h1
  have hnormT : ∀ g : G, g ∈ normalizer (S : Set G) → g ∈ normalizer (V : Set G) →
      g ∈ normalizer (N₀ : Set G) → g ∈ normalizer (T : Set G) := fun g hgS hgV hgN =>
    mem_normalizer_iff.2 fun m => ⟨fun hm => hconj g hgS hgV hgN m hm, fun hm => by
      have := hconj g⁻¹ (inv_mem hgS) (inv_mem hgV) (inv_mem hgN) _ hm
      rwa [show g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m by group] at this⟩
  have hSnT : S ≤ normalizer (T : Set G) := fun g hg =>
    hnormT g (Subgroup.le_normalizer hg) (hSV hg) (hSN hg)
  have hJnT : J' ≤ normalizer (T : Set G) := fun j hj => hnormT j (hJS hj) (hJV hj) (hJN hj)
  have hfix : ∀ m ∈ S, ∀ j ∈ J', m⁻¹ * (j * m * j⁻¹) ∈ T := by
    intro m hm j hj
    have hm' : j * m * j⁻¹ ∈ S := (mem_normalizer_iff.1 (hJS hj) m).1 hm
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hm) hm', mem_centralizerModulo_iff.2
      ⟨mul_mem (inv_mem (hSN hm)) (hSN hm'), fun x hx => ?_⟩⟩
    have hx₁V : j⁻¹ * x * j ∈ V := by
      have := (mem_normalizer_iff.1 (hJV (inv_mem hj)) x).1 hx
      rwa [inv_inv] at this
    have hxx₁ : x⁻¹ * (j⁻¹ * x * j) ∈ N₀ := by
      have := hjV x hx j⁻¹ (inv_mem hj)
      rwa [inv_inv] at this
    have hyV : m * x * m⁻¹ ∈ V := (mem_normalizer_iff.1 (hSV hm) x).1 hx
    have hyy₁ : (m * x * m⁻¹)⁻¹ * (m * (j⁻¹ * x * j) * m⁻¹) ∈ N₀ := by
      have := (mem_normalizer_iff.1 (hSN hm) _).1 hxx₁
      rwa [show m * (x⁻¹ * (j⁻¹ * x * j)) * m⁻¹ = (m * x * m⁻¹)⁻¹ * (m * (j⁻¹ * x * j) * m⁻¹) by
        group] at this
    have hjy := hjV _ hyV j hj
    have hjyy₁ : (j * (m * x * m⁻¹) * j⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹) ∈ N₀ := by
      have := (mem_normalizer_iff.1 (hJN hj) _).1 hyy₁
      rwa [show j * ((m * x * m⁻¹)⁻¹ * (m * (j⁻¹ * x * j) * m⁻¹)) * j⁻¹ =
        (j * (m * x * m⁻¹) * j⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹) by group] at this
    have hn : (m * x * m⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹) ∈ N₀ := by
      have := mul_mem hjy hjyy₁
      rwa [show (m * x * m⁻¹)⁻¹ * (j * (m * x * m⁻¹) * j⁻¹) *
        ((j * (m * x * m⁻¹) * j⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹)) =
        (m * x * m⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹) by group] at this
    have h2 := (mem_normalizer_iff.1 (hSN (inv_mem hm)) _).1 hn
    rw [inv_inv] at h2
    have h3 := (mem_normalizer_iff.1 (hVN hx) _).1 h2
    rwa [show x * (m⁻¹ * ((m * x * m⁻¹)⁻¹ * (j * (m * (j⁻¹ * x * j) * m⁻¹) * j⁻¹)) * m) * x⁻¹ =
      m⁻¹ * (j * m * j⁻¹) * x * (m⁻¹ * (j * m * j⁻¹))⁻¹ * x⁻¹ by group] at h3
  intro s hs v hv
  obtain ⟨c, hc, n, hn, rfl⟩ := hcop hTS hSnT hJnT hs fun j hj => hfix s hs j hj
  have hcS : c ∈ S := (Subgroup.mem_inf.1 hc).1
  have h1 := (mem_normalizer_iff.1 (hSN hcS) _).1
    ((mem_centralizerModulo_iff.1 (Subgroup.mem_inf.1 hn).2).2 v hv)
  have h2 := hC c hc v hv
  have := mul_mem h1 h2
  rwa [show c * (n * v * n⁻¹ * v⁻¹) * c⁻¹ * (c * v * c⁻¹ * v⁻¹) = c * n * v * (c * n)⁻¹ * v⁻¹ by
    group] at this

private def barImage (H N E : Subgroup G) [(N.subgroupOf H).Normal] : Subgroup (H ⧸ N.subgroupOf H) :=
  (E.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))

private theorem mem_barImage {H N E : Subgroup G} [(N.subgroupOf H).Normal]
    {q : H ⧸ N.subgroupOf H} :
    q ∈ barImage H N E ↔ ∃ y : H, (y : G) ∈ E ∧ QuotientGroup.mk' (N.subgroupOf H) y = q := by
  simp [barImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]

private theorem mem_barImage_iff {H N E : Subgroup G} [(N.subgroupOf H).Normal] (hNE : N ≤ E) (x : H) :
    QuotientGroup.mk' (N.subgroupOf H) x ∈ barImage H N E ↔ (x : G) ∈ E := by
  rw [mem_barImage]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : (y : H)⁻¹ * x ∈ N.subgroupOf H := QuotientGroup.eq.mp hyx
    rw [mem_subgroupOf] at h1
    have h2 : (y : G)⁻¹ * (x : G) ∈ E := hNE h1
    simpa using E.mul_mem hy h2
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem barImage_mono {H N E E' : Subgroup G} [(N.subgroupOf H).Normal] (h : E ≤ E') :
    barImage H N E ≤ barImage H N E' := by
  intro q hq
  obtain ⟨y, hy, rfl⟩ := mem_barImage.1 hq
  exact mem_barImage.2 ⟨y, h hy, rfl⟩

private theorem barImage_sup {H N E E' : Subgroup G} [(N.subgroupOf H).Normal] (hE : E ≤ H)
    (hE' : E' ≤ H) :
    barImage H N (E ⊔ E') = barImage H N E ⊔ barImage H N E' := by
  unfold barImage
  rw [Subgroup.subgroupOf_sup hE hE', Subgroup.map_sup]

private theorem commute_mk_iff {H N : Subgroup G} [(N.subgroupOf H).Normal] (x y : H) :
    Commute (QuotientGroup.mk' (N.subgroupOf H) x) (QuotientGroup.mk' (N.subgroupOf H) y) ↔
      ⁅(x : G), (y : G)⁆ ∈ N := by
  rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, mem_subgroupOf]
  simp [commutatorElement_def]

private theorem isMulCommutative_barImage {H N E : Subgroup G} [(N.subgroupOf H).Normal]
    (hE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ N) : IsMulCommutative (barImage H N E) := by
  rw [isMulCommutative_iff]
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨x, hx, rfl⟩ := mem_barImage.1 ha
  obtain ⟨y, hy, rfl⟩ := mem_barImage.1 hb
  exact Subtype.ext ((commute_mk_iff x y).2 (hE x hx y hy))

private theorem forall_commutator_mem_of_isMulCommutative_barImage {H N E : Subgroup G}
    [(N.subgroupOf H).Normal] (hNE : N ≤ E) (hEH : E ≤ H) [IsMulCommutative (barImage H N E)] :
    ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ N := by
  intro x hx y hy
  refine (commute_mk_iff (⟨x, hEH hx⟩ : H) ⟨y, hEH hy⟩).1 ?_
  exact congrArg Subtype.val (mul_comm'
    (⟨_, (mem_barImage_iff hNE (⟨x, hEH hx⟩ : H)).2 hx⟩ : barImage H N E)
    ⟨_, (mem_barImage_iff hNE (⟨y, hEH hy⟩ : H)).2 hy⟩)

private theorem exists_barImage_eq {H N : Subgroup G} [(N.subgroupOf H).Normal] (hNH : N ≤ H)
    (Ebar : Subgroup (H ⧸ N.subgroupOf H)) :
    ∃ E : Subgroup G, N ≤ E ∧ E ≤ H ∧ barImage H N E = Ebar := by
  refine ⟨(Ebar.comap (QuotientGroup.mk' (N.subgroupOf H))).map H.subtype, ?_,
    Subgroup.map_subtype_le _, ?_⟩
  · intro n hn
    refine ⟨⟨n, hNH hn⟩, ?_, rfl⟩
    have h1 : (⟨n, hNH hn⟩ : H) ∈ N.subgroupOf H := hn
    have h2 : QuotientGroup.mk' (N.subgroupOf H) ⟨n, hNH hn⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 h1
    show QuotientGroup.mk' (N.subgroupOf H) ⟨n, hNH hn⟩ ∈ Ebar
    rw [h2]
    exact Ebar.one_mem
  · ext q
    rw [mem_barImage]
    constructor
    · rintro ⟨y, ⟨z, hz, hzy⟩, rfl⟩
      have h1 : z = y := Subtype.ext hzy
      subst h1
      exact hz
    · intro hq
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨y, ⟨y, hq, rfl⟩, rfl⟩

private theorem card_eq_card_barImage_mul {H N E : Subgroup G} [(N.subgroupOf H).Normal] (hNE : N ≤ E)
    (hEH : E ≤ H) : Nat.card E = Nat.card (barImage H N E) * Nat.card N := by
  let f : E →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion hEH)
  have hrange : f.range = barImage H N E := by
    ext q
    rw [MonoidHom.mem_range, mem_barImage]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨Subgroup.inclusion hEH e, e.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : f.ker = N.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    change (QuotientGroup.mk (Subgroup.inclusion hEH e) : H ⧸ N.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    rfl
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker, hker, hrange] at h
  rw [← h, mul_comm]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNE).toEquiv

private theorem isElementaryAbelian_barImage {H N E : Subgroup G} [(N.subgroupOf H).Normal]
    (hE : ElemModulo N E) : IsElementaryAbelian 2 (barImage H N E) := by
  have hcomm : IsMulCommutative (barImage H N E) :=
    isMulCommutative_barImage fun x hx y hy => (hE x hx y hy).2
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  rintro ⟨q, hq⟩
  obtain ⟨y, hy, rfl⟩ := mem_barImage.1 hq
  apply Subtype.ext
  change (QuotientGroup.mk' (N.subgroupOf H) y) ^ 2 = 1
  rw [← map_pow, pow_two, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
  exact (hE y hy y hy).1

private theorem card_le_max_of_forall_commutator_mem [Finite G]
    {H S₀ A B N X : Subgroup G} [(N.subgroupOf H).Normal]
    (hNA : N ≤ A) (hNB : N ≤ B) (hAS : A ≤ S₀) (hBS : B ≤ S₀) (hSH : S₀ ≤ H)
    (hex : ∀ s ∈ S₀, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hAel : ElemModulo N A) (hBel : ElemModulo N B)
    (hnonab : ∃ x ∈ S₀, ∃ y ∈ S₀, ⁅x, y⁆ ∉ N)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S₀, ⁅s, a⁆ ∈ N → s ∈ A)
    (hNX : N ≤ X) (hXS : X ≤ S₀) (hX : ∀ x ∈ X, ∀ y ∈ X, ⁅x, y⁆ ∈ N) :
    Nat.card X ≤ max (Nat.card A) (Nat.card B) := by
  have hAH : A ≤ H := hAS.trans hSH
  have hBH : B ≤ H := hBS.trans hSH
  have hXH : X ≤ H := hXS.trans hSH
  have hNS : N ≤ S₀ := hNA.trans hAS
  have hAcomm : IsMulCommutative (barImage H N A) :=
    isMulCommutative_barImage fun x hx y hy => (hAel x hx y hy).2
  have hprod : Common.TwoElementaryProduct (barImage H N S₀) (barImage H N A) (barImage H N B) :=
    { le_left := barImage_mono hAS
      le_right := barImage_mono hBS
      exists_mul := by
        intro s hs
        obtain ⟨y, hy, rfl⟩ := mem_barImage.1 hs
        obtain ⟨a, ha, b, hb, hab⟩ := hex y hy
        refine ⟨QuotientGroup.mk' (N.subgroupOf H) ⟨a, hAH ha⟩,
          (mem_barImage_iff hNA _).2 ha, QuotientGroup.mk' (N.subgroupOf H) ⟨b, hBH hb⟩,
          (mem_barImage_iff hNB _).2 hb, ?_⟩
        rw [← map_mul]
        exact congrArg _ (Subtype.ext hab)
      isElementaryAbelian_left := isElementaryAbelian_barImage hAel
      isElementaryAbelian_right := isElementaryAbelian_barImage hBel
      exists_mul_ne := by
        obtain ⟨x, hx, y, hy, hxy⟩ := hnonab
        refine ⟨QuotientGroup.mk' (N.subgroupOf H) ⟨x, hSH hx⟩,
          (mem_barImage_iff hNS _).2 hx, QuotientGroup.mk' (N.subgroupOf H) ⟨y, hSH hy⟩,
          (mem_barImage_iff hNS _).2 hy, fun h => hxy ?_⟩
        exact (commute_mk_iff (⟨x, hSH hx⟩ : H) ⟨y, hSH hy⟩).1 h
      inf_centralizer_left := by
        intro abar habar habarB
        obtain ⟨a, haA, rfl⟩ := mem_barImage.1 habar
        have haB : (a : G) ∉ B := fun h => habarB ((mem_barImage_iff hNB a).2 h)
        apply le_antisymm
        · rintro s ⟨hs, hsc⟩
          obtain ⟨y, hy, rfl⟩ := mem_barImage.1 hs
          have hc : Commute (QuotientGroup.mk' (N.subgroupOf H) y)
              (QuotientGroup.mk' (N.subgroupOf H) a) := mem_centralizer_singleton_iff.1 hsc
          exact (mem_barImage_iff hNA y).2 (hcent a haA haB y hy ((commute_mk_iff y a).1 hc))
        · intro s hs
          refine ⟨barImage_mono hAS hs, mem_centralizer_singleton_iff.2 ?_⟩
          exact congrArg Subtype.val (mul_comm' (⟨s, hs⟩ : barImage H N A) ⟨_, habar⟩) }
  have hXcomm : IsMulCommutative (barImage H N X) := isMulCommutative_barImage hX
  have h := hprod.card_le_of_isMulCommutative (barImage_mono hXS)
  rw [card_eq_card_barImage_mul hNX hXH, card_eq_card_barImage_mul hNA hAH,
    card_eq_card_barImage_mul hNB hBH]
  rcases le_max_iff.1 h with h | h
  · exact le_max_of_le_left (Nat.mul_le_mul_right _ h)
  · exact le_max_of_le_right (Nat.mul_le_mul_right _ h)

private theorem thompsonSubgroup_quotient_eq [Finite G] {R S N M₀ D₀ : Subgroup G}
    [(N.subgroupOf R).Normal] (hNS : N ≤ S) (hSR : S ≤ R)
    (hNM : N ≤ M₀) (hMS : M₀ ≤ S) (hND : N ≤ D₀) (hDS : D₀ ≤ S) (hSMD : S = M₀ ⊔ D₀)
    (hM₀ : ∀ x ∈ M₀, ∀ y ∈ M₀, ⁅x, y⁆ ∈ N) (hD₀ : ∀ x ∈ D₀, ∀ y ∈ D₀, ⁅x, y⁆ ∈ N)
    (m : ℕ) (hMc : Nat.card M₀ = m) (hDc : Nat.card D₀ = m)
    (hbound : ∀ B : Subgroup G, N ≤ B → B ≤ R → (∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ N) →
      Nat.card B ≤ m)
    (hsmall : ∀ B : Subgroup G, N ≤ B → B ≤ R → (∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ N) →
      Nat.card B = m → B ≤ S) :
    CFSG.Open.thompsonSubgroup (⊤ : Subgroup (R ⧸ N.subgroupOf R)) =
      (S.subgroupOf R).map (QuotientGroup.mk' (N.subgroupOf R)) := by
  have hMR : M₀ ≤ R := hMS.trans hSR
  have hDR : D₀ ≤ R := hDS.trans hSR
  have hNR : N ≤ R := hNS.trans hSR
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have key : ∀ Ebar : Subgroup (R ⧸ N.subgroupOf R), IsMulCommutative Ebar →
      ∃ E : Subgroup G, N ≤ E ∧ E ≤ R ∧ barImage R N E = Ebar ∧
        (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ N) ∧ Nat.card E = Nat.card Ebar * Nat.card N := by
    intro Ebar hEbar
    obtain ⟨E, hNE, hER, rfl⟩ := exists_barImage_eq hNR Ebar
    exact ⟨E, hNE, hER, rfl,
      forall_commutator_mem_of_isMulCommutative_barImage hNE hER,
      card_eq_card_barImage_mul hNE hER⟩
  have hmax : ∀ {E : Subgroup G}, N ≤ E → E ≤ R → (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ N) →
      Nat.card E = m → CFSG.IsMaxCardAbelian (barImage R N E) := by
    intro E hNE hER hE hcard
    refine ⟨isMulCommutative_barImage hE, fun Bbar hBbar => ?_⟩
    obtain ⟨B, hNB, hBR, rfl, hB, hBcard⟩ := key Bbar hBbar
    have h2 : Nat.card (barImage R N B) * Nat.card N ≤ Nat.card (barImage R N E) * Nat.card N := by
      rw [← hBcard, ← card_eq_card_barImage_mul hNE hER, hcard]
      exact hbound B hNB hBR hB
    exact Nat.le_of_mul_le_mul_right h2 hNpos
  have hMmax := hmax hNM hMR hM₀ hMc
  have hDmax := hmax hND hDR hD₀ hDc
  have e : CFSG.Open.thompsonSubgroup (⊤ : Subgroup (R ⧸ N.subgroupOf R)) =
      CFSG.maxCardThompson (R ⧸ N.subgroupOf R) := CFSG.ambientMaxCardThompson_top
  rw [e]
  change _ = barImage R N S
  apply le_antisymm
  · apply sSup_le
    intro Abar hAbar
    obtain ⟨E, hNE, hER, rfl, hE, hEcard⟩ := key Abar hAbar.1
    have h1 : Nat.card (barImage R N M₀) ≤ Nat.card (barImage R N E) := hAbar.2 _ hMmax.1
    have h2 : m ≤ Nat.card E := by
      rw [hEcard, ← hMc, card_eq_card_barImage_mul hNM hMR]
      exact Nat.mul_le_mul_right _ h1
    exact barImage_mono (hsmall E hNE hER hE (le_antisymm (hbound E hNE hER hE) h2))
  · rw [hSMD, barImage_sup hMR hDR]
    exact sup_le (CFSG.le_maxCardThompson hMmax) (CFSG.le_maxCardThompson hDmax)

private theorem autImage_eq_of_thompsonSubgroup_quotient [Finite G] {H N S : Subgroup G}
    [(N.subgroupOf H).Normal] (hNS : N ≤ S) (hSH : S ≤ H)
    (hJ : CFSG.Open.thompsonSubgroup (⊤ : Subgroup (H ⧸ N.subgroupOf H)) =
      (S.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H)))
    (φ : H ≃* H) (hφ : autImage φ N = N) : autImage φ S = S := by
  have hNφ : ∀ y : H, ((φ y : H) : G) ∈ N ↔ (y : G) ∈ N := by
    intro y
    constructor
    · intro hy
      rw [← hφ] at hy
      obtain ⟨y', hy', hyy'⟩ := mem_autImage.1 hy
      have h1 : y' = y := φ.injective (Subtype.ext hyy')
      subst h1
      exact hy'
    · intro hy
      have h1 : ((φ y : H) : G) ∈ autImage φ N := mem_autImage.2 ⟨y, hy, rfl⟩
      rwa [hφ] at h1
  have hmap : (N.subgroupOf H).map (φ : H →* H) = N.subgroupOf H := by
    ext x
    rw [mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_subgroupOf] at hy ⊢
      exact (hNφ y).2 hy
    · intro hx
      refine ⟨φ.symm x, ?_, by simp⟩
      rw [mem_subgroupOf] at hx ⊢
      apply (hNφ _).1
      simpa using hx
  let φ' := QuotientGroup.congr (N.subgroupOf H) (N.subgroupOf H) φ hmap
  have hJ' : (CFSG.maxCardThompson (H ⧸ N.subgroupOf H)).map φ'.toMonoidHom =
      CFSG.maxCardThompson (H ⧸ N.subgroupOf H) := CFSG.maxCardThompson_map_mulEquiv φ'
  have hJ2 : CFSG.maxCardThompson (H ⧸ N.subgroupOf H) = barImage H N S := by
    rw [← CFSG.ambientMaxCardThompson_top]
    exact hJ
  have hchar : ∀ q : H ⧸ N.subgroupOf H, φ' q ∈ CFSG.maxCardThompson (H ⧸ N.subgroupOf H) ↔
      q ∈ CFSG.maxCardThompson (H ⧸ N.subgroupOf H) := by
    intro q
    conv_lhs => rw [← hJ']
    rw [Subgroup.mem_map_equiv]
    simp
  have hiff : ∀ x : H, (x : G) ∈ S ↔ ((φ x : H) : G) ∈ S := by
    intro x
    have h1 : φ' (QuotientGroup.mk' (N.subgroupOf H) x) =
        QuotientGroup.mk' (N.subgroupOf H) (φ x) := rfl
    rw [← mem_barImage_iff hNS x, ← mem_barImage_iff hNS (φ x), ← hJ2, ← h1]
    exact (hchar _).symm
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_autImage.1 hy
    exact (hiff x).1 hx
  · intro hy
    refine mem_autImage.2 ⟨φ.symm ⟨y, hSH hy⟩, ?_, by simp⟩
    rw [hiff]
    simpa using hy


private theorem commutator_mem_sup_of_le_normalizer {A B N : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hN : A ⊔ B ≤ normalizer (N : Set G)) (hA : ∀ a ∈ A, ∀ a' ∈ A, ⁅a, a'⁆ ∈ N)
    (hB : ∀ b ∈ B, ∀ b' ∈ B, ⁅b, b'⁆ ∈ N) (hc : ∀ a ∈ A, ∀ b ∈ B, ⁅a, b⁆ ∈ N) :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, ⁅x, y⁆ ∈ N := by
  intro x hx y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Common.exists_mul_of_le_normalizer' hAB x hx
  obtain ⟨a', ha', b', hb', rfl⟩ := Common.exists_mul_of_le_normalizer' hAB y hy
  have haN : a ∈ normalizer (N : Set G) := hN (mem_sup_left ha)
  have ha'N : a' ∈ normalizer (N : Set G) := hN (mem_sup_left ha')
  have h1 : ⁅b, a' * b'⁆ ∈ N := by
    have e : ⁅b, a' * b'⁆ = ⁅b, a'⁆ * (a' * ⁅b, b'⁆ * a'⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    refine mul_mem ?_ ((mem_normalizer_iff.1 ha'N _).1 (hB b hb b' hb'))
    have := inv_mem (hc a' ha' b hb)
    rwa [commutatorElement_inv] at this
  have h2 : ⁅a, a' * b'⁆ ∈ N := by
    have e : ⁅a, a' * b'⁆ = ⁅a, a'⁆ * (a' * ⁅a, b'⁆ * a'⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mul_mem (hA a ha a' ha') ((mem_normalizer_iff.1 ha'N _).1 (hc a ha b' hb'))
  have e : ⁅a * b, a' * b'⁆ = a * ⁅b, a' * b'⁆ * a⁻¹ * ⁅a, a' * b'⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 haN _).1 h1 |> fun h => by
    simpa [mul_assoc] using h) h2

private theorem elemModulo_mono {N N' E : Subgroup G} (hN : N ≤ N') (hE : ElemModulo N E) :
    ElemModulo N' E := fun x hx y hy => ⟨hN (hE x hx y hy).1, hN (hE x hx y hy).2⟩

private theorem maximal_map_conj_of_map_eq {N N' Q : Subgroup G} {g : G}
    (hgN : N.map (MulAut.conj g).toMonoidHom = N') (hgQ : g ∈ normalizer (Q : Set G))
    {E : Subgroup G}
    (hE : Maximal (fun E' : Subgroup G => N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') E) :
    Maximal (fun E' : Subgroup G => N' ≤ E' ∧ E' ≤ Q ∧ ElemModulo N' E')
      (E.map (MulAut.conj g).toMonoidHom) := by
  have key : ∀ {g : G} {N N' : Subgroup G}, N.map (MulAut.conj g).toMonoidHom = N' →
      g ∈ normalizer (Q : Set G) → ∀ {E' : Subgroup G}, (N ≤ E' ∧ E' ≤ Q ∧ ElemModulo N E') →
        (N' ≤ E'.map (MulAut.conj g).toMonoidHom ∧ E'.map (MulAut.conj g).toMonoidHom ≤ Q ∧
          ElemModulo N' (E'.map (MulAut.conj g).toMonoidHom)) := by
    intro g N N' hN hgQ E' ⟨h1, h2, h3⟩
    refine ⟨hN ▸ Subgroup.map_mono h1, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hgQ x).1 (h2 hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      obtain ⟨h4, h5⟩ := h3 x hx y hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨?_, ?_⟩
      · rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, ← hN]
        exact ⟨x * x, h4, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      · rw [commutatorElement_def] at h5 ⊢
        rw [show g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
          g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ by group, ← hN]
        exact ⟨_, h5, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  have hinv : N'.map (MulAut.conj g⁻¹).toMonoidHom = N := by
    rw [← hgN]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
    · intro hx
      refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  refine ⟨key hgN hgQ hE.1, fun y hy hEy => ?_⟩
  have hy' := key hinv (inv_mem hgQ) hy
  have hEy' : E ≤ y.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro x hx
    refine ⟨g * x * g⁻¹, hEy ⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hle := hE.2 hy' hEy'
  intro z hz
  refine ⟨g⁻¹ * z * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have : g⁻¹ * z * g ∈ y.map (MulAut.conj g⁻¹).toMonoidHom :=
    ⟨z, hz, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  exact hle this

end Generic


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Local

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

private theorem yamadaR₅_le_normalizers (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaF₂ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaY₂ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaW₂ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaX₂ d t : Set G) := by
  have hR₅R₂N : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  obtain ⟨hRE, hEF, hFY⟩ := h.normalizer_yamadaR₂_le d hK hD
  obtain ⟨-, hle⟩ := h.yamada_5_21_4 hW d hK hD
  exact ⟨hR₅R₂N, hR₅R₂N.trans (hRE.trans hEF), hR₅R₂N.trans (hRE.trans (hEF.trans hFY)),
    fun x hx => (Subgroup.mem_inf.1 (hle (hR₅R₂N hx))).1,
    fun x hx => (Subgroup.mem_inf.1 (hle (hR₅R₂N hx))).2⟩

private theorem yamadaR₅_le_normalizer_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t ≤ normalizer (yamadaW₃ d t : Set G) := by
  obtain ⟨hW₃L₃, hchar⟩ := h.yamada_5_35_5 hW d hK hQ
  have hR₅L₃ := (h.yamada_5_37_1 hW d hK hQ).2.1
  have := hchar
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaW₃ d t).subgroupOf (yamadaL₃ d t))
  rw [subgroupOf_map_subtype, inf_of_le_left hW₃L₃] at h1
  exact hR₅L₃.trans h1

private theorem yamadaR₅_le_normalizer_yamadaX₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaR₅ d t ≤ normalizer (yamadaX₄ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨⟨-, -, -, hR₅R₄⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  obtain ⟨-, -, -, -, hX₂N⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  intro x hx
  rw [h.yamadaX₄_eq_inf_centralizer hW d hK hQ]
  exact Common.mem_normalizer_inf (hR₅R₄ hx) (mem_normalizer_centralizer (hX₂N hx))

private theorem yamadaW₃_le_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaW₃ d t ≤ yamadaR₅ d t :=
  (h.yamadaW₃_le_yamadaR₃ hW d hK hD).trans
    (le_sup_left.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge)

private theorem yamadaX₄_le_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaX₄ d t ≤ yamadaR₅ d t :=
  (h.yamadaX₄_le_yamadaR₄ hW d hK hD).1.trans
    (le_sup_right.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge)

private theorem yamadaV₂_inf_yamadaW₃_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaV₂ d t ⊓ yamadaW₃ d t ≤ yamadaW₂ d t := fun x hx => by
  obtain ⟨-, -, -, hW₂W₃, htW₃, -, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hxV, hxW⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨htW, -⟩ := h.t_mem_normalizer_yamadaW₂ d hK hD
  rcases (mem_sup_zpowers_iff_of h.t_mul_t htW).1 hxV with h1 | ⟨a, ha, rfl⟩
  · exact h1
  · exfalso
    refine htW₃ ?_
    have := mul_mem (inv_mem (hW₂W₃ ha)) hxW
    rwa [inv_mul_cancel_left] at this

private theorem yamadaW₃_inf_yamadaR₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaW₃ d t ⊓ yamadaR₂ d t ≤ yamadaW₂ d t := fun x hx => by
  obtain ⟨hW₃V₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hV₃R₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨hxW, hxR⟩ := Subgroup.mem_inf.1 hx
  refine h.yamadaV₂_inf_yamadaW₃_le hW d hK hD (Subgroup.mem_inf.2 ⟨?_, hxW⟩)
  rw [← hV₃R₂]
  exact Subgroup.mem_inf.2 ⟨hW₃V₃ hxW, hxR⟩

theorem yamada_5_46_1 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaW₃ d t ∧ yamadaY₂ d t ≤ yamadaX₄ d t ∧
      yamadaW₃ d t ⊔ yamadaX₄ d t = yamadaF₅ d t ∧ yamadaW₃ d t ⊓ yamadaX₄ d t = yamadaY₂ d t ∧
      ElemModulo (yamadaY₂ d t) (yamadaF₅ d t) ∧
      Nat.card (yamadaF₅ d t) = Nat.card K ^ 4 * Nat.card (yamadaY₂ d t) := by
  have hD := hQ.doubling
  obtain ⟨hW₃V₃, hV₃N, hJW₃, hW₂W₃, htW₃, hV₃eq, hW₃c⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hX₄U₄, hU₄N, hJX₄, hX₂X₄, htX₄, hU₄eq, hX₄c⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨hWel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hXel, hXc, -⟩ := h.yamada_5_45_3 hW d hK hQ
  obtain ⟨⟨-, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hY₂W₂ : yamadaY₂ d t ≤ yamadaW₂ d t := le_sup_right
  have hY₂X₂ : yamadaY₂ d t ≤ yamadaX₂ d t := le_sup_right
  have hTwo := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  obtain ⟨-, -, -, hR₅W₂, hR₅X₂⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hWX : yamadaW₂ d t ⊓ yamadaX₂ d t = yamadaY₂ d t := by
    rw [← hTwo.inf_centralizer_self]
    exact h.yamadaF₂_center d hK hD
  have hinf : yamadaW₃ d t ⊓ yamadaX₄ d t = yamadaY₂ d t := by
    refine le_antisymm (fun x hx => ?_) (le_inf (hY₂W₂.trans hW₂W₃) (hY₂X₂.trans hX₂X₄))
    obtain ⟨hxW, hxX⟩ := Subgroup.mem_inf.1 hx
    have hxR₂ : x ∈ yamadaR₂ d t := by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨h.yamadaW₃_le_yamadaR₃ hW d hK hD hxW, hX₄R₄ hxX⟩
    have hxW₂ := h.yamadaW₃_inf_yamadaR₂_le hW d hK hD (Subgroup.mem_inf.2 ⟨hxW, hxR₂⟩)
    have hxX₂ : x ∈ yamadaX₂ d t := by
      rw [← hX₄R₂]
      exact Subgroup.mem_inf.2 ⟨hxX, hxR₂⟩
    rw [← hWX]
    exact Subgroup.mem_inf.2 ⟨hxW₂, hxX₂⟩
  have hF₂ : yamadaF₂ d t ≤ yamadaW₃ d t ⊔ yamadaX₄ d t := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hTwo.exists_mul x hx
    exact mul_mem (mem_sup_left (hW₂W₃ ha)) (mem_sup_right (hX₂X₄ hb))
  have hF₅eq : yamadaW₃ d t ⊔ yamadaX₄ d t = yamadaF₅ d t := by
    refine le_antisymm (sup_le ((le_sup_left : yamadaW₃ d t ≤ yamadaF₃ d t).trans
      (le_sup_left : yamadaF₃ d t ≤ yamadaF₅ d t)) ((le_sup_left : yamadaX₄ d t ≤ yamadaF₄ d t).trans
      (le_sup_right : yamadaF₄ d t ≤ yamadaF₅ d t))) ?_
    exact sup_le (sup_le le_sup_left hF₂) (sup_le le_sup_right hF₂)
  refine ⟨hY₂W₂.trans hW₂W₃, hY₂X₂.trans hX₂X₄, hF₅eq, hinf, ?_, ?_⟩
  · rw [← hF₅eq]
    refine elemModulo_sup_of_le_normalizer (fun a ha => hR₅X₄ (hW₃R₅ ha))
      (sup_le (fun x hx => hR₅Y₂ (hW₃R₅ hx)) (fun x hx => hR₅Y₂ (hX₄R₅ hx)))
      (elemModulo_of_elementaryAbelian hWel) (elemModulo_of_elementaryAbelian hXel) ?_
    intro a ha b hb
    rw [← hinf]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have := mul_mem ha ((mem_normalizer_iff.1 (hR₅W₃ (hX₄R₅ hb)) a⁻¹).1 (inv_mem ha))
      rwa [show a * (b * a⁻¹ * b⁻¹) = ⁅a, b⁆ by simp only [commutatorElement_def]; group] at this
    · have := mul_mem ((mem_normalizer_iff.1 (hR₅X₄ (hW₃R₅ ha)) b).1 hb) (inv_mem hb)
      rwa [show a * b * a⁻¹ * b⁻¹ = ⁅a, b⁆ by simp only [commutatorElement_def]] at this
  · have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaW₃ d t) (B := yamadaX₄ d t)
      (fun x hx => hR₅W₃ (hX₄R₅ hx))
    rw [hF₅eq, hinf, hW₃c, hXc, h.card_yamadaY₂ d hK hD] at h1
    rw [h.card_yamadaY₂ d hK hD]
    have hpos : 0 < Nat.card K ^ 4 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1]
    ring


private theorem inv_mul_conj_mem_yamadaY₂_of_mem_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {w j : G} (hw : w ∈ yamadaW₃ d t) (hj : j ∈ d.J₂) :
    w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hW₃V₃, hV₃N, hJW₃, hW₂W₃, htW₃, hV₃eq, hW₃c⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hV₂V₃, hV₃E₃, hV₃L₂, -, -, -, -, hV₃W₂, -⟩ := h.yamadaV₃_facts hW d hK hD
  obtain ⟨hJ₂J, -⟩ := h.J₂_facts d hK
  obtain ⟨hR₃R, -⟩ := h.yamadaR₃_facts hW d hK hD
  obtain ⟨-, hJV₂⟩ := h.J_le_normalizer_yamadaV₃ hW d hK hD
  obtain ⟨-, -, -, -, hWF, hFD, -, hDS, -⟩ := d.inclusions
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := (hW₃V₃.trans hV₃E₃).trans inf_le_left
  have hW₃p : IsPGroup 2 (yamadaW₃ d t) := (h.isPGroup_yamadaRstar d).to_le
    ((hW₃L₃.trans (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t)).trans hR₃R)
  have hJ₂W₃ : d.J₂ ≤ normalizer (yamadaW₃ d t : Set G) := fun j hj => hJW₃ (hJ₂J hj)
  have hJ₂Y₂ : d.J₂ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaY₂ d hK hD (hJ₂J hj)
  have hJ₂W₂ : d.J₂ ≤ normalizer (yamadaW₂ d t : Set G) := fun j hj =>
    (h.normalizer_yamadaV₂_le hW d hK hD).1 (hJV₂ (hJ₂J hj))
  have hWY₂ : d.W ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hWF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have hA1 : ∀ w ∈ yamadaW₂ d t, ∀ j ∈ d.J₂, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hWY₂ w hw
      obtain ⟨-, haY⟩ := h.J₂_conj_W d hK hD hj ha
      rw [show (a * y)⁻¹ * (j * (a * y) * j⁻¹) = y⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * (j * y * j⁻¹) by
        group]
      exact mul_mem (mul_mem (inv_mem hy) (h.Y_le_yamadaY₂ d hK hD haY))
        ((mem_normalizer_iff.1 (hJ₂Y₂ hj) y).1 hy)
  have hA2 : ∀ w ∈ yamadaW₃ d t, ∀ j ∈ d.J₂, w⁻¹ * (j * w * j⁻¹) ∈ yamadaW₂ d t :=
    fun w hw j hj => by
      have h1 := h.inv_mul_conj_mem_yamadaL₂ hW d hK hD (hW₃L₃ hw) hj
      have h2 : w⁻¹ * (j * w * j⁻¹) ∈ yamadaW₃ d t :=
        mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJ₂W₃ hj) w).1 hw)
      exact h.yamadaV₂_inf_yamadaW₃_le hW d hK hD (Subgroup.mem_inf.2
        ⟨hV₃L₂.le (Subgroup.mem_inf.2 ⟨hW₃V₃ h2, h1⟩), h2⟩)
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₂_mul d hK hW₂W₃ (hW₃V₃.trans hV₃W₂)
    hJ₂W₃ hJ₂W₂ hW₃p hw fun j hj => hA2 w hw j hj
  have hcj : j * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j hj
  rw [show (c * n)⁻¹ * (j * (c * n) * j⁻¹) = n⁻¹ * (c⁻¹ * (j * c) * n * j⁻¹) by group, hcj,
    show n⁻¹ * (c⁻¹ * (c * j) * n * j⁻¹) = n⁻¹ * (j * n * j⁻¹) by group]
  exact hA1 n hn j hj

private theorem inv_mul_conj_mem_yamadaY₂_of_mem_yamadaX₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d)
    {w j : G} (hw : w ∈ yamadaX₄ d t) (hj : j ∈ d.J₆) :
    w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hX₄U₄, hU₄N, hJX₄, hX₂X₄, -, hU₄eq, hX₄c⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨-, -, -, -, -, -, hU₄X₂, hU₄Y₂⟩ := h.yamadaU₄_facts hW d hK hD
  obtain ⟨hJ₆J, -⟩ := h.J₆_facts d hK
  obtain ⟨hR₄R, -⟩ := h.yamadaR₄_facts hW d hK hD
  obtain ⟨-, -, -, hXF, -, hFD, -, hDS, -⟩ := d.inclusions
  have hX₄p : IsPGroup 2 (yamadaX₄ d t) := (h.isPGroup_yamadaRstar d).to_le (hX₄R₄.trans hR₄R)
  have hJ₆X₄ : d.J₆ ≤ normalizer (yamadaX₄ d t : Set G) := fun j hj => hJX₄ (hJ₆J hj)
  have hJ₆Y₂ : d.J₆ ≤ normalizer (yamadaY₂ d t : Set G) := fun j hj =>
    h.J_le_normalizer_yamadaY₂ d hK hD (hJ₆J hj)
  have hJ₆X₂ : d.J₆ ≤ normalizer (yamadaX₂ d t : Set G) := fun j hj =>
    ((h.J_le_normalizer_yamadaU₄ hW d hK hD).2.trans (h.normalizer_yamadaU₂_le hW d hK hD).1)
      (hJ₆J hj)
  have hXY₂ : d.X ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hXF.trans (hFD.trans hDS)).trans (h.yamada_5_13_3 d hK hD).1
  have hA1 : ∀ w ∈ yamadaX₂ d t, ∀ j ∈ d.J₆, w⁻¹ * (j * w * j⁻¹) ∈ yamadaY₂ d t :=
    fun w hw j hj => by
      obtain ⟨a, ha, y, hy, rfl⟩ := Common.exists_mul_of_le_normalizer' hXY₂ w hw
      obtain ⟨-, haY⟩ := h.J₆_conj_X d hK hD hj ha
      rw [show (a * y)⁻¹ * (j * (a * y) * j⁻¹) = y⁻¹ * (a⁻¹ * (j * a * j⁻¹)) * (j * y * j⁻¹) by
        group]
      exact mul_mem (mul_mem (inv_mem hy) (h.Y_le_yamadaY₂ d hK hD haY))
        ((mem_normalizer_iff.1 (hJ₆Y₂ hj) y).1 hy)
  have hA2 : ∀ w ∈ yamadaX₄ d t, ∀ j ∈ d.J₆, w⁻¹ * (j * w * j⁻¹) ∈ yamadaX₂ d t :=
    fun w hw j hj => by
      rw [← hX₄R₂]
      exact Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hw) ((mem_normalizer_iff.1 (hJ₆X₄ hj) w).1 hw),
        h.inv_mul_conj_mem_yamadaR₂_of_J₆ hW d hK hD (hX₄R₄ hw) hj⟩
  obtain ⟨c, hc, n, hn, rfl⟩ := exists_centralizer_J₆_mul d hX₂X₄ (hX₄U₄.trans hU₄X₂)
    hJ₆X₄ hJ₆X₂ hX₄p hw fun j hj => hA2 w hw j hj
  have hcj : j * c = c * j := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2 j hj
  rw [show (c * n)⁻¹ * (j * (c * n) * j⁻¹) = n⁻¹ * (c⁻¹ * (j * c) * n * j⁻¹) by group, hcj,
    show n⁻¹ * (c⁻¹ * (c * j) * n * j⁻¹) = n⁻¹ * (j * n * j⁻¹) by group]
  exact hA1 n hn j hj

private theorem S_le_yamadaR₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) : d.S ≤ yamadaR₅ d t :=
  (le_sup_right : d.S ≤ yamadaR₃ d t).trans
    (le_sup_left.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge)

private theorem commutator_mem_yamadaY₂_of_mem_S_yamadaW₃ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {s w : G} (hs : s ∈ d.S) (hw : w ∈ yamadaW₃ d t) :
    s * w * s⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hWel, -, -, -⟩ := h.yamada_5_33_3_uniform hW d hK hQ.doubling
  obtain ⟨hW₃V₃, hV₃N, hJW₃, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨hJ₂J, hJC, hC, -⟩ := h.J₂_facts d hK
  obtain ⟨-, -, hWdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  refine commutator_mem_of_coprime_fixed (S := d.S) (V := yamadaW₃ d t) (N₀ := yamadaY₂ d t)
    (J' := d.J₂) (fun x hx => hR₅W₃ (hSR₅ hx)) (fun x hx => hR₅Y₂ (hSR₅ hx))
    (fun x hx => hR₅Y₂ (hW₃R₅ hx)) (fun j hj => (Subgroup.mem_inf.1 (hJC hj)).2)
    (fun j hj => hJW₃ (hJ₂J hj)) (fun j hj => h.J_le_normalizer_yamadaY₂ d hK hD (hJ₂J hj))
    ?_ (fun v hv j hj => h.inv_mul_conj_mem_yamadaY₂_of_mem_yamadaW₃ hW d hK hD hv hj) ?_ s hs w hw
  · intro T hTS hST hJT m hm hfix
    exact exists_centralizer_J₂_mul d hK hTS hST (fun j hj => (Subgroup.mem_inf.1 (hJC hj)).2)
      hJT d.isSylowOf_S.isPGroup hm hfix
  · intro c hc v hv
    have hcg : c ∈ d.rootGroup g2v := by
      rw [← hC]
      exact hc
    have hcW₃ : c ∈ yamadaW₃ d t :=
      ((le_sup_left : d.W ≤ yamadaW₂ d t).trans hW₂W₃) (le_sup_left.trans hWdef.le hcg)
    rw [show c * v * c⁻¹ * v⁻¹ = 1 by
      rw [mul_comm_of_elementaryAbelian hWel hcW₃ hv]; group]
    exact one_mem _

private theorem commutator_mem_yamadaY₂_of_mem_S_yamadaX₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {s w : G} (hs : s ∈ d.S) (hw : w ∈ yamadaX₄ d t) :
    s * w * s⁻¹ * w⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hXel, -, -⟩ := h.yamada_5_45_3 hW d hK hQ
  obtain ⟨hX₄U₄, hU₄N, hJX₄, hX₂X₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  obtain ⟨hJ₆J, -, hC, -⟩ := h.J₆_facts d hK
  obtain ⟨-, hXdef, -⟩ := d.yamada_defs
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hJS : d.J₆ ≤ normalizer (d.S : Set G) := fun j hj =>
    (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d (hJ₆J hj))).2
  refine commutator_mem_of_coprime_fixed (S := d.S) (V := yamadaX₄ d t) (N₀ := yamadaY₂ d t)
    (J' := d.J₆) (fun x hx => hR₅X₄ (hSR₅ hx)) (fun x hx => hR₅Y₂ (hSR₅ hx))
    (fun x hx => hR₅Y₂ (hX₄R₅ hx)) hJS
    (fun j hj => hJX₄ (hJ₆J hj)) (fun j hj => h.J_le_normalizer_yamadaY₂ d hK hD (hJ₆J hj))
    ?_ (fun v hv j hj => h.inv_mul_conj_mem_yamadaY₂_of_mem_yamadaX₄ hW d hK hD hv hj) ?_ s hs w hw
  · intro T hTS hST hJT m hm hfix
    exact exists_centralizer_J₆_mul d hTS hST hJS hJT d.isSylowOf_S.isPGroup hm hfix
  · intro c hc v hv
    have hcg : c ∈ d.rootGroup g2u := by
      rw [← hC]
      exact hc
    have hcX₄ : c ∈ yamadaX₄ d t :=
      ((le_sup_left : d.X ≤ yamadaX₂ d t).trans hX₂X₄) (le_sup_left.trans hXdef.le hcg)
    rw [show c * v * c⁻¹ * v⁻¹ = 1 by
      rw [mul_comm_of_elementaryAbelian hXel hcX₄ hv]; group]
    exact one_mem _

private theorem commutator_mem_yamadaY₂_of_mem_yamadaS₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {y x : G} (hy : y ∈ yamadaS₅ d t) (hx : x ∈ yamadaF₅ d t) :
    y * x * y⁻¹ * x⁻¹ ∈ yamadaY₂ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hS₅eq, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, hEl, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hF₅R₅ : yamadaF₅ d t ≤ yamadaR₅ d t := hF₅eq ▸ sup_le hW₃R₅ hX₄R₅
  have hS : d.S ≤ centralizerModulo (yamadaY₂ d t) (yamadaF₅ d t) := fun s hs => by
    refine mem_centralizerModulo_iff.2 ⟨hR₅Y₂ (hSR₅ hs), fun z hz => ?_⟩
    rw [← hF₅eq] at hz
    obtain ⟨w, hw, x₄, hx₄, rfl⟩ := Common.exists_mul_of_le_normalizer
      (fun a ha => hR₅W₃ (hX₄R₅ ha)) z hz
    have h1 := h.commutator_mem_yamadaY₂_of_mem_S_yamadaW₃ hW d hK hQ hs hw
    have h2 := (mem_normalizer_iff.1 (hR₅Y₂ (hW₃R₅ hw)) _).1
      (h.commutator_mem_yamadaY₂_of_mem_S_yamadaX₄ hW d hK hQ hs hx₄)
    have := mul_mem h1 h2
    rwa [show s * w * s⁻¹ * w⁻¹ * (w * (s * x₄ * s⁻¹ * x₄⁻¹) * w⁻¹) =
      s * (w * x₄) * s⁻¹ * (w * x₄)⁻¹ by group] at this
  have hF : yamadaF₅ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaF₅ d t) := fun f' hf' =>
    mem_centralizerModulo_iff.2 ⟨hR₅Y₂ (hF₅R₅ hf'), fun z hz => (hEl f' hf' z hz).2⟩
  have hS₅ : yamadaS₅ d t ≤ centralizerModulo (yamadaY₂ d t) (yamadaF₅ d t) := by
    rw [hS₅eq]
    exact sup_le hS hF
  exact (mem_centralizerModulo_iff.1 (hS₅ hy)).2 x hx

private theorem elemModulo_yamadaY₂_M (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) (hK4 : 4 ≤ Nat.card K) : ElemModulo (yamadaY₂ d t) d.M :=
  fun x hx y hy => by
    refine ⟨?_, ?_⟩
    · have h1 : x * x ∈ closure {z | ∃ g ∈ d.M, z = g ^ 2} := subset_closure ⟨x, hx, (sq x).symm⟩
      rw [(d.yamada_3_12_mho hK4).2.1] at h1
      exact h.Y_le_yamadaY₂ d hK hD h1
    · have h1 : ⁅x, y⁆ ∈ ⁅d.M, d.M⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [(d.yamada_3_12_commutators hK4).2.1] at h1
      exact h.Y_le_yamadaY₂ d hK hD h1

private theorem elemModulo_yamadaY₂_D (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) (hK4 : 4 ≤ Nat.card K) : ElemModulo (yamadaY₂ d t) d.D :=
  fun x hx y hy => by
    have hUY₂ : d.U ≤ yamadaY₂ d t := d.inclusions.1.trans (h.Y_le_yamadaY₂ d hK hD)
    refine ⟨?_, ?_⟩
    · have h1 : x * x ∈ closure {z | ∃ g ∈ d.D, z = g ^ 2} := subset_closure ⟨x, hx, (sq x).symm⟩
      rw [(d.yamada_3_12_mho hK4).1] at h1
      exact hUY₂ h1
    · have h1 : ⁅x, y⁆ ∈ ⁅d.D, d.D⁆ := Subgroup.commutator_mem_commutator hx hy
      rw [(d.yamada_3_12_commutators hK4).1] at h1
      exact hUY₂ h1

private theorem elemModulo_yamadaY₂_yamadaM₅_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ElemModulo (yamadaY₂ d t) (yamadaM₅ d t) ∧ ElemModulo (yamadaY₂ d t) (yamadaD₅ d t) := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, hEl, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hF₅R₅ : yamadaF₅ d t ≤ yamadaR₅ d t := hF₅eq ▸ sup_le hW₃R₅ hX₄R₅
  have hR₅F₅ : yamadaR₅ d t ≤ normalizer (yamadaF₅ d t : Set G) := fun x hx => by
    rw [← hF₅eq]
    exact mem_normalizer_sup (hR₅W₃ hx) (hR₅X₄ hx)
  have hSS₅ : d.S ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_left
  have hMD : ∀ {A : Subgroup G}, A ≤ d.S → ElemModulo (yamadaY₂ d t) A →
      ElemModulo (yamadaY₂ d t) (A ⊔ yamadaF₅ d t) := fun {A} hAS hA =>
    elemModulo_sup_of_le_normalizer (fun a ha => hR₅F₅ (hSR₅ (hAS ha)))
      (sup_le (fun x hx => hR₅Y₂ (hSR₅ (hAS hx))) (fun x hx => hR₅Y₂ (hF₅R₅ hx))) hA hEl
      (fun a ha b hb => h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ
        (hSS₅ (hAS ha)) hb)
  rw [hM₅eq, hD₅eq]
  exact ⟨hMD hMS (h.elemModulo_yamadaY₂_M d hK hD hK4),
    hMD hDS (h.elemModulo_yamadaY₂_D d hK hD hK4)⟩

theorem yamada_5_46_2 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) (E : Subgroup G) :
    Maximal (fun E' : Subgroup G => yamadaY₂ d t ≤ E' ∧ E' ≤ yamadaS₅ d t ∧
        ElemModulo (yamadaY₂ d t) E') E ↔ E = yamadaM₅ d t ∨ E = yamadaD₅ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, ⟨hSF, hMF, hDF⟩⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hY₂W₃, hY₂X₄, hF₅eq, hinf, hEl, hcardF⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hF₅R₅ : yamadaF₅ d t ≤ yamadaR₅ d t := hF₅eq ▸ sup_le hW₃R₅ hX₄R₅
  have hR₅F₅ : yamadaR₅ d t ≤ normalizer (yamadaF₅ d t : Set G) := fun x hx => by
    rw [← hF₅eq]
    exact mem_normalizer_sup (hR₅W₃ hx) (hR₅X₄ hx)
  have hY₂F₅ : yamadaY₂ d t ≤ yamadaF₅ d t := hF₅eq ▸ le_sup_of_le_left hY₂W₃
  have hSS₅ : d.S ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_left
  have hF₅S₅ : yamadaF₅ d t ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_right
  obtain ⟨hMel, hDel⟩ := h.elemModulo_yamadaY₂_yamadaM₅_yamadaD₅ hW d hK hQ
  have hM : yamadaY₂ d t ≤ yamadaM₅ d t ∧ yamadaM₅ d t ≤ yamadaS₅ d t ∧
      ElemModulo (yamadaY₂ d t) (yamadaM₅ d t) := by
    refine ⟨?_, ?_, hMel⟩
    · rw [hM₅eq]
      exact hY₂F₅.trans le_sup_right
    · rw [hM₅eq, hS₅eq]
      exact sup_le_sup_right hMS _
  have hDD : yamadaY₂ d t ≤ yamadaD₅ d t ∧ yamadaD₅ d t ≤ yamadaS₅ d t ∧
      ElemModulo (yamadaY₂ d t) (yamadaD₅ d t) := by
    refine ⟨?_, ?_, hDel⟩
    · rw [hD₅eq]
      exact hY₂F₅.trans le_sup_right
    · rw [hD₅eq, hS₅eq]
      exact sup_le_sup_right hDS _
  have key : ∀ E' : Subgroup G, E' ≤ yamadaS₅ d t → ElemModulo (yamadaY₂ d t) E' →
      E' ≤ yamadaM₅ d t ∨ E' ≤ yamadaD₅ d t := fun E' hE'S hE' =>
    le_or_le_of_subset_union fun x hx => by
      have hxS : x ∈ d.S ⊔ yamadaF₅ d t := hS₅eq ▸ hE'S hx
      obtain ⟨s, hs, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
        (fun a ha => hR₅F₅ (hSR₅ ha)) x hxS
      have hxx := (hE' _ hx _ hx).1
      have h1 := h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ (hSS₅ (inv_mem hs)) hf'
      have h2 : (s⁻¹ * f' * s) * f' ∈ yamadaY₂ d t := by
        have := mul_mem h1 (hEl f' hf' f' hf').1
        rwa [show s⁻¹ * f' * s⁻¹⁻¹ * f'⁻¹ * (f' * f') = (s⁻¹ * f' * s) * f' by group] at this
      have h3 : s * s ∈ yamadaY₂ d t := by
        have := mul_mem hxx (inv_mem h2)
        rwa [show s * f' * (s * f') * ((s⁻¹ * f' * s) * f')⁻¹ = s * s by group] at this
      have h4 : s * s ∈ d.Y := by
        rw [← h.yamadaY₂_inf_centralizer d hK hD]
        exact Subgroup.mem_inf.2 ⟨h3, h.S_le_centralizer d (mul_mem hs hs)⟩
      rcases d.mem_D_or_M_of_mul_self_mem hs h4 with hsD | hsM
      · right
        rw [hD₅eq]
        exact mul_mem (mem_sup_left hsD) (mem_sup_right hf')
      · left
        rw [hM₅eq]
        exact mul_mem (mem_sup_left hsM) (mem_sup_right hf')
  have hne1 : ¬ yamadaM₅ d t ≤ yamadaD₅ d t := fun hle => d.not_M_le_D fun m hm => by
    have hm' : m ∈ d.D ⊔ yamadaF₅ d t := hD₅eq ▸ hle (hM₅eq ▸ mem_sup_left hm)
    obtain ⟨δ, hδ, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
      (fun a ha => hR₅F₅ (hSR₅ (hDS ha))) m hm'
    have hf'S : f' ∈ d.S ⊓ yamadaF₅ d t := by
      refine Subgroup.mem_inf.2 ⟨?_, hf'⟩
      have := mul_mem (inv_mem (hDS hδ)) (hMS hm)
      rwa [inv_mul_cancel_left] at this
    rw [hSF] at hf'S
    exact mul_mem hδ (hFD hf'S)
  have hne2 : ¬ yamadaD₅ d t ≤ yamadaM₅ d t := fun hle => d.not_D_le_M fun m hm => by
    have hm' : m ∈ d.M ⊔ yamadaF₅ d t := hM₅eq ▸ hle (hD₅eq ▸ mem_sup_left hm)
    obtain ⟨μ, hμ, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
      (fun a ha => hR₅F₅ (hSR₅ (hMS ha))) m hm'
    have hf'S : f' ∈ d.S ⊓ yamadaF₅ d t := by
      refine Subgroup.mem_inf.2 ⟨?_, hf'⟩
      have := mul_mem (inv_mem (hMS hμ)) (hDS hm)
      rwa [inv_mul_cancel_left] at this
    rw [hSF] at hf'S
    exact mul_mem hμ (hFM hf'S)
  constructor
  · rintro ⟨⟨-, hES, hE⟩, hmax⟩
    rcases key E hES hE with h' | h'
    · exact Or.inl (le_antisymm h' (hmax hM h'))
    · exact Or.inr (le_antisymm h' (hmax hDD h'))
  · rintro (rfl | rfl)
    · refine ⟨hM, fun E' hE' hME' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h' | h'
      · exact h'
      · exact absurd (hME'.trans h') hne1
    · refine ⟨hDD, fun E' hE' hDE' => ?_⟩
      rcases key E' hE'.2.1 hE'.2.2 with h' | h'
      · exact absurd (hDE'.trans h') hne2
      · exact h'

private theorem card_yamadaF₂ (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f)
    (hD : h.DoublingFacts d) : Nat.card (yamadaF₂ d t) = Nat.card K ^ 6 := by
  obtain ⟨-, -, -, -, -, hFD, -, hDS, -, -⟩ := d.inclusions
  have hFN : d.F ≤ normalizer (yamadaY₂ d t : Set G) :=
    (hFD.trans hDS).trans (h.yamada_5_13_3 d hK hD).1
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaY₂ d t) (B := d.F) hFN
  have hinf : yamadaY₂ d t ⊓ d.F = d.Y := by
    refine le_antisymm (fun x hx => ?_) (le_inf (h.Y_le_yamadaY₂ d hK hD)
      (d.inclusions.2.1.trans d.inclusions.2.2.2.1))
    obtain ⟨hxY, hxF⟩ := Subgroup.mem_inf.1 hx
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hxY, h.S_le_centralizer d (hFD.trans hDS hxF)⟩
  have hF₂ : yamadaF₂ d t = yamadaY₂ d t ⊔ d.F := sup_comm _ _
  rw [hinf, ← hF₂, h.card_yamadaY₂ d hK hD, d.cards.2.1, d.cards.2.2.2.2.1] at h1
  have hpos : 0 < Nat.card K ^ 2 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h1]
  ring

private theorem card_yamadaM₅_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    Nat.card (yamadaM₅ d t) = Nat.card K ^ 9 ∧ Nat.card (yamadaD₅ d t) = Nat.card K ^ 9 := by
  have hD := hQ.doubling
  obtain ⟨⟨-, hM₅eq, hD₅eq⟩, ⟨-, hMF, hDF⟩⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, -, hcardF⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hR₅F₅ : yamadaR₅ d t ≤ normalizer (yamadaF₅ d t : Set G) := fun x hx => by
    rw [← hF₅eq]
    exact mem_normalizer_sup (hR₅W₃ hx) (hR₅X₄ hx)
  have hF₅c : Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 := by
    rw [hcardF, h.card_yamadaY₂ d hK hD]
    ring
  have hFc := d.cards.2.2.2.2.1
  have hpos : 0 < Nat.card K ^ 4 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have hMc := d.cards.2.2.2.2.2.2.1
  have hDc := d.cards.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaF₅ d t) (B := d.M)
      (fun x hx => hR₅F₅ (hSR₅ (hMS hx)))
    rw [sup_comm, ← hM₅eq, inf_comm, hMF, hF₅c, hMc, hFc] at h1
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1]
    ring
  · have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaF₅ d t) (B := d.D)
      (fun x hx => hR₅F₅ (hSR₅ (hDS hx)))
    rw [sup_comm, ← hD₅eq, inf_comm, hDF, hF₅c, hDc, hFc] at h1
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1]
    ring

private theorem mem_yamadaM₅_of_commutator_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {m s : G}
    (hm : m ∈ yamadaM₅ d t) (hmF : m ∉ yamadaF₅ d t) (hs : s ∈ yamadaS₅ d t)
    (hc : s * m * s⁻¹ * m⁻¹ ∈ yamadaY₂ d t) : s ∈ yamadaM₅ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨hS₅eq, hM₅eq, -⟩, ⟨-, hMF, -⟩⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, -, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, hYW, hMS⟩ : d.U ≤ d.Y ∧ d.Y ≤ d.W ∧ d.M ≤ d.S := by
    obtain ⟨hUY, -, hYW, -, -, -, -, -, hMS, -⟩ := d.inclusions
    exact ⟨hUY, hYW, hMS⟩
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hR₅F₅ : yamadaR₅ d t ≤ normalizer (yamadaF₅ d t : Set G) := fun x hx => by
    rw [← hF₅eq]
    exact mem_normalizer_sup (hR₅W₃ hx) (hR₅X₄ hx)
  have hSS₅ : d.S ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_left
  have hF₅S₅ : yamadaF₅ d t ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_right
  have hFF₅ : d.F ≤ yamadaF₅ d t := hMF ▸ inf_le_right
  have hm' : m ∈ d.M ⊔ yamadaF₅ d t := hM₅eq ▸ hm
  have hs' : s ∈ d.S ⊔ yamadaF₅ d t := hS₅eq ▸ hs
  obtain ⟨m₀, hm₀, f₁, hf₁, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun a ha => hR₅F₅ (hSR₅ (hMS ha))) m hm'
  obtain ⟨s₀, hs₀, f₂, hf₂, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun a ha => hR₅F₅ (hSR₅ ha)) s hs'
  have hm₀S : m₀ ∈ d.S := hMS hm₀
  have ha : m₀ * f₁ ∈ yamadaS₅ d t := mul_mem (hSS₅ hm₀S) (hF₅S₅ hf₁)
  have hA : s₀ * (m₀ * f₁) * s₀⁻¹ * (m₀ * f₁)⁻¹ ∈ yamadaY₂ d t := by
    have h1 := h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ ha hf₂
    have h2 : f₂ * (m₀ * f₁) * f₂⁻¹ * (m₀ * f₁)⁻¹ ∈ yamadaY₂ d t := by
      have := inv_mem h1
      rwa [show (m₀ * f₁ * f₂ * (m₀ * f₁)⁻¹ * f₂⁻¹)⁻¹ =
        f₂ * (m₀ * f₁) * f₂⁻¹ * (m₀ * f₁)⁻¹ by group] at this
    have h3 := (mem_normalizer_iff.1 (hR₅Y₂ (hSR₅ hs₀)) _).1 h2
    have := mul_mem (inv_mem h3) hc
    rwa [show (s₀ * (f₂ * (m₀ * f₁) * f₂⁻¹ * (m₀ * f₁)⁻¹) * s₀⁻¹)⁻¹ *
      (s₀ * f₂ * (m₀ * f₁) * (s₀ * f₂)⁻¹ * (m₀ * f₁)⁻¹) =
      s₀ * (m₀ * f₁) * s₀⁻¹ * (m₀ * f₁)⁻¹ by group] at this
  have hB : s₀ * m₀ * s₀⁻¹ * m₀⁻¹ ∈ yamadaY₂ d t := by
    have h1 := h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ (hSS₅ hs₀) hf₁
    have h3 := (mem_normalizer_iff.1 (hR₅Y₂ (hSR₅ hm₀S)) _).1 h1
    have := mul_mem hA (inv_mem h3)
    rwa [show s₀ * (m₀ * f₁) * s₀⁻¹ * (m₀ * f₁)⁻¹ *
      (m₀ * (s₀ * f₁ * s₀⁻¹ * f₁⁻¹) * m₀⁻¹)⁻¹ = s₀ * m₀ * s₀⁻¹ * m₀⁻¹ by group] at this
  have hBY : s₀ * m₀ * s₀⁻¹ * m₀⁻¹ ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hB, h.S_le_centralizer d
      (mul_mem (mul_mem (mul_mem hs₀ hm₀S) (inv_mem hs₀)) (inv_mem hm₀S))⟩
  rcases d.mem_M_or_mem_F_of_commutator_mem_W hK4 hs₀ hm₀ (hYW hBY) with hsM | hmF'
  · rw [hM₅eq]
    exact mul_mem (mem_sup_left hsM) (mem_sup_right hf₂)
  · exact absurd (mul_mem (hFF₅ hmF') hf₁) hmF

private theorem exists_commutator_not_mem_yamadaY₂ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ x ∈ yamadaS₅ d t, ∃ y ∈ yamadaS₅ d t, ⁅x, y⁆ ∉ yamadaY₂ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨⟨hS₅eq, -, -⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  have hSS₅ : d.S ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_left
  obtain ⟨m, hm, hmF⟩ : ∃ m ∈ d.M, m ∉ d.F := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show d.M ≤ d.F from hcon)
    rw [d.cards.2.2.2.2.2.2.1, d.cards.2.2.2.2.1] at this
    exact absurd this (not_le.2 (pow_lt_pow_right₀ hQ.one_lt
      (by norm_num : 4 < 5)))
  obtain ⟨s, hs, hsM⟩ := Set.not_subset.1 d.not_D_le_M
  have hsS : s ∈ d.S := hDS hs
  have hmS : m ∈ d.S := hMS hm
  refine ⟨s, hSS₅ hsS, m, hSS₅ hmS, fun hc => ?_⟩
  have hY : ⁅s, m⁆ ∈ d.Y := by
    rw [← h.yamadaY₂_inf_centralizer d hK hD]
    exact Subgroup.mem_inf.2 ⟨hc, h.S_le_centralizer d
      (Subgroup.commutator_mem_commutator hsS hmS |> fun _ =>
        mul_mem (mul_mem (mul_mem hsS hmS) (inv_mem hsS)) (inv_mem hmS))⟩
  rcases d.mem_M_or_mem_F_of_commutator_mem_W hK4 hsS hm (d.inclusions.2.2.1 hY) with h1 | h1
  · exact hsM h1
  · exact hmF h1

private theorem yamadaS₅_basic (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaY₂ d t ≤ yamadaF₅ d t ∧ yamadaF₅ d t ≤ yamadaM₅ d t ∧ yamadaF₅ d t ≤ yamadaD₅ d t ∧
      yamadaM₅ d t ≤ yamadaS₅ d t ∧ yamadaD₅ d t ≤ yamadaS₅ d t ∧ yamadaS₅ d t ≤ yamadaR₅ d t ∧
      yamadaR₅ d t ≤ normalizer (yamadaF₅ d t : Set G) ∧
      yamadaR₅ d t ≤ normalizer (yamadaS₅ d t : Set G) ∧ yamadaF₅ d t ≤ yamadaR₅ d t ∧
      d.S ≤ yamadaS₅ d t ∧ t ∈ yamadaR₅ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hY₂W₃, -, hF₅eq, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, ⟨hS₅R, htS₅N, htS₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hR₅X₄ := h.yamadaR₅_le_normalizer_yamadaX₄ hW d hK hQ
  have hW₃R₅ := h.yamadaW₃_le_yamadaR₅ hW d hK hD
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  have hSS₅ : d.S ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_left
  have hF₅S₅ : yamadaF₅ d t ≤ yamadaS₅ d t := by
    rw [hS₅eq]
    exact le_sup_right
  have hS₅R₅ : yamadaS₅ d t ≤ yamadaR₅ d t := hS₅R ▸ le_sup_left
  refine ⟨hF₅eq ▸ le_sup_of_le_left hY₂W₃, ?_, ?_, ?_, ?_, hS₅R₅, ?_, ?_, ?_, hSS₅, ?_⟩
  · rw [hM₅eq]
    exact le_sup_right
  · rw [hD₅eq]
    exact le_sup_right
  · rw [hM₅eq, hS₅eq]
    exact sup_le_sup_right hMS _
  · rw [hD₅eq, hS₅eq]
    exact sup_le_sup_right hDS _
  · intro x hx
    rw [← hF₅eq]
    exact mem_normalizer_sup (hR₅W₃ hx) (hR₅X₄ hx)
  · rw [← hS₅R]
    exact sup_le Subgroup.le_normalizer ((zpowers_le).2 htS₅N)
  · rw [← hF₅eq]
    exact sup_le hW₃R₅ hX₄R₅
  · rw [← hS₅R]
    exact mem_sup_right (mem_zpowers t)

private theorem yamadaF₅_inf_yamadaR₂_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₅ d t ⊓ yamadaR₂ d t ≤ yamadaF₂ d t := fun x hx => by
  have hD := hQ.doubling
  obtain ⟨-, -, hF₅eq, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨⟨-, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hTwo := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  have hR₅W₃ := h.yamadaR₅_le_normalizer_yamadaW₃ hW d hK hQ
  have hX₄R₅ := h.yamadaX₄_le_yamadaR₅ hW d hK hD
  obtain ⟨hxF, hxR₂⟩ := Subgroup.mem_inf.1 hx
  rw [← hF₅eq] at hxF
  obtain ⟨w, hw, x₄, hx₄, rfl⟩ := Common.exists_mul_of_le_normalizer
    (fun a ha => hR₅W₃ (hX₄R₅ ha)) x hxF
  have hR₂R₃ : yamadaR₂ d t ≤ yamadaR₃ d t := hR₃R₄.ge.trans inf_le_left
  have hwR₃ := h.yamadaW₃_le_yamadaR₃ hW d hK hD hw
  have hx₄R₂ : x₄ ∈ yamadaR₂ d t := by
    rw [← hR₃R₄]
    refine Subgroup.mem_inf.2 ⟨?_, hX₄R₄ hx₄⟩
    have := mul_mem (inv_mem hwR₃) (hR₂R₃ hxR₂)
    rwa [inv_mul_cancel_left] at this
  have hx₄X₂ : x₄ ∈ yamadaX₂ d t := by
    rw [← hX₄R₂]
    exact Subgroup.mem_inf.2 ⟨hx₄, hx₄R₂⟩
  have hwR₂ : w ∈ yamadaR₂ d t := by
    have := mul_mem hxR₂ (inv_mem hx₄R₂)
    rwa [mul_inv_cancel_right] at this
  have hwW₂ := h.yamadaW₃_inf_yamadaR₂_le hW d hK hD (Subgroup.mem_inf.2 ⟨hw, hwR₂⟩)
  exact mul_mem (hTwo.le_left hwW₂) (hTwo.le_right hx₄X₂)

private theorem mem_yamadaR₂_of_commutator_mem (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {x : G}
    (hx : x ∈ yamadaR₅ d t) (hc : x * t * x⁻¹ * t⁻¹ ∈ yamadaY₂ d t) : x ∈ yamadaR₂ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htR₅⟩ := h.yamadaS₅_basic hW d hK hQ
  obtain ⟨⟨-, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hR₅R₂N : yamadaR₅ d t ≤ normalizer (yamadaR₂ d t : Set G) :=
    LieType.BorelTits.pCoreOf_le 2 _
  have hy : t⁻¹ * (x * t * x⁻¹ * t⁻¹) * t⁻¹⁻¹ ∈ yamadaY₂ d t :=
    (mem_normalizer_iff.1 (hR₅Y₂ (inv_mem htR₅)) _).1 hc
  obtain ⟨-, -, h3, -, h5⟩ := h.yamada_5_21_3 hW d hK hD
  have hx' : x ∈ yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) := by
    refine (h3 x).1 ⟨hR₅R₂N hx, _, hy, ?_⟩
    group
  have hx'' : x ∈ ((yamadaR₂ d t ⊔ (centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G)) :
      Subgroup G) : Set G) := hx'
  rw [h5] at hx''
  obtain ⟨r, hr, c, hcN, rfl⟩ := Set.mem_mul.1 hx''
  have hR₂R₃ : yamadaR₂ d t ≤ yamadaR₃ d t := hR₃R₄.ge.trans inf_le_left
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t :=
    le_sup_left.trans (h.yamada_5_27_2 hW d hK hD).1.1.ge
  have hcR₅ : c ∈ yamadaR₅ d t := by
    have := mul_mem (inv_mem (hR₃R₅ (hR₂R₃ hr))) hx
    rwa [inv_mul_cancel_left] at this
  have hcR := h.yamadaR₅_inf_le d hK hD (Subgroup.mem_inf.2 ⟨hcR₅, hcN⟩)
  exact mul_mem hr ((h.yamadaR₂_inf_centralizer d hK).1 hcR)

private theorem card_le_of_commutator_mem_yamadaS₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {B : Subgroup G}
    (hYB : yamadaY₂ d t ≤ B) (hBS : B ≤ yamadaS₅ d t)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ yamadaY₂ d t) : Nat.card B ≤ Nat.card K ^ 9 := by
  have hD := hQ.doubling
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hMel, hDel⟩ := h.elemModulo_yamadaY₂_yamadaM₅_yamadaD₅ hW d hK hQ
  obtain ⟨hMc, hDc⟩ := h.card_yamadaM₅_yamadaD₅ hW d hK hQ
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, -, -, -, hSdef⟩ := d.yamada_defs
  have hY₂R₅ : yamadaY₂ d t ≤ yamadaR₅ d t := hF₅R₅.trans' hY₂F₅
  haveI : ((yamadaY₂ d t).subgroupOf (yamadaR₅ d t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hY₂R₅).2 hR₅Y₂
  have hres := card_le_max_of_forall_commutator_mem (H := yamadaR₅ d t) (S₀ := yamadaS₅ d t)
    (A := yamadaM₅ d t) (B := yamadaD₅ d t) (N := yamadaY₂ d t) (X := B)
    (hY₂F₅.trans hF₅M₅) (hY₂F₅.trans hF₅D₅) hM₅S₅ hD₅S₅ hS₅R₅ ?_ hMel hDel
    (h.exists_commutator_not_mem_yamadaY₂ hW d hK hQ) ?_ hYB hBS hB
  · rw [hMc, hDc, max_self] at hres
    exact hres
  · intro s hs
    rw [hS₅eq] at hs
    obtain ⟨s₀, hs₀, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
      (fun a ha => hR₅F₅ (hS₅R₅ (hSS₅ ha))) s hs
    have hs₀' : s₀ ∈ d.M ⊔ d.D := by
      rw [sup_comm, hSdef]
      exact hs₀
    obtain ⟨m, hm, δ, hδ, rfl⟩ := Common.exists_mul_of_le_normalizer
      (fun a ha => d.S_le_normalizers.2.2.2.2.2.2 (hDS ha)) s₀ hs₀'
    refine ⟨m, ?_, δ * f', ?_, ?_⟩
    · rw [hM₅eq]
      exact mem_sup_left hm
    · rw [hD₅eq]
      exact mul_mem (mem_sup_left hδ) (mem_sup_right hf')
    · group
  · intro a ha haD s hs hsc
    refine h.mem_yamadaM₅_of_commutator_mem hW d hK hQ ha (fun hF => haD (hF₅D₅ hF)) hs hsc

private theorem card_le_of_commutator_mem_of_not_le (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    {B : Subgroup G} (hYB : yamadaY₂ d t ≤ B) (hBR : B ≤ yamadaR₅ d t)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ⁅x, y⁆ ∈ yamadaY₂ d t) (hBS : ¬ B ≤ yamadaS₅ d t) :
    Nat.card B ≤ 2 * Nat.card K ^ 7 := by
  have hD := hQ.doubling
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, hF₅eq, -, hEl, hcardF⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, ⟨hS₅R, htS₅N, htS₅⟩, -⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  have hY₂S₅ : yamadaY₂ d t ≤ yamadaS₅ d t := hY₂F₅.trans (hF₅M₅.trans hM₅S₅)
  obtain ⟨b, hbB, hbS₅⟩ := Set.not_subset.1 hBS
  have hbR : b ∈ yamadaS₅ d t ⊔ zpowers t := hS₅R ▸ hBR hbB
  obtain ⟨s', hs', rfl⟩ : ∃ s' ∈ yamadaS₅ d t, b = s' * t := by
    rcases (mem_sup_zpowers_iff_of h.t_mul_t htS₅N).1 hbR with h1 | h1
    · exact absurd h1 hbS₅
    · exact h1
  have hBS₅R : yamadaS₅ d t ⊔ B = yamadaR₅ d t := by
    refine le_antisymm (sup_le hS₅R₅ hBR) ?_
    rw [← hS₅R]
    refine sup_le le_sup_left ((zpowers_le).2 ?_)
    have := mul_mem (inv_mem (mem_sup_left hs' : s' ∈ yamadaS₅ d t ⊔ B))
      (mem_sup_right hbB : s' * t ∈ yamadaS₅ d t ⊔ B)
    rwa [inv_mul_cancel_left] at this
  set B₀ : Subgroup G := yamadaS₅ d t ⊓ B with hB₀
  have hcardB : Nat.card B = 2 * Nat.card B₀ := by
    have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaS₅ d t) (B := B)
      (fun x hx => hR₅S₅ (hBR hx))
    rw [hBS₅R, ← hS₅R, h.card_sup_zpowers htS₅N htS₅] at h1
    have hpos : 0 < Nat.card (yamadaS₅ d t) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [← h1]
    ring
  have hB₀B : B₀ ≤ B := inf_le_right
  have hB₀S₅ : B₀ ≤ yamadaS₅ d t := inf_le_left
  have hB₀R₅ : B₀ ≤ yamadaR₅ d t := hB₀S₅.trans hS₅R₅
  have hB₁ : ∀ x ∈ B₀ ⊔ yamadaF₅ d t, ∀ y ∈ B₀ ⊔ yamadaF₅ d t, ⁅x, y⁆ ∈ yamadaY₂ d t :=
    commutator_mem_sup_of_le_normalizer (fun a ha => hR₅F₅ (hB₀R₅ ha))
      (sup_le (fun x hx => hR₅Y₂ (hB₀R₅ hx)) (fun x hx => hR₅Y₂ (hF₅R₅ hx)))
      (fun a ha a' ha' => hB a (hB₀B ha) a' (hB₀B ha'))
      (fun b hb b' hb' => (hEl b hb b' hb').2)
      (fun a ha b hb => h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ (hB₀S₅ ha) hb)
  have hB₁c : Nat.card (B₀ ⊔ yamadaF₅ d t : Subgroup G) ≤ Nat.card K ^ 9 :=
    h.card_le_of_commutator_mem_yamadaS₅ hW d hK hQ
      (le_sup_of_le_right hY₂F₅) (sup_le hB₀S₅ (hF₅M₅.trans hM₅S₅)) hB₁
  have hFB : yamadaF₅ d t ⊓ B₀ ≤ yamadaF₂ d t := by
    intro x hx
    obtain ⟨hxF, hxB₀⟩ := Subgroup.mem_inf.1 hx
    have hxB : x ∈ B := hB₀B hxB₀
    have h1 : ⁅x, s' * t⁆ ∈ yamadaY₂ d t := hB x hxB _ hbB
    have h2 : x * s' * x⁻¹ * s'⁻¹ ∈ yamadaY₂ d t := by
      have := inv_mem (h.commutator_mem_yamadaY₂_of_mem_yamadaS₅ hW d hK hQ hs' hxF)
      rwa [show (s' * x * s'⁻¹ * x⁻¹)⁻¹ = x * s' * x⁻¹ * s'⁻¹ by group] at this
    have h3 : x * t * x⁻¹ * t⁻¹ ∈ yamadaY₂ d t := by
      have h4 : s' * (x * t * x⁻¹ * t⁻¹) * s'⁻¹ ∈ yamadaY₂ d t := by
        have := mul_mem (inv_mem h2) h1
        rwa [show (x * s' * x⁻¹ * s'⁻¹)⁻¹ * ⁅x, s' * t⁆ =
          s' * (x * t * x⁻¹ * t⁻¹) * s'⁻¹ by simp only [commutatorElement_def]; group] at this
      have h5 := (mem_normalizer_iff.1 (hR₅Y₂ (inv_mem (hS₅R₅ hs'))) _).1 h4
      rwa [show s'⁻¹ * (s' * (x * t * x⁻¹ * t⁻¹) * s'⁻¹) * s'⁻¹⁻¹ = x * t * x⁻¹ * t⁻¹ by
        group] at h5
    have hxR₂ := h.mem_yamadaR₂_of_commutator_mem hW d hK hQ (hF₅R₅ hxF) h3
    exact h.yamadaF₅_inf_yamadaR₂_le hW d hK hQ (Subgroup.mem_inf.2 ⟨hxF, hxR₂⟩)
  have hF₂c := h.card_yamadaF₂ d hK hD
  have hF₅c : Nat.card (yamadaF₅ d t) = Nat.card K ^ 8 := by
    rw [hcardF, h.card_yamadaY₂ d hK hD]
    ring
  have h2 : Nat.card (yamadaF₅ d t ⊓ B₀ : Subgroup G) ≤ Nat.card K ^ 6 :=
    (Subgroup.card_le_of_le hFB).trans hF₂c.le
  have h1 := Common.card_sup_mul_card_inf_eq (A := yamadaF₅ d t) (B := B₀)
    (fun x hx => hR₅F₅ (hB₀R₅ hx))
  rw [sup_comm, hF₅c] at h1
  have h3 : Nat.card K ^ 8 * Nat.card B₀ ≤ Nat.card K ^ 8 * Nat.card K ^ 7 := by
    rw [← h1]
    calc Nat.card (B₀ ⊔ yamadaF₅ d t : Subgroup G) * Nat.card (yamadaF₅ d t ⊓ B₀ : Subgroup G)
        ≤ Nat.card K ^ 9 * Nat.card K ^ 6 := Nat.mul_le_mul hB₁c h2
      _ = Nat.card K ^ 8 * Nat.card K ^ 7 := by ring
  have hpos8 : 0 < Nat.card K ^ 8 := by
    have : 0 < Nat.card K := Nat.card_pos
    positivity
  have h4 := Nat.le_of_mul_le_mul_left h3 hpos8
  rw [hcardB]
  omega

theorem yamada_5_46_3 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ _ : ((yamadaY₂ d t).subgroupOf (yamadaR₅ d t)).Normal,
      CFSG.Open.thompsonSubgroup
          (⊤ : Subgroup (yamadaR₅ d t ⧸ (yamadaY₂ d t).subgroupOf (yamadaR₅ d t))) =
        ((yamadaS₅ d t).subgroupOf (yamadaR₅ d t)).map
          (QuotientGroup.mk' ((yamadaY₂ d t).subgroupOf (yamadaR₅ d t))) := by
  have hD := hQ.doubling
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, -⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hMel, hDel⟩ := h.elemModulo_yamadaY₂_yamadaM₅_yamadaD₅ hW d hK hQ
  obtain ⟨hMc, hDc⟩ := h.card_yamadaM₅_yamadaD₅ hW d hK hQ
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, hR₅Y₂, -, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨-, -, -, -, -, -, -, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, -, -, -, hSdef⟩ := d.yamada_defs
  have hY₂R₅ : yamadaY₂ d t ≤ yamadaR₅ d t := hF₅R₅.trans' hY₂F₅
  have hNormal : ((yamadaY₂ d t).subgroupOf (yamadaR₅ d t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hY₂R₅).2 hR₅Y₂
  refine ⟨hNormal, ?_⟩
  have hq : 2 * Nat.card K ^ 7 < Nat.card K ^ 9 := by
    have h7 : 0 < Nat.card K ^ 7 := by
      have : 0 < Nat.card K := Nat.card_pos
      positivity
    have h2 : 2 < Nat.card K ^ 2 := by nlinarith [hQ.four_le]
    calc 2 * Nat.card K ^ 7 < Nat.card K ^ 2 * Nat.card K ^ 7 :=
          Nat.mul_lt_mul_of_pos_right h2 h7
      _ = Nat.card K ^ 9 := by ring
  refine thompsonSubgroup_quotient_eq (R := yamadaR₅ d t) (S := yamadaS₅ d t)
    (N := yamadaY₂ d t) (M₀ := yamadaM₅ d t) (D₀ := yamadaD₅ d t)
    (hY₂F₅.trans (hF₅M₅.trans hM₅S₅)) hS₅R₅ (hY₂F₅.trans hF₅M₅) hM₅S₅ (hY₂F₅.trans hF₅D₅) hD₅S₅
    ?_ (fun x hx y hy => (hMel x hx y hy).2) (fun x hx y hy => (hDel x hx y hy).2)
    (Nat.card K ^ 9) hMc hDc ?_ ?_
  · refine le_antisymm ?_ (sup_le hM₅S₅ hD₅S₅)
    rw [hS₅eq]
    refine sup_le ?_ (hF₅M₅.trans le_sup_left)
    rw [← hSdef]
    refine sup_le ?_ ?_
    · exact (show d.D ≤ yamadaD₅ d t by rw [hD₅eq]; exact le_sup_left).trans le_sup_right
    · exact (show d.M ≤ yamadaM₅ d t by rw [hM₅eq]; exact le_sup_left).trans le_sup_left
  · intro B hYB hBR hBc
    by_cases hBS : B ≤ yamadaS₅ d t
    · exact h.card_le_of_commutator_mem_yamadaS₅ hW d hK hQ hYB hBS hBc
    · exact ((h.card_le_of_commutator_mem_of_not_le hW d hK hQ hYB hBR hBc hBS).trans hq.le)
  · intro B hYB hBR hBc hBcard
    by_contra hBS
    have := h.card_le_of_commutator_mem_of_not_le hW d hK hQ hYB hBR hBc hBS
    omega

private theorem mul_self_mem_yamadaC₁_of_mem_yamadaCstar (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) (hK4 : 4 ≤ Nat.card K) {x : G}
    (hx : x ∈ yamadaCstar d t) : x * x ∈ yamadaC₁ d t := by
  obtain ⟨hN₁, hN₂, φ, -⟩ := h.yamada_5_19_4 d hK hD
  obtain ⟨δ, hδ⟩ := QuotientGroup.mk_surjective (φ (QuotientGroup.mk ⟨x, hx⟩))
  have h1 : φ (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨x, hx⟩) = 1 := by
    rw [map_mul, ← hδ, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have h2 : (δ : G) * (δ : G) ∈ closure {z | ∃ g ∈ d.D, z = g ^ 2} :=
      subset_closure ⟨δ, δ.2, (sq (δ : G)).symm⟩
    rw [(d.yamada_3_12_mho hK4).1] at h2
    exact h2
  have h3 : (QuotientGroup.mk ⟨x, hx⟩ * QuotientGroup.mk ⟨x, hx⟩ :
      yamadaCstar d t ⧸ (yamadaC₁ d t).subgroupOf (yamadaCstar d t)) = 1 :=
    φ.injective (h1.trans (map_one φ).symm)
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf] at h3
  exact h3

private theorem yamadaF₂_le_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaF₂ d t ≤ yamadaF₅ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hF₅eq, -⟩ := yamada_5_46_1 hW h d hK hQ
  obtain ⟨-, -, -, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, -, -, hX₂X₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  have hTwo := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  rw [← hF₅eq]
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hTwo.exists_mul x hx
  exact mul_mem (mem_sup_left (hW₂W₃ ha)) (mem_sup_right (hX₂X₄ hb))

private theorem yamadaM₅_inf_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    yamadaM₅ d t ⊓ yamadaD₅ d t = yamadaF₅ d t ∧ ¬ yamadaM₅ d t ≤ yamadaD₅ d t ∧
      ¬ yamadaD₅ d t ≤ yamadaM₅ d t := by
  have hD := hQ.doubling
  obtain ⟨⟨hS₅eq, hM₅eq, hD₅eq⟩, ⟨hSF, hMF, hDF⟩⟩ := h.yamadaS₅_eq_sup hW d hK hQ
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, -, -, -, hFD, hFM, hDS, hMS, -⟩ := d.inclusions
  obtain ⟨-, -, -, -, -, -, -, hDM, -⟩ := d.yamada_defs
  have hSR₅ := h.S_le_yamadaR₅ hW d hK hD
  have hFF₅ : d.F ≤ yamadaF₅ d t := hMF ▸ inf_le_right
  have hne1 : ¬ yamadaM₅ d t ≤ yamadaD₅ d t := fun hle => d.not_M_le_D fun m hm => by
    have hm' : m ∈ d.D ⊔ yamadaF₅ d t := hD₅eq ▸ hle (hM₅eq ▸ mem_sup_left hm)
    obtain ⟨δ, hδ, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
      (fun a ha => hR₅F₅ (hSR₅ (hDS ha))) m hm'
    have hf'S : f' ∈ d.S ⊓ yamadaF₅ d t := by
      refine Subgroup.mem_inf.2 ⟨?_, hf'⟩
      have := mul_mem (inv_mem (hDS hδ)) (hMS hm)
      rwa [inv_mul_cancel_left] at this
    rw [hSF] at hf'S
    exact mul_mem hδ (hFD hf'S)
  have hne2 : ¬ yamadaD₅ d t ≤ yamadaM₅ d t := fun hle => d.not_D_le_M fun m hm => by
    have hm' : m ∈ d.M ⊔ yamadaF₅ d t := hM₅eq ▸ hle (hD₅eq ▸ mem_sup_left hm)
    obtain ⟨μ, hμ, f', hf', rfl⟩ := Common.exists_mul_of_le_normalizer'
      (fun a ha => hR₅F₅ (hSR₅ (hMS ha))) m hm'
    have hf'S : f' ∈ d.S ⊓ yamadaF₅ d t := by
      refine Subgroup.mem_inf.2 ⟨?_, hf'⟩
      have := mul_mem (inv_mem (hMS hμ)) (hDS hm)
      rwa [inv_mul_cancel_left] at this
    rw [hSF] at hf'S
    exact mul_mem hμ (hFM hf'S)
  refine ⟨le_antisymm (fun x hx => ?_) (le_inf hF₅M₅ hF₅D₅), hne1, hne2⟩
  obtain ⟨hxM, hxD⟩ := Subgroup.mem_inf.1 hx
  have hxM' : x ∈ d.M ⊔ yamadaF₅ d t := hM₅eq ▸ hxM
  obtain ⟨m, hm, f₁, hf₁, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun a ha => hR₅F₅ (hSR₅ (hMS ha))) x hxM'
  have hmD : m ∈ yamadaD₅ d t := by
    have := mul_mem hxD (inv_mem (hF₅D₅ hf₁))
    rwa [mul_inv_cancel_right] at this
  have hmD' : m ∈ d.D ⊔ yamadaF₅ d t := hD₅eq ▸ hmD
  obtain ⟨δ, hδ, f₂, hf₂, rfl⟩ := Common.exists_mul_of_le_normalizer'
    (fun a ha => hR₅F₅ (hSR₅ (hDS ha))) m hmD'
  have hf₂S : f₂ ∈ d.S ⊓ yamadaF₅ d t := by
    refine Subgroup.mem_inf.2 ⟨?_, hf₂⟩
    have := mul_mem (inv_mem (hDS hδ)) (hMS hm)
    rwa [inv_mul_cancel_left] at this
  rw [hSF] at hf₂S
  have hmF : δ * f₂ ∈ d.F := by
    rw [← hDM]
    exact Subgroup.mem_inf.2 ⟨mul_mem hδ (hFD hf₂S), hm⟩
  exact mul_mem (hFF₅ hmF) hf₁

private theorem closure_sq_yamadaM₅_yamadaD₅ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    closure {z | ∃ g ∈ yamadaM₅ d t, z = g ^ 2} = yamadaY₂ d t ∧
      closure {z | ∃ g ∈ yamadaD₅ d t, z = g ^ 2} ≤ yamadaY₁ d t := by
  have hD := hQ.doubling
  have hK4 : 4 ≤ Nat.card K := hQ.four_le
  obtain ⟨hMel, hDel⟩ := h.elemModulo_yamadaY₂_yamadaM₅_yamadaD₅ hW d hK hQ
  have hM₃sq := (h.yamada_5_35_3 hW d hK hQ).2.2.2
  refine ⟨le_antisymm ((closure_le _).2 fun z ⟨g, hg, e⟩ => ?_) ?_, ?_⟩
  · rw [e, SetLike.mem_coe, sq]
    exact (hMel g hg g hg).1
  · rw [← hM₃sq]
    exact closure_mono fun z ⟨g, hg, e⟩ => ⟨g, (le_sup_left : yamadaM₃ d t ≤ yamadaM₅ d t) hg, e⟩
  · rw [closure_le]
    rintro z ⟨g, hg, rfl⟩
    have hgC : g ∈ yamadaCstar d t :=
      ((sup_le (inf_le_right.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        yamadaD₅ d t ≤ yamadaCstar d t) hg)
    have h1 : g * g ∈ yamadaC₁ d t := h.mul_self_mem_yamadaC₁_of_mem_yamadaCstar d hK hD hK4 hgC
    have h2 : g * g ∈ yamadaY₂ d t := (hDel g hg g hg).1
    rw [SetLike.mem_coe, sq, ← h.yamadaY₂_inf_yamadaR₁ d hK hD]
    exact Subgroup.mem_inf.2 ⟨h2, (le_sup_left : yamadaC₁ d t ≤ yamadaR₁ d t) h1⟩

theorem yamada_5_46_4 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    (yamadaF₅ d t ≤ yamadaR₅ d t ∧ yamadaM₅ d t ≤ yamadaR₅ d t ∧ yamadaD₅ d t ≤ yamadaR₅ d t ∧
      yamadaS₅ d t ≤ yamadaR₅ d t) ∧
    ((yamadaF₅ d t).subgroupOf (yamadaR₅ d t)).Characteristic ∧
      ((yamadaM₅ d t).subgroupOf (yamadaR₅ d t)).Characteristic ∧
      ((yamadaD₅ d t).subgroupOf (yamadaR₅ d t)).Characteristic ∧
      ((yamadaS₅ d t).subgroupOf (yamadaR₅ d t)).Characteristic := by
  have hD := hQ.doubling
  obtain ⟨hNormal, hJ⟩ := yamada_5_46_3 hW h d hK hQ
  haveI := hNormal
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨hMDinf, hne1, hne2⟩ := h.yamadaM₅_inf_yamadaD₅ hW d hK hQ
  obtain ⟨hM₅sq, hD₅sq⟩ := h.closure_sq_yamadaM₅_yamadaD₅ hW d hK hQ
  have hM₅R₅ := hM₅S₅.trans hS₅R₅
  have hD₅R₅ := hD₅S₅.trans hS₅R₅
  have hF₂R₅ := (h.yamadaF₂_le_yamadaF₅ hW d hK hQ).trans hF₅R₅
  have hY₂R₅ := hY₂F₅.trans hF₅R₅
  have hF₂fix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaF₂ d t) = yamadaF₂ d t :=
    fun φ => by
      have h37 := (h.yamada_5_37_3 hW d hK hQ).2.2
      rw [← h37, autImage_closure_sq φ le_rfl, autImage_self]
  have hY₂fix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaY₂ d t) = yamadaY₂ d t :=
    fun φ => by
      have hc := h.yamadaF₂_center d hK hD
      calc autImage φ (yamadaY₂ d t)
          = autImage φ (yamadaF₂ d t ⊓ centralizer (yamadaF₂ d t : Set G)) := by rw [hc]
        _ = autImage φ (yamadaF₂ d t) ⊓ centralizer (autImage φ (yamadaF₂ d t) : Set G) :=
          autImage_inf_centralizer φ hF₂R₅
        _ = yamadaF₂ d t ⊓ centralizer (yamadaF₂ d t : Set G) := by rw [hF₂fix φ]
        _ = yamadaY₂ d t := hc
  have hS₅fix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaS₅ d t) = yamadaS₅ d t :=
    fun φ => autImage_eq_of_thompsonSubgroup_quotient
      (hY₂F₅.trans (hF₅M₅.trans hM₅S₅)) hS₅R₅ hJ φ (hY₂fix φ)
  have hmax : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, ∀ {E : Subgroup G},
      (E = yamadaM₅ d t ∨ E = yamadaD₅ d t) →
      autImage φ E = yamadaM₅ d t ∨ autImage φ E = yamadaD₅ d t := fun φ E hE => by
    rw [← h.yamada_5_46_2 hW d hK hQ]
    refine maximal_autImage φ (hY₂fix φ) (hS₅fix φ) hS₅R₅ ?_
    exact (h.yamada_5_46_2 hW d hK hQ E).2 hE
  have hcard := h.card_yamadaY₁ d hK hD
  have hcard₂ := h.card_yamadaY₂ d hK hD
  have hq : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right hQ.one_lt (by norm_num)
  have hMfix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaM₅ d t) = yamadaM₅ d t :=
    fun φ => by
      rcases hmax φ (Or.inl rfl) with h1 | h1
      · exact h1
      · exfalso
        have h2 : autImage φ (yamadaY₂ d t) ≤ yamadaY₁ d t := by
          rw [← hM₅sq, autImage_closure_sq φ hM₅R₅, h1]
          exact hD₅sq
        have h3 := Subgroup.card_le_of_le h2
        rw [card_autImage φ hY₂R₅, hcard, hcard₂] at h3
        omega
  have hDfix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaD₅ d t) = yamadaD₅ d t :=
    fun φ => by
      rcases hmax φ (Or.inr rfl) with h1 | h1
      · exfalso
        exact hne2 (by
          rw [autImage_injective φ hD₅R₅ hM₅R₅ (h1.trans (hMfix φ).symm)])
      · exact h1
  have hFfix : ∀ φ : yamadaR₅ d t ≃* yamadaR₅ d t, autImage φ (yamadaF₅ d t) = yamadaF₅ d t :=
    fun φ => by
      have hle : autImage φ (yamadaF₅ d t) ≤ yamadaF₅ d t := by
        rw [← hMDinf]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := mem_autImage.1 hx
        have hy' : (y : G) ∈ yamadaM₅ d t ⊓ yamadaD₅ d t := hMDinf ▸ hy
        obtain ⟨hyM, hyD⟩ := Subgroup.mem_inf.1 hy'
        refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
        · rw [← hMfix φ]
          exact mem_autImage.2 ⟨y, hyM, rfl⟩
        · rw [← hDfix φ]
          exact mem_autImage.2 ⟨y, hyD, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_autImage φ hF₅R₅])
  exact ⟨⟨hF₅R₅, hM₅R₅, hD₅R₅, hS₅R₅⟩, characteristic_of_autImage hFfix,
    characteristic_of_autImage hMfix, characteristic_of_autImage hDfix,
    characteristic_of_autImage hS₅fix⟩

private theorem normalizer_yamadaR₅_le_normalizer_yamadaF₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₅ d t : Set G) ≤ normalizer (yamadaF₅ d t : Set G) := by
  obtain ⟨⟨hF₅R₅, -⟩, hchar, -⟩ := h.yamada_5_46_4 hW d hK hQ
  have := hchar
  have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((yamadaF₅ d t).subgroupOf (yamadaR₅ d t))
  rw [subgroupOf_map_subtype, inf_of_le_left hF₅R₅] at h1
  exact h1

private theorem mem_yamadaR₃_of_mem_normalizer_yamadaV₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a : G}
    (ha : a ∈ yamadaR₅ d t) (hV : a ∈ normalizer (yamadaV₂ d t : Set G)) :
    a ∈ yamadaR₃ d t := by
  have hD := hQ.doubling
  have hR₆ : a ∈ yamadaL₆ d t ⊔ d.S := h.yamadaR₅_le_yamadaR₆ hW d hK hQ ha
  obtain ⟨l, hl, s, hs, rfl⟩ := Common.exists_mul_of_le_normalizer
    (h.S_le_normalizer_yamadaL₆ d) a hR₆
  obtain ⟨-, -, -, hR₃V, -⟩ := h.yamadaL₃_facts hW d hK hD
  have hsR₃ : s ∈ yamadaR₃ d t := (le_sup_right : d.S ≤ yamadaR₃ d t) hs
  have hlV : l ∈ normalizer (yamadaV₂ d t : Set G) := by
    have := mul_mem hV (inv_mem (hR₃V hsR₃))
    rwa [mul_inv_cancel_right] at this
  have hlL₃ : l ∈ yamadaL₃ d t := by
    rw [← (h.yamada_5_39_1 hW d hK hQ).2]
    exact Subgroup.mem_inf.2 ⟨hl, hlV⟩
  exact mul_mem ((le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t) hlL₃) hsR₃

private theorem mem_yamadaR₄_of_mem_normalizer_yamadaU₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a : G}
    (ha : a ∈ yamadaR₅ d t) (hU : a ∈ normalizer (yamadaU₂ d t : Set G)) :
    a ∈ yamadaR₄ d t := by
  have hD := hQ.doubling
  have hy' : a ∈ ((normalizer (yamadaU₂ d t : Set G) : Subgroup G) : Set G) := hU
  rw [(h.yamada_5_25_1 hW d hK hD).2.2.1] at hy'
  obtain ⟨ρ, hρ, c, hcN, hyρ⟩ := Set.mem_mul.1 hy'
  have hR₅eq := (h.yamada_5_27_2 hW d hK hD).1
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := hR₅eq.1 ▸ le_sup_right
  have hcR : c ∈ yamadaR d t := by
    refine h.yamadaR₅_inf_le d hK hD ⟨?_, hcN⟩
    have := mul_mem (inv_mem (hR₄R₅ hρ)) ha
    rwa [← hyρ, inv_mul_cancel_left] at this
  have hcR₂ : c ∈ yamadaR₂ d t := (h.yamadaR₂_inf_centralizer d hK).1 hcR
  rw [← hyρ]
  exact mul_mem hρ ((h.yamadaR₄_facts hW d hK hD).2.1 hcR₂)

private theorem maximal_elemModulo_yamadaE₅_yamadaW₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (X : Subgroup G) :
    Maximal (fun E' : Subgroup G => yamadaW₂ d t ≤ E' ∧ E' ≤ yamadaE₅ d t ∧
        ElemModulo (yamadaW₂ d t) E') X ↔ X = yamadaF₅ d t ∨ X = yamadaE₃ d t := by
  have hD := hQ.doubling
  obtain ⟨hY₂W₃, -, hF₅eq, -, hEl, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, -, -, ⟨hE₅eq, htF₅N, htF₅⟩⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, ⟨hE₃eq, htF₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, -, hR₅W₂, -⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨hW₃V₃, -, -, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨-, hF₅R₃, -⟩ := h.yamadaE₃_inf_E₄ hW d hK hQ
  obtain ⟨-, -, -, hR₃V, -⟩ := h.yamadaL₃_facts hW d hK hD
  have htW₂N := (h.t_mem_normalizer_yamadaW₂ d hK hD).1
  have hF₃E₃ : yamadaF₃ d t ≤ yamadaE₃ d t := hE₃eq ▸ le_sup_left
  have hF₃R₃ : yamadaF₃ d t ≤ yamadaR₃ d t :=
    hF₃E₃.trans (inf_le_left.trans (le_sup_left : yamadaL₃ d t ≤ yamadaR₃ d t))
  have hNA : yamadaW₂ d t ≤ yamadaF₅ d t := hW₂W₃.trans (hF₅eq ▸ le_sup_left)
  have hC : ∀ a ∈ yamadaF₅ d t, a ∈ yamadaF₃ d t ↔ t * a * t * a⁻¹ ∈ yamadaW₂ d t := by
    intro a ha
    constructor
    · intro haF₃
      exact (le_sup_left : d.W ≤ yamadaW₂ d t)
        (h.crossed_mem_W hW d hK hD (hR₃V (hF₃R₃ haF₃)))
    · intro hw
      have haN : a ∈ normalizer (yamadaV₂ d t : Set G) := by
        refine mem_normalizer_sup_zpowers_of_conj_mem (A := yamadaW₂ d t)
          (hR₅W₂ (hF₅R₅ ha)) ?_
        have e : a * t * a⁻¹ = t * (t * a * t * a⁻¹) := by
          calc a * t * a⁻¹ = (t * t) * a * t * a⁻¹ := by rw [h.t_mul_t, one_mul]
            _ = t * (t * a * t * a⁻¹) := by group
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hw)
      have haR₃ := h.mem_yamadaR₃_of_mem_normalizer_yamadaV₂ hW d hK hQ (hF₅R₅ ha) haN
      rw [← hF₅R₃]
      exact Subgroup.mem_inf.2 ⟨ha, haR₃⟩
  have hne : ∃ a ∈ yamadaF₅ d t, a ∉ yamadaF₃ d t := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hX₄U₄, hU₄N, hJX₄, hX₂X₄, -⟩ := h.yamadaX₄_facts hW d hK hD
    obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
    obtain ⟨⟨-, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
    have hX₄F₅ : yamadaX₄ d t ≤ yamadaF₅ d t := hF₅eq ▸ le_sup_right
    have hX₄R₂' : yamadaX₄ d t ≤ yamadaR₂ d t := fun x hx => by
      rw [← hR₃R₄]
      exact Subgroup.mem_inf.2 ⟨hF₃R₃ (hcon x (hX₄F₅ hx)), hX₄R₄ hx⟩
    have hlt := (h.yamada_5_32_2 hW d hK hD).2.1.2.2.2
    exact absurd (fun x hx => hX₄R₂ ▸ Subgroup.mem_inf.2 ⟨hx, hX₄R₂' hx⟩ :
      yamadaX₄ d t ≤ yamadaX₂ d t) (not_le_of_gt hlt)
  have := maximal_elemModulo_iff_sup_zpowers hNA (le_sup_left : yamadaF₃ d t ≤ yamadaF₅ d t)
    h.t_mul_t htF₅ htF₅N htW₂N (elemModulo_mono (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hEl) hC
    hne X
  rw [hE₅eq, hE₃eq] at this
  exact this

private theorem yamadaF₄_le_yamadaR₄ (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hD : h.DoublingFacts d) :
    yamadaF₄ d t ≤ yamadaR₄ d t := by
  obtain ⟨hX₄R₄, hX₄R₂, -⟩ := h.yamadaX₄_le_yamadaR₄ hW d hK hD
  obtain ⟨-, hR₂R₄, -⟩ := h.yamadaR₄_facts hW d hK hD
  have hF₂R₂ : yamadaF₂ d t ≤ yamadaR₂ d t :=
    ((le_sup_left : yamadaF₂ d t ≤ yamadaE₂ d t).trans (h.yamadaE₂_le_yamadaL₂ d hK hD).2).trans
      (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t)
  exact sup_le hX₄R₄ (hF₂R₂.trans hR₂R₄)

private theorem mem_yamadaF₄_iff (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) {a : G}
    (ha : a ∈ yamadaF₅ d t) : a ∈ yamadaF₄ d t ↔ t * a * t * a⁻¹ ∈ yamadaX₂ d t := by
  have hD := hQ.doubling
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, -, -, hR₅X₂⟩ := h.yamadaR₅_le_normalizers hW d hK hD
  obtain ⟨-, -, hF₄R₄⟩ := h.yamadaE₃_inf_E₄ hW d hK hQ
  have hF₄R₄' := h.yamadaF₄_le_yamadaR₄ hW d hK hD
  constructor
  · intro haF₄
    have hg : a ∈ normalizer (yamadaU₂ d t : Set G) :=
      LieType.BorelTits.pCoreOf_le 2 _ (hF₄R₄' haF₄)
    exact (le_sup_left : d.X ≤ yamadaX₂ d t) (h.crossed_mem_X hW d hK hD hg)
  · intro hw
    have haN : a ∈ normalizer (yamadaU₂ d t : Set G) := by
      refine mem_normalizer_sup_zpowers_of_conj_mem (A := yamadaX₂ d t) (hR₅X₂ (hF₅R₅ ha)) ?_
      have e : a * t * a⁻¹ = t * (t * a * t * a⁻¹) := by
        calc a * t * a⁻¹ = (t * t) * a * t * a⁻¹ := by rw [h.t_mul_t, one_mul]
          _ = t * (t * a * t * a⁻¹) := by group
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hw)
    have haR₄ := h.mem_yamadaR₄_of_mem_normalizer_yamadaU₂ hW d hK hQ (hF₅R₅ ha) haN
    rw [← hF₄R₄]
    exact Subgroup.mem_inf.2 ⟨ha, haR₄⟩

private theorem exists_mem_yamadaF₅_not_mem_yamadaF₄ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    ∃ a ∈ yamadaF₅ d t, a ∉ yamadaF₄ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hF₅eq, -⟩ := h.yamada_5_46_1 hW d hK hQ
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, hW₂W₃, -⟩ := h.yamadaW₃_facts hW d hK hD
  obtain ⟨⟨-, hR₃R₄, -, -⟩, -⟩ := h.yamada_5_27_2 hW d hK hD
  have hF₄R₄' := h.yamadaF₄_le_yamadaR₄ hW d hK hD
  have hW₃F₅ : yamadaW₃ d t ≤ yamadaF₅ d t := hF₅eq ▸ le_sup_left
  have hW₃R₂ : yamadaW₃ d t ≤ yamadaR₂ d t := fun x hx => by
    rw [← hR₃R₄]
    exact Subgroup.mem_inf.2 ⟨h.yamadaW₃_le_yamadaR₃ hW d hK hD hx,
      hF₄R₄' (hcon x (hW₃F₅ hx))⟩
  have hlt := (h.yamada_5_30_2 hW d hK hD).2.1.2.2.2
  have hle : yamadaW₃ d t ≤ yamadaW₂ d t := fun x hx =>
    h.yamadaW₃_inf_yamadaR₂_le hW d hK hD (Subgroup.mem_inf.2 ⟨hx, hW₃R₂ hx⟩)
  exact not_le_of_gt hlt hle

private theorem maximal_elemModulo_yamadaE₅_yamadaX₂ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (X : Subgroup G) :
    Maximal (fun E' : Subgroup G => yamadaX₂ d t ≤ E' ∧ E' ≤ yamadaE₅ d t ∧
        ElemModulo (yamadaX₂ d t) E') X ↔ X = yamadaF₅ d t ∨ X = yamadaE₄ d t := by
  have hD := hQ.doubling
  obtain ⟨-, -, hF₅eq, -, hEl, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨-, -, -, -, ⟨hE₅eq, htF₅N, htF₅⟩⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, ⟨hE₄eq, htF₄⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  obtain ⟨-, -, -, hX₂X₄, -⟩ := h.yamadaX₄_facts hW d hK hD
  have htX₂N := (h.t_mem_normalizer_yamadaX₂ d hK hD).1
  have hNA : yamadaX₂ d t ≤ yamadaF₅ d t := hX₂X₄.trans (hF₅eq ▸ le_sup_right)
  have := maximal_elemModulo_iff_sup_zpowers (C := yamadaF₄ d t) hNA
    (le_sup_right : yamadaF₄ d t ≤ yamadaF₅ d t)
    h.t_mul_t htF₅ htF₅N htX₂N
    (elemModulo_mono (le_sup_right : yamadaY₂ d t ≤ yamadaX₂ d t) hEl)
    (fun a ha => h.mem_yamadaF₄_iff hW d hK hQ ha)
    (h.exists_mem_yamadaF₅_not_mem_yamadaF₄ hW d hK hQ) X
  rw [hE₅eq, hE₄eq] at this
  exact this

private theorem normalizer_yamadaR₂_le_normalizer_yamadaE₅ (hW : CFSG.Walter.WalterOrderForm)
    (h : Setup G L f t) (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₂ d t : Set G) ≤ normalizer (yamadaE₅ d t : Set G) := by
  have hD := hQ.doubling
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, -, -, ⟨hE₅eq, htF₅N, htF₅⟩⟩ := h.yamada_5_37_2 hW d hK hQ
  have hR₅F₂N : yamadaR₅ d t ≤ normalizer (yamadaF₂ d t : Set G) :=
    (h.yamadaR₅_le_normalizers hW d hK hD).2.1
  have hcomm := comm_mem_of_mul_self_mem hR₅F₂N fun x hx =>
    h.mul_self_mem_yamadaF₂ hW d hK hQ hx
  have hF₂F₅ := h.yamadaF₂_le_yamadaF₅ hW d hK hQ
  intro g hg
  have hg' : g ∈ ((normalizer (yamadaR₂ d t : Set G) : Subgroup G) : Set G) := hg
  rw [(h.yamada_5_27_1 hW d hK hD).2.1] at hg'
  obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.1 hg'
  rw [← hE₅eq]
  refine mul_mem ?_ ?_
  · refine mem_normalizer_sup_zpowers_of_conj_mem (hR₅F₅ hr) ?_
    have e : r * t * r⁻¹ = (r * t * r⁻¹ * t⁻¹) * t := by group
    rw [e]
    exact mul_mem (mem_sup_left (hF₂F₅ (hcomm r hr t htR₅))) (mem_sup_right (mem_zpowers t))
  · have hcN₂ : c ∈ normalizer (yamadaR₂ d t : Set G) :=
      (h.yamada_5_27_1 hW d hK hD).1.ge (mem_sup_right hc)
    have hcR₅ : c ∈ normalizer (yamadaR₅ d t : Set G) :=
      LieType.BorelTits.le_normalizer_pCoreOf 2 _ hcN₂
    have hcF₅ := h.normalizer_yamadaR₅_le_normalizer_yamadaF₅ hW d hK hQ hcR₅
    have hct : c * t = t * c := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc).1
    refine mem_normalizer_sup_zpowers_of_conj_mem hcF₅ ?_
    rw [show c * t * c⁻¹ = t by rw [hct, mul_inv_cancel_right]]
    exact mem_sup_right (mem_zpowers t)

theorem yamada_5_47 (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t) (d : G2Data L K)
    (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    normalizer (yamadaR₅ d t : Set G) ⊓ normalizer (yamadaE₅ d t : Set G) =
      normalizer (yamadaR₂ d t : Set G) := by
  have hD := hQ.doubling
  refine le_antisymm (fun x hx => ?_) (fun x hx => Subgroup.mem_inf.2
    ⟨LieType.BorelTits.le_normalizer_pCoreOf 2 _ hx,
      h.normalizer_yamadaR₂_le_normalizer_yamadaE₅ hW d hK hQ hx⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hE₃F₅E₄, -⟩ := (h.yamadaE₃_inf_E₄ hW d hK hQ).imp_right fun h' => h'
  obtain ⟨-, -, hF₅eq, -⟩ := h.yamada_5_46_1 hW d hK hQ
  obtain ⟨hY₂F₅, hF₅M₅, hF₅D₅, hM₅S₅, hD₅S₅, hS₅R₅, hR₅F₅, hR₅S₅, hF₅R₅, hSS₅, htR₅⟩ :=
    h.yamadaS₅_basic hW d hK hQ
  obtain ⟨-, -, -, -, ⟨hE₅eq, htF₅N, htF₅⟩⟩ := h.yamada_5_37_2 hW d hK hQ
  obtain ⟨-, -, ⟨hE₃eq, htF₃⟩, -⟩ := h.yamada_5_30_2 hW d hK hD
  obtain ⟨-, -, ⟨hE₄eq, htF₄⟩, -⟩ := h.yamada_5_32_2 hW d hK hD
  have hTwo := h.twoElementaryProduct_yamadaF₂ hW d hK hQ
  have hcardW := h.card_yamadaW₂ d hK hD
  have hcardX := h.card_yamadaX₂ d hK hD
  have hWneX : yamadaW₂ d t ≠ yamadaX₂ d t := by
    intro he
    have h1 := congrArg (fun A => A ⊓ centralizer ({t} : Set G)) he
    simp only [h.yamadaW₂_inf_centralizer d hK hD, h.yamadaX₂_inf_centralizer d hK hD] at h1
    exact d.W_ne_X h1
  have hE₃ne : yamadaE₃ d t ≠ yamadaF₅ d t := fun he => htF₅ (he ▸ (hE₃eq ▸
    (mem_sup_right (mem_zpowers t) : t ∈ yamadaF₃ d t ⊔ zpowers t)))
  have hE₄ne : yamadaE₄ d t ≠ yamadaF₅ d t := fun he => htF₅ (he ▸ (hE₄eq ▸
    (mem_sup_right (mem_zpowers t) : t ∈ yamadaF₄ d t ⊔ zpowers t)))
  have key : ∀ x ∈ normalizer (yamadaR₅ d t : Set G) ⊓ normalizer (yamadaE₅ d t : Set G),
      ∀ y ∈ yamadaE₂ d t, x * y * x⁻¹ ∈ yamadaE₂ d t := by
    intro x hx y hy
    obtain ⟨hxR₅, hxE₅⟩ := Subgroup.mem_inf.1 hx
    have hxF₅ := h.normalizer_yamadaR₅_le_normalizer_yamadaF₅ hW d hK hQ hxR₅
    have hxF₂ : x ∈ normalizer (yamadaF₂ d t : Set G) := by
      have := mem_normalizer_closure_sq_of_mem_normalizer hxR₅
      rwa [(h.yamada_5_37_3 hW d hK hQ).2.2] at this
    have hF₅map : (yamadaF₅ d t).map (MulAut.conj x).toMonoidHom = yamadaF₅ d t :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 hxF₅
    have himg : ∀ {A : Subgroup G}, (A = yamadaW₂ d t ∨ A = yamadaX₂ d t) →
        A.map (MulAut.conj x).toMonoidHom = yamadaW₂ d t ∨
          A.map (MulAut.conj x).toMonoidHom = yamadaX₂ d t := by
      intro A hA
      have hAF : A ≤ yamadaF₂ d t := by
        rcases hA with rfl | rfl
        exacts [hTwo.le_left, hTwo.le_right]
      have hAel : CFSG.IsElementaryAbelian 2 A := by
        rcases hA with rfl | rfl
        exacts [hTwo.isElementaryAbelian_left, hTwo.isElementaryAbelian_right]
      have hAc : Nat.card A = Nat.card K ^ 5 := by
        rcases hA with rfl | rfl
        exacts [hcardW, hcardX]
      have hmapF : A.map (MulAut.conj x).toMonoidHom ≤ yamadaF₂ d t := by
        rintro _ ⟨a, ha, rfl⟩
        exact (mem_normalizer_iff.1 hxF₂ a).1 (hAF ha)
      haveI := hAel
      haveI : CFSG.IsElementaryAbelian 2 (A.map (MulAut.conj x).toMonoidHom) :=
        CFSG.IsElementaryAbelian.map _
      have hc2 : Nat.card (A.map (MulAut.conj x).toMonoidHom) = Nat.card K ^ 5 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hAc]
      rcases hTwo.le_or_le hmapF with h1 | h1
      · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [hc2, hcardW]))
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge h1 (by rw [hc2, hcardX]))
    have hinj : Function.Injective (Subgroup.map (MulAut.conj x).toMonoidHom) :=
      Subgroup.map_injective (MulAut.conj x).injective
    have hcase : (( yamadaW₂ d t).map (MulAut.conj x).toMonoidHom = yamadaW₂ d t ∧
        (yamadaX₂ d t).map (MulAut.conj x).toMonoidHom = yamadaX₂ d t) ∨
        ((yamadaW₂ d t).map (MulAut.conj x).toMonoidHom = yamadaX₂ d t ∧
          (yamadaX₂ d t).map (MulAut.conj x).toMonoidHom = yamadaW₂ d t) := by
      rcases himg (Or.inl rfl) with h1 | h1
      · refine Or.inl ⟨h1, ?_⟩
        rcases himg (Or.inr rfl) with h2 | h2
        · exact absurd (hinj (h1.trans h2.symm)) hWneX
        · exact h2
      · refine Or.inr ⟨h1, ?_⟩
        rcases himg (Or.inr rfl) with h2 | h2
        · exact h2
        · exact absurd (hinj (h1.trans h2.symm)) hWneX
    have hW₂max := (h.maximal_elemModulo_yamadaE₅_yamadaW₂ hW d hK hQ (yamadaE₃ d t)).2
      (Or.inr rfl)
    have hX₂max := (h.maximal_elemModulo_yamadaE₅_yamadaX₂ hW d hK hQ (yamadaE₄ d t)).2
      (Or.inr rfl)
    have hyE : y ∈ yamadaE₃ d t ⊓ yamadaE₄ d t := by
      rw [hE₃F₅E₄]
      exact hy
    obtain ⟨hyE₃, hyE₄⟩ := Subgroup.mem_inf.1 hyE
    have hy₃ : x * y * x⁻¹ ∈ (yamadaE₃ d t).map (MulAut.conj x).toMonoidHom := ⟨y, hyE₃, rfl⟩
    have hy₄ : x * y * x⁻¹ ∈ (yamadaE₄ d t).map (MulAut.conj x).toMonoidHom := ⟨y, hyE₄, rfl⟩
    rw [← hE₃F₅E₄]
    rcases hcase with ⟨hw, hx'⟩ | ⟨hw, hx'⟩
    · have h3 := maximal_map_conj_of_map_eq hw hxE₅ hW₂max
      have h4 := maximal_map_conj_of_map_eq hx' hxE₅ hX₂max
      rcases (h.maximal_elemModulo_yamadaE₅_yamadaW₂ hW d hK hQ _).1 h3 with h5 | h5
      · exact absurd (hinj (h5.trans hF₅map.symm)) hE₃ne
      rcases (h.maximal_elemModulo_yamadaE₅_yamadaX₂ hW d hK hQ _).1 h4 with h6 | h6
      · exact absurd (hinj (h6.trans hF₅map.symm)) hE₄ne
      rw [h5] at hy₃
      rw [h6] at hy₄
      exact Subgroup.mem_inf.2 ⟨hy₃, hy₄⟩
    · have h3 := maximal_map_conj_of_map_eq hw hxE₅ hW₂max
      have h4 := maximal_map_conj_of_map_eq hx' hxE₅ hX₂max
      rcases (h.maximal_elemModulo_yamadaE₅_yamadaX₂ hW d hK hQ _).1 h3 with h5 | h5
      · exact absurd (hinj (h5.trans hF₅map.symm)) hE₃ne
      rcases (h.maximal_elemModulo_yamadaE₅_yamadaW₂ hW d hK hQ _).1 h4 with h6 | h6
      · exact absurd (hinj (h6.trans hF₅map.symm)) hE₄ne
      rw [h5] at hy₃
      rw [h6] at hy₄
      exact Subgroup.mem_inf.2 ⟨hy₄, hy₃⟩
  have hxE₂ : x ∈ normalizer (yamadaE₂ d t : Set G) := mem_normalizer_iff.2 fun y =>
    ⟨key x hx y, fun hy => by
      have := key x⁻¹ (inv_mem hx) _ hy
      rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this⟩
  rw [(h.yamada_5_21_4 hW d hK hD).1]
  exact hxE₂

end Local

end Setup

end CFSG.LocalAnalysis.EvenBN.G2
