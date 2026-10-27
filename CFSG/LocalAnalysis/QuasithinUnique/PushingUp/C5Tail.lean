module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Rank1
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.QuasithinUnique.C5

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem thompsonJ_le_baum' (R : Subgroup G) : thompsonJ R ≤ baum R := by
  refine le_inf (iSup₂_le fun A hA => hA.1) ?_
  refine Subgroup.le_centralizer_iff.mpr ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨hz, -⟩
  exact hz.2

theorem eq_bot_of_noCommonNormal' {R H M₀ X : Subgroup G} {x : G} (hC : NoCommonNormal R H M₀)
    (hXR : X ≤ R) (hHX : H ≤ normalizer (X : Set G)) (hRX : R ≤ normalizer (X : Set G))
    (hxX : x ∈ normalizer (X : Set G)) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x) : X = ⊥ := by
  by_contra hne
  exact hC X hXR hne hHX (hM₀.trans (sup_le hRX (Subgroup.zpowers_le.mpr hxX)))

theorem le_normalizer_conj {R Y : Subgroup G} {x : G} (hxR : x ∈ normalizer (R : Set G))
    (hRY : R ≤ normalizer (Y : Set G)) :
    R ≤ normalizer ((conjSubgroup Y x : Subgroup G) : Set G) := by
  have := conjSubgroup_mono hRY x
  rwa [conjSubgroup_eq_self hxR, conjSubgroup_normalizer] at this

namespace Rank1

variable {B Q U W : Subgroup G} {q : ℕ} (h : Rank1 B Q U W q)
include h

theorem P_le_sup_inf_conj [Finite G] {R P D : Subgroup G} {x : G}
    (hPR : P ≤ R) (hxR : x ∈ normalizer (R : Set G)) (hxB : x ∈ normalizer (B : Set G))
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hDx : D ≤ conjSubgroup Q x)
    (hRU : R ≤ normalizer (U : Set G)) (hRP : R ≤ normalizer (P : Set G))
    (hUP : U ≤ P) (hQP : Q ≤ P) (hBR : B ≤ R) (hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u)
    (hSC : ∀ r ∈ R, (∀ b ∈ B, ⁅r, b⁆ ∈ P) → r ∈ B ⊔ P) :
    P ≤ U ⊔ (P ⊓ conjSubgroup P x) := by
  intro p hp
  have hpR : p ∈ R := hPR hp
  have hRUx := le_normalizer_conj hxR hRU
  have hRPx := le_normalizer_conj hxR hRP
  have hUxPx : conjSubgroup U x ≤ conjSubgroup P x := conjSubgroup_mono hUP x
  have hQxPx : conjSubgroup Q x ≤ conjSubgroup P x := conjSubgroup_mono hQP x
  have key : ∀ b' ∈ B, ⁅p, b'⁆ ∈ conjSubgroup P x := by
    intro b' hb'
    obtain ⟨u', hu', u₁, hu₁, d, hd, rfl⟩ := h.mem_B_decomp hxB hx2 hD hDc hb'
    have hc : ⁅p, u₁⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hPU p hp u₁ hu₁).symm
    have e1 : ⁅p, u₁ * d⁆ = ⁅p, u₁⁆ * (u₁ * ⁅p, d⁆ * u₁⁻¹) := by
      simp only [commutatorElement_def]; group
    have e2 : ⁅p, u' * (u₁ * d)⁆ = ⁅p, u'⁆ * (u' * ⁅p, u₁ * d⁆ * u'⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e2, e1, hc, one_mul]
    have hu'P : u' ∈ conjSubgroup P x := hUxPx hu'
    have hdP : d ∈ conjSubgroup P x := hQxPx (hDx hd)
    have m1 : ⁅p, u'⁆ ∈ conjSubgroup P x := by
      have h1 : p * u' * p⁻¹ ∈ conjSubgroup U x :=
        (Subgroup.mem_normalizer_iff.mp (hRUx hpR) u').mp hu'
      exact Subgroup.mul_mem _ (hUxPx h1) (Subgroup.inv_mem _ hu'P)
    have m2 : ⁅p, d⁆ ∈ conjSubgroup P x := by
      have h1 : p * d * p⁻¹ ∈ conjSubgroup P x :=
        (Subgroup.mem_normalizer_iff.mp (hRPx hpR) d).mp hdP
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hdP)
    have hu₁R : u₁ ∈ R := hPR (hUP hu₁)
    have m3 : u₁ * ⁅p, d⁆ * u₁⁻¹ ∈ conjSubgroup P x :=
      (Subgroup.mem_normalizer_iff.mp (hRPx hu₁R) _).mp m2
    exact Subgroup.mul_mem _ m1
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu'P m3) (Subgroup.inv_mem _ hu'P))
  have hrR : x * p * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxR p).mp hpR
  have hS2 : ∀ b ∈ B, ⁅x * p * x⁻¹, b⁆ ∈ P := by
    intro b hb
    have hb' : x⁻¹ * b * x ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxB) b).mp hb
      simpa using this
    have e : ⁅x * p * x⁻¹, b⁆ = x * ⁅p, x⁻¹ * b * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact mem_conjSubgroup_iff.mp (key _ hb')
  have hBP : B ≤ normalizer (P : Set G) := hBR.trans hRP
  obtain ⟨b₂, hb₂, p₂, hp₂, hr⟩ :=
    mem_sup_of_le_normalizer hBP (hSC _ hrR hS2)
  have hb₃ : x⁻¹ * b₂ * x ∈ B := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxB) b₂).mp hb₂
    simpa using this
  have hp₃ : x⁻¹ * p₂ * x ∈ conjSubgroup P x := by
    rw [mem_conjSubgroup_iff]; simpa [mul_assoc] using hp₂
  have hpeq : p = (x⁻¹ * b₂ * x) * (x⁻¹ * p₂ * x) := by
    calc p = x⁻¹ * (x * p * x⁻¹) * x := by group
      _ = x⁻¹ * (b₂ * p₂) * x := by rw [hr]
      _ = (x⁻¹ * b₂ * x) * (x⁻¹ * p₂ * x) := by group
  have hQN : Q ≤ normalizer ((conjSubgroup U x : Subgroup G) : Set G) :=
    h.Q_le_B.trans (h.B_le_normU_conj hxB)
  have hb₃' : x⁻¹ * b₂ * x ∈ Q ⊔ conjSubgroup U x := by
    rw [sup_comm]; exact (h.sup_Q_conj hxB hx2).symm ▸ hb₃
  obtain ⟨q₀, hq₀, u'', hu'', hb₃eq⟩ := mem_sup_of_le_normalizer hQN hb₃'
  have hq₀' := hq₀
  rw [hD] at hq₀'
  obtain ⟨u₁, hu₁, d, hd, rfl⟩ := mem_sup_of_commute hDc hq₀'
  have hy : d * u'' * (x⁻¹ * p₂ * x) ∈ conjSubgroup P x :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hQxPx (hDx hd)) (hUxPx hu'')) hp₃
  have hpeq' : p = u₁ * (d * u'' * (x⁻¹ * p₂ * x)) := by
    rw [hpeq, hb₃eq]; simp [mul_assoc]
  have hyP : d * u'' * (x⁻¹ * p₂ * x) ∈ P := by
    have : d * u'' * (x⁻¹ * p₂ * x) = u₁⁻¹ * p := by rw [hpeq']; simp
    rw [this]
    exact P.mul_mem (P.inv_mem (hUP hu₁)) hp
  rw [hpeq']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁) (Subgroup.mem_sup_right ⟨hyP, hy⟩)

theorem P_eq_Q [Finite G] {R H M₀ P D : Subgroup G} {x : G} (hC : NoCommonNormal R H M₀)
    (hBdef : B = baum R) (hQmax : IsMaxElemAbelian R Q)
    (hBR : B ≤ R) (hPR : P ≤ R) (hxR : x ∈ normalizer (R : Set G))
    (hxB : x ∈ normalizer (B : Set G)) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hD : Q = U ⊔ D)
    (hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u) (hDx : D ≤ conjSubgroup Q x)
    (hDx' : D ≤ conjSubgroup Q x⁻¹) (hRU : R ≤ normalizer (U : Set G))
    (hRP : R ≤ normalizer (P : Set G)) (hHP : H ≤ normalizer (P : Set G))
    (hUP : U ≤ P) (hQP : Q ≤ P) (hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u)
    (hSC : ∀ r ∈ R, (∀ b ∈ B, ⁅r, b⁆ ∈ P) → r ∈ B ⊔ P) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x) :
    P = Q ∧ ElemAb2 P := by
  have h1 := h.P_le_sup_inf_conj hPR hxR hxB hx2 hD hDc hDx hRU hRP hUP hQP hBR hPU hSC
  have h2 := h.P_le_sup_inf_conj (x := x⁻¹) hPR (inv_mem hxR) (inv_mem hxB)
    (by rw [inv_inv]; exact hx1) hD hDc hDx' hRU hRP hUP hQP hBR hPU hSC
  have e1 : P = U ⊔ (P ⊓ conjSubgroup P x) := le_antisymm h1 (sup_le hUP inf_le_left)
  have e2 : P = U ⊔ (P ⊓ conjSubgroup P x⁻¹) := le_antisymm h2 (sup_le hUP inf_le_left)
  have hcomm : ∀ A : Subgroup G, A ≤ P → ∀ u ∈ U, ∀ a ∈ A, u * a = a * u := fun A hA u hu a ha =>
    hPU a (hA ha) u hu
  have s1 : sqSub P = sqSub (P ⊓ conjSubgroup P x) := by
    conv_lhs => rw [e1]
    exact sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have s2 : sqSub P = sqSub (P ⊓ conjSubgroup P x⁻¹) := by
    conv_lhs => rw [e2]
    exact sqSub_sup_eq hU2 (hcomm _ inf_le_left)
  have hxsq : conjSubgroup (sqSub P) x = sqSub P := by
    calc conjSubgroup (sqSub P) x = conjSubgroup (sqSub (P ⊓ conjSubgroup P x⁻¹)) x := by
          rw [← s2]
      _ = sqSub (conjSubgroup (P ⊓ conjSubgroup P x⁻¹) x) := conjSubgroup_sqSub _ _
      _ = sqSub (P ⊓ conjSubgroup P x) := by
          rw [conjSubgroup_inf, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one,
            inf_comm]
      _ = sqSub P := s1.symm
  have hsq_eq_bot : sqSub P = ⊥ := by
    refine eq_bot_of_noCommonNormal' hC (sqSub_le_self.trans hPR) (fun g hg => ?_)
      (fun g hg => ?_) (conjSubgroup_eq_iff_mem_normalizer.mp hxsq) hM₀
    · exact conjSubgroup_eq_iff_mem_normalizer.mp
        (conjSubgroup_sqSub_of_mem_normalizer (hHP hg))
    · exact conjSubgroup_eq_iff_mem_normalizer.mp
        (conjSubgroup_sqSub_of_mem_normalizer (hRP hg))
  have hP2 : ∀ p ∈ P, p ^ 2 = 1 := sqSub_eq_bot_iff.mp hsq_eq_bot
  have hPe : ElemAb2 P := ⟨comm_of_sq_eq_one hP2, hP2⟩
  have hOmega : omegaOneCenterOf (thompsonJ R) ≤ Q := by
    rw [(omegaOne_centralizer_thompsonJ R).2]
    exact iInf₂_le Q hQmax
  have hPB : P ≤ B := by
    intro p hp
    rw [hBdef]
    refine ⟨hPR hp, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact (hPe.1 z (hQP (hOmega hz)) p hp)
  refine ⟨le_antisymm ?_ hQP, hPe⟩
  intro p hp
  rw [h.Q_eq]
  exact ⟨hPB hp, Subgroup.mem_centralizer_iff.mpr fun u hu => hPU p hp u hu⟩

theorem rank1_main [Finite G] {R H M₀ K P : Subgroup G} {x : G}
    (hC : NoCommonNormal R H M₀) (hBdef : B = baum R) (hq2 : 2 ≤ q)
    (hxR : x ∈ normalizer (R : Set G)) (hxx : x * x ∈ R) (hx1 : ¬ conjSubgroup U x ≤ Q)
    (hx2 : ¬ conjSubgroup U x⁻¹ ≤ Q) (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hUK : U ≤ K)
    (hKQ : K ≤ normalizer (Q : Set G))
    (hZ : (U ⊓ centralizer (K : Set G)).relIndex U = q ^ 2)
    (hgen : ∀ y : G, y ∈ normalizer (B : Set G) → ¬ conjSubgroup U y ≤ Q →
      ¬ conjSubgroup U y⁻¹ ≤ Q →
      ∃ k ∈ K, K ≤ conjSubgroup U y ⊔ conjSubgroup (conjSubgroup U y) k)
    (hRK : R ≤ normalizer (K : Set G)) (hRU : R ≤ normalizer (U : Set G))
    (hHKR : H ≤ K ⊔ R) (hM₀ : M₀ ≤ R ⊔ Subgroup.zpowers x)
    (hPR : P ≤ R) (hRP : R ≤ normalizer (P : Set G)) (hHP : H ≤ normalizer (P : Set G))
    (hUP : U ≤ P) (hQP : Q ≤ P) (hPU : ∀ p ∈ P, ∀ u ∈ U, u * p = p * u)
    (hCRU : R ⊓ centralizer (U : Set G) ≤ P)
    (hSC : ∀ r ∈ R, (∀ b ∈ B, ⁅r, b⁆ ∈ P) → r ∈ B ⊔ P) :
    Q = U ⊔ (Q ⊓ centralizer (K : Set G)) ∧ ElemAb2 (Q ⊓ centralizer (K : Set G)) ∧
      (Q ⊓ centralizer (K : Set G)) ⊓ conjSubgroup (Q ⊓ centralizer (K : Set G)) x = ⊥ ∧
      P = Q ∧ ElemAb2 Q ∧ IsMaxElemAbelian R Q ∧
      (∀ A, IsMaxElemAbelian R A ↔ A = Q ∨ A = conjSubgroup Q x) ∧
      conjSubgroup Q x = (Q ⊓ centralizer (K : Set G)) ⊔ conjSubgroup U x ∧
      thompsonJ R = B ∧ B = Q ⊔ conjSubgroup Q x ∧
      R ⊓ centralizer (K : Set G) = Q ⊓ centralizer (K : Set G) := by
  have hBR : B ≤ R := hBdef ▸ inf_le_left
  have hxB : x ∈ normalizer (B : Set G) := by
    rw [hBdef]; exact normalizer_le_normalizer_baum R hxR
  have hRB : R ≤ normalizer (B : Set G) := by
    rw [hBdef]; exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)
  have hRQ : R ≤ normalizer (Q : Set G) := by
    intro r hr
    rw [h.Q_eq]
    exact mem_normalizer_inf (hRB hr) (mem_normalizer_centralizer (hRU hr))
  have hA : ∀ A, IsMaxElemAbelian R A → A ≤ B := fun A hA =>
    hBdef ▸ ((le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ R).trans (thompsonJ_le_baum' R))
  set D := Q ⊓ centralizer (K : Set G) with hDdef
  have hDc : ∀ u ∈ U, ∀ a ∈ D, u * a = a * u := fun u hu a ha =>
    Subgroup.mem_centralizer_iff.mp ha.2 u (hUK hu)
  have hxinv : x⁻¹ ∈ normalizer (B : Set G) := inv_mem hxB
  have hx1' : ¬ conjSubgroup U x⁻¹⁻¹ ≤ Q := by rw [inv_inv]; exact hx1
  obtain ⟨hD, hDx⟩ := h.Q_eq_sup_centralizer hxB hx1 hUK hKQ hZ (hgen x hxB hx1 hx2)
  obtain ⟨-, hDx'⟩ := h.Q_eq_sup_centralizer hxinv hx2 hUK hKQ hZ (hgen x⁻¹ hxinv hx2 hx1')
  have hsq : sqSub D = ⊥ := h.sqSub_centralizer_eq_bot hC hBR hRQ hRK hHKR hM₀ hU2 hUK hxB hx1 hx2 hD
  have hD2 : ElemAb2 D := ⟨comm_of_sq_eq_one (sqSub_eq_bot_iff.mp hsq), sqSub_eq_bot_iff.mp hsq⟩
  have hDD := h.inf_conj_centralizer_eq_bot hC hBR hRQ hRK hxR hxx hHKR hM₀
  obtain ⟨hQmax, hQxmax, hQxeq, hall, hBeq, hJ⟩ :=
    h.A_R_structure hBR hA hq2 hU2 hxB hx1 hx2 hD hDc hD2 hDx
  obtain ⟨hPQ, hPe⟩ := h.P_eq_Q hC hBdef hQmax hBR hPR hxR hxB hx1 hx2 hU2 hD hDc hDx hDx' hRU
    hRP hHP hUP hQP hPU hSC hM₀
  refine ⟨hD, hD2, hDD, hPQ, hPQ ▸ hPe, hQmax, hall, hQxeq, hJ, hBeq, ?_⟩
  refine le_antisymm ?_ (inf_le_inf_right _ (h.Q_le_B.trans hBR))
  intro c hc
  refine ⟨?_, hc.2⟩
  rw [← hPQ]
  exact hCRU ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun u hu =>
    Subgroup.mem_centralizer_iff.mp hc.2 u (hUK hu)⟩

end Rank1

end CFSG.QuasithinUnique.C5
