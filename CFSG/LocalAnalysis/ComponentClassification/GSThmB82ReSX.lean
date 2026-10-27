module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Inst

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conj_mem_of_inf_le {S₀ T L : Subgroup X} (hST : S₀ ≤ T)
    (hSL : S₀ ≤ normalizer (L : Set X)) (hTL : T ⊓ L ≤ S₀) {τ : X} (hτL : τ ∈ L)
    (hτT : τ ∈ normalizer (T : Set X)) {s : X} (hs : s ∈ S₀) : τ * s * τ⁻¹ ∈ S₀ := by
  have h1 : τ * s * τ⁻¹ * s⁻¹ ∈ T :=
    mul_mem ((mem_normalizer_iff.mp hτT s).mp (hST hs)) (inv_mem (hST hs))
  have h2 : τ * s * τ⁻¹ * s⁻¹ ∈ L := by
    have h3 : s * τ⁻¹ * s⁻¹ ∈ L := (mem_normalizer_iff.mp (hSL hs) τ⁻¹).mp (inv_mem hτL)
    rw [show τ * s * τ⁻¹ * s⁻¹ = τ * (s * τ⁻¹ * s⁻¹) by group]
    exact mul_mem hτL h3
  rw [show τ * s * τ⁻¹ = τ * s * τ⁻¹ * s⁻¹ * s by group]
  exact mul_mem (hTL (mem_inf.mpr ⟨h1, h2⟩)) hs

omit [Finite X] in
theorem mem_normalizer_of_inf_le {S₀ T L : Subgroup X} (hST : S₀ ≤ T)
    (hSL : S₀ ≤ normalizer (L : Set X)) (hTL : T ⊓ L ≤ S₀) {τ : X} (hτL : τ ∈ L)
    (hτT : τ ∈ normalizer (T : Set X)) : τ ∈ normalizer (S₀ : Set X) := by
  rw [mem_normalizer_iff]
  intro s
  refine ⟨conj_mem_of_inf_le hST hSL hTL hτL hτT, fun hs => ?_⟩
  have h1 := conj_mem_of_inf_le hST hSL hTL (inv_mem hτL) (inv_mem hτT) hs
  rwa [show τ⁻¹ * (τ * s * τ⁻¹) * τ⁻¹⁻¹ = s by group] at h1

namespace Seven

omit [Finite X] in
theorem IsSylowIn.eq_of_le_of_isPGroup {R Q N : Subgroup X} (hR : IsSylowIn R N)
    (hQN : Q ≤ N) (hQ2 : IsPGroup 2 Q) (hRQ : R ≤ Q) : Q = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRN, R', hR'⟩ := hR
  have hle : (R' : Subgroup ↥N) ≤ Q.subgroupOf N := by
    rw [hR']
    exact fun w hw => mem_subgroupOf.mpr (hRQ (mem_subgroupOf.mp hw))
  have h1 : Q.subgroupOf N = (R' : Subgroup ↥N) := R'.is_maximal' hQ2.comap_subtype hle
  rw [hR', subgroupOf_inj, inf_eq_left.mpr hQN, inf_eq_left.mpr hRN] at h1
  exact h1

theorem E_le_sup_secB0 {h : Hyp52 X} {y : X} (h61 : h.Lemma61Shape y) :
    E h y ≤ zpowers h.a ⊔ h.secB0 y := by
  refine sup_le le_sup_left ?_
  rcases h61 with h1 | ⟨b, -, -, -, hbB0, -, hle, -⟩
  · rw [h1]
    exact le_sup_left
  · refine hle.trans ((closure_le _).mpr ?_)
    rintro w (rfl | rfl)
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right hbB0

theorem Lay_le_centralizer_secB0 (h : Hyp52 X) (y : X) :
    Lay h y ≤ centralizer (h.secB0 y : Set X) :=
  map_subtype_le _

theorem secG0_le_normalizer_Lay (h : Hyp52 X) (y : X) :
    h.secG0 y ≤ normalizer (Lay h y : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  have hC : g ∈ normalizer (centralizer (B0 h y : Set X) : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    rw [mem_centralizer_iff, mem_centralizer_iff]
    constructor
    · intro hx c hc
      have hc' : g⁻¹ * c * g⁻¹⁻¹ ∈ B0 h y := (mem_normalizer_iff.mp (inv_mem hg) c).mp hc
      rw [inv_inv] at hc'
      have h1 := hx _ hc'
      calc c * (g * x * g⁻¹) = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * c := by group
    · intro hx c hc
      have hc' : g * c * g⁻¹ ∈ B0 h y := (mem_normalizer_iff.mp hg c).mp hc
      have h1 := hx _ hc'
      calc c * x = g⁻¹ * ((g * c * g⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (g * c * g⁻¹)) * g := by rw [h1]
        _ = x * c := by group
  have : (pLayer ↥(centralizer (B0 h y : Set X)) 2).Characteristic :=
    CatalogueBPrimeJoin.pLayer_characteristic
  exact UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ hC

end Seven

namespace Hyp52

@[reducible, expose] def reChooseSX (h h' : Hyp52 X) (ha : h'.a = h.a) (hJ : h'.J = h.J)
    (hB : h'.B = h.B) : Hyp52 X :=
  { h with
    S := h'.S
    x := h'.x
    S_le := by rw [← ha, ← hJ]; exact h'.S_le
    S_sylow := by rw [← ha, ← hJ]; exact h'.S_sylow
    B_le := by rw [← hB, ← hJ]; exact h'.B_le
    isoCorr_of_lt := by rw [← ha, ← hJ, ← hB]; exact h'.isoCorr_of_lt
    x_mem := h'.x_mem
    inf_conjugate_x := by rw [← hB]; exact h'.inf_conjugate_x
    x_sq_mem := by rw [← hJ, ← hB]; exact h'.x_sq_mem
    sylow_layer := by rw [← hJ, ← hB]; exact h'.sylow_layer }

section ReChooseSX

variable {h hr : Hyp52 X} {ha : hr.a = h.a} {hJ : hr.J = h.J} {hB : hr.B = h.B}

theorem reChooseSX_P_of_le {y : X} (hS0 : h.S ⊓ h.secG0 y ≤ hr.S) :
    h.P ⊓ h.secG0 y ≤ (h.reChooseSX hr ha hJ hB).P := fun w hw => by
  obtain ⟨hwP, hwG⟩ := mem_inf.mp hw
  exact mem_inf.mpr ⟨hS0 (mem_inf.mpr ⟨(mem_inf.mp hwP).1, hwG⟩), (mem_inf.mp hwP).2⟩

theorem mem_P_of_reChooseSX {w : X} (hwS : w ∈ h.S)
    (hwP : w ∈ (h.reChooseSX hr ha hJ hB).P) : w ∈ h.P :=
  mem_inf.mpr ⟨hwS, (mem_inf.mp hwP).2⟩

end ReChooseSX

theorem inf_Lay_le_of_reChoice {h : Hyp52 X} {y : X} {S' : Subgroup X}
    (hS0E : h.S ⊓ normalizer (h.secB0 y : Set X) ≤ centralizer (Seven.E h y : Set X))
    (hS0syl : ∃ R : Sylow 2 ↥(normalizer (h.secB0 y : Set X) ⊓
        centralizer (Seven.E h y : Set X)),
      (R : Subgroup _) = (h.S ⊓ normalizer (h.secB0 y : Set X)).subgroupOf
        (normalizer (h.secB0 y : Set X) ⊓ centralizer (Seven.E h y : Set X)))
    (h61 : h.Lemma61Shape y) (hS'a : S' ≤ centralizer ({h.a} : Set X))
    (hS'2 : IsPGroup 2 S') (hS0S' : h.S ⊓ h.secG0 y ≤ S') :
    S' ⊓ Seven.Lay h y ≤ h.S ⊓ h.secG0 y := by
  set M := normalizer (h.secB0 y : Set X) ⊓ centralizer (Seven.E h y : Set X) with hM
  set N := Seven.Lay h y ⊓ centralizer ({h.a} : Set X) with hN
  have haE : h.a ∈ Seven.E h y := mem_sup_left (mem_zpowers _)
  have hNM : N ≤ M := by
    intro w hw
    obtain ⟨hwL, hwa⟩ := mem_inf.mp hw
    have hwB : w ∈ centralizer (h.secB0 y : Set X) := Seven.Lay_le_centralizer_secB0 h y hwL
    refine mem_inf.mpr ⟨centralizer_le_normalizer _ hwB, ?_⟩
    have hle : zpowers h.a ⊔ h.secB0 y ≤ centralizer ({w} : Set X) := by
      refine sup_le ?_ fun b hb => mem_centralizer_singleton_iff.mpr
        ((mem_centralizer_iff.mp hwB) b hb)
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hwa).symm
    rw [mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.mp (hle (Seven.E_le_sup_secB0 h61 he))
  have hMN : M ≤ normalizer (N : Set X) := by
    intro m hm
    obtain ⟨hmG, hmE⟩ := mem_inf.mp hm
    have hma : m ∈ centralizer ({h.a} : Set X) :=
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hmE) h.a haE).symm
    exact Seven.mem_normalizer_inf (Seven.secG0_le_normalizer_Lay h y hmG) (le_normalizer hma)
  have hSyl : Seven.IsSylowIn (h.S ⊓ normalizer (h.secB0 y : Set X) ⊓ N) N :=
    Seven.IsSylowIn.inf_of_le_normalizer ⟨le_inf inf_le_right hS0E, hS0syl⟩ hNM hMN
  have heq : S' ⊓ N = h.S ⊓ normalizer (h.secB0 y : Set X) ⊓ N :=
    hSyl.eq_of_le_of_isPGroup inf_le_right (hS'2.to_le inf_le_left) (inf_le_inf_right N hS0S')
  intro w hw
  obtain ⟨hwS', hwL⟩ := mem_inf.mp hw
  have hwN : w ∈ S' ⊓ N := mem_inf.mpr ⟨hwS', mem_inf.mpr ⟨hwL, hS'a hwS'⟩⟩
  rw [heq] at hwN
  exact (mem_inf.mp hwN).1

theorem mem_normalizer_S0_of_reChoice {h : Hyp52 X} {y : X} {S' : Subgroup X}
    (hS0S' : h.S ⊓ h.secG0 y ≤ S') (hTL : S' ⊓ Seven.Lay h y ≤ h.S ⊓ h.secG0 y) {τ : X}
    (hτL : τ ∈ Seven.Lay h y)
    (hτT : τ ∈ normalizer ((S' ⊓ h.secG0 y : Subgroup X) : Set X)) :
    τ ∈ normalizer ((h.S ⊓ h.secG0 y : Subgroup X) : Set X) :=
  mem_normalizer_of_inf_le (le_inf hS0S' inf_le_right)
    (inf_le_right.trans (Seven.secG0_le_normalizer_Lay h y))
    (fun _ hw => hTL (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hw).1).1, (mem_inf.mp hw).2⟩))
    hτL hτT

theorem mul_self_mem_S0_of_reChoice {h : Hyp52 X} {y : X} {S' : Subgroup X}
    (hTL : S' ⊓ Seven.Lay h y ≤ h.S ⊓ h.secG0 y) {τ : X} (hτL : τ ∈ Seven.Lay h y)
    (hτ2 : τ * τ ∈ S') : τ * τ ∈ h.S ⊓ h.secG0 y :=
  hTL (mem_inf.mpr ⟨hτ2, mul_mem hτL hτL⟩)

end Hyp52

end CFSG.ComponentClassification.GSThmB
