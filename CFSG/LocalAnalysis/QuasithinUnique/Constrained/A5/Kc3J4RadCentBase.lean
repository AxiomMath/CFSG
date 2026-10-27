
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4RadGlobBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Core
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Q

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4
open scoped commutatorElement

theorem d5Plus_of_d5Core {G : Type} [Group G] {L : Subgroup G} (h : D5Core L) : D5Plus L := by
  obtain ⟨V, hVL, hV2, hLV, α, hα, hαV, β, hβ⟩ := h
  refine ⟨V, V, le_rfl, hVL, hV2, hLV, hLV, ?_, α, hα, hαV, β, hβ⟩
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) v⁻¹).1 (V.inv_mem hv)
  have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact V.mul_mem hv h1

theorem pCoreOf_abelian_of_d5Core {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : D5Core L) : ∀ a ∈ pCoreOf 2 L, ∀ b ∈ pCoreOf 2 L, a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVL, hV2, hLV, α, hα, hαV, β, hβ⟩ := h
  have hPV : pCoreOf 2 L = V := by
    apply le_antisymm
    · exact le_Q_of_normal_two α hα hαV (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hLV hV2
  rw [hPV]
  intro a ha b hb
  have h : β ⟨a, ha⟩ * β ⟨b, hb⟩ = β ⟨b, hb⟩ * β ⟨a, ha⟩ := mul_comm _ _
  have h' : (⟨a, ha⟩ : ↥V) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ :=
    β.injective (by rw [map_mul, map_mul]; exact h)
  exact congrArg Subtype.val h'

theorem conj_mem_centralizer_of_normalizer {X : Type*} [Group X] {Q : Subgroup X} {n u : X}
    (hn : n ∈ Subgroup.normalizer (Q : Set X)) (hu : u ∈ Subgroup.centralizer (Q : Set X)) :
    n * u * n⁻¹ ∈ Subgroup.centralizer (Q : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hw' : n⁻¹ * w * n ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) w).1 hw
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hu _ hw'
  calc w * (n * u * n⁻¹) = n * ((n⁻¹ * w * n) * u) * n⁻¹ := by group
    _ = n * (u * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
    _ = (n * u * n⁻¹) * w := by group

theorem normalizer_le_normalizer_centralizer {X : Type*} [Group X] (Q : Subgroup X) :
    Subgroup.normalizer (Q : Set X) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set X) : Subgroup X) : Set X) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨fun hu => conj_mem_centralizer_of_normalizer hn hu, fun hu => ?_⟩
  have := conj_mem_centralizer_of_normalizer (inv_mem hn) hu
  simpa [mul_assoc] using this

theorem centralizer_le_normalizer_set {X : Type*} [Group X] (Q : Subgroup X) :
    Subgroup.centralizer (Q : Set X) ≤ Subgroup.normalizer (Q : Set X) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have hcv : ∀ w ∈ Q, c * w * c⁻¹ = w := by
    intro w hw
    have := Subgroup.mem_centralizer_iff.1 hc w hw
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  constructor
  · intro hv
    rw [hcv v hv]
    exact hv
  · intro hv
    have hw := Subgroup.mem_centralizer_iff.1 (inv_mem hc) (c * v * c⁻¹) hv
    have h3 : v = c * v * c⁻¹ := by
      calc v = c⁻¹ * (c * v * c⁻¹) * c := by group
        _ = (c * v * c⁻¹) * c⁻¹ * c := by rw [← hw]
        _ = c * v * c⁻¹ := by group
    rw [h3]
    exact hv

theorem blockRad_conditions_of_centralizer {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : D5Plus L) (hno : ¬ ∃ y : X, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l)
    (hU : IsPGroup 2 (Subgroup.centralizer (pCoreOf 2 L : Set X)))
    (hg : ∃ g ∈ L, orderOf g = 5 ∧
      16 < (Subgroup.centralizer (pCoreOf 2 L : Set X) ⊓
        Subgroup.centralizer ({g} : Set X)).relIndex
          (Subgroup.centralizer (pCoreOf 2 L : Set X))) :
    Subgroup.centralizer (blockRadAbs L : Set X) ≤ blockRadAbs L ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (blockRadAbs L ⊓ Subgroup.centralizer ({g} : Set X)).relIndex (blockRadAbs L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : D5Core L := by
    rcases d5Core_or_central_of_d5Plus hL with h | ⟨z, -, hz2, hzc⟩
    · exact h
    · exact absurd ⟨z, hz2, hzc⟩ hno
  have hab := pCoreOf_abelian_of_d5Core hcore
  have hQU : pCoreOf 2 L ≤ Subgroup.centralizer (pCoreOf 2 L : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hab b hb a ha
  have hUR : Subgroup.centralizer (pCoreOf 2 L : Set X) ≤ blockRadAbs L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (centralizer_le_normalizer_set _)
      (normalizer_le_normalizer_centralizer _) hU
  have hQR : pCoreOf 2 L ≤ blockRadAbs L := hQU.trans hUR
  refine ⟨fun c hc => hUR (Subgroup.centralizer_le (fun x hx => hQR hx) hc), ?_⟩
  obtain ⟨g, hgL, hg5, hg16⟩ := hg
  exact ⟨g, hgL, hg5, lt_of_lt_of_le hg16 (relIndex_inf_mono hUR g)⟩

@[expose] def J4GlobalRadC : Prop :=
  ∀ L : Subgroup ↥J, D5Plus L → ⁅L, L⁆ = L →
    (∀ g : ↥J, ¬ L ≤ Hj.map (MulAut.conj g).toMonoidHom) →
    (¬ ∃ y : ↥J, orderOf y = 2 ∧ ∀ l ∈ L, l * y = y * l) →
    IsPGroup 2 (Subgroup.centralizer (pCoreOf 2 L : Set ↥J)) ∧
      ∃ g ∈ L, orderOf g = 5 ∧
        16 < (Subgroup.centralizer (pCoreOf 2 L : Set ↥J) ⊓
          Subgroup.centralizer ({g} : Set ↥J)).relIndex
            (Subgroup.centralizer (pCoreOf 2 L : Set ↥J))

theorem j4GlobalRad_of_globalRadC (h : J4GlobalRadC) : J4GlobalRad := by
  intro L hL hLp hnH hno
  obtain ⟨hU, hg⟩ := h L hL hLp hnH hno
  exact blockRad_conditions_of_centralizer (X := ↥J) hL hno hU hg

end CFSG.QuasithinUnique.A5
