module

public import CFSG.CGT.PushingUpLit.T2K.SixA

public section

namespace CFSG.CGT.PushingUpLit.T2K

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure IsD (L M D : Subgroup G) : Prop where
  le_Q : D ≤ QOf L M
  exists_g : ∃ g : G, g ∉ M ∧ D ≤ (QOf L M).map (MulAut.conj g).toMonoidHom
  maximal : ∀ D' : Subgroup G, D ≤ D' → D' ≤ QOf L M →
    (∃ g : G, g ∉ M ∧ D' ≤ (QOf L M).map (MulAut.conj g).toMonoidHom) → D' = D

namespace T2Hyp

variable {L M T : Subgroup G} {n : ℕ}

theorem exists_isD (h : T2Hyp G L M n) : ∃ D : Subgroup G, IsD L M D := by
  obtain ⟨g₀, hg₀⟩ : ∃ g : G, g ∉ M := by
    by_contra hcon
    push Not at hcon
    exact h.M_ne_top (eq_top_iff.2 fun x _ => hcon x)
  let 𝔇 : Set (Subgroup G) := {D' | D' ≤ QOf L M ∧
    ∃ g : G, g ∉ M ∧ D' ≤ (QOf L M).map (MulAut.conj g).toMonoidHom}
  obtain ⟨D, hD, hmax⟩ := Set.exists_max_image 𝔇 (fun D' => Nat.card ↥D') (Set.toFinite _)
    ⟨⊥, bot_le, g₀, hg₀, bot_le⟩
  refine ⟨D, hD.1, hD.2, fun D' hle hD'Q hD'g => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle (hmax D' ⟨hD'Q, hD'g⟩)).symm

end T2Hyp

namespace IsD

variable {L M D T : Subgroup G} {n : ℕ}

theorem lt_Q (hs : Sec6 G L M T n) (hD : IsD L M D) : D < QOf L M := by
  refine lt_of_le_of_ne hD.le_Q fun heq => ?_
  obtain ⟨g, hgM, hg⟩ := hD.exists_g
  rw [heq] at hg
  apply hgM
  have : (QOf L M).map (MulAut.conj g).toMonoidHom = QOf L M :=
    (Subgroup.eq_of_le_of_card_ge hg (by rw [card_map_conj])).symm
  rw [← hs.N_Q]
  exact mem_normalizer_of_map_conj_eq this

omit [Finite G] in
theorem ti (hD : IsD L M D) {x : G} (hx : x ∈ Subgroup.centralizer (D : Set G)) (hxM : x ∉ M) :
    QOf L M ⊓ (QOf L M).map (MulAut.conj x).toMonoidHom = D := by
  have hle : D ≤ QOf L M ⊓ (QOf L M).map (MulAut.conj x).toMonoidHom := by
    intro d hd
    refine ⟨hD.le_Q hd, (mem_map_conj_iff x _ d).2 ?_⟩
    have : x⁻¹ * d * x = d := by
      have h1 := Subgroup.mem_centralizer_iff.1 hx d hd
      calc x⁻¹ * d * x = x⁻¹ * (d * x) := by group
        _ = x⁻¹ * (x * d) := by rw [← h1]
        _ = d := by group
    rw [this]
    exact hD.le_Q hd
  exact hD.maximal _ hle inf_le_left ⟨x, hxM, inf_le_right⟩

end IsD

namespace T2Hyp

variable {L M T D : Subgroup G} {n : ℕ}

theorem two_le_M (hs : Sec6 G L M T n) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hQS : QOf L M ≤ S) : S ≤ M := by
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isPGroup hs.sec4.sylowG hS le_top
  have hQk : (QOf L M).map (MulAut.conj k).toMonoidHom ≤ T :=
    (Subgroup.map_mono hQS).trans hk
  have hkM : k ∈ M := by
    rw [← hs.N_Q]
    exact mem_normalizer_of_map_conj_eq (hs.Q_wc k hQk)
  intro s hs'
  have h1 : k * s * k⁻¹ ∈ T := hk ⟨s, hs', by simp [MulAut.conj_apply]⟩
  have h2 : k * s * k⁻¹ ∈ M := hs.sec4.sylow.le h1
  have e : s = k⁻¹ * (k * s * k⁻¹) * k := by group
  rw [e]
  exact M.mul_mem (M.mul_mem (M.inv_mem hkM) h2) hkM

end T2Hyp

structure Sit64 (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G)
    (g : G) : Prop where
  sec6 : Sec6 G L M T n
  isD : IsD L M D
  D_lt_Q : D < QOf L M
  ti : ∀ x : G, x ∈ Subgroup.centralizer (D : Set G) → x ∉ M →
    QOf L M ⊓ (QOf L M).map (MulAut.conj x).toMonoidHom = D
  two_le_M : ∀ S : Subgroup G, IsPGroup 2 S → QOf L M ≤ S → S ≤ M
  g_mem : g ∈ Subgroup.centralizer (D : Set G)
  g_not_M : g ∉ M
  D_lt : D < (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M

@[expose] def Print64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L M T : Subgroup G) (n : ℕ) (D : Subgroup G),
    Sec6 G L M T n → IsD L M D →
    ∃ g : G, g ∈ Subgroup.centralizer (D : Set G) ∧ g ∉ M ∧
      D < (QOf L M).map (MulAut.conj g).toMonoidHom ⊓ M

namespace T2Hyp

variable {L M T D : Subgroup G} {n : ℕ}

theorem sit64 (h64 : Print64) (hs : Sec6 G L M T n) (hD : IsD L M D) :
    ∃ g : G, Sit64 G L M T n D g := by
  obtain ⟨g, hg, hgM, hlt⟩ := h64 G L M T n D hs hD
  exact ⟨g, hs, hD, hD.lt_Q hs, fun x hx hxM => hD.ti hx hxM,
    fun S hS hQS => two_le_M hs hS hQS, hg, hgM, hlt⟩

end T2Hyp

end CFSG.CGT.PushingUpLit.T2K
