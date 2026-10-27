module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_2

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G] [Finite G]

theorem delta_inf_centralizer_le_of_commutator {p : ℕ} (hp : p.Prime) {D : Subgroup G} {x : G}
    (hDx : D ≤ Subgroup.centralizer ({x} : Set G)) (hD : IsElemAbelian p D) (hD1 : D ≠ ⊥)
    (hJ : ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({x} : Set G)) J →
      ⁅GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G), J⁆ ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G))) :
    GLADelta p D ⊓ Subgroup.centralizer ({x} : Set G) ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer ({x} : Set G) with hH
  set S : Subgroup G := GLADelta p D ⊓ H with hS
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥H) with hπ
  have hO : GLAPPrimeCore p (↥H ⧸ GLAPPrimeCore p ↥H) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hH1 : CFSG.HardMathSupport.Timmesfeld.Balance.H1Stmt.{0} := by
    intro X Z _ _ _ φ hφ p hp Q hQ
    exact CFSG.HardMathSupport.Timmesfeld.Proving.map_glaPPrimeCoreOf_centralizer_le φ hφ hp hQ
  obtain ⟨e₀, he₀D, he₀1⟩ : ∃ e ∈ D, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hD1 ((Subgroup.eq_bot_iff_forall D).2 hcon)
  have he₀H : e₀ ∈ H := hDx he₀D
  set e : ↥H := ⟨e₀, he₀H⟩ with he
  have hene : e ≠ 1 := fun h => he₀1 (congrArg Subtype.val h)
  have hcore : ∀ y ∈ S, y ∈ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e₀} : Set G)) := by
    intro y hy
    obtain ⟨hyΔ, hyH⟩ := Subgroup.mem_inf.1 hy
    have hye : y ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({e₀} : Set G)) := by
      simp only [GLADelta, Subgroup.mem_iInf] at hyΔ
      exact hyΔ e₀ he₀D he₀1
    have hyCe : y ∈ Subgroup.centralizer ({e₀} : Set G) := Subgroup.map_subtype_le _ hye
    exact inf_glaPPrimeCoreOf_le (H := H ⊓ Subgroup.centralizer ({e₀} : Set G))
      (A := Subgroup.centralizer ({e₀} : Set G)) hp inf_le_right
      (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyH, hyCe⟩, hye⟩)
  have hSbar : barX p H S = ⊥ := by
    refine CFSG.HardMathSupport.Timmesfeld.Balance.eq_bot_of_centralizes_pCore_of_centralizes_components_p
      hp hO ?_ ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      have hs' : (s : G) ∈ S := (Subgroup.mem_subgroupOf).1 hs
      have hcop : (orderOf (s : G)).Coprime p :=
        CFSG.HardMathSupport.Timmesfeld.Proving.orderOf_coprime_of_mem_GLAPPrimeCoreOf hp
          (hcore _ hs')
      rw [Subgroup.orderOf_coe] at hcop
      exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd π s) hcop
    · rintro _ ⟨s, hs, rfl⟩
      have hs' : (s : G) ∈ S := (Subgroup.mem_subgroupOf).1 hs
      have hmem := CFSG.HardMathSupport.Timmesfeld.Balance.mk_mem_centralizer_core hH1 hp
        (hDx) hD (e := e) he₀D hene (x := s) (hcore _ hs')
      have hpe : (π e) ^ p = 1 := by
        rw [← map_pow]
        have : e ^ p = 1 := Subtype.ext (by simpa using hD.2 e₀ he₀D)
        rw [this, map_one]
      have hQ : IsPGroup p (Subgroup.zpowers (π e)) :=
        CFSG.HardMathSupport.Timmesfeld.Balance.isPGroup_zpowers_of_pow_eq_one hp hpe
      have hc := CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCoreOf_centralizer_le_centralizer_pCore
        hp hQ hmem
      exact hc
    · intro L hL
      obtain ⟨J, hJc, rfl⟩ := exists_glaPComponent_barX_eq (p := p) H
        ((CFSG.isComponent_iff_open L).1 hL)
      refine barX_le_centralizer (fun s hs t ht _ _ => ?_)
      exact hJ J hJc (Subgroup.commutator_mem_commutator hs ht)
  intro y hy
  have hyH : y ∈ H := (Subgroup.mem_inf.1 hy).2
  have hmem : π ⟨y, hyH⟩ ∈ barX p H S := ⟨⟨y, hyH⟩, (Subgroup.mem_subgroupOf).2 hy, rfl⟩
  rw [hSbar, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

theorem input19_2_4Pos_holds :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      IsKProper G → ∀ p : ℕ, p.Prime → ∀ B : Subgroup G, IsElemAbelian p B → ∀ k : ℕ, 1 ≤ k →
        (∀ D : Subgroup G, IsEkIn p k B D → ∀ b ∈ B, b ≠ 1 → ∀ J : Subgroup G,
          GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J →
            ⁅GLADelta p D ⊓ Subgroup.centralizer ({b} : Set G), J⁆ ≤
              GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) →
        IsBalancedWrt p k B := by
  intro G _ _ _ _ _ p hp B hB k hk hcomm D hD x hx hx1
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card D = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 := hD.2.2
    rw [h1] at h2
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  exact delta_inf_centralizer_le_of_commutator hp (hD.1.trans (i192_le_centralizer hB hx)) hD.2.1
    hD1 (hcomm D hD x hx hx1)

end CFSG.HardMathSupport.Solomon.Coordinator
