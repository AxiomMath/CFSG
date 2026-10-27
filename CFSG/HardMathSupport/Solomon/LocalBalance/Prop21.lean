module

public import CFSG.HardMathSupport.Solomon.Coordinator.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma23Proof

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

@[expose] def Input19DeltaTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProper G → ∀ p : ℕ, p.Prime → 5 < p →
    ∀ B : Subgroup G, GLAIsBmax p B → ∀ H : Subgroup G, H ≠ ⊤ → B ≤ H →
      ∀ E : Subgroup G, E ≤ B → IsElemAbelian p E → Nat.card E = p ^ 2 →
        (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
            GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set G))) ≤ GLAPPrimeCoreOf p H

theorem gLAPPrimeCoreOf_inf_le [Finite G] {p : ℕ} (hp : p.Prime) (K H : Subgroup G) :
    GLAPPrimeCoreOf p K ⊓ H ≤ GLAPPrimeCoreOf p (K ⊓ H) := by
  rintro y ⟨hyK, hyH⟩
  let N : Subgroup ↥(K ⊓ H) := (GLAPPrimeCoreOf p K).comap (K ⊓ H).subtype
  have hN : N.Normal :=
    ⟨fun n hn g => by
      change ((g * n * g⁻¹ : ↥(K ⊓ H)) : G) ∈ GLAPPrimeCoreOf p K
      have := mem_gLAPPrimeCoreOf_conj (x := (n : G)) (h := (g : G)) hn g.2.1
      simpa using this⟩
  have hcop : Nat.Coprime p (Nat.card N) := by
    have hle : N.map (K ⊓ H).subtype ≤ GLAPPrimeCoreOf p K := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at h1
    have h2 : Nat.card (GLAPPrimeCoreOf p K) = Nat.card (GLAPPrimeCore p K) :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    exact (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp K).coprime_dvd_right
      (h2 ▸ h1)
  have hyK' : y ∈ K := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le p K hyK
  have hyN : (⟨y, ⟨hyK', hyH⟩⟩ : ↥(K ⊓ H)) ∈ N := hyK
  exact ⟨⟨y, ⟨hyK', hyH⟩⟩,
    le_sSup (show N ∈ {N : Subgroup ↥(K ⊓ H) | N.Normal ∧ Nat.Coprime p (Nat.card N)} from
      ⟨hN, hcop⟩) hyN, rfl⟩

omit [Group G] in
theorem centralizer_ne_top_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ∃ a b : G, a * b ≠ b * a) {x : G} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  have hx' : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({x} : Set G) := h ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 this x rfl).symm
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h1 | h1
  · exact hx (Subgroup.mem_bot.1 (h1 ▸ hx'))
  · obtain ⟨a, b, hab⟩ := hna
    exact hab (Subgroup.mem_center_iff.1 (h1 ▸ Subgroup.mem_top a) b).symm

theorem isBalancedWrt_of_localDelta [Finite G] {p k : ℕ} (hp : p.Prime) {B : Subgroup G}
    (hB : IsElemAbelian p B) (hnc : ∀ x : G, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≠ ⊤)
    (hin : ∀ H : Subgroup G, H ≠ ⊤ → B ≤ H → ∀ E : Subgroup G, E ≤ B → IsElemAbelian p E →
      Nat.card E = p ^ k →
        (⨅ (e : G) (_ : e ∈ E) (_ : e ≠ 1),
          GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({e} : Set G))) ≤ GLAPPrimeCoreOf p H) :
    IsBalancedWrt p k B := by
  intro D hD x hx hx1 y hy
  obtain ⟨hDB, hDel, hDcard⟩ := hD
  have hBH : B ≤ Subgroup.centralizer ({x} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun z hz => by
      rw [Set.mem_singleton_iff.1 hz]
      exact elemAbelian_comm hB hx hb
  refine hin _ (hnc x hx1) hBH D hDB hDel hDcard ?_
  simp only [Subgroup.mem_iInf]
  intro e he he1
  have h1 : y ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLADelta_le_GLAPPrimeCoreOf p he he1 hy.1
  have := gLAPPrimeCoreOf_inf_le hp (Subgroup.centralizer ({e} : Set G))
    (Subgroup.centralizer ({x} : Set G)) ⟨h1, hy.2⟩
  rwa [inf_comm] at this

theorem prop21_of_inputs (h3 : CFSG.LocalAnalysis.GLTheoremB.Input19Delta)
    (h2 : Input19DeltaTwo) : Prop21 := by
  intro G _ _ m p hS B hB
  have := hS.simple
  have hnc : ∀ x : G, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≠ ⊤ := fun x hx =>
    centralizer_ne_top_of_simple hS.nonabelian hx
  refine ⟨isBalancedWrt_of_localDelta hS.prime hB.1 hnc fun H hH hBH E hEB hE hcard =>
      h3 G hS.kProper p hS.prime hS.ne_two B hB H hH hBH E hEB hE hcard, fun hp5 => ?_⟩
  exact isBalancedWrt_of_localDelta hS.prime hB.1 hnc fun H hH hBH E hEB hE hcard =>
    h2 G hS.kProper p hS.prime hp5 B hB H hH hBH E hEB hE hcard

end CFSG.HardMathSupport.Solomon.LocalBalance
