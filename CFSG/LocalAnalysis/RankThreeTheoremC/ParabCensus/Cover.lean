module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxSylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

theorem le_normalizer_of_commutator_le {Γ : Type*} [Group Γ] {H N : Subgroup Γ} (hNH : N ≤ H)
    (h : ⁅H, H⁆ ≤ N) : H ≤ normalizer (N : Set Γ) := by
  have hconj : ∀ {x y : Γ}, x ∈ H → y ∈ N → x * y * x⁻¹ ∈ N := by
    intro x y hx hy
    have hc : ⁅x, y⁆ ∈ N := h (Subgroup.commutator_mem_commutator hx (hNH hy))
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem hc hy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact hconj hg
  · intro hn
    have h1 : g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ ∈ N := hconj (H.inv_mem hg) hn
    rwa [show g⁻¹ * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n by group] at h1

theorem not_two_dvd_relIndex_pi {k : ℕ} {G : Fin k → Type} [∀ j, Group (G j)]
    [∀ j, Finite (G j)] {S T : ∀ j, Subgroup (G j)} (hST : ∀ j, S j ≤ T j)
    {Λ : Subgroup (∀ j, G j)} (h1 : Subgroup.pi Set.univ S ≤ Λ)
    (h2 : Λ ≤ Subgroup.pi Set.univ T) (h : ∀ j, ¬ 2 ∣ (S j).relIndex (T j)) :
    ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex Λ := by
  classical
  have hSTpi : Subgroup.pi Set.univ S ≤ Subgroup.pi Set.univ T := by
    intro x hx
    rw [Subgroup.mem_pi] at hx ⊢
    exact fun j hj => hST j (hx j hj)
  have hidx : (Subgroup.pi Set.univ S).index =
      (∏ j, (S j).relIndex (T j)) * (Subgroup.pi Set.univ T).index := by
    rw [CFSG.SignalizerFunctorTheorem.McBride.Near.index_pi_dep,
      CFSG.SignalizerFunctorTheorem.McBride.Near.index_pi_dep, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => (Subgroup.relIndex_mul_index (hST j)).symm
  have hrel : (Subgroup.pi Set.univ S).relIndex (Subgroup.pi Set.univ T) =
      ∏ j, (S j).relIndex (T j) := by
    have hpos : (0 : ℕ) < (Subgroup.pi Set.univ T).index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := Subgroup.pi Set.univ T))
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [Subgroup.relIndex_mul_index hSTpi, hidx]
  have hodd : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex (Subgroup.pi Set.univ T) := by
    rw [hrel]
    exact (Nat.Prime.prime Nat.prime_two).not_dvd_finsetProd fun j _ => h j
  intro hdiv
  have hdvd : (Subgroup.pi Set.univ S).relIndex Λ ∣
      (Subgroup.pi Set.univ S).relIndex (Subgroup.pi Set.univ T) :=
    ⟨Λ.relIndex (Subgroup.pi Set.univ T),
      (Subgroup.relIndex_mul_relIndex _ _ _ h1 h2).symm⟩
  exact hodd (hdiv.trans hdvd)

theorem hasLeviCensus_of_cover {X C : Type} [Group X] [Group C] [Finite C] {L J : Subgroup X}
    (hJL : J ≤ L) (ρ : C →* ↥L) (hρ : Function.Surjective ρ) (hc : ρ.ker ≤ center C)
    (ho : Odd (Nat.card ρ.ker)) {B : (X : Type) → [Group X] → Prop} {k : ℕ} {G : Fin k → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range) (hS : ∀ j, S j = ⊥ ∨ B ↥(S j))
    (hZ : ∀ j, ¬ CFSG.Open.IsQuasisimple ↥(S j) → ∀ z : ↥((J.subgroupOf L).comap ρ),
      ρ z = 1 → β z ∈ (S j).map (MonoidHom.mulSingle G j) → β z = 1) :
    HasLeviCensus ↥J B := by
  classical
  let Q : Subgroup C := (J.subgroupOf L).comap ρ
  let σ : ↥Q →* ↥J :=
    (Subgroup.subgroupOfEquivOfLe hJL).toMonoidHom.comp
      ((ρ.domRestrict Q).codRestrict (J.subgroupOf L) fun c => c.2)
  have hσcoe : ∀ c : ↥Q, ((σ c : ↥J) : X) = (ρ (c : C) : X) := by
    intro c
    change (((Subgroup.subgroupOfEquivOfLe hJL)
      (((ρ.domRestrict Q).codRestrict (J.subgroupOf L) fun c => c.2) c) : X)) =
        (ρ (c : C) : X)
    exact Subgroup.subgroupOfEquivOfLe_apply_coe hJL _
  have hσ : Function.Surjective σ := by
    intro j
    let jL : ↥L := ⟨(j : X), hJL j.2⟩
    obtain ⟨c, hc⟩ := hρ jL
    have hcQ : c ∈ Q := by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [hc]
      exact j.2
    refine ⟨⟨c, hcQ⟩, Subtype.ext ?_⟩
    rw [hσcoe]
    exact congrArg Subtype.val hc
  have hσker_coe : ∀ z : ↥Q, z ∈ σ.ker → ρ (z : C) = 1 := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    refine Subtype.ext ?_
    rw [← hσcoe z, hz]
    rfl
  have hσker : σ.ker ≤ center ↥Q := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hzC : (z : C) ∈ center C := hc (hσker_coe z hz)
    exact Subtype.ext (Subgroup.mem_center_iff.mp hzC (w : C))
  have hker_le : ρ.ker ≤ Q := by
    intro c hc'
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [MonoidHom.mem_ker] at hc'
    rw [hc']
    exact J.one_mem
  have hkerEq : σ.ker = (ρ.ker).subgroupOf Q := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun hz => hσker_coe z (by rwa [MonoidHom.mem_ker]),
      fun hz => by
        apply Subtype.ext
        rw [hσcoe]
        simpa using congrArg Subtype.val hz⟩
  have hcard : Nat.card σ.ker = Nat.card ρ.ker := by
    rw [hkerEq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv
  refine ⟨↥Q, inferInstance, inferInstance, σ, k, G, inferInstance, inferInstance, S, β,
    hσ, hσker, ?_, hβ, hle, hn, hi, hS, ?_⟩
  · rw [hcard]
    exact ho
  · intro j hj z hz hβz
    exact hZ j hj z (hσker_coe z hz) hβz

theorem hasLeviCensus_of_mulEquiv {X C : Type} [Group X] [Group C] [Finite C] {L J : Subgroup X}
    (hJL : J ≤ L) (ρ : C ≃* ↥L) {B : (X : Type) → [Group X] → Prop} {k : ℕ} {G : Fin k → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)}
    (β : ↥((J.subgroupOf L).comap ρ.toMonoidHom) →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (hle : Subgroup.pi Set.univ S ≤ β.range)
    (hn : β.range ≤ normalizer (Subgroup.pi Set.univ S : Set (∀ j, G j)))
    (hi : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex β.range) (hS : ∀ j, S j = ⊥ ∨ B ↥(S j)) :
    HasLeviCensus ↥J B := by
  classical
  have hker : ρ.toMonoidHom.ker = ⊥ :=
    MonoidHom.ker_eq_bot_iff ρ.toMonoidHom |>.mpr ρ.injective
  refine hasLeviCensus_of_cover hJL ρ.toMonoidHom ρ.surjective ?_ ?_ β hβ hle hn hi hS ?_
  · rw [hker]
    exact bot_le
  · rw [hker]
    simpa using (show Odd (1 : ℕ) by norm_num)
  · intro j _ z hz _
    have hz1 : ρ (z : C) = 1 := hz
    have hz_eq : (z : C) = 1 := ρ.injective (by simpa using hz1)
    rw [show z = 1 from Subtype.ext hz_eq, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
