module

public import CFSG.CGT.PushingUpLit.SolK.Cfg
public import CFSG.CGT.PushingUpLit.SolK.Local

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem W_ne_bot : S.D.W ≠ ⊥ := by
  intro hbot
  have hn : 2 ≤ n := S.hyp.two_le
  let a : Fin (2 * n + 1) := ⟨0, by omega⟩
  let b : Fin (2 * n + 1) := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  let w : ↥S.D.W := S.D.β.symm (pairVec a b)
  have hw1 : (w : G) = 1 := by
    have : (w : G) ∈ (⊥ : Subgroup G) := hbot ▸ w.2
    exact Subgroup.mem_bot.1 this
  have hw : w = 1 := Subtype.ext hw1
  have h1 : pairVec a b = 1 := by
    have := congrArg S.D.β hw
    rwa [MulEquiv.apply_symm_apply, map_one] at this
  have h2 := congrArg (fun v => vcoord v a) h1
  simp only [vcoord_pairVec, vcoord_one] at h2
  simp [hab] at h2

theorem normalizer_Q_eq : Subgroup.normalizer (pCoreOf 2 M : Set G) = M := by
  have hM : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => pCoreOf_normalized M hm hq, fun hq => ?_⟩
    have h1 := pCoreOf_normalized M (M.inv_mem hm) hq
    have e : m⁻¹ * (m * q * m⁻¹) * (m⁻¹)⁻¹ = q := by group
    rwa [e] at h1
  have hne : pCoreOf 2 M ≠ ⊥ := by
    intro hbot
    apply S.W_ne_bot
    exact le_bot_iff.1 (hbot ▸ S.W_le_Q)
  have hloc : IsPLocal 2 (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hne, isPGroup_pCoreOf' M, rfl⟩
  by_contra hne'
  exact S.hyp.maxLocal.2 _ (lt_of_le_of_ne hM (Ne.symm hne')) hloc

theorem centralizer_le_M (hchar : IsCharTwoType G)
    (hQab : ∀ q ∈ pCoreOf 2 M, ∀ q' ∈ pCoreOf 2 M, q * q' = q' * q) {B : Subgroup G}
    (hBQ : B ≤ pCoreOf 2 M) (hB : B ≠ ⊥)
    (hO2 : pCoreOf 2 (M ⊓ Subgroup.centralizer (B : Set G)) ≤ pCoreOf 2 M) :
    pCoreOf 2 (Subgroup.centralizer (B : Set G)) = pCoreOf 2 M ∧
      Subgroup.normalizer (B : Set G) ≤ M := by
  classical
  set Q : Subgroup G := pCoreOf 2 M with hQ
  set K : Subgroup G := Subgroup.centralizer (B : Set G) with hK
  set K1 : Subgroup G := M ⊓ K with hK1
  set P : Subgroup G := pCoreOf 2 K with hP
  have hB2 : IsPGroup 2 B := isPGroup_of_le (isPGroup_pCoreOf' M) hBQ
  have hQ2 : IsPGroup 2 Q := isPGroup_pCoreOf' M
  have hP2 : IsPGroup 2 P := isPGroup_pCoreOf' K
  have hQK : Q ≤ K := fun q hq => Subgroup.mem_centralizer_iff.2 fun b hb => hQab b (hBQ hb) q hq
  have hQM : Q ≤ M := pCoreOf_le_self M
  have hQK1 : Q ≤ K1 := le_inf hQM hQK
  have hQnorm : ∀ k ∈ K1, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
    pCoreOf_normalized M hk.1 hq
  have hQ1 : pCoreOf 2 K1 = Q := le_antisymm hO2
    (le_pCoreOf_of_normalized hQK1 hQnorm hQ2)
  have hPnormK : ∀ k ∈ K, ∀ p ∈ P, k * p * k⁻¹ ∈ P := fun k hk p hp => pCoreOf_normalized K hk hp
  have hQNP : Q ≤ Subgroup.normalizer (P : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hPnormK q (hQK hq) p hp, fun hp => ?_⟩
    have := hPnormK q⁻¹ (K.inv_mem (hQK hq)) _ hp
    simpa [mul_assoc] using this
  have hT2 : IsPGroup 2 (P ⊔ Q : Subgroup G) := hP2.to_sup_of_normal_left' hQ2 hQNP
  have hTK : P ⊔ Q ≤ K := sup_le (pCoreOf_le_self K) hQK
  have hTnorm : ∀ k ∈ K1, ∀ t ∈ P ⊔ Q, k * t * k⁻¹ ∈ P ⊔ Q := by
    intro k hk t ht
    have hle : (P ⊔ Q).map (MulAut.conj k).toMonoidHom ≤ P ⊔ Q := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨z, hz, rfl⟩
        exact hPnormK k hk.2 z hz
      · rintro _ ⟨z, hz, rfl⟩
        exact hQnorm k hk z hz
    exact hle ⟨t, ht, rfl⟩
  have hNQ : (P ⊔ Q) ⊓ Subgroup.normalizer (Q : Set G) ≤ Q := by
    have hnormM := S.normalizer_Q_eq
    intro g hg
    have hgM : g ∈ M := by rw [← hnormM]; exact hg.2
    have hle : (P ⊔ Q) ⊓ M ≤ pCoreOf 2 K1 := by
      refine le_pCoreOf_of_normalized (fun t ht => ⟨ht.2, hTK ht.1⟩) (fun k hk z hz => ?_)
        (isPGroup_of_le hT2 inf_le_left)
      exact Subgroup.mem_inf.2 ⟨hTnorm k hk z hz.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk.1
        hz.2) (M.inv_mem hk.1)⟩
    exact hQ1.le (hle ⟨hg.1, hgM⟩)
  have hPQ : P ≤ Q := by
    by_contra hnot
    have hne : Q ≠ P ⊔ Q := by
      intro heq
      apply hnot
      rw [heq]
      exact le_sup_left
    obtain ⟨t, htT, htQ, htN⟩ := exists_mem_normalizer_of_lt hT2 le_sup_right hne
    exact htQ (hNQ ⟨htT, htN⟩)
  have hPeq : P = Q := by
    refine le_antisymm hPQ ?_
    have hcen : Q ≤ K ⊓ Subgroup.centralizer (P : Set G) :=
      le_inf hQK (fun q hq => Subgroup.mem_centralizer_iff.2 fun p hp => hQab p (hPQ hp) q hq)
    exact (hcen.trans (centralizer_two_constrained hchar hB hB2 |> fun h => by
      intro x hx
      exact h hx))
  refine ⟨hPeq, ?_⟩
  intro n hn
  have hKnorm : ∀ n ∈ Subgroup.normalizer (B : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K :=
    fun n hn k hk => centralizer_normalized hn hk
  have hPn : ∀ n ∈ Subgroup.normalizer (B : Set G), ∀ p ∈ P, n * p * n⁻¹ ∈ P :=
    fun n hn p hp => pCoreOf_normalized_of_normal hKnorm hn hp
  have hnP : n ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    rw [← hPeq]
    refine ⟨fun hq => hPn n hn q hq, fun hq => ?_⟩
    have := hPn n⁻¹ ((Subgroup.normalizer (B : Set G)).inv_mem hn) _ hq
    simpa [mul_assoc] using this
  rw [← S.normalizer_Q_eq]
  exact hnP

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
