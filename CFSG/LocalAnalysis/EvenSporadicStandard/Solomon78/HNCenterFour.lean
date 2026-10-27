module

public import CFSG.Sporadic.HNOddCore.FourPairA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenterInputs
public import Certificates.Certificate25670
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Closing
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.Sporadic.HNOddCore Equiv

theorem eq_one_of_central_of_transitive {K : Type*} [Group K] {n : ℕ} (ρ : K →* Perm (Fin n))
    {i₀ : Fin n} {S : Set K} (hS : ∀ s ∈ S, ρ s i₀ = i₀)
    (hfix : ∀ k : Fin n, (∀ s ∈ S, ρ s k = k) → k = i₀)
    (htrans : ∀ j : Fin n, ∃ g : K, ρ g i₀ = j) {z : K} (hz : ∀ y : K, z * y = y * z) :
    ρ z = 1 := by
  have h0 : ρ z i₀ = i₀ := hfix _ fun s hs => by
    have h := congrArg (fun w => ρ w i₀) (hz s)
    simp only [map_mul, Perm.mul_apply, hS s hs] at h
    exact h.symm
  refine Equiv.ext fun j => ?_
  obtain ⟨g, rfl⟩ := htrans j
  have h := congrArg (fun w => ρ w i₀) (hz g)
  simp only [map_mul, Perm.mul_apply, h0] at h
  exact h

theorem hnFixCheck_spec (h : hnFixCheck = true) {k : ℕ} (hk : k < 800) :
    k = 0 ↔ ∀ s < 9, (InvData.s4Perms[s]!)[k]! = k := by
  unfold hnFixCheck at h
  have h1 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [beq_iff_eq] at h1
  have hA : ((List.range 9).all fun s => (InvData.s4Perms[s]!)[k]! == k) = true ↔
      ∀ s < 9, (InvData.s4Perms[s]!)[k]! = k := by
    rw [List.all_eq_true]
    exact ⟨fun h s hs => beq_iff_eq.1 (h s (List.mem_range.2 hs)),
      fun h s hs => beq_iff_eq.2 (h s (List.mem_range.1 hs))⟩
  rw [← hA, ← h1]
  exact beq_iff_eq.symm

theorem rho4_g4
    {s : ℕ} (hs : s < 10) {x : JH}
    (hx : x ∈ Subgroup.centralizer {t4J}) (hxs : x = g4 s) (k : Fin 800) :
    ((rho4 ⟨jR x, jR_mem_C4 hx⟩ k : Fin 800) : ℕ) = (InvData.s4Perms[s]!)[(k : ℕ)]! := by
  subst hxs
  have e : (⟨jR (g4 s), jR_mem_C4 hx⟩ : C4) = gC4 ⟨s, by omega⟩ :=
    Subtype.ext (by simp [gC4, gC, hs])
  rw [e]
  exact (prep_rho_gC ⟨s, by omega⟩ k).symm

theorem rho4_transitive
    (j : Fin 800) :
    ∃ g : JH, ∃ hg : g ∈ Subgroup.centralizer {t4J}, rho4 ⟨jR g, jR_mem_C4 hg⟩ 0 = j := by
  have hx : jR t4J • hF4.pt ((finCongr f4_size).symm j) = hF4.pt ((finCongr f4_size).symm j) :=
    (fix_t4 _).2 ⟨_, rfl⟩
  have hx' : hF4.pt ((finCongr f4_size).symm j) ∈ MulAction.orbit S4 x0 := by
    rw [orbit_S4]
    exact hx
  obtain ⟨⟨g, hgS⟩, hg⟩ := hx'
  refine ⟨g, S4_le hgS, ?_⟩
  apply (finCongr f4_size).symm.injective
  apply hF4.pt_injective
  rw [pt_rho4, x0_eq_pt]
  show jR g • x0 = _
  rw [jR_smul]
  exact hg

theorem centerInvAt_t4J :
    CenterInvAt t4J := by
  intro z _ hzc
  have hspec := fun {k : ℕ} (hk : k < 800) =>
    hnFixCheck_spec Certificates.certificate25670 hk
  let ι : Subgroup.centralizer ({t4J} : Set JH) →* C4 :=
    (jR.comp (Subgroup.centralizer ({t4J} : Set JH)).subtype).codRestrict C4
      (fun g => jR_mem_C4 g.2)
  let z' : Subgroup.centralizer ({t4J} : Set JH) :=
    ⟨z, Subgroup.mem_centralizer_singleton_iff.2 (hzc t4J rfl)⟩
  have key : (rho4.comp ι) z' = 1 := by
    refine eq_one_of_central_of_transitive (rho4.comp ι) (i₀ := 0)
      (S := {x | ∃ s : Fin 9, (x : JH) = g4 s}) ?_ ?_ ?_ ?_
    · rintro x ⟨s, hs⟩
      refine Fin.ext ?_
      have h1 := rho4_g4 (by omega : (s : ℕ) < 10) x.2 hs 0
      have h2 := (hspec (by norm_num : 0 < 800)).1 rfl s s.2
      exact h1.trans h2
    · intro k hk
      refine Fin.ext ((hspec k.2).2 fun s hs => ?_)
      have hx : g4 s ∈ Subgroup.centralizer ({t4J} : Set JH) :=
        g4_mem s (by omega)
      have h1 := rho4_g4 (by omega : s < 10) hx rfl k
      have h2 := hk ⟨g4 s, hx⟩ ⟨⟨s, hs⟩, rfl⟩
      exact h1.symm.trans (congrArg Fin.val h2)
    · intro j
      obtain ⟨g, hg, h⟩ := rho4_transitive j
      exact ⟨⟨g, hg⟩, h⟩
    · intro y
      exact Subtype.ext (hzc y (Subgroup.mem_centralizer_singleton_iff.1 y.2))
  have h1 : ι z' ∈ rho4.ker := key
  rw [ker_rho4, Subgroup.mem_zpowers_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have hn2 : t4C ^ (n % 2) = ι z' := by
    have h := zpow_mod_orderOf t4C n
    rw [orderOf_t4C, Nat.cast_ofNat] at h
    rw [← hn]
    exact h
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [h, zpow_zero] at hn2
    exact jR_injective ((congrArg Subtype.val hn2).symm.trans (map_one jR).symm)
  · right
    rw [h, zpow_one] at hn2
    exact jR_injective (congrArg Subtype.val hn2).symm

end CFSG.EvenSporadicStandard.Solomon78
