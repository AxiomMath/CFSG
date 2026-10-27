module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open CFSG.RankThree.LocalRank

theorem le_center_iff_map_mulEquiv {H K : Type*} [Group H] [Group K] (ψ : H ≃* K)
    (S : Subgroup H) : S ≤ Subgroup.center H ↔ S.map ψ.toMonoidHom ≤ Subgroup.center K := by
  constructor
  · intro hS
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨h, rfl⟩ := ψ.surjective k
    have hc := Subgroup.mem_center_iff.mp (hS hs) h
    simpa [map_mul] using congrArg ψ hc
  · intro hT s hs
    rw [Subgroup.mem_center_iff]
    intro h
    have hm : ψ s ∈ S.map ψ.toMonoidHom := Subgroup.mem_map_of_mem _ hs
    have hc := Subgroup.mem_center_iff.mp (hT hm) (ψ h)
    apply ψ.injective
    simpa [map_mul] using hc

theorem props_map_mulEquiv {H K : Type*} [Group H] [Group K] (ψ : H ≃* K) {p : ℕ}
    (N : Subgroup H) (hn : N.Normal) (hs : Group.IsSolvable N) (hp : ¬p ∣ Nat.card N) :
    (N.map ψ.toMonoidHom).Normal ∧ Group.IsSolvable (N.map ψ.toMonoidHom) ∧
      ¬p ∣ Nat.card (N.map ψ.toMonoidHom) := by
  refine ⟨hn.map ψ.toMonoidHom ψ.surjective, ?_, ?_⟩
  · exact Group.isSolvable_of_surjective (f := (ψ.subgroupMap N).toMonoidHom)
      (ψ.subgroupMap N).surjective
  · have hcard : Nat.card (N.map ψ.toMonoidHom) = Nat.card N :=
      Nat.card_congr (ψ.subgroupMap N).toEquiv.symm
    rw [hcard]
    exact hp

theorem aschbacherSolvableCore_map_mulEquiv {H K : Type*} [Group H] [Group K] [Finite H]
    {p : ℕ} (hp : p.Prime) (ψ : H ≃* K) :
    aschbacherSolvableCore p K = (aschbacherSolvableCore p H).map ψ.toMonoidHom := by
  have : Finite K := Finite.of_equiv H ψ.toEquiv
  obtain ⟨_, _, _, _, ⟨hmemH, hupH⟩, _, _⟩ :=
    solvable_prime_complement_core_characterization hp (H := H)
  obtain ⟨_, _, _, _, _, hunique, _⟩ :=
    solvable_prime_complement_core_characterization hp (H := K)
  refine (hunique _ ⟨?_, ?_⟩).symm
  · exact props_map_mulEquiv ψ _ hmemH.1 hmemH.2.1 hmemH.2.2
  · intro N hN
    obtain ⟨hn, hs, hp'⟩ := hN
    have hN' := props_map_mulEquiv ψ.symm N hn hs hp'
    have hle : N.map ψ.symm.toMonoidHom ≤ aschbacherSolvableCore p H := hupH hN'
    intro x hx
    exact Subgroup.mem_map.mpr ⟨ψ.symm x, hle (Subgroup.mem_map_of_mem ψ.symm.toMonoidHom hx),
      by simp⟩

theorem map_centralizer_singleton_eq {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (b : X) :
    (Subgroup.centralizer ({b} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e b} : Set Y) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hxb := hx b (Set.mem_singleton b)
    simpa [map_mul] using congrArg e hxb
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    apply e.injective
    have hyb := hy (e h) (Set.mem_singleton _)
    simpa [map_mul] using hyb

theorem aschbacherSolvableCore_three_centralizer_iff {X Y : Type*} [Group X] [Group Y] [Finite X]
    (e : X ≃* Y) (b : X) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) ≤
        Subgroup.center (Subgroup.centralizer ({b} : Set X)) ↔
      aschbacherSolvableCore 3 (Subgroup.centralizer ({e b} : Set Y)) ≤
        Subgroup.center (Subgroup.centralizer ({e b} : Set Y)) := by
  let ψ : Subgroup.centralizer ({b} : Set X) ≃*
      Subgroup.centralizer ({e b} : Set Y) :=
    (e.subgroupMap (Subgroup.centralizer ({b} : Set X))).trans
      (MulEquiv.subgroupCongr (map_centralizer_singleton_eq e b))
  have hnat := aschbacherSolvableCore_map_mulEquiv (H := Subgroup.centralizer ({b} : Set X))
    (K := Subgroup.centralizer ({e b} : Set Y)) Nat.prime_three ψ
  rw [le_center_iff_map_mulEquiv ψ, ← hnat]
