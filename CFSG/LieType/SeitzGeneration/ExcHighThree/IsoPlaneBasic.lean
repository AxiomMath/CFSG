module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_le_card_eq_pow_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {k : ℕ} (hk : p ^ k ≤ Nat.card A) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = p ^ k := by
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hA.isPGroup hk
  refine ⟨H.map A.subtype, Subgroup.map_subtype_le H, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective, hH]

theorem exists_plane_mem_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) (h : p ^ 2 ≤ Nat.card A) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = p ^ 2 ∧ a ∈ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by
    have := pow_pos hp.pos 2
    omega)
  have hord : orderOf a = p := orderOf_eq_prime (hA.2 a haA) ha1
  have hcardz : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  obtain ⟨m, hm⟩ := hA.isPGroup.exists_card_eq
  have hdvd : p ^ 2 ∣ Nat.card A := by
    rw [hm] at h ⊢
    exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).1 h)
  obtain ⟨E, hEcard, hzE, hEA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 2)
    (H := Subgroup.zpowers a) (L := A)
    (by rw [hcardz]; exact dvd_pow_self p two_ne_zero) hdvd
    (Subgroup.zpowers_le.mpr haA)
  exact ⟨E, hEA, hEcard, hzE (Subgroup.mem_zpowers a)⟩

theorem exists_plane_not_le_of_isElemAbelian {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) (h : p ^ 2 ≤ Nat.card A) {H : Subgroup G} (hAH : ¬ A ≤ H) :
    ∃ E : Subgroup G, E ≤ A ∧ Nat.card E = p ^ 2 ∧ ¬ E ≤ H := by
  obtain ⟨a, haA, haH⟩ := Set.not_subset.1 hAH
  have ha1 : a ≠ 1 := fun h1 => haH (h1 ▸ H.one_mem)
  obtain ⟨E, hEA, hEc, haE⟩ := exists_plane_mem_of_isElemAbelian hp hA h haA ha1
  exact ⟨E, hEA, hEc, fun hEH => haH (hEH haE)⟩

open CFSG.LieType.SeitzGeneration

theorem three_ne_p_of_card_mod_three_eq_one {q : TauCeti.PrimePower} (hq : q.card % 3 = 1) :
    3 ≠ q.p := by
  intro h
  have h3 : 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, ← h]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  omega

theorem three_ne_p_of_card_mod_three_eq_two {q : TauCeti.PrimePower} (hq : q.card % 3 = 2) :
    3 ≠ q.p := by
  intro h
  have h3 : 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, ← h]
    exact dvd_pow_self 3 q.exponent_pos.ne'
  omega

theorem exists_plane_of_map_congr {C P : Type*} [Group C] [Group P] (e : C ≃* P) {p : ℕ}
    {Ē : Subgroup (MulAut C)} {En : Subgroup (MulAut P)}
    (hle : En ≤ Ē.map (MulAut.congr e).toMonoidHom) (hel : IsElemAbelian p En)
    (hcard : Nat.card En = p ^ 2) (hgen : PlaneGen En) :
    ∃ E : Subgroup (MulAut C), E ≤ Ē ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧ PlaneGen E := by
  set φ : MulAut C →* MulAut P := (MulAut.congr e).toMonoidHom with hφdef
  have hφ : Function.Injective φ := (MulAut.congr e).injective
  have hφs : Function.Surjective φ := (MulAut.congr e).surjective
  have hmap : (En.comap φ).map φ = En := Subgroup.map_comap_eq_self_of_surjective hφs En
  refine ⟨En.comap φ, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    obtain ⟨y, hy, hyψ⟩ := hle hψ
    rwa [← hφ hyψ]
  · refine ⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun x hx => hφ ?_⟩
    · have h1 := congrArg Subtype.val (hel.1.is_comm.comm ⟨φ a, a.2⟩ ⟨φ b, b.2⟩)
      simpa using h1
    · rw [map_pow, map_one]
      exact hel.2 _ hx
  · rw [← Subgroup.card_map_of_injective (K := En.comap φ) hφ, hmap]
    exact hcard
  · exact (planeGen_map_congr e (En.comap φ)).mp (by rwa [hmap])

theorem planeGen_map_conj_of_planeCl {C N : Type*} [Group C] [Group N] (e : C ≃* N)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {E₀ : Subgroup C}
    (htop : planeCl (E₀.map e.toMonoidHom) = ⊤) :
    PlaneGen (E₀.map (MulAut.conj : C →* MulAut C)) := by
  set T : Set C := {k | ∃ c ∈ E₀, c ≠ 1 ∧ Commute k c} with hT
  have himage : e.toMonoidHom '' T =
      {k : N | ∃ x ∈ E₀.map e.toMonoidHom, x ≠ 1 ∧ Commute k x} := by
    ext k
    constructor
    · rintro ⟨k₀, ⟨c, hc, hc1, hkc⟩, rfl⟩
      exact ⟨e c, ⟨c, hc, rfl⟩, fun h => hc1 (e.injective (h.trans (map_one e).symm)),
        hkc.map e.toMonoidHom⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hx1, hkx⟩
      refine ⟨e.symm k, ⟨c, hc, fun h => hx1 (by rw [h]; exact map_one e.toMonoidHom), ?_⟩, ?_⟩
      · have := hkx.map e.symm.toMonoidHom
        simpa using this
      · simp
  have hTtop : Subgroup.closure T = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e.toMonoidHom k ∈
        Subgroup.closure {k : N | ∃ x ∈ E₀.map e.toMonoidHom, x ≠ 1 ∧ Commute k x} := by
      rw [show Subgroup.closure {k : N | ∃ x ∈ E₀.map e.toMonoidHom, x ≠ 1 ∧ Commute k x} = ⊤
        from htop]
      exact Subgroup.mem_top _
    rw [← himage, ← MonoidHom.map_closure] at hk
    obtain ⟨k₀, hk₀, hk₀e⟩ := hk
    have : k₀ = k := e.injective hk₀e
    rw [← this]
    exact hk₀
  have hle : Subgroup.closure T ≤ planeClosure (E₀.map (MulAut.conj : C →* MulAut C)) := by
    rw [Subgroup.closure_le]
    rintro k ⟨c, hc, hc1, hkc⟩
    refine Subgroup.subset_closure ⟨MulAut.conj c, ⟨c, hc, rfl⟩, fun h => hc1 ?_, ?_⟩
    · exact hinj (h.trans (map_one _).symm)
    · rw [MulAut.conj_apply, ← hkc.eq]
      group
  rw [PlaneGen, eq_top_iff, ← hTtop]
  exact hle

end CFSG.LieType.SeitzGeneration.ExcHighThree
