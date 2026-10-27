module

public import CFSG.GH74.Uniqueness.SU.SU10Orb
public import CFSG.GH74.Uniqueness.SU.SU10Ctrl
public import CFSG.GH74.Uniqueness.SU.SU10Z

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8

variable {G : Type} [Group G]

theorem mem_normalizer_of_map_eq {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    have : x = y := (MulAut.conj g).injective hxy
    rwa [← this]

theorem map_conj_eq_of_mem {S : Subgroup G} {s : G} (hs : s ∈ S) :
    S.map (MulAut.conj s).toMonoidHom = S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem hs hy) (S.inv_mem hs)
  · intro hx
    refine ⟨s⁻¹ * x * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs, ?_⟩
    show s * (s⁻¹ * x * s) * s⁻¹ = x
    group

theorem le_normalizer_omegaOne (S : Subgroup G) :
    S ≤ normalizer ((omegaOne S : Subgroup G) : Set G) := by
  intro s hs
  apply mem_normalizer_of_map_eq
  rw [← omegaOne_map (MulAut.conj s) S, map_conj_eq_of_mem hs]

section Finite

variable [Finite G]

omit [Finite G] in
theorem odd_ncard_conj_orbit {N S : Subgroup G} {z : G}
    (hSC : S ≤ centralizer ({z} : Set G)) (hodd : Odd (S.relIndex N)) :
    Odd ({y : G | ∃ n ∈ N, n * z * n⁻¹ = y} : Set G).ncard := by
  let _ : MulAction N G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (g : N) (y : G), g • y = (g : G) * y * (g : G)⁻¹ := fun g y =>
    ConjAct.smul_def (g : G) y
  have hstab : MulAction.stabilizer N z = (centralizer ({z} : Set G)).subgroupOf N := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg (fun t => t * (g : G)) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      simp
  have horbit : ({y : G | ∃ n ∈ N, n * z * n⁻¹ = y} : Set G) = MulAction.orbit N z := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hsmul ⟨n, hn⟩ z⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, (hsmul g z).symm⟩
  rw [horbit, ← MulAction.index_stabilizer, hstab]
  have hdvd : ((centralizer ({z} : Set G)).subgroupOf N).index ∣ (S.subgroupOf N).index := by
    refine Subgroup.index_dvd_of_le ?_
    intro s hs
    exact Subgroup.mem_subgroupOf.mpr (hSC (Subgroup.mem_subgroupOf.mp hs))
  exact Odd.of_dvd_nat hodd hdvd

theorem exists_mem_normalizer_conj_omegaOne (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {z : G} (hz2 : orderOf z = 2)
    (hzmem : z ∈ (S : Subgroup G)) (hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * a = 1 → b * b = 1 →
      a * b = b * a)
    {m : ℕ} {y : G} (hm : 1 ≤ m) (hcard : Nat.card (omegaOne (S : Subgroup G)) = 2 ^ (m + 1))
    (hyN : y ∈ normalizer ((omegaOne (S : Subgroup G) : Subgroup G) : Set G))
    (hyz : y * z = z * y)
    (htrans : ∀ a ∈ omegaOne (S : Subgroup G), ∀ b ∈ omegaOne (S : Subgroup G), a ≠ 1 → a ≠ z →
      b ≠ 1 → b ≠ z →
      ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b ∨ y ^ j * a * (y ^ j)⁻¹ = b * z) :
    ∀ a ∈ omegaOne (S : Subgroup G), a ≠ 1 →
      ∃ n ∈ normalizer ((omegaOne (S : Subgroup G) : Subgroup G) : Set G), n * z * n⁻¹ = a := by
  classical
  set A : Subgroup G := omegaOne (S : Subgroup G) with hA
  set N : Subgroup G := normalizer (A : Set G) with hN
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzA : z ∈ A := Subgroup.subset_closure ⟨hzmem, hzz⟩
  set W : Set G := {y : G | ∃ n ∈ N, n * z * n⁻¹ = y} with hW
  have hWA : W ⊆ (A : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hn z).mp hzA
  have hW1 : (1 : G) ∉ W := by
    rintro ⟨n, hn, h⟩
    apply hz1
    calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  have hwW : z ∈ W := ⟨1, N.one_mem, by group⟩
  have hWne : ∃ u ∈ W, u ≠ z := by
    obtain ⟨g, hgne, hgS⟩ := exists_conj_mem_sylow_ne hs hn S hz2 hzS
    have hu2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [hzz]; group
    have huA : g * z * g⁻¹ ∈ A := Subgroup.subset_closure ⟨hgS, hu2⟩
    obtain ⟨n, hnN, hnz⟩ := exists_mem_normalizer_omegaOne S hcomm hzA huA rfl
    exact ⟨g * z * g⁻¹, ⟨n, hnN, hnz⟩, hgne⟩
  have hWy : ∀ a ∈ W, ∀ j : ℤ, y ^ j * a * (y ^ j)⁻¹ ∈ W := by
    rintro _ ⟨n, hn, rfl⟩ j
    refine ⟨y ^ j * n, N.mul_mem (Subgroup.zpow_mem N hyN j) hn, ?_⟩
    group
  have hSN : (S : Subgroup G) ≤ N := le_normalizer_omegaOne _
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzS s hs')
  have hodd : Odd ((S : Subgroup G).relIndex N) := by
    have hdvd : (S : Subgroup G).relIndex N ∣ (S : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le hSN
    exact Nat.not_even_iff_odd.mp fun hev =>
      S.not_dvd_index (dvd_trans (even_iff_two_dvd.mp hev) hdvd)
  have hWodd : Odd W.ncard := odd_ncard_conj_orbit hSC hodd
  intro a ha ha1
  exact eq_of_odd_card hm hcard hzA hz1 hzz hyz htrans W hWA hW1 hwW hWne hWy hWodd a ha ha1

end Finite

end CFSG.GH74.Uniqueness.SU.SU10
