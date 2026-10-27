module

public import CFSG.GF2Type.Smith1979.W4O83Step1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4O83

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.Open
open CFSG.RankThree.Literature.FSmith (zmod2_cases)
open CFSG.RankThree.OrthogonalInvolutions (add_self_vec neg_vec_eq)

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem mem_Qa_iff' (g x : G) : x ∈ S.Qa g ↔ g⁻¹ * x * g ∈ S.QG := by
  rw [Setting.Qa_eq_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem Omega83Config.th_add_self_mem_plane (C : Omega83Config S) (i : Fin 4) (v : S.Qt) :
    C.th i v + v ∈ C.plane i := by
  have h1 : C.th i v + v = C.th i (C.prL i v) + C.prL i v := by
    conv_lhs => rw [← C.sum_prL v]
    rw [map_sum, ← Finset.sum_add_distrib, Finset.sum_eq_single i]
    · intro j _ hji
      rw [C.th_eq_of_ne (Ne.symm hji) (C.prL_mem_plane j v), add_self_vec (ZMod 2)]
    · simp
  rw [h1]
  exact add_mem (C.th_mem_plane (C.prL_mem_plane i v)) (C.prL_mem_plane i v)

theorem Omega83Config.exists_t (C : Omega83Config S) {g : G} (H : Hyp4 S g) (Cn : Cons311 S g)
    (hw : S.width = 4) (k : Fin 4) :
    ∃ t : G, t ∈ S.QG ∧ t ∈ S.Qa g ∧ t ^ 2 = 1 ∧ S.cl t ≠ 0 ∧ C.th k (S.cl t) = S.cl t := by
  set D : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa g) with hD
  have hdim : finrank (ZMod 2) D + 1 = 5 :=
    S.finrank_clSub_QG_inf_Qa H.conj_mem H.conj_ne (k := 5) (by rw [Cn.card_QG_inf_Qa, hw])
  let Φ : S.Qt →ₗ[ZMod 2] S.Qt := (C.th k : S.Qt →ₗ[ZMod 2] S.Qt) + LinearMap.id
  have hΦ : ∀ v, Φ v ∈ C.plane k := fun v => C.th_add_self_mem_plane k v
  let f : ↥D →ₗ[ZMod 2] ↥(C.plane k) := (Φ.comp D.subtype).codRestrict (C.plane k) (fun v => hΦ v)
  have hlt : finrank (ZMod 2) ↥(C.plane k) < finrank (ZMod 2) ↥D := by
    rw [C.finrank_plane k]
    omega
  have hker : LinearMap.ker f ≠ ⊥ := f.ker_ne_bot_of_finrank_lt hlt
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hfv : Φ (v : S.Qt) = 0 := by
    have h0 : f v = 0 := LinearMap.mem_ker.mp hv
    have h1 : ((f v : ↥(C.plane k)) : S.Qt) = Φ (v : S.Qt) := rfl
    rw [← h1, h0]
    rfl
  have hthv : C.th k (v : S.Qt) = v := by
    have h1 : C.th k (v : S.Qt) + v = 0 := by simpa [Φ] using hfv
    rw [eq_neg_of_add_eq_zero_left h1, neg_vec_eq (ZMod 2)]
  obtain ⟨t, htD, htQ, hct⟩ := S.mem_clSub_iff.mp v.2
  refine ⟨t, htQ, htD.2, S.QG_inf_Qa_sq H.conj_ne htD, ?_, ?_⟩
  · rw [hct]
    exact fun h => hv0 (Subtype.ext h)
  · rw [hct]
    exact hthv

theorem Omega83Config.exists_fixed_index (C : Omega83Config S)
    (hbase : ∀ g' : G, g' * S.z * g'⁻¹ ∈ S.QG → g' * S.z * g'⁻¹ ≠ S.z → Hyp4 S g') {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) {t : G} (htQ : t ∈ S.QG)
    (htQa : t ∈ S.Qa g) {k : Fin 4} (hk : C.th k (S.cl t) = S.cl t) (ht0 : S.cl t ≠ 0) :
    ∃ l : Fin 4, C.th l (S.cl (g⁻¹ * t * g)) = S.cl (g⁻¹ * t * g) := by
  by_contra hcon
  push Not at hcon
  have ht'Q : g⁻¹ * t * g ∈ S.QG := (mem_Qa_iff' g t).mp htQa
  obtain ⟨κ, hκ⟩ := C.exists_conj_of_full (hbase g haQ hne) ht'Q hcon
  have e : g * κ * S.z * (g * κ)⁻¹ = t := by
    calc g * κ * S.z * (g * κ)⁻¹ = g * (κ * S.z * κ⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [← hκ]
      _ = t := by group
  have htz : g * κ * S.z * (g * κ)⁻¹ ≠ S.z := by
    rw [e]
    intro h
    apply ht0
    rw [h, S.cl_z]
  have hQ : g * κ * S.z * (g * κ)⁻¹ ∈ S.QG := by
    rw [e]
    exact htQ
  have := C.th_ne_cl_conj_z (hbase (g * κ) hQ htz) k
  rw [e] at this
  exact this hk

theorem pCoreOf_facts (K : Subgroup G) :
    IsPGroup 2 (pCoreOf 2 K) ∧ pCoreOf 2 K ≤ K ∧
      ∀ k ∈ K, ∀ r ∈ pCoreOf 2 K, k * r * k⁻¹ ∈ pCoreOf 2 K := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  · rw [pCoreOf]
    exact Subgroup.map_subtype_le _
  · intro k hk r hr
    rw [pCoreOf] at hr ⊢
    obtain ⟨o', ho', rfl⟩ := hr
    exact ⟨⟨k, hk⟩ * o' * ⟨k, hk⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem zpow_eq_one_or_self {x : G} (hx2 : orderOf x = 2) (k : ℤ) : x ^ k = 1 ∨ x ^ k = x := by
  have h2 : ((orderOf x : ℕ) : ℤ) = 2 := by exact_mod_cast hx2
  have h := zpow_mod_orderOf x k
  rw [h2] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [← h, h0, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

theorem normalizer_zpowers_eq_centralizer {x : G} (hx2 : orderOf x = 2) :
    normalizer (zpowers x : Set G) = centralizer ({x} : Set G) := by
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx2
    omega
  ext g
  constructor
  · intro h
    rw [mem_centralizer_singleton_iff]
    have h1 : g * x * g⁻¹ ∈ zpowers x := (mem_normalizer_iff.mp h x).mp (mem_zpowers x)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    rcases zpow_eq_one_or_self hx2 k with h2 | h2
    · exfalso
      have hk' : g * x * g⁻¹ = 1 := by
        rw [h2] at hk
        exact hk.symm
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * 1 * g := by rw [hk']
        _ = 1 := by group
    · have hk' : g * x * g⁻¹ = x := by
        rw [h2] at hk
        exact hk.symm
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [hk']
  · intro h
    have hg : g ∈ centralizer ((zpowers x : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      have hcomm : Commute x g := (mem_centralizer_singleton_iff.mp h).symm
      exact (hcomm.zpow_left k).eq
    exact (centralizer_le_normalizer _) hg

theorem centralizer_pCoreOf_le (hchar : IsCharTwoType G) {x : G} (hx2 : orderOf x = 2) :
    ∀ y ∈ centralizer ({x} : Set G),
      (∀ r ∈ pCoreOf 2 (centralizer ({x} : Set G)), y * r = r * y) →
      y ∈ pCoreOf 2 (centralizer ({x} : Set G)) := by
  intro y hy hcomm
  have hloc : IsTwoLocal (centralizer ({x} : Set G)) := by
    refine ⟨zpowers x, ?_, ?_, (normalizer_zpowers_eq_centralizer hx2).symm⟩
    · intro hbot
      rw [zpowers_eq_bot] at hbot
      rw [hbot, orderOf_one] at hx2
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one])
  have hcent : y ∈ centralizer ((pCoreOf 2 (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact (hcomm h hh).symm
  exact hchar (centralizer ({x} : Set G)) hloc (mem_inf.mpr ⟨hy, hcent⟩)

theorem Omega83Config.step_one_conj (C : Omega83Config S) (hchar : IsCharTwoType G) {g t : G}
    (ht2 : orderOf t = 2) (ht'Q : g⁻¹ * t * g ∈ S.QG) {l : Fin 4}
    (hl : C.th l (S.cl (g⁻¹ * t * g)) = S.cl (g⁻¹ * t * g)) :
    ∀ y ∈ S.QG, S.cl y ∈ C.plane l → g * y * g⁻¹ ∈ pCoreOf 2 (centralizer ({t} : Set G)) := by
  obtain ⟨hU2, hUle, hUnorm⟩ := pCoreOf_facts (centralizer ({t} : Set G))
  set U : Subgroup G := pCoreOf 2 (centralizer ({t} : Set G)) with hU
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  have ht'2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by
          rw [pow_two, pow_two]
          group
      _ = 1 := by rw [ht2']; group
  have hconjC : ∀ h : G, h ∈ centralizer ({g⁻¹ * t * g} : Set G) →
      g * h * g⁻¹ ∈ centralizer ({t} : Set G) := by
    intro h hh
    rw [mem_centralizer_singleton_iff] at hh ⊢
    calc g * h * g⁻¹ * t = g * (h * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * h) * g⁻¹ := by rw [hh]
      _ = t * (g * h * g⁻¹) := by group
  have hstep := C.step_one ht'Q ht'2 hl (U' := U.comap (MulAut.conj g).toMonoidHom)
    (hU2.comap_of_injective _ (MulAut.conj g).injective)
    (fun h hh u hu => by
      have hu' : g * u * g⁻¹ ∈ U := hu
      have h1 := hUnorm _ (hconjC h hh) _ hu'
      change g * (h * u * h⁻¹) * g⁻¹ ∈ U
      have e : g * (h * u * h⁻¹) * g⁻¹ = (g * h * g⁻¹) * (g * u * g⁻¹) * (g * h * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact h1)
    (fun y hy hcomm => by
      have hy' : g * y * g⁻¹ ∈ centralizer ({t} : Set G) := hconjC y hy
      have := centralizer_pCoreOf_le hchar ht2 (g * y * g⁻¹) hy' (fun r hr => by
        have hr' : g⁻¹ * r * g ∈ U.comap (MulAut.conj g).toMonoidHom := by
          change g * (g⁻¹ * r * g) * g⁻¹ ∈ U
          have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
          rw [e]
          exact hr
        have h1 := hcomm _ hr'
        calc g * y * g⁻¹ * r = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by rw [h1]
          _ = r * (g * y * g⁻¹) := by group)
      exact this)
  exact hstep

end CFSG.GF2Type.Smith1979.W4O83
