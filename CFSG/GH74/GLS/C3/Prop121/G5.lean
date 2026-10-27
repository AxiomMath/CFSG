module

public import CFSG.GH74.GLS.C3.Prop121.G5Core
public import CFSG.GH74.GLS.C3.Layer2.ModelBridge
public import CFSG.GH74.GLS.C3.Prop121.G5Norm
public import CFSG.GH74.GLS.C3.Prop121.G5Pat
public import CFSG.GH74.GLS.C3.Prop121.G5Iota
public import CFSG.GH74.GLS.C3.Prop121.G5Four
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.FnFacts
public import CFSG.GH74.GLS.C3.Prop121.PatternFacts

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem exists_g_five
    (hG : pRank 2 G ≤ 4) (h : IsAConfig 5 x K T Q S a)
    (hA : IsApproxTo G (alternatingGroup (Fin 9))) :
    ∃ g : G, g ^ 2 = 1 ∧ ∀ q ∈ Q, g * q * g⁻¹ ∈ K := by
  have hG4 : pRank 2 G ≤ 4 := hG
  have hn : (5 : ℕ) = 5 ∨ (5 : ℕ) = 6 ∨ (5 : ℕ) = 7 := Or.inl rfl
  obtain ⟨ι₀, hι₀1, hι₀Q⟩ := exists_coord hn hG4 h
  obtain ⟨ι, hι1, hιQ, hιT⟩ := exists_equiv_T5 h ι₀ hι₀1 hι₀Q
  have hK := K_iff hn h hιQ
  have hF := fnFacts 5 hn
  have hP := patternFacts_of_approx (n := 5) hn hA
  have hC := coordData_of_config h hι1 hιQ
  have hQX : ∀ q ∈ Q, q ≠ 1 → q ≠ x → IsConj x q :=
    fun q hq hq1 hqx => Coord.isConj_x_of_mem_Q hC hF hP hq hq1 hqx
  have hTS : T ≤ S := h.T_lt_S.le
  have hxS : x ∈ S := hTS h.x_mem_T
  have hTinf : S ⊓ centralizer ({x} : Set G) = T :=
    h.sylowT.eq_of_le (le_inf hTS h.T_le_C) inf_le_right h.sylowS.isPGroup.to_inf_left
  have hTcent : ∀ s ∈ S, s * x = x * s → s ∈ T := fun s hs hc => by
    rw [← hTinf]
    exact ⟨hs, mem_centralizer_singleton_iff.2 hc⟩
  obtain ⟨φ, hφinj, hφsyl, hφconj, hφcard⟩ := pattern_map hA.1 h.sylowS
  have hC480 : Nat.card ↥(centralizer ({x} : Set G)) = 480 := by
    rw [Coord.card_cent_x ι]
    decide
  have hT32 : Nat.card T = 32 := by
    have := h.sylowT.card_eq
    rw [hC480, Nat.factorization_def _ Nat.prime_two] at this
    rw [this]
    decide +kernel
  have hS64 : Nat.card S = 64 := by
    have h1 : Nat.card S = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    have h2 := hφsyl.card_eq
    rw [Subgroup.card_top, card_A9, Nat.factorization_def _ Nat.prime_two] at h2
    rw [h1, h2]
    decide +kernel
  have hidx : (T.subgroupOf S).index = 2 := by
    have h1 : T.relIndex S * Nat.card (T ⊓ S : Subgroup G) = Nat.card S :=
      Subgroup.relIndex_mul_card T S
    rw [inf_eq_left.2 hTS, hT32, hS64] at h1
    exact (by omega : T.relIndex S = 2)
  set xS : ↥S := ⟨x, hxS⟩ with hxSdef
  have haS : a ∈ S := h.a_mem.1
  set aS : ↥S := ⟨a, haS⟩ with haSdef
  set x'S : ↥S := ⟨a * x * a⁻¹, mul_mem (mul_mem haS hxS) (inv_mem haS)⟩ with hx'Sdef
  have hx'eq : x'S = aS * xS * aS⁻¹ := rfl
  have hne : xS ≠ x'S := fun hc => h.a_conj_x_ne (congrArg Subtype.val hc).symm
  have hsq : xS * xS = 1 := Subtype.ext (by
    show x * x = 1
    rw [← sq]
    exact h.x_sq)
  have hkey : ∀ s : ↥S, s * xS * s⁻¹ = xS ∨ s * xS * s⁻¹ = x'S := by
    intro s
    by_cases hs : (s : G) ∈ T
    · left
      have hc : (s : G) * x = x * (s : G) := mem_centralizer_singleton_iff.1 (h.T_le_C hs)
      have : s * xS = xS * s := Subtype.ext hc
      rw [this]
      group
    · right
      have haT : (a : G) ∉ T := h.a_mem.2.2.1
      have h1 : aS⁻¹ * s ∈ T.subgroupOf S := by
        rw [mul_mem_iff_of_index_two hidx]
        constructor
        · intro hh
          have h2 : (a : G)⁻¹ ∈ T := hh
          exact absurd (inv_mem_iff.1 h2) haT
        · intro hh
          exact absurd hh hs
      have hcT : ((aS⁻¹ * s : ↥S) : G) ∈ T := h1
      have hc : ((aS⁻¹ * s : ↥S) : G) * x = x * ((aS⁻¹ * s : ↥S) : G) :=
        mem_centralizer_singleton_iff.1 (h.T_le_C hcT)
      have hc' : (aS⁻¹ * s) * xS = xS * (aS⁻¹ * s) := Subtype.ext hc
      have hs' : s = aS * (aS⁻¹ * s) := by group
      rw [hx'eq]
      calc s * xS * s⁻¹ = aS * ((aS⁻¹ * s) * xS * (aS⁻¹ * s)⁻¹) * aS⁻¹ := by group
        _ = aS * xS * aS⁻¹ := by rw [hc']; group
  have hcl : ∀ s : ↥S, (s * xS * s⁻¹ = xS ∨ s * xS * s⁻¹ = x'S) ∧
      (s * x'S * s⁻¹ = xS ∨ s * x'S * s⁻¹ = x'S) := by
    intro s
    refine ⟨hkey s, ?_⟩
    have e : s * x'S * s⁻¹ = (s * aS) * xS * (s * aS)⁻¹ := by rw [hx'eq]; group
    rw [e]
    exact hkey (s * aS)
  have hxord : orderOf xS = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hsq) (fun hc => h.x_ne_one (congrArg Subtype.val hc))
  have hφxord : orderOf (φ xS) = 2 := by rw [orderOf_injective φ hφinj]; exact hxord
  have hnm : numMoved ((φ xS : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 4 :=
    numMoved_eq_four_of_card_centralizer (φ xS) hφxord (by rw [← hφcard xS hxord]; exact hC480)
  obtain ⟨ψ, hψinj, hψnm, hψS0, hψsurj, hψx⟩ :=
    normalize φ hφinj hφsyl xS x'S hne hsq hnm hcl
  have hψconj : ∀ u v : ↥S, orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G) →
      numMoved (ψ u) = numMoved (ψ v) := by
    intro u v hu hv huv
    have := numMoved_eq_of_isConj_alternating 9 ((hφconj u v hu hv).1 huv)
    rw [hψnm, hψnm]
    exact this
  obtain ⟨g, hg2, hgQ⟩ := core_five hxS (by rw [← sq]; exact h.x_sq) h.x_ne_one hTS h.T_le_C hTcent
    h.Q_le_T (fun q hq => by rw [← sq]; exact h.Q_sq hq) hQX ι hι1 hιQ hιT hK ψ hψinj hψS0
    hψsurj hψx hψconj
  exact ⟨g, by rw [sq]; exact hg2, hgQ⟩

end CFSG.GH74.GLS.C3.Prop121
