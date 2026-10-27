module

public import CFSG.ClassicalInvolution.Asc77.AscT7Y1
public import CFSG.ClassicalInvolution.Q3.Q3T6AutNorm
public import CFSG.ClassicalInvolution.Q3.Q3TIYTPAut

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7.OddC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3T6
  CFSG.ClassicalInvolution.Q3.Q3TIY CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Perm

variable {G : Type} [Group G]

theorem conjSub_eq_self_of_odd {x : G} (hx : Odd (orderOf x)) {A B : Subgroup G} (hAB : A ≠ B)
    (hA : conjSub x A = A ∨ conjSub x A = B) (hB : conjSub x B = A ∨ conjSub x B = B) :
    conjSub x A = A := by
  by_contra hne
  have h1 : conjSub x A = B := hA.resolve_left hne
  have h2 : conjSub x B = A := by
    rcases hB with h | h
    · exact h
    · exact absurd (conjSub_injective x (h1.trans h.symm)) hAB
  have key : ∀ k : ℕ, conjSub (x ^ (2 * k + 1)) A = B := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      have e : x ^ (2 * (k + 1) + 1) = x * (x * x ^ (2 * k + 1)) := by
        rw [show 2 * (k + 1) + 1 = 1 + (1 + (2 * k + 1)) by ring, pow_add, pow_add, pow_one]
      rw [e, conjSub_mul, conjSub_mul, ih, h2, h1]
  obtain ⟨m, hm⟩ := hx
  have h3 := key m
  rw [← hm, pow_orderOf_eq_one, conjSub_one] at h3
  exact hAB h3

theorem conjSub_le_centralizer {g c : G} (hg : g ∈ Subgroup.centralizer ({c} : Set G))
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({c} : Set G)) :
    conjSub g K ≤ Subgroup.centralizer ({c} : Set G) := by
  intro y hy
  rw [mem_conjSub_iff] at hy
  have hk : Commute (g⁻¹ * y * g) c := Subgroup.mem_centralizer_singleton_iff.mp (hK hy)
  have hgc : Commute g c := Subgroup.mem_centralizer_singleton_iff.mp hg
  have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : Commute y c := by
    rw [e]
    exact (hgc.mul_left hk).mul_left hgc.inv_left
  exact this.eq

end Perm

section OddCore

variable {G : Type} [Group G]

theorem conj_mem_oddCoreOf {X : Subgroup G} {y : G} (hy : y ∈ X) {x : G} (hx : x ∈ oddCoreOf X) :
    y * x * y⁻¹ ∈ oddCoreOf X := by
  obtain ⟨n, hn, rfl⟩ := hx
  have h1 := (inferInstance : (classicalInvolutionOddCore ↥X).Normal).conj_mem n hn ⟨y, hy⟩
  exact ⟨_, h1, by simp⟩

theorem odd_orderOf_of_mem_oddCoreOf [Finite G] {X : Subgroup G} {x : G} (hx : x ∈ oddCoreOf X) :
    Odd (orderOf x) :=
  (oddCoreOf_odd_natCard X).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)

theorem commute_of_inner [Finite G] {C M : Subgroup G} (hMC : M ≤ C)
    (hex : classicalInvolutionOddCore ↥M = ⊥) {x : G} (hx : x ∈ oddCoreOf C)
    (hxM : conjSub x M = M) {m : G} (hm : m ∈ M) : x * m = m * x := by
  have hd : m * x * m⁻¹ * x⁻¹ ∈ M ⊓ oddCoreOf C := by
    refine ⟨?_, ?_⟩
    · have h1 : x * m⁻¹ * x⁻¹ ∈ M := by
        have := conj_mem_conjSub (n := x) (K := M) (M.inv_mem hm)
        rwa [hxM] at this
      have h2 := M.mul_mem hm h1
      simpa [mul_assoc] using h2
    · exact (oddCoreOf C).mul_mem (conj_mem_oddCoreOf (hMC hm) hx) ((oddCoreOf C).inv_mem hx)
  have hle : M ⊓ oddCoreOf C ≤ Balance.oddCoreIn M := by
    refine Balance.le_oddCoreIn_of_normalizes inf_le_left ?_ ?_
    · intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact ⟨M.mul_mem (M.mul_mem hg hh.1) (M.inv_mem hg), conj_mem_oddCoreOf (hMC hg) hh.2⟩
      · intro hh
        have e : h = g⁻¹ * (g * h * g⁻¹) * g := by group
        rw [e]
        refine ⟨M.mul_mem (M.mul_mem (M.inv_mem hg) hh.1) hg, ?_⟩
        simpa using conj_mem_oddCoreOf (hMC (M.inv_mem hg)) hh.2
    · exact (oddCoreOf_odd_natCard C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have h0 : Balance.oddCoreIn M = ⊥ := by
    show (classicalInvolutionOddCore ↥M).map M.subtype = ⊥
    rw [hex, Subgroup.map_bot]
  have h3 := hle hd
  rw [h0, Subgroup.mem_bot] at h3
  have h4 : ⁅m, x⁆ = 1 := h3
  exact (commutatorElement_eq_one_iff_mul_comm.mp h4).symm

end OddCore

section Outer

variable {G : Type} [Group G]

theorem commute_of_outer [Finite G] {M N : Subgroup G} {z b b' c x : G}
    (hM : IsClassicalMember3 M z) (hexM : classicalInvolutionOddCore ↥M = ⊥)
    (hMN : Commutes M N) (hb : b ∈ M) (hb2 : b * b = z) (hb' : b' ∈ N) (hc : c = b * b')
    (hxM : conjSub x M = M) (hxN : conjSub x N = N) (hxc : x * c * x⁻¹ = c)
    (hodd : Odd (orderOf x)) {m : G} (hm : m ∈ M) : x * m = m * x := by
  classical
  have hxb : x * b * x⁻¹ ∈ M := by
    have := conj_mem_conjSub (n := x) (K := M) hb
    rwa [hxM] at this
  have hxb' : x * b' * x⁻¹ ∈ N := by
    have := conj_mem_conjSub (n := x) (K := N) hb'
    rwa [hxN] at this
  set w : G := b⁻¹ * (x * b * x⁻¹) with hw
  have hwM : w ∈ M := M.mul_mem (M.inv_mem hb) hxb
  have hxb_eq : x * b * x⁻¹ = b * w := by rw [hw]; group
  have hxb'_eq : x * b' * x⁻¹ = w⁻¹ * b' := by
    have h1 : (x * b * x⁻¹) * (x * b' * x⁻¹) = b * b' := by
      calc (x * b * x⁻¹) * (x * b' * x⁻¹) = x * (b * b') * x⁻¹ := by group
        _ = b * b' := by rw [← hc]; exact hxc
    rw [hxb_eq] at h1
    calc x * b' * x⁻¹ = (b * w)⁻¹ * (b * w * (x * b' * x⁻¹)) := by group
      _ = (b * w)⁻¹ * (b * b') := by rw [h1]
      _ = w⁻¹ * b' := by group
  have hwN : w ∈ N := by
    have h2 : w⁻¹ = (x * b' * x⁻¹) * b'⁻¹ := by rw [hxb'_eq]; group
    have h3 : w⁻¹ ∈ N := by
      rw [h2]
      exact N.mul_mem hxb' (N.inv_mem hb')
    simpa using N.inv_mem h3
  have hwcomm : ∀ y ∈ M, y * w = w * y := fun y hy => hMN y hy w hwN
  obtain ⟨e₀⟩ := hM.nonempty_equiv
  have hxn : x ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := mem_conjSub_iff (n := x) (K := M) (x := x * h * x⁻¹)
    rw [hxM] at h1
    have e : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    rw [e] at h1
    exact h1.symm
  set n : Subgroup.normalizer (M : Set G) := ⟨x, hxn⟩ with hn
  set α : MulAut SL(2, ZMod 3) := normalizerToAutSL3 e₀ n with hα
  set bM : M := ⟨b, hb⟩ with hbM
  set wM : M := ⟨w, hwM⟩ with hwM'
  have hnb : normalizerConj M n bM = bM * wM := Subtype.ext (by
    rw [normalizerConj_apply_coe]
    exact hxb_eq)
  set s : SL(2, ZMod 3) := e₀ (QuotientGroup.mk bM) with hs
  set σ : SL(2, ZMod 3) := e₀ (QuotientGroup.mk wM) with hσ
  have hαs : α s = s * σ := by
    rw [hs, hα, normalizerToAutSL3_apply, hnb, QuotientGroup.mk_mul, map_mul]
  have hσc : σ ∈ Subgroup.center SL(2, ZMod 3) := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨q, rfl⟩ := e₀.surjective t
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hσ, ← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 2
    exact Subtype.ext (hwcomm y y.2)
  have hσ1 : σ = 1 ∨ σ = -1 := (mem_center_sl2_iff σ).mp hσc
  have hneg2 : (-1 : SL(2, ZMod 3)) * -1 = 1 := by decide
  have hneg1 : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have hαneg : α (-1) = -1 := by
    have h1 : α (-1) * α (-1) = 1 := by rw [← map_mul, hneg2, map_one]
    rcases sl2_sq_eq_one h2ne h1 with h | h
    · exact absurd (α.injective (h.trans (map_one α).symm)) hneg1
    · exact h
  have hασ : α σ = σ := by
    rcases hσ1 with h | h
    · rw [h, map_one]
    · rw [h, hαneg]
  have hσσ : σ * σ = 1 := by
    rcases hσ1 with h | h
    · rw [h, one_mul]
    · rw [h, hneg2]
  have hα2s : α (α s) = s := by
    rw [hαs, map_mul, hαs, hασ, mul_assoc, hσσ, mul_one]
  have hbb : s * s = -1 := by
    have hz1 : z ≠ 1 := fun h => by
      have := hM.orderOf_eq_two
      rw [h, orderOf_one] at this
      omega
    have hzz : z * z = 1 := by
      have h2 := pow_orderOf_eq_one z
      rw [hM.orderOf_eq_two] at h2
      simpa [sq] using h2
    set zM : M := ⟨z, hM.mem⟩ with hzM
    have hss : s * s = e₀ (QuotientGroup.mk zM) := by
      rw [hs, ← map_mul, ← QuotientGroup.mk_mul]
      congr 2
      exact Subtype.ext hb2
    have hζ2 : e₀ (QuotientGroup.mk zM) * e₀ (QuotientGroup.mk zM) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, show zM * zM = 1 from Subtype.ext hzz,
        QuotientGroup.mk_one, map_one]
    rcases sl2_sq_eq_one h2ne hζ2 with h | h
    · exfalso
      have h1 : (QuotientGroup.mk zM : M ⧸ classicalInvolutionOddCore ↥M) = 1 := e₀.injective
        (h.trans (map_one e₀).symm)
      rw [QuotientGroup.eq_one_iff, hexM, Subgroup.mem_bot] at h1
      exact hz1 (congrArg Subtype.val h1)
    · rw [hss, h]
  have hαm : α ^ orderOf x = 1 := by
    rw [hα, ← map_pow]
    have : n ^ orderOf x = 1 := Subtype.ext (by simp [hn, pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨k, hk⟩ := id hodd
  have hβ1 : α ^ 2 = 1 := by
    refine sl2Three_mulAut_eq_one_of_odd_fix (α ^ 2) hodd ?_ hbb ?_
    · rw [← pow_mul, mul_comm, pow_mul, hαm, one_pow]
    · show (α * α) s = s
      exact hα2s
  have hα1 : α = 1 := by
    calc α = α ^ orderOf x := by
          rw [hk, pow_succ, pow_mul, hβ1, one_pow, one_mul]
      _ = 1 := hαm
  have hcomm := (normalizerToAutSL3_eq_one_iff e₀ n).mp hα1 m hm
  have h0 : oddCoreOf M = ⊥ := by
    unfold oddCoreOf
    rw [hexM, Subgroup.map_bot]
  rw [h0, Subgroup.mem_bot] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

end Outer

section Frame

variable {G : Type} [Group G]

theorem oddCore_centralizer_eq_bot_of_frame [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    (hconj : ConjInvariant Ω) (hex : ExactMembers Ω)
    {K₁ K₂ K₃ K₄ : Subgroup G} {z c b b' : G}
    (h₁Ω : K₁ ∈ Ω) (h₂Ω : K₂ ∈ Ω) (h₃Ω : K₃ ∈ Ω) (h₄Ω : K₄ ∈ Ω)
    (hz₁ : IsUniqueInvolution K₁ z) (hz₂ : IsUniqueInvolution K₂ z)
    (hz₃ : IsUniqueInvolution K₃ z) (hz₄ : IsUniqueInvolution K₄ z) (h12 : K₁ ≠ K₂)
    (h34 : K₃ ≠ K₄)
    (hV : ∀ M ∈ Ω, IsUniqueInvolution M z → M = K₁ ∨ M = K₂ ∨ M = K₃ ∨ M = K₄)
    (hK₁c : K₁ ≤ Subgroup.centralizer ({c} : Set G))
    (hK₂c : K₂ ≤ Subgroup.centralizer ({c} : Set G))
    (hK₃c : ¬ K₃ ≤ Subgroup.centralizer ({c} : Set G))
    (hK₄c : ¬ K₄ ≤ Subgroup.centralizer ({c} : Set G))
    (hb : b ∈ K₃) (hb' : b' ∈ K₄) (hbb : b * b = z) (hb'b' : b' * b' = z) (hc : c = b * b')
    (hc1 : c ≠ 1) (hcomm : Commutes K₃ K₄) (hM₃ : IsClassicalMember3 K₃ z)
    (hM₄ : IsClassicalMember3 K₄ z) (hα : alphaOf (Subgroup.closure ({c, z} : Set G)) = ⊥)
    (hGen : K₁ ⊔ K₂ ⊔ K₃ ⊔ K₄ ⊔ Subgroup.centralizer ({c} : Set G) = ⊤) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) = ⊥ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({c} : Set G) with hC
  set P : Subgroup G := K₁ ⊔ K₂ ⊔ K₃ ⊔ K₄ with hP
  have hcz : ∀ x ∈ oddCoreOf C, x * z = z * x := by
    intro x hx
    have hcA : c ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
    have hzA : z ∈ Subgroup.closure ({c, z} : Set G) := Subgroup.subset_closure (by simp)
    exact T7Y.commute_of_alphaOf_eq_bot hcA hc1 hα hx hzA
  have hxC : ∀ x ∈ oddCoreOf C, x ∈ C := fun x hx => oddCoreOf_le_self C hx
  have hxc : ∀ x ∈ oddCoreOf C, x * c * x⁻¹ = c := by
    intro x hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hxC x hx)
    rw [h]; group
  have hnotC : ∀ x ∈ C, ∀ M N : Subgroup G, ¬ M ≤ C → N ≤ C → conjSub x M ≠ N := by
    intro x hx M N hM hN h
    apply hM
    have h1 : conjSub x⁻¹ (conjSub x M) = M := conjSub_inv_conjSub x M
    rw [h] at h1
    rw [← h1]
    exact conjSub_le_centralizer (C.inv_mem hx) hN
  have hmem4 : ∀ x ∈ oddCoreOf C, ∀ M ∈ Ω, IsUniqueInvolution M z →
      conjSub x M = K₁ ∨ conjSub x M = K₂ ∨ conjSub x M = K₃ ∨ conjSub x M = K₄ := by
    intro x hx M hM hMz
    have h1 := hMz.conj x
    rw [show x * z * x⁻¹ = z by rw [hcz x hx]; group] at h1
    exact hV _ (hconj x M hM) h1
  have hin : ∀ x ∈ oddCoreOf C, ∀ M ∈ Ω, IsUniqueInvolution M z → M ≤ C →
      conjSub x M = K₁ ∨ conjSub x M = K₂ := by
    intro x hx M hM hMz hMC
    have hle : conjSub x M ≤ C := conjSub_le_centralizer (hxC x hx) hMC
    rcases hmem4 x hx M hM hMz with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hle) hK₃c
    · exact absurd (h ▸ hle) hK₄c
  have hout : ∀ x ∈ oddCoreOf C, ∀ M ∈ Ω, IsUniqueInvolution M z → ¬ M ≤ C →
      conjSub x M = K₃ ∨ conjSub x M = K₄ := by
    intro x hx M hM hMz hMC
    rcases hmem4 x hx M hM hMz with h | h | h | h
    · exact absurd h (hnotC x (hxC x hx) M K₁ hMC hK₁c)
    · exact absurd h (hnotC x (hxC x hx) M K₂ hMC hK₂c)
    · exact Or.inl h
    · exact Or.inr h
  have hfix : ∀ x ∈ oddCoreOf C, conjSub x K₁ = K₁ ∧ conjSub x K₂ = K₂ ∧ conjSub x K₃ = K₃ ∧
      conjSub x K₄ = K₄ := by
    intro x hx
    have hodd := odd_orderOf_of_mem_oddCoreOf hx
    have a1 := hin x hx K₁ h₁Ω hz₁ hK₁c
    have a2 := hin x hx K₂ h₂Ω hz₂ hK₂c
    have b3 := hout x hx K₃ h₃Ω hz₃ hK₃c
    have b4 := hout x hx K₄ h₄Ω hz₄ hK₄c
    exact ⟨conjSub_eq_self_of_odd hodd h12 a1 a2,
      conjSub_eq_self_of_odd hodd h12.symm a2.symm a1.symm,
      conjSub_eq_self_of_odd hodd h34 b3 b4,
      conjSub_eq_self_of_odd hodd h34.symm b4.symm b3.symm⟩
  have hcomm' : Commutes K₄ K₃ := fun a ha d hd => (hcomm d hd a ha).symm
  have hc' : c = b' * b := by rw [hc]; exact hcomm b hb b' hb'
  have hPc : ∀ x ∈ oddCoreOf C, P ≤ Subgroup.centralizer ({x} : Set G) := by
    intro x hx
    obtain ⟨f1, f2, f3, f4⟩ := hfix x hx
    have hodd := odd_orderOf_of_mem_oddCoreOf hx
    have c1 : K₁ ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_inner hK₁c (hex K₁ h₁Ω) hx f1 hm).symm
    have c2 : K₂ ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_inner hK₂c (hex K₂ h₂Ω) hx f2 hm).symm
    have c3 : K₃ ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_outer hM₃ (hex K₃ h₃Ω) hcomm hb hbb hb' hc f3 f4 (hxc x hx) hodd hm).symm
    have c4 : K₄ ≤ Subgroup.centralizer ({x} : Set G) := fun m hm =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_outer hM₄ (hex K₄ h₄Ω) hcomm' hb' hb'b' hb hc' f4 f3 (hxc x hx) hodd hm).symm
    exact sup_le (sup_le (sup_le c1 c2) c3) c4
  set S : Set G := {y | ∃ g ∈ C, ∃ p ∈ P, y = g * p * g⁻¹} with hS
  set N : Subgroup G := Subgroup.closure S with hN
  have hPN : P ≤ N := fun p hp => Subgroup.subset_closure ⟨1, C.one_mem, p, hp, by group⟩
  have hSconj : ∀ g' ∈ C, ∀ y ∈ S, g' * y * g'⁻¹ ∈ S := by
    rintro g' hg' y ⟨g, hg, p, hp, rfl⟩
    exact ⟨g' * g, C.mul_mem hg' hg, p, hp, by group⟩
  have hNconj : ∀ g' ∈ C, conjSub g' N ≤ N := by
    intro g' hg'
    show N.map (MulAut.conj g').toMonoidHom ≤ N
    rw [hN, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, hy, rfl⟩
    simpa using hSconj g' hg' y hy
  have hCnorm : C ≤ Subgroup.normalizer (N : Set G) := by
    intro g' hg'
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hNconj g' hg' (conj_mem_conjSub hh)
    · intro hh
      have h1 := hNconj g'⁻¹ (C.inv_mem hg') (conj_mem_conjSub hh)
      simpa [mul_assoc] using h1
  have hNtop : Subgroup.normalizer (N : Set G) = ⊤ := by
    rw [eq_top_iff, ← hGen]
    exact sup_le (hPN.trans Subgroup.le_normalizer) hCnorm
  have hNnormal : N.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hcenter : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exact absurd (by rw [h]; exact le_top) hM₃.not_le_center
  have hNtop' : N = ⊤ := by
    have := hNnormal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exfalso
      have hK₁P : K₁ ≤ P := le_sup_left.trans (le_sup_left.trans le_sup_left)
      have hzN : z ∈ N := hPN (hK₁P hz₁.mem)
      rw [h, Subgroup.mem_bot] at hzN
      exact hz₁.ne_one hzN
    · exact h
  have hZ : oddCoreOf C = ⊥ := by
    refine eq_bot_iff.mpr (fun x hx => ?_)
    rw [Subgroup.mem_bot]
    have hSle : S ⊆ (Subgroup.centralizer ({x} : Set G) : Set G) := by
      rintro _ ⟨g, hg, p, hp, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hx' : g⁻¹ * x * g ∈ oddCoreOf C := by
        have := conj_mem_oddCoreOf (C.inv_mem hg) hx
        simpa using this
      have hp' : p ∈ Subgroup.centralizer ({g⁻¹ * x * g} : Set G) := hPc _ hx' hp
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hp'
      calc g * p * g⁻¹ * x = g * (p * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * p) * g⁻¹ := by rw [h1]
        _ = x * (g * p * g⁻¹) := by group
    have hNle : N ≤ Subgroup.centralizer ({x} : Set G) := (Subgroup.closure_le _).mpr hSle
    rw [hNtop'] at hNle
    have hxcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hNle (Subgroup.mem_top g))
    rw [hcenter] at hxcenter
    exact Subgroup.mem_bot.mp hxcenter
  have hinj : Function.Injective C.subtype := C.subtype_injective
  have hZ' : (classicalInvolutionOddCore ↥C).map C.subtype = ⊥ := hZ
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).mp hZ'

end Frame

end CFSG.ClassicalInvolution.Q3.Q3T7.OddC
