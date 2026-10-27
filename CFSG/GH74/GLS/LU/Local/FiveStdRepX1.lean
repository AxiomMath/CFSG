module

public import CFSG.GH74.GLS.LU.Local.FiveStdBase
public import CFSG.GH74.GLS.LU.Local.FiveStdRepA

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd CFSG.GH74.GLS.LU.Local.Five.FiveStdRep

namespace FiveStdX1

variable {G : Type} [Group G]

theorem mem_zpowers_lt [Finite G] {y : G} (h5 : y ^ 5 = 1) {x : G} :
    x ∈ zpowers y ↔ ∃ i < 5, x = y ^ i := by
  constructor
  · intro hx
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n % 5, Nat.mod_lt _ (by norm_num), pow_eq_pow_mod n h5⟩
  · rintro ⟨i, -, rfl⟩
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i

theorem coe_zpowers_eq_S [Finite G] {ι : E → G} (hM : Model ι) {g : E} (hg : validE g = true) (h5 : ι g ^ 5 = 1) :
    ((zpowers (ι g) : Subgroup G) : Set G) = S ι (powers g 5) := by
  ext x
  rw [SetLike.mem_coe, mem_zpowers_lt h5, hM.S_powers hg 5, Set.mem_ofPred_eq]

theorem mem_sup_zpowers_lt {x y : G} (hxy : x * y = y * x) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) {h : G} :
    h ∈ zpowers x ⊔ zpowers y ↔ ∃ i < 5, ∃ j < 5, h = x ^ i * y ^ j := by
  obtain ⟨P, hP⟩ := FiveStdBase.exists_pp_sub hxy hx hy
  have hxP : x ∈ P := (hP x).2 ⟨1, 0, by simp⟩
  have hyP : y ∈ P := (hP y).2 ⟨0, 1, by simp⟩
  constructor
  · intro hh
    have : h ∈ P :=
      (sup_le (Subgroup.zpowers_le.2 hxP) (Subgroup.zpowers_le.2 hyP) : zpowers x ⊔ zpowers y ≤ P) hh
    obtain ⟨i, j, rfl⟩ := (hP h).1 this
    exact ⟨i % 5, Nat.mod_lt _ (by norm_num), j % 5, Nat.mod_lt _ (by norm_num),
      by rw [← pow_eq_pow_mod i hx, ← pow_eq_pow_mod j hy]⟩
  · rintro ⟨i, -, j, -, rfl⟩
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i)
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) j)

theorem coe_sup_zpowers_eq_S {ι : E → G} (hM : Model ι) {g g2 : E} (hg : validE g = true) (hg2 : validE g2 = true)
    (hcomm : ι g * ι g2 = ι g2 * ι g) (h5 : ι g ^ 5 = 1) (h52 : ι g2 ^ 5 = 1) :
    ((zpowers (ι g) ⊔ zpowers (ι g2) : Subgroup G) : Set G) = S ι (ppE g g2 5 5) := by
  ext x
  rw [SetLike.mem_coe, mem_sup_zpowers_lt hcomm h5 h52, hM.S_ppE hg hg2, Set.mem_ofPred_eq]

theorem cjL_zpowers (c x : G) : cjL c (zpowers x) = zpowers (c * x * c⁻¹) := by
  unfold cjL
  rw [MonoidHom.map_zpowers]
  rfl

theorem mem_normalizer_of_gens [Finite G] {K : Subgroup G} {c : G} {gens : Set G} (hK : K ≤ closure gens)
    (h : ∀ x ∈ gens, c * x * c⁻¹ ∈ K) : c ∈ normalizer (K : Set G) := by
  rw [← repCj_eq_iff]
  apply repCj_eq_of_le
  intro k hk
  have hle : closure gens ≤ K.comap (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    exact h x hx
  exact hle (hK hk)

theorem normG_iff_normalizer [Finite G] {ι : E → G} (hM : Model ι) {c : E} (hc : validE c = true)
    {gens L : List E} (hgens : V gens) (hL : V L) {K : Subgroup G} (hKL : (K : Set G) = S ι L)
    (hKgens : ∀ x ∈ gens, ι x ∈ K) (hK : K ≤ closure (ι '' {x | x ∈ gens})) :
    normG c gens L = true ↔ ι c ∈ normalizer (K : Set G) := by
  rw [hM.normG_iff hc hgens hL]
  constructor
  · intro h
    apply mem_normalizer_of_gens hK
    rintro _ ⟨x, hx, rfl⟩
    have := h x hx
    rwa [← hKL] at this
  · intro h x hx
    rw [← hKL]
    exact (Subgroup.mem_normalizer_iff.1 h _).1 (hKgens x hx)

theorem cenG_iff_centralizer {ι : E → G} (hM : Model ι) {c : E} (hc : validE c = true)
    {gens : List E} (hgens : V gens) {K : Subgroup G}
    (hKgens : ∀ x ∈ gens, ι x ∈ K) (hK : K ≤ closure (ι '' {x | x ∈ gens})) :
    cenG c gens = true ↔ ι c ∈ centralizer (K : Set G) := by
  rw [hM.cenG_iff hc hgens, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have hle : closure (ι '' {x | x ∈ gens}) ≤ centralizer ({ι c} : Set G) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h x hx).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (hK hk))
  · intro h x hx
    exact (h _ (hKgens x hx)).symm

theorem coe_filter_Cs {G : Type} [Group G] (st : FiveStdSetting G) {M : Subgroup G} {p : E → Bool}
    (hp : ∀ x ∈ Cs, p x = true ↔ st.ι x ∈ M) :
    S st.ι (Cs.filter p) = ((M ⊓ Cz st.z : Subgroup G) : Set G) := by
  have hC : ∀ g : G, g ∈ S st.ι Cs ↔ g ∈ Cz st.z := fun g => by
    rw [← st.hC]
    exact Iff.rfl
  rw [S_filter hp]
  ext g
  rw [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_inf, hC]
  exact and_comm

theorem sup2_of_coe_eq {N P Q : Subgroup G} (h : (N : Set G) = (P : Set G) * (Q : Set G)) : N = P ⊔ Q := by
  apply le_antisymm
  · intro g hg
    have : g ∈ (P : Set G) * (Q : Set G) := by rw [← h]; exact hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 this
    exact Subgroup.mul_mem_sup hx hy
  · refine sup_le ?_ ?_
    · intro x hx
      have : x * 1 ∈ (P : Set G) * (Q : Set G) := Set.mul_mem_mul hx Q.one_mem
      rw [mul_one, ← h] at this
      exact this
    · intro y hy
      have : 1 * y ∈ (P : Set G) * (Q : Set G) := Set.mul_mem_mul P.one_mem hy
      rw [one_mul, ← h] at this
      exact this

theorem sup3_of_coe_eq {N P Q R : Subgroup G}
    (h : (N : Set G) = (P : Set G) * (Q : Set G) * (R : Set G)) : N = P ⊔ Q ⊔ R := by
  apply le_antisymm
  · intro g hg
    have : g ∈ (P : Set G) * (Q : Set G) * (R : Set G) := by rw [← h]; exact hg
    obtain ⟨_, ⟨x, hx, y, hy, rfl⟩, w, hw, rfl⟩ := Set.mem_mul.1 this
    exact Subgroup.mul_mem_sup (Subgroup.mul_mem_sup hx hy) hw
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      have : x * 1 * 1 ∈ (P : Set G) * (Q : Set G) * (R : Set G) :=
        Set.mul_mem_mul (Set.mul_mem_mul hx Q.one_mem) R.one_mem
      rw [mul_one, mul_one, ← h] at this
      exact this
    · intro y hy
      have : 1 * y * 1 ∈ (P : Set G) * (Q : Set G) * (R : Set G) :=
        Set.mul_mem_mul (Set.mul_mem_mul P.one_mem hy) R.one_mem
      rw [one_mul, mul_one, ← h] at this
      exact this
    · intro w hw
      have : 1 * 1 * w ∈ (P : Set G) * (Q : Set G) * (R : Set G) :=
        Set.mul_mem_mul (Set.mul_mem_mul P.one_mem Q.one_mem) hw
      rw [one_mul, one_mul, ← h] at this
      exact this

end FiveStdX1

end CFSG.GH74.GLS.LU.Local.Five
