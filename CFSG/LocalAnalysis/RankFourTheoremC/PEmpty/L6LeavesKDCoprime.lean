module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDOrbit

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

open CFSG Subgroup

theorem mem_normalizer_of_forward {G : Type} [Group G] {z : G} {p : ℕ} (hp : 0 < p)
    (hzp : z ^ p = 1) {U : Subgroup G} (h : ∀ g ∈ U, z * g * z⁻¹ ∈ U) :
    z ∈ Subgroup.normalizer (U : Set G) := by
  have hit : ∀ k : ℕ, ∀ g ∈ U, z ^ k * g * (z ^ k)⁻¹ ∈ U := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih =>
      intro g hg
      have h1 := h _ (ih g hg)
      have e : z * (z ^ k * g * (z ^ k)⁻¹) * z⁻¹ = z ^ (k + 1) * g * (z ^ (k + 1))⁻¹ := by
        group
      rwa [e] at h1
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  have h2 := hit k _ hg
  have e : z ^ k * (z * g * z⁻¹) * (z ^ k)⁻¹ = g := by
    have e' : z ^ k * (z * g * z⁻¹) * (z ^ k)⁻¹ = z ^ (k + 1) * g * (z ^ (k + 1))⁻¹ := by
      group
    rw [e', hzp]
    simp
  rwa [e] at h2

theorem mem_normalizer_of_pow_eq {G : Type} [Group G] {z : G} {p : ℕ} (hp : p.Prime)
    (hzp : z ^ p = 1) {i : ℕ} (hi0 : 0 < i) (hip : i < p) {L : Subgroup G}
    (h : conjPow z i L = L) : z ∈ Subgroup.normalizer (L : Set G) := by
  have hcop : Nat.Coprime i p := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    have := Nat.le_of_dvd hi0 hd
    omega
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hdm := Nat.div_add_mod (i * j) p
  rw [hj] at hdm
  have hzij : (z ^ i) ^ j = z := by
    rw [← pow_mul, ← hdm, pow_add, pow_mul, hzp, one_pow, one_mul, pow_one]
  have hstep : ∀ x ∈ L, z ^ i * x * (z ^ i)⁻¹ ∈ L := by
    intro x hx
    have hmem : z ^ i * x * (z ^ i)⁻¹ ∈ conjPow z i L :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [h] at hmem
  have hiter : ∀ k : ℕ, ∀ x ∈ L, (z ^ i) ^ k * x * ((z ^ i) ^ k)⁻¹ ∈ L := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have e : (z ^ i) ^ (k + 1) * x * ((z ^ i) ^ (k + 1))⁻¹
          = (z ^ i) ^ k * (z ^ i * x * (z ^ i)⁻¹) * ((z ^ i) ^ k)⁻¹ := by
        group
      rw [e]
      exact ih _ (hstep x hx)
  apply mem_normalizer_of_forward hp.pos hzp
  intro g hg
  have := hiter j g hg
  rwa [hzij] at this

@[expose] def conjSubEquiv {G : Type} [Group G] (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H ≃* H where
  toFun x := ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : G) * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hg _).mpr (by
    have e : g * (g⁻¹ * (x : G) * g⁻¹⁻¹) * g⁻¹ = x := by group
    rw [e]
    exact x.2)⟩
  left_inv x := Subtype.ext (by
    show g⁻¹ * (g * (x : G) * g⁻¹) * g⁻¹⁻¹ = x
    group)
  right_inv x := Subtype.ext (by
    show g * (g⁻¹ * (x : G) * g⁻¹⁻¹) * g⁻¹ = x
    group)
  map_mul' x y := Subtype.ext (by
    show g * ((x : G) * (y : G)) * g⁻¹ = (g * (x : G) * g⁻¹) * (g * (y : G) * g⁻¹)
    group)

theorem isSylowOf_two_map_surjective {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P ⊤) :
    CFSG.ABGLocalTools.IsSylowOf 2 (P.map f) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨-, hPp, hdvd⟩ := hP
  refine ⟨le_top, hPp.map f, ?_⟩
  rw [Subgroup.relIndex_top_right] at hdvd ⊢
  have hidx : (P.map f).index = (P ⊔ f.ker).index := by
    rw [← Subgroup.index_comap_of_surjective (H := P.map f) hf, Subgroup.comap_map_eq]
  have hdiv : (P ⊔ f.ker).index ∣ P.index := Subgroup.index_dvd_of_le le_sup_left
  intro h2
  rw [hidx] at h2
  exact hdvd (h2.trans hdiv)

theorem centralizer_le_normalizer_sub {G : Type} [Group G] (K : Subgroup G) :
    Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem component_normal_layer {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsComponent K) : (K.subgroupOf (layer G)).Normal := by
  have hKle : K ≤ layer G := by
    rw [layer.eq_sSup]
    exact le_sSup hK
  have hN : layer G ≤ Subgroup.normalizer (K : Set G) := by
    rw [layer.eq_sSup]
    apply sSup_le
    intro K' hK'
    have hK'' : IsComponent K' := hK'
    rcases LocalCores.distinct_components_commute hK hK'' with h | h
    · subst h
      exact Subgroup.le_normalizer
    · have h' : ⁅K', K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact h
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h').trans
        (centralizer_le_normalizer_sub K)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr hN

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD
