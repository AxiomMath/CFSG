module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

section Quotient

variable {G : Type*} [Group G] {r : ℕ} (Z : Subgroup G) [Z.Normal]

theorem mem_of_mk_mem_map (hZ : Z ≤ Subgroup.center G) (hZr : Nat.Coprime (Nat.card Z) r)
    {Q : Subgroup G} (hQ : IsPGroup r Q) {y : G}
    (hy : QuotientGroup.mk' Z y ∈ Q.map (QuotientGroup.mk' Z)) {n : ℕ} (hyn : y ^ r ^ n = 1) :
    y ∈ Q := by
  obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp hy
  obtain ⟨z, hz, rfl⟩ := (QuotientGroup.mk'_eq_mk' Z).mp hqy
  obtain ⟨m, hm⟩ := hQ ⟨q, hq⟩
  have hqm : q ^ r ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hpow : z ^ r ^ (m + n) = 1 := by
    have h := Commute.mul_pow (Subgroup.mem_center_iff.mp (hZ hz) q) (r ^ (m + n))
    rw [pow_add, pow_mul', hyn, one_pow, pow_mul, hqm, one_pow, one_mul] at h
    rw [pow_add]
    exact h.symm
  have hord : orderOf z = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Z.orderOf_dvd_natCard hz) (Nat.Coprime.pow_right _ hZr))
      (orderOf_dvd_of_pow_eq_one hpow)
  rw [orderOf_eq_one_iff] at hord
  rwa [hord, mul_one]

theorem normalizer_eq_comap_normalizer_map (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) {Q : Subgroup G} (hQ : IsPGroup r Q) :
    Subgroup.normalizer (Q : Set G) =
      (Subgroup.normalizer (Q.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
        (QuotientGroup.mk' Z) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mp (Subgroup.le_normalizer_map _)) ?_
  have key : ∀ g ∈ (Subgroup.normalizer (Q.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
      (QuotientGroup.mk' Z), ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
    intro g hg x hx
    obtain ⟨n, hn⟩ := hQ ⟨x, hx⟩
    have hxn : x ^ r ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine mem_of_mk_mem_map Z hZ hZr hQ ?_ (n := n)
      (by rw [conj_pow, hxn, mul_one, mul_inv_cancel])
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_comap.mp hg) _).mp
      (Subgroup.mem_map_of_mem _ hx)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨key g hg x, fun hx => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hx

theorem exists_isPGroup_map_eq [Finite G] [Fact r.Prime] {V : Subgroup (G ⧸ Z)}
    (hV : IsPGroup r V) : ∃ V₀ : Subgroup G, IsPGroup r V₀ ∧ V₀.map (QuotientGroup.mk' Z) = V := by
  let W := V.comap (QuotientGroup.mk' Z)
  let f : W →* V := ((QuotientGroup.mk' Z).comp W.subtype).codRestrict V fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z v
    exact ⟨⟨g, hv⟩, rfl⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow r W))
  have htop : (P : Subgroup W).map f = ⊤ := by
    have h := (Sylow.mapSurjective hf P).is_maximal' (hV.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  refine ⟨(P : Subgroup W).map W.subtype, P.isPGroup'.map _, ?_⟩
  have hcomp : (QuotientGroup.mk' Z).comp W.subtype = V.subtype.comp f := MonoidHom.ext fun _ => rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem map_pCoreOf_le [Finite G] [Fact r.Prime] {H : Type*} [Group H] (f : G →* H)
    (P : Subgroup G) : (pCoreOf r P).map f ≤ pCoreOf r (P.map f) :=
  le_pCoreOf_of_le_normalizer r (Subgroup.map_mono (pCoreOf_le r P))
    ((Subgroup.map_mono (le_normalizer_pCoreOf r P)).trans (Subgroup.le_normalizer_map f))
    ((pCoreOf_isPGroup r P).map f)

theorem pCoreOf_le_map_pCoreOf_comap [Finite G] [Fact r.Prime] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) (M : Subgroup (G ⧸ Z)) :
    pCoreOf r M ≤ (pCoreOf r (M.comap (QuotientGroup.mk' Z))).map (QuotientGroup.mk' Z) := by
  obtain ⟨Q, hQ, hQM⟩ := exists_isPGroup_map_eq Z (pCoreOf_isPGroup r M)
  rw [← hQM]
  refine Subgroup.map_mono (le_pCoreOf_of_le_normalizer r ?_ ?_ hQ)
  · refine (Subgroup.le_comap_map (QuotientGroup.mk' Z) Q).trans (Subgroup.comap_mono ?_)
    rw [hQM]
    exact pCoreOf_le r M
  · rw [normalizer_eq_comap_normalizer_map Z hZ hZr hQ, hQM]
    exact Subgroup.comap_mono (le_normalizer_pCoreOf r M)

end Quotient

theorem Holds.quotient {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    (hZr : Nat.Coprime (Nat.card Z) r) (h : Holds G r) : Holds (G ⧸ Z) r := by
  intro U hU hUr
  have hπ : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  obtain ⟨U₀, hU₀, hU₀U⟩ := exists_isPGroup_map_eq Z hUr
  have hne : U₀ ≠ ⊥ := by
    rintro rfl
    exact hU (by rw [← hU₀U, Subgroup.map_bot])
  obtain ⟨S₀, P₀, hP₀, hN₀, hcore₀, -, hS₀⟩ := h U₀ hne hU₀
  have hNU : Subgroup.normalizer (U₀ : Set G) =
      (Subgroup.normalizer (U : Set (G ⧸ Z))).comap (QuotientGroup.mk' Z) := by
    rw [normalizer_eq_comap_normalizer_map Z hZ hZr hU₀, hU₀U]
  have hle : ∀ V : Subgroup (G ⧸ Z), V.comap (QuotientGroup.mk' Z) ≤ P₀ →
      V ≤ P₀.map (QuotientGroup.mk' Z) := fun V hV =>
    (Subgroup.map_comap_eq_self_of_surjective hπ V).symm.le.trans (Subgroup.map_mono hV)
  refine conclusion_of_core r U hUr (Sylow.mapSurjective hπ S₀) (P₀.map (QuotientGroup.mk' Z))
    ?_ (hle _ (hNU ▸ hN₀)) ?_ (hle _ ?_)
  · intro htop
    apply hP₀
    have hker : (QuotientGroup.mk' Z).ker ≤ P₀ := by
      rw [QuotientGroup.ker_mk']
      exact hZ.trans ((Subgroup.center_le_normalizer _).trans hS₀)
    rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
  · refine (pCoreOf_le_map_pCoreOf_comap Z hZ hZr _).trans ?_
    rw [← hNU]
    exact (Subgroup.map_mono hcore₀).trans (map_pCoreOf_le _ P₀)
  · rw [Sylow.coe_mapSurjective, ← normalizer_eq_comap_normalizer_map Z hZ hZr S₀.isPGroup']
    exact hS₀

theorem scalar_eq_one_of_pow_eq_one {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] {r : ℕ}
    [Fact r.Prime] [CharP K r] (c : Kˣ) (hc : Matrix.GeneralLinearGroup.scalar ι c ^ r = 1) :
    Matrix.GeneralLinearGroup.scalar ι c = 1 := by
  ext i j
  have hii := congrArg (fun A : GL ι K => (A : Matrix ι ι K) i i) hc
  simp only [← map_pow, Matrix.GeneralLinearGroup.coe_scalar] at hii
  have hc1 : (c : K) = 1 := frobenius_inj K r (by simpa [frobenius_def] using hii)
  simp [Matrix.GeneralLinearGroup.coe_scalar, hc1]

theorem Holds.statedProj {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {r : ℕ} [Fact r.Prime] [CharP K r] (H : Subgroup (GL ι K)) (h : Holds H r) :
    Holds (CFSG.Assembly.LowTwoRank.StatedProj H) r := by
  refine Holds.quotient _ ?_ ?_ h
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hx
    rw [Subgroup.mem_center_iff]
    exact fun g => Subtype.ext (Subgroup.mem_center_iff.mp hx' g)
  · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hdvd
    have hxr : x ^ r = 1 := hx ▸ pow_orderOf_eq_one x
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp x.2
    have hcr : Matrix.GeneralLinearGroup.scalar ι c ^ r = 1 := by
      rw [hc]
      simpa using congrArg (fun y : (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H =>
        ((y : H) : GL ι K)) hxr
    have hx1 : x = 1 := Subtype.ext (Subtype.ext (hc ▸ scalar_eq_one_of_pow_eq_one c hcr))
    rw [hx1, orderOf_one] at hx
    exact (Fact.out : r.Prime).one_lt.ne hx

end CFSG.LieType.BorelTits
