module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneCData
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bProps

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P58b

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem commute_of_commute_mul_central {G : Type*} [Group G] {y n z : G} (hn : n ∈ center G)
    (h : y * (n * z) = (n * z) * y) : y * z = z * y := by
  have h2 : n * y = y * n := ((mem_center_iff.mp hn) y).symm
  apply mul_left_cancel (a := n)
  calc n * (y * z) = (n * y) * z := by group
    _ = (y * n) * z := by rw [h2]
    _ = y * (n * z) := by group
    _ = (n * z) * y := h
    _ = n * (z * y) := by group

theorem nonempty_equiv_galoisField {p k : ℕ} [Fact p.Prime] (hk : k ≠ 0) {Y : Type} [Group Y]
    (h : IsSLTwoOver (p ^ k) Y) : Nonempty (Y ≃* SL(2, GaloisField p k)) := by
  obtain ⟨F, i₁, i₂, hF, ⟨e⟩⟩ := h
  have : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField p k) := by
    rw [hF, ← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  exact ⟨e.trans (Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
    (FiniteField.ringEquivOfCardEq hcard))⟩

theorem pPrimeCore_eq_of_quotient {R : Type*} [Group R] [Finite R] {N : Subgroup R} [N.Normal]
    (hN : Odd (Nat.card N)) {G : Type*} [Group G] [IsSimpleGroup G] (e : R ⧸ N ≃* G)
    (hnt : Nontrivial (R ⧸ pPrimeCore 2 R)) : pPrimeCore 2 R = N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNO : N ≤ pPrimeCore 2 R := le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hN⟩
  refine le_antisymm ?_ hNO
  have hMn : (((pPrimeCore 2 R).map (QuotientGroup.mk' N)).map e.toMonoidHom).Normal :=
    ((pPrimeCore_normal (p := 2) (G := R)).map _ (QuotientGroup.mk'_surjective N)).map _
      e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((pPrimeCore 2 R).map (QuotientGroup.mk' N)).map e.toMonoidHom) with h | h
  · intro x hx
    have h1 : e.toMonoidHom (QuotientGroup.mk' N x) ∈
        ((pPrimeCore 2 R).map (QuotientGroup.mk' N)).map e.toMonoidHom :=
      mem_map_of_mem _ (mem_map_of_mem _ hx)
    rw [h, mem_bot, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    have htop : (pPrimeCore 2 R).map (QuotientGroup.mk' N) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have h1 : e y ∈ ((pPrimeCore 2 R).map (QuotientGroup.mk' N)).map e.toMonoidHom := by
        rw [h]; exact mem_top _
      obtain ⟨w, hw, hwy⟩ := mem_map.mp h1
      rw [← e.injective hwy]
      exact hw
    apply not_subsingleton_iff_nontrivial.mpr hnt
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have hmem : ∀ x : R, x ∈ pPrimeCore 2 R := fun x => by
      have h1 : QuotientGroup.mk' N x ∈ (pPrimeCore 2 R).map (QuotientGroup.mk' N) :=
        htop ▸ mem_top _
      obtain ⟨w, hw, hwx⟩ := mem_map.mp h1
      have h2 : w⁻¹ * x ∈ N := QuotientGroup.eq.mp hwx
      have h3 : x = w * (w⁻¹ * x) := by group
      rw [h3]
      exact mul_mem hw (hNO h2)
    rw [(QuotientGroup.eq_one_iff a).mpr (hmem a), (QuotientGroup.eq_one_iff b).mpr (hmem b)]

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem normal_map_centralizer_of_ker {S : Type*} [Group S] (π : X →* S)
    (hπ : Function.Surjective π) (hker : π.ker = center X) (t : X) :
    (((centralizer {t}).map π).subgroupOf (centralizer {π t})).Normal := by
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  refine ⟨fun a ha b => ?_⟩
  rw [mem_subgroupOf] at ha ⊢
  obtain ⟨h, hh, hha⟩ := ha
  obtain ⟨y, hy⟩ := hπ b
  have hbt : π y * π t = π t * π y := by rw [hy]; exact mem_centralizer_singleton_iff.mp b.2
  have hz : y * t * y⁻¹ * t⁻¹ ∈ center X := by
    rw [← hπZ]
    simp only [map_mul, map_inv]
    rw [hbt]
    group
  have hht : h * t = t * h := mem_centralizer_singleton_iff.mp hh
  refine ⟨y * h * y⁻¹, ?_, ?_⟩
  · show y * h * y⁻¹ ∈ centralizer ({t} : Set X)
    rw [mem_centralizer_singleton_iff]
    refine commute_of_commute_mul_central hz ?_
    calc y * h * y⁻¹ * (y * t * y⁻¹ * t⁻¹ * t) = y * (h * t) * y⁻¹ := by group
      _ = y * (t * h) * y⁻¹ := by rw [hht]
      _ = y * t * y⁻¹ * t⁻¹ * t * (y * h * y⁻¹) := by group
  · rw [map_mul, map_mul, map_inv, hy, hha]
    rfl

theorem exists_psl2_component (hX : IsQuasisimple X) {S : Type} [Group S] [Finite S]
    (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = center X) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) :
    π t * π t = 1 ∧ π t ≠ 1 ∧ Q.map π ≤ centralizer {π t} ∧
      IsPComponent 2 ((Q.map π).subgroupOf (centralizer {π t})) ∧
      ∃ (N : Subgroup ↥(Q.map π)) (_ : N.Normal), Odd (Nat.card N) ∧
        Nonempty (↥(Q.map π) ⧸ N ≃* PSL(2, GaloisField p k)) := by
  obtain ⟨hc2, hcZ, ht2, htZ, hQ, hcQ, h5, hSL⟩ := hcfg
  have : Group.IsPerfect X := hX.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  obtain ⟨e⟩ := nonempty_equiv_galoisField hk hSL
  have hF2 : (2 : GaloisField p k) ≠ 0 := Burgoyne.C.two_ne_zero_galoisField hp2
  have hπZ : ∀ {x : X}, π x = 1 ↔ x ∈ center X := fun {x} => by rw [← MonoidHom.mem_ker, hker]
  have hQt : Q ≤ centralizer {t} := hQ.1
  have hQc : IsPComponent 2 (Q.subgroupOf (centralizer {t})) :=
    (isTwoComponentIn_iff hQt).mp hQ
  have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  have hxx : π t * π t = 1 := by rw [← map_mul, htt, map_one]
  have hx1 : π t ≠ 1 := fun h => htZ (hπZ.mp h)
  have hcent : ∀ {x : X}, x ∈ centralizer ({t} : Set X) → π x ∈ centralizer ({π t} : Set S) :=
    fun {x} hx => by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, hx, map_mul]
  have hRv : Q.map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent (hQt hx)
  have hH₁v : (centralizer {t}).map π ≤ centralizer {π t} := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcent hx
  let πH : ↥(centralizer ({t} : Set X)) →* ↥((centralizer ({t} : Set X)).map π) :=
    (π.comp (centralizer ({t} : Set X)).subtype).codRestrict _ fun h => ⟨h, h.2, rfl⟩
  have hπHs : Function.Surjective πH := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have hπHc : πH.ker ≤ center ↥(centralizer ({t} : Set X)) := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    exact mem_center_iff.2 fun y => Subtype.ext (mem_center_iff.1 hx' y)
  have hR₁ : IsPComponent 2 ((Q.map π).subgroupOf ((centralizer {t}).map π)) := by
    have h := CatalogueBCentralQuotient.pComponent_map 2 πH hπHs hπHc
      (Q.subgroupOf (centralizer {t})) hQc
    have heq : (Q.subgroupOf (centralizer {t})).map πH =
        (Q.map π).subgroupOf ((centralizer {t}).map π) := by
      ext ⟨y, hy⟩
      simp only [mem_map, mem_subgroupOf]
      constructor
      · rintro ⟨⟨x, hxH⟩, hxQ, hxy⟩
        exact ⟨x, hxQ, congrArg Subtype.val hxy⟩
      · rintro ⟨x, hxQ, rfl⟩
        exact ⟨⟨x, hQt hxQ⟩, hxQ, rfl⟩
    rwa [heq] at h
  have hRc : IsPComponent 2 ((Q.map π).subgroupOf (centralizer {π t})) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal (map_mono hQt) hH₁v
      (normal_map_centralizer_of_ker π hπ hker t).isSubnormal hR₁
  let πQ : ↥Q →* ↥(Q.map π) := (π.comp Q.subtype).codRestrict _ fun q => ⟨q, q.2, rfl⟩
  have hπQs : Function.Surjective πQ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let ψ : ↥Q →* PSL(2, GaloisField p k) :=
    (QuotientGroup.mk' (center SL(2, GaloisField p k))).comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore 2 ↥Q)))
  have hψs : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hcen : ∀ x : ↥Q, (x : X) ∈ center X →
      e (QuotientGroup.mk x) ∈ center SL(2, GaloisField p k) := by
    intro x hx
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥Q))) g
    change e (QuotientGroup.mk y) * e (QuotientGroup.mk x) =
      e (QuotientGroup.mk x) * e (QuotientGroup.mk y)
    have hxy : y * x = x * y := Subtype.ext (mem_center_iff.1 hx y)
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  have hle : πQ.ker ≤ ψ.ker := by
    intro x hx
    have hx' : π x = 1 := congrArg Subtype.val hx
    rw [hπZ] at hx'
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk (e (QuotientGroup.mk x)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hcen x hx'
  let φ : ↥(Q.map π) →* PSL(2, GaloisField p k) := (QuotientGroup.lift πQ.ker ψ hle).comp
    (QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm.toMonoidHom
  have hφ : ∀ x, φ (πQ x) = ψ x := fun x => by
    change QuotientGroup.lift πQ.ker ψ hle
      ((QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm (πQ x)) = ψ x
    rw [show (QuotientGroup.quotientKerEquivOfSurjective πQ hπQs).symm (πQ x) =
      QuotientGroup.mk x from (MulEquiv.symm_apply_eq _).2 rfl]
    rfl
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := hψs y
    exact ⟨πQ x, hφ x⟩
  set c' : ↥Q := ⟨c, hcQ⟩ with hc'
  have hc'2 : orderOf c' = 2 := by rw [Subgroup.orderOf_mk]; exact hc2
  have hc'O := Burgoyne.C.not_mem_pPrimeCore_of_orderOf hc'2
  have hec : e (QuotientGroup.mk c') = -1 := by
    have hcc : c' * c' = 1 := by
      have := pow_orderOf_eq_one c'
      rwa [hc'2, pow_two] at this
    have hsq : e (QuotientGroup.mk c') * e (QuotientGroup.mk c') = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, hcc, QuotientGroup.mk_one, map_one]
    rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 _ hsq with h1 | h1
    · exfalso
      rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact hc'O h1
    · exact h1
  have hker' : φ.ker ≤ (pPrimeCore 2 ↥Q).map πQ := by
    intro r hr
    obtain ⟨x, rfl⟩ := hπQs r
    rw [MonoidHom.mem_ker, hφ] at hr
    change QuotientGroup.mk (e (QuotientGroup.mk x)) = 1 at hr
    rw [QuotientGroup.eq_one_iff] at hr
    rcases Burgoyne.C.eq_one_or_eq_neg_one hF2 _ (by
      rw [← pow_two]; exact Burgoyne.C.sq_eq_one_of_mem_center_SL hr) with h1 | h1
    · rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at h1
      exact ⟨x, h1, rfl⟩
    · rw [← hec] at h1
      have h1' := QuotientGroup.eq.1 (e.injective h1)
      refine ⟨c'⁻¹ * x, ?_, ?_⟩
      · have := inv_mem h1'
        rwa [mul_inv_rev, inv_inv] at this
      · rw [map_mul, map_inv]
        have hπc : πQ c' = 1 := Subtype.ext ((hπZ).2 hcZ)
        rw [hπc, inv_one, one_mul]
  refine ⟨hxx, hx1, hRv, hRc, φ.ker, inferInstance, ?_,
    ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφs⟩⟩
  have hodd : Odd (Nat.card ((pPrimeCore 2 ↥Q).map πQ)) :=
    Odd.of_dvd_nat Burgoyne.C.odd_card_pPrimeCore (Subgroup.card_map_dvd _ _)
  exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hker')

theorem exists_psl2_lieModel_component (hX : IsQuasisimple X) {S : Type} [Group S] [Finite S]
    (π : X →* S) (hπ : Function.Surjective π) (hker : π.ker = center X) {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {c t : X} {Q : Subgroup X}
    (hcfg : Lemma58bConfig X p k c t Q) :
    π t * π t = 1 ∧ π t ≠ 1 ∧ ∃ J : Subgroup ↥(centralizer ({π t} : Set S)),
      IsPComponent 2 J ∧ Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  obtain ⟨hxx, hx1, hRv, hRc, N, hN, hNodd, ⟨eN⟩⟩ :=
    exists_psl2_component hX π hπ hker hp2 hcfg
  refine ⟨hxx, hx1, (Q.map π).subgroupOf (centralizer {π t}), hRc, ?_⟩
  have hk : k ≠ 0 := by
    rintro rfl
    simp at h5
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  have hsimple : IsSimpleGroup PSL(2, GaloisField p k) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 (GaloisField p k) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  let eJ : ↥((Q.map π).subgroupOf (centralizer {π t})) ≃* ↥(Q.map π) :=
    Subgroup.subgroupOfEquivOfLe hRv
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).1
    hRc
  have hqR : IsQuasisimple (↥(Q.map π) ⧸ pPrimeCore 2 ↥(Q.map π)) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hq
  have hO : pPrimeCore 2 ↥(Q.map π) = N :=
    pPrimeCore_eq_of_quotient hNodd eN (LocalCores.isQuasisimple_nontrivial hqR)
  let e₁ : ↥((Q.map π).subgroupOf (centralizer {π t})) ⧸
      pPrimeCore 2 ↥((Q.map π).subgroupOf (centralizer {π t})) ≃*
        PSL(2, GaloisField p k) :=
    (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)).trans
      ((QuotientGroup.quotientMulEquivOfEq hO).trans eN)
  exact Or.inl ⟨by decide, statedClassicalModel_psl_two_of_mulEquiv _ p k h5 e₁⟩

end CFSG.ComponentClassification.HarrisLit.T1.P58b
