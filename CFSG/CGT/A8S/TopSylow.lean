module

public import CFSG.CGT.A8S.LocalStmt
public import CFSG.CGT.T75P.A8ExclCfg
public import CFSG.CGT.T75P.Aut

public section

namespace CFSG.CGT.A8S

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {G : Type} [Group G] {T H : Subgroup G}

namespace TopSylow

theorem exists_linearization (hN : NaturalSL T H 3 1) :
    ∃ (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) (ρ : ↥H →* SL(3, GaloisField 2 1)),
      Function.Surjective ρ ∧
      ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
        Multiplicative.toAdd (φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩) =
          ρ h • Multiplicative.toAdd (φ t) := by
  obtain ⟨hn, e, φ, hc⟩ := hN
  refine ⟨φ, e.toMonoidHom.comp (QuotientGroup.mk' _),
    e.surjective.comp (QuotientGroup.mk'_surjective _), fun h t hmem => ?_⟩
  rw [hc h t hmem, toAdd_ofAdd]
  rfl

theorem mk_eq_mk_iff {v w : Fin 3 → GaloisField 2 1} (hv : v ≠ 0) (hw : w ≠ 0) :
    Projectivization.mk (GaloisField 2 1) v hv = Projectivization.mk (GaloisField 2 1) w hw ↔
      v = w := by
  rw [Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, rfl⟩
    have ha : (a : GaloisField 2 1) = 1 :=
      (CFSG.CGT.T75P.galoisField_two_one_eq (a : GaloisField 2 1)).resolve_left a.ne_zero
    rw [Units.smul_def, ha, one_smul]
  · rintro rfl
    exact ⟨1, one_smul _ _⟩

theorem card_projectivization :
    Nat.card (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)) = 7 := by
  have h := Projectivization.card (GaloisField 2 1) (Fin 3 → GaloisField 2 1)
  have hF : Nat.card (GaloisField 2 1) = 2 := by simpa using GaloisField.card 2 1 one_ne_zero
  rw [Nat.card_fun, hF, Nat.card_fin] at h
  omega

theorem index_fixingSubgroup {v w : Fin 3 → GaloisField 2 1} (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ≠ w) :
    (fixingSubgroup SL(3, GaloisField 2 1) ({Projectivization.mk (GaloisField 2 1) v hv,
      Projectivization.mk (GaloisField 2 1) w hw} :
        Set (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)))).index = 42 := by
  have hne : Projectivization.mk (GaloisField 2 1) v hv ≠
      Projectivization.mk (GaloisField 2 1) w hw := by
    rwa [Ne, mk_eq_mk_iff]
  have h2 := Set.ncard_pair hne
  rw [MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq _ (by rw [h2]; infer_instance),
    h2, card_projectivization]
  rfl

theorem toAdd_ne_zero (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) {t : G}
    (ht : t ∈ T) (ht1 : t ≠ 1) : Multiplicative.toAdd (φ ⟨t, ht⟩) ≠ 0 := by
  intro h
  rw [toAdd_eq_zero, MulEquiv.map_eq_one_iff] at h
  exact ht1 (congrArg Subtype.val h)

theorem toAdd_injective (φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)) {s t : G}
    (hs : s ∈ T) (ht : t ∈ T) (hst : s ≠ t) :
    Multiplicative.toAdd (φ ⟨s, hs⟩) ≠ Multiplicative.toAdd (φ ⟨t, ht⟩) := fun h =>
  hst (congrArg Subtype.val (φ.injective (Multiplicative.toAdd.injective h)))

theorem mem_centralizer_iff_smul_eq {φ : ↥T ≃* Multiplicative (Fin 3 → GaloisField 2 1)}
    {ρ : ↥H →* SL(3, GaloisField 2 1)} (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hc : ∀ (h : ↥H) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
      Multiplicative.toAdd (φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩) =
        ρ h • Multiplicative.toAdd (φ t))
    (h : ↥H) {t : G} (ht : t ∈ T) :
    (h : G) ∈ Subgroup.centralizer ({t} : Set G) ↔
      ρ h • Multiplicative.toAdd (φ ⟨t, ht⟩) = Multiplicative.toAdd (φ ⟨t, ht⟩) := by
  rw [Subgroup.mem_centralizer_singleton_iff,
    ← hc h ⟨t, ht⟩ (conj_mem_of_mem_normalizer (hHN h.2) ht), EmbeddingLike.apply_eq_iff_eq,
    EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq, mul_inv_eq_iff_eq_mul]

theorem card_inf_centralizer_pair (h : A8Hyp T H) {v w : G} (hv : v ∈ T) (hv1 : v ≠ 1)
    (hw : w ∈ T) (hw1 : w ≠ 1) (hvw : v ≠ w) :
    Nat.card ↥(H ⊓ Subgroup.centralizer ({v} : Set G) ⊓
      Subgroup.centralizer ({w} : Set G)) = 32 := by
  have c : CFSG.CGT.T75P.A8Cfg T H := ⟨h.le, h.wc, h.nat, h.compl, h.odd⟩
  obtain ⟨φ, ρ, hρ, hc⟩ := exists_linearization h.nat
  have hHN := c.le_normalizer
  have hv0 := toAdd_ne_zero φ hv hv1
  have hw0 := toAdd_ne_zero φ hw hw1
  set X := H ⊓ Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) with hX
  have hsub : X.subgroupOf H = (fixingSubgroup SL(3, GaloisField 2 1)
      ({Projectivization.mk (GaloisField 2 1) _ hv0, Projectivization.mk (GaloisField 2 1) _ hw0} :
        Set (Projectivization (GaloisField 2 1) (Fin 3 → GaloisField 2 1)))).comap ρ := by
    ext h
    simp only [hX, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
      mem_fixingSubgroup_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq]
    rw [Projectivization.smul_mk, Projectivization.smul_mk, mk_eq_mk_iff, mk_eq_mk_iff,
      ← mem_centralizer_iff_smul_eq hHN hc h hv, ← mem_centralizer_iff_smul_eq hHN hc h hw]
    exact ⟨fun h' => ⟨h'.1.2, h'.2⟩, fun h' => ⟨⟨h.2, h'.1⟩, h'.2⟩⟩
  have hidx : (X.subgroupOf H).index = 42 := by
    rw [hsub, Subgroup.index_comap_of_surjective _ hρ,
      index_fixingSubgroup hv0 hw0 (toAdd_injective φ hv hw hvw)]
  have h1 := Subgroup.card_mul_index (X.subgroupOf H)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv,
    c.card_H] at h1
  rw [hX]
  omega

theorem factorization_two_eq_six {m : ℕ} (hm : Odd m) : (1344 * m).factorization 2 = 6 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have h21 : ¬ 2 ∣ 21 * m := (Odd.mul (by decide) hm).not_two_dvd_nat
  rw [show 1344 * m = 2 ^ 6 * (21 * m) by ring,
    Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h21, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self]
  rfl

end TopSylow

open TopSylow in
theorem exists_sylow_of_a8Hyp [Finite G] (h : A8Hyp T H) :
    ∃ S : Sylow 2 G, T ≤ (S : Subgroup G) ∧ Nat.card S = 2 ^ 6 ∧ ∃ z ∈ T, z ≠ 1 ∧
      ∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z)) := by
  classical
  have c : CFSG.CGT.T75P.A8Cfg T H := ⟨h.le, h.wc, h.nat, h.compl, h.odd⟩
  have hTH := h.le
  have hN' := h.nat
  obtain ⟨hn, -, -, -⟩ := hN'
  obtain ⟨S₀⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥H))
  have hS₁card : Nat.card ((S₀ : Subgroup ↥H).map H.subtype) =
      2 ^ (Nat.card G).factorization 2 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity,
      ← H.card_mul_index, c.card_H, factorization_two_eq_six h.odd,
      ← factorization_two_eq_six odd_one, mul_one]
  set S : Sylow 2 G := Sylow.ofCard _ hS₁card with hSdef
  have hS : (S : Subgroup G) = (S₀ : Subgroup ↥H).map H.subtype := Sylow.coe_ofCard _ _
  have hSH : (S : Subgroup G) ≤ H := hS ▸ Subgroup.map_subtype_le _
  have hTS : T ≤ (S : Subgroup G) := by
    have hTp : IsPGroup 2 (T.subgroupOf H) := IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, c.card_T]
      rfl)
    have hle := hTp.le_sylow_of_normal S₀
    intro t ht
    rw [hS]
    exact ⟨⟨t, hTH ht⟩, hle (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hcentT : ∀ x ∈ (S : Subgroup G), (∀ y ∈ (S : Subgroup G), x * y = y * x) → x ∈ T := by
    intro x hx hxc
    rw [← CFSG.CGT.T75P.inf_centralizer_eq_of_natural hTH c.le_normalizer h.nat]
    exact ⟨hSH hx, Subgroup.mem_centralizer_iff.2 fun t ht => (hxc t (hTS ht)).symm⟩
  have hcardS : Nat.card S = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, ← H.card_mul_index, c.card_H, factorization_two_eq_six h.odd]
  have : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardS]
    norm_num
  have := S.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥(S : Subgroup G)))
  have hzc : ∀ y ∈ (S : Subgroup G), ((z : ↥(S : Subgroup G)) : G) * y = y * z := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩)).symm
  have hz0 : ((z : ↥(S : Subgroup G)) : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzT := hcentT _ (z : ↥(S : Subgroup G)).2 hzc
  refine ⟨S, hTS, hcardS, _, hzT, hz0, fun x hx => ⟨fun hxc => ?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨hx1, hxz⟩ := not_or.1 hne
    have hxT := hcentT x hx hxc
    have hle : (S : Subgroup G) ≤ H ⊓ Subgroup.centralizer ({((z : ↥(S : Subgroup G)) : G)} :
        Set G) ⊓ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      ⟨⟨hSH hy, Subgroup.mem_centralizer_singleton_iff.2 (hzc y hy).symm⟩,
        Subgroup.mem_centralizer_singleton_iff.2 (hxc y hy).symm⟩
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hcardS, card_inf_centralizer_pair h hzT hz0 hxT hx1 (Ne.symm hxz)] at hdvd
    norm_num at hdvd
  · rintro (rfl | rfl)
    · exact fun y _ => by rw [one_mul, mul_one]
    · exact hzc

end CFSG.CGT.A8S
