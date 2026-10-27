module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Tools
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt41
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.SubAbs

open Subgroup CFSG CFSG.LocalCores
open scoped commutatorElement

section PrimeCore

variable {G : Type} [Group G] [Finite G]

theorem pPrimeCore_odd : Odd (Nat.card (pPrimeCore 2 G)) :=
  Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))

omit [Finite G] in
theorem le_pPrimeCore_of_odd (K : Subgroup G) [K.Normal] (hK : Odd (Nat.card K)) :
    K ≤ pPrimeCore 2 G :=
  le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hK⟩

theorem pPrimeCore_solvable : Group.IsSolvable (pPrimeCore 2 G) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ pPrimeCore_odd

theorem pPrimeCore_quotient_eq_bot : pPrimeCore 2 (G ⧸ pPrimeCore 2 G) = ⊥ := by
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 G)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  have h := (prime_complement_kernel_core_preimage (p := 2) (QuotientGroup.mk' (pPrimeCore 2 G))
    (QuotientGroup.mk'_surjective _) hker).1
  refine Subgroup.comap_injective (QuotientGroup.mk'_surjective (pPrimeCore 2 G)) ?_
  rw [h, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem pCore_quotient_eq_bot {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    pCore p (G ⧸ pPrimeCore 2 G) = ⊥ := by
  have hle : pCore p (G ⧸ pPrimeCore 2 G) ≤ pPrimeCore 2 (G ⧸ pPrimeCore 2 G) := by
    have : (pCore p (G ⧸ pPrimeCore 2 G)).Normal := pCore_normal
    refine le_pPrimeCore_of_odd _ ?_
    have hpg : IsPGroup p ↥(pCore p (G ⧸ pPrimeCore 2 G)) := pCore_isPGroup
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := ↥(pCore p (G ⧸ pPrimeCore 2 G)))).mp hpg
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow
  rw [pPrimeCore_quotient_eq_bot (G := G)] at hle
  exact le_bot_iff.mp hle

end PrimeCore

section Generic

theorem normal_of_le_center {Q : Type*} [Group Q] (H : Subgroup Q) (hH : H ≤ center Q) :
    H.Normal :=
  ⟨fun n hn g => by rw [mem_center_iff.mp (hH hn) g, mul_inv_cancel_right]; exact hn⟩

theorem isSolvable_of_sup_zpowers_eq_top {Q : Type*} [Group Q] {X : Subgroup Q}
    [Group.IsSolvable X] {t : Q} (ht : t ∈ normalizer (X : Set Q)) (hgen : X ⊔ zpowers t = ⊤) :
    Group.IsSolvable Q := by
  have hXn : X.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hgen]
    exact sup_le le_normalizer (zpowers_le.mpr ht)
  have hquot : Group.IsSolvable (Q ⧸ X) := by
    refine Group.isSolvable_of_surjective (G := zpowers t)
      (f := (QuotientGroup.mk' X).comp (zpowers t).subtype) ?_
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ ((zpowers t ⊔ X : Subgroup Q) : Set Q) := by
      rw [sup_comm, hgen]; exact mem_top g
    rw [Subgroup.mul_normal] at hg
    obtain ⟨a, ha, x, hx, rfl⟩ := hg
    refine ⟨⟨a, ha⟩, ?_⟩
    simp [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).mpr hx]
  exact Group.isSolvable_of_ker_le_range X.subtype (QuotientGroup.mk' X)
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem perfect_le_of_solvable_quotient {Q : Type*} [Group Q] {K : Subgroup Q} [K.Normal]
    (hS : Group.IsSolvable (Q ⧸ K)) {A : Subgroup Q} (hA : Group.IsPerfect A) : A ≤ K := by
  have hperf : Group.IsPerfect (A.map (QuotientGroup.mk' K)) :=
    Group.IsPerfect.map (QuotientGroup.mk' K)
  have hsolv : Group.IsSolvable (A.map (QuotientGroup.mk' K)) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  have hbot : A.map (QuotientGroup.mk' K) = ⊥ := by
    by_contra hne
    have : Nontrivial (A.map (QuotientGroup.mk' K)) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isSolvable _ hsolv
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

end Generic

section Center

variable {Q : Type} [Group Q] [Finite Q]

theorem center_le_pCore_of_pPrimeCore_eq_bot (hQ : pPrimeCore 2 Q = ⊥) : center Q ≤ pCore 2 Q := by
  have hpg : IsPGroup 2 ↥(center Q) := by
    rw [IsPGroup.iff_orderOf]
    intro c
    rw [← Subgroup.orderOf_coe]
    have hc : (c : Q) ∈ center Q := c.2
    have hn0 : orderOf (c : Q) ≠ 0 := (orderOf_pos (c : Q)).ne'
    obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
    set v : Q := (c : Q) ^ (2 ^ k) with hv
    have hvc : v ∈ center Q := Subgroup.pow_mem _ hc _
    have hvm : v ^ m = 1 := by
      rw [hv, ← pow_mul, ← hn]
      exact pow_orderOf_eq_one _
    have hodd : Odd (Nat.card (zpowers v)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hvm)
    have hnormal : (zpowers v).Normal := normal_of_le_center _ (zpowers_le.mpr hvc)
    have hle := le_pPrimeCore_of_odd (zpowers v) hodd
    rw [hQ] at hle
    have hv1 : v = 1 := Subgroup.mem_bot.mp (hle (mem_zpowers v))
    have hdvd : orderOf (c : Q) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hv1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  exact le_sSup ⟨inferInstance, hpg⟩

theorem pCore_le_center_of_quasisimple (hq : IsQuasisimple Q) : pCore 2 Q ≤ center Q := by
  rcases quasisimple_normal_subgroups hq (pCore_normal (p := 2) (G := Q)) with h | h
  · exfalso
    have hpg : IsPGroup 2 ↥(pCore 2 Q) := pCore_isPGroup
    rw [h] at hpg
    have hpg' : IsPGroup 2 Q := hpg.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent Q := hpg'.isNilpotent
    have : Nontrivial Q := isQuasisimple_nontrivial hq
    have := hq.1
    exact Group.IsPerfect.not_isSolvable Q inferInstance
  · exact h

end Center

section JN

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCore_le_centralizer {J : Subgroup G} [J.Normal] (hq : IsQuasisimple ↥J) :
    J ⊓ pPrimeCore 2 G ≤ centralizer (J : Set G) := by
  set S : Subgroup ↥J := (pPrimeCore 2 G).subgroupOf J with hS
  have hSn : S.Normal := inferInstance
  have hSodd : Odd (Nat.card S) := by
    have hle : S.map J.subtype ≤ pPrimeCore 2 G := by
      rintro _ ⟨s, hs, rfl⟩
      exact hs
    have hcard : Nat.card ↥(S.map J.subtype) = Nat.card ↥S :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [← hcard]
    exact Odd.of_dvd_nat pPrimeCore_odd (Subgroup.card_dvd_of_le hle)
  rcases quasisimple_normal_subgroups hq hSn with h | h
  · exfalso
    have hJN : J ≤ pPrimeCore 2 G := fun x hx => by
      have : (⟨x, hx⟩ : ↥J) ∈ S := by rw [h]; exact mem_top _
      exact this
    have := pPrimeCore_solvable (G := G)
    have hsolv : Group.IsSolvable ↥J :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJN)
    have := isQuasisimple_nontrivial hq
    have := hq.1
    exact Group.IsPerfect.not_isSolvable ↥J hsolv
  · rintro x ⟨hxJ, hxN⟩
    rw [mem_centralizer_iff]
    intro y hy
    have hx : (⟨x, hxJ⟩ : ↥J) ∈ center ↥J := h hxN
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

theorem commutator_eq_bot_of_le_pPrimeCore {J : Subgroup G} [J.Normal] (hq : IsQuasisimple ↥J)
    {K : Subgroup G} (hK : ⁅J, K⁆ ≤ pPrimeCore 2 G) : ⁅J, K⁆ = ⊥ := by
  have h1 : ⁅J, K⁆ ≤ J ⊓ pPrimeCore 2 G := le_inf (Subgroup.commutator_le_left J K) hK
  have h2 : ⁅⁅J, K⁆, J⁆ = ⊥ :=
    le_bot_iff.mp <| (commutator_mono h1 le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr (inf_pPrimeCore_le_centralizer hq)).le
  exact perfect_double_commutator hq.1 h2

theorem inf_pPrimeCore_le_centralizer' {J : Subgroup G} [J.Normal] (hq : IsQuasisimple ↥J)
    (K : Subgroup G) : K ⊓ pPrimeCore 2 G ≤ centralizer (J : Set G) := by
  have h1 : ⁅J, K ⊓ pPrimeCore 2 G⁆ ≤ pPrimeCore 2 G :=
    (commutator_mono le_rfl inf_le_right).trans (Subgroup.commutator_le_right J (pPrimeCore 2 G))
  have h2 := commutator_eq_bot_of_le_pPrimeCore hq h1
  rw [Subgroup.commutator_comm] at h2
  exact commutator_eq_bot_iff_le_centralizer.mp h2

end JN

section Abs

variable {G : Type} [Group G]

structure AbsHyp (t : G) (p : ℕ) (X J : Subgroup G) : Prop where
  A4 : Sig4A t (⊤ : Subgroup G) p X
  t2 : t * t = 1
  normal : J.Normal
  quasi : IsQuasisimple ↥J
  gen : J ⊔ X ⊔ zpowers t = ⊤
  JX : ⁅J, X⁆ ≠ ⊥

variable {t : G} {p : ℕ} {X J : Subgroup G}

theorem normal_centralizer_inf (h : AbsHyp t p X J) : (centralizer (J : Set G) ⊓ X).Normal := by
  have hJn : J.Normal := h.normal
  have hDn : (centralizer (J : Set G)).Normal := normal_centralizer_of_normal J
  have htX : t ∈ normalizer (X : Set G) := z_mem_normalizer_of_sig4A h.A4
  have key : ∀ g ∈ normalizer (X : Set G),
      g ∈ normalizer ((centralizer (J : Set G) ⊓ X : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff] at hg ⊢
    intro x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hDn.conj_mem x hx1 g, (hg x).mp hx2⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨?_, (hg x).mpr hx2⟩
      have := hDn.conj_mem _ hx1 g⁻¹
      simpa [mul_assoc] using this
  rw [← normalizer_eq_top_iff, eq_top_iff, ← h.gen]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine le_trans ?_ (centralizer_le_normalizer _)
    intro j hj
    rw [mem_centralizer_iff]
    intro d hd
    exact (mem_centralizer_iff.mp hd.1 j hj).symm
  · exact fun x hx => key x (le_normalizer hx)
  · exact zpowers_le.mpr (key t htX)

theorem centralizer_inf_le_pPrimeCore [Finite G] (h : AbsHyp t p X J) :
    centralizer (J : Set G) ⊓ X ≤ pPrimeCore 2 G := by
  have := normal_centralizer_inf h
  refine le_pPrimeCore_of_odd _ ?_
  have : Fact p.Prime := ⟨h.A4.prime⟩
  have hX := h.A4.pgroup.to_le (inf_le_right : centralizer (J : Set G) ⊓ X ≤ X)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (G := ↥(centralizer (J : Set G) ⊓ X))).mp hX
  rw [hn]
  exact (h.A4.prime.odd_of_ne_two h.A4.odd).pow

theorem mk_eq_one_iff_of_mem [Finite G] (h : AbsHyp t p X J) {x : G} (hx : x ∈ X) :
    (QuotientGroup.mk x : G ⧸ pPrimeCore 2 G) = 1 ↔ x ∈ centralizer (J : Set G) := by
  have := h.normal
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro hxN
    exact inf_pPrimeCore_le_centralizer' h.quasi X ⟨hx, hxN⟩
  · intro hxc
    exact centralizer_inf_le_pPrimeCore h ⟨hxc, hx⟩

theorem map_X_ne_bot [Finite G] (h : AbsHyp t p X J) :
    X.map (QuotientGroup.mk' (pPrimeCore 2 G)) ≠ ⊥ := by
  intro hbot
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  have := h.normal
  have hX : X ≤ centralizer (J : Set G) := fun x hx =>
    inf_pPrimeCore_le_centralizer' h.quasi X ⟨hx, hbot hx⟩
  exact h.JX (by rw [Subgroup.commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hX)

theorem sig4A_quotient [Finite G] (h : AbsHyp t p X J) :
    Sig4A (QuotientGroup.mk t : G ⧸ pPrimeCore 2 G) (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) p
      (X.map (QuotientGroup.mk' (pPrimeCore 2 G))) where
  prime := h.A4.prime
  odd := h.A4.odd
  z_mem := mem_top _
  X_le := le_top
  pgroup := h.A4.pgroup.map _
  ne_bot := map_X_ne_bot h
  inv := by
    intro c _ hc
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : (QuotientGroup.mk c' : G ⧸ pPrimeCore 2 G) * QuotientGroup.mk t =
        QuotientGroup.mk t * QuotientGroup.mk c' := mem_centralizer_singleton_iff.mp hc
    have hmem : t * c' * t⁻¹ * c'⁻¹ ∈ pPrimeCore 2 G := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hc']
      group
    obtain ⟨n, hn, hfix⟩ := exists_fixed_of_odd_coset (pPrimeCore 2 G) pPrimeCore_odd t h.t2 c' hmem
    have hc'' : c' * n ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc c' * n * t = (t * (c' * n) * t⁻¹) * t := by rw [hfix]
        _ = t * (c' * n) := by group
    have hnorm := h.A4.inv (c' * n) (mem_top _) hc''
    have hmk : (QuotientGroup.mk (c' * n) : G ⧸ pPrimeCore 2 G) = QuotientGroup.mk c' := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
    rw [← hmk]
    exact le_normalizer_map (QuotientGroup.mk' (pPrimeCore 2 G)) (mem_map_of_mem _ hnorm)
  comm := by
    have e : zpowers (QuotientGroup.mk t : G ⧸ pPrimeCore 2 G) =
        (zpowers t).map (QuotientGroup.mk' (pPrimeCore 2 G)) :=
      (MonoidHom.map_zpowers (QuotientGroup.mk' (pPrimeCore 2 G)) t).symm
    rw [e, ← Subgroup.map_commutator, h.A4.comm]

theorem map_J_normal (h : AbsHyp t p X J) :
    (J.map (QuotientGroup.mk' (pPrimeCore 2 G))).Normal := by
  have := h.normal
  exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)

theorem not_J_le_pPrimeCore [Finite G] (h : AbsHyp t p X J) : ¬ J ≤ pPrimeCore 2 G := by
  intro hle
  have := pPrimeCore_solvable (G := G)
  have hsolv : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have := isQuasisimple_nontrivial h.quasi
  have := h.quasi.1
  exact Group.IsPerfect.not_isSolvable ↥J hsolv

theorem quasi_map_J [Finite G] (h : AbsHyp t p X J) :
    IsQuasisimple ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 G))) :=
  isQuasisimple_map h.quasi _ (by rw [QuotientGroup.ker_mk']; exact not_J_le_pPrimeCore h)

theorem isComponent_map_J [Finite G] (h : AbsHyp t p X J) :
    IsComponent (J.map (QuotientGroup.mk' (pPrimeCore 2 G))) :=
  ⟨quasi_map_J h, (map_J_normal h).isSubnormal⟩

theorem gen_quotient (h : AbsHyp t p X J) :
    J.map (QuotientGroup.mk' (pPrimeCore 2 G)) ⊔ X.map (QuotientGroup.mk' (pPrimeCore 2 G)) ⊔
      zpowers (QuotientGroup.mk t : G ⧸ pPrimeCore 2 G) = ⊤ := by
  have e : zpowers (QuotientGroup.mk t : G ⧸ pPrimeCore 2 G) =
      (zpowers t).map (QuotientGroup.mk' (pPrimeCore 2 G)) :=
    (MonoidHom.map_zpowers (QuotientGroup.mk' (pPrimeCore 2 G)) t).symm
  rw [e, ← Subgroup.map_sup, ← Subgroup.map_sup, h.gen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem layer_quotient [Finite G] (h : AbsHyp t p X J) :
    layer (G ⧸ pPrimeCore 2 G) = J.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
  have hJn := map_J_normal h
  refine le_antisymm (sSup_le fun C hC => ?_) (component_le_layer (isComponent_map_J h))
  have hsolv : Group.IsSolvable
      ((G ⧸ pPrimeCore 2 G) ⧸ J.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
    let π₂ : (G ⧸ pPrimeCore 2 G) →*
        (G ⧸ pPrimeCore 2 G) ⧸ J.map (QuotientGroup.mk' (pPrimeCore 2 G)) := QuotientGroup.mk' _
    have : Fact p.Prime := ⟨h.A4.prime⟩
    have hpg : IsPGroup p ↥((X.map (QuotientGroup.mk' (pPrimeCore 2 G))).map π₂) :=
      (h.A4.pgroup.map _).map _
    have : Group.IsNilpotent ↥((X.map (QuotientGroup.mk' (pPrimeCore 2 G))).map π₂) :=
      hpg.isNilpotent
    refine isSolvable_of_sup_zpowers_eq_top
      (X := (X.map (QuotientGroup.mk' (pPrimeCore 2 G))).map π₂)
      (t := π₂ (QuotientGroup.mk t)) ?_ ?_
    · exact le_normalizer_map π₂
        (mem_map_of_mem π₂ (z_mem_normalizer_of_sig4A (sig4A_quotient h)))
    · have h1 := congrArg (Subgroup.map π₂) (gen_quotient h)
      rwa [Subgroup.map_sup, Subgroup.map_sup,
        (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge, bot_sup_eq,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
        MonoidHom.map_zpowers] at h1
  exact perfect_le_of_solvable_quotient hsolv hC.1.1

theorem pPrimeCore_map_J_eq_bot [Finite G] (h : AbsHyp t p X J) :
    pPrimeCore 2 ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 G))) = ⊥ := by
  have := map_J_normal h
  set Jb := J.map (QuotientGroup.mk' (pPrimeCore 2 G)) with hJb
  set K := pPrimeCore 2 ↥Jb with hK
  have hKn : (K.map Jb.subtype).Normal := inferInstance
  have hKodd : Odd (Nat.card (K.map Jb.subtype)) := by
    rw [Subgroup.card_map_of_injective Jb.subtype_injective]
    exact pPrimeCore_odd
  have hle := le_pPrimeCore_of_odd (K.map Jb.subtype) hKodd
  rw [pPrimeCore_quotient_eq_bot (G := G)] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ Jb.subtype_injective).mp (le_bot_iff.mp hle)

theorem not_commutator_le_center [Finite G] (h : AbsHyp t p X J) :
    ¬ ⁅J.map (QuotientGroup.mk' (pPrimeCore 2 G)), X.map (QuotientGroup.mk' (pPrimeCore 2 G))⁆ ≤
      (center ↥(J.map (QuotientGroup.mk' (pPrimeCore 2 G)))).map
        (J.map (QuotientGroup.mk' (pPrimeCore 2 G))).subtype := by
  intro hle
  set Jb := J.map (QuotientGroup.mk' (pPrimeCore 2 G)) with hJb
  have h1 : ⁅⁅Jb, X.map (QuotientGroup.mk' (pPrimeCore 2 G))⁆, Jb⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅Jb, X.map (QuotientGroup.mk' (pPrimeCore 2 G))⁆, Jb⁆
        ≤ ⁅(center ↥Jb).map Jb.subtype, Jb⁆ := commutator_mono hle le_rfl
      _ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
          (fun z hz => ((mem_map_center_iff Jb).mp hz).2)
      _ ≤ ⊥ := le_rfl
  have h2 : ⁅Jb, X.map (QuotientGroup.mk' (pPrimeCore 2 G))⁆ = ⊥ :=
    perfect_double_commutator (quasi_map_J h).1 h1
  have h3 : ⁅J, X⁆ ≤ pPrimeCore 2 G := by
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 G), ← Subgroup.map_eq_bot_iff,
      Subgroup.map_commutator]
    exact h2
  have := h.normal
  exact h.JX (commutator_eq_bot_of_le_pPrimeCore h.quasi h3)

theorem hyp42_quotient [Finite G] (h : AbsHyp t p X J) :
    Hyp42 (QuotientGroup.mk t : G ⧸ pPrimeCore 2 G)
      (X.map (QuotientGroup.mk' (pPrimeCore 2 G))) := by
  unfold Hyp42
  rw [layer_quotient h]
  refine ⟨gen_quotient h, quasi_map_J h, ?_, not_commutator_le_center h⟩
  exact le_antisymm (center_le_pCore_of_pPrimeCore_eq_bot (pPrimeCore_map_J_eq_bot h))
    (pCore_le_center_of_quasisimple (quasi_map_J h))

theorem equiv_map_J [Finite G] (h : AbsHyp t p X J) :
    Nonempty (↥(J.map (QuotientGroup.mk' (pPrimeCore 2 G))) ≃* (↥J ⧸ pPrimeCore 2 ↥J)) := by
  have hJn := h.normal
  let f : ↥J →* G ⧸ pPrimeCore 2 G := (QuotientGroup.mk' (pPrimeCore 2 G)).comp J.subtype
  have hrange : f.range = J.map (QuotientGroup.mk' (pPrimeCore 2 G)) := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  have hker : f.ker = pPrimeCore 2 ↥J := by
    apply le_antisymm
    · have hle : f.ker.map J.subtype ≤ pPrimeCore 2 G := by
        rintro _ ⟨κ, hκ, rfl⟩
        have : QuotientGroup.mk' (pPrimeCore 2 G) (κ : G) = 1 := hκ
        exact (QuotientGroup.eq_one_iff _).mp this
      have hodd : Odd (Nat.card f.ker) := by
        rw [← Subgroup.card_map_of_injective J.subtype_injective (K := f.ker)]
        exact Odd.of_dvd_nat pPrimeCore_odd (Subgroup.card_dvd_of_le hle)
      exact le_pPrimeCore_of_odd f.ker hodd
    · have hKn : ((pPrimeCore 2 ↥J).map J.subtype).Normal := inferInstance
      have hodd : Odd (Nat.card ((pPrimeCore 2 ↥J).map J.subtype)) := by
        rw [Subgroup.card_map_of_injective J.subtype_injective]
        exact pPrimeCore_odd
      have hle := le_pPrimeCore_of_odd _ hodd
      intro κ hκ
      have : (κ : G) ∈ pPrimeCore 2 G := hle (mem_map_of_mem _ hκ)
      exact (QuotientGroup.eq_one_iff _).mpr this
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans (QuotientGroup.quotientMulEquivOfEq hker))⟩

end Abs

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.SubAbs
