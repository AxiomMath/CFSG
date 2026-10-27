module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormalizerQuotient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.TwoCore
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.RankTwoShapes

variable {G : Type*} [Group G]

theorem pCore_normalizer_quotient_eq_bot [Finite G] {p : ℕ} [Fact p.Prime] (Q : Subgroup G)
    (hrad : ∀ R : Subgroup G, Q ⊔ Subgroup.centralizer (Q : Set G) ≤ R →
      R ≤ Subgroup.normalizer (Q : Set G) →
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (R : Set G) →
      (∃ k : ℕ, ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf R).index = p ^ k) →
      R = Q ⊔ Subgroup.centralizer (Q : Set G)) :
    CFSG.pCore p (Subgroup.normalizer (Q : Set G) ⧸
      (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))) = ⊥ := by
  rw [CFSG.pCore, sSup_eq_bot]
  rintro D ⟨hDn, hDp⟩
  have hQCN : Q ⊔ Subgroup.centralizer (Q : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)
  let M := (Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))
  let R := (D.comap (QuotientGroup.mk' M)).map (Subgroup.normalizer (Q : Set G)).subtype
  have hQCR : Q ⊔ Subgroup.centralizer (Q : Set G) ≤ R := by
    intro x hx
    refine ⟨⟨x, hQCN hx⟩, ?_, rfl⟩
    change QuotientGroup.mk' M ⟨x, hQCN hx⟩ ∈ D
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff (N := M)
      (⟨x, hQCN hx⟩ : Subgroup.normalizer (Q : Set G))).mpr hx]
    exact D.one_mem
  have hRN : R ≤ Subgroup.normalizer (Q : Set G) := Subgroup.map_subtype_le _
  have hNR : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, (hDn.comap _).conj_mem y hy ⟨n, hn⟩, rfl⟩
    · rintro ⟨y, hy, hyg⟩
      refine ⟨⟨n, hn⟩⁻¹ * y * ⟨n, hn⟩⁻¹⁻¹, (hDn.comap _).conj_mem y hy _, ?_⟩
      simp only [Subgroup.coe_subtype, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hyg ⊢
      rw [hyg]
      group
  have hidx : ∃ k : ℕ, ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf R).index = p ^ k := by
    obtain ⟨k, hk⟩ := hDp.exists_card_eq
    refine ⟨k, ?_⟩
    change (Q ⊔ Subgroup.centralizer (Q : Set G)).relIndex R = p ^ k
    have hQC_eq : Q ⊔ Subgroup.centralizer (Q : Set G) =
        M.map (Subgroup.normalizer (Q : Set G)).subtype :=
      ((Subgroup.subgroupOf_map_subtype _ _).trans (inf_eq_left.mpr hQCN)).symm
    have hker := Subgroup.relIndex_ker (D.comap (QuotientGroup.mk' M)) (QuotientGroup.mk' M)
    rw [QuotientGroup.ker_mk'] at hker
    rw [hQC_eq, Subgroup.relIndex_map_map_of_injective _ _ (Subgroup.subtype_injective _), hker,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), hk]
  have hR := hrad R hQCR hRN hNR hidx
  rw [eq_bot_iff]
  intro d hd
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective M d
  have hnR : (n : G) ∈ R := ⟨n, hd, rfl⟩
  rw [hR] at hnR
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff n).mpr hnR

theorem lt_inf_normalizer_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {Q S : Subgroup G}
    (hS : IsPGroup p S) (hQS : Q < S) : Q < S ⊓ Subgroup.normalizer (Q : Set G) := by
  have : Group.IsNilpotent S := hS.isNilpotent
  have hlt : Q.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hQS.not_ge ?_
    exact Subgroup.subgroupOf_eq_top.mp h
  have hnorm := Group.normalizerCondition_of_isNilpotent (G := S) _ hlt
  obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.exists_of_lt hnorm
  have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hx' := Subgroup.mem_normalizer_iff.mp hx
    constructor
    · intro hg
      have := (hx' ⟨g, hQS.le hg⟩).mp hg
      exact this
    · intro hg
      have hgS : g ∈ S := by
        have h1 : x * g * x⁻¹ ∈ S := hQS.le hg
        have h2 : g = (x : G)⁻¹ * ((x : G) * g * (x : G)⁻¹) * (x : G) := by group
        rw [h2]
        exact S.mul_mem (S.mul_mem (S.inv_mem x.2) h1) x.2
      exact (hx' ⟨g, hgS⟩).mpr hg
  refine lt_of_le_of_ne (le_inf hQS.le Subgroup.le_normalizer) fun h => hxQ ?_
  have : (x : G) ∈ S ⊓ Subgroup.normalizer (Q : Set G) := ⟨x.2, hxN⟩
  rw [← h] at this
  exact this

@[expose] def infCentralizerEquivCenter (Q : Subgroup G) :
    (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) ≃ Subgroup.center Q where
  toFun z := ⟨⟨z, z.2.1⟩, Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp z.2.2 g g.2)⟩
  invFun w := ⟨w.1.1, w.1.2, Subgroup.mem_centralizer_iff.mpr fun h hh =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨h, hh⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem unitary_alperin_eq_sylow {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (Q : Subgroup G) (hQ : CFSG.RankTwoShapes.IsAlperinSubgroup 2 (S : Subgroup G) Q)
    (hU : ∃ (H : Type) (_ : Group H) (U : Sylow 2 H),
      CFSG.Assembly.LowTwoRank.StatedClassicalModel H .PSU 3 2 2 ∧ Nonempty (Q ≃* (U : Subgroup H)))
    (h3 : 3 ∣ ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G))).index)
    (hrank : ∀ E : Subgroup G, E ≤ (S : Subgroup G) → IsMulCommutative E →
      (∀ e ∈ E, e ^ 2 = 1) → Nat.card E ≤ 4) :
    Q = (S : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQS, hcop, hCS, hrad⟩ := hQ
  by_contra hne
  have hlt : Q < S := lt_of_le_of_ne hQS hne
  have hQp : IsPGroup 2 Q := S.isPGroup'.to_le hQS
  have hQlt := lt_inf_normalizer_of_lt_of_isPGroup S.isPGroup' hlt
  have hP₀p : IsPGroup 2 (((S : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf
      (Subgroup.normalizer (Q : Set G))) :=
    (S.isPGroup'.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  let P : Sylow 2 (Subgroup.normalizer (Q : Set G)) :=
    hP₀p.toSylow ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop)
  have hPcoe : (P : Subgroup (Subgroup.normalizer (Q : Set G))) =
      ((S : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalizer (Q : Set G)) := rfl
  have hPmap : (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
      (Subgroup.normalizer (Q : Set G)).subtype =
        (S : Subgroup G) ⊓ Subgroup.normalizer (Q : Set G) := by
    rw [hPcoe, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hQP : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) ≤ P := by
    rw [hPcoe]
    exact Subgroup.comap_mono hQlt.le
  have hCP : (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
      (Subgroup.normalizer (Q : Set G)).subtype ⊓ Subgroup.centralizer (Q : Set G) =
        Q ⊓ Subgroup.centralizer (Q : Set G) := by
    rw [hPmap]
    apply le_antisymm
    · intro x hx
      exact ⟨hCS ⟨hx.2, hx.1.1⟩, hx.2⟩
    · exact inf_le_inf_right _ hQlt.le
  obtain ⟨T, _, U, hT, ⟨eQU⟩⟩ := hU
  obtain ⟨hUcard, hUcenter, hUsq⟩ := unitaryFour_sylow_card hT U
  have hZcard : Nat.card (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) = 4 := by
    rw [Nat.card_congr (infCentralizerEquivCenter Q),
      Nat.card_congr (Subgroup.centerCongr eQU).toEquiv, hUcenter]
  have hZea : IsElementaryAbelian 2 (Q ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) := {
    toIsMulCommutative := {
      is_comm := {
        comm := fun a b => Subtype.ext
          (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
      }
    }
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro z
      have hz : eQU ⟨z, z.2.1⟩ ∈ Subgroup.center (U : Subgroup T) :=
        ((Subgroup.centerCongr eQU) (infCentralizerEquivCenter Q z)).2
      have h1 := hUsq _ hz
      rw [← map_pow, map_eq_one_iff _ eQU.injective] at h1
      have h2 : (z : G) ^ 2 = 1 := by simpa using congrArg Subtype.val h1
      exact Subtype.ext (by simpa using h2)
  }
  have hrad' := pCore_normalizer_quotient_eq_bot Q hrad
  obtain ⟨hKC, -, -, -, -, -, hdecomp, -, -, hinjP, hinjQ, ⟨P', hP'⟩, hcore, -, hcent⟩ :=
    fourCenter_centricRadical_normalizerQuotient Q hQp ⟨hZea, hZcard⟩ P hQP hCP hrad'
  have hQN : Q ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨eUW⟩ := nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hK
  let f : Q.subgroupOf (Subgroup.normalizer (Q : Set G)) →*
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) :=
    ((centricQuotientMk Q).comp
      (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).subtype).codRestrict _ fun x =>
        Subgroup.mem_map_of_mem _ x.2
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinjQ x.2 y.2 (congrArg Subtype.val hxy))
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let e' : (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) ≃*
      unitaryFourW (GaloisField 2 4) hK :=
    (MulEquiv.ofBijective f hf).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hQN).trans (eQU.trans eUW))
  have hCQ' : Subgroup.centralizer (((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
      (centricQuotientMk Q) : Subgroup (centricQuotient Q)) : Set (centricQuotient Q)) ≤
        (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) := by
    rw [hcent]
    exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have h3' : 3 ∣ ((Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map
      (centricQuotientMk Q)).index := by
    have hQK : Q ⊔ centralizerOddPart Q = Q ⊔ Subgroup.centralizer (Q : Set G) := by
      apply le_antisymm
      · exact sup_le_sup_left hKC _
      · apply sup_le le_sup_left
        rw [← hdecomp]
        exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
      Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      ← Subgroup.subgroupOf_sup hQN (centralizerOddPart_le_normalizer Q), hQK]
    exact h3
  have hQ'P' : (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) <
      (P' : Subgroup (centricQuotient Q)) := by
    rw [hP']
    refine lt_of_le_of_ne (Subgroup.map_mono hQP) fun h => ?_
    obtain ⟨x, hx, hxQ⟩ := IsConcreteLE.exists_of_lt hQlt
    have hxP : (⟨x, hx.2⟩ : Subgroup.normalizer (Q : Set G)) ∈
        (P : Subgroup (Subgroup.normalizer (Q : Set G))) := hx
    have hxmap : centricQuotientMk Q ⟨x, hx.2⟩ ∈
        (Q.subgroupOf (Subgroup.normalizer (Q : Set G))).map (centricQuotientMk Q) := by
      rw [h]
      exact Subgroup.mem_map_of_mem _ hxP
    obtain ⟨q, hq, hqx⟩ := hxmap
    have hqx' := hinjP (hQP hq) hxP hqx
    apply hxQ
    have hq' : (q : G) = x := congrArg Subtype.val hqx'
    rw [← hq']
    exact hq
  obtain ⟨E', hE'P, hE'comm, hE'sq, hE'card⟩ :=
    exists_elementaryEight_le_of_unitaryFour_twoCore _ hcore hCQ' e' h3' P' hQ'P'
  let E₀ : Subgroup (Subgroup.normalizer (Q : Set G)) :=
    E'.comap (centricQuotientMk Q) ⊓ (P : Subgroup (Subgroup.normalizer (Q : Set G)))
  let E : Subgroup G := E₀.map (Subgroup.normalizer (Q : Set G)).subtype
  have hES : E ≤ (S : Subgroup G) := by
    rintro _ ⟨a, ha, rfl⟩
    have : (a : G) ∈ (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
        (Subgroup.normalizer (Q : Set G)).subtype := Subgroup.mem_map_of_mem _ ha.2
    rw [hPmap] at this
    exact this.1
  have hE₀card : Nat.card E₀ = Nat.card E' := by
    let g : E₀ → E' := fun a => ⟨centricQuotientMk Q a, a.2.1⟩
    refine Nat.card_eq_of_bijective g ⟨fun a b hab => ?_, fun y => ?_⟩
    · exact Subtype.ext (hinjP a.2.2 b.2.2 (congrArg Subtype.val hab))
    · have hy : (y : centricQuotient Q) ∈ (P : Subgroup (Subgroup.normalizer (Q : Set G))).map
          (centricQuotientMk Q) := hP' ▸ hE'P y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, show centricQuotientMk Q x ∈ E' from hxy ▸ y.2, hx⟩, Subtype.ext hxy⟩
  have hEcard : Nat.card E = 8 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE₀card, hE'card]
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : centricQuotientMk Q (a * b) = centricQuotientMk Q (b * a) := by
      rw [map_mul, map_mul]
      exact hE'comm _ ha.1 _ hb.1
    have h2 := hinjP (Subgroup.mul_mem _ ha.2 hb.2) (Subgroup.mul_mem _ hb.2 ha.2) h1
    exact congrArg Subtype.val h2
  have hEsq : ∀ x ∈ E, x ^ 2 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : centricQuotientMk Q (a ^ 2) = centricQuotientMk Q 1 := by
      rw [map_pow, map_one]
      exact hE'sq _ ha.1
    have h2 := hinjP (Subgroup.pow_mem _ ha.2 2) (Subgroup.one_mem _) h1
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hEab : IsMulCommutative E :=
    ⟨⟨fun a b => Subtype.ext (hEcomm a a.2 b b.2)⟩⟩
  have := hrank E hES hEab hEsq
  omega

end CFSG.RankTwoShapes

