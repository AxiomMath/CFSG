module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.QuasithinUnique.A5.C25

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

variable {G : Type} [Group G] [Finite G]

@[expose] def RankOneLocalSolvable : Prop :=
  ∀ (X : Type) [Group X] [Finite X], A38Types X → ∀ P Λ : Subgroup X, IsElemAbelian 2 P →
    16 ≤ Nat.card P → Λ ≤ Subgroup.normalizer (P : Set X) → Group.IsSolvable ↥Λ

structure Setting (Gi L SI U : Subgroup G) : Prop where
  qtke : LocalSQTK G
  gi_core : pCoreOf 2 Gi ≠ ⊥
  L_le : L ≤ Gi
  SI_le : SI ≤ Gi
  local_SI : quasithinIsLocal SI L
  short : IsShort2 L
  alt5 : IsAltType L 5
  U_le : U ≤ pCoreOf 2 L
  U_elem : IsElemAbelian 2 U
  U_card : 16 ≤ Nat.card U
  L_norm : L ≤ Subgroup.normalizer (U : Set G)
  U_inf : U ⊓ pCoreOf 2 Gi = ⊥
  big : ∃ T : Subgroup G, IsSylowTwoOf T Gi ∧ SI < T
  star : ∀ H₁ S₁ : Subgroup G, CharTwo H₁ → L ⊔ SI ≤ H₁ → H₁ ≤ Gi → IsSylowTwoOf S₁ H₁ →
    SI < S₁ → quasithinIsCComponent L H₁

section Basic

variable {Gi L SI U : Subgroup G}

omit [Finite G] in
theorem U_le_L (S : Setting Gi L SI U) : U ≤ L :=
  S.U_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L)

omit [Finite G] in
theorem L_mem_cComp (S : Setting Gi L SI U) : L ∈ cComp (L ⊔ SI) := cComp_of_isLocal S.local_SI

theorem not_solvable_L (S : Setting Gi L SI U) : ¬ Group.IsSolvable ↥L :=
  not_isSolvable_of_mem_cComp (L_mem_cComp S)

theorem pCoreOf_le_of_mem_cComp {K : Subgroup G} (hK : K ∈ cComp Gi) :
    pCoreOf 2 K ≤ pCoreOf 2 Gi := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)

theorem U_inf_pCoreOf (S : Setting Gi L SI U) {K : Subgroup G} (hK : K ∈ cComp Gi) :
    U ⊓ pCoreOf 2 K = ⊥ :=
  eq_bot_iff.2 (S.U_inf ▸ inf_le_inf_left U (pCoreOf_le_of_mem_cComp hK))

end Basic

section Normal

variable {Gi L SI U : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_subgroupOf_iff' {U K : Subgroup G} (hUK : U ≤ K) (x : ↥K) :
    x ∈ Subgroup.normalizer ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (x : G) ∈ Subgroup.normalizer (U : Set G) := by
  have h := Subgroup.comap_normalizer_eq_of_le_range (H := U) (f := K.subtype)
    (by rw [Subgroup.range_subtype]; exact hUK)
  change x ∈ Subgroup.normalizer ((U.comap K.subtype : Subgroup ↥K) : Set ↥K) ↔ _
  rw [← h]
  rfl

theorem normal_of_rankOne (hR : RankOneLocalSolvable) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (S : Setting Gi L SI U) {K : Subgroup G} (hK : K ∈ cComp Gi) (hLK : L ≤ K) :
    (K.subgroupOf Gi).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases lemma_1_2_1_three S.qtke h37 h38 S.gi_core hK with hn | ⟨-, htypes⟩
  · exact hn
  · exfalso
    have hUK : U ≤ K := (U_le_L S).trans hLK
    let φ : ↥K →* (↥K ⧸ CFSG.pCore 2 ↥K) := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
    have hker : ∀ x : ↥K, φ x = 1 → (x : G) ∈ pCoreOf 2 K := fun x hx =>
      ⟨x, by exact (QuotientGroup.eq_one_iff x).1 hx, rfl⟩
    have hUinj : Function.Injective (φ.comp (U.subgroupOf K).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
      have h1 : ((u : ↥K) : G) ∈ U ⊓ pCoreOf 2 K := ⟨u.2, hker _ hu⟩
      rw [U_inf_pCoreOf S hK, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Subtype.ext (Subtype.ext h1)
    let P : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := (φ.comp (U.subgroupOf K).subtype).range
    have hUcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv => by
      have := S.U_elem.1
      exact setLike_mul_comm hu hv
    have hPe : IsElemAbelian 2 P := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨u, hu⟩ := a.2
        obtain ⟨v, hv⟩ := b.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hu, ← hv, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subtype.ext (hUcomm _ u.2 _ v.2))
      · obtain ⟨u, rfl⟩ := hx
        change φ (u : ↥K) ^ 2 = 1
        rw [← map_pow]
        have : (u : ↥K) ^ 2 = 1 := Subtype.ext (S.U_elem.2 _ u.2)
        rw [this, map_one]
    have hPcard : 16 ≤ Nat.card ↥P := by
      have e1 : Nat.card ↥(U.subgroupOf K) = Nat.card ↥P :=
        Nat.card_congr (MonoidHom.ofInjective hUinj).toEquiv
      have e2 : Nat.card ↥(U.subgroupOf K) = Nat.card ↥U :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
      rw [← e1, e2]
      exact S.U_card
    have hLK' : L ≤ K := hLK
    let Λ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) := (φ.comp (L.subgroupOf K).subtype).range
    have hΛN : Λ ≤ Subgroup.normalizer (P : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
      rintro _ ⟨l, rfl⟩
      have hlN : ((l : ↥K) : G) ∈ Subgroup.normalizer (U : Set G) := S.L_norm l.2
      have hlN' := (mem_normalizer_subgroupOf_iff' hUK (l : ↥K)).2 hlN
      rw [Subgroup.mem_normalizer_iff]
      intro p
      constructor
      · rintro ⟨q, rfl⟩
        refine ⟨⟨(l : ↥K) * (q : ↥K) * (l : ↥K)⁻¹, ?_⟩, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 hlN' (q : ↥K)).1 q.2
        · simp
      · rintro ⟨q, hq⟩
        have hmem : (l : ↥K)⁻¹ * (q : ↥K) * (l : ↥K) ∈ U.subgroupOf K := by
          have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hlN') (q : ↥K)).1 q.2
          simpa using this
        refine ⟨⟨_, hmem⟩, ?_⟩
        have hq' : φ (q : ↥K) = φ (l : ↥K) * p * (φ (l : ↥K))⁻¹ := hq
        show φ ((l : ↥K)⁻¹ * (q : ↥K) * (l : ↥K)) = p
        rw [map_mul, map_mul, map_inv, hq']
        group
    have hΛs : ¬ Group.IsSolvable ↥Λ := by
      intro hs
      apply not_solvable_L S
      let ρ : ↥(L.subgroupOf K) →* ↥Λ := (φ.comp (L.subgroupOf K).subtype).rangeRestrict
      let N : Subgroup ↥(L.subgroupOf K) := ρ.ker
      have hNs : Group.IsSolvable ↥N := by
        let ψ : ↥N →* ↥(CFSG.pCore 2 ↥K) :=
          ((L.subgroupOf K).subtype.comp N.subtype).codRestrict (CFSG.pCore 2 ↥K) (fun x => by
            have hx := x.2
            rw [MonoidHom.mem_ker] at hx
            have hx' : φ ((x : ↥(L.subgroupOf K)) : ↥K) = 1 := by
              have h1 : ((ρ (x : ↥(L.subgroupOf K)) : ↥Λ) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
                rw [hx]; rfl
              exact h1
            exact (QuotientGroup.eq_one_iff _).1 hx')
        have hψ : Function.Injective ψ := by
          intro a b hab
          have := congrArg Subtype.val hab
          exact Subtype.ext (Subtype.ext (by simpa [ψ] using this))
        have : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := isSolvable_pCore_two_group ↥K
        exact Group.isSolvable_of_isSolvable_injective hψ
      have : Group.IsSolvable ↥N := hNs
      have : Group.IsSolvable ↥Λ := hs
      have hLs' : Group.IsSolvable ↥(L.subgroupOf K) :=
        Group.isSolvable_of_ker_le_range N.subtype ρ (by
          intro x hx
          exact ⟨⟨x, hx⟩, rfl⟩)
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hLK').symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hLK').symm.injective
    exact hΛs (hR _ htypes P Λ hPe hPcard hΛN)

end Normal

section CharTwoPart

variable {Gi L SI U : Subgroup G}

omit [Finite G] in
theorem isSylowTwoOf_of_le_of_le' {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem charTwo_sup {K T : Subgroup G} (hK : CharTwo K) (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) : CharTwo (K ⊔ T) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hK hT hTK

theorem not_charTwo (S : Setting Gi L SI U) {K : Subgroup G} (hK : K ∈ cComp Gi) (hLK : L ≤ K)
    (hKn : (K.subgroupOf Gi).Normal) : ¬ CharTwo K := by
  intro hc
  obtain ⟨T, hT, hlt⟩ := S.big
  have hKGi : K ≤ Gi := le_of_mem_cComp hK
  have hGiN : Gi ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKGi).1 hKn
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.1.trans hGiN
  have hH : CharTwo (K ⊔ T) := charTwo_sup hc hT.2.1 hTK
  have hLSI : L ⊔ SI ≤ K ⊔ T := sup_le (hLK.trans le_sup_left) (hlt.le.trans le_sup_right)
  have hHGi : K ⊔ T ≤ Gi := sup_le hKGi hT.1
  have hTH : IsSylowTwoOf T (K ⊔ T) := isSylowTwoOf_of_le_of_le' hT le_sup_right hHGi
  have hstar : L ∈ cComp (K ⊔ T) := S.star (K ⊔ T) T hH hLSI hHGi hTH hlt
  have hLmem : L ∈ cComp K := cComp_mem_of_le hstar hLK le_sup_left
  have hLeq : L = K := by
    have := hLmem
    rw [cComp_self_eq_singleton hK] at this
    exact this
  have hU : U ≤ pCoreOf 2 K := hLeq ▸ S.U_le
  have hbot : U = ⊥ := by
    have := U_inf_pCoreOf S hK
    rwa [inf_eq_left.2 hU] at this
  have h16 := S.U_card
  rw [hbot, Subgroup.card_bot] at h16
  omega

end CharTwoPart

section Component

variable {X K : Subgroup G}

omit [Finite G] in
theorem mathlib_isSubnormal_of_open_top {H : Subgroup G} (h : CFSG.Open.IsSubnormal H ⊤) :
    H.IsSubnormal :=
  CFSG.Open.IsSubnormal.top_iff.1 h

omit [Finite G] in
theorem subgroupOf_isSubnormal_of_open (h : CFSG.Open.IsSubnormal K X) :
    (K.subgroupOf X).IsSubnormal := by
  have := Quasithin.A3.subnormal_comap X.subtype h
  rw [show X.comap X.subtype = ⊤ from Subgroup.subgroupOf_self X] at this
  exact mathlib_isSubnormal_of_open_top this

omit [Finite G] in
theorem isComponentIn_of_mem_cComp (h : K ∈ cComp X) (hq : CFSG.IsQuasisimple ↥K) :
    IsComponentIn K X :=
  ⟨le_of_mem_cComp h,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp h)).symm hq,
    subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp h)⟩

end Component

section Main

variable {Gi L SI U : Subgroup G}

theorem exists_component (hR : RankOneLocalSolvable) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (S : Setting Gi L SI U) (hT : ∃ K ∈ cComp Gi, L ≤ K)
    (hG : ∀ K ∈ cComp Gi, L ≤ K → ¬ CharTwo K → CFSG.IsQuasisimple ↥K) :
    ∃ K : Subgroup G, IsComponentIn K Gi ∧ L ≤ K ∧ (K.subgroupOf Gi).Normal := by
  obtain ⟨K, hK, hLK⟩ := hT
  have hn := normal_of_rankOne hR h37 h38 S hK hLK
  have hnc := not_charTwo S hK hLK hn
  exact ⟨K, isComponentIn_of_mem_cComp hK (hG K hK hLK hnc), hLK, hn⟩

end Main

end CFSG.QuasithinUnique.A5.C25
