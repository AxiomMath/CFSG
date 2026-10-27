module

public import CFSG.GH74.Generic.BProg.B2.T4PGVDefs
public import CFSG.GH74.Generic.BProg.B2.T4PGVGen
public import CFSG.GH74.Generic.BProg.B2.T4PGVL4a
public import CFSG.GH74.Generic.BProg.B2.T4PGVLift

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.PGV

open CFSG CFSG.GH74.Generic CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover Subgroup
open scoped MatrixGroups

theorem sup_centralizer_eq_top_of_surjective {S M : Type} [Group S] [Group M] (π : S →* M)
    (hπ : Function.Surjective π) {v₁ v₂ : S}
    (h : centralizer ({v₁} : Set S) ⊔ centralizer ({v₂} : Set S) ⊔
      centralizer ({v₁ * v₂} : Set S) = ⊤) :
    centralizer ({π v₁} : Set M) ⊔ centralizer ({π v₂} : Set M) ⊔
      centralizer ({π v₁ * π v₂} : Set M) = ⊤ := by
  have hle : ∀ v : S, (centralizer ({v} : Set S)).map π ≤ centralizer ({π v} : Set M) := by
    rintro v _ ⟨x, hx, rfl⟩
    have hx' : x ∈ centralizer ({v} : Set S) := hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx' ⊢
    rw [← map_mul, ← map_mul, hx']
  have h2 := congrArg (Subgroup.map π) h
  rw [Subgroup.map_top_of_surjective π hπ, Subgroup.map_sup, Subgroup.map_sup] at h2
  refine eq_top_iff.2 (h2.symm.le.trans (sup_le_sup (sup_le_sup (hle v₁) (hle v₂)) ?_))
  rw [← map_mul]
  exact hle _

theorem sup_centralizer_eq_top_of_cover {S M : Type} [Group S] [Group M] [Finite S]
    (π : S →* M) (hπ : Function.Surjective π) (hk : π.ker ≤ center S)
    (hk2 : IsPGroup 2 ↥π.ker)
    (hgen : ∀ v₁ v₂ : S, v₁ * v₁ = 1 → v₂ * v₂ = 1 → v₁ * v₂ = v₂ * v₁ → v₁ ∉ center S →
      v₂ ∉ center S → v₁ * v₂ ∉ center S →
      centralizer ({v₁} : Set S) ⊔ centralizer ({v₂} : Set S) ⊔
        centralizer ({v₁ * v₂} : Set S) = ⊤)
    {J : Subgroup M} (hJ : IsQuasisimple ↥J) {Y : Type} [Group Y] (eY : ↥J ⧸ center ↥J ≃* Y)
    (hM : Odd (Nat.card (hopfMultiplier Y))) {u₁ u₂ : M} (hu₁ : u₁ ∈ J) (hu₂ : u₂ ∈ J)
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h₁₂ : u₁ * u₂ = u₂ * u₁) (hc₁ : u₁ ∉ center M)
    (hc₂ : u₂ ∉ center M) (hc₁₂ : u₁ * u₂ ∉ center M) :
    centralizer ({u₁} : Set M) ⊔ centralizer ({u₂} : Set M) ⊔
      centralizer ({u₁ * u₂} : Set M) = ⊤ := by
  obtain ⟨v₁, v₂, rfl, rfl, hv₁, hv₂, hv₁₂⟩ :=
    exists_commuting_lift π hπ hk hk2 hJ eY hM hu₁ hu₂ h₁ h₂ h₁₂
  have hZ : ∀ v : S, v ∈ center S → π v ∈ center M := by
    intro v hv
    rw [Subgroup.mem_center_iff] at hv ⊢
    intro m
    obtain ⟨s, rfl⟩ := hπ m
    rw [← map_mul, ← map_mul, hv s]
  refine sup_centralizer_eq_top_of_surjective π hπ (hgen v₁ v₂ hv₁ hv₂ hv₁₂ ?_ ?_ ?_)
  · exact fun h => hc₁ (hZ _ h)
  · exact fun h => hc₂ (hZ _ h)
  · exact fun h => hc₁₂ (by rw [← map_mul]; exact hZ _ h)

section Main

variable {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem mk_not_mem_center {O : Subgroup L} [O.Normal] (hO : O ≤ center L)
    (hcen : center (L ⧸ O) = (center L).map (QuotientGroup.mk' O)) {J : Subgroup L}
    (hJZ : Odd (Nat.card ↥(center ↥J))) {u : L} (hu : u ∈ J) (huu : u * u = 1)
    (hu1 : u ≠ 1) : (QuotientGroup.mk u : L ⧸ O) ∉ center (L ⧸ O) := by
  intro h
  rw [hcen] at h
  obtain ⟨z, hz, hzu⟩ := h
  have hzu' : z⁻¹ * u ∈ O :=
    QuotientGroup.eq.1 (show (QuotientGroup.mk z : L ⧸ O) = QuotientGroup.mk u from hzu)
  have huZ : u ∈ center L := by
    have e : u = z * (z⁻¹ * u) := by group
    rw [e]
    exact (center L).mul_mem hz (hO hzu')
  have huJ : (⟨u, hu⟩ : ↥J) ∈ center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 huZ g)
  have h2 : orderOf (⟨⟨u, hu⟩, huJ⟩ : ↥(center ↥J)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact huu) hu1
  have hdvd := orderOf_dvd_natCard (⟨⟨u, hu⟩, huJ⟩ : ↥(center ↥J))
  rw [h2] at hdvd
  exact absurd (Odd.of_dvd_nat hJZ hdvd) (by decide)

theorem sup_centralizer_eq_top_of_puL4Any
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hq : IsQuasisimple L) (hT : PuL4Any (L ⧸ center L)) {J : Subgroup L}
    (hJ : IsQuasisimple ↥J) {Y : Type} [Group Y] (eY : ↥J ⧸ center ↥J ≃* Y)
    (hM : Odd (Nat.card (hopfMultiplier Y))) {u₁ u₂ : L} (hu₁ : u₁ ∈ J) (hu₂ : u₂ ∈ J)
    (h₁ : u₁ * u₁ = 1) (h₂ : u₂ * u₂ = 1) (h₁₂ : u₁ * u₂ = u₂ * u₁) (h₁1 : u₁ ≠ 1)
    (h₂1 : u₂ ≠ 1) (hne : u₁ ≠ u₂) :
    centralizer ({u₁} : Set L) ⊔ centralizer ({u₂} : Set L) ⊔
      centralizer ({u₁ * u₂} : Set L) = ⊤ := by
  classical
  set O := oddCenter L with hOdef
  have hO : O ≤ center L := oddCenter_le_center
  have hperf : commutator L = ⊤ := by
    have : Group.IsPerfect L := hq.1
    exact Group.IsPerfect.commutator_eq_top
  refine sup_centralizer_eq_top_of_quot hperf hO odd_card_oddCenter h₁ h₂ h₁₂ ?_
  obtain ⟨hqs, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hq O hO
  have h2Z : IsPGroup 2 ↥(center (L ⧸ O)) := isPGroup_center_quot hq
  let eQ : (L ⧸ O) ⧸ center (L ⧸ O) ≃* L ⧸ center L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient O (center L) hO)
  set mk : L →* L ⧸ O := QuotientGroup.mk' O with hmk
  have hJZ : Odd (Nat.card ↥(center ↥J)) :=
    Odd.of_dvd_nat hM (card_center_dvd_hopfMultiplier hJ eY)
  have hnc : ∀ u ∈ J, u * u = 1 → u ≠ 1 → mk u ∉ center (L ⧸ O) :=
    fun u hu huu hu1 => mk_not_mem_center hO hcen hJZ hu huu hu1
  have h₁₂1 : u₁ * u₂ ≠ 1 := fun h =>
    hne ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right h₂))
  have hc₁ := hnc u₁ hu₁ h₁ h₁1
  have hc₂ := hnc u₂ hu₂ h₂ h₂1
  have hc₁₂ : mk u₁ * mk u₂ ∉ center (L ⧸ O) := by
    rw [← map_mul]
    exact hnc _ (J.mul_mem hu₁ hu₂) (mul_mul_self_eq_one h₁ h₂ h₁₂) h₁₂1
  have hm₁ : mk u₁ * mk u₁ = 1 := by rw [← map_mul, h₁, map_one]
  have hm₂ : mk u₂ * mk u₂ = 1 := by rw [← map_mul, h₂, map_one]
  have hm₁₂ : mk u₁ * mk u₂ = mk u₂ * mk u₁ := by rw [← map_mul, ← map_mul, h₁₂]
  have hJnot : ¬ J ≤ mk.ker := fun h => hc₁ (by
    rw [(MonoidHom.mem_ker).1 (h hu₁)]
    exact Subgroup.one_mem _)
  set Js : Subgroup (L ⧸ O) := J.map mk with hJs
  have hJsq : IsQuasisimple ↥Js := CFSG.LocalCores.isQuasisimple_map hJ mk hJnot
  have hker : (mk.subgroupMap J).ker ≤ center ↥J := by
    intro x hx
    have hx' : (x : L) ∈ O := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hx)
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hO hx') g)
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hJ
    (mk.subgroupMap J) (mk.subgroupMap_surjective J) hker
  have hmJ : ∀ u ∈ J, mk u ∈ Js := fun u hu => ⟨u, hu, rfl⟩
  obtain ⟨p, f, hp, hp2, -, hm | hm⟩ := hT
  ·
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    have hF2 : ringChar F ≠ 2 := CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hF
    have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
    obtain ⟨π, hπ, hcompat⟩ := psl4_cover_of_griess hGA hqs h2Z F hodd (eQ.trans e)
    set φ := specialLinearGroupEquivStatedSL 4 F with hφ
    set π' : SL(4, F) →* L ⧸ O := π.comp φ.toMonoidHom with hπ'
    have hk := ker_le_center_of_cover (eQ.trans e) π hcompat
    have hk2 := isPGroup_ker_of_cover_sl (eQ.trans e) π hcompat
    have hk' : π'.ker ≤ center SL(4, F) := by
      intro x hx
      have hφx : φ x ∈ π.ker := hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply φ.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 (hk hφx) (φ y)
    have hk2' : IsPGroup 2 ↥π'.ker := by
      intro x
      obtain ⟨k, hk'⟩ := hk2 ⟨φ (x : SL(4, F)), x.2⟩
      refine ⟨k, Subtype.ext (φ.injective ?_)⟩
      have h1 : (φ (x : SL(4, F))) ^ (2 ^ k) = 1 := congrArg Subtype.val hk'
      rw [Subgroup.coe_pow, map_pow, h1, Subgroup.coe_one, map_one]
    exact sup_centralizer_eq_top_of_cover π' (hπ.comp φ.surjective) hk' hk2'
      (fun v₁ v₂ hv₁ hv₂ hv₁₂ hd₁ hd₂ hd₁₂ =>
        sup_centralizer_eq_top_sl4 hF2 hv₁ hv₂ hv₁₂ hd₁ hd₂ hd₁₂)
      hJsq (eJ.symm.trans eY) hM (hmJ u₁ hu₁) (hmJ u₂ hu₂) hm₁ hm₂ hm₁₂ hc₁ hc₂ hc₁₂
  ·
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    have hqodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨π, hπ, hcompat⟩ := psu4_cover_of_griess hGA hqs h2Z K (p ^ f) hK hqodd (eQ.trans e)
    exact sup_centralizer_eq_top_of_cover π hπ (ker_le_center_of_cover (eQ.trans e) π hcompat)
      (isPGroup_ker_of_cover_su hp hK (eQ.trans e) π hcompat)
      (fun v₁ v₂ hv₁ hv₂ hv₁₂ hd₁ hd₂ hd₁₂ =>
        sup_centralizer_eq_top_su4 hp hp2 hK hv₁ hv₂ hv₁₂ hd₁ hd₂ hd₁₂)
      hJsq (eJ.symm.trans eY) hM (hmJ u₁ hu₁) (hmJ u₂ hu₂) hm₁ hm₂ hm₁₂ hc₁ hc₂ hc₁₂

end Main

end CFSG.GH74.Generic.BProg.B2.T4.PGV
