module

public import CFSG.GroupTheory.ComponentCovering
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.Assembly.Defs

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem relIndex_sup_inf_key {A B R Z : Subgroup G} (hAB : A ≤ normalizer (B : Set G))
    (hRZ : R ≤ normalizer (Z : Set G)) (hRA : R ≤ A) (hZB : Z ≤ B) :
    (R ⊔ Z).relIndex (A ⊔ B) * (R ⊓ Z).relIndex (A ⊓ B) =
      R.relIndex A * Z.relIndex B := by
  classical
  have h1 := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := A) (K := B) hAB
  have h2 := CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := R) (K := Z) hRZ
  have h3 := Subgroup.relIndex_mul_card (H := R) (K := A)
  have h4 := Subgroup.relIndex_mul_card (H := Z) (K := B)
  have h5 := Subgroup.relIndex_mul_card (H := R ⊔ Z) (K := A ⊔ B)
  have h6 := Subgroup.relIndex_mul_card (H := R ⊓ Z) (K := A ⊓ B)
  rw [inf_eq_left.mpr hRA] at h3
  rw [inf_eq_left.mpr hZB] at h4
  rw [inf_eq_left.mpr (sup_le (hRA.trans le_sup_left) (hZB.trans le_sup_right))] at h5
  rw [inf_eq_left.mpr (inf_le_inf hRA hZB)] at h6
  have hpos : 0 < Nat.card ↥(R ⊔ Z) * Nat.card ↥(R ⊓ Z) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc ((R ⊔ Z).relIndex (A ⊔ B) * (R ⊓ Z).relIndex (A ⊓ B)) *
        (Nat.card ↥(R ⊔ Z) * Nat.card ↥(R ⊓ Z))
      = ((R ⊔ Z).relIndex (A ⊔ B) * Nat.card ↥(R ⊔ Z)) *
          ((R ⊓ Z).relIndex (A ⊓ B) * Nat.card ↥(R ⊓ Z)) := by ring
    _ = Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) := by rw [h5, h6]
    _ = Nat.card A * Nat.card B := h1
    _ = (R.relIndex A * Nat.card R) * (Z.relIndex B * Nat.card Z) := by rw [← h3, ← h4]
    _ = (R.relIndex A * Z.relIndex B) * (Nat.card ↥(R ⊔ Z) * Nat.card ↥(R ⊓ Z)) := by
        rw [h2]; ring

private theorem not_dvd_relIndex_sup_inf {p : ℕ} [Fact p.Prime] {T A B : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hA : IsSylowOf p (T ⊓ A) A)
    (hB : IsSylowOf p (T ⊓ B) B) (hRZ : T ⊓ A ≤ normalizer ((T ⊓ B : Subgroup G) : Set G)) :
    ¬ p ∣ ((T ⊓ A) ⊔ (T ⊓ B)).relIndex (A ⊔ B) := by
  classical
  have hRA : ¬ p ∣ (T ⊓ A).relIndex A := (isSylowOf_iff.mp hA).2.2
  have hZB : ¬ p ∣ (T ⊓ B).relIndex B := (isSylowOf_iff.mp hB).2.2
  intro hdvd
  have hki : p ∣ ((T ⊓ A) ⊔ (T ⊓ B)).relIndex (A ⊔ B) *
      ((T ⊓ A) ⊓ (T ⊓ B)).relIndex (A ⊓ B) := hdvd.mul_right _
  rw [relIndex_sup_inf_key hAB hRZ inf_le_right inf_le_right] at hki
  rcases (Fact.out : p.Prime).dvd_mul.mp hki with h | h
  · exact hRA h
  · exact hZB h

theorem inf_sup_eq_sup_of_isSylowOf {p : ℕ} [Fact p.Prime] {T A B : Subgroup G}
    (hT : IsPGroup p T) (hAB : A ≤ normalizer (B : Set G)) (hA : IsSylowOf p (T ⊓ A) A)
    (hB : IsSylowOf p (T ⊓ B) B) :
    T ⊓ (A ⊔ B) = (T ⊓ A) ⊔ (T ⊓ B) := by
  classical
  have hRZ : T ⊓ A ≤ normalizer ((T ⊓ B : Subgroup G) : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer)
      (inf_le_right.trans hAB)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hle : (T ⊓ A) ⊔ (T ⊓ B) ≤ T ⊓ (A ⊔ B) :=
    sup_le (inf_le_inf_left T le_sup_left) (inf_le_inf_left T le_sup_right)
  have hR : IsPGroup p ↥(T ⊓ A) := hT.to_inf_left (H := T) (K := A)
  have hZ : IsPGroup p ↥(T ⊓ B) := hT.to_inf_left (H := T) (K := B)
  have hWp : IsPGroup p ↥((T ⊓ A) ⊔ (T ⊓ B)) :=
    hR.to_sup_of_normal_right' (H := T ⊓ A) (K := T ⊓ B) hZ hRZ
  have hW : IsSylowOf p ((T ⊓ A) ⊔ (T ⊓ B)) (A ⊔ B) :=
    isSylowOf_iff.mpr ⟨hle.trans inf_le_right, hWp,
      not_dvd_relIndex_sup_inf hAB hA hB hRZ⟩
  exact hW.eq_of_le hle inf_le_right (hT.to_inf_left (H := T) (K := A ⊔ B))

omit [Finite G] in
theorem finset_sup_subgroupOf_normal {E : Subgroup G} (S : Finset (Subgroup G))
    (hle : ∀ L ∈ S, L ≤ E) (hn : ∀ L ∈ S, E ≤ normalizer (L : Set G)) :
    ((S.sup id).subgroupOf E).Normal := by
  classical
  refine Finset.induction
    (motive := fun S => (∀ L ∈ S, L ≤ E) → (∀ L ∈ S, E ≤ normalizer (L : Set G)) →
      ((S.sup id).subgroupOf E).Normal) ?_ ?_ S hle hn
  · intro _ _
    simp
  · intro L S hLS ih hleS hnS
    have hSle : ∀ K ∈ S, K ≤ E := fun K hK => hleS K (Finset.mem_insert_of_mem hK)
    have hSn : ∀ K ∈ S, E ≤ normalizer (K : Set G) :=
      fun K hK => hnS K (Finset.mem_insert_of_mem hK)
    have hLmem : L ≤ E := hleS L (Finset.mem_insert_self L S)
    have hLn : E ≤ normalizer (L : Set G) := hnS L (Finset.mem_insert_self L S)
    have hJleE : S.sup id ≤ E := Finset.sup_le hSle
    have hJnorm : E ≤ normalizer ((S.sup id : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJleE).mp (ih hSle hSn)
    have hsup : (insert L S).sup id = S.sup id ⊔ L := by
      simp [Finset.sup_insert, sup_comm]
    rw [hsup]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hJleE hLmem)).mpr
      ((le_inf hJnorm hLn).trans (Subgroup.inf_normalizer_le_normalizer_sup (S.sup id) L))

private theorem inf_finsetSup_le_of_normal_family {p : ℕ} [Fact p.Prime]
    {T H E Q : Subgroup G} (hT : IsSylowOf p T H) (hE : IsSubnormal E H)
    {𝓕 : Set (Subgroup G)} (hle : ∀ L ∈ 𝓕, L ≤ E)
    (hn : ∀ L ∈ 𝓕, E ≤ normalizer (L : Set G)) (hQ : ∀ L ∈ 𝓕, T ⊓ L ≤ Q)
    (S : Finset (Subgroup G)) (hS : ∀ L ∈ S, L ∈ 𝓕) : T ⊓ (S.sup id) ≤ Q := by
  classical
  refine Finset.induction
    (motive := fun S => (∀ L ∈ S, L ∈ 𝓕) → T ⊓ (S.sup id) ≤ Q) ?_ ?_ S hS
  · intro _
    simp
  · intro L S hLS ih hS
    have hS' : ∀ K ∈ S, K ∈ 𝓕 := fun K hK => hS K (Finset.mem_insert_of_mem hK)
    have hLmem : L ∈ 𝓕 := hS L (Finset.mem_insert_self L S)
    have ih' : T ⊓ (S.sup id) ≤ Q := ih hS'
    have hJleE : S.sup id ≤ E := Finset.sup_le fun K hK => hle K (hS' K hK)
    have hLleE : L ≤ E := hle L hLmem
    have hJnorm : ((S.sup id).subgroupOf E).Normal :=
      finset_sup_subgroupOf_normal S (fun K hK => hle K (hS' K hK))
        (fun K hK => hn K (hS' K hK))
    have hJsub : IsSubnormal (S.sup id) H := IsSubnormal.step hJleE hJnorm hE
    have hLnorm : (L.subgroupOf E).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLleE).mpr (hn L hLmem)
    have hLsub : IsSubnormal L H := IsSubnormal.step hLleE hLnorm hE
    have hsplit := inf_sup_eq_sup_of_isSylowOf (p := p) hT.isPGroup
      (hJleE.trans (hn L hLmem)) (hT.inf_of_isSubnormal hJsub)
      (hT.inf_of_isSubnormal hLsub)
    have hsup : (insert L S).sup id = S.sup id ⊔ L := by
      simp [Finset.sup_insert, sup_comm]
    rw [hsup, hsplit]
    exact sup_le ih' (hQ L hLmem)

theorem inf_iSup_le_of_normal_family {p : ℕ} [Fact p.Prime] {T H E Q : Subgroup G}
    (hT : IsSylowOf p T H) (hE : IsSubnormal E H) (𝓕 : Set (Subgroup G))
    (hle : ∀ L ∈ 𝓕, L ≤ E) (hn : ∀ L ∈ 𝓕, E ≤ normalizer (L : Set G))
    (hQ : ∀ L ∈ 𝓕, T ⊓ L ≤ Q) : T ⊓ (⨆ L ∈ 𝓕, L) ≤ Q := by
  classical
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  let S : Finset (Subgroup G) := (Set.toFinite 𝓕).toFinset
  have hS : ∀ L ∈ S, L ∈ 𝓕 := fun L hL => (Set.toFinite 𝓕).mem_toFinset.mp hL
  have hkey : T ⊓ (S.sup id) ≤ Q :=
    inf_finsetSup_le_of_normal_family hT hE hle hn hQ S hS
  have hScoe : (S : Set (Subgroup G)) = 𝓕 := (Set.toFinite 𝓕).coe_toFinset
  have hsup : (⨆ L ∈ 𝓕, L) = S.sup id := by
    rw [← hScoe, Finset.sup_eq_iSup]
    simp
  rwa [hsup]

theorem le_of_isPGroup_of_isSylowOf_le_normal {p : ℕ} [Fact p.Prime] {P K H Q : Subgroup G}
    (hP : IsSylowOf p P H) (hPK : P ≤ K) (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hQ : IsPGroup p Q) (hQH : Q ≤ H) : Q ≤ K := by
  classical
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK
  haveI := hKnorm
  have hPidx : ¬ p ∣ P.relIndex H := (isSylowOf_iff.mp hP).2.2
  have hKind : ¬ p ∣ K.relIndex H := by
    intro hdvd
    exact hPidx ((Subgroup.relIndex_mul_relIndex P K H hPK hKH) ▸
      dvd_mul_of_dvd_right hdvd (P.relIndex K))
  have hQ' : IsPGroup p (Q.subgroupOf H) := hQ.comap_subtype
  obtain ⟨n, hn⟩ := hQ'.exists_card_eq
  have hcop : Nat.Coprime (Nat.card (Q.subgroupOf H)) (K.subgroupOf H).index := by
    rw [hn]
    exact Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr
        (by simpa [Subgroup.relIndex] using hKind))
  have hle : Q.subgroupOf H ≤ K.subgroupOf H :=
    CFSG.GroupTheory.WielandtProduct.le_of_coprime_index hcop
  intro q hq
  let qH : H := ⟨q, hQH hq⟩
  have hqQ : qH ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.mpr hq
  exact Subgroup.mem_subgroupOf.mp (hle hqQ)

end CFSG.GroupTheory
