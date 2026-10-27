module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

theorem goldschmidtSimpleType_of_isGoldTypeI {L : Type} [Group L] (hI : IsGoldTypeI L)
    (hZ : center L = ⊥) : goldschmidtSimpleType L := by
  let eQ : L ≃* L ⧸ center L :=
    (QuotientGroup.quotientBot (G := L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩))

theorem typeI_facts
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (hI : IsGoldTypeI L)
    (hZ : center L = ⊥) (R : Sylow 2 L) :
    (∀ X : Subgroup L, Omega1 (R : Subgroup L) ≤ X → X ≤ R →
      normalizer ((R : Subgroup L) : Set L) ≤ normalizer (X : Set L) →
      X = Omega1 (R : Subgroup L) ∨ X = R) ∧
    ∃ d ∈ normalizer ((R : Subgroup L) : Set L),
      ∀ r ∈ (R : Subgroup L), d⁻¹ * r * d = r → r = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hDN, hDcyc, -, -, -, -, -, hΩ, htrans, hna, -, -, -, -, -, -, -, -⟩ := G32 L hI R
  refine ⟨fun X hΩX hXR hNX => ?_, ?_⟩
  · by_cases hab : IsMulCommutative (R : Subgroup L)
    · have hΩR : Omega1 (R : Subgroup L) = R := by
        rw [hΩ]
        refine le_antisymm inf_le_left (le_inf le_rfl ?_)
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (hab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
      left
      exact le_antisymm (hXR.trans hΩR.ge) hΩX
    · obtain ⟨-, -, hirr⟩ := hna hab
      rw [hΩ] at hΩX ⊢
      exact hirr X hΩX hXR (hDN.trans hNX)
  · obtain ⟨⟨g, hgD⟩, hg⟩ := IsCyclic.exists_generator (α := D)
    refine ⟨g, hDN hgD, fun r hr hrfix => ?_⟩
    by_contra hr1
    set F := (R : Subgroup L) ⊓ centralizer ({g} : Set L) with hF
    have hgcomm : ∀ x ∈ F, g * x = x * g := by
      intro x hx
      exact mem_centralizer_iff.mp (mem_inf.mp hx).2 g (Set.mem_singleton _)
    have hrF : r ∈ F := by
      refine mem_inf.mpr ⟨hr, ?_⟩
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      calc g * r = g * (g⁻¹ * r * g) := by rw [hrfix]
        _ = r * g := by group
    have hFp : IsPGroup 2 F := R.isPGroup'.to_le inf_le_left
    have hFne : F ≠ ⊥ := fun h => hr1 (by rw [h] at hrF; exact (mem_bot).mp hrF)
    obtain ⟨z, hz⟩ : ∃ z : F, orderOf z = 2 := by
      rcases hFp.card_eq_or_dvd with h1 | h2
      · exact absurd ((Subgroup.card_eq_one).mp h1) hFne
      · exact exists_prime_orderOf_dvd_card' 2 h2
    have hz2 : orderOf (z : L) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
    have hzsq : (z : L) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (z : L)
      rwa [hz2] at h
    have hzΩ : (z : L) ∈ Omega1 (R : Subgroup L) := subset_closure ⟨(mem_inf.mp z.2).1, hzsq⟩
    have hz1 : (z : L) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hz2
      exact absurd hz2 (by norm_num)
    have hΩab : IsMulCommutative (Omega1 (R : Subgroup L)) := by
      rw [hΩ]
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      exact mem_centralizer_iff.mp (mem_inf.mp b.2).2 a (mem_inf.mp a.2).1
    have hcard := (N11b L (goldschmidtSimpleType_of_isGoldTypeI hI hZ) R hΩab).1
    have hex : ∃ z' ∈ Omega1 (R : Subgroup L), z' ≠ 1 ∧ z' ≠ z := by
      by_contra hcon
      have hsub : ((Omega1 (R : Subgroup L) : Subgroup L) : Set L) ⊆ {1, (z : L)} := by
        intro y hy
        by_contra hy'
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hy'
        exact hcon ⟨y, hy, hy'.1, hy'.2⟩
      have h1 : Nat.card (Omega1 (R : Subgroup L)) ≤ 2 := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
        calc _ ≤ ({1, (z : L)} : Set L).ncard := Set.ncard_le_ncard hsub
          _ ≤ ({(z : L)} : Set L).ncard + 1 := Set.ncard_insert_le _ _
          _ = 2 := by rw [Set.ncard_singleton]
      omega
    obtain ⟨z', hz'Ω, hz'1, hz'z⟩ := hex
    obtain ⟨δ, hδD, hδ⟩ := htrans _ hzΩ _ hz'Ω hz1 hz'1
    obtain ⟨k, hk⟩ := hg ⟨δ, hδD⟩
    have hδk : δ = g ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    have hcomm : Commute (g ^ k) (z : L) := (Commute.zpow_left (hgcomm _ z.2) k)
    apply hz'z
    rw [← hδ, hδk, mul_assoc, ← hcomm.eq]
    group

variable {G : Type} [Group G] [Finite G]

theorem typeI_facts_of_le
    {K R : Subgroup G} [IsSimpleGroup K] (hI : IsGoldTypeI K)
    (hZ : center K = ⊥) (hRK : fusionIsSylowIn 2 R K) :
    (∀ X : Subgroup G, X ≤ R → Omega1 R ≤ X →
      (∀ n ∈ K, (∀ r ∈ R, n⁻¹ * r * n ∈ R) → ∀ x ∈ X, n⁻¹ * x * n ∈ X) →
      X = Omega1 R ∨ X = R) ∧
    ∃ d ∈ K, (∀ r ∈ R, d⁻¹ * r * d ∈ R) ∧ ∀ r ∈ R, d⁻¹ * r * d = r → r = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R', hR'⟩ := G310.exists_sylow_of_fusionIsSylowIn hRK
  obtain ⟨h1, d', hd'N, hd'free⟩ := typeI_facts hI hZ R'
  have hRK' : R ≤ K := hRK.1
  have hΩmap : (Omega1 (R' : Subgroup K)).map K.subtype = Omega1 R := by
    rw [SStarTransport.omega1_map_of_injective _ K.subtype_injective, hR']
  have hmemR : ∀ y : K, (y : G) ∈ R ↔ y ∈ (R' : Subgroup K) := by
    intro y
    constructor
    · intro hy
      rw [← hR'] at hy
      obtain ⟨y', hy', hyy'⟩ := hy
      rwa [show y = y' from Subtype.ext hyy'.symm]
    · intro hy
      rw [← hR']
      exact ⟨y, hy, rfl⟩
  have hnorm : ∀ n : K, n ∈ normalizer ((R' : Subgroup K) : Set K) →
      ∀ r ∈ R, (n : G)⁻¹ * r * n ∈ R := by
    intro n hn r hr
    have hrK : r ∈ K := hRK' hr
    have h2 := (mem_normalizer_iff.mp (inv_mem hn) ⟨r, hrK⟩).mp ((hmemR ⟨r, hrK⟩).mp hr)
    have h3 := (hmemR _).mpr h2
    simpa [mul_assoc] using h3
  refine ⟨fun X hXR hΩX hX => ?_, ⟨(d' : G), d'.2, hnorm d' hd'N, fun r hr hrfix => ?_⟩⟩
  · have hXK : X ≤ K := hXR.trans hRK'
    have h := h1 (X.subgroupOf K) (fun y hy => by
        rw [mem_subgroupOf]
        apply hΩX
        rw [← hΩmap]
        exact ⟨y, hy, rfl⟩)
      (fun y hy => (hmemR y).mp (hXR (mem_subgroupOf.mp hy)))
      (fun n hn => by
        rw [mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          rw [mem_subgroupOf] at hy ⊢
          have := hX (n⁻¹ : K) (n⁻¹ : K).2 (by simpa using hnorm (n⁻¹) (inv_mem hn)) y hy
          simpa using this
        · intro hy
          rw [mem_subgroupOf] at hy ⊢
          have := hX n n.2 (hnorm n hn) _ hy
          simpa [mul_assoc] using this)
    rcases h with h | h
    · left
      rw [← map_subgroupOf_eq_of_le hXK, h, hΩmap]
    · right
      rw [← map_subgroupOf_eq_of_le hXK, h, hR']
  · have hrK : r ∈ K := hRK' hr
    have h := hd'free ⟨r, hrK⟩ ((hmemR _).mp hr) (Subtype.ext (by simpa using hrfix))
    exact congrArg Subtype.val h

end CFSG.Goldschmidt75
