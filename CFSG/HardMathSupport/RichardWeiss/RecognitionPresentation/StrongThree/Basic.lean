module

public import CFSG.Open.GLBDefs

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open

variable {G : Type*} [Group G]

theorem mem_inf_glbConj {M : Subgroup G} {g x : G} (hx : x ∈ M) (hgx : g * x * g⁻¹ ∈ M) :
    x ∈ M ⊓ GLBConj g M := by
  refine ⟨hx, ?_⟩
  unfold GLBConj
  exact Subgroup.mem_map.mpr ⟨g * x * g⁻¹, hgx, by simp [mul_assoc]⟩

variable [Finite G]

omit [Finite G] in
theorem normalizer_le_of_stronglyEmbedded {M R : Subgroup G} (hM : GLBStronglyEmbedded 3 M)
    (hR : R ≤ M) (h3 : 3 ∣ Nat.card R) : Subgroup.normalizer (R : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hle : R ≤ M ⊓ GLBConj g M := fun x hx =>
    mem_inf_glbConj (hR hx) (hR ((Subgroup.mem_normalizer_iff.mp hg x).mp hx))
  exact hM.2.2 g hgM (h3.trans (Subgroup.card_dvd_of_le hle))

omit [Finite G] in
theorem not_dvd_card_normalCore {M : Subgroup G} (hM : GLBStronglyEmbedded 3 M) :
    ¬ 3 ∣ Nat.card M.normalCore := by
  intro h3
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ M := by
    by_contra hall
    exact hM.1 (eq_top_iff.mpr fun x _ => by_contra fun hx => hall ⟨x, hx⟩)
  have hle : M.normalCore ≤ M ⊓ GLBConj g M := fun x hx =>
    mem_inf_glbConj (M.normalCore_le hx)
      (M.normalCore_le ((Subgroup.normalCore_normal M).conj_mem x hx g))
  exact hM.2.2 g hg (h3.trans (Subgroup.card_dvd_of_le hle))

theorem exists_sylow_le_of_le {M E : Subgroup G} (hM : GLBStronglyEmbedded 3 M) (hEM : E ≤ M)
    (hE : IsPGroup 3 E) : ∃ P : Sylow 3 G, E ≤ P ∧ (P : Subgroup G) ≤ M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hEQ⟩ := (hE.comap_subtype (K := M)).exists_le_sylow
  set Q' : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hQ'
  have hEQ' : E ≤ Q' := fun x hx => ⟨⟨x, hEM hx⟩, hEQ hx, rfl⟩
  have hQ'p : IsPGroup 3 Q' := Q.isPGroup'.map _
  obtain ⟨S, hQS⟩ := hQ'p.exists_le_sylow
  refine ⟨S, hEQ'.trans hQS, ?_⟩
  by_contra hSM
  have hQ3 : 3 ∣ Nat.card Q' := by
    have h1 : 3 ∣ Nat.card M := hM.2.1
    have h2 : Nat.card M = Nat.card Q * (Q : Subgroup ↥M).index := by
      rw [mul_comm]; exact (Subgroup.index_mul_card _).symm
    have h3 : ¬ 3 ∣ (Q : Subgroup ↥M).index := Q.not_dvd_index
    have : 3 ∣ Nat.card Q := by
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 (h2 ▸ h1) with h | h
      · exact h
      · exact absurd h h3
    rw [hQ', Subgroup.card_map_of_injective M.subtype_injective]
    exact this
  have hSMQ : (S : Subgroup G) ⊓ M ≤ Q' := by
    have hT : IsPGroup 3 (((S : Subgroup G) ⊓ M).subgroupOf M) :=
      (S.isPGroup'.to_le inf_le_left).comap_subtype
    have hQT : (Q : Subgroup ↥M) ≤ ((S : Subgroup G) ⊓ M).subgroupOf M := fun m hm =>
      ⟨hQS (Subgroup.mem_map_of_mem _ hm), m.2⟩
    have hEq := Q.is_maximal' hT hQT
    intro x hx
    have hx' : (⟨x, hx.2⟩ : ↥M) ∈ ((S : Subgroup G) ⊓ M).subgroupOf M := hx
    rw [hEq] at hx'
    exact ⟨_, hx', rfl⟩
  have : Group.IsNilpotent ↥(S : Subgroup G) := S.isPGroup'.isNilpotent
  set H : Subgroup ↥(S : Subgroup G) := Q'.subgroupOf (S : Subgroup G) with hH
  have hHtop : H < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hSM fun x hx => ?_
    have hxH : (⟨x, hx⟩ : ↥(S : Subgroup G)) ∈ H := h ▸ Subgroup.mem_top _
    exact Subgroup.map_subtype_le (Q : Subgroup ↥M) hxH
  obtain ⟨y, hyN, hyH⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHtop)
  have hyQ' : (y : G) ∉ Q' := hyH
  have hyM : (y : G) ∉ M := fun hyM => hyQ' (hSMQ ⟨y.2, hyM⟩)
  have hnorm : ∀ x : G, x ∈ Q' → (y : G) * x * (y : G)⁻¹ ∈ Q' := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.mp hyN ⟨x, hQS hx⟩).mp hx
    exact this
  have hle : Q' ≤ M ⊓ GLBConj (y : G) M := fun x hx =>
    mem_inf_glbConj (Subgroup.map_subtype_le (Q : Subgroup ↥M) hx)
      (Subgroup.map_subtype_le (Q : Subgroup ↥M) (hnorm x hx))
  exact hM.2.2 y hyM (hQ3.trans (Subgroup.card_dvd_of_le hle))

theorem exists_sylow_le {M : Subgroup G} (hM : GLBStronglyEmbedded 3 M) :
    ∃ P : Sylow 3 G, (P : Subgroup G) ≤ M := by
  obtain ⟨P, -, hP⟩ := exists_sylow_le_of_le hM (bot_le : (⊥ : Subgroup G) ≤ M) (IsPGroup.of_card
    (by simp : Nat.card (⊥ : Subgroup G) = 3 ^ 0))
  exact ⟨P, hP⟩

theorem exists_conj_orderThree_mem {S : Subgroup G} (h3 : 3 ∣ Nat.card S) (P : Sylow 3 G) :
    ∃ y : G, ∃ a : G, a ∈ (P : Subgroup G) ∧ a ∈ S.map (MulAut.conj y).toMonoidHom ∧
      orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 h3
  have hs' : orderOf (s : G) = 3 := by rw [← hs]; exact orderOf_submonoid s
  have hsp : IsPGroup 3 (Subgroup.zpowers (s : G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hs']; simp
  obtain ⟨P', hP'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
  have hsP' : (s : G) ∈ ((g • P : Sylow 3 G) : Subgroup G) := by
    rw [hg]; exact hP' (Subgroup.mem_zpowers _)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hsP'
  refine ⟨g⁻¹, (MulAut.conj g)⁻¹ • (s : G), hsP', ⟨s, s.2, ?_⟩, ?_⟩
  · simp
  · have : (MulAut.conj g)⁻¹ • (s : G) = (MulAut.conj g⁻¹) (s : G) := by simp
    rw [this]; exact (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) (s : G)).trans hs'

omit [Finite G] in
theorem centralizer_le_of_orderThree {M : Subgroup G} (hM : GLBStronglyEmbedded 3 M) {a : G}
    (haM : a ∈ M) (ha : orderOf a = 3) : Subgroup.centralizer ({a} : Set G) ≤ M := by
  have hz : Subgroup.zpowers a ≤ M := (Subgroup.zpowers_le).mpr haM
  have h3 : 3 ∣ Nat.card (Subgroup.zpowers a) := by rw [Nat.card_zpowers, ha]
  refine le_trans ?_ (normalizer_le_of_stronglyEmbedded hM hz h3)
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have hgcomm : ∀ k : ℤ, g * a ^ k * g⁻¹ = a ^ k := by
    intro k
    have hc : Commute g a := hg
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simpa using (hgcomm k).symm⟩
  · rintro ⟨k, hk⟩
    simp only at hk
    have : h = a ^ k := by
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = g⁻¹ * a ^ k * g := by rw [← hk]
        _ = g⁻¹ * (g * a ^ k * g⁻¹) * g := by rw [hgcomm k]
        _ = a ^ k := by group
    exact ⟨k, this.symm⟩

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
