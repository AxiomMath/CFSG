module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma411

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

namespace L415

theorem exists_mem_normalizer_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P Q : Subgroup G} (hQ : IsPGroup p Q) (hPQ : P < Q) :
    ∃ x ∈ Q, x ∉ P ∧ x ∈ normalizer (P : Set G) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hPQ.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : Q) ∈ P.subgroupOf Q := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := Q) _ hlt)
  refine ⟨y, y.2, fun h => hyP (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (P : Set G)).subgroupOf Q := by
    rw [Subgroup.subgroupOf_normalizer_eq hPQ.le]
    exact hyN
  exact Subgroup.mem_subgroupOf.mp hy

theorem twoPart_centralizer_conj {G : Type} [Group G] (a c : G) :
    twoPart (centralizer ({c * a * c⁻¹} : Set G)) = twoPart (centralizer ({a} : Set G)) := by
  unfold twoPart
  rw [← map_conj_centralizer a c, Subgroup.card_map_of_injective (MulAut.conj c).injective]

end L415

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem lt_inf_centralizer [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {b : X} (hbX : b ∈ closure {t, w ^ (orderOf w / 2), z})
    (hlt : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) < twoPart (centralizer ({b} : Set X))) :
    zpowers t ⊔ (S ⊓ L) ⊔ zpowers w < V ⊓ centralizer ({b} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have hTb : T ≤ centralizer ({b} : Set X) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hσ.X_le_center_T hbX).2 y hy)
  have hTp : IsPGroup 2 T := hS.isPGroup.to_le hσ.T_le
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_ge hTp hTb
  have hTP' : T < P := by
    refine lt_of_le_of_ne hTP fun hTP2 => ?_
    have h1 : Nat.card T = twoPart (centralizer ({b} : Set X)) := by
      rw [hTP2]
      exact hP.card_eq
    omega
  obtain ⟨n, hnP, hnT, hnN⟩ := L415.exists_mem_normalizer_of_lt hP.isPGroup hTP'
  have hQle : T ⊔ zpowers n ≤ centralizer ({b} : Set X) ⊓
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    sup_le (le_inf hTb le_normalizer) (zpowers_le.mpr (mem_inf.mpr ⟨hP.le hnP, hnN⟩))
  have hQp : IsPGroup 2 ↥(T ⊔ zpowers n) :=
    hP.isPGroup.to_le (sup_le hTP (zpowers_le.mpr hnP))
  have hQcard : Nat.card ↥(T ⊔ zpowers n) ≤ Nat.card ↥(V ⊓ centralizer ({b} : Set X)) := by
    rw [(hσ.isSylowOf_inf_centralizer hKF hV hbX).card_eq]
    exact card_le_twoPart hQp hQle
  have hTQ : T < T ⊔ zpowers n := lt_of_le_of_ne le_sup_left fun h1 =>
    hnT (h1 ▸ mem_sup_right (mem_zpowers n))
  have hTV : T ≤ V ⊓ centralizer ({b} : Set X) := le_inf (hσ.T_le.trans hSV) hTb
  refine lt_of_le_of_ne hTV fun h1 => ?_
  have h2 := Subgroup.card_lt_of_lt hTQ
  rw [← h1] at hQcard
  omega

theorem isBeta411_t_mul [Finite X] (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) {b : X} (hbX : b ∈ closure {t, w ^ (orderOf w / 2), z})
    (hbD : b ∉ zpowers t ⊔ (S ⊓ L))
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} →
      g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z)
    (hlt : Nat.card ↥(zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) <
      twoPart (centralizer ({t * b} : Set X)))
    (hle : twoPart (⊤ : Subgroup X) ≤ 4 * twoPart (centralizer ({t * b} : Set X))) :
    IsBeta411 t L S w z V (t * b) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := zpowers t ⊔ (S ⊓ L) ⊔ zpowers w with hT
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have htD : t ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_left (mem_zpowers t)
  have hzD : z ∈ zpowers t ⊔ (S ⊓ L) := mem_sup_right hσ.z_mem
  have htbX : t * b ∈ closure {t, w ^ (orderOf w / 2), z} := mul_mem htX hbX
  have htbD : t * b ∉ zpowers t ⊔ (S ⊓ L) := fun h1 => hbD (by
    have h2 := mul_mem (inv_mem htD) h1
    rwa [inv_mul_cancel_left] at h2)
  have htb1 : t * b ≠ 1 := fun h1 => htbD (h1 ▸ one_mem _)
  have htbz : t * b ≠ z := fun h1 => htbD (h1 ▸ hzD)
  have hinf := hσ.inf_centralizer_inf_t hKC hV hSV htbX htbD
  have hlt' := hσ.lt_inf_centralizer hKF hV hSV htbX hlt
  have hconjX : ∀ v ∈ V, v * t * v⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := fun v hv =>
    (mem_normalizer_iff.mp (hσ.normalizer_T_le_normalizer_X (hV.le hv)) t).mp htX
  obtain ⟨v, hv, hvT⟩ := IsConcreteLE.exists_of_lt hlt'
  have hvS : v ∉ S := fun h1 => hvT (by
    rw [← hinf]
    exact mem_inf.mpr ⟨hv, hS.le h1⟩)
  have hvt : v * t * v⁻¹ = t * z := by
    rcases hfus v (hconjX v (mem_inf.mp hv).1) with h1 | h1
    · exfalso
      apply hvT
      rw [← hinf]
      refine mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
      calc v * t = v * t * v⁻¹ * v := by group
        _ = t * v := by rw [h1]
    · exact h1
  have hv2 : v ^ 2 ∈ T := by
    refine hσ.sq_mem_T_of_fix hKC hV hSV htbX htb1 htbz (mem_inf.mp hv).1 ?_
    rw [mem_centralizer_singleton_iff.mp (mem_inf.mp hv).2, mul_inv_cancel_right]
  have hrel : (V ⊓ centralizer ({t * b} : Set X)).relIndex V ≤ 2 := by
    have htV : t ∈ V := hSV (h.t_mem hS)
    have hsub : {y : X | ∃ a ∈ V, a * t * a⁻¹ = y} ⊆ {t, t * z} := by
      rintro _ ⟨a, ha, rfl⟩
      rcases hfus a (hconjX a ha) with h1 | h1 <;> rw [h1] <;> simp
    have hVS := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (ncard_pair_le_two t (t * z))
    rw [ncard_conj_orbit V htV, ← inf_relIndex_right, inf_comm,
      hσ.inf_centralizer_t hV hSV] at hVS
    have hST := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.1
    have hcV := Subgroup.relIndex_mul_card S V
    rw [inf_of_le_left hSV] at hcV
    have hcU := Subgroup.relIndex_mul_card (V ⊓ centralizer ({t * b} : Set X)) V
    rw [inf_of_le_left inf_le_left] at hcU
    have h2T : 2 * Nat.card T ≤ Nat.card ↥(V ⊓ centralizer ({t * b} : Set X)) := by
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hlt'.le
      have hcl := Subgroup.card_lt_of_lt hlt'
      rw [hk] at hcl ⊢
      rcases k with _ | _ | k
      · simp at hcl
      · simp at hcl
      · nlinarith
    have hTpos : 0 < Nat.card T := Nat.card_pos
    have hV4 : Nat.card V ≤ 4 * Nat.card T := by
      rw [← hcV]
      calc S.relIndex V * Nat.card S ≤ 2 * (2 * Nat.card T) :=
            Nat.mul_le_mul hVS hST
        _ = 4 * Nat.card T := by ring
    by_contra hgt
    push Not at hgt
    have h3 : 3 * Nat.card ↥(V ⊓ centralizer ({t * b} : Set X)) ≤
        (V ⊓ centralizer ({t * b} : Set X)).relIndex V *
          Nat.card ↥(V ⊓ centralizer ({t * b} : Set X)) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨htbX, htbD, fun g h1 => ?_, ⟨v, hv, hvS, hv2, Or.inl hvt⟩, hlt',
    hσ.isSylowOf_inf_centralizer hKF hV htbX,
    fun g hg hgX => hσ.exists_conj_of_mem_centralizer hKF hV htbX hg hgX, hinf, hrel, hle, ?_⟩
  ·
    have hgX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
      rw [h1]
      exact htbX
    rcases hfus g hgX with h2 | h2
    · apply hbD
      have h3 : t * b = t * 1 := by rw [← h1, h2, mul_one]
      rw [mul_left_cancel h3]
      exact one_mem _
    · apply hbD
      have h3 : t * b = t * z := by rw [← h1, h2]
      rw [mul_left_cancel h3]
      exact hzD
  ·
    rintro ⟨g, hgX, hne⟩
    exfalso
    rcases hfus g hgX with h1 | h1
    · exact hne 1 (one_mem _) (by rw [h1]; group)
    · exact hne v hv (by rw [hvt, h1])

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
