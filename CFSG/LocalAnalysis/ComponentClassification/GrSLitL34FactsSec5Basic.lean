module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCenter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem card_sq_eq_one_le {A : Type*} [CommGroup A] [Finite A] (g₁ g₂ : A)
    (hgen : ∀ x : A, ∃ a b : ℕ, x = g₁ ^ a * g₂ ^ b) : Nat.card {x : A // x * x = 1} ≤ 4 := by
  set sq : A →* A := powMonoidHom 2 with hsq
  have hker : Nat.card {x : A // x * x = 1} = Nat.card sq.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [MonoidHom.mem_ker, hsq, powMonoidHom_apply, pow_two]
  have h1 : Nat.card sq.ker * Nat.card sq.range = Nat.card A := by
    rw [← Subgroup.card_mul_index sq.ker, Subgroup.index_ker]
  have h2 : Nat.card A ≤ 4 * Nat.card sq.range := by
    have hs : Function.Surjective
        (fun p : Fin 2 × Fin 2 × sq.range => g₁ ^ (p.1 : ℕ) * g₂ ^ (p.2.1 : ℕ) * (p.2.2 : A)) := by
      intro x
      obtain ⟨a, b, rfl⟩ := hgen x
      refine ⟨(⟨a % 2, Nat.mod_lt _ two_pos⟩, ⟨b % 2, Nat.mod_lt _ two_pos⟩,
        ⟨(g₁ ^ (a / 2) * g₂ ^ (b / 2)) ^ 2, ⟨_, rfl⟩⟩), ?_⟩
      show g₁ ^ (a % 2) * g₂ ^ (b % 2) * (g₁ ^ (a / 2) * g₂ ^ (b / 2)) ^ 2 = g₁ ^ a * g₂ ^ b
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← pow_add, ← pow_add,
        mul_comm (a / 2) 2, mul_comm (b / 2) 2, Nat.mod_add_div, Nat.mod_add_div]
    have h := Nat.card_le_card_of_surjective _ hs
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
      at h
    omega
  have hpos : 0 < Nat.card sq.range := Nat.card_pos
  rw [hker]
  nlinarith

variable {G : Type} [Group G]

theorem centerRank :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      Nat.card ↥(omegaOne (P ⊓ zStarIn K)) ≤ 4 := by
  intro G _ _ K P hK hL hP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hjq : ∀ {a : G} (ha : a ∈ P ⊓ zStarIn K), jq K ⟨a, hP.1 ha.1⟩ ∈ center (Jhat K) :=
    fun ha => (mem_zStarIn_iff _).1 ha.2
  have hZc : ∀ a ∈ P ⊓ zStarIn K, ∀ b ∈ P ⊓ zStarIn K, a * b = b * a := by
    intro a ha b hb
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem ha.1 hb.1) (P.mul_mem hb.1 ha.1)
    show jq K (⟨a, hP.1 ha.1⟩ * ⟨b, hP.1 hb.1⟩) = jq K (⟨b, hP.1 hb.1⟩ * ⟨a, hP.1 ha.1⟩)
    rw [map_mul, map_mul]
    exact mem_center_iff.mp (hjq hb) _
  let H₀ : Subgroup G :=
    { carrier := {h | h ∈ P ⊓ zStarIn K ∧ h * h = 1}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hZc b hb.1 a ha.1]
          _ = a * a * (b * b) := by group
          _ = 1 := by rw [ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨one_mem _, mul_one 1⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by rw [← mul_inv_rev, ha.2, inv_one]⟩ }
  have hle : omegaOne (P ⊓ zStarIn K) ≤ H₀ := (closure_le _).2 fun _ hh => hh
  let _ : CommGroup ↥(center (Jhat K)) :=
    { (inferInstance : Group ↥(center (Jhat K))) with
      mul_comm := fun a b => Subtype.ext (mem_center_iff.mp b.2 a) }
  have hl₁ := lam_z_facts hQ.ker_le hQ.ql
  have hgen : ∀ x : ↥(center (Jhat K)), ∃ a b : ℕ,
      x = (⟨l z₁, hl₁.1⟩ : ↥(center (Jhat K))) ^ a * ⟨l z₂, hl₁.2.1⟩ ^ b := by
    intro x
    obtain ⟨c, hc⟩ := hls x.1
    have hck : c ∈ sigma.ker := by
      have hx : (x : Jhat K) ∈ q.ker := by rw [hqker]; exact x.2
      rw [MonoidHom.mem_ker, ← hQ.q_l c, hc]
      exact hx
    rw [← range_zHom] at hck
    obtain ⟨d, rfl⟩ := hck
    refine ⟨d.1.toAdd.val, d.2.1.toAdd.val, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hc, zHom_apply,
      map_mul, map_mul, map_pow, map_pow, map_pow, hQ.lz₃, one_pow, mul_one]
  have hcard := card_sq_eq_one_le _ _ hgen
  refine (Subgroup.card_le_of_le hle).trans (le_trans ?_ hcard)
  refine Nat.card_le_card_of_injective
    (fun h => ⟨⟨jq K ⟨h, hP.1 h.2.1.1⟩, hjq h.2.1⟩, Subtype.ext ?_⟩) fun a b hab => ?_
  · show jq K ⟨h, hP.1 h.2.1.1⟩ * jq K ⟨h, hP.1 h.2.1.1⟩ = 1
    rw [← map_mul]
    have e1 : (⟨h, hP.1 h.2.1.1⟩ : K) * ⟨h, hP.1 h.2.1.1⟩ = 1 := Subtype.ext h.2.2
    rw [e1, map_one]
  · have h1 := congrArg (fun x => ((x : ↥(center (Jhat K))) : Jhat K)) (congrArg Subtype.val hab)
    exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2.1.1 b.2.1.1 h1)

theorem centerNoncyclic :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K → ¬ IsCyclic ↥(P ⊓ zStarIn K) →
      (∃ z ∈ P ⊓ zStarIn K, z * z ≠ 1) →
      P ⊓ centralizer (P : Set G) = P ⊓ zStarIn K := by
  intro G _ _ K P hK hL hP _ hz
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨z, hz, hz2⟩ := hz
  have hk4 : ∃ e ∈ q.ker, e * e ≠ 1 := by
    refine ⟨jq K ⟨z, hP.1 hz.1⟩, by rw [hqker]; exact (mem_zStarIn_iff _).1 hz.2,
      fun h => hz2 ?_⟩
    refine eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hz.1 hz.1) ?_
    show jq K (⟨z, hP.1 hz.1⟩ * ⟨z, hP.1 hz.1⟩) = 1
    rw [map_mul]
    exact h
  ext y
  constructor
  · rintro ⟨hy, hc⟩
    have hq1 := hQ.q_eq_one_of_central hk4 ((hT _).2 ⟨y, hy, _, rfl⟩)
      (e := jq K ⟨y, hP.1 hy⟩) fun e' he' => by
        obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e').1 he'
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext ((mem_centralizer_iff.mp hc) p hpP).symm
    refine ⟨hy, (mem_zStarIn_iff (hP.1 hy)).2 ?_⟩
    rw [← hqker]
    exact hq1
  · rintro ⟨hy, hyz⟩
    refine ⟨hy, mem_centralizer_iff.mpr fun p hp => ?_⟩
    have hc := (mem_zStarIn_iff (hP.1 hy)).1 hyz
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hp hy) (P.mul_mem hy hp)
    show jq K (⟨p, hP.1 hp⟩ * ⟨y, hP.1 hy⟩) = jq K (⟨y, hP.1 hy⟩ * ⟨p, hP.1 hp⟩)
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hc _

theorem elementaryRank :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
      ∃ A : Subgroup G, A ≤ P ∧ IsElemTwo A ∧ Nat.card A = 16 * Nat.card ↥(P ⊓ zStarIn K) := by
  intro G _ _ K P hK hL hP hZ
  obtain ⟨E, -, hEP, hE, hcard, -⟩ := l34ElementaryCenterFact G K P hK hL hP hZ
  exact ⟨E, hEP, hE, hcard⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
