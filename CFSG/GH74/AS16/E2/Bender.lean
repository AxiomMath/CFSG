module

public import CFSG.GH74.AS16.E2.Decomp
public import CFSG.GH74.E2.Tools
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.AS16.E2

open Subgroup
open scoped commutatorElement

structure BenderTable {G : Type*} [Group G] (L TL : Subgroup G) : Prop where
  invol_central : ∀ x ∈ TL, x ^ 2 = 1 → ∀ y ∈ TL, y * x = x * y
  center_exp2 : ∀ a ∈ TL ⊓ centralizer (TL : Set G), a ^ 2 = 1
  center_le_comm : TL ⊓ centralizer (TL : Set G) ≤ ⁅TL, TL⁆
  torus : ∃ x ∈ L ⊓ normalizer (TL : Set G), ∀ a ∈ TL ⊓ centralizer (TL : Set G),
    ∀ b ∈ TL ⊓ centralizer (TL : Set G), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = b

theorem ncard_conjOrbit_eq_index {G : Type*} [Group G] (N : Subgroup G) (z : G) :
    {w : G | ∃ n ∈ N, w = n⁻¹ * z * n}.ncard = ((centralizer ({z} : Set G)).subgroupOf N).index := by
  let f : ↥N →* MulAut G := (MulAut.conj : G →* MulAut G).comp N.subtype
  let _ : MulAction ↥N G := MulAction.compHom G f
  have hsmul : ∀ (n : ↥N) (g : G), n • g = (n : G) * g * (n : G)⁻¹ := fun n g => rfl
  have hstab : MulAction.stabilizer ↥N z = (centralizer ({z} : Set G)).subgroupOf N := by
    ext n
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc (n : G) * z = (n * z * (n : G)⁻¹) * n := by group
        _ = z * n := by rw [h]
    · intro h
      rw [h]; group
  have horb : MulAction.orbit ↥N z = {w : G | ∃ n ∈ N, w = n⁻¹ * z * n} := by
    ext w
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : G)⁻¹, N.inv_mem n.2, by rw [hsmul]; simp⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n⁻¹, N.inv_mem hn⟩, by rw [hsmul]; simp⟩
  rw [← horb, ← hstab, MulAction.index_stabilizer]

theorem conj_fixed_of_bender {G : Type*} [Group G] [Finite G] {S L : Subgroup G} {z : G}
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) (hzS : z ∈ S)
    (hLz : ∀ l ∈ L, l * z = z * l)
    (hdec : ∀ t ∈ S, ∃ s ∈ S ⊓ L, ∃ c ∈ S ⊓ centralizer (L : Set G), t = s * c)
    (hmeet : ∀ g ∈ L, g ∈ centralizer (L : Set G) → g = 1)
    (hTCcomm : ∀ c ∈ S ⊓ centralizer (L : Set G), ∀ c' ∈ S ⊓ centralizer (L : Set G),
      c * c' = c' * c)
    (hTCinv : ∀ c ∈ S ⊓ centralizer (L : Set G), c ^ 2 = 1 → c = 1 ∨ c = z)
    (hB : BenderTable L (S ⊓ L))
    (hodd : Odd ((centralizer ({z} : Set G)).subgroupOf (normalizer (S : Set G))).index) :
    (∀ u ∈ S, u ^ 2 = 1 → ∀ t ∈ S, t * u = u * t) ∧
      ∀ n ∈ normalizer (S : Set G), n⁻¹ * z * n = z := by
  classical
  set TL : Subgroup G := S ⊓ L with hTL
  set TC : Subgroup G := S ⊓ centralizer (L : Set G) with hTC
  set A : Subgroup G := TL ⊓ centralizer (TL : Set G) with hA
  have hLC : ∀ l ∈ L, ∀ c ∈ TC, l * c = c * l := fun l hl c hc =>
    Subgroup.mem_centralizer_iff.1 hc.2 l hl
  have hz_TC : z ∈ TC := ⟨hzS, Subgroup.mem_centralizer_iff.2 fun l hl => hLz l hl⟩
  have claimI : ∀ u ∈ S, u ^ 2 = 1 → ∃ a ∈ A, ∃ c ∈ TC, u = a * c ∧ (c = 1 ∨ c = z) := by
    intro u hu hu2
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec u hu
    have hcomm : Commute s c := hLC s hs.2 c hc
    have h1 : s ^ 2 * c ^ 2 = 1 := by rw [← hcomm.mul_pow]; exact hu2
    have hs2 : s ^ 2 = 1 := by
      have e1 : s ^ 2 = (c ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h2L : s ^ 2 ∈ L := L.pow_mem hs.2 2
      have h2C : s ^ 2 ∈ centralizer (L : Set G) := by
        rw [e1]
        exact (centralizer (L : Set G)).inv_mem ((centralizer (L : Set G)).pow_mem hc.2 2)
      exact hmeet _ h2L h2C
    have hc2 : c ^ 2 = 1 := by rw [hs2, one_mul] at h1; exact h1
    exact ⟨s, ⟨hs, Subgroup.mem_centralizer_iff.2 fun y hy => hB.invol_central s hs hs2 y hy⟩,
      c, hc, rfl, hTCinv c hc hc2⟩
  have hcentral : ∀ u ∈ S, u ^ 2 = 1 → ∀ t ∈ S, t * u = u * t := by
    intro u hu hu2 t ht
    obtain ⟨a, ha, c, hc, rfl, -⟩ := claimI u hu hu2
    obtain ⟨s', hs', c', hc', rfl⟩ := hdec t ht
    have e1 : Commute s' a := Subgroup.mem_centralizer_iff.1 ha.2 s' hs'
    have e2 : Commute c' a := (hLC a ha.1.2 c' hc').symm
    have e3 : Commute s' c := hLC s' hs'.2 c hc
    have e4 : Commute c' c := hTCcomm c' hc' c hc
    exact Commute.mul_left (Commute.mul_right e1 e3) (Commute.mul_right e2 e4)
  have hcommS : ∀ t ∈ S, ∀ t' ∈ S, ⁅t, t'⁆ ∈ TL := by
    intro t ht t' ht'
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec t ht
    obtain ⟨s', hs', c', hc', rfl⟩ := hdec t' ht'
    have hcs' : c * s' = s' * c := (hLC s' hs'.2 c hc).symm
    have hc's : c' * s = s * c' := (hLC s hs.2 c' hc').symm
    have hcc' : c * c' = c' * c := hTCcomm c hc c' hc'
    have hc_comm : c * (s' * c') = (s' * c') * c := by
      rw [← mul_assoc, hcs', mul_assoc, hcc', mul_assoc]
    have hc's_inv : c' * s⁻¹ * c'⁻¹ = s⁻¹ := by
      calc c' * s⁻¹ * c'⁻¹ = (c' * s * c'⁻¹)⁻¹ := by group
        _ = s⁻¹ := by rw [show c' * s * c'⁻¹ = s by rw [hc's]; group]
    have e : ⁅s * c, s' * c'⁆ = ⁅s, s'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc s * c * (s' * c') * (s * c)⁻¹ * (s' * c')⁻¹
          = s * (c * (s' * c')) * c⁻¹ * s⁻¹ * (s' * c')⁻¹ := by group
        _ = s * ((s' * c') * c) * c⁻¹ * s⁻¹ * (s' * c')⁻¹ := by rw [hc_comm]
        _ = s * (s' * c') * s⁻¹ * (s' * c')⁻¹ := by group
        _ = s * s' * (c' * s⁻¹ * c'⁻¹) * s'⁻¹ := by group
        _ = s * s' * s⁻¹ * s'⁻¹ := by rw [hc's_inv]
    rw [e, commutatorElement_def]
    exact TL.mul_mem (TL.mul_mem (TL.mul_mem hs hs') (TL.inv_mem hs)) (TL.inv_mem hs')
  have hSS : ⁅S, S⁆ ≤ TL := Subgroup.commutator_le.2 hcommS
  have hz_nc : z ∉ ⁅S, S⁆ := by
    intro h
    exact hz1 (hmeet z (hSS h).2 hz_TC.2)
  have hnormSS : ∀ m ∈ normalizer (S : Set G), ∀ x ∈ ⁅S, S⁆, m * x * m⁻¹ ∈ ⁅S, S⁆ := by
    intro m hm x hx
    have hle : ⁅S, S⁆ ≤ (⁅S, S⁆).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro g1 hg1 g2 hg2
      show m * ⁅g1, g2⁆ * m⁻¹ ∈ ⁅S, S⁆
      have e : m * ⁅g1, g2⁆ * m⁻¹ = ⁅m * g1 * m⁻¹, m * g2 * m⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.1 hm g1).1 hg1)
        ((Subgroup.mem_normalizer_iff.1 hm g2).1 hg2)
    exact hle hx
  have hAcomm : A ≤ ⁅S, S⁆ := fun a ha =>
    Subgroup.commutator_mono (inf_le_left : TL ≤ S) (inf_le_left : TL ≤ S) (hB.center_le_comm ha)
  have hconj : ∀ m ∈ normalizer (S : Set G), ∃ a ∈ A, m⁻¹ * z * m = a * z := by
    intro m hm
    have hm' : m⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem hm
    have hwS : m⁻¹ * z * m ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hm' z).1 hzS
      simpa using this
    have hw2 : (m⁻¹ * z * m) ^ 2 = 1 := by
      calc (m⁻¹ * z * m) ^ 2 = m⁻¹ * z ^ 2 * m := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hz2]; group
    obtain ⟨a, ha, c, hc, hwe, hc1 | hcz⟩ := claimI _ hwS hw2
    · exfalso
      rw [hc1, mul_one] at hwe
      have hw : m⁻¹ * z * m ∈ ⁅S, S⁆ := hwe ▸ hAcomm ha
      apply hz_nc
      have := hnormSS m hm _ hw
      simpa [mul_assoc] using this
    · exact ⟨a, ha, by rw [hwe, hcz]⟩
  refine ⟨hcentral, ?_⟩
  intro n hn
  by_contra hne
  obtain ⟨a₀, ha₀, hna⟩ := hconj n hn
  have ha₀1 : a₀ ≠ 1 := by
    intro h; apply hne; rw [hna, h, one_mul]
  obtain ⟨x, hxLN, htorus⟩ := hB.torus
  have hxL : x ∈ L := hxLN.1
  have hxS : ∀ x' ∈ L ⊓ normalizer (TL : Set G), ∀ y ∈ S, x' * y * x'⁻¹ ∈ S := by
    intro x' hx' y hy
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec y hy
    have hcx : x' * c = c * x' := hLC x' hx'.1 c hc
    have e : x' * (s * c) * x'⁻¹ = (x' * s * x'⁻¹) * c := by
      calc x' * (s * c) * x'⁻¹ = (x' * s * x'⁻¹) * (x' * c * x'⁻¹) := by group
        _ = (x' * s * x'⁻¹) * c := by rw [hcx]; group
    rw [e]
    exact S.mul_mem ((Subgroup.mem_normalizer_iff.1 hx'.2 s).1 hs).1 hc.1
  have hxN : x ∈ normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hxS x hxLN y hy, fun hy => ?_⟩
    have hxinv : x⁻¹ ∈ L ⊓ normalizer (TL : Set G) :=
      (L ⊓ normalizer (TL : Set G)).inv_mem hxLN
    have := hxS x⁻¹ hxinv _ hy
    simpa [mul_assoc] using this
  set N : Subgroup G := normalizer (S : Set G) with hN
  set Orb : Set G := {w | ∃ m ∈ N, w = m⁻¹ * z * m} with hOrb
  have hsub1 : Orb ⊆ (fun a : G => a * z) '' (A : Set G) := by
    rintro w ⟨m, hm, rfl⟩
    obtain ⟨a, ha, h⟩ := hconj m hm
    exact ⟨a, ha, h.symm⟩
  have hxz : ∀ k : ℕ, x ^ k * z * (x ^ k)⁻¹ = z := by
    intro k
    have h := hLz (x ^ k) (L.pow_mem hxL k)
    rw [h]; group
  have hsub2 : (fun a : G => a * z) '' (A : Set G) ⊆ Orb := by
    rintro w ⟨b, hb, rfl⟩
    by_cases hb1 : b = 1
    · exact ⟨1, N.one_mem, by simp [hb1]⟩
    · obtain ⟨k, hk⟩ := htorus a₀ ha₀ b hb ha₀1 hb1
      refine ⟨n * (x ^ k)⁻¹, N.mul_mem hn (N.inv_mem (N.pow_mem hxN k)), ?_⟩
      show b * z = (n * (x ^ k)⁻¹)⁻¹ * z * (n * (x ^ k)⁻¹)
      calc b * z = (x ^ k * a₀ * (x ^ k)⁻¹) * (x ^ k * z * (x ^ k)⁻¹) := by rw [hk, hxz k]
        _ = x ^ k * (a₀ * z) * (x ^ k)⁻¹ := by group
        _ = x ^ k * (n⁻¹ * z * n) * (x ^ k)⁻¹ := by rw [hna]
        _ = (n * (x ^ k)⁻¹)⁻¹ * z * (n * (x ^ k)⁻¹) := by group
  have hOrbEq : Orb = (fun a : G => a * z) '' (A : Set G) := Set.Subset.antisymm hsub1 hsub2
  have hcard : Orb.ncard = Nat.card A := by
    rw [hOrbEq, Set.ncard_image_of_injective _ (mul_left_injective z)]
    exact (Nat.card_coe_set_eq (A : Set G)).symm
  have hcard2 : Orb.ncard = ((centralizer ({z} : Set G)).subgroupOf N).index :=
    ncard_conjOrbit_eq_index N z
  have hAeven : 2 ∣ Nat.card A := by
    have ha2 : a₀ ^ 2 = 1 := hB.center_exp2 a₀ ha₀
    have hord : orderOf a₀ = 2 := orderOf_eq_prime ha2 ha₀1
    rw [← hord]
    exact Subgroup.orderOf_dvd_natCard A ha₀
  have hdvd : 2 ∣ ((centralizer ({z} : Set G)).subgroupOf N).index := by
    rw [← hcard2, hcard]; exact hAeven
  obtain ⟨k, hk⟩ := hodd
  omega

theorem BenderTable.of_subtype {G : Type*} [Group G] (L : Subgroup G) (Q : Subgroup ↥L)
    (h : BenderTable (⊤ : Subgroup ↥L) Q) : BenderTable L (Q.map L.subtype) := by
  have hinj : Function.Injective L.subtype := L.subtype_injective
  have hcen : ∀ a ∈ Q.map L.subtype ⊓ centralizer ((Q.map L.subtype : Subgroup G) : Set G),
      ∃ q ∈ Q ⊓ centralizer (Q : Set ↥L), L.subtype q = a := by
    rintro a ⟨⟨q, hq, rfl⟩, ha⟩
    refine ⟨q, ⟨hq, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 ha (L.subtype y) ⟨y, hy, rfl⟩
    exact hinj this
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩ hq2 _ ⟨q', hq', rfl⟩
    have hq2' : q ^ 2 = 1 := hinj (by simpa using hq2)
    have := h.invol_central q hq hq2' q' hq'
    exact congrArg L.subtype this
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := hcen a ha
    have := h.center_exp2 q hq
    simpa using congrArg L.subtype this
  · intro a ha
    obtain ⟨q, hq, rfl⟩ := hcen a ha
    have := h.center_le_comm hq
    rw [← Subgroup.map_commutator]
    exact ⟨q, this, rfl⟩
  · obtain ⟨x, hx, htor⟩ := h.torus
    have hnorm : L.subtype x ∈ normalizer ((Q.map L.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨x * q * x⁻¹, (Subgroup.mem_normalizer_iff.1 hx.2 q).1 hq, by simp⟩
      · rintro ⟨q, hq, hqe⟩
        have hqx : x⁻¹ * q * x ∈ Q := by
          refine (Subgroup.mem_normalizer_iff.1 hx.2 (x⁻¹ * q * x)).2 ?_
          have e : x * (x⁻¹ * q * x) * x⁻¹ = q := by group
          rw [e]; exact hq
        refine ⟨x⁻¹ * q * x, hqx, ?_⟩
        have hg : g = (L.subtype x)⁻¹ * (L.subtype x * g * (L.subtype x)⁻¹) * L.subtype x := by group
        rw [hg, ← hqe]
        simp
    refine ⟨L.subtype x, ⟨x.2, hnorm⟩, ?_⟩
    · intro a ha b hb ha1 hb1
      obtain ⟨a', ha', rfl⟩ := hcen a ha
      obtain ⟨b', hb', rfl⟩ := hcen b hb
      have ha1' : a' ≠ 1 := fun h' => ha1 (by rw [h']; simp)
      have hb1' : b' ≠ 1 := fun h' => hb1 (by rw [h']; simp)
      obtain ⟨k, hk⟩ := htor a' ha' b' hb' ha1' hb1'
      exact ⟨k, by simpa using congrArg L.subtype hk⟩

theorem isSylowOf_top {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) :
    CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, T.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

theorem false_of_bender {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) (hLz : ∀ l ∈ L, l * z = z * l)
    (hdec : ∀ t ∈ (T : Subgroup G), ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c)
    (hmeet : ∀ g ∈ L, g ∈ centralizer (L : Set G) → g = 1)
    (hTCcyc : IsCyclic ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hB : BenderTable L ((T : Subgroup G) ⊓ L)) : False := by
  classical
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hzTC : z ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) :=
    ⟨hzT, Subgroup.mem_centralizer_iff.2 fun l hl => hLz l hl⟩
  have hTCcomm : ∀ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G),
      ∀ c' ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), c * c' = c' * c := by
    intro c hc c' hc'
    have := cyclic_mul_comm (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G))) ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hTCinv : ∀ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), c ^ 2 = 1 → c = 1 ∨ c = z := by
    intro c hc hc2
    have := cyclic_pow_two_eq_one (X := ↥((T : Subgroup G) ⊓ centralizer (L : Set G)))
      (z := ⟨z, hzTC⟩) (c := ⟨c, hc⟩)
      (Subtype.ext (by simpa using hz2)) (fun h => hz1 (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hc2))
    rcases this with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hodd : Odd ((centralizer ({z} : Set G)).subgroupOf
      (normalizer ((T : Subgroup G) : Set G))).index := by
    have hTle : (T : Subgroup G) ≤ normalizer ((T : Subgroup G) : Set G) :=
      Subgroup.le_normalizer
    have hSyl' := CFSG.ABGLocalTools.IsSylowOf.of_le (isSylowOf_top T) hTle le_top
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSyl'
    have hnd : ¬ 2 ∣ (T : Subgroup G).relIndex (normalizer ((T : Subgroup G) : Set G)) :=
      hSyl'.2.2
    have hle : (T : Subgroup G).subgroupOf (normalizer ((T : Subgroup G) : Set G)) ≤
        (centralizer ({z} : Set G)).subgroupOf (normalizer ((T : Subgroup G) : Set G)) := by
      intro g hg
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzc g hg
    have hdvd := Subgroup.index_dvd_of_le hle
    exact Nat.odd_iff.2 (by
      by_contra hcon
      have h2 : 2 ∣ ((centralizer ({z} : Set G)).subgroupOf
          (normalizer ((T : Subgroup G) : Set G))).index := by omega
      exact hnd (h2.trans hdvd))
  obtain ⟨hcen, hfix⟩ := conj_fixed_of_bender hz1 hz2 hzT hLz hdec hmeet hTCcomm hTCinv hB hodd
  refine CFSG.GH74.E2.tool_Z hs hnab hz hzT hzc ?_ ?_
  · intro u hu hu2
    have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    refine ⟨1, by simp, by simpa using hu, fun s hs' => ?_⟩
    simpa using hcen u hu hu2' s hs'
  · intro n hn w _ _ hw
    rw [hw]
    exact hfix n hn

end CFSG.GH74.AS16.E2
