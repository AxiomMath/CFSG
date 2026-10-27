module

public import CFSG.GH74.Generic.S3.Nbhd

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

section TwoGroups

variable {G : Type} [Group G]

theorem exists_involution_pow {a : G} {k : ℕ} (hk : orderOf a = 2 ^ k) (ha1 : a ≠ 1) :
    ∃ n : ℕ, orderOf (a ^ n) = 2 := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero, orderOf_eq_one_iff] at hk
      exact absurd hk ha1
    · exact h
  have h2 : 2 ∣ orderOf a := by
    rw [hk]
    exact dvd_pow_self 2 (by omega)
  exact ⟨orderOf a / 2, orderOf_pow_orderOf_div (by rw [hk]; positivity) h2⟩

theorem eq_bot_of_pGroup_no_involution {H : Subgroup G} (hH : IsPGroup 2 ↥H)
    (hno : ∀ a ∈ H, a * a = 1 → a = 1) : H = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  by_contra hne
  have ha1 : a ≠ 1 := fun h => hne (by rw [h]; exact one_mem _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hH) ⟨a, ha⟩
  have hk' : orderOf a = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe ⟨a, ha⟩
  obtain ⟨n, hn⟩ := exists_involution_pow hk' ha1
  obtain ⟨hb2, hb1⟩ := orderOf_eq_prime_iff.1 hn
  exact hb1 (hno _ (H.pow_mem ha n) (by rw [← pow_two]; exact hb2))

theorem exists_central_involution [Finite G] {H : Subgroup G} (hH : IsPGroup 2 ↥H) (hne : H ≠ ⊥) :
    ∃ z ∈ H, z * z = 1 ∧ z ≠ 1 ∧ ∀ h ∈ H, h * z = z * h := by
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).2 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥(Subgroup.center ↥H) := hH.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥H))
  have hcc : (c : ↥H) ∈ Subgroup.center ↥H := c.2
  have hc1' : ((c : ↥H) : G) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hH) (c : ↥H)
  have hk' : orderOf ((c : ↥H) : G) = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (c : ↥H)
  obtain ⟨n, hn⟩ := exists_involution_pow hk' hc1'
  obtain ⟨hb2, hb1⟩ := orderOf_eq_prime_iff.1 hn
  refine ⟨((c : ↥H) : G) ^ n, H.pow_mem (c : ↥H).2 n, by rw [← pow_two]; exact hb2, hb1, ?_⟩
  intro h hh
  have := Subgroup.mem_center_iff.1 hcc ⟨h, hh⟩
  have hcomm : ((c : ↥H) : G) * h = h * ((c : ↥H) : G) := by
    have := congrArg Subtype.val this
    simpa using this.symm
  exact ((Commute.pow_right (hcomm.symm : Commute h ((c : ↥H) : G)) n)).eq

theorem unique_involution_of_noCommInv [Finite G] {H : Subgroup G} (hH : IsPGroup 2 ↥H) (hne : H ≠ ⊥)
    (hrk : NoCommInv H) :
    ∃ z ∈ H, z * z = 1 ∧ z ≠ 1 ∧ ∀ a ∈ H, a * a = 1 → a = 1 ∨ a = z := by
  obtain ⟨z, hz, hzz, hz1, hzc⟩ := exists_central_involution hH hne
  refine ⟨z, hz, hzz, hz1, fun a ha haa => ?_⟩
  rcases hrk a ha z hz haa hzz (hzc a ha) with h | h | h
  · exact Or.inl h
  · exact absurd h hz1
  · exact Or.inr h

theorem inf_eq_bot_of_no_involution {A B : Subgroup G} (hAB : IsPGroup 2 ↥(A ⊓ B))
    (hno : ∀ a ∈ A, a ∈ B → a * a = 1 → a = 1) : A ⊓ B = ⊥ :=
  eq_bot_of_pGroup_no_involution hAB fun a ha haa => hno a ha.1 ha.2 haa

theorem eq_of_involutions_of_cyclic {D : Subgroup G} [Finite D] (hD : IsCyclic ↥D) {a b : G}
    (ha : a ∈ D) (hb : b ∈ D) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha2 : a * a = 1) (hb2 : b * b = 1) :
    a = b := by
  classical
  by_contra hab
  have : Fintype D := Fintype.ofFinite D
  have hle := IsCyclic.card_pow_eq_one_le (α := D) (n := 2) (by norm_num)
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset D) ⊆ Finset.univ.filter (fun g : D => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hg with rfl | rfl | rfl
    · simp
    · exact Subtype.ext (by simpa [pow_two] using ha2)
    · exact Subtype.ext (by simpa [pow_two] using hb2)
  have hcard : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset D).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · intro h
      apply hab
      exact congrArg Subtype.val h
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  have := Finset.card_le_card hsub
  omega

theorem exists_split_homs {L R T Q : Subgroup G} (hQT : Q ≤ T) (hRT : R ≤ T) (hRL : R ≤ L)
    (hRC : R ⊓ centralizer (L : Set G) = ⊥)
    (hsplit : ∀ a ∈ Q, ∃ z ∈ R ⊓ centralizer (R : Set G), a * z⁻¹ ∈ centralizer (L : Set G)) :
    ∃ φ ψ : ↥Q →* G, (∀ a, φ a ∈ R ⊓ centralizer (R : Set G)) ∧
      (∀ a, ψ a ∈ T ⊓ centralizer (L : Set G)) ∧ (∀ a : ↥Q, (a : G) = φ a * ψ a) := by
  classical
  have huniq : ∀ (a z1 z2 : G), z1 ∈ R → z2 ∈ R → a * z1⁻¹ ∈ centralizer (L : Set G) →
      a * z2⁻¹ ∈ centralizer (L : Set G) → z1 = z2 := by
    intro a z1 z2 h1 h2 c1 c2
    have hmem : z1 * z2⁻¹ ∈ R ⊓ centralizer (L : Set G) := by
      refine ⟨R.mul_mem h1 (R.inv_mem h2), ?_⟩
      have := (centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).inv_mem c1) c2
      have e : (a * z1⁻¹)⁻¹ * (a * z2⁻¹) = z1 * z2⁻¹ := by group
      rwa [e] at this
    rw [hRC, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.1 hmem
  let z : ↥Q → G := fun a => Classical.choose (hsplit a a.2)
  have hz : ∀ a : ↥Q, z a ∈ R ⊓ centralizer (R : Set G) ∧
      (a : G) * (z a)⁻¹ ∈ centralizer (L : Set G) := fun a => Classical.choose_spec (hsplit a a.2)
  have hzmul : ∀ a b : ↥Q, z (a * b) = z a * z b := by
    intro a b
    apply huniq ((a * b : ↥Q) : G) _ _ (hz (a * b)).1.1 (R.mul_mem (hz a).1.1 (hz b).1.1)
      (hz (a * b)).2
    have hcb : (b : G) * (z b)⁻¹ ∈ centralizer (L : Set G) := (hz b).2
    have hza : (z a)⁻¹ ∈ L := L.inv_mem (hRL (hz a).1.1)
    have hcomm : ((b : G) * (z b)⁻¹) * (z a)⁻¹ = (z a)⁻¹ * ((b : G) * (z b)⁻¹) :=
      (mem_centralizer_iff.1 hcb _ hza).symm
    have e : ((a * b : ↥Q) : G) * (z a * z b)⁻¹ =
        ((a : G) * (z a)⁻¹) * ((b : G) * (z b)⁻¹) :=
      calc ((a * b : ↥Q) : G) * (z a * z b)⁻¹
          = (a : G) * ((b : G) * (z b)⁻¹) * (z a)⁻¹ := by
            rw [Subgroup.coe_mul]; group
        _ = (a : G) * ((z a)⁻¹ * ((b : G) * (z b)⁻¹)) := by rw [mul_assoc, hcomm]
        _ = ((a : G) * (z a)⁻¹) * ((b : G) * (z b)⁻¹) := by rw [← mul_assoc]
    rw [e]
    exact (centralizer (L : Set G)).mul_mem (hz a).2 hcb
  let φ : ↥Q →* G := MonoidHom.mk' z hzmul
  refine ⟨φ, MonoidHom.mk' (fun a => (a : G) * (z a)⁻¹) ?_, fun a => (hz a).1, fun a => ?_,
    fun a => ?_⟩
  · intro a b
    have hcb : (b : G) * (z b)⁻¹ ∈ centralizer (L : Set G) := (hz b).2
    have hza : (z a)⁻¹ ∈ L := L.inv_mem (hRL (hz a).1.1)
    have hcomm : ((b : G) * (z b)⁻¹) * (z a)⁻¹ = (z a)⁻¹ * ((b : G) * (z b)⁻¹) :=
      (mem_centralizer_iff.1 hcb _ hza).symm
    rw [hzmul, Subgroup.coe_mul]
    calc (a : G) * (b : G) * (z a * z b)⁻¹
        = (a : G) * ((b : G) * (z b)⁻¹) * (z a)⁻¹ := by group
      _ = (a : G) * ((z a)⁻¹ * ((b : G) * (z b)⁻¹)) := by rw [mul_assoc, hcomm]
      _ = ((a : G) * (z a)⁻¹) * ((b : G) * (z b)⁻¹) := by rw [← mul_assoc]
  · refine ⟨T.mul_mem (hQT a.2) (T.inv_mem (hRT (hz a).1.1)), (hz a).2⟩
  · show (a : G) = z a * ((a : G) * (z a)⁻¹)
    have hcomm : z a * ((a : G) * (z a)⁻¹) = ((a : G) * (z a)⁻¹) * z a :=
      mem_centralizer_iff.1 (hz a).2 (z a) (hRL (hz a).1.1)
    rw [hcomm]
    group

theorem cyclic_of_split [Finite G] {L R T Q : Subgroup G} (hQT : Q ≤ T) (hRT : R ≤ T) (hRL : R ≤ L)
    (hRC : R ⊓ centralizer (L : Set G) = ⊥)
    (hsplit : ∀ a ∈ Q, ∃ z ∈ R ⊓ centralizer (R : Set G), a * z⁻¹ ∈ centralizer (L : Set G))
    (hinf : Q ⊓ (T ⊓ centralizer (L : Set G)) = ⊥)
    (hcyc : IsCyclic ↥(R ⊓ centralizer (R : Set G))) :
    IsCyclic ↥Q ∧ ∀ n : ℕ, (∀ z ∈ R ⊓ centralizer (R : Set G), orderOf z ∣ n) →
      ∀ a ∈ Q, orderOf a ∣ n := by
  obtain ⟨φ, ψ, hφ, hψ, hdec⟩ := exists_split_homs hQT hRT hRL hRC hsplit
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have e : (a : G) = ψ a := by rw [hdec a, ha, one_mul]
    have hmem : (a : G) ∈ Q ⊓ (T ⊓ centralizer (L : Set G)) := ⟨a.2, by rw [e]; exact hψ a⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hinj' : Function.Injective (φ.codRestrict (R ⊓ centralizer (R : Set G)) hφ) := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  refine ⟨isCyclic_of_injective _ hinj', fun n hn a ha => ?_⟩
  have h1 : orderOf (φ ⟨a, ha⟩) = orderOf (⟨a, ha⟩ : ↥Q) := orderOf_injective φ hinj ⟨a, ha⟩
  have h2 : orderOf (⟨a, ha⟩ : ↥Q) = orderOf a := (Subgroup.orderOf_coe ⟨a, ha⟩).symm
  rw [← h2, ← h1]
  exact hn _ (hφ ⟨a, ha⟩)

theorem embed_of_split {L R T Q : Subgroup G} (hQT : Q ≤ T) (hRT : R ≤ T) (hRL : R ≤ L)
    (hRC : R ⊓ centralizer (L : Set G) = ⊥)
    (hsplit : ∀ a ∈ Q, ∃ z ∈ R ⊓ centralizer (R : Set G), a * z⁻¹ ∈ centralizer (L : Set G))
    (hQR : Q ⊓ R = ⊥) :
    ∃ ψ : ↥Q →* G, Function.Injective ψ ∧ ∀ a, ψ a ∈ T ⊓ centralizer (L : Set G) := by
  obtain ⟨φ, ψ, hφ, hψ, hdec⟩ := exists_split_homs hQT hRT hRL hRC hsplit
  refine ⟨ψ, ?_, hψ⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have e : (a : G) = φ a := by rw [hdec a, ha, mul_one]
  have hmem : (a : G) ∈ Q ⊓ R := ⟨a.2, by rw [e]; exact (hφ a).1⟩
  rw [hQR, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem not_central_involution_of_odd {L : Subgroup G} (hodd : Odd (Nat.card ↥(center ↥L))) {a : G}
    (ha : a ∈ L) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hc : ∀ i ∈ L, i * a = a * i) : False := by
  have hmem : (⟨a, ha⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  have hdvd := Subgroup.orderOf_dvd_natCard (center ↥L) hmem
  have hord : orderOf (⟨a, ha⟩ : ↥L) = 2 := by
    have h1 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
    rw [← Subgroup.orderOf_coe]
    exact h1
  rw [hord] at hdvd
  exact (Nat.not_odd_iff_even.2 even_two) (Odd.of_dvd_nat hodd hdvd)

theorem mem_normalizer_of_conj {L : Subgroup G} {c : G} (h1 : ∀ i ∈ L, c * i * c⁻¹ ∈ L)
    (h2 : ∀ i ∈ L, c⁻¹ * i * c ∈ L) : c ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff]
  intro i
  refine ⟨fun hi => h1 i hi, fun hi => ?_⟩
  have := h2 _ hi
  have e : c⁻¹ * (c * i * c⁻¹) * c = i := by group
  rwa [e] at this

theorem side_lemma [Finite G] {L T Q : Subgroup G} {u : G} (hTpg : IsPGroup 2 ↥T)
    (hTL : ∀ s ∈ T, ∀ i ∈ L, s * i * s⁻¹ ∈ L) (hodd : Odd (Nat.card ↥(center ↥L)))
    (hZcyc : IsCyclic ↥((T ⊓ L) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G)))
    (hksplit : ∀ A : Subgroup G, A ≤ normalizer (L : Set G) → IsPGroup 2 ↥A →
      (∀ a ∈ A, ∀ r ∈ T ⊓ L, a * r = r * a) →
        ∀ a ∈ A, ∃ z ∈ (T ⊓ L) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G),
          a * z⁻¹ ∈ centralizer (L : Set G))
    (hQT : Q ≤ T) (hQconj : ∀ s ∈ T, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q)
    (hQinv : ∀ a ∈ Q, a * a = 1 → a = 1 ∨ a = u) (huL : u ∉ L)
    (hQQ' : Q ⊓ (T ⊓ centralizer (L : Set G)) = ⊥) {n : ℕ}
    (hn : ∀ z ∈ (T ⊓ L) ⊓ centralizer ((T ⊓ L : Subgroup G) : Set G), orderOf z ∣ n) :
    IsCyclic ↥Q ∧ (∀ a ∈ Q, orderOf a ∣ n) ∧
      ∃ ψ : ↥Q →* G, Function.Injective ψ ∧ ∀ a, ψ a ∈ T ⊓ centralizer (L : Set G) := by
  have hRC : (T ⊓ L) ⊓ centralizer (L : Set G) = ⊥ := by
    apply inf_eq_bot_of_no_involution
      (hTpg.to_le (show (T ⊓ L) ⊓ centralizer (L : Set G) ≤ T from fun a ha => ha.1.1))
    intro a ha hc haa
    by_contra ha1
    exact not_central_involution_of_odd hodd ha.2 haa ha1 (mem_centralizer_iff.1 hc)
  have hQR : Q ⊓ (T ⊓ L) = ⊥ := by
    apply inf_eq_bot_of_no_involution
      (hTpg.to_le (show Q ⊓ (T ⊓ L) ≤ T from fun a ha => ha.2.1))
    intro a ha hb haa
    by_contra ha1
    rcases hQinv a ha haa with h1 | h1
    · exact ha1 h1
    · exact huL (h1 ▸ hb.2)
  have hRnorm : ∀ s ∈ T, ∀ r ∈ T ⊓ L, s * r * s⁻¹ ∈ T ⊓ L := fun s hs r hr =>
    ⟨T.mul_mem (T.mul_mem hs hr.1) (T.inv_mem hs), hTL s hs r hr.2⟩
  have hcomm : ∀ a ∈ Q, ∀ r ∈ T ⊓ L, a * r = r * a := by
    intro a ha r hr
    have h1 : a * r * a⁻¹ * r⁻¹ ∈ Q ⊓ (T ⊓ L) := by
      constructor
      · have h3 : r * a⁻¹ * r⁻¹ ∈ Q := hQconj r hr.1 a⁻¹ (Q.inv_mem ha)
        have e : a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) := by group
        rw [e]
        exact Q.mul_mem ha h3
      · exact (T ⊓ L).mul_mem (hRnorm a (hQT ha) r hr) ((T ⊓ L).inv_mem hr)
    rw [hQR, Subgroup.mem_bot] at h1
    have h2 : a * r * a⁻¹ = r := mul_inv_eq_one.1 h1
    calc a * r = (a * r * a⁻¹) * a := by group
      _ = r * a := by rw [h2]
  have hQN : Q ≤ normalizer (L : Set G) := fun q hq =>
    mem_normalizer_of_conj (hTL q (hQT hq)) (fun i hi => by
      have := hTL q⁻¹ (T.inv_mem (hQT hq)) i hi
      simpa using this)
  have hsplit := hksplit Q hQN (hTpg.to_le hQT) hcomm
  obtain ⟨hcyc, hord⟩ := cyclic_of_split hQT inf_le_left inf_le_right hRC hsplit hQQ' hZcyc
  refine ⟨hcyc, fun a ha => hord n hn a ha, ?_⟩
  exact embed_of_split hQT inf_le_left inf_le_right hRC hsplit hQR

end TwoGroups

end CFSG.GH74.Generic.S3
