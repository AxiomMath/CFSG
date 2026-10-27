module

public import CFSG.GH74.GLS.Stage1.Thm4.Core98
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Transfer
public import CFSG.GH74.GLS.Stage1.Thm6.Adapters

public section

namespace CFSG.GH74.GLS.Stage1.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3 CFSG.GH74.GLS.Stage1.Thm6

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mk'_ne_one_of_orderOf_two {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) {x : G}
    (hx : orderOf x = 2) : QuotientGroup.mk' N x ≠ 1 := by
  intro h1
  have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).1 h1
  have : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hxN⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  rw [hx] at this
  exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 this)

omit [Finite G] in
theorem mem_sylow_of_central {z : G} (hz : orderOf z = 2) {S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) : z ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hS
  have hzC : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let g : ↥(centralizer ({z} : Set G)) := ⟨z, hzC⟩
  have hcomm : ∀ c : ↥(centralizer ({z} : Set G)), Commute c g := by
    intro c
    apply Subtype.ext
    have := c.2
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this
  have hnorm : (zpowers g).Normal := ⟨fun n hn c => by
    obtain ⟨m, rfl⟩ := hn
    have h1 : Commute c (g ^ m) := (hcomm c).zpow_right m
    rw [h1.eq, mul_inv_cancel_right]
    exact mem_zpowers_iff.mpr ⟨m, rfl⟩⟩
  have hord : orderOf g = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hz
  have hN : IsPGroup 2 (zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  have hle := hN.le_sylow_of_normal Q
  have hgQ : g ∈ (Q : Subgroup ↥(centralizer ({z} : Set G))) := hle (mem_zpowers g)
  rw [← hQ]
  exact ⟨g, hgQ, rfl⟩

theorem eq_of_central_involutions {X : Type} [Group X] [Finite X] {M : Subgroup X} [M.Normal]
    (hM : Odd (Nat.card M)) (hZ : Nat.card (center (X ⧸ M)) = 2) {a b : X} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hbc : ∀ g : X, g * b = b * g)
    (hac : ∀ g : X ⧸ M, g * (a : X ⧸ M) = (a : X ⧸ M) * g) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a' : center (X ⧸ M) := ⟨(a : X ⧸ M), Subgroup.mem_center_iff.2 hac⟩
  let b' : center (X ⧸ M) := ⟨(b : X ⧸ M), Subgroup.mem_center_iff.2 fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hbc g]⟩
  have ha1 : a' ≠ 1 := by
    intro h1
    exact mk'_ne_one_of_orderOf_two hM ha (congrArg Subtype.val h1)
  have hb1 : b' ≠ 1 := by
    intro h1
    exact mk'_ne_one_of_orderOf_two hM hb (congrArg Subtype.val h1)
  obtain ⟨_, -, hy⟩ := (Nat.card_eq_two_iff' (1 : center (X ⧸ M))).1 hZ
  have hab : a' = b' := (hy a' ha1).trans (hy b' hb1).symm
  have hmk : (a : X ⧸ M) = (b : X ⧸ M) := congrArg Subtype.val hab
  have hm : a⁻¹ * b ∈ M := QuotientGroup.eq.1 hmk
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb2 : b ^ 2 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hcomm : Commute a⁻¹ b := (hbc a⁻¹)
  have hsq : (a⁻¹ * b) ^ 2 = 1 := by
    rw [hcomm.mul_pow, inv_pow, ha2, hb2]; simp
  have hone := eq_one_of_pow_two_pow_of_odd (D := ↥M) hM (x := ⟨a⁻¹ * b, hm⟩) (m := 1)
    (Subtype.ext (by simpa using hsq))
  exact inv_mul_eq_one.1 (congrArg Subtype.val hone)

theorem sylow_central_of_zcen {z : G} {S : Subgroup G} (hz : orderOf z = 2)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({z} : Set G))) (hzS : z ∈ S)
    (hZ : ∀ w ∈ S, (∀ s ∈ S, s * w = w * s) → orderOf w = 2 → w = z) :
    CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ IsCentralInvolution z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST⟩ := IsPGroup.exists_le_sylow hS.isPGroup
  have hTp : IsPGroup 2 ↥(T : Subgroup G) := T.isPGroup'
  have hzT : z ∈ (T : Subgroup G) := hST hzS
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; omega
  haveI : Nontrivial ↥(T : Subgroup G) := ⟨⟨⟨z, hzT⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial ↥(center ↥(T : Subgroup G)) := hTp.center_nontrivial
  have h2dvd : 2 ∣ Nat.card ↥(center ↥(T : Subgroup G)) := by
    rcases (hTp.to_subgroup (center ↥(T : Subgroup G))).card_eq_or_dvd with h | h
    · exfalso
      have := (Nat.card_eq_one_iff_unique.1 h).1
      exact not_nontrivial_iff_subsingleton.2 this inferInstance
    · exact h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hu'ord : orderOf (((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hu
  have hu'T : (((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)) : G) ∈ (T : Subgroup G) :=
    ((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)).2
  have hucomm : ∀ s ∈ (T : Subgroup G),
      s * (((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)) : G) =
        (((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)) : G) * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 u.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  set u' : G := (((u : ↥(center ↥(T : Subgroup G))) : ↥(T : Subgroup G)) : G) with hu'
  have hu'C : u' ∈ centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hucomm z hzT).symm
  have hSu : S ⊔ zpowers u' = S := by
    have hle : S ⊔ zpowers u' ≤ (T : Subgroup G) := sup_le hST ((Subgroup.zpowers_le).2 hu'T)
    have hCle : S ⊔ zpowers u' ≤ centralizer ({z} : Set G) :=
      sup_le hS.le ((Subgroup.zpowers_le).2 hu'C)
    exact hS.eq_of_le le_sup_left hCle (hTp.to_le hle)
  have hu'S : u' ∈ S := by rw [← hSu]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u')
  have hu'z : u' = z := hZ u' hu'S (fun s hs => hucomm s (hST hs)) hu'ord
  have hzc : ∀ s ∈ (T : Subgroup G), s * z = z * s := by
    intro s hs; rw [← hu'z]; exact hucomm s hs
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzc s hs)
  have hTS : (T : Subgroup G) = S := hS.eq_of_le hST hTC hTp
  refine ⟨?_, hz, T, hzT, hzc⟩
  rw [← hTS, CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hTp, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact T.not_dvd_index

end Sylow

section Index

variable {C : Type} [Group C] [Finite C] {N K S : Subgroup C}

theorem core_relIndex_le (hA : IVK_5_1_index) [N.Normal] [K.Normal] {n : ℕ}
    (hyp : Hyp5B (C ⧸ N) (K.map (QuotientGroup.mk' N)) n) (hN : Odd (Nat.card N))
    (hS : IsPGroup 2 ↥S) : (S ⊓ K).relIndex S ≤ 2 := by
  have hle := hA _ _ n hyp
  rw [index_map_mk] at hle
  have hsub : S ⊓ (K ⊔ N) = S ⊓ K := by
    apply le_antisymm
    · rintro x ⟨hxS, hxKN⟩
      obtain ⟨m, hm⟩ := hS ⟨x, hxS⟩
      have hm' : x ^ (2 ^ m) = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      exact ⟨hxS, mem_of_mem_sup_odd hN hm' hxKN⟩
    · exact inf_le_inf_left _ le_sup_left
  have h1 : (S ⊓ K).relIndex S = (K ⊔ N).relIndex S := by
    rw [← hsub, inf_comm, Subgroup.inf_relIndex_right]
  rw [h1]
  have hpos : 0 < (K ⊔ N).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd hpos (Subgroup.relIndex_dvd_index_of_normal _ _)).trans hle

end Index

section Transfer

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inv_mul_mem_of_relIndex_two {S N : Subgroup G} (hnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N)
    (h2 : N.relIndex S = 2) {x y : G} (hx : x ∈ S) (hy : y ∈ S) (hxN : x ∉ N) (hyN : y ∉ N) :
    x⁻¹ * y ∈ N := by
  obtain ⟨a, ha, hXor⟩ := Subgroup.relIndex_eq_two_iff.1 h2
  have hxa : x * a ∈ N := by
    rcases hXor x hx with ⟨h, -⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hxN
  have hya : y * a ∈ N := by
    rcases hXor y hy with ⟨h, -⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hyN
  have := hnorm a ha ((x * a)⁻¹ * (y * a)) (mul_mem (inv_mem hxa) hya)
  have e : a * ((x * a)⁻¹ * (y * a)) * a⁻¹ = x⁻¹ * y := by group
  rwa [e] at this

theorem exists_conj_mem_of_relIndex_two (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S N : Subgroup G} (hS : IsSylow2In S ⊤) (hNS : N ≤ S)
    (hnorm : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N) (h2 : N.relIndex S = 2) {u : G} (huS : u ∈ S)
    (huN : u ∉ N) (hu2 : orderOf u = 2) : ∃ g : G, g⁻¹ * u * g ∈ N := by
  have hne : N ≠ S := by
    intro h; rw [h, Subgroup.relIndex_self] at h2; omega
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ N := by
    obtain ⟨b, hbS, hbN⟩ : ∃ b ∈ S, b ∉ N := by
      by_contra hcon
      exact hne (le_antisymm hNS fun x hx => by_contra fun hxN => hcon ⟨x, hx, hxN⟩)
    refine ⟨b, hbS, fun t ht => ?_⟩
    by_cases htN : t ∈ N
    · exact ⟨0, by simpa using htN⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_relIndex_two hnorm h2 hbS ht hbN htN⟩
  have hord : ∀ v ∈ S, v ∉ N → orderOf u ≤ orderOf v := by
    intro v hv hvN
    rw [hu2]
    have hv1 : v ≠ 1 := fun h => hvN (h ▸ N.one_mem)
    have hpos : 0 < orderOf v := orderOf_pos v
    have : orderOf v ≠ 1 := fun h => hv1 (orderOf_eq_one_iff.1 h)
    omega
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * u * g = y) → Sec12.IsExtremal S y → y ∈ N ∨ u⁻¹ * y ∈ N := by
    intro y hy _ _
    by_cases hyN : y ∈ N
    · exact Or.inl hyN
    · exact Or.inr (inv_mul_mem_of_relIndex_two hnorm h2 huS hy huN hyN)
  obtain ⟨g, hg, -⟩ := Sec12b.transfer_conj Sec12.ig_15_15 hsimple hnab hS hNS hnorm hne hcyc huS huN
    hord hext
  exact ⟨g, hg⟩

end Transfer

end CFSG.GH74.GLS.Stage1.Thm4
