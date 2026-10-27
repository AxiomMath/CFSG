module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrJKer

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem actsAs_pow {k : G} {α : MulAut (L ⧸ center L)} (h : ActsAs L k α) (n : ℕ) :
    ActsAs L (k ^ n) (α ^ n) := by
  induction n with
  | zero => simpa using actsAs_one L
  | succ n ih => rw [pow_succ, pow_succ]; exact actsAs_mul L ih h

private noncomputable def jOnCod {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) :
    ↥V →* ↥(jSub L V) :=
  (jOn L hV).codRestrict (jSub L V) fun x => by
    rw [← range_jOn L hV]; exact ⟨x, rfl⟩

private theorem jOnCod_apply {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) (x : ↥V) :
    (jOnCod (L := L) hV x : MulAut (L ⧸ center L)) = jOn L hV x := rfl

private theorem jOnCod_surjective {V : Subgroup G} (hV : V ≤ normalizer (L : Set G)) :
    Function.Surjective (jOnCod (L := L) hV) := by
  intro y
  have hy : (y : MulAut (L ⧸ center L)) ∈ (jOn L hV).range := by
    rw [range_jOn L hV]; exact y.2
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, Subtype.ext hx⟩

private theorem jOnCod_comap [Group.IsPerfect ↥L] {V N : Subgroup G}
    (hV : V ≤ normalizer (L : Set G)) (hNV : N ≤ V)
    (hK : ∀ x ∈ V, x ∈ centralizer (L : Set G) → x ∈ N) :
    ((jSub L N).subgroupOf (jSub L V)).comap (jOnCod (L := L) hV) = N.subgroupOf V := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    rw [jOnCod_apply, mem_jSub L] at hx
    obtain ⟨n, hnN, hnacts⟩ := hx
    have hacts : ActsAs L ((x : G) * n⁻¹) 1 := by
      have h := actsAs_mul L (jOn_actsAs L hV x) (actsAs_inv L hnacts)
      simpa using h
    have hmem : (x : G) * n⁻¹ ∈ centralizer (L : Set G) := (actsAs_one_iff L).mp hacts
    have hmemV : (x : G) * n⁻¹ ∈ V := V.mul_mem x.2 (V.inv_mem (hNV hnN))
    have hxN : (x : G) * n⁻¹ ∈ N := hK _ hmemV hmem
    have hxeq : (x : G) = ((x : G) * n⁻¹) * n := by group
    rw [hxeq]; exact N.mul_mem hxN hnN
  · intro hx
    rw [jOnCod_apply, mem_jSub L]
    exact ⟨(x : G), hx, jOn_actsAs L hV x⟩

private theorem jOnCod_map [Group.IsPerfect ↥L] {V N : Subgroup G}
    (hV : V ≤ normalizer (L : Set G)) (hNV : N ≤ V)
    (hK : ∀ x ∈ V, x ∈ centralizer (L : Set G) → x ∈ N) :
    (N.subgroupOf V).map (jOnCod (L := L) hV) = (jSub L N).subgroupOf (jSub L V) := by
  rw [← jOnCod_comap hV hNV hK]
  exact Subgroup.map_comap_eq_self_of_surjective (jOnCod_surjective hV) _

private theorem normal_subgroupOf_jSub_iff [Group.IsPerfect ↥L] {V N : Subgroup G}
    (hV : V ≤ normalizer (L : Set G)) (hNV : N ≤ V)
    (hK : ∀ x ∈ V, x ∈ centralizer (L : Set G) → x ∈ N) :
    (N.subgroupOf V).Normal ↔ ((jSub L N).subgroupOf (jSub L V)).Normal := by
  constructor
  · intro h
    rw [← jOnCod_map hV hNV hK]
    exact h.map _ (jOnCod_surjective hV)
  · intro h
    rw [← jOnCod_comap hV hNV hK]
    exact h.comap _

private noncomputable def jSubQuotientEquiv [Group.IsPerfect ↥L] {V N : Subgroup G}
    (hV : V ≤ normalizer (L : Set G)) (hNV : N ≤ V)
    (hK : ∀ x ∈ V, x ∈ centralizer (L : Set G) → x ∈ N)
    [hN1 : (N.subgroupOf V).Normal] [hN2 : ((jSub L N).subgroupOf (jSub L V)).Normal] :
    (↥V ⧸ N.subgroupOf V) ≃* (↥(jSub L V) ⧸ (jSub L N).subgroupOf (jSub L V)) := by
  refine MulEquiv.ofBijective
    (QuotientGroup.map (N.subgroupOf V) ((jSub L N).subgroupOf (jSub L V))
      (jOnCod (L := L) hV) ?_) ⟨?_, ?_⟩
  · exact le_of_eq (jOnCod_comap hV hNV hK).symm
  · rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, jOnCod_comap hV hNV hK,
      QuotientGroup.map_mk'_self]
  · apply QuotientGroup.map_surjective_of_surjective
    intro y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective y
    obtain ⟨v, hv⟩ := jOnCod_surjective hV w
    exact ⟨v, by rw [Function.comp_apply, hv, hw]⟩

theorem secProp_jSub [Group.IsPerfect ↥L] {V N : Subgroup G} (hV : V ≤ normalizer (L : Set G))
    (hNV : N ≤ V) (hK : ∀ x ∈ V, x ∈ centralizer (L : Set G) → x ∈ N)
    (Q : (Y : Type) → [Group Y] → Prop)
    (hQ : ∀ (Y Y' : Type) [Group Y] [Group Y'], (Y ≃* Y') → (Q Y ↔ Q Y')) :
    SecProp V N (fun Y _ _ _ => Q Y) ↔
      SecProp (jSub L V) (jSub L N) (fun Y _ _ _ => Q Y) := by
  have hnorm := normal_subgroupOf_jSub_iff hV hNV hK
  constructor
  · rintro ⟨hN1, hq⟩
    haveI : (N.subgroupOf V).Normal := hN1
    have hN2 : ((jSub L N).subgroupOf (jSub L V)).Normal := hnorm.mp hN1
    haveI : ((jSub L N).subgroupOf (jSub L V)).Normal := hN2
    exact ⟨hN2, (hQ _ _ (jSubQuotientEquiv hV hNV hK)).mp hq⟩
  · rintro ⟨hN2, hq⟩
    haveI : ((jSub L N).subgroupOf (jSub L V)).Normal := hN2
    have hN1 : (N.subgroupOf V).Normal := hnorm.mpr hN2
    haveI : (N.subgroupOf V).Normal := hN1
    exact ⟨hN1, (hQ _ _ (jSubQuotientEquiv hV hNV hK).symm).mp hq⟩

theorem isSylowIn_jSub [Group.IsPerfect ↥L] {p : ℕ} (hp : p.Prime) {V T : Subgroup G}
    (hV : V ≤ normalizer (L : Set G)) (hT : IsSylowIn p V T) :
    IsSylowIn p (jSub L V) (jSub L T) := by
  refine ⟨jSub_mono L hT.1, isPGroup_jSub L hT.2.1, ?_⟩
  have hmap : (T.subgroupOf V).map (jOnCod (L := L) hV) ≤
      (jSub L T).subgroupOf (jSub L V) := by
    rintro y ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, jOnCod_apply, mem_jSub L]
    exact ⟨(x : G), Subgroup.mem_subgroupOf.mp hx, jOn_actsAs L hV x⟩
  have hdvd : ((jSub L T).subgroupOf (jSub L V)).index ∣ (T.subgroupOf V).index :=
    (Subgroup.index_dvd_of_le hmap).trans
      ((T.subgroupOf V).index_map_dvd (jOnCod_surjective hV))
  intro hpdiv
  exact hT.2.2 (hpdiv.trans hdvd)

theorem isPGroup_zpowers_of_actsAs {p : ℕ} {k : G} {α : MulAut (L ⧸ center L)}
    (hα : ActsAs L k α) (hk : IsPGroup p ↥(zpowers k)) : IsPGroup p ↥(zpowers α) := by
  obtain ⟨m, hm⟩ := hk ⟨k, Subgroup.mem_zpowers k⟩
  have hkpow : k ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hαpow : α ^ p ^ m = 1 := by
    refine actsAs_unique L ?_ (actsAs_one L)
    rw [← hkpow]
    exact actsAs_pow hα (p ^ m)
  apply IsPGroup.of_card_dvd_pow (n := m)
  rw [Nat.card_zpowers]
  exact orderOf_dvd_iff_pow_eq_one.mpr hαpow

theorem ne_one_of_actsAs_of_not_mem_zL [Group.IsPerfect ↥L] {k : G} (hk : k ∈ L)
    {α : MulAut (L ⧸ center L)} (hα : ActsAs L k α) (hkz : k ∉ zL L) : α ≠ 1 := by
  intro h
  exact hkz ((actsAs_one_iff_mem_zL hk).mp (h ▸ hα))

theorem exists_pElem_of_jSub [Group.IsPerfect ↥L] {p : ℕ} (hp : p.Prime) {N : Subgroup G}
    (hN : N ≤ L) {κ : MulAut (L ⧸ center L)} (hκ : κ ∈ jSub L N)
    (hκp : IsPGroup p ↥(zpowers κ)) (hκ1 : κ ≠ 1) :
    ∃ k ∈ N, IsPGroup p ↥(zpowers k) ∧ k ∉ zL L := by
  obtain ⟨n, hnN, hnα⟩ := (mem_jSub L).mp hκ
  have hn0 : orderOf n ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite n)
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  refine ⟨n ^ m, N.pow_mem hnN m, ?_, ?_⟩
  · apply IsPGroup.of_card_dvd_pow (n := e)
    rw [Nat.card_zpowers]
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rw [← pow_mul, mul_comm m (p ^ e), ← hnm, pow_orderOf_eq_one]
  · intro hkz
    have hkL : n ^ m ∈ L := hN (N.pow_mem hnN m)
    have hacts : ActsAs L (n ^ m) (κ ^ m) := actsAs_pow hnα m
    have hone : ActsAs L (n ^ m) (1 : MulAut (L ⧸ center L)) :=
      (actsAs_one_iff_mem_zL hkL).mpr hkz
    have hκm : κ ^ m = 1 := actsAs_unique L hacts hone
    have hpκ : p ∣ orderOf κ := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hne : (⟨κ, Subgroup.mem_zpowers κ⟩ : zpowers κ) ≠ 1 := by
        intro h; exact hκ1 (Subtype.ext_iff.mp h)
      have := hκp.dvd_orderOf hne
      rwa [Subgroup.orderOf_mk] at this
    exact hm (hpκ.trans (orderOf_dvd_iff_pow_eq_one.mpr hκm))

theorem isSylowIn_zpowers_of_secProp_perm3 {Γ : Type} [Group Γ] [Finite Γ] {N K : Subgroup Γ}
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) (hKN : K ≤ N)
    (hK : IsPGroup 2 ↥K) {κ : Γ} (hκ : κ ∈ N) (hκ3 : IsPGroup 3 ↥(zpowers κ)) (hκ1 : κ ≠ 1) :
    IsSylowIn 3 N (zpowers κ) := by
  obtain ⟨hKn, ⟨e⟩⟩ := h
  haveI := hKn
  have hq : Nat.card (↥N ⧸ K.subgroupOf N) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hKidx : (K.subgroupOf N).index = 6 := by rw [Subgroup.index_eq_card, hq]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2) (G := ↥K)).mp hK
  have hcardKN : Nat.card ↥(K.subgroupOf N) = Nat.card ↥K := by
    rw [← Subgroup.card_subtype N (K.subgroupOf N), Subgroup.map_subgroupOf_eq_of_le hKN]
  have hNcard : Nat.card ↥N = 6 * 2 ^ a := by
    rw [← Subgroup.index_mul_card (H := K.subgroupOf N), hKidx, hcardKN, ha]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3ord : 3 ∣ orderOf κ := by
    have hne : (⟨κ, Subgroup.mem_zpowers κ⟩ : zpowers κ) ≠ 1 := by
      intro h; exact hκ1 (Subtype.ext_iff.mp h)
    have := hκ3.dvd_orderOf hne
    rwa [Subgroup.orderOf_mk] at this
  refine ⟨Subgroup.zpowers_le.mpr hκ, hκ3, ?_⟩
  intro hdiv
  have hrel : (zpowers κ).relIndex N * orderOf κ = Nat.card ↥N := by
    rw [← Subgroup.relIndex_mul_card (H := zpowers κ) (K := N),
      inf_eq_left.mpr (Subgroup.zpowers_le.mpr hκ), Nat.card_zpowers]
  have h9 : 9 ∣ Nat.card ↥N := by
    rw [← hrel]
    exact mul_dvd_mul hdiv h3ord
  have h9not : ¬ 9 ∣ Nat.card ↥N := by
    rw [hNcard]
    intro h9dvd
    have h' : 3 * 3 ∣ 3 * 2 ^ (a + 1) := by
      have h1 : 3 * 2 ^ (a + 1) = 6 * 2 ^ a := by rw [pow_succ]; ring
      rw [h1]; exact h9dvd
    have h3 : 3 ∣ 2 ^ (a + 1) :=
      (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 3)).mp h'
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32
  exact h9not h9

theorem exists_threeElem_of_secProp_perm3 {Γ : Type} [Group Γ] [Finite Γ] {N K : Subgroup Γ}
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) (hKN : K ≤ N) :
    ∃ κ ∈ N, IsPGroup 3 ↥(zpowers κ) ∧ κ ≠ 1 := by
  obtain ⟨hKn, ⟨e⟩⟩ := h
  haveI := hKn
  have hq : Nat.card (↥N ⧸ K.subgroupOf N) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hKidx : (K.subgroupOf N).index = 6 := by rw [Subgroup.index_eq_card, hq]
  have hNcard : 3 ∣ Nat.card ↥N := by
    rw [← Subgroup.index_mul_card (H := K.subgroupOf N), hKidx]
    exact ⟨2 * Nat.card ↥(K.subgroupOf N), by ring⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨κ, hκord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 hNcard
  refine ⟨(κ : Γ), κ.2, ?_, ?_⟩
  · apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hκord, pow_one]
  · intro h
    have h1 : κ = 1 := Subtype.ext h
    rw [h1] at hκord
    simp at hκord

theorem eq_of_secProp_perm3 {N K M : Subgroup G}
    (h : SecProp N K (fun Y _ _ _ => Nonempty (Y ≃* Equiv.Perm (Fin 3)))) (hKM : K ≤ M)
    (hMN : M ≤ N) {k a : G} (hkM : k ∈ M) (hk : k ∉ K) (hk3 : IsPGroup 3 ↥(zpowers k))
    (haM : a ∈ M) (ha : a ∉ K) (ha2 : IsPGroup 2 ↥(zpowers a)) : M = N := by
  obtain ⟨hKn, ⟨e⟩⟩ := h
  haveI := hKn
  let φ : ↥N →* Equiv.Perm (Fin 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (K.subgroupOf N))
  let M' : Subgroup (Equiv.Perm (Fin 3)) := (M.subgroupOf N).map φ
  have hperm : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hkφ : φ ⟨k, hMN hkM⟩ ∈ M' := Subgroup.mem_map.mpr ⟨⟨k, hMN hkM⟩, hkM, rfl⟩
  have haφ : φ ⟨a, hMN haM⟩ ∈ M' := Subgroup.mem_map.mpr ⟨⟨a, hMN haM⟩, haM, rfl⟩
  have hk3' : IsPGroup 3 ↥(zpowers (⟨k, hMN hkM⟩ : ↥N)) := by
    obtain ⟨j, hj⟩ := hk3 ⟨k, Subgroup.mem_zpowers k⟩
    have hkpow : k ^ 3 ^ j = 1 := by simpa using congrArg Subtype.val hj
    apply IsPGroup.of_card_dvd_pow (n := j)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hkpow
  have hk3φ : IsPGroup 3 ↥(zpowers (φ ⟨k, hMN hkM⟩)) := by
    rw [← MonoidHom.map_zpowers φ ⟨k, hMN hkM⟩]
    exact hk3'.map φ
  have hkφne : φ ⟨k, hMN hkM⟩ ≠ 1 := by
    intro h1
    have hmk : QuotientGroup.mk' (K.subgroupOf N) ⟨k, hMN hkM⟩ = 1 := by
      apply e.injective
      simpa [φ] using h1
    have hker : (⟨k, hMN hkM⟩ : ↥N) ∈ (QuotientGroup.mk' (K.subgroupOf N)).ker := by
      rw [MonoidHom.mem_ker]; exact hmk
    rw [QuotientGroup.ker_mk'] at hker
    exact hk (Subgroup.mem_subgroupOf.mp hker)
  have hkφ3 : 3 ∣ orderOf (φ ⟨k, hMN hkM⟩) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : (⟨φ ⟨k, hMN hkM⟩, Subgroup.mem_zpowers _⟩ :
        zpowers (φ ⟨k, hMN hkM⟩)) ≠ 1 := by
      intro h; exact hkφne (Subtype.ext_iff.mp h)
    have := hk3φ.dvd_orderOf hne
    rwa [Subgroup.orderOf_mk] at this
  have ha2' : IsPGroup 2 ↥(zpowers (⟨a, hMN haM⟩ : ↥N)) := by
    obtain ⟨j, hj⟩ := ha2 ⟨a, Subgroup.mem_zpowers a⟩
    have hapow : a ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    apply IsPGroup.of_card_dvd_pow (n := j)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hapow
  have ha2φ : IsPGroup 2 ↥(zpowers (φ ⟨a, hMN haM⟩)) := by
    rw [← MonoidHom.map_zpowers φ ⟨a, hMN haM⟩]
    exact ha2'.map φ
  have haφne : φ ⟨a, hMN haM⟩ ≠ 1 := by
    intro h1
    have hmk : QuotientGroup.mk' (K.subgroupOf N) ⟨a, hMN haM⟩ = 1 := by
      apply e.injective
      simpa [φ] using h1
    have hker : (⟨a, hMN haM⟩ : ↥N) ∈ (QuotientGroup.mk' (K.subgroupOf N)).ker := by
      rw [MonoidHom.mem_ker]; exact hmk
    rw [QuotientGroup.ker_mk'] at hker
    exact ha (Subgroup.mem_subgroupOf.mp hker)
  have haφ2 : 2 ∣ orderOf (φ ⟨a, hMN haM⟩) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hne : (⟨φ ⟨a, hMN haM⟩, Subgroup.mem_zpowers _⟩ :
        zpowers (φ ⟨a, hMN haM⟩)) ≠ 1 := by
      intro h; exact haφne (Subtype.ext_iff.mp h)
    have := ha2φ.dvd_orderOf hne
    rwa [Subgroup.orderOf_mk] at this
  have h3M' : 3 ∣ Nat.card M' := hkφ3.trans (Subgroup.orderOf_dvd_natCard M' hkφ)
  have h2M' : 2 ∣ Nat.card M' := haφ2.trans (Subgroup.orderOf_dvd_natCard M' haφ)
  have hM'dvd : Nat.card M' ∣ 6 := by
    have := Subgroup.card_dvd_of_le (H := M') (K := (⊤ : Subgroup (Equiv.Perm (Fin 3)))) le_top
    rwa [Subgroup.card_top, hperm] at this
  have h6dvd : 6 ∣ Nat.card M' :=
    (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2M' h3M'
  have hM'card : Nat.card M' = 6 := Nat.dvd_antisymm hM'dvd h6dvd
  have hM'top : M' = ⊤ := Subgroup.eq_top_of_card_eq M' (by rw [hM'card, hperm])
  apply le_antisymm hMN
  intro n hn
  have hn' : φ ⟨n, hn⟩ ∈ M' := by rw [hM'top]; trivial
  rw [Subgroup.mem_map] at hn'
  obtain ⟨x, hx, hxφ⟩ := hn'
  have hxM : (x : G) ∈ M := hx
  have hxeq : QuotientGroup.mk' (K.subgroupOf N) x =
      QuotientGroup.mk' (K.subgroupOf N) ⟨n, hn⟩ := by
    apply e.injective
    simpa [φ] using hxφ
  have hker : x⁻¹ * ⟨n, hn⟩ ∈ K.subgroupOf N := by
    rw [← QuotientGroup.ker_mk' (K.subgroupOf N), MonoidHom.mem_ker, map_mul, map_inv, hxeq,
      inv_mul_cancel]
  have hkerG : (x : G)⁻¹ * n ∈ K := by
    simpa using Subgroup.mem_subgroupOf.mp hker
  have hmul : (x : G) * ((x : G)⁻¹ * n) ∈ M := M.mul_mem hxM (hKM hkerG)
  rwa [mul_inv_cancel_left] at hmul

end CFSG.OddStandard.HigherRank.YamadaG23
