module

public import CFSG.GH74.Uniqueness.Section153
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X}

omit [Finite X] in
theorem M_le_normalizer_C0 (F : Facts15 M n L D K J Mo V) :
    M ≤ normalizer (centralizer (Mo : Set X) : Set X) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => F.C0_conj hg hx
  · intro hx
    have := F.C0_conj (inv_mem hg) hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this

omit [Finite X] in
theorem Mo_comm (F : Facts15 M n L D K J Mo V) {a b : X} (ha : a ∈ Mo) (hb : b ∈ Mo) :
    a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (F.Mo_sq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (F.Mo_sq b hb)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (F.Mo_sq (a * b) (mul_mem ha hb))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

theorem exists_central_C0 (F : Facts15 M n L D K J Mo V) {S : Subgroup X}
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S M) :
    ∃ u₀ ∈ S, u₀ ∈ centralizer (Mo : Set X) ∧ u₀ ∉ Mo ∧ u₀ * u₀ ∈ Mo ∧
      ∀ s ∈ S, u₀⁻¹ * (s * u₀ * s⁻¹) ∈ Mo := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C0 : Subgroup X := centralizer (Mo : Set X) with hC0
  have hSM : S ≤ M := hS.le
  have hMoS : Mo ≤ S := le_of_isSylowOf_of_normal hS F.Mo_le_M F.Mo_normal F.Mo_isPGroup
  have hMoC0 : Mo ≤ C0 := by
    intro x hx
    rw [hC0, mem_centralizer_iff]
    intro y hy
    exact F.Mo_comm hy hx
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ C0) C0 :=
    hS.inf_of_le_normalizer F.cent_Mo_le F.M_le_normalizer_C0
  have hne : Mo ≠ S ⊓ C0 := by
    intro heq
    obtain ⟨u, huJ, hu2⟩ := F.exists_inv_J
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu2
      norm_num at hu2
    have huP : IsPGroup 2 (zpowers u) := isPGroup_zpowers_of_orderOf hu2
    obtain ⟨Q, hQ, huQ⟩ := exists_isSylowOf_ge (zpowers_le.mpr (F.J_le_C0 huJ)) huP
    obtain ⟨k, hk, hkx⟩ := hP.exists_mem_conj hQ
    have h1 : k⁻¹ * u * k ∈ S ⊓ C0 := (hkx u).mp (huQ (mem_zpowers u))
    rw [← heq] at h1
    have h2 : u ∈ Mo := by
      have := F.Mo_normal k (F.cent_Mo_le hk) _ h1
      have e : k * (k⁻¹ * u * k) * k⁻¹ = u := by group
      rwa [e] at this
    exact hu1 (F.eq_one_of_mem_L_J (F.Mo_le_L h2) huJ)
  have hSn : ∀ s ∈ S, ∀ x ∈ S ⊓ C0, s * x * s⁻¹ ∈ S ⊓ C0 := by
    intro s hs x hx
    obtain ⟨hxS, hxC⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs hxS) (inv_mem hs), F.C0_conj (hSM hs) hxC⟩
  obtain ⟨u₀, hu₀, hu₀Mo, hu₀2, hu₀c⟩ := exists_central_mod hS.isPGroup (le_inf hMoS hMoC0)
    inf_le_left (fun s hs x hx => F.Mo_normal s (hSM hs) x hx) hSn hne
  exact ⟨u₀, (mem_inf.mp hu₀).1, (mem_inf.mp hu₀).2, hu₀Mo, hu₀2, hu₀c⟩

end Facts15

omit [Finite X] in
theorem conj_mem_of_sup {A B C : Subgroup X} {d : X} (hA : ∀ x ∈ A, d * x * d⁻¹ ∈ C)
    (hB : ∀ x ∈ B, d * x * d⁻¹ ∈ C) {x : X} (hx : x ∈ A ⊔ B) : d * x * d⁻¹ ∈ C := by
  have hle : A ⊔ B ≤ C.comap (MulAut.conj d).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hA a ha
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hB b hb
  have := hle hx
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem mem_normalizer_of_conj_mem {H : Subgroup X} {g : X} (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    g ∈ normalizer (H : Set X) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : g * y * g⁻¹ = g * x * g⁻¹ := hyx
  have : y = x := by simpa using hyx'
  rwa [← this]

theorem mem_normalizer_zpowers_of_conj_inv {u y : X} (h : u * y * u⁻¹ = y⁻¹) :
    u ∈ normalizer (zpowers y : Set X) := by
  refine mem_normalizer_of_conj_mem fun w hw => ?_
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
  rw [← conj_zpow, h]
  exact zpow_mem (inv_mem (mem_zpowers y)) i

omit [Finite X] in
theorem isPGroup_zpowers_of_pow_two_pow {G : Type*} [Group G] {x : G} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : IsPGroup 2 (zpowers x) := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

namespace Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X}

theorem dihedral_or_inverted (F : Facts15 M n L D K J Mo V) {a b : X}
    (ha : a ∈ centralizer (Mo : Set X)) (hb : b ∈ centralizer (Mo : Set X)) (ha2 : a * a ∈ Mo)
    (hb2 : b * b ∈ Mo) :
    IsPGroup 2 (closure ({a, b} : Set X)) ∨
      ∃ y ∈ centralizer (Mo : Set X), (orderOf y).Prime ∧ orderOf y ≠ 2 ∧ a * y * a⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hw⟩ : ∃ w : X, w = a * b := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : X, m = (a * a) * (b * b) := ⟨_, rfl⟩
  have hmMo : m ∈ Mo := hm ▸ mul_mem ha2 hb2
  have hwC : w ∈ centralizer (Mo : Set X) := hw ▸ mul_mem ha hb
  have hconj : a * w * a⁻¹ = m * w⁻¹ := by
    rw [hw, hm]
    group
  have hmw : m * w = w * m := mem_centralizer_iff.mp hwC m hmMo
  by_cases h2 : ∃ k : ℕ, orderOf w = 2 ^ k
  · left
    obtain ⟨k, hk⟩ := h2
    have hwk : w ^ 2 ^ k = 1 := by rw [← hk, pow_orderOf_eq_one]
    have hwP : IsPGroup 2 (zpowers w) := isPGroup_zpowers_of_pow_two_pow hwk
    have haM : a ∈ M := F.cent_Mo_le ha
    have hwM : w ∈ M := F.cent_Mo_le hwC
    have hwN' : w ∈ normalizer (Mo : Set X) :=
      mem_normalizer_of_conj_mem (H := Mo) fun x hx => F.Mo_normal w hwM x hx
    have hwN : zpowers w ≤ normalizer (Mo : Set X) := zpowers_le.mpr hwN'
    have hG1 : IsPGroup 2 ↥(zpowers w ⊔ Mo) :=
      IsPGroup.to_sup_of_normal_right' hwP F.Mo_isPGroup hwN
    have hconjG : ∀ x ∈ zpowers w ⊔ Mo, a * x * a⁻¹ ∈ zpowers w ⊔ Mo := by
      intro x hx
      refine conj_mem_of_sup (A := zpowers w) (B := Mo) (fun y hy => ?_)
        (fun y hy => mem_sup_right (F.Mo_normal a haM y hy)) hx
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
      rw [← conj_zpow, hconj]
      exact zpow_mem (mul_mem (mem_sup_right hmMo) (mem_sup_left (inv_mem (mem_zpowers w)))) i
    have haN' : a ∈ normalizer ((zpowers w ⊔ Mo : Subgroup X) : Set X) :=
      mem_normalizer_of_conj_mem (H := zpowers w ⊔ Mo) hconjG
    have haN : zpowers a ≤ normalizer ((zpowers w ⊔ Mo : Subgroup X) : Set X) :=
      zpowers_le.mpr haN'
    have ha4 : a ^ 2 ^ 2 = 1 := by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq, F.Mo_sq _ ha2]
    have haP : IsPGroup 2 (zpowers a) := isPGroup_zpowers_of_pow_two_pow ha4
    have hG2 : IsPGroup 2 ↥((zpowers w ⊔ Mo) ⊔ zpowers a) :=
      IsPGroup.to_sup_of_normal_left' hG1 haP haN
    refine hG2.to_le ((closure_le _).mpr ?_)
    intro x hx
    rcases hx with rfl | hx
    · exact mem_sup_right (mem_zpowers x)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have e : b = a⁻¹ * w := by rw [hw]; group
      rw [e]
      exact mul_mem (mem_sup_right (inv_mem (mem_zpowers a)))
        (mem_sup_left (mem_sup_left (mem_zpowers w)))
  · right
    have hw0 : orderOf w ≠ 0 := (orderOf_pos w).ne'
    obtain ⟨p, hp, hpdvd, hp2⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ orderOf w ∧ p ≠ 2 := by
      by_contra hno
      push Not at hno
      exact h2 ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hw0 fun {p} hp hpd => hno p hp hpd⟩
    set e := orderOf w / p with he
    set y := w ^ e with hy
    have hyo : orderOf y = p := orderOf_pow_orderOf_div hw0 hpdvd
    refine ⟨y, pow_mem hwC e, hyo ▸ hp, hyo ▸ hp2, ?_⟩
    have h1 : a * y * a⁻¹ = m ^ e * y⁻¹ := by
      rw [hy, ← conj_pow, hconj,
        (Commute.mul_pow (show Commute m w⁻¹ from (Commute.inv_right hmw))), inv_pow]
    have hc : m ^ e * y⁻¹ = y⁻¹ * m ^ e := by
      rw [hy]
      exact (((Commute.pow_left hmw e).pow_right e).inv_right).eq
    have hcp : (m ^ e) ^ p = 1 := by
      have h3 : (a * y * a⁻¹) ^ p = 1 := by
        rw [conj_pow, ← hyo, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      rw [h1, (Commute.mul_pow hc), inv_pow, ← hyo, pow_orderOf_eq_one, inv_one, mul_one] at h3
      rwa [hyo] at h3
    have hme : (m ^ e) * (m ^ e) = 1 := F.Mo_sq _ (pow_mem hmMo e)
    have hc1 : m ^ e = 1 := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      rw [hk, pow_succ, pow_mul, pow_two, hme, one_pow, one_mul] at hcp
      exact hcp
    rw [h1, hc1, one_mul]

theorem exists_inverted (F : Facts15 M n L D K J Mo V) (hVMo : V = Mo) {u₀ : X}
    (hu₀C : u₀ ∈ centralizer (Mo : Set X)) (hu₀Mo : u₀ ∉ Mo) (hu₀2 : u₀ * u₀ ∈ Mo) :
    ∃ y ∈ centralizer (Mo : Set X), (orderOf y).Prime ∧ orderOf y ≠ 2 ∧ u₀ * y * u₀⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu₀M : u₀ ∈ M := F.cent_Mo_le hu₀C
  by_contra hno
  apply hu₀Mo
  rw [← hVMo]
  set x : ↥M := ⟨u₀, hu₀M⟩ with hx
  have hx4 : x ^ 2 ^ 2 = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    change u₀ ^ 2 ^ 2 = 1
    rw [show (2 : ℕ) ^ 2 = 2 + 2 from rfl, pow_add, sq, F.Mo_sq _ hu₀2]
  have hxP : IsPGroup 2 (zpowers x) := isPGroup_zpowers_of_pow_two_pow hx4
  have hall : ∀ g : ↥M, IsPGroup 2 (closure ({x, g * x * g⁻¹} : Set ↥M)) := by
    intro g
    have hb : (g : X) * u₀ * (g : X)⁻¹ ∈ centralizer (Mo : Set X) := F.C0_conj g.2 hu₀C
    have hb2 : ((g : X) * u₀ * (g : X)⁻¹) * ((g : X) * u₀ * (g : X)⁻¹) ∈ Mo := by
      have e : ((g : X) * u₀ * (g : X)⁻¹) * ((g : X) * u₀ * (g : X)⁻¹) =
          (g : X) * (u₀ * u₀) * (g : X)⁻¹ := by group
      rw [e]
      exact F.Mo_normal g g.2 _ hu₀2
    rcases F.dihedral_or_inverted hu₀C hb hu₀2 hb2 with hP | hinv
    · have hmap : (closure ({x, g * x * g⁻¹} : Set ↥M)).map M.subtype =
          closure ({u₀, (g : X) * u₀ * (g : X)⁻¹} : Set X) := by
        rw [MonoidHom.map_closure, Set.image_pair]
        simp [hx]
      have hP' : IsPGroup 2 ((closure ({x, g * x * g⁻¹} : Set ↥M)).map M.subtype) := by
        rw [hmap]
        exact hP
      exact hP'.of_equiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm
    · exact absurd hinv hno
  have hcore := CFSG.BaerSuzuki.baer_suzuki x hxP hall
  have hle : (CFSG.pCore 2 ↥M).map M.subtype ≤ V := by
    refine F.V_max _ (map_subtype_le _) ?_ ((CFSG.pCore_isPGroup (p := 2) (G := ↥M)).map M.subtype)
    intro g hg y hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨⟨g, hg⟩ * y' * ⟨g, hg⟩⁻¹,
      (CFSG.pCore_normal (p := 2) (G := ↥M)).conj_mem y' hy' ⟨g, hg⟩, rfl⟩
  exact hle ⟨x, hcore, rfl⟩

theorem lemma154 (F : Facts15 M n L D K J Mo V) :
    ∃ W : Subgroup X, W ≤ J ∧ W ≠ ⊥ ∧ IsPGroup 2 W ∧ ∀ j ∈ J, ∀ w ∈ W, j * w * j⁻¹ ∈ W := by
  by_contra hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVD : V ⊓ D = ⊥ := by
    by_contra hne
    apply hO
    refine ⟨V ⊓ D, fun x hx => ?_, hne, F.V_pgroup.to_le inf_le_left, fun j hj w hw => ?_⟩
    · rw [← F.C0_inf_D]
      exact mem_inf.mpr ⟨F.V_le_C0 (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
    · obtain ⟨hwV, hwD⟩ := mem_inf.mp hw
      exact mem_inf.mpr ⟨F.V_normal j (F.J_le_M hj) w hwV,
        mul_mem (mul_mem (F.J_le_D hj) hwD) (inv_mem (F.J_le_D hj))⟩
  have hinv : ∀ s ∈ V, s * s = 1 → s ∈ Mo := by
    intro s hs hs2
    by_contra hsMo
    have hs1 : s ≠ 1 := fun h1 => hsMo (h1 ▸ one_mem _)
    have hso : orderOf s = 2 := orderOf_eq_prime (by rwa [pow_two]) hs1
    obtain ⟨m, hm, hmD⟩ := F.conj_D s (F.V_le hs) hso hsMo
    have hmV : m⁻¹ * s * m ∈ V := by
      have := F.V_normal m⁻¹ (inv_mem hm) s hs
      rwa [inv_inv] at this
    have hmem : m⁻¹ * s * m ∈ V ⊓ D := mem_inf.mpr ⟨hmV, hmD⟩
    rw [hVD, mem_bot] at hmem
    apply hs1
    calc s = m * (m⁻¹ * s * m) * m⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  have hVMo := F.lemma153 hinv
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
  obtain ⟨u₀, -, hu₀C, hu₀Mo, hu₀2, hu₀c⟩ := F.exists_central_C0 hS
  obtain ⟨y, hyC, hyp, hy2, hyinv⟩ := F.exists_inverted hVMo hu₀C hu₀Mo hu₀2
  set p := orderOf y with hp
  have : Fact p.Prime := ⟨hyp⟩
  obtain ⟨PJ, hPJ⟩ := CFSG.ABGLocalTools.exists_isSylowOf p J
  have hPJC : CFSG.ABGLocalTools.IsSylowOf p PJ (centralizer (Mo : Set X)) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card (hPJ.le.trans F.J_le_C0) ?_
    rw [hPJ.card_eq]
    congr 1
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le F.J_le_C0) p
    · have h1 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (Nat.mul_pos (by positivity) Nat.card_pos).ne').mpr F.card_C0_dvd p
      have h2 : (2 ^ (3 * n) : ℕ).factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd =>
          hy2 ((Nat.prime_dvd_prime_iff_eq hyp Nat.prime_two).mp (hyp.dvd_of_dvd_pow hd))
      rw [Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply, h2,
        zero_add] at h1
      exact h1
  obtain ⟨Q, hQ, hyQ⟩ := exists_isSylowOf_ge (zpowers_le.mpr hyC)
    (isPGroup_zpowers_of_orderOf hp.symm)
  obtain ⟨c, hcC, hcx⟩ := hPJC.exists_mem_conj hQ
  have hcM : c ∈ M := F.cent_Mo_le hcC
  set y₁ := c⁻¹ * y * c with hy₁
  set u₁ := c⁻¹ * u₀ * c with hu₁
  have hy₁J : y₁ ∈ J := hPJ.le ((hcx y).mp (hyQ (mem_zpowers y)))
  have hinv₁ : u₁ * y₁ * u₁⁻¹ = y₁⁻¹ := by
    calc u₁ * y₁ * u₁⁻¹ = c⁻¹ * (u₀ * y * u₀⁻¹) * c := by rw [hu₁, hy₁]; group
      _ = y₁⁻¹ := by rw [hyinv, hy₁]; group
  have hy₁1 : y₁ ≠ 1 := by
    intro h1
    have hy1 : y = 1 := by
      calc y = c * y₁ * c⁻¹ := by rw [hy₁]; group
        _ = 1 := by rw [h1]; group
    apply hyp.one_lt.ne'
    rw [hp, hy1, orderOf_one]
  have hu₁N : u₁ ∈ normalizer (L : Set X) := by
    refine F.NY_le (zpowers y₁) (zpowers_le.mpr hy₁J) ?_ (mem_normalizer_zpowers_of_conj_inv hinv₁)
    intro hb
    apply hy₁1
    have := mem_zpowers y₁
    rw [hb] at this
    exact mem_bot.mp this
  have hu₁C : u₁ ∈ centralizer (Mo : Set X) := by
    have := F.C0_conj (inv_mem hcM) hu₀C
    rwa [inv_inv] at this
  obtain ⟨m, hm, j, hj, hu₁mj⟩ := F.cent_Mo_N u₁ hu₁N fun x hx =>
    (mem_centralizer_iff.mp hu₁C x hx).symm
  have hmu : m * u₁ = u₁ * m := mem_centralizer_iff.mp hu₁C m hm
  have hju : j = m⁻¹ * u₁ := by rw [hu₁mj]; group
  have hu₁2 : u₁ * u₁ ∈ Mo := by
    have e : u₁ * u₁ = c⁻¹ * (u₀ * u₀) * c⁻¹⁻¹ := by rw [hu₁]; group
    rw [e]
    exact F.Mo_normal c⁻¹ (inv_mem hcM) _ hu₀2
  have hjj : j * j ∈ Mo := by
    have hmu' : u₁ * m⁻¹ = m⁻¹ * u₁ := by
      calc u₁ * m⁻¹ = m⁻¹ * (m * u₁) * m⁻¹ := by group
        _ = m⁻¹ * (u₁ * m) * m⁻¹ := by rw [hmu]
        _ = m⁻¹ * u₁ := by group
    have e : j * j = (m⁻¹ * m⁻¹) * (u₁ * u₁) := by
      rw [hju]
      calc m⁻¹ * u₁ * (m⁻¹ * u₁) = m⁻¹ * (u₁ * m⁻¹) * u₁ := by group
        _ = m⁻¹ * (m⁻¹ * u₁) * u₁ := by rw [hmu']
        _ = (m⁻¹ * m⁻¹) * (u₁ * u₁) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hm) (inv_mem hm)) hu₁2
  have hj2 : j * j = 1 := F.eq_one_of_mem_L_J (F.Mo_le_L hjj) (mul_mem hj hj)
  have hj1 : j ≠ 1 := by
    intro h1
    apply hu₀Mo
    have hu₁Mo : u₁ ∈ Mo := by rw [hu₁mj, h1, mul_one]; exact hm
    have := F.Mo_normal c hcM _ hu₁Mo
    have e : c * u₁ * c⁻¹ = u₀ := by rw [hu₁]; group
    rwa [e] at this
  set S₁ := conjugate S c with hS₁
  have hS₁M : S₁ ≤ M := fun s hs => by
    have h1 := mem_conjugate_iff.mp hs
    have h2 := M.mul_mem (M.mul_mem (inv_mem hcM) (hS.le h1)) hcM
    have e : c⁻¹ * (c * s * c⁻¹) * c = s := by group
    rwa [e] at h2
  have hS₁card : Nat.card S₁ = Nat.card S := card_conjugate S c
  have hS₁j : ∀ s ∈ S₁, j⁻¹ * (s * j * s⁻¹) ∈ Mo := by
    intro s hs
    have hs' : c * s * c⁻¹ ∈ S := mem_conjugate_iff.mp hs
    have h1 := hu₀c _ hs'
    have h2 : u₁⁻¹ * (s * u₁ * s⁻¹) ∈ Mo := by
      have := F.Mo_normal c⁻¹ (inv_mem hcM) _ h1
      have e : c⁻¹ * (u₀⁻¹ * (c * s * c⁻¹ * u₀ * (c * s * c⁻¹)⁻¹)) * c⁻¹⁻¹ =
          u₁⁻¹ * (s * u₁ * s⁻¹) := by rw [hu₁]; group
      rwa [e] at this
    have hsM := hS₁M hs
    have e : j⁻¹ * (s * j * s⁻¹) =
        (u₁⁻¹ * (m * (s * m⁻¹ * s⁻¹)) * u₁⁻¹⁻¹) * (u₁⁻¹ * (s * u₁ * s⁻¹)) := by
      rw [hju]
      group
    rw [e]
    refine mul_mem ?_ h2
    have h3 : m * (s * m⁻¹ * s⁻¹) ∈ Mo := mul_mem hm (F.Mo_normal s hsM _ (inv_mem hm))
    exact F.Mo_normal u₁⁻¹ (inv_mem (F.cent_Mo_le hu₁C)) _ h3
  have horb := Sec128.ncard_conj_mul_card S₁ j
  have horbsub : {y : X | ∃ g ∈ S₁, g⁻¹ * j * g = y} ⊆ (fun x => j * x) '' (Mo : Set X) := by
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨j⁻¹ * (g⁻¹ * j * g⁻¹⁻¹), hS₁j g⁻¹ (inv_mem hg), ?_⟩
    simp only [inv_inv, mul_inv_cancel_left]
  have horbcard : {y : X | ∃ g ∈ S₁, g⁻¹ * j * g = y}.ncard ≤ 2 ^ n := by
    calc _ ≤ ((fun x => j * x) '' (Mo : Set X)).ncard := Set.ncard_le_ncard horbsub (Set.toFinite _)
      _ ≤ (Mo : Set X).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = 2 ^ n := by rw [← Nat.card_coe_set_eq]; exact F.card_Mo
  have hCle : centralizer ({j} : Set X) ⊓ S₁ ≤ Mo ⊔ D := by
    intro g hg
    obtain ⟨hgC, hgS⟩ := mem_inf.mp hg
    have hjne : zpowers j ≠ ⊥ := by
      intro hb
      apply hj1
      have := mem_zpowers j
      rw [hb] at this
      exact mem_bot.mp this
    have hgN : g ∈ normalizer (L : Set X) := F.NY_le (zpowers j) (zpowers_le.mpr hj) hjne
      (mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hgC))
    obtain ⟨m', hm', d, hd, rfl⟩ := F.NM_eq g (hS₁M hgS) hgN
    exact mul_mem (mem_sup_left hm') (mem_sup_right hd)
  have hMoD : Nat.card ↥(Mo ⊔ D) = 2 ^ n * Nat.card D := by
    rw [card_sup_of_normal (fun d hd x hx => F.Mo_normal d (F.D_le hd) x hx) ?_, F.card_Mo]
    rw [eq_bot_iff]
    intro x hx
    exact mem_bot.mpr (F.eq_one_of_mem_Mo_D (mem_inf.mp hx).1 (mem_inf.mp hx).2)
  set d2 := (Nat.card D).factorization 2 with hd2
  have hScard : Nat.card S = 2 ^ (3 * n + d2) := by
    rw [hS.card_eq, F.card_M, Nat.factorization_mul (by positivity) Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.prime_two.factorization_self, smul_eq_mul, mul_one]
  have hS₁P : IsPGroup 2 S₁ := IsPGroup.of_card (hS₁card.trans hScard)
  have hC : Nat.card ↥(centralizer ({j} : Set X) ⊓ S₁) ≤ 2 ^ (n + d2) := by
    obtain ⟨k, hk⟩ := (hS₁P.to_le inf_le_right).exists_card_eq
    have hdvd : 2 ^ k ∣ 2 ^ n * Nat.card D := by
      rw [← hk, ← hMoD]
      exact Subgroup.card_dvd_of_le hCle
    have hk' : k ≤ n + d2 := by
      have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two
        (Nat.mul_pos (by positivity) Nat.card_pos).ne').mp hdvd
      rw [Nat.factorization_mul (by positivity) Nat.card_pos.ne', Finsupp.add_apply,
        Nat.factorization_pow, Finsupp.smul_apply, Nat.prime_two.factorization_self,
        smul_eq_mul, mul_one] at h1
      exact h1
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk'
  rw [hS₁card, hScard] at horb
  have hle : 2 ^ (3 * n + d2) ≤ 2 ^ (n + (n + d2)) := by
    rw [pow_add 2 n (n + d2), ← horb]
    exact Nat.mul_le_mul horbcard hC
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  linarith [F.two_le]

end Facts15

end CFSG.GH74.Uniqueness
