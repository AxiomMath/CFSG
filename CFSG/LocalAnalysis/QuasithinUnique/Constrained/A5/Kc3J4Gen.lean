module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Gen

public section

namespace CFSG.QuasithinUnique.A5.Kc3J4

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3Gen
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem factorization_eq_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ∣ n)
    (h2 : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have a := (hp.pow_dvd_iff_le_factorization hn).1 (by simpa using h1 : p ^ 1 ∣ n)
  have b : ¬ 2 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem exists_conj_of_card_prime [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hG : ¬ p ^ 2 ∣ Nat.card G) {P P' : Subgroup G} (hP : Nat.card P = p)
    (hP' : Nat.card P' = p) : ∃ m : G, ∀ y ∈ P', ∃ z ∈ P, y = m * z * m⁻¹ := by
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hd : p ∣ Nat.card G := hP ▸ Subgroup.card_subgroup_dvd_card P
  have hf := factorization_eq_one hp.out hn hd hG
  let S : Sylow p G := Sylow.ofCard P (by rw [hP, hf, pow_one])
  let S' : Sylow p G := Sylow.ofCard P' (by rw [hP', hf, pow_one])
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq G S S'
  refine ⟨m, fun y hy => ?_⟩
  have h1 : (S' : Subgroup G) = MulAut.conj m • (S : Subgroup G) := by
    rw [← Sylow.coe_subgroup_smul, hm]
  have hy' : y ∈ (S' : Subgroup G) := hy
  rw [h1, Subgroup.mem_smul_pointwise_iff_exists] at hy'
  obtain ⟨z, hz, hzy⟩ := hy'
  exact ⟨z, hz, by simpa [MulAut.smul_def, MulAut.conj_apply] using hzy.symm⟩

theorem exists_conj_of_orderOf_prime [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}
    (hP : ¬ p ^ 2 ∣ Nat.card P) {a b : G} (ha : a ∈ P) (hb : b ∈ P) (hao : orderOf a = p)
    (hbo : orderOf b = p) : ∃ m ∈ P, ∃ k : ℤ, b = m * a ^ k * m⁻¹ := by
  let a' : P := ⟨a, ha⟩
  let b' : P := ⟨b, hb⟩
  have ha' : orderOf a' = p := by rw [← hao]; exact (Subgroup.orderOf_coe a').symm
  have hb' : orderOf b' = p := by rw [← hbo]; exact (Subgroup.orderOf_coe b').symm
  have hA : Nat.card (Subgroup.zpowers a') = p := by rw [Nat.card_zpowers, ha']
  have hB : Nat.card (Subgroup.zpowers b') = p := by rw [Nat.card_zpowers, hb']
  obtain ⟨m, hm⟩ := exists_conj_of_card_prime (G := P) hP hA hB
  obtain ⟨z, hz, hbz⟩ := hm b' (Subgroup.mem_zpowers b')
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  refine ⟨m, m.2, k, ?_⟩
  have := congrArg Subtype.val hbz
  simpa [a', b'] using this

theorem mem_of_normal_of_orderOf_prime [Finite G] {p : ℕ} [hp : Fact p.Prime] {A M : Subgroup G}
    (hAM : A ≤ M) (hN : (A.subgroupOf M).Normal) (hdvd : p ∣ Nat.card A)
    (hM : ¬ p ^ 2 ∣ Nat.card M) {x : G} (hx : x ∈ M) (hxo : orderOf x = p) : x ∈ A := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hdvd' : p ∣ Fintype.card A := by simpa [Nat.card_eq_fintype_card] using hdvd
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card p hdvd'
  have hao : orderOf (a : G) = p := by rw [Subgroup.orderOf_coe]; exact ha
  obtain ⟨m, hm, k, hk⟩ := exists_conj_of_orderOf_prime hM (hAM a.2) hx hao hxo
  have h1 : (⟨m, hm⟩ : M) * (⟨(a : G), hAM a.2⟩ : M) ^ k * (⟨m, hm⟩ : M)⁻¹ ∈ A.subgroupOf M :=
    hN.conj_mem _ ((A.subgroupOf M).zpow_mem (Subgroup.mem_subgroupOf.2 a.2) k) _
  have h2 := Subgroup.mem_subgroupOf.1 h1
  rw [hk]
  simpa using h2

theorem mem_of_isSubnormal_of_orderOf_prime [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {A B : Subgroup G} (h : IsSubnormal A B) (hdvd : p ∣ Nat.card A)
    (hB : ¬ p ^ 2 ∣ Nat.card B) {x : G} (hx : x ∈ B) (hxo : orderOf x = p) : x ∈ A := by
  induction h with
  | refl A => exact hx
  | @step H M K hHM hHN hMK ih =>
    have hMK' : M ≤ K := isSubnormal_le hMK
    have hdM : p ∣ Nat.card M := hdvd.trans (Subgroup.card_dvd_of_le hHM)
    have hM : ¬ p ^ 2 ∣ Nat.card M := fun h => hB (h.trans (Subgroup.card_dvd_of_le hMK'))
    exact mem_of_normal_of_orderOf_prime hHM hHN hdvd hM (ih hdM hB hx) hxo

theorem normalizes_of_isSubnormal [Finite G] {p : ℕ} [hp : Fact p.Prime] {L Y : Subgroup G}
    (h : IsSubnormal L Y) (hdvd : p ∣ Nat.card L) (hY : ¬ p ^ 2 ∣ Nat.card Y)
    (hgen : ∀ N : Subgroup G, (∀ x ∈ L, orderOf x = p → x ∈ N) → L ≤ N) :
    Y ≤ Subgroup.normalizer (L : Set G) := by
  have hLY : L ≤ Y := isSubnormal_le h
  have key : ∀ z ∈ Y, ∀ x ∈ L, z * x * z⁻¹ ∈ L := by
    intro z hz
    have h1 := hgen ((L.comap (MulAut.conj z).toMonoidHom)) (fun x hx hxo => by
      show z * x * z⁻¹ ∈ L
      refine mem_of_isSubnormal_of_orderOf_prime h hdvd hY
        (Y.mul_mem (Y.mul_mem hz (hLY hx)) (Y.inv_mem hz)) ?_
      have := (MulAut.conj z).orderOf_eq x
      rw [MulAut.conj_apply] at this
      rw [this, hxo])
    intro x hx
    exact h1 hx
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (Y.inv_mem hy) _ hx
  simpa [mul_assoc] using this

theorem pow_eq_one_of_mem_two_group {Q : Subgroup G} (hQ : IsPGroup 2 Q) {g : G}
    (hg : orderOf g = 5) {k : ℤ} (hk : g ^ k ∈ Q) : g ^ k = 1 := by
  obtain ⟨n, hn⟩ := hQ ⟨g ^ k, hk⟩
  have h1 : (g ^ k) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  have h2 : (g ^ k) ^ 5 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hg]
    simp [pow_orderOf_eq_one]
  have hc : Nat.Coprime (2 ^ n) 5 := by
    apply Nat.Coprime.pow_left
    norm_num
  have h3 : orderOf (g ^ k) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (g ^ k) ∣ 5 := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf (g ^ k) = 1 := Nat.eq_one_of_dvd_coprimes hc h3 h4
  exact orderOf_eq_one_iff.1 h5

theorem comm_mem_of_normalizing [Finite G] {L Q V R : Subgroup G} {g : G}
    (hgL : g ∈ L) (hg5 : orderOf g = 5) (hL25 : ¬ 5 ^ 2 ∣ Nat.card L)
    (hQL : Q ≤ L) (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ D : Subgroup G, D ≤ L → L ≤ Subgroup.normalizer (D : Set G) → IsPGroup 2 D → D ≤ Q)
    (hQV : ⁅Q, L⁆ ≤ V) (hR2 : IsPGroup 2 R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) {r : G} (hr : r ∈ R) :
    r * g * r⁻¹ * g⁻¹ ∈ V := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set x : G := r * g * r⁻¹ with hx
  have hxL : x ∈ L := (Subgroup.mem_normalizer_iff.1 (hRL hr) g).1 hgL
  have hxgR : x * g⁻¹ ∈ R := by
    have h1 : g * r⁻¹ * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hLR hgL) r⁻¹).1 (R.inv_mem hr)
    have := R.mul_mem hr h1
    simpa [hx, mul_assoc] using this
  have hxgL : x * g⁻¹ ∈ L := L.mul_mem hxL (L.inv_mem hgL)
  have hDQ : L ⊓ R ≤ Q := by
    refine hmax (L ⊓ R) inf_le_left ?_ (hR2.to_le inf_le_right)
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro d
    constructor
    · rintro ⟨hdL, hdR⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) d).1 hdL,
        (Subgroup.mem_normalizer_iff.1 (hLR hl) d).1 hdR⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer hl) d).2 h1
        exact this
      · exact (Subgroup.mem_normalizer_iff.1 (hLR hl) d).2 h2
  have hxgQ : x * g⁻¹ ∈ Q := hDQ ⟨hxgL, hxgR⟩
  set P : Subgroup G := Subgroup.zpowers g ⊔ Q with hP
  have hgP : g ∈ P := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  have hQP : Q ≤ P := le_sup_right
  have hPL : P ≤ L := sup_le ((Subgroup.zpowers_le).2 hgL) hQL
  have hP25 : ¬ 5 ^ 2 ∣ Nat.card P := fun h => hL25 (h.trans (Subgroup.card_dvd_of_le hPL))
  have hxP : x ∈ P := by
    have : x = (x * g⁻¹) * g := by group
    rw [this]
    exact P.mul_mem (hQP hxgQ) hgP
  have hxo : orderOf x = 5 := by
    have := (MulAut.conj r).orderOf_eq g
    rw [MulAut.conj_apply] at this
    rw [hx, this, hg5]
  obtain ⟨m, hmP, k, hk⟩ := exists_conj_of_orderOf_prime hP25 hgP hxP hg5 hxo
  have hzn : Subgroup.zpowers g ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le).2 (hQn hgL)
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers g) Q hzn
  have hmP' : m ∈ ((Subgroup.zpowers g * Q : Set G)) := by
    rw [← hmul]; exact hmP
  obtain ⟨gj, hgj, q', hq', rfl⟩ := hmP'
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgj
  have hq : g ^ j * q' * (g ^ j)⁻¹ ∈ Q := by
    have : g ^ j ∈ Subgroup.normalizer (Q : Set G) := hQn (L.zpow_mem hgL j)
    exact (Subgroup.mem_normalizer_iff.1 this q').1 hq'
  set q : G := g ^ j * q' * (g ^ j)⁻¹ with hqdef
  have hxq : x = q * g ^ k * q⁻¹ := by
    rw [hk, hqdef]
    have : (g ^ j * q') * g ^ k * (g ^ j * q')⁻¹ = (g ^ j * q' * (g ^ j)⁻¹) * g ^ k *
        (g ^ j * q' * (g ^ j)⁻¹)⁻¹ := by
      have hc : g ^ j * g ^ k = g ^ k * g ^ j := by rw [← zpow_add, ← zpow_add, add_comm]
      calc (g ^ j * q') * g ^ k * (g ^ j * q')⁻¹
          = g ^ j * q' * (g ^ j)⁻¹ * (g ^ j * g ^ k * (g ^ j)⁻¹) * (g ^ j * q' * (g ^ j)⁻¹)⁻¹ := by
            group
        _ = _ := by rw [hc]; group
    exact this
  have hgk : g ^ k * g⁻¹ ∈ Q := by
    have h1 : x * (g ^ k)⁻¹ ∈ Q := by
      rw [hxq]
      have : q * g ^ k * q⁻¹ * (g ^ k)⁻¹ = q * (g ^ k * q⁻¹ * (g ^ k)⁻¹) := by group
      rw [this]
      refine Q.mul_mem hq ?_
      have hn : g ^ k ∈ Subgroup.normalizer (Q : Set G) := hQn (L.zpow_mem hgL k)
      exact (Subgroup.mem_normalizer_iff.1 hn q⁻¹).1 (Q.inv_mem hq)
    have h2 := Q.mul_mem (Q.inv_mem h1) hxgQ
    have e : (x * (g ^ k)⁻¹)⁻¹ * (x * g⁻¹) = g ^ k * g⁻¹ := by group
    rwa [e] at h2
  have hgk1 : g ^ (k - 1) ∈ Q := by
    have : g ^ (k - 1) = g ^ k * g⁻¹ := by rw [zpow_sub_one]
    rw [this]; exact hgk
  have h1 := pow_eq_one_of_mem_two_group hQ2 hg5 hgk1
  have hkg : g ^ k = g := by
    have : g ^ k = g ^ (k - 1) * g := by rw [← zpow_add_one, sub_add_cancel]
    rw [this, h1, one_mul]
  rw [hkg] at hxq
  have : r * g * r⁻¹ * g⁻¹ = q * g * q⁻¹ * g⁻¹ := by rw [← hx, hxq]
  rw [this]
  have hcomm : ⁅q, g⁆ ∈ ⁅Q, L⁆ := Subgroup.commutator_mem_commutator hq hgL
  exact hQV hcomm

theorem relIndex_centralizer_le [Finite G] {L Q V R : Subgroup G} {g : G}
    (hgL : g ∈ L) (hg5 : orderOf g = 5) (hL25 : ¬ 5 ^ 2 ∣ Nat.card L)
    (hQL : Q ≤ L) (hQn : L ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hmax : ∀ D : Subgroup G, D ≤ L → L ≤ Subgroup.normalizer (D : Set G) → IsPGroup 2 D → D ≤ Q)
    (hQV : ⁅Q, L⁆ ≤ V) (hR2 : IsPGroup 2 R) (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hLR : L ≤ Subgroup.normalizer (R : Set G)) :
    (R ⊓ Subgroup.centralizer ({g} : Set G)).relIndex R ≤ Nat.card V := by
  classical
  set C : Subgroup G := R ⊓ Subgroup.centralizer ({g} : Set G) with hC
  have hmem : ∀ r : R, (r : G) * g * (r : G)⁻¹ * g⁻¹ ∈ V := fun r =>
    comm_mem_of_normalizing hgL hg5 hL25 hQL hQn hQ2 hmax hQV hR2 hRL hLR r.2
  let F : R → V := fun r => ⟨(r : G) * g * (r : G)⁻¹ * g⁻¹, hmem r⟩
  have hF : ∀ a b : R, QuotientGroup.leftRel (C.subgroupOf R) a b → F a = F b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hc : ((a⁻¹ * b : R) : G) ∈ Subgroup.centralizer ({g} : Set G) :=
      (Subgroup.mem_subgroupOf.1 hab).2
    have h1 : (a : G)⁻¹ * (b : G) * g = g * ((a : G)⁻¹ * (b : G)) :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    apply Subtype.ext
    show (a : G) * g * (a : G)⁻¹ * g⁻¹ = (b : G) * g * (b : G)⁻¹ * g⁻¹
    have : (b : G) * g * (b : G)⁻¹ = (a : G) * g * (a : G)⁻¹ := by
      calc (b : G) * g * (b : G)⁻¹ = (a : G) * ((a : G)⁻¹ * (b : G) * g) * (b : G)⁻¹ := by group
        _ = (a : G) * (g * ((a : G)⁻¹ * (b : G))) * (b : G)⁻¹ := by rw [h1]
        _ = (a : G) * g * (a : G)⁻¹ := by group
    rw [this]
  let F' : (↥R ⧸ C.subgroupOf R) → V := Quotient.lift F hF
  have hinj : Function.Injective F' := by
    intro u w
    refine Quotient.inductionOn₂' u w ?_
    intro a b hab
    have h1 : (a : G) * g * (a : G)⁻¹ * g⁻¹ = (b : G) * g * (b : G)⁻¹ * g⁻¹ :=
      congrArg Subtype.val hab
    have h2 : (a : G) * g * (a : G)⁻¹ = (b : G) * g * (b : G)⁻¹ := mul_right_cancel h1
    apply Quotient.sound'
    show QuotientGroup.leftRel (C.subgroupOf R) a b
    rw [QuotientGroup.leftRel_apply]
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact R.mul_mem (R.inv_mem a.2) b.2
    · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      show (a : G)⁻¹ * (b : G) * g = g * ((a : G)⁻¹ * (b : G))
      calc (a : G)⁻¹ * (b : G) * g = (a : G)⁻¹ * ((b : G) * g * (b : G)⁻¹) * (b : G) := by group
        _ = (a : G)⁻¹ * ((a : G) * g * (a : G)⁻¹) * (b : G) := by rw [h2]
        _ = g * ((a : G)⁻¹ * (b : G)) := by group
  have := Nat.card_le_card_of_injective F' hinj
  unfold Subgroup.relIndex Subgroup.index
  exact this

theorem le_of_normalizes_isSylowTwoOf [Finite G] {X S R : Subgroup G} (hS : IsSylowTwoOf S X)
    (hRX : R ≤ X) (hRn : X ≤ Subgroup.normalizer (R : Set G)) (hR : IsPGroup 2 R) : R ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSX, hS2, hSi⟩ := hS
  have hS2' : IsPGroup 2 ↥(S.subgroupOf X) := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have hR2' : IsPGroup 2 ↥(R.subgroupOf X) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm
  have hRN : (R.subgroupOf X).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hRn h.2) x).mp hx
    simpa using this
  have h1 := hR2'.le_sylow_of_normal (hS2'.toSylow hSi)
  intro r hr
  have := h1 (show (⟨r, hRX hr⟩ : ↥X) ∈ R.subgroupOf X from Subgroup.mem_subgroupOf.2 hr)
  exact Subgroup.mem_subgroupOf.1 ((IsPGroup.mem_toSylow hS2' hSi).1 this)

theorem not_prime_sq_dvd_of_le_sup [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {K T₀ Y : Subgroup G} (hT : IsPGroup 2 T₀) (hTK : T₀ ≤ Subgroup.normalizer (K : Set G))
    (hY : Y ≤ K ⊔ T₀) (hK : ¬ p ^ 2 ∣ Nat.card K) : ¬ p ^ 2 ∣ Nat.card Y := by
  intro h
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := Y) p h
  have hPK : P.map Y.subtype ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    have hxo : (x : G) ^ (p ^ 2) = 1 := by
      have hxP : (⟨x, hx⟩ : P) ^ Nat.card P = 1 := pow_card_eq_one'
      rw [hP] at hxP
      have := congrArg (fun z : P => ((z : Y) : G)) hxP
      simpa using this
    obtain ⟨m, hm⟩ := exists_pow_mem hT hTK (hY x.2)
    have hc : Nat.Coprime (2 ^ m) (p ^ 2) := by
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
    have h2 : (x : G) ^ (a * ((2 ^ m : ℕ) : ℤ)) = ((x : G) ^ (2 ^ m)) ^ a := by
      rw [zpow_mul', zpow_natCast]
    have h3 : (x : G) ^ (b * ((p ^ 2 : ℕ) : ℤ)) = 1 := by
      rw [zpow_mul', zpow_natCast, hxo, one_zpow]
    have : (x : G) = ((x : G) ^ (2 ^ m)) ^ a := by
      calc (x : G) = (x : G) ^ (a * ((2 ^ m : ℕ) : ℤ) + b * ((p ^ 2 : ℕ) : ℤ)) := by
            rw [hab, zpow_one]
        _ = _ := by rw [zpow_add, h2, h3, mul_one]
    show (x : G) ∈ K
    rw [this]
    exact K.zpow_mem hm a
  have h1 := Subgroup.card_dvd_of_le hPK
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hP] at h1
  exact hK h1

theorem exists_fixed_involution [Finite G] {C S : Subgroup G} (hS : IsPGroup 2 S)
    (hSC : S ≤ Subgroup.normalizer (C : Set G)) (hC : ∃ y ∈ C, orderOf y = 2) :
    ∃ y ∈ C, orderOf y = 2 ∧ ∀ s ∈ S, s * y * s⁻¹ = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥S →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hSC)
  let _ : MulAction ↥S ↥C := MulAction.compHom ↥C f
  have hsmul : ∀ (s : S) (c : C), ((s • c : C) : G) = s * c * (s : G)⁻¹ := fun s c => by
    show ((f s) c : G) = _
    simp [f]
  set F : Subgroup G := C ⊓ Subgroup.centralizer (S : Set G) with hF
  have hmod : Nat.card ↥C ≡ Nat.card (MulAction.fixedPoints ↥S ↥C) [MOD 2] :=
    hS.card_modEq_card_fixedPoints ↥C
  have hfix : Nat.card (MulAction.fixedPoints ↥S ↥C) = Nat.card F := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun c => ⟨(c.1 : G), c.1.2, ?_⟩
        invFun := fun x => ⟨⟨(x : G), x.2.1⟩, ?_⟩
        left_inv := fun c => by rfl
        right_inv := fun x => by rfl }
    · refine Subgroup.mem_centralizer_iff.2 ?_
      intro s hs
      have h := c.2 ⟨s, hs⟩
      have := congrArg (fun z : C => (z : G)) h
      rw [hsmul] at this
      simp only at this
      calc s * (c.1 : G) = (s * c.1 * s⁻¹) * s := by group
        _ = (c.1 : G) * s := by rw [this]
    · intro s
      show s • (⟨(x : G), x.2.1⟩ : C) = ⟨(x : G), x.2.1⟩
      apply Subtype.ext
      rw [hsmul]
      have := Subgroup.mem_centralizer_iff.1 x.2.2 (s : G) s.2
      calc (s : G) * (x : G) * (s : G)⁻¹ = ((x : G) * s) * (s : G)⁻¹ := by rw [this]
        _ = x := by group
  obtain ⟨y0, hy0, hy0o⟩ := hC
  have hCdvd : 2 ∣ Nat.card C := by
    have h1 : orderOf (⟨y0, hy0⟩ : C) ∣ Nat.card C := orderOf_dvd_natCard _
    have h2 : orderOf (⟨y0, hy0⟩ : C) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hy0o
    rwa [h2] at h1
  have hFdvd : 2 ∣ Nat.card F := by
    have h1 : Nat.card ↥C % 2 = Nat.card (MulAction.fixedPoints ↥S ↥C) % 2 := hmod
    rw [hfix] at h1
    have h0 : Nat.card ↥C % 2 = 0 := Nat.mod_eq_zero_of_dvd hCdvd
    exact Nat.dvd_of_mod_eq_zero (h1 ▸ h0)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 hFdvd
  refine ⟨(x : G), x.2.1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hx
  · intro s hs
    have h := Subgroup.mem_centralizer_iff.1 x.2.2 s hs
    calc s * (x : G) * s⁻¹ = ((x : G) * s) * s⁻¹ := by rw [h]
      _ = x := by group

end CFSG.QuasithinUnique.A5.Kc3J4
