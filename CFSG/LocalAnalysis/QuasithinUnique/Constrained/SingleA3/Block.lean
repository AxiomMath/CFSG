module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.QuasithinUnique

open CFSG.Open Subgroup

namespace Alt3Core

theorem alt3_step1 {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hcard : Nat.card X = 3 * Nat.card Q) :
    ∃ c : X, orderOf c = 3 ∧ c ∉ Q ∧ Q ⊔ zpowers c = ⊤ := by
  classical
  have h3 : 3 ∣ Nat.card X := ⟨Nat.card Q, hcard⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
  have hcQ : c ∉ Q := by
    intro hq
    have hQc : IsPGroup 2 (zpowers c) := hQ2.to_le (zpowers_le.mpr hq)
    have : Nat.card (zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
    obtain ⟨k, hk⟩ := hQc.exists_card_eq
    rw [this] at hk
    have h2 : (2 : ℕ) ∣ 3 ∨ k = 0 := by
      rcases k with _ | k
      · right; rfl
      · left; rw [hk]; exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    rcases h2 with h2 | h2
    · omega
    · subst h2; simp at hk
  refine ⟨c, hc, hcQ, ?_⟩
  have hidx : Q.index = 3 := by
    have := Subgroup.card_mul_index Q
    rw [hcard] at this
    have hpos : 0 < Nat.card Q := Nat.card_pos
    nlinarith
  have hle : Q ≤ Q ⊔ zpowers c := le_sup_left
  have hne : Q ≠ Q ⊔ zpowers c := fun h =>
    hcQ (h ▸ (le_sup_right : zpowers c ≤ Q ⊔ zpowers c) (mem_zpowers c))
  have hdvd : (Q ⊔ zpowers c).index ∣ 3 := hidx ▸ Subgroup.index_dvd_of_le hle
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact index_eq_one.mp h
  · exfalso
    apply hne
    exact Subgroup.eq_of_le_of_card_ge hle (by
      have h1 := Subgroup.card_mul_index (Q ⊔ zpowers c)
      have h2 := Subgroup.card_mul_index Q
      rw [h, hidx] at *
      omega)

theorem alt3_lemmaP {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    (hQ2 : IsPGroup 2 Q) {c : X} (hc3 : orderOf c = 3) (hQc : Q ⊔ zpowers c = ⊤)
    (hno2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (U : Subgroup X) [hUn : U.Normal] (hUQ : U ≤ Q) (hcomm : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ U) :
    Q ≤ U := by
  classical
  have hform : ∀ x : X, ∃ q ∈ Q, ∃ n : ℤ, x = q * c ^ n := by
    intro x
    have hx : x ∈ Q ⊔ zpowers c := hQc ▸ Subgroup.mem_top x
    obtain ⟨q, hq, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨q, hq, n, rfl⟩
  set K : Subgroup X := zpowers c ⊔ U with hK
  have hconjc : ∀ g : X, g * c * g⁻¹ ∈ K := by
    intro g
    obtain ⟨q, hq, n, rfl⟩ := hform g
    have hcn : c ^ n * c = c * c ^ n := (Commute.zpow_self c n).eq
    have : q * c ^ n * c * (q * c ^ n)⁻¹ = (q * c * q⁻¹ * c⁻¹) * c := by
      calc q * c ^ n * c * (q * c ^ n)⁻¹ = q * (c ^ n * c) * (c ^ n)⁻¹ * q⁻¹ := by group
        _ = q * (c * c ^ n) * (c ^ n)⁻¹ * q⁻¹ := by rw [hcn]
        _ = (q * c * q⁻¹ * c⁻¹) * c := by group
    rw [this]
    exact mul_mem (mem_sup_right (hcomm q hq)) (mem_sup_left (mem_zpowers c))
  have hKn : K.Normal := by
    constructor
    intro n hn g
    obtain ⟨a, ha, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : g * (c ^ m * u) * g⁻¹ = (g * c * g⁻¹) ^ m * (g * u * g⁻¹) := by
      rw [conj_zpow]; group
    rw [h1]
    exact mul_mem (zpow_mem (hconjc g) m) (mem_sup_right (hUn.conj_mem u hu g))
  have hquot : IsPGroup 2 (X ⧸ K) := by
    intro x
    induction x using QuotientGroup.induction_on with | _ z => ?_
    obtain ⟨q, hq, n, rfl⟩ := hform z
    obtain ⟨k, hk⟩ := hQ2 ⟨q, hq⟩
    refine ⟨k, ?_⟩
    have hc : ((c ^ n : X) : X ⧸ K) = 1 :=
      (QuotientGroup.eq_one_iff (N := K) (c ^ n)).mpr (zpow_mem (mem_sup_left (mem_zpowers c)) n)
    have hq1 : q ^ 2 ^ k = (1 : X) := by simpa using congrArg Subtype.val hk
    rw [QuotientGroup.mk_mul, hc, mul_one, ← QuotientGroup.mk_pow, hq1]
    exact QuotientGroup.mk_one K
  have hKtop : K = ⊤ := hno2 K hquot
  intro q hq
  have hqK : q ∈ K := hKtop ▸ Subgroup.mem_top q
  obtain ⟨a, ha, u, hu, hau⟩ := Subgroup.mem_sup_of_normal_right.mp hqK
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hcm : c ^ m ∈ Q := by
    have : c ^ m = q * u⁻¹ := by rw [← hau]; group
    rw [this]
    exact mul_mem hq (inv_mem (hUQ hu))
  obtain ⟨k, hk⟩ := hQ2 ⟨c ^ m, hcm⟩
  have h2k : (c ^ m) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h3 : (c ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : c ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, ← hc3]; exact pow_orderOf_eq_one c
    rw [this, one_zpow]
  have hord : orderOf (c ^ m) = 1 := by
    have d1 : orderOf (c ^ m) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have d2 : orderOf (c ^ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h2k
    have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd d1 d2)
  have hcm1 : c ^ m = 1 := orderOf_eq_one_iff.mp hord
  have : q = u := by rw [hcm1, one_mul] at hau; exact hau.symm
  rw [this]; exact hu

theorem alt3_key {X : Type*} [Group X] (Q : Subgroup X) [Q.Normal]
    (hQ2 : IsPGroup 2 Q) {c : X} (hc3 : orderOf c = 3) (hQc : Q ⊔ zpowers c = ⊤)
    (hno2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hexpQ : ∀ x ∈ Q, x ^ 2 = 1)
    {z : X} (hz : z ∈ Q) (hzc : c * z * c⁻¹ = z) : z = 1 := by
  let _ : CommGroup Q :=
    { (inferInstance : Group Q) with mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  have hc3' : c * c * c = 1 := by
    have h := pow_orderOf_eq_one c
    rw [hc3] at h
    rw [← pow_two, ← pow_succ]; exact h
  let φ : Q →* Q := (MulAut.conjNormal c).toMonoidHom
  have hφ : ∀ a : Q, ((φ a : Q) : X) = c * a * c⁻¹ := fun a => MulAut.conjNormal_apply c a
  have hconj3 : ∀ h : X, c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = h := by
    intro h
    calc c * (c * (c * h * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * h * (c * c * c)⁻¹ := by group
      _ = h := by rw [hc3']; simp
  have hφ3 : ∀ a : Q, φ (φ (φ a)) = a := by
    intro a
    apply Subtype.ext
    rw [hφ, hφ, hφ]
    exact hconj3 a
  let N : Q →* Q :=
    { toFun := fun a => a * φ a * φ (φ a)
      map_one' := by simp
      map_mul' := by intro a b; simp only [map_mul]; ac_rfl }
  have hN : ∀ a : Q, N a = a * φ a * φ (φ a) := fun a => rfl
  have hNφ : ∀ a : Q, N (φ a) = N a := by
    intro a; rw [hN, hN, hφ3]; ac_rfl
  let M : Subgroup X := N.ker.map Q.subtype
  have hMQ : M ≤ Q := by rintro _ ⟨a, _, rfl⟩; exact a.2
  have hMmem : ∀ x : X, x ∈ M ↔ ∃ a : Q, N a = 1 ∧ (a : X) = x := by
    intro x; constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  have hMc' : ∀ h ∈ M, c * h * c⁻¹ ∈ M := by
    intro h hh
    obtain ⟨a, ha, rfl⟩ := (hMmem h).mp hh
    exact (hMmem _).mpr ⟨φ a, by rw [hNφ]; exact ha, hφ a⟩
  have hMnorm : M.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hQc]
    refine sup_le ?_ ?_
    · intro q hq
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hhQ : h ∈ Q := hMQ hh
        have : q * h * q⁻¹ = h := by rw [hab q hq h hhQ, mul_inv_cancel_right]
        rw [this]; exact hh
      · intro hh
        have hhQ : q * h * q⁻¹ ∈ Q := hMQ hh
        have hh' : h ∈ Q := by
          have := (inferInstance : Q.Normal).conj_mem _ hhQ q⁻¹
          simpa [mul_assoc] using this
        have : q * h * q⁻¹ = h := by rw [hab q hq h hh', mul_inv_cancel_right]
        rwa [this] at hh
    · rw [zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact hMc' h
      · intro hh
        have h2 := hMc' _ (hMc' _ hh)
        rwa [hconj3] at h2
  have hMc : ∀ q ∈ Q, q * c * q⁻¹ * c⁻¹ ∈ M := by
    intro q hq
    refine (hMmem _).mpr ⟨⟨q, hq⟩ * (φ ⟨q, hq⟩)⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv, hNφ, mul_inv_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]; simp only []; group
  have hQM : Q ≤ M := alt3_lemmaP Q hQ2 hc3 hQc hno2 M hMQ hMc
  obtain ⟨a, ha, rfl⟩ := (hMmem z).mp (hQM hz)
  have hφa : φ a = a := by apply Subtype.ext; rw [hφ]; exact hzc
  have haa : a * a = 1 := by
    apply Subtype.ext; simpa [pow_two] using hexpQ a a.2
  rw [hN, hφa, hφa, haa, one_mul] at ha
  rw [ha]; rfl

theorem alt3_core {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (hQ2 : IsPGroup 2 Q) (hcard : Nat.card X = 3 * Nat.card Q)
    (hUQ : ⁅Q, (⊤ : Subgroup X)⁆ ≤ Q)
    (hcomm : ∀ q ∈ Q, ∀ u ∈ ⁅Q, (⊤ : Subgroup X)⁆, q * u = u * q)
    (hexp : ∀ x ∈ ⁅Q, (⊤ : Subgroup X)⁆, x ^ 2 = 1)
    (hno2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hZ : Nat.card (⁅Q, (⊤ : Subgroup X)⁆ : Subgroup X) =
      4 * Nat.card (⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X : Subgroup X)) :
    Q = ⁅Q, (⊤ : Subgroup X)⁆ ∧ Nat.card Q = 4 ∧ Nat.card X = 12 ∧ center X = ⊥ ∧
      ∃ c : X, orderOf c = 3 ∧ (∀ u ∈ Q, u ≠ 1 → c * u * c⁻¹ ≠ u) ∧ Q ⊔ zpowers c = ⊤ := by
  classical
  obtain ⟨c, hc3, hcQ, hQc⟩ := alt3_step1 Q hQ2 hcard
  have hQU : Q ≤ ⁅Q, (⊤ : Subgroup X)⁆ :=
    alt3_lemmaP Q hQ2 hc3 hQc hno2 _ hUQ
      (fun q hq => Subgroup.commutator_mem_commutator hq (Subgroup.mem_top c))
  have hEq : Q = ⁅Q, (⊤ : Subgroup X)⁆ := le_antisymm hQU hUQ
  have hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hcomm a ha b (hEq ▸ hb)
  have hexpQ : ∀ x ∈ Q, x ^ 2 = 1 := fun x hx => hexp x (hEq ▸ hx)
  have hkey : ∀ z ∈ Q, c * z * c⁻¹ = z → z = 1 := fun z hz hzc =>
    alt3_key Q hQ2 hc3 hQc hno2 hab hexpQ hz hzc
  have hZbot : (⁅Q, (⊤ : Subgroup X)⁆ ⊓ center X : Subgroup X) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzU, hzc⟩
    have hzQ : z ∈ Q := hEq ▸ hzU
    have h1 : c * z * c⁻¹ = z := by
      have := Subgroup.mem_center_iff.mp hzc c
      rw [this]; group
    rw [hkey z hzQ h1]; exact one_mem _
  have hcardQ : Nat.card Q = 4 := by
    have h := hZ
    rw [hZbot, Subgroup.card_bot, mul_one] at h
    rw [hEq]; exact h
  have hcardX : Nat.card X = 12 := by rw [hcard, hcardQ]
  refine ⟨hEq, hcardQ, hcardX, ?_, c, hc3, ?_, hQc⟩
  · rw [eq_bot_iff]
    intro z hz
    have hzc := Subgroup.mem_center_iff.mp hz
    have hzX : z ∈ Q ⊔ zpowers c := hQc ▸ Subgroup.mem_top z
    obtain ⟨q, hq, k, hk, hqk⟩ := Subgroup.mem_sup_of_normal_left.mp hzX
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    have hqc : c * q * c⁻¹ = q := by
      have h1 := hzc c
      rw [← hqk] at h1
      have h2 : c * q * c ^ n = q * c ^ n * c := by rw [mul_assoc]; exact h1
      have h3 : c ^ n * c = c * c ^ n := (Commute.zpow_self c n).eq
      calc c * q * c⁻¹ = (c * q * c ^ n) * (c ^ n)⁻¹ * c⁻¹ := by group
        _ = (q * c ^ n * c) * (c ^ n)⁻¹ * c⁻¹ := by rw [h2]
        _ = q * (c ^ n * c) * (c ^ n)⁻¹ * c⁻¹ := by group
        _ = q * (c * c ^ n) * (c ^ n)⁻¹ * c⁻¹ := by rw [h3]
        _ = q := by group
    have hq1 : q = 1 := hkey q hq hqc
    rw [hq1, one_mul] at hqk
    have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    have hmod : c ^ n = c ^ (n % 3) := by
      have := zpow_mod_orderOf c n
      rw [hc3] at this
      simpa using this.symm
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [← hqk, hmod, h0]; simp
    · exfalso
      rw [h1, zpow_one] at hmod
      have hQtriv : ∀ u ∈ Q, u = 1 := by
        intro u hu
        apply hkey u hu
        have := hzc u
        rw [← hqk, hmod] at this
        calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [this]
          _ = u := by group
      have : Nat.card Q = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext (by rw [hQtriv a a.2, hQtriv b b.2])⟩, ⟨1⟩⟩
      omega
    · exfalso
      have hmod2 : c ^ n = c ^ 2 := by rw [hmod, h2]; simp
      have hQtriv : ∀ u ∈ Q, u = 1 := by
        intro u hu
        apply hkey u hu
        have h1 := hzc u
        rw [← hqk, hmod2] at h1
        have hcc : c = c ^ 2 * c ^ 2 := by
          calc c = c * 1 := by simp
            _ = c * c ^ 3 := by rw [hc3']
            _ = c ^ 2 * c ^ 2 := by group
        have hcu : c * u = u * c := by
          calc c * u = (c ^ 2 * c ^ 2) * u := by rw [← hcc]
            _ = c ^ 2 * (c ^ 2 * u) := by rw [mul_assoc]
            _ = c ^ 2 * (u * c ^ 2) := by rw [h1]
            _ = (c ^ 2 * u) * c ^ 2 := by rw [mul_assoc]
            _ = (u * c ^ 2) * c ^ 2 := by rw [h1]
            _ = u * (c ^ 2 * c ^ 2) := by rw [mul_assoc]
            _ = u * c := by rw [← hcc]
        calc c * u * c⁻¹ = (u * c) * c⁻¹ := by rw [hcu]
          _ = u := by group
      have : Nat.card Q = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext (by rw [hQtriv a a.2, hQtriv b b.2])⟩, ⟨1⟩⟩
      omega
  · intro u hu hu1 hfix
    exact hu1 (hkey u hu hfix)

end Alt3Core

variable {G : Type} [Group G] [Finite G]

theorem IsShort2.alt3_structure {L : Subgroup G} (hs : IsShort2 L) (ha : IsAltType L 3) :
    blockQ L = blockU L ∧ Nat.card (blockU L) = 4 ∧ (∀ u ∈ blockU L, u ^ 2 = 1) ∧
      (∀ u ∈ blockU L, ∀ v ∈ blockU L, u * v = v * u) ∧ Nat.card L = 12 ∧
      (∀ g ∈ L, (∀ l ∈ L, g * l = l * g) → g = 1) ∧
      ∃ c ∈ L, orderOf c = 3 ∧ c ∈ Subgroup.normalizer (blockU L : Set G) ∧
        (∀ u ∈ blockU L, u ≠ 1 → c * u * c⁻¹ ≠ u) ∧ L = blockU L ⊔ Subgroup.zpowers c := by
  classical
  obtain ⟨hno2, -, ⟨hUcent, hUexp⟩, -, -⟩ := hs
  obtain ⟨α, hαs, hαk, β, hβs, hβk, -⟩ := ha
  let ι : L →* G := L.subtype
  have hι : Function.Injective ι := L.subtype_injective
  set Qt : Subgroup L := CFSG.pCore 2 L with hQt
  have hQtn : Qt.Normal := CFSG.pCore_normal
  have hQ2 : IsPGroup 2 Qt := CFSG.pCore_isPGroup
  set Ut : Subgroup L := ⁅Qt, (⊤ : Subgroup L)⁆ with hUt
  have hQmap : blockQ L = Qt.map ι := by
    unfold blockQ pCoreOf
    try with_reducible rfl
  have hUmap : blockU L = Ut.map ι := by
    change ⁅blockQ L, L⁆ = _
    rw [hQmap, hUt, Subgroup.map_commutator]
    congr 1
    rw [← MonoidHom.range_eq_map]; exact (Subgroup.range_subtype L).symm
  have hZmap : blockZ L = (Ut ⊓ Subgroup.center L).map ι := by
    ext x
    constructor
    · rintro ⟨hxU, hxc⟩
      rw [hUmap] at hxU
      obtain ⟨u, hu, rfl⟩ := hxU
      refine ⟨u, ⟨hu, Subgroup.mem_center_iff.mpr ?_⟩, rfl⟩
      intro g
      apply hι
      have := Subgroup.mem_centralizer_iff.mp hxc (ι g) g.2
      simpa using this
    · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
      refine ⟨hUmap ▸ ⟨u, hu, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h hh
      have h1 := Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
      have h2 : ((⟨h, hh⟩ * u : L) : G) = ((u * ⟨h, hh⟩ : L) : G) := congrArg Subtype.val h1
      exact h2
  have hUQ : Ut ≤ Qt := by
    have h1 : blockU L ≤ blockQ L := (le_inf_iff.mp hUcent).1
    rw [hUmap, hQmap] at h1
    exact (Subgroup.map_le_map_iff_of_injective hι).mp h1
  have hcomm : ∀ q ∈ Qt, ∀ u ∈ Ut, q * u = u * q := by
    intro q hq u hu
    have hu' : ι u ∈ blockU L := hUmap ▸ ⟨u, hu, rfl⟩
    have hq' : ι q ∈ blockQ L := hQmap ▸ ⟨q, hq, rfl⟩
    have hc := (le_inf_iff.mp hUcent).2 hu'
    have := Subgroup.mem_centralizer_iff.mp hc (ι q) hq'
    apply hι
    simpa using this
  have hexp : ∀ x ∈ Ut, x ^ 2 = 1 := by
    intro x hx
    have hx' : ι x ∈ blockU L := hUmap ▸ ⟨x, hx, rfl⟩
    have := hUexp (ι x) hx'
    apply hι
    simpa using this
  have hcardL : Nat.card L = 3 * Nat.card Qt := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv, hαk] at h1
    have h3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    rw [h3] at h1
    exact h1
  have hZ : Nat.card (Ut : Subgroup L) = 4 * Nat.card (Ut ⊓ Subgroup.center L : Subgroup L) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hβk] at h1
    have h4 : Nat.card (Multiplicative (evenWeight 3)) = 4 := by
      rw [Nat.card_congr (Multiplicative.ofAdd (α := evenWeight 3)).symm]
      have h : Nat.card (evenWeight 3) = Nat.card {x : Fin 3 → ZMod 2 // ∑ i, x i = 0} := by
        apply Nat.card_congr
        exact (Equiv.subtypeEquivRight (fun x => by simp [evenWeight, AddMonoidHom.mem_ker]))
      rw [h, Nat.card_eq_fintype_card, Fintype.card_subtype]
      decide
    rw [h4] at h1
    have hle : blockZ L ≤ blockU L := inf_le_left
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
    rw [hUmap, hZmap, Subgroup.card_map_of_injective hι, Subgroup.card_map_of_injective hι] at h1
    exact h1
  obtain ⟨hEq, hcard4, hcard12, hcenter, c', hc3, hfpf, hQc⟩ :=
    Alt3Core.alt3_core Qt hQ2 hcardL hUQ hcomm hexp hno2 hZ
  have hEq' : Qt = Ut := hEq
  have hUn : Ut.Normal := Subgroup.commutator_normal Qt ⊤
  have hmapEq : blockQ L = blockU L := by
    rw [hQmap, hUmap, hEq']
  refine ⟨hmapEq, ?_, ?_, ?_, hcard12, ?_, ι c', c'.2, ?_, ?_, ?_, ?_⟩
  · rw [hUmap, Subgroup.card_map_of_injective hι, ← hEq']; exact hcard4
  · intro u hu
    have hu' : u ∈ Ut.map ι := hUmap ▸ hu
    obtain ⟨x, hx, rfl⟩ := hu'
    have := hexp x hx
    rw [← map_pow, this, map_one]
  · intro u hu v hv
    have hu' : u ∈ Ut.map ι := hUmap ▸ hu
    have hv' : v ∈ Ut.map ι := hUmap ▸ hv
    obtain ⟨x, hx, rfl⟩ := hu'
    obtain ⟨y, hy, rfl⟩ := hv'
    rw [← map_mul, ← map_mul, hcomm x (hUQ hx) y hy]
  · intro g hg hgc
    have h1 : (⟨g, hg⟩ : L) ∈ Subgroup.center L := by
      refine Subgroup.mem_center_iff.mpr ?_
      intro l
      apply Subtype.ext
      exact (hgc l l.2).symm
    rw [hcenter, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exact (Subgroup.orderOf_coe c').trans hc3
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hUmap]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨c' * u * c'⁻¹, hUn.conj_mem u hu c', by simp⟩
    · rintro ⟨u, hu, hh⟩
      refine ⟨c'⁻¹ * u * c', ?_, ?_⟩
      · simpa using hUn.conj_mem u hu c'⁻¹
      · rw [map_mul, map_mul, map_inv, hh]; group
  · intro u hu hu1
    have hu' : u ∈ Ut.map ι := hUmap ▸ hu
    obtain ⟨x, hx, rfl⟩ := hu'
    have hx1 : x ≠ 1 := fun h => hu1 (by rw [h, map_one])
    intro hcon
    apply hfpf x (hUQ hx) hx1
    apply hι
    simpa using hcon
  · have h1 := congrArg (Subgroup.map ι) hQc
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    rw [hUmap, ← hEq']
    exact h1.symm

end CFSG.QuasithinUnique
