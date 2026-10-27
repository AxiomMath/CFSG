module

public import CFSG.GH74.Uniqueness.SU.SU10Setup
public import CFSG.GH74.Uniqueness.SU.SU10Lift
public import CFSG.GH74.Uniqueness.SU.SU10X
public import CFSG.GH74.Uniqueness.SU.SU10Trans
public import CFSG.GH74.Uniqueness.SU.SU10Syl
public import CFSG.GH74.Uniqueness.SU.SU8Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU8 CFSG.Blueprint

structure BarCfg (X : Type) [Group X] (T : Sylow 2 X) (K₁ : Subgroup X) (w : X) : Prop where
  uniq : ∀ q ∈ (T : Subgroup X) ⊓ centralizer (K₁ : Set X), q * q = 1 → q = 1 ∨ q = w
  comm : ∀ a ∈ (T : Subgroup X), ∀ b ∈ (T : Subgroup X), a * a = 1 → b * b = 1 → a * b = b * a
  inv_le : ∀ t ∈ (T : Subgroup X), t * t = 1 → t ∈ K₁ ⊔ centralizer (K₁ : Set X)
  orb : ∃ (m : ℕ) (y : X), 1 ≤ m ∧ Nat.card (omegaOne (T : Subgroup X)) = 2 ^ (m + 1) ∧
    y ∈ normalizer ((omegaOne (T : Subgroup X) : Subgroup X) : Set X) ∧ y * w = w * y ∧
    ∀ a ∈ omegaOne (T : Subgroup X), ∀ b ∈ omegaOne (T : Subgroup X), a ≠ 1 → a ≠ w → b ≠ 1 →
      b ≠ w → ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b ∨ y ^ j * a * (y ^ j)⁻¹ = b * w

theorem BarCfg.of_bender
    {X : Type} [Group X] [Finite X] (T : Sylow 2 X) {K : Subgroup X}
    [K.Normal] (hK : CFSG.BenderSuzuki.IsBenderGroup ↥K) {w : X} (hw2 : orderOf w = 2)
    (hwc : ∀ x : X, x * w = w * x) (hwT : w ∈ (T : Subgroup X))
    (hC : Open.pRank 2 (centralizer (K : Set X)) = 1)
    (hle : Subgroup.closure {g : X | g ∈ (T : Subgroup X) ∧ g * g = 1} ≤
      K ⊔ centralizer (K : Set X)) : BarCfg X T K w := by
  obtain ⟨-, hq, -, hcomm, horb⟩ := bender_config T hK hw2 hwc hwT hC hle
  exact ⟨hq, hcomm, fun t ht htt => hle (Subgroup.subset_closure ⟨ht, htt⟩), horb⟩

theorem omegaOne_map_of_injOn {A B : Type} [Group A] [Group B] {φ : A →* B} {X : Subgroup A}
    (h : Set.InjOn φ X) : omegaOne (X.map φ) = (omegaOne X).map φ := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hg⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    have : φ (x * x) = φ 1 := by rw [map_mul, map_one]; exact hg
    exact h (X.mul_mem hx hx) X.one_mem this
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, hx2, map_one]⟩

@[expose] def zbar {G : Type} [Group G] (z : G) : Hbar (centralizer ({z} : Set G)) :=
  QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({z} : Set G)))
    ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

section Lift

variable {G : Type} [Group G] [Finite G] {Hh S : Subgroup G}

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 Hh)

theorem eq_of_map_eq (hS : IsSylowIn Hh S) {a b : G} (ha : a ∈ S) (hb : b ∈ S)
    (h : π ⟨a, hS.1 ha⟩ = π ⟨b, hS.1 hb⟩) : a = b :=
  congrArg Subtype.val (injOn_of_isPGroup (isPGroup_subgroupOf hS)
    (Subgroup.mem_subgroupOf.mpr ha) (Subgroup.mem_subgroupOf.mpr hb) h)

omit [Finite G] in
theorem map_mem_hbarImage (hSH : S ≤ Hh) {x : G} (hx : x ∈ S) :
    π ⟨x, hSH hx⟩ ∈ hbarImage Hh S :=
  Subgroup.mem_map.mpr ⟨⟨x, hSH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

omit [Finite G] in
theorem map_mul_self_eq_one {t : G} (htH : t ∈ Hh) (htt : t * t = 1) :
    π ⟨t, htH⟩ * π ⟨t, htH⟩ = 1 := by
  rw [← map_mul]
  have : (⟨t, htH⟩ : ↥Hh) * ⟨t, htH⟩ = 1 := Subtype.ext htt
  rw [this, map_one]

theorem exists_involution_of_ne_bot {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ g ∈ P, orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hP
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
  have hdvd : 2 ∣ Nat.card P := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 hdvd
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

theorem commute_of_bar (hS : IsSylowIn Hh S) {T : Sylow 2 (Hbar Hh)}
    (hT : (T : Subgroup (Hbar Hh)) = hbarImage Hh S)
    (hcomm : ∀ a ∈ (T : Subgroup (Hbar Hh)), ∀ b ∈ (T : Subgroup (Hbar Hh)), a * a = 1 →
      b * b = 1 → a * b = b * a) :
    ∀ a ∈ S, ∀ b ∈ S, a * a = 1 → b * b = 1 → a * b = b * a := by
  intro a ha b hb haa hbb
  have haH : a ∈ Hh := hS.1 ha
  have hbH : b ∈ Hh := hS.1 hb
  have hTa : π ⟨a, haH⟩ ∈ (T : Subgroup (Hbar Hh)) := by
    rw [hT]
    exact map_mem_hbarImage hS.1 ha
  have hTb : π ⟨b, hbH⟩ ∈ (T : Subgroup (Hbar Hh)) := by
    rw [hT]
    exact map_mem_hbarImage hS.1 hb
  have h3 := hcomm _ hTa _ hTb (map_mul_self_eq_one haH haa) (map_mul_self_eq_one hbH hbb)
  apply eq_of_map_eq hS (S.mul_mem ha hb) (S.mul_mem hb ha)
  have e1 : (⟨a * b, hS.1 (S.mul_mem ha hb)⟩ : ↥Hh) = ⟨a, haH⟩ * ⟨b, hbH⟩ := rfl
  have e2 : (⟨b * a, hS.1 (S.mul_mem hb ha)⟩ : ↥Hh) = ⟨b, hbH⟩ * ⟨a, haH⟩ := rfl
  rw [e1, e2, map_mul, map_mul]
  exact h3

omit [Finite G] in
theorem omegaOne_le_sup (hS : IsSylowIn Hh S) {T : Sylow 2 (Hbar Hh)}
    (hT : (T : Subgroup (Hbar Hh)) = hbarImage Hh S) {L : Subgroup G}
    (hinv : ∀ t ∈ (T : Subgroup (Hbar Hh)), t * t = 1 →
      t ∈ hbarImage Hh L ⊔ centralizer ((hbarImage Hh L : Subgroup (Hbar Hh)) : Set (Hbar Hh))) :
    omegaOne S ≤ L ⊔ centralizerBar Hh L := by
  unfold omegaOne
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨htS, htt⟩
  have htH : t ∈ Hh := hS.1 htS
  have hTt : π ⟨t, htH⟩ ∈ (T : Subgroup (Hbar Hh)) := by
    rw [hT]
    exact map_mem_hbarImage hS.1 htS
  exact mem_L_sup_centralizerBar rfl htH (hinv _ hTt (map_mul_self_eq_one htH htt))

theorem unique_involution_Q (hS : IsSylowIn Hh S) {T : Sylow 2 (Hbar Hh)}
    (hT : (T : Subgroup (Hbar Hh)) = hbarImage Hh S) {L : Subgroup G} {z : G} (hzS : z ∈ S)
    {zb : Hbar Hh} (hzb : zb = π ⟨z, hS.1 hzS⟩)
    (huniq : ∀ q ∈ (T : Subgroup (Hbar Hh)) ⊓
      centralizer ((hbarImage Hh L : Subgroup (Hbar Hh)) : Set (Hbar Hh)),
      q * q = 1 → q = 1 ∨ q = zb) :
    ∀ q ∈ S ⊓ centralizerBar Hh L, q * q = 1 → q = 1 ∨ q = z := by
  rintro q ⟨hqS, hqC⟩ hqq
  obtain ⟨q', hq', hq'q⟩ := hqC
  have hqH : q ∈ Hh := hS.1 hqS
  have hq'eq : q' = ⟨q, hqH⟩ := Subtype.ext hq'q
  have hTq : π ⟨q, hqH⟩ ∈ (T : Subgroup (Hbar Hh)) ⊓
      centralizer ((hbarImage Hh L : Subgroup (Hbar Hh)) : Set (Hbar Hh)) := by
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact map_mem_hbarImage hS.1 hqS
    · rw [← hq'eq]
      exact Subgroup.mem_comap.mp hq'
  rcases huniq _ hTq (map_mul_self_eq_one hqH hqq) with h1 | h1
  · left
    exact eq_of_map_eq hS hqS (Subgroup.one_mem _) (by rw [h1]; exact (map_one π).symm)
  · right
    exact eq_of_map_eq hS hqS hzS (h1.trans hzb)

theorem Q_tame_of_unique {L : Subgroup G} {z : G} (hSp : IsPGroup 2 S)
    (hHz : ∀ x : G, x * z = z * x → x ∈ Hh) (hLn : Hh ≤ normalizer (L : Set G))
    (hQ : ∀ q ∈ S ⊓ centralizerBar Hh L, q * q = 1 → q = 1 ∨ q = z) :
    ∀ x : G, x ∉ normalizer (L : Set G) →
      (S ⊓ centralizerBar Hh L) ⊓ conjSub x (S ⊓ centralizerBar Hh L) = ⊥ := by
  intro x hx
  by_contra hne
  have hBp : IsPGroup 2 ↥((S ⊓ centralizerBar Hh L) ⊓ conjSub x (S ⊓ centralizerBar Hh L)) :=
    hSp.to_le (inf_le_left.trans inf_le_left)
  obtain ⟨g, hgB, hg2⟩ := exists_involution_of_ne_bot hBp hne
  have hgg : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg2, sq] at this
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  have hgz : g = z := (hQ g hgB.1 hgg).resolve_left hg1
  obtain ⟨q, hqQ, hqg⟩ := hgB.2
  have hqg0 : x * q * x⁻¹ = g := hqg
  have hqg' : x * q * x⁻¹ = z := hqg0.trans hgz
  have hqq : q * q = 1 := by
    have h1 : (x * q * x⁻¹) * (x * q * x⁻¹) = 1 := by
      rw [hqg0]
      exact hgg
    calc q * q = x⁻¹ * ((x * q * x⁻¹) * (x * q * x⁻¹)) * x := by group
      _ = 1 := by rw [h1]; group
  have hq1 : q ≠ 1 := by
    intro h
    apply hg1
    rw [← hqg0, h]
    group
  have hqz : q = z := (hQ q hqQ hqq).resolve_left hq1
  have hxz : x * z = z * x := by
    rw [hqz] at hqg'
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hqg']
  exact hx (hLn (hHz x hxz))

theorem exists_lift_orb (hS : IsSylowIn Hh S) {w : G} (hw : w ∈ S) (hwH : w ∈ Hh)
    {T : Sylow 2 (Hbar Hh)} (hT : (T : Subgroup (Hbar Hh)) = hbarImage Hh S)
    {wb : Hbar Hh} (hwb : wb = π ⟨w, hwH⟩) {m : ℕ} {yb : Hbar Hh}
    (hcard : Nat.card (omegaOne (T : Subgroup (Hbar Hh))) = 2 ^ (m + 1))
    (hybN : yb ∈ normalizer
      ((omegaOne (T : Subgroup (Hbar Hh)) : Subgroup (Hbar Hh)) : Set (Hbar Hh)))
    (htr : ∀ a ∈ omegaOne (T : Subgroup (Hbar Hh)), ∀ b ∈ omegaOne (T : Subgroup (Hbar Hh)),
      a ≠ 1 → a ≠ wb → b ≠ 1 → b ≠ wb →
        ∃ j : ℤ, yb ^ j * a * (yb ^ j)⁻¹ = b ∨ yb ^ j * a * (yb ^ j)⁻¹ = b * wb) :
    ∃ y : G, y ∈ Hh ∧ Nat.card (omegaOne S) = 2 ^ (m + 1) ∧
      y ∈ normalizer ((omegaOne S : Subgroup G) : Set G) ∧
      ∀ a ∈ omegaOne S, ∀ b ∈ omegaOne S, a ≠ 1 → a ≠ w → b ≠ 1 → b ≠ w →
        ∃ j : ℤ, y ^ j * a * (y ^ j)⁻¹ = b ∨ y ^ j * a * (y ^ j)⁻¹ = b * w := by
  subst hwb
  rw [hT] at hcard hybN htr
  set S₁ : Subgroup ↥Hh := S.subgroupOf Hh with hS₁
  have hS₁p : IsPGroup 2 S₁ := isPGroup_subgroupOf hS
  have hinj : Set.InjOn π S₁ := injOn_of_isPGroup hS₁p
  have hsubinj : Set.InjOn Hh.subtype S₁ := fun x _ y _ hxy => Subtype.ext hxy
  have hS₁S : S₁.map Hh.subtype = S := by
    rw [hS₁, Subgroup.subgroupOf_map_subtype, inf_of_le_left hS.1]
  have hA₁T : omegaOne (hbarImage Hh S) = (omegaOne S₁).map π :=
    omegaOne_map_of_injOn hinj
  have hA₁S : omegaOne S = (omegaOne S₁).map Hh.subtype := by
    rw [← omegaOne_map_of_injOn hsubinj, hS₁S]
  have hA₁le : omegaOne S₁ ≤ S₁ := omegaOne_le S₁
  have hinjA : Set.InjOn π (omegaOne S₁) := fun x hx y hy hxy => hinj (hA₁le hx) (hA₁le hy) hxy
  have hsubinjA : Set.InjOn Hh.subtype (omegaOne S₁) := fun x _ y _ hxy => Subtype.ext hxy
  have hcardS : Nat.card (omegaOne S) = 2 ^ (m + 1) := by
    rw [hA₁S, card_map_of_injOn hsubinjA, ← card_map_of_injOn hinjA, ← hA₁T]
    exact hcard
  have hA₁p : IsPGroup 2 (omegaOne S₁) := hS₁p.to_le hA₁le
  rw [hA₁T, normalizer_map_eq hA₁p] at hybN
  obtain ⟨y₁, hy₁N, hy₁⟩ := hybN
  have hyN : (y₁ : G) ∈ normalizer ((omegaOne S : Subgroup G) : Set G) := by
    rw [hA₁S]
    exact Subgroup.le_normalizer_map Hh.subtype ⟨y₁, hy₁N, rfl⟩
  refine ⟨y₁, y₁.2, hcardS, hyN, ?_⟩
  intro a ha b hb ha1 haw hb1 hbw
  rw [hA₁S] at ha hb
  obtain ⟨a₁, ha₁, ha₁a⟩ := ha
  obtain ⟨b₁, hb₁, hb₁b⟩ := hb
  have ha₁a' : (a₁ : G) = a := by simpa using ha₁a
  have hb₁b' : (b₁ : G) = b := by simpa using hb₁b
  subst ha₁a' hb₁b'
  have hw₁ : (⟨w, hwH⟩ : ↥Hh) ∈ S₁ := Subgroup.mem_subgroupOf.mpr hw
  have hne1 : ∀ c : ↥Hh, c ∈ omegaOne S₁ → (c : G) ≠ 1 → π c ≠ 1 := by
    intro c hc hc1 hπ
    apply hc1
    have : c = 1 := hinj (hA₁le hc) S₁.one_mem (by rw [hπ, map_one])
    rw [this]
    rfl
  have hnew : ∀ c : ↥Hh, c ∈ omegaOne S₁ → (c : G) ≠ w → π c ≠ π ⟨w, hwH⟩ := by
    intro c hc hcw hπ
    apply hcw
    have : c = ⟨w, hwH⟩ := hinj (hA₁le hc) hw₁ hπ
    rw [this]
  have hπa : π a₁ ∈ omegaOne (hbarImage Hh S) := by
    rw [hA₁T]
    exact ⟨a₁, ha₁, rfl⟩
  have hπb : π b₁ ∈ omegaOne (hbarImage Hh S) := by
    rw [hA₁T]
    exact ⟨b₁, hb₁, rfl⟩
  obtain ⟨j, hj⟩ := htr (π a₁) hπa (π b₁) hπb (hne1 a₁ ha₁ ha1) (hnew a₁ ha₁ haw)
    (hne1 b₁ hb₁ hb1) (hnew b₁ hb₁ hbw)
  refine ⟨j, ?_⟩
  have hconjA : ∀ c ∈ omegaOne S₁, y₁ ^ j * c * (y₁ ^ j)⁻¹ ∈ omegaOne S₁ := fun c hc =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpow_mem _ hy₁N j) c).mp hc
  have hπconj : π (y₁ ^ j * a₁ * (y₁ ^ j)⁻¹) = π y₁ ^ j * π a₁ * (π y₁ ^ j)⁻¹ := by
    simp only [map_mul, map_zpow, map_inv]
  rw [hy₁] at hπconj
  rcases hj with hj | hj
  · refine Or.inl ?_
    have h1 : y₁ ^ j * a₁ * (y₁ ^ j)⁻¹ = b₁ :=
      hinj (hA₁le (hconjA a₁ ha₁)) (hA₁le hb₁) (by rw [hπconj]; exact hj)
    have := congrArg Subtype.val h1
    simpa using this
  · refine Or.inr ?_
    have h1 : y₁ ^ j * a₁ * (y₁ ^ j)⁻¹ = b₁ * ⟨w, hwH⟩ :=
      hinj (hA₁le (hconjA a₁ ha₁)) (S₁.mul_mem (hA₁le hb₁) hw₁)
        (by rw [hπconj, map_mul]; exact hj)
    have := congrArg Subtype.val h1
    simpa using this

end Lift

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem hyp20A_of_barCfg {S : Sylow 2 G} {M : Subgroup G} {z : G} (h : Hyp21 S M z)
    {L : Subgroup G} (hLc : GLS.IsPCompIn 2 (centralizer ({z} : Set G)) L)
    (hLn : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hLb : CFSG.BenderSuzuki.IsBenderGroup ↥(hbarImage (centralizer ({z} : Set G)) L) ∨
      Nonempty ((↥(hbarImage (centralizer ({z} : Set G)) L) ⧸
        center ↥(hbarImage (centralizer ({z} : Set G)) L)) ≃* CFSG.Theory.Comparator.SzModel 1))
    {T : Sylow 2 (Hbar (centralizer ({z} : Set G)))}
    (hT : (T : Subgroup (Hbar (centralizer ({z} : Set G)))) =
      hbarImage (centralizer ({z} : Set G)) (S : Subgroup G))
    (hcfg : BarCfg (Hbar (centralizer ({z} : Set G))) T
      (hbarImage (centralizer ({z} : Set G)) L) (zbar z)) :
    Hyp20A z (S : Subgroup G) L (omegaOne (S : Subgroup G)) := by
  classical
  have hzH : z ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hS : IsSylowIn (centralizer ({z} : Set G)) (S : Subgroup G) := h.isSylowIn
  have hzS : z ∈ (S : Subgroup G) := h.z_mem
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.z_invol, sq] at this
  have hcommG := commute_of_bar hS hT hcfg.comm
  have hel : Open.IsElemAbelian 2 (omegaOne (S : Subgroup G)) := isElemAbelian_omegaOne hcommG
  have hzA : z ∈ omegaOne (S : Subgroup G) := Subgroup.subset_closure ⟨hzS, hzz⟩
  obtain ⟨m, yb, hm, hcardT, hybN, -, htr⟩ := hcfg.orb
  obtain ⟨y, hyH, hcardS, hyN, htrans⟩ :=
    exists_lift_orb hS hzS hzH hT (wb := zbar z) rfl hcardT hybN htr
  have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
  have htransG := exists_mem_normalizer_conj_omegaOne h.simple h.nonab S h.z_invol hzS h.z_center
    hcommG hm hcardS hyN hyz htrans
  refine
    { simple := h.simple, nonab := h.nonab, kgh := h.kgh, z_invol := h.z_invol,
      S_sylow_H := hS, L_comp := hLc, L_normal := hLn, L_bender := hLb,
      A_ge := ?_, A_le := omegaOne_le_sup hS hT hcfg.inv_le, A_elem := hel,
      A_strongly_closed := ?_,
      Q_tame := Q_tame_of_unique S.isPGroup'
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr hx) hLn
        (unique_involution_Q hS hT hzS (zb := zbar z) rfl hcfg.uniq),
      S_sylow := isSylowIn_top S, irreducible := ?_ }
  · refine sup_le ?_ ((Subgroup.zpowers_le).mpr hzA)
    unfold omegaOne
    exact Subgroup.closure_mono (fun t ht => ⟨ht.1.1, ht.2⟩)
  · refine ⟨S, omegaOne_le _, fun a ha g hg => ?_⟩
    have ha2 : a * a = 1 := by
      have := (SU1.isElemAbelian_iff.mp hel).2 a ha
      rwa [sq] at this
    have hgg : (g⁻¹ * a * g) * (g⁻¹ * a * g) = 1 := by
      calc (g⁻¹ * a * g) * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
        _ = 1 := by rw [ha2]; group
    exact Subgroup.subset_closure ⟨hg, hgg⟩
  · intro B hBA hB1 hBN
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
    have hbA : (b : G) ∈ omegaOne (S : Subgroup G) := hBA b.2
    have hb1' : (b : G) ≠ 1 := fun h' => hb1 (Subtype.ext h')
    obtain ⟨n, hnN, hnz⟩ := htransG _ hbA hb1'
    have hzB : z ∈ B := by
      have h1 : n * z * n⁻¹ ∈ B := hnz ▸ b.2
      exact (Subgroup.mem_normalizer_iff.mp (hBN hnN) z).mpr h1
    refine le_antisymm hBA fun a ha => ?_
    by_cases ha1 : a = 1
    · rw [ha1]
      exact B.one_mem
    · obtain ⟨n', hn'N, hn'z⟩ := htransG a ha ha1
      rw [← hn'z]
      exact (Subgroup.mem_normalizer_iff.mp (hBN hn'N) z).mp hzB

end Assembly

end CFSG.GH74.Uniqueness.SU.SU10
