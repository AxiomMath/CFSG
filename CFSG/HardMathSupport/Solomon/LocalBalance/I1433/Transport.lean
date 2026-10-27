module

public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SimpleCfg

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.Yardstones.Md42047359a2a
open scoped commutatorElement

namespace Transport

@[expose] def autQuot (Y : Type*) [Group Y] : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) where
  toFun α := QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x; obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x; rfl
  map_mul' α β := by
    ext x; obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x; rfl

@[expose] def conjAct {X : Type*} [Group X] (K : Subgroup X) [K.Normal] :
    X →* MulAut (↥K ⧸ Subgroup.center ↥K) :=
  (autQuot ↥K).comp MulAut.conjNormal

theorem conjAct_coe {X : Type*} [Group X] (K : Subgroup X) [K.Normal] (k₀ : ↥K) :
    conjAct K (k₀ : X) = MulAut.conj (QuotientGroup.mk k₀ : ↥K ⧸ Subgroup.center ↥K) := by
  ext s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  show (QuotientGroup.mk (MulAut.conjNormal (k₀ : X) k) : ↥K ⧸ _) = _
  rw [MulAut.conjNormal_val]
  simp [MulAut.conj_apply]

theorem mem_centralizer_of_conjAct_eq_one {X : Type*} [Group X] {K : Subgroup X} [K.Normal]
    (hperf : Group.IsPerfect ↥K) {g : X} (hg : conjAct K g = 1) :
    g ∈ Subgroup.centralizer (K : Set X) := by
  set α : MulAut ↥K := MulAut.conjNormal g with hα
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, π (α k) = (conjAct K g) (π k) := fun k => rfl
  have hall : ∀ k, α k = k := by
    have : (⊤ : Subgroup ↥K) ≤ fixSubgroup α := by
      have h1 : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
        have := hperf.commutator_eq_top; rwa [_root_.commutator_def] at this
      rw [← h1, Subgroup.commutator_le]
      intro a _ b _
      apply comm_mem_fixSubgroup π hker α (conjAct K g) hαβ
      · show conjAct K g (π a) = π a
        rw [hg]; rfl
      · show conjAct K g (π b) = π b
        rw [hg]; rfl
    intro k
    exact this (Subgroup.mem_top k)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 := congrArg Subtype.val (hall ⟨k, hk⟩)
  rw [hα, MulAut.conjNormal_apply] at h1
  have h2 : g * k = k * g := by
    calc g * k = g * k * g⁻¹ * g := by group
      _ = k * g := by rw [show g * k * g⁻¹ = k from h1]
  exact h2.symm

theorem map_commutator_le {G H : Type*} [Group G] [Group H] (f : G →* H) :
    (commutator G).map f ≤ commutator H := by
  rw [_root_.commutator_def, Subgroup.map_commutator, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem map_conjAct_le_derived {X : Type*} [Group X] {K Q : Subgroup X} [K.Normal]
    (h : Q.map (MulAut.conjNormal : X →* MulAut ↥K) ≤ commutator (MulAut ↥K)) :
    Q.map (conjAct K) ≤ commutator (MulAut (↥K ⧸ Subgroup.center ↥K)) := by
  have h2 : Q.map (conjAct K) =
      (Q.map (MulAut.conjNormal : X →* MulAut ↥K)).map (autQuot ↥K) := by
    rw [Subgroup.map_map]; rfl
  rw [h2]
  exact (Subgroup.map_mono h).trans (map_commutator_le _)

section InjOn

variable {X M : Type*} [Group X] [Group M] {ρ : X →* M} {Q : Subgroup X}

theorem injOn_of_ker (hinj : ∀ g ∈ Q, ρ g = 1 → g = 1) : Set.InjOn ρ Q := by
  intro a ha b hb hab
  have h : a⁻¹ * b = 1 :=
    hinj _ (Q.mul_mem (Q.inv_mem ha) hb) (by rw [map_mul, map_inv, hab, inv_mul_cancel])
  exact inv_mul_eq_one.1 h

theorem injective_subgroupMap (hinj : Set.InjOn ρ Q) : Function.Injective (ρ.subgroupMap Q) := by
  intro a b hab
  exact Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val hab))

@[expose] noncomputable def mapEquivOfInjOn (hinj : Set.InjOn ρ Q) : ↥Q ≃* ↥(Q.map ρ) :=
  MulEquiv.ofBijective (ρ.subgroupMap Q)
    ⟨injective_subgroupMap hinj, MonoidHom.subgroupMap_surjective ρ Q⟩

theorem card_map_of_injOn (hinj : Set.InjOn ρ Q) : Nat.card ↥(Q.map ρ) = Nat.card ↥Q :=
  (Nat.card_congr (mapEquivOfInjOn hinj).toEquiv).symm

theorem center_map_of_injOn (hinj : Set.InjOn ρ Q) :
    (Subgroup.center ↥(Q.map ρ)).map (Q.map ρ).subtype =
      ((Subgroup.center ↥Q).map Q.subtype).map ρ := by
  ext m
  constructor
  · rintro ⟨⟨m, hm⟩, hmc, rfl⟩
    obtain ⟨a, haQ, rfl⟩ := hm
    refine ⟨a, ⟨⟨a, haQ⟩, ?_, rfl⟩, rfl⟩
    have hmc' := Subgroup.mem_center_iff.1 hmc
    refine Subgroup.mem_center_iff.2 fun b => ?_
    have h := hmc' ⟨ρ b, b, b.2, rfl⟩
    have h' : ρ (b * a) = ρ (a * b) := by simpa using congrArg Subtype.val h
    exact Subtype.ext (hinj (Q.mul_mem b.2 haQ) (Q.mul_mem haQ b.2) h')
  · rintro ⟨a, ⟨⟨a, haQ⟩, hac, rfl⟩, rfl⟩
    refine ⟨⟨ρ a, a, haQ, rfl⟩, ?_, rfl⟩
    have hac' := Subgroup.mem_center_iff.1 hac
    refine Subgroup.mem_center_iff.2 ?_
    rintro ⟨m, b, hb, rfl⟩
    have h := congrArg (fun y : ↥Q => ρ (y : X)) (hac' ⟨b, hb⟩)
    exact Subtype.ext (by simpa using h)

theorem exists_noncomm_map (hinj : Set.InjOn ρ Q) (h : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) :
    ∃ a ∈ Q.map ρ, ∃ b ∈ Q.map ρ, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  refine ⟨ρ a, ⟨a, ha, rfl⟩, ρ b, ⟨b, hb, rfl⟩, fun h' => hab ?_⟩
  rw [← map_mul, ← map_mul] at h'
  exact hinj (Q.mul_mem ha hb) (Q.mul_mem hb ha) h'

theorem exponent_map (h : ∀ g ∈ Q, g ^ 3 = 1) : ∀ m ∈ Q.map ρ, m ^ 3 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, h a ha, map_one]

end InjOn

theorem center_map_conjAct {X : Type*} [Group X] {K Q : Subgroup X} [K.Normal] {z : X}
    (hzK : z ∈ K) (hZz : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers z)
    (hinj : Set.InjOn (conjAct K) Q) :
    (Subgroup.center ↥(Q.map (conjAct K))).map (Q.map (conjAct K)).subtype =
      Subgroup.zpowers (MulAut.conj (QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K)) := by
  rw [center_map_of_injOn hinj, hZz, MonoidHom.map_zpowers]
  exact congrArg Subgroup.zpowers (conjAct_coe K ⟨z, hzK⟩)

theorem orderOf_mk_eq_three {X : Type*} [Group X] {K : Subgroup X} {z : X} (hzK : z ∈ K)
    (hz3 : orderOf z = 3) (hzZ : z ∉ (Subgroup.center ↥K).map K.subtype) :
    orderOf (QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K) = 3 := by
  have hz1 : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  have hx3 : (QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨z, hzK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hz1)
    rw [this]; rfl
  have hx1 : (QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff] at h
    exact hzZ ⟨⟨z, hzK⟩, h, rfl⟩
  exact orderOf_eq_prime hx3 hx1

theorem coprime_orderOf_of_mem_gLAPPrimeCore {G : Type*} [Group G] [Finite G] {o : G}
    (ho : o ∈ GLAPPrimeCore 3 G) : Nat.Coprime 3 (orderOf o) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 G)) := CFSG.pPrimeCore_coprime_card
  have hd : orderOf o ∣ Nat.card (GLAPPrimeCore 3 G) := by
    have := orderOf_dvd_natCard (⟨o, ho⟩ : GLAPPrimeCore 3 G)
    rwa [Subgroup.orderOf_mk] at this
  exact Nat.Coprime.coprime_dvd_right hd hc

theorem inf_center_eq_bot {X : Type} [Group X] [Finite X] {K J : Subgroup X}
    (hZ3 : IsPGroup 3 ↥(Subgroup.center ↥K)) {z : X} (hz3 : orderOf z = 3)
    (hzK : z ∉ (Subgroup.center ↥K).map K.subtype) (hJK : J ≤ K)
    (hctr : ((Subgroup.zpowers z).subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) =
      Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    J ⊓ (Subgroup.center ↥K).map K.subtype = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
  rw [eq_bot_iff]
  rintro w ⟨hwJ, a, haZ, hwa⟩
  rw [Subgroup.mem_bot]
  by_contra hw1
  have hwc : ∀ y : ↥J, y * (⟨w, hwJ⟩ : ↥J) = ⟨w, hwJ⟩ * y := by
    intro y
    apply Subtype.ext
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 haZ ⟨(y : X), hJK y.2⟩)
    simpa [← hwa] using this
  obtain ⟨m, hm⟩ := hZ3 ⟨a, haZ⟩
  have hwm : (⟨w, hwJ⟩ : ↥J) ^ (3 ^ m) = 1 := by
    apply Subtype.ext
    have := congrArg (fun y : ↥(Subgroup.center ↥K) => ((y : ↥K) : X)) hm
    simpa [← hwa] using this
  have hmk : (QuotientGroup.mk (⟨w, hwJ⟩ : ↥J) : ↥J ⧸ GLAPPrimeCore 3 ↥J) ∈
      Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hwc y]
  rw [← hctr] at hmk
  obtain ⟨u, hu, hu'⟩ := hmk
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hu)
  have ho : u⁻¹ * ⟨w, hwJ⟩ ∈ GLAPPrimeCore 3 ↥J := QuotientGroup.eq.1 hu'
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    show ((u : ↥J) : X) ^ 3 = 1
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz1, one_zpow]
  have hcomm : Commute u⁻¹ (⟨w, hwJ⟩ : ↥J) := hwc u⁻¹
  have ho3 : (u⁻¹ * ⟨w, hwJ⟩ : ↥J) ^ 3 = (⟨w, hwJ⟩ : ↥J) ^ 3 := by
    rw [hcomm.mul_pow, inv_pow, hu3, inv_one, one_mul]
  have hcop := coprime_orderOf_of_mem_gLAPPrimeCore ho
  have hcop3 : Nat.Coprime 3 (orderOf ((u⁻¹ * ⟨w, hwJ⟩ : ↥J) ^ 3)) :=
    Nat.Coprime.coprime_dvd_right (orderOf_pow_dvd 3) hcop
  have hdvd : orderOf ((u⁻¹ * ⟨w, hwJ⟩ : ↥J) ^ 3) ∣ 3 ^ m := by
    rw [ho3]
    exact (orderOf_pow_dvd 3).trans (orderOf_dvd_of_pow_eq_one hwm)
  have h1 : orderOf ((u⁻¹ * ⟨w, hwJ⟩ : ↥J) ^ 3) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left m hcop3).symm hdvd
  have h3 : (u⁻¹ * ⟨w, hwJ⟩ : ↥J) ^ 3 = 1 := orderOf_eq_one_iff.1 h1
  have h4 : orderOf (u⁻¹ * ⟨w, hwJ⟩ : ↥J) = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop.symm (orderOf_dvd_of_pow_eq_one h3)
  have h5 : u⁻¹ * ⟨w, hwJ⟩ = 1 := orderOf_eq_one_iff.1 h4
  have hwu : (⟨w, hwJ⟩ : ↥J) = u := (inv_mul_eq_one.1 h5).symm
  have hwz : w = z ^ n := by
    have := congrArg Subtype.val hwu
    exact this.trans hn.symm
  have hwo : orderOf w = 3 := by
    have hd : orderOf w ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hwz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz1, one_zpow]
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hw1
    · exact h
  have hle : Subgroup.zpowers w ≤ Subgroup.zpowers z :=
    Subgroup.zpowers_le.2 (hwz ▸ Subgroup.zpow_mem_zpowers z n)
  have heq : Subgroup.zpowers w = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hz3])
  apply hzK
  have hwZ : w ∈ (Subgroup.center ↥K).map K.subtype := ⟨a, haZ, hwa⟩
  have : z ∈ Subgroup.zpowers w := by rw [heq]; exact Subgroup.mem_zpowers z
  exact (Subgroup.zpowers_le.2 hwZ) this

section ImgQ

variable {X : Type*} [Group X] {K J : Subgroup X}

@[expose] def imgQ (K J : Subgroup X) : Subgroup (↥K ⧸ Subgroup.center ↥K) :=
  (J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))

theorem mem_imgQ {s : ↥K ⧸ Subgroup.center ↥K} :
    s ∈ imgQ K J ↔ ∃ k : ↥K, (k : X) ∈ J ∧ (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = s :=
  Iff.rfl

@[expose] def toImgQ (hJK : J ≤ K) : ↥J →* ↥(imgQ K J) where
  toFun j := ⟨QuotientGroup.mk ⟨(j : X), hJK j.2⟩, mem_imgQ.2 ⟨⟨(j : X), hJK j.2⟩, j.2, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toImgQ_injective (hJK : J ≤ K) (h : J ⊓ (Subgroup.center ↥K).map K.subtype = ⊥) :
    Function.Injective (toImgQ hJK) := by
  intro j₁ j₂ hj
  have h1 : (QuotientGroup.mk ⟨(j₁ : X), hJK j₁.2⟩ : ↥K ⧸ Subgroup.center ↥K) =
      QuotientGroup.mk ⟨(j₂ : X), hJK j₂.2⟩ := congrArg Subtype.val hj
  have h2 := QuotientGroup.eq.1 h1
  have h3 : (j₁ : X)⁻¹ * (j₂ : X) ∈ J ⊓ (Subgroup.center ↥K).map K.subtype :=
    ⟨J.mul_mem (J.inv_mem j₁.2) j₂.2, _, h2, rfl⟩
  rw [h, Subgroup.mem_bot] at h3
  exact Subtype.ext (inv_mul_eq_one.1 h3)

theorem toImgQ_surjective (hJK : J ≤ K) : Function.Surjective (toImgQ hJK) := by
  rintro ⟨s, k, hk, rfl⟩
  exact ⟨⟨(k : X), hk⟩, rfl⟩

@[expose] noncomputable def equivImgQ (hJK : J ≤ K)
    (h : J ⊓ (Subgroup.center ↥K).map K.subtype = ⊥) : ↥J ≃* ↥(imgQ K J) :=
  MulEquiv.ofBijective (toImgQ hJK) ⟨toImgQ_injective hJK h, toImgQ_surjective hJK⟩

theorem map_zpowers_equivImgQ (hJK : J ≤ K) (h : J ⊓ (Subgroup.center ↥K).map K.subtype = ⊥)
    {z : X} (hzK : z ∈ K) (hzJ : z ∈ J) :
    ((Subgroup.zpowers z).subgroupOf J).map (equivImgQ hJK h).toMonoidHom =
      (Subgroup.zpowers (QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K)).subgroupOf
        (imgQ K J) := by
  ext s
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hj)
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩)
    rw [← QuotientGroup.mk_zpow]
    show _ = (QuotientGroup.mk (⟨(j : X), hJK j.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)
    congr 1
    exact Subtype.ext (by simpa using hn)
  · intro hs
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hs)
    refine ⟨⟨z ^ n, J.zpow_mem hzJ n⟩, Subgroup.mem_subgroupOf.2
      (Subgroup.zpow_mem_zpowers z n), ?_⟩
    apply Subtype.ext
    show (QuotientGroup.mk ⟨z ^ n, hJK (J.zpow_mem hzJ n)⟩ : ↥K ⧸ Subgroup.center ↥K) = _
    rw [← hn, ← QuotientGroup.mk_zpow]
    congr 1

end ImgQ

theorem isSL3EpsOver_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y') {q : ℕ}
    (h : IsSL3EpsOver Y q) : IsSL3EpsOver Y' q := by
  obtain ⟨hty, h3⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hty with ⟨F, hF, hfin, hc, ⟨e'⟩⟩ | ⟨F, hF, hfin, hc, ⟨e'⟩⟩
    · exact Or.inl ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩
    · exact Or.inr ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩
  · rwa [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]

theorem exists_barEquiv {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B) :
    ∃ f : (A ⧸ GLAPPrimeCore 3 A) ≃* (B ⧸ GLAPPrimeCore 3 B),
      ∀ a : A, f (QuotientGroup.mk a) = QuotientGroup.mk (e a) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (GLAPPrimeCore 3 A).map e.toMonoidHom ≤ GLAPPrimeCore 3 B :=
    CFSG.map_pPrimeCore_le e.toMonoidHom e.surjective
  have h2 : (GLAPPrimeCore 3 B).map e.symm.toMonoidHom ≤ GLAPPrimeCore 3 A :=
    CFSG.map_pPrimeCore_le e.symm.toMonoidHom e.symm.surjective
  have hmap : (GLAPPrimeCore 3 A).map e.toMonoidHom = GLAPPrimeCore 3 B := by
    refine le_antisymm h1 ?_
    intro y hy
    refine ⟨e.symm y, h2 ⟨y, hy, rfl⟩, ?_⟩
    simp
  exact ⟨QuotientGroup.congr (GLAPPrimeCore 3 A) (GLAPPrimeCore 3 B) e hmap,
    fun a => QuotientGroup.congr_mk _ _ e hmap a⟩

theorem transport_bar {A B : Type} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B)
    {ZA : Subgroup A} {ZB : Subgroup B} (hZ : ZA.map e.toMonoidHom = ZB) {q : ℕ}
    (hsl3 : IsSL3EpsOver (A ⧸ GLAPPrimeCore 3 A) q)
    (hzctr : ZA.map (QuotientGroup.mk' (GLAPPrimeCore 3 A)) =
      Subgroup.center (A ⧸ GLAPPrimeCore 3 A))
    (hord : (Nat.card A).factorization 3 = 3) :
    IsSL3EpsOver (B ⧸ GLAPPrimeCore 3 B) q ∧
      ZB.map (QuotientGroup.mk' (GLAPPrimeCore 3 B)) = Subgroup.center (B ⧸ GLAPPrimeCore 3 B) ∧
      (Nat.card B).factorization 3 = 3 := by
  obtain ⟨f, hf⟩ := exists_barEquiv e
  refine ⟨isSL3EpsOver_of_mulEquiv f hsl3, ?_, by rwa [← Nat.card_congr e.toEquiv]⟩
  rw [← Subgroup.map_center_eq f, ← hzctr, Subgroup.map_map, ← hZ, Subgroup.map_map]
  congr 1
  ext a
  exact (hf a).symm

theorem comp_and_centralizes {X : Type} [Group X] [Finite X] {K J Q : Subgroup X} [K.Normal]
    {z : X} (hzK : z ∈ K) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) J)
    (hQ : Q ≤ Subgroup.centralizer
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) : Set X)) :
    GLAPComponent 3
        (Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hzK⟩ : ↥K ⧸ Subgroup.center ↥K)} :
          Set (↥K ⧸ Subgroup.center ↥K))) (imgQ K J) ∧
      ∀ L : Subgroup (↥K ⧸ Subgroup.center ↥K),
        GLAPComponent 3 (Subgroup.centralizer ({(QuotientGroup.mk ⟨z, hzK⟩ :
          ↥K ⧸ Subgroup.center ↥K)} : Set (↥K ⧸ Subgroup.center ↥K))) L →
        ∀ g ∈ Q, ∀ l ∈ L, conjAct K g l = l := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set x : ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk ⟨z, hzK⟩ with hx
  have hzN : z ∈ Subgroup.normalizer (K : Set X) := Subgroup.le_normalizer hzK
  set α : MulAut ↥K := i253α K z hzN with hα
  set π : ↥K →* ↥K ⧸ Subgroup.center ↥K := QuotientGroup.mk' (Subgroup.center ↥K) with hπ
  set β : MulAut (↥K ⧸ Subgroup.center ↥K) := MulAut.conj x with hβ
  have hX : (fixSubgroup α).map K.subtype = K ⊓ Subgroup.centralizer ({z} : Set X) :=
    map_fixSubgroup_i253α K z hzN
  have hc : ∀ y ∈ fixSubgroup α ⊓ K.subtype.ker, ∀ w ∈ fixSubgroup α, w * y = y * w := by
    intro y hy
    have : y = 1 := Subtype.ext (MonoidHom.mem_ker.1 hy.2)
    intro w _
    rw [this, mul_one, one_mul]
  have hker : π.ker ≤ Subgroup.center ↥K := (QuotientGroup.ker_mk' _).le
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hαβ : ∀ k, π (α k) = β (π k) := by
    intro k
    show (QuotientGroup.mk (α k) : ↥K ⧸ Subgroup.center ↥K) = x * QuotientGroup.mk k * x⁻¹
    rw [hx, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
  have hfix : fixSubgroup β = Subgroup.centralizer ({x} : Set (↥K ⧸ Subgroup.center ↥K)) := by
    ext y
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
    show x * y * x⁻¹ = y ↔ y * x = x * y
    constructor
    · intro h
      calc y * x = x * y * x⁻¹ * x := by rw [h]
        _ = x * y := by group
    · intro h
      calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h]
        _ = y := by group
  refine ⟨?_, ?_⟩
  · obtain ⟨J', hJ', hmap⟩ := exists_glaPComponent_map_central hp K.subtype hc (hX ▸ hJ)
    have h1 := glaPComponent_map_fixSubgroup π hker α β hαβ hπs hp hJ'
    have hJ'eq : J.subgroupOf K = J' := by
      rw [← hmap]
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective J'
    rw [hfix] at h1
    have : imgQ K J = J'.map π := by rw [← hJ'eq]; rfl
    rw [this]
    exact h1
  · intro L hL g hg l hl
    obtain ⟨J'', hJ'', hmap⟩ := exists_glaPComponent_map_fixSubgroup π hker α β hαβ hπs hp
      (hfix ▸ hL)
    have h1 := glaPComponent_map_central hp K.subtype hc hJ''
    rw [hX] at h1
    have h2 : J''.map K.subtype ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) :=
      le_sSup h1
    rw [← hmap] at hl
    obtain ⟨j, hj, rfl⟩ := hl
    show (QuotientGroup.mk (MulAut.conjNormal g j) : ↥K ⧸ Subgroup.center ↥K) =
      QuotientGroup.mk j
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hcomm := Subgroup.mem_centralizer_iff.1 (hQ hg) (j : X) (h2 ⟨j, hj, rfl⟩)
    calc g * (j : X) * g⁻¹ = (j : X) * g * g⁻¹ := by rw [← hcomm]
      _ = j := by group

end Transport

open Transport

variable {X : Type} [Group X] [Finite X] {K Q₁ Q J : Subgroup X} {t : X} {q : ℕ}

theorem I1433Cfg.exists_sCfg (c : I1433Cfg K Q₁ Q J t q) :
    ∃ (x : ↥K ⧸ Subgroup.center ↥K) (Q' : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)))
      (J' : Subgroup (↥K ⧸ Subgroup.center ↥K)), I1433SCfg Q' x J' q := by
  haveI := c.setup.normal
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzK, hz3, hZz⟩ := c.exists_gen
  have hzQ : z ∈ ZQ Q := hZz ▸ Subgroup.mem_zpowers z
  have hperf : Group.IsPerfect ↥K := c.setup.quasisimple.1
  have hZ3 : IsPGroup 3 ↥(Subgroup.center ↥K) :=
    CFSG.isPGroup_of_nilpotent_normal (Subgroup.center ↥K) inferInstance inferInstance
      c.primeCore_K
  have hzZ : z ∉ (Subgroup.center ↥K).map K.subtype := by
    intro h
    have h1 : z ∈ ZQ Q ⊓ (Subgroup.center ↥K).map K.subtype := ⟨hzQ, h⟩
    rw [c.zq_inf_center, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hz3
    omega
  have hinj : ∀ g ∈ Q, conjAct K g = 1 → g = 1 := by
    intro g hgQ hg
    have h1 : g ∈ Q ⊓ Subgroup.centralizer (K : Set X) :=
      ⟨hgQ, mem_centralizer_of_conjAct_eq_one hperf hg⟩
    rw [c.faithful, Subgroup.mem_bot] at h1
    exact h1
  have hinjOn : Set.InjOn (conjAct K) Q := injOn_of_ker hinj
  have hcomp := c.comp3 hZz
  have hJK : J ≤ K := hcomp.1.trans inf_le_left
  have hzJ : z ∈ J := c.zle hzQ
  have hzctr : ((Subgroup.zpowers z).subgroupOf J).map
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) = Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    hZz ▸ c.zctr
  have hJinf : J ⊓ (Subgroup.center ↥K).map K.subtype = ⊥ :=
    inf_center_eq_bot hZ3 hz3 hzZ hJK hzctr
  have hQ : Q ≤ Subgroup.centralizer
      (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({z} : Set X)) : Set X) := by
    have := c.setup.centralizes
    have hZz' : (Subgroup.center ↥Q).map Q.subtype = Subgroup.zpowers z := hZz
    rw [hZz', centralizer_zpowers_eq z] at this
    exact this
  obtain ⟨hcomp', hcent⟩ := comp_and_centralizes hzK hcomp hQ
  obtain ⟨hsl3, hzctr', hord⟩ := transport_bar (equivImgQ hJK hJinf)
    (map_zpowers_equivImgQ hJK hJinf hzK hzJ) c.sl3 hzctr c.ord
  refine ⟨QuotientGroup.mk ⟨z, hzK⟩, Q.map (conjAct K), imgQ K J, ?_⟩
  exact
    { derived := map_conjAct_le_derived c.map_le_derived
      card := (card_map_of_injOn hinjOn).trans c.setup.orderQ
      exponent := exponent_map c.setup.exponentQ
      nonabelian := by
        refine exists_noncomm_map hinjOn ?_
        by_contra hcon
        apply c.setup.nonabelianQ
        intro a ha b hb
        by_contra hab
        exact hcon ⟨a, ha, b, hb, hab⟩
      center := center_map_conjAct hzK hZz hinjOn
      order := orderOf_mk_eq_three hzK hz3 hzZ
      comp := hcomp'
      mem := mem_imgQ.2 ⟨⟨z, hzK⟩, hzJ, rfl⟩
      sl3 := hsl3
      zctr := hzctr'
      ord := hord
      centralizes := by
        rintro L hL _ ⟨g, hg, rfl⟩ l hl
        exact hcent L hL g hg l hl }

theorem nonD4LieContraOn_of_simple {F : LieFamily} (h : NonD4LieContraS F) :
    NonD4LieContraOn F := by
  intro X _ _ K Q₁ Q J t q p c hp hp3 idx hidx hchar ⟨e⟩ hnD4
  obtain ⟨x, Q', J', hcfg⟩ := c.exists_sCfg
  have hq := c.setup.quasisimple
  have hKq : CFSG.Open.IsQuasisimple ↥K := ⟨hq.1.commutator_eq_top, hq.2.1⟩
  exact h (↥K ⧸ Subgroup.center ↥K) hq.2.1
    (by
      obtain ⟨a, b, hab⟩ :=
        CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥K hKq
      exact ⟨a, b, hab⟩)
    p hp hp3 idx hidx hchar ⟨e⟩ hnD4 Q' x J' q hcfg

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
