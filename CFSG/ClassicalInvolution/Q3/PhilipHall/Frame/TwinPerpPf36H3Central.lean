module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf36H3Leaves
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf9A01

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

namespace S24B
open CFSG.ClassicalInvolution.Asc77.S24B

section Generic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conj_mem_OCW {W : Subgroup G} {g o : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (ho : o ∈ OCW W) : g * o * g⁻¹ ∈ OCW W := by
  have h := CFSG.ClassicalInvolution.Asc77.Thompson.conjSub_OCW g W
  rw [mem_normalizer_iff_conjSub_eq.mp hg] at h
  rw [← h]
  exact conj_mem_conjSub ho

@[expose] def zhat (hΩ : HypOmegaMod Ω) (W : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (W : Set G) ∧
    ∀ y ∈ MGrp Ω W, x * y * x⁻¹ * y⁻¹ ∈ OCW W}
  one_mem' := ⟨Subgroup.one_mem _, fun y _ => by simp⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, fun y hy => ?_⟩
    have e : x₁ * x₂ * y * (x₁ * x₂)⁻¹ * y⁻¹ =
        x₁ * (x₂ * y * x₂⁻¹ * y⁻¹) * x₁⁻¹ * (x₁ * y * x₁⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (conj_mem_OCW h₁ (k₂ y hy)) (k₁ y hy)
  inv_mem' := by
    rintro x ⟨h, k⟩
    refine ⟨Subgroup.inv_mem _ h, fun y hy => ?_⟩
    have e : x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ = x⁻¹ * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_OCW (Subgroup.inv_mem _ h) (Subgroup.inv_mem _ (k y hy))

theorem mem_zhat_iff {hΩ : HypOmegaMod Ω} {W : Subgroup G} {x : G} :
    x ∈ zhat hΩ W ↔ x ∈ Subgroup.normalizer (W : Set G) ∧
      ∀ y ∈ MGrp Ω W, x * y * x⁻¹ * y⁻¹ ∈ OCW W := Iff.rfl

theorem conj_mem_zhat (hΩ : HypOmegaMod Ω) {W : Subgroup G} {s x : G}
    (hs : s ∈ Subgroup.normalizer (W : Set G)) (hx : x ∈ zhat hΩ W) :
    s * x * s⁻¹ ∈ zhat hΩ W := by
  obtain ⟨h, k⟩ := hx
  rw [mem_zhat_iff]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h) (Subgroup.inv_mem _ hs), fun y hy => ?_⟩
  have hy' : s⁻¹ * y * s⁻¹⁻¹ ∈ MGrp Ω W :=
    Thompson.conj_mem_MGrp hΩ (Subgroup.inv_mem _ hs) hy
  have e : s * x * s⁻¹ * y * (s * x * s⁻¹)⁻¹ * y⁻¹ =
      s * (x * (s⁻¹ * y * s⁻¹⁻¹) * x⁻¹ * (s⁻¹ * y * s⁻¹⁻¹)⁻¹) * s⁻¹ := by group
  rw [e]
  exact conj_mem_OCW hs (k _ hy')

@[expose] def cmodO (W : Subgroup G) (a : G) : Subgroup G where
  carrier := {y | y ∈ Subgroup.normalizer (W : Set G) ∧ a * y * a⁻¹ * y⁻¹ ∈ OCW W}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro y₁ y₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
    refine ⟨Subgroup.mul_mem _ h₁ h₂, ?_⟩
    have e : a * (y₁ * y₂) * a⁻¹ * (y₁ * y₂)⁻¹ =
        (a * y₁ * a⁻¹ * y₁⁻¹) * (y₁ * (a * y₂ * a⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ k₁ (conj_mem_OCW h₁ k₂)
  inv_mem' := by
    rintro y ⟨h, k⟩
    refine ⟨Subgroup.inv_mem _ h, ?_⟩
    have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_OCW (Subgroup.inv_mem _ h) (Subgroup.inv_mem _ k)

theorem le_cmodO {W X : Subgroup G} {a : G} (hXN : X ≤ Subgroup.normalizer (W : Set G))
    (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) : X ≤ cmodO W a := by
  intro y hy
  refine ⟨hXN hy, ?_⟩
  have h : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hXa hy)
  have e : a * y * a⁻¹ * y⁻¹ = 1 := by
    rw [← h]; group
  rw [e]
  exact Subgroup.one_mem _

theorem OCW_le_cmodO {W : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (W : Set G)) :
    OCW W ≤ cmodO W a := by
  intro o ho
  refine ⟨CFSG.ClassicalInvolution.Asc77.Thompson.OCW_le_normalizer W ho, ?_⟩
  exact Subgroup.mul_mem _ (conj_mem_OCW ha ho) (Subgroup.inv_mem _ ho)

theorem exists_sylow_between (S₀ : Sylow 2 G) {N Q : Subgroup G} (hS₀ : (S₀ : Subgroup G) ≤ N)
    (hQ : IsPGroup 2 Q) (hQN : Q ≤ N) :
    ∃ S₁ : Sylow 2 G, Q ≤ (S₁ : Subgroup G) ∧ (S₁ : Subgroup G) ≤ N := by
  obtain ⟨V, hV, hQV⟩ := IsSylow2In.exists_ge hQ hQN
  have hS₀N := T8.isSylow2In_of_sylow_le S₀ hS₀
  have hc : Nat.card V = 2 ^ (Nat.card G).factorization 2 := by
    rw [← hS₀N.natCard_eq hV]
    exact Sylow.card_eq_multiplicity S₀
  exact ⟨Sylow.ofCard V hc, hQV, hV.1⟩

theorem exists_involution_pow {x : G} (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hx1 : x ≠ 1) :
    ∃ n : ℕ, x ^ n * x ^ n = 1 ∧ x ^ n ≠ 1 := by
  obtain ⟨k, hk⟩ := hx2.exists_card_eq
  rw [Nat.card_zpowers] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.mp (by simpa using hk))
  have h2 : 2 ∣ orderOf x := hk ▸ dvd_pow_self 2 hk0
  have ho := orderOf_pow_orderOf_div (orderOf_pos x).ne' h2
  refine ⟨orderOf x / 2, ?_, ?_⟩
  · have := pow_orderOf_eq_one (x ^ (orderOf x / 2))
    rwa [ho, pow_two] at this
  · intro h
    rw [h, orderOf_one] at ho
    omega

end Generic


namespace HCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : Asc77.S24B.HCtx Ω K K' W S R R' z u)

include H in
theorem hΩ : HypOmegaMod Ω := H.C.hs.stand.hyp

theorem a_mem_centralizer_W : H.a ∈ Subgroup.centralizer (W : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hw => H.comm_W hw

theorem W_le_centralizer_a : W ≤ Subgroup.centralizer ({H.a} : Set G) := fun _ hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (H.comm_W hw)

theorem a_mem_normalizer : H.a ∈ Subgroup.normalizer (W : Set G) :=
  Subgroup.centralizer_le_normalizer _ H.a_mem_centralizer_W

include H in
theorem R_mem_DSet : R ∈ DSet Ω W := by
  rw [← H.C.hR]
  exact H.C.D.F.ρ.hR

include H in
theorem R'_mem_DSet : R' ∈ DSet Ω W := by
  rw [← H.C.hR']
  exact H.C.D.F.ρ'.hR

include H in
theorem R_le_normalizer : R ≤ Subgroup.normalizer (W : Set G) := H.R_mem_DSet.2

include H in
theorem R'_le_normalizer : R' ≤ Subgroup.normalizer (W : Set G) := H.R'_mem_DSet.2

theorem T_mem_DSet : H.T₃ ∈ DSet Ω W :=
  ⟨mem_RSet_of_isSylow2In H.C.D.F.ρ₃.hK H.hT, H.hTN⟩

theorem MGrp_le_cmodO : MGrp Ω W ≤ cmodO W H.a := by
  have hΩ := H.hΩ
  have hRa : R ≤ cmodO W H.a := le_cmodO H.R_le_normalizer H.haR
  have hR'a : R' ≤ cmodO W H.a := le_cmodO H.R'_le_normalizer H.haR'
  have hTa : H.T₃ ≤ cmodO W H.a := le_cmodO H.hTN H.hTa
  have hWa : W ≤ cmodO W H.a := le_cmodO Subgroup.le_normalizer H.W_le_centralizer_a
  have hOa : OCW W ≤ cmodO W H.a := OCW_le_cmodO H.a_mem_normalizer
  have hkey := H.C.D.c.hkey
  have hr : H.C.D.F.ρ.r ∈ cmodO W H.a := hRa H.C.r_mem_R
  have ht : H.C.D.F.ρ'.r ∈ cmodO W H.a := hR'a H.C.t_mem_R'
  have hs : H.C.D.F.ρ₃.r ∈ cmodO W H.a := by
    have := hkey H.T₃ H.T_mem_DSet H.C.D.F.ρ₃.R H.C.D.F.ρ₃.hR H.C.D.F.ρ₃.K H.C.D.F.ρ₃.hK
      H.hT.1 H.C.D.F.ρ₃.hRK.1
    exact sup_le (sup_le hTa hWa) hOa (this H.C.D.F.ρ₃.hr)
  unfold MGrp
  refine iSup₂_le fun R₂ hR₂ => ?_
  obtain ⟨J₂, hJ₂, hR₂J₂⟩ := exists_isSylow2In_of_mem_RSet hR₂.1
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hΩ H.C.hd.hW hJ₂ hR₂J₂ hR₂
  obtain ⟨h, hh, hK⟩ := exists_conj_of_frame H.C.D.c H.C.D.hφ H.C.D.F H.C.D.hab H.C.D.hcomm
    H.C.D.hac hr ht hs σ
  have hRD := H.R_mem_DSet
  have hhR : conjSub h R ∈ DSet Ω W := by
    refine ⟨RSet.conj hΩ.conjInvariant hRD.1 h, ?_⟩
    intro x hx
    rw [mem_conjSub_iff] at hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh.1 (hRD.2 hx)) (Subgroup.inv_mem _ hh.1)
  have hhRa : conjSub h R ≤ cmodO W H.a := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have e : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hRa hx)) (Subgroup.inv_mem _ hh)
  have hhRJ : conjSub h R ≤ J₂ := by
    rw [← hσK, ← hK]
    refine conjSub_mono ?_
    rw [H.C.hK]
    exact H.C.hd.hR.2.1
  exact (hkey (conjSub h R) hhR R₂ hR₂ J₂ hJ₂ hhRJ hR₂J₂.1).trans (sup_le (sup_le hhRa hWa) hOa)

theorem a_mem_zhat : H.a ∈ zhat H.hΩ W := by
  refine ⟨H.a_mem_normalizer, fun y hy => (H.MGrp_le_cmodO hy).2⟩

theorem exists_S₁ : ∃ S₁ : Sylow 2 G, H.a ∈ (S₁ : Subgroup G) ∧ W ≤ (S₁ : Subgroup G) ∧
    R ≤ (S₁ : Subgroup G) ∧ R' ≤ (S₁ : Subgroup G) ∧
    (S₁ : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
  have hP : IsPGroup 2 ↥(R ⊔ R' ⊔ W) :=
    S.isPGroup'.to_le (sup_le (sup_le H.C.hd.hR.2.2 H.C.hd.hR'.2.2) H.C.hd.hWS)
  have hPa : R ⊔ R' ⊔ W ≤ Subgroup.centralizer ({H.a} : Set G) :=
    sup_le (sup_le H.haR H.haR') H.W_le_centralizer_a
  have haP : H.a ∈ Subgroup.centralizer ((R ⊔ R' ⊔ W : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hPa hx)
  have hza : Subgroup.zpowers H.a ≤ Subgroup.normalizer ((R ⊔ R' ⊔ W : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ haP)
  have hQ : IsPGroup 2 ↥(Subgroup.zpowers H.a ⊔ (R ⊔ R' ⊔ W)) :=
    IsPGroup.to_sup_of_normal_right' (ExactLayer.isPGroup_zpowers_of_sq_eq_one H.ha2) hP hza
  have hQN : Subgroup.zpowers H.a ⊔ (R ⊔ R' ⊔ W) ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr H.a_mem_normalizer)
      (sup_le (sup_le H.R_le_normalizer H.R'_le_normalizer) Subgroup.le_normalizer)
  obtain ⟨S₁, hQS₁, hS₁N⟩ := exists_sylow_between S H.C.le_normalizer_W hQ hQN
  refine ⟨S₁, hQS₁ (le_sup_left (a := Subgroup.zpowers H.a) (Subgroup.mem_zpowers H.a)),
    fun x hx => hQS₁ (le_sup_right (a := Subgroup.zpowers H.a) (le_sup_right (a := R ⊔ R') hx)),
    fun x hx => hQS₁ (le_sup_right (a := Subgroup.zpowers H.a)
      (le_sup_left (b := W) (le_sup_left (b := R') hx))),
    fun x hx => hQS₁ (le_sup_right (a := Subgroup.zpowers H.a)
      (le_sup_left (b := W) (le_sup_right (a := R) hx))), hS₁N⟩

theorem exists_central (S₁ : Sylow 2 G) (haS₁ : H.a ∈ (S₁ : Subgroup G))
    (hS₁ : (S₁ : Subgroup G) ≤ Subgroup.normalizer (W : Set G)) :
    ∃ a₀ ∈ zhat H.hΩ W, a₀ ∈ (S₁ : Subgroup G) ∧
      a₀ ∈ Subgroup.centralizer ((S₁ : Subgroup G) : Set G) ∧ a₀ * a₀ = 1 ∧ a₀ ≠ 1 := by
  let Z₁ : Subgroup ↥(S₁ : Subgroup G) := (zhat H.hΩ W).subgroupOf (S₁ : Subgroup G)
  have hZn : Z₁.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_zhat H.hΩ (hS₁ g.2) hn⟩
  haveI := S₁.isPGroup'.isNilpotent
  have hne : Z₁ ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨⟨H.a, haS₁⟩, (Subgroup.mem_subgroupOf).mpr H.a_mem_zhat⟩, ?_⟩
    intro h
    apply H.ha1
    have := congrArg (fun y : ↥Z₁ => ((y : ↥(S₁ : Subgroup G)) : G)) h
    simpa using this
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  set y : G := ((x : ↥(S₁ : Subgroup G)) : G) with hy
  have hyZ : y ∈ zhat H.hΩ W := (Subgroup.mem_subgroupOf).mp (Subgroup.mem_inf.mp x.2).1
  have hyc : ∀ h ∈ (S₁ : Subgroup G), h * y = y * h := fun h hh =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp x.2).2 ⟨h, hh⟩)
  have hyS : y ∈ (S₁ : Subgroup G) := (x : ↥(S₁ : Subgroup G)).2
  have hy1 : y ≠ 1 := by
    intro h
    apply hx1
    exact Subtype.ext (Subtype.ext h)
  obtain ⟨n, hn2, hn1⟩ := exists_involution_pow
    (S₁.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)) hy1
  refine ⟨y ^ n, Subgroup.pow_mem _ hyZ n, Subgroup.pow_mem _ hyS n,
    Subgroup.mem_centralizer_iff.mpr fun h hh => ((Commute.pow_right (hyc h hh) n)).eq, hn2, hn1⟩

theorem exists_T (a₀ : G) (ha₀Z : a₀ ∈ zhat H.hΩ W) (ha₀2 : a₀ * a₀ = 1)
    (ha₀W : W ≤ Subgroup.centralizer ({a₀} : Set G)) :
    ∃ T : Subgroup G, IsSylow2In T H.C.D.F.ρ₃.K ∧ T ≤ Subgroup.normalizer (W : Set G) ∧
      T ≤ Subgroup.centralizer ({a₀} : Set G) := by
  have hΩ := H.hΩ
  have hJ : H.C.D.F.ρ₃.K ∈ Ω := H.C.D.F.ρ₃.hK
  have ha₀N : a₀ ∈ Subgroup.normalizer (W : Set G) := ha₀Z.1
  have hx₃ : H.C.D.x₃ * a₀ = a₀ * H.C.D.x₃ :=
    Subgroup.mem_centralizer_singleton_iff.mp (ha₀W H.C.D.x₃_mem)
  have haJ : conjSub a₀ H.C.D.F.ρ₃.K = H.C.D.F.ρ₃.K := by
    have h4 : 4 ≤ Nat.card (Subgroup.zpowers H.C.D.x₃) := by
      rw [Nat.card_zpowers, H.C.orderOf_x₃]
    have h2 : IsPGroup 2 (Subgroup.zpowers H.C.D.x₃) :=
      S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (H.C.hd.hWS H.C.D.x₃_mem))
    refine CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.eq_of_le_of_le hΩ
      (hΩ.conjInvariant a₀ _ hJ) hJ h2 h4 ?_ (Subgroup.zpowers_le.mpr H.C.x₃_mem_J)
    rw [Subgroup.zpowers_le, mem_conjSub_iff]
    have e : a₀⁻¹ * H.C.D.x₃ * a₀ = H.C.D.x₃ := by
      rw [mul_assoc, hx₃, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact H.C.x₃_mem_J
  have ha₀NJ : a₀ ∈ Subgroup.normalizer (H.C.D.F.ρ₃.K : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr haJ
  set X : Subgroup G := H.C.D.F.ρ₃.K ⊓ Subgroup.normalizer (W : Set G) with hXdef
  have ha₀X : a₀ ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    rw [hXdef, Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr (Subgroup.mem_normalizer_iff.mp ha₀NJ g)
      (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ha₀N) g)
  have hYN : X ⊔ Subgroup.zpowers a₀ ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr ha₀X)
  obtain ⟨V, hV, haV⟩ := IsSylow2In.exists_ge (ExactLayer.isPGroup_zpowers_of_sq_eq_one ha₀2)
    (le_sup_right : Subgroup.zpowers a₀ ≤ X ⊔ Subgroup.zpowers a₀)
  have ha₀V : a₀ ∈ V := haV (Subgroup.mem_zpowers a₀)
  have hQ : IsSylow2In (V ⊓ X) X := isSylow2In_inf_of_le_normalizer hV le_sup_left hYN
  have hTX : IsSylow2In H.T₃ X := ⟨le_inf H.hT.1 H.hTN, H.hT.2.1,
    fun V' hV'X h2 hle => H.hT.2.2 V' (hV'X.trans inf_le_left) h2 hle⟩
  have hQJ : IsSylow2In (V ⊓ X) H.C.D.F.ρ₃.K :=
    H.hT.of_natCard_le hQ.2.1 (hQ.1.trans inf_le_left) (hTX.natCard_eq hQ).le
  have hQN : V ⊓ X ≤ Subgroup.normalizer (W : Set G) := hQ.1.trans inf_le_right
  have hQD : V ⊓ X ∈ DSet Ω W := ⟨mem_RSet_of_isSylow2In hJ hQJ, hQN⟩
  refine ⟨V ⊓ X, hQJ, hQN, fun q hq => ?_⟩
  have hqM : q ∈ MGrp Ω W := Thompson.le_MGrp_of_mem_D hQD hq
  have hcO : a₀ * q * a₀⁻¹ * q⁻¹ ∈ OCW W := ha₀Z.2 q hqM
  have hcQ : a₀ * q * a₀⁻¹ * q⁻¹ ∈ V ⊓ X := by
    refine Subgroup.mul_mem _ ⟨?_, ?_⟩ (Subgroup.inv_mem _ hq)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₀V (Subgroup.mem_inf.mp hq).1)
        (Subgroup.inv_mem _ ha₀V)
    · exact (Subgroup.mem_normalizer_iff.mp ha₀X q).mp (Subgroup.mem_inf.mp hq).2
  have hc1 : a₀ * q * a₀⁻¹ * q⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard (Subgroup.centralizer (W : Set G)))
      hcO (hQ.2.1.to_le (Subgroup.zpowers_le.mpr hcQ))
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc q * a₀ = (a₀ * q * a₀⁻¹ * q⁻¹)⁻¹ * (a₀ * q) := by group
    _ = a₀ * q := by rw [hc1, inv_one, one_mul]

end HCtx

theorem centralizeH_proved : CentralizeH := by
  intro G _ _ _ Ω K K' W S R R' z u _ H
  obtain ⟨S₁, haS₁, hWS₁, hRS₁, hR'S₁, hS₁N⟩ := H.exists_S₁
  obtain ⟨a₀, ha₀Z, ha₀S₁, ha₀c, ha₀2, ha₀1⟩ := H.exists_central S₁ haS₁ hS₁N
  have hc : ∀ X : Subgroup G, X ≤ (S₁ : Subgroup G) →
      X ≤ Subgroup.centralizer ({a₀} : Set G) := fun X hX x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp ha₀c x (hX hx))
  obtain ⟨T, hT, hTN, hTa⟩ := H.exists_T a₀ ha₀Z ha₀2 (hc W hWS₁)
  let H' : HCtx Ω K K' W S R R' z u :=
    ⟨H.C, a₀, T, ha₀2, ha₀1, hc R hRS₁, hc R' hR'S₁, hT, hTN, hTa⟩
  exact ⟨H', S₁, hS₁N, hRS₁, hR'S₁, ha₀c, fun y hy => ha₀Z.2 y hy⟩

end S24B
end Asc77
end CFSG.ClassicalInvolution.Q8P
