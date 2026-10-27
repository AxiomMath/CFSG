module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21A

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Generic

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_of_forall {H : Subgroup G} {a : G} (h : ∀ x ∈ H, x = 1 ∨ x = a) :
    Nat.card H ≤ 2 := by
  have hsub : (H : Set G) ⊆ {1, a} := fun x hx => by
    rcases h x hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have h1 : Nat.card H = Set.ncard (H : Set G) := Nat.card_coe_set_eq (H : Set G)
  rw [h1]
  calc Set.ncard (H : Set G) ≤ Set.ncard ({1, a} : Set G) :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      simp

theorem exists_ne_of_card_four {E : Subgroup G} (hE : Nat.card E = 4) (a : G) :
    ∃ e ∈ E, e ≠ 1 ∧ e ≠ a := by
  by_contra hno
  push Not at hno
  have := card_le_two_of_forall (H := E) (a := a) fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hno x hx h1)
  omega

theorem eight_le_card_of_nonabelian {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hQ : ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a) : 8 ≤ Nat.card Q := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push Not at hk3
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  have h4 : Nat.card Q ≤ 4 := by
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  obtain ⟨a, ha, b, hb, hab⟩ := hQ
  exact hab (DS.commutative_of_card_le_four hQ2 h4 a ha b hb)

theorem four_le_card_of_ne_two {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q) (hQ : Q ≠ ⊥)
    (h2 : Nat.card Q ≠ 2) : 4 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have h1 : Nat.card Q ≠ 1 := fun h1 => hQ (Subgroup.card_eq_one.mp h1)
  by_contra hlt
  push Not at hlt
  have hk2 : k < 2 := by
    by_contra hk3
    push Not at hk3
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  interval_cases k <;> simp_all

omit [Finite G] in
theorem commutator_le_self (X : Subgroup G) : ⁅X, X⁆ ≤ X := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

end Generic

section SBarGeneric

variable {G : Type} [Group G] [Finite G] {S A : Subgroup G} {P : Type} [Group P] [Finite P]
  {π : G → P} {R : Subgroup P}

omit [Finite G] in
theorem SBar.card_inf_mul_card_img (h : SBar S A π R) {X : Subgroup G} (hXS : X ≤ S) :
    Nat.card ↥(X ⊓ A) * Nat.card ↥(h.img X) = Nat.card ↥X := by
  let f : ↥X →* P := h.hom.comp (Subgroup.inclusion hXS)
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : Nat.card f.ker = Nat.card ↥(X ⊓ A) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : f.ker => (⟨((x.1 : ↥X) : G), (x.1).2, ?_⟩ : ↥(X ⊓ A))) ⟨?_, ?_⟩)
    · have hx : f x.1 = 1 := x.2
      have hx' : π ((x.1 : ↥X) : G) = 1 := hx
      exact (h.ker _ (hXS (x.1).2)).mp hx'
    · intro x y hxy
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨y, hyX, hyA⟩
      refine ⟨⟨⟨y, hyX⟩, ?_⟩, rfl⟩
      show π y = 1
      exact (h.ker y (hXS hyX)).mpr hyA
  have hrange : f.range = h.img X := by
    ext p
    rw [MonoidHom.mem_range, h.mem_img]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, hXS x.2, rfl⟩
    · rintro ⟨x, hxX, hxS, rfl⟩
      exact ⟨⟨x, hxX⟩, rfl⟩
  rw [hker, hrange] at h1
  exact h1

omit [Finite G] in
theorem SBar.img_mono (h : SBar S A π R) {X Y : Subgroup G} (hXY : X ≤ Y) :
    h.img X ≤ h.img Y := by
  intro p hp
  obtain ⟨x, hxX, hxS, rfl⟩ := h.mem_img.mp hp
  exact h.pi_mem_img (hXY hxX) hxS

omit [Finite G] in
theorem SBar.pi_mem_of_centralizes_nonabelian (h : SBar S A π R) {B : Subgroup G} (hBS : B ≤ S)
    (hBA : B ⊓ A = ⊥) (hB : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) {c : G} (hcS : c ∈ S)
    (hc : ∀ b ∈ B, b * c = c * b) : π c = 1 ∨ π c = h.ds.z := by
  have hBb := h.nonabelian_img hBS hBA hB
  have hcomm : ∀ p ∈ h.img B, p * π c = π c * p := by
    intro p hp
    obtain ⟨x, hxB, hxS, rfl⟩ := h.mem_img.mp hp
    rw [← h.mul x hxS c hcS, ← h.mul c hcS x hxS, hc x hxB]
  exact h.ds.central_in_nonabelian hBb hcomm

omit [Finite G] in
theorem SBar.not_le_Rt_of_nonabelian (h : SBar S A π R) {B : Subgroup G} (hBS : B ≤ S)
    (hBA : B ⊓ A = ⊥) (hB : ∃ a ∈ B, ∃ b ∈ B, a * b ≠ b * a) : ¬ B ≤ h.Rt := by
  intro hle
  obtain ⟨a, ha, b, hb, hab⟩ := hB
  apply hab
  have hπ : π (a * b) = π (b * a) := by
    rw [h.mul a (hBS ha) b (hBS hb), h.mul b (hBS hb) a (hBS ha)]
    exact h.ds.comm ((h.mem_Rt.mp (hle ha)).2) ((h.mem_Rt.mp (hle hb)).2)
  have h1 := (h.pi_eq_iff (S.mul_mem (hBS ha) (hBS hb)) (S.mul_mem (hBS hb) (hBS ha))).mp hπ
  have h2 : (a * b)⁻¹ * (b * a) ∈ B ⊓ A :=
    ⟨B.mul_mem (B.inv_mem (B.mul_mem ha hb)) (B.mul_mem hb ha), h1⟩
  rw [hBA, Subgroup.mem_bot] at h2
  exact inv_mul_eq_one.mp h2

end SBarGeneric

section Notation

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

@[expose] def Notation25.SCx (N : Notation25 hs) : Subgroup G := CFSG.conjugate N.SC N.x

@[expose] def Notation25.S0 (N : Notation25 hs) : Subgroup G :=
  N.S ⊓ Subgroup.centralizer (N.SC : Set G)

theorem Notation25.mem_SCx {N : Notation25 hs} {b : G} : b ∈ N.SCx ↔ N.x * b * N.x⁻¹ ∈ N.SC :=
  BenderBranch.mem_conjugate_iff

theorem Notation25.mem_S0 {N : Notation25 hs} {g : G} :
    g ∈ N.S0 ↔ g ∈ N.S ∧ ∀ a ∈ N.SC, a * g = g * a := by
  unfold Notation25.S0
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem Notation25.S0_le_S (N : Notation25 hs) : N.S0 ≤ N.S := inf_le_left

theorem Notation25.card_SCx (N : Notation25 hs) : Nat.card ↥N.SCx = Nat.card ↥N.SC :=
  BenderBranch.card_conjugate _ _

theorem Notation25.conj_mem_SCx {N : Notation25 hs} {a : G} (ha : a ∈ N.SC) :
    N.x⁻¹ * a * N.x ∈ N.SCx := by
  rw [Notation25.mem_SCx]
  have : N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ = a := by group
  rw [this]
  exact ha

variable {N : Notation25 hs} {t zK : G}

theorem Lv2520.SCx_le_S (h : Lv2520 N t zK) : N.SCx ≤ N.S := h.concl255.2.1

theorem Lv2520.SCx_inf_SC (h : Lv2520 N t zK) : N.SCx ⊓ N.SC = ⊥ := by
  rw [inf_comm]
  exact h.concl255.1

theorem Lv2520.SC_commutes_SCx (h : Lv2520 N t zK) : ∀ a ∈ N.SC, ∀ b ∈ N.SCx, a * b = b * a :=
  h.concl255.2.2

theorem Lv2520.SK_le_S0 (h : Lv2520 N t zK) : N.SK ≤ N.S0 := fun q hq =>
  Notation25.mem_S0.mpr ⟨hq.1, fun _ ha => h.SC_commutes ha q hq.2⟩

theorem Lv2520.SCx_le_S0 (h : Lv2520 N t zK) : N.SCx ≤ N.S0 := fun b hb =>
  Notation25.mem_S0.mpr ⟨h.SCx_le_S hb, fun a ha => h.SC_commutes_SCx a ha b hb⟩

theorem Lv2520.S_inf_centralizer_SCx (_h : Lv2520 N t zK) :
    N.S ⊓ Subgroup.centralizer (N.SCx : Set G) = CFSG.conjugate N.S0 N.x := by
  have hSx : CFSG.conjugate N.S N.x = N.S :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr N.x_mem.2
  unfold Notation25.S0 Notation25.SCx
  rw [BenderBranch.conjugate_inf, BenderBranch.conjugate_centralizer, hSx]

theorem Lv2520.SCx_nonabelian (_h : Lv2520 N t zK) (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) :
    ∃ a ∈ N.SCx, ∃ b ∈ N.SCx, a * b ≠ b * a := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  refine ⟨N.x⁻¹ * a * N.x, Notation25.conj_mem_SCx ha, N.x⁻¹ * b * N.x,
    Notation25.conj_mem_SCx hb, fun hc => hab ?_⟩
  have h1 : N.x⁻¹ * (a * b) * N.x = N.x⁻¹ * (b * a) * N.x := by
    calc N.x⁻¹ * (a * b) * N.x = (N.x⁻¹ * a * N.x) * (N.x⁻¹ * b * N.x) := by group
      _ = (N.x⁻¹ * b * N.x) * (N.x⁻¹ * a * N.x) := hc
      _ = N.x⁻¹ * (b * a) * N.x := by group
  exact mul_left_cancel (mul_right_cancel h1)

end Notation

section CaseC

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G} {R : Subgroup ↥(autOn N.S N.K)}

theorem Lv2520.tx_commutes_SCx (h : Lv2520 N t zK) :
    ∀ b ∈ N.SCx, b * (N.x⁻¹ * t * N.x) = (N.x⁻¹ * t * N.x) * b := by
  intro b hb
  have hb' : N.x * b * N.x⁻¹ ∈ N.SC := Notation25.mem_SCx.mp hb
  have hct : (N.x * b * N.x⁻¹) * t = t * (N.x * b * N.x⁻¹) :=
    Subgroup.mem_centralizer_iff.mp h.facts2511.t_mem_center.2 _ (N.SC_le_S hb')
  calc b * (N.x⁻¹ * t * N.x) = N.x⁻¹ * ((N.x * b * N.x⁻¹) * t) * N.x := by group
    _ = N.x⁻¹ * (t * (N.x * b * N.x⁻¹)) * N.x := by rw [hct]
    _ = (N.x⁻¹ * t * N.x) * b := by group

theorem Lv2520.caseC_center_SC (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) {a : G} (ha : a ∈ N.SC)
    (hac : ∀ a' ∈ N.SC, a * a' = a' * a) : a = 1 ∨ a = t := by
  by_cases ha1 : a = 1
  · exact Or.inl ha1
  right
  have hSB := h.sBar hR
  have hf := h.facts2511
  have key : N.x⁻¹ * a * N.x = N.x⁻¹ * t * N.x := by
    refine hSB.central_unique h.SCx_le_S h.SCx_inf_SC (h.SCx_nonabelian hnab)
      (Notation25.conj_mem_SCx ha) (Notation25.conj_mem_SCx hf.t_mem) ?_ h.tx_commutes_SCx ?_ ?_
    · intro b hb
      have hb' : N.x * b * N.x⁻¹ ∈ N.SC := Notation25.mem_SCx.mp hb
      have h1 := hac _ hb'
      calc b * (N.x⁻¹ * a * N.x) = N.x⁻¹ * ((N.x * b * N.x⁻¹) * a) * N.x := by group
        _ = N.x⁻¹ * (a * (N.x * b * N.x⁻¹)) * N.x := by rw [← h1]
        _ = (N.x⁻¹ * a * N.x) * b := by group
    · intro h1
      apply ha1
      calc a = N.x * (N.x⁻¹ * a * N.x) * N.x⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      apply hf.t_ne_one
      calc t = N.x * (N.x⁻¹ * t * N.x) * N.x⁻¹ := by group
        _ = 1 := by rw [h1]; group
  exact mul_left_cancel (mul_right_cancel key)

theorem Lv2520.caseC_card_S0_inf_SC_le (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : Nat.card ↥(N.S0 ⊓ N.SC) ≤ 2 := by
  refine card_le_two_of_forall (a := t) fun a ha => ?_
  refine h.caseC_center_SC hR hnab ha.2 fun a' ha' => ?_
  exact ((Notation25.mem_S0.mp ha.1).2 a' ha').symm

theorem Lv2520.caseC_card_P_le (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC)) :
    Nat.card ↥(autOn N.S N.K) ≤ 2 * Nat.card ↥N.SK := by
  have hSB := h.sBar hR
  have h1 := hSB.card_S N.SC_le_S
  have hpos : 0 < Nat.card ↥N.SC := Nat.card_pos
  have h2 : Nat.card ↥N.SC * Nat.card ↥(autOn N.S N.K) ≤
      Nat.card ↥N.SC * (2 * Nat.card ↥N.SK) := by
    calc Nat.card ↥N.SC * Nat.card ↥(autOn N.S N.K) = Nat.card ↥N.S := h1
      _ ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC) := hidx
      _ = Nat.card ↥N.SC * (2 * Nat.card ↥N.SK) := by ring
  exact Nat.le_of_mul_le_mul_left h2 hpos

theorem Lv2520.caseC_commutator_S0_le (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : ⁅N.S0, N.S0⁆ ≤ N.SK := by
  have hSB := h.sBar hR
  have hcard := hSB.card_inf_mul_card_img N.S0_le_S
  have h2 := h.caseC_card_S0_inf_SC_le hR hnab
  have hP := h.caseC_card_P_le hR hidx
  have himg : Nat.card ↥(hSB.img N.S0) ≤ Nat.card ↥(autOn N.S N.K) :=
    Subgroup.card_le_card_group _
  refine DS.commutator_le_of_card_le h.SK_le_S0
    (fun s hs' q hq => h.SK_normal_in_S (N.S0_le_S hs') hq)
    (N.tuple.sylow.isPGroup.to_le N.S0_le_S) ?_
  calc Nat.card ↥N.S0 = Nat.card ↥(N.S0 ⊓ N.SC) * Nat.card ↥(hSB.img N.S0) := hcard.symm
    _ ≤ 2 * Nat.card ↥(autOn N.S N.K) := Nat.mul_le_mul h2 himg
    _ ≤ 2 * (2 * Nat.card ↥N.SK) := Nat.mul_le_mul_left 2 hP
    _ = 4 * Nat.card ↥N.SK := by ring

theorem Lv2520.caseC_zK_mem_commutator (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : zK ∈ ⁅N.SCx, N.SCx⁆ := by
  have hSB := h.sBar hR
  have hnabB := h.SCx_nonabelian hnab
  have hB2 : IsPGroup 2 ↥N.SCx := N.tuple.sylow.isPGroup.to_le h.SCx_le_S
  have hB8 := eight_le_card_of_nonabelian hB2 hnabB
  obtain ⟨ρ, hρB, hρR, hρ⟩ := hSB.exists_sq_ne_one h.SCx_le_S h.SCx_inf_SC hB8
  obtain ⟨w, hwc, hwz⟩ := hSB.exists_mem_commutator h.SCx_le_S h.SCx_inf_SC
    (hSB.not_le_Rt_of_nonabelian h.SCx_le_S h.SCx_inf_SC hnabB) hρB hρR hρ
  have hwSK : w ∈ N.SK := h.caseC_commutator_S0_le hR hidx hnab
    (Subgroup.commutator_mono h.SCx_le_S0 h.SCx_le_S0 hwc)
  have hwS : w ∈ N.S := N.SK_le_S hwSK
  have hzKS : zK ∈ N.S := h.facts2511.zK_mem_center.1
  have hmem : w⁻¹ * zK ∈ N.SC := (hSB.pi_eq_iff hwS hzKS).mp (hwz.trans (h.pi_zK hR).symm)
  have hK : w⁻¹ * zK ∈ N.K :=
    N.K.mul_mem (N.K.inv_mem (N.SK_le_K hwSK)) (h.hK0 ▸ h.facts2511.zK_mem)
  have hw : w = zK := inv_mul_eq_one.mp (h.K_inf_SC_eq_bot_mem hK hmem)
  rw [← hw]
  exact hwc

theorem Lv2520.caseC_tx (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : N.x⁻¹ * t * N.x = zK := by
  have hSB := h.sBar hR
  have hf := h.facts2511
  have hzKB : zK ∈ N.SCx := commutator_le_self _ (h.caseC_zK_mem_commutator hR hidx hnab)
  refine hSB.central_unique h.SCx_le_S h.SCx_inf_SC (h.SCx_nonabelian hnab)
    (Notation25.conj_mem_SCx hf.t_mem) hzKB h.tx_commutes_SCx ?_ ?_ h.zK_ne_one
  · intro b hb
    exact Subgroup.mem_centralizer_iff.mp hf.zK_mem_center.2 b (h.SCx_le_S hb)
  · intro h1
    apply hf.t_ne_one
    calc t = N.x * (N.x⁻¹ * t * N.x) * N.x⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem Lv2520.caseC_z (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : N.z = t * zK := by
  have h1 := h.concl2513.1.2 N.x N.x_mem N.x_not_mem
  rw [h.caseC_tx hR hidx hnab] at h1
  have ht2 : t * t = 1 := h.facts2511.t_mul_t
  calc N.z = (t * t) * N.z := by rw [ht2, one_mul]
    _ = t * (t * N.z) := by group
    _ = t * zK := by rw [← h1]

theorem Lv2520.caseC_not_conj (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : ∀ g : G, g⁻¹ * t * g ≠ t * zK := by
  intro g hg
  rw [← h.caseC_z hR hidx hnab] at hg
  apply h.facts2511.not_conj g⁻¹
  rw [inv_inv, ← hg]
  group

theorem Lv2520.caseC_card_centralizer_SCx_le (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) :
    Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.SCx : Set G)) ≤ 2 * Nat.card ↥N.SC := by
  have hSB := h.sBar hR
  have hcard := hSB.card_inf_mul_card_img
    (inf_le_left : N.S ⊓ Subgroup.centralizer (N.SCx : Set G) ≤ N.S)
  have himg : Nat.card ↥(hSB.img (N.S ⊓ Subgroup.centralizer (N.SCx : Set G))) ≤ 2 := by
    refine card_le_two_of_forall (a := hSB.ds.z) fun p hp => ?_
    obtain ⟨c, hcY, hcS, rfl⟩ := hSB.mem_img.mp hp
    exact hSB.pi_mem_of_centralizes_nonabelian h.SCx_le_S h.SCx_inf_SC (h.SCx_nonabelian hnab)
      hcS (fun b hb => Subgroup.mem_centralizer_iff.mp hcY.2 b hb)
  have hAY : Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.SCx : Set G) ⊓ N.SC) ≤ Nat.card ↥N.SC :=
    Subgroup.card_le_of_le inf_le_right
  calc Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.SCx : Set G))
      = Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.SCx : Set G) ⊓ N.SC) *
        Nat.card ↥(hSB.img (N.S ⊓ Subgroup.centralizer (N.SCx : Set G))) := hcard.symm
    _ ≤ Nat.card ↥N.SC * 2 := Nat.mul_le_mul hAY himg
    _ = 2 * Nat.card ↥N.SC := mul_comm _ _

theorem Lv2520.caseC_card_S0_le (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) :
    Nat.card ↥N.S0 ≤ 2 * Nat.card ↥N.SC := by
  have hY := h.caseC_card_centralizer_SCx_le hR hnab
  rw [h.S_inf_centralizer_SCx, BenderBranch.card_conjugate] at hY
  exact hY

theorem Lv2520.caseC_img_eq (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) :
    (h.sBar hR).img N.SCx = (h.sBar hR).img N.S0 := by
  have hSB := h.sBar hR
  have hf := h.facts2511
  have hcard := hSB.card_inf_mul_card_img N.S0_le_S
  have h2le := h.caseC_card_S0_inf_SC_le hR hnab
  have h2ge : 2 ≤ Nat.card ↥(N.S0 ⊓ N.SC) := by
    have hle : Subgroup.zpowers t ≤ N.S0 ⊓ N.SC := by
      rw [Subgroup.zpowers_le]
      exact ⟨Notation25.mem_S0.mpr ⟨hf.t_mem_center.1, fun a ha =>
        Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 a (N.SC_le_S ha)⟩, hf.t_mem⟩
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(Subgroup.zpowers t) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hf.t_sq hf.t_ne_one
    omega
  have h2 : Nat.card ↥(N.S0 ⊓ N.SC) = 2 := le_antisymm h2le h2ge
  have hS0 := h.caseC_card_S0_le hR hnab
  have h3 : Nat.card ↥(hSB.img N.SCx) = Nat.card ↥N.SC := by
    rw [hSB.card_img h.SCx_le_S h.SCx_inf_SC, N.card_SCx]
  have hle : Nat.card ↥(hSB.img N.S0) ≤ Nat.card ↥(hSB.img N.SCx) := by
    rw [h2] at hcard
    omega
  exact Subgroup.eq_of_le_of_card_ge (hSB.img_mono h.SCx_le_S0) hle

theorem Lv2520.caseC_exists_invol (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) :
    ∃ i ∈ N.SC, i ≠ 1 ∧ i * i = 1 ∧ i ≠ t := by
  have hSB := h.sBar hR
  have hf := h.facts2511
  obtain ⟨E, hESK, hE4⟩ := h.exists_four_SK
  obtain ⟨e, heE, he1, hezK⟩ := exists_ne_of_card_four hE4.2 zK
  have heSK : e ∈ N.SK := hESK heE
  have heS : e ∈ N.S := N.SK_le_S heSK
  have heK : e ∈ N.K := N.SK_le_K heSK
  have he2 : e * e = 1 := hE4.sq heE
  have hmem : actS N.K N.S h.S_le_normalizer e ∈ hSB.img N.SCx := by
    rw [h.caseC_img_eq hR hnab]
    exact hSB.img_mono h.SK_le_S0 (hSB.pi_mem_img heSK heS)
  obtain ⟨b, hbB, hbS, hb⟩ := hSB.mem_img.mp hmem
  have hb2 : b * b = 1 := by
    have h1 : actS N.K N.S h.S_le_normalizer (b * b) = 1 := by
      rw [hSB.mul b hbS b hbS, hb, ← hSB.mul e heS e heS, he2, hSB.pi_one]
    have h2 : b * b ∈ N.SC := (hSB.ker _ (N.S.mul_mem hbS hbS)).mp h1
    have h3 : b * b ∈ N.SCx ⊓ N.SC := ⟨N.SCx.mul_mem hbB hbB, h2⟩
    rw [h.SCx_inf_SC, Subgroup.mem_bot] at h3
    exact h3
  have hπe1 : actS N.K N.S h.S_le_normalizer e ≠ 1 := by
    intro h1
    exact he1 (h.K_inf_SC_eq_bot_mem heK ((hSB.ker e heS).mp h1))
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hπe1
    rw [← hb, hb1, hSB.pi_one]
  refine ⟨N.x * b * N.x⁻¹, Notation25.mem_SCx.mp hbB, ?_, ?_, ?_⟩
  · intro h1
    apply hb1
    calc b = N.x⁻¹ * (N.x * b * N.x⁻¹) * N.x := by group
      _ = 1 := by rw [h1]; group
  · calc N.x * b * N.x⁻¹ * (N.x * b * N.x⁻¹) = N.x * (b * b) * N.x⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  · intro hit
    have hbz : b = zK := by
      calc b = N.x⁻¹ * (N.x * b * N.x⁻¹) * N.x := by group
        _ = N.x⁻¹ * t * N.x := by rw [hit]
        _ = zK := h.caseC_tx hR hidx hnab
    have hzKS : zK ∈ N.S := hf.zK_mem_center.1
    have hpe : actS N.K N.S h.S_le_normalizer e = actS N.K N.S h.S_le_normalizer zK := by
      rw [← hb, hbz]
    have h1 : e⁻¹ * zK ∈ N.SC := (hSB.pi_eq_iff heS hzKS).mp hpe
    have hK : e⁻¹ * zK ∈ N.K :=
      N.K.mul_mem (N.K.inv_mem heK) (h.hK0 ▸ hf.zK_mem)
    exact hezK (inv_mul_eq_one.mp (h.K_inf_SC_eq_bot_mem hK h1))

structure CaseCParams (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)) : Prop where
  ds : DS.DSData R
  idx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC)
  nonab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a
  htx : N.x⁻¹ * t * N.x = zK
  hz : N.z = t * zK
  not_conj : ∀ g : G, g⁻¹ * t * g ≠ t * zK
  invol : ∃ i ∈ N.SC, i ≠ 1 ∧ i * i = 1 ∧ i ≠ t

theorem Lv2520.caseCParams (h : Lv2520 N t zK) (hR : DS.DSData R)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hnab : ∃ a ∈ N.SC, ∃ b ∈ N.SC, a * b ≠ b * a) : CaseCParams N t zK R where
  ds := hR
  idx := hidx
  nonab := hnab
  htx := h.caseC_tx hR hidx hnab
  hz := h.caseC_z hR hidx hnab
  not_conj := h.caseC_not_conj hR hidx hnab
  invol := h.caseC_exists_invol hR hidx hnab

end CaseC

@[expose] def Lemma2521CaseC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (hs : UnconstrainedSetting G T M)
    (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)),
    Lv2520 N t zK → OutFamily N.K N.H → CaseCParams N t zK R → False

end CFSG.QuasithinUnique
