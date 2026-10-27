module

public import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Walter.W67.W1Basic
import CFSG.Walter.Bender1970.S4.ComponentTools
public import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.Goldschmidt

namespace G74

variable {G : Type} [Group G] [Finite G]

section Products

omit [Finite G] in
theorem comm_of_le {A X Y : Subgroup G} (hA : IsMulCommutative A) (hX : X ≤ A) (hY : Y ≤ A) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hX hx⟩ ⟨y, hY hy⟩)

theorem card_sup_le {A X Y : Subgroup G} (hA : IsMulCommutative A) (hX : X ≤ A) (hY : Y ≤ A) :
    Nat.card (X ⊔ Y : Subgroup G) ≤ Nat.card X * Nat.card Y := by
  obtain ⟨h, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute X Y (comm_of_le hA hX hY)
  rw [← h]
  exact Nat.le_mul_of_pos_right _ Nat.card_pos

omit [Finite G] in
theorem card_sup_of_inf_eq_bot {A X Y : Subgroup G} (hA : IsMulCommutative A) (hX : X ≤ A)
    (hY : Y ≤ A) (hXY : X ⊓ Y = ⊥) :
    Nat.card (X ⊔ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  obtain ⟨h, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute X Y (comm_of_le hA hX hY)
  rwa [hXY, Subgroup.card_bot, mul_one] at h

end Products

section CommMap

variable {A : Subgroup G}

omit [Finite G] in
theorem conj_mem {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) {x : G}
    (hx : x ∈ A) : y * x * y⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hy x).mp hx

@[expose] def commMap (hA : IsMulCommutative A) {y : G} (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    A →* A where
  toFun x := ⟨y * x * y⁻¹ * x⁻¹, A.mul_mem (conj_mem hy x.2) (A.inv_mem x.2)⟩
  map_one' := by ext; simp
  map_mul' x z := by
    ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    have hb : y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ A :=
      A.mul_mem (conj_mem hy z.2) (A.inv_mem z.2)
    have hc := comm_of_le hA le_rfl le_rfl _ (A.inv_mem x.2) _ hb
    calc y * (x * z) * y⁻¹ * ((z : G)⁻¹ * (x : G)⁻¹)
        = y * x * y⁻¹ * ((y * z * y⁻¹ * (z : G)⁻¹) * (x : G)⁻¹) := by group
      _ = y * x * y⁻¹ * ((x : G)⁻¹ * (y * z * y⁻¹ * (z : G)⁻¹)) := by rw [hc]
      _ = y * x * y⁻¹ * (x : G)⁻¹ * (y * z * y⁻¹ * (z : G)⁻¹) := by group

omit [Finite G] in
theorem commMap_apply (hA : IsMulCommutative A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (x : A) :
    (commMap hA hy x : G) = y * x * y⁻¹ * (x : G)⁻¹ := rfl

omit [Finite G] in
theorem mem_ker_commMap (hA : IsMulCommutative A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (x : A) :
    x ∈ (commMap hA hy).ker ↔ (x : G) ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_singleton_iff, ← Subtype.val_inj,
    commMap_apply, OneMemClass.coe_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

omit [Finite G] in
theorem card_ker_commMap (hA : IsMulCommutative A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card (commMap hA hy).ker =
      Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  have h : (commMap hA hy).ker.map A.subtype = A ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (mem_ker_commMap hA hy z).mp hz⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, (mem_ker_commMap hA hy _).mpr hx.2, rfl⟩
  rw [← h, Subgroup.card_map_of_injective A.subtype_injective]

omit [Finite G] in
theorem card_eq_mul (hA : IsMulCommutative A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) :
    Nat.card A = Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) *
      Nat.card (commMap hA hy).range := by
  rw [← card_ker_commMap hA hy, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem le_commutator_of_inf_centralizer_eq_bot (hA : IsMulCommutative A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G))
    (h : A ⊓ Subgroup.centralizer ({y} : Set G) = ⊥) : A ≤ ⁅A, Subgroup.zpowers y⁆ := by
  have hinj : Function.Injective (commMap hA hy) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ A ⊓ Subgroup.centralizer ({y} : Set G) :=
      ⟨x.2, (mem_ker_commMap hA hy x).mp hx⟩
    rw [h, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have hsurj := Finite.surjective_of_injective hinj
  intro x hx
  obtain ⟨z, hz⟩ := hsurj ⟨x, hx⟩
  have hx' : x = y * z * y⁻¹ * (z : G)⁻¹ := by rw [← commMap_apply hA hy z, hz]
  rw [hx', Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) z.2

theorem four_mul_card_le (hA : CFSG.Open.IsElemAbelian 2 A) {y : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hyodd : Odd (orderOf y))
    (hyA : y ∉ Subgroup.centralizer (A : Set G)) :
    4 * Nat.card (A ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ≤ Nat.card A := by
  set ψ := commMap hA.1 hy
  have hc : ∀ x : A, (ψ x : G) * x = y * x * y⁻¹ := fun x => by
    rw [commMap_apply]; group
  obtain ⟨b, hb, hbc⟩ : ∃ b ∈ ψ.range, y * (b : G) * y⁻¹ ≠ b := by
    by_contra hcon
    push Not at hcon
    apply hyA
    have hy2 : ∀ x ∈ A, y ^ 2 * x * (y ^ 2)⁻¹ = x := by
      intro x hx
      have h1 := hcon (ψ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
      have h2 := hc ⟨x, hx⟩
      have h3 : (ψ ⟨x, hx⟩ : G) * (ψ ⟨x, hx⟩ : G) = 1 := by
        rw [← sq]; exact hA.2 _ (ψ ⟨x, hx⟩).2
      calc y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by rw [sq]; group
        _ = y * ((ψ ⟨x, hx⟩ : G) * x) * y⁻¹ := by rw [← h2]
        _ = (y * (ψ ⟨x, hx⟩ : G) * y⁻¹) * (y * x * y⁻¹) := by group
        _ = (ψ ⟨x, hx⟩ : G) * ((ψ ⟨x, hx⟩ : G) * x) := by rw [h1, ← h2]
        _ = x := by rw [← mul_assoc, h3, one_mul]
    obtain ⟨k, hk⟩ := hyodd
    have hyeq : y = (y ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx2 : ∀ n : ℕ, (y ^ 2) ^ n * x * ((y ^ 2) ^ n)⁻¹ = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (y ^ 2) ^ (n + 1) * x * ((y ^ 2) ^ (n + 1))⁻¹
            = (y ^ 2) ^ n * (y ^ 2 * x * (y ^ 2)⁻¹) * ((y ^ 2) ^ n)⁻¹ := by group
          _ = x := by rw [hy2 x hx, ih]
    have := hx2 (k + 1)
    rw [← hyeq] at this
    calc x * y = y * x * y⁻¹ * y := by rw [this]
      _ = y * x := by group
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbc (by simp)
  have hcb : (⟨y * (b : G) * y⁻¹, conj_mem hy b.2⟩ : A) ∈ ψ.range := by
    obtain ⟨x, rfl⟩ := hb
    refine ⟨⟨y * x * y⁻¹, conj_mem hy x.2⟩, Subtype.ext ?_⟩
    simp only [ψ, commMap_apply]
    group
  have hcb1 : (⟨y * (b : G) * y⁻¹, conj_mem hy b.2⟩ : A) ≠ 1 := by
    intro h
    apply hb1
    have h1 : y * (b : G) * y⁻¹ = 1 := congrArg Subtype.val h
    exact Subtype.ext (by
      calc (b : G) = y⁻¹ * (y * b * y⁻¹) * y := by group
        _ = 1 := by rw [h1]; group)
  have hcbb : (⟨y * (b : G) * y⁻¹, conj_mem hy b.2⟩ : A) ≠ b := fun h =>
    hbc (congrArg Subtype.val h)
  have h3 : 3 ≤ Nat.card ψ.range := by
    classical
    have : Fintype ψ.range := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    let s : Finset ψ.range := {1, ⟨b, hb⟩, ⟨_, hcb⟩}
    have hs : s.card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair]
      · intro h; exact hcbb (congrArg Subtype.val h).symm
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hb1 (congrArg Subtype.val h).symm,
          fun h => hcb1 (congrArg Subtype.val h).symm⟩
    rw [← hs]
    exact Finset.card_le_univ s
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := fun g => ⟨1, by simpa only [pow_one] using Subtype.ext (hA.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := hA2.exists_card_eq
  have hdvd : Nat.card ψ.range ∣ 2 ^ n := hn ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h4 : 4 ≤ Nat.card ψ.range := by
    rw [hk] at h3 ⊢
    rcases k with _ | _ | k
    · norm_num at h3
    · norm_num at h3
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [card_eq_mul hA.1 hy, mul_comm]
  exact Nat.mul_le_mul_left _ h4

end CommMap

section L2

omit [Finite G] in
theorem card_le_four_mul {A K : Subgroup G} (hA : IsPGroup 2 A) (hK : IsGoldL2 K) :
    Nat.card (A ⊓ K : Subgroup G) ≤
      4 * Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  obtain ⟨p, f, hp, hpodd, hf, -, h8, ⟨e⟩⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : (A ⊓ K : Subgroup G) →* K ⧸ Subgroup.center K :=
    (QuotientGroup.mk' (Subgroup.center K)).comp (Subgroup.inclusion inf_le_right) with hφ
  have hker : Nat.card φ.ker =
      Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
    have hmem : ∀ x : (A ⊓ K : Subgroup G), x ∈ φ.ker ↔
        (x : G) ∈ Subgroup.centralizer (K : Set G) := by
      intro x
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h k hk
        exact congrArg Subtype.val (h ⟨k, hk⟩)
      · intro h k
        exact Subtype.ext (h k k.2)
    have h : φ.ker.map (A ⊓ K).subtype = A ⊓ K ⊓ Subgroup.centralizer (K : Set G) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, (hmem z).mp hz⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, (hmem _).mpr hx.2, rfl⟩
    rw [← h, Subgroup.card_map_of_injective (A ⊓ K).subtype_injective]
  have hrange : Nat.card φ.range ≤ 4 := by
    have h2 : IsPGroup 2 (A ⊓ K : Subgroup G) := hA.to_le inf_le_left
    have h2r : IsPGroup 2 φ.range := h2.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    have h2e : IsPGroup 2 (φ.range.map e.toMonoidHom) := h2r.map _
    obtain ⟨P, hP⟩ := h2e.exists_le_sylow
    rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
      ← (CFSG.Walter.psl2_odd_sylow_two_isKleinFour hpodd hf h8 P).card_four]
    exact Subgroup.card_le_of_le hP
  rw [← hker, ← Subgroup.card_mul_index φ.ker, Subgroup.index_ker, mul_comm]
  exact Nat.mul_le_mul_right _ hrange

end L2

section Fusion

theorem mem_normalizer_of_conj_le {S : Sylow 2 G} {A T : Subgroup G}
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hAT : A ≤ T)
    (hT : IsPGroup 2 T) {g : G} (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ T) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ, hQ⟩ := stronglyClosed_of_le_pGroup S hcl hT hAT
  have hle : conjSub g⁻¹ A ≤ (Q : Subgroup G) := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have h1 := hg _ hx
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e] at h1
    exact hTQ h1
  have heq := conj_eq_of_conj_le hQ hle
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : g * y * g⁻¹ ∈ conjSub g⁻¹ A := by
      rw [mem_conjSub, inv_inv]
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]
      exact hy
    rwa [heq] at h1
  · intro hy
    rw [← heq, mem_conjSub, inv_inv] at hy
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [e] at hy

theorem le_sup_normalizer {S : Sylow 2 G} {A X M : Subgroup G} (hAS : A ≤ S)
    (hcl : CFSG.Open.fusionStronglyClosed (A : Set G) (S : Subgroup G)) (hMX : M ≤ X)
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) (hAM : A ≤ M) :
    X ≤ M ⊔ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hAS
  obtain ⟨PX, hPX⟩ := (hA2.comap_subtype (K := X)).exists_le_sylow
  have hMn : (M.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMX).mpr hXM
  obtain ⟨P', hP'⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal PX hMn.isSubnormal
  have hN := Sylow.normalizer_sup_eq_top P'
  rw [hP'] at hN
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ Subgroup.normalizer
      (((PX : Subgroup X) ⊓ M.subgroupOf X : Subgroup X) : Set X) ⊔ M.subgroupOf X := by
    rw [hN]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, m, hm, hhm⟩ := Subgroup.mem_sup_of_normal_right.1 hmem
  have hAX : A ≤ X := hAM.trans hMX
  have hhA : (h : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine mem_normalizer_of_conj_le hcl (T := ((PX : Subgroup X) ⊓ M.subgroupOf X).map X.subtype)
      (fun a ha => ⟨⟨a, hAX ha⟩, ⟨hPX (show (⟨a, hAX ha⟩ : X) ∈ A.comap X.subtype from ha),
        hAM ha⟩, rfl⟩) ((PX.isPGroup'.to_le inf_le_left).map _) fun a ha => ?_
    have h1 : (⟨a, hAX ha⟩ : X) ∈ (PX : Subgroup X) ⊓ M.subgroupOf X :=
      ⟨hPX (show (⟨a, hAX ha⟩ : X) ∈ A.comap X.subtype from ha), hAM ha⟩
    exact ⟨_, (Subgroup.mem_normalizer_iff.mp hh _).mp h1, rfl⟩
  have hx' : x = (h : G) * m := (congrArg Subtype.val hhm).symm
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hhA) (Subgroup.mem_sup_left hm)

end Fusion

section Conj

theorem index_eq_two {X K : Subgroup G} {x₁ : G} (hx₁ : x₁ ∈ X)
    (hx₁K : K.map (MulAut.conj x₁).toMonoidHom ≠ K)
    (huniq : ∀ a ∈ X, ∀ b ∈ X, K.map (MulAut.conj a).toMonoidHom ≠ K →
      K.map (MulAut.conj b).toMonoidHom ≠ K →
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    ((X ⊓ Subgroup.normalizer (K : Set G)).subgroupOf X).index = 2 := by
  set K' := K.map (MulAut.conj x₁).toMonoidHom with hK'
  have hmemA : ∀ b : X, b ∈ (X ⊓ Subgroup.normalizer (K : Set G)).subgroupOf X ↔
      K.map (MulAut.conj (b : G)).toMonoidHom = K := fun b => by
    rw [Subgroup.mem_subgroupOf, CFSG.Walter.map_conj_eq_iff_mem_normalizer]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  have hinj : ∀ (b : G) (A₁ A₂ : Subgroup G), A₁.map (MulAut.conj b).toMonoidHom =
      A₂.map (MulAut.conj b).toMonoidHom → A₁ = A₂ :=
    fun b _ _ h => Subgroup.map_injective (MulAut.conj b).injective h
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x₁, hx₁⟩, fun b => xor_iff_iff_not.mpr ⟨fun hbg hb => ?_, fun hb => ?_⟩⟩
  · rw [hmemA, Subgroup.coe_mul, ← CFSG.Walter.map_conj_map_conj] at hbg
    rw [hmemA] at hb
    exact hx₁K (hinj b K' K (hbg.trans hb.symm))
  · rw [hmemA] at hb
    rw [hmemA, Subgroup.coe_mul, ← CFSG.Walter.map_conj_map_conj]
    by_contra hne
    have h1 := huniq _ (X.mul_mem b.2 hx₁) _ b.2
      (by rw [← CFSG.Walter.map_conj_map_conj]; exact hne) hb
    rw [← CFSG.Walter.map_conj_map_conj] at h1
    exact hx₁K (hinj b K' K h1)

end Conj

section Setting

variable {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem le_derivedSeries {Q : Type*} [Group Q] {L : Subgroup Q} (hL : ⁅L, L⁆ = L) (n : ℕ) :
    L ≤ derivedSeries Q n := by
  induction n with
  | zero =>
    rw [derivedSeries_zero]
    exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc L = ⁅L, L⁆ := hL.symm
      _ ≤ _ := Subgroup.commutator_mono ih ih

theorem not_forall_centralizer_le (hG : GoldSetting G S A) {H : Subgroup G} (hH : H ≠ ⊤)
    (h : ∀ c ∈ A, c ≠ 1 → Subgroup.centralizer ({c} : Set G) ≤ H) : False := by
  apply hH
  rw [eq_top_iff, ← hG.gen]
  exact iSup_le fun c => h c.1 c.2.1 c.2.2

theorem inf_centralizer_ne_bot (h36 : S_G36) (hG : GoldSetting G S A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) {K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) :
    A ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ := by
  intro h0
  obtain ⟨y, hy, -, htr, hyC, -⟩ :=
    h36 G H A (G73.isSStarIn_of_mem_benderM hG ha hH) hG.elem K hK
  rw [h0] at hyC
  have hAle := le_commutator_of_inf_centralizer_eq_bot hG.elem.1 hy.2 hyC
  have hyH : y ∈ H := (G73.isComponentOf_of_normalClosureIn hK).1 hy.1
  refine not_forall_centralizer_le hG (CFSG.Walter.ne_top_of_mem_benderM hH) fun c hc hc1 => ?_
  obtain ⟨k, hk⟩ := htr a (hAle ha) c (hAle hc) ha1 hc1
  intro g hg
  have hykH : y ^ k ∈ H := H.pow_mem hyH k
  have hg' : y ^ k * g * (y ^ k)⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    rw [← hk] at hg
    calc y ^ k * g * (y ^ k)⁻¹ * a = y ^ k * (g * ((y ^ k)⁻¹ * a * y ^ k)) * (y ^ k)⁻¹ := by
          group
      _ = y ^ k * (((y ^ k)⁻¹ * a * y ^ k) * g) * (y ^ k)⁻¹ := by rw [hg]
      _ = a * (y ^ k * g * (y ^ k)⁻¹) := by group
  have h2 := CFSG.Walter.centralizer_le_of_mem_benderM hH hg'
  have hge : g = (y ^ k)⁻¹ * (y ^ k * g * (y ^ k)⁻¹) * y ^ k := by group
  rw [hge]
  exact H.mul_mem (H.mul_mem (H.inv_mem hykH) h2) hykH

theorem four_mul_card_inf_centralizer_le (h31 : S_G31) (h36 : S_G36) (hG : GoldSetting G S A)
    {a : G} (ha : a ∈ A) {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) {K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) :
    4 * Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ Nat.card A := by
  have hS := G73.isSStarIn_of_mem_benderM hG ha hH
  obtain ⟨y, hy, hyodd, -, hyC, -⟩ := h36 G H A hS hG.elem K hK
  rw [← hyC]
  refine four_mul_card_le hG.elem hy.2 hyodd fun hyA => ?_
  apply G73.not_inf_le_centralizer h31 hS hG.elem hK
  intro x hx
  have hxy : x ∈ A ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyA x hx.1)⟩
  rw [hyC] at hxy
  exact hxy.2

theorem card_le_four_mul_of_isGoldL2 (h31 : S_G31) (hG : GoldSetting G S A) {a : G}
    (ha : a ∈ A) {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) {K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A)) (hK2 : IsGoldL2 K) :
    Nat.card A ≤ 4 * Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  have hS := G73.isSStarIn_of_mem_benderM hG ha hH
  have hα := G73.eq_inf_sup_inf_centralizer h31 hS hG.elem hK
  obtain ⟨h1, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (A ⊓ K)
    (A ⊓ Subgroup.centralizer (K : Set G)) (comm_of_le hG.elem.1 inf_le_left inf_le_left)
  rw [← hα] at h1
  have hinf : A ⊓ K ⊓ (A ⊓ Subgroup.centralizer (K : Set G)) =
      A ⊓ K ⊓ Subgroup.centralizer (K : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hinf] at h1
  have h2 := card_le_four_mul (G73.isPGroup hG) hK2
  have hpos : 0 < Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
    Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) * Nat.card A
      = Nat.card (A ⊓ K : Subgroup G) * Nat.card (A ⊓ Subgroup.centralizer (K : Set G) :
          Subgroup G) := by rw [mul_comm, h1]
    _ ≤ 4 * Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) *
          Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
        Nat.mul_le_mul_right _ h2
    _ = Nat.card (A ⊓ K ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) *
          (4 * Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G)) := by ring

theorem normalClosureIn_le_sup (h71 : S_G71) (hG : GoldSetting G S A) (h8 : 8 ≤ Nat.card A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) :
    normalClosureIn H A ≤ A ⊔ GorensteinWalter.componentLayerOf (normalClosureIn H A) ⊔
      oddCoreOf (normalClosureIn H A) := by
  set K := normalClosureIn H A with hKdef
  obtain ⟨n, hn⟩ := h71 G S A hG h8 a ha ha1 H hH
  obtain ⟨-, -, T, -, -, -, h1, -, h3, -⟩ := G73.isSStarIn_of_mem_benderM hG ha hH
  set π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore K) with hπ
  have hlayer : CFSG.Open.goldschmidtLayer (K ⧸ CFSG.Open.goldschmidtOddCore K) ≤
      (derivedSeries K n).map π := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _)]
    refine sSup_le fun L hL => le_derivedSeries ?_ n
    exact Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hL.2.2.1)
  have htop : (⊤ : Subgroup (K ⧸ CFSG.Open.goldschmidtOddCore K)) ≤
      (A.subgroupOf K ⊔ derivedSeries K n).map π := by
    rw [Subgroup.map_sup, ← h1]
    refine sup_le_sup ?_ hlayer
    change CFSG.Open.pCore 2 (K ⧸ CFSG.Open.goldschmidtOddCore K) ≤ barOf K A
    rw [h3]
    exact le_sup_left
  have h4 : (⊤ : Subgroup K) ≤
      A.subgroupOf K ⊔ derivedSeries K n ⊔ CFSG.Open.goldschmidtOddCore K := by
    have := Subgroup.comap_mono (f := π) htop
    rwa [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  intro x hx
  have h5 := Subgroup.mem_map_of_mem K.subtype (h4 (Subgroup.mem_top (⟨x, hx⟩ : K)))
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype] at h5
  exact sup_le_sup (sup_le_sup inf_le_left hn) le_rfl h5

end Setting

end G74

end CFSG.Goldschmidt
