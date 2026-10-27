module

public import CFSG.Quasithin.H13.A6S1356S6Fr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1356S6

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

private theorem elem_sup_zpowers {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : IsElemAbelian 3 A) {y : G} (hyA : ∀ a ∈ A, a * y = y * a) (hy3 : y ^ 3 = 1)
    (hy : y ∉ A) :
    IsElemAbelian 3 (A ⊔ Subgroup.zpowers y) ∧
      Nat.card (A ⊔ Subgroup.zpowers y : Subgroup G) = 3 * Nat.card A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : A ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
    intro a ha
    refine Subgroup.centralizer_le_normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hyA a ha).symm
  have hy1 : y ≠ 1 := fun h => hy (h ▸ A.one_mem)
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hZ : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
  have hinf : A ⊓ Subgroup.zpowers y = ⊥ := by
    have hd : Nat.card ↥(A ⊓ Subgroup.zpowers y) ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      apply hy
      have e : A ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hZ])
      have : y ∈ A ⊓ Subgroup.zpowers y := by rw [e]; exact Subgroup.mem_zpowers y
      exact this.1
  have hprod := card_sup_mul_card_inf' hle
  rw [hinf, Subgroup.card_bot, mul_one, hZ] at hprod
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, by rw [hprod, mul_comm]⟩
  · have hset := Subgroup.coe_mul_of_left_le_normalizer_right A (Subgroup.zpowers y) hle
    have ha : (a : G) ∈ (A : Set G) * (Subgroup.zpowers y : Set G) := by rw [← hset]; exact a.2
    have hb : (b : G) ∈ (A : Set G) * (Subgroup.zpowers y : Set G) := by rw [← hset]; exact b.2
    obtain ⟨a₁, ha₁, z₁, hz₁, hae⟩ := ha
    obtain ⟨b₁, hb₁, z₂, hz₂, hbe⟩ := hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₁
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz₂
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hae, ← hbe]
    have c1 : Commute a₁ (y ^ l) := Commute.zpow_right (hyA a₁ ha₁) l
    have c2 : Commute b₁ (y ^ k) := Commute.zpow_right (hyA b₁ hb₁) k
    have c3 : a₁ * b₁ = b₁ * a₁ := isElemAbelian_comm hA ha₁ hb₁
    have c4 : y ^ k * y ^ l = y ^ l * y ^ k := by rw [← zpow_add, ← zpow_add, add_comm]
    calc a₁ * y ^ k * (b₁ * y ^ l) = a₁ * (y ^ k * b₁) * y ^ l := by group
      _ = a₁ * (b₁ * y ^ k) * y ^ l := by rw [c2.eq]
      _ = (a₁ * b₁) * (y ^ k * y ^ l) := by group
      _ = (b₁ * a₁) * (y ^ l * y ^ k) := by rw [c3, c4]
      _ = b₁ * (a₁ * y ^ l) * y ^ k := by group
      _ = b₁ * (y ^ l * a₁) * y ^ k := by rw [c1.eq]
      _ = b₁ * y ^ l * (a₁ * y ^ k) := by group
  · have hset := Subgroup.coe_mul_of_left_le_normalizer_right A (Subgroup.zpowers y) hle
    have hx' : x ∈ (A : Set G) * (Subgroup.zpowers y : Set G) := by rw [← hset]; exact hx
    obtain ⟨a, ha, z, hz, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcommaz : Commute a (y ^ k) := Commute.zpow_right (hyA a ha) k
    rw [hcommaz.mul_pow, hA.2 a ha, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hy3, one_zpow]

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section L2

variable (h13315 : Stmt13_3_15_F4) (hhat : ¬ IsHatA6 L)
include h13315 hhat

theorem L2_le_I2_and_F4 :
    S.L2 ≤ conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) ∧
      S.L2 ⊓ Subgroup.centralizer (S.V2 : Set G) ≤
        pCoreOf 2 (conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G))) := by
  obtain ⟨-, hI, hC, -⟩ := h13315 G T L V S.V2 S.X2 _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 S.X2_hat S.X2_not_hat rfl
  rw [S.X2_not_hat hhat] at hI
  have hle : S.L2 ≤ conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) := by
    rw [hI]; exact le_sup_left
  exact ⟨hle, (inf_le_inf_right _ hle).trans hC.le⟩

theorem isPGroup_L2_inf_C_F4 : IsPGroup 2 ↥(S.L2 ⊓ Subgroup.centralizer (S.V2 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCoreOf_isPGroup 2 _).to_le (S.L2_le_I2_and_F4 h13315 hhat).2

theorem not_mem_C_V2_of_cube_F4 {x : G} (hxL2 : x ∈ S.L2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    x ∉ Subgroup.centralizer (S.V2 : Set G) := by
  intro hxC
  obtain ⟨k, hk⟩ := S.isPGroup_L2_inf_C_F4 h13315 hhat ⟨x, hxL2, hxC⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf x ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one hk')
  have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact hx1 h1

theorem comm_odd_mem_F4 {a b : G} (ha : a ∈ S.L2) (hb : b ∈ S.L2) {m n : ℕ} (hm : Odd m)
    (hn : Odd n) (ham : a ^ m = 1) (hbn : b ^ n = 1) : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 S.L2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hI, -, ⟨e⟩, -⟩ := h13315 G T L V S.V2 S.X2 _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 S.X2_hat S.X2_not_hat rfl
  set I₂ := conjClosure (pCoreOf 2 (g1 T V)) (Subgroup.normalizer (S.V2 : Set G)) with hI₂
  have hle := (S.L2_le_I2_and_F4 h13315 hhat).1
  let φ : ↥I₂ →* Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hodd : ∀ {c : G} (hc : c ∈ S.L2) {k : ℕ}, Odd k → c ^ k = 1 → φ ⟨c, hle hc⟩ ^ 3 = 1 := by
    intro c hc k hk hck
    rw [← orderOf_dvd_iff_pow_eq_one]
    have h1 : orderOf (φ ⟨c, hle hc⟩) ∣ k := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← map_pow]
      have : (⟨c, hle hc⟩ : ↥I₂) ^ k = 1 := Subtype.ext (by simpa using hck)
      rw [this, map_one]
    have h2 : orderOf (φ ⟨c, hle hc⟩) ∣ 2 * 3 := by
      have := orderOf_dvd_card (x := φ ⟨c, hle hc⟩)
      rwa [Fintype.card_perm, Fintype.card_fin] at this
    have hcop : (orderOf (φ ⟨c, hle hc⟩)).Coprime 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h2' =>
        (Nat.not_even_iff_odd.mpr hk) (even_iff_two_dvd.mpr (h2'.trans h1)))
    exact hcop.dvd_of_dvd_mul_left h2
  have hcomm := s3_odd_comm _ _ (hodd ha hm ham) (hodd hb hn hbn)
  have hker : φ (⟨a, hle ha⟩ * ⟨b, hle hb⟩ * (⟨a, hle ha⟩)⁻¹ * (⟨b, hle hb⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hmem : (⟨a, hle ha⟩ * ⟨b, hle hb⟩ * (⟨a, hle ha⟩)⁻¹ * (⟨b, hle hb⟩)⁻¹ : ↥I₂) ∈
      CFSG.pCore 2 ↥I₂ := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥I₂)
        (⟨a, hle ha⟩ * ⟨b, hle hb⟩ * (⟨a, hle ha⟩)⁻¹ * (⟨b, hle hb⟩)⁻¹) = 1 :=
      e.injective (by rw [map_one]; exact hker)
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hO : a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 I₂ := by
    unfold pCoreOf
    exact Subgroup.mem_map_of_mem I₂.subtype hmem
  have hL : a * b * a⁻¹ * b⁻¹ ∈ S.L2 :=
    S.L2.mul_mem (S.L2.mul_mem (S.L2.mul_mem ha hb) (S.L2.inv_mem ha)) (S.L2.inv_mem hb)
  have hsub : S.L2 ⊓ pCoreOf 2 I₂ ≤ pCoreOf 2 S.L2 := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun l hl => ?_)
      ((pCoreOf_isPGroup 2 I₂).to_le inf_le_right)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hl) y)
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 I₂ (hle hl)) y)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  exact hsub ⟨hL, hO⟩

theorem relIndex_cent_O2L2_F4 {x : G} (hxL2 : x ∈ S.L2) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    32 ≤ (pCoreOf 2 S.L2 ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (pCoreOf 2 S.L2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 S.L2 with hPdef
  set C := P ⊓ Subgroup.centralizer ({x} : Set G) with hCdef
  have hxL : x ∈ L := S.L2_le_L hxL2
  set xN : ↥(Subgroup.normalizer (V : Set G)) := ⟨x, S.frame.L_le hxL⟩ with hxNdef
  have hxC : x ∉ Subgroup.centralizer (S.V2 : Set G) :=
    S.not_mem_C_V2_of_cube_F4 h13315 hhat hxL2 hx3 hx1
  have hst := S.stabW2_of_mem (x := xN) (S.L2_le_NV2 hxL2)
  have hmv := S.movesW2_of_not_mem (x := xN) hxC
  have h3 : (S.frame.ρ xN) ^ 3 = 1 := by
    rw [← map_pow]
    have : xN ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  obtain ⟨hfp, hnofix⟩ := syn3_facts _ hst h3 hmv
  have h45 : (S.frame.ρ xN) ^ 45 = 1 := by
    rw [show (45 : ℕ) = 3 * 15 by norm_num, pow_mul, h3, one_pow]
  obtain ⟨hFPF, -⟩ := fpf_of _ hst h45 hmv
  have hVab := S.elemAbelian_V
  have hVp : IsPGroup 2 V := isPGroup_of_isElemAbelian hVab
  have hVL2 : V ≤ S.L2 := S.le_of_fpf (x := xN) hxL2 S.V_le_NL2 hFPF
  have hL2N : S.L2 ≤ Subgroup.normalizer (V : Set G) := fun l hl => S.frame.L_le (S.L2_le_L hl)
  have hVP : V ≤ P := le_pCoreOf_of_le_normalizer 2 hVL2 hL2N hVp

  have hCV : C ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvx : v * x = x * v := Subgroup.mem_centralizer_singleton_iff.mp hv.1.2
    have hconj : (xN : G) * v * (xN : G)⁻¹ = v := by
      show x * v * x⁻¹ = v
      rw [← hvx, mul_inv_cancel_right]
    have h1 := (S.conj_eq_iff xN ⟨v, hv.2⟩).1 hconj
    have h2 := hnofix _ (S.frame.ψ ⟨v, hv.2⟩).2 (congrArg Subtype.val h1)
    have : (⟨v, hv.2⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [map_one]; exact Subtype.ext h2)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

  have hCC : C ≤ Subgroup.centralizer (V : Set G) := by
    intro q hq
    have hqL : q ∈ L := S.L2_le_L (pCoreOf_le 2 S.L2 hq.1)
    set qN : ↥(Subgroup.normalizer (V : Set G)) := ⟨q, S.frame.L_le hqL⟩ with hqNdef
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L2 ⟨q, hq.1⟩
    have hk' : qN ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h4 : (S.frame.ρ qN) ^ 4 = 1 := perm6_pow_four_of_two (by rw [← map_pow, hk', map_one])
    have hs : Perm.sign (S.frame.ρ qN) = 1 :=
      Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨qN, hqL, rfl⟩)
    have hcomm : S.frame.ρ xN * S.frame.ρ qN = S.frame.ρ qN * S.frame.ρ xN := by
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      show x * q = q * x
      exact (Subgroup.mem_centralizer_singleton_iff.mp hq.2).symm
    have h1 := comm_fpf3 _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h3, hfp⟩) _ h4 hs hcomm
    exact (S.rho_eq_one_iff qN).1 h1

  obtain ⟨a, haL, ⟨m, hm, ham⟩, ha⟩ := S.exists_L_odd s024_facts.2.1 s024_facts.1
  obtain ⟨b, hbL, ⟨n, hn, hbn⟩, hb⟩ := S.exists_L_odd s024_facts.2.2.2 s024_facts.2.2.1
  have hstab2 : ∀ σ : Perm (Fin 6), StabW2 σ → StabW2 (σ * σ) := fun σ h y hy => by
    rw [act4f_mul]; exact h _ (h y hy)
  have haN : (a : G) ∈ Subgroup.normalizer (S.V2 : Set G) := by
    refine S.mem_normalizer_V2_of ?_
    rcases ha with h | h <;> rw [h]
    · exact stabW2_s024
    · exact hstab2 _ stabW2_s024
  have hbN : (b : G) ∈ Subgroup.normalizer (S.V2 : Set G) := by
    refine S.mem_normalizer_V2_of ?_
    rcases hb with h | h <;> rw [h]
    · exact stabW2_s025
    · exact hstab2 _ stabW2_s025
  have ham' : (a : G) ^ m = 1 := by simpa using congrArg Subtype.val ham
  have hbn' : (b : G) ^ n = 1 := by simpa using congrArg Subtype.val hbn
  have haL2 := S.mem_L2_of_odd haL haN hm ham'
  have hbL2 := S.mem_L2_of_odd hbL hbN hn hbn'
  have hcP := S.comm_odd_mem_F4 h13315 hhat haL2 hbL2 hm hn ham' hbn'
  have hcC : (a : G) * b * (a : G)⁻¹ * (b : G)⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
    intro h
    have h1 := (S.rho_eq_one_iff (a * b * a⁻¹ * b⁻¹)).2 (by simpa using h)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : S.frame.ρ a * S.frame.ρ b = S.frame.ρ b * S.frame.ρ a := by
      calc S.frame.ρ a * S.frame.ρ b =
          (S.frame.ρ a * S.frame.ρ b * (S.frame.ρ a)⁻¹ * (S.frame.ρ b)⁻¹) *
            (S.frame.ρ b * S.frame.ρ a) := by group
        _ = S.frame.ρ b * S.frame.ρ a := by rw [h1, one_mul]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] at h2
    · exact s024_s025_noncomm 1 (by simp) 1 (by simp) (by simpa using h2)
    · exact s024_s025_noncomm 1 (by simp) 2 (by simp) (by simpa [sq] using h2)
    · exact s024_s025_noncomm 2 (by simp) 1 (by simp) (by simpa [sq] using h2)
    · exact s024_s025_noncomm 2 (by simp) 2 (by simp) (by simpa [sq] using h2)

  have hCN : C ≤ Subgroup.normalizer (V : Set G) := fun q hq => hL2N (pCoreOf_le 2 S.L2 hq.1)
  have hprod := card_sup_mul_card_inf' hCN
  rw [hCV, Subgroup.card_bot, mul_one, S.card_V] at hprod
  have r1 := Subgroup.relIndex_mul_card C (C ⊔ V)
  rw [inf_eq_left.2 le_sup_left] at r1
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h16 : C.relIndex (C ⊔ V) = 16 := by
    have : C.relIndex (C ⊔ V) * Nat.card C = 16 * Nat.card C := by rw [r1, hprod, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hCVle : C ⊔ V ≤ P := sup_le inf_le_left hVP
  have hle2 : 2 ≤ (C ⊔ V).relIndex P := by
    have hne : (C ⊔ V).relIndex P ≠ 1 := by
      intro h1
      rw [Subgroup.relIndex_eq_one] at h1
      apply hcC
      have hmem := h1 hcP
      have hsub : C ⊔ V ≤ Subgroup.centralizer (V : Set G) :=
        sup_le hCC fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
          isElemAbelian_comm hVab hw hv
      exact hsub hmem
    have hne0 : (C ⊔ V).relIndex P ≠ 0 := by
      intro h0
      have r2 := Subgroup.relIndex_mul_card (C ⊔ V) P
      rw [h0, zero_mul] at r2
      exact Nat.card_pos.ne' r2.symm
    omega
  calc 32 = 16 * 2 := by norm_num
    _ ≤ C.relIndex (C ⊔ V) * (C ⊔ V).relIndex P := by rw [h16]; exact Nat.mul_le_mul_left _ hle2
    _ = C.relIndex P := Subgroup.relIndex_mul_relIndex C (C ⊔ V) P le_sup_left hCVle

variable {g : G} (hg : conjSub g S.V2 = S.W0)
include hg

theorem normalizer_W0_le_Xg_F4 :
    Subgroup.normalizer (S.W0 : Set G) ≤ Subgroup.normalizer (conjSub g S.L2 : Set G) := by
  intro h hh
  rw [← hg, conjSub_normalizer, mem_conjSub] at hh
  have hN := S.NV2_le_NX2_F4 h13315
  rw [S.X2_not_hat hhat] at hN
  rw [conjSub_normalizer, mem_conjSub]
  exact hN hh

theorem normalizer_W0_le_R_F4 :
    Subgroup.normalizer (S.W0 : Set G) ≤
      Subgroup.normalizer (conjSub g (pCoreOf 2 S.L2) : Set G) := by
  rw [← pCoreOf_conjSub]
  exact (S.normalizer_W0_le_Xg_F4 h13315 hhat hg).trans (normalizer_le_normalizer_pCoreOf 2 _)

theorem isPGroup_Xg_inf_C_F4 :
    IsPGroup 2 ↥(conjSub g S.L2 ⊓ Subgroup.centralizer (S.W0 : Set G)) := by
  rw [← hg, conjSub_centralizer, ← conjSub_inf]
  exact (S.isPGroup_L2_inf_C_F4 h13315 hhat).map _

theorem not_mem_C_W0_F4 {y : G} (hy : y ∈ conjSub g S.L2) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    y ∉ Subgroup.centralizer (S.W0 : Set G) := by
  intro hyC
  obtain ⟨k, hk⟩ := S.isPGroup_Xg_inf_C_F4 h13315 hhat hg ⟨y, hy, hyC⟩
  have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf y ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hk')
  have h2 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
  rw [h2, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact hy1 h1

theorem card_le_three_of_le_Xg_F4 {Y : Subgroup G} (hY : IsPGroup 3 Y)
    (hYX : Y ≤ conjSub g S.L2) : Nat.card Y ≤ 3 := by
  have h1 := relIndex_inf_centralizer_le_three S.card_W0
    (hYX.trans (S.Xg_le_NW0 hg)) hY
  have hbot : Y ⊓ Subgroup.centralizer (S.W0 : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨a, ha⟩ := hY ⟨y, hy.1⟩
    obtain ⟨b, hb⟩ := S.isPGroup_Xg_inf_C_F4 h13315 hhat hg ⟨y, hYX hy.1, hy.2⟩
    have ha' : y ^ (3 ^ a) = 1 := by simpa using congrArg Subtype.val ha
    have hb' : y ^ (2 ^ b) = 1 := by simpa using congrArg Subtype.val hb
    have h2 : orderOf y ∣ Nat.gcd (3 ^ a) (2 ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha') (orderOf_dvd_of_pow_eq_one hb')
    have h3 : Nat.gcd (3 ^ a) (2 ^ b) = 1 :=
      Nat.Coprime.pow _ _ (by decide : Nat.Coprime 3 2)
    rw [h3, Nat.dvd_one, orderOf_eq_one_iff] at h2
    exact Subgroup.mem_bot.2 h2
  have hc1 : Nat.card ↥(Y ⊓ Subgroup.centralizer (S.W0 : Set G)) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have r := Subgroup.relIndex_mul_card (Y ⊓ Subgroup.centralizer (S.W0 : Set G)) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ Subgroup.centralizer (S.W0 : Set G) ≤ Y), hc1,
    mul_one] at r
  omega

omit hhat in

theorem false_of_elem27_F4 {E : Subgroup G} (hE : IsElemAbelian 3 E) (h27 : Nat.card E = 27)
    (hEN : E ≤ Subgroup.normalizer (S.W0 : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, hm3, -⟩ := h13315 G T L V S.V2 S.X2 _ S.h13 S.irr S.zv S.isV2
    S.not_iso_a5 S.X2_hat S.X2_not_hat rfl
  have hEp : IsPGroup 3 E := by
    rintro ⟨e, he⟩
    exact ⟨1, Subtype.ext (by simpa using hE.2 e he)⟩
  have h1 := relIndex_inf_centralizer_le_three S.card_W0 hEN hEp
  set E' := E ⊓ Subgroup.centralizer (S.W0 : Set G) with hE'
  have r := Subgroup.relIndex_mul_card E' E
  rw [inf_eq_left.2 (inf_le_left : E' ≤ E), h27] at r
  have h9 : 9 ≤ Nat.card E' := by nlinarith

  set F := conjSub g⁻¹ E' with hF
  have hFC : F ≤ Subgroup.centralizer (S.V2 : Set G) := by
    have : E' ≤ conjSub g (Subgroup.centralizer (S.V2 : Set G)) := by
      rw [← conjSub_centralizer, hg]; exact inf_le_right
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have := this hx
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  have hcardF : Nat.card F = Nat.card E' := CosetGeom.card_conjSub _ _
  have hFp : IsPGroup 3 F := (hEp.to_le inf_le_left).map _
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hFp
  have h9d : 3 ^ 2 ∣ Nat.card F := by
    rw [hj]
    refine pow_dvd_pow 3 ?_
    by_contra h
    push Not at h
    have : 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F₂, hF₂⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9d
  set F₉ := F₂.map F.subtype with hF₉
  have hF₉card : Nat.card F₉ = 3 ^ 2 := by
    rw [hF₉, ← hF₂]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ F.subtype_injective).toEquiv.symm
  have hF₉le : F₉ ≤ F := Subgroup.map_subtype_le _
  have hFab : IsElemAbelian 3 F₉ := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have ha := hF₉le a.2
      have hb := hF₉le b.2
      rw [mem_conjSub, inv_inv] at ha hb
      have hc := isElemAbelian_comm hE ha.1 hb.1
      show (a : G) * b = b * a
      calc (a : G) * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [hc]
        _ = b * a := by group
    · have hx' := hF₉le hx
      rw [mem_conjSub, inv_inv] at hx'
      have h3 := hE.2 _ hx'.1
      have h4 : g * x ^ 3 * g⁻¹ = 1 := by rw [← conj_pow]; exact h3
      calc x ^ 3 = g⁻¹ * (g * x ^ 3 * g⁻¹) * g := by group
        _ = 1 := by rw [h4]; group
  set C := Subgroup.centralizer (S.V2 : Set G) with hC
  set A : Subgroup ↥C := F₉.subgroupOf C with hA
  have hAcard : Nat.card A = 3 ^ 2 := by
    rw [hA, ← hF₉card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hF₉le.trans hFC)).toEquiv
  have hAel : IsElementaryAbelian 3 ↥A := by
    refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
    · have := hFab.1.is_comm.comm ⟨((a : ↥C) : G), a.2⟩ ⟨((b : ↥C) : G), b.2⟩
      apply Subtype.ext
      apply Subtype.ext
      show ((a : ↥C) : G) * ((b : ↥C) : G) = ((b : ↥C) : G) * ((a : ↥C) : G)
      exact congrArg (fun x : ↥F₉ => (x : G)) this
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (Subtype.ext ?_)
      simpa using hFab.2 ((a : ↥C) : G) a.2
  have hrank : 2 ≤ pRank 3 ↥C := by
    refine le_csSup ⟨Nat.card ↥C, fun k hk => ?_⟩ ⟨A, hAel, hAcard⟩
    obtain ⟨D, -, hDk⟩ := hk
    have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card D ≤ Nat.card ↥C := Subgroup.card_le_card_group D
    omega
  omega

theorem exists_y_F4 (hS6 : ¬ autOn T V ≤ autOn L V) (h6 : CFSG.Quasithin.IsAltBlockType L 6) :
    ∃ y : ↥(Subgroup.normalizer (V : Set G)), (y : G) ∈ L ∧ (y : G) ∈ conjSub g S.L2 ∧
      (y : G) ^ 3 = 1 ∧ (S.frame.ρ y = tri012 ∨ S.frame.ρ y = tri012 * tri012) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hPL, hPN, hPcard, hPab, hPρ⟩ := S.exists_P9 h6
  set X := conjSub g S.L2 with hX
  have hPW : P ≤ Subgroup.normalizer (S.W0 : Set G) := fun p hp =>
    S.mem_normalizer_W0_of (h := ⟨p, hPN hp⟩) (e9L_facts _ (hPρ ⟨p, hPN hp⟩ hp)).2.2
  have hPX : P ≤ Subgroup.normalizer (X : Set G) := hPW.trans (S.normalizer_W0_le_Xg_F4 h13315 hhat hg)

  obtain ⟨y, hyP, hyX, hy1⟩ : ∃ y ∈ P, y ∈ X ∧ y ≠ 1 := by
    by_contra hall
    push Not at hall
    have hinf : P ⊓ X = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.2 (hall y hy.1 hy.2)

    obtain ⟨a, haL, ⟨m, hm, ham⟩, ha⟩ := S.exists_L_odd s024_facts.2.1 s024_facts.1
    have hstab2 : ∀ σ : Perm (Fin 6), StabW2 σ → StabW2 (σ * σ) := fun σ h y hy => by
      rw [act4f_mul]; exact h _ (h y hy)
    have haN : (a : G) ∈ Subgroup.normalizer (S.V2 : Set G) := by
      refine S.mem_normalizer_V2_of ?_
      rcases ha with h | h <;> rw [h]
      · exact stabW2_s024
      · exact hstab2 _ stabW2_s024
    have ham' : (a : G) ^ m = 1 := by simpa using congrArg Subtype.val ham
    have haL2 := S.mem_L2_of_odd haL haN hm ham'
    have h3a : 3 ∣ orderOf (a : G) := by
      have h1 : orderOf (S.frame.ρ a) = 3 := by
        refine orderOf_eq_prime ?_ ?_
        · rcases ha with h | h <;> rw [h]
          · exact s024_facts.1
          · rw [← sq, ← pow_mul, mul_comm, pow_mul, s024_facts.1, one_pow]
        · rcases ha with h | h <;> rw [h] <;> decide
      have h2 := orderOf_map_dvd S.frame.ρ a
      rw [h1] at h2
      have h3 : orderOf a = orderOf (a : G) := (Subgroup.orderOf_coe a).symm
      rw [h3] at h2
      exact h2
    have h3X : 3 ∣ Nat.card X := by
      rw [hX, CosetGeom.card_conjSub]
      exact h3a.trans (Subgroup.orderOf_dvd_natCard _ haL2)

    set K := P ⊔ X with hK
    have hKX : K ≤ Subgroup.normalizer (X : Set G) := sup_le hPX Subgroup.le_normalizer
    have hcK := card_sup_mul_card_inf' hPX
    rw [hinf, Subgroup.card_bot, mul_one, hPcard] at hcK
    have h27 : 3 ^ (2 + 1) ∣ Nat.card K := by
      rw [hcK]
      obtain ⟨c, hc⟩ := h3X
      rw [hc]
      exact ⟨c, by ring⟩
    have hPK : Nat.card (P.subgroupOf K) = 3 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hPcard]; norm_num
    obtain ⟨S', hS'card, hS'P⟩ := Sylow.exists_subgroup_card_pow_succ h27 hPK
    set S₀ := S'.map K.subtype with hS₀
    have hS₀K : S₀ ≤ K := Subgroup.map_subtype_le _
    have hS₀card : Nat.card S₀ = 27 := by
      rw [hS₀, show (27 : ℕ) = 3 ^ (2 + 1) by norm_num, ← hS'card]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ K.subtype_injective).toEquiv.symm
    have hPS₀ : P ≤ S₀ := by
      intro p hp
      exact ⟨⟨p, (le_sup_left : P ≤ P ⊔ X) hp⟩,
        hS'P (by simpa [Subgroup.mem_subgroupOf] using hp), rfl⟩
    have hS₀p : IsPGroup 3 S₀ := IsPGroup.of_card (hS₀card.trans (by norm_num : (27 : ℕ) = 3 ^ 3))
    have hY3 : Nat.card ↥(S₀ ⊓ X) ≤ 3 :=
      S.card_le_three_of_le_Xg_F4 h13315 hhat hg (hS₀p.to_le inf_le_left) inf_le_right
    have hcS := card_sup_mul_card_inf' (hS₀K.trans hKX)
    have hle : Nat.card ↥(S₀ ⊔ X) ≤ Nat.card K :=
      Subgroup.card_le_of_le (sup_le hS₀K le_sup_right)
    rw [hS₀card] at hcS
    have hXpos : 0 < Nat.card X := Nat.card_pos
    have hge : 3 ≤ Nat.card ↥(S₀ ⊓ X) := by nlinarith
    have hY3' : Nat.card ↥(S₀ ⊓ X) = 3 := le_antisymm hY3 hge

    obtain ⟨y₀, hy₀, hy₀1⟩ : ∃ y₀ ∈ S₀ ⊓ X, y₀ ≠ 1 := by
      by_contra h
      push Not at h
      have : S₀ ⊓ X = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
      rw [this, Subgroup.card_bot] at hY3'
      omega
    have hy₀3 : y₀ ^ 3 = 1 := by
      have := orderOf_dvd_natCard (⟨y₀, hy₀⟩ : ↥(S₀ ⊓ X))
      rw [hY3', Subgroup.orderOf_mk] at this
      exact orderOf_dvd_iff_pow_eq_one.1 this
    have hord : orderOf y₀ = 3 := orderOf_eq_prime hy₀3 hy₀1
    have hZ : Subgroup.zpowers y₀ = S₀ ⊓ X := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le]; exact hy₀
      · rw [hY3', Nat.card_zpowers, hord]
    have hy₀P : y₀ ∉ P := fun h => hy₀1 (hall y₀ h hy₀.2)

    have hcent : ∀ p ∈ P, p * y₀ = y₀ * p := by
      intro p hp
      have hc : p * y₀ * p⁻¹ ∈ Subgroup.zpowers y₀ := by
        rw [hZ]
        exact ⟨S₀.mul_mem (S₀.mul_mem (hPS₀ hp) hy₀.1) (S₀.inv_mem (hPS₀ hp)),
          (Subgroup.mem_normalizer_iff.mp (hPX hp) y₀).mp hy₀.2⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      rw [← zpow_mod_orderOf, hord] at hk
      have hk3 : (k % (3 : ℕ) : ℤ) = 0 ∨ (k % (3 : ℕ) : ℤ) = 1 ∨ (k % (3 : ℕ) : ℤ) = 2 := by
        omega
      have hp3 : p ^ 3 = 1 := hPab.2 p hp
      rcases hk3 with h | h | h <;> rw [h] at hk
      · exfalso
        rw [zpow_zero] at hk
        apply hy₀1
        have : p * y₀ * p⁻¹ = 1 := hk.symm
        calc y₀ = p⁻¹ * (p * y₀ * p⁻¹) * p := by group
          _ = 1 := by rw [this]; group
      · rw [zpow_one] at hk
        calc p * y₀ = p * y₀ * p⁻¹ * p := by group
          _ = y₀ * p := by rw [← hk]
      · exfalso
        have e1 : p * y₀ * p⁻¹ = y₀ * y₀ := by rw [← hk]; rw [zpow_two]
        have e2 : p ^ 3 * y₀ * (p ^ 3)⁻¹ = y₀ * y₀ := by
          have h2 : p * (y₀ * y₀) * p⁻¹ = (p * y₀ * p⁻¹) * (p * y₀ * p⁻¹) := by group
          have h3 : p * (y₀ * y₀ * y₀ * y₀) * p⁻¹ =
              (p * (y₀ * y₀) * p⁻¹) * (p * (y₀ * y₀) * p⁻¹) := by group
          have h4 : y₀ * y₀ * y₀ * y₀ = y₀ := by
            rw [show y₀ * y₀ * y₀ = y₀ ^ 3 by rw [pow_succ, pow_succ, pow_one], hy₀3, one_mul]
          rw [show p ^ 3 = p * p * p by rw [pow_succ, pow_succ, pow_one]]
          calc p * p * p * y₀ * (p * p * p)⁻¹ = p * (p * (p * y₀ * p⁻¹) * p⁻¹) * p⁻¹ := by group
            _ = p * (p * (y₀ * y₀) * p⁻¹) * p⁻¹ := by rw [e1]
            _ = p * ((p * y₀ * p⁻¹) * (p * y₀ * p⁻¹)) * p⁻¹ := by rw [h2]
            _ = p * (y₀ * y₀ * (y₀ * y₀)) * p⁻¹ := by rw [e1]
            _ = p * (y₀ * y₀ * y₀ * y₀) * p⁻¹ := by group
            _ = p * y₀ * p⁻¹ := by rw [h4]
            _ = y₀ * y₀ := e1
        rw [hp3, one_mul, inv_one, mul_one] at e2
        apply hy₀1
        calc y₀ = y₀⁻¹ * (y₀ * y₀) := by group
          _ = y₀⁻¹ * y₀ := by rw [← e2]
          _ = 1 := by group

    obtain ⟨hE, hEcard⟩ := elem_sup_zpowers hPab hcent hy₀3 hy₀P
    refine S.false_of_elem27_F4 h13315 hg hE (by rw [hEcard, hPcard]) ?_
    refine sup_le hPW ?_
    rw [Subgroup.zpowers_le]
    exact S.Xg_le_NW0 hg hy₀.2

  set yN : ↥(Subgroup.normalizer (V : Set G)) := ⟨y, hPN hyP⟩ with hyNdef
  have hy3 : y ^ 3 = 1 := hPab.2 y hyP
  have hρy := hPρ yN hyP
  obtain ⟨h₁, h₁LT, hρh₁⟩ := S.exists_LT_rho hS6 (swap 0 1)
  have hh₁W : (h₁ : G) ∈ Subgroup.normalizer (S.W0 : Set G) :=
    S.mem_normalizer_W0_of (by rw [hρh₁]; exact stabW0_of _ fix345_swaps.1)
  set w : ↥(Subgroup.normalizer (V : Set G)) := yN * (h₁ * yN * h₁⁻¹) with hwdef
  have hwX : (w : G) ∈ X := by
    have h1 : (h₁ : G) * y * (h₁ : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (S.normalizer_W0_le_Xg_F4 h13315 hhat hg hh₁W) y).mp hyX
    exact X.mul_mem hyX h1
  have hρw : S.frame.ρ w = S.frame.ρ yN * (swap 0 1 * S.frame.ρ yN * swap 0 1) := by
    rw [hwdef, map_mul, map_mul, map_mul, map_inv, hρh₁, swap_inv]
  obtain ⟨hw3, hwfix, hw1⟩ := e9L_twist _ hρy
  rw [← hρw] at hw3 hwfix hw1
  have hρw1 : S.frame.ρ w = 1 := by
    by_contra hne
    have hwC : (w : G) ∈ Subgroup.centralizer (S.W0 : Set G) :=
      S.mem_centralizer_pre_of_fix w fun z hz => hwfix _ hz
    obtain ⟨k, hk⟩ := S.isPGroup_Xg_inf_C_F4 h13315 hhat hg ⟨w, hwX, hwC⟩
    have hk' : w ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : (S.frame.ρ w) ^ (2 ^ k) = 1 := by rw [← map_pow, hk', map_one]
    have h3 : orderOf (S.frame.ρ w) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw3) (orderOf_dvd_of_pow_eq_one h2)
    have h4 : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 2)
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact hne h3
  rcases hw1 hρw1 with h | h | h
  · exfalso
    have hyC : y ∈ Subgroup.centralizer (S.W0 : Set G) := by
      have := (S.rho_eq_one_iff yN).1 h
      exact Subgroup.centralizer_le (S.W0_le_V) this
    exact S.not_mem_C_W0_F4 h13315 hhat hg hyX hy3 hy1 hyC
  · exact ⟨yN, hPL hyP, hyX, hy3, Or.inl h⟩
  · exact ⟨yN, hPL hyP, hyX, hy3, Or.inr h⟩

theorem false_of_conj_W0_F4 (hS6 : ¬ autOn T V ≤ autOn L V) (hS : IsShort2 L)
    (h6 : CFSG.Quasithin.IsAltBlockType L 6) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, -, hc1, hc2⟩ := conj_c012
  obtain ⟨y, hyL, hyX, hy3, hρy⟩ := S.exists_y_F4 h13315 hhat hg hS6 h6
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have h' : y = 1 := Subtype.ext h
    rw [h', map_one] at hρy
    rcases hρy with h | h
    · exact hc1 h.symm
    · exact hc2 h.symm
  set Y := Subgroup.zpowers (y : G) with hYdef
  set R := conjSub g (pCoreOf 2 S.L2) with hRdef
  have hRp : IsPGroup 2 R := (pCoreOf_isPGroup 2 S.L2).map _
  have hRN : Subgroup.normalizer (S.W0 : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    S.normalizer_W0_le_R_F4 h13315 hhat hg
  have hyR : (y : G) ∈ Subgroup.normalizer (R : Set G) := hRN (S.Xg_le_NW0 hg hyX)

  have hν : 32 * Nat.card ↥(R ⊓ Subgroup.centralizer ({(y : G)} : Set G)) ≤ Nat.card R := by
    obtain ⟨x, hx⟩ : ∃ x : G, x = g⁻¹ * (y : G) * g := ⟨_, rfl⟩
    have hxL2 : x ∈ S.L2 := by
      have h1 := hyX
      rw [mem_conjSub] at h1
      rw [hx]; exact h1
    have hx3 : x ^ 3 = 1 := by
      have e : x ^ 3 = g⁻¹ * (y : G) ^ 3 * g := by
        rw [hx]; simp only [pow_succ, pow_zero, one_mul]; group
      rw [e, hy3]; group
    have hx1 : x ≠ 1 := by
      intro h
      apply hy1
      calc (y : G) = g * x * g⁻¹ := by rw [hx]; group
        _ = 1 := by rw [h]; group
    have h32 := S.relIndex_cent_O2L2_F4 h13315 hhat hxL2 hx3 hx1
    have hr := Subgroup.relIndex_mul_card (pCoreOf 2 S.L2 ⊓ Subgroup.centralizer ({x} : Set G))
      (pCoreOf 2 S.L2)
    rw [inf_eq_left.2 (inf_le_left :
      pCoreOf 2 S.L2 ⊓ Subgroup.centralizer ({x} : Set G) ≤ pCoreOf 2 S.L2)] at hr
    have e : conjSub g (pCoreOf 2 S.L2 ⊓ Subgroup.centralizer ({x} : Set G)) =
        R ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
      ext r
      rw [mem_conjSub, Subgroup.mem_inf, Subgroup.mem_inf, hRdef, mem_conjSub,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, hx]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        calc r * (y : G) = g * (g⁻¹ * r * g * (g⁻¹ * y * g)) * g⁻¹ := by group
          _ = g * (g⁻¹ * y * g * (g⁻¹ * r * g)) * g⁻¹ := by rw [h2]
          _ = y * r := by group
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        calc g⁻¹ * r * g * (g⁻¹ * y * g) = g⁻¹ * (r * y) * g := by group
          _ = g⁻¹ * (y * r) * g := by rw [h2]
          _ = g⁻¹ * y * g * (g⁻¹ * r * g) := by group
    have hc1' : Nat.card ↥(R ⊓ Subgroup.centralizer ({(y : G)} : Set G)) =
        Nat.card ↥(pCoreOf 2 S.L2 ⊓ Subgroup.centralizer ({x} : Set G)) := by
      rw [← e, CosetGeom.card_conjSub]
    have hc2' : Nat.card R = Nat.card (pCoreOf 2 S.L2) := CosetGeom.card_conjSub _ _
    rw [hc1', hc2', ← hr]
    exact Nat.mul_le_mul_right _ h32

  have hRY : ∀ r ∈ R, r ∈ Subgroup.normalizer (Y : Set G) →
      r ∈ Subgroup.centralizer ({(y : G)} : Set G) := by
    intro r hr hrY
    have h1 : r * y * r⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hrY y).mp (Subgroup.mem_zpowers _)
    obtain ⟨c, hc⟩ : ∃ c : G, c = r * (y : G) * r⁻¹ * (y : G)⁻¹ := ⟨_, rfl⟩
    have hcY : c ∈ Y := by rw [hc]; exact Y.mul_mem h1 (Y.inv_mem (Subgroup.mem_zpowers _))
    have hcR : c ∈ R := by
      have h2 : (y : G) * r⁻¹ * (y : G)⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hyR r⁻¹).mp (R.inv_mem hr)
      have e : c = r * ((y : G) * r⁻¹ * (y : G)⁻¹) := by rw [hc]; group
      rw [e]; exact R.mul_mem hr h2
    obtain ⟨k, hk⟩ := hRp ⟨c, hcR⟩
    have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hc1 := eq_one_of_pow_three_of_two (pow_three_of_mem_zpowers hy3 hcY) hk'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * (y : G) = c * (y * r) := by rw [hc]; group
      _ = y * r := by rw [hc1, one_mul]

  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  set CQ := Q ⊓ Subgroup.centralizer ({(y : G)} : Set G) with hCQdef
  have hcommW : ∀ q ∈ Q, q * y * q⁻¹ * (y : G)⁻¹ ∈ S.W0 := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hq.1
    have hρq : S.frame.ρ ⟨q, hqN⟩ = 1 := (S.rho_eq_one_iff _).2 hq.2
    have hwL : q * y * q⁻¹ * (y : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.T_le_NL hq.1) y).mp hyL) (L.inv_mem hyL)
    have hwC : q * y * q⁻¹ * (y : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have := (S.rho_eq_one_iff ((⟨q, hqN⟩ : ↥(Subgroup.normalizer (V : Set G))) * y *
        (⟨q, hqN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * y⁻¹)).1 (by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρq]; group)
      exact this
    have hw3 : (q * y * q⁻¹ * (y : G)⁻¹ * y) ^ 3 = 1 := by
      rw [inv_mul_cancel_right, conj_pow, hy3, mul_one, mul_inv_cancel]
    exact S.mem_W0_of_cube hS h6 (z := y) hyL hy3 hρy hwL hwC hw3
  have hQV : ∀ q ∈ Q, ∀ v ∈ V, q * v = v * q := fun q hq v hv =>
    (Subgroup.mem_centralizer_iff.mp hq.2 v hv).symm
  let φQ : ↥Q →* ↥S.W0 :=
    { toFun := fun q => ⟨(q : G) * y * (q : G)⁻¹ * (y : G)⁻¹, hcommW q q.2⟩
      map_one' := Subtype.ext (by
        show (1 : G) * y * (1 : G)⁻¹ * (y : G)⁻¹ = 1
        group)
      map_mul' := fun a b => Subtype.ext (by
        show ((a : G) * b) * y * ((a : G) * b)⁻¹ * (y : G)⁻¹ =
          ((a : G) * y * (a : G)⁻¹ * (y : G)⁻¹) * ((b : G) * y * (b : G)⁻¹ * (y : G)⁻¹)
        have hbV : (b : G) * y * (b : G)⁻¹ * (y : G)⁻¹ ∈ V := S.W0_le_V (hcommW b b.2)
        have haV : (a : G) * y * (a : G)⁻¹ * (y : G)⁻¹ ∈ V := S.W0_le_V (hcommW a a.2)
        have h1 := hQV a a.2 _ hbV
        have h2 := isElemAbelian_comm S.elemAbelian_V haV hbV
        calc ((a : G) * b) * y * ((a : G) * b)⁻¹ * (y : G)⁻¹ =
            ((a : G) * ((b : G) * y * (b : G)⁻¹ * (y : G)⁻¹)) *
              ((y : G) * (a : G)⁻¹ * (y : G)⁻¹) := by group
          _ = ((b : G) * y * (b : G)⁻¹ * (y : G)⁻¹) * (a : G) *
              ((y : G) * (a : G)⁻¹ * (y : G)⁻¹) := by rw [h1]
          _ = ((b : G) * y * (b : G)⁻¹ * (y : G)⁻¹) *
              ((a : G) * y * (a : G)⁻¹ * (y : G)⁻¹) := by group
          _ = _ := h2.symm) }
  have hQcard : Nat.card Q ≤ Nat.card CQ * 4 := by
    have h1 := card_le_card_inf_mul_card_range (A := Subgroup.centralizer ({(y : G)} : Set G))
      φQ (fun q hq => by
        have h : (q : G) * y * (q : G)⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (q : G) * y = ((q : G) * y * (q : G)⁻¹ * (y : G)⁻¹) * (y * q) := by group
          _ = y * q := by rw [h, one_mul])
    have h2 : Nat.card φQ.range ≤ 4 := by
      have := Subgroup.card_le_card_group φQ.range
      rwa [S.card_W0] at this
    calc Nat.card Q ≤ Nat.card CQ * Nat.card φQ.range := h1
      _ ≤ Nat.card CQ * 4 := Nat.mul_le_mul_left _ h2

  let ρT : ↥T →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion S.frame.T_le)
  have hTcard : Nat.card T ≤ Nat.card Q * 16 := by
    have h1 := card_le_card_inf_mul_card_range (A := Subgroup.centralizer (V : Set G)) ρT
      (fun t ht => (S.rho_eq_one_iff (Subgroup.inclusion S.frame.T_le t)).1 ht)
    have h2 : Nat.card ρT.range ≤ 16 := by
      have hmem : ∀ σ ∈ ρT.range, InD6 σ := by
        rintro _ ⟨t, rfl⟩
        exact S.frame.T_D (Subgroup.inclusion S.frame.T_le t) t.2
      have h16 : Nat.card {σ : Perm (Fin 6) // InD6 σ} = 16 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_D6]
      rw [← h16]
      exact Nat.card_le_card_of_injective
        (fun σ : ρT.range => (⟨σ.1, hmem σ.1 σ.2⟩ : {σ : Perm (Fin 6) // InD6 σ}))
        (fun a b h => Subtype.ext
          (congrArg (Subtype.val : {σ : Perm (Fin 6) // InD6 σ} → Perm (Fin 6)) h))
    calc Nat.card T ≤ Nat.card Q * Nat.card ρT.range := h1
      _ ≤ Nat.card Q * 16 := Nat.mul_le_mul_left _ h2

  set H₂ : Subgroup G := (L ⊔ T) ⊓
    (e4Sub.comap S.frame.ρ).map (Subgroup.normalizer (V : Set G)).subtype ⊓
      Subgroup.normalizer (Y : Set G) with hH₂def
  have hH₂N : H₂ ≤ Subgroup.normalizer (V : Set G) := fun h hh => by
    obtain ⟨n, -, hn⟩ := hh.1.2
    rw [← hn]; exact n.2
  have hH₂ρ : ∀ h (hh : h ∈ H₂), S.frame.ρ ⟨h, hH₂N hh⟩ ∈ e4L := by
    intro h hh
    obtain ⟨n, hn, hne⟩ := hh.1.2
    have e : n = ⟨h, hH₂N hh⟩ := Subtype.ext hne
    rw [← e]; exact hn
  have hH₂p : IsPGroup 2 H₂ := by
    rintro ⟨h, hh⟩
    have hm := hH₂ρ h hh
    have hρ2 : S.frame.ρ (⟨h, hH₂N hh⟩ ^ 2) = 1 := by rw [map_pow]; exact (e4L_facts _ hm).1
    have hC : h ^ 2 ∈ Subgroup.centralizer (V : Set G) := by
      have := (S.rho_eq_one_iff _).1 hρ2
      simpa using this
    obtain ⟨k, hk⟩ := S.isPGroup_LT_inf_C h6 ⟨h ^ 2, (L ⊔ T).pow_mem hh.1.1 2, hC⟩
    have hk' : (h ^ 2) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k + 1, Subtype.ext ?_⟩
    have e : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [SubmonoidClass.coe_pow, e, pow_mul]
    exact hk'
  have hH₂W : H₂ ≤ Subgroup.normalizer (S.W0 : Set G) := fun h hh =>
    S.mem_normalizer_W0_of (h := ⟨h, hH₂N hh⟩) (stabW0_of _ (e4L_facts _ (hH₂ρ h hh)).2)
  have hH₂R : H₂ ≤ Subgroup.normalizer (R : Set G) := hH₂W.trans hRN
  have hmemH₂ : ∀ n : ↥(Subgroup.normalizer (V : Set G)), (n : G) ∈ L ⊔ T →
      S.frame.ρ n ∈ e4L → (n : G) * y * (n : G)⁻¹ ∈ Y → (n : G) ∈ H₂ := by
    intro n hn hρn hny
    exact ⟨⟨hn, n, hρn, rfl⟩, mem_normalizer_zpowers_of hny⟩

  have hmemy : S.frame.ρ y ∈ [tri012, tri012 * tri012] := by
    rcases hρy with e | e <;> rw [e] <;> simp
  obtain ⟨hc01, hc34, hcsq⟩ := conj_c012_list _ hmemy
  obtain ⟨h₁, h₁LT, hρh₁⟩ := S.exists_LT_rho hS6 (swap 0 1)
  have hyy3 : ((y * y : ↥(Subgroup.normalizer (V : Set G))) : G) ^ 3 = 1 := by
    have e : ((y : G) * y) ^ 3 = (y : G) ^ 3 * (y : G) ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul]; group
    show ((y : G) * y) ^ 3 = 1
    rw [e, hy3, one_mul]
  have hρyy : S.frame.ρ (y * y) = tri012 ∨ S.frame.ρ (y * y) = tri012 * tri012 := by
    rw [map_mul]; exact hcsq
  obtain ⟨n₁, hn₁LT, hρn₁, hn₁y⟩ := S.exists_conj_eq hS h6 (z := y) (z' := y * y) hyL
    (L.mul_mem hyL hyL) hy3 hyy3 hρyy h₁LT (by rw [hρh₁, map_mul]; exact hc01)
  obtain ⟨h₂, h₂LT, hρh₂⟩ := S.exists_LT_rho hS6 (swap 3 4)
  obtain ⟨n₂, hn₂LT, hρn₂, hn₂y⟩ := S.exists_conj_eq hS h6 (z := y) (z' := y) hyL hyL hy3 hy3
    hρy h₂LT (by rw [hρh₂]; exact hc34)
  rw [hρh₁] at hρn₁
  rw [hρh₂] at hρn₂
  have hn₁H : (n₁ : G) ∈ H₂ := hmemH₂ n₁ hn₁LT (by rw [hρn₁]; decide)
    (by rw [hn₁y]; exact Y.mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _))
  have hn₂H : (n₂ : G) ∈ H₂ := hmemH₂ n₂ hn₂LT (by rw [hρn₂]; decide)
    (by rw [hn₂y]; exact Subgroup.mem_zpowers _)
  have hCQH : CQ ≤ H₂ := by
    intro q hq
    have hqN : q ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le hq.1.1
    have hρq : S.frame.ρ ⟨q, hqN⟩ = 1 := (S.rho_eq_one_iff _).2 hq.1.2
    refine hmemH₂ ⟨q, hqN⟩ (Subgroup.mem_sup_right hq.1.1) (by rw [hρq]; decide) ?_
    have hqy : q * (y : G) = y * q := Subgroup.mem_centralizer_singleton_iff.mp hq.2
    show q * (y : G) * q⁻¹ ∈ Y
    rw [hqy, mul_inv_cancel_right]
    exact Subgroup.mem_zpowers _

  let ρH : ↥H₂ →* Perm (Fin 6) := S.frame.ρ.comp (Subgroup.inclusion hH₂N)
  have e1 : ρH ⟨n₁, hn₁H⟩ = swap 0 1 := by
    show S.frame.ρ (Subgroup.inclusion hH₂N ⟨n₁, hn₁H⟩) = swap 0 1
    rw [show Subgroup.inclusion hH₂N ⟨(n₁ : G), hn₁H⟩ = n₁ from Subtype.ext rfl, hρn₁]
  have e2 : ρH ⟨n₂, hn₂H⟩ = swap 3 4 := by
    show S.frame.ρ (Subgroup.inclusion hH₂N ⟨n₂, hn₂H⟩) = swap 3 4
    rw [show Subgroup.inclusion hH₂N ⟨(n₂ : G), hn₂H⟩ = n₂ from Subtype.ext rfl, hρn₂]
  have hH₂card : Nat.card CQ * 4 ≤ Nat.card H₂ := by
    have h1 := card_mul_card_range_le ρH hCQH
      (fun a ha => (S.rho_eq_one_iff (Subgroup.inclusion hH₂N ⟨a, hCQH ha⟩)).2 ha.1.2)
    have h2 : 4 ≤ Nat.card ρH.range := by
      rw [← card_e4Sub]
      refine Subgroup.card_le_of_le fun σ hσ => ?_
      have hσ' : σ ∈ e4L := hσ
      simp only [e4L, List.mem_cons, List.mem_nil_iff, or_false] at hσ'
      rcases hσ' with rfl | rfl | rfl | rfl
      · exact ρH.range.one_mem
      · exact ⟨⟨n₁, hn₁H⟩, e1⟩
      · exact ⟨⟨n₂, hn₂H⟩, e2⟩
      · exact ⟨⟨n₁, hn₁H⟩ * ⟨n₂, hn₂H⟩, by rw [map_mul, e1, e2]⟩
    calc Nat.card CQ * 4 ≤ Nat.card CQ * Nat.card ρH.range := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card H₂ := h1

  have hsup := card_sup_mul_card_inf' hH₂R
  have hinf : Nat.card ↥(H₂ ⊓ R) ≤
      Nat.card ↥(R ⊓ Subgroup.centralizer ({(y : G)} : Set G)) :=
    Subgroup.card_le_of_le fun r hr => ⟨hr.2, hRY r hr.2 hr.1.2⟩
  have hT2 : Nat.card ↥(H₂ ⊔ R) ≤ Nat.card T :=
    card_le_of_isPGroup_two S.h13.sylow (hH₂p.to_sup_of_normal_right' hRp hH₂R)
  have hpos1 : 0 < Nat.card ↥(H₂ ⊓ R) := Nat.card_pos
  have hpos2 : 0 < Nat.card CQ := Nat.card_pos
  have h1 : 32 * Nat.card H₂ * Nat.card ↥(H₂ ⊓ R) ≤
      Nat.card ↥(H₂ ⊔ R) * Nat.card ↥(H₂ ⊓ R) := by
    rw [hsup]
    calc 32 * Nat.card H₂ * Nat.card ↥(H₂ ⊓ R) ≤
        32 * Nat.card H₂ * Nat.card ↥(R ⊓ Subgroup.centralizer ({(y : G)} : Set G)) :=
          Nat.mul_le_mul_left _ hinf
      _ = Nat.card H₂ * (32 * Nat.card ↥(R ⊓ Subgroup.centralizer ({(y : G)} : Set G))) := by
          ring
      _ ≤ Nat.card H₂ * Nat.card R := Nat.mul_le_mul_left _ hν
  have h2 := Nat.le_of_mul_le_mul_right h1 hpos1
  omega

end L2

end Setting4

theorem input1356TwoS6Block_of_F4 (h13315 : Stmt13_3_15_F4) : Input1356TwoS6Block_F4 := by
  intro G _ _ T L V S _ hS6 hblk h6 g hg
  exact S.false_of_conj_W0_F4 h13315 (not_isHatA6_of_block h6) hg hS6 hblk.1 h6

end CFSG.Quasithin.H13.A6
