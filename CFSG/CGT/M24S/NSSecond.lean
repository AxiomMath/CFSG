module

public import CFSG.CGT.M24S.NSSecondW
public import CFSG.CGT.M24S.NaturalSL
public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting

public section

namespace CFSG.CGT.M24S.NSSecond

open CFSG.CGT.Timmesfeld75 Matrix GL4
open scoped MatrixGroups

variable {G : Type} [Group G] {T H : Subgroup G} {z : G}

theorem mat_pow (c : NatCoord T H z) {x : G} (hx : x ∈ H) (n : ℕ) :
    c.mat (x ^ n) = c.mat x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, c.mat_one]
  | succ n ih => rw [pow_succ, c.mat_mul (H.pow_mem hx n) hx, ih, pow_succ]

theorem exists_lift [Finite G] {c : NatCoord T H z} {W : Subgroup G} {w : Fin 3 → G}
    (hS : SecondData c W w) {τ : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hτ : τ * τ = 1)
    (hτe : τ *ᵥ e0 = e0) :
    ∃ a ∈ H ⊓ Subgroup.centralizer ({z} : Set G),
      a ∈ Subgroup.normalizer (span3 w : Set G) ∧ c.mat a = τ := by
  obtain ⟨g, hg, hgm⟩ := c.exists_mat_eq τ (det_eq_one_of_mul_self' hτ)
  have hgK : g ∈ H ⊓ Subgroup.centralizer ({z} : Set G) :=
    ⟨hg, (c.mem_centralizer_iff hg).2 (by rw [hgm]; exact hτe)⟩
  obtain ⟨s, hs, hsN⟩ := exists_mul_mem_normalizer hS hgK
  refine ⟨s * g, mul_mem (c.E_le (c.T_le_E hs)) hgK, hsN, ?_⟩
  rw [c.mat_mul (c.le hs) hg, (c.mat_eq_one_iff (c.le hs)).2 hs, Matrix.one_mul, hgm]

theorem exists_sylow_complement [Finite G] {c : NatCoord T H z} {W : Subgroup G}
    {w : Fin 3 → G} (hS : SecondData c W w) :
    ∃ Q : Subgroup G, Q ≤ H ∧ Nat.card Q = 64 ∧ T ⊓ Q = ⊥ := by
  obtain ⟨a, haK, haN, ham⟩ := exists_lift hS tauA_mul_self liftData_tauA.1
  obtain ⟨b, hbK, hbN, hbm⟩ := exists_lift hS tauB_mul_self liftData_tauB.1
  have ha2 : a * a = 1 := mul_self_eq_one_of_liftData hS liftData_tauA haK haN ham
  have hb2 : b * b = 1 := mul_self_eq_one_of_liftData hS liftData_tauB hbK hbN hbm
  have hrK : a * b ∈ H ⊓ Subgroup.centralizer ({z} : Set G) := mul_mem haK hbK
  have hrN : a * b ∈ Subgroup.normalizer (span3 w : Set G) := mul_mem haN hbN
  have hrm : c.mat (a * b) = tauA * tauB := by rw [c.mat_mul haK.1 hbK.1, ham, hbm]
  have hr4 : (a * b) ^ 4 = 1 := by
    have h := mul_self_eq_one_of_liftData hS liftData_tauC (mul_mem hrK hrK) (mul_mem hrN hrN)
      (by rw [c.mat_mul hrK.1 hrK.1, hrm, tauA_mul_tauB_sq])
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    exact h
  have hDN : Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a ≤
      Subgroup.normalizer (span3 w : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hrN) (Subgroup.zpowers_le.2 haN)
  have hW₀H : span3 w ≤ H := (span3_le hS.mem).trans (hS.le_E.trans (c.E_le.trans inf_le_left))
  have hQH : span3 w ⊔ (Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a) ≤ H :=
    sup_le hW₀H (sup_le (Subgroup.zpowers_le.2 hrK.1) (Subgroup.zpowers_le.2 haK.1))
  set Q : Subgroup G := span3 w ⊔ (Subgroup.zpowers (a * b) ⊔ Subgroup.zpowers a) with hQ
  have hQle : Nat.card Q ≤ 64 :=
    (card_sup_le_of_le_normalizer hDN).trans
      (Nat.mul_le_mul (card_span3_le' hS) (card_dihedral_le ha2 hb2 hr4))
  choose u hu hut using exists_mem_span3_top_eq hS
  have hdQ : ∀ p : Fin 4 × Fin 2, (a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ) ∈ Q := fun p =>
    Subgroup.mem_sup_right (mul_mem
      (pow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) _)
      (pow_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _))
  have hdm : ∀ p : Fin 4 × Fin 2,
      c.mat ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ)) = dihedralMat p := fun p => by
    rw [c.mat_mul (H.pow_mem hrK.1 _) (H.pow_mem haK.1 _), mat_pow c hrK.1, mat_pow c haK.1,
      hrm, ham]
    rfl
  have huQ : ∀ x, u x ∈ Q := fun x => Subgroup.mem_sup_left (hu x)
  have hum : ∀ x, c.mat (u x) = mk4 x 1 := fun x => by
    rw [c.mat_eq_mk4_of_mem_E (hS.le_E (span3_le hS.mem (hu x))), hut]
  have hinj : ∀ x x' (p p' : Fin 4 × Fin 2),
      c.mat (u x * ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ))) =
        c.mat (u x' * ((a * b) ^ (p'.1 : ℕ) * a ^ (p'.2 : ℕ))) → x = x' ∧ p = p' := by
    intro x x' p p' h
    rw [c.mat_mul (hQH (huQ x)) (hQH (hdQ p)), c.mat_mul (hQH (huQ x')) (hQH (hdQ p'))] at h
    have hp : p = p' := by
      have h1 := congrArg blk h
      rw [hum, hum, hdm, hdm, blk_mul _ _ (mk4_mulVec_e0 _ _), blk_mul _ _ (mk4_mulVec_e0 _ _),
        blk_mk4, blk_mk4, Matrix.one_mul, Matrix.one_mul] at h1
      exact blk_dihedralMat_injective p p' h1
    subst hp
    refine ⟨?_, rfl⟩
    have hdH := hQH (hdQ p)
    have h2 : c.mat (u x) = c.mat (u x') := by
      calc c.mat (u x) = c.mat (u x) * c.mat ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ)) *
            c.mat ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ))⁻¹ := by
            rw [Matrix.mul_assoc, c.mat_mul_inv hdH, Matrix.mul_one]
        _ = c.mat (u x') * c.mat ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ)) *
            c.mat ((a * b) ^ (p.1 : ℕ) * a ^ (p.2 : ℕ))⁻¹ := by rw [h]
        _ = c.mat (u x') := by rw [Matrix.mul_assoc, c.mat_mul_inv hdH, Matrix.mul_one]
    calc x = top (c.mat (u x)) := (hut x).symm
      _ = top (c.mat (u x')) := by rw [h2]
      _ = x' := hut x'
  let f : Q →* SL(4, ZMod 2) := c.ρ.comp (Subgroup.inclusion hQH)
  have hf : ∀ y : Q, ((f y : SL(4, ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = c.mat y :=
    fun y => (c.mat_of_mem (hQH y.2)).symm
  let Φ : (Fin 3 → ZMod 2) × (Fin 4 × Fin 2) → f.range := fun q =>
    ⟨f ⟨u q.1 * ((a * b) ^ (q.2.1 : ℕ) * a ^ (q.2.2 : ℕ)), mul_mem (huQ q.1) (hdQ q.2)⟩,
      ⟨_, rfl⟩⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨x, p⟩ ⟨x', p'⟩ h
    have h1 := congrArg (fun y : f.range => ((y : SL(4, ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2))) h
    simp only [Φ, hf] at h1
    obtain ⟨rfl, rfl⟩ := hinj x x' p p' h1
    rfl
  have hr : 64 ≤ Nat.card f.range := by
    have := Nat.card_le_card_of_injective Φ hΦ
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin,
      Nat.card_fin, Nat.card_fin] at this
    calc 64 = 2 ^ 3 * (4 * 2) := by norm_num
      _ ≤ Nat.card f.range := this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hcard
  have hk1 : Nat.card f.ker = 1 := by
    have h1 : 64 * Nat.card f.ker ≤ 64 :=
      (Nat.mul_le_mul_right _ hr).trans (hcard ▸ hQle)
    have h2 : 0 < Nat.card f.ker := Nat.card_pos
    omega
  rw [hk1, mul_one] at hcard
  refine ⟨Q, hQH, by omega, ?_⟩
  rw [eq_bot_iff]
  intro y hy
  have hker : (⟨y, hy.2⟩ : Q) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact (c.ker_iff ⟨y, hQH hy.2⟩).2 hy.1
  rw [Subgroup.card_eq_one.1 hk1, Subgroup.mem_bot] at hker
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hker)

theorem hasComplement_of_card [Finite G] (hTH : T ≤ H) (hN : NaturalSL T H 4 1)
    {Q : Subgroup G} (hQH : Q ≤ H) (hQ : Nat.card Q = 64) (hTQ : T ⊓ Q = ⊥) :
    HasComplement T H := by
  have hn : (T.subgroupOf H).Normal := by
    obtain ⟨h, -⟩ := hN
    exact h
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 (le_centralizer_of_naturalSL hTH hN hb) a ha
  have : IsMulCommutative (T.subgroupOf H) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (hTc _ a.2 _ b.2))⟩⟩
  have hNK : T.subgroupOf H ⊓ Q.subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : (x : G) ∈ T ⊓ Q := ⟨hx.1, hx.2⟩
    rw [hTQ, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (Subtype.ext hx')
  have hcardN : Nat.card (T.subgroupOf H) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv, card_T_of_naturalSL hN]
  have hcardK : Nat.card (Q.subgroupOf H) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ]
  have hrel : (T.subgroupOf H).relIndex (T.subgroupOf H ⊔ Q.subgroupOf H) = 64 := by
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hNK,
      Subgroup.relIndex_bot_left, hcardK]
  have hcardNK : Nat.card (T.subgroupOf H ⊔ Q.subgroupOf H : Subgroup H) = 1024 := by
    have h := Subgroup.relIndex_mul_relIndex ⊥ (T.subgroupOf H)
      (T.subgroupOf H ⊔ Q.subgroupOf H) bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hcardN, hrel] at h
    omega
  have hidx : (T.subgroupOf H ⊔ Q.subgroupOf H).index = 315 := by
    have h := Subgroup.index_mul_card (T.subgroupOf H ⊔ Q.subgroupOf H)
    rw [hcardNK, card_H_of_naturalSL hTH hN] at h
    omega
  have hcop : Nat.Coprime (T.subgroupOf H ⊔ Q.subgroupOf H).index
      (Nat.card (T.subgroupOf H)) := by
    rw [hidx, hcardN]
    norm_num
  obtain ⟨D, -, hD1, hD2⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting
    (T.subgroupOf H) (T.subgroupOf H ⊔ Q.subgroupOf H) (Q.subgroupOf H) hcop hNK rfl
  refine ⟨D.map H.subtype, Subgroup.map_subtype_le D, ?_, ?_⟩
  · have h := congrArg (Subgroup.map H.subtype) hD1
    rwa [Subgroup.map_inf_eq _ _ _ H.subtype_injective, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hTH] at h
  · have h := congrArg (Subgroup.map H.subtype) hD2
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hTH,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

end CFSG.CGT.M24S.NSSecond

namespace CFSG.CGT.M24S

open CFSG.CGT.Timmesfeld75 NSSecond

theorem hasComplement_of_secondE16 {G : Type} [Group G] [Finite G] {T H : Subgroup G}
    (hTH : T ≤ H) (hN : NaturalSL T H 4 1) {t : G} (ht : t ∈ T) (ht1 : t ≠ 1) {W : Subgroup G}
    (hWK : W ≤ H ⊓ Subgroup.centralizer ({t} : Set G))
    (hWn : ∀ k ∈ H ⊓ Subgroup.centralizer ({t} : Set G), ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hW16 : Nat.card W = 16) (hWT : W ⊓ T = Subgroup.zpowers t)
    (hWc : ∀ w ∈ W, CentreTransvecting T t w) : HasComplement T H := by
  obtain ⟨c⟩ := nonempty_natCoord hTH hN ht ht1
  have hWE : W ≤ c.E := fun y hy => mem_E_of_centreTransvecting c (hWK hy) (hWc y hy)
  choose w hwW hwt using fun i : Fin 3 => exists_mem_top_eq c hWE hW16 hWT (Pi.single i 1)
  obtain ⟨Q, hQH, hQ, hTQ⟩ :=
    exists_sylow_complement (⟨hWE, hWn, hWab, hW2, hWT, hwW, hwt⟩ : SecondData c W w)
  exact hasComplement_of_card hTH hN hQH hQ hTQ

end CFSG.CGT.M24S
