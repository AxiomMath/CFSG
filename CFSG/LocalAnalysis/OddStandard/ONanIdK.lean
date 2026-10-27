module

public import CFSG.LocalAnalysis.OddStandard.ONanIdKSet
public import CFSG.LocalAnalysis.OddStandard.ONanIdInvert

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open scoped Pointwise

set_option maxRecDepth 100000 in
theorem jE_inv_d : ∀ e : AlpE, (jE⁻¹ * e).d = 0 → e.d = 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem mZ' : ∀ e : AlpE, e * y0E = y0E * e → InY0E (e * e) →
    (∀ g ∈ [gen 0, gen 1, gen 2, gen 3], InY0E ((g * e)⁻¹ * (e * g))) →
    InY0E e ∨ InY0E ((invE 1)⁻¹ * e) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mVjcent' : ∀ e : AlpE, (e.d = 0 ∨ (jE⁻¹ * e).d = 0) →
    InY0E ((e * gen 0 ^ 2)⁻¹ * (gen 0 ^ 2 * e)) ∧ InY0E ((e * gen 1 ^ 2)⁻¹ * (gen 1 ^ 2 * e)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem mbcent' : ∀ q : AlpE, q * y0E = y0E * q → InY0E ((q * invE 1)⁻¹ * (invE 1 * q)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem gen_comm_y0E : ∀ g ∈ [gen 0, gen 1, gen 2, gen 3], g * y0E = y0E * g := by
  decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

omit [Finite G] D in
theorem two_mul_card_le_of_lt {X : Type*} [Group X] [Finite X] {M T : Subgroup X} (hMT : M ≤ T)
    (hne : M ≠ T) : 2 * Nat.card M ≤ Nat.card T := by
  have h := relIndex_mul_card (H := M) (K := T)
  rw [inf_of_le_left hMT] at h
  have h1 : M.relIndex T ≠ 1 := fun h1 => hne (le_antisymm hMT (relIndex_eq_one.1 h1))
  have h0 : M.relIndex T ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact (Nat.card_pos (α := T)).ne' h.symm
  have h2 : 2 ≤ M.relIndex T := by omega
  rw [← h]
  exact Nat.mul_le_mul_right _ h2

theorem card_S1_ge : 32 ≤ Nat.card (liftQ (v1 * v3)
    (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3))) := by
  have H := D.invSettingK
  have hne : liftQ (v1 * v3) (alpV v1 v2 v3) ≠
      liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) := fun h =>
    H.jC (h ▸ H.jS)
  have := two_mul_card_le_of_lt H.CS hne
  rw [D.card_C] at this
  omega

omit [Finite G] D in
theorem πQ_comm_iff {y : G} (a b : centralizer ({y} : Set G)) :
    πQ y a * πQ y b = πQ y b * πQ y a ↔ ((a : G) * b)⁻¹ * (b * a) ∈ zpowers y := by
  rw [← map_mul, ← map_mul, πQ_eq_iff]
  rfl

theorem exists_phi_Vj {k : G} (hk : k ∈ alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) :
    ∃ e : AlpE, D.E.φ e = k ∧ (e.d = 0 ∨ (jE⁻¹ * e).d = 0) := by
  rcases (D.mem_Vj_iff).1 hk with h | h
  · obtain ⟨e, he, rfl⟩ := D.exists_phi_V h
    exact ⟨e, rfl, Or.inl he⟩
  · obtain ⟨e, he, he'⟩ := D.exists_phi_V h
    refine ⟨jE * e, ?_, Or.inr (by rw [inv_mul_cancel_left]; exact he)⟩
    rw [map_mul, he', ← D.j_eq, ← mul_assoc, D.rep_sq 3, one_mul]

theorem S1_le_centralizer_w {w : G} (hw : w = v1 ^ 2 ∨ w = v2 ^ 2)
    (hwY : w ∈ centralizer ({v1 * v3} : Set G)) :
    liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) ≤
      centralizer ({πQ (v1 * v3) ⟨w, hwY⟩} : Set (KQ (v1 * v3))) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
  rw [mem_centralizer_singleton_iff, πQ_comm_iff]
  obtain ⟨e, he, hd⟩ := D.exists_phi_Vj hk
  obtain ⟨h0, h1⟩ := mVjcent' e hd
  show ((k : G) * w)⁻¹ * (w * k) ∈ zpowers (v1 * v3)
  rcases hw with rfl | rfl
  · rw [← he, D.w3_eq, ← map_mul, ← map_mul, ← map_inv, ← map_mul, D.mem_Y0_iff]
    exact h0
  · have hv2 : v2 ^ 2 = D.E.φ (gen 1 ^ 2) := by rw [map_pow, AlpEmb.φ_v2]
    rw [← he, hv2, ← map_mul, ← map_mul, ← map_inv, ← map_mul, D.mem_Y0_iff]
    exact h1

theorem mem_S1_of_mem_Sb {x : KQ (v1 * v3)}
    (hx : x ∈ liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)))
    (hx2 : x * x = 1) :
    x ∈ liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) := by
  obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
  rw [← map_mul, πQ_eq_one_iff] at hx2
  obtain ⟨e, he⟩ := D.exists_phi_of_mem_P hk.1
  have hey : e * y0E = y0E * e := (D.comm_y0_phi e).1 (by
    rw [he]; exact mem_centralizer_singleton_iff.1 hk.2)
  have hee : InY0E (e * e) := by
    rw [← D.mem_Y0_iff, map_mul, he]
    exact hx2
  refine πQ_mem_liftQ ((D.mem_Vj_iff).2 ?_)
  rcases mQinv e hey hee with h | h
  · left
    rw [← he]
    exact (D.mem_V_phi e).2 h
  · right
    have hjinv : jE⁻¹ = jE := inv_eq_of_mul_eq_one_right jE_sq
    rw [hjinv] at h
    rw [← he, D.j_eq, ← map_mul]
    exact (D.mem_V_phi _).2 h

theorem gens_mem_Q : ∀ g ∈ [gen 0, gen 1, gen 2, gen 3],
    D.E.φ g ∈ alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) := fun g hg =>
  ⟨AlpEmb.φ_mem D.E g, mem_centralizer_singleton_iff.2 ((D.comm_y0_phi g).2 (gen_comm_y0E g hg))⟩

theorem isSylowOf_Sb_w {w : G} (hw : w = v1 ^ 2 ∨ w = v2 ^ 2)
    (hwY : w ∈ centralizer ({v1 * v3} : Set G)) :
    IsSylowOf 2 (liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) ⊓
      centralizer ({πQ (v1 * v3) ⟨w, hwY⟩} : Set (KQ (v1 * v3))))
      (centralizer ({πQ (v1 * v3) ⟨w, hwY⟩} : Set (KQ (v1 * v3)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Sb := liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({(v1 * v3)} : Set G)) with hSb
  set S1 := liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) with hS1
  set u := πQ (v1 * v3) ⟨w, hwY⟩ with hu
  set M := Sb ⊓ centralizer ({u} : Set (KQ (v1 * v3))) with hM
  have hw2 : w ∈ alpW v1 v2 v3 := by
    rcases hw with rfl | rfl <;> exact subset_closure (by simp)
  have hwV : w ∈ alpV v1 v2 v3 := D.W_le_V hw2
  have hwQ : w ∈ alpP v1 v2 v3 s t ⊓ centralizer ({(v1 * v3)} : Set G) := ⟨D.V_le_P hwV, hwY⟩
  have hS1M : S1 ≤ M := fun x hx => ⟨by
    obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
    obtain ⟨e, he, -⟩ := D.exists_phi_Vj hk
    exact πQ_mem_liftQ ⟨he ▸ AlpEmb.φ_mem D.E e, k.2⟩, D.S1_le_centralizer_w hw hwY hx⟩
  have hMp : IsPGroup 2 M := D.isSylowOf_Sb.isPGroup.to_le inf_le_left
  obtain ⟨T, hT, hMT⟩ := exists_isSylowOf_of_le' hMp inf_le_right
  by_cases hMT' : M = T
  · rw [hMT']; exact hT
  exfalso
  have hcardM : 32 ≤ Nat.card M := D.card_S1_ge.trans (Subgroup.card_le_of_le hS1M)
  have hcardT := two_mul_card_le_of_lt hMT hMT'
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_Sb le_top hT.isPGroup
  set T' := T.map (MulAut.conj c).toMonoidHom with hT'
  have hT'le : T' ≤ Sb := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hT'eq : T' = Sb := eq_of_le_of_card_ge hT'le (by
    rw [hT', card_map_of_injective (MulAut.conj c).injective, D.card_Sb]
    omega)
  have huT : u ∈ T := hMT ⟨πQ_mem_liftQ hwQ, mem_centralizer_singleton_iff.2 rfl⟩
  have hcent : ∀ q ∈ Sb, q * (c * u * c⁻¹) = c * u * c⁻¹ * q := by
    intro q hq
    rw [← hT'eq] at hq
    obtain ⟨t', ht', rfl⟩ := hq
    have htu : t' * u = u * t' := mem_centralizer_singleton_iff.1 (hT.le ht')
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * t' * c⁻¹ * (c * u * c⁻¹) = c * (t' * u) * c⁻¹ := by group
      _ = c * (u * t') * c⁻¹ := by rw [htu]
      _ = c * u * c⁻¹ * (c * t' * c⁻¹) := by group
  have hcuSb : c * u * c⁻¹ ∈ Sb := hT'eq ▸ ⟨u, huT, rfl⟩
  obtain ⟨ĉ, rfl⟩ := πQ_surjective (v1 * v3) c
  set x : centralizer ({(v1 * v3)} : Set G) := ĉ * ⟨w, hwY⟩ * ĉ⁻¹ with hx
  have hπx : πQ (v1 * v3) x = πQ (v1 * v3) ĉ * u * (πQ (v1 * v3) ĉ)⁻¹ := by
    rw [hx, map_mul, map_mul, map_inv]
  have hxQ : (x : G) ∈ alpP v1 v2 v3 s t ⊓ centralizer ({(v1 * v3)} : Set G) :=
    D.mem_of_liftQ (by rw [hπx]; exact hcuSb)
  obtain ⟨e, he⟩ := D.exists_phi_of_mem_P hxQ.1
  have hey : e * y0E = y0E * e := (D.comm_y0_phi e).1 (by
    rw [he]; exact mem_centralizer_singleton_iff.1 hxQ.2)
  have hw2' : w * w = 1 := (D.mem_W_iff.1 hw2).2
  have hx2 : (x : G) * x = 1 := by
    show (ĉ : G) * w * (ĉ : G)⁻¹ * ((ĉ : G) * w * (ĉ : G)⁻¹) = 1
    calc (ĉ : G) * w * (ĉ : G)⁻¹ * ((ĉ : G) * w * (ĉ : G)⁻¹) = ĉ * (w * w) * (ĉ : G)⁻¹ := by
          group
      _ = 1 := by rw [hw2']; group
  have he2 : e * e = 1 := D.E.inj (by rw [map_mul, he, hx2, map_one])
  have hgens : ∀ g ∈ [gen 0, gen 1, gen 2, gen 3], InY0E ((g * e)⁻¹ * (e * g)) := by
    intro g hg
    have hgQ := D.gens_mem_Q g hg
    have hgc := hcent _ (πQ_mem_liftQ (k := ⟨D.E.φ g, hgQ.2⟩) hgQ)
    rw [← hπx, πQ_comm_iff] at hgc
    rw [← D.mem_Y0_iff, map_mul, map_inv, map_mul, map_mul, he]
    exact hgc
  rcases mZ' e hey (by rw [he2]; exact Or.inl rfl) hgens with h | h
  ·
    have hxY0 : (x : G) ∈ zpowers (v1 * v3) := by rw [← he, D.mem_Y0_iff]; exact h
    have hw1 : πQ (v1 * v3) ⟨w, hwY⟩ = 1 := by
      have h1 : πQ (v1 * v3) x = 1 := (πQ_eq_one_iff x).2 hxY0
      rw [hπx] at h1
      have := congrArg (fun y => (πQ (v1 * v3) ĉ)⁻¹ * y * πQ (v1 * v3) ĉ) h1
      simpa [mul_assoc] using this
    have hwY0 := (πQ_eq_one_iff _).1 hw1
    have hwY0' : w ∈ zpowers (v1 * v3) := hwY0
    rcases hw with rfl | rfl
    · rw [D.w3_eq, D.mem_Y0_iff] at hwY0'
      exact mnotY0.1 hwY0'
    · have hv2 : v2 ^ 2 = D.E.φ (gen 1 ^ 2) := by rw [map_pow, AlpEmb.φ_v2]
      rw [hv2, D.mem_Y0_iff] at hwY0'
      exact mnotY0.2.1 hwY0'
  ·
    have hxb := mbinv e h he2
    have hxV : (x : G) ∈ alpV v1 v2 v3 := by
      rw [← he]
      rcases hxb with rfl | rfl
      · rw [← D.b_eq]; exact D.b_mem_V
      · rw [map_mul, ← D.b_eq, ← D.z_eq]; exact mul_mem D.b_mem_V D.z_mem_V'
    obtain ⟨n, hn, hnY, hnw⟩ := D.exists_normalizer_Y_conj hwV hxV ĉ.2 (by rw [hx]; rfl)
    obtain ⟨q, hq, hqn⟩ := D.exists_mem_Q_of_normalizer hn
      (mem_centralizer_singleton_iff.1 hnY)
    have hqw : (q : G) * w * q⁻¹ = x := by
      have hc := mem_centralizer_iff.1 hqn w hwV
      rw [← hnw]
      calc (q : G) * w * q⁻¹ = q * (q⁻¹ * n) * w * (q * (q⁻¹ * n))⁻¹ := by
            rw [show (q : G) * (q⁻¹ * n) = n by group] at *
            calc (q : G) * w * q⁻¹ = q * (w * (q⁻¹ * n)) * (q⁻¹ * n)⁻¹ * q⁻¹ := by group
              _ = q * ((q⁻¹ * n) * w) * (q⁻¹ * n)⁻¹ * q⁻¹ := by rw [hc]
              _ = n * w * n⁻¹ := by group
        _ = n * w * n⁻¹ := by group
    obtain ⟨eq, heq⟩ := D.exists_phi_of_mem_P hq.1
    have heqy : eq * y0E = y0E * eq := (D.comm_y0_phi eq).1 (by
      rw [heq]; exact mem_centralizer_singleton_iff.1 hq.2)
    rw [← he, ← heq] at hqw
    rcases hw with rfl | rfl
    · rw [D.w3_eq, ← map_inv, ← map_mul, ← map_mul] at hqw
      have hqw' := D.E.inj hqw
      rcases hxb with rfl | rfl
      · exact (mw1 eq heqy).1 hqw'
      · exact (mw1 eq heqy).2 hqw'
    · have hv2 : v2 ^ 2 = D.E.φ (gen 1 ^ 2) := by rw [map_pow, AlpEmb.φ_v2]
      rw [hv2, ← map_inv, ← map_mul, ← map_mul] at hqw
      have hqw' := D.E.inj hqw
      rcases hxb with rfl | rfl
      · exact (mw2 eq heqy).1 hqw'
      · exact (mw2 eq heqy).2 hqw'


theorem Sb_le_centralizer_b (hbY : invRep v1 v2 v3 s t 1 ∈ centralizer ({v1 * v3} : Set G)) :
    liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) ≤
      centralizer ({πQ (v1 * v3) ⟨invRep v1 v2 v3 s t 1, hbY⟩} : Set (KQ (v1 * v3))) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
  rw [mem_centralizer_singleton_iff, πQ_comm_iff]
  obtain ⟨e, he⟩ := D.exists_phi_of_mem_P hk.1
  have hey : e * y0E = y0E * e := (D.comm_y0_phi e).1 (by
    rw [he]; exact mem_centralizer_singleton_iff.1 hk.2)
  have h := mbcent' e hey
  show ((k : G) * invRep v1 v2 v3 s t 1)⁻¹ * (invRep v1 v2 v3 s t 1 * k) ∈ zpowers (v1 * v3)
  rw [← he, D.b_eq, ← map_mul, ← map_mul, ← map_inv, ← map_mul, D.mem_Y0_iff]
  exact h

theorem isSylowOf_Sb_centralizer {u : KQ (v1 * v3)} (hu : u ∈ liftQ (v1 * v3) (alpW0 v1 v2 v3)) :
    IsSylowOf 2 (liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) ⊓
      centralizer ({u} : Set (KQ (v1 * v3)))) (centralizer ({u} : Set (KQ (v1 * v3)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hu
  obtain ⟨e, he, he'⟩ := D.exists_phi_W0 hk
  have hrep : ∀ (r : AlpE) (hr : D.E.φ r ∈ centralizer ({v1 * v3} : Set G)),
      InY0E (r⁻¹ * e) → πQ (v1 * v3) k = πQ (v1 * v3) ⟨D.E.φ r, hr⟩ := by
    intro r hr h
    rw [πQ_eq_iff]
    show (k : G)⁻¹ * D.E.φ r ∈ zpowers (v1 * v3)
    have h' : D.E.φ (r⁻¹ * e) ∈ zpowers (v1 * v3) := (D.mem_Y0_iff _).2 h
    rw [map_mul, map_inv, he'] at h'
    have := inv_mem h'
    rwa [mul_inv_rev, inv_inv] at this
  have hbY : invRep v1 v2 v3 s t 1 ∈ centralizer ({v1 * v3} : Set G) :=
    D.V_le_Y D.b_mem_V
  have hw1Y : v1 ^ 2 ∈ centralizer ({v1 * v3} : Set G) := D.V_le_Y (D.W_le_V w3_mem_W)
  have hw2Y : v2 ^ 2 ∈ centralizer ({v1 * v3} : Set G) :=
    D.V_le_Y (D.W_le_V (subset_closure (by simp)))
  rcases mW0rep e he with h | h | h | h
  ·
    have h1 : πQ (v1 * v3) k = 1 := by
      rw [πQ_eq_one_iff, ← he', D.mem_Y0_iff]
      exact h
    have htop : centralizer ({(1 : KQ (v1 * v3))} : Set (KQ (v1 * v3))) = ⊤ :=
      eq_top_iff.2 fun x _ => mem_centralizer_singleton_iff.2 (by rw [mul_one, one_mul])
    rw [h1, htop, inf_top_eq]
    exact D.isSylowOf_Sb
  ·
    rw [hrep (invE 1) (by rw [← D.b_eq]; exact hbY) h]
    have hle := D.Sb_le_centralizer_b hbY
    simp only [← D.b_eq] at hle ⊢
    rw [inf_of_le_left hle]
    exact D.isSylowOf_Sb.of_le hle le_top
  ·
    rw [hrep (gen 0 ^ 2) (by rw [← D.w3_eq]; exact hw1Y) h]
    have := D.isSylowOf_Sb_w (w := v1 ^ 2) (Or.inl rfl) hw1Y
    simp only [← D.w3_eq]
    exact this
  ·
    have hv2 : v2 ^ 2 = D.E.φ (gen 1 ^ 2) := by rw [map_pow, AlpEmb.φ_v2]
    rw [hrep (gen 1 ^ 2) (by rw [← hv2]; exact hw2Y) h]
    have := D.isSylowOf_Sb_w (w := v2 ^ 2) (Or.inr rfl) hw2Y
    simp only [← hv2]
    exact this

theorem hconjK : ∀ u ∈ liftQ (v1 * v3) (alpW0 v1 v2 v3), ∀ R : Subgroup (KQ (v1 * v3)),
    R ≤ centralizer ({u} : Set (KQ (v1 * v3))) → IsPGroup 2 R → (∀ r ∈ R, r * r = 1) →
    ∃ c ∈ centralizer ({u} : Set (KQ (v1 * v3))), ∀ r ∈ R, c * r * c⁻¹ ∈
      liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) := by
  intro u hu R hR hRp hR2
  obtain ⟨c, hc, hcR⟩ := exists_conj_le_of_isSylowOf (D.isSylowOf_Sb_centralizer hu) hR hRp
  refine ⟨c, hc, fun r hr => D.mem_S1_of_mem_Sb (hcR r hr).1 ?_⟩
  calc c * r * c⁻¹ * (c * r * c⁻¹) = c * (r * r) * c⁻¹ := by group
    _ = 1 := by rw [hR2 r hr]; group


theorem S1_le_Sb : liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) ≤
    liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_liftQ_iff.1 hx
  obtain ⟨e, he, -⟩ := D.exists_phi_Vj hk
  exact πQ_mem_liftQ ⟨he ▸ AlpEmb.φ_mem D.E e, k.2⟩

theorem s_mem_Y : s ∈ centralizer ({v1 * v3} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← AlpEmb.φ_s D.E, D.comm_y0_phi]
  exact y0E_comm_s

theorem card_WG [DecidableEq G] : (WEL.toFinset.image D.E.φ).card = 8 := by
  rw [Finset.card_image_of_injective _ D.E.inj]
  rfl

theorem mem_WG [DecidableEq G] {g : G} :
    g ∈ WEL.toFinset.image D.E.φ ↔ g ∈ alpW v1 v2 v3 := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (D.mem_W_phi_iff e).2 (List.mem_toFinset.1 he)
  · intro hg
    obtain ⟨e, he, rfl⟩ := D.exists_phi_WEL hg
    exact ⟨e, List.mem_toFinset.2 he, rfl⟩

theorem isSylowOf_S1_normalizer_U :
    IsSylowOf 2 (liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)))
      (normalizer (D.invSettingK.U : Set (KQ (v1 * v3)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have H := D.invSettingK
  set Sb := liftQ (v1 * v3) (alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G)) with hSb
  set S1 := liftQ (v1 * v3) (alpV v1 v2 v3 ⊔ zpowers (invRep v1 v2 v3 s t 3)) with hS1
  set U := D.invSettingK.U with hU
  have hS1N : S1 ≤ normalizer (U : Set (KQ (v1 * v3))) := D.invSettingK.S_le_normalizer_U
  have hS1p : IsPGroup 2 S1 := D.isSylowOf_Sb.isPGroup.to_le D.S1_le_Sb
  obtain ⟨T, hT, hS1T⟩ := exists_isSylowOf_of_le' hS1p hS1N
  by_cases hS1T' : S1 = T
  · have h : IsSylowOf 2 S1 (normalizer (U : Set (KQ (v1 * v3)))) := by rw [hS1T']; exact hT
    exact h
  exfalso
  have hcardT := two_mul_card_le_of_lt hS1T hS1T'
  have hcardS1 : 32 ≤ Nat.card S1 := D.card_S1_ge
  obtain ⟨c, -, hc⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_Sb le_top hT.isPGroup
  set T' := T.map (MulAut.conj c).toMonoidHom with hT'
  have hT'le : T' ≤ Sb := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  have hT'eq : T' = Sb := eq_of_le_of_card_ge hT'le (by
    rw [hT', card_map_of_injective (MulAut.conj c).injective, D.card_Sb]
    omega)
  obtain ⟨ĉ, rfl⟩ := πQ_surjective (v1 * v3) c
  have hUT : U ≤ T := (D.invSettingK.U_le_S).trans hS1T
  have hxQ : ∀ u : centralizer ({v1 * v3} : Set G), πQ (v1 * v3) u ∈ U →
      ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) ∈
        alpP v1 v2 v3 s t ⊓ centralizer ({v1 * v3} : Set G) := by
    intro u hu
    refine D.mem_of_liftQ ?_
    rw [map_mul, map_mul, map_inv]
    show πQ (v1 * v3) ĉ * πQ (v1 * v3) u * (πQ (v1 * v3) ĉ)⁻¹ ∈ Sb
    rw [← hT'eq]
    exact ⟨πQ (v1 * v3) u, hUT hu, rfl⟩
  set sY : centralizer ({v1 * v3} : Set G) := ⟨s, D.s_mem_Y⟩ with hsY
  have hxs : ∀ u : centralizer ({v1 * v3} : Set G), πQ (v1 * v3) u ∈ U →
      ∃ u' : centralizer ({v1 * v3} : Set G), πQ (v1 * v3) u' ∈ U ∧
        sY * (ĉ * u * ĉ⁻¹) * sY⁻¹ = ĉ * u' * ĉ⁻¹ := by
    intro u hu
    have hsSb : πQ (v1 * v3) sY ∈ Sb := πQ_mem_liftQ ⟨s_mem_P, D.s_mem_Y⟩
    rw [← hT'eq] at hsSb
    obtain ⟨t', ht', ht'e⟩ := hsSb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at ht'e
    refine ⟨ĉ⁻¹ * sY * ĉ * u * ĉ⁻¹ * sY⁻¹ * ĉ, ?_, by group⟩
    have e : πQ (v1 * v3) (ĉ⁻¹ * sY * ĉ * u * ĉ⁻¹ * sY⁻¹ * ĉ) = t' * πQ (v1 * v3) u * t'⁻¹ := by
      simp only [map_mul, map_inv]
      rw [← ht'e]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (hT.le ht') _).1 hu
  have hsq : ∀ u : centralizer ({v1 * v3} : Set G), πQ (v1 * v3) u ∈ U →
      ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) *
        ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) ∈ zpowers (v1 * v3) := by
    intro u hu
    have h1 : πQ (v1 * v3) (u * u) = 1 := by rw [map_mul]; exact D.invSettingK.U_sq hu
    have h2 := (πQ_eq_one_iff _).1 h1
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 h2
    have hcomm : (ĉ : G) * (v1 * v3) = v1 * v3 * ĉ := mem_centralizer_singleton_iff.1 ĉ.2
    have e : ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) *
        ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) =
        (ĉ : G) * ((u : G) * u) * (ĉ : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    have hu2 : ((u : G) * u) = (v1 * v3) ^ n := by
      rw [hn]
      rfl
    rw [hu2, (Commute.zpow_right hcomm n).eq, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) n
  have hinvW : ∀ u : centralizer ({v1 * v3} : Set G), πQ (v1 * v3) u ∈ U →
      ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) *
        ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) = 1 →
      ((ĉ * u * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) ∈ alpW v1 v2 v3 := by
    intro u hu hx2
    have hQ := hxQ u hu
    obtain ⟨e, he⟩ := D.exists_phi_of_mem_P hQ.1
    have hey : e * y0E = y0E * e := (D.comm_y0_phi e).1 (by
      rw [he]; exact mem_centralizer_singleton_iff.1 hQ.2)
    have he2 : e * e = 1 := D.E.inj (by rw [map_mul, he, hx2, map_one])
    rcases mQinv e hey (by rw [he2]; exact Or.inl rfl) with h | h
    · rw [← he]
      exact D.mem_W_iff.2 ⟨(D.mem_V_phi e).2 h, by rw [← map_mul, he2, map_one]⟩
    · exfalso
      have hd := jE_inv_d e h
      obtain ⟨u', hu', hu'e⟩ := hxs u hu
      have hprod : πQ (v1 * v3) (u' * u) ∈ U := by rw [map_mul]; exact mul_mem hu' hu
      have h3 := hsq (u' * u) hprod
      have e3 : ((ĉ * (u' * u) * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) =
          D.E.φ (gen 3 * e * (gen 3)⁻¹ * e) := by
        have : ĉ * (u' * u) * ĉ⁻¹ = (sY * (ĉ * u * ĉ⁻¹) * sY⁻¹) * (ĉ * u * ĉ⁻¹) := by
          rw [hu'e]; group
        rw [this, map_mul, map_mul, map_mul, map_inv, AlpEmb.φ_s D.E, he]
        rfl
      rw [e3, ← map_mul, D.mem_Y0_iff] at h3
      exact msx e hd he2 h3
  set f : G → G := fun g => (ĉ : G) * g * (ĉ : G)⁻¹ with hf
  set WG := WEL.toFinset.image D.E.φ with hWG
  have h1WG : (1 : G) ∈ WG := D.mem_WG.2 (one_mem _)
  have hjWG : invRep v1 v2 v3 s t 3 ∉ WG.erase 1 := fun h =>
    D.j_notMem_V (D.W_le_V (D.mem_WG.1 (Finset.mem_of_mem_erase h)))
  set S8 := insert (invRep v1 v2 v3 s t 3) (WG.erase 1) with hS8
  have hcard8 : S8.card = 8 := by
    rw [hS8, Finset.card_insert_of_notMem hjWG, Finset.card_erase_of_mem h1WG, D.card_WG]
  have hcard7 : (WG.erase 1).card = 7 := by
    rw [Finset.card_erase_of_mem h1WG, D.card_WG]
  have hmaps : ∀ a ∈ S8, f a ∈ WG.erase 1 := by
    intro a ha
    have hdata : ∃ hY : a ∈ centralizer ({v1 * v3} : Set G),
        πQ (v1 * v3) ⟨a, hY⟩ ∈ U ∧ a * a = 1 ∧ a ≠ 1 := by
      rcases Finset.mem_insert.1 ha with rfl | ha
      · refine ⟨D.j_mem_Y, D.invSettingK.j_mem_U, D.rep_sq 3, D.rep_ne_one 3⟩
      · obtain ⟨ha1, haW⟩ := Finset.mem_erase.1 ha
        have haW' := D.mem_WG.1 haW
        refine ⟨D.V_le_Y (D.W_le_V haW'), D.invSettingK.A_le_U (πQ_mem_liftQ
          (mem_sup_left haW')), (D.mem_W_iff.1 haW').2, ha1⟩
    obtain ⟨hY, hU, ha2, ha1⟩ := hdata
    have hx2 : ((ĉ * ⟨a, hY⟩ * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) *
        ((ĉ * ⟨a, hY⟩ * ĉ⁻¹ : centralizer ({v1 * v3} : Set G)) : G) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (ĉ : G) * a * (ĉ : G)⁻¹ * ((ĉ : G) * a * (ĉ : G)⁻¹) = ĉ * (a * a) * (ĉ : G)⁻¹ := by
            group
        _ = 1 := by rw [ha2]; group
    have hW := hinvW ⟨a, hY⟩ hU hx2
    refine Finset.mem_erase.2 ⟨fun h => ha1 ?_, D.mem_WG.2 hW⟩
    have : (ĉ : G) * a * (ĉ : G)⁻¹ = 1 := h
    calc a = (ĉ : G)⁻¹ * ((ĉ : G) * a * (ĉ : G)⁻¹) * ĉ := by group
      _ = 1 := by rw [this]; group
  have hinj : Set.InjOn f S8 := fun a _ b _ hab => by
    have : (ĉ : G) * a * (ĉ : G)⁻¹ = (ĉ : G) * b * (ĉ : G)⁻¹ := hab
    simpa using this
  have := Finset.card_le_card_of_injOn f hmaps hinj
  omega

theorem not_conj_j_mem_V {k : G} (hk : k ∈ centralizer ({v1 * v3} : Set G)) :
    k⁻¹ * invRep v1 v2 v3 s t 3 * k ∉ alpV v1 v2 v3 := by
  intro h
  apply D.invSettingK.not_conj_mem_of D.card_A D.hconjK D.isSylowOf_S1_normalizer_U
    (πQ (v1 * v3) ⟨k, hk⟩)
  have e : (πQ (v1 * v3) ⟨k, hk⟩)⁻¹ * πQ (v1 * v3) D.jY * πQ (v1 * v3) ⟨k, hk⟩ =
      πQ (v1 * v3) (⟨k, hk⟩⁻¹ * D.jY * ⟨k, hk⟩) := by
    simp only [map_mul, map_inv]
  rw [e]
  exact πQ_mem_liftQ h

end FusCtx

end CFSG.OddStandard.ONanRec
