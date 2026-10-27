module

public import CFSG.Quasithin.H13.L32NLem1445c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1445b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace L1444

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setup5_F4
open Setup5
open CFSG.Quasithin.H13.L1444.Setup5_F4

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup5_F4 G T L V V₂ g D Q₁ Q₂)
include S

theorem exists_mem_L_conj_eq_F4 {b : G} (hb : b ∈ L ⊔ T) :
    ∃ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ = b * v * b⁻¹ := by
  obtain ⟨_, S'⟩ := S.set14
  have hbN : b ∈ Subgroup.normalizer (V : Set G) := S.normV hb
  have hmem : conjAct V ⟨b, hbN⟩ ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One S'.h1281_F4]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hmem
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, fun v hv => ?_⟩
  exact congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hlα

theorem mem_or_mul_mem_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V) {b : G}
    (hb : b ∈ L ⊔ T) : b ∈ L ∨ b * s ∈ L := by
  obtain ⟨l, hl, hlb⟩ := S.exists_mem_L_conj_eq_F4 hb
  have hc : l⁻¹ * b ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).inv_mem (Subgroup.mem_sup_left hl)) hb,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    calc v * (l⁻¹ * b) = l⁻¹ * (l * v * l⁻¹) * l * (l⁻¹ * b) := by group
      _ = l⁻¹ * (b * v * b⁻¹) * l * (l⁻¹ * b) := by rw [hlb v hv]
      _ = l⁻¹ * b * v := by group
  by_cases hcV : l⁻¹ * b ∈ V
  · left
    rw [show b = l * (l⁻¹ * b) by group]
    exact L.mul_mem hl (S.V_le_L hcV)
  · right
    have h1 := S.inv_mul_mem_V_F4 hc hs hcV hsV
    have hcc : (l⁻¹ * b)⁻¹ = l⁻¹ * b := inv_eq_of_mul_eq_one_left (S.mul_self_cent_F4 hCTL hc)
    rw [hcc] at h1
    rw [show b * s = l * (l⁻¹ * b * s) by group]
    exact L.mul_mem hl (S.V_le_L h1)

theorem relIndex_T_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V) :
    (T ⊓ L).relIndex T = 2 := by
  rw [Subgroup.inf_relIndex_left]
  refine Subgroup.index_eq_two_iff_exists_notMem_and.mpr ⟨⟨s, S.cent_le_T_F4 hs⟩, fun h => ?_,
    fun b => ?_⟩
  · exact hsV (S.mem_V_of_mem_cent_F4 hs (Subgroup.mem_subgroupOf.1 h))
  · rcases S.mem_or_mul_mem_F4 hCTL hs hsV (Subgroup.mem_sup_right b.2) with h | h
    · exact Or.inr (Subgroup.mem_subgroupOf.2 h)
    · exact Or.inl (Subgroup.mem_subgroupOf.2 h)

theorem exists_seven_F4 :
    ∃ y ∈ L, orderOf y = 7 ∧ ∃ u ∈ V, y * u * y⁻¹ ≠ u := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 7 (by rw [S.cardL]; norm_num)
  refine ⟨y, y.2, by rw [Subgroup.orderOf_coe, hy], ?_⟩
  by_contra h
  push Not at h
  have hyV : (y : G) ∈ V := S.centL.le ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun v hv => by
    calc v * y = (y : G) * v * (y : G)⁻¹ * y := by rw [h v hv]
      _ = y * v := by group⟩
  have h2 : orderOf (y : G) ∣ 2 := orderOf_dvd_of_pow_eq_one (S.elem.2 _ hyV)
  rw [Subgroup.orderOf_coe, hy] at h2
  norm_num at h2

theorem exists_fix_cent_F4 {y : G} (hyL : y ∈ L) (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1)
    {s₀ : G} (hs₀ : s₀ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hs₀V : s₀ ∉ V) :
    ∃ s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G), s ∉ V ∧ y * s * y⁻¹ = s := by
  obtain ⟨w, hw, hfx⟩ := L1445.exists_fix_mul (S.L_le_normV hyL) hfix hs₀.2
    (S.comm_mem_V_of_cent_F4 hs₀ hyL)
  have hwC : w ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨Subgroup.mem_sup_left (S.V_le_L hw),
      Subgroup.mem_centralizer_iff.mpr fun v hv => S.comm_V hv hw⟩
  refine ⟨s₀ * w, Subgroup.mul_mem _ hs₀ hwC, fun h => hs₀V ?_, hfx⟩
  rw [show s₀ = s₀ * w * w⁻¹ by group]
  exact V.mul_mem h (V.inv_mem hw)

theorem exists_conj_cent_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {y : G} (hyL : y ∈ L)
    (hy : orderOf y = 7) (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (hys : y * s * y⁻¹ = s) {w : G} (hw : w ∈ V) : ∃ l ∈ L, l * s * l⁻¹ = s * w := by
  have hsv : ∀ v ∈ V, s * v = v * s := fun v hv =>
    (Subgroup.mem_centralizer_iff.mp hs.2 v hv).symm

  obtain ⟨l₀, hl₀, hl₀s⟩ : ∃ l₀ ∈ L, l₀ * s * l₀⁻¹ ≠ s := by
    by_contra h
    push Not at h
    have h1 := eq_one_of_comm_L hCTL (S.cent_le_T_F4 hs) h
    exact hsV (h1 ▸ V.one_mem)
  set u := l₀ * s * l₀⁻¹ * s⁻¹ with hu
  have huV : u ∈ V := S.comm_mem_V_of_cent_F4 hs hl₀
  have hu1 : u ≠ 1 := fun h => hl₀s (by
    calc l₀ * s * l₀⁻¹ = l₀ * s * l₀⁻¹ * s⁻¹ * s := by group
      _ = s := by rw [← hu, h, one_mul])
  by_cases hw1 : w = 1
  · exact ⟨1, L.one_mem, by rw [hw1]; group⟩
  obtain ⟨i, hi⟩ := L1445.exists_pow_conj_eq S.card8 hy (S.L_le_normV hyL) hfix huV hu1 hw hw1
  have hcs : ∀ j : ℕ, y ^ j * s * (y ^ j)⁻¹ = s := by
    have hc : Commute y s := by
      show y * s = s * y
      calc y * s = y * s * y⁻¹ * y := by group
        _ = s * y := by rw [hys]
    intro j
    rw [(hc.pow_left j).eq, mul_inv_cancel_right]
  refine ⟨y ^ i * l₀, L.mul_mem (L.pow_mem hyL i) hl₀, ?_⟩
  calc y ^ i * l₀ * s * (y ^ i * l₀)⁻¹ = y ^ i * (u * s) * (y ^ i)⁻¹ := by rw [hu]; group
    _ = (y ^ i * u * (y ^ i)⁻¹) * (y ^ i * s * (y ^ i)⁻¹) := by group
    _ = w * s := by rw [hi, hcs]
    _ = s * w := (hsv w hw).symm

theorem card_inf_centralizer_F4 {s : G} (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))
    (htr : ∀ w ∈ V, ∃ l ∈ L, l * s * l⁻¹ = s * w) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168 := by
  have hmem : ∀ l ∈ L, s⁻¹ * (l * s * l⁻¹) ∈ V := by
    intro l hl
    have h := S.comm_mem_V_of_cent_F4 hs hl
    have hsv := (Subgroup.mem_centralizer_iff.mp hs.2 _ h).symm
    rw [show s⁻¹ * (l * s * l⁻¹) = s⁻¹ * (l * s * l⁻¹ * s⁻¹) * s by group, mul_assoc, ← hsv]
    simpa using h
  have h := L1445.card_eq_mul_card_inf_centralizer hmem htr
  rw [S.cardL, S.card8] at h
  omega

theorem le_cent_of_isPGroup_F4 (hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥) {s : G}
    (hs : s ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) (hsV : s ∉ V)
    (h168 : Nat.card ↥(L ⊓ Subgroup.centralizer ({s} : Set G)) = 168) {P : Subgroup G}
    (hCP : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ P)
    (hP : P ≤ (L ⊔ T) ⊓ Subgroup.centralizer ({s} : Set G)) (hP2 : IsPGroup 2 P) :
    P ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  have hVC : V ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := fun v hv =>
    ⟨Subgroup.mem_sup_left (S.V_le_L hv),
      Subgroup.mem_centralizer_iff.mpr fun w hw => S.comm_V hw hv⟩

  have hPL : P ⊓ L = V := by
    have hle : V ≤ P ⊓ L := le_inf (hVC.trans hCP) S.V_le_L
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [S.card8]
    have hdvd : Nat.card ↥(P ⊓ L) ∣ 168 := by
      rw [← h168]
      exact Subgroup.card_dvd_of_le fun x hx => ⟨hx.2, (hP hx.1).2⟩
    obtain ⟨k, hk⟩ := (hP2.to_le inf_le_left).exists_card_eq
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) 21 := Nat.Coprime.pow_left k (by norm_num)
    have h8 : 2 ^ k ∣ 8 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    exact Nat.le_of_dvd (by norm_num) h8
  intro p hp
  rcases S.mem_or_mul_mem_F4 hCTL hs hsV (hP hp).1 with h | h
  · exact hVC (hPL ▸ ⟨hp, h⟩)
  · have hps : p * s ∈ V := hPL ▸ ⟨P.mul_mem hp (hCP hs), h⟩
    rw [show p = p * s * s⁻¹ by group]
    exact Subgroup.mul_mem _ (hVC hps) (Subgroup.inv_mem _ hs)

end Setup5_F4

end L1444

end CFSG.Quasithin.H13
