module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Setup
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem517A5Block

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

structure Setting_F4 (T M L W : Subgroup G) (F : S5Frame (L ⊔ T) W) (n : ℕ) : Prop where

  hyp : Hyp5_0_1 G T M L n

  h432 : Stmt4_3_2_F4

  hB : A5BaumHyp F T

  WU : W = blockU L

  O2 : pCoreOf 2 (L ⊔ T) = W ⊔ (T ⊓ Subgroup.centralizer (L : Set G))

  disj : W ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥

  CTW : T ⊓ Subgroup.centralizer (W : Set G) = pCoreOf 2 (L ⊔ T)

  NS : ¬ Subgroup.normalizer (baum T : Set G) ≤ M

namespace Setting_F4
open CFSG.Quasithin.H13.A5Push.Setting_F4

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ}

theorem W_le_L_F4 (hs : Setting_F4 T M L W F n) : W ≤ L := by
  rw [hs.WU]
  exact Subgroup.le_normalizer_iff_commutator_le_right.mp
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)

theorem M_le_normalizer_F4 (hs : Setting_F4 T M L W F n) : M ≤ Subgroup.normalizer (W : Set G) := by
  intro g hg
  rw [hs.WU]
  exact C1.mem_normalizer_blockU (hs.hyp.normal hg)

theorem sup_le_normalizer_F4 (_hs : Setting_F4 T M L W F n) :
    L ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
  fun _ hg => F.le hg

theorem W_ne_bot_F4 (_hs : Setting_F4 T M L W F n) : W ≠ ⊥ := by
  intro h
  have h1 := F.card_W
  rw [h, Subgroup.card_bot] at h1
  omega

theorem W_le_Q_F4 (hs : Setting_F4 T M L W F n) :
    W ≤ baum T ⊓ Subgroup.centralizer (W : Set G) := by
  refine le_inf hs.hB.le_baum fun w hw => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have := hs.hB.el.1
  exact setLike_mul_comm hv hw

theorem QC_le_Q_F4 (hs : Setting_F4 T M L W F n) :
    baum T ⊓ Subgroup.centralizer (L : Set G) ≤ baum T ⊓ Subgroup.centralizer (W : Set G) :=
  inf_le_inf_left _ (Subgroup.centralizer_le hs.W_le_L_F4)

theorem Q_le_F4 (hs : Setting_F4 T M L W F n) :
    baum T ⊓ Subgroup.centralizer (W : Set G) ≤ W ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) := by
  rw [← hs.O2, ← hs.CTW]
  exact inf_le_inf_right _ (Setting.S_le_T T)

theorem mem_decomp_F4 (hs : Setting_F4 T M L W F n) {q : G}
    (hq : q ∈ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    ∃ w ∈ W, ∃ c ∈ baum T ⊓ Subgroup.centralizer (L : Set G), q = w * c := by
  have hCN : T ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    inf_le_left.trans (le_sup_right.trans hs.sup_le_normalizer_F4)
  have h1 : q ∈ ((W ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) : Set G) :=
    hs.Q_le_F4 hq
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W _ hCN] at h1
  obtain ⟨w, hw, c, hc, rfl⟩ := Set.mem_mul.mp h1
  refine ⟨w, hw, c, ⟨?_, hc.2⟩, rfl⟩
  have h2 : c = w⁻¹ * (w * c) := by group
  rw [h2]
  exact (baum T).mul_mem ((baum T).inv_mem (hs.hB.le_baum hw)) hq.1

theorem W_inf_QC_F4 (hs : Setting_F4 T M L W F n) :
    W ⊓ (baum T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  rw [eq_bot_iff, ← hs.disj]
  exact inf_le_inf_left _ (inf_le_inf_right _ (Setting.S_le_T T))

theorem commutator_mem_F4 (hs : Setting_F4 T M L W F n) {q l : G}
    (hq : q ∈ baum T ⊓ Subgroup.centralizer (W : Set G)) (hl : l ∈ L) :
    q * l * q⁻¹ * l⁻¹ ∈ W := by
  obtain ⟨w, hw, c, hc, rfl⟩ := hs.mem_decomp_F4 hq
  have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc.2 l hl).symm
  have e : w * c * l * (w * c)⁻¹ * l⁻¹ = w * (l * w⁻¹ * l⁻¹) := by
    calc w * c * l * (w * c)⁻¹ * l⁻¹ = w * (c * l) * c⁻¹ * w⁻¹ * l⁻¹ := by group
      _ = w * (l * c) * c⁻¹ * w⁻¹ * l⁻¹ := by rw [hcl]
      _ = w * (l * w⁻¹ * l⁻¹) := by group
  rw [e]
  refine W.mul_mem hw ?_
  exact (Subgroup.mem_normalizer_iff.mp (hs.sup_le_normalizer_F4 (Subgroup.mem_sup_left hl)) _).mp
    (W.inv_mem hw)

theorem L_le_normalizer_Q_F4 (hs : Setting_F4 T M L W F n) :
    L ≤ Subgroup.normalizer ((baum T ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) :
      Set G) := by
  have key : ∀ l ∈ L, ∀ q ∈ baum T ⊓ Subgroup.centralizer (W : Set G),
      l * q * l⁻¹ ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
    intro l hl q hq
    have h1 := hs.commutator_mem_F4 hq hl
    have e : l * q * l⁻¹ = (q * l * q⁻¹ * l⁻¹)⁻¹ * q := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hs.W_le_Q_F4 h1)) hq
  intro l hl
  refine mem_normalizer_of_conj (key l hl) fun q hq => ?_
  have := key l⁻¹ (L.inv_mem hl) q hq
  simpa using this

theorem T_le_normalizer_Q_F4 (hs : Setting_F4 T M L W F n) :
    T ≤ Subgroup.normalizer ((baum T ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) :
      Set G) := by
  have key : ∀ t ∈ T, ∀ q ∈ baum T ⊓ Subgroup.centralizer (W : Set G),
      t * q * t⁻¹ ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
    intro t ht q hq
    refine Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (Setting.T_le_normalizer_S T ht) q).mp hq.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have htW := hs.sup_le_normalizer_F4 (Subgroup.mem_sup_right ht)
    have hw' : t⁻¹ * w * t ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htW) w).mp hw
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hq.2 _ hw'
    calc w * (t * q * t⁻¹) = t * ((t⁻¹ * w * t) * q) * t⁻¹ := by group
      _ = t * (q * (t⁻¹ * w * t)) * t⁻¹ := by rw [h1]
      _ = t * q * t⁻¹ * w := by group
  intro t ht
  refine mem_normalizer_of_conj (key t ht) fun q hq => ?_
  have := key t⁻¹ (T.inv_mem ht) q hq
  simpa using this

theorem normalizer_Q_le_F4 (hs : Setting_F4 T M L W F n) :
    Subgroup.normalizer ((baum T ⊓ Subgroup.centralizer (W : Set G) : Subgroup G) : Set G) ≤
      M := by
  refine hs.hyp.normalizer_le_of_le_F4 hs.h432 ?_ ?_ hs.L_le_normalizer_Q_F4
  · intro hb
    apply hs.W_ne_bot_F4
    rw [eq_bot_iff, ← hb]
    exact hs.W_le_Q_F4
  · exact hs.hyp.sylow.1.to_le (inf_le_left.trans (Setting.S_le_T T))

theorem rho_eq_one_iff_F4 (_hs : Setting_F4 T M L W F n) (s : ↥(L ⊔ T)) (hsS : (s : G) ∈ baum T) :
    F.ρ s = 1 ↔ (s : G) ∈ baum T ⊓ Subgroup.centralizer (W : Set G) := by
  rw [F.ρ_eq_one_iff]
  exact ⟨fun h => ⟨hsS, h⟩, fun h => h.2⟩

theorem exists_conj_not_le_F4 (hs : Setting_F4 T M L W F n) :
    ∃ k ∈ Subgroup.normalizer (baum T : Set G),
      ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G) := by
  by_contra hcon
  push Not at hcon
  set NS := Subgroup.normalizer (baum T : Set G) with hNS
  set Q := baum T ⊓ Subgroup.centralizer (W : Set G) with hQ
  set U₀ : Subgroup G :=
    Subgroup.closure {x | ∃ k ∈ NS, ∃ w ∈ W, x = k * w * k⁻¹} with hU₀
  have hU₀Q : U₀ ≤ Q := by
    rw [hU₀, Subgroup.closure_le]
    rintro x ⟨k, hk, w, hw, rfl⟩
    exact hcon k hk (conj_mem_conj_map hw)
  have hWU : W ≤ U₀ := fun w hw =>
    Subgroup.subset_closure ⟨1, NS.one_mem, w, hw, by group⟩

  have hNU : ∀ k ∈ NS, ∀ x ∈ U₀, k * x * k⁻¹ ∈ U₀ := by
    intro k hk x hx
    rw [hU₀] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k', hk', w, hw, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨k * k', NS.mul_mem hk hk', w, hw, by group⟩
    | one => simp
    | mul y z _ _ hy hz =>
      have e : k * (y * z) * k⁻¹ = (k * y * k⁻¹) * (k * z * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hy hz
    | inv y _ hy =>
      have e : k * y⁻¹ * k⁻¹ = (k * y * k⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hy
  have hNSU : NS ≤ Subgroup.normalizer (U₀ : Set G) := fun k hk =>
    mem_normalizer_of_conj (hNU k hk) fun x hx => by
      have := hNU k⁻¹ (NS.inv_mem hk) x hx
      simpa using this

  have hLU : ∀ l ∈ L, ∀ x ∈ U₀, l * x * l⁻¹ ∈ U₀ := by
    intro l hl x hx
    have h1 := hs.commutator_mem_F4 (hU₀Q hx) hl
    have e : l * x * l⁻¹ = (x * l * x⁻¹ * l⁻¹)⁻¹ * x := by group
    rw [e]
    exact U₀.mul_mem (U₀.inv_mem (hWU h1)) hx
  have hLN : L ≤ Subgroup.normalizer (U₀ : Set G) := fun l hl =>
    mem_normalizer_of_conj (hLU l hl) fun x hx => by
      have := hLU l⁻¹ (L.inv_mem hl) x hx
      simpa using this
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hb
    apply hs.W_ne_bot_F4
    rw [eq_bot_iff, ← hb]
    exact hWU
  have hU₀2 : IsPGroup 2 U₀ :=
    hs.hyp.sylow.1.to_le (hU₀Q.trans (inf_le_left.trans (Setting.S_le_T T)))
  exact hs.NS (hNSU.trans (hs.hyp.normalizer_le_of_le_F4 hs.h432 hU₀ne hU₀2 hLN))

end Setting_F4

end CFSG.Quasithin.H13.A5Push
