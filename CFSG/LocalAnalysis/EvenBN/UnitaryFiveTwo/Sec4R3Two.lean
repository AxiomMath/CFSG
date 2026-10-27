module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R3

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem index_subgroupOf_eq_two {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hc : Nat.card K = 2 * Nat.card H) : (H.subgroupOf K).index = 2 := by
  have e := Subgroup.relIndex_mul_card (H := H) (K := K)
  rw [inf_of_le_left hHK, hc] at e
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos e

theorem le_normalizer_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hc : Nat.card K = 2 * Nat.card H) : K ≤ normalizer (H : Set G) := by
  have hN := Subgroup.normal_of_index_eq_two (index_subgroupOf_eq_two hHK hc)
  intro k hk
  refine mem_normalizer_fintype fun x hx => ?_
  have := hN.conj_mem ⟨x, hHK hx⟩ hx ⟨k, hk⟩
  exact this

theorem mul_mem_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hc : Nat.card K = 2 * Nat.card H) {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (haH : a ∉ H) (hbH : b ∉ H) : a * b ∈ H := by
  have := (Subgroup.mul_mem_iff_of_index_two (index_subgroupOf_eq_two hHK hc)
    (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).2 (iff_of_false haH hbH)
  exact this

theorem conj_mem_oTwo_of_mem_normalizer' {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    {h g : G} (hh : h ∈ normalizer (X : Set G)) (hg : g ∈ oTwo X) : h * g * h⁻¹ ∈ oTwo X := by
  have hle : (oTwo X).map (MulAut.conj h).toMonoidHom ≤ oTwo X := by
    refine le_oTwo ?_ ?_ ((isPGroup_oTwo X).map _)
    · rintro _ ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hh y).1 (oTwo_le X hy)
    · intro x hx
      refine mem_normalizer_fintype fun z hz => ?_
      obtain ⟨y, hy, rfl⟩ := hz
      have hx' : h⁻¹ * x * h ∈ X := by
        have := (mem_normalizer_iff.1 (inv_mem hh) x).1 hx
        rwa [inv_inv] at this
      refine ⟨(h⁻¹ * x * h) * y * (h⁻¹ * x * h)⁻¹, conj_mem_oTwo hx' hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hle ⟨g, hg, rfl⟩

theorem mul_self_mem_ZX₄sub {a : SU52} (ha : a ∈ A₁sub) : a * a ∈ ZX₄sub :=
  mem_ZX₄sub_of_cvec_eq_zero (mul_mem ha ha) (by
    rw [cvec_mul ha ha]
    funext i
    exact CharTwo.add_self_eq_zero _)

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem mul_self_mem_ZX₄ {a : G} (ha : a ∈ d.A₁) : a * a ∈ d.ZX₄ := by
  obtain ⟨α, hα, rfl⟩ := ha
  exact ⟨α * α, mul_self_mem_ZX₄sub hα, map_mul _ _ _⟩

omit [Finite G] in
theorem S_comm_mod_F {s a : G} (hs : s ∈ d.S) (ha : a ∈ d.X₄ ⊔ d.F) :
    s * a * s⁻¹ * a⁻¹ ∈ d.F := by
  have ha' : a ∈ d.pull (X₄sub ⊔ Fsub) := by
    rw [d.pull_sup]
    exact ha
  obtain ⟨σ, hσ, rfl⟩ := hs
  obtain ⟨α, hα, rfl⟩ := ha'
  refine ⟨_, (mem_X₄sub_sup_Fsub_iff.1 hα).2 σ hσ, ?_⟩
  simp only [map_mul, map_inv]

theorem R_inf_L (h : d.Hyp) : d.R ⊓ d.L = d.S := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left (d.pull_le_L _))
  obtain ⟨hxR, hxL⟩ := Subgroup.mem_inf.1 hx
  have htS : ∀ s ∈ d.S, d.t * s * d.t ∈ d.S := fun s hs => by
    rw [← h.t_comm_of_mem_L (d.pull_le_L _ hs), mul_assoc, h.t_mul_t, mul_one]
    exact hs
  rcases (mem_sup_zpowers_iff h.t_mul_t htS).1 hxR with hs | hs
  · exact hs
  · exfalso
    apply h.t_not_mem_L
    have := mul_mem (inv_mem hxL) (d.pull_le_L _ hs)
    rwa [inv_mul_cancel_left] at this

theorem R_le_NHS (h : d.Hyp) : d.R ≤ normalizer (d.S : Set G) ⊓ d.H :=
  le_inf h.R_le_normalizer_S h.R_le_H

theorem NHS_le_normalizer_R :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.R : Set G) := fun g hg => by
  obtain ⟨hgS, hgH⟩ := Subgroup.mem_inf.1 hg
  refine mem_normalizer_sup hgS (mem_normalizer_fintype fun x hx => ?_)
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
  rw [(Commute.zpow_right (mem_centralizer_singleton_iff.1 hgH) n).eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) n

omit [Finite G] in
theorem crossed_mul_of_mem_H {n y : G} (hn : n ∈ d.H) :
    n * y * d.t * (n * y)⁻¹ * d.t = n * (y * d.t * y⁻¹ * d.t) * n⁻¹ := by
  have hnt : n⁻¹ * d.t = d.t * n⁻¹ := mem_centralizer_singleton_iff.1 (inv_mem hn)
  calc n * y * d.t * (n * y)⁻¹ * d.t = n * y * d.t * y⁻¹ * (n⁻¹ * d.t) := by group
    _ = n * y * d.t * y⁻¹ * (d.t * n⁻¹) := by rw [hnt]
    _ = n * (y * d.t * y⁻¹ * d.t) * n⁻¹ := by group

theorem le_R_of_isPGroup
    (h : d.Hyp) {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (d.S : Set G) ⊓ d.H)
    (hn : ∀ n ∈ normalizer (d.S : Set G) ⊓ d.H, ∀ q ∈ Q, n * q * n⁻¹ ∈ Q) : Q ≤ d.R := by
  have hQH : Q ≤ d.H := hQN.trans inf_le_right
  let Q' : Subgroup (MulAut SU52) := (Q.subgroupOf d.H).map h.act
  have hQ' : IsPGroup 2 Q' := (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm).map _
  have hQS : ∀ α ∈ Q', ∀ x ∈ Ssub, α x ∈ Ssub := by
    rintro _ ⟨q, hq, rfl⟩ x hx
    have hqS : (q : G) ∈ normalizer (d.S : Set G) := (hQN (Subgroup.mem_subgroupOf.1 hq)).1
    have : d.ι (h.act q x) ∈ d.S := by
      rw [h.ι_act_apply]
      exact (mem_normalizer_iff.1 hqS _).1 ⟨x, hx, rfl⟩
    exact d.ι_mem_pull_iff.1 this
  have he₁ : d.ι e₁SU ∈ normalizer (d.S : Set G) ⊓ d.H :=
    Subgroup.mem_inf.2 ⟨ι_mem_normalizer_pull (Esub_le_normalizer_Ssub
      (mem_sup_left (mem_zpowers _))), h.L_le_H (d.ι_mem _)⟩
  let e : d.H := ⟨d.ι e₁SU, he₁.2⟩
  have hact : h.act e = MulAut.conj e₁SU := MulEquiv.ext fun g => d.ι_injective (by
    rw [h.ι_act_apply, MulAut.conj_apply, ← ι_conj])
  have he : ∀ α ∈ Q', MulAut.conj e₁SU * α * (MulAut.conj e₁SU)⁻¹ ∈ Q' := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨e * q * e⁻¹, ?_, ?_⟩
    · exact hn _ he₁ _ (Subgroup.mem_subgroupOf.1 hq)
    · rw [map_mul, map_mul, map_inv, hact]
  intro q hq
  obtain ⟨s, hs, hqs⟩ := exists_eq_conj_of_mem_of_isPGroup hQ' hQS he
    (⟨⟨q, hQH hq⟩, hq, rfl⟩ : h.act ⟨q, hQH hq⟩ ∈ Q')
  obtain ⟨c, hc, ec⟩ := exists_eq_mul_of_act_eq_conj d.L d.η ⟨q, h.H_le_normalizer (hQH hq)⟩ s hqs
  change q = d.ι s * c at ec
  have hcH : c ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (d.ι_mem s))) (hQH hq)
    rwa [ec, inv_mul_cancel_left] at this
  have hct : c ∈ zpowers d.t := by
    rw [← h.centralizer_inf_H_eq]
    exact Subgroup.mem_inf.2 ⟨hc, hcH⟩
  rw [ec]
  exact mul_mem (mem_sup_left ⟨s, hs, rfl⟩) (mem_sup_right hct)

end Data.Hyp

@[expose] def Data.UR₂ {G : Type} [Group G] (d : Data G) : Subgroup G where
  carrier := {x | x ∈ normalizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) ∧
    x ∈ normalizer (((d.X₄ ⊔ d.F) ⊔ d.V₂ : Subgroup G) : Set G) ∧
    ∀ s ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂, x * s * x⁻¹ * s⁻¹ ∈ d.F ⊔ d.V₂}
  one_mem' := ⟨one_mem _, one_mem _, fun _ _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx₁, hx₂, hx⟩ ⟨hy₁, hy₂, hy⟩
    refine ⟨mul_mem hx₁ hy₁, mul_mem hx₂ hy₂, fun s hs => ?_⟩
    rw [show x * y * s * (x * y)⁻¹ * s⁻¹ =
      x * (y * s * y⁻¹ * s⁻¹) * x⁻¹ * (x * s * x⁻¹ * s⁻¹) by group]
    exact mul_mem ((mem_normalizer_iff.1 hx₁ _).1 (hy s hs)) (hx s hs)
  inv_mem' := by
    rintro x ⟨hx₁, hx₂, hx⟩
    refine ⟨inv_mem hx₁, inv_mem hx₂, fun s hs => ?_⟩
    have hs' : x⁻¹ * s * x ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := by
      have := (mem_normalizer_iff.1 (inv_mem hx₂) s).1 hs
      rwa [inv_inv] at this
    have := inv_mem (hx _ hs')
    rw [inv_inv]
    rwa [show (x * (x⁻¹ * s * x) * x⁻¹ * (x⁻¹ * s * x)⁻¹)⁻¹ = x⁻¹ * s * x * s⁻¹ by group]
      at this

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem FV₂_le_Y
    (h : d.Hyp) :
    d.F ⊔ d.V₂ ≤ d.Y := sup_le h.F_le_Y h.V₂_le_Y

omit [Finite G] in
theorem SV₂_le_R₂ : (d.X₄ ⊔ d.F) ⊔ d.V₂ ≤ d.R₂ :=
  sup_le (XF_le_S.trans (le_sup_left.trans le_sup_left)) le_sup_right

theorem mem_F_iff_FV₂
    (h : d.Hyp) (v : G) :
    v ∈ d.F ↔ v ∈ d.F ⊔ d.V₂ ∧ v * d.t = d.t * v := by
  refine ⟨fun hv => ⟨mem_sup_left hv, h.t_comm_F hv⟩, fun ⟨hv, hvt⟩ => ?_⟩
  obtain ⟨f, hf, w, hw, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun f hf w hw => h.Y_comm (h.F_le_Y hf) (h.V₂_le_Y hw)) hv
  have hwH : w ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (h.F_le_L hf))) (mem_centralizer_singleton_iff.2 hvt)
    rwa [inv_mul_cancel_left] at this
  have hwZ : w ∈ d.Z₂ := by
    rw [← h.V₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨hw, hwH⟩
  exact mul_mem hf (Z₂_le_F hwZ)

theorem crossed_mem_F_of_mem_Y
    (h : d.Hyp) {y : G}
    (hy : y ∈ d.Y) : y * d.t * y⁻¹ * d.t ∈ d.F := by
  have := h.U_crossed_mem_F (h.E₂_le_U (h.Y_eq_E₂ ▸ inv_mem hy))
  rwa [inv_inv] at this

theorem crossed_mem_F_of_mem_NHSY
    (h : d.Hyp) {x : G}
    (hx : x ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) : x * d.t * x⁻¹ * d.t ∈ d.F := by
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.Y
    h.NHS_le_normalizer_Y
  have hmem : x ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact hx
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.1 hmem
  rw [crossed_mul_of_mem_H (Subgroup.mem_inf.1 hn).2]
  exact (mem_normalizer_iff.1 (normalizer_S_le_normalizer_F (Subgroup.mem_inf.1 hn).1) _).1
    (h.crossed_mem_F_of_mem_Y hy)

theorem crossed_mul_eq (h : d.Hyp) (u x : G) :
    u * x * d.t * (u * x)⁻¹ * d.t = u * (x * d.t * x⁻¹ * d.t) * u⁻¹ * (u * d.t * u⁻¹ * d.t) := by
  calc u * x * d.t * (u * x)⁻¹ * d.t = u * x * d.t * x⁻¹ * (d.t * d.t) * u⁻¹ * d.t := by
        rw [h.t_mul_t]
        group
    _ = _ := by group

theorem R₃_inf_NHS_le
    (h : d.Hyp) :
    d.R₃ ⊓ (normalizer (d.S : Set G) ⊓ d.H) ≤ d.R :=
  h.le_R_of_isPGroup ((isPGroup_oTwo _).to_le inf_le_left) inf_le_right fun _ hn' _ hq' =>
    Subgroup.mem_inf.2 ⟨conj_mem_oTwo (h.NHS_le_normalizer_R₂ hn') (Subgroup.mem_inf.1 hq').1,
      mul_mem (mul_mem hn' (Subgroup.mem_inf.1 hq').2) (inv_mem hn')⟩

theorem D₃_inf_R
    (h : d.Hyp) :
    d.D₃ ⊓ d.R = d.A₁ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (fun a ha => h.AW_le_D₃ (mem_sup_left ha))
    fun a ha => mem_sup_left (d.A₁_le_S ha))
  rw [← h.D₁_inf_H]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2,
    h.R_le_H (Subgroup.mem_inf.1 hx).2⟩

theorem NHSY_le_normalizer_RY
    (h : d.Hyp) :
    (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y ≤ normalizer ((d.R ⊔ d.Y : Subgroup G) : Set G) :=
  sup_le (fun _ hg => mem_normalizer_sup (NHS_le_normalizer_R hg) (h.NHS_le_normalizer_Y hg))
    (le_sup_right.trans (d.R ⊔ d.Y).le_normalizer)

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem normalizer_R₂_le_normalizer_FV₂
    (h : d.Hyp) :
    normalizer (d.R₂ : Set G) ≤ normalizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) := fun x hx => by
  rw [← R₂_inf_centralizer_eq h]
  exact mem_normalizer_fintype fun y hy => conj_mem_inf_centralizer hx
    (mem_normalizer_fintype fun z hz => conj_mem_commutator_self_of_mem_normalizer hx hz) hy

theorem normalizer_R₂_le_normalizer_SV₂
    (h : d.Hyp) :
    normalizer (d.R₂ : Set G) ≤ normalizer (((d.X₄ ⊔ d.F) ⊔ d.V₂ : Subgroup G) : Set G) :=
    fun x hx => by
  have hxD : x ∈ normalizer ((⁅d.R₂, d.R₂⁆ : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun z hz => conj_mem_commutator_self_of_mem_normalizer hx hz
  have hXV : (d.X₄ ⊔ d.F) ⊔ d.V₂ = ⁅d.R₂, d.R₂⁆ ⊔ (d.F ⊔ d.V₂) := by
    rw [commutator_R₂_eq h]
    refine le_antisymm (sup_le (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_right))
      (sup_le (sup_le le_sup_left (h.W_le_V₂.trans le_sup_right)) (sup_le
        ((le_sup_right : d.F ≤ d.X₄ ⊔ d.F).trans le_sup_left) le_sup_right))
  rw [hXV]
  exact mem_normalizer_sup hxD (h.normalizer_R₂_le_normalizer_FV₂ hx)

theorem Y_le_normalizer_R₂
    (h : d.Hyp) :
    d.Y ≤ normalizer (d.R₂ : Set G) := fun _ hy =>
  le_normalizer_of_card_eq_two_mul (H := d.R₂) (sup_le le_sup_left
    (h.V₂_le_Y.trans le_sup_right)) (by rw [h.card_RY, h.card_R₂]; norm_num) (mem_sup_right hy)

theorem t_conj_mem_FV₂
    (h : d.Hyp) :
    ∀ v ∈ d.F ⊔ d.V₂, d.t * v * d.t ∈ d.F ⊔ d.V₂ := by
  have htN : d.t ∈ normalizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) := by
    refine mem_normalizer_sup (mem_normalizer_fintype fun f hf => ?_)
      (mem_normalizer_fintype fun v hv => ?_)
    · rw [← h.t_comm_F hf, mul_inv_cancel_right]
      exact hf
    · rw [h.t_inv, show d.t * v * d.t = v * (v⁻¹ * d.t * v * d.t) by group]
      exact mul_mem hv (h.Z₂_le_V₂ (h.crossed_mem_Z₂_of_mem_V₂ hv))
  intro v hv
  have := (mem_normalizer_iff.1 htN v).1 hv
  rwa [h.t_inv] at this

theorem mem_normalizer_withT_F_of_crossed_mem
    (h : d.Hyp) {x : G} (hx : x ∈ normalizer (d.R₂ : Set G))
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.F ⊔ d.V₂) :
    x ∈ normalizer ((d.withT d.F : Subgroup G) : Set G) := by
  have hxV := h.normalizer_R₂_le_normalizer_FV₂ hx
  have hxVt : x ∈ normalizer (((d.F ⊔ d.V₂) ⊔ zpowers d.t : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun k hk => ?_
    have hle : (d.F ⊔ d.V₂) ⊔ zpowers d.t ≤
        ((d.F ⊔ d.V₂) ⊔ zpowers d.t).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le (fun v hv => ?_) ?_
      · change x * v * x⁻¹ ∈ (d.F ⊔ d.V₂) ⊔ zpowers d.t
        exact mem_sup_left ((mem_normalizer_iff.1 hxV v).1 hv)
      · rw [zpowers_le]
        change x * d.t * x⁻¹ ∈ (d.F ⊔ d.V₂) ⊔ zpowers d.t
        rw [show x * d.t * x⁻¹ = (x * d.t * x⁻¹ * d.t) * d.t by
          rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
        exact mul_mem (mem_sup_left hθ) (mem_sup_right (mem_zpowers _))
    exact hle hk
  exact mem_normalizer_sup_zpowers_of_elem h.t_mul_t (fun ht => h.t_not_mem_Y (h.FV₂_le_Y ht))
    h.t_conj_mem_FV₂ (fun v hv => h.Y_sq (h.FV₂_le_Y hv)) h.mem_F_iff_FV₂ hxVt hxV

theorem mem_NHS_of_mem_normalizer_R₂
    (h : d.Hyp) {n : G} (hn : n ∈ normalizer (d.R₂ : Set G))
    (hnH : n ∈ d.H) : n ∈ normalizer (d.S : Set G) ⊓ d.H := by
  refine Subgroup.mem_inf.2 ⟨mem_normalizer_fintype fun s hs => ?_, hnH⟩
  have hsR₂ : s ∈ d.R₂ := mem_sup_left (mem_sup_left hs)
  have hsH : s ∈ d.H := h.L_le_H (d.pull_le_L _ hs)
  have h1 : n * s * n⁻¹ ∈ d.R₂ ⊓ d.H := Subgroup.mem_inf.2
    ⟨(mem_normalizer_iff.1 hn s).1 hsR₂, mul_mem (mul_mem hnH hsH) (inv_mem hnH)⟩
  rw [h.R₂_inf_H] at h1
  have h2 : n * s * n⁻¹ ∈ d.L :=
    (mem_normalizer_iff.1 (h.H_le_normalizer hnH) s).1 (d.pull_le_L _ hs)
  rw [← h.R_inf_L]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem mem_NHSY_of_crossed_mem
    (h : d.Hyp) {x : G} (hx : x ∈ normalizer (d.R₂ : Set G))
    (hθ : x * d.t * x⁻¹ * d.t ∈ d.F ⊔ d.V₂) :
    x ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y := by
  have h1 := h.normalizer_withT_F_le_NHA₂Y (h.mem_normalizer_withT_F_of_crossed_mem hx hθ)
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.A₂ : Set G) ⊓ d.H) d.Y
    h.NHA₂_le_normalizer_Y
  have hmem : x ∈ ((normalizer (d.A₂ : Set G) ⊓ d.H : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact h1
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.1 hmem
  have hnR : n ∈ normalizer (d.R₂ : Set G) := by
    have := mul_mem hx (inv_mem (h.Y_le_normalizer_R₂ hy))
    rwa [mul_inv_cancel_right] at this
  exact mul_mem (mem_sup_left (h.mem_NHS_of_mem_normalizer_R₂ hnR (Subgroup.mem_inf.1 hn).2))
    (mem_sup_right hy)

theorem exists_D₃_mul_mem
    (h : d.Hyp) {x : G}
    (hx : x ∈ normalizer (d.R₂ : Set G)) :
    ∃ u ∈ d.D₃, u * x ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y := by
  have hθ := h.crossed_mem_of_mem_normalizer_R₂ hx
  rw [sup_assoc] at hθ
  obtain ⟨k, hk, m, hm, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun k hk m hm => h.XF_comm_Y (mem_sup_left hk) (h.FV₂_le_Y hm)) hθ
  obtain ⟨u, hu, w, hw, eu⟩ := h.exists_D₃_conj_t (inv_mem (mem_sup_right hk : k ∈ d.X₃ ⊔ d.X₄))
  obtain ⟨huN, huD⟩ := Subgroup.mem_inf.1 hu
  have hw' : u * k * u⁻¹ * k⁻¹ ∈ d.W := by
    have := ((mem_UA₁_iff.1 (Subgroup.mem_inf.1 huD).1).2 k⁻¹
      (inv_mem (d.pull_mono X₄sub_le_A₁sub' hk))).1
    rw [inv_inv] at this
    have := inv_mem this
    rwa [show (k * u * k⁻¹ * u⁻¹)⁻¹ = u * k * u⁻¹ * k⁻¹ by group] at this
  have hm' : u * m * u⁻¹ ∈ d.F ⊔ d.V₂ :=
    (mem_normalizer_iff.1 (h.normalizer_R₂_le_normalizer_FV₂ huN) m).1 hm
  have hkc : k * (u * m * u⁻¹) = (u * m * u⁻¹) * k :=
    h.XF_comm_Y (mem_sup_left hk) (h.FV₂_le_Y hm')
  refine ⟨u, hu, h.mem_NHSY_of_crossed_mem (mul_mem huN hx) ?_⟩
  rw [h.crossed_mul_eq, ← e, eu, show u * (k * m) * u⁻¹ * (k⁻¹ * w) =
    (u * k * u⁻¹ * k⁻¹) * (k * (u * m * u⁻¹)) * k⁻¹ * w by group, hkc,
    show (u * k * u⁻¹ * k⁻¹) * ((u * m * u⁻¹) * k) * k⁻¹ * w =
      (u * k * u⁻¹ * k⁻¹) * (u * m * u⁻¹) * w by group]
  exact mul_mem (mul_mem (mem_sup_right (h.W_le_V₂ hw')) hm') (mem_sup_right (h.W_le_V₂ hw))

theorem normalizer_R₂_eq
    (h : d.Hyp) :
    normalizer (d.R₂ : Set G) = ((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊔ d.D₃ := by
  refine le_antisymm (fun x hx => ?_) (sup_le (sup_le h.NHS_le_normalizer_R₂
    h.Y_le_normalizer_R₂) fun _ hu => (Subgroup.mem_inf.1 hu).1)
  obtain ⟨u, hu, hux⟩ := h.exists_D₃_mul_mem hx
  have := mul_mem (mem_sup_right (inv_mem hu)) (mem_sup_left hux :
    u * x ∈ ((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊔ d.D₃)
  rwa [inv_mul_cancel_left] at this

theorem conj_mem_UR₂
    (h : d.Hyp) {g x : G}
    (hg : g ∈ normalizer (d.R₂ : Set G)) (hx : x ∈ d.UR₂) : g * x * g⁻¹ ∈ d.UR₂ := by
  obtain ⟨hx₁, hx₂, hx⟩ := hx
  have hg₁ := h.normalizer_R₂_le_normalizer_FV₂ hg
  have hg₂ := h.normalizer_R₂_le_normalizer_SV₂ hg
  refine ⟨mul_mem (mul_mem hg₁ hx₁) (inv_mem hg₁), mul_mem (mul_mem hg₂ hx₂) (inv_mem hg₂),
    fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := by
    have := (mem_normalizer_iff.1 (inv_mem hg₂) s).1 hs
    rwa [inv_inv] at this
  have := (mem_normalizer_iff.1 hg₁ _).1 (hx _ hs')
  rwa [show g * (x * (g⁻¹ * s * g) * x⁻¹ * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
    g * x * g⁻¹ * s * (g * x * g⁻¹)⁻¹ * s⁻¹ by group] at this

theorem R_le_UR₂
    (h : d.Hyp) :
    d.R ≤ d.UR₂ := by
  have hRN : ∀ r ∈ d.R, r ∈ normalizer (d.R₂ : Set G) := fun r hr =>
    (d.R₂).le_normalizer (mem_sup_left hr)
  have hdec : ∀ k ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂, ∃ a ∈ d.X₄ ⊔ d.F, ∃ m ∈ d.V₂, a * m = k := fun k hk =>
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha m hm => (h.Y_comm_XFW (h.V₂_le_Y hm) (mem_sup_left ha)).symm) hk
  refine sup_le (fun s hs => ⟨h.normalizer_R₂_le_normalizer_FV₂ (hRN s (mem_sup_left hs)),
    h.normalizer_R₂_le_normalizer_SV₂ (hRN s (mem_sup_left hs)), fun k hk => ?_⟩)
    (zpowers_le.2 ⟨h.normalizer_R₂_le_normalizer_FV₂ (hRN _ (mem_sup_right (mem_zpowers _))),
      h.normalizer_R₂_le_normalizer_SV₂ (hRN _ (mem_sup_right (mem_zpowers _))),
      fun k hk => ?_⟩)
  · obtain ⟨a, ha, m, hm, rfl⟩ := hdec k hk
    have h1 := S_comm_mod_F hs ha
    have h2 := ((h.mem_V₂_iff).1 hm).2 s hs
    have h3 : a * (s * m * s⁻¹ * m⁻¹) * a⁻¹ = s * m * s⁻¹ * m⁻¹ := by
      rw [h.XF_comm_Y ha (d.W_le_Y h2), mul_inv_cancel_right]
    rw [show s * (a * m) * s⁻¹ * (a * m)⁻¹ =
      (s * a * s⁻¹ * a⁻¹) * (a * (s * m * s⁻¹ * m⁻¹) * a⁻¹) by group, h3]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (h.W_le_V₂ h2))
  · obtain ⟨a, ha, m, hm, rfl⟩ := hdec k hk
    have hat : d.t * a = a * d.t := (h.t_comm_of_mem_L (d.pull_le_L _ (XF_le_S ha))).symm
    have hz : m * d.t * m⁻¹ * d.t ∈ d.Z₂ := by
      have := h.crossed_mem_Z₂_of_mem_V₂ (inv_mem hm)
      rwa [inv_inv] at this
    have hz' : d.t * m * d.t⁻¹ * m⁻¹ ∈ d.F := by
      have := inv_mem (Z₂_le_F hz)
      rwa [show (m * d.t * m⁻¹ * d.t)⁻¹ = d.t * m * d.t⁻¹ * m⁻¹ by
        simp only [mul_inv_rev, inv_inv, h.t_inv, mul_assoc]] at this
    have h3 : a * (d.t * m * d.t⁻¹ * m⁻¹) * a⁻¹ = d.t * m * d.t⁻¹ * m⁻¹ := by
      rw [h.XF_comm_Y ha (h.F_le_Y hz'), mul_inv_cancel_right]
    rw [show d.t * (a * m) * d.t⁻¹ * (a * m)⁻¹ = (d.t * a) * m * d.t⁻¹ * m⁻¹ * a⁻¹ by group,
      hat, show a * d.t * m * d.t⁻¹ * m⁻¹ * a⁻¹ = a * (d.t * m * d.t⁻¹ * m⁻¹) * a⁻¹ by group, h3]
    exact mem_sup_left hz'

theorem Y_le_UR₂
    (h : d.Hyp) :
    d.Y ≤ d.UR₂ := fun y hy => by
  have hyN := h.Y_le_normalizer_R₂ hy
  refine ⟨h.normalizer_R₂_le_normalizer_FV₂ hyN, h.normalizer_R₂_le_normalizer_SV₂ hyN,
    fun k hk => ?_⟩
  obtain ⟨a, ha, m, hm, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha m hm => (h.Y_comm_XFW (h.V₂_le_Y hm) (mem_sup_left ha)).symm) hk
  have hya : y * (a * m) = (a * m) * y := by
    rw [← mul_assoc, ← h.XF_comm_Y ha hy, mul_assoc, h.Y_comm hy (h.V₂_le_Y hm), mul_assoc]
  rw [hya, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem D₃_le_UR₂
    (h : d.Hyp) :
    d.D₃ ≤ d.UR₂ := fun u hu => by
  obtain ⟨huN, huD⟩ := Subgroup.mem_inf.1 hu
  have huV := h.normalizer_R₂_le_normalizer_FV₂ huN
  refine ⟨huV, h.normalizer_R₂_le_normalizer_SV₂ huN, fun k hk => ?_⟩
  rw [sup_assoc] at hk
  obtain ⟨a, ha, m, hm, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha m hm => h.XF_comm_Y (mem_sup_left ha) (h.FV₂_le_Y hm)) hk
  have hw : u * a * u⁻¹ * a⁻¹ ∈ d.W := by
    have := ((mem_UA₁_iff.1 (Subgroup.mem_inf.1 huD).1).2 a⁻¹
      (inv_mem (d.pull_mono X₄sub_le_A₁sub' ha))).1
    rw [inv_inv] at this
    have := inv_mem this
    rwa [show (a * u * a⁻¹ * u⁻¹)⁻¹ = u * a * u⁻¹ * a⁻¹ by group] at this
  have hm' : u * m * u⁻¹ * m⁻¹ ∈ d.F ⊔ d.V₂ :=
    mul_mem ((mem_normalizer_iff.1 huV m).1 hm) (inv_mem hm)
  have h3 : a * (u * m * u⁻¹ * m⁻¹) * a⁻¹ = u * m * u⁻¹ * m⁻¹ := by
    rw [h.XF_comm_Y (mem_sup_left ha) (h.FV₂_le_Y hm'), mul_inv_cancel_right]
  rw [show u * (a * m) * u⁻¹ * (a * m)⁻¹ =
    (u * a * u⁻¹ * a⁻¹) * (a * (u * m * u⁻¹ * m⁻¹) * a⁻¹) by group, h3]
  exact mul_mem (mem_sup_right (h.W_le_V₂ hw)) hm'

theorem crossed_conj_mem_FV₂
    (h : d.Hyp) {u x : G}
    (hu : u ∈ d.D₃) (hx : x ∈ d.UR₂) (hθ : x * d.t * x⁻¹ * d.t ∈ d.F ⊔ d.V₂) :
    u * x * u⁻¹ * d.t * (u * x * u⁻¹)⁻¹ * d.t ∈ d.F ⊔ d.V₂ := by
  have huU := h.D₃_le_UR₂ hu
  have huN := (Subgroup.mem_inf.1 hu).1
  have hσ := h.crossed_mem_of_mem_normalizer_R₂ huN
  have hT : ∀ g : G, g * d.t * g⁻¹ * d.t = g * d.t * g⁻¹ * d.t⁻¹ := fun g => by rw [h.t_inv]
  rw [hT] at hθ hσ ⊢
  set σ := u * d.t * u⁻¹ * d.t⁻¹ with hσdef
  have hx' : u * x * u⁻¹ ∈ d.UR₂ := mul_mem (mul_mem huU hx) (inv_mem huU)
  have hc := hx'.2.2 σ⁻¹ (inv_mem hσ)
  rw [inv_inv] at hc
  have hσN : σ ∈ normalizer ((d.F ⊔ d.V₂ : Subgroup G) : Set G) :=
    h.normalizer_R₂_le_normalizer_FV₂ ((d.R₂).le_normalizer (SV₂_le_R₂ hσ))
  have h2 : σ⁻¹ * (u * (x * d.t * x⁻¹ * d.t⁻¹) * u⁻¹) * σ ∈ d.F ⊔ d.V₂ := by
    have := (mem_normalizer_iff.1 (inv_mem hσN) _).1
      ((mem_normalizer_iff.1 (h.normalizer_R₂_le_normalizer_FV₂ huN) _).1 hθ)
    rwa [inv_inv] at this
  rw [show u * x * u⁻¹ * d.t * (u * x * u⁻¹)⁻¹ * d.t⁻¹ =
    (u * x * u⁻¹ * σ⁻¹ * (u * x * u⁻¹)⁻¹ * σ) *
      (σ⁻¹ * (u * (x * d.t * x⁻¹ * d.t⁻¹) * u⁻¹) * σ) by rw [hσdef]; group]
  exact mul_mem hc h2

theorem D₃_le_normalizer_M
    (h : d.Hyp) :
    d.D₃ ≤ normalizer ((((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊓ d.UR₂ : Subgroup G) :
      Set G) := fun u hu => mem_normalizer_fintype fun x hx => by
  obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.1 hx
  have huN := (Subgroup.mem_inf.1 hu).1
  have hxN : x ∈ normalizer (d.R₂ : Set G) :=
    (sup_le h.NHS_le_normalizer_R₂ h.Y_le_normalizer_R₂) hxK
  refine Subgroup.mem_inf.2 ⟨h.mem_NHSY_of_crossed_mem (mul_mem (mul_mem huN hxN) (inv_mem huN))
    (h.crossed_conj_mem_FV₂ hu hxU (mem_sup_left (h.crossed_mem_F_of_mem_NHSY hxK))),
    mul_mem (mul_mem (h.D₃_le_UR₂ hu) hxU) (inv_mem (h.D₃_le_UR₂ hu))⟩

theorem NHS_le_normalizer_M
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤
      normalizer ((((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊓ d.UR₂ : Subgroup G) : Set G) :=
    fun n hn => mem_normalizer_fintype fun x hx => by
  obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.1 hx
  have hnK : n ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y := mem_sup_left hn
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hnK hxK) (inv_mem hnK),
    h.conj_mem_UR₂ (h.NHS_le_normalizer_R₂ hn) hxU⟩

theorem oTwo_M_eq
    (h : d.Hyp) :
    oTwo (((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊓ d.UR₂) = d.R ⊔ d.Y := by
  set M := ((normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y) ⊓ d.UR₂ with hM
  have hRYM : d.R ⊔ d.Y ≤ M := le_inf (sup_le_sup_right h.R_le_NHS _)
    (sup_le h.R_le_UR₂ h.Y_le_UR₂)
  have hRY2 : IsPGroup 2 (d.R ⊔ d.Y : Subgroup G) := IsPGroup.of_card h.card_RY
  have hge : d.R ⊔ d.Y ≤ oTwo M :=
    le_oTwo hRYM (inf_le_left.trans h.NHSY_le_normalizer_RY) hRY2
  refine le_antisymm (fun q hq => ?_) hge
  have hqK : q ∈ (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y := (inf_le_left : M ≤ _) (oTwo_le M hq)
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.Y
    h.NHS_le_normalizer_Y
  have hmem : q ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact hqK
  obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.1 hmem
  have hnO : n ∈ oTwo M := by
    have := mul_mem hq (inv_mem (hge (mem_sup_right hy)))
    rwa [mul_inv_cancel_right] at this
  have hQ : oTwo M ⊓ (normalizer (d.S : Set G) ⊓ d.H) ≤ d.R := h.le_R_of_isPGroup
    ((isPGroup_oTwo M).to_le inf_le_left) inf_le_right fun n' hn' q' hq' =>
      Subgroup.mem_inf.2 ⟨conj_mem_oTwo_of_mem_normalizer' (h.NHS_le_normalizer_M hn')
        (Subgroup.mem_inf.1 hq').1, mul_mem (mul_mem hn' (Subgroup.mem_inf.1 hq').2)
          (inv_mem hn')⟩
  exact mul_mem (mem_sup_left (hQ (Subgroup.mem_inf.2 ⟨hnO, hn⟩))) (mem_sup_right hy)

theorem D₃_le_normalizer_RY
    (h : d.Hyp) :
    d.D₃ ≤ normalizer ((d.R ⊔ d.Y : Subgroup G) : Set G) := fun u hu =>
  mem_normalizer_fintype fun x hx => by
    rw [← h.oTwo_M_eq] at hx ⊢
    exact conj_mem_oTwo_of_mem_normalizer' (h.D₃_le_normalizer_M hu) hx

theorem RY_inf_D₃
    (h : d.Hyp) :
    (d.R ⊔ d.Y) ⊓ d.D₃ = d.A₁ ⊔ d.V₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le (fun a ha => mem_sup_left (mem_sup_left
    (d.A₁_le_S ha))) (h.V₂_le_Y.trans le_sup_right)) (sup_le (fun a ha => h.AW_le_D₃
      (mem_sup_left ha)) h.V₂_le_D₃))
  obtain ⟨hxRY, hxD⟩ := Subgroup.mem_inf.1 hx
  rw [← (h.sec4_11_4).1]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxD).2,
    (sup_le_sup_right h.R_le_NHS _) hxRY⟩

theorem card_RYD₃
    (h : d.Hyp) :
    Nat.card ((d.R ⊔ d.Y) ⊔ d.D₃ : Subgroup G) = 2 ^ 17 := by
  have e := card_sup_mul_card_inf_of_le_normalizer (d.R ⊔ d.Y) d.D₃ h.D₃_le_normalizer_RY
  rw [h.RY_inf_D₃, h.card_RY, h.card_D₃, h.card_A₁V₂] at e
  norm_num at e ⊢
  omega

theorem NHSY_le_normalizer_RYD₃
    (h : d.Hyp) :
    (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.Y ≤
      normalizer (((d.R ⊔ d.Y) ⊔ d.D₃ : Subgroup G) : Set G) :=
  sup_le (fun _ hg => mem_normalizer_sup (h.NHSY_le_normalizer_RY (mem_sup_left hg))
      (mem_normalizer_fintype fun _ hu => h.conj_mem_D₃ hg hu))
    ((le_sup_right.trans le_sup_left).trans ((d.R ⊔ d.Y) ⊔ d.D₃).le_normalizer)

theorem R₃_eq
    (h : d.Hyp) :
    d.R₃ = (d.R ⊔ d.Y) ⊔ d.D₃ := by
  set P := (d.R ⊔ d.Y) ⊔ d.D₃ with hP
  have hPN : P ≤ normalizer (d.R₂ : Set G) := sup_le (sup_le (fun _ hr => (d.R₂).le_normalizer
    (mem_sup_left hr)) h.Y_le_normalizer_R₂) fun _ hu => (Subgroup.mem_inf.1 hu).1
  have hNP : normalizer (d.R₂ : Set G) ≤ normalizer (P : Set G) := by
    rw [h.normalizer_R₂_eq]
    exact sup_le h.NHSY_le_normalizer_RYD₃ (le_sup_right.trans P.le_normalizer)
  have hle : P ≤ d.R₃ := le_oTwo hPN hNP (IsPGroup.of_card h.card_RYD₃)
  refine le_antisymm (fun q hq => ?_) hle
  obtain ⟨u, hu, huq⟩ := h.exists_D₃_mul_mem (oTwo_le _ hq)
  have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.Y
    h.NHS_le_normalizer_Y
  have hmem : u * q ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset]
    exact huq
  obtain ⟨n, hn, y, hy, e⟩ := Set.mem_mul.1 hmem
  have hnR₃ : n ∈ d.R₃ := by
    rw [show n = u * q * y⁻¹ by rw [← e]; group]
    exact mul_mem (mul_mem (hle (mem_sup_right hu)) hq)
      (inv_mem (hle (mem_sup_left (mem_sup_right hy))))
  have hnP : n ∈ P :=
    mem_sup_left (mem_sup_left (h.R₃_inf_NHS_le (Subgroup.mem_inf.2 ⟨hnR₃, hn⟩)))
  rw [show q = u⁻¹ * (n * y) by rw [e]; group]
  exact mul_mem (mem_sup_right (inv_mem hu)) (mul_mem hnP (mem_sup_left (mem_sup_right hy)))

theorem sec4_13_2
    (h : d.Hyp) :
    normalizer (d.R₂ : Set G) = (normalizer (d.S : Set G) ⊓ d.H) ⊔ d.R₃ ∧
      d.R₃ ⊓ d.H = d.R ∧ d.R₃ = (d.R ⊔ d.Y) ⊔ d.D₃ := by
  have hRle : d.R ≤ d.R₃ := by
    rw [h.R₃_eq]
    exact le_sup_left.trans le_sup_left
  refine ⟨le_antisymm ?_ (sup_le h.NHS_le_normalizer_R₂ (oTwo_le _)), le_antisymm
    (fun x hx => ?_) (le_inf hRle h.R_le_H), h.R₃_eq⟩
  · rw [h.normalizer_R₂_eq, h.R₃_eq]
    exact sup_le (sup_le le_sup_left (((le_sup_right : d.Y ≤ d.R ⊔ d.Y).trans
      (le_sup_left : d.R ⊔ d.Y ≤ (d.R ⊔ d.Y) ⊔ d.D₃)).trans le_sup_right))
      ((le_sup_right : d.D₃ ≤ (d.R ⊔ d.Y) ⊔ d.D₃).trans le_sup_right)
  · obtain ⟨hxR₃, hxH⟩ := Subgroup.mem_inf.1 hx
    have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 hxH
    have hθ : x * d.t * x⁻¹ * d.t = 1 := by
      rw [hxt, mul_inv_cancel_right, h.t_mul_t]
    have hxK := h.mem_NHSY_of_crossed_mem (oTwo_le _ hxR₃) (by rw [hθ]; exact one_mem _)
    have hset := coe_mul_of_left_le_normalizer_right (normalizer (d.S : Set G) ⊓ d.H) d.Y
      h.NHS_le_normalizer_Y
    have hmem : x ∈ ((normalizer (d.S : Set G) ⊓ d.H : Subgroup G) : Set G) * (d.Y : Set G) := by
      rw [← hset]
      exact hxK
    obtain ⟨n, hn, y, hy, rfl⟩ := Set.mem_mul.1 hmem
    rw [crossed_mul_of_mem_H (Subgroup.mem_inf.1 hn).2] at hθ
    have hy1 : y * d.t * y⁻¹ * d.t = 1 := by
      calc y * d.t * y⁻¹ * d.t = n⁻¹ * (n * (y * d.t * y⁻¹ * d.t) * n⁻¹) * n := by group
        _ = 1 := by rw [hθ]; group
    have hyt : y * d.t = d.t * y := by
      calc y * d.t = (y * d.t * y⁻¹ * d.t) * (d.t * y) := by
            rw [show y * d.t * y⁻¹ * d.t * (d.t * y) = y * d.t * y⁻¹ * (d.t * d.t) * y by group,
              h.t_mul_t]
            group
        _ = d.t * y := by rw [hy1, one_mul]
    have hyR : y ∈ d.R :=
      mem_sup_left (d.A₂_le_S (d.F_le_A₂ ((h.mem_F_iff_Y y).2 ⟨hy, hyt⟩)))
    have hnR₃ : n ∈ d.R₃ := by
      have := mul_mem hxR₃ (inv_mem (hRle hyR))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (h.R₃_inf_NHS_le (Subgroup.mem_inf.2 ⟨hnR₃, hn⟩)) hyR

theorem R_le_normalizer_D₃
    (h : d.Hyp) :
    d.R ≤ normalizer (d.D₃ : Set G) := fun _ hr =>
  mem_normalizer_fintype fun _ hu => h.conj_mem_D₃ (h.R_le_NHS hr) hu

theorem card_RD₃
    (h : d.Hyp) :
    Nat.card (d.R ⊔ d.D₃ : Subgroup G) = 2 ^ 16 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.D₃ d.R h.R_le_normalizer_D₃
  rw [h.D₃_inf_R, sup_comm, h.card_D₃, h.card_R, d.card_A₁] at e
  norm_num at e ⊢
  omega

theorem RY_inf_RD₃
    (h : d.Hyp) :
    (d.R ⊔ d.Y) ⊓ (d.R ⊔ d.D₃) = d.R₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le le_sup_left
    (h.V₂_le_Y.trans le_sup_right)) (sup_le le_sup_left (h.V₂_le_D₃.trans le_sup_right)))
  obtain ⟨hxRY, hxRD⟩ := Subgroup.mem_inf.1 hx
  have hset := coe_mul_of_right_le_normalizer_left d.D₃ d.R h.R_le_normalizer_D₃
  have hmem : x ∈ (d.D₃ : Set G) * (d.R : Set G) := by
    rw [← hset, sup_comm]
    exact hxRD
  obtain ⟨u, hu, r, hr, rfl⟩ := Set.mem_mul.1 hmem
  have huRY : u ∈ d.R ⊔ d.Y := by
    have := mul_mem hxRY (inv_mem (mem_sup_left hr : r ∈ d.R ⊔ d.Y))
    rwa [mul_inv_cancel_right] at this
  have huA : u ∈ d.A₁ ⊔ d.V₂ := by
    rw [← h.RY_inf_D₃]
    exact Subgroup.mem_inf.2 ⟨huRY, hu⟩
  exact mul_mem ((sup_le (fun a ha => mem_sup_left (mem_sup_left (d.A₁_le_S ha)))
    le_sup_right : d.A₁ ⊔ d.V₂ ≤ d.R₂) huA) (mem_sup_left hr)

theorem mul_self_mem_R₂_of_mem_R₃
    (h : d.Hyp) {x : G} (hx : x ∈ d.R₃) : x * x ∈ d.R₂ := by
  rw [h.R₃_eq] at hx
  have hset := coe_mul_of_right_le_normalizer_left (d.R ⊔ d.Y) d.D₃ h.D₃_le_normalizer_RY
  have hmem : x ∈ ((d.R ⊔ d.Y : Subgroup G) : Set G) * (d.D₃ : Set G) := by
    rw [← hset]
    exact hx
  obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.1 hmem
  have huN := (Subgroup.mem_inf.1 hu).1
  have huD := (Subgroup.mem_inf.1 hu).2
  have hR₂RY : d.R₂ ≤ d.R ⊔ d.Y := sup_le le_sup_left (h.V₂_le_Y.trans le_sup_right)
  have hc : Nat.card (d.R ⊔ d.Y : Subgroup G) = 2 * Nat.card d.R₂ := by
    rw [h.card_RY, h.card_R₂]
    norm_num
  have hu2 : u * u ∈ d.R₂ := by
    obtain ⟨w, hw, e⟩ := h.crossed_mul_mem (Subgroup.mem_inf.1 huD).1 (D₁_le_XW huD)
    obtain ⟨a, ha, w₀, hw₀, ea⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha w hw => h.X₃₄_comm_W ha hw) (h.crossed_mem_of_mem_D₃ hu)
    have hθ : u * u * d.t * (u * u)⁻¹ * d.t ∈ d.W := by
      rw [e, ← ea, show a * w₀ * (a * w₀) * w = (a * a) * (w₀ * w₀) * w by
        rw [show a * w₀ * (a * w₀) = a * (w₀ * a) * w₀ by group, ← h.X₃₄_comm_W ha hw₀]
        group]
      exact mul_mem (mul_mem (h.ZX₄_le_W (mul_self_mem_ZX₄ (X₃₄_le_A₁ ha)))
        (mul_mem hw₀ hw₀)) hw
    exact (sup_le (fun a ha => mem_sup_left (mem_sup_left (d.A₁_le_S ha)))
      (h.W_le_V₂.trans le_sup_right) : d.AW ≤ d.R₂)
      ((h.crossed_mem_W_iff_of_mem_D₁ (mul_mem huD huD)).1 hθ)
  have hm' : u * m * u⁻¹ ∈ d.R ⊔ d.Y :=
    (mem_normalizer_iff.1 (h.D₃_le_normalizer_RY hu) m).1 hm
  have hmm : m * (u * m * u⁻¹) ∈ d.R₂ := by
    by_cases hmR : m ∈ d.R₂
    · exact mul_mem hmR ((mem_normalizer_iff.1 huN m).1 hmR)
    · refine mul_mem_of_card_eq_two_mul hR₂RY hc hm hm' hmR fun h' => hmR ?_
      have := (mem_normalizer_iff.1 (inv_mem huN) _).1 h'
      rwa [show u⁻¹ * (u * m * u⁻¹) * u⁻¹⁻¹ = m by group] at this
  rw [show m * u * (m * u) = m * (u * m * u⁻¹) * (u * u) by group]
  exact mul_mem hmm hu2

theorem sec4_13_3
    (h : d.Hyp) :
    (d.R ⊔ d.Y) ⊓ (d.R ⊔ d.D₃) = d.R₂ ∧ (d.R ⊔ d.Y) ⊔ (d.R ⊔ d.D₃) = d.R₃ ∧
      Nat.card d.R₂ = 2 ^ 14 ∧ Nat.card (d.R ⊔ d.Y : Subgroup G) = 2 ^ 15 ∧
      Nat.card (d.R ⊔ d.D₃ : Subgroup G) = 2 ^ 16 ∧ Nat.card d.R₃ = 2 ^ 17 ∧
      (∀ x ∈ d.R₃, x * x ∈ d.R₂) ∧ d.R₃ ≤ normalizer ((d.R ⊔ d.Y : Subgroup G) : Set G) ∧
      d.R₃ ≤ normalizer (((d.X₄ ⊔ d.F) ⊔ d.V₂ : Subgroup G) : Set G) := by
  refine ⟨h.RY_inf_RD₃, ?_, h.card_R₂, h.card_RY, h.card_RD₃, by rw [h.R₃_eq]; exact h.card_RYD₃,
    fun _ hx => h.mul_self_mem_R₂_of_mem_R₃ hx, ?_,
    (oTwo_le _).trans h.normalizer_R₂_le_normalizer_SV₂⟩
  · rw [h.R₃_eq]
    exact le_antisymm (sup_le le_sup_left (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
      (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  · rw [h.R₃_eq]
    exact sup_le (d.R ⊔ d.Y).le_normalizer h.D₃_le_normalizer_RY

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
