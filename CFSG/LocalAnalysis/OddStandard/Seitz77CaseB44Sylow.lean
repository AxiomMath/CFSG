module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Basic

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.OddStandard.Seitz77.L34 CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

section Uniq

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M₁ M₂ : Subgroup G}

theorem isSylowOf_cs' {P K : Subgroup G} (h : IsSylowOf 2 P K) (g : G) :
    IsSylowOf 2 (cs g P) (cs g K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨cs_mono g hle, hP.map (MulAut.conj g).toMonoidHom, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P K
  have h2 := Subgroup.relIndex_mul_card (cs g P) (cs g K)
  rw [inf_eq_left.mpr hle] at h1
  rw [inf_eq_left.mpr (cs_mono g hle), nat_card_cs, nat_card_cs] at h2
  have h3 : (cs g P).relIndex (cs g K) = P.relIndex K := by
    have hpos : 0 < Nat.card P := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h2, h1]
  rw [h3]
  exact hdvd

theorem CaseB.Factors.mem_sylow_of_mul_mem (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral)
    {S'' : Subgroup G} (hS'' : IsSylowOf 2 S'' c.Ninf) {a b : G} (ha : a ∈ M₁) (hb : b ∈ M₂)
    (ha2 : ∃ n, orderOf a = 2 ^ n) (hab : a * b ∈ S'') : a ∈ S'' ∧ b ∈ S'' := by
  have hcomm : ∀ x ∈ M₁, ∀ y ∈ M₂, x * y = y * x := fun x hx y hy => F.comm_elem hZ hx hy
  have hO : Odd2 M₁ M₂ :=
    ⟨fun x hx m hm => F.norm₁ x (F.ninf_eq ▸ hx) m hm,
      fun x hx m hm => F.norm₂ x (F.ninf_eq ▸ hx) m hm, F.odd_inf⟩
  have hSn : IsSylowOf 2 S'' (M₁ ⊔ M₂) := F.ninf_eq ▸ hS''
  have hsup : S'' = (S'' ⊓ M₁) ⊔ (S'' ⊓ M₂) := hO.sylow_eq_sup hSn
  have hab' : a * b ∈ (S'' ⊓ M₁) ⊔ (S'' ⊓ M₂) := hsup ▸ hab
  obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := mem_sup_of_forall_comm (O := S'' ⊓ M₁) (E := S'' ⊓ M₂)
    (fun x hx y hy => hcomm x hx.2 y hy.2) hab'
  have hz : s₁⁻¹ * a = s₂ * b⁻¹ := by
    calc s₁⁻¹ * a = s₁⁻¹ * (a * b) * b⁻¹ := by group
      _ = s₁⁻¹ * (s₁ * s₂) * b⁻¹ := by rw [← hss]
      _ = s₂ * b⁻¹ := by group
  have hzmem : s₁⁻¹ * a ∈ M₁ ⊓ M₂ :=
    ⟨M₁.mul_mem (M₁.inv_mem hs₁.2) ha, by rw [hz]; exact M₂.mul_mem hs₂.2 (M₂.inv_mem hb)⟩
  have hzodd : Odd (orderOf (s₁⁻¹ * a)) := by
    have := orderOf_dvd_natCard (⟨s₁⁻¹ * a, hzmem⟩ : ↥(M₁ ⊓ M₂))
    rw [Subgroup.orderOf_mk] at this
    exact F.odd_inf.of_dvd_nat this
  have hs₁N : s₁ ∈ c.Ninf := F.M₁_le hs₁.2
  have hcent : (s₁⁻¹ * a) * s₁ = s₁ * (s₁⁻¹ * a) := F.inf_central hZ hzmem hs₁N
  have hs₁2 : ∃ n, orderOf s₁ = 2 ^ n := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hS''.isPGroup ⟨s₁, hs₁.1⟩
    exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
  have hz1 : s₁⁻¹ * a = 1 :=
    eq_one_of_two_power_of_odd (y := a) (v := s₁) (k := s₁⁻¹ * a) (by group) hs₁2 ha2
      hcent.symm hzodd
  have ha_eq : s₁ = a := inv_mul_eq_one.mp hz1
  have hb_eq : s₂ = b := by
    rw [hz1] at hz
    exact mul_inv_eq_one.mp hz.symm
  exact ⟨ha_eq ▸ hs₁.1, hb_eq ▸ hs₂.1⟩

theorem CaseB.Factors.sylow_unique (F : c.Factors M₁ M₂) (hZ : c.OddCoreCentral)
    {S S'' A₁ B₁ : Subgroup G} (hS : IsSylowOf 2 S c.Ninf) (hS'' : IsSylowOf 2 S'' c.Ninf)
    (hSAB : S = A₁ ⊔ B₁) (hA₁ : A₁ ≤ M₁) (hB₁ : B₁ ≤ M₂)
    (hsw₁ : ∀ a ∈ A₁, t * a * t⁻¹ ∈ B₁) (hsw₂ : ∀ b ∈ B₁, t * b * t⁻¹ ∈ A₁)
    (ht : t * t = 1) (hV : ∀ a ∈ A₁, a * (t * a * t⁻¹) ∈ S'') : S'' = S := by
  have hA₁S : A₁ ≤ S := hSAB ▸ le_sup_left
  have hA₁2 : ∀ a ∈ A₁, ∃ n, orderOf a = 2 ^ n := fun a ha => by
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hS.isPGroup ⟨a, hA₁S ha⟩
    exact ⟨n, by rwa [Subgroup.orderOf_mk] at hn⟩
  have hAS : ∀ a ∈ A₁, a ∈ S'' ∧ t * a * t⁻¹ ∈ S'' := fun a ha =>
    F.mem_sylow_of_mul_mem hZ hS'' (hA₁ ha) (hB₁ (hsw₁ a ha)) (hA₁2 a ha) (hV a ha)
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hle : S ≤ S'' := by
    rw [hSAB]
    refine sup_le (fun a ha => (hAS a ha).1) (fun b hb => ?_)
    have h1 := (hAS _ (hsw₂ b hb)).2
    have e : t * (t * b * t⁻¹) * t⁻¹ = b := by
      calc t * (t * b * t⁻¹) * t⁻¹ = (t * t) * b * (t⁻¹ * t⁻¹) := by group
        _ = b := by rw [ht, ht', ht]; group
    rwa [e] at h1
  have hcard : Nat.card ↥S'' ≤ Nat.card ↥S := by
    rw [hS''.card_eq, hS.card_eq]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

end Uniq


section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.S_le_G₀ : S ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := by
  rw [CS.S_eq]
  exact sup_le (CS.A₁_le_M₁.trans (le_sup_left.trans le_sup_left))
    (CS.B₁_le_M₂.trans (le_sup_left.trans le_sup_right))

theorem CommonSylow.odd_centralizer :
    Odd (Nat.card (centralizer ((M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) : Subgroup G) : Set G))) := by
  by_contra hodd
  have hev : 2 ∣ Nat.card (centralizer ((M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) : Subgroup G) : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer ((M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) : Subgroup G) : Set G)) 2 hev
  have hxC : (x : G) ∈ centralizer ((M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) : Subgroup G) : Set G) := x.2
  have hord : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxc : ∀ g ∈ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂), g * (x : G) = (x : G) * g := fun g hg =>
    mem_centralizer_iff.mp hxC g hg
  have hM₁ : M₁ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_left.trans le_sup_left
  have hM₂ : M₂ ≤ M₁ ⊔ N₁ ⊔ (M₂ ⊔ N₂) := le_sup_left.trans le_sup_right
  have hxW : (x : G) ∈ c₁.W := by
    refine CS.F₁.two_elem x ?_ ⟨1, by rw [hord]; rfl⟩
    rw [mem_centralizer_iff]
    intro w hw
    exact hxc w (CS.S_le_G₀ (CS.W₁_le_S hw))
  rw [← CS.F₁.W_eq] at hxW
  obtain ⟨f₁, hf₁, f₂, hf₂, hxf⟩ := mem_sup_of_forall_comm (O := c₁.W ⊓ M₁) (E := c₁.W ⊓ M₂)
    (fun a ha b hb => comm_of_isElemAbelian_two c₁.W_elem ha.1 hb.1) hxW
  have h1 : f₁ = 1 := by
    refine CS.F₁.cent_F₁ hf₁ fun m hm => ?_
    have hm2 : m * f₂ = f₂ * m := mem_centralizer_iff.mp (CS.F₁.W₂_cent hf₂) m hm
    have h3 : m * (f₁ * f₂) = (f₁ * f₂) * m := by rw [← hxf]; exact hxc m (hM₁ hm)
    have h4 : m * f₁ = f₁ * m := by
      have : m * f₁ * f₂ = f₁ * m * f₂ := by
        calc m * f₁ * f₂ = m * (f₁ * f₂) := by group
          _ = (f₁ * f₂) * m := h3
          _ = f₁ * (f₂ * m) := by group
          _ = f₁ * (m * f₂) := by rw [hm2]
          _ = f₁ * m * f₂ := by group
      exact mul_right_cancel this
    calc m * f₁ * m⁻¹ = f₁ * m * m⁻¹ := by rw [h4]
      _ = f₁ := by group
  have h2 : f₂ = 1 := by
    refine CS.F₁.cent_F₂ hf₂ fun m hm => ?_
    have hm1 : m * f₁ = f₁ * m := mem_centralizer_iff.mp (CS.F₁.W₁_cent hf₁) m hm
    have h3 : m * (f₁ * f₂) = (f₁ * f₂) * m := by rw [← hxf]; exact hxc m (hM₂ hm)
    have h4 : m * f₂ = f₂ * m := by
      have : f₁ * (m * f₂) = f₁ * (f₂ * m) := by
        calc f₁ * (m * f₂) = (f₁ * m) * f₂ := by group
          _ = (m * f₁) * f₂ := by rw [hm1]
          _ = m * (f₁ * f₂) := by group
          _ = (f₁ * f₂) * m := h3
          _ = f₁ * (f₂ * m) := by group
      exact mul_left_cancel this
    calc m * f₂ * m⁻¹ = f₂ * m * m⁻¹ := by rw [h4]
      _ = f₂ := by group
  rw [h1, h2, one_mul] at hxf
  rw [hxf, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem CommonSylow.P_le (hR : Radicals d.V V₁ V₂) (hZ₁ : c₁.OddCoreCentral)
    (hZ₂ : c₂.OddCoreCentral) : d.P ≤ normalizer (S : Set G) := by
  intro p hp
  have hpt : p * d.t = d.t * p := d.P_comm_t hp
  have hpV : ∀ v ∈ d.V, p * v * p⁻¹ ∈ d.V := fun v hv => d.conj_mem_V hp hv
  have hpV' : ∀ v ∈ d.V, p⁻¹ * v * p ∈ d.V := fun v hv => by
    have := d.conj_mem_V (d.P.inv_mem hp) hv
    simpa using this
  have hrad : cs p V₁ = V₁ ∨ cs p V₁ = V₂ := by
    refine hR.eq_of_card _ ?_ (SwapPair.isElemAbelian_cs hR.elem₁ p) (by rw [nat_card_cs, hR.card₁])
    intro y hy
    rw [mem_cs] at hy
    have := hpV _ (hR.le₁ hy)
    have e : p * (p⁻¹ * y * p) * p⁻¹ = y := by group
    rwa [e] at this
  have hVS : ∀ a ∈ A₁, a * (d.t * a * d.t⁻¹) ∈ cs p S := by
    intro a ha
    rw [mem_cs]
    have hv : a * (d.t * a * d.t⁻¹) ∈ d.V := (CS.syl.V_diag _).mpr ⟨a, ha, rfl⟩
    exact CS.syl.V_le (hpV' _ hv)
  have hmemN : p ∈ normalizer (S : Set G) ↔ cs p S = S := by
    constructor
    · intro hpN
      ext y
      rw [mem_cs]
      have h1 := mem_normalizer_iff.mp (normalizer (S : Set G) |>.inv_mem hpN) y
      simpa using h1.symm
    · intro heq
      refine Subgroup.mem_normalizer_fintype fun s hs => ?_
      have : p * s * p⁻¹ ∈ cs p S := mem_cs_iff.mpr hs
      rwa [heq] at this
  rw [hmemN]
  have ht2 : d.t * d.t = 1 := c₁.t_mul_self
  rcases hrad with h1 | h1
  ·
    have hpE : p ∈ normalizer ((V₁ ⊔ zpowers d.t : Subgroup G) : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      have hy' : y ∈ V₁ ⊔ zpowers d.t := hy
      obtain ⟨v, hv, s, hs, rfl⟩ := mem_sup_of_forall_comm (O := V₁) (E := zpowers d.t)
        (fun v hv s hs => by
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
          exact (Commute.zpow_right (show Commute v d.t from d.V_comm_t (hR.le₁ hv)) n).eq) hy'
      have hps : p * s * p⁻¹ = s := by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
        have : Commute p (d.t ^ n) := (Commute.zpow_right (show Commute p d.t from hpt) n)
        rw [this.eq]; group
      have hpv : p * v * p⁻¹ ∈ V₁ := by
        have : p * v * p⁻¹ ∈ cs p V₁ := mem_cs_iff.mpr hv
        rwa [h1] at this
      have e : p * (v * s) * p⁻¹ = (p * v * p⁻¹) * (p * s * p⁻¹) := by group
      show p * (v * s) * p⁻¹ ∈ V₁ ⊔ zpowers d.t
      rw [e, hps]
      exact mul_mem (mem_sup_left hpv) (mem_sup_right hs)
    have hpN : p ∈ c₁.N := c₁.normalizer_E_le_N hpE
    have hN := cs_Ninf_eq (c := c₁) hpN
    have hSyl : IsSylowOf 2 (cs p S) c₁.Ninf := by
      have := isSylowOf_cs' CS.syl.S₀_sylow p
      rwa [hN] at this
    exact CS.F₁.sylow_unique hZ₁ CS.syl.S₀_sylow hSyl CS.S_eq CS.A₁_le_M₁ CS.B₁_le_M₂
      CS.syl.swap₁ CS.syl.swap₂ ht2 hVS
  ·
    have hWD : cs p c₁.W = c₂.W := by
      have hVW : V₁ ≤ c₁.W := c₁.R_le_W
      refine c₂.H.eq_W_of_elem (D := cs p c₁.W) ?_ (SwapPair.isElemAbelian_cs c₁.W_elem p)
        (by rw [nat_card_cs]; exact c₁.W_card) ?_ ?_
      · intro y hy
        rw [mem_centralizer_iff]
        intro z hz
        rw [mem_cs] at hy
        rw [← h1, SetLike.mem_coe, mem_cs] at hz
        have := comm_of_isElemAbelian_two c₁.W_elem (hVW hz) hy
        calc z * y = p * ((p⁻¹ * z * p) * (p⁻¹ * y * p)) * p⁻¹ := by group
          _ = p * ((p⁻¹ * y * p) * (p⁻¹ * z * p)) * p⁻¹ := by rw [this]
          _ = y * z := by group
      · have hpt' : p⁻¹ * d.t = d.t * p⁻¹ := by
          calc p⁻¹ * d.t = p⁻¹ * (d.t * p) * p⁻¹ := by group
            _ = p⁻¹ * (p * d.t) * p⁻¹ := by rw [hpt]
            _ = d.t * p⁻¹ := by group
        ext y
        constructor
        · rintro ⟨hy, hyt⟩
          have hy' : p⁻¹ * y * p ∈ c₁.W := mem_cs.mp hy
          have hyt' : y * d.t = d.t * y := mem_centralizer_singleton_iff.mp hyt
          have hc : (p⁻¹ * y * p) * d.t = d.t * (p⁻¹ * y * p) := by
            calc (p⁻¹ * y * p) * d.t = p⁻¹ * y * (p * d.t) := by group
              _ = p⁻¹ * y * (d.t * p) := by rw [hpt]
              _ = p⁻¹ * (y * d.t) * p := by group
              _ = p⁻¹ * (d.t * y) * p := by rw [hyt']
              _ = (p⁻¹ * d.t) * y * p := by group
              _ = (d.t * p⁻¹) * y * p := by rw [hpt']
              _ = d.t * (p⁻¹ * y * p) := by group
          have h3 : p⁻¹ * y * p ∈ c₁.W ⊓ centralizer ({d.t} : Set G) :=
            ⟨hy', mem_centralizer_singleton_iff.mpr hc⟩
          rw [c₁.W_inf_centralizer_t] at h3
          rw [← h1]
          exact mem_cs.mpr h3
        · intro hy
          rw [← h1] at hy
          have hy2 : p⁻¹ * y * p ∈ V₁ := mem_cs.mp hy
          have hy1 : y ∈ cs p c₁.W := mem_cs.mpr (hVW hy2)
          refine ⟨hy1, mem_centralizer_singleton_iff.mpr ?_⟩
          have hct := d.V_comm_t (hR.le₁ hy2)
          calc y * d.t = p * (p⁻¹ * y * p) * p⁻¹ * d.t := by group
            _ = p * (p⁻¹ * y * p) * (p⁻¹ * d.t) := by group
            _ = p * (p⁻¹ * y * p) * (d.t * p⁻¹) := by rw [hpt']
            _ = p * ((p⁻¹ * y * p) * d.t) * p⁻¹ := by group
            _ = p * (d.t * (p⁻¹ * y * p)) * p⁻¹ := by rw [hct]
            _ = (p * d.t) * (p⁻¹ * y * p) * p⁻¹ := by group
            _ = (d.t * p) * (p⁻¹ * y * p) * p⁻¹ := by rw [hpt]
            _ = d.t * y := by group
      · have hz : cs p (zpowers d.t) = zpowers d.t := by
          have : (zpowers d.t).map (MulAut.conj p).toMonoidHom = zpowers d.t := by
            rw [MonoidHom.map_zpowers]
            have : (MulAut.conj p).toMonoidHom d.t = d.t := by
              show p * d.t * p⁻¹ = d.t
              rw [hpt]; group
            rw [this]
          exact this
        calc ⁅cs p c₁.W, zpowers d.t⁆ = ⁅cs p c₁.W, cs p (zpowers d.t)⁆ := by rw [hz]
          _ = cs p ⁅c₁.W, zpowers d.t⁆ := (cs_commutator p _ _).symm
          _ = cs p V₁ := by rw [c₁.commutator_W_t]
          _ = V₂ := h1
    have hN : cs p c₁.Ninf = c₂.Ninf := by
      show cs p (perfectResidualOf (normalizer (c₁.W : Set G))) =
        perfectResidualOf (normalizer (c₂.W : Set G))
      rw [← perfectResidualOf_cs, cs_normalizer, hWD]
    have hSyl : IsSylowOf 2 (cs p S) c₂.Ninf := by
      have := isSylowOf_cs' CS.syl.S₀_sylow p
      rwa [hN] at this
    exact CS.F₂.sylow_unique hZ₂ CS.S_sylow₂ hSyl CS.S_eq CS.A₁_le_N₁ CS.B₁_le_N₂
      CS.swapPair.swap₁ CS.swapPair.swap₂ ht2 hVS

end CS

end CFSG.OddStandard.Seitz77
