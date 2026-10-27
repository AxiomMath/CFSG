module

public import CFSG.CGT.Timmesfeld75.Sec66Conj
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section DProd

theorem Sec6Ctx.mul_mem_classD_of_card_eq [Finite G] (hc : Sec6Ctx T T₁ n m) {e d : G}
    (he : e ∈ classD T) (heN : e ∈ Subgroup.normalizer (T : Set G))
    (hcard : Nat.card ↥(commSub e T) = Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)))
    (hd : d ∈ T) (hde : d * e = e * d) : e * d ∈ classD T := by
  have hTab := hc.hy.pair.wc.1
  have hee : e * e = 1 := mul_self_eq_one_of_mem_classD hTab he
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact hee
  have hdd : d * d = 1 := elemAbelian_mul_self hTab hd
  have hsq : (e * d) ^ 2 = 1 := by
    rw [pow_two]
    calc e * d * (e * d) = e * (d * e) * d := by group
      _ = e * (e * d) * d := by rw [hde]
      _ = (e * e) * (d * d) := by group
      _ = 1 := by rw [hee, hdd, one_mul]
  obtain ⟨s, hs, hes⟩ := (card_commSub_eq_iff hTab he2 heN).1 hcard d hd hsq
  rw [hes]
  exact classD_conj he s

theorem Sec6Ctx.classD_mul_of_comm (h63 : Sec63) (hc : Sec6Ctx T T₁ n m) (hn : n = 2) :
    ∀ d ∈ classD T, ∀ e ∈ classD T, d ≠ e → d * e = e * d → d * e ∈ classD T := by
  have := hc.finite
  have hTab := hc.hy.pair.wc.1
  have hA8 : ¬ (n = 4 ∧ m = 1) := by omega
  have core : ∀ d ∈ T, d ≠ 1 → ∀ e ∈ classD T, d ≠ e → d * e = e * d → d * e ∈ classD T := by
    intro d hd hd1 e he hne hde
    have heN : e ∈ Subgroup.normalizer (T : Set G) :=
      hc.hy.pair.wc.centralizer_le_normalizer hd hd1
        (Subgroup.mem_centralizer_singleton_iff.2 hde.symm)
    by_cases heT : e ∈ T
    · refine mem_classD_of_mem (T.mul_mem hd heT) ?_
      intro h
      apply hne
      have h1 : e = d⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1, elemAbelian_inv hTab hd]
    · have hmem : e ∈ normD T := ⟨he, heN⟩
      obtain ⟨-, hcm⟩ := hc.card_index_centralizer_eq h63 hA8 hmem heT
      have hC := hc.card_centralizer_eq h63 hA8 hmem heT
      have hLn := hc.card_normIn
      have hcard : Nat.card ↥(commSub e T) =
          Nat.card ↥(T ⊓ Subgroup.centralizer ({e} : Set G)) := by
        rw [hcm, hC, hLn, hn]
        simp
      rw [hde]
      exact hc.mul_mem_classD_of_card_eq he heN hcard hd hde
  intro d hd e he hne hde
  obtain ⟨g, t, ht, ht1, hdg⟩ := hd
  have he' : g * e * g⁻¹ ∈ classD T := by
    have := classD_conj he g⁻¹
    rwa [inv_inv] at this
  have hne' : t ≠ g * e * g⁻¹ := by
    intro h
    apply hne
    rw [hdg, h]
    group
  have hde' : t * (g * e * g⁻¹) = (g * e * g⁻¹) * t := by
    have e1 : t = g * d * g⁻¹ := by rw [hdg]; group
    rw [e1]
    calc g * d * g⁻¹ * (g * e * g⁻¹) = g * (d * e) * g⁻¹ := by group
      _ = g * (e * d) * g⁻¹ := by rw [hde]
      _ = g * e * g⁻¹ * (g * d * g⁻¹) := by group
  have h2 := classD_conj (core t ht ht1 _ he' hne' hde') g
  have e3 : g⁻¹ * (t * (g * e * g⁻¹)) * g = d * e := by rw [hdg]; group
  rwa [e3] at h2

end DProd

section Center

theorem exists_mul_of_mem_sup_normIn (hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G))
    {z : G} (hz : z ∈ T ⊔ normIn T₁ T) : ∃ u ∈ normIn T₁ T, ∃ t ∈ T, z = u * t := by
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (normIn T₁ T) T hL₁N
  have hz' : z ∈ ((normIn T₁ T : Set G) * (T : Set G)) := by
    rw [← hmul, sup_comm]
    exact hz
  obtain ⟨u, hu, t, ht, hut⟩ := hz'
  exact ⟨u, hu, t, ht, hut.symm⟩

theorem Sec6Ctx.center_eq (hc : Sec6Ctx T T₁ n m) :
    ∀ z ∈ T ⊔ normIn T₁ T,
      ((∀ w ∈ T ⊔ normIn T₁ T, z * w = w * z) ↔ z ∈ normIn T T₁) := by
  have := hc.finite
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hTab := hP.wc.1
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ normIn T₁ T, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hS3.cfg.ne₁ (eq_bot_iff.2 (fun y hy => Subgroup.mem_bot.2 (hcon y hy)))
  have hCx : T ⊓ Subgroup.centralizer ({x} : Set G) = normIn T T₁ :=
    hS3.cfg.inf_centralizer_eq_normIn hx hx1
  have hm1 := hc.one_le_m
  have hLlt : Nat.card ↥(normIn T T₁) < Nat.card T := by
    rw [hc.card_normIn, hc.hT]
    have h2 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
    have hn1 := hc.one_le
    calc (2 ^ m) ^ (n - 1) < (2 ^ m) ^ (n - 1) * 2 ^ m := by
          have : 0 < (2 ^ m) ^ (n - 1) := by positivity
          nlinarith
      _ = (2 ^ m) ^ n := by
          rw [← pow_succ]
          congr 1
          omega
  intro z hz
  constructor
  · intro hcen
    obtain ⟨u, hu, t, ht, rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N hz
    have hKu : ∀ w ∈ T, u * w = w * u := by
      intro w hw
      have h1 := hcen w (Subgroup.mem_sup_left hw)
      have h2 : t * w = w * t := elemAbelian_mul_comm hTab ht hw
      have h3 : u * w * t = w * u * t := by
        calc u * w * t = u * (w * t) := by group
          _ = u * (t * w) := by rw [h2]
          _ = u * t * w := by group
          _ = w * (u * t) := h1
          _ = w * u * t := by group
      exact mul_right_cancel h3
    have hu1 : u = 1 := by
      by_contra hu1
      have hCu : T ⊓ Subgroup.centralizer ({u} : Set G) = normIn T T₁ :=
        hS3.cfg.inf_centralizer_eq_normIn hu hu1
      have hTle : T ≤ normIn T T₁ := by
        intro w hw
        rw [← hCu]
        exact ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 (hKu w hw).symm⟩
      have := Subgroup.card_le_of_le hTle
      omega
    subst hu1
    have hzt : (1 : G) * t = t := one_mul t
    rw [hzt] at hcen ⊢
    have := hcen x (Subgroup.mem_sup_right hx)
    rw [← hCx]
    exact ⟨ht, Subgroup.mem_centralizer_singleton_iff.2 this⟩
  · intro hzL w hw
    have hK : T ⊔ normIn T₁ T ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun t ht => ?_) (fun u hu => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (elemAbelian_mul_comm hTab ht (normIn_le _ _ hzL))
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hS3.cfg.comm_L_L₁ hzL hu).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hK hw)).symm

theorem Sec6Ctx.comm_mem_normIn_sup (hc : Sec6Ctx T T₁ n m) :
    ∀ a ∈ T ⊔ normIn T₁ T, ∀ b ∈ T ⊔ normIn T₁ T, ⁅a, b⁆ ∈ normIn T T₁ := by
  have := hc.finite
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hTab := hP.wc.1
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hL₁ab : IsElemAbelian 2 (normIn T₁ T) :=
    isElemAbelian_of_le hS3.cfg.wc₁.1 (normIn_le _ _)
  have hcen := hc.center_eq
  have hcentral : ∀ z ∈ normIn T T₁, ∀ w ∈ T ⊔ normIn T₁ T, z * w = w * z := fun z hz w hw =>
    ((hcen z (Subgroup.mem_sup_left (normIn_le _ _ hz))).2 hz) w hw
  have hLK : ∀ z ∈ normIn T T₁, z ∈ T ⊔ normIn T₁ T := fun z hz =>
    Subgroup.mem_sup_left (normIn_le _ _ hz)
  intro a ha b hb
  obtain ⟨u, hu, t, ht, rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N ha
  obtain ⟨u', hu', t', ht', rfl⟩ := exists_mul_of_mem_sup_normIn hL₁N hb
  have hc1 : ⁅u, t'⁆ ∈ normIn T T₁ := by
    have := hS3.cfg.comm_mem_normIn ht' hu
    rw [← commutatorElement_inv]
    exact (normIn T T₁).inv_mem this
  have hc2 : ⁅u', t⁆ ∈ normIn T T₁ := by
    have := hS3.cfg.comm_mem_normIn ht hu'
    rw [← commutatorElement_inv]
    exact (normIn T T₁).inv_mem this
  set c₁ := ⁅u, t'⁆ with hc1def
  set c₂ := ⁅u', t⁆ with hc2def
  have huK : u ∈ T ⊔ normIn T₁ T := Subgroup.mem_sup_right hu
  have hu'K : u' ∈ T ⊔ normIn T₁ T := Subgroup.mem_sup_right hu'
  have hc₂u : c₂⁻¹ * u = u * c₂⁻¹ :=
    (hcentral _ ((normIn T T₁).inv_mem hc2) u huK)
  have hc₁u' : c₁⁻¹ * u' = u' * c₁⁻¹ :=
    (hcentral _ ((normIn T T₁).inv_mem hc1) u' hu'K)
  have huu' : u * u' = u' * u := elemAbelian_mul_comm hL₁ab hu hu'
  have htt' : t * t' = t' * t := elemAbelian_mul_comm hTab ht ht'
  have e1 : t * u' = c₂⁻¹ * (u' * t) := by rw [hc2def, commutatorElement_def]; group
  have e2 : t' * u = c₁⁻¹ * (u * t') := by rw [hc1def, commutatorElement_def]; group
  have hab : u * t * (u' * t') = c₂⁻¹ * ((u' * u) * (t' * t)) := by
    calc u * t * (u' * t') = u * (t * u') * t' := by group
      _ = u * (c₂⁻¹ * (u' * t)) * t' := by rw [e1]
      _ = (u * c₂⁻¹) * (u' * t) * t' := by group
      _ = (c₂⁻¹ * u) * (u' * t) * t' := by rw [hc₂u]
      _ = c₂⁻¹ * ((u * u') * (t * t')) := by group
      _ = c₂⁻¹ * ((u' * u) * (t' * t)) := by rw [huu', htt']
  have hba : u' * t' * (u * t) = c₁⁻¹ * ((u' * u) * (t' * t)) := by
    calc u' * t' * (u * t) = u' * (t' * u) * t := by group
      _ = u' * (c₁⁻¹ * (u * t')) * t := by rw [e2]
      _ = (u' * c₁⁻¹) * (u * t') * t := by group
      _ = (c₁⁻¹ * u') * (u * t') * t := by rw [hc₁u']
      _ = c₁⁻¹ * ((u' * u) * (t' * t)) := by group
  have key : ⁅u * t, u' * t'⁆ = c₂⁻¹ * c₁ := by
    rw [commutatorElement_def]
    calc u * t * (u' * t') * (u * t)⁻¹ * (u' * t')⁻¹
        = (c₂⁻¹ * ((u' * u) * (t' * t))) * (u * t)⁻¹ * (u' * t')⁻¹ := by rw [hab]
      _ = (c₂⁻¹ * c₁) * (c₁⁻¹ * ((u' * u) * (t' * t))) * (u * t)⁻¹ * (u' * t')⁻¹ := by group
      _ = (c₂⁻¹ * c₁) * (u' * t' * (u * t)) * (u * t)⁻¹ * (u' * t')⁻¹ := by rw [hba]
      _ = c₂⁻¹ * c₁ := by group
  rw [key]
  exact (normIn T T₁).mul_mem ((normIn T T₁).inv_mem hc2) hc1

end Center

section O2

theorem normal_pGroup_sl2_eq_bot {F : Type} [Field F] [Finite F] [CharP F 2]
    (N : Subgroup SL(2, F)) (hN : ∀ g : SL(2, F), conjSubgroup g N = N) (hp : IsPGroup 2 N) :
    N = ⊥ := by
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSubgroup_utri_eq_of_sylow P
  have h1 : N ≤ utri F := by
    intro x hx
    have h2 : g * x * g⁻¹ ∈ N := by
      have : x ∈ conjSubgroup g⁻¹ N := by rw [hN g⁻¹]; exact hx
      simpa [mem_conjSubgroup] using this
    have h3 : g * x * g⁻¹ ∈ conjSubgroup g (utri F) := by rw [hg]; exact hP h2
    have := mem_conjSubgroup.1 h3
    simpa [mul_assoc] using this
  have h4 : N ≤ conjSubgroup wElt (utri F) := by
    intro x hx
    have : x ∈ conjSubgroup wElt N := by rw [hN wElt]; exact hx
    have h5 := mem_conjSubgroup.1 this
    have h6 := h1 h5
    rw [mem_conjSubgroup]
    exact h6
  have h5 := utri_inf_conj_eq_bot (F := F) (g := wElt) wElt_not_mem_borel
  exact eq_bot_iff.2 (fun x hx => by
    have := (le_inf h1 h4) hx
    rw [h5] at this
    exact this)

theorem Sec6Ctx.normal_two_subgroup_le [Finite G]
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) 2 m)
    (N : Subgroup G) (hNH : N ≤ hSub T (normIn T₁ T))
    (hNn : ∀ h ∈ hSub T (normIn T₁ T), conjSubgroup h N = N) (hp : IsPGroup 2 N) : N ≤ T := by
  obtain ⟨hN, e, -, -⟩ := hnat
  set H := hSub T (normIn T₁ T) with hHdef
  let π : ↥H →* ↥H ⧸ T.subgroupOf H := QuotientGroup.mk' (T.subgroupOf H)
  have hNp : IsPGroup 2 ↥(N.subgroupOf H) := hp.comap_subtype
  have hNbp : IsPGroup 2 ↥(((N.subgroupOf H).map π).map e.toMonoidHom) :=
    (hNp.map π).map e.toMonoidHom
  have hNbn : ∀ g : SL(2, GaloisField 2 m),
      conjSubgroup g (((N.subgroupOf H).map π).map e.toMonoidHom) =
        ((N.subgroupOf H).map π).map e.toMonoidHom := by
    intro g
    obtain ⟨q, rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : conjSubgroup h (N.subgroupOf H) = N.subgroupOf H := by
      rw [conjSubgroup_subgroupOf, hNn (h : G) h.2]
    have h2 : conjSubgroup (e (QuotientGroup.mk h))
        (((N.subgroupOf H).map π).map e.toMonoidHom) =
        ((conjSubgroup (QuotientGroup.mk h) ((N.subgroupOf H).map π)).map e.toMonoidHom) :=
      (map_conjSubgroup e.toMonoidHom (QuotientGroup.mk h) _).symm
    have h3 : conjSubgroup (QuotientGroup.mk h) ((N.subgroupOf H).map π) =
        ((conjSubgroup h (N.subgroupOf H)).map π) := (map_conjSubgroup π h _).symm
    rw [h2, h3, h1]
  have hbot := normal_pGroup_sl2_eq_bot _ hNbn hNbp
  intro x hx
  have hxH : x ∈ H := hNH hx
  have hmem : e (π ⟨x, hxH⟩) ∈ ((N.subgroupOf H).map π).map e.toMonoidHom :=
    ⟨π ⟨x, hxH⟩, ⟨⟨x, hxH⟩, hx, rfl⟩, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h2 : π ⟨x, hxH⟩ = 1 := e.injective (by rw [hmem, map_one])
  have h3 : (⟨x, hxH⟩ : ↥H) ∈ T.subgroupOf H := (QuotientGroup.eq_one_iff _).1 h2
  exact Subgroup.mem_subgroupOf.1 h3

end O2

section Closure

theorem card_eq_ncard_orbit_mul_card_centralizer [Finite G] (H : Subgroup G) (d : G) :
    Nat.card ↥H = Set.ncard {y : G | ∃ h ∈ H, y = h * d * h⁻¹} *
      Nat.card ↥(H ⊓ Subgroup.centralizer ({d} : Set G)) := by
  let _ : MulAction ↥H G := MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp H.subtype)
  have hsmul : ∀ (h : ↥H) (g : G), h • g = (h : G) * g * (h : G)⁻¹ := fun h g => by
    show ConjAct.toConjAct (h : G) • g = _
    rw [ConjAct.smul_def]
    simp
  have hidx := MulAction.index_stabilizer ↥H d
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer ↥H d)
  have hstab : (MulAction.stabilizer ↥H d).map H.subtype =
      H ⊓ Subgroup.centralizer ({d} : Set G) := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨h.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h1 := MulAction.mem_stabilizer_iff.1 hh
      rw [hsmul] at h1
      show (h : G) * d = d * h
      calc (h : G) * d = ((h : G) * d * (h : G)⁻¹) * h := by group
        _ = d * h := by rw [h1]
    · rintro ⟨hgH, hgC⟩
      refine ⟨⟨g, hgH⟩, MulAction.mem_stabilizer_iff.2 ?_, rfl⟩
      rw [hsmul]
      have := Subgroup.mem_centralizer_singleton_iff.1 hgC
      show g * d * g⁻¹ = d
      rw [this]
      group
  have horb : MulAction.orbit ↥H d = {y : G | ∃ h ∈ H, y = h * d * h⁻¹} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, (hsmul h d)⟩
    · rintro ⟨h, hh, rfl⟩
      exact ⟨⟨h, hh⟩, (hsmul ⟨h, hh⟩ d)⟩
  rw [← horb, ← hidx, ← hcard, ← Subgroup.card_map_of_injective H.subtype_injective, hstab]
  ring

theorem Sec6Ctx.closure_classD_comm (h57 : Step57) (h1 : Sec4NoA) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hn : n = 2)
    (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) {d : G} (hd : d ∈ normIn T T₁)
    (hd1 : d ≠ 1) :
    Subgroup.closure {e : G | e ∈ classD T ∧ e * d = d * e} = T ⊔ normIn T₁ T := by
  subst hn
  have := hc.finite
  have hy := hc.hy
  have hP := hy.pair
  have hS3 := hc.sec3
  have hTab := hP.wc.1
  have hdT : d ∈ T := normIn_le _ _ hd
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hL₁T : normIn T₁ T ⊓ T = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc normIn T₁ T ⊓ T ≤ T ⊓ T₁ := le_inf inf_le_right (inf_le_left.trans (normIn_le T₁ T))
      _ = ⊥ := hS3.cfg.inf
  have hA8 : ¬ (2 = 4 ∧ m = 1) := by omega
  set H := hSub T (normIn T₁ T) with hHdef
  have hHN : H ≤ Subgroup.normalizer (T : Set G) := hSub_le_normalizer hL₁N
  have hKH : T ⊔ normIn T₁ T ≤ H := sup_le left_le_hSub le_hSub
  set C := H ⊓ Subgroup.centralizer ({d} : Set G) with hCdef
  have hKC : T ⊔ normIn T₁ T ≤ C := by
    refine le_inf hKH (sup_le (fun t ht => ?_) (fun u hu => ?_))
    · exact Subgroup.mem_centralizer_singleton_iff.2 (elemAbelian_mul_comm hTab ht hdT)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hS3.cfg.comm_L_L₁ hd hu).symm
  have hm1 := hc.one_le_m
  have hq1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  have hTcard : Nat.card T = (2 ^ m) ^ 2 := hc.hT
  have hL₁card : Nat.card ↥(normIn T₁ T) = 2 ^ m := by
    rw [hc.card_normIn_swap, hc.card_normIn]
    simp
  have hHcard : Nat.card ↥H = (2 ^ m) ^ 2 * ((2 ^ m) * ((2 ^ m) ^ 2 - 1)) := by
    obtain ⟨hN, e, -, -⟩ := hnat
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H)
    have h2 : Nat.card ↥(T.subgroupOf H) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe left_le_hSub).toEquiv
    have h3 : Nat.card (↥H ⧸ T.subgroupOf H) = Nat.card (SL(2, GaloisField 2 m)) :=
      Nat.card_congr e.toEquiv
    have h4 : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
    have h5 := CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two (GaloisField 2 m)
    rw [h1, h2, h3, h5, h4, hTcard]
    ring
  have horb : {y : G | ∃ h ∈ H, y = h * d * h⁻¹} = (T : Set G) \ {1} := by
    ext y
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨conj_mem_of_mem_normalizer (hHN hh) hdT, ?_⟩
      intro h1
      apply hd1
      have h2 : h * d * h⁻¹ = 1 := h1
      calc d = h⁻¹ * (h * d * h⁻¹) * h := by group
        _ = 1 := by rw [h2]; group
    · rintro ⟨hyT, hy1⟩
      obtain ⟨h, hh, hhy⟩ := h57 G T T₁ hy d hdT hd1 y hyT hy1
      exact ⟨h, hh, hhy.symm⟩
  have hncard : Set.ncard {y : G | ∃ h ∈ H, y = h * d * h⁻¹} = (2 ^ m) ^ 2 - 1 := by
    rw [horb, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem T), ← Nat.card_coe_set_eq]
    change Nat.card ↥T - 1 = _
    rw [hTcard]
  have hCcard : Nat.card ↥C ≤ (2 ^ m) ^ 3 := by
    have h := card_eq_ncard_orbit_mul_card_centralizer H d
    rw [hncard, hHcard] at h
    have hpos : 0 < (2 ^ m) ^ 2 - 1 := by
      have : 1 < (2 ^ m) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
      omega
    have h' : (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) = Nat.card ↥C * ((2 ^ m) ^ 2 - 1) := by
      rw [mul_comm (Nat.card ↥C)]
      calc (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1)
          = (2 ^ m) ^ 2 * ((2 ^ m) * ((2 ^ m) ^ 2 - 1)) := by ring
        _ = ((2 ^ m) ^ 2 - 1) * Nat.card ↥C := h
    exact (Nat.eq_of_mul_eq_mul_right hpos h').symm.le
  have hKcard : (2 ^ m) ^ 3 ≤ Nat.card ↥(T ⊔ normIn T₁ T) := by
    let f : ↥(normIn T₁ T) × ↥T → ↥(T ⊔ normIn T₁ T) := fun p =>
      ⟨(p.1 : G) * (p.2 : G), (T ⊔ normIn T₁ T).mul_mem (Subgroup.mem_sup_right p.1.2)
        (Subgroup.mem_sup_left p.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨u, hu⟩, ⟨t, ht⟩⟩ ⟨⟨u', hu'⟩, ⟨t', ht'⟩⟩ h
      have h' : u * t = u' * t' := congrArg Subtype.val h
      have h2 : u'⁻¹ * u = t' * t⁻¹ := by
        calc u'⁻¹ * u = u'⁻¹ * (u * t) * t⁻¹ := by group
          _ = u'⁻¹ * (u' * t') * t⁻¹ := by rw [h']
          _ = t' * t⁻¹ := by group
      have h3 : u'⁻¹ * u ∈ normIn T₁ T ⊓ T :=
        ⟨(normIn T₁ T).mul_mem ((normIn T₁ T).inv_mem hu') hu, by
          rw [h2]; exact T.mul_mem ht' (T.inv_mem ht)⟩
      rw [hL₁T, Subgroup.mem_bot] at h3
      have hu2 : u = u' := (inv_mul_eq_one.1 h3).symm
      subst hu2
      have : t = t' := mul_left_cancel h'
      subst this
      rfl
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, hL₁card, hTcard] at this
    calc (2 ^ m) ^ 3 = 2 ^ m * (2 ^ m) ^ 2 := by ring
      _ ≤ _ := this
  have hKeq : T ⊔ normIn T₁ T = C := Subgroup.eq_of_le_of_card_ge hKC (hCcard.trans hKcard)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro e he
    have heN : e ∈ Subgroup.normalizer (T : Set G) :=
      hP.wc.centralizer_le_normalizer hdT hd1 (Subgroup.mem_centralizer_singleton_iff.2 he.2)
    have heH : e ∈ H := hc.normD_le_hSub_of_not_a8 h1 h63 hA8 ⟨he.1, heN⟩
    have : e ∈ C := ⟨heH, Subgroup.mem_centralizer_singleton_iff.2 he.2⟩
    rw [← hKeq] at this
    exact this
  · refine sup_le (fun t ht => ?_) (fun u hu => ?_)
    · by_cases ht1 : t = 1
      · rw [ht1]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure ⟨mem_classD_of_mem ht ht1, elemAbelian_mul_comm hTab ht hdT⟩
    · by_cases hu1 : u = 1
      · rw [hu1]
        exact Subgroup.one_mem _
      · obtain ⟨x₀, hx₀⟩ := hP.conj
        have huk : u ∈ conjSubgroup x₀ T := hx₀ ▸ normIn_le _ _ hu
        exact Subgroup.subset_closure
          ⟨mem_classD_of_mem_conjSubgroup huk hu1, (hS3.cfg.comm_L_L₁ hd hu).symm⟩

end Closure

end CFSG.CGT.Timmesfeld75
