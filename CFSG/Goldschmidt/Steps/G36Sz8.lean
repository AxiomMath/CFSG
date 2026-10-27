module

public import CFSG.Goldschmidt.Steps.G36TypeI
import CFSG.Walter.Bender1970.S38.Omega

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped commutatorElement

variable {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}

namespace G36Borel

variable {Tb D : Subgroup (L ⧸ Subgroup.center L)} {y : L}

theorem g36Local_sz8 (h : G36Hyp L A₀ T₀) (hB : G36Borel L A₀ T₀ Tb D y)
    (hsz : Nonempty (L ⧸ Subgroup.center L ≃* Sz 1))
    (hev : Even (Nat.card (Subgroup.center L)))
    (hnc : ¬ ∀ t ∈ (T₀ : Subgroup L), ∀ a ∈ A₀, t * a = a * t) : G36Local L A₀ := by
  classical
  set Z := Subgroup.center L with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  set Zb := Tb ⊓ Subgroup.centralizer (Tb : Set (L ⧸ Z)) with hZbdef
  set yb : L ⧸ Z := π y with hyb
  obtain ⟨hZ8, hT64, hD7⟩ := hB.sz 1 le_rfl hsz
  replace hZ8 : Nat.card Zb = 8 := hZ8.trans (by norm_num)
  replace hT64 : Nat.card Tb = 64 := hT64.trans (by norm_num)
  replace hD7 : Nat.card D = 7 := hD7.trans (by norm_num)
  have hDprime : (Nat.card D).Prime := by rw [hD7]; norm_num
  have hyD : yb ∈ D := hB.zpowers_eq ▸ Subgroup.mem_zpowers _
  have hyord : orderOf yb = 7 := by
    rw [← Nat.card_zpowers]
    exact (congrArg (fun H : Subgroup (L ⧸ Z) => Nat.card H) hB.zpowers_eq).trans hD7
  have hmap : A₀.map π = Zb := hB.map_eq
  have hDZ : D ≤ Subgroup.normalizer (Zb : Set (L ⧸ Z)) :=
    hB.le_normalizer.trans (normalizer_le_normalizer_inf_centralizer Tb)
  have hyN : yb ∈ Subgroup.normalizer (Tb : Set (L ⧸ Z)) := hB.le_normalizer hyD
  have hTnab : ¬ IsMulCommutative Tb := by
    intro hab
    have hZT : Zb = Tb := by
      refine le_antisymm inf_le_left fun t ht => ⟨ht, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun s hs =>
        congrArg Subtype.val (hab.is_comm.comm (⟨s, hs⟩ : Tb) ⟨t, ht⟩)
    rw [hZT, hT64] at hZ8
    norm_num at hZ8
  have hZbT : Zb ≤ Tb := inf_le_left
  have hTb : ∀ t ∈ (T₀ : Subgroup L), π t ∈ Tb := fun t ht => hB.tb_eq ▸ ⟨t, ht, rfl⟩
  have hyT : y ∈ Subgroup.normalizer ((T₀ : Subgroup L) : Set L) := by
    apply mem_normalizer_of_conj_mem
    intro t ht
    obtain ⟨k, hk⟩ := h.exists_pow_eq_one ht
    refine h.mem_sylow_of_mk_mem (k := k) (by rw [conj_pow, hk, mul_one, mul_inv_cancel]) ?_
    rw [← hB.tb_eq]
    change π (y * t * y⁻¹) ∈ Tb
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hyN (π t)).mp (hTb t ht)
  have hyA := hB.mem_normalizer
  have hyC : y ∈ Subgroup.normalizer ((Subgroup.centralizer (A₀ : Set L)) : Set L) := by
    apply mem_normalizer_of_conj_mem
    intro c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have ha' : y⁻¹ * a * y ∈ A₀ := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (A₀ : Set L)).inv_mem hyA) a).mp ha
      simpa using this
    have h1 := hc _ ha'
    calc a * (y * c * y⁻¹) = y * ((y⁻¹ * a * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * a * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * a := by group
  obtain ⟨a₀, ha₀A, ha₀Z⟩ : ∃ a ∈ A₀, a ∉ Z := by
    by_contra hcon
    push Not at hcon
    exact h.not_le_center hcon
  have ha₀1 : π a₀ ≠ 1 := by
    rw [hπdef, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    exact ha₀Z
  have ha₀Zb : π a₀ ∈ Zb := hmap ▸ ⟨a₀, ha₀A, rfl⟩
  have hDfix : ∀ d ∈ D, (∀ a ∈ Zb, d * a = a * d) → d = 1 := by
    intro d hd hdc
    by_contra hd1
    have hdD : Subgroup.zpowers d = D := by
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hd)
      rw [Nat.card_zpowers]
      have hdvd : orderOf d ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd
      rcases (Nat.dvd_prime hDprime).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hd1
      · exact h1.ge
    have hyd : yb ∈ Subgroup.zpowers d := hdD ▸ hyD
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hyd
    apply hB.not_fixed _ ha₀Zb ha₀1
    change yb * π a₀ * yb⁻¹ = π a₀
    have hc : Commute (d ^ j) (π a₀) := Commute.zpow_left (hdc _ ha₀Zb) j
    rw [← hj, hc.eq, mul_inv_cancel_right]
  have hCT : (T₀ : Subgroup L) ⊓ Subgroup.centralizer (A₀ : Set L) ≤ A₀ := by
    set X := ((T₀ : Subgroup L) ⊓ Subgroup.centralizer (A₀ : Set L)).map π with hX
    have hZX : Zb ≤ X := by
      rw [← hmap]
      apply Subgroup.map_mono
      intro a ha
      exact ⟨h.le ha, Subgroup.mem_centralizer_iff.mpr fun b hb => h.mul_comm hb ha⟩
    have hXT : X ≤ Tb := by
      rw [hB.tb_eq]
      exact Subgroup.map_mono inf_le_left
    have hDX : D ≤ Subgroup.normalizer (X : Set (L ⧸ Z)) := by
      rw [← hB.zpowers_eq, Subgroup.zpowers_le]
      apply Subgroup.le_normalizer_map π
      refine ⟨y, ?_, rfl⟩
      apply mem_normalizer_of_conj_mem
      intro x hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hyT x).mp hxT,
        (Subgroup.mem_normalizer_iff.mp hyC x).mp hxC⟩
    rcases hB.irred hTnab X hZX hXT hDX with hXZ | hXT'
    · intro c hc
      apply h.mem_of_mk_mem (Subgroup.mem_inf.mp hc).1
      change π c ∈ A₀.map π
      rw [hmap]
      have hcX : π c ∈ X := ⟨c, hc, rfl⟩
      rw [hXZ] at hcX
      exact hcX
    · exfalso
      apply hnc
      intro t ht a ha
      have htX : π t ∈ X := hXT' ▸ hTb t ht
      obtain ⟨c, hc, hct⟩ := htX
      have hz : c⁻¹ * t ∈ Z := by
        rw [← QuotientGroup.eq]
        exact hct
      have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 a ha
      have h2 := Subgroup.mem_center_iff.mp hz a
      have ht' : t = c * (c⁻¹ * t) := by group
      rw [ht']
      calc c * (c⁻¹ * t) * a = c * ((c⁻¹ * t) * a) := by group
        _ = c * (a * (c⁻¹ * t)) := by rw [h2]
        _ = (c * a) * (c⁻¹ * t) := by group
        _ = (a * c) * (c⁻¹ * t) := by rw [h1]
        _ = a * (c * (c⁻¹ * t)) := by group
  have hC : Subgroup.centralizer (A₀ : Set L) = Zb.comap π := by
    apply le_antisymm
    · intro c hc
      have hcN : c ∈ Subgroup.normalizer (A₀ : Set L) := CFSG.centralizer_le_normalizer A₀ hc
      obtain ⟨t, ht, w, hw, j, rfl⟩ := hB.exists_eq_mul hcN
      have hw1 : π w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
      have hyj : π (y ^ j) = 1 := by
        refine hDfix _ (by rw [map_zpow]; exact D.zpow_mem hyD j) ?_
        intro ab hab
        rw [← hmap] at hab
        obtain ⟨a, ha, rfl⟩ := hab
        have h1 : π (t * w * y ^ j) * π a = π a * π (t * w * y ^ j) := by
          rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hc a ha)]
        have h2 : π a * π t = π t * π a :=
          (Subgroup.mem_centralizer_iff.mp (hmap ▸ ⟨a, ha, rfl⟩ : π a ∈ Zb).2 (π t)
            (hTb t ht)).symm
        rw [map_mul, map_mul, hw1, mul_one] at h1
        calc π (y ^ j) * π a = (π t)⁻¹ * (π t * π (y ^ j) * π a) := by group
          _ = (π t)⁻¹ * (π a * (π t * π (y ^ j))) := by rw [h1]
          _ = (π t)⁻¹ * ((π a * π t) * π (y ^ j)) := by group
          _ = (π t)⁻¹ * ((π t * π a) * π (y ^ j)) := by rw [h2]
          _ = π a * π (y ^ j) := by group
      have hyjZ : y ^ j ∈ Z := (QuotientGroup.eq_one_iff _).mp hyj
      have htC : t ∈ Subgroup.centralizer (A₀ : Set L) := by
        have hwy : w * y ^ j ∈ Subgroup.centralizer (A₀ : Set L) :=
          Subgroup.mem_centralizer_iff.mpr fun b _ =>
            Subgroup.mem_center_iff.mp (Z.mul_mem hw hyjZ) b
        have : t = (t * w * y ^ j) * (w * y ^ j)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hwy)
      have htA : t ∈ A₀ := hCT ⟨ht, htC⟩
      show π (t * w * y ^ j) ∈ Zb
      rw [map_mul, map_mul, hw1, hyj, mul_one, mul_one]
      exact hmap ▸ ⟨t, htA, rfl⟩
    · intro g hg
      rw [Subgroup.mem_comap, ← hmap] at hg
      obtain ⟨a, ha, hag⟩ := hg
      have hz : a⁻¹ * g ∈ Z := by
        rw [← QuotientGroup.eq]
        exact hag
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := h.mul_comm hb ha
      have h2 := Subgroup.mem_center_iff.mp hz b
      have hg' : g = a * (a⁻¹ * g) := by group
      rw [hg']
      calc b * (a * (a⁻¹ * g)) = (b * a) * (a⁻¹ * g) := by group
        _ = (a * b) * (a⁻¹ * g) := by rw [h1]
        _ = a * (b * (a⁻¹ * g)) := by group
        _ = a * ((a⁻¹ * g) * b) := by rw [h2]
        _ = a * (a⁻¹ * g) * b := by group
  have hN : Subgroup.normalizer (A₀ : Set L) =
      (Subgroup.normalizer (Tb : Set (L ⧸ Z))).comap π := by
    ext n
    exact hB.normalizer_iff n
  have hNcard : Nat.card (Subgroup.normalizer (Tb : Set (L ⧸ Z))) = 448 := by
    have hle1 : Nat.card Tb * Nat.card D ≤ Nat.card (Subgroup.normalizer (Tb : Set (L ⧸ Z))) :=
      CFSG.Walter.card_mul_card_le_of_inf_eq_bot Subgroup.le_normalizer hB.le_normalizer
        hB.inf_eq
    have hle2 : Nat.card (Subgroup.normalizer (Tb : Set (L ⧸ Z))) ≤ Nat.card Tb * Nat.card D := by
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_surjective
        (fun p : Tb × D => (⟨(p.1 : L ⧸ Z) * p.2,
          Subgroup.mul_mem _ (Subgroup.le_normalizer p.1.2) (hB.le_normalizer p.2.2)⟩ :
            Subgroup.normalizer (Tb : Set (L ⧸ Z)))) ?_
      rintro ⟨x, hx⟩
      rw [← hB.sup_eq] at hx
      have hx' : x ∈ ((Tb ⊔ D : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left Tb D hB.le_normalizer] at hx'
      obtain ⟨t, ht, d, hd, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨(⟨t, ht⟩, ⟨d, hd⟩), rfl⟩
    rw [hT64, hD7] at hle1 hle2
    omega
  have hidx : ((Subgroup.centralizer (A₀ : Set L)).subgroupOf
      (Subgroup.normalizer (A₀ : Set L))).index = 56 := by
    change (Subgroup.centralizer (A₀ : Set L)).relIndex (Subgroup.normalizer (A₀ : Set L)) = 56
    rw [hC, hN, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hπs]
    have h1 := Subgroup.relIndex_mul_card Zb (Subgroup.normalizer (Tb : Set (L ⧸ Z)))
    have hZN : Zb ⊓ Subgroup.normalizer (Tb : Set (L ⧸ Z)) = Zb :=
      inf_eq_left.mpr (hZbT.trans Subgroup.le_normalizer)
    rw [hZN, hZ8, hNcard] at h1
    omega
  have hyC' : y ∉ Subgroup.centralizer (A₀ : Set L) := by
    intro hyc
    rw [hC, Subgroup.mem_comap] at hyc
    have hyTD : yb ∈ Tb ⊓ D := ⟨hyc.1, hyD⟩
    rw [hB.inf_eq, Subgroup.mem_bot] at hyTD
    rw [hyTD, orderOf_one] at hyord
    omega
  have hy7 : y ^ 7 ∈ Subgroup.centralizer (A₀ : Set L) := by
    rw [hC, Subgroup.mem_comap, map_pow, ← hyord, pow_orderOf_eq_one]
    exact Zb.one_mem
  let X' : Subgroup (L ⧸ Z) :=
    { carrier := {s | s ∈ Tb ∧ yb * s * yb⁻¹ * s⁻¹ ∈ Zb}
      mul_mem' := by
        rintro s₁ s₂ ⟨h₁T, h₁⟩ ⟨h₂T, h₂⟩
        refine ⟨Tb.mul_mem h₁T h₂T, ?_⟩
        have hc : s₁ * (yb * s₂ * yb⁻¹ * s₂⁻¹) = (yb * s₂ * yb⁻¹ * s₂⁻¹) * s₁ :=
          Subgroup.mem_centralizer_iff.mp h₂.2 s₁ h₁T
        have : yb * (s₁ * s₂) * yb⁻¹ * (s₁ * s₂)⁻¹ =
            (yb * s₁ * yb⁻¹ * s₁⁻¹) * (s₁ * (yb * s₂ * yb⁻¹ * s₂⁻¹) * s₁⁻¹) := by group
        rw [this, hc, mul_inv_cancel_right]
        exact Zb.mul_mem h₁ h₂
      one_mem' := ⟨Tb.one_mem, by
        rw [mul_one, mul_inv_cancel, inv_one, mul_one]
        exact Zb.one_mem⟩
      inv_mem' := by
        rintro s ⟨hT, hs⟩
        refine ⟨Tb.inv_mem hT, ?_⟩
        have hc : s * (yb * s * yb⁻¹ * s⁻¹) = (yb * s * yb⁻¹ * s⁻¹) * s :=
          Subgroup.mem_centralizer_iff.mp hs.2 s hT
        have : yb * s⁻¹ * yb⁻¹ * s⁻¹⁻¹ = s⁻¹ * (yb * s * yb⁻¹ * s⁻¹)⁻¹ * s := by group
        rw [this]
        have hc' : s⁻¹ * (yb * s * yb⁻¹ * s⁻¹)⁻¹ = (yb * s * yb⁻¹ * s⁻¹)⁻¹ * s⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hc]
        rw [hc', inv_mul_cancel_right]
        exact Zb.inv_mem hs }
  have hmemX' : ∀ s, s ∈ X' ↔ s ∈ Tb ∧ yb * s * yb⁻¹ * s⁻¹ ∈ Zb := fun _ => Iff.rfl
  have hX'Z : X' = Zb := by
    have hZX' : Zb ≤ X' := by
      intro s hs
      refine (hmemX' s).mpr ⟨hs.1, Zb.mul_mem ?_ (Zb.inv_mem hs)⟩
      exact (Subgroup.mem_normalizer_iff.mp (hDZ hyD) s).mp hs
    have hX'T : X' ≤ Tb := fun s hs => ((hmemX' s).mp hs).1
    have hDX' : D ≤ Subgroup.normalizer (X' : Set (L ⧸ Z)) := by
      rw [← hB.zpowers_eq, Subgroup.zpowers_le]
      change yb ∈ Subgroup.normalizer (X' : Set (L ⧸ Z))
      apply mem_normalizer_of_conj_mem
      intro s hs
      obtain ⟨hsT, hsZ⟩ := (hmemX' s).mp hs
      refine (hmemX' _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hyN s).mp hsT, ?_⟩
      have : yb * (yb * s * yb⁻¹) * yb⁻¹ * (yb * s * yb⁻¹)⁻¹ =
          yb * (yb * s * yb⁻¹ * s⁻¹) * yb⁻¹ := by group
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (hDZ hyD) _).mp hsZ
    rcases hB.irred hTnab X' hZX' hX'T hDX' with hX | hX
    · exact hX
    · exfalso
      have hall : ∀ s ∈ Tb, yb * s * yb⁻¹ * s⁻¹ ∈ Zb := fun s hs =>
        ((hmemX' s).mp (hX ▸ hs)).2
      have hpow : ∀ k : ℕ, ∀ s ∈ Tb, yb ^ k * s * (yb ^ k)⁻¹ * s⁻¹ ∈ Zb := by
        intro k
        induction k with
        | zero =>
          intro s _
          rw [pow_zero, one_mul, inv_one, mul_one, mul_inv_cancel]
          exact Zb.one_mem
        | succ k ih =>
          intro s hs
          have : yb ^ (k + 1) * s * (yb ^ (k + 1))⁻¹ * s⁻¹ =
              (yb * (yb ^ k * s * (yb ^ k)⁻¹ * s⁻¹) * yb⁻¹) * (yb * s * yb⁻¹ * s⁻¹) := by
            rw [pow_succ']
            group
          rw [this]
          exact Zb.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDZ hyD) _).mp (ih s hs))
            (hall s hs)
      have hcomm : ⁅Tb, D⁆ ≤ Zb := by
        rw [Subgroup.commutator_le]
        intro s hs d hd
        rw [← hB.zpowers_eq] at hd
        obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hd : d ∈ Submonoid.powers yb)
        have hk' : yb ^ k = d := hk
        have h1 := Zb.inv_mem (hpow k s hs)
        rw [hk'] at h1
        have : ⁅s, d⁆ = (d * s * d⁻¹ * s⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [this]
        exact h1
      have hle : Tb ≤ Zb := hB.comm_eq ▸ hcomm
      have := Subgroup.card_le_of_le hle
      rw [hT64, hZ8] at this
      omega
  have hself : ∀ x ∈ Subgroup.normalizer (A₀ : Set L),
      x⁻¹ * y * x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L) →
      x ∈ Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L) := by
    intro x hx hxy
    obtain ⟨t, ht, w, hw, j, rfl⟩ := hB.exists_eq_mul hx
    set Y := Subgroup.zpowers y ⊔ Subgroup.centralizer (A₀ : Set L) with hY
    have hwC : w ∈ Subgroup.centralizer (A₀ : Set L) :=
      Subgroup.mem_centralizer_iff.mpr fun b _ => Subgroup.mem_center_iff.mp hw b
    have hwyY : w * y ^ j ∈ Y :=
      Subgroup.mul_mem _ (le_sup_right (a := Subgroup.zpowers y) hwC)
        (le_sup_left (b := Subgroup.centralizer (A₀ : Set L)) (Subgroup.zpow_mem_zpowers y j))
    suffices htA : t ∈ A₀ by
      have htC : t ∈ Subgroup.centralizer (A₀ : Set L) :=
        Subgroup.mem_centralizer_iff.mpr fun b hb => h.mul_comm hb htA
      have : t * w * y ^ j = t * (w * y ^ j) := by group
      rw [this]
      exact Subgroup.mul_mem _ (le_sup_right (a := Subgroup.zpowers y) htC) hwyY
    have htyt : t⁻¹ * y * t ∈ Y := by
      have : t⁻¹ * y * t =
          (w * y ^ j) * ((t * w * y ^ j)⁻¹ * y * (t * w * y ^ j)) * (w * y ^ j)⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwyY hxy) (Subgroup.inv_mem _ hwyY)
    have hYle : Y ≤ (Zb ⊔ D).comap π := by
      apply sup_le
      · rw [Subgroup.zpowers_le]
        exact le_sup_right (a := Zb) hyD
      · rw [hC]
        exact Subgroup.comap_mono le_sup_left
    have h1 : π (t⁻¹ * y * t) ∈ ((Zb ⊔ D : Subgroup (L ⧸ Z)) : Set (L ⧸ Z)) := hYle htyt
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Zb D hDZ] at h1
    obtain ⟨zh, hzh, d, hd, hzd⟩ := Set.mem_mul.mp h1
    set s := π t with hs
    have hsT : s ∈ Tb := hTb t ht
    have hzd' : zh * d = s⁻¹ * yb * s := by
      rw [hzd, map_mul, map_mul, map_inv]
    have hdy : d = yb := by
      have hmem : d * yb⁻¹ ∈ Tb ⊓ D := by
        refine ⟨?_, D.mul_mem hd (D.inv_mem hyD)⟩
        have : d * yb⁻¹ = zh⁻¹ * (s⁻¹ * (yb * s * yb⁻¹)) := by
          calc d * yb⁻¹ = zh⁻¹ * (zh * d) * yb⁻¹ := by group
            _ = zh⁻¹ * (s⁻¹ * yb * s) * yb⁻¹ := by rw [hzd']
            _ = zh⁻¹ * (s⁻¹ * (yb * s * yb⁻¹)) := by group
        rw [this]
        exact Tb.mul_mem (Tb.inv_mem (hZbT hzh)) (Tb.mul_mem (Tb.inv_mem hsT)
          ((Subgroup.mem_normalizer_iff.mp hyN s).mp hsT))
      rw [hB.inf_eq, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    rw [hdy] at hzd'
    have hcomm : yb * s * yb⁻¹ * s⁻¹ ∈ Zb := by
      have hzh' : zh = s⁻¹ * yb * s * yb⁻¹ := by
        calc zh = zh * yb * yb⁻¹ := by group
          _ = s⁻¹ * yb * s * yb⁻¹ := by rw [hzd']
      have : yb * s * yb⁻¹ * s⁻¹ = s * zh * s⁻¹ := by
        rw [hzh']
        group
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_inf_centralizer Tb
        (Subgroup.le_normalizer hsT)) zh).mp hzh
    have hsX : s ∈ X' := (hmemX' s).mpr ⟨hsT, hcomm⟩
    rw [hX'Z] at hsX
    apply h.mem_of_mk_mem ht
    change π t ∈ A₀.map π
    rw [hmap]
    exact hsX
  exact ⟨y, hyA, hB.odd, hB.trans_commutator h, fun _ ha hay => hB.mem_center_of_commute ha hay,
    Or.inr ⟨⟨hsz, hev⟩, hidx, hyC', hy7, hself⟩⟩

end G36Borel

end CFSG.Goldschmidt
