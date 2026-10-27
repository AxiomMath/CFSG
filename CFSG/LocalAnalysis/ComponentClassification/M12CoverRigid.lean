module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverLift
public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

theorem exists_local_coordinates {E : Type*} [Group E] [Group.IsPerfect E]
    {π : E →* NativeSporadic.M12} {z : E} (hπ : IsCentralDoubleExt π z)
    (h4 : ∀ v : E, orderOf (π v) = 2 → fixedCount (π v) = 4 → orderOf v = 2)
    (h0 : ∀ v : E, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = z) :
    ∃ ι : S.comap π ≃* R, (∀ x, ((ι x).snd : NativeSporadic.M12) = π x) ∧
      ((ι.symm ⟨1, 1⟩ : S.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = beta (π x)) →
        ∀ (x : E) (hx : π x ∈ S) (hφx : π (φ x) ∈ S), ι ⟨φ x, hφx⟩ = tau (ι ⟨x, hx⟩) := by
  classical
  let u₀ : S → E := fun s =>
    if s = 1 then 1 else Function.surjInv hπ.surjective (s : NativeSporadic.M12)
  have hu₀ : ∀ s : S, π (u₀ s) = s := by
    intro s
    by_cases hs : s = 1
    · simp [u₀, hs]
    · simp only [u₀, hs, ↓reduceIte]
      exact Function.surjInv_eq hπ.surjective _
  have hu₀1 : u₀ 1 = 1 := by simp [u₀]
  let c : S → S → ZMod 2 := fun s t => binCoord (u₀ s * u₀ t) (u₀ (s * t))
  have hcu : ∀ s t, u₀ s * u₀ t = z ^ (c s t).val * u₀ (s * t) := fun s t =>
    hπ.eq_pow_binCoord_mul (by rw [map_mul, hu₀, hu₀, hu₀, Subgroup.coe_mul])
  have hl : ∀ t, c 1 t = 0 := fun t =>
    hπ.binCoord_eq (by rw [hu₀1, one_mul, one_mul, ZMod.val_zero, pow_zero, one_mul])
  have hr : ∀ s, c s 1 = 0 := fun s =>
    hπ.binCoord_eq (by rw [hu₀1, mul_one, mul_one, ZMod.val_zero, pow_zero, one_mul])
  have hc : ∀ a b w, c a b + c (a * b) w = c b w + c a (b * w) := by
    intro a b w
    apply hπ.pow_val_mul_cancel (x := u₀ (a * b * w))
    calc z ^ (c a b + c (a * b) w).val * u₀ (a * b * w)
        = z ^ (c a b).val * (z ^ (c (a * b) w).val * u₀ (a * b * w)) := by
          rw [hπ.pow_val_add, mul_assoc]
      _ = u₀ a * u₀ b * u₀ w := by rw [← hcu, ← mul_assoc, ← hcu]
      _ = u₀ a * (z ^ (c b w).val * u₀ (b * w)) := by rw [mul_assoc, hcu]
      _ = z ^ (c b w).val * (z ^ (c a (b * w)).val * u₀ (a * (b * w))) := by
          rw [hπ.mul_pow_val_mul, hcu]
      _ = z ^ (c b w + c a (b * w)).val * u₀ (a * b * w) := by
          rw [← mul_assoc, ← hπ.pow_val_add, mul_assoc a b w]
  have hd : ∀ q : S, orderOf q = 2 → c q q = f q q := by
    intro q hq
    have hqq : q * q = 1 := by rw [← sq, ← hq, pow_orderOf_eq_one]
    have hsq : u₀ q ^ 2 = z ^ (c q q).val := by rw [sq, hcu, hqq, hu₀1, mul_one]
    have hπq : orderOf (π (u₀ q)) = 2 := by rw [hu₀, Subgroup.orderOf_coe, hq]
    rcases f_diag q hq with ⟨h4q, hfq⟩ | ⟨h0q, hfq⟩
    · have h1 : u₀ q ^ 2 = 1 := by
        rw [← h4 (u₀ q) hπq (by rw [hu₀]; exact h4q), pow_orderOf_eq_one]
      rw [hfq]
      exact hπ.pow_val_inj.1 (by rw [← hsq, h1, ZMod.val_zero, pow_zero])
    · have h1 : u₀ q ^ 2 = z := h0 (u₀ q) hπq (by rw [hu₀]; exact h0q)
      rw [hfq]
      exact hπ.pow_val_inj.1 (by rw [← hsq, h1, zmod_two_val_one, pow_one])
  obtain ⟨ν, hν⟩ := f_class_unique ⟨c, hl, hr, hc⟩ hd
  obtain ⟨ι, hι, -⟩ := hπ.exists_comap_mulEquiv_of_section S u₀ hu₀ fN ν (fun s t => by
    have h := hν s t
    change c s t = _ at h
    rw [hcu, h, fN_apply, coboundary_apply, add_assoc, add_assoc, add_assoc])
  exact transport_beta hπ ι hι

theorem mem_center_R_of_snd {x : R} (hx : x.snd = d 27) : x ∈ Subgroup.center R := by
  rcases zmod2_cases x.fst with h | h
  · have hx' : x = encR 27 := by rw [encR_27]; exact CocycleExtension.ext h hx
    rw [hx', mem_center_R]
    exact Or.inr (Or.inl rfl)
  · have hx' : x = encR 91 := by rw [encR_91]; exact CocycleExtension.ext h hx
    rw [hx', mem_center_R]
    exact Or.inr (Or.inr (Or.inr rfl))

theorem inl_mem_center_T (ε : ZMod 2) {x : R} (hx : x ∈ Subgroup.center R) :
    (TwistExt.inl x : T ε) ∈ Subgroup.center (T ε) := by
  rcases (mem_center_R x).1 hx with rfl | rfl | rfl | rfl
  · rw [← encT_inl ε]
    exact (mem_center_T ε _).2 (Or.inl rfl)
  · rw [← encT_inl ε]
    exact (mem_center_T ε _).2 (Or.inr (Or.inl rfl))
  · rw [← encT_inl ε]
    exact (mem_center_T ε _).2 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [← encT_inl ε]
    exact (mem_center_T ε _).2 (Or.inr (Or.inr (Or.inr rfl)))

theorem eq_or_exists_conj_d27 {E : Type*} [Group E] {π : E →* NativeSporadic.M12} {z : E}
    (hπ : IsCentralDoubleExt π z)
    (h0 : ∀ v : E, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = z) {u : E}
    (hu : orderOf u = 2) : u = z ∨ ∃ k : E, π (k⁻¹ * u * k) = d 27 := by
  have hu2 : u ^ 2 = 1 := by rw [← hu, pow_orderOf_eq_one]
  by_cases h1 : π u = 1
  · left
    have hmem : u ∈ Subgroup.zpowers z := by rw [← hπ.ker_eq]; exact h1
    rcases eq_one_or_eq_of_mem_zpowers hπ.orderOf_eq hmem with rfl | h
    · rw [orderOf_one] at hu
      exact absurd hu (by norm_num)
    · exact h
  · right
    have hπu : orderOf (π u) = 2 := orderOf_eq_prime (by rw [← map_pow, hu2, map_one]) h1
    have h4 : fixedCount (π u) = 4 := by
      rcases fixedCount_of_orderOf_eq_two _ hπu with h | h
      · exact h
      · exact absurd ((h0 u hπu h).symm.trans hu2) hπ.ne_one
    obtain ⟨g₁, hg₁⟩ := conj_elemR_of_fixedCount_four _ hπu h4
    obtain ⟨g₂, hg₂⟩ := conj_elemR_of_fixedCount_four (d 27 : NativeSporadic.M12)
      (by rw [Subgroup.orderOf_coe]; exact orderOf_d27) card_fixed_d27
    obtain ⟨k, hk⟩ := hπ.surjective (g₁ * g₂⁻¹)
    refine ⟨k, ?_⟩
    rw [map_mul, map_mul, map_inv, hk, ← hg₁, ← hg₂]
    group

theorem exists_twist_embedding {H : Type*} [Group H] (ε : ZMod 2) (j : R →* H)
    (hj : Function.Injective j) (q : H) (hqj : ∀ x, j x ≠ q)
    (hconj : ∀ x, q * j x = j (tau x) * q) (hq : q * q = j (zε ε)) :
    ∃ Φ : T ε →* H, Function.Injective Φ ∧ ∀ x, Φ (TwistExt.inl x) = j x := by
  have hmul : ∀ a b : T ε,
      j (a * b).x * q ^ (a * b).e.val = j a.x * q ^ a.e.val * (j b.x * q ^ b.e.val) := by
    intro a b
    rw [TwistExt.mul_def]
    dsimp only
    rcases zmod2_cases a.e with ha | ha <;> rcases zmod2_cases b.e with hb | hb <;>
      rw [ha, hb]
    · simp [TwistExt.twist_zero, TwistExt.zpow2_zero]
    · simp [TwistExt.twist_zero, TwistExt.zpow2_zero, mul_assoc]
    · simp only [TwistExt.twist_one, mul_zero, TwistExt.zpow2_zero, mul_one, add_zero,
        zmod_two_val_one, pow_one, ZMod.val_zero, pow_zero, map_mul, mul_assoc, hconj]
    · simp only [TwistExt.twist_one, mul_one, TwistExt.zpow2_one, zmod_two_add_self,
        ZMod.val_zero, pow_zero, zmod_two_val_one, pow_one, map_mul, mul_assoc]
      rw [← mul_assoc q, hconj, mul_assoc, hq]
  let Φ : T ε →* H := MonoidHom.mk' (fun a => j a.x * q ^ a.e.val) hmul
  refine ⟨Φ, (injective_iff_map_eq_one Φ).2 fun a ha => ?_, fun x => ?_⟩
  · change j a.x * q ^ a.e.val = 1 at ha
    rcases zmod2_cases a.e with he | he
    · rw [he, ZMod.val_zero, pow_zero, mul_one, ← map_one j] at ha
      exact TwistExt.ext (hj ha) he
    · rw [he, zmod_two_val_one, pow_one] at ha
      exact absurd (by rw [map_inv]; exact (eq_inv_of_mul_eq_one_right ha).symm) (hqj a.x⁻¹)
  · change j x * q ^ (0 : ZMod 2).val = j x
    rw [ZMod.val_zero, pow_zero, mul_one]

theorem factorization_two_pow_mul_1485 (k : ℕ) : (2 ^ k * 1485).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 1485)]
  simp

theorem exists_rigid_sylow_of_model {H G : Type*} [Group H] [Finite H] [Group G] {L : Subgroup H}
    {t : H} (j : R → H) (hjt : j ⟨1, 1⟩ = t)
    (hR : ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ x ∈ Subgroup.center R, j x = k⁻¹ * u * k)
    (Φ : G →* H) (hΦ : Function.Injective Φ)
    (hcard : Nat.card G = 2 ^ (Nat.card H).factorization 2)
    (hcen : IsElementaryAbelian 2 (Subgroup.center G) ∧ Nat.card (Subgroup.center G) = 4)
    (haut : ∀ φ : MulAut G, ∀ w ∈ Subgroup.center G, φ w = w)
    (hc : ∀ x ∈ Subgroup.center R, ∃ w ∈ Subgroup.center G, Φ w = j x) :
    ∃ T : Sylow 2 H, IsElementaryAbelian 2 (Subgroup.center (T : Subgroup H)) ∧
      Nat.card (Subgroup.center (T : Subgroup H)) = 4 ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ z ∈ Subgroup.center (T : Subgroup H), φ z = z) ∧
      (∃ z ∈ Subgroup.center (T : Subgroup H), (z : H) = t) ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k := by
  let e : G ≃* Φ.range := MonoidHom.ofInjective hΦ
  have hT : Nat.card Φ.range = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  have himg : ∀ w ∈ Subgroup.center G, ∃ z ∈ Subgroup.center Φ.range, (z : H) = Φ w :=
    fun w hw => ⟨e w, map_mem_center e hw, MonoidHom.ofInjective_apply hΦ⟩
  have hcenT : ∀ z ∈ Subgroup.center Φ.range, e.symm z ∈ Subgroup.center G :=
    fun z hz => map_mem_center e.symm hz
  have := hcen.1
  have hfix : ∀ φ : MulAut Φ.range, ∀ z ∈ Subgroup.center Φ.range, φ z = z := by
    intro φ z hz
    have h := haut ((e.trans φ).trans e.symm) (e.symm z) (hcenT z hz)
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at h
    exact e.symm.injective h
  obtain ⟨zt, hzt, hztt⟩ : ∃ z ∈ Subgroup.center Φ.range, (z : H) = t := by
    obtain ⟨w, hw, hwt⟩ := hc ⟨1, 1⟩ (CocycleExtension.mk_one_mem_center 1)
    obtain ⟨z, hz, hzw⟩ := himg w hw
    exact ⟨z, hz, by rw [hzw, hwt, hjt]⟩
  have key : IsElementaryAbelian 2 (Subgroup.center Φ.range) ∧
      Nat.card (Subgroup.center Φ.range) = 4 ∧
      (∀ φ : MulAut Φ.range, ∀ z ∈ Subgroup.center Φ.range, φ z = z) ∧
      (∃ z ∈ Subgroup.center Φ.range, (z : H) = t) ∧
      (∀ φ : MulAut Φ.range, ∀ x : Φ.range, (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center Φ.range,
        (z : H) = k⁻¹ * u * k := by
    refine ⟨isElementaryAbelian_center_of fun z hz => ?_, ?_, hfix, ⟨zt, hzt, hztt⟩,
      fun φ x hx => ?_, fun u hu hu2 => ?_⟩
    · apply e.symm.injective
      rw [map_pow, elemPow_eq_one_of_isElementaryAbelian _ (hcenT z hz), map_one]
    · rw [← hcen.2]
      exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm
    · obtain rfl : x = zt := Subtype.ext (hx.trans hztt.symm)
      exact hfix φ x hzt
    · obtain ⟨k, hk, x, hx, hxk⟩ := hR u hu hu2
      obtain ⟨w, hw, hwx⟩ := hc x hx
      obtain ⟨z, hz, hzw⟩ := himg w hw
      exact ⟨k, hk, z, hz, by rw [hzw, hwx, hxk]⟩
  exact ⟨Sylow.ofCard Φ.range hT, key⟩

theorem exists_lift_beta {H : Type*} [Group H] {L : Subgroup H} [L.Normal] [Group.IsPerfect L]
    (π : L →* NativeSporadic.M12) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center L) (hCL : Subgroup.centralizer (L : Set H) ≤ L) {h₀ : H}
    (hh₀ : h₀ ∉ L) : ∃ q : H, q ∉ L ∧ fullAction π hπ hker q = beta := by
  obtain ⟨g, hg⟩ := exists_conj_or_conj_mul_beta (fullAction π hπ hker h₀)
  have hg' : fullAction π hπ hker h₀ = MulAut.conj g * beta := by
    rcases hg with hg | hg
    · exact absurd (by rw [hg]; exact ⟨g, rfl⟩) (fullAction_notMem_inner π hπ hker hCL hh₀)
    · exact hg
  obtain ⟨l, hl⟩ := hπ g
  refine ⟨(l : H)⁻¹ * h₀, fun hq => hh₀ ?_, ?_⟩
  · have := L.mul_mem l.2 hq
    rwa [mul_inv_cancel_left] at this
  · rw [map_mul, map_inv, fullAction_coe, hl, hg', ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.ComponentClassification.M12Cover.InternalSylow

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover
open InternalSylow (R d tau zε exists_local_coordinates eq_or_exists_conj_d27
  mem_center_R_of_snd exists_rigid_sylow_of_model exists_lift_beta exists_twist_embedding
  inl_mem_center_T factorization_two_pow_mul_1485)

theorem m12_actual_double_cover_internal_sylow_rigidity {H : Type} [Group H] [Finite H]
    {L : Subgroup H} {t : H} (hLn : L.Normal) (hLq : Assembly.IsQuasisimple L)
    (ht : orderOf t = 2) (hZ : (Subgroup.center L).map L.subtype = Subgroup.zpowers t)
    (hQ : NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12)
    (hCL : Subgroup.centralizer (L : Set H) = Subgroup.zpowers t) (hidx : L.index ≤ 2) :
    ∃ T : Sylow 2 H, IsElementaryAbelian 2 (Subgroup.center (T : Subgroup H)) ∧
      Nat.card (Subgroup.center (T : Subgroup H)) = 4 ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ z ∈ Subgroup.center (T : Subgroup H), φ z = z) ∧
      (∃ z ∈ Subgroup.center (T : Subgroup H), (z : H) = t) ∧
      (∀ φ : MulAut (T : Subgroup H), ∀ x : (T : Subgroup H), (x : H) = t → φ x = x) ∧
      ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ z ∈ Subgroup.center (T : Subgroup H),
        (z : H) = k⁻¹ * u * k := by
  obtain ⟨e₀⟩ := hQ
  let e : L ⧸ Subgroup.center L ≃* NativeSporadic.M12 := e₀
  obtain ⟨tL, htLc, htLt⟩ : t ∈ (Subgroup.center L).map L.subtype :=
    hZ ▸ Subgroup.mem_zpowers t
  have htLt' : (tL : H) = t := htLt
  have hZL : Subgroup.center L = Subgroup.zpowers tL := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hZ, MonoidHom.map_zpowers, htLt]
  have htL : orderOf tL = 2 := by rw [← Subgroup.orderOf_coe, htLt', ht]
  let π : L →* NativeSporadic.M12 := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = Subgroup.center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = Subgroup.zpowers tL := hkerZ.trans hZL
  have hπ : IsCentralDoubleExt π tL := ⟨hπs, htLc, htL, hker⟩
  have : Group.IsPerfect L := Group.isPerfect_def.2 hLq.1
  have hcardL : Nat.card L = 190080 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv,
      CFSG.Sporadic.Schreier.m12_card, hker, Nat.card_zpowers, htL]
  obtain ⟨-, h4, h0⟩ := m12_double_cover_involution_lift_orders hLq htL hZL π hπs hker
  have h0' : ∀ v : L, orderOf (π v) = 2 → fixedCount (π v) = 0 → v ^ 2 = tL :=
    fun v h1 h2 => (h0 v h1 h2).1
  obtain ⟨ι, hιs, hιz, hιβ⟩ := exists_local_coordinates hπ h4 h0'
  let j : R →* H := L.subtype.comp ((InternalSylow.S.comap π).subtype.comp ι.symm.toMonoidHom)
  have hj : Function.Injective j :=
    L.subtype_injective.comp ((InternalSylow.S.comap π).subtype_injective.comp ι.symm.injective)
  have hjt : j ⟨1, 1⟩ = t := by
    rw [← htLt']
    exact congrArg Subtype.val hιz
  have hjL : ∀ x, j x ∈ L := fun x => ((ι.symm x : InternalSylow.S.comap π) : L).2
  have hR : ∀ u ∈ L, orderOf u = 2 → ∃ k ∈ L, ∃ x ∈ Subgroup.center R, j x = k⁻¹ * u * k := by
    intro u hu hu2
    rcases eq_or_exists_conj_d27 hπ h0' (u := ⟨u, hu⟩)
      ((Subgroup.orderOf_coe _).symm.trans hu2) with h | ⟨k, hk⟩
    · refine ⟨1, L.one_mem, ⟨1, 1⟩, CocycleExtension.mk_one_mem_center 1, ?_⟩
      rw [hjt, inv_one, one_mul, mul_one, ← htLt']
      exact (congrArg Subtype.val h).symm
    · have hy : k⁻¹ * ⟨u, hu⟩ * k ∈ InternalSylow.S.comap π := by
        rw [Subgroup.mem_comap, hk]
        exact (d 27).2
      refine ⟨k, k.2, ι ⟨_, hy⟩, mem_center_R_of_snd (Subtype.ext ((hιs _).trans hk)), ?_⟩
      change (((ι.symm (ι ⟨_, hy⟩) : InternalSylow.S.comap π) : L) : H) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
  rcases (show L.index = 1 ∨ L.index = 2 by
    have := L.index_ne_zero_of_finite
    omega) with h1 | h2
  · have hcardH : Nat.card H = 2 ^ 7 * 1485 := by
      rw [← L.card_mul_index, h1, hcardL]
      norm_num
    refine exists_rigid_sylow_of_model j hjt hR j hj ?_ InternalSylow.center_R_elementary
      InternalSylow.aut_fixes_center_R fun x hx => ⟨x, hx, rfl⟩
    rw [InternalSylow.card_R, hcardH, factorization_two_pow_mul_1485]
    norm_num
  · have hcardH : Nat.card H = 2 ^ 8 * 1485 := by
      rw [← L.card_mul_index, h2, hcardL]
      norm_num
    have hCL' : Subgroup.centralizer (L : Set H) ≤ L := by
      rw [hCL, Subgroup.zpowers_le, ← htLt']
      exact tL.2
    obtain ⟨h₀, hh₀⟩ : ∃ h₀ : H, h₀ ∉ L := not_forall.1 fun hall => by
      have hL : L = ⊤ := eq_top_iff.2 fun x _ => hall x
      rw [hL, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨q, hqL, hθq⟩ := exists_lift_beta π hπs hkerZ hCL' hh₀
    have hqq : q * q ∈ Subgroup.zpowers t := by
      rw [← hCL, ← ker_fullAction π hπs hkerZ, MonoidHom.mem_ker, map_mul, hθq, beta_mul_self]
    obtain ⟨ε, hε⟩ : ∃ ε : ZMod 2, q * q = j (zε ε) := by
      rcases eq_one_or_eq_of_mem_zpowers ht hqq with h | h
      · exact ⟨0, by rw [h]; simp [zε]⟩
      · exact ⟨1, by rw [h]; simp [zε, hjt]⟩
    have hφ : ∀ x : L, π (MulAut.conjNormal q x) = beta (π x) := fun x => by
      rw [← fullAction_apply π hπs hkerZ, hθq]
    have hconj : ∀ x : R, q * j x = j (tau x) * q := by
      intro x
      have hy : π ((ι.symm x : InternalSylow.S.comap π) : L) ∈ InternalSylow.S :=
        (ι.symm x).2
      have hφy : π (MulAut.conjNormal q ((ι.symm x : InternalSylow.S.comap π) : L)) ∈
          InternalSylow.S := by
        rw [hφ]
        exact InternalSylow.beta_mem_S hy
      have h := hιβ (MulAut.conjNormal q) hφ _ hy hφy
      have hyx : ι ⟨_, hy⟩ = x := ι.apply_symm_apply x
      rw [hyx] at h
      have h' : ι.symm (tau x) = ⟨_, hφy⟩ := by rw [← h, MulEquiv.symm_apply_apply]
      change q * (((ι.symm x : InternalSylow.S.comap π) : L) : H) =
        (((ι.symm (tau x) : InternalSylow.S.comap π) : L) : H) * q
      rw [h', MulAut.conjNormal_apply, inv_mul_cancel_right]
    obtain ⟨Φ, hΦ, hΦinl⟩ :=
      exists_twist_embedding ε j hj q (fun x hx => hqL (hx ▸ hjL x)) hconj hε
    refine exists_rigid_sylow_of_model j hjt hR Φ hΦ ?_ (InternalSylow.center_T_elementary ε)
      (InternalSylow.aut_fixes_center_T ε) fun x hx =>
        ⟨TwistExt.inl x, inl_mem_center_T ε hx, hΦinl x⟩
    rw [InternalSylow.card_T, hcardH, factorization_two_pow_mul_1485]
    norm_num

theorem internalSylowData_M12 : StandardRecognition.InternalSylowData .M12 := by
  intro H _ _ L t ⟨hLn, hLq, ht, hZ, hQ, hCL, hidx⟩
  obtain ⟨T, -, -, -, -, hfix, hinv⟩ :=
    m12_actual_double_cover_internal_sylow_rigidity hLn hLq ht hZ hQ hCL hidx
  exact ⟨T, hfix, hinv⟩

end CFSG.ComponentClassification.M12Cover
