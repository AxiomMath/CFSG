module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreS14Basic

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open scoped Pointwise

theorem eq_one_or_conj_of_mem_sup {G : Type*} [Group G] {K : Subgroup G} [K.Normal]
    (hK : ∀ k ∈ K, Odd (orderOf k)) {a : G} (ha : a * a = 1) {y : G}
    (hy : y ∈ K ⊔ Subgroup.zpowers a) (hyy : y * y = 1) :
    y = 1 ∨ ∃ g : G, y = g * a * g⁻¹ := by
  have hmem : y ∈ (K : Set G) * (Subgroup.zpowers a : Set G) := by
    rw [← Subgroup.normal_mul]
    exact hy
  obtain ⟨k, hk, b, hb, rfl⟩ := Set.mem_mul.mp hmem
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hab : a ^ j = 1 ∨ a ^ j = a := by
    obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' j
    · left
      rw [zpow_mul, zpow_two, ha, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, ha, one_zpow, one_mul, zpow_one]
  obtain ⟨m, hm⟩ := hK k hk
  rcases hab with h1 | h1 <;> rw [h1] at hyy ⊢
  · left
    rw [mul_one] at hyy ⊢
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hyy)
    have h2 : orderOf k = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
      · exact h2
      · omega
    exact orderOf_eq_one_iff.mp h2
  · right
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
    have hak : a * k * a⁻¹ = k⁻¹ := by
      rw [hainv]
      refine eq_inv_of_mul_eq_one_right ?_
      calc k * (a * k * a) = k * a * (k * a) := by group
        _ = 1 := hyy
    have hk1 : k ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one k
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, j₀ = k ^ (m + 1) := ⟨_, rfl⟩
    have hj₀k : j₀ * j₀ = k := by
      rw [hj₀, ← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hk1, one_mul]
    have hj : a * j₀ * a⁻¹ = j₀⁻¹ := by rw [hj₀, ← conj_pow, hak, inv_pow]
    refine ⟨j₀, ?_⟩
    calc k * a = j₀ * j₀ * a := by rw [hj₀k]
      _ = j₀ * (a * j₀ * a⁻¹)⁻¹ * a := by rw [hj, inv_inv]
      _ = j₀ * a * j₀⁻¹ := by group

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z : J}

abbrev quasiCenterQuotient (w : J) :=
  quasiNormalizer w ⧸ (Subgroup.center J).subgroupOf (quasiNormalizer w)

abbrev quasiCenterMk (w : J) : quasiNormalizer w →* quasiCenterQuotient w :=
  QuotientGroup.mk' _

omit [Finite J] in
theorem quasiCenterMk_eq_iff {w : J} (x y : quasiNormalizer w) :
    quasiCenterMk w x = quasiCenterMk w y ↔ (x : J)⁻¹ * y ∈ Subgroup.center J := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

omit [Finite J] in
theorem quasiCenterMk_eq_one_iff {w : J} (x : quasiNormalizer w) :
    quasiCenterMk w x = 1 ↔ (x : J) ∈ Subgroup.center J := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem Setting.inv_central_mul_mul_mem (h : Setting J Q B) (x : J) :
    (centralElt J * x)⁻¹ * x ∈ Subgroup.center J := by
  rw [mul_inv_rev, mul_assoc, ← (h.commute_centralElt x).inv_right.eq, inv_mul_cancel_left]
  exact (Subgroup.center J).inv_mem h.centralElt_mem_center

namespace FourGen

theorem exists_cover_of_isolated (hz : FourGen Q z) (h : Setting J Q B) {w : J}
    (hw : w * w = centralElt J) (hwz : w * z = z * w)
    (hSyl : ∀ P ≤ quasiNormalizer w, IsPGroup 2 P →
      Nat.card P ≤ Nat.card ((Q : Subgroup J) ⊓ quasiNormalizer w : Subgroup J))
    (hiso : ∀ x ∈ (Q : Subgroup J) ⊓ quasiNormalizer w, x * x = 1 → x ∈ fourGroup z) :
    ∃ W : Subgroup J, (∀ t ∈ quasiNormalizer w, orderOf t = 2 → t ∈ W) ∧
      ∀ y ∈ W, y * y ≠ centralElt J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := quasiNormalizer w with hM
  set T := (Q : Subgroup J) ⊓ M with hT
  have hTM : T ≤ M := inf_le_right
  have hT2 : IsPGroup 2 T := Q.isPGroup'.to_le inf_le_left
  have hzM : z ∈ M := h.mem_quasiNormalizer_of_mul_eq hw hwz.symm
  have hzT : z ∈ T := ⟨hz.mem, hzM⟩
  have hZM : Subgroup.center J ≤ M := fun c hc => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← Subgroup.mem_center_iff.mp hc x, mul_inv_cancel_right]
  have hZT : Subgroup.center J ≤ T := le_inf h.center_le_sylow hZM
  have hTz : ∀ x ∈ T, x * x = 1 → x ≠ 1 → x ≠ centralElt J →
      x = z ∨ x = centralElt J * z := fun x hxT hxx hx1 hxe => by
    rcases hz.eq_of_mem_fourGroup_of_ne_one h (hiso x hxT hxx) hx1 with h1 | h1 | h1
    · exact absurd h1 hxe
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨T₀, hT₀⟩ := exists_sylow_eq_subgroupOf hTM hT2 hSyl
  set π := quasiCenterMk w with hπ
  set S := T₀.mapSurjective (QuotientGroup.mk'_surjective ((Subgroup.center J).subgroupOf M))
    with hS
  have hSeq : (S : Subgroup (quasiCenterQuotient w)) = (T.subgroupOf M).map π := by
    rw [hS, Sylow.coe_mapSurjective, hT₀]
  set zM : M := ⟨z, hzM⟩ with hzMdef
  have hzS : π zM ∈ (S : Subgroup (quasiCenterQuotient w)) := by
    rw [hSeq]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hzT)
  set zbar : (S : Subgroup (quasiCenterQuotient w)) := ⟨π zM, hzS⟩ with hzbar
  have hzz1 : π zM * π zM = 1 := by
    rw [← map_mul, show zM * zM = 1 from Subtype.ext hz.mul_self, map_one]
  have hz1 : π zM ≠ 1 := by
    rw [hπ, Ne, quasiCenterMk_eq_one_iff]
    exact hz.not_mem_center
  have hzZ : zbar ∈ Subgroup.center (S : Subgroup (quasiCenterQuotient w)) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hs : (s : quasiCenterQuotient w) ∈ (T.subgroupOf M).map π := by
      rw [← hSeq]
      exact s.2
    obtain ⟨m, hm, hms⟩ := Subgroup.mem_map.mp hs
    have hmQ : (m : J) ∈ (Q : Subgroup J) := (Subgroup.mem_subgroupOf.mp hm).1
    change (s : quasiCenterQuotient w) * π zM = π zM * s
    rw [← hms, ← map_mul, ← map_mul, hπ, quasiCenterMk_eq_iff]
    have hc := hz.comm_mem_center (m : J) hmQ
    have heq : ((m * zM : M) : J)⁻¹ * ((zM * m : M) : J) = ((m : J) * z)⁻¹ *
        ((m : J) * z * (m : J)⁻¹ * z⁻¹)⁻¹ * ((m : J) * z)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, hzMdef]
      group
    rw [heq, Setting.conj_eq_of_mem_center ((Subgroup.center J).inv_mem hc)]
    exact (Subgroup.center J).inv_mem hc
  have hzord : orderOf zbar = 2 := by
    rw [hzbar, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz1) hz1
  have hwc : ∀ g : quasiCenterQuotient w, g⁻¹ * (zbar : quasiCenterQuotient w) * g ∈
      (S : Subgroup (quasiCenterQuotient w)) → g⁻¹ * (zbar : quasiCenterQuotient w) * g = zbar := by
    intro g hg
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective ((Subgroup.center J).subgroupOf M) g
    change π m⁻¹ * π zM * π m ∈ _ at hg
    change π m⁻¹ * π zM * π m = π zM
    rw [← map_mul, ← map_mul] at hg ⊢
    rw [hSeq] at hg
    obtain ⟨t, ht, htm⟩ := Subgroup.mem_map.mp hg
    rw [hπ, quasiCenterMk_eq_iff] at htm
    have hxT : ((m⁻¹ * zM * m : M) : J) ∈ T := by
      have h1 := T.mul_mem (Subgroup.mem_subgroupOf.mp ht) (hZT htm)
      rwa [mul_inv_cancel_left] at h1
    have hxx : ((m⁻¹ * zM * m : M) : J) * ((m⁻¹ * zM * m : M) : J) = 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzMdef]
      calc (m : J)⁻¹ * z * m * ((m : J)⁻¹ * z * m) = (m : J)⁻¹ * (z * z) * m := by group
        _ = 1 := by rw [hz.mul_self, mul_one, inv_mul_cancel]
    have hx1 : ((m⁻¹ * zM * m : M) : J) ≠ 1 := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzMdef]
      intro h1
      have hz1' : z = 1 := by
        calc z = (m : J) * ((m : J)⁻¹ * z * m) * (m : J)⁻¹ := by group
          _ = 1 := by rw [h1, mul_one, mul_inv_cancel]
      have := hz.order
      rw [hz1', orderOf_one] at this
      exact absurd this (by decide)
    have hxe : ((m⁻¹ * zM * m : M) : J) ≠ centralElt J := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzMdef]
      intro h1
      apply hz.ne_centralElt h
      calc z = (m : J) * ((m : J)⁻¹ * z * m) * (m : J)⁻¹ := by group
        _ = centralElt J := by rw [h1, Setting.conj_eq_of_mem_center h.centralElt_mem_center]
    rw [hπ, quasiCenterMk_eq_iff]
    rcases hTz _ hxT hxx hx1 hxe with h1 | h1 <;> rw [h1]
    · rw [hzMdef, inv_mul_cancel]
      exact (Subgroup.center J).one_mem
    · rw [hzMdef]
      exact h.inv_central_mul_mul_mem z
  obtain ⟨hZstar, -⟩ := CFSG.Adapters.glauberman_zStar S zbar hzZ hzord hwc
  set K := CFSG.oddCore (quasiCenterQuotient w) with hK
  refine ⟨((K ⊔ Subgroup.zpowers (π zM)).comap π).map M.subtype, ?_, ?_⟩
  · intro t htM ht2
    obtain ⟨m, hmM, hm⟩ := exists_conj_mem_of_card_le hTM hT2 hSyl
      (Subgroup.zpowers_le.mpr htM) (isPGroup_zpowers_of_orderOf_eq_two ht2)
    have hxT : m⁻¹ * t * m ∈ T := hm t (Subgroup.mem_zpowers t)
    refine ⟨⟨t, htM⟩, ?_, rfl⟩
    change π ⟨t, htM⟩ ∈ K ⊔ Subgroup.zpowers (π zM)
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; exact absurd ht2 (by decide)
    have hxx : m⁻¹ * t * m * (m⁻¹ * t * m) = 1 := by
      calc m⁻¹ * t * m * (m⁻¹ * t * m) = m⁻¹ * (t * t) * m := by group
        _ = 1 := by rw [htt, mul_one, inv_mul_cancel]
    have hx1 : m⁻¹ * t * m ≠ 1 := fun h1 => ht1 (by
      calc t = m * (m⁻¹ * t * m) * m⁻¹ := by group
        _ = 1 := by rw [h1, mul_one, mul_inv_cancel])
    by_cases hxe : m⁻¹ * t * m = centralElt J
    · have hte : t ∈ Subgroup.center J := by
        rw [show t = m * (m⁻¹ * t * m) * m⁻¹ by group, hxe,
          Setting.conj_eq_of_mem_center h.centralElt_mem_center]
        exact h.centralElt_mem_center
      rw [(quasiCenterMk_eq_one_iff (w := w) ⟨t, htM⟩).mpr hte]
      exact Subgroup.one_mem _
    have h1 : π (⟨m, hmM⟩⁻¹ * ⟨t, htM⟩ * ⟨m, hmM⟩) = π zM := by
      rw [hπ, quasiCenterMk_eq_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzMdef]
      rcases hTz _ hxT hxx hx1 hxe with h2 | h2 <;> rw [h2]
      · rw [inv_mul_cancel]
        exact (Subgroup.center J).one_mem
      · exact h.inv_central_mul_mul_mem z
    obtain ⟨c, hc, k, hk, hck⟩ := hZstar (π ⟨m, hmM⟩)⁻¹
    have hcz : c⁻¹ * π zM * c = π zM := by
      have h2 : c * π zM = π zM * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [mul_assoc, ← h2, inv_mul_cancel_left]
    have hπt : π ⟨t, htM⟩ = k⁻¹ * π zM * k := by
      have h2 : π ⟨t, htM⟩ = (π ⟨m, hmM⟩)⁻¹⁻¹ * π zM * (π ⟨m, hmM⟩)⁻¹ := by
        rw [inv_inv, ← h1]
        simp only [map_mul, map_inv]
        group
      rw [h2, hck]
      calc (c * k)⁻¹ * π zM * (c * k) = k⁻¹ * (c⁻¹ * π zM * c) * k := by group
        _ = k⁻¹ * π zM * k := by rw [hcz]
    rw [hπt]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem hk))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_left hk)
  · rintro _ ⟨y, hy, rfl⟩ hyy
    change π y ∈ K ⊔ Subgroup.zpowers (π zM) at hy
    simp only [Subgroup.coe_subtype] at hyy
    have hyy' : π y * π y = 1 := by
      rw [← map_mul, hπ, quasiCenterMk_eq_one_iff, Subgroup.coe_mul, hyy]
      exact h.centralElt_mem_center
    rcases eq_one_or_conj_of_mem_sup (fun k hk => CFSG.Adapters.odd_orderOf_of_mem_oddCore hk)
      hzz1 hy hyy' with h1 | ⟨g, hg⟩
    · rw [hπ, quasiCenterMk_eq_one_iff] at h1
      have := h.mul_self_of_mem_center h1
      rw [hyy] at this
      exact h.centralElt_ne_one this
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective ((Subgroup.center J).subgroupOf M) g
      have h2 : π (a * zM * a⁻¹) = π y := by
        change π y = π a * π zM * (π a)⁻¹ at hg
        rw [map_mul, map_mul, map_inv]
        exact hg.symm
      rw [hπ, quasiCenterMk_eq_iff] at h2
      obtain ⟨x, hx⟩ : ∃ x, x = ((a * zM * a⁻¹ : M) : J) := ⟨_, rfl⟩
      rw [← hx] at h2
      obtain ⟨c', hc'⟩ : ∃ c', c' = x⁻¹ * (y : J) := ⟨_, rfl⟩
      rw [← hc'] at h2
      have hxx : x * x = 1 := by
        rw [hx]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hzMdef]
        calc (a : J) * z * (a : J)⁻¹ * ((a : J) * z * (a : J)⁻¹) =
              (a : J) * (z * z) * (a : J)⁻¹ := by group
          _ = 1 := by rw [hz.mul_self, mul_one, mul_inv_cancel]
      have hy' : (y : J) = x * c' := by rw [hc']; group
      apply h.centralElt_ne_one
      rw [← hyy, hy']
      calc x * c' * (x * c') = x * (c' * x) * c' := by group
        _ = x * (x * c') * c' := by rw [← Subgroup.mem_center_iff.mp h2 x]
        _ = (x * x) * (c' * c') := by group
        _ = 1 := by rw [hxx, h.mul_self_of_mem_center h2, one_mul]

end FourGen

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
