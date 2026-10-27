module

public import CFSG.GH74.Defs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem orderOf_conj_eq {z : G} (g : G) : orderOf (g * z * g⁻¹) = orderOf z := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z
  simpa [MulAut.conj_apply] using this

theorem mul_self_eq_one_of_orderOf_two {a : G} (h : orderOf a = 2) : a * a = 1 := by
  have := pow_orderOf_eq_one a
  rwa [h, sq] at this

theorem isCentralInvolution_conj [Finite G] {z : G} (h : CFSG.GH74.IsCentralInvolution z) (g : G) :
    CFSG.GH74.IsCentralInvolution (g * z * g⁻¹) := by
  obtain ⟨hz, S, hzS, hzc⟩ := h
  refine ⟨by rw [orderOf_conj_eq, hz], g • S, ?_, ?_⟩
  · rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨z, hzS, by simp [MulAut.conj_apply]⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul] at hs
    obtain ⟨s', hs', rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hs
    have h1 : (MulAut.conj g • s') = g * s' * g⁻¹ := by simp
    rw [h1]
    calc g * s' * g⁻¹ * (g * z * g⁻¹) = g * (s' * z) * g⁻¹ := by group
      _ = g * (z * s') * g⁻¹ := by rw [hzc s' hs']
      _ = g * z * g⁻¹ * (g * s' * g⁻¹) := by group

theorem isCentralInvolution_of_mem_center_sylow [Finite G] {V : Subgroup G} (hV : IsPGroup 2 ↥V)
    (hidx : ¬ 2 ∣ V.index) {z : G} (hzV : z ∈ V) (hzc : ∀ v ∈ V, v * z = z * v)
    (hz : orderOf z = 2) : CFSG.GH74.IsCentralInvolution z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hz, hV.toSylow hidx, ?_, ?_⟩
  · simpa using hzV
  · intro s hs
    exact hzc s (by simpa using hs)

theorem central_of_normal_of_center {V P : Subgroup G} (hPn : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P)
    {z : G} (hzP : z ∈ P) (hz1 : z ≠ 1) (hzc : ∀ p ∈ P, z * p = p * z)
    (hZ : ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z) : ∀ v ∈ V, v * z = z * v := by
  intro v hv
  have hw : v * z * v⁻¹ ∈ P := hPn v hv z hzP
  have hwc : ∀ p ∈ P, (v * z * v⁻¹) * p = p * (v * z * v⁻¹) := by
    intro p hp
    have hp' : v⁻¹ * p * v ∈ P := by
      have := hPn v⁻¹ (V.inv_mem hv) p hp
      simpa using this
    have h1 := hzc _ hp'
    calc v * z * v⁻¹ * p = v * (z * (v⁻¹ * p * v)) * v⁻¹ := by group
      _ = v * ((v⁻¹ * p * v) * z) * v⁻¹ := by rw [h1]
      _ = p * (v * z * v⁻¹) := by group
  rcases hZ _ hw hwc with h | h
  · exfalso
    apply hz1
    have : z = v⁻¹ * (v * z * v⁻¹) * v := by group
    rw [this, h]; group
  · have : v * z = (v * z * v⁻¹) * v := by group
    rw [this, h]

theorem eq_of_sq_eq_one_of_cyclic {Q : Type} [Group Q] [Finite Q] [IsCyclic Q] {a b : Q}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) : a = b := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  by_contra hne
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) (by norm_num)
  have hsub : ({1, a, b} : Finset Q) ⊆ Finset.univ.filter (fun c : Q => c ^ 2 = 1) := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hc with rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
  have hcard : ({1, a, b} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm⟩
  have := Finset.card_le_card hsub
  omega

theorem commutator_eq_top_of_simple [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) : _root_.commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exfalso
    have hm : ⁅a, b⁆ ∈ _root_.commutator G :=
      Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · exact h

theorem normal_subgroupOf_of_conj {V V₀ : Subgroup G}
    (hn : ∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) : (V₀.subgroupOf V).Normal :=
  ⟨fun w hw g => by
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact hn g g.2 w hw⟩

theorem isCyclic_quot_of_elem {V V₀ : Subgroup G} [(V₀.subgroupOf V).Normal]
    {b : G} (hbV : b ∈ V) (h : ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀) :
    IsCyclic (↥V ⧸ V₀.subgroupOf V) := by
  refine ⟨⟨QuotientGroup.mk ⟨b, hbV⟩, fun q => ?_⟩⟩
  induction q using QuotientGroup.induction_on with
  | H v =>
    obtain ⟨k, hk⟩ := h v v.2
    refine ⟨k, ?_⟩
    show ((QuotientGroup.mk (⟨b, hbV⟩ : ↥V) : ↥V ⧸ V₀.subgroupOf V)) ^ k = QuotientGroup.mk v
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hk

theorem commutator_le_of_cyclic_quot {V V₀ : Subgroup G} [(V₀.subgroupOf V).Normal]
    (hcyc : IsCyclic (↥V ⧸ V₀.subgroupOf V)) : ⁅V, V⁆ ≤ V₀ := by
  refine Subgroup.commutator_le.2 (fun a ha b hb => ?_)
  let A : ↥V := ⟨a, ha⟩
  let B : ↥V := ⟨b, hb⟩
  have hcomm : (QuotientGroup.mk A : ↥V ⧸ V₀.subgroupOf V) * QuotientGroup.mk B =
      QuotientGroup.mk B * QuotientGroup.mk A :=
    (IsCyclic.commGroup (α := ↥V ⧸ V₀.subgroupOf V)).mul_comm _ _
  have h1 : (QuotientGroup.mk ⁅A, B⁆ : ↥V ⧸ V₀.subgroupOf V) = 1 := by
    have := map_commutatorElement (QuotientGroup.mk' (V₀.subgroupOf V)) A B
    simp only [QuotientGroup.mk'_apply] at this
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem inv_mul_mem_of_cyclic [Finite G] {V V₀ : Subgroup G} [(V₀.subgroupOf V).Normal]
    (hcyc : IsCyclic (↥V ⧸ V₀.subgroupOf V)) {a b : G} (haV : a ∈ V) (hbV : b ∈ V)
    (ha : a * a = 1) (hb : b * b = 1) (ha0 : a ∉ V₀) (hb0 : b ∉ V₀) : a⁻¹ * b ∈ V₀ := by
  let A : ↥V := ⟨a, haV⟩
  let B : ↥V := ⟨b, hbV⟩
  have hA1 : (QuotientGroup.mk A : ↥V ⧸ V₀.subgroupOf V) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact ha0 h
  have hB1 : (QuotientGroup.mk B : ↥V ⧸ V₀.subgroupOf V) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact hb0 h
  have hA2 : (QuotientGroup.mk A : ↥V ⧸ V₀.subgroupOf V) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : A ^ 2 = 1 := Subtype.ext (by simpa [sq] using ha)
    rw [this]; rfl
  have hB2 : (QuotientGroup.mk B : ↥V ⧸ V₀.subgroupOf V) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : B ^ 2 = 1 := Subtype.ext (by simpa [sq] using hb)
    rw [this]; rfl
  have := eq_of_sq_eq_one_of_cyclic hA1 hB1 hA2 hB2
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
  simpa using this

theorem thm1_false_of_end [Finite G] (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {x f : G} {T P V V₀ : Subgroup G}
    (hx : orderOf x = 2) (hxT : x ∈ T) (hnc : ¬ CFSG.GH74.IsCentralInvolution x)
    (hfT : f ∈ T) (hf : orderOf f = 2) (hfx : f * x = x * f) (hfP : ∀ p ∈ P, f * p = p * f)
    (hPT : P ≤ T)
    (hZ : ∃ z ∈ P, orderOf z = 2 ∧ (∀ p ∈ P, z * p = p * z) ∧
      ∀ w ∈ P, (∀ p ∈ P, w * p = p * w) → w = 1 ∨ w = z)
    (hfus : ∀ z ∈ P, orderOf z = 2 → (∀ p ∈ P, z * p = p * z) → ∀ u ∈ P ⊔ zpowers f,
      orderOf u = 2 → ∃ g : G, g * u * g⁻¹ = z ∨ g * u * g⁻¹ = f ∨ g * u * g⁻¹ = f * z)
    (hVp : IsPGroup 2 ↥V) (hVidx : ¬ 2 ∣ V.index) (hVf : ∀ v ∈ V, v * f = f * v)
    (hTV : ∀ t ∈ T, f * t = t * f → t ∈ V)
    (hPn : ∀ v ∈ V, ∀ p ∈ P, v * p * v⁻¹ ∈ P)
    (hV0 : V₀ ≤ V) (hV0n : ∀ v ∈ V, ∀ w ∈ V₀, v * w * v⁻¹ ∈ V₀) (hxV0 : x ∉ V₀)
    (hcyc : ∃ b ∈ V, ∀ v ∈ V, ∃ k : ℤ, (b ^ k)⁻¹ * v ∈ V₀)
    (hom : ∀ u ∈ V₀, u * u = 1 → u ∈ P ⊔ zpowers f) : False := by
  have hxV : x ∈ V := hTV x hxT hfx
  have hfV : f ∈ V := hTV f hfT rfl
  have hPV : ∀ p ∈ P, p ∈ V := fun p hp => hTV p (hPT hp) (hfP p hp)
  obtain ⟨z, hzP, hz2, hzc, hZ'⟩ := hZ
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzV : z ∈ V := hPV z hzP
  have hzcV : ∀ v ∈ V, v * z = z * v := central_of_normal_of_center hPn hzP hz1 hzc hZ'
  have hCIz : CFSG.GH74.IsCentralInvolution z :=
    isCentralInvolution_of_mem_center_sylow hVp hVidx hzV hzcV hz2
  have hCIf : CFSG.GH74.IsCentralInvolution f :=
    isCentralInvolution_of_mem_center_sylow hVp hVidx hfV (fun v hv => hVf v hv) hf
  have hCI0 : ∀ u ∈ V₀, orderOf u = 2 → CFSG.GH74.IsCentralInvolution u := by
    intro u hu hu2
    have huP : u ∈ P ⊔ zpowers f := hom u hu (mul_self_eq_one_of_orderOf_two hu2)
    obtain ⟨g, hg⟩ := hfus z hzP hz2 hzc u huP hu2
    have hCIg : CFSG.GH74.IsCentralInvolution (g * u * g⁻¹) := by
      rcases hg with h | h | h
      · rw [h]; exact hCIz
      · rw [h]; exact hCIf
      · have hord : orderOf (f * z) = 2 := by rw [← h, orderOf_conj_eq, hu2]
        rw [h]
        refine isCentralInvolution_of_mem_center_sylow hVp hVidx (V.mul_mem hfV hzV)
          (fun v hv => ?_) hord
        calc v * (f * z) = (v * f) * z := by group
          _ = (f * v) * z := by rw [hVf v hv]
          _ = f * (v * z) := by group
          _ = f * (z * v) := by rw [hzcV v hv]
          _ = (f * z) * v := by group
    have := isCentralInvolution_conj hCIg g⁻¹
    have e : g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u := by group
    rwa [e] at this
  have hN : (V₀.subgroupOf V).Normal := normal_subgroupOf_of_conj hV0n
  obtain ⟨b, hbV, hb⟩ := hcyc
  have hcycQ : IsCyclic (↥V ⧸ V₀.subgroupOf V) := isCyclic_quot_of_elem hbV hb
  have habel : ⁅V, V⁆ ≤ V₀ := commutator_le_of_cyclic_quot hcycQ
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_two hx
  have hcop : Nat.Coprime 2 V.index := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hVidx
  have hmain := CFSG.Quasithin.generalized_thompson_transfer_two hcop ⟨hV0, hN⟩ habel hxV hxV0 hx
    (fun a ha => by
      have hu2 : orderOf (a⁻¹ * x * a) = 2 := by
        have := orderOf_conj_eq (z := x) a⁻¹
        simpa using this.trans hx
      have huV0 : a⁻¹ * x * a ∉ V₀ := by
        intro hu
        have h1 := isCentralInvolution_conj (hCI0 _ hu hu2) a
        have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
        rw [e] at h1
        exact hnc h1
      have hu1 : (a⁻¹ * x * a) * (a⁻¹ * x * a) = 1 := mul_self_eq_one_of_orderOf_two hu2
      exact inv_mul_mem_of_cyclic hcycQ hxV ha hxx hu1 hxV0 huV0)
  apply hmain
  rw [commutator_eq_top_of_simple hsimple hnonab]
  exact mem_top x

end CFSG.GH74.GLS.C3.Layer1.Thm1
