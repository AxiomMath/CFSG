module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_12Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFacts
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic

public section

namespace CFSG.QuasithinUnique.Out21

open CFSG.Open CFSG.Quasithin

section OutSettingFacts

variable {G : Type} [Group G] [Finite G] {K H S : Subgroup G}

theorem S_le_normalizer (h : OutSetting K H S) : S ≤ Subgroup.normalizer (K : Set G) :=
  h.sylow.le.trans h.H_le_normalizer

theorem exists_mul (h : OutSetting K H S) {x : G} (hx : x ∈ H) :
    ∃ k ∈ K, ∃ s ∈ S, x = k * s := by
  rw [h.join] at hx
  exact mem_sup_of_le_normalizer (S_le_normalizer h) hx

theorem isSylowTwoOf_inf (h : OutSetting K H S) : IsSylowTwoOf (S ⊓ K) K :=
  Unc25Small.isSylowTwoOf_inf_of_mul h.sylow h.K_le_H fun x hx => by
    obtain ⟨k, hk, s, hs, rfl⟩ := exists_mul h hx
    exact ⟨k, hk, s, hs, rfl⟩

theorem isSylowTwoOf_autOn (h : OutSetting K H S) : IsSylowTwoOf (autOn S K) (autOn H K) :=
  Setup.isSylowTwoOf_autOn h.sylow h.H_le_normalizer

theorem card_alternatingGroup_fin_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

omit [Finite G] in
theorem card_K_of_a6 (e : ↥K ≃* alternatingGroup (Fin 6)) : Nat.card ↥K = 360 := by
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_six]

theorem nonabelian
    (h : OutSetting K H S) : ∃ a b : ↥K, a * b ≠ b * a := by
  have := h.simple
  rcases h.fam with hX | ⟨⟨e⟩, -⟩
  · exact (l2pFacts ↥K hX).nonabelian
  · exact Unc25K1.not_comm_of_simple_of_four_dvd' (by rw [card_K_of_a6 e]; norm_num)

theorem center_trivial
    (h : OutSetting K H S) {x : G} (hx : x ∈ K)
    (hc : ∀ y ∈ K, y * x = x * y) : x = 1 :=
  BenderBranch.eq_one_of_commute_of_simple h.simple (nonabelian h) hx hc

theorem inf_centralizer_eq_bot
    (h : OutSetting K H S) : K ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact center_trivial h hx.1 fun y hy => (Subgroup.mem_centralizer_iff.mp hx.2 y hy)

theorem card_S (h : OutSetting K H S) :
    Nat.card ↥S = Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) * Nat.card ↥(autOn S K) := by
  have hr := Subgroup.card_ker_mul_card_range (Setup.rho K S (S_le_normalizer h))
  have hker : (Setup.rho K S (S_le_normalizer h)).ker =
      (Subgroup.centralizer (K : Set G)).subgroupOf S := by
    ext p
    simp only [MonoidHom.mem_ker, Setup.rho_eq_one_iff, Subgroup.mem_subgroupOf]
  rw [Setup.range_rho, hker] at hr
  have hc : Nat.card ↥((Subgroup.centralizer (K : Set G)).subgroupOf S) =
      Nat.card ↥(S ⊓ Subgroup.centralizer (K : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), x.1.2, Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y => ⟨⟨(y : G), y.2.1⟩, Subgroup.mem_subgroupOf.mpr y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  rw [hc] at hr
  exact hr.symm

noncomputable def actOf (h : OutSetting K H S) (u : G) (hu : u ∈ H) : MulAut ↥K :=
  Setup.rho K H h.H_le_normalizer ⟨u, hu⟩

theorem actOf_apply (h : OutSetting K H S) {u : G} (hu : u ∈ H) (v : ↥K) :
    ((actOf h u hu v : ↥K) : G) = u * v * u⁻¹ :=
  Setup.rho_apply_coe h.H_le_normalizer ⟨u, hu⟩ v

theorem actOf_mem_autOn (h : OutSetting K H S) {u : G} (hu : u ∈ H) :
    actOf h u hu ∈ autOn H K := by
  rw [← Setup.range_rho h.H_le_normalizer]
  exact ⟨⟨u, hu⟩, rfl⟩

theorem actOf_mul_self (h : OutSetting K H S) {u : G} (hu : u ∈ H) (hu2 : u * u = 1) :
    actOf h u hu * actOf h u hu = 1 := by
  ext v
  have h1 : ((actOf h u hu (actOf h u hu v) : ↥K) : G) = (v : G) := by
    rw [actOf_apply, actOf_apply]
    calc u * (u * (v : G) * u⁻¹) * u⁻¹ = (u * u) * v * (u * u)⁻¹ := by group
      _ = v := by rw [hu2]; group
  simpa using h1

theorem conj_eq_actOf (h : OutSetting K H S) (k : ↥K) :
    (MulAut.conj k : MulAut ↥K) = actOf h (k : G) (h.K_le_H k.2) := by
  ext v
  rw [actOf_apply]
  simp [MulAut.conj_apply]

theorem innerAut_le_autOn (h : OutSetting K H S) : innerAut ↥K ≤ autOn H K := by
  rintro _ ⟨k, rfl⟩
  have : (MulAut.conj : ↥K →* MulAut ↥K) k = actOf h (k : G) (h.K_le_H k.2) := conj_eq_actOf h k
  rw [this]
  exact actOf_mem_autOn h _

theorem conj_injective
    (h : OutSetting K H S) :
    Function.Injective (MulAut.conj : ↥K →* MulAut ↥K) := by
  intro a b hab
  have h1 : ∀ y : ↥K, ((a : G) * y * (a : G)⁻¹) = (b : G) * y * (b : G)⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut ↥K => ((φ y : ↥K) : G)) hab
    simpa [MulAut.conj_apply] using this
  have hc : ((b : G)⁻¹ * a) = 1 := by
    refine center_trivial h (K.mul_mem (K.inv_mem b.2) a.2) fun y hy => ?_
    have := h1 ⟨y, hy⟩
    simp only at this
    calc y * ((b : G)⁻¹ * a) = (b : G)⁻¹ * ((b : G) * y * (b : G)⁻¹) * a := by group
      _ = (b : G)⁻¹ * ((a : G) * y * (a : G)⁻¹) * a := by rw [this]
      _ = ((b : G)⁻¹ * a) * y := by group
  apply Subtype.ext
  have : (a : G) = b := by
    calc (a : G) = (b : G) * ((b : G)⁻¹ * a) := by group
      _ = b := by rw [hc, mul_one]
  exact this

theorem card_innerAut
    (h : OutSetting K H S) : Nat.card ↥(innerAut ↥K) = Nat.card ↥K :=
  (Nat.card_congr (MonoidHom.ofInjective (conj_injective h)).toEquiv).symm

theorem actOf_not_mem_innerAut (h : OutSetting K H S) {u : G} (hu : u ∈ H)
    (hout : u ∉ K ⊔ (H ⊓ Subgroup.centralizer (K : Set G))) : actOf h u hu ∉ innerAut ↥K := by
  rintro ⟨k, hk⟩
  apply hout
  have hw : (k : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨v, hv⟩ : ↥K) : G)) hk
    simp only [MulAut.conj_apply] at h1
    rw [actOf_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc v * ((k : G)⁻¹ * u) = (k : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) * u := by group
      _ = (k : G)⁻¹ * (u * v * u⁻¹) * u := by rw [h1]
      _ = ((k : G)⁻¹ * u) * v := by group
  have hwH : (k : G)⁻¹ * u ∈ H := H.mul_mem (H.inv_mem (h.K_le_H k.2)) hu
  have : u = (k : G) * ((k : G)⁻¹ * u) := by group
  rw [this]
  exact Subgroup.mul_mem_sup k.2 ⟨hwH, hw⟩

@[expose] def fixSub {X : Type*} [Group X] (α : MulAut X) : Subgroup X where
  carrier := {x | α x = x}
  mul_mem' := by
    intro a b ha hb
    show α (a * b) = a * b
    rw [map_mul, show α a = a from ha, show α b = b from hb]
  one_mem' := map_one α
  inv_mem' := by
    intro a ha
    show α a⁻¹ = a⁻¹
    rw [map_inv, show α a = a from ha]

theorem mem_fixSub {X : Type*} [Group X] {α : MulAut X} {x : X} : x ∈ fixSub α ↔ α x = x :=
  Iff.rfl

theorem mem_fixSub_actOf (h : OutSetting K H S) {u : G} (hu : u ∈ H) (x : ↥K) :
    x ∈ fixSub (actOf h u hu) ↔ (x : G) ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [mem_fixSub, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have := congrArg (fun y : ↥K => (y : G)) hx
    simp only [actOf_apply] at this
    calc (x : G) * u = (u * x * u⁻¹) * u := by rw [this]
      _ = u * x := by group
  · intro hx
    apply Subtype.ext
    rw [actOf_apply]
    calc u * (x : G) * u⁻¹ = (x * u) * u⁻¹ := by rw [← hx]
      _ = x := by group

omit [Finite G] in
theorem le_oddCoreIn' {H N : Subgroup G} (hNH : N ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ oddCoreIn H := by
  have hnormal : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hnorm
  have hodd' : Odd (Nat.card (N.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
  have hle : N.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hNH hk⟩, hle hk, rfl⟩

@[expose] def OddNormalFix {X : Type*} [Group X] (α : MulAut X) : Prop :=
  ∃ N : Subgroup X, N ≠ ⊥ ∧ Odd (Nat.card N) ∧ N ≤ fixSub α ∧
    fixSub α ≤ Subgroup.normalizer (N : Set X)

theorem oddCoreIn_ne_bot_of_oddNormalFix (h : OutSetting K H S) {u : G} (hu : u ∈ H)
    (hN : OddNormalFix (actOf h u hu)) :
    oddCoreIn (K ⊓ Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
  obtain ⟨N, hN1, hNodd, hNle, hNnorm⟩ := hN
  set C := K ⊓ Subgroup.centralizer ({u} : Set G) with hC
  have hN'C : N.map K.subtype ≤ C := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨n.2, (mem_fixSub_actOf h hu n).mp (hNle hn)⟩
  have hCnorm : C ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
    intro c hc
    have hx : (⟨c, hc.1⟩ : ↥K) ∈ fixSub (actOf h u hu) :=
      (mem_fixSub_actOf h hu ⟨c, hc.1⟩).mpr hc.2
    have hxn := Subgroup.mem_normalizer_iff.mp (hNnorm hx)
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      refine ⟨⟨c, hc.1⟩ * n * ⟨c, hc.1⟩⁻¹, (hxn n).mp hn, ?_⟩
      simp
    · rintro ⟨n, hn, hng⟩
      have hgK : g ∈ K := by
        have h1 : (c : G)⁻¹ * (c * g * c⁻¹) * c ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem hc.1) (hng ▸ n.2)) hc.1
        simpa [mul_assoc] using h1
      refine ⟨⟨g, hgK⟩, ?_, rfl⟩
      have h2 : (⟨c, hc.1⟩ : ↥K) * ⟨g, hgK⟩ * ⟨c, hc.1⟩⁻¹ = n := by
        apply Subtype.ext
        simpa using hng.symm
      exact (hxn ⟨g, hgK⟩).mpr (by rw [h2]; exact hn)
  have hodd' : Odd (Nat.card (N.map K.subtype)) := by
    rwa [Subgroup.card_map_of_injective K.subtype_injective]
  have hle := le_oddCoreIn' hN'C hCnorm hodd'
  intro hbot
  rw [hbot, le_bot_iff] at hle
  exact hN1 (Subgroup.map_injective K.subtype_injective (by rw [hle, Subgroup.map_bot]))

end OutSettingFacts

end CFSG.QuasithinUnique.Out21
