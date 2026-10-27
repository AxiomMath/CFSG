module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.NFacts

public section

namespace CFSG.Wreathed.OriginalAllPrime.TIFacts

open CFSG.ABGTheoremB
open scoped Pointwise

section Lift

variable {M H : Type*} [Group M] [Group H]

theorem exists_commute_lift [Finite M] (φ : M →* H) (hodd : Odd (Nat.card φ.ker)) {y : M}
    (hy : y * y = 1) {U : Subgroup M} (hU : ∀ u ∈ U, y * u * y⁻¹ ∈ U) {g : M} (hg : g ∈ U)
    (hc : φ g * φ y = φ y * φ g) : ∃ u ∈ U, φ u = φ g ∧ u * y = y * u := by
  set K : Subgroup M := U ⊓ φ.ker
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_right)
  have hmem : ∀ k ∈ K, g⁻¹ * y * g * k * y⁻¹ ∈ K := by
    intro k hk
    have hk1 : φ k = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hk).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : g⁻¹ * y * g * k * y⁻¹ = g⁻¹ * (y * g * y⁻¹) * (y * k * y⁻¹) := by group
      rw [h1]
      exact U.mul_mem (U.mul_mem (U.inv_mem hg) (hU g hg)) (hU k (Subgroup.mem_inf.mp hk).1)
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, hk1, mul_one,
        mul_assoc (φ g)⁻¹, ← hc]
      group
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let f : K → K := fun k => ⟨g⁻¹ * y * g * k * y⁻¹, hmem k k.2⟩
  have hff : ∀ k, f (f k) = k := by
    intro k
    apply Subtype.ext
    change g⁻¹ * y * g * (g⁻¹ * y * g * (k : M) * y⁻¹) * y⁻¹ = k
    rw [hyinv]
    calc g⁻¹ * y * g * (g⁻¹ * y * g * (k : M) * y) * y = g⁻¹ * (y * y) * g * k * (y * y) := by
          group
      _ = k := by rw [hy]; group
  let τ : Equiv.Perm K := ⟨f, f, hff, hff⟩
  have hτ : τ ^ 2 ^ 1 = 1 := by
    ext k
    rw [pow_one, sq, Equiv.Perm.mul_apply]
    exact congrArg Subtype.val (hff k)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have hnd : ¬ 2 ∣ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card]
    exact hKodd.not_two_dvd_nat
  obtain ⟨k, hk⟩ := Equiv.Perm.exists_fixed_point_of_prime hnd hτ
  have hk' : g⁻¹ * y * g * (k : M) * y⁻¹ = k := congrArg Subtype.val hk
  refine ⟨g * k, U.mul_mem hg (Subgroup.mem_inf.mp k.2).1, ?_, ?_⟩
  · rw [map_mul, MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp k.2).2, mul_one]
  · calc g * k * y = g * (g⁻¹ * y * g * (k : M) * y⁻¹) * y := by rw [hk']
      _ = y * (g * k) := by group

theorem map_inf_centralizer_eq_bot [Finite M] (φ : M →* H) (hodd : Odd (Nat.card φ.ker))
    {y : M} (hy : y * y = 1) {U : Subgroup M} (hU : ∀ u ∈ U, y * u * y⁻¹ ∈ U)
    (hCU : U ⊓ Subgroup.centralizer {y} = ⊥) :
    U.map φ ⊓ Subgroup.centralizer {φ y} = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨⟨g, hg, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  obtain ⟨u, hu, hφu, hcu⟩ := exists_commute_lift φ hodd hy hU hg hc
  have hu1 : u ∈ U ⊓ Subgroup.centralizer {y} :=
    Subgroup.mem_inf.mpr ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr hcu⟩
  rw [hCU, Subgroup.mem_bot] at hu1
  rw [Subgroup.mem_bot, ← hφu, hu1, map_one]

theorem map_centralizer_eq [Finite M] (φ : M →* H) (hsurj : Function.Surjective φ)
    (hodd : Odd (Nat.card φ.ker)) {y : M} (hy : y * y = 1) :
    (Subgroup.centralizer {y}).map φ = Subgroup.centralizer {φ y} := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, hg, map_mul]
  · intro w hw
    obtain ⟨g, rfl⟩ := hsurj w
    rw [Subgroup.mem_centralizer_singleton_iff] at hw
    obtain ⟨u, -, hφu, hcu⟩ := exists_commute_lift φ hodd hy (U := ⊤) (fun _ _ => trivial)
      trivial hw
    exact ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr hcu, hφu⟩

end Lift

section Setting

variable {G : Type} [Group G]

theorem C_le_N (σ : Setting G) : σ.C ≤ σ.N := by
  intro c hc
  rw [Setting.C, Setting.T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff] at hc
  exact Subgroup.mem_centralizer_singleton_iff.mpr (hc σ.x (by simp)).symm

theorem mem_C_iff (σ : Setting G) {g : G} (hg : g ∈ σ.N) :
    g ∈ σ.C ↔ g * σ.x₂ = σ.x₂ * g := by
  have hx : g * σ.x = σ.x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [Setting.C, Setting.T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact (h σ.x₂ (by simp)).symm
  · intro h t ht
    rcases ht with rfl | rfl
    · exact hx.symm
    · exact h.symm

theorem ON_le_N (σ : Setting G) : σ.ON ≤ σ.N :=
  oddCoreIn_le σ.N

theorem subgroupOf_mono_of_le {A B : Subgroup G} (h : A ≤ B) (K : Subgroup G) :
    A.subgroupOf K ≤ B.subgroupOf K :=
  Subgroup.comap_mono h

structure IsModelMap (σ : Setting G) {H : Type} [Group H] (φ : σ.N →* H) (M : Subgroup H)
    (y : H) : Prop where
  surjective : Function.Surjective φ
  ker_eq : φ.ker = σ.ON.subgroupOf σ.N
  x₂_mem : σ.x₂ ∈ σ.N
  x₂_mul_self : σ.x₂ * σ.x₂ = 1
  map_x₂ : φ ⟨σ.x₂, x₂_mem⟩ = y
  L₀_le : σ.L₀ ≤ σ.N
  ON_le : σ.ON ≤ σ.L₀
  map_L₀ : (σ.L₀.subgroupOf σ.N).map φ = M

namespace IsModelMap

variable {σ : Setting G} {H : Type} [Group H] {φ : σ.N →* H} {M : Subgroup H} {y : H}

theorem odd_card_ker [Finite G] (hφ : IsModelMap σ φ M y) : Odd (Nat.card φ.ker) := by
  rw [hφ.ker_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ON_le_N σ)).toEquiv]
  exact odd_card_oddCoreIn σ.N

theorem C_subgroupOf (hφ : IsModelMap σ φ M y) :
    σ.C.subgroupOf σ.N = Subgroup.centralizer {(⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)} := by
  ext g
  rw [Subgroup.mem_subgroupOf, mem_C_iff σ g.2, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem map_C [Finite G] (hφ : IsModelMap σ φ M y) :
    (σ.C.subgroupOf σ.N).map φ = Subgroup.centralizer {y} := by
  rw [hφ.C_subgroupOf, map_centralizer_eq φ hφ.surjective hφ.odd_card_ker
    (Subtype.ext hφ.x₂_mul_self), hφ.map_x₂]

theorem mem_of_map_mem (hφ : IsModelMap σ φ M y) {K : Subgroup G} (hK : σ.ON ≤ K) {g : σ.N}
    (hg : φ g ∈ (K.subgroupOf σ.N).map φ) : (g : G) ∈ K := by
  obtain ⟨k, hk, hkg⟩ := hg
  have hr : k⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hr
  have hkg' : (g : G) = k * ((k⁻¹ * g : σ.N) : G) := by simp
  rw [hkg']
  exact K.mul_mem (Subgroup.mem_subgroupOf.mp hk) (hK hr)

theorem le_normalizer_map (_hφ : IsModelMap σ φ M y) {K X : Subgroup G} (hX : X ≤ σ.N)
    (h : K ≤ Subgroup.normalizer (X : Set G)) :
    (K.subgroupOf σ.N).map φ ≤
      Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup H) : Set H) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map φ)
  rw [← Subgroup.subgroupOf_normalizer_eq hX]
  exact subgroupOf_mono_of_le h σ.N

section Complement

variable {J : Subgroup G}

theorem J_le_N (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) : J ≤ σ.N :=
  hJ.le.trans hφ.L₀_le

theorem eq_of_map_eq (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) {a b : σ.N}
    (ha : (a : G) ∈ J) (hb : (b : G) ∈ J) (hab : φ a = φ b) : a = b := by
  have h1 : a⁻¹ * b ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at h1
  have h2 : ((a⁻¹ * b : σ.N) : G) ∈ J := by
    simpa using J.mul_mem (J.inv_mem ha) hb
  have h3 : ((a⁻¹ * b : σ.N) : G) ∈ J ⊓ σ.ON := Subgroup.mem_inf.mpr ⟨h2, h1⟩
  rw [hJ.inf_eq, Subgroup.mem_bot] at h3
  exact inv_mul_eq_one.mp (Subtype.ext h3)

theorem map_J (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) :
    (J.subgroupOf σ.N).map φ = M := by
  rw [← hφ.map_L₀, hJ.sup_eq, Subgroup.subgroupOf_sup (hφ.J_le_N hJ) (ON_le_N σ),
    Subgroup.map_sup, ← hφ.ker_eq, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]

theorem commute_of_mem_J (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) {g : σ.N}
    (hg : (g : G) ∈ J) (hc : φ g * y = y * φ g) :
    g * ⟨σ.x₂, hφ.x₂_mem⟩ = ⟨σ.x₂, hφ.x₂_mem⟩ * g := by
  have hzJ : ((⟨σ.x₂, hφ.x₂_mem⟩ * g * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ : σ.N) : G) ∈ J := by
    have h := (Subgroup.mem_normalizer_iff.mp (hJ.normal hφ.x₂_mem) g).mp hg
    simpa using h
  have h := hφ.eq_of_map_eq hJ hg hzJ (by
    rw [map_mul, map_mul, map_inv, hφ.map_x₂, ← hc, mul_inv_cancel_right])
  calc g * ⟨σ.x₂, hφ.x₂_mem⟩ =
      ⟨σ.x₂, hφ.x₂_mem⟩ * g * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ * ⟨σ.x₂, hφ.x₂_mem⟩ := by
        rw [← h]
    _ = ⟨σ.x₂, hφ.x₂_mem⟩ * g := by group

theorem mem_of_map_mem_J (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {K : Subgroup G} (hKJ : K ≤ J) {g : σ.N} (hg : (g : G) ∈ J)
    (hgK : φ g ∈ (K.subgroupOf σ.N).map φ) : (g : G) ∈ K := by
  obtain ⟨k, hk, hkg⟩ := hgK
  have hk' : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  rw [← hφ.eq_of_map_eq hJ (hKJ hk') hg hkg]
  exact hk'

theorem le_of_map_le (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ J) (h₂ : K₂ ≤ J)
    (h : (K₁.subgroupOf σ.N).map φ ≤ (K₂.subgroupOf σ.N).map φ) : K₁ ≤ K₂ := by
  intro g hg
  have hgN : g ∈ σ.N := hφ.J_le_N hJ (h₁ hg)
  exact hφ.mem_of_map_mem_J hJ h₂ (g := ⟨g, hgN⟩) (h₁ hg) (h ⟨⟨g, hgN⟩, hg, rfl⟩)

theorem eq_of_map_eq_map (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ J) (h₂ : K₂ ≤ J)
    (h : (K₁.subgroupOf σ.N).map φ = (K₂.subgroupOf σ.N).map φ) : K₁ = K₂ :=
  le_antisymm (hφ.le_of_map_le hJ h₁ h₂ h.le) (hφ.le_of_map_le hJ h₂ h₁ h.ge)

theorem eq_bot_of_map_eq_bot (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {K : Subgroup G} (hK : K ≤ J) (h : (K.subgroupOf σ.N).map φ = ⊥) : K = ⊥ := by
  apply hφ.eq_of_map_eq_map hJ hK bot_le
  rw [h, Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem exists_of_le (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) {X : Subgroup H}
    (hX : X ≤ M) : ∃ K : Subgroup G, K ≤ J ∧ (K.subgroupOf σ.N).map φ = X := by
  refine ⟨((X.comap φ) ⊓ J.subgroupOf σ.N).map σ.N.subtype, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp ha).2
  · change ((((X.comap φ) ⊓ J.subgroupOf σ.N).map σ.N.subtype).comap σ.N.subtype).map φ = X
    rw [Subgroup.comap_map_eq_self_of_injective σ.N.subtype_injective]
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact (Subgroup.mem_inf.mp ha).1
    · intro w hw
      rw [← hφ.map_J hJ] at hX
      obtain ⟨a, ha, rfl⟩ := hX hw
      exact ⟨a, Subgroup.mem_inf.mpr ⟨hw, ha⟩, rfl⟩

theorem card_map (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J) {K : Subgroup G}
    (hK : K ≤ J) : Nat.card ((K.subgroupOf σ.N).map φ) = Nat.card K := by
  have hinj : Function.Injective (φ.domRestrict (K.subgroupOf σ.N)) := by
    intro a b hab
    apply Subtype.ext
    exact hφ.eq_of_map_eq hJ (hK (Subgroup.mem_subgroupOf.mp a.2))
      (hK (Subgroup.mem_subgroupOf.mp b.2)) hab
  rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hK.trans (hφ.J_le_N hJ))).toEquiv]

theorem isPGroup_of_map (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {K : Subgroup G} (hK : K ≤ J) {r : ℕ} (h : IsPGroup r ((K.subgroupOf σ.N).map φ)) :
    IsPGroup r K := by
  have hKN := hK.trans (hφ.J_le_N hJ)
  refine IsPGroup.of_injective h ((φ.subgroupMap (K.subgroupOf σ.N)).comp
    (Subgroup.subgroupOfEquivOfLe hKN).symm.toMonoidHom) ?_
  intro a b hab
  have h1 : φ ⟨a, hKN a.2⟩ = φ ⟨b, hKN b.2⟩ := congrArg Subtype.val hab
  have h2 := hφ.eq_of_map_eq hJ (a := ⟨a, hKN a.2⟩) (b := ⟨b, hKN b.2⟩) (hK a.2) (hK b.2) h1
  have h3 : (a : G) = b := congrArg (fun x : σ.N => (x : G)) h2
  exact Subtype.ext h3

theorem map_conjSub (_hφ : IsModelMap σ φ M y) {z : G} (hz : z ∈ σ.N) {X : Subgroup G}
    (hX : X ≤ σ.N) :
    ((TotallyInverted.conjSub z X).subgroupOf σ.N).map φ =
      TotallyInverted.conjSub (φ ⟨z, hz⟩) ((X.subgroupOf σ.N).map φ) := by
  ext w
  constructor
  · rintro ⟨a, ⟨g, hg, hga⟩, rfl⟩
    refine ⟨φ ⟨g, hX hg⟩, ⟨⟨g, hX hg⟩, hg, rfl⟩, ?_⟩
    have h1 : z * g * z⁻¹ = (a : G) := by simpa using hga
    have ha : a = ⟨z, hz⟩ * ⟨g, hX hg⟩ * (⟨z, hz⟩ : σ.N)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact h1.symm
    rw [ha, map_mul, map_mul, map_inv]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨⟨z, hz⟩ * g * (⟨z, hz⟩ : σ.N)⁻¹, ⟨g, hg, by simp⟩, by simp⟩

theorem conjSub_le (hJ : σ.IsLayerComplement J) {z : G} (hz : z ∈ σ.N) {X : Subgroup G}
    (hXJ : X ≤ J) : TotallyInverted.conjSub z X ≤ J := by
  rintro _ ⟨g, hg, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hJ.normal hz) g).mp (hXJ hg)

theorem map_inf_eq_bot (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {X : Subgroup G} (hXJ : X ≤ J) (hXC : X ⊓ σ.C = ⊥) :
    (X.subgroupOf σ.N).map φ ⊓ Subgroup.centralizer {y} = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨⟨g, hg, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hw
  have hgX : (g : G) ∈ X := Subgroup.mem_subgroupOf.mp hg
  have hcomm := hφ.commute_of_mem_J hJ (hXJ hgX)
    (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hgC : (g : G) ∈ σ.C := (mem_C_iff σ g.2).mpr (congrArg Subtype.val hcomm)
  have hg1 : (g : G) ∈ X ⊓ σ.C := Subgroup.mem_inf.mpr ⟨hgX, hgC⟩
  rw [hXC, Subgroup.mem_bot] at hg1
  rw [Subgroup.mem_bot, show g = 1 from Subtype.ext hg1, map_one]

theorem inf_C_eq_bot_of_map [Finite G] (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {X : Subgroup G} (hXJ : X ≤ J)
    (h : (X.subgroupOf σ.N).map φ ⊓ Subgroup.centralizer {y} = ⊥) : X ⊓ σ.C = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.mp hg
  have hgN := C_le_N σ hgC
  have hmem : φ ⟨g, hgN⟩ ∈ (X.subgroupOf σ.N).map φ ⊓ Subgroup.centralizer {y} := by
    refine Subgroup.mem_inf.mpr ⟨⟨⟨g, hgN⟩, hgX, rfl⟩, ?_⟩
    rw [← hφ.map_C]
    exact ⟨⟨g, hgN⟩, hgC, rfl⟩
  rw [h, Subgroup.mem_bot] at hmem
  have h1 := hφ.eq_of_map_eq hJ (a := ⟨g, hgN⟩) (b := 1) (hXJ hgX) J.one_mem
    (by rw [hmem, map_one])
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)

theorem le_normalizer_of_map [Finite G] (hφ : IsModelMap σ φ M y)
    (hJ : σ.IsLayerComplement J) {X : Subgroup G} (hXJ : X ≤ J)
    (h : Subgroup.centralizer {y} ≤
      Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup H) : Set H)) :
    σ.C ≤ Subgroup.normalizer (X : Set G) := by
  have key : ∀ c ∈ σ.C, ∀ g ∈ X, c * g * c⁻¹ ∈ X := by
    intro c hc g hg
    have hcN := C_le_N σ hc
    have hgN := hφ.J_le_N hJ (hXJ hg)
    have hJmem : ((⟨c, hcN⟩ * ⟨g, hgN⟩ * (⟨c, hcN⟩ : σ.N)⁻¹ : σ.N) : G) ∈ J := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hJ.normal hcN) g).mp (hXJ hg)
      simpa using h1
    have hcy : φ ⟨c, hcN⟩ ∈ Subgroup.centralizer {y} := by
      rw [← hφ.map_C]
      exact ⟨⟨c, hcN⟩, hc, rfl⟩
    have hmem : φ (⟨c, hcN⟩ * ⟨g, hgN⟩ * (⟨c, hcN⟩ : σ.N)⁻¹) ∈ (X.subgroupOf σ.N).map φ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (h hcy) (φ ⟨g, hgN⟩)).mp ⟨⟨g, hgN⟩, hg, rfl⟩
    exact hφ.mem_of_map_mem_J hJ hXJ hJmem hmem
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact key c hc g
  · intro hg
    have h1 := key c⁻¹ (σ.C.inv_mem hc) _ hg
    simpa [mul_assoc] using h1

theorem map_mem_signalizers [Finite G] (hφ : IsModelMap σ φ M y) (hJ : σ.IsLayerComplement J)
    {X : Subgroup G} {r : ℕ} (hX : X ∈ signalizers J σ.C r) :
    (X.subgroupOf σ.N).map φ ∈ signalizers M (Subgroup.centralizer {y}) r := by
  obtain ⟨hXJ, hXp, hCX, hXC⟩ := hX
  refine ⟨?_, hXp.comap_subtype.map φ, ?_, hφ.map_inf_eq_bot hJ hXJ hXC⟩
  · rw [← hφ.map_J hJ]
    exact Subgroup.map_mono (subgroupOf_mono_of_le hXJ σ.N)
  · rw [← hφ.map_C]
    exact hφ.le_normalizer_map (hXJ.trans (hφ.J_le_N hJ)) hCX

theorem mem_signalizers_of_map [Finite G] (hφ : IsModelMap σ φ M y)
    (hJ : σ.IsLayerComplement J) {X : Subgroup G} (hXJ : X ≤ J) {r : ℕ}
    (h : (X.subgroupOf σ.N).map φ ∈ signalizers M (Subgroup.centralizer {y}) r) :
    X ∈ signalizers J σ.C r :=
  ⟨hXJ, hφ.isPGroup_of_map hJ hXJ h.2.1, hφ.le_normalizer_of_map hJ hXJ h.2.2.1,
    hφ.inf_C_eq_bot_of_map hJ hXJ h.2.2.2⟩

end Complement

theorem cyclic [Finite G] (hφ : IsModelMap σ φ M y)
    (hcyc : IsCyclic (M ⊓ Subgroup.centralizer {y} : Subgroup H)) :
    ∀ J : Subgroup G, σ.IsLayerComplement J → IsCyclic (σ.C ⊓ J : Subgroup G) := by
  intro J hJ
  have hle : σ.C ⊓ J ≤ σ.N := inf_le_left.trans (C_le_N σ)
  let f₀ : (σ.C ⊓ J : Subgroup G) →* H := φ.comp (Subgroup.inclusion hle)
  have hf₀ : ∀ g, f₀ g ∈ M ⊓ Subgroup.centralizer {y} := by
    intro g
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hφ.map_J hJ]
      exact ⟨Subgroup.inclusion hle g, (Subgroup.mem_inf.mp g.2).2, rfl⟩
    · rw [← hφ.map_C]
      exact ⟨Subgroup.inclusion hle g, (Subgroup.mem_inf.mp g.2).1, rfl⟩
  refine isCyclic_of_injective (f₀.codRestrict _ hf₀) ?_
  intro a b hab
  have hab' : φ (Subgroup.inclusion hle a) = φ (Subgroup.inclusion hle b) :=
    congrArg Subtype.val hab
  have h1 := hφ.eq_of_map_eq hJ (a := Subgroup.inclusion hle a) (b := Subgroup.inclusion hle b)
    (Subgroup.mem_inf.mp a.2).2 (Subgroup.mem_inf.mp b.2).2 hab'
  exact Subtype.ext (congrArg (fun x : σ.N => (x : G)) h1)

theorem centralizer_le [Finite G] (hφ : IsModelMap σ φ M y) {B : Subgroup H}
    (hcent : ∀ g ∈ Subgroup.centralizer {y},
      g ∈ Subgroup.centralizer ((M ⊓ Subgroup.centralizer {y} : Subgroup H) : Set H) → g ∈ B)
    (hB : B ≤ (σ.L.subgroupOf σ.N).map φ) :
    ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ g ∈ σ.C,
      g ∈ Subgroup.centralizer ((σ.C ⊓ J : Subgroup G) : Set G) → g ∈ σ.L := by
  intro J hJ g hgC hgc
  have hgN := C_le_N σ hgC
  have h1 : φ ⟨g, hgN⟩ ∈ Subgroup.centralizer {y} := by
    rw [← hφ.map_C]
    exact ⟨⟨g, hgN⟩, hgC, rfl⟩
  have h2 : φ ⟨g, hgN⟩ ∈
      Subgroup.centralizer ((M ⊓ Subgroup.centralizer {y} : Subgroup H) : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨hwM, hwy⟩ := Subgroup.mem_inf.mp hw
    rw [← hφ.map_J hJ] at hwM
    obtain ⟨j, hj, rfl⟩ := hwM
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hjc := hφ.commute_of_mem_J hJ hjJ (Subgroup.mem_centralizer_singleton_iff.mp hwy)
    have hjC : (j : G) ∈ σ.C ⊓ J :=
      Subgroup.mem_inf.mpr ⟨(mem_C_iff σ j.2).mpr (congrArg Subtype.val hjc), hjJ⟩
    have h3 := Subgroup.mem_centralizer_iff.mp hgc j hjC
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext h3
  have hON : σ.ON ≤ σ.L := hφ.ON_le.trans le_sup_left
  exact hφ.mem_of_map_mem hON (g := ⟨g, hgN⟩) (hB (hcent _ h1 h2))

theorem signalizer_le [Finite G] (hφ : IsModelMap σ φ M y)
    (hsig : ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ U ∈ signalizers ⊤ (Subgroup.centralizer {y}) r, U ≤ M) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ U ∈ signalizers σ.N σ.C r, U ≤ σ.L₀ := by
  intro r hr hr2 U hU
  obtain ⟨hUN, hUp, hCU, hUC⟩ := hU
  have hx₂C : σ.x₂ ∈ σ.C := (mem_C_iff σ hφ.x₂_mem).mpr rfl
  have hinv : ∀ u ∈ U.subgroupOf σ.N,
      ⟨σ.x₂, hφ.x₂_mem⟩ * u * (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)⁻¹ ∈ U.subgroupOf σ.N := by
    intro u hu
    rw [Subgroup.mem_subgroupOf]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hCU hx₂C) u).mp (Subgroup.mem_subgroupOf.mp hu)
    simpa using h1
  have hinf : U.subgroupOf σ.N ⊓ Subgroup.centralizer {(⟨σ.x₂, hφ.x₂_mem⟩ : σ.N)} = ⊥ := by
    rw [← hφ.C_subgroupOf, eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    have h1 : (g : G) ∈ U ⊓ σ.C := Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_subgroupOf.mp hg1, Subgroup.mem_subgroupOf.mp hg2⟩
    rw [hUC, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have himg : (U.subgroupOf σ.N).map φ ∈ signalizers ⊤ (Subgroup.centralizer {y}) r := by
    refine ⟨le_top, hUp.comap_subtype.map φ, ?_, ?_⟩
    · rw [← hφ.map_C]
      exact hφ.le_normalizer_map hUN hCU
    · rw [← hφ.map_x₂]
      exact map_inf_centralizer_eq_bot φ hφ.odd_card_ker (Subtype.ext hφ.x₂_mul_self) hinv hinf
  intro u hu
  have hle := hsig r hr hr2 _ himg
  rw [← hφ.map_L₀] at hle
  exact hφ.mem_of_map_mem hφ.ON_le (g := ⟨u, hUN hu⟩) (hle ⟨⟨u, hUN hu⟩, hu, rfl⟩)

theorem layer_signalizer [Finite G] (hφ : IsModelMap σ φ M y) (hheight : σ.height ≠ 1)
    (hls : ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ X ∈ signalizers M (Subgroup.centralizer {y}) r, X ≠ ⊥ → σ.q % 4 = 1 ∧ r = σ.p) :
    ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ r : ℕ, r.Prime → r ≠ 2 →
      ∀ X ∈ signalizers J σ.C r, X ≠ ⊥ → σ.DeltaEpsMinus ∧ r = σ.p := by
  intro J hJ r hr hr2 X hX hXne
  have hne : (X.subgroupOf σ.N).map φ ≠ ⊥ := fun h => hXne (hφ.eq_bot_of_map_eq_bot hJ hX.1 h)
  obtain ⟨hq, hrp⟩ := hls r hr hr2 _ (hφ.map_mem_signalizers hJ hX) hne
  exact ⟨Or.inr ⟨hheight, hq⟩, hrp⟩

theorem layer_signalizer_pair [Finite G] (hφ : IsModelMap σ φ M y) {x : H}
    (hpair : σ.q % 4 = 1 → ∃ Q Qs : Subgroup H,
      Q ∈ signalizers M (Subgroup.centralizer {y}) σ.p ∧
      Qs ∈ signalizers M (Subgroup.centralizer {y}) σ.p ∧
      Nat.card Q = σ.q ∧ Nat.card Qs = σ.q ∧ Q ≠ Qs ∧ M = Q ⊔ Qs ∧
      (∀ h : H, h * y * h⁻¹ = x * y → TotallyInverted.conjSub h Q = Qs) ∧
      (∀ X ∈ signalizers M (Subgroup.centralizer {y}) σ.p, X ≤ Q ∨ X ≤ Qs) ∧
      (∀ X : Subgroup H, X ≤ Q →
        Subgroup.centralizer {y} ≤ Subgroup.normalizer (X : Set H) → X = ⊥ ∨ X = Q) ∧
      (∀ X : Subgroup H, X ≤ Qs →
        Subgroup.centralizer {y} ≤ Subgroup.normalizer (X : Set H) → X = ⊥ ∨ X = Qs))
    (hδ : σ.DeltaEpsMinus → σ.q % 4 = 1) {z : G} (hzD : z ∈ σ.D) (hzN : z ∈ σ.N)
    (hz : φ ⟨z, hzN⟩ * y * (φ ⟨z, hzN⟩)⁻¹ = x * y) :
    ∀ J : Subgroup G, σ.IsLayerComplement J → σ.DeltaEpsMinus →
      ∃ Q Qs : Subgroup G, Q ∈ signalizers J σ.C σ.p ∧ Qs ∈ signalizers J σ.C σ.p ∧
        Nat.card Q = σ.q ∧ Nat.card Qs = σ.q ∧ Q ≠ Qs ∧ J = Q ⊔ Qs ∧
        (∃ z ∈ σ.D, TotallyInverted.conjSub z Q = Qs) ∧
        (∀ X ∈ signalizers J σ.C σ.p, X ≤ Q ∨ X ≤ Qs) ∧
        (∀ X : Subgroup G, X ≤ Q → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q) ∧
        (∀ X : Subgroup G, X ≤ Qs → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Qs) := by
  intro J hJ hδε
  obtain ⟨Q', Qs', hQ', hQs', hcQ', hcQs', hne', hM', hconj', hmax', hirrQ', hirrQs'⟩ :=
    hpair (hδ hδε)
  have hJN := hφ.J_le_N hJ
  obtain ⟨Q, hQJ, hQimg⟩ := hφ.exists_of_le hJ hQ'.1
  obtain ⟨Qs, hQsJ, hQsimg⟩ := hφ.exists_of_le hJ hQs'.1
  have hirr : ∀ {P : Subgroup G} {P' : Subgroup H}, P ≤ J → (P.subgroupOf σ.N).map φ = P' →
      (∀ X : Subgroup H, X ≤ P' →
        Subgroup.centralizer {y} ≤ Subgroup.normalizer (X : Set H) → X = ⊥ ∨ X = P') →
      ∀ X : Subgroup G, X ≤ P → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = P := by
    intro P P' hPJ hPimg hP' X hXP hCX
    have hXJ := hXP.trans hPJ
    have hle : (X.subgroupOf σ.N).map φ ≤ P' :=
      hPimg ▸ Subgroup.map_mono (subgroupOf_mono_of_le hXP σ.N)
    have hnorm : Subgroup.centralizer {y} ≤
        Subgroup.normalizer (((X.subgroupOf σ.N).map φ : Subgroup H) : Set H) := by
      rw [← hφ.map_C]
      exact hφ.le_normalizer_map (hXJ.trans hJN) hCX
    rcases hP' _ hle hnorm with h | h
    · exact Or.inl (hφ.eq_bot_of_map_eq_bot hJ hXJ h)
    · exact Or.inr (hφ.eq_of_map_eq_map hJ hXJ hPJ (h.trans hPimg.symm))
  refine ⟨Q, Qs, hφ.mem_signalizers_of_map hJ hQJ (hQimg ▸ hQ'),
    hφ.mem_signalizers_of_map hJ hQsJ (hQsimg ▸ hQs'), ?_, ?_, ?_, ?_, ⟨z, hzD, ?_⟩, ?_,
    hirr hQJ hQimg hirrQ', hirr hQsJ hQsimg hirrQs'⟩
  · rw [← hφ.card_map hJ hQJ, hQimg, hcQ']
  · rw [← hφ.card_map hJ hQsJ, hQsimg, hcQs']
  · intro h
    apply hne'
    rw [← hQimg, ← hQsimg, h]
  · apply hφ.eq_of_map_eq_map hJ le_rfl (sup_le hQJ hQsJ)
    rw [hφ.map_J hJ, Subgroup.subgroupOf_sup (hQJ.trans hJN) (hQsJ.trans hJN), Subgroup.map_sup,
      hQimg, hQsimg, hM']
  · apply hφ.eq_of_map_eq_map hJ (conjSub_le hJ hzN hQJ) hQsJ
    rw [hφ.map_conjSub hzN (hQJ.trans hJN), hQimg, hQsimg, hconj' _ hz]
  · intro X hX
    rcases hmax' _ (hφ.map_mem_signalizers hJ hX) with h | h
    · exact Or.inl (hφ.le_of_map_le hJ hX.1 hQJ (hQimg ▸ h))
    · exact Or.inr (hφ.le_of_map_le hJ hX.1 hQsJ (hQsimg ▸ h))

theorem permutable_le [Finite G] (hφ : IsModelMap σ φ M y)
    (hperm : ∀ U : Subgroup H, Odd (Nat.card U) →
      (U : Set H) * (Subgroup.centralizer {y} : Set H) =
        (Subgroup.centralizer {y} : Set H) * (U : Set H) →
      ∃ (p' : ℕ) (X : Subgroup H), p'.Prime ∧ X ∈ signalizers M (Subgroup.centralizer {y}) p' ∧
        U ≤ Subgroup.centralizer {y} ⊔ X) :
    ∀ J : Subgroup G, σ.IsLayerComplement J → ∀ U : Subgroup G, U ≤ σ.N →
      Odd (Nat.card U) → (U : Set G) * (σ.C : Set G) = (σ.C : Set G) * (U : Set G) →
        ∃ (p : ℕ) (X : Subgroup G), p.Prime ∧ X ∈ signalizers J σ.C p ∧
          U ≤ σ.C ⊔ X ⊔ σ.ON := by
  intro J hJ U hUN hUodd hUC
  have hodd : Odd (Nat.card ((U.subgroupOf σ.N).map φ)) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv]
  have hU' : (σ.N.subtype : σ.N → G) '' (U.subgroupOf σ.N : Set σ.N) = U := by
    rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hUN]
  have hC' : (σ.N.subtype : σ.N → G) '' (σ.C.subgroupOf σ.N : Set σ.N) = σ.C := by
    rw [← Subgroup.coe_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (C_le_N σ)]
  have hperm' : ((U.subgroupOf σ.N).map φ : Set H) * (Subgroup.centralizer {y} : Set H) =
      (Subgroup.centralizer {y} : Set H) * ((U.subgroupOf σ.N).map φ : Set H) := by
    rw [← hφ.map_C, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul]
    congr 1
    apply (Set.image_injective.mpr σ.N.subtype_injective)
    rw [Set.image_mul, Set.image_mul, hU', hC']
    exact hUC
  obtain ⟨p', X', hp', hX', hUX'⟩ := hperm _ hodd hperm'
  obtain ⟨X, hXJ, hXimg⟩ := hφ.exists_of_le hJ hX'.1
  refine ⟨p', X, hp', hφ.mem_signalizers_of_map hJ hXJ (hXimg ▸ hX'), ?_⟩
  intro u hu
  have hON : σ.ON ≤ σ.C ⊔ X ⊔ σ.ON := le_sup_right
  apply hφ.mem_of_map_mem hON (g := ⟨u, hUN hu⟩)
  have hmem : φ ⟨u, hUN hu⟩ ∈ Subgroup.centralizer {y} ⊔ X' := hUX' ⟨⟨u, hUN hu⟩, hu, rfl⟩
  rw [← hφ.map_C, ← hXimg, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (C_le_N σ) (hXJ.trans (hφ.J_le_N hJ))] at hmem
  exact Subgroup.map_mono (subgroupOf_mono_of_le le_sup_left σ.N) hmem

end IsModelMap

end Setting

end CFSG.Wreathed.OriginalAllPrime.TIFacts
