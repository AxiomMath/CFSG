module

public import CFSG.GH74.Uniqueness.SU.SU13TB2Abs
public import CFSG.GH74.Uniqueness.SU.SU13Data
public import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.RankThree.Asc83Table.GL23

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB CFSG.GH74

variable {G : Type} [Group G]


theorem card_inf_centralizer_conj {Y : Subgroup G} {k : G} (hk : k ∈ normalizer (Y : Set G)) (z : G) :
    Nat.card (Y ⊓ centralizer ({k * z * k⁻¹} : Set G) : Subgroup G) =
      Nat.card (Y ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  have hkinv : k⁻¹ ∈ normalizer (Y : Set G) := inv_mem hk
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨k⁻¹ * x * k, ?_⟩
      invFun := fun x => ⟨k * x * k⁻¹, ?_⟩
      left_inv := fun x => ?_
      right_inv := fun x => ?_ }
  · obtain ⟨hxY, hxc⟩ := mem_inf.mp x.2
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hkinv x).mp hxY |> fun h => by simpa using h, ?_⟩
    rw [mem_centralizer_singleton_iff] at hxc ⊢
    calc k⁻¹ * x * k * z = k⁻¹ * (x * (k * z * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * z * k⁻¹) * x) * k := by rw [hxc]
      _ = z * (k⁻¹ * x * k) := by group
  · obtain ⟨hxY, hxc⟩ := mem_inf.mp x.2
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hk x).mp hxY, ?_⟩
    rw [mem_centralizer_singleton_iff] at hxc ⊢
    calc k * x * k⁻¹ * (k * z * k⁻¹) = k * (x * z) * k⁻¹ := by group
      _ = k * (z * x) * k⁻¹ := by rw [hxc]
      _ = k * z * k⁻¹ * (k * x * k⁻¹) := by group
  · apply Subtype.ext
    show k * (k⁻¹ * (x : G) * k) * k⁻¹ = x
    group
  · apply Subtype.ext
    show k⁻¹ * (k * (x : G) * k⁻¹) * k = x
    group

theorem order_Y_ten (hKI8b : K.KI8b) [Finite G] {z : G} (hz : orderOf z = 2)
    (e : Elts G z) (hm : MPart10 z e)
    (hone : ∀ u v : G, u * e.s₂ = e.s₂ * u → v * e.s₂ = e.s₂ * v → orderOf u = 2 → orderOf v = 2 →
      ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = v)
    {R : Subgroup G} (hR : IsSylowIn (centralizer ({e.s₂} : Set G)) R) (hzR : z ∈ R)
    (hRz : ∀ r ∈ R, r * z = z * r)
    (hk₁ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t)
    (hk₂ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t * z) :
    Nat.card (oc (centralizer ({e.s₂} : Set G))) = 81 ∧
      3 ^ 5 ∣ Nat.card (centralizer ({e.s₂} : Set G)) := by
  set C : Subgroup G := centralizer ({e.s₂} : Set G) with hC
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hMC : M ≤ C := inf_le_left
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr e.s₂_comm.symm
  have htC : e.t ∈ C := mem_centralizer_singleton_iff.mpr e.t_s₂
  have hone' : K.OneInvClass (Mbar C) :=
    oneInvClass_mbar (fun u v hu hv hu2 hv2 => by
      obtain ⟨c, hc, hcuv⟩ := hone u v (mem_centralizer_singleton_iff.mp hu)
        (mem_centralizer_singleton_iff.mp hv) hu2 hv2
      exact ⟨c, mem_centralizer_singleton_iff.mpr hc, hcuv⟩)
  have hmain : oc C ⊓ centralizer ({z} : Set G) = oc M :=
    oc_inf_centralizer hKI8b hone' hzC hz hR hzR hRz hm.gl
  have h9 : Nat.card (oc M) = 9 := by
    obtain ⟨e2⟩ := hm.gl
    have h48 : Nat.card (Mbar M) = 48 := by
      rw [Nat.card_congr e2.toEquiv]
      exact CFSG.RankThree.Asc83Table.card_GL23
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥M)
    have hoc : Nat.card (oc M) = Nat.card (pPrimeCore 2 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    have h48' : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = 48 := h48
    rw [hm.card, h48'] at hq
    rw [hoc]
    omega
  have hs₂Y : zpowers e.s₂ ≤ oc C := by
    refine le_oc_of_normal_odd ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr rfl)) ?_ ?_
    · intro g hg n hn
      have hc : Commute g e.s₂ := (mem_centralizer_singleton_iff.mp hg)
      have hcn : Commute g n := by
        obtain ⟨k, rfl⟩ := hn
        exact hc.zpow_right k
      have : g * n * g⁻¹ = n := by rw [hcn.eq]; group
      rw [this]; exact hn
    · rw [Nat.card_zpowers, e.s₂_ord]; decide
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have ht_sq : e.t * e.t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcomm : Commute e.t z := e.t_comm
  let T : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq hcomm
  have hTk : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq ht1 hz1
      e.t_ne hcomm
  have hTmem : ∀ x ∈ T, x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 := by
    intro x hx
    have : x ∈ ({e.t * z, e.t, z, 1} : Set G) := hx
    simpa using this
  have htT : e.t ∈ T := by
    show e.t ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzT : z ∈ T := by
    show z ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hTC : T ≤ C := by
    intro x hx
    rcases hTmem x hx with rfl | rfl | rfl | rfl
    · exact mul_mem htC hzC
    · exact htC
    · exact hzC
    · exact C.one_mem
  have hYodd : Odd (Nat.card (oc C)) := odd_card_oc C
  have hTn : T ≤ normalizer ((oc C : Subgroup G) : Set G) := fun x hx => le_normalizer_oc C (hTC hx)
  have hBW := CFSG.ABGLocalTools.card_mul_card_centralizer_four_sq (T := T) (K := oc C) hYodd hTn
    (a := e.t) (b := z) htT hzT ht1 hz1 e.t_ne
  have hYz : Nat.card (oc C ⊓ centralizer ({z} : Set G) : Subgroup G) = 9 := by
    rw [hmain]; exact h9
  have hYt : Nat.card (oc C ⊓ centralizer ({e.t} : Set G) : Subgroup G) = 9 := by
    obtain ⟨k, hk, hkz⟩ := hk₁
    have := card_inf_centralizer_conj (le_normalizer_oc C (mem_centralizer_singleton_iff.mpr hk)) z
    rw [hkz] at this
    rw [this, hYz]
  have hYtz : Nat.card (oc C ⊓ centralizer ({e.t * z} : Set G) : Subgroup G) = 9 := by
    obtain ⟨k, hk, hkz⟩ := hk₂
    have := card_inf_centralizer_conj (le_normalizer_oc C (mem_centralizer_singleton_iff.mpr hk)) z
    rw [hkz] at this
    rw [this, hYz]
  have hYT : oc C ⊓ centralizer (T : Set G) = zpowers e.s₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxY, hxT⟩ := mem_inf.mp hx
      have hxz : x * z = z * x := (mem_centralizer_iff.mp hxT z hzT).symm
      have hxt : e.t * x = x * e.t := mem_centralizer_iff.mp hxT e.t htT
      have hxM : x ∈ oc C ⊓ centralizer ({z} : Set G) :=
        mem_inf.mpr ⟨hxY, mem_centralizer_singleton_iff.mpr hxz⟩
      rw [hmain] at hxM
      exact hm.cent_t x hxM hxt
    · intro x hx
      refine mem_inf.mpr ⟨hs₂Y hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := hx
      have hcy : Commute y e.s₂ := by
        rcases hTmem y hy with rfl | rfl | rfl | rfl
        · exact Commute.mul_left e.t_s₂ e.s₂_comm.symm
        · exact e.t_s₂
        · exact e.s₂_comm.symm
        · exact Commute.one_left _
      exact hcy.zpow_right k
  have hYTcard : Nat.card (oc C ⊓ centralizer (T : Set G) : Subgroup G) = 3 := by
    rw [hYT, Nat.card_zpowers, e.s₂_ord]
  rw [hYt, hYz, hYtz, hYTcard] at hBW
  have hY81 : Nat.card (oc C) = 81 := by omega
  refine ⟨hY81, ?_⟩
  have hker : ∀ m : ↥M, proj C (Subgroup.inclusion hMC m) = 1 ↔ m ∈ pPrimeCore 2 ↥M := by
    intro m
    have hmc : (m : G) ∈ centralizer ({z} : Set G) := (mem_inf.mp m.2).2
    constructor
    · intro h
      have h1 : (Subgroup.inclusion hMC m) ∈ pPrimeCore 2 ↥C := by rw [← ker_proj C]; exact h
      have h2 : (m : G) ∈ oc C := mem_oc.mpr ⟨hMC m.2, h1⟩
      have h3 : (m : G) ∈ oc C ⊓ centralizer ({z} : Set G) := mem_inf.mpr ⟨h2, hmc⟩
      rw [hmain] at h3
      obtain ⟨hmM, h4⟩ := mem_oc.mp h3
      exact h4
    · intro h
      have h2 : (m : G) ∈ oc M := mem_oc.mpr ⟨m.2, h⟩
      rw [← hmain] at h2
      obtain ⟨hmC, h3⟩ := mem_oc.mp (mem_inf.mp h2).1
      rw [← MonoidHom.mem_ker, ker_proj C]
      exact h3
  let ψ : ↥M →* Mbar C := (proj C).comp (Subgroup.inclusion hMC)
  have hψker : ψ.ker = pPrimeCore 2 ↥M := by
    ext m
    exact hker m
  have hψcard := Subgroup.card_ker_mul_card_range ψ
  have hker9 : Nat.card ψ.ker = 9 := by
    rw [hψker]
    have hoc : Nat.card (oc M) = Nat.card (pPrimeCore 2 ↥M) :=
      Subgroup.card_map_of_injective M.subtype_injective
    rw [← hoc]; exact h9
  rw [hker9, hm.card] at hψcard
  have hrange : Nat.card ψ.range = 48 := by omega
  have hdvd1 : Nat.card ψ.range ∣ Nat.card (Mbar C) := Subgroup.card_subgroup_dvd_card ψ.range
  have hCq := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥C)
  have hoc81 : Nat.card (pPrimeCore 2 ↥C) = 81 := by
    have : Nat.card (oc C) = Nat.card (pPrimeCore 2 ↥C) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [← this]; exact hY81
  have hCq' : Nat.card ↥C = Nat.card (Mbar C) * 81 := by rw [hCq, hoc81]
  rw [hrange] at hdvd1
  obtain ⟨c, hc⟩ := hdvd1
  rw [hCq', hc]
  exact ⟨16 * c, by ring⟩

end CFSG.GH74.Uniqueness.SU.SU13
