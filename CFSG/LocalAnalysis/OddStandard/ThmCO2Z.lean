module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.Adapters.Involutions
public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG.OddStandard.ThmC.O2.ZN

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_mul_self {z : G} (hz2 : z * z = 1) : IsPGroup 2 (zpowers z) := by
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  rw [Nat.card_zpowers]
  exact orderOf_dvd_of_pow_eq_one (by rw [Nat.pow_one, sq]; exact hz2)

omit [Finite G] in
theorem mem_sylow_of_central_involution (S : Sylow 2 G) {z : G} (hz : z ∈ center G)
    (hz2 : z * z = 1) : z ∈ (S : Subgroup G) := by
  have hn : (zpowers z).Normal := normal_of_le_center (by rwa [zpowers_le])
  exact (isPGroup_zpowers_of_mul_self hz2).le_sylow_of_normal S (mem_zpowers z)

omit [Finite G] in
theorem Z_cases {S : Subgroup G} (td : TData S) {z z' : G} (hzZ : z ∈ td.Z)
    (hcard : Nat.card (zpowers z) = 2) (hz'Z : z' ∈ td.Z) (hz' : z' ∉ zpowers z) :
    ∀ w ∈ td.Z, w ∈ zpowers z ∨ ∃ c ∈ zpowers z, w = c * z' := by
  have hle : zpowers z ≤ td.Z := zpowers_le.2 hzZ
  have hidx : ((zpowers z).subgroupOf td.Z).index = 2 := by
    have h1 := Subgroup.card_mul_index ((zpowers z).subgroupOf td.Z)
    have h2 : Nat.card ((zpowers z).subgroupOf td.Z) = 2 := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h2, td.card_Z] at h1
    omega
  intro w hw
  by_cases hwz : w ∈ zpowers z
  · exact Or.inl hwz
  · refine Or.inr ⟨w * z', ?_, ?_⟩
    · exact (Subgroup.mul_mem_iff_of_index_two (a := (⟨w, hw⟩ : td.Z))
        (b := (⟨z', hz'Z⟩ : td.Z)) hidx).2
        (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false hwz hz')
    · rw [mul_assoc, td.Z_sq z' hz'Z, mul_one]

theorem exists_conj_mem_of_le {H : Type} [Group H] [Finite H] (P : Sylow 2 H) (C W : Subgroup H)
    (hPC : (P : Subgroup H) ≤ C) (hWC : W ≤ C) (hW : IsPGroup 2 W) :
    ∃ c ∈ C, ∀ w ∈ W, c * w * c⁻¹ ∈ (P : Subgroup H) := by
  have hW' : IsPGroup 2 (W.subgroupOf C) := hW.comap_subtype
  obtain ⟨Q, hQ⟩ := hW'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q (P.subtype hPC)
  refine ⟨c, c.2, fun w hw => ?_⟩
  have hwQ : (⟨w, hWC hw⟩ : C) ∈ Q := hQ (by rwa [Subgroup.mem_subgroupOf])
  have hmem : MulAut.conj c • (⟨w, hWC hw⟩ : C) ∈ ((c • Q : Sylow 2 C) : Subgroup C) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hwQ
  rw [hc, Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  simpa [MulAut.smul_def, MulAut.conj_apply] using hmem

theorem weakClosed_of_extremal {H : Type} [Group H] [Finite H] (P : Sylow 2 H) {x : H}
    (hx1 : x ≠ 1) (hxc : ∀ p ∈ (P : Subgroup H), p * x = x * p)
    (hcomm : ∀ u ∈ (P : Subgroup H), ∀ v ∈ (P : Subgroup H),
      u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = x)
    (hext : ∀ a ∈ (P : Subgroup H), a ≠ 1 → a ≠ x → ∃ u ∈ (P : Subgroup H),
      ∃ v ∈ (P : Subgroup H), u * a = a * u ∧ v * a = a * v ∧ u * v * u⁻¹ * v⁻¹ = x)
    (g : H) (hg : g⁻¹ * x * g ∈ (P : Subgroup H)) : g⁻¹ * x * g = x := by
  by_contra hne
  have ha1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨u, hu, v, hv, hua, hva, huv⟩ := hext _ hg ha1 hne
  set C : Subgroup H := centralizer ({x} : Set H) with hC
  have hPC : (P : Subgroup H) ≤ C := fun p hp => mem_centralizer_singleton_iff.2 (hxc p hp)
  set Q : Subgroup H := (P : Subgroup H).map (MulAut.conj g).toMonoidHom with hQ
  have hQp : IsPGroup 2 (Q ⊓ C : Subgroup H) := (P.isPGroup'.map _).to_inf_left
  have hconj : ∀ y ∈ (P : Subgroup H), y * (g⁻¹ * x * g) = (g⁻¹ * x * g) * y →
      g * y * g⁻¹ ∈ Q ⊓ C := by
    intro y hy hyc
    refine ⟨⟨y, hy, by simp [MulAut.conj_apply]⟩, mem_centralizer_singleton_iff.2 ?_⟩
    calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by rw [hyc]
      _ = x * (g * y * g⁻¹) := by group
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_le P C (Q ⊓ C) hPC inf_le_right hQp
  have hcx : c * x = x * c := mem_centralizer_singleton_iff.1 hcC
  have h3 := hcomm _ (hc _ (hconj u hu hua)) _ (hc _ (hconj v hv hva))
  have key : (c * (g * u * g⁻¹) * c⁻¹) * (c * (g * v * g⁻¹) * c⁻¹) * (c * (g * u * g⁻¹) * c⁻¹)⁻¹ *
      (c * (g * v * g⁻¹) * c⁻¹)⁻¹ = c * g * (u * v * u⁻¹ * v⁻¹) * g⁻¹ * c⁻¹ := by group
  rw [key, huv] at h3
  rcases h3 with h3 | h3
  · apply hx1
    calc x = (c * g)⁻¹ * (c * g * x * g⁻¹ * c⁻¹) * (c * g) := by group
      _ = 1 := by rw [h3]; group
  · apply hne
    have hcx' : c⁻¹ * x * c = x := by
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcx]
        _ = x := by group
    have hgx : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = c⁻¹ * (c * g * x * g⁻¹ * c⁻¹) * c := by group
        _ = c⁻¹ * x * c := by rw [h3]
        _ = x := hcx'
    calc g⁻¹ * x * g = g⁻¹ * (g * x * g⁻¹) * g := by rw [hgx]
      _ = x := by group

theorem central_of_weakClosed {H : Type} [Group H] [Finite H] (hO : pPrimeCore 2 H = ⊥)
    (P : Sylow 2 H) {x : H} (hxP : x ∈ (P : Subgroup H)) (hx1 : x ≠ 1) (hx2 : x * x = 1)
    (hxc : ∀ p ∈ (P : Subgroup H), p * x = x * p)
    (hwc : ∀ g : H, g⁻¹ * x * g ∈ (P : Subgroup H) → g⁻¹ * x * g = x) (g : H) :
    g * x = x * g := by
  have hodd : oddCore H = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hO]
    exact sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  have hord : orderOf (⟨x, hxP⟩ : (P : Subgroup H)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · ext
      simpa [sq] using hx2
    · intro h
      exact hx1 (congrArg Subtype.val h)
  have hcen : (⟨x, hxP⟩ : (P : Subgroup H)) ∈ center (P : Subgroup H) := by
    rw [mem_center_iff]
    intro p
    exact Subtype.ext (hxc p p.2)
  obtain ⟨hfirst, -⟩ := CFSG.Adapters.glauberman_zStar P ⟨x, hxP⟩ hcen hord hwc
  obtain ⟨c, hc, k, hk, rfl⟩ := hfirst g
  rw [hodd, mem_bot] at hk
  subst hk
  rw [mul_one]
  exact mem_centralizer_singleton_iff.1 hc

omit [Finite G] in
theorem mul_comm_of_conj_mem_ker {H : Type} [Group H] (f : G →* H) {s a : G}
    (h : s * a * s⁻¹ * a⁻¹ ∈ f.ker) : f s * f a = f a * f s := by
  have h' := MonoidHom.mem_ker.1 h
  simp only [map_mul, map_inv] at h'
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
  exact h'

theorem Z_normal_of_ker {H : Type} [Group H] [Finite H] (f : G →* H) (hf : Function.Surjective f)
    (hO : pPrimeCore 2 H = ⊥) (S : Sylow 2 G) (td : TData (S : Subgroup G)) {z : G}
    (hker : f.ker = zpowers z) (hz : z ∈ center G) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    td.Z.Normal := by
  have hzS := mem_sylow_of_central_involution S hz hz2
  have hzZ : z ∈ td.Z := (td.mem_Z z).2 ⟨hzS, fun s hs => (mem_center_iff.1 hz s).symm⟩
  have hcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hle : zpowers z ≤ td.Z := zpowers_le.2 hzZ
  obtain ⟨z', hz'Z, hz'⟩ : ∃ z' ∈ td.Z, z' ∉ zpowers z := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show td.Z ≤ zpowers z from hcon)
    rw [td.card_Z, hcard] at this
    omega
  have hcases := Z_cases td hzZ hcard hz'Z hz'
  have hz'S : z' ∈ (S : Subgroup G) := ((td.mem_Z z').1 hz'Z).1
  have hz'c : ∀ s ∈ (S : Subgroup G), z' * s = s * z' := ((td.mem_Z z').1 hz'Z).2
  have hZq : ∀ w ∈ td.Z, w ∉ zpowers z → f w = f z' := by
    intro w hw hwz
    rcases hcases w hw with h | ⟨c, hc, rfl⟩
    · exact absurd h hwz
    · rw [map_mul, MonoidHom.mem_ker.1 (by rwa [hker]), one_mul]
  have hZq' : ∀ w ∈ td.Z, f w = 1 ∨ f w = f z' := by
    intro w hw
    by_cases hwz : w ∈ zpowers z
    · left
      rw [← MonoidHom.mem_ker, hker]
      exact hwz
    · exact Or.inr (hZq w hw hwz)
  set P : Sylow 2 H := S.mapSurjective hf with hP
  have hmemP : ∀ y : H, y ∈ (P : Subgroup H) ↔ ∃ s ∈ (S : Subgroup G), f s = y := fun y =>
    Subgroup.mem_map
  have hx1 : f z' ≠ 1 := fun h => hz' (by rw [← hker]; exact h)
  have hxP : f z' ∈ (P : Subgroup H) := (hmemP _).2 ⟨z', hz'S, rfl⟩
  have hx2 : f z' * f z' = 1 := by rw [← map_mul, td.Z_sq z' hz'Z, map_one]
  have hxc : ∀ p ∈ (P : Subgroup H), p * f z' = f z' * p := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := (hmemP p).1 hp
    rw [← map_mul, ← map_mul, hz'c s hs]
  have hcomm : ∀ u ∈ (P : Subgroup H), ∀ v ∈ (P : Subgroup H),
      u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = f z' := by
    intro u hu v hv
    obtain ⟨s, hs, rfl⟩ := (hmemP u).1 hu
    obtain ⟨t, ht, rfl⟩ := (hmemP v).1 hv
    have : f s * f t * (f s)⁻¹ * (f t)⁻¹ = f (s * t * s⁻¹ * t⁻¹) := by simp
    rw [this]
    exact hZq' _ (td.comm_mem_Z s hs t ht)
  have hext : ∀ a ∈ (P : Subgroup H), a ≠ 1 → a ≠ f z' → ∃ u ∈ (P : Subgroup H),
      ∃ v ∈ (P : Subgroup H), u * a = a * u ∧ v * a = a * v ∧ u * v * u⁻¹ * v⁻¹ = f z' := by
    intro a ha ha1 hax
    obtain ⟨a₀, ha₀, rfl⟩ := (hmemP a).1 ha
    have ha₀Z : a₀ ∉ td.Z := fun h => (hZq' a₀ h).elim ha1 hax
    obtain ⟨s, hs, t, ht, h1, h2, h3⟩ := td.extremal z hzZ hz1 a₀ ha₀ ha₀Z
    refine ⟨f s, (hmemP _).2 ⟨s, hs, rfl⟩, f t, (hmemP _).2 ⟨t, ht, rfl⟩, ?_, ?_, ?_⟩
    · exact mul_comm_of_conj_mem_ker f (by rwa [hker])
    · exact mul_comm_of_conj_mem_ker f (by rwa [hker])
    · have : f s * f t * (f s)⁻¹ * (f t)⁻¹ = f (s * t * s⁻¹ * t⁻¹) := by simp
      rw [this]
      exact hZq _ (td.comm_mem_Z s hs t ht) h3
  have hwc := weakClosed_of_extremal P hx1 hxc hcomm hext
  have hcen := central_of_weakClosed hO P hxP hx1 hx2 hxc hwc
  have hconj : ∀ g : G, g * z' * g⁻¹ ∈ td.Z := by
    intro g
    have hmem : g * z' * g⁻¹ * z'⁻¹ ∈ zpowers z := by
      rw [← hker, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul.2 (hcen (f g)), mul_inv_cancel]
    simpa using td.Z.mul_mem (hle hmem) hz'Z
  refine ⟨fun n hn g => ?_⟩
  rcases hcases n hn with h | ⟨c, hc, rfl⟩
  · have hcn : n ∈ center G := (zpowers_le.2 hz) h
    have : g * n * g⁻¹ = n := by
      rw [mem_center_iff.1 hcn g]
      simp
    rw [this]
    exact hn
  · have hcc : c ∈ center G := (zpowers_le.2 hz) hc
    have : g * (c * z') * g⁻¹ = c * (g * z' * g⁻¹) := by
      calc g * (c * z') * g⁻¹ = (g * c) * z' * g⁻¹ := by group
        _ = (c * g) * z' * g⁻¹ := by rw [mem_center_iff.1 hcc g]
        _ = c * (g * z' * g⁻¹) := by group
    rw [this]
    exact td.Z.mul_mem (hle hc) (hconj g)

end CFSG.OddStandard.ThmC.O2.ZN

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem Z_normal_of_central_involution (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) {z : G} (hz : z ∈ center G) (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    td.Z.Normal := by
  have hle : zpowers z ≤ center G := zpowers_le.2 hz
  have hn : (zpowers z).Normal := normal_of_le_center hle
  have hp : IsPGroup 2 (zpowers z) := ZN.isPGroup_zpowers_of_mul_self hz2
  have hO' : pPrimeCore 2 (G ⧸ zpowers z) = ⊥ := by
    rw [central_p_subgroup_prime_core_quotient (zpowers z) hle hp, hO, Subgroup.map_bot]
  exact ZN.Z_normal_of_ker (QuotientGroup.mk' (zpowers z)) (QuotientGroup.mk'_surjective _)
    hO' S td (QuotientGroup.ker_mk' _) hz hz1 hz2

end CFSG.OddStandard.ThmC.O2
