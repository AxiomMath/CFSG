module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LUna
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LCycAb

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Core

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

structure E25Hyp (J : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V ≃ₗ[ZMod 2] V) : Prop where
  dim : finrank (ZMod 2) V = 8
  abel : ∀ g ∈ J, ∀ k ∈ J, g * k = k * g
  exp : ∀ g ∈ J, g ^ 5 = 1
  mem : a ∈ J
  ord : orderOf a = 5
  fix : ∀ v : V, a v = v → v = 0

theorem E25_eq_one_of_fix {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v : V, g v = v) : g = 1 :=
  LinearEquiv.ext hg

theorem E25_exists_restr (J : Subgroup (V ≃ₗ[ZMod 2] V)) (M : Submodule (ZMod 2) V)
    (hM : ∀ g ∈ J, Stable g M) :
    ∃ r : J →* (M ≃ₗ[ZMod 2] M),
      ∀ (g : J) (u : M), ((r g u : M) : V) = (g : V ≃ₗ[ZMod 2] V) u := by
  have hmap : ∀ g : J, M.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = M := by
    intro g
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact hM g g.2 u hu
    · intro u hu
      refine ⟨((g : V ≃ₗ[ZMod 2] V)⁻¹) u, hM _ (J.inv_mem g.2) u hu, ?_⟩
      simp
  exact ⟨{ toFun := fun g => LinearEquiv.ofSubmodules (g : V ≃ₗ[ZMod 2] V) M M (hmap g)
           map_one' := by ext u; rfl
           map_mul' := fun g g' => by ext u; rfl }, fun g u => rfl⟩

variable [Module.Finite (ZMod 2) V] {J : Subgroup (V ≃ₗ[ZMod 2] V)} {a : V ≃ₗ[ZMod 2] V}

theorem E25_finite_GL : Finite (V ≃ₗ[ZMod 2] V) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V)) DFunLike.coe_injective

theorem E25_stable_finrank (hH : E25Hyp J a) {U : Submodule (ZMod 2) V}
    (hU : ∀ g ∈ J, Stable g U) (hU0 : U ≠ ⊥) :
    finrank (ZMod 2) U = 4 ∨ finrank (ZMod 2) U = 8 := by
  have h5 : a ^ 5 = 1 := hH.exp a hH.mem
  have hdvd := four_dvd_finrank_of_stable h5 (hU a hH.mem) (fun u _ hu => hH.fix u hu)
  have hle : finrank (ZMod 2) U ≤ 8 := hH.dim ▸ Submodule.finrank_le U
  have hpos : finrank (ZMod 2) U ≠ 0 := fun h0 => hU0 (Submodule.finrank_eq_zero.mp h0)
  obtain ⟨k, hk⟩ := hdvd
  omega

theorem E25_stable_le (hH : E25Hyp J a) {M U : Submodule (ZMod 2) V}
    (hM : finrank (ZMod 2) M = 4) (hU : ∀ g ∈ J, Stable g U) (hUM : U ≤ M) : U = ⊥ ∨ U = M := by
  by_cases h0 : U = ⊥
  · exact Or.inl h0
  · right
    have hle : finrank (ZMod 2) U ≤ 4 := hM ▸ Submodule.finrank_mono hUM
    rcases E25_stable_finrank hH hU h0 with h4 | h8
    · exact Submodule.eq_of_le_of_finrank_eq hUM (by rw [h4, hM])
    · omega

theorem E25_odd (hH : E25Hyp J a) : Odd (Nat.card J) := by
  haveI := E25_finite_GL (V := V)
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : IsPGroup 5 J := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hH.exp g g.2⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  rw [hn]
  exact Odd.pow (by decide)

theorem E25_eq_zpowers_of_card (hH : E25Hyp J a) (hcard : Nat.card J = 5) :
    J = Subgroup.zpowers a := by
  haveI := E25_finite_GL (V := V)
  have hle : Subgroup.zpowers a ≤ J := Subgroup.zpowers_le.mpr hH.mem
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hH.ord, hcard]

theorem E25_eq_zpowers_of_isCyclic (hH : E25Hyp J a) (hcyc : IsCyclic J) :
    J = Subgroup.zpowers a := by
  haveI := E25_finite_GL (V := V)
  apply E25_eq_zpowers_of_card hH
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := J)
  have hg5 : g ^ 5 = 1 := Subtype.ext (by simpa using hH.exp g g.2)
  have h1 : Nat.card J ∣ 5 := hg ▸ orderOf_dvd_of_pow_eq_one hg5
  have h2 : 5 ∣ Nat.card J := by
    have := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hH.mem)
    rwa [Nat.card_zpowers, hH.ord] at this
  exact Nat.dvd_antisymm h1 h2

theorem E25_exists_stable_four (hH : E25Hyp J a) (hne : J ≠ Subgroup.zpowers a) :
    ∃ M : Submodule (ZMod 2) V, (∀ g ∈ J, Stable g M) ∧ finrank (ZMod 2) M = 4 := by
  by_contra hno
  have hno' : ∀ M : Submodule (ZMod 2) V, (∀ g ∈ J, Stable g M) → finrank (ZMod 2) M ≠ 4 :=
    fun M hM h4 => hno ⟨M, hM, h4⟩
  apply hne
  apply E25_eq_zpowers_of_isCyclic hH
  apply isCyclic_of_irreducible_abelian J hH.abel
  intro U hU
  by_cases h0 : U = ⊥
  · exact Or.inl h0
  · right
    rcases E25_stable_finrank hH hU h0 with h4 | h8
    · exact absurd h4 (hno' U hU)
    · exact Submodule.eq_top_of_finrank_eq (by rw [h8, hH.dim])

theorem E25_exists_two (hH : E25Hyp J a) (hne : J ≠ Subgroup.zpowers a) :
    ∃ M₁ M₂ : Submodule (ZMod 2) V, finrank (ZMod 2) M₁ = 4 ∧ finrank (ZMod 2) M₂ = 4 ∧
      IsCompl M₁ M₂ ∧ (∀ g ∈ J, Stable g M₁) ∧ ∀ g ∈ J, Stable g M₂ := by
  obtain ⟨M₁, hM₁, hd₁⟩ := E25_exists_stable_four hH hne
  obtain ⟨M₂, hc, hM₂⟩ := exists_stable_complement J (E25_odd hH) M₁ hM₁
  refine ⟨M₁, M₂, hd₁, ?_, hc, hM₁, hM₂⟩
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  have h2 := hH.dim
  omega

theorem E25_range_restr (hH : E25Hyp J a) {M : Submodule (ZMod 2) V}
    (hd : finrank (ZMod 2) M = 4) (r : J →* (M ≃ₗ[ZMod 2] M))
    (hr : ∀ (g : J) (u : M), ((r g u : M) : V) = (g : V ≃ₗ[ZMod 2] V) u) :
    Nat.card r.range = 5 ∧ r.range = Subgroup.zpowers (r ⟨a, hH.mem⟩) := by
  haveI := E25_finite_GL (V := M)
  have hirr : ∀ U : Submodule (ZMod 2) M, (∀ g ∈ r.range, Stable g U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have hW : ∀ g ∈ J, Stable g (U.map M.subtype) := by
      rintro g hg _ ⟨u, hu, rfl⟩
      exact ⟨r ⟨g, hg⟩ u, hU _ ⟨⟨g, hg⟩, rfl⟩ u hu, hr ⟨g, hg⟩ u⟩
    rcases E25_stable_le hH hd hW (Submodule.map_subtype_le M U) with h | h
    · left
      exact Submodule.map_injective_of_injective M.injective_subtype (by rw [h, Submodule.map_bot])
    · right
      exact Submodule.map_injective_of_injective M.injective_subtype
        (by rw [h, Submodule.map_subtype_top])
  have hab : ∀ g ∈ r.range, ∀ k ∈ r.range, g * k = k * g := by
    rintro _ ⟨g, rfl⟩ _ ⟨k, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg r (Subtype.ext (hH.abel g g.2 k k.2))
  have hcyc : IsCyclic r.range := isCyclic_of_irreducible_abelian r.range hab hirr
  have hr5 : ∀ g : J, (r g) ^ 5 = 1 := fun g => by
    rw [← map_pow]
    have : g ^ 5 = 1 := Subtype.ext (by simpa using hH.exp g g.2)
    rw [this, map_one]
  have hra : r ⟨a, hH.mem⟩ ≠ 1 := by
    intro h1
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (fun h => by rw [h, finrank_bot] at hd; omega : M ≠ ⊥)
    have := hr ⟨a, hH.mem⟩ ⟨u, hu⟩
    rw [h1] at this
    exact hu0 (hH.fix u this.symm)
  have hord : orderOf (r ⟨a, hH.mem⟩) = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime (hr5 _) hra
  have hle : Subgroup.zpowers (r ⟨a, hH.mem⟩) ≤ r.range := Subgroup.zpowers_le.mpr ⟨_, rfl⟩
  have hcard5 : Nat.card r.range = 5 := by
    have h1 : 5 ∣ Nat.card r.range := by
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hord] at this
    have h2 : Nat.card r.range ∣ 5 := by
      rw [← IsCyclic.exponent_eq_card]
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, g, rfl⟩
      exact Subtype.ext (hr5 g)
    exact Nat.dvd_antisymm h2 h1
  refine ⟨hcard5, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
  rw [Nat.card_zpowers, hord, hcard5]

theorem E25_kernel_data (hH : E25Hyp J a) {M : Submodule (ZMod 2) V}
    (hM : ∀ g ∈ J, Stable g M) (hd : finrank (ZMod 2) M = 4) :
    ∃ K : Subgroup (V ≃ₗ[ZMod 2] V), K ≤ J ∧ (∀ g, g ∈ K ↔ g ∈ J ∧ ∀ u ∈ M, g u = u) ∧
      Nat.card K * 5 = Nat.card J ∧
      (∀ H : Subgroup (V ≃ₗ[ZMod 2] V), H ≤ J → H ⊓ K = ⊥ → Nat.card H ∣ 5) ∧
      ∀ g ∈ J, ∃ k : ℕ, ∀ v ∈ M, g v = a ^ k • v := by
  haveI := E25_finite_GL (V := M)
  obtain ⟨r, hr⟩ := E25_exists_restr J M hM
  obtain ⟨hcard5, hzp⟩ := E25_range_restr hH hd r hr
  have hKmem : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ (MonoidHom.ker r).map J.subtype ↔
      g ∈ J ∧ ∀ u ∈ M, g u = u := by
    intro g
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j.2, fun u hu => ?_⟩
      have := hr j ⟨u, hu⟩
      rw [MonoidHom.mem_ker.mp hj] at this
      exact this.symm
    · rintro ⟨hg, hfix⟩
      refine ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      ext u
      rw [hr ⟨g, hg⟩ u]
      exact hfix u u.2
  refine ⟨(MonoidHom.ker r).map J.subtype, Subgroup.map_subtype_le _, hKmem, ?_, ?_, ?_⟩
  · rw [Subgroup.card_subtype J (MonoidHom.ker r)]
    have := Subgroup.card_mul_index (MonoidHom.ker r)
    rwa [Subgroup.index_ker, hcard5] at this
  · intro H hHJ hHK
    let f : H →* (M ≃ₗ[ZMod 2] M) := r.comp (Subgroup.inclusion hHJ)
    have hinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro h hh
      have h1 : r (Subgroup.inclusion hHJ h) = 1 := hh
      have hmemK : (h : V ≃ₗ[ZMod 2] V) ∈ (MonoidHom.ker r).map J.subtype :=
        (hKmem _).mpr ⟨hHJ h.2, fun u hu => by
          have := hr (Subgroup.inclusion hHJ h) ⟨u, hu⟩
          rw [h1] at this
          exact this.symm⟩
      have h2 : (h : V ≃ₗ[ZMod 2] V) ∈ H ⊓ (MonoidHom.ker r).map J.subtype := ⟨h.2, hmemK⟩
      rw [hHK, Subgroup.mem_bot] at h2
      exact Subtype.ext h2
    have h1 : Nat.card H = Nat.card f.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [h1, ← hcard5]
    apply Subgroup.card_dvd_of_le
    rw [MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · intro g hg
    have hmem : r ⟨g, hg⟩ ∈ Subgroup.zpowers (r ⟨a, hH.mem⟩) := hzp ▸ ⟨_, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
    refine ⟨n, fun v hv => ?_⟩
    have h2 := hr (⟨a, hH.mem⟩ ^ n) ⟨v, hv⟩
    rw [map_pow, hn, hr ⟨g, hg⟩ ⟨v, hv⟩] at h2
    rw [h2]
    simp

theorem E25_card_data {G : Type*} [Group G] [Finite G] {J K₁ K₂ : Subgroup G} (h₁ : K₁ ≤ J)
    (h₂ : K₂ ≤ J) (hbot : K₁ ⊓ K₂ = ⊥) (c₁ : Nat.card K₁ * 5 = Nat.card J)
    (c₂ : Nat.card K₂ * 5 = Nat.card J) (d₁ : Nat.card K₁ ∣ 5) (hJ5 : Nat.card J ≠ 5) :
    Nat.card K₁ = 5 ∧ Nat.card K₂ = 5 ∧ Nat.card J = 25 ∧ K₁ ⊔ K₂ = J := by
  have hK₁ : Nat.card K₁ = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp d₁ with h | h
    · exact absurd (by omega) hJ5
    · exact h
  have hJ : Nat.card J = 25 := by omega
  have hK₂ : Nat.card K₂ = 5 := by omega
  refine ⟨hK₁, hK₂, hJ, ?_⟩
  have hS : K₁ ⊔ K₂ ≤ J := sup_le h₁ h₂
  have hd₁ : 5 ∣ Nat.card ↥(K₁ ⊔ K₂) := hK₁ ▸ Subgroup.card_dvd_of_le le_sup_left
  have hd₂ : Nat.card ↥(K₁ ⊔ K₂) ∣ 5 ^ 2 := by
    have := Subgroup.card_dvd_of_le hS
    rwa [hJ] at this
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hd₂
  have hcS : Nat.card ↥(K₁ ⊔ K₂) = 25 := by
    interval_cases i
    · rw [hi'] at hd₁
      norm_num at hd₁
    · have e₁ : K₁ = K₁ ⊔ K₂ := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
      have e₂ : K₂ = K₁ ⊔ K₂ := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
      have hK12 : K₁ = K₂ := e₁.trans e₂.symm
      have : K₁ = ⊥ := by rw [← hbot, ← hK12, inf_idem]
      rw [this, Subgroup.card_bot] at hK₁
      omega
    · simpa using hi'
  exact Subgroup.eq_of_le_of_card_ge hS (by omega)

theorem E25_fix_eq (hH : E25Hyp J a) {K : Subgroup (V ≃ₗ[ZMod 2] V)} (hKJ : K ≤ J)
    {M : Submodule (ZMod 2) V} (hd : finrank (ZMod 2) M = 4) (hKM : ∀ g ∈ K, ∀ u ∈ M, g u = u)
    (hK : K ≠ ⊥) (v : V) : v ∈ M ↔ ∀ g ∈ K, g v = v := by
  refine ⟨fun hv g hg => hKM g hg v hv, fun hv => ?_⟩
  let C : Submodule (ZMod 2) V :=
    { carrier := {w | ∀ g ∈ K, g w = w}
      add_mem' := fun {w w'} hw hw' g hg => by rw [map_add, hw g hg, hw' g hg]
      zero_mem' := fun g _ => map_zero g
      smul_mem' := fun c w hw g hg => by rw [map_smul, hw g hg] }
  have hMC : M ≤ C := fun u hu g hg => hKM g hg u hu
  have hCst : ∀ j ∈ J, Stable j C := by
    intro j hj w hw g hg
    have h1 : g * j = j * g := hH.abel g (hKJ hg) j hj
    calc g (j w) = (g * j) w := rfl
      _ = (j * g) w := by rw [h1]
      _ = j w := by show j (g w) = j w; rw [hw g hg]
  have hC0 : C ≠ ⊥ := by
    intro h0
    have : finrank (ZMod 2) M ≤ finrank (ZMod 2) C := Submodule.finrank_mono hMC
    rw [h0, finrank_bot, hd] at this
    omega
  have hCM : C = M := by
    rcases E25_stable_finrank hH hCst hC0 with h4 | h8
    · exact (Submodule.eq_of_le_of_finrank_eq hMC (by rw [h4, hd])).symm
    · exfalso
      have hC : C = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h8, hH.dim])
      apply hK
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      apply E25_eq_one_of_fix
      intro w
      have : w ∈ C := by rw [hC]; trivial
      exact this g hg
  rw [← hCM]
  exact hv

theorem E25_unique (hH : E25Hyp J a) {M₁ M₂ : Submodule (ZMod 2) V}
    (hd₁ : finrank (ZMod 2) M₁ = 4) (hd₂ : finrank (ZMod 2) M₂ = 4) (hc : IsCompl M₁ M₂)
    (hs₁ : ∀ g ∈ J, Stable g M₁) (hs₂ : ∀ g ∈ J, Stable g M₂)
    {K : Subgroup (V ≃ₗ[ZMod 2] V)} (hKJ : K ≤ J) (hKM : ∀ g ∈ K, ∀ u ∈ M₁, g u = u)
    (hK : K ≠ ⊥) {U : Submodule (ZMod 2) V} (hU : ∀ g ∈ J, Stable g U)
    (hdU : finrank (ZMod 2) U = 4) : U = M₁ ∨ U = M₂ := by
  by_contra hcon
  have hn₁ : U ≠ M₁ := fun h => hcon (Or.inl h)
  have hn₂ : U ≠ M₂ := fun h => hcon (Or.inr h)
  have hinf : ∀ {M : Submodule (ZMod 2) V}, finrank (ZMod 2) M = 4 → (∀ g ∈ J, Stable g M) →
      U ≠ M → U ⊓ M = ⊥ := by
    intro M hdM hsM hne
    have hst : ∀ g ∈ J, Stable g (U ⊓ M) := fun g hg w hw =>
      Submodule.mem_inf.mpr ⟨hU g hg w hw.1, hsM g hg w hw.2⟩
    rcases E25_stable_le hH hdM hst inf_le_right with h | h
    · exact h
    · exfalso
      apply hne
      have hle : M ≤ U := h ▸ inf_le_left
      exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdM, hdU])).symm
  have h1 : U ⊓ M₁ = ⊥ := hinf hd₁ hs₁ hn₁
  have h2 : U ⊓ M₂ = ⊥ := hinf hd₂ hs₂ hn₂
  apply hK
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hgJ := hKJ hg
  have hM₂ : ∀ v : V, g v - v ∈ M₂ := by
    intro v
    have hv : v ∈ M₁ ⊔ M₂ := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
    have : g (m₁ + m₂) - (m₁ + m₂) = g m₂ - m₂ := by
      rw [map_add, hKM g hg m₁ hm₁]
      abel
    rw [this]
    exact M₂.sub_mem (hs₂ g hgJ m₂ hm₂) hm₂
  have hU' : ∀ u ∈ U, g u = u := by
    intro u hu
    have h3 : g u - u ∈ U ⊓ M₂ := ⟨U.sub_mem (hU g hgJ u hu) hu, hM₂ u⟩
    rw [h2, Submodule.mem_bot] at h3
    exact sub_eq_zero.mp h3
  have hsup : U ⊔ M₁ = ⊤ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U M₁
    rw [h1, finrank_bot] at this
    have h8 := hH.dim
    exact Submodule.eq_top_of_finrank_eq (by omega)
  apply E25_eq_one_of_fix
  intro v
  have hv : v ∈ U ⊔ M₁ := by rw [hsup]; trivial
  obtain ⟨u, hu, m, hm, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hU' u hu, hKM g hg m hm]

theorem E25_core (hH : E25Hyp J a) (hne : J ≠ Subgroup.zpowers a) :
    Nat.card J = 25 ∧ ∃ M₁ M₂ : Submodule (ZMod 2) V, finrank (ZMod 2) M₁ = 4 ∧
      finrank (ZMod 2) M₂ = 4 ∧ IsCompl M₁ M₂ ∧ (∀ g ∈ J, Stable g M₁ ∧ Stable g M₂) ∧
      (∀ U : Submodule (ZMod 2) V, (∀ g ∈ J, Stable g U) → finrank (ZMod 2) U = 4 →
        U = M₁ ∨ U = M₂) ∧
      (∀ g ∈ J, (∃ k : ℕ, ∀ v ∈ M₁, g v = a ^ k • v) ∧ ∃ k : ℕ, ∀ v ∈ M₂, g v = a ^ k • v) ∧
      ∃ K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V), K₁ ≤ J ∧ K₂ ≤ J ∧ K₁ ⊓ K₂ = ⊥ ∧ K₁ ⊔ K₂ = J ∧
        Nat.card K₁ = 5 ∧ Nat.card K₂ = 5 ∧ (∀ v : V, v ∈ M₁ ↔ ∀ g ∈ K₁, g v = v) ∧
        ∀ v : V, v ∈ M₂ ↔ ∀ g ∈ K₂, g v = v := by
  haveI := E25_finite_GL (V := V)
  obtain ⟨M₁, M₂, hd₁, hd₂, hc, hs₁, hs₂⟩ := E25_exists_two hH hne
  obtain ⟨K₁, hK₁J, hK₁m, hK₁c, -, hK₁p⟩ := E25_kernel_data hH hs₁ hd₁
  obtain ⟨K₂, hK₂J, hK₂m, hK₂c, hK₂d, hK₂p⟩ := E25_kernel_data hH hs₂ hd₂
  have hbot : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    obtain ⟨h1, h2⟩ := hg
    apply E25_eq_one_of_fix
    intro v
    have hv : v ∈ M₁ ⊔ M₂ := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, ((hK₁m g).mp h1).2 m₁ hm₁, ((hK₂m g).mp h2).2 m₂ hm₂]
  have hJ5 : Nat.card J ≠ 5 := fun h => hne (E25_eq_zpowers_of_card hH h)
  obtain ⟨c₁, c₂, c₃, c₄⟩ :=
    E25_card_data hK₁J hK₂J hbot hK₁c hK₂c (hK₂d K₁ hK₁J hbot) hJ5
  have hK₁ne : K₁ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at c₁; omega
  have hK₂ne : K₂ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at c₂; omega
  refine ⟨c₃, M₁, M₂, hd₁, hd₂, hc, fun g hg => ⟨hs₁ g hg, hs₂ g hg⟩, ?_,
    fun g hg => ⟨hK₁p g hg, hK₂p g hg⟩, K₁, K₂, hK₁J, hK₂J, hbot, c₄, c₁, c₂,
    E25_fix_eq hH hK₁J hd₁ (fun g hg u hu => ((hK₁m g).mp hg).2 u hu) hK₁ne,
    E25_fix_eq hH hK₂J hd₂ (fun g hg u hu => ((hK₂m g).mp hg).2 u hu) hK₂ne⟩
  intro U hU hdU
  exact E25_unique hH hd₁ hd₂ hc hs₁ hs₂ hK₁J (fun g hg u hu => ((hK₁m g).mp hg).2 u hu)
    hK₁ne hU hdU

end Core

section Permute

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem E25_map_stable {J : Subgroup (V ≃ₗ[ZMod 2] V)} {n : V ≃ₗ[ZMod 2] V}
    (hn : ∀ g ∈ J, n⁻¹ * g * n ∈ J) {U : Submodule (ZMod 2) V} (hU : ∀ g ∈ J, Stable g U) :
    ∀ g ∈ J, Stable g (U.map (n : V →ₗ[ZMod 2] V)) := by
  rintro g hg _ ⟨u, hu, rfl⟩
  refine ⟨(n⁻¹ * g * n) u, hU _ (hn g hg) u hu, ?_⟩
  simp [LinearEquiv.mul_apply]

theorem E25_perm {M₁ M₂ : Submodule (ZMod 2) V} {n : V ≃ₗ[ZMod 2] V} (hc : IsCompl M₁ M₂)
    (h1 : M₁ ≠ ⊥) (a1 : M₁.map (n : V →ₗ[ZMod 2] V) = M₁ ∨ M₁.map (n : V →ₗ[ZMod 2] V) = M₂)
    (a2 : M₂.map (n : V →ₗ[ZMod 2] V) = M₁ ∨ M₂.map (n : V →ₗ[ZMod 2] V) = M₂) :
    (M₁.map (n : V →ₗ[ZMod 2] V) = M₁ ∧ M₂.map (n : V →ₗ[ZMod 2] V) = M₂) ∨
      (M₁.map (n : V →ₗ[ZMod 2] V) = M₂ ∧ M₂.map (n : V →ₗ[ZMod 2] V) = M₁) := by
  have hne : M₁ ≠ M₂ := by
    intro h
    apply h1
    have := hc.inf_eq_bot
    rwa [← h, inf_idem] at this
  have hinj : Function.Injective (Submodule.map (n : V →ₗ[ZMod 2] V)) :=
    Submodule.map_injective_of_injective n.injective
  rcases a1 with e1 | e1 <;> rcases a2 with e2 | e2
  · exact absurd (hinj (e1.trans e2.symm)) hne
  · exact Or.inl ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact absurd (hinj (e1.trans e2.symm)) hne

end Permute

section JbarFacts

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B]

@[expose] def Jbar (ρ : B →* (V ≃ₗ[ZMod 2] V)) (x : B) : Subgroup (V ≃ₗ[ZMod 2] V) :=
  (normalClosure ({x} : Set B)).map ρ

variable {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}

theorem E25_rho_mem_Jbar (ρ : B →* (V ≃ₗ[ZMod 2] V)) (x : B) : ρ x ∈ Jbar ρ x :=
  Subgroup.mem_map_of_mem ρ (Subgroup.subset_normalClosure rfl)

theorem E25_Jbar_conj (ρ : B →* (V ≃ₗ[ZMod 2] V)) (x b : B) {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ Jbar ρ x) : (ρ b)⁻¹ * g * ρ b ∈ Jbar ρ x := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hg
  refine Subgroup.mem_map.mpr ⟨b⁻¹ * n * b, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.normalClosure_normal (s := ({x} : Set B))).conj_mem n hn b⁻¹
  simpa using this

theorem E25_Jbar_pow_five (hx : (ρ x) ^ 5 = 1)
    (hab : ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a) : ∀ g ∈ Jbar ρ x, g ^ 5 = 1 := by
  rintro _ ⟨n, hn, rfl⟩
  have key : ∀ n : B, n ∈ Subgroup.closure (Group.conjugatesOfSet ({x} : Set B)) →
      (ρ n) ^ 5 = 1 := by
    intro n hn
    induction hn using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', hc⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨c, rfl⟩ := isConj_iff.mp hc
      rw [map_mul, map_mul, map_inv, conj_pow, hx, mul_one, mul_inv_cancel]
    | one => simp
    | mul y w hy hw ihy ihw =>
      have hyJ : ρ y ∈ Jbar ρ x := Subgroup.mem_map_of_mem ρ hy
      have hwJ : ρ w ∈ Jbar ρ x := Subgroup.mem_map_of_mem ρ hw
      rw [map_mul, Commute.mul_pow (hab _ hyJ _ hwJ), ihy, ihw, one_mul]
    | inv y hy ih => rw [map_inv, inv_pow, ih, inv_one]
  exact key n hn

theorem E25_tbar_not_central (H : HypM ρ x t z h) : ¬ ∀ g ∈ Jbar ρ x, ρ t * g = g * ρ t := by
  intro hc
  have hg := E25_Jbar_conj ρ x h (E25_rho_mem_Jbar ρ x)
  have h1 := hc _ hg
  have h2 : ρ (t * z) * ρ x = ρ x * ρ (t * z) := by
    have e : ρ (t * z) = ρ h * ρ t * (ρ h)⁻¹ := by rw [← H.ht, map_mul, map_mul, map_inv]
    rw [e]
    calc ρ h * ρ t * (ρ h)⁻¹ * ρ x = ρ h * (ρ t * ((ρ h)⁻¹ * ρ x * ρ h)) * (ρ h)⁻¹ := by group
      _ = ρ h * (((ρ h)⁻¹ * ρ x * ρ h) * ρ t) * (ρ h)⁻¹ := by rw [h1]
      _ = ρ x * (ρ h * ρ t * (ρ h)⁻¹) := by group
  have htx : ρ t * ρ x = ρ x * ρ t := by rw [← map_mul, ← map_mul, H.tx]
  have h3 : ρ z * ρ x = ρ x * ρ z := by
    have ez : ρ z = ρ t * ρ (t * z) := by rw [map_mul, ← mul_assoc, H.t_sq, one_mul]
    rw [ez, mul_assoc, h2, ← mul_assoc, htx, mul_assoc]
  have h4 : ρ z * ρ x * (ρ z)⁻¹ = (ρ x)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, H.zx, map_inv]
  rw [h3, mul_inv_cancel_right] at h4
  have h5 : ρ x ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.mpr h4
  have h6 := orderOf_dvd_of_pow_eq_one h5
  rw [H.ord_x] at h6
  omega

theorem E25_Jbar_ne_zpowers (H : HypM ρ x t z h) : Jbar ρ x ≠ Subgroup.zpowers (ρ x) := by
  intro heq
  apply E25_tbar_not_central H
  intro g hg
  rw [heq] at hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have htx : Commute (ρ t) (ρ x) := by
    show ρ t * ρ x = ρ x * ρ t
    rw [← map_mul, ← map_mul, H.tx]
  exact htx.zpow_right k

theorem E25_Jbar_hyp (H : HypM ρ x t z h)
    (hab : ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a) : E25Hyp (Jbar ρ x) (ρ x) where
  dim := H.dim
  abel := hab
  exp := E25_Jbar_pow_five (by rw [← H.ord_x]; exact pow_orderOf_eq_one _) hab
  mem := E25_rho_mem_Jbar ρ x
  ord := H.ord_x
  fix := H.fix

end JbarFacts

section Modules

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B] [Finite B]

variable {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}

theorem module_E25_abs (H : HypM ρ x t z h)
    (hab : ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a) :
    Nat.card (Jbar ρ x) = 25 ∧
      ∃ V₁ V₂ : Submodule (ZMod 2) V, finrank (ZMod 2) V₁ = 4 ∧ IsCompl V₁ V₂ ∧
        V₂ = V₁.map (ρ t : V →ₗ[ZMod 2] V) ∧ (∀ g ∈ Jbar ρ x, Stable g V₁ ∧ Stable g V₂) ∧
        (∀ b : B, (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₁ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₂) ∨
          (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₂ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₁)) ∧
        (∀ g ∈ Jbar ρ x, (∃ k : ℕ, ∀ v ∈ V₁, g v = (ρ x) ^ k • v) ∧
          ∃ k : ℕ, ∀ v ∈ V₂, g v = (ρ x) ^ k • v) ∧
        ∃ K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V), K₁ ≤ Jbar ρ x ∧ K₂ ≤ Jbar ρ x ∧ K₁ ⊓ K₂ = ⊥ ∧
          K₁ ⊔ K₂ = Jbar ρ x ∧ Nat.card K₁ = 5 ∧ Nat.card K₂ = 5 ∧
          (∀ v : V, v ∈ V₁ ↔ ∀ g ∈ K₁, g v = v) ∧ (∀ v : V, v ∈ V₂ ↔ ∀ g ∈ K₂, g v = v) := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [H.dim]; norm_num)
  have hx5 : (ρ x) ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one _
  obtain ⟨hcard, M₁, M₂, hd₁, hd₂, hc, hst, huniq, hpow, hK⟩ :=
    E25_core (E25_Jbar_hyp H hab) (E25_Jbar_ne_zpowers H)
  have hM₁ : M₁ ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hd₁; omega
  have hperm : ∀ b : B,
      (M₁.map (ρ b : V →ₗ[ZMod 2] V) = M₁ ∧ M₂.map (ρ b : V →ₗ[ZMod 2] V) = M₂) ∨
        (M₁.map (ρ b : V →ₗ[ZMod 2] V) = M₂ ∧ M₂.map (ρ b : V →ₗ[ZMod 2] V) = M₁) := by
    intro b
    have hn : ∀ g ∈ Jbar ρ x, (ρ b)⁻¹ * g * ρ b ∈ Jbar ρ x := fun g hg => E25_Jbar_conj ρ x b hg
    have s1 := E25_map_stable hn (fun g hg => (hst g hg).1)
    have s2 := E25_map_stable hn (fun g hg => (hst g hg).2)
    exact E25_perm hc hM₁
      (huniq _ s1 ((LinearEquiv.finrank_map_eq (ρ b) M₁).trans hd₁))
      (huniq _ s2 ((LinearEquiv.finrank_map_eq (ρ b) M₂).trans hd₂))
  have hswap : M₁.map (ρ t : V →ₗ[ZMod 2] V) = M₂ ∧ M₂.map (ρ t : V →ₗ[ZMod 2] V) = M₁ := by
    rcases hperm t with ⟨e1, e2⟩ | h12
    · exfalso
      have hxt : ρ x * ρ t = ρ t * ρ x := by rw [← map_mul, ← map_mul, H.tx]
      have ht2 : (ρ t) ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact H.t_sq
      have hfix₁ : ∀ u ∈ M₁, ρ t u = u :=
        commuting_two_elt_trivial hx5 hxt hd₁
          (fun u hu => (hst _ (E25_rho_mem_Jbar ρ x)).1 u hu)
          (fun u hu => e1 ▸ Submodule.mem_map_of_mem hu) (fun u _ hu => H.fix u hu) ht2
      have hfix₂ : ∀ u ∈ M₂, ρ t u = u :=
        commuting_two_elt_trivial hx5 hxt hd₂
          (fun u hu => (hst _ (E25_rho_mem_Jbar ρ x)).2 u hu)
          (fun u hu => e2 ▸ Submodule.mem_map_of_mem hu) (fun u _ hu => H.fix u hu) ht2
      have ht1 : ρ t = 1 := by
        apply E25_eq_one_of_fix
        intro v
        have hv : v ∈ M₁ ⊔ M₂ := by rw [hc.sup_eq_top]; trivial
        obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add, hfix₁ m₁ hm₁, hfix₂ m₂ hm₂]
      exact E25_tbar_not_central H fun g _ => by rw [ht1, one_mul, mul_one]
    · exact h12
  obtain ⟨K₁, K₂, hK'⟩ := hK
  exact ⟨hcard, M₁, M₂, hd₁, hc, hswap.1.symm, hst, hperm, hpow, K₁, K₂, hK'⟩

end Modules

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
