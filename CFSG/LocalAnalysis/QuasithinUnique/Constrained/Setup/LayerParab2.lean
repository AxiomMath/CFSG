module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerPlaneAux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6 CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup
open scoped commutatorElement

universe v

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem isSylowTwoOf_subgroupOf_top' {X : Type*} [Group X] {T H : Subgroup X}
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) := by
  refine ⟨le_top, ?_, ?_⟩
  · have e : ↥(T.subgroupOf H) ≃* ↥T := Subgroup.subgroupOfEquivOfLe hT.1
    exact hT.2.1.of_injective e.toMonoidHom e.injective
  · have h := hT.2.2
    have e : ((T.subgroupOf H).subgroupOf (⊤ : Subgroup ↥H)).index = (T.subgroupOf H).index :=
      Subgroup.index_comap_of_surjective (T.subgroupOf H) (f := (⊤ : Subgroup ↥H).subtype)
        (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩)
    rw [e]
    exact h

theorem abstract_setting {H T M : Subgroup (V ≃ₗ[k] V)}
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M) :
    IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) ∧ T.subgroupOf H ≤ M.subgroupOf H ∧
      M.subgroupOf H < ⊤ ∧
      (∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H) ∧
      CFSG.pCore 2 ↥H = ⊥ := by
  have hT' := isSylowTwoOf_subgroupOf_top' hT
  have hTX : T.subgroupOf H ≤ M.subgroupOf H := fun x hx => hTM hx
  have hXH : M.subgroupOf H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    apply hMH.not_ge
    intro x hx
    have : (⟨x, hx⟩ : ↥H) ∈ M.subgroupOf H := by rw [htop]; trivial
    exact this
  have hmax' : ∀ Y : Subgroup ↥H, T.subgroupOf H ≤ Y → Y < ⊤ → Y ≤ M.subgroupOf H := by
    intro Y hTY hY
    have h1 : T ≤ Y.map H.subtype := fun t ht => ⟨⟨t, hT.1 ht⟩, hTY ht, rfl⟩
    have h2 : Y.map H.subtype < H := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le Y) fun heq => hY.ne ?_
      have := Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y
      rw [heq] at this
      rw [← this]
      exact Subgroup.subgroupOf_self H
    intro y hy
    exact hmax _ h1 h2 ⟨y, hy, rfl⟩
  have hpc : CFSG.pCore 2 ↥H = ⊥ := by
    refine le_bot_iff.1 (sSup_le fun K hK => ?_)
    obtain ⟨hKn, hK2⟩ := hK
    have hKN : (K.map H.subtype).subgroupOf H = K :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective K
    have hmapn : ((K.map H.subtype).subgroupOf H).Normal := by
      rw [hKN]
      exact hKn
    have hN2 : IsPGroup 2 ↥(K.map H.subtype) := by
      have e : ↥K ≃* ↥(K.map H.subtype) := K.equivMapOfInjective H.subtype H.subtype_injective
      exact hK2.of_surjective e.toMonoidHom e.surjective
    have hbot := hO2 _ (Subgroup.map_subtype_le K) hmapn hN2
    exact le_bot_iff.2 ((Subgroup.map_eq_bot_iff_of_injective K H.subtype_injective).1 hbot)
  exact ⟨hT', hTX, hXH, hmax', hpc⟩

theorem normal_le_max_odd [Finite V] {H T M : Subgroup (V ≃ₗ[k] V)}
    (hO2 : ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup 2 N → N = ⊥)
    (hT : IsSylowTwoOf T H) (hTn : ¬ (T.subgroupOf H).Normal) (hTM : T ≤ M) (hMH : M < H)
    (hmax : ∀ Y : Subgroup (V ≃ₗ[k] V), T ≤ Y → Y < H → Y ≤ M) :
    ∀ N : Subgroup (V ≃ₗ[k] V), N ≤ H → (N.subgroupOf H).Normal → N ≤ M → Odd (Nat.card N) := by
  have : Finite (V ≃ₗ[k] V) := finite_linearEquiv
  obtain ⟨hT', hTX, hXH, hmax', hpc'⟩ := abstract_setting hO2 hT hTM hMH hmax
  have hpc : CFSG.Open.pCore 2 ↥H = ⊥ := by exact hpc'
  obtain ⟨-, ⟨-, hodd', -⟩, -⟩ :=
    qt_A7_unique_Sylow_overgroup_core_and_simple_section hT' hTn hTX hXH hmax'
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hpc]
  have e : ↥(kerIn (M.subgroupOf H) ⊤) ≃*
      ↥((kerIn (M.subgroupOf H) ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))) :=
    Subgroup.equivMapOfInjective _ _ hinj
  have hodd : Odd (Nat.card ↥(kerIn (M.subgroupOf H) ⊤)) := by
    rw [Nat.card_congr e.toEquiv]
    exact hodd'
  intro N hNH hNn hNM
  have hle : N.subgroupOf H ≤ kerIn (M.subgroupOf H) ⊤ := by
    intro x hx b _
    exact hNM (hNn.conj_mem x hx b)
  have h1 : Nat.card ↥(N.subgroupOf H) ∣ Nat.card ↥(kerIn (M.subgroupOf H) ⊤) :=
    Subgroup.card_dvd_of_le hle
  have h2 : Nat.card ↥(N.subgroupOf H) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  rw [← h2]
  exact Odd.of_dvd_nat hodd h1

theorem odd_mem_of_sup_eq {H J T : Subgroup (V ≃ₗ[k] V)} (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hTH : T ≤ H) (hT2 : IsPGroup 2 T) (hsup : J ⊔ T = H) :
    ∀ g ∈ H, Odd (orderOf g) → g ∈ J := by
  intro g hg hodd
  have hTn : T ≤ Subgroup.normalizer (J : Set (V ≃ₗ[k] V)) :=
    hTH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJH).1 hJn)
  have hg' : g ∈ J ⊔ T := by rw [hsup]; exact hg
  obtain ⟨j, hj, t, ht, rfl⟩ := mem_sup_mul hTn hg'
  let q : ↥H →* ↥H ⧸ J.subgroupOf H := QuotientGroup.mk' (J.subgroupOf H)
  let gg : ↥H := ⟨j * t, hg⟩
  have hjH : j ∈ H := hJH hj
  have htH : t ∈ H := hTH ht
  have hq : q gg = q ⟨t, htH⟩ := by
    have : gg = ⟨j, hjH⟩ * ⟨t, htH⟩ := rfl
    rw [this, map_mul]
    have h1 : q ⟨j, hjH⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hj
    rw [h1, one_mul]
  obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
  have hn' : (⟨t, htH⟩ : ↥H) ^ 2 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  have h1 : (q gg) ^ 2 ^ n = 1 := by rw [hq, ← map_pow, hn', map_one]
  have h2 : (q gg) ^ orderOf (j * t) = 1 := by
    rw [← map_pow]
    have : gg ^ orderOf (j * t) = 1 := by
      apply Subtype.ext
      simp [gg]
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ n) (orderOf (j * t)) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf (q gg) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (q gg) ∣ orderOf (j * t) := orderOf_dvd_of_pow_eq_one h2
  have h5 : orderOf (q gg) = 1 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
  have h6 : q gg = 1 := orderOf_eq_one_iff.1 h5
  have h7 : gg ∈ J.subgroupOf H := (QuotientGroup.eq_one_iff _).1 h6
  exact h7

end CFSG.QuasithinUnique.Setup.Layer
