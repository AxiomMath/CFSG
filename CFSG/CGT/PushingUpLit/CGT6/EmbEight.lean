module

public import CFSG.CGT.PushingUpLit.CGT6.EmbMin

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp
open scoped commutatorElement Pointwise

section Helpers

theorem centralizer_zpowers_eq {Γ : Type*} [Group Γ] (u : Γ) :
    Subgroup.centralizer ((Subgroup.zpowers u : Subgroup Γ) : Set Γ) =
      Subgroup.centralizer ({u} : Set Γ) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h u (Subgroup.mem_zpowers u)
  · intro h x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left (show Commute u g from h) k).eq

theorem isPGroup_zpowers_of_sq {Γ : Type*} [Group Γ] {u : Γ} (hu2 : u ^ 2 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers u) := by
  by_cases hu : u = 1
  · subst hu
    exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, orderOf_one]; norm_num)
  · have hord : orderOf u = 2 := by
      have hd : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu
      · exact h
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)

theorem zpowers_ne_bot {Γ : Type*} [Group Γ] {u : Γ} (hu : u ≠ 1) :
    Subgroup.zpowers u ≠ ⊥ := fun h =>
  hu (Subgroup.zpowers_eq_bot.mp h)

theorem exists_central_involution {Γ : Type*} [Group Γ] [Finite Γ] {T : Subgroup Γ} (hT1 : T ≠ ⊥)
    (hT2 : IsPGroup 2 ↥T) :
    ∃ z ∈ T, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ s ∈ T, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
  have hc : Nontrivial ↥(Subgroup.center ↥T) := hT2.center_nontrivial
  have hp : IsPGroup 2 ↥(Subgroup.center ↥T) := hT2.to_subgroup _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥T) := by
    rcases k with _ | k
    · have : Nat.card ↥(Subgroup.center ↥T) = 1 := by simpa using hk
      exact absurd (Nat.card_eq_one_iff_unique.mp this).1 (not_subsingleton _)
    · rw [hk, pow_succ]
      exact Dvd.intro_left _ rfl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥T)) 2 hdvd
  refine ⟨((x : ↥T) : Γ), (x : ↥T).2, ?_, ?_, ?_⟩
  · intro h1
    have : (x : ↥T) = 1 := Subtype.ext h1
    have : x = 1 := Subtype.ext this
    rw [this, orderOf_one] at hx
    omega
  · have : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    have h2 : ((x : ↥T) : Γ) ^ 2 = ((x ^ 2 : ↥(Subgroup.center ↥T)) : ↥T) := rfl
    rw [h2, this]
    rfl
  · intro s hs
    have := Subgroup.mem_center_iff.mp x.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

theorem isSubnormal_map_conj {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (c : Γ)
    (h : (A.subgroupOf B).IsSubnormal) :
    ((A.map (MulAut.conj c).toMonoidHom).subgroupOf
      (B.map (MulAut.conj c).toMonoidHom)).IsSubnormal := by
  let φ : Γ →* Γ := (MulAut.conj c).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj c).injective
  let e : ↥B ≃* ↥(B.map φ) := B.equivMapOfInjective φ hφ
  have h1 := h.comap e.symm.toMonoidHom
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
  have hx : φ ((e.symm x : ↥B) : Γ) = (x : Γ) := by
    have h2 : ((e (e.symm x) : ↥(B.map φ)) : Γ) = φ ((e.symm x : ↥B) : Γ) := rfl
    exact h2.symm.trans (congrArg Subtype.val (e.apply_symm_apply x))
  constructor
  · rintro ⟨a, ha, hax⟩
    have : a = ((e.symm x : ↥B) : Γ) := hφ (hax.trans hx.symm)
    exact this ▸ ha
  · intro hmem
    exact ⟨_, hmem, hx⟩

theorem exists_conj_le_of_maximal {Γ : Type*} [Group Γ] [Finite Γ] {K T P : Subgroup Γ}
    (hTK : T ≤ K) (hT2 : IsPGroup 2 ↥T)
    (hmax : ∀ T' : Subgroup Γ, T ≤ T' → T' ≤ K → IsPGroup 2 ↥T' → T' = T)
    (hPK : P ≤ K) (hP2 : IsPGroup 2 ↥P) :
    ∃ c ∈ K, P.map (MulAut.conj c).toMonoidHom ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀ : IsPGroup 2 ↥(T.subgroupOf K) :=
    IsPGroup.of_surjective hT2 (Subgroup.subgroupOfEquivOfLe hTK).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTK).symm.surjective
  have hP₀ : IsPGroup 2 ↥(P.subgroupOf K) :=
    IsPGroup.of_surjective hP2 (Subgroup.subgroupOfEquivOfLe hPK).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPK).symm.surjective
  obtain ⟨Q₀, hTQ₀⟩ := hT₀.exists_le_sylow
  obtain ⟨Q₁, hPQ₁⟩ := hP₀.exists_le_sylow
  have hQ₀ : (Q₀ : Subgroup ↥K) ≤ T.subgroupOf K := by
    have hQ₀2 : IsPGroup 2 ↥(Q₀ : Subgroup ↥K) := Q₀.isPGroup'
    have h1 : IsPGroup 2 ↥((Q₀ : Subgroup ↥K).map K.subtype) := hQ₀2.map K.subtype
    have h2 : T ≤ (Q₀ : Subgroup ↥K).map K.subtype := fun t ht =>
      ⟨⟨t, hTK ht⟩, hTQ₀ (show (⟨t, hTK ht⟩ : ↥K) ∈ T.subgroupOf K from ht), rfl⟩
    have h3 : (Q₀ : Subgroup ↥K).map K.subtype ≤ K := fun x ⟨y, _, hy⟩ => hy ▸ y.2
    have h4 := hmax _ h2 h3 h1
    intro x hx
    have : (x : Γ) ∈ (Q₀ : Subgroup ↥K).map K.subtype := ⟨x, hx, rfl⟩
    rw [h4] at this
    exact this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥K Q₁ Q₀
  refine ⟨(g : Γ), g.2, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hp₀ : (⟨p, hPK hp⟩ : ↥K) ∈ Q₁ := hPQ₁ (show (⟨p, hPK hp⟩ : ↥K) ∈ P.subgroupOf K from hp)
  have h5 := Subgroup.smul_mem_pointwise_smul (⟨p, hPK hp⟩ : ↥K) (MulAut.conj g) (Q₁ : Subgroup ↥K)
    hp₀
  have h6 : (g • Q₁ : Sylow 2 ↥K) = Q₀ := hg
  have h7 : (MulAut.conj g • (Q₁ : Subgroup ↥K)) = (Q₀ : Subgroup ↥K) := by
    rw [← h6]
    rfl
  rw [h7] at h5
  have h8 := hQ₀ h5
  exact h8

end Helpers

section Cent

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem inf_centralizer_ne_of_pCore_bot {G : Subgroup (MulAut V)} (ho2 : pCore 2 ↥G = ⊥)
    {u : MulAut V} (huG : u ∈ G) (hu1 : u ≠ 1) (hu2 : u ^ 2 = 1) :
    G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ≠ G := by
  intro heq
  obtain ⟨c, hcu⟩ : ∃ c : ↥G, (c : MulAut V) = u := ⟨⟨u, huG⟩, rfl⟩
  have hcomm : ∀ g : ↥G, Commute g c := fun g => by
    have hg : (g : MulAut V) ∈ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) := by
      rw [heq]
      exact g.2
    exact Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hcu]
      exact ((Subgroup.mem_centralizer_iff.mp hg.2) u (Set.mem_singleton u)).symm)
  have hn : (Subgroup.zpowers c).Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have : g * c ^ k = c ^ k * g := ((hcomm g).zpow_right k).eq
    rw [this, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c k
  have hc2 : c ^ 2 = 1 := Subtype.ext (by simpa [hcu] using hu2)
  have hle : Subgroup.zpowers c ≤ pCore 2 ↥G := le_sSup ⟨hn, isPGroup_zpowers_of_sq hc2⟩
  rw [ho2] at hle
  have hc1 : c = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers c))
  exact hu1 (hcu ▸ congrArg Subtype.val hc1)


theorem Emb4Pre.core (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (h : Emb4Pre G T Y) (ho2 : pCore 2 ↥G = ⊥) {u : MulAut V} (huG : u ∈ G) (hu1 : u ≠ 1)
    (hu2 : u ^ 2 = 1) {S : Subgroup (MulAut V)} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hSH : S ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)))
    (hYH : Y ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)))
    (hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)))).IsSubnormal) :
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)))).IsSubnormal := by
  set H := G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) with hH
  have hHG : H ≤ G := inf_le_left
  have hHne : H ≠ G := inf_centralizer_ne_of_pCore_bot ho2 huG hu1 hu2
  have hsm : Smaller H G :=
    Or.inl (lt_of_not_ge fun hge => hHne (Subgroup.eq_of_le_of_card_ge hHG hge))
  have hadm : Adm4 H S Y := ⟨hSH, hS1, hS2, hYH, hsub, h.adm.hperf, h.adm.hcls⟩
  obtain ⟨X₁, hX₁⟩ := h.ih V hV H hsm (isKGroup_of_le h.kgroup hHG) S Y hadm
  by_cases hYX : Y = X₁
  · rw [hYX]
    exact hX₁.2.2.1
  exfalso
  have hcent := centralizer_zpowers_eq u
  have hadmG : Adm4 G (Subgroup.zpowers u) X₁ :=
    { hTG := Subgroup.zpowers_le.mpr huG
      hT1 := zpowers_ne_bot hu1
      hT2 := isPGroup_zpowers_of_sq hu2
      hYC := by rw [hcent]; exact hX₁.2.1
      hsub := by rw [hcent]; exact hX₁.2.2.1
      hperf := hX₁.commutator_eq_self hV h.adm.hperf h.adm.hcls
      hcls := hX₁.classX4 }
  have hlt : Nat.card ↥Y < Nat.card ↥X₁ :=
    lt_of_not_ge fun hge => hYX (Subgroup.eq_of_le_of_card_ge hX₁.1 hge)
  have hlift : ∃ X', Lift4 G X₁ X' := by
    by_contra hno
    exact absurd (h.maxY _ _ hadmG hno) (not_le.mpr hlt)
  obtain ⟨X', hX'⟩ := hlift
  exact h.nolift ⟨X', Lift4.trans hV h.adm.hperf h.adm.hcls hX₁ hHG hX'⟩

structure CentHyp (G T Y : Subgroup (MulAut V)) : Prop where
  hTG : T ≤ G
  hT1 : T ≠ ⊥
  hT2 : IsPGroup 2 ↥T
  hYC : Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V))
  hsub : (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal
  sylow : ∀ T' : Subgroup (MulAut V), T ≤ T' →
    T' ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) → IsPGroup 2 ↥T' → T' = T
  core : ∀ {u : MulAut V}, u ∈ G → u ≠ 1 → u ^ 2 = 1 → ∀ {S : Subgroup (MulAut V)}, S ≠ ⊥ →
    IsPGroup 2 ↥S → S ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) →
    Y ≤ G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)) →
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)) ⊓
      Subgroup.centralizer (S : Set (MulAut V)))).IsSubnormal →
    (Y.subgroupOf (G ⊓ Subgroup.centralizer ({u} : Set (MulAut V)))).IsSubnormal

theorem CentHyp.cent {G T Y : Subgroup (MulAut V)} (h : CentHyp G T Y) :
    ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
      (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal := by
  obtain ⟨z, hzT, hz1, hz2, hzc⟩ := exists_central_involution h.hT1 h.hT2
  have hzG : z ∈ G := h.hTG hzT
  have hYT : ∀ y ∈ Y, ∀ s ∈ T, s * y = y * s := fun y hy s hs =>
    (Subgroup.mem_centralizer_iff.mp (h.hYC hy).2 s hs)
  have hYG : Y ≤ G := fun y hy => (h.hYC hy).1
  have hz : (Y.subgroupOf (G ⊓ Subgroup.centralizer ({z} : Set (MulAut V)))).IsSubnormal := by
    refine h.core hzG hz1 hz2 h.hT1 h.hT2 ?_ ?_ ?_
    · intro s hs
      exact ⟨h.hTG hs, Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact (hzc s hs).symm⟩
    · intro y hy
      exact ⟨⟨hYG hy, Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hYT y hy x hzT⟩, (h.hYC hy).2⟩
    · refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le ?_ h.hsub
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
  have hs : ∀ s ∈ T, s ≠ 1 → s ^ 2 = 1 →
      (Y.subgroupOf (G ⊓ Subgroup.centralizer ({s} : Set (MulAut V)))).IsSubnormal := by
    intro s hsT hs1 hs2
    have hsG : s ∈ G := h.hTG hsT
    refine h.core hsG hs1 hs2 (zpowers_ne_bot hz1) (isPGroup_zpowers_of_sq hz2) ?_ ?_ ?_
    · intro x hx
      refine ⟨Subgroup.zpowers_le.mpr hzG hx, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_left (show Commute z a from (hzc a hsT).symm) k)).eq.symm
    · intro y hy
      refine ⟨⟨hYG hy, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩,
        Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hYT y hy x hsT
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact ((Commute.zpow_left (show Commute z y from hYT y hy z hzT) k)).eq
    · refine CFSG.GroupTheory.isSubnormal_subgroupOf_of_le ?_ hz
      intro x hx
      refine ⟨hx.1.1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (Subgroup.mem_centralizer_iff.mp hx.2 a (Subgroup.mem_zpowers a))
  intro t ht ht1 ht2
  have hTK : T ≤ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)) := fun x hx =>
    ⟨h.hTG hx, Subgroup.mem_centralizer_iff.mpr fun y hy => (hYT y hy x hx).symm⟩
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_maximal hTK h.hT2 h.sylow
    (P := Subgroup.zpowers t) (Subgroup.zpowers_le.mpr ht) (isPGroup_zpowers_of_sq ht2)
  have hsT : c * t * c⁻¹ ∈ T := hc ⟨t, Subgroup.mem_zpowers t, by simp [MulAut.conj_apply]⟩
  have hs1 : c * t * c⁻¹ ≠ 1 := fun h1 => ht1 (by simpa using h1)
  have hs2 : (c * t * c⁻¹) ^ 2 = 1 := by
    have : (c * t * c⁻¹) ^ 2 = c * t ^ 2 * c⁻¹ := by
      rw [pow_two, pow_two]
      group
    rw [this, ht2]
    group
  have key := isSubnormal_map_conj c⁻¹ (hs _ hsT hs1 hs2)
  have e1 : Y.map (MulAut.conj c⁻¹).toMonoidHom = Y := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hcx : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hcK.2 x hx).symm
      have : c⁻¹ * x * c⁻¹⁻¹ = x := by rw [inv_inv, mul_assoc, ← hcx]; group
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [this]
      exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      have hcy : c * y = y * c := (Subgroup.mem_centralizer_iff.mp hcK.2 y hy).symm
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [inv_inv, mul_assoc, ← hcy]
      group
  have e2 : (G ⊓ Subgroup.centralizer ({c * t * c⁻¹} : Set (MulAut V))).map
      (MulAut.conj c⁻¹).toMonoidHom = G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyG, hy⟩, rfl⟩
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      · simpa [MulAut.conj_apply] using
          G.mul_mem (G.mul_mem (G.inv_mem hcK.1) hyG)
            (show (c⁻¹)⁻¹ ∈ G by rw [inv_inv]; exact hcK.1)
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        have hy' := Subgroup.mem_centralizer_iff.mp hy (c * a * c⁻¹) (Set.mem_singleton _)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        calc a * (c⁻¹ * y * c) = c⁻¹ * ((c * a * c⁻¹) * y) * c := by group
          _ = c⁻¹ * (y * (c * a * c⁻¹)) * c := by rw [hy']
          _ = (c⁻¹ * y * c) * a := by group
    · rintro ⟨hxG, hx⟩
      refine ⟨c * x * c⁻¹, ⟨?_, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, ?_⟩
      · exact G.mul_mem (G.mul_mem hcK.1 hxG) (G.inv_mem hcK.1)
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        have hx' := Subgroup.mem_centralizer_iff.mp hx t (Set.mem_singleton _)
        calc c * t * c⁻¹ * (c * x * c⁻¹) = c * (t * x) * c⁻¹ := by group
          _ = c * (x * t) * c⁻¹ := by rw [hx']
          _ = c * x * c⁻¹ * (c * t * c⁻¹) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
  rw [e1, e2] at key
  exact key


theorem Emb4Pre.cent (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
    (h : Emb4Pre G T Y) (ho2 : pCore 2 ↥G = ⊥) :
    ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
      (Y.subgroupOf (G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)))).IsSubnormal :=
  CentHyp.cent ⟨h.adm.hTG, h.adm.hT1, h.adm.hT2, h.adm.hYC, h.adm.hsub, h.sylow,
    fun {_} huG hu1 hu2 {_} hS1 hS2 hSH hYH hsub =>
      h.core hV ho2 huG hu1 hu2 hS1 hS2 hSH hYH hsub⟩

end Cent

end CFSG.CGT.PushingUpLit.CGT6
