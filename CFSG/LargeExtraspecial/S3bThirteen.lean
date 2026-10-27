module

public import CFSG.LargeExtraspecial.S3bWeak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions

section Generic

variable {X : Type*} [Group X] [Finite X]

private theorem exists_mem_normalizer_of_lt_of_isPGroup {p : ℕ} [Fact p.Prime]
    {P S₀ : Subgroup X} (hP : IsPGroup p P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set X) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set X)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

noncomputable def sylowOfMaximal {p : ℕ} {K R : Subgroup X} (hRK : R ≤ K) (hR : IsPGroup p R)
    (hRmax : ∀ R' : Subgroup X, R ≤ R' → R' ≤ K → IsPGroup p R' → R' = R) : Sylow p K where
  toSubgroup := R.subgroupOf K
  isPGroup' := hR.of_equiv (subgroupOfEquivOfLe hRK).symm
  is_maximal' := fun {Q'} hQ' hle => by
    have h1 := hRmax (Q'.map K.subtype)
      (fun x hx => ⟨⟨x, hRK hx⟩, hle (mem_subgroupOf.mpr hx), rfl⟩) (map_subtype_le Q')
      (hQ'.map K.subtype)
    ext y
    constructor
    · intro hy
      rw [mem_subgroupOf, ← h1]
      exact ⟨y, hy, rfl⟩
    · intro hy
      exact hle hy

omit [Finite X] in
theorem conj_mem_of_smul_eq {p : ℕ} {K : Subgroup X} {T T' : Sylow p K} {c : K}
    (hc : c • T' = T) {y : K} (hy : y ∈ (T' : Subgroup K)) : c * y * c⁻¹ ∈ (T : Subgroup K) := by
  have h1 : MulAut.conj c • y ∈ ((c • T' : Sylow p K) : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul]
    exact smul_mem_pointwise_smul _ _ _ hy
  rwa [hc, MulAut.smul_def, MulAut.conj_apply] at h1

theorem exists_mem_map_conj_eq_of_maximal {p : ℕ} [Fact p.Prime] {K P P' : Subgroup X}
    (hPK : P ≤ K) (hP : IsPGroup p P)
    (hPmax : ∀ R : Subgroup X, P ≤ R → R ≤ K → IsPGroup p R → R = P)
    (hP'K : P' ≤ K) (hP' : IsPGroup p P')
    (hP'max : ∀ R : Subgroup X, P' ≤ R → R ≤ K → IsPGroup p R → R = P') :
    ∃ c ∈ K, P'.map (MulAut.conj c).toMonoidHom = P := by
  set T := sylowOfMaximal hPK hP hPmax
  set T' := sylowOfMaximal hP'K hP' hP'max
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K T' T
  have hc' : c⁻¹ • T = T' := by rw [← hc, inv_smul_smul]
  refine ⟨c, c.2, le_antisymm ?_ fun x hx => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h1 := conj_mem_of_smul_eq hc (y := ⟨y, hP'K hy⟩) (mem_subgroupOf.mpr hy)
    exact mem_subgroupOf.mp h1
  · have h1 := conj_mem_of_smul_eq hc' (y := ⟨x, hPK hx⟩) (mem_subgroupOf.mpr hx)
    refine ⟨_, mem_subgroupOf.mp h1, ?_⟩
    simp [mul_assoc]

end Generic

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

theorem eq_of_commute_of_sq {x : G} (hxQ : x ∈ S.QG) (hx1 : x ≠ 1) (hxz : x ≠ S.z)
    {S₀ : Subgroup G} (hFS₀ : S.QG ⊓ centralizer ({x} : Set G) ≤ S₀) {w : G}
    (hw : ∀ s ∈ S₀, w * s = s * w) (hw2 : w ^ 2 = 1) :
    w = 1 ∨ w = S.z ∨ w = x ∨ w = x * S.z := by
  have hF := S.relIndex_centralizer_eq_two hxQ hx1 hxz
  have hwQ : w ∈ S.QG :=
    S.mem_QG_of_sq_eq_one_of_commute inf_le_left hF hw2 fun f hf => hw f (hFS₀ hf)
  exact (S.mem_centralizer_centralizer_iff hxQ).mp
    ⟨hwQ, mem_centralizer_iff.mpr fun f hf => (hw f (hFS₀ hf)).symm⟩

theorem maximal_of_not_conj {x : G} (hxQ : x ∈ S.QG) (hx1 : x ≠ 1) (hxz : x ≠ S.z)
    (hxc : ∀ k : G, k * S.z * k⁻¹ ≠ x) {S₀ : Subgroup G}
    (hFS₀ : S.QG ⊓ centralizer ({x} : Set G) ≤ S₀)
    (hS₀ : S₀ ≤ S.M ⊓ centralizer ({x} : Set G))
    (hmax : ∀ P : Subgroup G, S₀ ≤ P → P ≤ S.M ⊓ centralizer ({x} : Set G) → IsPGroup 2 P →
      P = S₀) :
    ∀ P : Subgroup G, S₀ ≤ P → P ≤ centralizer ({x} : Set G) → IsPGroup 2 P → P = S₀ := by
  intro P hS₀P hPC hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨n, hnP, hnS₀, hnN⟩ :=
    exists_mem_normalizer_of_lt_of_isPGroup hP (lt_of_le_of_ne hS₀P (Ne.symm hne))
  have hnx : n * x = x * n := mem_centralizer_singleton_iff.mp (hPC hnP)
  have hw : ∀ s ∈ S₀, n * S.z * n⁻¹ * s = s * (n * S.z * n⁻¹) := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S₀ := by
      refine (mem_normalizer_iff.mp hnN (n⁻¹ * s * n)).mpr ?_
      rw [show n * (n⁻¹ * s * n) * n⁻¹ = s by group]
      exact hs
    have hzc : S.z * (n⁻¹ * s * n) = n⁻¹ * s * n * S.z := (S.z_comm (hS₀ hs').1).symm
    calc n * S.z * n⁻¹ * s = n * (S.z * (n⁻¹ * s * n)) * n⁻¹ := by group
      _ = n * (n⁻¹ * s * n * S.z) * n⁻¹ := by rw [hzc]
      _ = s * (n * S.z * n⁻¹) := by group
  have hw2 : (n * S.z * n⁻¹) ^ 2 = 1 := by
    rw [conj_pow, S.z_sq]
    group
  rcases S.eq_of_commute_of_sq hxQ hx1 hxz hFS₀ hw hw2 with h | h | h | h
  · apply S.z_ne_one
    calc S.z = n⁻¹ * (n * S.z * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · have hnM : n ∈ S.M := S.mem_M_iff.mpr (by
      calc n * S.z = n * S.z * n⁻¹ * n := by group
        _ = S.z * n := by rw [h])
    have hle : S₀ ⊔ zpowers n ≤ P := sup_le hS₀P (zpowers_le.mpr hnP)
    have heq := hmax (S₀ ⊔ zpowers n) le_sup_left
      (sup_le hS₀ (zpowers_le.mpr ⟨hnM, hPC hnP⟩)) (hP.to_le hle)
    exact hnS₀ (heq ▸ (le_sup_right : zpowers n ≤ S₀ ⊔ zpowers n) (mem_zpowers n))
  · apply hxz
    have hxn : n⁻¹ * x * n = x := by
      calc n⁻¹ * x * n = n⁻¹ * (x * n) := by group
        _ = n⁻¹ * (n * x) := by rw [hnx]
        _ = x := by group
    calc x = n⁻¹ * x * n := hxn.symm
      _ = n⁻¹ * (n * S.z * n⁻¹) * n := by rw [h]
      _ = S.z := by group
  · obtain ⟨q, -, hq⟩ := S.exists_conj_eq_mul_z hxQ hx1 hxz
    refine hxc (q⁻¹ * n) ?_
    calc (q⁻¹ * n) * S.z * (q⁻¹ * n)⁻¹ = q⁻¹ * (n * S.z * n⁻¹) * q := by group
      _ = q⁻¹ * (q * x * q⁻¹) * q := by rw [h, hq]
      _ = x := by group

theorem exists_maximal_twoSubgroup (x : G) :
    ∃ S₀ : Subgroup G, S.QG ⊓ centralizer ({x} : Set G) ≤ S₀ ∧
      S₀ ≤ S.M ⊓ centralizer ({x} : Set G) ∧ IsPGroup 2 S₀ ∧
      ∀ P : Subgroup G, S₀ ≤ P → P ≤ S.M ⊓ centralizer ({x} : Set G) → IsPGroup 2 P → P = S₀ := by
  set F := S.QG ⊓ centralizer ({x} : Set G)
  have hfin : {P : Subgroup G |
      F ≤ P ∧ P ≤ S.M ⊓ centralizer ({x} : Set G) ∧ IsPGroup 2 P}.Finite := Set.toFinite _
  obtain ⟨S₀, hFS₀, hS₀max⟩ := hfin.exists_le_maximal (a := F)
    ⟨le_rfl, le_inf (inf_le_left.trans S.QG_le_M) inf_le_right, S.isPGroup_QG.to_le inf_le_left⟩
  exact ⟨S₀, hFS₀, hS₀max.prop.2.1, hS₀max.prop.2.2, fun P h1 h2 h3 =>
    (hS₀max.eq_of_le ⟨hFS₀.trans h1, h2, h3⟩ h1).symm⟩

theorem janko_control_fusion {x k : G} (hxQ : x ∈ S.QG) (hx1 : x ≠ 1) (hxz : x ≠ S.z)
    (hxc : ∀ g : G, g * S.z * g⁻¹ ≠ x) (hyQ : k * x * k⁻¹ ∈ S.QG) :
    ∃ m ∈ S.M, m * x * m⁻¹ = k * x * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases S.sq_eq_one_or_z hxQ with hx2 | hx2
  swap
  ·
    refine ⟨k, ?_, rfl⟩
    rw [S.mem_M_iff]
    have h1 : (k * x * k⁻¹) ^ 2 = k * S.z * k⁻¹ := by rw [conj_pow, hx2]
    rcases S.sq_eq_one_or_z hyQ with h | h
    · exfalso
      rw [h] at h1
      apply S.z_ne_one
      calc S.z = k⁻¹ * (k * S.z * k⁻¹) * k := by group
        _ = 1 := by rw [← h1]; group
    · rw [h] at h1
      calc k * S.z = k * S.z * k⁻¹ * k := by group
        _ = S.z * k := by rw [← h1]
  set y := k * x * k⁻¹ with hy
  have hy1 : y ≠ 1 := fun h => hx1 (by
    calc x = k⁻¹ * y * k := by rw [hy]; group
      _ = 1 := by rw [h]; group)
  have hyc : ∀ g : G, g * S.z * g⁻¹ ≠ y := fun g h => hxc (k⁻¹ * g) (by
    calc (k⁻¹ * g) * S.z * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * S.z * g⁻¹) * k := by group
      _ = x := by rw [h, hy]; group)
  have hyz : y ≠ S.z := fun h => hyc 1 (by rw [h]; group)
  obtain ⟨S₀, hFS₀, hS₀, hS₀2, hS₀max⟩ := S.exists_maximal_twoSubgroup x
  obtain ⟨S₁, hFS₁, hS₁, hS₁2, hS₁max⟩ := S.exists_maximal_twoSubgroup y
  have hmax₀ := S.maximal_of_not_conj hxQ hx1 hxz hxc hFS₀ hS₀ hS₀max
  have hmax₁ := S.maximal_of_not_conj hyQ hy1 hyz hyc hFS₁ hS₁ hS₁max
  set P' := S₁.map (MulAut.conj k⁻¹).toMonoidHom with hP'
  have hcy : ∀ s : G, s * y = y * s → k⁻¹ * s * k⁻¹⁻¹ * x = x * (k⁻¹ * s * k⁻¹⁻¹) := by
    intro s hs
    calc k⁻¹ * s * k⁻¹⁻¹ * x = k⁻¹ * (s * y) * k := by rw [hy]; group
      _ = k⁻¹ * (y * s) * k := by rw [hs]
      _ = x * (k⁻¹ * s * k⁻¹⁻¹) := by rw [hy]; group
  have hP'C : P' ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact hcy s (mem_centralizer_singleton_iff.mp (hS₁ hs).2)
  have hP'2 : IsPGroup 2 P' := hS₁2.map _
  have hP'max : ∀ R : Subgroup G, P' ≤ R → R ≤ centralizer ({x} : Set G) → IsPGroup 2 R →
      R = P' := by
    intro R hP'R hRC hR
    have h1 : R.map (MulAut.conj k).toMonoidHom = S₁ := by
      refine hmax₁ _ ?_ ?_ (hR.map _)
      · intro s hs
        refine ⟨k⁻¹ * s * k⁻¹⁻¹, hP'R ⟨s, hs, rfl⟩, ?_⟩
        simp [mul_assoc]
      · rintro _ ⟨r, hr, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have h2 := mem_centralizer_singleton_iff.mp (hRC hr)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc k * r * k⁻¹ * y = k * (r * x) * k⁻¹ := by rw [hy]; group
          _ = k * (x * r) * k⁻¹ := by rw [h2]
          _ = y * (k * r * k⁻¹) := by rw [hy]; group
    rw [hP', ← h1, Subgroup.map_map]
    ext r
    simp [mul_assoc]
  obtain ⟨c, hcC, hcP⟩ := exists_mem_map_conj_eq_of_maximal (K := centralizer ({x} : Set G))
    (hS₀.trans inf_le_right) hS₀2 hmax₀ hP'C hP'2 hP'max
  have hcx : c * x * c⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hcC]
    group
  set k' := c * k⁻¹ with hk'
  have hk'y : k' * y * k'⁻¹ = x := by
    rw [hk', hy, show c * k⁻¹ * (k * x * k⁻¹) * (c * k⁻¹)⁻¹ = c * x * c⁻¹ by group, hcx]
  have hzS₁ : S.z ∈ S₁ :=
    hFS₁ ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm_QG hyQ).symm⟩
  have hwS₀ : ∀ s ∈ S₀, k' * S.z * k'⁻¹ * s = s * (k' * S.z * k'⁻¹) := by
    intro s hs
    rw [← hcP] at hs
    obtain ⟨_, ⟨s₁, hs₁, rfl⟩, rfl⟩ := hs
    have hzc : S.z * s₁ = s₁ * S.z := (S.z_comm (hS₁ hs₁).1).symm
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k' * S.z * k'⁻¹ * (c * (k⁻¹ * s₁ * k⁻¹⁻¹) * c⁻¹) = k' * (S.z * s₁) * k'⁻¹ := by
          rw [hk']; group
      _ = k' * (s₁ * S.z) * k'⁻¹ := by rw [hzc]
      _ = c * (k⁻¹ * s₁ * k⁻¹⁻¹) * c⁻¹ * (k' * S.z * k'⁻¹) := by rw [hk']; group
  have hw2 : (k' * S.z * k'⁻¹) ^ 2 = 1 := by
    rw [conj_pow, S.z_sq]
    group
  have hk'M : k' ∈ S.M := by
    rcases S.eq_of_commute_of_sq hxQ hx1 hxz hFS₀ hwS₀ hw2 with h | h | h | h
    · exfalso
      apply S.z_ne_one
      calc S.z = k'⁻¹ * (k' * S.z * k'⁻¹) * k' := by group
        _ = 1 := by rw [h]; group
    · rw [S.mem_M_iff]
      calc k' * S.z = k' * S.z * k'⁻¹ * k' := by group
        _ = S.z * k' := by rw [h]
    · exact absurd h (hxc k')
    · exfalso
      obtain ⟨q, -, hq⟩ := S.exists_conj_eq_mul_z hxQ hx1 hxz
      refine hxc (q⁻¹ * k') ?_
      calc (q⁻¹ * k') * S.z * (q⁻¹ * k')⁻¹ = q⁻¹ * (k' * S.z * k'⁻¹) * q := by group
        _ = q⁻¹ * (q * x * q⁻¹) * q := by rw [h, hq]
        _ = x := by group
  refine ⟨k'⁻¹, S.M.inv_mem hk'M, ?_⟩
  rw [← hk'y]
  group

theorem sq_eq_one_of_mem_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {s : S.O}
    (hs : s ∈ S.Lbar g) : s ^ 2 = 1 := by
  have h := (S.isElementaryAbelian_Lbar haQ).exponent_dvd_p
  have h1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h ⟨s, hs⟩
  exact congrArg Subtype.val h1

theorem isPGroup_Lbar_subgroupOf {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    IsPGroup 2 ((S.Lbar g).subgroupOf S.Mbar) := by
  intro y
  refine ⟨1, ?_⟩
  have h := S.sq_eq_one_of_mem_Lbar haQ (mem_subgroupOf.mp y.2)
  apply Subtype.ext
  apply Subtype.ext
  simpa using h

theorem lemma_3_13 (h2 : 2 ≤ S.width)
    (hno : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ≠ S.z → ¬ S.HasTypeAInL g)
    {x k : G} (hxQ : x ∈ S.QG) (hx1 : x ≠ 1) (hxz : x ≠ S.z) (hyQ : k * x * k⁻¹ ∈ S.QG)
    (hyz : k * x * k⁻¹ ≠ S.z) : ∃ m ∈ S.M, m * x * m⁻¹ = k * x * k⁻¹ := by
  by_cases hc : ∃ g : G, g * S.z * g⁻¹ = x
  swap
  · push Not at hc
    exact S.janko_control_fusion hxQ hx1 hxz hc hyQ
  obtain ⟨g, rfl⟩ := hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ekg : (k * g) * S.z * (k * g)⁻¹ = k * (g * S.z * g⁻¹) * k⁻¹ := by group
  have hbQ : (k * g) * S.z * (k * g)⁻¹ ∈ S.QG := by rw [ekg]; exact hyQ
  have hbz : (k * g) * S.z * (k * g)⁻¹ ≠ S.z := by rw [ekg]; exact hyz
  obtain ⟨P, hAP⟩ := (S.isPGroup_Lbar_subgroupOf hxQ).exists_le_sylow
  obtain ⟨P', hBP'⟩ := (S.isPGroup_Lbar_subgroupOf hbQ).exists_le_sylow
  obtain ⟨mb, hmb⟩ := MulAction.exists_smul_eq S.Mbar P' P
  obtain ⟨⟨m, hm⟩, hmm⟩ := MonoidHom.mem_range.mp mb.2
  have hB'P : (S.Lbar (m * (k * g))).subgroupOf S.Mbar ≤ P := by
    rw [← S.map_conj_Lbar_subgroupOf hm mb hmm]
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact conj_mem_of_smul_eq hmb (hBP' hy)
  have hPN := S.le_normalizer_Lbar_of_isPGroup h2 hxQ hxz (hno g hxQ hxz) P.isPGroup' hAP
  have hle : S.Lbar (m * (k * g)) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro s hs
    have hsM : s ∈ S.Mbar := S.Lbar_le_Mbar _ hs
    have h1 := hPN (hB'P
      (show (⟨s, hsM⟩ : S.Mbar) ∈ (S.Lbar (m * (k * g))).subgroupOf S.Mbar from hs))
    rw [← subgroupOf_normalizer_eq (S.Lbar_le_Mbar g)] at h1
    exact h1
  have hb'Q := S.conj_mul_mem_QG hm hbQ
  have hb'z := S.conj_mul_ne_z hm hbz
  rw [← mul_assoc] at hb'Q hb'z
  have hmem : S.cl (g * S.z * g⁻¹) ∈ S.fixLbar (m * (k * g)) :=
    S.mem_fixLbar.mpr fun s hs =>
      S.fixes_of_mem_normalizer_Lbar h2 hxQ hxz (hno g hxQ hxz) (hle hs)
  rw [← mul_assoc] at hmem
  rcases (S.lemma_3_9 h2 hb'Q hb'z).resolve_right (hno _ hb'Q hb'z) _ hmem
    (S.q_cl_conj_z hxQ) with h | h
  · exact absurd h (S.cl_conj_z_ne_zero hxQ hxz)
  · rcases (S.cl_eq_cl_iff hxQ hb'Q).mp h with h' | h'
    · refine ⟨m⁻¹, S.M.inv_mem hm, ?_⟩
      calc m⁻¹ * (g * S.z * g⁻¹) * m⁻¹⁻¹ =
            m⁻¹ * ((m * k * g) * S.z * (m * k * g)⁻¹) * m := by rw [h']; group
        _ = k * (g * S.z * g⁻¹) * k⁻¹ := by group
    · obtain ⟨q, hq, hqa⟩ := S.exists_conj_eq_mul_z hxQ hx1 hxz
      refine ⟨m⁻¹ * q, S.M.mul_mem (S.M.inv_mem hm) (S.QG_le_M hq), ?_⟩
      calc (m⁻¹ * q) * (g * S.z * g⁻¹) * (m⁻¹ * q)⁻¹ =
            m⁻¹ * (q * (g * S.z * g⁻¹) * q⁻¹) * m := by group
        _ = m⁻¹ * ((m * k * g) * S.z * (m * k * g)⁻¹) * m := by rw [hqa, h']
        _ = k * (g * S.z * g⁻¹) * k⁻¹ := by group

end Setting

end CFSG.LargeExtraspecial
