module

public import CFSG.LocalAnalysis.QuasithinUnique.FusionDatum
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PCore.CharacteristicPPrimeCore
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem eq_of_fixed_coset {M : Subgroup G} {z : G} (hzM : z ∈ M)
    (hcent : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ M → ∃ m ∈ M, g⁻¹ * z * g = m⁻¹ * z * m) {g : G}
    (hg : g * z * g⁻¹ ∈ M) : g ∈ M := by
  have _ := hzM
  have _ : Finite G := inferInstance
  obtain ⟨m, hm, hmg⟩ := hfus g⁻¹ (by simpa using hg)
  have hmg' : g * z * g⁻¹ = m⁻¹ * z * m := by simpa using hmg
  have hcomm : m * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * g * z = m * (g * z * g⁻¹) * g := by group
      _ = m * (m⁻¹ * z * m) * g := by rw [hmg']
      _ = z * (m * g) := by group
  have : g = m⁻¹ * (m * g) := by group
  rw [this]
  exact M.mul_mem (M.inv_mem hm) (hcent hcomm)

section Datum

variable {T M U : Subgroup G} {z : G}

private theorem UniqueFusionDatum.z_mem_M (hd : UniqueFusionDatum T M U z) : z ∈ M :=
  hd.setting.le (hd.le_T hd.z_mem)

private theorem UniqueFusionDatum.isPGroup_U (hd : UniqueFusionDatum T M U z) : IsPGroup 2 U :=
  fun x => ⟨1, Subtype.ext (by simpa using hd.elem.2 x x.2)⟩

end Datum

theorem UniqueFusionDatum.normalizer_le_of_mem {T M U : Subgroup G} {z : G}
    (hd : UniqueFusionDatum T M U z) {S : Subgroup G} (hS : IsPGroup 2 S) (hzS : z ∈ S) :
    S ≤ M ∧ Subgroup.normalizer (S : Set G) ≤ M := by
  have hz2 : z ^ 2 = 1 := hd.elem.2 z hd.z_mem
  have hclaim : ∀ g : G, g * z * g⁻¹ ∈ M → g ∈ M := fun g hg =>
    eq_of_fixed_coset hd.z_mem_M hd.centralizer_le
      (fun g hg => hd.control z hd.z_mem_M ⟨1, by simpa using hz2⟩ g hg) hg
  have hSM : S ≤ M := by
    by_contra hne
    have hP : S ⊓ M ≠ S := fun h => hne (h ▸ inf_le_right)
    obtain ⟨x, hx, hxn⟩ := EscapingLocal.exists_mem_inf_normalizer_not_mem hS inf_le_left hP
    have hxz : x * z * x⁻¹ ∈ S ⊓ M :=
      (Subgroup.mem_normalizer_iff.mp hx.2 z).mp ⟨hzS, hd.z_mem_M⟩
    exact hxn ⟨hx.1, hclaim x hxz.2⟩
  refine ⟨hSM, fun x hx => hclaim x (hSM ?_)⟩
  exact (Subgroup.mem_normalizer_iff.mp hx z).mp hzS

section Datum

variable {T M U : Subgroup G} {z : G}

private theorem UniqueFusionDatum.centralizer_conj_le (hd : UniqueFusionDatum T M U z) {m : G}
    (hm : m ∈ M) : Subgroup.centralizer ({m⁻¹ * z * m} : Set G) ≤ M := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hc : m * x * m⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc m * x * m⁻¹ * z = m * (x * (m⁻¹ * z * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * z * m) * x) * m⁻¹ := by rw [hx]
      _ = z * (m * x * m⁻¹) := by group
  have h1 := hd.centralizer_le hc
  have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm

private theorem UniqueFusionDatum.normalizer_le_of_conj (hd : UniqueFusionDatum T M U z) {m : G}
    (hm : m ∈ M) {R : Subgroup G} (hR : IsPGroup 2 R) (hw : m⁻¹ * z * m ∈ R) :
    Subgroup.normalizer (R : Set G) ≤ M := by
  let R' : Subgroup G := R.comap (MulAut.conj m⁻¹).toMonoidHom
  have hR' : ∀ h, h ∈ R' ↔ m⁻¹ * h * m ∈ R := fun h => by
    simp [R', Subgroup.mem_comap]
  have hpR' : IsPGroup 2 R' :=
    hR.comap_of_injective (MulAut.conj m⁻¹).toMonoidHom (MulAut.conj m⁻¹).injective
  have hzR' : z ∈ R' := (hR' z).mpr hw
  have hN := (hd.normalizer_le_of_mem hpR' hzR').2
  intro x hx
  have hx' : m * x * m⁻¹ ∈ Subgroup.normalizer (R' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hR', hR']
    have := Subgroup.mem_normalizer_iff.mp hx (m⁻¹ * h * m)
    rw [this]
    simp [mul_assoc]
  have h1 := hN hx'
  have : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [this]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm

private theorem UniqueFusionDatum.conj_mem_U (hd : UniqueFusionDatum T M U z) {m : G}
    (hm : m ∈ M) : m⁻¹ * z * m ∈ U := by
  have := (Subgroup.mem_normalizer_iff.mp (hd.normal (M.inv_mem hm)) z).mp hd.z_mem
  simpa using this

private theorem UniqueFusionDatum.exists_conj_centralizing (hd : UniqueFusionDatum T M U z)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hUS : U ≤ S) :
    S ≤ M ∧ (∀ a ∈ U, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ U) ∧
      ∃ w : G, (∃ m ∈ M, w = m⁻¹ * z * m) ∧ w ∈ U ∧ w ∈ Subgroup.centralizer (S : Set G) ∧
        w ≠ 1 ∧ Subgroup.centralizer ({w} : Set G) ≤ M ∧
        ∀ R : Subgroup G, IsPGroup 2 R → w ∈ R → Subgroup.normalizer (R : Set G) ≤ M := by
  have hSM : S ≤ M := (hd.normalizer_le_of_mem hS (hUS hd.z_mem)).1
  have hT := hd.setting.sylow
  have hTM : T ≤ M := hd.setting.le
  have hTind : ¬ 2 ∣ (T.subgroupOf M).index := by
    have h1 : ¬ 2 ∣ T.index := by simpa only [index_subgroupOf_top] using hT.2.2
    exact fun h => h1 (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))
  obtain ⟨m, hmM, hm⟩ := EscapingLocal.exists_conj_mem_of_isPGroup hTM hT.2.1 hTind hSM hS
  have hUconj : ∀ x, x ∈ U ↔ m * x * m⁻¹ ∈ U := fun x =>
    Subgroup.mem_normalizer_iff.mp (hd.normal hmM) x
  refine ⟨hSM, ?_, m⁻¹ * z * m, ⟨m, hmM, rfl⟩, hd.conj_mem_U hmM, ?_, ?_,
    hd.centralizer_conj_le hmM, fun R hR hwR => hd.normalizer_le_of_conj hmM hR hwR⟩
  · intro a ha g hg
    have h1 : m * (g⁻¹ * a * g) * m⁻¹ ∈ T := hm _ hg
    have h2 : (g * m⁻¹)⁻¹ * a * (g * m⁻¹) ∈ T := by simpa [mul_assoc] using h1
    have h3 := hd.stronglyClosed a ha (g * m⁻¹) h2
    exact (hUconj _).mpr (by simpa [mul_assoc] using h3)
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hc : m * s * m⁻¹ * z = z * (m * s * m⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hd.z_center _ (hm s hs)
    calc s * (m⁻¹ * z * m) = m⁻¹ * (m * s * m⁻¹ * z) * m := by group
      _ = m⁻¹ * (z * (m * s * m⁻¹)) * m := by rw [hc]
      _ = m⁻¹ * z * m * s := by group
  · intro h
    apply hd.z_ne_one
    calc z = m * (m⁻¹ * z * m) * m⁻¹ := by group
      _ = 1 := by rw [h]; group

private theorem UniqueFusionDatum.four_le_card (hd : UniqueFusionDatum T M U z) {u : G}
    (hu : u ∈ U) (hu1 : u ≠ 1) (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    4 ≤ Nat.card U := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hd.isPGroup_U
  have hne : u ≠ z := by
    rintro rfl
    exact hH hd.centralizer_le
  by_contra hlt
  have hn1 : n ≤ 1 := by
    by_contra h
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · have : Subsingleton U := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact hu1 (congrArg Subtype.val (Subsingleton.elim (⟨u, hu⟩ : U) 1))
  · rw [pow_one] at hn
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : U)).mp hn
    have h1 := huniq ⟨u, hu⟩ fun h => hu1 (congrArg Subtype.val h)
    have h2 := huniq ⟨z, hd.z_mem⟩ fun h => hd.z_ne_one (congrArg Subtype.val h)
    exact hne (congrArg Subtype.val (h1.trans h2.symm))

private theorem UniqueFusionDatum.charTwo_centralizer_inf (hd : UniqueFusionDatum T M U z)
    {u : G} (hu : u ∈ U) : CharTwo (Subgroup.centralizer ({u} : Set G) ⊓ M) := by
  have huM : u ∈ M := hd.setting.le (hd.le_T hu)
  have hX : Subgroup.zpowers u ≤ M := Subgroup.zpowers_le.mpr huM
  have hXp : IsPGroup 2 (Subgroup.zpowers u) := hd.isPGroup_U.to_le (Subgroup.zpowers_le.mpr hu)
  have h := hd.setting.charTwo.inf_centralizer hX hXp
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, inf_comm] at h
  exact h

private theorem UniqueFusionDatum.le_centralizer (hd : UniqueFusionDatum T M U z) {u : G}
    (hu : u ∈ U) : U ≤ Subgroup.centralizer ({u} : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  have := hd.elem.1
  exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : U) ⟨u, hu⟩)

private theorem UniqueFusionDatum.not_charTwo_centralizer (hd : UniqueFusionDatum T M U z)
    {u : G} (hu : u ∈ U) (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    ¬ CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  intro hchar
  have hUH := hd.le_centralizer hu
  obtain ⟨S, hS, hUS⟩ := EscapingLocal.exists_isSylowTwoOf_ge hUH hd.isPGroup_U
  obtain ⟨-, -, w, -, hwU, hwS, -, -, hwR⟩ := hd.exists_conj_centralizing hS.2.1 hUS
  have hQS : pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≤ S :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hwQ : w ∈ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
    hchar ⟨hUH hwU, Subgroup.centralizer_le (by exact_mod_cast hQS) hwS⟩
  have hQp : IsPGroup 2 (pCoreOf 2 (Subgroup.centralizer ({u} : Set G))) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
  exact hH ((CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _).trans
    (hwR _ hQp hwQ))

end Datum

theorem UniqueFusionDatum.escaping_centralizer_local_structure {T M U : Subgroup G} {z : G}
    (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    4 ≤ Nat.card U ∧ CharTwo (Subgroup.centralizer ({u} : Set G) ⊓ M) ∧
      ¬ CharTwo (Subgroup.centralizer ({u} : Set G)) ∧
      ∀ S : Subgroup G, IsSylowTwoOf S (Subgroup.centralizer ({u} : Set G)) → U ≤ S →
        S ≤ M ∧
        (∀ a ∈ U, ∀ g ∈ Subgroup.centralizer ({u} : Set G), g⁻¹ * a * g ∈ S →
          g⁻¹ * a * g ∈ U) ∧
        ∃ w : G, (∃ m ∈ M, w = m⁻¹ * z * m) ∧ w ∈ U ∧
          w ∈ Subgroup.centralizer (S : Set G) ∧ w ≠ 1 ∧
          Subgroup.centralizer ({w} : Set G) ≤ M ∧
          ∀ R : Subgroup G, IsPGroup 2 R → w ∈ R → Subgroup.normalizer (R : Set G) ≤ M := by
  refine ⟨hd.four_le_card hu hu1 hH, hd.charTwo_centralizer_inf hu,
    hd.not_charTwo_centralizer hu hH, fun S hS hUS => ?_⟩
  obtain ⟨hSM, hsc, hw⟩ := hd.exists_conj_centralizing hS.2.1 hUS
  exact ⟨hSM, fun a ha g _ hg => hsc a ha g hg, hw⟩

section Datum

variable {T M U : Subgroup G} {z : G}

private theorem UniqueFusionDatum.exists_conj_mem_hyperplane (hd : UniqueFusionDatum T M U z)
    (h4 : 4 ≤ Nat.card U) {B : Subgroup U} (hB : B.index = 2) :
    ∃ m ∈ M, ∃ h : m⁻¹ * z * m ∈ U, (⟨m⁻¹ * z * m, h⟩ : U) ∈ B := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hz2 : z * z = 1 := by simpa [pow_two] using hd.elem.2 z hd.z_mem
  let A : Set G := {a | ∃ m ∈ M, a = m⁻¹ * z * m}
  let W : Subgroup G := B.map U.subtype
  have hWU : W ≤ U := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hABW : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ W := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨m', hm', rfl⟩
    have h1 := hcon m hm (hd.conj_mem_U hm)
    have h2 := hcon m' hm' (hd.conj_mem_U hm')
    have : (⟨m⁻¹ * z * m, hd.conj_mem_U hm⟩ : U) * ⟨m'⁻¹ * z * m', hd.conj_mem_U hm'⟩ ∈ B :=
      (Subgroup.mul_mem_iff_of_index_two hB).mpr (iff_of_false h1 h2)
    exact ⟨_, this, rfl⟩
  let S : Set G := {x | ∃ a ∈ A, ∃ b ∈ A, x = a * b}
  let V : Subgroup G := Subgroup.closure S
  have hVW : V ≤ W := (Subgroup.closure_le W).mpr (by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hABW a ha b hb)
  have hSconj : ∀ m ∈ M, ∀ x ∈ S, m * x * m⁻¹ ∈ S := by
    rintro m hm _ ⟨_, ⟨m₁, hm₁, rfl⟩, _, ⟨m₂, hm₂, rfl⟩, rfl⟩
    refine ⟨(m₁ * m⁻¹)⁻¹ * z * (m₁ * m⁻¹), ⟨m₁ * m⁻¹, M.mul_mem hm₁ (M.inv_mem hm), rfl⟩,
      (m₂ * m⁻¹)⁻¹ * z * (m₂ * m⁻¹), ⟨m₂ * m⁻¹, M.mul_mem hm₂ (M.inv_mem hm), rfl⟩, ?_⟩
    group
  have hVconj : ∀ m ∈ M, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
    intro m hm v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hSconj m hm x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) := by group
      rw [this]
      exact V.mul_mem hx hy
    | inv x _ hx =>
      have : m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ := by group
      rw [this]
      exact V.inv_mem hx
  have hVnorm : M ≤ Subgroup.normalizer (V : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨hVconj m hm v, fun h => ?_⟩
    have := hVconj m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this
  have hVne : V ≠ U := by
    intro hVU
    have hB1 : B ≠ ⊤ := fun h => by simp [h] at hB
    obtain ⟨y, hy⟩ := not_forall.mp fun h => hB1 ((Subgroup.eq_top_iff' B).mpr h)
    have hyV : (y : G) ∈ V := by
      rw [hVU]
      exact y.2
    obtain ⟨y', hy'B, hy'⟩ := hVW hyV
    have : y' = y := Subtype.ext hy'
    rw [this] at hy'B
    exact hy hy'B
  have hV1 : V = ⊥ := (hd.irreducible V (hVW.trans hWU) hVnorm).resolve_right hVne
  have hconj : ∀ m ∈ M, m⁻¹ * z * m = z := by
    intro m hm
    have h : z * (m⁻¹ * z * m) ∈ V :=
      Subgroup.subset_closure ⟨z, ⟨1, M.one_mem, by simp⟩, m⁻¹ * z * m, ⟨m, hm, rfl⟩, rfl⟩
    rw [hV1, Subgroup.mem_bot] at h
    calc m⁻¹ * z * m = z⁻¹ * (z * (m⁻¹ * z * m)) := by group
      _ = z⁻¹ := by rw [h, mul_one]
      _ = z := inv_eq_of_mul_eq_one_right hz2
  have hzk : ∀ m ∈ M, ∀ k : ℤ, m * z ^ k * m⁻¹ = z ^ k := by
    intro m hm k
    have h1 : m * z * m⁻¹ = z := by simpa using hconj m⁻¹ (M.inv_mem hm)
    rw [← conj_zpow, h1]
  have hnz : M ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [hzk m hm k]
      exact hh
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      have h3 : h = m⁻¹ * (m * h * m⁻¹) * m := by group
      rw [h3, ← hk]
      have := hzk m⁻¹ (M.inv_mem hm) k
      rw [inv_inv] at this
      rw [this]
      exact Subgroup.zpow_mem_zpowers z k
  rcases hd.irreducible _ (Subgroup.zpowers_le.mpr hd.z_mem) hnz with hz | hz
  · exact hd.z_ne_one (Subgroup.zpowers_eq_bot.mp hz)
  · have hcard : Nat.card U = orderOf z := by
      rw [← hz, Nat.card_zpowers]
    have hord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hz2)
    have := Nat.le_of_dvd (by norm_num) hord
    omega

end Datum

theorem UniqueFusionDatum.escaping_centralizer_odd_core_components {T M U : Subgroup G} {z : G}
    (hd : UniqueFusionDatum T M U z) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1)
    (hH : ¬ Subgroup.centralizer ({u} : Set G) ≤ M) :
    CFSG.oddCore (Subgroup.centralizer ({u} : Set G)) = ⊥ ∧
      (∃ L : Subgroup (Subgroup.centralizer ({u} : Set G)), CFSG.IsComponent L) ∧
      ∀ L : Subgroup (Subgroup.centralizer ({u} : Set G)), CFSG.IsComponent L →
        ¬ L.map (Subgroup.centralizer ({u} : Set G)).subtype ≤ M := by
  obtain ⟨h4, hCM, hnotchar, -⟩ := hd.escaping_centralizer_local_structure hu hu1 hH
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G)
  have hUH : U ≤ H := hd.le_centralizer hu
  have hcharC : CFSG.IsCharacteristicP 2 ↥(H ⊓ M) := EscapingLocal.isCharacteristicP_of_charTwo hCM
  set R : Subgroup G := (CFSG.oddCore H).map H.subtype with hR
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hRnormal : (R.subgroupOf H).Normal := by
    have : R.subgroupOf H = CFSG.oddCore H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
    infer_instance
  have hHN : H ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mp hRnormal
  have hRU : ∀ a ∈ U, ∀ r ∈ R, a * r * a⁻¹ ∈ R := fun a ha r hr =>
    (Subgroup.mem_normalizer_iff.mp (hHN (hUH ha)) r).mp hr
  have hRodd : ¬ 2 ∣ Nat.card R := by
    rw [hR, Subgroup.card_map_of_injective H.subtype_injective]
    have := Nat.odd_iff.mp (EscapingLocal.odd_card_oddCore H)
    omega
  have hRM : R ≤ M := by
    refine EscapingLocal.le_of_forall_hyperplane_centralizer hRU hRodd hd.elem hd.ne_bot ?_
    intro B hB r _ hcomm
    obtain ⟨m, hm, hmU, hmB⟩ := hd.exists_conj_mem_hyperplane h4 hB
    refine hd.centralizer_conj_le hm ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm ⟨⟨_, hmU⟩, hmB⟩).symm
  have hR1 : R = ⊥ := by
    have hRC : R ≤ H ⊓ M := le_inf hRH hRM
    have hN : (R.subgroupOf (H ⊓ M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mpr (inf_le_left.trans hHN)
    have hodd : ¬ 2 ∣ Nat.card (R.subgroupOf (H ⊓ M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv]
      exact hRodd
    have h0 := (CFSG.characteristic_p_normal_prime_complement_trivial hcharC).1 _ hN hodd
    refine (Subgroup.eq_bot_iff_forall R).mpr fun x hx => ?_
    have : (⟨x, hRC hx⟩ : ↥(H ⊓ M)) ∈ R.subgroupOf (H ⊓ M) := hx
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hodd1 : CFSG.oddCore H = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hR1
  refine ⟨hodd1, ?_, ?_⟩
  · by_contra hno
    have hlayer : CFSG.layer H = ⊥ :=
      sSup_eq_bot.mpr fun K hK => absurd ⟨K, hK⟩ hno
    have hcore : CFSG.pPrimeCore 2 H = ⊥ := by
      rw [← EscapingLocal.oddCore_eq_pPrimeCore]
      exact hodd1
    have hch := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot H 2 hcore hlayer
    apply hnotchar
    rw [charTwo_iff_internal]
    change Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H at hch
    exact hch
  · intro L hL hLM
    have hCH : H ⊓ M ≤ H := inf_le_left
    have hLC : L ≤ (H ⊓ M).subgroupOf H := fun x hx => ⟨x.2, hLM ⟨x, hx, rfl⟩⟩
    have h1 := CFSG.LocalCores.component_overgroup hL hLC
    have h2 := CFSG.LocalCores.isComponent_map_mulEquiv (Subgroup.subgroupOfEquivOfLe hCH) h1
    have hlayer := CFSG.layer_eq_bot_of_isCharacteristicP (H ⊓ M : Subgroup G) 2 hcharC
    have h3 : _ ≤ CFSG.layer ↥(H ⊓ M) := le_sSup h2
    rw [hlayer, le_bot_iff] at h3
    exact (Subgroup.nontrivial_iff_ne_bot _).mp (CFSG.LocalCores.isQuasisimple_nontrivial h2.1) h3

end CFSG.QuasithinUnique
